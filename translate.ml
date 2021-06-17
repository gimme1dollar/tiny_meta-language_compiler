open Mach
open Mono 

exception NotImplemented

(* location *)
type loc =
    L_INT of int          (* integer constant *)
  | L_BOOL of bool        (* boolean constant *)
  | L_UNIT                (* unit constant *)
  | L_STR of string       (* string constant *)
  | L_ADDR of Mach.addr   (* at the specified address *)
  | L_REG of Mach.reg     (* at the specified register *)
  | L_DREF of loc * int   (* at the specified location with the specified offset *)

type venv = (Mono.avid, loc) Dict.dict  (* variable environment *)
let venv0 : venv = Dict.empty           (* empty variable environment *)

type env = venv * int
let env0 : env = (venv0, 0)

(* val loc2rvalue : loc -> Mach.code * rvalue *)
let rec loc2rvalue l = match l with
    L_INT i -> (Mach.code0, Mach.INT i)
  | L_BOOL b -> (Mach.code0, Mach.BOOL b)
  | L_UNIT -> (Mach.code0, Mach.UNIT)
  | L_STR s -> (Mach.code0, Mach.STR s)
  | L_ADDR a -> (Mach.code0, Mach.ADDR a)
  | L_REG r -> (Mach.code0, Mach.REG r)
  | L_DREF (L_ADDR a, i) -> (Mach.code0, Mach.REFADDR (a, i))
  | L_DREF (L_REG r, i) -> (Mach.code0, Mach.REFREG (r, i))
  | L_DREF (l, i) ->
     let (code, rvalue) = loc2rvalue l in
     (Mach.cpost code [Mach.MOVE (Mach.LREG Mach.tr, rvalue)], Mach.REFREG (Mach.tr, i))

let (exceptionLabel : label) = "_EXCEPTION_"
let (plusLabel : label) = "_PLUS_"
let (minusLabel : label) = "_MINUS_"
let (multLabel : label) = "_MULT_"
let (eqLabel : label) = "_EQ_"
let (neqLabel : label) = "_NEQ_"
let (trueLabel : label) = "_TRUE_"
let (falseLabel : label) = "_FALSE_"

(*
 * Generate code for Abstract Machine MACH 
 *)

(* patty2code : Mach.label -> Mach.label -> loc -> Mono.patty -> Mach.code * venv *)
let patty2code lstart lfailure l patty = 
  let rec patty2codeAux lfailure l patty venv =
    let PATTY (pat, ty) = patty in
    match pat with
    P_WILD -> (code0, venv)
    | P_VID (x, VAR) -> (code0, Dict.insert (x, l) venv)
    | P_VID (x, CON) -> let (code, rvalue) = loc2rvalue (L_DREF (l, 0)) in (cpost code [JMPNEQSTR (ADDR (CADDR lfailure), STR x, rvalue)], venv)
    | P_VID (x, CONF) -> let (code, rvalue) = loc2rvalue l in (cpost code [JMPNEQSTR (ADDR (CADDR lfailure), STR x, rvalue)], venv)
    | P_VIDP (x, patty) -> 
        let (code1, venv1) = patty2codeAux lfailure (L_DREF (l, 0)) (PATTY (P_VID x, T_UNIT)) venv in
        let (code2, venv2) = patty2codeAux lfailure (L_DREF (l, 1)) patty venv in
        (code1 @@ code2, Dict.merge venv1 venv2)
    | P_INT i -> let (code, rvalue) = loc2rvalue l in (cpost code [JMPNEQ (ADDR (CADDR lfailure), rvalue, INT i)], venv)
    | P_BOOL b -> let (code, rvalue) = loc2rvalue l in (cpost code [XOR (LREG ax, rvalue, BOOL b); JMPTRUE (ADDR (CADDR lfailure), REG ax)], venv)
    | P_UNIT -> (code0, venv)
    | P_PAIR (patty1, patty2) -> 
        let (code1, venv1) = patty2codeAux lfailure (L_DREF (l, 0)) patty1 venv in 
        let (code2, venv2) = patty2codeAux lfailure (L_DREF (l, 1)) patty2 venv in
        (code1 @@ code2, Dict.merge venv1 venv2)
  in

  let (code, venv) = patty2codeAux lfailure l patty venv0 in 
  (cpre [LABEL lstart] code, venv)

let updateContextVenv venv =
  let rec aux loc = 
    match loc with
    | L_REG x -> if x = cp then L_DREF (L_REG x, 1) else loc 
    | L_DREF (loc, offset) -> L_DREF (aux loc, offset)
    | _ -> loc
  in

  Dict.map aux venv

let createFunctionRValue label = clist [MALLOC (LREG ax, INT 2); MOVE (LREFREG (ax, 0), ADDR (CADDR label))]

let recursiveFunctionCounter = ref 0

let pushRecursiveFunction rvalue = 
  let rec aux loc idx =
    if idx = !recursiveFunctionCounter then loc else L_DREF (aux loc (idx + 1), 1)
  in

  let insertLoc = aux (L_REG r10) 0 in
  let (code, room) = loc2rvalue insertLoc in
  let code = cpost code [PUSH rvalue; MOVE (LREG ax, room); POP (LREFREG (ax, 0)); MALLOC (LREFREG (ax, 1), INT 2)] in
  (recursiveFunctionCounter := !recursiveFunctionCounter + 1; (code, L_DREF (insertLoc, 0)))

(* expty2code : env -> Mach.label -> Mono.expty -> Mach.code * Mach.rvalue *)
let rec expty2code (venv, count) expty = 
  let EXPTY (exp, ty) = expty in
  match exp with
  E_INT i -> (code0, Mach.INT i)
  | E_BOOL b -> (code0, Mach.BOOL b)
  | E_UNIT -> (code0, Mach.UNIT)
  | E_VID (x, VAR) -> (
    let loc = Dict.lookup x venv in
    match loc with
    None -> ([EXCEPTION], INT 0)
    | Some loc -> loc2rvalue loc
  )
  | E_VID (x, CON) -> ([MALLOC (LREG ax, INT 2); MOVE (LREFREG (ax, 0), STR x)], REG ax)
  | E_VID (x, CONF) -> 
      let functionLabel = labelNew () in
      let escapeLabel = labelNewLabel "ESCAPE_" (functionLabel ^ "_") in
      let code1 = clist [JUMP (ADDR (CADDR escapeLabel)); LABEL functionLabel; MALLOC (LREG ax, INT 2); MOVE (LREFREG (ax, 0), STR x); MOVE (LREFREG (ax, 1), REFREG (cp, 0)); RETURN; LABEL escapeLabel] in
      let code2 = clist [MALLOC (LREG ax, INT 2); MOVE (LREFREG (ax, 0), ADDR (CADDR functionLabel)); MOVE (LREFREG (ax, 1), REG cp)] in
      (code1 @@ code2, REG ax)
  | E_PLUS -> (createFunctionRValue plusLabel, REG ax)
  | E_MINUS -> (createFunctionRValue minusLabel, REG ax)
  | E_MULT -> (createFunctionRValue multLabel, REG ax)
  | E_EQ -> (createFunctionRValue eqLabel, REG ax)
  | E_NEQ -> (createFunctionRValue neqLabel, REG ax)
  | E_FUN ml -> 
      let functionLabel = labelNew () in
      let code = createFunction functionLabel (updateContextVenv venv, 0) ml in
      (cpost code [MALLOC (LREG ax, INT 2); MOVE (LREFREG (ax, 0), ADDR (CADDR functionLabel)); MOVE (LREFREG (ax, 1), REG cp)], REG ax)
  | E_LET (dec, expty) ->
      let (code1, env') = dec2code (venv, count) dec in
      let (code2, rvalue) = expty2code env' expty in 
      (code1 @ code2, rvalue)
  | E_APP (expty1, expty2) ->
      let code1 = clist [PUSH (REG cp)] in
      let (code2, rvalue1) = expty2code (venv, count + 1) expty2 in
      let code3 = clist [POP (LREG cp); PUSH rvalue1] in
      let (code4, rvalue2) = expty2code (venv, count + 1) expty1 in
      let code5 = clist [MOVE (LREG ax, rvalue2); MALLOC (LREG cp, INT 2); POP (LREFREG (cp, 0)); MOVE (LREFREG (cp, 1), REFREG (ax, 1)); CALL (REFREG (ax, 0))] in
      (code1 @@ code2 @@ code3 @@ code4 @@ code5, REG ax)
  | E_PAIR (expty1, expty2) -> 
      let code1 = clist [PUSH (REG cp)] in
      let (code2, rvalue1) = expty2code (venv, count + 1) expty1 in 
      let code3 = clist [POP (LREG cp); PUSH rvalue1] in
      let (code4, rvalue2) = expty2code (venv, count + 1) expty2 in 
      let code5 = clist [PUSH rvalue2; MALLOC (LREG ax, INT 2); POP (LREFREG (ax, 1)); POP (LREFREG (ax, 0))] in
      (code1 @@ code2 @@ code3 @@ code4 @@ code5, REG ax)

and createFunction label (venv, count) ml = 
  let escapeLabel = labelNewLabel "ESCAPE_" (label ^ "_") in
  let (code, _) = List.fold_right (fun mrule (code, lfailure) -> let lstart = labelNewStr (label ^ "_") in ((mrule2code (venv, count) lstart lfailure mrule) @@ code, lstart)) ml (code0, exceptionLabel) in
  let code = cpre [JUMP (ADDR (CADDR escapeLabel)); LABEL label] code in
  cpost code [LABEL escapeLabel]

(* dec2code : env -> Mono.dec -> Mach.code * env *)
and dec2code (venv, count) dec = 
  match dec with
  D_VAL (patty, expty) -> 
    let code1 = clist [PUSH (REG cp)] in
    let (code2, rvalue) = expty2code (venv, count + 1) expty in 
    let code3 = clist [MALLOC (LREG cp, INT 2); POP (LREFREG (cp, 1)); MOVE (LREFREG (cp, 0), rvalue)] in
    let (code4, venv') = patty2code (labelNew ()) exceptionLabel (L_DREF (L_REG cp, 0)) patty in
    (code1 @@ code2 @@ code3 @@ code4, (Dict.merge (updateContextVenv venv) venv', count))
  | D_REC (PATTY (P_VID (x, VAR), _), EXPTY (E_FUN ml, _)) -> 
      let functionName = labelNew () in
      let code1 = clist [MALLOC (LREG ax, INT 2); MOVE (LREFREG (ax, 0), ADDR (CADDR functionName)); MOVE (LREFREG (ax, 1), REG cp)] in
      let (code2, loc) = pushRecursiveFunction (REG ax) in 
      let venv = Dict.insert (x, loc) venv in
      let code3 = createFunction functionName (updateContextVenv venv, 0) ml in
      (code1 @@ code2 @@ code3, (venv, count))
  | _ -> (code0, (venv, count))

(* mrule2code : env -> Mach.label -> Mach.label -> Mono.mrule -> Mach.code *)
and mrule2code (venv, count) lstart lfailure mrule = 
  let M_RULE (patty, expty) = mrule in
  let (code, venv') = patty2code lstart lfailure (L_DREF (L_REG cp, 0)) patty in
  let (code', rvalue) = expty2code (Dict.merge venv venv', 0) expty in
  cpost (code @@ code') [MOVE (LREG ax, rvalue); RETURN]

(* program2code : Mono.program -> Mach.code *)
let program2code (dlist, et) = 
  let _ = (recursiveFunctionCounter := 0) in
  let plusFunction = clist [LABEL plusLabel; MOVE (LREG bx, REFREG (cp, 0)); ADD (LREG ax, REFREG (bx, 0), REFREG (bx, 1)); RETURN] in
  let minusFunction = clist [LABEL minusLabel; MOVE (LREG bx, REFREG (cp, 0)); SUB (LREG ax, REFREG (bx, 0), REFREG (bx, 1)); RETURN] in
  let multFunction = clist [LABEL multLabel; MOVE (LREG bx, REFREG (cp, 0)); MUL (LREG ax, REFREG (bx, 0), REFREG (bx, 1)); RETURN] in

  let eqFunction = clist [LABEL eqLabel; MOVE (LREG bx, REFREG (cp, 0)); JMPNEQ (ADDR (CADDR falseLabel), REFREG (bx, 0), REFREG (bx, 1)); LABEL trueLabel; MOVE (LREG ax, BOOL true); RETURN]  in
  let neqFunction = clist [LABEL neqLabel; MOVE (LREG bx, REFREG (cp, 0)); JMPNEQ (ADDR (CADDR trueLabel), REFREG (bx, 0), REFREG (bx, 1)); LABEL falseLabel; MOVE (LREG ax, BOOL false); RETURN] in

  let arithmeticFunctions = plusFunction @@ minusFunction @@ multFunction @@ eqFunction @@ neqFunction in

  let c_start = cpost arithmeticFunctions [LABEL exceptionLabel; EXCEPTION; LABEL start_label; MALLOC (LREG r10, INT 2)] in 
  let (c_global, env) = List.fold_left (fun (code, env) dec -> let (code', env) = (dec2code env dec) in (code @@ code', env)) (code0, env0) dlist in

  let (c_main, rvalue) = expty2code env et in
  c_start @@ c_global @@ c_main @@ [HALT rvalue]
;;

