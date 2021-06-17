open Mach
open Mono 

exception NotImplemented

let (exception_label : label) = "_EXCEPTION_"
let (plus_label : label) = "_PLUS_"
let (minus_label : label) = "_MINUS_"
let (mult_label : label) = "_MULT_"
let (equal_label : label) = "_EQUAL_"
let (notequal_label : label) = "_NOTEQUAL_"
let (true_label : label) = "_TRUE_"
let (false_label : label) = "_FALSE_"

let code_exception = 
  [LABEL exception_label; 
  EXCEPTION]
let code_plus = 
  [LABEL plus_label;
  MOVE (LREG 7, REFREG (bp, -3));
  MOVE (LREG 6, REFREG (7, 0));
  MOVE (LREG 5, REFREG (7, 1)); 
  ADD (LREG ax, REG 6, REG 5);
  RETURN]
let code_minus = 
  [LABEL minus_label;
  MOVE (LREG 7, REFREG (bp, -3));
  MOVE (LREG 6, REFREG (7, 0)); 
  MOVE (LREG 5, REFREG (7, 1)); 
  SUB (LREG ax, REG 6, REG 5);
  RETURN]
let code_mult = 
  [LABEL mult_label;
  MOVE (LREG 7, REFREG (bp, -3));
  MOVE (LREG 6, REFREG (7, 0)); 
  MOVE (LREG 5, REFREG (7, 1)); 
  MUL (LREG ax, REG 6, REG 5);
  RETURN]
let code_eq = 
  [LABEL equal_label;
  MOVE (LREG 7, REFREG (bp, -3));
  MOVE (LREG 6, REFREG (7, 0)); 
  MOVE (LREG 5, REFREG (7, 1)); 
  JMPNEQ ((ADDR (CADDR false_label)), REG 6, REG 5);
  MOVE (LREG ax, BOOL true);
  RETURN;
  LABEL false_label;
  MOVE (LREG ax, BOOL false);
  RETURN]
let code_neq = 
  [LABEL notequal_label;
  MOVE (LREG 7, REFREG (bp, -3));
  MOVE (LREG 6, REFREG (7, 0)); 
  MOVE (LREG 5, REFREG (7, 1)); 
  JMPNEQ ((ADDR (CADDR true_label)), REG 6, REG 5);
  MOVE (LREG ax, BOOL false);
  RETURN;
  LABEL true_label;
  MOVE (LREG ax, BOOL true);
  RETURN]
let code_start = 
  [LABEL start_label]

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

(* loc2rvalue : loc -> Mach.code * rvalue *)
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

(* realloc_env : venv -> int -> venv *)
let rec realloc_env venv count =
  let realloc loc count = 
    match loc with
		| L_DREF (L_REG 1, i) -> L_DREF ((L_REG cp), i) 
    | L_DREF (L_REG cp, i) -> L_DREF ((L_DREF (L_REG cp, count)), i) 
    | _ -> loc
  in

  match venv with
  | [] -> venv0
  | (key, loc)::venv_tl ->
		Dict.insert (key, (realloc loc count)) (realloc_env venv_tl count)

(* env2code env -> (code * rvalue) *)
let env2code env is_rec addr =
	let (venv, count) = env in
  
  let rec local2env n =
    let code' = code0 in
	  match n with
		| 0 -> code' 
		| n -> 
      let code' = code' @@ [PUSH (REFREG (bp, n-1))] in
      let code' = code' @@ (local2env (n-1)) in
      let code' = code' @@ [POP (LREFREG (4, n-1))] in
      code' 
	in

  let env_label = addr ^ "ENV_" in
  let out_label = env_label ^ "OUT_" in
  let code' = [LABEL env_label] in
  let code_shift = (local2env count) in

  if is_rec = false
  then (* function *)
    let code' = code' @@ [MALLOC (LREG 4, INT (count + 1)); PUSH (REG cp)] in
    let code' = code' @@ code_shift in
    let code' = code' @@ [POP (LREFREG (4, count)); MOVE (LREG ax, REG 4)] in
	  (code', REG ax)
  else (* rec function *)
		let code' = code' @@ [MALLOC (LREG 4, INT (count + 2))] in
    let code' = code' @@ code_shift in
    let code' = code' @@ [MALLOC (LREG 5, INT 2); MOVE (LREFREG (5, 0), ADDR (CADDR addr)); MOVE (LREFREG (5, 1), REG 4)] in
    let code' = code' @@ [PUSH (REG 5); PUSH (REG cp)] in
    let code' = code' @@ [POP (LREFREG (4, count + 1)); MOVE (LREFREG (4, count), REFREG (bp, count)); MOVE (LREG ax, REG 4)] in
    (code', REG ax)

(* patty2code : label -> label -> loc -> Mono.patty -> env -> Mach.code * env *)
let rec patty2code saddr faddr loc patty env =
	let (venv, count) = env in
	let (code, rvalue) = loc2rvalue loc in

  let code' = code0 in
	match patty with
	| PATTY (P_WILD, _) -> 
    (code', env)
	| PATTY (P_UNIT, _) -> 
    (code', env)
	| PATTY (P_INT n, _) ->
		let code' = code' @@ code in
    let code' = code' @@ [PUSH (rvalue)] in
    let code' = code' @@ [POP (LREG 4); JMPNEQ (ADDR (CADDR faddr), INT n, REG 4)] in
    let code' = code' @@ [JUMP (ADDR (CADDR saddr)); LABEL (faddr); MOVE (LREG 5, INT 0); LABEL (saddr)] in
		(code', env)
	| PATTY (P_BOOL b, _) ->
    let code' = code' @@ code in
    let code' = code' @@ [PUSH (rvalue)] in
    let code' = code' @@ [POP (LREG 4); XOR (LREG 4, BOOL b, REG 4); JMPTRUE (ADDR (CADDR faddr), REG 4)] in
    let code' = code' @@ [JUMP (ADDR (CADDR saddr)); LABEL (faddr); MOVE (LREG 5, INT 0); LABEL (saddr)] in
		(code', env)
	| PATTY (P_VID (avid, VAR), _) -> 
		let code' = code' @@ code in
    let code' = code' @@ [PUSH (rvalue)] in
    let venv = Dict.insert (avid, L_DREF (L_REG 1, count)) venv in
    let env = (venv, count+1) in
		(code', env)
	| PATTY (P_VID (avid, CON), _) ->
		let code' = code' @@ code in 
    let code' = code' @@ [PUSH (rvalue)] in
    let code' = code' @@ [POP (LREG 4); JMPNEQSTR (ADDR (CADDR faddr), STR avid, REFREG (4, 0))] in
    let code' = code' @@ [JUMP (ADDR (CADDR saddr)); LABEL (faddr); MOVE (LREG 5, INT 0); LABEL (saddr)] in
		(code', env)
  | PATTY (P_VID (avid, CONF), _) ->
    (code', env)
	| PATTY (P_VIDP ((avid, _), patty'), _) ->
    let code' = code' @@ code in
    let code' = code' @@ [PUSH (rvalue)] in
    let code' = code' @@ [POP (LREG 4); JMPNEQSTR (ADDR (CADDR faddr), STR avid, REFREG (4, 0))] in
    let code' = code' @@ [JUMP (ADDR (CADDR saddr)); LABEL (faddr); MOVE (LREG 5, INT 0); LABEL (saddr)] in
		let (code, env) = patty2code saddr faddr (L_DREF (L_REG 4, 1)) patty' env in
    let code' = code' @@ code in
		(code', env)
	| PATTY (P_PAIR (patty1, patty2), _) ->
		let (code1, env) = patty2code saddr faddr (L_DREF (loc, 0)) patty1 env in
    let code' = code' @@ code1 in
		let (code2, env) = patty2code saddr faddr (L_DREF (loc, 1)) patty2 env in
    let code' = code' @@ code2 in
		(code', env)

(* expty2code : env -> Mono.label -> Mono.expty -> Mach.code * Mach.rvalue *)
let rec expty2code env expty =
  let code' = code0 in
	match expty with
  | EXPTY (exp, ty) ->
    (
    match exp with
  	| E_INT i -> 
      let code' = [MOVE (LREG ax, INT i)] in
      (code', REG ax)
	  | E_BOOL b -> 
      let code' = [MOVE (LREG ax, BOOL b)] in
      (code', REG ax)
	  | E_UNIT -> 
      let code' = [MOVE (LREG ax, UNIT)] in
      (code', REG ax)
    | E_PLUS -> 
      let code' = code' @@ [PUSH (ADDR (CADDR plus_label))] in
      let code' = code' @@ [MOVE (LREG ax, ADDR (CADDR plus_label))] in
      (code', REG ax)
    | E_MINUS -> 
      let code' = code' @@ [PUSH (ADDR (CADDR plus_label))] in
      let code' = code' @@ [MOVE (LREG ax, ADDR (CADDR minus_label))] in
      (code', REG ax)
    | E_MULT -> 
      let code' = code' @@ [PUSH (ADDR (CADDR plus_label))] in
      let code' = code' @@ [MOVE (LREG ax, ADDR (CADDR mult_label))] in
      (code', REG ax)
    | E_EQ -> 
      let code' = code' @@ [PUSH (ADDR (CADDR plus_label))] in
      let code' = code' @@ [MOVE (LREG ax, ADDR (CADDR equal_label))] in
      (code', REG ax)
    | E_NEQ -> 
      let code' = code' @@ [PUSH (ADDR (CADDR plus_label))] in
      let code' = code' @@ [MOVE (LREG ax, ADDR (CADDR notequal_label))] in
      (code', REG ax)
	  | E_VID (avid, VAR) ->
		  let (venv, count) = env in 
      let Some loc = Dict.lookup avid venv in
      let (code, rvalue) = loc2rvalue loc in
      let code' = code' @@ code in
      let code' = code' @@ [MOVE (LREG ax, rvalue)] in
      (code', REG ax)
	  | E_VID (avid, CON) ->
  		let con_label = "_" ^ labelNewStr "CON_" ^ "_" in
      let code' = code' @@ [LABEL con_label] in

      let (code_env, rvalue) = env2code env false con_label in
      let code' = code' @@ code_env in
      
      let code_con = con2code env expty in
      let code' = code' @@ code_con in

      (code', REG ax)
	  | E_VID (avid, CONF) ->
  		let conf_label = "_" ^ labelNewStr "CONF_" ^ "_" in
      let code' = code' @@ [LABEL conf_label] in

      let (code_env, rvalue) = env2code env false conf_label in
      let code' = code' @@ code_env in
      
      let code_conf = conf2code env expty in 
      let code' = code' @@ code_conf in

      (code', REG ax)
	  | E_FUN mlist ->
  		let func_label = "_" ^ labelNewStr "FUNC_" ^ "_" in
	  	let out_label = func_label ^ "OUT" in
      
      let (code_env, rvalue) = env2code env false func_label in
	  	let code' = code' @@ code_env in
      let code' = code' @@ [MALLOC (LREG 4, INT 2); PUSH (REG 4)] in
	  
	  	let code' = code' @@ [JUMP (ADDR (CADDR out_label)); LABEL (func_label)] in
      let (venv, count) = env in
      let rvenv = realloc_env venv count in
      let renv = (rvenv, 0) in
      let code_mlist = mlist2code renv mlist in
      let code' = code' @@ code_mlist in
	  	let code' = code' @@ [RETURN; LABEL (out_label)] in
	  	let code' = code' @@ [POP (LREG 4); MOVE (LREFREG (4, 0), ADDR (CADDR func_label)); MOVE (LREFREG (4 , 1), rvalue); MOVE (LREG ax, REG 4)] in
		  (code', REG ax)
    | E_PAIR (expty1, expty2) ->
      let (code1, rvalue1) = expty2code env expty1 in
		  let code' = code' @@ code1 in
      let code' = code' @@ [PUSH (rvalue1)] in

		  let (code2, rvalue2) = expty2code env expty2 in
      let code' = code' @@ [MALLOC (LREG 4, INT 2); POP (LREFREG (4, 0)); PUSH (REG 4)] in
      let code' = code' @@ code2 in
		  let code' = code' @@ [POP (LREG 4); MOVE (LREFREG (4, 1), rvalue2); MOVE (LREG ax, REG 4)] in
		  
      (code', REG ax)
    | E_LET (dec, expty) ->
		  let (code_dec, env) = dec2code env dec in
      let code' = code' @@ code_dec in

		  let (code_expty, rvalue) = expty2code env expty in
      let code' = code' @@ code_expty in

      let code' = code' @@ [MOVE (LREG ax, rvalue)] in
      (code', REG ax)
    | E_APP (expty1, expty2) ->
      let app_label = "_" ^ labelNewStr "APP_" ^ "_" in
      let app_start = app_label ^ "START_" in
      let app_out   = app_label ^ "OUT_" in

      let code' = code' @@ [LABEL app_start] in
      let (code2, rvalue2) = expty2code env expty2 in
      (
		  match expty1 with
		  | EXPTY (E_PLUS, _) | EXPTY (E_MINUS, _) | EXPTY (E_MULT, _) | EXPTY (E_EQ, _) | EXPTY (E_NEQ, _) ->
        let (code1, rvalue1) = expty2code env expty1 in
        let code' = code' @@ code1 in
        let code' = code' @@ [PUSH (rvalue1)] in
        let code' = code' @@ code2 in
        let code' = code' @@ [PUSH (rvalue2); CALL (REFREG (sp, -2));] in
        let code' = code' @@ [POP (LREG tr); POP (LREG tr); POP (LREG tr); LABEL app_out] in
			  (code', REG ax)
      | EXPTY (E_VID (avid, VAR), _) ->
        let (venv, count) = env in
        let Some loc = Dict.lookup avid venv in
				let (code1, rvalue1) = loc2rvalue loc in
        let code' = code' @@ code1 in
        let code' = code' @@ [PUSH rvalue1] in
        let code' = code' @@ code2 in 
        let code' = code' @@ [PUSH rvalue2] in
        let code' = code' @@ [POP (LREG ax); MOVE (LREG 5, REG cp); POP (LREG 4); PUSH (REG 5);] in
        let code' = code' @@ [MOVE (LREG cp, REFREG (4, 1)); CALL (REFREG (4, 0)); POP (LREG cp)] in
        let code' = code' @@ [LABEL app_out] in
				(code', REG ax)
	    | EXPTY (E_VID (avid, CON), _) ->
			  let (code1, rvalue1) = expty2code env expty1 in
        let code' = code' @@ code1 in
        let code' = code' @@ [PUSH (rvalue1)] in
        let code' = code' @@ code2 in
        let code' = code' @@ [PUSH (rvalue2)] in
			  let code' = code' @@ [POP (LREG ax); POP (LREG 4); MOVE (LREG cp, REFREG (4, 1)); CALL (REFREG (4, 0))] in
        let code' = code' @@ [LABEL app_out] in
			  (code', REG ax)
	    | EXPTY (E_VID (avid, CONF), _) ->
        let (code1, rvalue1) = expty2code env expty1 in
        let code' = code' @@ code1 in
        let code' = code' @@ [PUSH (rvalue1)] in
        let code' = code' @@ code2 in
        let code' = code' @@ [PUSH (rvalue2)] in
        let code' = code' @@ [MALLOC (LREG 4, INT 2); MOVE (LREFREG (4, 0), STR avid); POP (LREFREG (4, 1))] in
        let code' = code' @@ [MOVE (LREG ax, REG 4); POP (LREG tr); LABEL app_out] in
			  (code', REG ax)	
		  | _ -> (* (function, arg) *)
			  let (code1, rvalue1) = expty2code env expty1 in
        let code' = code' @@ code1 in
        let code' = code' @@ [PUSH (rvalue1)] in
        let code' = code' @@ code2 in
        let code' = code' @@ [PUSH (rvalue2)] in
			  let code' = code' @@ [POP (LREG ax); POP (LREG 4); MOVE (LREG cp, REFREG (4, 1)); CALL (REFREG (4, 0))] in
        let code' = code' @@ [LABEL app_out] in
			  (code', REG ax)
		  )
		)

(* con2code : env -> Mono.expty -> Mach.code *)
and con2code env expty =
  let _ = print_endline "** TODO :: EVID CON **" in

  let code' = code0 in
  match expty with
  | EXPTY (E_VID (avid, CON), _) ->
    let code' = code' @@ [PUSH (STR avid)] in
    let code' = code' @@ [MALLOC (LREG 4, INT 2); POP (LREFREG(4, 0)); MOVE (LREFREG(4, 1), INT 0); MOVE (LREG ax, REG 4)] in 
    code'
  | _ ->
    code'

(* conf2code : env -> Mono.expty -> Mach.code *)
and conf2code env expty = 
  let _ = print_endline "** TODO :: EVID CONF **" in
  let code' = code0 in
  match expty with
  | EXPTY (E_VID (avid, CONF), T_INT) ->
    code'
  | EXPTY (E_VID (avid, CONF), T_BOOL) ->
    code'
  | EXPTY (E_VID (avid, CONF), T_UNIT) ->
    code'
  | EXPTY (E_VID (avid, CONF), T_NAME ty) ->
    code'
  | EXPTY (E_VID (avid, CONF), T_PAIR (ty1, ty2)) ->
    code'
  | EXPTY (E_VID (avid, CONF), T_FUN (ty1, ty2)) ->
    code'
  | _ ->
    code' 
    
(* mlist2code : env -> Mono.mrule list -> Mach.code *)
and mlist2code env mlist =
  let rec pop n =
	  match n with
	  | 0 -> code0
	  | i ->
      [POP (LREG tr)] @@ (pop (i-1))
  in

  let mrule2code env mrule =
    let code' = code0 in
    match mrule with
    | M_RULE (patty, expty) ->
      let func_label = "_" ^ labelNewStr "FUNC_" ^ "_" in
      let out_label  = func_label ^ "OUT_" in

      let saddr = "_" ^ labelNewStr "MATCH_SUCCESS_" ^ "_" in
      let faddr = "_" ^ labelNewStr "MATCH_FAIL_" ^ "_" in
  	  let (code_patty, penv) = patty2code saddr faddr (L_REG ax) patty env in
      let (pvenv, pcount) = penv in
	    let (code_expty, rvalue) = expty2code penv expty in
      let (evenv, ecount) = env in
      let locals = pcount - ecount in

      let code' = code' @@ [MOVE (LREG 5, INT 1)] in
      let code' = code' @@ code_patty in
      let code' = code' @@ [JMPNEQ (ADDR (CADDR out_label), REG 5, INT 1)] in
      let code' = code' @@ code_expty in
    
	    let pop_code = pop locals in
      let code' = code' @@ pop_code in
      let code' = code' @@ [MOVE (LREG ax, rvalue); RETURN] in
      let code' = code' @@ [LABEL out_label] in
      let code' = code' @@ pop_code in
      code'
    | _ -> code'
  in

  let code' = code0 in
	match mlist with
	| [] -> 
    code'
	| mh :: mt -> 
    let code_head = (mrule2code env mh) in
    let code' = code' @@ code_head in
    let code_tail = mlist2code env mt in
    let code' = code' @@ code_tail in
    code'


(* dec2code : env -> Mono.dec -> Mach.code * env *)
and dec2code env dec =
  let code' = code0 in
  let (venv, count) = env in

  let dec_label = "_" ^ labelNewStr "DEC_" ^ "_" in
  let dec_start = dec_label ^ "START_" in
  let dec_out   = dec_label ^ "OUT_" in
  let code' = code' @@ [LABEL dec_start] in

  match dec with
  | D_VAL (PATTY (P_VID (avid1, is), _), EXPTY (E_VID (avid2, VAR), _)) -> 
    let Some loc = Dict.lookup avid2 venv in
    let nvenv = Dict.insert (avid1, loc) venv in
    let env  = (nvenv, count) in
    (code', env) 
	| D_VAL (PATTY (P_VID (avid1, is), _), EXPTY (E_VID (avid2, CON), _)) -> 
    let _ = print_endline "***** TODO :: DEC CON ***** " in

    let Some loc = Dict.lookup avid2 venv in
    let nvenv = Dict.insert (avid1, loc) venv in
    let env  = (nvenv, count) in
    (code', env) 
	| D_VAL (PATTY (P_VID (avid1, is), _), EXPTY (E_VID (avid2, CONF), _)) -> 
    let _ = print_endline "***** TODO :: DEC CONF ***** " in

    let Some loc = Dict.lookup avid2 venv in
    let nvenv = Dict.insert (avid1, loc) venv in
    let env  = (nvenv, count) in
    (code', env) 
  | D_VAL (PATTY (P_VID (avid, is), _), expty) -> 
    let nvenv = Dict.insert (avid, L_DREF (L_REG bp, count)) venv in
    let env  = (nvenv, count+1) in
  	let (code, rvalue) = expty2code env expty in
    let code' = code' @@ code in
    let code' = code' @@ [PUSH rvalue] in
    (code', env) 
	| D_REC (PATTY (P_VID (avid, is), _), EXPTY (E_FUN mlist, _)) ->
    let (code_env, rvalue) = env2code env true dec_start in
    let code' = code' @@ code_env in
    let code' = code' @@ [MALLOC (LREG 4, INT 2); PUSH (REG 4); MOVE (LREFREG (4 , 1), rvalue)] in

    let code' = code' @@ [JUMP (ADDR (CADDR dec_out)); LABEL dec_start] in
    let nvenv = (Dict.insert (avid, L_DREF (L_REG 1, count)) venv) in
    let rvenv = realloc_env nvenv (count+1) in
    let renv = (rvenv, 0) in
    let code_mlist = mlist2code renv mlist in
    let code' = code' @@ code_mlist in
    let code' = code' @@ [LABEL dec_out] in

    let env = (nvenv, count+1) in
    let code' = code' @@ [POP (LREG 4); MOVE (LREFREG (4, 0), ADDR (CADDR dec_start)); MOVE (LREG ax, REG 4);] in
    (code', env)
	| D_DTYPE -> 
    (code', env)
	| _ -> 
    (code', env)	

(* dlist2code env -> dlist -> (Mach.code * env) *)
let rec dlist2code env dlist =
	match dlist with
	| [] -> (code0, env)
	| hd :: tl ->
    let code' = code0 in
		let (code_dh, env_dh) = dec2code env hd in
    let code' = code' @@ code_dh in
		let (code_dt, env_dt) = dlist2code env_dh tl in
    let code' = code' @@ code_dt in
		(code', env_dt) 

(* program2code : Mono.program -> Mach.code *)
let program2code (dlist, et) =
  let code' = code0 in
  let code' = code' @@ code_exception @@ code_plus @@ code_minus @@ code_mult @@ code_eq @@ code_neq in
  let code' = code' @@ [LABEL start_label] in

	let (code_dlist, env_dlist) = dlist2code env0 dlist in
  let code' = code' @@ code_dlist in

	let (code_expty, rvalue) = expty2code env_dlist et in
  let code' = code' @@ code_expty in

  let code' = code' @@ [HALT (REG ax)] in
	code'