open Core
open Dict
open Set_type

exception NotImplemented
exception TypingError

let try_lookup key = match key with Some value -> value | None -> raise TypingError

(* fresh type-variable *)
let fresh_tyvar_counter = ref 0
let get_fresh_tyvar () = (fresh_tyvar_counter := !fresh_tyvar_counter + 2; (!fresh_tyvar_counter))

(* fresh type-name *)
let fresh_tyname_counter = ref 1
let get_fresh_tyname () = (fresh_tyname_counter := !fresh_tyname_counter + 2; (!fresh_tyname_counter))

(* type_scheme : (type_variable set) * type *)
type tsch = tyvar set * ty

let rec ty2tyvars ty =
	match ty with
	| T_INT | T_BOOL | T_UNIT -> []
	| T_NAME n | T_VAR n -> [n]
	| T_PAIR (ty1, ty2) | T_FUN (ty1, ty2) -> union (ty2tyvars ty1) (ty2tyvars ty2)
	| _ -> []

let rec get_scheme_free_var tsch =
	let (var_set, ty) = tsch in
	let tyvar_set = ty2tyvars ty in
	diff tyvar_set var_set

let rec is_scheme_free_var tsch =
	let (tyvar, ty) = tsch in
    match ty with
    | T_INT | T_BOOL | T_UNIT -> false
    | T_NAME _ -> false
	| T_VAR tyvar' -> (tyvar = tyvar')
    | T_PAIR (ty1, ty2) | T_FUN (ty1, ty2) -> 
	  (is_scheme_free_var (tyvar, ty1)) && (is_scheme_free_var (tyvar, ty2))
	| _ -> false
    
(* type_env : (type_constructor -> type_name) *)
type tenv = (Ast.tycon, tyname) dict
let tenv0 : tenv = []

(* var_env : (vid -> (type_scheme, is)) *)
type venv = (Ast.vid, (tsch * is)) dict
let venv0 : venv = []

let rec get_venv_free_var ve acc =
	match ve with
	| [] -> acc
	| ve_head :: ve_tail ->
	  let (_, (tsch, _)) = ve_head in
	  let free_vars = get_scheme_free_var tsch in
	  get_venv_free_var ve_tail (union free_vars acc)
	
let rec closure ve ve' acc =
	match ve with
	| [] -> acc
	| ve_head::ve_tail ->
	  let (vid', ((tyvar, ty), is)) = ve_head in
	  let targ_free = (get_venv_free_var ve' []) in
	  let refr_free = diff (ty2tyvars ty) tyvar in
	  let remn_free = diff refr_free targ_free in

	  let tsch' = ((union remn_free tyvar, ty), is) in
	  closure ve_tail ve' ([(vid', tsch')] @ acc)
	  
(* typing_ctx : tenv * venv *)
type tctx = tenv * venv
let tctx0 : tctx = (tenv0, venv0) 
	
(* substitution : (type_variable * type) list *)
type subst = (tyvar * ty) list

let rec subst_type ty ss =
	let func ty s = 
		let (tyvar', ty') = s in
		match ty with
		| T_INT -> T_INT
		| T_BOOL -> T_BOOL
		| T_UNIT -> T_UNIT
		| T_NAME n -> T_NAME n
		| T_PAIR (ty1, ty2) -> T_PAIR (subst_type ty1 [s], subst_type ty2 [s]) 
		| T_FUN (ty1, ty2) -> T_FUN (subst_type ty1 [s], subst_type ty2 [s]) 
		| T_VAR v -> if v = tyvar' then ty' else ty
		| _ -> ty
	in

	List.fold_left func ty ss 

let rec subst_patty patty ss =
	let func patty s = 
		match patty with
		| PATTY (P_WILD, ty) -> 
			PATTY (P_WILD, subst_type ty [s])
		| PATTY (P_INT n, ty) -> 
			PATTY (P_INT n, subst_type ty [s])
		| PATTY (P_BOOL b, ty) -> 
			PATTY (P_BOOL b, subst_type ty [s])
		| PATTY (P_UNIT, ty) -> 
			PATTY (P_UNIT, subst_type ty [s])
		| PATTY (P_VID vid, ty) -> 
			PATTY (P_VID vid, subst_type ty [s])
		| PATTY (P_VIDP (vid, vid_ty), ty) -> 
			let vid_ty' = subst_patty vid_ty [s] in
			PATTY (P_VIDP (vid, vid_ty'), subst_type ty [s])
		| PATTY (P_PAIR (patty1, patty2), ty) -> 
			let patty1' = subst_patty patty1 [s] in
			let patty2' = subst_patty patty2 [s] in
			PATTY (P_PAIR (patty1', patty2'), subst_type ty [s]) 
		| _ -> patty
	in

	List.fold_left func patty ss
	
let rec subst_expty expty ss =
	let func expty s = 
		begin match expty with
		| EXPTY (E_INT n, ty) -> 
			EXPTY (E_INT n, subst_type ty [s])
		| EXPTY (E_BOOL b, ty) -> 
			EXPTY (E_BOOL b, subst_type ty [s])
		| EXPTY (E_UNIT, ty) -> 
			EXPTY (E_UNIT, subst_type ty [s])
		| EXPTY (E_PLUS, ty) -> 
			EXPTY (E_PLUS, subst_type ty [s])
		| EXPTY (E_MINUS, ty) -> 
			EXPTY (E_MINUS, subst_type ty [s])
		| EXPTY (E_MULT, ty) -> 
			EXPTY (E_MULT, subst_type ty [s])
		| EXPTY (E_EQ, ty) -> 
			EXPTY (E_EQ, subst_type ty [s])
		| EXPTY (E_NEQ, ty) -> 
			EXPTY (E_NEQ, subst_type ty [s])
		| EXPTY (E_VID vid, ty) -> 
			EXPTY (E_VID vid, subst_type ty [s])
		| EXPTY (E_FUN mlist, ty) ->
			begin match mlist with
			| [] -> expty
			| M_RULE (patty, expty) :: tl ->
			let mrule' = M_RULE (subst_patty patty [s], subst_expty expty [s]) in
			let EXPTY (E_FUN mlist', _) = subst_expty (EXPTY (E_FUN tl, ty)) [s] in 
			EXPTY (E_FUN ([mrule'] @ mlist'), subst_type ty [s])
			end
		| EXPTY (E_APP (expty1, expty2), ty) -> 
			let expty1' = subst_expty expty1 [s] in 
			let expty2' = subst_expty expty2 [s] in
			EXPTY (E_APP (expty1', expty2'), subst_type ty [s])
		| EXPTY (E_PAIR (expty1, expty2), ty) -> 
			let expty1' = subst_expty expty1 [s] in 
			let expty2' = subst_expty expty2 [s] in
			EXPTY (E_PAIR (expty1', expty2'), subst_type ty [s])
		| EXPTY (E_LET (dec, exp), ty) -> 
			let dec' = subst_dec dec [s] in
			let exp' = subst_expty exp [s] in
			let expty' = E_LET (dec', exp') in
			EXPTY (expty', subst_type ty [s])
		| _ -> expty
		end
	in

	List.fold_left func expty ss   

and subst_mlist mlist ss = raise NotImplemented

and subst_dec dec ss =
    match dec with
    | D_VAL (patty, expty) -> 
	  D_VAL (subst_patty patty ss, subst_expty expty ss)
    | D_REC (patty, expty) -> 
	  D_REC (subst_patty patty ss, subst_expty expty ss)
    | D_DTYPE -> 
	  D_DTYPE
	| _ -> dec

let subst_venv venv ss =
	let func venv s = 
	  	let (s_var, _) = s in

	  	let subst v =
		  	let ((tyvars, ty'), is) = v in

			if mem s_var tyvars 
			then ((tyvars, ty'), is)
			else ((tyvars, subst_type ty' [s]), is)
	  	in
		
        map subst venv
	in
	
	List.fold_left func venv ss   

let subst_pair pair ss = 
	let func pair =
		let (ty1, ty2) = pair in
		(subst_type ty1 ss, subst_type ty2 ss)
	in

	List.map func pair

(* unify : (ty * ty) list -> substitution *)
let rec unify e =
	match e with
    | (T_INT, T_INT) :: t | (T_BOOL, T_BOOL) :: t | (T_UNIT, T_UNIT) :: t -> 
	  unify t
    | (T_NAME tyname1, T_NAME tyname2) :: t -> 
	  if tyname1 = tyname2 
	  then unify t
	  else []
    | (T_PAIR (ty11, ty12), T_PAIR (ty21, ty22)) :: t | (T_FUN (ty11, ty12), T_FUN (ty21, ty22)) :: t -> 
	  unify ((ty11, ty21) :: (ty12, ty22) :: t)
    | (T_VAR tyvar1, T_VAR tyvar2) :: t ->
      if tyvar1 = tyvar2 
	  then unify t
      else let s = (tyvar1, T_VAR tyvar2) in s :: (unify (subst_pair t [s]))
    | (T_VAR tyvar, ty) :: t | (ty, T_VAR tyvar) :: t ->
      if is_scheme_free_var (tyvar, ty) 
	  then []
      else let s = (tyvar, ty) in s :: (unify (subst_pair t [s]))
    | _ -> []


(* ty2ty : Ast.ty -> tenv -> Core.ty *)
let rec ty2ty ty te = 
	match ty with
	| Ast.T_INT -> T_INT
	| Ast.T_BOOL -> T_BOOL
	| Ast.T_UNIT -> T_UNIT
	| Ast.T_CON tycon -> T_NAME (try_lookup (lookup tycon te))
	| Ast.T_PAIR (t1, t2) -> T_PAIR (ty2ty t1 te, ty2ty t2 te)
	| Ast.T_FUN (t1, t2) -> T_FUN (ty2ty t1 te, ty2ty t2 te)

(* conbind2ty : Ast.conbinding -> tenv -> Ast.ty -> venv *)
let rec conbind2ty conbind te t = 
	let conbinding2ty conbinding te t = 
		match conbinding with
		| Ast.CB_VID vid' -> 
		  let ve' = (([], T_NAME t), CON) in
	  	  (vid', ve')
		| Ast.CB_TVID (vid', ty) ->
	  	  let ty = T_FUN (ty2ty ty te, T_NAME t) in
		  let ve' = (([], ty), CONF) in
	  	  (vid', ve')
	in

	match conbind with
	| [] -> []
	| ch::ct -> 
	  let ve_head = conbinding2ty ch te t in
	  insert ve_head (conbind2ty ct te t)

(* pat2ty : pat -> tctx -> (ty * pat * venv) *)
let rec pat2ty pat ctx =
	let (te, ve) = ctx in
	match pat with
	| Ast.P_WILD -> 
	  let alpha = get_fresh_tyvar() in
	  (T_VAR alpha, P_WILD, [])
	| Ast.P_INT n -> 
	  (T_INT, P_INT n, [])
	| Ast.P_BOOL b -> 
	  (T_BOOL, P_BOOL b, [])
	| Ast.P_UNIT -> 
	  (T_UNIT, P_UNIT, [])
	| Ast.P_VID vid' -> 
	  begin match (lookup vid' ve) with
	  | Some (_, VAR) | None ->
		let alpha = get_fresh_tyvar () in
		let ve' = [(vid', (([], T_VAR(alpha)), VAR))] in
		(T_VAR alpha, P_VID (vid', VAR), ve')
	  | Some (([], T_NAME t), CON) ->
		(T_VAR t, P_VID (vid', CON), [])
	  | _ -> raise TypingError
	  end
	| Ast.P_VIDP (vid, patty) ->
	let (ty', pat', pat'_ve) = pat2ty patty ctx in
	  let (vid_tsch, vid_is) = try_lookup (lookup vid ve) in
	  if vid_is <> CONF
	  then raise TypingError 
	  else begin match vid_tsch with
	  | ([], T_FUN(ty, T_NAME tyname)) ->
		let s = (unify [(ty, ty')]) in
		let patty' = subst_patty (PATTY (pat', ty')) s in
		let ve' = subst_venv pat'_ve s in
		(T_NAME tyname, P_VIDP ((vid, CONF), patty'), ve') end
	| Ast.P_PAIR (pat1, pat2) ->
	  let (ty1, pat1, ve1) = pat2ty pat1 ctx in
	  let (ty2, pat2, ve2) = pat2ty pat2 ctx in

	  let ve' = merge ve1 ve2 in
	  (T_PAIR (ty1, ty2), P_PAIR (PATTY (pat1, ty1), PATTY (pat2, ty2)), ve')
	| Ast.P_TPAT (patty, ty) ->
	  let (ty', pat', pat'_ve) = pat2ty patty ctx in
	  let PATTY (pat', ty') = subst_patty (PATTY (pat', ty')) (unify [(ty2ty ty te, ty')]) in
	  let ve' = subst_venv pat'_ve (unify [(ty2ty ty te, ty')]) in
	  (ty', pat', ve')

and print_subst ss = 
	let print_tyvar s = 
		let (tyvar, ty) = s in
		let _ = print_endline (string_of_int tyvar) in
		tyvar
	in 

	let _ = print_endline "***" in
	List.map print_tyvar ss

(* exp2ty : exp -> tctx -> ty * exp * (subst list) *)
and exp2ty exp ctx =
	let (te, ve) = ctx in
	match exp with
	| Ast.E_INT n ->  
	  (T_INT, E_INT n, [])
	| Ast.E_BOOL b ->  
	  (T_BOOL, E_BOOL b, [])
	| Ast.E_UNIT -> 
	  (T_UNIT, E_UNIT, [])
	| Ast.E_PLUS ->  
	  (T_FUN(T_PAIR(T_INT, T_INT), T_INT), E_PLUS, [])
	| Ast.E_MINUS ->  
	  (T_FUN(T_PAIR(T_INT, T_INT), T_INT), E_MINUS, [])
	| Ast.E_MULT ->  
	  (T_FUN(T_PAIR(T_INT, T_INT), T_INT), E_MULT, [])
	| Ast.E_EQ ->  
	  (T_FUN(T_PAIR(T_INT, T_INT), T_BOOL), E_EQ, [])
	| Ast.E_NEQ -> 
	  (T_FUN(T_PAIR(T_INT, T_INT), T_BOOL), E_NEQ, [])
	| Ast.E_VID vid ->
	  let ((tyvars, ty), is) = try_lookup (lookup vid ve) in
	  let f s tyvar = ([( tyvar, T_VAR(get_fresh_tyvar()) )] @ s) in
      let s = fold f [] tyvars in

	  (subst_type ty s, E_VID (vid, is), [])
	| Ast.E_FUN mlist ->
	  let (ty', exp', s') = mlist2ty mlist ctx in
	  (ty', exp', s')
	| Ast.E_APP (exp1, exp2) ->
	  let alpha = T_VAR (get_fresh_tyvar()) in

	  let (t1, e1, s1) = exp2ty exp1 ctx in
	  let (t2, e2, s2) = exp2ty exp2 (te, subst_venv ve s1) in
	  let s3 = unify [(subst_type t1 s2, T_FUN (t2, alpha))] in

	  let s' = s1 @ s2 @ s3 in
	  let ty' = subst_type alpha s3 in
	  let exp1' = subst_expty (EXPTY (e1, t1)) s' in
	  let exp2' = subst_expty (EXPTY (e2, t2)) s' in
	  (ty', E_APP (exp1', exp2'), s')
	| Ast.E_PAIR (exp1, exp2) ->
	  let (t1, e1, s1) = exp2ty exp1 ctx in
	  let _ = print_subst s1  in
	  let (t2, e2, s2) = exp2ty exp2 (te, subst_venv ve s1) in
	  let _ = print_subst s2 in

	  let s' = s1 @ s2 in
	  let expty' = EXPTY (E_PAIR (EXPTY (e1, t1), EXPTY (e2, t2)), T_PAIR (t1, t2)) in
	  let EXPTY (exp', ty') = subst_expty expty' s' in
	  (ty', exp', s')
	| Ast.E_LET (dec', exp') ->
	  let ((te', ve'), dec') = dec2ty dec' ctx in
	  let (ty', exp', s') = exp2ty exp' (te @ te', ve @ ve') in

	  let exp' = E_LET (dec', EXPTY (exp', ty')) in
	  (ty', exp', s')
	| Ast.E_TEXP (exp', ty') ->
	  let (ty, exp, s1) = exp2ty exp' ctx in
	  let s2 = unify [(ty, (ty2ty ty' te))] in

	  let EXPTY (exp', ty') = subst_expty (EXPTY(exp, ty)) (s1 @ s2) in
	  (ty', exp', [])
	| _ -> raise TypingError

(* mlist2ty : mlist -> tctx -> ty * exp * (subst list) *)
and mlist2ty mlist ctx = 
	match mlist with
	| hd :: [] ->
	  let (ty', exp', s') = mrule2ty hd ctx in
	  (ty', exp', s')

	| hd :: tl ->	
	  let (hd_type, hd_exp, _)  = mrule2ty hd ctx in
	  let (tl_type, tl_exp, _) = exp2ty (Ast.E_FUN tl) ctx in

	  let s' = unify [hd_type, tl_type] in
	  let EXPTY (E_FUN hd_mlist, hd_ty) = subst_expty (EXPTY (hd_exp, hd_type)) s' in
	  let EXPTY (E_FUN tl_mlist, tl_ty) = subst_expty (EXPTY (tl_exp, tl_type)) s' in
	  (subst_type tl_ty s', E_FUN (hd_mlist @ tl_mlist), s')

(* mrule2ty : mrule -> tctx -> ty * exp * (subst list) *)
and mrule2ty mrule ctx = 
	let (te, ve) = ctx in
	let Ast.M_RULE (pat, exp) = mrule in

	let (ty_pat, pat, ve') = pat2ty pat ctx in
	let (ty_exp, exp, s) = exp2ty exp (te, merge ve ve') in	
	let PATTY (pat, ty_pat) = subst_patty (PATTY(pat, ty_pat)) s in

	(T_FUN (ty_pat, ty_exp), E_FUN [M_RULE (PATTY (pat, ty_pat), EXPTY (exp, ty_exp))], s)

(* dec2ty Ast.dec -> tctx - > (tctx * dlist) *)
and dec2ty dec ctx = 
	let (te, ve) = ctx in
	match dec with
	| Ast.D_VAL (pat, exp) ->
	  let (ty_pat, pat, venv) = pat2ty pat ctx in
	  let (ty_exp, exp, _) = exp2ty exp ctx in
	  let sub = unify [(ty_pat, ty_exp)] in

	  let patty' = subst_patty (PATTY(pat, ty_pat)) sub in
	  let expty' = subst_expty (EXPTY(exp, ty_exp)) sub in
	  let decty' = D_VAL (patty', expty') in
	  let te' = [] in
	  let ve' = closure (subst_venv venv sub) ve []  in
	  ((te', ve'), decty')
	| Ast.D_REC (pat, exp) ->
	  let (ty_pat, pat, venv) = pat2ty pat ctx in
	  let (ty_exp, exp, _) = exp2ty exp (te, merge venv ve) in
	  let sub = unify [(ty_pat, ty_exp)] in

	  let patty' = subst_patty (PATTY(pat, ty_pat)) sub in
	  let expty' = subst_expty (EXPTY(exp, ty_exp)) sub in
	  let decty' = D_VAL (patty', expty') in
	  let te' = [] in
	  let ve' = closure (subst_venv venv sub) ve []  in
	  ((te', ve'), decty')
	| Ast.D_DTYPE (tycon, conbinding) ->
	  let alpha = get_fresh_tyname () in
	  let decty' = D_DTYPE in
	  let te' = insert (tycon, alpha) te in
	  let ve' = conbind2ty conbinding te' alpha in
	  ((te', ve'), decty')

let rec dlist2ty dlist ctx = 
	let (te, ve) = ctx in
	match dlist with
	| [] -> ((te, ve), [])
	| dh::dt -> 
	  let ((te_head, ve_head), dec_head) = dec2ty dh ctx in
	  let ((te_tail, ve_tail), dec_tail) = dlist2ty dt (te @ te_head, ve @ ve_head) in
	  ((te @ te_head @ te_tail, ve @ ve_head @ ve_tail), [dec_head] @ dec_tail)

(* tprogram : Ast.program -> Core.program *)
let tprogram (dlist, exp) =
	let (ctx, decty) = dlist2ty dlist tctx0 in
	let (ty, exp, _) = exp2ty exp ctx in
	(decty, EXPTY (exp, ty))
