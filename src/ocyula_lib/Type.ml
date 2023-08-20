(* This is the Hindly Miller Type Checking Algorithm with some modification *)
type type_var = string

exception Unimplemented

module FVSet = struct
   include Set.Make(String)
   let pp fmt (s : t) : unit = 
      s
      |> map (fun s -> "`" ^ s ^ "`")
      |> fun s -> fold (fun e arr -> e :: arr) s []
      |> String.concat ", "
      |> Format.fprintf fmt "{%s}"
end

module TypeEnv = CCPersistentHashtbl.Make(struct
   type t = Ast.ident
   let equal s t = s = t
   let hash = Hashtbl.hash
end)

type ty = 
   | TyInt
   | TyStr
   | TyF64
   | TyBool
   | TyType
   | TyKeyword
   | TyTuple of ty list
   | TyList of ty
   | TyLam of ty list * ty
   | TyVar of type_var [@printer fun fmt -> fprintf fmt "%s"]
   | TyForall of FVSet.t * ty (* polymorphic types *)
   (* | TyApp *) (* If we have generics *)
[@@deriving show]

let tyUnit = TyTuple []

type type_env = ty TypeEnv.t

(* TODO: typing for pattern *)
type pattern =
   | Bind of Ast.ident * ty (* creates new binding *)
   | Pin of Ast.ident * ty (* match with exisiting value *)
   (* For Lens pattern, we force the last param to be a pattern as well so we may match on it. *)
   | Lens of pattern * Ast.ident * typed_exp list * ty
            (* A          B           (c, d, e)        T*)
            (* A.B(c, d, e) as T *)
   | PatTuple of pattern list * ty
   | PatList of pattern list * ty
   | Lit of Ast.atom * ty

and typed_exp =
   | TAtom of Ast.atom * ty
   | TVal of Ast.ident * ty 
   | TMatch of pattern * typed_exp * ty
   | TTuple of typed_exp list * ty
   | TList of typed_exp list * ty
   | TIf of typed_exp * typed_exp list * typed_exp list * ty
   | TCall of Ast.ident * typed_exp list * ty
   | TLam of Ast.ident list * typed_exp list * ty
   | TCase of typed_exp * (pattern * typed_exp list) list * ty
   | TSeq of typed_exp list * ty

(* let check_exp (env : type_env) (exp : Ast.exp) = 1 *)
(* and  exp_to_pat (env : type_env) (exp : Ast.exp) = 1 *)

type subst = (type_var * ty) list

exception Type_error of string

let rec subst_var_scheme ((tyvar : type_var), (to_typ: ty)) (in_typ: ty) : ty = 
   match in_typ with
   | TyVar(v) when v = tyvar -> to_typ
   | TyTuple(l) -> TyTuple(List.map (subst_var_scheme (tyvar, to_typ)) l)
   | TyList t -> TyList (subst_var_scheme (tyvar, to_typ) t)
   | TyLam(params, ret) -> TyLam (List.map (subst_var_scheme (tyvar, to_typ)) params, subst_var_scheme (tyvar, to_typ) ret)
   | TyForall(fvs, inner) ->
      if FVSet.mem tyvar fvs then TyForall(fvs, inner)
      else TyForall(fvs, subst_var_scheme (tyvar, to_typ) inner)
   | any -> any

let apply_subst_typ (subst: subst) (t: ty) : ty =
   List.fold_right subst_var_scheme subst t  

let apply_subst_typeenv (subst: subst) : (type_env -> type_env) = TypeEnv.map (fun _ ty -> apply_subst_typ subst ty)
   
(* apply substitution src on dest *)
let apply_subst_subst (src : subst) (dest: subst) : subst =
   List.map (fun (id, ty) -> (id, apply_subst_typ src ty)) dest

(* apply sub1 and then apply sub2 *)
let compose_subst (sub1: subst) (sub2: subst) : subst = 
   (apply_subst_subst sub2 sub1) @ sub2

let compose_substs (subs: subst list) : subst = 
   List.fold_left compose_subst [] subs

let rec free_variables (t: ty) : FVSet.t =
   match t with
   | TyVar(v) -> FVSet.singleton v
   | TyTuple(l) -> 
      let sets = List.map free_variables l in
         List.fold_right FVSet.union sets FVSet.empty
   | TyList t -> free_variables t
   | TyLam(params, ret) -> 
      let sets = List.map free_variables params in
         List.fold_right FVSet.union sets (free_variables ret)
   | TyForall(fvs, inner) ->
      FVSet.diff (free_variables inner) fvs
   | _ -> FVSet.empty

let occurs (v: type_var) (t: ty) = 
   FVSet.mem v (free_variables t) 

let gensym = 
   let count = ref 0 in 
   let next () = 
      count := !count + 1;
      !count
   in fun str -> TyVar (Printf.sprintf "%s_%d" str (next ()))

let instantiate (fvs: FVSet.t) (ty: ty) : ty = 
   let alpha_equiv_subst = FVSet.fold (fun s subst -> (s, gensym s) :: subst) fvs [] in 
      apply_subst_typ alpha_equiv_subst ty

type cmp_res = LT | GT | EQ

let compare l r = 
   if l < r then LT 
   else if l = r then EQ 
   else GT

exception Split_error of string
let rec split_at l i = 
   if i < 0 then
      raise (Split_error "splitting with negative index")
   else if i == 0 then
      ([], l)
   else 
      match l with
      | a :: rest ->
         let (leftl, rightl) = split_at rest (i - 1) in
            (a :: leftl, rightl)
      | [] -> raise (Split_error "list too short")

let rec unify_tuple (t1: ty list) (t2: ty list) : subst = 
   if List.length t1 = List.length t2 then 
      List.combine t1 t2
      |> List.map (fun (l, r) -> unify l r)
      |> compose_substs
   else raise (Type_error (Printf.sprintf "Can't unify between %s and %s" (show_ty (TyTuple t1)) (show_ty (TyTuple t2))))
and unify (t1: ty) (t2: ty) : subst = 
   match (t1, t2) with
   | (lhs, rhs) when lhs = rhs -> []
   | (TyVar(t1v), t2) -> 
      if (occurs t1v t2) then 
         raise (Type_error (Printf.sprintf "Nested unify between %s and %s" (show_ty t1) (show_ty t2)))
      else 
         [(t1v, t2)]
   | (t1, TyVar(t2v)) -> 
      if (occurs t2v t1) then 
         raise (Type_error (Printf.sprintf "Nested unify between %s and %s" (show_ty t1) (show_ty t2)))
      else 
         [(t2v, t1)]
   | (TyTuple t1, TyTuple t2) -> unify_tuple t1 t2
   | (TyList tleft, TyList tright) -> unify tleft tright
   | (TyLam(argl, retl), TyLam(argr, retr)) ->
      (* We need to take currying into consideration *)
      let len_l = List.length argl in
      let len_r = List.length argr in
         begin match compare len_l len_r with
         | EQ -> 
            compose_subst (unify_tuple argl argr) (unify retl retr)
         | LT -> 
            let (r_match, r_rest) = split_at argr len_l in 
            let rest_unified = unify retl (TyLam (r_rest, retr)) in
            compose_subst (unify_tuple argl r_match) rest_unified 
         | GT ->
            let (l_match, l_rest) = split_at argl len_r in 
            let rest_unified = unify (TyLam (l_rest, retl)) retr in
            compose_subst (unify_tuple l_match argr) rest_unified 
         end
   | (TyForall(fvs, inner), t2) -> 
      unify (instantiate fvs inner) t2
   | (t1, TyForall(fvs, inner)) -> 
      unify t1 (instantiate fvs inner)
   | _ -> raise (Type_error (Printf.sprintf "Can't unify between %s and %s" (show_ty t1) (show_ty t2)))

exception IndexOutOfBound

let rec last l = 
   match l with
   | [x] -> x
   | _ :: rest -> last rest
   | _ -> raise IndexOutOfBound

(* NOTE: return value for infer function is a 3-tuple (t, s, out),
   where e is the alterred env(there might be new bindings introduced), 
   s is the subsitution on exisiting types, 
   out is the return type *)
let rec infer_pattern_series (env : type_env) (pats : Ast.exp list) : type_env * subst * ty list = 
   match pats with 
   | [] -> (env, [], [])
   | first :: rest -> 
      let env, subst_first, ty_first = infer_pattern env first in 
      (* let env = apply_subst_typeenv subst_first env in *)
      let env, subst_rest, tys_rest = infer_pattern_series env rest in
      env, compose_subst subst_first subst_rest, ty_first :: tys_rest

and infer_pattern (env : type_env) (pattern : Ast.exp) : type_env * subst * ty = 
   match pattern with
   | Atom (Int _)     -> env, [], TyInt
   | Atom (F64 _)     -> env, [], TyF64
   | Atom (Str _)     -> env, [], TyStr
   | Atom (Keyword _) -> env, [], TyKeyword
   | Val id           -> 
      let ty_sym = gensym id in
      let new_env = TypeEnv.add env id ty_sym in
      new_env, [], ty_sym
   | Tuple exps -> 
      let env, sub, list = infer_pattern_series env exps in 
      env, sub, TyTuple list
   | List exps -> 
      let env, sub, tys = infer_pattern_series env exps in
      begin match tys with
      | [] -> env, sub, TyList (gensym "list")
      | [only] -> env, sub, TyList only
      | first :: rest -> 
         let sub = List.map (unify first) rest |> compose_substs in
         env, sub, TyList (apply_subst_typ sub first)
      end
   | _ -> raise Unimplemented

and infer_series (env : type_env) (exps : Ast.exp list) : type_env * subst * ty list = 
   match exps with 
   | [] -> (env, [], [])
   | first :: rest -> 
      let env, subst_first, ty_first = infer_exp env first in 
      (* let env = apply_subst_typeenv subst_first env in *)
      let env, subst_rest, tys_rest = infer_series env rest in
      env, compose_subst subst_first subst_rest, ty_first :: tys_rest

and infer_pattern_match (env : type_env) (lhs : Ast.exp) (rhs : Ast.exp) : type_env * subst * ty =
   let env, subl, ty_lhs = infer_pattern env lhs in
   let env, subr, ty_rhs = infer_exp env rhs in

   let sub_match = unify ty_lhs ty_rhs in
   let sub_final = compose_substs [subl; subr; sub_match] in

   apply_subst_typeenv sub_final env, sub_final, apply_subst_typ sub_final ty_rhs

and infer_exp (env : type_env) (exp : Ast.exp): type_env * subst * ty = 
   match exp with
   | Atom (Int _)     -> env, [], TyInt
   | Atom (F64 _)     -> env, [], TyF64
   | Atom (Str _)     -> env, [], TyStr
   | Atom (Keyword _) -> env, [], TyKeyword
   | Val id           -> env, [], TypeEnv.find env id
   | Tuple exps -> 
      let env, sub, list = infer_series env exps in 
      env, sub, TyTuple list
   | List exps -> 
      let env, sub, tys = infer_series env exps in
      begin match tys with
      | [] -> env, sub, TyList (gensym "list")
      | [only] -> env, sub, TyList only
      | first :: rest -> 
         let sub = List.map (unify first) rest |> compose_substs in
         env, sub, TyList (apply_subst_typ sub first)
      end
   | Call("!match", [_lhs; _rhs]) ->
      infer_pattern_match env _lhs _rhs
   | Call(fn, params) -> 
      let ty_fn = TypeEnv.find env fn in

      let [@warning "-8"] env, sub_inner, TyTuple ty_params = infer_exp env (Tuple params) in
      let ret_type = gensym "ret" in
      let ty_fn_instantiated = TyLam(ty_params, ret_type) in

      let sub_call = unify ty_fn ty_fn_instantiated in 
      let final_sub = compose_subst sub_inner sub_call in

      apply_subst_typeenv final_sub env, final_sub, apply_subst_typ final_sub ret_type 
   | Lam(params, body) ->
      let updateEnv env param =
         TypeEnv.add env param (gensym ("lam_arg" ^ param))
      in
      let env_body = List.fold_left updateEnv env params in
      (* NOTE: no bindings will be leaked outside of a lambda function *)
      let _, subst, ret_inferred = infer_exp env_body (Tuple body) in
      let params_inferred = 
         params 
         |> List.map (TypeEnv.find env_body) 
         |> List.map (apply_subst_typ subst) 
      in
      apply_subst_typeenv subst env, subst, TyLam(params_inferred, ret_inferred)
   | If(_cond, _then, _else) ->
      (* NOTE: no bindings will be introduced by a if statement *)
      let [@warning "-8"] _, sub_inner, [ty_cond; TyTuple ty_then_tup; TyTuple ty_else_tup] =
         infer_series env [_cond; Tuple _then; Tuple _else] in
      let ty_then = last ty_then_tup in
      let ty_else = last ty_else_tup in

      let sub_test = unify TyBool ty_cond in
      let sub_body = unify ty_then ty_else in

      let sub_final = compose_substs [sub_inner; sub_test; sub_body] in 
      apply_subst_typeenv sub_final env, sub_final, apply_subst_typ sub_final ty_then
   | Case(matched, cases) -> 
         let infer_case env (case: (Ast.exp * Ast.exp list)) : (subst * ty) = 
            let pat, body = case in
            (* drop the env as we should not leak *)
            let _, subst, ret = infer_exp env (Seq (Call("!match", [pat; matched]) :: body)) in
            subst, ret
         in
         let infer_cases env (cases : (Ast.exp * Ast.exp list) list) : (subst * ty) list =  
            List.map (infer_case env) cases 
         in
         (* NOTE: no bindings will be introduced by a case statement *)
         let env_inner, _, _ = infer_exp env matched in
         let substs, tys = infer_cases env_inner cases |> List.split in
         begin match tys with 
         | [only] -> 
            env, compose_substs substs, only
         | [] -> raise Unimplemented
         | first :: rest -> 
            let subs = List.map (unify first) rest in
            let sub_final = compose_substs (substs @ subs) in
            apply_subst_typeenv sub_final env, sub_final, apply_subst_typ sub_final first
         end
   | Seq exps -> 
      let env, sub, list = infer_series env exps in 
         if List.length list = 0 
         then env, sub, tyUnit
         else env, sub, last list
   | _ -> raise Unimplemented
