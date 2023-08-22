type cmp_res = LT | GT | EQ

let compare l r = 
   if l < r then LT 
   else if l = r then EQ 
   else GT

exception Unimplemented

type type_var = string
type ident = string

module FVSet = Set.Make(String)
module TypeEnv = CCPersistentHashtbl.Make(struct
   type t = ident
   let equal s t = s = t
   let hash = Hashtbl.hash
end)

type ty = 
   | TyInt
   | TyF64
   | TyStr
   | TyBool
   | TyType
   | TyKeyword
   | TyTuple of ty list
   | TyList of ty
   | TyLam of ty * ty (* we have currying *)
   | TyVar of type_var
   | TyForAll of type_var * ty (* multiple Forall's should be chained *)

type unify_error_reason = 
     InfiniteSubstitution
   | TupleLengthMismatch
   | CantUnifyBetween of ty * ty
exception UnifyError of unify_error_reason

type type_env = ty TypeEnv.t

let tyUnit = TyTuple []

type 'a exp_prim = 
   | Atom of (Ast.atom * 'a)
   | Val of (ident * 'a)
   | Tuple of ('a exp_prim list * 'a)
   | List of ('a exp_prim list * 'a)
   | Let of (ident * 'a exp_prim * 'a exp_prim * 'a)
   | If of ('a exp_prim * 'a exp_prim * 'a exp_prim * 'a)
   | App of ('a exp_prim * 'a exp_prim * 'a)
   (* I should call this Abstraction instead to closely match lambda abstraction *)
   | Lam of (ident * 'a exp_prim * 'a)
   (* Our low-level try only have 2 options: succeeds in first branch, or fallback to the second *)
   | Try of ('a exp_prim * 'a exp_prim * 'a)
   | Seq of ('a exp_prim list * 'a)

type ty_constraint = ty * ty
type ty_constraints = ty_constraint list

type exp_prim_input = unit exp_prim

type exp_prim_annotated = ty exp_prim

let take_annotated_type (e : exp_prim_annotated) : ty =
   match e with 
   | Atom (_, t) -> t
   | Val (_, t) -> t
   | Tuple (_, t) -> t
   | List (_, t) -> t
   | Let (_, _, _, t) -> t
   | If (_, _, _, t) -> t
   | App (_, _, t) -> t
   | Lam (_, _, t) -> t
   | Try (_, _, t) -> t
   | Seq (_, t) -> t

let put_annotated_type (e: exp_prim_annotated) (ty : ty) : exp_prim_annotated =
   match e with 
   | Atom (a, _) -> Atom(a, ty)
   | Val (v, _) -> Val(v, ty)
   | Tuple (t, _) -> Tuple(t, ty)
   | List (l, _) -> List (l, ty)
   | Let (s, b, i, _) -> Let(s, b, i, ty)
   | If (c, t, f, _) -> If(c, t, f, ty)
   | App (f, x, _) -> App(f, x, ty)
   | Lam (p, b, _) -> Lam (p, b, ty)
   | Try (t, f, _) -> Try(t, f, ty)
   | Seq (s, _) -> Seq(s, ty)

let rec free_variables (t: ty) : FVSet.t =
   match t with
   | TyVar(v) -> FVSet.singleton v
   | TyTuple(l) -> 
      let sets = List.map free_variables l in
         List.fold_right FVSet.union sets FVSet.empty
   | TyList t -> free_variables t
   | TyLam(param, ret) -> 
      FVSet.union (free_variables param) (free_variables ret)
   | TyForAll(fv, inner) ->
      FVSet.remove fv (free_variables inner)
   | _ -> FVSet.empty

let free_variables_env (env: type_env) : FVSet.t =
   TypeEnv.fold (fun s _ t -> FVSet.union s (free_variables t)) FVSet.empty env

let occurs (v : type_var) (t: ty) =
   FVSet.mem v (free_variables t)

type subst = (type_var * ty) list

let subst_on_typ (sub: subst) (t: ty) : ty = 
   let rec sub1 s in_ty =
      let (tyvar, to_ty) = s in
         match in_ty with
         | TyVar(v) when v = tyvar -> to_ty
         | TyTuple(l) -> TyTuple(List.map (sub1 s) l)
         | TyList t -> TyList (sub1 s t)
         | TyLam(param, ret) -> TyLam (sub1 s param, sub1 s ret)
         | TyForAll(fv, inner) when tyvar != fv ->
            TyForAll(fv, sub1 s inner)
         | any -> any
   in
   List.fold_right sub1 sub t 

let subst_on_subst (src: subst) (dest: subst) : subst =
   List.map (fun (id, ty) -> (id, subst_on_typ src ty)) dest

let subst_on_constraints (sub: subst) (cs: ty_constraints) : ty_constraints = 
   List.map (fun (t1, t2) -> (subst_on_typ sub t1, subst_on_typ sub t2)) cs

let subst_on_env (sub: subst) (env: type_env) : type_env = 
   TypeEnv.map (fun _ t -> subst_on_typ sub t) env

let rec subst_on_exp_annotated (sub: subst) (e : exp_prim_annotated) : exp_prim_annotated =
   let subt = subst_on_typ sub in
   let sube = subst_on_exp_annotated sub in 
   match e with
   | Atom(v, t) -> Atom(v, subt t)
   | Val(id, t) -> Val(id, subt t)
   | Tuple(es, t) -> 
      Tuple(List.map sube es, subt t)
   | List(es, t) -> 
      List(List.map sube es, subt t)
   | Let (id, exp, body, t) -> 
      Let(id, sube exp, sube body, subt t)
   | If (cond, _then, _else, t) -> 
      If(sube cond, sube _then, sube _else, subt t)
   | App (f, x, t) ->
      App(sube f, sube x, subt t)
   | Lam (id, body, t) ->
      Lam(id, sube body, subt t)
   | Try (tried, fail, t) ->
      Try(sube tried, sube fail, subt t)
   | Seq (es, t) ->
      Seq (List.map sube es, subt t)

(* compose_subst(sub2, sub1) ty = sub2(sub1(ty)) *)
let compose_subst (sub2: subst) (sub1: subst) : subst = 
   sub2 @ (subst_on_subst sub2 sub1) 

let gensym = 
   let count = ref 0 in 
   let next () = count := !count + 1; !count
   in fun prefix -> prefix ^ string_of_int (next ())

let instantiate (ty: ty) : ty =
   match ty with 
   | TyForAll(v, inner) -> 
      let instantiate = gensym ("instantiate_" ^ v) in
         subst_on_typ [(v, TyVar instantiate)] inner
   | _ -> ty

let rec unify_one (c: ty_constraint) : subst = 
   match c with
   | (TyVar(v1), t2) ->
      if occurs v1 t2 then
         raise (UnifyError InfiniteSubstitution)
      else
         [(v1, t2)]
   | (t1, TyVar(v2)) ->
      if occurs v2 t1 then
         raise (UnifyError InfiniteSubstitution)
      else
         [(v2, t1)]
   | (TyTuple t1s, TyTuple t2s) ->
      if List.length t1s = List.length t2s then
         unify (List.combine t1s t2s)
      else
         raise (UnifyError TupleLengthMismatch)
   | (TyList t1, TyList t2) ->
      unify_one (t1, t2)
   | (TyLam (p1, r1), TyLam (p2, r2)) ->
      compose_subst 
         (unify_one (p1, p2))
         (unify_one (r1, r2))
   | (TyForAll (v, inner), rhs) ->
      unify_one ((instantiate (TyForAll (v, inner))), rhs)
   | (lhs, TyForAll (v, inner)) ->
      unify_one (lhs, (instantiate (TyForAll (v, inner))))
   | (lhs, rhs) -> 
      if lhs = rhs 
      then []
      else raise (UnifyError (CantUnifyBetween(lhs, rhs)))

and unify (cs: ty_constraints): subst = 
   match cs with 
   | [] -> []
   | c :: rest -> 
      let c_subst = unify_one c in
         (* there's no need to use compose here, as we already subsitute on the constratints as a whole *)
         (unify (subst_on_constraints c_subst rest)) @ c_subst

let generalize (env : type_env) (ty : ty) (cons: ty_constraints): ty = 
   (* Cons is the contraint we got by inferring some expression, 
      ty is the type returned. 
      What we need to do now is to *)
   let subst = unify cons in
   let env_inferred = subst_on_env subst env in
   let ty_subst = subst_on_typ subst ty in 
   (* Any free variables in the substituted type but not in the substituted environment are variables 
      that can't be inferred, we need to generalize,
      we are free to reuse the constraints *)
   let fvs = FVSet.diff (free_variables ty_subst) (free_variables_env env_inferred) in
      FVSet.fold (fun id ty -> TyForAll(id, ty)) fvs ty_subst

let rec infer_constraints (env: type_env) (exp : exp_prim_input) : (exp_prim_annotated * ty_constraints) = 
   match exp with 
   | Atom (Bool b, _) -> Atom (Bool b, TyBool), []
   | Atom (Int i, _) -> Atom (Int i, TyInt), []
   | Atom (F64 f, _) -> Atom (F64 f, TyF64), []
   | Atom (Str s, _) -> Atom (Str s, TyStr), []
   | Atom (Keyword k, _) -> Atom (Keyword k, TyKeyword), []
   | Val (id, _) -> 
      Val (id, TyVar (gensym ("var_" ^ id))), []
   | Tuple (exps, _) ->
      let exps, constraints_list = List.map (infer_constraints env) exps |> List.split in
      let inner_tys = List.map take_annotated_type exps in
      let constraints = List.concat constraints_list in
      Tuple (exps, TyTuple inner_tys), constraints
   | List (exps, _) -> 
      let exps, constraints_list = List.map (infer_constraints env) exps |> List.split in
      let inner_tys = List.map take_annotated_type exps in
      let constraints = List.concat constraints_list in
      begin match inner_tys with
      | [] -> 
         let f = gensym "list" in
            List (exps, (TyList (TyVar f))), constraints
      | [only] -> 
         List (exps, TyList only), constraints
      | first :: rest -> 
         List (exps, TyList first), constraints @ (List.map (fun ty -> ty, first) rest) 
      end
   | Let (id, bind, inner, _) -> 
      let bind, bind_cons = infer_constraints env bind in
      let bind_ty = take_annotated_type bind in
      let bind_ty_generalize = generalize env bind_ty bind_cons in
      let env_bind = TypeEnv.add env id bind_ty_generalize in
      let bind_generalized = put_annotated_type bind bind_ty_generalize in
      let inner, inner_cons = infer_constraints env_bind inner in
         Let (id, bind_generalized, inner, take_annotated_type inner), bind_cons @ inner_cons
   | If (_test, _then, _else, _) ->
      let _test, test_constraint = infer_constraints env _test in
      let ty_test = take_annotated_type _test in
      let _then, then_constraint = infer_constraints env _then in
      let ty_then = take_annotated_type _then in
      let _else, else_constraint = infer_constraints env _else in
      let ty_else = take_annotated_type _else in
         If (_test, _then, _else, ty_then), 
         test_constraint @ 
         then_constraint @ 
         else_constraint @
         [ty_test, TyBool; ty_then, ty_else]
   | App (fn, par, _) ->
      let fn, fn_cons = infer_constraints env fn in
      let ty_fn = take_annotated_type fn in
      let par, par_cons = infer_constraints env par in 
      let ty_par = take_annotated_type par in
      let out = gensym "app_ret" in
         App (fn, par, TyVar out), 
         fn_cons @ par_cons @ [ty_fn, TyLam(ty_par, (TyVar out))]
   | Lam (param, body, _) ->
      let param_ty = TyVar (gensym ("lam_param" ^ param)) in
      let env_updated = TypeEnv.add env param param_ty in
      let body, body_cons = infer_constraints env_updated body in
      let ty_body = take_annotated_type body in
         Lam (param, body, TyLam (param_ty, ty_body)), body_cons
   | Try (_try, _catch, _) ->
      let _try, try_constraint = infer_constraints env _try in
      let ty_try = take_annotated_type _try in
      let _catch, catch_constraints = infer_constraints env _catch in
      let ty_catch = take_annotated_type _catch in
         Try (_try, _catch, ty_try), 
         try_constraint @
         catch_constraints @
         [ty_try, ty_catch]
   | Seq (exps, _) ->
      let exps, constraints_list = List.map (infer_constraints env) exps |> List.split in
      let inner_tys = List.map take_annotated_type exps in
      let constraints = List.concat constraints_list in
         if List.length exps = 0 
         then Tuple ([], tyUnit), constraints
         else Seq (exps, inner_tys |> List.rev |> List.hd), constraints

let infer_and_generalize (env: type_env) (exp: exp_prim_input) : exp_prim_annotated = 
   let annotated, cons = infer_constraints env exp in
   let ty_annotated = take_annotated_type annotated in  
   let ty_generalized = generalize env ty_annotated cons in
   let annotated_generalized = put_annotated_type annotated ty_generalized in
      annotated_generalized 
