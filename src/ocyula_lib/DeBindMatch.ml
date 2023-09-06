open Ast

type updatable = 
   | Bind of ident
   | Lens of updatable * ident * exp list
             (* obj    . method  (arg1, arg2, ...) *)
and pat = 
   | Updatable of updatable
   | Union of pat list
   | With of pat * exp
   (* NOTE:
      we have some ADT:
      type f = 
      | Left of int
      | Right of unit
      Left i | Right () with (i = 3) = Right()
      exists solely for balancing the variables on both side of a union pattern
   *)
   | Pin of ident
   | PatTuple of pat list
   | PatList of pat list
   | PLit of atom
   | PAny

and exp = 
   | Assert of exp
   | Val of ident
   | Lit of atom
   | Bin of exp * bin_op * exp
   | Un of un_op * exp
   | Seq of exp list
   | If of exp * exp * exp
   | Tuple of exp list
   | List of exp list
   | Lambda of ident list * exp
   | Call of ident * exp list 
   | BindStmt of ident * exp
   | KthTuple of exp * int (* we may remove this from primitives later if we have a dependent type system *)
   | UnPin of ident (* refer to the previous definition, rather than the closest*)
   | CaseMatch of exp * (pat * exp * exp) list
   | Annotate of exp * Type.ty

module IDSet = Set.Make(struct
   type t = ident
   let compare = compare
end)

let rec collect_binds_upd_pat : (Ast.updatable -> IDSet.t) = function
   | Bind i -> IDSet.singleton(i)
   | Lens(u, _, _) -> collect_binds_upd_pat u
and collect_binds_pat : (Ast.pat -> IDSet.t) = function
   | Updatable u -> collect_binds_upd_pat u
   (* checking unions aren't malformed are done later *)
   | Union ps -> collect_binds_pat (List.hd ps)
   | PAny | Pin _ | PLit _ -> IDSet.empty
   | With(_p, _e) -> raise Unimplemented
   | PatTuple ps | PatList ps -> 
      begin match ps |> List.map collect_binds_pat with
      | first :: rest -> List.fold_left IDSet.union first rest 
      | [] -> IDSet.empty
      end

let rec deBindMatch_upd_pat : Ast.updatable -> updatable = function 
   | Bind i -> Bind i
   | Lens(u, m, es) -> Lens(deBindMatch_upd_pat u, m, List.map deBindMatch es)
and deBindMatch_pat : Ast.pat -> pat = function 
   | Updatable u -> Updatable (deBindMatch_upd_pat u)
   | Union ps -> Union (List.map deBindMatch_pat ps)
   | With(p, e) -> With(deBindMatch_pat p, deBindMatch e)
   | PAny -> PAny
   | Pin id -> Pin id
   | PLit l -> PLit l
   | PatTuple ps -> PatTuple(List.map deBindMatch_pat ps)
   | PatList ps -> PatList(List.map deBindMatch_pat ps)
and deBindMatch (e: Ast.exp) : exp = 
   let fs = List.map deBindMatch in
   match e with
   | Lambda(pats, e) ->
      let pat_syms = 
         gensyms (List.length pats) 
         |> List.map (fun i -> Gensym i)
      in let pat_binds = 
         List.combine pats pat_syms
         |> List.map (fun (p, s) -> BindMatch(p, Val s))
      in let binds_dematched = deBindMatch(Seq(pat_binds))
      in
      Lambda(pat_syms, Seq[binds_dematched; deBindMatch e])
   | BindMatch(p, e) -> 
      let binds = collect_binds_pat p |> IDSet.to_seq |> List.of_seq in
      let binds_val = List.map (fun b -> Ast.Val b) binds  in
      let tmp_bind_all = gensym() in 
         Seq (
            [BindStmt(
               Gensym tmp_bind_all, 
               deBindMatch(
                  CaseMatch(e, 
                  [(p, Lit(Bool true), Tuple binds_val);
                   (PAny, Lit(Bool true), Assert(Lit(Bool false)))])))] @
            List.mapi (fun i b -> BindStmt(b, KthTuple(Val(Gensym tmp_bind_all), i))) binds 
         )
   | Assert(e) -> Assert(deBindMatch e)
   | Val(i) -> Val(i)
   | Lit(a) -> Lit(a)
   | Bin(lhs, op, rhs) -> Bin(deBindMatch lhs, op, deBindMatch rhs)
   | Un(op, e) -> Un(op, deBindMatch e)
   | Seq(es) -> Seq(fs es)
   | If(test, _then, _else) -> If(deBindMatch test, deBindMatch _then, deBindMatch _else)
   | Tuple(es) -> Tuple(fs es)
   | List(es) -> List(fs es)
   | Call(id, es) -> Call(id, fs es)
   | UnPin(id) -> UnPin(id)
   | CaseMatch(e, bs) -> 
      let f_branch (pat, cond, e) = (deBindMatch_pat pat, deBindMatch cond, deBindMatch e) in
         CaseMatch(deBindMatch e, List.map f_branch bs)
   | Annotate(e, ty) -> Annotate(deBindMatch e, ty)
