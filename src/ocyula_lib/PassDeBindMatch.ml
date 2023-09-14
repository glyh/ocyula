open Ast

type src = PassDeSeq.dst
type dst = <
   seq: no;
   pattern: yes;
   lambda: yes;
   call: yes;
   recbind: yes; 
   unique_id: no;
   bind_only: yes;
   letin: no>

module IDSet = Set.Make(struct
   type t = src id_t
   let compare = compare
end)

let rec collect_binds_upd_pat : (src upd_pat_t -> IDSet.t) = function
   | Bind i -> IDSet.singleton(i)
   | Lens(u, _, _) -> collect_binds_upd_pat u
and collect_binds_pat : (src pat_t -> IDSet.t) = function
   | Updatable u -> collect_binds_upd_pat u
   (* checking unions aren't malformed are done later *)
   | Union ps -> collect_binds_pat (List.hd ps)
   | PAny _ | Pin _ | PLit _ -> IDSet.empty
   | With(_p, _e) -> raise Unimplemented
   | PatTuple ps | PatList ps -> 
      begin match ps |> List.map collect_binds_pat with
      | first :: rest -> List.fold_left IDSet.union first rest 
      | [] -> IDSet.empty
      end

let rec de_bind_match: type a. (a, src) gen_ast -> (a, dst) gen_ast = function
   | LamPat(pats, exps) -> 
      let pat_syms = 
         gensyms (List.length pats)
         |> List.map (fun i -> Gensym i)
      in let pat_binds = 
         List.combine pats pat_syms
         |> List.map (fun (p, s) -> BindMatch(p, Val s))
      in let binds_dematched = de_bind_match (Seq(pat_binds)) 
      in
      Lam(List.map de_bind_match pat_syms, Seq[binds_dematched; de_bind_match exps])

   | BindMatch(p, e) -> 
      let binds = collect_binds_pat p |> IDSet.to_seq |> List.of_seq in
      let binds_val = List.map (fun b -> Ast.Val b) binds  in
      let tmp_bind_all_sym = gensym() in
      let tmp_bind_all: dst exp_t = BindOnly(
               Gensym (tmp_bind_all_sym), 
               de_bind_match(CaseMatch(
                  e, 
                  [(p, Lit(Bool true), Tuple binds_val)])))
      in
         Seq (
            [ tmp_bind_all ] 
            @ List.mapi 
               (fun i b -> BindOnly(b, KthTuple(Val(Gensym tmp_bind_all_sym), i))) 
               (List.map de_bind_match binds) 
         )

   | Assert _ as e -> shallow_map {f = de_bind_match} e
   | Concrete _ as e -> shallow_map {f = de_bind_match} e
   | Gensym _ as e -> shallow_map {f = de_bind_match} e
   | Bind _ as e -> shallow_map {f = de_bind_match} e
   | Lens _ as e -> shallow_map {f = de_bind_match} e
   | Union _ as e -> shallow_map {f = de_bind_match} e
   | Updatable _ as e -> shallow_map {f = de_bind_match} e
   | Pin _ as e -> shallow_map {f = de_bind_match} e
   | PatTuple _ as e -> shallow_map {f = de_bind_match} e
   | PatList _ as e -> shallow_map {f = de_bind_match} e
   | PLit _ as e -> shallow_map {f = de_bind_match} e
   | PAny _ as e -> shallow_map {f = de_bind_match} e
   | With _ as e -> shallow_map {f = de_bind_match} e
   | Val _ as e -> shallow_map {f = de_bind_match} e
   | Lit _ as e -> shallow_map {f = de_bind_match} e
   | Binary _ as e -> shallow_map {f = de_bind_match} e
   | Unary _ as e -> shallow_map {f = de_bind_match} e
   | Seq _ as e -> shallow_map {f = de_bind_match} e
   | If _ as e -> shallow_map {f = de_bind_match} e
   | Tuple _ as e -> shallow_map {f = de_bind_match} e
   | KthTuple _ as e -> shallow_map {f = de_bind_match} e
   | List _ as e -> shallow_map {f = de_bind_match} e
   | Call _ as e -> shallow_map {f = de_bind_match} e
   | UnPin _ as e -> shallow_map {f = de_bind_match} e
   | CaseMatch _ as e -> shallow_map {f = de_bind_match} e
