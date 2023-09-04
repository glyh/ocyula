open Ast

type deSeq = <
   seq: no;
   pattern: yes;
   compound_type: yes;
   lambda: yes;
   call: yes;
   letin: no;
   unpin: yes>

let rec de_seq: type a. (a, top) gen_ast -> (a, deSeq) gen_ast = fun e ->
   match e with
   | IfSeq(test, _then, _else) -> If(de_seq test, Seq(List.map de_seq _then), Seq(List.map de_seq _else))
   | LamPatSeq(pats, exps) -> LamPat(List.map de_seq pats, Seq(List.map de_seq exps))
   | CaseMatchSeq(e, branches) ->
      let branch_de_seq (pat, guard, body) = (de_seq pat, de_seq guard, Seq (List.map de_seq body)) in
         CaseMatch(de_seq e, List.map branch_de_seq branches)

   | Bind _ as e -> shallow_map {f = de_seq} e
   | Lens _ as e -> shallow_map {f = de_seq} e
   | Union _ as e -> shallow_map {f = de_seq} e
   | Updatable _ as e -> shallow_map {f = de_seq} e
   | Pin _ as e -> shallow_map {f = de_seq} e
   | PatTuple _ as e -> shallow_map {f = de_seq} e
   | PatList _ as e -> shallow_map {f = de_seq} e
   | Lit _ as e -> shallow_map { f = de_seq} e
   | Any _ as e -> shallow_map {f = de_seq} e
   | Val _ as e -> shallow_map {f = de_seq} e
   | Atom _ as e -> shallow_map {f = de_seq} e
   | Binary _ as e -> shallow_map {f = de_seq} e
   | Unary _ as e -> shallow_map {f = de_seq} e
   | Fix _ as e -> shallow_map {f = de_seq} e
   | Seq _ as e -> shallow_map {f = de_seq} e
   | Tuple _ as e -> shallow_map {f = de_seq} e
   | List _ as e -> shallow_map {f = de_seq} e
   | Call _ as e -> shallow_map {f = de_seq} e
   | Match _ as e -> shallow_map {f = de_seq} e
   | UnPin _ as e -> shallow_map {f = de_seq} e
