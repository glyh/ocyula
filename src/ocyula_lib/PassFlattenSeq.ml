open Ast

(* this exists so we can make sure there's no misjudge on scoping rule *)

type src = PassDeBindMatch.dst
type dst = PassDeBindMatch.dst (* this transformation doesn't affect the shape of AST *)


let rec flatten_seq: type a. (a, src) gen_ast -> (a, dst) gen_ast = function
   | Seq(es) ->
      let rec join_seqs exps = begin match exps with
      | [] -> []
      | Seq s :: rest -> s @ join_seqs rest
      | some :: rest -> some :: join_seqs rest
      end in
      es
      |> List.map flatten_seq
      |> join_seqs
      |> fun ss -> Seq ss

   | Assert _ as e -> shallow_map {f = flatten_seq} e
   | Concrete _ as e -> shallow_map {f = flatten_seq} e
   | Gensym _ as e -> shallow_map {f = flatten_seq} e
   | Bind _ as e -> shallow_map {f = flatten_seq} e
   | Lens _ as e -> shallow_map {f = flatten_seq} e
   | Union _ as e -> shallow_map {f = flatten_seq} e
   | Updatable _ as e -> shallow_map {f = flatten_seq} e
   | Pin _ as e -> shallow_map {f = flatten_seq} e
   | PatTuple _ as e -> shallow_map {f = flatten_seq} e
   | PatList _ as e -> shallow_map {f = flatten_seq} e
   | PLit _ as e -> shallow_map {f = flatten_seq} e
   | PAny _ as e -> shallow_map {f = flatten_seq} e
   | With _ as e -> shallow_map {f = flatten_seq} e
   | Val _ as e -> shallow_map {f = flatten_seq} e
   | Lit _ as e -> shallow_map {f = flatten_seq} e
   | Binary _ as e -> shallow_map {f = flatten_seq} e
   | Unary _ as e -> shallow_map {f = flatten_seq} e
   | If _ as e -> shallow_map {f = flatten_seq} e
   | Tuple _ as e -> shallow_map {f = flatten_seq} e
   | KthTuple _ as e -> shallow_map {f = flatten_seq} e
   | List _ as e -> shallow_map {f = flatten_seq} e
   | Call _ as e -> shallow_map {f = flatten_seq} e
   | UnPin _ as e -> shallow_map {f = flatten_seq} e
   | CaseMatch _ as e -> shallow_map {f = flatten_seq} e
   | Lam _ as e -> shallow_map {f = flatten_seq} e
   | BindOnly _ as e -> shallow_map {f = flatten_seq} e

