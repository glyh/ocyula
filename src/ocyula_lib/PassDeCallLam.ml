open Ast

exception Unreachable

type src = PassFlattenSeq.src
type dst = <
   seq: no;
   pattern: yes;
   lambda: no;
   call: no;
   recbind: yes; 
   unique_id: no;
   bind_only: yes;
   letin: no>

let rec de_call_lam: type a. (a, src) gen_ast -> (a, dst) gen_ast = function
   | Lam(args, e) -> 
      List.fold_left (fun lam arg -> Abs(arg, lam)) (de_call_lam e) (args |> List.rev |> List.map de_call_lam)
   | Call(id, args) ->
      List.fold_left (fun f x -> App(f, x)) (Val(de_call_lam id)) (List.map de_call_lam args)
      (* as e -> shallow_map {f = de_call_lam} e *)
   | If _ as e -> shallow_map {f = de_call_lam} e
   | Bind _ as e -> shallow_map {f = de_call_lam} e
   | Lens _ as e -> shallow_map {f = de_call_lam} e
   | Union _ as e -> shallow_map {f = de_call_lam} e
   | Updatable _ as e -> shallow_map {f = de_call_lam} e
   | Pin _ as e -> shallow_map {f = de_call_lam} e
   | PatTuple _ as e -> shallow_map {f = de_call_lam} e
   | PatList _ as e -> shallow_map {f = de_call_lam} e
   | PLit _ as e -> shallow_map { f = de_call_lam} e
   | PAny _ as e -> shallow_map {f = de_call_lam} e
   | With _ as e -> shallow_map {f = de_call_lam} e
   | Val _ as e -> shallow_map {f = de_call_lam} e
   | Lit _ as e -> shallow_map {f = de_call_lam} e
   | Binary _ as e -> shallow_map {f = de_call_lam} e
   | Unary _ as e -> shallow_map {f = de_call_lam} e
   | Seq _ as e -> shallow_map {f = de_call_lam} e
   | Tuple _ as e -> shallow_map {f = de_call_lam} e
   | List _ as e -> shallow_map {f = de_call_lam} e
   | UnPin _ as e -> shallow_map {f = de_call_lam} e
   | KthTuple _ as e -> shallow_map {f = de_call_lam} e
   | Concrete _ as e -> shallow_map {f = de_call_lam} e
   | Gensym _ as e -> shallow_map {f = de_call_lam} e
   | Assert _ as e -> shallow_map {f = de_call_lam} e
   | BindOnly _ as e -> shallow_map {f = de_call_lam} e
   | CaseMatch _ as e -> shallow_map {f = de_call_lam} e
