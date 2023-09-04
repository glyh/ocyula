open Ast

type deLetInApp = <
   seq: no;
   pattern: no;
   compound_type: yes;
   lambda: yes;
   call: no;
   letin: yes;
   unpin: no>

type deRecBind = PassDeRecBind.deRecBind

let rec deletin: type a. (a, deRecBind) gen_ast -> (a, deLetInApp) gen_ast = function

   (* TODO: figure out how should we solve mutlti bind *)
   | LetIn _ -> 
      raise Unimplemented
   (* | LetIn(ids, _val, e) ->  *)
      (* let lam =Lam(ids, deletin _val) in *)
      (* App(lam, deletin e) *)
   | Call(id, exps) ->
      begin match exps with
      | [] -> 
          App(Val(id), Tuple([]))
      | head :: rest ->
          List.fold_left (fun acc ele -> App(acc, deletin ele)) (App(Val(id), deletin head)) rest 
      end

   | Val _ as e -> shallow_map {f = deletin} e
   | Atom _ as e -> shallow_map {f = deletin} e
   | Binary _ as e -> shallow_map {f = deletin} e
   | Unary _ as e -> shallow_map {f = deletin} e
   | Fix _ as e -> shallow_map {f = deletin} e
   | Seq _ as e -> shallow_map {f = deletin} e
   | If _ as e -> shallow_map {f = deletin} e
   | Lam _ as e -> shallow_map {f = deletin} e
   | Tuple _ as e -> shallow_map {f = deletin} e
   | List _ as e -> shallow_map {f = deletin} e
   | ConcreteCaseMatch _ as e -> shallow_map {f = deletin} e
