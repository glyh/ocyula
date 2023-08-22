exception Unimplemented

type desugar_err_reason = 
   WrongNumberArgForMatch
   | CantParsePattern
exception DesugarError of desugar_err_reason

let gensym = 
   let count = ref 0 in 
   let next () = count := !count + 1; !count
   in fun prefix -> prefix ^ string_of_int (next ())

type pattern =                                            
   | Bind of Ast.ident (* creates new binding *)
   | Pin of Ast.ident (* match with exisiting value *) 
   | Lens of Ast.ident * Ast.ident * Ast.exp list
            (* A          B           (c, d, e)        T *) 
            (* A.B(c, d, e) as T *)                       
   | PatTuple of pattern list
   | PatList of pattern list
   | Lit of Ast.atom

let rec parse_pattern (e : Ast.exp) : pattern = 
   match e with
   | Atom(x) -> Lit(x) | Val(id) -> Bind(id)
   | Tuple(t) -> PatTuple(List.map parse_pattern t)
   | List(t) -> PatList(List.map parse_pattern t)
   | Call("!pin", [Val(pinned)]) -> Pin(pinned)
   | Call(f, Val(id) :: args) -> Lens(id, f, args)
   | _ -> raise (DesugarError CantParsePattern)

(*
This converts something like 
   `a = 1; b = 2; c ` 
into something like
   `let a = 1 in let b = 2 in c`
*)
let rec expand_set (es: Type.exp_prim_input list) : Type.exp_prim_input =
   match es with
   | [] -> Seq ([], ())
   | Type.App(
         Type.App(Val("!set", ()), 
                  Val(id, ()), ()), 
         to_match, ()) :: rest -> 
      Let (id, to_match, expand_set rest, ())
   | _else :: rest -> 
      Seq ([_else ; expand_set rest], ())

let rec desugar (e: Ast.exp) : Type.exp_prim_input =
   match e with
   | Atom(a) -> Atom(a, ())
   | Val(id) -> Val(id, ())
   | Tuple(es) -> Tuple(List.map desugar es, ())
   | List(es) -> List(List.map desugar es, ())
   | If(test, _then, _else) ->
      If(desugar test, desugar (Seq _then), desugar (Seq _else), ())
   | Call("!match", es) -> 
      begin match es with
      | [lhs; rhs] -> desugar_pat (parse_pattern lhs) (desugar rhs)
      | _ -> raise (DesugarError WrongNumberArgForMatch)
      end
   | Call(id, es) -> es 
      |> List.map desugar 
      |> List.fold_left (fun f x -> Type.App(f, x, ())) (Type.Val(id, ()))
   | Lam (ids, body) ->
      List.fold_right 
         (fun id fn -> Type.Lam(id, fn, ()))
         ids
         (desugar (Seq body)) 
   | Case(exp, cases) -> 
      let to_match = Ast.Val(gensym "__case_") in
      let decase (pat, body) = 
         Ast.Seq(Call("!match", [pat; to_match]) :: body)
      in
      let cases = begin match List.map decase cases with
      | [] -> Type.Seq ([],())
      | first :: rest -> 
         let first_desugared = desugar first in
         let rest_desugared = List.map desugar rest in
            List.fold_left (fun acc ele -> Type.Try(acc, ele, ())) first_desugared rest_desugared 
      end in
      Seq ([
         desugar (Call("!match", [to_match; exp]));
         cases
      ], ())
   | Seq s -> expand_set (List.map desugar s)

and desugar_pat (pat: pattern) (to_match: Type.exp_prim_input) : Type.exp_prim_input=
   (* ;( sadly these has to be this ugly *)
   match pat with 
   | Bind(id) -> 
      Type.App(
         Type.App(Val("!set", ()), 
                  Val(id, ()), ()), 
         to_match, ())
   (* I keep these down unimplemented, after I implement dependent type it would be a good time to implement this. *)
   | _ -> raise Unimplemented
