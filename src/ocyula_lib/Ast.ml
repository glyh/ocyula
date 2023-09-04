exception Unimplemented

type ident = string

type unary_operator = 
     NOT

type binary_operator = 
   | EQ | NE | LE | LT | GE | GT
   | ADD | SUB | MUL | DIV
   | AND | OR
   | AS (* type annotation *)

type atom = 
   | Int of int
   | F64 of float
   | Str of string
   | Keyword of string
   | Bool of bool
   (* TODO: | Type of type_t *)

type yes = Yes
type no = No

type upd_pat = UpdatablePattern
type pat = Pattern
type exp = Expression

(* Random: we may extend GADT by allowing same constructor to be overloaded *)
(* https://icfp23.sigplan.org/details/ocaml-2023-papers/4/Modern-DSL-compiler-architecture-in-OCaml-our-experience-with-Catala *)
type ('ty, 'dep, 'sur) flex_ast = 

   (* UPDATABLE PATTERN *)

   | Bind: ident 
   -> (upd_pat, 'dep, <pattern: yes; ..> as 'sur) flex_ast 
   | Lens: 
   (* obj                  . method  (arg1, arg2, ...) *) 
   (upd_pat, 'dep) gen_ast * ident * (exp, 'dep) gen_ast list 
   -> (upd_pat, 'dep, <pattern: yes; ..> as 'sur) flex_ast


   (* PATTERN *)

   | Union: 
   (* rhs matches any of LHS, we should require LHS have same bindings and 
      corresponding bindings have same type *)
   (pat, 'dep) gen_ast list 
   -> (pat, 'dep, <pattern: yes; ..> as 'sur) flex_ast
   
   | Updatable: 
   (upd_pat, 'dep) gen_ast
   -> (pat, 'dep, <pattern: yes; ..> as 'sur) flex_ast
   
   | Pin: (* match with exisiting value *)
   ident
   -> (pat, 'dep, <pattern: yes; ..> as 'sur) flex_ast

   | PatTuple: 
   (pat, 'dep) gen_ast list
   -> (pat, 'dep, <pattern: yes; ..> as 'sur) flex_ast

   | PatList: 
   (pat, 'dep) gen_ast list
   -> (pat, 'dep, <pattern: yes; ..> as 'sur) flex_ast

   | Lit:
   atom
   -> (pat, 'dep, <pattern: yes; ..> as 'sur) flex_ast

   | Any:
   unit
   -> (pat, 'dep, <pattern: yes; ..> as 'sur) flex_ast


   (* EXPRESSION *)

   | Val: 
   ident 
   -> (exp, 'dep, 'sur) flex_ast

   | Atom:
   atom
   -> (exp, 'dep, 'sur) flex_ast

   | Binary:
   binary_operator * (exp, 'dep) gen_ast * (exp, 'dep) gen_ast
   -> (exp, 'dep, 'sur) flex_ast

   | Unary:
   unary_operator * (exp, 'dep) gen_ast
   -> (exp, 'dep, 'sur) flex_ast

   | Fix:
   (exp, 'dep) gen_ast
   -> (exp, 'dep, 'sur) flex_ast

   | Seq:
   (exp, 'dep) gen_ast list
   -> (exp, 'dep, 'sur) flex_ast

   | If:
   (exp, 'dep) gen_ast * (exp, 'dep) gen_ast * (exp, 'dep) gen_ast
   -> (exp, 'dep, <seq: no; ..> as 'sur) flex_ast
   | IfSeq:
   (exp, 'dep) gen_ast * (exp, 'dep) gen_ast list * (exp, 'dep) gen_ast list
   -> (exp, 'dep, <seq: yes; ..> as 'sur) flex_ast

   | Tuple: 
   (exp, 'dep) gen_ast list
   -> (exp, 'dep, <compound_type: yes; ..> as 'sur) flex_ast

   | List: 
   (exp, 'dep) gen_ast list
   -> (exp, 'dep, <compound_type: yes; ..> as 'sur) flex_ast

   | Abs:
   ident * (exp, 'dep) gen_ast
   -> (exp, 'dep, <lambda: no; ..> as 'sur) flex_ast

   | Lam:
   (ident list) * (exp, 'dep) gen_ast
   -> (exp, 'dep, <lambda: yes; seq: no; pattern: no; ..> as 'sur) flex_ast
   | LamPat:
   ((pat, 'dep) gen_ast list) * (exp, 'dep) gen_ast
   -> (exp, 'dep, <lambda: yes; seq: no; pattern: yes; ..> as 'sur) flex_ast
   | LamPatSeq:
   ((pat, 'dep) gen_ast list) * (exp, 'dep) gen_ast list
   -> (exp, 'dep, <lambda: yes; seq: yes; pattern: yes; ..> as 'sur) flex_ast

   | App: 
   (exp, 'dep) gen_ast * (exp, 'dep) gen_ast 
   -> (exp, 'dep, <call: no; ..> as 'sur) flex_ast

   | Call: 
   ident * (exp, 'dep) gen_ast list
   -> (exp, 'dep, <call: yes; ..> as 'sur) flex_ast

   | LetIn: (* we may need fix to create mutual recursive bindings here so a let may have more than one output *)
   ident list * (exp, 'dep) gen_ast * (exp, 'dep) gen_ast 
   -> (exp, 'dep, <letin: yes; ..> as 'sur) flex_ast

   | Match:
   (pat, 'dep) gen_ast * (exp, 'dep) gen_ast
   -> (exp, 'dep, <letin: no; pattern: yes; ..> as 'sur) flex_ast

   | UnPin:
   ident
   -> (exp, 'dep, <unpin: yes; ..> as 'sur) flex_ast

   | ConcreteCaseMatch: 
   (* exp to match *)
   (exp, 'dep) gen_ast *
   (* pat  guard                 ret *)
   (atom * (exp, 'dep) gen_ast * (exp, 'dep) gen_ast) list *
   (exp, 'dep) gen_ast option ->
   (exp, 'dep, <pattern: no; seq: no; ..> as 'sur) flex_ast

   | CaseMatch: 
   (exp, 'dep) gen_ast *
   ((pat, 'dep) gen_ast * (exp, 'dep) gen_ast * (exp, 'dep) gen_ast) list ->
   (exp, 'dep, <pattern: yes; seq: no; ..> as 'sur) flex_ast

   | CaseMatchSeq:
   (exp, 'dep) gen_ast *
   ((pat, 'dep) gen_ast * (exp, 'dep) gen_ast * (exp, 'dep) gen_ast list) list ->
   (exp, 'dep, <pattern: yes; seq: yes; ..> as 'sur) flex_ast

and ('ty, 'a) gen_ast = ('ty, 'a, 'a) flex_ast

type top = <
   seq: yes;
   pattern: yes;
   compound_type: yes;
   lambda: yes;
   call: yes;
   letin: no;
   unpin: yes>

type btm = <
   seq: no;
   pattern: no;
   compound_type: no;
   lambda: no;
   call: no;
   letin: no;
   unpin: no>

type ('src, 'dst) desugarer = { f: 't. ('t, 'src) gen_ast -> ('t, 'dst) gen_ast }

let shallow_map
   (type ty src dst)
   (f: (src, dst) desugarer)
   (e: (ty, src, dst) flex_ast)
   : (ty, dst) gen_ast =
   match e with 
   (* updatable pattern *)
   | Bind(id) -> Bind(id)
   | Lens(obj, _method, args) -> 
      Lens(f.f obj, _method, List.map f.f args)
   (* pattern *)
   | Union(alts) -> Union(List.map f.f alts)
   | Updatable(u) -> Updatable(f.f u)
   | Pin(id) -> Pin(id)
   | PatTuple(ps) -> PatTuple(List.map f.f ps)
   | PatList(ps) -> PatList(List.map f.f ps)
   | Lit(a) -> Lit(a)
   | Any() -> Any()

   (* expression *)
   | Val(v) -> Val(v)
   | Atom(a) -> Atom(a)
   | Binary(op, lhs, rhs) -> Binary(op, f.f lhs, f.f rhs)
   | Unary(g, x) -> Unary(g, f.f x)
   | Fix(e) -> Fix(f.f e)
   | Seq(es) -> Seq(List.map f.f es)
   | If(test, _then, _else) -> If(f.f test, f.f _then, f.f _else)
   | IfSeq(test, _then, _else) -> IfSeq(f.f test, List.map f.f _then, List.map f.f _else)
   | Tuple(es) -> Tuple(List.map f.f es)
   | List(es) -> List(List.map f.f es)
   | Abs(id, e) -> Abs(id, f.f e)
   | Lam(ids, e) -> Lam(ids, f.f e)
   | LamPat(pats, e) -> LamPat(List.map f.f pats, f.f e)
   | LamPatSeq(pats, es) -> LamPatSeq(List.map f.f pats, List.map f.f es)
   | App(g, x) -> App(f.f g, f.f x)
   | Call(id, es) -> Call(id, List.map f.f es)
   | LetIn(ids, _val, inner) -> LetIn(ids, f.f _val, f.f inner)
   | Match(lhs, rhs) -> Match(f.f lhs, f.f rhs)
   | UnPin(id) -> UnPin(id)
   | ConcreteCaseMatch(e, branches, _else) ->
      let f_branch (_val, guard, ret) = (_val, f.f guard, f.f ret) in 
      begin match _else with
         | Some(has_else) -> ConcreteCaseMatch(f.f e, List.map f_branch branches, Some(f.f has_else))
         | _ -> raise Unimplemented
      end
   | CaseMatch(e, branches) ->
      let f_branch (pat, guard, ret) = (f.f pat, f.f guard, f.f ret) in
      CaseMatch(f.f e, List.map f_branch branches)
   | CaseMatchSeq(e, branches) ->
      let f_branch (pat, guard, ret) = (f.f pat, f.f guard, List.map f.f ret) in
      CaseMatchSeq(f.f e, List.map f_branch branches)
