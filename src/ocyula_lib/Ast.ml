exception Unimplemented

type un_op = 
     NOT

type bin_op = 
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
   (* TODO: dependent types
   | Type of Type.ty *)

type ty = 
   | TInt
   | TF64
   | TStr
   | TBool
   | TKeyword
   | TTuple of ty list
   | TList of ty
   | TArrow of ty * ty (* we have currying *)

(* Random: we may extend GADT by allowing same constructor to be overloaded *)
(* https://icfp23.sigplan.org/details/ocaml-2023-papers/4/Modern-DSL-compiler-architecture-in-OCaml-our-experience-with-Catala *)

type yes = Yes
type no = No

type exp = EXP
type upd_pat = UPDPAT
type pat = PAT
type id = ID

type 'a exp_t = (exp, 'a) gen_ast
and 'a upd_pat_t = (upd_pat, 'a) gen_ast
and 'a pat_t = (pat, 'a) gen_ast
and 'a id_t = (id, 'a) gen_ast
and ('ty, 'a) gen_ast = ('ty, 'a, 'a) flex_ast

(* 'd means underlaying structure, while 's means surface structure *)
and ('ty, 'd, 's) flex_ast = 

   (* Identifiers *)
   | Concrete: string -> (id, 'dep, <unique_id: no; ..> as 'sur) flex_ast 
   | Unique: string * int -> (id, 'dep, <unique_id: yes; ..> as 'sur) flex_ast 
   | Gensym: int -> (id, 'dep, 'sur) flex_ast 

   (* Updatable Patterns *)
   | Bind: 'dep id_t
   -> (upd_pat, 'dep, <pattern: yes; ..> as 'sur) flex_ast 
   | Lens: 
   (* obj                  . method  (arg1, arg2, ...) *) 
   'dep upd_pat_t * 'dep id_t * 'dep exp_t list 
   -> (upd_pat, 'dep, <pattern: yes; ..> as 'sur) flex_ast

   (* PATTERN *)
   | Union: 
   (* rhs matches any of LHS, we should require LHS have same bindings and 
      corresponding bindings have same type *)
   'dep pat_t list 
   -> (pat, 'dep, <pattern: yes; ..> as 'sur) flex_ast
   
   | Updatable: 
   'dep upd_pat_t
   -> (pat, 'dep, <pattern: yes; ..> as 'sur) flex_ast
   
   | Pin: (* match with exisiting value *)
   'dep id_t
   -> (pat, 'dep, <pattern: yes; ..> as 'sur) flex_ast

   | PatTuple: 
   'dep pat_t list
   -> (pat, 'dep, <pattern: yes; ..> as 'sur) flex_ast

   | PatList: 
   'dep pat_t list
   -> (pat, 'dep, <pattern: yes; ..> as 'sur) flex_ast

   | PLit:
   atom
   -> (pat, 'dep, <pattern: yes; ..> as 'sur) flex_ast

   | PAny:
   unit
   -> (pat, 'dep, <pattern: yes; ..> as 'sur) flex_ast

   | With:
   'dep pat_t * 'dep exp_t 
   -> (pat, 'dep, <pattern: yes; ..> as 'sur) flex_ast


   (* EXPRESSION *)

   (* a temporary solution, we may add algebraic effects later *)
   | Assert:
   'dep exp_t
   -> (exp, 'dep, 'sur) flex_ast

   | Val: 
   'dep id_t 
   -> (exp, 'dep, 'sur) flex_ast

   | Lit:
   atom
   -> (exp, 'dep, 'sur) flex_ast

   | Binary:
   bin_op * 'dep exp_t * 'dep exp_t
   -> (exp, 'dep, 'sur) flex_ast

   | Unary:
   un_op * 'dep exp_t
   -> (exp, 'dep, 'sur) flex_ast

   | Fix:
   'dep exp_t
   -> (exp, 'dep, <recbind: no; ..> as 'sur) flex_ast

   | Seq:
   'dep exp_t list
   -> (exp, 'dep, 'sur) flex_ast

   | If:
   'dep exp_t * 'dep exp_t * 'dep exp_t
   -> (exp, 'dep, <seq: no; .. > as 'sur) flex_ast
   | IfSeq:
   'dep exp_t * 'dep exp_t list * 'dep exp_t list
   -> (exp, 'dep, <seq: yes; ..> as 'sur) flex_ast

   | Tuple: 
   'dep exp_t list
   -> (exp, 'dep, 'sur) flex_ast

   | KthTuple: 
      'dep exp_t * int 
   -> (exp, 'dep, 'sur) flex_ast

   | List: 
   'dep exp_t list
   -> (exp, 'dep, 'sur) flex_ast

   | Abs:
   'dep id_t * 'dep exp_t
   -> (exp, 'dep, <lambda: no; ..> as 'sur) flex_ast

   | Lam:
   ('dep id_t list) * 'dep exp_t
   -> (exp, 'dep, <lambda: yes; seq: no; bind_only: yes; ..> as 'sur) flex_ast
   | LamPat:
   ('dep pat_t list) * 'dep exp_t
   -> (exp, 'dep, <lambda: yes; seq: no; bind_only: no; ..> as 'sur) flex_ast
   | LamPatSeq:
   ('dep pat_t list) * 'dep exp_t list
   -> (exp, 'dep, <lambda: yes; seq: yes; bind_only: no; ..> as 'sur) flex_ast

   | App: 
   'dep exp_t * 'dep exp_t 
   -> (exp, 'dep, <call: no; ..> as 'sur) flex_ast

   | Call: 
   'dep id_t * 'dep exp_t list
   -> (exp, 'dep, <call: yes; ..> as 'sur) flex_ast

   | LetIn: (* we may need fix to create mutual recursive bindings here so a let may have more than one output *)
   'dep id_t * 'dep exp_t * 'dep exp_t 
   -> (exp, 'dep, <bind_only: yes; letin: yes; ..> as 'sur) flex_ast

   | BindOnly: 
   'dep id_t * 'dep exp_t
   -> (exp, 'dep, <bind_only: yes; letin: no; ..> as 'sur) flex_ast
   | BindMatch:
   'dep pat_t * 'dep exp_t
   -> (exp, 'dep, <bind_only: no; ..> as 'sur) flex_ast

   | UnPin: 'dep id_t
   -> (exp, 'dep, <unique_id: no; ..> as 'sur) flex_ast

   | ConcreteCaseMatch: 
   (* exp to match *)
   'dep exp_t *
   (* pat  guard                 ret *)
   (atom * 'dep exp_t * 'dep exp_t) list *
   'dep exp_t option ->
   (exp, 'dep, <pattern: no; seq: no; ..> as 'sur) flex_ast

   | CaseMatch: 
   'dep exp_t *
   ('dep pat_t * 'dep exp_t * 'dep exp_t) list ->
   (exp, 'dep, <pattern: yes; seq: no; ..> as 'sur) flex_ast

   | CaseMatchSeq:
   'dep exp_t *
   ('dep pat_t * 'dep exp_t * 'dep exp_t list) list ->
   (exp, 'dep, <pattern: yes; seq: yes; ..> as 'sur) flex_ast

type top = <
   seq: yes;
   pattern: yes;
   lambda: yes;
   call: yes;
   recbind: yes; 
   unique_id: no;
   bind_only: no;
   letin: no>

type btm = <
   seq: no;
   pattern: no;
   lambda: no;
   call: no;
   recbind: no;
   unique_id: yes;
   bind_only: yes;
   letin: no>

type ('src, 'dst) desugarer = { f: 't. ('t, 'src) gen_ast -> ('t, 'dst) gen_ast }

let gensym =
   let counter = ref 1 in 
      fun () -> 
         counter := !counter + 1;
         !counter - 1

let rec gensyms n = 
   if n == 0 
   then []
   else gensym () :: gensyms (n - 1)

let shallow_map
   (type ty src dst)
   (f: (src, dst) desugarer)
   (e: (ty, src, dst) flex_ast)
   : (ty, dst) gen_ast =
   match e with 

   (* identifier *)
   | Concrete(id) -> Concrete(id)
   | Unique(id, i) -> Unique(id, i)
   | Gensym(i) -> Gensym(i)

   (* updatable pattern *)
   | Bind(id) -> Bind(f.f id)
   | Lens(obj, _method, args) -> 
      Lens(f.f obj, f.f _method, List.map f.f args)
   (* pattern *)
   | Union(alts) -> Union(List.map f.f alts)
   | Updatable(u) -> Updatable(f.f u)
   | Pin(id) -> Pin(f.f id)
   | PatTuple(ps) -> PatTuple(List.map f.f ps)
   | PatList(ps) -> PatList(List.map f.f ps)
   | PLit(a) -> PLit(a)
   | PAny() -> PAny()

   (* expression *)
   | Val(v) -> Val(f.f v)
   | Lit(a) -> Lit(a)
   | Binary(op, lhs, rhs) -> Binary(op, f.f lhs, f.f rhs)
   | Unary(g, x) -> Unary(g, f.f x)
   | Fix(e) -> Fix(f.f e)
   | Seq(es) -> Seq(List.map f.f es)
   | If(test, _then, _else) -> If(f.f test, f.f _then, f.f _else)
   | IfSeq(test, _then, _else) -> IfSeq(f.f test, List.map f.f _then, List.map f.f _else)
   | Tuple(es) -> Tuple(List.map f.f es)
   | KthTuple(e, k) -> KthTuple(f.f e, k) 
   | List(es) -> List(List.map f.f es)
   | Abs(id, e) -> Abs(f.f id, f.f e)
   | Lam(ids, e) -> Lam(List.map f.f ids, f.f e)
   | LamPat(pats, e) -> LamPat(List.map f.f pats, f.f e)
   | LamPatSeq(pats, es) -> LamPatSeq(List.map f.f pats, List.map f.f es)
   | App(g, x) -> App(f.f g, f.f x)
   | Call(id, es) -> Call(f.f id, List.map f.f es)
   | BindMatch(lhs, rhs) -> BindMatch(f.f lhs, f.f rhs)
   | UnPin(id) -> UnPin(f.f id)
   | ConcreteCaseMatch(e, branches, _else) ->
      let f_branch (_val, guard, ret) = (_val, f.f guard, f.f ret) in 
      begin match _else with
         | Some(has_else) -> ConcreteCaseMatch(f.f e, List.map f_branch branches, Some(f.f has_else))
         | _ -> ConcreteCaseMatch(f.f e, List.map f_branch branches, None)
      end
   | CaseMatch(e, branches) ->
      let f_branch (pat, guard, ret) = (f.f pat, f.f guard, f.f ret) in
      CaseMatch(f.f e, List.map f_branch branches)
   | CaseMatchSeq(e, branches) ->
      let f_branch (pat, guard, ret) = (f.f pat, f.f guard, List.map f.f ret) in
      CaseMatchSeq(f.f e, List.map f_branch branches)
   | LetIn(id, _val, inner) -> LetIn(f.f id, f.f _val, f.f inner)
   | BindOnly(id, e) -> BindOnly(f.f id, f.f e)
   | Assert(e) -> Assert(f.f e)
   | With(pat, e) -> With(f.f pat, f.f e)
