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

type updatable_pattern =
   | Bind of ident (* creates new binding *)
   | Lens of updatable_pattern * ident * exp list
            (* obj             . method (arg1, arg2, ...) *) 

and pattern = 
   | Updatable of updatable_pattern
   | Pin of ident (* match with exisiting value *) 
   | PatTuple of pattern list
   | PatList of pattern list
   | Lit of atom
   | Any
   (* TODO : add `as` pattern to match against types *)

and exp =
   | Atom of atom
   | UnPin of ident
   | Val of ident 
   | Tuple of exp list
   | List of exp list
   | If of exp * exp list * exp list
   | Call of ident * exp list
   | Lam of pattern list * exp list
   (* In (pattern * exp * exp list), second exp is the boolean expression acting as a guard *)
   | CaseMatch of exp * (pattern * exp * exp list) list
   | Seq of exp list
   | Match of pattern * exp
   (* builtins *)
   | Binary of binary_operator * exp * exp
   | Unary of unary_operator * exp

(* type program = Program of exp list *)
