type ident = string

type unary_operator = 
     NOT

type atom = 
   | Int of int
   | F64 of float
   | Str of string
   | Keyword of string
   | Bool of bool
   (* TODO: | Type of type_t *)

type updatable_pattern =
   | Bind of ident (* creates new binding *)
   | Lens of ident * ident * exp list
            (* obj . method (arg1, arg2, ...) *) 

and pattern = 
   | Updatable of updatable_pattern
   | Pin of ident (* match with exisiting value *) 
   | PatTuple of pattern list
   | PatList of pattern list
   | Lit of atom
   (* TODO : add `as` pattern to match against types *)

and exp =
   | Atom of atom
   | Val of ident 
   | Tuple of exp list
   | List of exp list
   | If of exp * exp list * exp list
   | Call of ident * exp list
   | Lam of pattern list * exp list
   (* pattern matching can be represented as case *)
   | Case of exp * (pattern * exp list) list
   | Seq of exp list
   | Match of pattern * exp

(* type program = Program of exp list *)
