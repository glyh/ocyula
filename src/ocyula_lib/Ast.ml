type ident = string

type unary_operator = 
     NOT

type atom = 
   | Int of int
   | F64 of float
   | Str of string
   | Keyword of string
   | Bool of bool
   (* | Type of type_t *)

type exp =
   | Atom of atom
   | Val of ident 
   | Tuple of exp list
   | List of exp list
   | If of exp * exp list * exp list
   | Call of ident * exp list
   | Lam of ident list * exp list 
   | Case of exp * (exp * exp list) list
   | Seq of exp list
   (* | Recur of exp list *)

   (* | Binary of bin_operator * exp * exp *)
   (* | UpdateMatch of ident * exp * exp *)
   (* | Unary of unary_operator * exp *)

(* type program = Program of exp list *)
