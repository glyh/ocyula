type type_t = 
     TInt
   | TStr
   | TF64
   | TType
   | TKeyword

type ident = string

type bin_operator = 
     EQ | NE | LE | LT | GE | GT
   | ADD | SUB | MUL | DIV
   | AND | OR
   | AS (* type annotation *)
   | MATCH (* pattern matching *)

type unary_operator = 
     NOT

type atom = 
     (* Type of type_t *)
   | Int of int
   | F64 of float
   | Str of string
   | Keyword of string

type exp =
     Atom of atom
   (* | Binary of bin_operator * exp * exp *)
   (* | UpdateMatch of ident * exp * exp *)
   (* | Unary of unary_operator * exp *)
   | Val of ident 
   | Tuple of exp list
   | List of exp list
   | If of exp * exp list * exp list
   | Call of ident * exp list
   (* | Recur of exp list *)
   | Lam of ident option * ident list * exp list 
   | Case of exp * (exp * exp list) list
   | Seq of exp list

(* type program = Program of exp list *)
