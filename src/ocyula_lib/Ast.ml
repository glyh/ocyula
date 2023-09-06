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
   (* TODO: | Type of type_t *)

type value =
   | Atom of atom
   | List of value list
   | Tuple of value list

type ident = 
   | Concrete of string
   | Gensym of int

type updatable = 
   | Bind of ident
   | Lens of updatable * ident * exp list
             (* obj    . method  (arg1, arg2, ...) *)
and pat = 
   | Updatable of updatable
   | Union of pat list
   | With of pat * exp
   (* NOTE:
      we have some ADT:
      type f = 
      | Left of int
      | Right of unit
      Left i | Right () with (i = 3) = Right()
      exists solely for balancing the variables on both side of a union pattern
   *)
   | Pin of ident
   | PatTuple of pat list
   | PatList of pat list
   | PLit of atom
   | PAny

and exp = 
   | Assert of exp
   | Val of ident
   | Lit of atom
   | Bin of exp * bin_op * exp
   | Un of un_op * exp
   | Seq of exp list
   | If of exp * exp * exp
   | Tuple of exp list
   | List of exp list
   | Lambda of pat list * exp
   | Call of ident * exp list 
   | BindMatch of pat * exp
   | UnPin of ident
   | CaseMatch of exp * (pat * exp * exp) list
   | Annotate of exp * Type.ty

let gensym =
   let counter = ref 1 in 
      fun () -> 
         counter := !counter + 1;
         !counter - 1

let rec gensyms n = 
   if n == 0 
   then []
   else gensym() :: gensyms (n - 1)
