type type_var = string

type ty = 
   | TyInt
   | TyF64
   | TyStr
   | TyBool
   | TyType
   | TyKeyword
   | TyTuple of ty list
   | TyList of ty
   | TyLam of ty * ty (* we have currying *)
   | TyVar of type_var
   | TyForAll of type_var * ty (* multiple Forall's should be chained *)
(* type atom = Ast.atom *)
(* type binop = Ast.bin_op *)
(* type ident = string *)
(**)
(* type core_op =  *)
(*    | LE | ADD | SUB | MUL | DIV | AND | OR | NOT *)
(**)
(* type core_exp =  *)
(*    | Atom of atom *)
(*    | Var of ident *)
(*    | App of core_exp * core_exp *)
(*    | Lam of ident * core_exp *)
(*    | Let of ident * core_exp * core_exp *)
(*    | Lit of atom *)
(*    | If of core_exp * core_exp * core_exp *)
(*    | Fix of core_exp (* Y combinator, support for recursion *) *)
(*    | Op of core_op * core_exp * core_exp *)
