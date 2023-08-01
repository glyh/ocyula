open Ast

let explode s = List.init (String.length s) (String.get s)

let requote_char (s : char) =
   match s with
   | '\n' -> "\\n"
   | '"' -> "\\\""
   | any -> String.make 1 any

let requote_inner (s : char list) =
   String.concat "" (List.map requote_char s)

let requote (s : string) = 
   "\"" ^ requote_inner (explode s) ^ "\""

let compile_atom (a : atom) =
   match a with 
   (* | Type TInt -> "Int" *)
   (* | Type TStr -> "String" *)
   (* | Type TF64 -> "F64" *)
   (* | Type TType -> "Type" *)
   (* | Type TKeyword -> "Keyword" *)
   | Int i -> string_of_int i 
   | F64 f -> string_of_float f
   | Str s -> requote s
   | Keyword k -> ":" ^ k

let rec compile_exps (exps: exp list) =
   (String.concat "\n" (List.map compile_exp exps)) ^ "\nend"

and compile_pattern pat = 
   (* TODO: fix this *)
   compile_exp pat
and compile_call id args = 
   match id, args with
   | "=", [lhs; rhs] -> 
      "(" ^ compile_pattern(lhs) ^ " = " ^ compile_exp(rhs) ^ ")"
   | "==", [lhs; rhs] -> 
      "(" ^ compile_exp(lhs) ^ " == " ^ compile_exp(rhs) ^ ")"
   | "!=", [lhs; rhs] -> 
      "(" ^ compile_exp(lhs) ^ " != " ^ compile_exp(rhs) ^ ")"
   | "<=", [lhs; rhs] -> 
      "(" ^ compile_exp(lhs) ^ " <= " ^ compile_exp(rhs) ^ ")"
   | "<", [lhs; rhs] -> 
      "(" ^ compile_exp(lhs) ^ " < " ^ compile_exp(rhs) ^ ")"
   | ">=", [lhs; rhs] -> 
      "(" ^ compile_exp(lhs) ^ " >= " ^ compile_exp(rhs) ^ ")"
   | ">", [lhs; rhs] -> 
      "(" ^ compile_exp(lhs) ^ " > " ^ compile_exp(rhs) ^ ")"
   | "+", [lhs; rhs] -> 
      "(" ^ compile_exp(lhs) ^ " + " ^ compile_exp(rhs) ^ ")"
   | "-", [lhs; rhs] -> 
      "(" ^ compile_exp(lhs) ^ " - " ^ compile_exp(rhs) ^ ")"
   | "*", [lhs; rhs] -> 
      "(" ^ compile_exp(lhs) ^ " * " ^ compile_exp(rhs) ^ ")"
   | "/", [lhs; rhs] -> 
      "(" ^ compile_exp(lhs) ^ " / " ^ compile_exp(rhs) ^ ")"
   | "and", [lhs; rhs] -> 
      "(" ^ compile_exp(lhs) ^ " and " ^ compile_exp(rhs) ^ ")"
   | "or", [lhs; rhs] -> 
      "(" ^ compile_exp(lhs) ^ " or " ^ compile_exp(rhs) ^ ")"
   | "not", [inner] -> 
      "(not " ^ compile_exp(inner) ^ ")"
   | id, args when String.contains_from id 0 '.' -> 
      id ^ "(" ^ (String.concat ", " (List.map compile_exp args)) ^ ")"
   | id, args -> 
      id ^ ".(" ^ (String.concat ", " (List.map compile_exp args)) ^ ")"

and compile_exp (exp : exp) = 
   match exp with
   | Atom a -> compile_atom a
   (* | Binary(op, lhs, rhs) ->  *)
   (*    compile_exp(Call(bin_op_to_str(op), [lhs; rhs])) *)
      (* "((" ^ compile_exp(lhs) ^ ")" ^ compile_bin_op(op) ^ "(" ^ compile_exp(rhs) ^ "))" *)
   (* | UpdateMatch(f, lhs, rhs) *)
   (*    -> compile_exp(Binary(MATCH, lhs, Call(f, [lhs; rhs])))  *)
   (* | Unary(op, exp) ->  *)
   (*    compile_exp(Call(un_op_to_str(op), [exp])) *)
      (* "(" ^ compile_un_op(op) ^ "(" ^ compile_exp(exp) ^ "))" *)
   | Val(id) -> id
   | Tuple l -> "{" ^ (String.concat ", " (List.map compile_exp l)) ^ "}"
   | List l -> "[" ^ (String.concat ", " (List.map compile_exp l)) ^ "]"
   | If(test, _then, _else) -> "(if " ^ (compile_exp test) ^ " do\n" ^ (compile_exps _then) ^ "\nelse\n" ^ (compile_exps _else) ^ ")"
   (* we only use lambda here, so all call would be qualified with `.` *)
   | Call(id, args) -> compile_call id args
   | Lam(None, args, body) -> "fn " ^ (String.concat ", " args) ^ "do\n" ^ (compile_exps body)
   | Lam(Some id, args, body) -> id ^ "= fn " ^ (String.concat ", " args) ^ "do\n" ^ (compile_exps body)
   | Case(_case, _matchings) -> "TODO"
   | Seq(exps) -> "do\n" ^ compile_exps(exps)

(* Compiles to Haskell *)
let compile (exp: exp) = 
   {|#!/usr/bin/env elixir
Mix.install([])
   |} ^ (compile_exp exp)
