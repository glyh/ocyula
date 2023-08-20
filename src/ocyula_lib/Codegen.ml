open Ast
open Type

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

let counter = ref 0
let gensym () =
   counter := !counter + 1;
   "__generated_" ^ string_of_int !counter

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
   | Bool true -> "true"
   | Bool false -> "false"

let rec compile_exps (exps: exp list) =
   (String.concat "\n" (List.map compile_exp exps)) ^ "\nend"

and compile_call id args = 
   match id, args with
   | "=", [lhs; rhs] -> 
      "(" ^ compile_exp(lhs) ^ " = " ^ compile_exp(rhs) ^ ")"
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
   | Lam(args, body) -> "fn " ^ (String.concat ", " args) ^ "do\n" ^ (compile_exps body)
   (* | Lam(Some id, args, body) -> id ^ "= fn " ^ (String.concat ", " args) ^ "do\n" ^ (compile_exps body) *)
   | Case(_case, _matchings) -> "TODO"
   | Seq(exps) -> "do\n" ^ compile_exps(exps)

and compile_match (pat : pattern) (_rhs : typed_exp) = 
   let rhs_tmp = gensym() in 
   String.concat ";" [
      rhs_tmp ^ " = " ^ compile_typed_exp _rhs;
      (
         match pat with
         | Pin(id, _) -> "^" ^ id ^ " = " ^ rhs_tmp
         | Bind(id, _) -> id ^ " = " ^ rhs_tmp
         | Lens _ -> "TODO"
         | PatTuple (pat_list, _) -> 
            let pat_sym_list = pat_list |> List.map(fun pat -> (pat, gensym())) in
            let comma_separated = pat_sym_list |> List.map(fun (_, sym) -> sym) |> String.concat ", " in
            "{" ^ comma_separated ^ "} = " ^ rhs_tmp ^ ";"
            ^ 
            (pat_sym_list
            |> List.map(fun (pat, sym) -> compile_match pat (TVal(sym, TyInt)))
               (* WARN: WRONG TYPE *)
            |> String.concat ";")
         | PatList (pat_list, _) ->
            let pat_sym_list = pat_list |> List.map(fun pat -> (pat, gensym())) in
            let comma_separated = pat_sym_list |> List.map(fun (_, sym) -> sym) |> String.concat ", " in
            "[" ^ comma_separated ^ "] = " ^ rhs_tmp ^ ";"
            ^ 
            (pat_sym_list
            |> List.map(fun (pat, sym) -> compile_match pat (TVal(sym, TyInt)))
               (* WARN: WRONG TYPE *)
            |> String.concat ";")
         | Lit (l, _) -> compile_atom(l) ^ " = " ^ rhs_tmp
      );
      rhs_tmp (* the whole expression evaluates to rhs_tmp *)
   ]

and compile_typed_exps (exps : typed_exp list) = 
   (String.concat "\n" (List.map compile_typed_exp exps)) ^ "\nend"

and compile_typed_exp (exp : typed_exp) = 
   let rec compile_cases (sym : ident) (cases : (pattern * typed_exp list) list) =
      match cases with
      | (pat, body) :: rest -> 
        "try do\n" ^
         compile_match pat (TVal(sym, TyInt)) ^
         (*WARN: WRONGTYPE *)
         compile_typed_exps body ^
         "\nrescue\nMatchError ->" ^
         compile_cases sym rest ^
         "end"
         
      | [] -> "" in
   match exp with
   | TAtom (a, _) -> compile_atom a
   | TVal (id, _) -> id
   | TMatch (pat, rhs, _) -> compile_match pat rhs
   | TTuple (exps , _) -> "{" ^ (String.concat ", " (List.map compile_typed_exp exps)) ^ "}"
   | TList (exps , _) -> "[" ^ (String.concat ", " (List.map compile_typed_exp exps)) ^ "]"
   | TIf (test, _then, _else, _) -> 
      "(if " ^ (compile_typed_exp test) ^ " do\n" ^ (compile_typed_exps _then) ^ "\nelse\n" ^ (compile_typed_exps _else)   ^ ")"
   | TCall(id, params, _) -> id ^ ".(" ^ (String.concat ", " (List.map compile_typed_exp params)) ^ ")"
   | TLam (args, body, _) -> "fn " ^ (String.concat ", " args) ^ "do\n" ^ (compile_typed_exps body)
   | TCase (_matched, _matchings, _) -> 
      let rhs_tmp = gensym() in 
         rhs_tmp ^ "=" ^ compile_typed_exp _matched ^ "\n" ^
         compile_cases rhs_tmp _matchings
   | TSeq (exps, _) -> "do\n" ^ (compile_typed_exps exps)

(* Compiles to Elixir *)
let compile (exp: exp) = 
   {|#!/usr/bin/env elixir
Mix.install([])

# Captures operators, so we can genereate uniform codes
_eq = &==/2
_ne = &!=/2
_le = &<=/2
_lt = &</2
_ge = &>=/2
_gt = &>/2
_add = &+/2
_sub = &-/2
_mul = &*/2
_div = &//2
_and = &and/2
_or = &or/2
_as = fn v, t -> v end # TODO: do real type check
_not = &not/1
puts = &IO.puts/1

   |} ^ (compile_exp exp)
