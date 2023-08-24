{
open Lexing
open Parser

let advance_line lexbuf =
  let pos = lexbuf.lex_curr_p in
  let pos' = { pos with
    pos_bol = lexbuf.lex_curr_pos;
    pos_lnum = pos.pos_lnum + 1
  } in
  lexbuf.lex_curr_p <- pos'

let drop_str n s = 
  let len = String.length s in
    String.sub s n (len - n)
let drop_str_r n s = 
  let len = String.length s in
    String.sub s 0 (len - n)
}

let digit = ['0'-'9']
let sign = ['-' '+']
let exponent = ['e' 'E']
let alpha = ['a'-'z' 'A'-'Z']

let int_constant = sign? digit+
let float_constant = sign? digit+ '.' digit+ (exponent sign? digit+)?
let identifier = alpha (alpha | digit | '_')*

let keyword = ':' (alpha | digit) +

let whitespace = [' ' '\t']+
let newline = '\r' | '\n' | "\r\n"

(* Rules *)

rule token = parse
  | int_constant { INT_CONSTANT (int_of_string (Lexing.lexeme lexbuf)) }
  | float_constant { FLOAT_CONSTANT (float_of_string (Lexing.lexeme lexbuf)) }
  | keyword { KEYWORD (drop_str 1 (Lexing.lexeme lexbuf)) }
  (* binary operators *)
  | identifier "(" { CALL (drop_str_r 1 (Lexing.lexeme lexbuf)) }
  | "(" { LPAREN }
  | ")" { RPAREN }
  | "[" { LBRACKET }
  | "]" { RBRACKET }
  | "," { COMMA }
  | "." { DOT }
  | identifier ":" { LABEL (drop_str_r 1 (Lexing.lexeme lexbuf)) } 
  | ":" { COLON }
  | "^" { T_PIN }
  | "as" { T_AS }
  | (identifier | "+" | "-" | "*" | "/" | "and" | "or" | "not") "=" { T_UPDATE_MATCH (drop_str_r 1 (Lexing.lexeme lexbuf)) }
  | "==" { T_EQ }
  | "!=" { T_NE }
  | "<=" { T_LE }
  | "<" { T_LT }
  | ">=" { T_GE }
  | ">" { T_GT }
  | "+" { T_ADD }
  | "-" { T_SUB }
  | "*" { T_MUL }
  | "/" { T_DIV }
  | "and" { T_AND }
  | "or" { T_OR }
  | "not" { T_NOT }
  | "=" { T_MATCH }

  (* preserved words *)
  | "end" { END }
  | "if" { IF }
  (*| "elif" { ELSE_IF } *)
  | "else" { ELSE }
  (* | "recur" { RECUR } *)
  | "fn" { FUNCTION }
  | "match" { MATCH }
  | "case" { CASE }
  | "when" { WHEN }
  | "do" { DO }

  | "true" { BOOL_CONSTANT true }
  | "false" { BOOL_CONSTANT false }

  (* primitive types *)
  (* | "Int" { INT_T }*)
  (* | "Str" { STR_T }*)
  (* | "F64" { F64_T }*)
  (* | "Type" { TYPE_T }*)
  (* | "Keyword" { KEYWORD_T }*)

  (*This is for disambiguiate, as we allow arbitrary sequence of expressions, and
    `ID (..)` is a tuple followed by an ID, while `ID(..)` is a call *)
  | identifier { IDENT (Lexing.lexeme lexbuf) }
  | '"' { read_string (Buffer.create 32) lexbuf }
  (* etc. *)
  | whitespace { token lexbuf }
  | newline { token lexbuf } (* just ignore *)
  | eof { EOF }
  | _ { raise (Failure ("Character not allowed in source text: '" ^ Lexing.lexeme lexbuf ^ "'")) }

and read_string buf = parse
  | '"' { STRING (Buffer.contents buf) }
  | '\\' '"' { Buffer.add_char buf '"'; read_string buf lexbuf } 
  | '\\' 'n' { Buffer.add_char buf '\n'; read_string buf lexbuf } 
  | [^ '"' '\\']+ { Buffer.add_string buf (Lexing.lexeme lexbuf); read_string buf lexbuf } 
  | _ { raise (Failure ("Illegal string character: " ^ Lexing.lexeme lexbuf)) }
  | eof { raise (Failure ("String is not terminated")) }
