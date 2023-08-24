%{
open Ast

(* let up_pat_to_exp (u : updatable_pattern) : exp =  *)
(*    match u with *)
(*    | Bind(id) -> Val(id) *)
(*    | Lens(obj, _method, params) -> Call(_method, Val(obj) :: params) *)

exception WrongPatternFormat

let rec break_last (l: 'a list) : ('a list * 'a) option = 
  match l with
  | [] -> None
  | [x] -> Some ([], x)
  | x :: rest -> 
    match break_last rest with
    | Some (l, last) -> Some (x :: l, last)
    | None -> None

let rec call_to_lens (_method : string) (args : exp list) =
  match break_last args with
  | Some (but_last, e) -> 
    begin match exp_to_pat e with
    | Updatable u ->  Updatable(Lens(u, _method, but_last))
    | _ -> raise WrongPatternFormat
    end
  | _ -> raise WrongPatternFormat

and exp_to_pat (p: exp) : pattern =
  match p with 
  | Atom a -> Lit a
  | UnPin id -> Pin id
  | Val id -> Updatable (Bind id)
  | Tuple t -> PatTuple (List.map exp_to_pat t)
  | List l -> PatList (List.map exp_to_pat l)
  | Call(id, args) -> call_to_lens id args
  | _ -> raise WrongPatternFormat

%}

%token <int> INT_CONSTANT
%token <float> FLOAT_CONSTANT
%token <string> KEYWORD
%token <string> STRING
%token <string> IDENT
%token <string> CALL // this is identifier followed by a LBRACKET, because disambiguiate we need this
%token <string> T_UPDATE_MATCH // this is identifier followed by a match operator, we also need it for disambiguiate.
%token <string> LABEL
// %token <string> PIN_IDENT

%token LPAREN
%token RPAREN
%token LBRACKET
%token RBRACKET
%token COMMA
%token COLON

%token DOT

%token T_AS
// %token FATARROW
%token T_EQ
%token T_NE
%token T_LE
%token T_LT
%token T_GE
%token T_GT
%token T_ADD
%token T_SUB
%token T_MUL
%token T_DIV
%token T_AND
%token T_OR
%token T_NOT
%token T_PIN
%token T_MATCH

%token DO
%token END
%token IF
/* %token ELSE_IF */
%token ELSE
%token FUNCTION
%token CASE
%token WHEN
// %token INT_T
// %token STR_T
// %token F64_T
// %token TYPE_T
// %token KEYWORD_T

%token EOF

%right T_MATCH // T_UPDATE_MATCH
%left T_OR
%left T_AND
%left T_AS
%left T_EQ T_NE T_LE T_LT T_GE T_GT
%left T_ADD T_SUB
%left T_MUL T_DIV
//%left DOT
%nonassoc T_NOT
%nonassoc T_PIN

%type <exp> program
// %type <pattern> pattern
// %type <updatable_pattern> updatable_pattern
%type <unary_operator> un_op

%start program

%%

program: 
  | exps=list(exp) EOF { Seq(exps) }

%inline un_op: 
  | T_NOT { NOT }

// Satement-like expressions
exp: 
  | IF test=exp _then=no_end_terminated_exps ELSE _else=end_terminated_exps { If(test, _then, _else) }
  | CASE matched=exp body=list(case_param) END { Case(matched, body) }
  | FUNCTION LPAREN args=separated_list(COMMA, exp4) RPAREN body=end_terminated_exps { 
    Lam(List.map exp_to_pat args, body)
  }
  | FUNCTION name=IDENT LPAREN args=separated_list(COMMA, exp4) RPAREN body=end_terminated_exps { 
    Match(Updatable(Bind name), Lam(List.map exp_to_pat args, body))
  }
  | DO exps=end_terminated_exps { Seq(exps) }
  | exp1 { $1 }

case_param: 
  | WHEN pat=exp4 act=no_end_terminated_exps { 
    (exp_to_pat pat, act) 
  }

no_end_terminated_exps: 
  | l=list(exp) { l }
  | COLON e=exp { [e] }

end_terminated_exps: 
  | l=list(exp) END { l }
  | COLON e=exp { [e] }

// update match, not nestable
exp1: 
  | pat=exp4 op=T_UPDATE_MATCH rhs=exp3 { 
    match exp_to_pat pat with
    | Updatable u -> Match (Updatable u, Call(op, [pat; rhs]))
    | _ -> raise WrongPatternFormat
  }
  | exp3 { $1 }

// "Expression-like" expressions, all rules conflicts with do block.
exp3: 
  | pat=exp4 T_MATCH rhs=exp3 {
    Match(exp_to_pat pat, rhs)
  }
  | e1=exp3 op=bin_op e2=exp3 { 
    Binary(op, e1, e2)
  }
  | op=un_op e=exp3 { 
    Unary(op, e)
  }
  | T_PIN id=IDENT {
    UnPin(id)
  }
  | exp4 { $1 }

// Expressions that have higher precedence than DOT
exp4: 
  | obj=exp4 DOT _method=CALL args=separated_list(COMMA, exp) RPAREN { Call(_method, args @ [obj]) }
  // above rule conflicts with binary/unary operation
  | id=CALL l=separated_list(COMMA, exp) RPAREN { Call(id, l) }
  | LPAREN first=exp COMMA l=separated_nonempty_list(COMMA, exp) RPAREN { Tuple(first :: l) }
  | LBRACKET l=separated_list(COMMA, exp) RBRACKET { List(l) }
  | LPAREN e=exp RPAREN {e}
  | a=atom { Atom(a) }
  | id=IDENT { Val(id) }
  | LPAREN RPAREN { Tuple([]) }

%inline bin_op: 
  | T_EQ { EQ }
  | T_NE { NE }
  | T_LE { LE }
  | T_LT { LT }
  | T_GE { GE }
  | T_GT { GT }
  | T_ADD { ADD }
  | T_SUB { SUB }
  | T_MUL { MUL }
  | T_DIV { DIV }
  | T_AND { AND }
  | T_OR { OR }
  | T_AS { AS }
  // | T_MATCH { MATCH }

// updatable_pattern: 
//   | id=IDENT { Bind(id) }
//   | obj=IDENT DOT _method=CALL args=separated_list(COMMA, exp) RPAREN { Lens(obj, _method, args) }
//   // above rule conflicts with binary/unary operation
//   | _method=CALL args=separated_list(COMMA, exp) COMMA obj=IDENT RPAREN { Lens(obj, _method, args) }

// pattern: 
//   | u=updatable_pattern { Updatable(u) }
//   | pinned=PIN_IDENT { Pin(pinned) }
//   | LPAREN l=separated_list(COMMA, pattern) RPAREN { PatTuple(l) }
//   | LBRACKET l=separated_list(COMMA, pattern) RBRACKET { PatList(l) }
//   | a=atom { Lit(a) }


atom: 
  // | INT_T { Type TInt }
  // | STR_T { Type TStr }
  // | F64_T { Type TF64 }
  // | TYPE_T { Type TType }
  // | KEYWORD_T { Type TKeyword }
  | i=INT_CONSTANT { Int i }
  | f=FLOAT_CONSTANT { F64 f }
  | s=STRING { Str s }
  | kw=KEYWORD { Keyword kw }
