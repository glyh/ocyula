%{
open Ast

type bin_operator = 
   | EQ | NE | LE | LT | GE | GT
   | ADD | SUB | MUL | DIV
   | AND | OR
   | AS (* type annotation *)
   (* | MATCH (* pattern matching *) *)

let bin_op_to_str = function
   | EQ -> "_eq"
   | NE -> "_ne"
   | LE -> "_le"
   | LT -> "_lt"
   | GE -> "_ge"
   | GT -> "_gt"
   | ADD -> "_add"
   | SUB -> "_sub"
   | MUL -> "_mul"
   | DIV -> "_div"
   | AND -> "_and"
   | OR -> "_or"
   | AS -> "_as"
   (* | MATCH -> "!match" *)

let un_op_to_str = function
   | NOT -> "_not"

let up_pat_to_exp (u : Ast.updatable_pattern) : Ast.exp = 
   match u with
   | Bind(id) -> Val(id)
   | Lens(obj, _method, params) -> Call(_method, Val(obj) :: params)

%}

%token <int> INT_CONSTANT
%token <float> FLOAT_CONSTANT
%token <string> KEYWORD
%token <string> STRING
%token <string> IDENT
%token <string> CALL // this is identifier followed by a LBRACKET, because disambiguiate we need this
%token <string> T_UPDATE_MATCH // this is identifier followed by a match operator, we also need it for disambiguiate.
// %token <string> LABEL
%token <string> PIN_IDENT

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

%left T_OR
%left T_AND
%right T_MATCH T_UPDATE_MATCH
%left T_AS
%left T_EQ T_NE T_LE T_LT T_GE T_GT
%left T_ADD T_SUB
%left T_MUL T_DIV
//%left DOT
%nonassoc T_NOT

%type <Ast.exp> program
%type <Ast.pattern> pattern
%type <Ast.updatable_pattern> updatable_pattern
%type <Ast.unary_operator> un_op

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
  | FUNCTION LPAREN args=separated_list(COMMA, pattern) RPAREN body=end_terminated_exps { 
    Lam(args, body)
  }
  | FUNCTION name=IDENT LPAREN args=separated_list(COMMA, pattern) RPAREN body=end_terminated_exps { 
    Match(Updatable(Bind name), Lam(args, body))
    (* Call(bin_op_to_str(MATCH), [Val(name); Lam(args, body)]) *)
  }
  | DO exps=end_terminated_exps { Seq(exps) }
  | exp1 { $1 }

case_param: 
  | WHEN pat=pattern act=no_end_terminated_exps { (pat, act) }

no_end_terminated_exps: 
  | l=list(exp) { l }
  | COLON e=exp { [e] }

end_terminated_exps: 
  | l=list(exp) END { l }
  | COLON e=exp { [e] }

// "Expression-like" expressions, all rules conflicts with do block.
exp1: 
  | pat=updatable_pattern op=T_UPDATE_MATCH rhs=exp1 { 
    let evaluated = up_pat_to_exp pat in
      Match(Updatable pat, Call(op, [evaluated; rhs]))
  }
  | e1=exp1 op=bin_op e2=exp1 { 
    Call(bin_op_to_str(op), [e1; e2])
  }
  | op=un_op e=exp1 { 
    Call(un_op_to_str(op), [e])
  }
  | exp2 { $1 }

exp2: 
  | selected=exp2 DOT id=CALL l=separated_list(COMMA, exp) RPAREN { Call(id, l @ [selected]) }
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
  //| T_MATCH { MATCH }

updatable_pattern: 
  | id=IDENT { Bind(id) }
  | target=IDENT DOT id=CALL args=separated_list(COMMA, exp) RPAREN { Lens(target, id, args) }
  // above rule conflicts with binary/unary operation
  | id=CALL args=separated_list(COMMA, exp) COMMA target=IDENT RPAREN { Lens(target, id, args) }

pattern: 
  | u=updatable_pattern { Updatable(u) }
  | pinned=PIN_IDENT { Pin(pinned) }
  | LPAREN l=separated_list(COMMA, pattern) RPAREN { PatTuple(l) }
  | LBRACKET l=separated_list(COMMA, pattern) RBRACKET { PatList(l) }
  | a=atom { Lit(a) }

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
