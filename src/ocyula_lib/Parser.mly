%{
open Ast

let bin_op_to_str ( op : bin_operator) =
   match op with 
   | EQ -> "=="
   | NE -> "!="
   | LE -> "<="
   | LT -> "<"
   | GE -> ">="
   | GT -> ">"
   | ADD -> "+"
   | SUB -> "-"
   | MUL -> "*"
   | DIV -> "/"
   | AND -> "and"
   | OR -> "or"
   | AS -> "as"
   | MATCH -> "="

let un_op_to_str = function
   | NOT -> "not"
%}

%token <int> INT_CONSTANT
%token <float> FLOAT_CONSTANT
%token <string> KEYWORD
%token <string> STRING
%token <string> IDENT
%token <string> CALL // this is identifier followed by a LBRACKET, because disambiguiate we need this
%token <string> T_UPDATE_MATCH
%token <string> LABEL

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
  | FUNCTION name=option(ident) LPAREN args=separated_list(COMMA, ident) RPAREN body=end_terminated_exps { Lam(name, args, body) }
  | DO exps=end_terminated_exps { Seq(exps) }
  | exp1 { $1 }

case_param: 
  | WHEN pat=exp act=no_end_terminated_exps { (pat, act) }

no_end_terminated_exps: 
  | l=list(exp) { l }
  | COLON e=exp { [e] }

end_terminated_exps: 
  | l=list(exp) END { l }
  | COLON e=exp { [e] }

// "Expression-like" expressions, all rules conflicts with do block.
exp1: 
  | e1=exp1 op=T_UPDATE_MATCH e2=exp1 { 
    Call(bin_op_to_str(MATCH), [e1; Call(op, [e1; e2])])
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
  | LPAREN first=exp COMMA l=separated_nonempty_list(COMMA, exp) RPAREN { Tuple(first :: l) }
  | LBRACKET l=separated_list(COMMA, exp) RBRACKET { List(l) }
  |id=CALL l=separated_list(COMMA, exp) RPAREN { Call(id, l) }
  | LPAREN e=exp RPAREN {e}
  | a=atom { Atom(a) }
  | id=ident { Val(id) }
  | LPAREN RPAREN { Tuple([]) }

ident:
  | id=IDENT { id }

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
  | T_MATCH { MATCH }

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
