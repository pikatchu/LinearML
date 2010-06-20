%{
open Ast 
%}


%token ARROW 
%token BAR
%token COLON
%token COLONCOLON
%token COMMA
%token <Pos.t * string> CSTR
%token DOT
%token ELSE
%token END
%token EOF 
%token EQ
%token FUN
%token <Pos.t * string> ID
%token IF
%token IN
%token <Pos.t * string> INT
%token LET
%token <Pos.t> LB
%token <Pos.t> LCB
%token <Pos.t> LP
%token MATCH
%token MINUS
%token MODULE
%token <Pos.t> RB
%token <Pos.t> RCB
%token <Pos.t> RP
%token PLUS
%token SC   
%token STAR 
%token STRUCT
%token THEN
%token <Pos.t * string> TVAR
%token TYPE
%token UNDERSCORE
%token WITH

%nonassoc match_
%nonassoc let_
%nonassoc if_
%left BAR
%right ARROW
%left SC
%left COMMA
%left EQ
%right COLONCOLON
%left PLUS MINUS 
%left STAR
%left apply


%start program
%type <unit> program

%%

program: 
| module_l EOF          {}

module_l:
|                       {}
| module_ module_l      {}

module_: 
| MODULE CSTR EQ STRUCT def_l {}

def_l:
| END {}
| def def_l {}

def:
| MODULE CSTR EQ CSTR {}
| LET simpl_pat_l EQ expr {}
| type_def {} 

type_def:
| TYPE ID EQ type_expr {}
| TYPE LP tvar_l RP ID EQ type_expr {}

tvar_l:
| TVAR {}
| TVAR COMMA TVAR {}

type_expr_l:
| type_expr {}
| type_expr COMMA type_expr {}

type_expr:
| ID {}
| TVAR {}
| CSTR DOT ID {}
| LP type_expr_l RP ID {}
| LP type_expr_l RP CSTR DOT ID {}
| type_expr STAR type_expr {}
| type_expr ARROW type_expr {}
| LCB field_type_seq RCB {}

field_type_seq:
| field_type {}
| field_type SC {}
| field_type SC field_type_seq {}

field_type:
| ID COLON type_expr {}

simpl_pat_l:
| simpl_pat {}
| simpl_pat simpl_pat_l {}

simpl_pat: 
| ID         {}
| UNDERSCORE {}
| LP RP      {}
| LP simpl_pat RP {}
| LP simpl_pat COLON type_expr RP {}
| simpl_pat COMMA simpl_pat {}

pat_expr_l:
| {}
| pat_expr {}
| pat_expr_l BAR pat_expr {} 

pat_expr:
| pat ARROW expr {}

pat_field:
| ID {}
| ID EQ pat {}

pat_field_l:
| UNDERSCORE {}
| pat_field {}
| pat_field SC {}
| pat_field SC pat_field_l {}

pat_seq:
| {}
| pat SC pat_seq {}

pat:
| ID {}
| INT {}
| UNDERSCORE {}
| CSTR       {}
| CSTR ID    {}
| CSTR LP pat RP {}
| LP pat RP {}
| pat COMMA pat {}
| LCB pat_field_l RCB {}
| pat COLONCOLON pat {}
| LB pat_seq RB {}

field:
| ID {}
| ID EQ expr {}

field_l:
| field {}
| field SC {}
| field SC field_l {}

seq_expr:
| {}
| expr {}
| expr SC seq_expr {}

simpl_expr: 
| ID {}
| ID DOT ID {}
| CSTR DOT ID {}
| INT {}
| CSTR {}
| LP expr RP {}
| LCB field_l RCB {}
| LP RP {}
| LB seq_expr RB {}

simpl_expr_l: 
| simpl_expr {}
| simpl_expr simpl_expr_l {}

expr:
| MATCH expr WITH pat_expr_l %prec match_ {}
| LET simpl_pat_l EQ expr IN expr %prec let_ {}
| IF expr THEN expr ELSE expr %prec if_ {}
| FUN simpl_pat_l ARROW expr {}
| expr EQ expr     {}
| expr PLUS expr   {}
| expr MINUS expr  {}
| expr STAR  expr  {}
| expr COMMA expr  {}
| expr COLONCOLON expr {}
| LP expr COLON type_expr RP {}
| simpl_expr  %prec apply {}
| simpl_expr simpl_expr_l %prec apply {}

