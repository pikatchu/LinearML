%{
open Ast 

let btw (x,_) (y,_) = Pos.btw x y

let rec last = function
  | [] -> assert false
  | [x,_] -> x
  | _ :: rl -> last rl

let rec tapply x = function
  | [] -> x
  | t :: rl -> tapply (btw x t, Tapply (t, [x])) rl

let lapply pos x = function
  | [] -> failwith "Syntax error TODO"
  | t :: rl -> tapply (Pos.btw pos (fst t), Tapply (t, x)) rl

%}

%token AND
%token ARROW 
%token ASSIGN
%token BAR
%token BEGIN
%token <Pos.t * string> CHAR
%token COLEQ
%token COLON
%token COMMA
%token <Pos.t * string> CSTR
%token DO
%token DONE
%token DOT
%token ELSE
%token END
%token EOF 
%token EQ
%token EQEQ
%token FOR
%token FROM
%token <Pos.t> FUN
%token GT
%token GTE
%token <Pos.t * string> ID
%token <Pos.t> IF
%token IN
%token <Pos.t * string> INT
%token <Pos.t * string> FLOAT
%token <Pos.t> LET
%token <Pos.t> LB
%token <Pos.t> LCB
%token <Pos.t> LP
%token LT
%token LTE
%token <Pos.t> MATCH
%token <Pos.t> MINUS
%token MODULE
%token OF
%token <Pos.t> RB
%token <Pos.t> RCB
%token <Pos.t> RP
%token PLUS
%token REC
%token SC   
%token STAR 
%token <Pos.t * string> STRING
%token SIG
%token STRUCT 
%token THEN
%token TO
%token <Pos.t * string> TVAR
%token TYPE
%token <Pos.t> UNDERSCORE
%token VAL
%token WITH
%token WHEN
%token WHILE
%token <Pos.t> TRUE FALSE

%nonassoc match_
%nonassoc let_
%nonassoc if_
%left BAR
%right ARROW
%right SC
%right COMMA
%left EQ LT LTE GT GTE
%left PLUS MINUS 
%left STAR
%left apply_
%left unary_minus


%start program
%type <Ast.program> program
%type <Ast.expr> expr

%%

program: 
| module_l EOF          { $1 }

module_l:
|                       { [] }
| module_ module_l      { $1 :: $2 }

module_: 
| MODULE CSTR COLON SIG decl_l
    EQ STRUCT def_l { { md_id = $2 ; 
			md_decls = $5 ; 
			md_defs = $8 } }

decl_l:
| END { [] }
| type_def decl_l { $1 :: $2 }

def_l:
| END { [] }
| def def_l { $1 :: $2 }

def:
| MODULE CSTR EQ CSTR { Dmodule ($2, $4) }
| LET ID EQ ID { Dalias ($2, $4) }
| LET ID simpl_pat_l EQ expr { Dlet ($2, $3, $5) }
| LET REC ID simpl_pat_l EQ expr expr_l { Dletrec (($3, $4, $6) :: $7) }

expr_l:
| { [] }
| AND ID simpl_pat_l EQ expr expr_l { ($2, $3, $5) :: $6 }

simpl_pat:
| ID { fst $1, Pid $1 }
| LP pat_l RP { let x, y, z = $2 in Pos.btw x y, Ptuple z }
| UNDERSCORE { $1, Pany }

simpl_pat_l:
| simpl_pat { [$1] }
| simpl_pat simpl_pat_l { $1 :: $2 }

type_def:
| TYPE type_decl type_decl_l { Dtype ($2 :: $3)}
| VAL ID COLON type_expr { Dval ($2, $4) }

type_decl:
| type_id EQ LCB field_type_seq RCB { $1, (fst (fst $1), Trecord $4) }
| type_id EQ algebric { $1, (fst (fst $1), Talgebric $3) }
| type_id EQ BAR algebric { $1, (fst (fst $1), Talgebric $4) }
| type_id EQ type_expr { $1, (fst (fst $1), Tabbrev $3) }

type_decl_l:
| { [] }
| AND type_decl type_decl_l { $2 :: $3 }

tvar_l:
| TVAR { [$1] }
| TVAR COMMA tvar_l { $1 :: $3 }

type_id:
| ID { $1, [] }
| TVAR ID { $2, [$1] }
| LP tvar_l RP ID { $4, $2 }

variant: 
| CSTR { $1, None }
| CSTR OF type_expr { $1, Some $3 }

algebric:
| variant { [$1] }
| variant BAR algebric { $1 :: $3 }

type_expr_l:
| type_expr { [$1] }
| type_expr COMMA type_expr_l { $1 :: $3 }

simpl_type_expr:
| ID { fst $1, Tid $1 }
| CSTR DOT ID { btw $1 $3, Tpath ($1, $3) }

simpl_type_expr_l:
| { [] }
| simpl_type_expr simpl_type_expr_l { $1 :: $2 }

type_expr:
| TVAR simpl_type_expr_l { tapply (fst $1, Tvar $1) $2 }
| LP type_expr_l RP simpl_type_expr_l { lapply $1 $2 $4 }
| simpl_type_expr simpl_type_expr_l { tapply $1 $2 }
| type_expr ARROW type_expr { btw $1 $3, Tfun ($1, $3) }
| type_expr STAR type_expr { btw $1 $3, Ttuple [$1; $3] }

field_type_seq:
| field_type { [$1] }
| field_type SC { [$1] }
| field_type SC field_type_seq { $1 :: $3 }

field_type:
| ID COLON type_expr { ($1, $3) }

pat_field:
| ID { fst $1, PFid $1 }
| ID EQ pat { btw $1 $3, PField ($1, $3) }

pat_field_l:
| UNDERSCORE { [$1, PFany] }
| pat_field { [$1] }
| pat_field SC { [$1] }
| pat_field SC pat_field_l { $1 :: $3 }

pat_:
| TRUE { $1, Pbool true }
| FALSE { $1, Pbool false }
| CHAR { fst $1, Pchar (snd $1) }
| FLOAT { fst $1, Pfloat (snd $1) }
| STRING { fst $1, Pstring (snd $1) }
| LP RP { Pos.btw $1 $2, Punit }
| ID { fst $1, Pid $1 }
| INT { fst $1, Pint (snd $1) }
| UNDERSCORE { $1, Pany }
| CSTR { fst $1, Pcstr $1 }
| CSTR LP pat RP  { Pos.btw (fst $1) $4, Pvariant ($1, $3) }
| CSTR DOT CSTR { btw $1 $3, Ppath_cstr ($1, $3) }
| CSTR DOT CSTR LP pat RP { Pos.btw (fst $1) $4, Ppath_variant ($1, $3, $5) }
| LCB pat_field_l RCB { Pos.btw $1 $3, Precord $2 }
| LP pat RP { $2 }

pat_l:
| pat_ { fst $1, fst $1, [$1] }
| pat_ COMMA pat_l { 
  let _, last, x = $3 in
  fst $1, last, $1 :: x 
}

pat:
| pat BAR pat { btw $1 $3, Pbar ($1,$3) }
| pat_l { let x, y, z = $1 in Pos.btw x y, Ptuple z }

pat_action_l:
| { [] }
| pat_action_l BAR pat_action { $3 :: $1 } 

pat_action:
| pat ARROW expr { $1, $3 }

field:
| ID EQ expr { $1, $3 }

field_l:
| field { [$1] }
| field SC { [$1] }
| field SC field_l { $1 :: $3 }

simpl_expr: 
| ID { fst $1, Eid $1 }
| LP RP { Pos.btw $1 $2, Eunit }
| TRUE { $1, Ebool true }
| FALSE { $1, Ebool false }
| INT { fst $1, Eint (snd $1) }
| FLOAT { fst $1, Efloat (snd $1) }
| CSTR { fst $1, Ecstr $1 }
| STRING { fst $1, Estring $1 }
| CHAR { fst $1, Echar $1 }
| LCB field_l RCB { Pos.btw $1 $3, Erecord $2 }
| simpl_expr LB expr RB { btw $1 $3, Ederef ($1, $3) }
| simpl_expr DOT ID { btw $1 $3, Epath ($1, $3) }
| LP expr RP { $2 }
| BEGIN expr END { $2 }

simpl_expr_l:
| { [] }
| simpl_expr simpl_expr_l { $1 :: $2 }

expr:
| IF expr THEN expr ELSE expr %prec if_ { Pos.btw $1 (fst $6), Eif ($2, $4, $6) }
| LET pat EQ expr IN expr %prec let_ { Pos.btw $1 (fst $6), Elet ($2, $4, $6) }
| MATCH expr WITH pat_action_l %prec match_ { Pos.btw $1 (fst (last $4)), Ematch ($2, $4) }
| FUN simpl_pat_l ARROW expr { Pos.btw $1 (fst $4), Efun ($2, $4) }
| MINUS expr %prec unary_minus { Pos.btw $1 (fst $2), Euminus $2 }
| expr EQ expr { btw $1 $3, Eeq ($1, $3) }
| expr LT expr { btw $1 $3, Elt ($1, $3) }
| expr LTE expr { btw $1 $3, Elte ($1, $3) }
| expr GT expr { btw $1 $3, Egt ($1, $3) }
| expr GTE expr { btw $1 $3, Egte ($1, $3) }
| expr PLUS expr { btw $1 $3, Eplus ($1, $3) }
| expr MINUS expr { btw $1 $3, Eminus ($1, $3) }
| expr STAR expr { btw $1 $3, Estar ($1, $3) }
| expr SC expr { btw $1 $3, Eseq ($1, $3) }
| expr COMMA expr { btw $1 $3, Etuple [$1;$3] }
| simpl_expr simpl_expr_l { 
  match $2 with 
  | [] -> $1 
  | _ -> Pos.btw (fst $1) (last $2), Eapply ($1, $2)
}