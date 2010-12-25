%{
open Ast 

let btw (x,_) (y,_) = Pos.btw x y

let empty pos = 
  pos, Eecstr ((pos, "List"), (pos, "Empty"))

let pempty pos = 
  pos, Pecstr ((pos, "List"), (pos, "Empty"))

let cons ((pos, _) as x) rl = 
  let cstr = (pos, Eecstr ((pos, "List"), (pos, "Cons"))) in
  pos, Eapply (cstr, [x ; rl])

let pcons ((pos, _) as x) rl = 
  pos, Pevariant ((pos, "List"), (pos, "Cons"), (pos, Ptuple [x ; rl]))

let rec make_list cons empty l = 
  match l with
  | [] -> assert false
  | [pos, _ as x] -> cons x (empty pos)
  | ((pos, _) as x) :: rl -> cons x (make_list cons empty rl)

let make_elist pos l = 
  match l with
  | [] -> empty pos
  | _ -> make_list cons empty l

let make_plist pos l = 
  match l with
  | [] -> pempty pos
  | _ -> make_list pcons pempty l

let rec last = function
  | [] -> assert false
  | [x,_] -> x
  | _ :: rl -> last rl

let rec pat_end = function
  | [] -> assert false
  | [_,x] -> (fst x)
  | _ :: rl -> pat_end rl


let rec tapply x = function
  | [] -> x
  | t :: rl -> tapply (btw x t, Tapply (t, [x])) rl

let lapply pos x = function
  | [] -> Pos.btw pos (last x), Ttuple x
  | t :: rl -> tapply (Pos.btw pos (fst t), Tapply (t, x)) rl

let rec simpl_arg e = function
  | [] -> e
  | `Id x :: rl -> 
      let p = btw e x in
      simpl_arg (p, Efield (e, x)) rl
  | `Path (x1, x2) :: rl -> 
      let p = btw e x2 in
      simpl_arg (p, Eefield (e, x1, x2)) rl

let rec cstr_arg id = function
  | `Null -> fst id, Ecstr id
  | `Cstr x -> btw id x, Eecstr (id, x)
  | `Id f -> btw id f, Eextern (id, f)

let dtype l = (List.map (fun ((x, idl), ty) -> 
  match idl with
  | [] -> x, ty
  | _ -> x, (fst x, Tabs (idl, ty))) l)

%}

%token <Pos.t> AND
%token <Pos.t> ARROW 
%token <Pos.t> SARROW 
%token <Pos.t> AS
%token <Pos.t> ASSIGN
%token <Pos.t> BAR
%token <Pos.t> BEGIN
%token <Pos.t * string> CHAR
%token <Pos.t> COLEQ
%token <Pos.t> COLON
%token <Pos.t> COMMA
%token <Pos.t * string> CSTR
%token <Pos.t> DO
%token <Pos.t> DONE
%token <Pos.t> DOT
%token <Pos.t> ELSE
%token <Pos.t> END
%token <Pos.t> EOF 
%token <Pos.t> EQ
%token <Pos.t> EQEQ
%token <Pos.t> FOR
%token <Pos.t> FROM
%token <Pos.t> FUN
%token <Pos.t> GT
%token <Pos.t> GTE
%token <Pos.t * string> ID
%token <Pos.t> IF
%token <Pos.t> IN
%token <Pos.t * string> INT
%token <Pos.t * string> FLOAT
%token <Pos.t> LET
%token <Pos.t> LB
%token <Pos.t> LCB
%token <Pos.t> LP
%token <Pos.t> LT
%token <Pos.t> LTE
%token <Pos.t> MATCH
%token <Pos.t> MINUS
%token <Pos.t> MODULE
%token <Pos.t> OF
%token <Pos.t> RB
%token <Pos.t> RCB
%token <Pos.t> REC
%token <Pos.t> RP
%token <Pos.t> PLUS
%token <Pos.t> SC   
%token <Pos.t> STAR 
%token <Pos.t * string> STRING
%token <Pos.t> SIG
%token <Pos.t> STRUCT 
%token <Pos.t> THEN
%token <Pos.t> TILD
%token <Pos.t> TO
%token <Pos.t * string> TVAR
%token <Pos.t> TYPE
%token <Pos.t> UNDERSCORE
%token <Pos.t> VAL
%token <Pos.t> WITH
%token <Pos.t> WHEN
%token <Pos.t> WHILE
%token <Pos.t> TRUE FALSE
%token <Pos.t> COLONCOLON

%nonassoc match_
%nonassoc let_
%nonassoc if_
%right COLEQ
%nonassoc AS
%left BAR
%right ARROW SARROW
%right SC
%right COMMA
%left EQ LT LTE GT GTE
%right COLONCOLON
%left PLUS MINUS 
%left STAR
%left apply_ DOT
%nonassoc module_dot
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
| MODULE CSTR EQ STRUCT def_l 
    { { md_id = $2 ; 
	md_defs = $5 } 
    }

def_l:
| END { [] }
| def def_l { $1 :: $2 }

def:
| MODULE CSTR EQ CSTR { Dmodule ($2, $4) }
| TYPE type_decl type_decl_l { Dtype (dtype ($2 :: $3))}
| VAL ID COLON type_expr external_opt { Dval ($2, $4, $5) }
| LET rec_opt ID simpl_pat_l EQ expr { Dlet ($3, $4, $6) }

rec_opt:
| { }
| REC { } 

external_opt:
| { None }
| EQ STRING { Some $2 }

type_decl:
| type_id { $1, (Pos.none, Tabstract) }
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
| type_expr ARROW type_expr { btw $1 $3, Tfun (Lfun, $1, $3) }
| type_expr SARROW type_expr { btw $1 $3, Tfun (Cfun, $1, $3) }
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
| TILD ID { Pos.btw $1 (fst $2), PField ($2, (fst $2, Pid $2)) }
| UNDERSCORE { ($1, PFany) }

pat_field_l:
| pat_field { [$1] }
| pat_field SC { [$1] }
| pat_field SC pat_field_l { $1 :: $3 }

simpl_pat:
| ID { fst $1, Pid $1 }
| CSTR { fst $1, Pcstr $1 } 
| LP RP { Pos.btw $1 $2, Punit }
| LP pat RP { $2 }
| UNDERSCORE { $1, Pany }
| TRUE { $1, Pbool true }
| FALSE { $1, Pbool false }
| CHAR { fst $1, Pchar $1 }
| FLOAT { fst $1, Pfloat $1 }
| STRING { fst $1, Pstring $1 }
| INT { fst $1, Pint $1 }
| LCB pat_field_l RCB { Pos.btw $1 $3, Precord $2 }
| LB pat_list RB { make_plist (Pos.btw $1 $3) $2 }

pat_list:
| { [] }
| simpl_pat { [$1] }
| simpl_pat SC pat_list { $1 :: $3 }

simpl_pat_l:
| simpl_pat { [$1] }
| simpl_pat simpl_pat_l { $1 :: $2 }

pat_:
| simpl_pat { $1 }
| pat_ COLONCOLON pat_ { 
  let pos = btw $1 $3 in
  pos, Pevariant (($2, "List"), ($2, "Cons"), (pos, Ptuple [$1 ; $3]))
}
| CSTR simpl_pat_l { 
  let p, tuple = Pos.list $2 in
  Pos.btw (fst $1) p, 
  Pvariant ($1, (p, Ptuple tuple))
}
| CSTR DOT CSTR { btw $1 $3, Pecstr ($1, $3) }
| CSTR DOT CSTR simpl_pat_l { 
  let p, tuple = Pos.list $4 in
  Pos.btw (fst $1) p, 
  Pevariant ($1, $3, (p, Ptuple tuple)) 
}

pat_l:
| pat_ { fst $1, fst $1, [$1] }
| pat_ COMMA pat_l { 
  let _, last, x = $3 in
  fst $1, last, $1 :: x 
}

pat:
| pat AS ID { btw $1 $3, Pas ($3, $1) }
| pat BAR pat { btw $1 $3, Pbar ($1,$3) }
| pat_l { let x, y, z = $1 in Pos.btw x y, Ptuple z }

pat_action_l:
| { [] }
| pat_action { [$1] }
| pat_action_l BAR pat_action { $3 :: $1 } 

pat_action:
| pat ARROW expr { $1, $3 }

field:
| ID EQ expr { Eflocl ($1, $3) }
| TILD ID { Eflocl ($2, (fst $2, Eid $2)) }
| TILD CSTR DOT ID { Efextr ($2, $4, (fst $4, Eid $4)) }
| CSTR DOT ID EQ expr { Efextr ($1, $3, $5) }

field_l:
| field { [$1] }
| field SC { [$1] }
| field SC field_l { $1 :: $3 }

simpl_expr: 
| ID dot_id { simpl_arg (fst $1, Eid $1) $2 }
| CSTR dot_cstr { cstr_arg $1 $2 }
| LP RP { Pos.btw $1 $2, Eunit }
| TRUE { $1, Ebool true }
| FALSE { $1, Ebool false }
| INT { fst $1, Eint $1 }
| FLOAT { fst $1, Efloat $1 }
| STRING { fst $1, Estring $1 }
| CHAR { fst $1, Echar $1 }
| LCB field_l RCB dot_id { simpl_arg (Pos.btw $1 $3, Erecord $2) $4 }
| LCB simpl_expr WITH field_l RCB dot_id { 
  simpl_arg (Pos.btw $1 $5, Ewith ($2, $4)) $6 
}
| LP expr RP dot_id { simpl_arg (Pos.btw $1 $3, snd $2) $4 }
| BEGIN expr END dot_id { simpl_arg $2 $4 }
| LB expr_list RB { make_elist (Pos.btw $1 $3) $2 }

expr_list:
| { [] }
| simpl_expr { [$1] }
| simpl_expr SC expr_list { $1 :: $3 }


dot_cstr:
| { `Null }
| DOT CSTR { `Cstr $2 }
| DOT ID { `Id $2 }

dot_id:
| { [] }
| DOT ID dot_id { `Id $2 :: $3 }
| DOT CSTR DOT ID dot_id { `Path($2, $4) :: $5 }

simpl_expr_l:
| { [] }
| simpl_expr simpl_expr_l { $1 :: $2 }

expr:
| IF expr THEN expr ELSE expr %prec if_ { 
    Pos.btw $1 (fst $6), Eif ($2, $4, $6) 
  }

| LET pat EQ expr IN expr %prec let_ { 
  Pos.btw $1 (fst $6), Elet ($2, $4, $6) 
}

| MATCH expr WITH pat_action_l %prec match_ { 
  let l = List.rev $4 in
  Pos.btw $1 (pat_end l), Ematch ($2, l) 
  }

| FUN simpl_pat_l ARROW expr { Pos.btw $1 (fst $4), Efun ($2, $4) }
| MINUS expr %prec unary_minus { Pos.btw $1 (fst $2), Euop (Euminus, $2) }
| expr EQ expr { btw $1 $3, Ebinop (Eeq, $1, $3) }
| expr LT expr { btw $1 $3, Ebinop (Elt, $1, $3) }
| expr LTE expr { btw $1 $3, Ebinop (Elte, $1, $3) }
| expr GT expr { btw $1 $3, Ebinop (Egt, $1, $3) }
| expr GTE expr { btw $1 $3, Ebinop (Egte, $1, $3) }
| expr PLUS expr { btw $1 $3, Ebinop (Eplus, $1, $3) }
| expr MINUS expr { btw $1 $3, Ebinop (Eminus, $1, $3) }
| expr STAR expr { btw $1 $3, Ebinop (Estar, $1, $3) }
| expr SC expr { btw $1 $3, Eseq ($1, $3) }
| expr COMMA expr { btw $1 $3, Etuple [$1;$3] }
| expr COLONCOLON expr { 
  let pos = btw $1 $3 in
  let cons = Eecstr (($2, "List"), ($2, "Cons")) in
  pos, Eapply (($2, cons), [$1 ; $3])
}
| ID COLEQ expr SC expr { btw $1 $5, Elet ((fst $1, Pid $1), $3, $5) }
| simpl_expr simpl_expr_l { 
  match $2 with 
  | [] -> $1 
  | _ -> Pos.btw (fst $1) (last $2), Eapply ($1, $2)
}

