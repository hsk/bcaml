%{

  open Syntax

  let curr_id = ref 0

  let gen_id () =
    let ret = !curr_id in
    curr_id := !curr_id + 1;
    ret

%}

%token LPAREN RPAREN LBRACK RBRACK LBRACE RBRACE
%token COLON COMMA SEMI SEMISEMI CONS QUOTE
%token BEGIN END
%token <string> LID UID
%token WILD AS
%token <int> INT
%token <string> STRING
%token <bool> BOOL
%token <float> FLOAT
%token TYPE ARROW OF
%token MATCH WITH FUNCTION
%token LET REC AND IN
%token FUN BAR BARBAR
%token IF THEN ELSE WHEN
%token REF DEREF ASSIGN
%token AT
%token EQ NQ LT GT LE GE
%token PLUS PLUSDOT
%token STAR STARDOT STARSTAR
%token MINUS MINUSDOT
%token DIV DIVDOT
%token LSL LSR ASR
%token MOD
%token AMPERAMPER
%token LAND LOR LXOR
%token EOF

%nonassoc IN
%right ARROW
%right SEMI
%right prec_list
%nonassoc ELSE
%right ASSIGN
%left AS
%left BAR
%left BARBAR
%left AMPERAMPER
%left  EQ NQ LT GT LE GE
%right AT
%right CONS
%left  PLUS PLUSDOT MINUS MINUSDOT REF DEREF
%left  STAR STARDOT DIV DIVDOT MOD LAND LOR LXOR
%right LSL LSR ASR STARSTAR

%start<def list> top

%%


top:
| def EOF
    { [(gen_id (), $1)] }
| def SEMISEMI top
    { (gen_id (), $1)::$3 }

def: 
| TYPE separated_nonempty_list(AND, ty_def)
    { Deftype $2 }
| LET separated_nonempty_list(AND, let_def)
    { Deflet $2 }
| LET REC separated_nonempty_list(AND, let_rec_def)
    { Defletrec $3 }
| expr
    { Defexpr $1 }

expr:
| simple_expr { $1 }
| simple_expr simple_expr+ { Eapply($1,$2) }
| MATCH expr WITH nonempty_list(BAR function_case { $2 })
    { Eapply(Efunction($4),[$2]) }
| FUNCTION nonempty_list(BAR function_case { $2 })
    { Efunction($2) }
| FUN function_case
    { Efunction([$2]) }
| LET separated_nonempty_list(AND, let_def) IN expr
    { Elet($2,$4) }
| LET REC separated_nonempty_list(AND, let_rec_def) IN expr
    { Eletrec($3,$5) }
| expr SEMI expr  { Esequence($1,$3) }
| IF expr THEN expr ELSE expr
    { Econdition($2,$4,$6) }
| expr binop expr  { Eapply(Evar $2,$1::$3::[]) }
| expr CONS expr { Econstruct("::",Etuple($1::$3::[])) }
| MINUS expr { Eapply(Evar("-"),$2::[]) }
| MINUSDOT expr { Eapply(Evar("-."),$2::[]) }
| REF expr { Econstruct("ref",Etuple($2::[])) }
| DEREF expr { Econstruct("!",Etuple($2::[])) }

simple_expr:
| ident { Evar $1 }
| UID { Econstruct_ $1 }
| const_expr { Econstant $1 }
| LBRACK RBRACK { Econstruct_ "[]" }
| LBRACK expr_semi_list RBRACK { $2 }
| LBRACE expr_label_list RBRACE { Erecord $2 }
| LPAREN RPAREN { Econstruct_ "()" }
| LPAREN expr COMMA separated_nonempty_list(COMMA,expr) RPAREN
    { Etuple($2::$4) }
| LPAREN expr COLON ty RPAREN { Econstraint($2,$4) }
| LPAREN expr RPAREN { $2 }
| BEGIN expr END { $2 }

expr_semi_list:
| expr_semi_list SEMI expr %prec prec_list 
  { Econstruct("::",Etuple($1::$3::[])) }
| expr %prec prec_list
  { Econstruct("::",Etuple($1::(Econstruct_ "[]")::[])) }

expr_label_list:
| expr_label_list SEMI field EQ expr %prec prec_list
  { ($3,$5)::$1 }
| field EQ expr %prec prec_list
  { ($1,$3)::[] }
  

const_expr:
| INT { (Cint($1)) }
| STRING { (Cstring($1)) }
| BOOL { (Cbool($1)) }
| FLOAT { (Cfloat($1)) }

function_case:
| nonempty_list(simple_pat) ARROW expr
    { (Pparams $1,$3) }
| nonempty_list(simple_pat) WHEN expr ARROW expr
    { (Pparams $1,Ewhen($3,$5)) }

let_def:
| pat EQ expr
    { ($1,$3) }
| ident nonempty_list(simple_pat) EQ expr
    { (Pvar $1,Efunction((Pparams $2,$4)::[])) }
| ident nonempty_list(simple_pat) COLON ty EQ expr
    { (Pvar $1,Efunction((Pparams $2,Econstraint($6,$4))::[])) }

let_rec_def:
| ident nonempty_list(simple_pat) EQ expr
    { (Pvar $1,Efunction((Pparams $2,$4)::[])) }
| ident nonempty_list(simple_pat) COLON ty EQ expr
    { (Pvar $1,Efunction((Pparams $2,Econstraint($6,$4))::[])) }

pat: 
| simple_pat
    { $1 }
| pat AS lid
    { Palias($1,$3) }
| pat CONS pat
    { Pconstruct("::",Ptuple($1::$3::[])) }
| UID simple_pat
    { Pconstruct($1,$2) }


comma_pat: 
| pat COMMA separated_nonempty_list(COMMA, pat)
    { $1::$3 }

pat_semi_list:
| pat_semi_list SEMI pat 
  { Pconstruct("::",Ptuple($1::$3::[])) }
| pat
  { Pconstruct("::",Ptuple($1::(Pconstruct_ "[]")::[])) }


simple_pat: 
| ident
    { Pvar $1 }
| UID
    { Pconstruct_ $1 }
| WILD
    { Pwild }
| const_expr
    { Pconstant $1 }
| LBRACE separated_nonempty_list(SEMI, separated_pair(field, EQ, pat)) RBRACE
    { Precord $2 }
| LBRACK pat_semi_list RBRACK
    { $2 }
| LBRACK RBRACK
    { Pconstruct_ "[]" }
| LPAREN RPAREN
    { Pconstruct_ "()" }
| LPAREN pat COLON ty RPAREN
    { Pconstraint ($2,$4) }
| LPAREN pat RPAREN
    { $2 }
| LPAREN comma_pat RPAREN
    { Ptuple $2 }


lid:
| LID
    { $1 }

field:
| lid
    { $1 }

tyname:
| lid
    { $1 }

ident:
| lid { $1 }
| LPAREN binop RPAREN
    { $2 }

%inline binop:
| BARBAR
    { "||" }
| AMPERAMPER
    { "&&" }
| EQ
    { "=" }
| NQ
    { "<>" }
| LT
    { "<" }
| GT
    { ">" }
| LE
    { "<=" }
| GE
    { ">=" }
| ASSIGN
    { ":=" }
| AT
    { "@" }
| PLUS
    { "+" }
| MINUS
    { "-" }
| STAR
    { "*" }
| DIV
    { "/" }
| PLUSDOT
    { "+." }
| MINUSDOT
    { "-." }
| STARDOT
    { "*." }
| DIVDOT
    { "/." }
| STARSTAR
    { "**" }
| MOD
    { "mod" }
| LAND
    { "land" }
| LOR
    { "lor" }
| LXOR
    { "lxor" }
| LSL
    { "lsl" }
| LSR
    { "lsr" }
| ASR
    { "asr" }


param:
| QUOTE lid
   { {id=Idstr $2; level= 0} }


params:
|
    { [] }
| param
    { $1::[] }
| LPAREN separated_nonempty_list(COMMA, param) RPAREN
    { $2 }

ty_def:
| params tyname EQ LBRACE separated_nonempty_list(SEMI, separated_pair(field, COLON, ty)) RBRACE
    { Drecord($2,$1,$5) }
| params tyname EQ nonempty_list(BAR sum_case { $2 })
    { Dvariant($2,$1,$4) }
| params tyname EQ ty
    { Dabbrev($2,$1,$4) }

ty: 
| simple_ty
    { $1 }
| ty ARROW ty
    { Tarrow($1,$3) }
| tuple_ty
    { Ttuple $1 }

tuple_ty:
| simple_ty STAR separated_nonempty_list(STAR, simple_ty)
    { $1::$3 }

simple_ty: 
| LPAREN ty COMMA separated_nonempty_list(COMMA, ty) RPAREN tyname
    { Tconstr($6,$2::$4) }
| simple_ty tyname
    { Tconstr($2,$1::[]) }
| tyname
    { Tconstr($1,[]) }
| param
    { Tvar (ref (Unbound $1)) }
| LPAREN ty RPAREN
    { $2 }

sum_case:
| UID
    { Gconstruct_ $1 }
| UID OF ty
    { Gconstruct($1,$3) }


%%
