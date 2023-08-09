%{
  open Syntax
%}
%token LPAREN "(" RPAREN ")" LBRACK "[" RBRACK "]" LBRACE "{" RBRACE "}"
%token COLON ":" COMMA "," SEMI ";" SEMISEMI ";;" CONS "::" QUOTE "'" DOT "."
%token BEGIN END TUNIT TBOOL TINT TFLOAT TSTRING TCHAR
%token <string> LID UID
%token WILD "_" AS
%token <int> INT
%token <char> CHAR
%token <string> STRING
%token <bool> BOOL
%token <float> FLOAT
%token TYPE ARROW "->" OF
%token MATCH WITH FUNCTION
%token LET REC AND IN
%token FUN BAR "|" BARBAR "||"
%token IF THEN ELSE WHEN
%token REF DEREF "!" ASSIGN ":="
%token AT "@"
%token EQ "=" NQ "<>" LT "<" GT ">" LE "<=" GE ">=" EQIMM "==" NQIMM "!="
%token PLUS "+" PLUSDOT "+."
%token STAR "*" STARDOT "*." STARSTAR "**"
%token MINUS "-" MINUSDOT "-."
%token DIV "/" DIVDOT "/."
%token LSL LSR ASR
%token MOD
%token AMPERAMPER "&&" NOT
%token LAND LOR LXOR LNOT
%token EOF

%right prec_def
%nonassoc IN
%right "->"
%right ";"
%right prec_list
%nonassoc ELSE

%right ":="
%left AS
%left "|"
%left "||"
%left "&&"
%left "=" "<>" "<" ">" "<=" ">=" "==" "!="
%right "@"
%right "::"
%left  "+" "+." "-" "-."
%left  "*" "*." "/" "/." MOD LAND LOR LXOR
%right LSL LSR ASR "**"
%right prec_uminus
%right REF "!" LNOT NOT

%start<def list> top
%start<def list> def

%%

top             : list(def) EOF                     { List.flatten $1 }

def             : ";;"                              { [] }
                | def_ %prec prec_def               { [$1] }

def_            : TYPE separated_nonempty_list(AND, ty_def)
                                                    { Deftype $2 }
                | LET separated_nonempty_list(AND, let_def)
                                                    { Deflet $2 }
                | LET REC separated_nonempty_list(AND, let_rec_def)
                                                    { Defletrec $3 }
                | expr                              { Defexpr $1 }
expr            : simple_expr                       { $1 }
                | simple_expr_ simple_expr+         { Eapply($1,$2) }
                | MATCH expr WITH function_case     { Eapply(Efunction($4),[$2]) }
                | FUNCTION function_case            { Efunction($2) }
                | FUN fun_case                      { Efunction([$2]) }
                | LET separated_nonempty_list(AND, let_def) IN expr
                                                    { Elet($2,$4) }
                | LET REC separated_nonempty_list(AND, let_rec_def) IN expr
                                                    { Eletrec($3,$5) }
                | expr ";" expr                     { Esequence($1,$3) }
                | IF expr THEN expr ELSE expr       { Econdition($2,$4,$6) }
                | expr binop expr                   { Eapply(Evar $2,$1::$3::[]) }
                | expr ":=" expr                    { Eassign($1,$3) }
                | expr "::" expr                    { Econs($1,$3) }
                | "-" expr %prec prec_uminus        { Eapply(Evar("~-"),$2::[]) }
                | "-." expr %prec prec_uminus       { Eapply(Evar("~-."),$2::[]) }
                | LNOT expr                         { Eapply(Evar("lnot"),$2::[]) }
                | NOT expr                          { Eapply(Evar("not"),$2::[]) }
                | REF expr                          { Eref($2) }
                | "!" expr                          { Ederef($2) }
                | UID simple_expr                   { Econstruct($1,$2) }

simple_expr     : UID                               { Econstruct($1,Etag) }
                | simple_expr_                      { $1 }

simple_expr_    :
                | ident                             { Evar $1 }
                | const_expr                        { Econstant $1 }
                | "[" "]"                           { Enil }
                | "[" expr_semi_list "]"            { List.fold_left (fun cdr car -> Econs(car,cdr)) Enil $2 }
                | "{" expr_label_list "}"           { Erecord $2 }
                | "(" ")"                           { Eunit }
                | "(" expr "," separated_nonempty_list(",",expr) ")"
                                                    { Etuple($2::$4) }
                | "(" expr ":" ty ")"               { Econstraint($2,$4) }
                | "(" expr ")"                      { $2 }
                | BEGIN expr END                    { $2 }
                | simple_expr "." LID               { Erecord_access($1,$3) }

expr_semi_list  : expr_semi_list ";" expr %prec prec_list
                                                    { $3::$1 }
                | expr %prec prec_list              { [$1] }

expr_label_list : expr_label_list ";" field "=" expr{ ($3,$5)::$1 }
                | field "=" expr                    { ($1,$3)::[] }
  

const_expr      : INT                               { (Cint($1)) }
                | CHAR                              { (Cchar($1)) }
                | STRING                            { (Cstring($1)) }
                | BOOL                              { (Cbool($1)) }
                | FLOAT                             { (Cfloat($1)) }

fun_case        : nonempty_list(simple_pat) "->" expr
                                                    { (Pparams $1,$3) }

function_case   : "|" pat "->" expr                 { [($2,$4)] }
                | "|" pat WHEN expr "->" expr       { [($2,Ewhen($4,$6))] }
                | "|" pat "->" expr function_case   { ($2,$4)::$5 }
                | "|" pat WHEN expr "->" expr function_case
                                                    { ($2,Ewhen($4,$6))::$7 }


let_def         : pat "=" expr                      { ($1,$3) }
                | ident nonempty_list(simple_pat) "=" expr
                                                    { (Pvar $1,Efunction((Pparams $2,$4)::[])) }
                | ident nonempty_list(simple_pat) ":" ty "=" expr
                                                    { (Pvar $1,Efunction((Pparams $2,Econstraint($6,$4))::[])) }

let_rec_def     : ident "=" expr                    { (Pvar $1,Efix(Pvar $1,$3)) }
                | ident nonempty_list(simple_pat) "=" expr
                                                    { (Pvar $1,Efix(Pvar $1,Efunction((Pparams $2,$4)::[]))) }
                | ident nonempty_list(simple_pat) ":" ty "=" expr
                                                    { (Pvar $1,Efix (Pvar $1,Efunction((Pparams $2,Econstraint($6,$4))::[]))) }

pat             : simple_pat                        { $1 }
                | pat AS lid                        { Palias($1,$3) }
                | pat "::" pat                      { Pcons($1,$3) }
                | UID simple_pat                    { Pconstruct($1,$2) }
                | REF simple_pat                    { Pref $2 }

comma_pat       :  pat "," separated_nonempty_list(",", pat)
                                                    { $1::$3 }

pat_semi_list   : pat ";" pat_semi_list             { Pcons($1,$3) }
                | pat                               { Pcons($1,Pnil) }

simple_pat      : ident                             { Pvar $1 }
                | UID                               { Pconstruct($1,Ptag) }
                | "_"                               { Pwild }
                | const_expr                        { Pconstant $1 }
                | "{" separated_nonempty_list(";", separated_pair(field, "=", pat)) "}"
                                                    { Precord $2 }
                | "[" pat_semi_list "]"             { $2 }
                | "[" "]"                           { Pnil }
                | "(" ")"                           { Punit }
                | "(" pat ":" ty ")"                { Pconstraint ($2,$4) }
                | "(" pat ")"                       { $2 }
                | "(" comma_pat ")"                 { Ptuple $2 }


lid             : LID                               { $1 }
field           : lid                               { $1 }
tyname          : lid                               { $1 }
ident           : lid                               { $1 }
                | "(" binop ")"                     { $2 }

%inline binop   : "||"                              { "||" }
                | "&&"                              { "&&" }
                | "="                               { "=" }
                | "<>"                              { "<>" }
                | "<"                               { "<" }
                | ">"                               { ">" }
                | "<="                              { "<=" }
                | ">="                              { ">=" }
                | "=="                              { "==" }
                | "!="                              { "!=" }
                | "@"                               { "@" }
                | "+"                               { "+" }
                | "-"                               { "-" }
                | "*"                               { "*" }
                | "/"                               { "/" }
                | "+."                              { "+." }
                | "-."                              { "-." }
                | "*."                              { "*." }
                | "/."                              { "/." }
                | "**"                              { "**" }
                | MOD                               { "mod" }
                | LAND                              { "land" }
                | LOR                               { "lor" }
                | LXOR                              { "lxor" }
                | LSL                               { "lsl" }
                | LSR                               { "lsr" }
                | ASR                               { "asr" }


param           : "'" lid                           { Tvar (ref (Unbound {id=Idstr $2; level= generic})) }

params          :                                   { [] }
                | param                             { $1::[] }
                | "(" separated_nonempty_list(",", param) ")"
                                                    { $2 }

ty_def          : params tyname "=" "{" separated_nonempty_list(";", separated_pair(field, ":", ty)) "}"
                                                    { Drecord($2,$1,$5) }
                | params tyname "=" nonempty_list("|" sum_case { $2 })
                                                    { Dvariant($2,$1,$4) }
                | params tyname "=" ty              { Dabbrev($2,$1,$4) }

ty              : simple_ty                         { $1 }
                | ty "->" ty                        { Tarrow($1,$3) }
                | tuple_ty                          { Ttuple $1 }

tuple_ty        : simple_ty "*" separated_nonempty_list("*", simple_ty)
                                                    { $1::$3 }

simple_ty       : "(" ty "," separated_nonempty_list(",", ty) ")" tyname
                                                    { Tconstr($6,$2::$4) }
                | simple_ty tyname                  { Tconstr($2,$1::[]) }
                | TUNIT                             { Tunit }
                | TBOOL                             { Tbool }
                | TINT                              { Tint }
                | TFLOAT                            { Tfloat }
                | TCHAR                             { Tchar }
                | TSTRING                           { Tstring }
                | simple_ty REF                     { Tref $1 }
                | tyname                            { Tconstr($1,[]) }
                | param                             { $1 }
                | "(" ty ")"                        { $2 }

sum_case        : UID                               { ($1, Ttag) }
                | UID OF ty                         { ($1, $3) }
