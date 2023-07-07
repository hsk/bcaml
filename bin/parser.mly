%{

%}

%token LPAREN RPAREN LBRACK RBRACK LBRACE RBRACE
%token COLON COMMA SEMI SEMISEMI EQUAL CONS QUOTE
%token BEGIN END
%token <string> LID UID
%token UNDERSCORE AS
%token <int> INT
%token <string> STRING
%token <bool> BOOL
%token <float> FLOAT
%token TYPE ARROW OF
%token MATCH WITH FUNCTION
%token LET REC AND IN
%token FUN BAR BARBAR
%token IF THEN ELSE
%token REF DEREF
%token AT
%token PLUS STAR MINUS MINUSDOT
%token LSL LSR ASR
%token MOD OR
%token AMPER AMPERAMPER
%token LAND LOR LXOR
%token EOF

%nonassoc IN
%right ARROW
%right SEMI
%right prec_list
%nonassoc ELSE
%left BAR
%left OR BARBAR
%left AMPER AMPERAMPER
%left  EQUAL
%right AT
%right CONS
%left  PLUS MINUS MINUSDOT REF DEREF
%left  STAR MOD LAND LOR LXOR
%right LSL LSR ASR

%start<()> top

%%


top:
| def EOF
| expr EOF
| def SEMISEMI top
| expr SEMISEMI top
     { }

def: 
| TYPE separated_nonempty_list(AND, ty_def)
| LET separated_nonempty_list(AND, let_def)
| LET REC separated_nonempty_list(AND, let_rec_def)
    {}

expr:
| simple_expr
| simple_expr simple_expr+
| MATCH expr WITH nonempty_list(BAR match_case {})
| FUNCTION nonempty_list(BAR function_case {})
| FUN fun_case
| LET separated_nonempty_list(AND, let_def) IN expr
| LET REC separated_nonempty_list(AND, let_rec_def) IN expr
| expr SEMI expr
| IF expr THEN expr ELSE expr
| expr binop expr
| expr CONS expr
| MINUS expr
| MINUSDOT expr
| REF expr
| DEREF expr
    {  }

simple_expr:
| ident
| UID
| const_expr
| LBRACK expr_semi_list RBRACK
| LBRACE expr_label_list RBRACE
| LPAREN RPAREN
| LPAREN expr COMMA separated_nonempty_list(COMMA,expr) RPAREN
| LPAREN expr COLON ty RPAREN
| LPAREN expr RPAREN
| BEGIN expr END
      {}

expr_semi_list:
| 
| expr_semi_list SEMI expr %prec prec_list 
| expr %prec prec_list
  {}

expr_label_list:
| 
| expr_label_list SEMI field EQUAL expr %prec prec_list
| field EQUAL expr %prec prec_list
  {}
  

const_expr:
| INT
| STRING
| BOOL
| FLOAT
    {}

function_case:
| pat ARROW expr
    {}

match_case:
| pat ARROW expr
    {}

fun_case:
| nonempty_list(simple_pat) ARROW expr
  {}

let_def:
| pat EQUAL expr
| pat COLON ty EQUAL expr
| ident nonempty_list(simple_pat) EQUAL expr
    {}

let_rec_def:
| ident nonempty_list(simple_pat) EQUAL expr
    {  }



pat: 
| comma_pat
    {}
| pat AS lid
    {}

comma_pat: 
| separated_nonempty_list(COMMA, cons_pat)
    {}

cons_pat: 
| variant_pat
    {}
| variant_pat CONS cons_pat
    {}

variant_pat: 
| UID simple_pat
| simple_pat
    {  }

simple_pat: 
| ident
| UID
| UNDERSCORE
| const_expr
| LBRACE separated_nonempty_list(SEMI, separated_pair(field, EQUAL, pat)) RBRACE
| LBRACK separated_list(SEMI, pat) RBRACK
| LPAREN RPAREN
| LPAREN pat COLON ty RPAREN
| LPAREN pat RPAREN
    { }


lid:
| LID
    { }

field:
| lid
    { }

tyname:
| lid
    { }

ident:
| lid
| LPAREN binop RPAREN
    {      }

%inline binop:
| OR
    { "or" }
| BARBAR
    { "||" }
| AMPER
    { "&" }
| AMPERAMPER
    { "&&" }
| AT
    { "@" }
| PLUS
    { "+" }
| MINUSDOT
    { "-." }
| MINUS
    { "-" }
| EQUAL
    { "=" }
| STAR
    { "*" }
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
   {}


params:
|
| param
| LPAREN separated_nonempty_list(COMMA, param) RPAREN
    {}

ty_def:
| params tyname EQUAL defined_ty
    {  }

defined_ty:
| LBRACE separated_nonempty_list(SEMI, separated_pair(field, COLON, ty)) RBRACE
| nonempty_list(BAR sum_case {})
| ty
    {}

ty: 
| simple_ty
| ty ARROW ty
| prod_ty
    { }

prod_ty:
| simple_ty STAR separated_nonempty_list(STAR, simple_ty)
    { }

simple_ty: 
| LPAREN ty COMMA separated_nonempty_list(COMMA, ty) RPAREN tyname
| simple_ty tyname
| tyname
| param
| LPAREN ty RPAREN
    { }

sum_case:
| UID
| UID OF ty
    {  }


%%
