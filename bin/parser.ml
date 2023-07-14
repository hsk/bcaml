
type token = 
  | WITH
  | WHEN
  | UNDERSCORE
  | UID of (
# 10 "parser.mly"
       (string)
# 10 "parser.ml"
)
  | TYPE
  | THEN
  | STRING of (
# 13 "parser.mly"
       (string)
# 17 "parser.ml"
)
  | STAR
  | SEMISEMI
  | SEMI
  | RPAREN
  | REF
  | REC
  | RBRACK
  | RBRACE
  | QUOTE
  | PLUS
  | OR
  | OF
  | MOD
  | MINUSDOT
  | MINUS
  | MATCH
  | LXOR
  | LSR
  | LSL
  | LPAREN
  | LOR
  | LID of (
# 10 "parser.mly"
       (string)
# 43 "parser.ml"
)
  | LET
  | LBRACK
  | LBRACE
  | LAND
  | INT of (
# 12 "parser.mly"
       (int)
# 52 "parser.ml"
)
  | IN
  | IF
  | FUNCTION
  | FUN
  | FLOAT of (
# 15 "parser.mly"
       (float)
# 61 "parser.ml"
)
  | EQUAL
  | EOF
  | END
  | ELSE
  | DEREF
  | CONS
  | COMMA
  | COLON
  | BOOL of (
# 14 "parser.mly"
       (bool)
# 74 "parser.ml"
)
  | BEGIN
  | BARBAR
  | BAR
  | AT
  | ASR
  | AS
  | ARROW
  | AND
  | AMPERAMPER
  | AMPER

# 1 "parser.mly"
  

open Syntax


# 93 "parser.ml"

let menhir_begin_marker =
  0

and (xv_tyname, xv_ty_def, xv_ty, xv_tuple_ty, xv_top, xv_sum_case, xv_simple_ty, xv_simple_pat, xv_simple_expr, xv_separated_pair_field_EQUAL_pat_, xv_separated_pair_field_COLON_ty_, xv_separated_nonempty_list_STAR_simple_ty_, xv_separated_nonempty_list_SEMI_separated_pair_field_EQUAL_pat__, xv_separated_nonempty_list_SEMI_separated_pair_field_COLON_ty__, xv_separated_nonempty_list_COMMA_ty_, xv_separated_nonempty_list_COMMA_pat_, xv_separated_nonempty_list_COMMA_param_, xv_separated_nonempty_list_COMMA_expr_, xv_separated_nonempty_list_AND_ty_def_, xv_separated_nonempty_list_AND_let_rec_def_, xv_separated_nonempty_list_AND_let_def_, xv_pat_semi_list, xv_pat, xv_params, xv_param, xv_nonempty_list_simple_pat_, xv_nonempty_list_simple_expr_, xv_nonempty_list___anonymous_2_, xv_nonempty_list___anonymous_1_, xv_nonempty_list___anonymous_0_, xv_lid, xv_let_rec_def, xv_let_def, xv_ident, xv_function_case, xv_field, xv_expr_semi_list, xv_expr_label_list, xv_expr, xv_def, xv_const_expr, xv_comma_pat, xv_binop, xv___anonymous_2, xv___anonymous_1, xv___anonymous_0) =
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 171 "<standard.mly>"
              y
# 102 "parser.ml"
   : 'tv_pat) (_startpos_y_ : Lexing.position) (_endpos_y_ : Lexing.position) (_startofs_y_ : int) (_endofs_y_ : int) (_loc_y_ : Lexing.position * Lexing.position) (
# 171 "<standard.mly>"
        _2
# 106 "parser.ml"
   : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_loc__2_ : Lexing.position * Lexing.position) (
# 171 "<standard.mly>"
  x
# 110 "parser.ml"
   : 'tv_field) (_startpos_x_ : Lexing.position) (_endpos_x_ : Lexing.position) (_startofs_x_ : int) (_endofs_x_ : int) (_loc_x_ : Lexing.position * Lexing.position) ->
    (
# 172 "<standard.mly>"
    ( (x, y) )
# 115 "parser.ml"
     : 'tv_separated_pair_field_EQUAL_pat_) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 171 "<standard.mly>"
              y
# 120 "parser.ml"
   : 'tv_ty) (_startpos_y_ : Lexing.position) (_endpos_y_ : Lexing.position) (_startofs_y_ : int) (_endofs_y_ : int) (_loc_y_ : Lexing.position * Lexing.position) (
# 171 "<standard.mly>"
        _2
# 124 "parser.ml"
   : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_loc__2_ : Lexing.position * Lexing.position) (
# 171 "<standard.mly>"
  x
# 128 "parser.ml"
   : 'tv_field) (_startpos_x_ : Lexing.position) (_endpos_x_ : Lexing.position) (_startofs_x_ : int) (_endofs_x_ : int) (_loc_x_ : Lexing.position * Lexing.position) ->
    (
# 172 "<standard.mly>"
    ( (x, y) )
# 133 "parser.ml"
     : 'tv_separated_pair_field_COLON_ty_) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 239 "<standard.mly>"
                    xs
# 138 "parser.ml"
   : 'tv_separated_nonempty_list_STAR_simple_ty_) (_startpos_xs_ : Lexing.position) (_endpos_xs_ : Lexing.position) (_startofs_xs_ : int) (_endofs_xs_ : int) (_loc_xs_ : Lexing.position * Lexing.position) (
# 239 "<standard.mly>"
        _2
# 142 "parser.ml"
   : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_loc__2_ : Lexing.position * Lexing.position) (
# 239 "<standard.mly>"
  x
# 146 "parser.ml"
   : 'tv_simple_ty) (_startpos_x_ : Lexing.position) (_endpos_x_ : Lexing.position) (_startofs_x_ : int) (_endofs_x_ : int) (_loc_x_ : Lexing.position * Lexing.position) ->
    (
# 240 "<standard.mly>"
    ( x :: xs )
# 151 "parser.ml"
     : 'tv_separated_nonempty_list_STAR_simple_ty_) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 237 "<standard.mly>"
  x
# 156 "parser.ml"
   : 'tv_simple_ty) (_startpos_x_ : Lexing.position) (_endpos_x_ : Lexing.position) (_startofs_x_ : int) (_endofs_x_ : int) (_loc_x_ : Lexing.position * Lexing.position) ->
    (
# 238 "<standard.mly>"
    ( [ x ] )
# 161 "parser.ml"
     : 'tv_separated_nonempty_list_STAR_simple_ty_) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 239 "<standard.mly>"
                    xs
# 166 "parser.ml"
   : 'tv_separated_nonempty_list_SEMI_separated_pair_field_EQUAL_pat__) (_startpos_xs_ : Lexing.position) (_endpos_xs_ : Lexing.position) (_startofs_xs_ : int) (_endofs_xs_ : int) (_loc_xs_ : Lexing.position * Lexing.position) (
# 239 "<standard.mly>"
        _2
# 170 "parser.ml"
   : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_loc__2_ : Lexing.position * Lexing.position) (
# 239 "<standard.mly>"
  x
# 174 "parser.ml"
   : 'tv_separated_pair_field_EQUAL_pat_) (_startpos_x_ : Lexing.position) (_endpos_x_ : Lexing.position) (_startofs_x_ : int) (_endofs_x_ : int) (_loc_x_ : Lexing.position * Lexing.position) ->
    (
# 240 "<standard.mly>"
    ( x :: xs )
# 179 "parser.ml"
     : 'tv_separated_nonempty_list_SEMI_separated_pair_field_EQUAL_pat__) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 237 "<standard.mly>"
  x
# 184 "parser.ml"
   : 'tv_separated_pair_field_EQUAL_pat_) (_startpos_x_ : Lexing.position) (_endpos_x_ : Lexing.position) (_startofs_x_ : int) (_endofs_x_ : int) (_loc_x_ : Lexing.position * Lexing.position) ->
    (
# 238 "<standard.mly>"
    ( [ x ] )
# 189 "parser.ml"
     : 'tv_separated_nonempty_list_SEMI_separated_pair_field_EQUAL_pat__) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 239 "<standard.mly>"
                    xs
# 194 "parser.ml"
   : 'tv_separated_nonempty_list_SEMI_separated_pair_field_COLON_ty__) (_startpos_xs_ : Lexing.position) (_endpos_xs_ : Lexing.position) (_startofs_xs_ : int) (_endofs_xs_ : int) (_loc_xs_ : Lexing.position * Lexing.position) (
# 239 "<standard.mly>"
        _2
# 198 "parser.ml"
   : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_loc__2_ : Lexing.position * Lexing.position) (
# 239 "<standard.mly>"
  x
# 202 "parser.ml"
   : 'tv_separated_pair_field_COLON_ty_) (_startpos_x_ : Lexing.position) (_endpos_x_ : Lexing.position) (_startofs_x_ : int) (_endofs_x_ : int) (_loc_x_ : Lexing.position * Lexing.position) ->
    (
# 240 "<standard.mly>"
    ( x :: xs )
# 207 "parser.ml"
     : 'tv_separated_nonempty_list_SEMI_separated_pair_field_COLON_ty__) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 237 "<standard.mly>"
  x
# 212 "parser.ml"
   : 'tv_separated_pair_field_COLON_ty_) (_startpos_x_ : Lexing.position) (_endpos_x_ : Lexing.position) (_startofs_x_ : int) (_endofs_x_ : int) (_loc_x_ : Lexing.position * Lexing.position) ->
    (
# 238 "<standard.mly>"
    ( [ x ] )
# 217 "parser.ml"
     : 'tv_separated_nonempty_list_SEMI_separated_pair_field_COLON_ty__) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 239 "<standard.mly>"
                    xs
# 222 "parser.ml"
   : 'tv_separated_nonempty_list_COMMA_ty_) (_startpos_xs_ : Lexing.position) (_endpos_xs_ : Lexing.position) (_startofs_xs_ : int) (_endofs_xs_ : int) (_loc_xs_ : Lexing.position * Lexing.position) (
# 239 "<standard.mly>"
        _2
# 226 "parser.ml"
   : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_loc__2_ : Lexing.position * Lexing.position) (
# 239 "<standard.mly>"
  x
# 230 "parser.ml"
   : 'tv_ty) (_startpos_x_ : Lexing.position) (_endpos_x_ : Lexing.position) (_startofs_x_ : int) (_endofs_x_ : int) (_loc_x_ : Lexing.position * Lexing.position) ->
    (
# 240 "<standard.mly>"
    ( x :: xs )
# 235 "parser.ml"
     : 'tv_separated_nonempty_list_COMMA_ty_) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 237 "<standard.mly>"
  x
# 240 "parser.ml"
   : 'tv_ty) (_startpos_x_ : Lexing.position) (_endpos_x_ : Lexing.position) (_startofs_x_ : int) (_endofs_x_ : int) (_loc_x_ : Lexing.position * Lexing.position) ->
    (
# 238 "<standard.mly>"
    ( [ x ] )
# 245 "parser.ml"
     : 'tv_separated_nonempty_list_COMMA_ty_) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 239 "<standard.mly>"
                    xs
# 250 "parser.ml"
   : 'tv_separated_nonempty_list_COMMA_pat_) (_startpos_xs_ : Lexing.position) (_endpos_xs_ : Lexing.position) (_startofs_xs_ : int) (_endofs_xs_ : int) (_loc_xs_ : Lexing.position * Lexing.position) (
# 239 "<standard.mly>"
        _2
# 254 "parser.ml"
   : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_loc__2_ : Lexing.position * Lexing.position) (
# 239 "<standard.mly>"
  x
# 258 "parser.ml"
   : 'tv_pat) (_startpos_x_ : Lexing.position) (_endpos_x_ : Lexing.position) (_startofs_x_ : int) (_endofs_x_ : int) (_loc_x_ : Lexing.position * Lexing.position) ->
    (
# 240 "<standard.mly>"
    ( x :: xs )
# 263 "parser.ml"
     : 'tv_separated_nonempty_list_COMMA_pat_) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 237 "<standard.mly>"
  x
# 268 "parser.ml"
   : 'tv_pat) (_startpos_x_ : Lexing.position) (_endpos_x_ : Lexing.position) (_startofs_x_ : int) (_endofs_x_ : int) (_loc_x_ : Lexing.position * Lexing.position) ->
    (
# 238 "<standard.mly>"
    ( [ x ] )
# 273 "parser.ml"
     : 'tv_separated_nonempty_list_COMMA_pat_) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 239 "<standard.mly>"
                    xs
# 278 "parser.ml"
   : 'tv_separated_nonempty_list_COMMA_param_) (_startpos_xs_ : Lexing.position) (_endpos_xs_ : Lexing.position) (_startofs_xs_ : int) (_endofs_xs_ : int) (_loc_xs_ : Lexing.position * Lexing.position) (
# 239 "<standard.mly>"
        _2
# 282 "parser.ml"
   : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_loc__2_ : Lexing.position * Lexing.position) (
# 239 "<standard.mly>"
  x
# 286 "parser.ml"
   : 'tv_param) (_startpos_x_ : Lexing.position) (_endpos_x_ : Lexing.position) (_startofs_x_ : int) (_endofs_x_ : int) (_loc_x_ : Lexing.position * Lexing.position) ->
    (
# 240 "<standard.mly>"
    ( x :: xs )
# 291 "parser.ml"
     : 'tv_separated_nonempty_list_COMMA_param_) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 237 "<standard.mly>"
  x
# 296 "parser.ml"
   : 'tv_param) (_startpos_x_ : Lexing.position) (_endpos_x_ : Lexing.position) (_startofs_x_ : int) (_endofs_x_ : int) (_loc_x_ : Lexing.position * Lexing.position) ->
    (
# 238 "<standard.mly>"
    ( [ x ] )
# 301 "parser.ml"
     : 'tv_separated_nonempty_list_COMMA_param_) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 239 "<standard.mly>"
                    xs
# 306 "parser.ml"
   : 'tv_separated_nonempty_list_COMMA_expr_) (_startpos_xs_ : Lexing.position) (_endpos_xs_ : Lexing.position) (_startofs_xs_ : int) (_endofs_xs_ : int) (_loc_xs_ : Lexing.position * Lexing.position) (
# 239 "<standard.mly>"
        _2
# 310 "parser.ml"
   : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_loc__2_ : Lexing.position * Lexing.position) (
# 239 "<standard.mly>"
  x
# 314 "parser.ml"
   : 'tv_expr) (_startpos_x_ : Lexing.position) (_endpos_x_ : Lexing.position) (_startofs_x_ : int) (_endofs_x_ : int) (_loc_x_ : Lexing.position * Lexing.position) ->
    (
# 240 "<standard.mly>"
    ( x :: xs )
# 319 "parser.ml"
     : 'tv_separated_nonempty_list_COMMA_expr_) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 237 "<standard.mly>"
  x
# 324 "parser.ml"
   : 'tv_expr) (_startpos_x_ : Lexing.position) (_endpos_x_ : Lexing.position) (_startofs_x_ : int) (_endofs_x_ : int) (_loc_x_ : Lexing.position * Lexing.position) ->
    (
# 238 "<standard.mly>"
    ( [ x ] )
# 329 "parser.ml"
     : 'tv_separated_nonempty_list_COMMA_expr_) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 239 "<standard.mly>"
                    xs
# 334 "parser.ml"
   : 'tv_separated_nonempty_list_AND_ty_def_) (_startpos_xs_ : Lexing.position) (_endpos_xs_ : Lexing.position) (_startofs_xs_ : int) (_endofs_xs_ : int) (_loc_xs_ : Lexing.position * Lexing.position) (
# 239 "<standard.mly>"
        _2
# 338 "parser.ml"
   : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_loc__2_ : Lexing.position * Lexing.position) (
# 239 "<standard.mly>"
  x
# 342 "parser.ml"
   : 'tv_ty_def) (_startpos_x_ : Lexing.position) (_endpos_x_ : Lexing.position) (_startofs_x_ : int) (_endofs_x_ : int) (_loc_x_ : Lexing.position * Lexing.position) ->
    (
# 240 "<standard.mly>"
    ( x :: xs )
# 347 "parser.ml"
     : 'tv_separated_nonempty_list_AND_ty_def_) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 237 "<standard.mly>"
  x
# 352 "parser.ml"
   : 'tv_ty_def) (_startpos_x_ : Lexing.position) (_endpos_x_ : Lexing.position) (_startofs_x_ : int) (_endofs_x_ : int) (_loc_x_ : Lexing.position * Lexing.position) ->
    (
# 238 "<standard.mly>"
    ( [ x ] )
# 357 "parser.ml"
     : 'tv_separated_nonempty_list_AND_ty_def_) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 239 "<standard.mly>"
                    xs
# 362 "parser.ml"
   : 'tv_separated_nonempty_list_AND_let_rec_def_) (_startpos_xs_ : Lexing.position) (_endpos_xs_ : Lexing.position) (_startofs_xs_ : int) (_endofs_xs_ : int) (_loc_xs_ : Lexing.position * Lexing.position) (
# 239 "<standard.mly>"
        _2
# 366 "parser.ml"
   : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_loc__2_ : Lexing.position * Lexing.position) (
# 239 "<standard.mly>"
  x
# 370 "parser.ml"
   : 'tv_let_rec_def) (_startpos_x_ : Lexing.position) (_endpos_x_ : Lexing.position) (_startofs_x_ : int) (_endofs_x_ : int) (_loc_x_ : Lexing.position * Lexing.position) ->
    (
# 240 "<standard.mly>"
    ( x :: xs )
# 375 "parser.ml"
     : 'tv_separated_nonempty_list_AND_let_rec_def_) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 237 "<standard.mly>"
  x
# 380 "parser.ml"
   : 'tv_let_rec_def) (_startpos_x_ : Lexing.position) (_endpos_x_ : Lexing.position) (_startofs_x_ : int) (_endofs_x_ : int) (_loc_x_ : Lexing.position * Lexing.position) ->
    (
# 238 "<standard.mly>"
    ( [ x ] )
# 385 "parser.ml"
     : 'tv_separated_nonempty_list_AND_let_rec_def_) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 239 "<standard.mly>"
                    xs
# 390 "parser.ml"
   : 'tv_separated_nonempty_list_AND_let_def_) (_startpos_xs_ : Lexing.position) (_endpos_xs_ : Lexing.position) (_startofs_xs_ : int) (_endofs_xs_ : int) (_loc_xs_ : Lexing.position * Lexing.position) (
# 239 "<standard.mly>"
        _2
# 394 "parser.ml"
   : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_loc__2_ : Lexing.position * Lexing.position) (
# 239 "<standard.mly>"
  x
# 398 "parser.ml"
   : 'tv_let_def) (_startpos_x_ : Lexing.position) (_endpos_x_ : Lexing.position) (_startofs_x_ : int) (_endofs_x_ : int) (_loc_x_ : Lexing.position * Lexing.position) ->
    (
# 240 "<standard.mly>"
    ( x :: xs )
# 403 "parser.ml"
     : 'tv_separated_nonempty_list_AND_let_def_) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 237 "<standard.mly>"
  x
# 408 "parser.ml"
   : 'tv_let_def) (_startpos_x_ : Lexing.position) (_endpos_x_ : Lexing.position) (_startofs_x_ : int) (_endofs_x_ : int) (_loc_x_ : Lexing.position * Lexing.position) ->
    (
# 238 "<standard.mly>"
    ( [ x ] )
# 413 "parser.ml"
     : 'tv_separated_nonempty_list_AND_let_def_) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 219 "<standard.mly>"
         xs
# 418 "parser.ml"
   : 'tv_nonempty_list_simple_pat_) (_startpos_xs_ : Lexing.position) (_endpos_xs_ : Lexing.position) (_startofs_xs_ : int) (_endofs_xs_ : int) (_loc_xs_ : Lexing.position * Lexing.position) (
# 219 "<standard.mly>"
  x
# 422 "parser.ml"
   : 'tv_simple_pat) (_startpos_x_ : Lexing.position) (_endpos_x_ : Lexing.position) (_startofs_x_ : int) (_endofs_x_ : int) (_loc_x_ : Lexing.position * Lexing.position) ->
    (
# 220 "<standard.mly>"
    ( x :: xs )
# 427 "parser.ml"
     : 'tv_nonempty_list_simple_pat_) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 217 "<standard.mly>"
  x
# 432 "parser.ml"
   : 'tv_simple_pat) (_startpos_x_ : Lexing.position) (_endpos_x_ : Lexing.position) (_startofs_x_ : int) (_endofs_x_ : int) (_loc_x_ : Lexing.position * Lexing.position) ->
    (
# 218 "<standard.mly>"
    ( [ x ] )
# 437 "parser.ml"
     : 'tv_nonempty_list_simple_pat_) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 219 "<standard.mly>"
         xs
# 442 "parser.ml"
   : 'tv_nonempty_list_simple_expr_) (_startpos_xs_ : Lexing.position) (_endpos_xs_ : Lexing.position) (_startofs_xs_ : int) (_endofs_xs_ : int) (_loc_xs_ : Lexing.position * Lexing.position) (
# 219 "<standard.mly>"
  x
# 446 "parser.ml"
   : 'tv_simple_expr) (_startpos_x_ : Lexing.position) (_endpos_x_ : Lexing.position) (_startofs_x_ : int) (_endofs_x_ : int) (_loc_x_ : Lexing.position * Lexing.position) ->
    (
# 220 "<standard.mly>"
    ( x :: xs )
# 451 "parser.ml"
     : 'tv_nonempty_list_simple_expr_) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 217 "<standard.mly>"
  x
# 456 "parser.ml"
   : 'tv_simple_expr) (_startpos_x_ : Lexing.position) (_endpos_x_ : Lexing.position) (_startofs_x_ : int) (_endofs_x_ : int) (_loc_x_ : Lexing.position * Lexing.position) ->
    (
# 218 "<standard.mly>"
    ( [ x ] )
# 461 "parser.ml"
     : 'tv_nonempty_list_simple_expr_) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 219 "<standard.mly>"
         xs
# 466 "parser.ml"
   : 'tv_nonempty_list___anonymous_2_) (_startpos_xs_ : Lexing.position) (_endpos_xs_ : Lexing.position) (_startofs_xs_ : int) (_endofs_xs_ : int) (_loc_xs_ : Lexing.position * Lexing.position) (
# 219 "<standard.mly>"
  x
# 470 "parser.ml"
   : 'tv___anonymous_2) (_startpos_x_ : Lexing.position) (_endpos_x_ : Lexing.position) (_startofs_x_ : int) (_endofs_x_ : int) (_loc_x_ : Lexing.position * Lexing.position) ->
    (
# 220 "<standard.mly>"
    ( x :: xs )
# 475 "parser.ml"
     : 'tv_nonempty_list___anonymous_2_) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 217 "<standard.mly>"
  x
# 480 "parser.ml"
   : 'tv___anonymous_2) (_startpos_x_ : Lexing.position) (_endpos_x_ : Lexing.position) (_startofs_x_ : int) (_endofs_x_ : int) (_loc_x_ : Lexing.position * Lexing.position) ->
    (
# 218 "<standard.mly>"
    ( [ x ] )
# 485 "parser.ml"
     : 'tv_nonempty_list___anonymous_2_) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 219 "<standard.mly>"
         xs
# 490 "parser.ml"
   : 'tv_nonempty_list___anonymous_1_) (_startpos_xs_ : Lexing.position) (_endpos_xs_ : Lexing.position) (_startofs_xs_ : int) (_endofs_xs_ : int) (_loc_xs_ : Lexing.position * Lexing.position) (
# 219 "<standard.mly>"
  x
# 494 "parser.ml"
   : 'tv___anonymous_1) (_startpos_x_ : Lexing.position) (_endpos_x_ : Lexing.position) (_startofs_x_ : int) (_endofs_x_ : int) (_loc_x_ : Lexing.position * Lexing.position) ->
    (
# 220 "<standard.mly>"
    ( x :: xs )
# 499 "parser.ml"
     : 'tv_nonempty_list___anonymous_1_) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 217 "<standard.mly>"
  x
# 504 "parser.ml"
   : 'tv___anonymous_1) (_startpos_x_ : Lexing.position) (_endpos_x_ : Lexing.position) (_startofs_x_ : int) (_endofs_x_ : int) (_loc_x_ : Lexing.position * Lexing.position) ->
    (
# 218 "<standard.mly>"
    ( [ x ] )
# 509 "parser.ml"
     : 'tv_nonempty_list___anonymous_1_) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 219 "<standard.mly>"
         xs
# 514 "parser.ml"
   : 'tv_nonempty_list___anonymous_0_) (_startpos_xs_ : Lexing.position) (_endpos_xs_ : Lexing.position) (_startofs_xs_ : int) (_endofs_xs_ : int) (_loc_xs_ : Lexing.position * Lexing.position) (
# 219 "<standard.mly>"
  x
# 518 "parser.ml"
   : 'tv___anonymous_0) (_startpos_x_ : Lexing.position) (_endpos_x_ : Lexing.position) (_startofs_x_ : int) (_endofs_x_ : int) (_loc_x_ : Lexing.position * Lexing.position) ->
    (
# 220 "<standard.mly>"
    ( x :: xs )
# 523 "parser.ml"
     : 'tv_nonempty_list___anonymous_0_) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 217 "<standard.mly>"
  x
# 528 "parser.ml"
   : 'tv___anonymous_0) (_startpos_x_ : Lexing.position) (_endpos_x_ : Lexing.position) (_startofs_x_ : int) (_endofs_x_ : int) (_loc_x_ : Lexing.position * Lexing.position) ->
    (
# 218 "<standard.mly>"
    ( [ x ] )
# 533 "parser.ml"
     : 'tv_nonempty_list___anonymous_0_) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 201 "parser.mly"
 _1
# 538 "parser.ml"
   : 'tv_lid) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) (_loc__1_ : Lexing.position * Lexing.position) ->
    (
# 202 "parser.mly"
    ( _1 )
# 543 "parser.ml"
     : 'tv_tyname) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 264 "parser.mly"
                     _4
# 548 "parser.ml"
   : 'tv_ty) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_loc__4_ : Lexing.position * Lexing.position) (
# 264 "parser.mly"
               _3
# 552 "parser.ml"
   : unit) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_loc__3_ : Lexing.position * Lexing.position) (
# 264 "parser.mly"
        _2
# 556 "parser.ml"
   : 'tv_tyname) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_loc__2_ : Lexing.position * Lexing.position) (
# 264 "parser.mly"
 _1
# 560 "parser.ml"
   : 'tv_params) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) (_loc__1_ : Lexing.position * Lexing.position) ->
    (
# 265 "parser.mly"
    ( _1 )
# 565 "parser.ml"
     : 'tv_ty_def) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 262 "parser.mly"
                     _4
# 570 "parser.ml"
   : 'tv_nonempty_list___anonymous_2_) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_loc__4_ : Lexing.position * Lexing.position) (
# 262 "parser.mly"
               _3
# 574 "parser.ml"
   : unit) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_loc__3_ : Lexing.position * Lexing.position) (
# 262 "parser.mly"
        _2
# 578 "parser.ml"
   : 'tv_tyname) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_loc__2_ : Lexing.position * Lexing.position) (
# 262 "parser.mly"
 _1
# 582 "parser.ml"
   : 'tv_params) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) (_loc__1_ : Lexing.position * Lexing.position) ->
    (
# 263 "parser.mly"
    ( Dvariant(_2,_1,_4) )
# 587 "parser.ml"
     : 'tv_ty_def) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 260 "parser.mly"
                                                                                            _6
# 592 "parser.ml"
   : unit) (_startpos__6_ : Lexing.position) (_endpos__6_ : Lexing.position) (_startofs__6_ : int) (_endofs__6_ : int) (_loc__6_ : Lexing.position * Lexing.position) (
# 260 "parser.mly"
                            _5
# 596 "parser.ml"
   : 'tv_separated_nonempty_list_SEMI_separated_pair_field_COLON_ty__) (_startpos__5_ : Lexing.position) (_endpos__5_ : Lexing.position) (_startofs__5_ : int) (_endofs__5_ : int) (_loc__5_ : Lexing.position * Lexing.position) (
# 260 "parser.mly"
                     _4
# 600 "parser.ml"
   : unit) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_loc__4_ : Lexing.position * Lexing.position) (
# 260 "parser.mly"
               _3
# 604 "parser.ml"
   : unit) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_loc__3_ : Lexing.position * Lexing.position) (
# 260 "parser.mly"
        _2
# 608 "parser.ml"
   : 'tv_tyname) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_loc__2_ : Lexing.position * Lexing.position) (
# 260 "parser.mly"
 _1
# 612 "parser.ml"
   : 'tv_params) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) (_loc__1_ : Lexing.position * Lexing.position) ->
    (
# 261 "parser.mly"
    ( Drecord(_2,_1,_5) )
# 617 "parser.ml"
     : 'tv_ty_def) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 272 "parser.mly"
 _1
# 622 "parser.ml"
   : 'tv_tuple_ty) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) (_loc__1_ : Lexing.position * Lexing.position) ->
    (
# 273 "parser.mly"
    ( Ttuple _1 )
# 627 "parser.ml"
     : 'tv_ty) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 270 "parser.mly"
          _3
# 632 "parser.ml"
   : 'tv_ty) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_loc__3_ : Lexing.position * Lexing.position) (
# 270 "parser.mly"
    _2
# 636 "parser.ml"
   : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_loc__2_ : Lexing.position * Lexing.position) (
# 270 "parser.mly"
 _1
# 640 "parser.ml"
   : 'tv_ty) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) (_loc__1_ : Lexing.position * Lexing.position) ->
    (
# 271 "parser.mly"
    ( Tarrow(_1,_3) )
# 645 "parser.ml"
     : 'tv_ty) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 268 "parser.mly"
 _1
# 650 "parser.ml"
   : 'tv_simple_ty) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) (_loc__1_ : Lexing.position * Lexing.position) ->
    (
# 269 "parser.mly"
    ( _1 )
# 655 "parser.ml"
     : 'tv_ty) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 276 "parser.mly"
                _3
# 660 "parser.ml"
   : 'tv_separated_nonempty_list_STAR_simple_ty_) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_loc__3_ : Lexing.position * Lexing.position) (
# 276 "parser.mly"
           _2
# 664 "parser.ml"
   : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_loc__2_ : Lexing.position * Lexing.position) (
# 276 "parser.mly"
 _1
# 668 "parser.ml"
   : 'tv_simple_ty) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) (_loc__1_ : Lexing.position * Lexing.position) ->
    (
# 277 "parser.mly"
    ( _1::_3 )
# 673 "parser.ml"
     : 'tv_tuple_ty) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) ((
# 58 "parser.mly"
               _3
# 678 "parser.ml"
   : 'tv_top) : (
# 46 "parser.mly"
      (def list)
# 682 "parser.ml"
  )) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_loc__3_ : Lexing.position * Lexing.position) (
# 58 "parser.mly"
      _2
# 686 "parser.ml"
   : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_loc__2_ : Lexing.position * Lexing.position) (
# 58 "parser.mly"
 _1
# 690 "parser.ml"
   : 'tv_expr) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) (_loc__1_ : Lexing.position * Lexing.position) ->
    ((
# 59 "parser.mly"
     ( (Defexpr _1)::_3 )
# 695 "parser.ml"
     : 'tv_top) : (
# 46 "parser.mly"
      (def list)
# 699 "parser.ml"
    )) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) ((
# 56 "parser.mly"
              _3
# 704 "parser.ml"
   : 'tv_top) : (
# 46 "parser.mly"
      (def list)
# 708 "parser.ml"
  )) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_loc__3_ : Lexing.position * Lexing.position) (
# 56 "parser.mly"
     _2
# 712 "parser.ml"
   : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_loc__2_ : Lexing.position * Lexing.position) (
# 56 "parser.mly"
 _1
# 716 "parser.ml"
   : 'tv_def) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) (_loc__1_ : Lexing.position * Lexing.position) ->
    ((
# 57 "parser.mly"
    ( _1::_3 )
# 721 "parser.ml"
     : 'tv_top) : (
# 46 "parser.mly"
      (def list)
# 725 "parser.ml"
    )) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 54 "parser.mly"
      _2
# 730 "parser.ml"
   : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_loc__2_ : Lexing.position * Lexing.position) (
# 54 "parser.mly"
 _1
# 734 "parser.ml"
   : 'tv_expr) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) (_loc__1_ : Lexing.position * Lexing.position) ->
    ((
# 55 "parser.mly"
    ( Defexpr _1 )
# 739 "parser.ml"
     : 'tv_top) : (
# 46 "parser.mly"
      (def list)
# 743 "parser.ml"
    )) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 52 "parser.mly"
     _2
# 748 "parser.ml"
   : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_loc__2_ : Lexing.position * Lexing.position) (
# 52 "parser.mly"
 _1
# 752 "parser.ml"
   : 'tv_def) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) (_loc__1_ : Lexing.position * Lexing.position) ->
    ((
# 53 "parser.mly"
    ( _1 )
# 757 "parser.ml"
     : 'tv_top) : (
# 46 "parser.mly"
      (def list)
# 761 "parser.ml"
    )) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 294 "parser.mly"
        _3
# 766 "parser.ml"
   : 'tv_ty) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_loc__3_ : Lexing.position * Lexing.position) (
# 294 "parser.mly"
     _2
# 770 "parser.ml"
   : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_loc__2_ : Lexing.position * Lexing.position) (
# 294 "parser.mly"
 _1
# 774 "parser.ml"
   : (
# 10 "parser.mly"
       (string)
# 778 "parser.ml"
  )) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) (_loc__1_ : Lexing.position * Lexing.position) ->
    (
# 295 "parser.mly"
    ( Gconstruct(_1,_3) )
# 783 "parser.ml"
     : 'tv_sum_case) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 292 "parser.mly"
 _1
# 788 "parser.ml"
   : (
# 10 "parser.mly"
       (string)
# 792 "parser.ml"
  )) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) (_loc__1_ : Lexing.position * Lexing.position) ->
    (
# 293 "parser.mly"
    ( Gconstruct_ _1 )
# 797 "parser.ml"
     : 'tv_sum_case) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 288 "parser.mly"
           _3
# 802 "parser.ml"
   : unit) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_loc__3_ : Lexing.position * Lexing.position) (
# 288 "parser.mly"
        _2
# 806 "parser.ml"
   : 'tv_ty) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_loc__2_ : Lexing.position * Lexing.position) (
# 288 "parser.mly"
 _1
# 810 "parser.ml"
   : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) (_loc__1_ : Lexing.position * Lexing.position) ->
    (
# 289 "parser.mly"
    ( _1 )
# 815 "parser.ml"
     : 'tv_simple_ty) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 286 "parser.mly"
 _1
# 820 "parser.ml"
   : 'tv_param) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) (_loc__1_ : Lexing.position * Lexing.position) ->
    (
# 287 "parser.mly"
    ( Tvar _1 )
# 825 "parser.ml"
     : 'tv_simple_ty) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 284 "parser.mly"
 _1
# 830 "parser.ml"
   : 'tv_tyname) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) (_loc__1_ : Lexing.position * Lexing.position) ->
    (
# 285 "parser.mly"
    ( Tname _1 )
# 835 "parser.ml"
     : 'tv_simple_ty) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 282 "parser.mly"
           _2
# 840 "parser.ml"
   : 'tv_tyname) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_loc__2_ : Lexing.position * Lexing.position) (
# 282 "parser.mly"
 _1
# 844 "parser.ml"
   : 'tv_simple_ty) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) (_loc__1_ : Lexing.position * Lexing.position) ->
    (
# 283 "parser.mly"
    ( Tconstr(_2,_1::[]) )
# 849 "parser.ml"
     : 'tv_simple_ty) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 280 "parser.mly"
                                                           _6
# 854 "parser.ml"
   : 'tv_tyname) (_startpos__6_ : Lexing.position) (_endpos__6_ : Lexing.position) (_startofs__6_ : int) (_endofs__6_ : int) (_loc__6_ : Lexing.position * Lexing.position) (
# 280 "parser.mly"
                                                    _5
# 858 "parser.ml"
   : unit) (_startpos__5_ : Lexing.position) (_endpos__5_ : Lexing.position) (_startofs__5_ : int) (_endofs__5_ : int) (_loc__5_ : Lexing.position * Lexing.position) (
# 280 "parser.mly"
                 _4
# 862 "parser.ml"
   : 'tv_separated_nonempty_list_COMMA_ty_) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_loc__4_ : Lexing.position * Lexing.position) (
# 280 "parser.mly"
           _3
# 866 "parser.ml"
   : unit) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_loc__3_ : Lexing.position * Lexing.position) (
# 280 "parser.mly"
        _2
# 870 "parser.ml"
   : 'tv_ty) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_loc__2_ : Lexing.position * Lexing.position) (
# 280 "parser.mly"
 _1
# 874 "parser.ml"
   : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) (_loc__1_ : Lexing.position * Lexing.position) ->
    (
# 281 "parser.mly"
    ( Tconstr(_6,_2::_4) )
# 879 "parser.ml"
     : 'tv_simple_ty) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 188 "parser.mly"
                  _3
# 884 "parser.ml"
   : unit) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_loc__3_ : Lexing.position * Lexing.position) (
# 188 "parser.mly"
        _2
# 888 "parser.ml"
   : 'tv_comma_pat) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_loc__2_ : Lexing.position * Lexing.position) (
# 188 "parser.mly"
 _1
# 892 "parser.ml"
   : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) (_loc__1_ : Lexing.position * Lexing.position) ->
    (
# 189 "parser.mly"
    ( Ptuple _2 )
# 897 "parser.ml"
     : 'tv_simple_pat) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 186 "parser.mly"
            _3
# 902 "parser.ml"
   : unit) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_loc__3_ : Lexing.position * Lexing.position) (
# 186 "parser.mly"
        _2
# 906 "parser.ml"
   : 'tv_pat) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_loc__2_ : Lexing.position * Lexing.position) (
# 186 "parser.mly"
 _1
# 910 "parser.ml"
   : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) (_loc__1_ : Lexing.position * Lexing.position) ->
    (
# 187 "parser.mly"
    ( _2 )
# 915 "parser.ml"
     : 'tv_simple_pat) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 184 "parser.mly"
                     _5
# 920 "parser.ml"
   : unit) (_startpos__5_ : Lexing.position) (_endpos__5_ : Lexing.position) (_startofs__5_ : int) (_endofs__5_ : int) (_loc__5_ : Lexing.position * Lexing.position) (
# 184 "parser.mly"
                  _4
# 924 "parser.ml"
   : 'tv_ty) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_loc__4_ : Lexing.position * Lexing.position) (
# 184 "parser.mly"
            _3
# 928 "parser.ml"
   : unit) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_loc__3_ : Lexing.position * Lexing.position) (
# 184 "parser.mly"
        _2
# 932 "parser.ml"
   : 'tv_pat) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_loc__2_ : Lexing.position * Lexing.position) (
# 184 "parser.mly"
 _1
# 936 "parser.ml"
   : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) (_loc__1_ : Lexing.position * Lexing.position) ->
    (
# 185 "parser.mly"
    ( Pconstraint (_2,_4) )
# 941 "parser.ml"
     : 'tv_simple_pat) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 182 "parser.mly"
        _2
# 946 "parser.ml"
   : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_loc__2_ : Lexing.position * Lexing.position) (
# 182 "parser.mly"
 _1
# 950 "parser.ml"
   : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) (_loc__1_ : Lexing.position * Lexing.position) ->
    (
# 183 "parser.mly"
    ( Pconstruct_ "()" )
# 955 "parser.ml"
     : 'tv_simple_pat) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 180 "parser.mly"
        _2
# 960 "parser.ml"
   : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_loc__2_ : Lexing.position * Lexing.position) (
# 180 "parser.mly"
 _1
# 964 "parser.ml"
   : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) (_loc__1_ : Lexing.position * Lexing.position) ->
    (
# 181 "parser.mly"
    ( Pconstruct_ "[]" )
# 969 "parser.ml"
     : 'tv_simple_pat) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 178 "parser.mly"
                      _3
# 974 "parser.ml"
   : unit) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_loc__3_ : Lexing.position * Lexing.position) (
# 178 "parser.mly"
        _2
# 978 "parser.ml"
   : 'tv_pat_semi_list) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_loc__2_ : Lexing.position * Lexing.position) (
# 178 "parser.mly"
 _1
# 982 "parser.ml"
   : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) (_loc__1_ : Lexing.position * Lexing.position) ->
    (
# 179 "parser.mly"
    ( _2 )
# 987 "parser.ml"
     : 'tv_simple_pat) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 176 "parser.mly"
                                                                         _3
# 992 "parser.ml"
   : unit) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_loc__3_ : Lexing.position * Lexing.position) (
# 176 "parser.mly"
        _2
# 996 "parser.ml"
   : 'tv_separated_nonempty_list_SEMI_separated_pair_field_EQUAL_pat__) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_loc__2_ : Lexing.position * Lexing.position) (
# 176 "parser.mly"
 _1
# 1000 "parser.ml"
   : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) (_loc__1_ : Lexing.position * Lexing.position) ->
    (
# 177 "parser.mly"
    ( Precord _2 )
# 1005 "parser.ml"
     : 'tv_simple_pat) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 174 "parser.mly"
 _1
# 1010 "parser.ml"
   : 'tv_const_expr) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) (_loc__1_ : Lexing.position * Lexing.position) ->
    (
# 175 "parser.mly"
    ( Pconstant _1 )
# 1015 "parser.ml"
     : 'tv_simple_pat) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 172 "parser.mly"
 _1
# 1020 "parser.ml"
   : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) (_loc__1_ : Lexing.position * Lexing.position) ->
    (
# 173 "parser.mly"
    ( Pwild )
# 1025 "parser.ml"
     : 'tv_simple_pat) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 170 "parser.mly"
 _1
# 1030 "parser.ml"
   : (
# 10 "parser.mly"
       (string)
# 1034 "parser.ml"
  )) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) (_loc__1_ : Lexing.position * Lexing.position) ->
    (
# 171 "parser.mly"
    ( Pconstruct_ _1 )
# 1039 "parser.ml"
     : 'tv_simple_pat) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 168 "parser.mly"
 _1
# 1044 "parser.ml"
   : 'tv_ident) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) (_loc__1_ : Lexing.position * Lexing.position) ->
    (
# 169 "parser.mly"
    ( Pvar _1 )
# 1049 "parser.ml"
     : 'tv_simple_pat) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 104 "parser.mly"
            _3
# 1054 "parser.ml"
   : unit) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_loc__3_ : Lexing.position * Lexing.position) (
# 104 "parser.mly"
       _2
# 1058 "parser.ml"
   : 'tv_expr) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_loc__2_ : Lexing.position * Lexing.position) (
# 104 "parser.mly"
 _1
# 1062 "parser.ml"
   : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) (_loc__1_ : Lexing.position * Lexing.position) ->
    (
# 104 "parser.mly"
                 ( _2 )
# 1067 "parser.ml"
     : 'tv_simple_expr) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 103 "parser.mly"
             _3
# 1072 "parser.ml"
   : unit) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_loc__3_ : Lexing.position * Lexing.position) (
# 103 "parser.mly"
        _2
# 1076 "parser.ml"
   : 'tv_expr) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_loc__2_ : Lexing.position * Lexing.position) (
# 103 "parser.mly"
 _1
# 1080 "parser.ml"
   : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) (_loc__1_ : Lexing.position * Lexing.position) ->
    (
# 103 "parser.mly"
                     ( _2 )
# 1085 "parser.ml"
     : 'tv_simple_expr) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 102 "parser.mly"
                      _5
# 1090 "parser.ml"
   : unit) (_startpos__5_ : Lexing.position) (_endpos__5_ : Lexing.position) (_startofs__5_ : int) (_endofs__5_ : int) (_loc__5_ : Lexing.position * Lexing.position) (
# 102 "parser.mly"
                   _4
# 1094 "parser.ml"
   : 'tv_ty) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_loc__4_ : Lexing.position * Lexing.position) (
# 102 "parser.mly"
             _3
# 1098 "parser.ml"
   : unit) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_loc__3_ : Lexing.position * Lexing.position) (
# 102 "parser.mly"
        _2
# 1102 "parser.ml"
   : 'tv_expr) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_loc__2_ : Lexing.position * Lexing.position) (
# 102 "parser.mly"
 _1
# 1106 "parser.ml"
   : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) (_loc__1_ : Lexing.position * Lexing.position) ->
    (
# 102 "parser.mly"
                              ( Econstraint(_2,_4) )
# 1111 "parser.ml"
     : 'tv_simple_expr) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 100 "parser.mly"
                                                       _5
# 1116 "parser.ml"
   : unit) (_startpos__5_ : Lexing.position) (_endpos__5_ : Lexing.position) (_startofs__5_ : int) (_endofs__5_ : int) (_loc__5_ : Lexing.position * Lexing.position) (
# 100 "parser.mly"
                   _4
# 1120 "parser.ml"
   : 'tv_separated_nonempty_list_COMMA_expr_) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_loc__4_ : Lexing.position * Lexing.position) (
# 100 "parser.mly"
             _3
# 1124 "parser.ml"
   : unit) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_loc__3_ : Lexing.position * Lexing.position) (
# 100 "parser.mly"
        _2
# 1128 "parser.ml"
   : 'tv_expr) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_loc__2_ : Lexing.position * Lexing.position) (
# 100 "parser.mly"
 _1
# 1132 "parser.ml"
   : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) (_loc__1_ : Lexing.position * Lexing.position) ->
    (
# 101 "parser.mly"
    ( Etuple(_2::_4) )
# 1137 "parser.ml"
     : 'tv_simple_expr) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 99 "parser.mly"
        _2
# 1142 "parser.ml"
   : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_loc__2_ : Lexing.position * Lexing.position) (
# 99 "parser.mly"
 _1
# 1146 "parser.ml"
   : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) (_loc__1_ : Lexing.position * Lexing.position) ->
    (
# 99 "parser.mly"
                ( Econstruct_ "()" )
# 1151 "parser.ml"
     : 'tv_simple_expr) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 98 "parser.mly"
                        _3
# 1156 "parser.ml"
   : unit) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_loc__3_ : Lexing.position * Lexing.position) (
# 98 "parser.mly"
        _2
# 1160 "parser.ml"
   : 'tv_expr_label_list) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_loc__2_ : Lexing.position * Lexing.position) (
# 98 "parser.mly"
 _1
# 1164 "parser.ml"
   : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) (_loc__1_ : Lexing.position * Lexing.position) ->
    (
# 98 "parser.mly"
                                ( Erecord _2 )
# 1169 "parser.ml"
     : 'tv_simple_expr) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 97 "parser.mly"
                       _3
# 1174 "parser.ml"
   : unit) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_loc__3_ : Lexing.position * Lexing.position) (
# 97 "parser.mly"
        _2
# 1178 "parser.ml"
   : 'tv_expr_semi_list) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_loc__2_ : Lexing.position * Lexing.position) (
# 97 "parser.mly"
 _1
# 1182 "parser.ml"
   : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) (_loc__1_ : Lexing.position * Lexing.position) ->
    (
# 97 "parser.mly"
                               ( _1 )
# 1187 "parser.ml"
     : 'tv_simple_expr) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 96 "parser.mly"
        _2
# 1192 "parser.ml"
   : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_loc__2_ : Lexing.position * Lexing.position) (
# 96 "parser.mly"
 _1
# 1196 "parser.ml"
   : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) (_loc__1_ : Lexing.position * Lexing.position) ->
    (
# 96 "parser.mly"
                ( Econstruct_ "[]" )
# 1201 "parser.ml"
     : 'tv_simple_expr) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 95 "parser.mly"
 _1
# 1206 "parser.ml"
   : 'tv_const_expr) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) (_loc__1_ : Lexing.position * Lexing.position) ->
    (
# 95 "parser.mly"
             ( _1 )
# 1211 "parser.ml"
     : 'tv_simple_expr) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 94 "parser.mly"
 _1
# 1216 "parser.ml"
   : (
# 10 "parser.mly"
       (string)
# 1220 "parser.ml"
  )) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) (_loc__1_ : Lexing.position * Lexing.position) ->
    (
# 94 "parser.mly"
      ( Econstruct_ _1 )
# 1225 "parser.ml"
     : 'tv_simple_expr) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 93 "parser.mly"
 _1
# 1230 "parser.ml"
   : 'tv_ident) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) (_loc__1_ : Lexing.position * Lexing.position) ->
    (
# 93 "parser.mly"
        ( Evar _1 )
# 1235 "parser.ml"
     : 'tv_simple_expr) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 163 "parser.mly"
 _1
# 1240 "parser.ml"
   : 'tv_pat) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) (_loc__1_ : Lexing.position * Lexing.position) ->
    (
# 164 "parser.mly"
  ( Pconstruct("::",Ptuple(_1::(Pconstruct_ "[]")::[])) )
# 1245 "parser.ml"
     : 'tv_pat_semi_list) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 161 "parser.mly"
                    _3
# 1250 "parser.ml"
   : 'tv_pat) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_loc__3_ : Lexing.position * Lexing.position) (
# 161 "parser.mly"
               _2
# 1254 "parser.ml"
   : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_loc__2_ : Lexing.position * Lexing.position) (
# 161 "parser.mly"
 _1
# 1258 "parser.ml"
   : 'tv_pat_semi_list) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) (_loc__1_ : Lexing.position * Lexing.position) ->
    (
# 162 "parser.mly"
  ( Pconstruct("::",Ptuple(_1::_2::[])) )
# 1263 "parser.ml"
     : 'tv_pat_semi_list) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 152 "parser.mly"
     _2
# 1268 "parser.ml"
   : 'tv_simple_pat) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_loc__2_ : Lexing.position * Lexing.position) (
# 152 "parser.mly"
 _1
# 1272 "parser.ml"
   : (
# 10 "parser.mly"
       (string)
# 1276 "parser.ml"
  )) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) (_loc__1_ : Lexing.position * Lexing.position) ->
    (
# 153 "parser.mly"
    ( Pconstruct(_1,_2) )
# 1281 "parser.ml"
     : 'tv_pat) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 150 "parser.mly"
          _3
# 1286 "parser.ml"
   : 'tv_pat) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_loc__3_ : Lexing.position * Lexing.position) (
# 150 "parser.mly"
     _2
# 1290 "parser.ml"
   : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_loc__2_ : Lexing.position * Lexing.position) (
# 150 "parser.mly"
 _1
# 1294 "parser.ml"
   : 'tv_pat) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) (_loc__1_ : Lexing.position * Lexing.position) ->
    (
# 151 "parser.mly"
    ( Pconstruct("::",Ptuple(_1::_3::[])) )
# 1299 "parser.ml"
     : 'tv_pat) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 148 "parser.mly"
        _3
# 1304 "parser.ml"
   : 'tv_lid) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_loc__3_ : Lexing.position * Lexing.position) (
# 148 "parser.mly"
     _2
# 1308 "parser.ml"
   : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_loc__2_ : Lexing.position * Lexing.position) (
# 148 "parser.mly"
 _1
# 1312 "parser.ml"
   : 'tv_pat) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) (_loc__1_ : Lexing.position * Lexing.position) ->
    (
# 149 "parser.mly"
    ( Pconstraint(_1,_3) )
# 1317 "parser.ml"
     : 'tv_pat) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 146 "parser.mly"
 _1
# 1322 "parser.ml"
   : 'tv_simple_pat) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) (_loc__1_ : Lexing.position * Lexing.position) ->
    (
# 147 "parser.mly"
    ( _1 )
# 1327 "parser.ml"
     : 'tv_pat) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 256 "parser.mly"
                                              _3
# 1332 "parser.ml"
   : unit) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_loc__3_ : Lexing.position * Lexing.position) (
# 256 "parser.mly"
        _2
# 1336 "parser.ml"
   : 'tv_separated_nonempty_list_COMMA_param_) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_loc__2_ : Lexing.position * Lexing.position) (
# 256 "parser.mly"
 _1
# 1340 "parser.ml"
   : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) (_loc__1_ : Lexing.position * Lexing.position) ->
    (
# 257 "parser.mly"
    ( _2 )
# 1345 "parser.ml"
     : 'tv_params) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 254 "parser.mly"
 _1
# 1350 "parser.ml"
   : 'tv_param) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) (_loc__1_ : Lexing.position * Lexing.position) ->
    (
# 255 "parser.mly"
    ( _1::[] )
# 1355 "parser.ml"
     : 'tv_params) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) ->
    (
# 253 "parser.mly"
    ( [] )
# 1361 "parser.ml"
     : 'tv_params) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 247 "parser.mly"
       _2
# 1366 "parser.ml"
   : 'tv_lid) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_loc__2_ : Lexing.position * Lexing.position) (
# 247 "parser.mly"
 _1
# 1370 "parser.ml"
   : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) (_loc__1_ : Lexing.position * Lexing.position) ->
    (
# 248 "parser.mly"
   ( {id=_2; level=ref 0} )
# 1375 "parser.ml"
     : 'tv_param) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 193 "parser.mly"
 _1
# 1380 "parser.ml"
   : (
# 10 "parser.mly"
       (string)
# 1384 "parser.ml"
  )) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) (_loc__1_ : Lexing.position * Lexing.position) ->
    (
# 194 "parser.mly"
    ( _1 )
# 1389 "parser.ml"
     : 'tv_lid) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 142 "parser.mly"
                                                _6
# 1394 "parser.ml"
   : 'tv_expr) (_startpos__6_ : Lexing.position) (_endpos__6_ : Lexing.position) (_startofs__6_ : int) (_endofs__6_ : int) (_loc__6_ : Lexing.position * Lexing.position) (
# 142 "parser.mly"
                                          _5
# 1398 "parser.ml"
   : unit) (_startpos__5_ : Lexing.position) (_endpos__5_ : Lexing.position) (_startofs__5_ : int) (_endofs__5_ : int) (_loc__5_ : Lexing.position * Lexing.position) (
# 142 "parser.mly"
                                       _4
# 1402 "parser.ml"
   : 'tv_ty) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_loc__4_ : Lexing.position * Lexing.position) (
# 142 "parser.mly"
                                 _3
# 1406 "parser.ml"
   : unit) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_loc__3_ : Lexing.position * Lexing.position) (
# 142 "parser.mly"
       _2
# 1410 "parser.ml"
   : 'tv_nonempty_list_simple_pat_) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_loc__2_ : Lexing.position * Lexing.position) (
# 142 "parser.mly"
 _1
# 1414 "parser.ml"
   : 'tv_ident) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) (_loc__1_ : Lexing.position * Lexing.position) ->
    (
# 143 "parser.mly"
    ( (Pvar _1,Efunction((_2,Econstraint(_6,_4))::[])) )
# 1419 "parser.ml"
     : 'tv_let_rec_def) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 140 "parser.mly"
                                       _4
# 1424 "parser.ml"
   : 'tv_expr) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_loc__4_ : Lexing.position * Lexing.position) (
# 140 "parser.mly"
                                 _3
# 1428 "parser.ml"
   : unit) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_loc__3_ : Lexing.position * Lexing.position) (
# 140 "parser.mly"
       _2
# 1432 "parser.ml"
   : 'tv_nonempty_list_simple_pat_) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_loc__2_ : Lexing.position * Lexing.position) (
# 140 "parser.mly"
 _1
# 1436 "parser.ml"
   : 'tv_ident) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) (_loc__1_ : Lexing.position * Lexing.position) ->
    (
# 141 "parser.mly"
    ( (Pvar _1,Efunction((_2,_4)::[])) )
# 1441 "parser.ml"
     : 'tv_let_rec_def) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 136 "parser.mly"
                                                _6
# 1446 "parser.ml"
   : 'tv_expr) (_startpos__6_ : Lexing.position) (_endpos__6_ : Lexing.position) (_startofs__6_ : int) (_endofs__6_ : int) (_loc__6_ : Lexing.position * Lexing.position) (
# 136 "parser.mly"
                                          _5
# 1450 "parser.ml"
   : unit) (_startpos__5_ : Lexing.position) (_endpos__5_ : Lexing.position) (_startofs__5_ : int) (_endofs__5_ : int) (_loc__5_ : Lexing.position * Lexing.position) (
# 136 "parser.mly"
                                       _4
# 1454 "parser.ml"
   : 'tv_ty) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_loc__4_ : Lexing.position * Lexing.position) (
# 136 "parser.mly"
                                 _3
# 1458 "parser.ml"
   : unit) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_loc__3_ : Lexing.position * Lexing.position) (
# 136 "parser.mly"
       _2
# 1462 "parser.ml"
   : 'tv_nonempty_list_simple_pat_) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_loc__2_ : Lexing.position * Lexing.position) (
# 136 "parser.mly"
 _1
# 1466 "parser.ml"
   : 'tv_ident) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) (_loc__1_ : Lexing.position * Lexing.position) ->
    (
# 137 "parser.mly"
    ( (Pvar _1,Efunction((_2,Econstraint(_6,_4))::[])) )
# 1471 "parser.ml"
     : 'tv_let_def) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 134 "parser.mly"
                                       _4
# 1476 "parser.ml"
   : 'tv_expr) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_loc__4_ : Lexing.position * Lexing.position) (
# 134 "parser.mly"
                                 _3
# 1480 "parser.ml"
   : unit) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_loc__3_ : Lexing.position * Lexing.position) (
# 134 "parser.mly"
       _2
# 1484 "parser.ml"
   : 'tv_nonempty_list_simple_pat_) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_loc__2_ : Lexing.position * Lexing.position) (
# 134 "parser.mly"
 _1
# 1488 "parser.ml"
   : 'tv_ident) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) (_loc__1_ : Lexing.position * Lexing.position) ->
    (
# 135 "parser.mly"
    ( (Pvar _1,Efunction((_2,_4)::[])) )
# 1493 "parser.ml"
     : 'tv_let_def) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 132 "parser.mly"
           _3
# 1498 "parser.ml"
   : 'tv_expr) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_loc__3_ : Lexing.position * Lexing.position) (
# 132 "parser.mly"
     _2
# 1502 "parser.ml"
   : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_loc__2_ : Lexing.position * Lexing.position) (
# 132 "parser.mly"
 _1
# 1506 "parser.ml"
   : 'tv_pat) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) (_loc__1_ : Lexing.position * Lexing.position) ->
    (
# 133 "parser.mly"
    ( (_1,_3) )
# 1511 "parser.ml"
     : 'tv_let_def) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 206 "parser.mly"
              _3
# 1516 "parser.ml"
   : unit) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_loc__3_ : Lexing.position * Lexing.position) (
# 206 "parser.mly"
        _2
# 1520 "parser.ml"
   : 'tv_binop) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_loc__2_ : Lexing.position * Lexing.position) (
# 206 "parser.mly"
 _1
# 1524 "parser.ml"
   : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) (_loc__1_ : Lexing.position * Lexing.position) ->
    (
# 207 "parser.mly"
    ( _2 )
# 1529 "parser.ml"
     : 'tv_ident) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 205 "parser.mly"
 _1
# 1534 "parser.ml"
   : 'tv_lid) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) (_loc__1_ : Lexing.position * Lexing.position) ->
    (
# 205 "parser.mly"
      ( _1 )
# 1539 "parser.ml"
     : 'tv_ident) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 128 "parser.mly"
                                           _5
# 1544 "parser.ml"
   : 'tv_expr) (_startpos__5_ : Lexing.position) (_endpos__5_ : Lexing.position) (_startofs__5_ : int) (_endofs__5_ : int) (_loc__5_ : Lexing.position * Lexing.position) (
# 128 "parser.mly"
                                     _4
# 1548 "parser.ml"
   : unit) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_loc__4_ : Lexing.position * Lexing.position) (
# 128 "parser.mly"
                                _3
# 1552 "parser.ml"
   : 'tv_expr) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_loc__3_ : Lexing.position * Lexing.position) (
# 128 "parser.mly"
                           _2
# 1556 "parser.ml"
   : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_loc__2_ : Lexing.position * Lexing.position) (
# 128 "parser.mly"
 _1
# 1560 "parser.ml"
   : 'tv_nonempty_list_simple_pat_) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) (_loc__1_ : Lexing.position * Lexing.position) ->
    (
# 129 "parser.mly"
    ( (_1,Ewhen(_3,_5)) )
# 1565 "parser.ml"
     : 'tv_function_case) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 126 "parser.mly"
                                 _3
# 1570 "parser.ml"
   : 'tv_expr) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_loc__3_ : Lexing.position * Lexing.position) (
# 126 "parser.mly"
                           _2
# 1574 "parser.ml"
   : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_loc__2_ : Lexing.position * Lexing.position) (
# 126 "parser.mly"
 _1
# 1578 "parser.ml"
   : 'tv_nonempty_list_simple_pat_) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) (_loc__1_ : Lexing.position * Lexing.position) ->
    (
# 127 "parser.mly"
    ( (_1,_3) )
# 1583 "parser.ml"
     : 'tv_function_case) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 197 "parser.mly"
 _1
# 1588 "parser.ml"
   : 'tv_lid) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) (_loc__1_ : Lexing.position * Lexing.position) ->
    (
# 198 "parser.mly"
    ( _1 )
# 1593 "parser.ml"
     : 'tv_field) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 109 "parser.mly"
 _1
# 1598 "parser.ml"
   : 'tv_expr) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) (_loc__1_ : Lexing.position * Lexing.position) ->
    (
# 110 "parser.mly"
  ( Econstruct("::",Etuple(_1::(Econstruct_ "[]")::[])) )
# 1603 "parser.ml"
     : 'tv_expr_semi_list) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 107 "parser.mly"
                     _3
# 1608 "parser.ml"
   : 'tv_expr) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_loc__3_ : Lexing.position * Lexing.position) (
# 107 "parser.mly"
                _2
# 1612 "parser.ml"
   : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_loc__2_ : Lexing.position * Lexing.position) (
# 107 "parser.mly"
 _1
# 1616 "parser.ml"
   : 'tv_expr_semi_list) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) (_loc__1_ : Lexing.position * Lexing.position) ->
    (
# 108 "parser.mly"
  ( Econstruct("::",Etuple(_1::_2::[])) )
# 1621 "parser.ml"
     : 'tv_expr_semi_list) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 115 "parser.mly"
             _3
# 1626 "parser.ml"
   : 'tv_expr) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_loc__3_ : Lexing.position * Lexing.position) (
# 115 "parser.mly"
       _2
# 1630 "parser.ml"
   : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_loc__2_ : Lexing.position * Lexing.position) (
# 115 "parser.mly"
 _1
# 1634 "parser.ml"
   : 'tv_field) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) (_loc__1_ : Lexing.position * Lexing.position) ->
    (
# 116 "parser.mly"
  ( (_1,_3)::[] )
# 1639 "parser.ml"
     : 'tv_expr_label_list) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 113 "parser.mly"
                                  _5
# 1644 "parser.ml"
   : 'tv_expr) (_startpos__5_ : Lexing.position) (_endpos__5_ : Lexing.position) (_startofs__5_ : int) (_endofs__5_ : int) (_loc__5_ : Lexing.position * Lexing.position) (
# 113 "parser.mly"
                            _4
# 1648 "parser.ml"
   : unit) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_loc__4_ : Lexing.position * Lexing.position) (
# 113 "parser.mly"
                      _3
# 1652 "parser.ml"
   : 'tv_field) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_loc__3_ : Lexing.position * Lexing.position) (
# 113 "parser.mly"
                 _2
# 1656 "parser.ml"
   : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_loc__2_ : Lexing.position * Lexing.position) (
# 113 "parser.mly"
 _1
# 1660 "parser.ml"
   : 'tv_expr_label_list) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) (_loc__1_ : Lexing.position * Lexing.position) ->
    (
# 114 "parser.mly"
  ( (_3,_5)::_1 )
# 1665 "parser.ml"
     : 'tv_expr_label_list) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 90 "parser.mly"
       _2
# 1670 "parser.ml"
   : 'tv_expr) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_loc__2_ : Lexing.position * Lexing.position) (
# 90 "parser.mly"
 _1
# 1674 "parser.ml"
   : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) (_loc__1_ : Lexing.position * Lexing.position) ->
    (
# 90 "parser.mly"
             ( Econstruct("!",Etuple(_2::[])) )
# 1679 "parser.ml"
     : 'tv_expr) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 89 "parser.mly"
     _2
# 1684 "parser.ml"
   : 'tv_expr) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_loc__2_ : Lexing.position * Lexing.position) (
# 89 "parser.mly"
 _1
# 1688 "parser.ml"
   : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) (_loc__1_ : Lexing.position * Lexing.position) ->
    (
# 89 "parser.mly"
           ( Econstruct("ref",Etuple(_2::[])) )
# 1693 "parser.ml"
     : 'tv_expr) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 88 "parser.mly"
          _2
# 1698 "parser.ml"
   : 'tv_expr) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_loc__2_ : Lexing.position * Lexing.position) (
# 88 "parser.mly"
 _1
# 1702 "parser.ml"
   : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) (_loc__1_ : Lexing.position * Lexing.position) ->
    (
# 88 "parser.mly"
                ( Eapply(Evar("-."),_2::[]) )
# 1707 "parser.ml"
     : 'tv_expr) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 87 "parser.mly"
       _2
# 1712 "parser.ml"
   : 'tv_expr) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_loc__2_ : Lexing.position * Lexing.position) (
# 87 "parser.mly"
 _1
# 1716 "parser.ml"
   : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) (_loc__1_ : Lexing.position * Lexing.position) ->
    (
# 87 "parser.mly"
             ( Eapply(Evar("-"),_2::[]) )
# 1721 "parser.ml"
     : 'tv_expr) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 86 "parser.mly"
           _3
# 1726 "parser.ml"
   : 'tv_expr) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_loc__3_ : Lexing.position * Lexing.position) (
# 86 "parser.mly"
      _2
# 1730 "parser.ml"
   : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_loc__2_ : Lexing.position * Lexing.position) (
# 86 "parser.mly"
 _1
# 1734 "parser.ml"
   : 'tv_expr) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) (_loc__1_ : Lexing.position * Lexing.position) ->
    (
# 86 "parser.mly"
                 ( Econstruct("::",Etuple(_1::_2::[])) )
# 1739 "parser.ml"
     : 'tv_expr) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 85 "parser.mly"
            _3
# 1744 "parser.ml"
   : 'tv_expr) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_loc__3_ : Lexing.position * Lexing.position) (
# 85 "parser.mly"
      _2
# 1748 "parser.ml"
   : 'tv_binop) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_loc__2_ : Lexing.position * Lexing.position) (
# 85 "parser.mly"
 _1
# 1752 "parser.ml"
   : 'tv_expr) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) (_loc__1_ : Lexing.position * Lexing.position) ->
    (
# 85 "parser.mly"
                   ( Eapply(_2,_1::_3::[]) )
# 1757 "parser.ml"
     : 'tv_expr) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 83 "parser.mly"
                        _6
# 1762 "parser.ml"
   : 'tv_expr) (_startpos__6_ : Lexing.position) (_endpos__6_ : Lexing.position) (_startofs__6_ : int) (_endofs__6_ : int) (_loc__6_ : Lexing.position * Lexing.position) (
# 83 "parser.mly"
                   _5
# 1766 "parser.ml"
   : unit) (_startpos__5_ : Lexing.position) (_endpos__5_ : Lexing.position) (_startofs__5_ : int) (_endofs__5_ : int) (_loc__5_ : Lexing.position * Lexing.position) (
# 83 "parser.mly"
              _4
# 1770 "parser.ml"
   : 'tv_expr) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_loc__4_ : Lexing.position * Lexing.position) (
# 83 "parser.mly"
         _3
# 1774 "parser.ml"
   : unit) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_loc__3_ : Lexing.position * Lexing.position) (
# 83 "parser.mly"
    _2
# 1778 "parser.ml"
   : 'tv_expr) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_loc__2_ : Lexing.position * Lexing.position) (
# 83 "parser.mly"
 _1
# 1782 "parser.ml"
   : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) (_loc__1_ : Lexing.position * Lexing.position) ->
    (
# 84 "parser.mly"
    ( Econdition(_2,_4,_6) )
# 1787 "parser.ml"
     : 'tv_expr) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 82 "parser.mly"
           _3
# 1792 "parser.ml"
   : 'tv_expr) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_loc__3_ : Lexing.position * Lexing.position) (
# 82 "parser.mly"
      _2
# 1796 "parser.ml"
   : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_loc__2_ : Lexing.position * Lexing.position) (
# 82 "parser.mly"
 _1
# 1800 "parser.ml"
   : 'tv_expr) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) (_loc__1_ : Lexing.position * Lexing.position) ->
    (
# 82 "parser.mly"
                  ( Esequence(_1,_3) )
# 1805 "parser.ml"
     : 'tv_expr) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 80 "parser.mly"
                                                      _5
# 1810 "parser.ml"
   : 'tv_expr) (_startpos__5_ : Lexing.position) (_endpos__5_ : Lexing.position) (_startofs__5_ : int) (_endofs__5_ : int) (_loc__5_ : Lexing.position * Lexing.position) (
# 80 "parser.mly"
                                                   _4
# 1814 "parser.ml"
   : unit) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_loc__4_ : Lexing.position * Lexing.position) (
# 80 "parser.mly"
         _3
# 1818 "parser.ml"
   : 'tv_separated_nonempty_list_AND_let_rec_def_) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_loc__3_ : Lexing.position * Lexing.position) (
# 80 "parser.mly"
     _2
# 1822 "parser.ml"
   : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_loc__2_ : Lexing.position * Lexing.position) (
# 80 "parser.mly"
 _1
# 1826 "parser.ml"
   : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) (_loc__1_ : Lexing.position * Lexing.position) ->
    (
# 81 "parser.mly"
    ( Eletrec(_3,_5) )
# 1831 "parser.ml"
     : 'tv_expr) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 78 "parser.mly"
                                              _4
# 1836 "parser.ml"
   : 'tv_expr) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_loc__4_ : Lexing.position * Lexing.position) (
# 78 "parser.mly"
                                           _3
# 1840 "parser.ml"
   : unit) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_loc__3_ : Lexing.position * Lexing.position) (
# 78 "parser.mly"
     _2
# 1844 "parser.ml"
   : 'tv_separated_nonempty_list_AND_let_def_) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_loc__2_ : Lexing.position * Lexing.position) (
# 78 "parser.mly"
 _1
# 1848 "parser.ml"
   : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) (_loc__1_ : Lexing.position * Lexing.position) ->
    (
# 79 "parser.mly"
    ( Elet(_2,_4) )
# 1853 "parser.ml"
     : 'tv_expr) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 76 "parser.mly"
     _2
# 1858 "parser.ml"
   : 'tv_function_case) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_loc__2_ : Lexing.position * Lexing.position) (
# 76 "parser.mly"
 _1
# 1862 "parser.ml"
   : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) (_loc__1_ : Lexing.position * Lexing.position) ->
    (
# 77 "parser.mly"
    ( Efunction([_2]) )
# 1867 "parser.ml"
     : 'tv_expr) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 74 "parser.mly"
          _2
# 1872 "parser.ml"
   : 'tv_nonempty_list___anonymous_1_) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_loc__2_ : Lexing.position * Lexing.position) (
# 74 "parser.mly"
 _1
# 1876 "parser.ml"
   : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) (_loc__1_ : Lexing.position * Lexing.position) ->
    (
# 75 "parser.mly"
    ( Efunction(_2) )
# 1881 "parser.ml"
     : 'tv_expr) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 72 "parser.mly"
                 _4
# 1886 "parser.ml"
   : 'tv_nonempty_list___anonymous_0_) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_loc__4_ : Lexing.position * Lexing.position) (
# 72 "parser.mly"
            _3
# 1890 "parser.ml"
   : unit) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_loc__3_ : Lexing.position * Lexing.position) (
# 72 "parser.mly"
       _2
# 1894 "parser.ml"
   : 'tv_expr) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_loc__2_ : Lexing.position * Lexing.position) (
# 72 "parser.mly"
 _1
# 1898 "parser.ml"
   : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) (_loc__1_ : Lexing.position * Lexing.position) ->
    (
# 73 "parser.mly"
    ( Eapply(Efunction(_4),[_2]) )
# 1903 "parser.ml"
     : 'tv_expr) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 71 "parser.mly"
             _2
# 1908 "parser.ml"
   : 'tv_nonempty_list_simple_expr_) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_loc__2_ : Lexing.position * Lexing.position) (
# 71 "parser.mly"
 _1
# 1912 "parser.ml"
   : 'tv_simple_expr) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) (_loc__1_ : Lexing.position * Lexing.position) ->
    (
# 71 "parser.mly"
                           ( Eapply(_1,_2) )
# 1917 "parser.ml"
     : 'tv_expr) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 70 "parser.mly"
 _1
# 1922 "parser.ml"
   : 'tv_simple_expr) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) (_loc__1_ : Lexing.position * Lexing.position) ->
    (
# 70 "parser.mly"
              ( _1 )
# 1927 "parser.ml"
     : 'tv_expr) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 66 "parser.mly"
         _3
# 1932 "parser.ml"
   : 'tv_separated_nonempty_list_AND_let_rec_def_) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_loc__3_ : Lexing.position * Lexing.position) (
# 66 "parser.mly"
     _2
# 1936 "parser.ml"
   : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_loc__2_ : Lexing.position * Lexing.position) (
# 66 "parser.mly"
 _1
# 1940 "parser.ml"
   : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) (_loc__1_ : Lexing.position * Lexing.position) ->
    (
# 67 "parser.mly"
    ( Defletrec _3 )
# 1945 "parser.ml"
     : 'tv_def) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 64 "parser.mly"
     _2
# 1950 "parser.ml"
   : 'tv_separated_nonempty_list_AND_let_def_) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_loc__2_ : Lexing.position * Lexing.position) (
# 64 "parser.mly"
 _1
# 1954 "parser.ml"
   : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) (_loc__1_ : Lexing.position * Lexing.position) ->
    (
# 65 "parser.mly"
    ( Deflet _2 )
# 1959 "parser.ml"
     : 'tv_def) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 62 "parser.mly"
      _2
# 1964 "parser.ml"
   : 'tv_separated_nonempty_list_AND_ty_def_) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_loc__2_ : Lexing.position * Lexing.position) (
# 62 "parser.mly"
 _1
# 1968 "parser.ml"
   : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) (_loc__1_ : Lexing.position * Lexing.position) ->
    (
# 63 "parser.mly"
    ( Deftype _2 )
# 1973 "parser.ml"
     : 'tv_def) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 123 "parser.mly"
 _1
# 1978 "parser.ml"
   : (
# 15 "parser.mly"
       (float)
# 1982 "parser.ml"
  )) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) (_loc__1_ : Lexing.position * Lexing.position) ->
    (
# 123 "parser.mly"
        ( Econstant(Cfloat(_1)) )
# 1987 "parser.ml"
     : 'tv_const_expr) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 122 "parser.mly"
 _1
# 1992 "parser.ml"
   : (
# 14 "parser.mly"
       (bool)
# 1996 "parser.ml"
  )) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) (_loc__1_ : Lexing.position * Lexing.position) ->
    (
# 122 "parser.mly"
       ( Econstant(Cbool(_1)) )
# 2001 "parser.ml"
     : 'tv_const_expr) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 121 "parser.mly"
 _1
# 2006 "parser.ml"
   : (
# 13 "parser.mly"
       (string)
# 2010 "parser.ml"
  )) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) (_loc__1_ : Lexing.position * Lexing.position) ->
    (
# 121 "parser.mly"
         ( Econstant(Cstring(_1)) )
# 2015 "parser.ml"
     : 'tv_const_expr) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 120 "parser.mly"
 _1
# 2020 "parser.ml"
   : (
# 12 "parser.mly"
       (int)
# 2024 "parser.ml"
  )) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) (_loc__1_ : Lexing.position * Lexing.position) ->
    (
# 120 "parser.mly"
      ( Econstant(Cint(_1)) )
# 2029 "parser.ml"
     : 'tv_const_expr) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 157 "parser.mly"
           _3
# 2034 "parser.ml"
   : 'tv_separated_nonempty_list_COMMA_pat_) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_loc__3_ : Lexing.position * Lexing.position) (
# 157 "parser.mly"
     _2
# 2038 "parser.ml"
   : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_loc__2_ : Lexing.position * Lexing.position) (
# 157 "parser.mly"
 _1
# 2042 "parser.ml"
   : 'tv_pat) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) (_loc__1_ : Lexing.position * Lexing.position) ->
    (
# 158 "parser.mly"
    ( _1::_3 )
# 2047 "parser.ml"
     : 'tv_comma_pat) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 242 "parser.mly"
 _1
# 2052 "parser.ml"
   : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) (_loc__1_ : Lexing.position * Lexing.position) ->
    (
# 243 "parser.mly"
    ( "asr" )
# 2057 "parser.ml"
     : 'tv_binop) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 240 "parser.mly"
 _1
# 2062 "parser.ml"
   : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) (_loc__1_ : Lexing.position * Lexing.position) ->
    (
# 241 "parser.mly"
    ( "lsr" )
# 2067 "parser.ml"
     : 'tv_binop) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 238 "parser.mly"
 _1
# 2072 "parser.ml"
   : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) (_loc__1_ : Lexing.position * Lexing.position) ->
    (
# 239 "parser.mly"
    ( "lsl" )
# 2077 "parser.ml"
     : 'tv_binop) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 236 "parser.mly"
 _1
# 2082 "parser.ml"
   : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) (_loc__1_ : Lexing.position * Lexing.position) ->
    (
# 237 "parser.mly"
    ( "lxor" )
# 2087 "parser.ml"
     : 'tv_binop) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 234 "parser.mly"
 _1
# 2092 "parser.ml"
   : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) (_loc__1_ : Lexing.position * Lexing.position) ->
    (
# 235 "parser.mly"
    ( "lor" )
# 2097 "parser.ml"
     : 'tv_binop) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 232 "parser.mly"
 _1
# 2102 "parser.ml"
   : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) (_loc__1_ : Lexing.position * Lexing.position) ->
    (
# 233 "parser.mly"
    ( "land" )
# 2107 "parser.ml"
     : 'tv_binop) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 230 "parser.mly"
 _1
# 2112 "parser.ml"
   : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) (_loc__1_ : Lexing.position * Lexing.position) ->
    (
# 231 "parser.mly"
    ( "mod" )
# 2117 "parser.ml"
     : 'tv_binop) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 228 "parser.mly"
 _1
# 2122 "parser.ml"
   : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) (_loc__1_ : Lexing.position * Lexing.position) ->
    (
# 229 "parser.mly"
    ( "*" )
# 2127 "parser.ml"
     : 'tv_binop) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 226 "parser.mly"
 _1
# 2132 "parser.ml"
   : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) (_loc__1_ : Lexing.position * Lexing.position) ->
    (
# 227 "parser.mly"
    ( "=" )
# 2137 "parser.ml"
     : 'tv_binop) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 224 "parser.mly"
 _1
# 2142 "parser.ml"
   : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) (_loc__1_ : Lexing.position * Lexing.position) ->
    (
# 225 "parser.mly"
    ( "-" )
# 2147 "parser.ml"
     : 'tv_binop) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 222 "parser.mly"
 _1
# 2152 "parser.ml"
   : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) (_loc__1_ : Lexing.position * Lexing.position) ->
    (
# 223 "parser.mly"
    ( "-." )
# 2157 "parser.ml"
     : 'tv_binop) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 220 "parser.mly"
 _1
# 2162 "parser.ml"
   : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) (_loc__1_ : Lexing.position * Lexing.position) ->
    (
# 221 "parser.mly"
    ( "+" )
# 2167 "parser.ml"
     : 'tv_binop) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 218 "parser.mly"
 _1
# 2172 "parser.ml"
   : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) (_loc__1_ : Lexing.position * Lexing.position) ->
    (
# 219 "parser.mly"
    ( "@" )
# 2177 "parser.ml"
     : 'tv_binop) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 216 "parser.mly"
 _1
# 2182 "parser.ml"
   : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) (_loc__1_ : Lexing.position * Lexing.position) ->
    (
# 217 "parser.mly"
    ( "&&" )
# 2187 "parser.ml"
     : 'tv_binop) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 214 "parser.mly"
 _1
# 2192 "parser.ml"
   : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) (_loc__1_ : Lexing.position * Lexing.position) ->
    (
# 215 "parser.mly"
    ( "&" )
# 2197 "parser.ml"
     : 'tv_binop) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 212 "parser.mly"
 _1
# 2202 "parser.ml"
   : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) (_loc__1_ : Lexing.position * Lexing.position) ->
    (
# 213 "parser.mly"
    ( "||" )
# 2207 "parser.ml"
     : 'tv_binop) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 210 "parser.mly"
 _1
# 2212 "parser.ml"
   : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) (_loc__1_ : Lexing.position * Lexing.position) ->
    (
# 211 "parser.mly"
    ( "or" )
# 2217 "parser.ml"
     : 'tv_binop) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 262 "parser.mly"
                                       _2
# 2222 "parser.ml"
   : 'tv_sum_case) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_loc__2_ : Lexing.position * Lexing.position) (
# 262 "parser.mly"
                                    _1
# 2226 "parser.ml"
   : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) (_loc__1_ : Lexing.position * Lexing.position) ->
    (
# 262 "parser.mly"
                                                 ( _2 )
# 2231 "parser.ml"
     : 'tv___anonymous_2) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 74 "parser.mly"
                            _2
# 2236 "parser.ml"
   : 'tv_function_case) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_loc__2_ : Lexing.position * Lexing.position) (
# 74 "parser.mly"
                         _1
# 2240 "parser.ml"
   : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) (_loc__1_ : Lexing.position * Lexing.position) ->
    (
# 74 "parser.mly"
                                           ( _2 )
# 2245 "parser.ml"
     : 'tv___anonymous_1) in
  let _ = fun (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_sloc : Lexing.position * Lexing.position) (_loc : Lexing.position * Lexing.position) (
# 72 "parser.mly"
                                   _2
# 2250 "parser.ml"
   : 'tv_function_case) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_loc__2_ : Lexing.position * Lexing.position) (
# 72 "parser.mly"
                                _1
# 2254 "parser.ml"
   : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) (_loc__1_ : Lexing.position * Lexing.position) ->
    (
# 72 "parser.mly"
                                                  ( _2 )
# 2259 "parser.ml"
     : 'tv___anonymous_0) in
  ((let rec diverge() = diverge() in diverge()) : 'tv_tyname * 'tv_ty_def * 'tv_ty * 'tv_tuple_ty * 'tv_top * 'tv_sum_case * 'tv_simple_ty * 'tv_simple_pat * 'tv_simple_expr * 'tv_separated_pair_field_EQUAL_pat_ * 'tv_separated_pair_field_COLON_ty_ * 'tv_separated_nonempty_list_STAR_simple_ty_ * 'tv_separated_nonempty_list_SEMI_separated_pair_field_EQUAL_pat__ * 'tv_separated_nonempty_list_SEMI_separated_pair_field_COLON_ty__ * 'tv_separated_nonempty_list_COMMA_ty_ * 'tv_separated_nonempty_list_COMMA_pat_ * 'tv_separated_nonempty_list_COMMA_param_ * 'tv_separated_nonempty_list_COMMA_expr_ * 'tv_separated_nonempty_list_AND_ty_def_ * 'tv_separated_nonempty_list_AND_let_rec_def_ * 'tv_separated_nonempty_list_AND_let_def_ * 'tv_pat_semi_list * 'tv_pat * 'tv_params * 'tv_param * 'tv_nonempty_list_simple_pat_ * 'tv_nonempty_list_simple_expr_ * 'tv_nonempty_list___anonymous_2_ * 'tv_nonempty_list___anonymous_1_ * 'tv_nonempty_list___anonymous_0_ * 'tv_lid * 'tv_let_rec_def * 'tv_let_def * 'tv_ident * 'tv_function_case * 'tv_field * 'tv_expr_semi_list * 'tv_expr_label_list * 'tv_expr * 'tv_def * 'tv_const_expr * 'tv_comma_pat * 'tv_binop * 'tv___anonymous_2 * 'tv___anonymous_1 * 'tv___anonymous_0)

and menhir_end_marker =
  0

# 298 "parser.mly"
  

# 2269 "parser.ml"
