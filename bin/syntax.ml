open Prims

type constant =
| Cint of int
| Cbool of bool
| Cfloat of float
| Cstring of string
| Cchar of char
[@@deriving show]

let generic = -1
let notgeneric = 0

type id_kind =
| Idint of int
| Idstr of string
[@@deriving show]

type tyvar = {id:id_kind; level:int}
[@@deriving show]

type link =
| Unbound of tyvar
| Linkto of ty
[@@deriving show]

and ty =
| Tvar of link ref
| Tunit
| Tbool
| Tint 
| Tfloat
| Tchar
| Tstring
| Tlist of ty
| Tref of ty
| Tarrow of ty * ty
| Ttuple of ty list
| Tconstr of string * ty list
| Trecord of string * (string * ty) list
| Tvariant of string * (string * ty) list
| Ttag
[@@deriving show]

and expr =
| Evar of string
| Econstant of constant
| Eprim of prim
| Etuple of expr list
| Enil
| Econs of expr * expr
| Elist of expr list
| Eref of expr
| Ederef of expr
| Eassign of expr * expr
| Eloc of int
| Etag
| Eunit
| Econstruct of string * expr
| Eapply of expr * expr list
| Elet of (pat * expr) list * expr
| Eletrec of (pat * expr) list * expr
| Efunction of (pat * expr) list
| Esequence of expr * expr
| Econdition of expr * expr * expr
| Econstraint of expr * ty
| Erecord of (string * expr) list
| Erecord_access of expr * string
| Ewhen of expr * expr
[@@deriving show]

and pat =
| Pwild
| Pvar of string
| Pparams of pat list
| Palias of pat * string
| Pconstant of constant
| Ptuple of pat list
| Pnil 
| Pcons of pat * pat
| Pref of pat
| Punit
| Ptag
| Pconstruct of string * pat
| Por of pat * pat
| Pconstraint of pat * ty
| Precord of (string * pat) list
[@@deriving show]

type type_decl =
| Drecord of string * ty list * (string * ty) list
| Dvariant of string * ty list * (string * ty) list
| Dabbrev of string * ty list * ty
[@@deriving show]


and def =
| Defexpr of expr
| Deflet of (pat * expr) list
| Defletrec of (pat * expr) list
| Deftype of type_decl list
[@@deriving show]

and def_list = def list
[@@deriving show]

type tyenv = (string * ty) list
[@@deriving show]

let get_constant = function
| Econstant cst -> cst
| _ -> failwith "get_constant"

let get_int = function
| Cint i -> i
| _ -> failwith "get_int"

let get_bool = function
| Cbool b -> b
| _ -> failwith "get_bool"

let get_float = function
| Cfloat f -> f
| _ -> failwith "get_float"

let get_string = function
| Cstring s -> s
| _ -> failwith "get_string"

let get_char = function
| Cchar c ->  c
| _ -> failwith "get_char"

let do_int op = function
| Econstant(Cint i) -> Econstant(Cint(op i))
| _ -> failwith "do_int"

let do_int_to_char op = function
| Econstant(Cint i) -> Econstant(Cchar(op i))
| _ -> failwith "do_int_to_char"

let do_int_to_string op = function
| Econstant(Cint i) -> Econstant(Cstring(op i))
| _ -> failwith "do_int_to_char"

let do_bool op = function
| Econstant(Cbool b) -> Econstant(Cbool(op b))
| _ -> failwith "do_bool"

let do_bool_to_string op = function
| Econstant(Cbool b) -> Econstant(Cstring(op b))
| _ -> failwith "do_bool_to_string"

let do_float op = function
| Econstant(Cfloat f) -> Econstant(Cfloat(op f))
| _ -> failwith "do_float"

let do_float_to_string op = function
| Econstant(Cfloat f) -> Econstant(Cstring(op f))
| _ -> failwith "do_float"

let do_string op = function
| Econstant(Cstring s) -> Econstant(Cstring(op s))
| _ -> failwith "do_string"

let do_string_to_bool op = function
| Econstant(Cstring s) -> Econstant(Cbool(op s))
| _ -> failwith "do_string_to_bool"

let do_string_to_int op = function
| Econstant(Cstring s) -> Econstant(Cint(op s))
| _ -> failwith "do_string_to_int"

let do_string_to_float op = function
| Econstant(Cstring s) -> Econstant(Cfloat(op s))
| _ -> failwith "do_string_to_float"

let do_char op = function
| Econstant(Cchar c) -> Econstant(Cchar(op c))
| _ -> failwith "do_char"

let do_char_to_int op = function
| Econstant(Cchar c) -> Econstant(Cint(op c))
| _ -> failwith "do_char_to_int"


let do_int_bin op x y =
  let ret =
  match get_constant x, get_constant y with
  | Cint x, Cint y -> Cint(op x y)
  | _ -> failwith "do_int_bin"
  in Econstant ret

let do_bool_bin op x y =
  let ret =
  match get_constant x, get_constant y with
  | Cbool x, Cbool y -> Cbool(op x y)
  | _ -> failwith "do_bool_bin"
  in Econstant ret

let do_float_bin op x y =
  let ret =
  match get_constant x, get_constant y with
  | Cfloat x, Cfloat y -> Cfloat(op x y)
  | _ -> failwith "do_float_bin"
  in Econstant ret

let do_string_bin op x y =
  let ret =
  match get_constant x, get_constant y with
  | Cstring x, Cstring y -> Cstring(op x y)
  | _ -> failwith "do_string_bin"
  in Econstant ret

let do_char_bin op x y =
  let ret =
  match get_constant x, get_constant y with
  | Cchar x, Cchar y -> Cchar(op x y)
  | _ -> failwith "do_char_bin"
  in Econstant ret