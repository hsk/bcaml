type constant =
| Cint of int
| Cbool of bool
| Cfloat of float
| Cstring of string
| Cchar of char
[@@deriving show]

type buildin =
| BAddint
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
| Ebuildin of buildin
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