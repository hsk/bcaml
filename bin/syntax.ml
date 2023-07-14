
let generic = -1
let notgeneric = 0


type tyvar = {id:string; level:int ref}

type constant =
| Cint of int
| Cbool of bool
| Cfloat of float
| Cstring of string
| Cchar of char

type ty =
| Tvar of tyvar
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
| Trecord of string * ty list
| Tvariant of string * ty list
| Tabbrev of string * ty list



and expr =
| Evar of string
| Econstant of constant
| Ebuildin of buildin
| Etuple of expr list
| Elist of expr list
| Econstruct_ of string
| Econstruct of string * expr
| Eapply of expr * expr list
| Elet of (pat * expr) list * expr
| Eletrec of (pat * expr) list * expr
| Efunction of (pat * expr) list
| Etrywith of expr * (pat * expr) list
| Esequence of expr * expr
| Econdition of expr * expr * expr
| Econstraint of expr * ty
| Eassign of string * expr
| Erecord of (string * expr) list
| Erecord_access of expr * string
| Erecord_update of expr * string * expr
| Ewhen of expr * expr

and pat =
| Pwild
| Pvar of string
| Pparams of pat list
| Palias of pat * string
| Pconstant of constant
| Ptuple of pat list
| Pconstruct_ of string
| Pconstruct of string * pat
| Por of pat * pat
| Pconstraint of pat * ty
| Precord of (string * pat) list

type type_decl =
| Drecord of string * tyvar list * (string * ty) list
| Dvariant of string * tyvar list * tag list
| Dabbrev of string * tyvar list * ty

type tag =
| Gconstruct_ of string
| Gconstruct of string * ty

and def =
| Defexpr of expr
| Deflet of (pat * expr) list
| Defletrec of (pat * expr) list
| Deftype of type_decl list
| Defexc of string * ty option

