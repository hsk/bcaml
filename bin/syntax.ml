
let generic = -1
let notgeneric = 0

type pos = (int * int)

type 'a loc = {info:'a; loc:(pos *pos)}

type tyvar = {id:int; level:int ref}

type constant =
| Cint of int
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
| Trecord of string * ty list
| Tvariant of string * ty list
| Tabbrev of string * ty list
| Tabstract of string

and expr' = {e_desc: expr_desc; e_ty: ty ref}

and expr = expr' loc

and expr_desc =
| Elocal of string
| Eglobal of string
| Econstant of constant
| Etuple of expr list
| Econstruct of string * expr option
| Eapply of expr * expr list
| Elet of bool * (pat * expr) list * expr
| Efunction of (pat list * expr) list
| Etrywith of expr * (pat * expr) list
| Esequence of expr * expr
| Econdition of expr * expr * expr
| Ewhile of expr * expr
| Efor of string * expr * expr * bool * expr
| Econstraint of expr * ty
| Eassign of string * expr
| Erecord of (string * expr) list
| Erecord_access of expr * string
| Erecord_update of expr * string * expr
| Ewhen of expr * expr

and pat' = {p_desc: pat_desc; p_ty: ty ref}

and pat = pat' loc

and pat_desc =
| Pwild
| Pvar of string
| Palias of pat * string
| Pconstant of constant
| Ptuple of pat list
| Pconstruct of string * pat option
| Por of pat * pat
| Pconstraint of pat * ty
| Precord of (string * pat) list

type value =
| Vbuildin of buildin
| Vconst of constant 
| Vclosure of (pat * expr) list
| Vtuple of value list
| Vconstruct of string * value option
| Vrecord of (string * value) list

type type_decl =
| Drecord of string * tyvar list * (string * ty) list
| Dvariant of string * tyvar list * (string * ty) list
| Dabbrev of string * tyvar list * ty
| Dabstract of string * ty option

and impl_phrase = impl_desc loc

and impl_desc =
| Imexpr of expr
| Imletdef of bool * (pat * expr) list
| Imtypedef of type_decl list
| Imexcdef of string * ty option

