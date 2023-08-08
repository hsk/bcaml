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
| Trecord of string * ty list * (string * ty) list
| Tvariant of string * ty list * (string * ty) list
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
| Efix of pat * expr
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

and matches =
(pat * expr) list
[@@deriving show]

and def_list = def list
[@@deriving show]

type tyenv = (string * ty) list
[@@deriving show]

let int_to_alpha i =
  if i < 26 then Printf.sprintf "%c" (Char.chr (i+97))
  else Printf.sprintf "%c%d" (Char.chr ((i mod 26)+97)) (i/26)

let tvars_counter = ref 0
let tvars_names = ref []

let reset_tvar_name () =
  tvars_counter := 0; tvars_names := []

let name_of_tvar tvar =
  try
    List.assoc tvar !tvars_names
  with Not_found ->
    let name = int_to_alpha !tvars_counter in
    let varname = name in
    incr tvars_counter;
    tvars_names := (tvar,varname)::!tvars_names;
    varname

let rec pp_ty = function
| Tvar{contents=Unbound {id=id;level=_}} -> "'" ^ name_of_tvar id
| Tvar{contents=Linkto ty} -> pp_ty ty
| Tunit -> "unit"
| Tbool -> "bool"
| Tint  -> "int"
| Tfloat -> "float"
| Tchar -> "char"
| Tstring -> "string"
| Tlist ty -> (pp_ty ty) ^ " list"
| Tref ty -> (pp_ty ty) ^ " ref"
| Tarrow(l,r) -> "(" ^ (pp_ty l) ^ "->" ^ (pp_ty r) ^ ")"
| Ttuple(x::xl) -> "(" ^ (pp_ty x) ^ (List.fold_left (fun s x -> s ^ " * " ^ (pp_ty x)) "" xl) ^ ") "
| Tconstr(name, []) -> name
| Tconstr(name, x::[]) -> (pp_ty x) ^ " " ^ name
| Tconstr(name, x::xl) -> "(" ^ (pp_ty x) ^ (List.fold_left (fun s x -> s ^ "," ^ (pp_ty x)) "" xl) ^ ") " ^ name
| Trecord(name,[],_) -> name
| Trecord(name,x::[],_) -> (pp_ty x) ^ " " ^ name
| Trecord(name,x::xl,_) -> "(" ^ (pp_ty x) ^ (List.fold_left (fun s x -> s ^ "," ^ (pp_ty x)) "" xl) ^ ") " ^ name
| Tvariant(name,[],_) -> name
| Tvariant(name,x::[],_) -> (pp_ty x) ^ " " ^ name
| Tvariant(name,x::xl,_) -> "(" ^ (pp_ty x) ^ (List.fold_left (fun s x -> s ^ "," ^ (pp_ty x)) "" xl) ^ ") " ^ name
| ty -> failwith (Printf.sprintf "pp_ty %s" (show_ty ty))

let pp_tydecl = function
| Drecord(n,[],(name,ty)::[]) -> 
  "type " ^ n ^ " = {" ^ name ^ " = " ^ pp_ty ty ^ "}"
| Drecord(n,x::[],(name,ty)::[]) -> 
  "type " ^ pp_ty x ^ " " ^ n ^ " = {" ^ name ^ " = " ^ pp_ty ty ^ "}"
| Drecord(n,x::xl,(name,ty)::[]) -> 
  let pp_x = pp_ty x in
  "type " ^ "(" ^ pp_x ^ List.fold_left (fun s x-> s ^ "," ^ pp_ty x) "" xl ^ ")" ^ " " ^ n ^ " = {" ^ name ^ " = " ^ pp_ty ty ^ "}"
| Drecord(n,[],(name,ty)::tl) -> 
  let rec pp_fields = function
  | [] -> ""
  | (name,ty)::xl -> "; " ^ name ^ " = " ^ pp_ty ty ^ pp_fields xl
  in "type " ^ n ^ " = {" ^ name ^ " = " ^ pp_ty ty ^ "; " ^ pp_fields tl ^ "}"
| Drecord(n,x::[],(name,ty)::tl) -> 
  let rec pp_fields = function
  | [] -> ""
  | (name,ty)::xl -> "; " ^ name ^ " = " ^ pp_ty ty ^ pp_fields xl
  in "type " ^ pp_ty x ^ " " ^ n ^ " = {" ^ name ^ " = " ^ pp_ty ty ^ "; " ^ pp_fields tl ^ "}"
| Drecord(n,x::xl,(name,ty)::tl) -> 
  let rec pp_fields = function
  | [] -> ""
  | (name,ty)::xl -> "; " ^ name ^ " = " ^ pp_ty ty ^ pp_fields xl
  in 
  let pp_x = pp_ty x in
  "type " ^ "(" ^ pp_x ^ List.fold_left (fun s x-> s ^ "," ^ pp_ty x) "" xl ^ ")" ^ " " ^ n ^ " = {" ^ name ^ " = " ^ pp_ty ty ^ "; " ^ pp_fields tl ^ "}"

| Dvariant(n,[],(name,Ttag)::[]) -> 
  "type " ^ n ^ " = | " ^ name
| Dvariant(n,x::[],(name,Ttag)::[]) -> 
  "type " ^ pp_ty x ^ " " ^ n ^ " = | " ^ name
| Dvariant(n,x::xl,(name,Ttag)::[]) -> 
  let pp_x = pp_ty x in
  "type " ^ "(" ^ pp_x ^ List.fold_left (fun s x-> s ^ "," ^ pp_ty x) "" xl ^ ")" ^ " " ^ n ^ " = | " ^ name
| Dvariant(n,[],(name,Ttag)::tl) -> 
  let rec pp_fields = function
  | [] -> ""
  | (name,Ttag)::xl -> " | " ^ name ^ pp_fields xl
  | (name,ty)::xl -> " | " ^ name ^ " of " ^ pp_ty ty ^ pp_fields xl
  in "type " ^ n ^ " = | " ^ name ^ pp_fields tl
| Dvariant(n,x::[],(name,Ttag)::tl) -> 
  let rec pp_fields = function
  | [] -> ""
  | (name,Ttag)::xl -> " | " ^ name ^ pp_fields xl
  | (name,ty)::xl -> " | " ^ name ^ " of " ^ pp_ty ty ^ pp_fields xl
  in "type " ^ pp_ty x ^ " " ^ n ^ " = | " ^ name ^ pp_fields tl
| Dvariant(n,x::xl,(name,Ttag)::tl) -> 
  let rec pp_fields = function
  | [] -> ""
  | (name,Ttag)::xl -> " | " ^ name ^ pp_fields xl
  | (name,ty)::xl -> " | " ^ name ^ " of " ^ pp_ty ty ^ pp_fields xl
  in 
  let pp_x = pp_ty x in
  "type " ^ "(" ^ pp_x ^List.fold_left (fun s x-> s ^ "," ^ pp_ty x) "" xl  ^ ")" ^ " " ^ n ^ " = | " ^ name ^ pp_fields tl

| Dvariant(n,[],(name,ty)::[]) -> 
  "type " ^ name ^ " = | " ^ n ^ " of " ^ pp_ty ty
| Dvariant(n,x::[],(name,ty)::[]) -> 
  "type " ^ pp_ty x ^ " " ^ n ^ " = | " ^ name ^ " of " ^ pp_ty ty
| Dvariant(n,x::xl,(name,ty)::[]) -> 
  let pp_x = pp_ty x in
  "type " ^ "(" ^ pp_x ^ List.fold_left (fun s x-> s ^ "," ^ pp_ty x) "" xl ^ ")" ^ " " ^ n ^ " = | " ^ name ^ " of " ^ pp_ty ty
| Dvariant(n,[],(name,ty)::tl) -> 
  let rec pp_fields = function
  | [] -> ""
  | (name,Ttag)::xl -> " | " ^ name ^ pp_fields xl
  | (name,ty)::xl -> " | " ^ name ^ " of " ^ pp_ty ty ^ pp_fields xl
  in "type " ^ n ^ " = | " ^ name ^ " of " ^ pp_ty ty ^ pp_fields tl
| Dvariant(n,x::[],(name,ty)::tl) -> 
  let rec pp_fields = function
  | [] -> ""
  | (name,Ttag)::xl -> " | " ^ name ^ pp_fields xl
  | (name,ty)::xl -> " | " ^ name ^ " of " ^ pp_ty ty ^ pp_fields xl
  in "type " ^ pp_ty x ^ " " ^ n ^ " = | " ^ name ^ " of " ^ pp_ty ty ^ pp_fields tl
| Dvariant(n,x::xl,(name,ty)::tl) -> 
  let rec pp_fields = function
  | [] -> ""
  | (name,Ttag)::xl -> " | " ^ name ^ pp_fields xl
  | (name,ty)::xl -> " | " ^ name ^ " of " ^ pp_ty ty ^ pp_fields xl
  in 
  let pp_x = pp_ty x in  
  "type " ^ "(" ^ pp_x ^List.fold_left (fun s x-> s ^ "," ^ pp_ty x) "" xl  ^ ")" ^ " " ^ n ^ " = | " ^ name ^ " of " ^ pp_ty ty ^ pp_fields tl
| Dabbrev(n,[],ty) -> "type " ^ n ^ " = " ^ pp_ty ty 
| Dabbrev(n,x::[],ty) -> "type " ^ pp_ty x ^ " " ^ n ^ " = " ^ pp_ty ty 
| Dabbrev(n,x::xl,ty) -> 
  let pp_x = pp_ty x in
  "type " ^ "(" ^ pp_x ^ List.fold_left (fun s x-> s ^ "," ^ pp_ty x) "" xl ^ ")" ^ " " ^ n ^ " = " ^ pp_ty ty 
| _ -> failwith "pp_tydecl"

let pp_tydecls decls = 
  let ret = List.fold_left (fun s decl -> s ^ "\n" ^ pp_tydecl decl) "" decls in
  reset_tvar_name ();
  ret

let pp_cst = function
| Cint i -> string_of_int i
| Cbool b -> string_of_bool b 
| Cfloat f -> string_of_float f 
| Cchar c -> Printf.sprintf "'%C'" c
| Cstring s -> Printf.sprintf "\"%s\"" s

let rec pp_exp = function
| Econstant cst -> pp_cst cst
| Eprim _ -> "<fun>"
| Etuple(x::xl) -> "(" ^ (pp_exp x) ^ (List.fold_left (fun s x -> s ^ ", " ^ (pp_exp x)) "" xl) ^ ")"
| Elist [] -> "[]"
| Elist(x::[]) -> "[" ^ (pp_exp x) ^ "]"
| Elist(x::xl) -> "[" ^ (pp_exp x) ^ (List.fold_left (fun s x -> s ^ "; " ^ (pp_exp x)) "" xl) ^ "]"
| Eloc _ -> "<ref>"
| Eunit -> "()"
| Econstruct(name,Etag) -> name
| Econstruct(name,expr) -> name ^ " " ^ (pp_exp expr) 
| Efix _ -> "<fun>"
| Efunction _ -> "<fun>"
| Erecord((n,x)::[]) -> "{" ^ n ^ "=" ^ (pp_exp x) ^ "}"
| Erecord((n,x)::xl) -> "{" ^ n ^ "=" ^ (pp_exp x) ^ (List.fold_left (fun s (n,x) -> s ^ "; " ^ n ^ "=" ^ (pp_exp x)) "" xl) ^ "}"
| _ -> failwith "pp_exp"
 
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

let do_int_to_float op = function
| Econstant(Cint i) -> Econstant(Cfloat(op i))
| _ -> failwith "do_int_to_float"

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

let do_float_to_int op = function
| Econstant(Cfloat f) -> Econstant(Cint(op f))
| _ -> failwith "do_float_to_int"

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