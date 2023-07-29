open Syntax
open Typing

let rec check_valid_ty tyl = function
| Tvar {contents=Unbound{id=id;level=_}} -> List.exists (occursin id) tyl
| Tvar {contents=Linkto t} -> check_valid_ty tyl t
| Tlist t -> check_valid_ty tyl t
| Tref t -> check_valid_ty tyl t
| Tarrow(arg,ret) -> check_valid_ty tyl arg && check_valid_ty tyl ret
| Ttuple tyl' -> List.for_all (fun t->check_valid_ty tyl t) tyl'
| Tconstr(_,tyl') -> List.for_all (fun t->check_valid_ty tyl t) tyl'
| Trecord(_,fields) ->
    check_valid_fields tyl fields
| Tvariant(_,fields) -> 
    check_valid_fields tyl fields
| _ -> true

and check_valid_fields tyl fields =
  List.for_all (fun (_,t)-> check_valid_ty tyl t) fields

let rec is_abbrev name = function
| Dabbrev(name',_,_)::_ when name = name' ->
  true
| _::rest ->
  is_abbrev name rest
| [] ->
  false

let rec abbrev_found_in_ty decl seen = function
| Tvar _ -> seen
| Tlist t -> abbrev_found_in_ty decl seen t
| Tref t ->  abbrev_found_in_ty decl seen t
| Tarrow(arg,ret) -> abbrev_found_in_ty decl (abbrev_found_in_ty decl seen arg) ret
| Ttuple tyl -> List.fold_left (abbrev_found_in_ty decl) seen tyl
| Tconstr(name,tyl) when is_abbrev name decl -> name::List.fold_left (abbrev_found_in_ty decl) seen tyl
| Trecord(_,fields) ->
    List.fold_left (abbrev_found_in_ty decl) seen (List.map snd fields)
| Tvariant(_,fields) -> 
    List.fold_left (abbrev_found_in_ty decl) seen (List.map snd fields)
| _ -> seen


let check_recursive_abbrev lhs rhs decl = 
  let rec aux lhs rhs = function
  | Dabbrev(name,_,ty)::rest ->
    aux (name::lhs) (abbrev_found_in_ty decl rhs ty) rest
  | _::rest ->
    aux lhs rhs rest
  | [] ->
    List.exists (fun e -> List.mem e rhs) lhs
  in aux lhs rhs decl

let rec is_def name = function
| Drecord(name',_,_)::_ when name = name' ->
  true
| Dvariant(name',_,_)::_ when name = name' ->
  true
| _::rest ->
  is_def name rest
| [] ->
  false

let rec def_found_in_ty decl seen = function
| Tvar _ -> seen
| Tlist t -> def_found_in_ty decl seen t
| Tarrow(arg,ret) -> def_found_in_ty decl (def_found_in_ty decl seen arg) ret
| Ttuple tyl -> List.fold_left (def_found_in_ty decl) seen tyl
| Trecord(name,fields) when is_def name decl ->
    name::List.fold_left (def_found_in_ty decl) seen (List.map snd fields)
| Tvariant(name,fields) when is_def name decl -> 
    name::List.fold_left (def_found_in_ty decl) seen (List.map snd fields)
| _ -> seen

let check_recursive_def lhs rhs decl = 
  let rec aux lhs rhs = function
  | Drecord(name,_,fields)::rest ->
    aux (name::lhs) (List.fold_left (def_found_in_ty decl) rhs (List.map snd fields)) rest
  | Dvariant(name,_,fields)::rest ->
    aux (name::lhs) (List.fold_left (def_found_in_ty decl) rhs (List.map snd fields)) rest
  | _::rest ->
    aux lhs rhs rest
  | [] ->
    List.exists (fun e -> List.mem e rhs) lhs
  in aux lhs rhs decl