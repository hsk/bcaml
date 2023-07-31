open Syntax
open Typing
open Globals

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

type status = 
| Checking
| Checked

let name_is_checking name seen =
  if List.mem_assoc name seen then
    !(List.assoc name seen) = Checking
  else 
    false

let name_is_checked name seen =
  if List.mem_assoc name seen then
    !(List.assoc name seen) = Checked
  else 
    false


let rec is_abbrev name = function
| Dabbrev(name',_,_)::_ when name = name' ->
  true
| _::rest ->
  is_abbrev name rest
| [] ->
  false

let rec abbrev_found_in_ty decl seen = function
| Tlist t -> abbrev_found_in_ty decl seen t
| Tref t ->  abbrev_found_in_ty decl seen t
| Tarrow(arg,ret) -> abbrev_found_in_ty decl seen arg; abbrev_found_in_ty decl seen ret
| Ttuple tyl -> List.iter (abbrev_found_in_ty decl seen) tyl
| Tconstr(name,_) when name_is_checking name seen -> 
  failwith "recursive type abbreviation"
| Tconstr(name,tyl) when name_is_checked name seen -> 
  List.iter (abbrev_found_in_ty decl seen) tyl
| Tconstr(name,tyl) when is_abbrev name decl ->
  abbrev_found_in_decl name seen decl;
  List.iter (abbrev_found_in_ty decl seen) tyl
| _ -> ()

and abbrev_found_in_decl name seen decl = 
  let rec aux = function
  | Dabbrev(n,_,ty)::_ when n = name ->
    let pair = (name,ref Checking) in
    abbrev_found_in_ty decl (pair::seen) ty;
    snd pair := Checked
  | _::rest ->
    aux rest
  | [] ->
    failwith "name not found abbrev_found_in_decl"
  in aux decl

let check_recursive_abbrev decl = 
  let rec aux = function 
  | Dabbrev(name,_,_)::rest -> 
    abbrev_found_in_decl name [] decl;
    aux rest
  | _::rest ->
    aux rest
  | [] ->
    ()
  in aux decl

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
| Tlist t -> def_found_in_ty decl seen t
| Tarrow(arg,ret) -> def_found_in_ty decl seen arg; def_found_in_ty decl seen ret
| Ttuple tyl -> List.iter (def_found_in_ty decl seen) tyl
| Trecord(name,_) when name_is_checking name seen -> 
  failwith "recursive type abbreviation"
| Trecord(name,fields) when name_is_checked name seen -> 
  List.iter (def_found_in_ty decl seen) (List.map snd fields)
| Trecord(name,fields) when is_def name decl ->
  def_found_in_decl name seen decl;
  List.iter (abbrev_found_in_ty decl seen) (List.map snd fields)
| Tvariant(name,_) when name_is_checking name seen -> 
  failwith "recursive type abbreviation"
| Tvariant(name,fields) when name_is_checked name seen -> 
  List.iter (def_found_in_ty decl seen) (List.map snd fields)
| Tvariant(name,fields) when is_def name decl ->
  def_found_in_decl name seen decl;
  List.iter (abbrev_found_in_ty decl seen) (List.map snd fields)
| _ -> ()

and def_found_in_decl name seen decl = 
  let rec aux = function
  | Drecord(n,_,fields)::_ when n = name ->
    let pair = (name,ref Checking) in
    List.iter (fun t->def_found_in_ty decl (pair::seen) (convert_constr t)) (List.map snd fields);
    snd pair := Checked
  | Dvariant(n,_,fields)::_ when n = name ->
    let pair = (name,ref Checking) in
    List.iter (fun t->def_found_in_ty decl (pair::seen) (convert_constr t)) (List.map snd fields);
    snd pair := Checked
  | _::rest ->
    aux rest
  | [] ->
    failwith "name not found def_found_in_decl"
  in aux decl

let check_recursive_def decl = 
  let rec aux = function 
  | Drecord(name,_,_)::rest -> 
    def_found_in_decl name [] decl;
    aux rest
  | Dvariant(name,_,_)::rest -> 
    def_found_in_decl name [] decl;
    aux rest 
  | _::rest ->
    aux rest
  | [] ->
    ()
  in aux decl

let rec check_ast = function
| Deftype decl::rest ->
  push_tydecl decl;
  check_recursive_abbrev decl;
  check_recursive_def decl;
  check_ast rest
| Defexpr expr::rest ->
  let ty = type_expr (get_tyenv ()) 0 expr in
  print_endline (show_ty ty);
  check_ast rest
| _::rest ->
  check_ast rest
| [] ->
  ()
