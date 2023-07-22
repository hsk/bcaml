open Syntax

let curr_id = ref 0

let gen_id () =
  let ret = !curr_id in
  incr curr_id;
  ret

let rec type_repr ty =
  match ty with
  | Tvar {contents=Unbound _} -> ty
  | Tvar {contents=Linkto t1 } ->
    let t2 = type_repr t1 in
    Tvar {contents=Linkto t2 } 
  | _ -> ty

let new_type_var level =
  Tvar (ref (Unbound {id=Idint (gen_id ());level=level}))

let rec new_type_var_list n level =
  if n <= 0 then []
  else new_type_var level :: new_type_var_list (n - 1) level

let rec get_type_level ty =
  let ty = type_repr ty in
  match ty with
  | Tvar {contents=Unbound{id=_;level=level}} -> level
  | Tvar {contents=Linkto ty} -> get_type_level ty
  | Tunit | Tbool | Tint | Tfloat | Tchar |Tstring -> notgeneric
  | Tlist ty | Tref ty -> get_type_level ty
  | Tarrow(arg,ret) -> min (get_type_level arg) (get_type_level ret)
  | Ttuple [] | Tconstr(_,[]) | Trecord(_,[]) | Tvariant(_,[]) ->
    notgeneric
  | Ttuple tyl | Tconstr(_,tyl) | Trecord(_,tyl) | Tvariant(_,tyl) ->
    get_type_level_list tyl 

and get_type_level_list = function
| [] -> failwith "get_type_level_list"
| [ty] -> get_type_level ty
| ty::rest ->
  let lv1 = get_type_level ty in
  let lv2 = get_type_level_list rest in
  min lv1 lv2


let free_type_vars level ty =
  let fv = ref [] in
  let rec free_vars ty =
    let ty = type_repr ty in
    match ty with
    | Tvar _ ->
      if get_type_level ty >= level then fv := ty :: !fv
    | Tlist ty | Tref ty -> free_vars ty
    | Tarrow(arg,ret) -> free_vars arg; free_vars ret
    | Ttuple tyl | Tconstr(_,tyl) | Trecord(_,tyl) | Tvariant(_,tyl) ->
      List.iter free_vars tyl
    | _ -> ()
  in free_vars ty;
  !fv

let rec gen_type level ty =
  let ty = type_repr ty in
  match ty with
  | Tvar link ->
    begin match link with
    | {contents=Unbound{id=id;level=level'}} 
      when level' > level ->
      link := (Unbound {id=id;level=generic})
    | {contents=Linkto ty} -> gen_type level ty
    | _ -> ()
    end
  | Tlist ty | Tref ty -> gen_type level ty
  | Tarrow(arg,ret) -> gen_type level arg; gen_type level ret
  | Ttuple tyl | Tconstr(_,tyl) | Trecord(_,tyl) | Tvariant(_,tyl) ->
    List.iter (gen_type level) tyl
  | _ -> ()

let rec nongen_type level ty =
  let ty = type_repr ty in
  match ty with
  | Tvar link ->
    begin match link with
    | {contents=Unbound{id=id;level=level'}} 
      when level' > level ->
      link := (Unbound {id=id;level=level})
    | {contents=Linkto ty} -> nongen_type level ty
    | _ -> ()
    end
  | Tlist ty | Tref ty -> nongen_type level ty
  | Tarrow(arg,ret) -> nongen_type level arg; nongen_type level ret
  | Ttuple tyl | Tconstr(_,tyl) | Trecord(_,tyl) | Tvariant(_,tyl) ->
    List.iter (nongen_type level) tyl
  | _ -> ()