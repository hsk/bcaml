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

let type_instance level ty =
  let ty = type_repr ty in
  let ty_lv = get_type_level ty in
  let id_var_hash = Hashtbl.create 10 in
  let rec f ty =
    match ty with
    | Tvar link ->
      begin match link with
      | {contents=Unbound{id=id;level=level'}} when level' = generic ->
        (
          try 
            Hashtbl.find id_var_hash id
          with Not_found ->
            let tvar = Tvar(ref (Linkto(new_type_var level))) in
            Hashtbl.add id_var_hash id tvar;
            tvar
        )  
      | {contents=Linkto ty} -> f ty
      | _ -> ty
      end
    | Tlist ty when ty_lv = generic -> Tlist (f ty)
    | Tref ty when ty_lv = generic -> Tref (f ty)
    | Tarrow(arg,ret)
      when ty_lv = generic -> Tarrow(f arg, f ret)
    | Ttuple tyl when ty_lv = generic -> Ttuple(List.map f tyl)
    | Tconstr(name,tyl) when ty_lv = generic -> Tconstr(name,List.map f tyl)
    | Trecord(name,tyl) when ty_lv = generic -> Trecord(name,List.map f tyl)
    | Tvariant(name,tyl) when ty_lv = generic -> Tvariant(name,List.map f tyl)
    | _ -> ty
  in f ty