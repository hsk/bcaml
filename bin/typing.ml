open Syntax

let curr_id = ref 0

let gen_id () =
  let ret = !curr_id in
  incr curr_id;
  ret

let rec type_repr ty =
  match ty with
  | Tvar {contents=Unbound _} -> ty
  | Tvar ({contents=Linkto t1} as link) ->
    let t2 = type_repr t1 in
    link := Linkto t2;
    t2 
  | _ -> ty

let new_type_var level =
  Tvar (ref (Unbound {id=Idint (gen_id ());level=level}))

let rec get_type_level level ty =
  let ty = type_repr ty in
  match ty with
  | Tvar {contents=Unbound{id=_;level=level}} -> level
  | Tvar {contents=Linkto ty} -> get_type_level level ty
  | Tunit | Tbool | Tint | Tfloat | Tchar |Tstring -> level
  | Tlist ty | Tref ty -> get_type_level level ty
  | Tarrow(arg,ret) -> min (get_type_level notgeneric arg) (get_type_level notgeneric ret)
  | Ttuple [] | Tconstr(_,[]) | Trecord(_,[],_) | Tvariant(_,[],_) ->
    level
  | Ttuple tyl | Tconstr(_,tyl) | Trecord(_,tyl,_) | Tvariant(_,tyl,_) ->
    get_type_level_list notgeneric tyl 
  | Ttag -> level

and get_type_level_list level = function
| [] -> failwith "get_type_level_list"
| [ty] -> get_type_level level ty
| ty::rest ->
  let lv1 = get_type_level level ty in
  let lv2 = get_type_level_list level rest in
  min lv1 lv2


let free_type_vars level ty =
  let fv = ref [] in
  let rec free_vars ty =
    let ty = type_repr ty in
    match ty with
    | Tvar _ ->
      if get_type_level generic ty >= level then fv := ty :: !fv
    | Tlist ty | Tref ty -> free_vars ty
    | Tarrow(arg,ret) -> free_vars arg; free_vars ret
    | Ttuple tyl | Tconstr(_,tyl) | Trecord(_,tyl,_) | Tvariant(_,tyl,_) ->
      List.iter free_vars tyl
    | _ -> ()
  in free_vars ty;
  !fv

let rec generalize level ty =
  let ty = type_repr ty in
  match ty with
  | Tvar link ->
    begin match link with
    | {contents=Unbound{id=id;level=level'}} 
      when level' > level ->
      link := (Unbound {id=id;level=generic});
      ty
    | {contents=Linkto ty} -> generalize level ty
    | _ -> ty
    end
  | Tlist ty -> Tlist (generalize level ty)
  | Tref ty -> Tref (generalize level ty)
  | Tarrow(arg,ret) -> Tarrow(generalize level arg, generalize level ret)
  | Ttuple tyl -> Ttuple(List.map (generalize level) tyl)
  | Tconstr(name,tyl) -> Tconstr(name,List.map (generalize level) tyl)
  | Trecord(name,tyl,elem) -> Tvariant(name,List.map (generalize level) tyl,elem)
  | Tvariant(name,tyl,elem) -> Tvariant(name,List.map (generalize level) tyl,elem)
  | _ -> ty

let instantiate level ty =
  let ty = type_repr ty in
  let ty_lv = get_type_level notgeneric ty in
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
    | Trecord(name,tyl,elem) when ty_lv = generic -> Trecord(name,List.map f tyl,elem)
    | Tvariant(name,tyl,elem) when ty_lv = generic -> Tvariant(name,List.map f tyl,elem)
    | _ -> ty
  in f ty

let rec occursin id = function
| Tvar link ->
  begin match link with
  | {contents=Unbound{id=id';level=_}} -> id = id'
  | {contents=Linkto ty} -> occursin id ty
  end
| Tlist ty -> occursin id ty
| Tref ty -> occursin id ty
| Tarrow(arg,ret) -> occursin id arg || occursin id ret
| Ttuple tyl | Tconstr(_,tyl) | Trecord(_,tyl,_) | Tvariant(_,tyl,_) -> List.exists (occursin id) tyl
| _ -> false

let rec adjustlevel level = function
| Tvar link ->
  begin match link with
  | {contents=Unbound{id=id';level=level'}} ->
    if level < level' then link := Unbound{id=id';level=level}
  | {contents=Linkto ty} -> adjustlevel level ty
  end
| Tlist ty -> adjustlevel level ty
| Tref ty -> adjustlevel level ty
| Tarrow(arg,ret) -> adjustlevel level arg; adjustlevel level ret
| Ttuple tyl | Tconstr(_,tyl) | Trecord(_,tyl,_) | Tvariant(_,tyl,_) -> List.iter (adjustlevel level) tyl
| _ -> ()

let new_type_var_subst tyl fields =
  let new_type_var_list = ref [] in
  let rec subst id ty = function
  | [] -> []
  | (name,Tvar {contents=Unbound{id=id';level=_}})::rest when id=id' ->
    (name,ty)::subst id ty rest
  | field::rest ->
    field::subst id ty rest
  in
  let subst_new_type_var fields ty =
  match ty with
  | Tvar {contents=Unbound{id=id;level=_}} ->
    let new_type_var' = new_type_var notgeneric in
    new_type_var_list := new_type_var' :: !new_type_var_list;
    subst id new_type_var' fields
  | _ -> fields
  in
  let snd = List.fold_left subst_new_type_var fields tyl in
  (List.rev !new_type_var_list,snd)

let rec decl_to_ty name curr_num = function
| (num,decl_list)::def_list when num <= curr_num ->
  let rec iter_decl_list = function
  | Drecord(n,tyl,fields)::_ when n=name-> 
    let (tyl,fields) = new_type_var_subst tyl fields in
    Trecord(n,tyl,fields)
  | Dvariant(n,tyl,fields)::_ when n=name-> 
    let (tyl,fields) = new_type_var_subst tyl fields in
    Tvariant(n,tyl,fields)
  | _::rest ->
    iter_decl_list rest
  | [] ->
    decl_to_ty name curr_num def_list
  in iter_decl_list decl_list
| _::def_list -> decl_to_ty name curr_num def_list
| [] -> failwith (Printf.sprintf "decl_to_ty %s" name)