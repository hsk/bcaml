open Syntax
open Globals

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

let rec unify ty1 ty2 = 
  match ty1, ty2 with
  | Tvar ({contents=Unbound{id=id;level=level}} as link), ty 
  | ty, Tvar ({contents=Unbound{id=id;level=level}} as link) ->
    if occursin id ty then failwith "unify error due to ocurr check";
    adjustlevel level ty;
    link := Linkto ty
  | Tvar {contents=Linkto t1}, t2
  | t1, Tvar {contents=Linkto t2} -> unify t1 t2
  | Tlist t1, Tlist t2 -> unify t1 t2
  | Tref t1, Tref t2 -> unify t1 t2
  | Tarrow(arg1,ret1), Tarrow(arg2,ret2) -> unify arg1 arg2; unify ret1 ret2
  | Ttuple tyl1, Ttuple tyl2 -> unify_list tyl1 tyl2
  | Tconstr(name1,tyl1), Tconstr(name2,tyl2) when name1 = name2 ->
    unify_list tyl1 tyl2
  | Trecord(name1,_,fields1), Trecord(name2,_,fields2) when name1 = name2 ->
    unify_list (List.map snd fields1) (List.map snd fields2)
  | Tvariant(name1,_,fields1), Tvariant(name2,_,fields2) when name1 = name2 -> 
    unify_list (List.map snd fields1) (List.map snd fields2)
  | ty1,ty2 when ty1 = ty2 -> ()
  | _ -> failwith "Cannot unify types" 
and unify_list tyl1 tyl2 =
  List.iter2 unify tyl1 tyl2

let rec subst_ty t id ty =
  match t with
  | Tvar {contents=Unbound{id=id';level=_}} when id = id' -> ty
  | Tvar {contents=Unbound _} -> t
  | Tvar {contents=Linkto t} -> subst_ty t id ty
  | Tlist t -> Tlist (subst_ty t id ty)
  | Tref t -> Tref (subst_ty t id ty)
  | Tarrow(arg,ret) -> Tarrow(subst_ty arg id ty, subst_ty ret id ty)
  | Ttuple tyl -> Ttuple(subst_ty_to_tyl tyl id ty)
  | Tconstr(name,tyl) -> Tconstr(name,subst_ty_to_tyl tyl id ty)
  | Trecord(name,tyl,fields) ->
    Trecord(name,subst_ty_to_tyl tyl id ty,subst_ty_to_fields fields id ty)
  | Tvariant(name,tyl,fields) -> 
    Tvariant(name,subst_ty_to_tyl tyl id ty,subst_ty_to_fields fields id ty)
  | _ -> t

and subst_ty_to_tyl tyl id ty =
  List.map (fun t -> subst_ty t id ty) tyl

and subst_ty_to_fields fields id ty =
  List.map (fun (s,t) -> (s,subst_ty t id ty)) fields

let decl_to_ty name =
  let rec aux = function
  | Drecord(n,tyl,fields)::_ when n=name-> 
    let (tyl,fields) =  fold_idl_for_fields fields (tyl_to_idl tyl) in
    (tyl,Trecord(n,tyl,fields))
  | Dvariant(n,tyl,fields)::_ when n=name-> 
    let (tyl,fields) =  fold_idl_for_fields fields (tyl_to_idl tyl) in
    (tyl,Tvariant(n,tyl,fields))
  | Dabbrev(n,tyl,ty)::_ when n=name-> 
    let (tyl,ty) =  fold_idl_for_ty ty (tyl_to_idl tyl) in
    (tyl,ty)
  | _::rest ->
    aux rest
  | [] -> failwith "decl_to_ty"

  and tyl_to_idl tyl =
    match tyl with
    | Tvar {contents=Unbound{id=id;level=_}}::tyl ->
      id::tyl_to_idl tyl
    | [] -> []
    | _ -> failwith "tyl_to_idl"

  and fold_idl_for_fields fields idl=
    let new_type_vars = ref [] in
    let snd = List.fold_left 
    (
      fun fields id -> 
        let ty = new_type_var notgeneric in
        new_type_vars := !new_type_vars @ [ty];
        subst_ty_to_fields fields id ty
    ) fields idl in
    (!new_type_vars,snd)

  and fold_idl_for_ty ty idl=
    let new_type_vars = ref [] in
    let snd = List.fold_left 
    (
      fun t id -> 
        let ty = new_type_var notgeneric in
        new_type_vars := !new_type_vars @ [ty];
        subst_ty t id ty
    ) ty idl in
    (!new_type_vars,snd)

  in aux !modules.tydecls

let rec convert_constr ty =
  match ty with 
  | Tconstr(name,params) ->
    let (tyl,ty) = decl_to_ty name in
    if List.length params = List.length tyl then
      begin
        unify_list params tyl;
        convert_constr ty
      end
    else
      failwith "the number of parameters of type constructor doesn't match"
  | _ -> ty

let dom_of_fields name =
  let fields =
    match decl_to_ty name with
    | _,Trecord(_,_,fields) -> fields
    | _ -> failwith "not a record type"
    in
    List.map fst fields

let compare_label name (label1,_) (label2,_) =
  let rec aux label n = function
  | x::_ when label = x -> n
  | _::xs -> aux label (n + 1) xs
  | [] -> failwith "label not found"
  in
  let labels = dom_of_fields name in
  let aux label = aux label 0 labels in
  aux label1 - aux label2

let label_belong_to label =
  let rec aux = function
  | Drecord(name,_,fields)::_ when List.mem_assoc label fields -> name
  | _::rest -> aux rest
  | _ -> failwith "label_belong_to"
  in aux !modules.tydecls

let tag_belong_to tag =
  let rec aux = function
  | Drecord(name,_,fields)::_ when List.mem_assoc tag fields -> name
  | _::rest -> aux rest
  | _ -> failwith "tag_belong_to"
  in aux !modules.tydecls

let is_valid_record fields =
  let first_label = fst (List.hd fields) in
  let record_name = label_belong_to first_label in
  let fields = List.sort (compare_label record_name) fields in
  List.map fst fields = dom_of_fields record_name