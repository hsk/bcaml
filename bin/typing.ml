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


let min lhs rhs =
  match lhs,rhs with
  | Some l, Some r -> Some(min l r)
  | Some l, None -> Some l
  | None, Some r -> Some r
  | None, None -> None

let rec get_type_level ty =
  let ty = type_repr ty in
  match ty with
  | Tvar {contents=Unbound{id=_;level=level}} -> Some level
  | Tvar {contents=Linkto ty} -> get_type_level ty
  | Tunit | Tbool | Tint | Tfloat | Tchar |Tstring -> None
  | Tlist ty | Tref ty -> get_type_level ty
  | Tarrow(arg,ret) -> min (get_type_level arg) (get_type_level ret)
  | Ttuple tyl | Tconstr(_,tyl) -> get_type_level_list tyl
  | Trecord(_,fields) | Tvariant(_,fields) -> get_type_level_list (List.map snd fields)
  | Ttag -> None

and get_type_level_list = function
| [] -> None
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
      begin match get_type_level ty with
      | Some level' when level' >= level -> fv := ty :: !fv
      | _ -> ()
      end
    | Tlist ty | Tref ty -> free_vars ty
    | Tarrow(arg,ret) -> free_vars arg; free_vars ret
    | Ttuple tyl | Tconstr(_,tyl) -> List.iter free_vars tyl
    | Trecord(_,fields) | Tvariant(_,fields) ->
      List.iter free_vars (List.map snd fields)
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
      link := (Unbound {id=id;level=generic})
    | {contents=Linkto ty} -> generalize level ty
    | _ -> ()
    end
  | Tlist ty -> generalize level ty
  | Tref ty -> generalize level ty
  | Tarrow(arg,ret) -> generalize level arg; generalize level ret
  | Ttuple tyl -> List.iter (generalize level) tyl
  | Tconstr(_,tyl) -> List.iter (generalize level) tyl
  | Trecord(_,fields) -> List.iter (fun (_,ty) -> generalize level ty) fields
  | Tvariant(_,fields) -> List.iter (fun (_,ty) -> generalize level ty) fields
  | _ -> ()

let instantiate level ty =
  let ty = type_repr ty in
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
    | Tlist ty -> Tlist (f ty)
    | Tref ty -> Tref (f ty)
    | Tarrow(arg,ret) -> Tarrow(f arg, f ret)
    | Ttuple tyl -> Ttuple(List.map f tyl)
    | Tconstr(name,tyl) -> Tconstr(name,List.map f tyl)
    | Trecord(name,fields) -> Trecord(name,List.map (fun (n,ty) -> (n,f ty)) fields)
    | Tvariant(name,fields) -> Tvariant(name,List.map (fun (n,ty) -> (n,f ty)) fields)
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
| Ttuple tyl | Tconstr(_,tyl) -> List.exists (occursin id) tyl
| Trecord(_,fields) | Tvariant(_,fields) -> List.exists (occursin id) (List.map snd fields)
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
| Ttuple tyl | Tconstr(_,tyl) -> List.iter (adjustlevel level) tyl
| Trecord(_,fields) | Tvariant(_,fields) -> List.iter (adjustlevel level) (List.map snd fields)
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
  | Trecord(name1,fields1), Trecord(name2,fields2) when name1 = name2 ->
    unify_list (List.map snd fields1) (List.map snd fields2)
  | Tvariant(name1,fields1), Tvariant(name2,fields2) when name1 = name2 -> 
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
  | Trecord(name,fields) ->
    Trecord(name,subst_ty_to_fields fields id ty)
  | Tvariant(name,fields) -> 
    Tvariant(name,subst_ty_to_fields fields id ty)
  | _ -> t

and subst_ty_to_tyl tyl id ty =
  List.map (fun t -> subst_ty t id ty) tyl

and subst_ty_to_fields fields id ty =
  List.map (fun (s,t) -> (s,subst_ty t id ty)) fields

let decl_to_ty name =
  let rec aux = function
  | Drecord(n,tyl,fields)::_ when n=name-> 
    let (tyl,fields) =  fold_idl_for_fields fields (tyl_to_idl tyl) in
    (tyl,Trecord(n,fields))
  | Dvariant(n,tyl,fields)::_ when n=name-> 
    let (tyl,fields) =  fold_idl_for_fields fields (tyl_to_idl tyl) in
    (tyl,Tvariant(n,fields))
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

let get_fields name =
  let fields =
    match decl_to_ty name with
    | _,Trecord(_,fields) -> fields
    | _,Tvariant(_,fields) -> fields
    | _ -> failwith "not a record or variant type"
    in fields

let compare_label name (label1,_) (label2,_) =
  let rec aux label n = function
  | x::_ when label = x -> n
  | _::xs -> aux label (n + 1) xs
  | [] -> failwith "label not found"
  in
  let labels = List.map fst (get_fields name) in
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
  | Dvariant(name,_,fields)::_ when List.mem_assoc tag fields -> name
  | _::rest -> aux rest
  | _ -> failwith "tag_belong_to"
  in aux !modules.tydecls

let rec subst_ty_to_tvar t ty =
  match t with
  | Tvar {contents=Unbound{id=_;level=_}} -> ty
  | Tvar {contents=Linkto t} -> subst_ty_to_tvar t ty
  | Tlist t -> Tlist (subst_ty_to_tvar t ty)
  | Tref t -> Tref (subst_ty_to_tvar t ty)
  | Tarrow(arg,ret) -> Tarrow(subst_ty_to_tvar arg ty, subst_ty_to_tvar ret ty)
  | Ttuple tyl -> Ttuple(subst_ty_to_tvar_in_tyl tyl ty)
  | Tconstr(name,tyl) -> Tconstr(name,subst_ty_to_tvar_in_tyl tyl ty)
  | Trecord(name,fields) ->
    Trecord(name,subst_ty_to_tvar_in_fields fields ty)
  | Tvariant(name,fields) -> 
    Tvariant(name,subst_ty_to_tvar_in_fields fields  ty)
  | _ -> t

and subst_ty_to_tvar_in_tyl tyl ty =
  List.map (fun t -> subst_ty_to_tvar t ty) tyl

and subst_ty_to_tvar_in_fields fields ty =
  List.map (fun (s,t) -> (s,subst_ty_to_tvar t ty)) fields

let validate_record level fields =
  let first_label = fst (List.hd fields) in
  let record_name = label_belong_to first_label in
  let fields = List.sort (compare_label record_name) fields in
  if List.map fst fields = List.map fst (get_fields record_name) then
    subst_ty_to_tvar_in_fields fields (new_type_var level)
  else
    failwith "invalid record"
  
let validate_variant level tag_name =
  let variant_name = tag_belong_to tag_name in
  let fields = get_fields variant_name in
  subst_ty_to_tvar_in_fields fields (new_type_var level)

let rec is_simple = function
| Evar _ -> true
| Econstant _ -> true
| Ebuildin _ -> false
| Etuple l -> List.for_all is_simple l
| Etag -> true
| Econstruct(_,expr) -> is_simple expr
| Eapply _ -> false
| Elet(l, body) -> List.for_all is_simple (List.map snd l) && is_simple body
| Eletrec(l, body) -> List.for_all is_simple (List.map snd l) && is_simple body
| Efunction l -> List.for_all is_simple (List.map snd l)
| Etrywith(body, l) -> is_simple body && List.for_all is_simple (List.map snd l)
| Esequence(expr1,expr2) -> is_simple expr1 && is_simple expr2
| Econdition(_,ifso,ifelse) -> is_simple ifso && is_simple ifelse
| Econstraint(expr,_) -> is_simple expr
| Erecord l -> List.for_all is_simple (List.map snd l)
| Erecord_access(expr,_) -> is_simple expr
| Ewhen(expr,body) -> is_simple expr && is_simple body