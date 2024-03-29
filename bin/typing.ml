open Syntax
open Prims
open Globals

let curr_id = ref 0

let gen_id () =
  let ret = !curr_id in
  incr curr_id;
  ret

let new_type_var level =
  Tvar (ref (Unbound {id=Idint (gen_id ());level=level}))

let min lhs rhs =
  match lhs,rhs with
  | Some l, Some r -> Some(min l r)
  | Some l, None -> Some l
  | None, Some r -> Some r
  | None, None -> None

let rec get_type_level ty =
  match ty with
  | Tvar {contents=Unbound{id=_;level=level}} -> Some level
  | Tvar {contents=Linkto ty} -> get_type_level ty
  | Tunit | Tbool | Tint | Tfloat | Tchar |Tstring -> None
  | Tlist ty | Tref ty -> get_type_level ty
  | Tarrow(arg,ret) -> min (get_type_level arg) (get_type_level ret)
  | Ttuple tyl | Tconstr(_,tyl) -> get_type_level_list tyl
  | Trecord(_,_,fields) | Tvariant(_,_,fields) -> get_type_level_list (List.map snd fields)
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
    match ty with
    | Tvar _ ->
      begin match get_type_level ty with
      | Some level' when level' >= level -> fv := ty :: !fv
      | _ -> ()
      end
    | Tlist ty | Tref ty -> free_vars ty
    | Tarrow(arg,ret) -> free_vars arg; free_vars ret
    | Ttuple tyl | Tconstr(_,tyl) -> List.iter free_vars tyl
    | Trecord(_,_,fields) | Tvariant(_,_,fields) ->
      List.iter free_vars (List.map snd fields)
    | _ -> ()
  in free_vars ty;
  !fv

let rec generalize level ty =
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
  | Trecord(_,_,fields) -> List.iter (fun (_,ty) -> generalize level ty) fields
  | Tvariant(_,_,fields) -> List.iter (fun (_,ty) -> generalize level ty) fields
  | _ -> ()

let instantiate level ty =
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
    | Trecord(name,tyl,fields) -> Trecord(name,tyl,List.map (fun (n,ty) -> (n,f ty)) fields)
    | Tvariant(name,tyl,fields) -> Tvariant(name,tyl,List.map (fun (n,ty) -> (n,f ty)) fields)
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
| Trecord(_,_,fields) | Tvariant(_,_,fields) -> List.exists (occursin id) (List.map snd fields)
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
| Trecord(_,_,fields) | Tvariant(_,_,fields) -> List.iter (adjustlevel level) (List.map snd fields)
| _ -> ()

let rec unify ty1 ty2 =
  match ty1, ty2 with
  | Tvar link1, Tvar link2 when link1 = link2 -> ()
  | Tvar ({contents=Unbound{id=id;level=level}} as link), ty 
  | ty, Tvar ({contents=Unbound{id=id;level=level}} as link) ->
    if occursin id ty then failwith (Printf.sprintf "unify error due to ocurr check %s" (show_ty ty));
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
  | Tconstr(name1,tyl1), Trecord(name2,tyl2,_) when name1 = name2 ->
    unify_list tyl1 tyl2
  | Tconstr(name1,tyl1), Tvariant(name2,tyl2,_) when name1 = name2 ->
    unify_list tyl1 tyl2
  | Trecord(name1,tyl1,_), Tconstr(name2,tyl2) when name1 = name2 ->
    unify_list tyl1 tyl2
  | Tvariant(name1,tyl1,_), Tconstr(name2,tyl2) when name1 = name2 ->
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
    Trecord(name,tyl,subst_ty_to_fields fields id ty)
  | Tvariant(name,tyl,fields) -> 
    Tvariant(name,tyl,subst_ty_to_fields fields id ty)
  | _ -> t

and subst_ty_to_tyl tyl id ty =
  List.map (fun t -> subst_ty t id ty) tyl

and subst_ty_to_fields fields id ty =
  List.map (fun (s,t) -> (s,subst_ty t id ty)) fields

let rec decl_to_ty name =
  let rec aux = function
  | Drecord(n,tyl,fields)::_ when n=name-> 
    let (tyl,fields) =  subst_tvars_to_fields fields (collect_tvars tyl) in
    (tyl,Trecord(n,tyl,fields))
  | Dvariant(n,tyl,fields)::_ when n=name-> 
    let (tyl,fields) =  subst_tvars_to_fields fields (collect_tvars tyl) in
    (tyl,Tvariant(n,tyl,fields))
  | Dabbrev(n,tyl,ty)::_ when n=name-> 
    let (tyl,ty) =  subst_tvars_to_tylist ty (collect_tvars tyl) in
    (tyl, ty)
  | _::rest ->
    aux rest
  | [] -> failwith (Printf.sprintf "decl_to_ty %s" name)

  and collect_tvars tyl =
    match tyl with
    | Tvar {contents=Unbound{id=id;level=_}}::tyl ->
      id::collect_tvars tyl
    | [] -> []
    | _ -> failwith "tyl_to_idl"

  and subst_tvars_to_fields fields idl=
    let new_type_vars = ref [] in
    let snd = List.fold_left 
    (
      fun fields id -> 
        let ty = new_type_var 1 in
        new_type_vars := !new_type_vars @ [ty];
        subst_ty_to_fields fields id ty
    ) fields idl in
    (!new_type_vars,snd)

  and subst_tvars_to_tylist ty idl=
    let new_type_vars = ref [] in
    let snd = List.fold_left 
    (
      fun t id -> 
        let ty = new_type_var 1 in
        new_type_vars := !new_type_vars @ [ty];
        subst_ty t id ty
    ) ty idl in
    (!new_type_vars,snd)

  in aux !modules.tydecls

and expand_abbrev ty =
  match ty with 
  | Tconstr(name,params) ->
    let (tyl,ty) = decl_to_ty name in
    if List.length params = List.length tyl then
      begin
        unify_list params tyl;
        ty
      end
    else
      failwith "the number of parameters of type constructor doesn't match"
  | Tlist t -> Tlist (expand_abbrev t)
  | Tref t -> Tref (expand_abbrev t)
  | Tarrow(arg,ret) -> Tarrow(expand_abbrev arg, expand_abbrev ret)
  | Ttuple tyl -> Ttuple(List.map expand_abbrev tyl)
  | Trecord(name,tyl,fields) ->
    Trecord(name,tyl,List.map (fun(n,t) -> (n,expand_abbrev t)) fields)
  | Tvariant(name,tyl,fields) -> 
    Tvariant(name,tyl,List.map (fun(n,t) -> (n,expand_abbrev t)) fields)
  | _ -> ty



let get_fields ty =
  let fields =
    match ty with
    | Trecord(_,_,fields) -> fields
    | Tvariant(_,_,fields) -> fields
    | _ -> failwith "not a record or variant type"
    in fields

let compare_label name (label1,_) (label2,_) =
  let rec aux label n = function
  | x::_ when label = x -> n
  | _::xs -> aux label (n + 1) xs
  | [] -> failwith "label not found"
  in
  let (_,ty) = decl_to_ty name in
  let labels = List.map fst (get_fields ty) in
  let aux label = aux label 0 labels in
  aux label1 - aux label2

let label_belong_to label =
  let rec aux = function
  | Drecord(name,_,fields)::_ when List.mem_assoc label fields -> name
  | _::rest -> aux rest
  | _ -> failwith (Printf.sprintf "label not found %s" label)
  in aux !modules.tydecls

let tag_belong_to tag =
  let rec aux = function
  | Dvariant(name,_,fields)::_ when List.mem_assoc tag fields -> name
  | _::rest -> aux rest
  | _ -> failwith (Printf.sprintf "tag not found %s" tag)
  in aux !modules.tydecls

let rec is_simple = function
| Evar _ -> true
| Econstant _ -> true
| Eprim _ -> true
| Etuple l -> List.for_all is_simple l
| Enil -> true
| Econs(car,cdr) -> is_simple car && is_simple cdr
| Elist _ -> true
| Eref _ -> false
| Ederef _ -> false
| Eassign(_,_) -> false
| Eloc _ -> true
| Eunit -> true
| Etag -> true
| Econstruct(_,expr) -> is_simple expr
| Eapply _ -> false
| Elet(l, body) -> List.for_all is_simple (List.map snd l) && is_simple body
| Eletrec(l, body) -> List.for_all is_simple (List.map snd l) && is_simple body
| Efix _ -> true
| Efunction _ -> true
| Esequence(expr1,expr2) -> is_simple expr1 && is_simple expr2
| Econdition(_,ifso,ifelse) -> is_simple ifso && is_simple ifelse
| Econstraint(expr,_) -> is_simple expr
| Erecord l -> List.for_all is_simple (List.map snd l)
| Erecord_access(expr,_) -> is_simple expr
| Ewhen(expr,body) -> is_simple expr && is_simple body

let type_prim level = function
| Beq
| Bnq
| Blt
| Bgt
| Ble
| Bge
| Beqimm
| Bnqimm ->
  let tvar = new_type_var level in
  Tarrow(tvar,(Tarrow(tvar,Tbool)))
| Bnot -> Tarrow(Tbool,Tbool)
| Band 
| Bor -> Tarrow(Tbool,Tarrow(Tbool,Tbool))
| Bnegint -> Tarrow(Tint,Tint)
| Baddint
| Bsubint
| Bmulint
| Bdivint
| Bmod -> Tarrow(Tint,Tarrow(Tint,Tint))
| Blnot -> Tarrow(Tint,Tint)
| Bland
| Blor
| Blxor
| Blsl
| Blsr
| Basr -> Tarrow(Tint,Tarrow(Tint,Tint))
| Bnegfloat -> Tarrow(Tfloat,Tfloat)
| Baddfloat
| Bsubfloat
| Bmulfloat
| Bdivfloat
| Bpower -> Tarrow(Tfloat,Tarrow(Tfloat,Tfloat))
| Bconcatstring -> Tarrow(Tstring,Tarrow(Tstring,Tstring))
| Bintoffloat -> Tarrow(Tfloat,Tint)
| Bfloatofint -> Tarrow(Tint,Tfloat)
| Bintofchar -> Tarrow(Tchar,Tint)
| Bcharofint -> Tarrow(Tint,Tchar)
| Bstringofbool -> Tarrow(Tbool,Tstring)
| Bboolofstring -> Tarrow(Tstring,Tbool)
| Bstringofint -> Tarrow(Tint,Tstring)
| Bintofstring -> Tarrow(Tstring,Tint)
| Bstringoffloat -> Tarrow(Tfloat,Tstring)
| Bfloatofstring -> Tarrow(Tstring,Tfloat)
| Bconcat -> 
  let tvar = new_type_var level in
  Tarrow(Tlist tvar,(Tarrow(Tlist tvar,Tlist tvar)))
| Bfailwith ->
  let tvar = new_type_var level in
  Tarrow(Tstring,tvar)

let rec type_patt level new_env pat ty =
  match pat with
  | Pwild -> new_env
  | Pvar s ->
    if List.mem_assoc s new_env then failwith "a variable found more than twice"
    else (s,ty)::new_env
  | Pparams _ -> failwith "type_patt"
  | Palias(pat,s) -> 
    if List.mem_assoc s new_env then failwith "a variable found more than twice"
    else type_patt level ((s,ty)::new_env) pat ty
  | Pconstant cst ->
    let cst_ty = begin match cst with
    | Cint _ -> Tint
    | Cbool _ -> Tbool
    | Cfloat _ -> Tfloat
    | Cstring _ -> Tstring
    | Cchar _ -> Tchar
    end in
    unify ty cst_ty;
    new_env
  | Ptuple patl -> 
    let tyl = List.init (List.length patl) (fun _ -> new_type_var level) in
    unify (Ttuple tyl) ty;
    List.fold_left2 (type_patt level) new_env patl tyl
  | Pnil ->
    unify ty (Tlist (new_type_var level));
    new_env
  | Pcons(car,cdr) ->
    let ty1 = new_type_var level in
    let ty2 = new_type_var level in
    let new_env = type_patt level new_env car ty1 in
    let new_env = type_patt level new_env cdr ty2 in
    unify (Tlist ty1) ty2;
    unify ty2 ty;
    new_env
  | Pref expr ->
    let ty1 = new_type_var level in
    let new_env = type_patt level new_env expr ty1 in
    unify (Tref ty1) ty;
    new_env
  | Punit ->
    unify Tunit ty;
    new_env
  | Ptag ->
    unify ty Ttag;
    new_env
  | Pconstruct(name,pat) -> 
    validate_variant_pat new_env level (name,pat) ty
  | Por(pat1,pat2) ->
    let env1 = type_patt level new_env pat1 ty in
    let env2 = type_patt level new_env pat2 ty in
    let is_same_list xl yl =
      let rec aux xl yl =
      match xl with
      | x::xs -> List.mem x yl && aux xs yl
      | [] -> true
      in
      (List.length xl = List.length yl) && aux xl yl
    in
    if is_same_list (List.map fst env1) (List.map fst env2) then
      env1
    else
      failwith "invalid or pattern"
  | Pconstraint(pat,expected) ->
    let new_env = type_patt level new_env pat ty in
    unify ty (instantiate level expected);
    new_env
  | Precord fields ->
    validate_record_pat new_env level fields ty

and type_pat level pat ty =
  type_patt level [] pat ty 

and validate_record_pat env level fields ty =
  let first_label = fst (List.hd fields) in
  let record_name = label_belong_to first_label in
  let record_ty = instantiate level (snd (decl_to_ty record_name)) in
  let fields1 = List.sort (compare_label record_name) fields in
  let fields2 = get_fields record_ty in
  if List.map fst fields1 = List.map fst fields2 then
    begin
      unify record_ty ty;
      List.fold_left2  (type_patt level) env (List.map snd fields1) (List.map snd fields2)
    end
  else
    failwith "invalid record pattern"
  
and validate_variant_pat env level (tag_name,pat) ty =
  let variant_name = tag_belong_to tag_name in
  let (_,variant_ty) = decl_to_ty variant_name in
  unify ty (instantiate level variant_ty);
  let ty = List.assoc tag_name (get_fields variant_ty) in
  type_patt level env pat ty

and type_expr env level = function
| Evar s ->
  begin
    try 
      let prim = List.assoc s prim_list in
      type_prim level prim
    with
    | _ ->
      instantiate level (List.assoc s env)
  end
| Econstant cst -> 
  begin match cst with
  | Cint _ -> Tint
  | Cbool _ -> Tbool
  | Cfloat _ -> Tfloat
  | Cstring _ -> Tstring
  | Cchar _ -> Tchar
  end
| Eprim prim -> type_prim level prim
| Etuple l -> Ttuple(List.map (fun t->type_expr env level t) l)
| Enil -> Tlist (new_type_var level)
| Econs(car,cdr) ->
  let ty1 = type_expr env level car in
  let ty2 = type_expr env level cdr in
  unify (Tlist ty1) ty2;
  ty2
| Elist l -> 
  let ty = new_type_var level in
  List.iter (fun expr -> unify ty (type_expr env level expr)) l;
  Tlist ty
| Eref expr ->
  let ty = type_expr env level expr in
  Tref ty
| Ederef expr ->
  let ty1 = new_type_var level in
  let ty2 = type_expr env level expr in
  unify (Tref ty1) ty2;
  ty1
| Eassign(lhs,rhs) ->
  let ty1 = type_expr env level lhs in
  let ty2 = type_expr env level rhs in
  unify ty1 (Tref ty2);
  Tunit
| Eloc _ ->
  let ty = new_type_var level in
  Tref ty
| Eunit ->
  Tunit
| Etag -> Ttag
| Econstruct(tag_name,expr) -> 
  let ty = validate_variant_expr env level (tag_name,expr) in
  ty
| Eapply(fct,args) -> 
  let fct_ty = type_expr env level fct in
  let args = List.map (type_expr env level) args in
  let ty = List.fold_left
  (
    fun fct_ty arg_ty ->
      let param_ty = new_type_var level in
      let ret_ty = new_type_var level in
      unify fct_ty (Tarrow(param_ty,ret_ty));
      unify arg_ty param_ty;
      ret_ty
  ) fct_ty args in ty
| Elet(pat_expr, body) -> 
  let patl = List.map (fun (pat,_) -> pat) pat_expr in
  let tyl = List.map (fun (_,_)->new_type_var level) pat_expr in
  let add_env = List.fold_left2 (type_patt level) env patl tyl in
  List.iter2 (
    fun ty (_,expr) -> 
      unify ty (type_expr env (level+1) expr);
      if is_simple expr then generalize (level+1) ty
    ) tyl pat_expr;
  type_expr (add_env@env) level body
| Eletrec(pat_expr, body) -> 
  let patl = List.map (fun (pat,_) -> pat) pat_expr in
  let tyl = List.map (fun (_,_)->new_type_var level) pat_expr in
  let add_env = List.fold_left2 (type_patt level) env patl tyl in
  List.iter2 (
    fun ty (_,expr) -> 
      unify ty (type_expr (add_env@env) (level+1) expr);
      if is_simple expr then generalize (level+1) ty
    ) tyl pat_expr;
  type_expr (add_env@env) level body
| Efix(_,e) ->
  type_expr env level e
| Efunction l -> 
  begin match l with
  | [] -> failwith "empty function"
  | [(Pparams patl,expr)] ->
    let tyl = List.map (fun _ -> new_type_var level) patl in
    let add_env = List.fold_left2 (type_patt level) env patl tyl in
    let ret_ty = type_expr add_env level expr in
    let ty = List.fold_left (
      fun ret_ty arg_ty -> Tarrow(arg_ty,ret_ty)
    ) ret_ty (List.rev tyl) in ty
  | pat_expr ->
    let arg_ty = new_type_var level in
    let ret_ty = new_type_var level in
    List.iter (
      fun (pat,expr) ->
      let add_env = type_pat level pat arg_ty in
      let ty = type_expr (add_env@env) level expr in
      unify ty ret_ty
    ) pat_expr;
    Tarrow(arg_ty,ret_ty)
  end
| Esequence(expr1,expr2) -> 
  let ty = type_expr env level expr1 in
  unify ty Tunit;
  type_expr env level expr2
| Econdition(flag,ifso,ifelse) ->
  let flag = type_expr env level flag in
  unify flag Tbool;
  let ty = type_expr env level ifso in
  unify ty (type_expr env level ifelse);
  ty
| Econstraint(expr,expected) -> 
  let ty = type_expr env level expr in
  unify ty (instantiate level expected);
  ty
| Erecord [] -> failwith "empty record fields"
| Erecord l ->
  validate_record_expr env level l
| Erecord_access(expr,label) ->
  let ty = type_expr env level expr in
  let record_name = label_belong_to label in
  let record_ty = instantiate level (snd (decl_to_ty record_name)) in
  unify ty (instantiate level record_ty);
  List.assoc label (get_fields record_ty)
| Ewhen(expr,body) -> 
  let ty = type_expr env level expr in
  unify ty Tbool;
  type_expr env level body

and validate_record_expr env level fields =
  let first_label = fst (List.hd fields) in
  let record_name = label_belong_to first_label in
  let record_ty = instantiate level (snd (decl_to_ty record_name)) in
  let fields = List.sort (compare_label record_name) fields in
  let fields1 = (List.map (fun (n,e)->(n,type_expr env level e)) fields) in
  let fields2 = get_fields record_ty in
  if List.map fst fields = List.map fst (get_fields record_ty) then
    begin
      unify_list (List.map snd fields1) (List.map snd fields2);
      record_ty
    end
  else
    failwith "invalid record expression"
  
and validate_variant_expr env level (tag_name,expr) =
  let variant_name = tag_belong_to tag_name in
  let variant_ty = instantiate level (snd (decl_to_ty variant_name)) in
  let ty = List.assoc tag_name (get_fields variant_ty) in
  let ty1 = (type_expr env level expr) in
  unify ty ty1;
  variant_ty

let type_let env pat_expr =
  let level = 0 in
  let patl = List.map (fun (pat,_) -> pat) pat_expr in
  let tyl = List.map (fun (_,_)->new_type_var (level+1)) pat_expr in
  let add_env = List.fold_left2 (type_patt (level+1)) env patl tyl in
  List.iter2 (
    fun ty (_,expr) -> 
      unify ty (type_expr env (level+1) expr);
      if is_simple expr then generalize level ty
    ) tyl pat_expr;
  add_env

let type_letrec env pat_expr =
  let level = 0 in
  let patl = List.map (fun (pat,_) -> pat) pat_expr in
  let tyl = List.map (fun (_,_)->new_type_var (level+1)) pat_expr in
  let add_env = List.fold_left2 (type_patt (level+1)) env patl tyl in
  List.iter2 (
    fun ty (_,expr) -> 
      unify ty (type_expr add_env (level+1) expr);
      if is_simple expr then generalize level ty
    ) tyl pat_expr;
  add_env