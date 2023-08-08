open Prims
open Syntax

exception InterpreterError of string

type ctx = (string *expr) list 

let ctx = ref (List.map (fun (n,p) ->(n,Eprim p)) prim_list)

let extendcontext name v = 
  ctx := List.append !ctx [(name,v)]

let lookupcontext name = List.assoc name !ctx

type store = expr list 

let store = ref [] 

let extendstore v = 
  let loc = List.length !store in
  store := List.append !store [v];
  loc

let lookuploc l = List.nth !store l

let updatestore n v =
  let rec f s = match s with 
      (0, _::rest) -> v::rest
    | (n, v'::rest) -> v' :: (f (n-1,rest))
    | _ -> failwith "bad index"
  in
    store := f (n,!store)

let rec isval = function
| Evar _ -> false
| Econstant _ -> true
| Eprim _ -> false
| Etuple l -> List.for_all isval l
| Enil
| Econs _ -> false
| Elist _ -> true
| Eref _
| Ederef _
| Eassign _ -> false
| Eloc _
| Etag
| Eunit -> true
| Econstruct(_,expr) -> isval expr
| Eapply _ 
| Elet _
| Eletrec _ -> false
| Efix _ -> false
| Efunction _ -> true
| Esequence _ -> false
| Econdition _ -> false
| Econstraint(expr,_) -> isval expr
| Erecord l -> List.for_all isval (List.map snd l)
| Erecord_access _ -> false
| Ewhen _ -> true

let rec subst expr name expr' = 
match expr with
| Evar n when n = name -> expr'
| Evar _ -> expr
| Econstant _
| Eprim _ -> expr
| Etuple l -> Etuple(List.map (fun e-> subst e name expr') l)
| Enil -> expr
| Econs(car,cdr) -> Econs(subst car name expr', subst cdr name expr')
| Elist l -> Elist(List.map (fun e->subst e name expr') l)
| Eref e -> Eref(subst e name expr')
| Ederef e -> Ederef(subst e name expr')
| Eassign(lhs,rhs) -> Eassign(subst lhs name expr',subst rhs name expr')
| Eloc _
| Etag 
| Eunit -> expr
| Econstruct(tag,expr) -> Econstruct(tag, subst expr name expr')
| Eapply(expr,l) -> Eapply(subst expr name expr',List.map (fun e->subst e name expr') l)
| Elet (l,expr) -> Elet(List.map (fun pe -> (fst pe, subst (snd pe) name expr')) l, subst expr name expr')
| Eletrec(l,expr) -> Eletrec(List.map (fun pe -> (fst pe, subst (snd pe) name expr')) l, subst expr name expr')
| Efix(p,e) -> Efix(p,e)
| Efunction l -> Efunction(List.map (fun pe -> (fst pe, subst (snd pe) name expr')) l)
| Esequence(lhs,rhs) -> Esequence(subst lhs name expr',subst rhs name expr')
| Econdition(expr1,expr2,expr3)-> Econdition(subst expr1 name expr',subst expr2 name expr',subst expr3 name expr')
| Econstraint(expr,ty) -> Econstraint(subst expr name expr',ty)
| Erecord l ->Erecord(List.map (fun field->(fst field,subst (snd field) name expr')) l)
| Erecord_access(expr,label) -> Erecord_access(subst expr name expr',label)
| Ewhen(lhs,rhs) -> Ewhen(subst lhs name expr',subst rhs name expr')

let eval_prim_unary prim x =
match prim with
| Bnot -> do_bool (not) x
| Bnegint -> do_int (~-) x
| Blnot -> do_int (lnot) x
| Bnegfloat -> do_float (~-.) x
| Bintoffloat -> do_float_to_int int_of_float x
| Bfloatofint -> do_int_to_float float_of_int x
| Bintofchar -> do_char_to_int int_of_char x
| Bcharofint -> do_int_to_char char_of_int x
| Bstringofbool -> do_bool_to_string string_of_bool x
| Bboolofstring -> do_string_to_bool bool_of_string x
| Bstringofint -> do_int_to_string string_of_int x
| Bintofstring -> do_string_to_int int_of_string x
| Bstringoffloat -> do_float_to_string string_of_float x
| Bfloatofstring -> do_string_to_float float_of_string x
| Bfailwith -> raise  (InterpreterError (get_string (get_constant x)))
| _ -> failwith "ecal_prim_unary"

let rec eval_prim_eq x y = match (x,y) with
| (Econstant l, Econstant r) -> l = r
| (Etuple l, Etuple r) -> List.for_all2 eval_prim_eq l r
| (Elist l, Elist r) -> List.for_all2 eval_prim_eq l r
| (Eloc l, Eloc r) -> eval_prim_eq (lookuploc l) (lookuploc r)
| (Etag, Etag) -> true
| (Eunit, Eunit) -> true
| (Econstruct(ln,l), Econstruct(rn,r)) when ln = rn -> eval_prim_eq l r
| (Erecord ls, Erecord rs) -> List.for_all (fun (n,e) -> eval_prim_eq (List.assoc n ls) e) rs
| (Eprim _, Eprim _) -> raise (InterpreterError "comparison between functions")
| (Efunction _, Efunction _) -> raise (InterpreterError "comparison between functions")
| (_,_) -> failwith "eval_prim_eq"

let rec eval_prim_eq_imm x y = match (x,y) with
| (Econstant l, Econstant r) -> l = r
| (Etuple l, Etuple r) -> List.for_all2 eval_prim_eq_imm l r
| (Elist l, Elist r) -> List.for_all2 eval_prim_eq_imm l r
| (Eloc l, Eloc r) -> l = r
| (Etag, Etag) -> true
| (Eunit, Eunit) -> true
| (Econstruct(ln,l), Econstruct(rn,r)) when ln = rn -> eval_prim_eq_imm l r
| (Erecord ls, Erecord rs) -> List.for_all (fun (n,e) -> eval_prim_eq_imm (List.assoc n ls) e) rs
| (Eprim _, Eprim _) -> raise (InterpreterError "comparison between functions")
| (Efunction _, Efunction _) -> raise (InterpreterError "comparison between functions")
| (_,_) -> failwith "eval_prim_eq"

let eval_prim_binary prim x y =
match prim with
| Beq -> Econstant (Cbool (eval_prim_eq x y)) 
| Bnq -> Econstant (Cbool (not (eval_prim_eq x y)))
| Blt ->
  let ret =
  match get_constant x, get_constant y with
  | Cint x, Cint y -> Cbool((<) x y)
  | Cbool x, Cbool y -> Cbool((<) x y)
  | Cfloat x, Cfloat y -> Cbool((<) x y)
  | Cstring x, Cstring y -> Cbool((<) x y)
  | Cchar x, Cchar y -> Cbool((<) x y)
  | _ -> failwith "eval_prim_binary"
  in Econstant ret
| Bgt ->
  let ret =
  match get_constant x, get_constant y with
  | Cint x, Cint y -> Cbool((>) x y)
  | Cbool x, Cbool y -> Cbool((>) x y)
  | Cfloat x, Cfloat y -> Cbool((>) x y)
  | Cstring x, Cstring y -> Cbool((>) x y)
  | Cchar x, Cchar y -> Cbool((>) x y)
  | _ -> failwith "eval_prim_binary"
  in Econstant ret
| Ble ->  
  let ret =
  match get_constant x, get_constant y with
  | Cint x, Cint y -> Cbool((<=) x y)
  | Cbool x, Cbool y -> Cbool((<=) x y)
  | Cfloat x, Cfloat y -> Cbool((<=) x y)
  | Cstring x, Cstring y -> Cbool((<=) x y)
  | Cchar x, Cchar y -> Cbool((<=) x y)
  | _ -> failwith "eval_prim_binary"
  in Econstant ret
| Bge ->
  let ret =
  match get_constant x, get_constant y with
  | Cint x, Cint y -> Cbool((>=) x y)
  | Cbool x, Cbool y -> Cbool((>=) x y)
  | Cfloat x, Cfloat y -> Cbool((>=) x y)
  | Cstring x, Cstring y -> Cbool((>=) x y)
  | Cchar x, Cchar y -> Cbool((>=) x y)
  | _ -> failwith "eval_prim_binary"
  in Econstant ret
| Beqimm -> Econstant (Cbool (eval_prim_eq_imm x y)) 
| Bnqimm -> Econstant (Cbool (not (eval_prim_eq_imm x y)))
| Band -> do_bool_bin (&&) x y
| Bor -> do_bool_bin (||) x y
| Baddint -> do_int_bin (+) x y
| Bsubint -> do_int_bin (-) x y
| Bmulint -> do_int_bin ( * ) x y
| Bdivint -> do_int_bin (/) x y
| Bmod -> do_int_bin (mod) x y
| Bland -> do_int_bin (land) x y
| Blor -> do_int_bin (lor) x y
| Blxor -> do_int_bin (lxor) x y
| Blsl -> do_int_bin (lsl) x y
| Blsr -> do_int_bin (lsr) x y
| Basr -> do_int_bin (asr) x y
| Baddfloat -> do_float_bin (+.) x y
| Bsubfloat -> do_float_bin (-.) x y
| Bmulfloat -> do_float_bin ( *.) x y
| Bdivfloat -> do_float_bin (/.) x y
| Bpower -> do_float_bin ( **) x y
| Bconcatstring -> do_string_bin (^) x y
| Bconcat ->
  begin match x, y with
  | Elist x, Elist y -> Elist(x @ y)
  | _ -> failwith "eval_prim_binary"
  end
| _ -> failwith "eval_prim_binary"


let rec eval_match pat expr expr'=
 match (pat,expr') with
| (Pwild,_) -> expr
| (Pvar name,_) -> subst expr name expr'
| (Pparams [p],_) -> eval_match p expr expr'
| (Pparams(p::pl),_) -> Efunction((Pparams(pl),eval_match p expr expr')::[])
| (Palias(p,name),_) -> eval_match p (subst expr name expr') expr'
| (Pconstant cst1,Econstant cst2) when cst1 = cst2 -> expr
| (Ptuple pl,Etuple el) -> List.fold_left2 (fun e p e'-> eval_match p e e') expr pl el
| (Pnil,Elist []) -> expr
| (Pcons(car,cdr), Elist (e::el)) -> eval_match cdr (eval_match car expr e) (Elist el)
| (Pref p,Eloc loc) -> eval_match p expr (lookuploc loc)
| (Punit,Eunit)
| (Ptag,Etag) -> expr
| (Pconstruct(name1,pat),Econstruct(name2,expr')) when name1 = name2 ->
  eval_match pat expr expr'
| (Por(p1,p2),_) ->
  begin
    try 
      eval_match p1 expr expr'
    with
    | Failure _ -> eval_match p2 expr expr'
  end
| (Pconstraint(p,_),_) -> eval_match p expr expr'
| (Precord pf,Erecord ef) ->
  List.fold_left (fun e p-> eval_match (snd p) e (List.assoc (fst p) ef)) expr pf
| _ -> failwith "eval_match"

let rec eval_match' pat expr =
 match (pat,expr) with
| (Pwild,_) -> ()
| (Pvar name,_) -> extendcontext name expr
| (Pparams(p::_),_) -> eval_match' p expr
| (Palias(p,name),_) -> extendcontext name expr;eval_match' p expr
| (Pconstant cst1,Econstant cst2) when cst1 = cst2 -> ()
| (Ptuple pl,Etuple el) -> List.iter2 (fun p e-> eval_match' p e) pl el
| (Pnil,Elist []) -> ()
| (Pcons(car,cdr), Elist (e::el)) -> eval_match' car e; eval_match' cdr (Elist el) 
| (Pref p,Eloc loc) -> eval_match' p (lookuploc loc)
| (Punit,Eunit)
| (Ptag,Etag) -> ()
| (Pconstruct(name1,pat),Econstruct(name2,expr)) when name1 = name2 ->
  eval_match' pat expr
| (Por(p1,p2),_) ->
  begin
    try 
      eval_match' p1 expr
    with
    | Failure _ -> eval_match' p2 expr
  end
| (Pconstraint(p,_),_) -> eval_match' p expr
| (Precord pf,Erecord ef) ->
  List.iter (fun p-> eval_match' (snd p) (List.assoc (fst p) ef)) pf
| _ -> failwith "eval_match'"

and eval_matches pat_exprs expr' =
  match pat_exprs with 
  | (p,e)::l -> 
    begin
      try 
        let expr = eval_match p e expr' in
        match expr with
        | Ewhen(flag,expr) ->
          begin match eval flag with
          | Econstant (Cbool true) ->
            expr
          | _ ->
            eval_matches l expr'
          end
        | _ -> expr
      with _ ->
        eval_matches l expr'
    end
  | [] -> raise (InterpreterError "no matching found")

and eval1 = function
| Evar name -> lookupcontext name
| Eprim prim when is_unary prim ->
  Efunction [(Pvar "A",Eapply(Eprim prim,[Evar "A"]))]
| Eprim prim when is_binary prim ->
  Efunction [(Pvar "A",Efunction [(Pvar "B",Eapply(Eprim prim,[Evar "A";Evar "B"]))])]
| Etuple l when not (List.exists isval l) -> Etuple (List.map eval1 l)
| Enil -> Elist []
| Econs(car,cdr) when not (isval car) -> Econs(eval1 car,cdr)
| Econs(car,cdr) when not (isval cdr) -> Econs(car,eval1 cdr)
| Econs(car,Elist cdr) -> Elist (car::cdr)
| Eref expr when isval expr -> Eloc(extendstore expr)
| Eref expr -> Eref (eval1 expr)
| Ederef (Eloc l) -> lookuploc l
| Ederef expr -> Ederef (eval1 expr)
| Eassign(lhs,rhs) when not (isval lhs) ->
  Eassign(eval1 lhs,rhs)
| Eassign(lhs,rhs) when not (isval rhs) ->
  Eassign(lhs,eval1 rhs)
| Eassign(Eloc l,rhs) ->
  updatestore l rhs;
  Eunit
| Econstruct(name,expr) when isval expr ->
  Econstruct(name,expr)
| Econstruct(name,expr) ->
  Econstruct(name,eval1 expr)
| Eapply(Eprim prim,[e]) when not (isval e) ->
  Eapply(Eprim prim,[eval1 e]) 
| Eapply(Eprim prim,[e]) ->
  eval_prim_unary prim e
| Eapply(Eprim prim,[e1;e2]) when not (isval e1)  ->
  Eapply(Eprim prim,[(eval1 e1);e2])
| Eapply(Eprim prim,[e1;e2]) when not (isval e2)  ->
  Eapply(Eprim prim,[e1;(eval1 e2)])
| Eapply(Eprim prim,[e1;e2]) ->
  eval_prim_binary prim e1 e2
| Eapply(e,l) when not (isval e) ->
  Eapply(eval1 e,l)
| Eapply(e,l) when not (List.exists isval l) ->
  Eapply(e,List.map eval1 l)
| Eapply(Efunction pat_exprs,[e]) ->
  eval_matches pat_exprs e
| Eapply(Efunction pat_exprs,e::el) ->
  Eapply(eval_matches pat_exprs e,el)
| Elet(pat_exprs,expr) ->
  List.fold_left (fun e (p,e') -> eval_match p e (eval e')) expr pat_exprs
| Eletrec(pat_exprs,expr) ->
  List.fold_left (fun e (p,e') -> eval_match p e (eval  e')) expr pat_exprs
| Efix(p,e) when not (isval e)  ->
  Efix(p,eval1 e)
| Efix(p,e)  ->
  eval_match p e (Efix(p,e) )
| Esequence(lhs,rhs) when not (isval lhs) ->
  Esequence(eval1 lhs,rhs)
| Esequence(Eunit,rhs) ->
  rhs
| Econdition(Econstant (Cbool true),lhs,_) ->
  lhs
| Econdition(Econstant (Cbool false),_,rhs) ->
  rhs
| Econdition(flag,lhs,rhs) ->
  Econdition(eval1 flag,lhs,rhs)
| Econstraint(expr,_) ->
  expr
| Erecord fields when not (List.exists isval (List.map snd fields)) ->
  Erecord (List.map (fun (n,e)->(n,eval1 e)) fields)
| Erecord_access (expr,label) when not (isval expr) ->
  Erecord_access(eval1 expr,label)
| Erecord_access(Erecord fields, label) ->
  List.assoc label fields
| expr when (isval expr) -> expr
| expr -> print_endline (show_expr expr);failwith "eval1"

and eval expr =
  let expr = eval1 expr in
  if isval expr then
    expr
  else 
  try 
    eval expr
  with Failure _ -> print_endline (show_expr expr);failwith "eval"

let eval_let pat_exprs =
  List.iter (fun (p,e) -> eval_match' p (eval e)) pat_exprs


let eval_letrec pat_exprs =
  List.iter (fun (p,e) -> eval_match' p (eval e)) pat_exprs

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
| Tvar{contents=Unbound {id=id;level=level}} when level = generic -> "'" ^ name_of_tvar id
| Tvar{contents=Unbound {id=id;level=_}}  -> "'" ^ "_" ^ name_of_tvar id
| Tvar{contents=Linkto ty} -> pp_ty ty
| Tunit -> "unit"
| Tbool -> "bool"
| Tint  -> "int"
| Tfloat -> "float"
| Tchar -> "char"
| Tstring -> "string"
| Tlist ty -> (pp_ty ty) ^ " list"
| Tref ty -> (pp_ty ty) ^ " ref"
| Tarrow(l,r) -> let pp_l = pp_ty l in "(" ^ pp_l ^ " -> " ^ (pp_ty r) ^ ")"
| Ttuple(x::xl) -> let pp_x = pp_ty x in "(" ^ pp_x ^ (List.fold_left (fun s x -> s ^ " * " ^ (pp_ty x)) "" xl) ^ ") "
| Tconstr(name, []) -> name
| Tconstr(name, x::[]) -> (pp_ty x) ^ " " ^ name
| Tconstr(name, x::xl) -> let pp_x = pp_ty x in "(" ^ pp_x ^ (List.fold_left (fun s x -> s ^ "," ^ (pp_ty x)) "" xl) ^ ") " ^ name
| Trecord(name,[],_) -> name
| Trecord(name,x::[],_) -> (pp_ty x) ^ " " ^ name
| Trecord(name,x::xl,_) -> let pp_x = pp_ty x in "(" ^ pp_x ^ (List.fold_left (fun s x -> s ^ "," ^ (pp_ty x)) "" xl) ^ ") " ^ name
| Tvariant(name,[],_) -> name
| Tvariant(name,x::[],_) -> (pp_ty x) ^ " " ^ name
| Tvariant(name,x::xl,_) -> let pp_x = pp_ty x in "(" ^ pp_x ^ (List.fold_left (fun s x -> s ^ "," ^ (pp_ty x)) "" xl) ^ ") " ^ name
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
  in "type " ^ n ^ " = {" ^ name ^ " = " ^ pp_ty ty ^ pp_fields tl ^ "}"
| Drecord(n,x::[],(name,ty)::tl) -> 
  let rec pp_fields = function
  | [] -> ""
  | (name,ty)::xl -> "; " ^ name ^ " = " ^ pp_ty ty ^ pp_fields xl
  in "type " ^ pp_ty x ^ " " ^ n ^ " = {" ^ name ^ " = " ^ pp_ty ty  ^ pp_fields tl ^ "}"
| Drecord(n,x::xl,(name,ty)::tl) -> 
  let rec pp_fields = function
  | [] -> ""
  | (name,ty)::xl -> "; " ^ name ^ " = " ^ pp_ty ty ^ pp_fields xl
  in 
  let pp_x = pp_ty x in
  "type " ^ "(" ^ pp_x ^ List.fold_left (fun s x-> s ^ "," ^ pp_ty x) "" xl ^ ")" ^ " " ^ n ^ " = {" ^ name ^ " = " ^ pp_ty ty ^ pp_fields tl ^ "}"

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

let rec pp_exp n = function
| Econstant cst -> pp_cst cst
| Eprim _ -> "<fun>"
| Etuple(x::xl) -> "(" ^ (pp_exp n x) ^ (List.fold_left (fun s x -> s ^ ", " ^ (pp_exp n x)) "" xl) ^ ")"
| Elist [] -> "[]"
| Elist(x::[]) -> "[" ^ (pp_exp n x) ^ "]"
| Elist(x::xl) -> "[" ^ (pp_exp n x) ^ (List.fold_left (fun s x -> s ^ "; " ^ (pp_exp n x)) "" xl) ^ "]"
| Eloc l -> if n < 5 then "ref " ^ pp_exp (n + 1) (lookuploc l) else "<ref>"
| Eunit -> "()"
| Econstruct(name,Etag) -> name
| Econstruct(name,expr) -> name ^ " " ^ (pp_exp n expr) 
| Efix _ -> "<fun>"
| Efunction _ -> "<fun>"
| Erecord((name,x)::[]) -> let pp_x = pp_exp n x in "{" ^ name ^ " = " ^ pp_x ^ "}"
| Erecord((name,x)::xl) -> let pp_x = pp_exp n x in "{" ^ name ^ " = " ^ pp_x ^ (List.fold_left (fun s (name,x) -> s ^ "; " ^ name ^ " = " ^ (pp_exp n x)) "" xl) ^ "}"
| _ -> failwith "pp_exp"

let pp_exp = pp_exp 0