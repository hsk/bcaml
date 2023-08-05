open Prims
open Syntax

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
| Efunction _ -> true
| Esequence _ -> false
| Econdition _ -> false
| Econstraint(expr,_) -> isval expr
| Erecord l -> List.for_all isval (List.map snd l)
| Erecord_access _
| Ewhen _ -> false

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
| Efunction l -> Efunction(List.map (fun pe -> (fst pe, subst (snd pe) name expr')) l)
| Esequence(lhs,rhs) -> Esequence(subst lhs name expr',subst rhs name expr')
| Econdition(expr1,expr2,expr3)-> Econdition(subst expr1 name expr',subst expr2 name expr',subst expr3 name expr')
| Econstraint(expr,ty) -> Econstraint(subst expr name expr',ty)
| Erecord l ->Erecord(List.map (fun field->(fst field,subst (snd field) name expr')) l)
| Erecord_access(expr,label) -> Erecord_access(subst expr name expr',label)
| Ewhen(lhs,rhs) -> Ewhen(subst lhs name expr',subst rhs name expr')

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

let rec eval_matches pat_exprs expr' =
  match pat_exprs with 
  | (p,e)::l -> 
    begin
      try 
        eval_match p e expr'
      with _ ->
        eval_matches l expr'
    end
  | _ -> failwith "eval_matches"

let eval_prim_unary prim x =
match prim with
| Bnot -> do_bool (not) x
| Bnegint -> do_int (~-) x
| Blnot -> do_int (lnot) x
| Bnegfloat -> do_float (~-.) x
| Bintofchar -> do_char_to_int int_of_char x
| Bcharofint -> do_int_to_char char_of_int x
| Bstringofbool -> do_bool_to_string string_of_bool x
| Bboolofstring -> do_string_to_bool bool_of_string x
| Bstringofint -> do_int_to_string string_of_int x
| Bintofstring -> do_string_to_int int_of_string x
| Bstringoffloat -> do_float_to_string string_of_float x
| Bfloatofstring -> do_string_to_float float_of_string x
| _ -> failwith "ecal_prim_unary"

let eval_prim_binary prim x y =
match prim with
| Beq ->
  let ret =
  match get_constant x, get_constant y with
  | Cint x, Cint y -> Cbool((=) x y)
  | Cbool x, Cbool y -> Cbool((=) x y)
  | Cfloat x, Cfloat y -> Cbool((=) x y)
  | Cstring x, Cstring y -> Cbool((=) x y)
  | Cchar x, Cchar y -> Cbool((=) x y)
  | _ -> failwith "eval_prim_binary"
  in Econstant ret
| Bnq ->
  let ret =
  match get_constant x, get_constant y with
  | Cint x, Cint y -> Cbool((<>) x y)
  | Cbool x, Cbool y -> Cbool((<>) x y)
  | Cfloat x, Cfloat y -> Cbool((<>) x y)
  | Cstring x, Cstring y -> Cbool((<>) x y)
  | Cchar x, Cchar y -> Cbool((<>) x y)
  | _ -> failwith "eval_prim_binary"
  in Econstant ret
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
| Beqimm ->
  let ret =
  match get_constant x, get_constant y with
  | Cint x, Cint y -> Cbool((==) x y)
  | Cbool x, Cbool y -> Cbool((==) x y)
  | Cfloat x, Cfloat y -> Cbool((==) x y)
  | Cstring x, Cstring y -> Cbool((==) x y)
  | Cchar x, Cchar y -> Cbool((==) x y)
  | _ -> failwith "eval_prim_binary"
  in Econstant ret
| Bnqimm ->  
  let ret =
  match get_constant x, get_constant y with
  | Cint x, Cint y -> Cbool((!=) x y)
  | Cbool x, Cbool y -> Cbool((!=) x y)
  | Cfloat x, Cfloat y -> Cbool((!=) x y)
  | Cstring x, Cstring y -> Cbool((!=) x y)
  | Cchar x, Cchar y -> Cbool((!=) x y)
  | _ -> failwith "eval_prim_binary"
  in Econstant ret
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

let rec eval1 = function
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
  updatestore l rhs;Eunit
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
  List.fold_left (fun e (p,e') -> eval_match p e (eval1 e')) expr pat_exprs
(*
| Eletrec of (pat * expr) list * expr
*)
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


let rec eval expr =
  let expr = eval1 expr in
  if isval expr then
    expr
  else 
  try 
    eval expr
  with _ -> print_endline (show_expr expr);failwith "eval"