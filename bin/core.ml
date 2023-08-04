open Prims
open Syntax

type store = expr list  
let extendstore store v = (List.length store, List.append store [v])
let lookuploc store l = List.nth store l
let updatestore store n v =
  let rec f s = match s with 
      (0, _::rest) -> v::rest
    | (n, v'::rest) -> v' :: (f (n-1,rest))
    | _ -> failwith "bad index"
  in
    f (n,store)

let rec isval = function
| Evar _
| Econstant _
| Ebuildin _ -> true
| Etuple l -> List.for_all isval l
| Enil -> true
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

let rec subst expr name expr' = match expr with
| Evar n when n = name -> expr'
| Evar _ -> expr
| Econstant _
| Ebuildin _ -> expr
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

let rec eval_match store pat expr expr'= match (pat,expr') with
| (Pwild,_) -> expr
| (Pvar name,_) -> subst expr name expr'
| (Pparams [],_) -> failwith "eval_match"
| (Pparams [p],_) -> eval_match store p expr expr'
| (Pparams(p::pl),_) -> Efunction((Pparams(pl),eval_match store p expr expr')::[])
| (Palias(p,name),_) -> eval_match store p (subst expr name expr') expr'
| (Pconstant cst1,Econstant cst2) when cst1 = cst2 -> expr
| (Ptuple pl,Etuple el) -> List.fold_left2 (fun e p e'-> eval_match store p e e') expr pl el
| (Pnil,Elist []) -> expr
| (Pcons(car,cdr), Elist (e::el)) -> eval_match store cdr (eval_match store car expr e) (Elist el)
| (Pref p,Eloc loc) -> eval_match store p expr (lookuploc store loc)
| (Punit,Eunit)
| (Ptag,Etag) -> expr
| (Pconstruct(name1,pat),Econstruct(name2,expr')) when name1 = name2 ->
  eval_match store pat expr expr'
| (Por(p1,p2),_) ->
  begin
    try 
      eval_match store p1 expr expr'
    with
    | Failure _ -> eval_match store p2 expr expr'
  end
| (Pconstraint(p,_),_) -> eval_match store p expr expr'
| (Precord pf,Erecord ef) ->
  List.fold_left (fun e p-> eval_match store (snd p) e (List.assoc (fst p) ef)) expr pf
| _ -> failwith "eval_match"

let rec eval_matches store pat_exprs expr' =
  match pat_exprs with 
  | (p,e)::l -> 
    begin
      try 
        eval_match store p e expr'
      with _ ->
        eval_matches store l expr'
    end
  | _ -> failwith "eval_matches"

