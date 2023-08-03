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

let rec subst expr name expr' = match expr with
| Evar n when n = name -> expr'
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

let rec isval ctx = function
| Evar _
| Econstant _
| Ebuildin _ -> true
| Etuple l -> List.for_all (isval ctx) l
| Enil -> true
| Econs _ -> false
| Elist _ -> true
| Eref _
| Ederef _
| Eassign _ -> false
| Eloc _ -> true
| Etag
| Eunit -> true
| Econstruct(_,expr) -> isval ctx expr
| Eapply _ 
| Elet _
| Eletrec _ -> false
| Efunction _ -> true
| Esequence _ -> false
| Econdition _ -> false
| Econstraint(expr,_) -> isval ctx expr
| Erecord l -> List.for_all (isval ctx) (List.map snd l)
| Erecord_access _
| Ewhen _ -> false