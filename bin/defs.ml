open Syntax
open Typing

let rec check_valid_fields tyl = function
| [] -> true
| (_,Tvar {contents=Unbound{id=id;level=_}})::rest ->
  List.exists (occursin id) tyl && check_valid_fields tyl rest
| _::rest ->
  check_valid_fields tyl rest

