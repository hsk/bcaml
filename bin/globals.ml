open Syntax

type ctx = {genv:tyenv;tydecls:type_decl list;mods:ctx list}
[@@deriving show]

let modules = ref {genv=[];tydecls=[];mods=[]}