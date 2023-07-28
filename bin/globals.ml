open Syntax

type ctx = {tyenv:tyenv;tydecls:type_decl list;mods:ctx list}
[@@deriving show]

let modules = ref {tyenv=[];tydecls=[];mods=[]}