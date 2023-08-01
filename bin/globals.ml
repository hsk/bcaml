open Syntax

type ctx = {tyenv:tyenv;tydecls:type_decl list;mods:ctx list}
[@@deriving show]


let modules = ref {tyenv=[];tydecls=[];mods=[]}

let push_tyenv env = 
  modules := {!modules with tyenv=env@(!modules.tyenv)}

let push_tydecl decl = 
  modules := {!modules with tydecls=decl@(!modules.tydecls)}

let push_module mod_ = 
  modules := {!modules with mods=mod_::!modules.mods}

let get_tyenv () =
  !modules.tyenv