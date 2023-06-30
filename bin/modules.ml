open Syntax

type module = (string * impl_phrase list)

let module_list:module list ref = ref []

let import_list:(string option * string) list ref = ref []