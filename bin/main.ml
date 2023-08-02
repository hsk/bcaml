open Syntax
open Defs

let () =
  let argc = Array.length Sys.argv in
  if argc != 2 then 
    begin
      Format.printf "Usage: ./bcaml [filename]\n";exit (-1)
    end
  else
  let fname = Sys.argv.(1) in
  let inchan = open_in fname in
  let filebuf = Lexing.from_channel inchan in
  try
    let ast = Parser.top Lexer.token filebuf in
    check_ast ast;
    print_endline (show_def_list ast)
  with
  | Failure msg -> print_endline msg
  | Parser.Error -> print_endline "parser error"
  | _ -> print_endline "something went wrong"

