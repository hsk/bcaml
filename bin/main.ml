open Syntax

let () =
  let argc = Array.length Sys.argv in
  if argc != 2 then 
    begin
      Format.printf "Usage: ./block [filename]\n";exit (-1)
    end
  else
  let fname = Sys.argv.(1) in
  let inchan = open_in fname in
  let filebuf = Lexing.from_channel inchan in
  try
    let ast = Parser.top Lexer.token filebuf in
    print_endline (show_def_list ast)
  with
  | Failure msg -> print_endline msg
  | Parser.Error -> print_endline "parser error"
  | _ -> print_endline "something went wrong"

open Defs