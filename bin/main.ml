(*open Syntax*)
open Defs
open Core

let interp flag inchan =
  let filebuf = Lexing.from_channel inchan in
  try
    if flag then
      begin
        print_string "# ";
        flush stdout;
        let def = Parser.def Lexer.token filebuf in
        check_ast [] def
      end
    else
      let ast = Parser.top Lexer.token filebuf in
      check_ast [] ast
  with
  | InterpreterError msg -> print_endline ("InterpreterError " ^ msg)
  | Failure msg -> print_endline msg
  | Parser.Error -> print_endline "parser error"
  | Not_found -> print_endline "an unbound variable found"
  | _ -> print_endline "something went wrong"

let () =
  let argc = Array.length Sys.argv in
  if argc = 1 then 
    while true do
      interp true stdin
    done
  else if argc = 2 then
    let fname = Sys.argv.(1) in
    let inchan = open_in fname in
    interp false inchan
  else
    begin
      Format.printf "Usage: ./bcaml [filename]\n";exit (-1)
    end