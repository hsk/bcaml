{

}

let lid = ( ['a'-'z'] ['_' 'a'-'z' 'A'-'Z' '0'-'9' '\'']*
            | ['_' 'a'-'z'] ['_' 'a'-'z' 'A'-'Z' '0'-'9' '\'']+)

let uid = ['A'-'Z'] ['_' 'a'-'z' 'A'-'Z' '0'-'9' '\'']*

let int = ['0'-'9'] ['0'-'9' '_']*

let int_ =
    ( ("0x" | "0X") ['0'-'9' 'a'-'f' 'A'-'F'] (['0'-'9' 'a'-'f' 'A'-'F'] | '_')*
    | ("0o" | "0O") ['0'-'7'] ['0'-'7' '_']*
    | ("0b" | "0B") ['0' '1'] ['0' '1' '_']*)

let float =
  '-'? ['0'-'9'] ['0'-'9' '_']*
  (('.' ['0'-'9' '_']*) (['e' 'E'] ['+' '-']? ['0'-'9'] ['0'-'9' '_']*)? |
   ('.' ['0'-'9' '_']*)? (['e' 'E'] ['+' '-']? ['0'-'9'] ['0'-'9' '_']*))




rule token = parse
| '\n'                { Lexing.new_line lexbuf; token lexbuf }
| [' ' '\r' '\t']     { token lexbuf }
| "(*"                { comment 0 lexbuf }
| int                 { INT (int_of_string (Lexing.lexeme lexbuf)) }
| int_                { try
                            INT (int_of_string (Lexing.lexeme lexbuf))
                          with Failure _ -> Error.syntax ~loc:(Location.of_lexeme lexbuf) "Invalid integer constant"
                      }
| float               { FLOAT (float_of_string(Lexing.lexeme lexbuf)) }
| '"'                 { STRING (string "" lexbuf) }
| "(" { LPAR }
| ")" { RPAR }
| "[" { LBRACK }
| "]" { RBRACK }
| "{" { LBRACE }
| "}" { RBRACE }
| "|" { BAR }
| ";;"{ SEMISEMI }
| ";" { SEMI }
| "," { COMMA }
| ":" { COLON }
| "." { DOT }

| "=" { EQ }
| "->" { ARROW }
| "!" { DEREF }
| ":=" { ASSIGN }
| "::" { CONS }

| "+" { ADDOP }
| "-" { SUBOP }
| "*" { MULOP }
| "/" { DIVOP }
| "%" { MODOP }
| "&&" { ANDOP }
| "||" { OROP }
| "^^" { XOROP }
| "<<" { SHLOP }
| ">>" { SHROP }


| "==" { EQOP }
| "<>" { NEOP }
| "<" { LTOP }
| ">" { GTOP }
| "<=" { LEOP }
| ">=" { GEOP }

| "~" { NOTOP }


| "_" { WILD }
| "and" { AND }
| "assert" { ASSERT }
| "case" { CASE }
| "data" { DATA }
| "do" { DO }
| "else" { ELSE }
| "fun" { FUN }
| "if" { IF }
| "in" { IN }
| "import" { IMPORT }
| "let" { LET }
| "of" { OF }
| "rec" { REC }
| "ref" { REF }
| "then" { THEN }
| "type" { TYPE }
| "val" { VAL }
| "with" { WITH }

| lid as s { LID s }
| uid as s { UID s }

| eof { EOF }

| _ {  }


and comment n = parse
| "*)"                {  }
| "(*"                {  }
| '\n'                {  }
| _                   {  }
| eof                 {  }


and char = parse
| [^ '\\' '\''] "'"  {  }
| '\\' ['\\' '\'' 'n' 't' 'b' 'r'] "'" {  }
| [^ '\'']* ("'" | eof) { }

and string = parse
| '"'   { }
| '\\' ['\\' '"' 'n' 't' 'b' 'r'] {  }
| eof {  }
| _ { }