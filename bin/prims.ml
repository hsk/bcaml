type prim =
| Beq
| Bnq
| Blt
| Bgt
| Ble
| Bge
| Beqimm
| Bnqimm
| Bnot
| Band 
| Bor
| Bnegint
| Baddint
| Bsubint
| Bmulint
| Bdivint
| Bmod
| Blnot
| Bland
| Blor
| Blxor
| Blsl
| Blsr
| Basr
| Bnegfloat
| Baddfloat
| Bsubfloat
| Bmulfloat
| Bdivfloat
| Bpower
| Bconcatstring
| Bintofchar
| Bcharofint
| Bstringofbool
| Bboolofstring
| Bstringofint
| Bintofstring
| Bstringoffloat
| Bfloatofstring
| Bconcat
[@@deriving show]


let prim_list = [
("=",Beq);
("<>",Bnq);
("<",Blt);
(">",Bgt);
("<=",Ble);
(">=",Bge);
("==",Beqimm);
("!=",Bnqimm);
("not",Bnot);
("&&",Band);
("||",Bor);
("~-",Bnegint);
("+",Baddint);
("-",Bsubint);
("*",Bmulint);
("/",Bdivint);
("mod",Bmod);
("lnot",Blnot);
("land",Bland);
("lor",Blor);
("lxor",Blxor);
("lsl",Blsl);
("lsr",Blsr);
("asr",Basr);
("~-.",Bnegfloat);
("+.",Baddfloat);
("-.",Bsubfloat);
("*.",Bmulfloat);
("/.",Bdivfloat);
("**",Bpower);
("^",Bconcatstring);
("int_of_char",Bintofchar);
("char_of_int",Bcharofint);
("string_of_bool",Bstringofbool);
("bool_of_string",Bboolofstring);
("string_of_int",Bstringofint);
("int_of_string",Bintofstring);
("string_of_float",Bstringoffloat);
("float_of_string",Bfloatofstring);
("@",Bconcat)
]
