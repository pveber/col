{
  open Printf
  let print s = printf "DEBUG: %s\n%!" s
}
let sep = ","
let quote = '"'
let eol = '\r'? '\n'
let space = '\t' | ' '
let nonquotednospace = 
  ([^'\n'',''\r'' ''\t']+ | '\r'[^'\n'','' ''\t'])+
let nonquoted = (space* nonquotednospace)+ as s | space* ("" as s)

rule csv_row = parse
    space* quote  { let field = 
		      String.concat "" (quoted_string lexbuf) in
		    match find_sep lexbuf with
			`Sep -> field :: csv_row lexbuf
		      | `Eol -> [field] }
  | space*        { let field = string lexbuf in
		    match field with
			`Field s -> s :: csv_row lexbuf
		      | `Lastfield s -> [s] }
  | eof           { raise End_of_file }

and find_sep = parse
    space* sep    { `Sep }
  | space* eol    { `Eol }

and quoted_string = parse
    quote quote                { "\"" :: quoted_string lexbuf }
  | quote                      { [] }
  | (_#quote)* as s            { s :: quoted_string lexbuf }
  | eof                        { failwith "non-terminated string" }

and string = parse
    nonquoted space* sep   { `Field s }
  | nonquoted space* eol   { `Lastfield s }
