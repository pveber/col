open Printf

let input_csv_line lexbuf = Array.of_list (Run_col_lexer.csv_row lexbuf)

let input_csv_header ?(strict = false) lexbuf fields =
  let tbl = Hashtbl.create (Array.length fields) in
  Array.iteri 
    (fun j label -> Hashtbl.add tbl label (Some j))
    fields;
  let h = input_csv_line lexbuf in
  let format = Array.make (Array.length fields) (-1) in
  Array.iteri
    (fun i label ->
       try 
	 let data = Hashtbl.find tbl label in
	 match data with 
	     None -> 
	       invalid_arg 
	       (sprintf "CSV input: duplicate field %S in header" 
		  label)
	   | Some j -> 
	       format.(j) <- i;
	       Hashtbl.remove tbl label
       with Not_found -> 
	 if strict then
	   invalid_arg (sprintf "CSV input: unknown field %S in header" label))
    h;
  let missing = ref [] in
  Array.iteri 
    (fun j i ->
       if i < 0 then
	 missing := fields.(j) :: !missing)
    format;
  match List.rev !missing with
      [] -> format
    | l ->
	invalid_arg 
	  (sprintf "CSV input: fields %s are missing"
	     (String.concat ", " l))

let input_csv_lexbuf 
  ?strict ?(noheader = false) fields lexbuf handle_array =
  let line_num = ref 0 in
  let format = 
    if noheader then Array.mapi (fun j name -> j) fields
    else 
      (incr line_num;
       input_csv_header ?strict lexbuf fields) in
  try
    while true do
      incr line_num;
      let a = input_csv_line lexbuf in
      let len = Array.length a in
      handle_array 
	(Array.map (fun j -> 
		      if j < len then a.(j)
		      else 
			invalid_arg 
			  (sprintf 
			     "CSV input, data line %i: missing data fields"
			     !line_num))
	   format);
    done
  with End_of_file -> ()

let input_csv_file 
  ?strict ?noheader fields convert file handle_record =
  let ic = open_in file in
  let handle_array a : unit = handle_record (convert a) in
  try 
    let lexbuf = Lexing.from_channel ic in
    input_csv_lexbuf ?strict ?noheader fields lexbuf handle_array;
    close_in ic
  with e -> 
    close_in_noerr ic;
    raise e

let input_csv_list_file 
  ?strict ?noheader ?(rev = false) fields convert file =
  let accu = ref [] in
  let handle_record r = accu := r :: !accu in
  input_csv_file ?strict ?noheader fields convert file handle_record;
  if not rev then List.rev !accu
  else !accu

let quote buf s =
  Buffer.clear buf;
  let escape = ref (s = "") in
  for i = 0 to String.length s - 1 do
    let c = s.[i] in
    match c with
	' ' | '\t' | '\n' | '\r' | ',' -> 
	  escape := true; 
	  Buffer.add_char buf c
      | '"' ->
	  escape := true;
	  Buffer.add_string buf "\"\""
      | _ -> Buffer.add_char buf c
  done;
  let s' = Buffer.contents buf in
  if !escape then "\"" ^ s' ^ "\""
  else s'

let output_csv_line buf oc sep a =
  let n = Array.length a in
  for i = 0 to n - 2 do
    fprintf oc "%s%c" (quote buf a.(i)) sep
  done;
  fprintf oc "%s\n" (quote buf a.(n-1))


(* imperative output *)
let open_out_csv ?(sep = ',') ?(noheader = false) fields convert file =
  let oc = open_out file in
  let buf = Buffer.create 1024 in
  let closed = ref false in
  if not noheader then
    output_csv_line buf oc sep fields;

  let put r = 
    if !closed then invalid_arg "CSV: cannot output line to closed channel";
    let a = convert r in
    output_csv_line buf oc sep a in

  let close () = 
    closed := true; 
    close_out oc in

  (put, close)


(* output by pulling from a lazy source *)
let output_csv_file ?sep ?noheader fields convert file get_record =
  let put, close = open_out_csv ?sep ?noheader fields convert file in
  let rec loop () =
    match get_record () with
	None -> ()
      | Some r -> put r; loop () in
  try 
    loop (); 
    close ()
  with e -> 
    close ();
    raise e

(* output a whole list *)
let output_csv_list_file ?sep ?noheader fields convert file l =
  let put, close = open_out_csv ?sep ?noheader fields convert file in
  try 
    List.iter put l;
    close ()
  with e -> 
    (try close () with _ -> ()); 
    raise e

let bool_of_string e s =
  try bool_of_string s
  with _ -> raise e

let int_of_string e s =
  try int_of_string s
  with _ -> raise e

let float_of_string e s =
  try float_of_string s
  with _ -> raise e

let any_option_of_string f s =
  if s = "" then None
  else Some (f s)

let string_of_any_option f o =
  match o with
      None -> ""
    | Some x -> f x

let option_of_string s =
  if s = "" then None
  else Some s

let string_of_option o =
  match o with
      None -> ""
    | Some x -> x


let multi_compare l a b =
  let rec loop a b = function
      [] -> 0
    | f :: l ->
	let c = f a b in
	if c = 0 then loop a b l
	else c in
  loop a b l

let compare_opt cmp a b =
  match a, b with
      None, None -> 0
    | None, _ -> -1
    | Some _, None -> 1
    | Some a, Some b -> cmp a b
