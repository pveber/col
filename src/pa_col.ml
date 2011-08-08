(*
Copyright (c) 2006, 2007 Martin Jambon <martin_jambon@emailuser.net>
All rights reserved.

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions
are met:
1. Redistributions of source code must retain the above copyright
   notice, this list of conditions and the following disclaimer.
2. Redistributions in binary form must reproduce the above copyright
   notice, this list of conditions and the following disclaimer in the
   documentation and/or other materials provided with the distribution.
3. The name of the author may not be used to endorse or promote products
   derived from this software without specific prior written permission.

THIS SOFTWARE IS PROVIDED BY THE AUTHOR ``AS IS'' AND ANY EXPRESS OR
IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES
OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED.
IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY DIRECT, INDIRECT,
INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT
NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF
THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
*)


open Printf
open Lexing
open Camlp4.PreCast

(* for some reason, there is a function in camlp4 that asserts false
   when there are RbNil and RbAnt constructors in a rec_binding. This
   function shyly tries to remove them *)
let rec clean_rec_binding_aux = Ast.(function
  | RbSem (_loc, RbNil _, RbNil _) -> RbNil _loc
  | RbSem (_loc, RbNil _, x) -> x
  | RbSem (_loc, x, RbNil _) -> x
  | RbSem (_loc, x, y) -> RbSem (_loc,
				 clean_rec_binding_aux x, 
				 clean_rec_binding_aux y)
  | x -> x
)

let rec fixpoint f x = 
  let y = f x in 
  if x = y then x
  else fixpoint f y

let clean_rec_binding = fixpoint clean_rec_binding_aux



let rec mapreduce map reduce = function
  | [] -> raise (Invalid_argument "mapreduce")
  | h :: [] -> map h
  | h :: t -> reduce (map h) (mapreduce map reduce t)
  
let check_unique f l =
  let tbl = Hashtbl.create 50 in
  List.iter
    (fun x -> 
       let (_loc, id) = f x in
       if Hashtbl.mem tbl id then
	 Loc.raise _loc
	   (Failure "this tag or label is not unique")
       else Hashtbl.add tbl id ())
    l

let prefix = "__pa_col"
let unique = let n = ref 0 in fun () -> incr n; prefix ^ (string_of_int !n)
let run_item _loc f = <:expr< Run_col_main.$lid:f$ >>

let mod_ctyp (_loc, l) = 
  List.fold_left 
    (fun m id ->
       <:ctyp< $id: Ast.ident_of_ctyp m$ . $uid:id$ >>)
    <:ctyp< $uid:List.hd l$ >> (List.tl l)

let mod_expr (_loc, l) = 
  List.fold_left (fun m id -> <:expr< $m$ . $uid:id$ >>)
    <:expr< $uid:List.hd l$ >> (List.tl l)

let mod_name (_loc, l) =
  match l with
      [s] -> Some s
    | _ -> None

let poly_type _loc poly l =
  if poly then
    let cases = 
      List.fold_right 
	(fun (id, label) accu -> 
	   <:ctyp< `$id$ | $accu$ >>) l <:ctyp< >> in
    <:ctyp< [ = $cases$ ] >>
  else
    let cases = 
      List.fold_right
	(fun (id, label) accu -> 
	   <:ctyp< $uid:id$ | $accu$ >>) l <:ctyp< >> in
    <:ctyp< [ $cases$ ] >>

let poly_of_string _loc poly l e =
  let cases =
    List.fold_right
      (fun (id, label) accu -> 
	 let e =
	   if poly then <:expr< ` $id$ >>
	   else <:expr< $uid:id$ >> in
	 <:match_case< $str: String.escaped label$ -> $e$ | $accu$ >>)
      l <:match_case< _ -> raise $uid:e$ >> in
  <:expr< fun [ $cases$ ] >>

let poly_to_string _loc poly l =
  let cases =
    List.fold_right
      (fun (id, label) accu -> 
	 let p =
	   if poly then <:patt< ` $id$ >> 
	   else <:patt< $uid:id$ >> in
	 <:match_case< $p$ -> $str: String.escaped label$ | $accu$ >>)
      l <:match_case< >> in
  <:expr< fun [ $cases$ ] >>

let poly_to_int _loc poly l =
  let n, cases =
    List.fold_left 
      (fun (n, cases) (id, label) -> 
	 let p = 
	   if poly then <:patt< ` $id$ >> 
	   else <:patt< $uid:id$ >> in 
	 (n + 1,
	  <:match_case< $cases$ | $p$ -> $int: string_of_int n$ >>))
      (0, <:match_case< >>) l in
  <:expr< fun [ $cases$ ] >>

let poly_of_int _loc poly l e =
  let n, cases =
    List.fold_left 
      (fun (n, l) (id, cases) -> 
	 let e =
	   if poly then <:expr< ` $id$ >>
	   else <:expr< $uid:id$ >> in
	 (n + 1,
	  <:match_case< $int:string_of_int n$ -> $e$ | $l$ >>))
      (0, <:match_case< >>) l in
  <:expr< fun [ $cases$ | _ -> raise $uid:e$ ] >>

let expand_tag _loc name predef poly l =
  let type_def = 
    if predef then <:str_item< >>
    else <:str_item< type $lid:name$ = $poly_type _loc poly l$ >> in
  <:str_item< 
    $type_def$;
    module $uid:String.capitalize name$ = 
    struct
      type t = $lid:name$;
      exception Bad_format;
      value of_string = $poly_of_string _loc poly l "Bad_format"$;
      value to_string = $poly_to_string _loc poly l$;
      value of_int = $poly_of_int _loc poly l "Bad_format"$;
      value to_int = $poly_to_int _loc poly l$;
      value compare a b = Pervasives.compare (to_int a) (to_int b);
    end;
  >>


let convert _loc name (typ, opt) =
  let conv =
    match typ with
	`String ->
	  (<:ctyp< string >>,
	   None,
	   None,
	   Some "string",
	   <:expr< String.compare >>)
      | `Bool ->
	  (<:ctyp< bool >>,
	   Some <:expr< $run_item _loc "bool_of_string"$ Bad_format >>,
	   Some <:expr< string_of_bool >>,
	   Some "bool",
	   <:expr< Pervasives.compare >>)
      | `Poly l ->
	  (poly_type _loc true l,
	   Some (poly_of_string _loc true l "Bad_format"),
	   Some (poly_to_string _loc true l),
	   None,
	   <:expr< fun a b -> 
	     Pervasives.compare 
	       ($poly_to_int _loc true l$ a)
	       ($poly_to_int _loc true l$ b) >>)
      | `Int ->
	  (<:ctyp< int >>,
	   Some <:expr< $run_item _loc "int_of_string"$ Bad_format >>,
	   Some <:expr< string_of_int >>,
	   Some "int",
           <:expr< Pervasives.compare >>)
      | `Float -> 
	  (<:ctyp< float >>,
	   Some <:expr< $run_item _loc "float_of_string"$ Bad_format >>,
	   Some <:expr< string_of_float >>,
	   Some "float",
	   <:expr< Pervasives.compare >>)
      | `Module m -> 
	  let m_ctyp = mod_ctyp m
	  and m_expr = mod_expr m
	  and m_name = mod_name m in
	  (<:ctyp< $id:Ast.ident_of_ctyp m_ctyp$ . t >>,
	   Some <:expr< $m_expr$ . of_string >>,
	   Some <:expr< $m_expr$ . to_string >>,
	   m_name,
	   <:expr< $m_expr$.compare >>) in
  let add_suffix = function
      None -> None
    | Some s -> Some (s ^ "_option") in
  let compare_opt cmp =
    <:expr< $run_item _loc "compare_opt"$ $cmp$ >> in

  let t, of_s, to_s, s, cmp =
    if not opt then conv
    else
      match conv with
	  (t, Some of_s, Some to_s, s, cmp) ->
	    let app e1 e2 = <:expr< $e1$ $e2$ >> in
	    (<:ctyp< option $t$ >>,
	     Some (app (run_item _loc "any_option_of_string") of_s),
	     Some (app (run_item _loc "string_of_any_option") to_s), 
	     add_suffix s,
	     compare_opt cmp)
	| (t, None, None, s, cmp) ->
	    (<:ctyp< option $t$ >>,
	     Some (run_item _loc "option_of_string"),
	     Some (run_item _loc "string_of_option"),
	     add_suffix s,
	     compare_opt cmp)
	| _ -> assert false in
  (object
     method t = t
     method of_string = of_s
     method to_string = to_s
     method of_string_fun = 
       match of_s with
	   None -> <:expr< fun ( s : string ) -> s >>
	 | Some f -> f
     method to_string_fun =
       match to_s with
	   None -> <:expr< fun ( s : string ) -> s >>
	 | Some f -> f
     method name = s
     method compare = cmp
   end)


let error _loc s =
  Loc.raise _loc (Failure s)

let get_tuple_field ?t ?arg _loc addr record_length =
  let a = Array.init record_length (fun i ->
				      if i = addr then <:patt< x >>
				      else <:patt< _ >>) in
  let tup = 
    Array.fold_left (fun accu p -> <:patt< $accu$, $p$ >>) <:patt< >> a in
  let p0 = <:patt< $tup:tup$ >> in
  let p = 
  match t with 
      None -> p0
    | Some typ -> <:patt< ( $p0$ : $typ$ ) >> in
  match arg with
      None -> <:expr< fun $p$ -> x >>
    | Some e -> <:expr< let $p$ = $e$ in x >>

let get_by_type _loc kind l =
  let tbl = Hashtbl.create 50 in
  List.iter 
    (fun (_loc, addr, mut, name, label, conv, default) ->
       match conv#name with 
	   Some t ->
	     let r = 
	       try Hashtbl.find tbl t 
	       with Not_found -> 
		 let r = ref [] in
		 Hashtbl.add tbl t r;
		 r in
	     r := (name, label, addr) :: !r
	 | None -> ())
    l;
  let clusters = Hashtbl.fold (fun t r l -> (t, List.rev !r) :: l) tbl [] in
  let record_length = List.length l in
  let str_items =
    List.map
      (fun (t, l) -> 
	 let field_error = 
	   <:match_case< s -> raise (Invalid_field s) >> in
	 let label_error = 
	   <:match_case< s -> raise (Invalid_label s) >> in
	 let field_cases, label_cases = 
	   List.fold_right 
	     (fun (field, label, addr) (field_cases, label_cases) -> 
		let f = 
		  match kind with
		      `Record -> (<:expr< fun ( r : t ) -> r.$lid:field$ >>)
		    | `Tuple -> 
			get_tuple_field ~t:<:ctyp< t >> _loc addr record_length
		    | `Object -> (<:expr< fun ( o : t ) -> o#$lid:field$ >>) in
		(<:match_case< $str:String.escaped field$ -> $f$ 
		             | $field_cases$ >>,
		 <:match_case< $str:String.escaped label$ -> $f$
			     | $label_cases$ >>))
	     l (field_error, label_error) in
	 <:str_item< 
	     value $lid:"type_"^t^"_field"$ = fun [ $field_cases$ ];
             value $lid:"type_"^t^"_label"$ = fun [ $label_cases$ ]; 
         >>)
      clusters in
  <:str_item<
    exception Invalid_field of string;
    exception Invalid_label of string;
    $list:str_items$;
  >>         

let rec_binding_of_iel _loc l = 
  mapreduce
    (fun (id, expr) -> <:rec_binding< $lid:id$ = $expr$ >>)
    (fun x y -> <:rec_binding< $x$ ; $y$ >>)
    l

let expand _loc name predef l =
  begin
    (* sanity checks *)
    let labels = Hashtbl.create 50 in
    List.iter 
      (fun (_loc, addr, mut, name, label, conv, default) -> 

	 (* testing for repeated labels (which may not be equal to 
	    the record field names) *)
	 if Hashtbl.mem labels label then
	   error _loc (sprintf "label %s is not unique" label);

	 (* avoiding set_ prefix, in order to define read methods
	    without a get_ prefix *)
	 Hashtbl.add labels label ();
	 if String.length name >= 4 then
	   let prefix = String.sub name 0 4 in
	   if prefix = "set_" then
	     error _loc "field names cannot start with \"set_\"")
      l
  end;

  let record_length = List.length l in

  let type_def =
    if predef then <:str_item< >>
    else
      let fields = 
	List.fold_right 
	  (fun (_loc, addr, mut, name, label, conv, default) accu ->
	     let t = conv#t in
	     let t = if mut then <:ctyp< mutable $t$ >> else t in
	     let field = <:ctyp< $lid:name$ : $t$ >> in
	     <:ctyp< $field$ ; $accu$ >>)
	  l <:ctyp< >> in
      <:str_item< type $lid:name$ = { $fields$ } >> in

  let tuple_type_def =
    let types =
      List.fold_right
	(fun (_loc, addr, mut, name, label, conv, default) t -> 
	   <:ctyp< $conv#t$ * $t$ >>)
	l <:ctyp< >> in
    <:str_item< type t = $tup:types$ >> in

  let functions =
    let create_record, create_tuple =
      let record_expr =
	let field_expr (_loc, addr, mut, name, label, conv, default) =
	  <:rec_binding< $lid:name$ = $lid:name$ >> in
	let rbs = mapreduce field_expr (fun x y -> <:rec_binding< $x$ ; $y$ >>) l in
	<:expr< fun () -> $Ast.ExRec (_loc, rbs, Ast.ExNil _loc)$ >> in
      let tuple_expr =
	let t =
	  List.fold_right
	    (fun (_loc, addr, mut, name, label, conv, default) accu -> 
	       <:expr< ( $lid:name$ : $conv#t$ ), $accu$ >>)
	    l <:expr< >> in
	<:expr< fun () -> $tup:t$ >> in

      let create e =
	List.fold_right
	  (fun (_loc, addr, mut, name, label, conv, default) e ->
	     match default with
		 None ->
		   <:expr< fun ~ $name$ -> $e$ >>
		     | Some x ->
			 <:expr< fun ? ($lid:name$ = $x$) -> $e$ >>)
	  l e in

      (create record_expr, create tuple_expr) in
  
    let class_fun =
      let class_items = 
	List.map
	  (fun (_loc, addr, mut, name, label, conv, 
		default) ->
	     let typ = conv#t in
	     let mutable_mod = if mut then Ast.MuMutable else Ast.MuNil in
	     let common =
	       <:class_str_item< 
		 value $mutable:mutable_mod$ $lid:name$ : $typ$ = $lid:name$;
	         method $lid:name$ = $lid:name$;
               >> in
	     if mut then
	       let x = if name <> "x" then "x" else unique () in
	       <:class_str_item< 
	         $common$; 
	         method $lid:"set_"^name$ $lid:x$ = $lid:name$ := $lid:x$;
               >>
             else common) l in

      let obj_expr =
	<:class_expr< fun () -> object $list:class_items$ end >> in

      List.fold_right
	(fun (_loc, addr, mut, name, label, conv, default) e ->
	   match default with
	       None ->
		 <:class_expr< fun ~ $name$ -> $e$ >>
	     | Some x ->
		 <:class_expr< fun ? ($lid:name$ = $x$) -> $e$ >>)
	l obj_expr in


    let fields, labels = 
      List.fold_right
	(fun (_loc, addr, mut, name, label, conv, default) (a, b) -> 
	   <:expr< $str:String.escaped name$ ; $a$ >>,
	   <:expr< $str:String.escaped label$ ; $b$ >>) 
	l (<:expr< >>, <:expr< >>) in

    let field_converters =
      List.fold_right
	(fun (_loc, addr, mut, name, label, conv, default) l -> 
	   (<:binding< $lid:name ^ "_of_string"$ = $conv#of_string_fun$ >>) ::
	   (<:binding< $lid:name ^ "_to_string"$ = $conv#to_string_fun$ >>) :: 
	   l)
	l [] in
    let of_array =
      List.map 
	(fun (_loc, addr, mut, name, label, conv, default) -> 
	   let x = <:expr< a.($int:string_of_int addr$) >> in
	   let e = 
	     match conv#of_string with
		 None -> x 
	       | Some f -> <:expr< $lid:name^"_of_string"$ $x$ >> in
	   name, e)
	l in
    let to_array = 
      List.map 
	(fun (_loc, addr, mut, name, label, conv, default) ->
	   let x = <:expr< r.$lid:name$ >> in
	   match conv#to_string with
	       None -> x 
	     | Some f -> <:expr< $lid:name^"_to_string"$ $x$ >>)
	l in

    let default_comparisons =
      List.map 
	(fun (_loc, addr, mut, name, label, conv, default) ->
	   <:str_item< value $lid:name$ = $conv#compare$ >>)
	l in

    let compare_fields access =
      let cases dir = 
	List.fold_right 
	  (fun (_loc, addr, mut, name, label, conv, default) cases -> 
	     let p = <:patt< $str:name$ >> in
	     let a = 
	       access ~addr ~name ~len:record_length _loc <:expr< a >> in
	     let b = 
	       access ~addr ~name ~len:record_length _loc <:expr< b >> in
	     let cmp = <:expr< Compare.$lid:name$ >> in
	     let e = 
	       match dir with
		   `Up -> <:expr< fun a b -> $cmp$ $a$ $b$ >>
	         | `Down -> <:expr< fun a b -> $cmp$ $b$ $a$ >> in
	     <:match_case< $p$ -> $e$ | $cases$ >>)
	l <:match_case< s -> raise (Invalid_field s) >> in
      let up_cases = cases `Up in
      let down_cases = cases `Down in
      let f = <:expr< fun [ `Up s -> 
			      match s with [ $up_cases$ ]
			  | `Down s -> 
			      match s with [ $down_cases$ ]
			  | `Custom f -> f ] >> in
      <:expr< fun l -> $run_item _loc "multi_compare"$ (List.map $f$ l) >> in

    let compare_fields_r = 
      compare_fields 
	(fun ~addr ~name ~len _loc e -> <:expr< $e$ . $lid:name$ >>) in
    let compare_fields_t = 
      compare_fields 
	(fun ~addr ~name ~len _loc e -> 
	   (*get_tuple_field ~t:<:ctyp< t >> ~arg:e _loc addr len*)
	   <:expr< $lid:"get_"^name$ $e$ >>) in
    let compare_fields_o = 
      compare_fields 
	(fun ~addr ~name ~len _loc e -> <:expr< $e$ # $lid:name$ >>) in
    
	
    let compare_labels access =
      let cases dir = 
	List.fold_right 
	  (fun (_loc, addr, mut, name, label, conv, default) cases -> 
	     let p = <:patt< $str:label$ >> in
	     let a = 
	       access ~addr ~name ~len:record_length _loc <:expr< a >> in
	     let b = 
	       access ~addr ~name ~len:record_length _loc <:expr< b >> in
	     let cmp = <:expr< Compare.$lid:name$ >> in
	     let e = 
	       match dir with
		   `Up -> <:expr< fun a b -> $cmp$ $a$ $b$ >>
	         | `Down -> <:expr< fun a b -> $cmp$ $b$ $a$ >> in
	     <:match_case< $p$ -> $e$ | $cases$ >>)
	l <:match_case< s -> raise (Invalid_label s) >> in
      let up_cases = cases `Up in
      let down_cases = cases `Down in
      let f = <:expr< fun [ `Up s -> 
			      match s with [ $up_cases$ ]
			  | `Down s -> 
			      match s with [ $down_cases$ ]
			  | `Custom f -> f ] >> in
      <:expr< fun l -> $run_item _loc "multi_compare"$ (List.map $f$ l) >> in



    let compare_labels_r = 
      compare_labels 
	(fun ~addr ~name ~len _loc e -> <:expr< $e$ . $lid:name$ >>) in
    let compare_labels_t = 
      compare_labels 
	(fun ~addr ~name ~len _loc e -> 
	   (*get_tuple_field ~t:<:ctyp< t >> ~arg:e _loc addr len*)
	   <:expr< $lid:"get_"^name$ $e$ >>) in
    let compare_labels_o = 
      compare_labels 
	(fun ~addr ~name ~len _loc e -> <:expr< $e$ # $lid:name$ >>) in

    let tup_of_array =
      let t = 
	List.fold_right 
	  (fun (_loc, addr, mut, name, label, conv, default) t -> 
	     let x = <:expr< a.($int:string_of_int addr$) >> in
	     let e =
	       match conv#of_string with
		   None -> x 
		 | Some f -> <:expr< $lid:name^"_of_string"$ $x$ >> in
	     <:expr< $e$, $t$ >>)
	  l <:expr< >> in
      <:expr< fun a -> $tup:t$ >> in

    let tup_of_record =
      let t =
	List.fold_right
	  (fun (_loc, addr, mut, name, label, conv, default) t -> 
	     <:expr< r.$lid:name$, $t$ >>)
	  l <:expr< >> in
      <:expr< fun r -> ( $tup:t$ : t ) >> in

    let tup_to_array = 
      let pl, el =
	List.fold_right 
	  (fun (_loc, addr, mut, name, label, conv, default) (pl, el) ->
	     let pl = <:patt< $lid:name$, $pl$ >> in
	     let x = <:expr< $lid:name$ >> in
	     let e =
	       match conv#to_string with
		   None -> x
		 | Some f -> <:expr< $lid:name^"_to_string"$ $x$ >> in
	     let el = <:expr< $e$ ; $el$ >> in
	     (pl, el))
	  l (<:patt< >>, <:expr< >>) in
      <:expr< fun $tup:pl$ -> [| $el$ |] >> in

    let tup_to_record = 
      let t, fields =
	List.fold_right 
	  (fun (_loc, addr, mut, name, label, conv, default) (t, fields) ->
	     <:patt< $lid:name$, $t$ >>, 
	     <:rec_binding< $lid:name$ = $lid:name$ ; $fields$ >>)
	  l (<:patt< >>, <:rec_binding< >>) in
	<:expr< fun ( $tup:t$ : t ) -> $Ast.ExRec (_loc, 
						   clean_rec_binding fields, 
						   Ast.ExNil _loc)$ >> in

    let tup_get =
      let pel = 
	List.map 
	  (fun (_loc, addr, mut, name, label, conv, default) ->
	     let e =
	       get_tuple_field ~t:<:ctyp< t >> _loc addr record_length in
	     <:binding< $lid:"get_"^name$ = $e$ >>)
	  l in
      <:str_item< value $list:pel$ >> in

    let obj_of_array =
      let f =
	List.fold_left
	  (fun f (_loc, addr, mut, name, label, conv, default) -> 
	     let x = <:expr< a.($int:string_of_int addr$) >> in
	     let e = 
	       match conv#of_string with
		   None -> x 
		 | Some f -> <:expr< $lid:name^"_of_string"$ $x$ >> in
	     <:expr< $f$ ~ $name$ : $e$ >>)
	  <:expr< new t >> l in
      <:expr< $f$ () >> in

    let obj_of_record =
      let f =
	List.fold_left
	  (fun f (_loc, addr, mut, name, label, conv, default) -> 
	     <:expr< $f$ ~ $name$ : r.$lid:name$ >>)
	  <:expr< new t >> l in
      <:expr< $f$ () >> in

    let obj_to_array = 
      List.map 
	(fun (_loc, addr, mut, name, label, conv, default) ->
	   let x = <:expr< o#$lid:name$ >> in
	   match conv#to_string with
	       None -> x 
	     | Some f -> <:expr< $lid:name^"_to_string"$ $x$ >>)
	l in

    let obj_to_record = 
      List.map 
	(fun (_loc, addr, mut, name, label, conv, default) ->
	   name, <:expr< o#$lid:name$ >>)
	l in

    let app s = run_item _loc s in
    let load =
      <:expr< fun ?strict ?noheader file f ->
	$app "input_csv_file"$
	?strict ?noheader labels of_array file f >> in
    let load_list =
      <:expr< fun ?strict ?noheader ?rev file ->
	  $app "input_csv_list_file"$ 
	  ?strict ?noheader ?rev labels of_array file >> in
    let output = 
      <:expr< fun ?sep ?noheader file -> 
	  $app "open_out_csv"$ ?sep ?noheader labels to_array file >> in
    let save = 
      <:expr< fun ?sep ?noheader file f -> 
	  $app "output_csv_file"$ ?sep ?noheader labels to_array file f >> in
    let save_list =
      <:expr< fun ?sep ?noheader file l -> 
	 $app "output_csv_list_file"$ 
	   ?sep ?noheader labels to_array file l >> in

    let type_get_record = get_by_type _loc `Record l in
    let type_get_tuple = get_by_type _loc `Tuple l in   
    let type_get_object = get_by_type _loc `Object l in   

    let indices = 
      List.map
	(fun (_loc, addr, mut, name, label, conv, default) ->
	   <:str_item< value $lid:name$ = $int:string_of_int addr$ >>) l in
    let tdef = 
      if name = "t" then (* does anyone have a better solution? *)
	<:str_item< 
          type t' = t;
	  type t = t';
        >>
      else
	<:str_item< type t = $lid:name$ >> in

    <:str_item<
    module $uid:String.capitalize name$ = 
    struct 
      value create = $create_record$;
      value create_tuple = $create_tuple$;
      class obj = $class_fun$;
      exception Bad_format;
      value $list:field_converters$;
      $tdef$;
      module Index = struct $list:indices$ end;
      module Compare = struct $list:default_comparisons$ end;
      value fields = [| $fields$ |];
      value labels = [| $labels$ |];
      value of_array a = { $rec_binding_of_iel _loc of_array$ };
      value to_array r = [| $Ast.exSem_of_list to_array$ |];
      $type_get_record$;
      value load_csv_rows = $load$;
      value load_csv = $load_list$;
      value open_out_csv = $output$;
      value save_csv_rows = $save$;
      value save_csv = $save_list$;
      value compare_fields = $compare_fields_r$;
      value compare_labels = $compare_labels_r$;
      module Tup =
      struct
      	(); (* <-- bug workaround for camlp4 3.10+beta *)
      	$tuple_type_def$;
        value create = create_tuple;
        value of_array = $tup_of_array$;
      	value to_array = $tup_to_array$;
      	value of_record = $tup_of_record$;
      	value to_record = $tup_to_record$;
        $tup_get$;
        $type_get_tuple$;
      	value load_csv_rows = $load$;
      	value load_csv = $load_list$;
      	value open_out_csv = $output$;
      	value save_csv_rows = $save$;
      	value save_csv = $save_list$;
      	value compare_fields = $compare_fields_t$;
      	value compare_labels = $compare_labels_t$;
      end;
      module OO =
      struct
      	class t = obj;
      	value create = new t;
      	value of_array a = $obj_of_array$;
      	value to_array o = [| $Ast.exSem_of_list obj_to_array$ |];
      	value of_record r = $obj_of_record$;
      	value to_record o = { $rec_binding_of_iel _loc obj_to_record$ };
        $type_get_object$;
      	value load_csv_rows = $load$;
      	value load_csv = $load_list$;
      	value open_out_csv = $output$;
      	value save_csv_rows = $save$;
      	value save_csv = $save_list$;
      	value compare_fields = $compare_fields_o$;
      	value compare_labels = $compare_labels_o$;
      end;
    end >> in

  let defs = [ type_def; functions ] in
  <:str_item< $list:defs$ >>

open Syntax

let add_addr l =
  let len, l' =
  List.fold_left 
    (fun (i, l) (_loc, mut, name, aliases, typ, default) ->
       (i + 1, (_loc, i, mut, name, aliases, typ, default) :: l))
    (0, [])
    l in
  List.rev l'

let unopt default = function
    None -> default
  | Some x -> x

let eval_string s = Camlp4.Struct.Token.Eval.string ~strict:() s

EXTEND Gram
  GLOBAL: str_item;
  str_item: LEVEL "top" [
    [ "type" ; LIDENT "col"; name = LIDENT; "="; 
      predef = OPT [ LIDENT "predefined" ];
      "{"; l = col_list; "}" -> expand _loc name (predef <> None) (add_addr l)
    | "type"; LIDENT "tag"; name = LIDENT; "="; 
      predef = OPT [ LIDENT "predefined" ];
      v = variants ->
	let poly, l = v in
	expand_tag _loc name (predef <> None) poly l ]
  ];

  variants: [
    [ l = poly -> (true, l)
    | l = classic -> (false, l) ]
  ];

  poly: [
    [ "["; l = LIST1 [ "`"; id = [ id = ident -> (_loc, id) ]; 
		       label = OPT [ s = STRING -> 
				       (_loc, eval_string s) ] -> 
			 (id, unopt id label) ] SEP "|";
      "]" -> 
	check_unique fst l;
        check_unique snd l;
	List.map (fun ((_, a), (_, b)) -> (a, b)) l ]
  ];

  classic: [
    [ OPT "|"; 
      l = LIST1 [ id = [ id = UIDENT -> (_loc, id) ]; 
		  label = OPT [ s = STRING ->
				  (_loc, eval_string s) ] -> 
		    (id, unopt id label) ] SEP "|" -> 
      check_unique fst l;
      check_unique snd l;
      List.map (fun ((_, a), (_, b)) -> (a, b)) l ]
  ];

  col: [
    [ mut = OPT "mutable"; 
      name = LIDENT; 
      label = OPT [ s = STRING -> eval_string s ];
      typopt = 
	OPT [ ":"; 
	      typ = [ LIDENT "string" -> `String
		    | LIDENT "bool" -> `Bool
		    | l = poly -> `Poly l
		    | LIDENT "int" -> `Int
		    | LIDENT "float" -> `Float
		    | m = LIST1 [ x = UIDENT -> x ] SEP "." -> 
			`Module (_loc, m) ];
	      o = OPT [ LIDENT "option" ]
		  -> (typ, o <> None) ];
      default = OPT [ "="; e = expr LEVEL "top" -> e] -> 
	let typ =
	  match typopt with 
	      None -> (`String, false )
	    | Some x -> x in
	(_loc,
	 mut <> None,
	 name,
	 (match label with None -> name | Some s -> s),
	 convert _loc name typ,
	 default) ]
  ];

  col_list: [
    [ x = col; ";"; l = SELF -> x :: l
    | x = col; ";" -> [x]
    | x = col -> [x] ]
  ];

  ident: [
    [ id = LIDENT -> id 
    | id = UIDENT -> id ]
  ];
END

