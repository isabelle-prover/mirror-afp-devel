(*
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

section "Record Antiquotation"

theory ML_Record_Antiquotation
  imports Main
begin

subsection \<open>Motivation\<close>
text \<open>
A shortcoming of ML records is the lack of proper update / map functions for the record fields.
Manually defining those update functions is considered as painful, as it requires 'quadratic' 
editing when adding a new field:
 - add the new field to every record pattern (in every already defined update / map function)
 - add a new update / map function for the field.

Various workarounds have been proposed. E.g.
- Using mutable references as fields to allow for destructive updates
- Fancy higher order function-combinators (Fold): \<^url>\<open>http://mlton.org/FunctionalRecordUpdate\<close>  

Here we develop yet another solution. We provide a ML-Antiquotation that generates the definitions.

For a record specification as datatype \<^verbatim>\<open>datatype 'a foo = Foo {f1:'a, f2:bool}\<close> 
it generates the datatype as specified with one constructor
\<^verbatim>\<open>Foo\<close> wrapping the record and additionally all the 'canonical' functions:
 
\<^item> \<^verbatim>\<open>make_foo\<close>
\<^item> \<^verbatim>\<open>dest_foo\<close>
\<^item> \<^verbatim>\<open>get_f1\<close>
\<^item> \<^verbatim>\<open>get_f2\<close>
\<^item> \<^verbatim>\<open>map_f1\<close>
\<^item> \<^verbatim>\<open>map_f2\<close>

\<close>

subsection \<open>Example\<close>

ML_val \<open>
datatype 'a foo = Foo of {f1:'a, f2:bool};

val make_foo = Foo;
fun dest_foo (Foo r) = r;

fun get_f1 (Foo r) = #f1 r;
fun get_f2 (Foo r) = #f2 r;

fun map_f1 f (Foo {f1, f2})  =
  Foo {f1 = f f1, f2 = f2};
fun map_f2 f (Foo {f1, f2})  = 
  Foo {f1 = f1, f2 = f f2}; 
\<close>

subsection \<open>Implementation\<close>

ML \<open>

structure ML_Record_Antiquotation =
struct

fun remove_comments s =
  let
    val unbalanced_comments_msg = "unbalanced ML comments (* ... *)"
    fun err_unbalanced () = error unbalanced_comments_msg

    fun rem n [] = if n = 0 then [] else err_unbalanced ()
      | rem n ("("::"*"::xs) = rem (n + 1) xs
      | rem n ("*"::")"::xs) = if n > 0 then rem (n - 1) xs else err_unbalanced ()
      | rem n (x::xs) = if n = 0 then x::rem n xs else rem n xs
  in
    s |> Symbol.explode |> rem 0 |> implode
  end

fun to_upper_first s = 
   case String.explode s of 
     [] => "" 
    | c::cs => String.implode ((Char.toUpper c)::cs)

fun split_first [] = raise List.Empty
  | split_first (x :: xs) = (x, xs);

\<comment> \<open>We rely on the ML compiler to check the syntax and only provide a hands-on parser here.\<close>
fun parse_record_declaration s =
  let
    fun is_whitespace c = member (op =) [" ", "\t", "\n"] (str c) 

    fun white_space_explode "" = []
      | white_space_explode s = String.fields (is_whitespace) s |> filter_out (fn x => x = "")

    fun remove p s
      = String.explode s |> filter_out p |> String.implode

    val normalize_spaces = space_implode " " o white_space_explode;

    val remove_delimiter = remove (fn c => member (op =) ["{","(", "}",")",";"] (str c))
    val trim = remove (fn c => str c = " ")

    fun strip_word word s = 
      let 
        val (first, rest) = s |> white_space_explode |> split_first
      in
        if first = word then space_implode " " rest else error ("expecting '" ^ word ^ "'")
      end

    val [lhs, rhs] = s |> remove_comments |> normalize_spaces |> space_explode "=" |> map normalize_spaces

    fun split_first_word s = s |> white_space_explode |> split_first ||> space_implode " "
    fun split_last_word s  = s |> white_space_explode |> split_last  |>> space_implode " "

    fun split_type s = 
      let
        val (params, type_name) = s
          |> strip_word "datatype"
          |> split_last_word
          |>> remove_delimiter
          |>> space_explode ","
      in (params, type_name) end

    val (params, rec_name) = split_type lhs 

    fun is_type_parameter s = String.isPrefix "'" s orelse String.isPrefix "''" s
 
    fun get_params s = s 
      |> white_space_explode 
      |> map remove_delimiter 
      |> map (space_explode ",") 
      |> flat 
      |> filter is_type_parameter

    val (constr, field_names_params) = 
        rhs
        |> split_first_word
        ||> strip_word "of"
        ||> remove_delimiter 
        ||> space_explode "," 
        ||> map (space_explode ":")
        ||> map (fn [name, typ] => (trim name, get_params typ))
       
  in ((lhs, rhs), (params, rec_name), constr, field_names_params) end

fun mk_record fields = enclose "{" "}" (commas fields);

fun make_name record = "make_" ^ record;
fun dest_name record = "dest_" ^ record;
fun map_name field = "map_" ^ field;
fun get_name field = "get_" ^ field;

fun mk_record_ass fields values = 
  fields ~~ values
  |> map (fn (f,v) => f ^ " = " ^ v)
  |> commas
  |> enclose "{" "}"

fun replace p q = map (fn x => if x = p then q else x)

fun mk_map constr fields n =
  let 
    val (field, params) = nth fields n
    val field_names = map fst fields
    val [f] = Name.variant_list field_names ["f"]
  in
    "fun " ^ map_name field ^ 
      " f (" ^ constr ^ " "  ^ mk_record field_names ^ ") " ^ " = \n" ^ 
    "  " ^ constr ^ " " ^ mk_record_ass field_names (replace field (f ^ " " ^ field) field_names) ^ ";"
  end 

fun mk_maps constr fields =
 0 upto (length fields) - 1 
 |> map (mk_map constr fields)
 |> cat_lines

fun mk_get constr field_name =
  "fun " ^ get_name field_name ^ " (" ^ constr ^ " r) = #" ^ field_name ^ " r;";

fun mk_gets constr fields =
  fields |> map fst |> map (mk_get constr) |> cat_lines

fun mk_record_datatype_declaration add_decl s =
  let
    val ((lhs, rhs), record as (params, rec_name), constr, fields) = parse_record_declaration s; 
    val decl = lhs ^ " = " ^ rhs ^ ";";
    val make = "val " ^ make_name rec_name ^ " = " ^ constr ^ ";";
    val dest = "fun " ^ dest_name rec_name ^ " (" ^ constr ^ " r) = r;";  
    val gets = mk_gets constr fields;
    val maps = mk_maps constr fields;
    fun cond_cons P a xs = if P then a::xs else xs
  in
    cat_lines (cond_cons add_decl decl [make, dest, gets, maps])
  end

end
\<close>

text \<open>Test the parser and its output.\<close>

ML_val \<open>
let
  val test = "datatype 'a foo = Foo of {fld1:int, fld2:'a}"
in writeln (ML_Record_Antiquotation.mk_record_datatype_declaration true test) end
\<close>

setup \<open>
ML_Antiquotation.inline_embedded (Binding.make ("record",\<^here>))
  (Scan.lift Parse.embedded_input >> (fn source => 
    let 
      val _ = ML_Lex.read_source source; \<comment> \<open>provide some markup as side effect\<close>
      val sanitized_str = fst (Input.source_content source) |> ML_Lex.tokenize |> ML_Lex.flatten
    in ML_Record_Antiquotation.mk_record_datatype_declaration true sanitized_str end))
\<close>


subsection \<open>Examples\<close>

ML_val \<open>

structure JustAStruct = struct
datatype bar = Bar of int;

@{record \<open>datatype 'a foo = 
  Foo of {f1:'a (* comments are removed *), 
  f2:bar }
\<close>}

val my_foo = Foo {f1 = 1, f2 = Bar 42};
val my_foo1 = map_f1 (K (Bar 44)) my_foo;
val t = get_f1 my_foo1

val t1 = make_foo {f1=3, f2=Bar 4}
val t2 = dest_foo t1

@{record \<open>datatype foo2 = Foo2 of {f3:int foo}\<close>}

end
\<close>

text \<open>Note that the markup of the datatype declaration is limited to basic Lex-markup.
Experiments with explicitly evaluating the datatype with e.g. the @{ML "ML"} function failed.
The issue there is that the @{ML "ML"} function is not evaluated at the point (aka context) 
exactly in the text position, but with the context of the surrounding ML command.

The following examples try to illustrate the issues.
\<close>

text \<open>Works as expected, as every type referred to in the datatype spec is already known 
at the beginnig of the @{command ML_val} command.\<close>
ML_val \<open>
val _ = ML \<open>datatype foo = Foo of int\<close>;
\<close>

text \<open>The following fails as 'bar' is not known at the beginning of the context.\<close>
ML_val \<open>
datatype bar = Bar of int
val _ = ML \<open>datatype foo = Foo of bar\<close>
handle ERROR x => warning x
\<close>

text \<open>Adding a semicolon after the definition of bar helps. 
There the semicolon marks the end of an "evaluation / compilation chunk". So @{ML "ML"} is
evaluated within an already augmented ML-context that knows about \<open>bar\<close>.
\<close>
ML_val \<open>
datatype bar = Bar of int;
val _ = ML \<open>datatype foo = Foo of bar\<close>
\<close>

text \<open>In the context of a structure the semicolon is not enough. \<close>
ML_val \<open>

structure InAStruct = 
struct
datatype bar = Bar of int;

val _ = ML \<open>datatype foo = Foo of bar\<close>
handle ERROR x => warning x
end

\<close>

end