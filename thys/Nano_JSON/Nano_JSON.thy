(***********************************************************************************
 * Copyright (c) 2019-2022 Achim D. Brucker
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * * Redistributions of source code must retain the above copyright notice, this
 *
 * * Redistributions in binary form must reproduce the above copyright notice,
 *   this list of conditions and the following disclaimer in the documentation
 *   and/or other materials provided with the distribution.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 * DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
 * SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
 * CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
 * OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 ***********************************************************************************)

section\<open>An Import/Export of JSON-like Formats for Isabelle/HOL\<close>
theory
  "Nano_JSON"
imports 
  Main 
keywords
      "JSON_file" :: thy_load
  and "JSON" :: thy_decl
  and "JSON_export" :: thy_decl
  and "defining"::quasi_command

begin
text\<open>
  This theory implements an import/export format for Isabelle/HOL that is inspired by 
  JSON (JavaScript Object Notation). While the format defined in this theory is inspired 
  by the JSON standard (@{url "https://www.json.org"}), it is not fully compliant. Most 
  notably, 

  \<^item> only basic support for Unicode characters. In particular,  JSON strings are mapped to a 
    polymorphic type usually is either instantiated with the @{type "string"} or 
    @{type "String.literal"}. Hence, the strings that can be represented in JSON are limited
    by the characters that Isabelle/HOL can handle (support on the Isabelle/ML level is 
    less constrained).
  \<^item> numbers are mapped to a polymorphic type, which can, e.g., be instantiated with 
    \<^item> @{term "real"}. Note that this is not a faithful representation of IEEE754 floating 
          point numbers that are assumed in the JSON standard. Moreover, this required that
          parent theories include Complex\_Main.
    \<^item> @{type "int"}. This is recommended configuration, if the JSON files only contain integers
      as numerical data.  
    \<^item> @{type "string"}. If not numerical operations need to be done, numberical values can also 
      be encoded as HOL strings (or @{type "String.literal"}).

  While the provided JSON import and export mechanism is not fully compliant to the JSON standard
  (hence, its name ``Nano JSON''), it should work with most real-world JSON files. Actually, it 
  has already served well in various projects, allowing us to simply exchange data between Isabelle/HOL
  and external tools. 
\<close>


subsection\<open>Defining a JSON-like Data Structure\<close>

text\<open>
  We start by modelling a HOL data type for representing the abstract syntax of JSON, which 
  consists out of objects, lists (called arrays), numbers, strings, and Boolean values.
 \<close>
subsubsection\<open>A HOL Data Type for JSON\<close>

datatype ('string, 'number) json =
     OBJECT "('string * ('string, 'number) json) list"
     | ARRAY "('string, 'number) json list"
  | NUMBER "'number" 
  | STRING "'string" 
  | BOOL "bool" 
  | NULL 

text\<open>
  Using the data type @{typ "('string, 'number) json"}, we can now represent JSON encoded data 
  easily in HOL, e.g., using the concrete instance @{typ "(string, int) json"}:\<close>
definition example01::\<open>(string, int) json\<close> where 
"example01 = 
  OBJECT [(''menu'', OBJECT [(''id'', STRING ''file''), (''value'', STRING ''File''),
          (''popup'', OBJECT [(''menuitem'', ARRAY
                       [OBJECT [(''value'', STRING ''New''), 
                                (''onclick'', STRING ''CreateNewDoc()'')], 
                        OBJECT [(''value'', STRING ''Open''), 
                                (''onclick'', STRING ''OpenDoc()'')],
                        OBJECT [(''value'', STRING ''Close''), 
                                (''onclick'', STRING ''CloseDoc()'')]
                       ])]
           )]),(''flag'', BOOL True), (''number'', NUMBER 42)
         ]"


subsubsection\<open>ML Implementation\<close>
text\<open>
  The translation of the data type @{typ "('string, 'number) json"} to Isabelle/ML is straight 
  forward with the exception that we do not need to distinguish different String representations. 
  In addition, we also  provide methods for converting JSON instances between the representation 
  as Isabelle terms and the representation as Isabelle/ML data structure.
\<close>

ML\<open>
signature NANO_JSON_TYPE = sig
    datatype NUMBER = INTEGER of int | REAL of IEEEReal.decimal_approx
    datatype json = OBJECT of (string * json) list
                  | ARRAY of json list
                  | NUMBER of NUMBER
                  | STRING of string
                  | BOOL of bool
                  | NULL

    val term_of_real: bool -> IEEEReal.decimal_approx -> term 
    val term_of_json: bool -> typ -> typ -> json -> term
    val json_of_term: term -> json
end
\<close>

ML_file Nano_JSON_Type.ML
text\<open>
 The file @{file \<open>Nano_JSON_Type.ML\<close>} provides the Isabelle/ML structure 
 @{ML_structure \<open>Nano_Json_Type:NANO_JSON_TYPE\<close>}. When first argument of 
 the functions @{ML \<open>Nano_Json_Type.term_of_real\<close>} and @{ML \<open>Nano_Json_Type.term_of_json\<close>} is 
 @{ML \<open>true\<close>}, then warnings are reported to the the output window of Isabelle. Otherwise, warning 
 will be ignored. Furthermore, the two arguments of type @{ML_type \<open>typ\<close>} of the function  
 @{ML \<open>Nano_Json_Type.term_of_json\<close>} represent the HOL target type for JSON strings and numerical 
 values. An example invocation of this function looks as follows:
\<close>
ML\<open>Nano_Json_Type.term_of_json false @{typ "string"} @{typ \<open>int\<close>} Nano_Json_Type.NULL\<close>

subsection\<open>Parsing Nano JSON\<close>

text\<open>
  In this section, we define the infrastructure for parsing JSON-like data structures as
  well as for importing them into Isabelle/HOL. This implementation was inspired by the 
  ``Simple Standard ML JSON parser'' from Chris Cannam.
\<close>

subsubsection\<open>ML Implementation\<close>

paragraph\<open>Configuration Attributes.\<close>
text\<open>
  We start by preparing the infrastructure for three configuration attributes, using 
  the Isabelle/Isar attribute mechanism:
\<close>
ML\<open>
  val json_num_type = let
    val (json_num_type_config, json_num_type_setup) =
      Attrib.config_string (Binding.name "JSON_num_type") (K "int")
  in
    Context.>>(Context.map_theory json_num_type_setup);
    json_num_type_config
  end
\<close>
text\<open>
  The attribute ``JSON\_num\_type'' (default @{type "int"}) allows for configuring the HOL-type 
  used representing JSON numerals.
\<close>

ML\<open>
  val json_string_type = let
    val (json_string_type_config, json_string_type_setup) =
      Attrib.config_string (Binding.name "JSON_string_type") (K "string")
  in
    Context.>>(Context.map_theory json_string_type_setup);
    json_string_type_config
  end
\<close>
text\<open>
  The attribute ``JSON\_string\_type'' (default @{type "string"}) allows for configuring the 
  HOL-type used representing JSON string.
\<close>

ML\<open>
  val json_verbose = let
    val (json_string_type_config, json_string_type_setup) =
      Attrib.config_bool (Binding.name "JSON_verbose") (K false)
  in
    Context.>>(Context.map_theory json_string_type_setup);
    json_string_type_config
  end
\<close>
text\<open>
  The Boolean attribute ``JSON\_verbose'' (default: false) allows for enabling warnings during the 
  JSON processing.
\<close>

paragraph\<open>Lexer.\<close>
text\<open>The following Isabelle/ML signatures captures the lexer:\<close>
ML\<open>
signature NANO_JSON_LEXER = sig
    structure T : sig
        datatype token = NUMBER of char list
                       | STRING of string
                       | BOOL of bool
                       | NULL
                       | CURLY_L
                       | CURLY_R
                       | SQUARE_L
                       | SQUARE_R
                       | COLON
                       | COMMA

        val string_of_T : token -> string
    end
    val tokenize_string: string -> T.token list
end
\<close>
ML_file Nano_JSON_Lexer.ML
text\<open>
 The file @{file \<open>Nano_JSON_Lexer.ML\<close>} provides the Isabelle/ML structure 
 @{ML_structure \<open>Nano_Json_Lexer:NANO_JSON_LEXER\<close>}. It provides the  
 function @{ML \<open>Nano_Json_Lexer.tokenize_string\<close>} which, as the name suggests, 
 tokenizes a string (containing a JSON object).
\<close>  

ML\<open>

signature NANO_JSON_PARSER = sig
    val json_of_string : string -> Nano_Json_Type.json
    val term_of_json_string : bool -> typ -> typ -> string -> term
    val numT: theory -> typ
    val stringT: theory -> typ
end
\<close>

ML_file "Nano_JSON_Parser.ML"
text\<open>
  The file @{file \<open>Nano_JSON_Parser.ML\<close>} provides the Isabelle/ML structure 
  @{ML_structure \<open>Nano_Json_Parser:NANO_JSON_PARSER\<close>}. The two main functions:
 
  \<^item> First, @{ML \<open>Nano_Json_Parser.json_of_string\<close>} parsing a string (containing a JSON object)
    and returning its abstract syntax (i.e., an instance of the type @{ML_type \<open>Nano_Json_Type.json\<close>}.
  \<^item> Second, @{ML \<open>Nano_Json_Parser.term_of_json_string\<close>}, which parses a string into a HOL term. 
    As for @{ML \<open>Nano_Json_Type.term_of_json\<close>}, the first argument decides if warnings are printed
    and the next wo arguments determine the HOL type representations for JSON strings and numerical
    values.

  The parser ML\<open>Nano_Json_Parser.term_of_json_string\<close> can now be used, on the Isabelle/ML-level
  as follows:
\<close>
ML\<open>
  Nano_Json_Parser.term_of_json_string true (@{typ string}) (@{typ int}) 
                                       "{\"name\": [true,false,\"test\"]}"
\<close>

subsubsection\<open>Isar Setup: Cartouche and Isar-Top-level Binding\<close>

paragraph\<open>The JSON Cartouche.\<close>
text\<open>First, we define a cartouche that allows using JSON syntax within HOL expressions:\<close>

syntax "_cartouche_nano_json" :: "cartouche_position \<Rightarrow> 'a"  ("JSON _")
parse_translation\<open> 
let
  fun translation u args = let
      val thy = Context.the_global_context u
      val verbose = Config.get_global thy json_verbose
      val strT = Nano_Json_Parser.stringT thy
      val numT = Nano_Json_Parser.numT thy
      fun err () = raise TERM ("Common._cartouche_nano_json", args)
      fun input s pos = Symbol_Pos.implode (Symbol_Pos.cartouche_content 
                                           (Symbol_Pos.explode (s, pos)))
    in
      case args of
        [(c as Const (@{syntax_const "_constrain"}, _)) $ Free (s, _) $ p] =>
          (case Term_Position.decode_position p of
            SOME (pos, _) => c 
                          $ Nano_Json_Parser.term_of_json_string verbose strT numT (input s pos) 
                          $ p
          | NONE => err ())
      | _ => err ()
  end
in
  [(@{syntax_const "_cartouche_nano_json"}, K (translation ()))] 
end
\<close>  

text\<open>
  In the following, we briefly illustrate the use of the JSON cartouche and the attribute 
  for mapping JSON types to HOL types:
\<close>

declare [[JSON_string_type = string]]
lemma \<open>y == JSON \<open>{"name": true}\<close> \<close>
  oops

declare [[JSON_string_type = String.literal]]
lemma \<open>y == JSON \<open>{"name": true}\<close> \<close>
  oops 
declare [[JSON_string_type = string]]

lemma \<open>y == JSON\<open>{"name": [true,false,"test"]}\<close> \<close>
  oops
lemma \<open>y == JSON\<open>{"name": [true,false,"test"],
                  "bool": true, 
                  "number" : 1 }\<close> \<close>
  oops


paragraph\<open>Isar Top-Level Commands.\<close> 
text\<open>
  Furthermore, we define two Isar top-level commands: one that allows for importing JSON 
  data from the file system, and one for defining JSON ``inline'' within Isabelle theory files.
\<close>
ML\<open>
structure Nano_Json_Parser_Isar = struct
    fun make_const_def (binding, trm) lthy = let
            val lthy' =  snd ( Local_Theory.begin_nested lthy )
            val arg = ((binding, NoSyn), 
                       ((Thm.def_binding binding,@{attributes [code]}), trm)) 
            val ((_, (_ , thm)), lthy'') = Local_Theory.define arg lthy'
        in
            (thm, Local_Theory.end_nested lthy'')
        end


    fun def_json name json lthy = let 
            val thy = Proof_Context.theory_of lthy    
            val strT = Nano_Json_Parser.stringT thy  
            val numT = Nano_Json_Parser.numT thy 
            val verbose = Config.get_global thy json_verbose
    in 
       (snd o (make_const_def (Binding.name name, 
                               Nano_Json_Parser.term_of_json_string verbose strT numT json))) 
       lthy
    end 

    val typeCfgParse  = Scan.optional 
                             (Args.parens (Parse.name -- Args.$$$ "," -- Parse.name)) 
                             (("",""),"");
    val jsonP = (Parse.name -- Parse.cartouche)

end
\<close>

ML\<open>
val _ = Outer_Syntax.local_theory @{command_keyword "JSON"} 
        "Define JSON." 
        ((Parse.cartouche -- \<^keyword>\<open>defining\<close> -- Parse.name) >> (fn ((json, _), name)
        => Nano_Json_Parser_Isar.def_json name json))

val _ = Outer_Syntax.command \<^command_keyword>\<open>JSON_file\<close> 
        "Import JSON and bind it to a definition."
        ((Resources.parse_file -- \<^keyword>\<open>defining\<close> -- Parse.name) >> 
         (fn ((get_file,_),name) =>
           Toplevel.theory (fn thy =>
           let
              val ({lines, ...}:Token.file) = get_file thy;
              val thy'' = Named_Target.theory_map 
                            (Nano_Json_Parser_Isar.def_json name (String.concat lines)) 
                            thy
           in thy'' end)))
\<close>

subsubsection\<open>Examples\<close>

text\<open>
  Now we can use the JSON Cartouche for defining JSON-like data ``on-the-fly''. Note that you 
  need to escape quotes within the JSON Cartouche, if you are using quotes as lemma delimiters, 
  e.g.,:
\<close>
lemma "y == JSON\<open>{\"name\": [true,false,\"test\"]}\<close>"
  oops
text\<open>
  Thus, we recommend to use the Cartouche delimiters when using the JSON Cartouche with 
  non-trivial data structures:
\<close>
lemma \<open> example01 == JSON \<open>{"menu": {
                            "id": "file",
                            "value": "File",
                            "popup": {
                              "menuitem": [
                               {"value": "New", "onclick": "CreateNewDoc()"},
                               {"value": "Open", "onclick": "OpenDoc()"},
                               {"value": "Close", "onclick": "CloseDoc()"}
                              ] 
                            }},
                           "flag": true,
                           "number": 42
                           }\<close>\<close>
  by(simp add: example01_def)

text\<open>
  We can define new JSON data ``inline'', using the Isar keyword @{command "JSON"}:
\<close>
JSON \<open>
{"menu": {
  "id": "file",
  "value": "File",
  "popup": {
    "menuitem": [
      {"value": "New", "onclick": "CreateNewDoc()"},
      {"value": "Open", "onclick": "OpenDoc()"},
      {"value": "Close", "onclick": "CloseDoc()"}
    ]
  }
}, "flag":true, "number":42}
\<close> defining example04

text\<open>
  Moreover, we can define new JSON data by reading it from a file, using the Isar keyword 
  @{command "JSON_file"}:
\<close>

JSON_file "example.json" defining example03

thm example03_def example04_def

lemma "example03 = example04"
  by (simp add:example03_def example04_def)

subsection\<open>Serializing Nano JSON\<close>

text\<open>
  In this section, we define the necessary infrastructure to serialize (export) data from HOL using 
  a JSON-like data structure that other JSON tools should be able to import.
\<close>

subsubsection\<open>ML Implementation\<close>
ML\<open>
signature NANO_JSON_SERIALIZER = sig
    val serialize_json: Nano_Json_Type.json -> string
    val serialize_json_pretty: Nano_Json_Type.json -> string
    val serialize_term: term -> string
    val serialize_term_pretty: term -> string
end
\<close>

ML_file "Nano_JSON_Serializer.ML"
text\<open>
  The file @{file \<open>Nano_JSON_Serializer.ML\<close>} provides the Isabelle/ML structure
  @{ML_structure \<open>Nano_Json_Serializer:NANO_JSON_SERIALIZER\<close>}. It provides
  functions for serializing JSON data from it abstract syntax as well as from 
  its HOL term representations. Moreover, variants are provided that try to 
  pretty print the output with the goal of making it easier to read for humans.
\<close>
subsubsection\<open>Isar Setup\<close>
ML\<open>
structure Nano_Json_Serialize_Isar = struct
  fun export_json thy json_const filename =
    let
        val term = Thm.concl_of (Global_Theory.get_thm thy (json_const^"_def"))
         fun export binding content thy =
             let
               val thy' = thy |> Generated_Files.add_files (binding, content);
               val _ = Export.export thy' binding (Bytes.contents_blob content)
             in thy' end;
        val json_term = case term of
                        Const (@{const_name "Pure.eq"}, _) $ _ $ json_term => json_term
                      | _ $ (_ $ json_term) => json_term
                      | _ => error ("Term structure not supported.")
        val json_string  = Nano_Json_Serializer.serialize_term_pretty json_term 
        val json_bytes = (XML.add_content (YXML.parse json_string) Buffer.empty)
                           |> Bytes.buffer
    in
        case filename of 
             SOME filename => let 
                                val filename = Path.explode (filename^".json")
                                val thy' = export (Path.binding 
                                                    (Path.append (Path.explode "json") 
                                                       filename,Position.none)) 
                                                    json_bytes thy
                                val _ =  writeln (Export.message thy (Path.basic "json"))
                              in
                                 thy'                                 
                              end
           | NONE =>  (tracing json_string; thy) 
    end
end
\<close>

ML\<open>
  Outer_Syntax.command ("JSON_export", Position.none) 
  "export JSON data to an external file"
  ((Parse.name -- Scan.option (\<^keyword>\<open>file\<close>-- Parse.name)) 
   >> (fn (const_name,filename) =>
         (Toplevel.theory (fn state => Nano_Json_Serialize_Isar.export_json state 
                                                   const_name (Option.map snd filename)))));
\<close>


subsubsection\<open>Examples\<close>
text\<open>
  We can now serialize JSON and print the result in the output window of Isabelle/HOL:
\<close>
JSON_export example01
thm example01_def

text\<open>
  Alternatively, we can export the serialized JSON into a file:
\<close>
JSON_export example01 file example01

subsection\<open>Putting Everything Together\<close>
text\<open>
  For convenience, we provide an ML structure that provides access to both the parser and the 
  serializer:  
\<close>
ML\<open>
structure Nano_Json = struct
    open Nano_Json_Type 
    open Nano_Json_Parser
    open Nano_Json_Serializer
end
\<close>

end
