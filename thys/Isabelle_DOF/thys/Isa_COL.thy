(*************************************************************************
 * Copyright (C) 
 *               2019      The University of Exeter 
 *               2018-2019 The University of Paris-Saclay
 *               2018      The University of Sheffield
 *
 * License:
 *   This program can be redistributed and/or modified under the terms
 *   of the 2-clause BSD-style license.
 *
 *   SPDX-License-Identifier: BSD-2-Clause
 *************************************************************************)

chapter \<open>The Document Ontology Common Library for the Isabelle Ontology Framework\<close>

text\<open> Building a fundamental infrastructure for common document elements such as
      Structuring Text-Elements (the top classes), Figures, (Tables yet todo)

      The COL provides a number of ontological "macros" like "section*" which 
      automatically set a number of class-attributes in particular ways without 
      user-interference. 
    \<close> 

theory Isa_COL   
  imports  Isa_DOF  
  keywords "title*"        "subtitle*"      
           "chapter*"      "section*"    "paragraph*"
           "subsection*"   "subsubsection*" 
           "figure*"       "listing*"    "frame*" :: document_body

begin

section\<open>Basic Text and Text-Structuring Elements\<close>

text\<open> The attribute @{term "level"} in the subsequent enables doc-notation support section* etc.
we follow LaTeX terminology on levels 
\<^enum>             part          = Some -1
\<^enum>             chapter       = Some 0
\<^enum>             section       = Some 1
\<^enum>             subsection    = Some 2
\<^enum>             subsubsection = Some 3
\<^enum>             ... 

for scholarly paper: invariant level > 0. \<close>

doc_class text_element =     
   level         :: "int  option"    <=  "None" 
   referentiable :: bool <= "False"
   variants      :: "String.literal set" <= "{STR ''outline'', STR ''document''}" 

doc_class "chapter" = text_element +
   level         :: "int  option"    <=  "Some 0" 
doc_class "section" = text_element +
   level         :: "int  option"    <=  "Some 1" 
doc_class "subsection" = text_element +
   level         :: "int  option"    <=  "Some 2" 
doc_class "subsubsection" = text_element +
   level         :: "int  option"    <=  "Some 3" 
doc_class "paragraph" = text_element +
   level         :: "int  option"    <=  "Some 4" 


subsection\<open>Ontological Macros\<close>

ML\<open> 

structure Onto_Macros =
struct
local open ODL_Meta_Args_Parser in
(* *********************************************************************** *)
(* Ontological Macro Command Support                                       *)
(* *********************************************************************** *)

(* {markdown = true} sets the parsing process such that in the text-core markdown elements are
   accepted. *)

 
fun enriched_text_element_cmd level =
   let fun transform doc_attrs = case level of 
                  NONE => doc_attrs 
                | SOME(NONE)   => (("level",@{here}),"None")::doc_attrs
                | SOME(SOME x) => (("level",@{here}),"Some("^ Int.toString x ^"::int)")::doc_attrs
   in Monitor_Command_Parser.gen_enriched_document_cmd {inline=true} I transform end; 

local 
fun transform_cid _ NONE X = X
   |transform_cid _ (SOME ncid) NONE =  (SOME(ncid,@{here}))
   |transform_cid thy (SOME cid) (SOME (sub_cid,pos)) =
                             let val cid_long  = DOF_core.get_onto_class_name_global' cid thy
                                 val sub_cid_long =  DOF_core.get_onto_class_name_global' sub_cid thy
                             in  if DOF_core.is_subclass_global thy  sub_cid_long cid_long
                                 then (SOME (sub_cid,pos))
                                 else (*  BUG : check reveals problem of Definition* misuse.  *)
                                        error("class "^sub_cid_long^
                                              " must be sub-class of "^cid_long) 
                             end  
in

fun transform_attr S doc_attrs =
  let
    fun transform_attr' [] doc_attrs = doc_attrs
      | transform_attr' (s::S) (doc_attrs) =
          let val (name', value) = s
              val doc_attrs' = doc_attrs
                               |> map (fn (name, term) => if name = name'
                                                          then (name, value)
                                                          else (name, term))
          in if doc_attrs' = doc_attrs
             then transform_attr' S doc_attrs' |> cons (name', value) 
             else transform_attr' S doc_attrs' 
          end
  in transform_attr' S doc_attrs end

fun enriched_formal_statement_command ncid (S: (string * string) list) =
  let fun transform_attr doc_attrs = (map (fn(cat,tag) => ((cat,@{here}),tag)) S) @ 
                                      (("formal_results",@{here}),"([]::thm list)")::doc_attrs
  in  fn margs => fn thy =>
          Monitor_Command_Parser.gen_enriched_document_cmd {inline=true} 
                                    (transform_cid thy ncid) transform_attr margs thy
  end;

fun enriched_document_cmd_exp ncid (S: (string * string) list) =
   (* expands ncid into supertype-check. *)
   let fun transform_attr attrs = (map (fn(cat,tag) => ((cat,@{here}),tag)) S) @ attrs
   in  fn margs => fn thy =>
         Monitor_Command_Parser.gen_enriched_document_cmd {inline=true} (transform_cid thy ncid)
                                                                            transform_attr margs thy
   end;
end (* local *)


fun heading_command (name, pos) descr level =
  Monitor_Command_Parser.document_command (name, pos) descr
    {markdown = false, body = true} (enriched_text_element_cmd level) [] I;

val _ = heading_command \<^command_keyword>\<open>title*\<close> "section heading" NONE;
val _ = heading_command \<^command_keyword>\<open>subtitle*\<close> "section heading" NONE;
val _ = heading_command \<^command_keyword>\<open>chapter*\<close> "section heading" (SOME (SOME 0));
val _ = heading_command \<^command_keyword>\<open>section*\<close> "section heading" (SOME (SOME 1));
val _ = heading_command \<^command_keyword>\<open>subsection*\<close> "subsection heading" (SOME (SOME 2));
val _ = heading_command \<^command_keyword>\<open>subsubsection*\<close> "subsubsection heading" (SOME (SOME 3));
val _ = heading_command \<^command_keyword>\<open>paragraph*\<close> "paragraph" (SOME (SOME 4));


end 
end
\<close>


section\<open>Layout Trimming Commands (with syntactic checks)\<close>

ML\<open> 
local

val scan_cm = Scan.ahead (Basic_Symbol_Pos.$$$ "c" |-- Basic_Symbol_Pos.$$$ "m" ) ;
val scan_pt = Scan.ahead (Basic_Symbol_Pos.$$$ "p" |-- Basic_Symbol_Pos.$$$ "t" ) ;
val scan_blank = Scan.repeat (   Basic_Symbol_Pos.$$$ " "
                              || Basic_Symbol_Pos.$$$ "\t" 
                              || Basic_Symbol_Pos.$$$ "\n");

in

val scan_latex_measure = (scan_blank
                          |-- Scan.option (Basic_Symbol_Pos.$$$ "-")
                          |-- Symbol_Pos.scan_nat 
                          |-- (Scan.option ((Basic_Symbol_Pos.$$$ ".") |-- Symbol_Pos.scan_nat))
                          |-- scan_blank
                          |-- (scan_cm || scan_pt)
                          |-- scan_blank
                         ) ;
           
fun check_latex_measure _ src  = 
         let val _ = ((Scan.catch scan_latex_measure (Symbol_Pos.explode(Input.source_content src)))
                     handle Fail _ => error ("syntax error in LaTeX measure") )
         in () end

val parse_latex_measure = Parse.embedded_input >> (fn src => (check_latex_measure () (* dummy arg *) src; 
                                       (fst o Input.source_content) src )  )

end\<close>



setup\<open> DOF_lib.define_macro \<^binding>\<open>vs\<close>  "\\vspace{" "}" (check_latex_measure) \<close> 
setup\<open> DOF_lib.define_macro \<^binding>\<open>hs\<close>  "\\hspace{" "}" (check_latex_measure) \<close> 
define_shortcut* hfill \<rightleftharpoons> \<open>\hfill\<close>
(*<*)

text\<open>Tests: \<^vs>\<open>-0.14cm\<close>\<close>

ML\<open> check_latex_measure @{context} (Input.string "-0.14 cm") \<close>
define_macro* vs2 \<rightleftharpoons> \<open>\vspace{\<close> _ \<open>}\<close> (check_latex_measure) (* checkers NYI on Isar-level *)
define_macro* hs2 \<rightleftharpoons> \<open>\hspace{\<close> _ \<open>}\<close> (* works fine without checker.*)

(*>*)

define_shortcut* clearpage \<rightleftharpoons> \<open>\clearpage{}\<close>
                 hf \<rightleftharpoons> \<open>\hfill\<close> 
                 br \<rightleftharpoons> \<open>\break\<close> 


section\<open> Library of Standard Figure Ontology \<close>

datatype placement = here  |  top  |  bottom  

(*
ML\<open> "side_by_side_figure"  |> Name_Space.declared (DOF_core.get_onto_classes \<^context>
                           |> Name_Space.space_of_table)\<close>
*)

datatype float_kind = listing | table | graphics

doc_class float        = 
   placement           :: "placement list"
   kind                :: float_kind
   spawn_columns       :: bool <= False 
   main_caption        :: string <= "''''" 

doc_class figure       =  float +
   kind                :: float_kind <= graphics 
   file_src            :: string
   relative_width      :: int 
   relative_height     :: int 
   invariant fig_kind  :: "kind \<sigma> = graphics"


doc_class listing      =  float +
   kind                :: float_kind
   invariant fig_kind' :: "kind \<sigma> = float_kind.listing"


(* obsolete 
doc_class side_by_side_figure = figure +
   anchor           :: "string"
   caption          :: "string"
   relative_width2  :: "int"  (* percent of textwidth *)    
   src2             :: "string"
   anchor2          :: "string"
   caption2         :: "string"
*)


subsection\<open>Figures\<close>

(*<*)

ML\<open>
fun setup source =
  ML_Context.expression (Input.pos_of source)
    (ML_Lex.read "Theory.setup (" @ ML_Lex.read_source source @ ML_Lex.read ")")
  |> Context.theory_map;
\<close>

(*>*)

subsubsection\<open>The Figure Content Antiquotation\<close>
text\<open>The intermediate development goal is to separate the ontological, top-level construct 
\<open>figure*\<close>, which will remain a referentiable, ontological document unit, from the more versatile
\<^emph>\<open>import\<close> of a figure. This opens the way for more orthogonality and abstraction from the LaTeX 
engine.
\<close>
ML\<open>    

type fig_content =   {relative_width  : int, (* percent of textwidth, default 100 *)
                      relative_height : int, (* percent, default 100 *)
                      caption         : Input.source (* default empty *)}

val mt_fig_content = {relative_width  = 100,
                      relative_height = 100,    
                      caption         = Input.empty }: fig_content

fun make_fig_content (relative_width, relative_height, caption) =
   {relative_width = relative_width, relative_height = relative_height, caption = caption}

fun upd_fig_content f =
  fn {relative_width, relative_height, caption} =>
    make_fig_content (f (relative_width, relative_height, caption))

fun upd_relative_width f =
  upd_fig_content (fn (relative_width, relative_height, caption) =>
    (f relative_width, relative_height, caption))

fun upd_relative_height f =
  upd_fig_content (fn (relative_width, relative_height, caption) =>
    (relative_width, f relative_height, caption))

fun upd_caption f =
  upd_fig_content (fn (relative_width, relative_height, caption) =>
    (relative_width, relative_height, f caption))

val widthN     = "width"
val heightN    = "height" 
val captionN   = "caption";

fun fig_content_modes (ctxt, toks) = 
       let val (y, toks') = ((((Scan.optional 
                      (Args.parens 
                         (Parse.list1
                           (   (Args.$$$ widthN |-- Args.$$$ "=" -- Parse.int
                                >> (fn (_, k) => upd_relative_width (K k)))
                            || (Args.$$$ heightN |-- Args.$$$ "=" -- Parse.int
                                >> (fn (_, k) => upd_relative_height (K k)))
                            || (Args.$$$ captionN |-- Args.$$$ "=" -- Parse.document_source
                                >> (fn (_, k) => upd_caption (K k)))
                      ))) [K mt_fig_content]) 
                      : (fig_content -> fig_content) list parser)
                      >> (foldl1 (op #>)))
                      : (fig_content -> fig_content) parser)
                      (toks)
        in (y, (ctxt, toks')) end

fun get_session_dir ctxt path = 
         Resources.check_session_dir ctxt 
                                     (SOME (path))  
                                     (Syntax.read_input ".")
          handle ERROR s => (if String.isPrefix "Bad session root directory (missing ROOT or ROOTS): " s 
                             then get_session_dir ctxt (Path.dir path)
                             else error s)

fun get_document_dir ctxt =
      let val thy = Proof_Context.theory_of ctxt
          val sess_dir = get_session_dir ctxt  (Resources.master_directory thy)
      in  Path.append sess_dir  (Path.explode "document") end;

fun generate_caption ctxt caption = 
    let 
              val cap_txt= Document_Output.output_document ctxt {markdown = false} caption
              fun drop_latex_macro (XML.Elem (("latex_environment", [("name", "isabelle")]),xmlt)) = xmlt
                 |drop_latex_macro X = [X]
              val drop_latex_macros = List.concat o map drop_latex_macro;
    in
      drop_latex_macros cap_txt
    end

fun process_args cfg_trans =
  let val {relative_width,relative_height,caption} = cfg_trans mt_fig_content
      val _ = if relative_width < 0 orelse relative_height <0
              then error("negative parameter.")
               else ()
      val wdth_val_s = Real.toString((Real.fromInt relative_width)
                         / (Real.fromInt 100))^"\\textwidth"
      val ht_s= if relative_height = 100
                then ""
                else "height="
                     ^ Real.toString((Real.fromInt relative_height)
                         / (Real.fromInt 100))
                     ^ "\\textheight"
  in (wdth_val_s, ht_s, caption) end

fun fig_content ctxt (cfg_trans,file:Input.source) = 
       let val (wdth_val_s, ht_s, caption) = process_args cfg_trans
           val arg_single  = enclose "[" "]" (commas ["keepaspectratio","width="^wdth_val_s,ht_s])
           val arg    = enclose "[" "]" (commas ["keepaspectratio","width=\\textwidth",ht_s])
           val _   = Resources.check_file ctxt (SOME (get_document_dir ctxt)) file
           (* ToDo: must be declared source of type png or jpeg or pdf, ... *)
           
       in if Input.string_of(caption) = ""  then
                   file 
                   |> (Latex.string o Input.string_of) 
                   |> Latex.macro ("includegraphics"^arg_single)
          else
                   file 
                   |> (Latex.string o Input.string_of) 
                   |> (fn X => (Latex.string ("{"^wdth_val_s^"}")) 
                                @ (Latex.macro0 "centering")
                                @ (Latex.macro ("includegraphics"^arg) X)
                                @ (Latex.macro "caption" (generate_caption ctxt caption)))
                   |> (Latex.environment ("subcaptionblock") )
(* BUG: newline at the end of subcaptionlbock, making side-by-side a figure-below-figure setup *)
       end

fun fig_content_antiquotation name scan =
  (Document_Output.antiquotation_raw_embedded name 
    (scan : ((fig_content -> fig_content) * Input.source) context_parser)
    (fig_content : Proof.context -> (fig_content -> fig_content) * Input.source -> Latex.text));
          

fun figure_content ctxt (cfg_trans,file:Input.source) =
  let val _   = Resources.check_file ctxt (SOME (get_document_dir ctxt)) file
      (* ToDo: must be declared source of type png or jpeg or pdf, ... *)
      val (wdth_val_s, ht_s, caption) = process_args cfg_trans
      val args = ["keepaspectratio","width=" ^ wdth_val_s, ht_s]
                 |> commas
                 |> enclose "[" "]"
  in file
     |> (Latex.string o Input.string_of)
     |> Latex.macro ("includegraphics" ^ args)
     |> (fn X => X @ Latex.macro "caption" (generate_caption ctxt caption))
     |> Latex.environment ("figure")
  end

fun figure_antiquotation name scan =
  (Document_Output.antiquotation_raw_embedded name
    (scan : ((fig_content -> fig_content) * Input.source) context_parser)
    (figure_content : Proof.context -> (fig_content -> fig_content) * Input.source -> Latex.text));

val _ = Theory.setup 
           (   fig_content_antiquotation \<^binding>\<open>fig_content\<close> 
                                         (fig_content_modes -- Scan.lift(Parse.path_input))
               #> figure_antiquotation \<^binding>\<open>figure_content\<close>
                                         (fig_content_modes -- Scan.lift(Parse.path_input)))

\<close>


ML\<open>


fun convert_meta_args ctxt (X, (((str,_),value) :: R)) =
     let fun conv_int x = snd(HOLogic.dest_number(Syntax.read_term ctxt x))
                          handle TERM _ =>  error "Illegal int format."
     in
         (case YXML.content_of str of 
             "relative_width" =>  upd_relative_width (K (conv_int value))
                                  o  convert_meta_args ctxt (X, R)
          |  "relative_height" => upd_relative_height (K (conv_int value))
                                  o  convert_meta_args ctxt (X, R )
          |  "file_src"        => convert_meta_args ctxt (X, R)
          |  s => error("!undefined attribute:"^s))
     end
   |convert_meta_args _ (_,[]) = I

fun convert_src_from_margs ctxt (X, (((str,_),value)::R)) = 
          (case YXML.content_of str of 
             "file_src" => Input.string (HOLogic.dest_string (Syntax.read_term ctxt value))
           | _          => convert_src_from_margs ctxt (X,R))
   |convert_src_from_margs _ (_, [])     = error("No file_src provided.")

fun float_command (name, pos) descr cid  =
  let fun set_default_class NONE = SOME(cid,pos)
         |set_default_class (SOME X) = SOME X 
      fun create_instance  (((binding,cid_pos), doc_attrs) : ODL_Meta_Args_Parser.meta_args_t)  =
                Value_Command.Docitem_Parser.create_and_check_docitem 
               {is_monitor = false} 
               {is_inline = true}
               {define = true} binding (set_default_class cid_pos) doc_attrs
      fun generate_fig_ltx_ctxt ctxt cap_src oid body = 
        Latex.macro0 "centering" 
        @ body 
        @ Latex.macro "caption" (generate_caption ctxt cap_src)
        @ Latex.macro "label" (DOF_core.get_instance_name_global oid (Proof_Context.theory_of ctxt)
                               |> DOF_core.output_name
                               |> Latex.string)
      fun parse_and_tex (margs as ((binding,_), _), cap_src) ctxt =
        let val oid = Binding.name_of binding
        in
          (convert_src_from_margs ctxt margs)
          |> pair (upd_caption (K Input.empty) #> convert_meta_args ctxt margs)
          |> fig_content ctxt 
          |> generate_fig_ltx_ctxt ctxt cap_src oid
          |> (Latex.environment ("figure") )
        end
  in  Monitor_Command_Parser.onto_macro_cmd_command (name, pos) descr create_instance parse_and_tex
  end

fun listing_command (name, pos) descr cid  =
  let fun set_default_class NONE = SOME(cid,pos)
         |set_default_class (SOME X) = SOME X 
      fun create_instance  (((binding,cid_pos), doc_attrs) : ODL_Meta_Args_Parser.meta_args_t)  =
                Value_Command.Docitem_Parser.create_and_check_docitem 
               {is_monitor = false} 
               {is_inline = true}
               {define = true} binding (set_default_class cid_pos) doc_attrs
      fun parse_and_tex (margs as ((binding,_), _), _) _ =
        let val pos = Binding.pos_of binding
        in
          ISA_core.err ("Not yet implemented.\n Please use text*[oid::listing]\<open>\<close> instead.") pos
        end
  in  Monitor_Command_Parser.onto_macro_cmd_command (name, pos) descr create_instance parse_and_tex
  end
  

(* *********************************************************************** *)
(* Ontological Macro Command Support                                       *)
(* *********************************************************************** *)

val _ = float_command \<^command_keyword>\<open>figure*\<close> "figure" "Isa_COL.figure" ;
val _ = listing_command \<^command_keyword>\<open>listing*\<close> "listing" "Isa_COL.listing" ;  (* Hack ! *)
\<close>


subsection\<open>Tables\<close>
(* Under development *)

text\<open>Tables are (sub) document-elements represented inside the documentation antiquotation
language. The used technology is similar to the existing railroad-diagram support 
(cf. \<^url>\<open>https://isabelle.in.tum.de/doc/isar-ref.pdf\<close>, Sec. 4.5). 

However, tables are not directly based on the idiosyncrasies of Knuth-based language design ---

However, tables come with a more abstract structure model than conventional typesetting in the 
LaTeX tradition. It is based of the following principles:
  \<^item> The core unit of a table is a \<^emph>\<open>cell\<close> having a \<^emph>\<open>configuration\<close>, i.e. a
    number of attributes specifying its width, height, borderline, etc. 
    A cell may be \<^emph>\<open>elementary\<close>, i.e. containing structured text or \<^emph>\<open>compound\<close>, 
    i.e. containing a sub-table.
  \<^item> A \<^emph>\<open>table\<close> contains either a list of \<^emph>\<open>rows\<close> or a list of \<^emph>\<open>columns\<close>, which are both
    lists of cells.
  \<^item> The tables, rows and columns posses own configurations.
  \<^item> Concerning the layout, \<^emph>\<open>propagation\<close>  laws of configurations control that 
    information flows top-down from tables to rows or columns, from rows/columns to cells,
    from left to right within rows and from top to bottom in columns; propagation produces
    the desired presentation effect of tables that cells appear somewhat uniform in it. 
  \<^item> Since rows are lists of cells, configurations are also a list of attributes.
    Attributes of the same kind may appear repeatedly. If the sub-list of attributes 
    of the same kind is shorter than the list of cells it is referring to, than
    the last element in this sub-list is duplicated as many times as necessary. This feature
    of configuration propagation is called \<^emph>\<open>filling\<close>.
  \<^item> Lists of rows and lists of cells consists of the same number of cells.
  \<^item> Since propagation and filling induce a congruence relation on table trees, a normalisation
    process is a necessary pre-requisite for the compilation to LaTeX.
\<close>

ML\<open>
local

fun mk_line _ st2 [a] =  [a @ Latex.string st2]
   |mk_line st1 st2 (a::S) = [a @ Latex.string st1] @ mk_line st1 st2 S;

(* tab attributes for global setup *)

type cell_config =   {cell_placing    : string list, 
                      cell_height     : string list,
                      cell_width      : string list,
                      cell_bgnd_color : string list,
                      cell_line_color : string list,
                      cell_line_width : string list}

val mt_cell_config = {cell_placing   = [],
                      cell_height    = [],    
                      cell_width     = [],    
                      cell_bgnd_color= [], 
                      cell_line_color= [], 
                      cell_line_width= [] }: cell_config

fun upd_cell_placing key 
            {cell_placing,cell_height,cell_width, cell_bgnd_color,   
             cell_line_color,cell_line_width} : cell_config = 
            {cell_placing   = cell_placing @ [key],  cell_height    = cell_height,    
             cell_width     = cell_width,            cell_bgnd_color= cell_bgnd_color, 
             cell_line_color= cell_line_color,       cell_line_width= cell_line_width } 
            : cell_config

fun upd_cell_height num 
            {cell_placing,cell_height,cell_width, cell_bgnd_color,   
             cell_line_color,cell_line_width} : cell_config = 
            {cell_placing   = cell_placing ,  cell_height    = cell_height @ [num],    
             cell_width     = cell_width,     cell_bgnd_color= cell_bgnd_color, 
             cell_line_color= cell_line_color,cell_line_width= cell_line_width } 
            : cell_config

fun upd_cell_width num 
            {cell_placing,cell_height,cell_width, cell_bgnd_color,   
             cell_line_color,cell_line_width} : cell_config = 
            {cell_placing   = cell_placing ,   cell_height    = cell_height,    
             cell_width     = cell_width@[num],cell_bgnd_color= cell_bgnd_color, 
             cell_line_color= cell_line_color, cell_line_width= cell_line_width } 
            : cell_config

fun upd_cell_bgnd_color str 
            {cell_placing,cell_height,cell_width, cell_bgnd_color,   
             cell_line_color,cell_line_width} : cell_config = 
            {cell_placing   = cell_placing ,   cell_height    = cell_height,    
             cell_width     = cell_width,      cell_bgnd_color= cell_bgnd_color@[str], 
             cell_line_color= cell_line_color, cell_line_width= cell_line_width } 
            : cell_config

fun upd_cell_line_color str 
            {cell_placing,cell_height,cell_width, cell_bgnd_color,   
             cell_line_color,cell_line_width} : cell_config = 
            {cell_placing   = cell_placing ,         cell_height    = cell_height,    
             cell_width     = cell_width,            cell_bgnd_color= cell_bgnd_color, 
             cell_line_color= cell_line_color@[str], cell_line_width= cell_line_width } 
            : cell_config

fun upd_cell_line_width num 
            {cell_placing,cell_height,cell_width, cell_bgnd_color,   
             cell_line_color,cell_line_width} : cell_config = 
            {cell_placing    = cell_placing ,   cell_height     = cell_height,    
             cell_width      = cell_width,      cell_bgnd_color = cell_bgnd_color, 
             cell_line_color = cell_line_color, cell_line_width = cell_line_width@[num] } 
            : cell_config

(* global default configs *)
val (tab_cell_placing, tab_cell_placing_setup)
     = Attrib.config_string \<^binding>\<open>tab_cell_placing\<close> (K "center");
val (tab_cell_height, tab_cell_height_setup)
     = Attrib.config_string \<^binding>\<open>tab_cell_height\<close> (K "0.0cm");
val (tab_cell_width, tab_cell_width_setup)
     = Attrib.config_string \<^binding>\<open>tab_cell_width\<close> (K "0.0cm");
val (tab_cell_bgnd_color, tab_cell_bgnd_color_setup)
     = Attrib.config_string \<^binding>\<open>tab_cell_bgnd_height\<close> (K "white");
val (tab_cell_line_color, tab_cell_line_color_setup)
     = Attrib.config_string \<^binding>\<open>tab_cell_line_color\<close> (K "black");
val (tab_cell_line_width, tab_cell_line_width_setup)
     = Attrib.config_string \<^binding>\<open>tab_cell_line_height\<close> (K "0.0cm");

fun default_cell_config ctxt = {cell_placing    = [Config.get ctxt tab_cell_placing],
                                cell_height     = [Config.get ctxt tab_cell_height],    
                                cell_width      = [Config.get ctxt tab_cell_width],    
                                cell_bgnd_color = [Config.get ctxt tab_cell_bgnd_color], 
                                cell_line_color = [Config.get ctxt tab_cell_line_color], 
                                cell_line_width = [Config.get ctxt tab_cell_line_width]}
                              : cell_config


val _ = Theory.setup(   tab_cell_placing_setup
                     #> tab_cell_height_setup
                     #> tab_cell_width_setup
                     #> tab_cell_bgnd_color_setup
                     #> tab_cell_line_color_setup
                     #> tab_cell_line_width_setup
                    )


(*syntax for local tab specifier *)
val cell_placingN    = "cell_placing"
val cell_heightN     = "cell_height" 
val cell_widthN      = "cell_width"
val cell_bgnd_colorN = "cell_bgnd_color" 
val cell_line_colorN = "cell_line_color"
val cell_line_widthN = "cell_line_width" 

val placing_scan = Args.$$$ "left" || Args.$$$ "center" || Args.$$$ "right" 

val color_scan   =   Args.$$$ "none" || Args.$$$ "red" || Args.$$$ "green"                   
                  || Args.$$$ "blue" || Args.$$$ "black"


fun lift scan (st, xs) =
  let val (y, xs') = scan xs
  in (y, (st, xs')) end;


fun tabitem_modes (ctxt, toks) = 
       let val (y, toks') = ((((Scan.optional 
                      (Args.parens 
                         (Parse.list1
                           (   (Args.$$$ cell_placingN |-- Args.$$$ "=" -- placing_scan
                                >> (fn (_, k) => upd_cell_placing k))   
                            || (Args.$$$ cell_heightN |-- Args.$$$ "=" -- parse_latex_measure
                                >> (fn (_, k) => upd_cell_height k))    
                            || (Args.$$$ cell_widthN |-- Args.$$$ "=" -- parse_latex_measure
                                >> (fn (_, k) => upd_cell_width k))    
                            || (Args.$$$ cell_bgnd_colorN |-- Args.$$$ "=" -- color_scan
                                >> (fn (_, k) => upd_cell_bgnd_color k))
                            || (Args.$$$ cell_line_colorN |-- Args.$$$ "=" -- color_scan
                                >> (fn (_, k) => upd_cell_line_color k))
                            || (Args.$$$ cell_line_widthN |-- Args.$$$ "=" -- parse_latex_measure
                                >> (fn (_, k) => upd_cell_line_width k))
                      ))) [K (default_cell_config (Context.the_proof ctxt))]) 
                      : (cell_config -> cell_config) list parser)
                      >> (foldl1 (op #>)))
                      : (cell_config -> cell_config) parser)
                      (toks)
        in (y, (ctxt, toks')) end


datatype table_tree  = mk_tab    of cell_config * cell_group
                     | mk_cell   of cell_config * Input.source
   and   cell_group  = mk_row    of cell_config * table_tree list
                     | mk_column of cell_config * table_tree list
                                             


val tab_config_parser =  tabitem_modes : ((cell_config -> cell_config) ) context_parser
val table_parser =  tab_config_parser -- Scan.repeat1(Scan.repeat1(Scan.lift Args.cartouche_input))

fun table_antiquotation name scan =
  Document_Output.antiquotation_raw_embedded name 
    scan
    (fn ctxt => 
      (fn (cfg_trans,content:Input.source list list) =>
          let val cfg = cfg_trans mt_cell_config
              val _ = writeln ("XXX"^ @{make_string} cfg)
              fun check _ = ()  (* ToDo *)
              val _  = check content
          in  content 
              |> (map(map (Document_Output.output_document ctxt {markdown = false})
                  #> mk_line "&" "\\\\"
                  #> List.concat )
                  #> List.concat)
              |> XML.enclose "\\table[allerhandquatsch]{" "}"
          end
      )
    );

fun cell_antiquotation name scan =
    Document_Output.antiquotation_raw_embedded name 
    scan
    (fn ctxt => 
      (fn (cfg_trans,content:Input.source) => 
          let val cfg = cfg_trans mt_cell_config
              val _ = writeln ("XXX"^ @{make_string} cfg) 
          in  content |> Document_Output.output_document ctxt {markdown = false}
          end
      )
    )

fun row_antiquotation name scan =
    Document_Output.antiquotation_raw_embedded name 
    scan
    (fn ctxt => 
      (fn (cfg_trans,content:Input.source list) => 
          let val cfg = cfg_trans mt_cell_config
              val _ = writeln ("XXX"^ @{make_string} cfg) 
          in  content |> (map (Document_Output.output_document ctxt {markdown = false})
                          #> List.concat)
          end
      )
    )

fun column_antiquotation name scan =
    Document_Output.antiquotation_raw_embedded name 
    scan
    (fn ctxt => 
      (fn (cfg_trans,content:Input.source list) => 
          let val cfg = cfg_trans mt_cell_config
              val _ = writeln ("XXX"^ @{make_string} cfg) 
          in  content |> (map (Document_Output.output_document ctxt {markdown = false})
                          #> List.concat)
          end
      )
    )

in

val _ = Theory.setup 
           (   table_antiquotation  \<^binding>\<open>table_inline\<close> 
                                    table_parser
            #> table_antiquotation  \<^binding>\<open>subtab\<close> table_parser
            #> cell_antiquotation   \<^binding>\<open>cell\<close>   
                                    (tab_config_parser--Scan.lift Args.cartouche_input)
            #> row_antiquotation    \<^binding>\<open>row\<close>  
                                    (tab_config_parser--Scan.repeat1(Scan.lift Args.cartouche_input))  
            #> column_antiquotation \<^binding>\<open>column\<close> 
                                    (tab_config_parser--Scan.repeat1(Scan.lift Args.cartouche_input))
           );

end
\<close>



(*<*)

declare[[tab_cell_placing="left",tab_cell_height="18.0cm"]]

section\<open>Some Rudimentary Tests\<close>

text\<open> @{fig_content   [display] (height = 80, width=80, caption=\<open>this is \<^term>\<open>\<sigma>\<^sub>i+2\<close> \<dots>\<close>) 
                      \<open>figures/isabelle-architecture.pdf\<close>}\<close>
text\<open> @{table_inline  [display] (cell_placing = center,cell_height =\<open>12.0cm\<close>,
                                 cell_height =\<open>13pt\<close>,  cell_width = \<open>12.0cm\<close>,
                                 cell_bgnd_color=black,cell_line_color=red,cell_line_width=\<open>12.0cm\<close>)
          \<open>\<open>\<^cell>\<open>dfg\<close> \<^col>\<open>dfg\<close> \<^row>\<open>dfg\<close> @{cell (cell_height =\<open>12.0cm\<close>) \<open>abracadabra\<close>}\<close>
           \<open>\<open>1\<close>  \<open>2\<close>  \<open>3\<sigma>\<close>\<close>
          \<close>}
      \<^cell>\<open>dfg\<close>  @{row \<open>is technical\<close> \<open> \<open>\<sigma> * a\<^sub>4\<close> \<close>}\<close>

(*>*)

text\<open>beamer support\<close>
(* Under development *)

doc_class frame =
  options :: string
  frametitle :: string
  framesubtitle :: string

ML\<open>
type frame = {options: Input.source
              , frametitle: Input.source
              , framesubtitle: Input.source}

val empty_frame = {options = Input.empty
                   , frametitle = Input.empty
                   , framesubtitle = Input.empty}: frame

fun make_frame (options, frametitle, framesubtitle) =
  {options = options, frametitle = frametitle, framesubtitle = framesubtitle}

fun upd_frame f =
  fn {options, frametitle, framesubtitle} => make_frame (f (options, frametitle, framesubtitle))

fun upd_options f =
  upd_frame (fn (options, frametitle, framesubtitle) => (f options, frametitle, framesubtitle))

fun upd_frametitle f =
  upd_frame (fn (options, frametitle, framesubtitle) => (options, f frametitle, framesubtitle))

fun upd_framesubtitle f =
  upd_frame (fn (options, frametitle, framesubtitle) => (options, frametitle, f framesubtitle))

type block = {title: Input.source}

val empty_block = {title = Input.empty}

fun make_block title = {title = title}

fun upd_block f =
  fn {title} => make_block (f title)

fun upd_block_title f =
  upd_block (fn title => f title)

val unenclose_string = unenclose o unenclose

fun read_string s =
  let val s' = DOF_core.markup2string s
      val symbols = s' |> Symbol_Pos.explode0
  in if hd symbols |> fst |> equal Symbol.open_
     then Token.read_cartouche symbols |> Token.input_of
     else unenclose_string s' |> Syntax.read_input
  end

val block_titleN = "title"

fun block_modes (ctxt, toks) =
  let val (y, toks') = ((((Scan.optional
                (Args.parens
                   (Parse.list1
                     ((Args.$$$ block_titleN |-- Args.$$$ "=" -- Parse.document_source
                          >> (fn (_, k) => upd_block_title (K k)))
                      ))) [K empty_block])
                : (block -> block) list parser)
                >> (foldl1 (op #>)))
                : (block -> block) parser)
                (toks)
  in (y, (ctxt, toks')) end

fun process_args cfg_trans =
  let val {title} = cfg_trans empty_block
  in title end

fun block ctxt (cfg_trans,src) =
  let val title = process_args cfg_trans
  in Latex.string "{"
     @ (title |> Document_Output.output_document ctxt {markdown = false})
     @ Latex.string "}"
     @ (src |> Document_Output.output_document ctxt {markdown = false})
     |> (Latex.environment "block")
  end

fun block_antiquotation name scan =
  (Document_Output.antiquotation_raw_embedded name
    (scan : ((block -> block) * Input.source) context_parser)
    (block: Proof.context -> (block -> block) * Input.source -> Latex.text));

val _ = block_antiquotation \<^binding>\<open>block\<close> (block_modes -- Scan.lift Parse.document_source)
        |> Theory.setup

fun convert_meta_args ctxt (X, (((str,_),value) :: R)) =
    (case YXML.content_of str of
         "frametitle" =>  upd_frametitle (K(YXML.content_of value |> read_string))
                            o convert_meta_args ctxt (X, R)
       | "framesubtitle" => upd_framesubtitle (K(YXML.content_of value |> read_string))
                              o convert_meta_args ctxt (X, R)
       | "options" => upd_options (K(YXML.content_of value |> read_string))
                        o convert_meta_args ctxt (X, R)
       | s => error("!undefined attribute:"^s))
  | convert_meta_args _ (_,[]) = I

fun frame_command (name, pos) descr cid  =
  let fun set_default_class NONE = SOME(cid,pos)
         |set_default_class (SOME X) = SOME X
      fun create_instance  (((binding,cid_pos), doc_attrs) : ODL_Meta_Args_Parser.meta_args_t)  =
                Value_Command.Docitem_Parser.create_and_check_docitem
               {is_monitor = false}
               {is_inline = true}
               {define = true} binding (set_default_class cid_pos) doc_attrs
      fun titles_src ctxt frametitle framesubtitle src =
        Latex.string "{"
        @ Document_Output.output_document ctxt {markdown = false} frametitle
        @ Latex.string "}"
        @ Latex.string "{"
        @ (Document_Output.output_document ctxt {markdown = false} framesubtitle)
        @ Latex.string "}"
        @ Document_Output.output_document ctxt {markdown = true} src
      fun generate_src_ltx_ctxt ctxt src cfg_trans =
        let val {options, frametitle, framesubtitle} = cfg_trans empty_frame
        in
          let val options_str = Input.string_of options
          in if options_str = ""
             then titles_src ctxt frametitle framesubtitle src
             else (options_str
                   |> enclose "[" "]"
                   |> Latex.string)
                   @ titles_src ctxt frametitle framesubtitle src
          end
       end
      fun parse_and_tex (margs, src) ctxt =
        convert_meta_args ctxt margs
        |> generate_src_ltx_ctxt ctxt src
        |> Latex.environment ("frame")
        |> Latex.environment ("isamarkuptext")
  in Monitor_Command_Parser.onto_macro_cmd_command (name, pos) descr create_instance parse_and_tex
  end

val _ = frame_command \<^command_keyword>\<open>frame*\<close> "frame environment" "Isa_COL.frame" ;
\<close>

end
