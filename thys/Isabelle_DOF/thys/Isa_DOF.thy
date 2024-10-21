(*************************************************************************
 * Copyright (C) 
 *               2019-2022 The University of Exeter 
 *               2018-2022 The University of Paris-Saclay
 *               2018      The University of Sheffield
 *
 * License:
 *   This program can be redistributed and/or modified under the terms
 *   of the 2-clause BSD-style license.
 *
 *   SPDX-License-Identifier: BSD-2-Clause
 *************************************************************************)

chapter \<open>The Document Ontology Framework for Isabelle\<close>

text\<open> Offering 
\<^item> text-elements that can be annotated with meta-information
\<^item> typed links to text-elements via specifically generated anti-quotations
\<^item> typed structure of this meta-information specifiable in an Ontology-Language ODL
  providing syntax and PIDE support of document classes 
\<^item> inner-syntax-antiquotations (ISA's) allowing to reference Isabelle-entities such as 
  types, terms, theorems inside the meta-information
\<^item> monitors allowing to enforce a specific textual structure of an Isabelle Document
\<^item> a basic infrastructure to define class invariants
  (for continuous checking of meta-information side-conditions of text-elements 
\<^item> LaTeX support. \<close> 
  
text\<open> In this section, we develop on the basis of a management of references Isar-markups
that provide direct support in the PIDE framework. \<close> 
  
theory Isa_DOF                (* Isabelle Document Ontology Framework *)
  imports  Main  
           RegExpInterface    (* Interface to functional regular automata for monitoring *)
           
  keywords "+=" ":=" "accepts"  "rejects" "invariant"
           
  and      "open_monitor*"      "close_monitor*" 
           "declare_reference*" "update_instance*"
           "doc_class"          "onto_class" (* a syntactic alternative *)
           "onto_morphism"                                 :: thy_decl
  and      "to"
  and      "ML*"
           "define_shortcut*"   "define_macro*"            :: thy_decl
  
  and      "definition*"                                   :: thy_defn
  and      "theorem*" "lemma*" "corollary*" "proposition*" :: thy_goal_stmt
  and      "schematic_goal*" :: thy_goal_stmt

  and      "text*"              "text-macro*"              :: document_body
  and      "term*"   "value*"   "assert*"                  :: document_body

  and      "use_template" "use_ontology"                   :: thy_decl
  and      "define_template" "define_ontology"             :: thy_load
  and      "print_doc_classes"        "print_doc_items" 
           "print_doc_class_template" "check_doc_global"
           "list_ontologies" "list_templates"              :: diag

      

           
  
begin

text\<open> @{footnote \<open>sdf\<close>}, @{file "$ISABELLE_HOME/src/Pure/ROOT.ML"}\<close> 

section\<open>Primitive Markup Generators\<close>
ML\<open>

val docrefN   = "docref";    
val docclassN = "doc_class";
val onto_classN = "onto_class";

(** name components **)

val defN = "def"
val def_suffixN = "_" ^ defN
val defsN = defN ^ "s"
val instances_of_suffixN = "_instances"
val invariant_suffixN = "_inv"
val monitor_suffixN = "_monitor"
val instance_placeholderN = "\<sigma>"
val makeN = "make"
val schemeN = "_scheme"
val instanceN = "instance"
val monitor_infoN = "monitor_info"
val isa_transformerN = "isa_transformer"
val ml_invariantN = "ml_invariant"
val traceN = "trace"
\<close>

section\<open> A HomeGrown Document Type Management (the ''Model'') \<close>


ML\<open>
structure DOF_core =
 
struct

  datatype onto_class = Onto_Class of 
    {params         : (string * sort) list,
     name           : binding,
     virtual        : {virtual : bool}, 
     inherits_from  : (typ list * string) option,    (* imports *)
     attribute_decl : (binding*typ*term option)list, (* class local *)
     rejectS        : term list,
     rex            : term list,
     invs           : (binding * term) list  } (* monitoring regexps --- product semantics*)

  fun make_onto_class (params, name, virtual, inherits_from, attribute_decl , rejectS, rex, invs) =
    Onto_Class {params = params, name = name, virtual = virtual, inherits_from = inherits_from
                , attribute_decl = attribute_decl, rejectS = rejectS , rex = rex, invs = invs}

  structure Onto_Classes = Theory_Data
  (
    type T =  onto_class Name_Space.table;
    val empty : T = Name_Space.empty_table onto_classN;
    fun merge data : T = Name_Space.merge_tables data;
  );

  val get_onto_classes = Onto_Classes.get o Proof_Context.theory_of

  (* Get the Onto_Class object from its short name or long name *)
  fun get_onto_class_global name thy  =
    Name_Space.check (Context.Theory thy)
                      (get_onto_classes (Proof_Context.init_global thy)) (name, Position.none) |> #2

  fun markup2string s = Protocol_Message.clean_output s
                        |> Symbol.explode
                        |> List.filter (fn c => c <> Symbol.DEL)
                        |> String.concat

  fun get_name name =
     name |>  markup2string
          |> Symbol.explode_words |> split_last |> #2

  (* Get the Onto_Class object.
     The function does not use the abstract syntax of an onto_class.
     and relies entirely on the associated record created with the onto_class and its type.
     The function takes, for the name argument, a string that has the same form as
     the input of an ML \<^typ>\<open>\<close> anti-quotation to get a record type.
     To get the type of the record ('a, 'b) A, we'll use \<^typ>\<open>('a, 'b) A\<close>.
     So the name argument will be "('a, 'b) A" *) 
  (* does not take class synonyms into account *)
  fun get_onto_class_global' name thy  =
    let val name' = name |> get_name
    in Name_Space.check (Context.Theory thy)
                    (get_onto_classes (Proof_Context.init_global thy)) (name', Position.none) |> #2
    end

  (* Get the full-qualified name of an onto_class from its short name or long name *)
  fun get_onto_class_name_global name thy  =
    Name_Space.check (Context.Theory thy)
                      (get_onto_classes (Proof_Context.init_global thy)) (name, Position.none) |> #1

  (* Get the full-qualified name of an onto-class.
     The function does not use the abstract syntax of an onto_class.
     and relies entirely on the associated record created with the onto_class and its type.
     The function takes, for the name argument, a string that has the same form as
     the input of an ML \<^typ>\<open>\<close> anti-quotation to get a record type.
     To get the type of the record ('a, 'b) A, we'll use \<^typ>\<open>('a, 'b) A\<close>.
     So the name argument will be "('a, 'b) A". *)
  (* does not take class synonyms into account *)
  fun get_onto_class_name_global' name thy  =
    let val name' = name |> get_name
    in Name_Space.check (Context.Theory thy)
                    (get_onto_classes (Proof_Context.init_global thy)) (name', Position.none) |> #1
    end

  (* Get the full-qualified name of an onto-class,
     its string representation with arguments and sorts, and its type
     from its short or long name.
     To get the type of the record ('a::one, 'b) A, we'll use \<^typ>\<open>('a::one, 'b) A\<close>.
     So the name argument will be "('a::one, 'b) A" *)
  (* does not takes class synonyms into account *)
  fun get_onto_class_cid thy name =
    let val cid_typ = name |> Syntax.read_typ_global thy
        val (args, name') = name |> Symbol.explode_words |> split_last
        val name'' = (name', Position.none) |> Name_Space.check (Context.Theory thy)
                                               (get_onto_classes (Proof_Context.init_global thy))
                                              |> fst
        val args_cid = append args [name''] |> space_implode Symbol.space
    in ((name'', args_cid), cid_typ)
    end

  fun check_onto_class ctxt =
    #1 o Name_Space.check (Context.Proof ctxt) (get_onto_classes ctxt);

  fun add_onto_class name onto_class thy =
    thy |> Onto_Classes.map (Name_Space.define (Context.Theory thy) true (name, onto_class) #> #2);

  fun update_onto_class name onto_class thy =
    thy |> Onto_Classes.map (Name_Space.define (Context.Theory thy) false (name, onto_class) #> #2);

  fun map_onto_class_entry name f thy =
    thy |> Onto_Classes.map (Name_Space.map_table_entry (get_onto_class_name_global' name thy)
            (fn Onto_Class
                  {params, name, virtual, inherits_from, attribute_decl, rejectS , rex, invs} =>
              make_onto_class (f (params, name, virtual, inherits_from, attribute_decl,
                                  rejectS , rex, invs))));

  fun map_params name f =
    map_onto_class_entry name (fn (params, name, virtual, inherits_from, attribute_decl,
                                  rejectS , rex, invs) =>
      (f params, name, virtual, inherits_from, attribute_decl, rejectS , rex, invs))

  fun map_name name f =
    map_onto_class_entry name (fn (params, name, virtual, inherits_from, attribute_decl,
                                  rejectS , rex, invs) =>
      (params, f name, virtual, inherits_from, attribute_decl, rejectS , rex, invs))

  fun map_virtual name f =
    map_onto_class_entry name (fn (params, name, virtual, inherits_from, attribute_decl,
                                  rejectS , rex, invs) =>
      (params, name, f virtual, inherits_from, attribute_decl, rejectS , rex, invs))

  fun map_inherits_from name f =
    map_onto_class_entry name (fn (params, name, virtual, inherits_from, attribute_decl,
                                  rejectS , rex, invs) =>
      (params, name, virtual, f inherits_from, attribute_decl, rejectS , rex, invs))

  fun map_attribute_decl name f =
    map_onto_class_entry name (fn (params, name, virtual, inherits_from, attribute_decl,
                                  rejectS , rex, invs) =>
      (params, name, virtual, inherits_from, f attribute_decl, rejectS , rex, invs))

  fun map_rejectS name f =
    map_onto_class_entry name (fn (params, name, virtual, inherits_from, attribute_decl,
                                  rejectS , rex, invs) =>
      (params, name, virtual, inherits_from, attribute_decl, f rejectS , rex, invs))

  fun map_rex name f =
    map_onto_class_entry name (fn (params, name, virtual, inherits_from, attribute_decl,
                                  rejectS , rex, invs) =>
      (params, name, virtual, inherits_from, attribute_decl, rejectS , f rex, invs))

  fun map_invs name f =
    map_onto_class_entry name (fn (params, name, virtual, inherits_from, attribute_decl,
                                  rejectS , rex, invs) =>
      (params, name, virtual, inherits_from, attribute_decl, rejectS , rex, f invs))

  fun rep_onto_class cid thy = get_onto_class_global cid thy |> (fn Onto_Class rep => rep)

  fun params_of cid = #params o rep_onto_class cid
  fun name_of cid = #name o rep_onto_class cid
  fun virtual_of cid = #virtual o rep_onto_class cid
  fun inherits_from_of cid = #inherits_from o rep_onto_class cid
  fun attribute_decl_of cid = #attribute_decl o rep_onto_class cid
  fun rejectS_of cid = #rejectS o rep_onto_class cid
  fun rex_of cid = #rex o rep_onto_class cid
  fun invs_of cid = #invs o rep_onto_class cid

  fun print_onto_classes verbose ctxt =
    Pretty.big_list "Isabelle.DOF Onto_Classes:"
      (map (Pretty.mark_str o #1) (Name_Space.markup_table verbose ctxt (get_onto_classes ctxt)))
    |> Pretty.writeln;

  fun the_onto_class T i =
    (case Name_Space.lookup_key T i of
      SOME entry => entry
    | NONE => raise TYPE ("Unknown onto_class: " ^ quote i, [], []));


   val tag_attr = (\<^binding>\<open>tag_attribute\<close>, \<^Type>\<open>int\<close>, Mixfix.NoSyn)
        (* Attribute hidden to the user and used internally by isabelle_DOF.
           For example, this allows to add a specific id to a class
           to be able to reference the class internally.
        *)

   val default_cid = "text"    (* the top (default) document class: everything is a text.*)

   val default_cid_typ = \<^typ>\<open>unit\<close> (* top document class type *)

(* Due to the implementation, is_subclass0 is _NOT_ compatible with DOF classes type synonyms,
   so they must be resolved to full class names before use. *)
  fun is_subclass0 s t ctxt =
    let fun get id = if id = default_cid
                     then default_cid
                     else get_onto_class_name_global id (Proof_Context.theory_of ctxt)
        val s' = get s
        val t' = get t
        fun father_is_sub s = case get_onto_class_global s (Proof_Context.theory_of ctxt)  of 
                                  (Onto_Class {inherits_from=NONE, ...}) => s = t'
                                | (Onto_Class {inherits_from=SOME (_, s''), ...}) =>
                                    s'' = t' orelse father_is_sub s''
        val s'_defined = s' |> Name_Space.declared (get_onto_classes ctxt
                                                    |> Name_Space.space_of_table)
    in s' = t' orelse
       (t' = default_cid  andalso s'_defined) orelse
       (s' <> default_cid andalso father_is_sub s')
    end


  datatype instance = Instance of 
    {defined: bool,
     input_term: term,
     value: term,
     inline: bool, 
     cid: string,
     vcid: string option}

  val undefined_instance = "undefined_instance"

  val undefined_value = Free ("Undefined_Value", default_cid_typ)

  val empty_instance = Instance {defined = false,
     input_term = \<^term>\<open>()\<close>,
     value = \<^term>\<open>()\<close>,
     inline = false, 
     cid = "",
     vcid = NONE}

  fun make_instance (defined, input_term, value, inline, cid, vcid) =
    Instance {defined = defined, input_term = input_term, value = value, inline = inline
              , cid = cid, vcid = vcid}

  structure Instances = Theory_Data
  (
    type T =  instance Name_Space.table;
    val empty : T = Name_Space.empty_table instanceN;
    fun merge data : T = Name_Space.merge_tables data;
  );

  val get_instances = Instances.get o Proof_Context.theory_of

  fun get_instance_global oid thy  =
    Name_Space.check (Context.Theory thy)
                      (get_instances (Proof_Context.init_global thy)) (oid, Position.none) |> #2

  fun get_instance_name_global oid thy  =
    Name_Space.check (Context.Theory thy)
                      (get_instances (Proof_Context.init_global thy)) (oid, Position.none) |> #1

  fun check_instance ctxt =
    #1 o Name_Space.check (Context.Proof ctxt) (get_instances ctxt);

  fun add_instance name instance thy =
    thy |> Instances.map (Name_Space.define (Context.Theory thy) true (name, instance) #> #2);

  fun update_instance name instance thy =
    thy |> Instances.map (Name_Space.define (Context.Theory thy) false (name, instance) #> #2);

  fun map_instance_entry name f thy =
    thy |> Instances.map (Name_Space.map_table_entry (get_instance_name_global name thy)
            (fn Instance {defined, input_term, value, inline, cid, vcid} =>
              make_instance (f (defined, input_term, value, inline, cid, vcid))));

  fun map_defined name f =
    map_instance_entry name (fn (defined, input_term, value, inline, cid, vcid) =>
      (f defined, input_term, value, inline, cid, vcid))

  fun map_input_term name f =
    map_instance_entry name (fn (defined, input_term, value, inline, cid, vcid) =>
      (defined, f input_term, value, inline, cid, vcid))

  fun map_value name f =
    map_instance_entry name (fn (defined, input_term, value, inline, cid, vcid) =>
      (defined, input_term, f value, inline, cid, vcid))

  fun map_input_term_value name f g =
    map_instance_entry name (fn (defined, input_term, value, inline, cid, vcid) =>
      (defined, f input_term, g value, inline, cid, vcid))

  fun map_inline name f =
    map_instance_entry name (fn (defined, input_term, value, inline, cid, vcid) =>
      (defined, input_term, value, f inline, cid, vcid))

  fun map_cid name f =
    map_instance_entry name (fn (defined, input_term, value, inline, cid, vcid) =>
      (defined, input_term, value, inline, f cid, vcid))

  fun map_vcid name f =
    map_instance_entry name (fn (defined, input_term, value, inline, cid, vcid) =>
      (defined, input_term, value, inline, cid, f vcid))

  fun print_instances verbose ctxt =
    Pretty.big_list "Isabelle.DOF Instances:"
      (map (Pretty.mark_str o #1) (Name_Space.markup_table verbose ctxt (get_instances ctxt)))
    |> Pretty.writeln;

  fun the_instance T i =
    (case Name_Space.lookup_key T i of
      SOME entry => entry
    | NONE => raise TYPE ("Unknown instance: " ^ quote i, [], []));

  fun rep_instance oid thy = get_instance_global oid thy |> (fn Instance rep => rep)

  fun defined_of oid = #defined o rep_instance oid
  fun input_term_of oid = #input_term o rep_instance oid
  fun value_of oid = #value o rep_instance oid
  fun inline_of oid = #inline o rep_instance oid
  fun cid_of oid = #cid o rep_instance oid
  fun vcid_of oid = #vcid o rep_instance oid


  datatype isa_transformer = ISA_Transformer of 
    {check     : (theory -> term * typ * Position.T -> string -> term option),
     elaborate : (theory -> string -> typ -> term option -> Position.T -> term)}

  fun make_isa_transformer (check, elaborate) =
    ISA_Transformer {check = check, elaborate = elaborate}

  structure ISA_Transformers = Theory_Data
  (
    type T = isa_transformer Name_Space.table;
    val empty : T = Name_Space.empty_table isa_transformerN;
    fun merge data : T = Name_Space.merge_tables data;
  );

  val get_isa_transformers = ISA_Transformers.get o Proof_Context.theory_of

  fun get_isa_transformer_global id thy  =
    Name_Space.check (Context.Theory thy)
                    (get_isa_transformers (Proof_Context.init_global thy)) (id, Position.none) |> #2

  fun get_isa_transformer_name_global id thy  =
    Name_Space.check (Context.Theory thy)
                    (get_isa_transformers (Proof_Context.init_global thy)) (id, Position.none) |> #1

  fun check_isa_transformer ctxt =
    #1 o Name_Space.check (Context.Proof ctxt) (get_isa_transformers ctxt);

  fun add_isa_transformer name isa_transformer thy =
    thy |> ISA_Transformers.map
      (Name_Space.define (Context.Theory thy) true (name, isa_transformer) #> #2);

  fun update_isa_transformer name isa_transformer thy =
    thy |> ISA_Transformers.map
      (Name_Space.define (Context.Theory thy) false (name, isa_transformer) #> #2);

  fun map_isa_transformer_entry name f thy =
    thy |> ISA_Transformers.map (Name_Space.map_table_entry (get_isa_transformer_name_global name thy)
            (fn ISA_Transformer {check, elaborate} => make_isa_transformer (f (check, elaborate))));

  fun map_check name f =
    map_isa_transformer_entry name (fn (check, elaborate) => (f check, elaborate))

  fun map_elaborate name f =
    map_isa_transformer_entry name (fn (check, elaborate) => (check, f elaborate))

  fun rep_isa_transformer id thy = get_isa_transformer_global id thy
                                   |> (fn ISA_Transformer rep => rep)

  fun check_of id = #check o rep_isa_transformer id
  fun elaborate_of id = #elaborate o rep_isa_transformer id

  fun print_isa_transformers verbose ctxt =
    Pretty.big_list "Isabelle.DOF ISA_Transformers:"
      (map (Pretty.mark_str o #1) (Name_Space.markup_table verbose ctxt (get_isa_transformers ctxt)))
    |> Pretty.writeln;

  fun the_isa_transformer T i =
    (case Name_Space.lookup_key T i of
      SOME entry => entry
    | NONE => raise TYPE ("Unknown isa_transformer: " ^ quote i, [], []));


  datatype ml_invariant = ML_Invariant of
    {check : string -> {is_monitor:bool} -> Context.generic -> bool
     , class : string}

  fun make_ml_invariant (check, class) =
    ML_Invariant {check = check, class = class}

  structure ML_Invariants = Theory_Data
  (
    type T = (ml_invariant Name_Space.table * ml_invariant Name_Space.table)
             * ml_invariant Name_Space.table;
    val empty : T = ((Name_Space.empty_table ml_invariantN
                      , Name_Space.empty_table ("opening_" ^ ml_invariantN))
                      , Name_Space.empty_table ("closing_" ^ ml_invariantN));
    fun merge (((ml_invariants1, opening_ml_invariants1), closing_ml_invariants1)
                , ((ml_invariants2, opening_ml_invariants2), closing_ml_invariants2)) =
        ((Name_Space.merge_tables (ml_invariants1, ml_invariants2)
        , Name_Space.merge_tables (opening_ml_invariants1, opening_ml_invariants2))
        , Name_Space.merge_tables (closing_ml_invariants1, closing_ml_invariants2));
  );

  fun get_invariants which = which o ML_Invariants.get o Proof_Context.theory_of

  val get_ml_invariants = get_invariants (fst o fst)

  val get_opening_ml_invariants = get_invariants (snd o fst)

  val get_closing_ml_invariants = get_invariants snd

  fun get_invariant_global which cid thy  =
    Name_Space.check (Context.Theory thy)
                  (get_invariants which (Proof_Context.init_global thy)) (cid, Position.none) |> #2

  val get_ml_invariant_global = get_invariant_global (fst o fst)

  val get_opening_ml_invariant_global = get_invariant_global (snd o fst)

  val get_closing_ml_invariant_global = get_invariant_global snd

  fun get_invariant_name_global which cid thy  =
    Name_Space.check (Context.Theory thy)
                  (get_invariants which (Proof_Context.init_global thy)) (cid, Position.none) |> #1

  val get_ml_invariant_name_global = get_invariant_name_global (fst o fst)

  val get_opening_ml_invariant_name_global = get_invariant_name_global (snd o fst)

  val get_closing_ml_invariant_name_global = get_invariant_name_global snd

  fun check_invariant which ctxt =
    #1 o Name_Space.check (Context.Proof ctxt) (get_invariants which ctxt);

  val check_ml_invariant = check_invariant (fst o fst)

  val check_opening_ml_invariant = check_invariant (snd o fst)

  val check_closing_ml_invariant = check_invariant snd

  fun add_invariant (get, ap) name invariant thy =
    let
      val table =
        ML_Invariants.get thy |> get
                              |> (Name_Space.define (Context.Theory thy) true (name, invariant))
                              |> snd
    in (ML_Invariants.map o ap) (K table) thy end

  val add_ml_invariant = add_invariant (fst o fst, apfst o apfst)

  val add_opening_ml_invariant = add_invariant (snd o fst, apfst o apsnd)

  val add_closing_ml_invariant = add_invariant (snd, apsnd)

  fun update_invariant (get, ap) name invariant thy =
    let
      val table =
        ML_Invariants.get thy |> get
                              |> (Name_Space.define (Context.Theory thy) false (name, invariant))
                              |> snd
    in (ML_Invariants.map o ap) (K table) thy end

  val update_ml_invariant = update_invariant (fst o fst, apfst o apfst)

  val update_opening_ml_invariant = update_invariant (snd o fst, apfst o apsnd)

  val update_closing_ml_invariant = update_invariant (snd, apsnd)

  fun map_invariant_entry (get, ap) name f thy =
    thy |> (ML_Invariants.map o ap) (Name_Space.map_table_entry (get_invariant_name_global get name thy)
            (fn ML_Invariant {check, class} => make_ml_invariant (f (check, class))));

  val map_ml_invariant_entry = map_invariant_entry (fst o fst, apfst o apfst)

  val map_opening_ml_invariant_entry = map_invariant_entry (snd o fst , apfst o apsnd)

  val map_closing_ml_invariant_entry = map_invariant_entry (snd, apsnd)

  fun map_invariant_check (get, ap) name f =
    map_invariant_entry (get, ap) name (fn (check, class) => (f check, class))

  val map_ml_invariant_check = map_invariant_check (fst o fst, apfst o apfst)

  val map_opening_ml_invariant_check = map_invariant_check (snd o fst, apfst o apsnd)

  val map_closing_ml_invariant_check = map_invariant_check (snd, apsnd)

  fun map_invariant_class (get, ap) name f =
    map_invariant_entry (get, ap) name (fn (check, class) => (check, f class))

  val map_ml_invariant_class = map_invariant_class (fst o fst, apfst o apfst)

  val map_opening_ml_invariant_class = map_invariant_class (snd o fst , apfst o apsnd)

  val map_closing_ml_invariant_class = map_invariant_class (snd, apsnd)

  fun rep_invariant which id thy = get_invariant_global which id thy |> (fn ML_Invariant rep => rep)

  val rep_ml_invariant = rep_invariant (fst o fst)

  val rep_opening_ml_invariant = rep_invariant (snd o fst)

  val rep_closing_ml_invariant = rep_invariant snd

  fun invariant_check_of which id = #check o rep_invariant which id

  val ml_invariant_check_of = invariant_check_of (fst o fst)

  val opening_ml_invariant_check_of = invariant_check_of (snd o fst)

  val closing_ml_invariant_check_of = invariant_check_of snd

  fun invariant_class_of which id = #class o rep_invariant which id

  val ml_invariant_class_of = invariant_class_of (fst o fst)

  val opening_ml_invariant_class_of = invariant_class_of (snd o fst)

  val closing_ml_invariant_class_of = invariant_class_of snd

  fun print_invariants which verbose ctxt =
    Pretty.big_list "Isabelle.DOF ML_Invariants:"
      (map (Pretty.mark_str o #1) (Name_Space.markup_table verbose ctxt (get_invariants which ctxt)))
    |> Pretty.writeln;

  val print_ml_invariants = print_invariants (fst o fst)

  val print_opening_ml_invariants = print_invariants (snd o fst)

  val print_closing_ml_invariants = print_invariants snd

  fun the_invariant which thy i =
    (case (ML_Invariants.get thy |> which |> Name_Space.lookup_key) i of
      SOME entry => entry
    | NONE => raise TYPE ("Unknown ml_invariant: " ^ quote i, [], []));

  val the_ml_invariant = the_invariant (fst o fst)

  val the_opening_ml_invariant = the_invariant (snd o fst)

  val the_closing_ml_invariant = the_invariant snd

  (* Monitor infos are not integrated to an instance datatype
     to avoid issues when comparing objects.
     Indeed automata do not have an equality type and then,
     should two instances with monitor infos be compared, an error will be triggered.
     So monitor infos are defined in their own name space.
     They are declared when opening a monitor and have the same
     reference (the key of the name space table) as their related monitor instance:
     the name of the instance prefixed by the theory. *)
  datatype monitor_info = Monitor_Info of 
    {accepted_cids : RegExpInterface.env,
     rejected_cids : RegExpInterface.env,
     automatas     : RegExpInterface.automaton list}


  fun make_monitor_info (accepted_cids, rejected_cids, automatas) =
    Monitor_Info {accepted_cids = accepted_cids,
                  rejected_cids = rejected_cids,
                  automatas = automatas}

  structure Monitor_Info = Theory_Data
  (
    type T =  monitor_info Name_Space.table;
    val empty : T = Name_Space.empty_table monitor_infoN;
    fun merge data : T = Name_Space.merge_tables data;
  );

  val get_monitor_infos = Monitor_Info.get o Proof_Context.theory_of

  fun get_monitor_info_global oid thy  =
    Name_Space.check (Context.Theory thy)
                      (get_monitor_infos (Proof_Context.init_global thy)) (oid, Position.none) |> #2

  fun get_monitor_info_name_global oid thy  =
    Name_Space.check (Context.Theory thy)
                      (get_monitor_infos (Proof_Context.init_global thy)) (oid, Position.none) |> #1

  fun check_monitor_info ctxt =
    #1 o Name_Space.check (Context.Proof ctxt) (get_monitor_infos ctxt);

  fun add_monitor_info name monitor_info thy =
    thy |> Monitor_Info.map
      (Name_Space.define (Context.Theory thy) true (name, monitor_info) #> #2);

  fun update_monitor_info name monitor_info thy =
    thy |> Monitor_Info.map
      (Name_Space.define (Context.Theory thy) false (name, monitor_info) #> #2);

  fun map_monitor_info_entry name f thy =
    thy |> Monitor_Info.map
            (Name_Space.map_table_entry (get_monitor_info_name_global name thy)
            (fn Monitor_Info {accepted_cids, rejected_cids, automatas} =>
              make_monitor_info (f (accepted_cids, rejected_cids, automatas))));

  fun map_monitor_info_accepted_cids name f =
    map_monitor_info_entry name (fn (accepted_cids, rejected_cids, automatas) =>
                                  (f accepted_cids, rejected_cids, automatas))

  fun map_monitor_info_rejected_cids name f =
    map_monitor_info_entry name (fn (accepted_cids, rejected_cids, automatas) =>
                                  (accepted_cids, f rejected_cids, automatas))

  fun map_monitor_info_automatas name f =
    map_monitor_info_entry name (fn (accepted_cids, rejected_cids, automatas) =>
                                  (accepted_cids, rejected_cids, f automatas))

  fun rep_monitor_info id thy = get_monitor_info_global id thy |> (fn Monitor_Info rep => rep)

  fun accepted_cids_of id = #accepted_cids o rep_monitor_info id
  fun rejected_cids_of id = #rejected_cids o rep_monitor_info id
  fun automatas_of id = #automatas o rep_monitor_info id
  fun alphabet_of id thy = (accepted_cids_of id thy) @ (rejected_cids_of id thy)

  fun print_monitors_infos verbose ctxt =
    Pretty.big_list "Isabelle.DOF Monitor_Infos:"
      (map (Pretty.mark_str o #1) (Name_Space.markup_table verbose ctxt (get_monitor_infos ctxt)))
    |> Pretty.writeln;

  fun the_monitor_info T i =
    (case Name_Space.lookup_key T i of
      SOME entry => entry
    | NONE => raise TYPE ("Unknown monitor_info: " ^ quote i, [], []));


(* doc-class-name management: We still use the record-package for internally 
   representing doc-classes. The main motivation is that "links" to entities are
   types over doc-classes, *types* in the Isabelle sense, enriched by additional data.
   This has the advantage that the type-inference can be abused to infer long-names
   for doc-class-names. Note, however, that doc-classes are currently implemented
   by non-polymorphic records only; this means that the extensible "_ext" versions
   of type names must be reduced to qualifier names only. The used Syntax.parse_typ 
   handling the identification does that already. *)
 
fun is_subclass (ctxt) s t = is_subclass0 s t ctxt
fun is_subclass_global thy s t = let val ctxt = Proof_Context.init_global thy
                                 in  is_subclass0  s t ctxt end

fun check_regexps term = 
    let val _ = case fold_aterms  Term.add_free_names term [] of
                   n::_ => error("No free variables allowed in monitor regexp:" ^ n)
                 | _ => ()  
        val _ = case fold_aterms  Term.add_var_names term [] of
                   (n,_)::_ => error("No schematic variables allowed in monitor regexp:" ^ n)
                 | _ => ()
        (* Missing: Checks on constants such as undefined, ... *)
    in  term end

fun check_reject_atom term = 
    let val _ = case fold_aterms  Term.add_free_names term [] of
                   n::_ => error("No free variables allowed in monitor regexp:" ^ n)
                 | _ => ()  
        val _ = case fold_aterms  Term.add_var_names term [] of
                   (n,_)::_ => error("No schematic variables allowed in monitor regexp:" ^ n)
                 | _ => ()
        (* Missing: Checks on constants such as undefined, ... *)
    in  term end


fun define_doc_class_global (params', binding) parent fields rexp reject_Atoms invs virtual thy  = 
(* This operation is executed in a context where the record has already been defined, but
   its conversion into a class is not yet done. *)
    let val rejectS = map (Syntax.read_term_global thy) reject_Atoms;
        val _ = map (check_reject_atom) rejectS; 
        val reg_exps = map (Syntax.read_term_global thy) rexp;
        val _ = map check_regexps reg_exps
        val _ = if not(null rejectS) andalso (null reg_exps) 
                then  error ("reject clause requires accept clause ! " ) else ();
        val _ = if invs |> map (Binding.name_of o fst) |> has_duplicates (uncurry equal)
                then invs |> hd |> fst |> Binding.pos_of
                     |> (fn pos => error("invariant labels must be unique"^  Position.here pos)) 
                else ()
        val invs' = map (apsnd(Syntax.read_term_global thy)) invs 
    in  thy |> add_onto_class binding (make_onto_class (params', binding, virtual, parent, fields
                                                        , rejectS, reg_exps, invs'))
    end

fun define_object_global {define = define} (binding, instance) thy  = 
  let
    val oid = Binding.name_of binding
    val pos = Binding.pos_of binding
    val _ = if oid = undefined_instance
            then error (oid ^ ": This name is reserved by the implementation" ^ Position.here pos)
            else ()
    val (oid', instance') = Name_Space.check (Context.Theory thy)
                                (get_instances (Proof_Context.init_global thy)) (oid, Position.none)
                                handle ERROR _ => (undefined_instance, empty_instance)
    val Instance {input_term, value, inline, cid, vcid, ...} = instance
    val instance_args= (define, input_term, value, inline, cid, vcid)
    val instance'' = make_instance instance_args 
  in if oid' = undefined_instance andalso instance' = empty_instance
     then (* declare instance using declare_reference* or else define instance *)
          add_instance binding instance'' thy
     else if define
          then let val Instance {defined, ...} = instance'
               in  if defined
                   then (* trigger error when adding already defined instance *)
                        add_instance binding instance'' thy
                   else (* define already declared instance *)
                        map_instance_entry oid' (K instance_args) thy end
          else (* trigger error with declare_reference* when declaring already declared instance *)
               add_instance binding instance thy
  end

fun get_attributes_local cid ctxt =
  if cid = default_cid then []
  else let val cid_long = get_onto_class_name_global cid (Proof_Context.theory_of ctxt)
       in 
       case get_onto_class_global cid_long (Proof_Context.theory_of ctxt) of
           Onto_Class {inherits_from=NONE,
                       attribute_decl = X, ...} => [(cid_long,X)]
         | Onto_Class {inherits_from=SOME(_, father), attribute_decl = X, ...} =>
            get_attributes_local father ctxt @ [(cid_long,X)]
       end

fun get_attributes cid thy = get_attributes_local cid (Proof_Context.init_global thy)


fun get_all_attributes_local cid ctxt =
 (tag_attr, get_attributes_local cid ctxt)

fun get_all_attributes cid thy = get_all_attributes_local cid (Proof_Context.init_global thy)


type attributes_info = { def_occurrence : string,
                         def_pos        : Position.T,
                         long_name      : string,
                         typ            : typ
                       }

fun get_attribute_info_local (*long*)cid attr ctxt : attributes_info option=
    let val hierarchy = get_attributes_local cid ctxt  (* search in order *)
        fun found (s,L) = case find_first (fn (bind,_,_) => Binding.name_of bind = attr) L of
                            NONE => NONE
                          | SOME X => SOME(s,X)
    in  case get_first found hierarchy of
           NONE => NONE
         | SOME (cid',(bind, ty,_)) => SOME({def_occurrence = cid,
                                             def_pos = Binding.pos_of bind,
                                             long_name = cid'^"."^(Binding.name_of bind), 
                                             typ = ty})
    end

fun get_attribute_info (*long*)cid attr thy =
  get_attribute_info_local cid attr (Proof_Context.init_global thy)

fun get_attribute_defaults (* long*)cid thy = 
    let val attrS = flat(map snd (get_attributes cid thy))
        fun trans (_,_,NONE) = NONE
           |trans (na,ty,SOME def) =SOME(na,ty, def)
    in  map_filter trans attrS end


fun binding_from_pos get_objects get_object_name name thy  =
  let
    val ns = get_objects (Proof_Context.init_global thy)
                         |> Name_Space.space_of_table 
    val {pos, ...} = Name_Space.the_entry ns (get_object_name name thy)
  in if Long_Name.is_qualified name
     then Binding.make (Long_Name.base_name name, pos)
     else Binding.make (name, pos)end

fun binding_from_onto_class_pos name thy  =
  binding_from_pos get_onto_classes get_onto_class_name_global name thy

fun binding_from_instance_pos name thy  =
  binding_from_pos get_instances get_instance_name_global name thy

fun check_invs get_ml_invs invariant_class_of invariant_check_of cid_long oid is_monitor thy =
  thy |> Context.Theory
      |> (fn ctxt =>
            let val invs = get_ml_invs (Proof_Context.init_global thy)
                                              |> Name_Space.dest_table
                val checks = invs |> filter (fn (name, _) => 
                                                equal (invariant_class_of name thy) cid_long)
                                  |> map (fn (name, _) => invariant_check_of name thy)
                                  |> map (fn check => check oid is_monitor ctxt)
            in (forall I checks) end)

val check_ml_invs = check_invs get_ml_invariants ml_invariant_class_of ml_invariant_check_of

val check_opening_ml_invs =
  check_invs get_opening_ml_invariants opening_ml_invariant_class_of opening_ml_invariant_check_of

val check_closing_ml_invs =
  check_invs get_closing_ml_invariants closing_ml_invariant_class_of closing_ml_invariant_check_of

(* Output name for LaTeX macros.
   Also rewrite "." to allow macros with objects long names
   and "\<^sub>" allowed in name bindings and then in instance names *)
val output_name = Symbol.explode
                  #> map (fn s => if equal s Symbol.sub then "SUB" else s)
                  #> implode
                  #> translate_string (fn "." => "DOT" | s => s)
                  #> Latex.output_name

val ISA_prefix = "Isabelle_DOF_"

val doc_class_prefix = ISA_prefix ^ "doc_class_"

val long_doc_class_prefix = ISA_prefix ^ "long_doc_class_"

fun is_ISA s = String.isPrefix ISA_prefix (Long_Name.base_name s)


fun transduce_term_global {mk_elaboration=mk_elaboration} (term,pos) thy =
    (* pre: term should be fully typed in order to allow type-related term-transformations *)
    let val ctxt = Proof_Context.init_global thy
        val tab = get_isa_transformers ctxt  
        fun T(Const(s,ty) $ t) =
                if is_ISA s
                then let val name = check_isa_transformer ctxt (s, Position.none)
                         val (_, ISA_Transformer {check, elaborate}) = the_isa_transformer tab name
                     in case check thy (t,ty,pos) s of
                            NONE => Const(s,ty) $ t
                            (* checking isa, may raise error though. *)
                         | SOME t => if mk_elaboration 
                                     then elaborate thy s ty (SOME t) pos
                                     else Const(s,ty) $ t
                                     (* transforming isa *)
                     end
                else (Const(s,ty) $ (T t))
          | T(t1 $ t2) = T(t1) $ T(t2)
          | T(Const(s,ty)) =
                if is_ISA s
                then 
                  let val name = check_isa_transformer ctxt (s, Position.none)
                      val (_, ISA_Transformer {elaborate, ...}) = the_isa_transformer tab name
                  in if mk_elaboration 
                     then elaborate thy s ty NONE pos
                     else Const(s, ty)
                     (* transforming isa *)
                  end
                else Const(s, ty)
          | T(Abs(s,ty,t)) = Abs(s,ty,T t)
          | T t = t
    in T term end

(* Elaborate an Isabelle_DOF term-antiquotation from an only parsed-term (not checked) *)
fun parsed_elaborate ctxt pos (Const(s,ty) $ t) =
        if is_ISA s
        then Syntax.check_term ctxt (Const(s, ty) $ t)
             |> (fn t => transduce_term_global {mk_elaboration=true} (t , pos)
                                  (Proof_Context.theory_of ctxt))
        else (Const(s,ty) $ (parsed_elaborate ctxt pos t))
  | parsed_elaborate ctxt pos (t1 $ t2) = parsed_elaborate ctxt pos (t1) $ parsed_elaborate ctxt pos (t2)
  | parsed_elaborate ctxt pos (Const(s,ty)) =
        if is_ISA s
        then Syntax.check_term ctxt (Const(s, ty))
             |> (fn t => transduce_term_global {mk_elaboration=true} (t , pos)
                                  (Proof_Context.theory_of ctxt))
        else Const(s,ty)
  | parsed_elaborate ctxt pos (Abs(s,ty,t)) = Abs (s,ty,parsed_elaborate ctxt pos t)
  | parsed_elaborate _ _ t = t

fun elaborate_term' ctxt parsed_term = parsed_elaborate ctxt Position.none parsed_term

fun elaborate_term ctxt term = transduce_term_global {mk_elaboration=true}
                                                              (term , Position.none)
                                                              (Proof_Context.theory_of ctxt)

fun check_term ctxt term = transduce_term_global {mk_elaboration=false}
                                                              (term , Position.none)
                                                              (Proof_Context.theory_of ctxt)

(* Check an Isabelle_DOF term-antiquotation from an only parsed-term (not checked) *)
fun parsed_check ctxt pos (Const(s,ty) $ t) =
        if is_ISA s
        then let val _ = Syntax.check_term ctxt (Const(s, ty) $ t)
                         |> (fn t => transduce_term_global {mk_elaboration=false} (t , pos)
                                  (Proof_Context.theory_of ctxt))
             in (Const(s,ty) $ (parsed_check ctxt pos t)) end
        else (Const(s,ty) $ (parsed_check ctxt pos t))
  | parsed_check ctxt pos (t1 $ t2) = parsed_check ctxt pos (t1) $ parsed_check ctxt pos (t2)
  | parsed_check ctxt pos (Const(s,ty)) =
        if is_ISA s
        then let val _ = Syntax.check_term ctxt (Const(s, ty))
                         |> (fn t => transduce_term_global {mk_elaboration=false} (t , pos)
                                  (Proof_Context.theory_of ctxt))
             in Const(s,ty) end
        else Const(s,ty)
  | parsed_check ctxt pos (Abs(s,ty,t)) = Abs (s,ty,parsed_check ctxt pos t)
  | parsed_check _ _ t = t

fun check_term' ctxt parsed_term = parsed_check ctxt Position.none parsed_term

fun prep_decls prep_var raw_vars ctxt =
  let
    val (vars, ctxt') = fold_map prep_var raw_vars ctxt;
    val (xs, ctxt'') = ctxt'
      |> Context_Position.set_visible false
      |> Proof_Context.add_fixes vars
      ||> Context_Position.restore_visible ctxt';
    val _ =
      Context_Position.reports ctxt''
        (map (Binding.pos_of o #1) vars ~~        
          map (Variable.markup_entity_def ctxt'' ##> Properties.remove Markup.kindN) xs);
  in ((vars, xs), ctxt'') end;

fun print_doc_class_tree ctxt P T = 
    let val classes = Name_Space.dest_table (get_onto_classes ctxt)
        fun is_class_son X (_, onto_class) =
          let val Onto_Class inherits_from = onto_class
          in (inherits_from |> #inherits_from) = X end
        fun tree _ [] = ""
           |tree lev ((n,_)::S) = (if P(lev,n) 
                                  then "."^Int.toString lev^" "^(T n)^"{...}.\n"
                                       ^ (tree(lev + 1)(filter(is_class_son(SOME([],n))) classes))
                                  else "."^Int.toString lev^" ... \n") 
                                  ^ (tree lev S)
        val roots = filter(is_class_son NONE) classes
    in  ".0 .\n" ^ tree 1 roots end

val (object_value_debug, object_value_debug_setup)
     = Attrib.config_bool \<^binding>\<open>object_value_debug\<close> (K false);

val (strict_monitor_checking, strict_monitor_checking_setup)
     = Attrib.config_bool \<^binding>\<open>strict_monitor_checking\<close> (K false);

val (free_class_in_monitor_checking, free_class_in_monitor_checking_setup)
     = Attrib.config_bool \<^binding>\<open>free_class_in_monitor_checking\<close> (K false);

val (free_class_in_monitor_strict_checking, free_class_in_monitor_strict_checking_setup)
     = Attrib.config_bool \<^binding>\<open>free_class_in_monitor_strict_checking\<close> (K false);

val (invariants_checking, invariants_checking_setup) 
     = Attrib.config_bool \<^binding>\<open>invariants_checking\<close> (K true);

val (invariants_strict_checking, invariants_strict_checking_setup) 
     = Attrib.config_bool \<^binding>\<open>invariants_strict_checking\<close> (K false);

val (invariants_checking_with_tactics, invariants_checking_with_tactics_setup) 
     = Attrib.config_bool \<^binding>\<open>invariants_checking_with_tactics\<close> (K false);


end (* struct *)

\<close>

setup\<open>DOF_core.object_value_debug_setup
      #> DOF_core.strict_monitor_checking_setup
      #> DOF_core.free_class_in_monitor_checking_setup
      #> DOF_core.free_class_in_monitor_strict_checking_setup
      #> DOF_core.invariants_checking_setup
      #> DOF_core.invariants_strict_checking_setup
      #> DOF_core.invariants_checking_with_tactics_setup\<close>

section\<open> Syntax for Term Annotation Antiquotations (TA)\<close>

text\<open>Isabelle/DOF allows for annotations at the term level, for which an
antiquotation syntax and semantics is defined at the inner syntax level.
(For this reasons, the mechanism has been called somewhat misleading
\<^emph>\<open>inner syntax antiquotations\<close> in earlier versions of Isabelle/DOF.)

For the moment, only a fixed number of builtin TA's is supported, future
versions might extend this feature substantially.\<close>

subsection\<open> Syntax \<close> 

datatype "doc_class" = mk string

ML\<open>
val doc_class_rexp_T = \<^typ>\<open>doc_class rexp\<close>
val doc_class_rexp_Ts = "doc_class rexp"
fun doc_class_rexp_t cid = \<^Const>\<open>Atom \<^typ>\<open>doc_class\<close>\<close> $ (\<^Const>\<open>mk\<close> $ HOLogic.mk_string cid)

val trace_attr_Ts = "(" ^ doc_class_rexp_Ts ^ " \<times> string) list"
val trace_attr_ts = ((\<^binding>\<open>trace\<close>, trace_attr_Ts , Mixfix.NoSyn), SOME "[]")
fun trace_attr_t cid oid =
  let val t = [\<^Const>\<open>Pair doc_class_rexp_T \<^typ>\<open>string\<close>\<close>
               $ doc_class_rexp_t cid
               $ HOLogic.mk_string oid]
              |> HOLogic.mk_list \<^Type>\<open>prod doc_class_rexp_T \<^typ>\<open>string\<close>\<close>
  in [(traceN, \<^here>, "+=", t)] end
\<close>

\<comment> \<open>and others in the future : file, http, thy, ...\<close> 

datatype "typ" = Isabelle_DOF_typ string (\<open>@{typ _}\<close>)
datatype "term" = Isabelle_DOF_term string (\<open>@{term _}\<close>)
datatype "thm" = Isabelle_DOF_thm string (\<open>@{thm _}\<close>)
datatype "file" = Isabelle_DOF_file string (\<open>@{file _}\<close>)
datatype "thy" = Isabelle_DOF_thy string (\<open>@{thy _}\<close>)
consts Isabelle_DOF_docitem      :: "string \<Rightarrow> 'a" (\<open>@{docitem _}\<close>)
datatype "docitem_attr" = Isabelle_DOF_docitem_attr string  string (\<open>@{docitemattr (_) :: (_)}\<close>)
consts Isabelle_DOF_trace_attribute :: "string \<Rightarrow> (string * string) list" (\<open>@{trace'_attribute _}\<close>)
consts Isabelle_DOF_instances_of :: "string \<Rightarrow> 'a list" (\<open>@{instances'_of _}\<close>)

\<comment> \<open>Dynamic setup of inner syntax cartouche\<close>

ML \<open>
(*  Author:     Frédéric Tuong, Université Paris-Saclay *)
(*  Title:      HOL/ex/Cartouche_Examples.thy
    Author:     Makarius
*)
  local
    fun mk_char (f_char, f_cons, _) (s, _) accu =
        fold
          (fn c => fn (accu, l) =>
            (f_char c accu, f_cons c l))
          (rev (map Char.ord (String.explode s)))
          accu;

    fun mk_string (_, _, f_nil) accu [] = (accu, f_nil)
      | mk_string f accu (s :: ss) = mk_char f s (mk_string f accu ss);
  in
    fun string_tr f f_mk accu content args =
      let fun err () = raise TERM ("string_tr", args) in
        (case args of
          [(c as Const (@{syntax_const "_constrain"}, _)) $ Free (s, _) $ p] =>
            (case Term_Position.decode_position1 p of
              SOME pos => c $ f (mk_string f_mk accu (content (s, pos))) $ p
            | NONE => err ())
        | _ => err ())
      end;
  end;
\<close>

syntax "_cartouche_string" :: "cartouche_position \<Rightarrow> _"  (\<open>_\<close>)

ML\<open>
structure Cartouche_Grammar = struct
  fun list_comb_mk cst n c = list_comb (Syntax.const cst, String_Syntax.mk_bits_syntax n c)
  val nil1 = Syntax.const @{const_syntax String.empty_literal}
  fun cons1 c l = list_comb_mk @{const_syntax String.Literal} 7 c $ l

  val default =
    [ ( "char list"
      , ( Const (@{const_syntax Nil}, @{typ "char list"})
        , fn c => fn l => Syntax.const @{const_syntax Cons} $ list_comb_mk @{const_syntax Char} 8 c $ l
        , snd))
    , ( "String.literal", (nil1, cons1, snd))]
end
\<close>

ML\<open>
fun parse_translation_cartouche binding l f_integer accu =
  let val cartouche_type = Attrib.setup_config_string binding (K (fst (hd l)))
      (* if there is no type specified, by default we set the first element
         to be the default type of cartouches *) in
  fn ctxt =>
    let val cart_type = Config.get ctxt cartouche_type in
    case List.find (fn (s, _) => s = cart_type) l of
      NONE => error ("Unregistered return type for the cartouche: \"" ^ cart_type ^ "\"")
    | SOME (_, (nil0, cons, f)) =>
        string_tr f (f_integer, cons, nil0) accu (Symbol_Pos.cartouche_content o Symbol_Pos.explode)
    end
  end
\<close>

parse_translation \<open>
  [( @{syntax_const "_cartouche_string"}
   , parse_translation_cartouche \<^binding>\<open>cartouche_type\<close> Cartouche_Grammar.default (K I) ())]
\<close>

(* tests *)  
term "@{typ  ''int => int''}"  
term "@{term ''Bound 0''}"  
term "@{thm  ''refl''}"  
term "@{docitem  ''<doc_ref>''}"
ML\<open>   @{term "@{docitem  ''<doc_ref>''}"}\<close>

term "@{typ  \<open>int \<Rightarrow> int\<close>}"  
term "@{term \<open>\<forall>x. P x \<longrightarrow> Q\<close>}"  
term "@{thm  \<open>refl\<close>}"  
term "@{docitem  \<open>doc_ref\<close>}"
ML\<open>   @{term "@{docitem  \<open>doc_ref\<close>}"}\<close>
(**)
declare [[cartouche_type = "String.literal"]]
term "\<open>Université\<close> :: String.literal"
declare [[cartouche_type = "char list"]]
term "\<open>Université\<close> :: char list"



subsection\<open> Semantics \<close>

ML\<open>
structure ISA_core = 
struct

fun err msg pos = error (msg ^ Position.here pos);
fun warn msg pos = warning (msg ^ Position.here pos);

fun ML_isa_check_generic check thy (term, pos) =
  let val name = (HOLogic.dest_string term
                  handle TERM(_,[t]) => error ("wrong term format: must be string constant: " 
                                               ^ Syntax.string_of_term_global thy t ))
      val _ = check thy (name,pos)
  in  SOME term end;  

fun check_identity _ (term, _, _) _ = SOME term

fun ML_isa_check_typ thy (term, _, pos) _ =
  let fun check thy (name, _) = let val ctxt = (Proof_Context.init_global thy)
                                in (Syntax.check_typ ctxt o Syntax.parse_typ ctxt) name end
  in  ML_isa_check_generic check thy (term, pos) end


fun ML_isa_check_term thy (term, _, pos) _ =
  let fun check thy (name, _) = let val ctxt = (Proof_Context.init_global thy)
                                in (Syntax.check_term ctxt o Syntax.parse_term ctxt) name end 
  in  ML_isa_check_generic check thy (term, pos) end


fun ML_isa_check_thm thy (term, _, pos) _ =    
  let fun check thy (name, _) = Global_Theory.check_fact thy (name, Position.none)
  in   ML_isa_check_generic check thy (term, pos) end


fun ML_isa_check_file thy (term, _, pos) _ =
  let fun check thy (name, _) = name |> Syntax.read_input
                                     |> Resources.check_file (Proof_Context.init_global thy) NONE 
  in  ML_isa_check_generic check thy (term, pos) end;

fun check_instance thy (term, _, pos) s =
  let
    val bname = Long_Name.base_name s;
    val qual = Long_Name.qualifier s;
    val class_name = (case try (unprefix DOF_core.doc_class_prefix) bname of
                        NONE => unprefix DOF_core.long_doc_class_prefix bname
                      | SOME name => name)
                     |> Long_Name.qualify qual
    fun check thy (name, _)  =
      let
        val name' = DOF_core.cid_of name thy
                   |> DOF_core.get_onto_class_cid thy |> (fst o fst)
        fun check' (class_name, object_cid) =
          if class_name = object_cid
          then ()
          else err (name ^ " is not an instance of " ^ class_name) pos
      in check' (class_name, name') end;
  in ML_isa_check_generic check thy (term, pos) end

fun check_instance_of thy (term, _, pos) _ =
  let
    fun check thy (name, _)  =
      if equal name DOF_core.default_cid
      then ()
      else
        let
          val class_typ = name |> DOF_core.get_onto_class_cid thy |> snd
          fun check' (class_name, typ) =
            if equal (class_name |> Syntax.read_typ_global thy) typ
            then ()
            else err (name ^ " is not a class name") pos
        in check' (name, class_typ) end;
  in ML_isa_check_generic check thy (term, pos) end

fun ML_isa_id _ (term,_) = SOME term


fun ML_isa_check_docitem thy (term, _, pos) _ =
  let fun check thy (name, _) = DOF_core.get_instance_global name thy
  in  ML_isa_check_generic check thy (term, pos) end

fun ML_isa_check_trace_attribute thy (term, _, _) _ =
  let
    val oid = (HOLogic.dest_string term
                  handle TERM(_,[t]) => error ("wrong term format: must be string constant: " 
                                               ^ Syntax.string_of_term_global thy t ))
    val _ = DOF_core.get_instance_global oid thy
  in SOME term end

fun ML_isa_elaborate_generic (_:theory) isa_name ty term_option _ =
  case term_option of
      NONE => error("Wrong term option. You must use a defined term")
    | SOME term => Const (isa_name, ty) $ term

(* Convert some excluded mixfix symbols that can appear in an inner syntax name. *)
val clean_mixfix = translate_string
  (fn "_" => "'_"
    | "'" => "''"
    | c => c);

fun rm_mixfix name mixfix thy =
  let
    val old_constants =
      Consts.dest (Sign.consts_of thy) |> #constants
      |> map fst
      |> filter (Long_Name.base_name #> equal name)
      |> map (pair mixfix)
      |> map swap
      |> map (apfst (Syntax.read_term_global thy))
      |> map (apsnd Mixfix.mixfix)
  in thy |> (Local_Theory.notation false Syntax.mode_default old_constants
             |> Named_Target.theory_map)
  end

fun elaborate_instance thy _ _ term_option _ =
  case term_option of
      NONE => error ("Malformed term annotation")
    | SOME term => let val instance_name = HOLogic.dest_string term
                   in DOF_core.value_of instance_name thy
                   end

(*
  The function declare_ISA_class_accessor_and_check_instance uses a prefix
  because the class name is already bound to "doc_class Regular_Exp.rexp" constant
  by add_doc_class_cmd function
*)
fun declare_ISA_class_accessor_and_check_instance (params, doc_class_name, bind_pos) thy =
  let
    val bname = Long_Name.base_name doc_class_name
    val bname' = prefix DOF_core.doc_class_prefix bname
    val bind = bname' |> pair bind_pos |> swap |> Binding.make
    val bind' = prefix DOF_core.long_doc_class_prefix bname
                |> pair bind_pos |> swap |> Binding.make
    val typ = Type (doc_class_name, map TFree params)
    val const_typ = \<^typ>\<open>string\<close> --> typ
    fun mixfix_enclose name = name |> enclose "@{"  " _}"
    val mixfix = clean_mixfix bname |> mixfix_enclose
    val mixfix' = clean_mixfix doc_class_name |> mixfix_enclose
  in
    thy |> rm_mixfix bname' mixfix
        |> Sign.add_consts [(bind, const_typ, Mixfix.mixfix mixfix)]
        |> DOF_core.add_isa_transformer bind ((check_instance, elaborate_instance)
                                               |> DOF_core.make_isa_transformer)
        |> Sign.add_consts [(bind', const_typ, Mixfix.mixfix mixfix')]
        |> DOF_core.add_isa_transformer bind' ((check_instance, elaborate_instance)
                                                |> DOF_core.make_isa_transformer)

  end

fun elaborate_instances_of thy _ _ term_option _ =
  let
    val class_name = case term_option of
                        NONE => error ("Malformed term annotation")
                      | SOME term => HOLogic.dest_string term
    fun mk_list class_typ f =
      let
          val values = thy |> Proof_Context.init_global |> DOF_core.get_instances
                       |> Name_Space.dest_table
                       |> map fst
                       |> f
                       |> map (fn oid => DOF_core.value_of oid thy)
        in HOLogic.mk_list class_typ values end
  in if equal class_name DOF_core.default_cid
     then
       (* When the class name is default_cid = "text",
          return the instances attached to this default class.
          We want the class default_cid to stay abstract
          and not have the capability to be defined with attribute, invariants, etc.
          Hence this can handle docitem without a class associated,
          for example when you just want a document element to be referentiable
          without using the burden of ontology classes.
          ex: text*[sdf]\<open> Lorem ipsum @{thm refl}\<close> *)
       (filter (fn name => DOF_core.cid_of name thy |> equal DOF_core.default_cid))
       |> mk_list DOF_core.default_cid_typ
     else
       let
         val class_typ = class_name |> Syntax.read_typ_global thy
       in
         (filter_out (fn name => DOF_core.cid_of name thy |> equal DOF_core.default_cid)
          #> filter (fn name => DOF_core.cid_of name thy
                                |> Syntax.read_typ_global thy
                                |> equal class_typ))
         |> mk_list class_typ
       end
  end

fun symbex_attr_access0 ctxt proj_term term =
let
      val [subterm'] = Type_Infer_Context.infer_types ctxt [proj_term $ term]
in Value_Command.value ctxt (subterm') end

fun compute_attr_access ctxt attr oid pos_option pos' = (* template *)
  let
    val value =  DOF_core.value_of oid (Context.theory_of ctxt)
    val ctxt' =  Context.proof_of ctxt
    val thy = Context.theory_of ctxt
    val DOF_core.Instance {cid,...} =
                                    DOF_core.get_instance_global oid thy
    val instances = DOF_core.get_instances ctxt'
    val markup = DOF_core.get_instance_name_global oid thy
                 |> Name_Space.markup (Name_Space.space_of_table instances)
    val _ = Context_Position.report ctxt' pos' markup;
    val {long_name, typ=ty, ...} = 
      case DOF_core.get_attribute_info_local cid attr ctxt' of
          SOME f => f
        | NONE =>  error("attribute undefined for reference: "
                         ^ oid
                         ^ Position.here
                         (the pos_option handle Option.Option =>
                         error("Attribute "
                               ^ attr
                               ^ " undefined for reference: "
                               ^ oid ^ Position.here pos')))
    val proj_term = Const(long_name,dummyT --> ty)
    val _ = case pos_option of
                NONE => ()
              | SOME pos =>
                  let 
                    val class_name = Long_Name.qualifier long_name
                    val onto_classes = DOF_core.get_onto_classes ctxt'
                    val markup = DOF_core.get_onto_class_name_global class_name thy
                                 |> Name_Space.markup (Name_Space.space_of_table onto_classes)
                  in Context_Position.report ctxt' pos markup end
  in  symbex_attr_access0 ctxt' proj_term value end

fun ML_isa_elaborate_trace_attribute (thy:theory) _ _ term_option pos =
case term_option of
    NONE => err ("Malformed term annotation") pos
  | SOME term => 
      let
        val oid = HOLogic.dest_string term
        val traces = compute_attr_access (Context.Theory thy) traceN oid NONE pos
        fun conv (\<^Const>\<open>Pair \<^typ>\<open>doc_class rexp\<close> \<^typ>\<open>string\<close>\<close>
                    $ (\<^Const>\<open>Atom \<^typ>\<open>doc_class\<close>\<close> $ (\<^Const>\<open>mk\<close> $ s)) $ S) =
          let val s' =  DOF_core.get_onto_class_name_global (HOLogic.dest_string s) thy 
          in \<^Const>\<open>Pair \<^typ>\<open>string\<close> \<^typ>\<open>string\<close>\<close> $ HOLogic.mk_string s' $ S end
        val traces' = map conv (HOLogic.dest_list traces)
      in HOLogic.mk_list \<^Type>\<open>prod \<^typ>\<open>string\<close> \<^typ>\<open>string\<close>\<close> traces' end

end; (* struct *)
                                                            
\<close>


subsection\<open> Isar - Setup\<close>
(* Isa_transformers declaration for Isabelle_DOF term anti-quotations (typ, term, thm, etc.).
   They must be declared in the same theory file as the one of the declaration
   of Isabelle_DOF term anti-quotations !!! *)
setup\<open>
[(\<^type_name>\<open>typ\<close>, ISA_core.ML_isa_check_typ, ISA_core.ML_isa_elaborate_generic)
  , (\<^type_name>\<open>term\<close>, ISA_core.ML_isa_check_term, ISA_core.ML_isa_elaborate_generic)
  , (\<^type_name>\<open>thm\<close>, ISA_core.ML_isa_check_thm, ISA_core.ML_isa_elaborate_generic)
  , (\<^type_name>\<open>file\<close>, ISA_core.ML_isa_check_file, ISA_core.ML_isa_elaborate_generic)]
|> fold (fn (n, check, elaborate) => fn thy =>
let val ns = Sign.tsig_of thy |> Type.type_space
    val name = n
    val {pos, ...} = Name_Space.the_entry ns name
    val bname = Long_Name.base_name name
    val binding = Binding.make (bname, pos)
                   |> Binding.prefix_name DOF_core.ISA_prefix
                   |> Binding.prefix false bname
in  DOF_core.add_isa_transformer binding ((check, elaborate) |> DOF_core.make_isa_transformer) thy
end)
#>
([(\<^const_name>\<open>Isabelle_DOF_docitem\<close>,
    ISA_core.ML_isa_check_docitem, ISA_core.ML_isa_elaborate_generic)
  , (\<^const_name>\<open>Isabelle_DOF_trace_attribute\<close>,
      ISA_core.ML_isa_check_trace_attribute, ISA_core.ML_isa_elaborate_trace_attribute)
  , (\<^const_name>\<open>Isabelle_DOF_instances_of\<close>,
      ISA_core.check_instance_of, ISA_core.elaborate_instances_of)]
|> fold (fn (n, check, elaborate) => fn thy =>
let val ns = Sign.consts_of thy |> Consts.space_of
    val name = n
    val {pos, ...} = Name_Space.the_entry ns name
    val bname =  Long_Name.base_name name
    val binding = Binding.make (bname, pos)
in  DOF_core.add_isa_transformer binding ((check, elaborate) |> DOF_core.make_isa_transformer) thy
end))
\<close>

section\<open> Syntax for Annotated Documentation Commands (the '' View'' Part I) \<close>

ML\<open>
structure ODL_Meta_Args_Parser = 
struct

type meta_args_t = (binding * (string * Position.T) option)
                   * ((string * Position.T) * string) list

val empty_meta_args = ((Binding.empty, NONE), [])

val is_improper = not o (Token.is_proper orf Token.is_begin_ignore orf Token.is_end_ignore);
val improper = Scan.many is_improper; (* parses white-space and comments *)

val attribute =
    Parse.position Parse.const
    --| improper 
    -- Scan.optional (Parse.$$$ "=" --| improper |-- Parse.!!! Parse.term --| improper) "True"
   : ((string * Position.T) * string) parser;

val attribute_upd  : (((string * Position.T) * string) * string) parser =
    Parse.position Parse.const 
    --| improper
    -- ((@{keyword "+="} --| improper) || (@{keyword ":="} --| improper))
    -- Parse.!!! Parse.term
    --| improper
    : (((string * Position.T) * string) * string) parser;

val reference =
    Parse.binding
    --| improper
    -- Scan.option (Parse.$$$ "::" 
                    -- improper 
                    |-- (Parse.!!! (Parse.position Parse.name))
                    ) 
    --| improper;

val attributes =  
    ((Parse.$$$ "["
      -- improper 
     |-- (reference -- 
         (Scan.optional(Parse.$$$ "," -- improper |-- (Parse.enum "," (improper |-- attribute)))) []))
     --| Parse.$$$ "]"
     --| improper)  : meta_args_t parser

val opt_attributes = Scan.optional attributes empty_meta_args

val attributes_upd =  
    ((Parse.$$$ "[" 
     -- improper 
     |-- (reference -- 
         (Scan.optional(Parse.$$$ "," -- improper |-- (Parse.enum "," (improper |-- attribute_upd)))) []))
     --| Parse.$$$ "]")
     --| improper

end (* structure ODL_Meta_Args_Parser *)
\<close>

ML\<open>
(* c.f. \<^file>\<open>~~/src/HOL/Tools/value_command.ML\<close> *)
(*
  The value* command uses the same code as the value command
  and adds the evaluation Term Annotation Antiquotations (TA)
  with the help of the DOF_core.transduce_term_global function.
*)
(*  Based on:
    Title:      HOL/Tools/value_command.ML
    Author:     Florian Haftmann, TU Muenchen

Generic value command for arbitrary evaluators, with default using nbe or SML.
*)

(*signature VALUE_COMMAND =
sig
  val value: Proof.context -> term -> term
  val value_without_elaboration: Proof.context -> term -> term
  val value_select: string -> Proof.context -> term -> term
  val value_cmd:  {assert: bool} -> ODL_Command_Parser.meta_args_t option ->
                  string ->  string list ->  string -> Position.T
                  -> theory -> theory
   val add_evaluator: binding * (Proof.context -> term -> term) 
                  -> theory -> string * theory
end;*)


structure Value_Command (*: VALUE_COMMAND*) =
struct

structure Evaluators = Theory_Data
(
  type T = (Proof.context -> term -> term) Name_Space.table;
  val empty = Name_Space.empty_table "evaluator";
  val merge = Name_Space.merge_tables;
)

fun add_evaluator (b, evaluator) thy =
  let
    val (name, tab') = Name_Space.define (Context.Theory thy) true
      (b, evaluator) (Evaluators.get thy);
    val thy' = Evaluators.put tab' thy;
  in (name, thy') end;

fun intern_evaluator thy raw_name =
  if raw_name = "" then ""
  else Name_Space.intern (Name_Space.space_of_table
    (Evaluators.get (thy))) raw_name;

fun default_value ctxt t =
  if null (Term.add_frees t [])
  then Code_Evaluation.dynamic_value_strict ctxt t
  else Nbe.dynamic_value ctxt t;

fun value_select name ctxt =
  if name = ""
  then default_value ctxt
  else Name_Space.get (Evaluators.get (Proof_Context.theory_of ctxt)) name ctxt;

fun value_select' raw_name ctxt raw_t =
  let val thy = Proof_Context.theory_of ctxt
      val t = Syntax.parse_term ctxt raw_t;
      val t' = DOF_core.elaborate_term' ctxt t
      val t'' = Syntax.check_term ctxt t'
  in
    if raw_name = ""
    then t'' |> default_value ctxt
    else let val name = intern_evaluator thy raw_name
         in t'' |> Name_Space.get (Evaluators.get thy) name ctxt
         end
    end

val value = value_select ""

val value_without_elaboration = value_select ""

structure Docitem_Parser = 
struct

fun create_default_object thy binding class_name typ = 
  let
    val purified_class_name = String.translate (fn #"." => "_" | x => String.implode [x]) class_name
    fun attr_to_s (binding, _, _) = purified_class_name ^ "_"
                                      ^ (Binding.name_of binding)
                                      ^ "_Attribute_Not_Initialized"
    val class_list = DOF_core.get_attributes class_name thy
    fun attrs_filter [] = [] 
      | attrs_filter (x::xs) =
          let val (cid, ys) = x
              fun is_duplicated _ [] = false
                | is_duplicated y (x::xs) =
                    let val (_, ys) = x
                    in if ys |> exists (fn x => (x,y) |> apply2 (#1 #> Binding.name_of)
                                                      |> uncurry equal)
                       then true
                       else is_duplicated y xs end
          in (cid, filter_out (fn y => is_duplicated y xs) ys)::attrs_filter xs end
    val class_list' = rev (attrs_filter (rev class_list))
    val tag_attr_s = serial () |> string_of_int
    fun trans_attr thy trans tag_attr  (cid, filtered_attr_list) =
      if DOF_core.virtual_of cid thy |> #virtual
      then (tag_attr)::(map (trans) filtered_attr_list)
      else (map (trans) filtered_attr_list)
    val test_class = class_list' |> map (trans_attr thy (attr_to_s) tag_attr_s)
                                 |> flat
                                 |> cons tag_attr_s
    val term = test_class |> cons (Long_Name.qualify class_name makeN) |> space_implode Symbol.space
    val ctxt = Proof_Context.init_global thy
    val term' = term |> Syntax.parse_term ctxt |> DOF_core.elaborate_term' ctxt
    val parsed_prop = Const (\<^const_name>\<open>Pure.eq\<close>, dummyT) $ Free (Binding.name_of binding, dummyT) $ term'
    val raw_vars = [(binding, SOME typ, NoSyn)]
    val (_, vars_ctxt) = DOF_core.prep_decls Proof_Context.cert_var raw_vars ctxt
    val concl = Syntax.check_prop vars_ctxt parsed_prop
  in Logic.dest_equals concl |> snd end


fun check_classref {is_monitor=is_monitor} (SOME (cid, pos)) thy =                        
  let
    val ctxt = Proof_Context.init_global thy
    val name_cid_typ = DOF_core.get_onto_class_cid thy cid
    val cid_long = name_cid_typ |> (fst o fst)
    val rex = DOF_core.rex_of cid_long thy
    val _ = if is_monitor andalso (null rex orelse cid_long= DOF_core.default_cid ) 
            then error("should be monitor class!")
            else ()
    val onto_classes = DOF_core.get_onto_classes ctxt
    val markup = DOF_core.get_onto_class_name_global cid_long thy
                 |> Name_Space.markup (Name_Space.space_of_table onto_classes)
    val _ = Context_Position.report ctxt pos markup;
  in  (name_cid_typ, pos)
  end
  | check_classref _ NONE _ = pair DOF_core.default_cid DOF_core.default_cid
                              |> rpair DOF_core.default_cid_typ
                              |> rpair Position.none

fun calc_update_term {mk_elaboration=mk_elaboration} thy (name, typ)
                     (S:(string * Position.T * string * term)list) term = 
    let val cid_long = name
        val cid_ty = typ
        val ctxt = Proof_Context.init_global thy
        fun read_assn (lhs, pos:Position.T, opr, rhs) term =
            let 
                fun get_class_name parent_cid attribute_name pos =
                  let
                    val DOF_core.Onto_Class {attribute_decl, inherits_from, ...} = 
                                                      DOF_core.get_onto_class_global parent_cid thy
                  in
                    if exists (fn (binding, _, _) => Binding.name_of binding = attribute_name)
                              attribute_decl
                    then parent_cid
                    else
                      case inherits_from of
                          NONE =>
                                ISA_core.err ("Attribute " ^ attribute_name
                                              ^ " not defined for class: " ^ cid_long) pos
                        | SOME (_, parent_name) => get_class_name parent_name attribute_name pos
                  end
                val _ = if mk_elaboration
                        then
                          let val attr_defined_cid = get_class_name cid_long lhs pos
                              val onto_classes = DOF_core.get_onto_classes ctxt
                              val markup = DOF_core.get_onto_class_name_global attr_defined_cid thy
                                           |> Name_Space.markup (Name_Space.space_of_table onto_classes)
                          in Context_Position.report ctxt pos markup end
                        else ()
                val info_opt = DOF_core.get_attribute_info cid_long (Long_Name.base_name lhs) thy
                val (ln,lnt,lnu,_) = case info_opt of 
                                           NONE => error ("unknown attribute >" 
                                                          ^((Long_Name.base_name lhs))
                                                          ^"< in class: "^cid_long)
                                        |  SOME{long_name, typ, ...} => (long_name, typ, 
                                                                         long_name ^ Record.updateN,
                                                                         (typ --> typ) 
                                                                          --> cid_ty --> cid_ty)
                val _ = if Long_Name.base_name lhs = lhs orelse ln = lhs then ()
                        else error("illegal notation for attribute of "^cid_long)
                fun join (ttt as \<^Type>\<open>int\<close>) = \<^Const>\<open>Groups.plus ttt\<close>
                   |join (ttt as \<^Type>\<open>set _\<close>) = \<^Const>\<open>Lattices.sup dummyT\<close>
                   |join \<^Type>\<open>list A\<close> = \<^Const>\<open>List.append dummyT\<close>
                   |join _ = error("implicit fusion operation not defined for attribute: "^ lhs)
                 (* could be extended to bool, map, multisets, ... *)
             in case opr of 
                  "=" => Const(lnu, dummyT) $ Abs ("uu_", dummyT, rhs) $ term
                | ":=" => Const(lnu, dummyT) $ Abs ("uu_", dummyT, rhs) $ term
                | "+=" => Const(lnu, dummyT) $ Abs ("uu_u", dummyT, join lnt $ (Bound 0) $ rhs) $ term
                | _ => error "corrupted syntax - oops - this should not occur" 
             end
             val t = fold read_assn S term
             val t' = if mk_elaboration
                      then DOF_core.elaborate_term' ctxt t
                      else DOF_core.check_term' ctxt t
    in if t = term
       then Sign.certify_term thy t'
       else
          let
             val concl = Syntax.check_term ctxt t';
          in Sign.certify_term thy concl end
    end

fun msg thy txt pos = if Config.get_global thy DOF_core.strict_monitor_checking
                  then ISA_core.err txt pos
                  else ISA_core.warn txt pos

fun msg_intro get n oid cid = ("accepts clause " ^ Int.toString n 
                               ^ " of monitor " ^ oid
                               ^ get (" not enabled for", " rejected")
                               ^ " doc_class: " ^ cid)

fun register_oid_cid_in_open_monitors binding (name, pos') thy = 
  let 
      val oid = Binding.name_of binding
      val cid_long= name
      fun is_enabled (n, monitor_info) = 
                     if exists (DOF_core.is_subclass_global thy cid_long) 
                                (DOF_core.alphabet_of n thy)
                     then SOME (n, monitor_info)
                     else if Config.get_global thy DOF_core.free_class_in_monitor_strict_checking
                             orelse  Config.get_global thy DOF_core.free_class_in_monitor_checking
                          then SOME (n, monitor_info)
                          else NONE
      (* filtering those monitors with automata, whose alphabet contains the
         cid of this oid. The enabled ones were selected and moved to their successor state
         along the super-class id. The evaluation is in parallel, simulating a product
         semantics without expanding the subclass relationship. *)
      fun is_enabled_for_cid (moid , monitor_info) =
        let val DOF_core.Monitor_Info {accepted_cids, automatas, rejected_cids, ...} = monitor_info
            val indexS= 1 upto (length automatas)
            val indexed_autoS = automatas ~~ indexS
            fun check_for_cid (A,n) = 
              let fun direct_super_class _ cid [] = cid
                    | direct_super_class thy cid (x::xs) =
                        if DOF_core.is_subclass_global thy cid x
                        then direct_super_class thy cid xs
                        else direct_super_class thy x xs
                  val accS = (RegExpInterface.enabled A accepted_cids)
                  val accS' = filter (DOF_core.is_subclass_global thy cid_long) accS
                  fun first_super_class cids =
                      case List.getItem cids
                        of  SOME (hd,tl) => SOME (direct_super_class thy hd tl)
                          | NONE => NONE
                  val first_accepted = first_super_class accS'
                  val rejectS = filter (DOF_core.is_subclass_global thy cid_long) rejected_cids
                  val first_rejected = first_super_class rejectS
              in
                case first_accepted of
                    NONE => (case first_rejected of
                                 NONE =>
                                   if Config.get_global thy DOF_core.free_class_in_monitor_strict_checking
                                   then ISA_core.err (msg_intro fst n moid cid_long) pos'
                                   else if Config.get_global thy DOF_core.free_class_in_monitor_checking
                                        then (ISA_core.warn (msg_intro fst n moid cid_long) pos';A)
                                        else A
                               | SOME _ => (msg thy (msg_intro snd n moid cid_long) pos';A))
                  | SOME accepted => (case first_rejected of
                                          NONE => RegExpInterface.next A accepted_cids (accepted)
                                        | SOME rejected =>
                                            if DOF_core.is_subclass_global thy accepted rejected
                                            then RegExpInterface.next A accepted_cids (accepted)
                                            else (msg thy (msg_intro snd n moid cid_long) pos';A))
              end
         in (moid,map check_for_cid indexed_autoS, monitor_info)  end  
      val enabled_monitors = List.mapPartial is_enabled
                      (Name_Space.dest_table (DOF_core.get_monitor_infos (Proof_Context.init_global thy)))
      val defined = DOF_core.defined_of oid thy
      val trace_attr = if defined
                       then trace_attr_t cid_long oid 
                       else []
      fun mon_cid oid = DOF_core.cid_of oid thy |> DOF_core.get_onto_class_cid thy
                                                |> (fn ((name, _), typ) => (name, typ))
      val ctxt = Proof_Context.init_global thy
      fun def_trans_value oid =
        (#1 o (calc_update_term {mk_elaboration=true} thy (mon_cid oid) trace_attr))
        #> value ctxt
      val _ = if null enabled_monitors
              then ()
              else if defined
                   then (tracing "registrating in monitors ..." ;
                         app (fn (n, _) => tracing (oid^" : "^cid_long^" ==> "^n)) enabled_monitors)
                   else ()
      (* check that any transition is possible: *)
      fun class_inv_checks thy =
        enabled_monitors
        |> map (fn (x, _) =>
                  let val cid_long =
                            let val DOF_core.Instance cid = DOF_core.get_instance_global x thy
                            in cid |> #cid end
                  in DOF_core.check_ml_invs cid_long x {is_monitor=true} thy end)
      val delta_autoS = map is_enabled_for_cid  enabled_monitors;
      fun update_info (n, aS, monitor_info) =  
        let val DOF_core.Monitor_Info {accepted_cids,rejected_cids,...} = monitor_info
        in Name_Space.map_table_entry n (K ((accepted_cids, rejected_cids, aS)
                                            |> DOF_core.make_monitor_info))
        end
      fun update_trace mon_oid =
        if Config.get_global thy DOF_core.object_value_debug
        then let fun def_trans_input_term  oid =
                   #1 o (calc_update_term {mk_elaboration=false} thy (mon_cid oid) trace_attr)
              in DOF_core.map_input_term_value mon_oid
                                   (def_trans_input_term mon_oid) (def_trans_value mon_oid) end
        else DOF_core.map_value mon_oid (def_trans_value mon_oid)
  in  thy |> (* update traces of all enabled monitors *)
             fold update_trace (map #1 enabled_monitors)
          |> (* check class invariants of enabled monitors *)
             tap class_inv_checks
          |> (* update the automata of enabled monitors *)
              DOF_core.Monitor_Info.map (fold update_info delta_autoS)
  end

fun check_invariants thy binding =
  let
    val oid = Binding.name_of binding
    val docitem_value = DOF_core.value_of oid thy
    val name = DOF_core.cid_of oid thy
               |> DOF_core.get_onto_class_cid thy |> (fst o fst)
    fun get_all_invariants cid thy =
      case DOF_core.get_onto_class_global cid thy of
          DOF_core.Onto_Class {inherits_from=NONE, invs, ...} => single (cid, invs)
        | DOF_core.Onto_Class {inherits_from=SOME(_, father), invs, ...} =>
            (cid, invs) :: get_all_invariants father thy
    val cids_invariants = get_all_invariants name thy
    val inv_and_apply_list = 
      let fun mk_inv_and_apply cid_invs value thy =
            let val ctxt = Proof_Context.init_global thy 
                val (cid_long, invs) = cid_invs
            in invs |> map
                    (fn (bind, _) =>
                      let
                        val inv_name = Binding.name_of bind
                                       |> Long_Name.qualify cid_long
                        val pos = Binding.pos_of bind
                        val inv_def = inv_name |> Syntax.parse_term ctxt
                        in ((inv_name, pos), Syntax.check_term ctxt (inv_def $ value)) end)
            end    
      in cids_invariants |> map (fn cid_invs => mk_inv_and_apply cid_invs docitem_value thy) 
                         |> flat
      end
    fun check_invariants' ((inv_name, pos), term) =
      let val ctxt = Proof_Context.init_global thy
          val trivial_true = \<^term>\<open>True\<close> |> HOLogic.mk_Trueprop |> Thm.cterm_of ctxt |> Thm.trivial
          val evaluated_term = value ctxt term
                handle  Match => error ("exception Match raised when checking "
                                       ^ inv_name ^ " invariant." ^ Position.here pos ^ "\n"
                                       ^ "You might want to check the definition of the invariant\n"
                                       ^ "against the value specified in the instance\n"
                                       ^ "or the default value declared in the instance class.")
                      | ERROR e =>
                  if (String.isSubstring "Wellsortedness error" e)
                      andalso (Config.get_global thy DOF_core.invariants_checking_with_tactics)
                  then (warning("Invariants checking uses proof tactics");
                         let val prop_term = HOLogic.mk_Trueprop term
                             val thms = Proof_Context.get_thms ctxt (inv_name ^ def_suffixN)
                             (* Get the make definition (def(1) of the record) *)
                             val thms' =
                                  (Proof_Context.get_thms ctxt (Long_Name.append name defsN)) @ thms
                             val _ = Goal.prove ctxt [] [] prop_term
                                                  (K ((unfold_tac ctxt thms') THEN (auto_tac ctxt)))
                                     |> Thm.close_derivation \<^here>
                                     handle ERROR e =>
                                       let
                                         val msg_intro = "Invariant "
                                                      ^ inv_name
                                                      ^ " failed to be checked using proof tactics"
                                                      ^ " with error:\n"
                                       in 
                                         if Config.get_global thy DOF_core.invariants_strict_checking
                                         then ISA_core.err (msg_intro ^ e) pos
                                         else (ISA_core.warn (msg_intro ^ e) pos; trivial_true) end
                         (* If Goal.prove does not fail, then the evaluation is considered True,
                            else an error is triggered by Goal.prove *)
                         in @{term True} end)
                  else \<^term>\<open>True \<Longrightarrow> True\<close>
      in case evaluated_term of
             \<^term>\<open>True\<close> => ((inv_name, pos), term)
           | \<^term>\<open>True \<Longrightarrow> True\<close> =>
                let val msg_intro = "Fail to check invariant "
                                    ^ inv_name
                                    ^ ".\nMaybe you can try "
                                    ^ "to activate invariants_checking_with_tactics\n"
                                    ^ "if your invariant is checked against doc_class algebraic "
                                    ^ "types like 'doc_class list' or 'doc_class set'"
                in if Config.get_global thy DOF_core.invariants_strict_checking
                   then ISA_core.err (msg_intro) pos
                   else (ISA_core.warn (msg_intro) pos; ((inv_name, pos), term)) end
           | _ => let val msg_intro = "Invariant " ^ inv_name ^ " violated"
                  in if Config.get_global thy DOF_core.invariants_strict_checking
                     then ISA_core.err msg_intro pos
                     else  (ISA_core.warn msg_intro pos; ((inv_name, pos), term)) end
      end
    val _ = map check_invariants' inv_and_apply_list
  in thy end


fun create_and_check_docitem is_monitor {is_inline=is_inline} {define=define} binding cid_pos doc_attrs thy =
  let
    val oid = Binding.name_of binding
    val (((name, args_cid), typ:typ), pos') = check_classref is_monitor cid_pos thy
    val cid_pos' = (name, pos')
    val cid_long = fst cid_pos'
    val default_cid = args_cid = DOF_core.default_cid
    val vcid = if default_cid
               then NONE
               else if DOF_core.virtual_of cid_long thy |> #virtual
                    then SOME args_cid
                    else NONE
    val value_terms = if default_cid
                      then let
                             val undefined_value = dest_Free DOF_core.undefined_value
                                                   |> apfst (fn x => oid ^ "_" ^ x)
                                                   |> Free
                           in (undefined_value, undefined_value) end
                            (* Handle initialization of docitem without a class associated,
                               for example when you just want a document element to be referentiable
                               without using the burden of ontology classes.
                               ex: text*[sdf]\<open> Lorem ipsum @{thm refl}\<close> *)
                     else let
                            fun conv_attrs ((lhs, pos), rhs) = (Protocol_Message.clean_output lhs,pos,"=", Syntax.parse_term (Proof_Context.init_global thy) rhs)
                            val assns' = map conv_attrs doc_attrs
                            val defaults_init = create_default_object thy binding cid_long typ
                            fun conv (na, _(*ty*), parsed_term) =(Binding.name_of na, Binding.pos_of na, "=", parsed_term);
                            val S = map conv (DOF_core.get_attribute_defaults cid_long thy);
                            val (defaults, _) = calc_update_term {mk_elaboration=false}
                                                                      thy (name, typ) S defaults_init;
                            val (value_term', _) = calc_update_term {mk_elaboration=true}
                                                                      thy (name, typ) assns' defaults
                          in if Config.get_global thy DOF_core.object_value_debug
                             then let
                                    val (input_term, _) = calc_update_term {mk_elaboration=false}
                                                                        thy (name, typ)  assns' defaults
                                  in (input_term, value_term') end
                             else (\<^term>\<open>()\<close>, value_term') end
  in thy |> DOF_core.define_object_global
              {define = define} (binding, DOF_core.make_instance
                                               (false, fst value_terms,
                                                (snd value_terms)
                                                |> value (Proof_Context.init_global thy),
                                                 is_inline, args_cid, vcid))
         |> register_oid_cid_in_open_monitors binding (name,  pos')
         |> (fn thy =>
            if (* declare_reference* without arguments is not checked against invariants *)
               thy |> DOF_core.defined_of oid |> not
               andalso null doc_attrs
            then thy
            else thy |> tap (DOF_core.check_opening_ml_invs cid_long oid is_monitor)
                     |> tap (DOF_core.check_ml_invs cid_long oid is_monitor)
                     (* Bypass checking of high-level invariants when the class default_cid = "text",
                        the top (default) document class.
                        We want the class default_cid to stay abstract
                        and not have the capability to be defined with attribute, invariants, etc.
                        Hence this bypass handles docitem without a class associated,
                        for example when you just want a document element to be referentiable
                        without using the burden of ontology classes.
                        ex: text*[sdf]\<open> Lorem ipsum @{thm refl}\<close> *)
                     |> (fn thy => if default_cid then thy
                                   else if Config.get_global thy DOF_core.invariants_checking
                                        then check_invariants thy binding else thy))
  end

end (* structure Docitem_Parser *)


fun meta_args_exec (meta_args as ((binding, cid_pos), doc_attrs) : ODL_Meta_Args_Parser.meta_args_t) thy =
         thy |> (if meta_args = ODL_Meta_Args_Parser.empty_meta_args
                 then (K thy)
                 else Docitem_Parser.create_and_check_docitem 
                                    {is_monitor = false} {is_inline = true} {define = true}
                                    binding (I cid_pos) (I doc_attrs))

fun value_cmd {assert=assert} meta_args_opt raw_name modes raw_t pos thy  =
  let
    val thy' = meta_args_exec meta_args_opt thy
    val name = intern_evaluator thy' raw_name;
    val t = Syntax.parse_term (Proof_Context.init_global thy') raw_t;
    val term' = DOF_core.parsed_elaborate (Proof_Context.init_global thy') pos t
    val term'' = Syntax.check_term (Proof_Context.init_global thy') term'
    val t' = value_select name (Proof_Context.init_global thy') term'';
    val ty' = Term.type_of t';
    val ty' = if assert
              then case ty' of
                       \<^typ>\<open>bool\<close> => ty'
                     | _ =>  error "Assertion expressions must be boolean."
              else ty'
    val t'  = if assert
              then case t'  of
                       \<^term>\<open>True\<close> => t'
                     | _ =>  error "Assertion failed."
              else t'
    val ctxt' = Proof_Context.augment t' (Proof_Context.init_global thy');
    val p = Print_Mode.with_modes modes (fn () =>
      Pretty.block [Pretty.quote (Syntax.pretty_term ctxt' t'), Pretty.fbrk,
        Pretty.str "::", Pretty.brk 1, Pretty.quote (Syntax.pretty_typ ctxt' ty')]) ();
    val _ = Pretty.writeln p 
  in  thy' end;

val opt_modes =
  Scan.optional (\<^keyword>\<open>(\<close> |-- Parse.!!! (Scan.repeat1 Parse.name --| \<^keyword>\<open>)\<close>)) [];

val opt_evaluator =
  Scan.optional (\<^keyword>\<open>[\<close> |-- Parse.name --| \<^keyword>\<open>]\<close>) "";

fun pass_trans_to_value_cmd (((name, meta_args_opt), modes), t) trans =
let val pos = Toplevel.pos_of trans
in
   trans |> Toplevel.theory (value_cmd {assert=false} meta_args_opt name modes t pos)
end

\<comment> \<open>c.f. \<^file>\<open>~~/src/Pure/Isar/isar_cmd.ML\<close>\<close>

(*
  term* command uses the same code as term command
  and adds the possibility to check Term Annotation Antiquotations (TA)
  with the help of DOF_core.transduce_term_global function
*)
fun string_of_term  s pos ctxt =
let
  val t = Syntax.read_term ctxt s;
  val T = Term.type_of t;
  val ctxt' = Proof_Context.augment t ctxt;
  val _ = DOF_core.transduce_term_global {mk_elaboration=false} (t , pos)
                                          (Proof_Context.theory_of ctxt');
in
  Pretty.string_of
    (Pretty.block [Pretty.quote (Syntax.pretty_term ctxt' t), Pretty.fbrk,
      Pretty.str "::", Pretty.brk 1, Pretty.quote (Syntax.pretty_typ ctxt' T)])
end;

fun print_item string_of (modes, arg) state =  
    Print_Mode.with_modes modes (fn () => writeln (string_of state arg)) (); 

fun prin t pos state _  = string_of_term t pos (Toplevel.context_of state)

fun print_term meta_args_opt (string_list, string) trans =
let
  val pos = Toplevel.pos_of trans
in meta_args_exec meta_args_opt
   #> tap (fn thy => print_item (prin string pos) (string_list, string) (Toplevel.make_state (SOME thy)))
   |> (fn thy => Toplevel.theory thy trans)
end

val (disable_assert_evaluation, disable_assert_evaluation_setup)
     = Attrib.config_bool \<^binding>\<open>disable_assert_evaluation\<close> (K false);

val _ = Theory.setup disable_assert_evaluation_setup

fun pass_trans_to_assert_value_cmd (((name, meta_args_opt), modes), t) trans =
let val pos = Toplevel.pos_of trans
in trans
   |> Toplevel.theory
        (fn thy =>
           if Config.get_global thy disable_assert_evaluation
           then (meta_args_exec meta_args_opt
                 #> tap (fn thy => print_item (prin t pos) (modes, t) (Toplevel.make_state (SOME thy))))
                thy
           else value_cmd {assert=true} meta_args_opt name modes t pos thy) 
end

(* setup ontology aware commands *)

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>term*\<close> "read and print term"
     (ODL_Meta_Args_Parser.opt_attributes -- (opt_modes -- Parse.term) 
     >> (uncurry print_term));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>value*\<close> "evaluate and print term"
    ((opt_evaluator -- ODL_Meta_Args_Parser.opt_attributes -- opt_modes -- Parse.term) 
     >> (pass_trans_to_value_cmd));
                                


val _ =
  Outer_Syntax.command \<^command_keyword>\<open>assert*\<close> "evaluate and assert term"
    ((opt_evaluator -- ODL_Meta_Args_Parser.opt_attributes -- opt_modes -- Parse.term) 
     >> pass_trans_to_assert_value_cmd);


(* setup ontology - aware text and ML antiquotations. Due to lexical restrictions, we can not
   declare them as value* or term*, although we will refer to them this way in papers. *)
local
  fun pretty_term_style ctxt (style: term -> term, t) =
      Document_Output.pretty_term ctxt (style (DOF_core.check_term ctxt t))
  fun print_term ctxt t = ML_Syntax.print_term (DOF_core.check_term (Context.proof_of ctxt) t)
in
val _ = Theory.setup
  (Document_Output.antiquotation_pretty_source_embedded \<^binding>\<open>value_\<close>
    (Scan.lift opt_evaluator -- Term_Style.parse -- Scan.lift Parse.term)
    (fn ctxt => fn ((name, style), t) =>
      Document_Output.pretty_term ctxt (style (value_select' name ctxt t)))
  #> ML_Antiquotation.inline_embedded \<^binding>\<open>value_\<close>
      ((Scan.lift (opt_evaluator -- Parse.term))
      #> (fn ((name, t),(ctxt, ts)) =>
           (((value_select' name (Context.proof_of ctxt) t)
             |> (ML_Syntax.atomic o (print_term ctxt))), (ctxt, ts))))
  #> Document_Output.antiquotation_pretty_source_embedded \<^binding>\<open>term_\<close> 
             (Term_Style.parse -- Args.term) pretty_term_style
  #> ML_Antiquotation.inline_embedded \<^binding>\<open>term_\<close>
       (fn (ctxt, ts) => (Args.term >> (ML_Syntax.atomic o (print_term ctxt))) (ctxt, ts)))
end

(* setup evaluators  *)
val _ = Theory.setup(
     add_evaluator (\<^binding>\<open>simp\<close>, Code_Simp.dynamic_value) #> snd
  #> add_evaluator (\<^binding>\<open>nbe\<close>,  Nbe.dynamic_value) #> snd
  #> add_evaluator (\<^binding>\<open>code\<close>, Code_Evaluation.dynamic_value_strict) #> snd);


end;  (* structure Value_Command *)


structure Monitor_Command_Parser = 
struct

fun update_instance_command  ((binding, cid_pos),
                              doc_attrs: (((string*Position.T)*string)*string)list) thy
            : theory = 
  let val oid = Binding.name_of binding
      val cid = let val DOF_core.Instance {cid,...} =
                                      DOF_core.get_instance_global oid thy
                    val ctxt =  Proof_Context.init_global thy
                    val instances = DOF_core.get_instances ctxt
                    val markup = DOF_core.get_instance_name_global oid thy
                                 |> Name_Space.markup (Name_Space.space_of_table instances)
                    val _ = Context_Position.report ctxt (Binding.pos_of binding) markup;
                in  cid end
      val default_cid = cid = DOF_core.default_cid
      val (((name, cid'), typ), pos') = Value_Command.Docitem_Parser.check_classref {is_monitor = false}
                                                                              cid_pos thy
      val cid_pos' = (name, pos')
      val cid_long = fst cid_pos'
      val _ = if cid' = DOF_core.default_cid  orelse cid = cid'
              then () 
              else error("incompatible classes:"^cid^":"^cid')
      fun conv_attrs (((lhs, pos), opn), rhs) = ((Protocol_Message.clean_output lhs),pos,opn, 
                                                  Syntax.parse_term (Proof_Context.init_global thy) rhs)
      val assns' = map conv_attrs doc_attrs
      val def_trans_value  =
        #1 o (Value_Command.Docitem_Parser.calc_update_term {mk_elaboration=true}
                                                                      thy (name, typ) assns')
        #> Value_Command.value (Proof_Context.init_global thy)
  in     
      thy |> (if Config.get_global thy DOF_core.object_value_debug 
              then let val def_trans_input_term  =
                         #1 o (Value_Command.Docitem_Parser.calc_update_term
                                   {mk_elaboration=false} thy (name, typ)  assns')
              in DOF_core.map_input_term_value oid
                         def_trans_input_term def_trans_value end
              else DOF_core.map_value oid def_trans_value)
          |> tap (DOF_core.check_ml_invs cid_long oid {is_monitor=false})
          (* Bypass checking of high-level invariants when the class default_cid = "text",
             the top (default) document class.
             We want the class default_cid to stay abstract
             and not have the capability to be defined with attribute, invariants, etc.
             Hence this bypass handles docitem without a class associated,
             for example when you just want a document element to be referentiable
             without using the burden of ontology classes.
             ex: text*[sdf]\<open> Lorem ipsum @{thm refl}\<close> *)
          |> (fn thy => if default_cid then thy
                        else if Config.get_global thy DOF_core.invariants_checking
                             then Value_Command.Docitem_Parser.check_invariants thy binding
                             else thy)
  end


(* General criticism : attributes like "level" were treated here in the kernel instead of dragging
   them out into the COL -- bu *)


fun open_monitor_command  (((binding, raw_parent_pos), doc_attrs) : ODL_Meta_Args_Parser.meta_args_t) thy =
    let fun o_m_c binding params_cid_pos doc_attrs thy =
          Value_Command.Docitem_Parser.create_and_check_docitem 
            {is_monitor=true}  (* this is a monitor *)
            {is_inline=false} (* monitors are always inline *)
            {define=true}
            binding params_cid_pos doc_attrs thy
        fun compute_enabled_set cid thy =
          let
            val DOF_core.Onto_Class X = DOF_core.get_onto_class_global' cid thy
            val ralph = RegExpInterface.alphabet (#rejectS X)
            val aalph = RegExpInterface.alphabet (#rex X)
          in  (aalph, ralph, map (RegExpInterface.rexp_term2da thy aalph)(#rex X)) end 
        fun create_monitor_entry thy =  
          let val cid = case raw_parent_pos of
                            NONE => ISA_core.err ("You must specified a monitor class.") (Binding.pos_of binding)
                          | SOME (raw_parent, _) =>
                              DOF_core.markup2string raw_parent 
                              |> DOF_core.get_onto_class_cid thy |> (fst o fst)
              val (accS, rejectS, aS) = compute_enabled_set cid thy
          in DOF_core.add_monitor_info binding
                                       (DOF_core.make_monitor_info (accS, rejectS, aS)) thy
          end
    in
      thy
      |> o_m_c binding raw_parent_pos doc_attrs
      |> create_monitor_entry
    end;


fun close_monitor_command (args as ((binding, cid_pos),
                                    _: (((string*Position.T)*string)*string)list)) thy = 
    let val oid = Binding.name_of binding
        val pos = Binding.pos_of binding
        fun check_if_final aS = let val i = (find_index (not o RegExpInterface.final) aS) + 1
                                in  if i >= 1 
                                    then
                                      Value_Command.Docitem_Parser.msg thy
                                                    ("accepts clause " ^ Int.toString i 
                                                     ^ " of monitor " ^ oid
                                                     ^ " not in final state.") pos
                                    else ()
                                end
        val _ = let val DOF_core.Monitor_Info {automatas,...} =
                                                  DOF_core.get_monitor_info_global oid thy
                in check_if_final automatas end
        val oid' = DOF_core.get_monitor_info_name_global oid thy
        val delete_monitor_entry = DOF_core.Monitor_Info.map (Name_Space.del_table oid')
        val DOF_core.Instance {cid=cid_long,...} = DOF_core.get_instance_global oid thy
        val ctxt = Proof_Context.init_global thy
        val instances = DOF_core.get_instances ctxt
        val markup = DOF_core.get_instance_name_global oid thy
                      |> Name_Space.markup (Name_Space.space_of_table instances)
        val _ = Context_Position.report ctxt pos markup;
    in  thy |> tap (DOF_core.check_closing_ml_invs cid_long oid {is_monitor=true})
            |> update_instance_command args
            |> tap (DOF_core.check_ml_invs cid_long oid {is_monitor=true})
            |> (fn thy => if Config.get_global thy DOF_core.invariants_checking
                          then Value_Command.Docitem_Parser.check_invariants thy binding
                          else thy)
            |> delete_monitor_entry
    end 


fun meta_args_2_latex thy sem_attrs transform_attr
      (((binding, cid_opt), attr_list) : ODL_Meta_Args_Parser.meta_args_t) =
    (* for the moment naive, i.e. without textual normalization of 
       attribute names and adapted term printing *)
    let val lab = Binding.name_of binding
        val l   = DOF_core.get_instance_name_global lab thy |> DOF_core.output_name
                                                            |> enclose "{" "}"
                                                            |> prefix "label = "
        val ((cid_long, _), _) = case cid_opt of
                               NONE => let val DOF_core.Instance cid =
                                             DOF_core.get_instance_global lab thy
                                        in pair (cid |> #cid) (cid |> #cid)
                                           |> rpair DOF_core.default_cid_typ end
                                  
                              | SOME(cid,_) => DOF_core.get_onto_class_cid thy cid        

        val cid_txt  = cid_long |> DOF_core.output_name
                                |> enclose "{" "}"
                                |> prefix "type = "
        fun ltx_of_term _ _ (c as \<^Const_>\<open>Cons \<^Type>\<open>char\<close> for _ _\<close>) = HOLogic.dest_string c
          | ltx_of_term _ _ \<^Const_>\<open>Nil _\<close> = ""
          | ltx_of_term _ _ \<^Const_>\<open>numeral _ for t\<close> = Int.toString(HOLogic.dest_numeral t)
          | ltx_of_term ctx encl \<^Const_>\<open>Cons _ for t1 t2\<close> =
              let val inner = (case t2 of 
                                 \<^Const_>\<open>Nil _\<close> => ltx_of_term ctx true t1
                              | _ => ((ltx_of_term ctx false t1)^", " ^(ltx_of_term ctx false t2)))
              in if encl then enclose "{" "}" inner else inner end
          | ltx_of_term _ _ \<^Const_>\<open>None _\<close> = ""
          | ltx_of_term ctxt _ \<^Const_>\<open>Some _ for t\<close> = ltx_of_term ctxt true t
          | ltx_of_term ctxt _ t = ""^(Sledgehammer_Util.hackish_string_of_term ctxt t)


        fun ltx_of_term_dbg ctx encl term  = let 
              val t_str = ML_Syntax.print_term term  
                          handle (TERM _) => "Exception TERM in ltx_of_term_dbg (print_term)"
              val ltx = ltx_of_term ctx encl term
              val _ = writeln("<STRING>"^(Sledgehammer_Util.hackish_string_of_term ctx term)^"</STRING>")
              val _ = writeln("<LTX>"^ltx^"</LTX>")
              val _ = writeln("<TERM>"^t_str^"</TERM>")
            in ltx end 


        fun markup2string s = String.concat (List.filter (fn c => c <> Symbol.DEL) 
                                            (Symbol.explode (Protocol_Message.clean_output s)))
        fun ltx_of_markup ctxt s = let
  	                            val term = (Syntax.check_term ctxt o Syntax.parse_term ctxt) s
                                val str_of_term = ltx_of_term  ctxt true term 
                                  (*  handle _ => "Exception in ltx_of_term" *)
                              in
                                str_of_term
                              end 
        fun toLong n = #long_name(the(DOF_core.get_attribute_info cid_long (markup2string n) thy))
        val ctxt = Proof_Context.init_global thy
        val actual_args =  map (fn ((lhs,_),rhs) => (toLong lhs, ltx_of_markup ctxt rhs))
                               attr_list
	      val default_args =
          (DOF_core.get_attribute_defaults cid_long thy)
          |> map (fn (b,_, parsed_term) =>
                    (toLong (Long_Name.base_name ( Sign.full_name thy b))
                    , ltx_of_term ctxt true (Syntax.check_term ctxt parsed_term)))
              
        val default_args_filtered = filter (fn (a,_) => not (exists (fn b => b = a) 
                                    (map (fn (c,_) => c) actual_args))) default_args
        val transformed_args = (actual_args@default_args_filtered)
                               |> transform_attr
        fun update_sem_std_attrs [] attrs = attrs
          | update_sem_std_attrs (attr::attrs) attrs' =
              let val attrs'' = attrs' |> map (fn (name, value) =>
                                let val value' = value |> Long_Name.base_name
                                in 
                                  if name = attr
                                  then if value' |>  Symbol.is_ascii_identifier
                                        then (name, DOF_core.output_name value')
                                        else ISA_core.err ("Bad name of semantic attribute"
                                                           ^ name ^ ": " ^ value
                                                           ^ ". Name must be ASCII") (Binding.pos_of binding)
                                else (name, value') end)
              in update_sem_std_attrs attrs attrs'' end
        val updated_sem_std_attrs = update_sem_std_attrs sem_attrs transformed_args
        val updated_sem_std_attrs' = updated_sem_std_attrs |> map (apfst DOF_core.output_name)
        val str_args = updated_sem_std_attrs'
                       |> map (fn (lhs,rhs) => lhs^" = "^(enclose "{" "}" rhs)) 
                      
        val label_and_type = String.concat [ l, ",", cid_txt]
        val str_args = label_and_type::str_args
    in
      Latex.string (enclose "[" "]" (String.concat [ label_and_type, ", args={", (commas str_args), "}"]))
    end


(* level-attribute information management *)
fun gen_enriched_document_cmd {inline} cid_transform attr_transform
    (((binding,cid_pos), doc_attrs) : ODL_Meta_Args_Parser.meta_args_t) : theory -> theory =
  Value_Command.Docitem_Parser.create_and_check_docitem {is_monitor = false} {is_inline = inline}
   {define = true} binding (cid_transform cid_pos) (attr_transform doc_attrs);

fun gen_enriched_document_cmd' {inline} cid_transform attr_transform
    (((binding,cid_pos), doc_attrs) : ODL_Meta_Args_Parser.meta_args_t) : theory -> theory =
  Value_Command.Docitem_Parser.create_and_check_docitem {is_monitor = false} {is_inline = inline}
   {define = false} binding (cid_transform cid_pos) (attr_transform doc_attrs);


(* markup reports and document output *)

(* {markdown = true} sets the parsing process such that in the text-core
   markdown elements are accepted. *)

fun document_output {markdown: bool, markup: Latex.text -> Latex.text} sem_attrs transform_attr meta_args text ctxt =
  let
    val thy = Proof_Context.theory_of ctxt;
    val _ = Context_Position.reports ctxt (Document_Output.document_reports text);
    val output_meta = meta_args_2_latex thy sem_attrs transform_attr meta_args;
    val output_text = Document_Output.output_document ctxt {markdown = markdown} text;
  in markup (output_meta @ output_text) end;

fun document_output_reports name {markdown, body} sem_attrs transform_attr meta_args text ctxt =
  let
    fun markup xml =
      let val m = if body then Markup.latex_body else Markup.latex_heading
      in [XML.Elem (m (Latex.output_name name), xml)] end;
    val config = {markdown = markdown, markup = markup}
  in document_output config sem_attrs transform_attr meta_args text ctxt 
  end;


(* document output commands *)

fun document_command (name, pos) descr mark cmd sem_attrs transform_attr =
  Outer_Syntax.command (name, pos) descr
  (ODL_Meta_Args_Parser.attributes -- Parse.document_source >> (fn (meta_args, text) =>
      Toplevel.theory' (fn _ => cmd meta_args)
          (SOME (Toplevel.presentation_context #> document_output_reports name mark sem_attrs transform_attr meta_args text)))); 

fun onto_macro_cmd_output_reports output_cmd (meta_args, text) ctxt =
 let
   val _ = Context_Position.reports ctxt (Document_Output.document_reports text);
 in output_cmd (meta_args, text) ctxt end

fun onto_macro_cmd_command (name, pos) descr cmd output_cmd = 
  Outer_Syntax.command (name, pos) descr 
  (ODL_Meta_Args_Parser.attributes -- Parse.document_source >>  
     (fn (meta_args, text) =>
          Toplevel.theory' (fn _ => cmd meta_args)
             (SOME (Toplevel.presentation_context
              #> onto_macro_cmd_output_reports output_cmd  (meta_args, text)
              ))))



(* Core Command Definitions *)

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>open_monitor*\<close>
                       "open a document reference monitor"
                       (ODL_Meta_Args_Parser.attributes
                        >> (Toplevel.theory o open_monitor_command));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>close_monitor*\<close>
                       "close a document reference monitor"
                       (ODL_Meta_Args_Parser.attributes_upd
                        >> (Toplevel.theory o close_monitor_command)); 

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>update_instance*\<close>
                       "update meta-attributes of an instance of a document class"
                        (ODL_Meta_Args_Parser.attributes_upd
                         >> (Toplevel.theory o update_instance_command));

val _ =
  document_command \<^command_keyword>\<open>text*\<close> "formal comment (primary style)"
    {markdown = true, body = true} (gen_enriched_document_cmd {inline=true} I I) [] I;
                                                 

(* This is just a stub at present *)
val _ =
  document_command \<^command_keyword>\<open>text-macro*\<close> "formal comment macro"
    {markdown = true, body = true}
    (gen_enriched_document_cmd {inline=false} (* declare as macro *) I I) [] I;

 
val (declare_reference_default_class, declare_reference_default_class_setup) 
     = Attrib.config_string \<^binding>\<open>declare_reference_default_class\<close> (K "");

val _ = Theory.setup declare_reference_default_class_setup

val _ = 
  let fun default_cid meta_args thy =
        let
          fun default_cid' _ NONE cid_pos = cid_pos
            | default_cid' thy (SOME ncid) NONE =
                let val name = DOF_core.get_onto_class_name_global' ncid thy
                    val ns = DOF_core.get_onto_classes (Proof_Context.init_global thy)
                             |> Name_Space.space_of_table
                    val {pos, ...} = Name_Space.the_entry ns name
                in SOME (name,pos) end
            | default_cid' _ (SOME _) cid_pos = cid_pos
          val ncid =  Config.get_global thy declare_reference_default_class
          val ncid' = if ncid = ""
                      then NONE
                      else SOME ncid
        in gen_enriched_document_cmd' {inline=true} (default_cid' thy ncid') I meta_args thy
        end
  in  Outer_Syntax.command \<^command_keyword>\<open>declare_reference*\<close>
                       "declare document reference"
                       (ODL_Meta_Args_Parser.attributes 
                        >> (Toplevel.theory o default_cid))
  end;

end (* structure Monitor_Command_Parser *)
\<close>



ML\<open>
fun print_doc_classes _ ctxt = 
    let val classes = Name_Space.dest_table (DOF_core.get_onto_classes ctxt)
        val _ = writeln "=====================================";    
        fun print_attr (n, _, NONE) = (Binding.print n)
          | print_attr (n, _, SOME t)= (Binding.print n^"("^Syntax.string_of_term ctxt t^")")
        fun print_inv (bind,trm) = ((Binding.name_of bind |> unsuffix invariant_suffixN)
                                     ^"::"^Syntax.string_of_term ctxt trm)
        fun print_virtual {virtual} = Bool.toString virtual
        fun print_class (n, DOF_core.Onto_Class {attribute_decl, name, inherits_from, virtual
                                                 , invs, ...}) =
           (case inherits_from of 
               NONE => writeln ("docclass: "^n)
             | SOME(_,nn) => writeln ("docclass: "^n^" = "^nn^" + ");
            writeln ("    name:       "^(Binding.print name));
            writeln ("    virtual:    "^(print_virtual virtual));
            writeln ("    attrs:      "^commas (map print_attr attribute_decl));
            writeln ("    invs:       "^commas (map print_inv invs))
           );
    in  map print_class classes; 
        writeln "=====================================\n\n\n" 
    end;

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>print_doc_classes\<close> "print document classes"
    (Parse.opt_bang >> (fn b => Toplevel.keep (print_doc_classes b o Toplevel.context_of)));

fun print_docclass_template cid ctxt = 
    let (* takes class synonyms into account *)
        val cid_long = DOF_core.get_onto_class_name_global' cid (Proof_Context.theory_of ctxt)
        val brute_hierarchy = (DOF_core.get_attributes_local cid_long ctxt)
        val flatten_hrchy = flat o (map(fn(lname, attrS) => 
                                           map (fn (s,_,_)=>(lname,(Binding.name_of s))) attrS))
        fun filter_overrides [] = []
           |filter_overrides ((ln,s)::S) = (ln,s):: filter_overrides(filter(fn(_,s')=> s<>s')S) 
        val hierarchy = map (fn(ln,s)=>ln^"."^s)(filter_overrides(flatten_hrchy brute_hierarchy)) 
        val args = String.concatWith "=%\n , " ("  label=,type":: hierarchy);
        val template = "\\newisadof{"^cid_long^"}%\n["^args^"=%\n][1]\n{%\n#1%\n}\n\n";
    in writeln template end;

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>print_doc_class_template\<close> 
                       "print document class latex template"
    (Parse.string >> (fn b => Toplevel.keep (print_docclass_template b o Toplevel.context_of)));

fun print_doc_items _ ctxt =
    let val x = DOF_core.get_instances ctxt
        val _ = writeln "=====================================";  
        fun dfg true = "true" 
           |dfg false= "false"   
        fun print_item (n, DOF_core.Instance {defined,cid,vcid, inline, input_term, value}) =
                 ((if defined then 
                  writeln ("docitem:             "^n)
                  else
                  writeln ("forward reference for docitem: "^n));
                  writeln ("    defined:         "^dfg defined);
                  writeln ("    type:            "^cid);
                  case vcid of NONE => () | SOME (s) => 
                  writeln ("    virtual type:    "^ s);
                  writeln ("    inline:          "^dfg inline);
                  (if Config.get ctxt DOF_core.object_value_debug
                   then  writeln ("    input_term:      "^ (Syntax.string_of_term ctxt input_term))
                   else ());
                  writeln ("    value:           "^ (Syntax.string_of_term ctxt value))
                 )
    in  map print_item (Name_Space.dest_table x); 
        writeln "=====================================\n\n\n" end;

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>print_doc_items\<close>  "print document items"
    (Parse.opt_bang >> (fn b => Toplevel.keep (print_doc_items b o Toplevel.context_of)));

fun check_doc_global (strict_checking : bool) ctxt = 
  let val S = ctxt |> DOF_core.get_instances |> Name_Space.dest_table
              |> filter (fn (_, DOF_core.Instance {defined,...}) => (not defined))
              |> map #1
      val T = map fst (Name_Space.dest_table (DOF_core.get_monitor_infos ctxt))
  in if null S 
     then if null T then ()
          else error("Global consistency error - there are open monitors:  "
                ^ String.concatWith "," T) 
     else error("Global consistency error - Unresolved forward references: "
                ^ String.concatWith "," S)   
  end

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>check_doc_global\<close> "check global document consistency"
    (Parse.opt_bang >> (fn b => Toplevel.keep (check_doc_global b o Toplevel.context_of)));

\<close>

\<comment> \<open>c.f. \<^file>\<open>~~/src/Pure/Isar/outer_syntax.ML\<close>\<close>
(*
  The ML* generates an "ontology-aware" version of the SML code-execution command.
*)
ML\<open>
structure ML_star_Command =
struct

fun meta_args_exec (meta_args as ((binding,cid_pos), doc_attrs) : ODL_Meta_Args_Parser.meta_args_t) ctxt = 
         ctxt |> (if meta_args = ODL_Meta_Args_Parser.empty_meta_args
                 then (K ctxt)                               
                 else Context.map_theory (Value_Command.Docitem_Parser.create_and_check_docitem 
                                    {is_monitor = false} {is_inline = true} 
                                    {define = true} binding (I cid_pos) (I doc_attrs)))

val attributes_opt = Scan.option ODL_Meta_Args_Parser.attributes

val _ =
  Outer_Syntax.command ("ML*", \<^here>) "ODL annotated ML text within theory or local theory"
    ((ODL_Meta_Args_Parser.attributes -- Parse.ML_source) 
     >> (fn (meta_args_opt, source) =>
            Toplevel.generic_theory
              ((meta_args_exec meta_args_opt)
               #> (ML_Context.exec (fn () =>  
                     (ML_Context.eval_source (ML_Compiler.verbose true ML_Compiler.flags) source)) 
               #> Local_Theory.propagate_ml_env))));

end
\<close>

\<comment> \<open>c.f. \<^file>\<open>~~/src/Pure/Isar/specification.ML\<close> and \<^file>\<open>~~/src/Pure/Pure.thy\<close>\<close>
ML\<open>
structure Definition_Star_Command =
struct

fun get_positions ctxt x =
  let
    fun get Cs (Const ("_type_constraint_", C) $ t) = get (C :: Cs) t
      | get Cs (Free (y, T)) =
          if x = y then
            maps Term_Position.decode_positionT
              (T :: map (Type.constraint_type ctxt) Cs)
          else []
      | get _ (t $ u) = get [] t @ get [] u
      | get _ (Abs (_, _, t)) = get [] t
      | get _ _ = [];
  in get [] end;

fun dummy_frees ctxt xs tss =
  let
    val names =
      Variable.names_of ((fold o fold) Variable.declare_term tss ctxt)
      |> fold Name.declare xs;
    val (tss', _) = (fold_map o fold_map) Term.free_dummy_patterns tss names;
  in tss' end;

fun prep_spec_open prep_var parse_prop raw_vars raw_params raw_prems raw_concl ctxt =
  let
    val ((vars, xs), vars_ctxt) = DOF_core.prep_decls prep_var raw_vars ctxt;
    val (ys, params_ctxt) = vars_ctxt |> fold_map prep_var raw_params |-> Proof_Context.add_fixes;
    val props =
      map (parse_prop params_ctxt) (raw_concl :: raw_prems)
      |> singleton (dummy_frees params_ctxt (xs @ ys));
    val props' = props |> map (DOF_core.elaborate_term' ctxt)
    val concl :: prems = Syntax.check_props params_ctxt props';
    val spec = Logic.list_implies (prems, concl);
    val spec_ctxt = Variable.declare_term spec params_ctxt;

    fun get_pos x = maps (get_positions spec_ctxt x) props;
    in ((vars, xs, get_pos, spec), spec_ctxt) end;

val read_spec_open = prep_spec_open Proof_Context.read_var Syntax.parse_prop;

(* definition *)

fun gen_def prep_spec prep_att raw_var raw_params raw_prems ((a, raw_atts), raw_spec) int lthy =
  let
    val atts = map (prep_att lthy) raw_atts;

    val ((vars, xs, get_pos, spec), _) = lthy
      |> prep_spec (the_list raw_var) raw_params raw_prems raw_spec;
    val (((x, T), rhs), prove) = Local_Defs.derived_def lthy get_pos {conditional = true} spec;
    val _ = Name.reject_internal (x, []);
    val (b, mx) =
      (case (vars, xs) of
        ([], []) => (Binding.make (x, (case get_pos x of [] => Position.none | p :: _ => p)), NoSyn)
      | ([(b, _, mx)], [y]) =>
          if x = y then (b, mx)
          else
            error ("Head of definition " ^ quote x ^ " differs from declaration " ^ quote y ^
              Position.here (Binding.pos_of b)));

    val name = Thm.def_binding_optional b a;
    val ((lhs, (_, raw_th)), lthy2) = lthy
      |> Local_Theory.define_internal ((b, mx), ((Binding.suffix_name "_raw" name, []), rhs));

    val th = prove lthy2 raw_th;
    val lthy3 = lthy2 |> Spec_Rules.add name Spec_Rules.equational [lhs] [th];

    val ([(def_name, [th'])], lthy4) = lthy3
      |> Local_Theory.notes [((name, atts), [([th], [])])];

    val lthy5 = lthy4
      |> Code.declare_default_eqns [(th', true)];

    val lhs' = Morphism.term (Local_Theory.target_morphism lthy5) lhs;

    val _ =
      Proof_Display.print_consts int (Position.thread_data ()) lthy5
        (Frees.defined (Frees.build (Frees.add_frees lhs'))) [(x, T)];
  in ((lhs, (def_name, th')), lthy5) end;

val definition_cmd = gen_def read_spec_open Attrib.check_src;

fun definition_cmd' meta_args_opt decl params prems spec bool ctxt =
  Local_Theory.background_theory (Value_Command.meta_args_exec meta_args_opt) ctxt
  |> definition_cmd decl params prems spec bool

val _ =
  Outer_Syntax.local_theory' \<^command_keyword>\<open>definition*\<close> "constant definition"
    (ODL_Meta_Args_Parser.opt_attributes --
      (Scan.option Parse_Spec.constdecl -- (Parse_Spec.opt_thm_name ":" -- Parse.prop) --
        Parse_Spec.if_assumes -- Parse.for_fixes)
     >> (fn (meta_args_opt, (((decl, spec), prems), params)) => 
                                    #2 oo definition_cmd' meta_args_opt decl params prems spec));
end
\<close>

\<comment> \<open>c.f. \<^file>\<open>~~/src/Pure/Isar/specification.ML\<close> and \<^file>\<open>~~/src/Pure/Pure.thy\<close>\<close>
ML\<open>
(* theorem*, lemma*, etc. commands *)

local

fun elaborate stmt ctxt = stmt |> map (apsnd (map (apfst (DOF_core.elaborate_term ctxt)
                                              #> apsnd (map (DOF_core.elaborate_term ctxt)))))

fun prep_statement prep_att prep_stmt raw_elems raw_stmt ctxt =
  let
    val (stmt, elems_ctxt) = prep_stmt raw_elems raw_stmt ctxt;
    val prems = Assumption.local_prems_of elems_ctxt ctxt;
    val stmt_ctxt = fold (fold (Proof_Context.augment o fst) o snd) stmt elems_ctxt;
  in
    (case raw_stmt of
      Element.Shows _ =>
        let val stmt' = Attrib.map_specs (map prep_att) stmt
            val stmt'' = elaborate stmt' ctxt
        in (([], prems, stmt'', NONE), stmt_ctxt) end
    | Element.Obtains raw_obtains =>
        let
          val asms_ctxt = stmt_ctxt
            |> fold (fn ((name, _), asm) =>
                snd o Proof_Context.add_assms Assumption.assume_export
                  [((name, [Context_Rules.intro_query NONE]), asm)]) stmt;
          val that = Assumption.local_prems_of asms_ctxt stmt_ctxt;
          val ([(_, that')], that_ctxt) = asms_ctxt
            |> Proof_Context.set_stmt true
            |> Proof_Context.note_thmss "" [((Binding.name Auto_Bind.thatN, []), [(that, [])])]
            ||> Proof_Context.restore_stmt asms_ctxt;

          val stmt' = [(Binding.empty_atts, [(#2 (#1 (Obtain.obtain_thesis ctxt)), [])])];
          val stmt'' = elaborate stmt' ctxt
        in ((Obtain.obtains_attribs raw_obtains, prems, stmt'', SOME that'), that_ctxt) end)
  end;

fun gen_theorem schematic bundle_includes prep_att prep_stmt
    long kind before_qed after_qed (name, raw_atts) raw_includes raw_elems raw_concl int lthy =
  let
    val _ = Local_Theory.assert lthy;

    val elems = raw_elems |> map (Element.map_ctxt_attrib (prep_att lthy));
    val ((more_atts, prems, stmt, facts), goal_ctxt) = lthy
      |> bundle_includes raw_includes
      |> prep_statement (prep_att lthy) prep_stmt elems raw_concl;
    val atts = more_atts @ map (prep_att lthy) raw_atts;

    val pos = Position.thread_data ();
    val print_results =
      Proof_Display.print_results {interactive = int, pos = pos, proof_state = false};

    fun after_qed' results goal_ctxt' =
      let
        val results' =
          burrow (map (Goal.norm_result lthy) o Proof_Context.export goal_ctxt' lthy) results;
        val (res, lthy') =
          if forall (Binding.is_empty_atts o fst) stmt then (map (pair "") results', lthy)
          else
            Local_Theory.notes_kind kind
              (map2 (fn (b, _) => fn ths => (b, [(ths, [])])) stmt results') lthy;
        val lthy'' =
          if Binding.is_empty_atts (name, atts)
          then (print_results lthy' ((kind, ""), res); lthy')
          else
            let
              val ([(res_name, _)], lthy'') =
                Local_Theory.notes_kind kind [((name, atts), [(maps #2 res, [])])] lthy';
              val _ = print_results lthy' ((kind, res_name), res);
            in lthy'' end;
      in after_qed results' lthy'' end;

    val prems_name = if long then Auto_Bind.assmsN else Auto_Bind.thatN;
  in
    goal_ctxt
    |> not (null prems) ?
      (Proof_Context.note_thmss "" [((Binding.name prems_name, []), [(prems, [])])] #> snd)
    |> Proof.theorem before_qed after_qed' (map snd stmt)
    |> (case facts of NONE => I | SOME ths => Proof.refine_insert ths)
    |> tap (fn state => not schematic andalso Proof.schematic_goal state andalso
        error "Illegal schematic goal statement")
  end;

in

val theorem_cmd =
  gen_theorem false Bundle.includes_cmd Attrib.check_src Expression.read_statement;

fun theorem_cmd' meta_args_opt long kind before_qed after_qed (name, raw_atts) raw_includes raw_elems raw_concl int lthy =
  Local_Theory.background_theory (Value_Command.meta_args_exec meta_args_opt) lthy
  |> theorem_cmd long kind before_qed after_qed (name, raw_atts) raw_includes raw_elems raw_concl int;

val schematic_theorem_cmd =
  gen_theorem true Bundle.includes_cmd Attrib.check_src Expression.read_statement;

fun schematic_theorem_cmd' meta_args_opt long kind before_qed after_qed (name, raw_atts) raw_includes raw_elems raw_concl int lthy =
  Local_Theory.background_theory (Value_Command.meta_args_exec meta_args_opt) lthy
  |> schematic_theorem_cmd long kind before_qed after_qed (name, raw_atts) raw_includes raw_elems raw_concl int;

end;

local
val long_keyword =
  Parse_Spec.includes >> K "" ||
  Parse_Spec.long_statement_keyword;

val long_statement =
  ODL_Meta_Args_Parser.opt_attributes --
  Scan.optional (Parse_Spec.opt_thm_name ":" --| Scan.ahead long_keyword) Binding.empty_atts --
  Scan.optional Parse_Spec.includes [] -- Parse_Spec.long_statement
    >> (fn (((meta_args_opt, binding), includes), (elems, concl)) => (meta_args_opt, true, binding, includes, elems, concl));

val short_statement =
  ODL_Meta_Args_Parser.opt_attributes --
  Parse_Spec.statement -- Parse_Spec.if_statement -- Parse.for_fixes
    >> (fn (((meta_args_opt, shows), assumes), fixes) =>
      (meta_args_opt, false, Binding.empty_atts, [], [Element.Fixes fixes, Element.Assumes assumes],
        Element.Shows shows));

fun theorem spec schematic descr =
  Outer_Syntax.local_theory_to_proof' spec ("state " ^ descr)
    ((long_statement || short_statement) >> (fn (meta_args_opt, long, binding, includes, elems, concl) =>
      ((if schematic then schematic_theorem_cmd' else theorem_cmd')
        meta_args_opt long Thm.theoremK NONE (K I) binding includes elems concl)));

val _ = theorem \<^command_keyword>\<open>theorem*\<close> false "theorem";
val _ = theorem \<^command_keyword>\<open>lemma*\<close> false "lemma";
val _ = theorem \<^command_keyword>\<open>corollary*\<close> false "corollary";
val _ = theorem \<^command_keyword>\<open>proposition*\<close> false "proposition";
val _ = theorem \<^command_keyword>\<open>schematic_goal*\<close> true "schematic goal";
in end
\<close>


section\<open> Syntax for Ontological Antiquotations (the '' View'' Part II) \<close>

ML\<open>
structure OntoLinkParser = 
struct

val basic_entity = Document_Output.antiquotation_pretty_source
    : binding -> 'a context_parser -> (Proof.context -> 'a -> Pretty.T) -> theory -> theory;

fun check_and_mark ctxt cid_decl ({strict_checking = strict}) {inline=inline_req} pos name  =
  let
    val thy = Proof_Context.theory_of ctxt;
    val DOF_core.Instance {cid,inline, defined, ...} = DOF_core.get_instance_global name thy
    val _ = if not strict
            then if defined
                 then ISA_core.warn ("Instance defined, unchecked option useless") pos
                 else ()
            else if defined
                 then ()
                 else ISA_core.err ("Instance declared but not defined, try option unchecked") pos
    val _ = if not inline_req 
            then if inline then () else error("referred text-element is macro! (try option display)")
            else if not inline then () else error("referred text-element is no macro!")
    val instances = DOF_core.get_instances ctxt
    val name' = DOF_core.get_instance_name_global name thy
    val markup = name' |> Name_Space.markup (Name_Space.space_of_table instances)
    (* this sends a report for a ref application to the PIDE interface ... *)
    val _ = Context_Position.report ctxt pos markup;
    val cid' = if cid = DOF_core.default_cid
               then cid
               else DOF_core.get_onto_class_cid thy cid |> (fst o fst)
    val _ = if not(DOF_core.is_subclass ctxt cid' cid_decl)
            then error("reference ontologically inconsistent: "
                       ^ name ^ " is an instance of " ^ cid
                       ^ " and " ^ cid
                       ^ " is not a subclass of " ^ cid_decl ^ Position.here pos)
            else ()
  in () end

val _ =  check_and_mark : Proof.context ->  string ->  
                          {strict_checking: bool} -> {inline:bool} ->
                          Position.T -> Symtab.key -> unit

(* generic syntax for doc_class links. *) 

val defineN    = "define"
val uncheckedN = "unchecked" 

val docitem_modes = Scan.optional (Args.parens (Args.$$$ defineN || Args.$$$ uncheckedN) 
                                   >> (fn str => if str = defineN 
                                                 then {unchecked = false, define= true}  
                                                 else {unchecked = true,  define= false})) 
                                   {unchecked = false, define= false} (* default *);


val docitem_antiquotation_parser = (Scan.lift (docitem_modes -- Parse.embedded_input))
                                   : ({define:bool,unchecked:bool} * Input.source) context_parser;


fun pretty_docitem_antiquotation_generic cid_decl ctxt ({unchecked, define}, src ) = 
    let val (str,pos) = Input.source_content src
                        |> apfst (fn str => (Proof_Context.theory_of ctxt)
                                            |> DOF_core.get_instance_name_global str)
        val inline = Config.get ctxt Document_Antiquotation.thy_output_display
        val _ = check_and_mark ctxt cid_decl {strict_checking = not unchecked} 
                                             {inline = inline} pos str
        val cid_decl' = DOF_core.output_name cid_decl
    in  
        (case (define,inline) of
            (true,false) => XML.enclose("{\\isaDofDOTlabel[type={"^cid_decl'^"}]   {")"}}" 
           |(false,false)=> XML.enclose("{\\isaDofDOTref[type={"^cid_decl'^"}]     {")"}}"
           |(true,true)  => XML.enclose("{\\isaDofDOTmacroDef[type={"^cid_decl'^"}]{")"}}" 
           |(false,true) => XML.enclose("{\\isaDofDOTmacroExp[type={"^cid_decl'^"}]{")"}}"
        )
        (Latex.text (DOF_core.output_name str, pos))
    end      


fun docitem_antiquotation bind cid =
  Document_Output.antiquotation_raw bind  docitem_antiquotation_parser
                                       (pretty_docitem_antiquotation_generic cid)

fun check_and_mark_term ctxt oid  =
  let
    val ctxt' = Context.proof_of ctxt
    val thy = Proof_Context.theory_of ctxt';
    val oid' = DOF_core.get_instance_name_global oid thy
    val DOF_core.Instance {cid,value,...} = DOF_core.get_instance_global oid' thy
    val instances = DOF_core.get_instances ctxt'
    val ns = instances |> Name_Space.space_of_table 
    val {pos, ...} = Name_Space.the_entry ns oid'
    val markup = oid' |> Name_Space.markup (Name_Space.space_of_table instances)
    val _ = Context_Position.report ctxt' pos markup;
    (* this sends a report for a ref application to the PIDE interface ... *) 
    val _ = if cid = DOF_core.default_cid
            then error("anonymous "^ DOF_core.default_cid ^ " class has no value" )
            else ()
  in value end

fun ML_antiquotation_docitem_value (ctxt, toks) = 
    (Scan.lift (Args.cartouche_input) 
     >> (fn inp => (ML_Syntax.atomic o ML_Syntax.print_term) 
                   ((check_and_mark_term ctxt o fst o Input.source_content) inp)))
     (ctxt, toks)

(* Setup for general docitems of the global DOF_core.default_cid - class ("text")*)
val _ = Theory.setup
           (docitem_antiquotation   \<^binding>\<open>docitem\<close>  DOF_core.default_cid #>
            
            ML_Antiquotation.inline \<^binding>\<open>docitem_value\<close> ML_antiquotation_docitem_value)

end (* struct *)
\<close>


ML\<open> 
structure AttributeAccess = 
struct

val basic_entity = Document_Output.antiquotation_pretty_source 
    : binding -> 'a context_parser -> (Proof.context -> 'a -> Pretty.T) -> theory -> theory;

fun compute_trace_ML ctxt oid pos_opt pos' =
    (* grabs attribute, and converts its HOL-term into (textual) ML representation *)
  let val term = ISA_core.compute_attr_access ctxt traceN oid pos_opt pos'
      fun conv (\<^Const>\<open>Pair \<^typ>\<open>doc_class rexp\<close> \<^typ>\<open>string\<close>\<close>
                  $ (\<^Const>\<open>Atom \<^typ>\<open>doc_class\<close>\<close> $ (\<^Const>\<open>mk\<close> $ s)) $ S) =
        let val s' =  DOF_core.get_onto_class_name_global (HOLogic.dest_string s) (Context.theory_of ctxt)
        in (s', HOLogic.dest_string S) end
  in  map conv (HOLogic.dest_list term) end


val parse_oid  = Scan.lift(Parse.position Args.name) 
val parse_cid  = Scan.lift(Parse.position Args.name) 
val parse_oid' = Term_Style.parse -- parse_oid
val parse_oid'' = Scan.lift(Parse.embedded_position)
val parse_cid' = Term_Style.parse -- parse_cid



val parse_attribute_access = (parse_oid
                              --| (Scan.lift @{keyword "::"}) 
                              -- Scan.lift (Parse.position Args.name))
                              : ((string *Position.T) * (string * Position.T)) context_parser 

val parse_attribute_access' = Term_Style.parse -- parse_attribute_access
                              : ((term -> term) *
                                 ((string * Position.T) * (string * Position.T))) context_parser

fun attr_2_ML ctxt ((attr:string,pos),(oid:string,pos')) = (ML_Syntax.atomic o ML_Syntax.print_term) 
                                                           (ISA_core.compute_attr_access ctxt attr oid (SOME pos) pos') 


fun get_instance_value_2_ML ctxt (oid:string,pos) =
    let val ctxt' = Context.the_proof ctxt
        val thy = Proof_Context.theory_of ctxt'
        val value = DOF_core.value_of oid thy
        val instances = DOF_core.get_instances ctxt'
        val markup = DOF_core.get_instance_name_global oid thy
                     |> Name_Space.markup (Name_Space.space_of_table instances)
        val _ = Context_Position.report ctxt' pos markup;
    in  ML_Syntax.print_term value end

fun get_instance_name_2_ML ctxt (oid:string,pos) =
    let val ctxt' = Context.the_proof ctxt
        val instances = DOF_core.get_instances ctxt'
        val markup = DOF_core.get_instance_name_global oid (Proof_Context.theory_of ctxt')
                     |> Name_Space.markup (Name_Space.space_of_table instances)
        val _ = Context_Position.report ctxt' pos markup;
    in "\"" ^ oid ^ "\"" end

fun trace_attr_2_ML ctxt (oid:string,pos) =
    let val print_string_pair = ML_Syntax.print_pair  ML_Syntax.print_string ML_Syntax.print_string
        val toML = (ML_Syntax.atomic o (ML_Syntax.print_list print_string_pair))
    in  toML (compute_trace_ML ctxt oid NONE pos) end 

fun compute_cid_repr ctxt cid _ = 
  let val _ = DOF_core.get_onto_class_name_global cid (Proof_Context.theory_of ctxt)
  in Const(cid,dummyT) end

local

fun pretty_attr_access_style ctxt (style, ((attr,pos),(oid,pos'))) = 
           Document_Output.pretty_term ctxt (style (ISA_core.compute_attr_access (Context.Proof ctxt) 
                                                                    attr oid (SOME pos) pos'));
fun pretty_trace_style ctxt (style, (oid,pos)) = 
          Document_Output.pretty_term ctxt (style (ISA_core.compute_attr_access  (Context.Proof ctxt) 
                                                                   traceN oid NONE pos));

fun pretty_name_style ctxt (oid,pos) =
let
  val instances = DOF_core.get_instances ctxt
  val ns = Name_Space.space_of_table instances
  val name  = DOF_core.get_instance_name_global oid (Proof_Context.theory_of ctxt)
  val ctxt' = Config.put Name_Space.names_unique true ctxt
  val _ = name |> Name_Space.markup ns
               |> Context_Position.report ctxt pos
in Name_Space.pretty ctxt' ns name end

fun pretty_cid_style ctxt (style, (cid,pos)) = 
          Document_Output.pretty_term ctxt (style (compute_cid_repr ctxt cid pos));

(* NEW VERSION: PLEASE INTEGRATE ALL OVER : *)
fun context_position_parser parse_con (ctxt, toks) = 
     let val pos = case toks of 
                    a :: _ => Token.pos_of a 
                  | _ => @{here}             \<comment> \<open>a real hack !\<close>
         val (res, (ctxt', toks')) = parse_con (ctxt, toks)
     in  ((res,pos),(ctxt', toks')) end

val parse_cid0 = parse_cid
val parse_cid = (context_position_parser Args.typ_abbrev)
          >> (fn (Type(ss,_),pos) =>  (pos,ss)
                |( _,pos) => ISA_core.err "Undefined Class Id" pos);


val parse_cid' = Term_Style.parse -- parse_cid

fun pretty_cid_style ctxt (_,(pos,cid)) = 
    (*reconversion to term in order to have access to term print options like: names_short etc...) *)
          Document_Output.pretty_term ctxt ((compute_cid_repr ctxt cid pos));

fun get_class_2_ML ctxt (str,_) =
        let val thy = Context.theory_of ctxt
            val DOF_core.Onto_Class S = (DOF_core.get_onto_class_global' str thy) 
         in @{make_string} S end

in
val _ = Theory.setup 
           (ML_Antiquotation.inline  \<^binding>\<open>docitem\<close> 
               (fn (ctxt,toks) => (parse_oid >> get_instance_value_2_ML ctxt) (ctxt, toks))  #>
            ML_Antiquotation.inline  \<^binding>\<open>docitem_attribute\<close> 
               (fn (ctxt,toks) => (parse_attribute_access >>  attr_2_ML ctxt) (ctxt, toks))  #>
            ML_Antiquotation.inline  \<^binding>\<open>trace_attribute\<close>  
               (fn (ctxt,toks) => (parse_oid >> trace_attr_2_ML ctxt) (ctxt, toks)) #>
            ML_Antiquotation.inline  \<^binding>\<open>docitem_name\<close>  
               (fn (ctxt,toks) => (parse_oid >> get_instance_name_2_ML ctxt) (ctxt, toks)) #>
            ML_Antiquotation.inline  \<^binding>\<open>doc_class\<close>  
               (fn (ctxt,toks) => (parse_cid0 >> get_class_2_ML ctxt) (ctxt, toks)) #>
            basic_entity  \<^binding>\<open>trace_attribute\<close>  parse_oid'  pretty_trace_style #>
            basic_entity  \<^binding>\<open>doc_class\<close>  parse_cid'  pretty_cid_style #>
            basic_entity  \<^binding>\<open>onto_class\<close> parse_cid'  pretty_cid_style #>
            basic_entity  \<^binding>\<open>docitem_attribute\<close>  parse_attribute_access' pretty_attr_access_style #>
            basic_entity  \<^binding>\<open>docitem_name\<close>  parse_oid'' pretty_name_style
           )
end
end
\<close>

text\<open> Note that the functions \<^verbatim>\<open>basic_entities\<close> and \<^verbatim>\<open>basic_entity\<close> in 
      @{ML_structure AttributeAccess} are copied from 
      @{file "$ISABELLE_HOME/src/Pure/Thy/document_output.ML"} \<close>


section\<open> Syntax for Ontologies (the '' View'' Part III) \<close> 
ML\<open>
structure OntoParser = 
struct

fun read_parent NONE ctxt = (NONE, ctxt)
  | read_parent (SOME raw_T) ctxt =
      (case Proof_Context.read_typ_abbrev ctxt raw_T of
        Type (name, Ts) => (SOME (Ts, name), fold Variable.declare_typ Ts ctxt)
      | T => error ("Bad parent record specification: " ^ Syntax.string_of_typ ctxt T));


fun read_fields raw_fields ctxt =
    let
      val fields' = raw_fields |> map (apfst (fn (b, ty, mx) => (b, Syntax.read_typ ctxt ty, mx)))
                               |> map (apsnd (Option.map (Syntax.parse_term ctxt #> DOF_core.elaborate_term' ctxt)))
      fun check_default ctxt ((b, ty, _), SOME trm) = 
        let val parsed_prop = Const (\<^const_name>\<open>Pure.eq\<close>, dummyT) $ Free (Binding.name_of b, dummyT) $ trm
            val raw_vars = [(b, SOME ty, NoSyn)]
            val (_, vars_ctxt) = DOF_core.prep_decls Proof_Context.cert_var raw_vars ctxt
            (* check typ unification *)
            val _  = Syntax.check_prop vars_ctxt parsed_prop
        in () end
                                         (* BAD STYLE : better would be catching exn. *) 
        | check_default _ (_, NONE)= ()
      val _ = map (check_default ctxt) fields'
      val ctxt' = fields' |> map (#2 o fst) |> (fn Ts => fold Variable.declare_typ Ts ctxt);
    in (map fst fields', map snd fields', ctxt') end;

fun def_cmd (decl, spec, prems, params) lthy =
  let
    val ((lhs as Free (x, T), _), lthy') = Specification.definition decl params prems spec lthy;
    val lhs' = Morphism.term (Local_Theory.target_morphism lthy') lhs;
    val _ =
      Proof_Display.print_consts true (Position.thread_data ()) lthy'
        (Frees.defined (Frees.build (Frees.add_frees lhs'))) [(x, T)]
  in lthy' end

fun mk_meta_eq (t, u) = \<^Const>\<open>Pure.eq \<open>fastype_of t\<close> for t u\<close>;

fun define_cond bind eq (ctxt:local_theory) =
       let
           val args = (SOME(bind,NONE,NoSyn), (Binding.empty_atts,eq),[],[])
       in def_cmd args ctxt end

fun define_inv (bind, inv) thy = 
    let val ctxt = Proof_Context.init_global thy
        val inv_parsed_term = Syntax.parse_term ctxt inv |> DOF_core.elaborate_term' ctxt
        val abs_term = Term.lambda (Free (instance_placeholderN, dummyT)) inv_parsed_term
        val eq = Logic.mk_equals (Free(Binding.name_of bind, dummyT), abs_term)
                 |> Syntax.check_term (Proof_Context.init_global thy)
    in  thy |> Named_Target.theory_map (define_cond bind eq) end

fun define_monitor_const doc_class_name bind thy = 
  let val bname = Long_Name.base_name doc_class_name
      val rex = DOF_core.rex_of doc_class_name thy
      val monitor_binding = bind |> (Binding.qualify false bname
                                     #> Binding.suffix_name monitor_suffixN)
  in
    if can hd rex
    then
      let val eq = Logic.mk_equals (Free(Binding.name_of monitor_binding, doc_class_rexp_T), hd rex) 
      in thy |> Named_Target.theory_map (define_cond monitor_binding eq) end
    else thy
  end

fun add_doc_class_cmd overloaded (raw_params, binding)
                      raw_parent raw_fieldsNdefaults reject_Atoms regexps invariants thy =
    let
      val bind_pos = Binding.pos_of binding
      val name =
        let val name = Binding.name_of binding
        in case name |> Option.filter (not o equal DOF_core.default_cid) of
                NONE => bind_pos |> ISA_core.err (name
                                                  ^ ": This name is reserved by the implementation")
             | SOME name => name
       end
      val ctxt = Proof_Context.init_global thy;
      val params = map (apsnd (Typedecl.read_constraint ctxt)) raw_params;
      val ctxt1 = fold (Variable.declare_typ o TFree) params ctxt;
      fun markup2string s = String.concat (List.filter (fn c => c <> Symbol.DEL) 
                                            (Symbol.explode (Protocol_Message.clean_output s)))
      val name' =
        case raw_parent of
            NONE => DOF_core.default_cid
          | SOME s => markup2string s |> (fn s => DOF_core.get_onto_class_name_global' s thy)
      fun cid thy = DOF_core.get_onto_class_name_global name thy
      val (parent, ctxt2) = read_parent raw_parent ctxt1;
      val parent' = case parent of
                        NONE => NONE
                      | SOME (Ts, _) => SOME (Ts, name')
      val raw_fieldsNdefaults' = filter (fn((bi,_,_),_) => Binding.name_of bi <> traceN) 
                                        raw_fieldsNdefaults
      val _ = if length raw_fieldsNdefaults' <> length raw_fieldsNdefaults 
              then warning("re-declaration of trace attribute in monitor --- ignored")
              else ()
      val raw_fieldsNdefaults'' = if  null regexps  
                                  then raw_fieldsNdefaults' 
                                  else trace_attr_ts::raw_fieldsNdefaults'
      val (fields, parsed_terms, ctxt3) = read_fields raw_fieldsNdefaults'' ctxt2;
      val fieldsNterms = (map (fn (a,b,_) => (a,b)) fields) ~~ parsed_terms
      val fieldsNterms' = map (fn ((x,y),z) => (x,y,z)) fieldsNterms
      val params' = map (Proof_Context.check_tfree ctxt3) params;
      fun check_n_filter thy (bind,ty,mf) = 
        case DOF_core.get_attribute_info name' (Binding.name_of bind) thy of
            NONE => SOME(bind,ty,mf)
          | SOME{def_occurrence,long_name,typ,...} =>
              if ty = typ 
              then (warning("overriding attribute:"
                            ^ long_name
                            ^ " in doc class:"
                            ^ def_occurrence); NONE)
              else error("no overloading allowed.")
      val record_fields = map_filter (check_n_filter thy) fields
      fun mk_eq_pair name = (Free (name, doc_class_rexp_T), doc_class_rexp_t name)
                            |> mk_meta_eq
      val args = (SOME(binding,NONE,NoSyn)
                  , (Binding.empty_atts, Binding.name_of binding |> mk_eq_pair), [], [])
      fun add record_fields invariants virtual =
        Record.add_record overloaded (params', binding) parent' record_fields
        #> (Local_Theory.notation true Syntax.mode_default RegExpInterface_Notations.notations
            |> Named_Target.theory_map)
        #> DOF_core.define_doc_class_global (params', binding) parent fieldsNterms' regexps 
                                            reject_Atoms invariants virtual
        #> (Local_Theory.notation false Syntax.mode_default RegExpInterface_Notations.notations
            |> Named_Target.theory_map)
       val invariants' = invariants |> map (apfst (Binding.qualify false name
                                                   #> Binding.suffix_name invariant_suffixN))
    in thy    (* adding const symbol representing doc-class for Monitor-RegExps.*)
           |> Named_Target.theory_map (def_cmd args)
           |> (case parent' of
                   NONE => add (DOF_core.tag_attr::record_fields) invariants' {virtual=false}
                 | SOME _  => if (not o null) record_fields
                                then add record_fields invariants' {virtual=false}
                                else add [DOF_core.tag_attr] invariants' {virtual=true})
              (* defines the ontology-checked text antiquotation to this document class *)
           |> (fn thy => OntoLinkParser.docitem_antiquotation binding (cid thy) thy)
           |> (fn thy => fold define_inv (invariants') thy)
           |> (fn thy => define_monitor_const (cid thy) binding thy)
           (* The function declare_ISA_class_accessor_and_check_instance uses a prefix
              because the class name is already bound to "doc_class Regular_Exp.rexp" constant
              by add_doc_class_cmd function *)
           |> (fn thy => ISA_core.declare_ISA_class_accessor_and_check_instance (params', cid thy, bind_pos) thy)
    end;
           

(* repackaging argument list *)
fun add_doc_class_cmd' (((overloaded, hdr), (parent, attrs)),((rejects,accept_rex),invars)) =
    (add_doc_class_cmd {overloaded = overloaded} hdr parent attrs rejects accept_rex invars)

val parse_invariants = Parse.and_list (Parse.binding --| Parse.$$$ "::" -- Parse.term)

val parse_doc_class = (Parse_Spec.overloaded 
      -- (Parse.type_args_constrained  -- Parse.binding) 
      -- (\<^keyword>\<open>=\<close>  
         |-- Scan.option (Parse.typ --| \<^keyword>\<open>+\<close>) 
          -- Scan.repeat1 (Parse.const_binding -- Scan.option (\<^keyword>\<open><=\<close> |-- Parse.term))
          )
      -- (   Scan.optional (\<^keyword>\<open>rejects\<close>    |-- Parse.enum1 "," Parse.term) []
          -- Scan.repeats   (\<^keyword>\<open>accepts\<close>    |-- (Parse.and_list Parse.term))
          -- Scan.repeats ((\<^keyword>\<open>invariant\<close>) |-- parse_invariants))
     )


val _ =
  Outer_Syntax.command \<^command_keyword>\<open>doc_class\<close> 
                       "define document class"
                        (parse_doc_class >> (Toplevel.theory o add_doc_class_cmd'));


(*just an alternative syntax*)
val _ =
  Outer_Syntax.command \<^command_keyword>\<open>onto_class\<close> 
                       "define ontological class"
                        (parse_doc_class >> (Toplevel.theory o add_doc_class_cmd'));



val clean_mixfix_sub = translate_string
  (fn "\<^sub>_" => "_"
    | "\<^sub>'" => "'"
    | c =>  c);

val prefix_sub = prefix "\<^sub>"

val convertN = "convert"

fun add_onto_morphism classes_mappings eqs thy =
  if (length classes_mappings = length eqs) then
    let
      val specs = map (fn x => (Binding.empty_atts, x)) eqs
      val converts =
        map (fn (oclasses, dclass) =>
               let
                 val oclasses_string = map Protocol_Message.clean_output oclasses
                 val dclass_string = Protocol_Message.clean_output dclass
                 val const_sub_name = dclass_string
                                      |> (oclasses_string |> fold_rev (fn x => fn y => x ^ "_" ^ y))
                                      |> String.explode |> map (fn x => "\<^sub>" ^ (String.str x)) |> String.concat
                 val convert_typ = oclasses_string |> rev |> hd
                                   |> (oclasses_string |> rev |> tl |> fold (fn x => fn y => x ^ " \<times> " ^ y))
                 val convert_typ' = convert_typ ^ " \<Rightarrow> " ^ dclass_string
                 val oclasses_sub_string = oclasses_string
                                           |> map (clean_mixfix_sub
                                                   #> String.explode
                                                   #> map (prefix_sub o String.str)
                                                   #> String.concat)
                 val mixfix = oclasses_sub_string |> rev |> hd
                              |> (oclasses_sub_string |> rev |> tl |> fold (fn x => fn y => x ^ "\<^sub>\<times>" ^ y))
                              |> ISA_core.clean_mixfix
                 val mixfix' = convertN ^ mixfix ^ "\<^sub>\<Rightarrow>"
                                ^ (dclass_string |> clean_mixfix_sub |> String.explode
                                   |> map (prefix_sub o String.str) |> String.concat)
               in SOME (Binding.name (convertN ^ const_sub_name), SOME convert_typ', Mixfix.mixfix mixfix') end)
            classes_mappings
      val args = map (fn (x, y) => (x, y, [], [])) (converts ~~ specs)
      val lthy = Named_Target.theory_init thy
      val updated_lthy = fold (fn (decl, spec, prems, params) => fn lthy => 
                        let
                          val (_, lthy') = Specification.definition_cmd decl params prems spec true lthy
                        in lthy' end) args lthy
    in Local_Theory.exit_global updated_lthy end
    (* alternative way to update the theory using the Theory.join_theory function *)
      (*val lthys = map (fn (decl, spec, prems, params) => 
                        let
                          val (_, lthy') = Specification.definition_cmd decl params prems spec true lthy
                        in lthy' end) args
      val thys = map (Local_Theory.exit_global) lthys

    in Theory.join_theory thys end*)
  else error("The number of morphisms declarations does not match the number of definitions")

fun add_onto_morphism' (classes_mappings, eqs) = add_onto_morphism classes_mappings eqs

val parse_onto_morphism = Parse.and_list
                            ((Parse.$$$ "(" |-- Parse.enum1 "," Parse.typ --| Parse.$$$ ")" --| \<^keyword>\<open>to\<close>)
                              -- Parse.typ)
                          --  (\<^keyword>\<open>where\<close> |-- Parse.and_list Parse.prop)

(* The name of the definitions must follow this rule:
   for the declaration "onto_morphism (AA, BB) to CC",
   the name of the constant must be "convert\<^sub>A\<^sub>A\<^sub>\<times>\<^sub>B\<^sub>B\<^sub>\<Rightarrow>\<^sub>C\<^sub>C". *)
val _ =
  Outer_Syntax.command \<^command_keyword>\<open>onto_morphism\<close> "define ontology morpism"
                       (parse_onto_morphism >> (Toplevel.theory o add_onto_morphism'));



end (* struct *)
\<close>  



section\<open>Shortcuts, Macros, Environments\<close>
text\<open>The features described in this section are actually \<^emph>\<open>not\<close> real ISADOF features, rather a 
slightly more abstract layer over somewhat buried standard features of the Isabelle document 
generator ... (Thanks to Makarius) Conceptually, they are \<^emph>\<open>sub-text-elements\<close>. \<close>

text\<open>This module provides mechanisms to define front-end checked:
\<^enum> \<^emph>\<open>shortcuts\<close>, i.e. machine-checked abbreviations without arguments 
  that were mapped to user-defined LaTeX code (Example: \<^verbatim>\<open>\ie\<close>)
\<^enum> \<^emph>\<open>macros\<close>  with one argument that were mapped to user-defined code. Example: \<^verbatim>\<open>\myurl{bla}\<close>.
  The argument can be potentially checked and reports can be sent to PIDE;
  if no such checking is desired, this can be expressed by setting the
  \<^theory_text>\<open>reportNtest\<close>-parameter to \<^theory_text>\<open>K(K())\<close>.
\<^enum> \<^emph>\<open>macros\<close> with two arguments, potentially independently checked. See above. 
  Example: \<^verbatim>\<open>\myurl[ding]{dong}\<close>,
\<^enum> \<^emph>\<open>boxes\<close> which are more complex sub-text-elements in the line of the \<^verbatim>\<open>verbatim\<close> or 
  \<^verbatim>\<open>theory_text\<close> environments.

Note that we deliberately refrained from a code-template definition mechanism for simplicity,
so the patterns were just described by strings.  No additional ado with quoting/unquoting 
mechanisms ... 
\<close>

ML\<open>
structure DOF_lib =
struct
fun define_shortcut name latexshcut = 
       Document_Output.antiquotation_raw name (Scan.succeed ())
          (fn _ => fn () => Latex.string latexshcut) 

(* This is a generalization of the Isabelle2020 function "control_antiquotation" from 
   document_antiquotations.ML. (Thanks Makarius!) *)
fun define_macro name s1 s2 reportNtest =
      Document_Output.antiquotation_raw_embedded name (Scan.lift Args.cartouche_input)
         (fn ctxt => 
             fn src => let val () = reportNtest ctxt src 
                       in  src |>   XML.enclose s1 s2 
                                  o Document_Output.output_document ctxt {markdown = false}
                       end);

local (* hide away really strange local construction *)
fun enclose_body2 front body1 middle body2 post =
  (if front  = "" then [] else Latex.string front) @ body1 @
  (if middle = "" then [] else Latex.string middle) @ body2 @
  (if post   = "" then [] else Latex.string post);
in
fun define_macro2 name front middle post reportNtest1 reportNtest2 =
      Document_Output.antiquotation_raw_embedded name (Scan.lift (   Args.cartouche_input 
                                                             -- Args.cartouche_input))
         (fn ctxt => 
             fn (src1,src2) => let val () = reportNtest1 ctxt src1 
                                   val () = reportNtest2 ctxt src2 
                                   val T1 = Document_Output.output_document ctxt {markdown = false} src1
                                   val T2 = Document_Output.output_document ctxt {markdown = false} src2
                               in  enclose_body2 front T1 middle T2 post
                               end);
end

fun report_text ctxt text =
    let val pos = Input.pos_of text in
       Context_Position.reports ctxt
         [(pos, Markup.language_text (Input.is_delimited text)),
          (pos, Markup.raw_text)]
    end;

fun report_theory_text ctxt text =
    let val keywords = Thy_Header.get_keywords' ctxt;
        val _ = report_text ctxt text;
        val _ =
          Input.source_explode text
          |> Token.tokenize keywords {strict = true}
          |> maps (Token.reports keywords)
          |> Context_Position.reports_text ctxt;
    in () end

fun prepare_text ctxt =
  Input.source_content #> #1 #> Document_Antiquotation.prepare_lines ctxt;
(* This also produces indent-expansion and changes space to "\_" and the introduction of "\newline",
   I believe. Otherwise its in Thy_Output.output_source, the compiler from string to LaTeX.text. *)

fun string_2_text_antiquotation ctxt text = 
        prepare_text ctxt text
        |> Document_Output.output_source ctxt
        |> Document_Output.isabelle ctxt

fun string_2_theory_text_antiquotation ctxt text =
      let
        val keywords = Thy_Header.get_keywords' ctxt;
      in
        prepare_text ctxt text
        |> Token.explode0 keywords
        |> maps (Document_Output.output_token ctxt)
        |> Document_Output.isabelle ctxt
      end

fun gen_text_antiquotation name reportNcheck compile =
  Document_Output.antiquotation_raw_embedded name (Scan.lift Parse.embedded_input)
    (fn ctxt => fn text:Input.source =>
      let
        val _ = reportNcheck ctxt text;
      in
        compile ctxt text    
      end);

fun std_text_antiquotation name (* redefined in these more abstract terms *) =
    gen_text_antiquotation name report_text string_2_text_antiquotation

fun std_theory_text_antiquotation name (* redefined in these more abstract terms *) =
    gen_text_antiquotation name report_theory_text string_2_theory_text_antiquotation

fun environment_delim name =
 ("%\n\\begin{" ^ Latex.output_name name ^ "}\n",
  "\n\\end{" ^ Latex.output_name name ^ "}");

fun environment_block name = environment_delim name |-> XML.enclose;

fun enclose_env verbatim ctxt block_env body =
  if Config.get ctxt Document_Antiquotation.thy_output_display
  then if verbatim 
       then environment_block block_env body
       else Latex.environment block_env body
  else XML.enclose ("\\inline"^block_env ^"{") "}" body;

end
\<close>


ML\<open>
local 
val parse_literal = Parse.alt_string || Parse.cartouche
val parse_define_shortcut = Parse.binding -- ((\<^keyword>\<open>\<rightleftharpoons>\<close> || \<^keyword>\<open>==\<close>) |-- parse_literal)
val define_shortcuts = fold(uncurry DOF_lib.define_shortcut)
in
val _ =  Outer_Syntax.command \<^command_keyword>\<open>define_shortcut*\<close> "define LaTeX shortcut"
            (Scan.repeat1 parse_define_shortcut >> (Toplevel.theory o define_shortcuts));
end
\<close>

ML\<open>
val parse_literal = Parse.alt_string || Parse.cartouche
val parse_define_shortcut =  Parse.binding 
                             -- ((\<^keyword>\<open>\<rightleftharpoons>\<close> || \<^keyword>\<open>==\<close>) |-- parse_literal)
                             --|Parse.underscore
                             -- parse_literal
                             -- (Scan.option (\<^keyword>\<open>(\<close> |-- Parse.ML_source --|\<^keyword>\<open>)\<close>))

fun define_macro (X,NONE) = (uncurry(uncurry(uncurry DOF_lib.define_macro)))(X,K(K()))
   |define_macro (X,SOME(_:Input.source)) = 
       let val check_code = K(K()) (* hack *)
           val _ = warning "Checker code support Not Yet Implemented - use ML"
       in  (uncurry(uncurry(uncurry DOF_lib.define_macro)))(X,check_code)
       end;

val _ =  Outer_Syntax.command \<^command_keyword>\<open>define_macro*\<close> "define LaTeX shortcut"
            (Scan.repeat1 parse_define_shortcut >> (Toplevel.theory o (fold define_macro)));

\<close>


section \<open>Document context: template and ontology\<close>

ML \<open>
signature DOCUMENT_CONTEXT =
sig
  val template_space: Context.generic -> Name_Space.T
  val ontology_space: Context.generic -> Name_Space.T
  val print_template: Context.generic -> string -> string
  val print_ontology: Context.generic -> string -> string
  val check_template: Context.generic -> xstring * Position.T -> string * (string * string)
  val check_ontology: Context.generic -> xstring * Position.T -> string * (string * string)
  val define_template: binding * (string * string) -> theory -> string * theory
  val define_ontology: binding * (string * string) -> theory -> string * theory
  val use_template: Context.generic -> xstring * Position.T -> unit
  val use_ontology: Context.generic -> (xstring * Position.T) list -> unit
  val list_ontologies: Context.generic -> unit
  val list_templates: Context.generic -> unit
end;

structure Document_Context: DOCUMENT_CONTEXT =
struct

(* theory data *)

local

structure Data = Theory_Data
(
  type T = (string * string) Name_Space.table * (string * string) Name_Space.table;
  val empty : T =
   (Name_Space.empty_table "document_template",
    Name_Space.empty_table "document_ontology");
  fun merge ((templates1, ontologies1), (templates2, ontologies2)) =
   (Name_Space.merge_tables (templates1, templates2),
    Name_Space.merge_tables (ontologies1, ontologies2));
);

fun naming_context thy =
  Proof_Context.init_global thy
  |> Proof_Context.map_naming (Name_Space.root_path #> Name_Space.add_path "Isabelle_DOF")
  |> Context.Proof;

fun get_space which = Name_Space.space_of_table o which o Data.get o Context.theory_of;

fun print which context =
  Name_Space.markup_extern (Context.proof_of context) (get_space which context)
  #> uncurry Markup.markup;

fun check which context arg =
  Name_Space.check context (which (Data.get (Context.theory_of context))) arg;

fun define (get, ap) (binding, arg) thy =
  let
    val (name, table') =
      Data.get thy |> get |> Name_Space.define (naming_context thy) true (binding, arg);
    val thy' = (Data.map o ap) (K table') thy;
  in (name, thy') end;

fun strip prfx sffx (path, pos) =
  (case try (unprefix prfx) (Path.file_name path) of
    NONE => error ("File name needs to have prefix " ^ quote prfx ^ Position.here pos)
  | SOME a =>
      (case try (unsuffix sffx) a of
        NONE => error ("File name needs to have suffix " ^ quote sffx ^ Position.here pos)
      | SOME b => b));

in


val template_space = get_space fst;
val ontology_space = get_space snd;

val print_template = print fst;
val print_ontology = print snd;

fun check_template context arg = check fst context arg ;
fun check_ontology context arg = check snd context arg ;

val define_template = define (fst, apfst);
val define_ontology = define (snd, apsnd);

fun use_template context arg =
  let val xml = arg |> check_template context |> snd |> fst  |> XML.string
  in Export.export (Context.theory_of context) \<^path_binding>\<open>dof/use_template\<close> xml end;

fun use_ontology context args =
  let
    val xml = args                                       
      |> map (fn a => check_ontology context a |> fst  )
      |> cat_lines |> XML.string;
  in Export.export (Context.theory_of context) \<^path_binding>\<open>dof/use_ontology\<close> xml end;

val strip_template = strip "root-" ".tex";
val strip_ontology = strip "DOF-" ".sty";


fun list cmdN sel which getName context = 
    let 
       fun get arg  =  check sel context arg |> snd |> snd;

       val full_names = map getName ((Name_Space.get_names o which) context)
       val descriptions = map get (map (fn n => (n, Position.none)) full_names) 
       val _ = map (fn (n,d) => writeln ((Active.sendback_markup_command (cmdN^" \""^n^"\""))^": "^d)) 
                   (ListPair.zip (full_names, descriptions))
    in ()  end

fun list_ontologies context = list "use_ontology" snd ontology_space  (fn n => ((Long_Name.base_name o Long_Name.qualifier) n )^"."^(Long_Name.base_name n)) context
fun list_templates context = list "use_template" fst template_space  Long_Name.base_name context

end;


(* Isar commands *)

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>use_template\<close>
    "use DOF document template (as defined within theory context)"
    (Parse.position Parse.name >> (fn arg =>
      Toplevel.theory (fn thy => (use_template (Context.Theory thy) arg; thy))));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>use_ontology\<close>
    "use DOF document ontologies (as defined within theory context)"
    (Parse.and_list1 (Parse.position Parse.name) >> (fn args =>
      Toplevel.theory (fn thy => (use_ontology (Context.Theory thy) args; thy))));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>define_template\<close>
    "define DOF document template (via LaTeX root file)"
    (Parse.position (Resources.provide_parse_file -- Parse.name) >>
      (fn ((get_file, desc), pos) => Toplevel.theory (fn thy =>
        let
          val (file, thy') = get_file thy;
          val binding = Binding.make (strip_template (#src_path file, pos), pos);
          val text = cat_lines (#lines file);
        in #2 (define_template (binding, (text, desc)) thy') end)));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>define_ontology\<close>
    "define DOF document ontology (via LaTeX style file)"
    (Parse.position (Resources.provide_parse_file -- Parse.name) >>
      (fn ((get_file, desc), pos) => Toplevel.theory (fn thy =>
        let
          val (file, thy') = get_file thy;
          val binding = Binding.qualify false (Long_Name.qualifier (Context.theory_long_name thy')) (Binding.make (strip_ontology (#src_path file, pos), pos));
          val text = cat_lines (#lines file);
        in #2 (define_ontology (binding, (text, desc)) thy') end)));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>list_templates\<close>
    "list available DOF document templates (as defined within theory context)"
    (Scan.succeed (Toplevel.theory (fn thy => (list_templates (Context.Theory thy); thy))));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>list_ontologies\<close>
    "list available DOF document ontologies (as defined within theory context)"
    (Scan.succeed (Toplevel.theory (fn thy => (list_ontologies (Context.Theory thy); thy))));


end;
\<close>

define_template "../latex/document-templates/root-lncs.tex" 
                "Documents using Springer's LNCS class."
define_template "../latex/document-templates/root-scrartcl.tex" 
                "A simple article layout."
define_template "../latex/document-templates/root-scrreprt-modern.tex" 
                "A 'modern' looking report layout."
define_template "../latex/document-templates/root-scrreprt.tex" 
                "A simple report layout."

section \<open>Isabelle/Scala module within session context\<close>

external_file "../etc/build.props"
external_file "../scala/dof_document_build.scala"


scala_build_generated_files
  external_files
    "build.props" (in "../etc")
  and
    "scala/dof.scala"
    "scala/dof_document_build.scala" (in "../")

end
