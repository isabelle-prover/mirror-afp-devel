(*************************************************************************
 * Copyright (C) 
 *               2019-2022 University of Exeter 
 *               2018-2022 University of Paris-Saclay
 *               2018      The University of Sheffield
 *
 * License:
 *   This program can be redistributed and/or modified under the terms
 *   of the 2-clause BSD-style license.
 *
 *   SPDX-License-Identifier: BSD-2-Clause
 *************************************************************************)

(*<*)
theory "M_07_Implementation"
  imports "M_06_RefMan"
begin           
(*>*)


chapter*[isadof_developers::text_section]\<open>Extending \<^isadof>\<close>
text\<open>
  In this chapter, we describe the basic implementation aspects of \<^isadof>, which is based on 
  the following design-decisions:
  \<^item> the entire \<^isadof> is a ``pure add-on,'' \<^ie>, we deliberately resign to the possibility to 
    modify Isabelle itself,
  \<^item> \<^isadof> has been organized as an AFP entry and a form of an Isabelle component that is
    compatible with this goal,
  \<^item> we decided to make the markup-generation by itself to adapt it as well as possible to the 
    needs of tracking the linking in documents,
  \<^item> \<^isadof> is deeply integrated into the Isabelle's IDE (PIDE) to give immediate feedback during 
    editing and other forms of document evolution.
\<close>
text\<open>
  Semantic macros, as required by our document model, are called \<^emph>\<open>document antiquotations\<close>
  in the Isabelle literature~\<^cite>\<open>"wenzel:isabelle-isar:2020"\<close>. While Isabelle's code-antiquotations 
  are an old concept going back to Lisp and having found via SML and OCaml their ways into modern 
  proof systems, special annotation syntax inside documentation comments have their roots in 
  documentation generators such as Javadoc. Their use, however, as a mechanism to embed 
  machine-checked \<^emph>\<open>formal content\<close> is usually very limited and also lacks 
  IDE support.
\<close>

section\<open>\<^isadof>: A User-Defined Plugin in Isabelle/Isar\<close>
text\<open> 
  A plugin in Isabelle starts with defining the local data and registering it in the framework. As 
  mentioned before, contexts are structures with independent cells/compartments having three
  primitives \<^boxed_sml>\<open>init\<close>,  \<^boxed_sml>\<open>extend\<close> and  \<^boxed_sml>\<open>merge\<close>. Technically this is done by 
  instantiating a functor  \<^boxed_sml>\<open>Theory_Data\<close>, and the following fairly typical code-fragment 
  is drawn from \<^isadof>:

@{boxed_sml [display]
\<open>structure Onto_Classes = Theory_Data
  (
    type T =  onto_class Name_Space.table;
    val empty : T = Name_Space.empty_table onto_classN;
    fun merge data : T = Name_Space.merge_tables data;
  );\<close>}
  where the table  \<^boxed_sml>\<open>Name_Space.table\<close> manages
  the environment for class definitions (\<^boxed_sml>\<open>onto_class\<close>), inducing the inheritance relation,
  using a \<^boxed_sml>\<open>Name_Space\<close> table. Other tables capture, \eg, 
  the class instances, class invariants, inner-syntax antiquotations.
  Operations follow the MVC-pattern, where 
  Isabelle/Isar provides the controller part. A typical model operation has the type:

@{boxed_sml [display]
\<open>val opn :: <args_type> -> theory -> theory\<close>}
  representing a transformation on system contexts. For example, the operation of defining a class
  in the context is presented as follows:

@{boxed_sml [display]
\<open>fun add_onto_class name onto_class thy =
    thy |> Onto_Classes.map
      (Name_Space.define (Context.Theory thy) true (name, onto_class) #> #2);
\<close>}
  This code fragment uses operations from the library structure \<^boxed_sml>\<open>Name_Space\<close>
  that were used to update the appropriate table for document objects in
  the plugin-local state.
  A name space manages a collection of long names, together with a mapping
  between partially qualified external names and fully qualified internal names
  (in both directions).
  It can also keep track of the declarations and updates position of objects,
  and then allows a simple markup-generation.
  Possible exceptions to the update operation are automatically triggered.

  Finally, the view-aspects were handled by an API for parsing-combinators. The library structure 
   \<^boxed_sml>\<open>Scan\<close> provides the operators:

@{boxed_sml [display]
\<open>op ||     : ('a -> 'b) * ('a -> 'b) -> 'a -> 'b
op --     : ('a -> 'b * 'c) * ('c -> 'd * 'e) -> 'a -> ('b * 'd) * 'e
op >>     : ('a -> 'b * 'c) * ('b -> 'd) -> 'a -> 'd * 'c
op option : ('a -> 'b * 'a) -> 'a -> 'b option * 'a
op repeat : ('a -> 'b * 'a) -> 'a -> 'b list * 'a \<close>}
  for alternative, sequence, and piping, as well as combinators for option and repeat. Parsing 
  combinators have the advantage that they can be integrated into standard programs, 
  and they enable the dynamic extension of the grammar. There is a more high-level structure 
  \<^boxed_sml>\<open>Parse\<close> providing specific combinators for the command-language Isar:

@{boxed_sml [display]
\<open>val attribute = Parse.position Parse.name 
              -- Scan.optional(Parse.$$$ "=" |-- Parse.!!! Parse.name)"";
val reference = Parse.position Parse.name 
              -- Scan.option (Parse.$$$ "::" |-- Parse.!!!
                              (Parse.position Parse.name));
val attributes =(Parse.$$$ "[" |-- (reference 
               -- (Scan.optional(Parse.$$$ ","
                   |--(Parse.enum ","attribute)))[]))--| Parse.$$$ "]"              
\<close>}                                          

  The ``model'' \<^boxed_sml>\<open>create_and_check_docitem\<close> and ``new''
  \<^boxed_sml>\<open>ODL_Meta_Args_Parser.attributes\<close> parts were 
  combined via the piping operator and registered in the Isar toplevel:

@{boxed_sml [display]
\<open>val _ = 
  let fun create_and_check_docitem (((oid, pos),cid_pos),doc_attrs) 
                 = (Value_Command.Docitem_Parser.create_and_check_docitem
                          {is_monitor = false} {is_inline=true}
                          {define = false} oid pos (cid_pos) (doc_attrs))
  in  Outer_Syntax.command @{command_keyword "declare_reference*"}
                       "declare document reference"
                       (ODL_Meta_Args_Parser.attributes 
                        >> (Toplevel.theory o create_and_check_docitem))
  end;\<close>}

  Altogether, this gives the extension of Isabelle/HOL with Isar syntax and semantics for the 
  new \emph{command}:

@{boxed_theory_text [display]\<open>
declare_reference* [lal::requirement, alpha="main", beta=42]
\<close>}

  The construction also generates implicitly some markup information; for example, when hovering
  over the \<^boxed_theory_text>\<open>declare_reference*\<close> command in the IDE, a popup window with the text: 
  ``declare document reference'' will appear.
\<close>

section\<open>Programming Antiquotations\<close>
text\<open>
  The definition and registration of text antiquotations and ML-antiquotations is similar in 
  principle: based on a number of combinators, new user-defined antiquotation syntax and semantics
  can be added to the system that works on the internal plugin-data freely. For example, in

@{boxed_sml [display]
\<open>val _ = Theory.setup
         (docitem_antiquotation  @{binding "docitem"}  DOF_core.default_cid #>
            
        ML_Antiquotation.inline @{binding "docitem_value"} 
              ML_antiquotation_docitem_value)\<close>}
  the text antiquotation \<^boxed_sml>\<open>docitem\<close> is declared and bounded to a parser for the argument 
  syntax and the overall semantics. This code defines a generic antiquotation to be used in text 
  elements such as

@{boxed_theory_text [display]\<open>
text\<open>as defined in @{docitem \<open>d1\<close>} ...\<close>
\<close>}

  The subsequent registration \<^boxed_sml>\<open>docitem_value\<close> binds code to a ML-antiquotation usable 
  in an ML context for user-defined extensions; it permits the access to the current ``value'' 
  of document element, \<^ie>, a term with the entire update history.

  It is possible to generate antiquotations \emph{dynamically}, as a consequence of a class 
  definition in ODL. The processing of the ODL class \<^typ>\<open>definition\<close> also \emph{generates}
  a text antiquotation \<^boxed_theory_text>\<open>@{"definition" \<open>d1\<close>}\<close>, which works similar to 
  \<^boxed_theory_text>\<open>@{docitem \<open>d1\<close>}\<close> except for an additional type-check that assures that 
  \<^boxed_theory_text>\<open>d1\<close> is a reference to a definition. These type-checks support the subclass hierarchy.
\<close>

section\<open>Implementing Second-level Type-Checking\<close>

text\<open>
  On expressions for attribute values, for which we chose to use HOL syntax to avoid that users 
  need to learn another syntax, we implemented an own pass over type-checked terms. Stored in the 
  late-binding table \<^boxed_sml>\<open>ISA_transformer_tab\<close>, we register for each term-annotation 
  (ISA's), a function of type

@{boxed_sml [display]
\<open>   theory -> term * typ * Position.T -> term option\<close>}

  Executed in a second pass of term parsing, ISA's may just return \<^boxed_theory_text>\<open>None\<close>. This is 
  adequate for ISA's just performing some checking in the logical context \<^boxed_theory_text>\<open>theory\<close>; 
  ISA's of this kind report errors  by exceptions. In contrast, \<^emph>\<open>transforming\<close> ISA's will 
  yield a term; this is adequate, for example, by replacing a string-reference to some term denoted 
  by it. This late-binding table is also used to generate standard inner-syntax-antiquotations from 
  a \<^boxed_theory_text>\<open>doc_class\<close>.
\<close>

section\<open>Programming Class Invariants\<close>
text\<open>
  See \<^technical>\<open>sec_low_level_inv\<close>.
\<close>

section\<open>Implementing Monitors\<close>

text\<open>
  Since monitor-clauses have a regular expression syntax, it is natural to implement them as 
  deterministic automata. These are stored in the  \<^boxed_sml>\<open>docobj_tab\<close> for monitor-objects 
  in the \<^isadof> component. We implemented the functions:

@{boxed_sml [display]
\<open>  val  enabled : automaton -> env -> cid list
   val  next    : automaton -> env -> cid -> automaton\<close>}
  where \<^boxed_sml>\<open>env\<close> is basically a map between internal automaton states and class-id's 
  (\<^boxed_sml>\<open>cid\<close>'s). An automaton is said to be \<^emph>\<open>enabled\<close> for a class-id, 
  iff it either occurs in its accept-set or its reject-set (see @{docitem "sec_monitors"}). During 
  top-down document validation, whenever a text-element is encountered, it is checked if a monitor 
  is \emph{enabled} for this class; in this case, the \<^boxed_sml>\<open>next\<close>-operation is executed. The 
  transformed automaton recognizing the suffix is stored in \<^boxed_sml>\<open>docobj_tab\<close> if
  possible;
  otherwise, if \<^boxed_sml>\<open>next\<close> fails, an error is reported. The automata implementation
  is, in large parts, generated from a formalization of functional automata
  \<^cite>\<open>"nipkow.ea:functional-Automata-afp:2004"\<close>.
\<close>

section\<open>The \<^LaTeX>-Core of \<^isadof>\<close>
text\<open>
  The \<^LaTeX>-implementation of \<^isadof> heavily relies on the 
  ``keycommand''~\<^cite>\<open>"chervet:keycommand:2010"\<close> package. In fact, the core \<^isadof> \<^LaTeX>-commands
  are just wrappers for the corresponding commands from the keycommand package:

@{boxed_latex [display]
\<open>\newcommand\newisadof[1]{%
  \expandafter\newkeycommand\csname isaDof.#1\endcsname}%
\newcommand\renewisadof[1]{%
  \expandafter\renewkeycommand\csname isaDof.#1\endcsname}%
\newcommand\provideisadof[1]{%
  \expandafter\providekeycommand\csname isaDof.#1\endcsname}%\<close>}

  The \<^LaTeX>-generator of \<^isadof> maps each \<^boxed_theory_text>\<open>doc_item\<close> to an \<^LaTeX>-environment (recall
  @{docitem "text_elements"}). As generic \<^boxed_theory_text>\<open>doc_item\<close>s are derived from the text element, 
  the environment \inlineltx|isamarkuptext*| builds the core of \<^isadof>'s \<^LaTeX> implementation. 

\<close>
(*<*)
end
(*>*)
