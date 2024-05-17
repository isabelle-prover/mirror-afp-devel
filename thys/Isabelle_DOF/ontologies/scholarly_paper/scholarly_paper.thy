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

chapter\<open>An example ontology for scientific, MINT-oriented papers.\<close>

theory scholarly_paper
  imports "Isabelle_DOF.Isa_COL"
  keywords "author*" "abstract*"                                :: document_body
    and    "Proposition*" "Definition*" "Lemma*" "Theorem*"     :: document_body 
    and    "Premise*" "Corollary*" "Consequence*" "Conclusion*" :: document_body
    and    "Assumption*" "Hypothesis*" "Assertion*"             :: document_body
    and    "Proof*" "Example*"                                  :: document_body
begin

define_ontology "DOF-scholarly_paper.sty" "Writing academic publications."

text\<open>Scholarly Paper provides a number of standard text - elements for scientific papers.
They were introduced in the following.\<close>

section\<open>General Paper Structuring Elements\<close>
doc_class title =
   short_title :: "string option"  <=  "None"
    
doc_class subtitle =
   abbrev ::      "string option"  <=  "None"
   
(* adding a contribution list and checking that it is cited as well in tech as in conclusion. ? *)

doc_class author =
   email       :: "string" <= "''''"
   http_site   :: "string" <= "''''"
   orcid       :: "string" <= "''''"
   affiliation :: "string"


doc_class abstract =
   keywordlist        :: "string list"   <= "[]" 
   principal_theorems :: "thm list"


ML\<open>
val _ =
  Monitor_Command_Parser.document_command \<^command_keyword>\<open>abstract*\<close> "Textual Definition"
    {markdown = true, body = true}
    (Onto_Macros.enriched_document_cmd_exp (SOME "abstract") []) [] I;

val _ =
  Monitor_Command_Parser.document_command \<^command_keyword>\<open>author*\<close> "Textual Definition"
    {markdown = true, body = true}
    (Onto_Macros.enriched_document_cmd_exp (SOME "author") []) [] I;
\<close>

text\<open>Scholarly Paper is oriented towards the classical domains in science:
\<^enum> mathematics
\<^enum> informatics
\<^enum> natural sciences
\<^enum> technology (= engineering)

which we formalize into:\<close>

doc_class text_section = text_element +
   main_author :: "author option"  <=  None
   fixme_list  :: "string list"    <=  "[]" 
   level       :: "int  option"    <=  "None"
   (* this attribute enables doc-notation support section* etc.
      we follow LaTeX terminology on levels 
                part          = Some -1
                chapter       = Some 0
                section       = Some 1
                subsection    = Some 2
                subsubsection = Some 3
       ... *)
   (* for scholarly paper: invariant level > 0 *)


doc_class "conclusion" = text_section +
   main_author :: "author option"  <=  None
   invariant level    :: "(level \<sigma>) \<noteq> None \<and> the (level \<sigma>) > 0"
   
doc_class related_work = "conclusion" +
   main_author :: "author option"  <=  None
   invariant level    :: "(level \<sigma>) \<noteq> None \<and> the (level \<sigma>) > 0"

doc_class bibliography = text_section +
   style       :: "string option"  <=  "Some ''LNCS''"
   invariant level    :: "(level \<sigma>) \<noteq> None \<and> the (level \<sigma>) > 0"

doc_class annex = "text_section" +
   main_author :: "author option"  <=  None
   invariant level    :: "(level \<sigma>) \<noteq> None \<and> the (level \<sigma>) > 0"

find_consts name:"scholarly_paper.*Leeee"

(*
datatype sc_dom = math | info | natsc | eng 
*)


doc_class introduction = text_section +
   comment :: string
   claims  :: "thm list"
   invariant level    :: "(level \<sigma>) \<noteq> None \<and> the (level \<sigma>) > 0"

text\<open>Technical text-elements posses a status: they can be either an \<^emph>\<open>informal explanation\<close> /
description or a kind of introductory text to definition etc. or a \<^emph>\<open>formal statement\<close> similar
to :

\<^bold>\<open>Definition\<close> 3.1: Security. 
As Security of the system we define etc...

A formal statement can, but must not have a reference to true formal Isabelle/Isar definition. 
\<close>

doc_class background = text_section +
   comment :: string
   claims  :: "thm list"
   invariant level    :: "(level \<sigma>) \<noteq> None \<and> the (level \<sigma>) > 0"


section\<open>Technical Content and Free-form Semi-formal Formats\<close>

datatype status = formal | semiformal | description

text\<open>The class \<^verbatim>\<open>technical\<close> regroups a number of text-elements that contain typical 
"technical content" in mathematical or engineering papers: definitions, theorems, lemmas, examples.  \<close>

(* OPEN PROBLEM: connection between referentiable and status. This should be explicit 
   and computable. *)


doc_class technical = text_section +
   definition_list :: "string list" <=  "[]"
   status          :: status <= "description"
   formal_results  :: "thm list"
   invariant level  :: "(level \<sigma>) \<noteq> None \<and> the (level \<sigma>) > 0"

type_synonym tc = technical (* technical content *)


text \<open>This a \<open>doc_class\<close> of \<^verbatim>\<open>examples\<close> in the broadest possible sense : they are \emph{not}
necessarily considered as technical content, but may occur in an article. 
Note that there are \<open>doc_class\<close>es of \<^verbatim>\<open>math_example\<close>s and \<^verbatim>\<open>tech_example\<close>s which 
follow a more specific regime of mathematical or engineering content.
\<close>
(* An example for the need of multiple inheritance on classes ? *)

doc_class example  = text_section + 
   referentiable   :: bool <= True
   status          :: status <= "description"
   short_name      :: string <= "''''"
   invariant level    :: "(level \<sigma>) \<noteq> None \<and> the (level \<sigma>) > 0"

text\<open>The intended use for the \<open>doc_class\<close>es \<^verbatim>\<open>math_motivation\<close> (or \<^verbatim>\<open>math_mtv\<close> for short),
     \<^verbatim>\<open>math_explanation\<close> (or \<^verbatim>\<open>math_exp\<close> for short) and 
     \<^verbatim>\<open>math_example\<close> (or \<^verbatim>\<open>math_ex\<close> for short)
     are \<^emph>\<open>informal\<close> descriptions of semi-formal definitions (by inheritance).
     Math-Examples can be made referentiable triggering explicit, numbered presentations.\<close>
doc_class math_motivation  = technical +  
   referentiable :: bool <= False
type_synonym math_mtv = math_motivation

doc_class math_explanation  = technical +
   referentiable :: bool <= False
type_synonym math_exp = math_explanation


subsection\<open>Freeform Mathematical Content\<close>

text\<open>We follow in our enumeration referentiable mathematical content class the AMS style and its
provided \<^emph>\<open>theorem environments\<close> (see \<^verbatim>\<open>texdoc amslatex\<close>). We add, however, the concepts 
\<^verbatim>\<open>axiom\<close>, \<^verbatim>\<open>rule\<close> and \<^verbatim>\<open>assertion\<close> to the list. A particular advantage of \<^verbatim>\<open>texdoc amslatex\<close> is 
that it is well-established and compatible with many LaTeX - styles.

The names for thhe following key's are deliberate non-standard abbreviations in order to avoid
future name clashes.\<close>

datatype math_content_class = 
    "defn"       \<comment>\<open>definition\<close> 
  | "axm"        \<comment>\<open>axiom\<close>
  | "theom"      \<comment>\<open>theorem\<close> 
  | "lemm"       \<comment>\<open>lemma\<close>
  | "corr"       \<comment>\<open>corollary\<close>
  | "prpo"       \<comment>\<open>proposition\<close>
  | "rulE"       \<comment>\<open>rule\<close>
  | "assn"       \<comment>\<open>assertion\<close>    
  | "hypt"      \<comment>\<open>hypothesis\<close>    
  | "assm"       \<comment>\<open>assumption\<close>
  | "prms"       \<comment>\<open>premise\<close>  
  | "cons"       \<comment>\<open>consequence\<close>
  | "conc_stmt"  \<comment>\<open>math. conclusion\<close>
  | "prf_stmt"   \<comment>\<open>math. proof\<close>
  | "expl_stmt"  \<comment>\<open>math. example\<close> 
  | "rmrk"       \<comment>\<open>remark\<close>  
  | "notn"       \<comment>\<open>notation\<close>  
  | "tmgy"       \<comment>\<open>terminology\<close>

text\<open>Instances of the \<open>doc_class\<close> \<^verbatim>\<open>math_content\<close> are by definition @{term "semiformal"}; they may
be non-referential, but in this case they will not have a @{term "short_name"}.\<close>

doc_class math_content = technical +
   referentiable :: bool <= False
   short_name    :: string <= "''''"
   status        :: status <= "semiformal"
   mcc           :: "math_content_class" <= "theom" 
   invariant s1  :: "\<not>referentiable \<sigma> \<longrightarrow> short_name \<sigma> = ''''"
   invariant s2  :: "technical.status \<sigma> = semiformal"
type_synonym math_tc = math_content

text\<open>The class \<^typ>\<open>math_content\<close> is perhaps more adequaltely described as "math-alike content".
Sub-classes can englobe instances such as:
\<^item> terminological definitions such as:
  \<open>Definition*[assessor::sfc, short_name="''assessor''"]\<open>entity that carries out an assessment\<close>\<close>
\<^item> free-form mathematical definitions such as:
  \<open>Definition*[process_ordering, short_name="''process ordering''"]\<open>
   We define \<open>P \<sqsubseteq> Q \<equiv> \<psi>\<^sub>\<D> \<and> \<psi>\<^sub>\<R> \<and> \<psi>\<^sub>\<M> \<close>,  where \<^vs>\<open>-0.2cm\<close>
   1) \<^vs>\<open>-0.2cm\<close> \<open>\<psi>\<^sub>\<D> = \<D> P \<supseteq> \<D> Q \<close>
   2) ...
   \<close>\<close>
\<^item> semi-formal descriptions, which are free-form mathematical definitions on which finally
  an attribute with a formal Isabelle definition is attached. \<close>


text\<open>Instances of the Free-form Content are Definition, Lemma, Assumption, Hypothesis, etc.
     The key class definitions are inspired by the AMS style, to which some target LaTeX's compile.\<close>   

text\<open>A proposition (or: "sentence") is a central concept in philosophy of language and related 
fields, often characterized as the primary bearer of truth or falsity. Propositions are also often 
characterized as being the kind of thing that declarative sentences denote. \<close>

doc_class "proposition"  = math_content +
   referentiable :: bool <= True
   level         :: "int option"         <= "Some 2"
   mcc           :: "math_content_class" <= "prpo" 
   invariant d  :: "mcc \<sigma> = prpo" (* can not be changed anymore. *)

text\<open>A definition is used to give a precise meaning to a new term, by describing a 
condition which unambiguously qualifies what a mathematical term is and is not. Definitions and 
axioms form the basis on which all of modern mathematics is to be constructed.\<close>
doc_class "definition"  = math_content +
   referentiable :: bool <= True
   level         :: "int option"         <= "Some 2"
   mcc           :: "math_content_class" <= "defn" 
   invariant d  :: "mcc \<sigma> = defn" (* can not be changed anymore. *)

doc_class "axiom"  = math_content +
   referentiable :: bool <= True
   level         :: "int option"         <= "Some 2"
   mcc           :: "math_content_class" <= "axm" 
   invariant d  :: "mcc \<sigma> = axm" (* can not be changed anymore. *)

text\<open>A lemma (plural lemmas or lemmata) is a generally minor, proven proposition which is used as 
a stepping stone to a larger result. For that reason, it is also known as a "helping theorem" or an 
"auxiliary theorem". In many cases, a lemma derives its importance from the theorem it aims to prove.\<close>
doc_class "lemma"       = math_content +
   referentiable :: bool <= "True"
   level         :: "int option"         <= "Some 2"
   mcc           :: "math_content_class" <= "lemm" 
   invariant d  :: "mcc \<sigma> = lemm"

doc_class "theorem"     = math_content +
   referentiable :: bool <= True
   level         :: "int option"         <= "Some 2"
   mcc           :: "math_content_class" <= "theom" 
   invariant d  :: "mcc \<sigma> = theom"

text\<open>A corollary is a theorem of less importance which can be readily deduced from a previous, 
more notable lemma or theorem. A corollary could, for instance, be a proposition which is incidentally 
proved while proving another proposition.\<close>
doc_class "corollary"   = math_content +
   referentiable :: bool <= "True"
   level         :: "int option"         <= "Some 2"
   mcc           :: "math_content_class" <= "corr" 
   invariant d  :: "mcc \<sigma> = corr"


text\<open>A premise or premiss[a] is a proposition — a true or false declarative statement—
     used in an argument to prove the truth of another proposition called the conclusion.\<close>
doc_class "premise"     = math_content +
   referentiable :: bool <= "True"
   level         :: "int option"         <= "Some 2"
   mcc           :: "math_content_class" <= "prms" 
   invariant d  :: "mcc \<sigma> = prms"

text\<open>A consequence describes the relationship between statements that hold true when one statement 
logically follows from one or more statements. A valid logical argument is one in which the 
conclusion is entailed by the premises, because the conclusion is the consequence of the premises. 
The philosophical analysis of logical consequence involves the questions: In what sense does a 
conclusion follow from its premises?\<close>
doc_class "consequence" = math_content +
   referentiable :: bool <= "True"
   level         :: "int option"         <= "Some 2"
   mcc           :: "math_content_class" <= "cons" 
   invariant d  :: "mcc \<sigma> = cons"

doc_class "conclusion_stmt" = math_content +   \<comment> \<open>not to confuse with a section element: Conclusion\<close>
   referentiable :: bool <= "True"
   level         :: "int option"         <= "Some 2"
   mcc           :: "math_content_class" <= "conc_stmt" 
   invariant d  :: "mcc \<sigma> = conc_stmt"

text\<open>An assertion is a statement that asserts that a certain premise is true.\<close>
doc_class "assertion"   = math_content +
   referentiable :: bool <= "True"
   level         :: "int option"         <= "Some 2"
   mcc           :: "math_content_class" <= "assn" 
   invariant d  :: "mcc \<sigma> = assn"

text\<open>An assumption is an explicit or a tacit proposition about the world or a background belief 
relating to an proposition.\<close>
doc_class "assumption"  = math_content +
   referentiable :: bool <= "True"
   level         :: "int option"         <= "Some 2"
   mcc           :: "math_content_class" <= "assm" 
   invariant d  :: "mcc \<sigma> = assm"

text\<open> A working hypothesis is a provisionally accepted hypothesis proposed for further research
 in a process beginning with an educated guess or thought.

 A different meaning of the term hypothesis is used in formal logic, to denote the antecedent of a 
 proposition; thus in the proposition "If \<open>P\<close>, then \<open>Q\<close>", \<open>P\<close> denotes the hypothesis (or antecedent); 
 \<open>Q\<close> can be called a consequent. \<open>P\<close> is the assumption in a (possibly counterfactual) What If question.\<close>
doc_class "hypothesis"  = math_content +
   referentiable :: bool <= "True"
   level         :: "int option"         <= "Some 2"
   mcc           :: "math_content_class" <= "hypt" 
   invariant d :: "mcc \<sigma> = hypt"

doc_class "math_proof"  = math_content +
   referentiable :: bool <= "True"
   level         :: "int option"         <= "Some 2"
   mcc           :: "math_content_class" <= "prf_stmt" 
   invariant d :: "mcc \<sigma> = prf_stmt"

doc_class "math_example"= math_content +
   referentiable :: bool <= "True"
   level         :: "int option"         <= "Some 2"
   mcc           :: "math_content_class" <= "expl_stmt" 
   invariant d :: "mcc \<sigma> = expl_stmt"



subsection\<open>Support of Command Macros \<^verbatim>\<open>Definition*\<close> , \<^verbatim>\<open>Lemma**\<close>, \<^verbatim>\<open>Theorem*\<close> ... \<close>

text\<open>These ontological macros allow notations are defined for the class 
  \<^typ>\<open>math_content\<close> in order to allow for a variety of free-form formats;
  in order to provide specific sub-classes, default options can be set
  in order to support more succinct notations and avoid constructs
  such as :

  \<^theory_text>\<open>Definition*[l::"definition"]\<open>...\<close>\<close>.

  Instead, the more convenient global declaration 
  \<^theory_text>\<open>declare[[Definition_default_class="definition"]]\<close>
  supports subsequent abbreviations:

    \<^theory_text>\<open>Definition*[l]\<open>...\<close>\<close>.

  Via the default classes, it is also possible to specify the precise concept
  that are not necessarily in the same inheritance hierarchy: for example:
  \<^item> mathematical definition vs terminological setting
  \<^item> mathematical example vs. technical example. 
  \<^item> mathematical proof vs. some structured argument
  \<^item> mathematical hypothesis vs. philosophical/metaphysical assumption
  \<^item> ... 

By setting the default classes, it is possible to reuse these syntactic support and give them
different interpretations in an underlying ontological class-tree.

\<close>

ML\<open>

val (Proposition_default_class, Proposition_default_class_setup) 
     = Attrib.config_string \<^binding>\<open>Proposition_default_class\<close> (K "");
val (Definition_default_class, Definition_default_class_setup) 
     = Attrib.config_string \<^binding>\<open>Definition_default_class\<close> (K "");
val (Axiom_default_class, Axiom_default_class_setup) 
     = Attrib.config_string \<^binding>\<open>Axiom_default_class\<close> (K "");
val (Lemma_default_class, Lemma_default_class_setup) 
     = Attrib.config_string \<^binding>\<open>Lemma_default_class\<close> (K "");
val (Theorem_default_class, Theorem_default_class_setup) 
     = Attrib.config_string \<^binding>\<open>Theorem_default_class\<close> (K "");
val (Corollary_default_class, Corollary_default_class_setup) 
     = Attrib.config_string \<^binding>\<open>Corollary_default_class\<close> (K "");
val (Assumption_default_class, Assumption_default_class_setup) 
     = Attrib.config_string \<^binding>\<open>Assumption_default_class\<close> (K "");
val (Assertion_default_class, Assertion_default_class_setup) 
     = Attrib.config_string \<^binding>\<open>Assertion_default_class\<close> (K "");
val (Consequence_default_class, Consequence_default_class_setup) 
     = Attrib.config_string \<^binding>\<open>Consequence_default_class\<close> (K "");
val (Conclusion_default_class, Conclusion_default_class_setup) 
     = Attrib.config_string \<^binding>\<open>Conclusion_default_class\<close> (K "");
val (Premise_default_class, Premise_default_class_setup) 
     = Attrib.config_string \<^binding>\<open>Premise_default_class\<close> (K "");
val (Hypothesis_default_class, Hypothesis_default_class_setup) 
     = Attrib.config_string \<^binding>\<open>Hypothesis_default_class\<close> (K "");
val (Proof_default_class, Proof_default_class_setup) 
     = Attrib.config_string \<^binding>\<open>Proof_default_class\<close> (K "");
val (Example_default_class, Example_default_class_setup) 
     = Attrib.config_string \<^binding>\<open>Example_default_class\<close> (K "");
val (Remark_default_class, Remark_default_class_setup) 
     = Attrib.config_string \<^binding>\<open>Remark_default_class\<close> (K "");
val (Notation_default_class, Notation_default_class_setup) 
     = Attrib.config_string \<^binding>\<open>Notation_default_class\<close> (K "");

\<close>

setup\<open>   Proposition_default_class_setup 
      #> Definition_default_class_setup 
      #> Axiom_default_class_setup 
      #> Lemma_default_class_setup 
      #> Theorem_default_class_setup 
      #> Corollary_default_class_setup 
      #> Assertion_default_class_setup 
      #> Assumption_default_class_setup 
      #> Premise_default_class_setup 
      #> Hypothesis_default_class_setup
      #> Consequence_default_class_setup 
      #> Conclusion_default_class_setup 
      #> Proof_default_class_setup 
      #> Remark_default_class_setup 
      #> Example_default_class_setup\<close>

ML\<open> 
local open ODL_Meta_Args_Parser in

local 
fun doc_cmd kwd txt flag key = 
    Monitor_Command_Parser.document_command kwd txt {markdown = true, body = true}
    (fn meta_args => fn thy =>
      let
        val ddc = Config.get_global thy flag 
        val default = SOME(((ddc = "") ? (K \<^const_name>\<open>math_content\<close>)) ddc)
      in
        Onto_Macros.enriched_formal_statement_command  default [("mcc",key)] meta_args thy
      end)
      [\<^const_name>\<open>mcc\<close>]
      (Onto_Macros.transform_attr [(\<^const_name>\<open>mcc\<close>,key)])

in

val _ = doc_cmd \<^command_keyword>\<open>Definition*\<close> "Freeform Definition" 
                Definition_default_class \<^const_name>\<open>defn\<close>;

val _ = doc_cmd \<^command_keyword>\<open>Lemma*\<close>      "Freeform Lemma Description" 
                 Lemma_default_class \<^const_name>\<open>lemm\<close>;

val _ = doc_cmd \<^command_keyword>\<open>Theorem*\<close>    "Freeform Theorem" 
                 Theorem_default_class \<^const_name>\<open>theom\<close>;

val _ = doc_cmd \<^command_keyword>\<open>Proposition*\<close> "Freeform Proposition"
                  Proposition_default_class \<^const_name>\<open>prpo\<close>;

val _ = doc_cmd \<^command_keyword>\<open>Premise*\<close> "Freeform Premise"
                  Premise_default_class \<^const_name>\<open>prms\<close>;

val _ = doc_cmd \<^command_keyword>\<open>Corollary*\<close> "Freeform Corollary"
                  Corollary_default_class \<^const_name>\<open>corr\<close>;

val _ = doc_cmd \<^command_keyword>\<open>Consequence*\<close> "Freeform Consequence"
                  Consequence_default_class \<^const_name>\<open>cons\<close>;
                      
val _ = doc_cmd \<^command_keyword>\<open>Conclusion*\<close> "Freeform Conclusion"
                  Conclusion_default_class \<^const_name>\<open>conc_stmt\<close>;
                           
val _ = doc_cmd \<^command_keyword>\<open>Assumption*\<close> "Freeform Assumption"
                  Assumption_default_class \<^const_name>\<open>assm\<close>;

val _ = doc_cmd \<^command_keyword>\<open>Hypothesis*\<close> "Freeform Hypothesis"
                  Hypothesis_default_class \<^const_name>\<open>prpo\<close>;

val _ = doc_cmd \<^command_keyword>\<open>Assertion*\<close> "Freeform Assertion"
                  Assertion_default_class \<^const_name>\<open>assn\<close>;

val _ = doc_cmd \<^command_keyword>\<open>Proof*\<close> "Freeform Proof"
                  Proof_default_class \<^const_name>\<open>prf_stmt\<close>;

val _ = doc_cmd \<^command_keyword>\<open>Example*\<close> "Freeform Example"
                  Example_default_class \<^const_name>\<open>expl_stmt\<close>;
end
end 
\<close>


subsection\<open>Formal Mathematical Content\<close>
text\<open>While this library is intended to give a lot of space to freeform text elements in
order to counterbalance Isabelle's standard view, it should not be forgot that the real strength
of Isabelle is its ability to handle both - and to establish links between both worlds. Therefore:\<close>

doc_class math_formal  = math_content +
   referentiable :: bool <= False
   status        :: status <= "formal"
   properties    :: "term list"
type_synonym math_fc = math_formal



subsubsection*[ex_ass::example]\<open>Logical Assertions\<close>

text\<open>Logical assertions allow for logical statements to be checked in the global context). \<close>

assert*[ass1::assertion, short_name = "\<open>This is an assertion\<close>"] \<open>(3::int) < 4\<close>


subsection\<open>Content in Engineering/Tech Papers \<close>
text\<open>This section is currently experimental and not supported by the documentation 
     generation backend.\<close>

doc_class engineering_content = technical +
   short_name :: string <= "''''"
   status     :: status
type_synonym eng_content = engineering_content


doc_class "experiment"  = engineering_content +
   tag :: "string" <=  "''''"

doc_class "evaluation"  = engineering_content +
   tag :: "string" <=  "''''"

doc_class "data"  = engineering_content +
   tag :: "string" <=  "''''"

doc_class tech_definition = engineering_content +
   referentiable :: bool <= True
   tag :: "string" <=  "''''"

doc_class tech_code = engineering_content +
   referentiable :: bool <= True
   tag :: "string" <=  "''''"

doc_class tech_example = engineering_content +
   referentiable :: bool <= True
   tag :: "string" <=  "''''"

doc_class eng_example = engineering_content +
   referentiable :: bool <= True
   tag :: "string" <=  "''''"


subsection\<open>Some Summary\<close>

print_doc_classes

print_doc_class_template "definition" (* just a sample *)
print_doc_class_template "lemma" (* just a sample *)
print_doc_class_template "theorem" (* just a sample *)
print_doc_class_template "premise" (* just a sample *)


subsection\<open>Structuring Enforcement in Engineering/Math Papers \<close>
(* todo : could be finer *)

text\<open> Besides subtyping, there is another relation between
doc\_classes: a class can be a \<^emph>\<open>monitor\<close> to other ones,
which is expressed by occurrence in the where clause.
While sub-classing refers to data-inheritance of attributes,
a monitor captures structural constraints -- the order --
in which instances of monitored classes may occur.

The control of monitors is done by the commands:
\<^item> \<^verbatim>\<open> monitor <oid::class_type, <attributes-defs> > \<close>
\<^item> \<^verbatim>\<open> close_monitor <oid[::class_type],<attributes-updates>> \<close>

where the automaton of the monitor class is expected
to be in a final state.

Monitors can be nested.

Classes neither directly or  indirectly (via inheritance)
mentioned in the monitor clause are \<^emph>\<open>independent\<close> from
the monitor and may occur freely, \ie{} in arbitrary order.n \<close>


text \<open>underlying idea: a monitor class automatically receives a  
    \<^verbatim>\<open>trace\<close> attribute in which a list of observed class-ids is maintained.
    The \<^verbatim>\<open>trace\<close> is a \<^emph>\<open>`predefined id`\<close> like \<^verbatim>\<open>main\<close> in C. It can be accessed
    like any other attribute of a class instance, \ie{} a document item.\<close>

doc_class article = 
   style_id :: string                <= "''LNCS''"
   version  :: "(int \<times> int \<times> int)"  <= "(0,0,0)"
   accepts "(title                   ~~ 
            \<lbrakk>subtitle\<rbrakk>                ~~
            \<lbrace>author\<rbrace>\<^sup>+                 ~~ 
            abstract                  ~~
            \<lbrace>introduction\<rbrace>\<^sup>+           ~~ 
            \<lbrace>background\<rbrace>\<^sup>*             ~~ 
            \<lbrace>technical || example || float \<rbrace>\<^sup>+      ~~
            \<lbrace>conclusion\<rbrace>\<^sup>+             ~~  
            bibliography              ~~
            \<lbrace>annex\<rbrace>\<^sup>* )"


ML\<open>
structure Scholarly_paper_trace_invariant =
struct 
local

fun group _ _ _ [] = []
   |group f g cidS (a::S) = case find_first (f a) cidS of
                            NONE => [a] :: group f g cidS S
                          | SOME cid => let val (pref,suff) =  chop_prefix  (g cid) S
                                        in (a::pref)::(group f g cidS suff) end;

fun partition ctxt cidS trace = 
    let fun find_lead (x,_) = DOF_core.is_subclass ctxt x;
        fun find_cont cid (cid',_) =  DOF_core.is_subclass ctxt cid' cid
    in group find_lead find_cont cidS trace end;

fun dest_option _ (Const (@{const_name "None"}, _)) = NONE
  | dest_option f (Const (@{const_name "Some"}, _) $ t) = SOME (f t)

in 

fun check ctxt cidS mon_id pos_opt =
    let val trace  = AttributeAccess.compute_trace_ML ctxt mon_id pos_opt @{here}
        val groups = partition (Context.proof_of ctxt) cidS trace
        fun get_level_raw oid = ISA_core.compute_attr_access ctxt "level" oid NONE @{here};
        fun get_level oid = dest_option (snd o HOLogic.dest_number) (get_level_raw (oid));
        fun check_level_hd a = case (get_level (snd a)) of
                                  NONE => error("Invariant violation: leading section " ^ snd a ^ 
                                                " must have lowest level")
                                | SOME X => X
        fun check_group_elem level_hd a = case (get_level (snd a)) of
                                              NONE => true
                                            | SOME y => if level_hd <= y then true
                                                        (* or < ? But this is too strong ... *)
                                                        else error("Invariant violation: "^
                                                                   "subsequent section " ^ snd a ^ 
                                                                   " must have higher level.");
        fun check_group [] = true
           |check_group [_] = true
           |check_group (a::S) = forall (check_group_elem (check_level_hd a)) (S)
    in if forall check_group groups then () 
       else error"Invariant violation: leading section must have lowest level" 
    end
end

end
\<close>

setup\<open>
(fn thy => 
let val cidS = ["scholarly_paper.introduction","scholarly_paper.technical", 
                       "scholarly_paper.example", "scholarly_paper.conclusion"];
    fun body moni_oid _ ctxt = (Scholarly_paper_trace_invariant.check ctxt cidS moni_oid NONE; true)
    val ctxt = Proof_Context.init_global thy
    val cid = "article"
    val binding = DOF_core.binding_from_onto_class_pos cid thy
    val cid_long = DOF_core.get_onto_class_name_global cid thy
in  DOF_core.add_ml_invariant binding (DOF_core.make_ml_invariant (body, cid_long)) thy end)
\<close>

term\<open>float\<close>
section\<open>Miscelleous\<close>

subsection\<open>Common Abbreviations\<close>

define_shortcut* eg  \<rightleftharpoons> \<open>\eg\<close>  (* Latin: „exempli gratia“  meaning  „for example“. *)
                 ie  \<rightleftharpoons> \<open>\ie\<close>  (* Latin: „id est“  meaning „that is to say“. *)
                 etc \<rightleftharpoons> \<open>\etc\<close> (* Latin : „et cetera“ meaning „et cetera“ *)

print_doc_classes

end

