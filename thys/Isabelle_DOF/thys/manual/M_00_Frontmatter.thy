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

(*<*)
theory "M_00_Frontmatter"
  imports 
    "Isabelle_DOF.technical_report"
begin
 
use_template "scrreprt-modern"
use_ontology "technical_report"

section\<open>Local Document Setup.\<close>
text\<open>Introducing document specific abbreviations and macros:\<close>

define_shortcut* dof     \<rightleftharpoons> \<open>\dof\<close>
                 isadof  \<rightleftharpoons> \<open>\isadof{}\<close>

define_shortcut* TeXLive \<rightleftharpoons> \<open>\TeXLive\<close>
                 BibTeX  \<rightleftharpoons> \<open>\BibTeX{}\<close> 
                 LaTeX   \<rightleftharpoons> \<open>\LaTeX{}\<close>
                 TeX     \<rightleftharpoons> \<open>\TeX{}\<close>
                 dofurl  \<rightleftharpoons> \<open>\dofurl\<close>
                 pdf     \<rightleftharpoons> \<open>PDF\<close>

text\<open>Note that these setups assume that the associated \<^LaTeX> macros 
     are defined, \<^eg>, in the document prelude. \<close>

define_macro* index     \<rightleftharpoons> \<open>\index{\<close> _ \<open>}\<close>
define_macro* bindex    \<rightleftharpoons> \<open>\bindex{\<close> _ \<open>}\<close>
define_macro* nolinkurl \<rightleftharpoons> \<open>\nolinkurl{\<close> _ \<open>}\<close>
define_macro* center    \<rightleftharpoons> \<open>\center{\<close> _ \<open>}\<close>
define_macro* ltxinline \<rightleftharpoons> \<open>\inlineltx|\<close> _ \<open>|\<close>

ML\<open>

fun boxed_text_antiquotation name (* redefined in these more abstract terms *) =
    DOF_lib.gen_text_antiquotation name DOF_lib.report_text 
                           (fn ctxt => DOF_lib.string_2_text_antiquotation ctxt
                                       #> DOF_lib.enclose_env false ctxt "isarbox")

val neant = K(Latex.text("",\<^here>))

fun boxed_theory_text_antiquotation name (* redefined in these more abstract terms *) =
    DOF_lib.gen_text_antiquotation name DOF_lib.report_theory_text 
                           (fn ctxt => DOF_lib.string_2_theory_text_antiquotation ctxt 
                                        #> DOF_lib.enclose_env false ctxt "isarbox"
                                        (* #> neant *)) (*debugging *)

fun boxed_sml_text_antiquotation name  =
    DOF_lib.gen_text_antiquotation name (K(K())) 
                           (fn ctxt => Input.source_content 
                                        #> Latex.text 
                                        #> DOF_lib.enclose_env true ctxt "sml") 
                           (* the simplest conversion possible *)

fun boxed_pdf_antiquotation name =
    DOF_lib.gen_text_antiquotation name (K(K())) 
                           (fn ctxt => Input.source_content 
                                        #> Latex.text 
                                        #> DOF_lib.enclose_env true ctxt "out") 
                           (* the simplest conversion possible *)

fun boxed_latex_antiquotation name =
    DOF_lib.gen_text_antiquotation name (K(K())) 
                           (fn ctxt => Input.source_content 
                                        #> Latex.text 
                                        #> DOF_lib.enclose_env true ctxt "ltx") 
                           (* the simplest conversion possible *)

fun boxed_bash_antiquotation name =
    DOF_lib.gen_text_antiquotation name (K(K())) 
                           (fn ctxt => Input.source_content 
                                        #> Latex.text 
                                        #> DOF_lib.enclose_env true ctxt "bash") 
                           (* the simplest conversion possible *)
\<close>

setup\<open>boxed_text_antiquotation         \<^binding>\<open>boxed_text\<close> #>
      boxed_text_antiquotation         \<^binding>\<open>boxed_cartouche\<close> #>
      boxed_theory_text_antiquotation  \<^binding>\<open>boxed_theory_text\<close> #>

      boxed_sml_text_antiquotation     \<^binding>\<open>boxed_sml\<close> #>
      boxed_pdf_antiquotation          \<^binding>\<open>boxed_pdf\<close> #>
      boxed_latex_antiquotation        \<^binding>\<open>boxed_latex\<close>#>
      boxed_bash_antiquotation         \<^binding>\<open>boxed_bash\<close> 
     \<close>

open_monitor*[this::report] 

(*>*)

title*[title::title]         \<open>Isabelle/DOF\<close> 
subtitle*[subtitle::subtitle]\<open>User and Implementation Manual\<close> 
author*[  adb,
          email       ="\<open>a.brucker@exeter.ac.uk\<close>",
          orcid       ="\<open>0000-0002-6355-1200\<close>",
          http_site   ="\<open>https://www.brucker.ch/\<close>",
          affiliation ="\<open>University of Exeter, Exeter, UK\<close>"]\<open>Achim D. Brucker\<close>
author*[  nico,
          email       = "\<open>nicolas.meric@lri.fr\<close>",
          affiliation = "\<open>Université Paris-Saclay, LRI, Paris, France\<close>"]\<open>Nicolas Méric\<close>
author*[  bu,
          email       = "\<open>wolff@lri.fr\<close>",
          affiliation = "\<open>Université Paris-Saclay, LRI, Paris, France\<close>"]\<open>Burkhart Wolff\<close>
 
abstract*[abs, keywordlist="[\<open>Ontology\<close>, \<open>Ontological Modeling\<close>, \<open>Document Management\<close>, 
                             \<open>Formal Document Development\<close>,\<open>Isabelle/DOF\<close>]"]
\<open>   \<^isadof> provides an implementation of \<^dof> on top of Isabelle/HOL. 
    \<^dof> itself is a novel framework for \<^emph>\<open>defining\<close> ontologies
    and \<^emph>\<open>enforcing\<close> them during document development and document
    evolution. \<^isadof> targets use-cases such as mathematical texts referring
    to a theory development or technical reports requiring a particular structure.
    A major application of \<^dof> is the integrated development of
    formal certification documents (\<^eg>, for Common Criteria or CENELEC
    50128) that require consistency across both formal and informal
    arguments.

    \<^isadof> is integrated into Isabelle's IDE, which
    allows for smooth ontology development as well as immediate
    ontological feedback during the editing of a document.
    Its checking facilities leverage the collaborative 
    development of documents required to be consistent with an
    underlying ontological structure.
    
    In this user-manual, we give an in-depth presentation of the design
    concepts of \<^dof>'s Ontology Definition Language (ODL) and describe
    comprehensively its major commands. Many examples show typical best-practice
    applications of the system.
  
    It is a unique feature of  \<^isadof>  that ontologies may be used to control
    the link between formal and informal content in documents inan automatic-checked way. 
    These links can connect both text elements and formal
    modeling elements such as terms, definitions, code  and logical formulas,
    altogether \<^emph>\<open>integrated\<close> into a state-of-the-art interactive theorem prover.

\<close>

(*<*) 
end
(*>*) 
  
