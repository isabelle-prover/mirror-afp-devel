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
theory 
  "M_04_Document_Ontology"
  imports 
    "M_03_GuidedTour"
  keywords "class_synonym" :: thy_defn
begin

(*>*)


(*<*)
definition combinator1 :: "'a \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'b" (infixl "|>" 65)
  where "x |> f = f x"


ML\<open>
local
val _ =
  Outer_Syntax.local_theory \<^command_keyword>\<open>class_synonym\<close> "declare type abbreviation"
    (Parse.type_args -- Parse.binding --
      (\<^keyword>\<open>=\<close> |-- Parse.!!! (Parse.typ -- Parse.opt_mixfix'))
      >> (fn ((args, a), (rhs, mx)) => snd o Typedecl.abbrev_cmd (a, args, mx) rhs));

in end
\<close>

(*>*)


(*<*)

doc_class "title"  = short_title :: "string option" <= "None"


doc_class elsevier =
  organization :: string
  address_line :: string
  postcode :: int
  city :: string
  
(*doc_class elsevier_affiliation = affiliation +*) 

doc_class acm =
  position :: string
  institution :: string
  department :: int
  street_address :: string
  city :: string
  state :: int
  country :: string
  postcode :: int

(*doc_class acm_affiliation = affiliation +*)

doc_class lncs =
  institution :: string

(*doc_class lncs_affiliation = affiliation +*)


doc_class author =
    name        :: string
    email       :: "string"   <= "''''"
    invariant ne_name :: "name \<sigma> \<noteq> ''''"

doc_class elsevier_author = "author" +
  affiliations :: "elsevier list"
  short_author :: string
  url :: string
  footnote :: string

text*[el1:: "elsevier"]\<open>\<close>
(*text*[el_aff1:: "affiliation", journal_style = "@{elsevier \<open>el1\<close>}"]\<open>\<close>*)
term*\<open>@{elsevier \<open>el1\<close>}\<close>
text*[el_auth1:: "elsevier_author", affiliations = "[@{elsevier \<open>el1\<close>}]"]\<open>\<close>

doc_class acm_author = "author" +
  affiliations :: "acm list"
  orcid :: int
  footnote :: string

text*[acm1:: "acm"]\<open>\<close>
(*text*[acm_aff1:: "acm affiliation", journal_style = "@{acm \<open>acm1\<close>}"]\<open>\<close>*)
text*[acm_auth1:: "acm_author", affiliations = "[@{acm \<open>acm1\<close>}]"]\<open>\<close>

doc_class lncs_author = "author" +
  affiliations :: "lncs list"
  orcid :: int
  short_author :: string
  footnote :: string

text*[lncs1:: "lncs"]\<open>\<close>
(*text*[lncs_aff1:: "lncs affiliation", journal_style = "@{lncs \<open>lncs1\<close>}"]\<open>\<close>*)
text*[lncs_auth1:: "lncs_author", affiliations = "[@{lncs \<open>lncs1\<close>}]"]\<open>\<close>


doc_class  "text_element" =
    authored_by :: "author set"  <= "{}"
    level       :: "int  option"  <= "None"
    invariant authors_req :: "authored_by \<sigma> \<noteq> {}" 
    and       level_req   :: "the (level \<sigma>) > 1"

doc_class "introduction" = "text_element" +
    authored_by :: "(author) set"  <= "UNIV"

doc_class  "technical" = "text_element" +
    formal_results  :: "thm list"

doc_class "definition" = "technical" +
    is_formal   :: "bool"

doc_class "theorem" = "technical" +
    is_formal   :: "bool"
    assumptions :: "term list"        <= "[]"
    statement   :: "term option"      <= "None"

doc_class "conclusion" = "text_element" +
    resumee     :: "(definition set \<times> theorem set)"
    invariant is_form :: "(\<exists>x\<in>(fst (resumee \<sigma>)). definition.is_formal x) \<longrightarrow> 
                  (\<exists>y\<in>(snd (resumee \<sigma>)). is_formal y)"

text*[def::"definition", is_formal = "True"]\<open>\<close>
text*[theo::"theorem", is_formal = "False"]\<open>\<close>
text*[conc::"conclusion", resumee="({@{definition \<open>def\<close>}}, {@{theorem \<open>theo\<close>}})"]\<open>\<close>

value*\<open>resumee @{conclusion \<open>conc\<close>} |> fst\<close>
value*\<open>resumee @{conclusion \<open>conc\<close>} |> snd\<close>

doc_class "article" =
    style_id    :: string   <= "''LNCS''"
    accepts "(title ~~ \<lbrace>author\<rbrace>\<^sup>+ ~~ \<lbrace>introduction\<rbrace>\<^sup>+  
             ~~ \<lbrace>\<lbrace>definition ~~ example\<rbrace>\<^sup>+ || theorem\<rbrace>\<^sup>+ ~~ \<lbrace>conclusion\<rbrace>\<^sup>+)"


datatype kind = expert_opinion | argument | "proof"

onto_class  result = " technical" +
  evidence :: kind
  property :: " theorem list" <= "[]"
  invariant has_property :: "evidence \<sigma> = proof \<longleftrightarrow> property \<sigma> \<noteq> []"

(*>*)

text*[paper_m::float, main_caption="\<open>A Basic Document Ontology: paper$^m$\<close>"]\<open>
 @{boxed_theory_text [display,indent=5] 
   \<open>doc_class "title"  = short_title :: "string option" <= "None"
doc_class affiliation =
  journal_style :: '\<alpha>
doc_class author =
    affiliations :: "'\<alpha> affiliation list"
    name        :: string
    email       :: "string"   <= "''''"
    invariant ne_name :: "name \<sigma> \<noteq> ''''"
doc_class "text_element" =
    authored_by :: "('\<alpha> author) set"  <= "{}"
    level       :: "int  option"  <= "None"
    invariant authors_req :: "authored_by \<noteq> {}" 
    and        level_req    :: "the (level) > 1"
doc_class "introduction" = text_element +
    authored_by :: "('\<alpha> author) set"  <= "UNIV"
doc_class "technical" = text_element +
    formal_results  :: "thm list"
doc_class "definition" = technical +
    is_formal   :: "bool"
doc_class "theorem" = technical +
    assumptions :: "term list"        <= "[]"
    statement   :: "term option"      <= "None"
doc_class "conclusion" = text_element +
    resumee     :: "(definition set \<times> theorem set)"
    invariant (\<forall>x\<in>fst resumee. is_formal x)
                  \<longrightarrow> (\<exists>y\<in>snd resumee. is_formal y)
doc_class "article" = 
    style_id    :: string   <= "''LNCS''"
    accepts "(title ~~ \<lbrace>author\<rbrace>\<^sup>+ ~~ \<lbrace>introduction\<rbrace>\<^sup>+  
             ~~ \<lbrace>\<lbrace>definition ~~ example\<rbrace>\<^sup>+ || theorem\<rbrace>\<^sup>+ ~~ \<lbrace>conclusion\<rbrace>\<^sup>+)"\<close>}
\<close>


(*<*)
datatype role =  PM     \<comment> \<open>Program Manager\<close>
              |  RQM    \<comment> \<open>Requirements Manager\<close> 
              |  DES    \<comment> \<open>Designer\<close>
              |  IMP    \<comment> \<open>Implementer\<close> 
              |  ASR    \<comment> \<open>Assessor\<close> 
              |  INT    \<comment> \<open>Integrator\<close> 
              |  TST    \<comment> \<open>Tester\<close>
              |  VER    \<comment> \<open>Verifier\<close>
              |  VnV    \<comment> \<open>Verification and Validation\<close>
              |  VAL    \<comment> \<open>Validator\<close>

abbreviation developer where "developer ==   DES"
abbreviation validator where "validator ==   VAL"
abbreviation verifier where "verifier ==   VER"

doc_class requirement = Isa_COL.text_element +
  long_name :: "string option"
  is_concerned :: "role set"

text*[req1::requirement,
      is_concerned="{developer, validator}"]
\<open>The operating system shall provide secure
memory separation.\<close>

text\<open>
The recurring issue of the certification
is @{requirement \<open>req1\<close>} ...\<close>

term "\<lparr>long_name = None,is_concerned = {developer,validator}\<rparr>"
(*>*)

(*<*)
end
(*>*)
