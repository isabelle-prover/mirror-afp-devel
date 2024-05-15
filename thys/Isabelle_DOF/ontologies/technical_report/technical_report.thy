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

section\<open>An example ontology for a scholarly paper\<close>

theory technical_report
   imports "Isabelle_DOF.scholarly_paper"
begin              

define_ontology "DOF-technical_report.sty" "Writing technical reports."

(* for reports paper: invariant: level \<ge> -1 *)

section\<open>More Global Text Elements for Reports\<close>

doc_class table_of_contents =
   bookmark_depth :: int <= 3
   depth          :: int <= 3

doc_class front_matter = 
   front_matter_style :: string    (* TODO Achim :::: *)

doc_class index =
   kind  :: "doc_class" 
   level :: "int option"

section\<open>Code Statement Elements\<close>

doc_class "code"     = technical +
   checked :: bool     <=  "False"
   caption :: "string" <=  "''''"

typ code

text\<open>The \<^doc_class>\<open>code\<close> is a general stub for free-form and type-checked code-fragments such as:
        \<^enum> SML code                                
        \<^enum> bash code
        \<^enum> isar code (although this might be an unwanted concurrence 
          to the Isabelle standard cartouche)
        \<^enum> C code.

It is intended that later refinements of this "stub" as done in \<^verbatim>\<open>Isabelle_C\<close> which come with their
own content checking and presentation styles. 
\<close>

doc_class "SML"     = code +
   checked :: bool <=  "False"

doc_class "ISAR"     = code +
   checked :: bool <=  "False"

doc_class "LATEX"     = code +
   checked :: bool <=  "False"

print_doc_class_template "SML" (* just a sample *)


doc_class report = 
   style_id :: string                <= "''LNCS''"
   version  :: "(int \<times> int \<times> int)"  <= "(0,0,0)"
   accepts "(title                 ~~ 
           \<lbrakk>subtitle\<rbrakk>              ~~
           \<lbrace>author\<rbrace>\<^sup>+               ~~ 
           \<lbrakk>front_matter\<rbrakk>          ~~
           abstract                ~~
           \<lbrakk>table_of_contents\<rbrakk>     ~~
           \<lbrace>introduction\<rbrace>\<^sup>+         ~~ 
           \<lbrace>background\<rbrace>\<^sup>*           ~~ 
           \<lbrace>technical || example || float \<rbrace>\<^sup>+ ~~ 
           \<lbrace>conclusion\<rbrace>\<^sup>+           ~~  
           bibliography            ~~ 
           \<lbrakk>index\<rbrakk> ~~ \<lbrace>annex\<rbrace>\<^sup>*   )"


section\<open>Experimental\<close>

(* switch on regexp syntax *)
notation Star  ("\<lbrace>(_)\<rbrace>\<^sup>*" [0]100)
notation Plus  (infixr "||" 55)
notation Times (infixr "~~" 60)
notation Atom  ("\<lfloor>_\<rfloor>" 65)



text\<open>Not a terribly deep theorem, but an interesting property of consistency between
ontologies - so, a lemma that shouldn't break if the involved ontologies were changed.
It reads as follows: 
"The structural language of articles should be included in the structural language of
reports, that is to say, reports should just have a richer structure than ordinary papers." \<close>

theorem articles_sub_reports: \<open>Lang article_monitor \<subseteq> Lang report_monitor\<close>
  unfolding article_monitor_def report_monitor_def
  apply(rule regexp_seq_mono[OF subset_refl] | rule seq_cancel_opt | rule subset_refl)+ 
  done

text\<open>The proof proceeds by blindly applying the monotonicity rules 
     on the language of regular expressions.\<close>

text\<open>All Class-Id's --- should be generated.\<close>

lemmas class_ids =
             SML_def code_def annex_def  title_def figure_def chapter_def  article_def theorem_def 
             paragraph_def tech_code_def assumption_def   definition_def  hypothesis_def 
             eng_example_def text_element_def math_content_def tech_example_def subsubsection_def  
             engineering_content_def data_def float_def axiom_def LATEX_def author_def listing_def 
             abstract_def assertion_def technical_def background_def evaluation_def math_proof_def 
             math_formal_def bibliography_def math_example_def text_section_def conclusion_stmt_def
             math_explanation_def ISAR_def frame_def lemma_def index_def report_def section_def 
             subtitle_def corollary_def subsection_def conclusion_def experiment_def consequence_def
             proposition_def introduction_def related_work_def front_matter_def math_motivation_def
             example_def table_of_contents_def tech_definition_def premise_def




definition allClasses 
  where \<open>allClasses \<equiv> 
             {SML, code, annex, title,figure,chapter, article, theorem, paragraph,
              tech_code, assumption, definition, hypothesis, eng_example, text_element,
              math_content,tech_example, subsubsection,tech_definition,
              engineering_content,data,float,axiom,LATEX,author,listing, example,abstract,
              assertion,technical,background,evaluation,math_proof,math_formal,bibliography,
              math_example,text_section,conclusion_stmt,math_explanation,ISAR,frame,
              lemma,index,report,section,premise,subtitle,corollary,subsection,conclusion,
              experiment, consequence,proposition,introduction,related_work,front_matter,
              math_motivation,table_of_contents}\<close>

text\<open>A rudimentary fragment of the class hierarchy re-modeled on classid's :\<close>


definition cid_of where \<open>cid_of = inv Regular_Exp.Atom\<close>

lemma Atom_inverse[simp]:\<open>cid_of (Regular_Exp.Atom a) = a\<close>
  unfolding cid_of_def by (meson UNIV_I f_inv_into_f image_eqI rexp.inject(1))



definition doc_class_rel
  where  \<open>doc_class_rel \<equiv> {(cid_of proposition,cid_of math_content),
                            (cid_of listing,cid_of float),
                            (cid_of figure,cid_of float)} \<close>

instantiation "doc_class" :: ord
begin

definition
  less_eq_doc_class: "x \<le> y \<longleftrightarrow> (x,y) \<in> doc_class_rel\<^sup>*"

definition
  less_doc_class: "(x::doc_class) < y \<longleftrightarrow> (x \<le> y \<and> \<not> y \<le> x)"

instance .. 

end

lemma drc_acyclic : "acyclic doc_class_rel"
  proof -
        let ?measure = "(\<lambda>x.3::int)(cid_of float := 0, cid_of math_content := 0, 
                                    cid_of listing := 1, cid_of figure := 1, cid_of proposition := 1)"
  show ?thesis
        unfolding doc_class_rel_def
        apply(rule acyclicI_order [where f = "?measure"])
        by(simp only: class_ids)(auto)
  qed


instantiation "doc_class" :: order
begin
instance 
   proof 
     fix x::"doc_class"
     show \<open>x \<le> x\<close>   
       unfolding less_eq_doc_class by simp
   next
     fix x y z:: "doc_class"
     show \<open>x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z\<close>
       unfolding less_eq_doc_class
       by force
   next
     fix x y::"doc_class"
     have * : "antisym (doc_class_rel\<^sup>*)" 
       by (simp add: acyclic_impl_antisym_rtrancl drc_acyclic)    
     show \<open>x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y\<close>
       apply(insert antisymD[OF *])
       using less_eq_doc_class by auto
   next
     fix x y::"doc_class"
     show \<open>(x < y) = (x \<le> y \<and> \<not> y \<le> x)\<close> 
       by(simp add: less_doc_class)
   qed
end

theorem articles_Lsub_reports: \<open>(L\<^sub>s\<^sub>u\<^sub>b article_monitor) \<subseteq> L\<^sub>s\<^sub>u\<^sub>b report_monitor\<close>
  unfolding article_monitor_def report_monitor_def
  by (meson order_refl regexp_seq_mono' seq_cancel_opt')


end
