(*  Title:       Isabelle Collections Library
    Author:      Peter Lammich <peter dot lammich at uni-muenster.de>
    Maintainer:  Peter Lammich <peter dot lammich at uni-muenster.de>
*)
header {* \isaheader{More Generic Algorithms} *}
theory Algos
imports Main "common/Misc" SetSpec MapSpec ListSpec
begin
text_raw {*\label{thy:Algos}*}
     

subsection "Injective Map to Naturals"
-- "Compute an injective map from objects into an initial 
    segment of the natural numbers"
definition map_to_nat 
  :: "('s,'x,nat \<times> 'm) iterator \<Rightarrow> 
      'm \<Rightarrow> ('x \<Rightarrow> nat \<Rightarrow> 'm \<Rightarrow> 'm) \<Rightarrow> 
      's \<Rightarrow> 'm" where
  "map_to_nat iterate1 empty2 update2 s ==
    snd (iterate1 (\<lambda>x (c,m). (c+1,update2 x c m)) s (0,empty2))
  "

-- "Whether a set is an initial segment of the natural numbers"
definition inatseg :: "nat set \<Rightarrow> bool" 
  where "inatseg s == \<exists>k. s = {i::nat. i<k}"

lemma inatseg_simps[simp]:
  "inatseg {}"
  "inatseg {0}"
  by (unfold inatseg_def)
    auto

lemma map_to_nat_correct:
  fixes \<alpha>1 :: "'s \<Rightarrow> 'x set"
  fixes \<alpha>2 :: "'m \<Rightarrow> 'x \<rightharpoonup> nat"
  assumes "set_iterate \<alpha>1 invar1 iterate1"
  assumes "map_empty \<alpha>2 invar2 empty2"
  assumes "map_update \<alpha>2 invar2 update2"

  assumes INV[simp]: "invar1 s"
  
  defines "nm == map_to_nat iterate1 empty2 update2 s"

  shows 
    -- "All elements have got a number"
    "dom (\<alpha>2 nm) = \<alpha>1 s" (is ?T1) and
    -- "No two elements got the same number"
    [rule_format]: "inj_on (\<alpha>2 nm) (\<alpha>1 s)" (is ?T2) and
    -- "Numbering is inatseg"
    [rule_format]: "inatseg (ran (\<alpha>2 nm))" (is ?T3) and
    -- "The result satisfies the map invariant"
    "invar2 nm" (is ?T4)
  proof -
      interpret s1: set_iterate \<alpha>1 invar1 iterate1 by fact
      interpret m2: map_empty \<alpha>2 invar2 empty2 by fact
      interpret m2: map_update \<alpha>2 invar2 update2 by fact

    have i_aux: "!!m S S' k v. \<lbrakk>inj_on m S; S' = insert k S; v\<notin>ran m\<rbrakk> 
                               \<Longrightarrow> inj_on (m(k\<mapsto>v)) S'"
      apply (rule inj_onI)
      apply (simp split: split_if_asm)
      apply (simp add: ran_def)
      apply (simp add: ran_def)
      apply blast
      apply (blast dest: inj_onD)
      done
    
    have "?T1 \<and> ?T2 \<and> ?T3 \<and> ?T4"
      apply (unfold nm_def map_to_nat_def)
      apply (rule_tac I="\<lambda>it (c,m). 
        invar2 m \<and> 
        dom (\<alpha>2 m) = \<alpha>1 s - it \<and> 
        inj_on (\<alpha>2 m) (\<alpha>1 s - it) \<and> 
        (ran (\<alpha>2 m) = {i. i<c})
        " in s1.iterate_rule_P)
      apply simp
      apply (simp add: m2.empty_correct)
      apply (case_tac \<sigma>)
      apply (simp add: m2.empty_correct m2.update_correct)
      apply (intro conjI)
      apply blast
      apply clarify
      apply (rule_tac m="\<alpha>2 ba" and 
                      k=x and v=aa and 
                      S'="(\<alpha>1 s - (it - {x}))" and 
                      S="(\<alpha>1 s - it)" 
                      in i_aux)
      apply auto [3]
      apply auto [1]
      apply (case_tac \<sigma>)
      apply (auto simp add: inatseg_def)
      done
    thus ?T1 ?T2 ?T3 ?T4 by auto
  qed



  subsection "Set to List(-interface)"
  subsubsection "Converting Set to List by Enqueue"
  definition it_set_to_List_enq :: "('s,'a,'f) iterator \<Rightarrow> 'f \<Rightarrow> ('a\<Rightarrow>'f\<Rightarrow>'f) \<Rightarrow> 's \<Rightarrow> 'f" 
    where "it_set_to_List_enq iterate emp enq S == iterate (\<lambda>x F. enq x F) S emp"

  lemma it_set_to_List_enq_correct: 
    assumes "set_iterate \<alpha> invar iterate" 
    assumes "list_empty \<alpha>l invarl emp"
    assumes "list_enqueue \<alpha>l invarl enq"
    assumes [simp]: "invar S"
    shows 
      "set (\<alpha>l (it_set_to_List_enq iterate emp enq S)) = \<alpha> S" (is ?T1)
      "invarl (it_set_to_List_enq iterate emp enq S)" (is ?T2)
      "distinct (\<alpha>l (it_set_to_List_enq iterate emp enq S))" (is ?T3)
  proof -
    interpret set_iterate \<alpha> invar iterate by fact
    interpret list_empty \<alpha>l invarl emp by fact
    interpret list_enqueue \<alpha>l invarl enq by fact
    have "?T1 \<and> ?T2 \<and> ?T3"
      apply (unfold it_set_to_List_enq_def)
      apply (rule_tac 
        I="\<lambda>it F. set (\<alpha>l F) = \<alpha> S - it \<and> invarl F \<and> distinct (\<alpha>l F)" 
        in iterate_rule_P)
      apply (auto simp add: enqueue_correct empty_correct)
      done
    thus ?T1 ?T2 ?T3 by auto
  qed

  subsubsection "Converting Set to List by Push"
  definition it_set_to_List_push :: "('s,'a,'f) iterator \<Rightarrow> 'f \<Rightarrow> ('a\<Rightarrow>'f\<Rightarrow>'f) \<Rightarrow> 's \<Rightarrow> 'f" 
    where "it_set_to_List_push iterate emp push S == iterate (\<lambda>x F. push x F) S emp"

  lemma it_set_to_List_push_correct: 
    assumes "set_iterate \<alpha> invar iterate" 
    assumes "list_empty \<alpha>l invarl emp"
    assumes "list_push \<alpha>l invarl push"
    assumes [simp]: "invar S"
    shows 
      "set (\<alpha>l (it_set_to_List_push iterate emp push S)) = \<alpha> S" (is ?T1)
      "invarl (it_set_to_List_push iterate emp push S)" (is ?T2)
      "distinct (\<alpha>l (it_set_to_List_push iterate emp push S))" (is ?T3)
  proof -
    interpret set_iterate \<alpha> invar iterate by fact
    interpret list_empty \<alpha>l invarl emp by fact
    interpret list_push \<alpha>l invarl push by fact
    have "?T1 \<and> ?T2 \<and> ?T3"
      apply (unfold it_set_to_List_push_def)
      apply (rule_tac 
        I="\<lambda>it F. set (\<alpha>l F) = \<alpha> S - it \<and> invarl F \<and> distinct (\<alpha>l F)" 
        in iterate_rule_P)
      apply (auto simp add: push_correct empty_correct)
      done
    thus ?T1 ?T2 ?T3 by auto
  qed


end
