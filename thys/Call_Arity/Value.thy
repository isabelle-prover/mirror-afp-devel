theory "Value"
  imports "~~/src/HOL/HOLCF/HOLCF"
begin

subsubsection {* The semantic domain for values and environments *}

domain Value = Fn (lazy "Value \<rightarrow> Value") | B (lazy "bool discr")

fixrec Fn_project :: "Value \<rightarrow> Value \<rightarrow> Value"
 where "Fn_project\<cdot>(Fn\<cdot>f) = f"

abbreviation Fn_project_abbr (infix "\<down>Fn" 55)
  where "f \<down>Fn v \<equiv> Fn_project\<cdot>f\<cdot>v"

lemma [simp]: "\<bottom> \<down>Fn x = \<bottom>"
  by (fixrec_simp)

fixrec B_project :: "Value \<rightarrow> Value \<rightarrow> Value \<rightarrow> Value" where
  "B_project\<cdot>(B\<cdot>db)\<cdot>v\<^sub>1\<cdot>v\<^sub>2 = (if undiscr db then v\<^sub>1 else v\<^sub>2)"

lemma [simp]:
  "B_project\<cdot>(B\<cdot>(Discr b))\<cdot>v\<^sub>1\<cdot>v\<^sub>2 = (if b then v\<^sub>1 else v\<^sub>2)"
  "B_project\<cdot>\<bottom>\<cdot>v\<^sub>1\<cdot>v\<^sub>2 = \<bottom>"
  "B_project\<cdot>(Fn\<cdot>f)\<cdot>v\<^sub>1\<cdot>v\<^sub>2 = \<bottom>"
by fixrec_simp+


end
