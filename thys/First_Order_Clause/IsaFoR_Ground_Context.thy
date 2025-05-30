theory IsaFoR_Ground_Context
  imports 
    Generic_Context 
    "Regular_Tree_Relations.Ground_Terms"
    Ground_Critical_Peaks
begin

type_synonym 'f ground_context = "('f, 'f gterm) actxt"

abbreviation apply_ground_context (\<open>_\<langle>_\<rangle>\<^sub>G\<close> [1000, 0] 1000) where
  "C\<langle>s\<rangle>\<^sub>G \<equiv> GFun\<langle>C;s\<rangle>"

interpretation ground_context: "context" where
  hole = \<box> and 
  apply_context = apply_ground_context and 
  compose_context = actxt_compose
proof unfold_locales
  fix c :: "'f ground_context" and t t' 
  assume "c\<langle>t\<rangle>\<^sub>G = c\<langle>t'\<rangle>\<^sub>G" 

  then show "t = t'"
    by (induction c) auto
qed (simp_all add: intp_actxt_compose)

end
