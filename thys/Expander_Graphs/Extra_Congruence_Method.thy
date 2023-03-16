subsection \<open>Congruence Method\<close>

text \<open>The following is a method for proving equalities of large terms by checking the equivalence
of subterms. It is possible to precisely control which operators to split by.\<close>

theory Extra_Congruence_Method
  imports 
    Main 
    "HOL-Eisbach.Eisbach"
begin

datatype cong_tag_type = CongTag

definition cong_tag_1 :: "('a \<Rightarrow> 'b) \<Rightarrow> cong_tag_type" 
  where "cong_tag_1 x = CongTag"
definition cong_tag_2 :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> cong_tag_type"
  where "cong_tag_2 x = CongTag"
definition cong_tag_3 :: "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd) \<Rightarrow> cong_tag_type" 
  where "cong_tag_3 x = CongTag"

lemma arg_cong3:
  assumes "x1 = x2" "y1 = y2" "z1 = z2"
  shows "f x1 y1 z1 = f x2 y2 z2"
  using assms by auto

method intro_cong for A :: "cong_tag_type list" uses more = 
  (match (A) in 
      "cong_tag_1 f#h" (multi) for f :: "'a \<Rightarrow> 'b" and h 
        \<Rightarrow> \<open>intro_cong h more:more arg_cong[where f="f"]\<close>
    \<bar> "cong_tag_2 f#h" (multi) for f :: "'a \<Rightarrow> 'b \<Rightarrow> 'c" and h 
        \<Rightarrow> \<open>intro_cong h more:more arg_cong2[where f="f"]\<close>
    \<bar> "cong_tag_3 f#h" (multi) for f :: "'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd" and h 
        \<Rightarrow> \<open>intro_cong h more:more arg_cong3[where f="f"]\<close>
    \<bar> _ \<Rightarrow> \<open>intro more refl\<close>)

bundle intro_cong_syntax
begin
  notation cong_tag_1 ("\<sigma>\<^sub>1")
  notation cong_tag_2 ("\<sigma>\<^sub>2")
  notation cong_tag_3 ("\<sigma>\<^sub>3")
end

bundle no_intro_cong_syntax
begin
  no_notation cong_tag_1 ("\<sigma>\<^sub>1")
  no_notation cong_tag_2 ("\<sigma>\<^sub>2")
  no_notation cong_tag_3 ("\<sigma>\<^sub>3")
end

lemma restr_Collect_cong:
  assumes "\<And>x. x \<in> A \<Longrightarrow> P x = Q x"
  shows "{x \<in> A. P x} = {x \<in> A. Q x}"
  using assms by auto

end


