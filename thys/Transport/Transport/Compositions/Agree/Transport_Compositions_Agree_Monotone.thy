\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Monotonicity\<close>
theory Transport_Compositions_Agree_Monotone
  imports
    Transport_Compositions_Agree_Base
begin

context transport_comp_agree
begin

lemma mono_wrt_rel_leftI:
  assumes "((\<le>\<^bsub>L1\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R1\<^esub>)) l1" "((\<le>\<^bsub>L2\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R2\<^esub>)) l2"
  and "\<And>x y. x \<le>\<^bsub>L1\<^esub> y \<Longrightarrow> l1 x \<le>\<^bsub>R1\<^esub> l1 y \<Longrightarrow> l1 x \<le>\<^bsub>L2\<^esub> l1 y"
  shows "((\<le>\<^bsub>L\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R\<^esub>)) l"
  unfolding left_eq_comp using assms by (rule dep_mono_wrt_rel_compI)

end

context transport_comp_same
begin

lemma mono_wrt_rel_leftI:
  assumes "((\<le>\<^bsub>L1\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R1\<^esub>)) l1" "((\<le>\<^bsub>R1\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R2\<^esub>)) l2"
  shows "((\<le>\<^bsub>L\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R\<^esub>)) l"
  using assms by (rule mono_wrt_rel_leftI) auto

end


end