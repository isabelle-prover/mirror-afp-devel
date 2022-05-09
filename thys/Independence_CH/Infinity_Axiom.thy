section\<open>The Axiom of Infinity in $M[G]$\<close>
theory Infinity_Axiom
  imports Separation_Axiom Union_Axiom Pairing_Axiom
begin

context G_generic1 begin

interpretation mg_triv: M_trivial"##M[G]"
  using transitivity_MG zero_in_MG generic Union_MG pairing_in_MG
  by unfold_locales auto

lemma infinity_in_MG : "infinity_ax(##M[G])"
proof -
  from infinity_ax
  obtain I where "I\<in>M" "0 \<in> I" "\<forall>y\<in>M. y \<in> I \<longrightarrow> succ(y) \<in> I"
    unfolding infinity_ax_def  by auto
  then
  have "check(I) \<in> M"
    using check_in_M by simp
  then
  have "I\<in> M[G]"
    using valcheck generic one_in_G one_in_P GenExtI[of "check(I)" G] by simp
  moreover from this \<open>I\<in>M[G]\<close> \<open>\<forall>y\<in>M. y \<in> I \<longrightarrow> succ(y) \<in> I\<close>
  have "succ(y) \<in> I \<inter> M[G]" if "y \<in> I" for y
    using that transitivity_MG transitivity[OF _ \<open>I\<in>M\<close>] by blast
  moreover
  note \<open>0\<in>I\<close>
  ultimately
  show ?thesis
    using transitivity_MG[of _ I]
    unfolding infinity_ax_def
    by auto
qed

end \<comment> \<open>\<^locale>\<open>G_generic1\<close>\<close>

end