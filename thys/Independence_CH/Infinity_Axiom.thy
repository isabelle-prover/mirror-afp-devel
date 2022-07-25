section\<open>The Axiom of Infinity in $M[G]$\<close>
theory Infinity_Axiom
  imports Union_Axiom Pairing_Axiom
begin
sublocale G_generic1 \<subseteq> forcing_data1
  by unfold_locales

context G_generic1 begin

interpretation mg_triv: M_trivial"##M[G]"
  using transitivity_MG zero_in_MG[of G] generic Union_MG pairing_in_MG
  by unfold_locales auto

lemma infinity_in_MG : "infinity_ax(##M[G])"
proof -
  have "\<omega> \<in> M[G]"
    using M_subset_MG one_in_G nat_in_M by auto
  moreover from this
  have "succ(y) \<in> \<omega> \<inter> M[G]" if "y \<in> \<omega>" for y
    using that transitivity_MG by blast
  ultimately
  show ?thesis
    using transitivity_MG[of 0 \<omega>]
    unfolding infinity_ax_def
    by auto
qed

end \<comment> \<open>\<^locale>\<open>G_generic1\<close>\<close>

end