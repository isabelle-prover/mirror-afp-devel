section\<open>The Axiom of Pairing in $M[G]$\<close>

theory Pairing_Axiom
  imports
    Names
begin

context G_generic1
begin

lemma val_Upair :
  "\<one> \<in> G \<Longrightarrow> val(G,{\<langle>\<tau>,\<one>\<rangle>,\<langle>\<rho>,\<one>\<rangle>}) = {val(G,\<tau>),val(G,\<rho>)}"
  by (rule trans, subst def_val,auto)

lemma pairing_in_MG : "upair_ax(##M[G])"
proof -
  {
    fix x y
    assume "x \<in> M[G]" "y \<in> M[G]"
    moreover from this
    obtain \<tau> \<rho> where "val(G,\<tau>) = x" "val(G,\<rho>) = y" "\<rho> \<in> M"  "\<tau> \<in> M"
      using GenExtD by blast
    moreover from this
    have "\<langle>\<tau>,\<one>\<rangle> \<in> M" "\<langle>\<rho>,\<one>\<rangle>\<in>M"
      using pair_in_M_iff by auto
    moreover from this
    have "{\<langle>\<tau>,\<one>\<rangle>,\<langle>\<rho>,\<one>\<rangle>} \<in> M" (is "?\<sigma> \<in> _")
      using upair_in_M_iff by simp
    moreover from this
    have "val(G,?\<sigma>) \<in> M[G]"
      using GenExtI by simp
    moreover from calculation
    have "{val(G,\<tau>),val(G,\<rho>)} \<in> M[G]"
      using val_Upair one_in_G by simp
    ultimately
    have "{x,y} \<in> M[G]"
      by simp
  }
  then
  show ?thesis
    unfolding upair_ax_def upair_def by auto
qed

end \<comment> \<open>\<^locale>\<open>G_generic1\<close>\<close>

end