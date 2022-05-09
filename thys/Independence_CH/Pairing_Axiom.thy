section\<open>The Axiom of Pairing in $M[G]$\<close>

theory Pairing_Axiom
  imports
    Names
begin

context forcing_data1
begin

lemma val_Upair :
  "\<one> \<in> G \<Longrightarrow> val(P,G,{\<langle>\<tau>,\<one>\<rangle>,\<langle>\<rho>,\<one>\<rangle>}) = {val(P,G,\<tau>),val(P,G,\<rho>)}"
  by (insert one_in_P, rule trans, subst def_val,auto)

lemma pairing_in_MG :
  assumes "M_generic(G)"
  shows "upair_ax(##M[G])"
proof -
  from assms
  have types: "\<one>\<in>G" "\<one>\<in>P" "\<one>\<in>M"
    using one_in_G one_in_M one_in_P
    by simp_all
  {
    fix x y
    note assms types
    moreover
    assume "x \<in> M[G]" "y \<in> M[G]"
    moreover from this
    obtain \<tau> \<rho> where "val(P,G,\<tau>) = x" "val(P,G,\<rho>) = y" "\<rho> \<in> M"  "\<tau> \<in> M"
      using GenExtD by blast
    moreover from types this
    have "\<langle>\<tau>,\<one>\<rangle> \<in> M" "\<langle>\<rho>,\<one>\<rangle>\<in>M"
      using pair_in_M_iff by auto
    moreover from this
    have "{\<langle>\<tau>,\<one>\<rangle>,\<langle>\<rho>,\<one>\<rangle>} \<in> M" (is "?\<sigma> \<in> _")
      using upair_in_M_iff by simp
    moreover from this
    have "val(P,G,?\<sigma>) \<in> M[G]"
      using GenExtI by simp
    moreover from calculation
    have "{val(P,G,\<tau>),val(P,G,\<rho>)} \<in> M[G]"
      using val_Upair assms one_in_G by simp
    ultimately
    have "{x,y} \<in> M[G]"
      by simp
  }
  then
  show ?thesis
    unfolding upair_ax_def upair_def by auto
qed

end \<comment> \<open>\<^locale>\<open>forcing_data1\<close>\<close>

end