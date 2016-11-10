(* Author: Alexander Bentkamp, Universität des Saarlandes
*)
section \<open>Missing Lemmas of VS\_Connect\<close>

theory DL_Missing_VS_Connect
imports "../Jordan_Normal_Form/VS_Connect" DL_Missing_Vector_Space
begin


lemma (in vec_space) fin_dim_span:
assumes "finite A" "A \<subseteq> carrier V"
shows "vectorspace.fin_dim F (vs (span A))"
proof -
  have "vectorspace F (span_vs A)" 
   using assms span_is_subspace subspace_def subspace_is_vs by simp
  have "A \<subseteq> span A" using assms in_own_span by simp 
  have "submodule F (span A) V" using assms span_is_submodule by simp 
  have "LinearCombinations.module.span F (vs (span A)) A = carrier (vs (span A))"
    using  span_li_not_depend(1)[OF `A \<subseteq> span A` `submodule F (span A) V`] by auto
  then show ?thesis unfolding vectorspace.fin_dim_def[OF `vectorspace F (span_vs A)`]
    using List.finite_set \<open>A \<subseteq> span A\<close> \<open>vectorspace F (vs (span A))\<close> 
    vec_vs vectorspace.carrier_vs_is_self[OF `vectorspace F (span_vs A)`] using assms(1) by auto
qed

lemma (in vec_space) fin_dim_span_cols:
assumes "A \<in> carrier\<^sub>m n nc"
shows "vectorspace.fin_dim F (vs (span (set (cols A))))"
using fin_dim_span cols_dim List.finite_set assms mat_carrierD(1) vec_module_simps(3) by force


end
