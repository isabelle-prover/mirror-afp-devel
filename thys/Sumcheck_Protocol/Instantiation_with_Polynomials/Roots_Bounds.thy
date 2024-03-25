(*******************************************************************************

  Project: Sumcheck Protocol

  Authors: Azucena Garvia Bosshard <zucegb@gmail.com>
           Christoph Sprenger, ETH Zurich <sprenger@inf.ethz.ch>
           Jonathan Bootle, IBM Research Europe <jbt@zurich.ibm.com>

*******************************************************************************)

section \<open>Roots Bound for Multivariate Polynomials of Arity at Most One\<close>

theory Roots_Bounds
  imports 
    "Polynomials.MPoly_Type_Univariate"
    Univariate_Roots_Bound
begin

text \<open>
\textbf{NOTE:} if considered to be useful enough, the lemmas in this theory could be moved to 
the theory @{theory "Polynomials.MPoly_Type_Univariate"}.
\<close>

subsection \<open>Lemmas connecting univariate and multivariate polynomials\<close>

subsubsection \<open>Basic lemmas\<close>

lemma mpoly_to_poly_zero_iff:
  fixes p::"'a::comm_monoid_add mpoly"
  assumes \<open>vars p \<subseteq> {v}\<close>  
  shows "mpoly_to_poly v p = 0 \<longleftrightarrow> p = 0"
  by (metis assms mpoly_to_poly_inverse poly_to_mpoly0 poly_to_mpoly_inverse)

lemma keys_monom_subset_vars:
  fixes p::"'a::zero mpoly"
  assumes \<open>m \<in> keys (mapping_of p)\<close> 
  shows "keys m \<subseteq> vars p" 
  using assms 
  by (auto simp add: vars_def)

lemma sum_lookup_keys_eq_lookup:
  fixes p::"'a::zero mpoly"
  assumes \<open>m \<in> keys (mapping_of p)\<close> and \<open>vars p \<subseteq> {v}\<close> 
  shows "sum (lookup m) (keys m) = lookup m v"
  using assms
  by (auto simp add: subset_singleton_iff dest!: keys_monom_subset_vars)


subsubsection \<open>Total degree corresponds to degree for polynomials of arity at most one\<close>

lemma poly_degree_eq_mpoly_degree:
  fixes p::"'a::comm_monoid_add mpoly"
  assumes \<open>vars p \<subseteq> {v}\<close>
  shows "degree (mpoly_to_poly v p) = MPoly_Type.degree p v"
  using assms
proof - 
  have *: "\<And>n. MPoly_Type.coeff p (Poly_Mapping.single v n) \<noteq> 0 
               \<longleftrightarrow> (\<exists>m\<in>keys (mapping_of p). n = lookup m v)"  
    by (metis (no_types, opaque_lifting) Diff_eq_empty_iff Diff_insert add_0 keys_eq_empty 
              keys_monom_subset_vars lookup_single_eq remove_key_keys remove_key_sum 
              singleton_insert_inj_eq' coeff_keys[symmetric] assms)

  have "degree (mpoly_to_poly v p) 
      = Max (insert 0 {n. MPoly_Type.coeff p (Poly_Mapping.single v n) \<noteq> 0})" 
    by (simp add: poly_degree_eq_Max_non_zero_coeffs) 
  also have "\<dots> = MPoly_Type.degree p v"
    by (simp add: degree.rep_eq image_def *)
  finally show ?thesis .
qed

lemma mpoly_degree_eq_total_degree:
  fixes p::"'a::zero mpoly"
  assumes \<open>vars p \<subseteq> {v}\<close>
  shows "MPoly_Type.degree p v = total_degree p"
  using assms
  by (auto simp add: MPoly_Type.degree_def total_degree_def sum_lookup_keys_eq_lookup)

corollary poly_degree_eq_total_degree:
  fixes p::"'a::comm_monoid_add mpoly"
  assumes \<open>vars p \<subseteq> {v}\<close>
  shows "degree (mpoly_to_poly v p) = total_degree p"
  using assms
  by (simp add: poly_degree_eq_mpoly_degree mpoly_degree_eq_total_degree)  


subsection \<open>Roots bound for univariate polynomials of type @{typ "'a mpoly"}\<close>

lemma univariate_mpoly_roots_bound: 
  fixes p::"'a::idom mpoly"
  assumes \<open>vars p \<subseteq> {v}\<close> \<open>p \<noteq> 0\<close> 
  shows \<open>card {x. insertion (\<lambda>v. x) p = 0} \<le> total_degree p\<close>
  using assms univariate_roots_bound[of "mpoly_to_poly v p", unfolded poly_eq_insertion[OF \<open>vars p \<subseteq> {v}\<close>]] 
  by (auto simp add: poly_degree_eq_total_degree mpoly_to_poly_zero_iff)

end
