theory Total_Degree_Env
  imports "Total_Degree" "Substitutions"
begin

section \<open>Bottom-up total\_degree under a substitution-degree environment\<close>

lift_definition total_degree_env
  :: "(nat \<Rightarrow> nat) \<Rightarrow> 'a::zero_neq_one mpoly \<Rightarrow> nat"
is "\<lambda>env p. Max (insert 0
     ((\<lambda>m. sum (\<lambda>i. env i * lookup m i) (keys m)) `
            (keys p)))" .

text \<open>
  @{term\<open>total_degree_env env p\<close>} walks over the monomial representation of p,
  and whenever it sees @{term\<open>Var i^m\<close>}, it contributes @{term\<open>m * env i\<close>} instead of m.
\<close>

lemma total_degree_env_id:
  "total_degree_env (\<lambda>_. 1) p = total_degree p"
  by transfer simp

lemma total_degree_env_zero[simp]: "total_degree_env f 0 = 0"
  by (simp add: total_degree_env.rep_eq zero_mpoly.rep_eq)

lemma total_degree_env_one[simp]: "total_degree_env f 1 = 0"
  by (simp add: total_degree_env.rep_eq one_mpoly.rep_eq)

lemma total_degree_env_Const[simp]: "total_degree_env f (Const c) = 0"
  by (simp add: total_degree_env.rep_eq Const.rep_eq Const\<^sub>0_def)

lemma total_degree_env_Const_le: "total_degree_env f (Const c) \<le> 0"
  by simp

lemma total_degree_env_Var[simp]:
  "total_degree_env f (Var i) = f i"
  by (simp add: total_degree_env.rep_eq Var.rep_eq Var\<^sub>0_def)

lemma total_degree_env_Var_le: "total_degree_env f (Var i) \<le> f i"
  by simp

lemma total_degree_env_neg: "total_degree_env f (-P) = total_degree_env f P"
  by (simp add: total_degree_env.rep_eq uminus_mpoly.rep_eq)

lemma total_degree_env_mult: "total_degree_env f (P * Q) \<le> total_degree_env f P + total_degree_env f Q"
proof -
  have "m \<in> keys (mapping_of (P * Q)) \<Longrightarrow>
        sum (\<lambda>i. f i * lookup m i) (keys m) \<le> total_degree_env f P + total_degree_env f Q" for m
  proof -
    assume "m \<in> keys (mapping_of (P * Q))"
    hence "m \<in> {a + b | a b. a \<in> keys (mapping_of P) \<and> b \<in> keys (mapping_of Q)}"
      unfolding times_mpoly.rep_eq using keys_mult by blast
    then obtain a b where m_def: "m = a + b"
                      and a_key: "a \<in> keys (mapping_of P)"
                      and b_key: "b \<in> keys (mapping_of Q)"
      by blast
    have a_bound: "sum (\<lambda>i. f i * lookup a i) (keys a) \<le> total_degree_env f P"
      unfolding total_degree_env.rep_eq
      by (rule Max_ge, simp_all add: a_key)
    have b_bound: "sum (\<lambda>i. f i * lookup b i) (keys b) \<le> total_degree_env f Q"
      unfolding total_degree_env.rep_eq
      by (rule Max_ge, simp_all add: b_key)
    show "sum (\<lambda>i. f i * lookup m i) (keys m) \<le> total_degree_env f P + total_degree_env f Q"
      unfolding m_def
      apply (subst setsum_keys_plus_distrib, simp_all add: algebra_simps)
      using a_bound b_bound by linarith
  qed
  thus ?thesis
    unfolding total_degree_env.rep_eq by simp
qed

lemma total_degree_env_pow: "total_degree_env f (P ^ n) \<le> n * total_degree_env f P"
  by (induction n, simp_all add: le_trans[OF total_degree_env_mult])

lemma total_degree_env_add: "total_degree_env f (P + Q) \<le> max (total_degree_env f P) (total_degree_env f Q)"
proof -
  have "m \<in> keys (mapping_of (P + Q)) \<Longrightarrow>
        sum (\<lambda>i. f i * lookup m i) (keys m) \<le> max (total_degree_env f P) (total_degree_env f Q)" for m
  proof -
    assume "m \<in> keys (mapping_of (P + Q))"
    hence in_union: "m \<in> keys (mapping_of P) \<union> keys (mapping_of Q)"
      unfolding plus_mpoly.rep_eq using Poly_Mapping.keys_add by fastforce
    show "sum (\<lambda>i. f i * lookup m i) (keys m) \<le> max (total_degree_env f P) (total_degree_env f Q)"
      unfolding total_degree_env.rep_eq
      by (metis (mono_tags, lifting) Max_ge UnE finite_imageI finite_insert finite_keys imageI
           in_union insertCI le_max_iff_disj)
  qed
  thus ?thesis unfolding total_degree_env.rep_eq by simp
qed

lemma total_degree_env_diff:
  fixes P :: "'a::{ab_group_add,zero_neq_one} mpoly"
  shows "total_degree_env f (P - Q) \<le> max (total_degree_env f P) (total_degree_env f Q)"
  unfolding diff_conv_add_uminus total_degree_env_neg[of f Q, symmetric]
  by (rule total_degree_env_add)

lemma total_degree_env_sum:
  fixes P :: "'a \<Rightarrow> 'b::{ab_group_add,zero_neq_one} mpoly"
  assumes S_fin: "finite S"
  shows "total_degree_env ctxt (sum P S) \<le> Max (insert 0 ((\<lambda>i. total_degree_env ctxt (P i)) ` S))"
  apply (induct rule: finite_induct[OF S_fin], simp_all)
  apply (rule le_trans[OF total_degree_env_add], simp)
  using order.trans by fastforce

lemma total_degree_env_prod:
  assumes S_fin: "finite S"
  shows "total_degree_env ctxt (prod P S) \<le> sum (\<lambda>i. total_degree_env ctxt (P i)) S"
  by (induct rule: finite_induct[OF S_fin], simp_all add: le_trans[OF total_degree_env_mult])

lemma total_degree_env_poly_subst_monom:
  defines "degree_monom \<equiv> (\<lambda>m t. (lookup m) t)" (* Intentionally written this way for clarity *)
  shows "total_degree_env ctxt (poly_subst_monom f m)
         \<le> (\<Sum>t\<in>keys m. degree_monom m t * total_degree_env ctxt (f t))"
  unfolding poly_subst_monom_alt degree_monom_def
  by (simp add: le_trans[OF total_degree_env_prod[OF finite_keys]]
                le_trans[OF sum_mono[OF total_degree_env_pow]])

lemma total_degree_env_poly_subst_list:
  fixes p :: "'a::comm_ring_1 mpoly"
  shows "total_degree_env ctxt (poly_subst_list fs p)
   \<le> total_degree_env (\<lambda>m. total_degree_env ctxt (fs !\<^sub>0 m)) p"
proof -
  have "total_degree_env ctxt (poly_subst_list fs p)
        = total_degree_env ctxt (\<Sum>m. Const (coeff p m) * poly_subst_monom ((!\<^sub>0) fs) m)"
    by (simp add: poly_subst_list_def poly_subst_def)
  also have "\<dots> \<le> Max (insert 0 
                    ((\<lambda>m. total_degree_env ctxt (Const (coeff p m)
                                   * poly_subst_monom ((!\<^sub>0) fs) m))
                   ` (keys (mapping_of p))))"
    using 
      total_degree_env_sum
    by (metis (no_types) finite_keys poly_subst_alt poly_subst_def total_degree_env_sum)
  also have "\<dots> \<le> Max (insert 0 
                    ((\<lambda>m. total_degree_env ctxt (Const (coeff p m))
                            + total_degree_env ctxt (poly_subst_monom ((!\<^sub>0) fs) m))
                   ` (keys (mapping_of p))))"
    using
      total_degree_env_mult
    by (smt (verit, best) Max.insert Max_function_mono Max_mono empty_not_insert finite_imageI finite_insert finite_keys image_is_empty max_nat.left_neutral subsetI)
  also have "\<dots> \<le> Max (insert 0 
                    ((\<lambda>m. total_degree_env ctxt (poly_subst_monom ((!\<^sub>0) fs) m))
                   ` (keys (mapping_of p))))"
    by simp
  also have "\<dots> \<le> Max (insert 0 
                    ((\<lambda>m. (\<Sum>i\<in>keys m. lookup m i * total_degree_env ctxt (fs !\<^sub>0 i)))
                   ` (keys (mapping_of p))))"
    using 
      total_degree_env_poly_subst_monom[of _ "\<lambda>m. fs !\<^sub>0 m"]
    by (metis (no_types, lifting) Max.insert Max_function_mono Orderings.order_eq_iff finite_imageI finite_keys image_is_empty max_nat.left_neutral)
  finally show ?thesis by (simp add: total_degree_env_def mult.commute)
qed

lemma total_degree_poly_subst_list_env:
  fixes p :: "'a::comm_ring_1 mpoly"
  shows "total_degree (poly_subst_list fs p)
   \<le> total_degree_env (\<lambda>m. total_degree (fs !\<^sub>0 m)) p"
  using total_degree_env_poly_subst_list total_degree_env_id
  by (metis (lifting) ext)

(* Lemmas for list of Var constructors *)

lemma total_degree_env_Var_list_bound: "total_degree_env (\<lambda>_. 1) ((map Var ls) !\<^sub>0 i) \<le> 1"
  by (cases "i < length ls", auto simp: nth0_def)

lemma total_degree_env_Var_list: 
  "total_degree_env (\<lambda>_. 1) ((map Var ls) !\<^sub>0 i) = (if i < length ls then 1 else 0)"
  by (simp add: nth0_def)

lemma total_degree_map_Var: 
  "total_degree ((map Var ls) !\<^sub>0 j :: 'a::comm_semiring_1 mpoly) \<le> 1"
  by (cases "j < length ls"; auto simp add: nth0_def)

lemma total_degree_map_Var_int: 
  "total_degree ((map Var ls) !\<^sub>0 j :: int mpoly) \<le> Suc 0"
  using total_degree_map_Var by auto

lemma total_degree_env_mono3_map_Var: 
  "(\<And>i. env i \<le> 1) \<Longrightarrow> total_degree_env env ((map Var ls) !\<^sub>0 j) \<le> 1"
  by (cases "j < length ls", simp_all add: nth0_def)

(* Substitution of a shorter list *)

lemma total_degree_env_reduce: "i < length ls
  \<Longrightarrow> total_degree_env env ((ls @ xs) !\<^sub>0 i) = total_degree_env env (ls !\<^sub>0 i)"
  unfolding nth0_def by (simp add: nth_append_left)

(* Lemmas of general monotonicity properties *)

lemma total_degree_env_mono: 
  fixes P :: "int mpoly" 
  assumes "\<forall>i\<le>max_vars P. env1 i \<le> env2 i"
  shows "total_degree_env env1 P \<le> total_degree_env env2 P"
  unfolding total_degree_env.rep_eq apply simp
  apply (rule)
  subgoal premises h for m
    apply (rule le_trans[of _ "(\<Sum>i\<in>keys m. env2 i * lookup m i)"])
    subgoal 
      apply (rule sum_mono)
      using h assms after_max_vars
      by (metis Suc_eq_plus1 in_keys_iff mult_le_mono1 not_less_eq_eq)
    subgoal 
      by (meson Max_ge finite_imageI finite_insert finite_keys h image_eqI insert_iff)
    done
  done
         
lemma total_degree_env_mono2:
  fixes P :: "int mpoly"
  shows "total_degree P \<le> rhs1 \<Longrightarrow> (\<And>i. i \<le> max_vars P \<Longrightarrow> env i \<le> 1) \<Longrightarrow> rhs1 = rhs2
  \<Longrightarrow> total_degree_env env P \<le> rhs2"
  unfolding total_degree_env_id[symmetric]
  by (meson dual_order.trans total_degree_env_mono)

lemma total_degree_env_mono3_bounded: 
  fixes ls :: "int mpoly list"
  shows "j \<le> bound \<Longrightarrow> (\<And>i. i \<le> bound \<Longrightarrow> env i \<le> 1) \<Longrightarrow> max_vars (ls !\<^sub>0 j) \<le> bound
    \<Longrightarrow> total_degree (ls !\<^sub>0 j) \<le> Suc 0 \<Longrightarrow> total_degree_env env (ls !\<^sub>0 j) \<le> Suc 0"
proof -
  assume a: "j \<le> bound" and b: "\<And>i. i \<le> bound \<Longrightarrow> env i \<le> 1"
    and c: "max_vars (ls !\<^sub>0 j) \<le> bound" and d: "total_degree (ls !\<^sub>0 j) \<le> Suc 0"

  {
    fix a
    assume "a \<in> keys (mapping_of (ls !\<^sub>0 j))"
    with c have "\<forall>i\<in>keys a. i \<le> bound"
      unfolding max_vars_def vars_def by simp
      (* unfolding max_vars_def vars_def
      by (meson Max_ge UN_I finite_UN finite_keys le_trans) *)
    with b have "(\<Sum>i\<in>keys a. env i * lookup a i) \<le> sum (lookup a) (keys a)"
      by (subst sum_mono, simp_all)
  } note e = this
  
  from d e show ?thesis
    apply (cases "j < length ls", simp_all add: nth0_def)
    unfolding total_degree_env_id[symmetric] total_degree_env.rep_eq
    using dual_order.trans by (auto, blast)
qed

lemma total_degree_env_mono3: 
  "(\<And>i. env i \<le> 1) \<Longrightarrow> total_degree (ls !\<^sub>0 j) \<le> 1
    \<Longrightarrow> total_degree_env env (ls !\<^sub>0 j) \<le> 1"
proof -
  assume a: "(\<And>i. env i \<le> 1)" and b: "total_degree (ls !\<^sub>0 j) \<le> 1"

  {
    fix a
    assume "a \<in> keys (mapping_of (ls ! j))"
    have "(\<Sum>i\<in>keys a. env i * lookup a i) \<le> sum (lookup a) (keys a)"
      apply (rule sum_mono)
      using a by simp
  } note c = this
  
  from a b show ?thesis
    apply (cases "j < length ls", simp_all add: nth0_def )
    unfolding total_degree_env_id[symmetric] total_degree_env.rep_eq
    using c dual_order.trans by (auto, blast)
qed

lemma total_degree_env_mono3': 
  "(\<And>i. env i \<le> Suc 0) \<Longrightarrow> total_degree (ls !\<^sub>0 j) \<le> Suc 0
    \<Longrightarrow> total_degree_env env (ls !\<^sub>0 j) \<le> Suc 0"
  using total_degree_env_mono3 by auto

lemma total_degree_env_mono4: 
  "(\<And>i. env i \<le> 1) \<Longrightarrow> total_degree_env (\<lambda>_. 1) (ls !\<^sub>0 j) \<le> 1
    \<Longrightarrow> total_degree_env env (ls !\<^sub>0 j) \<le> 1"
  unfolding total_degree_env_id by (rule total_degree_env_mono3, simp_all)

end

