theory Lemmas_for_spmf

imports CryptHOL.CryptHOL
        Finite_UNIV

begin
section \<open>Auxiliary Lemmas on \<open>spmf\<close>\<close>

text \<open>Replicate function for spmf.\<close>
definition replicate_spmf :: "nat \<Rightarrow> 'b pmf \<Rightarrow> 'b list spmf" where
"replicate_spmf m p = spmf_of_pmf (replicate_pmf m p)"

lemma replicate_spmf_Suc_cons:
"replicate_spmf (m + 1) p = 
  do {
    xs \<leftarrow> replicate_spmf m p;
    x \<leftarrow> spmf_of_pmf p;
    return_spmf (x # xs)
  }"
unfolding replicate_spmf_def 
by (simp add: spmf_of_pmf_bind bind_commute_pmf[of p])

lemma replicate_spmf_Suc_app:
"replicate_spmf (m + 1) p = 
  do {
    xs \<leftarrow> replicate_spmf m p;
    x \<leftarrow> spmf_of_pmf p;
    return_spmf (xs @ [x])
  }"
unfolding replicate_spmf_def replicate_pmf_distrib[of m 1 p] 
by (simp add: spmf_of_pmf_bind bind_assoc_pmf bind_return_pmf)

text \<open>Lemmas on \<open>coin_spmf\<close>\<close>

lemma spmf_coin_spmf: "spmf coin_spmf i = 1/2"
by (simp add: spmf_of_set)

lemma bind_spmf_coin:
assumes "lossless_spmf p"
shows "bind_spmf p (\<lambda>_. coin_spmf) = coin_spmf" 
proof (rule spmf_eqI, goal_cases)
  case (1 i)
  have weight: "weight_spmf p = 1" using assms by (simp add: lossless_spmf_def)
  have *: "spmf (bind_spmf p (\<lambda>_. coin_spmf)) i = 1/2" 
    unfolding spmf_bind by (simp add: weight spmf_coin_spmf)
  then show ?case unfolding spmf_coin_spmf * by simp
qed

lemma if_splits_coin:
"(if P then coin_spmf else coin_spmf) = coin_spmf"
by simp

text \<open>Lemmas for rewriting of discrete probabilities.\<close>

lemma ex1_sum:
assumes "\<exists>! (x ::'a). P x" "finite (UNIV :: 'a set)"
shows "sum (\<lambda>x. of_bool (P x)) UNIV = 1"
by (smt (verit, best) Finite_Cartesian_Product.sum_cong_aux 
Groups_Big.comm_monoid_add_class.sum.delta assms(1) assms(2) iso_tuple_UNIV_I of_bool_def)

lemma (in kyber_spec) surj_add_qr:
"surj (\<lambda>x. x + (y:: 'a qr))"
unfolding surj_def 
by (metis Groups.group_cancel.sub1 add_ac(2) add_diff_cancel_left')

lemma (in kyber_spec) bij_add_qr:
"bij (\<lambda>x. x + (y::'a qr))"
by (simp add: bij_def surj_add_qr)



text \<open>Lemmas for addition and difference of uniform distributions\<close>

lemma (in kyber_spec) spmf_of_set_add:
"let A = (UNIV :: ('a qr, 'k) vec set) in
do {x \<leftarrow> spmf_of_set A; y \<leftarrow> spmf_of_set A; return_spmf (x+y)} = spmf_of_set A"
unfolding Let_def
proof (intro spmf_eqI, goal_cases)
  case (1 i)
  have "(\<Sum>x\<in>UNIV. \<Sum>xa\<in>UNIV. of_bool (x + xa = i)) = real CARD('a qr) ^ CARD('k)"
  proof -
    have "\<exists>!xa. x + xa = i" for x 
    by (metis add_diff_cancel_left' group_cancel.sub1)
    then have "(\<Sum>xa\<in>UNIV. of_bool (x + xa = i)) = 1" for x by (intro ex1_sum, auto)
    then show ?thesis 
    by (smt (verit, best) CARD_vec of_nat_eq_of_nat_power_cancel_iff real_of_card sum.cong)
  qed
  then show ?case by (simp add: spmf_bind spmf_of_set integral_spmf_of_set indicator_def)
qed

lemma (in kyber_spec) spmf_of_set_diff:
"let A = (UNIV :: ('a qr, 'k) vec set) in
do {x \<leftarrow> spmf_of_set A; y \<leftarrow> spmf_of_set A; return_spmf (x-y)} = spmf_of_set A"
unfolding Let_def
proof (intro spmf_eqI, goal_cases)
  case (1 i)
  have "(\<Sum>x\<in>UNIV. \<Sum>xa\<in>UNIV. of_bool (x - xa = i)) = real CARD('a qr) ^ CARD('k)"
  proof -
    have "\<exists>!xa. x - xa = i" for x
    by (metis (no_types, opaque_lifting) cancel_ab_semigroup_add_class.diff_right_commute 
      right_minus_eq) 
    then have "(\<Sum>xa\<in>UNIV. of_bool (x - xa = i)) = 1" for x by (intro ex1_sum, auto)
    then show ?thesis 
    by (smt (verit, best) CARD_vec of_nat_eq_of_nat_power_cancel_iff real_of_card sum.cong)
  qed
  then show ?case by (simp add: spmf_bind spmf_of_set integral_spmf_of_set indicator_def)
qed


end