theory BatchKZG_def

imports KZG_correct

begin

section \<open>Batch Opening Definition\<close>

locale BatchEvalKZG = KZG
begin 

text \<open>We define the batched version of the KZG according to the original KZG paper \<^cite>\<open>KZG10\<close>.

The batched version allows to verifiably open a commitment
to a polynomial for up to max\_deg points using only one witness. Note, that this batch
version is different from the one mentioned in the Sonic \<^cite>\<open>Sonic\<close> and PLONK \<^cite>\<open>PLONK\<close>
SNARKs, where multiple commitments can be batch opened for one point. The KZG \<^cite>\<open>KZG10\<close>
batched version is an extension of the KZG as defined in chapter 3 for the two
functions CreateWitnessBatch and VerifyEvalBatch, which we define below as 
eval\_batch and verify\_eval\_batch.\<close>

type_synonym 'e' batch_evaluation = "'e' mod_ring poly"

subsection \<open>Polynomial operations and prerequisites\<close>

text \<open>calculate the remainder polynomial of \<open>\<phi>/\<Prod>i\<in>B.(x-i)\<close> i.e. \<open>r = \<phi> mod \<Prod>i\<in>B.(x-i)\<close>\<close>
fun r :: "'e argument set \<Rightarrow> 'e mod_ring poly \<Rightarrow>'e batch_evaluation" where
  "r B \<phi> = do {
  let prod_B = prod (\<lambda>i. [:-i,1:])  B;
  \<phi> mod prod_B}"

lemma deg_r: "degree (r B \<phi>) \<le> degree \<phi>"
  by (smt (verit) add.right_neutral bot_nat_0.not_eq_extremum degree_0 degree_mod_less' div_poly_eq_0_iff less_or_eq_imp_le mod_div_mult_eq mult_eq_0_iff nat_le_linear order_trans_rules(21) r.simps)

text \<open>calculate \<open>(\<phi>(x) - r(x))/\<Prod>i\<in>B.(x-i)\<close>\<close>
fun \<psi>\<^sub>B :: "'e argument set \<Rightarrow> 'e mod_ring poly \<Rightarrow> 'e mod_ring poly" where
  "\<psi>\<^sub>B B \<phi> = do {
    let prod_B = prod (\<lambda>i. [:-i,1:])  B;
    (\<phi> - (r B \<phi>)) div prod_B}"

text \<open>\<open>\<phi>(x)= (\<phi>(x)/\<Prod>i\<in>B.(x-i)) * \<Prod>i\<in>B.(x-i) + \<phi> mod \<Prod>i\<in>B.(x-i)\<close>\<close>
lemma "\<phi> = \<psi>\<^sub>B B \<phi> * (prod (\<lambda>i. [:-i,1:])  B) + r B \<phi>"
  by simp

text \<open>degree of \<open>\<Prod>i\<in>B.(x-i)\<close> is \<open>|B|\<close>\<close>
lemma deg_Prod: "degree (\<Prod>i\<in>B. [:- i, 1:]) = card (B::'e argument set)"
proof -
  have "finite B \<Longrightarrow> degree (\<Prod>i\<in>B. [:- i, 1:]) = card (B::'e argument set)"
  proof (induct B rule: finite_induct)
    case empty
    then show ?case by simp
  next
    case (insert a S)
    have "degree ([:- a, 1:] * (\<Prod>i\<in>S. [:- i, 1:])) = degree ([:- a, 1:]) + degree (\<Prod>i\<in>S. [:- i, 1:])"
      by (rule degree_mult_eq)auto
    then show ?case
      by (metis (no_types, lifting) One_nat_def card.insert degree_pCons_eq_if eq_numeral_extra(2) local.insert(1) local.insert(2) local.insert(3) one_pCons plus_1_eq_Suc prod.insert)
  qed
  then show ?thesis by fastforce
qed

lemma deg_r_B_le: "degree (r B \<phi>) \<le> card B"
  by (metis (no_types, lifting) card_0_eq deg_Prod degree_0 degree_mod_less' less_or_eq_imp_le not_gr0 prod.empty prod.infinite r.simps verit_eq_simplify(24))

lemma deg_r_B_less: "B \<noteq> {} \<Longrightarrow> degree \<phi> > card B \<Longrightarrow> degree (r B \<phi>) < card B"
  by (metis card_eq_0_iff card_gt_0_iff deg_Prod degree_0 degree_mod_less' finite r.simps)

lemma deg_div: "degree ((x::'e mod_ring poly) div y) \<le> degree x"
  by (metis (no_types, lifting) Polynomial.degree_div_less add_diff_cancel_left' bot_nat_0.extremum_strict degree_0 degree_mod_less' degree_mult_right_le diff_zero div_poly_eq_0_iff gr0I less_or_eq_imp_le mod_div_mult_eq)

lemma deg_\<psi>\<^sub>B: "degree (\<psi>\<^sub>B B \<phi>) \<le> degree \<phi>"
  by (simp add: poly_div_diff_left deg_div)

text \<open>\<open>e \<in> B\<close> implies \<open>\<Prod>i\<in>B.(x-i)\<close> is 0 at \<open>e\<close>\<close>
lemma i_in_B_prod_B_zero[simp]: 
  assumes"(i::'e argument) \<in> B "
  shows "poly (prod (\<lambda>i. [:-i,1:])  B) i = 0"
proof -
  have i_is_zero: "(\<lambda>x. poly [:-x,1:] i) i = 0" by simp
  have "poly (prod (\<lambda>i. [:-i,1:])  B) i 
      = (prod (\<lambda>x. poly [:-x,1:] i)  B)"
    using poly_prod by fast
  also have "prod (\<lambda>x. poly [:-x,1:] i)  B = 0"
  proof (rule prod_zero)
    show "finite B"
      by simp
    show "\<exists>a\<in>B. poly [:- a, 1:] i = 0"
      using i_is_zero assms by fast
  qed
  finally show "poly (prod (\<lambda>i. [:-i,1:])  B) i = 0" .
qed

text \<open>\<open>r(i)=\<phi>(i)\<close> for all \<open>i \<in> B\<close>\<close>
lemma r_eq_\<phi>_on_B:
  assumes "(i::'e argument) \<in> B"
  shows "poly (r B \<phi>) i = poly \<phi> i"
proof -
  let ?prod_B = "prod (\<lambda>i. [:-i,1:]) B"
  have "poly \<phi> i = poly (\<phi> div ?prod_B * ?prod_B) i + poly (\<phi> mod ?prod_B) i"
    by (metis div_mult_mod_eq poly_hom.hom_add)
  moreover have "poly (\<phi> div ?prod_B * ?prod_B) i = 0"
    using i_in_B_prod_B_zero[OF assms] by simp
  ultimately have "poly \<phi> i = poly (\<phi> mod ?prod_B) i"
    by fastforce
  then show "poly (r B \<phi>) i = poly \<phi> i"
    by simp
qed

lemma "(\<Prod>i\<in>B. [:- i, 1:]) dvd \<phi> \<Longrightarrow> \<phi> mod (\<Prod>i\<in>B. [:- i, 1:]) = 0 "
  by fastforce  

subsection \<open>Function definitions\<close>

text \<open>We define EvalBatch according to CreateWitnessBatch in \<^cite>\<open>KZG10\<close> section 3.4 Batch Opening.
The function reveals all points \<open>(i,\<phi>(i))\<close> for \<open>i \<in> B\<close> using only one witness value.
It returns (B,r(x),w\_i), where B is the provided set of positions, r(x) is a polynomial holding all 
evaluations (i.e. \<open>r(i)=\<phi>(i)\<close> for all \<open>i \<in> B\<close>), and w\_B is the witness for B and r(x).\<close>
definition eval_batch :: "'a ck \<Rightarrow> trapdoor \<Rightarrow> 'e mod_ring poly \<Rightarrow> 'e argument set
  \<Rightarrow> ('e batch_evaluation \<times> 'a witness)"
where 
  "eval_batch PK td \<phi> B =( 
    let r = r B \<phi>; \<comment>\<open>remainder of \<open>\<phi>(x)/(\<Prod>i\<in>B. (x-i))\<close> i.e. \<open>\<phi>(x) mod (\<Prod>i\<in>B. (x-i))\<close>\<close>
        \<psi> = \<psi>\<^sub>B B \<phi>; \<comment>\<open>\<open>(\<phi>(x) - r(x)) / (\<Prod>i\<in>B. (x-i))\<close>\<close>
        w_B = g_pow_PK_Prod PK \<psi> \<comment>\<open>\<open>g^\<psi>(\<alpha>)\<close>\<close>
    in
    (r, w_B) \<comment>\<open>\<open>(B, r(x), g^\<psi>(\<alpha>))\<close>\<close>
  )" 

text \<open>We define VerifyEvalBatch according to \<^cite>\<open>KZG10\<close> section 3.4 Batch Opening.
The function verifies the witness w\_B for a set B, a polynomial r(x), and a commitment C to a 
polynomial \<open>\<phi>(x)\<close>.\<close>
definition verify_eval_batch :: "'a vk \<Rightarrow> 'a commit \<Rightarrow> 'e argument set \<Rightarrow> ('e batch_evaluation \<times> 'a witness) 
  \<Rightarrow> bool"
where 
  "verify_eval_batch PK C B val = (
    let (r_x, w\<^sub>B) = val;
        g_pow_prod_B = g_pow_PK_Prod PK (prod (\<lambda>i. [:-i,1:]) B);
        g_pow_r = g_pow_PK_Prod PK r_x in
    (e g_pow_prod_B w\<^sub>B \<otimes>\<^bsub>G\<^sub>T\<^esub> (e \<^bold>g g_pow_r) = e C \<^bold>g))
    \<comment>\<open>\<open>e(g^(\<Prod>i\<in>B. (\<alpha>-i)), g^\<psi>(\<alpha>)) \<otimes> e(g,g^r(\<alpha>)) = e(C, g)\<close>\<close>"

definition valid_argument_batch :: "'e argument set \<Rightarrow> bool"
  where "valid_argument_batch B = (card B \<le> max_deg)"

definition valid_eval_batch::"('e batch_evaluation \<times> 'a witness) \<Rightarrow> bool"
  where "valid_eval_batch val = (let (r,w) = val in degree r < max_deg \<and> w \<in> carrier G\<^sub>p)"

text \<open>the BatchEvalKZG is a polynomial commitment scheme\<close>
sublocale bKZG: abstract_polynomial_commitment_scheme key_gen commit verify_poly eval_batch 
  verify_eval_batch valid_poly valid_argument_batch valid_eval_batch .

end

end