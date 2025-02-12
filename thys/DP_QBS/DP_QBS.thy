(* Title:  DP_QBS.thy
   Author: Michikazu Hirata, Institute of Science Tokyo *)

theory DP_QBS
  imports "Differential_Privacy.Differential_Privacy_Divergence"
          "Differential_Privacy.Differential_Privacy_Standard"
          "S_Finite_Measure_Monad.Monad_QuasiBorel"
begin

declare qbs_morphism_imp_measurable[measurable_dest]

section \<open> Definitions\<close>
text \<open> Details of differential privacy using quasi-Borel spaces are found at~\cite{Sato_Katsumata_2023}\<close>

subsection \<open> Divergence for Differential Privacy using QBS\<close>
definition DP_qbs_divergence :: "'a qbs_measure \<Rightarrow> 'a qbs_measure \<Rightarrow> real \<Rightarrow> ereal" ("DP'_divergence\<^sub>Q") where
DP_qbs_divergence_qbs_l: "DP_divergence\<^sub>Q p q e \<equiv> DP_divergence (qbs_l p) (qbs_l q) e"

abbreviation DP_qbs_inequality ("DP'_inequality\<^sub>Q") where
"DP_qbs_inequality p q \<epsilon> \<delta> \<equiv> DP_divergence\<^sub>Q p q \<epsilon> \<le> ereal \<delta>"

lemmas DP_qbs_divergence_def = DP_qbs_divergence_qbs_l[simplified DP_divergence_SUP]

(* non-negativity *)
lemma DP_qbs_divergence_nonneg[simp]: "0 \<le> DP_divergence\<^sub>Q p q e"
  by(auto simp: le_SUP_iff zero_ereal_def DP_qbs_divergence_def intro!: bexI[where x="{}"])

lemma DP_qbs_divergence_le_ereal_iff:
  "DP_divergence\<^sub>Q p q \<epsilon> \<le> ereal \<delta> \<longleftrightarrow> (\<forall>A \<in> sets (qbs_l p). measure (qbs_l p) A - exp \<epsilon> * measure (qbs_l q) A \<le> \<delta>)"
  by (auto simp: DP_divergence_forall DP_qbs_divergence_qbs_l)

corollary DP_qbs_divergence_le_ereal_dest:
  assumes "DP_divergence\<^sub>Q p q \<epsilon> \<le> ereal \<delta>"
  shows "measure (qbs_l p) A \<le> exp \<epsilon> * measure (qbs_l q) A + \<delta>"
  using assms order.trans[OF DP_qbs_divergence_nonneg assms]
  by(cases "A \<in> sets (qbs_l p)") (auto simp: DP_qbs_divergence_le_ereal_iff measure_notin_sets)

corollary DP_qbs_divergence_le_erealI:
  assumes "\<And> A. A \<in> sets (qbs_l p) \<Longrightarrow> measure (qbs_l p) A \<le> exp \<epsilon> * measure (qbs_l q) A + \<delta>"
  shows "DP_divergence\<^sub>Q p q \<epsilon> \<le> ereal \<delta>"
  using assms by(fastforce simp: DP_qbs_divergence_le_ereal_iff)

lemma DP_qbs_divergence_zero:
  assumes "p \<in> monadP_qbs X"
    and "q \<in> monadP_qbs X"
    and "DP_inequality\<^sub>Q p q 0 0"
  shows "p = q"
  by(auto intro!: inj_onD[OF qbs_l_inj_P] DP_divergence_zero[where L="qbs_to_measure X"]
                  assms[simplified DP_qbs_divergence_qbs_l] measurable_space[OF qbs_l_measurable_prob]
            simp: space_L)

(* antimonotonicity for \<epsilon> *)
lemma DP_qbs_divergence_antimono: "a \<le> b \<Longrightarrow> DP_divergence\<^sub>Q p q b \<le> DP_divergence\<^sub>Q p q a"
  by(auto simp: DP_qbs_divergence_def intro!: SUP_mono' mult_right_mono)

(* reflexivity *)
lemma DP_qbs_divergence_refl[simp]: "DP_divergence\<^sub>Q p p 0 = 0"
  unfolding DP_qbs_divergence_qbs_l by(rule DP_divergence_reflexivity)

lemma DP_qbs_divergence_refl'[simp]: "0 \<le> e \<Longrightarrow> DP_divergence\<^sub>Q p p e = 0"
  by(intro antisym DP_qbs_divergence_nonneg) (auto simp: DP_qbs_divergence_def SUP_le_iff mult_le_cancel_right1)

(* transitivity *)
lemma DP_qbs_divergence_trans':
  assumes "DP_inequality\<^sub>Q p q \<epsilon> \<delta>"
    and "DP_inequality\<^sub>Q q l \<epsilon>' 0"
  shows "DP_inequality\<^sub>Q p l (\<epsilon> + \<epsilon>') \<delta>"
  unfolding DP_qbs_divergence_le_ereal_iff diff_le_eq
proof safe
  fix A
  assume [measurable]:"A \<in> sets (qbs_l p)"
  show "measure (qbs_l p) A \<le> \<delta> + exp (\<epsilon> + \<epsilon>') * measure (qbs_l l) A"
  proof -
    have "measure (qbs_l p) A \<le> \<delta> + exp \<epsilon> * measure (qbs_l q) A"
      using assms(1) by(auto simp: DP_qbs_divergence_le_ereal_iff diff_le_eq)
    also have "... \<le> \<delta> + exp \<epsilon> * (exp \<epsilon>' * measure (qbs_l l) A)"
      using DP_qbs_divergence_le_ereal_dest assms(2) by fastforce
    finally show ?thesis
      by (simp add: exp_add)
  qed
qed

lemmas DP_qbs_divergence_trans = DP_qbs_divergence_trans'[where \<delta>=0]

(* composability *)
proposition DP_qbs_divergence_compose:
  assumes [qbs,measurable]:"p \<in> monadP_qbs X" "q \<in> monadP_qbs X" "f \<in> X \<rightarrow>\<^sub>Q monadP_qbs Y" "g \<in> X \<rightarrow>\<^sub>Q monadP_qbs Y"
    and dp1:"DP_divergence\<^sub>Q p q \<epsilon> \<le> ereal \<delta>"
    and dp2:"\<And>x. x \<in> qbs_space X \<Longrightarrow> DP_divergence\<^sub>Q (f x) (g x) \<epsilon>' \<le> ereal \<delta>'"
    and [arith]: "0 \<le> \<epsilon>" "0 \<le> \<epsilon>'"
  shows "DP_divergence\<^sub>Q (p \<bind> f) (q \<bind> g) (\<epsilon> + \<epsilon>') \<le> ereal (\<delta> + \<delta>')"
proof -
  interpret comparable_probability_measures "qbs_to_measure X" "qbs_l p" "qbs_l q"
    by(auto simp: comparable_probability_measures_def space_L intro!: qbs_l_measurable_prob[THEN measurable_space])
  note [measurable,simp] = qbs_l_measurable_prob
  show ?thesis
    by(auto simp: qbs_l_bind_qbsP[of _ X _ Y] space_L M N DP_qbs_divergence_qbs_l
        intro!: DP_divergence_composability[where K="qbs_to_measure Y" and L="qbs_to_measure X"]
                dp1[simplified DP_qbs_divergence_qbs_l] dp2[simplified DP_qbs_divergence_qbs_l])
qed

(* Dataprocessing inequality *)
corollary DP_qbs_divergence_dataprocessing:
  assumes [qbs]:"p \<in> monadP_qbs X" "q \<in> monadP_qbs X" "f \<in> X \<rightarrow>\<^sub>Q monadP_qbs Y"
    and dp: "DP_divergence\<^sub>Q p q \<epsilon> \<le> ereal \<delta>"
    and [arith]:"0 \<le> \<epsilon>"
  shows  "DP_divergence\<^sub>Q (p \<bind> f) (q \<bind> f) \<epsilon> \<le> ereal \<delta>"
proof -
  interpret comparable_probability_measures "qbs_to_measure X" "qbs_l p" "qbs_l q"
    by(auto simp: comparable_probability_measures_def space_L intro!: qbs_l_measurable_prob[THEN measurable_space])
  note [measurable] = qbs_l_measurable_prob qbs_morphism_imp_measurable[OF assms(3)]
  show ?thesis
    by(auto simp: qbs_l_bind_qbsP[of _ X _ Y] space_L M N DP_qbs_divergence_qbs_l
        intro!: DP_divergence_postprocessing[where L= "qbs_to_measure X" and K="qbs_to_measure Y"]
                dp[simplified DP_qbs_divergence_qbs_l])
qed

(* additivity = law for double-strength *)
lemma DP_qbs_divergence_additive:
  assumes [qbs]:"p \<in> monadP_qbs X" "q \<in> monadP_qbs X" "p' \<in> monadP_qbs Y" "q' \<in> monadP_qbs Y"
    and div1: "DP_divergence\<^sub>Q p q \<epsilon> \<le> ereal \<delta>"
    and div2: "DP_divergence\<^sub>Q p' q' \<epsilon>' \<le> ereal \<delta>'"
    and [arith]:"0 \<le> \<epsilon>" "0 \<le> \<epsilon>'"
  shows "DP_divergence\<^sub>Q (p \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s p') (q \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s q') (\<epsilon> + \<epsilon>') \<le> ereal (\<delta> + \<delta>')"
proof -
  note [qbs] = return_qbs_morphismP bind_qbs_morphismP qbs_space_monadPM
  have "DP_divergence\<^sub>Q (p \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s p') (q \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s q') (\<epsilon> + \<epsilon>')
      = DP_divergence\<^sub>Q (p \<bind> (\<lambda>x. p' \<bind> (\<lambda>y. return_qbs (X \<Otimes>\<^sub>Q Y) (x, y))))
                       (q \<bind> (\<lambda>x. q' \<bind> (\<lambda>y. return_qbs (X \<Otimes>\<^sub>Q Y) (x, y)))) (\<epsilon> + \<epsilon>')"
    by(simp add: qbs_pair_measure_def[of _ X _ Y])
  also have "... \<le> ereal (\<delta> + \<delta>')"
    by(auto intro!: DP_qbs_divergence_compose[of _ X _ _ "X \<Otimes>\<^sub>Q Y"] div1 div2
                    DP_qbs_divergence_dataprocessing[of _ Y _ _ "X \<Otimes>\<^sub>Q Y"])
  finally show ?thesis .
qed

(* strengh law *)
corollary DP_qbs_divergence_strength:
  assumes [qbs]:"p \<in> monadP_qbs X" "q \<in> monadP_qbs X" "x \<in> qbs_space Y"
    and dp: "DP_divergence\<^sub>Q p q \<epsilon> \<le> ereal \<delta>"
    and [simp]:"0 \<le> \<epsilon>"
  shows "DP_divergence\<^sub>Q (return_qbs Y x \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s p) (return_qbs Y x \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s q) \<epsilon> \<le> ereal \<delta>"
proof -
  note [qbs] = return_qbs_morphismP
  show ?thesis
    by(auto intro!: DP_qbs_divergence_additive[of _ Y _ _ X _ 0 0,simplified] dp)
qed


subsection \<open>Differential Privacy using QBS\<close>
definition DP_qbs ("differential'_privacy\<^sub>Q") where
DP_qbs_qbs_L:"differential_privacy\<^sub>Q M \<equiv> differential_privacy (\<lambda>x. qbs_l (M x))"

lemma DP_qbs_def:
  "differential_privacy\<^sub>Q M adj \<epsilon> \<delta> \<longleftrightarrow>
   (\<forall>(d1, d2)\<in>adj. DP_inequality\<^sub>Q (M d1) (M d2) \<epsilon> \<delta> \<and> DP_inequality\<^sub>Q (M d2) (M d1) \<epsilon> \<delta>)"
  by(simp add: DP_inequality_cong_DP_divergence differential_privacy_def DP_qbs_qbs_L DP_qbs_divergence_qbs_l)

lemma DP_qbs_adj_sym:
  assumes "sym adj"
  shows "differential_privacy\<^sub>Q M adj \<epsilon> \<delta> \<longleftrightarrow> (\<forall> (d1,d2) \<in> adj.  DP_inequality\<^sub>Q (M d1) (M d2) \<epsilon> \<delta>)"
  by(auto simp: differential_privacy_adj_sym[OF assms] DP_inequality_cong_DP_divergence
                DP_qbs_qbs_L DP_qbs_divergence_qbs_l)

lemma pure_DP_qbs_comp:
  assumes "adj \<subseteq> qbs_space X \<times> qbs_space X"
    and "adj' \<subseteq> qbs_space X \<times> qbs_space X"
    and "differential_privacy\<^sub>Q M adj \<epsilon> 0"
    and "differential_privacy\<^sub>Q M adj' \<epsilon>' 0"
    and "M \<in> X \<rightarrow>\<^sub>Q monadP_qbs Y"
  shows "differential_privacy\<^sub>Q M (adj O adj') (\<epsilon> + \<epsilon>') 0"
  using assms
  by(auto intro!: pure_differential_privacy_comp[where X="qbs_to_measure X" and R="qbs_to_measure Y"]
      simp: space_L DP_qbs_qbs_L)

lemma pure_DP_qbs_trans_k:
  assumes "adj \<subseteq> qbs_space X \<times> qbs_space X"
    and "differential_privacy\<^sub>Q M adj \<epsilon> 0"
    and "M \<in> X \<rightarrow>\<^sub>Q monadP_qbs Y"
  shows "differential_privacy\<^sub>Q M (adj ^^ k) (k * \<epsilon>) 0"
  using assms
  by(auto intro!: pure_differential_privacy_trans_k[where X="qbs_to_measure X" and R="qbs_to_measure Y"]
      simp: space_L DP_qbs_qbs_L)

proposition DP_qbs_postprocessing:
  assumes "\<epsilon> \<ge> 0"
    and "differential_privacy\<^sub>Q M adj \<epsilon> \<delta>"
    and [qbs,measurable]:"M \<in> X \<rightarrow>\<^sub>Q monadP_qbs Y"
    and [qbs,measurable]:"N \<in> Y \<rightarrow>\<^sub>Q monadP_qbs Z"
    and "adj \<subseteq> qbs_space X \<times> qbs_space X"
  shows "differential_privacy\<^sub>Q (\<lambda>x. M x \<bind> N) adj \<epsilon> \<delta>"
  using assms by(auto simp: DP_qbs_def intro!: DP_qbs_divergence_dataprocessing[of _ Y _ _ Z])

corollary DP_qbs_postprocessing_return:
  assumes "\<epsilon> \<ge> 0"
    and "differential_privacy\<^sub>Q M adj \<epsilon> \<delta>"
    and "M \<in> X \<rightarrow>\<^sub>Q monadP_qbs Y"
    and "N \<in> Y \<rightarrow>\<^sub>Q Z"
    and "adj \<subseteq> qbs_space X \<times> qbs_space X"
  shows "differential_privacy\<^sub>Q (\<lambda>x. M x \<bind> (\<lambda>y. return_qbs Z (N y))) adj \<epsilon> \<delta>"
  by(intro DP_qbs_postprocessing[where X=X and Y=Y and Z=Z])
    (use return_qbs_morphismP[of Z] assms in auto)

lemma DP_qbs_preprocessing:
  assumes "\<epsilon> \<ge> 0"
    and "differential_privacy\<^sub>Q M adj \<epsilon> \<delta>"
    and [measurable]:"f \<in> X' \<rightarrow>\<^sub>Q X"
    and "\<forall>(x,y) \<in> adj'. ((f x), (f y)) \<in> adj"
    and "adj \<subseteq> qbs_space X \<times> qbs_space X"
    and "adj' \<subseteq> qbs_space X' \<times> qbs_space X'"
  shows "differential_privacy\<^sub>Q (M \<circ> f) adj' \<epsilon> \<delta>"
  using assms by(auto simp: DP_qbs_def)

proposition DP_qbs_bind_adaptive:
  assumes "\<epsilon> \<ge> 0" and "\<epsilon>' \<ge> 0"
    and [qbs]:"M \<in> X \<rightarrow>\<^sub>Q monadP_qbs Y"
    and "differential_privacy\<^sub>Q M adj \<epsilon> \<delta>"
    and [qbs]:"N \<in> X \<Rightarrow>\<^sub>Q Y \<Rightarrow>\<^sub>Q monadP_qbs Z"
    and "\<And>y. y \<in> qbs_space Y \<Longrightarrow> differential_privacy\<^sub>Q (\<lambda>x. N x y) adj \<epsilon>' \<delta>'"
    and "adj \<subseteq> qbs_space X \<times> qbs_space X"
  shows "differential_privacy\<^sub>Q (\<lambda>x. M x \<bind> N x) adj (\<epsilon> + \<epsilon>') (\<delta> + \<delta>')"
 using assms by(fastforce simp add: DP_qbs_def intro!: DP_qbs_divergence_compose[of _ Y _ _ Z])

proposition DP_qbs_bind_pair:
  assumes "\<epsilon> \<ge> 0" "\<epsilon>' \<ge> 0"
    and [qbs]:"M \<in> X \<rightarrow>\<^sub>Q monadP_qbs Y"
    and "differential_privacy\<^sub>Q M adj \<epsilon> \<delta>"
    and [qbs]:"N \<in> X \<rightarrow>\<^sub>Q monadP_qbs Z"
    and "differential_privacy\<^sub>Q N adj \<epsilon>' \<delta>'"
    and "adj \<subseteq> qbs_space X \<times> qbs_space X"
  shows "differential_privacy\<^sub>Q (\<lambda>x. M x \<bind> (\<lambda>y. N x \<bind> (\<lambda>z. return_qbs (Y \<Otimes>\<^sub>Q Z) (y,z)))) adj (\<epsilon> + \<epsilon>') (\<delta> + \<delta>')"
proof -
  note [qbs] = return_qbs_morphismP bind_qbs_morphismP
  show "?thesis"
    using assms by(auto intro!: DP_qbs_bind_adaptive[where X=X and Y=Y and Z="Y \<Otimes>\<^sub>Q Z"]
                                DP_qbs_postprocessing[where X=X and Y=Z and Z="Y \<Otimes>\<^sub>Q Z"])
qed

end