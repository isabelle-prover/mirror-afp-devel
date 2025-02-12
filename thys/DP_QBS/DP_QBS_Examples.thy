(* Title:  DP_Examples.thy
   Author: Michikazu Hirata, Institute of Science Tokyo *)

section \<open> Examples \<close>
theory DP_QBS_Examples
  imports "DP_QBS"
          "Differential_Privacy.Differential_Privacy_Randomized_Response"
begin

(*TODO: move the follwoing to AFP entry S_Finite_Measure_Monad.Quasi-Borel *)
lemma qbs_space_list_qbs_borel[qbs]: "\<And>r. r \<in> qbs_space (list_qbs borel\<^sub>Q)"
  and qbs_space_list_qbs_count_space[qbs]: "\<And>i. r \<in> qbs_space (list_qbs (count_space\<^sub>Q (UNIV :: _ :: countable)))"
  by(auto simp: list_qbs_space)

subsection \<open> Randomized Response \<close>
lemma qbs_morphism_RR_mechanism[qbs]: "qbs_pmf \<circ> RR_mechanism e \<in> count_space\<^sub>Q UNIV \<rightarrow>\<^sub>Q monadP_qbs (count_space\<^sub>Q UNIV)"
  by(auto intro!: qbs_morphism_count_space' qbs_pmf_qbsP)

lemma qbs_DP_RR_mechanism:
  assumes [arith]:"\<epsilon> \<ge> 0"
  shows "DP_divergence\<^sub>Q (RR_mechanism \<epsilon> x) (RR_mechanism \<epsilon> y) \<epsilon> = 0"
proof(intro antisym DP_qbs_divergence_nonneg)
  have [arith]: "1 + exp \<epsilon> > 0"
    by(auto simp: add_pos_nonneg intro!:divide_le_eq_1_pos[THEN iffD2])
  have [arith]: "1 / (1 + exp \<epsilon>) \<le> exp \<epsilon> * exp \<epsilon> / (1 + exp \<epsilon>)"
    by(rule order.trans[where b="exp \<epsilon> * (1 / (1 + exp \<epsilon>))"])
      (auto simp: divide_right_mono mult_le_cancel_right1)
  show "DP_divergence\<^sub>Q (RR_mechanism \<epsilon> x) (RR_mechanism \<epsilon> y) \<epsilon> \<le> 0"
    unfolding zero_ereal_def
  proof(rule DP_qbs_divergence_le_erealI)
    fix A :: "bool set"
    have ineq1: "measure_pmf.prob (bernoulli_pmf (exp \<epsilon> / (1 + exp \<epsilon>))) A
                 \<le> exp \<epsilon> * measure_pmf.prob (bernoulli_pmf (exp \<epsilon> / (1 + exp \<epsilon>))) A"
      and ineq2: "measure_pmf.prob (bernoulli_pmf (1 / (1 + exp \<epsilon>))) A
                  \<le> exp \<epsilon> * measure_pmf.prob (bernoulli_pmf (1 / (1 + exp \<epsilon>))) A"
      by(auto simp: mult_le_cancel_right1)
    have ineq3: "measure_pmf.prob (bernoulli_pmf (exp \<epsilon> / (1 + exp \<epsilon>))) A
                 \<le> exp \<epsilon> * measure_pmf.prob (bernoulli_pmf (1 / (1 + exp \<epsilon>))) A"
    proof -
      consider "A = {}" | "A = {True}" | "A = {False}" | "A = UNIV"
        by (metis (full_types) UNIV_eq_I is_singletonI' is_singleton_the_elem)
      then show ?thesis
        by cases (simp_all add: measure_pmf_single RR_probability_flip1 RR_probability_flip2)
    qed
    have ineq4: "measure_pmf.prob (bernoulli_pmf (1 / (1 + exp \<epsilon>))) A
                 \<le> exp \<epsilon> * measure_pmf.prob (bernoulli_pmf (exp \<epsilon> / (1 + exp \<epsilon>))) A"
    proof -
      consider "A = {}" | "A = {True}" | "A = {False}" | "A = UNIV"
        by (metis (full_types) UNIV_eq_I is_singletonI' is_singleton_the_elem)
      then show ?thesis
        by cases (simp_all add: measure_pmf_single RR_probability_flip1 RR_probability_flip2)
    qed
    show " measure (qbs_l (qbs_pmf (RR_mechanism \<epsilon> x))) A \<le> exp \<epsilon> * measure (qbs_l (qbs_pmf (RR_mechanism \<epsilon> y))) A + 0"
      using ineq1 ineq2 ineq3 ineq4 by(auto simp: RR_mechanism_def)
  qed
qed


subsection \<open> Laplace Distribution in QBS\<close>

lemma qbs_morphism_laplace_density[qbs]:"laplace_density \<in> borel\<^sub>Q \<Rightarrow>\<^sub>Q borel\<^sub>Q \<Rightarrow>\<^sub>Q borel\<^sub>Q \<Rightarrow>\<^sub>Q borel\<^sub>Q"
proof -
  have [simp]:"laplace_density = (\<lambda>l m x. if l > 0 then exp(-\<bar>x - m\<bar> / l) / (2 * l) else 0)"
    by standard+ (simp add: laplace_density_def)
  show ?thesis
    by simp
qed

definition qbs_Lap_mechanism ("Lap'_mechanism\<^sub>Q") where
 "Lap_mechanism\<^sub>Q \<equiv> \<lambda>e x. if e \<le> 0 then return_qbs borel\<^sub>Q x else density_qbs lborel\<^sub>Q (laplace_density e x)"

lemma qbs_morphism_Lap_mechanism[qbs]:"Lap_mechanism\<^sub>Q \<in> borel\<^sub>Q \<rightarrow>\<^sub>Q borel\<^sub>Q \<Rightarrow>\<^sub>Q monadP_qbs borel\<^sub>Q"
  by(intro curry_preserves_morphisms qbs_morphism_monadPI)
    (auto intro!: prob_space_return
      simp: qbs_Lap_mechanism_def qbs_l_return_qbs space_L qbs_l_density_qbs[of _ borel] prob_space_laplacian_density)

lemma qbs_l_Lap_mechanism: "qbs_l (Lap_mechanism\<^sub>Q e r) = Lap_dist e r"
  by(auto simp: qbs_Lap_mechanism_def qbs_l_return_qbs space_L qbs_l_density_qbs[of _ borel] Lap_dist_def cong: return_cong)

lemma qbs_Lap_mechanism_qbs_l_inverse:"Lap_mechanism\<^sub>Q e x= qbs_l_inverse (Lap_dist e x)"
  by(auto intro!: inj_onD[OF qbs_l_inj_P[of borel]] standard_borel_ne.qbs_l_qbs_l_inverse[OF _ sets_Lap_dist,symmetric]
     standard_borel_ne.qbs_l_inverse_in_space_monadP[OF _ sets_Lap_dist] simp: qbs_l_Lap_mechanism)

proposition qbs_DP_Lap_mechanism:
  assumes "\<epsilon> > 0" and "\<bar>x - y\<bar> \<le> r"
  shows "DP_divergence\<^sub>Q (Lap_mechanism\<^sub>Q (1 / \<epsilon>) x) (Lap_mechanism\<^sub>Q (1 / \<epsilon>) y) (r * \<epsilon>) = 0"
  using DP_divergence_Lap_dist'[where b="1 / \<epsilon>"]
  by(intro antisym DP_qbs_divergence_nonneg)
    (auto simp: DP_qbs_qbs_L DP_qbs_divergence_qbs_l qbs_l_Lap_mechanism zero_ereal_def intro!: assms)
                                                                                                           
subsection \<open> Naive Report Noisy Max Mechanism\<close>
primrec qbs_NaiveRNM  :: "real \<Rightarrow> real list \<Rightarrow> real qbs_measure" where
  "qbs_NaiveRNM \<epsilon> [] = return_qbs borel 0" |
  "qbs_NaiveRNM \<epsilon> (x # xs) =
  (case xs of 
    Nil \<Rightarrow> Lap_mechanism\<^sub>Q (1 / \<epsilon>) x | 
    y#ys \<Rightarrow> do {x1 \<leftarrow> Lap_mechanism\<^sub>Q (1 / \<epsilon>) x; x2 \<leftarrow> qbs_NaiveRNM \<epsilon> xs; 
              return_qbs borel (max x1 x2)})"

lemma qbs_morhpism_NaiveRNM[qbs]: "qbs_NaiveRNM \<in> borel\<^sub>Q \<Rightarrow>\<^sub>Q list_qbs borel \<Rightarrow>\<^sub>Q monadP_qbs borel\<^sub>Q"
proof -
  note [qbs] = return_qbs_morphismP bind_qbs_morphismP
  show ?thesis
    by(simp add: qbs_NaiveRNM_def)
qed

theorem qbs_DP_NaiveRNM':
  assumes pos[arith,simp]: "\<epsilon> > 0"
    and "length xs = n" and "length ys = n"
    and adj: "(\<Sum>i<n. \<bar>nth xs i - nth ys i\<bar>) \<le> r"
  shows "DP_divergence\<^sub>Q (qbs_NaiveRNM \<epsilon> xs) (qbs_NaiveRNM \<epsilon> ys) (r * \<epsilon>) = 0"
  using assms(2,3,4)
proof(induct ys arbitrary: xs n r)
  case Nil
  then show ?case
    by simp
next
  case ih:(Cons y ys')
  show ?case (is "?lhs = _")
  proof(cases ys')
    case Nil
    then have "\<exists>a. xs = [a]"
      using ih
      by (metis length_Suc_conv length_greater_0_conv)
    then show ?thesis
      using ih by(auto intro!: qbs_DP_Lap_mechanism)
  next
    case h:(Cons y' ys'')
    note [qbs] = bind_qbs_morphismP return_qbs_morphismP
    obtain x x' xs'' where xs:"xs = x # x' # xs''"
      by (metis h ih(2) ih(3) length_Suc_conv)
    define xs' where "xs' = x' # xs''"
    obtain n' where n:"n = Suc n'"
      using ih(3) by force
    have xs_xs':"xs = x # xs'"
      by(auto simp: xs'_def h xs)
    have [simp]:"length xs' = n'" "length ys' = n'"
      using ih(2) ih(3) by(auto simp: xs_xs' n)
    define r1 where "r1 = \<bar>x - y\<bar>"
    define r2 where "r2 = (\<Sum>j<n'. \<bar>xs' ! j - ys' ! j\<bar>)"
    have "(\<Sum>i<n. \<bar>xs ! i - (y # ys') ! i\<bar>) = \<bar>x - y\<bar> + (\<Sum>i<n'. \<bar>xs' ! i - ys' ! i\<bar>)"
    proof -
      have "(\<Sum>i<n. \<bar>xs ! i - (y # ys') ! i\<bar>) = (\<Sum>i\<in>{0} \<union> {Suc 0..<n}. \<bar>xs ! i - (y # ys') ! i\<bar>)"
        using atLeast1_lessThan_eq_remove0 lessThan_Suc_eq_insert_0 n by fastforce
      also have "... = (\<Sum>i\<in>{0}. \<bar>xs ! i - (y # ys') ! i\<bar>) + (\<Sum>i\<in>{Suc 0..<n}. \<bar>xs ! i - (y # ys') ! i\<bar>)"
        by(subst sum_Un) auto
      also have "... = \<bar>x - y\<bar> + (\<Sum>i<n'. \<bar>xs ! Suc i - (y # ys') ! Suc i\<bar>)"
        unfolding n by(subst sum.atLeast_Suc_lessThan_Suc_shift) (simp add: xs_xs' n lessThan_atLeast0)
      finally show ?thesis by(simp add: xs_xs')
    qed
    hence r12[arith,simp]: "r1 + r2 \<le> r" "0 \<le> r1" "0 \<le> r2" "\<bar>x - y\<bar> \<le> r1" "(\<Sum>j<n'. \<bar>xs' ! j - ys' ! j\<bar>) \<le> r2" 
      using ih(4) by(auto simp: r1_def r2_def)

    have "?lhs =
           DP_divergence\<^sub>Q
             (Lap_mechanism\<^sub>Q (1 / \<epsilon>) x \<bind> (\<lambda>x1. qbs_NaiveRNM \<epsilon> xs' \<bind> (\<lambda>x2. return_qbs borel\<^sub>Q (max x1 x2))))
             (Lap_mechanism\<^sub>Q (1 / \<epsilon>) y \<bind> (\<lambda>x1. qbs_NaiveRNM \<epsilon> ys' \<bind> (\<lambda>x2. return_qbs borel\<^sub>Q (max x1 x2))))
             (r * \<epsilon>)"
      by(auto simp: h xs xs'_def)
    also have "... \<le>
            DP_divergence\<^sub>Q
              (Lap_mechanism\<^sub>Q (1 / \<epsilon>) x \<bind> (\<lambda>x1. qbs_NaiveRNM \<epsilon> xs' \<bind> (\<lambda>x2. return_qbs borel\<^sub>Q (max x1 x2))))
              (Lap_mechanism\<^sub>Q (1 / \<epsilon>) y \<bind> (\<lambda>x1. qbs_NaiveRNM \<epsilon> ys' \<bind> (\<lambda>x2. return_qbs borel\<^sub>Q (max x1 x2))))
              (r1 * \<epsilon> + r2 * \<epsilon>)"
      by(auto intro!: DP_qbs_divergence_antimono simp: distrib_right[symmetric])
    also have "... \<le> ereal (0 + 0)"
      by(intro DP_qbs_divergence_compose[of _ qbs_borel _ _ qbs_borel]
               DP_qbs_divergence_dataprocessing[of _ qbs_borel _ _ qbs_borel])
        (auto simp: qbs_DP_Lap_mechanism ih(1))
    finally show ?thesis
      using antisym zero_ereal_def by fastforce
  qed
qed

(* Differential Privacy for the naive RNM algorithm *)
definition adj_naive_RNM :: "real \<Rightarrow> (real list \<times> real list) set" where
"adj_naive_RNM r \<equiv> {(xs,ys). length xs = length ys \<and> (\<Sum>i<length xs. \<bar>nth xs i - nth ys i\<bar>) \<le> r}"

theorem qbs_DP_NaiveRNM:
  assumes pos: "\<epsilon> > 0"
  shows "differential_privacy\<^sub>Q (qbs_NaiveRNM \<epsilon>) (adj_naive_RNM r) (r * \<epsilon>) 0"
proof(safe intro!: DP_qbs_adj_sym[THEN iffD2])
  fix xs ys
  assume *:"(xs, ys) \<in> adj_naive_RNM r"
  let ?n = "length xs"
  have "length xs = ?n" and "length ys = ?n" and "(\<Sum>i<?n. \<bar>nth xs i - nth ys i\<bar>) \<le> r"
    using * by(auto simp: adj_naive_RNM_def)
  from qbs_DP_NaiveRNM'[OF pos this]
  show "DP_inequality\<^sub>Q (qbs_NaiveRNM \<epsilon> xs) (qbs_NaiveRNM \<epsilon> ys) (r * \<epsilon>) 0"
    by simp
qed(auto intro!: symI simp: adj_naive_RNM_def abs_minus_commute)

end