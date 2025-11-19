(*
 Title: differential_privacy_Standard.thy
 Author: Tetsuya Sato
*)

theory Differential_Privacy_Standard
  imports
    "Differential_Privacy_Laplace_Mechanism_Multi"
    "L1_norm_list"
    "HOL.Transitive_Closure"
begin

section \<open>Formalization of Differential privacy\<close>

text \<open>AFDP in this section means the textbook "The Algorithmic Foundations of Differential Privacy"written by Cynthia Dwork and Aaron Roth.\<close>

subsection \<open>Predicate of Differential privacy\<close>

paragraph \<open>The inequality for DP (cf. [Def 2.4, AFDP])\<close>

definition DP_inequality:: "'a measure \<Rightarrow> 'a measure \<Rightarrow> real \<Rightarrow> real \<Rightarrow> bool"where
  "DP_inequality M N \<epsilon> \<delta> \<equiv> (\<forall> A \<in> sets M. measure M A \<le> (exp \<epsilon>) * measure N A + \<delta>)"

paragraph \<open>The divergence for DP (cf. [Barthe \& Olmedo, ICALP 2013])\<close>

proposition DP_inequality_cong_DP_divergence:
  shows "DP_inequality M N \<epsilon> \<delta> \<longleftrightarrow> DP_divergence M N \<epsilon> \<le> \<delta>"
  by(auto simp: DP_divergence_forall[THEN sym] DP_inequality_def)

corollary DP_inequality_zero:
  assumes "M \<in> space (prob_algebra L)"
    and "N \<in> space (prob_algebra L)"
    and "DP_inequality M N 0 0"
  shows "M = N"
  using assms DP_divergence_zero unfolding DP_inequality_cong_DP_divergence by auto

paragraph \<open>Definition of the standard differential privacy with adjacency, and its basic properties\<close>

text \<open> We first we abstract the domain of database and the adjacency relations. later we instantiate them according to the textbook.\<close>

definition differential_privacy :: "('a \<Rightarrow> 'b measure) \<Rightarrow> ('a rel) \<Rightarrow> real \<Rightarrow> real \<Rightarrow> bool "where
  "differential_privacy M adj \<epsilon> \<delta> \<equiv> \<forall>(d1,d2)\<in>adj. DP_inequality (M d1) (M d2) \<epsilon> \<delta> \<and> DP_inequality (M d2) (M d1) \<epsilon> \<delta>"

(*TODO: DP for pmf/spmf*)

lemma differential_privacy_adj_sym:
  assumes "sym adj"
  shows "differential_privacy M adj \<epsilon> \<delta> \<longleftrightarrow> (\<forall> (d1,d2) \<in> adj. DP_inequality (M d1) (M d2) \<epsilon> \<delta>)"
  using assms by(auto simp: differential_privacy_def sym_def)

lemma differential_privacy_symmetrize:
  assumes "differential_privacy M adj \<epsilon> \<delta>"
  shows "differential_privacy M (adj \<union> adj\<inverse>) \<epsilon> \<delta>"
  using assms unfolding differential_privacy_def by blast

lemma differential_privacy_restrict:
  assumes "differential_privacy M adj \<epsilon> \<delta>"
    and "adj' \<subseteq> adj"
  shows "differential_privacy M adj' \<epsilon> \<delta>"
  using assms unfolding differential_privacy_def by blast

paragraph \<open>Lemmas for group privacy (cf. [Theorem 2.2, AFDP])\<close>

lemma pure_differential_privacy_comp:
  assumes "adj1 \<subseteq> (space X) \<times> (space X)"
    and "adj2 \<subseteq> (space X) \<times> (space X)"
    and "differential_privacy M adj1 \<epsilon>1 0"
    and "differential_privacy M adj2 \<epsilon>2 0"
    and M:"M \<in> X \<rightarrow>\<^sub>M (prob_algebra R)"
  shows "differential_privacy M (adj1 O adj2) (\<epsilon>1 + \<epsilon>2) 0"
  using assms unfolding differential_privacy_def
proof(intro ballI)
  note [measurable] = M
  fix x assume a1: "\<forall>(d1, d2)\<in> adj1. DP_inequality (M d1) (M d2) \<epsilon>1 0 \<and> DP_inequality (M d2) (M d1) \<epsilon>1 0"
    and a2: "\<forall>(d2, d3)\<in> adj2. DP_inequality (M d2) (M d3) \<epsilon>2 0 \<and> DP_inequality (M d3) (M d2) \<epsilon>2 0"
    and "x \<in> (adj1 O adj2)"
  then obtain d1 d2 d3
    where x: "x = (d1,d3)"and a: "(d1,d2) \<in>Restr adj1 (space X) "and b: "(d2,d3) \<in>Restr adj2 (space X) "
    using assms by blast
  then have "DP_inequality (M d1) (M d2) \<epsilon>1 0" "DP_inequality (M d2) (M d1) \<epsilon>1 0" "DP_inequality (M d2) (M d3) \<epsilon>2 0" "DP_inequality (M d3) (M d2) \<epsilon>2 0"
    using a1 a2 by auto
  moreover have "M d1 \<in> space (prob_algebra R)" "M d2 \<in> space (prob_algebra R)" "M d3 \<in> space (prob_algebra R)"
    using a b by(auto intro!: measurable_space[OF M])
  ultimately have 1: "DP_inequality (M d1) (M d3) (\<epsilon>1 + \<epsilon>2) 0" and "DP_inequality (M d3) (M d1) (\<epsilon>2 + \<epsilon>1) 0"
    unfolding DP_inequality_cong_DP_divergence zero_ereal_def[symmetric] by(intro DP_divergence_transitivity[of _  "(M d2)"],auto)+
  hence "DP_inequality (M d3) (M d1) (\<epsilon>1 + \<epsilon>2) 0"
    by argo
  with 1 show "case x of (d1, d2) \<Rightarrow> DP_inequality (M d1) (M d2) (\<epsilon>1 + \<epsilon>2) 0 \<and> DP_inequality (M d2) (M d1) (\<epsilon>1 + \<epsilon>2) 0"
    unfolding x case_prod_beta by auto
qed

lemma adj_trans_k:
  assumes "adj \<subseteq> A \<times> A"
    and "0 < k"
  shows "(adj ^^ k) \<subseteq> A \<times> A"
  using assms(2) by (induction k)(use assms(1) in fastforce)+

lemma pure_differential_privacy_trans_k:
  assumes "adj \<subseteq> (space X) \<times> (space X)"
    and "differential_privacy M adj \<epsilon> 0"
    and M[measurable]:"M \<in> X \<rightarrow>\<^sub>M (prob_algebra R)"
  shows "differential_privacy M (adj ^^ k) (k * \<epsilon>) 0"
proof(induction k)
  case 0
  then show ?case
    by(auto simp: differential_privacy_adj_sym sym_on_def DP_divergence_reflexivity DP_inequality_cong_DP_divergence)
next
  case (Suc k)
  then show ?case
  proof(cases k)
    case 0
    then show ?thesis
      using assms(1) assms(2) inf.orderE mult_eq_1_iff by fastforce
  next
    case (Suc l)
    then have 1: "0 < k"
      by auto
    have 2: "((Suc k) * \<epsilon>) = (k * \<epsilon>) + \<epsilon> "
      by (simp add: mult.commute nat_distrib(2))
    show ?thesis
      unfolding relpow.simps 2
    proof(subst pure_differential_privacy_comp[where X = X and R = R])
      show "adj ^^ k \<subseteq> space X \<times> space X"
        by(unfold Suc, rule adj_trans_k, auto simp: assms)
    qed(auto simp: assms Suc.IH)
  qed
qed

paragraph \<open>The relaxation of parameters (obvious in the pencil and paper manner).\<close>

lemma DP_inequality_relax:
  assumes 1: "\<epsilon> \<le> \<epsilon>'" and 2: "\<delta> \<le> \<delta>'"
    and DP: "DP_inequality M N \<epsilon> \<delta>"
  shows "DP_inequality M N \<epsilon>' \<delta>'"
  unfolding DP_inequality_def
proof
  fix A assume A: "A \<in> sets M "
  hence "measure M A \<le> exp \<epsilon> * measure N A + \<delta>"
    using DP by(auto simp: DP_inequality_def)
  also have "... \<le> exp \<epsilon>' * measure N A + \<delta>'"
    by (auto simp: add_mono mult_right_mono 1 2)
  finally show "measure M A \<le> exp \<epsilon>' * measure N A + \<delta>'".
qed

proposition differential_privacy_relax:
  assumes DP:"differential_privacy M adj \<epsilon> \<delta>"
    and 1: "\<epsilon> \<le> \<epsilon>'"and 2: "\<delta> \<le> \<delta>'"
  shows "differential_privacy M adj \<epsilon>' \<delta>'"
  using DP DP_inequality_relax [OF 1 2] unfolding differential_privacy_def by blast

paragraph \<open>Stability for post-processing (cf. [Prop 2.1, AFDP])\<close>

proposition differential_privacy_postprocessing:
  assumes "\<epsilon> \<ge> 0" 
    and "differential_privacy M adj \<epsilon> \<delta>"
    and M: "M \<in> X \<rightarrow>\<^sub>M (prob_algebra R)"
    and f: "f \<in> R \<rightarrow>\<^sub>M (prob_algebra R')" (*probabilistic post-process*)
    and "adj \<subseteq> (space X) \<times> (space X)"
  shows "differential_privacy (\<lambda>x. do{y \<leftarrow> M x; f y}) adj \<epsilon> \<delta>"
proof(subst differential_privacy_def)
  note [measurable] = M f
  note [arith] = assms(1)
  show "\<forall>(d1, d2)\<in> adj. DP_inequality (M d1 \<bind> f) (M d2 \<bind> f) \<epsilon> \<delta> \<and> DP_inequality (M d2 \<bind> f) (M d1 \<bind> f) \<epsilon> \<delta> "
  proof
    fix x ::"'a \<times> 'a"assume x:"x \<in> adj"
    then obtain d1 d2 ::'a
      where x: "x = (d1,d2)"
        and d1: "d1 \<in> space X"
        and d2: "d2 \<in> space X"
        and d: "(d1,d2) \<in> Restr adj (space X)"
        and div1[simp]: "DP_divergence (M d1) (M d2) \<epsilon> \<le> \<delta> "
        and div2[simp]: "DP_divergence (M d2) (M d1) \<epsilon> \<le> \<delta>"
      using DP_inequality_cong_DP_divergence assms differential_privacy_def[of M adj \<epsilon> \<delta>] by fastforce+
    hence Md1[simp]: "M d1 \<in> space (prob_algebra R)"and Md2[simp]: "M d2 \<in> space (prob_algebra R)"
      by(metis M measurable_space)+
    have "DP_divergence (M d1 \<bind> f) (M d2 \<bind> f) \<epsilon> \<le> \<delta>"
      by(auto simp: DP_divergence_postprocessing[where L = R and K = R'])
    moreover have "DP_divergence (M d2 \<bind> f) (M d1 \<bind> f) \<epsilon> \<le> \<delta>"
      by(auto simp: DP_divergence_postprocessing[where L = R and K = R'])
    ultimately show "case x of (d1,d2) \<Rightarrow> DP_inequality (M d1 \<bind> f) (M d2 \<bind> f) \<epsilon> \<delta> \<and> DP_inequality (M d2 \<bind> f) (M d1 \<bind> f) \<epsilon> \<delta>"
      unfolding DP_inequality_cong_DP_divergence using x by auto
  qed
qed

corollary differential_privacy_postprocessing_deterministic:
  assumes "\<epsilon> \<ge> 0"
    and "differential_privacy M adj \<epsilon> \<delta>"
    and M[measurable]: "M \<in> X \<rightarrow>\<^sub>M (prob_algebra R)"
    and f[measurable]: "f \<in> R \<rightarrow>\<^sub>M R'" (*deterministic post-process*)
    and "adj \<subseteq> (space X) \<times> (space X)"
  shows "differential_privacy (\<lambda>x. do{y \<leftarrow> M x; return R' (f y) } ) adj \<epsilon> \<delta>"
  by(rule differential_privacy_postprocessing[where f = "(\<lambda> y. return R' (f y))"and X = X and R = R and R'= R'],auto simp: assms)

text \<open> To handle the sensitivity, we prepare the conversions of adjacency relations by pre-processing. \<close>

lemma differential_privacy_preprocessing:
  assumes "\<epsilon> \<ge> 0"
    and "differential_privacy M adj \<epsilon> \<delta>"
    and f: "f \<in> X' \<rightarrow>\<^sub>M X" (*deterministic pre-process*)
    and ftr: "\<forall>(x,y) \<in> adj'. (f x, f y) \<in> adj"
    and "adj \<subseteq> (space X) \<times> (space X)"
    and "adj' \<subseteq> (space X') \<times> (space X')"
  shows "differential_privacy (M o f) adj' \<epsilon> \<delta>"
proof(subst differential_privacy_def)
  note [measurable] = f
  show "\<forall>(d1, d2)\<in> adj'. DP_inequality ((M \<circ> f) d1) ((M \<circ> f) d2) \<epsilon> \<delta> \<and> DP_inequality ((M \<circ> f) d2) ((M \<circ> f) d1) \<epsilon> \<delta>"
  proof
    fix x ::"'c \<times> 'c"assume x:"x \<in> adj'"
    then obtain d1 d2 ::'c where x: "x = (d1,d2)"and d1: "d1 \<in> space X'"and d2: "d2 \<in> space X'"and d: "(d1,d2) \<in> Restr adj' (space X')"
      using assms by auto
    hence fd: "(f d1, f d2) \<in> adj"
      using ftr by auto
    hence "DP_inequality (M (f d1)) (M (f d2)) \<epsilon> \<delta> \<and> DP_inequality (M (f d2)) (M (f d1)) \<epsilon> \<delta>"
      using differential_privacy_def[of M adj \<epsilon> \<delta>] assms by blast
    thus "case x of (d1,d2) \<Rightarrow> DP_inequality ((M o f) d1) ((M o f) d2) \<epsilon> \<delta> \<and> DP_inequality ((M o f) d2) ((M o f) d1) \<epsilon> \<delta>"
      using x by auto
  qed
qed

paragraph \<open> "Adaptive"composition (cf. [Theorem B.1, AFDP])\<close>

proposition differential_privacy_composition_adaptive:
  assumes "\<epsilon> \<ge> 0"
    and "\<epsilon>' \<ge> 0"
    and M: "M \<in> X \<rightarrow>\<^sub>M (prob_algebra Y)"
    and DPM: "differential_privacy M adj \<epsilon> \<delta>"
    and N: "N \<in> (X \<Otimes>\<^sub>M Y) \<rightarrow>\<^sub>M (prob_algebra Z)"
    and DPN: "\<forall> y \<in> space Y. differential_privacy (\<lambda> x. N (x,y)) adj \<epsilon>' \<delta>'"
    and "adj \<subseteq> (space X) \<times> (space X)"
  shows "differential_privacy (\<lambda>x. do{y \<leftarrow> M x; N (x, y)}) adj (\<epsilon> + \<epsilon>') (\<delta> + \<delta>')"
proof(subst differential_privacy_def)
  note [measurable] = M N
  note [simp] = space_pair_measure
  show "\<forall>(d1, d2)\<in>adj.
 DP_inequality (M d1 \<bind> (\<lambda>y. N (d1, y))) (M d2 \<bind> (\<lambda>y. N (d2, y))) (\<epsilon> + \<epsilon>') (\<delta> + \<delta>') \<and>
 DP_inequality (M d2 \<bind> (\<lambda>y. N (d2, y))) (M d1 \<bind> (\<lambda>y. N (d1, y))) (\<epsilon> + \<epsilon>') (\<delta> + \<delta>') "
  proof
    fix x ::"'a \<times> 'a"
    assume x:"x \<in> adj"
    then obtain x1 x2 ::'a
      where x: "x = (x1,x2)"
        and x1: "x1 \<in> space X"
        and x2: "x2 \<in> space X"
        and x': "(x1,x2) \<in> Restr adj (space X)"
        and div1: "DP_divergence (M x1) (M x2) \<epsilon> \<le> \<delta> "
        and div2: "DP_divergence (M x2) (M x1) \<epsilon> \<le> \<delta>"
      using DP_inequality_cong_DP_divergence assms differential_privacy_def[of M adj \<epsilon> \<delta>] by fastforce+
    hence N1: "(\<lambda>y. N (x1, y)) \<in> Y \<rightarrow>\<^sub>M prob_algebra Z"and N2: "(\<lambda>y. N (x2, y)) \<in> Y \<rightarrow>\<^sub>M prob_algebra Z"
      by auto
    have Mx1: "(M x1)\<in> space(prob_algebra Y)"and Mx2: "(M x2)\<in> space(prob_algebra Y)"
      by (meson measurable_space M x1 x2)+
    {
      fix y::'b assume y: "y \<in> space Y"
      have "DP_divergence (N (x1, y)) (N (x2, y)) \<epsilon>' \<le> \<delta>' \<and> DP_divergence (N (x2, y)) (N (x1, y)) \<epsilon>' \<le> \<delta>'"
        using DPN DP_inequality_cong_DP_divergence differential_privacy_def[of "(\<lambda> x. N (x,y))"adj \<epsilon>' \<delta>'] x1 x2 x' y by fastforce+
    }
    hence p1: "\<forall>y \<in> space Y. DP_divergence (N (x1, y)) (N (x2, y)) \<epsilon>' \<le> \<delta>'"and p2: "\<forall>y \<in> space Y. DP_divergence (N (x2, y)) (N (x1, y)) \<epsilon>' \<le> \<delta>'"
      by auto
    hence "DP_divergence ( M x1 \<bind> (\<lambda>y. N (x1, y))) ( M x2 \<bind> (\<lambda>y. N (x2, y))) (\<epsilon> + \<epsilon>') \<le> (\<delta> + \<delta>') \<and> DP_divergence ( M x2 \<bind> (\<lambda>y. N (x2, y))) ( M x1 \<bind> (\<lambda>y. N (x1, y))) (\<epsilon> + \<epsilon>') \<le> (\<delta> + \<delta>')"
      using DP_divergence_composability[of "M x1 "Y "M x2 ""(\<lambda>y. N (x1, y))"Z "(\<lambda>y. N (x2, y))"\<epsilon> \<delta> \<epsilon>' \<delta>' ,OF Mx1 Mx2 N1 N2 div1 _ assms(1,2)]
        DP_divergence_composability[of "M x2 "Y "M x1 ""(\<lambda>y. N (x2, y))"Z "(\<lambda>y. N (x1, y))"\<epsilon> \<delta> \<epsilon>' \<delta>' ,OF Mx2 Mx1 N2 N1 div2 _ assms(1,2)] by auto
    thus "case x of (x1,x2) \<Rightarrow> DP_inequality ( M x1 \<bind> (\<lambda>y. N (x1, y))) ( M x2 \<bind> (\<lambda>y. N (x2, y))) (\<epsilon> + \<epsilon>') (\<delta> + \<delta>') \<and> DP_inequality ( M x2 \<bind> (\<lambda>y. N (x2, y))) ( M x1 \<bind> (\<lambda>y. N (x1, y))) (\<epsilon> + \<epsilon>') (\<delta> + \<delta>')"
      by (auto simp: x DP_inequality_cong_DP_divergence)
  qed
qed

paragraph \<open> "Sequential"composition [Theorem 3.14, AFDP, generalized] \<close>

proposition differential_privacy_composition_pair:
  assumes "\<epsilon> \<ge> 0"
    and "\<epsilon>' \<ge> 0"
    and DPM: "differential_privacy M adj \<epsilon> \<delta>"
    and M[measurable]: "M \<in> X \<rightarrow>\<^sub>M (prob_algebra Y)"
    and DPN: "differential_privacy N adj \<epsilon>' \<delta>'"
    and N[measurable]: "N \<in> X \<rightarrow>\<^sub>M (prob_algebra Z)"
    and "adj \<subseteq> (space X) \<times> (space X)"
  shows "differential_privacy (\<lambda>x. do{y \<leftarrow> M x; z \<leftarrow> N x; return (Y \<Otimes>\<^sub>M Z) (y,z)} ) adj (\<epsilon> + \<epsilon>') (\<delta> + \<delta>')"
proof-
  have p: "(\<lambda>x. do{y \<leftarrow> M x; z \<leftarrow> N x; return (Y \<Otimes>\<^sub>M Z) (y,z)} ) = (\<lambda>x. M x \<bind> (\<lambda>y. case (x, y) of (x, y) \<Rightarrow> N x \<bind> (\<lambda>z. return (Y \<Otimes>\<^sub>M Z) (y, z))))"
    by auto
  have "\<And>y. y \<in> space Y \<Longrightarrow> differential_privacy (\<lambda>x. N x \<bind> (\<lambda>z. return (Y \<Otimes>\<^sub>M Z) (y, z))) adj \<epsilon>' \<delta>'"
  proof-
    fix y assume [measurable]: "y \<in> space Y"
    hence m: "(\<lambda>x. N x \<bind> (\<lambda>z. return (Y \<Otimes>\<^sub>M Z) (y, z))) \<in> X \<rightarrow>\<^sub>M prob_algebra (Y \<Otimes>\<^sub>M Z)"
      by auto
    show "differential_privacy (\<lambda>x. N x \<bind> (\<lambda>z. return (Y \<Otimes>\<^sub>M Z) (y, z))) adj \<epsilon>' \<delta>'"
      by(rule differential_privacy_postprocessing[where f = "(\<lambda>z. return (Y \<Otimes>\<^sub>M Z) (y, z))" and R' = "(Y \<Otimes>\<^sub>M Z)" and R = "Z" and X = X], auto simp: assms)
  qed
  thus ?thesis unfolding p using assms
    by(subst differential_privacy_composition_adaptive[where N ="(\<lambda>(x,y). N x \<bind> (\<lambda>z. return (Y \<Otimes>\<^sub>M Z) (y, z)) )"and Z = "(Y \<Otimes>\<^sub>M Z)"], auto ) (*takes a bit long time*)
qed

paragraph \<open> Laplace mechanism (1-dimensional version) (cf. [Def. 3.3 and Thm 3.6, AFDP]) \<close>

locale Lap_Mechanism_1dim =
  fixes X::"'a measure"
    and f::"'a \<Rightarrow> real"
    and adj::"('a rel)"
  assumes [measurable]: "f \<in> X \<rightarrow>\<^sub>M borel"(*A query to add noise*)
    and adj: "adj \<subseteq> (space X) \<times> (space X)"
begin

definition sensitivity:: ereal where
  "sensitivity = Sup{ ereal \<bar>(f x) - (f y)\<bar> | x y::'a. x \<in> space X \<and> y \<in> space X \<and> (x,y) \<in> adj }"

definition LapMech_1dim::"real \<Rightarrow> 'a \<Rightarrow> real measure"where
  "LapMech_1dim \<epsilon> x = Lap_dist ((real_of_ereal sensitivity) / \<epsilon>) (f x)"

lemma measurable_LapMech_1dim[measurable]:
  shows "LapMech_1dim \<epsilon> \<in> X \<rightarrow>\<^sub>M prob_algebra borel"
  unfolding LapMech_1dim_def by auto

lemma LapMech_1dim_def2:
  shows "LapMech_1dim \<epsilon> x = do{y \<leftarrow> Lap_dist0 ((real_of_ereal sensitivity) / \<epsilon>); return borel (f x + y) }"
  using Lap_dist_def2 LapMech_1dim_def by auto

proposition differential_privacy_LapMech_1dim:
  assumes pose: "0 < \<epsilon> "and "sensitivity > 0"and "sensitivity < \<infinity>"
  shows "differential_privacy (LapMech_1dim \<epsilon>) adj \<epsilon> 0"
proof(subst differential_privacy_def)
  show "\<forall>(d1::'a, d2::'a)\<in>adj.
 DP_inequality (LapMech_1dim \<epsilon> d1) (LapMech_1dim \<epsilon> d2) \<epsilon> (0::real) \<and>
 DP_inequality (LapMech_1dim \<epsilon> d2) (LapMech_1dim \<epsilon> d1) \<epsilon> (0::real)"
  proof
    fix x::"'a \<times> 'a"assume "x \<in> adj"
    then obtain d1 d2 where x: "x = (d1,d2)"and "(d1,d2) \<in> adj "and "d1 \<in> (space X)"and "d2 \<in> (space X)"
      using adj by blast
    with assms have "\<bar>(f d1) - (f d2)\<bar> \<le> sensitivity "
      unfolding sensitivity_def using le_Sup_iff by blast
    with assms have q: "\<bar>(f d1) - (f d2)\<bar> \<le> real_of_ereal sensitivity"
      by (auto simp: ereal_le_real_iff)
    hence q2: "\<bar>(f d2) - (f d1)\<bar> \<le> real_of_ereal sensitivity"
      by auto
    from assms have pos: "0 < (real_of_ereal sensitivity)/\<epsilon>"
      by (auto simp: zero_less_real_of_ereal)
    have a1: "DP_inequality (LapMech_1dim (\<epsilon>::real) d1) (LapMech_1dim \<epsilon> d2) \<epsilon> (0::real)"
      by (auto simp: DP_divergence_Lap_dist'_eps pose q DP_inequality_cong_DP_divergence LapMech_1dim_def )
    have a2: "DP_inequality (LapMech_1dim (\<epsilon>::real) d2) (LapMech_1dim \<epsilon> d1) \<epsilon> (0::real)"
      by (auto simp: DP_divergence_Lap_dist'_eps pose q2 DP_inequality_cong_DP_divergence LapMech_1dim_def )
    from a1 a2 show "case x of
 (d1::'a, d2::'a) \<Rightarrow>
 DP_inequality (LapMech_1dim \<epsilon> d1) (LapMech_1dim \<epsilon> d2) \<epsilon> (0::real) \<and>
 DP_inequality (LapMech_1dim \<epsilon> d2) (LapMech_1dim \<epsilon> d1) \<epsilon> (0::real)"
      by(auto simp:x)
  qed
qed

(*Future work: accuracy*)

end (* end-of-locale*)

paragraph \<open> Laplace mechanism (generalized version) (cf. [Def. 3.3 and Thm 3.6, AFDP]) \<close>

locale Lap_Mechanism_list =
  fixes X::"'a measure"
    and f::"'a \<Rightarrow> real list"
    and adj::"('a rel)"
    and m::nat (* length of output *)
  assumes [measurable]: "f \<in> X \<rightarrow>\<^sub>M (listM borel)"(*A query to add noise*)
    and len: "\<And> x. x \<in> space X \<Longrightarrow> length (f x) = m"
    and adj: "adj \<subseteq> (space X) \<times> (space X)"
begin

definition sensitivity:: ereal where
  "sensitivity = Sup{ ereal ( \<Sum> i\<in>{1..m}. \<bar> nth (f x) (i-1) - nth (f y) (i-1) \<bar>) | x y::'a. x \<in> space X \<and> y \<in> space X \<and> (x,y) \<in> adj}"

definition LapMech_list::"real \<Rightarrow> 'a \<Rightarrow> (real list) measure"where
  "LapMech_list \<epsilon> x = Lap_dist_list ((real_of_ereal sensitivity) / \<epsilon>) (f x)"

(* corresponds to [Def 3.3, AFDP] *)
lemma LapMech_list_def2:
  assumes "x \<in> space X"
  shows "LapMech_list \<epsilon> x = do{ xs \<leftarrow> Lap_dist0_list (real_of_ereal sensitivity / \<epsilon>) m; return (listM borel) (map2 (+) (f x) xs)}"
  using Lap_dist_list_def2 len[OF assms] LapMech_list_def by auto

(* corresponds to [Thm 3.6, AFDP] *)
proposition differential_privacy_LapMech_list:
  assumes pose: "\<epsilon> > 0"
    and "sensitivity > 0"
    and "sensitivity < \<infinity>"
  shows "differential_privacy (LapMech_list \<epsilon>) adj \<epsilon> 0"
proof(subst differential_privacy_def)
  show "\<forall>(d1, d2)\<in> adj. DP_inequality (LapMech_list \<epsilon> d1) (LapMech_list \<epsilon> d2) \<epsilon> 0
  \<and> DP_inequality (LapMech_list \<epsilon> d2) (LapMech_list \<epsilon> d1) \<epsilon> 0"
  proof(rule ballI)
    fix x::"'a \<times> 'a"assume "x \<in> adj"
    then obtain d1 d2::'a
      where x: "x = (d1,d2)"
        and "(d1,d2) \<in> adj "
        and d1: "d1 \<in> (space X)"
        and d2: "d2 \<in> (space X)"
      using adj by blast
    with assms have "(\<Sum> i\<in>{1..m}. \<bar> nth (f d1) (i-1) - nth (f d2) (i-1) \<bar>) \<le> sensitivity "
      unfolding sensitivity_def using le_Sup_iff by blast
    with assms have q: "(\<Sum> i\<in>{1..m}. \<bar> nth (f d1) (i-1) - nth (f d2) (i-1) \<bar>) \<le> real_of_ereal sensitivity"
      by (auto simp: ereal_le_real_iff)
    hence q2: "(\<Sum> i\<in>{1..m}. \<bar> nth (f d2) (i-1) - nth (f d1) (i-1) \<bar>) \<le> real_of_ereal sensitivity"
      by (simp add: abs_minus_commute)
    from assms have pos: "0 \<le> (real_of_ereal sensitivity)"
      by (simp add: real_of_ereal_pos)
    have fd1: "length (f d1) = m"and fd2: "length (f d2) = m"
      using len d1 d2 by auto
    have a1: "DP_inequality (LapMech_list (\<epsilon>::real) d1) (LapMech_list \<epsilon> d2) \<epsilon> 0"
      using DP_Lap_dist_list_eps[OF pose fd1 fd2 q pos] by (simp add: LapMech_list_def DP_inequality_cong_DP_divergence zero_ereal_def)
    have a2: "DP_inequality (LapMech_list (\<epsilon>::real) d2) (LapMech_list \<epsilon> d1) \<epsilon> 0"
      using DP_Lap_dist_list_eps[OF pose fd2 fd1 q2 pos] by (simp add: LapMech_list_def DP_inequality_cong_DP_divergence zero_ereal_def)
    show "case x of (d1, d2) \<Rightarrow> DP_inequality (local.LapMech_list \<epsilon> d1) (local.LapMech_list \<epsilon> d2) \<epsilon> 0 \<and> DP_inequality (local.LapMech_list \<epsilon> d2) (local.LapMech_list \<epsilon> d1) \<epsilon> 0"
      by(auto simp:x a1 a2 )
  qed
    (*Future work: accuracy*)(* corresponds to [Thm 3.8, AFDP] *)
qed

end (*end of locale*)

subsection \<open> Formalization of Results in [AFDP]\<close>

text\<open>We finally instantiate @{term X} and @{term adj} according to the textbook [AFDP] \<close>

locale results_AFDP =
  fixes n ::nat (* length of input *)
begin

interpretation L1_norm_list "(UNIV::nat set)" "(\<lambda> x y. \<bar>int x - int y\<bar>)" n
  by(unfold_locales,auto)

definition sp_Dataset :: "nat list measure"where
  "sp_Dataset \<equiv> restrict_space (listM (count_space UNIV)) space_L1_norm_list"

definition adj_L1_norm :: "(nat list \<times> nat list) set"where
  "adj_L1_norm \<equiv> {(xs,ys)| xs ys. xs \<in> space sp_Dataset \<and> ys \<in> space sp_Dataset \<and> dist_L1_norm_list xs ys \<le> 1}"

definition dist_L1_norm :: "nat \<Rightarrow> (nat list \<times> nat list) set"where
  "dist_L1_norm k \<equiv> {(xs,ys)| xs ys. xs \<in> space sp_Dataset \<and> ys \<in> space sp_Dataset \<and> dist_L1_norm_list xs ys \<le> k}"

abbreviation
  "differential_privacy_AFDP M \<epsilon> \<delta> \<equiv> differential_privacy M adj_L1_norm \<epsilon> \<delta>"

lemma adj_sub: "adj_L1_norm \<subseteq> space sp_Dataset \<times> space sp_Dataset"
  unfolding sp_Dataset_def adj_L1_norm_def by blast

lemmas differential_privacy_relax_AFDP' =
  differential_privacy_relax[of  _  adj_L1_norm]
  (* postprocessing [Prop 2.1, AFDP] *)
lemmas differential_privacy_postprocessing_AFDP =
  differential_privacy_postprocessing[of _ _  adj_L1_norm, OF _ _ _ _  adj_sub]
  (* "adaptive"composition [Theorem B.1, AFDP] *)
lemmas differential_privacy_composition_adaptive_AFDP =
  differential_privacy_composition_adaptive[of _ _ _ _ _  adj_L1_norm, OF _ _ _ _ _ _ adj_sub]
  (* "sequential"composition [Theorem 3.14, AFDP, generalized] *)
lemmas differential_privacy_composition_pair_AFDP =
  differential_privacy_composition_pair[of _ _ _ adj_L1_norm, OF _ _ _ _ _ _ adj_sub]

text\<open>Group privacy [Theorem 2.2, AFDP].\<close>

lemma group_privacy_AFDP:
  assumes M: "M \<in> sp_Dataset \<rightarrow>\<^sub>M prob_algebra Y"
    and DP: " differential_privacy_AFDP M \<epsilon> 0"
  shows "differential_privacy M (dist_L1_norm k) (real k * \<epsilon>) 0" 
proof(rule differential_privacy_restrict[where adj = "adj_L1_norm ^^ k"and adj' = "dist_L1_norm k"])
  show "differential_privacy M (adj_L1_norm ^^ k) (real k * \<epsilon>) 0"
    by(rule pure_differential_privacy_trans_k[OF adj_sub DP M])
  show "dist_L1_norm k \<subseteq> adj_L1_norm ^^ k"
    using L1_adj_iterate[of _ n _ k] unfolding space_restrict_space space_listM space_count_space lists_UNIV adj_L1_norm_def dist_L1_norm_def sp_Dataset_def by auto
qed


context
  fixes f::"nat list \<Rightarrow> real"
  assumes [measurable]: "f \<in> sp_Dataset \<rightarrow>\<^sub>M borel" (*A query to add noise*)
begin

interpretation Lap_Mechanism_1dim "sp_Dataset"f "adj_L1_norm"
  by(unfold_locales,auto simp: adj_sub)

thm LapMech_1dim_def

definition LapMech_1dim_AFDP :: "real \<Rightarrow> nat list \<Rightarrow> real measure"where
  "LapMech_1dim_AFDP \<epsilon> x = do{y \<leftarrow> Lap_dist0 ((real_of_ereal sensitivity) / \<epsilon>); return borel (f x + y) }"

lemma LapMech_1dim_AFDP':
  shows "LapMech_1dim_AFDP = LapMech_1dim"
  unfolding LapMech_1dim_AFDP_def LapMech_1dim_def2 by auto

(* Differential privacy of Laplace mechanism, 1-dimensional version [Thm 3.6, AFDP]*)

lemmas differential_privacy_Lap_Mechanism_1dim_AFDP =
  differential_privacy_LapMech_1dim[of _ , simplified LapMech_1dim_AFDP'[symmetric]]

end

context
  fixes f::"nat list \<Rightarrow> real list"
    and m::nat (* length of output *)
  assumes [measurable]: "f \<in> sp_Dataset \<rightarrow>\<^sub>M (listM borel)"(*A query to add noise*)
    and len: "\<And> x. x \<in> space X \<Longrightarrow> length (f x) = m"
begin

interpretation Lap_Mechanism_list "sp_Dataset"f "adj_L1_norm" m
  by(unfold_locales,auto simp: len adj_sub)

definition LapMech_list_AFDP :: "real \<Rightarrow> nat list \<Rightarrow> real list measure"where
  "LapMech_list_AFDP \<epsilon> x = do{ ys \<leftarrow> (Lap_dist0_list(real_of_ereal sensitivity / \<epsilon>) m); return (listM borel) (map2 (+) (f x) ys) }"

thm LapMech_list_def

lemma LapMech_list_AFDP':
  assumes "x \<in> space sp_Dataset"
  shows "LapMech_list_AFDP \<epsilon> x = LapMech_list \<epsilon> x"
  unfolding LapMech_list_AFDP_def LapMech_list_def2[OF assms] by auto

(* Differential privacy of Laplace mechanism [Thm 3.6, AFDP]*)

lemma differential_privacy_Lap_Mechanism_list_AFDP:
  assumes "0 < \<epsilon>"
    and "0 < sensitivity"
    and "sensitivity < \<infinity>"
  shows "differential_privacy_AFDP (LapMech_list_AFDP \<epsilon>) \<epsilon> 0"
proof(subst differential_privacy_def)
  {
    fix d1 d2 assume d: "(d1, d2)\<in> adj_L1_norm"
    then have 1: "d1 \<in> (space sp_Dataset)"and 2: "d2 \<in> (space sp_Dataset)"
      using adj_sub by auto
    have "DP_inequality (LapMech_list_AFDP \<epsilon> d1) (LapMech_list_AFDP \<epsilon> d2) \<epsilon> 0 \<and> DP_inequality (LapMech_list_AFDP \<epsilon> d2) (LapMech_list_AFDP \<epsilon> d1) \<epsilon> 0"
      using differential_privacy_LapMech_list[OF assms(1)] assms(2,3) d
      unfolding LapMech_list_AFDP'[OF 1] LapMech_list_AFDP'[OF 2] differential_privacy_def by blast
  }
  thus "\<forall>(d1, d2)\<in> adj_L1_norm. DP_inequality (LapMech_list_AFDP \<epsilon> d1) (LapMech_list_AFDP \<epsilon> d2) \<epsilon> 0 \<and> DP_inequality (LapMech_list_AFDP \<epsilon> d2) (LapMech_list_AFDP \<epsilon> d1) \<epsilon> 0"
    by blast
qed

end (*end of context*)

end (*end of lcoale*)


end


