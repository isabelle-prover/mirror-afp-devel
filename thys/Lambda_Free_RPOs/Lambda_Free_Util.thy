(*  Title:       Utilities for Lambda-Free Orders
    Author:      Jasmin Blanchette <jasmin.blanchette at inria.fr>, 2016
    Maintainer:  Jasmin Blanchette <jasmin.blanchette at inria.fr>
*)

section \<open>Utilities for Lambda-Free Orders\<close>

theory Lambda_Free_Util
imports "HOL-Library.Extended_Nat" "HOL-Library.Multiset_Order"
begin

text \<open>
This theory gathers various lemmas that likely belong elsewhere in Isabelle or
the \emph{Archive of Formal Proofs}. Most (but certainly not all) of them are
used to formalize orders on \<open>\<lambda>\<close>-free higher-order terms.
\<close>

subsection \<open>Function Power\<close>

lemma funpow_lesseq_iter:
  fixes f :: "('a::order) \<Rightarrow> 'a"
  assumes mono: "\<And>k. k \<le> f k" and m_le_n: "m \<le> n"
  shows "(f ^^ m) k \<le> (f ^^ n) k"
  using m_le_n by (induct n) (fastforce simp: le_Suc_eq intro: mono order_trans)+

lemma funpow_less_iter:
  fixes f :: "('a::order) \<Rightarrow> 'a"
  assumes mono: "\<And>k. k < f k" and m_lt_n: "m < n"
  shows "(f ^^ m) k < (f ^^ n) k"
  using m_lt_n by (induct n) (auto, blast intro: mono less_trans dest: less_antisym)


subsection \<open>Least Operator\<close>

lemma Least_eq[simp]: "(LEAST y. y = x) = x" and "(LEAST y. x = y) = x" for x :: "'a::order"
  by (blast intro: Least_equality)+

lemma Least_in_nonempty_set_imp_ex:
  fixes f :: "'b \<Rightarrow> ('a::wellorder)"
  assumes
    A_nemp: "A \<noteq> {}" and
    P_least: "P (LEAST y. \<exists>x \<in> A. y = f x)"
  shows "\<exists>x \<in> A. P (f x)"
proof -
  obtain a where a: "a \<in> A"
    using A_nemp by fast
  have "\<exists>x. x \<in> A \<and> (LEAST y. \<exists>x. x \<in> A \<and> y = f x) = f x"
    by (rule LeastI[of _ "f a"]) (fast intro: a)
  thus ?thesis
    by (metis P_least)
qed

lemma Least_eq_0_enat: "P 0 \<Longrightarrow> (LEAST x :: enat. P x) = 0"
  by (simp add: Least_equality)


subsection \<open>Antisymmetric Relations\<close>

lemma irrefl_trans_imp_antisym: "irrefl r \<Longrightarrow> trans r \<Longrightarrow> antisym r"
  unfolding irrefl_def trans_def antisym_def by fast

lemma irreflp_transp_imp_antisymP: "irreflp p \<Longrightarrow> transp p \<Longrightarrow> antisymp p"
  by (fact irrefl_trans_imp_antisym [to_pred])


subsection \<open>Acyclic Relations\<close>

lemma finite_nonempty_ex_succ_imp_cyclic:
  assumes
    fin: "finite A" and
    nemp: "A \<noteq> {}" and
    ex_y: "\<forall>x \<in> A. \<exists>y \<in> A. (y, x) \<in> r"
  shows "\<not> acyclic r"
proof -
  let ?R = "{(x, y). x \<in> A \<and> y \<in> A \<and> (x, y) \<in> r}"

  have R_sub_r: "?R \<subseteq> r"
    by auto

  have "?R \<subseteq> A \<times> A"
    by auto
  hence fin_R: "finite ?R"
    by (auto intro: fin dest!: infinite_super)

  have "\<not> acyclic ?R"
    by (rule notI, drule finite_acyclic_wf[OF fin_R], unfold wf_eq_minimal, drule spec[of _ A],
      use ex_y nemp in blast)
  thus ?thesis
    using R_sub_r acyclic_subset by auto
qed


subsection \<open>Reflexive, Transitive Closure\<close>

lemma relcomp_subset_left_imp_relcomp_trancl_subset_left:
  assumes sub: "R O S \<subseteq> R"
  shows "R O S\<^sup>* \<subseteq> R"
proof
  fix x
  assume "x \<in> R O S\<^sup>*"
  then obtain n where "x \<in> R O S ^^ n"
    using rtrancl_imp_relpow by fastforce
  thus "x \<in> R"
  proof (induct n)
    case (Suc m)
    thus ?case
      by (metis (no_types) O_assoc inf_sup_ord(3) le_iff_sup relcomp_distrib2 relpow.simps(2)
        relpow_commute sub subsetCE)
  qed auto
qed

lemma f_chain_in_rtrancl:
  assumes m_le_n: "m \<le> n" and f_chain: "\<forall>i \<in> {m..<n}. (f i, f (Suc i)) \<in> R"
  shows "(f m, f n) \<in> R\<^sup>*"
proof (rule relpow_imp_rtrancl, rule relpow_fun_conv[THEN iffD2], intro exI conjI)
  let ?g = "\<lambda>i. f (m + i)"
  let ?k = "n - m"

  show "?g 0 = f m"
    by simp
  show "?g ?k = f n"
    using m_le_n by force
  show "(\<forall>i < ?k. (?g i, ?g (Suc i)) \<in> R)"
    by (simp add: f_chain)
qed

lemma f_rev_chain_in_rtrancl:
  assumes m_le_n: "m \<le> n" and f_chain: "\<forall>i \<in> {m..<n}. (f (Suc i), f i) \<in> R"
  shows "(f n, f m) \<in> R\<^sup>*"
  by (rule f_chain_in_rtrancl[OF m_le_n, of "\<lambda>i. f (n + m - i)", simplified])
    (metis f_chain le_add_diff Suc_diff_Suc Suc_leI atLeastLessThan_iff diff_Suc_diff_eq1 diff_less
      le_add1 less_le_trans zero_less_Suc)


subsection \<open>Well-Founded Relations\<close>

lemma wf_app: "wf r \<Longrightarrow> wf {(x, y). (f x, f y) \<in> r}"
  unfolding wf_eq_minimal by (intro allI, drule spec[of _ "f ` Q" for Q]) fast

lemma wfP_app: "wfP p \<Longrightarrow> wfP (\<lambda>x y. p (f x) (f y))"
  unfolding wfP_def by (rule wf_app[of "{(x, y). p x y}" f, simplified])

lemma wf_exists_minimal:
  assumes wf: "wf r" and Q: "Q x"
  shows "\<exists>x. Q x \<and> (\<forall>y. (f y, f x) \<in> r \<longrightarrow> \<not> Q y)"
  using wf_eq_minimal[THEN iffD1, OF wf_app[OF wf], rule_format, of _ "{x. Q x}", simplified, OF Q]
  by blast

lemma wfP_exists_minimal:
  assumes wf: "wfP p" and Q: "Q x"
  shows "\<exists>x. Q x \<and> (\<forall>y. p (f y) (f x) \<longrightarrow> \<not> Q y)"
  by (rule wf_exists_minimal[of "{(x, y). p x y}" Q x, OF wf[unfolded wfP_def] Q, simplified])

lemma finite_irrefl_trans_imp_wf: "finite r \<Longrightarrow> irrefl r \<Longrightarrow> trans r \<Longrightarrow> wf r"
  by (erule finite_acyclic_wf) (simp add: acyclic_irrefl)

lemma finite_irreflp_transp_imp_wfp:
  "finite {(x, y). p x y} \<Longrightarrow> irreflp p \<Longrightarrow> transp p \<Longrightarrow> wfP p"
  using finite_irrefl_trans_imp_wf[of "{(x, y). p x y}"]
  unfolding wfP_def transp_def irreflp_def trans_def irrefl_def mem_Collect_eq prod.case
  by assumption

lemma wf_infinite_down_chain_compatible:
  assumes
    wf_R: "wf R" and
    inf_chain_RS: "\<forall>i. (f (Suc i), f i) \<in> R \<union> S" and
    O_subset: "R O S \<subseteq> R"
  shows "\<exists>k. \<forall>i. (f (Suc (i + k)), f (i + k)) \<in> S"
proof (rule ccontr)
  assume "\<nexists>k. \<forall>i. (f (Suc (i + k)), f (i + k)) \<in> S"
  hence "\<forall>k. \<exists>i. (f (Suc (i + k)), f (i + k)) \<notin> S"
    by blast
  hence "\<forall>k. \<exists>i > k. (f (Suc i), f i) \<notin> S"
    by (metis add.commute add_Suc less_add_Suc1)
  hence "\<forall>k. \<exists>i > k. (f (Suc i), f i) \<in> R"
    using inf_chain_RS by blast
  hence "\<exists>i > k. (f (Suc i), f i) \<in> R \<and> (\<forall>j > k. (f (Suc j), f j) \<in> R \<longrightarrow> j \<ge> i)" for k
    using wf_eq_minimal[THEN iffD1, OF wf_less, rule_format,
      of _ "{i. i > k \<and> (f (Suc i), f i) \<in> R}", simplified]
    by (meson not_less)
  then obtain j_of where
    j_of_gt: "\<And>k. j_of k > k" and
    j_of_in_R: "\<And>k. (f (Suc (j_of k)), f (j_of k)) \<in> R" and
    j_of_min: "\<And>k. \<forall>j > k. (f (Suc j), f j) \<in> R \<longrightarrow> j \<ge> j_of k"
    by moura

  have j_of_min_s: "\<And>k j. j > k \<Longrightarrow> j < j_of k \<Longrightarrow> (f (Suc j), f j) \<in> S"
    using j_of_min inf_chain_RS by fastforce

  define g :: "nat \<Rightarrow> 'a" where "\<And>k. g k = f (Suc ((j_of ^^ k) 0))"

  have between_g[simplified]: "(f ((j_of ^^ (Suc i)) 0), f (Suc ((j_of ^^ i) 0))) \<in> S\<^sup>*" for i
  proof (rule f_rev_chain_in_rtrancl; clarify?)
    show "Suc ((j_of ^^ i) 0) \<le> (j_of ^^ Suc i) 0"
      using j_of_gt by (simp add: Suc_leI)
  next
    fix ia
    assume ia: "ia \<in> {Suc ((j_of ^^ i) 0)..<(j_of ^^ Suc i) 0}"
    have ia_gt: "ia > (j_of ^^ i) 0"
      using ia by auto
    have ia_lt: "ia < j_of ((j_of ^^ i) 0)"
      using ia by auto
    show "(f (Suc ia), f ia) \<in> S"
      by (rule j_of_min_s[OF ia_gt ia_lt])
  qed

  have "\<And>i. (g (Suc i), g i) \<in> R"
    unfolding g_def funpow.simps comp_def
    by (rule subsetD[OF relcomp_subset_left_imp_relcomp_trancl_subset_left[OF O_subset]])
      (rule relcompI[OF j_of_in_R between_g])
  moreover have "\<forall>f. \<exists>i. (f (Suc i), f i) \<notin> R"
    using wf_R[unfolded wf_iff_no_infinite_down_chain] by blast
  ultimately show False
    by blast
qed


subsection \<open>Wellorders\<close>

lemma (in wellorder) exists_minimal:
  fixes x :: 'a
  assumes "P x"
  shows "\<exists>x. P x \<and> (\<forall>y. P y \<longrightarrow> y \<ge> x)"
  using assms by (auto intro: LeastI Least_le)


subsection \<open>Lists\<close>

lemma rev_induct2[consumes 1, case_names Nil snoc]:
  "length xs = length ys \<Longrightarrow> P [] [] \<Longrightarrow>
   (\<And>x xs y ys. length xs = length ys \<Longrightarrow> P xs ys \<Longrightarrow> P (xs @ [x]) (ys @ [y])) \<Longrightarrow> P xs ys"
proof (induct xs arbitrary: ys rule: rev_induct)
  case (snoc x xs ys)
  thus ?case
    by (induct ys rule: rev_induct) simp_all
qed auto

lemma hd_in_set: "length xs \<noteq> 0 \<Longrightarrow> hd xs \<in> set xs"
  by (cases xs) auto

lemma in_lists_iff_set: "xs \<in> lists A \<longleftrightarrow> set xs \<subseteq> A"
  by fast

lemma butlast_append_Cons[simp]: "butlast (xs @ y # ys) = xs @ butlast (y # ys)"
  using butlast_append[of xs "y # ys", simplified] by simp

lemma rev_in_lists[simp]: "rev xs \<in> lists A \<longleftrightarrow> xs \<in> lists A"
  by auto

lemma hd_le_sum_list:
  fixes xs :: "'a::ordered_ab_semigroup_monoid_add_imp_le list"
  assumes "xs \<noteq> []" and "\<forall>i < length xs. xs ! i \<ge> 0"
  shows "hd xs \<le> sum_list xs"
  using assms
  by (induct xs rule: rev_induct, simp_all,
    metis add_cancel_right_left add_increasing2 hd_append2 lessI less_SucI list.sel(1) nth_append
      nth_append_length order_refl self_append_conv2 sum_list.Nil)

lemma sum_list_ge_length_times:
  fixes a :: "'a::{ordered_ab_semigroup_add,semiring_1}"
  assumes "\<forall>i < length xs. xs ! i \<ge> a"
  shows "sum_list xs \<ge> of_nat (length xs) * a"
  using assms
proof (induct xs)
  case (Cons x xs)
  note ih = this(1) and xxs_i_ge_a = this(2)

  have xs_i_ge_a: "\<forall>i < length xs. xs ! i \<ge> a"
    using xxs_i_ge_a by auto

  have "x \<ge> a"
    using xxs_i_ge_a by auto
  thus ?case
    using ih[OF xs_i_ge_a] by (simp add: ring_distribs ordered_ab_semigroup_add_class.add_mono)
qed auto

lemma prod_list_nonneg:
  fixes xs :: "('a :: {ordered_semiring_0,linordered_nonzero_semiring}) list"
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> x \<ge> 0"
  shows "prod_list xs \<ge> 0"
  using assms by (induct xs) auto

lemma zip_append_0_upt:
  "zip (xs @ ys) [0..<length xs + length ys] =
   zip xs [0..<length xs] @ zip ys [length xs..<length xs + length ys]"
proof (induct ys arbitrary: xs)
  case (Cons y ys)
  note ih = this
  show ?case
    using ih[of "xs @ [y]"] by (simp, cases ys, simp, simp add: upt_rec)
qed auto

lemma zip_eq_butlast_last:
  assumes len_gt0: "length xs > 0" and len_eq: "length xs = length ys"
  shows "zip xs ys = zip (butlast xs) (butlast ys) @ [(last xs, last ys)]"
  using len_eq len_gt0 by (induct rule: list_induct2) auto


subsection \<open>Extended Natural Numbers\<close>

lemma the_enat_0[simp]: "the_enat 0 = 0"
  by (simp add: zero_enat_def)

lemma the_enat_1[simp]: "the_enat 1 = 1"
  by (simp add: one_enat_def)

lemma enat_le_minus_1_imp_lt: "m \<le> n - 1 \<Longrightarrow> n \<noteq> \<infinity> \<Longrightarrow> n \<noteq> 0 \<Longrightarrow> m < n" for m n :: enat
  by (cases m; cases n; simp add: zero_enat_def one_enat_def)

lemma enat_diff_diff_eq: "k - m - n = k - (m + n)" for k m n :: enat
  by (cases k; cases m; cases n) auto

lemma enat_sub_add_same[intro]: "n \<le> m \<Longrightarrow> m = m - n + n" for m n :: enat
  by (cases m; cases n) auto

lemma enat_the_enat_iden[simp]: "n \<noteq> \<infinity> \<Longrightarrow> enat (the_enat n) = n"
  by auto

lemma the_enat_minus_nat: "m \<noteq> \<infinity> \<Longrightarrow> the_enat (m - enat n) = the_enat m - n"
  by auto

lemma enat_the_enat_le: "enat (the_enat x) \<le> x"
  by (cases x; simp)

lemma enat_the_enat_minus_le: "enat (the_enat (x - y)) \<le> x"
  by (cases x; cases y; simp)

lemma enat_le_imp_minus_le: "k \<le> m \<Longrightarrow> k - n \<le> m" for k m n :: enat
  by (metis Groups.add_ac(2) enat_diff_diff_eq enat_ord_simps(3) enat_sub_add_same
    enat_the_enat_iden enat_the_enat_minus_le idiff_0_right idiff_infinity idiff_infinity_right
    order_trans_rules(23) plus_enat_simps(3))

lemma add_diff_assoc2_enat: "m \<ge> n \<Longrightarrow> m - n + p = m + p - n" for m n p :: enat
  by (cases m; cases n; cases p; auto)

lemma enat_mult_minus_distrib: "enat x * (y - z) = enat x * y - enat x * z"
  by (cases y; cases z; auto simp: enat_0 right_diff_distrib')


subsection \<open>Multisets\<close>

declare
  filter_eq_replicate_mset [simp]
  image_mset_subseteq_mono [intro]
  count_gt_imp_in_mset [intro]

end
