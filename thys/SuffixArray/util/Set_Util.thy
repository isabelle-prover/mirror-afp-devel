theory Set_Util
  imports Main
begin

section \<open>Sets\<close>

lemma pigeonhole_principle_advanced:
  assumes "finite A"
  and     "finite B"
  and     "A \<inter> B = {}"
  and     "card A > card B"
  and     "bij_betw f (A \<union> B) (A \<union> B)"
shows " \<exists>a\<in>A. f a \<in> A"
proof (rule ccontr)
  assume "\<not>(\<exists>a\<in>A. f a \<in> A)"
  hence "\<forall>a \<in> A. f a \<notin> A"
    by blast
  hence "\<forall>a\<in>A. f a \<in> B"
    using assms(5) bij_betw_apply by fastforce
  hence "f ` A \<subseteq> B"
    by blast

  have "inj_on f A"
    by (meson assms(5) bij_betw_def inj_on_Un)
  hence "card (f ` A) = card A"
    using card_image by blast
  hence "f ` A = B"
    by (metis \<open>f ` A \<subseteq> B\<close> assms(2,4) card_mono leD)
  hence "card B = card A"
    using \<open>card (f ` A) = card A\<close> by blast
  then show False
    using assms(4) by linarith
qed

lemma Suc_mod_n_bij_betw:
  "bij_betw (\<lambda>x. Suc x mod n) {0..<n} {0..<n}"
proof (intro bij_betwI')
  fix x y
  assume "x \<in> {0..<n}" "y \<in> {0..<n}"
  then show "(Suc x mod n = Suc y mod n) = (x = y)"
    by (simp add: mod_Suc)
next
  fix x
  assume "x \<in> {0..<n}"
  then show "Suc x mod n \<in> {0..<n}"
    by clarsimp
next
  fix y
  assume "y \<in> {0..<n}"
  then show "\<exists>x\<in>{0..<n}. y = Suc x mod n"
    by (metis atLeastLessThan_iff bot_nat_0.extremum less_nat_zero_code mod_Suc_eq mod_less
              mod_less_divisor mod_self not_gr_zero old.nat.exhaust)
qed



lemma subset_upt_no_Suc:
  assumes "A \<subseteq> {1..<n}"
  and     "\<forall>x\<in>A. Suc x \<notin> A"
  shows "card A \<le> n div 2"
proof (rule ccontr)
  assume "\<not> card A \<le> n div 2"
  hence "n div 2 < card A"
    by auto

  have "\<exists>a\<in>A. Suc a mod n \<in> A"
  proof (rule pigeonhole_principle_advanced[of A "{0..<n} - A" "(\<lambda>x. Suc x mod n)", simplified])
    show "finite A"
      using assms(1) finite_subset by blast
  next
    from card_Diff_subset
    have "card ({0..<n} - A) = card {0..<n} - card A"
      by (metis Diff_subset assms(1) dual_order.trans ivl_diff less_eq_nat.simps(1)
                subset_eq_atLeast0_lessThan_finite)
    moreover
    have "card {0..<n} - card A < card A"
      using \<open>\<not> card A \<le> n div 2\<close> assms by simp
    ultimately show "card ({0..<n} - A) < card A"
      by simp
  next
    have "A \<union> {0..<n} = {0..<n}"
      using assms(1) dual_order.trans by auto
    with Suc_mod_n_bij_betw[of n]
    show "bij_betw (\<lambda>x. Suc x mod n) (A \<union> {0..<n}) (A \<union> {0..<n})"
      by simp
  qed
  then obtain x where
    "x \<in> A"
    "Suc x mod n \<in> A"
    by blast

  show False
  proof (cases n)
    case 0
    then show ?thesis
      using \<open>Suc x mod n \<in> A\<close> \<open>x \<in> A\<close> assms(2) by force
  next
    case (Suc m)
    assume "n = Suc m"

    have "x = m \<or> x < m"
      using Suc \<open>x \<in> A\<close> assms(1) by auto
    then show ?thesis
    proof
      assume "x = m"
      then show False
        using Suc \<open>Suc x mod n \<in> A\<close> assms(1) by auto
    next
      assume "x < m"
      with mod_less[of "Suc x" "Suc m"]
      show False
        using Suc \<open>Suc x mod n \<in> A\<close> \<open>x \<in> A\<close> assms(2) by force
    qed
  qed
qed

lemma in_set_mapD:
  "x \<in> set (map f xs) \<Longrightarrow> \<exists>y \<in> set xs. x = f y"
  by (simp add: image_iff)

(*****************************)

subsection \<open>From AutoCorres \<close>

lemma disjointI':
  assumes "\<And>x y. \<lbrakk> x \<in> A; y \<in> B \<rbrakk> \<Longrightarrow> x \<noteq> y"
  shows " A \<inter> B = {}"
  using assms by fast

lemma disjoint_subset2:
  assumes "B' \<subseteq> B" and "A \<inter> B = {}"
  shows   "A \<inter> B' = {}"
  using assms by fast

(*****************************)

end