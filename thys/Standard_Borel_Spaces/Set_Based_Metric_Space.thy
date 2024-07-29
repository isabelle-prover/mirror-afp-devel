(*  Title:   Set_Based_Metric_Space.thy
    Author:  Michikazu Hirata, Tokyo Institute of Technology
*)

subsection  \<open>Lemmas for Abstract Metric Spaces\<close>
theory Set_Based_Metric_Space
  imports Lemmas_StandardBorel
begin

text \<open> We prove additional lemmas related to set-based metric spaces. \<close>

subsubsection \<open> Basic Lemmas \<close>
lemma
  assumes "Metric_space M d" "\<And>x y. x \<in> M \<Longrightarrow> y \<in> M \<Longrightarrow> d x y = d' x y"
      and "\<And>x y. d' x y = d' y x" "\<And>x y. d' x y \<ge> 0"
    shows Metric_space_eq: "Metric_space M d'"
      and Metric_space_eq_mtopology: "Metric_space.mtopology M d = Metric_space.mtopology M d'"
      and Metric_space_eq_mcomplete: "Metric_space.mcomplete M d \<longleftrightarrow> Metric_space.mcomplete M d'"
proof -
  interpret m1: Metric_space M d by fact
  show "Metric_space M d'"
    using assms by(auto simp: Metric_space_def)
  then interpret m2:Metric_space M d' .
  have [simp]: "m1.mball x e = m2.mball x e" for x e
    using assms by(auto simp: m1.mball_def m2.mball_def)
  show 1:"m1.mtopology = m2.mtopology"
    by(auto simp: topology_eq m1.openin_mtopology m2.openin_mtopology)
  show "m1.mcomplete = m2.mcomplete"
    by(auto simp: 1 m1.mcomplete_def m2.mcomplete_def m1.MCauchy_def m2.MCauchy_def assms(2) in_mono)
qed

context Metric_space
begin

lemma mtopology_base_in_balls: "base_in mtopology {mball a \<epsilon> | a \<epsilon>. a \<in> M \<and> \<epsilon> > 0}"
proof -
  have 1:"\<And>x. x \<in> {mball a \<epsilon> | a \<epsilon>. a \<in> M \<and> \<epsilon> > 0} \<Longrightarrow> openin mtopology x"
    by auto
  show ?thesis
    unfolding base_in_def2[of "{mball a \<epsilon> | a \<epsilon>. a \<in> M \<and> \<epsilon> > 0}",OF 1,simplified]
    by (metis centre_in_mball_iff in_mono openin_mtopology)
qed

lemma closedin_metric2: "closedin mtopology C \<longleftrightarrow> C \<subseteq> M \<and> (\<forall>x. x \<in> C \<longleftrightarrow> (\<forall>\<epsilon>>0. mball x \<epsilon> \<inter> C \<noteq> {}))"
proof
  assume h:"closedin mtopology C"
  have 1: "C \<subseteq> M"
    using Metric_space.closedin_metric Metric_space_axioms h by blast
  show "C \<subseteq> M \<and> (\<forall>x. x \<in> C \<longleftrightarrow> (\<forall>\<epsilon>>0. mball x \<epsilon> \<inter> C \<noteq> {}))"
  proof safe
    fix \<epsilon> x
    assume "x \<in> C" "(0 :: real) < \<epsilon>" "mball x \<epsilon> \<inter> C = {}"
    with 1 show False
      by blast
  next
    fix x
    assume "\<forall>\<epsilon>>0. mball x \<epsilon> \<inter> C \<noteq> {}"
    hence "\<exists>xn. xn \<in> mball x (1 / real (Suc n)) \<inter> C" for n
      by (meson all_not_in_conv divide_pos_pos of_nat_0_less_iff zero_less_Suc zero_less_one)
    then obtain xn where xn:"\<And>n. xn n \<in> mball x (1 / real (Suc n)) \<inter> C"
      by metis
    hence xxn:"x \<in> M" "range xn \<subseteq> C"
      using xn by auto
    have "limitin mtopology xn x sequentially"
      unfolding limitin_metric eventually_sequentially
    proof safe
      fix \<epsilon>
      assume "(0 :: real) < \<epsilon>"
      then obtain N where hN: "1 / real (Suc N) < \<epsilon>"
        using nat_approx_posE by blast
      show "\<exists>N. \<forall>n\<ge>N. xn n \<in> M \<and> d (xn n) x < \<epsilon>"
      proof(safe intro!: exI[where x="N"])
        fix n
        assume n[arith]: "N \<le> n"
        then have "1 / real (Suc n) < \<epsilon>"
          by (metis Suc_le_mono hN inverse_of_nat_le nat.distinct(1) order_le_less_trans)
        with xn[of n] show "d (xn n) x < \<epsilon>"
          by (simp add: commute)
      qed(use xxn 1 in auto)
    qed fact
    with h 1 xxn show "x \<in> C"
      by(auto simp: metric_closedin_iff_sequentially_closed)
  qed(use 1 in auto)
next
  assume"C \<subseteq> M \<and> (\<forall>x. (x \<in> C) \<longleftrightarrow> (\<forall>\<epsilon>>0. mball x \<epsilon> \<inter> C \<noteq> {}))"
  hence h:"C \<subseteq> M" "\<And>x. (x \<in> C) \<longleftrightarrow> (\<forall>\<epsilon>>0. mball x \<epsilon> \<inter> C \<noteq> {})"
    by simp_all
  show "closedin mtopology C"
    unfolding metric_closedin_iff_sequentially_closed
  proof safe
    fix xn x
    assume h':"range xn \<subseteq> C" "limitin mtopology xn x sequentially"
    hence "x \<in> M" by (simp add: limitin_mspace) 
    have "mball x \<epsilon> \<inter> C \<noteq> {}" if "\<epsilon> > 0" for \<epsilon>
    proof -
      obtain N where hN:"\<And>n. n \<ge> N \<Longrightarrow> d (xn n) x < \<epsilon>"
        using h'(2) \<open>\<epsilon> > 0\<close> limit_metric_sequentially by blast
      have "xn N \<in> mball x \<epsilon> \<inter> C"
        using h'(1) hN[of N] \<open>x \<in> M\<close> commute h(1) by fastforce
      thus "mball x \<epsilon> \<inter> C \<noteq> {}" by auto
    qed
    with h(2)[of x] show "x \<in> C" by simp
  qed(use h(1) in auto)
qed

lemma openin_mtopology2:
 "openin mtopology U \<longleftrightarrow> U \<subseteq> M \<and> (\<forall>xn x. limitin mtopology xn x sequentially \<and> x \<in> U \<longrightarrow> (\<exists>N. \<forall>n\<ge>N. xn n \<in> U))"
  unfolding openin_mtopology
proof safe
  fix xn x
  assume h: "\<forall>x. x \<in> U \<longrightarrow> (\<exists>r>0. mball x r \<subseteq> U)" "limitin mtopology xn x sequentially" "x \<in> U" "U \<subseteq> M"
  then obtain r where r: "r > 0" "mball x r \<subseteq> U"
    by auto
  with h(2) obtain N where N: "\<And>n. n \<ge> N \<Longrightarrow> xn n \<in> M" "\<And>n. n \<ge> N \<Longrightarrow> d (xn n) x < r"
    by (metis limit_metric_sequentially)
  with h have "\<exists>N. \<forall>n\<ge>N. xn n \<in> mball x r"
    by(auto intro!: exI[where x=N] simp:commute)
  with r show "\<exists>N. \<forall>n\<ge>N. xn n \<in> U"
    by blast
next
  fix x
  assume h:"U \<subseteq> M" "\<forall>xn x. limitin mtopology xn x sequentially \<and> x \<in> U \<longrightarrow> (\<exists>N. \<forall>n\<ge>N. xn n \<in> U)" "x \<in> U"
  show "\<exists>r>0. mball x r \<subseteq> U"
  proof(rule ccontr)
    assume "\<not> (\<exists>r>0. mball x r \<subseteq> U)"
    then have "\<forall>n. \<exists>xn\<in>mball x (1 / Suc n). xn \<notin> U"
      by (meson of_nat_0_less_iff subsetI zero_less_Suc zero_less_divide_1_iff)
    then obtain xn where xn: "\<And>n. xn n \<in> mball x (1 / Suc n)" "\<And>n. xn n \<notin>  U"
      by metis
    have "limitin mtopology xn x sequentially"
      unfolding limit_metric_sequentially
    proof safe
      fix e :: real
      assume e:"0 < e"
      then obtain N where N: "1 / real (Suc N) < e"
        using nat_approx_posE by blast
      show "\<exists>N. \<forall>n\<ge>N. xn n \<in> M \<and> d (xn n) x < e"
      proof(safe intro!: exI[where x=N])
        fix n
        assume n: "n \<ge> N"
        then have "1 / Suc n < e"
          by (metis N Suc_le_mono inverse_of_nat_le nat.distinct(1) order_le_less_trans)
        thus "d (xn n) x < e"
          using xn(1)[of n] by(auto simp: commute)
      qed(use xn in auto)
    qed(use h in auto)
    with h(2,3) xn(2) show False
      by auto
  qed
qed

lemma closure_of_mball: "mtopology closure_of mball a e \<subseteq> mcball a e"
  by (simp add: closure_of_minimal mball_subset_mcball)

lemma interior_of_mcball: "mball a e \<subseteq> mtopology interior_of mcball a e"
  by (simp add: interior_of_maximal_eq mball_subset_mcball)

lemma isolated_points_of_mtopology:
 "mtopology isolated_points_of A = {x\<in>M\<inter>A. \<forall>xn. range xn \<subseteq> A \<and> limitin mtopology xn x sequentially \<longrightarrow> (\<exists>no. \<forall>n\<ge>no. xn n = x)}"
proof safe
  fix x xn
  assume h:"x \<in> mtopology isolated_points_of A" "limitin mtopology xn x sequentially" "range xn \<subseteq> A"
  then have ha:"x \<in> topspace mtopology" "x \<in> A" "\<exists>U. x \<in> U \<and> openin mtopology U \<and> U \<inter> (A - {x}) = {}"
    by(simp_all add: in_isolated_points_of)
  then obtain U where u:"x \<in> U" "openin mtopology U" "U \<inter> (A - {x}) = {}"
    by auto
  then obtain e where e: "e > 0" "mball x e \<subseteq> U"
    by (meson openin_mtopology)
  then obtain N where "\<And>n. n \<ge> N \<Longrightarrow> xn n \<in> mball x e"
    using h(2) commute limit_metric_sequentially by fastforce
  thus "\<exists>no. \<forall>n\<ge>no. xn n = x"
    using h(3) e(2) u(3) by(fastforce intro!: exI[where x=N])
qed (auto simp: derived_set_of_sequentially isolated_points_of_def, blast)

lemma perfect_set_mball_infinite:
  assumes "perfect_set mtopology A" "a \<in> A" "e > 0"
  shows "infinite (mball a e)"
proof safe
  assume h: "finite (mball a e)"
  have "a \<in> M"
    using assms perfect_setD(2)[OF assms(1)] by auto
  have "\<exists>e > 0. mball a e = {a}"
  proof -
    consider "mball a e = {a}" | "{a} \<subset> mball a e"
      using \<open>a \<in> M\<close> assms(3) by blast
    thus ?thesis
    proof cases
      case 1
      with assms show ?thesis by auto
    next
      case 2
      then have nen:"{d a b |b. b \<in> mball a e \<and> a \<noteq> b} \<noteq> {}"
        by auto
      have fin: "finite {d a b |b. b \<in> mball a e \<and> a \<noteq> b}"
        using h by (auto simp del: in_mball)
      define e' where "e' \<equiv> Min {d a b |b. b \<in> mball a e \<and> a \<noteq> b}"
      have "e' > 0"
        using mdist_pos_eq[OF \<open>a \<in> M\<close>] by(simp add: e'_def Min_gr_iff[OF fin nen] del: in_mball) auto
      have bd:"\<And>b. b \<in> mball a e \<Longrightarrow> a \<noteq> b \<Longrightarrow> e' \<le> d a b"
        by(auto simp: e'_def Min_le_iff[OF fin nen] simp del: in_mball)
      have "e' \<le> e"
        unfolding e'_def Min_le_iff[OF fin nen]
        using nen by auto
      show ?thesis
      proof(safe intro!: exI[where x=e'])
        fix x
        assume x:"x \<in> mball a e'"
        then show "x = a"
          using \<open>e' \<le> e\<close> bd by fastforce
      qed (use \<open>a \<in> M\<close> \<open>e' > 0\<close> in auto)
    qed
  qed
  then obtain e' where e':"e' > 0" "mball a e' = {a}" by auto
  show False
    using perfect_setD(3)[OF assms(1,2) centre_in_mball_iff[of a e',THEN iffD2]] \<open>a \<in> M\<close> \<open>e' > 0\<close> e'(2) by blast
qed

lemma MCauchy_dist_Cauchy:
  assumes "MCauchy xn" "MCauchy yn"
  shows "Cauchy (\<lambda>n. d (xn n) (yn n))"
  unfolding metric_space_class.Cauchy_altdef2 dist_real_def
proof safe
  have h:"\<And>n. xn n \<in> M" "\<And>n. yn n \<in> M"
    using assms by(auto simp: MCauchy_def)
  fix e :: real
  assume e:"0 < e"
  with assms obtain N1 N2 where N: "\<And>n m. n \<ge> N1 \<Longrightarrow> m \<ge> N1 \<Longrightarrow> d (xn n) (xn m) < e / 2" "\<And>n m. n \<ge> N2 \<Longrightarrow> m \<ge> N2 \<Longrightarrow> d (yn n) (yn m) < e / 2"
    by (metis MCauchy_def zero_less_divide_iff zero_less_numeral)
  define N where "N \<equiv> max N1 N2"
  then have N': "N \<ge> N1" "N \<ge> N2" by auto
  show "\<exists>N. \<forall>n\<ge>N. \<bar>d (xn n) (yn n) - d (xn N) (yn N)\<bar> < e"
  proof(safe intro!: exI[where x=N])
    fix n
    assume n:"N \<le> n"
    have "d (xn n) (yn n) \<le> d (xn n) (xn N) + d (xn N) (yn N) + d (yn N) (yn n)"
         "d (xn N) (yn N) \<le> d (xn N) (xn n) + d (xn n) (yn n) + d (yn n) (yn N)"
      using triangle[OF h(1)[of n] h(1)[of N] h(2)[of n]] triangle[OF h(1)[of N] h(2)[of N] h(2)[of n]]
            triangle[OF h(1)[of N] h(2)[of n] h(2)[of N]] triangle[OF h(1)[of N] h(1)[of n] h(2)[of n]] by auto
    thus "\<bar>d (xn n) (yn n) - d (xn N) (yn N)\<bar> < e"
      using N(1)[OF N'(1) order.trans[OF N'(1) n]] N(2)[OF N'(2) order.trans[OF N'(2) n]] N(1)[OF order.trans[OF N'(1) n] N'(1)] N(2)[OF order.trans[OF N'(2) n] N'(2)]
      by auto
  qed
qed

subsubsection \<open> Dense in Metric Spaces\<close>
abbreviation "mdense \<equiv> dense_in mtopology"

text \<open>\<^url>\<open>https://people.bath.ac.uk/mw2319/ma30252/sec-dense.html\<close>\<close>
lemma mdense_def:
 "mdense U \<longleftrightarrow> U \<subseteq> M \<and> (\<forall>x\<in>M. \<forall>\<epsilon>>0. mball x \<epsilon> \<inter> U \<noteq> {})"
proof safe
  assume h:" U \<subseteq> M" "(\<forall>x\<in>M. \<forall>\<epsilon>>0. mball x \<epsilon> \<inter> U \<noteq> {})"
  show "dense_in mtopology U"
  proof(rule dense_inI)
    fix V
    assume h':"openin mtopology V" "V \<noteq> {}"
    then obtain x where 1:"x \<in> V" by auto
    then obtain \<epsilon> where 2:"\<epsilon>>0" "mball x \<epsilon> \<subseteq> V"
      by (meson h'(1) openin_mtopology)
    have "mball x \<epsilon> \<inter> U \<noteq> {}"
      using h 1 2 openin_subset[OF h'(1)]
      by (auto simp del: in_mball)
    thus "U \<inter> V \<noteq> {}" using 2 by auto
  qed(use h in auto)
next
  fix x \<epsilon>
  assume h:"x \<in> M" "(0 :: real) < \<epsilon>" "mball x \<epsilon> \<inter> U = {}" "mdense U"
  then have "mball x \<epsilon> \<noteq> {}" "openin mtopology (mball x \<epsilon>)"
    by auto
  with h(4) have "mball x \<epsilon> \<inter> U \<noteq> {}"
    by(auto simp: dense_in_def)
  with h(3) show False
    by simp
qed(auto simp: dense_in_def)

corollary mdense_balls_cover:
  assumes "mdense U" and "e > 0"
  shows "(\<Union>u\<in>U. mball u e) = M"
  using assms[simplified mdense_def] commute by fastforce

lemma mdense_empty_iff: "mdense {} \<longleftrightarrow> M = {}"
  by(auto simp: mdense_def) (use zero_less_one in blast)

lemma mdense_M: "mdense M"
  by(auto simp: mdense_def)

lemma mdense_def2:
 "mdense U \<longleftrightarrow> U \<subseteq> M \<and> (\<forall>x\<in>M. \<forall>\<epsilon>>0.\<exists>y\<in>U. d x y < \<epsilon>)"
proof safe
  fix x e
  assume h: "mdense U" and hxe: "x \<in> M" "(0 :: real) < e"
  then have "x \<in> (\<Union>u\<in>U. mball u e)"
    by(simp add: mdense_balls_cover)
  thus "\<exists>y\<in>U. d x y < e"
    by (fastforce simp: commute)
qed(fastforce simp: mdense_def)+

lemma mdense_def3:
 "mdense U \<longleftrightarrow> U \<subseteq> M \<and> (\<forall>x\<in>M. \<exists>xn. range xn \<subseteq> U \<and> limitin mtopology xn x sequentially)"
  unfolding mdense_def
proof safe
  fix x
  assume h: "U \<subseteq> M" "\<forall>x\<in>M. \<forall>\<epsilon>>0. mball x \<epsilon> \<inter> U \<noteq> {}" "x \<in> M"
  then have "\<And>n. mball x (1 / (real n + 1)) \<inter> U \<noteq> {}"
    by auto
  hence "\<forall>n. \<exists>k. k \<in> mball x (1 / (real n + 1)) \<inter> U" by (auto simp del: in_mball)
  hence "\<exists>a. \<forall>n. a n \<in> mball x (1 / (real n + 1)) \<inter> U" by(rule choice)
  then obtain xn where xn: "\<And>n. xn n \<in> mball x (1 / (real n + 1)) \<inter> U"
    by auto
  show "\<exists>xn. range xn \<subseteq> U \<and> limitin mtopology xn x sequentially"
    unfolding limitin_metric eventually_sequentially
  proof(safe intro!: exI[where x=xn])
    fix \<epsilon> :: real
    assume he:"0 < \<epsilon>"
    then obtain N where hn: "1 / \<epsilon> < real N"
      using reals_Archimedean2 by blast
    have hn': "0 < real N"
      by(rule ccontr) (use hn he in fastforce)
    hence "1 / real N < \<epsilon>"
      using he hn by (metis divide_less_eq mult.commute)
    hence hn'':"1 / (real N + 1) < \<epsilon>"
      using hn' by(auto intro!: order.strict_trans[OF linordered_field_class.divide_strict_left_mono[of "real N" "real N + 1" 1]])
    show "\<exists>N. \<forall>n\<ge>N. xn n \<in> M \<and> d (xn n) x < \<epsilon>"
    proof(safe intro!: exI[where x="N"])
      fix n
      assume "N \<le> n"
      then have 1:"1 / (real n + 1) \<le> 1 / (real N + 1)"
        using hn' by(auto intro!: linordered_field_class.divide_left_mono)
      show "d (xn n) x < \<epsilon>"
        using xn[of n] order.strict_trans1[OF 1 hn''] by (auto simp: commute)
    qed(use xn in auto)
  qed(use xn h in auto)
next
  fix x and e :: real
  assume h: "U \<subseteq> M" " \<forall>x\<in>M. \<exists>xn. range xn \<subseteq> U \<and> limitin mtopology xn x sequentially" "x \<in> M" "0 < e" "mball x e \<inter> U = {}"
  then obtain xn where xn:"range xn \<subseteq> U" "limitin mtopology xn x sequentially"
    by auto
  with h(4) obtain N where N: "\<And>n. n \<ge> N \<Longrightarrow> d (xn n) x < e"
    by (meson limit_metric_sequentially)
  have "xn N \<in> mball x e \<inter> U"
    using N[of N] xn(1) h(1,3) by (auto simp: commute)
  with h(5) show False by simp
qed

text \<open> Diameter\<close>
definition mdiameter :: "'a set \<Rightarrow> ennreal" where
"mdiameter A \<equiv> \<Squnion> {ennreal (d x y) | x y. x \<in> A \<inter> M \<and> y \<in> A \<inter> M}"

lemma mdiameter_empty[simp]:
 "mdiameter {} = 0"
  by(simp add: mdiameter_def bot_ennreal)

lemma mdiameter_def2:
  assumes "A \<subseteq> M"
  shows "mdiameter A = \<Squnion> {ennreal (d x y) | x y. x \<in> A \<and> y \<in> A}"
  using assms by(auto simp: mdiameter_def) (meson subset_eq)

lemma mdiameter_subset:
  assumes "A \<subseteq> B"
  shows "mdiameter A \<le> mdiameter B"
  unfolding mdiameter_def using assms by(auto intro!: Sup_subset_mono)

lemma mdiameter_cball_leq: "mdiameter (mcball a \<epsilon>) \<le> ennreal (2 * \<epsilon>)"
  unfolding Sup_le_iff mdiameter_def
proof safe
  fix x y
  assume h:"x \<in> mcball a \<epsilon>" "y \<in> mcball a \<epsilon>" "x \<in> M" "y \<in> M"
  have "d x y \<le> 2 * \<epsilon>"
    using h(1) h(2) triangle'' by fastforce
  thus "ennreal (d x y) \<le> ennreal (2 * \<epsilon>)"
    using ennreal_leI by blast
qed

lemma mdiameter_ball_leq:
 "mdiameter (mball a \<epsilon>) \<le> ennreal (2 * \<epsilon>)"
  using mdiameter_subset[OF mball_subset_mcball[of a \<epsilon>]] mdiameter_cball_leq[of a \<epsilon>]
  by auto

lemma mdiameter_is_sup:
  assumes "x \<in> A \<inter> M" "y \<in> A \<inter> M"
  shows "d x y \<le> mdiameter A"
  using assms by(auto simp: mdiameter_def intro!: Sup_upper)

lemma mdiameter_is_sup':
  assumes "x \<in> A \<inter> M" "y \<in> A \<inter> M" "mdiameter A \<le> ennreal r" "r \<ge> 0"
  shows "d x y \<le> r"
  using order.trans[OF mdiameter_is_sup[OF assms(1,2)] assms(3)] assms(4) by simp

lemma mdiameter_le:
  assumes "\<And>x y. x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> d x y \<le> r"
  shows "mdiameter A \<le> r"
  using assms by(auto simp: mdiameter_def Sup_le_iff ennreal_leI)

lemma mdiameter_eq_closure: "mdiameter (mtopology closure_of A) = mdiameter A"
proof(rule antisym)
  show "mdiameter A \<le> mdiameter (mtopology closure_of A)"
    by(fastforce intro!: Sup_subset_mono simp: mdiameter_def metric_closure_of)
next
  have "{ennreal (d x y) |x y. x \<in> A \<inter> M \<and> y \<in> A \<inter> M} = ennreal ` {d x y |x y. x \<in> A \<inter> M \<and> y \<in> A \<inter> M}"
    by auto
  also have "mdiameter (mtopology closure_of A) \<le> \<Squnion> ..."
    unfolding le_Sup_iff_less
  proof safe
    fix r
    assume "r < mdiameter (mtopology closure_of A)"
    then obtain x y where xy:"x \<in> mtopology closure_of A" "x \<in> M" "y \<in> mtopology closure_of A" "y \<in> M" "r < ennreal (d x y)"
      by(auto simp: mdiameter_def less_Sup_iff)
    hence "r < \<top>"
      using dual_order.strict_trans ennreal_less_top by blast
    define e where "e \<equiv> (d x y - enn2real r)/2"
    have "e > 0"
      using xy(5) \<open>r < \<top>\<close> by(simp add: e_def)
    then obtain x' y' where xy':"x' \<in> mball x e" "x'\<in> A" "y' \<in> mball y e" "y'\<in> A"
      using xy by(fastforce simp: metric_closure_of)
    show "\<exists>i\<in>{d x y |x y. x \<in> A \<inter> M \<and> y \<in> A \<inter> M}. r \<le> ennreal i"
    proof(safe intro!: bexI[where x="d x' y'"])
      have "d x y \<le> d x x' + d x' y' + d y y'"
        using triangle[OF xy(2) _ xy(4),of x'] xy' triangle[of x' y' y]
        by(fastforce simp add: commute)
      also have "... < d x y - enn2real r + d x' y'"
        using xy'(1) xy'(3) by(simp add: e_def)
      finally have "enn2real r < d x' y'" by simp
      thus "r \<le> ennreal (d x' y')"
        by (simp add: \<open>r < \<top>\<close>)
    qed(use xy'(1) xy'(3) xy'(2,4) in auto)
  qed
  finally show "mdiameter (mtopology closure_of A) \<le> mdiameter A"
    by(simp add: mdiameter_def)
qed

lemma mbounded_finite_mdiameter: "mbounded A \<longleftrightarrow> A \<subseteq> M \<and> mdiameter A < \<infinity>"
proof safe
  assume "mbounded A"
  then obtain x B where "A \<subseteq> mcball x B"
    by(auto simp: mbounded_def)
  then have "mdiameter A \<le> mdiameter (mcball x B)"
    by(rule mdiameter_subset)
  also have "... \<le> ennreal (2 * B)"
    by(rule mdiameter_cball_leq)
  also have "... < \<infinity>"
    by auto
  finally show "mdiameter A < \<infinity>" .
next
  assume h:"mdiameter A < \<infinity>" "A \<subseteq> M"
  consider "A = {}" | "A \<noteq> {}" by auto
  then show "mbounded A"
  proof cases
    case h2:2
    then have 1:"{d x y |x y. x \<in> A \<and> y \<in> A} \<noteq> {}" by auto
    have eq:"{ennreal (d x y) | x y. x \<in> A \<and> y \<in> A} = ennreal ` {d x y | x y. x \<in> A \<and> y \<in> A}"
      by auto
    hence 2:"mdiameter A = \<Squnion> (ennreal ` {d x y | x y. x \<in> A \<and> y \<in> A})"
      using h by(auto simp add: mdiameter_def2)
    obtain x y where hxy:
     "x \<in> A" "y \<in> A" "mdiameter A < ennreal (d x y + 1)"
      using SUP_approx_ennreal[OF _ 1 2,of 1] h by(fastforce simp: diameter_def)
    show ?thesis
      unfolding mbounded_alt
    proof(safe intro!: exI[where x="d x y + 1"])
      fix w z
      assume "w \<in> A" "z \<in> A "
      with SUP_lessD[OF hxy(3)[simplified 2]]
      have "ennreal (d w z) < ennreal (d x y + 1)"
        by blast
      thus "d w z \<le> d x y + 1"
        by (metis canonically_ordered_monoid_add_class.lessE ennreal_le_iff2 ennreal_neg le_iff_add not_less_zero)
    qed (use h in auto)
  qed(auto simp: mbounded_def)
qed(auto simp: mbounded_def)

text \<open> Distance between a point and a set. \<close>
definition d_set :: "'a set \<Rightarrow> 'a \<Rightarrow> real" where
"d_set A \<equiv> (\<lambda>x. if A \<noteq> {} \<and> A \<subseteq> M \<and> x \<in> M then Inf {d x y |y. y \<in> A} else 0)"

lemma d_set_nonneg[simp]:
 "d_set A x \<ge> 0"
proof -
  have "{d x y |y. y \<in> A} = d x ` A" by auto
  thus ?thesis
    by(auto simp: d_set_def intro!: cINF_greatest[of _ _ "d x"])
qed

lemma d_set_bdd_below[simp]:
 "bdd_below {d x y |y. y \<in> A}"
  by(auto simp: bdd_below_def intro!: exI[where x=0])

lemma d_set_singleton[simp]:
  "x \<in> M \<Longrightarrow> y \<in> M \<Longrightarrow> d_set {y} x = d x y"
  by(auto simp: d_set_def)

lemma d_set_empty[simp]:
 "d_set {} x = 0"
  by(simp add: d_set_def)

lemma d_set_notin:
  "x \<notin> M \<Longrightarrow> d_set A x = 0"
  by(auto simp: d_set_def)

lemma d_set_inA:
  assumes "x \<in> A"
  shows "d_set A x = 0"
proof -
  {
    assume "x \<in> M" "A \<subseteq> M"
    then have "0 \<in> {d x y |y. y \<in> A}"
      using assms by(auto intro: exI[where x=x])
    moreover have "A \<noteq> {}"
      using assms by auto
    ultimately have "Inf {d x y |y. y \<in> A} = 0"
      using cInf_lower[OF \<open>0 \<in> {d x y |y. y \<in> A}\<close>] d_set_nonneg[of A x] \<open>A \<subseteq> M\<close> \<open>x \<in> M\<close>
      by(auto simp: d_set_def)
  }
  thus ?thesis
    using assms by(auto simp: d_set_def)
qed

lemma d_set_nzeroD:
  assumes "d_set A x \<noteq> 0"
  shows "A \<subseteq> M" "x \<notin> A" "A \<noteq> {}"
   by(rule ccontr, use assms d_set_inA d_set_def in auto)

lemma d_set_antimono:
  assumes "A \<subseteq> B" "A \<noteq> {}" "B \<subseteq> M"
  shows "d_set B x \<le> d_set A x"
proof(cases "B = {}")
  case h:False
  with assms have "{d x y |y. y \<in> B} \<noteq> {}" "{d x y |y. y \<in> A} \<subseteq> {d x y |y. y \<in> B}" "A \<subseteq> M"
    by auto
  with assms(3) show ?thesis
    by(simp add: d_set_def cInf_superset_mono assms(2))
qed(use assms in simp)

lemma d_set_bounded:
  assumes "\<And>y. y \<in> A \<Longrightarrow> d x y < K" "K > 0"
  shows "d_set A x < K"
proof -
  consider "A = {}" | "\<not> A \<subseteq> M" | "x \<notin> M" | "A \<noteq> {}" "A \<subseteq> M" "x \<in> M"
    by blast
  then show ?thesis
  proof cases
    case 4
    then have 2:"{d x y |y. y \<in> A} \<noteq> {}" by auto
    show ?thesis
      using assms by (auto simp add: d_set_def cInf_lessD[OF 2]  cInf_less_iff[OF 2])
  qed(auto simp: d_set_def assms)
qed

lemma d_set_tr:
  assumes "x \<in> M" "y \<in> M"
  shows "d_set A x \<le> d x y + d_set A y"
proof -
  consider "A = {}" | "\<not> A \<subseteq> M" | "A \<noteq> {}" "A \<subseteq> M"
    by blast
  then show ?thesis
  proof cases
    case 3
    have "d_set A x \<le> Inf {d x y + d y a |a. a\<in>A}"
    proof -
      have "\<Sqinter> {d x y |y. y \<in> A} \<le> \<Sqinter> {d x y + d y a |a. a \<in> A}"
        by(rule cInf_mono) (use 3 assms triangle in fastforce)+
      thus ?thesis
        by(simp add: d_set_def assms 3)
    qed
    also have "... = (\<Sqinter>a\<in>A. d x y + d y a)"
      by (simp add: Setcompr_eq_image)
    also have "... = d x y + \<Sqinter> (d y ` A)"
      using 3 by(auto intro!: Inf_add_eq bdd_belowI[where m=0])
    also have "... = d x y + d_set A y"
      using assms 3 by(auto simp: d_set_def Setcompr_eq_image)
    finally show ?thesis .
  qed(auto simp: d_set_def)
qed

lemma d_set_abs_le:
  assumes "x \<in> M" "y \<in> M"
  shows "\<bar>d_set A x - d_set A y\<bar> \<le> d x y"
  using d_set_tr[OF assms,of A] d_set_tr[OF assms(2,1),of A,simplified commute[of y x]]
  by auto

lemma d_set_inA_le:
  assumes "y \<in> A"
  shows "d_set A x \<le> d x y"
proof -
  consider "A \<noteq> {}" "A \<subseteq> M" "x \<in> M" | "\<not> A \<subseteq> M" | "x \<notin> M"
    using assms by blast
  then show ?thesis
  proof cases
    case 1
    with assms have "y \<in> M" by auto
    from d_set_tr[OF 1(3) this,of A] show ?thesis
      by(simp add: d_set_inA[OF assms])
  qed(auto simp: d_set_def)
qed

lemma d_set_ball_empty:
  assumes "A \<noteq> {}" "A \<subseteq> M" "e > 0" "x \<in> M" "mball x e \<inter> A = {}"
  shows "d_set A x \<ge> e"
  using assms by(fastforce simp: d_set_def assms(1) le_cInf_iff)

lemma d_set_closed_pos:
  assumes "closedin mtopology A" "A \<noteq> {}" "x \<in> M" "x \<notin> A"
  shows "d_set A x > 0"
proof -
  have a:"A \<subseteq> M" "openin mtopology (M - A)"
    using closedin_subset[OF assms(1)] assms(1) by auto
  with assms(3,4) obtain e where e: "e > 0" "mball x e \<subseteq> M - A"
    using openin_mtopology by auto
  thus ?thesis
    by(auto intro!: order.strict_trans2[OF e(1) d_set_ball_empty[OF assms(2) a(1) e(1) assms(3)]])
qed

lemma gdelta_in_closed:
  assumes "closedin mtopology M"
  shows "gdelta_in mtopology M"
  by(auto intro!: closed_imp_gdelta_in metrizable_space_mtopology)

text \<open> Oscillation \<close>
definition osc_on :: "['b set, 'b topology, 'b \<Rightarrow> 'a, 'b] \<Rightarrow> ennreal" where
"osc_on A X f \<equiv> (\<lambda>y. \<Sqinter> {mdiameter (f ` (A \<inter> U)) |U. y \<in> U \<and> openin X U})"

abbreviation "osc X \<equiv> osc_on (topspace X) X"

lemma osc_def: "osc X f = (\<lambda>y. \<Sqinter> {mdiameter (f ` U) |U. y \<in> U \<and> openin X U})"
  by(standard,auto simp: osc_on_def) (metis (no_types, opaque_lifting) inf.absorb2 openin_subset)

lemma osc_on_less_iff:
 "osc_on A X f x < t \<longleftrightarrow> (\<exists>v. x \<in> v \<and> openin X v \<and> mdiameter (f ` (A \<inter> v)) < t)"
  by(auto simp add: osc_on_def Inf_less_iff)

lemma osc_less_iff:
 "osc X f x < t \<longleftrightarrow> (\<exists>v. x \<in> v \<and> openin X v \<and> mdiameter (f ` v) < t)"
  by(auto simp add: osc_def Inf_less_iff)

end

definition mdist_set :: "'a metric \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> real" where
"mdist_set m \<equiv> Metric_space.d_set (mspace m) (mdist m)"

lemma(in Metric_space) mdist_set_Self: "mdist_set Self = d_set"
  by(simp add: mdist_set_def)

lemma mdist_set_nonneg[simp]: "mdist_set m A x \<ge> 0"
  by(auto simp: mdist_set_def Metric_space.d_set_nonneg)

lemma mdist_set_singleton[simp]:
  "x \<in> mspace m \<Longrightarrow> y \<in> mspace m \<Longrightarrow> mdist_set m {y} x = mdist m x y"
  by(auto simp: mdist_set_def Metric_space.d_set_singleton)

lemma mdist_set_empty[simp]: "mdist_set m {} x = 0"
  by(auto simp: mdist_set_def Metric_space.d_set_empty)

lemma mdist_set_inA:
  assumes "x \<in> A"
  shows "mdist_set m A x = 0"
  by(auto simp: assms mdist_set_def Metric_space.d_set_inA)

lemma mdist_set_nzeroD:
  assumes "mdist_set m A x \<noteq> 0"
  shows "A \<subseteq> mspace m" "x \<notin> A" "A \<noteq> {}"
  using assms Metric_space.d_set_nzeroD[of "mspace m" "mdist m"]
  by(auto simp: mdist_set_def)

lemma mdist_set_antimono:
  assumes "A \<subseteq> B" "A \<noteq> {}" "B \<subseteq> mspace m"
  shows "mdist_set m B x \<le> mdist_set m A x"
  by(auto simp: assms mdist_set_def Metric_space.d_set_antimono)

lemma mdist_set_bounded:
  assumes "\<And>y. y \<in> A \<Longrightarrow> mdist m x y < K" "K > 0"
  shows "mdist_set m A x < K"
  by(auto simp: assms mdist_set_def Metric_space.d_set_bounded)

lemma mdist_set_tr:
  assumes "x \<in> mspace m" "y \<in> mspace m"
  shows "mdist_set m A x \<le> mdist m x y + mdist_set m A y"
  by(auto simp: assms mdist_set_def Metric_space.d_set_tr)

lemma mdist_set_abs_le:
  assumes "x \<in> mspace m" "y \<in> mspace m"
  shows "\<bar>mdist_set m A x - mdist_set m A y\<bar> \<le> mdist m x y"
  by(auto simp: assms mdist_set_def Metric_space.d_set_abs_le)

lemma mdist_set_inA_le:
  assumes "y \<in> A"
  shows "mdist_set m A x \<le> mdist m x y"
  by(auto simp: assms mdist_set_def Metric_space.d_set_inA_le)

lemma mdist_set_ball_empty:
  assumes "A \<noteq> {}" "A \<subseteq> mspace m" "e > 0" "x \<in> mspace m" "mball_of m x e \<inter> A = {}"
  shows "mdist_set m A x \<ge> e"
  by (metis Metric_space.d_set_ball_empty Metric_space_mspace_mdist assms mball_of_def mdist_set_def)

lemma mdist_set_closed_pos:
  assumes "closedin (mtopology_of m) A" "A \<noteq> {}" "x \<in> mspace m" "x \<notin> A"
  shows "mdist_set m A x > 0"
  by (metis Metric_space.d_set_closed_pos Metric_space_mspace_mdist assms mdist_set_def mtopology_of_def)

lemma mdist_set_uniformly_continuous: "uniformly_continuous_map m euclidean_metric (mdist_set m A)"
  unfolding uniformly_continuous_map_def
proof safe
  fix e :: real
  assume "0 < e"
  then show "\<exists>\<delta>>0. \<forall>x\<in>mspace m. \<forall>y\<in>mspace m. mdist m y x < \<delta> \<longrightarrow> mdist euclidean_metric (mdist_set m A y) (mdist_set m A x) < e"
    using order.strict_trans1[OF mdist_set_abs_le] by(auto intro!: exI[where x=e] simp: dist_real_def)
qed simp

lemma uniformly_continuous_map_add:
  fixes f :: "'a \<Rightarrow> 'b::real_normed_vector"
  assumes "uniformly_continuous_map m euclidean_metric f" "uniformly_continuous_map m euclidean_metric g"
  shows "uniformly_continuous_map m euclidean_metric (\<lambda>x. f x + g x)"
  unfolding uniformly_continuous_map_def
proof safe
  fix e :: real
  assume "e > 0"
  from half_gt_zero[OF this] assms obtain d1 d2 where d: "d1 > 0" "d2 > 0"
   "\<And>x y. x \<in> mspace m \<Longrightarrow> y \<in> mspace m \<Longrightarrow> mdist m x y < d1 \<Longrightarrow> dist (f x) (f y) < e / 2"    "\<And>x y. x \<in> mspace m \<Longrightarrow> y \<in> mspace m \<Longrightarrow> mdist m x y < d2 \<Longrightarrow> dist (g x) (g y) < e / 2"
    by(simp only: uniformly_continuous_map_def mdist_euclidean_metric) metis
  show "\<exists>\<delta>>0. \<forall>y\<in>mspace m. \<forall>x\<in>mspace m. mdist m x y < \<delta> \<longrightarrow> mdist euclidean_metric (f x + g x) (f y + g y) < e"
    using d by(fastforce intro!: exI[where x="min d1 d2"] order.strict_trans1[OF dist_triangle_add])
qed simp

lemma uniformly_continuous_map_real_divide:
  fixes f :: "'a \<Rightarrow> real"
  assumes "uniformly_continuous_map m euclidean_metric f" "uniformly_continuous_map m euclidean_metric g"
      and "\<And>x. x \<in> mspace m \<Longrightarrow> g x \<noteq> 0" "\<And>x. x \<in> mspace m \<Longrightarrow> \<bar>g x\<bar> \<ge> a" "a > 0" "\<And>x. x \<in> mspace m \<Longrightarrow> \<bar>g x\<bar> < Kg"
      and "\<And>x. x \<in> mspace m \<Longrightarrow> \<bar>f x\<bar> < Kf"
    shows "uniformly_continuous_map m euclidean_metric (\<lambda>x. f x / g x)"
  unfolding uniformly_continuous_map_def
proof safe
  fix e :: real
  assume e[arith]:"e > 0"
  consider "mspace m \<noteq> {}" | "mspace m = {}" by auto
  then show "\<exists>\<delta>>0. \<forall>x\<in>mspace m. \<forall>y\<in>mspace m. mdist m y x < \<delta> \<longrightarrow> mdist euclidean_metric (f y / g y) (f x / g x) < e"
  proof cases
    case m:1
    then have Kfg_pos[arith]: "Kg > 0" "Kf \<ge> 0"
      using assms(4-7) by auto fastforce+
    define e' where "e' \<equiv> a^2 / (Kf + Kg)  * e"
    have e':"e' > 0"
      using assms(5) by(auto simp: e'_def)
    with assms obtain d1 d2 where d: "d1 > 0" "d2 > 0"
    "\<And>x y. x \<in> mspace m \<Longrightarrow> y \<in> mspace m \<Longrightarrow> mdist m x y < d1 \<Longrightarrow> \<bar>f x - f y\<bar> < e'"    "\<And>x y. x \<in> mspace m \<Longrightarrow> y \<in> mspace m \<Longrightarrow> mdist m x y < d2 \<Longrightarrow> \<bar>g x - g y\<bar> < e'"
      by(simp only: uniformly_continuous_map_def mdist_euclidean_metric dist_real_def) metis
    show ?thesis
      unfolding mdist_euclidean_metric dist_real_def
    proof(safe intro!: exI[where x="min d1 d2"])
      fix x y
      assume x:"x \<in> mspace m" and y:"y \<in> mspace m" and "mdist m x y < min d1 d2"
      then have dist[arith]: "mdist m x y < d1" "mdist m x y < d2" by auto
      note [arith] = assms(3,4,6,7)[OF x] assms(3,4,6,7)[OF y]
      have "\<bar>f x / g x - f y / g y\<bar> = \<bar>(f x * g y - f y * g x) / (g x * g y)\<bar>"
        by(simp add: diff_frac_eq)
      also have "... = \<bar>(f x * g y - f x * g x + (f x * g x  - f y * g x)) / (g x * g y)\<bar>"
        by simp
      also have "... = \<bar>(f x - f y) * g x - f x * (g x - g y)\<bar> / (\<bar>g x\<bar> * \<bar>g y\<bar>)"
        by(simp add: left_diff_distrib right_diff_distrib abs_mult)
      also have "... \<le> (\<bar>f x - f y\<bar> * \<bar>g x\<bar> + \<bar>f x\<bar> * \<bar>g x - g y\<bar>) / (\<bar>g x\<bar> * \<bar>g y\<bar>)"
        by(rule divide_right_mono) (use abs_triangle_ineq4 abs_mult in metis,auto)
      also have "... < (e' * Kg + Kf * e') / (\<bar>g x\<bar> * \<bar>g y\<bar>)"
        by(rule divide_strict_right_mono[OF add_less_le_mono]) (auto intro!: mult_mono' mult_strict_mono, use  d(3,4)[OF x y] in auto)
      also have "... \<le> (e' * Kg + Kf * e') / a^2"
        by(auto intro!: divide_left_mono simp: power2_eq_square) (insert assms(5) e', auto simp: \<open>a \<le> \<bar>g x\<bar>\<close> mult_mono')
      also have "... = (Kf + Kg) / a^2 * e'"
        by (simp add: distrib_left mult.commute)
      also have "... = e"
        using assms(5) by(auto simp: e'_def)
      finally show " \<bar>f x / g x - f y / g y\<bar> < e" .
    qed(use d in auto)
  qed (auto intro!: exI[where x=1])
qed simp

lemma
  assumes "e > 0"
  shows uniformly_continuous_map_from_capped_metric:"uniformly_continuous_map (capped_metric e m1) m2 f \<longleftrightarrow> uniformly_continuous_map m1 m2 f" (is ?g1)
    and uniformly_continuous_map_to_capped_metric:"uniformly_continuous_map m1 (capped_metric e m2) f \<longleftrightarrow> uniformly_continuous_map m1 m2 f" (is ?g2)
proof -
  have [simp]:"(\<lambda>n. min e (X n)) \<longlonglongrightarrow> 0 \<longleftrightarrow> X \<longlonglongrightarrow> 0" for X
  proof
    assume h:"(\<lambda>n. min e (X n)) \<longlonglongrightarrow> 0"
    show "X \<longlonglongrightarrow> 0"
      unfolding LIMSEQ_def dist_real_def
    proof safe
      fix r :: real
      assume "0 < r"
      then have "min (e / 2) r > 0"
        using assms by auto
      from LIMSEQ_D[OF h this] obtain N where N:"\<And>n. n \<ge> N \<Longrightarrow> \<bar>min e (X n)\<bar> < min (e / 2) r"
        by auto
      have "min e (X n) = X n" if h:"n \<ge> N " for n
      proof(rule ccontr)
        assume "min e (X n) \<noteq> X n"
        then have "min e (X n) = e"
          by auto
        with N[OF h] show False
          by auto
      qed
      with N show "\<exists>no. \<forall>n\<ge>no. \<bar>X n - 0\<bar> < r"
        by(auto intro!: exI[where x=N])
    qed
  qed(auto intro!: tendsto_eq_intros(4)[of "\<lambda>x. e" e sequentially X _ ] simp: assms)
  show ?g1 ?g2
    using assms by(auto simp: uniformly_continuous_map_sequentially capped_metric_mdist)
qed

lemma Urysohn_lemma_uniform:
  assumes "closedin (mtopology_of m) T" "closedin (mtopology_of m) U" "T \<inter> U = {}" "\<And>x y. x \<in> T \<Longrightarrow> y \<in> U \<Longrightarrow> mdist m x y \<ge> e" "e > 0"
  obtains f :: "'a \<Rightarrow> real"
  where "uniformly_continuous_map m euclidean_metric f"
        "\<And>x. f x \<ge> 0" "\<And>x. f x \<le> 1" "\<And>x. x \<in> T \<Longrightarrow> f x = 1" "\<And>x. x \<in> U \<Longrightarrow> f x = 0"
proof -
  consider "T = {}" | "U = {}" | "T \<noteq> {}" "U \<noteq> {}" by auto
  then show ?thesis
  proof cases
    case 1
    define f where "f \<equiv> (\<lambda>x::'a. 0::real)"
    with 1 have "uniformly_continuous_map m euclidean_metric f" "\<And>x. f x \<ge> 0" "\<And>x. f x \<le> 1" "\<And>x. x \<in> T \<Longrightarrow> f x = 1" "\<And>x. x \<in> U \<Longrightarrow> f x = 0"
      by auto
    then show ?thesis
      using that by auto
  next
    case 2
    define f where "f \<equiv> (\<lambda>x::'a. 1::real)"
    with 2 have "uniformly_continuous_map m euclidean_metric f" "\<And>x. f x \<ge> 0" "\<And>x. f x \<le> 1" "\<And>x. x \<in> T \<Longrightarrow> f x = 1" "\<And>x. x \<in> U \<Longrightarrow> f x = 0"
      by auto
    then show ?thesis
      using that by auto
  next
    case TU:3
    then have STU:"mspace m \<noteq> {}" "T \<subseteq> mspace m" "U \<subseteq> mspace m"
      using assms(1,2) closedin_topspace_empty closedin_subset by fastforce+
    interpret m: Metric_space "mspace m" "mdist (capped_metric e m)"
      by (metis Metric_space_mspace_mdist capped_metric_mspace)
    have e:"x \<in> T \<Longrightarrow> y \<in> U \<Longrightarrow> mdist (capped_metric e m) x y \<ge> e" for x y
      by (simp add: assms(4) capped_metric_mdist)
    define f where "f \<equiv> (\<lambda>x. mdist_set (capped_metric e m) U x / (mdist_set (capped_metric e m) U x + mdist_set (capped_metric e m) T x))"
    have "uniformly_continuous_map m euclidean_metric f"
      unfolding uniformly_continuous_map_from_capped_metric[OF assms(5),of m,symmetric] f_def
    proof(rule uniformly_continuous_map_real_divide[where Kf="e + 1" and Kg="2 * e + 1" and a="e / 2"])
      show "uniformly_continuous_map (capped_metric e m) euclidean_metric (mdist_set (capped_metric e m) U)"
           "uniformly_continuous_map (capped_metric e m) euclidean_metric (\<lambda>x. mdist_set (capped_metric e m) U x + mdist_set (capped_metric e m) T x)"
        by(auto intro!: mdist_set_uniformly_continuous uniformly_continuous_map_add)
    next
      fix x
      assume x:"x \<in> mspace (capped_metric e m)"
      then consider "x \<notin> T" | "x \<notin> U"
        using TU assms by auto
      thus "mdist_set (capped_metric e m) U x + mdist_set (capped_metric e m) T x \<noteq> 0"
      proof cases
        case 1
        with TU x assms have "mdist_set (capped_metric e m) T x > 0"
          by(auto intro!: mdist_set_closed_pos simp: mtopology_capped_metric)
        thus?thesis
          by (metis add_less_same_cancel2 linorder_not_less mdist_set_nonneg)
      next
        case 2
        with TU x assms have "mdist_set (capped_metric e m) U x > 0"
          by(auto intro!: mdist_set_closed_pos simp: mtopology_capped_metric)
        thus?thesis
          by (metis add_less_same_cancel1 linorder_not_less mdist_set_nonneg)
      qed
    next
      fix x
      assume x:"x \<in> mspace (capped_metric e m)"
      consider "x \<in> (\<Union>a\<in>U. m.mball a (e / 2))" | "x \<notin> (\<Union>a\<in>U. m.mball a (e / 2))" by auto
      then show "e / 2 \<le> \<bar>mdist_set (capped_metric e m) U x + mdist_set (capped_metric e m) T x\<bar>"
      proof cases
        case 1
        have "m.mball x (e / 2) \<inter> T = {}"
        proof(rule ccontr)
          assume "m.mball x (e / 2) \<inter> T \<noteq> {}"
          then obtain y where y: "y \<in> m.mball x (e / 2)" "y \<in> T"
            by blast
          then obtain u where u:"u \<in> U" "x \<in> m.mball u (e / 2)"
            using 1 by auto
          have "mdist (capped_metric e m) y u \<le> mdist (capped_metric e m) y x + mdist (capped_metric e m) x u"
            using STU u y x by(auto intro!: m.triangle)
          also have "... < e / 2 + e / 2"
            using y u by(auto simp: m.commute)
          also have "... = e" using assms(5) by linarith
          finally show False
            using e[OF y(2) u(1)] by simp
        qed
        from m.d_set_ball_empty[OF _ _ _ _ this] TU STU x assms(1,5)
        have "e / 2 \<le> m.d_set T x"
          using STU(2) x by auto
        also have "... \<le> \<bar>mdist_set (capped_metric e m) U x + mdist_set (capped_metric e m) T x\<bar>"
          by (simp add: mdist_set_def)
        finally show ?thesis .
      next
        case 2
        then have "m.mball x (e / 2) \<inter> U = {}"
          using x by (auto simp: m.commute)
        hence "e / 2 \<le> m.d_set U x"
          by (metis STU(3) TU(2) assms(5) capped_metric_mspace half_gt_zero m.d_set_ball_empty x)
        also have "... \<le> \<bar>mdist_set (capped_metric e m) U x + mdist_set (capped_metric e m) T x\<bar>"
          by (simp add: mdist_set_def)
        finally show ?thesis .
      qed
    next
      fix x
      assume "x \<in> mspace (capped_metric e m)"
      have "\<bar>mdist_set (capped_metric e m) U x + mdist_set (capped_metric e m) T x\<bar> = mdist_set (capped_metric e m) U x + mdist_set (capped_metric e m) T x"
        using mdist_set_nonneg by auto
      also have "... < (e + 1 / 2) + (e + 1 / 2)"
        apply(intro add_strict_mono mdist_set_bounded)
        using assms(5) add_strict_increasing[of "1 / 2",OF _ mdist_capped[OF assms(5),of m x]] by (auto simp add: add.commute)
      also have "... = 2 * e + 1"
        by auto
      finally show "\<bar>mdist_set (capped_metric e m) U x + mdist_set (capped_metric e m) T x\<bar> < 2 * e + 1" .
      show " \<bar>mdist_set (capped_metric e m) U x\<bar> < e + 1"
        using assms(5) add_strict_increasing[of 1,OF _ mdist_capped[OF assms(5),of m x]] by (auto simp add: add.commute intro!: mdist_set_bounded)
    qed(use assms in auto)
    moreover have "\<And>x. f x \<in>{0..1}"
    proof -
      fix x
      have "f x \<le> mdist_set (capped_metric e m) U x / mdist_set (capped_metric e m) U x"
      proof -
        consider "mdist_set (capped_metric e m) U x = 0" | "mdist_set (capped_metric e m) U x > 0"
          using antisym_conv1 by fastforce
        thus ?thesis
        proof cases
          case 2
          show ?thesis
            unfolding f_def by(rule divide_left_mono[OF _ _ mult_pos_pos]) (auto simp: 2 add_strict_increasing)
        qed (simp add: f_def)
      qed
      also have "... \<le> 1" by simp
      finally show "f x \<in> {0..1}"
        by (auto simp: f_def)
    qed      
    moreover have "f x = 1" if x:"x \<in> T" for x
    proof -
      { assume h:"mdist_set (capped_metric e m) U x = 0"
        then have "x \<notin> U" using assms STU x by blast
        hence False
          by (metis STU(2) TU(2) assms(2) capped_metric_mspace h mdist_set_closed_pos mtopology_capped_metric order_less_irrefl subset_eq x)
      }
      thus ?thesis
        by (metis add.right_neutral divide_self_if f_def mdist_set_nzeroD(2) x)
    qed
    moreover have "\<And>x. x \<in> U \<Longrightarrow> f x = 0"
      by (simp add: f_def m.d_set_inA mdist_set_def)
    ultimately show ?thesis
      using that by auto
  qed
qed

text \<open> Open maps \<close>
lemma Metric_space_open_map_from_dist:
  assumes "f \<in> mspace m1 \<rightarrow> mspace m2"
      and "\<And>x \<epsilon>. x \<in> mspace m1 \<Longrightarrow> \<epsilon> > 0 \<Longrightarrow> \<exists>\<delta>>0. \<forall>y\<in>mspace m1. mdist m2 (f x) (f y) < \<delta> \<longrightarrow> mdist m1 x y < \<epsilon>"
    shows "open_map (mtopology_of m1) (subtopology (mtopology_of m2) (f ` mspace m1)) f"
proof -
  interpret m1: Metric_space "mspace m1" "mdist m1" by simp
  interpret m2: Metric_space "mspace m2" "mdist m2" by simp
  interpret m2': Submetric "mspace m2" "mdist m2" "f ` mspace m1"
    using assms(1) by(auto simp: Submetric_def Submetric_axioms_def)
  have "open_map m1.mtopology m2'.sub.mtopology f"
  proof(safe intro!: open_map_with_base[OF m1.mtopology_base_in_balls])
    fix a and e :: real
    assume h:"a \<in> mspace m1" "0 < e"
    show "openin m2'.sub.mtopology (f ` m1.mball a e)"
      unfolding m2'.sub.openin_mtopology
    proof safe
      fix x
      assume x:"x \<in> m1.mball a e"
      then have xs:"x \<in> mspace m1"
        by auto
      have "0 < e - mdist m1 a x"
        using x by auto
      from assms(2)[OF xs this] obtain d where d:"d > 0" "\<And>y. y \<in> mspace m1 \<Longrightarrow> mdist m2 (f x) (f y) < d \<Longrightarrow> mdist m1 x y < e - mdist m1 a x"
        by auto
      show "\<exists>r>0. m2'.sub.mball (f x) r \<subseteq> f ` m1.mball a e"
      proof(safe intro!: exI[where x=d])
        fix z
        assume z:"z \<in> m2'.sub.mball (f x) d"
        then obtain y where y:"z = f y" "y \<in> mspace m1"
          by auto
        hence "mdist m2 (f x) (f y) < d"
          using z by simp
        hence "mdist m1 x y < e - mdist m1 a x"
          using d y by auto
        hence "mdist m1 a y < e"
          using h(1) x y m1.triangle[of a x y] by auto
        with h(1) show "z \<in> f ` m1.mball a e"
          by(auto simp: y)
      qed fact
    qed auto
  qed
  thus "open_map (mtopology_of m1) (subtopology (mtopology_of m2) (f ` mspace m1)) f"
    by (simp add: mtopology_of_def m2'.mtopology_submetric)
qed

subsubsection \<open> Separability in Metric Spaces \<close>

context Metric_space
begin

text \<open> For a metric space $M$, $M$ is separable iff $M$ is second countable.\<close>
lemma generated_by_countable_balls:
  assumes "countable U" and "mdense U"
  shows "mtopology = topology_generated_by {mball y (1 / real n) | y n. y \<in> U}"
proof -
  have hu: "U \<subseteq> M" "\<And>x \<epsilon>. x \<in> M \<Longrightarrow> \<epsilon> > 0 \<Longrightarrow> mball x \<epsilon> \<inter> U \<noteq> {}"
    using assms by(auto simp: mdense_def)
  show ?thesis
    unfolding base_is_subbase[OF mtopology_base_in_balls,simplified subbase_in_def]
  proof(rule topology_generated_by_eq)
    fix K
    assume "K \<in> {mball y (1 / real n) |y n. y \<in> U}"
    then show "openin (topology_generated_by {mball a \<epsilon> |a \<epsilon>. a \<in> M \<and> 0 < \<epsilon>}) K"
      by(auto simp: base_is_subbase[OF mtopology_base_in_balls,simplified subbase_in_def,symmetric])
  next
    have h0:"\<And>x \<epsilon>. x \<in> M \<Longrightarrow> \<epsilon> > 0 \<Longrightarrow> \<exists>y\<in>U. \<exists>n. x \<in> mball y (1 / real n) \<and> mball y (1 / real n) \<subseteq> mball x \<epsilon>"
    proof -
      fix x \<epsilon>
      assume h: "x \<in> M" "(0 :: real) < \<epsilon>"
      then obtain N where hn: "1 / \<epsilon> < real N"
        using reals_Archimedean2 by blast
      have hn0: "0 < real N"
        by(rule ccontr) (use hn h in fastforce)
      hence hn':"1 / real N < \<epsilon>"
        using h hn by (metis divide_less_eq mult.commute)
      have "mball x (1 / (2 * real N)) \<inter> U \<noteq> {}"
        using mdense_def[of U] assms(2) h(1) hn0 by fastforce
      then obtain y where hy:
        "y\<in>U" "y \<in> M" "y \<in> mball x (1 / (real (2 * N)))"
        using hu by auto
      show "\<exists>y\<in>U. \<exists>n. x \<in> mball y (1 / real n) \<and> mball y (1 / real n) \<subseteq> mball x \<epsilon>"
      proof(intro bexI[where x=y] exI[where x="2 * N"] conjI)
        show "x \<in> mball y (1 / real (2 * N))"
          using hy(3) by (auto simp: commute)
      next
        show "mball y (1 / real (2 * N)) \<subseteq> mball x \<epsilon>"
        proof
          fix y'
          assume hy':"y' \<in> mball y (1 / real (2 * N))"
          have "d x y' < \<epsilon>" (is "?lhs < ?rhs")
          proof -
            have "?lhs \<le> d x y + d y y'"
              using hy(2)  hy' h(1) triangle by auto
            also have "... < 1 / real (2 * N) + 1 / real (2 * N)"
              by(rule strict_ordered_ab_semigroup_add_class.add_strict_mono) (use hy(3) hy(2) hy' h(1) hy' in auto)
            finally show ?thesis
              using hn' by auto
          qed
          thus "y' \<in> mball x \<epsilon>"
            using hy' h(1) by auto
        qed
      qed fact
    qed
    fix K
    assume hk: "K \<in> {mball a \<epsilon> |a \<epsilon>. a \<in> M \<and> 0 < \<epsilon>}"
    then obtain x \<epsilon>x where hxe:
       "x \<in> M" "0 < \<epsilon>x" "K = mball x \<epsilon>x" by auto
    have gh:"K = (\<Union>{mball y (1 / real n) | y n. y \<in> U \<and> mball y (1 / real n) \<subseteq> K})"
    proof
      show "K \<subseteq> (\<Union> {mball y (1 / real n) |y n. y \<in> U \<and> mball y (1 / real n) \<subseteq> K})"
      proof
        fix k
        assume hkink:"k \<in> K"
        then have hkinS:"k \<in> M"
          by(simp add: hxe)
        obtain \<epsilon>k where hek: "\<epsilon>k > 0" "mball k \<epsilon>k \<subseteq> K"
          by (metis Metric_space.openin_mtopology Metric_space_axioms hxe(3) hkink openin_mball)
        obtain y n where hyey:
          "y \<in> U" "k \<in> mball y (1 / real n)" "mball y (1 / real n) \<subseteq> mball k \<epsilon>k"
          using h0[OF hkinS hek(1)] by auto
        show "k \<in>  \<Union> {mball y (1 / real n) |y n. y \<in> U \<and> mball y (1 / real n) \<subseteq> K}"
          using hek(2) hyey by blast
      qed
    qed auto
    show "openin (topology_generated_by {mball y (1 / real n) |y n. y \<in> U}) K"
      unfolding openin_topology_generated_by_iff
      apply(rule generate_topology_on.UN[of "{mball y (1 / real n) |y n. y \<in> U \<and> mball y (1 / real n) \<subseteq> K}", simplified gh[symmetric]])
      apply(rule generate_topology_on.Basis) by auto
  qed
qed

lemma separable_space_imp_second_countable:
  assumes "separable_space mtopology"
  shows "second_countable mtopology"
proof -
  obtain U where hu:
   "countable U" "mdense U"
    using assms separable_space_def2 by blast
  show ?thesis
  proof(rule countable_base_from_countable_subbase[where \<O>="{mball y (1 / real n) | y n. y \<in> U}"])
    have "{mball y (1 / real n) |y n. y \<in> U} = (\<lambda>(y,n). mball y (1 / real n)) ` (U \<times> UNIV)"
      by auto
    also have "countable ..."
      using hu by auto
    finally show "countable {mball y (1 / real n) |y n. y \<in> U}" .
  qed(use subbase_in_def generated_by_countable_balls[of U] hu in auto)
qed

corollary separable_space_iff_second_countable:
  "separable_space mtopology \<longleftrightarrow> second_countable mtopology"
  using second_countable_imp_separable_space separable_space_imp_second_countable by auto

lemma Lindelof_mdiameter:
  assumes "separable_space mtopology" "0 < e"
  shows "\<exists>U. countable U \<and> \<Union> U = M \<and> (\<forall>u\<in>U. mdiameter u < ennreal e)"
proof -
  have "(\<And>u. u \<in> {mball x (e / 3) |x. x \<in> M} \<Longrightarrow> openin mtopology u)"
    by auto
  moreover have "\<Union> {mball x (e / 3) |x. x \<in> M} = M"
    using assms by auto
  ultimately have "\<exists>U'. countable U' \<and> U' \<subseteq> {mball x (e / 3) |x. x \<in> M} \<and> \<Union> U' = M"
    using second_countable_imp_Lindelof_space[OF assms(1)[simplified separable_space_iff_second_countable]]
    by(auto simp: Lindelof_space_def)
  then obtain U' where U': "countable U'" "U' \<subseteq> {mball x (e / 3) |x. x \<in> M}" "\<Union> U' = M"
    by auto
  show ?thesis
  proof(safe intro!: exI[where x=U'])
    fix u
    assume "u \<in> U'"
    then obtain x where u:"u = mball x (e / 3)"
      using U' by auto
    have "mdiameter u \<le> ennreal (2 * (e / 3))"
      by(simp only: u mdiameter_ball_leq)
    also have "... < ennreal e"
      by(auto intro!: ennreal_lessI assms)
    finally show "mdiameter u < ennreal e" .
  qed(use U' in auto)
qed

end

lemma metrizable_space_separable_iff_second_countable:
  assumes "metrizable_space X"
  shows "separable_space X \<longleftrightarrow> second_countable X"
proof -
  obtain d where "Metric_space (topspace X) d" "Metric_space.mtopology (topspace X) d = X"
    by (metis assms(1) Metric_space.topspace_mtopology metrizable_space_def)
  thus ?thesis
    using Metric_space.separable_space_iff_second_countable by fastforce
qed

abbreviation "mdense_of m U \<equiv> dense_in (mtopology_of m) U"

lemma mdense_of_def: "mdense_of m U \<longleftrightarrow> (U \<subseteq> mspace m \<and> (\<forall>x\<in>mspace m. \<forall>\<epsilon>>0. mball_of m x \<epsilon> \<inter> U \<noteq> {}))"
  using Metric_space.mdense_def[of "mspace m" "mdist m"] by (simp add: mball_of_def mtopology_of_def)

lemma mdense_of_def2: "mdense_of m U \<longleftrightarrow> (U \<subseteq> mspace m \<and> (\<forall>x\<in>mspace m. \<forall>\<epsilon>>0. \<exists>y\<in>U. mdist m x y < \<epsilon>))"
  using Metric_space.mdense_def2[of "mspace m" "mdist m"] by (simp add: mtopology_of_def)

lemma mdense_of_def3: "mdense_of m U \<longleftrightarrow> (U \<subseteq> mspace m \<and> (\<forall>x\<in>mspace m. \<exists>xn. range xn \<subseteq> U \<and> limitin (mtopology_of m) xn x sequentially))"
  using Metric_space.mdense_def3[of "mspace m" "mdist m"] by (simp add: mtopology_of_def)

subsubsection \<open> Compact Metric Spaces\<close>

context Metric_space
begin

lemma mtotally_bounded_eq_compact_closedin:
  assumes "mcomplete" "closedin mtopology S"
  shows "mtotally_bounded S \<longleftrightarrow> S \<subseteq> M \<and> compactin mtopology S"
  by (metis assms closure_of_eq mtotally_bounded_eq_compact_closure_of)

lemma mtotally_bounded_def2: "mtotally_bounded S \<longleftrightarrow> (\<forall>\<epsilon>>0. \<exists>K. finite K \<and> K \<subseteq> M \<and> S \<subseteq> (\<Union>x\<in>K. mball x \<epsilon>))"
  unfolding mtotally_bounded_def
proof safe
  fix e :: real
  assume h:"e > 0" "\<forall>e>0. \<exists>K. finite K \<and> K \<subseteq> S \<and> S \<subseteq> (\<Union>x\<in>K. mball x e)"
  then show "\<exists>K. finite K \<and> K \<subseteq> M \<and> S \<subseteq> (\<Union>x\<in>K. mball x e)"
    by (metis Metric_space.mbounded_subset Metric_space.mtotally_bounded_imp_mbounded Metric_space_axioms mbounded_subset_mspace mtotally_bounded_def)
next
  fix e :: real
  assume "e > 0" "\<forall>\<epsilon>>0. \<exists>K. finite K \<and> K \<subseteq> M \<and> S \<subseteq> (\<Union>x\<in>K. mball x \<epsilon>)"
  then obtain K where K: "finite K" "K \<subseteq> M" "S \<subseteq> (\<Union>x\<in>K. mball x (e / 2))"
    by (meson half_gt_zero)
  define K' where "K' \<equiv> {x\<in>K. mball x (e / 2) \<inter> S \<noteq> {}}"
  have K'1:"finite K'" "K' \<subseteq> M"
    using K by(auto simp: K'_def)
  have K'2: "S \<subseteq> (\<Union>x\<in>K'. mball x (e / 2))"
  proof
    fix x
    assume x:"x \<in> S"
    then obtain k where k:"k \<in> K" "x \<in> mball k (e / 2)"
      using K by auto
    with x have "k \<in> K'"
      by(auto simp: K'_def)
    with k show "x \<in> (\<Union>x\<in>K'. mball x (e / 2))"
      by auto
  qed
  have "\<forall>k\<in>K'. \<exists>y. y \<in> mball k (e / 2) \<inter> S"
    by(auto simp: K'_def)
  then obtain xk where xk: "\<And>k. k \<in> K' \<Longrightarrow> xk k \<in> mball k (e / 2)" "\<And>k. k \<in> K' \<Longrightarrow> xk k \<in> S"
    by (metis IntD2 inf_commute)
  hence "\<And>k. k \<in> K' \<Longrightarrow> mball k (e / 2) \<subseteq> mball (xk k) e"
    using triangle commute by fastforce
  hence "(\<Union>x\<in>K'. mball x (e / 2)) \<subseteq> (\<Union>x\<in>xk ` K'. mball x e)"
    by blast
  with K'2 have "S \<subseteq> (\<Union>x\<in>xk ` K'. mball x e)"
    by blast
  thus "\<exists>K. finite K \<and> K \<subseteq> S \<and> S \<subseteq> (\<Union>x\<in>K. mball x e)"
    by(intro exI[where x="xk ` K'"]) (use xk(2) K'1(1) in blast)
qed

lemma compact_space_imp_separable:
  assumes "compact_space mtopology"
  shows "separable_space mtopology"
proof -
  have "\<exists>A. finite A \<and> A \<subseteq> M \<and> M \<subseteq> \<Union> ((\<lambda>a. mball a (1 / real (Suc n))) ` A)" for n
    using assms by(auto simp: compact_space_eq_mcomplete_mtotally_bounded mtotally_bounded_def)
  then obtain A where A: "\<And>n. finite (A n)" "\<And>n. A n \<subseteq> M" "\<And>n. M \<subseteq>  \<Union> ((\<lambda>a. mball a (1 / real (Suc n))) ` (A n))"
    by metis
  define K where "K \<equiv> \<Union> (range A)"
  have 1: "countable K"
    using A(1) by(auto intro!: countable_UN[of _ id,simplified] simp: K_def countable_finite)
  show "separable_space mtopology"
    unfolding mdense_def2 separable_space_def2
  proof(safe intro!: exI[where x=K] 1)
    fix x and \<epsilon> :: real
    assume h: "x \<in> M" "0 < \<epsilon>"
    then obtain n where n:"1 / real (Suc n) \<le> \<epsilon>"
      by (meson nat_approx_posE order.strict_iff_not)
    then obtain y where y: "y \<in> A n" "x \<in> mball y (1 / real (Suc n))"
      using h(1) A(3)[of n] by auto
    thus "\<exists>y\<in>K. d x y < \<epsilon>"
      using n by(auto intro!: bexI[where x=y] simp: commute K_def)
  qed(use K_def A(2) in auto)
qed

lemma separable_space_cfunspace:
  assumes "separable_space mtopology" mcomplete
      and "metrizable_space X" "compact_space X"
    shows "separable_space (mtopology_of (cfunspace X Self))"
proof -
  consider "topspace X = {}" | "topspace X \<noteq> {}" "M = {}" | "topspace X \<noteq> {}" "M \<noteq> {}" by auto
  thus ?thesis
  proof cases
    case 1
    then show ?thesis
      by(auto intro!: countable_space_separable_space)
  next
    case 2
    then have [simp]:"mtopology = trivial_topology"
      using topspace_mtopology by auto
    have 1:"topspace (mtopology_of (cfunspace X Self)) = {}"
      apply simp
      using 2(1) by(auto simp: mtopology_of_def)
    show ?thesis
      by(rule countable_space_separable_space, simp only: 1) simp
  next
    case XS_nem:3
    have cm: "mcomplete_of (cfunspace X Self)"
      by (simp add: assms(2) mcomplete_cfunspace)
    show ?thesis
    proof -
      obtain dx where dx: "Metric_space (topspace X) dx" "Metric_space.mtopology (topspace X) dx = X"
        by (metis Metric_space.topspace_mtopology assms(3) metrizable_space_def)
      interpret dx: Metric_space "topspace X" dx
        by fact
      have dx_c: dx.mcomplete
        using assms by(auto intro!: dx.compact_space_imp_mcomplete simp: dx(2))
      have "\<exists>B. finite B \<and> B \<subseteq> topspace X \<and> topspace X \<subseteq> (\<Union>a\<in>B. dx.mball a (1 / Suc m))" for m
        using dx.compactin_imp_mtotally_bounded[of "topspace X"] assms(4)
        by(fastforce simp: dx(2) compact_space_def dx.mtotally_bounded_def2)
      then obtain Xm where Xm: "\<And>m. finite (Xm m)" "\<And>m. (Xm m) \<subseteq> topspace X" "\<And>m. topspace X \<subseteq> (\<Union>a\<in>Xm m. dx.mball a (1 / Suc m))"
        by metis
      hence Xm_eq: "\<And>m. topspace X = (\<Union>a\<in>Xm m. dx.mball a (1 / Suc m))"
        by fastforce
      have Xm_nem:"\<And>m. (Xm m) \<noteq> {}"
        using XS_nem Xm_eq by blast
      define xmk where "xmk \<equiv> (\<lambda>m. from_nat_into (Xm m))"
      define km where "km \<equiv> (\<lambda>m. card (Xm m))"
      have km_pos:"km m > 0" for m
        by(simp add: km_def card_gt_0_iff Xm Xm_nem)
      have xmk_bij: "bij_betw (xmk m) {..<km m} (Xm m)" for m
        using bij_betw_from_nat_into_finite[OF Xm(1)] by(simp add: km_def xmk_def)
      have xmk_into: "xmk m i \<in> Xm m" for m i
        by (simp add: Xm_nem from_nat_into xmk_def)
      have "\<exists>U. countable U \<and> \<Union> U = M \<and> (\<forall>u\<in>U. mdiameter u < 1 / (Suc l))" for l
        by(rule Lindelof_mdiameter[OF assms(1)]) auto
      then obtain U where U: "\<And>l. countable (U l)" "\<And>l. (\<Union> (U l)) = M" "\<And>l u. u \<in> U l \<Longrightarrow> mdiameter u < 1 / Suc l"
        by metis
      have Ul_nem: "U l \<noteq> {}" for l
        using XS_nem U(2) by auto
      define uli where "uli \<equiv> (\<lambda>l. from_nat_into (U l))"
      have uli_into:"uli l i \<in> U l" for l i
        by (simp add: Ul_nem from_nat_into uli_def)
      hence uli_diam: "mdiameter (uli l i) < 1 / Suc l" for l i
        using U(3) by auto
      have uli_un:"M = (\<Union>i. uli l i)" for l
        by(auto simp: range_from_nat_into[OF Ul_nem[of l] U(1)] uli_def U)
      define Cmn where "Cmn \<equiv> (\<lambda>m n. {f \<in> mspace (cfunspace X Self). \<forall>x\<in>topspace X. \<forall>y\<in>topspace X. dx x y < 1 / (Suc m) \<longrightarrow> d (f x) (f y) < 1 / Suc n})"
      define fmnls where "fmnls \<equiv> (\<lambda>m n l s. SOME f. f \<in> Cmn m n \<and> (\<forall>j<km m. f (xmk m j) \<in> uli l (s j)))"
      define Dmnl where "Dmnl \<equiv> (\<lambda>m n l. {fmnls m n l s |s. s \<in> {..<km m} \<rightarrow>\<^sub>E UNIV \<and> (\<exists>f \<in> Cmn m n. (\<forall>j<km m. f (xmk m j) \<in> uli l (s j))) })"
      have in_Dmnl: "fmnls m n l s \<in> Dmnl m n l" if "s\<in>{..<km m} \<rightarrow>\<^sub>E UNIV" "f\<in> Cmn m n" "\<forall>j<km m. f (xmk m j) \<in> uli l (s j)"for m n l s f
        using Dmnl_def that by blast
      define Dmn where "Dmn \<equiv> (\<lambda>m n. \<Union>l. Dmnl m n l)"
      have Dmn_subset: "Dmn m n \<subseteq> Cmn m n" for m n
      proof -
        have "Dmnl m n l \<subseteq> Cmn m n" for l
          by(auto simp: Dmnl_def fmnls_def someI[of "\<lambda>f. f \<in> Cmn m n \<and> (\<forall>j<km m. f (xmk m j) \<in> uli l (_ j))"])
        thus ?thesis by(auto simp: Dmn_def)
      qed
      have c_Dmn: "countable (Dmn m n)" for m n
      proof -
        have "countable (Dmnl m n l)" for l
        proof -
          have 1:"Dmnl m n l \<subseteq> (\<lambda>s. fmnls m n l s) ` ({..<km m} \<rightarrow>\<^sub>E UNIV)"
            by(auto simp: Dmnl_def)
          have "countable ..."
            by(auto intro!: countable_PiE)
          with 1 show ?thesis
            using countable_subset by blast
        qed
        thus ?thesis
          by(auto simp: Dmn_def)
      qed
      have claim: "\<exists>g\<in>Dmn m n. \<forall>y\<in>Xm m. d (f y) (g y) < e" if f:"f \<in> Cmn m n" and e:"e > 0" for f m n e
      proof -
        obtain l where l:"1 / Suc l < e"
          using e nat_approx_posE by blast
        define s where "s \<equiv> (\<lambda>i\<in>{..<km m}. SOME j. f (xmk m i) \<in> uli l j)"
        have s1:"s\<in>{..<km m} \<rightarrow>\<^sub>E UNIV" by(simp add: s_def)
        have s2:"\<forall>i<km m. f (xmk m i) \<in> uli l (s i)"
        proof -
          fix i
          have "f (xmk m i) \<in> uli l (SOME j. f (xmk m i) \<in> uli l j)" for i
          proof(rule someI_ex)
            have "xmk m i \<in> topspace X"
              using Xm(2) xmk_into by auto
            hence "f (xmk m i) \<in> M"
              using f by(auto simp: Cmn_def continuous_map_def)
            thus "\<exists>x. f (xmk m i) \<in> uli l x"
              using uli_un by auto
          qed
          thus ?thesis
            by (auto simp: s_def)
        qed
        have fmnls:"fmnls m n l s \<in> Cmn m n \<and> (\<forall>j<km m. fmnls m n l s (xmk m j) \<in> uli l (s j))"
          by(simp add: fmnls_def,rule someI[where x=f],auto simp: s2 f)
        show "\<exists>g\<in>Dmn m n. \<forall>y\<in>Xm m. d (f y) (g y) < e"
        proof(safe intro!: bexI[where x="fmnls m n l s"])
          fix y
          assume y:"y \<in> Xm m"
          then obtain i where i:"i < km m" "xmk m i = y"
            by (meson xmk_bij[of m] bij_betw_iff_bijections lessThan_iff)
          have "f y \<in> uli l (s i)" "fmnls m n l s y \<in> uli l (s i)"
            using i(1) s2 fmnls by(auto simp: i(2)[symmetric])
          moreover have "f y \<in> M" "fmnls m n l s y \<in> M"
            using f fmnls y Xm(2)[of m] by(auto simp: Cmn_def continuous_map_def)
          ultimately have "ennreal (d (f y) (fmnls m n l s y)) \<le> mdiameter (uli l (s i))"
            by(auto intro!: mdiameter_is_sup)
          also have "... < ennreal (1 / Suc l)"
            by(rule uli_diam)
          also have "... < ennreal e"
            using l e by(auto intro!: ennreal_lessI)
          finally show "d (f y) (fmnls m n l s y) < e"
            by(simp add: ennreal_less_iff[OF nonneg])
        qed(use in_Dmnl[OF s1 f s2] Dmn_def in auto)
      qed
      show "separable_space (mtopology_of (cfunspace X Self))"
        unfolding separable_space_def2 mdense_of_def2
      proof(safe intro!: exI[where x="\<Union>n. (\<Union>m. Dmn m n)"])
        fix f and e :: real
        assume h:"f \<in>  mspace (cfunspace X Self)" "0 < e"
        then obtain n where n:"1 / Suc n < e / 4"
          by (metis zero_less_divide_iff zero_less_numeral nat_approx_posE)
        have "\<exists>m. \<forall>l\<ge> m. f \<in> Cmn l n"
        proof -
          have "uniformly_continuous_map dx.Self Self f"
            using continuous_eq_uniformly_continuous_map[of dx.Self Self f] h assms(4) by(auto simp: mtopology_of_def dx)
          then obtain \<delta> where \<delta>:"\<delta> > 0" "\<And>x y. x\<in>topspace X \<Longrightarrow> y\<in>topspace X \<Longrightarrow> dx x y < \<delta> \<Longrightarrow> d (f x) (f y) < 1 / (Suc n)"
            by(simp only: uniformly_continuous_map_def) (metis  dx.mdist_Self dx.mspace_Self mdist_Self of_nat_0_less_iff zero_less_Suc zero_less_divide_1_iff)
          then obtain m where m:"1 / Suc m < \<delta>"
            using nat_approx_posE by blast
          have l: "l \<ge> m \<Longrightarrow> 1 / Suc l \<le> 1 / Suc m" for l
            by (simp add: frac_le)
          show ?thesis
            using \<delta>(2)[OF _ _ order.strict_trans[OF _ order.strict_trans1[OF l m]]] h by(auto simp: Cmn_def)
        qed
        then obtain m where m:"f \<in> Cmn m n" by auto
        obtain g where g:"g\<in>Dmn m n" "\<And>y. y\<in>Xm m \<Longrightarrow> d (f y) (g y) < e / 4"
          by (metis claim[OF m] h(2) zero_less_divide_iff zero_less_numeral)
        have "\<exists>n m. \<exists>g\<in>Dmn m n. mdist (cfunspace X Self) f g < e"
        proof(rule exI[where x=n])
          show "\<exists>m. \<exists>g\<in>Dmn m n. mdist (cfunspace X Self) f g < e"
          proof(intro exI[where x=m] bexI[OF _ g(1)])
            have g_cm:"g \<in> mspace (cfunspace X Self)"
              using g(1) Dmn_subset[of m n] by(auto simp: Cmn_def)
            have "mdist (cfunspace X Self) f g \<le> 3 * e / 4"
            proof(rule mdist_cfunspace_le)
              fix x
              assume x:"x \<in> topspace X"
              obtain y where y:"y \<in> Xm m" "x \<in> dx.mball y (1 / real (Suc m))"
                using Xm(3) x by fastforce
              hence ytop:"y \<in> topspace X"
                by auto
              have "mdist Self (f x) (g x) \<le> d (f x) (f y) + d (f y) (g x)"
                using x g_cm h(1) ytop by(auto intro!: triangle simp: continuous_map_def)
              also have "... \<le> d (f x) (f y) + d (f y) (g y) + d (g y) (g x)"
                using x g_cm h(1) ytop by(auto intro!: triangle simp: continuous_map_def)
              also have "... \<le> e / 4 + e / 4 + e / 4"
              proof -
                have dxy: "dx x y < 1 / Suc m" "dx y x < 1 / Suc m"
                  using y(2) by(auto simp: dx.commute)
                hence "d (f x) (f y) < 1 / (Suc n)" "d (g y) (g x) < 1 / (Suc n)"
                  using m x ytop g Dmn_subset[of m n] by(auto simp: Cmn_def)
                hence "d (f x) (f y) < e / 4" "d (g y) (g x) < e / 4"
                  using n by auto
                thus ?thesis
                  using g(2)[OF y(1)] by auto
              qed
              finally show "mdist Self (f x) (g x) \<le> 3 * e / 4"
                by simp
            qed(use h in auto)
            also have "... < e"
              using h by auto
            finally show "mdist (cfunspace X Self) f g < e" .
          qed
        qed
        thus "\<exists>y\<in>\<Union>n m. Dmn m n. mdist (cfunspace X Self) f y  < e"
          by auto
      qed(insert Dmn_subset c_Dmn,unfold Cmn_def, blast)+
    qed
  qed
qed

end

context Submetric
begin

lemma separable_sub:
  assumes "separable_space mtopology"
  shows "separable_space sub.mtopology"
  using assms unfolding separable_space_iff_second_countable sub.separable_space_iff_second_countable
  by(auto simp: second_countable_subtopology mtopology_submetric)

end

subsubsection  \<open>Discrete Distance\<close>
lemma(in discrete_metric) separable_space_iff: "separable_space disc.mtopology \<longleftrightarrow> countable M"
  by(simp add: mtopology_discrete_metric separable_space_discrete_topology)

subsubsection  \<open>Binary Product Metric Spaces\<close>
text \<open> We define the $L^{1}$-distance. $L^{1}$-distance and $L^{2}$ distance (Euclid distance)
       generate the same topological space.\<close>

definition "prod_dist_L1 \<equiv> \<lambda>d1 d2 (x,y) (x',y'). d1 x x' + d2 y y'"

context Metric_space12
begin

lemma prod_L1_metric: "Metric_space (M1 \<times> M2) (prod_dist_L1 d1 d2)"
proof
  fix x y z
  assume "x \<in> M1 \<times> M2" "y \<in> M1 \<times> M2" "z \<in> M1 \<times> M2"
  then show "prod_dist_L1 d1 d2 x z \<le> prod_dist_L1 d1 d2 x y + prod_dist_L1 d1 d2 y z"
    by(auto simp: prod_dist_L1_def) (metis M1.commute M1.triangle'' M2.commute M2.triangle'' ab_semigroup_add_class.add_ac(1) add.left_commute add_mono)
qed(auto simp: prod_dist_L1_def add_nonneg_eq_0_iff M1.commute M2.commute)

sublocale Prod_metric_L1: Metric_space "M1 \<times> M2" "prod_dist_L1 d1 d2"
  by(simp add: prod_L1_metric)

lemma prod_dist_L1_geq:
  shows "d1 x y \<le> prod_dist_L1 d1 d2 (x,x') (y,y')"
        "d2 x' y' \<le> prod_dist_L1 d1 d2 (x,x') (y,y')"
  by(auto simp: prod_dist_L1_def)

lemma prod_dist_L1_ball:
  assumes "(x,x') \<in> Prod_metric_L1.mball (a,a') \<epsilon>"
    shows "x \<in> M1.mball a \<epsilon>"
      and "x' \<in> M2.mball a' \<epsilon>"
  using assms prod_dist_L1_geq order.strict_trans1 by simp_all blast+

lemma prod_dist_L1_ball':
  assumes "z \<in> Prod_metric_L1.mball a \<epsilon>"
    shows "fst z \<in> M1.mball (fst a) \<epsilon>"
      and "snd z \<in> M2.mball (snd a) \<epsilon>"
  using prod_dist_L1_ball[of "fst z" "snd z" "fst a" "snd a" \<epsilon>] assms by auto

lemma prod_dist_L1_ball1': "Prod_metric_L1.mball (a1,a2) (min e1 e2) \<subseteq> M1.mball a1 e1 \<times> M2.mball a2 e2"
  using prod_dist_L1_geq order.strict_trans1 by auto blast+

lemma prod_dist_L1_ball1:
  assumes "b1 \<in> M1.mball a1 e1" "b2 \<in> M2.mball a2 e2"
  shows "\<exists>e12>0. Prod_metric_L1.mball (b1,b2) e12 \<subseteq> M1.mball a1 e1 \<times> M2.mball a2 e2"
proof -
  obtain ea1 ea2 where ea: "ea1 > 0" "ea2 > 0" "M1.mball b1 ea1 \<subseteq> M1.mball a1 e1" "M2.mball b2 ea2 \<subseteq> M2.mball a2 e2"
    using assms by (meson M1.openin_mball M1.openin_mtopology M2.openin_mball M2.openin_mtopology)
  thus ?thesis
    using prod_dist_L1_ball1'[of b1 b2 ea1 ea2] by(auto intro!: exI[where x="min ea1 ea2"])
qed

lemma prod_dist_L1_ball2':
  "M1.mball a1 e1 \<times> M2.mball a2 e2 \<subseteq> Prod_metric_L1.mball (a1,a2) (e1 + e2)"
  by auto (auto simp: prod_dist_L1_def)

lemma prod_dist_L1_ball2:
  assumes "(b1,b2) \<in> Prod_metric_L1.mball (a1,a2) e12"
    shows "\<exists>e1>0. \<exists>e2>0. M1.mball b1 e1 \<times> M2.mball b2 e2 \<subseteq> Prod_metric_L1.mball (a1,a2) e12"
proof -
  obtain e12' where "e12' > 0" "Prod_metric_L1.mball (b1,b2) e12' \<subseteq> Prod_metric_L1.mball (a1,a2) e12"
    by (metis assms Prod_metric_L1.openin_mball Prod_metric_L1.openin_mtopology)
  thus ?thesis
    using prod_dist_L1_ball2'[of b1 "e12' / 2" b2 "e12' / 2"] by(auto intro!: exI[where x="e12' / 2"])
qed

lemma prod_dist_L1_mtopology:
  "Prod_metric_L1.mtopology = prod_topology M1.mtopology M2.mtopology"
proof -
  have "Prod_metric_L1.mtopology = topology_generated_by { M1.mball a1 e1 \<times> M2.mball a2 e2 | a1 a2 e1 e2. a1 \<in> M1 \<and> a2 \<in> M2 \<and> e1 > 0 \<and> e2 > 0}"
    unfolding base_is_subbase[OF Prod_metric_L1.mtopology_base_in_balls,simplified subbase_in_def]
  proof(rule topology_generated_by_eq)
    fix U
    assume "U \<in> {M1.mball a1 e1 \<times> M2.mball a2 e2 | a1 a2 e1 e2. a1 \<in> M1 \<and> a2 \<in> M2 \<and> 0 < e1 \<and> 0 < e2}"
    then obtain a1 e1 a2 e2 where hae:
    "U = M1.mball a1 e1 \<times> M2.mball a2 e2" "a1 \<in> M1" "a2 \<in> M2" "0 < e1" "0 < e2"
      by auto
    show "openin (topology_generated_by {Prod_metric_L1.mball a \<epsilon> |a \<epsilon>. a \<in> M1 \<times> M2 \<and> 0 < \<epsilon>}) U"
      unfolding base_is_subbase[OF Prod_metric_L1.mtopology_base_in_balls,simplified subbase_in_def,symmetric] Prod_metric_L1.openin_mtopology hae(1)
      using prod_dist_L1_ball1[of _ a1 e1 _ a2 e2] by fastforce
  next
    fix U
    assume "U \<in> {Prod_metric_L1.mball a \<epsilon> |a \<epsilon>. a \<in> M1 \<times> M2 \<and> 0 < \<epsilon>}"
    then obtain a1 a2 \<epsilon> where hae:
    "U = Prod_metric_L1.mball (a1,a2) \<epsilon>" "a1 \<in> M1" "a2 \<in> M2" "0 < \<epsilon>"
      by auto
    show "openin (topology_generated_by {M1.mball a1 e1 \<times> M2.mball a2 e2 | a1 a2 e1 e2. a1 \<in> M1 \<and> a2 \<in> M2 \<and> 0 < e1 \<and> 0 < e2}) U"
      unfolding openin_subopen[of _ "Prod_metric_L1.mball (a1,a2) \<epsilon>"] hae(1)
    proof safe
      fix b1 b2
      assume h:"(b1, b2) \<in> Prod_metric_L1.mball (a1, a2) \<epsilon>"
      from prod_dist_L1_ball2[OF this] obtain e1 e2 where "e1 > 0" "e2 > 0" "M1.mball b1 e1 \<times> M2.mball b2 e2 \<subseteq> Prod_metric_L1.mball (a1, a2) \<epsilon>"
        by metis
      with h show "\<exists>T. openin (topology_generated_by {M1.mball a1 e1 \<times> M2.mball a2 e2 | a1 a2 e1 e2. a1 \<in> M1 \<and> a2 \<in> M2 \<and> 0 < e1 \<and> 0 < e2}) T \<and> (b1, b2) \<in> T \<and> T \<subseteq> Prod_metric_L1.mball (a1, a2) \<epsilon>"
        unfolding openin_topology_generated_by_iff
        by(auto intro!: generate_topology_on.Basis exI[where x="M1.mball b1 e1 \<times> M2.mball b2 e2"])
    qed
  qed
  also have "... = prod_topology M1.mtopology M2.mtopology"
  proof -
    have "{M1.mball a \<epsilon> \<times> M2.mball a' \<epsilon>' |a a' \<epsilon> \<epsilon>'. a \<in> M1 \<and> a' \<in> M2 \<and> 0 < \<epsilon> \<and> 0 < \<epsilon>'} = {U \<times> V |U V. U \<in> {M1.mball a \<epsilon> |a \<epsilon>. a \<in> M1 \<and> 0 < \<epsilon>} \<and> V \<in> {M2.mball a \<epsilon> |a \<epsilon>. a \<in> M2 \<and> 0 < \<epsilon>}}"
      by blast
    thus ?thesis
      unfolding base_is_subbase[OF M1.mtopology_base_in_balls,simplified subbase_in_def] base_is_subbase[OF M2.mtopology_base_in_balls,simplified subbase_in_def]
      by(simp only: prod_topology_generated_by[symmetric])
  qed
  finally show ?thesis .
qed

lemma prod_dist_L1_limitin_iff: "limitin Prod_metric_L1.mtopology zn z sequentially \<longleftrightarrow> limitin M1.mtopology (\<lambda>n. fst (zn n)) (fst z) sequentially \<and> limitin M2.mtopology (\<lambda>n. snd (zn n)) (snd z) sequentially"
proof safe
  assume h:"limitin Prod_metric_L1.mtopology zn z sequentially"
  show "limitin M1.mtopology (\<lambda>n. fst (zn n)) (fst z) sequentially"
       "limitin M2.mtopology (\<lambda>n. snd (zn n)) (snd z) sequentially"
    unfolding M1.limit_metric_sequentially M2.limit_metric_sequentially
  proof safe
    fix e :: real
    assume e: "0 < e"
    with h obtain N where N:"\<And>n. n \<ge> N \<Longrightarrow> zn n \<in> M1 \<times> M2" "\<And>n. n \<ge> N \<Longrightarrow> prod_dist_L1 d1 d2 (zn n) z < e"
      by(simp only: Prod_metric_L1.limit_metric_sequentially) metis
    show "\<exists>N. \<forall>n\<ge>N. fst (zn n) \<in> M1 \<and> d1 (fst (zn n)) (fst z) < e"
         "\<exists>N. \<forall>n\<ge>N. snd (zn n) \<in> M2 \<and> d2 (snd (zn n)) (snd z) < e"
    proof(safe intro!: exI[where x=N])
      fix n
      assume "N \<le> n"
      from N[OF this]
      show "d1 (fst (zn n)) (fst z) < e" " d2 (snd (zn n)) (snd z) < e"
        using order.strict_trans1[OF prod_dist_L1_geq(1)[of "fst (zn n)" "fst z" "snd (zn n)" "snd z"]] order.strict_trans1[OF prod_dist_L1_geq(2)[of "snd (zn n)" "snd z" "fst (zn n)" "fst z"]]
        by auto
    qed(use N(1)[simplified mem_Times_iff] in auto)
  qed(use h Prod_metric_L1.limit_metric_sequentially in auto)
next
  assume h:"limitin M1.mtopology (\<lambda>n. fst (zn n)) (fst z) sequentially"
           "limitin M2.mtopology (\<lambda>n. snd (zn n)) (snd z) sequentially"
  show "limitin Prod_metric_L1.mtopology zn z sequentially"
    unfolding Prod_metric_L1.limit_metric_sequentially
  proof safe
    fix e :: real
    assume e: "0 < e"
    with h obtain N1 N2 where N: "\<And>n. n \<ge> N1 \<Longrightarrow> fst (zn n) \<in> M1" "\<And>n. n \<ge> N1 \<Longrightarrow> d1 (fst (zn n)) (fst z) < e / 2"
      "\<And>n. n \<ge> N2 \<Longrightarrow> snd (zn n) \<in> M2" "\<And>n. n \<ge> N2 \<Longrightarrow> d2 (snd (zn n)) (snd z) < e / 2"
      unfolding M1.limit_metric_sequentially M2.limit_metric_sequentially
      using half_gt_zero by metis
    thus "\<exists>N. \<forall>n\<ge>N. zn n \<in> M1 \<times> M2 \<and> prod_dist_L1 d1 d2 (zn n) z < e"
      by(fastforce intro!: exI[where x="max N1 N2"] simp: prod_dist_L1_def split_beta' mem_Times_iff)
  qed(auto simp: mem_Times_iff h[simplified M1.limit_metric_sequentially M2.limit_metric_sequentially])
qed

lemma prod_dist_L1_MCauchy_iff: "Prod_metric_L1.MCauchy zn \<longleftrightarrow> M1.MCauchy (\<lambda>n. fst (zn n)) \<and> M2.MCauchy (\<lambda>n. snd (zn n))"
proof safe
  assume h:"Prod_metric_L1.MCauchy zn"
  show "M1.MCauchy (\<lambda>n. fst (zn n))" "M2.MCauchy (\<lambda>n. snd (zn n))"
    unfolding M1.MCauchy_def M2.MCauchy_def
  proof safe
    fix e :: real
    assume "0 < e"
    with h obtain N where N:"\<And>n m. N \<le> n \<Longrightarrow> N \<le> m \<Longrightarrow> prod_dist_L1 d1 d2 (zn n) (zn m) < e"
      by(fastforce simp: Prod_metric_L1.MCauchy_def)
    show "\<exists>N. \<forall>n n'. N \<le> n \<longrightarrow> N \<le> n' \<longrightarrow> d1 (fst (zn n)) (fst (zn n')) < e" " \<exists>N. \<forall>n n'. N \<le> n \<longrightarrow> N \<le> n' \<longrightarrow> d2 (snd (zn n)) (snd (zn n')) < e"
    proof(safe intro!: exI[where x=N])
      fix n m
      assume "n \<ge> N" "m \<ge> N"
      from N[OF this]
      show "d1 (fst (zn n)) (fst (zn m)) < e" "d2 (snd (zn n)) (snd (zn m)) < e"
        using order.strict_trans1[OF prod_dist_L1_geq(1)[of "fst (zn n)" "fst (zn m)" "snd (zn n)" "snd (zn m)"]] order.strict_trans1[OF prod_dist_L1_geq(2)[of "snd (zn n)" "snd (zn m)" "fst (zn n)" "fst (zn m)"]]
        by auto
    qed
  next
    have "\<And>n. zn n \<in> M1 \<times> M2"
      using h by(auto simp: Prod_metric_L1.MCauchy_def)
    thus "fst (zn n) \<in> M1" "snd (zn n) \<in> M2" for n
      by (auto simp: mem_Times_iff)
  qed
next
  assume h:"M1.MCauchy (\<lambda>n. fst (zn n))" "M2.MCauchy (\<lambda>n. snd (zn n))"
  show "Prod_metric_L1.MCauchy zn"
    unfolding Prod_metric_L1.MCauchy_def
  proof safe
    fix e :: real
    assume "0 < e"
    with h obtain N1 N2 where "\<And>n m. n \<ge> N1 \<Longrightarrow> m \<ge> N1 \<Longrightarrow> d1 (fst (zn n)) (fst (zn m)) < e / 2"
         "\<And>n m. n \<ge> N2 \<Longrightarrow> m \<ge> N2 \<Longrightarrow> d2 (snd (zn n)) (snd (zn m)) < e / 2"
      unfolding M1.MCauchy_def M2.MCauchy_def using half_gt_zero by metis
    thus "\<exists>N. \<forall>n n'. N \<le> n \<longrightarrow> N \<le> n' \<longrightarrow> prod_dist_L1 d1 d2 (zn n) (zn n') < e"
      by(fastforce intro!: exI[where x="max N1 N2"] simp: prod_dist_L1_def split_beta')
  next
    fix x y n
    assume 1:"(x,y) = zn n"
    have "fst (zn n) \<in> M1" "snd (zn n) \<in> M2"
      using h[simplified M1.MCauchy_def M2.MCauchy_def] by auto
    thus "x \<in> M1" "y \<in> M2"
      by(simp_all add: 1[symmetric])
  qed
qed

end

subsubsection  \<open>Sum Metric Spaces\<close>
locale Sum_metric =
  fixes I :: "'i set"
    and Mi :: "'i \<Rightarrow> 'a set"
    and di :: "'i \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> real"
  assumes Mi_disj: "disjoint_family_on Mi I"
      and d_nonneg: "\<And>i x y. 0 \<le> di i x y"
      and d_bounded: "\<And>i x y. di i x y < 1"
      and Md_metric: "\<And>i. i \<in> I \<Longrightarrow> Metric_space (Mi i) (di i)"
begin

abbreviation "M \<equiv> \<Union>i\<in>I. Mi i"

lemma Mi_inj_on:
  assumes "i \<in> I" "j \<in> I" "a \<in> Mi i" "a \<in> Mi j"
  shows "i = j"
  using Mi_disj assms by(auto simp: disjoint_family_on_def)

definition sum_dist :: "['a, 'a] \<Rightarrow> real" where
"sum_dist x y \<equiv> (if x \<in> M \<and> y \<in> M then (if \<exists>i\<in>I. x \<in> Mi i \<and> y \<in> Mi i then di (THE i. i \<in> I \<and> x \<in> Mi i \<and> y \<in> Mi i) x y else 1) else 0)"

lemma sum_dist_simps:
  shows "\<And>i. \<lbrakk>i \<in> I; x \<in> Mi i; y \<in> Mi i\<rbrakk> \<Longrightarrow> sum_dist x y = di i x y"
    and "\<And>i j. \<lbrakk>i \<in> I; j \<in> I; i \<noteq> j; x \<in> Mi i; y \<in> Mi j\<rbrakk> \<Longrightarrow> sum_dist x y = 1"
    and "\<And>i. \<lbrakk>i \<in> I; y \<in> M; x \<in> Mi i; y \<notin> Mi i\<rbrakk> \<Longrightarrow> sum_dist x y = 1"
    and "\<And>i. \<lbrakk>i \<in> I; x \<in> M; y \<in> Mi i; x \<notin> Mi i\<rbrakk> \<Longrightarrow> sum_dist x y = 1"
    and "x \<notin> M \<Longrightarrow> sum_dist x y = 0" "y \<notin> M \<Longrightarrow> sum_dist x y = 0"
proof -
  { fix i
    assume h:"i \<in> I" "x \<in> Mi i" "y \<in> Mi i"
    then have "sum_dist x y = di (THE i. i \<in> I \<and> x \<in> Mi i \<and> y \<in> Mi i) x y"
      by(auto simp: sum_dist_def)
    also have "... = di i x y"
    proof -
      have "(THE i. i \<in> I \<and> x \<in> Mi i \<and> y \<in> Mi i) = i"
        using Mi_disj h by(auto intro!: the1_equality simp: disjoint_family_on_def)
      thus ?thesis by simp
    qed
    finally show "sum_dist x y = di i x y" . }
  show "\<And>i j. \<lbrakk>i \<in> I; j \<in> I; i \<noteq> j; x \<in> Mi i; y \<in> Mi j\<rbrakk> \<Longrightarrow> sum_dist x y = 1"
       "\<And>i. \<lbrakk>i \<in> I; y \<in> M; x \<in> Mi i; y \<notin> Mi i\<rbrakk> \<Longrightarrow> sum_dist x y = 1" "\<And>i. \<lbrakk>i \<in> I; x \<in> M; y \<in> Mi i; x \<notin> Mi i\<rbrakk> \<Longrightarrow> sum_dist x y = 1"
       "x \<notin> M \<Longrightarrow> sum_dist x y = 0" "y \<notin> M \<Longrightarrow> sum_dist x y = 0"
    using Mi_disj by(auto simp: sum_dist_def disjoint_family_on_def dest: Mi_inj_on)
qed

lemma sum_dist_if_less1:
  assumes "i \<in> I" "x \<in> Mi i" "y \<in> M" "sum_dist x y < 1"
  shows "y \<in> Mi i"
  using assms sum_dist_simps(3) by fastforce

lemma inM_cases:
  assumes "x \<in> M" "y \<in> M"
      and "\<And>i. \<lbrakk>i \<in> I; x \<in> Mi i; y \<in> Mi i\<rbrakk> \<Longrightarrow> P x y"
      and "\<And>i j. \<lbrakk>i \<in> I; j \<in> I; i \<noteq> j; x \<in> Mi i; y \<in> Mi j; x \<noteq> y\<rbrakk> \<Longrightarrow> P x y"
    shows "P x y" using assms by auto

sublocale Sum_metric: Metric_space M sum_dist
proof
  fix x y
  assume "x \<in> M" "y \<in> M"
  then show "sum_dist x y = 0 \<longleftrightarrow> x = y"
    by(rule inM_cases, insert Md_metric) (auto simp: sum_dist_simps Metric_space_def)
next
  { fix i x y
    assume h: "i \<in> I" "x \<in> Mi i" "y \<in> Mi i"
    then have "sum_dist x y = di i x y"
              "sum_dist y x = di i x y"
      using Md_metric by(auto simp: sum_dist_simps Metric_space_def) }
  thus "\<And>x y. sum_dist x y = sum_dist y x"
    by (metis (no_types, lifting) sum_dist_def)
next
  show 1:"\<And>x y. 0 \<le> sum_dist x y"
    using d_nonneg by(simp add: sum_dist_def)
  fix x y z
  assume h: "x \<in> M" "y \<in> M" "z \<in> M"
  show "sum_dist x z \<le> sum_dist x y + sum_dist y z" (is "?lhs \<le> ?rhs")
  proof(rule inM_cases[OF h(1,3)])
    fix i
    assume h':"i \<in> I" "x \<in> Mi i" "z \<in> Mi i"
    consider "y \<in> Mi i" | "y \<notin> Mi i" by auto
    thus "?lhs \<le> ?rhs"
    proof cases
      case 1
      with h' Md_metric [OF h'(1)] show ?thesis
        by(simp add: sum_dist_simps Metric_space_def)
    next
      case 2
      with h' h(2) d_bounded[of i x z] 1[of y z]
      show ?thesis
        by(auto simp: sum_dist_simps)
    qed
  next
    fix i j
    assume h': "i \<in> I" "j \<in> I" "i \<noteq> j" "x \<in> Mi i" "z \<in> Mi j"
    consider "y \<notin> Mi i" | "y \<notin> Mi j"
      using h' h(2) Mi_disj by(auto simp: disjoint_family_on_def)
    thus "?lhs \<le> ?rhs"
      by (cases, insert 1[of x y] 1[of y z] h' h(2)) (auto simp: sum_dist_simps)
  qed
qed

lemma sum_dist_le1: "sum_dist x y \<le> 1"
  using d_bounded[of _ x y] by(auto simp: sum_dist_def less_eq_real_def)


lemma sum_dist_ball_eq_ball:
  assumes "i \<in> I" "e \<le> 1" "x \<in> Mi i"
  shows "Metric_space.mball (Mi i) (di i) x e = Sum_metric.mball x e"
proof -
  interpret m: Metric_space "Mi i" "di i"
    by(simp add: assms Md_metric)
  show ?thesis
    using assms sum_dist_simps(1)[OF assms(1) assms(3)] sum_dist_if_less1[OF assms(1,3)]
    by(fastforce simp: Sum_metric.mball_def)
qed

lemma ball_le_sum_dist_ball:
  assumes "i \<in> I"
  shows "Metric_space.mball (Mi i) (di i) x e \<subseteq> Sum_metric.mball x e"
proof -
  interpret m: Metric_space "Mi i" "di i"
    by(simp add: assms Md_metric)
  show ?thesis
    using assms by(auto simp: sum_dist_simps)
qed

lemma openin_mtopology_iff:
 "openin Sum_metric.mtopology U \<longleftrightarrow> U \<subseteq> M \<and> (\<forall>i\<in>I. openin (Metric_space.mtopology (Mi i) (di i)) (U \<inter> Mi i))"
proof safe
  fix i
  assume h:"openin Sum_metric.mtopology U" "i \<in> I"
  then interpret m: Metric_space "Mi i" "di i"
    using Md_metric by simp
  show "openin m.mtopology (U \<inter> Mi i)"
    unfolding m.openin_mtopology
  proof safe
    fix x
    assume x:"x \<in> U" "x \<in> Mi i"
    with h obtain e where e: "e > 0" "Sum_metric.mball x e \<subseteq> U"
      by(auto simp: Sum_metric.openin_mtopology)
    show "\<exists>\<epsilon>>0. m.mball x \<epsilon> \<subseteq> U \<inter> Mi i"
    proof(safe intro!: exI[where x=e])
      fix y
      assume "y \<in> m.mball x e"
      with h(2) have "y \<in> Sum_metric.mball x e"
        by(auto simp:sum_dist_simps)
      with e show "y \<in> U" by blast
    qed(use e in auto)
  qed
next
  show "\<And>x. openin Sum_metric.mtopology U \<Longrightarrow> x \<in> U \<Longrightarrow> x \<in> M"
    by(auto simp: Sum_metric.openin_mtopology)
next
  assume h: "U \<subseteq> M" "\<forall>i\<in>I. openin (Metric_space.mtopology (Mi i) (di i)) (U \<inter> Mi i)"
  show "openin Sum_metric.mtopology U"
    unfolding Sum_metric.openin_mtopology
  proof safe
    fix x
    assume x: "x \<in> U"
    then obtain i where i: "i \<in> I" "x \<in> Mi i"
      using h(1) by auto
    then interpret m: Metric_space "Mi i" "di i"
      using Md_metric by simp
    obtain e where e: "e > 0" "m.mball x e \<subseteq> U \<inter> Mi i"
      using i h(2) by (meson IntI m.openin_mtopology x)
    show "\<exists>\<epsilon>>0. Sum_metric.mball x \<epsilon> \<subseteq> U"
    proof(safe intro!: exI[where x="min e 1"])
      fix y
      assume y:"y \<in> Sum_metric.mball x (min e 1)"
      then show "y \<in> U"
        using sum_dist_ball_eq_ball[OF i(1) _ i(2),of "min e 1"] e by fastforce
    qed(simp add: e)
  qed(use h(1) in auto)
qed

corollary openin_mtopology_Mi:
  assumes "i \<in> I"
  shows "openin Sum_metric.mtopology (Mi i)"
  unfolding openin_mtopology_iff
proof safe
  fix j
  assume j:"j \<in> I"
  then interpret m: Metric_space "Mi j" "di j"
    by(simp add: Md_metric)
  show "openin m.mtopology (Mi i \<inter> Mi j)"
    by (cases "i = j", insert assms Mi_disj j) (auto simp: disjoint_family_on_def)
qed(use assms in auto)

corollary subtopology_mtopology_Mi:
  assumes "i \<in> I"
  shows "subtopology Sum_metric.mtopology (Mi i) = Metric_space.mtopology (Mi i) (di i)"
proof -
  interpret Mi: Metric_space "Mi i" "di i"
    by (simp add: Md_metric assms)
  show ?thesis
    unfolding topology_eq openin_subtopology
  proof safe
    fix T
    assume "openin Sum_metric.mtopology T"
    thus "openin Mi.mtopology (T \<inter> Mi i)"
      using assms by(auto simp: openin_mtopology_iff)
  next
    fix S
    assume h:"openin Mi.mtopology S"
    show "\<exists>T. openin Sum_metric.mtopology T \<and> S = T \<inter> Mi i"
    proof(safe intro!: exI[where x=S])
      show "openin Sum_metric.mtopology S"
        unfolding openin_mtopology_iff
      proof safe
        fix j
        assume j:"j \<in> I"
        then interpret Mj: Metric_space "Mi j" "di j"
          using Md_metric by auto
        have "i \<noteq> j \<Longrightarrow> S \<inter> Mi j = {}"
          using openin_subset[OF h] Mi_disj j assms
          by(auto simp: disjoint_family_on_def)
        thus "openin Mj.mtopology (S \<inter> Mi j)"
          by(cases "i = j") (use openin_subset[OF h] h in auto)
      qed(use openin_subset[OF h] assms in auto)
    qed(use openin_subset[OF h] assms in auto)
  qed
qed

lemma limitin_Mi_limitin_M:
  assumes "i \<in> I" "limitin (Metric_space.mtopology (Mi i) (di i)) xn x sequentially"
  shows "limitin Sum_metric.mtopology xn x sequentially"
proof -
  interpret m: Metric_space "Mi i" "di i"
    by(simp add: assms Md_metric)
  {
    fix e :: real
    assume "e > 0"
    then obtain N where "\<And>n. n \<ge> N \<Longrightarrow> xn n \<in> m.mball x e"
      using assms(2) m.commute m.limit_metric_sequentially by fastforce
    hence "\<exists>N. \<forall>n\<ge>N. xn n \<in> Sum_metric.mball x e"
      using ball_le_sum_dist_ball[OF assms(1),of x e]
      by(fastforce intro!: exI[where x=N]) }
  thus ?thesis
    by (metis Sum_metric.commute Sum_metric.in_mball Sum_metric.limit_metric_sequentially UN_I m.limitin_mspace assms)
qed

lemma limitin_M_limitin_Mi:
  assumes "limitin Sum_metric.mtopology xn x sequentially"
  shows "\<exists>i\<in>I. limitin (Metric_space.mtopology (Mi i) (di i)) xn x sequentially"
proof -
  obtain i where i: "i \<in> I" "x \<in> Mi i"
    using assms by (meson Sum_metric.limitin_mspace UN_E)
  then interpret m: Metric_space "Mi i" "di i"
    by(simp add: Md_metric)
  obtain N where N: "\<And>n. n \<ge> N \<Longrightarrow> sum_dist (xn n) x < 1" "\<And>n. n \<ge> N \<Longrightarrow> (xn n) \<in> M"
    using assms by (metis d_bounded i(2) m.mdist_zero Sum_metric.limit_metric_sequentially)
  hence xni: "n \<ge> N \<Longrightarrow> xn n \<in> Mi i" for n
    using assms by(auto intro!: sum_dist_if_less1[OF i,of "xn n"] simp: Sum_metric.commute)
  show ?thesis
  proof(safe intro!: bexI[where x=i] i)
    show "limitin m.mtopology xn x sequentially"
      unfolding m.limit_metric_sequentially
    proof safe
      fix e :: real
      assume e: "0 < e"
      then obtain N' where N': "\<And>n. n \<ge> N' \<Longrightarrow> sum_dist (xn n) x < e"
        using assms by (meson Sum_metric.limit_metric_sequentially)
      hence "n \<ge> max N N' \<Longrightarrow> di i (xn n) x < e" for n
        using sum_dist_simps(1)[OF i(1) xni[of n] i(2),symmetric] by auto        
      thus "\<exists>N. \<forall>n\<ge>N. xn n \<in> Mi i \<and> di i (xn n) x < e"
        using xni by(auto intro!: exI[where x="max N N'"])
    qed fact
  qed
qed

lemma MCauchy_Mi_MCauchy_M:
  assumes "i \<in> I" "Metric_space.MCauchy (Mi i) (di i) xn"
  shows "Sum_metric.MCauchy xn"
proof -
  interpret m: Metric_space "Mi i" "di i"
    by(simp add: assms Md_metric)
  have [simp]:"sum_dist (xn n) (xn m) = di i (xn n) (xn m)" for n m
    using assms sum_dist_simps(1)[OF assms(1),of "xn n" "xn m"]
    by(auto simp: m.MCauchy_def)
  show ?thesis
    using assms by(auto simp: m.MCauchy_def Sum_metric.MCauchy_def)
qed

lemma MCauchy_M_MCauchy_Mi:
  assumes "Sum_metric.MCauchy xn"
  shows "\<exists>m. \<exists>i\<in>I. Metric_space.MCauchy (Mi i) (di i) (\<lambda>n. xn (n + m))"
proof -
  obtain N where N: "\<And>n m. n \<ge> N \<Longrightarrow> m \<ge> N \<Longrightarrow> sum_dist (xn n) (xn m) < 1"
    using assms by(fastforce simp: Sum_metric.MCauchy_def)
  obtain i where i: "i \<in> I" "xn N \<in> Mi i"
    by (metis assms Sum_metric.MCauchy_def UNIV_I UN_E image_eqI subsetD)
  then have xn:"\<And>n. n \<ge> N \<Longrightarrow> xn n \<in> Mi i"
    by (metis N Sum_metric.MCauchy_def assms dual_order.refl range_subsetD sum_dist_if_less1)
  interpret m: Metric_space "Mi i" "di i"
    using i Md_metric by auto
  show ?thesis
  proof(safe intro!: exI[where x=N] bexI[where x=i])
    show "m.MCauchy (\<lambda>n. xn (n + N))"
      unfolding m.MCauchy_def
    proof safe
      show 1: "\<And>n. xn (n + N) \<in> Mi i"
        by(auto intro!: xn)
      fix e :: real
      assume "0 < e"
      then obtain N' where N': "\<And>n m. n \<ge> N' \<Longrightarrow> m \<ge> N' \<Longrightarrow> sum_dist (xn n) (xn m) < e"
        using Sum_metric.MCauchy_def assms by blast
      thus "\<exists>N'. \<forall>n n'. N' \<le> n \<longrightarrow> N' \<le> n' \<longrightarrow> di i (xn (n + N)) (xn (n' + N)) < e"
        by(auto intro!: exI[where x="N'"] simp: sum_dist_simps(1)[OF i(1) xn xn,symmetric])
    qed
  qed fact
qed

lemma separable_Mi_separable_M:
  assumes "countable I" "\<And>i. i \<in> I \<Longrightarrow> separable_space (Metric_space.mtopology (Mi i) (di i))"
  shows "separable_space Sum_metric.mtopology"
proof -
  obtain Ui where Ui: "\<And>i. i \<in> I \<Longrightarrow> countable (Ui i)" "\<And>i. i \<in> I \<Longrightarrow> dense_in (Metric_space.mtopology (Mi i) (di i)) (Ui i)"
    using assms by(simp only: separable_space_def2) metis
  define U where "U \<equiv> \<Union>i\<in>I. Ui i"
  show "separable_space Sum_metric.mtopology"
    unfolding separable_space_def2
  proof(safe intro!: exI[where x=U])
    show "countable U"
      using Ui(1) assms by(auto simp: U_def)
  next
    show "Sum_metric.mdense U"
      unfolding Sum_metric.mdense_def U_def
    proof safe
      fix i x
      assume "i \<in> I" "x \<in> Ui i"
      then show "x \<in> M"
        using Ui(2) by(auto intro!: bexI[where x=i] simp: Md_metric Metric_space.mdense_def2)
    next
      fix i x e
      assume h:"i \<in> I" "x \<in> Mi i" "(0 :: real) < e" "Sum_metric.mball x e \<inter> \<Union> (Ui ` I) = {}"
      then interpret m: Metric_space "Mi i" "di i"
        by(simp add: Md_metric)
      have "m.mball x e \<inter> Ui i \<noteq> {}"
        using Ui(2)[OF h(1)] h by(auto simp: m.mdense_def)
      hence "m.mball x e \<inter> \<Union> (Ui ` I) \<noteq> {}"
        using h(1) by blast
      thus False
        using ball_le_sum_dist_ball[OF \<open>i \<in> I\<close>,of x e] h(4) by blast
    qed
  qed
qed

lemma separable_M_separable_Mi:
  assumes "separable_space Sum_metric.mtopology" "\<And>i. i \<in> I"
  shows "separable_space (Metric_space.mtopology (Mi i) (di i))"
  using subtopology_mtopology_Mi[OF assms(2)] separable_space_open_subset[OF assms(1) openin_mtopology_Mi[OF assms(2)]]
  by simp

lemma mcomplete_Mi_mcomplete_M:
  assumes "\<And>i. i \<in> I \<Longrightarrow> Metric_space.mcomplete (Mi i) (di i)"
  shows Sum_metric.mcomplete
  unfolding Sum_metric.mcomplete_def
proof safe
  fix xn
  assume "Sum_metric.MCauchy xn"
  from MCauchy_M_MCauchy_Mi[OF this] obtain m i where mi:
  "i \<in> I" "Metric_space.MCauchy (Mi i) (di i) (\<lambda>n. xn (n + m))"
    by metis
  then interpret m: Metric_space "Mi i" "di i"
    by(simp add: Md_metric)
  from assms[OF mi(1)] mi(2) obtain x where x: "limitin m.mtopology (\<lambda>n. xn (n + m)) x sequentially"
    by(auto simp: m.mcomplete_def)
  from limitin_Mi_limitin_M[OF mi(1) limitin_sequentially_offset_rev[OF this]]
  show "\<exists>x. limitin Sum_metric.mtopology xn x sequentially"
    by auto
qed

lemma mcomplete_M_mcomplete_Mi:
  assumes Sum_metric.mcomplete "i \<in> I"
  shows "Metric_space.mcomplete (Mi i) (di i)"
proof -
  interpret Mi: Metric_space "Mi i" "di i"
    using assms(2) Md_metric by fastforce
  show ?thesis
    unfolding Mi.mcomplete_def
  proof safe
    fix xn
    assume xn:"Mi.MCauchy xn"
    from MCauchy_Mi_MCauchy_M[OF assms(2) this] assms(1) obtain x where "limitin Sum_metric.mtopology xn x sequentially"
      by(auto simp: Sum_metric.mcomplete_def)
    from limitin_M_limitin_Mi[OF this] obtain j where j:"j \<in> I" "limitin (Metric_space.mtopology (Mi j) (di j)) xn x sequentially"
      by auto
    have "j = i"
    proof -
      obtain N where "\<And>n. n \<ge> N \<Longrightarrow> xn n \<in> Mi j"
        by (metis Md_metric Metric_space.limitin_metric_dist_null eventually_sequentially j)
      hence "xn N \<in> Mi i \<inter> Mi j"
        using xn by(auto simp: Mi.MCauchy_def)
      with Mi_disj j(1) assms(2) show ?thesis
        by(fastforce simp: disjoint_family_on_def)
    qed
    thus "\<exists>x. limitin Mi.mtopology xn x sequentially"
      using j(2) by(auto intro!: exI[where x=x])
  qed
qed

end

lemma sum_metricI:
  fixes Si
  assumes "disjoint_family_on Si I"
      and "\<And>i x y. i \<notin> I \<Longrightarrow> 0 \<le> di i x y"
      and "\<And>i x y. di i x y < 1"
      and "\<And>i. i \<in> I \<Longrightarrow> Metric_space (Si i) (di i)"
    shows "Sum_metric I Si di"
  using assms by (metis Metric_space.nonneg Sum_metric_def) 

(* TDODO?: Sum metric space for Abstract type *)

end