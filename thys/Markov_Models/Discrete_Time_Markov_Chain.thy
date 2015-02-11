(* Author: Johannes Hölzl <hoelzl@in.tum.de> *)

section {* Discrete-Time Markov Chain *}

theory Discrete_Time_Markov_Chain
  imports
    Probability
    "~~/src/HOL/Library/Linear_Temporal_Logic_on_Streams"
    "../Coinductive/Coinductive_Stream"
    "../Coinductive/Coinductive_Nat"
begin

lemma not_MInfty_nonneg[simp]: "0 \<le> (x::ereal) \<Longrightarrow> x \<noteq> - \<infinity>"
  by auto

lemma ereal_of_enat_Sup:
  assumes "A \<noteq> {}" shows "ereal_of_enat (Sup A) = (\<Squnion>a\<in>A. ereal_of_enat a)"
proof (intro antisym mono_Sup)
  show "ereal_of_enat (Sup A) \<le> (\<Squnion>a\<in>A. ereal_of_enat a)"
  proof cases
    assume "finite A"
    with `A \<noteq> {}` obtain a where "a \<in> A" "ereal_of_enat (Sup A) = ereal_of_enat a"
      using Max_in[of A] by (auto simp: Sup_enat_def simp del: Max_in)
    then show ?thesis
      by (auto intro: SUP_upper)
  next
    assume "\<not> finite A"
    have [simp]: "(\<Squnion>a\<in>A. ereal_of_enat a) = \<top>"
      unfolding SUP_eq_top_iff
    proof safe
      fix x :: ereal assume "x < \<top>"
      then obtain n :: nat where "x < n"
        using less_PInf_Ex_of_nat top_ereal_def by auto
      obtain a where "a \<in> A - enat ` {.. n}"
        by (metis `\<not> finite A` all_not_in_conv finite_Diff2 finite_atMost finite_imageI finite.emptyI)
      then have "a \<in> A" "ereal n \<le> ereal_of_enat a"
        by (auto simp: image_iff Ball_def)
           (metis enat_iless enat_ord_simps(1) ereal_of_enat_less_iff ereal_of_enat_simps(1) less_le not_less)
      with `x < n` show "\<exists>i\<in>A. x < ereal_of_enat i"
        by (auto intro!: bexI[of _ a])
    qed
    show ?thesis
      by simp
  qed
qed (simp add: mono_def)

lemma mcont_ereal_of_enat: "mcont Sup (op \<le>) Sup op \<le> ereal_of_enat"
  by (auto intro!: mcontI monotoneI contI ereal_of_enat_Sup)

lemma mcont2mcont_ereal_of_enat[cont_intro]:
  "mcont lub ord Sup op \<le> f \<Longrightarrow> mcont lub ord Sup op \<le> (\<lambda>x. ereal_of_enat (f x))"
  by (auto intro: ccpo.mcont2mcont[OF complete_lattice_ccpo'] mcont_ereal_of_enat)

lemma ereal_of_enat_eSuc[simp]: "ereal_of_enat (eSuc x) = 1 + ereal_of_enat x"
  by (cases x) (auto simp: eSuc_enat)

declare stream.exhaust[cases type: stream]

lemma lfp_pair: "lfp (\<lambda>f (a, b). F (\<lambda>a b. f (a, b)) a b) (a, b) = lfp F a b"
  unfolding lfp_def
  by (auto intro!: INF_eq simp: le_fun_def)
     (auto intro!: exI[of _ "\<lambda>(a, b). x a b" for x])

lemma all_Suc_split: "(\<forall>i. P i) \<longleftrightarrow> (P 0 \<and> (\<forall>i. P (Suc i)))"
  using nat_induct by auto

lemma scount_eq_emeasure: "scount P \<omega> = emeasure (count_space UNIV) {i. P (sdrop i \<omega>)}"
proof cases
  assume "alw (ev P) \<omega>"
  moreover then have "infinite {i. P (sdrop i \<omega>)}"
    using infinite_iff_alw_ev[of P \<omega>] by simp
  ultimately show ?thesis
    by (simp add: scount_infinite_iff)
next
  assume "\<not> alw (ev P) \<omega>"
  moreover then have "finite {i. P (sdrop i \<omega>)}"
    using infinite_iff_alw_ev[of P \<omega>] by simp
  ultimately show ?thesis
    by (simp add: not_alw_iff not_ev_iff scount_eq_card)
qed

lemma measurable_scount[measurable]: 
  assumes [measurable]: "Measurable.pred (stream_space M) P"
  shows "scount P \<in> measurable (stream_space M) (count_space UNIV)"
  unfolding scount_eq[abs_def] by measurable

lemma measurable_sfirst[measurable]: 
  assumes "Measurable.pred (stream_space M) P"
  shows "sfirst P \<in> measurable (stream_space M) (count_space UNIV)"
  apply (coinduction rule: measurable_enat_coinduct)
  apply simp
  apply (rule exI[of _ "\<lambda>x. 0"])
  apply (rule exI[of _ stl])
  apply (rule exI[of _ P])
  apply (subst sfirst.simps[abs_def])
  apply simp
  apply fact
  done


context order
begin

definition
  "maximal f S = {x\<in>S. \<forall>y\<in>S. f y \<le> f x}"

lemma maximalI: "x \<in> S \<Longrightarrow> (\<And>y. y \<in> S \<Longrightarrow> f y \<le> f x) \<Longrightarrow> x \<in> maximal f S"
  by (simp add: maximal_def)

lemma maximalI_trans: "x \<in> maximal f S \<Longrightarrow> f x \<le> f y \<Longrightarrow> y \<in> S \<Longrightarrow> y \<in> maximal f S"
  unfolding maximal_def by (blast intro: antisym order_trans)

lemma maximalD1: "x \<in> maximal f S \<Longrightarrow> x \<in> S"
  by (simp add: maximal_def)

lemma maximalD2: "x \<in> maximal f S \<Longrightarrow> y \<in> S \<Longrightarrow> f y \<le> f x"
  by (simp add: maximal_def)

lemma maximal_inject: "x \<in> maximal f S \<Longrightarrow> y \<in> maximal f S \<Longrightarrow> f x = f y"
  unfolding maximal_def by (blast intro: antisym)

lemma maximal_empty[simp]: "maximal f {} = {}"
  by (simp add: maximal_def)

lemma maximal_singleton[simp]: "maximal f {x} = {x}"
  by (auto simp add: maximal_def)

lemma maximal_in_S: "maximal f S \<subseteq> S"
  using assms by (auto simp: maximal_def)

end

context linorder
begin

lemma maximal_ne:
  assumes "finite S" "S \<noteq> {}"
  shows "maximal f S \<noteq> {}"
  using assms
proof (induct rule: finite_ne_induct)
  case (insert s S)
  show ?case
  proof cases
    assume "\<forall>x\<in>S. f x \<le> f s"
    with insert have "s \<in> maximal f (insert s S)"
      by (auto intro!: maximalI)
    then show ?thesis
      by auto
  next
    assume "\<not> (\<forall>x\<in>S. f x \<le> f s)"
    then have "maximal f (insert s S) = maximal f S"
      by (auto simp: maximal_def)
    with insert show ?thesis
      by auto
  qed
qed simp
  
end

lemma mono_les:
  fixes s S N and l1 l2 :: "'a \<Rightarrow> real" and K :: "'a \<Rightarrow> 'a pmf"
  defines "\<Delta> x \<equiv> l2 x - l1 x"
  assumes s: "s \<in> S" and S: "(\<Union>s\<in>S. K s) \<subseteq> S \<union> N"
  assumes int_l1[simp]: "\<And>s. s \<in> S \<Longrightarrow> integrable (K s) l1"
  assumes int_l2[simp]: "\<And>s. s \<in> S \<Longrightarrow> integrable (K s) l2"
  assumes to_N: "\<And>s. s \<in> S \<Longrightarrow> \<exists>t\<in>N. (s, t) \<in> (SIGMA s:UNIV. K s)\<^sup>*"
  assumes l1: "\<And>s. s \<in> S \<Longrightarrow> (\<integral>t. l1 t \<partial>K s) + c s \<le> l1 s"
  assumes l2: "\<And>s. s \<in> S \<Longrightarrow> l2 s \<le> (\<integral>t. l2 t \<partial>K s) + c s"
  assumes eq: "\<And>s. s \<in> N \<Longrightarrow> l2 s \<le> l1 s"
  assumes finitary: "finite (\<Delta> ` (S\<union>N))"
  shows "l2 s \<le> l1 s"
proof -
  def M \<equiv> "{s\<in>S\<union>N. \<forall>t\<in>S\<union>N. \<Delta> t \<le> \<Delta> s}"

  have [simp]: "\<And>s. s\<in>S \<Longrightarrow> integrable (K s) \<Delta>"
    by (simp add: \<Delta>_def[abs_def])

  have M_unqiue: "\<And>s t. s \<in> M \<Longrightarrow> t \<in> M \<Longrightarrow> \<Delta> s = \<Delta> t"
    by (auto intro!: antisym simp: M_def)
  have M1: "\<And>s. s \<in> M \<Longrightarrow> s \<in> S \<union> N"
    by (auto simp: M_def)
  have M2: "\<And>s t. s \<in> M \<Longrightarrow> t \<in> S \<union> N \<Longrightarrow> \<Delta> t \<le> \<Delta> s"
    by (auto simp: M_def)
  have M3: "\<And>s t. s \<in> M \<Longrightarrow> t \<in> S \<union> N \<Longrightarrow> t \<notin> M \<Longrightarrow> \<Delta> t < \<Delta> s"
    by (auto simp: M_def less_le)

  have N: "\<forall>s\<in>N. \<Delta> s \<le> 0"
    using eq by (simp add: \<Delta>_def)

  { fix s assume s: "s \<in> M" "M \<inter> N = {}"
    then have "s \<in> S - N"
      by (auto dest: M1)
    with to_N[of s] obtain t where "(s, t) \<in> (SIGMA s:UNIV. K s)\<^sup>*" and "t \<in> N"
      by (auto simp: M_def)
    from this(1) `s \<in> M` have "\<Delta> s \<le> 0"
    proof (induction rule: converse_rtrancl_induct)
      case (step s s')
      then have s: "s \<in> M" "s \<in> S" "s \<notin> N" and s': "s' \<in> S \<union> N" "s' \<in> K s"
        using S `M \<inter> N = {}` by (auto dest: M1)
      have "s' \<in> M"
      proof (rule ccontr)
        assume "s' \<notin> M"
        with `s \<in> S` s' `s \<in> M`
        have "0 < pmf (K s) s'" "\<Delta> s' < \<Delta> s"
          by (auto simp: pmf_nonneg intro: M2 M3 pmf_positive)

        have "\<Delta> s \<le> ((\<integral>t. l2 t \<partial>K s) + c s) - ((\<integral>t. l1 t \<partial>K s) + c s)"
          unfolding \<Delta>_def using `s \<in> S` `s \<notin> N` by (intro diff_mono l1 l2) auto
        then have "\<Delta> s \<le> (\<integral>s'. \<Delta> s' \<partial>K s)"
          using `s \<in> S` by (simp add: \<Delta>_def)
        also have "\<dots> < (\<integral>s'. \<Delta> s \<partial>K s)"
          using `s' \<in> K s` `\<Delta> s' < \<Delta> s` `s\<in>S` S `s\<in>M`
          by (intro measure_pmf.integral_less_AE[where A="{s'}"])
             (auto simp: emeasure_measure_pmf_finite AE_measure_pmf_iff set_pmf_iff[symmetric] intro!: M2)
        finally show False
          using measure_pmf.prob_space[of "K s"] by simp
      qed
      with step.IH `t\<in>N` N have "\<Delta> s' \<le> 0" "s' \<in> M"
        by auto
      with `s\<in>S` show "\<Delta> s \<le> 0"
        by (force simp: M_def)
    qed (insert N `t\<in>N`, auto) }

  show ?thesis
  proof cases
    assume "M \<inter> N = {}"
    have "Max (\<Delta>`(S\<union>N)) \<in> \<Delta>`(S\<union>N)"
      using `s \<in> S` by (intro Max_in finitary) auto
    then obtain t where "t \<in> S \<union> N" "\<Delta> t = Max (\<Delta>`(S\<union>N))"
      unfolding image_iff by metis
    then have "t \<in> M"
      by (auto simp: M_def finitary intro!: Max_ge)
    have "\<Delta> s \<le> \<Delta> t"
      using `t\<in>M` `s\<in>S` by (auto dest: M2)
    also have "\<Delta> t \<le> 0"
      using `t\<in>M` `M \<inter> N = {}` by fact
    finally show ?thesis
      by (simp add: \<Delta>_def)
  next
    assume "M \<inter> N \<noteq> {}"
    then obtain t where "t \<in> M" "t \<in> N" by auto
    with N `s\<in>S` have "\<Delta> s \<le> 0"
      by (intro order_trans[of "\<Delta> s" "\<Delta> t" 0]) (auto simp: M_def)
    then show ?thesis
      by (simp add: \<Delta>_def)
  qed
qed

lemma unique_les:
  fixes s S N and l1 l2 :: "'a \<Rightarrow> real" and K :: "'a \<Rightarrow> 'a pmf"
  defines "\<Delta> x \<equiv> l2 x - l1 x"
  assumes s: "s \<in> S" and S: "(\<Union>s\<in>S. K s) \<subseteq> S \<union> N"
  assumes "\<And>s. s \<in> S \<Longrightarrow> integrable (K s) l1"
  assumes "\<And>s. s \<in> S \<Longrightarrow> integrable (K s) l2"
  assumes "\<And>s. s \<in> S \<Longrightarrow> \<exists>t\<in>N. (s, t) \<in> (SIGMA s:UNIV. K s)\<^sup>*"
  assumes "\<And>s. s \<in> S \<Longrightarrow> l1 s = (\<integral>t. l1 t \<partial>K s) + c s"
  assumes "\<And>s. s \<in> S \<Longrightarrow> l2 s = (\<integral>t. l2 t \<partial>K s) + c s"
  assumes "\<And>s. s \<in> N \<Longrightarrow> l2 s = l1 s"
  assumes 1: "finite (\<Delta> ` (S\<union>N))"
  shows "l2 s = l1 s"
proof -
  have "finite ((\<lambda>x. l2 x - l1 x) ` (S\<union>N))"
    using 1 by (auto simp: \<Delta>_def[abs_def])
  moreover then have "finite (uminus ` (\<lambda>x. l2 x - l1 x) ` (S\<union>N))"
    by auto
  ultimately show ?thesis
    using assms
    by (intro antisym mono_les[of s S K N l2 l1 c] mono_les[of s S K N l1 l2 c])
       (auto simp: image_comp comp_def)
qed

text {*

Markov chain with discrete time steps and discrete state space.

*}

locale MC_syntax =
  fixes K :: "'s \<Rightarrow> 's pmf"
begin

abbreviation accessible :: "('s \<times> 's) set" where
  "accessible \<equiv> (SIGMA s:UNIV. K s)\<^sup>*"

lemma countable_reachable: "countable ((SIGMA s:UNIV. set_pmf (K s))\<^sup>* `` {s})"
  by (auto intro!: countable_rtrancl countable_set_pmf simp: Sigma_Image)

lemma countable_accessible: "countable X \<Longrightarrow> countable (accessible `` X)"
  apply (rule countable_Image)
  apply (rule countable_reachable)
  apply assumption
  done

coinductive enabled where
  "enabled (shd \<omega>) (stl \<omega>) \<Longrightarrow> shd \<omega> \<in> K s \<Longrightarrow> enabled s \<omega>"

lemma alw_enabled: "enabled (shd \<omega>) (stl \<omega>) \<Longrightarrow> alw (\<lambda>\<omega>. enabled (shd \<omega>) (stl \<omega>)) \<omega>"
  by (coinduction arbitrary: \<omega> rule: alw_coinduct) (auto elim: enabled.cases)

abbreviation "S \<equiv> stream_space (count_space UNIV)"

lemma in_S [measurable (raw)]: "x \<in> space S"
  by (simp add: space_stream_space)

inductive_simps enabled_iff: "enabled s \<omega>"

lemma measurable_enabled[measurable]:
  "Measurable.pred (stream_space (count_space UNIV)) (enabled s)" (is "Measurable.pred ?S _")
  unfolding enabled_def
proof (coinduction arbitrary: s rule: measurable_gfp2_coinduct)
  case (step A s)
  then have [measurable]: "\<And>t. Measurable.pred ?S (A t)" by auto
  have *: "\<And>x. (\<exists>\<omega> t. s = t \<and> x = \<omega> \<and> A (shd \<omega>) (stl \<omega>) \<and> shd \<omega> \<in> set_pmf (K t)) \<longleftrightarrow>
    (\<exists>t\<in>K s. A t (stl x) \<and> t = shd x)"
    by auto
  note countable_set_pmf[simp]
  show ?case
    unfolding * by measurable
qed (auto simp: down_continuous_def)

lemma enabled_iff_snth: "enabled s \<omega> \<longleftrightarrow> (\<forall>i. \<omega> !! i \<in> K ((s ## \<omega>) !! i))"
proof safe
  fix i assume "enabled s \<omega>" then show "\<omega> !! i \<in> K ((s ## \<omega>) !! i)"
    by (induct i arbitrary: s \<omega>)
       (force elim: enabled.cases)+
next
  assume "\<forall>i. \<omega> !! i \<in> set_pmf (K ((s ## \<omega>) !! i))" then show "enabled s \<omega>"
    by (coinduction arbitrary: s \<omega>)
       (auto elim: allE[of _ "Suc i" for i] allE[of _ 0])
qed

primcorec force_enabled where
  "force_enabled x \<omega> =
    (let y = if shd \<omega> \<in> K x then shd \<omega> else (SOME y. y \<in> K x) in y ## force_enabled y (stl \<omega>))"

lemma force_enabled_in_set_pmf[simp, intro]: "shd (force_enabled x \<omega>) \<in> K x"
  by (auto simp: some_in_eq set_pmf_not_empty)

lemma enabled_force_enabled: "enabled x (force_enabled x \<omega>)"
  by (coinduction arbitrary: x \<omega>) (auto simp: some_in_eq set_pmf_not_empty)
  
lemma force_enabled: "enabled x \<omega> \<Longrightarrow> force_enabled x \<omega> = \<omega>"
  by (coinduction arbitrary: x \<omega>) (auto elim: enabled.cases)

lemma Ex_enabled: "\<exists>\<omega>. enabled x \<omega>"
  by (rule exI[of _ "force_enabled x undefined"] enabled_force_enabled)+

lemma measurable_force_enabled: "force_enabled x \<in> measurable S S"
proof (rule measurable_stream_space2)
  fix n show "(\<lambda>\<omega>. force_enabled x \<omega> !! n) \<in> measurable S (count_space UNIV)"
  proof (induction n arbitrary: x)
    case (Suc n) show ?case
      apply simp
      apply (rule measurable_compose_countable'[OF measurable_compose[OF measurable_stl Suc], where I="set_pmf (K x)"])
      apply (rule measurable_compose[OF measurable_shd])
      apply (auto simp: countable_set_pmf some_in_eq set_pmf_not_empty)
      done
  qed (auto intro!: measurable_compose[OF measurable_shd])
qed

abbreviation "D \<equiv> stream_space (\<Pi>\<^sub>M s\<in>UNIV. K s)"

lemma sets_D: "sets D = sets (stream_space (\<Pi>\<^sub>M s\<in>UNIV. count_space UNIV))"
  by (intro sets_stream_space_cong sets_PiM_cong) simp_all

lemma space_D: "space D = space (stream_space (\<Pi>\<^sub>M s\<in>UNIV. count_space UNIV))"
  using sets_eq_imp_space_eq[OF sets_D] .
  
lemma measurable_D_D: "measurable D D = 
    measurable (stream_space (\<Pi>\<^sub>M s\<in>UNIV. count_space UNIV)) (stream_space (\<Pi>\<^sub>M s\<in>UNIV. count_space UNIV))"
  by (simp add: measurable_def space_D sets_D)

primcorec walk :: "'s \<Rightarrow> ('s \<Rightarrow> 's) stream \<Rightarrow> 's stream" where
  "shd (walk s \<omega>) = (if shd \<omega> s \<in> K s then shd \<omega> s else (SOME t. t \<in> K s))"
| "stl (walk s \<omega>) = walk (if shd \<omega> s \<in> K s then shd \<omega> s else (SOME t. t \<in> K s)) (stl \<omega>)"

lemma enabled_walk: "enabled s (walk s \<omega>)"
  by (coinduction arbitrary: s \<omega>) (auto simp: some_in_eq set_pmf_not_empty)

lemma measurable_walk[measurable]: "walk s \<in> measurable D S"
proof -
  note measurable_compose[OF measurable_snth, intro!]
  note measurable_compose[OF measurable_component_singleton, intro!]
  note if_cong[cong del]
  note measurable_g = measurable_compose_countable'[OF _ _ countable_reachable]

  def n \<equiv> "0::nat"
  def g \<equiv> "\<lambda>_::('s \<Rightarrow> 's) stream. s"
  then have "g \<in> measurable D (count_space ((SIGMA s:UNIV. K s)\<^sup>* `` {s}))"
    by auto
  then have "(\<lambda>x. walk (g x) (sdrop n x)) \<in> measurable D S"
  proof (coinduction arbitrary: g n rule: measurable_stream_coinduct)
    case (shd f') show ?case
      by (fastforce intro: measurable_g[OF _ shd])
  next
    case (stl f') show ?case
      by (fastforce simp add: sdrop.simps[symmetric] some_in_eq set_pmf_not_empty
                    simp del: sdrop.simps intro: rtrancl_into_rtrancl measurable_g[OF _ stl])
  qed
  then show ?thesis
    by (simp add: g_def n_def)
qed

definition T :: "'s \<Rightarrow> 's stream measure" where
  "T s = distr (stream_space (\<Pi>\<^sub>M s\<in>UNIV. K s)) S (walk s)"

lemma space_T[simp]: "space (T s) = space S"
  by (simp add: T_def)

lemma sets_T[simp, measurable_cong]: "sets (T s) = sets S"
  by (simp add: T_def)

lemma measurable_T1[simp]: "measurable (T s) M = measurable S M"
  by (intro measurable_cong_sets) simp_all

lemma measurable_T2[simp]: "measurable M (T s) = measurable M S"
  by (intro measurable_cong_sets) simp_all

lemma in_measurable_T1[measurable (raw)]: "f \<in> measurable S M \<Longrightarrow> f \<in> measurable (T s) M"
  by simp

lemma in_measurable_T2[measurable (raw)]: "f \<in> measurable M S \<Longrightarrow> f \<in> measurable M (T s)"
  by simp

lemma AE_T_enabled: "AE \<omega> in T s. enabled s \<omega>"
  unfolding T_def by (simp add: AE_distr_iff enabled_walk)

sublocale T!: prob_space "T s" for s
proof -
  interpret P: product_prob_space K UNIV
    by default
  interpret prob_space "stream_space (\<Pi>\<^sub>M s\<in>UNIV. K s)"
    by (rule P.prob_space_stream_space)
  fix s show "prob_space (T s)"
    by (simp add: T_def prob_space_distr)
qed

lemma nn_integral_T:
  assumes f[measurable]: "f \<in> borel_measurable S"
  shows "(\<integral>\<^sup>+X. f X \<partial>T s) = (\<integral>\<^sup>+t. (\<integral>\<^sup>+\<omega>. f (t ## \<omega>) \<partial>T t) \<partial>K s)"
proof -
  interpret product_prob_space K UNIV
    by default
  interpret D: prob_space "stream_space (\<Pi>\<^sub>M s\<in>UNIV. K s)"
    by (rule prob_space_stream_space)

  have T: "\<And>f s. f \<in> borel_measurable S \<Longrightarrow> (\<integral>\<^sup>+X. f X \<partial>T s) = (\<integral>\<^sup>+\<omega>. f (walk s \<omega>) \<partial>D)"
    by (simp add: T_def nn_integral_distr)

  have "(\<integral>\<^sup>+X. f X \<partial>T s) = (\<integral>\<^sup>+\<omega>. f (walk s \<omega>) \<partial>D)"
    by (rule T) measurable
  also have "\<dots> = (\<integral>\<^sup>+d. \<integral>\<^sup>+\<omega>. f (walk s (d ## \<omega>)) \<partial>D \<partial>\<Pi>\<^sub>M i\<in>UNIV. K i)"
    by (simp add: P.nn_integral_stream_space)
  also have "\<dots> = (\<integral>\<^sup>+d. (\<integral>\<^sup>+\<omega>. f (d s ## walk (d s) \<omega>) * indicator {t. t \<in> K s} (d s) \<partial>D) \<partial>\<Pi>\<^sub>M i\<in>UNIV. K i)"
    apply (rule nn_integral_cong_AE)
    apply (subst walk.ctr)
    apply (simp cong del: if_cong)
    apply (intro UNIV_I AE_component)
    apply (auto simp: AE_measure_pmf_iff)
    done
  also have "\<dots> = (\<integral>\<^sup>+d. \<integral>\<^sup>+\<omega>. f (d s ## \<omega>) * indicator {t. t \<in> K s} (d s) \<partial>T (d s) \<partial>\<Pi>\<^sub>M i\<in>UNIV. K i)"
    by (subst T) (simp_all split: split_indicator)
  also have "\<dots> = (\<integral>\<^sup>+t. \<integral>\<^sup>+\<omega>. f (t ## \<omega>) * indicator {t. t \<in> K s} t \<partial>T t \<partial>K s)"
    by (subst (2) PiM_component[symmetric]) (simp_all add: nn_integral_distr)
  also have "\<dots> = (\<integral>\<^sup>+t. \<integral>\<^sup>+\<omega>. f (t ## \<omega>) \<partial>T t \<partial>K s)"
    by (rule nn_integral_cong_AE) (simp add: AE_measure_pmf_iff)
  finally show ?thesis .
qed

lemma emeasure_Collect_T:
  assumes f[measurable]: "Measurable.pred S P"
  shows "emeasure (T s) {x\<in>space (T s). P x} = (\<integral>\<^sup>+t. emeasure (T t) {x\<in>space (T t). P (t ## x)} \<partial>K s)"
  apply (subst (1 2) nn_integral_indicator[symmetric])
  apply simp
  apply simp
  apply (subst nn_integral_T)
  apply (auto intro!: nn_integral_cong simp add: space_stream_space indicator_def)
  done

lemma AE_T_iff:
  assumes [measurable]: "Measurable.pred S P"
  shows "(AE \<omega> in T x. P \<omega>) \<longleftrightarrow> (\<forall>y\<in>K x. AE \<omega> in T y. P (y ## \<omega>))"
  by (simp add: AE_iff_nn_integral nn_integral_T[where s=x])
     (auto simp add: nn_integral_0_iff_AE AE_measure_pmf_iff split: split_indicator)

lemma emeasure_suntil:
  assumes [measurable]: "Measurable.pred S P" "Measurable.pred S Q"
  shows "emeasure (T s) {x\<in>space (T s). (P suntil Q) x} =
   (SUP i. emeasure (T s) {x\<in>space (T s). ((\<lambda>R. Q or (P aand nxt R))^^i) (\<lambda>_. False) x})"
proof -
  have suntil_eq: "(P suntil Q) = lfp (\<lambda>R. Q or (P aand nxt R))"
    unfolding suntil_def by (auto intro!: arg_cong[where f=lfp])
  show ?thesis
    unfolding suntil_eq
  proof (coinduction arbitrary: s rule: emeasure_lfp)
    case measurable
    have [measurable]: "Measurable.pred S A"
      using measurable[of "T s"] by auto
    show ?case
      by simp
  qed (auto simp: Order_Continuity.continuous_def)
qed

lemma emeasure_ev:
  assumes [measurable]: "Measurable.pred S P"
  shows "emeasure (T s) {x\<in>space (T s). ev P x} =
   (SUP i. emeasure (T s) {x\<in>space (T s). ((\<lambda>R. P or nxt R)^^i) (\<lambda>_. False) x})"
proof -
  have ev_eq: "ev P = lfp (\<lambda>R. P or nxt R)"
    unfolding ev_def by (auto intro!: arg_cong[where f=lfp])
  show ?thesis
    unfolding ev_eq
  proof (coinduction arbitrary: s rule: emeasure_lfp)
    case measurable
    have [measurable]: "Measurable.pred S A"
      using measurable[of "T s"] by auto
    show ?case
      by simp
  qed (auto simp: Order_Continuity.continuous_def)
qed

lemma emeasure_suntil_HLD:
  assumes [measurable]: "Measurable.pred S P"
  shows "emeasure (T s) {x\<in>space (T s). (not (HLD {t}) suntil (HLD {t} aand nxt P)) x} =
   emeasure (T s) {x\<in>space (T s). ev (HLD {t}) x} * emeasure (T t) {x\<in>space (T t). P x}"
proof -
  let ?t = "HLD {t}"
  let ?M = "\<lambda>s P. emeasure (T s) {x\<in>space (T s). P x}"
  let ?F = "\<lambda>i. ((\<lambda>Q. (?t aand nxt P) or (not ?t aand nxt Q))^^i) (\<lambda>_. False)"
  let ?E = "\<lambda>i. ((\<lambda>Q. ?t or nxt Q)^^i) (\<lambda>_. False)"

  have "?M s ((not ?t) suntil (?t aand nxt P)) = (SUP i. ?M s (?F i))"
    by (rule emeasure_suntil) measurable
  also have "\<dots> = (SUP i. ?M s (?E i) * ?M t P)"
  proof (intro SUP_cong refl)
    fix i :: nat show "?M s (?F i) = ?M s (?E i) * ?M t P"
    proof (induct i arbitrary: s)
      case (Suc i)
      have "?M s (?F (Suc i)) = (\<integral>\<^sup>+t. ?M t (\<lambda>\<omega>. ?F (Suc i) (t ## \<omega>)) \<partial>K s)"
        by (intro emeasure_Collect_T measurable_predpow) auto
      also have "\<dots> = (\<integral>\<^sup>+t'. (if t' = t then ?M t P else ?M t' (?F i)) \<partial>K s)"
        by (intro nn_integral_cong) (auto simp: HLD_iff)
      also have "\<dots> = (\<integral>\<^sup>+t'. ?M t' (\<lambda>\<omega>. ?E (Suc i) (t' ## \<omega>)) * ?M t P \<partial>K s)"
        using T.emeasure_space_1 unfolding Suc by (intro nn_integral_cong) (auto simp: HLD_iff)
      also have "\<dots> = (\<integral>\<^sup>+t'. ?M t' (\<lambda>\<omega>. ?E (Suc i) (t' ## \<omega>)) \<partial>K s) * ?M t P"
        by (rule nn_integral_multc) auto
      also have "(\<integral>\<^sup>+t'. ?M t' (\<lambda>\<omega>. ?E (Suc i) (t' ## \<omega>)) \<partial>K s) = ?M s (?E (Suc i))"
        by (intro emeasure_Collect_T[symmetric] measurable_predpow) auto
      finally show ?case .
    qed simp
  qed
  also have "\<dots> = (SUP i. ?M s (?E i)) * ?M t P"
    by (subst (1 2) mult.commute) (auto intro!: SUP_ereal_mult_left)
  also have [symmetric]: "?M s (ev ?t) = (SUP i. ?M s (?E i))"
    by (rule emeasure_ev) measurable
  finally show ?thesis .
qed

lemma mult_eq_1:
  fixes a b :: "'a :: {ordered_semiring, comm_monoid_mult}"
  shows "0 \<le> a \<Longrightarrow> a \<le> 1 \<Longrightarrow> b \<le> 1 \<Longrightarrow> a * b = 1 \<longleftrightarrow> (a = 1 \<and> b = 1)"
  by (metis mult.left_neutral eq_iff mult.commute mult_right_mono)

lemma AE_suntil: 
  assumes [measurable]: "Measurable.pred S P"
  shows "(AE x in T s. (not (HLD {t}) suntil (HLD {t} aand nxt P)) x) \<longleftrightarrow>
   (AE x in T s. ev (HLD {t}) x) \<and> (AE x in T t. P x)"
  apply (subst (1 2 3) T.prob_Collect_eq_1[symmetric])
  apply simp
  apply simp
  apply simp
  apply (simp_all add: measure_def emeasure_suntil_HLD del: space_T nxt.simps)
  apply (auto simp: T.emeasure_eq_measure mult_eq_1 measure_nonneg)
  done

definition fair :: "'s \<Rightarrow> 's \<Rightarrow> 's stream \<Rightarrow> bool" where
  "fair s t = alw (ev (HLD {s})) impl alw (ev (HLD {s} aand nxt (HLD {t})))"

lemma AE_T_alw:
  assumes [measurable]: "Measurable.pred S P"
  assumes P: "\<And>x. AE \<omega> in T x. P \<omega>"
  shows "AE \<omega> in T x. alw P \<omega>"
proof -
  { fix i have "almost_everywhere (T x) (((\<lambda>p x. P x \<and> p (stl x)) ^^ i) top)"
      apply (induct i arbitrary: x)
      apply simp
      apply (subst AE_T_iff)
      unfolding top_fun_def
      apply measurable
      apply simp
      apply simp
      apply (subst AE_T_iff[symmetric])
      apply simp
      apply (rule P)
      done }
  then have "almost_everywhere (T x) (gfp (\<lambda>p x. P x \<and> p (stl x)))"
    by (subst down_continuous_gfp) (auto simp: down_continuous_def AE_all_countable)
  then show ?thesis
    by (simp add: alw_def)
qed

lemma AE_T_fair:
  assumes "t' \<in> K t"
  shows "AE \<omega> in T s. fair t t' \<omega>"
proof -
  def never \<equiv> "alw (ev (HLD {t})) aand alw (not (HLD {t} aand nxt (HLD {t'})))"
  have never_stl: "\<And>\<omega>. never \<omega> \<Longrightarrow> never (stl \<omega>)"
    by (auto simp: never_def)
  have [measurable]: "Measurable.pred S never"
    unfolding never_def by measurable

  def c \<equiv> "measure (K t) {t'}"
  have c_le_1[arith]: "c \<le> 1"
    unfolding c_def by (rule measure_pmf.prob_le_1)
  have "0 < c"
    unfolding c_def
    using emeasure_pmf_single_eq_zero_iff[of "K t" t'] `t' \<in> K t`
    by (simp add: measure_pmf.emeasure_eq_measure measure_nonneg less_le)

  let ?M = "\<lambda>s P. emeasure (T s) {\<omega>\<in>space (T s). P \<omega>}"
  { fix x k have "?M x (\<lambda>\<omega>. never \<omega>) \<le> (1 - c)^k"
    proof (induct k arbitrary: x)
      case 0 then show ?case
        by (simp add: T.measure_le_1 one_ereal_def[symmetric])
    next
      case (Suc k)
      let ?C = "ereal ((1 - c)^k)"
      let ?until = "not (HLD {t}) suntil (HLD {t} aand nxt (not (HLD {t'}) aand never))"
      { fix \<omega> assume "never \<omega>"
        then have "ev (HLD {t}) \<omega>" "never \<omega>"
          by (auto simp: never_def)
        then have "?until \<omega>"
        proof (induct rule: ev_induct_strong)
          case (base \<omega>) then show ?case
            by (intro suntil.base) (auto simp: never_def)
        next
          case (step \<omega>) then show ?case
            by (intro suntil.step[of _ \<omega>]) (auto simp: never_stl)
        qed }
      then have "?M x (\<lambda>\<omega>. never \<omega>) \<le> ?M x (\<lambda>\<omega>. ?until \<omega>)"
        apply (intro emeasure_mono_AE)
        defer
        apply measurable []
        apply (rule UNIV_I)
        apply measurable
        done
      also have "\<dots> = ?M x (\<lambda>\<omega>. ev (HLD {t}) \<omega>) * ?M t (\<lambda>\<omega>. (not (HLD {t'}) aand never) \<omega>)"
        by (intro emeasure_suntil_HLD) simp
      also have "\<dots> = ?M x (\<lambda>\<omega>. ev (HLD {t}) \<omega>) * (\<integral>\<^sup>+y. ?M y (\<lambda>\<omega>. y \<noteq> t' \<and> never (y ## \<omega>)) \<partial>K t)"
        by (subst (2) emeasure_Collect_T) (simp_all add: HLD_iff)
      also have "\<dots> \<le> ?M x (\<lambda>\<omega>. ev (HLD {t}) \<omega>) * (\<integral>\<^sup>+y. ?M y (\<lambda>\<omega>. y \<noteq> t' \<and> never \<omega>) \<partial>K t)"
        by (intro ereal_mult_left_mono emeasure_nonneg nn_integral_mono emeasure_mono_AE)
           (auto dest: never_stl[of "x ## s" for x s, simplified])
      also have "\<dots> = ?M x (\<lambda>\<omega>. ev (HLD {t}) \<omega>) * (\<integral>\<^sup>+y. indicator (- {t'}) y * ?M y never \<partial>K t)"
        by (subst (2 4) emeasure_Collect_T)
           (auto intro!: ereal_left_mult_cong nn_integral_cong split: split_indicator)
      also have "\<dots> \<le> ?M x (\<lambda>\<omega>. ev (HLD {t}) \<omega>) * (\<integral>\<^sup>+y. indicator (- {t'}) y * ?C \<partial>K t)"
        by (intro ereal_mult_left_mono emeasure_nonneg nn_integral_mono Suc ereal_indicator_nonneg)
      also have "\<dots> = ?M x (\<lambda>\<omega>. ev (HLD {t}) \<omega>) * (emeasure (K t) (space (K t) - {t'}) * ?C)"
        by (subst nn_integral_multc) (auto intro!: zero_le_power simp: Compl_eq_Diff_UNIV)
      also have "\<dots> \<le> 1 * (emeasure (K t) (space (K t) - {t'}) * ?C)"
        by (intro ereal_mult_right_mono T.measure_le_1) (auto intro!: ereal_0_le_mult)
      also have "emeasure (K t) (space (K t) - {t'}) = 1 - emeasure (K t) {t'}"
        using measure_pmf.emeasure_space_1[of "K t"] by (subst emeasure_compl) auto
      also have "1 * ((1 - emeasure (K t) {t'}) * ?C) \<le> 1 * (ereal (1 - c) * ?C)"
        unfolding c_def
        by (intro ereal_mult_right_mono ereal_mult_left_mono)
           (auto simp: measure_pmf.emeasure_eq_measure one_ereal_def field_simps intro!: zero_le_power)
      finally show ?case
        by simp
    qed }
  then have "\<And>x. emeasure (T x) {\<omega> \<in> space (T x). never \<omega>} \<le> 0"
  proof (intro tendsto_le_const[OF sequentially_bot])
    show "(\<lambda>k. ereal ((1 - c) ^ k)) ----> 0"
      unfolding zero_ereal_def by (auto intro!: LIMSEQ_realpow_zero `0 < c`)
  qed auto
  then have "\<And>x. AE \<omega> in T x. \<not> never \<omega>"
    by (intro AE_I[OF order_refl] antisym emeasure_nonneg) auto
  then have "AE \<omega> in T s. alw (not never) \<omega>"
    by (intro AE_T_alw) auto
  moreover
  { fix \<omega> assume "alw (ev (HLD {t})) \<omega>"
    then have "alw (alw (ev (HLD {t}))) \<omega>"
      unfolding alw_alw .
    moreover assume "alw (not never) \<omega>"
    then have "alw (alw (ev (HLD {t})) impl ev (HLD {t} aand nxt (HLD {t'}))) \<omega>"
      unfolding never_def not_alw_iff not_ev_iff de_Morgan_disj de_Morgan_conj not_not imp_conv_disj .
    ultimately have "alw (ev (HLD {t} aand nxt (HLD {t'}))) \<omega>"
      by (rule alw_mp) }
  then have "\<forall>\<omega>. alw (not never) \<omega> \<longrightarrow> fair t t' \<omega>"
    by (auto simp: fair_def)
  ultimately show ?thesis
    by (rule eventually_rev_mono)
qed

lemma enabled_imp_trancl:
  assumes "alw (HLD B) \<omega>" "enabled s \<omega>"
  shows "alw (HLD ((SIGMA s:UNIV. K s \<inter> B)\<^sup>* `` {s})) \<omega>"
proof -
  def t \<equiv> s
  then have "(s, t) \<in> (SIGMA s:UNIV. set_pmf (K s) \<inter> B)\<^sup>*"
    by auto
  moreover note `alw (HLD B) \<omega>`
  moreover note `enabled s \<omega>`[unfolded `t == s`[symmetric]]
  ultimately show ?thesis
  proof (coinduction arbitrary: t \<omega> rule: alw_coinduct)
    case stl from this(1,2,3) show ?case
      by (auto simp: enabled.simps[of _ \<omega>] alw.simps[of _ \<omega>] HLD_iff
                 intro!: exI[of _ "shd \<omega>"] rtrancl_trans[of s t])
  next
    case (alw t \<omega>) then show ?case
     by (auto simp: HLD_iff enabled.simps[of _ \<omega>] alw.simps[of _ \<omega>] intro!: rtrancl_trans[of s t])
  qed
qed
  

lemma AE_T_reachable: "AE \<omega> in T s. alw (HLD ((SIGMA s:UNIV. K s)\<^sup>* `` {s})) \<omega>"
  using AE_T_enabled
proof eventually_elim
  fix \<omega> assume "enabled s \<omega>"
  from enabled_imp_trancl[of UNIV, OF _ this]
  show "alw (HLD ((SIGMA s:UNIV. K s)\<^sup>* `` {s})) \<omega>"
    by (auto simp: HLD_iff[abs_def] all_imp_alw)
qed

lemma AE_T_all_fair: "AE \<omega> in T s. \<forall>(t,t')\<in>SIGMA t:UNIV. K t. fair t t' \<omega>"
proof -
  let ?R = "SIGMA t:UNIV. K t" let ?Rn = "SIGMA s:(?R\<^sup>* `` {s}). K s"
  have "AE \<omega> in T s. \<forall>(t,t')\<in>?Rn. fair t t' \<omega>"
  proof (subst AE_ball_countable)
    show "countable ?Rn"
      by (intro countable_SIGMA countable_rtrancl[OF countable_Image])
         (auto simp: Image_def countable_set_pmf)
  qed (auto intro!: AE_T_fair)
  then show ?thesis
    using AE_T_reachable
  proof (eventually_elim, safe)
    fix \<omega> t t' assume "\<forall>(t,t')\<in>?Rn. fair t t' \<omega>" "t' \<in> K t" and alw: "alw (HLD (?R\<^sup>* `` {s})) \<omega>"
    moreover
    { assume "t \<notin> ?R\<^sup>* `` {s}"
      then have "alw (not (HLD {t})) \<omega>"
        by (intro alw_mono[OF alw]) (auto simp: HLD_iff)
      then have "not (alw (ev (HLD {t}))) \<omega>"
        unfolding not_alw_iff not_ev_iff by auto
      then have "fair t t' \<omega>"
        unfolding fair_def by auto }
    ultimately show "fair t t' \<omega>"
      by auto
  qed
qed

lemma pigeonhole_stream:
  assumes "alw (HLD s) \<omega>"
  assumes "finite s"
  shows "\<exists>x\<in>s. alw (ev (HLD {x})) \<omega>"
proof -
  have "\<forall>i\<in>UNIV. \<exists>x\<in>s. \<omega> !! i = x"
    using `alw (HLD s) \<omega>` by (simp add: alw_iff_sdrop HLD_iff)
  from pigeonhole_infinite_rel[OF infinite_UNIV_nat `finite s` this]
  show ?thesis
    by (simp add: HLD_iff infinite_iff_alw_ev[symmetric])
qed

lemma fair_imp: assumes "fair t t' \<omega>" "alw (ev (HLD {t})) \<omega>" shows "alw (ev (HLD {t'})) \<omega>"
proof -
  { fix \<omega> assume "ev (HLD {t} aand nxt (HLD {t'})) \<omega>" then have "ev (HLD {t'}) \<omega>"
      by induction auto }
  with assms show ?thesis
    by (auto simp: fair_def elim!: alw_mp intro: all_imp_alw)
qed

lemma AE_T_ev_HLD:
  assumes exiting: "\<And>t. (s, t) \<in> (SIGMA s:UNIV. set_pmf (K s) - B)\<^sup>* \<Longrightarrow>
    \<exists>t'\<in>B. (t, t') \<in> (SIGMA s:UNIV. K s)\<^sup>*"
  assumes fin: "finite ((SIGMA s:UNIV. set_pmf (K s) - B)\<^sup>* `` {s})"
  shows "AE \<omega> in T s. ev (HLD B) \<omega>"
  using AE_T_all_fair AE_T_enabled
proof eventually_elim
  fix \<omega> assume fair: "\<forall>(t, t')\<in>(SIGMA s:UNIV. K s). fair t t' \<omega>" and "enabled s \<omega>"

  show "ev (HLD B) \<omega>"
  proof (rule ccontr)
    assume "\<not> ev (HLD B) \<omega>"
    then have "alw (HLD (- B)) \<omega>"
      by (simp add: not_ev_iff HLD_iff[abs_def])
    from enabled_imp_trancl[OF this `enabled s \<omega>`]
    have "alw (HLD ((SIGMA x:UNIV. set_pmf (K x) - B)\<^sup>* `` {s})) \<omega>"
      by (simp add: Diff_eq)
    from pigeonhole_stream[OF this fin]
    obtain t where "(s, t) \<in> (SIGMA s:UNIV. set_pmf (K s) - B)\<^sup>*" "alw (ev (HLD {t})) \<omega>"
      by auto
    from exiting[OF this(1)] obtain t' where "(t, t') \<in> (SIGMA x:UNIV. set_pmf (K x))\<^sup>*" "t' \<in> B"
      by auto
    from this(1) have "alw (ev (HLD {t'})) \<omega>"
    proof induction
      case (step u w) then show ?case
        using fair fair_imp[of u w \<omega>] by auto
    qed fact
    { assume "ev (HLD {t'}) \<omega>" then have "ev (HLD B) \<omega>"
      by (rule ev_mono) (auto simp: HLD_iff `t' \<in> B`) }
    then show False
      using `alw (ev (HLD {t'})) \<omega>` `\<not> ev (HLD B) \<omega>` by auto
  qed
qed

lemma nn_integral_enat_function:
  assumes f: "f \<in> measurable M (count_space UNIV)"
  shows "(\<integral>\<^sup>+ x. ereal_of_enat (f x) \<partial>M) = (\<Sum>t. emeasure M {x \<in> space M. t < f x})"
proof -
  def F \<equiv> "\<lambda>i::nat. {x\<in>space M. i < f x}"
  with assms have [measurable]: "\<And>i. F i \<in> sets M"
    by auto

  { fix x assume "x \<in> space M"
    have "(\<lambda>i::nat. if i < f x then 1 else 0) sums ereal_of_enat (f x)"
      using sums_If_finite[of "\<lambda>r. r < f x" "\<lambda>_. 1 :: ereal"]
      apply (cases "f x")
      apply (simp add: one_ereal_def real_of_nat_def[symmetric]) []
      apply (simp add: sums_def tendsto_PInfty_eq_at_top real_of_nat_def[symmetric]
                       filterlim_real_sequentially one_ereal_def)
      done
    also have "(\<lambda>i. (if i < f x then 1 else 0)) = (\<lambda>i. indicator (F i) x)"
      using `x \<in> space M` by (simp add: one_ereal_def F_def fun_eq_iff)
    finally have "ereal_of_enat (f x) = (\<Sum>i. indicator (F i) x)"
      by (simp add: sums_iff) }
  then have "(\<integral>\<^sup>+x. ereal_of_enat (f x) \<partial>M) = (\<integral>\<^sup>+x. (\<Sum>i. indicator (F i) x) \<partial>M)"
    by (simp cong: nn_integral_cong)
  also have "\<dots> = (\<Sum>i. emeasure M (F i))"
    by (simp add: nn_integral_suminf)
  finally show ?thesis
    by (simp add: F_def)
qed

lemma AE_T_max_sfirst:
  assumes [measurable]: "Measurable.pred S X"
  assumes AE: "AE \<omega> in T c. sfirst X (c ## \<omega>) < \<infinity>" and "0 < e"
  shows "\<exists>N::nat. \<P>(\<omega> in T c. N < sfirst X (c ## \<omega>)) < e" (is "\<exists>N. ?P N < e")
proof -
  have "?P ----> measure (T c) (\<Inter>N::nat. {bT \<in> space (T c). N < sfirst X (c ## bT)})"
    using dual_order.strict_trans enat_ord_simps(2)
    by (intro T.finite_Lim_measure_decseq) (force simp: decseq_Suc_iff simp del: enat_ord_simps)+
  also have "measure (T c) (\<Inter>N::nat. {bT \<in> space (T c). N < sfirst X (c ## bT)}) =
      \<P>(bT in T c. sfirst X (c ## bT) = \<infinity>)"
    by (auto simp del: not_infinity_eq intro!: arg_cong[where f="measure (T c)"])
       (metis less_irrefl not_infinity_eq)
  also have "\<P>(bT in T c. sfirst X (c ## bT) = \<infinity>) = 0"
    using AE by (intro T.prob_eq_0_AE) auto
  finally have "\<exists>N. \<forall>n\<ge>N. norm (?P n - 0) < e"
    using `0 < e` by (rule LIMSEQ_D)
  then show ?thesis
    by (auto simp: measure_nonneg)
qed

lemma nn_integral_sfirst_finite:
  assumes [simp]: "finite ((SIGMA x:- H. set_pmf (K x) - H)\<^sup>* `` {s})" (is "finite (?R `` {s})")
  assumes until: "AE \<omega> in T s. ev (HLD H) \<omega>"
  shows "(\<integral>\<^sup>+ \<omega>. sfirst (HLD H) (s ## \<omega>) \<partial>T s) \<noteq> \<infinity>"
proof cases
  assume "s \<in> H" then show ?thesis
    by (simp add: sfirst.simps)
next
  assume "s \<notin> H"
  then have [simp]: "?R `` {s} \<noteq> {}"
    by auto

  def X \<equiv> "\<lambda>n. ((\<lambda>Q. not (HLD H) aand nxt Q) ^^ n) \<top>"
  then have X_simps: "X 0 = \<top>" "\<And>n. X (Suc n) = not (HLD H) aand nxt (X n)"
    by simp_all

  have [measurable]: "\<And>n. Measurable.pred S (X n)"
    unfolding X_def
  proof (intro measurable_predpow)
    fix n and Q :: "'s stream \<Rightarrow> bool" assume [measurable]: "Measurable.pred S Q"
    show "Measurable.pred S (\<lambda>xs. \<not> HLD H xs \<and> nxt Q xs)"
      by measurable
  qed (simp add: top_fun_def)

  { fix t assume "(s, t) \<in> ?R"
    then have "AE \<omega> in T t. ev (HLD H) (t ## \<omega>)"
    proof induction
      case (step t u) with step.IH show ?case
        by (subst (asm) AE_T_iff)
           (auto simp add: ev_Stream holds_Stream simp del: holds.simps elim!: ballE[of _ _ u])
    qed (simp add: ev_Stream holds_Stream `s \<notin> H` del: holds.simps, fact)
    moreover
    assume "\<forall>n. AE \<omega> in T t. X n (t ## \<omega>)"
    then have "AE \<omega> in T t. alw (not (HLD H)) (t ## \<omega>)"
      unfolding alw_def X_def
      by (subst down_continuous_gfp) (auto simp: down_continuous_def AE_all_countable top_fun_def)
    ultimately have "AE \<omega> in T t. False"
      by eventually_elim (simp add: not_ev_iff[symmetric] del: holds.simps)
    then have False
      by auto }
  then have "\<forall>t\<in>?R `` {s}. \<exists>n. \<not> (AE \<omega> in T t. X n (t ## \<omega>))"
    by blast
  then obtain N where N: "\<And>t. (s, t) \<in> ?R \<Longrightarrow> \<not> (AE \<omega> in T t. X (N t) (t ## \<omega>))"
    unfolding bchoice_iff by auto

  def n \<equiv> "Max (N ` ?R `` {s})"
  { fix t and m :: nat assume t: "(s, t) \<in> ?R"
    then have "N t \<le> n"
      by (simp add: n_def)
    then have "X n \<le> X (N t)"
      unfolding X_def by (intro funpow_increasing) (auto simp: mono_def)
    with N[OF t] have "\<not> (AE \<omega> in T t. X n (t ## \<omega>))"
      by (auto intro: eventually_mono simp add: le_fun_def top_fun_def) }
  note n = this
  have "\<not> N s = 0"
      using N[of s] by (intro notI) (auto simp: X_simps)
  then have "1 \<le> n"
    unfolding n_def by (subst Max_ge_iff) (auto intro!: bexI[of _ s])

  def d \<equiv> "Max ((\<lambda>t. \<P>(\<omega> in T t. X n (t ## \<omega>))) ` ?R `` {s})"
  have d: "\<And>t. t \<in> ?R `` {s} \<Longrightarrow> \<P>(\<omega> in T t. X n (t ## \<omega>)) \<le> d"
    by (simp add: d_def)
  have [arith]: "0 \<le> d"
    using d[of s] by (auto intro: measure_nonneg order_trans)
  have "d < 1"
    unfolding d_def
    apply (subst Max_less_iff)
    apply (auto simp add: less_le dest!: n simp del: space_T)
    apply (subst (asm) T.prob_Collect_eq_1)
    apply simp_all
    done

  let ?M = "\<lambda>s P. emeasure (T s) {\<omega>\<in>space (T s). P \<omega>}"

  have "(\<integral>\<^sup>+ \<omega>. sfirst (HLD H) (s ## \<omega>) \<partial>T s) = (\<Sum>i. ?M s (\<lambda>\<omega>. i < sfirst (HLD H)(s ## \<omega>)))"
    by (intro nn_integral_enat_function) simp
  also have "\<dots> \<le> (\<Sum>i. ereal (d^(i div n)))"
  proof (intro suminf_le_pos emeasure_nonneg)
    fix N
    def i \<equiv> "N div n"
    def t \<equiv> "s"
    then have "(s, t) \<in> ?R"
      by simp
    have "\<And>\<omega>. enat N < sfirst (HLD H)(s ## \<omega>) \<Longrightarrow> enat (i * n) < sfirst (HLD H)(s ## \<omega>)"
      by (metis le_add1 mod_div_equality i_def enat_ord_code(1) le_less_trans)
    then have "?M s (\<lambda>\<omega>. enat N < sfirst (HLD H)(s ## \<omega>)) \<le> ?M t (\<lambda>\<omega>. enat (i * n) < sfirst (HLD H)(t ## \<omega>))"
      unfolding t_def by (intro emeasure_mono Collect_mono) (auto simp: i_def)
    also have "\<dots> \<le> ereal (d ^ i)"
      using `(s, t) \<in> ?R`
    proof (induction i arbitrary: t)
      case 0 then show ?case
        using T.emeasure_space_1
        by (cases "t \<in> H") (simp_all add: sfirst_Stream zero_enat_def[symmetric])
    next
      case (Suc i)
      def j \<equiv> "i * n"
      have [simp, arith]: "0 \<le> d ^ i"
        by (auto simp add: field_simps intro!: ereal_0_le_mult zero_le_power)
        
      { fix \<omega> have "enat (n + j) < sfirst (HLD H)\<omega> \<longleftrightarrow> X n \<omega> \<and> enat j < sfirst (HLD H)(sdrop n \<omega>)"
        proof (induct n arbitrary: \<omega>)
          case (Suc n) then show ?case
            by (cases \<omega>) (simp add: sfirst_Stream eSuc_enat[symmetric] X_simps)
        qed (simp add: X_simps) }
      then have "?M t (\<lambda>\<omega>. enat (Suc i * n) < sfirst (HLD H)(t ## \<omega>))
        = ?M t (\<lambda>\<omega>. X n (t ## \<omega>) \<and> enat j < sfirst (HLD H)(sdrop n (t ## \<omega>)))"
        by (simp add: j_def)
      also have "\<dots> \<le> ?M t (\<lambda>\<omega>. X n (t ## \<omega>)) * ereal (d ^ i)"
        using Suc.prems
      proof (induction n arbitrary: t)
        case (0 t) then show ?case
          using Suc.IH[of t] T.emeasure_space_1 `d < 1`
          by (auto simp add: X_simps sfirst_Stream j_def)
      next
        case (Suc n s)
        show ?case
        proof cases
          assume "s \<notin> H"
          then have "?M s (\<lambda>\<omega>. X (Suc n) (s ## \<omega>) \<and> enat j < sfirst (HLD H)(sdrop (Suc n) (s ## \<omega>)))
            = (\<integral>\<^sup>+t. ?M t (\<lambda>\<omega>. X n (t ## \<omega>) \<and> enat j < sfirst (HLD H)(sdrop n (t ## \<omega>))) \<partial>K s)"
            by (subst emeasure_Collect_T) (auto simp add: X_simps)
          also have "\<dots> \<le> (\<integral>\<^sup>+t. ?M t (\<lambda>\<omega>. X n (t ## \<omega>)) * ereal (d ^ i) \<partial>K s)"
            using `d < 1` `s \<notin> H`
            apply (intro nn_integral_mono_AE)
            apply (auto simp add: X_simps sfirst_Stream emeasure_nonneg AE_measure_pmf_iff)
            apply (case_tac "y \<in> H")
            apply (cases n)
            apply (auto simp add: X_simps sfirst_Stream intro!: ereal_0_le_mult) []
            apply (simp add: X_simps)
            apply (cut_tac t=y in Suc.IH[OF rtrancl_into_rtrancl[OF Suc.prems]])
            apply simp
            apply simp
            done
          also have "\<dots> = (\<integral>\<^sup>+t. ?M t (\<lambda>\<omega>. X n (t ## \<omega>)) \<partial>K s) * d ^ i"
            by (intro nn_integral_multc) auto
          also have "\<dots> = ?M s (\<lambda>\<omega>. X (Suc n) (s ## \<omega>)) * d ^ i"
            using `s \<notin>  H` by (subst (2) emeasure_Collect_T) (simp_all add: X_simps)
          finally show ?case .
        qed (simp add: X_simps)
      qed
      also have "\<dots> \<le> ereal d * d^i"
        using Suc.prems
        by (intro ereal_mult_right_mono)
           (simp_all add: T.emeasure_eq_measure d del: space_T)
      finally show ?case
        by simp
    qed
    finally show "emeasure (T s) {\<omega> \<in> space (T s). enat N < sfirst (HLD H)(s ## \<omega>)} \<le> ereal (d ^ i)" .
  qed
  also have "\<dots> < \<infinity>"
  proof cases
    assume "d = 0"
    with `1 \<le> n` have "summable (\<lambda>i. d ^ (i div n))"
      by (auto simp add: power_0_left div_eq_0_iff)
    then show "(\<Sum>i. ereal (d ^ (i div n))) < \<infinity>"
      by (auto simp: suminf_ereal_finite)
  next
    assume "d \<noteq> 0"
    from `d < 1` `1 \<le> n` have "root n d < 1"
      by (subst real_root_lt_1_iff) simp
    with summable_geometric[of "root n d"] `0 \<le> d`
    have "summable (\<lambda>i. root n d ^ i / d)"
      by (simp add: real_root_ge_zero summable_divide)
    then have "summable (\<lambda>i. d ^ (i div n))"
    proof (rule summable_comparison_test[rotated], intro exI allI impI)
      fix i
      have "i \<le> i div n * n + n"  
        using `1 \<le> n`
        by (subst mod_div_equality[symmetric, of i n]) (intro add_mono, auto)
      then have "(d ^ (i div n) * d) ^ Suc (n - 1) \<le> (root n d ^ n) ^ i"
        using `1 \<le> n` `0 \<le> d` `d < 1` mod_div_equality[of i n]
        by (auto simp add: power_Suc2[symmetric] power_mult[symmetric] simp del: power_Suc
                 intro!: power_decreasing)
      also have "\<dots> = (root n d ^ i) ^ (Suc (n - 1))"
        using `1 \<le> n` unfolding power_mult[symmetric] by (simp add: ac_simps)
      finally have "(d ^ (i div n) * d) \<le> root n d ^ i"
        by (rule power_le_imp_le_base) (insert `0 \<le> d` `1 \<le> n`, simp)
      then show "norm (d ^ (i div n)) \<le> (root n d ^ i / d)"
        using `0 \<le> d` `d \<noteq> 0` by (simp_all add: divide_simps)
    qed
    then show "(\<Sum>i. ereal (d ^ (i div n))) < \<infinity>"
      by (auto simp: suminf_ereal_finite)
  qed
  finally show ?thesis
    by simp
qed

lemma emeasure_HLD_nxt:
  assumes [measurable]: "Measurable.pred S P"
  shows "emeasure (T s) {\<omega>\<in>space (T s). (X \<cdot> P) \<omega>} =
    (\<integral>\<^sup>+x. emeasure (T x) {\<omega>\<in>space (T x). P \<omega>} * indicator X x \<partial>K s)"
  by (subst emeasure_Collect_T)
     (auto intro!: nn_integral_cong_AE simp: AE_measure_pmf_iff split: split_indicator)

lemma emeasure_HLD:
  "emeasure (T s) {\<omega>\<in>space (T s). HLD X \<omega>} = emeasure (K s) X"
  using emeasure_HLD_nxt[of "\<lambda>\<omega>. True" s X] T.emeasure_space_1 by simp

lemma emeasure_suntil_sums:
  assumes [measurable]: "Measurable.pred S \<phi>"
  assumes [measurable]: "Measurable.pred S \<psi>"
  shows "emeasure (T s) {\<omega>\<in>space (T s). (\<phi> suntil \<psi>) \<omega>} =
    (\<Sum>i. emeasure (T s) {\<omega>\<in>space (T s). ((\<lambda>R. \<phi> aand ((not \<psi>) aand (nxt R))) ^^ i) \<psi> \<omega>})"
proof -
  let ?R = "\<lambda>i \<omega>. ((\<lambda>R. \<psi> or (\<phi> aand (nxt R))) ^^ i) \<bottom> \<omega>"
  let ?L = "\<lambda>j \<omega>. ((\<lambda>R. \<phi> aand ((not \<psi>) aand (nxt R))) ^^ j) \<psi> \<omega>"
  { fix \<omega> i assume "?R i \<omega>" then have "\<exists>j<i. ?L j \<omega>"
    proof (induction i arbitrary: \<omega>)
      case (Suc i) then show ?case
        by (cases "\<not> \<psi> \<omega>") force+
    qed simp }
  moreover
  { fix \<omega> i j assume "?L j \<omega>" then have "?R (Suc j) \<omega>"
      by (induction j arbitrary: \<omega>) auto
    moreover assume "j < i"
    then have "?R (Suc j) \<le> ?R i"
      by (intro funpow_decreasing) (auto simp: mono_def)
    ultimately have "?R i \<omega>"
      by (auto simp: le_fun_def) }
  ultimately have R_eq_L: "\<And>i \<omega>. ?R i \<omega> \<longleftrightarrow> (\<exists>j<i. ?L j \<omega>)"
    by blast

  { fix m n \<omega> assume "?L m \<omega>" "?L n \<omega>"
    then have "m = n"
    proof (induction m arbitrary: \<omega> n)
      case 0 then show ?case
        by (cases n) auto
    next
      case (Suc m) then show ?case
        by (cases n) auto
    qed }
  note inj = this

  have "emeasure (T s) {\<omega>\<in>space (T s). (\<phi> suntil \<psi>) \<omega>} =
    (SUP i. emeasure (T s) {\<omega>\<in>space (T s). ?R i \<omega>})"
    unfolding bot_fun_def bot_bool_def by (intro emeasure_suntil) fact+
  also have "\<dots> = (SUP i. emeasure (T s) (\<Union>j<i. {\<omega>\<in>space (T s). ?L j \<omega>}))"
    unfolding R_eq_L by (auto intro!: SUP_cong arg_cong2[where f=emeasure])
  also have "\<dots> = (SUP i. \<Sum>j<i. emeasure (T s) {\<omega>\<in>space (T s). ?L j \<omega>})"
    apply (intro SUP_cong[OF refl] setsum_emeasure[symmetric] image_subset_iff[THEN iffD2] ballI)
    apply measurable
    apply (auto simp: disjoint_family_on_def inj)
    done
  also have "\<dots> = (\<Sum>i. emeasure (T s) {\<omega>\<in>space (T s). ?L i \<omega>})"
    by (intro suminf_ereal_eq_SUP[symmetric] emeasure_nonneg)
  finally show ?thesis .
qed

lemma emeasure_suntil_geometric:
  assumes [measurable]: "Measurable.pred S \<phi>"
  assumes [measurable]: "Measurable.pred S \<psi>"
  assumes "s \<in> X" and Y: "\<And>s. s \<in> X \<Longrightarrow> Y s \<subseteq> X" and "p < 1"
  assumes \<psi>: "\<And>s. s \<in> X \<Longrightarrow> emeasure (T s) {\<omega>\<in>space (T s). \<psi> \<omega>} = ereal r"
  assumes \<phi>: "\<And>s. s \<in> X \<Longrightarrow> AE \<omega> in T s. (((\<phi> aand not \<psi>) aand nxt \<psi>) \<omega> \<longleftrightarrow> (Y s \<cdot> \<psi>) \<omega>)"
   "\<And>s. s \<in> X \<Longrightarrow> AE \<omega> in T s. (((\<phi> aand not \<psi>) aand nxt (\<phi> aand not \<psi>)) \<omega> \<longleftrightarrow> (Y s \<cdot> (\<phi> aand not \<psi>)) \<omega>)"
  assumes p: "\<And>s. s \<in> X \<Longrightarrow> emeasure (K s) (Y s) = ereal p"
  shows "emeasure (T s) {\<omega>\<in>space (T s). (\<phi> suntil \<psi>) \<omega>} = r / (1 - p)"
proof -
  let ?P = "\<lambda>x P. emeasure (T x) {\<omega>\<in>space (T x). P \<omega>}"
  have nn: "0 \<le> r" "0 \<le> p"
    using p[OF `s \<in> X`, symmetric] \<psi>[OF `s \<in> X`, symmetric]
    by (auto simp: T.emeasure_eq_measure measure_pmf.emeasure_eq_measure measure_nonneg)

  let ?I = "\<lambda>n. ((\<lambda>R. \<phi> aand ((not \<psi>) aand nxt R)) ^^ n) \<psi>"
  { fix n
    from `s \<in> X` have "?P s (?I n) = p^n * r"
    proof (induction n arbitrary: s)
      case (Suc n)
      have "?P s (?I (Suc n)) = ?P s (Y s \<cdot> ?I n)"
      proof (intro emeasure_Collect_eq_AE)
        show "AE \<omega> in T s. ?I (Suc n) \<omega> \<longleftrightarrow> (Y s \<cdot> ?I n) \<omega>"
          using \<phi>[OF `s\<in>X`]
        proof eventually_elim
          fix \<omega> assume "((\<phi> aand not \<psi>) aand nxt \<psi>) \<omega> \<longleftrightarrow> (Y s \<cdot> \<psi>) \<omega>"
            "((\<phi> aand not \<psi>) aand nxt (\<phi> aand not \<psi>)) \<omega> \<longleftrightarrow> (Y s \<cdot> (\<phi> aand not \<psi>)) \<omega>"
          then show "?I (Suc n) \<omega> \<longleftrightarrow> (Y s \<cdot> ?I n) \<omega>"
            by (cases n) auto
        qed
        show "Measurable.pred (T s) (?I (Suc n))"
          by measurable simp
        show "Measurable.pred (T s) (Y s \<cdot> ?I n)"
          unfolding measurable_T1 by measurable
      qed
      also have "\<dots> = (\<integral>\<^sup>+y. ?P y (?I n) * indicator (Y s) y \<partial>K (s))"
        by (intro emeasure_HLD_nxt) measurable
      also have "\<dots> = (\<integral>\<^sup>+y. ereal (p^n * r) * indicator (Y s) y \<partial>K s)"
        using Suc Y by (intro nn_integral_cong) (auto split: split_indicator)
      also have "\<dots> = ereal (p^Suc n * r)"
        using nn Suc by (subst nn_integral_cmult_indicator) (auto simp: p)
      finally show ?case
        by simp
    qed (insert \<psi>, simp) }
  note iter = this

  have "?P s (\<phi> suntil \<psi>) = (\<Sum>n. ?P s (?I n))"
    by (subst emeasure_suntil_sums) measurable
  also have "\<dots> = (\<Sum>n. ereal (p^n * r))"
    by (subst iter) rule
  also have "\<dots> = ereal ((1 / (1 - p)) * r)"
    using `p < 1` nn by (intro sums_suminf_ereal sums_mult2 geometric_sums) auto
  finally show ?thesis
    by simp
qed

lemma emeasure_ev_sums:
  assumes [measurable]: "Measurable.pred S \<phi>"
  shows "emeasure (T s) {\<omega>\<in>space (T s). ev \<phi> \<omega>} =
    (\<Sum>i. emeasure (T s) {\<omega>\<in>space (T s). ((\<lambda>R. (not \<phi>) aand (nxt R)) ^^ i) \<phi> \<omega>})"
  using emeasure_suntil_sums[of "\<lambda>s. True" \<phi> s] by (simp add: true_suntil)

lemma prob_T:
  assumes P: "Measurable.pred S P"
  shows "\<P>(\<omega> in T s. P \<omega>) = (\<integral>t. \<P>(\<omega> in T t. P (t ## \<omega>)) \<partial>K s)"
  using emeasure_Collect_T[OF P, of s] unfolding T.emeasure_eq_measure
  by (subst (asm) nn_integral_eq_integral)
     (auto intro!: measure_pmf.integrable_const_bound[where B=1] simp: measure_nonneg)

lemma T_subprob: "T \<in> measurable (measure_pmf I) (subprob_algebra S)"
  by (auto intro!: space_bind simp: space_subprob_algebra) unfold_locales

subsection {* Markov chain with initial distribution @{term_type "I::'s pmf"}: *}

definition T' :: "'s pmf \<Rightarrow> 's stream measure" where
  "T' I = bind I (\<lambda>s. distr (T s) S (op ## s))"

lemma distr_Stream_subprob:
  "(\<lambda>s. distr (T s) S (op ## s)) \<in> measurable (measure_pmf I) (subprob_algebra S)"
  apply (intro measurable_distr2[OF _ T_subprob])
  apply (subst measurable_cong_sets[where M'="count_space UNIV \<Otimes>\<^sub>M S" and N'=S])
  apply (rule sets_pair_measure_cong)
  apply auto
  done

lemma sets_T': "sets (T' I) = sets S"
  by (simp add: T'_def)

lemma prob_space_T': "prob_space (T' I)"
  unfolding T'_def
proof (rule measure_pmf.prob_space_bind)
  show "AE s in I. prob_space (distr (T s) S (op ## s))"
    by (intro AE_measure_pmf_iff[THEN iffD2] ballI T.prob_space_distr) simp
qed (rule distr_Stream_subprob)

lemma AE_T':
  assumes [measurable]: "Measurable.pred S P"
  shows "(AE x in T' I. P x) \<longleftrightarrow> (\<forall>s\<in>I. AE x in T s. P (s ## x))"
  unfolding T'_def by (simp add: AE_bind[OF _ distr_Stream_subprob] AE_measure_pmf_iff AE_distr_iff)

lemma emeasure_T':
  assumes [measurable]: "X \<in> sets S"
  shows "emeasure (T' I) X = (\<integral>\<^sup>+s. emeasure (T s) {\<omega>\<in>space S. s ## \<omega> \<in> X} \<partial>I)"
  unfolding T'_def
  by (simp add: emeasure_bind[OF _ distr_Stream_subprob] emeasure_distr vimage_def Int_def conj_ac)

lemma prob_T':
  assumes [measurable]: "Measurable.pred S P"
  shows "\<P>(x in T' I. P x) = (\<integral>s. \<P>(x in T s. P (s ## x)) \<partial>I)"
proof -
  interpret T': prob_space "T' I" by (rule prob_space_T')
  show ?thesis
    using emeasure_T'[of "{x\<in>space (T' I). P x}" I]
    unfolding T'.emeasure_eq_measure T.emeasure_eq_measure sets_eq_imp_space_eq[OF sets_T']
    apply simp
    apply (subst (asm) nn_integral_eq_integral)
    apply (auto intro!: measure_pmf.integrable_const_bound[where B=1] integral_cong arg_cong2[where f=measure]
                simp: AE_measure_pmf measure_nonneg space_stream_space)
    done
qed

lemma T_eq_T': "T s = T' (K s)"
proof (rule measure_eqI)
  fix X assume X: "X \<in> sets (T s)"
  then have [measurable]: "X \<in> sets S"
    by simp
  have X_eq: "X = {x\<in>space (T s). x \<in> X}"
    using sets.sets_into_space[OF X] by auto
  show "emeasure (T s) X = emeasure (T' (K s)) X"
    apply (subst X_eq)
    apply (subst emeasure_Collect_T, simp)
    apply (subst emeasure_T', simp)
    apply simp
    done
qed (simp add: sets_T')

lemma T_eq_bind: "T s = (measure_pmf (K s) \<guillemotright>= (\<lambda>t. distr (T t) S (op ## t)))"
  by (subst T_eq_T') (simp add: T'_def)

declare T_subprob[measurable]

lemma T_split:
  "T s = (T s \<guillemotright>= (\<lambda>\<omega>. distr (T ((s ## \<omega>) !! n)) S (\<lambda>\<omega>'. stake n \<omega> @- \<omega>')))"
proof (induction n arbitrary: s)
  case 0 then show ?case
    apply (simp add: distr_cong[OF refl sets_T[symmetric, of s] refl])
    apply (subst bind_const')
    apply unfold_locales
    ..
next
  case (Suc n)
  let ?K = "measure_pmf (K s)" and ?m = "\<lambda>n \<omega> \<omega>'. stake n \<omega> @- \<omega>'"
  note sets_stream_space_cong[simp, measurable_cong]

  have "T s = (?K \<guillemotright>= (\<lambda>t. distr (T t) S (op ## t)))"
    by (rule T_eq_bind)
  also have "\<dots> = (?K \<guillemotright>= (\<lambda>t. distr (T t \<guillemotright>= (\<lambda>\<omega>. distr (T ((t ## \<omega>) !! n)) S (?m n \<omega>))) S (op ## t)))"
    unfolding Suc[symmetric] ..
  also have "\<dots> = (?K \<guillemotright>= (\<lambda>t. T t \<guillemotright>= (\<lambda>\<omega>. distr (distr (T ((t ## \<omega>) !! n)) S (?m n \<omega>)) S (op ## t))))"
    by (simp add: distr_bind[where K=S, OF measurable_distr2[where M=S]] space_stream_space)
  also have "\<dots> = (?K \<guillemotright>= (\<lambda>t. T t \<guillemotright>= (\<lambda>\<omega>. distr (T ((t ## \<omega>) !! n)) S (?m (Suc n) (t ## \<omega>)))))"
    by (simp add: distr_distr space_stream_space comp_def)
  also have "\<dots> = (?K \<guillemotright>= (\<lambda>t. distr (T t) S (op ## t) \<guillemotright>= (\<lambda>\<omega>. distr (T (\<omega> !! n)) S (?m (Suc n) \<omega>))))"
    by (simp add: space_stream_space bind_distr[OF _ measurable_distr2[where M=S]] del: stake.simps)
  also have "\<dots> = (T s \<guillemotright>= (\<lambda>\<omega>. distr (T (\<omega> !! n)) S (?m (Suc n) \<omega>)))"
    unfolding T_eq_bind[of s]
    by (subst bind_assoc[OF measurable_distr2[where M=S] measurable_distr2[where M=S], OF _ T_subprob])
       (simp_all add: space_stream_space del: stake.simps)
  finally show ?case
    by simp
qed

lemma nn_integral_T_split:
  assumes f[measurable]: "f \<in> borel_measurable S"
  shows "(\<integral>\<^sup>+\<omega>. f \<omega> \<partial>T s) = (\<integral>\<^sup>+\<omega>. (\<integral>\<^sup>+\<omega>'. f (stake n \<omega> @- \<omega>') \<partial>T ((s ## \<omega>) !! n)) \<partial>T s)"
  apply (subst T_split[of s n])
  apply (simp add: nn_integral_bind[OF f measurable_distr2[where M=S]])
  apply (subst nn_integral_distr)
  apply (simp_all add: space_stream_space)
  done

lemma emeasure_T_split:
  assumes P[measurable]: "Measurable.pred S P"
  shows "emeasure (T s) {\<omega>\<in>space (T s). P \<omega>} =
      (\<integral>\<^sup>+\<omega>. emeasure (T ((s ## \<omega>) !! n)) {\<omega>'\<in>space (T ((s ## \<omega>) !! n)). P (stake n \<omega> @- \<omega>')} \<partial>T s)"
  apply (subst T_split[of s n])
  apply (subst emeasure_bind[OF _ measurable_distr2[where M=S]])
  apply (simp_all add: )
  apply (simp add: space_stream_space)
  apply (subst emeasure_distr)
  apply simp_all
  apply (simp_all add: space_stream_space)
  done

lemma prob_T_split:
  assumes P[measurable]: "Measurable.pred S P"
  shows "\<P>(\<omega> in T s. P \<omega>) = (\<integral>\<omega>. \<P>(\<omega>' in T ((s ## \<omega>) !! n). P (stake n \<omega> @- \<omega>')) \<partial>T s)"
  unfolding T.emeasure_eq_measure[symmetric] ereal.inject[symmetric] emeasure_T_split[OF P, of s n]
  by (auto intro!: nn_integral_eq_integral T.integrable_const_bound[where B=1]
                   measure_measurable_subprob_algebra2[where N=S]
           simp: measure_nonneg T.emeasure_eq_measure SIGMA_Collect_eq)

lemma enabled_imp_alw:
  "(\<Union>s\<in>X. K s) \<subseteq> X \<Longrightarrow> x \<in> X \<Longrightarrow> enabled x \<omega> \<Longrightarrow> alw (HLD X) \<omega>"
proof (coinduction arbitrary: \<omega> x)
  case alw then show ?case
    unfolding enabled.simps[of _ \<omega>]
    by (auto simp: HLD_iff)
qed

lemma alw_HLD_iff_sconst:
  "alw (HLD {x}) \<omega> \<longleftrightarrow> \<omega> = sconst x"
proof
  assume "alw (HLD {x}) \<omega>" then show "\<omega> = sconst x"
    by (coinduction arbitrary: \<omega>) (auto simp: HLD_iff)
qed (auto simp: alw_sconst HLD_iff)

lemma enabled_iff_sconst:
  assumes [simp]: "set_pmf (K x) = {x}" shows "enabled x \<omega> \<longleftrightarrow> \<omega> = sconst x"
proof
  assume "enabled x \<omega>" then show "\<omega> = sconst x"
    by (coinduction arbitrary: \<omega>) (auto elim: enabled.cases)
next
  assume "\<omega> = sconst x" then show "enabled x \<omega>"
    by (coinduction arbitrary: \<omega>) auto
qed

lemma AE_sconst:
  assumes [simp]: "set_pmf (K x) = {x}"
  shows "(AE \<omega> in T x. P \<omega>) \<longleftrightarrow> P (sconst x)"
proof -
  have "(AE \<omega> in T x. P \<omega>) \<longleftrightarrow> (AE \<omega> in T x. P \<omega> \<and> \<omega> = sconst x)"
    using AE_T_enabled[of x] by (simp add: enabled_iff_sconst)
  also have "\<dots> = (AE \<omega> in T x. P (sconst x) \<and> \<omega> = sconst x)"
    by (simp del: AE_conj_iff cong: rev_conj_cong)
  also have "\<dots> = (AE \<omega> in T x. P (sconst x))"
    using AE_T_enabled[of x] by (simp add: enabled_iff_sconst)
  finally show ?thesis
    by simp
qed

subsection {* Trace space with restriction *}

definition "rT x = restrict_space (T x) {\<omega>. enabled x \<omega>}"

lemma space_rT: "\<omega> \<in> space (rT x) \<longleftrightarrow> enabled x \<omega>"
  by (auto simp: rT_def space_restrict_space space_stream_space)

lemma Collect_enabled_S[measurable]: "Collect (enabled x) \<in> sets S"
proof -
  have "Collect (enabled x) = {\<omega>\<in>space S. enabled x \<omega>}"
    by (auto simp: space_stream_space)
  then show ?thesis
    by simp
qed
   
lemma space_rT_in_S: "space (rT x) \<in> sets S"
  by (simp add: rT_def space_restrict_space)

lemma sets_rT: "A \<in> sets (rT x) \<longleftrightarrow> A \<in> sets S \<and> A \<subseteq> {\<omega>. enabled x \<omega>}"
  by (auto simp: rT_def sets_restrict_space space_stream_space)

lemma prob_space_rT: "prob_space (rT x)"
  unfolding rT_def by (auto intro!: prob_space_restrict_space T.emeasure_eq_1_AE AE_T_enabled)

lemma measurable_force_enabled2[measurable]: "force_enabled x \<in> measurable S (rT x)"
  unfolding rT_def 
  by (rule measurable_restrict_space2)
     (auto intro: measurable_force_enabled enabled_force_enabled)

lemma space_rT_not_empty[simp]: "space (rT x) \<noteq> {}"
  by (simp add: rT_def space_restrict_space Ex_enabled)

lemma T_eq_bind': "T x = do { y <- measure_pmf (K x) ; \<omega> <- T y ; return S (y ## \<omega>) }"
  apply (subst T_eq_bind)
  apply (subst bind_return_distr[symmetric])
  apply (simp_all add: space_stream_space comp_def)
  done

lemma rT_eq_bind: "rT x = do { y <- measure_pmf (K x) ; \<omega> <- rT y ; return (rT x) (y ## \<omega>) }"
  unfolding rT_def
  apply (subst T_eq_bind)
  apply (subst restrict_space_bind[where K=S])
  apply (rule measurable_distr2[where M=S])
  apply (auto simp del: measurable_pmf_measure1
              simp add: Ex_enabled return_restrict_space intro!: bind_cong )
  apply (subst restrict_space_bind[symmetric, where K=S])
  apply (auto simp add: Ex_enabled space_restrict_space return_cong[OF sets_T]
              intro!:  measurable_restrict_space1 measurable_compose[OF _ return_measurable]
              arg_cong2[where f=restrict_space])
  apply (subst bind_return_distr[unfolded comp_def])
  apply (simp add: space_restrict_space Ex_enabled)
  apply (simp add: measurable_restrict_space1)
  apply (rule measure_eqI)
  apply simp
  apply (subst (1 2) emeasure_distr)
  apply (auto simp: measurable_restrict_space1)
  apply (subst emeasure_restrict_space)
  apply (auto simp: space_restrict_space intro!: emeasure_eq_AE)
  using AE_T_enabled
  apply eventually_elim
  apply (simp add: space_stream_space)
  apply (rule sets_Int_pred)
  apply auto
  apply (simp add: space_stream_space)
  done

lemma snth_rT: "(\<lambda>x. x !! n) \<in> measurable (rT x) (count_space (accessible `` {x}))"
proof -
  have "\<And>\<omega>. enabled x \<omega> \<Longrightarrow> (x, \<omega> !! n) \<in> accessible"
  proof (induction n arbitrary: x)
    case (Suc n) from Suc.prems Suc.IH[of "shd \<omega>" "stl \<omega>"] show ?case
      by (auto simp: enabled.simps[of x \<omega>] intro: rtrancl_trans)
  qed (auto elim: enabled.cases)
  moreover
  { fix X :: "'s set"
    have [measurable]: "X \<in> count_space UNIV" by simp
    have *: "(\<lambda>x. x !! n) -` X \<inter> space (rT x) =  {\<omega>\<in>space S. \<omega> !! n \<in> X \<and> enabled x \<omega>}"
      by (auto simp: space_stream_space space_rT)
    have "(\<lambda>x. x !! n) -` X \<inter> space (rT x) \<in> sets S"
      unfolding * by measurable }
  ultimately show ?thesis
    by (auto simp: measurable_def space_rT sets_rT)
qed

lemma T_bisim:
  assumes "\<And>x. prob_space (M x)"
  assumes sets_M [simp, measurable_cong]: "\<And>x. sets (M x) = sets S"
  assumes M_eq: "\<And>x. M x = (measure_pmf (K x) \<guillemotright>= (\<lambda>s. distr (M s) S (op ## s)))"
  shows "T = M"
proof (intro ext stream_space_eq_sstart)
  interpret M: prob_space "M x" for x by fact
  have *:
    "\<And>x. (\<lambda>s. distr (M s) (stream_space (count_space UNIV)) (op ## s)) \<in> measurable (measure_pmf (K x)) (subprob_algebra S)"
    apply (intro measurable_distr2[where M=S])
    apply (auto simp: measurable_split_conv space_subprob_algebra
                intro!: measurable_Stream measurable_compose[OF measurable_fst])
    apply unfold_locales
    done

  fix x
  show "prob_space (T x)" "prob_space (M x)" by unfold_locales
  show "sets (M x) = sets S" "sets (T x) = sets S" by auto
  def \<Omega> \<equiv> "accessible `` {x}"

  have [simp]: "\<And>x. space (M x) = space S"
    using sets_M by (rule sets_eq_imp_space_eq)

  { fix xs have "sstart \<Omega> xs \<in> sets S"
    proof (induction xs)
      case (Cons x xs)
      note this[measurable]
      have "sstart \<Omega> (x # xs) = {\<omega>\<in>space S. \<omega> \<in> sstart \<Omega> (x # xs)}" by (auto simp: space_stream_space)
      also have "\<dots> \<in> sets S"
        unfolding in_sstart by measurable
      finally show ?case .
    qed (auto intro!: streams_sets) }
  note sstart_in_S = this [measurable] 

  show "countable \<Omega>"
    by (auto intro: countable_accessible simp: \<Omega>_def)
  have x[simp]: "x \<in> \<Omega>"
    by (auto simp: \<Omega>_def)

  note streams_sets[measurable]

  { fix n y assume "y \<in> \<Omega>"
    then have "(x, y) \<in> accessible" by (simp add: \<Omega>_def)
    then have "AE \<omega> in T y. \<omega> \<in> streams \<Omega>"
    proof induction
      case (step y z) then show ?case
        by (subst (asm) AE_T_iff) (auto simp: streams_Stream)
    qed (insert AE_T_reachable, simp add: alw_HLD_iff_streams \<Omega>_def) }
  note AE_T = this[simp]
  then show "AE xa in T x. xa \<in> streams \<Omega>"
    by simp

  { fix n x assume "x \<in> \<Omega>" then have "AE \<omega> in M x. \<omega> !! n \<in> \<Omega>"
    proof (induction n arbitrary: x)
      case 0 then show ?case
        apply (subst M_eq)
        apply (subst AE_bind[OF _ *])
        apply (force intro!: measurable_compose[OF measurable_shd] AE_distr_iff[THEN iffD2] predE
                    intro: rtrancl_into_rtrancl
                    simp: AE_measure_pmf_iff AE_distr_iff \<Omega>_def)+
        done
    next
      case (Suc n) then show ?case
        apply (subst M_eq)
        apply (subst AE_bind[OF _ *])
        apply (auto intro!: measurable_compose[OF measurable_snth]
                            measurable_compose[OF measurable_stl] AE_distr_iff[THEN iffD2] predE
                    intro: rtrancl_into_rtrancl
                    simp: AE_measure_pmf_iff AE_distr_iff \<Omega>_def)+
        done
    qed }
  then have AE_M: "\<And>x. x \<in> \<Omega> \<Longrightarrow> AE xa in M x. xa \<in> streams \<Omega>"
    by (auto simp: streams_iff_snth AE_all_countable)
  then show "AE xa in M x. xa \<in> streams \<Omega>" by simp

  have \<Omega>_trans: "\<And>x y. x \<in> \<Omega> \<Longrightarrow> y \<in> K x \<Longrightarrow> y \<in> \<Omega>"
    by (auto simp: \<Omega>_def intro: rtrancl_trans)

  fix xs
  from `x \<in> \<Omega>` show "emeasure (T x) (sstart \<Omega> xs) = emeasure (M x) (sstart \<Omega> xs)"
  proof (induction xs arbitrary: x)
    case Nil with AE_M[of x] AE_T[of x] show ?case
      by (cases "streams (accessible `` {x}) \<in> sets S")
         (simp_all add: T.emeasure_eq_1_AE M.emeasure_eq_1_AE emeasure_notin_sets)
  next
    case (Cons a xs)
    then have "emeasure (T x) {\<omega>\<in>space (T x). \<omega> \<in> sstart \<Omega> (a # xs)} =
      (\<integral>\<^sup>+y. emeasure (M y) (sstart \<Omega> xs) * indicator {a} y \<partial>K x)"
      by (subst emeasure_Collect_T)
         (auto intro!: nn_integral_cong_AE
               simp: space_stream_space AE_measure_pmf_iff \<Omega>_trans split: split_indicator
               simp del: nn_integral_indicator_singleton)
    also have "\<dots> = emeasure (M x) {\<omega>\<in>space (M x). \<omega> \<in> sstart \<Omega> (a # xs)}"
      apply (subst M_eq[of x])
      apply (auto intro!: nn_integral_cong arg_cong2[where f=emeasure]
                  simp add: emeasure_bind[OF _ *] emeasure_distr split: split_indicator
               simp del: nn_integral_indicator_singleton)
      apply (auto simp: space_stream_space)
      done
    finally show ?case
      by (simp add: space_stream_space del: in_sstart)
  qed
qed

lemma T_subprob'[measurable]: "T \<in> measurable (count_space UNIV) (subprob_algebra S)"
  by (auto intro!: space_bind simp: space_subprob_algebra) unfold_locales

lemma T_subprob''[simp]: "T a \<in> space (subprob_algebra S)"
  using measurable_space[OF T_subprob', of a] by simp

lemma AE_not_suntil_coinduct [consumes 1, case_names \<psi> \<phi>]:
  assumes "P s"
  assumes \<psi>: "\<And>s. P s \<Longrightarrow> s \<notin> \<psi>"
  assumes \<phi>: "\<And>s t. P s \<Longrightarrow> s \<in> \<phi> \<Longrightarrow> t \<in> K s \<Longrightarrow> P t"
  shows "AE \<omega> in T s. not (HLD \<phi> suntil HLD \<psi>) (s ## \<omega>)"
proof -
  { fix \<omega> have "\<not> (HLD \<phi> suntil HLD \<psi>) (s ## \<omega>) \<longleftrightarrow>
      (\<forall>n. \<not> ((\<lambda>R. HLD \<psi> or (HLD \<phi> aand nxt R)) ^^ n) \<bottom> (s ## \<omega>))"
      unfolding suntil_def
      by (subst continuous_lfp)
         (auto simp add: Order_Continuity.continuous_def) }
  moreover 
  { fix n from `P s` have "AE \<omega> in T s. \<not> ((\<lambda>R. HLD \<psi> or (HLD \<phi> aand nxt R)) ^^ n) \<bottom> (s ## \<omega>)"
    proof (induction n arbitrary: s)
      case (Suc n) then show ?case
        apply (subst AE_T_iff)
        apply (rule measurable_compose[OF measurable_Stream, where M1="count_space UNIV"])
        apply measurable
        apply simp
        apply (auto simp: bot_fun_def intro!: AE_impI dest: \<phi> \<psi>)
        done
    qed simp }
  ultimately show ?thesis
    by (simp add: AE_all_countable)
qed

lemma AE_not_suntil_coinduct_strong [consumes 1, case_names \<psi> \<phi>]:
  assumes "P s"
  assumes P_\<psi>: "\<And>s. P s \<Longrightarrow> s \<notin> \<psi>"
  assumes P_\<phi>: "\<And>s t. P s \<Longrightarrow> s \<in> \<phi> \<Longrightarrow> t \<in> K s \<Longrightarrow> P t \<or> 
    (AE \<omega> in T t. not (HLD \<phi> suntil HLD \<psi>) (t ## \<omega>))"
  shows "AE \<omega> in T s. not (HLD \<phi> suntil HLD \<psi>) (s ## \<omega>)" (is "?nuntil s")
proof -
  have "P s \<or> ?nuntil s"
    using `P s` by auto
  then show ?thesis
  proof (coinduction arbitrary: s rule: AE_not_suntil_coinduct)
    case (\<phi> t s) then show ?case
      by (auto simp: AE_T_iff[of _ s] suntil_Stream[of _ _ s] dest: P_\<phi>)
  qed (auto simp: suntil_Stream dest: P_\<psi>)
qed

end

locale MC_with_rewards = MC_syntax K for K :: "'s \<Rightarrow> 's pmf" +
  fixes \<iota> :: "'s \<Rightarrow> 's \<Rightarrow> ereal" and \<rho> :: "'s \<Rightarrow> ereal"
  assumes \<iota>_nonneg: "\<And>s t. 0 \<le> \<iota> s t" and \<rho>_nonneg: "\<And>s. 0 \<le> \<rho> s"
  assumes measurable_\<iota>[measurable]: "(\<lambda>(a, b). \<iota> a b) \<in> borel_measurable (count_space UNIV \<Otimes>\<^sub>M count_space UNIV)"
begin

definition reward_until :: "'s set \<Rightarrow> 's \<Rightarrow> 's stream \<Rightarrow> ereal" where
  "reward_until X = lfp (\<lambda>F s \<omega>. if s \<in> X then 0 else \<rho> s + \<iota> s (shd \<omega>) + (0 \<squnion> (F (shd \<omega>) (stl \<omega>))))"

lemma measurable_\<rho>[measurable]: "\<rho> \<in> borel_measurable (count_space UNIV)"
  by simp

lemma measurable_reward_until[measurable (raw)]:
  assumes [measurable]: "f \<in> measurable M (count_space UNIV)"
  assumes [measurable]: "g \<in> measurable M S"
  shows "(\<lambda>x. reward_until X (f x) (g x)) \<in> borel_measurable M"
proof -
  let ?F = "\<lambda>F (s, \<omega>). if s \<in> X then 0 else \<rho> s + \<iota> s (shd \<omega>) + (0 \<squnion> (F (shd \<omega>, stl \<omega>)))"
  { fix s \<omega> 
    have "reward_until X s \<omega> = lfp ?F (s, \<omega>)"
      unfolding reward_until_def lfp_pair[symmetric] .. }
  note * = this

  have [measurable]: "lfp ?F \<in> borel_measurable (count_space UNIV \<Otimes>\<^sub>M S)"
  proof (rule borel_measurable_lfp)
    show "Order_Continuity.continuous ?F"
      using \<iota>_nonneg \<rho>_nonneg
      by (auto simp: Order_Continuity.continuous_def SUP_ereal_add_right SUP_sup_distrib[symmetric]
               simp del: sup_ereal_def)
  next
    fix f :: "('s \<times> 's stream) \<Rightarrow> ereal"
    assume [measurable]: "f \<in> borel_measurable (count_space UNIV \<Otimes>\<^sub>M S)"
    show "?F f \<in> borel_measurable (count_space UNIV \<Otimes>\<^sub>M S)"
      unfolding split_beta'
      apply (intro measurable_If)
      apply measurable []
      apply measurable []
      apply (rule predE)
      apply (rule measurable_compose[OF measurable_fst])
      apply measurable []
      done
  qed
  show ?thesis
    unfolding * by measurable
qed

lemma continuous_reward_until:
  "Order_Continuity.continuous (\<lambda>F s \<omega>. if s \<in> X then 0 else \<rho> s + \<iota> s (shd \<omega>) + (0 \<squnion> (F (shd \<omega>) (stl \<omega>))))"
  unfolding Order_Continuity.continuous_def
  using \<iota>_nonneg \<rho>_nonneg
  by (auto simp: fun_eq_iff SUP_ereal_add_right SUP_sup_distrib[symmetric] simp del: sup_ereal_def)

lemma
  shows reward_until_nonneg: "\<And>s \<omega>. 0 \<le> reward_until X s \<omega>"
    and reward_until_unfold: "reward_until X s \<omega> =
        (if s \<in> X then 0 else \<rho> s + \<iota> s (shd \<omega>) + reward_until X (shd \<omega>) (stl \<omega>))"
      (is ?unfold)
proof -
  let ?F = "\<lambda>F s \<omega>. if s \<in> X then 0 else \<rho> s + \<iota> s (shd \<omega>) + (0 \<squnion> (F (shd \<omega>) (stl \<omega>)))"
  { fix s \<omega> have "reward_until X s \<omega> = ?F (reward_until X) s \<omega>"
      unfolding reward_until_def
      apply (subst lfp_unfold)
      apply (rule continuous_reward_until[THEN continuous_mono, of X])
      apply rule
      done }
  note step = this
  show "\<And>s \<omega>. 0 \<le> reward_until X s \<omega>"
    by (subst step) (auto intro!: ereal_add_nonneg_nonneg \<iota>_nonneg \<rho>_nonneg)
  then show ?unfold
    by (subst step) (auto intro!: arg_cong2[where f="op +"] split: split_max)
qed

lemma reward_until_simps[simp]:
  shows "s \<in> X \<Longrightarrow> reward_until X s \<omega> = 0"
    and "s \<notin> X \<Longrightarrow> reward_until X s \<omega> = \<rho> s + \<iota> s (shd \<omega>) + reward_until X (shd \<omega>) (stl \<omega>)"
  unfolding reward_until_unfold[of X s \<omega>] by simp_all

lemma nn_integral_reward_until_finite:
  assumes [simp]: "finite ((SIGMA x:- H. K x)\<^sup>* `` {s})" (is "finite (?R `` {s})")
  assumes \<rho>: "\<And>t. (s, t) \<in> (SIGMA x:- H. set_pmf (K x) - H)\<^sup>* \<Longrightarrow> \<rho> t < \<infinity>"
  assumes \<iota>: "\<And>t t'. (s, t) \<in> (SIGMA x:- H. set_pmf (K x) - H)\<^sup>* \<Longrightarrow> t' \<in> K t \<Longrightarrow> \<iota> t t' < \<infinity>"
  assumes ev: "AE \<omega> in T s. ev (HLD H) \<omega>"
  shows "(\<integral>\<^sup>+ \<omega>. reward_until H s \<omega> \<partial>T s) \<noteq> \<infinity>"
proof cases
  assume "s \<in> H" then show ?thesis
    by simp
next
  assume "s \<notin>  H"
  let ?L = "(SIGMA x:- H. set_pmf (K x) - H)\<^sup>*"
  def M \<equiv> "Max ((\<lambda>(s, t). \<rho> s + \<iota> s t) ` (SIGMA t:?L``{s}. K t))"
  have "?L \<subseteq> ?R"
    by (intro rtrancl_mono) auto
  with `s \<notin> H` have subset: "(SIGMA t:?L``{s}. K t) \<subseteq> (?R``{s} \<times> ?R``{s})"
    by (auto intro: rtrancl_into_rtrancl elim: rtrancl.cases)
  then have [simp, intro!]: "finite ((\<lambda>(s, t). \<rho> s + \<iota> s t) ` (SIGMA t:?L``{s}. K t))"
    by (intro finite_imageI) (auto dest: finite_subset)
  { fix t t' assume "(s, t) \<in> ?L" "t \<notin> H" "t' \<in> K t"
    then have "(t, t') \<in> (SIGMA t:?L``{s}. K t)"
      by (auto intro: rtrancl_into_rtrancl)
    then have "\<rho> t + \<iota> t t' \<le> M"
      unfolding M_def by (intro Max_ge) auto }
  note le_M = this

  have fin_L: "finite (?L `` {s})"
    by (intro finite_subset[OF _ assms(1)] Image_mono `?L \<subseteq> ?R` order_refl)

  have "M < \<infinity>"
    unfolding M_def
  proof (subst Max_less_iff, safe)
    show "(SIGMA x:?L `` {s}. set_pmf (K x)) = {} \<Longrightarrow> False"
      using `s \<notin> H` by (auto simp add: Sigma_empty_iff set_pmf_not_empty)
    fix t t' assume "(s, t) \<in> ?L" "t' \<in> K t" then show "\<rho> t + \<iota> t t' < \<infinity>"
      using \<rho>[of t] \<iota>[of t t'] by simp
  qed

  from set_pmf_not_empty[of "K s"] obtain t where "t \<in> K s"
    by auto
  with le_M[of s t] have "0 \<le> M"
    using set_pmf_not_empty[of "K s"] `s \<notin> H` le_M[of s] \<iota>_nonneg[of s] \<rho>_nonneg[of s]
    by (intro order_trans[OF _ le_M]) auto

  have "AE \<omega> in T s. reward_until H s \<omega> \<le> M * sfirst (HLD H) (s ## \<omega>)"
    using ev AE_T_enabled
  proof eventually_elim
    fix \<omega> assume "ev (HLD H) \<omega>" "enabled s \<omega>"
    moreover def t\<equiv>"s"
    ultimately have "ev (HLD H) \<omega>" "enabled t \<omega>" "t \<in> ?L``{s}"
      by auto
    then show "reward_until H t \<omega> \<le> M * sfirst (HLD H) (t ## \<omega>)"
    proof (induction arbitrary: t rule: ev_induct_strong)
      case (base \<omega> t) then show ?case
        by (auto simp: HLD_iff sfirst_Stream elim: enabled.cases intro: le_M)
    next
      case (step \<omega> t) from step.IH[of "shd \<omega>"] step.prems step.hyps show ?case
        by (auto simp add: HLD_iff enabled.simps[of t] ereal_right_distrib sfirst_Stream
                           reward_until_simps[of t]
                 simp del: reward_until_simps
                 intro!: ereal_add_mono le_M intro: rtrancl_into_rtrancl)
    qed
  qed
  then have "(\<integral>\<^sup>+\<omega>. reward_until H s \<omega> \<partial>T s) \<le> (\<integral>\<^sup>+\<omega>. M * sfirst (HLD H) (s ## \<omega>) \<partial>T s)"
    by (rule nn_integral_mono_AE)
  also have "\<dots> < \<infinity>"
    using `0 \<le> M` `M < \<infinity>` nn_integral_sfirst_finite[OF fin_L ev]
    by (simp add: nn_integral_cmult not_less nn_integral_nonneg)
  finally show ?thesis
    by simp
qed

end

locale MC_pair =
  K1!: MC_syntax K1 + K2!: MC_syntax K2 for K1 K2
begin

definition "Kp \<equiv> \<lambda>(a, b). pair_pmf (K1 a) (K2 b)"

sublocale MC_syntax Kp .

definition 
  "szip\<^sub>E a b \<equiv> \<lambda>(\<omega>1, \<omega>2). szip (K1.force_enabled a \<omega>1) (K2.force_enabled b \<omega>2)"

lemma szip_rT[measurable]: "(\<lambda>(\<omega>1, \<omega>2). szip \<omega>1 \<omega>2) \<in> measurable (K1.rT x1 \<Otimes>\<^sub>M K2.rT x2) S"
proof (rule measurable_stream_space2)
  fix n
  have "(\<lambda>x. (case x of (\<omega>1, \<omega>2) \<Rightarrow> szip \<omega>1 \<omega>2) !! n) = (\<lambda>\<omega>. (fst \<omega> !! n, snd \<omega> !! n))"
    by auto
  also have "\<dots> \<in> measurable (K1.rT x1 \<Otimes>\<^sub>M K2.rT x2) (count_space UNIV)"
    apply (rule measurable_compose_countable'[OF _ measurable_compose[OF measurable_fst K1.snth_rT, of n]])
    apply (rule measurable_compose_countable'[OF _ measurable_compose[OF measurable_snd K2.snth_rT, of n]])
    apply (auto intro!: K1.countable_accessible K2.countable_accessible)
    done
  finally show "(\<lambda>x. (case x of (\<omega>1, \<omega>2) \<Rightarrow> szip \<omega>1 \<omega>2) !! n) \<in> measurable (K1.rT x1 \<Otimes>\<^sub>M K2.rT x2) (count_space UNIV)"
    .
qed

lemma measurable_szipE[measurable]: "szip\<^sub>E a b \<in> measurable (K1.S \<Otimes>\<^sub>M K2.S) S"
  unfolding szip\<^sub>E_def by measurable

lemma T_eq_prod: "T = (\<lambda>(x1, x2). do { \<omega>1 \<leftarrow> K1.T x1 ; \<omega>2 \<leftarrow> K2.T x2 ; return S (szip\<^sub>E x1 x2 (\<omega>1, \<omega>2)) })"
  (is "_ = ?B")
proof (rule T_bisim)
  have T1x: "\<And>x. subprob_space (K1.T x)"
    by (rule prob_space_imp_subprob_space) unfold_locales

  interpret T12: pair_prob_space "K1.T x" "K2.T y" for x y
    by unfold_locales
  interpret T1K2: pair_prob_space "K1.T x" "K2 y" for x y
    by unfold_locales

  let ?P = "\<lambda>x1 x2. K1.T x1 \<Otimes>\<^sub>M K2.T x2"


  fix x show "prob_space (?B x)"
    by (auto simp: space_stream_space split: prod.splits
                intro!: prob_space.prob_space_bind prob_space_return
                        measurable_bind[where N=S] measurable_compose[OF _ return_measurable] AE_I2)
       unfold_locales

  show "sets (?B x) = sets S"
    by (simp split: prod.splits add: measurable_bind[where N=S] sets_bind[where N=S] space_stream_space)

  obtain a b where x_eq: "x = (a, b)"
    by (cases x) auto
  show "?B x = (measure_pmf (Kp x) \<guillemotright>= (\<lambda>s. distr (?B s) S (op ## s)))"
    unfolding x_eq
    apply (subst K1.T_eq_bind')
    apply (subst K2.T_eq_bind')
    apply (auto
         simp add: space_stream_space bind_assoc[where R=S and N=S] bind_return_distr[symmetric]
                   Kp_def T1K2.bind_rotate[where N=S] split_beta' set_pair_pmf space_subprob_algebra
                   bind_pair_pmf[of "split M" for M, unfolded split, symmetric, where N=S] szip\<^sub>E_def
                   stream_eq_Stream_iff bind_return[where N=S] space_bind[where N=S]
         simp del: measurable_pmf_measure1
         intro!: bind_measure_pmf_cong[where N=S] subprob_space_bind[where N=S] subprob_space_measure_pmf
                 T1x bind_cong[where M="MC_syntax.T K x" for K x] arg_cong2[where f=return])
    done
qed

lemma nn_integral_pT: 
  fixes f assumes [measurable]: "f \<in> borel_measurable S"
  shows "(\<integral>\<^sup>+\<omega>. f \<omega> \<partial>T (x, y)) = (\<integral>\<^sup>+\<omega>1. \<integral>\<^sup>+\<omega>2. f (szip\<^sub>E x y (\<omega>1, \<omega>2)) \<partial>K2.T y \<partial>K1.T x)"
  by (subst (1 3) nn_integral_max_0[symmetric])
     (simp add: nn_integral_bind[where B=S] nn_integral_return in_S T_eq_prod)

lemma prod_eq_prob_T:
  assumes [measurable]: "Measurable.pred K1.S P1" "Measurable.pred K2.S P2"
  shows "\<P>(\<omega> in K1.T x1. P1 \<omega>) * \<P>(\<omega> in K2.T x2. P2 \<omega>) =
    \<P>(\<omega> in T (x1, x2). P1 (smap fst \<omega>) \<and> P2 (smap snd \<omega>))"
proof -
  have "\<P>(\<omega> in T (x1, x2). P1 (smap fst \<omega>) \<and> P2 (smap snd \<omega>)) =
    (\<integral> x. \<integral> xa. indicator {\<omega> \<in> space S. P1 (smap fst \<omega>) \<and> P2 (smap snd \<omega>)} (szip\<^sub>E x1 x2 (x, xa)) \<partial>MC_syntax.T K2 x2 \<partial>MC_syntax.T K1 x1)"
    by (subst T_eq_prod)
       (simp add: K1.T.measure_bind[where N=S] K2.T.measure_bind[where N=S] measure_return)
  also have "... = (\<integral>\<omega>1. \<integral>\<omega>2. indicator {\<omega>\<in>space K1.S. P1 \<omega>} \<omega>1 * indicator {\<omega>\<in>space K2.S. P2 \<omega>} \<omega>2 \<partial>K2.T x2 \<partial>K1.T x1)"
    apply (intro integral_cong_AE)
    apply measurable
    using K1.AE_T_enabled
    apply eventually_elim
    apply (intro integral_cong_AE)
    apply measurable
    using K2.AE_T_enabled
    apply eventually_elim
    apply (auto simp: space_stream_space szip\<^sub>E_def K1.force_enabled K2.force_enabled
                      smap_szip_snd[where g="\<lambda>x. x"] smap_szip_fst[where f="\<lambda>x. x"]
                split: split_indicator)
    done
  also have "\<dots> = \<P>(\<omega> in K1.T x1. P1 \<omega>) * \<P>(\<omega> in K2.T x2. P2 \<omega>)"
    by simp
  finally show ?thesis ..
qed

end

end

