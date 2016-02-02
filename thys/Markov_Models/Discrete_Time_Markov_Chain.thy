(* Author: Johannes Hölzl <hoelzl@in.tum.de> *)

section {* Discrete-Time Markov Chain *}

theory Discrete_Time_Markov_Chain
  imports
    "~~/src/HOL/Probability/Probability"
    "~~/src/HOL/Library/Rewrite"
    "~~/src/HOL/Library/Linear_Temporal_Logic_on_Streams"
    "../Coinductive/Coinductive_Stream"
    "../Coinductive/Coinductive_Nat"
begin

lemma mult_eq_1:
  fixes a b :: "'a :: {ordered_semiring, comm_monoid_mult}"
  shows "0 \<le> a \<Longrightarrow> a \<le> 1 \<Longrightarrow> b \<le> 1 \<Longrightarrow> a * b = 1 \<longleftrightarrow> (a = 1 \<and> b = 1)"
  by (metis mult.left_neutral eq_iff mult.commute mult_right_mono)

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
      by (cases "f x")
         (simp_all add: sums_def tendsto_PInfty_eq_at_top filterlim_real_sequentially one_ereal_def)
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

lemma ereal_of_enat_inj[simp]:
  "ereal_of_enat i = ereal_of_enat j \<longleftrightarrow> i = j"
  by (cases i j rule: enat.exhaust[case_product enat.exhaust]) auto

lemma inf_continuous_suntil_disj[order_continuous_intros]:
  assumes Q: "inf_continuous Q"
  assumes disj: "\<And>x \<omega>. \<not> (P \<omega> \<and> Q x \<omega>)"
  shows "inf_continuous (\<lambda>x. P suntil Q x)"
  unfolding inf_continuous_def
proof (safe intro!: ext)
  fix M \<omega> i assume "(P suntil Q (\<Sqinter>i. M i)) \<omega>" "decseq M" then show "(P suntil Q (M i)) \<omega>"
    unfolding inf_continuousD[OF Q `decseq M`] by induction (auto intro: suntil.intros)
next
  fix M \<omega> assume *: "(\<Sqinter>i. P suntil Q (M i)) \<omega>" "decseq M"
  then have "(P suntil Q (M 0)) \<omega>"
    by auto
  from this * show "(P suntil Q (\<Sqinter>i. M i)) \<omega>"
    unfolding inf_continuousD[OF Q `decseq M`]
  proof induction
    case (base \<omega>) with disj[of \<omega> "M _"] show ?case by (auto intro: suntil.intros elim: suntil.cases)
  next
    case (step \<omega>) with disj[of \<omega> "M _"] show ?case by (auto intro: suntil.intros elim: suntil.cases)
  qed
qed

lemma inf_continuous_nxt[order_continuous_intros]: "inf_continuous P \<Longrightarrow> inf_continuous (\<lambda>x. nxt (P x) \<omega>)"
  by (auto simp: inf_continuous_def)

lemma sup_continuous_nxt[order_continuous_intros]: "sup_continuous P \<Longrightarrow> sup_continuous (\<lambda>x. nxt (P x) \<omega>)"
  by (auto simp: sup_continuous_def)

lemma ev_eq_suntil: "ev P \<omega> \<longleftrightarrow> (not P suntil P) \<omega>"
proof
  assume "ev P \<omega>" then show "((\<lambda>xs. \<not> P xs) suntil P) \<omega>"
    by (induction rule: ev_induct_strong) (auto intro: suntil.intros)
qed (auto simp: ev_suntil)

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

abbreviation acc :: "('s \<times> 's) set" where
  "acc \<equiv> (SIGMA s:UNIV. K s)\<^sup>*"

abbreviation acc_on :: "'s set \<Rightarrow> ('s \<times> 's) set" where
  "acc_on S \<equiv> (SIGMA s:UNIV. K s \<inter> S)\<^sup>*"

lemma countable_reachable: "countable (acc `` {s})"
  by (auto intro!: countable_rtrancl countable_set_pmf simp: Sigma_Image)

lemma countable_acc: "countable X \<Longrightarrow> countable (acc `` X)"
  apply (rule countable_Image)
  apply (rule countable_reachable)
  apply assumption
  done

context
  notes [[inductive_internals]]
begin

coinductive enabled where
  "enabled (shd \<omega>) (stl \<omega>) \<Longrightarrow> shd \<omega> \<in> K s \<Longrightarrow> enabled s \<omega>"

end

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
qed (auto simp: inf_continuous_def)

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
  then have "g \<in> measurable D (count_space (acc `` {s}))"
    by auto
  then have "(\<lambda>x. walk (g x) (sdrop n x)) \<in> measurable D S"
  proof (coinduction arbitrary: g n rule: measurable_stream_coinduct)
    case (shd g) show ?case
      by (fastforce intro: measurable_g[OF _ shd])
  next
    case (stl g) show ?case
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

sublocale T: prob_space "T s" for s
proof -
  interpret P: product_prob_space K UNIV ..
  interpret prob_space "stream_space (\<Pi>\<^sub>M s\<in>UNIV. K s)"
    by (rule P.prob_space_stream_space)
  fix s show "prob_space (T s)"
    by (simp add: T_def prob_space_distr)
qed

lemma emeasure_T_const[simp]: "emeasure (T s) (space S) = 1"
  using T.emeasure_space_1[of s] by simp

lemma nn_integral_T:
  assumes f[measurable]: "f \<in> borel_measurable S"
  shows "(\<integral>\<^sup>+X. f X \<partial>T s) = (\<integral>\<^sup>+t. (\<integral>\<^sup>+\<omega>. f (t ## \<omega>) \<partial>T t) \<partial>K s)"
proof -
  interpret product_prob_space K UNIV ..
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
  also have "\<dots> = (\<integral>\<^sup>+d. \<integral>\<^sup>+\<omega>. f (d s ## \<omega>) * indicator (K s) (d s) \<partial>T (d s) \<partial>\<Pi>\<^sub>M i\<in>UNIV. K i)"
    by (subst T) (simp_all split: split_indicator)
  also have "\<dots> = (\<integral>\<^sup>+t. \<integral>\<^sup>+\<omega>. f (t ## \<omega>) * indicator (K s) t \<partial>T t \<partial>K s)"
    by (subst (2) PiM_component[symmetric]) (simp_all add: nn_integral_distr)
  also have "\<dots> = (\<integral>\<^sup>+t. \<integral>\<^sup>+\<omega>. f (t ## \<omega>) \<partial>T t \<partial>K s)"
    by (rule nn_integral_cong_AE) (simp add: AE_measure_pmf_iff)
  finally show ?thesis .
qed

lemma nn_integral_T_gfp:
  fixes g
  defines "l \<equiv> \<lambda>f \<omega>. g (shd \<omega>) (f (stl \<omega>))"
  assumes [measurable]: "case_prod g \<in> borel_measurable (count_space UNIV \<Otimes>\<^sub>M borel)"
  assumes cont_g[THEN inf_continuous_compose, order_continuous_intros]: "\<And>s. inf_continuous (g s)"
  assumes int_g: "\<And>f s. f \<in> borel_measurable S \<Longrightarrow> (\<integral>\<^sup>+\<omega>. g s (f \<omega>) \<partial>T s) = g s (\<integral>\<^sup>+\<omega>. f \<omega> \<partial>T s)"
  assumes bnd_g: "\<And>f s. g s f \<le> b" "0 \<le> b" "b < \<infinity>"
  shows "(\<integral>\<^sup>+\<omega>. gfp l \<omega> \<partial>T s) = gfp (\<lambda>f s. \<integral>\<^sup>+t. g t (f t) \<partial>K s) s"
proof (rule nn_integral_gfp)
  show "\<And>s. sets (T s) = sets S" "\<And>F. F \<in> borel_measurable S \<Longrightarrow> l F \<in> borel_measurable S"
    by (auto simp: l_def)
  show "\<And>s. emeasure (T s) (space (T s)) \<noteq> 0"
   by (rewrite T.emeasure_space_1) simp
  { fix s F
    have "integral\<^sup>N (T s) (l F) \<le> (\<integral>\<^sup>+x. b \<partial>T s)"
      by (intro nn_integral_mono) (simp add: l_def bnd_g)
    also have "\<dots> < \<infinity>"
      using bnd_g by simp
    finally show "integral\<^sup>N (T s) (l F) < \<infinity>" . }
  show "inf_continuous (\<lambda>f s. \<integral>\<^sup>+ t. g t (f t) \<partial>K s)"
  proof (intro order_continuous_intros)
    fix f s
    have "(\<integral>\<^sup>+ t. g t (f t) \<partial>K s) \<le> (\<integral>\<^sup>+ t. b \<partial>K s)"
      by (intro nn_integral_mono bnd_g)
    also have "\<dots> < \<infinity>"
      using bnd_g by simp
    finally show "(\<integral>\<^sup>+ t. g t (f t) \<partial>K s) \<noteq> \<infinity>"
      by simp
  qed simp
next
  fix s and F :: "'s stream \<Rightarrow> ereal" assume "F \<in> borel_measurable S"
  then show "integral\<^sup>N (T s) (l F) = (\<integral>\<^sup>+ t. g t (integral\<^sup>N (T t) F) \<partial>K s) "
    by (rewrite nn_integral_T) (simp_all add: l_def int_g)
qed (auto intro!: order_continuous_intros simp: l_def)

lemma nn_integral_T_lfp:
  fixes g
  defines "l \<equiv> \<lambda>f \<omega>. g (shd \<omega>) (f (stl \<omega>))"
  assumes [measurable]: "case_prod g \<in> borel_measurable (count_space UNIV \<Otimes>\<^sub>M borel)"
  assumes cont_g[THEN sup_continuous_compose, order_continuous_intros]: "\<And>s. sup_continuous (g s)"
  assumes int_g: "\<And>f s. f \<in> borel_measurable S \<Longrightarrow> (\<integral>\<^sup>+\<omega>. g s (f \<omega>) \<partial>T s) = g s (\<integral>\<^sup>+\<omega>. f \<omega> \<partial>T s)"
  shows "(\<integral>\<^sup>+\<omega>. lfp l \<omega> \<partial>T s) = lfp (\<lambda>f s. \<integral>\<^sup>+t. g t (f t) \<partial>K s) s"
proof (rule nn_integral_lfp)
  show "\<And>s. sets (T s) = sets S" "\<And>F. F \<in> borel_measurable S \<Longrightarrow> l F \<in> borel_measurable S"
       "\<And>F s. 0 \<le> (\<integral>\<^sup>+ t. g t (F t) \<partial>K s)"
    by (auto simp: l_def nn_integral_nonneg)
next
  fix s and F :: "'s stream \<Rightarrow> ereal" assume "F \<in> borel_measurable S"
  then show "integral\<^sup>N (T s) (l F) = (\<integral>\<^sup>+ t. g t (integral\<^sup>N (T t) F) \<partial>K s) "
    by (rewrite nn_integral_T) (simp_all add: l_def int_g)
qed (auto simp: l_def intro!: order_continuous_intros)

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

lemma AE_T_alw:
  assumes [measurable]: "Measurable.pred S P"
  assumes P: "\<And>s. (x, s) \<in> acc \<Longrightarrow> AE \<omega> in T s. P \<omega>"
  shows "AE \<omega> in T x. alw P \<omega>"
proof -
  def F \<equiv> "\<lambda>p x. P x \<and> p (stl x)"
  have [measurable]: "\<And>p. Measurable.pred S p \<Longrightarrow> Measurable.pred S (F p)"
    by (auto simp: F_def)
  have "almost_everywhere (T s) ((F ^^ i) top)"
    if "(x, s) \<in> acc" for i s
    using that
  proof (induction i arbitrary: s)
    case (Suc i) then show ?case
      apply simp
      apply (subst F_def)
      apply (simp add: P)
      apply (subst AE_T_iff)
      apply (measurable; simp)
      apply (auto dest: rtrancl_into_rtrancl)
      done
  qed simp
  then have "almost_everywhere (T x) (gfp F)"
    by (subst inf_continuous_gfp) (auto simp: inf_continuous_def AE_all_countable F_def)
  then show ?thesis
    by (simp add: alw_def F_def)
qed

lemma emeasure_suntil_disj:
  assumes [measurable]: "Measurable.pred S P"
  assumes *: "\<And>t. AE \<omega> in T t. \<not> (P \<sqinter> (HLD X \<sqinter> nxt (HLD X suntil P))) \<omega>"
  shows "emeasure (T s) {\<omega>\<in>space (T s). (HLD X suntil P) \<omega>} =
    lfp (\<lambda>F s. emeasure (T s) {\<omega>\<in>space (T s). P \<omega>} + (\<integral>\<^sup>+t. F t * indicator X t \<partial>K s)) s"
  unfolding suntil_lfp
proof (rule emeasure_lfp[where s=s])
  fix F t assume [measurable]: "Measurable.pred (T s) F" and
    F: "F \<le> lfp (\<lambda>a b. P b \<or> HLD X b \<and> a (stl b))"
  have "emeasure (T t) {\<omega> \<in> space (T s). P \<omega> \<or> HLD X \<omega> \<and> F (stl \<omega>)} =
    emeasure (T t) {\<omega> \<in> space (T t). P \<omega>} + emeasure (T t) {\<omega>\<in>space (T t). HLD X \<omega> \<and> F (stl \<omega>)}"
  proof (rule emeasure_add_AE)
    show "AE x in T t. \<not> (x \<in> {\<omega> \<in> space (T t). P \<omega>} \<and> x \<in> {\<omega> \<in> space (T t). HLD X \<omega> \<and> F (stl \<omega>)})"
      using * by eventually_elim (insert F, auto simp: suntil_lfp[symmetric])
  qed auto
  also have "emeasure (T t) {\<omega>\<in>space (T t). HLD X \<omega> \<and> F (stl \<omega>)} =
    (\<integral>\<^sup>+t. emeasure (T t) {\<omega> \<in> space (T s). F \<omega>} * indicator X t \<partial>K t)"
    by (subst emeasure_Collect_T) (auto intro!: nn_integral_cong split: split_indicator)
  finally show "emeasure (T t) {\<omega> \<in> space (T s). P \<omega> \<or> HLD X \<omega> \<and> F (stl \<omega>)} =
    emeasure (T t) {\<omega> \<in> space (T t). P \<omega>} + (\<integral>\<^sup>+ t. emeasure (T t) {\<omega> \<in> space (T s). F \<omega>} * indicator X t \<partial>K t)" .
qed (auto intro!: order_continuous_intros split: split_indicator simp: emeasure_nonneg nn_integral_nonneg)

lemma emeasure_positive: "0 < emeasure M A \<longleftrightarrow> emeasure M A \<noteq> 0"
  using emeasure_nonneg[of M A] by auto

lemma emeasure_HLD_nxt:
  assumes [measurable]: "Measurable.pred S P"
  shows "emeasure (T s) {\<omega>\<in>space (T s). (X \<cdot> P) \<omega>} =
    (\<integral>\<^sup>+x. emeasure (T x) {\<omega>\<in>space (T x). P \<omega>} * indicator X x \<partial>K s)"
  by (subst emeasure_Collect_T)
     (auto intro!: nn_integral_cong_AE simp: AE_measure_pmf_iff split: split_indicator)

lemma emeasure_HLD:
  "emeasure (T s) {\<omega>\<in>space (T s). HLD X \<omega>} = emeasure (K s) X"
  using emeasure_HLD_nxt[of "\<lambda>\<omega>. True" s X] T.emeasure_space_1 by simp

lemma emeasure_suntil_HLD:
  assumes [measurable]: "Measurable.pred S P"
  shows "emeasure (T s) {x\<in>space (T s). (not (HLD {t}) suntil (HLD {t} aand nxt P)) x} =
   emeasure (T s) {x\<in>space (T s). ev (HLD {t}) x} * emeasure (T t) {x\<in>space (T t). P x}"
proof -
  let ?P = "emeasure (T t) {\<omega>\<in>space (T t). P \<omega>}"
  let ?F = "\<lambda>Q F s. emeasure (T s) {\<omega>\<in>space (T s). Q \<omega>} + (\<integral>\<^sup>+t'. F t' * indicator (- {t}) t' \<partial>K s)"
  have "emeasure (T s) {x\<in>space (T s). (HLD (-{t}) suntil ({t} \<cdot> P)) x} = lfp (?F ({t} \<cdot> P)) s"
    by (rule emeasure_suntil_disj) (auto simp: HLD_iff)
  also have "lfp (?F ({t} \<cdot> P)) = (\<lambda>s. lfp (?F (HLD {t})) s * ?P)"
  proof (rule lfp_transfer[symmetric, where \<alpha>="\<lambda>x s. x s * emeasure (T t) {\<omega>\<in>space (T t). P \<omega>}"])
    fix F show "(\<lambda>s. ?F (HLD {t}) F s * ?P) = ?F ({t} \<cdot> P) (\<lambda>s. F s * ?P)"
      unfolding emeasure_HLD emeasure_HLD_nxt[OF assms]
      apply (subst (1 3) nn_integral_max_0[symmetric])
      apply (simp add: ereal_left_distrib emeasure_nonneg nn_integral_nonneg max_absorb2)
      apply (auto simp: ac_simps fun_eq_iff nn_integral_cmult[symmetric] emeasure_nonneg ereal_zero_le_0_iff ereal_mult_le_0_iff
                        emeasure_positive[symmetric]
                  intro!: arg_cong[where f="\<lambda>x. c + x" for c] nn_integral_cong split: split_max split_indicator)
      done
  qed (auto intro!: order_continuous_intros split: split_indicator
              simp: nn_integral_nonneg emeasure_nonneg le_fun_def emeasure_positive bot_ereal_def)
  also have "lfp (?F (HLD {t})) s = emeasure (T s) {x\<in>space (T s). (HLD (-{t}) suntil HLD {t}) x}"
    by (rule emeasure_suntil_disj[symmetric]) (auto simp: HLD_iff)
  finally show ?thesis
    by (simp add: HLD_iff[abs_def] ev_eq_suntil)
qed

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

lemma AE_T_fair:
  assumes "t' \<in> K t"
  shows "AE \<omega> in T s. fair t t' \<omega>"
proof -
  let ?M = "\<lambda>P s. emeasure (T s) {\<omega>\<in>space (T s). P \<omega>}"
  let ?t = "HLD {t}" and ?t' = "HLD {t'}"
  def N \<equiv> "alw (ev ?t) aand alw (not (?t aand nxt ?t'))"
  let ?until = "not ?t suntil (?t aand nxt (not ?t' aand nxt N))"
  have N_stl: "\<And>\<omega>. N \<omega> \<Longrightarrow> N (stl \<omega>)"
    by (auto simp: N_def)
  have [measurable]: "Measurable.pred S N"
    unfolding N_def by measurable

  let ?c = "pmf (K t) t'"
  let ?R = "\<lambda>x. 1 \<sqinter> x * (1 - ereal ?c)"
  have "mono ?R"
    by (intro monoI ereal_mult_right_mono inf_mono)
       (auto simp: mono_def field_simps one_ereal_def pmf_le_1)
  have "\<And>s. ?M N s \<le> gfp ?R"
  proof (induction rule: gfp_ordinal_induct[OF \<open>mono ?R\<close>])
    fix x s assume x: "\<And>s. ?M N s \<le> x"
    { fix \<omega> assume "N \<omega>"
      then have "ev (HLD {t}) \<omega>" "N \<omega>"
        by (auto simp: N_def)
      then have "?until \<omega>"
        by (induct rule: ev_induct_strong) (auto simp: N_def intro: suntil.intros dest: N_stl) }
    then have "?M N s \<le> ?M ?until s"
      by (intro emeasure_mono_AE) auto
    also have "\<dots> = ?M (ev ?t) s * ?M (not ?t' aand nxt N) t"
      by (simp_all add: emeasure_suntil_HLD del: nxt.simps space_T)
    also have "\<dots> \<le> ?M (ev ?t) s * (\<integral>\<^sup>+s'. 1 \<sqinter> x * indicator (UNIV - {t'}) s' \<partial>K t)"
      by (auto intro!: ereal_mult_left_mono nn_integral_nonneg nn_integral_mono T.measure_le_1 emeasure_mono
               split: split_indicator simp add: x emeasure_Collect_T[of _ t] simp del: space_T)
    also have "\<dots> \<le> 1 * (\<integral>\<^sup>+s'. 1 \<sqinter> x * indicator (UNIV - {t'}) s' \<partial>K t)"
      by (intro ereal_mult_right_mono nn_integral_nonneg T.measure_le_1)
    finally show "?M N s \<le> 1 \<sqinter> x * (1 - ereal ?c)"
      using order_trans[OF emeasure_nonneg x]
      by (subst (asm) nn_integral_cmult_indicator) (auto simp: emeasure_Diff emeasure_pmf_single)
  qed (auto intro: Inf_greatest)
  also have "gfp ?R \<le> 0"
    using gfp_lemma2[OF \<open>mono ?R\<close>] assms[THEN pmf_positive]
    by (cases "gfp ?R" rule: ereal_cases)
       (auto simp: one_ereal_def min_def field_simps mult_le_0_iff split: split_if_asm)
  finally have "\<And>s. AE \<omega> in T s. \<not> N \<omega>"
    by (subst AE_iff_measurable[OF _ refl]) (auto intro: antisym simp: le_fun_def)
  then have "AE \<omega> in T s. alw (not N) \<omega>"
    by (intro AE_T_alw) auto
  moreover
  { fix \<omega> assume "alw (ev (HLD {t})) \<omega>"
    then have "alw (alw (ev (HLD {t}))) \<omega>"
      unfolding alw_alw .
    moreover assume "alw (not N) \<omega>"
    then have "alw (alw (ev (HLD {t})) impl ev (HLD {t} aand nxt (HLD {t'}))) \<omega>"
      unfolding N_def not_alw_iff not_ev_iff de_Morgan_disj de_Morgan_conj not_not imp_conv_disj .
    ultimately have "alw (ev (HLD {t} aand nxt (HLD {t'}))) \<omega>"
      by (rule alw_mp) }
  then have "\<forall>\<omega>. alw (not N) \<omega> \<longrightarrow> fair t t' \<omega>"
    by (auto simp: fair_def)
  ultimately show ?thesis
    by (simp add: eventually_mono)
qed

lemma enabled_imp_trancl:
  assumes "alw (HLD B) \<omega>" "enabled s \<omega>"
  shows "alw (HLD (acc_on B `` {s})) \<omega>"
proof -
  def t \<equiv> s
  then have "(s, t) \<in> acc_on B"
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

lemma AE_T_reachable: "AE \<omega> in T s. alw (HLD (acc `` {s})) \<omega>"
  using AE_T_enabled
proof eventually_elim
  fix \<omega> assume "enabled s \<omega>"
  from enabled_imp_trancl[of UNIV, OF _ this]
  show "alw (HLD (acc `` {s})) \<omega>"
    by (auto simp: HLD_iff[abs_def] all_imp_alw)
qed

lemma AE_T_all_fair: "AE \<omega> in T s. \<forall>(t,t')\<in>SIGMA t:UNIV. K t. fair t t' \<omega>"
proof -
  let ?Rn = "SIGMA s:(acc `` {s}). K s"
  have "AE \<omega> in T s. \<forall>(t,t')\<in>?Rn. fair t t' \<omega>"
  proof (subst AE_ball_countable)
    show "countable ?Rn"
      by (intro countable_SIGMA countable_rtrancl[OF countable_Image]) (auto simp: Image_def)
  qed (auto intro!: AE_T_fair)
  then show ?thesis
    using AE_T_reachable
  proof (eventually_elim, safe)
    fix \<omega> t t' assume "\<forall>(t,t')\<in>?Rn. fair t t' \<omega>" "t' \<in> K t" and alw: "alw (HLD (acc `` {s})) \<omega>"
    moreover
    { assume "t \<notin> acc `` {s}"
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

lemma fair_imp: assumes "fair t t' \<omega>" "alw (ev (HLD {t})) \<omega>" shows "alw (ev (HLD {t'})) \<omega>"
proof -
  { fix \<omega> assume "ev (HLD {t} aand nxt (HLD {t'})) \<omega>" then have "ev (HLD {t'}) \<omega>"
      by induction auto }
  with assms show ?thesis
    by (auto simp: fair_def elim!: alw_mp intro: all_imp_alw)
qed

lemma AE_T_ev_HLD:
  assumes exiting: "\<And>t. (s, t) \<in> acc_on (-B) \<Longrightarrow> \<exists>t'\<in>B. (t, t') \<in> acc"
  assumes fin: "finite (acc_on (-B) `` {s})"
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
    have "alw (HLD (acc_on (-B) `` {s})) \<omega>"
      by (simp add: Diff_eq)
    from pigeonhole_stream[OF this fin]
    obtain t where "(s, t) \<in> acc_on (-B)" "alw (ev (HLD {t})) \<omega>"
      by auto
    from exiting[OF this(1)] obtain t' where "(t, t') \<in> acc" "t' \<in> B"
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

lemma AE_T_ev_HLD':
  assumes exiting: "\<And>s. s \<notin> X \<Longrightarrow> \<exists>t\<in>X. (s, t) \<in> acc"
  assumes fin: "finite (-X)"
  shows "AE \<omega> in T s. ev (HLD X) \<omega>"
proof (rule AE_T_ev_HLD)
  show "\<And>t. (s, t) \<in> acc_on (- X) \<Longrightarrow> \<exists>t'\<in>X. (t, t') \<in> acc"
    using exiting by (auto elim: rtrancl.cases)
  have "acc_on (- X) `` {s} \<subseteq> -X \<union> {s}"
    by (auto elim: rtrancl.cases)
  with fin show "finite (acc_on (- X) `` {s})"
    by (auto dest: finite_subset )
qed

lemma AE_T_max_sfirst:
  assumes [measurable]: "Measurable.pred S X"
  assumes AE: "AE \<omega> in T c. sfirst X (c ## \<omega>) < \<infinity>" and "0 < e"
  shows "\<exists>N::nat. \<P>(\<omega> in T c. N < sfirst X (c ## \<omega>)) < e" (is "\<exists>N. ?P N < e")
proof -
  have "?P \<longlonglongrightarrow> measure (T c) (\<Inter>N::nat. {bT \<in> space (T c). N < sfirst X (c ## bT)})"
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

lemma nn_integral_sfirst_finite':
  assumes "s \<notin> H"
  assumes [simp]: "finite (acc_on (-H) `` {s})"
  assumes until: "AE \<omega> in T s. ev (HLD H) \<omega>"
  shows "(\<integral>\<^sup>+ \<omega>. sfirst (HLD H) \<omega> \<partial>T s) \<noteq> \<infinity>"
proof -
  have R_ne[simp]: "acc_on (-H) `` {s} \<noteq> {}"
    by auto
  have [measurable]: "H \<in> sets (count_space UNIV)"
    by simp

  let ?Pf = "\<lambda>n t. \<P>(\<omega> in T t. enat n < sfirst (HLD H) (t ## \<omega>))"
  have Pf_mono: "\<And>N n t. N \<le> n \<Longrightarrow> ?Pf n t \<le> ?Pf N t"
    by (auto intro!: T.finite_measure_mono simp del: enat_ord_code(1) simp: enat_ord_code(1)[symmetric])

  have not_H: "\<And>t. (s, t) \<in> acc_on (-H) \<Longrightarrow> t \<notin> H"
    using `s \<notin> H` by (auto elim: rtrancl.cases)

  have "\<forall>\<^sub>F n in sequentially. \<forall>t\<in>acc_on (-H)``{s}. ?Pf n t < 1"
  proof (safe intro!: eventually_ball_finite)
    fix t assume "(s, t) \<in> acc_on (-H)"
    then have "AE \<omega> in T t. sfirst (HLD H) (t ## \<omega>) < \<infinity>"
      unfolding sfirst_finite
    proof induction
      case (step t u) with step.IH show ?case
        by (subst (asm) AE_T_iff) (auto simp: ev_Stream not_H)
    qed (simp add: ev_Stream eventually_frequently_simps until)
    from AE_T_max_sfirst[OF _ this, of 1]
    obtain N where "?Pf N t < 1" by auto
    with Pf_mono[of N] show "\<forall>\<^sub>F n in sequentially. ?Pf n t < 1"
      by (auto simp: eventually_sequentially intro: le_less_trans)
  qed simp
  then obtain n where "\<And>t. (s, t) \<in> acc_on (-H) \<Longrightarrow> ?Pf n t < 1"
    by (auto simp: eventually_sequentially)
  moreover def d \<equiv> "Max (?Pf n ` acc_on (-H) `` {s})"
  ultimately have d: "0 \<le> d" "d < 1" "\<And>t. (s, t) \<in> acc_on (-H) \<Longrightarrow> ?Pf (Suc n) t \<le> d"
    using Pf_mono[of n "Suc n"] by (auto simp: Max_ge_iff measure_nonneg)

  let ?F = "\<lambda>F \<omega>. if shd \<omega> \<in> H then 0 else 0 \<squnion> F (stl \<omega>) + 1 :: ereal"
  have "sup_continuous ?F"
    by (intro order_continuous_intros) simp_all
  then have "mono ?F"
    by (rule sup_continuous_mono)
  have lfp_nonneg[simp]: "\<And>\<omega>. 0 \<le> lfp ?F \<omega>"
    by (subst lfp_unfold[OF \<open>mono ?F\<close>]) auto

  let ?I = "\<lambda>F s. \<integral>\<^sup>+t. (if t \<in> H then 0 else 0 \<squnion> F t + 1) \<partial>K s"
  have "sup_continuous ?I"
    by (intro order_continuous_intros) auto
  then have "mono ?I"
    by (rule sup_continuous_mono)

  def p \<equiv> "Suc n / (1 - d)"
  have p: "p = Suc n + d * p"
    unfolding p_def using d(1,2) by (auto simp: field_simps)
  have "0 \<le> p"
    using d(1,2) by (auto simp: p_def)

  have "(\<integral>\<^sup>+ \<omega>. sfirst (HLD H) \<omega> \<partial>T s) = (\<integral>\<^sup>+ \<omega>. lfp ?F \<omega> \<partial>T s)"
  proof (intro nn_integral_cong_AE)
    show "AE x in T s. sfirst (HLD H) x = lfp ?F x"
      using until
    proof eventually_elim
      fix \<omega> assume "ev (HLD H) \<omega>" then show "sfirst (HLD H) \<omega> = lfp ?F \<omega>"
        by (induction rule: ev_induct_strong;
            subst lfp_unfold[OF \<open>mono ?F\<close>], simp add: HLD_iff[abs_def] ac_simps max_absorb2)
    qed
  qed
  also have "\<dots> = lfp (?I^^Suc n) s"
    unfolding lfp_funpow[OF \<open>mono ?I\<close>]
    by (subst nn_integral_T_lfp)
       (auto simp: nn_integral_add nn_integral_max_0 max_absorb2 nn_integral_nonneg intro!: order_continuous_intros)
  also have "lfp (?I^^Suc n) t \<le> p" if "(s, t) \<in> acc_on (-H)" for t
    using that
  proof (induction arbitrary: t rule: lfp_ordinal_induct[of "?I^^Suc n"])
    case (step S)
    have "(?I^^i) S t \<le> i + ?Pf i t * p" for i
      using step(3)
    proof (induction i arbitrary: t)
      case 0 then show ?case
        using T.prob_space step(1)
        by (auto simp add: zero_ereal_def[symmetric] not_H zero_enat_def[symmetric] one_ereal_def[symmetric])
    next
      case (Suc i)
      then have "t \<notin> H"
        by (auto simp: not_H)
      from Suc.prems have "\<And>t'. t' \<in> K t \<Longrightarrow> t' \<notin> H \<Longrightarrow> (s, t') \<in> acc_on (-H)"
        by (rule rtrancl_into_rtrancl) (insert Suc.prems, auto dest: not_H)
      then have "(?I ^^ Suc i) S t \<le> ?I (\<lambda>t. ereal i + ereal (?Pf i t) * p) t"
        by (auto simp: AE_measure_pmf_iff simp del: sfirst_eSuc space_T
                 intro!: nn_integral_mono_AE add_mono max.mono Suc)
      also have "\<dots> \<le> (\<integral>\<^sup>+ t. ereal (Suc i) + ereal \<P>(\<omega> in T t. enat i < sfirst (HLD H) (t ## \<omega>)) * p \<partial>K t)"
        by (intro nn_integral_mono)
           (auto simp: max_def measure_nonneg `0 \<le> p` one_ereal_def[symmetric] plus_ereal.simps[symmetric] field_simps
                 simp del: ereal_plus_1 plus_ereal.simps)
      also have "\<dots> \<le> Suc i + ereal (?Pf (Suc i) t) * p"
        unfolding T.emeasure_eq_measure[symmetric]
        by (subst (2) emeasure_Collect_T)
           (auto simp: \<open>t \<notin> H\<close> eSuc_enat[symmetric] \<open>0 \<le> p\<close> emeasure_nonneg nn_integral_add nn_integral_multc)
      finally show ?case by simp
    qed
    then have "(?I^^Suc n) S t \<le> ereal (Suc n + ?Pf (Suc n) t * p)" .
    also have "\<dots> \<le> p"
      using d step by (subst (2) p) (auto intro!: mult_right_mono \<open>0 \<le> p\<close>)
    finally show ?case .
  qed (auto simp: SUP_least intro!: mono_pow \<open>mono ?I\<close> simp del: funpow.simps)
  finally show ?thesis
    unfolding p_def by auto
qed

lemma nn_integral_sfirst_finite:
  assumes [simp]: "finite (acc_on (-H) `` {s})"
  assumes until: "AE \<omega> in T s. ev (HLD H) \<omega>"
  shows "(\<integral>\<^sup>+ \<omega>. sfirst (HLD H) (s ## \<omega>) \<partial>T s) \<noteq> \<infinity>"
proof cases
  assume "s \<notin> H" then show ?thesis
    using nn_integral_sfirst_finite'[of s H] until by (simp add: nn_integral_add)
qed (simp add: sfirst.simps)

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

lemma T_eq_bind: "T s = (measure_pmf (K s) \<bind> (\<lambda>t. distr (T t) S (op ## t)))"
  by (subst T_eq_T') (simp add: T'_def)

declare T_subprob[measurable]

lemma T_split:
  "T s = (T s \<bind> (\<lambda>\<omega>. distr (T ((s ## \<omega>) !! n)) S (\<lambda>\<omega>'. stake n \<omega> @- \<omega>')))"
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

  have "T s = (?K \<bind> (\<lambda>t. distr (T t) S (op ## t)))"
    by (rule T_eq_bind)
  also have "\<dots> = (?K \<bind> (\<lambda>t. distr (T t \<bind> (\<lambda>\<omega>. distr (T ((t ## \<omega>) !! n)) S (?m n \<omega>))) S (op ## t)))"
    unfolding Suc[symmetric] ..
  also have "\<dots> = (?K \<bind> (\<lambda>t. T t \<bind> (\<lambda>\<omega>. distr (distr (T ((t ## \<omega>) !! n)) S (?m n \<omega>)) S (op ## t))))"
    by (simp add: distr_bind[where K=S, OF measurable_distr2[where M=S]] space_stream_space)
  also have "\<dots> = (?K \<bind> (\<lambda>t. T t \<bind> (\<lambda>\<omega>. distr (T ((t ## \<omega>) !! n)) S (?m (Suc n) (t ## \<omega>)))))"
    by (simp add: distr_distr space_stream_space comp_def)
  also have "\<dots> = (?K \<bind> (\<lambda>t. distr (T t) S (op ## t) \<bind> (\<lambda>\<omega>. distr (T (\<omega> !! n)) S (?m (Suc n) \<omega>))))"
    by (simp add: space_stream_space bind_distr[OF _ measurable_distr2[where M=S]] del: stake.simps)
  also have "\<dots> = (T s \<bind> (\<lambda>\<omega>. distr (T (\<omega> !! n)) S (?m (Suc n) \<omega>)))"
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

lemma T_eq_bind': "T x = do { y \<leftarrow> measure_pmf (K x) ; \<omega> \<leftarrow> T y ; return S (y ## \<omega>) }"
  apply (subst T_eq_bind)
  apply (subst bind_return_distr[symmetric])
  apply (simp_all add: space_stream_space comp_def)
  done

lemma rT_eq_bind: "rT x = do { y \<leftarrow> measure_pmf (K x) ; \<omega> \<leftarrow> rT y ; return (rT x) (y ## \<omega>) }"
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

lemma snth_rT: "(\<lambda>x. x !! n) \<in> measurable (rT x) (count_space (acc `` {x}))"
proof -
  have "\<And>\<omega>. enabled x \<omega> \<Longrightarrow> (x, \<omega> !! n) \<in> acc"
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
  assumes M_eq: "\<And>x. M x = (measure_pmf (K x) \<bind> (\<lambda>s. distr (M s) S (op ## s)))"
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
  def \<Omega> \<equiv> "acc `` {x}"

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
    by (auto intro: countable_acc simp: \<Omega>_def)
  have x[simp]: "x \<in> \<Omega>"
    by (auto simp: \<Omega>_def)

  note streams_sets[measurable]

  { fix n y assume "y \<in> \<Omega>"
    then have "(x, y) \<in> acc" by (simp add: \<Omega>_def)
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
      by (cases "streams (acc `` {x}) \<in> sets S")
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
      by (subst sup_continuous_lfp)
         (auto simp add: sup_continuous_def) }
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
  qed (auto intro!: \<iota>_nonneg \<rho>_nonneg ereal_add_nonneg_nonneg order_continuous_intros)
  show ?thesis
    unfolding * by measurable
qed

lemma continuous_reward_until:
  "sup_continuous (\<lambda>F s \<omega>. if s \<in> X then 0 else \<rho> s + \<iota> s (shd \<omega>) + (0 \<squnion> (F (shd \<omega>) (stl \<omega>))))"
  by (intro \<iota>_nonneg \<rho>_nonneg ereal_add_nonneg_nonneg order_continuous_intros)
     (auto simp: sup_continuous_def)

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
      apply (rule continuous_reward_until[THEN sup_continuous_mono, of X])
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
  assumes [simp]: "finite (acc `` {s})" (is "finite (?R `` {s})")
  assumes \<rho>: "\<And>t. (s, t) \<in> acc_on (-H) \<Longrightarrow> \<rho> t < \<infinity>"
  assumes \<iota>: "\<And>t t'. (s, t) \<in> acc_on (-H) \<Longrightarrow> t' \<in> K t \<Longrightarrow> \<iota> t t' < \<infinity>"
  assumes ev: "AE \<omega> in T s. ev (HLD H) \<omega>"
  shows "(\<integral>\<^sup>+ \<omega>. reward_until H s \<omega> \<partial>T s) \<noteq> \<infinity>"
proof cases
  assume "s \<in> H" then show ?thesis
    by simp
next
  assume "s \<notin>  H"
  let ?L = "acc_on (-H)"
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
  K1: MC_syntax K1 + K2: MC_syntax K2 for K1 K2
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
    apply (auto intro!: K1.countable_acc K2.countable_acc)
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
  show "?B x = (measure_pmf (Kp x) \<bind> (\<lambda>s. distr (?B s) S (op ## s)))"
    unfolding x_eq
    apply (subst K1.T_eq_bind')
    apply (subst K2.T_eq_bind')
    apply (auto
         simp add: space_stream_space bind_assoc[where R=S and N=S] bind_return_distr[symmetric]
                   Kp_def T1K2.bind_rotate[where N=S] split_beta' set_pair_pmf space_subprob_algebra
                   bind_pair_pmf[of "case_prod M" for M, unfolded split, symmetric, where N=S] szip\<^sub>E_def
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
