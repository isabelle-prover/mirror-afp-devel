(* Author: Johannes Hölzl <hoelzl@in.tum.de> *)

section {* Discrete-Time Markov Chain *}

theory Discrete_Time_Markov_Chain
  imports
    Probability
    "~~/src/HOL/Library/Linear_Temporal_Logic_on_Streams"
    "../Coinductive/Coinductive_Nat"
begin

subsection {* Auxiliary Lemmas *}

lemma emeasure_single_in_space: "emeasure M {x} \<noteq> 0 \<Longrightarrow> x \<in> space M"
  using emeasure_notin_sets[of "{x}" M] by (auto dest: sets.sets_into_space)

declare alw.cases[elim]
declare ev.intros[intro]

lemma ev_induct_strong[consumes 1, case_names base step]:
  "ev \<phi> x \<Longrightarrow> (\<And>xs. \<phi> xs \<Longrightarrow> P xs) \<Longrightarrow> (\<And>xs. ev \<phi> (stl xs) \<Longrightarrow> \<not> \<phi> xs \<Longrightarrow> P (stl xs) \<Longrightarrow> P xs) \<Longrightarrow> P x"
  by (induct rule: ev.induct) auto

lemma alw_coinduct[consumes 1, case_names alw stl]:
  "X x \<Longrightarrow> (\<And>x. X x \<Longrightarrow> \<phi> x) \<Longrightarrow> (\<And>x. X x \<Longrightarrow> \<not> alw \<phi> (stl x) \<Longrightarrow> X (stl x)) \<Longrightarrow> alw \<phi> x"
  using alw.coinduct[of X x \<phi>] by auto

lemma streams_iff_snth: "s \<in> streams X \<longleftrightarrow> (\<forall>n. s !! n \<in> X)"
  by (force simp: streams_iff_sset sset_range)

definition "HLD s = holds (\<lambda>x. x \<in> s)"

abbreviation HLD_nxt (infixr "\<cdot>" 65) where
  "s \<cdot> P \<equiv> HLD s aand nxt P"

lemma HLD_iff: "HLD s \<omega> \<longleftrightarrow> shd \<omega> \<in> s"
  by (simp add: HLD_def)

lemma HLD_Stream[simp]: "HLD X (x ## \<omega>) \<longleftrightarrow> x \<in> X"
  by (simp add: HLD_iff)

lemma subprob_measurableD:
  assumes N: "N \<in> measurable M (subprob_algebra S)" and x: "x \<in> space M"
  shows "space (N x) = space S"
    and "sets (N x) = sets S"
    and "measurable (N x) K = measurable S K"
    and "measurable K (N x) = measurable K S"
  using measurable_space[OF N x]
  by (auto simp: space_subprob_algebra intro!: measurable_cong_sets dest: sets_eq_imp_space_eq)

lemma emeasure_le_0: "emeasure M A \<le> 0 \<longleftrightarrow> emeasure M A = 0"
  using emeasure_nonneg[of M A] by auto

lemma (in -) pmf_le_1: "pmf M x \<le> 1"
  by (simp add: pmf.rep_eq)

lemma (in -) measurable_measure_pmf[measurable]:
  "(\<lambda>x. measure_pmf (M x)) \<in> measurable (count_space UNIV) (subprob_algebra (count_space UNIV))"
  by (auto simp: space_subprob_algebra intro!: prob_space_imp_subprob_space) unfold_locales

lemma (in -) nn_integral_count_space_indicator:
  assumes "NO_MATCH (X::'a set) (UNIV::'a set)"
  shows "(\<integral>\<^sup>+x. f x \<partial>count_space X) = (\<integral>\<^sup>+x. f x * indicator X x \<partial>count_space UNIV)"
  by (simp add: nn_integral_restrict_space[symmetric] restrict_count_space)

lemma (in -) measure_eqI_countable:
  assumes [simp]: "sets M = UNIV" "sets N = UNIV"
  assumes ae: "AE x in M. x \<in> \<Omega>" "AE x in N. x \<in> \<Omega>" and [simp]: "countable \<Omega>"
  assumes eq: "\<And>x. x \<in> \<Omega> \<Longrightarrow> emeasure M {x} = emeasure N {x}"
  shows "M = N"
proof (rule measure_eqI)
  fix A
  have "emeasure N A = emeasure N {x\<in>\<Omega>. x \<in> A}"
    using ae by (intro emeasure_eq_AE) auto
  also have "\<dots> = (\<integral>\<^sup>+x. emeasure N {x} \<partial>count_space {x\<in>\<Omega>. x \<in> A})"
    by (intro emeasure_countable_singleton) auto
  also have "\<dots> = (\<integral>\<^sup>+x. emeasure M {x} \<partial>count_space {x\<in>\<Omega>. x \<in> A})"
    by (intro nn_integral_cong eq[symmetric]) auto
  also have "\<dots> = emeasure M {x\<in>\<Omega>. x \<in> A}"
    by (intro emeasure_countable_singleton[symmetric]) auto
  also have "\<dots> = emeasure M A"
    using ae by (intro emeasure_eq_AE) auto
  finally show "emeasure M A = emeasure N A" ..
qed simp



lemma (in -) integrable_real_mult_indicator:
  fixes f :: "'a \<Rightarrow> real"
  shows "A \<in> sets M \<Longrightarrow> integrable M f \<Longrightarrow> integrable M (\<lambda>x. f x * indicator A x)"
  using integrable_mult_indicator[of A M f] by (simp add: mult_ac)

lemma sets_UNIV [measurable (raw)]: "A \<in> sets (count_space UNIV)"
  by simp

lemma eSuc_Inf: "eSuc (Inf A) = Inf (eSuc ` A)"
proof -
  { assume "A \<noteq> {}"
    then obtain a where "a \<in> A" by blast
    then have "eSuc (LEAST a. a \<in> A) = (LEAST a. a \<in> eSuc ` A)"
    proof (rule LeastI2_wellorder)
      fix a assume "a \<in> A" and b: "\<forall>b. b \<in> A \<longrightarrow> a \<le> b"
      then have a: "eSuc a \<in> eSuc ` A"
        by auto
      then show "eSuc a = (LEAST a. a \<in> eSuc ` A)"
        by (rule LeastI2_wellorder) (metis (full_types) b a antisym eSuc_le_iff imageE)
    qed }
  then show ?thesis
    by (simp add: Inf_enat_def)
qed

lemma nn_integral_measurable_subprob_algebra2:
  assumes f[measurable]: "(\<lambda>(x, y). f x y) \<in> borel_measurable (M \<Otimes>\<^sub>M N)" and [simp]: "\<And>x y. 0 \<le> f x y"
  assumes N[measurable]: "L \<in> measurable M (subprob_algebra N)"
  shows "(\<lambda>x. integral\<^sup>N (L x) (f x)) \<in> borel_measurable M"
proof -
  have "(\<lambda>x. integral\<^sup>N (distr (L x) (M \<Otimes>\<^sub>M N) (\<lambda>y. (x, y))) (\<lambda>(x, y). f x y)) \<in> borel_measurable M"
    apply (rule measurable_compose[OF _ nn_integral_measurable_subprob_algebra])
    apply (rule measurable_distr2)
    apply measurable
    apply (simp split: prod.split)
    done
  then show "(\<lambda>x. integral\<^sup>N (L x) (f x)) \<in> borel_measurable M"
    apply (rule measurable_cong[THEN iffD1, rotated])
    apply (subst nn_integral_distr)
    apply measurable
    apply (rule subprob_measurableD(2)[OF N], assumption)
    apply measurable
    done
qed

lemma emeasure_measurable_subprob_algebra2:
  assumes A[measurable]: "(SIGMA x:space M. A x) \<in> sets (M \<Otimes>\<^sub>M N)"
  assumes L[measurable]: "L \<in> measurable M (subprob_algebra N)"
  shows "(\<lambda>x. emeasure (L x) (A x)) \<in> borel_measurable M"
proof -
  { fix x assume "x \<in> space M"
    then have "Pair x -` Sigma (space M) A = A x"
      by auto
    with sets_Pair1[OF A, of x] have "A x \<in> sets N"
      by auto }
  note ** = this

  have *: "\<And>x. fst x \<in> space M \<Longrightarrow> snd x \<in> A (fst x) \<longleftrightarrow> x \<in> (SIGMA x:space M. A x)"
    by (auto simp: fun_eq_iff)
  have "(\<lambda>(x, y). indicator (A x) y::ereal) \<in> borel_measurable (M \<Otimes>\<^sub>M N)"
    apply measurable
    apply (subst measurable_cong)
    apply (rule *)
    apply (auto simp: space_pair_measure)
    done
  then have "(\<lambda>x. integral\<^sup>N (L x) (indicator (A x))) \<in> borel_measurable M"
    by (intro nn_integral_measurable_subprob_algebra2[where N=N] ereal_indicator_nonneg L)
  then show "(\<lambda>x. emeasure (L x) (A x)) \<in> borel_measurable M"
    apply (rule measurable_cong[THEN iffD1, rotated])
    apply (rule nn_integral_indicator)
    apply (simp add: subprob_measurableD[OF L] **)
    done
qed

lemma measure_measurable_subprob_algebra2:
  assumes A[measurable]: "(SIGMA x:space M. A x) \<in> sets (M \<Otimes>\<^sub>M N)"
  assumes L[measurable]: "L \<in> measurable M (subprob_algebra N)"
  shows "(\<lambda>x. measure (L x) (A x)) \<in> borel_measurable M"
  unfolding measure_def
  by (intro borel_measurable_real_of_ereal emeasure_measurable_subprob_algebra2[OF assms])

lemma distr_bind:
  assumes N: "N \<in> measurable M (subprob_algebra K)" "space M \<noteq> {}"
  assumes f: "f \<in> measurable K R"
  shows "distr (M \<guillemotright>= N) R f = (M \<guillemotright>= (\<lambda>x. distr (N x) R f))"
  unfolding bind_nonempty''[OF N]
  apply (subst bind_nonempty''[OF measurable_compose[OF N(1) measurable_distr] N(2)])
  apply (rule f)
  apply (simp add: join_distr_distr[OF _ f, symmetric])
  apply (subst distr_distr[OF measurable_distr, OF f N(1)])
  apply (simp add: comp_def)
  done

lemma bind_distr:
  assumes f[measurable]: "f \<in> measurable M X"
  assumes N[measurable]: "N \<in> measurable X (subprob_algebra K)" and "space M \<noteq> {}"
  shows "(distr M X f \<guillemotright>= N) = (M \<guillemotright>= (\<lambda>x. N (f x)))"
proof -
  have "space X \<noteq> {}" "space M \<noteq> {}"
    using `space M \<noteq> {}` f[THEN measurable_space] by auto
  then show ?thesis
    by (simp add: bind_nonempty''[where N=K] distr_distr comp_def)
qed

lemma measurable_shift[measurable]: 
  assumes f: "f \<in> measurable N (stream_space M)"
  assumes [measurable]: "g \<in> measurable N (stream_space M)"
  shows "(\<lambda>x. stake n (f x) @- g x) \<in> measurable N (stream_space M)"
  using f by (induction n arbitrary: f) simp_all

inductive ev_at :: "('a stream \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> 'a stream \<Rightarrow> bool" for P :: "'a stream \<Rightarrow> bool" where
  base: "P \<omega> \<Longrightarrow> ev_at P 0 \<omega>"
| step:"\<not> P \<omega> \<Longrightarrow> ev_at P n (stl \<omega>) \<Longrightarrow> ev_at P (Suc n) \<omega>"

inductive_simps ev_at_0[simp]: "ev_at P 0 \<omega>"
inductive_simps ev_at_Suc[simp]: "ev_at P (Suc n) \<omega>"

lemma ev_at_imp_snth: "ev_at P n \<omega> \<Longrightarrow> P (sdrop n \<omega>)"
  by (induction n arbitrary: \<omega>) auto

lemma ev_at_HLD_imp_snth: "ev_at (HLD X) n \<omega> \<Longrightarrow> \<omega> !! n \<in> X"
  by (auto dest!: ev_at_imp_snth simp: HLD_iff)

lemma ev_at_HLD_single_imp_snth: "ev_at (HLD {x}) n \<omega> \<Longrightarrow> \<omega> !! n = x"
  by (drule ev_at_HLD_imp_snth) simp

lemma ev_at_unique: "ev_at P n \<omega> \<Longrightarrow> ev_at P m \<omega> \<Longrightarrow> n = m"
proof (induction arbitrary: m rule: ev_at.induct)
  case (base \<omega>) then show ?case
    by (simp add: ev_at.simps[of _ _ \<omega>])
next
  case (step \<omega> n) from step.prems step.hyps step.IH[of "m - 1"] show ?case
    by (auto simp add: ev_at.simps[of _ _ \<omega>])
qed

lemma ev_iff_ev_at: "ev P \<omega> \<longleftrightarrow> (\<exists>n. ev_at P n \<omega>)"
proof
  assume "ev P \<omega>" then show "\<exists>n. ev_at P n \<omega>"
    by (induction rule: ev_induct_strong) (auto intro: ev_at.intros)
next
  assume "\<exists>n. ev_at P n \<omega>"
  then obtain n where "ev_at P n \<omega>"
    by auto
  then show "ev P \<omega>"
    by induction auto
qed

lemma ev_iff_ev_at_unqiue: "ev P \<omega> \<longleftrightarrow> (\<exists>!n. ev_at P n \<omega>)"
  by (auto intro: ev_at_unique simp: ev_iff_ev_at)

lemma measurable_ev_at[measurable]:
  assumes [measurable]: "Measurable.pred (stream_space M) P"
  shows "Measurable.pred (stream_space M) (ev_at P n)"
  by (induction n) auto

lemma pred_stream_const1[measurable (raw)]:
  "f \<in> measurable M (count_space UNIV) \<Longrightarrow> Measurable.pred M (\<lambda>x. f x = c)"
  by (intro pred_eq_const1[where N="count_space UNIV"]) (auto )

lemma pred_stream_const2[measurable (raw)]:
  "f \<in> measurable M (count_space UNIV) \<Longrightarrow> Measurable.pred M (\<lambda>x. c = f x)"
  by (intro pred_eq_const2[where N="count_space UNIV"]) (auto )

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
    assume "infinite A"
    have [simp]: "(\<Squnion>a\<in>A. ereal_of_enat a) = \<top>"
      unfolding SUP_eq_top_iff
    proof safe
      fix x :: ereal assume "x < \<top>"
      then obtain n :: nat where "x < n"
        using less_PInf_Ex_of_nat top_ereal_def by auto
      obtain a where "a \<in> A - enat ` {.. n}"
        by (metis `infinite A` all_not_in_conv finite_Diff2 finite_atMost finite_imageI infinite_imp_nonempty)
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

lemma alw_HLD_iff_streams: "alw (HLD X) \<omega> \<longleftrightarrow> \<omega> \<in> streams X"
proof
  assume "alw (HLD X) \<omega>" then show "\<omega> \<in> streams X"
  proof (coinduction arbitrary: \<omega>)
    case (streams \<omega>) then show ?case by (cases \<omega>) auto
  qed
next
  assume "\<omega> \<in> streams X" then show "alw (HLD X) \<omega>"
  proof (coinduction arbitrary: \<omega>)
    case (alw \<omega>) then show ?case by (cases \<omega>) auto
  qed
qed

lemma not_HLD: "not (HLD X) = HLD (- X)"
  by (auto simp: HLD_iff)

lemma power_series_tendsto_at_left:
  assumes nonneg: "\<And>i. 0 \<le> f i" and summable: "\<And>z. 0 \<le> z \<Longrightarrow> z < 1 \<Longrightarrow> summable (\<lambda>n. f n * z^n)"
  shows "((\<lambda>z. ereal (\<Sum>n. f n * z^n)) ---> (\<Sum>n. ereal (f n))) (at_left (1::real))"
proof (intro tendsto_at_left_sequentially)
  show "0 < (1::real)" by simp
  fix S :: "nat \<Rightarrow> real" assume S: "\<And>n. S n < 1" "\<And>n. 0 < S n" "S ----> 1" "incseq S"
  then have S_nonneg: "\<And>i. 0 \<le> S i" by (auto intro: less_imp_le)

  have "(\<lambda>i. (\<integral>\<^sup>+n. f n * S i^n \<partial>count_space UNIV)) ----> (\<integral>\<^sup>+n. ereal (f n) \<partial>count_space UNIV)"
  proof (rule nn_integral_LIMSEQ)
    show "incseq (\<lambda>i n. ereal (f n * S i^n))"
      using S by (auto intro!: mult_mono power_mono nonneg simp: incseq_def le_fun_def less_imp_le)
    fix n have "(\<lambda>i. ereal (f n * S i^n)) ----> ereal (f n * 1^n)"
      by (intro tendsto_intros lim_ereal[THEN iffD2] S)
    then show "(\<lambda>i. ereal (f n * S i^n)) ----> ereal (f n)"
      by simp
  qed (auto simp: S_nonneg intro!: mult_nonneg_nonneg nonneg)
  also have "(\<lambda>i. (\<integral>\<^sup>+n. f n * S i^n \<partial>count_space UNIV)) = (\<lambda>i. \<Sum>n. f n * S i^n)"
    by (subst nn_integral_count_space_nat)
       (intro ext suminf_ereal mult_nonneg_nonneg nonneg S_nonneg ereal_less_eq(5)[THEN iffD2]
              zero_le_power suminf_ereal_finite summable S)+
  also have "(\<integral>\<^sup>+n. ereal (f n) \<partial>count_space UNIV) = (\<Sum>n. ereal (f n))"
    by (simp add: nn_integral_count_space_nat nonneg)
  finally show "(\<lambda>n. ereal (\<Sum>na. f na * S n ^ na)) ----> (\<Sum>n. ereal (f n))" .
qed

lemma ereal_right_mult_cong: 
  fixes a b c d :: ereal
  shows "c = d \<Longrightarrow> (d \<noteq> 0 \<Longrightarrow> a = b) \<Longrightarrow> c * a = d * b"
  by (cases "d = 0") simp_all

lemma summable_power_series:
  fixes z :: real
  assumes le_1: "\<And>i. f i \<le> 1" and nonneg: "\<And>i. 0 \<le> f i" and z: "0 \<le> z" "z < 1"
  shows "summable (\<lambda>i. f i * z^i)"
proof (rule summable_comparison_test[OF _ summable_geometric])
  show "norm z < 1" using z by (auto simp: less_imp_le)
  show "\<And>n. \<exists>N. \<forall>na\<ge>N. norm (f na * z ^ na) \<le> z ^ na"
    using z by (auto intro!: exI[of _ 0] mult_left_le_one_le simp: abs_mult nonneg power_abs less_imp_le le_1)
qed

(* very special *)
lemma eventually_at_left_1: "(\<And>z::real. 0 < z \<Longrightarrow> z < 1 \<Longrightarrow> P z) \<Longrightarrow> eventually P (at_left 1)"
  by (subst eventually_at_left[of 0]) (auto intro: exI[of _ 0])

lemma (in complete_lattice) Inf_eq:
  "(\<And>a. a \<in> A \<Longrightarrow> \<exists>b\<in>B. b \<le> a) \<Longrightarrow> (\<And>b. b \<in> B \<Longrightarrow> \<exists>a\<in>A. a \<le> b) \<Longrightarrow>  Inf A = Inf B"
  by (intro antisym Inf_greatest) (blast intro: Inf_lower2 dest: assms)+

lemma (in subprob_space) measure_le_1: "measure M X \<le> 1"
  using subprob_measure_le_1[of X] by (simp add: emeasure_eq_measure)

lemma (in subprob_space) measure_bind:
  assumes f: "f \<in> measurable M (subprob_algebra N)" and X: "X \<in> sets N"
  shows "measure (M \<guillemotright>= f) X = \<integral>x. measure (f x) X \<partial>M"
proof -
  interpret Mf: subprob_space "M \<guillemotright>= f"
    by (rule subprob_space_bind[OF _ f]) unfold_locales

  { fix x assume "x \<in> space M"
    from f[THEN measurable_space, OF this] interpret subprob_space "f x"
      by (simp add: space_subprob_algebra)
    have "emeasure (f x) X = ereal (measure (f x) X)" "measure (f x) X \<le> 1"
      by (auto simp: emeasure_eq_measure measure_le_1) }
  note this[simp]

  have "emeasure (M \<guillemotright>= f) X = \<integral>\<^sup>+x. emeasure (f x) X \<partial>M"
    using subprob_not_empty f X by (rule emeasure_bind)
  also have "\<dots> = \<integral>\<^sup>+x. ereal (measure (f x) X) \<partial>M"
    by (intro nn_integral_cong) simp
  also have "\<dots> = \<integral>x. measure (f x) X \<partial>M"
    by (intro nn_integral_eq_integral integrable_const_bound[where B=1]
              measure_measurable_subprob_algebra2[OF _ f] pair_measureI X)
       (auto simp: measure_nonneg)
  finally show ?thesis
    by (simp add: Mf.emeasure_eq_measure)
qed

lemma subprob_space_return: 
  assumes "space M \<noteq> {}" shows "subprob_space (return M x)"
proof
  show "emeasure (return M x) (space (return M x)) \<le> 1"
    by (subst emeasure_return) (auto split: split_indicator)
qed (simp, fact)

lemma measure_return: assumes X: "X \<in> sets M" shows "measure (return M x) X = indicator X x"
  unfolding measure_def emeasure_return[OF X, of x] by (simp split: split_indicator)

(* generic *)

lemma one_not_le_zero_ereal[simp]: "\<not> (1 \<le> (0::ereal))"
  by (simp add: one_ereal_def zero_ereal_def)

lemma disjCI2: "(\<not> Q \<Longrightarrow> P) \<Longrightarrow> Q \<or> P"
  by blast

lemma mult_left_le:
  "(c::_::linordered_semidom) \<le> 1 \<Longrightarrow> 0 \<le> a \<Longrightarrow> a * c \<le> a"
  using mult_left_mono[of c 1 a] by simp

lemma mult_le_one: 
  "a \<le> (1::_::linordered_semidom) \<Longrightarrow> 0 \<le> b \<Longrightarrow> b \<le> 1 \<Longrightarrow> a * b \<le> 1"
  using mult_mono[of a 1 b 1] by simp

lemma Lim_within_LIMSEQ:
  fixes a :: "'a::first_countable_topology"
  assumes "\<forall>S. (\<forall>n. S n \<noteq> a \<and> S n \<in> T) \<and> S ----> a \<longrightarrow> (\<lambda>n. X (S n)) ----> L"
  shows "(X ---> L) (at a within T)"
  using assms unfolding tendsto_def [where l=L]
  by (simp add: sequentially_imp_eventually_within)


lemma (in -) indicator_eq_0_iff: "indicator A x = (0::'a::zero_neq_one) \<longleftrightarrow> x \<notin> A"
  by (auto split: split_indicator)

lemma (in -) inverse_nonneg_iff: "0 \<le> inverse (x :: ereal) \<longleftrightarrow> 0 \<le> x \<or> x = -\<infinity>"
  by (cases x) auto

lemma ereal_of_enat_eSuc[simp]: "ereal_of_enat (eSuc x) = 1 + ereal_of_enat x"
  by (cases x) (auto simp: eSuc_enat)

lemma emeasure_measure_pmf_finite:
  "finite S \<Longrightarrow> emeasure (measure_pmf M) S = (\<Sum>s\<in>S. pmf M s)"
  by (subst emeasure_eq_setsum_singleton) (auto simp: emeasure_pmf_single)

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

lemma countable_reachable: "countable ((SIGMA s:UNIV. set_pmf (K s))\<^sup>* `` {s})"
  by (auto intro!: countable_rtrancl countable_set_pmf simp: Sigma_Image)

lemma measurable_compose_countable':
  assumes f: "\<And>i. i \<in> I \<Longrightarrow> (\<lambda>x. f i x) \<in> measurable M N"
  and g: "g \<in> measurable M (count_space I)" and I: "countable I"
  shows "(\<lambda>x. f (g x) x) \<in> measurable M N"
  unfolding measurable_def
proof safe
  fix x assume "x \<in> space M" then show "f (g x) x \<in> space N"
    using measurable_space[OF f] g[THEN measurable_space] by auto
next
  fix A assume A: "A \<in> sets N"
  have "(\<lambda>x. f (g x) x) -` A \<inter> space M = (\<Union>i\<in>I. (g -` {i} \<inter> space M) \<inter> (f i -` A \<inter> space M))"
    using measurable_space[OF g] by auto
  also have "\<dots> \<in> sets M" using f[THEN measurable_sets, OF _ A] g[THEN measurable_sets]
    by (auto intro!: sets.countable_UN' measurable_sets I)
  finally show "(\<lambda>x. f (g x) x) -` A \<inter> space M \<in> sets M" .
qed

lemma mult_indicator_cong: 
  fixes f g :: "'a \<Rightarrow> ereal"
  shows "(x \<in> A \<Longrightarrow> f x = g x) \<Longrightarrow> f x * indicator A x = g x * indicator A x"
  by (simp split: split_indicator)

lemma emeasure_Collect_eq_AE:
  "AE x in M. P x \<longleftrightarrow> Q x \<Longrightarrow> Measurable.pred M Q \<Longrightarrow> Measurable.pred M P \<Longrightarrow>
   emeasure M {x\<in>space M. P x} = emeasure M {x\<in>space M. Q x}"
   by (intro emeasure_eq_AE) auto

lemma measurable_lfp[consumes 1, case_names continuity step]:
  assumes "P M"
  assumes "Order_Continuity.continuous F"
  assumes *: "\<And>M A. P M \<Longrightarrow> (\<And>N. P N \<Longrightarrow> Measurable.pred N A) \<Longrightarrow> Measurable.pred M (F A)"
  shows "Measurable.pred M (lfp F)"
proof -
  { fix i from `P M` have "Measurable.pred M (\<lambda>x. (F ^^ i) (\<lambda>x. False) x)"
      by (induct i arbitrary: M) (auto intro!: *) }
  then have "Measurable.pred M (\<lambda>x. \<exists>i. (F ^^ i) (\<lambda>x. False) x)"
    by measurable
  also have "(\<lambda>x. \<exists>i. (F ^^ i) (\<lambda>x. False) x) = (SUP i. (F ^^ i) bot)"
    by (auto simp add: bot_fun_def)
  also have "\<dots> = lfp F"
    by (rule continuous_lfp[symmetric]) fact
  finally show ?thesis .
qed

lemma measurable_gfp[consumes 1, case_names continuity step]:
  assumes "P M"
  assumes "Order_Continuity.down_continuous F"
  assumes *: "\<And>M A. P M \<Longrightarrow> (\<And>N. P N \<Longrightarrow> Measurable.pred N A) \<Longrightarrow> Measurable.pred M (F A)"
  shows "Measurable.pred M (gfp F)"
proof -
  { fix i from `P M` have "Measurable.pred M (\<lambda>x. (F ^^ i) (\<lambda>x. True) x)"
      by (induct i arbitrary: M) (auto intro!: *) }
  then have "Measurable.pred M (\<lambda>x. \<forall>i. (F ^^ i) (\<lambda>x. True) x)"
    by measurable
  also have "(\<lambda>x. \<forall>i. (F ^^ i) (\<lambda>x. True) x) = (INF i. (F ^^ i) top)"
    by (auto simp add: top_fun_def)
  also have "\<dots> = gfp F"
    by (rule down_continuous_gfp[symmetric]) fact
  finally show ?thesis .
qed

lemma measurable_lfp2[consumes 1, case_names continuity step]:
  assumes "P M s"
  assumes "Order_Continuity.continuous F"
  assumes *: "\<And>M A s. P M s \<Longrightarrow> (\<And>N t. P N t \<Longrightarrow> Measurable.pred N (A t)) \<Longrightarrow> Measurable.pred M (F A s)"
  shows "Measurable.pred M (lfp F s)"
proof -
  { fix i from `P M s` have "Measurable.pred M (\<lambda>x. (F ^^ i) (\<lambda>t x. False) s x)"
      by (induct i arbitrary: M s) (auto intro!: *) }
  then have "Measurable.pred M (\<lambda>x. \<exists>i. (F ^^ i) (\<lambda>t x. False) s x)"
    by measurable
  also have "(\<lambda>x. \<exists>i. (F ^^ i) (\<lambda>t x. False) s x) = (SUP i. (F ^^ i) bot) s"
    by (auto simp add: bot_fun_def)
  also have "(SUP i. (F ^^ i) bot) = lfp F"
    by (rule continuous_lfp[symmetric]) fact
  finally show ?thesis .
qed

lemma measurable_gfp2[consumes 1, case_names continuity step]:
  assumes "P M s"
  assumes "Order_Continuity.down_continuous F"
  assumes *: "\<And>M A s. P M s \<Longrightarrow> (\<And>N t. P N t \<Longrightarrow> Measurable.pred N (A t)) \<Longrightarrow> Measurable.pred M (F A s)"
  shows "Measurable.pred M (gfp F s)"
proof -
  { fix i from `P M s` have "Measurable.pred M (\<lambda>x. (F ^^ i) (\<lambda>t x. True) s x)"
      by (induct i arbitrary: M s) (auto intro!: *) }
  then have "Measurable.pred M (\<lambda>x. \<forall>i. (F ^^ i) (\<lambda>t x. True) s x)"
    by measurable
  also have "(\<lambda>x. \<forall>i. (F ^^ i) (\<lambda>t x. True) s x) = (INF i. (F ^^ i) top) s"
    by (auto simp add: top_fun_def)
  also have "(INF i. (F ^^ i) top) = gfp F"
    by (rule down_continuous_gfp[symmetric]) fact
  finally show ?thesis .
qed

lemma measurable_enat_coinduct:
  fixes f :: "'a \<Rightarrow> enat"
  assumes "R f"
  assumes *: "\<And>f. R f \<Longrightarrow> \<exists>g h i P. R g \<and> f = (\<lambda>x. if P x then h x else eSuc (g (i x))) \<and> 
    Measurable.pred M P \<and>
    i \<in> measurable M M \<and>
    h \<in> measurable M (count_space UNIV)"
  shows "f \<in> measurable M (count_space UNIV)"
proof (simp add: measurable_count_space_eq2_countable, rule )
  fix a :: enat
  have "f -` {a} \<inter> space M = {x\<in>space M. f x = a}"
    by auto
  { fix i :: nat
    from `R f` have "Measurable.pred M (\<lambda>x. f x = enat i)"
    proof (induction i arbitrary: f)
      case 0
      from *[OF this] obtain g h i P
        where f: "f = (\<lambda>x. if P x then h x else eSuc (g (i x)))" and
          [measurable]: "Measurable.pred M P" "i \<in> measurable M M" "h \<in> measurable M (count_space UNIV)"
        by auto
      have "Measurable.pred M (\<lambda>x. P x \<and> h x = 0)"
        by measurable
      also have "(\<lambda>x. P x \<and> h x = 0) = (\<lambda>x. f x = enat 0)"
        by (auto simp: f zero_enat_def[symmetric])
      finally show ?case .
    next
      case (Suc n)
      from *[OF Suc.prems] obtain g h i P
        where f: "f = (\<lambda>x. if P x then h x else eSuc (g (i x)))" and "R g" and
          M[measurable]: "Measurable.pred M P" "i \<in> measurable M M" "h \<in> measurable M (count_space UNIV)"
        by auto
      have "(\<lambda>x. f x = enat (Suc n)) =
        (\<lambda>x. (P x \<longrightarrow> h x = enat (Suc n)) \<and> (\<not> P x \<longrightarrow> g (i x) = enat n))"
        by (auto simp: f zero_enat_def[symmetric] eSuc_enat[symmetric])
      also have "Measurable.pred M \<dots>"
        by (intro pred_intros_logic measurable_compose[OF M(2)] Suc `R g`) measurable
      finally show ?case .
    qed
    then have "f -` {enat i} \<inter> space M \<in> sets M"
      by (simp add: pred_def Int_def conj_commute) }
  note fin = this
  show "f -` {a} \<inter> space M \<in> sets M"
  proof (cases a)
    case infinity
    then have "f -` {a} \<inter> space M = space M - (\<Union>n. f -` {enat n} \<inter> space M)"
      by auto
    also have "\<dots> \<in> sets M"
      by (intro sets.Diff sets.top sets.Un sets.countable_UN) (auto intro!: fin)
    finally show ?thesis .
  qed (simp add: fin)
qed

lemma measurable_alw[measurable]:
  "Measurable.pred (stream_space M) P \<Longrightarrow> Measurable.pred (stream_space M) (alw P)"
  unfolding alw_def
  by (coinduction rule: measurable_gfp) (auto simp: Order_Continuity.down_continuous_def)

lemma measurable_ev[measurable]:
  "Measurable.pred (stream_space M) P \<Longrightarrow> Measurable.pred (stream_space M) (ev P)"
  unfolding ev_def
  by (coinduction rule: measurable_lfp) (auto simp: Order_Continuity.continuous_def)

lemma measurable_holds [measurable]: "Measurable.pred M P \<Longrightarrow> Measurable.pred (stream_space M) (holds P)"
  unfolding holds.simps[abs_def]
  by (rule measurable_compose[OF measurable_shd]) simp

lemma not_alw_iff: "\<not> (alw P \<omega>) \<longleftrightarrow> ev (not P) \<omega>"
  using not_alw[of P] by (simp add: fun_eq_iff)

lemma not_ev_iff: "\<not> (ev P \<omega>) \<longleftrightarrow> alw (not P) \<omega>"
  using not_alw_iff[of "not P" \<omega>, symmetric]  by simp

lemma streamsE: "s \<in> streams A \<Longrightarrow> (shd s \<in> A \<Longrightarrow> stl s \<in> streams A \<Longrightarrow> P) \<Longrightarrow> P"
  by (erule streams.cases) simp_all

lemma Stream_image: "x ## y \<in> (op ## x') ` Y \<longleftrightarrow> x = x' \<and> y \<in> Y"
  by auto

lemma ev_Stream: "ev P (x ## s) \<longleftrightarrow> P (x ## s) \<or> ev P s"
  by (auto elim: ev.cases)

lemma alw_ev_imp_ev_alw:
  assumes "alw (ev P) \<omega>" shows "ev (P aand alw (ev P)) \<omega>"
proof -
  have "ev P \<omega>" using assms by auto
  from this assms show ?thesis
    by induct auto
qed

lemma ev_False: "ev (\<lambda>x. False) \<omega> \<longleftrightarrow> False"
proof
  assume "ev (\<lambda>x. False) \<omega>" then show False
    by induct auto
qed auto

lemma alw_False: "alw (\<lambda>x. False) \<omega> \<longleftrightarrow> False"
  by auto

lemma ev_iff_sdrop: "ev P \<omega> \<longleftrightarrow> (\<exists>m. P (sdrop m \<omega>))"
proof safe
  assume "ev P \<omega>" then show "\<exists>m. P (sdrop m \<omega>)"
    by (induct rule: ev_induct_strong) (auto intro: exI[of _ 0] exI[of _ "Suc n" for n])
next
  fix m assume "P (sdrop m \<omega>)" then show "ev P \<omega>"
    by (induct m arbitrary: \<omega>) auto
qed

lemma alw_iff_sdrop: "alw P \<omega> \<longleftrightarrow> (\<forall>m. P (sdrop m \<omega>))"
proof safe
  fix m assume "alw P \<omega>" then show "P (sdrop m \<omega>)"
    by (induct m arbitrary: \<omega>) auto
next
  assume "\<forall>m. P (sdrop m \<omega>)" then show "alw P \<omega>"
    by (coinduction arbitrary: \<omega>) (auto elim: allE[of _ 0] allE[of _ "Suc n" for n])
qed

lemma infinite_iff_alw_ev: "infinite {m. P (\<omega> !! m)} \<longleftrightarrow> alw (ev (holds P)) \<omega>"
  unfolding infinite_nat_iff_unbounded_le alw_iff_sdrop ev_iff_sdrop
  by simp (metis le_Suc_ex le_add1)

lemma alw_inv:
  assumes stl: "\<And>s. f (stl s) = stl (f s)"
  shows "alw P (f s) \<longleftrightarrow> alw (\<lambda>x. P (f x)) s"
proof
  assume "alw P (f s)" then show "alw (\<lambda>x. P (f x)) s"
    by (coinduction arbitrary: s rule: alw_coinduct)
       (auto simp: stl)
next
  assume "alw (\<lambda>x. P (f x)) s" then show "alw P (f s)"
    by (coinduction arbitrary: s rule: alw_coinduct) (auto simp: stl[symmetric])
qed

lemma ev_inv:
  assumes stl: "\<And>s. f (stl s) = stl (f s)"
  shows "ev P (f s) \<longleftrightarrow> ev (\<lambda>x. P (f x)) s"
proof
  assume "ev P (f s)" then show "ev (\<lambda>x. P (f x)) s"
    by (induction "f s" arbitrary: s) (auto simp: stl)
next
  assume "ev (\<lambda>x. P (f x)) s" then show "ev P (f s)"
    by induction (auto simp: stl[symmetric])
qed

lemma alw_smap: "alw P (smap f s) \<longleftrightarrow> alw (\<lambda>x. P (smap f x)) s"
  by (rule alw_inv) simp

lemma ev_smap: "ev P (smap f s) \<longleftrightarrow> ev (\<lambda>x. P (smap f x)) s"
  by (rule ev_inv) simp

lemma alw_cong:
  assumes P: "alw P \<omega>" and eq: "\<And>\<omega>. P \<omega> \<Longrightarrow> Q1 \<omega> \<longleftrightarrow> Q2 \<omega>"
  shows "alw Q1 \<omega> \<longleftrightarrow> alw Q2 \<omega>"
proof -
  from eq have "(alw P aand Q1) = (alw P aand Q2)" by auto
  then have "alw (alw P aand Q1) \<omega> = alw (alw P aand Q2) \<omega>" by auto
  with P show "alw Q1 \<omega> \<longleftrightarrow> alw Q2 \<omega>"
    by (simp add: alw_aand)
qed

lemma ev_cong:
  assumes P: "alw P \<omega>" and eq: "\<And>\<omega>. P \<omega> \<Longrightarrow> Q1 \<omega> \<longleftrightarrow> Q2 \<omega>"
  shows "ev Q1 \<omega> \<longleftrightarrow> ev Q2 \<omega>"
proof -
  from P have "alw (\<lambda>xs. Q1 xs \<longrightarrow> Q2 xs) \<omega>" by (rule alw_mono) (simp add: eq)
  moreover from P have "alw (\<lambda>xs. Q2 xs \<longrightarrow> Q1 xs) \<omega>" by (rule alw_mono) (simp add: eq)
  moreover note ev_alw_impl[of Q1 \<omega> Q2] ev_alw_impl[of Q2 \<omega> Q1]
  ultimately show "ev Q1 \<omega> \<longleftrightarrow> ev Q2 \<omega>"
    by auto
qed

lemma smap_ctr: "smap f s = x ## s' \<longleftrightarrow> f (shd s) = x \<and> smap f (stl s) = s'"
  by (cases s) simp

lemma alwD: "alw P x \<Longrightarrow> P x"
  by auto

lemma alw_alwD: "alw P \<omega> \<Longrightarrow> alw (alw P) \<omega>"
  by simp

lemma alw_ev_stl: "alw (ev P) (stl \<omega>) \<longleftrightarrow> alw (ev P) \<omega>"
  by (auto intro: alw.intros)

lemma holds_Stream: "holds P (x ## s) \<longleftrightarrow> P x"
  by simp

lemma holds_eq1[simp]: "holds (op = x) = HLD {x}"
  by rule (auto simp: HLD_iff)

lemma holds_eq2[simp]: "holds (\<lambda>y. y = x) = HLD {x}"
  by rule (auto simp: HLD_iff)

lemma not_holds_eq[simp]: "holds (- op = x) = not (HLD {x})"
  by rule (auto simp: HLD_iff)

lemma measurable_hld[measurable]: assumes [measurable]: "t \<in> sets M" shows "Measurable.pred (stream_space M) (HLD t)"
  unfolding HLD_def by measurable

partial_function (lfp) scount :: "'s set \<Rightarrow> 's stream \<Rightarrow> enat" where
  "scount X \<omega> = (if HLD X \<omega> then eSuc (scount X (stl \<omega>)) else scount X (stl \<omega>))"

lemma scount_simps:
  "HLD X \<omega> \<Longrightarrow> scount X \<omega> = eSuc (scount X (stl \<omega>))"
  "\<not> HLD X \<omega> \<Longrightarrow> scount X \<omega> = scount X (stl \<omega>)"
  using scount.simps[of X \<omega>] by auto

lemma scount_eq_0I: "alw (not (HLD X)) \<omega> \<Longrightarrow> scount X \<omega> = 0"
  by (induct arbitrary: \<omega> rule: scount.fixp_induct)
     (auto simp: bot_enat_def intro!: admissible_all admissible_imp admissible_eq_mcontI mcont_const)

lemma scount_eq_0D: "scount X \<omega> = 0 \<Longrightarrow> alw (not (HLD X)) \<omega>"
proof (induction rule: alw.coinduct)
  case (alw \<omega>) with scount.simps[of X \<omega>] show ?case
    by (simp split: split_if_asm)
qed

lemma scount_eq_0_iff: "scount X \<omega> = 0 \<longleftrightarrow> alw (not (HLD X)) \<omega>"
  by (metis scount_eq_0D scount_eq_0I)

lemma
  assumes "ev (alw (not (HLD X))) \<omega>"
  shows scount_eq_card: "scount X \<omega> = card {i. \<omega> !! i \<in> X}"
    and ev_alw_not_HLD_finite: "finite {i. \<omega> !! i \<in> X}"
  using assms
proof (induction \<omega>)
  case (step \<omega>)
  have eq: "{i. \<omega> !! i \<in> X} = (if HLD X \<omega> then {0} else {}) \<union> (Suc ` {i. stl \<omega> !! i \<in> X})"
    apply (intro set_eqI)
    apply (case_tac x)
    apply (auto simp: image_iff HLD_iff)
    done
  { case 1 show ?case
      using step unfolding eq by (auto simp: scount_simps card_image Zero_notin_Suc eSuc_enat) }
  { case 2 show ?case
      using step unfolding eq by auto }
next
   case (base \<omega>)
   then have [simp]: "{i. \<omega> !! i \<in> X} = {}"
     by (simp add: not_HLD alw_HLD_iff_streams streams_iff_snth)
   { case 1 show ?case using base by (simp add: scount_eq_0I enat_0) }
   { case 2 show ?case by simp }
qed

lemma scount_finite: "ev (alw (not (HLD X))) \<omega> \<Longrightarrow> scount X \<omega> < \<infinity>"
  using scount_eq_card[of X \<omega>] by auto

lemma scount_infinite: 
  "alw (ev (HLD X)) \<omega> \<Longrightarrow> scount X \<omega> = \<infinity>"
proof (coinduction arbitrary: \<omega> rule: enat_coinduct)
  case (Eq_enat \<omega>)
  then have "ev (HLD X) \<omega>" "alw (ev (HLD X)) \<omega>"
    by auto
  then show ?case
    by (induction rule: ev_induct_strong) (auto simp add: scount_simps)
qed

lemma scount_infinite_iff: "scount X \<omega> = \<infinity> \<longleftrightarrow> alw (ev (HLD X)) \<omega>"
  by (metis enat_ord_simps(4) not_alw_not scount_finite scount_infinite)

lemma scount_eq:
  "scount X \<omega> = (if alw (ev (HLD X)) \<omega> then \<infinity> else card {i. \<omega> !! i \<in> X})"
  by (auto simp: scount_infinite_iff scount_eq_card not_alw_iff not_ev_iff) 

lemma scount_eq_emeasure: "scount X \<omega> = emeasure (count_space UNIV) {i. \<omega> !! i \<in> X}"
proof cases
  assume "alw (ev (HLD X)) \<omega>"
  moreover then have "infinite {i. \<omega> !! i \<in> X}"
    using infinite_iff_alw_ev[of "\<lambda>x. x \<in> X" \<omega>] by (simp add: holds.simps[abs_def] HLD_iff[abs_def])
  ultimately show ?thesis
    by (simp add: scount_infinite_iff)
next
  assume "\<not> alw (ev (HLD X)) \<omega>"
  moreover then have "finite {i. \<omega> !! i \<in> X}"
    using infinite_iff_alw_ev[of "\<lambda>x. x \<in> X" \<omega>] by (simp add: holds.simps[abs_def] HLD_iff[abs_def])
  ultimately show ?thesis
    by (simp add: not_alw_iff not_ev_iff scount_eq_card)
qed

lemma measurable_scount[measurable]: 
  assumes [measurable]: "X \<in> sets M" shows "scount X \<in> measurable (stream_space M) (count_space UNIV)"
  unfolding scount_eq[abs_def] by measurable

text {* Strong until *}

inductive suntil (infix "suntil" 60) for \<phi> \<psi> where
  base: "\<psi> \<omega> \<Longrightarrow> (\<phi> suntil \<psi>) \<omega>"
| step: "\<phi> \<omega> \<Longrightarrow> (\<phi> suntil \<psi>) (stl \<omega>) \<Longrightarrow> (\<phi> suntil \<psi>) \<omega>"

inductive_simps suntil_Stream: "(\<phi> suntil \<psi>) (x ## s)"

lemma ev_suntil: "(\<phi> suntil \<psi>) \<omega> \<Longrightarrow> ev \<psi> \<omega>"
  by (induct rule: suntil.induct) (auto intro: ev.intros)

lemma suntil_inv:
  assumes stl: "\<And>s. f (stl s) = stl (f s)"
  shows "(P suntil Q) (f s) \<longleftrightarrow> ((\<lambda>x. P (f x)) suntil (\<lambda>x. Q (f x))) s"
proof
  assume "(P suntil Q) (f s)" then show "((\<lambda>x. P (f x)) suntil (\<lambda>x. Q (f x))) s"
    by (induction "f s" arbitrary: s) (auto simp: stl intro: suntil.intros)
next
  assume "((\<lambda>x. P (f x)) suntil (\<lambda>x. Q (f x))) s" then show "(P suntil Q) (f s)"
    by induction (auto simp: stl[symmetric] intro: suntil.intros)
qed

lemma suntil_smap: "(P suntil Q) (smap f s) \<longleftrightarrow> ((\<lambda>x. P (smap f x)) suntil (\<lambda>x. Q (smap f x))) s"
  by (rule suntil_inv) simp

lemma hld_smap: "HLD x (smap f s) = holds (\<lambda>y. f y \<in> x) s"
  by (simp add: HLD_def)

lemma suntil_mono:
  assumes eq: "\<And>\<omega>. P \<omega> \<Longrightarrow> Q1 \<omega> \<Longrightarrow> Q2 \<omega>" "\<And>\<omega>. P \<omega> \<Longrightarrow> R1 \<omega> \<Longrightarrow> R2 \<omega>"
  assumes *: "(Q1 suntil R1) \<omega>" "alw P \<omega>" shows "(Q2 suntil R2) \<omega>"
  using * by induct (auto intro: eq suntil.intros)

lemma suntil_cong:
  "alw P \<omega> \<Longrightarrow> (\<And>\<omega>. P \<omega> \<Longrightarrow> Q1 \<omega> \<longleftrightarrow> Q2 \<omega>) \<Longrightarrow> (\<And>\<omega>. P \<omega> \<Longrightarrow> R1 \<omega> \<longleftrightarrow> R2 \<omega>) \<Longrightarrow>
    (Q1 suntil R1) \<omega> \<longleftrightarrow> (Q2 suntil R2) \<omega>"
  using suntil_mono[of P Q1 Q2 R1 R2 \<omega>] suntil_mono[of P Q2 Q1 R2 R1 \<omega>] by auto

lemma ev_suntil_iff: "ev (P suntil Q) \<omega> \<longleftrightarrow> ev Q \<omega>"
proof
  assume "ev (P suntil Q) \<omega>" then show "ev Q \<omega>"
   by induct (auto dest: ev_suntil)
next
  assume "ev Q \<omega>" then show "ev (P suntil Q) \<omega>"
    by induct (auto intro: suntil.intros)
qed

lemma true_suntil: "((\<lambda>_. True) suntil P) = ev P"
  by (simp add: suntil_def ev_def)

lemma suntil_lfp: "(\<phi> suntil \<psi>) = lfp (\<lambda>P s. \<psi> s \<or> (\<phi> s \<and> P (stl s)))"
  by (simp add: suntil_def)

lemma sfilter_P[simp]: "P (shd s) \<Longrightarrow> sfilter P s = shd s ## sfilter P (stl s)"
  using sfilter_Stream[of P "shd s" "stl s"] by simp

lemma sfilter_not_P[simp]: "\<not> P (shd s) \<Longrightarrow> sfilter P s = sfilter P (stl s)"
  using sfilter_Stream[of P "shd s" "stl s"] by simp

lemma sfilter_eq: 
  assumes "ev (holds P) s"
  shows "sfilter P s = x ## s' \<longleftrightarrow>
    P x \<and> (not (holds P) suntil (HLD {x} aand nxt (\<lambda>s. sfilter P s = s'))) s"
  using assms
  by (induct rule: ev_induct_strong)
     (auto simp add: HLD_iff intro: suntil.intros elim: suntil.cases)

lemma sfilter_streams:
  "alw (ev (holds P)) \<omega> \<Longrightarrow> \<omega> \<in> streams A \<Longrightarrow> sfilter P \<omega> \<in> streams {x\<in>A. P x}"
proof (coinduction arbitrary: \<omega>)
  case (streams \<omega>)
  then have "ev (holds P) \<omega>" by blast
  from this streams show ?case
    by (induct rule: ev_induct_strong) (auto elim: streamsE)
qed

lemma alw_sfilter:
  assumes *: "alw (ev (holds P)) s"
  shows "alw Q (sfilter P s) \<longleftrightarrow> alw (\<lambda>x. Q (sfilter P x)) s"
proof
  assume "alw Q (sfilter P s)" with * show "alw (\<lambda>x. Q (sfilter P x)) s"
  proof (coinduction arbitrary: s rule: alw_coinduct)
    case (stl s) 
    then have "ev (holds P) s"
      by blast
    from this stl show ?case
      by (induct rule: ev_induct_strong) auto
  qed auto
next
  assume "alw (\<lambda>x. Q (sfilter P x)) s" with * show "alw Q (sfilter P s)"
  proof (coinduction arbitrary: s rule: alw_coinduct)
    case (stl s) 
    then have "ev (holds P) s"
      by blast
    from this stl show ?case
      by (induct rule: ev_induct_strong) auto
  qed auto
qed

lemma ev_sfilter:
  assumes *: "alw (ev (holds P)) s"
  shows "ev Q (sfilter P s) \<longleftrightarrow> ev (\<lambda>x. Q (sfilter P x)) s"
proof
  assume "ev Q (sfilter P s)" from this * show "ev (\<lambda>x. Q (sfilter P x)) s"
  proof (induction "sfilter P s" arbitrary: s rule: ev_induct_strong)
    case (step s)
    then have "ev (holds P) s"
      by blast
    from this step show ?case
      by (induct rule: ev_induct_strong) auto
  qed auto
next
  assume "ev (\<lambda>x. Q (sfilter P x)) s" then show "ev Q (sfilter P s)"
  proof (induction rule: ev_induct_strong)
    case (step s) then show ?case
      by (cases "P (shd s)") auto
  qed auto
qed

lemma holds_sfilter:
  assumes "ev (holds Q) s" shows "holds P (sfilter Q s) \<longleftrightarrow> (not (holds Q) suntil (holds (Q aand P))) s"
proof
  assume "holds P (sfilter Q s)" with assms show "(not (holds Q) suntil (holds (Q aand P))) s"
    by (induct rule: ev_induct_strong) (auto intro: suntil.intros)
next
  assume "(not (holds Q) suntil (holds (Q aand P))) s" then show "holds P (sfilter Q s)"
    by induct auto
qed

lemma funpow_mono:
  fixes f :: "'a \<Rightarrow> ('a::complete_lattice)"
  shows "mono f \<Longrightarrow> A \<le> B \<Longrightarrow> (f ^^ n) A \<le> (f ^^ n) B"
  by (induct n arbitrary: A B)
     (auto simp del: funpow.simps(2) simp add: funpow_Suc_right mono_def)

lemma funpow_increasing:
  fixes f :: "'a \<Rightarrow> ('a::complete_lattice)"
  shows "m \<le> n \<Longrightarrow> mono f \<Longrightarrow> (f ^^ n) \<top> \<le> (f ^^ m) \<top>"
  by (induct rule: inc_induct)
     (auto simp del: funpow.simps(2) simp add: funpow_Suc_right
           intro: order_trans[OF _ funpow_mono])

lemma div_eq_zero_iff: fixes a b :: nat shows "a div b = 0 \<longleftrightarrow> a < b \<or> b = 0"
  by (metis Divides.div_less Divides.div_positive div_by_0 gr0I less_numeral_extra(3) not_less)

lemma AE_ball_countable: 
  assumes [intro]: "countable X"
  shows "(AE x in M. \<forall>y\<in>X. P x y) \<longleftrightarrow> (\<forall>y\<in>X. AE x in M. P x y)"
proof
  assume "\<forall>y\<in>X. AE x in M. P x y"
  from this[unfolded eventually_ae_filter Bex_def, THEN bchoice]
  obtain N where N: "\<And>y. y \<in> X \<Longrightarrow> N y \<in> null_sets M" "\<And>y. y \<in> X \<Longrightarrow> {x\<in>space M. \<not> P x y} \<subseteq> N y"
    by auto
  have "{x\<in>space M. \<not> (\<forall>y\<in>X. P x y)} \<subseteq> (\<Union>y\<in>X. {x\<in>space M. \<not> P x y})"
    by auto
  also have "\<dots> \<subseteq> (\<Union>y\<in>X. N y)"
    using N by auto
  finally have "{x\<in>space M. \<not> (\<forall>y\<in>X. P x y)} \<subseteq> (\<Union>y\<in>X. N y)" .
  moreover from N have "(\<Union>y\<in>X. N y) \<in> null_sets M"
    by (intro null_sets_UN') auto
  ultimately show "AE x in M. \<forall>y\<in>X. P x y"
    unfolding eventually_ae_filter by auto
qed auto

lemma (in prob_space) ae_filter_bot: "ae_filter M \<noteq> bot"
  by (simp add: trivial_limit_def)

lemma measurable_nxt[measurable (raw)]:
  "Measurable.pred (stream_space M) P \<Longrightarrow> Measurable.pred (stream_space M) (nxt P)"
  unfolding nxt.simps[abs_def] by simp

lemma emeasure_lfp[consumes 1, case_names cont measurable]:
  assumes "P M"
  assumes cont: "Order_Continuity.continuous F"
  assumes *: "\<And>M A. P M \<Longrightarrow> (\<And>N. P N \<Longrightarrow> Measurable.pred N A) \<Longrightarrow> Measurable.pred M (F A)"
  shows "emeasure M {x\<in>space M. lfp F x} = (SUP i. emeasure M {x\<in>space M. (F ^^ i) (\<lambda>x. False) x})"
proof -
  have "emeasure M {x\<in>space M. lfp F x} = emeasure M (\<Union>i. {x\<in>space M. (F ^^ i) (\<lambda>x. False) x})"
    using continuous_lfp[OF cont] by (auto simp add: bot_fun_def intro!: arg_cong2[where f=emeasure])
  moreover { fix i from `P M` have "{x\<in>space M. (F ^^ i) (\<lambda>x. False) x} \<in> sets M"
    by (induct i arbitrary: M) (auto simp add: pred_def[symmetric] intro: *) }
  moreover have "incseq (\<lambda>i. {x\<in>space M. (F ^^ i) (\<lambda>x. False) x})"
  proof (rule incseq_SucI)
    fix i
    have "(F ^^ i) (\<lambda>x. False) \<le> (F ^^ (Suc i)) (\<lambda>x. False)"
    proof (induct i)
      case 0 show ?case by (simp add: le_fun_def)
    next
      case Suc thus ?case using monoD[OF continuous_mono[OF cont] Suc] by auto
    qed
    then show "{x \<in> space M. (F ^^ i) (\<lambda>x. False) x} \<subseteq> {x \<in> space M. (F ^^ Suc i) (\<lambda>x. False) x}"
      by auto
  qed
  ultimately show ?thesis
    by (subst SUP_emeasure_incseq) auto
qed

lemma emeasure_Collect_distr:
  assumes X[measurable]: "X \<in> measurable M N" "Measurable.pred N P"
  shows "emeasure (distr M N X) {x\<in>space N. P x} = emeasure M {x\<in>space M. P (X x)}"
  by (subst emeasure_distr)
     (auto intro!: arg_cong2[where f=emeasure] X(1)[THEN measurable_space])

lemma measurable_predpow[measurable]:
  assumes "Measurable.pred M T"
  assumes "\<And>Q. Measurable.pred M Q \<Longrightarrow> Measurable.pred M (R Q)"
  shows "Measurable.pred M ((R ^^ n) T)"
  by (induct n) (auto intro: assms)

lemma emeasure_lfp2[consumes 1, case_names cont f measurable]:
  assumes "P M"
  assumes cont: "Order_Continuity.continuous F"
  assumes f: "\<And>M. P M \<Longrightarrow> f \<in> measurable M' M"
  assumes *: "\<And>M A. P M \<Longrightarrow> (\<And>N. P N \<Longrightarrow> Measurable.pred N A) \<Longrightarrow> Measurable.pred M (F A)"
  shows "emeasure M' {x\<in>space M'. lfp F (f x)} = (SUP i. emeasure M' {x\<in>space M'. (F ^^ i) (\<lambda>x. False) (f x)})"
proof (subst (1 2) emeasure_Collect_distr[symmetric, where X=f])
  show "f \<in> measurable M' M"  "f \<in> measurable M' M"
    using f[OF `P M`] by auto
  { fix i show "Measurable.pred M ((F ^^ i) (\<lambda>x. False))"
    using `P M` by (induction i arbitrary: M) (auto intro!: *) }
  show "Measurable.pred M (lfp F)"
    using `P M` cont * by (rule measurable_lfp[of P])

  have "emeasure (distr M' M f) {x \<in> space (distr M' M f). lfp F x} =
    (\<Squnion>i. emeasure (distr M' M f) {x \<in> space (distr M' M f). (F ^^ i) (\<lambda>x. False) x})"
    using `P M`
  proof (coinduction arbitrary: M rule: emeasure_lfp)
    case (measurable A N) then have "\<And>N. P N \<Longrightarrow> Measurable.pred (distr M' N f) A"
      by metis
    then have "\<And>N. P N \<Longrightarrow> Measurable.pred N A"
      by simp
    with `P N`[THEN *] show ?case
      by auto
  qed fact
  then show "emeasure (distr M' M f) {x \<in> space M. lfp F x} =
    (\<Squnion>i. emeasure (distr M' M f) {x \<in> space M. (F ^^ i) (\<lambda>x. False) x})"
   by simp
qed

lemma (in prob_space) indep_eventsI_indep_vars:
  assumes indep: "indep_vars N X I"
  assumes P: "\<And>i. i \<in> I \<Longrightarrow> {x\<in>space (N i). P i x} \<in> sets (N i)"
  shows "indep_events (\<lambda>i. {x\<in>space M. P i (X i x)}) I"
proof -
  have "indep_sets (\<lambda>i. {X i -` A \<inter> space M |A. A \<in> sets (N i)}) I"
    using indep unfolding indep_vars_def2 by auto
  then show ?thesis
    unfolding indep_events_def_alt
  proof (rule indep_sets_mono_sets)
    fix i assume "i \<in> I"
    then have "{{x \<in> space M. P i (X i x)}} = {X i -` {x\<in>space (N i). P i x} \<inter> space M}"
      using indep by (auto simp: indep_vars_def dest: measurable_space)
    also have "\<dots> \<subseteq> {X i -` A \<inter> space M |A. A \<in> sets (N i)}"
      using P[OF `i \<in> I`] by blast
    finally show "{{x \<in> space M. P i (X i x)}} \<subseteq> {X i -` A \<inter> space M |A. A \<in> sets (N i)}" .
  qed
qed                              

lemma infinite_growing:
  fixes X :: "'a :: linorder set"
  assumes "X \<noteq> {}"
  assumes *: "\<And>x. x \<in> X \<Longrightarrow> \<exists>y\<in>X. y > x"
  shows "infinite X"
proof
  assume "finite X"
  with `X \<noteq> {}` have "Max X \<in> X" "\<forall>x\<in>X. x \<le> Max X"
    by auto
  with *[of "Max X"] show False
    by auto
qed

lemma emeasure_uniform_measure_1:
  "emeasure M S \<noteq> 0 \<Longrightarrow> emeasure M S \<noteq> \<infinity> \<Longrightarrow> emeasure (uniform_measure M S) S = 1"
  by (subst emeasure_uniform_measure)
     (simp_all add: emeasure_nonneg emeasure_neq_0_sets)

lemma nn_integral_divide:
  "0 < c \<Longrightarrow> f \<in> borel_measurable M \<Longrightarrow> (\<integral>\<^sup>+x. f x / c \<partial>M) = (\<integral>\<^sup>+x. f x \<partial>M) / c"
  unfolding divide_ereal_def
  apply (rule nn_integral_multc)
  apply assumption
  apply (cases c)
  apply auto
  done

lemma nn_integral_uniform_measure:
  assumes f[measurable]: "f \<in> borel_measurable M" and "\<And>x. 0 \<le> f x" and S[measurable]: "S \<in> sets M"
  shows "(\<integral>\<^sup>+x. f x \<partial>uniform_measure M S) = (\<integral>\<^sup>+x. f x * indicator S x \<partial>M) / emeasure M S"
proof -
  { assume "emeasure M S = \<infinity>"
    then have ?thesis
      by (simp add: uniform_measure_def nn_integral_density f) }
  moreover
  { assume [simp]: "emeasure M S = 0"
    then have ae: "AE x in M. x \<notin> S"
      using sets.sets_into_space[OF S]
      by (subst AE_iff_measurable[OF _ refl]) (simp_all add: subset_eq cong: rev_conj_cong)
    from ae have "(\<integral>\<^sup>+ x. indicator S x * f x / 0 \<partial>M) = 0"
      by (subst nn_integral_0_iff_AE) auto
    moreover from ae have "(\<integral>\<^sup>+ x. f x * indicator S x \<partial>M) = 0"
      by (subst nn_integral_0_iff_AE) auto
    ultimately have ?thesis
      by (simp add: uniform_measure_def nn_integral_density f) }
  moreover
  { assume "emeasure M S \<noteq> 0" "emeasure M S \<noteq> \<infinity>"
    moreover then have "0 < emeasure M S"
      by (simp add: emeasure_nonneg less_le)
    ultimately have ?thesis
      unfolding uniform_measure_def
      apply (subst nn_integral_density)
      apply (auto simp: f nn_integral_divide intro!: zero_le_divide_ereal)
      apply (simp add: mult.commute)
      done }
  ultimately show ?thesis by blast
qed

lemma prob_space_restrict_space:
  "S \<in> sets M \<Longrightarrow> emeasure M S = 1 \<Longrightarrow> prob_space (restrict_space M S)"
  by (intro prob_spaceI)
     (simp add: emeasure_restrict_space space_restrict_space)

lemma sets_Collect_restrict_space_iff: 
  assumes "S \<in> sets M"
  shows "{x\<in>space (restrict_space M S). P x} \<in> sets (restrict_space M S) \<longleftrightarrow> {x\<in>space M. x \<in> S \<and> P x} \<in> sets M"
proof -
  have "{x\<in>S. P x} = {x\<in>space M. x \<in> S \<and> P x}"
    using sets.sets_into_space[OF assms] by auto
  then show ?thesis
    by (subst sets_restrict_space_iff) (auto simp add: space_restrict_space assms)
qed

lemma pred_restrict_space:
  assumes "S \<in> sets M"
  shows "Measurable.pred (restrict_space M S) P \<longleftrightarrow> Measurable.pred M (\<lambda>x. x \<in> S \<and> P x)"
  unfolding pred_def sets_Collect_restrict_space_iff[OF assms] ..

lemma streams_sets:
  assumes X[measurable]: "X \<in> sets M" shows "streams X \<in> sets (stream_space M)"
proof -
  have "streams X = {x\<in>space (stream_space M). x \<in> streams X}"
    using streams_mono[OF _ sets.sets_into_space[OF X]] by (auto simp: space_stream_space)
  also have "\<dots> = {x\<in>space (stream_space M). gfp (\<lambda>p x. shd x \<in> X \<and> p (stl x)) x}"
    apply (simp add: set_eq_iff streams_def streamsp_def)
    apply (intro allI conj_cong refl arg_cong2[where f=gfp] ext)
    apply (case_tac xa)
    apply auto
    done
  also have "\<dots> \<in> sets (stream_space M)"
    apply (intro predE)
    apply (coinduction rule: measurable_gfp)
    apply (auto simp: down_continuous_def)
    done
  finally show ?thesis .
qed

lemma measurable_until:
  assumes [measurable]: "Measurable.pred (stream_space M) \<phi>" "Measurable.pred (stream_space M) \<psi>"
  shows "Measurable.pred (stream_space M) (\<phi> until \<psi>)"
  unfolding UNTIL_def
  by (coinduction rule: measurable_gfp) (simp_all add: down_continuous_def fun_eq_iff)

lemma [measurable (raw)]: "X \<in> sets (count_space UNIV)"
  by auto

lemma finite_nat_iff_bounded_le: "finite P \<longleftrightarrow> (\<exists>m::nat. \<forall>n\<ge>m. n \<notin> P)"
  using infinite_nat_iff_unbounded_le[of P] by auto

lemma (in prob_space) borel_0_1_law_AE:
  fixes P :: "nat \<Rightarrow> 'a \<Rightarrow> bool"
  assumes "indep_events (\<lambda>m. {x\<in>space M. P m x}) UNIV" (is "indep_events ?P _")
  shows "(AE x in M. infinite {m. P m x}) \<or> (AE x in M. finite {m. P m x})"
proof -
  have [measurable]: "\<And>m. {x\<in>space M. P m x} \<in> sets M"
    using assms by (auto simp: indep_events_def)
  have "prob (\<Inter>n. \<Union>m\<in>{n..}. ?P m) = 0 \<or> prob (\<Inter>n. \<Union>m\<in>{n..}. ?P m) = 1"
    by (rule borel_0_1_law) fact
  also have "prob (\<Inter>n. \<Union>m\<in>{n..}. ?P m) = 0 \<longleftrightarrow> (AE x in M. finite {m. P m x})"
    by (subst prob_eq_0) (simp_all add: Ball_def finite_nat_iff_bounded_le)
  also have "prob (\<Inter>n. \<Union>m\<in>{n..}. ?P m) = 1 \<longleftrightarrow> (AE x in M. infinite {m. P m x})"
    by (subst prob_eq_1) (simp_all add: Bex_def infinite_nat_iff_unbounded_le)
  finally show ?thesis
    by metis
qed

lemma AE_uniform_measure:
  assumes "emeasure M A \<noteq> 0" "emeasure M A < \<infinity>"
  shows "(AE x in uniform_measure M A. P x) \<longleftrightarrow> (AE x in M. x \<in> A \<longrightarrow> P x)"
proof -
  have "A \<in> sets M"
    using `emeasure M A \<noteq> 0` by (metis emeasure_notin_sets)
  moreover have "\<And>x. 0 < indicator A x / emeasure M A \<longleftrightarrow> x \<in> A"
    using emeasure_nonneg[of M A] assms
    by (cases "emeasure M A") (auto split: split_indicator simp: one_ereal_def)
  ultimately show ?thesis
    unfolding uniform_measure_def by (simp add: AE_density)
qed

lemma (in prob_space) indep_eventsI:
  "(\<And>i. i \<in> I \<Longrightarrow> F i \<in> sets M) \<Longrightarrow> (\<And>J. J \<subseteq> I \<Longrightarrow> finite J \<Longrightarrow> J \<noteq> {} \<Longrightarrow> prob (\<Inter>i\<in>J. F i) = (\<Prod>i\<in>J. prob (F i))) \<Longrightarrow> indep_events F I"
  by (auto simp: indep_events_def)

lemma case_same: "(case siterate f x of y ## s \<Rightarrow> g y s) = g x (siterate f (f x))"
  by (subst siterate.ctr) simp

lemma (in product_prob_space) AE_component: "i \<in> I \<Longrightarrow> AE x in M i. P x \<Longrightarrow> AE x in PiM I M. P (x i)"
  apply (rule AE_distrD[of "\<lambda>\<omega>. \<omega> i" "PiM I M" "M i" P])
  apply simp
  apply (subst PiM_component)
  apply simp_all
  done

lemma measurable_pred_countable[measurable (raw)]:
  assumes "countable X"
  shows 
    "(\<And>i. i \<in> X \<Longrightarrow> Measurable.pred M (\<lambda>x. P x i)) \<Longrightarrow> Measurable.pred M (\<lambda>x. \<forall>i\<in>X. P x i)"
    "(\<And>i. i \<in> X \<Longrightarrow> Measurable.pred M (\<lambda>x. P x i)) \<Longrightarrow> Measurable.pred M (\<lambda>x. \<exists>i\<in>X. P x i)"
  unfolding pred_def
  by (auto intro!: sets.sets_Collect_countable_All' sets.sets_Collect_countable_Ex' assms)

lemma measurable_THE:
  fixes P :: "'a \<Rightarrow> 'b \<Rightarrow> bool"
  assumes [measurable]: "\<And>i. Measurable.pred M (P i)"
  assumes I[simp]: "countable I" "\<And>i x. x \<in> space M \<Longrightarrow> P i x \<Longrightarrow> i \<in> I"
  assumes unique: "\<And>x i j. x \<in> space M \<Longrightarrow> P i x \<Longrightarrow> P j x \<Longrightarrow> i = j"
  shows "(\<lambda>x. THE i. P i x) \<in> measurable M (count_space UNIV)"
  unfolding measurable_def
proof safe
  fix X
  def f \<equiv> "\<lambda>x. THE i. P i x" def undef \<equiv> "THE i::'a. False"
  { fix i x assume "x \<in> space M" "P i x" then have "f x = i"
      unfolding f_def using unique by auto }
  note f_eq = this
  { fix x assume "x \<in> space M" "\<forall>i\<in>I. \<not> P i x"
    then have "\<And>i. \<not> P i x"
      using I(2)[of x] by auto
    then have "f x = undef"
      by (auto simp: undef_def f_def) }
  then have "f -` X \<inter> space M = (\<Union>i\<in>I \<inter> X. {x\<in>space M. P i x}) \<union>
     (if undef \<in> X then space M - (\<Union>i\<in>I. {x\<in>space M. P i x}) else {})"
    by (auto dest: f_eq)
  also have "\<dots> \<in> sets M"
    by (auto intro!: sets.Diff sets.countable_UN')
  finally show "f -` X \<inter> space M \<in> sets M" .
qed simp

lemma measurable_bot[measurable]: "Measurable.pred M \<bottom>"
  by (simp add: bot_fun_def)

lemma bex1_def: "(\<exists>!x\<in>X. P x) \<longleftrightarrow> (\<exists>x\<in>X. P x) \<and> (\<forall>x\<in>X. \<forall>y\<in>X. P x \<longrightarrow> P y \<longrightarrow> x = y)"
  by auto

lemma measurable_Ex1[measurable (raw)]:
  assumes [simp]: "countable I" and [measurable]: "\<And>i. i \<in> I \<Longrightarrow> Measurable.pred M (P i)"
  shows "Measurable.pred M (\<lambda>x. \<exists>!i\<in>I. P i x)"
  unfolding bex1_def by measurable

lemma measurable_split_if[measurable (raw)]:
  "(c \<Longrightarrow> Measurable.pred M f) \<Longrightarrow> (\<not> c \<Longrightarrow> Measurable.pred M g) \<Longrightarrow>
   Measurable.pred M (if c then f else g)"
  by simp

lemma ereal_times_divide_eq: "a * (b / c :: ereal) = a * b / c"
  by (cases a b c rule: ereal3_cases)
     (auto simp: field_simps zero_less_mult_iff)

lemma setsum_ereal_left_distrib:
  fixes f :: "'a \<Rightarrow> ereal"
  shows "(\<And>i. i \<in> A \<Longrightarrow> 0 \<le> f i) \<Longrightarrow> setsum f A * r = (\<Sum>n\<in>A. f n * r)"
  by (simp add: setsum_ereal_right_distrib mult_ac)

lemma emeasure_eq_0_AE: "AE x in M. \<not> P x \<Longrightarrow> emeasure M {x\<in>space M. P x} = 0"
  using AE_iff_measurable[OF _ refl, of M "\<lambda>x. \<not> P x"]
  by (cases "{x\<in>space M. P x} \<in> sets M") (simp_all add: emeasure_notin_sets)

lemma suntil_induct_strong[consumes 1, case_names base step]:
  "(\<phi> suntil \<psi>) x \<Longrightarrow>
    (\<And>\<omega>. \<psi> \<omega> \<Longrightarrow> P \<omega>) \<Longrightarrow>
    (\<And>\<omega>. \<phi> \<omega> \<Longrightarrow> \<not> \<psi> \<omega> \<Longrightarrow> (\<phi> suntil \<psi>) (stl \<omega>) \<Longrightarrow> P (stl \<omega>) \<Longrightarrow> P \<omega>) \<Longrightarrow> P x"
  using suntil.induct[of \<phi> \<psi> x P] by blast

lemma (in prob_space) prob_setsum:
  assumes [simp, intro]: "finite I"
  assumes P: "\<And>n. n \<in> I \<Longrightarrow> {x\<in>space M. P n x} \<in> events"
  assumes Q: "{x\<in>space M. Q x} \<in> events"
  assumes ae: "AE x in M. (\<forall>n\<in>I. P n x \<longrightarrow> Q x) \<and> (Q x \<longrightarrow> (\<exists>!n\<in>I. P n x))"
  shows "\<P>(x in M. Q x) = (\<Sum>n\<in>I. \<P>(x in M. P n x))"
proof -
  from ae[THEN AE_E_prob] guess S . note S = this
  then have disj: "disjoint_family_on (\<lambda>n. {x\<in>space M. P n x} \<inter> S) I"
    by (auto simp: disjoint_family_on_def)
  from S have ae_S:
    "AE x in M. x \<in> {x\<in>space M. Q x} \<longleftrightarrow> x \<in> (\<Union>n\<in>I. {x\<in>space M. P n x} \<inter> S)"
    "\<And>n. n \<in> I \<Longrightarrow> AE x in M. x \<in> {x\<in>space M. P n x} \<longleftrightarrow> x \<in> {x\<in>space M. P n x} \<inter> S"
    using ae by (auto dest!: AE_prob_1)
  from ae_S have *:
    "\<P>(x in M. Q x) = prob (\<Union>n\<in>I. {x\<in>space M. P n x} \<inter> S)"
    using P Q S by (intro finite_measure_eq_AE) (auto intro!: sets.Int)
  from ae_S have **:
    "\<And>n. n \<in> I \<Longrightarrow> \<P>(x in M. P n x) = prob ({x\<in>space M. P n x} \<inter> S)"
    using P Q S by (intro finite_measure_eq_AE) auto
  show ?thesis
    using S P disj
    by (auto simp add: * ** simp del: UN_simps intro!: finite_measure_finite_Union)
qed

lemma funpow_decreasing:
  fixes f :: "'a \<Rightarrow> ('a::complete_lattice)"
  shows "m \<le> n \<Longrightarrow> mono f \<Longrightarrow> (f ^^ m) \<bottom> \<le> (f ^^ n) \<bottom>"
  by (induct rule: dec_induct)
     (auto simp del: funpow.simps(2) simp add: funpow_Suc_right
           intro: order_trans[OF _ funpow_mono])

lemma nn_integral_count_space':
  assumes "finite A" "\<And>x. x \<in> B \<Longrightarrow> x \<notin> A \<Longrightarrow> f x = 0" "\<And>x. x \<in> A \<Longrightarrow> 0 \<le> f x" "A \<subseteq> B"
  shows "(\<integral>\<^sup>+x. f x \<partial>count_space B) = (\<Sum>x\<in>A. f x)"
proof -
  have "(\<integral>\<^sup>+x. f x \<partial>count_space B) = (\<Sum>a | a \<in> B \<and> 0 < f a. f a)"
    using assms(2,3)
    by (intro nn_integral_count_space finite_subset[OF _ `finite A`]) (auto simp: less_le)
  also have "\<dots> = (\<Sum>a\<in>A. f a)"
    using assms by (intro setsum.mono_neutral_cong_left) (auto simp: less_le)
  finally show ?thesis .
qed

lemma suntil_aand_nxt:
  "(\<phi> suntil (\<phi> aand nxt \<psi>)) \<omega> \<longleftrightarrow> (\<phi> aand nxt (\<phi> suntil \<psi>)) \<omega>"
proof
  assume "(\<phi> suntil (\<phi> aand nxt \<psi>)) \<omega>" then show "(\<phi> aand nxt (\<phi> suntil \<psi>)) \<omega>"
    by induction (auto intro: suntil.intros)
next
  assume "(\<phi> aand nxt (\<phi> suntil \<psi>)) \<omega>"
  then have "(\<phi> suntil \<psi>) (stl \<omega>)" "\<phi> \<omega>"
    by auto
  then show "(\<phi> suntil (\<phi> aand nxt \<psi>)) \<omega>"
    by (induction "stl \<omega>" arbitrary: \<omega>)
       (auto elim: suntil.cases intro: suntil.intros)
qed

lemma nn_integral_indicator_finite:
  fixes f :: "'a \<Rightarrow> ereal"
  assumes f: "finite A" and nn: "\<And>x. x \<in> A \<Longrightarrow> 0 \<le> f x" and [measurable]: "\<And>a. a \<in> A \<Longrightarrow> {a} \<in> sets M"
  shows "(\<integral>\<^sup>+x. f x * indicator A x \<partial>M) = (\<Sum>x\<in>A. f x * emeasure M {x})"
proof -
  from f have "(\<integral>\<^sup>+x. f x * indicator A x \<partial>M) = (\<integral>\<^sup>+x. (\<Sum>a\<in>A. f a * indicator {a} x) \<partial>M)"
    by (intro nn_integral_cong) (auto simp: indicator_def if_distrib[where f="\<lambda>a. x * a" for x] setsum.If_cases)
  also have "\<dots> = (\<Sum>a\<in>A. f a * emeasure M {a})"
    using nn by (subst nn_integral_setsum) (auto simp: nn_integral_cmult_indicator)
  finally show ?thesis .
qed

lemma nn_integral_measure_pmf_support:
  fixes f :: "'a \<Rightarrow> ereal"
  assumes f: "finite A" and nn: "\<And>x. x \<in> A \<Longrightarrow> 0 \<le> f x" "\<And>x. x \<in> set_pmf M \<Longrightarrow> x \<notin> A \<Longrightarrow> f x = 0"
  shows "(\<integral>\<^sup>+x. f x \<partial>measure_pmf M) = (\<Sum>x\<in>A. f x * pmf M x)"
proof -
  have "(\<integral>\<^sup>+x. f x \<partial>M) = (\<integral>\<^sup>+x. f x * indicator A x \<partial>M)"
    using nn by (intro nn_integral_cong_AE) (auto simp: AE_measure_pmf_iff split: split_indicator)
  also have "\<dots> = (\<Sum>x\<in>A. f x * emeasure M {x})"
    using assms by (intro nn_integral_indicator_finite) auto
  finally show ?thesis
    by (simp add: emeasure_measure_pmf_finite)
qed

lemma nn_integral_measure_pmf_finite:
  fixes f :: "'a \<Rightarrow> ereal"
  assumes f: "finite (set_pmf M)" and nn: "\<And>x. x \<in> set_pmf M \<Longrightarrow> 0 \<le> f x"
  shows "(\<integral>\<^sup>+x. f x \<partial>measure_pmf M) = (\<Sum>x\<in>set_pmf M. f x * pmf M x)"
  using assms by (intro nn_integral_measure_pmf_support) auto

lemma alw_sconst: "alw P (sconst x) \<longleftrightarrow> P (sconst x)"
proof
  assume "P (sconst x)" then show "alw P (sconst x)"
    by coinduction auto
qed auto

lemma ev_sconst: "ev P (sconst x) \<longleftrightarrow> P (sconst x)"
proof
  assume "ev P (sconst x)" then show "P (sconst x)"
    by (induction "sconst x") auto
qed auto

lemma suntil_sconst: "(\<phi> suntil \<psi>) (sconst x) \<longleftrightarrow> \<psi> (sconst x)"
proof
  assume "(\<phi> suntil \<psi>) (sconst x)" then show "\<psi> (sconst x)"
    by (induction "sconst x") auto
qed (auto intro: suntil.intros)

hide_const cont

lemma mono_funpow:
  fixes Q :: "('i \<Rightarrow> 'a::complete_lattice) \<Rightarrow> ('i \<Rightarrow> 'a::complete_lattice)"
  shows "mono Q \<Longrightarrow> mono (\<lambda>i. (Q ^^ i) \<bottom>)"
  by (auto intro!: funpow_decreasing simp: mono_def)

lemma mono_compose: "mono Q \<Longrightarrow> mono (\<lambda>i x. Q i (f x))"
  unfolding mono_def le_fun_def by auto

lemma SUP_ereal_mult_right:
  fixes f :: "'a \<Rightarrow> ereal"
  assumes "I \<noteq> {}"
  assumes "\<And>i. i \<in> I \<Longrightarrow> 0 \<le> f i"
    and "0 \<le> c"
  shows "(SUP i:I. c * f i) = c * (SUP i:I. f i)"
proof (rule SUP_eqI)
  fix i assume "i \<in> I"
  then have "f i \<le> SUPREMUM I f"
    by (rule SUP_upper)
  then show "c * f i \<le> c * SUPREMUM I f"
    using `0 \<le> c` by (rule ereal_mult_left_mono)
next
  fix y assume *: "\<And>i. i \<in> I \<Longrightarrow> c * f i \<le> y"
  { assume "c = \<infinity>" have "c * SUPREMUM I f \<le> y"
    proof cases
      assume "\<forall>i\<in>I. f i = 0"
      then show ?thesis
        using * `c = \<infinity>` by (auto simp: SUP_constant bot_ereal_def)
    next
      assume "\<not> (\<forall>i\<in>I. f i = 0)"
      then obtain i where "f i \<noteq> 0" "i \<in> I"
        by auto
      with *[of i] `c = \<infinity>` `i \<in> I \<Longrightarrow> 0 \<le> f i` show ?thesis
        by (auto split: split_if_asm)
    qed }
  moreover
  { assume "c \<noteq> 0" "c \<noteq> \<infinity>"
    moreover with `0 \<le> c` * have "SUPREMUM I f \<le> y / c"
      by (intro SUP_least) (auto simp: ereal_le_divide_pos)
    ultimately have "c * SUPREMUM I f \<le> y"
      using `0 \<le> c` * by (auto simp: ereal_le_divide_pos) }
  moreover { assume "c = 0" with * `I \<noteq> {}` have "c * SUPREMUM I f \<le> y" by auto }
  ultimately show "c * SUPREMUM I f \<le> y"
    by blast
qed

lemma SUP_ereal_add_left:
  fixes f :: "'a \<Rightarrow> ereal"
  assumes "I \<noteq> {}"
  assumes "\<And>i. i \<in> I \<Longrightarrow> 0 \<le> f i"
    and "0 \<le> c"
  shows "(SUP i:I. f i + c) = SUPREMUM I f + c"
proof (intro SUP_eqI)
  fix B assume *: "\<And>i. i \<in> I \<Longrightarrow> f i + c \<le> B"
  show "SUPREMUM I f + c \<le> B"
  proof cases
    assume "c = \<infinity>" with `I \<noteq> {}` * show ?thesis
      by auto
  next
    assume "c \<noteq> \<infinity>"
    with `0 \<le> c` have [simp]: "\<bar>c\<bar> \<noteq> \<infinity>"
      by simp
    have "SUPREMUM I f \<le> B - c"
      by (simp add: SUP_le_iff ereal_le_minus *)
    then show ?thesis
      by (simp add: ereal_le_minus)
  qed
qed (auto intro: ereal_add_mono SUP_upper)

lemma ereal_mult_divide: fixes a b :: ereal shows "0 < b \<Longrightarrow> b < \<infinity> \<Longrightarrow> b * (a / b) = a"
  by (cases a b rule: ereal2_cases) auto

lemma nn_integral_monotone_convergence_SUP:
  assumes f: "incseq f" and [measurable]: "\<And>i. f i \<in> borel_measurable M"
  shows "(\<integral>\<^sup>+ x. (SUP i. f i x) \<partial>M) = (SUP i. integral\<^sup>N M (f i))"
proof -
  have "(\<integral>\<^sup>+ x. max 0 (SUP i. f i x) \<partial>M) = (\<integral>\<^sup>+ x. (SUP i. max 0 (f i x)) \<partial>M)"
    unfolding sup_max[symmetric] Complete_Lattices.SUP_sup_distrib[symmetric] by simp
  also have "\<dots> = (SUP i. (\<integral>\<^sup>+ x. max 0 (f i x) \<partial>M))"
    apply (intro nn_integral_monotone_convergence_SUP)
    apply (auto simp: incseq_def le_fun_def not_le dest!: incseqD[OF f] split: split_max)
    apply (blast intro: order_trans less_imp_le)
    done
  finally show ?thesis
    unfolding nn_integral_max_0 .
qed

lemma some_in_iff: "(SOME x. x \<in> A) \<in> A \<longleftrightarrow> A \<noteq> {}"
  by (metis someI_ex ex_in_conv)

lemma all_le_Suc_split: "(\<forall>i\<le>Suc n. P i) \<longleftrightarrow> (P 0 \<and> (\<forall>i\<le>n. P (Suc i)))"
  by (metis Suc_le_mono less_eq_nat.simps(1) not0_implies_Suc)

lemma measure_le_0: "measure M X \<le> 0 \<longleftrightarrow> measure M X = 0"
  using measure_nonneg[of M X] by auto


lemma (in finite_measure) countable_support: (* replace version in pmf *)
  "countable {x. measure M {x} \<noteq> 0}"
proof cases
  assume "measure M (space M) = 0"
  with bounded_measure measure_le_0 have "{x. measure M {x} \<noteq> 0} = {}"
    by auto
  then show ?thesis
    by simp
next
  let ?M = "measure M (space M)" and ?m = "\<lambda>x. measure M {x}"
  assume "?M \<noteq> 0"
  then have *: "{x. ?m x \<noteq> 0} = (\<Union>n. {x. ?M / Suc n < ?m x})"
    using reals_Archimedean[of "?m x / ?M" for x]
    by (auto simp: field_simps not_le[symmetric] measure_nonneg divide_le_0_iff measure_le_0)
  have **: "\<And>n. finite {x. ?M / Suc n < ?m x}"
  proof (rule ccontr)
    fix n assume "infinite {x. ?M / Suc n < ?m x}" (is "infinite ?X")
    then obtain X where "finite X" "card X = Suc (Suc n)" "X \<subseteq> ?X"
      by (metis infinite_arbitrarily_large)
    from this(3) have *: "\<And>x. x \<in> X \<Longrightarrow> ?M / Suc n \<le> ?m x" 
      by auto
    { fix x assume "x \<in> X"
      from `?M \<noteq> 0` *[OF this] have "?m x \<noteq> 0" by (auto simp: field_simps measure_le_0)
      then have "{x} \<in> sets M" by (auto dest: measure_notin_sets) }
    note singleton_sets = this
    have "?M < (\<Sum>x\<in>X. ?M / Suc n)"
      using `?M \<noteq> 0` 
      by (simp add: `card X = Suc (Suc n)` real_eq_of_nat[symmetric] real_of_nat_Suc field_simps less_le measure_nonneg)
    also have "\<dots> \<le> (\<Sum>x\<in>X. ?m x)"
      by (rule setsum_mono) fact
    also have "\<dots> = measure M (\<Union>x\<in>X. {x})"
      using singleton_sets `finite X`
      by (intro finite_measure_finite_Union[symmetric]) (auto simp: disjoint_family_on_def)
    finally have "?M < measure M (\<Union>x\<in>X. {x})" .
    moreover have "measure M (\<Union>x\<in>X. {x}) \<le> ?M"
      using singleton_sets[THEN sets.sets_into_space] by (intro finite_measure_mono) auto
    ultimately show False by simp
  qed
  show ?thesis
    unfolding * by (intro countable_UN countableI_type countable_finite[OF **])
qed

lemma (in finite_measure) AE_support_countable:
  assumes [simp]: "sets M = UNIV"
  shows "(AE x in M. measure M {x} \<noteq> 0) \<longleftrightarrow> (\<exists>S. countable S \<and> (AE x in M. x \<in> S))"
proof
  assume "\<exists>S. countable S \<and> (AE x in M. x \<in> S)"
  then obtain S where S[intro]: "countable S" and ae: "AE x in M. x \<in> S"
    by auto
  then have "emeasure M (\<Union>x\<in>{x\<in>S. emeasure M {x} \<noteq> 0}. {x}) = 
    (\<integral>\<^sup>+ x. emeasure M {x} * indicator {x\<in>S. emeasure M {x} \<noteq> 0} x \<partial>count_space UNIV)"
    by (subst emeasure_UN_countable)
       (auto simp: disjoint_family_on_def nn_integral_restrict_space[symmetric] restrict_count_space)
  also have "\<dots> = (\<integral>\<^sup>+ x. emeasure M {x} * indicator S x \<partial>count_space UNIV)"
    by (auto intro!: nn_integral_cong split: split_indicator)
  also have "\<dots> = emeasure M (\<Union>x\<in>S. {x})"
    by (subst emeasure_UN_countable)
       (auto simp: disjoint_family_on_def nn_integral_restrict_space[symmetric] restrict_count_space)
  also have "\<dots> = emeasure M (space M)"
    using ae by (intro emeasure_eq_AE) auto
  finally have "emeasure M {x \<in> space M. x\<in>S \<and> emeasure M {x} \<noteq> 0} = emeasure M (space M)"
    by (simp add: emeasure_single_in_space cong: rev_conj_cong)
  with finite_measure_compl[of "{x \<in> space M. x\<in>S \<and> emeasure M {x} \<noteq> 0}"]
  have "AE x in M. x \<in> S \<and> emeasure M {x} \<noteq> 0"
    by (intro AE_I[OF order_refl]) (auto simp: emeasure_eq_measure set_diff_eq cong: conj_cong)
  then show "AE x in M. measure M {x} \<noteq> 0"
    by (auto simp: emeasure_eq_measure)
qed (auto intro!: exI[of _ "{x. measure M {x} \<noteq> 0}"] countable_support)

lemma ereal_indicator_le_0: "(indicator S x::ereal) \<le> 0 \<longleftrightarrow> x \<notin> S"
  by (auto split: split_indicator simp: one_ereal_def)

lemma nn_integral_bind:
  assumes f: "f \<in> borel_measurable B" "\<And>x. 0 \<le> f x"
  assumes N: "N \<in> measurable M (subprob_algebra B)"
  shows "(\<integral>\<^sup>+x. f x \<partial>(M \<guillemotright>= N)) = (\<integral>\<^sup>+x. \<integral>\<^sup>+y. f y \<partial>N x \<partial>M)"
proof cases
  assume M: "space M \<noteq> {}" show ?thesis
    unfolding bind_nonempty''[OF N M] nn_integral_join[OF f sets_distr]
    by (rule nn_integral_distr[OF N nn_integral_measurable_subprob_algebra[OF f]])
qed (simp add: bind_empty space_empty[of M] nn_integral_count_space)

lemma (in prob_space) prob_space_bind: 
  assumes ae: "AE x in M. prob_space (N x)"
    and N[measurable]: "N \<in> measurable M (subprob_algebra S)"
  shows "prob_space (M \<guillemotright>= N)"
proof
  have "emeasure (M \<guillemotright>= N) (space (M \<guillemotright>= N)) = (\<integral>\<^sup>+x. emeasure (N x) (space (N x)) \<partial>M)"
    by (subst emeasure_bind[where N=S])
       (auto simp: not_empty space_bind[OF N] subprob_measurableD[OF N] intro!: nn_integral_cong)
  also have "\<dots> = (\<integral>\<^sup>+x. 1 \<partial>M)"
    using ae by (intro nn_integral_cong_AE, eventually_elim) (rule prob_space.emeasure_space_1)
  finally show "emeasure (M \<guillemotright>= N) (space (M \<guillemotright>= N)) = 1"
    by (simp add: emeasure_space_1)
qed

lemma AE_bind:
  assumes P[measurable]: "Measurable.pred B P"
  assumes N[measurable]: "N \<in> measurable M (subprob_algebra B)"
  shows "(AE x in M \<guillemotright>= N. P x) \<longleftrightarrow> (AE x in M. AE y in N x. P y)"
proof cases
  assume M: "space M = {}" show ?thesis
    unfolding bind_empty[OF M] unfolding space_empty[OF M] by (simp add: AE_count_space)
next
  assume M: "space M \<noteq> {}"
  have *: "(\<integral>\<^sup>+x. indicator {x. \<not> P x} x \<partial>(M \<guillemotright>= N)) = (\<integral>\<^sup>+x. indicator {x\<in>space B. \<not> P x} x \<partial>(M \<guillemotright>= N))"
    by (intro nn_integral_cong) (simp add: space_bind[OF N M] split: split_indicator)

  have "(AE x in M \<guillemotright>= N. P x) \<longleftrightarrow> (\<integral>\<^sup>+ x. integral\<^sup>N (N x) (indicator {x \<in> space B. \<not> P x}) \<partial>M) = 0"
    by (simp add: AE_iff_nn_integral sets_bind[OF N M] space_bind[OF N M] * nn_integral_bind[where B=B]
             del: nn_integral_indicator)
  also have "\<dots> = (AE x in M. AE y in N x. P y)"
    apply (subst nn_integral_0_iff_AE)
    apply (rule measurable_compose[OF N nn_integral_measurable_subprob_algebra])
    apply measurable
    apply (intro eventually_subst AE_I2)
    apply simp
    apply (subst nn_integral_0_iff_AE)
    apply (simp add: subprob_measurableD(3)[OF N])
    apply (auto simp add: ereal_indicator_le_0 subprob_measurableD(1)[OF N] intro!: eventually_subst)
    done
  finally show ?thesis .
qed

lemma measure_eqI_restrict_generator:
  assumes E: "Int_stable E" "E \<subseteq> Pow \<Omega>" "\<And>X. X \<in> E \<Longrightarrow> emeasure M X = emeasure N X"
  assumes sets_eq: "sets M = sets N" and \<Omega>: "\<Omega> \<in> sets M"
  assumes "sets (restrict_space M \<Omega>) = sigma_sets \<Omega> E"
  assumes "sets (restrict_space N \<Omega>) = sigma_sets \<Omega> E" 
  assumes ae: "AE x in M. x \<in> \<Omega>" "AE x in N. x \<in> \<Omega>"
  assumes A: "countable A" "A \<noteq> {}" "A \<subseteq> E" "\<Union>A = \<Omega>" "\<And>a. a \<in> A \<Longrightarrow> emeasure M a \<noteq> \<infinity>"
  shows "M = N"
proof (rule measure_eqI)
  fix X assume X: "X \<in> sets M"
  then have "emeasure M X = emeasure (restrict_space M \<Omega>) (X \<inter> \<Omega>)"
    using ae \<Omega> by (auto simp add: emeasure_restrict_space intro!: emeasure_eq_AE)
  also have "restrict_space M \<Omega> = restrict_space N \<Omega>"
  proof (rule measure_eqI_generator_eq)
    fix X assume "X \<in> E"
    then show "emeasure (restrict_space M \<Omega>) X = emeasure (restrict_space N \<Omega>) X"
      using E \<Omega> by (subst (1 2) emeasure_restrict_space) (auto simp: sets_eq sets_eq[THEN sets_eq_imp_space_eq])
  next
    show "range (from_nat_into A) \<subseteq> E" "(\<Union>i. from_nat_into A i) = \<Omega>"
      unfolding Sup_image_eq[symmetric, where f="from_nat_into A"] using A by auto
  next
    fix i
    have "emeasure (restrict_space M \<Omega>) (from_nat_into A i) = emeasure M (from_nat_into A i)"
      using A \<Omega> by (subst emeasure_restrict_space)
                   (auto simp: sets_eq sets_eq[THEN sets_eq_imp_space_eq] intro: from_nat_into)
    with A show "emeasure (restrict_space M \<Omega>) (from_nat_into A i) \<noteq> \<infinity>"
      by (auto intro: from_nat_into)
  qed fact+
  also have "emeasure (restrict_space N \<Omega>) (X \<inter> \<Omega>) = emeasure N X"
    using X ae \<Omega> by (auto simp add: emeasure_restrict_space sets_eq intro!: emeasure_eq_AE)
  finally show "emeasure M X = emeasure N X" .
qed fact

lemma (in prob_space) emeasure_eq_1_AE:
  "S \<in> sets M \<Longrightarrow> AE x in M. x \<in> S \<Longrightarrow> emeasure M S = 1"
  by (subst emeasure_eq_AE[where B="space M"]) (auto simp: emeasure_space_1)

lemma streams_mono2: "S \<subseteq> T \<Longrightarrow> streams S \<subseteq> streams T"
  by (auto intro: streams_mono)

lemma emeasure_sigma: "emeasure (sigma \<Omega> A) X = 0"
  unfolding measure_of_def emeasure_def
  by (subst Abs_measure_inverse)
     (auto simp: measure_space_def positive_def countably_additive_def
           intro!: sigma_algebra_sigma_sets sigma_algebra_trivial)

lemma vimage_algebra_vimage_algebra_eq:
  assumes *: "f \<in> X \<rightarrow> Y" "g \<in> Y \<rightarrow> space M"
  shows "vimage_algebra X f (vimage_algebra Y g M) = vimage_algebra X (\<lambda>x. g (f x)) M"
  (is "?VV = ?V")
proof (rule measure_eqI)
  have "(\<lambda>x. g (f x)) \<in> X \<rightarrow> space M" "\<And>A. A \<inter> f -` Y \<inter> X = A \<inter> X"
    using * by auto
  with * show "sets ?VV = sets ?V"
    by (simp add: sets_vimage_algebra2 ex_simps[symmetric] vimage_comp comp_def del: ex_simps)
qed (simp add: vimage_algebra_def emeasure_sigma)

lemma sets_vimage_Sup_eq:
  assumes *: "M \<noteq> {}" "\<And>m. m \<in> M \<Longrightarrow> f \<in> X \<rightarrow> space m"
  shows "sets (vimage_algebra X f (Sup_sigma M)) = sets (\<Squnion>\<^sub>\<sigma> m \<in> M. vimage_algebra X f m)"
  (is "?IS = ?SI")
proof
  show "?IS \<subseteq> ?SI"
    by (intro sets_image_in_sets measurable_Sup_sigma2 measurable_Sup_sigma1)
       (auto simp: space_Sup_sigma measurable_vimage_algebra1 *)
  { fix m assume "m \<in> M"
    moreover then have "f \<in> X \<rightarrow> space (Sup_sigma M)" "f \<in> X \<rightarrow> space m"
      using * by (auto simp: space_Sup_sigma)
    ultimately have "f \<in> measurable (vimage_algebra X f (Sup_sigma M)) m"
      by (auto simp add: measurable_def sets_vimage_algebra2 intro: in_Sup_sigma) }
  then show "?SI \<subseteq> ?IS"
    by (auto intro!: sets_image_in_sets sets_Sup_in_sets del: subsetI simp: *)
qed

lemma restrict_space_eq_vimage_algebra:
  "\<Omega> \<subseteq> space M \<Longrightarrow> sets (restrict_space M \<Omega>) = sets (vimage_algebra \<Omega> (\<lambda>x. x) M)"
  unfolding restrict_space_def
  apply (subst sets_measure_of)
  apply (auto simp add: image_subset_iff dest: sets.sets_into_space) []
  apply (auto simp add: sets_vimage_algebra intro!: arg_cong2[where f=sigma_sets])
  done

lemma vimage_algebra_cong: "sets M = sets N \<Longrightarrow> sets (vimage_algebra X f M) = sets (vimage_algebra X f N)"
  by (simp add: sets_vimage_algebra)

lemma SUP_sigma_cong: 
  assumes *: "\<And>i. i \<in> I \<Longrightarrow> sets (M i) = sets (N i)" shows "sets (\<Squnion>\<^sub>\<sigma> i\<in>I. M i) = sets (\<Squnion>\<^sub>\<sigma> i\<in>I. N i)"
  using * sets_eq_imp_space_eq[OF *] by (simp add: Sup_sigma_def)

lemma snth_in: "s \<in> streams X \<Longrightarrow> s !! n \<in> X"
  by (force simp: streams_iff_sset sset_range)

lemma to_stream_in_streams: "to_stream X \<in> streams S \<longleftrightarrow> (\<forall>n. X n \<in> S)"
  by (simp add: to_stream_def streams_iff_snth)


lemma in_streams: "stl s \<in> streams S \<Longrightarrow> shd s \<in> S \<Longrightarrow> s \<in> streams S"
  by (cases s) auto

lemma sets_stream_space_in_sets:
  assumes space: "space N = streams (space M)"
  assumes sets: "\<And>i. (\<lambda>x. x !! i) \<in> measurable N M"
  shows "sets (stream_space M) \<subseteq> sets N"
  unfolding stream_space_def sets_distr
  by (auto intro!: sets_image_in_sets measurable_Sup_sigma2 measurable_vimage_algebra2 del: subsetI equalityI 
           simp add: sets_PiM_eq_proj snth_in space sets cong: measurable_cong_sets)

lemma sets_stream_space_eq: "sets (stream_space M) =
    sets (\<Squnion>\<^sub>\<sigma> i\<in>UNIV. vimage_algebra (streams (space M)) (\<lambda>s. s !! i) M)"
  by (auto intro!: sets_stream_space_in_sets sets_Sup_in_sets sets_image_in_sets
                   measurable_Sup_sigma1  snth_in measurable_vimage_algebra1 del: subsetI
           simp: space_Sup_sigma space_stream_space)

lemma sets_restrict_stream_space:
  assumes S[measurable]: "S \<in> sets M"
  shows "sets (restrict_space (stream_space M) (streams S)) = sets (stream_space (restrict_space M S))"
  using  S[THEN sets.sets_into_space]
  apply (subst restrict_space_eq_vimage_algebra)
  apply (simp add: space_stream_space streams_mono2)
  apply (subst vimage_algebra_cong[OF sets_stream_space_eq])
  apply (subst sets_stream_space_eq)
  apply (subst sets_vimage_Sup_eq)
  apply simp
  apply (auto intro: streams_mono) []
  apply (simp add: image_image space_restrict_space)
  apply (intro SUP_sigma_cong)
  apply (simp add: vimage_algebra_cong[OF restrict_space_eq_vimage_algebra])
  apply (subst (1 2) vimage_algebra_vimage_algebra_eq)
  apply (auto simp: streams_mono snth_in)
  done

primrec sstart :: "'a set \<Rightarrow> 'a list \<Rightarrow> 'a stream set" where
  "sstart S [] = streams S"
| [simp del]: "sstart S (x # xs) = op ## x ` sstart S xs"

lemma in_sstart[simp]: "s \<in> sstart S (x # xs) \<longleftrightarrow> shd s = x \<and> stl s \<in> sstart S xs"
  by (cases s) (auto simp: sstart.simps(2))

lemma sstart_in_streams: "xs \<in> lists S \<Longrightarrow> sstart S xs \<subseteq> streams S"
  by (induction xs) (auto simp: sstart.simps(2))

lemma sstart_eq: "x \<in> streams S \<Longrightarrow> x \<in> sstart S xs = (\<forall>i<length xs. x !! i = xs ! i)"
  by (induction xs arbitrary: x) (auto simp: nth_Cons streams_stl split: nat.splits)

lemma sstart_sets: "sstart S xs \<in> sets (stream_space (count_space UNIV))"
proof (induction xs)
  case (Cons x xs)
  note Cons[measurable]
  have "sstart S (x # xs) =
    {s\<in>space (stream_space (count_space UNIV)). shd s = x \<and> stl s \<in> sstart S xs}"
    by (simp add: set_eq_iff space_stream_space)
  also have "\<dots> \<in> sets (stream_space (count_space UNIV))"
    by measurable
  finally show ?case .
qed (simp add: streams_sets)

lemma sets_stream_space_sstart:
  assumes S[simp]: "countable S"
  shows "sets (stream_space (count_space S)) = sets (sigma (streams S) (sstart S`lists S \<union> {{}}))"
proof
  have [simp]: "sstart S ` lists S \<subseteq> Pow (streams S)"
    by (simp add: image_subset_iff sstart_in_streams)

  let ?S = "sigma (streams S) (sstart S ` lists S \<union> {{}})"
  { fix i a assume "a \<in> S"
    { fix x have "(x !! i = a \<and> x \<in> streams S) \<longleftrightarrow> (\<exists>xs\<in>lists S. length xs = i \<and> x \<in> sstart S (xs @ [a]))"
      proof (induction i arbitrary: x)
        case (Suc i) from this[of "stl x"] show ?case
          by (simp add: length_Suc_conv Bex_def ex_simps[symmetric] del: ex_simps)
             (metis stream.collapse streams_Stream)
      qed (insert `a \<in> S`, auto intro: streams_stl in_streams) }
    then have "(\<lambda>x. x !! i) -` {a} \<inter> streams S = (\<Union>xs\<in>{xs\<in>lists S. length xs = i}. sstart S (xs @ [a]))"
      by (auto simp add: set_eq_iff)
    also have "\<dots> \<in> sets ?S"
      using `a\<in>S` by (intro sets.countable_UN') (auto intro!: sigma_sets.Basic image_eqI)
    finally have " (\<lambda>x. x !! i) -` {a} \<inter> streams S \<in> sets ?S" . }
  then show "sets (stream_space (count_space S)) \<subseteq> sets (sigma (streams S) (sstart S`lists S \<union> {{}}))"
    by (intro sets_stream_space_in_sets) (auto simp: measurable_count_space_eq_countable snth_in)

  have "sigma_sets (space (stream_space (count_space S))) (sstart S`lists S \<union> {{}}) \<subseteq> sets (stream_space (count_space S))"
  proof (safe intro!: sets.sigma_sets_subset)
    fix xs assume "\<forall>x\<in>set xs. x \<in> S"
    then have "sstart S xs = {x\<in>space (stream_space (count_space S)). \<forall>i<length xs. x !! i = xs ! i}"
      by (induction xs)
         (auto simp: space_stream_space nth_Cons split: nat.split intro: in_streams streams_stl)
    also have "\<dots> \<in> sets (stream_space (count_space S))"
      by measurable
    finally show "sstart S xs \<in> sets (stream_space (count_space S))" .
  qed
  then show "sets (sigma (streams S) (sstart S`lists S \<union> {{}})) \<subseteq> sets (stream_space (count_space S))"
    by (simp add: space_stream_space)
qed

lemma Int_stable_sstart: "Int_stable (sstart S`lists S \<union> {{}})"
proof -
  { fix xs ys assume "xs \<in> lists S" "ys \<in> lists S"
    then have "sstart S xs \<inter> sstart S ys \<in> sstart S ` lists S \<union> {{}}"
    proof (induction xs ys rule: list_induct2')
      case (4 x xs y ys)
      show ?case
      proof cases
        assume "x = y"
        then have "sstart S (x # xs) \<inter> sstart S (y # ys) = op ## x ` (sstart S xs \<inter> sstart S ys)"
          by (auto simp: image_iff intro!: stream.collapse[symmetric])
        also have "\<dots> \<in> sstart S ` lists S \<union> {{}}"
          using 4 by (auto simp: sstart.simps(2)[symmetric] del: in_listsD)
        finally show ?case .
      qed auto
    qed (simp_all add: sstart_in_streams inf.absorb1 inf.absorb2 image_eqI[where x="[]"]) }
  then show ?thesis
    by (auto simp: Int_stable_def)
qed

lemma stream_space_eq_sstart:
  assumes S[simp]: "countable S"
  assumes P: "prob_space M" "prob_space N"
  assumes ae: "AE x in M. x \<in> streams S" "AE x in N. x \<in> streams S"
  assumes sets_M: "sets M = sets (stream_space (count_space UNIV))"
  assumes sets_N: "sets N = sets (stream_space (count_space UNIV))"
  assumes *: "\<And>xs. xs \<noteq> [] \<Longrightarrow> xs \<in> lists S \<Longrightarrow> emeasure M (sstart S xs) = emeasure N (sstart S xs)"
  shows "M = N"
proof (rule measure_eqI_restrict_generator[OF Int_stable_sstart])
  have [simp]: "sstart S ` lists S \<subseteq> Pow (streams S)"
    by (simp add: image_subset_iff sstart_in_streams)

  interpret M: prob_space M by fact

  show "sstart S ` lists S \<union> {{}} \<subseteq> Pow (streams S)"
    by (auto dest: sstart_in_streams del: in_listsD)

  { fix M :: "'a stream measure" assume M: "sets M = sets (stream_space (count_space UNIV))"
    have "sets (restrict_space M (streams S)) = sigma_sets (streams S) (sstart S ` lists S \<union> {{}})"
      apply (simp add: sets_eq_imp_space_eq[OF M] space_stream_space restrict_space_eq_vimage_algebra
        vimage_algebra_cong[OF M])
      apply (simp add: sets_eq_imp_space_eq[OF M] space_stream_space restrict_space_eq_vimage_algebra[symmetric])
      apply (simp add: sets_restrict_stream_space restrict_count_space sets_stream_space_sstart)
      done }
  from this[OF sets_M] this[OF sets_N]
  show "sets (restrict_space M (streams S)) = sigma_sets (streams S) (sstart S ` lists S \<union> {{}})"
       "sets (restrict_space N (streams S)) = sigma_sets (streams S) (sstart S ` lists S \<union> {{}})"
    by auto
  show "{streams S} \<subseteq> sstart S ` lists S \<union> {{}}"
    "\<Union>{streams S} = streams S" "\<And>s. s \<in> {streams S} \<Longrightarrow> emeasure M s \<noteq> \<infinity>"
    using M.emeasure_space_1 space_stream_space[of "count_space S"] sets_eq_imp_space_eq[OF sets_M]
    by (auto simp add: image_eqI[where x="[]"])
  show "sets M = sets N"
    by (simp add: sets_M sets_N)
next
  fix X assume "X \<in> sstart S ` lists S \<union> {{}}"
  then obtain xs where "X = {} \<or> (xs \<in> lists S \<and> X = sstart S xs)"
    by auto
  moreover have "emeasure M (streams S) = 1"
    using ae by (intro prob_space.emeasure_eq_1_AE[OF P(1)]) (auto simp: sets_M streams_sets)
  moreover have "emeasure N (streams S) = 1"
    using ae by (intro prob_space.emeasure_eq_1_AE[OF P(2)]) (auto simp: sets_N streams_sets)
  ultimately show "emeasure M X = emeasure N X"
    using P[THEN prob_space.emeasure_space_1]
    by (cases "xs = []") (auto simp: * space_stream_space del: in_listsD)
qed (auto simp: * ae sets_M del: in_listsD intro!: streams_sets)

lemma measure_density_const:
  "A \<in> sets M \<Longrightarrow> 0 \<le> c \<Longrightarrow> c \<noteq> \<infinity> \<Longrightarrow> measure (density M (\<lambda>_. c)) A = real c * measure M A"
  by (auto simp: emeasure_density_const measure_def)

lemma (in prob_space) measure_uniform_measure_eq_cond_prob:
  assumes [measurable]: "Measurable.pred M P" "Measurable.pred M Q"
  shows "\<P>(x in uniform_measure M {x\<in>space M. Q x}. P x) = \<P>(x in M. P x \<bar> Q x)"
proof cases
  assume Q: "measure M {x\<in>space M. Q x} = 0"
  then have "AE x in M. \<not> Q x"
    by (simp add: prob_eq_0)
  then have "AE x in M. indicator {x\<in>space M. Q x} x / ereal 0 = 0"
    by (auto split: split_indicator)
  from density_cong[OF _ _ this] show ?thesis
    by (simp add: uniform_measure_def emeasure_eq_measure cond_prob_def Q measure_density_const)
qed (auto simp add: emeasure_eq_measure cond_prob_def intro!: arg_cong[where f=prob])

text {*

Markov chain with discrete time steps and discrete state space.

*}

lemma measurable_suntil[measurable]:
  assumes [measurable]: "Measurable.pred (stream_space M) Q" "Measurable.pred (stream_space M) P"
  shows "Measurable.pred (stream_space M) (Q suntil P)"
  unfolding suntil_def by (coinduction rule: measurable_lfp) (auto simp: Order_Continuity.continuous_def)


context
begin

interpretation pmf_as_function .

lemma pmf_eqI: "(\<And>i. pmf M i = pmf N i) \<Longrightarrow> M = N"
  by transfer auto

lemma pmf_eq_iff: "M = N \<longleftrightarrow> (\<forall>i. pmf M i = pmf N i)"
  by (auto intro: pmf_eqI)

end

context
begin

interpretation pmf_as_measure .

lift_definition join_pmf :: "'a pmf pmf \<Rightarrow> 'a pmf" is "\<lambda>M. measure_pmf M \<guillemotright>= measure_pmf"
proof (intro conjI)
  fix M :: "'a pmf pmf"

  have *: "measure_pmf \<in> measurable (measure_pmf M) (subprob_algebra (count_space UNIV))"
    using measurable_measure_pmf[of "\<lambda>x. x"] by simp
  
  interpret bind: prob_space "measure_pmf M \<guillemotright>= measure_pmf"
    apply (rule measure_pmf.prob_space_bind[OF _ *])
    apply (auto intro!: AE_I2)
    apply unfold_locales
    done
  show "prob_space (measure_pmf M \<guillemotright>= measure_pmf)"
    by intro_locales
  show "sets (measure_pmf M \<guillemotright>= measure_pmf) = UNIV"
    by (subst sets_bind[OF *]) auto
  have "AE x in measure_pmf M \<guillemotright>= measure_pmf. emeasure (measure_pmf M \<guillemotright>= measure_pmf) {x} \<noteq> 0"
    by (auto simp add: AE_bind[OF _ *] AE_measure_pmf_iff emeasure_bind[OF _ *]
        nn_integral_0_iff_AE measure_pmf.emeasure_eq_measure measure_le_0 set_pmf_iff pmf.rep_eq)
  then show "AE x in measure_pmf M \<guillemotright>= measure_pmf. measure (measure_pmf M \<guillemotright>= measure_pmf) {x} \<noteq> 0"
    unfolding bind.emeasure_eq_measure by simp
qed

lemma pmf_join: "pmf (join_pmf N) i = (\<integral>M. pmf M i \<partial>measure_pmf N)"
proof (transfer fixing: N i)
  interpret N: subprob_space "measure_pmf N"
    by (rule prob_space_imp_subprob_space) intro_locales
  show "measure (measure_pmf N \<guillemotright>= measure_pmf) {i} = integral\<^sup>L (measure_pmf N) (\<lambda>M. measure M {i})"
    using measurable_measure_pmf[of "\<lambda>x. x"]
    by (intro N.measure_bind[where N="count_space UNIV"]) auto
qed (auto simp: Transfer.Rel_def rel_fun_def cr_pmf_def)

end

lemma sets_measure_pmf_count_space: "sets (measure_pmf M) = sets (count_space UNIV)"
  by simp

definition "bind_pmf M f = join_pmf (map_pmf f M)"

lemma (in pmf_as_measure) bind_transfer[transfer_rule]:
  "rel_fun pmf_as_measure.cr_pmf (rel_fun (rel_fun op = pmf_as_measure.cr_pmf) pmf_as_measure.cr_pmf) op \<guillemotright>= bind_pmf"
proof (auto simp: pmf_as_measure.cr_pmf_def rel_fun_def bind_pmf_def join_pmf.rep_eq map_pmf.rep_eq)
  fix M f and g :: "'a \<Rightarrow> 'b pmf" assume "\<forall>x. f x = measure_pmf (g x)"
  then have f: "f = (\<lambda>x. measure_pmf (g x))"
    by auto
  show "measure_pmf M \<guillemotright>= f = distr (measure_pmf M) (count_space UNIV) g \<guillemotright>= measure_pmf"
    unfolding f by (subst bind_distr[OF _ measurable_measure_pmf]) auto
qed

lemma pmf_bind: "pmf (bind_pmf N f) i = (\<integral>x. pmf (f x) i \<partial>measure_pmf N)"
  by (auto intro!: integral_distr simp: bind_pmf_def pmf_join map_pmf.rep_eq)

lemma return_sets_cong: "sets M = sets N \<Longrightarrow> return M = return N"
  by (auto dest: sets_eq_imp_space_eq simp: fun_eq_iff return_def)

lemma integral_return:
  fixes g :: "_ \<Rightarrow> 'a :: {banach, second_countable_topology}"
  assumes "x \<in> space M" "g \<in> borel_measurable M"
  shows "(\<integral>a. g a \<partial>return M x) = g x"
proof-
  interpret prob_space "return M x" by (rule prob_space_return[OF `x \<in> space M`])
  have "(\<integral>a. g a \<partial>return M x) = (\<integral>a. g x \<partial>return M x)" using assms
    by (intro integral_cong_AE) (auto simp: AE_return)
  then show ?thesis
    using prob_space by simp
qed

lemma integral_pmf_restrict:
  "(f::'a \<Rightarrow> 'b::{banach, second_countable_topology}) \<in> borel_measurable (count_space UNIV) \<Longrightarrow>
    (\<integral>x. f x \<partial>measure_pmf M) = (\<integral>x. f x \<partial>restrict_space M M)"
  by (auto intro!: integral_cong_AE simp add: integral_restrict_space AE_measure_pmf_iff)

lemma sets_restrict_space_cong: "sets M = sets N \<Longrightarrow> sets (restrict_space M \<Omega>) = sets (restrict_space N \<Omega>)"
  by (simp add: sets_restrict_space)

context
begin

interpretation pmf_as_measure .

lift_definition return_pmf :: "'a \<Rightarrow> 'a pmf" is "return (count_space UNIV)"
  by (auto intro!: prob_space_return simp: AE_return measure_return)

lemma join_return_pmf: "join_pmf (return_pmf M) = M"
  by (simp add: integral_return pmf_eq_iff pmf_join return_pmf.rep_eq)

lemma map_return_pmf: "map_pmf f (return_pmf x) = return_pmf (f x)"
  by transfer (simp add: distr_return)

lemma bind_return_pmf: "bind_pmf (return_pmf x) f = f x"
  unfolding bind_pmf_def map_return_pmf join_return_pmf ..

lemma bind_return_pmf': "bind_pmf N return_pmf = N"
proof (transfer, clarify)
  fix N :: "'a measure" assume "sets N = UNIV" then show "N \<guillemotright>= return (count_space UNIV) = N"
    by (subst return_sets_cong[where N=N]) (simp_all add: bind_return')
qed

lemma bind_return_pmf'': "bind_pmf N (\<lambda>x. return_pmf (f x)) = map_pmf f N"
proof (transfer, clarify)
  fix N :: "'b measure" and f :: "'b \<Rightarrow> 'a" assume "prob_space N" "sets N = UNIV"
  then show "N \<guillemotright>= (\<lambda>x. return (count_space UNIV) (f x)) = distr N (count_space UNIV) f"
    by (subst bind_return_distr[symmetric])
       (auto simp: prob_space.not_empty measurable_def comp_def)
qed

lemma bind_assoc_pmf: "bind_pmf (bind_pmf A B) C = bind_pmf A (\<lambda>x. bind_pmf (B x) C)"
  by transfer
     (auto intro!: bind_assoc[where N="count_space UNIV" and R="count_space UNIV"]
           simp: measurable_def space_subprob_algebra prob_space_imp_subprob_space)

lemma bind_commute_pmf: "bind_pmf A (\<lambda>x. bind_pmf B (C x)) = bind_pmf B (\<lambda>y. bind_pmf A (\<lambda>x. C x y))"
  unfolding pmf_eq_iff pmf_bind
proof
  fix i
  interpret B: prob_space "restrict_space B B"
    by (intro prob_space_restrict_space measure_pmf.emeasure_eq_1_AE)
       (auto simp: AE_measure_pmf_iff)
  interpret A: prob_space "restrict_space A A"
    by (intro prob_space_restrict_space measure_pmf.emeasure_eq_1_AE)
       (auto simp: AE_measure_pmf_iff)

  interpret AB: pair_prob_space "restrict_space A A" "restrict_space B B"
    by unfold_locales

  have "(\<integral> x. \<integral> y. pmf (C x y) i \<partial>B \<partial>A) = (\<integral> x. (\<integral> y. pmf (C x y) i \<partial>restrict_space B B) \<partial>A)"
    by (rule integral_cong) (auto intro!: integral_pmf_restrict)
  also have "\<dots> = (\<integral> x. (\<integral> y. pmf (C x y) i \<partial>restrict_space B B) \<partial>restrict_space A A)"
    apply (intro integral_pmf_restrict B.borel_measurable_lebesgue_integral)
    apply (auto simp: measurable_split_conv)
    apply (subst measurable_cong_sets)
    apply (rule sets_pair_measure_cong sets_restrict_space_cong sets_measure_pmf_count_space refl)+
    apply (simp add: restrict_count_space)
    apply (rule measurable_compose_countable'[OF _ measurable_snd])
    apply (rule measurable_compose[OF measurable_fst])
    apply (auto intro: countable_set_pmf)
    done
  also have "\<dots> = (\<integral> y. \<integral> x. pmf (C x y) i \<partial>restrict_space A A \<partial>restrict_space B B)"
    apply (rule AB.Fubini_integral[symmetric])
    apply (auto intro!: AB.integrable_const_bound[where B=1] simp: pmf_nonneg pmf_le_1)
    apply (auto simp: measurable_split_conv)
    apply (subst measurable_cong_sets)
    apply (rule sets_pair_measure_cong sets_restrict_space_cong sets_measure_pmf_count_space refl)+
    apply (simp add: restrict_count_space)
    apply (rule measurable_compose_countable'[OF _ measurable_snd])
    apply (rule measurable_compose[OF measurable_fst])
    apply (auto intro: countable_set_pmf)
    done
  also have "\<dots> = (\<integral> y. \<integral> x. pmf (C x y) i \<partial>restrict_space A A \<partial>B)"
    apply (intro integral_pmf_restrict[symmetric] A.borel_measurable_lebesgue_integral)
    apply (auto simp: measurable_split_conv)
    apply (subst measurable_cong_sets)
    apply (rule sets_pair_measure_cong sets_restrict_space_cong sets_measure_pmf_count_space refl)+
    apply (simp add: restrict_count_space)
    apply (rule measurable_compose_countable'[OF _ measurable_snd])
    apply (rule measurable_compose[OF measurable_fst])
    apply (auto intro: countable_set_pmf)
    done
  also have "\<dots> = (\<integral> y. \<integral> x. pmf (C x y) i \<partial>A \<partial>B)"
    by (rule integral_cong) (auto intro!: integral_pmf_restrict[symmetric])
  finally show "(\<integral> x. \<integral> y. pmf (C x y) i \<partial>B \<partial>A) = (\<integral> y. \<integral> x. pmf (C x y) i \<partial>A \<partial>B)" .
qed

lemma measure_pmf_bind: "measure_pmf (bind_pmf M f) = (measure_pmf M \<guillemotright>= (\<lambda>x. measure_pmf (f x)))"
  by transfer simp

end

locale MC_syntax =
  fixes K :: "'s \<Rightarrow> 's pmf"
begin

coinductive enabled where
  "enabled (shd \<omega>) (stl \<omega>) \<Longrightarrow> shd \<omega> \<in> K s \<Longrightarrow> enabled s \<omega>"

lemma alw_enabled: "enabled (shd \<omega>) (stl \<omega>) \<Longrightarrow> alw (\<lambda>\<omega>. enabled (shd \<omega>) (stl \<omega>)) \<omega>"
  by (coinduction arbitrary: \<omega> rule: alw_coinduct) (auto elim: enabled.cases)

abbreviation "S \<equiv> stream_space (count_space UNIV)"

inductive_simps enabled_iff: "enabled s \<omega>"

lemma measurable_enabled[measurable]:
  "Measurable.pred (stream_space (count_space UNIV)) (enabled s)" (is "Measurable.pred ?S _")
  unfolding enabled_def
proof (coinduction arbitrary: s rule: measurable_gfp2)
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
  by (coinduction arbitrary: s \<omega>) (auto simp: some_in_iff set_pmf_not_empty)

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
      by (fastforce simp add: sdrop.simps[symmetric] some_in_iff set_pmf_not_empty
                    simp del: sdrop.simps intro: rtrancl_into_rtrancl measurable_g[OF _ stl])
  qed
  then show ?thesis
    by (simp add: g_def n_def)
qed

definition T :: "'s \<Rightarrow> 's stream measure" where
  "T s = distr (stream_space (\<Pi>\<^sub>M s\<in>UNIV. K s)) S (walk s)"

lemma space_T[simp]: "space (T s) = space S"
  by (simp add: T_def)

lemma sets_T[simp]: "sets (T s) = sets S"
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
    by (subst (1 2) mult.commute) (auto intro!: SUP_ereal_cmult)
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
    by (simp add: infinite_iff_alw_ev[where P="\<lambda>x. x = b" for b] )
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

partial_function (gfp) hitting_time :: "'s set \<Rightarrow> 's stream \<Rightarrow> enat" where
  "hitting_time X \<omega> = (if HLD X \<omega> then 0 else eSuc (hitting_time X (stl \<omega>)))"

lemma measurable_hitting_time[measurable]: "hitting_time X \<in> measurable S (count_space UNIV)"
  apply (coinduction rule: measurable_enat_coinduct)
  apply simp
  apply (rule exI[of _ "\<lambda>x. 0"])
  apply (rule exI[of _ stl])
  apply (rule exI[of _ "HLD X"])
  apply (subst hitting_time.simps[abs_def])
  apply simp
  apply measurable
  done

lemma hitting_time_eq_0: "hitting_time X \<omega> = 0 \<longleftrightarrow> HLD X \<omega>"
  by (subst hitting_time.simps) auto

lemma hitting_time_HLD[simp]: "HLD X \<omega> \<Longrightarrow> hitting_time X \<omega> = 0"
  by (subst hitting_time.simps) auto

lemma hitting_time_nHLD[simp]: "\<not> HLD X \<omega> \<Longrightarrow> hitting_time X \<omega> = eSuc (hitting_time X (stl \<omega>))"
  by (subst hitting_time.simps) auto

lemma less_hitting_timeD:
  fixes n :: nat
  assumes "n < hitting_time X \<omega>" shows "\<omega> !! n \<notin> X"
  using assms
proof (induction n arbitrary: \<omega>)
  case (Suc n) then show ?case
    by (auto simp: hitting_time.simps[of _ \<omega>] eSuc_enat[symmetric] split: split_if_asm)
qed (simp add: enat_0 hitting_time_eq_0 HLD_iff)

lemma AE_T_max_hitting_time:
  assumes AE: "AE \<omega> in T c. hitting_time X (c ## \<omega>) < \<infinity>" and "0 < e"
  shows "\<exists>N::nat. \<P>(\<omega> in T c. N < hitting_time X (c ## \<omega>)) < e" (is "\<exists>N. ?P N < e")
proof -
  have "?P ----> measure (T c) (\<Inter>N::nat. {bT \<in> space (T c). N < hitting_time X (c ## bT)})"
    using dual_order.strict_trans enat_ord_simps(2)
    by (intro T.finite_Lim_measure_decseq) (force simp: decseq_Suc_iff simp del: enat_ord_simps)+
  also have "measure (T c) (\<Inter>N::nat. {bT \<in> space (T c). N < hitting_time X (c ## bT)}) =
      \<P>(bT in T c. hitting_time X (c ## bT) = \<infinity>)"
    by (auto simp del: not_infinity_eq intro!: arg_cong[where f="measure (T c)"])
       (metis less_irrefl not_infinity_eq)
  also have "\<P>(bT in T c. hitting_time X (c ## bT) = \<infinity>) = 0"
    using AE by (intro T.prob_eq_0_AE) auto
  finally have "\<exists>N. \<forall>n\<ge>N. norm (?P n - 0) < e"
    using `0 < e` by (rule LIMSEQ_D)
  then show ?thesis
    by (auto simp: measure_nonneg)
qed

lemma hitting_time_finite: "hitting_time H \<omega> < \<infinity> \<longleftrightarrow> ev (HLD H) \<omega>"
proof
  assume "hitting_time H \<omega> < \<infinity>"
  then obtain n where "hitting_time H \<omega> = enat n" by auto
  then show "ev (HLD H) \<omega>"
  proof (induction n arbitrary: \<omega>)
    case (Suc n) then show ?case
      by (auto simp add: eSuc_enat[symmetric] hitting_time.simps[of H \<omega>] split: split_if_asm)
  qed (auto simp add: enat_0 hitting_time_eq_0)
next
  assume "ev (HLD H) \<omega>" then show "hitting_time H \<omega> < \<infinity>"
    by (induction rule: ev_induct_strong) (auto simp: eSuc_enat)
qed

lemma hitting_time_Stream: "hitting_time X (s ## x) = (if s \<in> X then 0 else eSuc (hitting_time X x))"
  by (subst hitting_time.simps) (simp add: HLD_iff)

lemma less_hitting_time_iff:
  "(not (HLD X) until (alw (HLD X))) \<omega> \<Longrightarrow> n < hitting_time X \<omega> \<longleftrightarrow> \<omega> !! n \<notin> X"
proof (induction n arbitrary: \<omega>)
  case 0 then show ?case
    by (simp add: enat_0 hitting_time_eq_0 HLD_iff)
next
  case (Suc n)
  from Suc.prems have **: "HLD X \<omega> \<Longrightarrow> HLD X (stl \<omega>)"
    by (auto elim: UNTIL.cases)
  have *: "stl \<omega> !! n \<notin> X \<longleftrightarrow> enat n < hitting_time X (stl \<omega>)"
    using Suc.prems by (intro Suc.IH[symmetric]) (auto intro: UNTIL.intros elim: UNTIL.cases)
  show ?case
    unfolding snth.simps * by (cases "HLD X \<omega>") (simp_all add: ** eSuc_enat[symmetric])
qed

lemma nn_integral_hitting_time_finite:
  assumes [simp]: "finite ((SIGMA x:- H. set_pmf (K x) - H)\<^sup>* `` {s})" (is "finite (?R `` {s})")
  assumes until: "AE \<omega> in T s. ev (HLD H) \<omega>"
  shows "(\<integral>\<^sup>+ \<omega>. hitting_time H (s ## \<omega>) \<partial>T s) \<noteq> \<infinity>"
proof cases
  assume "s \<in> H" then show ?thesis
    by (simp add: hitting_time.simps)
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

  have "(\<integral>\<^sup>+ \<omega>. hitting_time H (s ## \<omega>) \<partial>T s) = (\<Sum>i. ?M s (\<lambda>\<omega>. i < hitting_time H (s ## \<omega>)))"
    by (intro nn_integral_enat_function) simp
  also have "\<dots> \<le> (\<Sum>i. ereal (d^(i div n)))"
  proof (intro suminf_le_pos emeasure_nonneg)
    fix N
    def i \<equiv> "N div n"
    def t \<equiv> "s"
    then have "(s, t) \<in> ?R"
      by simp
    have "\<And>\<omega>. enat N < hitting_time H (s ## \<omega>) \<Longrightarrow> enat (i * n) < hitting_time H (s ## \<omega>)"
      by (metis le_add1 mod_div_equality i_def enat_ord_code(1) le_less_trans)
    then have "?M s (\<lambda>\<omega>. enat N < hitting_time H (s ## \<omega>)) \<le> ?M t (\<lambda>\<omega>. enat (i * n) < hitting_time H (t ## \<omega>))"
      unfolding t_def by (intro emeasure_mono Collect_mono) (auto simp: i_def)
    also have "\<dots> \<le> ereal (d ^ i)"
      using `(s, t) \<in> ?R`
    proof (induction i arbitrary: t)
      case 0 then show ?case
        using T.emeasure_space_1
        by (cases "t \<in> H") (simp_all add: hitting_time_Stream zero_enat_def[symmetric])
    next
      case (Suc i)
      def j \<equiv> "i * n"
      have [simp, arith]: "0 \<le> d ^ i"
        by (auto simp add: field_simps intro!: ereal_0_le_mult zero_le_power)
        
      { fix \<omega> have "enat (n + j) < hitting_time H \<omega> \<longleftrightarrow> X n \<omega> \<and> enat j < hitting_time H (sdrop n \<omega>)"
        proof (induct n arbitrary: \<omega>)
          case (Suc n) then show ?case
            by (cases \<omega>) (simp add: hitting_time_Stream eSuc_enat[symmetric] X_simps)
        qed (simp add: X_simps) }
      then have "?M t (\<lambda>\<omega>. enat (Suc i * n) < hitting_time H (t ## \<omega>))
        = ?M t (\<lambda>\<omega>. X n (t ## \<omega>) \<and> enat j < hitting_time H (sdrop n (t ## \<omega>)))"
        by (simp add: j_def)
      also have "\<dots> \<le> ?M t (\<lambda>\<omega>. X n (t ## \<omega>)) * ereal (d ^ i)"
        using Suc.prems
      proof (induction n arbitrary: t)
        case (0 t) then show ?case
          using Suc.IH[of t] T.emeasure_space_1 `d < 1`
          by (auto simp add: X_simps hitting_time_Stream j_def)
      next
        case (Suc n s)
        show ?case
        proof cases
          assume "s \<notin> H"
          then have "?M s (\<lambda>\<omega>. X (Suc n) (s ## \<omega>) \<and> enat j < hitting_time H (sdrop (Suc n) (s ## \<omega>)))
            = (\<integral>\<^sup>+t. ?M t (\<lambda>\<omega>. X n (t ## \<omega>) \<and> enat j < hitting_time H (sdrop n (t ## \<omega>))) \<partial>K s)"
            by (subst emeasure_Collect_T) (auto simp add: X_simps)
          also have "\<dots> \<le> (\<integral>\<^sup>+t. ?M t (\<lambda>\<omega>. X n (t ## \<omega>)) * ereal (d ^ i) \<partial>K s)"
            using `d < 1` `s \<notin> H`
            apply (intro nn_integral_mono_AE)
            apply (auto simp add: X_simps hitting_time_Stream emeasure_nonneg AE_measure_pmf_iff)
            apply (case_tac "y \<in> H")
            apply (cases n)
            apply (auto simp add: X_simps hitting_time_Stream intro!: ereal_0_le_mult) []
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
    finally show "emeasure (T s) {\<omega> \<in> space (T s). enat N < hitting_time H (s ## \<omega>)} \<le> ereal (d ^ i)" .
  qed
  also have "\<dots> < \<infinity>"
  proof cases
    assume "d = 0"
    with `1 \<le> n` have "summable (\<lambda>i. d ^ (i div n))"
      by (auto simp add: power_0_left div_eq_zero_iff)
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

lemma (in MC_syntax) emeasure_suntil_sums:
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
        using Suc Y by (intro nn_integral_cong mult_indicator_cong) auto
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

end

lemma integrable_measure_pmf_finite:
  fixes f :: "'a \<Rightarrow> 'b::{banach, second_countable_topology}"
  shows "finite (set_pmf M) \<Longrightarrow> integrable M f"
  by (auto intro!: integrableI_bounded simp: nn_integral_measure_pmf_finite)

lemma integral_indicator_finite_real: (*TBD: generalize*)
  fixes f :: "'a \<Rightarrow> real"
  assumes [simp]: "finite A"
  assumes [measurable]: "\<And>a. a \<in> A \<Longrightarrow> {a} \<in> sets M"
  assumes finite: "\<And>a. a \<in> A \<Longrightarrow> emeasure M {a} < \<infinity>"
  shows "(\<integral>x. f x * indicator A x \<partial>M) = (\<Sum>a\<in>A. f a * measure M {a})"
proof -
  have "(\<integral>x. f x * indicator A x \<partial>M) = (\<integral>x. (\<Sum>a\<in>A. f a * indicator {a} x) \<partial>M)"
  proof (intro integral_cong refl)
    fix x show "f x * indicator A x = (\<Sum>a\<in>A. f a * indicator {a} x)"
      by (auto split: split_indicator simp: eq_commute[of x] cong: conj_cong)
  qed
  also have "\<dots> = (\<Sum>a\<in>A. f a * measure M {a})"
    using finite by (subst integral_setsum) (auto simp add: integrable_mult_left_iff)
  finally show ?thesis .
qed

lemma integral_measure_pmf:
  assumes [simp]: "finite A" and "\<And>a. a \<in> set_pmf M \<Longrightarrow> f a \<noteq> 0 \<Longrightarrow> a \<in> A"
  shows "(\<integral>x. f x \<partial>measure_pmf M) = (\<Sum>a\<in>A. f a * pmf M a)"
proof -
  have "(\<integral>x. f x \<partial>measure_pmf M) = (\<integral>x. f x * indicator A x \<partial>measure_pmf M)"
    using assms(2) by (intro integral_cong_AE) (auto split: split_indicator simp: AE_measure_pmf_iff)
  also have "\<dots> = (\<Sum>a\<in>A. f a * pmf M a)"
    by (subst integral_indicator_finite_real) (auto simp: measure_def emeasure_measure_pmf_finite)
  finally show ?thesis .
qed

lemma (in MC_syntax) prob_T:
  assumes P: "Measurable.pred S P"
  shows "\<P>(\<omega> in T s. P \<omega>) = (\<integral>t. \<P>(\<omega> in T t. P (t ## \<omega>)) \<partial>K s)"
  using emeasure_Collect_T[OF P, of s] unfolding T.emeasure_eq_measure
  by (subst (asm) nn_integral_eq_integral)
     (auto intro!: measure_pmf.integrable_const_bound[where B=1] simp: measure_nonneg)

lemma Sigma_empty_iff: "(SIGMA i:I. X i) = {} \<longleftrightarrow> (\<forall>i\<in>I. X i = {})"
  by auto

lemma borel_measurable_sup[measurable (raw)]:
  "f \<in> borel_measurable M \<Longrightarrow> g \<in> borel_measurable M \<Longrightarrow>
    (\<lambda>x. sup (f x) (g x)::ereal) \<in> borel_measurable M"
  by simp

lemma borel_measurable_lfp[consumes 1, case_names continuity step]:
  fixes F :: "('a \<Rightarrow> ereal) \<Rightarrow> ('a \<Rightarrow> ereal)"
  assumes "Order_Continuity.continuous F"
  assumes *: "\<And>f. f \<in> borel_measurable M \<Longrightarrow> F f \<in> borel_measurable M"
  shows "lfp F \<in> borel_measurable M"
proof -
  { fix i have "((F ^^ i) (\<lambda>t. \<bottom>)) \<in> borel_measurable M"
      by (induct i) (auto intro!: * simp: bot_fun_def) }
  then have "(\<lambda>x. SUP i. (F ^^ i) (\<lambda>t. \<bottom>) x) \<in> borel_measurable M"
    by measurable
  also have "(\<lambda>x. SUP i. (F ^^ i) (\<lambda>t. \<bottom>) x) = (SUP i. (F ^^ i) bot)"
    by (auto simp add: bot_fun_def)
  also have "(SUP i. (F ^^ i) bot) = lfp F"
    by (rule continuous_lfp[symmetric]) fact
  finally show ?thesis .
qed

lemma lfp_pair:
  "lfp (\<lambda>f (a, b). F (\<lambda>a b. f (a, b)) a b) (a, b) = lfp F a b"
  unfolding lfp_def
  apply simp
  unfolding INF_def
  apply (intro arg_cong[where f=Inf])
  apply (auto simp: le_fun_def image_Collect)
  apply (rule_tac x = "\<lambda>(a, b). u a b" in exI)
  apply auto
  done

lemma SUP_ereal_add_right:
  fixes c :: ereal
  shows "I \<noteq> {} \<Longrightarrow> (\<And>i. i \<in> I \<Longrightarrow> 0 \<le> f i) \<Longrightarrow> 0 \<le> c \<Longrightarrow> (\<Squnion>i\<in>I. c + f i) = c + SUPREMUM I f"
  using SUP_ereal_add_left[of I f c] by (simp add: add_ac)

lemma (in MC_syntax) T_subprob: "T \<in> measurable (measure_pmf I) (subprob_algebra S)"
  by (auto intro!: space_bind simp: space_subprob_algebra) unfold_locales

context MC_syntax
begin

text {* Markov chain with initial distribution @{term_type "I::'s pmf"}: *}

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
  by (simp add: T'_def sets_bind[OF distr_Stream_subprob])

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

end

lemma (in MC_syntax) T_eq_bind: "T s = (measure_pmf (K s) \<guillemotright>= (\<lambda>t. distr (T t) S (op ## t)))"
  by (subst T_eq_T') (simp add: T'_def)

declare (in MC_syntax) T_subprob[measurable]

lemma (in MC_syntax) T_split:
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
  note sets_stream_space_cong[simp]

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
    apply (subst bind_assoc[OF measurable_distr2[where M=S] measurable_distr2[where M=S], OF _ T_subprob])
    apply (simp_all add: space_stream_space del: stake.simps)
    apply measurable
    apply (rule sets_pair_measure_cong[OF _ refl])
    apply auto
    done
  finally show ?case
    by simp
qed

lemma (in MC_syntax) nn_integral_T_split:
  assumes f[measurable]: "f \<in> borel_measurable S" "\<And>x. 0 \<le> f x"
  shows "(\<integral>\<^sup>+\<omega>. f \<omega> \<partial>T s) = (\<integral>\<^sup>+\<omega>. (\<integral>\<^sup>+\<omega>'. f (stake n \<omega> @- \<omega>') \<partial>T ((s ## \<omega>) !! n)) \<partial>T s)"
  apply (subst T_split[of s n])
  apply (subst nn_integral_bind[OF f measurable_distr2[where M=S]])
  apply measurable
  apply (rule sets_stream_space_cong)
  apply simp
  apply (subst nn_integral_distr)
  apply (simp_all add: space_stream_space)
  done

lemma (in MC_syntax) emeasure_T_split:
  assumes P[measurable]: "Measurable.pred S P"
  shows "emeasure (T s) {\<omega>\<in>space (T s). P \<omega>} =
      (\<integral>\<^sup>+\<omega>. emeasure (T ((s ## \<omega>) !! n)) {\<omega>'\<in>space (T ((s ## \<omega>) !! n)). P (stake n \<omega> @- \<omega>')} \<partial>T s)"
  apply (subst T_split[of s n])
  apply (subst emeasure_bind[OF _ measurable_distr2[where M=S]])
  apply (simp_all add: )
  apply (simp add: space_stream_space)
  apply measurable
  apply (rule sets_stream_space_cong)
  apply simp
  apply (subst emeasure_distr)
  apply simp_all
  apply (simp_all add: space_stream_space)
  done

lemma SIGMA_Collect_eq: "(SIGMA x:space M. {y\<in>space N. P x y}) = {x\<in>space (M \<Otimes>\<^sub>M N). P (fst x) (snd x)}"
  by (auto simp: space_pair_measure)

lemma (in MC_syntax) prob_T_split:
  assumes P[measurable]: "Measurable.pred S P"
  shows "\<P>(\<omega> in T s. P \<omega>) = (\<integral>\<omega>. \<P>(\<omega>' in T ((s ## \<omega>) !! n). P (stake n \<omega> @- \<omega>')) \<partial>T s)"
  unfolding T.emeasure_eq_measure[symmetric] ereal.inject[symmetric] emeasure_T_split[OF P, of s n]
  apply (auto intro!: nn_integral_eq_integral T.integrable_const_bound[where B=1]
                      measure_measurable_subprob_algebra2[where N=S]
              simp: measure_nonneg T.emeasure_eq_measure SIGMA_Collect_eq)
  apply (rule measurable_compose[OF _ T_subprob])
  apply simp
  done

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

lemma hitting_time_simps[simp]:
  shows "shd \<omega> \<in> H \<Longrightarrow> hitting_time H \<omega> = 0"
    and "shd \<omega> \<notin> H \<Longrightarrow> hitting_time H \<omega> = eSuc (hitting_time H (stl \<omega>))"
  using hitting_time_Stream[of H "shd \<omega>" "stl \<omega>"] by auto

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

  have "AE \<omega> in T s. reward_until H s \<omega> \<le> M * hitting_time H (s ## \<omega>)"
    using ev AE_T_enabled
  proof eventually_elim
    fix \<omega> assume "ev (HLD H) \<omega>" "enabled s \<omega>"
    moreover def t\<equiv>"s"
    ultimately have "ev (HLD H) \<omega>" "enabled t \<omega>" "t \<in> ?L``{s}"
      by auto
    then show "reward_until H t \<omega> \<le> M * hitting_time H (t ## \<omega>)"
    proof (induction arbitrary: t rule: ev_induct_strong)
      case (base \<omega> t) then show ?case
        by (auto simp: HLD_iff hitting_time_Stream elim: enabled.cases intro: le_M)
    next
      case (step \<omega> t) from step.IH[of "shd \<omega>"] step.prems step.hyps show ?case
        by (auto simp add: HLD_iff enabled.simps[of t] ereal_right_distrib hitting_time_Stream
                           reward_until_simps[of t]
                 simp del: reward_until_simps hitting_time_simps
                 intro!: ereal_add_mono le_M intro: rtrancl_into_rtrancl)
    qed
  qed
  then have "(\<integral>\<^sup>+\<omega>. reward_until H s \<omega> \<partial>T s) \<le> (\<integral>\<^sup>+\<omega>. M * hitting_time H (s ## \<omega>) \<partial>T s)"
    by (rule nn_integral_mono_AE)
  also have "\<dots> < \<infinity>"
    using `0 \<le> M` `M < \<infinity>` nn_integral_hitting_time_finite[OF fin_L ev]
    by (simp add: nn_integral_cmult not_less nn_integral_nonneg)
  finally show ?thesis
    by simp
qed

end

lemma (in MC_syntax) enabled_imp_alw:
  "(\<Union>s\<in>X. K s) \<subseteq> X \<Longrightarrow> x \<in> X \<Longrightarrow> enabled x \<omega> \<Longrightarrow> alw (HLD X) \<omega>"
proof (coinduction arbitrary: \<omega> x)
  case alw then show ?case
    unfolding enabled.simps[of _ \<omega>]
    by (auto simp: HLD_iff)
qed

lemma (in MC_syntax) alw_HLD_iff_sconst:
  "alw (HLD {x}) \<omega> \<longleftrightarrow> \<omega> = sconst x"
proof
  assume "alw (HLD {x}) \<omega>" then show "\<omega> = sconst x"
    by (coinduction arbitrary: \<omega>) (auto simp: HLD_iff)
qed (auto simp: alw_sconst HLD_iff)

lemma (in MC_syntax) enabled_iff_sconst:
  assumes [simp]: "set_pmf (K x) = {x}" shows "enabled x \<omega> \<longleftrightarrow> \<omega> = sconst x"
proof
  assume "enabled x \<omega>" then show "\<omega> = sconst x"
    by (coinduction arbitrary: \<omega>) (auto elim: enabled.cases)
next
  assume "\<omega> = sconst x" then show "enabled x \<omega>"
    by (coinduction arbitrary: \<omega>) auto
qed

lemma (in MC_syntax) AE_sconst:
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

(* hitting_time should be part of the Stream library, call if sfirst  *)
lemma (in MC_syntax) hitting_time_eq_Inf: "hitting_time X \<omega> = Inf {enat i | i. \<omega> !! i \<in> X}"
proof (rule antisym)
  show "hitting_time X \<omega> \<le> \<Sqinter>{enat i |i. \<omega> !! i \<in> X}"
  proof (safe intro!: Inf_greatest)
    fix \<omega> i assume "\<omega> !! i \<in> X" then show "hitting_time X \<omega> \<le> enat i"
    proof (induction i arbitrary: \<omega>)
      case (Suc i) then show ?case
       by (auto simp add: hitting_time.simps[of X \<omega>] HLD_iff eSuc_enat[symmetric])
    qed (auto simp: HLD_iff)
  qed
  show "\<Sqinter>{enat i |i. \<omega> !! i \<in> X} \<le> hitting_time X \<omega>"
  proof (induction arbitrary: \<omega> rule: hitting_time.fixp_induct)
    case (3 f)
    have "{enat i |i. \<omega> !! i \<in> X} = (if HLD X \<omega> then {0} else {}) \<union> eSuc ` {enat i |i. stl \<omega> !! i \<in> X}"
      by (cases \<omega>) (force simp add: Stream_snth enat_0 eSuc_enat gr0_conv_Suc split: nat.splits)
    with 3[of "stl \<omega>"] show ?case
      by (auto simp: inf.absorb1 eSuc_Inf[symmetric] simp del: Inf_image_eq)
  qed simp_all
qed

lemma snth_Stream: "(x ## s) !! Suc i = s !! i"
  by simp

lemma map_pmf_comp: "map_pmf f (map_pmf g M) = map_pmf (\<lambda>x. f (g x)) M"
  using map_pmf_compose[of f g] by (simp add: comp_def)

lemma set_map_pmf: "set_pmf (map_pmf f M) = f`set_pmf M"
  using pmf_set_map[of f] by (auto simp: comp_def fun_eq_iff)

abbreviation (in MC_syntax) accessible :: "('s \<times> 's) set" where
  "accessible \<equiv> (SIGMA s:UNIV. K s)\<^sup>*"

lemma (in MC_syntax) countable_accessible: "countable X \<Longrightarrow> countable (accessible `` X)"
  apply (rule countable_Image)
  apply (rule countable_reachable)
  apply assumption
  done

lemma integrable_pmf: "integrable (count_space X) (pmf M)"
proof -
  have " (\<integral>\<^sup>+ x. pmf M x \<partial>count_space X) = (\<integral>\<^sup>+ x. pmf M x \<partial>count_space (M \<inter> X))"
    by (auto simp add: nn_integral_count_space_indicator set_pmf_iff intro!: nn_integral_cong split: split_indicator)
  then have "integrable (count_space X) (pmf M) = integrable (count_space (M \<inter> X)) (pmf M)"
    by (simp add: integrable_iff_bounded pmf_nonneg)
  then show ?thesis
    by (simp add: pmf.rep_eq measure_pmf.integrable_measure countable_set_pmf disjoint_family_on_def)
qed

lemma integral_pmf: "(\<integral>x. pmf M x \<partial>count_space X) = measure M X"
proof -
  have "(\<integral>x. pmf M x \<partial>count_space X) = (\<integral>\<^sup>+x. pmf M x \<partial>count_space X)"
    by (simp add: pmf_nonneg integrable_pmf nn_integral_eq_integral)
  also have "\<dots> = (\<integral>\<^sup>+x. emeasure M {x} \<partial>count_space (X \<inter> M))"
    by (auto intro!: nn_integral_cong_AE split: split_indicator
             simp: pmf.rep_eq measure_pmf.emeasure_eq_measure nn_integral_count_space_indicator
                   AE_count_space set_pmf_iff)
  also have "\<dots> = emeasure M (X \<inter> M)"
    by (rule emeasure_countable_singleton[symmetric]) (auto intro: countable_set_pmf)
  also have "\<dots> = emeasure M X"
    by (auto intro!: emeasure_eq_AE simp: AE_measure_pmf_iff)
  finally show ?thesis
    by (simp add: measure_pmf.emeasure_eq_measure)
qed

lemma (in -) ev_at_shift:
  "ev_at (HLD X) i (stake (Suc i) \<omega> @- \<omega>' :: 's stream) \<longleftrightarrow> ev_at (HLD X) i \<omega>"
  by (induction i arbitrary: \<omega>) (auto simp: HLD_iff)

lemma atMost_Suc_insert_0: "{.. Suc n} = insert 0 (Suc ` {.. n})"
  apply (auto simp: image_iff Ball_def)
  apply (case_tac x)
  apply auto
  done

lemma int_cases': "(\<And>n. x = int n \<Longrightarrow> P) \<Longrightarrow> (\<And>n. x = - int n \<Longrightarrow> P) \<Longrightarrow> P"
  by (metis int_cases)

lemma nat_abs_int_diff: "nat \<bar>int a - int b\<bar> = (if a \<le> b then b - a else a - b)"
  by auto

lemma nat_int_add: "nat (int a + int b) = a + b"
  by auto

lemma measurable_szip:
  "(\<lambda>(\<omega>1, \<omega>2). szip \<omega>1 \<omega>2) \<in> measurable (stream_space M \<Otimes>\<^sub>M stream_space N) (stream_space (M \<Otimes>\<^sub>M N))"
proof (rule measurable_stream_space2)
  fix n
  have "(\<lambda>x. (case x of (\<omega>1, \<omega>2) \<Rightarrow> szip \<omega>1 \<omega>2) !! n) = (\<lambda>(\<omega>1, \<omega>2). (\<omega>1 !! n, \<omega>2 !! n))"
    by auto
  also have "\<dots> \<in> measurable (stream_space M \<Otimes>\<^sub>M stream_space N) (M \<Otimes>\<^sub>M N)"
    by measurable
  finally show "(\<lambda>x. (case x of (\<omega>1, \<omega>2) \<Rightarrow> szip \<omega>1 \<omega>2) !! n) \<in> measurable (stream_space M \<Otimes>\<^sub>M stream_space N) (M \<Otimes>\<^sub>M N)"
    .
qed

definition "pair_pmf A B = bind_pmf A (\<lambda>x. bind_pmf B (\<lambda>y. return_pmf (x, y)))"

lemma restrict_space_measurable:
  assumes X: "X \<noteq> {}" "X \<in> sets K"
  assumes N: "N \<in> measurable M (subprob_algebra K)"
  shows "(\<lambda>x. restrict_space (N x) X) \<in> measurable M (subprob_algebra (restrict_space K X))"
proof (rule measurable_subprob_algebra)
  fix a assume a: "a \<in> space M"
  from N[THEN measurable_space, OF this]
  have "subprob_space (N a)" and [simp]: "sets (N a) = sets K" "space (N a) = space K"
    by (auto simp add: space_subprob_algebra dest: sets_eq_imp_space_eq)
  then interpret subprob_space "N a"
    by simp
  show "subprob_space (restrict_space (N a) X)"
  proof
    show "space (restrict_space (N a) X) \<noteq> {}"
      using X by (auto simp add: space_restrict_space)
    show "emeasure (restrict_space (N a) X) (space (restrict_space (N a) X)) \<le> 1"
      using X by (simp add: emeasure_restrict_space space_restrict_space subprob_measure_le_1)
  qed
  show "sets (restrict_space (N a) X) = sets (restrict_space K X)"
    by (intro sets_restrict_space_cong) fact
next
  fix A assume A: "A \<in> sets (restrict_space K X)"
  show "(\<lambda>a. emeasure (restrict_space (N a) X) A) \<in> borel_measurable M"
  proof (subst measurable_cong)
    fix a assume "a \<in> space M"
    from N[THEN measurable_space, OF this]
    have [simp]: "sets (N a) = sets K" "space (N a) = space K"
      by (auto simp add: space_subprob_algebra dest: sets_eq_imp_space_eq)
    show "emeasure (restrict_space (N a) X) A = emeasure (N a) (A \<inter> X)"
      using X A by (subst emeasure_restrict_space) (auto simp add: sets_restrict_space ac_simps)
  next
    show "(\<lambda>w. emeasure (N w) (A \<inter> X)) \<in> borel_measurable M"
      using A X
      by (intro measurable_compose[OF N measurable_emeasure_subprob_algebra])
         (auto simp: sets_restrict_space)
  qed
qed

lemma restrict_space_bind:
  assumes N: "N \<in> measurable M (subprob_algebra K)"
  assumes "space M \<noteq> {}"
  assumes X[simp]: "X \<in> sets K" "X \<noteq> {}"
  shows "restrict_space (bind M N) X = bind M (\<lambda>x. restrict_space (N x) X)"
proof (rule measure_eqI)
  fix A assume "A \<in> sets (restrict_space (M \<guillemotright>= N) X)"
  with X have "A \<in> sets K" "A \<subseteq> X"
    by (auto simp: sets_restrict_space sets_bind[OF assms(1,2)])
  then show "emeasure (restrict_space (M \<guillemotright>= N) X) A = emeasure (M \<guillemotright>= (\<lambda>x. restrict_space (N x) X)) A"
    using assms
    apply (subst emeasure_restrict_space)
    apply (simp_all add: space_bind[OF assms(1,2)] sets_bind[OF assms(1,2)] emeasure_bind[OF assms(2,1)])
    apply (subst emeasure_bind[OF _ restrict_space_measurable[OF _ _ N]])
    apply (auto simp: sets_restrict_space emeasure_restrict_space space_subprob_algebra
                intro!: nn_integral_cong dest!: measurable_space)
    done
qed (simp add: sets_restrict_space sets_bind[OF assms(1,2)] sets_bind[OF restrict_space_measurable[OF assms(4,3,1)] assms(2)])

lemma return_restrict_space:
  "\<Omega> \<in> sets M \<Longrightarrow> return (restrict_space M \<Omega>) x = restrict_space (return M x) \<Omega>"
  by (auto intro!: measure_eqI simp: sets_restrict_space emeasure_restrict_space)

lemma return_cong: "sets A = sets B \<Longrightarrow> return A x = return B x"
  by (auto simp add: return_def dest: sets_eq_imp_space_eq)

context MC_syntax
begin

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

primcorec force_enabled where
  "force_enabled x \<omega> =
    (let y = if shd \<omega> \<in> K x then shd \<omega> else (SOME y. y \<in> K x) in y ## force_enabled y (stl \<omega>))"

lemma force_enabled_in_set_pmf[simp, intro]: "shd (force_enabled x \<omega>) \<in> K x"
  by (auto simp: some_in_iff set_pmf_not_empty)

lemma enabled_force_enabled: "enabled x (force_enabled x \<omega>)"
  by (coinduction arbitrary: x \<omega>) (auto simp: some_in_iff set_pmf_not_empty)
  
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
      apply (auto simp: countable_set_pmf some_in_iff set_pmf_not_empty)
      done
  qed (auto intro!: measurable_compose[OF measurable_shd])
qed

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
  apply measurable
  apply (intro sets_pair_measure_cong)
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
  assumes sets_M [simp]: "\<And>x. sets (M x) = sets S"
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
               simp: space_stream_space AE_measure_pmf_iff \<Omega>_trans split: split_indicator)
    also have "\<dots> = emeasure (M x) {\<omega>\<in>space (M x). \<omega> \<in> sstart \<Omega> (a # xs)}"
      apply (subst M_eq[of x])
      apply (auto intro!: nn_integral_cong arg_cong2[where f=emeasure]
                  simp add: emeasure_bind[OF _ *] emeasure_distr split: split_indicator)
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


end

lemma (in pair_prob_space) pair_measure_eq_bind:
  "(M1 \<Otimes>\<^sub>M M2) = (M1 \<guillemotright>= (\<lambda>x. M2 \<guillemotright>= (\<lambda>y. return (M1 \<Otimes>\<^sub>M M2) (x, y))))"
proof (rule measure_eqI)
  have ps_M2: "prob_space M2" by unfold_locales
  note return_measurable[measurable]
  have 1: "(\<lambda>x. M2 \<guillemotright>= (\<lambda>y. return (M1 \<Otimes>\<^sub>M M2) (x, y))) \<in> measurable M1 (subprob_algebra (M1 \<Otimes>\<^sub>M M2))"
    by (auto simp add: space_subprob_algebra ps_M2
             intro!: measurable_bind[where N=M2] measurable_const prob_space_imp_subprob_space)
  show "sets (M1 \<Otimes>\<^sub>M M2) = sets (M1 \<guillemotright>= (\<lambda>x. M2 \<guillemotright>= (\<lambda>y. return (M1 \<Otimes>\<^sub>M M2) (x, y))))"
    by (simp add: M1.not_empty sets_bind[OF 1])
  fix A assume [measurable]: "A \<in> sets (M1 \<Otimes>\<^sub>M M2)"
  show "emeasure (M1 \<Otimes>\<^sub>M M2) A = emeasure (M1 \<guillemotright>= (\<lambda>x. M2 \<guillemotright>= (\<lambda>y. return (M1 \<Otimes>\<^sub>M M2) (x, y)))) A"
    by (auto simp: M2.emeasure_pair_measure emeasure_bind[OF _ 1] M1.not_empty
                          emeasure_bind[where N="M1 \<Otimes>\<^sub>M M2"] M2.not_empty
             intro!: nn_integral_cong)
qed

declare return_measurable[measurable]

lemma (in pair_prob_space) bind_rotate:
  assumes C[measurable]: "(\<lambda>(x, y). C x y) \<in> measurable (M1 \<Otimes>\<^sub>M M2) (subprob_algebra N)"
  shows "(M1 \<guillemotright>= (\<lambda>x. M2 \<guillemotright>= (\<lambda>y. C x y))) = (M2 \<guillemotright>= (\<lambda>y. M1 \<guillemotright>= (\<lambda>x. C x y)))"
proof - 
  interpret swap: pair_prob_space M2 M1 by unfold_locales
  note measurable_bind[where N="M2", measurable]
  note measurable_bind[where N="M1", measurable]
  have [simp]: "M1 \<in> space (subprob_algebra M1)" "M2 \<in> space (subprob_algebra M2)"
    by (auto simp: space_subprob_algebra) unfold_locales
  have "(M1 \<guillemotright>= (\<lambda>x. M2 \<guillemotright>= (\<lambda>y. C x y))) = 
    (M1 \<guillemotright>= (\<lambda>x. M2 \<guillemotright>= (\<lambda>y. return (M1 \<Otimes>\<^sub>M M2) (x, y)))) \<guillemotright>= (\<lambda>(x, y). C x y)"
    by (auto intro!: bind_cong simp: bind_return[where N=N] space_pair_measure bind_assoc[where N="M1 \<Otimes>\<^sub>M M2" and R=N])
  also have "\<dots> = (distr (M2 \<Otimes>\<^sub>M M1) (M1 \<Otimes>\<^sub>M M2) (\<lambda>(x, y). (y, x))) \<guillemotright>= (\<lambda>(x, y). C x y)"
    unfolding pair_measure_eq_bind[symmetric] distr_pair_swap[symmetric] ..
  also have "\<dots> = (M2 \<guillemotright>= (\<lambda>x. M1 \<guillemotright>= (\<lambda>y. return (M2 \<Otimes>\<^sub>M M1) (x, y)))) \<guillemotright>= (\<lambda>(y, x). C x y)"
    unfolding swap.pair_measure_eq_bind[symmetric]
    by (auto simp add: space_pair_measure M1.not_empty M2.not_empty bind_distr[OF _ C] intro!: bind_cong)
  also have "\<dots> = (M2 \<guillemotright>= (\<lambda>y. M1 \<guillemotright>= (\<lambda>x. C x y)))"
    by (auto intro!: bind_cong simp: bind_return[where N=N] space_pair_measure bind_assoc[where N="M2 \<Otimes>\<^sub>M M1" and R=N])
  finally show ?thesis .
qed

lemma subprob_algebra_cong: "sets M = sets N \<Longrightarrow> subprob_algebra M = subprob_algebra N"
  unfolding subprob_algebra_def by simp

lemma set_pmf_return: "set_pmf (return_pmf x) = {x}"
  by transfer (auto simp add: measure_return split: split_indicator)

lemma pmf_return: "pmf (return_pmf x) y = indicator {y} x"
  by transfer (simp add: measure_return)

lemma pmf_pair: "pmf (pair_pmf M N) (a, b) = pmf M a * pmf N b"
  unfolding pair_pmf_def pmf_bind pmf_return
  apply (subst integral_measure_pmf[where A="{b}"])
  apply (auto simp: indicator_eq_0_iff)
  apply (subst integral_measure_pmf[where A="{a}"])
  apply (auto simp: indicator_eq_0_iff setsum_nonneg_eq_0_iff pmf_nonneg)
  done

lemma bind_pair_pmf:
  assumes M[measurable]: "M \<in> measurable (count_space UNIV \<Otimes>\<^sub>M count_space UNIV) (subprob_algebra N)"
  shows "measure_pmf (pair_pmf A B) \<guillemotright>= M = (measure_pmf A \<guillemotright>= (\<lambda>x. measure_pmf B \<guillemotright>= (\<lambda>y. M (x, y))))"
    (is "?L = ?R")
proof (rule measure_eqI)
  have M'[measurable]: "M \<in> measurable (pair_pmf A B) (subprob_algebra N)"
    using M[THEN measurable_space] by (simp_all add: space_pair_measure)

  have sets_eq_N: "sets ?L = N"
    by (simp add: sets_bind[OF M'])
  show "sets ?L = sets ?R"
    unfolding sets_eq_N
    apply (subst sets_bind[where N=N])
    apply (rule measurable_bind)
    apply (rule measurable_compose[OF _ measurable_measure_pmf])
    apply measurable
    apply (auto intro!: sets_pair_measure_cong sets_measure_pmf_count_space)
    done
  fix X assume "X \<in> sets ?L"
  then have X[measurable]: "X \<in> sets N"
    unfolding sets_eq_N .
  then show "emeasure ?L X = emeasure ?R X"
    apply (simp add: emeasure_bind[OF _ M' X])
    unfolding pair_pmf_def measure_pmf_bind[of A]
    apply (subst nn_integral_bind[OF _ emeasure_nonneg])
    apply (rule measurable_compose[OF M' measurable_emeasure_subprob_algebra, OF X])
    apply (subst measurable_cong_sets[OF sets_measure_pmf_count_space refl])
    apply (subst subprob_algebra_cong[OF sets_measure_pmf_count_space])
    apply measurable
    unfolding measure_pmf_bind
    apply (subst nn_integral_bind[OF _ emeasure_nonneg])
    apply (rule measurable_compose[OF M' measurable_emeasure_subprob_algebra, OF X])
    apply (subst measurable_cong_sets[OF sets_measure_pmf_count_space refl])
    apply (subst subprob_algebra_cong[OF sets_measure_pmf_count_space])
    apply measurable
    apply (simp add: nn_integral_measure_pmf_finite set_pmf_return emeasure_nonneg pmf_return one_ereal_def[symmetric])
    apply (subst emeasure_bind[OF _ _ X])
    apply simp
    apply (rule measurable_bind[where N="count_space UNIV"])
    apply (rule measurable_compose[OF _ measurable_measure_pmf])
    apply measurable
    apply (rule sets_pair_measure_cong sets_measure_pmf_count_space refl)+
    apply (subst measurable_cong_sets[OF sets_pair_measure_cong[OF sets_measure_pmf_count_space refl] refl])
    apply simp
    apply (subst emeasure_bind[OF _ _ X])
    apply simp
    apply (rule measurable_compose[OF _ M])
    apply (auto simp: space_pair_measure)
    done
qed

lemma (in subprob_space) bind_in_space:
  "A \<in> measurable M (subprob_algebra N) \<Longrightarrow> (M \<guillemotright>= A) \<in> space (subprob_algebra N)"
  by (auto simp add: space_subprob_algebra subprob_not_empty intro!: subprob_space_bind)
     unfold_locales

lemma set_pmf_bind: "set_pmf (bind_pmf M N) = (\<Union>M\<in>set_pmf M. set_pmf (N M))"
  apply (simp add: set_eq_iff set_pmf_iff pmf_bind)
  apply (subst integral_nonneg_eq_0_iff_AE)
  apply (auto simp: pmf_nonneg pmf_le_1 AE_measure_pmf_iff
              intro!: measure_pmf.integrable_const_bound[where B=1])
  done

lemma set_pmf_pair_pmf: "set_pmf (pair_pmf A B) = set_pmf A \<times> set_pmf B"
  unfolding pair_pmf_def set_pmf_bind set_pmf_return by auto

lemma bind_pmf_cong:
  assumes "\<And>x. A x \<in> space (subprob_algebra N)" "\<And>x. B x \<in> space (subprob_algebra N)"
  assumes "\<And>i. i \<in> set_pmf x \<Longrightarrow> A i = B i"
  shows "bind (measure_pmf x) A = bind (measure_pmf x) B"
proof (rule measure_eqI)
  show "sets (measure_pmf x \<guillemotright>= A) = sets (measure_pmf x \<guillemotright>= B)"
    using assms by (subst (1 2) sets_bind) auto
next
  fix X assume "X \<in> sets (measure_pmf x \<guillemotright>= A)"
  then have X: "X \<in> sets N"
    using assms by (subst (asm) sets_bind) auto
  show "emeasure (measure_pmf x \<guillemotright>= A) X = emeasure (measure_pmf x \<guillemotright>= B) X"
    using assms
    by (subst (1 2) emeasure_bind[where N=N, OF _ _ X])
       (auto intro!: nn_integral_cong_AE simp: AE_measure_pmf_iff)
qed

interpretation measure_pmf: subprob_space "measure_pmf M" for M
  by (rule prob_space_imp_subprob_space) unfold_locales

locale Pair_MC =
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
                        measurable_bind[where R=S and N=S] measurable_compose[OF _ return_measurable] AE_I2)
       unfold_locales

  show "sets (?B x) = sets S"
    by (simp split: prod.splits add: measurable_bind[where N=S] sets_bind[where N=S] space_stream_space)
  
  note measurable_bind[where N=S and R=S, measurable]
  obtain a b where x_eq: "x = (a, b)"
    by (cases x) auto
  show "?B x = (measure_pmf (Kp x) \<guillemotright>= (\<lambda>s. distr (?B s) S (op ## s)))"
    unfolding x_eq
    apply (simp add: split_beta' comp_def
       bind_return_distr[symmetric] space_bind[where N=S] space_stream_space measurable_bind[where N=S])
    apply (subst bind_assoc[where R=S])
    apply (rule measurable_bind[where N=S])
    apply measurable
    apply (subst bind_assoc[where R=S and N=S])
    apply measurable
    apply (simp_all add: space_stream_space bind_return[where N=S])
    apply (subst K1.T_eq_bind')
    apply (subst bind_assoc[where R=S])
    apply measurable
    apply (rule sets_pair_measure_cong)
    apply (simp_all add: bind_assoc[where R=S and N=S] bind_return[where N=S] space_stream_space)
    apply (subst K2.T_eq_bind')
    apply (subst bind_assoc[where R=S])
    apply measurable
    apply (rule sets_pair_measure_cong)
    apply (simp_all add: space_stream_space bind_assoc[where R=S and N=S] bind_return[where N=S])
    apply (subst T1K2.bind_rotate[where N=S])
    apply (subst measurable_cong_sets[OF sets_pair_measure_cong, OF K1.sets_T sets_measure_pmf_count_space refl])
    apply measurable back
    apply (simp add: Kp_def)
    apply (subst bind_pair_pmf[of "split M" for M, unfolded split, symmetric])
    unfolding measurable_split_conv
    apply (rule measurable_bind) defer
    apply (rule measurable_bind) defer
    apply (rule measurable_compose[OF _ return_measurable])
    apply measurable
    defer
    apply measurable
    apply (rule sets_pair_measure_cong[OF _ refl])
    apply (simp_all add: split_beta')
    apply (intro bind_pmf_cong subprob_space.bind_in_space[OF T1x]
      measurable_bind)
    apply (rule measurable_compose[OF _ K2.T_subprob])
    apply simp
    apply (rule measurable_compose[OF _ return_measurable])
    apply simp
    apply (rule measurable_compose[OF _ K2.T_subprob])
    apply simp
    apply (rule measurable_compose[OF _ return_measurable])
    apply simp
    apply (intro bind_cong ballI arg_cong2[where f=return] refl)
    apply (auto simp add: szip\<^sub>E_def stream_eq_Stream_iff set_pmf_pair_pmf)
    done
qed

lemma nn_integral_pT: 
  fixes f assumes "f \<in> borel_measurable S" and "\<And>x. 0 \<le> f x"
  shows "(\<integral>\<^sup>+\<omega>. f \<omega> \<partial>T (x, y)) = (\<integral>\<^sup>+\<omega>1. \<integral>\<^sup>+\<omega>2. f (szip\<^sub>E x y (\<omega>1, \<omega>2)) \<partial>K2.T y \<partial>K1.T x)"
  apply (subst T_eq_prod)
  apply simp
  apply (subst nn_integral_bind[OF assms])
  apply (rule measurable_bind)
  apply (rule measurable_compose[OF _ K2.T_subprob'])
  apply measurable
  apply (subst nn_integral_bind[OF assms])
  apply (rule measurable_compose[OF _ return_measurable])
  apply measurable
  apply (simp_all add: space_stream_space)
  apply (subst nn_integral_return)
  using assms
  apply (auto simp: space_stream_space)
  done

lemma prod_eq_prob_T:
  assumes [measurable]: "Measurable.pred K1.S P1" "Measurable.pred K2.S P2"
  shows "\<P>(\<omega> in K1.T x1. P1 \<omega>) * \<P>(\<omega> in K2.T x2. P2 \<omega>) =
    \<P>(\<omega> in T (x1, x2). P1 (smap fst \<omega>) \<and> P2 (smap snd \<omega>))"
proof -
  have "\<P>(\<omega> in T (x1, x2). P1 (smap fst \<omega>) \<and> P2 (smap snd \<omega>)) = 
    (\<integral>\<omega>1. \<integral>\<omega>2. indicator {\<omega>\<in>space K1.S. P1 \<omega>} \<omega>1 * indicator {\<omega>\<in>space K2.S. P2 \<omega>} \<omega>2 \<partial>K2.T x2 \<partial>K1.T x1)"
    apply (subst T_eq_prod)
    unfolding split
    apply (subst K1.T.measure_bind[where N=S])
    apply (intro measurable_bind[where N=S] measurable_compose[OF _ return_measurable] )
    apply measurable
    apply simp
    apply (subst K2.T.measure_bind[where N=S])
    apply (intro measurable_bind[where N=S] measurable_compose[OF _ return_measurable] )
    apply measurable
    apply (simp add: space_stream_space)
    apply measurable
    apply simp
    apply (subst measure_return)
    apply simp
    apply (intro integral_cong_AE)
    apply measurable
    using K1.AE_T_enabled
    apply eventually_elim
    apply (intro integral_cong_AE measurable_compose[OF _ borel_measurable_indicator]
      measurable_compose[OF _ measurable_szipE])
    apply (rule measurable_compose[OF _ measurable_szipE])
    apply measurable
    apply simp_all
    apply (simp add: space_stream_space)
    using K2.AE_T_enabled
    apply eventually_elim
    apply (auto simp: space_stream_space szip\<^sub>E_def K1.force_enabled K2.force_enabled 
                      stream.map_ident smap_szip_snd[where g="\<lambda>x. x"] smap_szip_fst[where f="\<lambda>x. x"]
                split: split_indicator)
    done
  also have "\<dots> = \<P>(\<omega> in K1.T x1. P1 \<omega>) * \<P>(\<omega> in K2.T x2. P2 \<omega>)"
    by simp
  finally show ?thesis ..
qed

end

lemma (in prob_space) nn_integral_le_const:
  "(AE x in M. f x \<le> c) \<Longrightarrow> 0 \<le> c \<Longrightarrow> (\<integral>\<^sup>+x. f x \<partial>M) \<le> c"
  using nn_integral_mono_AE[of f "\<lambda>x. c" M] emeasure_space_1 by simp

lemma nn_integral_less:
  assumes [measurable]: "f \<in> borel_measurable M" "g \<in> borel_measurable M"
  assumes f: "AE x in M. 0 \<le> f x" "(\<integral>\<^sup>+x. f x \<partial>M) \<noteq> \<infinity>"
  assumes ord: "AE x in M. f x \<le> g x" "\<not> (AE x in M. g x \<le> f x)"
  shows "(\<integral>\<^sup>+x. f x \<partial>M) < (\<integral>\<^sup>+x. g x \<partial>M)"
proof -
  have "0 < (\<integral>\<^sup>+x. g x - f x \<partial>M)"
  proof (intro order_le_neq_trans nn_integral_nonneg notI)
    assume "0 = (\<integral>\<^sup>+x. g x - f x \<partial>M)"
    then have "AE x in M. g x - f x \<le> 0"
      using nn_integral_0_iff_AE[of "\<lambda>x. g x - f x" M] by simp
    with f(1) ord(1) have "AE x in M. g x \<le> f x"
      by eventually_elim (auto simp: ereal_minus_le_iff)
    with ord show False
      by simp
  qed
  also have "\<dots> = (\<integral>\<^sup>+x. g x \<partial>M) - (\<integral>\<^sup>+x. f x \<partial>M)"
    by (subst nn_integral_diff) (auto simp: f ord)
  finally show ?thesis
    by (simp add: ereal_less_minus_iff f nn_integral_nonneg)
qed

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


lemma hld_smap': "HLD x (smap f s) = HLD (f -` x) s"
  by (simp add: HLD_def)

lemma set_pmf_map: "set_pmf (map_pmf f M) = f ` set_pmf M"
  using pmf_set_map[of f] by (metis comp_def)

lemma (in finite_measure) ereal_integral_real:
  assumes [measurable]: "f \<in> borel_measurable M" 
  assumes ae: "AE x in M. 0 \<le> f x" "AE x in M. f x \<le> ereal B"
  shows "ereal (\<integral>x. real (f x) \<partial>M) = (\<integral>\<^sup>+x. f x \<partial>M)"
proof (subst nn_integral_eq_integral[symmetric])
  show "integrable M (\<lambda>x. real (f x))"
    using ae by (intro integrable_const_bound[where B=B]) (auto simp: real_le_ereal_iff)
  show "AE x in M. 0 \<le> real (f x)"
    using ae by (auto simp: real_of_ereal_pos)
  show "(\<integral>\<^sup>+ x. ereal (real (f x)) \<partial>M) = integral\<^sup>N M f"
    using ae by (intro nn_integral_cong_AE) (auto simp: ereal_real)
qed

lemma (in MC_syntax) AE_not_suntil_coinduct [consumes 1, case_names \<psi> \<phi>]:
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

lemma (in MC_syntax) AE_not_suntil_coinduct_strong [consumes 1, case_names \<psi> \<phi>]:
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

declare [[coercion real_of_rat]]

lemma of_rat_setsum: "of_rat (\<Sum>a\<in>A. f a) = (\<Sum>a\<in>A. of_rat (f a))"
  by (induct rule: infinite_finite_induct) (auto simp: of_rat_add)

lemma setsum_strict_mono_single: 
  fixes f :: "_ \<Rightarrow> 'a :: {comm_monoid_add,ordered_cancel_ab_semigroup_add}"
  shows "finite A \<Longrightarrow> a \<in> A \<Longrightarrow> f a < g a \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> f a \<le> g a) \<Longrightarrow> setsum f A < setsum g A"
  using setsum_strict_mono_ex1[of A f g] by auto

lemma prob_space_point_measure:
  "finite S \<Longrightarrow> (\<And>s. s \<in> S \<Longrightarrow> 0 \<le> p s) \<Longrightarrow> (\<Sum>s\<in>S. p s) = 1 \<Longrightarrow> prob_space (point_measure S p)"
  by (rule prob_spaceI) (simp add: space_point_measure emeasure_point_measure_finite)

lemma diff_mono:
  fixes a b c d :: "'a :: ordered_ab_group_add"
  assumes "a \<le> b" "d \<le> c" shows "a - c \<le> b - d"
  unfolding diff_conv_add_uminus by (intro add_mono le_imp_neg_le assms)

end

