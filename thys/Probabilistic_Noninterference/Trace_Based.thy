header{* Trace-Based Noninterference *}

theory Trace_Based
  imports Resumption_Based
begin

(* This contains the development leading to the paper's Prop. 4. *)

subsection{* Preliminaries *}

lemma lebesgue_integral_point_measure:
  assumes f: "finite {a\<in>A. 0 < f a \<and> g a \<noteq> 0}"
  shows "integral\<^sup>L (point_measure A f) g = (\<Sum>a|a\<in>A \<and> 0 < f a \<and> g a \<noteq> 0. f a * g a)"
proof -
  have *: "\<And>x y. ereal x * max 0 (ereal y) = ereal (x * max 0 y)"
    by (simp add: max_def)
  have **: "(\<Sum>a | a \<in> A \<and> 0 < f a \<and> 0 < g a. f a * max 0 (g a)) = (\<Sum>a | a \<in> A \<and> 0 < f a \<and> g a \<noteq> 0. if 0 < g a then f a * g a else 0)"
    by (auto intro!: setsum_mono_zero_cong_left[OF f] split: split_if_asm)
  have ***: "(\<Sum>a | a \<in> A \<and> 0 < f a \<and> g a < 0. f a * max 0 (- g a)) = (\<Sum>a | a \<in> A \<and> 0 < f a \<and> g a \<noteq> 0. if g a < 0 then - (f a * g a) else 0)"
    by (auto intro!: setsum_mono_zero_cong_left[OF f] split: split_if_asm)
  show ?thesis
    unfolding lebesgue_integral_def
    apply (subst (1 2) positive_integral_max_0[symmetric])
    apply (subst (1 2) positive_integral_point_measure)
    using f apply (rule rev_finite_subset, simp add: subset_eq max_def)
    using f apply (rule rev_finite_subset, simp add: subset_eq max_def)
    apply (auto intro!: setsum_cong simp add: * ** *** less_max_iff_disj setsum_subtractf[symmetric])
    done
qed

lemma (in finite_measure) finite_measure_dist:
  assumes AE: "AE x in M. x \<notin> C \<longrightarrow> (x \<in> A \<longleftrightarrow> x \<in> B)"
  assumes sets: "A \<in> sets M" "B \<in> sets M" "C \<in> sets M"
  shows "dist (measure M A) (measure M B) \<le> measure M C"
proof -
  { have "measure M A \<le> measure M (B \<union> C)"
      using AE sets by (auto intro: finite_measure_mono_AE elim: AE_mp)
    also have "\<dots> \<le> measure M B + measure M C"
      using sets by (auto intro: finite_measure_subadditive)
    finally have A: "measure M A \<le> measure M B + measure M C" . }
  moreover
  { have "measure M B \<le> measure M (A \<union> C)"
      using AE sets by (auto intro: finite_measure_mono_AE elim: AE_mp)
    also have "\<dots> \<le> measure M A + measure M C"
      using sets by (auto intro: finite_measure_subadditive)
    finally have B: "measure M B \<le> measure M A + measure M C" . }
  ultimately show ?thesis
    by (simp add: dist_real_def)
qed

lemma Least_eq_0_iff: "(\<exists>i::nat. P i) \<Longrightarrow> (LEAST i. P i) = 0 \<longleftrightarrow> P 0"
  by (metis LeastI_ex neq0_conv not_less_Least)

lemma case_nat_comp_Suc[simp]: "case_nat x f \<circ> Suc = f"
  by auto

lemma setsum_eq_0_iff:
  fixes f :: "_ \<Rightarrow> 'a :: {comm_monoid_add,ordered_ab_group_add}"
  shows "finite A \<Longrightarrow> (\<And>i. i \<in> A \<Longrightarrow> 0 \<le> f i) \<Longrightarrow> (\<Sum>i\<in>A. f i) = 0 \<longleftrightarrow> (\<forall>i\<in>A. f i = 0)"
  apply rule
  apply (blast intro: setsum_nonneg_0)
  apply simp
  done

lemma setsum_less_0_iff:
  fixes f :: "_ \<Rightarrow> 'a :: {comm_monoid_add,ordered_ab_group_add}"
  shows "finite A \<Longrightarrow> (\<And>i. i \<in> A \<Longrightarrow> 0 \<le> f i) \<Longrightarrow> 0 < (\<Sum>i\<in>A. f i) \<longleftrightarrow> (\<exists>i\<in>A. 0 < f i)"
  using setsum_nonneg[of A f] setsum_eq_0_iff[of A f] by (simp add: less_le)

context PL_Indis
begin

declare emp_gen[simp del]

lemma fst_cont_eff: "fst (cont_eff cf j) = cont (fst cf) (snd cf) j"
  by (simp add: cont_eff)

lemma snd_cont_eff: "snd (cont_eff cf j) = eff (fst cf) (snd cf) j"
  by (simp add: cont_eff)

inductive_set reachable for cf where
  reachable_start: "proper (fst cf) \<Longrightarrow> cf \<in> reachable cf"
| reachable_cont_eff: "cf' \<in> reachable cf \<Longrightarrow> i < brn (fst cf') \<Longrightarrow> cont_eff cf' i \<in> reachable cf"

lemma proper_reachable[simp]: "cf \<in> reachable st \<Longrightarrow> proper (fst cf)"
  by (induct rule: reachable.induct) (auto simp: fst_cont_eff)

lemma proper_reachable1[simp]: "cf \<in> reachable st \<Longrightarrow> proper (fst st)"
  by (induct rule: reachable.induct) (auto simp: fst_cont_eff)

definition "reachable' st = (if proper (fst st) then reachable st else {st})"

lemma reachable'[simp]: "cf \<in> reachable st \<Longrightarrow> cf \<in> reachable' st"
  by (simp add: reachable'_def)

definition trans where
  "trans st cf = (if cf \<in> reachable st
    then point_measure (reachable' st) (\<lambda>cf'. \<Sum>i | i < brn (fst cf) \<and> cf' = cont_eff cf i. wt (fst cf) (snd cf) i)
    else point_measure {st} (\<lambda>cf'. 1))"

lemma measurable_discrCf: "Measurable.pred (count_space (reachable st)) discrCf"
  by simp

lemma measurable_snd_approx: "Measurable.pred (count_space (reachable' st)) (\<lambda>x. snd x \<approx> s)"
  by simp

lemma countable_reachableCf: "countable (reachable st)"
proof (rule countable_subset, intro subsetI)
  fix cf assume "cf \<in> reachable st"
  then show "cf \<in> range (\<lambda>xs. foldr (\<lambda>i cf. cont_eff cf i) xs st)"
  proof induct
    case reachable_start then show ?case
      by (auto simp: image_iff intro!: exI[of _ "[]"])
  next
    case (reachable_cont_eff cf' i)
    then obtain xs where "cf' = foldr (\<lambda>i cf. cont_eff cf i) xs st" by auto
    then show ?case
      by (intro image_eqI[where x="i # xs"]) auto
  qed
qed auto

lemma setsum_wt_less_0:
  "cf \<in> reachable st \<Longrightarrow> 0 < setsum (wt (fst cf) (snd cf)) {i. i < brn (fst cf) \<and> P i} \<longleftrightarrow>
   (\<exists>i<brn (fst cf). 0 < wt (fst cf) (snd cf) i \<and> P i)"
  by (subst setsum_less_0_iff) (simp_all add: conj_ac)

lemma setsum_wt_eq_0:
  "cf \<in> reachable st \<Longrightarrow> setsum (wt (fst cf) (snd cf)) {i. i < brn (fst cf) \<and> P i} = 0 \<longleftrightarrow>
   (\<forall>i<brn (fst cf). P i \<longrightarrow> wt (fst cf) (snd cf) i = 0)"
  by (subst setsum_eq_0_iff) auto

lemma emeasure_trans:
  assumes cf: "cf \<in> reachable st" and A: "A \<subseteq> reachable st"
  shows "emeasure (trans st cf) A =
    (\<Sum>i | i < brn (fst cf) \<and> cont_eff cf i \<in> A. wt (fst cf) (snd cf) i)"
proof -
  have **: "\<And>a. setsum (wt (fst cf) (snd cf)) {i. i < brn (fst cf) \<and> a = cont_eff cf i} =
      setsum (wt (fst cf) (snd cf)) {i. i < brn (fst cf) \<and> a = cont_eff cf i \<and> 0 < wt (fst cf) (snd cf) i}"
    using cf by (intro setsum_mono_zero_cong_right) (auto simp: less_le)
  have ***: "(SIGMA a:{a \<in> A. \<exists>i<brn (fst cf). 0 < wt (fst cf) (snd cf) i \<and> a = cont_eff cf i}.
                  {i. i < brn (fst cf) \<and> a = cont_eff cf i \<and> 0 < wt (fst cf) (snd cf) i}) =
      (\<lambda>i. (cont_eff cf i, i)) ` {i. i < brn (fst cf) \<and> cont_eff cf i \<in> A \<and> 0 < wt (fst cf) (snd cf) i}"
    by (auto simp: image_iff)
  show ?thesis
    using cf
    apply (simp add: trans_def reachable'_def A)
    apply (subst emeasure_point_measure[OF _ A])
    apply (simp_all add: setsum_wt_less_0)
    apply (simp add: **)
    apply (simp add: setsum_Sigma)
    apply (simp add: *** setsum_reindex inj_on_def)
    apply (rule setsum_mono_zero_cong_left)
    apply (auto simp: less_le)
    done
qed

lemma countable_reachable': "countable (reachable' st)"
    unfolding reachable'_def by (auto intro!: countable_reachableCf)

end

sublocale PL_Indis \<subseteq> trans: prob_space "trans st cf" for st cf
proof
  show "emeasure (trans st cf) (space (trans st cf)) = 1"
  proof cases
    assume cf: "cf \<in> reachable st"
    then show ?thesis
      by (subst emeasure_trans)
         (auto simp: reachable'_def trans_def space_point_measure reachable_cont_eff lessThan_def[symmetric] one_ereal_def
               cong: conj_cong)
  next
    assume "cf \<notin> reachable st" then show ?thesis
      apply (simp add: trans_def)
      apply (subst emeasure_point_measure)
      apply (simp_all add: space_point_measure reachable_start)
      done
  qed
qed

sublocale PL_Indis \<subseteq> K: Discrete_Markov_Kernel "reachable' st" "trans st" for st
proof
  show "countable (reachable' st)"
    by (rule countable_reachable')
  show "reachable' st \<noteq> {}"
    unfolding reachable'_def by (auto intro: reachable_start)
  show "\<And>s. s \<in> reachable' st \<Longrightarrow> sets (trans st s) = Pow (reachable' st)"
    by (simp add: reachable'_def trans_def sets_point_measure split: split_if_asm)
qed

context PL_Indis
begin

definition "G cf = { cont_eff cf b | b. b < brn (fst cf) \<and> 0 < wt (fst cf) (snd cf) b}"

lemma G_iff: "cf' \<in> G cf \<longleftrightarrow> (\<exists>b. b < brn (fst cf) \<and> 0 < wt (fst cf) (snd cf) b \<and> cf' = cont_eff cf b)"
  by (auto simp: G_def)

lemma reachable_G: "cf \<in> reachable st \<Longrightarrow> cf' \<in> G cf \<Longrightarrow> cf' \<in> reachable st"
  by (auto simp add: G_iff intro: reachable_cont_eff)

lemma discrCf_G: "cf' \<in> G cf \<Longrightarrow> discrCf cf \<Longrightarrow> discrCf cf'"
  by (auto simp add: G_iff)

lemma E_eq_G[simp]: "cf \<in> reachable st \<Longrightarrow> cf' \<in> E st cf \<longleftrightarrow> cf' \<in> G cf"
  unfolding E_def G_iff
  by (auto simp add: emeasure_trans setsum_wt_eq_0 less_le[of 0] reachable_cont_eff reachable'_def
           cong: conj_cong)

definition "validT cf cfT \<longleftrightarrow> (\<forall>i. cfT i \<in> G (case_nat cf cfT i))"

lemma validT_D: "validT cf cfT \<Longrightarrow> cfT i \<in> G (case_nat cf cfT i)"
  unfolding validT_def by auto

lemma reachable_validT: "cf \<in> reachable st \<Longrightarrow> validT cf cfT \<Longrightarrow> case_nat cf cfT i \<in> reachable st"
  by (induct i) (auto intro: reachable_G simp: validT_def)

lemma all_nat_split: "(\<forall>i::nat. P i) \<longleftrightarrow> P 0 \<and> (\<forall>i. P (Suc i))"
  by (metis nat.exhaust)

lemma validT_case_nat:
  "validT cf (case_nat cf' cfT) \<longleftrightarrow> cf' \<in> G cf \<and> validT cf' cfT"
  unfolding validT_def by (subst all_nat_split) auto

lemma AE_validT: assumes cf: "cf \<in> reachable st" shows "AE cfT in paths st cf. validT cf cfT"
  unfolding validT_def
  using AE_all_enabled[OF reachable'[OF assms]]
proof (eventually_elim, intro allI)
  fix i cfT assume E: "\<forall>i. cfT i \<in> E st (case_nat cf cfT i)"
  have "case_nat cf cfT i \<in> reachable st \<and> cfT i \<in> G (case_nat cf cfT i)"
  proof (induct i)
    case 0 with cf E[THEN spec, of 0] show ?case by simp
  next
    case (Suc n) with E[THEN spec, of "Suc n"] show ?case
      by (fastforce simp add: reachable_G)
  qed
  then show "cfT i \<in> G (case_nat cf cfT i)" ..
qed

lemma discrCf_mono_Suc:
  assumes cf: "validT cf cfT"
  and j: "discrCf (case_nat cf cfT j)" shows "discrCf (case_nat cf cfT (Suc j))"
  using discrCf_G[OF validT_D[OF cf] j] by simp

lemma discrCf_mono:
  assumes 1: "validT cf cfT" and 2: "i \<le> j" "discrCf (case_nat cf cfT i)"
  shows "discrCf (case_nat cf cfT j)"
  using 2 by (rule dec_induct)  (rule discrCf_mono_Suc[OF 1])

lemma discrCf_validT: "validT cf cfT \<Longrightarrow> discrCf cf \<Longrightarrow> discrCf (case_nat cf cfT n)"
  using discrCf_mono[of cf cfT 0 n] by simp

lemma measurable_case_nat_cf': "(\<lambda>\<omega>. case_nat cf' \<omega> i) \<in> measurable (S_seq st) (count_space (reachable' st \<union> {cf'}))"
  apply (rule measurable_case_nat)
  apply simp
  apply (auto simp: measurable_def Pi_iff)
  apply (auto simp add: space_PiM)
  done

lemma measurable_case_nat_cf:
  "(\<And>cf'. cf' \<in> reachable' st \<union> {cf} \<Longrightarrow> f cf' \<in> measurable (S_seq st) N) \<Longrightarrow>
   (\<lambda>x. f (case i of 0 \<Rightarrow> cf | Suc xa \<Rightarrow> x xa) x) \<in> measurable (S_seq st) N"
  by (rule measurable_compose_countable[OF _ measurable_case_nat_cf', of st cf f N i])
     simp_all

lemma measurable_validT [measurable]: "Measurable.pred (S_seq st) (validT cf)"
  unfolding validT_def[abs_def]
  apply (intro pred_intros_countable)
  apply (rule_tac f="\<lambda>x cfT. cfT i \<in> G x" in measurable_case_nat_cf)
  apply simp
  done

lemma validT_E_ex:
  assumes cfT: "validT cf cfT"
  shows "\<exists>b<brn (fst (case_nat cf cfT i)).
    0 < wt (fst (case_nat cf cfT i)) (snd (case_nat cf cfT i)) b \<and>
    cfT i = cont_eff (case_nat cf cfT i) b"
  using validT_D[OF cfT] by (simp add: G_iff)

lemma validTE:
  assumes "validT cf cfT"
  obtains bT where "\<And>i. bT i < brn (fst (case_nat cf cfT i))"
    "\<And>i. 0 < wt (fst (case_nat cf cfT i)) (snd (case_nat cf cfT i)) (bT i)"
    "\<And>i. cfT i = cont_eff (case_nat cf cfT i) (bT i)"
  using validT_E_ex[OF assms] by metis

subsection "Quasi strong termination traces"

definition "qstermT cf cfT \<longleftrightarrow> (\<exists>i. discrCf (case_nat cf cfT i))"
definition "qsend cf cfT = (LEAST i. discrCf (case_nat cf cfT i))"

lemma measurable_qsend[measurable]: "qsend cf \<in> measurable (S_seq st) (count_space UNIV)"
  unfolding qsend_def[abs_def]
  apply (rule measurable_Least)
  apply (rule_tac measurable_case_nat_cf)
  apply simp_all
  done

lemma measurable_qsterm[measurable]: "qstermT cf \<in> measurable (S_seq st) (count_space UNIV)"
  unfolding qstermT_def[abs_def]
  apply (intro pred_intros_countable)
  apply (rule_tac measurable_case_nat_cf)
  apply simp_all
  done

lemma qsend: "qstermT cf cfT \<Longrightarrow> discrCf (case_nat cf cfT (qsend cf cfT))"
  unfolding qstermT_def qsend_def by (rule LeastI_ex)

lemma qsend_eq_0[simp]: "discrCf cf \<Longrightarrow> qsend cf bT = 0"
  by (auto simp: qsend_def intro!: Least_equality)

lemma discrCf_imp_qstermT[simp]: "discrCf cf \<Longrightarrow> qstermT cf bT"
  by (auto simp: qstermT_def intro!: exI[of _ 0])

lemma qstermT_Suc:
  assumes cfT: "validT cf cfT"
  shows "qstermT (cfT 0) (cfT \<circ> Suc) \<longleftrightarrow> qstermT cf cfT"
proof -
  from cfT guess bT by (rule validTE) note bT = this
  { fix i assume "discrCf (cfT i)" then have "discrCf (case_nat cf cfT (Suc i))"
      by simp }
  moreover
  { fix i assume "discrCf (case_nat cf cfT i)"
    from discrCf_mono[OF cfT _ this, of "Suc i"]
    have "discrCf (cfT i)" by simp }
  ultimately show "qstermT (cfT 0) (cfT \<circ> Suc) \<longleftrightarrow> qstermT cf cfT"
    unfolding qstermT_def comp_def case_nat_idem by blast
qed

lemma qsend_Suc_eq:
  assumes cfT: "validT cf cfT" and "qstermT cf cfT"
  shows "qsend (cfT 0) (cfT\<circ>Suc) = qsend cf cfT - 1"
proof -
  from cfT guess bT by (rule validTE) note bT = this
  from `qstermT cf cfT` obtain n where n: "discrCf (case n of 0 \<Rightarrow> cf | Suc n \<Rightarrow> cfT n)"
    by (auto simp: qstermT_def)
  show "qsend (cfT 0) (cfT \<circ> Suc) = qsend cf cfT - 1"
  proof cases
    assume "discrCf cf"
    with discrCf_cont[OF this, of "bT 0"] bT[of 0]
    show ?thesis by simp
  next
    assume not_discr: "\<not> discrCf cf"
    from n show ?thesis
      unfolding qsend_def
      by (subst (2) Least_Suc) (auto simp add: case_nat_idem comp_def not_discr cong: nat.case_cong)
  qed
qed

lemma qsend_eq_0_iff: "qstermT cf cfT \<Longrightarrow> qsend cf cfT = 0 \<longleftrightarrow> discrCf cf"
  unfolding qstermT_def qsend_def
  by (subst Least_eq_0_iff) auto

lemma measurable_discrCf'[measurable]: "Measurable.pred (S_seq st) (\<lambda>x. discrCf (case_nat cf x i))"
  by (rule measurable_case_nat_cf) simp

lemma measurable_snd'[measurable]: "Measurable.pred (S_seq st) (\<lambda>x. snd (case_nat cf x i) \<approx> s)"
  by (rule measurable_case_nat_cf) simp

lemma AE_T_max_qsend:
  assumes c[simp]: "c \<in> reachable st"
  assumes AE: "AE bT in paths st c. qstermT c bT" and "0 < e"
  shows "\<exists>N. \<P>(bT in paths st c. \<not> discrCf (case_nat c bT N)) < e" (is "\<exists>N. ?P N < e")
proof -
  have "(\<lambda>n. \<P>(bT in paths st c. validT c bT \<and> \<not> discrCf (case_nat c bT n))) ---->
    measure (paths st c) (\<Inter>N. {bT \<in> space (paths st c). validT c bT \<and> \<not> discrCf (case_nat c bT N)})"
    using discrCf_mono_Suc[of c]
    by (intro finite_Lim_measure_decseq) (auto simp: decseq_Suc_iff)
  also have "measure (paths st c) (\<Inter>N. {bT \<in> space (paths st c). validT c bT \<and> \<not> discrCf (case_nat c bT N)}) =
    \<P>(bT in paths st c. \<not> qstermT c bT)"
    using AE_validT[of c st] by (intro finite_measure_eq_AE) (auto simp: qstermT_def)
  also have "\<P>(bT in paths st c. \<not> qstermT c bT) = 0"
    using AE by (intro prob_eq_0_AE) auto
  also have "(\<lambda>n. \<P>(bT in paths st c. validT c bT \<and> \<not> discrCf (case_nat c bT n))) = ?P"
    using AE_validT[of c st] by (intro HOL.ext finite_measure_eq_AE) auto
  finally have "\<exists>N. \<forall>n\<ge>N. norm (?P n - 0) < e"
    using `0 < e` by (rule LIMSEQ_D)
  then show ?thesis
    by (auto simp: measure_nonneg)
qed

lemma qsendI:
  "qstermT c bT \<Longrightarrow> (\<And>x. discrCf (case_nat c bT x) \<Longrightarrow> P x) \<Longrightarrow> P (qsend c bT)"
  using assms unfolding qsend_def qstermT_def by (rule LeastI2_ex)

lemma less_qsend:
  assumes bT: "validT cf bT" and c: "\<not> discrCf (case_nat cf bT i)" and *: "qstermT cf bT"
  shows "i < qsend cf bT"
using * proof (rule qsendI)
  fix j assume "discrCf (case_nat cf bT j)"
  from discrCf_mono[OF bT _ this, of i] c
  show "i < j" by (cases "i < j") auto
qed

lemma qsend_le:
  "cf \<in> reachable st \<Longrightarrow> validT cf cfT \<Longrightarrow> discrCf (case_nat cf cfT N) \<Longrightarrow> qsend cf cfT \<le> N"
  by (auto intro!: Least_le simp: qsend_def)

lemma qstermT_case_nat:
  assumes "cf' \<in> G cf" "validT cf' cfT"
  shows "qstermT cf (case_nat cf' cfT) \<longleftrightarrow> qstermT cf' cfT"
  using assms qstermT_Suc[of cf "case_nat cf' cfT"]
  by (simp add: validT_case_nat)

lemma qsend_case_nat:
  assumes cf: "cf \<in> reachable st" "cf' \<in> G cf" "validT cf' cfT" and "qstermT cf' cfT"
  shows "qsend cf' cfT = qsend cf (case_nat cf' cfT) - 1"
  using assms qsend_Suc_eq[of cf "case_nat cf' cfT"]
  by (simp add: validT_case_nat qstermT_case_nat)

subsection "Terminating configurations"

definition "qstermCf cf \<longleftrightarrow> (\<forall>cfT. validT cf cfT \<longrightarrow> qstermT cf cfT)"

lemma qstermCf_E:
  "qstermCf cf \<Longrightarrow> cf' \<in> G cf \<Longrightarrow> qstermCf cf'"
  apply (auto simp: qstermCf_def)
  apply (erule_tac x="case_nat cf' cfT" in allE)
  apply (simp add: validT_case_nat  qstermT_case_nat)
  done

lemma qstermCf_validT: "validT cf cfT \<Longrightarrow> qstermCf cf \<Longrightarrow> qstermCf (case_nat cf cfT i)"
  by (induct i) (auto dest: validT_D intro: qstermCf_E)

abbreviation "eff_at cf bT n \<equiv> snd (case_nat cf bT n)"
abbreviation "cont_at cf bT n \<equiv> fst (case_nat cf bT n)"

lemma eff_at_indis: "validT cf cfT \<Longrightarrow> discrCf cf \<Longrightarrow> eff_at cf cfT n \<approx> snd cf"
proof (induct n)
  case (Suc n)
  then have "discrCf (case_nat cf cfT n)" by (auto intro: discrCf_validT)
  then have "eff_at cf cfT (Suc n) \<approx> eff_at cf cfT n"
    using validT_E_ex[OF `validT cf cfT`, of n] by (auto intro: indis_sym)
  moreover have "eff_at cf cfT n \<approx> snd cf"
    using Suc by simp
  ultimately show ?case by (auto intro: indis_trans)
qed auto

lemma eff_at_indis_iff:
  "validT cf cfT \<Longrightarrow> discrCf cf \<Longrightarrow> eff_at cf cfT n \<approx> s \<longleftrightarrow> snd cf \<approx> s"
  using eff_at_indis[of cf cfT n] by (blast intro: indis_trans indis_sym)

lemma validT_shift: "validT cf cfT \<Longrightarrow> validT (case_nat cf cfT n) (\<lambda>i. cfT (n + i))"
  unfolding validT_def
  apply (rule allI)
  apply (erule_tac x="n + i" in allE)
  apply (auto split: nat.split)
  done

lemma eff_at_discrCf:
  assumes cfT: "validT cf cfT" and discr: "discrCf (case_nat cf cfT n)"
  shows "n \<le> N \<Longrightarrow> eff_at cf cfT N \<approx> eff_at cf cfT n"
  using eff_at_indis[of "case_nat cf cfT n" "\<lambda>i. cfT (n + i)" "N - n", OF validT_shift[OF cfT] discr]
  by (auto simp: le_imp_diff_is_add ac_simps split: nat.splits)

lemma qsend_leD:
  assumes "validT cf cfT" "qstermT cf cfT" "qsend cf cfT \<le> N"
  shows "eff_at cf cfT N \<approx> eff_at cf cfT (qsend cf cfT)"
  by (rule eff_at_discrCf[OF _ qsend]) fact+

lemma trans_eq: "cf \<in> reachable st \<Longrightarrow>
    trans st cf = point_measure (reachable' st) (\<lambda>cf'. \<Sum>i | i < brn (fst cf) \<and> cf' = cont_eff cf i. wt (fst cf) (snd cf) i)"
  by (simp add: trans_def)

lemma integral_trans:
  assumes cf: "cf \<in> reachable st"
  shows "(\<integral>x. f x \<partial>trans st cf) = (\<Sum>i<brn (fst cf). wt (fst cf) (snd cf) i * f (cont_eff cf i))"
proof -
  have *: "\<And>a. setsum (wt (fst cf) (snd cf)) {i. i < brn (fst cf) \<and> a = cont_eff cf i} =
      setsum (wt (fst cf) (snd cf)) {i. i < brn (fst cf) \<and> a = cont_eff cf i \<and> 0 < wt (fst cf) (snd cf) i}"
    using cf by (auto intro!: setsum_mono_zero_cong_right simp: less_le)
  have **: "(SIGMA a:{a \<in> reachable' st. (\<exists>i<brn (fst cf). 0 < wt (fst cf) (snd cf) i \<and> a = cont_eff cf i \<and> 0 < wt (fst cf) (snd cf) i) \<and> f a \<noteq> 0}.
                  {i. i < brn (fst cf) \<and> a = cont_eff cf i \<and> 0 < wt (fst cf) (snd cf) i}) =
      (\<lambda>i. (cont_eff cf i, i)) ` {i. i < brn (fst cf) \<and> 0 < wt (fst cf) (snd cf) i \<and> f (cont_eff cf i) \<noteq> 0}"
    by (auto intro!: reachable_cont_eff cf reachable')
  show ?thesis
    unfolding trans_eq[OF cf] using cf
    apply (subst lebesgue_integral_point_measure)
    apply (simp add: setsum_wt_less_0)
    unfolding *
    apply (simp add: setsum_wt_less_0 setsum_left_distrib setsum_Sigma ** setsum_reindex inj_on_def)
    apply (auto intro!: setsum_mono_zero_cong_left simp: less_le)
    done
qed

end

lemma dist_setsum:
  fixes f :: "'a \<Rightarrow> real" and g :: "'a \<Rightarrow> real"
  assumes "\<And>i. i \<in> I \<Longrightarrow> dist (f i) (g i) \<le> e i"
  shows "dist (\<Sum>i\<in>I. f i) (\<Sum>i\<in>I. g i) \<le> (\<Sum>i\<in>I. e i)"
proof cases
  assume "finite I" from this assms show ?thesis
  proof induct
    case (insert i I)
    then have "dist (\<Sum>i\<in>insert i I. f i) (\<Sum>i\<in>insert i I. g i) \<le> dist (f i) (g i) + dist (\<Sum>i\<in>I. f i) (\<Sum>i\<in>I. g i)"
      by (simp add: dist_triangle_add)
    also have "\<dots> \<le> e i + (\<Sum>i\<in>I. e i)"
      using insert by (intro add_mono) auto
    finally show ?case using insert by simp
  qed simp
qed simp

lemma dist_mult[simp]: "dist (x * y) (x * z) = \<bar>x\<bar> * dist y z"
  unfolding dist_real_def abs_mult[symmetric] right_diff_distrib ..

lemma dist_divide[simp]: "dist (y / r) (z / r) = dist y z / \<bar>r\<bar>"
  unfolding dist_real_def abs_divide[symmetric] diff_divide_distrib ..

lemma dist_weighted_setsum:
  fixes f :: "'a \<Rightarrow> real" and g :: "'b \<Rightarrow> real"
  assumes eps: "\<And>i j. i \<in> I \<Longrightarrow> j \<in> J \<Longrightarrow> w i \<noteq> 0 \<Longrightarrow> v j \<noteq> 0 \<Longrightarrow> dist (f i) (g j) \<le> d i + e j"
    and pos: "\<And>i. i\<in>I \<Longrightarrow> 0 \<le> w i" "\<And>j. j\<in>J \<Longrightarrow> 0 \<le> v j"
    and sum: "(\<Sum>i\<in>I. w i) = 1" "(\<Sum>j\<in>J. v j) = 1"
  shows "dist (\<Sum>i\<in>I. w i * f i) (\<Sum>j\<in>J. v j * g j) \<le> (\<Sum>i\<in>I. w i * d i) + (\<Sum>j\<in>J. v j * e j)"
proof -
  let "?W h" = "(\<Sum>(i,j)\<in>I\<times>J. (w i * v j) * h (i,j))"
  { fix g :: "'b \<Rightarrow> real"
    have "(\<Sum>j\<in>J. v j * g j) = (\<Sum>i\<in>I. w i) * (\<Sum>j\<in>J. v j * g j)"
      using sum by simp
    also have "\<dots> = ?W (g\<circ>snd)"
      by (simp add: ac_simps setsum_product setsum_cartesian_product)
    finally have "(\<Sum>j\<in>J. v j * g j) = ?W (g\<circ>snd)" . }
  moreover
  { fix f :: "'a \<Rightarrow> real"
    have "(\<Sum>i\<in>I. w i * f i) = (\<Sum>i\<in>I. w i * f i) * (\<Sum>j\<in>J. v j)"
      using sum by simp
    also have "\<dots> = ?W (f\<circ>fst)"
      unfolding setsum_product setsum_cartesian_product by (simp add: ac_simps)
    finally have "(\<Sum>i\<in>I. w i * f i) = ?W (f\<circ>fst)" . }
  moreover
  { have "dist (?W (f\<circ>fst)) (?W (g\<circ>snd)) \<le> ?W (\<lambda>(i,j). d i + e j)"
      using eps pos
      by (intro dist_setsum)
         (auto simp: mult_le_cancel_left zero_less_mult_iff mult_le_0_iff not_le[symmetric])
    also have "\<dots> = ?W (d \<circ> fst) + ?W (e \<circ> snd)"
      by (auto simp add: setsum_addf[symmetric] field_simps intro!: setsum_cong)
    finally have "dist (?W (f\<circ>fst)) (?W (g\<circ>snd)) \<le> ?W (d \<circ> fst) + ?W (e \<circ> snd)" by simp }
  ultimately show ?thesis by simp
qed

lemma field_abs_le_zero_epsilon:
  fixes x :: "'a\<Colon>{linordered_field}"
  assumes epsilon: "\<And>e. 0 < e \<Longrightarrow> \<bar>x\<bar> \<le> e"
  shows "\<bar>x\<bar> = 0"
proof (rule antisym)
  show "\<bar>x\<bar> \<le> 0"
  proof (rule field_le_epsilon)
    fix e :: 'a assume "0 < e" then show "\<bar>x\<bar> \<le> 0 + e" by simp fact
  qed
qed simp

lemma nat_nat_induct[case_names less]:
  fixes P :: "nat \<Rightarrow> nat \<Rightarrow> bool"
  assumes less: "\<And>n m. (\<And>j k. j + k < n + m \<Longrightarrow> P j k) \<Longrightarrow> P n m"
  shows "P n m"
proof -
  def N \<equiv> "n + m"
  then show ?thesis
  proof (induct N arbitrary: n m rule: nat_less_induct)
    case 1 show "P n m"
      apply (rule less)
      apply (rule 1[rule_format])
      apply auto
      done
  qed
qed

lemma part_insert:
  assumes "part A P" assumes "X \<inter> A = {}"
  shows "part (A \<union> X) (insert X P)"
  using assms by (auto simp: part_def)

lemma part_insert_subset:
  assumes X: "part (A - X) P" "X \<subseteq> A"
  shows "part A (insert X P)"
  using X part_insert[of "A - X" P X] by (simp add: Un_absorb2)

lemma part_is_subset:
  "part S P \<Longrightarrow> p \<in> P \<Longrightarrow> p \<subseteq> S"
  unfolding part_def by (metis Union_upper)

lemma dist_nonneg_bounded:
  fixes l u x y :: real
  assumes "l \<le> x" "x \<le> u" "l \<le> y" "y \<le> u"
  shows "dist x y \<le> u - l"
  using assms unfolding dist_real_def by arith

context PL_Indis
begin

definition "amSec c \<longleftrightarrow> (\<forall>s1 s2 n t. s1 \<approx> s2 \<longrightarrow>
  \<P>(bT in paths (c, s1) (c, s1). eff_at (c, s1) bT n \<approx> t) =
  \<P>(bT in paths (c, s2) (c, s2). eff_at (c, s2) bT n \<approx> t))"

definition "eSec c \<longleftrightarrow> (\<forall>s1 s2 t. s1 \<approx> s2 \<longrightarrow>
  \<P>(bT in paths (c, s1) (c, s1). qstermT (c, s1) bT \<and> eff_at (c, s1) bT (qsend (c, s1) bT) \<approx> t) =
  \<P>(bT in paths (c, s2) (c, s2). qstermT (c, s2) bT \<and> eff_at (c, s2) bT (qsend (c, s2) bT) \<approx> t))"

definition "aeT c \<longleftrightarrow> (\<forall>s. AE bT in paths (c, s) (c,s). qstermT (c,s) bT)"

lemma dist_Ps_upper_bound:
  fixes cf1 cf2 :: "('test, 'atom, 'choice) cmd \<times> 'state" and s :: "'state" and S
  defines "S cf bT \<equiv> qstermT cf bT \<and> eff_at cf bT (qsend cf bT) \<approx> s"
  defines "Ps st cf \<equiv> \<P>(bT in paths st cf. S cf bT)"
  defines "N st cf n bT \<equiv> \<not> discrCf (case_nat cf bT n)"
  defines "Pn st cf n \<equiv> \<P>(bT in paths st cf. N st cf n bT)"
  assumes bisim: "cf1 \<in> reachable st1" "cf2 \<in> reachable st2" "fst cf1 \<approx>01 fst cf2" "snd cf1 \<approx> snd cf2"
  shows "dist (Ps st1 cf1) (Ps st2 cf2) \<le> Pn st1 cf1 n + Pn st2 cf2 m"
using bisim proof (induct n m arbitrary: cf1 cf2 rule: nat_nat_induct)
  case (less n m)
  note `cf1 \<in> reachable st1`[simp]
  note `cf2 \<in> reachable st2`[simp]

  def W \<equiv> "\<lambda>c. setsum (wt (fst c) (snd c))"
  from ZObis_mC_ZOC[OF `fst cf1 \<approx>01 fst cf2` `snd cf1 \<approx> snd cf2`]
  obtain I0 P F where mC: "mC_ZOC ZObis (fst cf1) (fst cf2) (snd cf1) (snd cf2) I0 P F" by blast
  then have P: "{} \<notin> P - {I0}" "part {..<brn (fst cf1)} P" and "I0 \<in> P"
    and FP: "{} \<notin> F`(P-{I0})" "part {..<brn (fst cf2)} (F`P)" "inj_on F P"
    and eff: "\<And>q i j. q\<in>P \<Longrightarrow> q\<noteq>I0 \<Longrightarrow> i\<in>q \<Longrightarrow> j\<in>F q \<Longrightarrow> eff (fst cf1) (snd cf1) i \<approx> eff (fst cf2) (snd cf2) j"
    and cont: "\<And>q i j. q\<in>P \<Longrightarrow> q\<noteq>I0 \<Longrightarrow> i\<in>q \<Longrightarrow> j\<in>F q \<Longrightarrow> cont (fst cf1) (snd cf1) i \<approx>01 cont (fst cf2) (snd cf2) j"
    and wt:
      "\<And>I. I \<in> P - {I0} \<Longrightarrow> W cf1 I0 < 1 \<Longrightarrow> W cf2 (F I0) < 1 \<Longrightarrow>
      W cf1 I / (1 - W cf1 I0) = W cf2 (F I) / (1 - W cf2 (F I0))"
    and I0:
      "\<And>i. i \<in> I0 \<Longrightarrow> snd cf1 \<approx> eff (fst cf1) (snd cf1) i"
      "\<And>i. i \<in> I0 \<Longrightarrow> cont (fst cf1) (snd cf1) i \<approx>01 fst cf2"
    and FI0:
      "\<And>i. i \<in> F I0 \<Longrightarrow> snd cf2 \<approx> eff (fst cf2) (snd cf2) i"
      "\<And>i. i \<in> F I0 \<Longrightarrow> fst cf1 \<approx>01 cont (fst cf2) (snd cf2) i"
    unfolding mC_ZOC_def mC_ZOC_part_def mC_ZOC_eff_cont_def mC_ZOC_eff_cont0_def mC_ZOC_wt_def W_def
    by simp_all

  have "finite P" "inj_on F (P - {I0})" and FP': "finite (F`P)" "F I0 \<in> F`P"
    using finite_part[OF _ P(2)] finite_part[OF _ FP(2)] `I0 \<in> P` `inj_on F P`
    by (auto intro: inj_on_diff)

  { fix I i assume "I \<in> P" "i \<in> I"
    with P have "0 \<le> wt (fst cf1) (snd cf1) i"
      by (auto dest: part_is_subset intro!: wt_ge_0 proper_reachable[where st=st1]) }
  note wt1_nneg[intro] = this

  { fix I i assume "I \<in> P" "i \<in> F I"
    with FP have "0 \<le> wt (fst cf2) (snd cf2) i"
      by (auto dest: part_is_subset intro!: wt_ge_0 proper_reachable[where st=st2]) }
  note wt2_nneg[intro] = this

  { fix I assume "I \<in> P"
    then have "0 \<le> W cf1 I"
      unfolding W_def by (auto intro!: setsum_nonneg) }
  note W1_nneg[intro] = this

  { fix I assume "I \<in> P"
    then have "0 \<le> W cf2 (F I)"
      unfolding W_def by (auto intro!: setsum_nonneg) }
  note W2_nneg[intro] = this

  show ?case
  proof cases
    { fix n st1 st2 cf1 cf2 assume *: "fst cf1 \<approx>01 fst cf2" "snd cf1 \<approx> snd cf2"
      have "dist (Ps st1 cf1) (Ps st2 cf2) \<le> Pn st1 cf1 0"
      proof cases
        assume cf1: "discrCf cf1"
        moreover
        note cf2 = ZObis_pres_discrCfR[OF this *]
        from cf1 cf2 have "S cf1 = (\<lambda>bT. snd cf1 \<approx> s)" "S cf2 = (\<lambda>bT. snd cf2 \<approx> s)"
          unfolding S_def[abs_def] by auto
        moreover from `snd cf1 \<approx> snd cf2` have "snd cf1 \<approx> s \<longleftrightarrow> snd cf2 \<approx> s"
          by (blast intro: indis_sym indis_trans)
        ultimately show ?thesis
          using prob_space by (cases "snd cf2 \<approx> s") (simp_all add: Ps_def Pn_def measure_nonneg)
      next
        assume cf1: "\<not> discrCf cf1"
        then have "Pn st1 cf1 0 = 1"
          using prob_space by (simp add: Pn_def N_def)
        moreover have "dist (Ps st1 cf1) (Ps st2 cf2) \<le> 1"
          using dist_nonneg_bounded[where u=1 and l=0 and x="Ps st1 cf1" and y="Ps st2 cf2"]
          by (auto simp add: dist_real_def Ps_def measure_nonneg split: abs_split)
        ultimately show ?thesis by simp
      qed }
    note base_case = this

    assume "n = 0 \<or> m = 0"
    then show ?thesis
    proof
      assume "n = 0"
      moreover
      with prob_space `fst cf1 \<approx>01 fst cf2` `snd cf1 \<approx> snd cf2`
      have "dist (Ps st1 cf1) (Ps st2 cf2) \<le> Pn st1 cf1 0"
        by (intro base_case) (auto simp: Ps_def Pn_def)
      moreover have "0 \<le> Pn st2 cf2 m"
        by (simp add: Pn_def measure_nonneg)
      ultimately show ?thesis
        by simp
    next
      assume "m = 0"
      moreover
      with prob_space `fst cf1 \<approx>01 fst cf2` `snd cf1 \<approx> snd cf2`
      have "dist (Ps st2 cf2) (Ps st1 cf1) \<le> Pn st2 cf2 0"
        by (intro base_case) (auto simp: Ps_def Pn_def intro: indis_sym ZObis_sym)
      moreover have "0 \<le> Pn st1 cf1 n"
        by (simp add: Pn_def measure_nonneg)
      ultimately show ?thesis
        by (simp add: dist_commute)
    qed
  next
    assume "\<not> (n = 0 \<or> m = 0)"
    then have "n \<noteq> 0" "m \<noteq> 0" by auto
    then obtain n' m' where nm: "n = Suc n'" "m = Suc m'"
      by (metis nat.exhaust)

    def ps \<equiv> "\<lambda>st cf I. \<Sum>b\<in>I. wt (fst cf) (snd cf) b / W cf I * Ps st (cont_eff cf b)"
    def pn \<equiv> "\<lambda>st cf I n. \<Sum>b\<in>I. wt (fst cf) (snd cf) b / W cf I * Pn st (cont_eff cf b) n"

    { fix I assume "I \<in> P" "I \<noteq> I0" and W: "W cf1 I \<noteq> 0" "W cf2 (F I) \<noteq> 0"
      then have "dist (ps st1 cf1 I) (ps st2 cf2 (F I)) \<le> pn st1 cf1 I n' + pn st2 cf2 (F I) m'"
        unfolding ps_def pn_def
      proof (intro dist_weighted_setsum)
        fix i j assume ij: "i \<in> I" "j \<in> F I"
        assume "wt (fst cf1) (snd cf1) i / W cf1 I \<noteq> 0"
          and "wt (fst cf2) (snd cf2) j / W cf2 (F I) \<noteq> 0"
        from `I \<in> P` ij P(2) FP(2) have br: "i < brn (fst cf1)" "j < brn (fst cf2)"
          by (auto dest: part_is_subset)
        show "dist (Ps st1 (cont_eff cf1 i)) (Ps st2 (cont_eff cf2 j)) \<le>
          Pn st1 (cont_eff cf1 i) n' + Pn st2 (cont_eff cf2 j) m'"
        proof (rule less.hyps)
          show "n' + m' < n + m" using nm by simp
          show "cont_eff cf1 i \<in> reachable st1" "cont_eff cf2 j \<in> reachable st2"
            using br less.prems by (auto simp: reachable_cont_eff)
          show "fst (cont_eff cf1 i) \<approx>01 fst (cont_eff cf2 j)"
            "snd (cont_eff cf1 i) \<approx> snd (cont_eff cf2 j)"
            using cont[OF `I \<in> P` `I \<noteq> I0` ij] eff[OF `I \<in> P` `I \<noteq> I0` ij] by (auto simp: cont_eff)
        qed
      next
        show "(\<Sum>b\<in>F I. wt (fst cf2) (snd cf2) b / W cf2 (F I)) = 1"
          "(\<Sum>b\<in>I. wt (fst cf1) (snd cf1) b / W cf1 I) = 1"
          using W by (auto simp: setsum_divide_distrib[symmetric] setsum_nonneg W_def)
      qed auto }
    note dist_n'_m' = this

    { fix I assume "I \<in> P" "I \<noteq> I0" and W: "W cf1 I = 0 \<longleftrightarrow> W cf2 (F I) = 0"
      have "dist (ps st1 cf1 I) (ps st2 cf2 (F I)) \<le> pn st1 cf1 I n' + pn st2 cf2 (F I) m'"
      proof cases
        assume "W cf2 (F I) = 0"
        then have "W cf2 (F I) = 0" "W cf1 I = 0" by (auto simp: W)
        then show ?thesis by (simp add: ps_def pn_def)
      next
        assume "W cf2 (F I) \<noteq> 0"
        then have "W cf1 I \<noteq> 0" "W cf2 (F I) \<noteq> 0" by (auto simp: W)
        from dist_n'_m'[OF `I \<in> P` `I \<noteq> I0` this] show ?thesis .
      qed }
    note dist_n'_m'_W_iff = this

    { fix I j assume W: "W cf2 (F I0) \<noteq> 0"
      from `I0 \<in> P` have "dist (\<Sum>i\<in>{()}. 1 * Ps st1 cf1) (ps st2 cf2 (F I0)) \<le> (\<Sum>i\<in>{()}. 1 * Pn st1 cf1 n) + pn st2 cf2 (F I0) m'"
        unfolding ps_def pn_def
      proof (intro dist_weighted_setsum)
        fix j assume "j \<in> F I0"
        with FP(2) `I0 \<in> P` have br: "j < brn (fst cf2)"
          by (auto dest: part_is_subset)
        show "dist (Ps st1 cf1) (Ps st2 (cont_eff cf2 j)) \<le> Pn st1 cf1 n + Pn st2 (cont_eff cf2 j) m'"
        proof (rule less.hyps)
          show "n + m' < n + m" using nm by simp
          show "cf1 \<in> reachable st1" "cont_eff cf2 j \<in> reachable st2"
            using br less.prems by (auto simp: reachable_cont_eff)
          show "fst cf1 \<approx>01 fst (cont_eff cf2 j)"
            "snd cf1 \<approx> snd (cont_eff cf2 j)"
            using FI0[OF `j \<in> F I0`] `snd cf1 \<approx> snd cf2`
            by (auto simp: cont_eff intro: indis_trans)
        qed
      next
        show "(\<Sum>b\<in>F I0. wt (fst cf2) (snd cf2) b / W cf2 (F I0)) = 1"
          using W `I0 \<in> P` by (auto simp: setsum_divide_distrib[symmetric] setsum_nonneg W_def)
      qed auto
      then have "dist (Ps st1 cf1) (ps st2 cf2 (F I0)) \<le> Pn st1 cf1 n + pn st2 cf2 (F I0) m'"
        by simp }
    note dist_n_m' = this

    { fix I j assume W: "W cf1 I0 \<noteq> 0"
      from `I0 \<in> P` have "dist (ps st1 cf1 I0) (\<Sum>i\<in>{()}. 1 * Ps st2 cf2) \<le> pn st1 cf1 I0 n' + (\<Sum>i\<in>{()}. 1 * Pn st2 cf2 m)"
        unfolding ps_def pn_def
      proof (intro dist_weighted_setsum)
        fix i assume "i \<in> I0"
        with P(2) `I0 \<in> P` have br: "i < brn (fst cf1)"
          by (auto dest: part_is_subset)
        show "dist (Ps st1 (cont_eff cf1 i)) (Ps st2 cf2) \<le> Pn st1 (cont_eff cf1 i) n' + Pn st2 cf2 m"
        proof (rule less.hyps)
          show "n' + m < n + m" using nm by simp
          show "cont_eff cf1 i \<in> reachable st1" "cf2 \<in> reachable st2"
            using br less.prems by (auto simp: reachable_cont_eff)
          show "fst (cont_eff cf1 i) \<approx>01 fst cf2"
            "snd (cont_eff cf1 i) \<approx> snd cf2"
            using I0[OF `i \<in> I0`] `snd cf1 \<approx> snd cf2`
            by (auto simp: cont_eff intro: indis_trans indis_sym)
        qed
      next
        show "(\<Sum>b\<in>I0. wt (fst cf1) (snd cf1) b / W cf1 I0) = 1"
          using W `I0 \<in> P` by (auto simp: setsum_divide_distrib[symmetric] setsum_nonneg W_def)
      qed auto
      then have "dist (ps st1 cf1 I0) (Ps st2 cf2) \<le> pn st1 cf1 I0 n' + Pn st2 cf2 m"
        by simp }
    note dist_n'_m = this

    have S_sets[measurable]: "\<And>st cf. Measurable.pred (paths st cf) (S cf)"
      unfolding S_def[abs_def] unfolding K.measurable_paths1
      apply (rule measurable_compose_countable[OF _ measurable_qsend])
      apply simp
      apply (rule measurable_case_nat_cf)
      apply simp
      done

    { fix st cf' cf assume cf[simp]: "cf \<in> reachable st" and cf': "cf' \<in> G cf"
      have "AE bT in paths st cf'. S cf (case_nat cf' bT) = S cf' bT"
        unfolding S_def
        using AE_validT[OF reachable_G[OF cf cf']]
      proof (eventually_elim, intro conj_cong)
        fix bT assume bT: "validT cf' bT"
        with qstermT_case_nat[OF cf'] show "qstermT cf (case_nat cf' bT) \<longleftrightarrow> qstermT cf' bT" .
        assume bT': "qstermT cf' bT"
        have "snd (case_nat cf (case_nat cf' bT) (qsend cf (case_nat cf' bT))) \<approx>
              snd (case_nat cf' bT (qsend cf (case_nat cf' bT) - 1))"
        proof (cases "qsend cf (case_nat cf' bT)")
          case 0
          with qstermT_case_nat[OF cf' bT] bT' have "qstermT cf (case_nat cf' bT)" by simp
          from qsend[OF this] 0 have "discrCf cf" by simp
          with cf' 0 show ?thesis
            by (auto simp add: G_iff)
        qed (auto intro: indis_sym)
        then show "snd (case_nat cf (case_nat cf' bT) (qsend cf (case_nat cf' bT))) \<approx> s \<longleftrightarrow>
            snd (case_nat cf' bT (qsend cf' bT)) \<approx> s"
          unfolding qsend_case_nat[OF cf cf' bT bT'] by (auto intro: indis_trans indis_sym)
      qed }
    note S_sets = this

    { fix cf :: "('test, 'atom, 'choice) cmd \<times> 'state" and P I0 S n st
      assume cf[simp]: "cf \<in> reachable st" and P: "part {..<brn (fst cf)} P" and "finite P" "I0 \<in> P"

      { fix I i assume "I \<in> P" "i \<in> I"
        with P have "0 \<le> wt (fst cf) (snd cf) i"
          by (auto dest: part_is_subset intro!: wt_ge_0 proper_reachable[where st=st]) }
      note wt_nneg[simp] = this

      assume S_sets[measurable]: "\<And>cf n. {bT \<in> space (S_seq st). S cf n bT} \<in> sets (S_seq st)"
        and S_next: "\<And>cf cf' n. cf \<in> reachable st \<Longrightarrow> cf' \<in> G cf \<Longrightarrow>
          AE bT in paths st cf'. S cf (Suc n) (case_nat cf' bT) = S cf' n bT"
      have finite_I: "\<And>I. I \<in> P \<Longrightarrow> finite I"
        using finite_subset[OF part_is_subset[OF P]] by blast
      let ?P = "\<lambda>I. \<Sum>i\<in>I. wt (fst cf) (snd cf) i * \<P>(bT in paths st (cont_eff cf i). S (cont_eff cf i) n bT)"
      let ?P' = "\<lambda>I. W cf I * (\<Sum>i\<in>I. wt (fst cf) (snd cf) i / W cf I * \<P>(bT in paths st (cont_eff cf i). S (cont_eff cf i) n bT))"
      have "\<P>(bT in paths st cf. S cf (Suc n) bT) = (\<integral>cf'. \<P>(bT in paths st cf'. S cf' n bT) \<partial>trans st cf)"
        unfolding prob_iterate_Collect[OF reachable'[OF cf] S_sets]
        apply (intro integral_cong_AE)
        using AE_enabled[OF reachable'[OF `cf \<in> reachable st`]]
        apply eventually_elim
        apply (rule prob_eq_AE)
        apply (simp_all add: S_next reachable_G[OF `cf \<in> reachable st`])
        done
      also have "\<dots> = (\<Sum>I\<in>P. ?P I)"
        unfolding integral_trans[OF cf] by (simp add: part_setsum[OF P])
      also have "\<dots> = (\<Sum>I\<in>P. ?P' I)"
        using `cf \<in> reachable st` finite_I
        by (auto intro!: setsum_cong simp add: setsum_right_distrib setsum_nonneg_eq_0_iff W_def)
      also have "\<dots> = ?P' I0 + (\<Sum>I\<in>P-{I0}. ?P' I)"
        unfolding setsum_diff1'[OF `finite P` `I0 \<in> P`] ..
      finally have "\<P>(bT in paths st cf. S cf (Suc n) bT) = \<dots>" . }
    note P_split = this

    have Ps1: "Ps st1 cf1 = W cf1 I0 * ps st1 cf1 I0 + (\<Sum>I\<in>P-{I0}. W cf1 I * ps st1 cf1 I)"
      unfolding Ps_def ps_def using P(2) `finite P` `I0 \<in> P` by (intro P_split S_sets) simp_all

    have "Ps st2 cf2 = W cf2 (F I0) * ps st2 cf2 (F I0) + (\<Sum>I\<in>F`P-{F I0}. W cf2 I * ps st2 cf2 I)"
      unfolding Ps_def ps_def using FP(2) `finite P` `I0 \<in> P` by (intro P_split S_sets) simp_all
    moreover have F_diff: "F ` P - {F I0} = F ` (P - {I0})"
      by (auto simp: `inj_on F P`[THEN inj_on_eq_iff] `I0 \<in> P`)
    ultimately have Ps2: "Ps st2 cf2 = W cf2 (F I0) * ps st2 cf2 (F I0) + (\<Sum>I\<in>P-{I0}. W cf2 (F I) * ps st2 cf2 (F I))"
      by (simp add: setsum_reindex `inj_on F (P-{I0})`)

    have Pn1: "Pn st1 cf1 n = W cf1 I0 * pn st1 cf1 I0 n' + (\<Sum>I\<in>P-{I0}. W cf1 I * pn st1 cf1 I n')"
      unfolding Pn_def pn_def nm using P(2) `finite P` `I0 \<in> P` by (intro P_split) (simp_all add: N_def)

    have "Pn st2 cf2 m = W cf2 (F I0) * pn st2 cf2 (F I0) m' + (\<Sum>I\<in>F`P-{F I0}. W cf2 I * pn st2 cf2 I m')"
      unfolding Pn_def pn_def nm using FP(2) `finite P` `I0 \<in> P` by (intro P_split) (simp_all add: N_def)
    with F_diff have Pn2: "Pn st2 cf2 m = W cf2 (F I0) * pn st2 cf2 (F I0) m' + (\<Sum>I\<in>P-{I0}. W cf2 (F I) * pn st2 cf2 (F I) m')"
      by (simp add: setsum_reindex `inj_on F (P-{I0})`)

    show ?thesis
    proof cases
      assume "W cf1 I0 = 1 \<or> W cf2 (F I0) = 1"
      then show ?thesis
      proof
        assume *: "W cf1 I0 = 1"
        then have "W cf1 I0 = W cf1 {..<brn (fst cf1)}" by (simp add: W_def  proper_reachable[where st=st1])
        also have "\<dots> = W cf1 I0 + (\<Sum>I\<in>P - {I0}. W cf1 I)"
          unfolding `part {..<brn (fst cf1)} P`[THEN part_setsum] W_def
          unfolding setsum_diff1'[OF `finite P` `I0 \<in> P`] ..
        finally have "(\<Sum>I\<in>P - {I0}. W cf1 I) = 0" by simp
        then have "\<forall>I\<in>P - {I0}. W cf1 I = 0"
          using `finite P` by (subst (asm) setsum_nonneg_eq_0_iff) auto
        then have "Ps st1 cf1 = ps st1 cf1 I0" "Pn st1 cf1 n = pn st1 cf1 I0 n'"
          unfolding Ps1 Pn1 * by simp_all
        moreover note dist_n'_m *
        ultimately show ?thesis by simp
      next
        assume *: "W cf2 (F I0) = 1"
        then have "W cf2 (F I0) = W cf2 {..<brn (fst cf2)}" by (simp add: W_def proper_reachable[where st=st2])
        also have "\<dots> = W cf2 (F I0) + (\<Sum>I\<in>F ` P - {F I0}. W cf2 I)"
          unfolding FP(2)[THEN part_setsum] W_def
          unfolding setsum_diff1'[OF FP'] ..
        finally have "(\<Sum>I\<in>F`P - {F I0}. W cf2 I) = 0" by simp
        then have "\<forall>I\<in>F`P - {F I0}. W cf2 I = 0"
          using `finite P` by (subst (asm) setsum_nonneg_eq_0_iff) auto
        then have "Ps st2 cf2 = ps st2 cf2 (F I0)" "Pn st2 cf2 m = pn st2 cf2 (F I0) m'"
          unfolding Ps2 Pn2 * by (simp_all add: F_diff)
        moreover note dist_n_m' *
        ultimately show ?thesis by simp
      qed
    next
      assume W_neq1: "\<not> (W cf1 I0 = 1 \<or> W cf2 (F I0) = 1)"
      moreover
      { fix cf :: "('test, 'atom, 'choice) cmd \<times> 'state" and I P
        assume "proper (fst cf)" "part {..<brn (fst (cf))} P" "I \<in> P"
        then have "W cf I \<le> W cf {..<brn (fst (cf))}"
          unfolding W_def
          by (intro setsum_mono2 part_is_subset) auto
        then have "W cf I \<le> 1" using `proper (fst cf)` by (simp add: W_def) }
      ultimately have wt_less1: "W cf1 I0 < 1" "W cf2 (F I0) < 1"
        using FP(2) FP'(2) P(2) `I0 \<in> P`
        unfolding le_less by (blast intro: `cf1 \<in> reachable st1` `cf2 \<in> reachable st2` proper_reachable)+

      { fix I assume *: "I \<in> P - {I0}"
        have "W cf1 I = 0 \<longleftrightarrow> W cf2 (F I) = 0"
          using wt[OF * wt_less1] wt_less1 by auto
        with * have "dist (ps st1 cf1 I) (ps st2 cf2 (F I)) \<le> pn st1 cf1 I n' + pn st2 cf2 (F I) m'"
          by (intro dist_n'_m'_W_iff) auto }
      note dist_eps = this

      { fix a b c d :: real
        have "dist a b = dist ((a - c) + c) ((b - d) + d)" by simp
        also have "\<dots> \<le> dist (a - c) (b - d) + dist c d"
          using dist_triangle_add .
        finally have "dist a b \<le> dist (a - c) (b - d) + dist c d" . }
      note dist_triangle_diff = this

      have dist_diff_diff: "\<And>a b c d::real. dist (a - b) (c - d) \<le> dist a b + dist c d"
        unfolding dist_real_def by auto

      let ?v0 = "W cf1 I0" and ?w0 = "W cf2 (F I0)"
      let ?v1 = "1 - ?v0" and ?w1 = "1 - ?w0"
      let ?wQ = "(Ps st2 cf2 - ?w0 * ps st2 cf2 (F I0)) / ?w1"
      let ?wP = "(Ps st1 cf1 - ?v0 * ps st1 cf1 I0) / ?v1"
      let ?D = "(?w0 * ?v1 * Ps st1 cf1 + ?w1 * ?v0 * ps st1 cf1 I0)"
      let ?E = "(?v0 * ?w1 * Ps st2 cf2 + ?v1 * ?w0 * ps st2 cf2 (F I0))"

      have w0v0_less1: "?w0 * ?v0 < 1 * 1"
        using wt_less1 `I0 \<in> P` by (intro mult_strict_mono) auto
      then have neg_w0v0_nonneg: "0 \<le> 1 - ?w0 * ?v0" by simp

      let ?e1 = "(\<Sum>I\<in>P-{I0}. W cf1 I / ?v1 * pn st1 cf1 I n') +
            (\<Sum>I\<in>P-{I0}. W cf2 (F I) / ?w1 * pn st2 cf2 (F I) m')"
      have "dist ((1 - ?w0 * ?v0) * Ps st1 cf1) ((1 - ?w0 * ?v0) * Ps st2 cf2) \<le>
        dist ((1 - ?w0 * ?v0) * Ps st1 cf1 - ?D) ((1 - ?w0 * ?v0) * Ps st2 cf2 - ?E) + dist ?D ?E"
        by (rule dist_triangle_diff)
      also have "\<dots> \<le> ?v1 * ?w1 * ?e1 + (?v1 * ?w0 * (Pn st1 cf1 n + pn st2 cf2 (F I0) m') + ?w1 * ?v0 * (pn st1 cf1 I0 n' + Pn st2 cf2 m))"
      proof (rule add_mono)
        { have "?wP = (\<Sum>I\<in>P-{I0}. W cf1 I * ps st1 cf1 I) / ?v1"
            unfolding Ps1 by (simp add: field_simps)
          also have "\<dots> = (\<Sum>I\<in>P-{I0}. W cf1 I / ?v1 * ps st1 cf1 I)"
            by (subst setsum_divide_distrib) simp
          finally have "?wP = (\<Sum>I\<in>P-{I0}. W cf1 I / ?v1 * ps st1 cf1 I)" . }
        moreover
        { have "?wQ = (\<Sum>I\<in>P-{I0}. W cf2 (F I) * ps st2 cf2 (F I)) / ?w1"
            using Ps2 by (simp add: field_simps)
          also have "\<dots> = (\<Sum>I\<in>P-{I0}. W cf2 (F I) / ?w1 * ps st2 cf2 (F I))"
            by (subst setsum_divide_distrib) simp
          also have "\<dots> = (\<Sum>I\<in>P-{I0}. W cf1 I / ?v1 * ps st2 cf2 (F I))"
            using wt[OF _ wt_less1] by simp
          finally have "?wQ = (\<Sum>I\<in>P-{I0}. W cf1 I / ?v1 * ps st2 cf2 (F I))" . }
        ultimately
        have "dist ?wP ?wQ \<le> (\<Sum>I\<in>P-{I0}. W cf1 I / ?v1 * (pn st1 cf1 I n' + pn st2 cf2 (F I) m'))"
          using wt_less1 dist_eps
          by (simp, intro dist_setsum)
             (simp add: setsum_nonneg divide_le_cancel mult_le_cancel_left not_le[symmetric] W1_nneg)
        also have "\<dots> = ?e1"
          unfolding setsum_addf[symmetric] using  wt[OF _ wt_less1]
          by (simp add: field_simps add_divide_distrib)
        finally have "dist (?v1 * ?w1 * ?wP) (?v1 * ?w1 * ?wQ) \<le> ?v1 * ?w1 * ?e1"
          using wt_less1 unfolding dist_mult by simp
        also {
          have "?v1 * ?w1 * ?wP = ?w1 * (?v0 * Ps st1 cf1 + ?v1 * Ps st1 cf1) - ?w1 * ?v0 * ps st1 cf1 I0"
            using wt_less1 unfolding divide_eq_eq times_divide_eq by (simp add: field_simps)
          also have "\<dots> = (1 - ?w0 * ?v0) * Ps st1 cf1 - ?D"
            by (simp add: field_simps)
          finally have "?v1 * ?w1 * ?wP = (1 - ?w0 * ?v0) * Ps st1 cf1 - ?D" . }
        also {
          have "?v1 * ?w1 * ?wQ = ?v1 * (?w0 * Ps st2 cf2 + ?w1 * Ps st2 cf2) - ?v1 * ?w0 * (ps st2 cf2 (F I0))"
            using wt_less1 unfolding divide_eq_eq times_divide_eq by (simp add: field_simps)
          also have "\<dots> = (1 - ?w0 * ?v0) * Ps st2 cf2 - ?E"
            by (simp add: field_simps)
          finally have "?v1 * ?w1 * ?wQ = (1 - ?w0 * ?v0) * Ps st2 cf2 - ?E" . }
        finally show "dist ((1 - ?w0 * ?v0) * Ps st1 cf1 - ?D) ((1 - ?w0 * ?v0) * Ps st2 cf2 - ?E) \<le> ?v1 * ?w1 * ?e1" .
      next
        have "dist ?D ?E = dist
          (?v1 * ?w0 * Ps st1 cf1 - ?v1 * ?w0 * ps st2 cf2 (F I0))
          (?w1 * ?v0 * Ps st2 cf2 - ?w1 * ?v0 * ps st1 cf1 I0)"
          unfolding dist_real_def by (simp add: ac_simps)
        also have "\<dots> \<le> dist (?v1 * ?w0 * Ps st1 cf1) (?v1 * ?w0 * ps st2 cf2 (F I0)) +
          dist (?w1 * ?v0 * Ps st2 cf2) (?w1 * ?v0 * ps st1 cf1 I0)"
          using dist_diff_diff .
        also have "\<dots> \<le> ?v1 * ?w0 * (Pn st1 cf1 n + pn st2 cf2 (F I0) m') + ?w1 * ?v0 * (pn st1 cf1 I0 n' + Pn st2 cf2 m)"
        proof (rule add_mono)
          show "dist (?v1 * ?w0 * Ps st1 cf1) (?v1 * ?w0 * ps st2 cf2 (F I0)) \<le> ?v1 * ?w0 * (Pn st1 cf1 n + pn st2 cf2 (F I0) m')"
            using wt_less1 dist_n_m' `I0 \<in> P`
            by (simp add: setsum_nonneg mult_le_cancel_left not_le[symmetric] mult_le_0_iff W2_nneg)
          show "dist (?w1 * ?v0 * Ps st2 cf2) (?w1 * ?v0 * ps st1 cf1 I0) \<le> ?w1 * ?v0 * (pn st1 cf1 I0 n' + Pn st2 cf2 m)"
            using wt_less1 dist_n'_m `I0 \<in> P`
            by (subst dist_commute)
               (simp add: setsum_nonneg mult_le_cancel_left not_le[symmetric] mult_le_0_iff W1_nneg)
        qed
        finally show "dist ?D ?E \<le> ?v1 * ?w0 * (Pn st1 cf1 n + pn st2 cf2 (F I0) m') + ?w1 * ?v0 * (pn st1 cf1 I0 n' + Pn st2 cf2 m)" .
      qed
      also  have "\<dots> = ?w1 * (\<Sum>I\<in>P-{I0}. W cf1 I * pn st1 cf1 I n') + ?v1 * (\<Sum>I\<in>P-{I0}. W cf2 (F I) * pn st2 cf2 (F I) m') +
        ?v1 * ?w0 * (Pn st1 cf1 n + pn st2 cf2 (F I0) m') + ?w1 * ?v0 * (pn st1 cf1 I0 n' + Pn st2 cf2 m)"
        using W_neq1 by (simp add: setsum_divide_distrib[symmetric] add_divide_eq_iff divide_add_eq_iff)
      also have "\<dots> = (1 - ?w0 * ?v0) * (Pn st1 cf1 n + Pn st2 cf2 m)"
        unfolding Pn1 Pn2 by (simp add: field_simps)
      finally show "dist (Ps st1 cf1) (Ps st2 cf2) \<le> Pn st1 cf1 n + Pn st2 cf2 m"
        using neg_w0v0_nonneg w0v0_less1 by (simp add: mult_le_cancel_left)
    qed
  qed
qed

lemma Ps_eq:
  fixes cf1 cf2 s and S
  defines "S cf bT \<equiv> qstermT cf bT \<and> eff_at cf bT (qsend cf bT) \<approx> s"
  defines "Ps st cf \<equiv> \<P>(bT in paths st cf. S cf bT)"
  assumes qsterm1: "AE bT in paths st1 cf1. qstermT cf1 bT"
  assumes qsterm2: "AE bT in paths st2 cf2. qstermT cf2 bT"
  and bisim:
    "cf1 \<in> reachable st1" "cf2 \<in> reachable st2" "fst cf1 \<approx>01 fst cf2" "snd cf1 \<approx> snd cf2"
  shows "Ps st1 cf1 = Ps st2 cf2"
proof -
  let ?nT = "\<lambda>cf n bT. \<not> discrCf (case_nat cf bT n)"
  let ?PnT = "\<lambda>st cf n. \<P>(bT in paths st cf. ?nT cf n bT)"

  { fix cf st and e :: real assume AE: "cf \<in> reachable st" "AE bT in paths st cf. qstermT cf bT" "0 < e"
    from AE_T_max_qsend[OF this]
    have "\<exists>N. ?PnT st cf N < e" . }
   note AE = this

   have "dist (Ps st1 cf1) (Ps st2 cf2) = 0"
     unfolding dist_real_def
   proof (rule field_abs_le_zero_epsilon)
     fix e ::real assume "0 < e"
     then have "0 < e / 2" by auto
     from AE[OF `cf1 \<in> reachable st1` qsterm1 this] AE[OF `cf2 \<in> reachable st2` qsterm2 this]
     obtain n m where "?PnT st1 cf1 n < e / 2" "?PnT st2 cf2 m < e / 2" by auto
     moreover have "dist (Ps st1 cf1) (Ps st2 cf2) \<le> ?PnT st1 cf1 n + ?PnT st2 cf2 m"
       unfolding Ps_def S_def using bisim by (rule dist_Ps_upper_bound)
     ultimately show "\<bar>Ps st1 cf1 - Ps st2 cf2\<bar> \<le> e"
       unfolding dist_real_def by auto
   qed
   then show "Ps st1 cf1 = Ps st2 cf2" by auto
qed

lemma siso_trace:
  assumes "siso c" "s \<approx> t" and t: "validT (c, t) cfT"
  shows "siso (cont_at (c, s) cfT n) \<and>
    cont_at (c, s) cfT n = cont_at (c, t) cfT n \<and>
    eff_at (c, s) cfT n \<approx> eff_at (c, t) cfT n"
proof (induct n)
  case 0 then show ?case using `s \<approx> t` `siso c` by simp
next
  case (Suc n)
  with validT_E_ex[OF t, of n] show ?case
    by (auto simp: G_iff cont_eff)
qed

lemma Sbis_trace:
  assumes "cf1 \<in> reachable st1" "cf2 \<in> reachable st2" "fst cf1 \<approx>s fst cf2" "snd cf1 \<approx> snd cf2"
  shows "\<P>(cfT in paths st1 cf1. eff_at cf1 cfT n \<approx> s') = \<P>(cfT in paths st2 cf2. eff_at cf2 cfT n \<approx> s')"
    (is "?P st1 cf1 n = ?P st2 cf2 n")
using assms proof (induct n arbitrary: cf1 cf2)
  case 0
  show ?case
  proof cases
    assume "snd cf1 \<approx> s'"
    with `snd cf1 \<approx> snd cf2` `fst cf1 \<approx>s fst cf2` have "snd cf1 \<approx> s'" "snd cf2 \<approx> s'"
      by (metis indis_trans indis_sym)+
    then show ?case
      using prob_space by simp
  next
    assume "\<not> snd cf1 \<approx> s'"
    with `snd cf1 \<approx> snd cf2` `fst cf1 \<approx>s fst cf2` have "\<not> snd cf1 \<approx> s' \<and> \<not> snd cf2 \<approx> s'"
      by (metis indis_trans indis_sym)
    then show ?case
      by auto
  qed
next
  case (Suc n)
  note `cf1 \<in> reachable st1`[simp] `cf2 \<in> reachable st2`[simp]

  from Sbis_mC_C `fst cf1 \<approx>s fst cf2` `snd cf1 \<approx> snd cf2`
  obtain P F where mP: "mC_C Sbis (fst cf1) (fst cf2) (snd cf1) (snd cf2) P F"
    by blast
  then have
    P: "part {..<brn (fst cf1)} P" "{} \<notin> P" and
    FP: "part {..<brn (fst cf2)} (F`P)" "{} \<notin> F ` P" "inj_on F P" and
    W: "\<And>I. I \<in> P \<Longrightarrow> setsum (wt (fst cf1) (snd cf1)) I = setsum (wt (fst cf2) (snd cf2)) (F I)" and
    eff: "\<And>I i j. I \<in> P \<Longrightarrow> i \<in> I \<Longrightarrow> j \<in> F I \<Longrightarrow>
      eff (fst cf1) (snd cf1) i \<approx> eff (fst cf2) (snd cf2) j" and
    cont: "\<And>I i j. I \<in> P \<Longrightarrow> i \<in> I \<Longrightarrow> j \<in> F I \<Longrightarrow>
      cont (fst cf1) (snd cf1) i \<approx>s cont (fst cf2) (snd cf2) j"
    unfolding mC_C_def mC_C_eff_cont_def mC_C_part_def mC_C_wt_def by metis+
  { fix cf1 st1 P assume cf[simp]: "cf1 \<in> reachable st1" and P: "part {..<brn (fst cf1)} P"
    have "?P st1 cf1 (Suc n) = (\<integral>cf'. ?P st1 cf' n \<partial>trans st1 cf1)"
      by (subst prob_iterate_Collect) simp_all
    also have "\<dots> = (\<Sum>b<brn (fst cf1). wt (fst cf1) (snd cf1) b * ?P st1 (cont_eff cf1 b) n)"
      unfolding integral_trans[OF cf] ..
    also have "\<dots> = (\<Sum>I\<in>P. \<Sum>b\<in>I. wt (fst cf1) (snd cf1) b * ?P st1 (cont_eff cf1 b) n)"
      unfolding part_setsum[OF P] ..
    finally have "?P st1 cf1 (Suc n) = \<dots>" . }
  note split = this

  { fix I i assume "I \<in> P" "i \<in> I"
    with `cf1 \<in> reachable st1` have "i < brn (fst cf1)"
      using part_is_subset[OF P(1) `I \<in> P`] by auto }
  note brn_cf[simp] = this

  { fix I i assume "I \<in> P" "i \<in> F I"
    with `cf2 \<in> reachable st2` have "i < brn (fst cf2)"
      using part_is_subset[OF FP(1), of "F I"] by auto }
  note brn_cf2[simp] = this

  { fix I assume "I \<in> P"
    with `{} \<notin> P` obtain i where "i \<in> I" by (metis all_not_in_conv)
    from `I \<in> P` FP have "F I \<noteq> {}" "F I \<subseteq> {..<brn (fst cf2)}"
      by (auto simp: part_is_subset)
    then obtain j where "j < brn (fst cf2)" "j \<in> F I" by auto
    { fix b assume "b \<in> F I"
      then have "?P st1 (cont_eff cf1 i) n = ?P st2 (cont_eff cf2 b) n"
        using `I \<in> P` `i \<in> I` cont eff
        by (intro Suc) (auto simp add: fst_cont_eff snd_cont_eff intro: reachable_cont_eff) }
    note cont_d_const = this[symmetric]
    { fix a assume "a \<in> I"
      with `I \<in> P` `i \<in> I` `j \<in> F I` cont eff
      have "?P st1 (cont_eff cf1 i) n = ?P st2 (cont_eff cf2 j) n \<and>
        ?P st1 (cont_eff cf1 a) n = ?P st2 (cont_eff cf2 j) n"
        by (intro conjI Suc) (auto simp add: fst_cont_eff snd_cont_eff intro: reachable_cont_eff)
      then have "?P st1 (cont_eff cf1 a) n = ?P st1 (cont_eff cf1 i) n" by simp }
    then have "(\<Sum>b\<in>I. wt (fst cf1) (snd cf1) b * ?P st1 (cont_eff cf1 b) n) =
        (\<Sum>b\<in>I. wt (fst cf1) (snd cf1) b) * ?P st1 (cont_eff cf1 i) n"
      by (simp add: setsum_left_distrib)
    also have "\<dots> = (\<Sum>b\<in>F I. wt (fst cf2) (snd cf2) b) * ?P st1 (cont_eff cf1 i) n"
      using W `I \<in> P` by auto
    also have "\<dots> = (\<Sum>b\<in>F I. wt (fst cf2) (snd cf2) b * ?P st2 (cont_eff cf2 b) n)"
      using cont_d_const by (auto simp add: setsum_left_distrib)
    finally have "(\<Sum>b\<in>I. wt (fst cf1) (snd cf1) b * ?P st1 (cont_eff cf1 b) n) = \<dots>" . }
  note sum_eq = this

  have "?P st1 cf1 (Suc n) = (\<Sum>I\<in>P. \<Sum>b\<in>I. wt (fst cf1) (snd cf1) b * ?P st1 (cont_eff cf1 b) n)"
    using `cf1 \<in> reachable st1` P(1) by (rule split)
  also have "\<dots> = (\<Sum>I\<in>P. \<Sum>b\<in>F I. wt (fst cf2) (snd cf2) b * ?P st2 (cont_eff cf2 b) n)"
    using sum_eq by simp
  also have "\<dots> = (\<Sum>I\<in>F`P. \<Sum>b\<in>I. wt (fst cf2) (snd cf2) b * ?P st2 (cont_eff cf2 b) n)"
    using `inj_on F P` by (simp add: setsum_reindex)
  also have "\<dots> = ?P st2 cf2 (Suc n)"
    using `cf2 \<in> reachable st2` FP(1) by (rule split[symmetric])
  finally show ?case .
qed

subsection {* Final Theorems *}

theorem ZObis_eSec: "\<lbrakk>proper c; c \<approx>01 c; aeT c\<rbrakk> \<Longrightarrow> eSec c"
  by (auto simp: aeT_def eSec_def intro!: Ps_eq[simplified] reachable_start)

theorem Sbis_amSec: "\<lbrakk>proper c; c \<approx>s c\<rbrakk> \<Longrightarrow> amSec c"
  by (auto simp: amSec_def intro!: Sbis_trace[simplified] reachable_start)

theorem amSec_eSec:
  assumes [simp]: "proper c" and "aeT c" "amSec c" shows "eSec c"
proof (unfold eSec_def, intro allI impI)
  fix s1 s2 t assume "s1 \<approx> s2"
  let ?T = "\<lambda>s bT. qstermT (c, s) bT \<and> eff_at (c,s) bT (qsend (c,s) bT) \<approx> t"
  let ?P = "\<lambda>s. \<P>(bT in paths (c, s) (c, s). ?T s bT)"

  have s1[simp]: "(c,s1) \<in> reachable (c,s1)" and s2[simp]: "(c,s2) \<in> reachable (c,s2)"
    by (auto intro: reachable_start)

  have "dist (?P s1) (?P s2) = 0"
    unfolding dist_real_def
  proof (rule field_abs_le_zero_epsilon)
    fix e :: real assume "0 < e"
    then have "0 < e / 2" by simp
    let ?N = "\<lambda>s n bT. \<not> discrCf (case_nat (c,s) bT n)"
    from AE_T_max_qsend[OF s1 _ `0 < e / 2`] obtain N1 where N1: "\<P>(bT in paths (c,s1) (c, s1). ?N s1 N1 bT) < e / 2"
      using `aeT c` unfolding aeT_def by auto
    from AE_T_max_qsend[OF s2 _ `0 < e / 2`] obtain N2 where N2: "\<P>(bT in paths (c,s2) (c, s2). ?N s2 N2 bT) < e / 2"
      using `aeT c` unfolding aeT_def by auto
    def N \<equiv> "max N1 N2"

    let ?Tn = "\<lambda>n s bT. eff_at (c,s) bT n \<approx> t"

    have "dist \<P>(bT in paths (c, s1) (c, s1). ?T s1 bT) \<P>(bT in paths (c, s1) (c, s1). ?Tn N s1 bT) \<le>
        \<P>(bT in paths (c, s1) (c, s1). ?N s1 N1 bT)"
      using `aeT c`[unfolded aeT_def, rule_format] AE_validT[OF s1] AE_space
    proof (intro finite_measure_dist, eventually_elim, simp, intro impI)
      fix bT assume T: "qstermT (c,s1) bT" and bT: "validT (c,s1) bT" "discrCf (case_nat (c,s1) bT N1)"
      with bT have "qsend (c,s1) bT \<le> N1"
        by (auto intro!: reachable_start qsend_le)
      also have "\<dots> \<le> N"
        by (auto simp: N_def)
      finally have "eff_at (c, s1) bT N \<approx> eff_at (c, s1) bT (qsend (c,s1) bT)"
        using bT T qsend_leD[of "(c,s1)" bT N] by auto
      with T bT show "eff_at (c,s1) bT (qsend (c,s1) bT) \<approx> t \<longleftrightarrow> ?Tn N s1 bT"
        by (auto intro: indis_trans indis_sym)
    qed simp_all
    moreover
    have "dist \<P>(bT in paths (c, s2) (c, s2). ?T s2 bT) \<P>(bT in paths (c, s2) (c, s2). ?Tn N s2 bT) \<le>
        \<P>(bT in paths (c, s2) (c, s2). ?N s2 N2 bT)"
      using `aeT c`[unfolded aeT_def, rule_format] AE_validT[OF s2] AE_space
    proof (intro finite_measure_dist, eventually_elim, simp, intro impI)
      fix bT assume T: "qstermT (c,s2) bT" and bT: "validT (c,s2) bT" "discrCf (case_nat (c,s2) bT N2)"
      with bT have "qsend (c,s2) bT \<le> N2"
        by (auto intro!: reachable_start qsend_le)
      also have "\<dots> \<le> N"
        by (auto simp: N_def)
      finally have "eff_at (c, s2) bT N \<approx> eff_at (c, s2) bT (qsend (c,s2) bT)"
        using bT T qsend_leD[of "(c,s2)" bT N] by auto
      with T bT show "eff_at (c,s2) bT (qsend (c,s2) bT) \<approx> t \<longleftrightarrow> ?Tn N s2 bT"
        by (auto intro: indis_trans indis_sym)
    qed simp_all
    ultimately have "dist \<P>(bT in paths (c, s1) (c, s1). ?T s1 bT) \<P>(bT in paths (c, s1) (c, s1). ?Tn N s1 bT) +
      dist \<P>(bT in paths (c, s2) (c, s2). ?T s2 bT) \<P>(bT in paths (c, s1) (c, s1). ?Tn N s1 bT) \<le> e"
      using `amSec c`[unfolded amSec_def, rule_format, OF `s1 \<approx> s2`, of N t]
      using N1 N2 by simp
    from dist_triangle_le[OF this]
    show "\<bar>?P s1 - ?P s2\<bar> \<le> e" by (simp add: dist_real_def)
  qed
  then show "?P s1 = ?P s2"
    by simp
qed

end

end
