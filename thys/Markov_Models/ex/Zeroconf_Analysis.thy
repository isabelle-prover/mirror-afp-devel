(* Author: Johannes Hölzl <hoelzl@in.tum.de> *)

section {* Formalizing the IPv4-address allocation in ZeroConf *}

theory Zeroconf_Analysis
  imports "../Discrete_Time_Markov_Chain"
begin

subsection {* Definition of a ZeroConf allocation run *}

datatype zc_state = start 
                  | probe nat
                  | ok
                  | error

lemma inj_probe: "inj_on probe X"
  by (simp add: inj_on_def)

instance zc_state :: countable
proof
  have "countable ({start, ok, error} \<union> probe`UNIV)"
    by auto
  also have "{start, ok, error} \<union> probe`UNIV = UNIV"
    using zc_state.nchotomy by auto
  finally show "\<exists>f::zc_state \<Rightarrow> nat. inj f"
    using inj_on_to_nat_on[of "UNIV :: zc_state set"] by auto
qed

locale Zeroconf_Analysis =
  fixes N :: nat and p q r e :: real
  assumes p: "0 < p" "p < 1" and q: "0 < q" "q < 1"
  assumes r: "0 \<le> r" and e: "0 \<le> e"
begin

interpretation pmf_as_function .

abbreviation "states == probe ` {.. N} \<union> ({start} \<union> {ok} \<union> {error})"

lift_definition \<tau> :: "zc_state \<Rightarrow> zc_state pmf" is
  "\<lambda>start   \<Rightarrow> ((\<lambda>_. 0) (probe 0 := q, ok := 1 - q))
  | probe n \<Rightarrow> if n < N then (\<lambda>_. 0) (probe (Suc n) := p, start := 1 - p) 
                           else (\<lambda>_. 0) (error := p, start := 1 - p)
  | ok      \<Rightarrow> ((\<lambda>_. 0) (ok := 1))
  | error   \<Rightarrow> ((\<lambda>_. 0) (error := 1))"
  using q p
  by (auto split: zc_state.splits split_if_asm simp: setsum.If_cases
           intro!: nn_integral_count_space'[where A="states", THEN trans])

primrec \<rho> :: "zc_state \<Rightarrow> zc_state \<Rightarrow> real" where
  "\<rho> start     = (\<lambda>_. 0) (probe 0 := r, ok := r * (N + 1))"
| "\<rho> (probe n) = (if n < N then (\<lambda>_. 0) (probe (Suc n) := r) else (\<lambda>_. 0) (error := e))"
| "\<rho> ok        = (\<lambda>_. 0) (ok := 0)"
| "\<rho> error     = (\<lambda>_. 0) (error := 0)"

lemma \<rho>_nonneg'[simp]: "0 \<le> \<rho> s t"
  using r e by (cases s) auto

sublocale MC_with_rewards \<tau> \<rho> "\<lambda>s. 0"
  proof qed (simp_all add: pair_measure_countable)

subsection {* The allocation run is a rewarded DTMC *}

abbreviation "E s \<equiv> set_pmf (\<tau> s)"

lemma E_start_iff[simp]: "E start = {probe 0, ok}"
  using q unfolding set_eq_iff set_pmf_iff by transfer simp

lemma E_probe_iff[simp]:
  "E (probe n) = (if n < N then {start, probe (Suc n)} else {start, error})"
  using p q unfolding set_eq_iff set_pmf_iff by transfer simp

lemma E_ok_iff[simp]: "E ok = {ok}"
  unfolding set_eq_iff set_pmf_iff by transfer simp

lemma enabled_ok: "enabled ok \<omega> \<longleftrightarrow> \<omega> = sconst ok"
  by (simp add: enabled_iff_sconst)

lemma E_error_iff[simp]: "E error = {error}"
  unfolding set_eq_iff set_pmf_iff by transfer simp

lemma finite_E[intro, simp]: "finite (E s)"
  by (cases s) auto

lemma E_closed: "s \<in> states \<Longrightarrow> E s \<subseteq> states"
  by (auto split: split_if_asm)

lemma enabled_error: "enabled error \<omega> \<longleftrightarrow> \<omega> = sconst error"
  by (simp add: enabled_iff_sconst)

lemma pos_neg_q_pn: "0 < 1 - q * (1 - p^Suc N)"
proof -
  have "p ^ Suc N \<le> 1 ^ Suc N"
    using p by (intro power_mono) auto
  with p q have "q * (1 - p^Suc N) < 1 * 1"
    by (intro mult_strict_mono) (auto simp: field_simps simp del: power_Suc)
  then show ?thesis by simp
qed

lemma to_error: assumes "n \<le> N" shows "(probe n, error) \<in> (Sigma UNIV E)\<^sup>*"
  using `n \<le> N`
proof (induction rule: inc_induct)
  case (step n') then show ?case
    by (intro rtrancl_trans[OF r_into_rtrancl step.IH]) auto
qed auto

subsection {* Probability of a erroneous allocation *}

definition "P_err s = \<P>(\<omega> in T s. ev (HLD {error}) (s ## \<omega>))"

lemma P_err: 
  defines "p_start == (q * p ^ Suc N) / (1 - q * (1 - p ^ Suc N))"
  defines "p_probe == (\<lambda>n. p ^ Suc (N - n) + (1 - p^Suc (N - n)) * p_start)"
  assumes s: "s \<in> states - {ok, error}"
  shows "P_err s = (case s of ok \<Rightarrow> 0 | error \<Rightarrow> 1 | probe n \<Rightarrow> p_probe n | start \<Rightarrow> p_start)"
    (is "\<dots> = ?E s")
  using s
proof (rule unique_les)
  have [arith]: "0 \<le> p * (q * p ^ N)"
    using p q by simp
  have p_eq: "p_start = p_probe 0 * q"
    "\<And>n. n < N \<Longrightarrow> p_probe n = p_start * (1 - p) + p_probe (Suc n) * p"
    "p_probe N = p + p_start * (1 - p)"
    using p q
    by (auto simp: p_probe_def p_start_def power_Suc[symmetric] Suc_diff_Suc divide_simps
             simp del: power_Suc)
       (auto simp: field_simps)
  fix s assume s: "s \<in> states - {ok, error}"
  then show "?E s = (\<integral>t. ?E t \<partial>\<tau> s) + 0"
    using p q
    by (subst integral_measure_pmf[of states])
       (auto split: zc_state.splits split_if_asm intro: p_eq
             simp: setsum_clauses setsum.reindex inj_probe \<tau>.rep_eq
                   setsum.If_cases if_distrib[where f="\<lambda>x. a * x" for a])
  show "\<exists>t\<in>{ok, error}. (s, t) \<in> (Sigma UNIV E)\<^sup>*"
    using s to_error by auto
  from s show "P_err s = integral\<^sup>L (measure_pmf (\<tau> s)) P_err + 0"
    unfolding P_err_def[abs_def] by (subst prob_T) (auto simp: ev_Stream)
next
  fix s assume "s \<in> {ok, error}" then show "P_err s = ?E s"
    by (auto intro!: T.prob_eq_0_AE T.prob_Collect_eq_1[THEN iffD2]
             simp: P_err_def AE_sconst ev_sconst HLD_iff ev_Stream T.prob_space
             simp del: space_T sets_T )
qed (auto intro!: integrable_measure_pmf_finite split: split_if_asm)

lemma P_err_start: "P_err start = (q * p ^ Suc N) / (1 - q * (1 - p ^ Suc N))"
  by (simp add: P_err)

subsection {* An allocation run terminates almost surely *}

lemma states_closed:
  assumes "s \<in> states"
  assumes "(s, t) \<in> (SIGMA s:UNIV. E s - {error, ok})\<^sup>*"
  shows "t \<in> states"
  using assms(2,1) by induction (auto split: split_if_asm)

lemma finite_reached:
  assumes s: "s \<in> states" shows "finite ((SIGMA s:UNIV. E s - {error, ok})\<^sup>* `` {s})"
  using states_closed[OF s]
  by (rule_tac finite_subset[of _ states]) auto

lemma AE_reaches_error_or_ok:
  assumes s: "s \<in> states"
  shows "AE \<omega> in T s. ev (HLD {error, ok}) \<omega>"
proof (rule AE_T_ev_HLD)
  { fix t assume t: "(s, t) \<in> (SIGMA s:UNIV. E s - {error, ok})\<^sup>*"
    with states_closed[OF s t] to_error show "\<exists>t'\<in>{error, ok}. (t, t') \<in> (Sigma UNIV E)\<^sup>*"
      by auto }
qed (rule finite_reached[OF s])

subsection {* Expected runtime of an allocation run *}

definition "R s = (\<integral>\<^sup>+ \<omega>. reward_until {error, ok} s \<omega> \<partial>T s)"

lemma R_finite:
  assumes s: "s \<in> states"
  shows "R s \<noteq> \<infinity>"
  unfolding R_def
proof (rule nn_integral_reward_until_finite)
  { fix t assume "(s, t) \<in> (Sigma (- {error, ok}) E)\<^sup>*" from this s have "t \<in> states"
      by induction (auto split: split_if_asm) } 
  then have "(Sigma (- {error, ok}) E)\<^sup>* `` {s} \<subseteq> states"
    by auto
  then show "finite ((Sigma (- {error, ok}) E)\<^sup>* `` {s})"
    by (auto dest: finite_subset)
qed (auto simp: AE_reaches_error_or_ok[OF s])

lemma R_nonneg: "0 \<le> R t"
  by (simp add: R_def nn_integral_nonneg)

lemma cost_from_start:
  "R start =
    (q * (r + p^Suc N * e + r * p * (1 - p^N) / (1 - p)) + (1 - q) * (r * Suc N)) /
    (1 - q + q * p^Suc N)"
proof -
  have "\<forall>s\<in>states. \<exists>r. R s = ereal r"
    using R_nonneg R_finite
    apply (intro ballI exI)
    apply (rule ereal_real'[symmetric])+
    apply simp
    done
  from bchoice[OF this] obtain R' where R': "\<And>s. s\<in>states \<Longrightarrow> R s = ereal (R' s)" by auto

  { fix s have "s \<in> states \<Longrightarrow> s \<noteq> error \<Longrightarrow> s \<noteq> ok \<Longrightarrow>
      R s = (\<Sum>s'\<in>states. pmf (\<tau> s) s' * (\<rho> s s' + R s'))"
      using T.emeasure_space_1 E_closed[of s]
      unfolding R_def
      apply (simp add: nn_integral_T[of _ s] nn_integral_add[of _ "T t" for t] reward_until_nonneg 
          nn_integral_measure_pmf_support[of states] nn_integral_nonneg)
      apply (subst nn_integral_measure_pmf_support[of states])
      apply (simp_all add: nn_integral_nonneg subset_eq field_simps)
      done }
  then have R'_sum: "\<And>s. s \<in> states \<Longrightarrow> s \<noteq> error \<Longrightarrow> s \<noteq> ok \<Longrightarrow>
    R' s = (\<Sum>s'\<in>states. pmf (\<tau> s) s' * (\<rho> s s' + R' s'))"
    using R' by simp

  have "R ok = 0 \<and> R error = 0"
    unfolding R_def by (subst (1 2) reward_until_unfold[abs_def]) simp
  with R' have R'_ok: "R' ok = 0" and R'_error: "R' error = 0"
    by simp_all

  then have R'_start: "R' start = q * (r + R' (probe 0)) + (1 - q) * (r * (N + 1))"
    by (subst R'_sum)
       (auto simp: field_simps setsum_clauses setsum.reindex inj_probe setsum.distrib
                   setsum.If_cases if_distrib[of "\<lambda>x. a * x" for a] \<tau>.rep_eq)

  have R'_probe: "\<And>n. n < N \<Longrightarrow> R' (probe n) = p * R' (probe (Suc n)) + p * r + (1 - p) * R' start"
    using R'_error
    by (subst R'_sum)
       (auto simp: field_simps setsum_clauses setsum.reindex inj_probe setsum.distrib
                   setsum.If_cases if_distrib[of "\<lambda>x. a * x" for a] \<tau>.rep_eq)

  have R'_N: "R' (probe N) = p * e + (1 - p) * R' start"
    using R'_error by (subst R'_sum)
       (auto simp: field_simps setsum_clauses setsum.reindex inj_probe setsum.distrib
                   setsum.If_cases if_distrib[of "\<lambda>x. a * x" for a] \<tau>.rep_eq)

  { fix n
    assume "n \<le> N"
    then have "R' (probe (N - n)) =
      p ^ Suc n * e + (1 - p^n) * r * p / (1 - p) + (1 - p^Suc n) * R' start"
    proof (induct n)
      case 0 with R'_N show ?case by simp
    next
      case (Suc n)
      moreover then have "Suc (N - Suc n) = N - n" by simp
      ultimately show ?case
        using R'_probe[of "N - Suc n"] p
        by simp (simp add: field_simps)
    qed }
  from this[of N]
  have "R' (probe 0) = p ^ Suc N * e + (1 - p^N) * r * p / (1 - p) + (1 - p^Suc N) * R' start"
    by simp
  then have "R' start - q * (1 - p^Suc N) * R' start =
    q * (r + p^Suc N * e + (1 - p^N) * r * p / (1 - p)) + (1 - q) * (r * (N + 1))"
    by (subst R'_start) (simp, simp add: field_simps)
  then have "R' start = (q * (r + p^Suc N * e + (1 - p^N) * r * p / (1 - p)) + (1 - q) * (r * Suc N)) /
    (1 - q * (1 - p^Suc N))"
    using pos_neg_q_pn
    by (simp add: field_simps)
  then show ?thesis
    using R' p q by (simp add: field_simps)
qed

end

interpretation ZC!: Zeroconf_Analysis 2 "16 / 65024 :: real" "0.01" "0.002" "3600"
  by default auto

lemma "ZC.P_err start \<le> 1 / 10^12"
  unfolding ZC.P_err_start by (simp add: power_one_over[symmetric])

lemma "ZC.R start \<le> 0.007"
  unfolding ZC.cost_from_start by (simp add: power_one_over[symmetric])

end