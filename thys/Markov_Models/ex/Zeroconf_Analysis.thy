(* Author: Johannes Hölzl <hoelzl@in.tum.de> *)

section {* Formalizing the IPv4-address allocation in ZeroConf *}

theory Zeroconf_Analysis
  imports "../Discrete_Time_Markov_Chain"
begin

lemma (in MC_with_rewards) reward_until_SCons[simp]:
  "reward_until X s (t ## \<omega>) = (if s \<in> X then 0 else \<rho> s + \<iota> s t + reward_until X t \<omega>)"
  by simp

lemmas [simp] = set_pmf_bernoulli UNIV_bool

lemma integral_map_pmf:
  fixes f :: "'a \<Rightarrow> 'b::{banach, second_countable_topology}"
  shows "integral\<^sup>L (measure_pmf (map_pmf g p)) f = integral\<^sup>L p (\<lambda>x. f (g x))"
  by (simp add: integral_distr map_pmf_rep_eq)

subsection {* Definition of a ZeroConf allocation run *}

datatype zc_state = start 
                  | probe nat
                  | ok
                  | error

lemma inj_probe: "inj_on probe X"
  by (auto simp: inj_on_def)

text {* Countability of @{typ zc_state} simplifies measurability of functions on @{typ zc_state}. *}

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

abbreviation states where
  "states \<equiv> probe ` {.. N} \<union> {start, ok, error}"

primrec \<tau> :: "zc_state \<Rightarrow> zc_state pmf" where
  "\<tau> start     = map_pmf (\<lambda>True \<Rightarrow> probe 0 | False \<Rightarrow> ok) (bernoulli_pmf q)"
| "\<tau> (probe n) = map_pmf (\<lambda>True \<Rightarrow> (if n < N then probe (Suc n) else error) | False \<Rightarrow> start) (bernoulli_pmf p)"
| "\<tau> ok        = return_pmf ok"
| "\<tau> error     = return_pmf error"

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

lemma enabled_ok: "enabled ok \<omega> \<longleftrightarrow> \<omega> = sconst ok"
  by (simp add: enabled_iff_sconst)

lemma finite_E[intro, simp]: "finite (E s)"
  by (cases s) auto

lemma E_closed: "s \<in> states \<Longrightarrow> E s \<subseteq> states"
  using p q by (cases s) (auto split: bool.splits)

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

lemma to_error: assumes "n \<le> N" shows "(probe n, error) \<in> acc"
  using `n \<le> N`
proof (induction rule: inc_induct)
  case (step n') with p show ?case
    by (intro rtrancl_trans[OF r_into_rtrancl step.IH]) auto
qed (insert p, auto)

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
    "\<And>n. n < N \<Longrightarrow> p_probe n = p_probe (Suc n) * p + p_start * (1 - p)"
    "p_probe N = p + p_start * (1 - p)"
    using p q
    by (auto simp: p_probe_def p_start_def power_Suc[symmetric] Suc_diff_Suc divide_simps
             simp del: power_Suc)
       (auto simp: field_simps)
  fix s assume s: "s \<in> states - {ok, error}"
  then show "?E s = (\<integral>t. ?E t \<partial>\<tau> s) + 0"
    using p q by (auto simp add: integral_map_pmf intro: p_eq)
  show "\<exists>t\<in>{ok, error}. (s, t) \<in> acc"
    using s q to_error by auto
  from s show "P_err s = integral\<^sup>L (measure_pmf (\<tau> s)) P_err + 0"
    unfolding P_err_def[abs_def] by (subst prob_T) (auto simp: ev_Stream simp del: UNIV_bool)
next
  fix s assume "s \<in> {ok, error}" then show "P_err s = ?E s"
    by (auto intro!: T.prob_eq_0_AE T.prob_Collect_eq_1[THEN iffD2]
             simp: P_err_def AE_sconst ev_sconst HLD_iff ev_Stream T.prob_space
             simp del: space_T sets_T )
qed (insert p q, auto intro!: integrable_measure_pmf_finite split: split_if_asm)

lemma P_err_start: "P_err start = (q * p ^ Suc N) / (1 - q * (1 - p ^ Suc N))"
  by (simp add: P_err)

subsection {* An allocation run terminates almost surely *}

lemma states_closed:
  assumes "s \<in> states"
  assumes "(s, t) \<in> acc_on (- {error, ok})"
  shows "t \<in> states"
  using assms(2,1) p q by induction (auto split: split_if_asm)

lemma finite_reached:
  assumes s: "s \<in> states" shows "finite (acc_on (- {error, ok}) `` {s})"
  using states_closed[OF s]
  by (rule_tac finite_subset[of _ states]) auto

lemma AE_reaches_error_or_ok:
  assumes s: "s \<in> states"
  shows "AE \<omega> in T s. ev (HLD {error, ok}) \<omega>"
proof (rule AE_T_ev_HLD)
  { fix t assume t: "(s, t) \<in> acc_on (- {error, ok})"
    with states_closed[OF s t] to_error p q show "\<exists>t'\<in>{error, ok}. (t, t') \<in> acc"
      by auto }
qed (rule finite_reached[OF s])

subsection {* Expected runtime of an allocation run *}

definition "R s = (\<integral>\<^sup>+ \<omega>. reward_until {error, ok} s \<omega> \<partial>T s)"

lemma R_iter: "s \<noteq> error \<Longrightarrow> s \<noteq> ok \<Longrightarrow> R s = (\<integral>\<^sup>+t. ereal (\<rho> s t) + R t \<partial>\<tau> s)"
  unfolding R_def using T.emeasure_space_1
  by (subst nn_integral_T)
     (auto simp del: \<tau>.simps \<rho>.simps simp add: AE_measure_pmf_iff nn_integral_add reward_until_nonneg
           intro!: nn_integral_cong_AE)

lemma R_finite:
  assumes s: "s \<in> states"
  shows "R s \<noteq> \<infinity>"
  unfolding R_def
proof (rule nn_integral_reward_until_finite)
  { fix t assume "(s, t) \<in> acc" from this s p q have "t \<in> states"
      by induction (auto split: split_if_asm) } 
  then have "acc `` {s} \<subseteq> states"
    by auto
  then show "finite (acc `` {s})"
    by (auto dest: finite_subset)
qed (auto simp: AE_reaches_error_or_ok[OF s])

lemma R_nonneg: "0 \<le> R t"
  by (simp add: R_def nn_integral_nonneg)

lemma cost_from_start:
  "R start =
    (q * (r + p^Suc N * e + r * p * (1 - p^N) / (1 - p)) + (1 - q) * (r * Suc N)) /
    (1 - q + q * p^Suc N)"
proof -
  have ok_error: "R ok = 0 \<and> R error = 0"
    unfolding R_def by (subst (1 2) reward_until_unfold[abs_def]) simp

  then have R_start: "R start = q * (r + R (probe 0)) + (1 - q) * (r * (N + 1))"
    using q r by (subst R_iter) (simp_all add: R_nonneg field_simps)
  
  have R_probe: "\<And>n. n < N \<Longrightarrow> R (probe n) = p * R (probe (Suc n)) + p * r + (1 - p) * R start"
    using p r by (subst R_iter) (simp_all add: R_nonneg field_simps ereal_right_distrib zero_ereal_def[symmetric])

  have R_N: "R (probe N) = p * e + (1 - p) * R start"
    using p e ok_error by (subst R_iter) (auto simp: R_nonneg zero_ereal_def[symmetric] mult.commute)

  { fix n
    assume "n \<le> N"
    then have "R (probe (N - n)) =
      p ^ Suc n * e + (1 - p^n) * r * p / (1 - p) + (1 - p^Suc n) * R start"
    proof (induct n)
      case 0 with R_N show ?case by simp
    next
      case (Suc n)
      moreover then have "Suc (N - Suc n) = N - n" by simp
      ultimately show ?case
        using R_probe[of "N - Suc n"] p R_nonneg[of start] R_finite[of start]
        by (cases "R start") (simp_all add: field_simps)
    qed }
  from this[of N]
  have "R (probe 0) = p ^ Suc N * e + (1 - p^N) * r * p / (1 - p) + (1 - p^Suc N) * R start"
    by simp
  then have "R start - q * (1 - p^Suc N) * R start =
    q * (r + p^Suc N * e + (1 - p^N) * r * p / (1 - p)) + (1 - q) * (r * (N + 1))"
    using R_nonneg[of start] R_finite[of start] by (subst R_start) (cases "R start", simp_all add: field_simps)
  then have "R start = (q * (r + p^Suc N * e + (1 - p^N) * r * p / (1 - p)) + (1 - q) * (r * Suc N)) /
    (1 - q * (1 - p^Suc N))"
    using pos_neg_q_pn R_nonneg[of start] R_finite[of start] by (cases "R start") (simp_all add: field_simps)
  then show ?thesis
    by (simp add: field_simps)
qed

end

interpretation ZC: Zeroconf_Analysis 2 "16 / 65024 :: real" "0.01" "0.002" "3600"
  by standard auto

lemma "ZC.P_err start \<le> 1 / 10^12"
  unfolding ZC.P_err_start by (simp add: power_divide power_one_over[symmetric])

lemma "ZC.R start \<le> 0.007"
  unfolding ZC.cost_from_start by (simp add: power_divide power_one_over[symmetric])

end
