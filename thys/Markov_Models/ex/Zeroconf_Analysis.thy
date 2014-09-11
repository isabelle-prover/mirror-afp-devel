(* Author: Johannes Hölzl <hoelzl@in.tum.de> *)

header {* Formalizing the IPv4-address allocation in ZeroConf *}

theory Zeroconf_Analysis
  imports "../Discrete_Time_Markov_Chain"
begin

subsection {* Definition of a ZeroConf allocation run *}

locale Zeroconf_Analysis =
  fixes N :: nat and p q r e :: real
  assumes p: "0 < p" "p < 1" and q: "0 < q" "q < 1"
  assumes r: "0 \<le> r" and e: "0 \<le> e"

datatype_new zc_state = start 
                  | probe nat
                  | ok
                  | error

context Zeroconf_Analysis
begin

definition "S = probe ` {.. N} \<union> ({start} \<union> {ok} \<union> {error})"

primrec \<tau> where
  "\<tau> start     = (\<lambda>_. 0) (probe 0 := q, ok := 1 - q)"
| "\<tau> (probe n) = (if n < N then (\<lambda>_. 0) (probe (Suc n) := p, start := 1 - p) 
                           else (\<lambda>_. 0) (error := p, start := 1 - p))"
| "\<tau> ok        = (\<lambda>_. 0) (ok := 1)"
| "\<tau> error     = (\<lambda>_. 0) (error := 1)"

primrec \<rho> where
  "\<rho> start     = (\<lambda>_. 0) (probe 0 := r, ok := r * (N + 1))"
| "\<rho> (probe n) = (if n < N then (\<lambda>_. 0) (probe (Suc n) := r) else (\<lambda>_. 0) (error := e))"
| "\<rho> ok        = (\<lambda>_. 0) (ok := 0)"
| "\<rho> error     = (\<lambda>_. 0) (error := 0)"

lemma inj_probe: "inj_on probe X"
  by (simp add: inj_on_def)

lemma setsum_S:
  "(\<Sum>s\<in>S. f s) = f start + (\<Sum>p\<le>N. f (probe p)) + f ok + f error"
  unfolding S_def
  by (subst setsum.union_disjoint) (auto simp: inj_probe setsum.reindex field_simps)

lemma SE:
  assumes "s \<in> S"
  obtains n where "n \<le> N" "s = probe n" | "s = start" | "s = ok" | "s = error"
  using assms unfolding S_def by blast

lemma SI[intro!, simp]:
  "start \<in> S"
  "ok \<in> S"
  "error \<in> S"
  "n \<le> N \<Longrightarrow> probe n \<in> S"
  by (auto simp: S_def)

end

subsection {* The allocation run is a rewarded DTMC *}

sublocale Zeroconf_Analysis \<subseteq> Rewarded_DTMC S start \<tau> \<rho> "\<lambda>s. 0"
  proof
  qed (insert p q r e,
       auto simp add: S_def \<rho>_def setsum_S setsum.If_cases field_simps elim!: SE)

lemma if_mult:
  "\<And>P a b c. (if P then a else b) * c =  (if P then a * c else b * c)"
  "\<And>P a b c. c * (if P then a else b) =  (if P then c * a else c * b)"
  by auto

context Zeroconf_Analysis
begin

lemma E_start_iff[simp]: "E start = {probe 0, ok}"
  using q by (auto simp: E_iff dest!: E_D)

lemma E_probe_iff[simp]:
    "n \<le> N \<Longrightarrow> E (probe n) = (if n < N then {start, probe (Suc n)} else {start, error})"
  using q p by (auto simp: E_iff dest!: E_D)

lemma E_ok_iff[simp]: "E ok = {ok}" by (auto simp: E_iff dest!: E_D)

lemma E_error_iff[simp]: "E error = {error}" by (auto simp: E_iff dest!: E_D)

lemma pos_neg_q_pn: "0 < 1 - q * (1 - p^Suc N)"
proof -
  have "p ^ Suc N \<le> 1 ^ Suc N"
    using p by (intro power_mono) auto
  with p q have "q * (1 - p^Suc N) < 1 * 1"
    by (intro mult_strict_mono) (auto simp: field_simps simp del: power_Suc)
  then show ?thesis by simp
qed

subsection {* Probability of a erroneous allocation *}

definition "P_err s = \<P>(\<omega> in paths s. case_nat s \<omega> \<in> until S {error})"

lemma P_err_ok: "P_err ok = 0"
proof -
  have "reachable (S - {error}) ok \<subseteq> {ok}"
    by (rule reachable_closed) auto
  then show "P_err ok = 0"
    unfolding P_err_def 
    by (subst prob_Collect_eq_0) (auto simp add: AE_nuntil_iff_not_reachable simp del: case_nat_until_iff)
qed

lemma P_err_error[simp]: "P_err error = 1"
  by (simp add: P_err_def)

lemma P_err_sum': "s \<in> S \<Longrightarrow> s \<noteq> error \<Longrightarrow> P_err s = (\<Sum>t\<in>S. \<tau> s t * P_err t)"
  unfolding P_err_def
  by (subst prob_eq_sum)
     (auto intro!: setsum.cong arg_cong2[where f="op *"] arg_cong2[where f=measure] simp: space_PiM PiE_def)

lemma P_err_sum: "s \<in> S \<Longrightarrow> 
    P_err s = \<tau> s start * P_err start + \<tau> s error + (\<Sum>p\<le>N. \<tau> s (probe p) * P_err (probe p))"
  using P_err_ok by (cases "s = error") (simp_all add: P_err_sum'[of s] setsum_S)

lemma P_err_last[simp]: "P_err (probe N) = p + (1 - p) * P_err start"
  by (subst P_err_sum) simp_all

lemma P_err_start[simp]: "P_err start = q * P_err (probe 0)"
  by (subst P_err_sum) (simp_all add: if_mult setsum.If_cases)

lemma P_err_probe: "n \<le> N \<Longrightarrow> P_err (probe (N - n)) = p ^ Suc n + (1 - p^Suc n) * P_err start"
proof (induct n)
  case (Suc n)
  then have "P_err (probe (N - Suc n)) =
    p * (p ^ Suc n + (1 - p^Suc n) * P_err start) + (1 - p) * P_err start"
    by (subst P_err_sum) (simp_all add: Suc_diff_Suc if_mult setsum.If_cases)
  also have "\<dots> = p^Suc (Suc n) + (1 - p^Suc (Suc n)) * P_err start"
    by (simp add: field_simps)
  finally show ?case .
qed simp

lemma prob_until_error: "P_err start = (q * p ^ Suc N) / (1 - q * (1 - p ^ Suc N))"
  using P_err_probe[of N] pos_neg_q_pn by (simp add: field_simps del: power_Suc)

subsection {* An allocation run terminates almost surely *}

lemma reachable_probe_error:
  "n \<le> N \<Longrightarrow> error \<in> reachable (S - {error, ok}) (probe n)"
proof (induct rule: inc_induct)
  case (step n) 
  then show ?case by (intro reachable_step_rev[of _ _ "probe (Suc n)" "probe n"]) auto
qed (auto intro!: reachable.start)

lemma reachable_start_error:
  "error \<in> reachable (S - {error, ok}) start"
  by (rule reachable_step_rev) (auto intro: reachable_probe_error)

lemma AE_reaches_error_or_ok:
  assumes "s \<in> S"
  shows "AE \<omega> in paths s. case_nat s \<omega> \<in> until S {error, ok}"
  apply (subst AE_until_iff_reachable[OF `s \<in> S` finite_Diff, OF finite_S])
proof (intro disjCI conjI `s\<in>S` ballI)
  fix t assume "t \<in> reachable (S - {error, ok}) s \<union> {s} - {error, ok}"
  with `s \<in> S` have "t \<in> S - {error, ok}" by auto
  with `s \<in> S` have "t \<in> {start} \<union> (probe ` {..N})" by (auto simp: S_def)
  with reachable_probe_error reachable_start_error
  have "error \<in> reachable (S - {error, ok}) t" by auto
  then show "reachable (S - {error, ok}) t \<inter> {error, ok} \<noteq> {}" by auto
qed auto

subsection {* Expected runtime of an allocation run *}

definition "R s = (\<integral>\<^sup>+ \<omega>. reward_until {error, ok} (case_nat s \<omega>) \<partial>paths s)"

lemma cost_from_start:
  "(R start::ereal) =
    (q * (r + p^Suc N * e + r * p * (1 - p^N) / (1 - p)) + (1 - q) * (r * Suc N)) /
    (1 - q + q * p^Suc N)"
proof -
  have "\<forall>s\<in>S. \<exists>r. R s = ereal r"
    unfolding R_def
    using nn_integral_reward_until_finite[OF _ AE_reaches_error_or_ok] by auto
  from bchoice[OF this] obtain R' where R': "\<And>s. s\<in>S \<Longrightarrow> R s = ereal (R' s)" by auto

  have R_sum: "\<And>s. s \<in> S \<Longrightarrow> s \<noteq> error \<Longrightarrow> s \<noteq> ok \<Longrightarrow>
    R s = (\<Sum>s'\<in>S. \<tau> s s' * (\<rho> s s' + R s'))"
    using R' unfolding R_def
    by (subst nn_integral_reward_until_real[OF _ _ AE_reaches_error_or_ok]) simp_all
       
  then have R'_sum: "\<And>s. s \<in> S \<Longrightarrow> s \<noteq> error \<Longrightarrow> s \<noteq> ok \<Longrightarrow>
    R' s = (\<Sum>s'\<in>S. \<tau> s s' * (\<rho> s s' + R' s'))"
    using R' by simp

  have "R ok = 0" "R error = 0"
    unfolding R_def by (simp_all add: reward_until_case_nat_0)
  with R' have R'_ok: "R' ok = 0" and R'_error: "R' error = 0"
    by simp_all

  then have R'_start: "R' start = q * (r + R' (probe 0)) + (1 - q) * (r * (N + 1))"
    by (subst R'_sum)
       (simp_all add: setsum_S field_simps setsum.distrib if_mult setsum.If_cases)

  have R'_probe: "\<And>n. n < N \<Longrightarrow> R' (probe n) = p * R' (probe (Suc n)) + p * r + (1 - p) * R' start"
    using R'_error
    by (subst R'_sum)
       (simp_all add: setsum_S setsum.distrib field_simps if_mult setsum.If_cases)

  have R'_N: "R' (probe N) = p * e + (1 - p) * R' start"
    using R'_error by (subst R'_sum) (simp_all add: setsum_S field_simps)

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

interpretation ZC: Zeroconf_Analysis 2 "16 / 65024 :: real" "0.01" "0.002" "3600"
  apply default
  apply auto
  done

lemma "ZC.P_err start \<le> 1 / 10^12"
  unfolding ZC.prob_until_error by (simp add: power_one_over[symmetric])

lemma "ZC.R start \<le> 0.007"
  unfolding ZC.cost_from_start by (simp add: power_one_over[symmetric])

end