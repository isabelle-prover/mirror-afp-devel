(* Author: Johannes Hölzl <hoelzl@in.tum.de> *)

header {* Formalizing the IPv4-address allocation in ZeroConf *}

theory Zeroconf_Analysis
  imports "../Rewarded_DTMC"
begin

subsection {* Definition of a ZeroConf allocation run *}

datatype zc_state = start 
                  | probe nat
                  | ok
                  | error

locale Zeroconf_Analysis =
  fixes last_probe :: nat
  fixes error_cost :: real
  fixes p q :: real and r E :: real
  assumes p: "0 < p" "p < 1"
    and q: "0 < q" "q < 1"
    and r: "0 \<le> r"
    and E: "0 \<le> E"
begin

definition "zc_states = probe ` {.. last_probe} \<union> ({start} \<union> {ok} \<union> {error})"

primrec zc_trans where
  "zc_trans start     = (\<lambda>_. 0) (probe 0 := q, ok := 1 - q)"
| "zc_trans (probe n) = (if n < last_probe then (\<lambda>_. 0) (probe (Suc n) := p, start := 1 - p)
                                           else (\<lambda>_. 0) (error := 1))"
| "zc_trans ok        = (\<lambda>_. 0) (ok := 1)"
| "zc_trans error     = (\<lambda>_. 0) (error := 1)"

primrec zc_cost where
  "zc_cost start     = (\<lambda>_. 0) (probe 0 := r, ok := r * (last_probe + 1))"
| "zc_cost (probe n) = (if n < last_probe then (\<lambda>_. 0) (probe (Suc n) := r, start := 0)
                                          else (\<lambda>_. 0) (error := E))"
| "zc_cost ok        = (\<lambda>_. 0) (ok := 0)"
| "zc_cost error     = (\<lambda>_. 0) (error := 0)"

lemma inj_probe: "inj_on probe X"
  by (simp add: inj_on_def)

lemma setsum_zc_states:
  "(\<Sum>s\<in>zc_states. f s) = f start + (\<Sum>p\<le>last_probe. f (probe p)) + f ok + f error"
  unfolding zc_states_def
  by (subst setsum_Un_disjoint) (auto simp: inj_probe setsum_reindex field_simps)

lemma zc_statesE:
  assumes "s \<in> zc_states"
  obtains n where "n \<le> last_probe" "s = probe n" | "s = start" | "s = ok" | "s = error"
  using assms unfolding zc_states_def by blast

lemma zc_statesI[intro!, simp]:
  "start \<in> zc_states"
  "ok \<in> zc_states"
  "error \<in> zc_states"
  "n \<le> last_probe \<Longrightarrow> probe n \<in> zc_states"
  by (auto simp: zc_states_def)

end

subsection {* The allocation run is a rewarded DTMC *}

sublocale Zeroconf_Analysis \<subseteq> Rewarded_DTMC zc_states start zc_trans zc_cost "\<lambda>s. 0"
proof
  fix s s' assume "s \<in> zc_states" "s' \<in> zc_states"
  with p q show "0 \<le> zc_trans s s'"
    by (auto simp: zc_states_def)
next
  fix s assume "s \<in> zc_states"
  with p q show "(\<Sum>s'\<in>zc_states. zc_trans s s') = 1"
    by (auto simp: setsum_zc_states setsum_cases field_simps elim!: zc_statesE)
next
  fix s s' assume "s \<in> zc_states" "s' \<in> zc_states"
  with r E show "0 \<le> zc_cost s s'"
    by (cases s) (auto simp: mult_nonneg_nonneg)
qed (auto simp add: zc_states_def zc_cost_def)

lemma if_mult:
  "\<And>P a b c. (if P then a else b) * c =  (if P then a * c else b * c)"
  "\<And>P a b c. c * (if P then a else b) =  (if P then c * a else c * b)"
  by auto

context Zeroconf_Analysis
begin

lemma pos_neg_q_pn: "0 < 1 - q * (1 - p^last_probe)"
proof -
  have "p ^ last_probe \<le> 1 ^ last_probe"
    using p by (intro power_mono) auto
  with p q have "q * (1 - p^last_probe) < 1 * 1"
    by (intro mult_strict_mono) (auto simp: field_simps)
  then show ?thesis by simp
qed

subsection {* Probability of a errernous allocation *}

lemma prob_until_error:
  defines "P \<equiv> \<lambda>s. prob s (nat_case s -` until zc_states {error} \<inter> (UNIV \<rightarrow> zc_states))"
  shows "P start = (q * p ^ last_probe) / (1 - q * (1 - p ^ last_probe))"
proof -
  have P_sum: "\<And>s. s \<in> zc_states \<Longrightarrow> s \<noteq> error \<Longrightarrow> P s = (\<Sum>s'\<in>zc_states. zc_trans s s' * P s')"
    unfolding P_def
    by (subst prob_eq_sum) (simp_all add: setsum_zc_states until_Int_space_eq)

  have P_error[simp]: "P error = 1"
    unfolding P_def by simp

  have P_n: "\<And>n. n < last_probe \<Longrightarrow> P (probe n) = p * P (probe (Suc n)) + (1 - p) * P start"
    by (subst P_sum) (auto simp: setsum_zc_states if_mult setsum_cases)
  have P_last: "P (probe last_probe) = 1"
    by (subst P_sum) (auto simp: setsum_zc_states if_mult setsum_cases)

  { fix n
    assume "n \<le> last_probe"
    then have "P (probe (last_probe - n)) = p ^ n + (1 - p^n) * P start"
    proof (induct n)
      case 0 with P_last show ?case by simp
    next
      case (Suc n)
      moreover then have "Suc (last_probe - Suc n) = last_probe - n" by simp
      ultimately show ?case
        using P_n[of "last_probe - Suc n"]
        by simp (simp add: field_simps)
    qed }
  note P_probe = this
  
  have "reachable (zc_states - {error}) ok \<subseteq> {ok}"
    by (rule reachable_closed') auto
  moreover have "ok \<in> reachable (zc_states - {error}) ok"
    by (rule reachable_in) auto
  ultimately have "reachable (zc_states - {error}) ok = {ok}"
    by auto
  then have "P ok = 0"
    using until_eq_0_iff_not_reachable[of ok zc_states "{error}"]
    by (simp add: P_def until_Int_space_eq)
  then have "P start = q * P (probe 0)"
    unfolding P_def
    by (subst prob_eq_sum) (simp_all add: setsum_zc_states until_Int_space_eq if_mult setsum_cases)
  with P_probe[of last_probe]
  have "P start = q * (p ^ last_probe + (1 - p^last_probe) * P start)"
    by simp
  then have "P start * (1 - q * (1 - p^last_probe)) = q * p ^ last_probe"
    by (simp add: field_simps)
  then have "(P start * (1 - q * (1 - p^last_probe))) / (1 - q * (1 - p^last_probe)) =
    (q * p ^ last_probe) / (1 - q * (1 - p^last_probe))"
    by simp
  with pos_neg_q_pn show ?thesis
    by (simp add: field_simps)
qed

lemma reachable_probe_error:
  assumes "n \<le> last_probe"
  shows "error \<in> reachable (zc_states - {error, ok}) (probe n)"
proof -
  def \<omega> \<equiv> "\<lambda>i. if i < last_probe - n then probe (Suc (i + n)) else error"
  show ?thesis
    unfolding reachable_def
  proof (safe intro!: exI[of _ \<omega>]
      exI[of _ "last_probe - n"] del: notI)
    fix i assume "i \<le> last_probe - n"
    with p `n \<le> last_probe` show "zc_trans (nat_case (probe n) \<omega> i) (\<omega> i) \<noteq> 0"
      by (auto simp: \<omega>_def split: nat.split)
  qed (auto simp: \<omega>_def)
qed

lemma reachable_start_error:
  "error \<in> reachable (zc_states - {error, ok}) start"
  using q
  by (intro reachable_probe_error[THEN reachable_step]) auto

subsection {* A allocation run terminates almost surely *}

lemma AE_reaches_error_or_ok:
  assumes "s \<in> zc_states"
  shows "AE \<omega> in path_space s. nat_case s \<omega> \<in> until zc_states {error, ok}"
proof cases
  assume s: "s \<in> {start} \<union> (probe ` {..last_probe})"
  have in_S: "s \<in> zc_states" "zc_states \<subseteq> zc_states" "{error, ok} \<subseteq> zc_states"
    using s by (auto simp: zc_states_def)
  have "s \<notin> {error, ok}"
    using s by auto
  then show ?thesis
    unfolding until_eq_1_if_reachable[OF in_S]
    apply (simp add: insert_absorb)
  proof (intro conjI ballI)
    show "reachable (zc_states - {error, ok}) s \<subseteq> zc_states"
      by (auto simp: reachable_def)
    moreover
    fix t assume "t \<in> insert s (reachable (zc_states - {error, ok}) s) - {error, ok}"
    with s have "(\<exists>n\<le>last_probe. t = probe n) \<or> t = start"
      unfolding reachable_def by (auto simp: zc_states_def)
    then show "error \<in> reachable (zc_states - {error, ok}) t \<or>
      ok \<in> reachable (zc_states - {error, ok}) t"
      using reachable_probe_error reachable_start_error by auto
  qed (insert in_S(1), auto simp: zc_states_def)
next
  assume s: "s \<notin> {start} \<union> (probe ` {..last_probe})"
  with assms have "s \<in> {error, ok}"
    by (auto simp: zc_states_def)
  then show ?thesis
    by (auto intro!: AE_I2 simp: space_path_space Pi_iff)
qed

subsection {* Expected runtime of a allocation run *}

lemma cost_from_start:
  defines "R \<equiv> \<lambda>s. \<integral>\<^isup>+ \<omega>. reward_until {error, ok} (nat_case s \<omega>) \<partial>path_space s"
  shows "(R start::ereal) =
    (r * ((last_probe + 1) * (1 - q) + q * (1 - p ^ (last_probe + 1)) / (1 - p)) + q * p ^ last_probe * E) /
    (1 - q + q * p ^ last_probe)"
proof -
  have "\<forall>s\<in>zc_states. \<exists>r. R s = ereal r"
    unfolding R_def
    using positive_integral_reward_until_finite[OF _ _ AE_reaches_error_or_ok] by auto
  from bchoice[OF this] obtain R' where R': "\<And>s. s\<in>zc_states \<Longrightarrow> R s = ereal (R' s)" by auto

  have R_sum: "\<And>s. s \<in> zc_states \<Longrightarrow> s \<noteq> error \<Longrightarrow> s \<noteq> ok \<Longrightarrow>
    R s = (\<Sum>s'\<in>zc_states. zc_trans s s' * (zc_cost s s' + R s'))"
    using R' unfolding R_def
    by (subst positive_integral_reward_until_real[OF _ _ _ AE_reaches_error_or_ok])
       (simp_all add: until_Int_space_eq)
  then have R'_sum: "\<And>s. s \<in> zc_states \<Longrightarrow> s \<noteq> error \<Longrightarrow> s \<noteq> ok \<Longrightarrow>
    R' s = (\<Sum>s'\<in>zc_states. zc_trans s s' * (zc_cost s s' + R' s'))"
    using R' by simp

  have "R ok = 0" "R error = 0"
    unfolding R_def by (simp_all add: reward_until_nat_case_0)
  with R' have R'_ok: "R' ok = 0" and R'_error: "R' error = 0"
    by simp_all

  then have R'_start: "R' start = q * (r + R' (probe 0)) + (1 - q) * (r * (last_probe + 1))"
    by (subst R'_sum)
       (simp_all add: setsum_zc_states field_simps setsum_addf if_mult setsum_cases)

  have R'_last_probe: "R' (probe last_probe) = E"
    using R'_error by (subst R'_sum) (simp_all add: setsum_zc_states field_simps)

  have R'_probe: "\<And>n. n < last_probe \<Longrightarrow> R' (probe n) = p * R' (probe (Suc n)) + p * r + (1 - p) * R' start"
    using R'_error
    by (subst R'_sum)
       (simp_all add: setsum_zc_states setsum_addf field_simps if_mult setsum_cases)

  { fix n
    assume "n \<le> last_probe"
    then have "R' (probe (last_probe - n)) =
      p ^ n * E + (1 - p^n) * r * p / (1 - p) + (1 - p^n) * R' start"
    proof (induct n)
      case 0 with R'_last_probe show ?case by simp
    next
      case (Suc n)
      moreover then have "Suc (last_probe - Suc n) = last_probe - n" by simp
      ultimately show ?case
        using R'_probe[of "last_probe - Suc n"] p
        by simp (simp add: field_simps)
    qed }
  from this[of last_probe]
  have "R' (probe 0) = p ^ last_probe * E + (1 - p^last_probe) * r * p / (1 - p) + (1 - p^last_probe) * R' start"
    by simp
  then have "R' start - q * (1 - p^last_probe) * R' start =
    q * (r + p ^ last_probe * E + (1 - p^last_probe) * r * p / (1 - p)) + (1 - q) * (r * (last_probe + 1))"
    by (subst R'_start) (simp, simp add: field_simps)
  then have "R' start = (q * (r + p ^ last_probe * E + (1 - p^last_probe) * r * p / (1 - p)) + (1 - q) * (r * (last_probe + 1))) /
    (1 - q * (1 - p^last_probe))"
    using pos_neg_q_pn
    by (simp add: field_simps)
  then show ?thesis
    using R' p q by (simp add: field_simps)
qed

end

end