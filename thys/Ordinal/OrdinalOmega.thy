(*  Title:       Countable Ordinals

    Author:      Brian Huffman, 2005
    Maintainer:  Brian Huffman <brianh at cse.ogi.edu>
*)

section \<open>Omega\<close>

theory OrdinalOmega
imports OrdinalFix
begin

subsection \<open>Embedding naturals in the ordinals\<close>

primrec ordinal_of_nat :: "nat \<Rightarrow> ordinal"
where
  "ordinal_of_nat 0 = 0"
| "ordinal_of_nat (Suc n) = oSuc (ordinal_of_nat n)"

lemma strict_mono_ordinal_of_nat: "strict_mono ordinal_of_nat"
  by (simp add: strict_mono_natI)

lemma not_limit_ordinal_nat: "\<not> limit_ordinal (ordinal_of_nat n)"
  by (induct n) simp_all

lemma ordinal_of_nat_eq [simp]:
  "(ordinal_of_nat x = ordinal_of_nat y) = (x = y)"
  by (rule strict_mono_cancel_eq[OF strict_mono_ordinal_of_nat])

lemma ordinal_of_nat_less [simp]:
  "(ordinal_of_nat x < ordinal_of_nat y) = (x < y)"
  by (rule strict_mono_cancel_less[OF strict_mono_ordinal_of_nat])

lemma ordinal_of_nat_le [simp]:
  "(ordinal_of_nat x \<le> ordinal_of_nat y) = (x \<le> y)"
  by (rule strict_mono_cancel_le[OF strict_mono_ordinal_of_nat])

lemma ordinal_of_nat_plus [simp]:
  "ordinal_of_nat x + ordinal_of_nat y = ordinal_of_nat (x + y)"
  by (induct y) simp_all

lemma ordinal_of_nat_times [simp]:
  "ordinal_of_nat x * ordinal_of_nat y = ordinal_of_nat (x * y)"
  by (induct y) (simp_all add: add.commute)

lemma ordinal_of_nat_exp [simp]:
  "ordinal_of_nat x ** ordinal_of_nat y = ordinal_of_nat (x ^ y)"
  by (induct y, cases x) (simp_all add: mult.commute)

lemma oSuc_plus_ordinal_of_nat:
  "oSuc x + ordinal_of_nat n = oSuc (x + ordinal_of_nat n)"
  by (induct n) simp_all

lemma less_ordinal_of_nat:
  "(x < ordinal_of_nat n) = (\<exists>m. x = ordinal_of_nat m \<and> m < n)"
  by (induction n) (use less_oSuc_eq_le in force)+

lemma le_ordinal_of_nat:
  "(x \<le> ordinal_of_nat n) = (\<exists>m. x = ordinal_of_nat m \<and> m \<le> n)"
  by (auto simp add: order_le_less less_ordinal_of_nat)


subsection \<open>Omega, the least limit ordinal\<close>

definition
  omega :: "ordinal"  ("\<omega>") where
  "omega = oLimit ordinal_of_nat"

lemma less_omegaD: "x < \<omega> \<Longrightarrow> \<exists>n. x = ordinal_of_nat n"
  by (metis less_oLimitD less_ordinal_of_nat omega_def)

lemma omega_leI: "\<forall>n. ordinal_of_nat n \<le> x \<Longrightarrow> \<omega> \<le> x"
  by (simp add: oLimit_leI omega_def)

lemma nat_le_omega [simp]: "ordinal_of_nat n \<le> \<omega>"
  by (simp add: oLimit_leI omega_def)

lemma nat_less_omega [simp]: "ordinal_of_nat n < \<omega>"
  by (simp add: omega_def strict_mono_less_oLimit strict_mono_ordinal_of_nat)

lemma zero_less_omega [simp]: "0 < \<omega>"
  using nat_less_omega ordinal_neq_0 by fastforce

lemma limit_ordinal_omega: "limit_ordinal \<omega>"
  by (metis limit_ordinal_oLimitI nat_less_omega omega_def)

lemma Least_limit_ordinal: "(LEAST x. limit_ordinal x) = \<omega>"
proof (rule Least_equality)
  show "\<And>y. limit_ordinal y \<Longrightarrow> \<omega> \<le> y"
    by (metis leI less_omegaD not_limit_ordinal_nat)
qed (rule limit_ordinal_omega)

lemma "range f = range ordinal_of_nat \<Longrightarrow> oLimit f = \<omega>"
  by (metis le_oLimit oLimit_leI omega_def order_antisym rangeE rangeI)


subsection \<open>Arithmetic properties of @{term \<omega>}\<close>

lemma oSuc_less_omega [simp]: "(oSuc x < \<omega>) = (x < \<omega>)"
  by (rule oSuc_less_limit_ordinal[OF limit_ordinal_omega])

lemma oSuc_plus_omega [simp]: "oSuc x + \<omega> = x + \<omega>"
proof -
  have "\<And>n. \<exists>m. oSuc x + ordinal_of_nat n \<le> x + ordinal_of_nat m"
    using oSuc_le_eq_less oSuc_plus_ordinal_of_nat by auto
  moreover
  have "\<And>n. \<exists>m. x + ordinal_of_nat n \<le> oSuc x + ordinal_of_nat m"
    using dual_order.order_iff_strict oSuc_plus_ordinal_of_nat by auto
  ultimately show ?thesis
    by (simp add: oLimit_eqI omega_def)
qed

lemma ordinal_of_nat_plus_omega [simp]:
  "ordinal_of_nat n + \<omega> = \<omega>"
  by (induct n) simp_all

lemma ordinal_of_nat_times_omega [simp]:
  assumes "k > 0" shows "ordinal_of_nat k * \<omega> = \<omega>"
proof -
  have "\<exists>m. ordinal_of_nat n \<le> ordinal_of_nat (k * m)"
    by (metis assms le_add1 mult_eq_if not_less_zero ordinal_of_nat_le)
  then have "oLimit (\<lambda>n. ordinal_of_nat (k * n)) = oLimit ordinal_of_nat"
    by (metis assms oLimit_eqI gr0_conv_Suc le_add1 mult_Suc ordinal_of_nat_le)
  then show ?thesis
    by (simp add: omega_def)
qed

lemma ordinal_plus_times_omega: "x + x * \<omega> = x * \<omega>"
  by (metis oSuc_plus_omega ordinal_0_plus ordinal_times_1 ordinal_times_distrib)

lemma ordinal_plus_absorb: "x * \<omega> \<le> y \<Longrightarrow> x + y = y"
  by (metis ordinal_plus_assoc ordinal_plus_minus2 ordinal_plus_times_omega)

lemma ordinal_less_plusL: 
  assumes "y < x * \<omega>" shows "y < x + y"
proof (cases "x = 0")
  case True
  with assms show ?thesis by auto
next
  case False
  then obtain n where n: "ordinal_of_nat n = y div x"
    using assms less_omegaD ordinal_div_less by metis
  then have "y < x * (1 + ordinal_of_nat n)"
    using n unfolding ordinal_one_def oSuc_plus_ordinal_of_nat
    by (metis False ordinal_0_plus ordinal_less_times_div_plus ordinal_neq_0 ordinal_times_oSuc)
  also have "... \<le> x + y"
    using n by (simp add: ordinal_times_distrib ordinal_times_div_le)
  finally show ?thesis .
qed

lemma ordinal_plus_absorb_iff: "(x + y = y) = (x * \<omega> \<le> y)"
  by (metis linorder_linear order_le_less order_less_irrefl ordinal_less_plusL ordinal_plus_absorb)

lemma ordinal_less_plusL_iff: "(y < x + y) = (y < x * \<omega>)"
  by (metis leI linorder_neq_iff ordinal_less_plusL ordinal_plus_absorb)


subsection \<open>Additive principal ordinals\<close>

locale additive_principal =
  fixes a :: ordinal
  assumes not_0:  "0 < a"
  assumes sum_eq: "\<And>b. b < a \<Longrightarrow> b + a = a"

lemma (in additive_principal) sum_less:
  "\<lbrakk>x < a; y < a\<rbrakk> \<Longrightarrow> x + y < a"
  by (metis ordinal_plus_strict_monoR sum_eq)

lemma (in additive_principal) times_nat_less:
  "x < a \<Longrightarrow> x * ordinal_of_nat n < a"
  by (induct n) (auto simp: not_0 sum_less)

lemma not_additive_principal_0: "\<not> additive_principal 0"
  by (simp add: additive_principal_def)

lemma additive_principal_oSuc:
  "additive_principal (oSuc a) = (a = 0)"
  unfolding additive_principal_def
  by (metis less_oSuc0 ordinal_plus_0 ordinal_plus_left_cancel_less ordinal_plus_oSuc)

lemma additive_principal_intro2 [rule_format]:
  assumes not_0: "0 < a" and lessa: "(\<forall>x<a. \<forall>y<a. x + y < a)"
  shows "additive_principal a"
proof -
  have "\<forall>b<a. b + a = a"
    using lessa
  proof (induction a rule: oLimit_induct)
    case zero
    then show ?case by auto
  next
    case (suc x)
    then show ?case
      by (metis le_oSucE less_oSuc linorder_not_le ordinal_le_plusL ordinal_plus_oSuc)
  next
    case (lim f)
    then show ?case 
      by (metis leD order_le_less ordinal_le_plusL ordinal_plus_minus2)
  qed
  then show ?thesis
    by (simp add: additive_principal_def not_0)
qed

lemma additive_principal_1: "additive_principal (oSuc 0)"
  by (simp add: additive_principal_def)

lemma additive_principal_omega: "additive_principal \<omega>"
  using additive_principal.intro less_omegaD ordinal_of_nat_plus_omega zero_less_omega by blast

lemma additive_principal_times_omega:
  assumes "0 < x" shows "additive_principal (x * \<omega>)"
proof (rule additive_principal.intro)
  fix b
  assume "b < x * \<omega>"
  then obtain k where k: "b < x * ordinal_of_nat k"
    by (metis less_oLimitD omega_def ordinal_times_oLimit)
  then have "b + x * ordinal_of_nat n \<le> x * ordinal_of_nat (k + n)" for n
    by (metis order_less_imp_le ordinal_of_nat_plus ordinal_plus_monoL ordinal_times_distrib)
  then show "b + x * \<omega> = x * \<omega>"
    by (metis oLimit_eqI omega_def ordinal_le_plusL ordinal_plus_oLimit ordinal_times_oLimit)
qed (use assms in auto)

lemma additive_principal_oLimit:
  assumes "\<forall>n. additive_principal (f n)" 
  shows "additive_principal (oLimit f)"
proof (rule additive_principal.intro)
  show "0 < oLimit f"
    by (metis assms less_oLimitI not_additive_principal_0 ordinal_neq_0)
next
  fix b
  assume "b < oLimit f"
  then obtain k where "b < f k"
    using less_oLimitD by auto
  then have "\<exists>m. b + f n \<le> f m" for n
    by (metis additive_principal.sum_eq assms order.trans leI order_less_imp_le ordinal_plus_left_cancel_le)
  then show "b + oLimit f = oLimit f"
    by (metis \<open>b < f k\<close> additive_principal_def assms le_oLimit ordinal_plus_assoc ordinal_plus_minus2)
qed

lemma additive_principal_omega_exp: "additive_principal (\<omega> ** x)"
  by (induction x rule: oLimit_induct)
     (auto simp: additive_principal_1 additive_principal_times_omega additive_principal_oLimit)

lemma (in additive_principal) omega_exp: "\<exists>x. a = \<omega> ** x"
proof -
  have "\<exists>x. \<omega> ** x \<le> a \<and> a < \<omega> ** (oSuc x)"
    by (metis not_0 oSuc_less_omega ordinal_exp_oLog_le ordinal_exp_oSuc ordinal_less_exp_oLog zero_less_omega)
  then show ?thesis
    by (metis leD order_le_imp_less_or_eq ordinal_exp_oSuc ordinal_plus_absorb_iff sum_eq)
qed

lemma additive_principal_iff:
  "additive_principal a = (\<exists>x. a = \<omega> ** x)"
  using additive_principal.omega_exp additive_principal_omega_exp by blast

lemma absorb_omega_exp:
  "x < \<omega> ** a \<Longrightarrow> x + \<omega> ** a = \<omega> ** a"
  by (rule additive_principal.sum_eq[OF additive_principal_omega_exp])

lemma absorb_omega_exp2: "a < b \<Longrightarrow> \<omega> ** a + \<omega> ** b = \<omega> ** b"
  by (rule absorb_omega_exp, simp add: ordinal_exp_strict_monoR)


subsection \<open>Cantor normal form\<close>

lemma cnf_lemma: "x > 0 \<Longrightarrow> x - \<omega> ** oLog \<omega> x < x"
  by (simp add: ordinal_exp_oLog_le ordinal_less_exp_oLog ordinal_less_plusL)

primrec from_cnf where
  "from_cnf []       = 0"
| "from_cnf (x # xs) = \<omega> ** x + from_cnf xs"

function to_cnf where
  [simp del]: "to_cnf x = (if x = 0 then [] else
    oLog \<omega> x # to_cnf (x - \<omega> ** oLog \<omega> x))"
  by pat_completeness auto

termination by (relation "{(x, y). x < y}")
    (simp_all add: wf cnf_lemma)

lemma to_cnf_0 [simp]: "to_cnf 0 = []"
  by (simp add: to_cnf.simps)

lemma to_cnf_not_0:
  "0 < x \<Longrightarrow> to_cnf x = oLog \<omega> x # to_cnf (x - \<omega> ** oLog \<omega> x)"
  by (simp add: to_cnf.simps[of x])

lemma to_cnf_eq_Cons: "to_cnf x = a # list \<Longrightarrow> a = oLog \<omega> x"
  by (case_tac "x = 0", simp, simp add: to_cnf_not_0)

lemma to_cnf_inverse: "from_cnf (to_cnf x) = x"
  using wf
proof (induction rule: wf_induct_rule)
  case (less x)
  then have IH: "\<forall>y<x. from_cnf (to_cnf y) = y"
    by simp
  show ?case
  proof (cases "x = 0")
    case False
    with cnf_lemma show ?thesis
      by (simp add: ordinal_exp_oLog_le to_cnf_not_0 IH)
  qed auto
qed

primrec normalize_cnf where
  normalize_cnf_Nil: "normalize_cnf [] = []"
| normalize_cnf_Cons: "normalize_cnf (x # xs) =
      (case xs of [] \<Rightarrow> [x] | y # ys \<Rightarrow>
        (if x < y then [] else [x]) @ normalize_cnf xs)"

lemma from_cnf_normalize_cnf: "from_cnf (normalize_cnf xs) = from_cnf xs"
proof (induction xs)
  case Nil
  then show ?case by auto
next
  case (Cons a xs)
  have "\<And>x y. a < x \<Longrightarrow> \<omega> ** x + from_cnf y = \<omega> ** a + (\<omega> ** x + from_cnf y)"
    by (metis absorb_omega_exp2 from_cnf.simps(2) ordinal_plus_assoc)
  with Cons show ?case
    by simp (auto simp del: normalize_cnf_Cons split: list.split)
qed


lemma normalize_cnf_to_cnf: "normalize_cnf (to_cnf x) = to_cnf x"
  using wf
proof (induction rule: wf_induct_rule)
  case (less x)
  then have IH: "\<forall>y<x. normalize_cnf (to_cnf y) = to_cnf y"
    by simp
  show ?case
  proof (cases "x = 0")
    case False
    then have \<section>: "normalize_cnf (to_cnf (x - \<omega> ** oLog \<omega> x)) = to_cnf (x - \<omega> ** oLog \<omega> x)"
      using IH cnf_lemma by blast
    with False show ?thesis
      apply (simp add: to_cnf_not_0)
      apply (case_tac "to_cnf (x - \<omega> ** oLog \<omega> x)", simp_all)
      by (metis cnf_lemma linorder_not_le order_le_less ordinal_oLog_monoR to_cnf_eq_Cons)
  qed auto
qed


text "alternate form of CNF"

lemma cnf2_lemma:
  "0 < x \<Longrightarrow> x mod \<omega> ** oLog \<omega> x < x"
  by (meson oSuc_less_omega order_less_le_trans ordinal_exp_not_0 ordinal_exp_oLog_le ordinal_mod_less zero_less_omega)


primrec from_cnf2 where
  "from_cnf2 []       = 0"
| "from_cnf2 (x # xs) = \<omega> ** fst x * ordinal_of_nat (snd x) + from_cnf2 xs"

function to_cnf2 where
  [simp del]: "to_cnf2 x = (if x = 0 then [] else
    (oLog \<omega> x, inv ordinal_of_nat (x div (\<omega> ** oLog \<omega> x)))
      # to_cnf2 (x mod (\<omega> ** oLog \<omega> x)))"
  by pat_completeness auto

termination by (relation "{(x,y). x < y}")
    (simp_all add: wf cnf2_lemma)

lemma to_cnf2_0 [simp]: "to_cnf2 0 = []"
  by (simp add: to_cnf2.simps)

lemma to_cnf2_not_0:
  "0 < x \<Longrightarrow> to_cnf2 x = (oLog \<omega> x, inv ordinal_of_nat (x div (\<omega> ** oLog \<omega> x)))
                       # to_cnf2 (x mod (\<omega> ** oLog \<omega> x))"
  by (simp add: to_cnf2.simps[of x])

lemma to_cnf2_eq_Cons: "to_cnf2 x = (a,b) # list \<Longrightarrow> a = oLog \<omega> x"
  by (metis Pair_inject list.discI list.inject to_cnf2.elims)

lemma ordinal_of_nat_of_ordinal:
  "x < \<omega> \<Longrightarrow> ordinal_of_nat (inv ordinal_of_nat x) = x"
  by (simp add: f_inv_into_f image_def less_omegaD)

lemma to_cnf2_inverse: "from_cnf2 (to_cnf2 x) = x"
  using wf
proof (induction x rule: wf_induct_rule)
  case (less x)
  show ?case
  proof (cases "x > 0")
    case True
    then show ?thesis
      by (simp add: cnf2_lemma less ordinal_div_exp_oLog_less ordinal_div_plus_mod ordinal_of_nat_of_ordinal to_cnf2_not_0)
  qed auto
qed

primrec is_normalized2 where
  is_normalized2_Nil: "is_normalized2 [] = True"
| is_normalized2_Cons: "is_normalized2 (x # xs) =
      (case xs of [] \<Rightarrow> True | y # ys \<Rightarrow> fst y < fst x \<and> is_normalized2 xs)"

lemma is_normalized2_to_cnf2: "is_normalized2 (to_cnf2 x)"
  using wf
proof (induction x rule: wf_induct_rule)
  case (less x)
  show ?case
  proof (cases "x > 0")
    case True
    then have *: "is_normalized2 (to_cnf2 (x mod \<omega> ** oLog \<omega> x))"
      using cnf2_lemma less by blast
    show ?thesis
    proof (cases "x mod \<omega> ** oLog \<omega> x = 0")
      case True
      with to_cnf2_not_0 \<open>x > 0\<close> show ?thesis by simp
    next
      case False
      with \<open>x > 0\<close> * show ?thesis
        by (simp add: ordinal_mod_less ordinal_oLog_less to_cnf2_not_0)
    qed   
  qed auto
qed


subsection \<open>Epsilon 0\<close>

definition epsilon0 :: ordinal  ("\<epsilon>\<^sub>0") where
  "epsilon0 = oFix ((**) \<omega>) 0"

lemma less_omega_exp: "x < \<epsilon>\<^sub>0 \<Longrightarrow> x < \<omega> ** x"
  by (simp add: epsilon0_def less_oFix_0D normal.mono normal_exp)

lemma omega_exp_epsilon0: "\<omega> ** \<epsilon>\<^sub>0 = \<epsilon>\<^sub>0"
  by (simp add: continuous_exp epsilon0_def oFix_fixed)

lemma oLog_omega_less: "\<lbrakk>0 < x; x < \<epsilon>\<^sub>0\<rbrakk> \<Longrightarrow> oLog \<omega> x < x"
  by (simp add: less_omega_exp ordinal_oLog_less)

end

