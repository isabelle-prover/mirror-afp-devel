section \<open>Dice Roll\label{sec:dice_roll}\<close>

theory Dice_Roll
  imports Tracking_SPMF
begin

text \<open>The following is a dice roll algorithm for an arbitrary number of sides @{term "n"}.
Besides correctness we also show that the expected number of coin flips is at most
@{term "log 2 n + 2"}. It is a specialization of the algorithm presented by Hao and
Hoshi~\cite{hao1997}. \footnote{An interesting alternative algorithm, which we did not formalized
here, has been introduced by Lambruso~\cite{lambruso2013}.}\<close>

lemma floor_le_ceil_minus_one:
  fixes x y :: real
  shows "x < y \<Longrightarrow> \<lfloor>x\<rfloor> \<le> \<lceil>y\<rceil>-1"
  by linarith

lemma combine_spmf_set_coin_spmf:
  fixes f :: "nat \<Rightarrow> 'a spmf"
  fixes k :: nat
  shows "pmf_of_set {..<2^k} \<bind> (\<lambda>l. coin_spmf \<bind>(\<lambda>b. f (2*l+ of_bool b))) =
    pmf_of_set {..<2^(k+1)} \<bind> f" (is "?L = ?R")
proof -
  let ?f = "(\<lambda>(l::nat,b). 2*l+ of_bool b)"
  let ?coin = "pmf_of_set (UNIV :: bool set)"

  have [simp]:"{..<(2::nat) ^ k} \<noteq> {}"
    by (simp add: lessThan_empty_iff)

  have bij:"bij_betw ?f ({..<2^k} \<times> UNIV) {..<2^(k+1)}"
    by (intro bij_betwI[where g="(\<lambda>x. (x div 2, odd x))"]) auto

  have "pmf (pair_pmf (pmf_of_set {..<2^k}) ?coin) x =
    pmf (pmf_of_set ({..<2^k}\<times>UNIV)) x" for x :: "nat\<times> bool"
    by (cases x) (simp add:pmf_pair indicator_def)
  hence 0:"pair_pmf (pmf_of_set {..<(2::nat)^k}) ?coin = pmf_of_set ({..<2^k}\<times>UNIV)"
    by (intro pmf_eqI) simp

  have "map_pmf ?f (pmf_of_set ({..<2^k}\<times>UNIV)) = pmf_of_set (?f ` ({..<2^k}\<times>UNIV))"
    using bij_betw_imp_inj_on[OF bij] by (intro map_pmf_of_set_inj) auto
  also have "... = pmf_of_set {..<2^(k+1)}"
    by (intro arg_cong[where f="pmf_of_set"] bij_betw_imp_surj_on[OF bij])
  finally have 1:"map_pmf ?f (pmf_of_set ({..<2^k}\<times>UNIV)) = pmf_of_set {..<2^(k+1)}"
    by simp

  have "?L = pmf_of_set {..<2^k} \<bind> (\<lambda>l. ?coin \<bind> (\<lambda>b. f (2*l + of_bool b)))"
    unfolding spmf_of_set_def bind_spmf_def spmf_of_pmf_def by (simp add:bind_map_pmf)
  also have "... = pair_pmf (pmf_of_set {..<2^k}) ?coin  \<bind> (\<lambda>(l,b). f (2*l + of_bool b))"
    unfolding pair_pmf_def by (simp add:bind_assoc_pmf bind_return_pmf)
  also have "... = map_pmf (\<lambda>(l,b). 2 * l + of_bool b) (pmf_of_set ({..<2^k}\<times>UNIV)) \<bind> f"
    unfolding 0 bind_map_pmf by (simp add:comp_def case_prod_beta')
  also have "... = ?R"
    unfolding 1 by simp
  finally show ?thesis by simp
qed

lemma count_ints_in_range:
  "real (card {x. of_int x \<in> {u..v}} ) \<ge> v-u-1" (is "?L \<ge> ?R")
proof (cases "u \<le> v")
  case True
  have 0:"of_int x \<in> {u..v} \<longleftrightarrow> x \<in> {\<lceil>u\<rceil>..\<lfloor>v\<rfloor>}" for x by simp linarith

  have "v - u - 1 \<le> \<lfloor>v\<rfloor> - \<lceil>u\<rceil> + 1" using True by linarith
  also have "... = real (nat (\<lfloor>v\<rfloor> - \<lceil>u\<rceil> + 1))" using True by (intro of_nat_nat[symmetric]) linarith
  also have "... = card {\<lceil>u\<rceil>..\<lfloor>v\<rfloor>}" by simp
  also have "... = ?L"
    unfolding 0 by (intro arg_cong[where f="real"] arg_cong[where f="card"]) auto
  finally show ?thesis by simp
next
  case False
  hence "v-u-1 \<le> 0" by simp
  thus ?thesis by simp
qed

partial_function (random_alg) dice_roll_step_ra :: "real \<Rightarrow> real \<Rightarrow> int random_alg"
  where "dice_roll_step_ra l h = (
    if \<lfloor>l\<rfloor> = \<lceil>l+h\<rceil>-1 then
      return_ra \<lfloor>l\<rfloor>
    else
      do { b \<leftarrow> coin_ra; dice_roll_step_ra (l + (h/2) * of_bool b) (h/2) }
    )"

definition "dice_roll_ra n = map_ra nat (dice_roll_step_ra 0 (of_nat n))"

partial_function (spmf) drs_tspmf :: "real \<Rightarrow> real \<Rightarrow> int tspmf"
  where "drs_tspmf l h = (
    if \<lfloor>l\<rfloor> = \<lceil>l+h\<rceil>-1 then
      return_tspmf \<lfloor>l\<rfloor>
    else
      do { b \<leftarrow> coin_tspmf; drs_tspmf (l + (h/2) * of_bool b) (h/2) }
    )"

definition "dice_roll_tspmf n = drs_tspmf 0 (of_nat n) \<bind> (\<lambda>x. return_tspmf (nat x))"

lemma drs_tspmf: "drs_tspmf l u = tspmf_of_ra (dice_roll_step_ra l u)"
proof -
  include lifting_syntax
  have "((=) ===> (=) ===> rel_tspmf_of_ra) drs_tspmf dice_roll_step_ra"
    unfolding drs_tspmf_def dice_roll_step_ra_def
    apply (rule rel_funD[OF curry_transfer])
    apply (rule fixp_rel_tspmf_of_ra_parametric[OF drs_tspmf.mono dice_roll_step_ra.mono])
    by transfer_prover
  thus ?thesis
    unfolding rel_fun_def rel_tspmf_of_ra_def by auto
qed

lemma dice_roll_ra_tspmf: "tspmf_of_ra (dice_roll_ra n) = dice_roll_tspmf n"
  unfolding dice_roll_ra_def dice_roll_tspmf_def map_ra_def tspmf_of_ra_bind tspmf_of_ra_return
    drs_tspmf by simp

lemma dice_roll_step_tspmf_lb:
  assumes "h > 0"
  shows "coin_tspmf \<bind> (\<lambda>b. drs_tspmf (l + (h/2) * of_bool b) (h/2)) \<le>\<^sub>R drs_tspmf l h"
proof (cases "\<lfloor>l\<rfloor> = \<lceil>l+h\<rceil>-1")
  case True
  hence 2:"drs_tspmf l h = return_tspmf \<lfloor>l\<rfloor>"
    by (subst drs_tspmf.simps) simp

  have 0: "\<lfloor>l + h / 2 * of_bool b\<rfloor> = \<lfloor>l\<rfloor>" for b
  proof -
    have "\<lfloor>l + h / 2 * of_bool b\<rfloor> \<le> \<lfloor>l + h / 2\<rfloor>"
      using assms by (intro floor_mono add_mono) auto
    also have "... \<le> \<lceil>l + h\<rceil> - 1"
      using assms by (intro floor_le_ceil_minus_one add_strict_left_mono) auto
    also have "... = \<lfloor>l\<rfloor>" using True by simp
    finally have "\<lfloor>l + h / 2 * of_bool b\<rfloor> \<le> \<lfloor>l\<rfloor>" by simp
    moreover have "\<lfloor>l\<rfloor> \<le> \<lfloor>l + h / 2 * of_bool b\<rfloor>"
      using assms by (intro floor_mono) auto
    ultimately show ?thesis by simp
  qed

  have 1: "\<lceil>l + h / 2 * of_bool b + h / 2\<rceil> - 1 = \<lfloor>l\<rfloor>" for b
  proof -
    have "\<lceil>l + h / 2 * of_bool b + h / 2\<rceil> - 1 \<le> \<lceil>l + h\<rceil>-1"
      using assms by (intro diff_mono ceiling_mono) auto
    also have "... = \<lfloor>l\<rfloor>" using True by simp
    finally have "\<lceil>l + h / 2 * of_bool b + h / 2\<rceil> - 1 \<le> \<lfloor>l\<rfloor>" by simp
    moreover have "\<lfloor>l\<rfloor> \<le> \<lceil>l + h / 2 * of_bool b + h / 2\<rceil> - 1"
      using assms by (intro floor_le_ceil_minus_one) auto
    ultimately show ?thesis by simp
  qed

  have 3:"drs_tspmf (l + (h/2) * of_bool b) (h/2) = return_tspmf \<lfloor>l\<rfloor>" for b
    using 0 1 by (subst drs_tspmf.simps) simp

  show ?thesis
    unfolding 2 3 bind_tspmf_def coin_tspmf_def pair_spmf_alt_def
    by (simp add:bind_spmf_const ord_tspmf_map_spmf)
next
  case False
  thus ?thesis
    by (subst drs_tspmf.simps) (auto intro:ord_tspmf_refl)
qed

abbreviation "coins k \<equiv> pmf_of_set {..<(2::nat)^k}"

lemma dice_roll_step_tspmf_expand:
  assumes "h > 0"
  shows "coins k \<bind> (\<lambda>l. use_coins k (drs_tspmf (real l*h) h)) \<le>\<^sub>R drs_tspmf 0 (h*2^k)"
  using assms
proof (induction k arbitrary:h)
  case 0
  have "{..<Suc 0} = {0}" by auto
  then show ?case
    by (auto intro:ord_tspmf_use_coins simp:pmf_of_set_singleton bind_return_pmf)
next
  case (Suc k)
  have "(coins (k+1) \<bind> (\<lambda>l. use_coins (k+1) (drs_tspmf (real l*h) h))) =
    coins k \<bind> (\<lambda>l. coin_spmf \<bind> (\<lambda>b. use_coins (k+1) (drs_tspmf (real (2*l+ of_bool b) * h) h)))"
    by (intro combine_spmf_set_coin_spmf[symmetric])
  also have "... = coins k \<bind> (\<lambda>l. use_coins (k+1) (coin_spmf \<bind>
    (\<lambda>b. drs_tspmf (real l* (2*h) + h * of_bool b) h)))"
    unfolding use_coins_def map_spmf_conv_bind_spmf by (simp add:algebra_simps)
  also have "... = coins k \<bind> (\<lambda>l. use_coins k (coin_tspmf \<bind>
    (\<lambda>b. drs_tspmf (real l* (2*h) + h * of_bool b) h)))"
    unfolding coin_tspmf_split use_coins_add by simp
  also have "... = coins k \<bind> (\<lambda>l. use_coins k (coin_tspmf \<bind>
    (\<lambda>b. drs_tspmf (real l* (2*h) + ((2*h)/2) * of_bool b) ((2*h)/2))))"
    using Suc(2) by simp
  also have "... \<le>\<^sub>R coins k \<bind> (\<lambda>l. use_coins k (drs_tspmf (real l * (2 * h)) (2*h)))"
    using Suc(2) by (intro ord_tspmf_bind_pmf ord_tspmf_use_coins_2 dice_roll_step_tspmf_lb) simp
  also have "... \<le>\<^sub>R drs_tspmf 0 ((2*h)*2^k)"
    using Suc(2) by (intro Suc(1)) auto
  also have "... = drs_tspmf 0 (h*2^(k+1))"
    unfolding power_add by (simp add:algebra_simps)
  finally show ?case
    by simp
qed

lemma dice_roll_step_tspmf_approx:
  fixes k :: nat
  assumes "h > (0::real)"
  defines "f \<equiv> (\<lambda>l. if \<lfloor>l*h\<rfloor>=\<lceil>(l+1)*h\<rceil>-1 then Some (\<lfloor>l*h\<rfloor>,k) else None)"
  shows "map_pmf f (coins k) \<le>\<^sub>R drs_tspmf 0 (h*2^k)" (is "?L \<le>\<^sub>R ?R")
proof -
  have "?L = coins k \<bind>
    (\<lambda>l. use_coins k (if \<lfloor>real l*h\<rfloor>=\<lceil>(l+1)*h\<rceil>-1 then return_tspmf \<lfloor>l*h\<rfloor> else return_pmf None))"
    unfolding f_def return_tspmf_def use_coins_def map_pmf_def
    by (simp add:if_distribR if_distrib bind_return_pmf algebra_simps cong:if_cong)
  also have "... \<le>\<^sub>R coins k \<bind> (\<lambda>l. use_coins k (drs_tspmf (real l*h) h))"
    by (subst drs_tspmf.simps, intro ord_tspmf_bind_pmf ord_tspmf_use_coins_2)
      (simp add:ord_tspmf_min ord_tspmf_refl algebra_simps)
  also have "... \<le>\<^sub>R drs_tspmf 0 (h*2^k)"
    by (intro dice_roll_step_tspmf_expand assms)
  finally show ?thesis by simp
qed

lemma dice_roll_step_spmf_approx:
  fixes k :: nat
  assumes "h > (0::real)"
  defines "f \<equiv> (\<lambda>l. if \<lfloor>l*h\<rfloor>=\<lceil>(l+1)*h\<rceil>-1 then Some (\<lfloor>l*h\<rfloor>) else None)"
  shows "ord_spmf (=) (map_pmf f (coins k)) (result (drs_tspmf 0 (h*2^k)))"
    (is "ord_spmf _ ?L ?R")
proof -
  have 0: "?L = result (map_pmf (\<lambda>l. if \<lfloor>l*h\<rfloor>=\<lceil>(l+1)*h\<rceil>-1 then Some (\<lfloor>l*h\<rfloor>,k) else None) (coins k))"
    unfolding result_def map_pmf_comp f_def by (intro map_pmf_cong refl) auto

  show ?thesis
    unfolding 0 using assms result_mono[OF dice_roll_step_tspmf_approx] by simp
qed

lemma spmf_dice_roll_step_lb:
  assumes "j < n"
  shows "spmf (result (drs_tspmf 0 (of_nat n))) (of_nat j) \<ge> 1/n" (is "?L \<ge> ?R")
proof (rule ccontr)
  assume "\<not>(spmf (result (drs_tspmf 0 (of_nat n))) (of_nat j) \<ge> 1/n)"
  hence a:"?L < 1/n" by simp
  define k :: nat where "k = nat \<lfloor>2-log 2 (1/n-?L)\<rfloor>"
  define h where "h = real n/2^k"
  define f where "f l = (if \<lfloor>l*h\<rfloor>=\<lceil>(l+1)*h\<rceil>-1 then Some \<lfloor>l*h\<rfloor> else None)" for l :: nat

  have h_gt_0: "h > 0" using assms unfolding h_def by auto
  have n_gt_0: "real n > 0" using assms by simp

  have 0: "x < 2^k" if "real x \<le> (real j+1)*2^k/n-1" for x
  proof -
    have "real x \<le> (real j+1)*2^k/n-1" using that by simp
    also have "... \<le> real n * 2^k/n - 1"
      using assms by (intro diff_mono divide_right_mono mult_right_mono) auto
    also have "... \<le> 2^k-1" by simp
    finally have "real x \<le> 2^k-1" by simp
    thus ?thesis using nat_less_real_le by auto
  qed
  have 2: "int ` {x. P (real x)} = {x. P (real_of_int x)}" if "\<And>x. P x \<Longrightarrow> x \<ge> 0" for P
  proof -
    have "bij_betw int {x. P (real x)} {x. P (real_of_int x)}"
      using that by (intro bij_betwI[where g="nat"]) force+
    thus ?thesis
      using bij_betw_imp_surj_on by auto
  qed
  have 1: "real j*2^k/n \<ge> 0" by auto

  have 3:"\<lfloor>real l*h\<rfloor>\<le>\<lceil>real (l+1)*h\<rceil>-1" for l
    using h_gt_0 by (intro floor_le_ceil_minus_one) force

  have "2 = (1/n - ?L)*2 powr (1-log 2 (1/n-?L))"
    using a n_gt_0 unfolding powr_diff by (subst powr_log_cancel) (auto simp:divide_simps)
  also have "... < (1/n - ?L)*2 powr \<lfloor>2-log 2 (1/n-?L)\<rfloor>"
    using a by (intro mult_strict_left_mono powr_less_mono) linarith+
  also have "... \<le> (1/n - ?L)*2 powr real k"
    using a unfolding k_def by (intro mult_left_mono powr_mono) auto
  also have "... = (1/n - ?L)*2^k" by (subst powr_realpow) auto
  finally have "2 < (1/n - ?L)*2^k" by simp
  hence "?L < 1/n-2/2^k" by (simp add:field_simps)
  also have "... = (((real j+1)*2^k/n-1)-(real j*2^k/n)-1) / 2^k"
    using n_gt_0 by (simp add:field_simps)
  also have "... \<le> real (card {x. of_int x \<in> {real j*2^k/n..(real j+1)*2^k/n-1}})/2^k"
    by (intro divide_right_mono count_ints_in_range) auto
  also have "... = real (card (int ` {x. real x \<in> {real j*2^k/n..(real j+1)*2^k/n-1}}))/2^k"
    using order_trans[OF 1] by (subst 2) auto
  also have "... = real (card {x. real x \<in> {real j*2^k/n..(real j+1)*2^k/n-1}})/2^k"
    by (subst card_image) auto
  also have "... = real (card {x. x<2^k \<and> real x \<in> {real j*2^k/n..(real j+1)*2^k/n-1}})/2^k"
    using 0 by (intro arg_cong[where f="\<lambda>x. real (card x)/2^k"]) auto
  also have "... = real (card {l. l< 2^k \<and> real j \<le> real l * h \<and> (1 + real l)*h\<le>real j+1}) / 2^k"
    using assms unfolding h_def
    by (intro arg_cong[where f="\<lambda>x. real (card x)/2^k"] Collect_cong) (auto simp:field_simps)
  also have "... = measure (coins k) {l. real j \<le> real l*h \<and> real (l+1)*h \<le> real j + 1 }"
    by (subst measure_pmf_of_set) (simp_all add:lessThan_empty_iff Int_def)
  also have "... = measure (coins k) {l. int j \<le> \<lfloor>real l*h\<rfloor> \<and> \<lceil>real (l+1)*h\<rceil> - 1 \<le> int j }"
    by (intro arg_cong2[where f="measure"] refl Collect_cong) linarith
  also have "... = measure (coins k) {l. int j = \<lfloor>real l*h\<rfloor> \<and> int j = \<lceil>real (l+1)*h\<rceil> - 1}"
    using 3 order.trans order_antisym
    by (intro arg_cong2[where f="measure"] refl Collect_cong iffI, blast, simp)
  also have "... = spmf (map_pmf f (coins k)) j"
    unfolding pmf_map f_def vimage_def
    by (intro arg_cong2[where f="measure"] refl Collect_cong) auto
  also have "... \<le> spmf (result (drs_tspmf 0 (h*2^k))) j"
    unfolding f_def by (intro ord_spmf_eq_leD dice_roll_step_spmf_approx h_gt_0)
  also have "... = ?L"
    unfolding h_def by simp
  finally have "?L < ?L" by simp
  thus "False" by simp
qed

lemma dice_roll_correct_aux:
  assumes "n > 0"
  shows "result (drs_tspmf 0 (of_nat n)) = spmf_of_set {0..<n}"
proof -
  have "weight_spmf (spmf_of_set {0..<int n}) \<ge> weight_spmf (result (drs_tspmf 0 (of_nat n)))"
    using assms unfolding weight_spmf_of_set
    by (simp add:lessThan_empty_iff weight_spmf_le_1)
  moreover have "spmf (spmf_of_set {0..<int n}) x \<le> spmf (result (drs_tspmf 0 (of_nat n))) x" for x
  proof (cases "x < n \<and> x \<ge> 0")
    case True
    hence "spmf (spmf_of_set {0..<int n}) x = 1/n"
      unfolding spmf_of_set by auto
    also have "... \<le> spmf (result (drs_tspmf 0 (of_nat n))) (of_nat (nat x))"
      using True by (intro spmf_dice_roll_step_lb) auto
    also have "... = spmf (result (drs_tspmf 0 (of_nat n))) x"
      using True by (subst of_nat_nat) auto
    finally show ?thesis by simp
  next
    case False
    hence "spmf (spmf_of_set {0..<int n}) x = 0"
      unfolding spmf_of_set by auto
    then show ?thesis by simp
  qed
  hence "ord_spmf (=) (spmf_of_set {0..<int n}) (result (drs_tspmf 0 (of_nat n)))"
    by (intro ord_pmf_increaseI refl) auto
  ultimately show ?thesis
    by (intro eq_iff_ord_spmf[symmetric]) auto
qed

theorem dice_roll_correct:
  assumes "n > 0"
  shows
    "result (dice_roll_tspmf n) = spmf_of_set {..<n}" (is "?L = ?R")
    "spmf_of_ra (dice_roll_ra n) = spmf_of_set {..<n}"
proof -
  have bij:"bij_betw nat {0..<int n} {..<n}"
    by (intro bij_betwI[where g="int"]) auto

  have "?L = map_spmf nat (spmf_of_set {0..<int n})"
    unfolding dice_roll_tspmf_def dice_roll_correct_aux[OF assms] result_bind result_return
      map_spmf_conv_bind_spmf by simp
  also have "... = spmf_of_set (nat ` {0..<int n})"
    by (intro map_spmf_of_set_inj_on inj_onI) auto
  also have "... = ?R"
    using bij_betw_imp_surj_on[OF bij] by (intro arg_cong[where f="spmf_of_set"]) auto
  finally show "?L = ?R" by simp
  thus "spmf_of_ra (dice_roll_ra n) = ?R"
    using spmf_of_tspmf dice_roll_ra_tspmf by metis
qed

lemma dice_roll_consumption_bound:
  assumes "n > 0"
  shows "measure (coin_usage_of_tspmf (dice_roll_tspmf n)) {x. x > enat k } \<le> real n/2^k"
    (is "?L \<le> ?R")
proof -
  define h where "h = real n/2^k"
  define f where "f l = (if \<lfloor>l*h\<rfloor>=\<lceil>(l+1)*h\<rceil>-1 then Some (\<lfloor>l*h\<rfloor>,k) else None)" for l :: nat

  have h_gt_0: " h > 0"
    using assms unfolding h_def
    by (intro divide_pos_pos) auto
  have 0:"real n = h * 2^k"
    unfolding h_def by simp

  have 1:"\<lfloor>real l*h\<rfloor><\<lfloor>(real l+1)*h\<rfloor>" if "\<lfloor>real l*h\<rfloor>\<noteq>\<lceil>(real l+1)*h\<rceil>-1" for l
  proof -
    have "\<lfloor>real l*h\<rfloor>\<le>\<lceil>(real l+1)*h\<rceil>-1"
      using h_gt_0 by (intro floor_le_ceil_minus_one) force
    hence "\<lfloor>real l*h\<rfloor><\<lceil>(real l+1)*h\<rceil>-1"
      using that by simp
    also have "... \<le> \<lfloor>(real l+1)*h\<rfloor>"
      by linarith
    finally show ?thesis by simp
  qed

  have "?L = measure (coin_usage_of_tspmf (drs_tspmf 0 n)) {x. x > enat k}"
    unfolding dice_roll_tspmf_def coin_usage_of_tspmf_bind_return by simp
  also have "... \<le> measure (coin_usage_of_tspmf (map_pmf f (coins k))) {x. x > enat k}"
    unfolding f_def 0
    by (intro coin_usage_of_tspmf_mono_rev dice_roll_step_tspmf_approx h_gt_0)
  also have "... = measure (coins k) {l. \<lfloor>real l*h\<rfloor>\<noteq>\<lceil>(real l+1)*h\<rceil>-1}"
    unfolding coin_usage_of_tspmf_def map_pmf_comp
    by (simp add:vimage_def f_def algebra_simps split:option.split)
  also have "... \<le> measure (coins k) {l. \<lfloor>real l*h\<rfloor><\<lfloor>(real l+1)*h\<rfloor>}"
    using 1 by (intro measure_pmf.finite_measure_mono subsetI) (simp_all)
  also have "... = (\<integral>l. indicator {l. \<lfloor>real l*h\<rfloor><\<lfloor>(real l+1)*h\<rfloor>} l \<partial>(coins k))"
    by simp
  also have "... = (\<Sum>j<2 ^ k. indicat_real {l. \<lfloor>real l*h\<rfloor> < \<lfloor>(real l+1)*h\<rfloor>} j * pmf (coins k) j)"
    by (intro integral_measure_pmf_real[where A="{..<2^k}"]) (simp_all add:lessThan_empty_iff)
  also have "... = (\<Sum>l<2 ^ k. of_bool (\<lfloor>real l*h\<rfloor> < \<lfloor>(real l+1)*h\<rfloor>)) / 2^k"
    by (simp add:lessThan_empty_iff indicator_def flip:sum_divide_distrib)
  also have "... \<le> (\<Sum>l<2 ^ k. of_int \<lfloor>real (Suc l)*h\<rfloor> - of_int \<lfloor>real l*h\<rfloor>) / 2^k"
    using h_gt_0 int_less_real_le
    by (intro divide_right_mono sum_mono) (auto intro:floor_mono simp:algebra_simps)
  also have "... = of_int \<lfloor>2 ^ k * h\<rfloor> / 2 ^ k"
    by (subst sum_lessThan_telescope) simp
  also have "... = real n / 2^k"
    unfolding h_def by simp
  finally show ?thesis
    by simp
qed

lemma dice_roll_expected_consumption_aux:
  assumes "n > (0::nat)"
  shows "expected_coin_usage_of_tspmf (dice_roll_tspmf n) \<le> log 2 n + 2" (is "?L \<le> ?R")
proof -
  define k0 where "k0 = nat \<lceil>log 2 n\<rceil>"
  define \<delta> where "\<delta> = log 2 n - \<lceil>log 2 n\<rceil>"

  have 0: "ennreal (measure (coin_usage_of_tspmf (dice_roll_tspmf n)) {x. x > enat k}) \<le>
    ennreal (min (real n/2^k) 1)" (is "?L1 \<le> ?R1") for k
    by (intro iffD2[OF ennreal_le_iff] min.boundedI dice_roll_consumption_bound[OF assms]) auto

  have 1[simp]: "(2::ennreal)^k < Orderings.top" for k::nat
    using ennreal_numeral_less_top power_less_top_ennreal by blast

  have "(\<Sum>k. ennreal ((1/2)^k)) = ennreal (\<Sum>k. ((1/2)^k))"
    by (intro suminf_ennreal2) auto
  also have "... = ennreal 2"
    by (subst suminf_geometric) simp_all
  finally have 2:"(\<Sum>k. ennreal ((1/2)^k)) = ennreal 2"
    by simp

  have "real n \<ge> 1"
    using assms by simp
  hence 3: "log 2 (real n) \<ge> 0"
    by simp

  have "real_of_int \<lceil>log 2 (real n)\<rceil> \<le> 1 + log 2 (real n)"
    by linarith
  hence 4: "\<delta>+1 \<in> {0..1}"
    unfolding \<delta>_def by (auto simp:algebra_simps)

  have twop_conv: "convex_on UNIV (\<lambda>x. 2 powr (x::real))"
    using convex_on_exp[where l="ln 2"] unfolding powr_def
    by (auto simp:algebra_simps)
  have 5:"2 powr x \<le> 1 + x" if "x \<in> {0..1}" for x :: real
    using that convex_onD[OF twop_conv, where x="0" and y="1" and t="x"]
    by (simp add:algebra_simps)

  have "?L = (\<Sum>k. ennreal (measure (coin_usage_of_tspmf (dice_roll_tspmf n)) {x. x > enat k}))"
    unfolding expected_coin_usage_of_tspmf by simp
  also have "... \<le> (\<Sum>k. ennreal (min (real n/2^k) 1))"
    by (intro suminf_le summableI 0)
  also have "... = (\<Sum>k. ennreal (min (real n/2^(k+k0)) 1))+(\<Sum>k < k0. ennreal(min (real n/2^k) 1))"
    by (intro suminf_offset summableI)
  also have "... \<le> (\<Sum>k. ennreal (real n/2^(k+k0))) + (\<Sum>k < k0. 1)"
    by (intro add_mono suminf_le summableI sum_mono iffD2[OF ennreal_le_iff]) auto
  also have "... = (\<Sum>k. ennreal (real n /2^k0) * ennreal ((1/2)^k)) + of_nat k0"
    by (intro suminf_cong arg_cong2[where f="(+)"])
     (simp_all add: ennreal_mult[symmetric] power_add divide_simps)
  also have "... = ennreal (real n /2^k0) * (\<Sum>k. ennreal ((1/2)^k)) + ennreal (real k0)"
    unfolding ennreal_of_nat_eq_real_of_nat by simp
  also have "... = ennreal (real n / 2^k0 * 2 + real k0)"
    unfolding 2 by (subst ennreal_mult[symmetric]) simp_all
  also have "... = ennreal (real n / 2 powr k0 * 2 + real k0)"
    by (subst powr_realpow) auto
  also have "... = ennreal (real n / 2 powr \<lceil>log 2 n\<rceil> * 2 + real k0)"
    using 3 unfolding k0_def by (subst of_nat_nat) auto
  also have "... = ennreal (real n / 2 powr (log 2 n - \<delta>) * 2 + real k0)"
    unfolding \<delta>_def by simp
  also have "... = ennreal (2 powr \<delta> * 2 powr 1 + real k0)"
    using assms unfolding powr_diff by (subst powr_log_cancel) auto
  also have "... \<le> ennreal (1+(\<delta>+1) + real k0)"
    using 4 unfolding powr_add[symmetric]
    by (intro iffD2[OF ennreal_le_iff] add_mono 5) auto
  also have "... = ?R"
    using 3 unfolding \<delta>_def k0_def by (subst of_nat_nat) auto
  finally show ?thesis
    by simp
qed

theorem dice_roll_coin_usage:
  assumes "n > (0::nat)"
  shows "expected_coin_usage_of_ra (dice_roll_ra n) \<le> log 2 n + 2" (is "?L \<le> ?R")
proof -
  have "?L = expected_coin_usage_of_tspmf (tspmf_of_ra (dice_roll_ra n))"
    unfolding expected_coin_usage_of_tspmf_correct[symmetric] by simp
  also have "... = expected_coin_usage_of_tspmf (dice_roll_tspmf n)"
    unfolding dice_roll_ra_tspmf by simp
  also have "... \<le> ?R"
    by (intro dice_roll_expected_consumption_aux assms)
  finally show ?thesis
    by simp
qed

end