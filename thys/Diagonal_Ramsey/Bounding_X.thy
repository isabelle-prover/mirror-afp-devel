section \<open>Bounding the Size of @{term X}\<close>

theory Bounding_X imports Bounding_Y

begin

subsection \<open>Preliminaries\<close>

lemma sum_odds_even:
  fixes f :: "nat \<Rightarrow> 'a :: ab_group_add"
  assumes "even m"
  shows "(\<Sum>i \<in> {i. i<m \<and> odd i}. f (Suc i) - f (i -Suc 0)) = f m - f 0"
  using assms
proof (induction m rule: less_induct)
  case (less m)
  show ?case
  proof (cases "m<2")
    case True
    with \<open>even m\<close> show ?thesis
       by fastforce
  next
    case False
    have eq: "{i. i<m \<and> odd i} = insert (m-1) {i. i<m-2 \<and> odd i}"
    proof
      show "{i. i < m \<and> odd i} \<subseteq> insert (m - 1) {i. i < m - 2 \<and> odd i}"
        using \<open>even m\<close> by clarify presburger
    qed (use False less in auto)
    have [simp]: "\<not> (m - Suc 0 < m - 2)"
      by linarith
    show ?thesis
      using False by (simp add: eq less flip: numeral_2_eq_2)
  qed
qed 

lemma sum_odds_odd:
  fixes f :: "nat \<Rightarrow> 'a :: ab_group_add"
  assumes "odd m"
  shows "(\<Sum>i \<in> {i. i<m \<and> odd i}. f (Suc i) - f (i - Suc 0)) = f (m-1) - f 0"
proof -
  have eq: "{i. i<m \<and> odd i} = {i. i<m-1 \<and> odd i}"
    using assms not_less_iff_gr_or_eq by fastforce
  show ?thesis
    by (simp add: sum_odds_even eq assms)
qed


context Book
begin

text \<open>the set of moderate density-boost steps (page 20)\<close>
definition dboost_star where
  "dboost_star \<equiv> {i \<in> Step_class {dboost_step}. real (hgt (pseq (Suc i))) - hgt (pseq i) \<le> \<epsilon> powr (-1/4)}"

definition bigbeta where
  "bigbeta \<equiv> let S = dboost_star in if S = {} then \<mu> else (card S) * inverse (\<Sum>i\<in>S. inverse (beta i))"

lemma dboost_star_subset: "dboost_star \<subseteq> Step_class {dboost_step}"
  by (auto simp: dboost_star_def)

lemma finite_dboost_star: "finite (dboost_star)"
    by (meson dboost_step_finite dboost_star_subset finite_subset)

lemma bigbeta_ge0: "bigbeta \<ge> 0"
  using \<mu>01 by (simp add: bigbeta_def Let_def beta_ge0 sum_nonneg)

lemma bigbeta_ge_square:
  assumes big: "Big_Red_5_3 \<mu> l"
  shows "bigbeta \<ge> 1 / (real k)^2"
proof -
  have k: "1 / (real k)\<^sup>2 \<le> \<mu>"
    using big kn0 l_le_k by (auto simp: Big_Red_5_3_def)
  have fin: "finite (dboost_star)"
    using assms finite_dboost_star by blast
  have R53: "\<forall>i \<in> Step_class {dboost_step}. 1 / (real k)^2 \<le> beta i"
    using Red_5_3 assms by blast 
  show "1 / (real k)^2 \<le> bigbeta"
  proof (cases "dboost_star = {}")
    case True
    then show ?thesis
      using assms k by (simp add: bigbeta_def)
  next
    case False
    then have card_gt0: "card (dboost_star) > 0"
      by (meson card_gt_0_iff dboost_star_subset fin finite_subset)
    moreover have *: "\<forall>i \<in> dboost_star. beta i > 0 \<and> (real k)^2 \<ge> inverse (beta i)"
      using R53 kn0 assms by (simp add: beta_gt0 field_simps dboost_star_def)
    ultimately have "(\<Sum>i\<in>dboost_star. inverse (beta i)) \<le> card (dboost_star) * (real k)^2"
      by (simp add: sum_bounded_above)
    moreover have "(\<Sum>i\<in>dboost_star. inverse (beta i)) \<noteq> 0"
      by (metis * False fin inverse_positive_iff_positive less_irrefl sum_pos)
    ultimately show ?thesis
      using False card_gt0 k bigbeta_ge0 
      by (simp add: bigbeta_def Let_def divide_simps split: if_split_asm)
  qed
qed


lemma bigbeta_gt0:
  assumes big: "Big_Red_5_3 \<mu> l"
  shows "bigbeta > 0"
  by (smt (verit) kn0 assms bigbeta_ge_square of_nat_zero_less_power_iff zero_less_divide_iff)

lemma bigbeta_less1:
  assumes big: "Big_Red_5_3 \<mu> l"
  shows "bigbeta < 1"
proof -
  have *: "\<forall>i\<in>Step_class {dboost_step}. 0 < beta i"
    using assms beta_gt0 big by blast 
  have fin: "finite (Step_class {dboost_step})"
    using dboost_step_finite  assms by blast
  show "bigbeta < 1"
  proof (cases "dboost_star = {}")
    case True
    then show ?thesis
      using assms \<mu>01 by (simp add: bigbeta_def)
  next
    case False
    then have gt0: "card (dboost_star) > 0"
      by (meson card_gt_0_iff dboost_star_subset fin finite_subset)
    have "real (card (dboost_star)) = (\<Sum>i\<in>dboost_star. 1)"
      by simp
    also have "\<dots>  < (\<Sum>i\<in>dboost_star. 1 / beta i)"
    proof (intro sum_strict_mono)
      show "finite (dboost_star)"
        using card_gt_0_iff gt0 by blast
      fix i
      assume "i \<in> dboost_star"
      with assms \<mu>01 "*" dboost_star_subset beta_le
      show "1 < 1 / beta i"
        by (force simp: Step_class_insert_NO_MATCH)
    qed (use False in auto)
    finally show ?thesis
      using False by (simp add: bigbeta_def Let_def divide_simps)
  qed
qed

lemma bigbeta_le:
  assumes big: "Big_Red_5_3 \<mu> l"
  shows "bigbeta \<le> \<mu>"
proof -
  have "real (card (dboost_star)) = (\<Sum>i\<in>dboost_star. 1)"
    by simp
  also have "\<dots> \<le> (\<Sum>i\<in>dboost_star. \<mu> / beta i)"
  proof (intro sum_mono)
    fix i
    assume i: "i \<in> dboost_star"
    with beta_le dboost_star_subset have "beta i \<le> \<mu>"
      by (auto simp: Step_class_insert_NO_MATCH)
    with beta_gt0 assms show "1 \<le> \<mu> / beta i"
      by (smt (verit) dboost_star_subset divide_less_eq_1_pos i subset_iff)
  qed
  also have "\<dots> = \<mu> * (\<Sum>i\<in>dboost_star. 1 / beta i)"
    by (simp add: sum_distrib_left)
  finally have "real (card (dboost_star)) \<le> \<mu> * (\<Sum>i\<in>dboost_star. 1 / beta i)" .
  moreover have "(\<Sum>i\<in>dboost_star. 1 / beta i) \<ge> 0"
    by (simp add: beta_ge0 sum_nonneg)
  ultimately show ?thesis
    using \<mu>01 by (simp add: bigbeta_def Let_def divide_simps)
qed

end

subsection \<open>Lemma 7.2\<close>

definition "Big_X_7_2 \<equiv> \<lambda>\<mu> l. nat \<lceil>real l powr (3/4)\<rceil> \<ge> 3 \<and> l > 1 / (1-\<mu>)"

text \<open>establishing the size requirements for 7.11\<close>
lemma Big_X_7_2:
  assumes "0<\<mu>0" "\<mu>1<1" 
  shows "\<forall>\<^sup>\<infinity>l. \<forall>\<mu>. \<mu> \<in> {\<mu>0..\<mu>1} \<longrightarrow> Big_X_7_2 \<mu> l"
  unfolding Big_X_7_2_def eventually_conj_iff all_imp_conj_distrib eps_def
  apply (simp add: eventually_conj_iff all_imp_conj_distrib)  
  apply (intro conjI strip eventually_all_geI1[where L=1] eventually_all_ge_at_top)
  apply real_asymp+
  by (smt (verit, best) \<open>\<mu>1<1\<close> frac_le)

definition "ok_fun_72 \<equiv> \<lambda>\<mu> k. (real k / ln 2) * ln (1 - 1 / (k * (1-\<mu>)))" 

lemma ok_fun_72:
  assumes "\<mu><1" 
  shows "ok_fun_72 \<mu> \<in> o(real)"
  using assms unfolding ok_fun_72_def by real_asymp

lemma ok_fun_72_uniform:
  assumes "0<\<mu>0" "\<mu>1<1" 
  assumes "e>0" 
  shows   "\<forall>\<^sup>\<infinity>k. \<forall>\<mu>. \<mu>0 \<le> \<mu> \<and> \<mu> \<le> \<mu>1 \<longrightarrow> \<bar>ok_fun_72 \<mu> k\<bar> / k \<le> e" 
proof (intro eventually_all_geI1 [where L = "Suc(nat\<lceil>1/(1-\<mu>1)\<rceil>)"])
  show "\<forall>\<^sup>\<infinity>k. \<bar>ok_fun_72 \<mu>1 k\<bar> / real k \<le> e"
    using assms unfolding ok_fun_72_def by real_asymp
next
  fix k \<mu>
  assume le_e: "\<bar>ok_fun_72 \<mu>1 k\<bar> / real k \<le> e"
    and \<mu>: "\<mu>0 \<le> \<mu>" "\<mu> \<le> \<mu>1"
    and k: "Suc(nat\<lceil>1/(1-\<mu>1)\<rceil>) \<le> k"
  with assms have "1 > 1 / (real k * (1 - \<mu>1))"
    by (smt (verit, best) divide_less_eq divide_less_eq_1 less_eq_Suc_le natceiling_lessD)
  then have *: "1 > 1 / (real k * (1 - r))" if "r\<le>\<mu>1" for r
    using that assms k less_le_trans by fastforce
  have \<dagger>: "1 / (k * (1 - \<mu>)) \<le> 1 / (k * (1 - \<mu>1))"
    using \<mu> assms by (simp add: divide_simps mult_less_0_iff)
  obtain "\<mu><1" "k>0" using \<mu> k assms by force
  then have "\<bar>ok_fun_72 \<mu> k\<bar> \<le> \<bar>ok_fun_72 \<mu>1 k\<bar>"
    using \<mu> * assms \<dagger>
    by (simp add: ok_fun_72_def abs_mult zero_less_mult_iff abs_of_neg divide_le_cancel)
  then show "\<bar>ok_fun_72 \<mu> k\<bar> / real k \<le> e"
    by (smt (verit, best) le_e divide_right_mono of_nat_0_le_iff)
qed

lemma (in Book) X_7_2:
  defines "\<R> \<equiv> Step_class {red_step}"
  assumes big: "Big_X_7_2 \<mu> l"
  shows "(\<Prod>i\<in>\<R>. card (Xseq(Suc i)) / card (Xseq i)) \<ge> 2 powr (ok_fun_72 \<mu> k) * (1-\<mu>) ^ card \<R>"
proof -
  define R where "R \<equiv> RN k (nat \<lceil>real l powr (3/4)\<rceil>)"
  have l34_ge3: "nat \<lceil>real l powr (3/4)\<rceil> \<ge> 3" and k_gt: "k > 1 / (1-\<mu>)"
    using big l_le_k by (auto simp: Big_X_7_2_def)
  then obtain "R > k" "k \<ge> 2"
    using \<mu>01 RN_gt1 R_def l_le_k
    by (smt (verit, best) divide_le_eq_1_pos fact_2 nat_le_real_less of_nat_fact)
  with k_gt \<mu>01 have bigR: "1-\<mu> > 1/R"
    by (smt (verit, best) less_imp_of_nat_less ln_div ln_le_cancel_iff zero_less_divide_iff)
  have *: "1-\<mu> - 1/R \<le> card (Xseq (Suc i)) / card (Xseq i)"
    if  "i \<in> \<R>" for i
  proof -
    let ?NRX = "\<lambda>i. Neighbours Red (cvx i) \<inter> Xseq i"
    have nextX: "Xseq (Suc i) = ?NRX i" and nont: "\<not> termination_condition (Xseq i) (Yseq i)"
      using that by (auto simp: \<R>_def step_kind_defs next_state_def split: prod.split)
    then have cardX: "card (Xseq i) > R"
      unfolding R_def by (meson not_less termination_condition_def)
    have 1: "card (?NRX i) \<ge> (1-\<mu>) * card (Xseq i) - 1"
      using that card_cvx_Neighbours \<mu>01 by (simp add: \<R>_def Step_class_def)
    have "R \<noteq> 0"
      using \<open>k < R\<close> by linarith
    with cardX have "(1-\<mu>) - 1 / R \<le> (1-\<mu>) - 1 / card (Xseq i)"
      by (simp add: inverse_of_nat_le)
    also have "\<dots> \<le> card (Xseq (Suc i)) / card (Xseq i)"
      using cardX nextX 1 by (simp add: divide_simps)
    finally show ?thesis .
  qed
  have fin_red: "finite \<R>"
    using red_step_finite by (auto simp: \<R>_def)
  define t where "t \<equiv> card \<R>"
  have "t\<ge>0"
    by (auto simp: t_def)
  have "(1-\<mu> - 1/R) ^ card Red_steps \<le> (\<Prod>i \<in> Red_steps. card (Xseq(Suc i)) / card (Xseq i))"
    if "Red_steps \<subseteq> \<R>" for Red_steps
    using finite_subset [OF that fin_red] that
  proof induction
    case empty
    then show ?case
      by auto
  next
    case (insert i Red_steps)
    then have i: "i \<in> \<R>"
      by auto
    have "((1-\<mu>) - 1/R) ^ card (insert i Red_steps) = ((1-\<mu>) - 1/R) * ((1-\<mu>) - 1/R) ^ card (Red_steps)"
      by (simp add: insert)
    also have "\<dots> \<le> (card (Xseq (Suc i)) / card (Xseq i)) * ((1-\<mu>) - 1/R) ^ card (Red_steps)"
      using bigR by (intro mult_right_mono * i) auto
    also have "\<dots> \<le> (card (Xseq (Suc i)) / card (Xseq i)) * (\<Prod>i \<in> Red_steps. card (Xseq(Suc i)) / card (Xseq i))"
      using insert by (intro mult_left_mono) auto
    also have "\<dots> = (\<Prod>i\<in>insert i Red_steps. card (Xseq(Suc i)) / card (Xseq i))"
      using insert by simp
    finally show ?case .
  qed
  then have *: "(1-\<mu> - 1/R) ^ t \<le> (\<Prod>i \<in> \<R>. card (Xseq(Suc i)) / card (Xseq i))"
    using t_def by blast
  \<comment> \<open>Asymptotic part of the argument\<close>
  have "1-\<mu> - 1/k \<le> 1-\<mu> - 1/R"
    using kn0 \<open>k < R\<close> by (simp add: inverse_of_nat_le)
  then have ln_le: "ln (1-\<mu> - 1/k) \<le> ln (1-\<mu> - 1/R)"
    using \<mu>01 k_gt \<open>R>k\<close> by (simp add: bigR divide_simps mult.commute less_le_trans)
  have "ok_fun_72 \<mu> k * ln 2 = k * ln (1 - 1 / (k * (1-\<mu>)))"
    by (simp add: ok_fun_72_def)
  also have "\<dots> \<le> t * ln (1 - 1 / (k * (1-\<mu>)))"
  proof (intro mult_right_mono_neg)
    have red_steps: "card \<R> < k"
      using red_step_limit \<open>0<\<mu>\<close> by (auto simp: \<R>_def)
    show "real t \<le> real k"
      using nat_less_le red_steps by (simp add: t_def)
    show "ln (1 - 1 / (k * (1-\<mu>))) \<le> 0"
      using \<mu>01 divide_less_eq k_gt ln_one_minus_pos_upper_bound by fastforce
  qed
  also have "\<dots> = t * ln ((1-\<mu> - 1/k) / (1-\<mu>))"
    using \<open>t\<ge>0\<close> \<mu>01 by (simp add: diff_divide_distrib)
  also have "\<dots> = t * (ln (1-\<mu> - 1/k) - ln (1-\<mu>))"
    using \<open>t\<ge>0\<close> \<mu>01 k_gt kn0 ln_div by force
  also have "\<dots> \<le> t * (ln (1-\<mu> - 1/R) - ln (1-\<mu>))"
    by (simp add: ln_le mult_left_mono)
  finally have "ok_fun_72 \<mu> k * ln 2 + t * ln (1-\<mu>) \<le> t * ln (1-\<mu> - 1/R)"
    by (simp add: ring_distribs)
  then have "2 powr ok_fun_72 \<mu> k * (1-\<mu>) ^ t \<le> (1-\<mu> - 1/R) ^ t"
    using \<mu>01 by (simp add: bigR ln_mult ln_powr ln_realpow flip: ln_le_cancel_iff)
  with * show ?thesis
    by (simp add: t_def)
qed

subsection \<open>Lemma 7.3\<close>

context Book
begin

definition "Bdelta \<equiv> \<lambda> \<mu> i. Bseq (Suc i) \<setminus> Bseq i"

lemma card_Bdelta: "card (Bdelta \<mu> i) = card (Bseq (Suc i)) - card (Bseq i)"
  by (simp add: Bseq_mono Bdelta_def card_Diff_subset finite_Bseq)

lemma card_Bseq_mono: "card (Bseq (Suc i)) \<ge> card (Bseq i)"
  by (simp add: Bseq_Suc_subset card_mono finite_Bseq)

lemma card_Bseq_sum: "card (Bseq i) = (\<Sum>j<i. card (Bdelta \<mu> j))"
proof (induction i)
  case 0
  then show ?case
    by auto
next
  case (Suc i)
  with card_Bseq_mono show ?case
    unfolding card_Bdelta sum.lessThan_Suc
    by (smt (verit, del_insts) Nat.add_diff_assoc diff_add_inverse)
qed

definition "get_blue_book \<equiv> \<lambda>i. let (X,Y,A,B) = stepper i in choose_blue_book (X,Y,A,B)"

text \<open>Tracking changes to X and B. The sets are necessarily finite\<close>
lemma Bdelta_bblue_step:
  assumes "i \<in> Step_class {bblue_step}" 
  shows "\<exists>S \<subseteq> Xseq i. Bdelta \<mu> i = S
            \<and> card (Xseq (Suc i)) \<ge> (\<mu> ^ card S) * card (Xseq i) / 2"
proof -
  obtain X Y A B S T where step: "stepper i = (X,Y,A,B)" and bb: "get_blue_book i = (S,T)"
    and valid: "valid_state(X,Y,A,B)"
    by (metis surj_pair valid_state_stepper)
  moreover have "finite X"
    by (metis V_state_stepper finX step)
  ultimately have *: "stepper (Suc i) = (T, Y, A, B\<union>S) \<and> good_blue_book X (S,T)" 
    and Xeq: "X = Xseq i"
    using assms choose_blue_book_works [of X S T Y A B]
    by (simp_all add: step_kind_defs next_state_def valid_state_def get_blue_book_def choose_blue_book_works split: if_split_asm)
  show ?thesis
  proof (intro exI conjI)
    have "S \<subseteq> X"
    proof (intro choose_blue_book_subset [THEN conjunct1] \<open>finite X\<close>)
      show "(S, T) = choose_blue_book (X, Y, A, B)"
        using bb step by (simp add: get_blue_book_def Xseq_def)
    qed
    then show "S \<subseteq> Xseq i"
      using Xeq by force
    have "disjnt X B"
      using valid by (auto simp: valid_state_def disjoint_state_def)
    then show "Bdelta \<mu> i = S"
      using * step \<open>S \<subseteq> X\<close> by (auto simp: Bdelta_def Bseq_def disjnt_iff)
    show "\<mu> ^ card S * real (card (Xseq i)) / 2 \<le> real (card (Xseq (Suc i)))"
      using * by (auto simp: Xseq_def good_blue_book_def step)
  qed
qed

lemma Bdelta_dboost_step:
  assumes "i \<in> Step_class {dboost_step}" 
  shows "\<exists>x \<in> Xseq i. Bdelta \<mu> i = {x}"
proof -
  obtain X Y A B where step: "stepper i = (X,Y,A,B)" and valid: "valid_state(X,Y,A,B)"
    by (metis surj_pair valid_state_stepper)
  have cvx: "choose_central_vx (X,Y,A,B) \<in> X"
    by (metis Step_class_insert Un_iff cvx_def cvx_in_Xseq assms step stepper_XYseq)
  then have "\<exists>X' Y'. stepper (Suc i) = (X', Y', A, insert (choose_central_vx (X,Y,A,B)) B)"
    using assms step
    by (auto simp: step_kind_defs next_state_def split: if_split_asm)
  moreover have "choose_central_vx (X,Y,A,B) \<notin> B"
    using valid cvx by (force simp: valid_state_def disjoint_state_def disjnt_iff)
  ultimately show ?thesis
    using step cvx by (auto simp: Bdelta_def Bseq_def disjnt_iff Xseq_def)
qed

lemma card_Bdelta_dboost_step:
  assumes "i \<in> Step_class {dboost_step}" 
  shows "card (Bdelta \<mu> i) = 1"
  using Bdelta_dboost_step [OF assms] by force

lemma Bdelta_trivial_step:
  assumes i: "i \<in> Step_class {red_step,dreg_step,halted}" 
  shows "Bdelta \<mu> i = {}"
  using assms
  by (auto simp: step_kind_defs next_state_def Bdelta_def degree_reg_def split: if_split_asm prod.split)

end

definition "ok_fun_73 \<equiv> \<lambda>k. - (real k powr (3/4))" 

lemma ok_fun_73: "ok_fun_73  \<in> o(real)"
  unfolding ok_fun_73_def by real_asymp

lemma (in Book) X_7_3:
  assumes big: "Big_Blue_4_1 \<mu> l"
  defines "\<B> \<equiv> Step_class {bblue_step}"
  defines "\<S> \<equiv> Step_class {dboost_step}"
  shows "(\<Prod>i \<in> \<B>. card (Xseq(Suc i)) / card (Xseq i)) \<ge> 2 powr (ok_fun_73 k) * \<mu> ^ (l - card \<S>)"
proof -
  have [simp]: "finite \<B>" "finite \<S>" and card\<B>: "card \<B> \<le> l powr (3/4)"
    using assms bblue_step_limit big by (auto simp: \<B>_def \<S>_def)
  define b where "b \<equiv> \<lambda>i. card (Bdelta \<mu> i)"
  obtain i where "card (Bseq i) = sum b \<B> + card \<S>" 
  proof -
    define i where "i = Suc (Max (\<B> \<union> \<S>))"
    define TRIV where "TRIV \<equiv> Step_class {red_step,dreg_step,halted} \<inter> {..<i}"
    have [simp]: "finite TRIV"
      by (auto simp: TRIV_def)
    have eq: "\<B> \<union> \<S> \<union> TRIV = {..<i}"
    proof
      show "\<B> \<union> \<S> \<union> TRIV \<subseteq> {..<i}"
        by (auto simp: i_def TRIV_def less_Suc_eq_le)
      show "{..<i} \<subseteq> \<B> \<union> \<S> \<union> TRIV"
        using stepkind.exhaust by (auto simp: \<B>_def \<S>_def TRIV_def Step_class_def)
    qed
    have dis: "\<B> \<inter> \<S> = {}" "(\<B> \<union> \<S>) \<inter> TRIV = {}"
      by (auto simp: \<B>_def \<S>_def TRIV_def Step_class_def)
    show thesis
    proof
      have "card (Bseq i) = (\<Sum>j \<in> \<B> \<union> \<S> \<union> TRIV. b j)"
        using card_Bseq_sum eq unfolding b_def by metis
      also have "\<dots> = (\<Sum>j\<in>\<B>. b j) + (\<Sum>j\<in>\<S>. b j) + (\<Sum>j\<in>TRIV. b j)"
        by (simp add: sum_Un_nat dis)
      also have "\<dots> = sum b \<B> + card \<S>"
        by (simp add: b_def \<S>_def card_Bdelta_dboost_step TRIV_def Bdelta_trivial_step)
      finally show "card (Bseq i) = sum b \<B> + card \<S>" .
    qed
  qed
  then have sum_b_\<B>: "sum b \<B> \<le> l - card \<S>"
    by (metis Bseq_less_l less_diff_conv nat_less_le)
  have "real (card \<B>) \<le> real k powr (3/4)"
    using card\<B> l_le_k
    by (smt (verit, best) divide_nonneg_pos of_nat_0_le_iff of_nat_mono powr_mono2)
  then have "2 powr (ok_fun_73 k) \<le> (1/2) ^ card \<B>"
    by (simp add: ok_fun_73_def powr_minus divide_simps flip: powr_realpow)
  then have "2 powr (ok_fun_73 k) * \<mu> ^ (l - card \<S>) \<le> (1/2) ^ card \<B> * \<mu> ^ (l - card \<S>)"
    by (simp add: \<mu>01)
  also have "(1/2) ^ card \<B> * \<mu> ^ (l - card \<S>) \<le> (1/2) ^ card \<B> * \<mu> ^ (sum b \<B>)" 
    using \<mu>01 sum_b_\<B> by simp
  also have "\<dots> = (\<Prod>i\<in>\<B>. \<mu> ^ b i / 2)"
    by (simp add: power_sum prod_dividef divide_simps)
  also have "\<dots> \<le> (\<Prod>i\<in>\<B>. card (Xseq (Suc i)) / card (Xseq i))"
  proof (rule prod_mono)
    fix i :: nat
    assume "i \<in> \<B>"
    then have "\<not> termination_condition (Xseq i) (Yseq i)"
      by (simp add: \<B>_def Step_class_def flip: step_non_terminating_iff)
    then have "card (Xseq i) \<noteq> 0"
      using termination_condition_def by force
    with \<open>i\<in>\<B>\<close> \<mu>01 show "0 \<le> \<mu> ^ b i / 2 \<and> \<mu> ^ b i / 2 \<le> card (Xseq (Suc i)) / card (Xseq i)"
      by (force simp: b_def \<B>_def divide_simps dest!: Bdelta_bblue_step)
  qed
  finally show ?thesis .
qed

subsection \<open>Lemma 7.5\<close>

text \<open>Small $o(k)$ bounds on summations for this section\<close>

text \<open>This is the explicit upper bound for heights given just below (5) on page 9\<close>
definition "ok_fun_26 \<equiv> \<lambda>k. 2 * ln k / eps k" 

definition "ok_fun_28 \<equiv> \<lambda>k. -2 * real k powr (7/8)"  

lemma ok_fun_26: "ok_fun_26 \<in> o(real)" and ok_fun_28: "ok_fun_28 \<in> o(real)"
  unfolding ok_fun_26_def ok_fun_28_def eps_def by real_asymp+

definition 
  "Big_X_7_5 \<equiv> 
    \<lambda>\<mu> l. Big_Blue_4_1 \<mu> l \<and> Big_Red_5_3 \<mu> l \<and> Big_Y_6_5_Bblue l
        \<and> (\<forall>k\<ge>l. Big_height_upper_bound k \<and> k\<ge>16 \<and> (ok_fun_26 k - ok_fun_28 k \<le> k))"

text \<open>establishing the size requirements for 7.5\<close>
lemma Big_X_7_5:
  assumes "0<\<mu>0" "\<mu>1<1" 
  shows "\<forall>\<^sup>\<infinity>l. \<forall>\<mu>. \<mu> \<in> {\<mu>0..\<mu>1} \<longrightarrow> Big_X_7_5 \<mu> l"
proof -
  have ok: "\<forall>\<^sup>\<infinity>l. ok_fun_26 l - ok_fun_28 l \<le> l" 
    unfolding eps_def ok_fun_26_def ok_fun_28_def by real_asymp
  show ?thesis
    using assms Big_Y_6_5_Bblue Big_Red_5_3 Big_Blue_4_1 
    unfolding Big_X_7_5_def 
    apply (simp add: eventually_conj_iff all_imp_conj_distrib)  
    apply (intro conjI strip eventually_all_ge_at_top ok Big_height_upper_bound; real_asymp)
    done
qed

context Book
begin

lemma X_26_and_28:
  assumes big: "Big_X_7_5 \<mu> l"
  defines "\<D> \<equiv> Step_class {dreg_step}"
  defines "\<B> \<equiv> Step_class {bblue_step}"
  defines "\<H> \<equiv> Step_class {halted}"
  defines "h \<equiv> \<lambda>i. real (hgt (pseq i))"
  obtains "(\<Sum>i\<in>{..<halted_point} \<setminus> \<D>. h (Suc i) - h (i-1)) \<le> ok_fun_26 k"
          "ok_fun_28 k \<le> (\<Sum>i \<in> \<B>. h(Suc i) - h(i-1))"
proof -
  define \<S> where "\<S> \<equiv> Step_class {dboost_step}" 
  have B_limit: "Big_Blue_4_1 \<mu> l" and bigY65B: "Big_Y_6_5_Bblue l"
    and hub: "Big_height_upper_bound k"
    using big l_le_k by (auto simp: Big_X_7_5_def)
  have m_minimal: "i \<notin> \<H> \<longleftrightarrow> i < halted_point" for i
    unfolding \<H>_def using halted_point_minimal assms by blast
  have oddset: "{..<halted_point} \<setminus> \<D> = {i \<in> {..<halted_point}. odd i}" 
    using m_minimal step_odd step_even not_halted_even_dreg 
    by (auto simp: \<D>_def \<H>_def Step_class_insert_NO_MATCH)
      \<comment> \<open>working on 28\<close>
  have "ok_fun_28 k \<le> -2 * \<epsilon> powr (-1/2) * card \<B>"
  proof -
    have "k powr (1/8) * card \<B> \<le> k powr (1/8) * l powr (3/4)"
      using B_limit bblue_step_limit by (simp add: \<B>_def mult_left_mono)
    also have "\<dots> \<le> k powr (1/8) * k powr (3/4)"
      by (simp add: l_le_k mult_mono powr_mono2)
    also have "\<dots> = k powr (7/8)"
      by (simp flip: powr_add)
    finally show ?thesis
      by (simp add: eps_def powr_powr ok_fun_28_def)
  qed
  also have "\<dots> \<le> (\<Sum>i \<in> \<B>. h(Suc i) - h(i-1))"
  proof -
    have "(\<Sum>i \<in> \<B>. -2 * \<epsilon> powr (-1/2)) \<le> (\<Sum>i \<in> \<B>. h(Suc i) - h(i-1))"
    proof (rule sum_mono)
      fix i :: nat
      assume i: "i \<in> \<B>"
      show "-2 * \<epsilon> powr (-1/2) \<le> h(Suc i) - h(i-1)"
        using bigY65B kn0 i Y_6_5_Bblue by (fastforce simp: \<B>_def h_def)
    qed
    then show ?thesis 
      by (simp add: mult.commute)
  qed
  finally have 28: "ok_fun_28 k \<le> (\<Sum>i \<in> \<B>. h(Suc i) - h(i-1))" .
  have "(\<Sum>i \<in> {..<halted_point} \<setminus> \<D>. h(Suc i) - h(i-1)) \<le> h halted_point - h 0"
  proof (cases "even halted_point")
    case False
    have "hgt (pseq (halted_point - Suc 0)) \<le> hgt (pseq halted_point)"
      using Y_6_5_DegreeReg [of "halted_point-1"] False m_minimal not_halted_even_dreg odd_pos  
      by (fastforce simp: \<H>_def)
    then have "h(halted_point - Suc 0) \<le> h halted_point"
      using h_def of_nat_mono by blast
    with False show ?thesis
      by (simp add: oddset sum_odds_odd)
  qed (simp add: oddset sum_odds_even)
  also have "\<dots> \<le> ok_fun_26 k"
  proof -
    have "hgt (pseq i) \<ge> 1" for i
      by (simp add: Suc_leI hgt_gt0)
    moreover have "hgt (pseq halted_point) \<le> ok_fun_26 k"
      using hub pee_le1 height_upper_bound unfolding ok_fun_26_def by blast 
    ultimately show ?thesis
      by (simp add: h_def)
  qed
  finally have 26: "(\<Sum>i\<in>{..<halted_point} \<setminus> \<D>. h (Suc i) - h (i-1)) \<le> ok_fun_26 k" .
  with 28 show ?thesis
    using that by blast
qed

proposition X_7_5:
  assumes \<mu>: "0<\<mu>" "\<mu><1" 
  defines "\<S> \<equiv> Step_class {dboost_step}" and "\<S>\<S> \<equiv> dboost_star"
  assumes big: "Big_X_7_5 \<mu> l"
  shows "card (\<S>\<setminus>\<S>\<S>) \<le> 3 * \<epsilon> powr (1/4) * k"
proof -
  define \<D> where "\<D> \<equiv> Step_class {dreg_step}"
  define \<R> where "\<R> \<equiv> Step_class {red_step}"
  define \<B> where "\<B> \<equiv> Step_class {bblue_step}"
  define h where "h \<equiv> \<lambda>i. real (hgt (pseq i))"
  obtain 26: "(\<Sum>i\<in>{..<halted_point} \<setminus> \<D>. h (Suc i) - h (i-1)) \<le> ok_fun_26 k"
     and 28: "ok_fun_28 k \<le> (\<Sum>i \<in> \<B>. h(Suc i) - h(i-1))"
    using X_26_and_28 assms(1-3) big
    unfolding \<B>_def \<D>_def h_def Big_X_7_5_def by blast
  have \<S>\<S>: "\<S>\<S> = {i \<in> \<S>. h(Suc i) - h i \<le> \<epsilon> powr (-1/4)}" and "\<S>\<S> \<subseteq> \<S>"
    by (auto simp: \<S>\<S>_def \<S>_def dboost_star_def h_def)
  have in_S: "h(Suc i) - h i > \<epsilon> powr (-1/4)" if "i \<in> \<S>\<setminus>\<S>\<S>" for i
    using that by (fastforce simp: \<S>\<S>)
  have B_limit: "Big_Blue_4_1 \<mu> l"
      and bigR53: "Big_Red_5_3 \<mu> l"
      and 16: "k\<ge>16" (*for Y_6_5_Red*)
      and ok_fun: "ok_fun_26 k - ok_fun_28 k \<le> k"
    using big l_le_k by (auto simp: Big_X_7_5_def)
  have [simp]: "finite \<R>" "finite \<B>" "finite \<S>"
    using finite_components by (auto simp: \<R>_def \<B>_def \<S>_def)
  have [simp]: "\<R> \<inter> \<S> = {}" "\<B> \<inter> (\<R>\<union>\<S>) = {}"
    by (auto simp: \<R>_def \<S>_def \<B>_def Step_class_def)

  obtain cardss:  "card \<S>\<S> \<le> card \<S>" "card (\<S>\<setminus>\<S>\<S>) = card \<S> - card \<S>\<S>"
    by (meson \<open>\<S>\<S> \<subseteq> \<S>\<close> \<open>finite \<S>\<close> card_Diff_subset card_mono infinite_super)
  have "(\<Sum>i \<in> \<S>. h(Suc i) - h(i-1)) \<ge> \<epsilon> powr (-1/4) * card (\<S>\<setminus>\<S>\<S>)"
  proof -
    have "(\<Sum>i \<in> \<S>\<setminus>\<S>\<S>. h(Suc i) - h(i-1)) \<ge> (\<Sum>i \<in> \<S>\<setminus>\<S>\<S>. \<epsilon> powr (-1/4))"
    proof (rule sum_mono)
      fix i :: nat
      assume i: "i \<in> \<S>\<setminus>\<S>\<S>"
      with i obtain "i-1 \<in> \<D>" "i>0"    
        using dreg_before_step1 dreg_before_gt0 by (fastforce simp: \<S>_def \<D>_def Step_class_insert_NO_MATCH)
      with i show "\<epsilon> powr (-1/4) \<le> h(Suc i) - h(i-1)"
        using in_S[of i] Y_6_5_DegreeReg[of "i-1"] by (simp add: \<D>_def h_def)
    qed
    moreover
    have "(\<Sum>i \<in> \<S>\<S>. h(Suc i) - h(i-1)) \<ge> 0"
    proof (intro sum_nonneg)
      show "\<And>i. i \<in> \<S>\<S> \<Longrightarrow> 0 \<le> h (Suc i) - h (i - 1)"
        using Y_6_4_dbooSt \<mu> bigR53 by(auto simp: h_def \<S>\<S> \<S>_def hgt_mono)
    qed
    ultimately show ?thesis
      by (simp add: mult.commute sum.subset_diff [OF \<open>\<S>\<S> \<subseteq> \<S>\<close> \<open>finite \<S>\<close>])
  qed
  moreover
  have "(\<Sum>i \<in> \<R>. h(Suc i) - h(i-1)) \<ge> (\<Sum>i \<in> \<R>. -2)"
  proof (rule sum_mono)
    fix i :: nat
    assume i: "i \<in> \<R>"
      with i obtain "i-1 \<in> \<D>" "i>0"    
        using dreg_before_step1 dreg_before_gt0 
          by (fastforce simp: \<R>_def \<D>_def Step_class_insert_NO_MATCH)
    with i have "hgt (pseq (i-1)) - 2 \<le> hgt (pseq (Suc i))"
      using Y_6_5_Red[of i] 16 Y_6_5_DegreeReg[of "i-1"]
      by (fastforce simp: algebra_simps \<R>_def \<D>_def)
    then show "- 2 \<le> h(Suc i) - h(i-1)"
      unfolding h_def by linarith
  qed
  ultimately have 27: "(\<Sum>i \<in> \<R>\<union>\<S>. h(Suc i) - h(i-1)) \<ge> \<epsilon> powr (-1/4) * card (\<S>\<setminus>\<S>\<S>) - 2 * card \<R>"
    by (simp add: sum.union_disjoint)

  have "ok_fun_28 k + (\<epsilon> powr (-1/4) * card (\<S>\<setminus>\<S>\<S>) - 2 * card \<R>) \<le> (\<Sum>i \<in> \<B>. h(Suc i) - h(i-1)) + (\<Sum>i \<in> \<R>\<union>\<S>. h(Suc i) - h(i-1))"
    using 27 28 by simp
  also have "\<dots> = (\<Sum>i \<in> \<B> \<union> (\<R>\<union>\<S>). h(Suc i) - h(i-1))"
    by (simp add: sum.union_disjoint)
  also have "\<dots> = (\<Sum>i \<in> {..<halted_point} \<setminus> \<D>. h(Suc i) - h(i-1))"
  proof -
    have "i \<in> \<B> \<union> (\<R>\<union>\<S>)" if "i < halted_point" "i \<notin> \<D>" for i
      using that unfolding \<D>_def \<B>_def \<R>_def \<S>_def
      using Step_class_cases halted_point_minimal by auto
    moreover
    have "i \<in> {..<halted_point} \<setminus> \<D>" if "i \<in> \<B> \<union> (\<R>\<union>\<S>)" for i
      using halted_point_minimal' that by (force simp: \<D>_def \<B>_def \<R>_def \<S>_def  Step_class_def)
    ultimately have "\<B> \<union> (\<R>\<union>\<S>) = {..<halted_point} \<setminus> \<D>"
      by auto
    then show ?thesis
      by simp
  qed
  finally have "ok_fun_28 k + (\<epsilon> powr (-1/4) * card (\<S>\<setminus>\<S>\<S>) - real (2 * card \<R>)) \<le> ok_fun_26 k" 
    using 26 by simp
  then have "real (card (\<S> \<setminus> \<S>\<S>)) \<le> (ok_fun_26 k - ok_fun_28 k + 2 * card \<R>) * \<epsilon> powr (1/4)"
    using eps_gt0 by (simp add: powr_minus field_simps del: div_add div_mult_self3)
  moreover have "card \<R> < k"
    using red_step_limit \<mu> unfolding \<R>_def by blast
  ultimately have "card (\<S>\<setminus>\<S>\<S>) \<le> (k + 2 * k) * \<epsilon> powr (1/4)"
    by (smt (verit, best) of_nat_add mult_2 mult_right_mono nat_less_real_le ok_fun powr_ge_zero)
  then show ?thesis
    by (simp add: algebra_simps)
qed

end

subsection \<open>Lemma 7.4\<close>

definition 
  "Big_X_7_4 \<equiv> \<lambda>\<mu> l. Big_X_7_5 \<mu> l \<and> Big_Red_5_3 \<mu> l"

text \<open>establishing the size requirements for 7.4\<close>
lemma Big_X_7_4:
  assumes "0<\<mu>0" "\<mu>1<1" 
  shows "\<forall>\<^sup>\<infinity>l. \<forall>\<mu>. \<mu> \<in> {\<mu>0..\<mu>1} \<longrightarrow> Big_X_7_4 \<mu> l"
  using assms Big_X_7_5 Big_Red_5_3
  unfolding Big_X_7_4_def  
  by (simp add: eventually_conj_iff all_imp_conj_distrib)


definition "ok_fun_74 \<equiv> \<lambda>k. -6 * eps k powr (1/4) * k * ln k / ln 2" 

lemma ok_fun_74: "ok_fun_74 \<in> o(real)"
  unfolding ok_fun_74_def eps_def by real_asymp

context Book
begin

lemma X_7_4:
  assumes big: "Big_X_7_4 \<mu> l"
  defines "\<S> \<equiv> Step_class {dboost_step}"
  shows "(\<Prod>i\<in>\<S>. card (Xseq (Suc i)) / card (Xseq i)) \<ge> 2 powr ok_fun_74 k * bigbeta ^ card \<S>"
proof -
  define \<S>\<S> where "\<S>\<S> \<equiv> dboost_star"
  then have big53: "Big_Red_5_3 \<mu> l" and X75: "card (\<S>\<setminus>\<S>\<S>) \<le> 3 * \<epsilon> powr (1/4) * k" 
    using \<mu>01 big by (auto simp: Big_X_7_4_def X_7_5 \<S>_def \<S>\<S>_def)
  then have R53:  "pseq (Suc i) \<ge> pseq i \<and> beta i \<ge> 1 / (real k)\<^sup>2" and beta_gt0: "0 < beta i"
    if "i \<in> \<S>" for i
    using that Red_5_3 beta_gt0 by (auto simp: \<S>_def)
  have bigbeta01: "bigbeta \<in> {0<..<1}"
    using big53 assms bigbeta_gt0 bigbeta_less1 by force
  have "\<S>\<S> \<subseteq> \<S>"
    unfolding \<S>\<S>_def \<S>_def dboost_star_def by auto
  then obtain [simp]: "finite \<S>" "finite \<S>\<S>"
    by (simp add: \<S>\<S>_def \<S>_def finite_dboost_star)
  have card_SSS: "card \<S>\<S> \<le> card \<S>"
    by (metis \<S>\<S>_def \<S>_def \<open>finite \<S>\<close> card_mono dboost_star_subset)
  have \<beta>: "beta i = card (Xseq (Suc i)) / card (Xseq i)" if "i \<in> \<S>" for i
  proof -
    have "Xseq (Suc i) = Neighbours Blue (cvx i) \<inter> Xseq i"
      using that unfolding \<S>_def
      by (auto simp: step_kind_defs next_state_def split: prod.split)
    then show ?thesis
      by (force simp: beta_eq)
  qed
  then have *: "(\<Prod>i\<in>\<S>. card (Xseq (Suc i)) / card (Xseq i)) = (\<Prod>i\<in>\<S>. beta i)"
    by force
  have prod_beta_gt0: "prod (beta) S' > 0" if "S' \<subseteq> \<S>" for S'
    using beta_gt0 that
    by (force simp: beta_ge0 intro: prod_pos)
      \<comment> \<open>bounding the immoderate steps\<close>
  have "(\<Prod>i\<in>\<S>\<setminus>\<S>\<S>. 1 / beta i) \<le> (\<Prod>i\<in>\<S>\<setminus>\<S>\<S>. real k ^ 2)"
  proof (rule prod_mono)
    fix i
    assume i: "i \<in> \<S> \<setminus> \<S>\<S>"
    with R53 kn0 beta_ge0 [of i] show "0 \<le> 1 / beta i \<and> 1 / beta i \<le> (real k)\<^sup>2"
      by (force simp: R53 divide_simps mult.commute)
  qed
  then have "(\<Prod>i\<in>\<S>\<setminus>\<S>\<S>. 1 / beta i) \<le> real k ^ (2 * card(\<S>\<setminus>\<S>\<S>))"
    by (simp add: power_mult)
  also have "\<dots> = real k powr (2 * card(\<S>\<setminus>\<S>\<S>))"
    by (metis kn0 of_nat_0_less_iff powr_realpow)
  also have "\<dots> \<le> k powr (2 * 3 * \<epsilon> powr (1/4) * k)"
    using X75 kn0 by (intro powr_mono; linarith) 
  also have "\<dots> \<le> exp (6 * \<epsilon> powr (1/4) * k * ln k)"
    by (simp add: powr_def)
  also have "\<dots> = 2 powr -ok_fun_74 k"
    by (simp add: ok_fun_74_def powr_def)
  finally have "(\<Prod>i\<in>\<S>\<setminus>\<S>\<S>. 1 / beta i) \<le> 2 powr -ok_fun_74 k" .
  then have A: "(\<Prod>i\<in>\<S>\<setminus>\<S>\<S>. beta i) \<ge> 2 powr ok_fun_74 k"
    using prod_beta_gt0[of "\<S>\<setminus>\<S>\<S>"]
    by (simp add: powr_minus prod_dividef mult.commute divide_simps)
\<comment> \<open>bounding the moderate steps\<close>
  have "(\<Prod>i\<in>\<S>\<S>. 1 / beta i) \<le> bigbeta powr (- (card \<S>\<S>))"
  proof (cases "\<S>\<S> = {}")
    case True
    with bigbeta01 show ?thesis
      by fastforce
  next
    case False
    then have "card \<S>\<S> > 0"
      using \<open>finite \<S>\<S>\<close> card_0_eq by blast
    have "(\<Prod>i\<in>\<S>\<S>. 1 / beta i) powr (1 / card \<S>\<S>) \<le> (\<Sum>i\<in>\<S>\<S>. 1 / beta i / card \<S>\<S>)"
    proof (rule arith_geom_mean [OF \<open>finite \<S>\<S>\<close> \<open>\<S>\<S> \<noteq> {}\<close>])
      show "\<And>i. i \<in> \<S>\<S> \<Longrightarrow> 0 \<le> 1 / beta i"
        by (simp add: beta_ge0)
    qed
    then have "((\<Prod>i\<in>\<S>\<S>. 1 / beta i) powr (1 / card \<S>\<S>)) powr (card \<S>\<S>) 
          \<le> (\<Sum>i\<in>\<S>\<S>. 1 / beta i / card \<S>\<S>) powr (card \<S>\<S>)"
      using powr_mono2 by auto
    with \<open>\<S>\<S> \<noteq> {}\<close> 
    have "(\<Prod>i\<in>\<S>\<S>. 1 / beta i) \<le> (\<Sum>i\<in>\<S>\<S>. 1 / beta i / card \<S>\<S>) powr (card \<S>\<S>)"
      by (simp add: powr_powr beta_ge0 prod_nonneg)
    also have "\<dots> \<le> (1 / (card \<S>\<S>) * (\<Sum>i\<in>\<S>\<S>. 1 / beta i)) powr (card \<S>\<S>)"
      using \<open>card \<S>\<S> > 0\<close> by (simp add: field_simps sum_divide_distrib)
    also have "\<dots> \<le> bigbeta powr (- (card \<S>\<S>))"
      using \<open>\<S>\<S> \<noteq> {}\<close> \<open>card \<S>\<S> > 0\<close> 
      by (simp add: bigbeta_def field_simps powr_minus powr_divide beta_ge0 sum_nonneg flip: \<S>\<S>_def)
    finally show ?thesis .
  qed
  then have B: "(\<Prod>i\<in>\<S>\<S>. beta i) \<ge> bigbeta powr (card \<S>\<S>)"
    using \<open>\<S>\<S> \<subseteq> \<S>\<close> prod_beta_gt0[of "\<S>\<S>"] bigbeta01
    by (simp add: powr_minus prod_dividef mult.commute divide_simps)
  have "2 powr ok_fun_74 k * bigbeta powr card \<S> \<le> 2 powr ok_fun_74 k * bigbeta powr card \<S>\<S>"
    using bigbeta01 big53 card_SSS by (simp add: powr_mono')
  also have "\<dots> \<le> (\<Prod>i\<in>\<S>\<setminus>\<S>\<S>. beta i) * (\<Prod>i\<in>\<S>\<S>. beta i)"
    using beta_ge0 by (intro mult_mono A B) (auto simp: prod_nonneg)
  also have "\<dots> = (\<Prod>i\<in>\<S>. beta i)"
    by (metis \<open>\<S>\<S> \<subseteq> \<S>\<close> \<open>finite \<S>\<close> prod.subset_diff)
  finally have "2 powr ok_fun_74 k * bigbeta powr real (card \<S>) \<le> prod (beta) \<S>" .
  with bigbeta01 show ?thesis
    by (simp add: "*" powr_realpow)
qed  

subsection \<open>Observation 7.7\<close>

lemma X_7_7:
  assumes i: "i \<in> Step_class {dreg_step}"
  defines "q \<equiv> \<epsilon> powr (-1/2) * alpha (hgt (pseq i))"
  shows "pseq (Suc i) - pseq i \<ge> card (Xseq i \<setminus> Xseq (Suc i)) / card (Xseq (Suc i)) * q \<and> card (Xseq (Suc i)) > 0"
proof -
  have finX: "finite (Xseq i)" for i
    using finite_Xseq by blast
  define Y where "Y \<equiv> Yseq"
  have "Xseq (Suc i) = {x \<in> Xseq i. red_dense (Y i) (red_density (Xseq i) (Y i)) x}"   
   and Y: "Y (Suc i) = Y i"
    using i
    by (simp_all add: step_kind_defs next_state_def X_degree_reg_def degree_reg_def 
        Y_def split: if_split_asm prod.split_asm)
  then have Xseq: "Xseq (Suc i) = {x \<in> Xseq i. card (Neighbours Red x \<inter> Y i) \<ge> (pseq i - q) * card (Y i)}"
    by (simp add: red_dense_def q_def pseq_def Y_def)
  have Xsub[simp]: "Xseq (Suc i) \<subseteq> Xseq i"
    using Xseq_Suc_subset by blast
  then have card_le: "card (Xseq (Suc i)) \<le> card (Xseq i)"
    by (simp add: card_mono finX)
  have [simp]: "disjnt (Xseq i) (Y i)"
    using Xseq_Yseq_disjnt Y_def by blast
  have Xnon0: "card (Xseq i) > 0" and Ynon0: "card (Y i) > 0"
    using i by (simp_all add: Y_def Xseq_gt0 Yseq_gt0 Step_class_def)
  have "alpha (hgt (pseq i)) > 0"
    by (simp add: alpha_gt0 kn0 hgt_gt0)
  with kn0 have "q > 0"
    by (smt (verit) q_def eps_gt0 mult_pos_pos powr_gt_zero)
  have Xdif: "Xseq i \<setminus> Xseq (Suc i) = {x \<in> Xseq i. card (Neighbours Red x \<inter> Y i) < (pseq i - q) * card (Y i)}"
    using Xseq by force
  have disYX: "disjnt (Y i) (Xseq i \<setminus> Xseq (Suc i))"
    by (metis Diff_subset \<open>disjnt (Xseq i) (Y i)\<close> disjnt_subset2 disjnt_sym)
  have "edge_card Red (Y i) (Xseq i \<setminus> Xseq (Suc i)) 
      = (\<Sum>x \<in> Xseq i \<setminus> Xseq (Suc i). real (card (Neighbours Red x \<inter> Y i)))"
    using edge_card_eq_sum_Neighbours [OF _ _ disYX] finX Red_E by simp
  also have "\<dots> \<le> (\<Sum>x \<in> Xseq i \<setminus> Xseq (Suc i). (pseq i - q) * card (Y i))"
    by (smt (verit, del_insts) Xdif mem_Collect_eq sum_mono)
  finally have A: "edge_card Red (Xseq i \<setminus> Xseq (Suc i)) (Y i) \<le> card (Xseq i \<setminus> Xseq (Suc i)) * (pseq i - q) * card (Y i)" 
    by (simp add: edge_card_commute)
  then have False if "Xseq (Suc i) = {}"
    using \<open>q>0\<close> Xnon0 Ynon0 that  by (simp add: edge_card_eq_pee Y_def mult_le_0_iff)
  then have XSnon0: "card (Xseq (Suc i)) > 0"
    using card_gt_0_iff finX by blast 
  have "pseq i * card (Xseq i) * real (card (Y i)) - edge_card Red (Xseq (Suc i)) (Y i)
     \<le> card (Xseq i \<setminus> Xseq (Suc i)) * (pseq i - q) * card (Y i)"
    by (metis A edge_card_eq_pee edge_card_mono Y_def Xsub \<open>disjnt (Xseq i) (Y i)\<close> edge_card_diff finX of_nat_diff)
  moreover have "real (card (Xseq (Suc i))) \<le> real (card (Xseq i))"
    using Xsub by (simp add: card_le)
  ultimately have \<section>: "edge_card Red (Xseq (Suc i)) (Y i) \<ge> pseq i * card (Xseq (Suc i)) * card (Y i) + card (Xseq i \<setminus> Xseq (Suc i)) * q * card (Y i)"
    using Xnon0 
    by (smt (verit, del_insts) Xsub card_Diff_subset card_gt_0_iff card_le left_diff_distrib finite_subset mult_of_nat_commute of_nat_diff) 
  have "edge_card Red (Xseq (Suc i)) (Y i) / (card (Xseq (Suc i)) * card (Y i)) \<ge> pseq i + card (Xseq i \<setminus> Xseq (Suc i)) * q / card (Xseq (Suc i))"
    using divide_right_mono [OF \<section>, of "card (Xseq (Suc i)) * card (Y i)"] XSnon0 Ynon0
    by (simp add: add_divide_distrib split: if_split_asm)
  moreover have "pseq (Suc i) = real (edge_card Red (Xseq (Suc i)) (Y i)) / (real (card (Y i)) * real (card (Xseq (Suc i))))"
    using Y by (simp add: pseq_def gen_density_def Y_def)
  ultimately show ?thesis
    by (simp add: algebra_simps XSnon0)
qed

end

subsection \<open>Lemma 7.8\<close>

definition "Big_X_7_8 \<equiv> \<lambda>k. k\<ge>2 \<and> eps k powr (1/2) / k \<ge> 2 / k^2"

lemma Big_X_7_8: "\<forall>\<^sup>\<infinity>k. Big_X_7_8 k"
  unfolding eps_def Big_X_7_8_def eventually_conj_iff eps_def
  by (intro conjI; real_asymp)

lemma (in Book) X_7_8:
  assumes big: "Big_X_7_8 k" 
    and i: "i \<in> Step_class {dreg_step}"
  shows "card (Xseq (Suc i)) \<ge> card (Xseq i) / k^2"
proof -
  define q where "q \<equiv> \<epsilon> powr (-1/2) * alpha (hgt (pseq i))"
  have "k>0" \<open>k\<ge>2\<close> using big by (auto simp: Big_X_7_8_def)
  have "2 / k^2 \<le> \<epsilon> powr (1/2) / k"
    using big by (auto simp: Big_X_7_8_def)
  also have "\<dots> \<le> q"
    using kn0 eps_gt0 Red_5_7a [of "pseq i"]
    by (simp add: q_def powr_minus divide_simps flip: powr_add)
  finally have q_ge: "q \<ge> 2 / k^2" .
  define Y where "Y \<equiv> Yseq"
  have "Xseq (Suc i) = {x \<in> Xseq i. red_dense (Y i) (red_density (Xseq i) (Y i)) x}"   
   and Y: "Y (Suc i) = Y i"
    using i
    by (simp_all add: step_kind_defs next_state_def X_degree_reg_def degree_reg_def 
        Y_def split: if_split_asm prod.split_asm)
  have XSnon0: "card (Xseq (Suc i)) > 0"
    using X_7_7 kn0 assms by simp
  have finX: "finite (Xseq i)" for i
    using finite_Xseq by blast
  have Xsub[simp]: "Xseq (Suc i) \<subseteq> Xseq i"
    using Xseq_Suc_subset by blast
  then have card_le: "card (Xseq (Suc i)) \<le> card (Xseq i)"
    by (simp add: card_mono finX)
  have "2 \<le> (real k)\<^sup>2"
    by (metis of_nat_numeral \<open>2 \<le> k\<close> of_nat_power_le_of_nat_cancel_iff self_le_ge2_pow)
  then have 2: "2 / (real k ^ 2 + 2) \<ge> 1 / k^2"
    by (simp add: divide_simps)
  have "q * card (Xseq i \<setminus> Xseq (Suc i)) / card (Xseq (Suc i)) \<le> pseq (Suc i) - pseq i"
    using X_7_7 \<mu>01 kn0 assms by (simp add: q_def mult_of_nat_commute)
  also have "\<dots> \<le> 1"
    by (smt (verit) pee_ge0 pee_le1)
  finally have "q * card (Xseq i \<setminus> Xseq (Suc i)) \<le> card (Xseq (Suc i))" 
    using XSnon0 by auto
  with q_ge have "card (Xseq (Suc i)) \<ge> (2 / k^2) * card (Xseq i \<setminus> Xseq (Suc i))"
    by (smt (verit, best) mult_right_mono of_nat_0_le_iff)
  then have "card (Xseq (Suc i)) * (1 + 2/k^2) \<ge> (2/k^2) * card (Xseq i)"
    by (simp add: card_Diff_subset finX card_le diff_divide_distrib field_simps)
  then have "card (Xseq (Suc i)) \<ge> (2/(real k ^ 2 + 2)) * card (Xseq i)"
    using kn0 add_nonneg_nonneg[of "real k^2" 2]
    by (simp del: add_nonneg_nonneg add: divide_simps split: if_split_asm)
  then show ?thesis
    using mult_right_mono [OF 2, of "card (Xseq i)"] by simp
qed

subsection \<open>Lemma 7.9\<close>

definition "Big_X_7_9 \<equiv> \<lambda>k. ((1 + eps k) powr (eps k powr (-1/4) + 1) - 1) / eps k \<le> 2 * eps k powr (-1/4)
   \<and> k\<ge>2 \<and> eps k powr (1/2) / k \<ge> 2 / k^2"

lemma Big_X_7_9: "\<forall>\<^sup>\<infinity>k. Big_X_7_9 k"
  unfolding eps_def Big_X_7_9_def eventually_conj_iff eps_def
  by (intro conjI; real_asymp)

lemma one_plus_powr_le:
  fixes p::real
  assumes "0\<le>p" "p\<le>1" "x\<ge>0"  
  shows "(1+x) powr p - 1 \<le> x*p"
proof -
  define f where "f \<equiv> \<lambda>x. x*p - ((1+x) powr p - 1)"
  have "0 \<le> f 0"
    by (simp add: f_def)
  also have "\<dots> \<le> f x"
  proof (intro DERIV_nonneg_imp_nondecreasing[of concl: f] exI conjI assms)
    fix y::real
    assume y: "0 \<le> y" "y \<le> x"
    show "(f has_real_derivative p - (1+y)powr (p-1) * p) (at y)"
      unfolding f_def using assms y by (intro derivative_eq_intros | simp)+
    show "p - (1+y)powr (p-1) * p \<ge> 0"
      using y assms less_eq_real_def powr_less_one by fastforce
  qed
  finally show ?thesis
    by (simp add: f_def)
qed

lemma (in Book) X_7_9:
  assumes i: "i \<in> Step_class {dreg_step}" and big: "Big_X_7_9 k"
  defines "hp \<equiv> \<lambda>i. hgt (pseq i)"
  assumes "pseq i \<ge> p0" and hgt: "hp (Suc i) \<le> hp i + \<epsilon> powr (-1/4)"
  shows "card (Xseq (Suc i)) \<ge> (1 - 2 * \<epsilon> powr (1/4)) * card (Xseq i)"
proof -
  have k: "k\<ge>2" "\<epsilon> powr (1/2) / k \<ge> 2 / k^2" 
    using big by (auto simp: Big_X_7_9_def)
  let ?q = "\<epsilon> powr (-1/2) * alpha (hp i)"
  have "k>0" using k by auto
  have Xsub[simp]: "Xseq (Suc i) \<subseteq> Xseq i"
    using Xseq_Suc_subset by blast
  have finX: "finite (Xseq i)" for i
    using finite_Xseq by blast
  then have card_le: "card (Xseq (Suc i)) \<le> card (Xseq i)"
    by (simp add: card_mono finX)
  have XSnon0: "card (Xseq (Suc i)) > 0"
    using X_7_7 \<open>0 < k\<close> i by blast
  have "card (Xseq i \<setminus> Xseq (Suc i)) / card (Xseq (Suc i)) * ?q \<le> pseq (Suc i) - pseq i"
    using X_7_7 i k hp_def by auto
  also have "\<dots> \<le> 2 * \<epsilon> powr (-1/4) * alpha (hp i)"
  proof -
    have hgt_le: "hp i \<le> hp (Suc i)" 
      using Y_6_5_DegreeReg \<open>0 < k\<close> i hp_def by blast
    have A: "pseq (Suc i) \<le> qfun (hp (Suc i))"
      by (simp add: \<open>0 < k\<close> hp_def hgt_works)
    have B: "qfun (hp i - 1) \<le> pseq i"
      using hgt_Least [of "hp i - 1" "pseq i"] \<open>pseq i \<ge> p0\<close> by (force simp: hp_def)
    have "pseq (Suc i) - pseq i \<le> qfun (hp (Suc i)) - qfun (hp i - 1)"
      using A B by auto
    also have "\<dots> = ((1 + \<epsilon>) ^ (Suc (hp i - 1 + hp (Suc i)) - hp i) -
                      (1 + \<epsilon>) ^ (hp i - 1))  /  k"
      using kn0 eps_gt0 hgt_le \<open>pseq i \<ge> p0\<close> hgt_gt0 [of k]
      by (simp add: hp_def qfun_eq Suc_diff_eq_diff_pred hgt_gt0 diff_divide_distrib)
    also have "\<dots> = alpha (hp i) / \<epsilon> * ((1 + \<epsilon>) ^ (1 + hp (Suc i) - hp i) - 1)"
      using kn0 hgt_le hgt_gt0 
      by (simp add: hp_def alpha_eq right_diff_distrib flip: diff_divide_distrib power_add)
    also have "\<dots> \<le> 2 * \<epsilon> powr (-1/4) * alpha (hp i)"
    proof -
      have "((1 + \<epsilon>) ^ (1 + hp (Suc i) - hp i) - 1)  / \<epsilon> \<le> ((1 + \<epsilon>) powr (\<epsilon> powr (-1/4) + 1) - 1) / \<epsilon>"
        using hgt eps_ge0 hgt_le powr_mono_both by (force simp flip: powr_realpow intro: divide_right_mono)
      also have "\<dots> \<le> 2 * \<epsilon> powr (-1/4)"
        using big by (meson Big_X_7_9_def)
      finally have *: "((1 + \<epsilon>) ^ (1 + hp (Suc i) - hp i) - 1) / \<epsilon> \<le> 2 * \<epsilon> powr (-1/4)" .
      show ?thesis
        using mult_left_mono [OF *, of "alpha (hp i)"]
        by (smt (verit) alpha_ge0 mult.commute times_divide_eq_right)
    qed
    finally show ?thesis .
  qed
  finally have 29: "card (Xseq i \<setminus> Xseq (Suc i)) / card (Xseq (Suc i)) * ?q \<le> 2 * \<epsilon> powr (-1/4) * alpha (hp i)" .
  moreover have "alpha (hp i) > 0"
    unfolding hp_def
    by (smt (verit, ccfv_SIG) eps_gt0 \<open>0 < k\<close> alpha_ge divide_le_0_iff hgt_gt0 of_nat_0_less_iff)
  ultimately have "card (Xseq i \<setminus> Xseq (Suc i)) / card (Xseq (Suc i)) * \<epsilon> powr (-1/2) \<le> 2 * \<epsilon> powr (-1/4)" 
    using mult_le_cancel_right by fastforce
  then have "card (Xseq i \<setminus> Xseq (Suc i)) / card (Xseq (Suc i)) \<le> 2 * \<epsilon> powr (-1/4) * \<epsilon> powr (1/2)" 
    using \<open>0 < k\<close> eps_gt0
    by (force simp: powr_minus divide_simps mult.commute mult_less_0_iff)
  then have "card (Xseq i \<setminus> Xseq (Suc i)) \<le> 2 * \<epsilon> powr (1/4) * card (Xseq (Suc i))"
    using XSnon0 by (simp add: field_simps flip: powr_add)
  also have "\<dots> \<le> 2 * \<epsilon> powr (1/4) * card (Xseq i)"
    by (simp add: card_le mult_mono')
  finally show ?thesis
    by (simp add: card_Diff_subset finX card_le algebra_simps)
qed

subsection \<open>Lemma 7.10\<close>
 
definition "Big_X_7_10 \<equiv> \<lambda>\<mu> l. Big_X_7_5 \<mu> l \<and> Big_Red_5_3 \<mu> l"

text \<open>establishing the size requirements for 7.10\<close>
lemma Big_X_7_10:
  assumes "0<\<mu>0" "\<mu>1<1" 
  shows "\<forall>\<^sup>\<infinity>l. \<forall>\<mu>. \<mu> \<in> {\<mu>0..\<mu>1} \<longrightarrow> Big_X_7_10 \<mu> l"
  using Big_X_7_10_def Big_X_7_4 Big_X_7_4_def assms by force


lemma (in Book) X_7_10:
  defines "\<R> \<equiv> Step_class {red_step}"
  defines "\<S> \<equiv> Step_class {dboost_step}"
  defines "h \<equiv> \<lambda>i. real (hgt (pseq i))"
  defines "C \<equiv> {i. h i \<ge> h (i-1) + \<epsilon> powr (-1/4)}"
  assumes big: "Big_X_7_10 \<mu> l" 
  shows "card ((\<R>\<union>\<S>) \<inter> C) \<le> 3 * \<epsilon> powr (1/4) * k"
proof -
  define \<D> where "\<D> \<equiv> Step_class {dreg_step}"
  define \<B> where "\<B> \<equiv> Step_class {bblue_step}"
  have hub: "Big_height_upper_bound k"
    and 16: "k\<ge>16" (*for Y_6_5_Red*)
    and ok_le_k: "ok_fun_26 k - ok_fun_28 k \<le> k"
    and bigR53: "Big_Red_5_3 \<mu> l"
    using big l_le_k by (auto simp: Big_X_7_5_def Big_X_7_10_def)
  have "\<R>\<union>\<S> \<subseteq> {..<halted_point} \<setminus> \<D> \<setminus> \<B>" and BmD: "\<B> \<subseteq> {..<halted_point} \<setminus> \<D>"
    using halted_point_minimal'
    by (fastforce simp: \<R>_def \<S>_def \<D>_def \<B>_def Step_class_def)+
  then have RS_eq: "\<R>\<union>\<S> = {..<halted_point} \<setminus> \<D> - \<B>"
    using halted_point_minimal Step_class_cases by (auto simp: \<R>_def \<S>_def \<D>_def \<B>_def)
  obtain 26: "(\<Sum>i\<in>{..<halted_point} \<setminus> \<D>. h (Suc i) - h (i-1)) \<le> ok_fun_26 k"
     and 28: "ok_fun_28 k \<le> (\<Sum>i \<in> \<B>. h(Suc i) - h(i-1))"
    using X_26_and_28 big unfolding \<B>_def \<D>_def h_def Big_X_7_10_def by blast
  have "(\<Sum>i\<in>\<R>\<union>\<S>. h (Suc i) - h (i-1)) = (\<Sum>i\<in>{..<halted_point} \<setminus> \<D>. h (Suc i) - h (i-1)) - (\<Sum>i \<in> \<B>. h(Suc i) - h(i-1))"
    unfolding RS_eq by (intro sum_diff BmD) auto
  also have "\<dots> \<le> ok_fun_26 k - ok_fun_28 k"
    using 26 28 by linarith
  finally have *: "(\<Sum>i\<in>\<R>\<union>\<S>. h (Suc i) - h (i-1)) \<le> ok_fun_26 k - ok_fun_28 k" .

  have [simp]: "finite \<R>" "finite \<S>"
  using finite_components by (auto simp: \<R>_def \<S>_def)
  have h_ge_0_if_S: "h(Suc i) - h(i-1) \<ge> 0" if "i \<in> \<S>" for i
  proof -
    have *: "hgt (pseq i) \<le> hgt (pseq (Suc i))"
      using bigR53 Y_6_5_dbooSt that unfolding \<S>_def by blast
    obtain "i-1 \<in> \<D>" "i>0"
      using that \<open>i\<in>\<S>\<close> dreg_before_step1[of i] dreg_before_gt0[of i]
      by (force simp: \<S>_def \<D>_def Step_class_insert_NO_MATCH)
    then have "hgt (pseq (i-1)) \<le> hgt (pseq i)"
      using that kn0 by (metis Suc_diff_1 Y_6_5_DegreeReg \<D>_def)
    with * show "0 \<le> h(Suc i) - h(i-1)"
      using kn0 unfolding h_def by linarith
  qed

  have "card ((\<R>\<union>\<S>) \<inter> C) * \<epsilon> powr (-1/4) + real (card \<R>) * (-2)
      = (\<Sum>i \<in> \<R>\<union>\<S>. if i\<in>C then \<epsilon> powr (-1/4) else 0) + (\<Sum>i \<in> \<R>\<union>\<S>. if i\<in>\<R> then -2 else 0)"
    by (simp add: Int_commute Int_left_commute flip: sum.inter_restrict)
  also have "\<dots> = (\<Sum>i \<in> \<R>\<union>\<S>. (if i\<in>C then \<epsilon> powr (-1/4) else 0) + (if i\<in>\<R> then -2 else 0))"
    by (simp add: sum.distrib)
  also have "\<dots> \<le> (\<Sum>i \<in> \<R>\<union>\<S>. h(Suc i) - h(i-1))"
  proof (rule sum_mono)
    fix i :: nat
    assume i: "i \<in> \<R>\<union>\<S>"
    with i dreg_before_step1 dreg_before_gt0 have D: "i-1 \<in> \<D>" "i>0"     
      by (force simp: \<S>_def \<R>_def \<D>_def dreg_before_step Step_class_def)+
    then have *: "hgt (pseq (i-1)) \<le> hgt (pseq i)"
      by (metis Suc_diff_1 Y_6_5_DegreeReg \<D>_def)
    show "(if i\<in>C then \<epsilon> powr (-1/4) else 0) + (if i\<in>\<R> then - 2 else 0) \<le> h (Suc i) - h (i-1)"
    proof (cases "i\<in>\<R>")
      case True
      then have "h i - 2 \<le> h (Suc i)"
        using Y_6_5_Red[of i] 16 by (force simp: algebra_simps \<R>_def h_def)
      with * True show ?thesis
        by (simp add: h_def C_def)
    next
      case False
      with i have "i\<in>\<S>" by blast
      show ?thesis
      proof (cases "i\<in>C")
        case True
        then have "h (i - Suc 0) + \<epsilon> powr (-1/4) \<le> h i"
          by (simp add: C_def)
        then show ?thesis
          using * i \<open>i\<notin>\<R>\<close> kn0 bigR53 Y_6_5_dbooSt by (force simp: h_def \<S>_def)
      qed (use \<open>i\<notin>\<R>\<close> \<open>i\<in>\<S>\<close> h_ge_0_if_S in auto)
    qed
  qed
  also have "\<dots> \<le> k"
    using * ok_le_k
    by linarith
  finally have "card ((\<R>\<union>\<S>) \<inter> C) * \<epsilon> powr (-1/4) - 2 * card \<R> \<le> k"
    by linarith 
  moreover have "card \<R> \<le> k"
    by (metis \<R>_def nless_le red_step_limit)
  ultimately have "card ((\<R>\<union>\<S>) \<inter> C) * \<epsilon> powr (-1/4) \<le> 3 * k"
    by linarith
  with eps_gt0 show ?thesis
    by (simp add: powr_minus divide_simps mult.commute split: if_split_asm)
qed


subsection \<open>Lemma 7.11\<close>

(*Big_X_7_5 is used (rather than the conclusion) because that theorem is split in two*)

definition "Big_X_7_11_inequalities \<equiv> \<lambda>k. 
              eps k * eps k powr (-1/4) \<le> (1 + eps k) ^ (2 * nat \<lfloor>eps k powr (-1/4)\<rfloor>) - 1
            \<and> k \<ge> 2 * eps k powr (-1/2) * k powr (3/4)
            \<and> ((1 + eps k) * (1 + eps k) powr (2 * eps k powr (-1/4))) \<le> 2
            \<and> (1 + eps k) ^ (nat \<lfloor>2 * eps k powr (-1/4)\<rfloor> + nat \<lfloor>2 * eps k powr (-1/2)\<rfloor> - 1) \<le> 2"

definition "Big_X_7_11 \<equiv> 
      \<lambda>\<mu> l. Big_X_7_5 \<mu> l \<and> Big_Red_5_3 \<mu> l \<and> Big_Y_6_5_Bblue l
          \<and> (\<forall>k. l\<le>k \<longrightarrow> Big_X_7_11_inequalities k)"

text \<open>establishing the size requirements for 7.11\<close>
lemma Big_X_7_11:
  assumes "0<\<mu>0" "\<mu>1<1" 
  shows "\<forall>\<^sup>\<infinity>l. \<forall>\<mu>. \<mu> \<in> {\<mu>0..\<mu>1} \<longrightarrow> Big_X_7_11 \<mu> l"
  using assms Big_Red_5_3 Big_X_7_5 Big_Y_6_5_Bblue
  unfolding Big_X_7_11_def Big_X_7_11_inequalities_def eventually_conj_iff all_imp_conj_distrib eps_def
  apply (simp add: eventually_conj_iff all_imp_conj_distrib)  
  apply (intro conjI strip eventually_all_geI0 eventually_all_ge_at_top; real_asymp)
  done

lemma (in Book) X_7_11:
  defines "\<R> \<equiv> Step_class {red_step}"
  defines "\<S> \<equiv> Step_class {dboost_step}"
  defines "C \<equiv> {i. pseq i \<ge> pseq (i-1) + \<epsilon> powr (-1/4) * alpha 1 \<and> pseq (i-1) \<le> p0}"
  assumes big: "Big_X_7_11 \<mu> l"
  shows "card ((\<R>\<union>\<S>) \<inter> C) \<le> 4 * \<epsilon> powr (1/4) * k"
proof -
  define qstar where "qstar \<equiv> p0 + \<epsilon> powr (-1/4) * alpha 1"
  define pstar where "pstar \<equiv> \<lambda>i. min (pseq i) qstar"
  define \<D> where "\<D> \<equiv> Step_class {dreg_step}"
  define \<B> where "\<B> \<equiv> Step_class {bblue_step}"
  have big_x75: "Big_X_7_5 \<mu> l"  
    and 711: "\<epsilon> * \<epsilon> powr (-1/4) \<le> (1 + \<epsilon>) ^ (2 * nat \<lfloor>\<epsilon> powr (-1/4)\<rfloor>) - 1"
    and big34: "k \<ge> 2 * \<epsilon> powr (-1/2) * k powr (3/4)"
    and le2: "((1 + \<epsilon>) * (1 + \<epsilon>) powr (2 * \<epsilon> powr (-1/4))) \<le> 2"
             "(1 + \<epsilon>) ^ (nat \<lfloor>2 * \<epsilon> powr (-1/4)\<rfloor> + nat \<lfloor>2 * \<epsilon> powr (-1/2)\<rfloor> - 1) \<le> 2"
    and bigY65B: "Big_Y_6_5_Bblue l"
    and R53:  "\<And>i. i \<in> \<S> \<Longrightarrow> pseq (Suc i) \<ge> pseq i"
    using big l_le_k
    by (auto simp: Red_5_3 Big_X_7_11_def Big_X_7_11_inequalities_def \<S>_def)
  then have Y_6_5_B: "\<And>i. i \<in> \<B> \<Longrightarrow> hgt (pseq (Suc i)) \<ge> hgt (pseq (i-1)) - 2 * \<epsilon> powr (-1/2)"
    using bigY65B Y_6_5_Bblue unfolding \<B>_def by blast 
  have big41: "Big_Blue_4_1 \<mu> l"
    and hub: "Big_height_upper_bound k"
    and 16: "k\<ge>16" (*for Y_6_5_Red*)
    and ok_le_k: "ok_fun_26 k - ok_fun_28 k \<le> k"
    using big_x75 l_le_k by (auto simp: Big_X_7_5_def)
  have oddset: "{..<halted_point} \<setminus> \<D> = {i \<in> {..<halted_point}. odd i}" 
    using step_odd step_even not_halted_even_dreg halted_point_minimal by (auto simp: \<D>_def)
  have [simp]: "finite \<R>" "finite \<B>" "finite \<S>"
    using finite_components by (auto simp: \<R>_def \<B>_def \<S>_def)
  have [simp]: "\<R> \<inter> \<S> = {}" and [simp]: "(\<R> \<union> \<S>) \<inter> \<B> = {}"
    by (simp_all add: \<R>_def \<S>_def \<B>_def Step_class_def disjoint_iff)

  have hgt_qstar_le: "hgt qstar \<le> 2 * \<epsilon> powr (-1/4)"
  proof (intro real_hgt_Least)
    show "0 < 2 * nat \<lfloor>\<epsilon> powr (-1/4)\<rfloor>"
      using kn0 eps_gt0 by (simp add: eps_le1 powr_le1 powr_minus_divide)
    show "qstar \<le> qfun (2 * nat \<lfloor>\<epsilon> powr (-1/4)\<rfloor>)"
      using kn0 711
      by (simp add: qstar_def alpha_def qfun_eq divide_right_mono mult.commute)
  qed auto
  then have "((1 + \<epsilon>) * (1 + \<epsilon>) ^ hgt qstar) \<le> ((1 + \<epsilon>) * (1 + \<epsilon>) powr (2 * \<epsilon> powr (-1/4)))"
    by (smt (verit) eps_ge0 mult_left_mono powr_mono powr_realpow)
  also have "((1 + \<epsilon>) * (1 + \<epsilon>) powr (2 * \<epsilon> powr (-1/4))) \<le> 2"
    using le2 by simp
  finally have "(1 + \<epsilon>) * (1 + \<epsilon>) ^ hgt qstar \<le> 2" .
  moreover have "card \<R> \<le> k"
    by (simp add: \<R>_def less_imp_le red_step_limit)
  ultimately have \<section>: "((1 + \<epsilon>) * (1 + \<epsilon>) ^ hgt qstar) * card \<R> \<le> 2 * real k"
    by (intro mult_mono) auto
  have "- 2 * alpha 1 * k \<le> - alpha (hgt qstar + 2) * card \<R>"
    using mult_right_mono_neg [OF \<section>, of "- \<epsilon>"] eps_ge0 
    by (simp add: alpha_eq divide_simps mult_ac)
  also have "\<dots> \<le> (\<Sum>i\<in>\<R>. pstar (Suc i) - pstar i)"
  proof -
    { fix i
      assume "i \<in> \<R>"
      have "- alpha (hgt qstar + 2) \<le> pstar (Suc i) - pstar i"
      proof (cases "hgt (pseq i) > hgt qstar + 2")
        case True
        then have "hgt (pseq (Suc i)) > hgt qstar"
          using Y_6_5_Red 16 \<open>i \<in> \<R>\<close> by (force simp: \<R>_def)
        then have "pstar (Suc i) = pstar i"
          using True hgt_mono' pstar_def by fastforce
        then show ?thesis
          by (simp add: alpha_ge0)
      next
        case False
        with \<open>i \<in> \<R>\<close> show ?thesis
          unfolding pstar_def \<R>_def
          by (smt (verit, del_insts) Y_6_4_Red alpha_ge0 alpha_mono hgt_gt0 linorder_not_less)
      qed
    }
    then show ?thesis
      by (smt (verit, ccfv_SIG) mult_of_nat_commute sum_constant sum_mono)
  qed
  finally have "- 2 * alpha 1 * k \<le> (\<Sum>i\<in>\<R>. pstar (Suc i) - pstar i)" .
  moreover have "0 \<le> (\<Sum>i\<in>\<S>. pstar (Suc i) - pstar i)"
    using R53 by (intro sum_nonneg) (force simp: pstar_def)
  ultimately have RS_half: "- 2 * alpha 1 * k \<le> (\<Sum>i\<in>\<R>\<union>\<S>. pstar (Suc i) - pstar i)"
    by (simp add: sum.union_disjoint)

  let ?e12 = "\<epsilon> powr (-1/2)"
  define h' where "h' \<equiv> hgt qstar + nat \<lfloor>2 * ?e12\<rfloor>"
  have "- alpha 1 * k \<le> -2 * ?e12 * alpha 1 * k powr (3/4)"
    using mult_right_mono_neg [OF big34, of "- alpha 1"] alpha_ge0 [of 1]
    by (simp add: mult_ac)
  also have "\<dots> \<le> -?e12 * alpha (h') * card \<B>"
  proof -
    have "card \<B> \<le> l powr (3/4)"
      using big41 bblue_step_limit by (simp add: \<B>_def)
    also have "\<dots> \<le> k powr (3/4)"
      by (simp add: powr_mono2 l_le_k)
    finally have 1: "card \<B> \<le> k powr (3/4)" .
    have "alpha (h') \<le> alpha (nat \<lfloor>2 * \<epsilon> powr (-1/4)\<rfloor> + nat \<lfloor>2 * ?e12\<rfloor>)"
    proof (rule alpha_mono)
      show "h' \<le> nat \<lfloor>2 * \<epsilon> powr (-1/4)\<rfloor> + nat \<lfloor>2 * ?e12\<rfloor>"
        using h'_def hgt_qstar_le le_nat_floor by auto
    qed (simp add: hgt_gt0 h'_def)
    also have "\<dots> \<le> 2 * alpha 1"
    proof -
      have *: "(1 + \<epsilon>) ^ (nat \<lfloor>2 * \<epsilon> powr (-1/4)\<rfloor> + nat \<lfloor>2 * ?e12\<rfloor> - 1) \<le> 2"
        using le2 by simp
      have "1 \<le> 2 * \<epsilon> powr (-1/4)"
        by (smt (verit) hgt_qstar_le Suc_leI divide_minus_left hgt_gt0 numeral_nat(7) real_of_nat_ge_one_iff)
      then show ?thesis
        using mult_right_mono [OF *, of "\<epsilon>"] eps_ge0 
        by (simp add: alpha_eq hgt_gt0 divide_right_mono mult.commute)
    qed
    finally have 2: "2 * alpha 1 \<ge> alpha (h')" .
    show ?thesis
      using mult_right_mono_neg [OF mult_mono [OF 1 2], of "-?e12"] alpha_ge0 by (simp add: mult_ac)
  qed
  also have "\<dots> \<le> (\<Sum>i\<in>\<B>. pstar (Suc i) - pstar (i-1))"
  proof -
    { fix i
      assume "i \<in> \<B>"
      have "-?e12 * alpha (h') \<le> pstar (Suc i) - pstar (i-1)"
      proof (cases "hgt (pseq (i-1)) > hgt qstar + 2 * ?e12")
        case True
        then have "hgt (pseq (Suc i)) > hgt qstar"
          using Y_6_5_B \<open>i \<in> \<B>\<close> by (force simp: \<R>_def)
        then have "pstar (i-1) = pstar(Suc i)" 
          unfolding pstar_def
          by (smt (verit) True hgt_mono' of_nat_less_iff powr_non_neg) 
        then show ?thesis
          by (simp add: alpha_ge0)
      next
        case False
        then have "hgt (pseq (i-1)) \<le> h'"
          by (simp add: h'_def) linarith 
        then have \<dagger>: "alpha (hgt (pseq (i-1))) \<le> alpha h'"
          by (intro alpha_mono hgt_gt0)
        have "pseq (Suc i) \<ge> pseq (i-1) - ?e12 * alpha (hgt (pseq (i-1)))"
          using Y_6_4_Bblue \<open>i \<in> \<B>\<close> unfolding \<B>_def by blast
        with mult_left_mono [OF \<dagger>, of ?e12] show ?thesis
          unfolding pstar_def
          by (smt (verit) alpha_ge0 mult_minus_left powr_non_neg mult_le_0_iff)
      qed
    }
    then show ?thesis
      by (smt (verit, ccfv_SIG) mult_of_nat_commute sum_constant sum_mono)
  qed
  finally have B: "- alpha 1 * k \<le> (\<Sum>i\<in>\<B>. pstar (Suc i) - pstar (i-1))" .

  have "\<epsilon> powr (-1/4) * alpha 1 * card ((\<R>\<union>\<S>) \<inter> C) \<le> (\<Sum>i\<in>\<R>\<union>\<S>. if i \<in> C then \<epsilon> powr (-1/4) * alpha 1 else 0)"
    by (simp add: flip: sum.inter_restrict)
  also have "(\<Sum>i\<in>\<R>\<union>\<S>. if i \<in> C then \<epsilon> powr (-1/4) * alpha 1 else 0) \<le> (\<Sum>i\<in>\<R>\<union>\<S>. pstar i - pstar (i-1))"
  proof (intro sum_mono)
    fix i
    assume i: "i \<in> \<R> \<union> \<S>"
    then obtain "i-1 \<in> \<D>" "i>0"
      unfolding \<R>_def \<S>_def \<D>_def by (metis dreg_before_step1 dreg_before_gt0 Step_class_insert Un_iff)
    then have "pseq (i-1) \<le> pseq i"
      by (metis Suc_pred' Y_6_4_DegreeReg \<D>_def)
    then have "pstar (i-1) \<le> pstar i"
      by (fastforce simp: pstar_def)
    then show "(if i \<in> C then \<epsilon> powr (-1/4) * alpha 1 else 0) \<le> pstar i - pstar (i-1)"
      using C_def pstar_def qstar_def by auto
  qed
  finally have \<section>: "\<epsilon> powr (-1/4) * alpha 1 * card ((\<R>\<union>\<S>) \<inter> C) \<le> (\<Sum>i\<in>\<R>\<union>\<S>. pstar i - pstar (i-1))" .

  have psplit: "pstar (Suc i) - pstar (i-1) = (pstar (Suc i) - pstar i) + (pstar i - pstar (i-1))" for i
    by simp
  have RS: "\<epsilon> powr (-1/4) * alpha 1 * card ((\<R>\<union>\<S>) \<inter> C) + (- 2 * alpha 1 * k) \<le> (\<Sum>i\<in>\<R>\<union>\<S>. pstar (Suc i) - pstar (i-1))"
    unfolding psplit sum.distrib using RS_half \<section> by linarith

  have k16: "k powr (1/16) \<le> k powr 1"
    using kn0 by (intro powr_mono) auto

  have meq: "{..<halted_point} \<setminus> \<D> = (\<R>\<union>\<S>) \<union> \<B>"
    using Step_class_cases halted_point_minimal' by(fastforce simp: \<R>_def \<S>_def \<D>_def \<B>_def Step_class_def)

  have "(\<epsilon> powr (-1/4) * alpha 1 * card ((\<R>\<union>\<S>) \<inter> C) + (- 2 * alpha 1 * k))
        + (- alpha 1 * k)
      \<le> (\<Sum>i \<in> \<R>\<union>\<S>. pstar(Suc i) - pstar(i-1)) + (\<Sum>i\<in>\<B>. pstar(Suc i) - pstar(i-1))"
    using RS B by linarith
  also have "\<dots> = (\<Sum>i \<in> {..<halted_point} \<setminus> \<D>. pstar(Suc i) - pstar(i-1))"
    by (simp add: meq sum.union_disjoint)
  also have "\<dots> \<le> pstar halted_point - pstar 0"
  proof (cases "even halted_point")
    case False
    have "pseq (halted_point - Suc 0) \<le> pseq halted_point"
      using Y_6_4_DegreeReg [of "halted_point-1"] False not_halted_even_dreg odd_pos 
      by (auto simp: halted_point_minimal)
    then have "pstar(halted_point - Suc 0) \<le> pstar halted_point"
      by (simp add: pstar_def)
    with False show ?thesis
      by (simp add: oddset sum_odds_odd)
  qed (simp add: oddset sum_odds_even)
  also have "\<dots> = (\<Sum>i < halted_point. pstar(Suc i) - pstar i)"
    by (simp add: sum_lessThan_telescope)
  also have "\<dots> = pstar halted_point - pstar 0" 
    by (simp add: sum_lessThan_telescope)
  also have "\<dots> \<le> alpha 1 * \<epsilon> powr (-1/4)"
    using alpha_ge0 by (simp add: mult.commute pee_eq_p0 pstar_def qstar_def) 
  also have "\<dots> \<le> alpha 1 * k"
    using alpha_ge0 k16 by (intro powr_mono mult_left_mono) (auto simp: eps_def powr_powr)
  finally have "\<epsilon> powr (-1/4) * card ((\<R> \<union> \<S>) \<inter> C) * alpha 1 \<le> 4 * k * alpha 1"
    by (simp add: mult_ac)
  then have "\<epsilon> powr (-1/4) * real (card ((\<R> \<union> \<S>) \<inter> C)) \<le> 4 * k"
    using kn0 by (simp add: divide_simps alpha_eq eps_gt0)
  then show ?thesis
    using alpha_ge0[of 1] kn0 eps_gt0 by (simp add: powr_minus divide_simps mult_ac split: if_split_asm)
qed


subsection \<open>Lemma 7.12\<close>

definition "Big_X_7_12 \<equiv>
   \<lambda>\<mu> l. Big_X_7_11 \<mu> l \<and> Big_X_7_10 \<mu> l \<and> (\<forall>k. l\<le>k \<longrightarrow> Big_X_7_9 k)"

text \<open>establishing the size requirements for 7.12\<close>
lemma Big_X_7_12:
  assumes "0<\<mu>0" "\<mu>1<1" 
  shows "\<forall>\<^sup>\<infinity>l. \<forall>\<mu>. \<mu> \<in> {\<mu>0..\<mu>1} \<longrightarrow> Big_X_7_12 \<mu> l"
  using assms Big_X_7_11 Big_X_7_10 Big_X_7_9
  unfolding Big_X_7_12_def eventually_conj_iff
  apply (simp add: eventually_conj_iff all_imp_conj_distrib eventually_frequently_const_simps)
  using eventually_all_ge_at_top by blast  

lemma (in Book) X_7_12:
  defines "\<R> \<equiv> Step_class {red_step}"
  defines "\<S> \<equiv> Step_class {dboost_step}"
  defines "C \<equiv> {i. card (Xseq i) < (1 - 2 * \<epsilon> powr (1/4)) * card (Xseq (i-1))}"
  assumes big: "Big_X_7_12 \<mu> l"
  shows "card ((\<R>\<union>\<S>) \<inter> C) \<le> 7 * \<epsilon> powr (1/4) * k"
proof -
  define \<D> where "\<D> \<equiv> Step_class {dreg_step}"
  have big_711: "Big_X_7_11 \<mu> l" and big_710: "Big_X_7_10 \<mu> l"
    using big by (auto simp: Big_X_7_12_def)
  have [simp]: "finite \<R>" "finite \<S>"
    using finite_components by (auto simp: \<R>_def \<S>_def)
  \<comment> \<open>now the conditions for Lemmas 7.10 and 7.11\<close>
  define C10 where "C10 \<equiv> {i. hgt (pseq i) \<ge> hgt (pseq (i-1)) + \<epsilon> powr (-1/4)}"
  define C11 where "C11 \<equiv> {i. pseq i \<ge> pseq (i-1) + \<epsilon> powr (-1/4) * alpha 1 \<and> pseq (i-1) \<le> p0}"
  have "(\<R>\<union>\<S>) \<inter> C \<inter> {i. pseq (i-1) \<le> p0} \<subseteq> (\<R>\<union>\<S>) \<inter> C11"
  proof
    fix i
    assume i: "i \<in> (\<R>\<union>\<S>) \<inter> C \<inter> {i. pseq (i-1) \<le> p0}"
    then have iRS: "i \<in> \<R> \<union> \<S>" and iC: "i \<in> C"
      by auto
    then obtain i1: "i-1 \<in> \<D>" "i>0"
      unfolding \<R>_def \<S>_def \<D>_def by (metis Step_class_insert Un_iff dreg_before_step1 dreg_before_gt0)
    then have 77: "card (Xseq (i-1) \<setminus> Xseq i) / card (Xseq i) * (\<epsilon> powr (-1/2) * alpha (hgt (pseq (i-1))))
            \<le> pseq i - pseq (i-1)"
      by (metis Suc_diff_1 X_7_7 \<D>_def)
    have card_Xm1: "card (Xseq (i-1)) = card (Xseq i) + card (Xseq (i-1) \<setminus> Xseq i)"
      by (metis Xseq_antimono add_diff_inverse_nat card_Diff_subset card_mono diff_le_self 
          finite_Xseq linorder_not_less)
    have "card (Xseq i) > 0"
      by (metis Step_class_insert card_Xseq_pos \<R>_def \<S>_def iRS)
    have "card (Xseq (i-1)) > 0"
      using C_def iC less_irrefl by fastforce
    moreover have "2 * (card (Xseq (i-1)) * \<epsilon> powr (1/4)) < card (Xseq (i-1) \<setminus> Xseq i)"
      using iC card_Xm1 by (simp add: algebra_simps C_def)
    moreover have "card (Xseq i) \<le> 2 * card (Xseq (i-1))"
      using card_Xm1 by linarith
    ultimately have "\<epsilon> powr (1/4) \<le> card (Xseq (i-1) \<setminus> Xseq i) / card (Xseq (i-1))"
      by (simp add: divide_simps mult.commute)
    moreover have "real (card (Xseq i)) \<le> card (Xseq (i-1))"
      using card_Xm1 by linarith
    ultimately have 1: "\<epsilon> powr (1/4) \<le> card (Xseq (i-1) \<setminus> Xseq i) / card (Xseq i)"
      by (smt (verit) \<open>0 < card (Xseq i)\<close> frac_le of_nat_0_le_iff of_nat_0_less_iff)
    have "\<epsilon> powr (-1/4) * alpha 1
       \<le> card (Xseq (i-1) \<setminus> Xseq i) / card (Xseq i) * (\<epsilon> powr (-1/2) * alpha 1)"
      using alpha_ge0 mult_right_mono [OF 1, of "\<epsilon> powr (-1/2) * alpha 1"] 
      by (simp add: mult_ac flip: powr_add)
    also have "\<dots> \<le> card (Xseq (i-1) \<setminus> Xseq i) / card (Xseq i) * (\<epsilon> powr (-1/2) * alpha (hgt (pseq (i-1))))"
      by (intro mult_left_mono alpha_mono) (auto simp: Suc_leI hgt_gt0)
    also have "\<dots> \<le> pseq i - pseq (i-1)"
      using 77 by simp
    finally have "\<epsilon> powr (-1/4) * alpha 1 \<le> pseq i - pseq (i-1)" .
    with i show "i \<in> (\<R> \<union> \<S>) \<inter> C11"
      by (simp add: C11_def)
  qed
  then have "real (card ((\<R>\<union>\<S>) \<inter> C \<inter> {i. pseq (i-1) \<le> p0})) \<le> real (card ((\<R>\<union>\<S>) \<inter> C11))"
    by (simp add: card_mono)
  also have "\<dots> \<le> 4 * \<epsilon> powr (1/4) * k"
    using X_7_11 big_711 by (simp add: \<R>_def \<S>_def C11_def Step_class_insert_NO_MATCH)
  finally have "card ((\<R>\<union>\<S>) \<inter> C \<inter> {i. pseq (i-1) \<le> p0}) \<le> 4 * \<epsilon> powr (1/4) * k" .
  moreover
  have "card ((\<R>\<union>\<S>) \<inter> C \<setminus> {i. pseq (i-1) \<le> p0}) \<le> 3 * \<epsilon> powr (1/4) * k" 
  proof -
    have "Big_X_7_9 k"
      using Big_X_7_12_def big l_le_k by presburger
    then have X79: "card (Xseq (Suc i)) \<ge> (1 - 2 * \<epsilon> powr (1/4)) * card (Xseq i)" 
      if "i \<in> Step_class {dreg_step}" and "pseq i \<ge> p0" 
          and "hgt (pseq (Suc i)) \<le> hgt (pseq i) + \<epsilon> powr (-1/4)" for i
      using X_7_9 that by blast 
    have "(\<R>\<union>\<S>) \<inter> C \<setminus> {i. pseq (i-1) \<le> p0} \<subseteq> (\<R>\<union>\<S>) \<inter> C10"
      unfolding C10_def C_def
    proof clarify
      fix i
      assume "i \<in> \<R> \<union> \<S>"
        and \<section>: "card (Xseq i) < (1 - 2 * \<epsilon> powr (1/4)) * card (Xseq (i-1))" "\<not> pseq (i-1) \<le> p0"
      then obtain "i-1 \<in> \<D>" "i>0"
        unfolding \<D>_def \<R>_def \<S>_def 
        by (metis dreg_before_step1 dreg_before_gt0 Step_class_Un Un_iff insert_is_Un)
      with X79 \<section> show "hgt (pseq (i - 1)) + \<epsilon> powr (-1/4) \<le> hgt (pseq i)"
        by (force simp: \<D>_def)
    qed
    then have "card ((\<R>\<union>\<S>) \<inter> C \<setminus> {i. pseq (i-1) \<le> p0}) \<le> real (card ((\<R>\<union>\<S>) \<inter> C10))"
      by (simp add: card_mono)
    also have "card ((\<R>\<union>\<S>) \<inter> C10) \<le> 3 * \<epsilon> powr (1/4) * k"
      unfolding \<R>_def \<S>_def C10_def by (intro X_7_10 assms big_710)
    finally show ?thesis . 
  qed
  moreover
  have "card ((\<R>\<union>\<S>) \<inter> C)
      = real (card ((\<R>\<union>\<S>) \<inter> C \<inter> {i. pseq (i-1) \<le> p0})) + real (card ((\<R>\<union>\<S>) \<inter> C \<setminus> {i. pseq (i-1) \<le> p0}))"
    by (metis card_Int_Diff of_nat_add \<open>finite \<R>\<close> \<open>finite \<S>\<close> finite_Int infinite_Un)
  ultimately show ?thesis
    by linarith 
qed

subsection \<open>Lemma 7.6\<close>

definition "Big_X_7_6 \<equiv>
   \<lambda>\<mu> l. Big_Blue_4_1 \<mu> l \<and> Big_X_7_12 \<mu> l \<and> (\<forall>k. k\<ge>l \<longrightarrow> Big_X_7_8 k \<and> 1 - 2 * eps k powr (1/4) > 0)"

lemma Big_X_7_6:
  assumes "0<\<mu>0" "\<mu>1<1" 
  shows "\<forall>\<^sup>\<infinity>l. \<forall>\<mu>. \<mu> \<in> {\<mu>0..\<mu>1} \<longrightarrow> Big_X_7_6 \<mu> l"
  using assms Big_Blue_4_1 Big_X_7_8 Big_X_7_12
  unfolding Big_X_7_6_def eps_def
  apply (simp add: eventually_conj_iff all_imp_conj_distrib eventually_all_ge_at_top)  
  apply (intro conjI strip eventually_all_geI0 eventually_all_ge_at_top; real_asymp)
  done

definition "ok_fun_76 \<equiv> 
  \<lambda>k. ((1 + 2 * real k) * ln (1 - 2 * eps k powr (1/4)) 
      - (k powr (3/4) + 7 * eps k powr (1/4) * k + 1) * (2 * ln k)) / ln 2" 

lemma ok_fun_76: "ok_fun_76 \<in> o(real)"
  unfolding eps_def ok_fun_76_def by real_asymp

lemma (in Book) X_7_6:
  assumes big: "Big_X_7_6 \<mu> l"
  defines "\<D> \<equiv> Step_class {dreg_step}"
  shows "(\<Prod>i\<in>\<D>. card(Xseq(Suc i)) / card (Xseq i)) \<ge> 2 powr ok_fun_76 k"
proof -
  define \<R> where "\<R> \<equiv> Step_class {red_step}"
  define \<B> where "\<B> \<equiv> Step_class {bblue_step}"
  define \<S> where "\<S> \<equiv> Step_class {dboost_step}"
  define C where "C \<equiv> {i. card (Xseq i) < (1 - 2 * \<epsilon> powr (1/4)) * card (Xseq (i-1))}"
  define C' where "C' \<equiv> Suc -` C"
  have big41: "Big_Blue_4_1 \<mu> l"
    and 712: "card ((\<R>\<union>\<S>) \<inter> C) \<le> 7 * \<epsilon> powr (1/4) * k"
    using big X_7_12 l_le_k by (auto simp: Big_X_7_6_def \<R>_def \<S>_def C_def)

  have [simp]: "finite \<D>" "finite \<R>" "finite \<B>" "finite \<S>"
    using finite_components by (auto simp: \<D>_def \<R>_def \<B>_def \<S>_def)
  have "card \<R> < k"
    using \<R>_def assms red_step_limit by blast+ 
  have "card \<B> \<le> l powr (3/4)"
    using big41 bblue_step_limit by (auto simp: \<B>_def)
  then have "card (\<B> \<inter> C) \<le> l powr (3/4)"
    using card_mono [OF _ Int_lower1] by (smt (verit) \<open>finite \<B>\<close> of_nat_mono)
  also have "\<dots> \<le> k powr (3/4)"
    by (simp add: l_le_k powr_mono2)
  finally have Bk_34: "card (\<B> \<inter> C) \<le> k powr (3/4)" .

  have less_l: "card \<B> + card \<S> < l"
    using bblue_dboost_step_limit big41 by (auto simp: \<B>_def \<S>_def)
  have [simp]: "(\<B> \<union> (\<R> \<union> \<S>)) \<inter> {halted_point} = {}" "\<R> \<inter> \<S> = {}" "\<B> \<inter> (\<R> \<union> \<S>) = {}" 
               "halted_point \<notin> \<B>" "halted_point \<notin> \<R>" "halted_point \<notin> \<S>"
               "\<B> \<inter> C \<inter> (\<R> \<inter> C \<union> \<S> \<inter> C) = {}" for C
    using halted_point_minimal' by (force simp: \<B>_def \<R>_def \<S>_def Step_class_def)+

  have "Big_X_7_8 k" and one_minus_gt0: "1 - 2 * \<epsilon> powr (1/4) > 0"
    using big l_le_k by (auto simp: Big_X_7_6_def)
  then have X78: "card (Xseq (Suc i)) \<ge> card (Xseq i) / k^2" if "i \<in> \<D>" for i
    using X_7_8 that by (force simp: \<D>_def)

  let ?DC = "\<lambda>k. k powr (3/4) + 7 * eps k powr (1/4) * k + 1"
  have dc_pos: "?DC k > 0" for k
    by (smt (verit) of_nat_less_0_iff powr_ge_zero zero_le_mult_iff)
  have X_pos: "card (Xseq i) > 0" if "i \<in> \<D>" for i
  proof -
    have "card (Xseq (Suc i)) > 0"
      using that X_7_7 kn0 unfolding \<D>_def by blast
    then show ?thesis
      by (metis Xseq_Suc_subset card_mono finite_Xseq gr0I leD)
  qed
  have "ok_fun_76 k \<le> log 2 ((1 / (real k)\<^sup>2) powr ?DC k * (1 - 2 * \<epsilon> powr (1/4)) ^ (k + l + 1))"
    unfolding ok_fun_76_def log_def
    using kn0 l_le_k one_minus_gt0
    by (simp add: ln_mult ln_div ln_realpow divide_right_mono mult_le_cancel_right flip: power_Suc mult.assoc)
  then have "2 powr ok_fun_76 k \<le> (1 / (real k)\<^sup>2) powr ?DC k * (1 - 2 * \<epsilon> powr (1/4)) ^ (k + l + 1)"
    using powr_eq_iff kn0 one_minus_gt0 by (simp add: le_log_iff)
  also have "\<dots> \<le> (1 / (real k)\<^sup>2) powr card (\<D> \<inter> C') * (1 - 2 * \<epsilon> powr (1/4)) ^ card (\<D>\<setminus>C')"
  proof (intro mult_mono powr_mono')
    have "Suc i \<in> \<R>" if "i \<in> \<D>" "Suc i \<noteq> halted_point" "Suc i \<notin> \<B>" "Suc i \<notin> \<S>" for i
    proof -
      have "Suc i \<notin> \<D>"
        by (metis \<D>_def \<open>i \<in> \<D>\<close> even_Suc step_even)
      moreover 
      have "stepper_kind i \<noteq> halted"
        using \<D>_def \<open>i \<in> \<D>\<close> Step_class_def by force
      ultimately show "Suc i \<in> \<R>"
        using that halted_point_minimal' halted_point_minimal Step_class_cases Suc_lessI 
          \<B>_def \<D>_def \<R>_def \<S>_def by blast
    qed
    then have "Suc ` \<D> \<subseteq> \<B> \<union> (\<R> \<union> \<S>) \<union> {halted_point}"
      by auto
    then have ifD: "Suc i \<in> \<B> \<or> Suc i \<in> \<R> \<or> Suc i \<in> \<S> \<or> Suc i = halted_point" if "i \<in> \<D>" for i
      using that by force
    then have "card \<D> \<le> card (\<B> \<union> (\<R>\<union>\<S>) \<union> {halted_point})"
      by (intro card_inj_on_le [of Suc]) auto
    also have "\<dots> = card \<B> + card \<R> + card \<S> + 1"
      by (simp add: card_Un_disjoint card_insert_if)
    also have "\<dots> \<le> k + l + 1"
      using \<open>card \<R> < k\<close> less_l by linarith
    finally have card_D: "card \<D> \<le> k + l + 1" .

    have "(1 - 2 * \<epsilon> powr (1/4)) * card (Xseq 0) \<le> 1 * real (card (Xseq 0))"
      by (intro mult_right_mono; force)
    then have "0 \<notin> C"
      by (force simp: C_def)
    then have C_eq_C': "C = Suc ` C'"
      using nat.exhaust by (auto simp: C'_def set_eq_iff image_iff)
    have "card (\<D> \<inter> C') \<le> real (card ((\<B> \<union> (\<R>\<union>\<S>) \<union> {halted_point}) \<inter> C))"
      using ifD
      by (intro of_nat_mono card_inj_on_le [of Suc]) (force simp: Int_insert_left C_eq_C')+
    also have "\<dots> \<le> card (\<B> \<inter> C) + real (card ((\<R>\<union>\<S>) \<inter> C)) + 1"
      by (simp add: Int_insert_left Int_Un_distrib2 card_Un_disjoint card_insert_if)
    also have "\<dots> \<le> ?DC k"
      using Bk_34 712 by force 
    finally show "card (\<D> \<inter> C') \<le> ?DC k" .
    have "card (\<D>\<setminus>C') \<le> card \<D>"
      using \<open>finite \<D>\<close> by (simp add: card_mono)
    then show "(1 - 2 * \<epsilon> powr (1/4)) ^ (k+l+1) \<le> (1 - 2 * \<epsilon> powr (1/4)) ^ card (\<D>\<setminus>C')"
      by (smt (verit) card_D add_leD2 one_minus_gt0 power_decreasing powr_ge_zero)
  qed (use one_minus_gt0 kn0 in auto)
  also have "\<dots> = (\<Prod>i\<in>\<D>. if i \<in> C' then 1 / real k ^ 2 else 1 - 2 * \<epsilon> powr (1/4))"
    by (simp add: kn0 powr_realpow prod.If_cases Diff_eq)
  also have "\<dots> \<le> (\<Prod>i \<in> \<D>. card (Xseq (Suc i)) / card (Xseq i))"
    using X_pos X78 one_minus_gt0 kn0 by (simp add: divide_simps C'_def C_def prod_mono)  
  finally show ?thesis .
qed

subsection \<open>Lemma 7.1\<close>

definition "Big_X_7_1 \<equiv>
   \<lambda>\<mu> l. Big_Blue_4_1 \<mu> l \<and> Big_X_7_2 \<mu> l \<and> Big_X_7_4 \<mu> l \<and> Big_X_7_6 \<mu> l"

text \<open>establishing the size requirements for 7.11\<close>
lemma Big_X_7_1:
  assumes "0<\<mu>0" "\<mu>1<1" 
  shows "\<forall>\<^sup>\<infinity>l. \<forall>\<mu>. \<mu> \<in> {\<mu>0..\<mu>1} \<longrightarrow> Big_X_7_1 \<mu> l"
  unfolding Big_X_7_1_def
  using assms Big_Blue_4_1 Big_X_7_2 Big_X_7_4 Big_X_7_6
  by (simp add: eventually_conj_iff all_imp_conj_distrib)  

definition "ok_fun_71 \<equiv> \<lambda>\<mu> k. ok_fun_72 \<mu> k + ok_fun_73 k + ok_fun_74 k + ok_fun_76 k"

lemma ok_fun_71:
  assumes "0<\<mu>" "\<mu><1" 
  shows "ok_fun_71 \<mu> \<in> o(real)"
  using ok_fun_72 ok_fun_73 ok_fun_74 ok_fun_76
  by (simp add: assms ok_fun_71_def sum_in_smallo)

lemma (in Book) X_7_1:
  assumes big: "Big_X_7_1 \<mu> l"
  defines "\<D> \<equiv> Step_class {dreg_step}"
  defines "\<R> \<equiv> Step_class {red_step}" and "\<S> \<equiv> Step_class {dboost_step}"
  shows "card (Xseq halted_point) \<ge> 
     2 powr ok_fun_71 \<mu> k * \<mu>^l * (1-\<mu>) ^ card \<R> * (bigbeta / \<mu>) ^ card \<S> * card X0"
proof -
  define \<B> where "\<B> \<equiv> Step_class {bblue_step}"
  have 72: "Big_X_7_2 \<mu> l" and 74: "Big_X_7_4 \<mu> l" 
    and 76: "Big_X_7_6 \<mu> l" 
    and big41: "Big_Blue_4_1 \<mu> l"
    using big by (auto simp: Big_X_7_1_def)
  then have [simp]: "finite \<R>" "finite \<B>" "finite \<S>" "finite \<D>" 
                    "\<R>\<inter>\<B> = {}" "\<S>\<inter>\<D> = {}" "(\<R>\<union>\<B>)\<inter>(\<S>\<union>\<D>) = {}"
    using finite_components by (auto simp: \<R>_def \<B>_def \<S>_def \<D>_def Step_class_def)
  have BS_le_l: "card \<B> + card \<S> < l"
    using big41 bblue_dboost_step_limit by (auto simp: \<S>_def \<B>_def)
  
  have R: "(\<Prod>i\<in>\<R>. card (Xseq(Suc i)) / card (Xseq i)) \<ge> 2 powr (ok_fun_72 \<mu> k) * (1-\<mu>) ^ card \<R>"
    unfolding \<R>_def using 72 X_7_2 by meson
  have B: "(\<Prod>i\<in>\<B>. card (Xseq(Suc i)) / card (Xseq i)) \<ge> 2 powr (ok_fun_73 k) * \<mu> ^ (l - card \<S>)"
    unfolding \<B>_def \<S>_def using big41 X_7_3 by meson
  have S: "(\<Prod>i\<in>\<S>. card (Xseq (Suc i)) / card (Xseq i)) \<ge> 2 powr ok_fun_74 k * bigbeta ^ card \<S>"
    unfolding \<S>_def using 74 X_7_4 by meson
  have D: "(\<Prod>i\<in>\<D>. card(Xseq(Suc i)) / card (Xseq i)) \<ge> 2 powr ok_fun_76 k"
    unfolding \<D>_def using 76 X_7_6 by meson
  have below_m: "\<R>\<union>\<B>\<union>\<S>\<union>\<D> = {..<halted_point}"
    using assms by (auto simp: \<R>_def \<B>_def \<S>_def \<D>_def before_halted_eq Step_class_insert_NO_MATCH)
  have X_nz: "\<And>i. i < halted_point \<Longrightarrow> card (Xseq i) \<noteq> 0"
    using assms below_halted_point_cardX by blast
  have tele: "card (Xseq halted_point) = (\<Prod>i < halted_point. card (Xseq(Suc i)) / card (Xseq i)) * card (Xseq 0)"
  proof (cases "halted_point=0")
    case False
    with X_nz prod_lessThan_telescope_mult [where f = "\<lambda>i. real (card (Xseq i))"] 
    show ?thesis by simp
  qed auto
  have X0_nz: "card (Xseq 0) > 0"
    by (simp add: card_XY0)
  have "2 powr ok_fun_71 \<mu> k * \<mu>^l * (1-\<mu>) ^ card \<R> * (bigbeta / \<mu>) ^ card \<S>
     \<le> 2 powr ok_fun_71 \<mu> k * \<mu> ^ (l - card \<S>) * (1-\<mu>) ^ card \<R> * (bigbeta ^ card \<S>)"
    using \<mu>01 BS_le_l by (simp add: power_diff power_divide)
  also have "\<dots> \<le> (\<Prod>i\<in>\<R>\<union>\<B>\<union>\<S>\<union>\<D>. card (Xseq(Suc i)) / card (Xseq i))"
  proof -
    have "(\<Prod>i\<in>(\<R>\<union>\<B>)\<union>(\<S>\<union>\<D>). card (Xseq(Suc i)) / card (Xseq i)) 
         \<ge> ((2 powr (ok_fun_72 \<mu> k) * (1-\<mu>) ^ card \<R>) * (2 powr (ok_fun_73 k) * \<mu> ^ (l - card \<S>)))
          * ((2 powr ok_fun_74 k * bigbeta ^ card \<S>) * (2 powr ok_fun_76 k))"
      using \<mu>01 by (auto simp: R B S D prod.union_disjoint prod_nonneg bigbeta_ge0 intro!: mult_mono)
    then show ?thesis
      by (simp add: Un_assoc mult_ac powr_add ok_fun_71_def)
  qed
  also have "\<dots> \<le> (\<Prod>i < halted_point. card (Xseq(Suc i)) / card (Xseq i))"
    using below_m by auto
  finally show ?thesis
    using X0_nz \<mu>01 unfolding tele by (simp add: divide_simps)
qed

end
