(* Author: Johannes Hölzl <hoelzl@in.tum.de> *)

header {* Markov Decision Processes *}

theory Markov_Decision_Process
  imports Discrete_Time_Markov_Chain
begin

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

subsection {* Schedulers *}

text {*

We want to construct a \emph{non-free} codatatype
  @{text "'s cfg = Cfg (state: 's) (action: 's pmf) (cont: 's \<Rightarrow> 's cfg)"}.
with the restriction
  @{term "state (cont cfg s) = s"}

*}

codatatype 's scheduler = Scheduler (action_sch: "'s pmf") (cont_sch: "'s \<Rightarrow> 's scheduler")
datatype 's cfg = Cfg' (state: 's) (scheduler: "'s scheduler")

definition "action cfg = action_sch (scheduler cfg)"
definition "cont cfg s = Cfg' s (cont_sch (scheduler cfg) s)"

definition Cfg :: "'s \<Rightarrow> 's pmf \<Rightarrow> ('s \<Rightarrow> 's cfg) \<Rightarrow> 's cfg" where
  "Cfg s D c = Cfg' s (Scheduler D (\<lambda>t. scheduler (c t)))"

definition cfg_corec :: "'s \<Rightarrow> ('a \<Rightarrow> 's pmf) \<Rightarrow> ('a \<Rightarrow> 's \<Rightarrow> 'a)  \<Rightarrow> 'a \<Rightarrow> 's cfg" where
  "cfg_corec s d c x = Cfg' s (corec_scheduler d (\<lambda>x s. Inr (c x s)) x)"

lemma
  shows state_cont[simp]: "state (cont cfg s) = s"
    and state_Cfg[simp]: "state (Cfg s d' c') = s"
    and action_Cfg[simp]: "action (Cfg s d' c') = d'"
    and cont_Cfg[simp]: "state (c' t) = t \<Longrightarrow> cont (Cfg s d' c') t = c' t"
    and state_cfg_corec[simp]: "state (cfg_corec s d c x) = s"
    and action_cfg_corec[simp]: "action (cfg_corec s d c x) = d x"
    and cont_cfg_corec[simp]: "cont (cfg_corec s d c x) t = cfg_corec t d c (c x t)"
  by (simp_all add: cfg_corec_def Cfg_def action_def cont_def cfg.expand)

lemma cfg_coinduct[consumes 1, case_names state action cont]:
  assumes "X c d"
  assumes state: "\<And>c d. X c d \<Longrightarrow> state c = state d"
  assumes action:  "\<And>c d. X c d \<Longrightarrow> action c = action d"
  assumes cont: "\<And>c d t. X c d \<Longrightarrow> X (cont c t) (cont d t)"
  shows "c = d"
proof (intro cfg.expand conjI assms)
  from `X c d` show "scheduler c = scheduler d"
    by (coinduction arbitrary: c d)
       (auto intro!: exI[of _ "cont c y" for c y] dest: cont action simp: cont_def action_def)
qed

subsubsection {* Memoryless scheduler *}

definition "memoryless_on f s = cfg_corec s f (\<lambda>_ t. t) s"

lemma
  shows state_memoryless_on[simp]: "state (memoryless_on f s) = s"
    and action_memoryless_on[simp]: "action (memoryless_on f s) = f s"
    and cont_memoryless_on[simp]: "cont (memoryless_on f s) t = memoryless_on f t"
  by (simp_all add: memoryless_on_def)

definition K_cfg :: "'s cfg \<Rightarrow> 's cfg pmf" where
  "K_cfg cfg = map_pmf (cont cfg) (action cfg)"

lemma set_K_cfg: "set_pmf (K_cfg cfg) = cont cfg ` set_pmf (action cfg)"
  by (simp add: K_cfg_def set_pmf_map)

lemma nn_integral_K_cfg: "(\<integral>\<^sup>+cfg. f cfg \<partial>K_cfg cfg) = (\<integral>\<^sup>+s. f (cont cfg s) \<partial>action cfg)"
  by (simp add: K_cfg_def map_pmf.rep_eq nn_integral_distr)

subsection {* Markov Decision Process *}

locale Markov_Decision_Process =
  fixes K :: "'s \<Rightarrow> 's pmf set"
  assumes K_wf: "\<And>s. K s \<noteq> {}"
begin

coinductive cfg_onp :: "'s \<Rightarrow> 's cfg \<Rightarrow> bool" where
  "\<And>s. state cfg = s \<Longrightarrow> action cfg \<in> K s \<Longrightarrow> (\<And>t. t \<in> action cfg \<Longrightarrow> cfg_onp t (cont cfg t)) \<Longrightarrow>
    cfg_onp s cfg"

definition "cfg_on s = {cfg. cfg_onp s cfg}"

lemma
  shows cfg_onD_action[intro, simp]: "cfg \<in> cfg_on s \<Longrightarrow> action cfg \<in> K s"
    and cfg_onD_cont[intro, simp]: "cfg \<in> cfg_on s \<Longrightarrow> t \<in> action cfg \<Longrightarrow> cont cfg t \<in> cfg_on t"
    and cfg_onD_state[simp]: "cfg \<in> cfg_on s \<Longrightarrow> state cfg = s"
    and cfg_onI: "state cfg = s \<Longrightarrow> action cfg \<in> K s \<Longrightarrow> (\<And>t. t \<in> action cfg \<Longrightarrow> cont cfg t \<in> cfg_on t) \<Longrightarrow> cfg \<in> cfg_on s"
  by (auto simp: cfg_on_def intro: cfg_onp.intros elim: cfg_onp.cases)

lemma cfg_on_coinduct[coinduct set: cfg_on]:
  assumes "P s cfg"
  assumes "\<And>cfg s. P s cfg \<Longrightarrow> state cfg = s"
  assumes "\<And>cfg s. P s cfg \<Longrightarrow> action cfg \<in> K s"
  assumes "\<And>cfg s t. P s cfg \<Longrightarrow> t \<in> action cfg \<Longrightarrow> P t (cont cfg t)"
  shows "cfg \<in> cfg_on s"
  using assms cfg_onp.coinduct[of P s cfg] by (simp add: cfg_on_def)

lemma memoryless_on_cfg_onI:
  assumes "\<And>s. f s \<in> K s"
  shows "memoryless_on f s \<in> cfg_on s"
  by (coinduction arbitrary: s) (auto intro: assms)

lemma cfg_of_cfg_onI:
  "D \<in> K s \<Longrightarrow> (\<And>t. t \<in> D \<Longrightarrow> c t \<in> cfg_on t) \<Longrightarrow> Cfg s D c \<in> cfg_on s"
  by (rule cfg_onI) auto

definition "arb_act s = (SOME D. D \<in> K s)"

lemma arb_actI[simp]: "arb_act s \<in> K s"
  by (simp add: arb_act_def some_in_iff K_wf)

lemma cfg_on_not_empty[intro, simp]: "cfg_on s \<noteq> {}"
  by (auto intro: memoryless_on_cfg_onI arb_actI)

sublocale MC!: MC_syntax K_cfg .

abbreviation St :: "'s stream measure" where
  "St \<equiv> stream_space (count_space UNIV)"

definition "T cfg = distr (MC.T cfg) St (smap state)"

sublocale T!: prob_space "T cfg" for cfg
  by (simp add: T_def MC.T.prob_space_distr)

lemma space_T[simp]: "space (T cfg) = space St"
  by (simp add: T_def)

lemma sets_T[simp]: "sets (T cfg) = sets St"
  by (simp add: T_def)

lemma nn_integral_T:
  assumes [measurable]: "f \<in> borel_measurable St"
  shows "(\<integral>\<^sup>+X. f X \<partial>T cfg) = (\<integral>\<^sup>+cfg'. (\<integral>\<^sup>+x. f (state cfg' ## x) \<partial>T cfg') \<partial>K_cfg cfg)"
  by (simp add: T_def MC.nn_integral_T[of _ cfg] nn_integral_distr)

lemma emeasure_Collect_T:
  assumes [measurable]: "Measurable.pred St P"
  shows "emeasure (T cfg) {x\<in>space St. P x} =
    (\<integral>\<^sup>+cfg'. emeasure (T cfg') {x\<in>space St. P (state cfg' ## x)} \<partial>K_cfg cfg)"
  using MC.emeasure_Collect_T[of "\<lambda>x. P (smap state x)" cfg]
  by (simp add: nn_integral_distr emeasure_Collect_distr T_def)

definition "E_sup s f = (\<Squnion>cfg\<in>cfg_on s. \<integral>\<^sup>+x. f x \<partial>T cfg)"

lemma E_sup_nonneg: "0 \<le> E_sup s f"
  by (auto intro!: SUP_upper2 nn_integral_nonneg memoryless_on_cfg_onI arb_actI simp: E_sup_def)

lemma E_sup_const: "0 \<le> c \<Longrightarrow> E_sup s (\<lambda>_. c) = c"
  using T.emeasure_space_1 by (simp add: E_sup_def)

lemma E_sup_mult_right:
  assumes [measurable]: "f \<in> borel_measurable St" and [simp]: "0 \<le> c"
  shows "E_sup s (\<lambda>x. c * f x) = c * E_sup s f"
  by (simp add: nn_integral_cmult E_sup_def SUP_ereal_mult_right nn_integral_nonneg)

lemma E_sup_mono:
  "(\<And>\<omega>. f \<omega> \<le> g \<omega>) \<Longrightarrow> E_sup s f \<le> E_sup s g"
  unfolding E_sup_def by (intro SUP_subset_mono order_refl nn_integral_mono)

lemma E_sup_add:
  assumes [measurable]: "f \<in> borel_measurable St" "g \<in> borel_measurable St"
  shows "E_sup s (\<lambda>x. f x + g x) \<le> E_sup s f + E_sup s g"
proof -
  { fix \<omega> have "f \<omega> + g \<omega> \<le> max 0 (f \<omega>) + max 0 (g \<omega>)"
      by (cases "f \<omega>" "g \<omega>" rule: ereal2_cases) (auto split: split_max) }
  then have "E_sup s (\<lambda>x. f x + g x) \<le> E_sup s (\<lambda>x. max 0 (f x) + max 0 (g x))"
    by (rule E_sup_mono)
  also have "\<dots> = (\<Squnion>cfg\<in>cfg_on s. (\<integral>\<^sup>+x. max 0 (f x) \<partial>T cfg) + (\<integral>\<^sup>+x. max 0 (g x) \<partial>T cfg))"
    by (simp add: E_sup_def nn_integral_add)
  also have "\<dots> \<le> (\<Squnion>cfg\<in>cfg_on s. \<integral>\<^sup>+x. max 0 (f x) \<partial>T cfg) + (\<Squnion>cfg\<in>cfg_on s. (\<integral>\<^sup>+x. max 0 (g x) \<partial>T cfg))"
    by (auto simp: SUP_le_iff intro!: ereal_add_mono SUP_upper)
  finally show ?thesis
    by (simp add: nn_integral_max_0 E_sup_def)
qed

lemma E_sup_add_left:
  assumes [measurable]: "f \<in> borel_measurable St" and nn: "0 \<le> c" "\<And>x. 0 \<le> f x"
  shows "E_sup s (\<lambda>x. f x + c) = E_sup s f + c"
  by (simp add: nn nn_integral_add E_sup_def T.emeasure_space_1[simplified] nn_integral_nonneg SUP_ereal_add_left)

lemma E_sup_SUP:
  assumes [measurable]: "\<And>i. f i \<in> borel_measurable St" and [simp]: "incseq f"
  shows "E_sup s (\<lambda>x. \<Squnion>i. f i x) = (\<Squnion>i. E_sup s (f i))"
  by (auto simp add: E_sup_def nn_integral_monotone_convergence_SUP intro: SUP_commute)

lemma E_sup_iterate:
  assumes [measurable]: "f \<in> borel_measurable St"
  shows "E_sup s f = (\<Squnion>D\<in>K s. \<integral>\<^sup>+ t. E_sup t (\<lambda>\<omega>. f (t ## \<omega>)) \<partial>D)"
proof -
  let ?v = "\<lambda>t. \<integral>\<^sup>+x. f (state t ## x) \<partial>T t"
  let ?p = "\<lambda>t. E_sup t (\<lambda>\<omega>. f (t ## \<omega>))"
  have "E_sup s f = (\<Squnion>cfg\<in>cfg_on s. \<integral>\<^sup>+t. ?v t \<partial>K_cfg cfg)"
    unfolding E_sup_def by (intro SUP_cong refl) (subst nn_integral_T, simp_all add: cfg_on_def)
  also have "\<dots> = (\<Squnion>D\<in>K s. \<integral>\<^sup>+t. ?p t \<partial>D)"
  proof (intro antisym SUP_least)
    fix cfg :: "'s cfg" assume cfg: "cfg \<in> cfg_on s"
    then show "(\<integral>\<^sup>+ t. ?v t \<partial>K_cfg cfg) \<le> (SUP D:K s. \<integral>\<^sup>+t. ?p t \<partial>D)"
      by (auto simp: E_sup_def nn_integral_K_cfg AE_measure_pmf_iff
               intro!: nn_integral_mono_AE SUP_upper2)
  next
    fix D assume D: "D \<in> K s" show "(\<integral>\<^sup>+t. ?p t \<partial>D) \<le> (SUP cfg : cfg_on s. \<integral>\<^sup>+ t. ?v t \<partial>K_cfg cfg)"
    proof cases
      assume p_finite: "\<forall>t\<in>D. ?p t < \<infinity>"
      show ?thesis
      proof (rule ereal_le_epsilon2, intro allI impI)
        fix e :: real assume "0 < e"
        have "\<forall>t\<in>D. \<exists>cfg\<in>cfg_on t. ?p t \<le> ?v cfg + e"
        proof
          fix t assume "t \<in> D"
          moreover have "(SUP cfg : cfg_on t. ?v cfg) = ?p t"
            unfolding E_sup_def by (simp add: cfg_on_def)
          moreover have "0 \<le> ?p t"
            by (rule E_sup_nonneg)
          ultimately have "\<bar>SUP cfg : cfg_on t. ?v cfg\<bar> \<noteq> \<infinity>"
            using p_finite by (intro ereal_infinity_cases) auto
          from SUP_approx_ereal[OF `0 < e` refl this]
          show "\<exists>cfg\<in>cfg_on t. ?p t \<le> ?v cfg + e"
            by (simp add: E_sup_def)
        qed
        then obtain cfg' where v_cfg': "\<And>t. t \<in> D \<Longrightarrow> ?p t \<le> ?v (cfg' t) + e" and
          cfg_on_cfg': "\<And>t. t \<in> D \<Longrightarrow> cfg' t \<in> cfg_on t"
          unfolding Bex_def bchoice_iff by blast
  
        let ?cfg = "Cfg s D cfg'"
        have cfg: "K_cfg ?cfg = map_pmf cfg' D"
          by (auto simp add: K_cfg_def fun_eq_iff intro!: map_pmf_cong dest: cfg_on_cfg')
  
        have "(\<integral>\<^sup>+ t. ?p t \<partial>D) \<le> (\<integral>\<^sup>+t. ?v (cfg' t) + e \<partial>D)"
          by (intro nn_integral_mono_AE) (simp add: v_cfg' AE_measure_pmf_iff)
        also have "\<dots> = (\<integral>\<^sup>+t. ?v (cfg' t) \<partial>D) + e"
          using `0 < e` measure_pmf.emeasure_space_1[of D]
          by (subst nn_integral_add) (auto intro: cfg_on_cfg' nn_integral_nonneg)
        also have "(\<integral>\<^sup>+t. ?v (cfg' t) \<partial>D) = (\<integral>\<^sup>+t. ?v t \<partial>K_cfg ?cfg)"
          by (simp add: cfg map_pmf.rep_eq nn_integral_distr)
        also have "\<dots> \<le> (SUP cfg:cfg_on s. (\<integral>\<^sup>+t. ?v t \<partial>K_cfg cfg))"
          by (auto intro!: SUP_upper intro!: cfg_of_cfg_onI D cfg_on_cfg')
        finally show "(\<integral>\<^sup>+ t. ?p t \<partial>D) \<le> (SUP cfg : cfg_on s. \<integral>\<^sup>+ t. ?v t \<partial>K_cfg cfg) + e"
          by (blast intro: ereal_add_mono)
      qed
    next
      assume "\<not> (\<forall>t\<in>D. ?p t < \<infinity>)"
      then obtain t where "t \<in> D" "?p t = \<infinity>"
        by auto
      then have "\<infinity> = pmf (D) t * ?p t"
        by (auto intro!: pmf_positive)
      also have "\<dots> = (SUP cfg : cfg_on t. pmf (D) t * ?v cfg)"
        unfolding E_sup_def
        by (auto simp add: pmf_nonneg nn_integral_nonneg intro!: SUP_ereal_mult_right[symmetric])
      also have "\<dots> \<le> (SUP cfg : cfg_on s. \<integral>\<^sup>+ t. ?v t \<partial>K_cfg cfg)"
        unfolding E_sup_def
      proof (intro SUP_least SUP_upper2)
        fix cfg :: "'s cfg" assume cfg: "cfg \<in> cfg_on t"

        let ?cfg = "Cfg s D ((memoryless_on arb_act) (t := cfg))"
        have C: "K_cfg ?cfg = map_pmf ((memoryless_on arb_act) (t := cfg)) D"
          by (auto simp add: K_cfg_def fun_eq_iff intro!: map_pmf_cong simp: cfg)

        show "?cfg \<in> cfg_on s"
          by (auto intro!: cfg_of_cfg_onI D cfg memoryless_on_cfg_onI)
        have "ereal (pmf (D) t) * (\<integral>\<^sup>+ x. f (state cfg ## x) \<partial>T cfg) =
          (\<integral>\<^sup>+t'. (\<integral>\<^sup>+ x. f (state cfg ## x) \<partial>T cfg) * indicator {t} t' \<partial>D)"
          by (subst mult_ac)
             (simp add: nn_integral_nonneg nn_integral_cmult_indicator emeasure_pmf_single)
        also have "\<dots> = (\<integral>\<^sup>+cfg. ?v cfg * indicator {t} (state cfg) \<partial>K_cfg ?cfg)"
          unfolding C using cfg
          by (auto simp add: nn_integral_distr map_pmf.rep_eq split: split_indicator
                   intro!: nn_integral_cong)
        also have "\<dots> \<le> (\<integral>\<^sup>+cfg. ?v cfg \<partial>K_cfg ?cfg)"
          by (auto intro!: nn_integral_mono nn_integral_nonneg split: split_indicator)
        finally show "ereal (pmf (D) t) * (\<integral>\<^sup>+ x. f (state cfg ## x) \<partial>T cfg)
           \<le> (\<integral>\<^sup>+ t. \<integral>\<^sup>+ x. f (state t ## x) \<partial>T t \<partial>K_cfg ?cfg)" .
      qed
      finally show ?thesis
        by simp
    qed
  qed
  finally show ?thesis .
qed

definition "E_inf s f = (\<Sqinter>cfg\<in>cfg_on s. \<integral>\<^sup>+x. f x \<partial>T cfg)"

lemma E_inf_nonneg: "0 \<le> E_inf s f"
  by (simp add: E_inf_def le_INF_iff nn_integral_nonneg)

lemma E_inf_const: "0 \<le> c \<Longrightarrow> E_inf s (\<lambda>_. c) = c"
  using T.emeasure_space_1 by (simp add: E_inf_def)

lemma E_inf_mono:
  "(\<And>\<omega>. f \<omega> \<le> g \<omega>) \<Longrightarrow> E_inf s f \<le> E_inf s g"
  unfolding E_inf_def by (intro INF_superset_mono order_refl nn_integral_mono)

lemma E_inf_iterate:
  assumes [measurable]: "f \<in> borel_measurable St"
  shows "E_inf s f = (\<Sqinter>D\<in>K s. \<integral>\<^sup>+ t. E_inf t (\<lambda>\<omega>. f (t ## \<omega>)) \<partial>D)"
proof -
  let ?v = "\<lambda>t. \<integral>\<^sup>+x. f (state t ## x) \<partial>T t"
  let ?p = "\<lambda>t. E_inf t (\<lambda>\<omega>. f (t ## \<omega>))"
  have "E_inf s f = (\<Sqinter>cfg\<in>cfg_on s. \<integral>\<^sup>+t. ?v t \<partial>K_cfg cfg)"
    unfolding E_inf_def by (intro INF_cong refl) (subst nn_integral_T, simp_all add: cfg_on_def)
  also have "\<dots> = (\<Sqinter>D\<in>K s. \<integral>\<^sup>+t. ?p t \<partial>D)"
  proof (intro antisym INF_greatest)
    fix cfg :: "'s cfg" assume cfg: "cfg \<in> cfg_on s"
    then show "(INF D:K s. \<integral>\<^sup>+t. ?p t \<partial>D) \<le> (\<integral>\<^sup>+ t. ?v t \<partial>K_cfg cfg)"
      by (auto simp add: E_inf_def nn_integral_K_cfg AE_measure_pmf_iff intro!: nn_integral_mono_AE INF_lower2)
  next
    fix D assume D: "D \<in> K s" show "(INF cfg : cfg_on s. \<integral>\<^sup>+ t. ?v t \<partial>K_cfg cfg) \<le> (\<integral>\<^sup>+t. ?p t \<partial>D)"
    proof (rule ereal_le_epsilon2, intro allI impI)
      fix e :: real assume "0 < e"
      have "\<forall>t\<in>D. \<exists>cfg\<in>cfg_on t. ?v cfg \<le> ?p t + e"
      proof
        fix t assume "t \<in> D"
        show "\<exists>cfg\<in>cfg_on t. ?v cfg \<le> ?p t + e"
        proof cases
          assume "?p t = \<infinity>" with cfg_on_not_empty[of t] show ?thesis
            by (auto simp del: cfg_on_not_empty)
        next
          assume p_finite: "?p t \<noteq> \<infinity>"
          note `t \<in> D`
          moreover have "(INF cfg : cfg_on t. ?v cfg) = ?p t"
            unfolding E_inf_def by (simp add: cfg_on_def)
          moreover have "0 \<le> ?p t"
            by (rule E_inf_nonneg)
          ultimately have "\<bar>INF cfg : cfg_on t. ?v cfg\<bar> \<noteq> \<infinity>"
            using p_finite by (intro ereal_infinity_cases) auto
          from INF_approx_ereal[OF `0 < e` refl this]
          show "\<exists>cfg\<in>cfg_on t. ?v cfg \<le> ?p t + e"
            by (auto simp: E_inf_def intro: less_imp_le)
        qed
      qed
      then obtain cfg' where v_cfg': "\<And>t. t \<in> D \<Longrightarrow> ?v (cfg' t) \<le> ?p t + e" and
        cfg_on_cfg': "\<And>t. t \<in> D \<Longrightarrow> cfg' t \<in> cfg_on t"
        unfolding Bex_def bchoice_iff by blast

      let ?cfg = "Cfg s D cfg'"

      have cfg: "K_cfg ?cfg = map_pmf cfg' D"
        by (auto simp add: K_cfg_def cfg_on_cfg' intro!: map_pmf_cong)

      have "?cfg \<in> cfg_on s"
        by (auto intro: D cfg_on_cfg' cfg_of_cfg_onI)
      then have "(INF cfg : cfg_on s. \<integral>\<^sup>+ t. ?v t \<partial>K_cfg cfg) \<le> (\<integral>\<^sup>+ t. ?p t + e \<partial>D)"
        by (rule INF_lower2) (auto simp: cfg map_pmf.rep_eq nn_integral_distr v_cfg' AE_measure_pmf_iff intro!: nn_integral_mono_AE)
      also have "\<dots> = (\<integral>\<^sup>+ t. ?p t \<partial>D) + e"
        using `0 < e` by (simp add: nn_integral_add E_inf_nonneg measure_pmf.emeasure_space_1[simplified])
      finally show "(INF cfg : cfg_on s. \<integral>\<^sup>+ t. ?v t \<partial>K_cfg cfg) \<le> (\<integral>\<^sup>+ t. ?p t \<partial>D) + e" .
    qed
  qed
  finally show ?thesis .
qed

definition "P_sup s P = (\<Squnion>cfg\<in>cfg_on s. emeasure (T cfg) {x\<in>space St. P x})"
definition "P_inf s P = (\<Sqinter>cfg\<in>cfg_on s. emeasure (T cfg) {x\<in>space St. P x})"

definition "E = (SIGMA s:UNIV. \<Union>D\<in>K s. set_pmf D)"

lemma P_sup_True[simp]: "P_sup t (\<lambda>\<omega>. True) = 1"
  using T.emeasure_space_1
  by (auto simp add: P_sup_def SUP_constant)

lemma P_sup_False[simp]: "P_sup t (\<lambda>\<omega>. False) = 0"
  by (auto simp add: P_sup_def SUP_constant)

lemma P_sup_SUP: 
  fixes P :: "nat \<Rightarrow> 's stream \<Rightarrow> bool"
  assumes "mono P" and P[measurable]: "\<And>i. Measurable.pred St (P i)"
  shows "P_sup s (\<lambda>x. \<exists>i. P i x) = (\<Squnion>i. P_sup s (P i))"
proof -
  have "P_sup s (\<lambda>x. \<Squnion>i. P i x) = (\<Squnion>cfg\<in>cfg_on s. emeasure (T cfg) (\<Union>i. {x\<in>space St. P i x}))"
    by (auto simp: P_sup_def intro!: SUP_cong arg_cong2[where f=emeasure])
  also have "\<dots> = (\<Squnion>cfg\<in>cfg_on s. \<Squnion>i. emeasure (T cfg) {x\<in>space St. P i x})"
    using `mono P` by (auto intro!: SUP_cong SUP_emeasure_incseq[symmetric] simp: mono_def le_fun_def)
  also have "\<dots> = (\<Squnion>i. P_sup s (P i))"
    by (subst SUP_commute) (simp add: P_sup_def)
  finally show ?thesis
    unfolding SUP_apply[abs_def] by simp
qed

lemma P_sup_lfp:
  assumes Q: "Order_Continuity.continuous Q"
  assumes f: "f \<in> measurable St M"
  assumes Q_m: "\<And>P. Measurable.pred M P \<Longrightarrow> Measurable.pred M (Q P)"
  shows "P_sup s (\<lambda>x. lfp Q (f x)) = (\<Squnion>i. P_sup s (\<lambda>x. (Q ^^ i) \<bottom> (f x)))"
  unfolding Order_Continuity.continuous_lfp[OF Q]
  apply simp
proof (rule P_sup_SUP)
  fix i show "Measurable.pred St (\<lambda>x. (Q ^^ i) \<bottom> (f x))"
    apply (intro measurable_compose[OF f])
    by (induct i) (auto intro!: Q_m)
qed (intro mono_funpow continuous_mono[OF Q] mono_compose[where f=f])

lemma P_sup_iterate:
  assumes [measurable]: "Measurable.pred St P"
  shows "P_sup s P = (\<Squnion>D\<in>K s. \<integral>\<^sup>+ t. P_sup t (\<lambda>\<omega>. P (t ## \<omega>)) \<partial>D)"
proof -
  have [simp]: "\<And>x s. indicator {x \<in> space St. P x} (x ## s) = indicator {s \<in> space St. P (x ## s)} s"
    by (auto simp: space_stream_space split: split_indicator)
  show ?thesis
    using E_sup_iterate[of "indicator {x\<in>space St. P x}" s]
    by (auto simp add: P_sup_def E_sup_def intro!: SUP_cong nn_integral_cong)
qed

end

locale Finite_Markov_Decision_Process = Markov_Decision_Process K for K :: "'s \<Rightarrow> 's pmf set" +
  fixes S :: "'s set"
  assumes S_not_empty: "S \<noteq> {}" 
  assumes S_finite: "finite S"
  assumes K_closed: "\<And>s. s \<in> S \<Longrightarrow> (\<Union>D\<in>K s. set_pmf D) \<subseteq> S"
  assumes K_finite: "\<And>s. s \<in> S \<Longrightarrow> finite (K s)"
begin

lemma action_closed: "s \<in> S \<Longrightarrow> cfg \<in> cfg_on s \<Longrightarrow> t \<in> action cfg \<Longrightarrow> t \<in> S"
  using cfg_onD_action[of cfg s] K_closed[of s] by auto

lemma set_pmf_closed: "s \<in> S \<Longrightarrow> D \<in> K s \<Longrightarrow> t \<in> D \<Longrightarrow> t \<in> S"
  using K_closed by auto

lemma E_closed: "s \<in> S \<Longrightarrow> (s, t) \<in> E \<Longrightarrow> t \<in> S"
  using K_closed by (auto simp: E_def)

definition "valid_cfg = (\<Union>s\<in>S. cfg_on s)"

lemma valid_cfgI: "s \<in> S \<Longrightarrow> cfg \<in> cfg_on s \<Longrightarrow> cfg \<in> valid_cfg"
  by (auto simp: valid_cfg_def)

lemma valid_cfgD: "cfg \<in> valid_cfg \<Longrightarrow> cfg \<in> cfg_on (state cfg)"
  by (auto simp: valid_cfg_def)

lemma 
  shows valid_cfg_state_in_S: "cfg \<in> valid_cfg \<Longrightarrow> state cfg \<in> S"
    and valid_cfg_action: "cfg \<in> valid_cfg \<Longrightarrow> s \<in> action cfg \<Longrightarrow> s \<in> S"
    and valid_cfg_cont: "cfg \<in> valid_cfg \<Longrightarrow> s \<in> action cfg \<Longrightarrow> cont cfg s \<in> valid_cfg"
  by (auto simp: valid_cfg_def intro!: bexI[of _ s] intro: action_closed)

lemma valid_K_cfg[intro]: "cfg \<in> valid_cfg \<Longrightarrow> cfg' \<in> K_cfg cfg \<Longrightarrow> cfg' \<in> valid_cfg"
  by (auto simp add: K_cfg_def set_pmf_map valid_cfg_cont)

definition "simple ct = memoryless_on (\<lambda>s. if s \<in> S then ct s else arb_act s)"

lemma simple_cfg_on[simp]: "ct \<in> Pi S K \<Longrightarrow> simple ct s \<in> cfg_on s"
  by (auto simp: simple_def intro!: memoryless_on_cfg_onI)

lemma simple_valid_cfg[simp]: "ct \<in> Pi S K \<Longrightarrow> s \<in> S \<Longrightarrow> simple ct s \<in> valid_cfg"
  by (auto intro: valid_cfgI)

lemma cont_simple[simp]: "s \<in> S \<Longrightarrow> cont (simple ct s) t = simple ct t"
  by (simp add: simple_def)

lemma state_simple[simp]: "state (simple ct s) = s"
  by (simp add: simple_def)

lemma action_simple[simp]: "s \<in> S \<Longrightarrow> action (simple ct s) = ct s"
  by (simp add: simple_def)

lemma simple_valid_cfg_iff: "ct \<in> Pi S K \<Longrightarrow> simple ct s \<in> valid_cfg \<longleftrightarrow> s \<in> S"
  using cfg_onD_state[of "simple ct s"] by (auto simp add: valid_cfg_def intro!: bexI[of _ s])

lemma Pi_closed: "ct \<in> Pi S K \<Longrightarrow> s \<in> S \<Longrightarrow> t \<in> ct s \<Longrightarrow> t \<in> S"
  using set_pmf_closed by auto

end

end
