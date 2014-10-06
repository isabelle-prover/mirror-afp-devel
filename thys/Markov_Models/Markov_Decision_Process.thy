theory Markov_Decision_Process
  imports Discrete_Time_Markov_Chain
begin

codatatype ('s, 'a) scheduler =
  Scheduler (scheduler_action: "'s \<Rightarrow> 'a") (scheduler_cont: "'s \<Rightarrow> ('s, 'a) scheduler")
datatype ('s, 'a) cfg = Cfg (cfg_scheduler: "('s, 'a) scheduler") (state: 's)

definition "action cfg = scheduler_action (cfg_scheduler cfg) (state cfg)"
definition "cont cfg s = Cfg (scheduler_cont (cfg_scheduler cfg) s) s"

lemma state_cont[simp]: "state (cont cfg s) = s"
  by (simp add: cont_def)

primcorec memoryless :: "('s \<Rightarrow> 'a) \<Rightarrow> ('s, 'a) scheduler" where
  "scheduler_cont (memoryless f) = (\<lambda>t. memoryless f)"
| "scheduler_action (memoryless f) = f"

definition "memoryless_on f s = Cfg (memoryless f) s"

lemma state_memoryless_on[simp]: "state (memoryless_on f s) = s"
  by (simp add: memoryless_on_def)
lemma action_memoryless_on[simp]: "action (memoryless_on f s) = f s"
  by (simp add: memoryless_on_def action_def)
lemma cont_memoryless_on[simp]: "cont (memoryless_on f s) t = memoryless_on f t"
  by (simp add: memoryless_on_def cont_def)

definition cfg_on :: "'s \<Rightarrow> ('s, 'a) cfg set" where
  "cfg_on s = {cfg. state cfg = s}"

lemma cfg_onD[dest]: "cfg \<in> cfg_on s \<Longrightarrow> state cfg = s"
  by (simp add: cfg_on_def)

lemma cont_cfg_on[simp, intro]: "cont cfg s \<in> cfg_on s"
  by (simp add: cfg_on_def)

lemma cfg_on_not_empty[intro, simp]: "cfg_on s \<noteq> {}"
  by auto

locale MDP_syntax =
  fixes K :: "'s \<Rightarrow> 'a \<Rightarrow> 's pmf"
begin

definition state_pmf :: "('s, 'a) cfg \<Rightarrow> 's pmf" where
  "state_pmf cfg = K (state cfg) (action cfg)"

definition K_MC :: "('s, 'a) cfg \<Rightarrow> ('s, 'a) cfg pmf" where
  "K_MC cfg = map_pmf (cont cfg) (state_pmf cfg)"

lemma nn_integral_K_MC: "(\<integral>\<^sup>+cfg. f cfg \<partial>K_MC cfg) = (\<integral>\<^sup>+s. f (cont cfg s) \<partial>state_pmf cfg)"
  by (simp add: K_MC_def map_pmf.rep_eq nn_integral_distr)

interpretation MC!: MC_syntax K_MC .

abbreviation S :: "'s stream measure" where
  "S \<equiv> stream_space (count_space UNIV)"

definition "T cfg = distr (MC.T cfg) S (smap state)"

interpretation T!: prob_space "T cfg" for cfg
  by (simp add: T_def MC.T.prob_space_distr)

lemma space_T[simp]: "space (T cfg) = space S"
  by (simp add: T_def)

lemma sets_T[simp]: "sets (T cfg) = sets S"
  by (simp add: T_def)

lemma nn_integral_T:
  assumes [measurable]: "f \<in> borel_measurable S"
  shows "(\<integral>\<^sup>+X. f X \<partial>T cfg) = (\<integral>\<^sup>+cfg'. (\<integral>\<^sup>+x. f (state cfg' ## x) \<partial>T cfg') \<partial>K_MC cfg)"
  by (simp add: T_def MC.nn_integral_T[of _ cfg] nn_integral_distr)

lemma emeasure_Collect_T:
  assumes [measurable]: "Measurable.pred S P"
  shows "emeasure (T cfg) {x\<in>space S. P x} =
    (\<integral>\<^sup>+cfg'. emeasure (T cfg') {x\<in>space S. P (state cfg' ## x)} \<partial>K_MC cfg)"
  using MC.emeasure_Collect_T[of "\<lambda>x. P (smap state x)" cfg]
  by (simp add: nn_integral_distr emeasure_Collect_distr T_def)

definition "E_sup s f = (\<Squnion>cfg\<in>cfg_on s. \<integral>\<^sup>+x. f x \<partial>T cfg)"

lemma E_sup_nonneg: "0 \<le> E_sup s f"
  by (auto intro!: SUP_upper2 nn_integral_nonneg simp: E_sup_def)

lemma E_sup_const: "0 \<le> c \<Longrightarrow> E_sup s (\<lambda>_. c) = c"
  using T.emeasure_space_1 by (simp add: E_sup_def)

lemma E_sup_mult_right:
  assumes [measurable]: "f \<in> borel_measurable S" and [simp]: "0 \<le> c"
  shows "E_sup s (\<lambda>x. c * f x) = c * E_sup s f"
  by (simp add: nn_integral_cmult E_sup_def SUP_ereal_mult_right nn_integral_nonneg)

lemma E_sup_mono:
  "(\<And>\<omega>. f \<omega> \<le> g \<omega>) \<Longrightarrow> E_sup s f \<le> E_sup s g"
  unfolding E_sup_def by (intro SUP_subset_mono order_refl nn_integral_mono)

lemma E_sup_add:
  assumes [measurable]: "f \<in> borel_measurable S" "g \<in> borel_measurable S"
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
  assumes [measurable]: "f \<in> borel_measurable S" and nn: "0 \<le> c" "\<And>x. 0 \<le> f x"
  shows "E_sup s (\<lambda>x. f x + c) = E_sup s f + c"
  by (simp add: nn nn_integral_add E_sup_def T.emeasure_space_1[simplified] nn_integral_nonneg SUP_ereal_add_left)

lemma E_sup_SUP:
  assumes [measurable]: "\<And>i. f i \<in> borel_measurable S" and [simp]: "incseq f"
  shows "E_sup s (\<lambda>x. \<Squnion>i. f i x) = (\<Squnion>i. E_sup s (f i))"
  by (auto simp add: E_sup_def nn_integral_monotone_convergence_SUP intro: SUP_commute)

lemma E_sup_iterate:
  assumes [measurable]: "f \<in> borel_measurable S"
  shows "E_sup s f = (\<Squnion>a. \<integral>\<^sup>+ t. E_sup t (\<lambda>\<omega>. f (t ## \<omega>)) \<partial>K s a)"
proof -
  let ?v = "\<lambda>t. \<integral>\<^sup>+x. f (state t ## x) \<partial>T t"
  let ?p = "\<lambda>t. E_sup t (\<lambda>\<omega>. f (t ## \<omega>))"
  have "E_sup s f = (\<Squnion>cfg\<in>cfg_on s. \<integral>\<^sup>+t. ?v t \<partial>K_MC cfg)"
    unfolding E_sup_def by (intro SUP_cong refl) (subst nn_integral_T, simp_all add: cfg_on_def)
  also have "\<dots> = (\<Squnion>a. \<integral>\<^sup>+t. ?p t \<partial>K s a)"
  proof (intro antisym SUP_least)
    fix cfg :: "('s, 'a) cfg" assume cfg: "cfg \<in> cfg_on s"
    then show "(\<integral>\<^sup>+ t. ?v t \<partial>K_MC cfg) \<le> (SUP a. \<integral>\<^sup>+t. ?p t \<partial>K s a)"
      by (auto simp add: E_sup_def state_pmf_def nn_integral_K_MC intro!: nn_integral_mono SUP_upper2)
  next
    fix a show "(\<integral>\<^sup>+t. ?p t \<partial>K s a) \<le> (SUP cfg : cfg_on s. \<integral>\<^sup>+ t. ?v t \<partial>K_MC cfg)"
    proof cases
      assume p_finite: "\<forall>t\<in>K s a. ?p t < \<infinity>"
      show ?thesis
      proof (rule ereal_le_epsilon2, intro allI impI)
        fix e :: real assume "0 < e"
        have "\<forall>t\<in>K s a. \<exists>cfg\<in>cfg_on t. ?p t \<le> ?v cfg + e"
        proof
          fix t assume "t \<in> K s a"
          moreover have "(SUP cfg : cfg_on t. ?v cfg) = ?p t"
            unfolding E_sup_def by (simp add: cfg_on_def)
          moreover have "0 \<le> ?p t"
            by (rule E_sup_nonneg)
          ultimately have "\<bar>SUP cfg : cfg_on t. ?v cfg\<bar> \<noteq> \<infinity>"
            using p_finite by (intro ereal_infinity_cases) auto
          from SUP_approx_ereal[OF `0 < e` refl this]
          show "\<exists>cfg\<in>cfg_on t. ?p t \<le> ?v cfg + e"
            by (simp add: E_sup_def cfg_onD)
        qed
        then obtain cfg' where v_cfg': "\<And>t. t \<in> K s a \<Longrightarrow> ?p t \<le> ?v (cfg' t) + e" and
          cfg_on_cfg': "\<And>t. t \<in> K s a \<Longrightarrow> cfg' t \<in> cfg_on t"
          unfolding Bex_def bchoice_iff by blast
  
        def cfg \<equiv> "Cfg (Scheduler (\<lambda>s\<in>{s}. a) (\<lambda>t. cfg_scheduler (cfg' t))) s"
        have cfg: "K_MC cfg = map_pmf cfg' (K s a)"
          apply (auto simp add: K_MC_def cfg_def state_pmf_def action_def cont_def[abs_def] fun_eq_iff
                      intro!: map_pmf_cong)
          apply (case_tac "cfg' x")
          apply (cut_tac t=x in cfg_on_cfg')
          apply (simp_all add: cfg_on_def)
          done
  
        have "(\<integral>\<^sup>+ t. ?p t \<partial>K s a) \<le> (\<integral>\<^sup>+t. ?v (cfg' t) + e \<partial>K s a)"
          by (intro nn_integral_mono_AE) (simp add: v_cfg' AE_measure_pmf_iff)
        also have "\<dots> = (\<integral>\<^sup>+t. ?v (cfg' t) \<partial>K s a) + e"
          using `0 < e` measure_pmf.emeasure_space_1[of "K s a"]
          by (subst nn_integral_add) (auto intro: cfg_on_cfg' nn_integral_nonneg)
        also have "(\<integral>\<^sup>+t. ?v (cfg' t) \<partial>K s a) = (\<integral>\<^sup>+t. ?v t \<partial>K_MC cfg)"
          by (simp add: cfg map_pmf.rep_eq nn_integral_distr)
        also have "\<dots> \<le> (SUP cfg:cfg_on s. (\<integral>\<^sup>+t. ?v t \<partial>K_MC cfg))"
          by (auto intro!: SUP_upper simp: cfg_def cfg_on_def)
        finally show "(\<integral>\<^sup>+ t. ?p t \<partial>K s a) \<le> (SUP cfg : cfg_on s. \<integral>\<^sup>+ t. ?v t \<partial>K_MC cfg) + e"
          by (blast intro: ereal_add_mono)
      qed
    next
      assume "\<not> (\<forall>t\<in>K s a. ?p t < \<infinity>)"
      then obtain t where "t \<in> K s a" "?p t = \<infinity>"
        by auto
      then have "\<infinity> = pmf (K s a) t * ?p t"
        by (auto intro!: pmf_positive)
      also have "\<dots> = (SUP cfg : cfg_on t. pmf (K s a) t * ?v cfg)"
        unfolding E_sup_def
        by (auto simp add: cfg_onD pmf_nonneg nn_integral_nonneg intro!: SUP_ereal_mult_right[symmetric])
      also have "\<dots> \<le> (SUP cfg : cfg_on s. \<integral>\<^sup>+ t. ?v t \<partial>K_MC cfg)"
        unfolding E_sup_def
      proof (intro SUP_least SUP_upper2)
        fix cfg :: "('s, 'a) cfg" assume cfg: "cfg \<in> cfg_on t"

        def C \<equiv> "Cfg (Scheduler (\<lambda>s\<in>{s}. a) (\<lambda>t. cfg_scheduler cfg)) s"
        have C: "K_MC C = map_pmf (Cfg (cfg_scheduler cfg)) (K s a)"
          by (auto simp add: K_MC_def C_def state_pmf_def action_def cont_def[abs_def] fun_eq_iff
                   intro!: map_pmf_cong)
        show "C \<in> cfg_on s"
          by (simp add: C_def cfg_on_def)
        have "ereal (pmf (K s a) t) * (\<integral>\<^sup>+ x. f (state cfg ## x) \<partial>T cfg) =
          (\<integral>\<^sup>+t'. (\<integral>\<^sup>+ x. f (state cfg ## x) \<partial>T cfg) * indicator {t} t' \<partial>K s a)"
          by (subst mult_ac)
             (simp add: nn_integral_nonneg nn_integral_cmult_indicator emeasure_pmf_single)
        also have "\<dots> = (\<integral>\<^sup>+cfg. ?v cfg * indicator {t} (state cfg) \<partial>K_MC C)"
          unfolding C using cfg
          by (auto simp add: nn_integral_distr map_pmf.rep_eq split: split_indicator
                   intro!: nn_integral_cong)
        also have "\<dots> \<le> (\<integral>\<^sup>+cfg. ?v cfg \<partial>K_MC C)"
          by (auto intro!: nn_integral_mono nn_integral_nonneg split: split_indicator)
        finally show "ereal (pmf (K s a) t) * (\<integral>\<^sup>+ x. f (state cfg ## x) \<partial>T cfg)
           \<le> (\<integral>\<^sup>+ t. \<integral>\<^sup>+ x. f (state t ## x) \<partial>T t \<partial>K_MC C)" .
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
  assumes [measurable]: "f \<in> borel_measurable S"
  shows "E_inf s f = (\<Sqinter>a. \<integral>\<^sup>+ t. E_inf t (\<lambda>\<omega>. f (t ## \<omega>)) \<partial>K s a)"
proof -
  let ?v = "\<lambda>t. \<integral>\<^sup>+x. f (state t ## x) \<partial>T t"
  let ?p = "\<lambda>t. E_inf t (\<lambda>\<omega>. f (t ## \<omega>))"
  have "E_inf s f = (\<Sqinter>cfg\<in>cfg_on s. \<integral>\<^sup>+t. ?v t \<partial>K_MC cfg)"
    unfolding E_inf_def by (intro INF_cong refl) (subst nn_integral_T, simp_all add: cfg_on_def)
  also have "\<dots> = (\<Sqinter>a. \<integral>\<^sup>+t. ?p t \<partial>K s a)"
  proof (intro antisym INF_greatest)
    fix cfg :: "('s, 'a) cfg" assume cfg: "cfg \<in> cfg_on s"
    then show "(INF a. \<integral>\<^sup>+t. ?p t \<partial>K s a) \<le> (\<integral>\<^sup>+ t. ?v t \<partial>K_MC cfg)"
      by (auto simp add: E_inf_def state_pmf_def nn_integral_K_MC intro!: nn_integral_mono INF_lower2)
  next
    fix a show "(INF cfg : cfg_on s. \<integral>\<^sup>+ t. ?v t \<partial>K_MC cfg) \<le> (\<integral>\<^sup>+t. ?p t \<partial>K s a)"
    proof (rule ereal_le_epsilon2, intro allI impI)
      fix e :: real assume "0 < e"
      have "\<forall>t\<in>K s a. \<exists>cfg\<in>cfg_on t. ?v cfg \<le> ?p t + e"
      proof
        fix t assume "t \<in> K s a"
        show "\<exists>cfg\<in>cfg_on t. ?v cfg \<le> ?p t + e"
        proof cases
          assume "?p t = \<infinity>" with cfg_on_not_empty show ?thesis
            by auto
        next
          assume p_finite: "?p t \<noteq> \<infinity>"
          note `t \<in> K s a`
          moreover have "(INF cfg : cfg_on t. ?v cfg) = ?p t"
            unfolding E_inf_def by (simp add: cfg_on_def)
          moreover have "0 \<le> ?p t"
            by (rule E_inf_nonneg)
          ultimately have "\<bar>INF cfg : cfg_on t. ?v cfg\<bar> \<noteq> \<infinity>"
            using p_finite by (intro ereal_infinity_cases) auto
          from INF_approx_ereal[OF `0 < e` refl this]
          show "\<exists>cfg\<in>cfg_on t. ?v cfg \<le> ?p t + e"
            by (auto simp add: E_inf_def cfg_onD intro: less_imp_le)
        qed
      qed
      then obtain cfg' where v_cfg': "\<And>t. t \<in> K s a \<Longrightarrow> ?v (cfg' t) \<le> ?p t + e" and
        cfg_on_cfg': "\<And>t. t \<in> K s a \<Longrightarrow> cfg' t \<in> cfg_on t"
        unfolding Bex_def bchoice_iff by blast

      def cfg \<equiv> "Cfg (Scheduler (\<lambda>s\<in>{s}. a) (\<lambda>t. cfg_scheduler (cfg' t))) s"
      have cfg: "K_MC cfg = map_pmf cfg' (K s a)"
        apply (auto simp add: K_MC_def cfg_def state_pmf_def action_def cont_def[abs_def] fun_eq_iff
                    intro!: map_pmf_cong)
        apply (case_tac "cfg' x")
        apply (cut_tac t=x in cfg_on_cfg')
        apply (simp_all add: cfg_on_def)
        done
      then have "cfg \<in> cfg_on s"
        by (simp add: cfg_on_def cfg_def)
      then have "(INF cfg : cfg_on s. \<integral>\<^sup>+ t. ?v t \<partial>K_MC cfg) \<le> (\<integral>\<^sup>+ t. ?p t + e \<partial>K s a)"
        by (rule INF_lower2) (auto simp: cfg map_pmf.rep_eq nn_integral_distr v_cfg' AE_measure_pmf_iff intro!: nn_integral_mono_AE)
      also have "\<dots> = (\<integral>\<^sup>+ t. ?p t \<partial>K s a) + e"
        using `0 < e` by (simp add: nn_integral_add E_inf_nonneg measure_pmf.emeasure_space_1[simplified])
      finally show "(INF cfg : cfg_on s. \<integral>\<^sup>+ t. ?v t \<partial>K_MC cfg) \<le> (\<integral>\<^sup>+ t. ?p t \<partial>K s a) + e" .
    qed
  qed
  finally show ?thesis .
qed

definition "P_sup s P = (\<Squnion>cfg\<in>cfg_on s. emeasure (T cfg) {x\<in>space S. P x})"
definition "P_inf s P = (\<Sqinter>cfg\<in>cfg_on s. emeasure (T cfg) {x\<in>space S. P x})"

definition "E = (SIGMA s:UNIV. \<Union>a. K s a)"

lemma P_sup_True[simp]: "P_sup t (\<lambda>\<omega>. True) = 1"
  using T.emeasure_space_1
  by (auto simp add: P_sup_def SUP_constant cfg_on_def elim!: allE[of _ "Cfg undefined t"])

lemma P_sup_False[simp]: "P_sup t (\<lambda>\<omega>. False) = 0"
  by (auto simp add: P_sup_def SUP_constant cfg_on_def elim!: allE[of _ "Cfg undefined t"])

lemma P_sup_SUP: 
  fixes P :: "nat \<Rightarrow> 's stream \<Rightarrow> bool"
  assumes "mono P" and P[measurable]: "\<And>i. Measurable.pred S (P i)"
  shows "P_sup s (\<lambda>x. \<exists>i. P i x) = (\<Squnion>i. P_sup s (P i))"
proof -
  have "P_sup s (\<lambda>x. \<Squnion>i. P i x) = (\<Squnion>cfg\<in>cfg_on s. emeasure (T cfg) (\<Union>i. {x\<in>space S. P i x}))"
    by (auto simp: P_sup_def intro!: SUP_cong arg_cong2[where f=emeasure])
  also have "\<dots> = (\<Squnion>cfg\<in>cfg_on s. \<Squnion>i. emeasure (T cfg) {x\<in>space S. P i x})"
    using `mono P` by (auto intro!: SUP_cong SUP_emeasure_incseq[symmetric] simp: mono_def le_fun_def)
  also have "\<dots> = (\<Squnion>i. P_sup s (P i))"
    by (subst SUP_commute) (simp add: P_sup_def)
  finally show ?thesis
    unfolding SUP_apply[abs_def] by simp
qed

lemma P_sup_lfp:
  assumes Q: "Order_Continuity.continuous Q"
  assumes f: "f \<in> measurable S M"
  assumes Q_m: "\<And>P. Measurable.pred M P \<Longrightarrow> Measurable.pred M (Q P)"
  shows "P_sup s (\<lambda>x. lfp Q (f x)) = (\<Squnion>i. P_sup s (\<lambda>x. (Q ^^ i) \<bottom> (f x)))"
  unfolding Order_Continuity.continuous_lfp[OF Q]
  apply simp
proof (rule P_sup_SUP)
  fix i show "Measurable.pred S (\<lambda>x. (Q ^^ i) \<bottom> (f x))"
    apply (intro measurable_compose[OF f])
    by (induct i) (auto intro!: Q_m)
qed (intro mono_funpow continuous_mono[OF Q] mono_compose[where f=f])

lemma P_sup_iterate:
  assumes [measurable]: "Measurable.pred S P"
  shows "P_sup s P = (\<Squnion>a. \<integral>\<^sup>+ t. P_sup t (\<lambda>\<omega>. P (t ## \<omega>)) \<partial>K s a)"
proof -
  have [simp]: "\<And>x s. indicator {x \<in> space S. P x} (x ## s) = indicator {s \<in> space S. P (x ## s)} s"
    by (auto simp: space_stream_space split: split_indicator)
  show ?thesis
    using E_sup_iterate[of "indicator {x\<in>space S. P x}" s]
    by (auto simp add: P_sup_def E_sup_def intro!: SUP_cong nn_integral_cong)
qed

end

locale Reachability_Problem = MDP_syntax K for K :: "'s \<Rightarrow> 'a \<Rightarrow> 's pmf" +
  fixes B :: "'s set"
begin

definition F_sup :: "('s \<Rightarrow> ereal) \<Rightarrow> 's \<Rightarrow> ereal" where
  "F_sup f s = (if s \<in> B then 1 else SUP a. \<integral>\<^sup>+t. f t \<partial>K s a)"

lemma continuous_F_sup: "Order_Continuity.continuous F_sup"
  unfolding Order_Continuity.continuous_def fun_eq_iff F_sup_def[abs_def]
  by (auto simp:  SUP_apply[abs_def] nn_integral_monotone_convergence_SUP intro: SUP_commute)

lemma mono_F_sup: "mono F_sup"
  by (intro continuous_mono continuous_F_sup)

lemma F_sup_nonneg: "0 \<le> F_sup F s"
  by (auto simp: F_sup_def intro!: SUP_upper2 nn_integral_nonneg)

lemma lfp_F_sup_iterate: "lfp F_sup = (SUP i. (F_sup ^^ i) (\<lambda>x. 0))"
proof -
  have "(SUP i. (F_sup ^^ i) \<bottom>) = (SUP i. (F_sup ^^ i) (\<lambda>x. 0))"
  proof (rule SUP_eq)
    fix i show "\<exists>j\<in>UNIV. (F_sup ^^ i) \<bottom> \<le> (F_sup ^^ j) (\<lambda>x. 0)"
      by (intro bexI[of _ i] funpow_mono mono_F_sup) auto
    show "\<exists>j\<in>UNIV. (F_sup ^^ i) (\<lambda>x. 0) \<le> (F_sup ^^ j) \<bottom>"
      by (auto intro!: exI[of _ "Suc i"] funpow_mono mono_F_sup 
               simp del: funpow.simps simp add: funpow_Suc_right F_sup_nonneg le_funI)
  qed
  then show ?thesis
    by (auto simp: continuous_lfp continuous_F_sup)
qed

lemma lfp_F_sup: "lfp F_sup = (\<lambda>s. P_sup s (\<lambda>\<omega>. ev (holds (\<lambda>s. s \<in> B)) (s ## \<omega>)))"
proof
  fix s
  have "P_sup s (\<lambda>\<omega>. ev (holds (\<lambda>s. s \<in> B)) (s ## \<omega>)) =
    (\<Squnion>i. P_sup s (\<lambda>\<omega>. ((\<lambda>P \<omega>. shd \<omega> \<in> B \<or> P (stl \<omega>)) ^^ i) \<bottom> (s ## \<omega>)))"
  proof (simp add: ev_def, rule P_sup_lfp)
    show "op ## s \<in> measurable S S"
      by simp
    (* This proof should work automatically *)
    fix P assume P: "Measurable.pred S P"
    show "Measurable.pred S (\<lambda>x. shd x \<in> B \<or> P (stl x))"
      by (intro pred_intros_logic measurable_compose[OF _ P] measurable_compose[OF measurable_shd]) auto
  qed (auto simp: Order_Continuity.continuous_def)
  also have "\<dots> = (SUP i. (F_sup ^^ i) (\<lambda>x. 0) s)"
  proof (rule SUP_cong)
    fix i show "P_sup s (\<lambda>\<omega>. ((\<lambda>P \<omega>. shd \<omega> \<in> B \<or> P (stl \<omega>)) ^^ i) \<bottom> (s##\<omega>)) = (F_sup ^^ i) (\<lambda>x. 0) s"
    proof (induct i arbitrary: s) 
      case 0 then show ?case by simp
    next
      case (Suc n) show ?case
      proof (subst P_sup_iterate)
        (* This proof should work automatically *)
        show "Measurable.pred S (\<lambda>\<omega>. ((\<lambda>P \<omega>. shd \<omega> \<in> B \<or> P (stl \<omega>)) ^^ Suc n) \<bottom> (s ## \<omega>))"
          apply (intro measurable_compose[OF measurable_Stream[OF measurable_const measurable_ident_sets[OF refl]] measurable_predpow])
          apply simp
          apply (simp add: bot_fun_def[abs_def])
          apply (intro pred_intros_logic measurable_compose[OF measurable_stl]  measurable_compose[OF measurable_shd])
          apply auto
          done
      next
        show "(\<Squnion>a. \<integral>\<^sup>+ t. P_sup t (\<lambda>\<omega>. ((\<lambda>P \<omega>. shd \<omega> \<in> B \<or> P (stl \<omega>)) ^^ Suc n) \<bottom> (s ## t ## \<omega>)) \<partial>measure_pmf (K s a)) =
          (F_sup ^^ Suc n) (\<lambda>x. 0) s"
          by (simp add: F_sup_def[of _ s] measure_pmf.emeasure_space_1[simplified] Suc)
      qed
    qed
  qed simp
  finally show "lfp F_sup s = P_sup s (\<lambda>\<omega>. ev (holds (\<lambda>s. s \<in> B)) (s ## \<omega>))"
    by (simp add: lfp_F_sup_iterate)
qed

end

end
