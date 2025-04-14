(* Title:      Kolmogorov_Chentsov/Kolmogorov_Chentsov_Extras.thy
   Author:     Christian Pardillo Laursen, University of York
*)

section "Supporting lemmas"

theory Kolmogorov_Chentsov_Extras
  imports "HOL-Probability.Probability"
begin

lemma atLeastAtMost_induct[consumes 1, case_names base Suc]:
  assumes "x \<in> {n..m}"
    and "P n"
    and "\<And>k. \<lbrakk>k \<ge> n; k < m; P k\<rbrakk> \<Longrightarrow> P (Suc k)"
  shows "P x"
  by (smt (verit, ccfv_threshold) assms Suc_le_eq atLeastAtMost_iff dec_induct le_trans)

lemma eventually_prodI':
  assumes "eventually P F" "eventually Q G" "\<forall>x y. P x \<longrightarrow> Q y \<longrightarrow> R (x,y)"
  shows "eventually R (F \<times>\<^sub>F G)"
  using assms eventually_prod_filter by blast

text \<open> Analogous to @{thm AE_E3}\<close>
lemma AE_I3:
  assumes "\<And>x. x \<in> space M - N \<Longrightarrow> P x" "N \<in> null_sets M"
  shows "AE x in M. P x"
  by (metis (no_types, lifting) assms DiffI eventually_ae_filter mem_Collect_eq subsetI)

text \<open>Extends @{thm tendsto_dist}\<close>
lemma tendsto_dist_prod:
  fixes l m :: "'a :: metric_space"
  assumes f: "(f \<longlongrightarrow> l) F"
    and g: "(g \<longlongrightarrow> m) G"
  shows "((\<lambda>x. dist (f (fst x)) (g (snd x))) \<longlongrightarrow> dist l m) (F \<times>\<^sub>F G)"
proof (rule tendstoI)
  fix e :: real assume "0 < e"
  then have e2: "0 < e/2" by simp
  show "\<forall>\<^sub>F x in F \<times>\<^sub>F G. dist (dist (f (fst x)) (g (snd x))) (dist l m) < e"
    using tendstoD [OF f e2] tendstoD [OF g e2] apply (rule eventually_prodI')
    apply simp
    by (smt (verit) dist_commute dist_norm dist_triangle real_norm_def)
qed

lemma borel_measurable_at_within_metric [measurable]:
  fixes f :: "'a :: first_countable_topology \<Rightarrow> 'b \<Rightarrow> 'c :: metric_space"
  assumes [measurable]: "\<And>t. t \<in> S \<Longrightarrow> f t \<in> borel_measurable M"
    and convergent: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> \<exists>l. ((\<lambda>t. f t \<omega>) \<longlongrightarrow> l) (at x within S)"
    and nontrivial: "at x within S \<noteq> \<bottom>"
  shows "(\<lambda>\<omega>. Lim (at x within S) (\<lambda>t. f t \<omega>)) \<in> borel_measurable M"
proof -
  obtain l where l: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> ((\<lambda>t. f t \<omega>) \<longlongrightarrow> l \<omega>) (at x within S)"
    using convergent by metis
  then have Lim_eq: "Lim (at x within S) (\<lambda>t. f t \<omega>) = l \<omega>"
    if "\<omega> \<in> space M" for \<omega>
    using tendsto_Lim[OF nontrivial] that by blast
  from nontrivial have 1: "x islimpt S"
    using trivial_limit_within by blast
  then obtain s :: "nat \<Rightarrow> 'a" where s: "\<And>n. s n \<in> S - {x}" "s \<longlonglongrightarrow> x"
    using islimpt_sequential by blast
  then have "\<And>n. f (s n) \<in> borel_measurable M"
    using s by simp
  moreover have "(\<lambda>n. (f (s n) \<omega>)) \<longlonglongrightarrow> l \<omega>" if "\<omega> \<in> space M" for \<omega>
    using s l[unfolded tendsto_at_iff_sequentially comp_def, OF that]
    by blast
  ultimately have "l \<in> borel_measurable M"
    by (rule borel_measurable_LIMSEQ_metric)
  then show ?thesis
    using measurable_cong[OF Lim_eq] by fast
qed

lemma Max_finite_image_ex:
  assumes "finite S" "S \<noteq> {}" "P (MAX k\<in>S. f k)" 
  shows "\<exists>k \<in> S. P (f k)"
  using bexI[of P "Max (f ` S)" "f ` S"] by (simp add: assms)

lemma measure_leq_emeasure_ennreal: "0 \<le> x \<Longrightarrow> emeasure M A \<le> ennreal x \<Longrightarrow> measure M A \<le> x"
  apply (cases "A \<in> M")
   apply (metis Sigma_Algebra.measure_def enn2real_leI)
  apply (auto simp: measure_notin_sets emeasure_notin_sets)
  done

lemma Union_add_subset: "(m :: nat) \<le> n \<Longrightarrow> (\<Union>k. A (k + n)) \<subseteq> (\<Union>k. A (k + m))"
  apply (subst subset_eq)
  apply simp
  apply (metis add.commute le_iff_add trans_le_add1)
  done

lemma floor_in_Nats [simp]: "x \<ge> 0 \<Longrightarrow> \<lfloor>x\<rfloor> \<in> \<nat>"
  by (metis nat_0_le of_nat_in_Nats zero_le_floor)

lemma triangle_ineq_list:
  fixes l :: "('a :: metric_space) list"
  assumes "l \<noteq> []"
  shows "dist (hd l) (last l) \<le> (\<Sum> i=1..length l - 1. dist (l!i) (l!(i-1)))"
  using assms proof (induct l rule: rev_nonempty_induct)
  case (single x)
  then show ?case by force
next
  case (snoc x xs)
  define S :: "'a list \<Rightarrow> real" where
    "S \<equiv> \<lambda>l. (\<Sum> i=1..length l - 1. dist (l!i) (l!(i-1)))"
  have "S (xs @ [x]) = dist x (last xs) + S xs"
    unfolding S_def apply simp
    apply (subst sum.last_plus)
     apply (simp add: Suc_leI snoc.hyps(1))
    apply (rule arg_cong2[where f="(+)"])
     apply (simp add: last_conv_nth nth_append snoc.hyps(1))
    apply (rule sum.cong)
     apply fastforce
    by (smt (verit) Suc_pred atLeastAtMost_iff diff_is_0_eq less_Suc_eq nat_less_le not_less nth_append)
  moreover have "dist (hd xs) (last xs) \<le> S xs"
    unfolding S_def using snoc by blast
  ultimately have "dist (hd xs) x \<le> S (xs@[x])"
    by (smt (verit) dist_triangle2)
  then show ?case
    unfolding S_def using snoc by simp    
qed

lemma triangle_ineq_sum:
  fixes f :: "nat \<Rightarrow> 'a :: metric_space"
  assumes "n \<le> m"
  shows "dist (f n) (f m) \<le> (\<Sum> i=Suc n..m. dist (f i) (f (i-1)))"
proof (cases "n=m")
  case True
  then show ?thesis by simp
next
  case False
  then have "n < m"
    using assms by simp
  define l where "l \<equiv> map (f o nat) [n..m]"
  have [simp]: "l \<noteq> []"
    using \<open>n < m\<close> l_def by fastforce
  have [simp]: "length l = m - n +1"
    unfolding l_def apply simp
    using assms by linarith
  with l_def have "hd l = f n"
    by (simp add: assms upto.simps)
  moreover have "last l = f m"
    unfolding l_def apply (subst last_map)
    using assms apply force
    using \<open>n < m\<close> upto_rec2 by force
  ultimately have "dist (f n) (f m) = dist (hd l) (last l)"
    by simp
  also have "... \<le>  (\<Sum> i=1..length l - 1. dist (l!i) (l!(i-1)))"
    by (rule triangle_ineq_list[OF \<open>l \<noteq> []\<close>])
  also have "... = (\<Sum> i=Suc n..m. dist (f i) (f (i-1)))"
    apply (rule sum.reindex_cong[symmetric, where l="(+) n"])
    using inj_on_add apply blast
     apply (simp add: assms)
    apply (rule arg_cong2[where f=dist])
     apply simp_all
    unfolding l_def apply (subst nth_map, fastforce)
     apply (subst nth_upto, linarith)
    subgoal by simp (insert nat_int_add, presburger)
    apply (subst nth_map, fastforce)
    apply (subst nth_upto, linarith)
    by (simp add: add_diff_eq nat_int_add nat_diff_distrib')
  finally show ?thesis
    by blast
qed

lemma (in product_prob_space) indep_vars_PiM_coordinate:
  assumes "I \<noteq> {}"
  shows "prob_space.indep_vars (\<Pi>\<^sub>M i\<in>I. M i) M (\<lambda>x f. f x) I"
proof -
  have "distr (Pi\<^sub>M I M) (Pi\<^sub>M I M) (\<lambda>x. restrict x I) = distr (Pi\<^sub>M I M) (Pi\<^sub>M I M) (\<lambda>x. x)"
    by (rule distr_cong; simp add: space_PiM)
  also have "... = PiM I M"
    by simp
  also have "... = Pi\<^sub>M I (\<lambda>i. distr (Pi\<^sub>M I M) (M i) (\<lambda>f. f i))"
    using PiM_component by (intro PiM_cong, auto)
  finally have "distr (Pi\<^sub>M I M) (Pi\<^sub>M I M) (\<lambda>x. restrict x I) = Pi\<^sub>M I (\<lambda>i. distr (Pi\<^sub>M I M) (M i) (\<lambda>f. f i))"
    .
  then show ?thesis
    using assms by (simp add: indep_vars_iff_distr_eq_PiM')
qed 

lemma (in prob_space) indep_sets_indep_set:
  assumes "indep_sets F I" "i \<in> I" "j \<in> I" "i \<noteq> j"
  shows "indep_set (F i) (F j)"
  unfolding indep_set_def
proof (rule indep_setsI)
  show "(case x of True \<Rightarrow> F i | False \<Rightarrow> F j) \<subseteq> events" for x
    using assms by (auto split: bool.split simp: indep_sets_def)
  fix A J assume *: "J \<noteq> {}" "J \<subseteq> UNIV" "\<forall>ja\<in>J. A ja \<in> (case ja of True \<Rightarrow> F i | False \<Rightarrow> F j)"
  {
    assume "J = UNIV"
    then have "indep_sets F I" "{i,j} \<subseteq> I" "{i, j} \<noteq> {}" "finite {i,j}" "\<forall>x \<in> {i,j}. (\<lambda>x. if x = i then A True else A False) x \<in> F x"
      using * assms apply simp_all
      by (simp add: bool.split_sel)
    then have "prob (\<Inter>j\<in>{i, j}. if j = i then A True else A False) = (\<Prod>j\<in>{i, j}. prob (if j = i then A True else A False))"
      by (rule indep_setsD)
    then have "prob (A True \<inter> A False) = prob (A True) * prob (A False)"
      using assms by (auto simp: ac_simps)
  } note X = this
  consider "J = {True, False}" | "J = {False}" | "J = {True}"
    using *(1,2) unfolding UNIV_bool by blast
  then show "prob (\<Inter> (A ` J)) = (\<Prod>j\<in>J. prob (A j))"
    using X by (cases; auto)
qed

lemma (in prob_space) indep_vars_indep_var:
  assumes "indep_vars M' X I" "i \<in> I" "j \<in> I" "i \<noteq> j"
  shows "indep_var (M' i) (X i) (M' j) (X j)"
  using assms unfolding indep_vars_def indep_var_eq
  by (meson indep_sets_indep_set)

end
