section \<open>Expander Walks as Pseudorandom Objects\<close>

theory Pseudorandom_Objects_Expander_Walks
  imports
    Universal_Hash_Families.Pseudorandom_Objects
    Expander_Graphs.Expander_Graphs_Strongly_Explicit
begin

unbundle intro_cong_syntax
hide_const (open) Quantum.T
hide_fact (open) SN_Orders.of_nat_mono

definition expander_pro ::
  "nat \<Rightarrow> real \<Rightarrow> ('a,'b) pseudorandom_object_scheme \<Rightarrow> (nat \<Rightarrow> 'a) pseudorandom_object"
  where "expander_pro l \<Lambda> S = (
    let e = see_standard (pro_size S) \<Lambda> in
      \<lparr> pro_last = see_size e * see_degree e^(l-1) - 1,
        pro_select = (\<lambda>i j. pro_select S (see_sample_walk e (l-1) i ! j mod pro_size S)) \<rparr>
    )"

open_bundle expander_pseudorandom_object_syntax
begin
notation expander_pro (\<open>\<E>\<close>)
end

unbundle expander_pseudorandom_object_syntax

context
  fixes l :: nat
  fixes \<Lambda> :: real
  fixes P :: "'a pseudorandom_object"
  assumes l_gt_0: "l > 0"
  assumes \<Lambda>_gt_0: "\<Lambda> > 0"
begin

private definition e where "e = see_standard (pro_size P) \<Lambda>"

private lemma expander_pro_alt:
  "expander_pro l \<Lambda> P =
    \<lparr> pro_last = see_size e * see_degree e^(l-1) - 1,
      pro_select = (\<lambda>i j. pro_select P (see_sample_walk e (l-1) i ! j mod pro_size P)) \<rparr>"
  unfolding expander_pro_def e_def[symmetric] by (auto simp:Let_def)

private lemmas see_standard = see_standard [OF pro_size_gt_0[where S="P"] \<Lambda>_gt_0]

interpretation E: regular_graph "graph_of e"
  using see_standard(1) unfolding is_expander_def e_def by auto

private lemma e_deg_gt_0: "see_degree e > 0"
  unfolding e_def see_standard by simp

private lemma e_size_gt_0: "see_size e > 0"
  unfolding e_def using see_standard pro_size_gt_0 by simp

private lemma expander_sample_size: "pro_size (\<E> l \<Lambda> P) =  see_size e * see_degree e^(l-1)"
  using e_deg_gt_0 e_size_gt_0 unfolding expander_pro_alt pro_size_def by simp

private lemma sample_pro_expander_walks:
  defines "R \<equiv> map_pmf (\<lambda>xs i. pro_select P (xs ! i mod pro_size P))
    (pmf_of_multiset (walks (graph_of e) l))"
  shows "sample_pro (expander_pro l \<Lambda> P) = R"
proof -
  let ?S = "{..<see_size e * see_degree e ^ (l-1)}"
  let ?T = "(map_pmf (see_sample_walk e (l-1)) (pmf_of_set ?S))"

  have "0 \<in> ?S"
    using e_size_gt_0 e_deg_gt_0  by auto
  hence "?S \<noteq> {}"
    by blast
  hence "?T = pmf_of_multiset {#see_sample_walk e (l-1) i. i \<in># mset_set ?S#}"
    by (subst map_pmf_of_set) simp_all
  also have "\<dots> = pmf_of_multiset (walks' (graph_of e) (l-1))"
    by (subst see_sample_walk) auto
  also have "\<dots> = pmf_of_multiset (walks (graph_of e) l)"
    unfolding walks_def using l_gt_0 by (cases l, simp_all)
  finally have 0:"?T = pmf_of_multiset (walks (graph_of e) l)"
    by simp

  have "sample_pro (expander_pro l \<Lambda> P) = map_pmf (\<lambda>xs j. pro_select P (xs ! j mod pro_size P)) ?T"
    unfolding expander_sample_size sample_pro_alt unfolding map_pmf_comp expander_pro_alt by simp
  also have "\<dots> = R" unfolding 0 R_def by simp
  finally show ?thesis by simp
qed

lemma expander_pro_range: "pro_select (expander_pro l \<Lambda> P) i j \<in> pro_set P"
  unfolding expander_pro_alt by (simp add:pro_select_in_set)

lemma expander_uniform_property:
  assumes "i < l"
  shows "map_pmf (\<lambda>w. w i) (sample_pro (expander_pro l \<Lambda> P)) = sample_pro P" (is "?L = ?R")
proof -
  have "?L = map_pmf (\<lambda>x. pro_select P (x mod pro_size P)) (map_pmf (\<lambda>xs. (xs ! i)) (pmf_of_multiset (walks (graph_of e) l)))"
    unfolding sample_pro_expander_walks by (simp add: map_pmf_comp)
  also have "\<dots> = map_pmf (\<lambda>x. pro_select P (x mod pro_size P)) (pmf_of_set (verts (graph_of e)))"
    unfolding E.uniform_property[OF assms] by simp
  also have "\<dots> = ?R"
    using pro_size_gt_0 unfolding sample_pro_alt
    by (intro map_pmf_cong) (simp_all add:e_def graph_of_def see_standard select_def)
  finally show ?thesis
    by simp
qed

lemma expander_kl_chernoff_bound:
  assumes "measure (sample_pro P) {w. T w} \<le> \<mu>"
  assumes "c \<le> 1" "\<mu> + \<Lambda> * (1-\<mu>) \<le> c" "\<mu> \<le> 1"
  shows "measure (sample_pro (expander_pro l \<Lambda> P)) {w. real (card {i \<in> {..<l}. T (w i)}) \<ge> c*l}
    \<le> exp (- real l * KL_div c (\<mu> + \<Lambda>*(1-\<mu>)))" (is "?L \<le> ?R")
proof (cases "measure (sample_pro P) {w. T w} > 0")
  case True
  let ?w = "pmf_of_multiset (walks (graph_of e) l)"
  define V where "V = {v\<in> verts (graph_of e). T (pro_select P v)} "
  define \<nu> where "\<nu> = measure (sample_pro P) {w. T w}"

  have \<nu>_gt_0: "\<nu> > 0" unfolding \<nu>_def using True by simp
  have \<nu>_le_1: "\<nu> \<le> 1" unfolding \<nu>_def by simp
  have \<nu>_le_\<mu>: "\<nu> \<le> \<mu>" unfolding \<nu>_def using assms(1) by simp

  have 0: "card {i \<in> {..<l}. T (pro_select P (w ! i mod pro_size P))} = card {i \<in> {..<l}. w ! i \<in> V}"
    if "w  \<in> set_pmf (pmf_of_multiset (walks (graph_of e) l))" for w
  proof -
    have a0: "w \<in># walks (graph_of e) l" using that E.walks_nonempty by simp
    have a1:"w ! i \<in> verts (graph_of e)" if "i < l" for i
      using that E.set_walks_3[OF a0] by auto
    moreover have "w ! i mod pro_size P = w ! i" if "i < l" for i
      using a1[OF that] see_standard(2) e_def by (simp add:graph_of_def)
    ultimately show ?thesis
      unfolding V_def
      by (intro arg_cong[where f="card"] restr_Collect_cong) auto
  qed

  have 1:"E.\<Lambda>\<^sub>a \<le> \<Lambda>"
    using see_standard(1) unfolding is_expander_def e_def by simp

  have 2: "V \<subseteq> verts (graph_of e)"
    unfolding V_def by simp

  have "\<nu> = measure (pmf_of_set {..<pro_size P}) ({v. T (pro_select P v)})"
    unfolding \<nu>_def sample_pro_alt by simp
  also have "\<dots> = real (card ({v\<in>{..<pro_size P}. T (pro_select P v)})) / real (pro_size P)"
    using pro_size_gt_0 by (subst measure_pmf_of_set) (auto simp add:Int_def)
  also have "\<dots> = real (card V) / card (verts (graph_of e))"
    unfolding V_def graph_of_def e_def using see_standard by (simp add:Int_commute)
  finally have \<nu>_eq: "\<nu> = real (card V) / card (verts (graph_of e))"
    by simp

  have 3: "0 < \<nu> + E.\<Lambda>\<^sub>a * (1 - \<nu>)"
    using \<nu>_le_1 by (intro add_pos_nonneg \<nu>_gt_0 mult_nonneg_nonneg E.\<Lambda>_ge_0) auto

  have "\<nu> + E.\<Lambda>\<^sub>a * (1 - \<nu>) = \<nu> * (1 - E.\<Lambda>\<^sub>a) + E.\<Lambda>\<^sub>a" by (simp add:algebra_simps)
  also have "\<dots> \<le> \<mu> * (1- E.\<Lambda>\<^sub>a) + E.\<Lambda>\<^sub>a" using E.\<Lambda>_le_1
    by (intro add_mono mult_right_mono \<nu>_le_\<mu>) auto
  also have "\<dots> = \<mu> + E.\<Lambda>\<^sub>a * (1 - \<mu>)" by (simp add:algebra_simps)
  also have "\<dots> \<le> \<mu> + \<Lambda> * (1 - \<mu>)" using assms(4) by (intro add_mono mult_right_mono 1) auto
  finally have 4: "\<nu> + E.\<Lambda>\<^sub>a * (1 - \<nu>) \<le> \<mu> + \<Lambda> * (1 - \<mu>)" by simp

  have 5: "\<nu> + E.\<Lambda>\<^sub>a*(1-\<nu>) \<le> c" using 4 assms(3) by simp

  have "?L = measure ?w {y. c * real l \<le> real (card {i \<in> {..<l}. T (pro_select P (y ! i mod pro_size P))})}"
    unfolding sample_pro_expander_walks by simp
  also have "\<dots> = measure ?w {y. c * real l \<le> real (card {i \<in> {..<l}. y ! i \<in> V})}"
    using 0 by (intro measure_pmf_cong) (simp)
  also have "\<dots> \<le> exp (- real l * KL_div c (\<nu> + E.\<Lambda>\<^sub>a*(1-\<nu>)) )"
    using assms(2) 3 5 unfolding \<nu>_eq by (intro E.kl_chernoff_property l_gt_0 2) auto
  also have "\<dots> \<le> exp (- real l * KL_div c (\<mu> + \<Lambda>*(1-\<mu>)))"
    using l_gt_0 by (intro iffD2[OF exp_le_cancel_iff] iffD2[OF mult_le_cancel_left_neg]
      KL_div_mono_right[OF disjI2] conjI 3 4 assms(2,3)) auto
  finally show ?thesis by simp
next
  case False
  hence 0:"measure (sample_pro P) {w. T w} = 0" using zero_less_measure_iff by blast
  hence 1:"T w = False" if "w \<in> pro_set P" for w using that measure_pmf_posI by force

  have "\<mu> + \<Lambda> * (1-\<mu>) > 0"
  proof (cases "\<mu> = 0")
    case True then show ?thesis using \<Lambda>_gt_0 by auto
  next
    case False
    then show ?thesis using assms(1,4) 0 \<Lambda>_gt_0
      by (intro add_pos_nonneg mult_nonneg_nonneg) simp_all
  qed
  hence "c > 0" using assms(3) by auto
  hence 2:"c*real l > 0" using l_gt_0 by simp

  let ?w = "pmf_of_multiset (walks (graph_of e) l)"

  have "?L = measure ?w {y. c*real l\<le> card {i \<in> {..<l}. T (pro_select P (y ! i mod pro_size P))}}"
    unfolding sample_pro_expander_walks by simp
  also have "\<dots> = 0" using pro_select_in_set 2 by (subst 1) auto
  also have "\<dots> \<le> ?R" by simp
  finally show ?thesis by simp
qed

lemma expander_pro_size:
  "pro_size (expander_pro l \<Lambda> P) = pro_size P * (16 ^ ((l-1) * nat \<lceil>ln \<Lambda> / ln (19 / 20)\<rceil>))"
  (is "?L = ?R")
proof -
  have "?L = see_size e * see_degree e ^ (l - 1)"
    unfolding expander_sample_size by simp
  also have "\<dots> = pro_size P * (16 ^ nat \<lceil>ln \<Lambda> / ln (19 / 20)\<rceil>) ^ (l - 1)"
    using see_standard unfolding e_def by simp
  also have "\<dots> = pro_size P * (16 ^ ((l-1) * nat \<lceil>ln \<Lambda> / ln (19 / 20)\<rceil>))"
    unfolding power_mult[symmetric] by (simp add:ac_simps)
  finally show ?thesis
    by simp
qed

context
  fixes \<gamma> :: real
  assumes \<gamma>_ge_0: "\<gamma> \<ge> 0"
begin

lemma expander_chernoff_bound_one_sided:
  assumes "AE x in sample_pro P. f x \<in> {0,1::real}"
  assumes "(\<integral>x. f x \<partial>sample_pro P) \<le> \<mu>"
  shows "measure (expander_pro l \<Lambda> P) {w. (\<Sum>i<l. f (w i))/l-\<mu>\<ge>\<gamma>+\<Lambda>} \<le> exp (- 2 * real l * \<gamma>^2)"
    (is "?L \<le> ?R")
proof -
  let ?w = "sample_pro (expander_pro l \<Lambda> P)"
  define T where "T x = (f x=1)" for x

  have 1: "indicator {w. T w} x = f x" if "x \<in> pro_set P" for x
  proof -
    have "f x \<in> {0,1}" using assms(1) that unfolding AE_measure_pmf_iff by simp
    thus ?thesis unfolding T_def by auto
  qed

  have "measure P {w. T w} = (\<integral>x. indicator {w. T w} x \<partial>P)" by simp
  also have "\<dots> = (\<integral>x. f x \<partial>P)" using 1 by (intro integral_cong_AE AE_pmfI) auto
  also have "\<dots> \<le> \<mu>" using assms(2) by simp
  finally have 0: "measure P {w. T w} \<le> \<mu>" by simp

  hence \<mu>_ge_0: "\<mu> \<ge> 0" using measure_nonneg order.trans by blast

  have cases: "(\<gamma>=0 \<Longrightarrow> p) \<Longrightarrow> (\<gamma>+\<Lambda>+\<mu> > 1  \<Longrightarrow> p) \<Longrightarrow> (\<gamma>+\<Lambda>+\<mu> \<le> 1 \<and> \<gamma> > 0 \<Longrightarrow> p) \<Longrightarrow> p" for p
    using \<gamma>_ge_0 by argo

  have "?L = measure ?w {w. (\<gamma>+\<Lambda>+\<mu>)*l \<le> (\<Sum>i<l. f (w i))}"
    using l_gt_0 by (intro measure_pmf_cong) (auto simp:field_simps)
  also have "\<dots> = measure ?w {w. (\<gamma>+\<Lambda>+\<mu>)*l \<le> card {i \<in> {..<l}. T (w i)}}"
  proof (rule measure_pmf_cong)
    fix \<omega>
    assume "\<omega> \<in> pro_set (expander_pro l \<Lambda> P)"
    hence "\<omega> x \<in> pro_set P" for x using expander_pro_range set_sample_pro by (metis image_iff)
    hence "(\<Sum>i<l. f (\<omega> i)) = (\<Sum>i<l. indicator {w. T w} (\<omega> i))" using 1 by (intro sum.cong) auto
    also have "\<dots> = card {i \<in> {..<l}. T (\<omega> i)}" unfolding indicator_def by (auto simp:Int_def)
    finally have "(\<Sum>i<l. f (\<omega> i)) = (card {i \<in> {..<l}. T (\<omega> i)})" by simp
    thus "(\<omega> \<in> {w. (\<gamma>+\<Lambda>+\<mu>)*l \<le> (\<Sum>i<l. f (w i))})=(\<omega> \<in> {w. (\<gamma>+\<Lambda>+\<mu>)*l\<le>card {i \<in> {..<l}. T (w i)}})"
      by simp
  qed
  also have "\<dots> \<le> ?R" (is "?L1 \<le> _")
  proof (rule cases)
    assume "\<gamma> = 0" thus "?thesis" by simp
  next
    assume a:"\<gamma> + \<Lambda> + \<mu> \<le> 1 \<and> 0 < \<gamma>"
    hence \<mu>_lt_1: "\<mu> < 1" using \<gamma>_ge_0 \<Lambda>_gt_0 by simp
    hence \<mu>_le_1: "\<mu> \<le> 1" by simp
    have "\<mu> + \<Lambda> * (1 - \<mu>) \<le> \<mu> + \<Lambda> * 1" using \<mu>_ge_0 \<Lambda>_gt_0 by (intro add_mono mult_left_mono) auto
    also have "\<dots> < \<gamma>+\<Lambda>+\<mu>" using \<gamma>_ge_0 a by simp
    finally have b:"\<mu> + \<Lambda> * (1 - \<mu>) < \<gamma> +\<Lambda> +\<mu>" by simp
    hence "\<mu> + \<Lambda> * (1 - \<mu>) < 1" using a by simp
    moreover have "\<mu> + \<Lambda> * (1 - \<mu>) > 0" using \<mu>_lt_1
      by (intro add_nonneg_pos \<mu>_ge_0 mult_pos_pos \<Lambda>_gt_0) simp
    ultimately have c: "\<mu> + \<Lambda> * (1 - \<mu>) \<in> {0<..<1}" by simp
    have d: " \<gamma> + \<Lambda> + \<mu> \<in> {0..1}" using a b c by simp
    have "?L1 \<le> exp (- real l * KL_div (\<gamma>+\<Lambda>+\<mu>) (\<mu> + \<Lambda>*(1-\<mu>)))"
      using a b by (intro expander_kl_chernoff_bound \<mu>_le_1 0) auto
    also have "\<dots> \<le> exp (- real l * (2 * ((\<gamma>+\<Lambda>+\<mu>)- (\<mu> + \<Lambda>*(1-\<mu>)))^2))"
      by (intro iffD2[OF exp_le_cancel_iff] mult_left_mono_neg KL_div_lower_bound c d) simp
    also have "\<dots> \<le> exp (- real l * (2 * (\<gamma>^2)))"
      using \<gamma>_ge_0 \<mu>_lt_1 \<Lambda>_gt_0 \<mu>_ge_0
      by (intro iffD2[OF exp_le_cancel_iff] mult_left_mono_neg[where c="-real l"] mult_left_mono
          power_mono) simp_all
    also have "\<dots> = ?R" by simp
    finally show "?L1 \<le> ?R" by simp
  next
    assume a:"1 < \<gamma> + \<Lambda> + \<mu>"
    have "(\<gamma>+\<Lambda>+\<mu>)* real l > real (card {i \<in> {..<l}. (x i)})" for x
    proof -
      have "real (card {i \<in> {..<l}. (x i)}) \<le> card {..<l}" by (intro of_nat_mono card_mono) auto
      also have "\<dots> = real l" by simp
      also have "\<dots> < (\<gamma>+\<Lambda>+\<mu>)* real l" using l_gt_0 a by simp
      finally show ?thesis by simp
    qed
    hence "?L1 = 0" unfolding not_le[symmetric] by auto
    also have "\<dots> \<le> ?R" by simp
    finally show "?L1 \<le> ?R" by simp
  qed
  finally show ?thesis by simp
qed

lemma expander_chernoff_bound_1:
  assumes "AE x in sample_pro P. f x \<in> {0,1::real}"
  defines "\<mu> \<equiv> (\<integral>x. f x \<partial>sample_pro P)"
  shows "measure (\<E> l \<Lambda> P) {w. \<bar>(\<Sum>i<l. f (w i))/l-\<mu>\<bar>\<ge>\<gamma>+\<Lambda>} \<le> 2*exp (- 2 * real l * \<gamma>^2)"
    (is "?L \<le> ?R")
proof -
  let ?w = "sample_pro (expander_pro l \<Lambda> P)"
  have "?L \<le> measure ?w {w. (\<Sum>i<l. f (w i))/l-\<mu>\<ge>\<gamma>+\<Lambda>} + measure ?w {w. (\<Sum>i<l. f (w i))/l-\<mu>\<le>-(\<gamma>+\<Lambda>)}"
    by (intro pmf_add) auto
  also have "\<dots> \<le> exp (-2*real l*\<gamma>^2) + measure ?w {w. -((\<Sum>i<l. f (w i))/l-\<mu>)\<ge>(\<gamma>+\<Lambda>)}"
    using assms by (intro add_mono expander_chernoff_bound_one_sided) (auto simp:algebra_simps)
  also have "\<dots> \<le> exp (-2*real l*\<gamma>^2) + measure ?w {w. ((\<Sum>i<l. 1-f (w i))/l-(1-\<mu>))\<ge>(\<gamma>+\<Lambda>)}"
    using l_gt_0 by (auto simp: sum_subtractf field_simps)
  also have "\<dots> \<le> exp (-2*real l*\<gamma>^2) + exp (-2*real l*\<gamma>^2)"
    using assms by (intro add_mono expander_chernoff_bound_one_sided) auto
  also have "\<dots> = ?R" by simp
  finally show ?thesis by simp
qed

lemma expander_chernoff_bound:
  assumes "AE x in sample_pro P. f x \<in> {0,1::real}"
  defines "\<mu> \<equiv> measure_pmf.expectation P f"
  shows "\<P>(\<omega> in \<E> l \<Lambda> P. \<bar>(\<Sum>i<l. f (\<omega> i))/l-\<mu>\<bar>\<ge>\<gamma>+\<Lambda>) \<le> 2*exp (- 2 * real l * \<gamma>^2)"
    (is "?L \<le> ?R")
proof -
  have "?L = measure (expander_pro l \<Lambda> P) {w. \<bar>(\<Sum>i<l. f (w i))/l-\<mu>\<bar>\<ge>\<gamma>+\<Lambda>}" by simp
  also have "\<dots> \<le> ?R" unfolding \<mu>_def by (intro expander_chernoff_bound_1 assms(1))
  finally show ?thesis by simp
qed

lemma expander_chernoff_bound_2:
  assumes "AE x in sample_pro P. f x \<in> {0,1::real}"
  defines "\<mu> \<equiv> measure_pmf.expectation P f"
  shows "\<P>(\<omega> in sample_pro (\<E> l \<Lambda> P). \<bar>(\<Sum>i<l. f (\<omega> i))-real l*\<mu>\<bar>\<ge>real l*(\<gamma>+\<Lambda>)) \<le> 2*exp (- 2 * real l * \<gamma>^2)"
    (is "?L \<le> ?R")
proof -
  have "?L = measure (expander_pro l \<Lambda> P) {w. \<bar>(\<Sum>i<l. f (w i))/l-\<mu>\<bar>\<ge>\<gamma>+\<Lambda>}"
    using l_gt_0 by (intro arg_cong2[where f="measure"] refl Collect_cong) (simp add: field_simps)
  also have "\<dots> \<le> ?R" unfolding \<mu>_def by (intro expander_chernoff_bound_1 assms(1))
  finally show ?thesis by simp
qed

end

end

unbundle no intro_cong_syntax

end