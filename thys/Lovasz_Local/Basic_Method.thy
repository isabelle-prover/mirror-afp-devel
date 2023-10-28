(* Theory: Basic_Method
   Author: Chelsea Edmonds
*)

section \<open>The Basic Probabilistic Method Framework\<close>
text \<open>This theory includes all aspects of step (3) and (4) of the basic method framework, 
which are purely probabilistic \<close>

theory Basic_Method imports Indep_Events
begin

subsection \<open>More Set and Multiset lemmas \<close>
lemma card_size_set_mset: "card (set_mset A) \<le> size A"
  using size_multiset_overloaded_eq
  by (metis card_eq_sum count_greater_eq_one_iff sum_mono) 
  
lemma Union_exists: "{a \<in> A . \<exists> b \<in> B . P a b} = (\<Union>b \<in> B . {a \<in> A . P a b})"
  by blast

lemma Inter_forall:  "B \<noteq> {} \<Longrightarrow> {a \<in> A . \<forall> b \<in> B . P a b} = (\<Inter>b \<in> B . {a \<in> A . P a b})"
  by auto

lemma function_map_multi_filter_size:
  assumes "image_mset F (mset_set A) = B" and "finite A"
  shows "card {a \<in> A . P (F a)} = size {# b \<in># B . P b #}"
using assms(2) assms(1) proof (induct A arbitrary: B rule: finite_induct)
  case empty
  then show ?case by simp
next
  case (insert x C)
  then have beq: "B= image_mset F (mset_set C) + {#F x#}" by auto
  then show ?case proof (cases "P (F x)")
    case True
    then have "filter_mset P B = filter_mset P (image_mset F (mset_set C)) + {#F x#}"
      by (simp add: True beq) 
    then have s: "size (filter_mset P B) = size (filter_mset P (image_mset F (mset_set C))) + 1"
      using size_single size_union by auto
    have "{a \<in> insert x C. P (F a)} = insert x {a \<in> C. P (F a)}" using True by auto
    moreover have "x \<notin> {a \<in> C. P (F a)}" using insert.hyps(2) by simp
    ultimately have "card {a \<in> insert x C. P (F a)} = card {a \<in> C. P (F a)} + 1" 
      using card_insert_disjoint insert.hyps(1) by auto
    then show ?thesis using s insert.hyps(3) by simp
  next
    case False
    then have "filter_mset P B = filter_mset P (image_mset F (mset_set C))" using beq by simp
    moreover have "{a \<in> insert x C. P (F a)} = {a \<in> C. P (F a)}" using False by auto
    ultimately show ?thesis using insert.hyps(3) by simp
  qed
qed

lemma bij_mset_obtain_set_elem:
  assumes "image_mset F (mset_set A) = B"
  assumes "b \<in># B"
  obtains a where "a \<in> A" and "F a = b"
  using assms set_image_mset
  by (metis finite_set_mset_mset_set image_iff mem_simps(2) mset_set.infinite  set_mset_empty) 

lemma bij_mset_obtain_mset_elem: 
  assumes "finite A"
  assumes "image_mset F (mset_set A) = B"
  assumes "a \<in> A"
  obtains b where "b \<in># B" and "F a = b"
  using assms by fastforce

lemma prod_fn_le1: 
  fixes f :: "'c \<Rightarrow> ('d :: {comm_monoid_mult, linordered_semidom})"
  assumes "finite A"
  assumes "A \<noteq> {}"
  assumes "\<And> y. y \<in> A \<Longrightarrow> f y \<ge> 0 \<and> f y < 1"
  shows "(\<Prod>x\<in> A. f x) < 1"
using assms(1) assms(2) assms(3) proof (induct A rule: finite_ne_induct)
  case (singleton x)
  then show ?case by auto
next
  case (insert x F)
  then show ?case
  proof (cases "x \<in> F")
    case True
    then show ?thesis using insert.hyps by auto
  next
    case False
    then have "prod f (insert x F) = f x * prod f F" by (simp add: local.insert(1))
    moreover have "prod f F < 1" using insert.hyps insert.prems by auto
    moreover have "f x < 1" "f x \<ge> 0" using insert.prems by auto
    ultimately show ?thesis
      by (metis basic_trans_rules(20) basic_trans_rules(23) more_arith_simps(6) 
          mult_left_less_imp_less verit_comp_simplify1(3)) 
  qed
qed

context prob_space
begin

subsection \<open>Existence Lemmas \<close>

lemma prob_lt_one_obtain: 
  assumes "{e \<in> space M . Q e} \<in> events"
  assumes "prob {e \<in> space M . Q e} < 1"
  obtains e where "e \<in> space M" and "\<not> Q e"
proof -
  have sin: "{e \<in> space M . \<not> Q e} \<in> events" using assms(1)
    using sets.sets_Collect_neg by blast
  have "prob {e \<in> space M . \<not> Q e} = 1 - prob {e \<in> space M . Q e}" using prob_neg assms by auto
  then have "prob {e\<in> space M . \<not> Q e} > 0" using assms(2) by auto
  then show ?thesis using that
    by (smt (verit, best) empty_Collect_eq measure_empty) 
qed

lemma prob_gt_zero_obtain: 
  assumes "{e \<in> space M . Q e} \<in> events"
  assumes "prob {e \<in> space M . Q e} > 0"
  obtains e where "e \<in> space M" and "Q e"
  using assms by (smt (verit) empty_Collect_eq inf.strict_order_iff measure_empty)

lemma inter_gt0_event: 
  assumes "F ` I \<subseteq> events"
  assumes "prob (\<Inter> i \<in> I . (space M - (F i))) > 0"
  shows "(\<Inter> i \<in> I . (space M - (F i))) \<in> events" and "(\<Inter> i \<in> I . (space M - (F i))) \<noteq> {}"
  using assms using  measure_notin_sets by (smt (verit), fastforce)

lemma obtain_intersection:
  assumes "F ` I \<subseteq> events"
  assumes "prob (\<Inter> i \<in> I . (space M - (F i)))> 0"
  obtains e where "e \<in> space M" and "\<And> i. i \<in> I \<Longrightarrow> e \<notin> F i"
proof -
  have ine: "(\<Inter> i \<in> I . (space M - (F i))) \<noteq> {}" using inter_gt0_event[of F I] assms by fast
  then obtain e where "\<And> i. i \<in> I \<Longrightarrow>  e \<in> space M - F i"  by blast
  then show ?thesis
    by (metis Diff_iff ex_in_conv subprob_not_empty that) 
qed

lemma obtain_intersection_prop:
  assumes "F ` I \<subseteq> events"
  assumes "\<And> i. i \<in> I \<Longrightarrow> F i = {e \<in> space M . P e i}"
  assumes "prob (\<Inter> i \<in> I . (space M - (F i)))> 0"
  obtains e where "e \<in> space M" and "\<And> i. i \<in> I \<Longrightarrow> \<not> P e i"
proof -
  obtain e where ein: "e \<in> space M" and "\<And> i. i \<in> I \<Longrightarrow> e \<notin> F i"
    using obtain_intersection assms(1) assms(3) by auto
  then have "\<And> i. i \<in> I \<Longrightarrow> e \<in> {e \<in> space M . \<not> P e i}" using assms(2) by simp
  then show ?thesis using ein that by simp
qed
   
lemma not_in_big_union:
  assumes "\<And> i . i \<in> A \<Longrightarrow> e \<notin> i"
  shows "e \<notin> (\<Union>A)"
  using assms by (induct A rule: infinite_finite_induct) auto

lemma not_in_big_union_fn:
  assumes "\<And> i . i \<in> A \<Longrightarrow> e \<notin> F i"
  shows "e \<notin> (\<Union>i \<in> A . F i)"
  using assms by (induct A rule: infinite_finite_induct) auto

lemma obtain_intersection_union:
  assumes "F ` I \<subseteq> events"
  assumes "prob (\<Inter> i \<in> I . (space M - (F i)))> 0"
  obtains e where "e \<in> space M" and "e \<notin> (\<Union>i \<in> I. F i)"
proof -
  obtain e where "e \<in> space M" and cond: "\<And> i. i \<in> I \<Longrightarrow>  e  \<notin>  F i"  
  using obtain_intersection[of F I] assms  by blast
  then show ?thesis using not_in_big_union_fn[of I e F] that by blast
qed

subsection \<open>Basic Bounds \<close>

text \<open>Lemmas on the Complete Independence and Union bound \<close>

lemma complete_indep_bound1: 
  assumes "finite A"
  assumes "A \<noteq> {}"
  assumes "A \<subseteq> events"
  assumes "indep_events_set A"
  assumes "\<And> a . a \<in> A \<Longrightarrow> prob a < 1"
  shows "prob (space M - (\<Inter>A)) > 0"
proof -
  have "\<Inter>A \<in> events" using assms(1) assms(2) assms(3) Inter_event_ss by simp
  then have "prob (space M - (\<Inter>A)) = 1 - prob (\<Inter>A)"
    by (simp add: prob_compl) 
  then have 1: "prob (space M - (\<Inter>A)) = 1 - prod prob A" 
    using indep_events_set_prod_all assms by simp
  moreover have "prod prob A < 1" using assms(5) assms(1) assms(2) assms(4) indep_events_set_events
    by (metis Inf_lower \<open>prob (space M - \<Inter> A) = 1 - prob (\<Inter> A)\<close> 
        basic_trans_rules(21) 1 diff_gt_0_iff_gt finite_has_maximal finite_measure_mono )
  ultimately show ?thesis by simp 
qed

lemma complete_indep_bound1_index: 
  assumes "finite A"
  assumes "A \<noteq> {}"
  assumes "F ` A \<subseteq> events"
  assumes "indep_events F A"
  assumes "\<And> a . a \<in> A \<Longrightarrow> prob (F a) < 1"
  shows "prob (space M - (\<Inter>(F` A))) > 0"
proof -
  have pos: "\<And> a. a \<in> A \<Longrightarrow> prob (F a) \<ge> 0" using assms(3) by auto
  have "\<Inter>(F ` A) \<in> events" using assms(1) assms(2) assms(3) Inter_event_ss by simp
  then have eq: "prob (space M - (\<Inter>(F ` A))) = 1 - prob (\<Inter>(F ` A))"
    by (simp add: prob_compl) 
  then have "prob (space M - (\<Inter>(F ` A))) = 1 - (\<Prod>i\<in>A. prob (F i))" 
    using indep_events_prod_all assms by simp
  moreover have "(\<Prod>i\<in>A. prob (F i)) < 1" 
    using assms(5) eq assms(2) assms(1) prod_fn_le1[of A "\<lambda> i. prob (F i)"] by auto 
  ultimately show ?thesis by simp 
qed

lemma complete_indep_bound2: 
  assumes "finite A"
  assumes "A \<subseteq> events"
  assumes "indep_events_set A"
  assumes "\<And> a . a \<in> A \<Longrightarrow> prob a < 1"
  shows "prob (space M - (\<Union>A)) > 0"
proof (cases "A = {}")
  case True
  then show ?thesis by (simp add: True prob_space) 
next
  case False
  then have "prob (space M - \<Union>A) = prob (\<Inter>a \<in> A . (space M - a))"  by simp
  moreover have "indep_events_set ((\<lambda> a. space M - a) ` A)" 
    using assms(1) assms(3) indep_events_set_compl by auto
  moreover have "finite ((\<lambda> a. space M - a) ` A)" using assms(1) by auto
  moreover have "((\<lambda> a. space M - a) ` A) \<noteq> {}" using False by auto
  ultimately have eq: "prob (space M - \<Union>A) = prod prob ((\<lambda> a. space M - a) ` A)" 
    using indep_events_set_prod_all[of "((\<lambda> a. space M - a) ` A)"] by linarith
  have "\<And> a. a \<in> ((\<lambda> a. space M - a) ` A) \<Longrightarrow> prob a > 0"
  proof -
    fix a assume "a \<in> ((\<lambda> a. space M - a) ` A)"
    then obtain a' where "a = space M - a'" and ain: "a' \<in> A" by blast
    then have "prob a = 1 - prob a'" using prob_compl assms(2) by auto
    moreover have "prob a' < 1" using assms(4) ain by simp
    ultimately show "prob a > 0" by simp
  qed
  then have "prod prob ((\<lambda> a. space M - a) ` A) > 0" by (meson prod_pos) 
  then show ?thesis using eq by simp
qed

lemma complete_indep_bound2_index: 
  assumes "finite A"
  assumes "F ` A \<subseteq> events"
  assumes "indep_events F A"
  assumes "\<And> a . a \<in> A \<Longrightarrow> prob (F a) < 1"
  shows "prob (space M - (\<Union>(F ` A))) > 0"
proof (cases "A = {}")
  case True
  then show ?thesis by (simp add: True prob_space) 
next
  case False
  then have "prob (space M - \<Union>(F `A)) = prob (\<Inter>a \<in> A . (space M - F a))"  by simp
  moreover have "indep_events (\<lambda> a. space M - F a) A" 
    using assms(1) assms(3) indep_events_compl by auto
  ultimately have eq: "prob (space M - \<Union>(F ` A)) = (\<Prod>i\<in>A. prob ((\<lambda> a. space M - F a) i))" 
    using indep_events_prod_all[of "(\<lambda> a. space M - F a)" A] assms(1) False by linarith
  have "\<And> a. a \<in> A \<Longrightarrow> prob (space M - F a) > 0"
    using prob_compl assms(2) assms(4) by auto
  then have "(\<Prod>i\<in>A. prob ((\<lambda> a. space M - F a) i)) > 0" by (meson prod_pos) 
  then show ?thesis using eq by simp
qed

lemma complete_indep_bound3: 
  assumes "finite A"
  assumes "A \<noteq> {}"
  assumes "F ` A \<subseteq> events"
  assumes "indep_events F A"
  assumes "\<And> a . a \<in> A \<Longrightarrow> prob (F a) < 1"
  shows "prob (\<Inter>a \<in> A. space M - F a) > 0"
  using complete_indep_bound2_index compl_Union_fn assms by auto 

text \<open>Combining complete independence with existence step \<close>
lemma complete_indep_bound_obtain: 
  assumes "finite A"
  assumes "A \<subseteq> events"
  assumes "indep_events_set A"
  assumes "\<And> a . a \<in> A \<Longrightarrow> prob a < 1"
  obtains e where "e \<in> space M" and "e \<notin> \<Union>A"
proof -
  have "prob (space M - (\<Union>A)) > 0" using complete_indep_bound2 assms by auto
  then show ?thesis
    by (metis Diff_eq_empty_iff less_numeral_extra(3) measure_empty subsetI that)
qed

lemma Union_bound_events: 
  assumes "finite A"
  assumes "A \<subseteq> events"
  shows "prob (\<Union>A) \<le> (\<Sum>a \<in> A. prob a)"
  using finite_measure_subadditive_finite[of A "\<lambda> x. x"]  assms by auto

lemma Union_bound_events_fun: 
  assumes "finite A"
  assumes "f ` A \<subseteq> events"
  shows "prob (\<Union>(f ` A)) \<le> (\<Sum> a \<in> A. prob (f a))"
  by (simp add: assms(1) assms(2) finite_measure_subadditive_finite) 


lemma Union_bound_avoid: 
  assumes "finite A"
  assumes "(\<Sum>a \<in> A. prob a) < 1"
  assumes "A \<subseteq> events"
  shows "prob (space M - \<Union>A) > 0"
proof -
  have "\<Union>A \<in> events"
    by (simp add: assms(1) assms(3) sets.finite_Union) 
  then have "prob (space M - \<Union>A) = 1 - prob (\<Union>A)"
    using prob_compl by simp
  moreover have "prob (\<Union>A) < 1" using assms Union_bound_events
    by fastforce 
  ultimately show ?thesis by simp
qed

lemma Union_bound_avoid_fun: 
  assumes "finite A"
  assumes "(\<Sum>a \<in> A. prob (f a)) < 1"
  assumes "f`A \<subseteq> events"
  shows "prob (space M - \<Union>(f ` A)) > 0"
proof -
  have "\<Union>(f ` A) \<in> events"
    by (simp add: assms(1) assms(3) sets.finite_Union) 
  then have "prob (space M - \<Union>(f ` A)) = 1 - prob (\<Union>(f ` A))"
    using prob_compl by simp
  moreover have "prob (\<Union>(f ` A)) < 1" using assms Union_bound_events_fun
    by (smt (verit, ccfv_SIG) sum.cong) 
  ultimately show ?thesis by simp
qed

text \<open>Combining union bound with existance step \<close>
lemma Union_bound_obtain:
  assumes "finite A"
  assumes "(\<Sum>a \<in> A. prob a) < 1"
  assumes "A \<subseteq> events"
  obtains e where "e \<in> space M" and "e \<notin> \<Union>A"
proof -
  have "prob (space M - \<Union>A) > 0" using Union_bound_avoid assms by simp
  then show ?thesis using that prob_gt_zero_obtain
    by (metis Diff_eq_empty_iff less_numeral_extra(3) measure_empty subsetI) 
qed

lemma Union_bound_obtain_fun:
  assumes "finite A"
  assumes "(\<Sum>a \<in> A. prob (f a)) < 1"
  assumes "f ` A \<subseteq> events"
  obtains e where "e \<in> space M" and "e \<notin> \<Union>( f` A)"
proof -
  have "prob (space M - \<Union>( f` A)) > 0" using Union_bound_avoid_fun assms by simp
  then show ?thesis using that prob_gt_zero_obtain
    by (metis Diff_eq_empty_iff less_numeral_extra(3) measure_empty subsetI) 
qed

lemma Union_bound_obtain_compl:
  assumes "finite A"
  assumes "(\<Sum>a \<in> A. prob a) < 1"
  assumes "A \<subseteq> events"
  obtains e where "e \<in> (space M - \<Union>A)"
proof -
  have "prob (space M - \<Union>A) > 0" using Union_bound_avoid assms by simp
  then show ?thesis using that prob_gt_zero_obtain
    by (metis all_not_in_conv measure_empty verit_comp_simplify(2) verit_comp_simplify1(3))
qed

lemma Union_bound_obtain_compl_fun:
  assumes "finite A"
  assumes "(\<Sum>a \<in> A. prob (f a)) < 1"
  assumes "f ` A \<subseteq> events"
  obtains e where "e \<in> (space M - \<Union>( f` A))"
proof -
  obtain e where "e \<in> space M" and "e \<notin> \<Union>(f` A)"
    using assms Union_bound_obtain_fun by blast
  then have "e \<in> space M - \<Union> (f ` A)" by simp
  then show ?thesis by fact
qed

end

end