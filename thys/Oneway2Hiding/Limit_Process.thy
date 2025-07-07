theory Limit_Process

imports Run_Adversary

begin

unbundle cblinfun_syntax
unbundle lattice_syntax
unbundle register_syntax

section \<open>Limit Processes\<close>

text \<open>We need some concept of limes of Kraus families, i.e.\ finite Kraus maps tending to a 
Kraus map. Therefore, we define a filter on the Kraus family.\<close>

text \<open>\<open>kf_elems\<close> is the set of Kraus maps with only one element that are part of the 
original Kraus map.\<close>

lift_definition kf_elems :: 
  "('a::chilbert_space, 'b::chilbert_space, unit) kraus_family \<Rightarrow> ('a, 'b, unit) kraus_family set" is 
  "\<lambda>E. (\<lambda>x. {x}) ` E"
  apply (intro CollectI kraus_family_if_finite)
  by (auto simp: kraus_family_def)

lemma kf_elems_Rep_kraus_family:
  "kf_elems \<EE> = (\<lambda>x. Abs_kraus_family {x}) ` Rep_kraus_family \<EE>"
  unfolding kf_elems_def by auto

lemma kf_elems_finite:
  assumes "F \<in> kf_elems \<EE>"
  shows "finite (Rep_kraus_family F)"
  using assms by transfer auto

lemma kf_bound_of_elems:
  assumes "F \<in> kf_elems E" 
  shows "kf_bound F \<le> kf_bound E" 
proof -
  have subset: "Rep_kraus_family F \<subseteq> Rep_kraus_family E" using assms by transfer auto
  have "kf_bound F = (\<Sum>(E, u)\<in>Rep_kraus_family F. E* o\<^sub>C\<^sub>L E)"
    using assms kf_bound_finite kf_elems_finite by blast
  also have "\<dots> \<le> kf_bound E" using kf_bound_geq_sum[OF subset] by auto
  finally show ?thesis by linarith
qed

lemma kf_elems_card_1:
  assumes "F \<in> kf_elems E" 
  shows "card (Rep_kraus_family F) = 1"
  using assms by transfer auto

lemma inj_on_kf_singleton:
  "inj_on (\<lambda>x. Abs_kraus_family {x}) (Rep_kraus_family \<EE>)" 
  apply (rule inj_onI)
  apply (subst (asm) Abs_kraus_family_inject)
  using Rep_kraus_family kraus_family_def by auto

lemma kf_apply_singleton:
  fixes E :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space \<times> 'x\<close>
  assumes \<open>fst E \<noteq> 0\<close>
  shows "kf_apply (Abs_kraus_family {E}) \<rho> = sandwich_tc (fst E) \<rho>"
  apply (subst kf_apply.abs_eq)
  using assms
   apply (simp add: eq_onp_same_args)
  by simp 

lemma kf_apply_summable_on_kf_elems:
  fixes \<EE> :: "('a::chilbert_space,'b::chilbert_space,unit) kraus_family"
  shows "(\<lambda>\<FF>. kf_apply \<FF> \<rho>) summable_on (kf_elems \<EE>)"
proof -
  have *: \<open>kf_apply (Abs_kraus_family {E}) \<rho> = sandwich_tc (fst E) \<rho>\<close>
    if \<open>E \<in> Rep_kraus_family \<EE>\<close> for E
    apply (subst kf_apply_singleton)
    using that Rep_kraus_family
     apply (force intro!: simp: kraus_family_def)
    by simp
  show ?thesis
    unfolding kf_elems_Rep_kraus_family 
    apply (subst summable_on_reindex[OF inj_on_kf_singleton])
    apply (rule summable_on_cong[where g=\<open>\<lambda>E. sandwich_tc (fst E) \<rho>\<close>, THEN iffD2])
    using * 
     apply force
    using kf_apply_summable
    by (force simp: case_prod_unfold)
qed

lemma kf_apply_has_sum_kf_elems:
  fixes \<EE> :: "('a::chilbert_space,'b::chilbert_space,unit) kraus_family"
  shows "((\<lambda>\<FF>. kf_apply \<FF> \<rho>) has_sum (kf_apply \<EE> \<rho>)) (kf_elems \<EE>)"
proof -
  have *: \<open>kf_apply (Abs_kraus_family {E}) \<rho> = sandwich_tc (fst E) \<rho>\<close>
    if \<open>E \<in> Rep_kraus_family \<EE>\<close> for E
    apply (subst kf_apply_singleton)
    using that Rep_kraus_family
     apply (force intro!: simp: kraus_family_def)
    by simp
  show ?thesis
    unfolding kf_elems_Rep_kraus_family 
    apply (subst has_sum_reindex[OF inj_on_kf_singleton])
    apply (rule has_sum_cong[where g=\<open>\<lambda>E. sandwich_tc (fst E) \<rho>\<close>, THEN iffD2])
    using * 
     apply force
    by (metis (no_types, lifting) has_sum_cong kf_apply_has_sum split_def)
qed

lemma kf_apply_abs_summable_on_kf_elems:
  fixes \<EE> :: "('a::chilbert_space,'b::chilbert_space,unit) kraus_family"
  shows "(\<lambda>\<FF>. kf_apply \<FF> \<rho>) abs_summable_on (kf_elems \<EE>)"
proof -
  have *: \<open>kf_apply (Abs_kraus_family {E}) \<rho> = sandwich_tc (fst E) \<rho>\<close>
    if \<open>E \<in> Rep_kraus_family \<EE>\<close> for E
    apply (subst kf_apply_singleton)
    using that Rep_kraus_family
     apply (force intro!: simp: kraus_family_def)
    by simp
  show ?thesis
    unfolding kf_elems_Rep_kraus_family 
    apply (subst summable_on_reindex[OF inj_on_kf_singleton])
    apply (subst o_def)
    apply (rule summable_on_cong[where g=\<open>\<lambda>E. norm (sandwich_tc (fst E) \<rho>)\<close>, THEN iffD2])
    using * 
     apply force
    using Rep_kraus_family kf_apply_abs_summable 
    by (force simp: case_prod_unfold)
qed

text \<open>Now, we can define a sub-adversary. An adversary is modeled by a sequence of $n$ Kraus maps.
A sub-adversary is then defined as a sequence of $n$ elements of the respective Kraus maps.
Adding all sub-adversaries together yields the original Kraus map.\<close>

definition finite_kraus_subadv :: "'a kraus_adv \<Rightarrow> nat \<Rightarrow> 'a kraus_adv set" where
  "finite_kraus_subadv \<EE> n =  PiE {0..<n+1} (\<lambda>i. kf_elems (\<EE> i))"

lemma finite_kraus_subadv_I:
  assumes "f \<in> finite_kraus_subadv \<EE> n" "i<n+1"
  shows "f i \<in> kf_elems (\<EE> i)"
  using assms unfolding finite_kraus_subadv_def by auto


lemma finite_kraus_subadv_rewrite:
  "finite_kraus_subadv \<EE> (Suc n) = 
  (\<lambda>(x,f). fun_upd f (Suc n) x) ` (kf_elems (\<EE> (Suc n)) \<times> finite_kraus_subadv \<EE> n)"
  by (metis PiE_insert_eq Suc_eq_plus1 finite_kraus_subadv_def set_upt_Suc)

lemma finite_kraus_subadv_rewrite_inj:
  "inj_on (\<lambda>(x, f). f(Suc n := x)) (kf_elems (\<EE> (Suc n)) \<times> finite_kraus_subadv \<EE> n)"
  unfolding inj_on_def proof (safe, goal_cases)
  case (1 a b aa ba) then show ?case by (metis fun_upd_eqD)
next
  case (2 a b aa b')
  then have "b x = b' x" if "x<Suc n" for x 
    by (metis fun_upd_eqD fun_upd_triv fun_upd_twist nat_neq_iff that)
  moreover have "b x = undefined" and "b' x = undefined" if "x \<ge> Suc n" for x 
    using 2(2,4) unfolding finite_kraus_subadv_def 
    by (metis PiE_arb Suc_eq_plus1 atLeastLessThan_iff not_le that)+
  ultimately show ?case by (intro ext) (metis not_le)
qed 


lemma norm_kf_apply_singleton_trace_tc:
  assumes "0 \<le> \<rho>" and \<open>fst x \<noteq> 0\<close>
  shows "norm (kf_apply (Abs_kraus_family {x}) \<rho>) = trace_tc (sandwich_tc (fst x) \<rho>)"
  apply (subst norm_tc_pos)
   apply (rule kf_apply_pos[OF assms(1)])
  using kf_apply_singleton
  apply (subst kf_apply_singleton)
  using assms by auto


lemma infsum_norm_kf_apply_step:
  assumes \<rho>n_summable: "\<rho>n summable_on finite_kraus_subadv \<EE> n"
    and pos: "\<And>x. x \<in> finite_kraus_subadv \<EE> n \<Longrightarrow> 0 \<le> \<rho>n x"
  shows "(\<lambda>x. \<Sum>\<^sub>\<infinity>y\<in>finite_kraus_subadv \<EE> n. norm (kf_apply x (\<rho>n y))) 
    abs_summable_on kf_elems (\<EE> (Suc n))"
proof -
  define \<rho> where "\<rho> = infsum \<rho>n (finite_kraus_subadv \<EE> n)"
  have "((\<lambda>y. trace_tc (sandwich_tc E y)) o (\<lambda>y. \<rho>n y) has_sum trace_tc (sandwich_tc E \<rho>))
     (finite_kraus_subadv \<EE> n)" for E::"'a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'a ell2"
    unfolding o_def by (subst has_sum_bounded_linear[OF bounded_linear_trace_norm_sandwich_tc])
      (auto simp add: \<rho>_def \<rho>n_summable)
  then have sandwich_tc_lim: "(\<Sum>\<^sub>\<infinity>y\<in>finite_kraus_subadv \<EE> n. trace_tc (sandwich_tc E (\<rho>n y))) = 
    trace_tc (sandwich_tc E (\<Sum>\<^sub>\<infinity>y\<in>finite_kraus_subadv \<EE> n. \<rho>n y))" 
    for E::"'a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'a ell2"
    by (intro infsumI) (auto simp add: o_def \<rho>_def)

  let ?f1 = "(\<lambda>(E,x). \<bar>\<Sum>\<^sub>\<infinity>y\<in>finite_kraus_subadv \<EE> n. trace_tc (sandwich_tc E (\<rho>n y))\<bar>)"
  let ?f2 = "(\<lambda>x. \<bar>\<Sum>\<^sub>\<infinity>y\<in>finite_kraus_subadv \<EE> n. norm (kf_apply (Abs_kraus_family {x}) (\<rho>n y))\<bar>)"

  have "(\<lambda>(E, x). sandwich_tc E \<rho>) abs_summable_on Rep_kraus_family (\<EE> (Suc n))"
    using Rep_kraus_family kf_apply_abs_summable by blast
  then have f1_summable: "?f1 summable_on Rep_kraus_family (\<EE> (Suc n))" 
    unfolding sandwich_tc_lim \<rho>_def[symmetric] using trace_tc_abs_summable_on o_def
    by (metis (mono_tags, lifting) abs_summable_summable norm_abs split_def summable_on_cong)  
  then have "?f2 summable_on Rep_kraus_family (\<EE> (Suc n))"
  proof -
    have "(?f1 summable_on Rep_kraus_family (\<EE> (Suc n))) = (?f2 summable_on Rep_kraus_family (\<EE> (Suc n)))"
    proof (subst summable_on_cong[of "Rep_kraus_family (\<EE> (Suc n))" ?f1 ?f2], goal_cases)
      case (1 x)
      then have neq0: \<open>fst x \<noteq> 0\<close>
        using Rep_kraus_family
        by (force simp: kraus_family_def)
      have infsum: "(\<Sum>\<^sub>\<infinity>y\<in>finite_kraus_subadv \<EE> n. trace_tc (sandwich_tc (fst x) (\<rho>n y))) = 
        (\<Sum>\<^sub>\<infinity>y\<in>finite_kraus_subadv \<EE> n. norm (kf_apply (Abs_kraus_family {x}) (\<rho>n y)))"
        apply (subst infsum_of_real[symmetric])
        apply (rule infsum_cong)
        apply (subst norm_kf_apply_singleton_trace_tc)
        using pos neq0 by auto
      then show ?case by (auto simp add: split_def abs_complex_def)
    next
      case 2
      then show ?case using summable_on_iff_abs_summable_on_complex by force
    qed 
    then show ?thesis using f1_summable by auto
  qed
  then show ?thesis unfolding  kf_elems_Rep_kraus_family 
    by (subst summable_on_reindex[OF inj_on_kf_singleton]) 
      (use kf_apply_singleton in \<open>auto simp add: o_def\<close> )
qed


text \<open>Run of adversary is summable on sub-adversaries.\<close>

lemma run_mixed_adv_greater_indifferent:
  assumes "m > n"
  shows "run_mixed_adv n (f(m := x)) UB init X Y H = run_mixed_adv n f UB init X Y H"
  using assms by (induct n arbitrary: f m) auto

lemma run_mixed_adv_Suc_indifferent:
  "run_mixed_adv n (f(Suc n := x)) UB init X Y H = run_mixed_adv n f UB init X Y H"
  by (intro run_mixed_adv_greater_indifferent) auto


lemma run_mixed_adv_abs_summable:
  fixes \<EE> :: "'a kraus_adv"
  shows "(\<lambda>f. run_mixed_adv n f UB init X Y H) abs_summable_on (finite_kraus_subadv \<EE> n)"
proof (induct n)
  case 0
  have "inj_on (\<lambda>f. f 0) (\<Pi>\<^sub>E i\<in>{0}. kf_elems (\<EE> i))" 
    unfolding  PiE_over_singleton_iff inj_on_def by auto
  then have inj: "inj_on (\<lambda>f. f 0) (finite_kraus_subadv \<EE> 0)" 
    unfolding finite_kraus_subadv_def by simp
  have "(\<lambda>\<FF>. kf_apply \<FF> (tc_selfbutter init)) abs_summable_on
     (kf_elems (\<EE> 0))" using kf_apply_abs_summable_on_kf_elems by auto
  moreover {
    have "x \<in> kf_elems (\<EE> 0) \<Longrightarrow>
         x \<in> (\<lambda>x. x 0) ` (\<Pi>\<^sub>E i\<in>{0}. kf_elems (\<EE> i))" for x
      unfolding PiE_over_singleton_iff by (simp add: image_iff)
    then have "(\<lambda>f. f 0) ` finite_kraus_subadv \<EE> 0 = kf_elems (\<EE> 0)" 
      by (auto simp add: finite_kraus_subadv_I finite_kraus_subadv_def)     
  }
  ultimately have "(\<lambda>\<FF>. kf_apply \<FF> (tc_selfbutter init)) o (\<lambda>f. f 0) abs_summable_on (finite_kraus_subadv \<EE> 0)" 
    by (subst abs_summable_on_reindex[OF inj, symmetric]) auto
  then show ?case by auto
next
  case (Suc n)
  define \<rho>n where "\<rho>n f = sandwich_tc ((X;Y) (Uquery H) o\<^sub>C\<^sub>L UB n)(run_mixed_adv n f UB init X Y H)"
    for f
  have \<rho>n_Suc_indiff:"\<rho>n (f(Suc n := x)) = \<rho>n f" for f x 
    unfolding \<rho>n_def run_mixed_adv_Suc_indifferent by auto
  have \<rho>n_abs_summable_on:
    "(\<lambda>f. \<rho>n f) abs_summable_on finite_kraus_subadv \<EE> n"
    unfolding \<rho>n_def using sandwich_tc_abs_summable_on[OF Suc] by (auto simp add: o_def)

  have one: "(\<lambda>xa. kf_apply x (\<rho>n (xa(Suc n := x)))) abs_summable_on finite_kraus_subadv \<EE> n" 
    if "x \<in> kf_elems (\<EE> (Suc n))" for x
    using \<rho>n_Suc_indiff \<rho>n_abs_summable_on finite_kf_apply_abs_summable_on by fastforce

  have \<rho>n_summable: "\<rho>n summable_on finite_kraus_subadv \<EE> n" 
    using Suc \<rho>n_def \<rho>n_abs_summable_on abs_summable_summable by blast
  have pos: "x \<in> finite_kraus_subadv \<EE> n \<Longrightarrow> 0 \<le> \<rho>n x" for x
    by (simp add: \<rho>n_def run_mixed_adv_pos sandwich_tc_pos)
  have two: "(\<lambda>x. \<Sum>\<^sub>\<infinity>y\<in>finite_kraus_subadv \<EE> n. norm (kf_apply x (\<rho>n (y(Suc n := x))))) 
    abs_summable_on kf_elems (\<EE> (Suc n))" 
    unfolding \<rho>n_Suc_indiff by (rule infsum_norm_kf_apply_step[OF \<rho>n_summable pos])

  have lim: "(\<lambda>x. kf_apply (x (Suc n)) (\<rho>n x)) abs_summable_on finite_kraus_subadv \<EE> (Suc n)"
    apply (subst finite_kraus_subadv_rewrite)
    apply (subst abs_summable_on_reindex[OF finite_kraus_subadv_rewrite_inj])
    apply (unfold o_def case_prod_beta) 
    apply (subst abs_summable_on_Sigma_iff)
    using one two by auto
  then have "(\<lambda>f. kf_apply (f (Suc n)) (sandwich_tc ((X;Y) (Uquery H) o\<^sub>C\<^sub>L UB n)
   (run_mixed_adv n f UB init X Y H))) abs_summable_on
   (finite_kraus_subadv \<EE> (Suc n))" 
    unfolding \<rho>n_def[symmetric] by auto
  then show ?case by auto
qed


lemma run_mixed_adv_summable:
  fixes \<EE> :: "'a kraus_adv"
  shows "(\<lambda>f. run_mixed_adv n f UB init X Y H) summable_on (finite_kraus_subadv \<EE> n)"
  using abs_summable_summable[OF run_mixed_adv_abs_summable] by blast

lemma run_mixed_adv_has_sum:
  fixes \<EE> :: "'a kraus_adv"
  shows "((\<lambda>f. run_mixed_adv n f UB init X Y H) has_sum run_mixed_adv n \<EE> UB init X Y H) 
  (finite_kraus_subadv \<EE> n)"
proof (induct n)
  case 0
  have "inj_on (\<lambda>f. f 0) (\<Pi>\<^sub>E i\<in>{0}. kf_elems (\<EE> i))" 
    unfolding  PiE_over_singleton_iff inj_on_def by auto
  then have inj: "inj_on (\<lambda>f. f 0) (finite_kraus_subadv \<EE> 0)" 
    unfolding finite_kraus_subadv_def by simp
  have rew: "(\<lambda>f. kf_apply (f 0) (tc_selfbutter init)) = 
    (\<lambda>\<FF>. kf_apply \<FF> (tc_selfbutter init)) o (\<lambda>f. f 0)" by auto
  have "((\<lambda>\<FF>. kf_apply \<FF> (tc_selfbutter init)) has_sum 
     kf_apply (\<EE> 0) (tc_selfbutter init))
     (kf_elems (\<EE> 0))" using kf_apply_has_sum_kf_elems by auto
  moreover {
    have "x \<in> kf_elems (\<EE> 0) \<Longrightarrow>
         x \<in> (\<lambda>x. x 0) ` (\<Pi>\<^sub>E i\<in>{0}. kf_elems (\<EE> i))" for x
      unfolding PiE_over_singleton_iff by (simp add: image_iff)
    then have "(\<lambda>f. f 0) ` finite_kraus_subadv \<EE> 0 = kf_elems (\<EE> 0)" 
      by (auto simp add: finite_kraus_subadv_I finite_kraus_subadv_def)     
  }
  ultimately have "((\<lambda>f. kf_apply (f 0) (tc_selfbutter init)) has_sum
     kf_apply (\<EE> 0) (tc_selfbutter init)) (finite_kraus_subadv \<EE> 0)" 
    unfolding rew by (subst has_sum_reindex[OF inj, symmetric]) auto
  then show ?case by auto
next
  case (Suc n)
  define \<rho>n where "\<rho>n f = sandwich_tc ((X;Y) (Uquery H) o\<^sub>C\<^sub>L UB n)(run_mixed_adv n f UB init X Y H)"
    for f
  have \<rho>n_Suc_indiff:"\<rho>n (f(Suc n := x)) = \<rho>n f" for f x 
    unfolding \<rho>n_def run_mixed_adv_Suc_indifferent by auto

  define \<rho> where "\<rho> = sandwich_tc ((X;Y) (Uquery H) o\<^sub>C\<^sub>L UB n) (run_mixed_adv n \<EE> UB init X Y H)"

  have \<rho>n_has_sum_\<rho>: "((\<lambda>f. \<rho>n f) has_sum \<rho>) (finite_kraus_subadv \<EE> n)"
    unfolding \<rho>n_def \<rho>_def by (use sandwich_tc_has_sum[OF Suc] in \<open>auto simp add: o_def\<close>)

  have \<rho>n_abs_summable_on:
    "(\<lambda>f. \<rho>n f) abs_summable_on finite_kraus_subadv \<EE> n"
  proof -
    have "\<forall>f c F. (\<lambda>fa. sandwich_tc c (f fa)) abs_summable_on F \<or> \<not> f abs_summable_on F"
      using sandwich_tc_abs_summable_on by auto
    then show ?thesis
      unfolding \<rho>n_def by (metis (no_types) run_mixed_adv_abs_summable)
  qed

  have one: "((\<lambda>y. kf_apply x (\<rho>n (y(Suc n := x)))) has_sum kf_apply x \<rho>)
          (finite_kraus_subadv \<EE> n)" if "x \<in> kf_elems (\<EE> (Suc n))" for x
    unfolding \<rho>n_Suc_indiff by (smt (verit, best) \<rho>n_has_sum_\<rho> comp_eq_dest_lhs 
        finite_kf_apply_has_sum has_sum_cong)
  have two: "((\<lambda>x. kf_apply x \<rho>) has_sum kf_apply (\<EE> (Suc n)) \<rho>)
     (kf_elems (\<EE> (Suc n)))" 
    by (simp add: kf_apply_has_sum_kf_elems)

  have "(\<lambda>(x,f). kf_apply x (\<rho>n (f(Suc n := x)))) abs_summable_on
    kf_elems (\<EE> (Suc n)) \<times> finite_kraus_subadv \<EE> n"
  proof (unfold \<rho>n_Suc_indiff, subst abs_summable_on_Sigma_iff, safe, goal_cases)
    case (1 x)
    then show ?case using \<rho>n_abs_summable_on finite_kf_apply_abs_summable_on by auto
  next
    case 2
    then show ?case 
      by (intro infsum_norm_kf_apply_step[OF abs_summable_summable[OF \<rho>n_abs_summable_on]]) 
        (auto simp add: \<rho>n_def run_mixed_adv_pos sandwich_tc_pos)
  qed
  then have "(\<lambda>(x,f). kf_apply x (\<rho>n (f(Suc n := x)))) summable_on
    kf_elems (\<EE> (Suc n)) \<times> finite_kraus_subadv \<EE> n"
    using abs_summable_summable by blast
  then have three: "(\<lambda>x. kf_apply (fst x) (\<rho>n ((snd x)(Suc n := fst x)))) summable_on
    kf_elems (\<EE> (Suc n)) \<times> finite_kraus_subadv \<EE> n"
    by (metis (no_types, lifting) split_def summable_on_cong)

  have lim: 
    "((\<lambda>f. kf_apply (f (Suc n)) (\<rho>n f)) has_sum kf_apply (\<EE> (Suc n)) \<rho>)
     (finite_kraus_subadv \<EE> (Suc n))" 
    apply (subst finite_kraus_subadv_rewrite)
    apply (subst has_sum_reindex[OF finite_kraus_subadv_rewrite_inj])
    apply (unfold o_def case_prod_beta) 
    apply (intro has_sum_SigmaI[where g = "(\<lambda>x. kf_apply x \<rho>)"]) 
    by (auto simp add: one two three)
  then have "((\<lambda>f. kf_apply (f (Suc n)) (sandwich_tc ((X;Y) (Uquery H) o\<^sub>C\<^sub>L UB n)
   (run_mixed_adv n f UB init X Y H))) has_sum kf_apply (\<EE> (Suc n))
   (sandwich_tc ((X;Y) (Uquery H) o\<^sub>C\<^sub>L UB n) (run_mixed_adv n \<EE> UB init X Y H)))
   (finite_kraus_subadv \<EE> (Suc n))" 
    unfolding \<rho>n_def \<rho>_def by auto
  then show ?case by auto
qed

text \<open>Now, we cover limits for adversary runs in the O2H setting.\<close>

context o2h_setting
begin


lemma run_mixed_A_has_sum:
  "((\<lambda>f. run_mixed_A f H) has_sum run_mixed_A kraus_A H) (finite_kraus_subadv kraus_A d)"
  unfolding run_mixed_A_def by (rule run_mixed_adv_has_sum)


lemma run_mixed_B_has_sum:
  "((\<lambda>f. run_mixed_adv d f (US S) init_B X_for_B Y_for_B H) has_sum run_mixed_B kraus_B H S) 
  (finite_kraus_subadv (\<lambda>n. kf_Fst (kraus_B n)) d)"
  unfolding run_mixed_B_def by (rule run_mixed_adv_has_sum)


lemma run_mixed_B_count_has_sum:
  "((\<lambda>f. run_mixed_adv d f (\<lambda>_. U_S' S) init_B_count X_for_C Y_for_C H) has_sum run_mixed_B_count kraus_B H S) 
  (finite_kraus_subadv (\<lambda>n. kf_Fst (kraus_B n)) d)"
  unfolding run_mixed_B_count_def by (rule run_mixed_adv_has_sum)


lemma kf_elems_kf_Fst:
  "kf_elems (kf_Fst \<EE>) = (\<lambda>f. kf_Fst f) ` kf_elems \<EE>"
  by transfer auto

lemma finite_kraus_subadv_Fst_invert:
  "finite_kraus_subadv (\<lambda>m.  (kf_Fst :: _\<Rightarrow>(('a \<times> 'c) ell2,_,_) kraus_family) (\<EE> m)) n =  
 (\<lambda>f. \<lambda>i\<in>{0..<n+1}. kf_Fst (f i)) ` (finite_kraus_subadv \<EE> n)"
  unfolding finite_kraus_subadv_def kf_elems_kf_Fst
proof (induct n)
  case 0
  have " (\<Pi>\<^sub>E i\<in>{0..<0 + 1}. kf_Fst ` kf_elems (\<EE> i)) =  
    (\<Pi>\<^sub>E i\<in>{0}. kf_Fst ` kf_elems (\<EE> i))" by auto
  also have "\<dots> = (\<Union>b\<in>kf_elems (\<EE> 0). {\<lambda>x\<in>{0}. kf_Fst b})" 
    unfolding PiE_over_singleton_iff by auto
  also have "\<dots> = (\<Union>b\<in>kf_elems (\<EE> 0). (\<lambda>f. \<lambda>i\<in>{0}. kf_Fst (f i)) ` {\<lambda>x\<in>{0}. b})"
  proof -
    have "(\<lambda>x\<in>{0}. kf_Fst b) = (\<lambda>a\<in>{0}. kf_Fst (if a = 0 then b else undefined))" for b
      by fastforce
    then show ?thesis  by (intro Union_cong) auto
  qed
  also have "\<dots> = (\<lambda>f. \<lambda>i\<in>{0}. kf_Fst (f i)) `(\<Union>b\<in>kf_elems (\<EE> 0). {\<lambda>x\<in>{0}. b})"
    unfolding image_UN by auto
  also have "\<dots> = (\<lambda>f. \<lambda>i\<in>{0..<0+1}. kf_Fst (f i)) ` (\<Pi>\<^sub>E i\<in>{0}. kf_elems (\<EE> i))" 
    unfolding PiE_over_singleton_iff by auto
  also have "\<dots> = (\<lambda>f. \<lambda>i\<in>{0..<0+1}. kf_Fst (f i)) ` (\<Pi>\<^sub>E i\<in>{0..<0+1}. kf_elems (\<EE> i))" 
    by auto
  finally show ?case by blast
next
  case (Suc n)
  let ?prodset = "kf_elems (\<EE> (Suc n)) \<times>(\<Pi>\<^sub>E i\<in>{0..<n+1}. kf_elems (\<EE> i))"
  have "(\<Pi>\<^sub>E i\<in>{0..<Suc n + 1}. (kf_Fst :: _\<Rightarrow>(('a \<times> 'c) ell2,_,_) kraus_family) ` 
    kf_elems (\<EE> i)) =  
    (\<Pi>\<^sub>E i\<in>(insert (Suc n) {0..<Suc n}). kf_Fst ` kf_elems (\<EE> i))" 
    by (auto simp add: set_upt_Suc)
  also have "\<dots> = (\<lambda>(y, g). g(Suc n := y)) ` (kf_Fst ` kf_elems (\<EE> (Suc n)) \<times>
     (\<Pi>\<^sub>E i\<in>{0..<n+1}. kf_Fst ` kf_elems (\<EE> i)))" 
    by (subst PiE_insert_eq) auto
  also have "\<dots> = (\<lambda>(y, g). g(Suc n := y)) ` (kf_Fst ` kf_elems (\<EE> (Suc n)) \<times>
     ((\<lambda>f. \<lambda>i\<in>{0..<n+1}. kf_Fst (f i)) ` (\<Pi>\<^sub>E i\<in>{0..<n+1}. kf_elems (\<EE> i))))" 
    by (subst Suc) auto
  also have "\<dots> = (\<lambda>(y, g). g(Suc n := y)) ` 
    (\<lambda>(a,x). (kf_Fst a, restrict (\<lambda>i. kf_Fst (x i)) {0..<n+1})) ` ?prodset" 
    by (simp add: image_paired_Times)
  also have "\<dots> = (\<lambda>(y, g). (restrict (\<lambda>i. kf_Fst (g i)) {0..<n+1})
    (Suc n := kf_Fst y)) ` ?prodset"
    by (subst image_image) (simp add: split_def) 
  also have "\<dots> = (\<lambda>(y, g). restrict ((\<lambda>i. kf_Fst (g i))(Suc n := kf_Fst y))
    (insert (Suc n) {0..<n+1})) ` ?prodset"
    by (subst restrict_upd) auto
  also have "\<dots> = (\<lambda>(y, g). restrict ((\<lambda>i. kf_Fst (g i))(Suc n := kf_Fst y))
    {0..<Suc n + 1}) ` ?prodset" using semiring_norm(174) set_upt_Suc by presburger
  also have "\<dots> = (\<lambda>(y, g). restrict (\<lambda>i. kf_Fst ((g(Suc n:=y)) i))
    {0..<Suc n + 1}) ` ?prodset" 
  proof -
    have rew: "(\<lambda>i. kf_Fst (g i))(Suc n := kf_Fst y) = 
      (\<lambda>i. (kf_Fst :: _\<Rightarrow>(('a \<times> 'c) ell2,_,_) kraus_family) ((g(Suc n:=y)) i))" for g y 
      by fastforce
    show ?thesis by (subst rew) auto
  qed
  also have "\<dots> = (\<lambda>f. restrict (\<lambda>i. kf_Fst (f i)) {0..<Suc n + 1}) ` 
    (\<lambda>(a,g). g(Suc n:= a)) ` ?prodset" 
    by (smt (verit, best) image_cong image_image restrict_ext split_def)
  also have "\<dots> = (\<lambda>f. restrict (\<lambda>i. kf_Fst (f i)) {0..<Suc n + 1}) ` 
    (\<Pi>\<^sub>E i\<in>(insert (Suc n) {0..<Suc n}). kf_elems (\<EE> i))" 
    by (metis Suc_eq_plus1 finite_kraus_subadv_def finite_kraus_subadv_rewrite set_upt_Suc)
  also have "\<dots> = (\<lambda>f. \<lambda>i\<in>{0..<Suc n + 1}. kf_Fst (f i)) ` 
    (\<Pi>\<^sub>E i\<in>{0..<Suc n+1}. kf_elems (\<EE> i))" by (simp add: set_upt_Suc)
  finally show ?case by blast
qed

lemma inj_kf_Fst: \<open>E = F\<close> if \<open>kf_Fst E = kf_Fst F\<close>
proof (insert that, transfer)
  fix E F :: \<open>('a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'c ell2 \<times> unit) set\<close>
  assume asm: \<open>(\<lambda>(x, _). (x \<otimes>\<^sub>o id_cblinfun, ())) ` E = (\<lambda>(x, _). (x \<otimes>\<^sub>o id_cblinfun, ())) ` F\<close>
  have \<open>inj (\<lambda>(x::'a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'c ell2, _::unit). (x \<otimes>\<^sub>o id_cblinfun, ()))\<close>
    apply (rewrite at \<open>inj \<hole>\<close> to \<open>map_prod (\<lambda>x. x \<otimes>\<^sub>o id_cblinfun) id\<close> DEADID.rel_mono_strong)
     apply (force intro!: simp:)
    apply (rule prod.inj_map)
    by (simp_all add: inj_tensor_left) 
  from inj_image_eq_iff[OF this] asm
  show \<open>E = F\<close>
    by blast
qed


lemma inj_on_kf_Fst:
  "inj_on (\<lambda>f. \<lambda>n\<in>{0..<n+1}. (kf_Fst (f n) :: (('a \<times> 'b) ell2, _, _) kraus_family)) 
  (finite_kraus_subadv \<EE> n)"
proof (rule inj_onI, rename_tac E F)
  fix E F :: \<open>nat \<Rightarrow> ('a ell2, 'a ell2, unit) kraus_family\<close>
  assume finE: \<open>E \<in> finite_kraus_subadv \<EE> n\<close> and finF: \<open>F \<in> finite_kraus_subadv \<EE> n\<close>
  assume eq: \<open>(\<lambda>i\<in>{0..<n + 1}. kf_Fst (E i)  :: (('a \<times> 'b) ell2, _, _) kraus_family) = (\<lambda>n\<in>{0..<n + 1}. kf_Fst (F n))\<close>
  have \<open>(kf_Fst (E i) :: (('a \<times> 'b) ell2, _, _) kraus_family) = kf_Fst (F i)\<close> if \<open>i \<in> {0..<n+1}\<close> for i
    using eq[unfolded fun_eq_iff, rule_format, of i]
    unfolding restrict_def
    using that by (auto intro!: simp: fun_eq_iff)
  then have \<open>E i = F i\<close> if \<open>i \<in> {0..<n+1}\<close> for i
    using inj_kf_Fst that by blast
  moreover from finE finF
  have \<open>E i = F i\<close> if \<open>i \<notin> {0..<n+1}\<close> for i
    using that
    by (simp add: finite_kraus_subadv_def PiE_def extensional_def)
  ultimately  show \<open>E = F\<close>
    by blast
qed


lemma run_mixed_adv_kf_Fst_restricted:
  "run_mixed_adv m (\<lambda>n. kf_Fst (f n)) U init' X' Y' H =
 run_mixed_adv m (\<lambda>n\<in>{0..<m + 1}. kf_Fst (f n)) U init' X' Y' H"
proof (induct m arbitrary: f)
  case (Suc m)
  let ?f1 = "(\<lambda>a. if a < Suc m then (kf_Fst ::_\<Rightarrow>(('a \<times> 'b) ell2,_,_) kraus_family) (f a) 
    else undefined)"
  let ?f2 = "(\<lambda>a. if a < Suc (Suc m) then (kf_Fst ::_\<Rightarrow>(('a \<times> 'b) ell2,_,_) kraus_family) (f a) 
    else undefined)"
  have f12: "?f1(Suc m:= kf_Fst (f (Suc m))) = ?f2" by fastforce
  have eq: "run_mixed_adv m ?f1 U init' X' Y' H = 
            run_mixed_adv m ?f2 U init' X' Y' H"
    unfolding f12[symmetric] by (subst run_mixed_adv_Suc_indifferent) auto
  show ?case by (auto simp add: eq Suc)
qed auto


lemma run_mixed_B_has_sum':
  "((\<lambda>f. run_mixed_B f H S) has_sum run_mixed_B kraus_B H S) (finite_kraus_subadv kraus_B d)"
  (is "(?f has_sum ?x) ?A") 
proof -
  have inj: "inj_on (\<lambda>f. \<lambda>n\<in>{0..<d + 1}. kf_Fst (f n)) (finite_kraus_subadv kraus_B d)" 
    using inj_on_kf_Fst by auto
  have rew: "?f = (\<lambda>f. run_mixed_adv d f (US S) init_B X_for_B Y_for_B H) o 
    (\<lambda>f. \<lambda>n\<in>{0..<d + 1}. kf_Fst (f n))" unfolding run_mixed_B_def
    using run_mixed_adv_kf_Fst_restricted[where init' = init_B and X' = X_for_B and Y'=Y_for_B] 
    by auto
  show ?thesis unfolding rew  by (subst has_sum_reindex[OF inj, symmetric]) 
      (unfold finite_kraus_subadv_Fst_invert[symmetric], rule run_mixed_B_has_sum)
qed



lemma run_mixed_B_count_has_sum':
  "((\<lambda>f. run_mixed_B_count f H S) has_sum run_mixed_B_count kraus_B H S) (finite_kraus_subadv kraus_B d)"
  (is "(?f has_sum ?x) ?A") 
proof -
  have inj: "inj_on (\<lambda>f. \<lambda>n\<in>{0..<d + 1}. kf_Fst (f n)) (finite_kraus_subadv kraus_B d)" 
    using inj_on_kf_Fst by auto
  have rew: "?f = (\<lambda>f. run_mixed_adv d f (\<lambda>_. U_S' S) init_B_count X_for_C Y_for_C H) o 
    (\<lambda>f. \<lambda>n\<in>{0..<d + 1}. kf_Fst (f n))" unfolding run_mixed_B_count_def
    using run_mixed_adv_kf_Fst_restricted[where init' = init_B_count and X' = X_for_C and Y'=Y_for_C]  
    by auto
  show ?thesis unfolding rew  by (subst has_sum_reindex[OF inj, symmetric]) 
      (unfold finite_kraus_subadv_Fst_invert[symmetric], rule run_mixed_B_count_has_sum)
qed




text \<open>Limit with finite sums\<close>

lemma has_sum_finite_sum:
  fixes f :: "'a \<Rightarrow> 'b \<Rightarrow> 'c:: {comm_monoid_add,topological_space, topological_comm_monoid_add}"
  assumes "\<And>val. (f val has_sum g val) A" "finite S"
  shows "((\<lambda>x. (\<Sum>val \<in> S. f val x)) has_sum (\<Sum>val \<in> S. g val)) A"
  using assms(2) proof (induct S)
  case empty
  show "((\<lambda>x. \<Sum>val\<in>{}. f val x) has_sum sum g {}) A" by auto
next
  case (insert x F)
  show "((\<lambda>xa. \<Sum>val\<in>insert x F. f val xa) has_sum sum g (insert x F)) A" 
    unfolding sum.insert_remove[OF \<open>finite F\<close>] by (intro has_sum_add[of "f x"])
      (use assms insert in \<open>auto\<close>)
qed



lemma fin_subadv_fin_Rep_kraus_family:
  assumes "F \<in> finite_kraus_subadv E n" "i < n+1" "n<d+1"
  shows "finite (Rep_kraus_family (F i))"
  using assms unfolding finite_kraus_subadv_def using kf_elems_finite by fastforce

lemma fin_subadv_bound_leq_id:
  assumes "F \<in> finite_kraus_subadv E d" 
  assumes "i < d+1"
  assumes E_norm_id: "\<And>i. i < d+1 \<Longrightarrow> kf_bound (E i) \<le> id_cblinfun"
  shows "kf_bound (F i) \<le> id_cblinfun"
proof -
  have "F i \<in> kf_elems (E i)" using assms unfolding finite_kraus_subadv_def by auto
  then have "kf_bound (F i) \<le> kf_bound (E i)" 
    using kf_bound_of_elems by auto
  then show ?thesis using E_norm_id[OF assms(2)] by auto
qed


lemma fin_subadv_nonzero:
  assumes "F \<in> finite_kraus_subadv E n" "i < n+1" "n<d+1"
  shows "Rep_kraus_family (F i) \<noteq> {}"
proof -
  have "F i \<in> kf_elems (E i)" using assms unfolding finite_kraus_subadv_def by auto
  then show ?thesis using kf_elems_card_1 by fastforce
qed

end

unbundle no cblinfun_syntax
unbundle no lattice_syntax
unbundle no register_syntax


end