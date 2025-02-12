section \<open>The Hilbert Basis theorem for Formal Power Series\<close>
theory Formal_Power_Series_Ring

imports 
  "HOL-Library.Extended_Nat" 
  "HOL-Computational_Algebra.Formal_Power_Series" 
  "HOL-Algebra.Module"
  "HOL-Algebra.Ring_Divisibility"  
begin

text \<open>We define the ring of formal power series over a domain (idom) as a record to match 
HOL-Algebra definitions. We then show that it is a domain for addition and multiplication.
This is immediate with the existing theory from HOL-Analysis.

We then proceed to show the theorem similar to Hilbert's basis theorem but for the
ring of Formal power series.\<close>

subsection \<open>Preliminaries definition and lemmas\<close>

context
  fixes R::\<open>'a::{idom} ring\<close> (structure) 
  defines R:\<open>R \<equiv> \<lparr>carrier = UNIV, monoid.mult = (*), one = 1, zero = 0, add = (+)\<rparr>\<close>
begin

lemma ring_R:\<open>ring R\<close>
  apply(unfold_locales)
  using add.right_inverse 
  by (auto simp add: R  mult.assoc ab_semigroup_add_class.add_ac(1) 
      add.left_commute Units_def  add.commute ring_class.ring_distribs(2) 
      ring_class.ring_distribs(1) exI[of _ "- x" for x])

lemma domain_R:\<open>domain R\<close>
  apply(rule domainI)
    apply(rule cringI) 
      apply (simp add: ring.is_abelian_group ring_R)
     apply (metis Groups.mult_ac(2) R monoid.monoid_comm_monoidI 
      monoid.simps(1) ring.is_monoid ring_R)
    apply (simp add: ring.ring_simprules(13) ring_R)
   apply (simp add: R)
  by (simp add: R)

definition
  FPS_ring :: "'a::{idom} fps ring"
  where "FPS_ring = \<lparr>carrier = UNIV, monoid.mult = (*), one = 1, zero = 0, add = (+)\<rparr>"


lemma ring_FPS:\<open>ring FPS_ring\<close>
  apply(rule ringI)
     apply(rule abelian_groupI) 
          apply (simp_all add: FPS_ring_def ab_semigroup_add_class.add_ac(1) 
      add.left_commute add.commute)
     apply (metis ab_group_add_class.ab_left_minus add.commute)
    apply(rule monoidI)
  by(simp_all add: FPS_ring_def  mult.assoc ab_semigroup_add_class.add_ac(1) 
      add.left_commute add.commute ring_class.ring_distribs(2) ring_class.ring_distribs(1))  

lemma cring_FPS:\<open>cring FPS_ring\<close>
  apply(rule cringI)
    apply (simp add: ring.is_abelian_group ring_FPS)
   apply(rule comm_monoidI)
       apply (simp add: ring.ring_simprules(5) ring_FPS)
      apply (simp add: ring.ring_simprules(6) ring_FPS)
     apply (simp add: ring.ring_simprules(11) ring_FPS)
    apply (simp add: ring.ring_simprules(12) ring_FPS)
   apply (simp add: FPS_ring_def)
  by (simp add: ring.ring_simprules(13) ring_FPS)

lemma domain_FPS:\<open>domain FPS_ring\<close>
  apply(rule domainI)
    apply (simp add: cring_FPS)
   apply (simp add: FPS_ring_def)
  by (simp add: FPS_ring_def)

text \<open>valuation over $FPS_ring$\<close>

definition v_subdegree :: "('a::{idom}) fps \<Rightarrow> enat" where
  "v_subdegree f = (if f = 0 then \<infinity> else subdegree f)"

definition valuation::\<open>'a::{idom} fps \<Rightarrow> enat\<close> ("\<nu>")where
  \<open>\<nu> x \<equiv> Sup {enat k |k. x\<in> cgenideal FPS_ring (fps_X^k)}\<close>

lemma fps_X_pow_k_ideal_iff:\<open>cgenideal FPS_ring (fps_X^k) = {x. v_subdegree x \<ge> k}\<close>
proof(induct k)
  case 0
  then show ?case unfolding cgenideal_def
    using enat_def zero_enat_def 
    by (simp add: FPS_ring_def)
next
  case (Suc k)
  have \<open>x\<in>carrier FPS_ring \<Longrightarrow> v_subdegree (x*fps_X^r) \<ge> r\<close> for r x
    apply(cases \<open>x=0\<close>) 
    unfolding v_subdegree_def by(auto) 
  then show ?case unfolding cgenideal_def v_subdegree_def FPS_ring_def
    apply(safe)
     apply(auto simp:FPS_ring_def) [1]
    by (metis (mono_tags, opaque_lifting) UNIV_I enat_ord_simps(1) fps_shift_times_fps_X_power
        monoid.select_convs(1) mult_zero_left partial_object.select_convs(1))
qed

lemma valuation_miscs_1:assumes h1:\<open>f \<in>carrier FPS_ring\<close>
  shows \<open>(valuation f) = (\<infinity>::enat) \<longleftrightarrow> f = 0\<close>
  apply(safe)
  unfolding valuation_def apply(subst (asm) fps_X_pow_k_ideal_iff)
   apply (smt (verit, best) Sup_least infinity_ileE mem_Collect_eq v_subdegree_def)
  apply(subst fps_X_pow_k_ideal_iff)
  unfolding v_subdegree_def 
  unfolding enat_def apply(clarsimp)
  by (smt (verit, ccfv_threshold) Suc_ile_eq Sup_le_iff enat.exhaust enat_def enat_ord_simps(2) 
      mem_Collect_eq nat_less_le order.refl)

lemma valuation_miscs_0:
  shows \<open>valuation f = Inf {enat n |n. fps_nth f n \<noteq> 0}\<close>
proof(cases \<open>f=0\<close>)
  case 1:True
  have f1:\<open>valuation f = \<infinity>\<close> 
    using 1 valuation_miscs_1 
    by (simp add: FPS_ring_def)
  have f0:\<open>{enat n |n. fps_nth f n \<noteq> 0} = {}\<close> 
    by (simp add: "1")
  show ?thesis 
    apply(subst f0) 
    unfolding Inf_enat_def using f1 by(auto) 
next
  case 2:False
  have f0:\<open>fps_nth f n \<noteq> 0 \<Longrightarrow> f \<notin> cgenideal FPS_ring (fps_X^(Suc n))\<close> for n
    apply(subst fps_X_pow_k_ideal_iff) 
    unfolding v_subdegree_def
    using not_less_eq_eq subdegree_leI by auto
  then have \<open>f \<notin> cgenideal FPS_ring (fps_X^(n)) \<Longrightarrow> \<forall>i\<ge>n. f \<notin> cgenideal FPS_ring (fps_X^(i))\<close>
    for n
    by (simp add: 2 fps_X_pow_k_ideal_iff v_subdegree_def)
  with f0 have f2:\<open>fps_nth f n \<noteq> 0 \<Longrightarrow> valuation f \<le> n\<close> for n
    unfolding valuation_def 
    by (smt (verit, del_insts) Sup_le_iff enat_ord_simps(1) mem_Collect_eq not_less_eq_eq)
  then have \<open>valuation f =  v_subdegree f\<close>
    by (smt (verit, best) "2" Orderings.order_eq_iff Sup_le_iff fps_X_pow_k_ideal_iff 
        mem_Collect_eq v_subdegree_def valuation_def)
  then show ?thesis unfolding v_subdegree_def subdegree_def
    using 2 enat_def 
    by (smt (z3) "2" LeastI_ex cInf_eq_minimum enat_def f2 fps_nonzero_nth mem_Collect_eq)     
qed

lemma valuation_miscs_3:\<open>valuation f = v_subdegree f\<close>
proof(cases \<open>f=0\<close>)
  case 1:True
  have f1:\<open>valuation f = \<infinity>\<close> 
    using 1 valuation_miscs_1 
    by (simp add: FPS_ring_def)
  show ?thesis 
    by (metis "1" Formal_Power_Series_Ring.v_subdegree_def f1)
next
  case 2:False
  have f0:\<open>fps_nth f n \<noteq> 0 \<Longrightarrow> f \<notin> cgenideal FPS_ring (fps_X^(Suc n))\<close> for n
    apply(subst fps_X_pow_k_ideal_iff) 
    unfolding v_subdegree_def
    using not_less_eq_eq subdegree_leI by auto
  then have \<open>f \<notin> cgenideal FPS_ring (fps_X^(n)) \<Longrightarrow> \<forall>i\<ge>n. f \<notin> cgenideal FPS_ring (fps_X^(i))\<close> 
    for n
    by (simp add: 2 fps_X_pow_k_ideal_iff v_subdegree_def)
  with f0 have f2:\<open>fps_nth f n \<noteq> 0 \<Longrightarrow> valuation f \<le> n\<close> for n
    unfolding valuation_def 
    by (smt (verit, del_insts) Sup_le_iff enat_ord_simps(1) mem_Collect_eq not_less_eq_eq)
  then show \<open>valuation f =  v_subdegree f\<close>
    by (smt (verit, best) "2" Orderings.order_eq_iff Sup_le_iff fps_X_pow_k_ideal_iff 
        mem_Collect_eq v_subdegree_def valuation_def)
qed

lemma triangular_ineq_v:\<open>valuation (f + g) \<ge>  min (valuation f) (valuation g)\<close> 
  apply(subst (1 2 3) valuation_miscs_3) 
  unfolding v_subdegree_def 
  by (simp add: subdegree_add_ge')

lemma triang_eq_v:assumes h1:\<open>valuation f\<noteq> valuation g\<close> 
  shows \<open>valuation (f+g) = min (valuation f) (valuation g)\<close>
proof -
  have f0:\<open>valuation (f+g) \<ge> min (valuation f) (valuation g)\<close> 
    by (simp add:triangular_ineq_v FPS_ring_def)
  have \<open>valuation (f+g) \<le> min (valuation f) (valuation g)\<close>
    apply(subst (1 2 3) valuation_miscs_3) unfolding min_def v_subdegree_def
    by (smt (verit, ccfv_threshold) Suc_le_eq add_cancel_right_left add_diff_cancel_right' 
        add_eq_0_iff2 diff_zero enat_ord_simps(2) enat_ord_simps(3) h1 not_less_eq_eq order_le_less 
        subdegree_add_eq1 subdegree_add_eq2 subdegree_uminus v_subdegree_def valuation_miscs_3)
  then show ?thesis using f0 
    by order
qed

lemma prod_triang_v:\<open>valuation (f*g) = valuation f + valuation g\<close>
  apply(subst (1 2 3) valuation_miscs_3) 
  unfolding v_subdegree_def by(auto)


subsection \<open>Premisses for noetherian ring proof\<close>
definition subdeg_poly_set:\<open>subdeg_poly_set S k =  {a. a\<in>S \<and> subdegree a = k}\<union>{0}\<close>

definition sublead_coeff_set::\<open>'b::{zero} fps set\<Rightarrow> nat \<Rightarrow> 'b set\<close>
  where \<open>sublead_coeff_set S k \<equiv> { fps_nth a (subdegree a) | a. a\<in> subdeg_poly_set S k}\<close>

lemma ideal_nonempty:\<open>ideal I FPS_ring \<Longrightarrow> I \<noteq> {}\<close>
  by (metis FPS_ring_def UNIV_I empty_iff ideal.axioms(2) 
      partial_object.select_convs(1) ring.quotient_eq_iff_same_a_r_cos)

lemma mult_X_in_ideal:\<open>ideal I FPS_ring \<Longrightarrow> \<forall>x\<in>I. fps_X * x \<in> I\<close>
  unfolding ideal_def ideal_axioms_def 
  by (simp add: FPS_ring_def)

lemma non_empty_sublead:\<open>ideal I FPS_ring \<Longrightarrow> sublead_coeff_set I k \<noteq> {}\<close>
  unfolding sublead_coeff_set_def subdeg_poly_set by(auto)

lemma inv_unique:\<open>\<forall>x\<in>carrier FPS_ring. \<exists>!y. x + y = 0\<close>
  by (metis add.right_inverse add_diff_cancel_left')

lemma inv_same_degree:assumes h:\<open>x\<in>carrier FPS_ring\<close> 
  shows\<open>subdegree (inv\<^bsub>add_monoid FPS_ring\<^esub> x) = subdegree x\<close>
  by (metis FPS_ring_def ring_FPS abelian_group.a_group add_eq_0_iff2 group.l_inv h 
      monoid.select_convs(1) monoid.select_convs(2) partial_object.select_convs(1) ring_def 
      ring_record_simps(11) ring_record_simps(12) subdegree_uminus)

lemma inv_subdegree_is_inv: assumes h:"x\<in>carrier FPS_ring" 
  shows \<open>fps_nth (inv\<^bsub>add_monoid FPS_ring\<^esub> x) (subdegree x) = 
          (inv\<^bsub>add_monoid R\<^esub> (fps_nth x (subdegree x)))\<close>
  unfolding a_inv_def 
  by (metis FPS_ring_def ring_FPS R UNIV_I a_inv_def  
      fps_add_nth partial_object.select_convs(1)
      ring.ring_simprules(17) ring.ring_simprules(9) ring_R 
      ring_record_simps(12))

lemma subdeg_inv_in_sublead:
  assumes h1:\<open>ideal I FPS_ring\<close> and h2:\<open>a \<in> sublead_coeff_set I k\<close>
  shows \<open>inv\<^bsub>add_monoid R\<^esub> a \<in> sublead_coeff_set I k\<close>
proof -
  have f0:\<open>x\<in>I \<Longrightarrow> inv\<^bsub>add_monoid FPS_ring\<^esub> x \<in> I\<close> for x
    by (meson additive_subgroup_def h1 ideal.axioms(1) subgroup.m_inv_closed)
  then have f1:\<open>x\<in>I \<Longrightarrow> inv\<^bsub>add_monoid FPS_ring\<^esub> x \<in> subdeg_poly_set I (subdegree x)\<close> for x
    unfolding subdeg_poly_set using UnCI h1 ideal.Icarr[of I FPS_ring x] inv_same_degree[of x]
      mem_Collect_eq by(auto)
  have f2:\<open>x\<in>I \<Longrightarrow> (inv\<^bsub>add_monoid R\<^esub> (fps_nth x (subdegree x))) 
                        \<in> sublead_coeff_set I (subdegree x)\<close>
    for x
    unfolding sublead_coeff_set_def 
    using f1[of x] h1 ideal.Icarr[of I FPS_ring x] inv_same_degree[of x]
      inv_subdegree_is_inv[of x] mem_Collect_eq
    by force
  have \<open>0\<in>I\<close> 
    by (metis FPS_ring_def additive_subgroup.zero_closed h1 ideal.axioms(1) ring.simps(1))
  then have f3:\<open>a\<noteq>0 \<Longrightarrow> \<exists>x\<in>I. a = fps_nth x (subdegree x) \<and> subdegree x = k\<close> 
    using h2 unfolding sublead_coeff_set_def subdeg_poly_set
    by(auto)  
  then obtain x where \<open>a \<noteq>0 \<Longrightarrow> x\<in>I \<and> a = fps_nth x (subdegree x)\<and> subdegree x = k\<close> by blast
  then have f5:\<open>a\<noteq>0 \<Longrightarrow> inv\<^bsub>add_monoid R\<^esub> a = fps_nth (inv\<^bsub>add_monoid FPS_ring\<^esub> x) (subdegree x)\<close>
    by (metis FPS_ring_def UNIV_I inv_subdegree_is_inv partial_object.select_convs(1))
  then have f6:\<open>a\<noteq>0 \<Longrightarrow> fps_nth (inv\<^bsub>add_monoid FPS_ring\<^esub> x) (subdegree x) \<in> sublead_coeff_set I k\<close>
    using \<open>a \<noteq> 0 \<Longrightarrow> x \<in> I \<and> a = fps_nth x (subdegree x) \<and> subdegree x = k\<close> f2 by force
  then show ?thesis 
    apply(cases \<open>a=0\<close>)
     apply (metis R a_inv_def h2 ring.minus_zero ring_R ring_record_simps(11))
    using f5 by presburger
qed

lemma mult_stable_sublead:
  assumes h1:\<open>ideal I FPS_ring\<close>
    and h2:\<open>a \<in> sublead_coeff_set I k\<close> 
    and h3:\<open>b \<in> sublead_coeff_set I k\<close> 
  shows \<open>a \<otimes>\<^bsub>R\<^esub> b \<in> sublead_coeff_set I k\<close>
proof -
  have \<open>0\<in>I\<close> 
    by (metis FPS_ring_def additive_subgroup.zero_closed h1 ideal.axioms(1) ring.simps(1))
  {assume h4:\<open>a\<noteq>0\<close> and h5:\<open>b\<noteq>0\<close>
    then have f3:\<open>\<exists>x\<in>I. a = fps_nth x (subdegree x) \<and> subdegree x = k\<close> 
      using h2 unfolding sublead_coeff_set_def subdeg_poly_set
      by(auto) 
    then obtain x where f0:\<open> x\<in>I \<and> a = fps_nth x (subdegree x)\<and> subdegree x = k\<close> by blast
    then have \<open>fps_const b \<in>carrier FPS_ring\<close> 
      by (simp add: FPS_ring_def)
    then have \<open>fps_const b*x \<in> I\<close>
      by (metis FPS_ring_def f0 h1 ideal_axioms_def ideal_def monoid.simps(1))
    then have \<open>fps_nth (fps_const b * x) k = a*b\<close> 
      by (simp add: f0)
    then have \<open>subdegree (fps_const b * x) = k\<close> 
      using f0 h4 h5 by force
    then have \<open>a \<otimes>\<^bsub>R\<^esub> b \<in> sublead_coeff_set I k\<close>  
      unfolding sublead_coeff_set_def subdeg_poly_set FPS_ring_def 
      using R \<open>fps_const b * x \<in> I\<close> \<open>fps_nth (fps_const b * x) k = a * b\<close> by force
  }note proof_2=this
  then show ?thesis
    apply(cases \<open>a=0 \<or> b=0\<close>)
    using R h2 h3 by auto
qed

lemma add_stable_sublead:
  assumes h1:\<open>ideal I FPS_ring\<close>
    and h2:\<open>a \<in> sublead_coeff_set I k\<close> 
    and h3:\<open>b \<in> sublead_coeff_set I k\<close> 
  shows \<open>a \<otimes>\<^bsub>add_monoid R\<^esub> b \<in> sublead_coeff_set I k\<close>
proof -
  have f0:\<open>0\<in>I\<close> 
    by (metis FPS_ring_def additive_subgroup.zero_closed h1 ideal.axioms(1) ring.simps(1))
  have p2:\<open>a=-b \<Longrightarrow> a + b \<in> sublead_coeff_set I k\<close>
    unfolding sublead_coeff_set_def subdeg_poly_set by(auto)
  {assume h4:\<open>a\<noteq>0\<close> and h5:\<open>b\<noteq>0\<close> and h6:\<open>a\<noteq>- b\<close>
    then have f3:\<open>\<exists>x\<in>I. a = fps_nth x (subdegree x) \<and> subdegree x = k\<close> 
      using h2 unfolding sublead_coeff_set_def subdeg_poly_set
      by(auto) 
    then obtain x where f2:\<open> x\<in>I \<and> a = fps_nth x (subdegree x)\<and> subdegree x = k\<close> by blast
    have f4:\<open>\<exists>x\<in>I. b = fps_nth x (subdegree x) \<and> subdegree x = k\<close> 
      using f0 h3 h4 h5 unfolding sublead_coeff_set_def subdeg_poly_set
      by(auto) 
    then obtain y where f1:\<open>y\<in>I \<and> b = fps_nth y (subdegree y)\<and> subdegree y = k\<close> by blast
    then have \<open>x + y \<in> I\<close> using h1 unfolding ideal_def 
      using f2 additive_subgroup.a_closed[of I FPS_ring x y] 
      by (simp add: FPS_ring_def)
    have f4:\<open>fps_nth (x+y) k =  a + b\<close> 
      by (simp add: f1 f2)
    have \<open>\<forall>i<k. fps_nth (x+y) i = 0\<close> 
      by (simp add: f1 f2 nth_less_subdegree_zero)
    then have f5:\<open>subdegree (x + y) = k\<close> 
      by (metis \<open>fps_nth (x + y) k = a + b\<close> eq_neg_iff_add_eq_0 h6 subdegreeI)
    then have \<open>a+b \<in> sublead_coeff_set I k\<close> 
      using f4 f5 unfolding sublead_coeff_set_def subdeg_poly_set 
      using \<open>x + y \<in> I\<close> by force 
  }note proof_1=this
  then show ?thesis
    apply(cases \<open>a=0 \<or> b = 0 \<or> a = -b\<close>)
    using R h2 h3 p2 proof_1 by auto
qed 

lemma outer_stable_sublead:
  assumes h1:\<open>ideal I FPS_ring\<close>and h2:\<open>a \<in> sublead_coeff_set I k\<close> and h3:\<open>b \<in> carrier R\<close> 
  shows \<open>b \<otimes> a \<in> sublead_coeff_set I k\<close>
proof -
  have \<open>0\<in>I\<close> 
    by (metis FPS_ring_def additive_subgroup.zero_closed h1 ideal.axioms(1) ring.simps(1))
  then have p2:\<open>0\<in>sublead_coeff_set I k\<close> unfolding sublead_coeff_set_def subdeg_poly_set by(auto)
  {assume h4:\<open>a\<noteq>0\<close> and h5:\<open>b\<noteq>0\<close>
    then have f3:\<open>\<exists>x\<in>I. a = fps_nth x (subdegree x) \<and> subdegree x = k\<close> 
      using h2 unfolding sublead_coeff_set_def subdeg_poly_set
      by(auto) 
    then obtain x where f0:\<open> x\<in>I \<and> a = fps_nth x (subdegree x)\<and> subdegree x = k\<close> by blast
    then have \<open>fps_const b \<in>carrier FPS_ring\<close> 
      by (simp add: FPS_ring_def)
    then have \<open>fps_const b*x \<in> I\<close>
      by (metis FPS_ring_def f0 h1 ideal_axioms_def ideal_def monoid.simps(1))
    then have \<open>fps_nth (fps_const b * x) k = a*b\<close> 
      by (simp add: f0)
    then have \<open>subdegree (fps_const b * x) = k\<close> 
      using f0 h4 h5 by force
    then have \<open>b \<otimes>\<^bsub>R\<^esub> a \<in> sublead_coeff_set I k\<close>  
      unfolding sublead_coeff_set_def subdeg_poly_set FPS_ring_def 
      using R \<open>fps_const b * x \<in> I\<close> \<open>fps_nth (fps_const b * x) k = a * b\<close> by force
  }note proof_2=this
  then show ?thesis 
    apply(cases \<open>a=0 \<or> b=0\<close>) 
    using R h2 h3 proof_2 p2 by auto
qed

lemma sublead_ideal:\<open>ideal I FPS_ring \<Longrightarrow> ideal (sublead_coeff_set I k) R\<close>
  apply(rule idealI)
     apply(simp add:ring_R)
    apply(rule group.subgroupI) 
  using abelian_group.a_group ring.is_abelian_group ring_R apply fastforce
       apply (simp add: R)
      apply(simp add:non_empty_sublead) 
  using subdeg_inv_in_sublead apply blast
  using add_stable_sublead apply force
   apply (simp add: outer_stable_sublead mult.commute)
  by (metis Groups.mult_ac(2) R monoid.simps(1) outer_stable_sublead)

lemma order_sublead:
  assumes h1:\<open>J1 \<subseteq> J2\<close> and h2:\<open>ideal J1 FPS_ring\<close> and h3:\<open>ideal J2 FPS_ring\<close>
  shows \<open>sublead_coeff_set J1 k \<subseteq> sublead_coeff_set J2 k\<close>
  unfolding sublead_coeff_set_def subdeg_poly_set 
  using h1 by blast

lemma sup_sublead_stable_add:\<open>ideal I FPS_ring \<Longrightarrow>
           a \<in> \<Union> (range (sublead_coeff_set I)) \<Longrightarrow>
           b \<in> \<Union> (range (sublead_coeff_set I))
  \<Longrightarrow> a \<otimes>\<^bsub>add_monoid R\<^esub> b \<in> \<Union> (range (sublead_coeff_set I))\<close>
proof -
  have f2:\<open>x\<noteq>0 \<and> x\<in>subdeg_poly_set I k \<Longrightarrow> subdegree x = k\<close> for x k
    unfolding subdeg_poly_set by auto
  then have f1:\<open>x\<noteq>0 \<and> x\<in>subdeg_poly_set I k \<Longrightarrow> fps_nth x k \<in> sublead_coeff_set I k\<close> for x k
    unfolding sublead_coeff_set_def by blast
  assume h1:\<open>ideal I FPS_ring\<close> \<open>a \<in> \<Union> (range (sublead_coeff_set I))\<close> 
    \<open>b \<in> \<Union> (range (sublead_coeff_set I))\<close>
  then obtain x x' k k' 
    where f0:\<open>a = fps_nth x k \<and> x\<in>subdeg_poly_set I k \<and> b = fps_nth x' k' \<and> x'\<in>subdeg_poly_set I k'\<close>
    unfolding sublead_coeff_set_def apply(safe)
    by (metis (mono_tags, lifting) Un_def mem_Collect_eq subdeg_poly_set)
  have p1:\<open>k=k'\<Longrightarrow>a\<noteq>0 \<Longrightarrow>b\<noteq>0 \<Longrightarrow> a\<in>sublead_coeff_set I k \<and> b \<in> sublead_coeff_set I k\<close>
    using h1 f0 f1 fps_nonzero_nth by blast
  have f3:\<open>k<k' \<Longrightarrow> a\<noteq>0 \<Longrightarrow> b\<noteq>0 \<Longrightarrow> fps_X^(k'-k)*x \<in> I\<close>
    by (metis (no_types, lifting) Formal_Power_Series_Ring.FPS_ring_def UNIV_I Un_iff 
        additive_subgroup.zero_closed f0 h1(1) ideal_axioms_def ideal_def mem_Collect_eq monoid.simps(1) 
        partial_object.select_convs(1) ring.simps(1) singletonD subdeg_poly_set)
  then have f4:\<open>k<k' \<Longrightarrow> a\<noteq>0 \<Longrightarrow> b\<noteq>0 \<Longrightarrow> subdegree (fps_X^(k'-k)*x) = k'\<close>
    by (metis f2 add_diff_inverse_nat f0 fps_nonzero_nth fps_subdegree_mult_fps_X_power(1) 
        less_numeral_extra(3) nat_diff_split_asm zero_less_diff)
  then have f5:\<open>k<k'\<Longrightarrow> a\<noteq>0 \<Longrightarrow> b\<noteq> 0 \<Longrightarrow> (fps_X^(k'-k)*x) \<in> subdeg_poly_set I k'\<close> 
    unfolding subdeg_poly_set using f3 by auto
  then have f6:\<open>k<k' \<Longrightarrow> a\<noteq>0 \<Longrightarrow> b\<noteq>0 
    \<Longrightarrow> fps_nth ((fps_X^(k'-k)*x) + x') k' \<in> \<Union> (range (sublead_coeff_set I))\<close>
    by (metis R UNIV_I UN_iff add_stable_sublead f0 f1 fps_add_nth fps_mult_fps_X_power_nonzero(1) 
        fps_zero_nth h1(1) monoid.simps(1) ring_record_simps(12))
  have f7:\<open>b \<noteq> 0 \<Longrightarrow> k < k'\<Longrightarrow> a = - b \<Longrightarrow> \<exists>r. 0 \<in> sublead_coeff_set I r \<close>
    by (metis R additive_subgroup.zero_closed h1(1) ideal_def ring.simps(1) sublead_ideal)
  have f8:\<open>a \<noteq> 0 \<Longrightarrow> b \<noteq> 0 \<Longrightarrow> k < k' \<Longrightarrow> a \<noteq> - b \<Longrightarrow> \<exists>r. a + b \<in> sublead_coeff_set I r\<close>
    by (metis UN_E add_diff_cancel_left' add_less_same_cancel2 diff_add_inverse2 f0 f6 
        fps_X_power_mult_nth fps_add_nth less_imp_add_positive not_less_zero)
  then have p2:\<open>a \<noteq> 0 \<Longrightarrow> b \<noteq> 0 \<Longrightarrow> k < k' \<Longrightarrow> \<exists>r. a \<oplus> b \<in> sublead_coeff_set I r\<close>
    apply(cases \<open>a=-b\<close>)
    by(auto simp:R FPS_ring_def f7) 
  have f3':\<open>k'<k \<Longrightarrow> a\<noteq>0 \<Longrightarrow> b\<noteq>0 \<Longrightarrow> fps_X^(k-k')*x' \<in> I\<close>
    by (metis (no_types, lifting) Formal_Power_Series_Ring.FPS_ring_def UNIV_I Un_iff 
        additive_subgroup.zero_closed f0 h1(1) ideal_axioms_def ideal_def mem_Collect_eq monoid.simps(1) 
        partial_object.select_convs(1) ring.simps(1) singletonD subdeg_poly_set)
  then have f4':\<open>k'<k \<Longrightarrow> a\<noteq>0 \<Longrightarrow> b\<noteq>0 \<Longrightarrow> subdegree (fps_X^(k-k')*x') = k\<close>
    by (metis f2 add_diff_inverse_nat f0 fps_nonzero_nth fps_subdegree_mult_fps_X_power(1) 
        less_numeral_extra(3) nat_diff_split_asm zero_less_diff)
  then have f5':\<open>k'<k\<Longrightarrow> a\<noteq>0 \<Longrightarrow> b\<noteq> 0 \<Longrightarrow> (fps_X^(k-k')*x') \<in> subdeg_poly_set I k\<close> 
    unfolding subdeg_poly_set using f3' by auto
  then have f6':\<open>k'<k \<Longrightarrow> a\<noteq>0 \<Longrightarrow> b\<noteq>0 
  \<Longrightarrow> fps_nth ((fps_X^(k-k')*x') + x) k \<in> \<Union> (range (sublead_coeff_set I))\<close>
    by (metis R UNIV_I UN_iff add_stable_sublead f0 f1 fps_add_nth fps_mult_fps_X_power_nonzero(1) 
        fps_zero_nth h1(1) monoid.simps(1) ring_record_simps(12))
  have f7':\<open>b \<noteq> 0 \<Longrightarrow> k' < k \<Longrightarrow> a = - b \<Longrightarrow> \<exists>r. 0 \<in> sublead_coeff_set I r \<close>
    by (metis R additive_subgroup.zero_closed h1(1) ideal_def ring.simps(1) sublead_ideal)
  have f8':\<open>a \<noteq> 0 \<Longrightarrow> b \<noteq> 0 \<Longrightarrow> k' < k \<Longrightarrow> a \<noteq> - b \<Longrightarrow> \<exists>r. a + b \<in> sublead_coeff_set I r\<close>
    by (metis (no_types, lifting) UN_iff f8 add.commute add_diff_cancel_right' add_diff_inverse_nat 
        f0 f4' f6' fps_X_power_mult_nth fps_add_nth not_less_zero nth_subdegree_zero_iff subdegree_0)
  then have p3:\<open>a \<noteq> 0 \<Longrightarrow> b \<noteq> 0 \<Longrightarrow> k' < k \<Longrightarrow> \<exists>r. a \<oplus> b \<in> sublead_coeff_set I r\<close>
    apply(cases \<open>a=-b\<close>)
    by(auto simp:R FPS_ring_def f7') 
  have cases:\<open>k=k' \<or> k<k' \<or> k'<k\<close> 
    by auto
  then show ?thesis
    apply(cases \<open>a=0 \<or> b= 0\<close>)
    using R h1(2) h1(3) apply force
    using Formal_Power_Series_Ring.add_stable_sublead R h1(1) p1 p2 p3 by(force) 
qed

lemma sup_sublead_ideal:\<open>ideal I FPS_ring \<Longrightarrow> ideal (\<Union> k. sublead_coeff_set I k) R\<close> 
  apply(rule idealI)
     apply (simp add: ring_R)
    apply(rule group.subgroupI) 
  using abelian_group.a_group ring.is_abelian_group ring_R apply blast
       apply (simp add: R)
  using non_empty_sublead apply force
  using subdeg_inv_in_sublead apply force
  using sup_sublead_stable_add apply force
   apply (metis UN_iff outer_stable_sublead)
  by (metis UN_iff ideal.I_r_closed sublead_ideal)

(* lemma v_sub_eq_sub:\<open>f\<noteq>0 \<Longrightarrow> v_subdegree f = subdegree f\<close>
  unfolding v_subdegree_def subdegree_def by(auto)
 *)
lemma Sub_subdeg_eq_ideal:\<open>ideal J FPS_ring \<Longrightarrow> (\<Union>k. subdeg_poly_set J k) = J\<close>
  unfolding subdeg_poly_set apply(safe) 
   apply (metis Formal_Power_Series_Ring.FPS_ring_def 
      additive_subgroup.zero_closed ideal.axioms(1) ring.simps(1))
  by auto


lemma eq_subdeg:
  assumes h1:\<open>J1 \<subseteq> J2\<close> 
    and h3:\<open> ideal J1 FPS_ring\<close> and h4:\<open>ideal J2 FPS_ring\<close>
  shows \<open>J1 = J2 \<longleftrightarrow> (\<forall>k. subdeg_poly_set J1 k = subdeg_poly_set J2 k)\<close>
proof -
  have \<open>\<forall>k. subdeg_poly_set J1 k = subdeg_poly_set J2 k 
        \<Longrightarrow> (\<Union>k. subdeg_poly_set J1 k) = (\<Union>k. subdeg_poly_set J2 k)\<close>
    by auto
  then have f0:\<open>\<forall>k. subdeg_poly_set J1 k = subdeg_poly_set J2 k \<Longrightarrow> J1 = J2\<close>
    by (metis Sub_subdeg_eq_ideal h3 h4)
  have f1:\<open>J1 = J2 \<Longrightarrow> \<forall>k. subdeg_poly_set J1 k = subdeg_poly_set J2 k\<close>
    unfolding subdeg_poly_set by auto
  then show ?thesis using f0 f1 by auto
qed

lemma inculded_sublead:\<open>ideal I FPS_ring \<Longrightarrow> sublead_coeff_set I k \<subseteq> sublead_coeff_set I (k+1)\<close>
  unfolding sublead_coeff_set_def subdeg_poly_set
proof(safe) 
  fix x a
  assume \<open>ideal I local.FPS_ring\<close>
    \<open>a \<in> I\<close>
    \<open>k = subdegree a \<close>
  show \<open>\<exists>aa. fps_nth a (subdegree a) = fps_nth aa (subdegree aa) 
        \<and> aa \<in> {aa \<in> I. subdegree aa = subdegree a + 1} \<union> {0}\<close>
    apply(rule exI[where x=\<open>fps_X * a\<close>]) 
    by (simp add:subdegree_eq_0_iff \<open>a \<in> I\<close> \<open>ideal I local.FPS_ring\<close> mult_X_in_ideal)+
next 
  show \<open>\<exists>a. fps_nth 0 (subdegree 0) = fps_nth a (subdegree a) 
        \<and> a \<in> {a \<in> I. subdegree a = k + 1} \<union> {0}\<close>
    by auto
qed

lemma included_sublead_gen:assumes \<open>ideal I FPS_ring\<close> \<open>k\<le>k'\<close> 
  shows \<open>sublead_coeff_set I k \<subseteq> sublead_coeff_set I (k')\<close>
  using assms 
  apply(induct \<open>k'-k\<close>)
   apply simp 
  by (metis Suc_eq_plus1 inculded_sublead lift_Suc_mono_le)

lemma sup_sublead:
  assumes h1:\<open>ideal I FPS_ring\<close> 
    and h2: \<open>noetherian_ring R\<close> 
  shows \<open>(\<Union>{sublead_coeff_set I k|k. k\<in>UNIV}) \<in> {sublead_coeff_set I k|k. k\<in>UNIV}\<close>
  apply(rule noetherian_ring.ideal_chain_is_trivial[OF h2, of \<open>{sublead_coeff_set I k|k. k\<in>UNIV}\<close>])
   apply blast
  unfolding subset_chain_def using included_sublead_gen 
  by(auto simp add: h1 sublead_ideal)(meson h1 in_mono linorder_linear)

lemma subdeg_inf_imp_s_tendsto_zero:
  fixes s::\<open>nat \<Rightarrow> 'a::{idom} fps\<close>
  assumes g2:\<open>strict_mono (\<lambda>n. subdegree (s n))\<close>
  shows \<open>s \<longlonglongrightarrow> 0\<close>
proof -
  have g1:\<open>(\<lambda>x. 1/x) \<longlonglongrightarrow> 0\<close> 
    using lim_1_over_n by force
  have \<open>\<forall>n. \<exists>k. n < subdegree (s k)\<close>
    by (metis dual_order.strict_trans g2 gt_ex linorder_not_le 
        nat_neq_iff strict_mono_imp_increasing)
  have r1:\<open>r>0 \<Longrightarrow> (n::nat) > log 2 (1/r) \<Longrightarrow> (1/2^n < r) \<longleftrightarrow> 2^n > 1/r\<close> for n r
    by(auto simp:field_simps) 
  have r2:\<open>r>0 \<Longrightarrow> (n::nat) > log 2 (1/r) \<Longrightarrow> 2^n > 2 powr (log 2 (1/r))\<close> for n r
    by (simp add: log_less_iff powr_realpow)
  then have r3:\<open>r>0 \<Longrightarrow> (n::nat) > log 2 (1/r) \<Longrightarrow>  2 powr (log 2 (1/r)) =  1/r\<close> for r n
    by auto
  then have r4:\<open>r>0 \<Longrightarrow> (n::nat) > log 2 (1/r) \<Longrightarrow> 2^n > 1/r\<close> for r n
    using \<open>\<And>r n. \<lbrakk>0 < r; log 2 (1 / r) < real n\<rbrakk> \<Longrightarrow> 2 powr log 2 (1 / r) < 2 ^ n\<close> by force
  then have r5:\<open>r>0 \<Longrightarrow> (n::nat) > log 2 (1/r) \<Longrightarrow> 1/2^n < r\<close> for r n
    using \<open>\<And>r n. \<lbrakk>0 < r; log 2 (1 / r) < real n\<rbrakk> \<Longrightarrow> (1 / 2 ^ n < r) = (1 / r < 2 ^ n)\<close> by blast
  have \<open>ceiling (r::real) \<ge> r\<close> for r
    by simp
  then have r6:\<open>r>0 \<Longrightarrow> (ceiling (log 2 (1/r))) \<ge> log 2 (1/r)\<close> for r
    by auto
  then have r7:\<open>r>0 \<Longrightarrow> (n::nat) >  (ceiling (log 2 (1/r))) \<Longrightarrow> 1/2^n < r\<close> for r n
    by (metis \<open>\<And>r n. \<lbrakk>0 < r; log 2 (1 / r) < real n\<rbrakk> \<Longrightarrow> 1 / 2 ^ n < r\<close> 
        ceiling_less_cancel ceiling_of_nat)
  have r8:\<open>r>0 \<Longrightarrow> \<exists>n::nat. n> (log 2 (1/r))\<close> for r 
    by (simp add: reals_Archimedean2)
  have r9:\<open>\<forall>(r::real)>0. \<exists>n0. \<forall>n\<ge>n0. 1/2^n < r\<close>
  proof(safe)
    fix r::real 
    assume \<open>r>0\<close>
    then obtain n::nat where \<open>n> (log 2 (1/r))\<close> using r8 by blast
    show \<open>\<exists>n0. \<forall>n\<ge>n0. 1 / 2 ^ n < r\<close>
      apply(rule exI[where x=n])
      using \<open>0 < r\<close> \<open>log 2 (1 / r) < real n\<close> r5 by auto
  qed
  show t2:\<open>s \<longlonglongrightarrow> 0\<close>
  proof(rule metric_LIMSEQ_I) 
    fix r::real
    assume \<open>0<r\<close>
    then obtain n where \<open>n>0 \<and> 1/2^n < r\<close> using r9  
      by (metis gr0I less_or_eq_imp_le zero_less_numeral)
    then have \<open>\<forall>k\<ge>n. inverse (2^k) < r\<close> 
      by (smt (verit, ccfv_threshold) inverse_eq_divide 
          inverse_less_iff_less power_increasing_iff zero_less_power)
    then obtain n1 where \<open>1/2^(subdegree (s n1)) < r \<and> n1>0\<close> 
      by (metis \<open>\<forall>n. \<exists>k. n < subdegree (s k)\<close> bot_nat_0.not_eq_extremum divide_inverse 
          mult_1 nle_le not_less_iff_gr_or_eq order_less_le_trans)
    then have \<open>dist (s n1) 0 < r\<close> 
      by (simp add: \<open>0 < r\<close> dist_fps_def inverse_eq_divide)
    then show \<open>\<exists>no. \<forall>n\<ge>no. dist (s n) 0 < r\<close>
      apply(intro exI[where x=n1])
      apply(safe) using g2 
      unfolding dist_fps_def strict_mono_def
      using power_strict_increasing_iff[of 2 \<open>subdegree (s n1)\<close>] inverse_eq_divide inverse_le_iff_le
      by (smt (verit) \<open>0 < r\<close> \<open>1 / 2 ^ subdegree (s n1) < r \<and> 0 < n1\<close> 
          diff_zero le_eq_less_or_eq power_less1_D)
  qed
qed




lemma idl_sum:\<open>finite A \<Longrightarrow> ideal {x. \<exists>s. x=(\<Sum>i\<in>{0..<card A}. s i * from_nat_into A i)} R\<close> for A
proof(rule idealI)
  assume \<open>finite A\<close>
  show \<open>ring R\<close>
    using ring_R by(simp)
  show \<open>subgroup {x. \<exists>s. x = (\<Sum>i = 0..<card A. s i * from_nat_into A i)} (add_monoid R)\<close>
  proof(rule group.subgroupI)
    show \<open>Group.group (add_monoid R)\<close>
      using abelian_group.a_group ring.is_abelian_group ring_R by blast
    show \<open>{x. \<exists>s. x = (\<Sum>i = 0..<card A. s i * from_nat_into A i)} \<subseteq> carrier (add_monoid R)\<close>
      by (simp add: R)
    show \<open>{x. \<exists>s. x = (\<Sum>i = 0..<card A. s i * from_nat_into A i)} \<noteq> {}\<close>
      by blast
  next
    fix a assume \<open>a \<in> {x. \<exists>s. x = (\<Sum>i = 0..<card A. s i * from_nat_into A i)}\<close>
    then show \<open>inv\<^bsub>add_monoid R\<^esub> a \<in> {x. \<exists>s. x = (\<Sum>i = 0..<card A. s i * from_nat_into A i)}\<close>
    proof(safe) 
      fix s
      have p6:\<open>(THE y. (\<Sum>i = 0..<card A. s i * from_nat_into A i) + y = 0 \<and> y +
(\<Sum>i = 0..<card A. s i * from_nat_into A i) = 0)
= (\<Sum>i = 0..<card A. - (s i * from_nat_into A i))\<close> for A::\<open>'a set\<close> and s
        using theI'[of \<open>\<lambda>y. (\<Sum>i = 0..<card A. s i * from_nat_into A i) + y = 0 \<and> y + 
(\<Sum>i = 0..<card A. s i * from_nat_into A i) = 0\<close>]
        by (smt (verit, best) add.commute add.right_inverse add_left_imp_eq sum.cong sum_negf)
      assume \<open>a = (\<Sum>i = 0..<card A. s i * from_nat_into A i)\<close>
      then show \<open> \<exists>sa. inv\<^bsub>add_monoid R\<^esub> (\<Sum>i = 0..<card A. s i * 
from_nat_into A i) = (\<Sum>i = 0..<card A. sa i * from_nat_into A i)\<close> 
        apply(intro exI[where  x=\<open>-s\<close>])
        by(auto simp add:m_inv_def p6 R)
    qed
  next
    fix a b
    assume \<open>a \<in> {x. \<exists>s. x = (\<Sum>i = 0..<card A. s i * from_nat_into A i)}\<close> 
      \<open>b \<in> {x. \<exists>s. x = (\<Sum>i = 0..<card A. s i * from_nat_into A i)}\<close>
    then show \<open>a \<otimes>\<^bsub>add_monoid R\<^esub> b \<in> {x. \<exists>s. x = (\<Sum>i = 0..<card A. s i * from_nat_into A i)}\<close>
    proof(safe)
      fix s sa
      assume \<open>a = (\<Sum>i = 0..<card A. s i * from_nat_into A i)\<close>
        \<open>b = (\<Sum>i = 0..<card A. sa i * from_nat_into A i)\<close>
      then show \<open> \<exists>sb. (\<Sum>i = 0..<card A. s i * from_nat_into A i) \<otimes>\<^bsub>add_monoid R\<^esub>
(\<Sum>i = 0..<card A. sa i * from_nat_into A i) = (\<Sum>i = 0..<card A. sb i * from_nat_into A i)\<close>
        apply(intro exI[where x=\<open>\<lambda>i. s i + sa i\<close>])
        by(simp add:R comm_semiring_class.distrib sum.distrib) 
    qed
  qed
next
  fix a x 
  assume \<open>finite A\<close> \<open>a \<in> {x. \<exists>s. x = (\<Sum>i = 0..<card A. s i * from_nat_into A i)}\<close> \<open>x \<in> carrier R\<close>
  then show \<open>x \<otimes> a \<in> {x. \<exists>s. x = (\<Sum>i = 0..<card A. s i * from_nat_into A i)}\<close> 
    \<open>a \<otimes> x \<in> {x. \<exists>s. x = (\<Sum>i = 0..<card A. s i * from_nat_into A i)}\<close>
  proof(safe)
    fix s
    assume \<open>a = (\<Sum>i = 0..<card A. s i * from_nat_into A i)\<close>
    then show 
      \<open>\<exists>sa. x \<otimes> (\<Sum>i = 0..<card A. s i * from_nat_into A i) = (\<Sum>i = 0..<card A. sa i * from_nat_into A i)\<close>
      apply(intro  exI[where x=\<open>(\<lambda>i. x * s i)\<close>])
      by (simp add:R comm_semiring_class.distrib sum.distrib mult.assoc sum_distrib_left) 
    show 
      \<open>\<exists>sa. (\<Sum>i = 0..<card A. s i * from_nat_into A i) \<otimes> x = (\<Sum>i = 0..<card A. sa i * from_nat_into A i)\<close>
      apply(intro  exI[where x=\<open>(\<lambda>i. x * s i)\<close>])
      by (simp add:R comm_semiring_class.distrib sum.distrib mult.assoc 
          sum_distrib_left mult.left_commute mult.commute) 
  qed
qed

lemma genideal_sum_rep: 
  \<open>finite A \<Longrightarrow> genideal R A = {x. \<exists>s. x=(\<Sum>i\<in>{0..<card A}. s i * from_nat_into A i)}\<close> for A
proof(subst set_eq_subset, rule conjI)
  assume hr:\<open>finite A\<close>
  then have unq:\<open>x\<in>A \<Longrightarrow> \<exists>!i. i<card A \<and> from_nat_into A i = x\<close> for x
    using bij_betw_from_nat_into_finite[of A, OF \<open>finite A\<close>] 
    unfolding bij_betw_def inj_on_def
    by (smt (verit, ccfv_threshold) \<open>bij_betw (from_nat_into A) {..<card A} A\<close>
        bij_betw_iff_bijections lessThan_iff)
  have \<open>A\<noteq>{}\<Longrightarrow>  (card ({0..<card A} \<inter> {i. from_nat_into A i = x})) = 1\<close> if hh:\<open>x\<in>A\<close> for x
  proof(rule ccontr) 
    assume hhh:\<open>card ({0..<card A} \<inter> {i. from_nat_into A i = x}) \<noteq> 1\<close> \<open>A\<noteq>{}\<close>
    then have jm:
      \<open>card ({0..<card A} \<inter> {i. from_nat_into A i = x}) > 1 \<Longrightarrow> \<exists>i1 i2. i1\<noteq>i2 \<and> i1 <card A 
\<and> i2<card A\<and> from_nat_into A i1 = from_nat_into A i2 \<and> from_nat_into A i1 = x\<close>
      by (smt (verit, ccfv_SIG) Int_Collect One_nat_def atLeastLessThan_iff card_le_Suc0_iff_eq
          finite_Int finite_atLeastLessThan linorder_not_less n_not_Suc_n)
    then have \<open>card ({0..<card A} \<inter> {i. from_nat_into A i = x}) > 1\<close> using hhh hr 
      by (metis (mono_tags, lifting) Int_def atLeastLessThan_iff card_eq_0_iff emptyE finite_Int 
          finite_atLeastLessThan le0 less_one linorder_neqE_nat mem_Collect_eq that unq)
    then show False using jm unq[OF hh] by(auto) 
  qed
  then have \<open>A\<subseteq>{x. \<exists>s. x = (\<Sum>i = 0..<card A. s i * from_nat_into A i)}\<close>
  proof(safe) 
    fix x
    assume hhhh:\<open>(\<And>x. x \<in> A \<Longrightarrow> A \<noteq> {} \<Longrightarrow> card ({0..<card A} \<inter> {i. from_nat_into A i = x}) = 1)\<close>
      \<open>x\<in>A\<close>
    then have \<open>of_nat (card ({0..<card A} \<inter> {xa. from_nat_into A xa = x})) = 1\<close>
      by (metis One_nat_def card.empty less_nat_zero_code of_nat_1 unq)
    with hhhh show \<open>\<exists>s. x = (\<Sum>i = 0..<card A. s i * from_nat_into A i)\<close>
      apply(cases \<open>x=0\<close>)
       apply(rule exI[where x=\<open>\<lambda>i. 0\<close>])
       apply(simp)
      apply(rule exI[where x=\<open>\<lambda>i. if from_nat_into A i = x then 1 else 0\<close>])
      apply(subst if_distrib[where f=\<open>\<lambda>x. x*a\<close> for a])
      apply(subst sum.If_cases)
      by(simp)+ 
  qed
  then show \<open>Idl A \<subseteq> {x. \<exists>s. x = (\<Sum>i = 0..<card A. s i * from_nat_into A i)}\<close>
    unfolding genideal_def using idl_sum[OF hr] by(auto)
  show \<open>{x. \<exists>s. x = (\<Sum>i = 0..<card A. s i * from_nat_into A i)} \<subseteq> Idl A \<close>
  proof(safe) 
    fix x and s::\<open>nat\<Rightarrow>'a\<close>
    have a:\<open>\<forall>i<card A. from_nat_into A i \<in> A\<close>  
      by (metis card.empty from_nat_into less_nat_zero_code)
    then have b:\<open>\<forall>i. s i \<in> carrier R\<close>
      using R by auto
    then have \<open>\<forall>i<card A. s i *  from_nat_into A i \<in> genideal R A\<close>
      using ring.genideal_ideal[OF ring_R, of A]  ideal.I_l_closed[of _ R ]
      by (metis R a ideal_def monoid.simps(1) partial_object.select_convs(1) 
          ring.genideal_self subsetD subset_UNIV) 
    have ff:\<open>A\<subseteq> carrier R\<close> by (simp add:R)
    then have \<open>\<forall>i<n. g i \<in> genideal R A \<Longrightarrow>  (\<Sum>i\<in>{0..<n}. g i) \<in> genideal R A\<close>
      for g::\<open>nat \<Rightarrow> 'a\<close> and n
      apply(induct n) 
       apply (metis R additive_subgroup.zero_closed atLeastLessThan_iff 
          ideal_def not_less_zero ring.genideal_ideal ring.simps(1) ring_R sum.neutral)
      using ring.genideal_ideal[OF ring_R, of A, OF \<open>A\<subseteq> carrier R\<close>] 
        additive_subgroup.a_closed[of \<open>genideal R A\<close> R _ _] unfolding ideal_def by(auto simp:R) 
    then show \<open>(\<Sum>i = 0..<card A. s i * from_nat_into A i) \<in> Idl A\<close>
      using \<open>\<forall>i<card A. s i * from_nat_into A i \<in> Idl A\<close> by presburger
  qed
qed


lemma fps_sum_rep_nth': 
  "fps_nth (sum (\<lambda>i. fps_const(a i)*fps_X^i) {0..m}) n = (if n \<le> m then a n else 0)"
  by (simp add: fps_sum_nth if_distrib cong del: if_weak_cong)

lemma abs_tndsto: shows \<open>(\<lambda>n. (\<Sum>i\<le>n. fps_const (s i) * fps_X^i)::'a fps) \<longlonglongrightarrow> Abs_fps s\<close>  
  (is \<open>?s \<longlonglongrightarrow> ?a\<close>)
proof -
  have "\<exists>n0. \<forall>n \<ge> n0. dist (?s n) ?a < r" if "r > 0" for r
  proof -
    obtain n0 where n0: "(1/2)^n0 < r" "n0 > 0"
      using reals_power_lt_ex[OF \<open>r > 0\<close>, of 2] by auto
    show ?thesis
    proof -
      have "dist (?s n) ?a < r" if nn0: "n \<ge> n0" for n
      proof -
        from that have thnn0: "(1/2)^n \<le> (1/2 :: real)^n0"
          by (simp add: field_split_simps)
        show ?thesis
        proof (cases "?s n = ?a")
          case True
          then show ?thesis
            unfolding metric_space.dist_eq_0_iff
            using \<open>r > 0\<close> by (simp del: dist_eq_0_iff)
        next
          case False
          from False have dth: "dist (?s n) ?a = (1/2)^subdegree (?s n - ?a)"
            by (simp add: dist_fps_def field_simps)
          from False have kn: "subdegree (?s n - ?a) > n"
            apply (intro subdegree_greaterI) apply(simp_all add: fps_sum_rep_nth')
            by (metis (full_types) atLeast0AtMost fps_sum_rep_nth')
          then have "dist (?s n) ?a < (1/2)^n"
            by (simp add: field_simps dist_fps_def)
          also have "\<dots> \<le> (1/2)^n0"
            using nn0 by (simp add: field_split_simps)
          also have "\<dots> < r"
            using n0 by simp
          finally show ?thesis .
        qed
      qed
      then show ?thesis by blast
    qed
  qed
  then show ?thesis
    unfolding lim_sequentially by blast
qed

lemma add_stable_FPS_ring:\<open>ideal I FPS_ring \<Longrightarrow> a\<in>I \<Longrightarrow> b\<in>I \<Longrightarrow> a+b \<in> I\<close>
  unfolding FPS_ring_def 
  by (metis additive_subgroup.a_closed ideal.axioms(1) ring_record_simps(12))


lemma abs_tndsto_le: shows \<open>(\<lambda>n. (\<Sum>i<n. fps_const (s i) * fps_X^i)::'a fps) \<longlonglongrightarrow> Abs_fps s\<close>  
  using LIMSEQ_lessThan_iff_atMost abs_tndsto by blast


lemma bij_betw_strict_mono:
  assumes \<open>strict_mono (f::nat\<Rightarrow>nat)\<close>
  shows \<open>bij_betw f UNIV (f`UNIV)\<close>
  by (simp add: assms bij_betw_imageI strict_mono_on_imp_inj_on)

lemma no_i_inf_0:\<open>strict_mono (f::nat\<Rightarrow>nat) \<Longrightarrow> i<f 0 \<Longrightarrow> \<not>(\<exists>j. f j = i)\<close>
  by (auto simp add: strict_mono_less)

lemma inter_mt:\<open>strict_mono (f::nat\<Rightarrow>nat) \<Longrightarrow> {..<f 0} \<inter> range f = {}\<close>
  by (metis Int_emptyI lessThan_iff no_i_inf_0 rangeE)

lemma range_inter_f:\<open>strict_mono (f::nat\<Rightarrow>nat) \<Longrightarrow> {..<f n} \<inter> range f = f`{0..<n}\<close>
  apply(induct n)
   apply (simp add: inter_mt)
  by (auto simp:strict_mono_less strict_monoD)

lemma simp_rule_sum:\<open>strict_mono (f::nat\<Rightarrow>nat) \<Longrightarrow> (\<Sum>i\<in>{..<f (Suc n)}. (if i \<in> range f
   then (s ((inv_into UNIV f) i)) *fps_X^i else 0)) = (\<Sum>i\<in>{..<f n}. (if i \<in> range f then 
(s ((inv_into UNIV f) i)) *fps_X^i else 0)) + (s ((inv_into UNIV f) (f n))) *fps_X^(f n)\<close>
proof -
  assume h1:\<open>strict_mono f\<close>
  have f0:\<open>\<forall>i\<in>{f n<..<f (Suc n)}. (if i \<in> range f then (s ((inv_into UNIV f) i)) *fps_X^i else 0) = 0\<close>
    by (metis greaterThanLessThan_iff h1 not_less_eq rangeE strict_mono_less)
  then have s:\<open>{..<f (Suc n)} = {..f n} \<union> {f n<..<f (Suc n)}\<close>
    by (metis h1 ivl_disj_un_one(1) strict_mono_Suc_iff)
  show ?thesis 
    apply(subst s)
    apply(subst sum.union_disjoint)
       apply(auto)[3] 
    using f0 apply(simp) 
    by (smt (verit, ccfv_SIG) lessThan_Suc_atMost rangeI sum.lessThan_Suc)
qed

lemma rewriting_sum: assumes \<open>strict_mono (f::nat\<Rightarrow>nat)\<close>
  shows \<open>(\<Sum>i<n. fps_const (s i) * fps_X^(f i))
 = (\<Sum>i\<in>{..<f n}. (if i \<in> range f then fps_const (s (inv_into UNIV f i)) *fps_X^i else 0))\<close>
proof(induct n)
  case 0
  then show ?case 
    by (simp add: assms inter_mt sum.If_cases )
next
  case (Suc n)
  then show ?case   
    apply(subst simp_rule_sum)
    by(auto simp:assms strict_mono_on_imp_inj_on) 
qed



lemma exists_seq:\<open>strict_mono (f::nat\<Rightarrow>nat) \<Longrightarrow> 
\<exists>s. (\<Sum>i\<in>{..<f n}. (if i \<in> range f then fps_const (s' (inv_into UNIV f i)) *fps_X^i else 0))
 = (\<Sum>i\<in>{..<f n}. fps_const (s i) *fps_X^i)\<close>
  apply(rule exI[where x=\<open>\<lambda>i. (if i \<in> range f then (s' ((inv_into UNIV f) i)) else 0) \<close>])
  using rewriting_sum 
  by (smt (verit, best) fps_const_0_eq_0 lambda_zero sum.cong)

lemma exists_seq':\<open>strict_mono (f::nat\<Rightarrow>nat) \<Longrightarrow> 
\<exists>s. (\<Sum>i<n. fps_const (s' i) * (fps_X::'a fps)^(f i)) = 
  (\<Sum>i\<in>{..<f n}. fps_const (s i) *fps_X^i)\<close>
  apply(subst rewriting_sum[])
  using exists_seq[of f \<open>\<lambda>i. (s' i)\<close>] 
  by(auto)  

lemma exists_seq_all:\<open>strict_mono (f::nat\<Rightarrow>nat) \<Longrightarrow> 
\<exists>s. \<forall>n. (\<Sum>i\<in>{..<f n}. (if i \<in> range f then fps_const (s' (inv_into UNIV f i)) *fps_X^i else 0))
 = (\<Sum>i\<in>{..<f n}. fps_const (s i) *fps_X^i)\<close>
  apply(rule exI[where x=\<open>\<lambda>i. (if i \<in> range f then (s' ((inv_into UNIV f) i)) else 0) \<close>])
  using rewriting_sum 
  by (smt (verit, best) fps_const_0_eq_0 lambda_zero sum.cong)



lemma exists_seq_all':\<open>strict_mono (f::nat\<Rightarrow>nat) \<Longrightarrow> 
\<exists>s. \<forall>n. (\<Sum>i<n. fps_const (s' i) * fps_X^(f i)) = 
  (\<Sum>i\<in>{..<f n}. fps_const (s i) *fps_X^i)\<close>
  apply(subst rewriting_sum)
  using exists_seq_all[of f \<open>\<lambda>i. (s' i)\<close>] 
  by(auto)  


lemma tendsto_f_seq:assumes \<open>strict_mono (f::nat\<Rightarrow>nat)\<close>
  shows \<open>(\<lambda>n. (\<Sum>i\<in>{..<f n}. fps_const (s i) *fps_X^i)::'a fps) \<longlonglongrightarrow> Abs_fps (\<lambda>i. s i)\<close>
  using fps_notation LIMSEQ_subseq_LIMSEQ[OF abs_tndsto_le[of s], of f] assms
  by(auto simp:o_def) 


lemma LIMSEQ_add_fps:
  fixes x y :: "'a::idom fps"
  assumes  f:"f \<longlonglongrightarrow> x" and g:"(g \<longlonglongrightarrow> y)"
  shows "((\<lambda>x. f x + g x) \<longlonglongrightarrow> x + y)"
proof -
  from f have \<open>\<forall>e>0. \<exists>n. \<forall>j\<ge>n. dist (f j) x < e/2\<close> 
    using lim_sequentially 
    using half_gt_zero by blast
  from g have f0:\<open>\<forall>e>0. \<exists>n. \<forall>j\<ge>n. dist (g j) y < e/2\<close>
    using lim_sequentially half_gt_zero by blast
  have f4:\<open>dist (f j - x) 0 = dist (f j) x\<close> for j
    unfolding dist_fps_def by(auto)
  have f5:\<open>dist (g j - y) 0 = dist (g j) y\<close> for j
    by (metis diff_0_right dist_fps_def eq_iff_diff_eq_0)
  then have f0':\<open>dist (f j + g j) (x + y) = dist (f j - x + g j - y) 0\<close> for j
    unfolding dist_fps_def 
    by (auto simp add: add.commute add_diff_eq diff_diff_eq2)
  have f1:\<open>dist (f j - x + g j - y) 0 \<le> max (dist (f j - x) 0) (dist (g j - y) 0)\<close> for j
    unfolding dist_fps_def apply(auto simp:le_max_iff_disj field_simps)[1]
    by (metis (no_types, lifting) add_diff_add eq_iff_diff_eq_0 min_le_iff_disj subdegree_add_ge')
  then have f2:\<open>dist (f j - x + g j - y) 0 \<le> dist (f j - x) 0 + dist (g j - y) 0  \<close> for j
    by (smt (verit) zero_le_dist)
  from f0 have f3:\<open>\<forall>e>0. \<exists>n. \<forall>j\<ge>n. dist (f j) x + dist (g j) y < e/2 + e/2\<close>
    by (metis \<open>\<forall>e>0. \<exists>n. \<forall>j\<ge>n. dist (f j) x < e / 2\<close> add_strict_mono le_trans linorder_le_cases)
  then show ?thesis
    unfolding LIMSEQ_def 
    by (metis f0' f2 f4 f5 field_sum_of_halves order_le_less_trans)
qed


lemma LIMSEQ_cmult_fps:
  fixes x y :: "'a::idom fps"
  assumes  f:"f \<longlonglongrightarrow> x"
  shows "((\<lambda>x. c * f x) \<longlonglongrightarrow> c*x)"
proof -
  from f have \<open>\<forall>e>0. \<exists>n. \<forall>j\<ge>n. dist (f j) x < e\<close> 
    using lim_sequentially 
    using half_gt_zero by blast
  have \<open>dist (c*f j - c*x) 0 = dist (c*(f j)) (c*x) \<close> for j
    unfolding dist_fps_def by auto
  have \<open>\<forall>i\<le>n . fps_nth (f j) i = fps_nth x i \<Longrightarrow> 
  (\<Sum>i = 0..n. fps_nth c i * fps_nth (f j) (n - i)) = (\<Sum>i = 0..n. fps_nth c i * fps_nth x (n - i))\<close>
    for j n 
    using diff_le_self by presburger
  have \<open>c\<noteq>0 \<Longrightarrow> dist (f j) x \<ge> dist (c*f j) (c*x)\<close> for j
  proof(cases \<open>x = f j\<close>)
    case True
    then show ?thesis 
      unfolding dist_fps_def subdegree_def 
      by(auto)
  next
    case False
    then have rule_su:\<open>(LEAST n. fps_nth (f j) n \<noteq> fps_nth x n) \<le> 
          (LEAST n. fps_nth (c * f j) n \<noteq> fps_nth (c * x) n) 
          \<Longrightarrow> c\<noteq>0 \<Longrightarrow> dist (c * f j) (c * x) \<le> dist (f j) x\<close>
      unfolding dist_fps_def subdegree_def  by(auto)
    have f0:\<open>n < (LEAST n. fps_nth (f j) n \<noteq> fps_nth x n) \<Longrightarrow> 
  (\<Sum>i = 0..n. fps_nth c i * fps_nth (f j) (n - i)) = (\<Sum>i = 0..n. fps_nth c i * fps_nth x (n - i))\<close>
      for n 
      by (metis (mono_tags, lifting) less_imp_diff_less not_less_Least)
    have f1:\<open>\<forall>n. (\<Sum>i = 0..n. fps_nth c i * fps_nth (f j) (n - i)) 
  = (\<Sum>i = 0..n. fps_nth c i * fps_nth x (n - i)) \<Longrightarrow>
  x \<noteq> f j \<Longrightarrow> c \<noteq> 0 \<Longrightarrow> (LEAST n. fps_nth (f j) n \<noteq> fps_nth x n) \<le> (LEAST n. False)\<close>
      (is \<open>?P \<Longrightarrow> ?R1 \<Longrightarrow> ?R2 \<Longrightarrow> ?R3\<close>)
    proof -
      assume a1: "c \<noteq> 0"
      assume a2: "x \<noteq> f j"
      assume "\<forall>n. (\<Sum>i = 0..n. fps_nth c i * fps_nth (f j) (n - i)) = 
      (\<Sum>i = 0..n. fps_nth c i * fps_nth x (n - i))" (is ?P)
      then show "(LEAST n. fps_nth (f j) n \<noteq> fps_nth x n) \<le> (LEAST n. False)"
        using a2 a1 by (metis (no_types) fps_ext fps_mult_nth mult_cancel_left)
    qed 
    have f2:\<open>x \<noteq> f j \<Longrightarrow> c \<noteq> 0 \<Longrightarrow> (LEAST n. fps_nth (f j) n \<noteq> fps_nth x n)
  \<le> (LEAST n. (\<Sum>i = 0..n. fps_nth c i * fps_nth (f j) (n - i)) \<noteq> 
  (\<Sum>i = 0..n. fps_nth c i * fps_nth x (n - i)))\<close> (is \<open>?R1\<Longrightarrow>?R2\<Longrightarrow>?P1\<close>)
    proof (cases \<open>?P\<close>)
      case True
      assume \<open>x\<noteq>f j\<close> \<open>c\<noteq>0\<close>
      then show ?thesis using True f1 by(auto) 
    next
      case False
      assume a1: "c \<noteq> 0"
      assume a2: "x \<noteq> f j"
      show ?thesis 
      proof(insert False a1 a2, rule ccontr)
        fix n
        assume **:\<open>\<not> ?P\<close>
        assume *:\<open>\<not> ?P1\<close>
          (is \<open>\<not> ?a \<le> ?b\<close>)
        then have \<open>fps_nth (f j) ?b = fps_nth (f j) ?b\<close> 
          by blast
        also have \<open>(\<Sum>i = 0..?b. fps_nth c i * fps_nth (f j) (?b - i)) 
      \<noteq> (\<Sum>i = 0..?b. fps_nth c i * fps_nth x (?b - i))\<close>
          using * 
          by (smt (verit, best) "**" LeastI sum.cong)
        thus False 
          using "*" f0 linorder_not_le by blast
      qed
    qed
    from False show ?thesis 
      unfolding dist_fps_def subdegree_def  
      by (simp add: f2 fps_mult_nth)
  qed   
  then show ?thesis
    unfolding LIMSEQ_def 
    by (metis \<open>\<forall>e>0. \<exists>n. \<forall>j\<ge>n. dist (f j) x < e\<close> dist_self lambda_zero order_le_less_trans)
qed

subsection \<open>The Hilbert Basis theorem\<close>
theorem Hilbert_basis_FPS: (*generalized_hilbert_basis_theorem ?*)
  assumes h2:\<open>noetherian_ring R\<close> 
  shows \<open>noetherian_ring FPS_ring\<close>
proof(rule ring.noetherian_ringI)
  show fst:\<open>ring FPS_ring\<close> 
    by (simp add: ring_FPS)
  fix I
  assume h1:\<open>ideal I FPS_ring\<close>
  show \<open>\<exists>A\<subseteq>carrier FPS_ring. finite A \<and> I = Idl\<^bsub>FPS_ring\<^esub> A\<close>
  proof(cases \<open>I={0} \<or> I = carrier FPS_ring\<close>)
    case True
    then show ?thesis apply(safe)
       apply(rule exI[where x=\<open>{0}\<close>])
       apply(simp add:genideal_def) 
      using h1 ideal.Icarr apply fastforce
      apply(rule exI[where x=\<open>{1}\<close>])
      using ideal.I_l_closed by(fastforce simp:FPS_ring_def genideal_def) 
  next
    case False
    have f0:\<open>subset.chain {I. ideal I R} {(sublead_coeff_set I k)|k. k\<in>UNIV} \<close>
      unfolding subset_chain_def using included_sublead_gen[OF h1] sublead_ideal[OF h1]
      by (smt (verit, ccfv_threshold) mem_Collect_eq nle_le subsetI)
    have f2:\<open>{(sublead_coeff_set I k)|k. k\<in>UNIV} \<noteq> {}\<close> 
      using h1 by(auto)
    have \<open>genideal R S = genideal R (S\<union>{0})\<close> for S
      unfolding genideal_def 
      by (metis R Un_insert_right additive_subgroup.zero_closed 
          ideal.axioms(1) insert_subset ring.simps(1) sup_bot_right)
    have \<open> (\<Union>k. sublead_coeff_set I k) \<in> { sublead_coeff_set I m|m. m\<in>UNIV}\<close>
      by (smt (verit, best) Collect_cong full_SetCompr_eq h1 h2 image_iff mem_Collect_eq sup_sublead)
    then have \<open>\<exists>m.  (\<Union>k. sublead_coeff_set I k) = sublead_coeff_set I m\<close> by auto
    then obtain m where f60:\<open> (\<Union>k. sublead_coeff_set I k) = sublead_coeff_set I m \<and> m>0\<close>
      by (metis Formal_Power_Series_Ring.included_sublead_gen UNIV_I UN_upper 
          bot_nat_0.extremum dual_order.eq_iff h1 less_Suc0 neq0_conv) 
    have \<open>\<forall>k\<ge>m. sublead_coeff_set I m = sublead_coeff_set I k\<close>
      using Formal_Power_Series_Ring.included_sublead_gen f60 h1 by auto
    from f2 have \<open>\<exists>S. \<forall>k. finite (S k) \<and> (sublead_coeff_set I k) = genideal R (S k)\<close>
      using h2 h1 sublead_ideal[OF h1] unfolding noetherian_ring_def noetherian_ring_axioms_def 
      by meson
    then obtain S where f4:\<open>\<forall>k. finite (S k) \<and> (sublead_coeff_set I k) = genideal R (S k)\<close> by blast
    then have 
      \<open>\<exists>S. \<forall>k. finite (S k)\<and> 0\<notin>S k \<and> (sublead_coeff_set I k) = genideal R (S k) \<and> (\<forall>k\<ge>m. S k = S m)\<close>
      apply(intro exI[where x= \<open>(\<lambda>k. if k\<le>m then S k - {0} else S m - {0})\<close>]) 
      by (smt (verit, ccfv_threshold) Diff_iff Un_Diff_cancel Un_commute \<open>\<And>S. Idl S = Idl (S \<union> {0})\<close>
          \<open>\<forall>k\<ge>m. sublead_coeff_set I m = sublead_coeff_set I k\<close> finite_Diff nle_le singletonI)
    then obtain S' where f5:
      \<open>\<forall>k. finite (S' k)\<and> 0 \<notin> S' k \<and> (sublead_coeff_set I k) = genideal R (S' k) \<and> (\<forall>k\<ge>m. S' k = S' m)\<close>
      by blast
    have *:\<open>\<forall>x\<in>(S' j). \<exists>y\<in>I. subdegree y = j \<and> fps_nth y j = x\<close> for j
    proof (safe)
      fix x
      assume h3:\<open>x\<in>S' j\<close>
      then have \<open>x\<in>sublead_coeff_set I j\<close> 
        using f5 unfolding genideal_def by(auto)
      then show \<open>\<exists>y\<in>I. subdegree y = j \<and> fps_nth y j = x\<close>
        unfolding sublead_coeff_set_def subdeg_poly_set using f5
        using h3 by auto
    qed
    define f where \<open>f  = (\<lambda>j x.  (SOME y. y\<in>I \<and> subdegree y = j \<and> fps_nth y j = x))\<close>
    define B where \<open>B = (\<lambda>j. {f j x|x. x\<in>S' j})\<close>
    have \<open>bij_betw (f k) (S' k) (B k)\<close> for k
      apply(rule bij_betwI[where g=\<open>\<lambda>x. fps_nth x k\<close>])
      using B_def apply blast
      using f5 B_def image_def f_def Pi_def apply(safe) 
        apply (smt (verit, del_insts) "*" someI_ex)
       apply (smt (verit, del_insts) "*" f_def someI_ex)
      unfolding f_def B_def image_def
      apply(safe)
      by (smt (verit, ccfv_threshold) "*" Eps_cong someI_ex)
    then have f6:\<open>card (B j) = card (S' j)\<close> for j
      by (metis bij_betw_same_card)
    have f7:\<open>bij_betw (from_nat_into (B k)) ({0..<card (B k)}) (B k)\<close> for k
      by (simp add: B_def atLeast0LessThan bij_betw_from_nat_into_finite f5)
    have f8:\<open>bij_betw (from_nat_into (S' k)) ({0..<card (S' k)}) (S' k)\<close> for k
      by (simp add: B_def atLeast0LessThan bij_betw_from_nat_into_finite f5)
    have \<open>\<forall>x\<in> S' k. \<exists>y\<in>B k. x = fps_nth y k\<close> for k
      using f5  unfolding B_def f_def sublead_coeff_set_def subdeg_poly_set 
      apply(safe)
      by (smt (verit, ccfv_threshold) "*" mem_Collect_eq someI_ex)
    have f30:\<open>\<forall>x\<in> B k. \<exists>y\<in>S' k. y = fps_nth x k\<close> for k
      using f5  unfolding B_def f_def sublead_coeff_set_def subdeg_poly_set 
      apply(safe)
      by (smt (verit, ccfv_threshold) "*" mem_Collect_eq someI_ex)
    have \<open>\<forall>i<card (B k). \<exists>!n. n<card (B k) \<and> fps_nth (from_nat_into (B k) n) k = from_nat_into (S' k) i\<close>
      for k
    proof(safe)
      fix i
      assume \<open>i<card (B k)\<close> 
      then have \<open>from_nat_into (S' k) i \<in> S' k\<close> 
        by (metis card.empty f6 from_nat_into less_nat_zero_code)
      then show \<open>\<exists>n<card (B k). fps_nth (from_nat_into (B k) n) k = from_nat_into (S' k) i\<close>
        by (smt (verit, ccfv_threshold) \<open>\<And>k. \<forall>x\<in>S' k. \<exists>y\<in>B k. x = fps_nth y k\<close> 
            atLeastLessThan_iff bij_betw_iff_bijections f7)
    next
      have f9:\<open>h\<in>B k \<and> g\<in> B k \<Longrightarrow> h \<noteq> g \<longleftrightarrow> fps_nth h k \<noteq> fps_nth g k\<close> for k h g
        using f5  unfolding B_def f_def  sublead_coeff_set_def subdeg_poly_set apply(safe)
        by (smt (verit) "*" someI_ex)+
      fix i n y
      assume \<open>i < card (B k)\<close> \<open>n < card (B k)\<close> 
        \<open>fps_nth (from_nat_into (B k) n) k = from_nat_into (S' k) i\<close> \<open>y < card (B k)\<close>
        \<open>fps_nth (from_nat_into (B k) y) k = from_nat_into (S' k) i\<close>
      then have \<open>(from_nat_into (B k) n) = (from_nat_into (B k) y)\<close> 
        using f9  
        by (metis card.empty from_nat_into less_nat_zero_code)
      then show \<open>n = y\<close> using f7 unfolding bij_betw_def inj_on_def 
        by (metis (no_types, opaque_lifting) \<open>n < card (B k)\<close> \<open>y < card (B k)\<close> 
            atLeastLessThan_iff bij_betw_iff_bijections f7 zero_le)
    qed
    then have \<open>\<exists>p. (\<forall>i<card (S' k). fps_nth (from_nat_into (B k) (p i)) k = from_nat_into (S' k) i)\<close> 
      for k
      apply(intro exI[where x=\<open>\<lambda>i. THE n. n<card (B k) 
            \<and> fps_nth (from_nat_into (B k) (n)) k = from_nat_into (S' k) i\<close>])
      apply(safe) 
      by (smt (z3) f6 theI')
    then obtain p 
      where f11:\<open>(\<forall>i<card (S' k). fps_nth (from_nat_into (B k) (p k i)) k = from_nat_into (S' k) i)\<close> 
      for k
      by metis
    have \<open>x\<noteq>y \<Longrightarrow> x\<in>S' j \<and> y\<in>S' j\<Longrightarrow> (SOME y. y\<in>I \<and> subdegree y = j \<and> fps_nth y j = x) 
  \<noteq> (SOME y'. y'\<in>I \<and> subdegree y' = j \<and> fps_nth y' j = y)\<close> for x y j
      using * 
      apply(safe) 
      by (smt (verit, best) someI_ex)
    then have \<open>\<forall>x y. x\<in>S' j \<and> y\<in>S' j \<and> x\<noteq>y \<longrightarrow> f j x \<noteq> f j y\<close> for j
      unfolding f_def by(auto)
    have f10:\<open>finite (B j)\<close> for j
      using f6 f5 B_def 
      using \<open>\<And>k. bij_betw (f k) (S' k) (B k)\<close> bij_betw_finite by blast
    from idl_sum 
    have \<open>\<forall>x\<in>sublead_coeff_set I m. (\<exists>s. x  = (\<Sum>i\<in>{0..<card (S m)}. s i * from_nat_into (S m) i))\<close>
      using f4 genideal_sum_rep by blast
    have \<open>genideal R {} = {0}\<close> 
      unfolding genideal_def 
    proof(safe) 
      fix x
      assume 1:\<open> x \<in> \<Inter> {I. ideal I R \<and> {} \<subseteq> I} \<close> \<open>x \<notin> {}\<close>
      have \<open>ideal ({0}) R\<close> 
        using R ring.zeroideal ring_R by fastforce
      then have \<open>x\<in>{0}\<close> using 1 by auto
      then show \<open>x=0\<close> by auto
    next
      fix X
      assume 2:\<open>ideal X R\<close> \<open>{}\<subseteq>X\<close>
      then show \<open>0\<in>X\<close> 
        using R additive_subgroup.zero_closed ideal.axioms(1) by fastforce
    qed
    have \<open>sublead_coeff_set I m \<noteq> {0} \<Longrightarrow> S m \<noteq> {}\<close>
      using \<open>Idl {} = {0}\<close> f4 by force
    define I' where \<open>I' \<equiv> genideal FPS_ring (\<Union>k\<le>m. B k)\<close>
    have f62:\<open>(\<Union>k\<le>m. B k) \<subseteq> I \<and> finite (\<Union>k\<le>m. B k)\<close> 
      apply(rule conjI) 
      using B_def f_def f10 apply(auto simp:image_def * some_eq_ex)[1]
       apply (smt (verit, del_insts) "*" some_eq_ex)
      using f10 apply(induct m) by(auto) 
    then have \<open>I' \<subseteq> I\<close>
      unfolding I'_def 
      by (meson Formal_Power_Series_Ring.ring_FPS h1 ring.genideal_minimal)
    have \<open>\<forall>k\<ge>m. S' m = S' k\<close> 
      using f5 by blast
    have eq_fps_S':\<open>{fps_nth f k|f. f\<in>B k} = S' k\<close> for k
      unfolding B_def f_def apply(safe)
      using B_def f30 f_def apply blast
      using B_def \<open>\<And>k. \<forall>x\<in>S' k. \<exists>y\<in>B k. x = fps_nth y k\<close> f_def by blast
    {
      fix f m'
      assume h9:\<open>f \<noteq> 0\<close> \<open>f\<in>I\<close> \<open>subdegree f \<le> m\<close> \<open>f\<notin>I'\<close> \<open>subdegree f = m'\<close>
      with h9 have \<open>fps_nth f m' \<in> sublead_coeff_set I m'\<close>
        unfolding sublead_coeff_set_def subdeg_poly_set
        by blast
      then have \<open>\<exists>s. fps_nth f m' = (\<Sum>k=0..<card (S' m'). (s k)*from_nat_into (S' m') k)\<close>
        using f5
        using genideal_sum_rep by blast
      then obtain s where f12:\<open>fps_nth f m' = (\<Sum>k=0..<card (S' m'). (s k)*from_nat_into (S' m') k)\<close>
        by blast
      then have f21:\<open>(\<Sum>k=0..<card (S' m'). (s k)*from_nat_into (S' m') k)
  = fps_nth (\<Sum>k=0..<card (B m'). (fps_const (s k))*from_nat_into (B m') (p m' k)) m'\<close>
        using f11 
        apply(subst fps_sum_nth)
        apply(subst fps_mult_left_const_nth)
        using f6 by fastforce
      then have f14:
        \<open>fps_nth f m' = fps_nth (\<Sum>k=0..<card (B m'). (fps_const (s k))*from_nat_into (B m') (p m' k)) m'\<close> 
        using f11 f12 by auto
      then have 
        \<open>fps_nth ((f - (\<Sum>k=0..<card (B m'). (fps_const (s k))*from_nat_into (B m') (p m' k)))) m' = 0\<close>
        by auto
      have f22:\<open>(from_nat_into (B m') (p m' ka)) \<in> B m'\<close> for ka
        by (metis atLeastLessThan0 card.empty f12 f6 from_nat_into h9(1) 
            h9(5) nth_subdegree_zero_iff sum.empty)
      then have f13:\<open>\<forall>k<m'.  fps_nth (from_nat_into (B m') (p m' ka)) k = 0\<close> for ka
        unfolding B_def f_def using f5 unfolding sublead_coeff_set_def subdeg_poly_set 
        by (smt (verit, best) "*" h9 mem_Collect_eq nth_less_subdegree_zero someI_ex)
      then have 
        \<open>\<forall>ka<m'. fps_nth (\<Sum>k=0..<card (B m'). (fps_const (s k))*from_nat_into (B m') (p m' k)) ka = 0\<close>
        apply(subst fps_sum_nth)
        apply(subst fps_mult_left_const_nth) apply(safe)
        apply(subst f13) by(auto)
      then have f18:\<open>ka\<le>m' \<Longrightarrow>  (fps_nth (f-(\<Sum>k=0..<card (B m').
  (fps_const (s k))*from_nat_into (B m') (p m' k))) ka = 0)\<close> for ka
        apply(cases \<open>ka=m'\<close>) 
        using f14 apply fastforce
        using nth_less_subdegree_zero 
        using h9(5) by force
      have \<open>from_nat_into (B m') (p m' k) \<in> I'\<close> for k
        using f22 unfolding I'_def genideal_def 
        using h9(3) h9(5) by blast
      then have f23:\<open>(fps_const (s k))*from_nat_into (B m') (p m' k) \<in> I'\<close> for k
        by (metis FPS_ring_def I'_def UNIV_I ideal.I_l_closed monoid.select_convs(1) 
            partial_object.select_convs(1) ring.genideal_ideal ring_FPS subset_UNIV)
      have f24:\<open>(\<Sum>k=0..<r. (fps_const (s k))*from_nat_into (B m') (p m' k)) \<in> I'\<close> for r using f22 
        apply(induct r)  
         apply (metis (full_types) Formal_Power_Series_Ring.FPS_ring_def I'_def 
            additive_subgroup.zero_closed atLeastLessThan0 ideal_def partial_object.select_convs(1) 
            ring.genideal_ideal ring.simps(1) ring_FPS sum.empty top_greatest)
        apply(subst sum.atLeast0_lessThan_Suc)
        unfolding I'_def 
        by (metis (no_types, lifting) Formal_Power_Series_Ring.FPS_ring_def I'_def 
            additive_subgroup.a_closed f23 ideal.axioms(1) partial_object.select_convs(1) 
            ring.genideal_ideal ring_FPS ring_record_simps(12) subset_UNIV)  
      then have f26:
        \<open>(f - (\<Sum>k=0..<card (B m'). (fps_const (s k))*from_nat_into (B m') (p m' k))) = 0 \<Longrightarrow> False\<close>
        using h9 by auto
      have \<open>subdegree (f - (\<Sum>k=0..<card (B m'). (fps_const (s k))*from_nat_into (B m') (p m' k))) > m'\<close>
        using f26
        by (smt (verit, ccfv_SIG)f18 enat_ord_code(4) enat_ord_simps(1) 
            linorder_not_less nth_subdegree_zero_iff)
      then have \<open>\<exists>g\<in>I'. subdegree (f + g) > m'\<and> (f + g) \<noteq> 0\<close>
        using f26 
        apply(intro bexI[where x=\<open>- (\<Sum>k=0..<card (B m'). (fps_const (s k))*
                        from_nat_into (B m') (p m' k))\<close>])
        using f26 f24 apply(safe)
          apply(auto)[2]
        by (metis (no_types, lifting) Formal_Power_Series_Ring.FPS_ring_def
            Formal_Power_Series_Ring.ring_FPS I'_def UNIV_I ideal.I_l_closed monoid.select_convs(1)
            mult_1s(3) partial_object.select_convs(1) ring.genideal_ideal subset_UNIV)
    } note first = this
    {
      fix f 
      assume h10:\<open>f\<noteq>0\<close> \<open>f\<in>I\<close> \<open>f\<notin>I'\<close> \<open>subdegree f < m\<close> 
      have \<open>\<exists>g\<in>I'. subdegree (f + g) > subdegree f \<and> f+g \<noteq>0 \<close>
        using first[OF h10(1) h10(2) _ h10(3)] 
        using h10(4) nat_less_le 
        by blast
      have \<open>\<exists>g\<in>I'. subdegree (f + g) \<ge> m' \<and> f+g \<noteq>0\<close> if hh:\<open>m'\<le>m\<close> for m'
        using hh h10 proof(induct m' arbitrary:f)
        case 0
        then show ?case 
          using first less_or_eq_imp_le by blast
      next
        case (Suc m')
        then obtain g where g1:\<open>g\<in>I' \<and> subdegree (f + g) \<ge> m' \<and> f+g \<noteq>0\<close> 
          using first order_less_imp_le 
          by (metis less_Suc_eq_le nle_le)
        {assume hh1:"subdegree (f+g) < Suc m'"
          with g1 have g2:\<open>subdegree (f+g) = m'\<close> 
            by auto 
          have g3:\<open>f+g \<in> I\<close> 
            by (metis Formal_Power_Series_Ring.FPS_ring_def Suc.prems(3) 
                \<open>I' \<subseteq> I\<close> additive_subgroup.a_closed g1 h1 ideal.axioms(1) 
                in_mono ring_record_simps(12))
          have g4:\<open>f+g \<notin> I'\<close> 
          proof(rule ccontr)
            assume \<open>\<not>f+g \<notin> I'\<close>
            have \<open>-g \<in> I'\<close>
              using g1 unfolding I'_def 
              by (metis (no_types, lifting) FPS_ring_def Formal_Power_Series_Ring.genideal_sum_rep
                  Formal_Power_Series_Ring.idl_sum UNIV_I f62 ideal.I_l_closed monoid.select_convs(1)
                  mult_1s(3) partial_object.select_convs(1))
            then have \<open>f+g-g \<in> I'\<close>
              by (metis (no_types, lifting) Formal_Power_Series_Ring.FPS_ring_def 
                  Formal_Power_Series_Ring.genideal_sum_rep Formal_Power_Series_Ring.idl_sum I'_def 
                  Suc.prems(4) f62 \<open>\<not>f+g \<notin> I'\<close> add.commute  additive_subgroup.a_closed ideal.axioms(1)
                  minus_add_cancel ring_record_simps(12))
            then have \<open>f\<in>I'\<close> by auto
            then show False 
              using Suc.prems(4) by auto
          qed
          have g5: \<open>subdegree (f+g)\<le>m\<close> 
            by (simp add: Suc.prems(1) Suc_leD g2)
          then obtain g' where \<open>g'\<in>I' \<and> subdegree (f + g +g') > subdegree (f+g) \<and> f+g+g' \<noteq>0\<close>
            using first[OF _ g3 g5 g4, of m'] 
            using g1 g2 by blast  
          then have \<open>subdegree (f+g+g') \<ge> Suc m'\<close> 
            using Suc_le_eq g2 by blast
          then have \<open>\<exists>g'\<in>I'. subdegree (f + g +g') \<ge> Suc m' \<and> f+g+g' \<noteq>0\<close> 
            using \<open>g' \<in> I' \<and> subdegree (f + g) < subdegree (f + g + g') \<and> f + g + g' \<noteq> 0\<close> by blast
        }note proof1=this
        then obtain g' where ttt:\<open>subdegree (f+g) <Suc m' \<Longrightarrow> g' \<in> I' \<and> 
  subdegree (f + g) < subdegree (f + g + g') \<and> f + g + g' \<noteq> 0\<close>
          using order_less_le_trans by blast
        show ?case apply(cases \<open>subdegree (f+g) \<ge>Suc m'\<close>)
          using g1 apply blast
          using proof1 
          apply(intro bexI[where x=\<open>g +g'\<close>]) 
           apply (metis Suc_leI ab_semigroup_add_class.add_ac(1) 
              g1 le_less_Suc_eq linorder_not_less ttt)
          unfolding I'_def 
          by (metis (no_types, lifting) FPS_ring_def Formal_Power_Series_Ring.genideal_sum_rep 
              Formal_Power_Series_Ring.idl_sum I'_def \<open>\<Union> (B ` {..m}) \<subseteq> I \<and> finite (\<Union> (B ` {..m}))\<close> 
              additive_subgroup.a_closed g1 ideal.axioms(1) linorder_not_less ring_record_simps(12) ttt)  
      qed            
    } note snd=this  
    { 
      fix f m'
      assume h9:\<open>f \<noteq> 0\<close> \<open>f\<in>I\<close> \<open>subdegree f \<ge> m\<close> \<open>subdegree f = m'\<close> \<open>f\<notin>I'\<close>
      then  have \<open>fps_nth f m' \<in> sublead_coeff_set I m'\<close>
        unfolding sublead_coeff_set_def subdeg_poly_set by auto
      then have f28:\<open>fps_nth f m' \<in> sublead_coeff_set I m\<close> 
        \<open>sublead_coeff_set I m' = genideal R (S' m)\<close>
        using \<open>\<forall>k\<ge>m. sublead_coeff_set I m = sublead_coeff_set I k\<close>
          h9 less_or_eq_imp_le apply blast
        using f5  by (metis h9(3-4))
      then have \<open>\<exists>s. fps_nth f m' = (\<Sum>k=0..<card (S' m). (s k)*from_nat_into (S' m) k)\<close> 
        using genideal_sum_rep f5 by blast
      then obtain s where f12:\<open>fps_nth f m' = (\<Sum>k=0..<card (S' m). (s k)*from_nat_into (S' m) k)\<close>
        by blast
      then have f21:\<open>(\<Sum>k=0..<card (S' m). (s k)*from_nat_into (S' m) k)
  =fps_nth (\<Sum>k=0..<card (B m). (fps_const (s k))*from_nat_into (B m) (p m k)) m\<close>
        using f11 
        apply(subst fps_sum_nth)
        apply(subst fps_mult_left_const_nth)
        using f6 by fastforce
      then have f14:
        \<open>fps_nth f m' = fps_nth (\<Sum>k=0..<card (B m). (fps_const (s k))*from_nat_into (B m) (p m k)) m\<close>
        using f11 f12 by auto
      have f22:\<open>(from_nat_into (B m) (p m ka)) \<in> B m\<close> for ka 
        by (metis atLeastLessThan0 card.empty f12 f6 from_nat_into h9(1) h9(4)
            nth_subdegree_zero_iff sum.empty)
      then have \<open>subdegree (from_nat_into (B m) (p m k)) = m\<close> for k
        unfolding B_def f_def sublead_coeff_set_def subdeg_poly_set  
        by (smt (verit, best) "*" h9 mem_Collect_eq nth_less_subdegree_zero someI_ex) 
      then have f32:\<open>subdegree ((fps_X^(m'-m))*from_nat_into (B m) (p m k)) = m'\<close> for k
        using fps_subdegree_mult_fps_X_power(1) 
        by (metis f30 f22 f5 h9(3) h9(4) le_add_diff_inverse nth_subdegree_zero_iff)
      have f31:
        \<open>fps_nth ((fps_X^(m'-m))*from_nat_into (B m) (p m k)) m' = fps_nth (from_nat_into (B m) (p m k)) m\<close> 
        for k
        by (metis diff_diff_cancel diff_le_self fps_X_power_mult_nth h9(3) h9(4) linorder_not_less)
      then have f31b:\<open>fps_nth (fps_const (s k)*(fps_X^(m'-m))*from_nat_into (B m) (p m k)) m' = 
  fps_nth (fps_const (s k)*from_nat_into (B m) (p m k)) m\<close> for k
        by (simp add: mult.assoc)
      then have f33:\<open>fps_nth f m' = fps_nth (\<Sum>k=0..<card (B m). (fps_const (s k))*(fps_X^(m'-m))*
from_nat_into (B m) (p m k)) m'\<close>
        apply(subst fps_sum_nth)
        apply(subst f31b)
        apply(subst fps_mult_left_const_nth)
        by (simp add: f14 fps_sum_nth)
      then have f36:\<open>fps_nth ((f - (\<Sum>k=0..<card (B m). (fps_const (s k))*(fps_X^(m'-m))*
        from_nat_into (B m) (p m k)))) m' = 0\<close>
        by auto
      have \<open>from_nat_into (B m) (p m k) \<in> I'\<close> for k
        using f22 unfolding I'_def genideal_def 
        using h9 by blast
      then have f23:\<open>(fps_const (s k))*from_nat_into (B m) (p m k) \<in> I'\<close> for k
        by (metis FPS_ring_def I'_def UNIV_I ideal.I_l_closed monoid.select_convs(1) 
            partial_object.select_convs(1) ring.genideal_ideal ring_FPS subset_UNIV)
      then have f23:\<open>(fps_const (s k))*fps_X^(m'-m)*from_nat_into (B m) (p m k) \<in> I'\<close> for k
        by (metis (no_types, lifting) FPS_ring_def Formal_Power_Series_Ring.genideal_sum_rep 
            Formal_Power_Series_Ring.idl_sum I'_def UNIV_I \<open>\<And>k. from_nat_into (B m) (p m k) \<in> I'\<close>
            f62 ideal.I_l_closed monoid.select_convs(1) partial_object.select_convs(1))
      have f24:\<open>(\<Sum>k=0..<r. (fps_const (s k))*fps_X^(m'-m)*from_nat_into (B m) (p m k)) \<in> I'\<close> 
        for r 
        using f22 
        apply(induct r)  
         apply(simp)
         apply (metis (full_types) Formal_Power_Series_Ring.FPS_ring_def I'_def additive_subgroup.zero_closed 
            ideal_def partial_object.select_convs(1) ring.genideal_ideal ring.simps(1) ring_FPS top_greatest)
        apply(subst sum.atLeast0_lessThan_Suc)
        unfolding I'_def 
        by (metis (no_types, lifting) Formal_Power_Series_Ring.FPS_ring_def I'_def 
            additive_subgroup.a_closed f23 ideal.axioms(1) partial_object.select_convs(1) 
            ring.genideal_ideal ring_FPS ring_record_simps(12) subset_UNIV)  
      then have f26:
        \<open>(f - (\<Sum>k=0..<card (B m). (fps_const (s k))*fps_X^(m'-m)*from_nat_into (B m) (p m k))) = 0 \<Longrightarrow> False\<close>
        (is \<open>f - ?A = 0\<Longrightarrow>False\<close>) using h9 by auto
      have \<open>\<forall>i<m'. fps_nth ((fps_const (s k))*(fps_X^(m'-m))*from_nat_into (B m) (p m k)) i = 0\<close> 
        for k
        using f32 
        by (metis ab_semigroup_mult_class.mult_ac(1) fps_mult_nth_outside_subdegrees(2))
      then have f34:\<open>\<forall>i<m'. fps_nth (?A) i = 0\<close>
        apply(subst fps_sum_nth)
        by(auto)
      then have f35:\<open>subdegree ?A = m'\<close>
        by (metis (no_types, lifting) f33 h9(1) h9(4) nth_subdegree_nonzero subdegreeI)
      have \<open>x\<in>I' \<Longrightarrow> -x\<in>I'\<close> for x
        unfolding I'_def FPS_ring_def 
        by (metis (no_types, lifting) Formal_Power_Series_Ring.genideal_sum_rep 
            Formal_Power_Series_Ring.idl_sum UNIV_I f62
            ideal.I_l_closed monoid.select_convs(1) mult_1s(3) partial_object.select_convs(1)) 
      have f39:\<open>subdegree (- ?A) \<ge> m\<close>
        using subdegree_uminus[of ?A] f35 h9 by argo
      have \<open>subdegree (f - (\<Sum>k=0..<card (B m). 
(fps_const (s k))*(fps_X^(m'-m))*from_nat_into (B m) (p m k))) > m'\<close>
        using h9 f33 
        by (metis (no_types, lifting) f36 f35 diff_zero f26 fps_sub_nth le_neq_implies_less 
            nth_subdegree_nonzero subdegree_leI)
      then have \<open>\<exists>g. \<exists>s. g=- (\<Sum>k=0..<card (B m). (fps_const (s k))*(fps_X^(m'-m))*
from_nat_into (B m) (p m k)) \<and> subdegree (f + g) > m' \<and> (f +g) \<noteq> 0 \<and> g \<in> I' \<and> subdegree (g) \<ge> m\<close> 
        using f26  f24  \<open>\<And>x. x \<in> I' \<Longrightarrow> - x \<in> I'\<close> f39 
        by (metis (no_types, lifting) add_uminus_conv_diff)
    }note thrd=this
    have in_I':\<open>x\<in>I' \<Longrightarrow> -x\<in>I'\<close> for x
      unfolding I'_def FPS_ring_def 
      by (metis (no_types, lifting) Formal_Power_Series_Ring.genideal_sum_rep 
          Formal_Power_Series_Ring.idl_sum UNIV_I \<open>\<Union> (B ` {..m}) \<subseteq> I \<and> finite (\<Union> (B ` {..m}))\<close> 
          ideal.I_l_closed monoid.select_convs(1) mult_1s(3) partial_object.select_convs(1)) 
    have \<open>I\<subseteq>I'\<close>
    proof(safe, rule ccontr)
      fix f
      assume h10:\<open>f\<in>I\<close> \<open>f\<notin>I'\<close>
      then have f40:\<open>f\<noteq>0\<close> 
        by (metis FPS_ring_def I'_def additive_subgroup.zero_closed ideal.axioms(1) 
            partial_object.select_convs(1) ring.genideal_ideal ring.simps(1) ring_FPS subset_UNIV)
      have \<open> \<exists>g\<in>I'. subdegree (f + g) \<ge> m \<and> f+g\<noteq>0\<close> 
        using snd[OF f40 h10 ] 
        by (metis Formal_Power_Series_Ring.FPS_ring_def Formal_Power_Series_Ring.ring_FPS I'_def 
            add.right_neutral additive_subgroup.zero_closed f40 ideal.axioms(1) linorder_not_less 
            order_refl partial_object.select_convs(1) ring.genideal_ideal ring.simps(1) subset_UNIV)
      then obtain g where f41:\<open>g\<in>I' \<and> subdegree (f + g) \<ge> m \<and> f+g\<noteq>0\<close> by blast   
      then have hyps:\<open>f+g\<noteq>0\<close> \<open>f+g \<in> I\<close> \<open>subdegree(f+g)\<ge>m\<close> \<open>(f+g)\<notin>I'\<close>
      proof -
        show \<open>f + g \<noteq> 0\<close> \<open>m \<le> subdegree (f + g)\<close> using f41 by auto
        have \<open>g\<in>I\<close> 
          using \<open>I' \<subseteq> I\<close> f41 by blast
        then show \<open>f + g \<in> I\<close> 
          by (metis FPS_ring_def additive_subgroup.a_closed h1 h10(1) ideal_def ring_record_simps(12))
        show \<open>f + g \<notin> I'\<close>
        proof(rule ccontr)
          assume \<open>\<not>f+g \<notin> I'\<close>
          have \<open>-g \<in> I'\<close>
            unfolding I'_def FPS_ring_def 
            by (metis Formal_Power_Series_Ring.FPS_ring_def Formal_Power_Series_Ring.ring_R I'_def
                f41 ideal.I_l_closed iso_tuple_UNIV_I monoid.select_convs(1) mult_minus1 
                partial_object.select_convs(1) ring.genideal_ideal subset_UNIV)
          then have \<open>f+g-g \<in> I'\<close>
            by (metis (no_types, lifting) Formal_Power_Series_Ring.FPS_ring_def 
                Formal_Power_Series_Ring.genideal_sum_rep Formal_Power_Series_Ring.idl_sum I'_def 
                f62 \<open>\<not> f + g \<notin> I'\<close> add_stable_FPS_ring uminus_add_conv_diff)
          then have \<open>f\<in>I'\<close> by auto
          then show False 
            using h10(2) by blast
        qed
      qed
      define the_s where \<open>the_s \<equiv> rec_nat (f+g) 
(\<lambda>n sn. sn + (SOME g. \<exists>s. g = -(\<Sum>k=0..<card (B m). (fps_const (s k))*(fps_X^(subdegree sn - m))
*from_nat_into (B m) (p m k))
  \<and> subdegree (sn + g) > subdegree sn \<and> (sn +g) \<noteq> 0 \<and> g\<in>I' \<and> subdegree g \<ge>m))\<close>
      have subst_rec:\<open> the_s (Suc n) = the_s n + (SOME g. \<exists>s. g = - (\<Sum>k=0..<card (B m). 
(fps_const (s k))*(fps_X^(subdegree (the_s (n)) - m))*from_nat_into (B m) (p m k))
\<and> subdegree ((the_s (n)) + g) > subdegree (the_s (n)) \<and> ((the_s (n)) + g) \<noteq> 0 
\<and> g\<in>I'\<and>subdegree g \<ge>m)\<close> for n
        unfolding the_s_def 
        apply(induct n) 
        by (meson old.nat.simps(7))+
      have hyps_thes:\<open>the_s n \<noteq> 0\<and>the_s n \<in> I\<and>subdegree(the_s n)\<ge>m\<and>(the_s n)\<notin>I'\<close> for n
      proof(induct n)
        case 0
        then show ?case unfolding the_s_def using hyps by auto
      next
        case (Suc n)
        then have y1:\<open>the_s n \<noteq> 0\<close> and y2: \<open>the_s n \<in> I\<close> and y3:\<open>m \<le> subdegree (the_s n)\<close> 
          and y4:\<open>the_s n \<notin> I'\<close>
          by auto
        have f50:\<open> \<exists>g. \<exists>s. g =  - (\<Sum>k = 0..<card (B m). fps_const (s k) * fps_X ^ 
  (subdegree (the_s n) - m) * from_nat_into (B m) (p m k)) \<and> subdegree (the_s n) < 
  subdegree (the_s n + g) \<and> the_s n + g \<noteq> 0 \<and> g\<in>I'\<and>subdegree g \<ge>m\<close>
          using thrd[OF y1 y2 y3 _ y4, of \<open>subdegree (the_s n)\<close>] by auto
        let ?g = \<open>(SOME g.  \<exists>s. g = - (\<Sum>k = 0..<card (B m). fps_const (s k) * fps_X ^ 
  (subdegree (the_s n) - m) * from_nat_into (B m) (p m k)) \<and> subdegree (the_s n) < 
  subdegree (the_s n + g) \<and>the_s n + g  \<noteq> 0 \<and> g\<in>I'\<and>subdegree g \<ge>m)\<close>
        have \<open>the_s (Suc n) \<notin> I'\<close>
        proof(subst subst_rec, rule ccontr)
          assume h100: \<open>\<not>the_s n+?g \<notin> I'\<close>
          have \<open>?g\<in>I'\<close>
            by(smt someI_ex f50)
          then have \<open>-?g \<in> I'\<close>
            using in_I' by auto
          then have \<open>the_s n+?g-?g \<in> I'\<close>
            by (metis (no_types, lifting) Formal_Power_Series_Ring.FPS_ring_def 
                Formal_Power_Series_Ring.genideal_sum_rep Formal_Power_Series_Ring.idl_sum I'_def 
                f62 h100 add_stable_FPS_ring add_uminus_conv_diff)
          then have \<open>the_s n\<in>I'\<close> by auto
          then show False 
            using y4 by blast
        qed
        have \<open>the_s (Suc n) \<in> I\<close> 
        proof(subst subst_rec) 
          have \<open>?g\<in>I'\<close>
            by(smt someI_ex f50)
          then show \<open>the_s n + ?g \<in> I\<close> 
            using \<open>I' \<subseteq> I\<close> add_stable_FPS_ring h1 y2 by blast
        qed
        have f51:\<open>the_s (Suc n) \<noteq> 0\<close>
          apply(subst subst_rec)
          by (smt someI_ex f50)
        have \<open>m \<le> subdegree (the_s (Suc n))\<close>
        proof(subst subst_rec)
          have \<open>subdegree ?g \<ge>m\<close> 
            by (smt someI_ex f50)
          then show \<open>m\<le>subdegree (the_s n + ?g)\<close>
            using f51 apply(subst (asm) subst_rec)
            by (smt (verit) add_diff_cancel_left' dual_order.trans f50 linorder_le_less_linear
                subdegree_diff_eq1 subdegree_diff_eq2 y1)
        qed
        then show ?case 
          using \<open>the_s (Suc n) \<in> I\<close> \<open>the_s (Suc n) \<notin> I'\<close> f51 by blast
      qed   
      have f53:\<open>\<forall>n. \<exists>g. \<exists>s. g = - (\<Sum>k=0..<card (B m). (fps_const (s k))*
(fps_X^(subdegree (the_s (n)) - m))*from_nat_into (B m) (p m k)) 
\<and> subdegree ((the_s (n)) + g) > subdegree (the_s (n))
\<and> ((the_s (n)) + g) \<noteq> 0 \<and> g\<in>I'\<and>subdegree g \<ge>m\<close> 
        using thrd hyps_thes by blast
      then have  f53':\<open>\<forall> n. \<exists>g. \<exists>s. the_s (Suc n) = the_s n + g \<and> g = - (\<Sum>k=0..<card (B m). 
(fps_const (s k))*(fps_X^(subdegree (the_s (n)) - m))*from_nat_into (B m) (p m k)) \<and>
subdegree ((the_s (n)) + g) > subdegree (the_s (n)) \<and> ((the_s (n)) + g) \<noteq> 0 \<and> g\<in>I'\<and>subdegree g \<ge>m\<close> 
        apply(subst subst_rec) 
        by (smt (z3) tfl_some)
      from f53 have \<open>subdegree (the_s n) < subdegree (the_s (Suc n))\<close> for n
        apply(subst subst_rec) 
        by (smt someI_ex f53 sum.cong)
      then have f56:\<open>strict_mono (\<lambda>n. subdegree (the_s n))\<close>
        using strict_mono_Suc_iff by blast
      have f70:\<open>strict_mono (\<lambda>k. subdegree(the_s k) - m)\<close>
        using f56 unfolding strict_mono_def 
        using diff_less_mono hyps_thes by presburger
      let ?f =\<open>\<lambda>k. subdegree (the_s k) - m\<close>
      have \<open>bij_betw ?f UNIV (range ?f)\<close>
        by (simp add: \<open>strict_mono ?f\<close> bij_betw_imageI strict_mono_on_imp_inj_on)
      from f56 have f80:\<open>the_s \<longlonglongrightarrow> 0\<close>
        using subdeg_inf_imp_s_tendsto_zero by blast
      have f54:\<open>\<exists>g' s'. \<forall>n. g' n = -(\<Sum>k=0..<card (B m). (fps_const (s' n k))*
(fps_X^(subdegree (the_s n) - m))*from_nat_into (B m) (p m k))
\<and> subdegree ((the_s n) + (g' n)) > subdegree (the_s n) \<and> ((the_s n) +g' n) \<noteq> 0 \<and> g' n\<in>I' 
\<and> subdegree (g' n) \<ge>m\<close> 
        using f53 by meson
      have \<open>\<exists>g' s'. \<forall>n. the_s (Suc n) = the_s n + g' n \<and> g' n =  -(\<Sum>k=0..<card (B m). 
(fps_const (s' n k))*(fps_X^(subdegree (the_s n) - m))*from_nat_into (B m) (p m k))
\<and> subdegree ((the_s n) + (g' n)) > subdegree (the_s n) \<and> ((the_s n) +g' n) \<noteq> 0 \<and> g' n\<in>I' 
\<and> subdegree (g' n) \<ge>m\<close> 
        using f53' by meson
      then obtain g' s' where f55:\<open>\<forall>n. the_s (Suc n) = the_s n + g' n \<and> g' n = -(\<Sum>k=0..<card (B m).
(fps_const (s' n k))*(fps_X^(subdegree (the_s n) - m))*from_nat_into (B m) (p m k)) 
\<and> subdegree ((the_s n) + (g' n)) > subdegree (the_s n) \<and> ((the_s n) +g' n) \<noteq> 0 \<and> g' n\<in>I' 
\<and> subdegree (g' n) \<ge>m\<close>
        by blast
      then have \<open>\<forall>n. \<exists>s. \<forall>k. s' n k = s (subdegree (the_s n) - m) k\<close> 
        by force
      have \<open>the_s n = f+g + (\<Sum>k<n. (the_s (Suc k) - the_s k))\<close> for n
        apply(induct n)
         apply(subst subst_rec[rule_format])
         apply (simp add: the_s_def)
        by simp
      then have t1:\<open>f+g = the_s n - (\<Sum>k<n. (the_s (Suc k) - the_s k))\<close> for n
        by (metis (no_types, lifting) add_diff_cancel_right')
      then have \<open>f+g = the_s n - (\<Sum>k<n. g' k)\<close> for n
        by (simp add: f55)
      then have \<open>f+g = the_s n - (\<Sum>k<n. -(\<Sum>i=0..<card (B m). (fps_const (s' k i))*
(fps_X^(subdegree (the_s k) - m))*from_nat_into (B m) (p m i)))\<close>for n
        by(simp add:f55)
      then have f87:\<open>f+g = the_s n + (\<Sum>k<n. (\<Sum>i=0..<card (B m). (fps_const (s' k i))*
(fps_X^(subdegree (the_s k) - m))*from_nat_into (B m) (p m i)))\<close>
        for n
        by (simp add: sum_negf)
      then have \<open>f+g = the_s n + ((\<Sum>i=0..<card (B m). \<Sum>k<n. (fps_const (s' k i))*
(fps_X^(subdegree (the_s k) - m))*from_nat_into (B m) (p m i)))\<close> for n
      proof -
        assume "\<And>n. f + g = the_s n + (\<Sum>k<n. \<Sum>i = 0..<card (B m). fps_const 
  (s' k i) * fps_X ^ (subdegree (the_s k) - m) * from_nat_into (B m) (p m i))"
        then have "f + g = the_s n + (\<Sum>n = 0..<n. \<Sum>na = 0..<card (B m). 
  fps_const (s' n na) * fps_X ^ (subdegree (the_s n) - m) * from_nat_into (B m) (p m na))"
          using atLeast0LessThan by moura
        then show ?thesis
          using atLeast0LessThan sum.swap by force
      qed
      then have f57:\<open>f+g = the_s n + ((\<Sum>i=0..<card (B m). (\<Sum>k<n. (fps_const (s' k i))*
                    (fps_X^(subdegree (the_s k) - m)))*from_nat_into (B m) (p m i)))\<close>
        for n
        by(auto simp:sum_distrib_right)
      have \<open>(\<lambda>n. (f+g)) - the_s = (\<lambda>n. (f+g) + (-the_s n))\<close> 
        by(auto simp:fun_eq_iff)
      have \<open>- the_s \<longlonglongrightarrow> 0\<close> 
        apply(rule metric_LIMSEQ_I)
        using f80
        apply(drule metric_LIMSEQ_D) 
        unfolding dist_fps_def 
        by fastforce
      then have f58:\<open>(\<lambda>n. (f+g)) - the_s \<longlonglongrightarrow> f + g\<close>
      proof -
        have "\<forall>n. f + g + (- the_s) n = ((\<lambda>n. f + g) - the_s) n"
          by auto
        then show ?thesis
          by (metis (no_types) \<open>- the_s \<longlonglongrightarrow> 0\<close> LIMSEQ_add_fps[of \<open>(\<lambda>n. f + g)\<close> \<open>f+g\<close> \<open>-the_s\<close> 0] 
              add.right_neutral lim_sequentially tendsto_const)
      qed  
      then have \<open>f+g = lim (\<lambda>n. the_s n + ((\<Sum>i=0..<card (B m). (\<Sum>k<n. (fps_const (s' k i))*(fps_X^(subdegree (the_s k) - m)))*from_nat_into (B m) (p m i)))) \<close>
        using f57 by auto 
      have \<open>(\<lambda>n. f+g) - the_s = (\<lambda>n. (\<Sum>i=0..<card (B m). (\<Sum>k<n. (fps_const (s' k i))*(fps_X^(subdegree (the_s k) - m)))*from_nat_into (B m) (p m i)))\<close>
        using f57 apply(subst fun_eq_iff, safe) 
        by (smt (verit, best) add_diff_cancel_left' minus_apply) 
      then have \<open>(\<lambda>n. (\<Sum>i=0..<card (B m). (\<Sum>k<n. (fps_const (s' k i))*(fps_X^(subdegree (the_s k)
 - m)))*from_nat_into (B m) (p m i))) \<longlonglongrightarrow> f+g\<close>
        (is \<open>?S \<longlonglongrightarrow> f+g\<close>)  using f58 by presburger 
      then have f84:\<open>f+g = lim ?S\<close>
        by (simp add: limI)
      have f63: \<open>finite (\<Union> (B ` {..m}))\<close>
        using f62 by fastforce
      have \<open>strict_mono (\<lambda>k. subdegree ((\<Sum>i=0..<card (B m). (fps_const (s' k i))*
          (fps_X^(subdegree (the_s k) - m))*from_nat_into (B m) (p m i))))\<close>
        apply(rule monotone_onI)
        apply(insert f55 f56 hyps_thes) 
        by (smt (verit, ccfv_threshold) f87 add.commute add_left_cancel diff_add_cancel 
            strict_monoD subdeg_inf_imp_s_tendsto_zero subdegree_diff_eq2 subdegree_uminus sum_negf)
      then have \<open>(\<lambda>k.  (\<Sum>i=0..<card (B m). (fps_const (s' k i))*(fps_X^(subdegree (the_s k) - m))*
from_nat_into (B m) (p m i))) \<longlonglongrightarrow> 0\<close> 
        using subdeg_inf_imp_s_tendsto_zero by presburger
      define fct where \<open>fct =?f\<close>
      then have f71:\<open>strict_mono fct\<close> using f70 by auto
      have \<open>\<forall>k. \<exists>s. \<forall>n. (\<Sum>i<n. (fps_const (s' i k))*(fps_X^(fct i))) = 
            (\<Sum>i<fct n. (fps_const (s i))*(fps_X^(i)))\<close> 
        using exists_seq_all'[OF f71, of \<open>\<lambda>i. s' i k\<close> for k]
        by meson
      then obtain s where f72:\<open>\<forall>n k. (\<Sum>i<n. (fps_const (s' i k))*(fps_X^(fct i))) = 
  (\<Sum>i<fct n. (fps_const (s i k))*(fps_X^(i)))\<close> 
        by meson
      then have f85: \<open>(\<lambda>n. \<Sum>i<fct n. (fps_const (s i k))*(fps_X^(i))) \<longlonglongrightarrow> Abs_fps (\<lambda>i. s i k)\<close> for k
        by (simp add: Formal_Power_Series_Ring.tendsto_f_seq f71)
      then have f86: \<open>(\<lambda>n. (\<Sum>i<n. (fps_const (s' i k))*(fps_X^(subdegree (the_s i) - m))))
 = (\<lambda>n. \<Sum>i<fct n. (fps_const (s i k))*(fps_X^(i)))\<close>
        for k
        using f72 fct_def by(auto simp:fun_eq_iff) 
      then have \<open>(\<lambda>n. (\<Sum>k<n. (fps_const (s' k i))*(fps_X^(subdegree (the_s k) - m))))
                 \<longlonglongrightarrow> Abs_fps (\<lambda>k. s k i)\<close> for i
        using f85 by presburger
      then have f82:\<open>(\<lambda>n. (\<Sum>i=0..<r. (\<Sum>k<n. (fps_const (s' k i))*(fps_X^(subdegree (the_s k) - m)))
*from_nat_into (B m) (p m i))) \<longlonglongrightarrow> (\<Sum>i=0..<r. Abs_fps (\<lambda>k. s k i)*from_nat_into (B m) (p m i))\<close>
        for r
      proof(induct r)
        case 0
        then show ?case by simp
      next
        case 1:(Suc r)
        have \<open>(\<lambda>n. (\<Sum>k<n. fps_const (s' k r) * fps_X ^ (subdegree (the_s k) - m)) * 
from_nat_into (B m) (p m r)) \<longlonglongrightarrow> Abs_fps (\<lambda>k. s k r) * from_nat_into (B m) (p m r)\<close>
        proof -
          have "(\<lambda>n. from_nat_into (B m) (p m r) * (\<Sum>n<n. fps_const (s' n r) * 
fps_X ^ (subdegree (the_s n) - m))) \<longlonglongrightarrow> from_nat_into (B m) (p m r) * Abs_fps (\<lambda>n. s n r)"
            using LIMSEQ_cmult_fps f85 f86 by presburger
          then show ?thesis
            by (simp add: mult.commute)
        qed
        then show ?case 
          apply(subst atLeast0_lessThan_Suc)
          by (simp add: "1" LIMSEQ_add_fps add.commute)
      qed
      have f83:\<open>(\<Sum>i=0..<r. Abs_fps (\<lambda>k. s k i)*from_nat_into (B m) (p m i)) \<in> I'\<close> for r
      proof(induct r)
        case 0
        then show ?case 
          by (metis (full_types) FPS_ring_def I'_def add_stable_FPS_ring atLeastLessThan0 diff_0 
              diff_add_cancel f53 in_I' partial_object.select_convs(1) ring.genideal_ideal ring_FPS subset_UNIV sum.empty)
      next
        case 1:(Suc r)
        have \<open> from_nat_into (B m) (p m r) \<in> I'\<close> 
          unfolding I'_def genideal_def apply(clarify) 
          by (metis (no_types, lifting) UN_subset_iff ab_group_add_class.ab_diff_conv_add_uminus add.right_neutral 
              add_diff_cancel_left' atLeastLessThan0 atMost_iff card.empty f53 from_nat_into in_mono less_irrefl_nat order_refl sum.empty)
        with 1 show ?case apply(clarsimp)
          by (metis (no_types, lifting) "1" FPS_ring_def Formal_Power_Series_Ring.genideal_sum_rep 
              Formal_Power_Series_Ring.idl_sum I'_def UNIV_I 
              add_stable_FPS_ring f62 ideal.I_l_closed monoid.select_convs(1) partial_object.select_convs(1))
      qed
      then have \<open>f+g \<in> I'\<close> 
      proof -
        have "\<And>n. lim (\<lambda>na. \<Sum>n = 0..<n. (\<Sum>na<na. fps_const (s' na n) * fps_X ^ (subdegree (the_s na) - m))
  * from_nat_into (B m) (p m n)) = (\<Sum>n = 0..<n. Abs_fps (\<lambda>na. s na n) * from_nat_into (B m) (p m n))"
          by (smt (z3) f82 limI)
        then show ?thesis
          using f83 f84 by presburger
      qed
      then show False 
        using hyps(4) by force
    qed
    then have \<open>I = I'\<close>
      using \<open>I' \<subseteq> I\<close> by fastforce
    then show \<open>\<exists>A\<subseteq>carrier local.FPS_ring. finite A \<and> I = Idl\<^bsub>local.FPS_ring\<^esub> A\<close>
      by (metis FPS_ring_def I'_def f62 partial_object.select_convs(1) subset_UNIV)
  qed
qed

end

end