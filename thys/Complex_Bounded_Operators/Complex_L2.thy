section \<open>\<open>Complex_L2\<close> -- Hilbert space of square-summable functions\<close>

(*
Authors:

  Dominique Unruh, University of Tartu, unruh@ut.ee
  Jose Manuel Rodriguez Caballero, University of Tartu, jose.manuel.rodriguez.caballero@ut.ee

*)

theory Complex_L2
  imports 
    Complex_Bounded_Linear_Function

    "HOL-Analysis.L2_Norm"
    "HOL-Library.Rewrite"
    "HOL-Analysis.Infinite_Sum"
begin

unbundle cblinfun_notation
unbundle no_notation_blinfun_apply

subsection \<open>l2 norm of functions\<close>

definition "has_ell2_norm (x::_\<Rightarrow>complex) \<longleftrightarrow> (\<lambda>i. (x i)\<^sup>2) abs_summable_on UNIV"

lemma has_ell2_norm_bdd_above: \<open>has_ell2_norm x \<longleftrightarrow> bdd_above (sum (\<lambda>xa. norm ((x xa)\<^sup>2)) ` Collect finite)\<close>
  by (simp add: has_ell2_norm_def abs_summable_bdd_above)

lemma has_ell2_norm_L2_set: "has_ell2_norm x = bdd_above (L2_set (norm o x) ` Collect finite)"
proof (rule iffI)
  have \<open>mono sqrt\<close>
    using monoI real_sqrt_le_mono by blast
  assume \<open>has_ell2_norm x\<close>
  then have *: \<open>bdd_above (sum (\<lambda>xa. norm ((x xa)\<^sup>2)) ` Collect finite)\<close>
    by (subst (asm) has_ell2_norm_bdd_above)
  have \<open>bdd_above ((\<lambda>F. sqrt (sum (\<lambda>xa. norm ((x xa)\<^sup>2)) F)) ` Collect finite)\<close>
    using bdd_above_image_mono[OF \<open>mono sqrt\<close> *]
    by (auto simp: image_image)
  then show \<open>bdd_above (L2_set (norm o x) ` Collect finite)\<close>
    by (auto simp: L2_set_def norm_power)
next
  define p2 where \<open>p2 x = (if x < 0 then 0 else x^2)\<close> for x :: real
  have \<open>mono p2\<close>
    by (simp add: monoI p2_def)
  have [simp]: \<open>p2 (L2_set f F) = (\<Sum>i\<in>F. (f i)\<^sup>2)\<close> for f and F :: \<open>'a set\<close>
    by (smt (verit) L2_set_def L2_set_nonneg p2_def power2_less_0 real_sqrt_pow2 sum.cong sum_nonneg)
  assume *: \<open>bdd_above (L2_set (norm o x) ` Collect finite)\<close>
  have \<open>bdd_above (p2 ` L2_set (norm o x) ` Collect finite)\<close>
    using bdd_above_image_mono[OF \<open>mono p2\<close> *]
    by auto
  then show \<open>has_ell2_norm x\<close>
    apply (simp add: image_image has_ell2_norm_def abs_summable_bdd_above)
    by (simp add: norm_power)
qed

definition ell2_norm :: \<open>('a \<Rightarrow> complex) \<Rightarrow> real\<close> where \<open>ell2_norm x = sqrt (\<Sum>\<^sub>\<infinity>i. norm (x i)^2)\<close>

lemma ell2_norm_SUP:
  assumes \<open>has_ell2_norm x\<close>
  shows "ell2_norm x = sqrt (SUP F\<in>{F. finite F}. sum (\<lambda>i. norm (x i)^2) F)"
  using assms apply (auto simp add: ell2_norm_def has_ell2_norm_def)
  apply (subst infsum_nonneg_is_SUPREMUM_real)
  by (auto simp: norm_power)

lemma ell2_norm_L2_set: 
  assumes "has_ell2_norm x"
  shows "ell2_norm x = (SUP F\<in>{F. finite F}. L2_set (norm o x) F)"
proof-
  have "sqrt (\<Squnion> (sum (\<lambda>i. (cmod (x i))\<^sup>2) ` Collect finite)) =
      (SUP F\<in>{F. finite F}. sqrt (\<Sum>i\<in>F. (cmod (x i))\<^sup>2))"
  proof (subst continuous_at_Sup_mono)
    show "mono sqrt"
      by (simp add: mono_def)      
    show "continuous (at_left (\<Squnion> (sum (\<lambda>i. (cmod (x i))\<^sup>2) ` Collect finite))) sqrt"
      using continuous_at_split isCont_real_sqrt by blast    
    show "sum (\<lambda>i. (cmod (x i))\<^sup>2) ` Collect finite \<noteq> {}"
      by auto      
    show "bdd_above (sum (\<lambda>i. (cmod (x i))\<^sup>2) ` Collect finite)"
      using has_ell2_norm_bdd_above[THEN iffD1, OF assms] by (auto simp: norm_power)
    show "\<Squnion> (sqrt ` sum (\<lambda>i. (cmod (x i))\<^sup>2) ` Collect finite) = (SUP F\<in>Collect finite. sqrt (\<Sum>i\<in>F. (cmod (x i))\<^sup>2))"
      by (metis image_image)      
  qed  
  thus ?thesis 
    using assms by (auto simp: ell2_norm_SUP L2_set_def)
qed

lemma has_ell2_norm_finite[simp]: "has_ell2_norm (x::'a::finite\<Rightarrow>_)"
  unfolding has_ell2_norm_def by simp

lemma ell2_norm_finite: 
  "ell2_norm (x::'a::finite\<Rightarrow>complex) = sqrt (sum (\<lambda>i. (norm(x i))^2) UNIV)"
  by (simp add: ell2_norm_def)

lemma ell2_norm_finite_L2_set: "ell2_norm (x::'a::finite\<Rightarrow>complex) = L2_set (norm o x) UNIV"
  by (simp add: ell2_norm_finite L2_set_def)

lemma ell2_ket:
  fixes a
  defines \<open>f \<equiv> (\<lambda>i. if a = i then 1 else 0)\<close>
  shows has_ell2_norm_ket: \<open>has_ell2_norm f\<close>
    and ell2_norm_ket: \<open>ell2_norm f = 1\<close>
proof -
  have \<open>(\<lambda>x. (f x)\<^sup>2) abs_summable_on {a}\<close>
    apply (rule summable_on_finite) by simp
  then show \<open>has_ell2_norm f\<close>
    unfolding has_ell2_norm_def
    apply (rule summable_on_cong_neutral[THEN iffD1, rotated -1])
    unfolding f_def by auto

  have \<open>(\<Sum>\<^sub>\<infinity>x\<in>{a}. (f x)\<^sup>2) = 1\<close>
    apply (subst infsum_finite)
    by (auto simp: f_def)
  then show \<open>ell2_norm f = 1\<close>
    unfolding ell2_norm_def
    apply (subst infsum_cong_neutral[where T=\<open>{a}\<close> and g=\<open>\<lambda>x. (cmod (f x))\<^sup>2\<close>])
    by (auto simp: f_def)
qed

lemma ell2_norm_geq0: \<open>ell2_norm x \<ge> 0\<close>
  by (auto simp: ell2_norm_def intro!: infsum_nonneg)

lemma ell2_norm_point_bound:
  assumes \<open>has_ell2_norm x\<close>
  shows \<open>ell2_norm x \<ge> cmod (x i)\<close>
proof -
  have \<open>(cmod (x i))\<^sup>2 = norm ((x i)\<^sup>2)\<close>
    by (simp add: norm_power)
  also have \<open>norm ((x i)\<^sup>2) = sum (\<lambda>i. (norm ((x i)\<^sup>2))) {i}\<close>
    by auto
  also have \<open>\<dots> = infsum (\<lambda>i. (norm ((x i)\<^sup>2))) {i}\<close>
    by (rule infsum_finite[symmetric], simp)
  also have \<open>\<dots> \<le> infsum (\<lambda>i. (norm ((x i)\<^sup>2))) UNIV\<close>
    apply (rule infsum_mono_neutral)
    using assms by (auto simp: has_ell2_norm_def)
  also have \<open>\<dots> = (ell2_norm x)\<^sup>2\<close>
    by (metis (no_types, lifting) ell2_norm_def ell2_norm_geq0 infsum_cong norm_power real_sqrt_eq_iff real_sqrt_unique)
  finally show ?thesis
    using ell2_norm_geq0 power2_le_imp_le by blast
qed

lemma ell2_norm_0:
  assumes "has_ell2_norm x"
  shows "(ell2_norm x = 0) = (x = (\<lambda>_. 0))"
proof
  assume u1: "x = (\<lambda>_. 0)"
  have u2: "(SUP x::'a set\<in>Collect finite. (0::real)) = 0"
    if "x = (\<lambda>_. 0)"
    by (metis cSUP_const empty_Collect_eq finite.emptyI)
  show "ell2_norm x = 0"
    unfolding ell2_norm_def
    using u1 u2 by auto 
next
  assume norm0: "ell2_norm x = 0"
  show "x = (\<lambda>_. 0)"
  proof
    fix i
    have \<open>cmod (x i) \<le> ell2_norm x\<close>
      using assms by (rule ell2_norm_point_bound)
    also have \<open>\<dots> = 0\<close>
      by (fact norm0)
    finally show "x i = 0" by auto
  qed
qed


lemma ell2_norm_smult:
  assumes "has_ell2_norm x"
  shows "has_ell2_norm (\<lambda>i. c * x i)" and "ell2_norm (\<lambda>i. c * x i) = cmod c * ell2_norm x"
proof -
  have L2_set_mul: "L2_set (cmod \<circ> (\<lambda>i. c * x i)) F = cmod c * L2_set (cmod \<circ> x) F" for F
  proof-
    have "L2_set (cmod \<circ> (\<lambda>i. c * x i)) F = L2_set (\<lambda>i. (cmod c * (cmod o x) i)) F"
      by (metis comp_def norm_mult)
    also have "\<dots> = cmod c * L2_set (cmod o x) F"
      by (metis norm_ge_zero L2_set_right_distrib)
    finally show ?thesis .
  qed

  from assms obtain M where M: "M \<ge> L2_set (cmod o x) F" if "finite F" for F
    unfolding has_ell2_norm_L2_set bdd_above_def by auto
  hence "cmod c * M \<ge> L2_set (cmod o (\<lambda>i. c * x i)) F" if "finite F" for F
    unfolding L2_set_mul
    by (simp add: ordered_comm_semiring_class.comm_mult_left_mono that) 
  thus has: "has_ell2_norm (\<lambda>i. c * x i)"
    unfolding has_ell2_norm_L2_set bdd_above_def using L2_set_mul[symmetric] by auto
  have "ell2_norm (\<lambda>i. c * x i) = (SUP F \<in> Collect finite. (L2_set (cmod \<circ> (\<lambda>i. c * x i)) F))"
    by (simp add: ell2_norm_L2_set has)
  also have "\<dots> = (SUP F \<in> Collect finite. (cmod c * L2_set (cmod \<circ> x) F))"
    using L2_set_mul by auto   
  also have "\<dots> = cmod c * ell2_norm x" 
  proof (subst ell2_norm_L2_set)
    show "has_ell2_norm x"
      by (simp add: assms)      
    show "(SUP F\<in>Collect finite. cmod c * L2_set (cmod \<circ> x) F) = cmod c * \<Squnion> (L2_set (cmod \<circ> x) ` Collect finite)"
    proof (subst continuous_at_Sup_mono [where f = "\<lambda>x. cmod c * x"])
      show "mono ((*) (cmod c))"
        by (simp add: mono_def ordered_comm_semiring_class.comm_mult_left_mono)
      show "continuous (at_left (\<Squnion> (L2_set (cmod \<circ> x) ` Collect finite))) ((*) (cmod c))"
      proof (rule continuous_mult)
        show "continuous (at_left (\<Squnion> (L2_set (cmod \<circ> x) ` Collect finite))) (\<lambda>x. cmod c)"
          by simp
        show "continuous (at_left (\<Squnion> (L2_set (cmod \<circ> x) ` Collect finite))) (\<lambda>x. x)"
          by simp
      qed    
      show "L2_set (cmod \<circ> x) ` Collect finite \<noteq> {}"
        by auto        
      show "bdd_above (L2_set (cmod \<circ> x) ` Collect finite)"
        by (meson assms has_ell2_norm_L2_set)        
      show "(SUP F\<in>Collect finite. cmod c * L2_set (cmod \<circ> x) F) = \<Squnion> ((*) (cmod c) ` L2_set (cmod \<circ> x) ` Collect finite)"
        by (metis image_image)        
    qed   
  qed     
  finally show "ell2_norm (\<lambda>i. c * x i) = cmod c * ell2_norm x".
qed


lemma ell2_norm_triangle:
  assumes "has_ell2_norm x" and "has_ell2_norm y"
  shows "has_ell2_norm (\<lambda>i. x i + y i)" and "ell2_norm (\<lambda>i. x i + y i) \<le> ell2_norm x + ell2_norm y"
proof -
  have triangle: "L2_set (cmod \<circ> (\<lambda>i. x i + y i)) F \<le> L2_set (cmod \<circ> x) F + L2_set (cmod \<circ> y) F" 
    (is "?lhs\<le>?rhs") 
    if "finite F" for F
  proof -
    have "?lhs \<le> L2_set (\<lambda>i. (cmod o x) i + (cmod o y) i) F"
    proof (rule L2_set_mono)
      show "(cmod \<circ> (\<lambda>i. x i + y i)) i \<le> (cmod \<circ> x) i + (cmod \<circ> y) i"
        if "i \<in> F"
        for i :: 'a
        using that norm_triangle_ineq by auto 
      show "0 \<le> (cmod \<circ> (\<lambda>i. x i + y i)) i"
        if "i \<in> F"
        for i :: 'a
        using that
        by simp 
    qed
    also have "\<dots> \<le> ?rhs"
      by (rule L2_set_triangle_ineq)
    finally show ?thesis .
  qed
  obtain Mx My where Mx: "Mx \<ge> L2_set (cmod o x) F" and My: "My \<ge> L2_set (cmod o y) F" 
    if "finite F" for F
    using assms unfolding has_ell2_norm_L2_set bdd_above_def by auto
  hence MxMy: "Mx + My \<ge> L2_set (cmod \<circ> x) F + L2_set (cmod \<circ> y) F" if "finite F" for F
    using that by fastforce
  hence bdd_plus: "bdd_above ((\<lambda>xa. L2_set (cmod \<circ> x) xa + L2_set (cmod \<circ> y) xa) ` Collect finite)"
    unfolding bdd_above_def by auto
  from MxMy have MxMy': "Mx + My \<ge> L2_set (cmod \<circ> (\<lambda>i. x i + y i)) F" if "finite F" for F 
    using triangle that by fastforce
  thus has: "has_ell2_norm (\<lambda>i. x i + y i)"
    unfolding has_ell2_norm_L2_set bdd_above_def by auto
  have SUP_plus: "(SUP x\<in>A. f x + g x) \<le> (SUP x\<in>A. f x) + (SUP x\<in>A. g x)" 
    if notempty: "A\<noteq>{}" and bddf: "bdd_above (f`A)"and bddg: "bdd_above (g`A)"
    for f g :: "'a set \<Rightarrow> real" and A
  proof-
    have xleq: "x \<le> (SUP x\<in>A. f x) + (SUP x\<in>A. g x)" if x: "x \<in> (\<lambda>x. f x + g x) ` A" for x
    proof -
      obtain a where aA: "a:A" and ax: "x = f a + g a"
        using x by blast
      have fa: "f a \<le> (SUP x\<in>A. f x)"
        by (simp add: bddf aA cSUP_upper)
      moreover have "g a \<le> (SUP x\<in>A. g x)"
        by (simp add: bddg aA cSUP_upper)
      ultimately have "f a + g a \<le> (SUP x\<in>A. f x) + (SUP x\<in>A. g x)" by simp
      with ax show ?thesis by simp
    qed
    have "(\<lambda>x. f x + g x) ` A \<noteq> {}"
      using notempty by auto        
    moreover have "x \<le> \<Squnion> (f ` A) + \<Squnion> (g ` A)"
      if "x \<in> (\<lambda>x. f x + g x) ` A"
      for x :: real
      using that
      by (simp add: xleq) 
    ultimately show ?thesis
      by (meson bdd_above_def cSup_le_iff)      
  qed
  have a2: "bdd_above (L2_set (cmod \<circ> x) ` Collect finite)"
    by (meson assms(1) has_ell2_norm_L2_set)    
  have a3: "bdd_above (L2_set (cmod \<circ> y) ` Collect finite)"
    by (meson assms(2) has_ell2_norm_L2_set)    
  have a1: "Collect finite \<noteq> {}"
    by auto    
  have a4: "\<Squnion> (L2_set (cmod \<circ> (\<lambda>i. x i + y i)) ` Collect finite)
    \<le> (SUP xa\<in>Collect finite.
           L2_set (cmod \<circ> x) xa + L2_set (cmod \<circ> y) xa)"
    by (metis (mono_tags, lifting) a1 bdd_plus cSUP_mono mem_Collect_eq triangle)    
  have "\<forall>r. \<Squnion> (L2_set (cmod \<circ> (\<lambda>a. x a + y a)) ` Collect finite) \<le> r \<or> \<not> (SUP A\<in>Collect finite. L2_set (cmod \<circ> x) A + L2_set (cmod \<circ> y) A) \<le> r"
    using a4 by linarith
  hence "\<Squnion> (L2_set (cmod \<circ> (\<lambda>i. x i + y i)) ` Collect finite)
    \<le> \<Squnion> (L2_set (cmod \<circ> x) ` Collect finite) +
       \<Squnion> (L2_set (cmod \<circ> y) ` Collect finite)"
    by (metis (no_types) SUP_plus a1 a2 a3)
  hence "\<Squnion> (L2_set (cmod \<circ> (\<lambda>i. x i + y i)) ` Collect finite) \<le> ell2_norm x + ell2_norm y"
    by (simp add: assms(1) assms(2) ell2_norm_L2_set)
  thus "ell2_norm (\<lambda>i. x i + y i) \<le> ell2_norm x + ell2_norm y"
    by (simp add: ell2_norm_L2_set has)  
qed

lemma ell2_norm_uminus:
  assumes "has_ell2_norm x"
  shows \<open>has_ell2_norm (\<lambda>i. - x i)\<close> and \<open>ell2_norm (\<lambda>i. - x i) = ell2_norm x\<close>
  using assms by (auto simp: has_ell2_norm_def ell2_norm_def)

subsection \<open>The type \<open>ell2\<close> of square-summable functions\<close>

typedef 'a ell2 = "{x::'a\<Rightarrow>complex. has_ell2_norm x}"
  unfolding has_ell2_norm_def by (rule exI[of _ "\<lambda>_.0"], auto)
setup_lifting type_definition_ell2

instantiation ell2 :: (type)complex_vector begin
lift_definition zero_ell2 :: "'a ell2" is "\<lambda>_. 0" by (auto simp: has_ell2_norm_def)
lift_definition uminus_ell2 :: "'a ell2 \<Rightarrow> 'a ell2" is uminus by (simp add: has_ell2_norm_def)
lift_definition plus_ell2 :: "'a ell2 \<Rightarrow> 'a ell2 \<Rightarrow> 'a ell2" is "\<lambda>f g x. f x + g x"
  by (rule ell2_norm_triangle) 
lift_definition minus_ell2 :: "'a ell2 \<Rightarrow> 'a ell2 \<Rightarrow> 'a ell2" is "\<lambda>f g x. f x - g x"
  apply (subst add_uminus_conv_diff[symmetric])
  apply (rule ell2_norm_triangle)
  by (auto simp add: ell2_norm_uminus)
lift_definition scaleR_ell2 :: "real \<Rightarrow> 'a ell2 \<Rightarrow> 'a ell2" is "\<lambda>r f x. complex_of_real r * f x"
  by (rule ell2_norm_smult)
lift_definition scaleC_ell2 :: "complex \<Rightarrow> 'a ell2 \<Rightarrow> 'a ell2" is "\<lambda>c f x. c * f x"
  by (rule ell2_norm_smult)

instance
proof
  fix a b c :: "'a ell2"

  show "((*\<^sub>R) r::'a ell2 \<Rightarrow> _) = (*\<^sub>C) (complex_of_real r)" for r
    apply (rule ext) apply transfer by auto
  show "a + b + c = a + (b + c)"
    by (transfer; rule ext; simp)
  show "a + b = b + a"
    by (transfer; rule ext; simp)
  show "0 + a = a"
    by (transfer; rule ext; simp)
  show "- a + a = 0"
    by (transfer; rule ext; simp)
  show "a - b = a + - b"
    by (transfer; rule ext; simp)
  show "r *\<^sub>C (a + b) = r *\<^sub>C a + r *\<^sub>C b" for r
    apply (transfer; rule ext)
    by (simp add: vector_space_over_itself.scale_right_distrib)
  show "(r + r') *\<^sub>C a = r *\<^sub>C a + r' *\<^sub>C a" for r r'
    apply (transfer; rule ext)
    by (simp add: ring_class.ring_distribs(2)) 
  show "r *\<^sub>C r' *\<^sub>C a = (r * r') *\<^sub>C a" for r r'
    by (transfer; rule ext; simp)
  show "1 *\<^sub>C a = a"
    by (transfer; rule ext; simp)
qed
end

instantiation ell2 :: (type)complex_normed_vector begin
lift_definition norm_ell2 :: "'a ell2 \<Rightarrow> real" is ell2_norm .
declare norm_ell2_def[code del]
definition "dist x y = norm (x - y)" for x y::"'a ell2"
definition "sgn x = x /\<^sub>R norm x" for x::"'a ell2"
definition [code del]: "uniformity = (INF e\<in>{0<..}. principal {(x::'a ell2, y). norm (x - y) < e})"
definition [code del]: "open U = (\<forall>x\<in>U. \<forall>\<^sub>F (x', y) in INF e\<in>{0<..}. principal {(x, y). norm (x - y) < e}. x' = x \<longrightarrow> y \<in> U)" for U :: "'a ell2 set"
instance
proof
  fix a b :: "'a ell2"
  show "dist a b = norm (a - b)"
    by (simp add: dist_ell2_def)    
  show "sgn a = a /\<^sub>R norm a"
    by (simp add: sgn_ell2_def)    
  show "uniformity = (INF e\<in>{0<..}. principal {(x, y). dist (x::'a ell2) y < e})"
    unfolding dist_ell2_def  uniformity_ell2_def by simp
  show "open U = (\<forall>x\<in>U. \<forall>\<^sub>F (x', y) in uniformity. (x'::'a ell2) = x \<longrightarrow> y \<in> U)" for U :: "'a ell2 set"
    unfolding uniformity_ell2_def open_ell2_def by simp_all        
  show "(norm a = 0) = (a = 0)"
    apply transfer by (fact ell2_norm_0)    
  show "norm (a + b) \<le> norm a + norm b"
    apply transfer by (fact ell2_norm_triangle)
  show "norm (r *\<^sub>R (a::'a ell2)) = \<bar>r\<bar> * norm a" for r
    and a :: "'a ell2"
    apply transfer
    by (simp add: ell2_norm_smult(2)) 
  show "norm (r *\<^sub>C a) = cmod r * norm a" for r
    apply transfer
    by (simp add: ell2_norm_smult(2)) 
qed  
end

lemma norm_point_bound_ell2: "norm (Rep_ell2 x i) \<le> norm x"
  apply transfer
  by (simp add: ell2_norm_point_bound)

lemma ell2_norm_finite_support:
  assumes \<open>finite S\<close> \<open>\<And> i. i \<notin> S \<Longrightarrow> Rep_ell2 x i = 0\<close>
  shows \<open>norm x = sqrt ((sum (\<lambda>i. (cmod (Rep_ell2 x i))\<^sup>2)) S)\<close>
proof (insert assms(2), transfer fixing: S)
  fix x :: \<open>'a \<Rightarrow> complex\<close>
  assume zero: \<open>\<And>i. i \<notin> S \<Longrightarrow> x i = 0\<close>
  have \<open>ell2_norm x = sqrt (\<Sum>\<^sub>\<infinity>i. (cmod (x i))\<^sup>2)\<close>
    by (auto simp: ell2_norm_def)
  also have \<open>\<dots> = sqrt (\<Sum>\<^sub>\<infinity>i\<in>S. (cmod (x i))\<^sup>2)\<close>
    apply (subst infsum_cong_neutral[where g=\<open>\<lambda>i. (cmod (x i))\<^sup>2\<close> and S=UNIV and T=S])
    using zero by auto
  also have \<open>\<dots> = sqrt (\<Sum>i\<in>S. (cmod (x i))\<^sup>2)\<close>
    using \<open>finite S\<close> by simp
  finally show \<open>ell2_norm x = sqrt (\<Sum>i\<in>S. (cmod (x i))\<^sup>2)\<close>
    by -
qed

instantiation ell2 :: (type) complex_inner begin
lift_definition cinner_ell2 :: "'a ell2 \<Rightarrow> 'a ell2 \<Rightarrow> complex" is 
  "\<lambda>x y. infsum (\<lambda>i. (cnj (x i) * y i)) UNIV" .
declare cinner_ell2_def[code del]

instance
proof standard
  fix x y z :: "'a ell2" fix c :: complex
  show "cinner x y = cnj (cinner y x)"
  proof transfer
    fix x y :: "'a\<Rightarrow>complex" assume "has_ell2_norm x" and "has_ell2_norm y"
    have "(\<Sum>\<^sub>\<infinity>i. cnj (x i) * y i) = (\<Sum>\<^sub>\<infinity>i. cnj (cnj (y i) * x i))"
      by (metis complex_cnj_cnj complex_cnj_mult mult.commute)
    also have "\<dots> = cnj (\<Sum>\<^sub>\<infinity>i. cnj (y i) * x i)"
      by (metis infsum_cnj) 
    finally show "(\<Sum>\<^sub>\<infinity>i. cnj (x i) * y i) = cnj (\<Sum>\<^sub>\<infinity>i. cnj (y i) * x i)" .
  qed

  show "cinner (x + y) z = cinner x z + cinner y z"
  proof transfer
    fix x y z :: "'a \<Rightarrow> complex"
    assume "has_ell2_norm x"
    hence cnj_x: "(\<lambda>i. cnj (x i) * cnj (x i)) abs_summable_on UNIV"
      by (simp del: complex_cnj_mult add: norm_mult[symmetric] complex_cnj_mult[symmetric] has_ell2_norm_def power2_eq_square)
    assume "has_ell2_norm y"
    hence cnj_y: "(\<lambda>i. cnj (y i) * cnj (y i)) abs_summable_on UNIV"
      by (simp del: complex_cnj_mult add: norm_mult[symmetric] complex_cnj_mult[symmetric] has_ell2_norm_def power2_eq_square)
    assume "has_ell2_norm z"
    hence z: "(\<lambda>i. z i * z i) abs_summable_on UNIV" 
      by (simp add: norm_mult[symmetric] has_ell2_norm_def power2_eq_square)
    have cnj_x_z:"(\<lambda>i. cnj (x i) * z i) abs_summable_on UNIV"
      using cnj_x z by (rule abs_summable_product) 
    have cnj_y_z:"(\<lambda>i. cnj (y i) * z i) abs_summable_on UNIV"
      using cnj_y z by (rule abs_summable_product) 
    show "(\<Sum>\<^sub>\<infinity>i. cnj (x i + y i) * z i) = (\<Sum>\<^sub>\<infinity>i. cnj (x i) * z i) + (\<Sum>\<^sub>\<infinity>i. cnj (y i) * z i)"
      apply (subst infsum_add [symmetric])
      using cnj_x_z cnj_y_z 
      by (auto simp add: summable_on_iff_abs_summable_on_complex distrib_left mult.commute)
  qed

  show "cinner (c *\<^sub>C x) y = cnj c * cinner x y"
  proof transfer
    fix x y :: "'a \<Rightarrow> complex" and c :: complex
    assume "has_ell2_norm x"
    hence cnj_x: "(\<lambda>i. cnj (x i) * cnj (x i)) abs_summable_on UNIV"
      by (simp del: complex_cnj_mult add: norm_mult[symmetric] complex_cnj_mult[symmetric] has_ell2_norm_def power2_eq_square)
    assume "has_ell2_norm y"
    hence y: "(\<lambda>i. y i * y i) abs_summable_on UNIV" 
      by (simp add: norm_mult[symmetric] has_ell2_norm_def power2_eq_square)
    have cnj_x_y:"(\<lambda>i. cnj (x i) * y i) abs_summable_on UNIV"
      using cnj_x y by (rule abs_summable_product) 
    thus "(\<Sum>\<^sub>\<infinity>i. cnj (c * x i) * y i) = cnj c * (\<Sum>\<^sub>\<infinity>i. cnj (x i) * y i)"
      by (auto simp flip: infsum_cmult_right simp add: abs_summable_summable mult.commute vector_space_over_itself.scale_left_commute)
  qed

  show "0 \<le> cinner x x"
  proof transfer
    fix x :: "'a \<Rightarrow> complex"
    assume "has_ell2_norm x"
    hence "(\<lambda>i. cmod (cnj (x i) * x i)) abs_summable_on UNIV"
      by (simp add: norm_mult has_ell2_norm_def power2_eq_square)
    hence "(\<lambda>i. cnj (x i) * x i) abs_summable_on UNIV"
      by auto
    hence sum: "(\<lambda>i. cnj (x i) * x i) abs_summable_on UNIV"
      unfolding has_ell2_norm_def power2_eq_square.
    have "0 = (\<Sum>\<^sub>\<infinity>i::'a. 0)" by auto
    also have "\<dots> \<le> (\<Sum>\<^sub>\<infinity>i. cnj (x i) * x i)"
      apply (rule infsum_mono_complex)
      by (auto simp add: abs_summable_summable sum)
    finally show "0 \<le> (\<Sum>\<^sub>\<infinity>i. cnj (x i) * x i)" by assumption
  qed

  show "(cinner x x = 0) = (x = 0)"
  proof (transfer, auto)
    fix x :: "'a \<Rightarrow> complex"
    assume "has_ell2_norm x"
    hence "(\<lambda>i::'a. cmod (cnj (x i) * x i)) abs_summable_on UNIV"
      by (smt (verit, del_insts) complex_mod_mult_cnj has_ell2_norm_def mult.commute norm_ge_zero norm_power real_norm_def summable_on_cong)
    hence cmod_x2: "(\<lambda>i. cnj (x i) * x i) abs_summable_on UNIV"
      unfolding has_ell2_norm_def power2_eq_square
      by simp
    assume eq0: "(\<Sum>\<^sub>\<infinity>i. cnj (x i) * x i) = 0"
    show "x = (\<lambda>_. 0)"
    proof (rule ccontr)
      assume "x \<noteq> (\<lambda>_. 0)"
      then obtain i where "x i \<noteq> 0" by auto
      hence "0 < cnj (x i) * x i"
        by (metis le_less cnj_x_x_geq0 complex_cnj_zero_iff vector_space_over_itself.scale_eq_0_iff)
      also have "\<dots> = (\<Sum>\<^sub>\<infinity>i\<in>{i}. cnj (x i) * x i)" by auto
      also have "\<dots> \<le> (\<Sum>\<^sub>\<infinity>i. cnj (x i) * x i)"
        apply (rule infsum_mono_neutral_complex)
        by (auto simp add: abs_summable_summable cmod_x2)
      also from eq0 have "\<dots> = 0" by assumption
      finally show False by simp
    qed
  qed

  show "norm x = sqrt (cmod (cinner x x))"
  proof transfer 
    fix x :: "'a \<Rightarrow> complex" 
    assume x: "has_ell2_norm x"
    have "(\<lambda>i::'a. cmod (x i) * cmod (x i)) abs_summable_on UNIV \<Longrightarrow>
    (\<lambda>i::'a. cmod (cnj (x i) * x i)) abs_summable_on UNIV"
      by (simp add: norm_mult has_ell2_norm_def power2_eq_square)
    hence sum: "(\<lambda>i. cnj (x i) * x i) abs_summable_on UNIV"
      by (metis (no_types, lifting) complex_mod_mult_cnj has_ell2_norm_def mult.commute norm_power summable_on_cong x)
    from x have "ell2_norm x = sqrt (\<Sum>\<^sub>\<infinity>i. (cmod (x i))\<^sup>2)"
      unfolding ell2_norm_def by simp
    also have "\<dots> = sqrt (\<Sum>\<^sub>\<infinity>i. cmod (cnj (x i) * x i))"
      unfolding norm_complex_def power2_eq_square by auto
    also have "\<dots> = sqrt (cmod (\<Sum>\<^sub>\<infinity>i. cnj (x i) * x i))"
      by (auto simp: infsum_cmod abs_summable_summable sum)
    finally show "ell2_norm x = sqrt (cmod (\<Sum>\<^sub>\<infinity>i. cnj (x i) * x i))" by assumption
  qed
qed
end

instance ell2 :: (type) chilbert_space
proof
  fix X :: \<open>nat \<Rightarrow> 'a ell2\<close>
  define x where \<open>x n a = Rep_ell2 (X n) a\<close> for n a
  have [simp]: \<open>has_ell2_norm (x n)\<close> for n
    using Rep_ell2 x_def[abs_def] by simp

  assume \<open>Cauchy X\<close>
  moreover have "dist (x n a) (x m a) \<le> dist (X n) (X m)" for n m a
    by (metis Rep_ell2 x_def dist_norm ell2_norm_point_bound mem_Collect_eq minus_ell2.rep_eq norm_ell2.rep_eq)
  ultimately have \<open>Cauchy (\<lambda>n. x n a)\<close> for a
    by (meson Cauchy_def le_less_trans)
  then obtain l where x_lim: \<open>(\<lambda>n. x n a) \<longlonglongrightarrow> l a\<close> for a
    apply atomize_elim apply (rule choice)
    by (simp add: convergent_eq_Cauchy)
  define L where \<open>L = Abs_ell2 l\<close>
  define normF where \<open>normF F x = L2_set (cmod \<circ> x) F\<close> for F :: \<open>'a set\<close> and x
  have normF_triangle: \<open>normF F (\<lambda>a. x a + y a) \<le> normF F x + normF F y\<close> if \<open>finite F\<close> for F x y
  proof -
    have \<open>normF F (\<lambda>a. x a + y a) = L2_set (\<lambda>a. cmod (x a + y a)) F\<close>
      by (metis (mono_tags, lifting) L2_set_cong comp_apply normF_def)
    also have \<open>\<dots> \<le> L2_set (\<lambda>a. cmod (x a) + cmod (y a)) F\<close>
      by (meson L2_set_mono norm_ge_zero norm_triangle_ineq)
    also have \<open>\<dots> \<le> L2_set (\<lambda>a. cmod (x a)) F + L2_set (\<lambda>a. cmod (y a)) F\<close>
      by (simp add: L2_set_triangle_ineq)
    also have \<open>\<dots> \<le> normF F x + normF F y\<close>
      by (smt (verit, best) L2_set_cong normF_def comp_apply)
    finally show ?thesis
      by -
  qed
  have normF_negate: \<open>normF F (\<lambda>a. - x a) = normF F x\<close> if \<open>finite F\<close> for F x
    unfolding normF_def o_def by simp
  have normF_ell2norm: \<open>normF F x \<le> ell2_norm x\<close> if \<open>finite F\<close> and \<open>has_ell2_norm x\<close> for F x
    apply (auto intro!: cSUP_upper2[where x=F] simp: that normF_def ell2_norm_L2_set)
    by (meson has_ell2_norm_L2_set that(2))

  note Lim_bounded2[rotated, rule_format, trans]

  from \<open>Cauchy X\<close>
  obtain I where cauchyX: \<open>norm (X n - X m) \<le> \<epsilon>\<close> if \<open>\<epsilon>>0\<close> \<open>n\<ge>I \<epsilon>\<close> \<open>m\<ge>I \<epsilon>\<close> for \<epsilon> n m
    by (metis Cauchy_def dist_norm less_eq_real_def)
  have normF_xx: \<open>normF F (\<lambda>a. x n a - x m a) \<le> \<epsilon>\<close> if \<open>finite F\<close> \<open>\<epsilon>>0\<close> \<open>n\<ge>I \<epsilon>\<close> \<open>m\<ge>I \<epsilon>\<close> for \<epsilon> n m F
    apply (subst asm_rl[of \<open>(\<lambda>a. x n a - x m a) = Rep_ell2 (X n - X m)\<close>])
     apply (simp add: x_def minus_ell2.rep_eq)
    using that cauchyX by (metis Rep_ell2 mem_Collect_eq normF_ell2norm norm_ell2.rep_eq order_trans)
  have normF_xl_lim: \<open>(\<lambda>m. normF F (\<lambda>a. x m a - l a)) \<longlonglongrightarrow> 0\<close> if \<open>finite F\<close> for F
  proof -
    have \<open>(\<lambda>xa. cmod (x xa m - l m)) \<longlonglongrightarrow> 0\<close> for m
      using x_lim by (simp add: LIM_zero_iff tendsto_norm_zero)
    then have \<open>(\<lambda>m. \<Sum>i\<in>F. ((cmod \<circ> (\<lambda>a. x m a - l a)) i)\<^sup>2) \<longlonglongrightarrow> 0\<close>
      by (auto intro: tendsto_null_sum)
    then show ?thesis
      unfolding normF_def L2_set_def
      using tendsto_real_sqrt by force
  qed
  have normF_xl: \<open>normF F (\<lambda>a. x n a - l a) \<le> \<epsilon>\<close>
    if \<open>n \<ge> I \<epsilon>\<close> and \<open>\<epsilon> > 0\<close> and \<open>finite F\<close> for n \<epsilon> F
  proof -
    have \<open>normF F (\<lambda>a. x n a - l a) - \<epsilon> \<le> normF F (\<lambda>a. x n a - x m a) + normF F (\<lambda>a. x m a - l a) - \<epsilon>\<close> for m
      using normF_triangle[OF \<open>finite F\<close>, where x=\<open>(\<lambda>a. x n a - x m a)\<close> and y=\<open>(\<lambda>a. x m a - l a)\<close>]
      by auto
    also have \<open>\<dots> m \<le> normF F (\<lambda>a. x m a - l a)\<close> if \<open>m \<ge> I \<epsilon>\<close> for m
      using normF_xx[OF \<open>finite F\<close> \<open>\<epsilon>>0\<close> \<open>n \<ge> I \<epsilon>\<close> \<open>m \<ge> I \<epsilon>\<close>]
      by auto
    also have \<open>(\<lambda>m. \<dots> m) \<longlonglongrightarrow> 0\<close>
      using \<open>finite F\<close> by (rule normF_xl_lim)
    finally show ?thesis
      by auto
  qed
  have \<open>normF F l \<le> 1 + normF F (x (I 1))\<close> if [simp]: \<open>finite F\<close> for F
    using normF_xl[where F=F and \<epsilon>=1 and n=\<open>I 1\<close>]
    using normF_triangle[where F=F and x=\<open>x (I 1)\<close> and y=\<open>\<lambda>a. l a - x (I 1) a\<close>]
    using normF_negate[where F=F and x=\<open>(\<lambda>a. x (I 1) a - l a)\<close>]
    by auto
  also have \<open>\<dots> F \<le> 1 + ell2_norm (x (I 1))\<close> if \<open>finite F\<close> for F
    using normF_ell2norm that by simp
  finally have [simp]: \<open>has_ell2_norm l\<close>
    unfolding has_ell2_norm_L2_set
    by (auto intro!: bdd_aboveI simp flip: normF_def)
  then have \<open>l = Rep_ell2 L\<close>
    by (simp add: Abs_ell2_inverse L_def)
  have [simp]: \<open>has_ell2_norm (\<lambda>a. x n a - l a)\<close> for n
    apply (subst diff_conv_add_uminus)
    apply (rule ell2_norm_triangle)
    by (auto intro!: ell2_norm_uminus)
  from normF_xl have ell2norm_xl: \<open>ell2_norm (\<lambda>a. x n a - l a) \<le> \<epsilon>\<close>
    if \<open>n \<ge> I \<epsilon>\<close> and \<open>\<epsilon> > 0\<close> for n \<epsilon>
    apply (subst ell2_norm_L2_set)
    using that by (auto intro!: cSUP_least simp: normF_def)
  have \<open>norm (X n - L) \<le> \<epsilon>\<close> if \<open>n \<ge> I \<epsilon>\<close> and \<open>\<epsilon> > 0\<close> for n \<epsilon>
    using ell2norm_xl[OF that]
    by (simp add: x_def norm_ell2.rep_eq \<open>l = Rep_ell2 L\<close> minus_ell2.rep_eq)
  then have \<open>X \<longlonglongrightarrow> L\<close>
    unfolding tendsto_iff
    apply (auto simp: dist_norm eventually_sequentially)
    by (meson field_lbound_gt_zero le_less_trans)
  then show \<open>convergent X\<close>
    by (rule convergentI)
qed

instantiation ell2 :: (CARD_1) complex_algebra_1 
begin
lift_definition one_ell2 :: "'a ell2" is "\<lambda>_. 1" by simp
lift_definition times_ell2 :: "'a ell2 \<Rightarrow> 'a ell2 \<Rightarrow> 'a ell2" is "\<lambda>a b x. a x * b x"
  by simp   
instance 
proof
  fix a b c :: "'a ell2" and r :: complex
  show "a * b * c = a * (b * c)"
    by (transfer, auto)
  show "(a + b) * c = a * c + b * c"
    apply (transfer, rule ext)
    by (simp add: distrib_left mult.commute)
  show "a * (b + c) = a * b + a * c"
    apply transfer
    by (simp add: ring_class.ring_distribs(1))
  show "r *\<^sub>C a * b = r *\<^sub>C (a * b)"
    by (transfer, auto)
  show "(a::'a ell2) * r *\<^sub>C b = r *\<^sub>C (a * b)"
    by (transfer, auto)
  show "1 * a = a"
    by (transfer, rule ext, auto)
  show "a * 1 = a"
    by (transfer, rule ext, auto)
  show "(0::'a ell2) \<noteq> 1"
    apply transfer
    by (meson zero_neq_one)
qed
end

instantiation ell2 :: (CARD_1) field begin
lift_definition divide_ell2 :: "'a ell2 \<Rightarrow> 'a ell2 \<Rightarrow> 'a ell2" is "\<lambda>a b x. a x / b x"
  by simp   
lift_definition inverse_ell2 :: "'a ell2 \<Rightarrow> 'a ell2" is "\<lambda>a x. inverse (a x)"
  by simp
instance
proof (intro_classes; transfer)
  fix a :: "'a \<Rightarrow> complex"
  assume "a \<noteq> (\<lambda>_. 0)"
  then obtain y where ay: "a y \<noteq> 0"
    by auto
  show "(\<lambda>x. inverse (a x) * a x) = (\<lambda>_. 1)"
  proof (rule ext)
    fix x
    have "x = y"
      by auto
    with ay have "a x \<noteq> 0"
      by metis
    then show "inverse (a x) * a x = 1"
      by auto
  qed
qed (auto simp add: divide_complex_def mult.commute ring_class.ring_distribs)
end


subsection \<open>Orthogonality\<close>

lemma ell2_pointwise_ortho:
  assumes \<open>\<And> i. Rep_ell2 x i = 0 \<or> Rep_ell2 y i = 0\<close>
  shows \<open>is_orthogonal x y\<close>
  using assms apply transfer
  by (simp add: infsum_0)

subsection \<open>Truncated vectors\<close>

lift_definition trunc_ell2:: \<open>'a set \<Rightarrow> 'a ell2 \<Rightarrow> 'a ell2\<close>
  is \<open>\<lambda> S x. (\<lambda> i. (if i \<in> S then x i else 0))\<close>
proof (rename_tac S x)
  fix x :: \<open>'a \<Rightarrow> complex\<close> and S :: \<open>'a set\<close>
  assume \<open>has_ell2_norm x\<close>
  then have \<open>(\<lambda>i. (x i)\<^sup>2) abs_summable_on UNIV\<close>
    unfolding has_ell2_norm_def by -
  then have \<open>(\<lambda>i. (x i)\<^sup>2) abs_summable_on S\<close>
    using summable_on_subset_banach by blast
  then have \<open>(\<lambda>xa. (if xa \<in> S then x xa else 0)\<^sup>2) abs_summable_on UNIV\<close>
    apply (rule summable_on_cong_neutral[THEN iffD1, rotated -1])
    by auto
  then show \<open>has_ell2_norm (\<lambda>i. if i \<in> S then x i else 0)\<close>
    unfolding has_ell2_norm_def by -
qed

lemma trunc_ell2_empty[simp]: \<open>trunc_ell2 {} x = 0\<close>
  apply transfer by simp

lemma norm_id_minus_trunc_ell2:
  \<open>(norm (x - trunc_ell2 S x))^2 = (norm x)^2 - (norm (trunc_ell2 S x))^2\<close>
proof-
  have \<open>Rep_ell2 (trunc_ell2 S x) i = 0 \<or> Rep_ell2 (x - trunc_ell2 S x) i = 0\<close> for i
    apply transfer
    by auto
  hence \<open>\<langle> (trunc_ell2 S x), (x - trunc_ell2 S x) \<rangle> = 0\<close>
    using ell2_pointwise_ortho by blast
  hence \<open>(norm x)^2 = (norm (trunc_ell2 S x))^2 + (norm (x - trunc_ell2 S x))^2\<close>
    using pythagorean_theorem by fastforce    
  thus ?thesis by simp
qed

lemma norm_trunc_ell2_finite:
  \<open>finite S \<Longrightarrow> (norm (trunc_ell2 S x)) = sqrt ((sum (\<lambda>i. (cmod (Rep_ell2 x i))\<^sup>2)) S)\<close>
proof-
  assume \<open>finite S\<close>
  moreover have \<open>\<And> i. i \<notin> S \<Longrightarrow> Rep_ell2 ((trunc_ell2 S x)) i = 0\<close>
    by (simp add: trunc_ell2.rep_eq)    
  ultimately have \<open>(norm (trunc_ell2 S x)) = sqrt ((sum (\<lambda>i. (cmod (Rep_ell2 ((trunc_ell2 S x)) i))\<^sup>2)) S)\<close>
    using ell2_norm_finite_support
    by blast 
  moreover have \<open>\<And> i. i \<in> S \<Longrightarrow> Rep_ell2 ((trunc_ell2 S x)) i = Rep_ell2 x i\<close>
    by (simp add: trunc_ell2.rep_eq)
  ultimately show ?thesis by simp
qed

lemma trunc_ell2_lim_at_UNIV:
  \<open>((\<lambda>S. trunc_ell2 S \<psi>) \<longlongrightarrow> \<psi>) (finite_subsets_at_top UNIV)\<close>
proof -
  define f where \<open>f i = (cmod (Rep_ell2 \<psi> i))\<^sup>2\<close> for i

  have has: \<open>has_ell2_norm (Rep_ell2 \<psi>)\<close>
    using Rep_ell2 by blast
  then have summable: "f abs_summable_on UNIV"
    by (smt (verit, del_insts) f_def has_ell2_norm_def norm_ge_zero norm_power real_norm_def summable_on_cong)

  have \<open>norm \<psi> = (ell2_norm (Rep_ell2 \<psi>))\<close>
    apply transfer by simp
  also have \<open>\<dots> = sqrt (infsum f UNIV)\<close>
    by (simp add: ell2_norm_def f_def[symmetric])
  finally have norm\<psi>: \<open>norm \<psi> = sqrt (infsum f UNIV)\<close>
    by -

  have norm_trunc: \<open>norm (trunc_ell2 S \<psi>) = sqrt (sum f S)\<close> if \<open>finite S\<close> for S
    using f_def that norm_trunc_ell2_finite by fastforce

  have \<open>(sum f \<longlongrightarrow> infsum f UNIV) (finite_subsets_at_top UNIV)\<close>
    using f_def[abs_def] infsum_tendsto local.summable by fastforce
  then have \<open>((\<lambda>S. sqrt (sum f S)) \<longlongrightarrow> sqrt (infsum f UNIV)) (finite_subsets_at_top UNIV)\<close>
    using tendsto_real_sqrt by blast
  then have \<open>((\<lambda>S. norm (trunc_ell2 S \<psi>)) \<longlongrightarrow> norm \<psi>) (finite_subsets_at_top UNIV)\<close>
    apply (subst tendsto_cong[where g=\<open>\<lambda>S. sqrt (sum f S)\<close>])
    by (auto simp add: eventually_finite_subsets_at_top_weakI norm_trunc norm\<psi>)
  then have \<open>((\<lambda>S. (norm (trunc_ell2 S \<psi>))\<^sup>2) \<longlongrightarrow> (norm \<psi>)\<^sup>2) (finite_subsets_at_top UNIV)\<close>
    by (simp add: tendsto_power)
  then have \<open>((\<lambda>S. (norm \<psi>)\<^sup>2 - (norm (trunc_ell2 S \<psi>))\<^sup>2) \<longlongrightarrow> 0) (finite_subsets_at_top UNIV)\<close>
    apply (rule tendsto_diff[where a=\<open>(norm \<psi>)^2\<close> and b=\<open>(norm \<psi>)^2\<close>, simplified, rotated])
    by auto
  then have \<open>((\<lambda>S. (norm (\<psi> - trunc_ell2 S \<psi>))\<^sup>2) \<longlongrightarrow> 0) (finite_subsets_at_top UNIV)\<close>
    unfolding norm_id_minus_trunc_ell2 by simp
  then have \<open>((\<lambda>S. norm (\<psi> - trunc_ell2 S \<psi>)) \<longlongrightarrow> 0) (finite_subsets_at_top UNIV)\<close>
    by auto
  then have \<open>((\<lambda>S. \<psi> - trunc_ell2 S \<psi>) \<longlongrightarrow> 0) (finite_subsets_at_top UNIV)\<close>
    by (rule tendsto_norm_zero_cancel)
  then show ?thesis
    apply (rule Lim_transform2[where f=\<open>\<lambda>_. \<psi>\<close>, rotated])
    by simp
qed

subsection \<open>Kets and bras\<close>

lift_definition ket :: "'a \<Rightarrow> 'a ell2" is "\<lambda>x y. if x=y then 1 else 0"
  by (rule has_ell2_norm_ket)

abbreviation bra :: "'a \<Rightarrow> (_,complex) cblinfun" where "bra i \<equiv> vector_to_cblinfun (ket i)*" for i

instance ell2 :: (type) not_singleton
proof standard
  have "ket undefined \<noteq> (0::'a ell2)"
  proof transfer
    show "(\<lambda>y. if (undefined::'a) = y then 1::complex else 0) \<noteq> (\<lambda>_. 0)"
      by (meson one_neq_zero)
  qed   
  thus \<open>\<exists>x y::'a ell2. x \<noteq> y\<close>
    by blast    
qed

lemma cinner_ket_left: \<open>\<langle>ket i, \<psi>\<rangle> = Rep_ell2 \<psi> i\<close>
  apply (transfer fixing: i)
  apply (subst infsum_cong_neutral[where T=\<open>{i}\<close>])
  by auto

lemma cinner_ket_right: \<open>\<langle>\<psi>, ket i\<rangle> = cnj (Rep_ell2 \<psi> i)\<close>
  apply (transfer fixing: i)
  apply (subst infsum_cong_neutral[where T=\<open>{i}\<close>])
  by auto

lemma cinner_ket_eqI:
  assumes \<open>\<And>i. cinner (ket i) \<psi> = cinner (ket i) \<phi>\<close>
  shows \<open>\<psi> = \<phi>\<close>
  by (metis Rep_ell2_inject assms cinner_ket_left ext)

lemma norm_ket[simp]: "norm (ket i) = 1"
  apply transfer by (rule ell2_norm_ket)

lemma cinner_ket_same[simp]:
  \<open>\<langle>ket i, ket i\<rangle> = 1\<close>
proof-
  have \<open>norm (ket i) = 1\<close>
    by simp
  hence \<open>sqrt (cmod \<langle>ket i, ket i\<rangle>) = 1\<close>
    by (metis norm_eq_sqrt_cinner)
  hence \<open>cmod \<langle>ket i, ket i\<rangle> = 1\<close>
    using real_sqrt_eq_1_iff by blast
  moreover have \<open>\<langle>ket i, ket i\<rangle> = cmod \<langle>ket i, ket i\<rangle>\<close>
  proof-
    have \<open>\<langle>ket i, ket i\<rangle> \<in> \<real>\<close>
      by (simp add: cinner_real)      
    thus ?thesis 
      by (metis cinner_ge_zero complex_of_real_cmod) 
  qed
  ultimately show ?thesis by simp
qed

lemma orthogonal_ket[simp]:
  \<open>is_orthogonal (ket i) (ket j) \<longleftrightarrow> i \<noteq> j\<close>
  by (simp add: cinner_ket_left ket.rep_eq)

lemma cinner_ket: \<open>\<langle>ket i, ket j\<rangle> = (if i=j then 1 else 0)\<close>
  by (simp add: cinner_ket_left ket.rep_eq)

lemma ket_injective[simp]: \<open>ket i = ket j \<longleftrightarrow> i = j\<close>
  by (metis cinner_ket one_neq_zero)

lemma inj_ket[simp]: \<open>inj ket\<close>
  by (simp add: inj_on_def)


lemma trunc_ell2_ket_cspan:
  \<open>trunc_ell2 S x \<in> (cspan (range ket))\<close> if \<open>finite S\<close>
proof (use that in induction)
  case empty
  then show ?case 
    by (auto intro: complex_vector.span_zero)
next
  case (insert a F)
  from insert.hyps have \<open>trunc_ell2 (insert a F) x = trunc_ell2 F x + Rep_ell2 x a *\<^sub>C ket a\<close>
    apply (transfer fixing: F a)
    by auto
  with insert.IH
  show ?case
    by (simp add: complex_vector.span_add_eq complex_vector.span_base complex_vector.span_scale)
qed

lemma closed_cspan_range_ket[simp]:
  \<open>closure (cspan (range ket)) = UNIV\<close>
proof (intro set_eqI iffI UNIV_I closure_approachable[THEN iffD2] allI impI)
  fix \<psi> :: \<open>'a ell2\<close>
  fix e :: real assume \<open>e > 0\<close>
  have \<open>((\<lambda>S. trunc_ell2 S \<psi>) \<longlongrightarrow> \<psi>) (finite_subsets_at_top UNIV)\<close>
    by (rule trunc_ell2_lim_at_UNIV)
  then obtain F where \<open>finite F\<close> and \<open>dist (trunc_ell2 F \<psi>) \<psi> < e\<close>
    apply (drule_tac tendstoD[OF _ \<open>e > 0\<close>])
    by (auto dest: simp: eventually_finite_subsets_at_top)
  moreover have \<open>trunc_ell2 F \<psi> \<in> cspan (range ket)\<close>
    using \<open>finite F\<close> trunc_ell2_ket_cspan by blast
  ultimately show \<open>\<exists>\<phi>\<in>cspan (range ket). dist \<phi> \<psi> < e\<close>
    by auto
qed

lemma ccspan_range_ket[simp]: "ccspan (range ket) = (top::('a ell2 ccsubspace))"
proof-
  have \<open>closure (complex_vector.span (range ket)) = (UNIV::'a ell2 set)\<close>
    using Complex_L2.closed_cspan_range_ket by blast
  thus ?thesis
    by (simp add: ccspan.abs_eq top_ccsubspace.abs_eq)
qed

lemma cspan_range_ket_finite[simp]: "cspan (range ket :: 'a::finite ell2 set) = UNIV"
  by (metis closed_cspan_range_ket closure_finite_cspan finite_class.finite_UNIV finite_imageI)

instance ell2 :: (finite) cfinite_dim
proof
  define basis :: \<open>'a ell2 set\<close> where \<open>basis = range ket\<close>
  have \<open>finite basis\<close>
    unfolding basis_def by simp
  moreover have \<open>cspan basis = UNIV\<close>
    by (simp add: basis_def)
  ultimately show \<open>\<exists>basis::'a ell2 set. finite basis \<and> cspan basis = UNIV\<close>
    by auto
qed

instantiation ell2 :: (enum) onb_enum begin
definition "canonical_basis_ell2 = map ket Enum.enum"
instance
proof
  show "distinct (canonical_basis::'a ell2 list)"
  proof-
    have \<open>finite (UNIV::'a set)\<close>
      by simp
    have \<open>distinct (enum_class.enum::'a list)\<close>
      using enum_distinct by blast
    moreover have \<open>inj_on ket (set enum_class.enum)\<close>
      by (meson inj_onI ket_injective)         
    ultimately show ?thesis
      unfolding canonical_basis_ell2_def
      using distinct_map
      by blast
  qed    

  show "is_ortho_set (set (canonical_basis::'a ell2 list))"
    apply (auto simp: canonical_basis_ell2_def enum_UNIV)
    by (smt (z3) norm_ket f_inv_into_f is_ortho_set_def orthogonal_ket norm_zero)

  show "cindependent (set (canonical_basis::'a ell2 list))"
    apply (auto simp: canonical_basis_ell2_def enum_UNIV)
    by (smt (verit, best) norm_ket f_inv_into_f is_ortho_set_def is_ortho_set_cindependent orthogonal_ket norm_zero)

  show "cspan (set (canonical_basis::'a ell2 list)) = UNIV"
    by (auto simp: canonical_basis_ell2_def enum_UNIV)

  show "norm (x::'a ell2) = 1"
    if "(x::'a ell2) \<in> set canonical_basis"
    for x :: "'a ell2"
    using that unfolding canonical_basis_ell2_def 
    by auto
qed

end

lemma canonical_basis_length_ell2[code_unfold, simp]:
  "length (canonical_basis ::'a::enum ell2 list) = CARD('a)"
  unfolding canonical_basis_ell2_def apply simp
  using card_UNIV_length_enum by metis

lemma ket_canonical_basis: "ket x = canonical_basis ! enum_idx x"
proof-
  have "x = (enum_class.enum::'a list) ! enum_idx x"
    using enum_idx_correct[where i = x] by simp
  hence p1: "ket x = ket ((enum_class.enum::'a list) ! enum_idx x)"
    by simp
  have "enum_idx x < length (enum_class.enum::'a list)"
    using enum_idx_bound[where x = x].
  hence "(map ket (enum_class.enum::'a list)) ! enum_idx x 
        = ket ((enum_class.enum::'a list) ! enum_idx x)"
    by auto      
  thus ?thesis
    unfolding canonical_basis_ell2_def using p1 by auto    
qed

lemma clinear_equal_ket:
  fixes f g :: \<open>'a::finite ell2 \<Rightarrow> _\<close>
  assumes \<open>clinear f\<close>
  assumes \<open>clinear g\<close>
  assumes \<open>\<And>i. f (ket i) = g (ket i)\<close>
  shows \<open>f = g\<close>
  apply (rule ext)
  apply (rule complex_vector.linear_eq_on_span[where f=f and g=g and B=\<open>range ket\<close>])
  using assms by auto

lemma equal_ket:
  fixes A B :: \<open>('a ell2, 'b::complex_normed_vector) cblinfun\<close>
  assumes \<open>\<And> x. cblinfun_apply A (ket x) = cblinfun_apply B (ket x)\<close>
  shows \<open>A = B\<close>
  apply (rule cblinfun_eq_gen_eqI[where G=\<open>range ket\<close>])
  using assms by auto

lemma antilinear_equal_ket:
  fixes f g :: \<open>'a::finite ell2 \<Rightarrow> _\<close>
  assumes \<open>antilinear f\<close>
  assumes \<open>antilinear g\<close>
  assumes \<open>\<And>i. f (ket i) = g (ket i)\<close>
  shows \<open>f = g\<close>
proof -
  have [simp]: \<open>clinear (f \<circ> from_conjugate_space)\<close>
    apply (rule antilinear_o_antilinear)
    using assms by (simp_all add: antilinear_from_conjugate_space)
  have [simp]: \<open>clinear (g \<circ> from_conjugate_space)\<close>
    apply (rule antilinear_o_antilinear)
    using assms by (simp_all add: antilinear_from_conjugate_space)
  have [simp]: \<open>cspan (to_conjugate_space ` (range ket :: 'a ell2 set)) = UNIV\<close>
    by simp
  have "f o from_conjugate_space = g o from_conjugate_space"
    apply (rule ext)
    apply (rule complex_vector.linear_eq_on_span[where f="f o from_conjugate_space" and g="g o from_conjugate_space" and B=\<open>to_conjugate_space ` range ket\<close>])
       apply (simp, simp)
    using assms(3) by (auto simp: to_conjugate_space_inverse)
  then show "f = g"
    by (smt (verit) UNIV_I from_conjugate_space_inverse surj_def surj_fun_eq to_conjugate_space_inject) 
qed

lemma cinner_ket_adjointI:
  fixes F::"'a ell2 \<Rightarrow>\<^sub>C\<^sub>L _" and G::"'b ell2 \<Rightarrow>\<^sub>C\<^sub>L_"
  assumes "\<And> i j. \<langle>F *\<^sub>V ket i, ket j\<rangle> = \<langle>ket i, G *\<^sub>V ket j\<rangle>"
  shows "F = G*"
proof -
  from assms
  have \<open>(F *\<^sub>V x) \<bullet>\<^sub>C y = x \<bullet>\<^sub>C (G *\<^sub>V y)\<close> if \<open>x \<in> range ket\<close> and \<open>y \<in> range ket\<close> for x y
    using that by auto
  then have \<open>(F *\<^sub>V x) \<bullet>\<^sub>C y = x \<bullet>\<^sub>C (G *\<^sub>V y)\<close> if \<open>x \<in> range ket\<close> for x y
    apply (rule bounded_clinear_eq_on[where G=\<open>range ket\<close> and t=y, rotated 2])
    using that by (auto intro!: bounded_linear_intros)
  then have \<open>(F *\<^sub>V x) \<bullet>\<^sub>C y = x \<bullet>\<^sub>C (G *\<^sub>V y)\<close> for x y
    apply (rule bounded_antilinear_eq_on[where G=\<open>range ket\<close> and t=x, rotated 2])
    by (auto intro!: bounded_linear_intros)
  then show ?thesis
    by (rule adjoint_eqI)
qed

lemma ket_nonzero[simp]: "ket i \<noteq> 0"
  using norm_ket[of i] by force


lemma cindependent_ket:
  "cindependent (range (ket::'a\<Rightarrow>_))"
proof-
  define S where "S = range (ket::'a\<Rightarrow>_)"
  have "is_ortho_set S"
    unfolding S_def is_ortho_set_def by auto
  moreover have "0 \<notin> S"
    unfolding S_def
    using ket_nonzero
    by (simp add: image_iff)
  ultimately show ?thesis
    using is_ortho_set_cindependent[where A = S] unfolding S_def 
    by blast
qed

lemma cdim_UNIV_ell2[simp]: \<open>cdim (UNIV::'a::finite ell2 set) = CARD('a)\<close>
  apply (subst cspan_range_ket_finite[symmetric])
  by (metis card_image cindependent_ket complex_vector.dim_span_eq_card_independent inj_ket)

lemma is_ortho_set_ket[simp]: \<open>is_ortho_set (range ket)\<close>
  using is_ortho_set_def by fastforce

subsection \<open>Butterflies\<close>

lemma cspan_butterfly_ket: \<open>cspan {butterfly (ket i) (ket j)| (i::'b::finite) (j::'a::finite). True} = UNIV\<close>
proof -
  have *: \<open>{butterfly (ket i) (ket j)| (i::'b::finite) (j::'a::finite). True} = {butterfly a b |a b. a \<in> range ket \<and> b \<in> range ket}\<close>
    by auto
  show ?thesis
    apply (subst *)
    apply (rule cspan_butterfly_UNIV)
    by auto
qed

lemma cindependent_butterfly_ket: \<open>cindependent {butterfly (ket i) (ket j)| (i::'b) (j::'a). True}\<close>
proof -
  have *: \<open>{butterfly (ket i) (ket j)| (i::'b) (j::'a). True} = {butterfly a b |a b. a \<in> range ket \<and> b \<in> range ket}\<close>
    by auto
  show ?thesis
    apply (subst *)
    apply (rule cindependent_butterfly)
    by auto
qed

lemma clinear_eq_butterfly_ketI:
  fixes F G :: \<open>('a::finite ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b::finite ell2) \<Rightarrow> 'c::complex_vector\<close>
  assumes "clinear F" and "clinear G"
  assumes "\<And>i j. F (butterfly (ket i) (ket j)) = G (butterfly (ket i) (ket j))"
  shows "F = G"
  apply (rule complex_vector.linear_eq_on_span[where f=F, THEN ext, rotated 3])
     apply (subst cspan_butterfly_ket)
  using assms by auto

lemma sum_butterfly_ket[simp]: \<open>(\<Sum>(i::'a::finite)\<in>UNIV. butterfly (ket i) (ket i)) = id_cblinfun\<close>
  apply (rule equal_ket)
  apply (subst complex_vector.linear_sum[where f=\<open>\<lambda>y. y *\<^sub>V ket _\<close>])
   apply (auto simp add: scaleC_cblinfun.rep_eq cblinfun.add_left clinearI butterfly_def cblinfun_compose_image cinner_ket)
  apply (subst sum.mono_neutral_cong_right[where S=\<open>{_}\<close>])
  by auto

subsection \<open>One-dimensional spaces\<close>

instantiation ell2 :: ("{enum,CARD_1}") one_dim begin
text \<open>Note: enum is not needed logically, but without it this instantiation
            clashes with \<open>instantiation ell2 :: (enum) onb_enum\<close>\<close>
instance
proof
  show "canonical_basis = [1::'a ell2]"
    unfolding canonical_basis_ell2_def
    apply transfer
    by (simp add: enum_CARD_1[of undefined])
  show "a *\<^sub>C 1 * b *\<^sub>C 1 = (a * b) *\<^sub>C (1::'a ell2)" for a b
    apply (transfer fixing: a b) by simp
  show "x / y = x * inverse y" for x y :: "'a ell2"
    by (simp add: divide_inverse)
  show "inverse (c *\<^sub>C 1) = inverse c *\<^sub>C (1::'a ell2)" for c :: complex
    apply transfer by auto
qed
end


subsection \<open>Classical operators\<close>

text \<open>We call an operator mapping \<^term>\<open>ket x\<close> to \<^term>\<open>ket (\<pi> x)\<close> or \<^term>\<open>0\<close> "classical".
(The meaning is inspired by the fact that in quantum mechanics, such operators usually correspond
to operations with classical interpretation (such as Pauli-X, CNOT, measurement in the computational
basis, etc.))\<close>

definition classical_operator :: "('a\<Rightarrow>'b option) \<Rightarrow> 'a ell2 \<Rightarrow>\<^sub>C\<^sub>L'b ell2" where
  "classical_operator \<pi> = 
    (let f = (\<lambda>t. (case \<pi> (inv (ket::'a\<Rightarrow>_) t) 
                           of None \<Rightarrow> (0::'b ell2) 
                          | Some i \<Rightarrow> ket i))
     in
      cblinfun_extension (range (ket::'a\<Rightarrow>_)) f)"


definition "classical_operator_exists \<pi> \<longleftrightarrow>
  cblinfun_extension_exists (range ket)
    (\<lambda>t. case \<pi> (inv ket t) of None \<Rightarrow> 0 | Some i \<Rightarrow> ket i)"

lemma classical_operator_existsI:
  assumes "\<And>x. B *\<^sub>V (ket x) = (case \<pi> x of Some i \<Rightarrow> ket i | None \<Rightarrow> 0)"
  shows "classical_operator_exists \<pi>"
  unfolding classical_operator_exists_def
  apply (rule cblinfun_extension_existsI[of _ B])
  using assms 
  by (auto simp: inv_f_f[OF inj_ket])

lemma classical_operator_exists_inj:
  assumes "inj_map \<pi>"
  shows "classical_operator_exists \<pi>"
proof -
  define f where \<open>f t = (case \<pi> (inv ket t) of None \<Rightarrow> 0 | Some x \<Rightarrow> ket x)\<close> for t
  define g where \<open>g = cconstruct (range ket) f\<close>
  have g_f: \<open>g (ket x) = f (ket x)\<close> for x
    unfolding g_def apply (rule complex_vector.construct_basis)
    using cindependent_ket by auto
  have \<open>clinear g\<close>
    unfolding g_def apply (rule complex_vector.linear_construct)
    using cindependent_ket by blast
  then have \<open>g (x + y) = g x + g y\<close> if \<open>x \<in> cspan (range ket)\<close> and \<open>y \<in> cspan (range ket)\<close> for x y
    using clinear_iff by blast
  moreover from \<open>clinear g\<close> have \<open>g (c *\<^sub>C x) = c *\<^sub>C g x\<close> if \<open>x \<in> cspan (range ket)\<close> for x c
    by (simp add: complex_vector.linear_scale)
  moreover have \<open>norm (g x) \<le> norm x\<close> if \<open>x \<in> cspan (range ket)\<close> for x
  proof -
    from that obtain t r where x_sum: \<open>x = (\<Sum>a\<in>t. r a *\<^sub>C a)\<close> and \<open>finite t\<close> and \<open>t \<subseteq> range ket\<close>
      unfolding complex_vector.span_explicit by auto
    then obtain T where tT: \<open>t = ket ` T\<close> and [simp]: \<open>finite T\<close>
      by (meson finite_subset_image)
    define R where \<open>R i = r (ket i)\<close> for i
    have x_sum: \<open>x = (\<Sum>i\<in>T. R i *\<^sub>C ket i)\<close>
      unfolding R_def tT x_sum
      apply (rule sum.reindex_cong)
      by (auto simp add: inj_on_def)

    define T' \<pi>' \<pi>T \<pi>R where \<open>T' = {i\<in>T. \<pi> i \<noteq> None}\<close> and \<open>\<pi>' = the o \<pi>\<close> and \<open>\<pi>T = \<pi>' ` T'\<close> and \<open>\<pi>R i = R (inv_into T' \<pi>' i)\<close> for i
    have \<open>inj_on \<pi>' T'\<close>
      by (smt (z3) T'_def \<pi>'_def assms comp_apply inj_map_def inj_on_def mem_Collect_eq option.expand)
    have [simp]: \<open>finite \<pi>T\<close>
      by (simp add: T'_def \<pi>T_def)

    have \<open>g x = (\<Sum>i\<in>T. R i *\<^sub>C g (ket i))\<close>
      by (smt (verit, ccfv_threshold) \<open>clinear g\<close> complex_vector.linear_scale complex_vector.linear_sum sum.cong x_sum)
    also have \<open>\<dots> = (\<Sum>i\<in>T. R i *\<^sub>C f (ket i))\<close>
      using g_f by presburger
    also have \<open>\<dots> = (\<Sum>i\<in>T. R i *\<^sub>C (case \<pi> i of None \<Rightarrow> 0 | Some x \<Rightarrow> ket x))\<close>
      unfolding f_def by auto
    also have \<open>\<dots> = (\<Sum>i\<in>T'. R i *\<^sub>C ket (\<pi>' i))\<close>
      apply (rule sum.mono_neutral_cong_right)
      unfolding T'_def \<pi>'_def
      by auto
    also have \<open>\<dots> = (\<Sum>i\<in>\<pi>' ` T'. R (inv_into T' \<pi>' i) *\<^sub>C ket i)\<close>
      apply (subst sum.reindex)
      using \<open>inj_on \<pi>' T'\<close> apply assumption
      apply (rule sum.cong)
      using \<open>inj_on \<pi>' T'\<close> by auto
    finally have gx_sum: \<open>g x = (\<Sum>i\<in>\<pi>T. \<pi>R i *\<^sub>C ket i)\<close>
      using \<pi>R_def \<pi>T_def by auto

    have \<open>(norm (g x))\<^sup>2 = (\<Sum>a\<in>\<pi>T. (cmod (\<pi>R a))\<^sup>2)\<close>
      unfolding gx_sum 
      apply (subst pythagorean_theorem_sum)
      by auto
    also have \<open>\<dots> = (\<Sum>i\<in>T'. (cmod (R i))\<^sup>2)\<close>
      unfolding \<pi>R_def \<pi>T_def
      apply (subst sum.reindex)
      using \<open>inj_on \<pi>' T'\<close> apply assumption
      apply (rule sum.cong)
      using \<open>inj_on \<pi>' T'\<close> by auto
    also have \<open>\<dots> \<le> (\<Sum>a\<in>T. (cmod (R a))\<^sup>2)\<close>
      apply (rule sum_mono2)
      using T'_def by auto
    also have \<open>\<dots> = (norm x)\<^sup>2\<close>
      unfolding x_sum 
      apply (subst pythagorean_theorem_sum)
      using \<open>finite T\<close> by auto
    finally show \<open>norm (g x) \<le> norm x\<close>
      by auto
  qed
  ultimately have \<open>cblinfun_extension_exists (cspan (range ket)) g\<close>
    apply (rule_tac cblinfun_extension_exists_bounded_dense[where B=1])
    by auto

  then have \<open>cblinfun_extension_exists (range ket) f\<close>
    by (metis (mono_tags, opaque_lifting) g_f cblinfun_extension_apply cblinfun_extension_existsI complex_vector.span_base rangeE)
  then show \<open>classical_operator_exists \<pi>\<close>
    unfolding classical_operator_exists_def f_def by simp
qed

lemma classical_operator_exists_finite[simp]: "classical_operator_exists (\<pi> :: _::finite \<Rightarrow> _)"
  unfolding classical_operator_exists_def
  apply (rule cblinfun_extension_exists_finite_dim)
  using cindependent_ket apply blast
  using finite_class.finite_UNIV finite_imageI closed_cspan_range_ket closure_finite_cspan by blast

lemma classical_operator_ket:
  assumes "classical_operator_exists \<pi>"
  shows "(classical_operator \<pi>) *\<^sub>V (ket x) = (case \<pi> x of Some i \<Rightarrow> ket i | None \<Rightarrow> 0)"
  unfolding classical_operator_def 
  using f_inv_into_f ket_injective rangeI
  by (metis assms cblinfun_extension_apply classical_operator_exists_def)

lemma classical_operator_ket_finite:
  "(classical_operator \<pi>) *\<^sub>V (ket (x::'a::finite)) = (case \<pi> x of Some i \<Rightarrow> ket i | None \<Rightarrow> 0)"
  by (rule classical_operator_ket, simp)

lemma classical_operator_adjoint[simp]:
  fixes \<pi> :: "'a \<Rightarrow> 'b option"
  assumes a1: "inj_map \<pi>"
  shows  "(classical_operator \<pi>)* = classical_operator (inv_map \<pi>)"
proof-
  define F where "F = classical_operator (inv_map \<pi>)"
  define G where "G = classical_operator \<pi>"
  have "\<langle>F *\<^sub>V ket i, ket j\<rangle> = \<langle>ket i, G *\<^sub>V ket j\<rangle>" for i j
  proof-
    have w1: "(classical_operator (inv_map \<pi>)) *\<^sub>V (ket i)
     = (case inv_map \<pi> i of Some k \<Rightarrow> ket k | None \<Rightarrow> 0)"
      by (simp add: classical_operator_ket classical_operator_exists_inj)
    have w2: "(classical_operator \<pi>) *\<^sub>V (ket j)
     = (case \<pi> j of Some k \<Rightarrow> ket k | None \<Rightarrow> 0)"
      by (simp add: assms classical_operator_ket classical_operator_exists_inj)
    have "\<langle>F *\<^sub>V ket i, ket j\<rangle> = \<langle>classical_operator (inv_map \<pi>) *\<^sub>V ket i, ket j\<rangle>"
      unfolding F_def by blast
    also have "\<dots> = \<langle>(case inv_map \<pi> i of Some k \<Rightarrow> ket k | None \<Rightarrow> 0), ket j\<rangle>"
      using w1 by simp
    also have "\<dots> = \<langle>ket i, (case \<pi> j of Some k \<Rightarrow> ket k | None \<Rightarrow> 0)\<rangle>"
    proof(induction "inv_map \<pi> i")
      case None
      hence pi1: "None = inv_map \<pi> i".
      show ?case 
      proof (induction "\<pi> j")
        case None
        thus ?case
          using pi1 by auto
      next
        case (Some c)
        have "c \<noteq> i"
        proof(rule classical)
          assume "\<not>(c \<noteq> i)"
          hence "c = i"
            by blast
          hence "inv_map \<pi> c = inv_map \<pi> i"
            by simp
          hence "inv_map \<pi> c = None"
            by (simp add: pi1)
          moreover have "inv_map \<pi> c = Some j"
            using Some.hyps unfolding inv_map_def
            apply auto
            by (metis a1 f_inv_into_f inj_map_def option.distinct(1) rangeI)
          ultimately show ?thesis by simp
        qed
        thus ?thesis
          by (metis None.hyps Some.hyps cinner_zero_left orthogonal_ket option.simps(4) 
              option.simps(5)) 
      qed       
    next
      case (Some d)
      hence s1: "Some d = inv_map \<pi> i".
      show "\<langle>case inv_map \<pi> i of 
            None \<Rightarrow> 0
        | Some a \<Rightarrow> ket a, ket j\<rangle> =
       \<langle>ket i, case \<pi> j of 
            None \<Rightarrow> 0 
        | Some a \<Rightarrow> ket a\<rangle>" 
      proof(induction "\<pi> j")
        case None
        have "d \<noteq> j"
        proof(rule classical)
          assume "\<not>(d \<noteq> j)"
          hence "d = j"
            by blast
          hence "\<pi> d = \<pi> j"
            by simp
          hence "\<pi> d = None"
            by (simp add: None.hyps)
          moreover have "\<pi> d = Some i"
            using Some.hyps unfolding inv_map_def
            apply auto
            by (metis f_inv_into_f option.distinct(1) option.inject)
          ultimately show ?thesis 
            by simp
        qed
        thus ?case
          by (metis None.hyps Some.hyps cinner_zero_right orthogonal_ket option.case_eq_if 
              option.simps(5)) 
      next
        case (Some c)
        hence s2: "\<pi> j = Some c" by simp
        have "\<langle>ket d, ket j\<rangle> = \<langle>ket i, ket c\<rangle>"
        proof(cases "\<pi> j = Some i")
          case True
          hence ij: "Some j = inv_map \<pi> i"
            unfolding inv_map_def apply auto
             apply (metis a1 f_inv_into_f inj_map_def option.discI range_eqI)
            by (metis range_eqI)
          have "i = c"
            using True s2 by auto
          moreover have "j = d"
            by (metis option.inject s1 ij)
          ultimately show ?thesis
            by (simp add: cinner_ket_same) 
        next
          case False
          moreover have "\<pi> d = Some i"
            using s1 unfolding inv_map_def
            by (metis f_inv_into_f option.distinct(1) option.inject)            
          ultimately have "j \<noteq> d"
            by auto            
          moreover have "i \<noteq> c"
            using False s2 by auto            
          ultimately show ?thesis
            by (metis orthogonal_ket) 
        qed
        hence "\<langle>case Some d of None \<Rightarrow> 0
        | Some a \<Rightarrow> ket a, ket j\<rangle> =
       \<langle>ket i, case Some c of None \<Rightarrow> 0 | Some a \<Rightarrow> ket a\<rangle>"
          by simp          
        thus "\<langle>case inv_map \<pi> i of None \<Rightarrow> 0
        | Some a \<Rightarrow> ket a, ket j\<rangle> =
       \<langle>ket i, case \<pi> j of None \<Rightarrow> 0 | Some a \<Rightarrow> ket a\<rangle>"
          by (simp add: Some.hyps s1)          
      qed
    qed
    also have "\<dots> = \<langle>ket i, classical_operator \<pi> *\<^sub>V ket j\<rangle>"
      by (simp add: w2)
    also have "\<dots> = \<langle>ket i, G *\<^sub>V ket j\<rangle>"
      unfolding G_def by blast
    finally show ?thesis .
  qed
  hence "G* = F"
    using cinner_ket_adjointI
    by auto
  thus ?thesis unfolding G_def F_def .
qed

lemma
  fixes \<pi>::"'b \<Rightarrow> 'c option" and \<rho>::"'a \<Rightarrow> 'b option"
  assumes "classical_operator_exists \<pi>"
  assumes "classical_operator_exists \<rho>"
  shows classical_operator_exists_comp[simp]: "classical_operator_exists (\<pi> \<circ>\<^sub>m \<rho>)"
    and classical_operator_mult[simp]: "classical_operator \<pi> o\<^sub>C\<^sub>L classical_operator \<rho> = classical_operator (\<pi> \<circ>\<^sub>m \<rho>)"
proof -
  define C\<pi> C\<rho> C\<pi>\<rho> where "C\<pi> = classical_operator \<pi>" and "C\<rho> = classical_operator \<rho>" 
    and "C\<pi>\<rho> = classical_operator (\<pi> \<circ>\<^sub>m \<rho>)"
  have C\<pi>x: "C\<pi> *\<^sub>V (ket x) = (case \<pi> x of Some i \<Rightarrow> ket i | None \<Rightarrow> 0)" for x
    unfolding C\<pi>_def using \<open>classical_operator_exists \<pi>\<close> by (rule classical_operator_ket)
  have C\<rho>x: "C\<rho> *\<^sub>V (ket x) = (case \<rho> x of Some i \<Rightarrow> ket i | None \<Rightarrow> 0)" for x
    unfolding C\<rho>_def using \<open>classical_operator_exists \<rho>\<close> by (rule classical_operator_ket)
  have C\<pi>\<rho>x': "(C\<pi> o\<^sub>C\<^sub>L C\<rho>) *\<^sub>V (ket x) = (case (\<pi> \<circ>\<^sub>m \<rho>) x of Some i \<Rightarrow> ket i | None \<Rightarrow> 0)" for x
    apply (simp add: scaleC_cblinfun.rep_eq C\<rho>x)
    apply (cases "\<rho> x")
    by (auto simp: C\<pi>x)
  thus \<open>classical_operator_exists (\<pi> \<circ>\<^sub>m \<rho>)\<close>
    by (rule classical_operator_existsI)
  hence "C\<pi>\<rho> *\<^sub>V (ket x) = (case (\<pi> \<circ>\<^sub>m \<rho>) x of Some i \<Rightarrow> ket i | None \<Rightarrow> 0)" for x
    unfolding C\<pi>\<rho>_def
    by (rule classical_operator_ket)
  with C\<pi>\<rho>x' have "(C\<pi> o\<^sub>C\<^sub>L C\<rho>) *\<^sub>V (ket x) = C\<pi>\<rho> *\<^sub>V (ket x)" for x
    by simp
  thus "C\<pi> o\<^sub>C\<^sub>L C\<rho> = C\<pi>\<rho>"
    by (simp add: equal_ket)
qed

lemma classical_operator_Some[simp]: "classical_operator (Some::'a\<Rightarrow>_) = id_cblinfun"
proof-
  have "(classical_operator Some) *\<^sub>V (ket i)  = id_cblinfun *\<^sub>V (ket i)"
    for i::'a
    apply (subst classical_operator_ket)
     apply (rule classical_operator_exists_inj)
    by auto
  thus ?thesis
    using equal_ket[where A = "classical_operator (Some::'a \<Rightarrow> _ option)"
        and B = "id_cblinfun::'a ell2 \<Rightarrow>\<^sub>C\<^sub>L _"]
    by blast
qed

lemma isometry_classical_operator[simp]:
  fixes \<pi>::"'a \<Rightarrow> 'b"
  assumes a1: "inj \<pi>"
  shows "isometry (classical_operator (Some o \<pi>))"
proof -
  have b0: "inj_map (Some \<circ> \<pi>)"
    by (simp add: a1)
  have b0': "inj_map (inv_map (Some \<circ> \<pi>))"
    by simp
  have b1: "inv_map (Some \<circ> \<pi>) \<circ>\<^sub>m (Some \<circ> \<pi>) = Some" 
    apply (rule ext) unfolding inv_map_def o_def 
    using assms unfolding inj_def inv_def by auto
  have b3: "classical_operator (inv_map (Some \<circ> \<pi>)) o\<^sub>C\<^sub>L
            classical_operator (Some \<circ> \<pi>) = classical_operator (inv_map (Some \<circ> \<pi>) \<circ>\<^sub>m (Some \<circ> \<pi>))"
    by (metis b0 b0' b1 classical_operator_Some classical_operator_exists_inj 
        classical_operator_mult)
  show ?thesis
    unfolding isometry_def
    apply (subst classical_operator_adjoint)
    using b0 by (auto simp add: b1 b3)
qed

lemma unitary_classical_operator[simp]:
  fixes \<pi>::"'a \<Rightarrow> 'b"
  assumes a1: "bij \<pi>"
  shows "unitary (classical_operator (Some o \<pi>))"
proof (unfold unitary_def, rule conjI)
  have "inj \<pi>"
    using a1 bij_betw_imp_inj_on by auto
  hence "isometry (classical_operator (Some o \<pi>))"
    by simp
  hence "classical_operator (Some \<circ> \<pi>)* o\<^sub>C\<^sub>L classical_operator (Some \<circ> \<pi>) = id_cblinfun"
    unfolding isometry_def by simp
  thus \<open>classical_operator (Some \<circ> \<pi>)* o\<^sub>C\<^sub>L classical_operator (Some \<circ> \<pi>) = id_cblinfun\<close>
    by simp 
next
  have "inj \<pi>"
    by (simp add: assms bij_is_inj)
  have comp: "Some \<circ> \<pi> \<circ>\<^sub>m inv_map (Some \<circ> \<pi>) = Some"
    apply (rule ext)
    unfolding inv_map_def o_def map_comp_def
    unfolding inv_def apply auto
     apply (metis \<open>inj \<pi>\<close> inv_def inv_f_f)
    using bij_def image_iff range_eqI
    by (metis a1)
  have "classical_operator (Some \<circ> \<pi>) o\<^sub>C\<^sub>L classical_operator (Some \<circ> \<pi>)*
      = classical_operator (Some \<circ> \<pi>) o\<^sub>C\<^sub>L classical_operator (inv_map (Some \<circ> \<pi>))"
    by (simp add: \<open>inj \<pi>\<close>)
  also have "\<dots> = classical_operator ((Some \<circ> \<pi>) \<circ>\<^sub>m (inv_map (Some \<circ> \<pi>)))"
    by (simp add: \<open>inj \<pi>\<close> classical_operator_exists_inj)
  also have "\<dots> = classical_operator (Some::'b\<Rightarrow>_)"
    using comp
    by simp 
  also have "\<dots> = (id_cblinfun:: 'b ell2 \<Rightarrow>\<^sub>C\<^sub>L _)"
    by simp
  finally show "classical_operator (Some \<circ> \<pi>) o\<^sub>C\<^sub>L classical_operator (Some \<circ> \<pi>)* = id_cblinfun".
qed



unbundle no_cblinfun_notation

end
