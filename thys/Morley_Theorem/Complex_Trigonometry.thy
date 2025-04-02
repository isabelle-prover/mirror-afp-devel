theory Complex_Trigonometry

imports  "HOL-Analysis.Convex"  Complex_Angles Complex_Triangles_Definitions

begin 

section \<open>Complex trigonometry\<close>
text \<open>In this section we add some trigonometric results, especially the law of sines\<close>
lemma ang_sin:
  shows\<open>Im ((b-a)*cnj(c-a)) = cmod (c-a) *cmod (b-a) * sin (angle_c c a b)\<close>
proof -
  have f0:\<open>sin (Arg (cnj c - cnj a)) = - sin (Arg ( c - a))\<close>
    by (metis arg_cnj_not_pi arg_cnj_pi complex_cnj_diff neg_0_equal_iff_equal sin_minus
        sin_pi)
  have f1:\<open>cos (Arg (cnj c - cnj a)) = cos (Arg (c - a))\<close>
    by (metis arg_cnj_not_pi arg_cnj_pi complex_cnj_diff cos_minus)
  then have \<open>b-a = cmod (b-a) * cis (Arg (b-a)) \<and> cnj (c-a) = cmod (c-a) * cis (Arg (cnj (c-a)))\<close>
    using rcis_cmod_Arg rcis_def 
    by (metis complex_mod_cnj)
  then have \<open>Im(cis (Arg (b-a)) * cis (Arg (cnj(c-a)))) = sin (angle_c c a b)\<close>
    unfolding ang_vec_def angle_c_def using f1 f0 by(auto simp:cis.code sin_diff) 
  then have \<open>Im (cmod (b-a) * cis (Arg (b-a)) * cmod (c-a) * cis (Arg (cnj (c-a)))) =
      cmod (c-a) *cmod (b-a) * sin (angle_c c a b) \<close>
    by (metis Im_complex_of_real[of "cmod (c - a)"] Im_complex_of_real[of "cmod (b - a)"]
        Im_mult_real[of "cor (cmod (c - a))"
          "cis (Arg (cnj (c - a))) * (cor (cmod (b - a)) * cis (Arg (b - a)))"]
        Im_mult_real[of "cor (cmod (b - a))" "cis (Arg (b - a)) * cis (Arg (cnj (c - a)))"]
        Re_complex_of_real[of "cmod (c - a)"] Re_complex_of_real[of "cmod (b - a)"]
        ab_semigroup_mult_class.mult_ac(1)[of "cor (cmod (b - a))" "cis (Arg (b - a))"
          "cis (Arg (cnj (c - a)))"]
        ab_semigroup_mult_class.mult_ac(1)[of "cis (Arg (cnj (c - a)))"
          "cor (cmod (b - a)) * cis (Arg (b - a))" "cor (cmod (c - a))"]
        ab_semigroup_mult_class.mult_ac(1)[of "cmod (c - a)" "cmod (b - a)"
          "Im (cis (Arg (b - a)) * cis (Arg (cnj (c - a))))"]
        mult.commute[of "cis (Arg (cnj (c - a)))" "cor (cmod (b - a)) * cis (Arg (b - a))"]
        mult.commute[of "cis (Arg (cnj (c - a))) * (cor (cmod (b - a)) * cis (Arg (b - a)))"
          "cor (cmod (c - a))"]
        mult.commute[of "cor (cmod (b - a)) * cis (Arg (b - a)) * cor (cmod (c - a))"
          "cis (Arg (cnj (c - a)))"])
  then show \<open>Im ((b - a) * cnj (c - a)) = cmod (c - a) * cmod (b - a) * sin (angle_c c a b)\<close> 
    by (metis \<open>b - a = cor (cmod (b - a)) * cis (Arg (b - a)) \<and> cnj (c - a) = cor (cmod (c - a)) * cis (Arg (cnj (c - a)))\<close> 
ab_semigroup_mult_class.mult_ac(1))
qed

lemma ang_cos:
  shows\<open>Re ((b-a)*cnj(c-a)) = cmod (c-a) *cmod (b-a) * cos (angle_c c a b)\<close>
proof -
  have f0:\<open>sin (Arg (cnj c - cnj a)) = - sin (Arg ( c - a))\<close>
    by (metis arg_cnj_not_pi arg_cnj_pi complex_cnj_diff neg_0_equal_iff_equal sin_minus
        sin_pi)
  have f1:\<open>cos (Arg (cnj c - cnj a)) = cos (Arg (c - a))\<close>
    by (metis arg_cnj_not_pi arg_cnj_pi complex_cnj_diff cos_minus)
  then have f2:\<open>b-a = cmod (b-a) * cis (Arg (b-a)) \<and> cnj (c-a) = cmod (c-a) * cis (Arg (cnj (c-a)))\<close>
    using rcis_cmod_Arg rcis_def 
    by (metis complex_mod_cnj)
  then have \<open>Re(cis (Arg (b-a)) * cis (Arg (cnj(c-a)))) = cos (angle_c c a b)\<close>
    unfolding ang_vec_def angle_c_def using f1 f0 by(auto simp:cis.code cos_diff) 
  then have \<open>Re (cmod (b-a) * cmod (c-a)* cis (Arg (b-a))  * cis (Arg (cnj (c-a)))) =
      Re (cmod (c-a) *cmod (b-a)) * cos (angle_c c a b) \<close>
  proof -
    have f1: "cor (cmod (b - a) * cmod (c - a)) * cis (Arg (b - a)) * cis (Arg (cnj (c - a)))
 = cor (cmod (b - a) * cmod (c - a)) * (cis (Arg (b - a)) * cis (Arg (cnj (c - a))))"
      using ab_semigroup_mult_class.mult_ac(1) by blast
    have "cmod (b - a) * cmod (c - a) = cmod (c - a) * cmod (b - a)"
      by argo
    then show ?thesis
      using f1 Im_complex_of_real Re_mult_real \<open>Re (cis (Arg (b - a)) * cis (Arg (cnj (c - a)))) 
          = cos (angle_c c a b)\<close> by presburger
  qed
  then show \<open>Re ((b-a)*cnj(c-a)) = cmod (c-a) *cmod (b-a) * cos (angle_c c a b)\<close> 
    by (metis Re_complex_of_real f2 mult.assoc mult.commute of_real_mult)
   
qed

lemma law_of_cosines':
  assumes h:\<open>A\<noteq>C\<close> \<open>A\<noteq>B\<close>
  shows "((cdist B C)\<^sup>2 - (cdist A C)\<^sup>2 - (cdist A B)\<^sup>2 ) / (- 2*(cdist A C)*(cdist A B)) = (cos (\<angle> (C-A) (B-A)))"
  using law_of_cosines[of B C A] h by(auto simp:field_simps)

lemma law_of_cosines'':
  shows "(cdist A C)\<^sup>2 = (cdist B C)\<^sup>2 - (cdist A B)\<^sup>2 + 2*(cdist A C)*(cdist A B)*(cos (\<angle> (C-A) (B-A)))"
  using law_of_cosines[of B C A]  by(auto simp:field_simps)

lemma law_of_cosines''':
  shows " (cdist A B)\<^sup>2 = (cdist B C)\<^sup>2 - (cdist A C)\<^sup>2 + 2*(cdist A C)*(cdist A B)*(cos (\<angle> (C-A) (B-A)))"
  using law_of_cosines[of B C A]  by(auto simp:field_simps)


subsection \<open>The law of sines\<close>
theorem law_of_sines:
  assumes h1:\<open>b \<noteq> a\<close> \<open>a \<noteq> c\<close> \<open>b \<noteq> c\<close>
  shows  "sin (angle_c a b c) * cdist b c = sin (angle_c c a b) * cdist a c" (is "?A = ?B") 
proof - 
  {fix a b c ::complex
    have f0:\<open>sin (Arg (cnj c - cnj a)) = - sin (Arg ( c - a))\<close>
      by (metis arg_cnj_not_pi arg_cnj_pi complex_cnj_diff neg_0_equal_iff_equal sin_minus
          sin_pi)
    have f1:\<open>cos (Arg (cnj c - cnj a)) = cos (Arg (c - a))\<close>
      by (metis arg_cnj_not_pi arg_cnj_pi complex_cnj_diff cos_minus)
    assume \<open>b-a \<noteq> 0\<close> \<open>c-a \<noteq> 0 \<close>
    then have f2: \<open>b-a = cmod (b-a) * cis (Arg (b-a)) \<and> cnj (c-a) = cmod (c-a) * cis (Arg (cnj (c-a)))\<close>
      using rcis_cmod_Arg rcis_def 
      by (metis complex_mod_cnj)
    then have \<open>Im(cis (Arg (b-a)) * cis (Arg (cnj(c-a)))) = sin (angle_c c a b)\<close>
      unfolding ang_vec_def angle_c_def using f1 f0 by(auto simp:cis.code sin_diff) 
    then have \<open>Im (cmod (b-a) * cis (Arg (b-a)) * cmod (c-a) * cis (Arg (cnj (c-a)))) =
      cmod (c-a) *cmod (b-a) * sin (angle_c c a b) \<close>
      by (metis Im_complex_of_real[of "cmod (c - a)"] Im_complex_of_real[of "cmod (b - a)"]
          Im_mult_real[of "cor (cmod (c - a))"
            "cis (Arg (cnj (c - a))) * (cor (cmod (b - a)) * cis (Arg (b - a)))"]
          Im_mult_real[of "cor (cmod (b - a))" "cis (Arg (b - a)) * cis (Arg (cnj (c - a)))"]
          Re_complex_of_real[of "cmod (c - a)"] Re_complex_of_real[of "cmod (b - a)"]
          ab_semigroup_mult_class.mult_ac(1)[of "cor (cmod (b - a))" "cis (Arg (b - a))"
            "cis (Arg (cnj (c - a)))"]
          ab_semigroup_mult_class.mult_ac(1)[of "cis (Arg (cnj (c - a)))"
            "cor (cmod (b - a)) * cis (Arg (b - a))" "cor (cmod (c - a))"]
          ab_semigroup_mult_class.mult_ac(1)[of "cmod (c - a)" "cmod (b - a)"
            "Im (cis (Arg (b - a)) * cis (Arg (cnj (c - a))))"]
          mult.commute[of "cis (Arg (cnj (c - a)))" "cor (cmod (b - a)) * cis (Arg (b - a))"]
          mult.commute[of "cis (Arg (cnj (c - a))) * (cor (cmod (b - a)) * cis (Arg (b - a)))"
            "cor (cmod (c - a))"]
          mult.commute[of "cor (cmod (b - a)) * cis (Arg (b - a)) * cor (cmod (c - a))"
            "cis (Arg (cnj (c - a)))"])
    then have \<open>Im ((b-a)*cnj(c-a)) = cmod (c-a) *cmod (b-a) * sin (angle_c c a b)\<close> 
      using ang_sin by presburger
  }note ang=this
  have i2:\<open>sin (angle_c c a b) = Im((b-a)*cnj(c-a))/ (cmod(b-a)*cmod(c-a))\<close>
    using ang[of b a c] h1 by(auto)
  have \<open>sin (angle_c a b c) = Im((c-b)*cnj(a-b)) / (cmod (c-b)*cmod (a-b))\<close>
    using ang h1 by(auto)
  then have imp1:\<open>cmod (c-b) * sin (angle_c a b c) = Im((c-b)*cnj(a-b)) / (cmod (a-b)) \<close>
    by auto
  from i2 have imp2:\<open>cmod (c-a) * sin (angle_c c a b) = Im((b-a)*cnj(c-a))/ (cmod(b-a)) \<close>
    by auto
  show ?thesis using imp1 imp2 by(auto simp:field_simps norm_minus_commute) 
qed

lemma law_of_sines':  assumes h1:\<open>b \<noteq> a\<close> \<open>a \<noteq> c\<close> \<open>b \<noteq> c\<close>
  shows "sin (angle_c a b c) * cdist b a = sin (angle_c b c a) * cdist a c"
proof - 
  {fix a b c ::complex
    have f0:\<open>sin (Arg (cnj c - cnj a)) = - sin (Arg ( c - a))\<close>
      by (metis arg_cnj_not_pi arg_cnj_pi complex_cnj_diff neg_0_equal_iff_equal sin_minus
          sin_pi)
    have f1:\<open>cos (Arg (cnj c - cnj a)) = cos (Arg (c - a))\<close>
      by (metis arg_cnj_not_pi arg_cnj_pi complex_cnj_diff cos_minus)
    assume \<open>b-a \<noteq> 0\<close> \<open>c-a \<noteq> 0 \<close>
    then have f2:\<open>b-a = cmod (b-a) * cis (Arg (b-a)) \<and> cnj (c-a) = cmod (c-a) * cis (Arg (cnj (c-a)))\<close>
      using rcis_cmod_Arg rcis_def 
      by (metis complex_mod_cnj)
    then have \<open>Im(cis (Arg (b-a)) * cis (Arg (cnj(c-a)))) = sin (angle_c c a b)\<close>
      unfolding ang_vec_def angle_c_def using f0 f1 by(auto simp:cis.code sin_diff) 
    then have \<open>Im (cmod (b-a) * cis (Arg (b-a)) * cmod (c-a) * cis (Arg (cnj (c-a)))) =
      cmod (c-a) *cmod (b-a) * sin (angle_c c a b) \<close>
      by (metis Im_complex_of_real[of "cmod (c - a)"] Im_complex_of_real[of "cmod (b - a)"]
          Im_mult_real[of "cor (cmod (c - a))"
            "cis (Arg (cnj (c - a))) * (cor (cmod (b - a)) * cis (Arg (b - a)))"]
          Im_mult_real[of "cor (cmod (b - a))" "cis (Arg (b - a)) * cis (Arg (cnj (c - a)))"]
          Re_complex_of_real[of "cmod (c - a)"] Re_complex_of_real[of "cmod (b - a)"]
          ab_semigroup_mult_class.mult_ac(1)[of "cor (cmod (b - a))" "cis (Arg (b - a))"
            "cis (Arg (cnj (c - a)))"]
          ab_semigroup_mult_class.mult_ac(1)[of "cis (Arg (cnj (c - a)))"
            "cor (cmod (b - a)) * cis (Arg (b - a))" "cor (cmod (c - a))"]
          ab_semigroup_mult_class.mult_ac(1)[of "cmod (c - a)" "cmod (b - a)"
            "Im (cis (Arg (b - a)) * cis (Arg (cnj (c - a))))"]
          mult.commute[of "cis (Arg (cnj (c - a)))" "cor (cmod (b - a)) * cis (Arg (b - a))"]
          mult.commute[of "cis (Arg (cnj (c - a))) * (cor (cmod (b - a)) * cis (Arg (b - a)))"
            "cor (cmod (c - a))"]
          mult.commute[of "cor (cmod (b - a)) * cis (Arg (b - a)) * cor (cmod (c - a))"
            "cis (Arg (cnj (c - a)))"])
    then have \<open>Im ((b-a)*cnj(c-a)) = cmod (c-a) *cmod (b-a) * sin (angle_c c a b)\<close> 
      using ang_sin by presburger
  }note ang=this
  have i2:\<open>sin (angle_c b c a) = Im((a-c)*cnj(b - c))/ (cmod(b-c)*cmod(a-c))\<close>
    using ang[of a c b] h1 by(auto)
  have \<open>sin (angle_c a b c) = Im((c-b)*cnj(a-b)) / (cmod (c-b)*cmod (a-b))\<close>
    using ang h1 by(auto)
  then have imp1:\<open>cmod (a-b) * sin (angle_c a b c) = Im((c-b)*cnj(a-b)) / (cmod (c-b)) \<close>
    by auto
  from i2 have imp2:\<open>cmod (a-c) * sin (angle_c b c a) = Im((a-c)*cnj(b-c))/ (cmod(b-c)) \<close>
    by auto
  show ?thesis using imp1 imp2 
    by (metis cdist_commute h1(1,2,3) law_of_sines)
qed


lemma ang_pos_pos:\<open>q\<noteq>p \<Longrightarrow> p\<noteq> r \<Longrightarrow> r \<noteq> q \<Longrightarrow> angle_c q r p \<ge> 0 \<Longrightarrow> angle_c r p q \<ge>0\<close>
  using law_of_sines'[of r q p] 
  by (smt (verit) ang_vec_bounded angle_c_def cdist_def mult_neg_pos mult_nonneg_nonneg 
right_minus_eq sin_ge_zero sin_gt_zero sin_minus zero_less_norm_iff)

lemma cmod_pos:\<open>cmod a \<ge> 0\<close>
  by simp

lemma ang_neg_neg:\<open>q\<noteq>p \<Longrightarrow> p\<noteq> r \<Longrightarrow> r \<noteq> q \<Longrightarrow> angle_c q r p < 0 \<Longrightarrow> angle_c r p q < 0\<close>
proof -
  assume \<open>q\<noteq>p\<close> \<open>p\<noteq> r\<close> \<open>r \<noteq> q\<close> \<open>angle_c q r p < 0\<close>
  then have \<open>sin (angle_c q r p) < 0\<close>
    using ang_c_in 
    by (metis ang_vec_def angle_c_def canon_ang(1) minus_less_iff neg_0_less_iff_less sin_gt_zero sin_minus)
  then have \<open>sin (angle_c q r p) * cdist r q < 0\<close>
    using \<open>r \<noteq> q\<close> mult_neg_pos by fastforce
  from law_of_sines'[of r q p] have  \<open>sin (angle_c r p q)<0\<close>
    by (metis \<open>p \<noteq> r\<close> \<open>q \<noteq> p\<close> \<open>r \<noteq> q\<close> \<open>sin (angle_c q r p) * cdist r q < 0\<close> 
        cdist_def linorder_not_less mult_less_0_iff norm_ge_zero)
  then show ?thesis
    using ang_c_in[of r p q] 
    by (metis ang_vec_def angle_c_def canon_ang(2) linorder_not_less sin_ge_zero) 
qed

lemma collinear_sin_neq_0:
  \<open>\<not>collinear a2 b2 c2 \<Longrightarrow> sin (angle_c a2 c2 b2) \<noteq> 0\<close>
  unfolding collinear_def angle_c_def 
  by (metis Im_complex_div_eq_0 ang_sin angle_c_def collinear_def
 collinear_sym1 collinear_sym2' mult_eq_0_iff)


lemma collinear_sin_neq_pi:
  \<open>\<not>collinear a2 b2 c2 \<Longrightarrow> sin (angle_c a2 c2 b2) \<noteq> pi\<close>
  unfolding collinear_def angle_c_def 
  by (metis add_cancel_right_left dual_order.antisym dual_order.trans le_add_same_cancel1 
linordered_nonzero_semiring_class.zero_le_one one_add_one one_neq_zero pi_ge_two sin_le_one)


lemma collinear_iff:
  assumes \<open>a\<noteq>b \<and> b\<noteq>c \<and> c\<noteq>a\<close> 
  shows \<open>collinear a b c \<longleftrightarrow> (angle_c a b c = pi \<or> angle_c a b c = 0)\<close>
  apply(rule iffI)
  using assms unfolding collinear_def using collinear_angle collinear_def apply(fastforce) 
  by (metis collinear_def collinear_sin_neq_0 collinear_sym1 sin_pi sin_zero)



definition \<open>innerprod a b \<equiv> cnj a * b\<close>


lemma left_lin_innerprod:\<open>innerprod (x + y) z = innerprod x z + innerprod y z\<close>
  unfolding innerprod_def  
  by (simp add: mult.commute ring_class.ring_distribs(1))

lemma right_lin_innerprod:\<open>innerprod x (y+z) = innerprod x y + innerprod x z\<close>
  unfolding innerprod_def 
  by (simp add: ring_class.ring_distribs(1))

lemma leftlin_innerprod:\<open>innerprod x (t*y) = t * innerprod x y\<close>
  unfolding innerprod_def by(auto)

lemma rightsesqlin_innerprod:\<open>innerprod (t*x) (y) = cnj t * innerprod x y\<close>
  unfolding innerprod_def by(auto)

lemma norm_eq_csqrt_inner:\<open>norm x = csqrt (innerprod x x)\<close>
  using complex_mod_sqrt_Re_mult_cnj innerprod_def by force

lemma abs2_eq_inner:\<open>abs (innerprod x y)^2 = innerprod x y * cnj (innerprod x y)\<close>
  unfolding innerprod_def abs_complex_def apply(rule complex_eqI)
  by (metis comp_apply complex_mult_cnj_cmod of_real_power)+

lemma complex_add_inner_cnj:\<open>t*innerprod x y + cnj (t*innerprod x y) = 2* Re (t*innerprod x y)\<close>
  using complex_add_cnj by blast

lemma Re_innerprod_inner:\<open>Re (innerprod (a-b) (c-b)) = (a-b)\<bullet>(c-b)\<close>
  unfolding innerprod_def inner_complex_def by(auto simp:field_simps) 

lemma angle_c_arccos_pos: 
  assumes h:\<open>a\<noteq>b \<and> b\<noteq> c\<close> \<open>angle_c a b c \<ge> 0\<close>
  shows \<open>angle_c a b c = arccos ((Re (innerprod (a-b) (c - b)))/(cmod(a-b)*cmod(c-b)))\<close>
proof - 
  have \<open>Re ((a-b)*cnj(c-b)) = (Re (innerprod (a-b) (c - b)))\<close>
    unfolding innerprod_def by(auto simp:field_simps) 
  then have \<open>((Re (innerprod (a-b) (c - b)))/(cmod(a-b)*cmod(c-b))) = cos (angle_c a b c)\<close>
    by (metis (no_types, lifting) ang_cos angle_c_commute cos_minus divisors_zero
 h(1) mult.commute nonzero_mult_div_cancel_left norm_eq_zero right_minus_eq)
  then show ?thesis 
    using ang_vec_bounded angle_c_def arccos_cos h(2) by presburger
qed


lemma angle_c_arccos_neg: 
  assumes h:\<open>a\<noteq>b \<and> b\<noteq> c\<close> \<open>angle_c a b c \<le> 0 \<close>
  shows \<open>- angle_c a b c = arccos ((Re (innerprod (a-b) (c - b)))/(cmod(a-b)*cmod(c-b)))\<close>
proof - 
  have \<open>Re ((a-b)*cnj(c-b)) = (Re (innerprod (a-b) (c - b)))\<close>
    unfolding innerprod_def by(auto simp:field_simps) 
  then have \<open>((Re (innerprod (a-b) (c - b)))/(cmod(a-b)*cmod(c-b))) = cos (angle_c a b c)\<close>
    by (metis (no_types, lifting) ang_cos angle_c_commute cos_minus divisors_zero
 h(1) mult.commute nonzero_mult_div_cancel_left norm_eq_zero right_minus_eq)
  then show ?thesis 
    using ang_vec_bounded angle_c_def arccos_cos h(2) 
    by (metis arccos_cos2 less_le_not_le)
qed

end