theory Complex_Triangles

imports Complex_Trigonometry Third_Unity_Root

begin

lemma similar_triangles':
  assumes h:"a \<noteq> 0 \<and> b \<noteq> 0 \<and> 0 \<noteq> c \<and> a' \<noteq> 0 \<and> b'\<noteq>0 \<and> c'\<noteq>0"
    and h1:\<open>\<angle> (-a) b = \<angle> (-a') b'\<close> \<open>\<angle> (-b') c'  = \<angle> (-b) c\<close>
  shows \<open>\<angle> (-c) a = \<angle> (-c') a'\<close>
proof -
  have \<open>\<downharpoonright>\<angle> (-a) b + \<angle> (-b) c  + \<angle> (-c) a\<downharpoonleft> = pi\<close>
    using angle_sum_triangle' h by auto
  also have \<open>\<downharpoonright>\<angle> (-a') b' + \<angle> (-b') c'  + \<angle> (-c') a'\<downharpoonleft> = pi\<close>
    using angle_sum_triangle' h by auto
  also have \<open>\<downharpoonright>\<angle> (-a') b' + \<angle> (-b') c'  + \<angle> (-c) a\<downharpoonleft> = pi\<close>
    using \<open>\<downharpoonright>\<angle> (- a) b + \<angle> (- b) c + \<angle> (- c) a\<downharpoonleft> = pi\<close> h1(1,2) by auto
  then have \<open>\<downharpoonright>\<angle> (- c) a\<downharpoonleft> = \<downharpoonright>\<angle> (- c') a'\<downharpoonleft>\<close>
    by (smt (verit) \<open>\<downharpoonright>\<angle> (- a') b' + \<angle> (- b') c' + \<angle> (- c') a'\<downharpoonleft> = pi\<close> add.inverse_inverse ang_vec_bounded
        ang_vec_opposite1 ang_vec_opposite2 ang_vec_opposite_opposite ang_vec_plus_pi1 ang_vec_plus_pi2
        canon_ang_diff canon_ang_id h neg_0_equal_iff_equal)
  ultimately show ?thesis 
    by (metis ang_vec_bounded canon_ang_id)
qed



lemma similar_triangles:
  assumes h:"a \<noteq> b \<and> b \<noteq> c \<and> a \<noteq> c \<and> a' \<noteq> b' \<and> b'\<noteq> c' \<and> c'\<noteq>a'"
    and h1:\<open>\<angle> (c-a) (b-a) = \<angle> (c'-a') (b'-a')\<close> \<open>\<angle> (a-b) (c-b)  =  \<angle> (a'-b') (c'-b')\<close>
  shows     \<open> \<angle> (b-c) (a-c) =  \<angle> (b'-c') (a'-c')\<close>
proof -
  have \<open>a-b\<noteq>0\<close> \<open>b-c\<noteq>0\<close> \<open>a-c\<noteq>0\<close> \<open>a'-b'\<noteq>0\<close> \<open>b'-c'\<noteq>0\<close> \<open>c'-a'\<noteq>0\<close>
    using h by auto
  then show ?thesis 
    by (smt (z3) diff_numeral_special(12) h1(1,2) minus_diff_eq similar_triangles')
qed

lemma similar_triangles_c:
  assumes h:"a \<noteq> b \<and> b \<noteq> c \<and> a \<noteq> c \<and> a' \<noteq> b' \<and> b'\<noteq> c' \<and> c'\<noteq>a'"
    and h1:\<open>angle_c c a b = angle_c c' a' b'\<close> \<open>angle_c a b c  =  angle_c a' b' c'\<close>
  shows     \<open>angle_c b c a =  angle_c b' c' a'\<close>
proof -
  have \<open>a-b\<noteq>0\<close> \<open>b-c\<noteq>0\<close> \<open>a-c\<noteq>0\<close> \<open>a'-b'\<noteq>0\<close> \<open>b'-c'\<noteq>0\<close> \<open>c'-a'\<noteq>0\<close>
    using h by auto
  then show ?thesis 
    unfolding angle_c_def 
    by (metis angle_c_def h h1(1,2) similar_triangles)
qed


lemmas congruent_ctriangleD = congruent_ctriangle.sides congruent_ctriangle.angles


lemma congruent_ctriangles_sss:
  assumes  h:"a \<noteq> b \<and> b \<noteq> c \<and> a \<noteq> c"
    and  h1:\<open>cmod (b - a)= cmod (b'-a')\<close> \<open>cmod (b - c) = cmod (b' - c')\<close> \<open>cmod (c - a) = cmod (c' - a')\<close>
  shows \<open>congruent_ctriangle a b c a' b' c'\<close>
proof -
  {fix c b a c' b' a'
    assume h:"a \<noteq> b \<and> b \<noteq> c \<and> a \<noteq> c"
      and h1:\<open>cmod (b - a)= cmod (b'-a')\<close> \<open>cmod (b - c) = cmod (b' - c')\<close> \<open>cmod (c - a) = cmod (c' - a')\<close>
    then have h':\<open>a'\<noteq>b' \<and> b'\<noteq>c' \<and> c'\<noteq>a'\<close> 
      by auto
    have \<open>cos (\<angle> (c-a) (b-a)) = ((cdist b c)\<^sup>2 - (cdist a c)\<^sup>2 - (cdist a b)\<^sup>2 ) / (- 2*(cdist a c)*(cdist a b)) \<close>
      using law_of_cosines' h by auto
    moreover have \<open>cos (\<angle> (c'-a') (b'-a')) = ((cdist b' c')\<^sup>2 - (cdist a' c')\<^sup>2 - (cdist a' b')\<^sup>2 ) / (- 2*(cdist a' c')*(cdist a' b')) \<close>
      using law_of_cosines' h h' by auto
    ultimately have f0:\<open>cos (\<angle> (c-a) (b-a)) = cos (\<angle> (c'-a') (b'-a'))\<close>
      by (metis cdist_def h1(1,2,3) norm_minus_commute)
    have \<open>\<angle> (c-a) (b-a) \<in> {-pi .. pi}\<close> \<open>\<angle> (c'-a') (b'-a') \<in> {-pi..pi}\<close>
      unfolding ang_vec_def 
      using canon_ang(1,2) less_eq_real_def by auto
    with f0 have  \<open>\<angle> (c-a) (b-a) = \<angle> (c'-a') (b'-a') \<or> \<angle> (c-a) (b-a) = - \<angle> (c'-a') (b'-a')\<close>
      unfolding ang_vec_def 
      by (smt (verit) arccos_cos2 arccos_minus_1 arccos_unique canon_ang(1,2))}note dem=this
  then show ?thesis 
    by (metis (mono_tags, lifting) angle_c_def cdist_def 
congruent_ctriangle_def h h1(1) h1(2) h1(3) norm_minus_commute)
qed  

lemma congruent_ctriangleI_sss:
  assumes  h:"a \<noteq> b \<and> b \<noteq> c \<and> a \<noteq> c"
    and  h1:\<open>cdist a b = cdist a' b'\<close> \<open>cdist b c = cdist b' c'\<close> \<open>cdist a c = cdist a' c'\<close>
  shows \<open>congruent_ctriangle a b c a' b' c'\<close>
  using cdist_def congruent_ctriangles_sss  h1(1,2,3) h
  by (metis dist_commute dist_complex_def)

lemmas congruent_ctriangle_sss = congruent_ctriangleD[OF congruent_ctriangleI_sss]

lemma isosceles_triangles:
  assumes \<open>cdist a b = cdist b c\<close>
  shows \<open>angle_c b c a =  angle_c b a c \<or> angle_c b c a = - angle_c b a c \<close>
  by (metis assms cdist_commute cdist_def congruent_ctriangle_sss(14) norm_eq_zero right_minus_eq)


lemma non_collinear_independant:"\<not> collinear a b c \<Longrightarrow> a \<noteq> b \<and> b \<noteq> c \<and> a \<noteq> c"
  using collinear_ex_real by force



lemma congruent_ctriangleI_sas:
  assumes \<open>a1 \<noteq> b1 \<and> b1 \<noteq> c1 \<and> a1 \<noteq> c1\<close>
  assumes h1:"cdist a1 b1 = cdist a2 b2"
  assumes h2:"cdist b1 c1 = cdist b2 c2"
  assumes h3:"angle_c a1 b1 c1 = angle_c a2 b2 c2 \<or> angle_c a1 b1 c1 = - angle_c a2 b2 c2"
  shows   "congruent_ctriangle a1 b1 c1 a2 b2 c2"
proof (rule congruent_ctriangleI_sss)
  have h1':"cdist a1 b1 = cdist b2 a2"
    using cdist_commute h1 by auto
  show "cdist a1 c1 = cdist a2 c2"
  proof (rule power2_eq_imp_eq)
    show "(cdist a1 c1)\<^sup>2 = (cdist a2 c2)\<^sup>2" 
      apply(insert law_of_cosines[of a1 c1 b1] law_of_cosines[of a2 c2 b2])
      apply(subst (asm) (1 2) h2) apply(subst (asm) (1 2) h1'[symmetric])
      using assms unfolding angle_c_def 
      by (smt (verit) congruent_ctriangle_sss(7) angle_c_commute angle_c_def
          cos_minus)
  qed simp_all
  show "a1 \<noteq> b1 \<and> b1 \<noteq> c1 \<and> a1 \<noteq> c1"
    "cdist a1 b1 = cdist a2 b2"
    "cdist b1 c1 = cdist b2 c2" using assms cdist_commute by auto
qed 

lemmas congruent_ctriangle_sas = congruent_ctriangleD[OF congruent_ctriangleI_sas]

(**)
lemma congruent_ctriangleI_aas:
  assumes h1:"angle_c a1 b1 c1 = angle_c a2 b2 c2"
  assumes h2:"angle_c b1 c1 a1 = angle_c b2 c2 a2"
  assumes h3:"cdist a1 b1 = cdist a2 b2"
  assumes h4:"\<not>collinear a1 b1 c1" "\<not>collinear a2 b2 c2"
  shows   "congruent_ctriangle a1 b1 c1 a2 b2 c2"
proof (rule congruent_ctriangleI_sas)
  from h4 have neq: "a1 \<noteq> b1" unfolding collinear_def by auto
  with assms(3) have neq': "a2 \<noteq> b2" by auto
  have h0:\<open>a1 \<noteq> b1\<close> \<open>b1 \<noteq> c1\<close> \<open>a1 \<noteq> c1\<close> 
    using assms(4) non_collinear_independant by auto
  have h0':\<open>a2 \<noteq> b2\<close> \<open>b2 \<noteq> c2\<close> \<open>a2 \<noteq> c2\<close> 
    using assms(5) non_collinear_independant by auto
  have A: "angle_c c1 a1 b1 = angle_c c2 a2 b2" using neq neq' assms
    apply(insert angle_sum_triangle_c[of a1 b1 c1] angle_sum_triangle_c[of a2 b2 c2])
    by (metis h0 assms(5) h1 h2 non_collinear_independant similar_triangles_c)
  have \<open>-\<angle> (b1 - c1) (a1 - c1) = - \<angle> (b2 - c2) (a2 - c2)\<close> 
    using h2 unfolding angle_c_def by auto
  then have A1:\<open>angle_c a1 c1 b1 = angle_c a2 c2 b2\<close>
    using h2  unfolding angle_c_def 
    apply(cases \<open>angle_c a1 c1 b1 = pi\<close>) 
     apply (metis ang_vec_def angle_c_def canon_ang_uminus_pi minus_diff_eq)
    by (metis ang_vec_sym ang_vec_sym_pi)
  have \<open>\<angle> (b1 - a1) (c1 - a1) = \<angle> (b2 - a2) (c2 - a2)\<close>
    by (metis ang_vec_sym ang_vec_sym_pi angle_c_def A)
  have sine1:\<open> sin (angle_c a1 c1 b1) * cdist c1 b1 = sin (angle_c b1 a1 c1) * cdist a1 b1\<close>
    by (metis h0 law_of_sines)
  have sine2:\<open>sin (angle_c a2 c2 b2) * cdist c2 b2 = sin (angle_c b2 a2 c2) * cdist a2 b2\<close>
    by (metis assms(5) law_of_sines non_collinear_independant)
  have \<open>\<not>collinear a2 b2 c2 \<Longrightarrow> sin (angle_c a2 c2 b2) \<noteq> 0\<close>
    unfolding collinear_def angle_c_def 
    using angle_c_def collinear_sin_neq_0 h4(2) by presburger
  have h3':\<open>cdist b1 a1 = cdist b2 a2\<close> 
    using h3 cdist_commute by auto
  have A2:\<open>angle_c b1 a1 c1 = angle_c b2 a2 c2\<close>
    using \<open>\<angle> (b1 - a1) (c1 - a1) = \<angle> (b2 - a2) (c2 - a2)\<close> angle_c_def by auto
  have \<open> cdist c1 b1 = sin (angle_c b2 a2 c2) * cdist a2 b2 / sin (angle_c a2 c2 b2) \<and>
     cdist c2 b2 = sin (angle_c b2 a2 c2) * cdist a2 b2 / sin (angle_c a2 c2 b2) \<close>
    apply(cases \<open> sin (angle_c a2 c2 b2) = 0\<close>)
     apply (simp add:
        \<open>\<not> Elementary_Complex_Geometry.collinear a2 b2 c2 \<Longrightarrow> sin (angle_c a2 c2 b2) \<noteq> 0\<close>
        \<open>\<not> Elementary_Complex_Geometry.collinear a2 b2 c2\<close>) 
    by (metis A1 A2 h3 nonzero_mult_div_cancel_left sine1 sine2)
  then show "cdist b1 c1 = cdist b2 c2"
    using cdist_commute by auto
  show  "a1 \<noteq> b1 \<and> b1 \<noteq> c1 \<and> a1 \<noteq> c1"
    "cdist a1 b1 = cdist a2 b2"
    "angle_c a1 b1 c1 = angle_c a2 b2 c2 \<or> angle_c a1 b1 c1 = - angle_c a2 b2 c2" 
    using assms h0 neq by auto
qed 


lemmas congruent_ctriangle_aas = congruent_ctriangleD[OF congruent_ctriangleI_aas]

lemma congruent_ctriangleI_asa:
  assumes "angle_c a1 b1 c1 = angle_c a2 b2 c2"
  assumes "cdist a1 b1 = cdist a2 b2"
  assumes h0:"angle_c b1 a1 c1 = angle_c b2 a2 c2"
  assumes h4:"\<not>collinear a1 b1 c1" "\<not>collinear a2 b2 c2"
  shows   "congruent_ctriangle a1 b1 c1 a2 b2 c2"
proof (rule congruent_ctriangleI_aas)
  from assms have neq: "a1 \<noteq> b1" "a2 \<noteq> b2" unfolding collinear_def by auto
  show "angle_c b1 c1 a1 = angle_c b2 c2 a2"
    apply (rule similar_triangles_c) 
    using assms(4,5) non_collinear_independant apply auto[1]
    using h0 unfolding angle_c_def 
     apply (metis ang_vec_sym ang_vec_sym_pi)
    using angle_c_def assms(1) by auto
qed fact+


lemmas congruent_ctriangle_asa = congruent_ctriangleD[OF congruent_ctriangleI_asa]


lemma orientation_respect_letter_order:
  assumes "angle_c a b c = angle_c b a c" "\<not> collinear a b c"
  shows   "False"
  by (smt (verit, ccfv_threshold) angle_c_commute assms(1)
      assms(2) collinear_sin_neq_0 collinear_sym1 similar_triangles_c sin_pi sin_zero)


lemma isoscele_iff_pr_cis_qr:
  assumes h':\<open>q\<noteq>r\<close> 
  shows \<open>(cdist q r = cdist p r) \<longleftrightarrow> (p-r) = cis(angle_c q r p)*(q-r)\<close>
proof (rule iffI)
  assume h:\<open>(cdist q r = cdist p r)\<close>
  then have f0:\<open>cmod(p-r) = cmod(q-r)\<close> 
    by (simp add: norm_minus_commute)
  have \<open>(p-r)/(q-r) = (p-r)*cnj(q-r)/cmod(q-r)^2\<close>
    using complex_div_cnj by blast
  have f1:\<open>Re ((p-r)*cnj(q-r)) = cmod(p-r)*cmod(q-r)*cos(angle_c q r p)\<close>
    by (metis (no_types, lifting)  ang_cos cdist_commute cdist_def h(1))
  have f2: \<open>Im ((p-r)*cnj(q-r)) = cmod(p-r)*cmod(q-r)* sin(angle_c q r p)\<close>
    using ang_sin h(1) by auto
  then have \<open> (p-r)*cnj(q-r)/cmod(q-r)^2 = cmod(p-r)*cmod(q-r)*cis(angle_c q r p)/cmod(q-r)^2\<close>
    apply(intro complex_eqI)
    using f1 f2 by auto
  then have f3:\<open>(p-r)/(q-r) = cmod(p-r)*cmod(q-r)*cis(angle_c q r p)/cmod(q-r)^2\<close>
    by (simp add: \<open>(p - r) / (q - r) = (p - r) * cnj (q - r) / cor ((cmod (q - r))\<^sup>2)\<close>)
  have \<open>(p-r)/(q-r) = cis (angle_c q r p)\<close>
    apply(subst f3) apply(subst f0) by(simp add:h h' power2_eq_square) 
  then show \<open>p - r = cis (angle_c q r p) * (q - r)\<close>
    using divide_eq_eq h h' by force
next
  assume \<open>p - r = cis (angle_c q r p) * (q - r) \<close>
  have \<open>(p-r)/(q-r) = (p-r)*cnj(q-r)/cmod(q-r)^2\<close>
    using complex_div_cnj by blast
  have f1:\<open>Re ((p-r)*cnj(q-r)) = cmod(p-r)*cmod(q-r)*cos(angle_c q r p)\<close>
    using ang_cos by fastforce
  have f2: \<open>Im ((p-r)*cnj(q-r)) = cmod(p-r)*cmod(q-r)* sin(angle_c q r p)\<close>
    using ang_sin by fastforce
  then have f4:\<open> (p-r)*cnj(q-r)/cmod(q-r)^2 = cmod(p-r)*cmod(q-r)*cis(angle_c q r p)/cmod(q-r)^2\<close>
    apply(intro complex_eqI)
    using f1 f2 by auto
  then have f3:\<open>(p-r)/(q-r) = cmod(p-r)*cmod(q-r)*cis(angle_c q r p)/cmod(q-r)^2\<close>
    by (simp add: \<open>(p - r) / (q - r) = (p - r) * cnj (q - r) / cor ((cmod (q - r))\<^sup>2)\<close>)
  have \<open>cmod(p-r)*cmod(q-r)*cis(angle_c q r p)/cmod(q-r)^2 = cis (angle_c q r p)\<close>  
    using \<open>p - r = cis (angle_c q r p) * (q - r)\<close> \<open>q \<noteq> r\<close> f3 by auto
  then have \<open>cmod(p-r)*cmod(q-r)/cmod(q-r)^2 = 1\<close> 
    by (metis f4 \<open>q \<noteq> r\<close> cmod_power2 complex_mod_cnj complex_mod_mult_cnj complex_mult_cnj 
        eq_iff_diff_eq_0 nonzero_norm_divide norm_cis norm_eq_zero norm_mult power_not_zero)
  then show \<open>cdist q r = cdist p r\<close> 
    by (metis cdist_commute cdist_def eq_divide_eq_1 mult.commute power2_eq_square real_divide_square_eq)
qed


lemma equilateral_imp_pi3:
  assumes \<open>q\<noteq>r\<close> "cdist q r = cdist p r" "cdist p r = cdist p q"
  shows "\<downharpoonright>(angle_c q r p)\<downharpoonleft> = pi/3 \<or> \<downharpoonright>(angle_c q r p)\<downharpoonleft> = -pi/3" 
    "(angle_c q r p) = (angle_c p q r) \<and> (angle_c q r p) = (angle_c r p q)"
proof -
  have f0:\<open>q\<noteq>r \<and> r\<noteq>p \<and> p\<noteq>q\<close> using assms by(auto)
  have \<open>angle_c q r p \<noteq> 0 \<and> angle_c q r p \<noteq> pi\<close>
    by (smt (verit, best) Re_complex_of_real angle_c_commute angle_c_commute_pi assms(1) assms(2) 
        assms(3) cdist_commute cdist_def congruent_ctriangle_sss(20) cor_cmod_real isoscele_iff_pr_cis_qr 
        minus_complex.simps(1) minus_complex.simps(2) minus_diff_eq mult_minus_right norm_eq_zero right_minus_eq)
  then have f1:\<open>\<not>collinear q r p\<close>
    using collinear_angle f0 by blast
  then have f1':\<open>\<not>collinear p q r\<close> 
    by (simp add: collinear_sym1 collinear_sym2)
  have f12:\<open>(angle_c q r p) = angle_c r p q \<or> (angle_c q r p) = - angle_c r p q\<close>
    apply(rule congruent_ctriangle_sss)
    using f0 assms by(auto simp:norm_minus_commute) 
  have f4:\<open>(angle_c q r p) = angle_c p q r \<or> (angle_c q r p) = - angle_c p q r\<close>
    apply(rule congruent_ctriangle_sss)
    using f0 assms by(auto simp:norm_minus_commute)
  have f5:\<open>(angle_c q r p) \<noteq> pi\<close>
    using f1 
    by (metis angle_c_commute canon_ang_sin canon_ang_uminus_pi collinear_sin_neq_0 f1' pi_canonical
        sin_pi)
  from f4 have \<open> \<downharpoonright>(angle_c q r p) +  (angle_c r p q) + (angle_c p q r)\<downharpoonleft> = pi\<close>
    using angle_sum_triangle_c[of p q r] f0 by auto
  have \<open>\<forall>x\<in>{-pi..0}. 3*x \<noteq> pi\<close> 
    by (metis atLeastAtMost_iff dual_order.trans mult_eq_0_iff mult_less_cancel_right2 numeral_le_one_iff
        pi_ge_zero pi_neq_zero semiring_norm(70) verit_comp_simplify1(3) verit_la_disequality)
  also have the_x:\<open>\<exists>!x\<in>{-pi<..pi}. 3*x = pi\<close>
    by(auto intro:exI[where x=\<open>pi/3\<close>])
  moreover have \<open>(angle_c x y z)  \<in>{-pi<..pi}\<close> for x y z
    using ang_c_in by auto
  have \<open>x\<in>{-3*pi<..3*pi} \<and> x-2*pi = pi \<Longrightarrow> ( x = 3*pi)\<close> for x k::real
    by(auto simp:) 
  have \<open>x\<in>{-3*pi<..3*pi} \<and> x-2*k*pi = pi \<and> ( k\<ge>2 \<or> k\<le> - 2) \<Longrightarrow> False\<close> for x and k::int
  proof -
    assume h:\<open>x\<in>{-3*pi<..3*pi} \<and> x-2*k*pi = pi \<and> ( k\<ge>2 \<or> k\<le> -2)\<close>
    then have f0:\<open> r = 2 \<Longrightarrow> x - 2* r*pi \<le> -pi\<close> for r by auto
    also have f1:\<open>k > 2 \<Longrightarrow> x - 2* k*pi < x-2*2*pi\<close> 
      by(auto)
    have f3:\<open>x-2*2*pi \<le> -pi\<close> 
      using f0[of 2] by(auto simp:abs_real_def)
    then have f2:\<open> k > 2 \<Longrightarrow> x - 2* k*pi < -pi\<close> 
      using f1 by argo
    ultimately have f3:\<open> k \<ge>2 \<Longrightarrow> x-2* k*pi \<le> -pi\<close> 
      apply(cases \<open>abs k=2\<close>) using f0 by(auto)
    have f0':\<open>r=-2 \<Longrightarrow> x - 2*r*pi > pi\<close> for r ::int
      using h by(auto) 
    have \<open>x+2*2*pi > pi\<close> using h by auto
    also have \<open>k< -2 \<Longrightarrow> x -2*k*pi > x - 2*(-2)*pi\<close> 
      using f0'[of 2] 
    proof -
      assume a1: "k < - 2"
      have f2: "pi < x - real_of_int (- 4) * pi"
        using f0' by force
      have "k + k \<le> - 4"
        using a1 by force
      then show ?thesis
        using f2 by (metis (no_types) diff_left_mono h mult.commute mult_2_right of_int_le_iff ordered_comm_semiring_class.comm_mult_left_mono pi_ge_zero verit_comp_simplify1(3))
    qed
    ultimately have f4:\<open>k \<le> -2 \<Longrightarrow> x-2* k*pi > pi\<close>
      apply(cases \<open>k=-2\<close>) using h  
        \<open>k < - 2 \<Longrightarrow> x - 2 * - 2 * pi < x - real_of_int (2 * k) * pi\<close> by auto 
    show False  
      using f3 f4 h by force
  qed
  then have possible_k:\<open>x\<in>{-3*pi<..3*pi} \<and> x-2*k*pi = pi \<Longrightarrow> k=-1 \<or> k=1 \<or> k=0\<close> for k::int and x
    by force
  have ang_3_in:\<open>y\<in>{-3*pi<..3*pi} \<and> \<downharpoonright>y\<downharpoonleft> = pi \<longleftrightarrow> y=pi \<or> y = 3*pi \<or> y=-pi\<close> for y
  proof(rule iffI)
    assume hyp:\<open>y \<in> {- 3 * pi<..3 * pi} \<and> \<downharpoonright>y\<downharpoonleft> = pi\<close>
    have \<open>\<exists>k. y - 2*k*pi = pi\<close> 
      by (metis add_diff_cancel_left' diff_add_cancel divide_self_if field_sum_of_halves mult.commute mult_1 mult_2
          pi_neq_zero times_divide_eq_right)
    with hyp show \<open>y = pi \<or> y=3*pi \<or> y= -pi\<close> 
      using hyp possible_k canon_ang_pi_3pi[of y] canon_ang_id canon_ang_uminus_pi 
      by (smt (verit, del_insts) canon_ang_minus_3pi_minus_pi greaterThanAtMost_iff)
  next
    assume \<open>y = pi \<or> y = 3 * pi \<or> y = - pi\<close>
    then show \<open>y \<in> {- 3 * pi<..3 * pi} \<and> \<downharpoonright>y\<downharpoonleft> = pi\<close>
      by(auto simp:canon_ang_uminus_pi canon_ang_pi_3pi) 
  qed
  ultimately have \<open>\<downharpoonright>3*(angle_c q r p)\<downharpoonleft> = pi \<Longrightarrow> angle_c q r p = -pi/3 \<or>  angle_c q r p = pi/3\<close> 
  proof -
    assume \<open>\<downharpoonright>3*(angle_c q r p)\<downharpoonleft> = pi\<close>
    have \<open>3*(angle_c q r p) \<in> {-3*pi<..3*pi}\<close>
      using ang_c_in by auto
    then have f0:\<open>3*(angle_c q r p) = -pi \<or> 3*(angle_c q r p) = pi \<or> 3*(angle_c q r p) = 3*pi\<close>
      using ang_3_in \<open>\<downharpoonright>3*(angle_c q r p)\<downharpoonleft> = pi\<close> by blast
    then have \<open>3*(angle_c q r p) = 3*pi \<Longrightarrow> False\<close>
      using collinear_sin_neq_pi by (simp add: f5) 
    then show \<open>angle_c q r p = -pi/3 \<or>  angle_c q r p = pi/3\<close>
      using f0 by auto
  qed
  have f2:\<open>\<downharpoonright>angle_c x y z \<downharpoonleft> = angle_c x y z\<close> for x y z::complex
    using ang_vec_bounded angle_c_def canon_ang_id by fastforce 
  then have \<open>\<downharpoonright>3*(angle_c q r p)\<downharpoonleft> = pi\<close>
    apply (cases \<open>(angle_c q r p) = - angle_c r p q\<close>)
     apply(simp add:f1 f2) 
     apply (metis add.commute add.right_inverse add.right_neutral angle_sum_triangle_c canon_ang_uminus_pi f0 f2 f4 f5)
    by (smt (verit) \<open>\<downharpoonright>angle_c q r p + angle_c r p q + angle_c p q r\<downharpoonleft> = pi\<close>
        \<open>angle_c q r p = angle_c p q r \<or> angle_c q r p = - angle_c p q r\<close>
        \<open>angle_c q r p = angle_c r p q \<or> angle_c q r p = - angle_c r p q\<close> canon_ang_uminus_pi
        f2)
  then have \<open>angle_c q r p = -pi/3 \<or>  angle_c q r p = pi/3\<close>
    using \<open>\<downharpoonright>3 * angle_c q r p\<downharpoonleft> = pi \<Longrightarrow> angle_c q r p = - pi / 3 \<or> angle_c q r p = pi / 3\<close> by auto
  then show \<open>\<downharpoonright>angle_c q r p\<downharpoonleft> = pi / 3 \<or> \<downharpoonright>angle_c q r p\<downharpoonleft> = - pi / 3\<close> 
    using f2 by auto
  then show \<open>angle_c q r p = angle_c p q r \<and> angle_c q r p = angle_c r p q\<close> 
    by (smt (verit, del_insts) \<open>\<downharpoonright>angle_c q r p + angle_c r p q + angle_c p q r\<downharpoonleft> = pi\<close> 
        f12 collinear_sin_neq_0 collinear_sym1 f1' f2 f4 f5 sin_pi)
qed

lemma isosceles_triangle_converse:
  assumes "angle_c a b c = angle_c c a b" "\<not>collinear a b c"
  shows   "dist a c = dist b c"
  by (metis assms(1) assms(2) cdist_def collinear_sin_neq_0 collinear_sym1 congruent_ctriangle_asa(8)
 congruent_ctriangle_asa(9) dist_complex_def law_of_sines mult_cancel_left non_collinear_independant)


lemma pi3_imp_equilateral:
  assumes \<open>q\<noteq>r\<close> \<open>p\<noteq>q\<close> \<open>r\<noteq>p\<close>
    and \<open>(angle_c q p r) = pi/3 \<or> (angle_c q p r) = -pi/3\<close> 
    and \<open>(angle_c q p r) = (angle_c r q p)\<close>
    and \<open>(angle_c q p r) = (angle_c p r q)\<close>
  shows \<open>cdist p r = cdist q r \<and> cdist p r = cdist p q\<close> 
proof(safe)
  have f0:\<open>\<not> collinear q p r\<close> 
    using assms(1-3) unfolding collinear_def 
    by (smt (verit, ccfv_SIG) arccos_one_half arcsin_one_half arcsin_plus_arccos assms(4) 
collinear_angle collinear_def divide_le_eq_1_pos divide_pos_pos minus_divide_left 
pi_def pi_gt_zero pi_half)
  then show \<open>cdist p r = cdist q r\<close>
  using isosceles_triangle_converse[of q p r] assms 
  by (simp add: dist_complex_def norm_minus_commute)
  show \<open>cdist p r = cdist p q \<close>
    using f0 isosceles_triangle_converse[of p r q] assms 
    by (metis \<open>cdist p r = cdist q r\<close> cdist_def collinear_iff dist_commute dist_norm)
qed


lemma pi3_isoscele_imp_equilateral:
  assumes \<open>q\<noteq>r\<close> \<open>p\<noteq>q\<close> "cdist q r = cdist p r" 
    and "\<downharpoonright>(angle_c q p r)\<downharpoonleft> = pi/3 \<or> \<downharpoonright>(angle_c q p r)\<downharpoonleft> = -pi/3"
  shows \<open>cdist p q = cdist r q\<close> 
proof( - )
  have f:\<open>angle_c p q r = (angle_c r p q)\<close>
    by (smt (verit, best) angle_c_commute angle_c_commute_pi assms(2) assms(3) cdist_commute 
collinear_angle isosceles_triangles orientation_respect_letter_order)
  have f0:\<open>r\<noteq>p\<close>
    using assms(1) assms(3) by force
  then have \<open>cdist q p = cdist r q\<close> 
    by (smt (verit) congruent_ctriangle_sss(19) add_divide_distrib ang_vec_bounded 
        angle_c_commute angle_c_def angle_sum_triangle_c arccos_minus_one_half arccos_one_half arcsin_minus_one_half
        arcsin_one_half arcsin_plus_arccos assms(2) assms(3) assms(4) canon_ang_id canon_ang_minus_3pi_minus_pi 
        cdist_commute field_sum_of_halves law_of_sines mult_cancel_right pi3_imp_equilateral sin_gt_zero sin_periodic_pi)
  then show \<open>cdist p q = cdist r q\<close> 
    using cdist_commute by force
qed



lemma pi3_isoscele_imp_equilateral':
  assumes \<open>q\<noteq>r\<close> \<open>p\<noteq>q\<close> "cdist q r = cdist p r" 
    and "\<downharpoonright>(angle_c q p r)\<downharpoonleft> = pi/3 \<or> \<downharpoonright>(angle_c q p r)\<downharpoonleft> = -pi/3"
  shows \<open>cdist p r = cdist p q\<close> 
  by (metis assms(2) assms(3) assms(4) cdist_commute pi3_isoscele_imp_equilateral)


lemma equilateral_caracterization:\<open>q\<noteq>r \<Longrightarrow> (cdist q r = cdist p r \<and> cdist p r = cdist p q)
\<longleftrightarrow> ((p-r) = cis(pi/3)*(q-r) \<or> (p-r) = cis(-pi/3)*(q-r))\<close>
proof(rule iffI)
  assume h: \<open>q \<noteq> r\<close> \<open>cdist q r = cdist p r \<and> cdist p r = cdist p q \<close>
  then have f1:\<open>p - r = cis (angle_c q r p) * (q - r) \<or> p - r = cis (- angle_c q r p) * (q - r)\<close>
    using isoscele_iff_pr_cis_qr by blast
  have f0:\<open>q\<noteq>r \<and> r \<noteq> p \<and> p \<noteq> q\<close> using h by auto
  have \<open>angle_c q r p = pi/3 \<or> angle_c q r p = -pi/3\<close> 
    using equilateral_imp_pi3(1)[of q r p] 
    by (metis ang_vec_bounded angle_c_def canon_ang_id h(1) h(2))
  then show \<open>p - r = cis (pi / 3) * (q - r) \<or> p - r = cis (- pi / 3) * (q - r)\<close>
    using f1 
    by (metis add.inverse_inverse minus_divide_left)
next
  assume h:\<open>q \<noteq> r\<close> \<open>p - r = cis (pi / 3) * (q - r) \<or> p - r = cis (- pi / 3) * (q - r)\<close>
  have \<open>(p-r)/(q-r) = (p-r)*cnj(q-r)/cmod(q-r)^2\<close>
    using complex_div_cnj by blast
  have f1:\<open>Re ((p-r)*cnj(q-r)) = cmod(p-r)*cmod(q-r)*cos(angle_c q r p)\<close>
    using ang_cos by force
  have f2: \<open>Im ((p-r)*cnj(q-r)) = cmod(p-r)*cmod(q-r)* sin(angle_c q r p)\<close>
    using ang_sin h(1) by auto
  then have \<open> (p-r)*cnj(q-r)/cmod(q-r)^2 = cmod(p-r)*cmod(q-r)*cis(angle_c q r p)/cmod(q-r)^2\<close>
    apply(intro complex_eqI)
    using f1 f2 by auto
  then have f3:\<open>(p-r)/(q-r) = cmod(p-r)*cmod(q-r)*cis(angle_c q r p)/cmod(q-r)^2\<close>
    by (simp add: \<open>(p - r) / (q - r) = (p - r) * cnj (q - r) / cor ((cmod (q - r))\<^sup>2)\<close>)
  have \<open>(p-r)/(q-r) = cis (angle_c q r p)\<close>
    apply(subst f3) 
    by (smt (z3) \<open>(p - r) * cnj (q - r) / cor ((cmod (q - r))\<^sup>2) = cor (cmod (p - r) * cmod (q - r))
 * cis (angle_c q r p) / cor ((cmod (q - r))\<^sup>2)\<close> cis_divide cis_mult cis_neq_zero cis_zero 
        cmod_cor_divide complex_mod_cnj eq_iff_diff_eq_0 f3 h(1) h(2) nonzero_mult_divide_mult_cancel_left 
        nonzero_mult_divide_mult_cancel_right norm_cis norm_mult numeral_One of_real_1 of_real_divide 
        power2_less_0 times_divide_eq_left)
  then have fpi:\<open>angle_c q r p = pi/3 \<or> angle_c q r p = -pi/3\<close> 
    using h ang_c_in 
    by (smt (verit, best) add_divide_distrib ang_vec_bounded angle_c_def arccos_one_half 
        arcsin_one_half arcsin_plus_arccos cis_inj diff_eq_diff_eq diff_numeral_special(9) 
        divide_nonneg_pos field_sum_of_halves nonzero_divide_eq_eq)
  then have ff:\<open>cdist p r = cdist q r\<close> 
    by (metis \<open>(p - r) / (q - r) = cis (angle_c q r p)\<close> h(1) isoscele_iff_pr_cis_qr nonzero_divide_eq_eq right_minus_eq)
  then have \<open>angle_c p q r = angle_c q p r  \<or> angle_c p q r = -angle_c q p r  \<close>
    by (metis congruent_ctriangle_sss(13) cdist_commute cdist_def norm_eq_zero right_minus_eq)
  then have f10:\<open>\<downharpoonright>angle_c p q r + angle_c q r p + angle_c r p q\<downharpoonleft> = pi\<close>
    by (metis \<open>angle_c q r p = pi / 3 \<or> angle_c q r p = - pi / 3\<close> angle_c_neq0 angle_sum_triangle_c 
        divide_eq_0_iff h(1) neg_equal_0_iff_equal pi_neq_zero zero_neq_numeral)
  then have \<open>\<downharpoonright>angle_c q p r\<downharpoonleft> = pi / 3 \<or> \<downharpoonright>angle_c q p r\<downharpoonleft> = - pi / 3\<close>
    by (smt (verit) \<open>angle_c p q r = angle_c q p r \<or> angle_c p q r = - angle_c q p r\<close> 
        add_divide_distrib ang_pos_pos ang_vec_bounded ang_vec_sym angle_c_def arccos_minus_one_half 
        arccos_one_half arcsin_minus_one_half arcsin_one_half arcsin_plus_arccos canon_ang_id 
        canon_ang_minus_3pi_minus_pi canon_ang_pi_3pi field_sum_of_halves fpi)
  show \<open>cdist q r = cdist p r \<and> cdist p r = cdist p q\<close> 
    apply(rule conjI)
    using ff apply(auto simp: norm_minus_commute)[1]
    apply(rule pi3_isoscele_imp_equilateral')
    using h(1) apply auto[1]
      apply (metis \<open>angle_c q r p = pi / 3 \<or> angle_c q r p = - pi / 3\<close> 
        angle_c_neq0 divide_eq_0_iff neg_equal_0_iff_equal pi_neq_zero zero_neq_numeral)
    using ff apply presburger
    using \<open>\<downharpoonright>angle_c q p r\<downharpoonleft> = pi / 3 \<or> \<downharpoonright>angle_c q p r\<downharpoonleft> = - pi / 3\<close> by blast
qed   

lemmas equilateral_imp_prcispi3 = equilateral_caracterization[THEN iffD1]

lemmas prcispi3_imp_equilateral = equilateral_caracterization[THEN iffD2]

lemma equilateral_caracterization_neg:
  fixes p q r::complex 
  assumes h1:\<open>p\<noteq>r\<close>
  shows \<open>(cdist p r = cdist p q \<and> cdist p q = cdist q r \<and> angle_c q r p = -pi/3)
\<longleftrightarrow> p + root3 * q + root3 ^ 2 * r = 0\<close>
proof(rule iffI)
  assume h:\<open>cdist p r = cdist p q \<and> cdist p q = cdist q r \<and> angle_c q r p = -pi/3\<close>
  then have \<open>p-r = cis(-pi/3)*(q-r)\<close> 
    using h1 isoscele_iff_pr_cis_qr[of q r p]  
    by force
  with h have \<open>p-r+cis(2*pi/3)*(q-r) = 0\<close>
    apply(simp add:cis.code)
    apply(subst sin_120)
    apply(intro complex_eqI)
    using cos_120 cos_60 sin_120 sin_60 
    by(auto simp add:field_simps) 
  then have \<open>p + root3*q - (root3+1)*r = 0\<close> by(auto simp:field_simps root3_def)
  then show \<open>p + root3 * q + root3^2 * r = 0\<close> 
    by (metis (no_types, lifting) add.commute eq_iff_diff_eq_0 left_diff_distrib 
         ring_class.ring_distribs(2) root3_eq_0)
next
  assume h:\<open>p + root3 * q + root3^2 * r = 0\<close>
  then have \<open>p + root3*q - (root3+1)*r = 0\<close> 
    by (metis add.commute add_diff_cancel_left diff_numeral_special(9) left_diff_distrib ring_class.ring_distribs(2)
        root3_eq_0)
  then have \<open>p-r+root3*(q-r) = 0\<close>
    by(auto simp:field_simps)
  have \<open>-root3 = cis(-pi/3)\<close>
    using cos_120 cos_60 sin_120 sin_60 
    by (auto intro:complex_eqI simp: root3_def)
  then have f1':\<open>p - r = cis(-pi/3)*(q-r)\<close>
    by (metis \<open>p - r + root3 * (q - r) = 0\<close> eq_neg_iff_add_eq_0 mult_minus_left)
  then have f1:\<open>p - r = cis(pi/3)*(q-r) \<or> p - r = cis(-pi/3)*(q-r)\<close>
    by auto
  then have f2:\<open>cmod (p-r) = cmod (q-r)\<close>
    by(auto simp:norm_mult) 
  then have f3:\<open>dist p r = dist q r\<close> 
    by (simp add: dist_complex_def)
  have ang_dem:\<open>angle_c q r p = -pi/3\<close>
  proof -
    have *:\<open>q\<noteq>r\<close> 
      using f2 h1 by auto
    then have **:\<open>(p - r) / (q-r) = cis(-pi/3)\<close> 
      using f1' by auto
    have ***:\<open> angle_c q r p = Arg ((p - r) /(q-r))\<close> 
      by (metis ang_vec_def angle_c_def arg_div f1' h1 mult_zero_right right_minus_eq)
    then have \<open>Arg ((p - r) /(q-r)) = \<downharpoonright>-pi/3\<downharpoonleft>\<close>
      by (simp add:arg_cis **)
    then show ?thesis using * ** *** 
      using canon_ang_id pi_ge_two by force
  qed
  have \<open>cmod (q - p) = cmod (r - q)\<close>
    using f2 
    by (metis cdist_def dist_eq_0_iff equilateral_caracterization f1' f3)
  then show \<open>cdist p r = cdist p q \<and> cdist p q = cdist q r \<and> angle_c q r p = -pi/3\<close> 
    using equilateral_caracterization[THEN iffD2, of q r p, OF _ f1]
    using f2 ang_dem by(auto simp: f2 field_simps intro!:) 
qed


end