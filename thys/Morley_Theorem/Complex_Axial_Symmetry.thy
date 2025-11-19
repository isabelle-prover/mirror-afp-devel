theory Complex_Axial_Symmetry

imports Complex_Angles Complex_Triangles

begin
section \<open>Axial symmetry in complex field\<close>

text \<open>In the following we define the axial symmetry and prove basics properties.\<close>
context
  fixes z1 z2 :: complex and \<alpha> \<beta> :: complex
  assumes neq0:\<open>z1\<noteq>z2\<close>
  defines \<open>\<alpha> \<equiv> (z1-z2)/(cnj z1 - cnj z2)\<close>
  defines \<open>\<beta>  \<equiv> (z2*cnj z1 - z1*cnj z2)/(cnj z1 - cnj z2)\<close>
begin

definition axial_symmetry::\<open>complex \<Rightarrow> complex\<close> where
  \<open>axial_symmetry z \<equiv> cnj z*(z1 - z2)/(cnj z1 - cnj z2) + (z2*cnj z1 - z1*cnj z2)/(cnj z1 - cnj z2)\<close>

lemma norm_\<alpha>_eq_1:\<open>cmod (\<alpha>) = 1\<close>
  by (auto simp: neq0 \<alpha>_def \<beta>_def)

lemma z1_inv:\<open>axial_symmetry z1 = z1\<close>
  unfolding axial_symmetry_def 
  by (metis (mono_tags, lifting) add_diff_eq add_divide_distrib complex_cnj_cancel_iff 
      diff_add_cancel eq_iff_diff_eq_0 mult.commute neq0 nonzero_eq_divide_eq right_diff_distrib') 

lemma z2_inv:\<open>axial_symmetry z2 = z2\<close>
  unfolding axial_symmetry_def 
  by (smt (z3) add_diff_cancel_left add_diff_cancel_left' add_divide_distrib axial_symmetry_def 
      complex_cnj_cancel_iff diff_add_cancel divide_divide_eq_right eq_divide_imp mult_commute_abs right_minus_eq z1_inv)

lemma cmod_axial:\<open>cmod (axial_symmetry z - axial_symmetry z') = cmod (\<alpha>*(cnj z - cnj z'))\<close>
  unfolding axial_symmetry_def 
  by (auto simp: \<alpha>_def \<beta>_def) (simp add: diff_divide_distrib mult.commute right_diff_distrib')

lemma cmod_axial_inv:\<open>cmod (axial_symmetry z - axial_symmetry z') = cmod (z - z')\<close>
  by (metis cmod_axial complex_cnj_diff complex_mod_cnj mult.commute 
      mult.right_neutral norm_\<alpha>_eq_1 norm_mult)

lemma axial_symmetry_dist1:\<open>cdist z1 z = cdist z1 (axial_symmetry z)\<close>
  by (metis cdist_def cmod_axial_inv z1_inv)

lemma axial_symmetry_dist2:\<open>cdist z2 z = dist z2 (axial_symmetry z)\<close>
  by (metis cdist_def cmod_axial_inv dist_commute dist_norm z2_inv)

lemma \<alpha>\<beta>: \<open>\<alpha>*cnj \<beta> + \<beta> = 0\<close>
  by (simp add: add_divide_eq_iff  \<alpha>_def \<beta>_def)

lemma involution_symmetry:\<open>axial_symmetry (axial_symmetry z) = z\<close>
proof -
  have \<open>\<alpha>*cnj(\<alpha>*cnj z + \<beta>) + \<beta> = \<alpha>*cnj \<alpha>*z + \<alpha>*cnj \<beta> +\<beta>\<close>
    by (simp add: ring_class.ring_distribs(1))
  then show ?thesis unfolding axial_symmetry_def
    by (smt (verit, best) \<alpha>\<beta> add.right_neutral cmod_eq_one group_cancel.add1 
        mult.commute mult_cancel_right2 norm_\<alpha>_eq_1 times_divide_eq_left \<alpha>_def \<beta>_def)
qed

lemma arg_\<alpha>:\<open>Arg \<alpha> = \<downharpoonright>2*Arg (z1-z2)\<downharpoonleft>\<close>
  unfolding \<alpha>_def \<beta>_def
  by (smt (verit, del_insts) arg_cnj_not_pi arg_div arg_pi_iff canon_ang_id canon_ang_pi_3pi 
      complex_cnj_cancel_iff complex_cnj_diff eq_cnj_iff_real eq_iff_diff_eq_0 neq0 pi_ge_two)

lemma Arg_invol:\<open>Arg (axial_symmetry (axial_symmetry z)) =  Arg z\<close>
  by (simp add: involution_symmetry)


lemma angle_sum_symmetry:\<open>z\<noteq>z1 \<Longrightarrow> \<downharpoonright>angle_c z z1 z2 + angle_c z2 z1 (axial_symmetry z)\<downharpoonleft> = angle_c z z1 (axial_symmetry z)\<close>
proof -
  assume \<open>z\<noteq>z1\<close>
  have \<open>z2-z1 \<noteq> 0\<close> using angle_c_sum neq0 by auto
  have \<open>z1 - (axial_symmetry z) \<noteq> 0\<close> 
    by (metis \<open>z \<noteq> z1\<close> eq_iff_diff_eq_0 involution_symmetry z1_inv)
  then show ?thesis
    using angle_c_sum 
    by (metis \<open>z2 - z1 \<noteq> 0\<close> right_minus_eq z1_inv)
qed

lemma angle_symmetry_eq_imp:
  assumes h:\<open>z1\<noteq>z\<close> \<open>z2\<noteq>z\<close>
  shows\<open>angle_c z z1 z2 = - angle_c (axial_symmetry z) z1 z2 \<or> angle_c z z1 z2 = angle_c (axial_symmetry z) z1 z2\<close>
  by (metis (mono_tags, lifting) axial_symmetry_dist1 cdist_def cmod_axial_inv
            congruent_ctriangle_sss(22) h(1) neq0 z2_inv)

lemma angle_symmetry:
  assumes h:\<open>z1\<noteq>z\<close> \<open>z2\<noteq>z\<close>
    and \<open>angle_c z z1 z2 = angle_c (axial_symmetry z) z1 z2\<close>
  shows \<open>z = axial_symmetry z\<close>
proof -
  have \<open>cmod (z - z1) = cmod (axial_symmetry z - z1)\<close>
    using axial_symmetry_dist1 by auto
  have \<open>cmod (z - z2) = cmod (axial_symmetry z - z2)\<close>
    by (metis axial_symmetry_dist2 cdist_def dist_commute dist_complex_def)
  have \<open>z-z1 = axial_symmetry z-z1\<close>
    by (metis \<open>cmod (z - z1) = cmod (local.axial_symmetry z - z1)\<close> ang_cos ang_sin assms(3) 
        complex_cnj_cnj complex_eq_iff eq_iff_diff_eq_0 mult_cancel_left neq0)
  then show ?thesis 
    by simp
qed

lemma line_is_inv:\<open>z\<in> line z1 z2 \<and> z\<noteq>z2 \<and> z\<noteq>z1 \<Longrightarrow> z = axial_symmetry z\<close>
proof -
  assume \<open>z\<in> line z1 z2 \<and> z\<noteq>z2 \<and> z\<noteq>z1\<close>
  then have \<open>angle_c z z1 z2 = 0 \<or> angle_c z z1 z2 = pi\<close>
    unfolding line_def using neq0 collinear_angle
    using collinear_sym1 collinear_sym2' by blast
  then show ?thesis 
    by (smt (verit) \<open>z \<in> line z1 z2 \<and> z \<noteq> z2 \<and> z \<noteq> z1\<close> 
        angle_c_commute angle_c_commute_pi angle_symmetry angle_symmetry_eq_imp)
qed

lemma dist_inv:\<open>cdist a b = cdist (axial_symmetry a) (axial_symmetry b)\<close>
  by (simp add: cmod_axial_inv)

lemma collinear_inv: assumes \<open>collinear a b c\<close> and \<open>a \<noteq> b\<and> b \<noteq> c \<and> c\<noteq>a\<close> 
  shows \<open>collinear (axial_symmetry a) (axial_symmetry b) (axial_symmetry c)\<close>
proof -
  have \<open>angle_c a b c = pi \<or> angle_c a b c = 0\<close>
    using assms(1) assms(2) collinear_angle by blast
  then have \<open>angle_c (axial_symmetry a) (axial_symmetry b) (axial_symmetry c) = angle_c a b c 
          \<or> angle_c (axial_symmetry a) (axial_symmetry b) (axial_symmetry c) = - angle_c a b c\<close>
    by (metis congruent_ctriangle_sss(24) assms(2) dist_inv minus_equation_iff)
  then show ?thesis 
    using \<open>angle_c a b c = pi \<or> angle_c a b c = 0\<close> collinear_sin_neq_0 collinear_sym1 by fastforce
qed

lemma axial_symmetry_eq_line:\<open>z\<noteq>z1 \<and> z\<noteq>z2 \<Longrightarrow> z = axial_symmetry z \<Longrightarrow> z \<in> line z1 z2\<close>
proof -
  assume \<open>z\<noteq>z1 \<and> z\<noteq>z2\<close> \<open>z = axial_symmetry z\<close>
  then have g0:\<open>z = \<alpha>*cnj z + \<beta>\<close> unfolding axial_symmetry_def 
    by (simp add: mult.commute \<alpha>_def \<beta>_def)
  then have g1:\<open>cnj z = (z-\<beta>)*cnj \<alpha> \<close>
    by (smt (verit, ccfv_threshold) add_diff_cancel complex_cnj_cnj complex_cnj_diff \<alpha>_def \<beta>_def
        complex_cnj_divide mult.commute neq0 nonzero_eq_divide_eq right_minus_eq times_divide_eq_left)
  also have g2:\<open>z = (cnj z - cnj \<beta>)*\<alpha>\<close>
    by (metis calculation complex_cnj_cnj complex_cnj_diff complex_cnj_mult)
  have \<open>\<alpha>/(z1-z2) = 1 /(cnj z1 - cnj z2)\<close>
    by (auto simp: \<alpha>_def \<beta>_def)
  have \<open>Im w = (w-cnj w)/(2*\<i>)\<close> for w
    using Im_express_cnj by blast
  then have \<open>Im (z2*cnj z1) = (z2*cnj z1 - cnj (z2*cnj z1))/(2*\<i>)\<close>
    by presburger
  then have \<open>Im (z2*cnj z1)*2*\<i> = (z2*cnj z1 - cnj z2* z1)\<close>
    by (metis complex_cnj_cnj complex_cnj_mult complex_diff_cnj mult.commute)
  have f0:\<open>(cnj z1 - cnj z2)*(z1-z2) = cmod z1^2 + cmod z2^2 - cnj z1 * z2 - cnj z2 * z1\<close>
    by (smt (verit) cancel_ab_semigroup_add_class.diff_right_commute complex_mult_cnj_cmod 
        diff_diff_eq2 left_diff_distrib mult.assoc mult.commute norm_minus_commute norm_mult of_real_add of_real_eq_iff)
  have f1:\<open>cmod z1^2 + cmod z2^2 - cnj z1 * z2 - cnj z2 * z1 = cmod z1^2 + cmod z2^2 - 2*Re z1*Re z2 - 2*Im z1*Im z2\<close>
    by(auto simp:field_simps intro:complex_eqI) 
  have \<open>\<beta> = 2*\<i>*Im (z2*cnj z1) / (cnj z1-cnj z2)\<close>
    using \<open>cor (Im (z2 * cnj z1)) = (z2 * cnj z1 - cnj (z2 * cnj z1)) / (2 * \<i>)\<close>
    unfolding \<alpha>_def \<beta>_def by auto
  then have f2:\<open>\<beta>/(z1-z2) = 2*\<i>*Im (z2*cnj z1) / ((cnj z1-cnj z2)*(z1-z2))\<close>
    by simp
  then have \<open>\<beta>/(z1-z2) = 2*\<i>*Im (z2*cnj z1) /(cmod z1^2 + cmod z2^2 - 2*Re z1*Re z2 - 2*Im z1*Im z2)\<close>
    using f0 f1 by presburger
  then have \<open>is_real ((z - z1)/(z1-z2))\<close>
    unfolding axial_symmetry_def using g2 
    by (smt (verit, del_insts) add_diff_cancel_right axial_symmetry_def complex_cnj_cnj
        complex_cnj_diff complex_cnj_divide diff_divide_distrib divide_divide_eq_right eq_cnj_iff_real
        g0 g2 mult.commute times_divide_eq_right z1_inv z2_inv \<alpha>_def \<beta>_def)
  then show \<open>z \<in> line z1 z2\<close> 
    unfolding line_def collinear_def 
    by (metis (mono_tags, lifting) Im_i_times Re_i_times cnj.simps(2) complex_i_mult_minus 
        eq_cnj_iff_real mem_Collect_eq minus_diff_eq minus_divide_right)
qed  

lemma angle_symmetry_eq:
  assumes h:\<open>z1\<noteq>z\<close> \<open>z2\<noteq>z\<close> \<open>z\<notin>line z1 z2\<close>
  shows\<open>angle_c z z1 z2 = - angle_c (axial_symmetry z) z1 z2\<close>
proof -
  have f0:\<open>angle_c z z1 z2 = - angle_c (axial_symmetry z) z1 z2 \<or>
           angle_c z z1 z2 = angle_c (axial_symmetry z) z1 z2\<close>
    using angle_symmetry_eq_imp h(1) h(2) by blast
  have f1:\<open>angle_c z z2 z1 = - angle_c (axial_symmetry z) z2 z1 
          \<or> angle_c z z2 z1 = angle_c (axial_symmetry z) z2 z1\<close>
    by (metis axial_symmetry_dist1 congruent_ctriangle_sss(24) dist_inv h(1) neq0 z2_inv)
  show ?thesis 
    using angle_symmetry axial_symmetry_eq_line f0 h(1) h(2) h(3) by presburger
qed

end
end