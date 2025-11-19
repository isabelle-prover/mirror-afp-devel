theory Morley 


imports Complex_Axial_Symmetry 

begin

section \<open>Rotations\<close>

locale complex_rotation =
  fixes A::complex and \<theta>::real
begin

definition \<open>r z = A + (z-A)*cis(\<theta>)\<close>

lemma cmod_inv_rotation:\<open>cmod (z-A) = cmod (r z - A)\<close>
  unfolding r_def 
  by (simp add: norm_mult)

lemma inner_ang:\<open>cos (\<angle> z1 z2)*(cmod z1 *cmod z2) = Re (innerprod z1 z2)\<close>
proof -
  have \<open>Re (innerprod z1 z2) = Re (scalprod z1 z2)\<close>
    unfolding innerprod_def by(auto)
  then show ?thesis 
    by (metis cos_cmod_scalprod mult.commute)
qed

lemma ang_eq_cos_theta:\<open>z\<noteq>A \<Longrightarrow> cos (angle_c z A (r z)) = cos (\<theta>)\<close>
proof -
  assume \<open>z\<noteq>A\<close>
  then have \<open>innerprod (z-A) ((r z - A)) = (z-A)*cis(\<theta>)*cnj(z - A)\<close>  
    unfolding innerprod_def r_def by auto 
  then have f0:\<open>innerprod (z-A) ((r z - A)) = cmod (z-A)^2*cis(\<theta>)\<close>
    by (metis ab_semigroup_mult_class.mult_ac(1) complex_mult_cnj_cmod mult.commute)
  then have \<open>cos (angle_c z A (r z))*cmod (z-A)*cmod(z - A) = Re (innerprod (z-A) ((r z - A)))\<close>
    unfolding angle_c_def 
    by (metis inner_ang mult.assoc cmod_inv_rotation)
  then have \<open>cos (angle_c z A (r z)) = Re (cis \<theta>)\<close>
    by (simp add: \<open>z \<noteq> A\<close> f0 power2_eq_square)
  then show ?thesis  
    by(auto simp:cis.code)
qed

lemma cdist_dist:\<open>cdist = dist\<close>
  using cdist_commute dist_complex_def by fastforce

lemma ang_eq_theta:assumes h:\<open>z\<noteq>A\<close> shows \<open>angle_c z A (r z) = \<downharpoonright>\<theta>\<downharpoonleft>\<close>
proof(cases \<open>angle_c z A (r z) = \<downharpoonright>- \<theta>\<downharpoonleft>\<close>)
  case True
  then have \<open>r z = A + (z-A)*cis(-\<theta>)\<close> 
    by (metis add_diff_cancel_left' arg_cis cdist_def cis_cmod cis_neq_zero cmod_inv_rotation 
        isoscele_iff_pr_cis_qr mult.left_commute mult.right_neutral mult_cancel_left norm_cis 
        norm_minus_commute of_real_1 r_def right_minus_eq)
  then show ?thesis 
    by (smt (verit, del_insts) True add_diff_cancel_left' angle_c_neq0 arg_cis arg_mult_eq
        canon_ang_cos canon_ang_sin cis.code cis_cnj diff_add_cancel divisors_zero r_def)
next
  case False
  have \<open>cos (angle_c z A (r z)) = cos (\<theta>)\<close>
    using ang_eq_cos_theta h by auto
  then show ?thesis 
    by (smt (verit, ccfv_threshold) cmod_inv_rotation r_def add_diff_cancel_left' angle_c_neq0 
        angle_c_sum arg_cis canon_ang_sin cdist_def cis.code cis_neq_zero divisors_zero eq_iff_diff_eq_0 h 
        isoscele_iff_pr_cis_qr nonzero_mult_div_cancel_left nonzero_mult_div_cancel_right norm_minus_commute)
qed

lemma inj_r:\<open>inj r\<close>
  unfolding inj_on_def by(auto simp:r_def)

lemma img_eqI:\<open>cdist A z1 = cdist A z2 \<and> angle_c z1 A z2 = \<theta> \<Longrightarrow> z2 = r z1\<close>
  apply(cases \<open>z1 = A \<or> z2 = A\<close>) 
  using r_def add_minus_cancel isoscele_iff_pr_cis_qr apply force
  unfolding r_def 
  by (metis add.commute cdist_commute diff_add_cancel isoscele_iff_pr_cis_qr mult.commute)

lemma r_id_iff:\<open>\<downharpoonright>\<theta>\<downharpoonleft> = 0 \<longleftrightarrow> r = id\<close>
proof -
  obtain cc :: "(complex \<Rightarrow> complex) \<Rightarrow> complex" 
    and cca :: "(complex \<Rightarrow> complex) \<Rightarrow> complex" where
    f1: "\<forall>f. (id = f \<or> f (cc f) \<noteq> cc f) \<and> ((\<forall>c. f c = c) \<or> id \<noteq> f)"
    by (metis (no_types) eq_id_iff)
  have f2: "\<forall>c ca ra. ca + (c - ca) * Complex (cos ra) (sin ra) = complex_rotation.r ca ra c"
    by (simp add: complex_rotation.r_def cis.code)
  then have "\<forall>c ca. complex_rotation.r c 0 ca = ca"
    by (metis (no_types) add_diff_cancel_left' cos_zero diff_diff_eq2 
        lambda_one mult.commute one_complex.code sin_zero)
  then show ?thesis
    using f2 f1 
    by (metis (lifting, full_types) ang_eq_theta angle_c_neq0 
        canon_ang_cos canon_ang_sin complex_i_not_zero)
qed

end


lemma axial_symmetry_eq:\<open>axial_symmetry B C P = axial_symmetry C B P\<close> if \<open>C\<noteq>B\<close> for C B P
  unfolding axial_symmetry_def[OF that] axial_symmetry_def[OF that[symmetric]] 
  by (metis (no_types, lifting) complex_cnj_cancel_iff eq_iff_diff_eq_0 
      minus_diff_eq nonzero_minus_divide_divide times_divide_eq_right)

lemma img_r_sym:
  assumes h:\<open>z1 \<noteq> z2\<close> \<open>z \<notin> line z1 z2\<close>
  shows \<open>axial_symmetry z1 z2 z = complex_rotation.r z1 (\<downharpoonright>2*angle_c z z1 z2\<downharpoonleft>) z\<close>
proof -
  interpret complex_rotation z1 "\<downharpoonright>2*angle_c z z1 z2\<downharpoonleft>" .
  let ?z = \<open>axial_symmetry z1 z2 z\<close>
  from h have \<open>z1\<noteq>z\<close> \<open>z2 \<noteq> z\<close>
    unfolding line_def Elementary_Complex_Geometry.collinear_def by(auto)
  then have \<open>angle_c ?z z1 z2 = -angle_c z z1 z2\<close>
    using angle_symmetry_eq h(1) h(2) by force
  then have \<open>angle_c z z1 ?z = \<downharpoonright>2*angle_c z z1 z2\<downharpoonleft>\<close>
    by (metis \<open>z1 \<noteq> z\<close> add.inverse_inverse angle_c_commute angle_c_commute_pi 
        angle_sum_symmetry h(1) mult_2_right mult_commute_abs)
  have \<open> cdist z1 z = cdist z1 (axial_symmetry z1 z2 z)\<close>
    using axial_symmetry_dist1 h(1) by blast
  then show ?thesis 
    apply(intro img_eqI)
    by (metis \<open>angle_c z z1 (axial_symmetry z1 z2 z) = \<downharpoonright>2 * angle_c z z1 z2\<downharpoonleft>\<close>)
qed

lemma img_r_sym':
  assumes h:\<open>z1 \<noteq> z2\<close> \<open>z\<notin>line z1 z2\<close>
  shows \<open>axial_symmetry z1 z2 z = complex_rotation.r z1 (\<downharpoonright>-2*angle_c z2 z1 z\<downharpoonleft>) z\<close>
  by (metis angle_c_commute angle_c_neq0 axial_symmetry_eq_line
            cancel_comm_monoid_add_class.diff_cancel complex_rotation.img_eqI
            complex_rotation.r_def h(1,2) img_r_sym mult_eq_0_iff mult_minus_left
            mult_minus_right pi_neq_zero two_pi_canonical)

lemma equality_for_pqr:
  assumes 1:\<open>(a2::complex)*a3\<noteq>1\<close> and 2:\<open>\<And>z. h z = a3*z + b3\<close> and 3:\<open>\<And>z. g z = a2*z + b2\<close> and 4:\<open>g (h z) = z\<close>
  shows \<open>z = (a2*b3 + b2)/(1-a2*a3)\<close>
proof -
  have f21:\<open>g (h z) = a2*a3*z + a2*b3 +b2\<close>
    using assms by(auto simp:2 3field_simps)  
  then have \<open> g (h z) = a2*a3*z + a2*b3 +b2 \<longleftrightarrow> z*(1-a2*a3) = a2*b3 + b2\<close>
    by(auto simp:field_simps 4) 
  then have \<open>a2*a3 \<noteq>1 \<Longrightarrow>  z = (a2*b3 + b2)/(1-a2*a3)\<close>
    using f21 by(auto simp:field_simps)
  then show ?thesis using 1 by auto
qed

lemma equality_for_comp:
  assumes 2:\<open>\<And>z. h z = (a3::complex)*z + b3\<close> and 3:\<open>\<And>z. g z = a2*z + b2\<close> 
    and 4:\<open>\<And>z. f z = a1*z +b1\<close> 
  shows \<open>((f\<circ>f\<circ>f)\<circ>(g\<circ>g\<circ>g)\<circ>(h\<circ>h\<circ>h)) z = (a1*a2*a3)^3*z +(a1^2+a1+1)*b1 +a1^3*(a2^2+a2+1)*b2 
+a1^3*a2^3*(a3^2+a3+1)*b3 \<close>
  using assms unfolding comp_def by(auto simp:fun_eq_iff power2_eq_square power3_eq_cube field_simps)

lemma eq_translation_id:
  assumes \<open>h = complex_rotation.r A 0\<close> \<open>h B = B\<close>
  shows \<open>h = id\<close>
  using assms(1) complex_rotation.r_id_iff by auto

lemma r_eqI: 
  assumes \<open>A = B\<close> \<open>\<theta>1 = \<theta>2\<close> 
  shows \<open>r A \<theta>1 = r B \<theta>2\<close>
  using assms(1) assms(2) by force

lemma r_eqI': 
  assumes \<open>A = B\<close> \<open>\<theta>1 = \<theta>2\<close> 
  shows \<open>r A \<theta>1 z = r B \<theta>2 z\<close>
  using assms(1) assms(2) by force

lemma composed_rotations_same_center:
  shows \<open>(complex_rotation.r A \<theta>1 \<circ> complex_rotation.r A \<theta>2) = complex_rotation.r A (\<theta>1 + \<theta>2)\<close>
  unfolding complex_rotation.r_def by (auto simp: fun_eq_iff cis_mult add_ac)


lemma composed_rotations:
  assumes h:\<open>\<downharpoonright>\<theta>1 + \<theta>2\<downharpoonleft> \<noteq> 0\<close>
  shows \<open>(complex_rotation.r A \<theta>1 \<circ> complex_rotation.r B \<theta>2) = 
           complex_rotation.r ((A*(1-cis \<theta>1) + B*cis \<theta>1*(1-cis \<theta>2))/(1-cis (\<theta>1+\<theta>2))) (\<theta>1 + \<theta>2)\<close>
proof -
  have \<open>cis (\<theta>1 + \<theta>2) \<noteq> 1\<close>
    by (metis arg_cis assms cis_zero zero_canonical)
  with h have \<open>(complex_rotation.r A \<theta>1 \<circ> complex_rotation.r B \<theta>2) 
                  ((A*(1-cis \<theta>1) + B*cis \<theta>1*(1-cis \<theta>2))/(1-cis (\<theta>1+\<theta>2)))
            = (A*(1-cis \<theta>1) + B*cis \<theta>1*(1-cis \<theta>2))/(1-cis (\<theta>1+\<theta>2)) \<close>
    unfolding complex_rotation.r_def using assms 
    by(auto simp:cis_mult field_simps  intro!:) 
  with h show ?thesis
    apply(cases \<open>\<theta>1 = 0 \<or> \<theta>2 = 0\<close>)
    unfolding complex_rotation.r_def using assms 
    by(auto simp:cis_mult field_simps fun_eq_iff diff_divide_distrib add_divide_distrib intro!:) 
qed


lemma composed_rotation_is_trans:
  assumes \<open>\<downharpoonright>\<theta>1 + \<theta>2\<downharpoonleft> = 0\<close>  
  shows \<open>(complex_rotation.r A \<theta>1 \<circ> complex_rotation.r B \<theta>2) z = z + (B - A)*(cis(\<theta>1) - 1)\<close>
  using assms  
  by (auto simp:complex_rotation.r_def add_divide_distrib diff_divide_distrib field_simps) 
    (metis add.commute canon_ang_cos canon_ang_sin cis.code cis_mult cis_zero lambda_one mult.commute)

section \<open>Morley's theorem\<close>

text \<open>We begin by proving the Morley's theorem in the case where angles are positives
then using the congruence between two triangles with the same angles only not of the same sign
we prove Morley's theorem when angles are negatives.

We then proceed to conclude because in a triangle either angles are all negatives or all the
angles are positives depending on orientation.\<close>

theorem Morley_pos:
  assumes\<open>\<not>collinear A B C\<close>
    \<open>angle_c A B R = angle_c A B C / 3\<close> (is \<open>?abr = ?abc\<close>)
    "angle_c B A R = angle_c B A C / 3" (is \<open>?bar = ?\<alpha>\<close>)
    "angle_c B C P = angle_c B C A / 3" (is \<open>?bcp = ?bca\<close>)
    "angle_c C B P = angle_c C B A / 3" (is \<open>?cbp = ?\<beta>\<close>)
    "angle_c C A Q = angle_c C A B / 3" (is \<open>?caq = ?cab\<close>)
    "angle_c A C Q = angle_c A C B / 3" (is \<open>?acq = ?\<gamma>\<close>)
    and hhh:\<open>\<downharpoonright>angle_c B A C / 3+angle_c C B A / 3+angle_c A C B / 3\<downharpoonleft> = pi/3\<close>
  shows  \<open>cdist R P = cdist P Q \<and> cdist Q R = cdist P Q\<close>
proof -
  have bundle_line:\<open>A\<notin> line B C\<close> \<open>B\<notin> line A C\<close> \<open>C \<notin> line A B\<close> \<open>A\<noteq>B\<close> \<open>B\<noteq>C\<close> \<open>C\<noteq>A\<close>
    using assms(1) non_collinear_independant by (auto simp:collinear_sym1 collinear_sym2 line_def) 
  {fix A B C \<gamma>
    assume ABC_nline:\<open>A \<notin> line B C\<close>
      and eq_3c:\<open>angle_c A C B = 3*\<gamma>\<close>
    then have neq_PI:\<open>abs \<gamma> < pi/3\<close> 
    proof - 
      have \<open>angle_c A C B \<noteq> pi\<close> 
        using ABC_nline(1) unfolding line_def  
        by (metis angle_c_commute_pi collinear_iff mem_Collect_eq non_collinear_independant)
      then have \<open>angle_c A C B \<in> {-pi<..<pi}\<close> 
        using ang_c_in less_eq_real_def by auto
      then show \<open>abs \<gamma> < pi/3\<close> 
        using eq_3c by force
    qed}note ang_inf_pi3=this
  have \<open>\<downharpoonright>angle_c B A C + angle_c C B A  + angle_c A C B\<downharpoonleft> = pi\<close>
    by (metis collinear_def add.commute 
        angle_sum_triangle_c assms(1) collinear_sym1 collinear_sym2')
  have eq_pi:\<open>\<downharpoonright>3*?\<alpha> + 3*?\<beta> + 3*?\<gamma>\<downharpoonleft> = pi\<close>
    using \<open>\<downharpoonright>angle_c B A C + angle_c C B A + angle_c A C B\<downharpoonleft> = pi\<close> by force
  then have neq_pi:\<open>\<downharpoonright>?\<beta>\<downharpoonleft> \<noteq> pi \<and> \<downharpoonright>?\<gamma>\<downharpoonleft> \<noteq> pi \<and> \<downharpoonright>?\<alpha>\<downharpoonleft> \<noteq> pi\<close>
    by (smt (verit) ang_neg_neg angle_c_commute angle_c_neq0 assms 
        canon_ang_sin collinear_angle collinear_sin_neq_0 divide_eq_0_iff divide_nonneg_pos 
        minus_divide_left pi_neq_zero sin_pi sin_pi_minus zero_canonical)
  moreover have \<open>3*?\<alpha> \<noteq> 0\<and>3*?\<beta> \<noteq> 0\<and>3*?\<gamma> \<noteq> 0\<close>
    using bundle_line collinear_sin_neq_0 line_def angle_c_commute assms(1) bundle_line(4) 
      bundle_line(5) bundle_line(6) collinear_iff assms(1) collinear_sin_neq_0 
    by (metis collinear_sym2' divide_eq_eq_numeral1(1) mem_Collect_eq mult.commute zero_neq_numeral)
  ultimately have neq_0:\<open>\<downharpoonright>?\<beta>\<downharpoonleft> \<noteq> 0 \<and> \<downharpoonright>?\<gamma>\<downharpoonleft> \<noteq> 0 \<and> \<downharpoonright>?\<alpha>\<downharpoonleft> \<noteq> 0\<close> 
    by (metis ang_vec_def angle_c_def arg_cis assms(3) assms(5) assms(7) canon_ang_arg mult_zero_right)

  interpret rot1: complex_rotation A "2*?\<alpha>" .
  interpret rot2: complex_rotation B "2*?\<beta>" .
  interpret rot3: complex_rotation C "2*?\<gamma>" .

  let ?f=\<open>rot1.r\<close>
  have f0:\<open>rot1.r A = A\<close>
    unfolding rot1.r_def by auto
  have f1:\<open>rot2.r B = B\<close>
    unfolding rot2.r_def by auto
  have f2:\<open>rot3.r C = C\<close>
    unfolding rot3.r_def by auto

  have \<open>cmod (rot3.r z - C) = cmod (z-C)\<close> for z
    using rot3.cmod_inv_rotation by presburger
  have f2:\<open>B\<noteq>C\<close> 
    by (metis collinear_def assms(1) collinear_sym1 collinear_sym2)
  have f5:\<open>angle_c C B P = ?\<beta>\<close> \<open>angle_c P B C = -?\<beta>\<close> 
    by (auto simp add: assms(5) angle_c_commute) 
      (metis angle_c_commute angle_c_commute_pi assms(5) neq_pi pi_canonical)
  then have f3:\<open>P \<notin> line C B\<close>
    by (smt (verit, ccfv_SIG) neq_0 neq_pi angle_c_commute angle_c_neq0 assms(4)
        collinear_angle divide_eq_0_iff line_def mem_Collect_eq pi_canonical zero_canonical)
  then have f3':\<open>P \<notin> line B C\<close> 
    using collinear_sym2' line_def by blast
  then have f4:\<open>P\<noteq>C \<and> P\<noteq>B\<close>
    by (metis collinear_def collinear_sym1 collinear_sym2 line_def mem_Collect_eq)
  then have \<open>angle_c P B C = - angle_c (axial_symmetry B C P) B C\<close>
    using angle_symmetry_eq[OF f2 _ _ f3'] by auto
  then have \<open>angle_c (axial_symmetry B C P) B C = ?\<beta>\<close>
    using f5(2) by fastforce

  have f13:\<open>angle_c P C B =  ?\<gamma>\<close> 
    by (smt (verit, ccfv_threshold) angle_c_commute angle_c_commute_pi assms(1) assms(4) assms(7) 
        collinear_sin_neq_0 nonzero_minus_divide_divide nonzero_minus_divide_right sin_pi)
  let ?P'= \<open>(axial_symmetry B C P)\<close>

  have \<open>angle_c (axial_symmetry B C P) B P  = \<downharpoonright>2*?\<beta>\<downharpoonleft>\<close>
    by (metis \<open>P \<noteq> C \<and> P \<noteq> B\<close> \<open>angle_c (axial_symmetry B C P) B C = angle_c C B A / 3\<close> 
        angle_sum_symmetry f2 f5(1) involution_symmetry mult.commute mult_2_right z1_inv)
  have \<open>cdist B (P) = cdist B ?P'\<close>
    by(auto)(metis cmod_axial_inv f2 z1_inv)
  then have \<open>cdist B (rot2.r P) = cdist B ?P'\<close>
    unfolding cdist_def 
    using rot2.cmod_inv_rotation by presburger
  have f16:\<open>rot2.r ?P' = P\<close> 
    by (metis \<open>angle_c (axial_symmetry B C P) B P = \<downharpoonright>2 * (angle_c C B A / 3)\<downharpoonleft>\<close>
        \<open>cdist B P = cdist B (axial_symmetry B C P)\<close> canon_ang_cos
        canon_ang_sin cis.code complex_rotation.img_eqI complex_rotation.r_def)
  have f10:\<open>angle_c P C B = \<downharpoonright>?\<gamma>\<downharpoonleft>\<close>
    by (metis \<open>angle_c P C B = angle_c A C B / 3\<close> ang_vec_def angle_c_def arg_cis canon_ang_arg)

  from f10 have f11:\<open>angle_c B C ?P' = \<downharpoonright>?\<gamma>\<downharpoonleft>\<close>
    by (metis axial_symmetry_eq \<open>P \<noteq> C \<and> P \<noteq> B\<close> \<open>angle_c P C B = angle_c A C B / 3\<close> angle_c_commute 
        angle_symmetry angle_symmetry_eq_imp axial_symmetry_eq_line canon_ang_uminus_pi f2 f3 pi_canonical)
  then have f12:\<open>angle_c P C ?P' = \<downharpoonright>2*?\<gamma>\<downharpoonleft>\<close>
    by (metis axial_symmetry_eq f13 angle_sum_symmetry f10 f2 f4 mult.commute mult_2_right)
  then have f15:\<open>rot3.r P = ?P'\<close> 
    by (metis axial_symmetry_eq canon_ang_cos canon_ang_sin cis.code f13 f2 f3 img_r_sym complex_rotation.r_def)
  have P_inv:\<open>rot2.r (rot3.r P) = P\<close>
    using f16 f15 by presburger
  let ?Q'=\<open>axial_symmetry A C Q\<close>
  have \<open>angle_c C A Q = -?\<alpha>\<close> 
    by (metis angle_c_commute assms(1) assms(6) collinear_sin_neq_0
        collinear_sym1 collinear_sym2' minus_divide_left sin_pi)
  then have \<open>angle_c Q A C = ?\<alpha>\<close>
    by (metis add.inverse_inverse angle_c_commute canon_ang_uminus_pi neq_pi pi_canonical)
  have \<open>A\<noteq>C \<and> Q\<notin>line A C\<close> 
    by (metis \<open>angle_c Q A C = angle_c B A C / 3\<close> angle_c_neq0 assms(7) collinear_angle div_0 
        f10 f13 line_def mem_Collect_eq neq_0 neq_pi zero_canonical)
  then have f17:\<open>rot1.r Q = ?Q'\<close>
    using img_r_sym[of A C Q] 
    using \<open>angle_c Q A C = angle_c B A C / 3\<close> canon_ang_cos canon_ang_sin cis.code complex_rotation.r_def 
    by presburger
  then have \<open>angle_c ?Q' C A = ?\<gamma>\<close>
    by (smt (verit, ccfv_SIG) \<open>A \<noteq> C \<and> Q \<notin> line A C\<close> \<open>angle_c Q A C = angle_c B A C / 3\<close> 
        complex_rotation.ang_eq_theta angle_c_commute angle_symmetry angle_symmetry_eq_imp assms(7) 
        axial_symmetry_eq axial_symmetry_eq_line f10 f13 complex_rotation.img_eqI neq_0 neq_pi)
  then have \<open>angle_c A C Q = ?\<gamma>\<close>
    using assms(7) by blast
  then have \<open>angle_c ?Q' C Q =\<downharpoonright>2*?\<gamma>\<downharpoonleft>\<close>
    by (metis \<open>A \<noteq> C \<and> Q \<notin> line A C\<close> \<open>angle_c (axial_symmetry A C Q) C A = angle_c A C B / 3\<close> 
        \<open>angle_c Q A C = angle_c B A C / 3\<close> angle_c_neq0 angle_sum_symmetry angle_symmetry_eq
        axial_symmetry_eq involution_symmetry mult_2_right mult_commute_abs neg_equal_0_iff_equal
        neq_0 zero_canonical)
  then have f18:\<open>rot3.r ?Q' = Q\<close> 
    using  img_r_sym[of C A ?Q']
    by (metis \<open>A \<noteq> C \<and> Q \<notin> line A C\<close> axial_symmetry_dist1 
        axial_symmetry_eq canon_ang_cos canon_ang_sin cis.code 
        complex_rotation.img_eqI complex_rotation.r_def)
  have Q_inv:\<open>rot3.r (rot1.r Q) = Q\<close>
    using f17 f18 by presburger
  let ?R'=\<open>axial_symmetry A B R\<close>
  have \<open>angle_c B A R = ?\<alpha>\<close> 
    by (simp add: assms(3))
  then have \<open>angle_c R A B = -?\<alpha>\<close>
    by (metis angle_c_commute canon_ang_uminus_pi neq_pi pi_canonical)
  have \<open>angle_c R B A = ?\<beta>\<close>
    by (metis \<open>angle_c (axial_symmetry B C P) B C = angle_c C B A / 3\<close> angle_c_commute 
        angle_c_commute_pi assms(1) assms(2) collinear_sin_neq_0 collinear_sym1 minus_divide_left sin_pi)
  have \<open>A\<noteq>B \<and> R\<notin>line A B\<close> 
    by (metis (no_types, opaque_lifting) \<open>angle_c Q A C = angle_c B A C / 3\<close> \<open>angle_c R A B = - 
(angle_c B A C / 3)\<close> angle_c_commute angle_c_commute_pi angle_c_neq0 assms(2) collinear_angle 
        collinear_sym2' diff_zero divide_eq_0_iff line_def mem_Collect_eq minus_diff_eq neg_equal_zero 
        neq_0 zero_canonical)
  then have f17:\<open>rot2.r R = ?R'\<close>
    using img_r_sym[of B A R] 
    using \<open>angle_c R B A = angle_c C B A / 3\<close> axial_symmetry_eq 
      cis.code collinear_sym2 line_def complex_rotation.r_def by auto
  then have \<open>angle_c ?R' A B = ?\<alpha>\<close>
    by (metis \<open>A \<noteq> B \<and> R \<notin> line A B\<close> \<open>angle_c R A B = - (angle_c B A C / 3)\<close> 
        \<open>angle_c R B A = angle_c C B A / 3\<close> add.inverse_inverse add.inverse_neutral angle_c_neq0 
        angle_symmetry_eq neq_0 zero_canonical)
  then have f18:\<open>rot1.r ?R' = R\<close>
    using img_r_sym[of A B ?R'] 
    by (metis \<open>A \<noteq> B \<and> R \<notin> line A B\<close> axial_symmetry_eq canon_ang_cos canon_ang_sin cis.code
        involution_symmetry line_is_inv complex_rotation.r_def z2_inv)
  have R_inv:\<open>rot1.r (rot2.r R) = R\<close>
    using f17 f18 by presburger
  let ?a1 = \<open>cis(2*?\<alpha>)\<close> let ?b1=\<open>A*(1-?a1)\<close> let ?a2=\<open>cis(2*?\<beta>)\<close> let ?b2=\<open>B*(1-?a2)\<close>
  let ?a3=\<open>cis(2*?\<gamma>)\<close> let ?b3=\<open>C*(1-?a3)\<close>
  have possi_abc:\<open>\<downharpoonright>?\<alpha>+?\<beta>+?\<gamma>\<downharpoonleft> =pi/3 \<or> \<downharpoonright>?\<alpha>+?\<beta>+?\<gamma>\<downharpoonleft> = -pi/3 \<or> \<downharpoonright>?\<alpha>+?\<beta>+?\<gamma>\<downharpoonleft> = pi\<close>
  proof -
    have \<open>\<downharpoonright>?\<alpha>+?\<beta>+?\<gamma>\<downharpoonleft>\<in>{-pi<..pi}\<close> 
      by (simp add: canon_ang(1) canon_ang(2))
    then have \<open>3*\<downharpoonright>?\<alpha>+?\<beta>+?\<gamma>\<downharpoonleft> \<in> {-3*pi<..3*pi}\<close>
      by(auto) 
    then have \<open>\<downharpoonright>\<downharpoonright>?\<alpha>+?\<beta>+?\<gamma>\<downharpoonleft>+\<downharpoonright>?\<alpha>+?\<beta>+?\<gamma>\<downharpoonleft>+\<downharpoonright>?\<alpha>+?\<beta>+?\<gamma>\<downharpoonleft>\<downharpoonleft> = \<downharpoonright>?\<alpha>+?\<beta>+?\<gamma>+?\<alpha>+?\<beta>+?\<gamma>+?\<alpha>+?\<beta>+?\<gamma>\<downharpoonleft>\<close>
      by (smt (verit, ccfv_SIG) add.commute arg_cis canon_ang_arg 
          canon_ang_sum distrib_left is_num_normalize(1) mult_2)
    then have \<open>\<downharpoonright>3*\<downharpoonright>?\<alpha>+?\<beta>+?\<gamma>\<downharpoonleft>\<downharpoonleft>=pi\<close>
      using eq_pi by argo
    then have \<open>3*\<downharpoonright>?\<alpha>+?\<beta>+?\<gamma>\<downharpoonleft> = 3*pi \<or> 3*\<downharpoonright>?\<alpha>+?\<beta>+?\<gamma>\<downharpoonleft> = -pi \<or>   3*\<downharpoonright>?\<alpha>+?\<beta>+?\<gamma>\<downharpoonleft>=pi\<close>
      by (smt (verit, del_insts) canon_ang(1) canon_ang(2) canon_ang_id
          canon_ang_minus_3pi_minus_pi canon_ang_pi_3pi)
    then show ?thesis 
      by force
  qed
  have jj:\<open>B \<notin> line C A\<close> \<open>Q \<notin> line A C\<close> \<open>R \<notin> line A B\<close>
    using assms f3' \<open>A \<noteq> C \<and> Q \<notin> line A C\<close> \<open>A \<noteq> B \<and> R \<notin> line A B\<close>  
    by (simp_all add: collinear_sym1 collinear_sym2 line_def)
  then have inf_pi3:\<open>abs ?\<alpha> < pi/3\<close> \<open>abs ?\<beta> < pi/3\<close> \<open>abs ?\<gamma> < pi/3\<close>
    using ang_inf_pi3[of B C A ?\<alpha>] ang_inf_pi3[of C A B ?\<beta>] ang_inf_pi3[of A B C ?\<gamma>] 
    by (auto simp add:collinear_sym2 collinear_sym1 assms line_def) 
  then have \<open>abs (?\<alpha>+?\<beta>+?\<gamma>) < pi\<close> 
    by argo
  have j1:\<open>\<downharpoonright>?\<alpha>+?\<beta>+?\<gamma>\<downharpoonleft> = pi/3 \<Longrightarrow> ?a1*?a2*?a3 = root3\<close> 
  proof -
    assume hh:\<open>\<downharpoonright>?\<alpha>+?\<beta>+?\<gamma>\<downharpoonleft> = pi/3\<close>
    have f20:\<open>cis (2 * (angle_c B A C / 3)) * cis (2 * (angle_c C B A / 3)) * cis (2 * (angle_c A C B / 3))
  = cis (2*(?\<alpha>+?\<beta>+?\<gamma>))\<close> 
      by (simp add: cis_mult)
    then have f21:\<open>cis (2*(\<downharpoonright>?\<alpha>+?\<beta>+?\<gamma>\<downharpoonleft>)) = cis (2*(?\<alpha>+?\<beta>+?\<gamma>))\<close>
      by (smt (verit, ccfv_threshold) canon_ang_cos canon_ang_sin canon_ang_sum cis.code)  
    with hh show ?thesis 
      by (metis (no_types, opaque_lifting) f21  f20 times_divide_eq_right root3_def)
  qed
  have \<open>rot1.r\<circ>rot1.r = complex_rotation.r A (4*?\<alpha>)\<close>
    using composed_rotations_same_center  by auto
  have g10:\<open>((rot1.r\<circ>rot1.r\<circ>rot1.r)\<circ>(rot2.r\<circ>rot2.r\<circ>rot2.r)\<circ>(rot3.r \<circ>rot3.r\<circ>rot3.r))  = 
             complex_rotation.r A (6*?\<alpha>) \<circ> complex_rotation.r B (6*?\<beta>) \<circ> complex_rotation.r C (6*?\<gamma>)\<close>
    using composed_rotations_same_center by auto
  have f26:\<open>\<downharpoonright>6*?\<alpha> + 6*?\<beta> + 6*?\<gamma>\<downharpoonleft> = 0\<close> 
    by (smt (verit, ccfv_SIG) canon_ang_sum eq_pi two_pi_canonical)
  also have \<open>\<downharpoonright>6*?\<gamma>\<downharpoonleft> \<noteq> 0\<close>
  proof (rule ccontr)
    assume \<open>\<not> \<downharpoonright>6 * (angle_c A C B / 3)\<downharpoonleft> \<noteq> 0\<close>
    then obtain k::int where  \<open>6 * \<downharpoonright>(angle_c A C B / 3)\<downharpoonleft> = 2*k*pi\<close>
      by (metis add.commute add.inverse_neutral add_0 canon_ang(3) 
          diff_conv_add_uminus f10 f13 of_int_mult of_int_numeral)
    then have \<open>3*\<downharpoonright>(angle_c A C B / 3)\<downharpoonleft> = k*pi\<close> 
      by force
    then show False 
      by (metis (no_types, opaque_lifting) assms(1) collinear_sin_neq_0 divide_eq_eq_numeral1(1)
          f10 f13 mult_1 sin_kpi times_divide_eq_left zero_neq_numeral)
  qed
  then have f24:\<open>\<downharpoonright>6*?\<alpha> + 6*?\<beta>\<downharpoonleft> \<noteq> 0\<close> 
    by (metis add.commute add.right_neutral arg_cis calculation
        canon_ang_cos canon_ang_sin canon_ang_sum cis.code)
  let ?A1=\<open>(A*(1-cis (6*?\<alpha>)) + B*cis (6*?\<alpha>)*(1-cis (6*?\<beta>)))/(1-cis (6*?\<beta>+6*?\<alpha>))\<close>
  have g11:\<open>complex_rotation.r A (6*?\<alpha>) \<circ> complex_rotation.r B (6*?\<beta>) \<circ> complex_rotation.r C (6*?\<gamma>) =
            complex_rotation.r ?A1 (6*?\<alpha> + 6*?\<beta>)\<circ> complex_rotation.r C (6*?\<gamma>) \<close>
    using composed_rotations[of \<open>6*?\<alpha>\<close> \<open>6*?\<beta>\<close> A B, OF f24]  
    by argo
  then have f27:\<open>complex_rotation.r ?A1 (6*?\<alpha> + 6*?\<beta>)\<circ> complex_rotation.r C (6*?\<gamma>) = (\<lambda>z. z + (C -
     (A * (1 - cis (6 * (angle_c B A C / 3))) + B * cis (6 * (angle_c B A C / 3)) * (1 - cis (6 * (angle_c C B A / 3)))) /
     (1 - cis (6 * (angle_c C B A / 3) + 6 * (angle_c B A C / 3)))) *
    (cis (6 * (angle_c B A C / 3) + 6 * (angle_c C B A / 3)) - 1))\<close> (is \<open>?l = (\<lambda>z. z + ?A2)\<close>)
    using composed_rotation_is_trans[of \<open>6*?\<alpha> + 6*?\<beta>\<close> \<open>6*?\<gamma>\<close> ?A1 C, OF f26] 
    by auto
  have f30:\<open>2*angle_c A C B = 6*?\<gamma>\<close>
    by auto
  have \<open>axial_symmetry C B A = complex_rotation.r C (\<downharpoonright>2*angle_c A C B\<downharpoonleft>) A\<close>
    using img_r_sym collinear_sym1 f2 jj(1) line_def by auto
  then have first:\<open>complex_rotation.r C (6*?\<gamma>) A = axial_symmetry C B A\<close> (is \<open>?rr = ?axA\<close>)
    using canon_ang_cos canon_ang_sin cis.code f30 complex_rotation.r_def by presburger
  have f31:\<open>axial_symmetry B C ?axA = complex_rotation.r B (\<downharpoonright>2*angle_c ?axA B C\<downharpoonleft>) ?axA\<close>
    by (metis \<open>A \<noteq> C \<and> Q \<notin> line A C\<close> \<open>\<downharpoonright>6 * (angle_c A C B / 3)\<downharpoonleft> \<noteq> 0\<close>
        \<open>complex_rotation.r C (6 * (angle_c A C B / 3)) A = axial_symmetry C B A\<close> 
        complex_rotation.ang_eq_theta angle_c_neq0 
        axial_symmetry_eq f2 img_r_sym involution_symmetry line_is_inv z1_inv)
  have f32:\<open>angle_c C B A = 3*?\<beta>\<close>
    by simp
  then have f33:\<open>angle_c ?axA B C = 3*?\<beta>\<close>
    by (smt (verit) \<open>A \<noteq> B \<and> R \<notin> line A B\<close> \<open>A \<noteq> C \<and> Q \<notin> line A C\<close> \<open>\<downharpoonright>6 * (angle_c A C B / 3)\<downharpoonleft> \<noteq> 0\<close> 
        \<open>complex_rotation.r C (6 * (angle_c A C B / 3)) A = axial_symmetry C B A\<close> 
        complex_rotation.ang_eq_theta angle_c_commute angle_c_neq0 angle_symmetry_eq assms(1) 
        axial_symmetry_eq collinear_sin_neq_0 collinear_sym1 f2 line_is_inv sin_pi)
  then have snd:\<open>complex_rotation.r B (6*?\<beta>) ((axial_symmetry B C A)) = A\<close>
    by (smt (verit, ccfv_SIG) \<open>A \<noteq> C \<and> Q \<notin> line A C\<close> \<open>\<downharpoonright>6 * (angle_c A C B / 3)\<downharpoonleft> \<noteq> 0\<close> 
        \<open>complex_rotation.r C (6 * (angle_c A C B / 3)) A = axial_symmetry C B A\<close> 
        complex_rotation.ang_eq_theta angle_c_neq0 axial_symmetry_eq canon_ang_cos canon_ang_sin
        cis.code f2 img_r_sym involution_symmetry line_is_inv complex_rotation.r_def z1_inv)
  then have thrd:\<open>complex_rotation.r A (6*?\<alpha>) A = A\<close>
    unfolding complex_rotation.r_def by auto
  then have \<open>(complex_rotation.r A (6*?\<alpha>) \<circ> complex_rotation.r B (6*?\<beta>) \<circ> complex_rotation.r C (6*?\<gamma>)) A = A\<close>
    apply(simp) 
    by (smt (verit, best) axial_symmetry_eq f30 f32 first snd)
  then have g21:\<open>((rot1.r\<circ>rot1.r\<circ>rot1.r)\<circ>(rot2.r\<circ>rot2.r\<circ>rot2.r)\<circ>(rot3.r \<circ>rot3.r\<circ>rot3.r)) = (\<lambda>z. z + ?A2)\<close>
    apply(subst g10) apply(subst g11) apply(subst f27) by(simp add:fun_eq_iff) 
  then have \<open>?A2 = 0\<close>
    by (metis \<open>(complex_rotation.r A (6 * (angle_c B A C / 3)) \<circ>
                complex_rotation.r B (6 * (angle_c C B A / 3)) \<circ> 
                complex_rotation.r C (6 * (angle_c A C B / 3))) A = A\<close> 
        add_diff_cancel_left' cancel_comm_monoid_add_class.diff_cancel g10)
  then have g22:\<open>((rot1.r\<circ>rot1.r\<circ>rot1.r)\<circ>(rot2.r\<circ>rot2.r\<circ>rot2.r)\<circ>(rot3.r \<circ>rot3.r\<circ>rot3.r)) = id\<close>
    using g21 by(auto simp:fun_eq_iff)
  have g20:\<open>rot1.r z = ?a1*z +?b1\<close> \<open>rot2.r z =?a2*z + ?b2\<close> \<open>rot3.r z = ?a3 * z + ?b3\<close> for z
    by(auto simp:field_simps complex_rotation.r_def) 
  then  have \<open>((rot1.r\<circ>rot1.r\<circ>rot1.r)\<circ>(rot2.r\<circ>rot2.r\<circ>rot2.r)\<circ>(rot3.r \<circ>rot3.r\<circ>rot3.r)) z = (cis (2 * (angle_c B A C / 3)) * cis (2 * (angle_c C B A / 3))
 * cis (2 * (angle_c A C B / 3))) ^ 3 * z +
    ((cis (2 * (angle_c B A C / 3)))\<^sup>2 + cis (2 * (angle_c B A C / 3)) + 1) * (A * (1 - cis (2 * (angle_c B A C / 3)))) +
    cis (2 * (angle_c B A C / 3)) ^ 3 * ((cis (2 * (angle_c C B A / 3)))\<^sup>2 + cis (2 * (angle_c C B A / 3)) + 1) *
    (B * (1 - cis (2 * (angle_c C B A / 3)))) +
    cis (2 * (angle_c B A C / 3)) ^ 3 * cis (2 * (angle_c C B A / 3)) ^ 3 *
    ((cis (2 * (angle_c A C B / 3)))\<^sup>2 + cis (2 * (angle_c A C B / 3)) + 1) *
    (C * (1 - cis (2 * (angle_c A C B / 3))))\<close> (is \<open>?l z = ?A3 z\<close>) for z 
    using equality_for_comp[of rot3.r ?a3 ?b3 rot2.r ?a2 ?b2 rot1.r ?a1 ?b1, OF g20(3) g20(2) g20(1)] 
    by blast
  then have \<open>z = ?A3 z\<close> for z 
    by (metis g22 id_apply)
  then have very_imp:\<open>((cis (2 * (angle_c B A C / 3)))\<^sup>2 + cis (2 * (angle_c B A C / 3)) + 1) * (A * (1 - cis (2 * (angle_c B A C / 3)))) +
    cis (2 * (angle_c B A C / 3)) ^ 3 * ((cis (2 * (angle_c C B A / 3)))\<^sup>2 + cis (2 * (angle_c C B A / 3)) + 1) *
    (B * (1 - cis (2 * (angle_c C B A / 3)))) +
    cis (2 * (angle_c B A C / 3)) ^ 3 * cis (2 * (angle_c C B A / 3)) ^ 3 *
    ((cis (2 * (angle_c A C B / 3)))\<^sup>2 + cis (2 * (angle_c A C B / 3)) + 1) *
    (C * (1 - cis (2 * (angle_c A C B / 3)))) = 0\<close> 
    by (metis comm_monoid_add_class.add_0 mult_zero_class.mult_zero_right)
  {assume hhh:\<open>\<downharpoonright>?\<alpha>+?\<beta>+?\<gamma>\<downharpoonleft> = pi/3\<close>
    have j5:\<open>?a1*?a2 \<noteq>1\<close>
    proof(rule ccontr)
      assume \<open>\<not> cis (2 * (angle_c B A C / 3)) * cis (2 * (angle_c C B A / 3)) \<noteq> 1\<close>
      then have \<open>?a1*?a2 = cis 0\<close> 
        using cis_zero by presburger
      then have \<open>\<downharpoonright>2*(?\<alpha>+?\<beta>)\<downharpoonleft> = 0\<close> 
        by (metis arg_cis cis_mult distrib_left zero_canonical)
      then have t:\<open>\<downharpoonright>?\<alpha>+?\<beta>\<downharpoonleft> = pi \<or> \<downharpoonright>?\<alpha>+?\<beta>\<downharpoonleft> = 0\<close>
        by (smt (verit, del_insts) canon_ang(1) canon_ang_id canon_ang_sum canon_ang_uminus)
      then have \<open>\<downharpoonright>?\<alpha>+?\<beta>\<downharpoonleft> = 0 \<Longrightarrow> False\<close> 
        by (metis add_0 assms(1) canon_ang_sum collinear_sin_neq_0 
            divide_cancel_right f10 f13 hhh sin_pi zero_neq_numeral)
      then have \<open>\<downharpoonright>1/3*(3*?\<alpha>+3*?\<beta>)\<downharpoonleft>=pi\<close> using t by(auto simp:algebra_simps)
      then have \<open>\<downharpoonright>(pi-\<downharpoonright>3*?\<gamma>\<downharpoonleft>)\<downharpoonleft> = \<downharpoonright>(3*?\<alpha>+3*?\<beta>)\<downharpoonleft>\<close> 
        by (smt (verit, ccfv_SIG) canon_ang_diff eq_pi)
      then have \<open>\<downharpoonright>(pi/3-\<downharpoonright>?\<gamma>\<downharpoonleft>)\<downharpoonleft> = pi\<close>
        by (smt (verit, best) \<open>\<downharpoonright>angle_c B A C / 3 + angle_c C B A / 3\<downharpoonleft> = 0 \<Longrightarrow> False\<close>
            canon_ang_diff hhh t)
      then have \<open>\<downharpoonright>?\<gamma>\<downharpoonleft> \<in> {0<..<pi/3}\<close> 
        by (smt (verit, ccfv_SIG) add_divide_distrib ang_vec_bounded angle_c_def 
            arccos_minus_one_half arccos_one_half arcsin_minus_one_half arcsin_one_half 
            arcsin_plus_arccos canon_ang_id canon_ang_pi_3pi divide_cancel_right f13 field_sum_of_halves)
      then show False 
        using \<open>\<downharpoonright>pi / 3 - \<downharpoonright>angle_c A C B / 3\<downharpoonleft>\<downharpoonleft> = pi\<close> add_divide_distrib canon_ang_id by auto
    qed
    have r_eq_all:\<open>rot1.r z = ?a1*z + ?b1\<close> \<open>rot2.r z = ?a2*z + ?b2\<close> \<open>rot3.r z = ?a3*z+?b3\<close> for z
      by(auto simp:field_simps complex_rotation.r_def cis.code) 
    have f21:\<open>rot2.r (rot3.r P) = ?a2*?a3*P + ?a2*?b3 +?b2\<close>
      apply(subst r_eq_all(2)) apply(subst r_eq_all(3)) by(auto simp:field_simps) 

    then have \<open> rot2.r (rot3.r P) = ?a2*?a3*P + ?a2*?b3 +?b2 \<longleftrightarrow> P*(1-?a2*?a3) = ?a2*?b3 + ?b2\<close>
      by (smt (verit) add.commute add_diff_cancel_left' add_diff_eq f15 
f16 mult.commute mult.right_neutral right_diff_distrib')
    then have j2:\<open>?a2*?a3 \<noteq>1 \<Longrightarrow>  P = (?a2*?b3 + ?b2)/(1-?a2*?a3)\<close>
      using f21 by(auto simp:field_simps) 
    have j4:\<open>?a1*?a3 \<noteq> 1\<close>
    proof(rule ccontr)
      assume \<open>\<not> cis (2 * (angle_c B A C / 3)) * cis (2 * (angle_c A C B / 3)) \<noteq> 1\<close>
      then have \<open>?a1*?a3 = cis 0\<close> 
        using cis_zero by presburger
      then have \<open>\<downharpoonright>2*(?\<alpha>+?\<gamma>)\<downharpoonleft> = 0\<close> 
        by (metis arg_cis cis_mult distrib_left zero_canonical)
      then have t:\<open>\<downharpoonright>?\<alpha>+?\<gamma>\<downharpoonleft> = pi \<or> \<downharpoonright>?\<alpha>+?\<gamma>\<downharpoonleft> = 0\<close>
        by (smt (verit, del_insts) canon_ang(1) canon_ang_id canon_ang_sum canon_ang_uminus)
      then have k0:\<open>\<downharpoonright>?\<alpha>+?\<gamma>\<downharpoonleft> = 0 \<Longrightarrow> False\<close> 
        by (smt (verit, ccfv_SIG) \<open>A \<noteq> B \<and> R \<notin> line A B\<close> \<open>A \<noteq> C \<and> Q \<notin> line A C\<close> 
            \<open>\<bar>angle_c B A C / 3 + angle_c C B A / 3 + angle_c A C B / 3\<bar> < pi\<close> 
            \<open>angle_c (axial_symmetry A B R) A B = angle_c B A C / 3\<close> \<open>angle_c R A B = - (angle_c B A C / 3)\<close> 
            \<open>angle_c R B A = angle_c C B A / 3\<close> ang_pos_pos assms(3) canon_ang_id f2 f30 f32 neq_0 z1_inv)

      then have \<open>\<downharpoonright>1/3*(3*?\<alpha>+3*?\<gamma>)\<downharpoonleft>=pi\<close> using t by(auto simp:algebra_simps)
      then have \<open>\<downharpoonright>(pi-\<downharpoonright>3*?\<beta>\<downharpoonleft>)\<downharpoonleft> = \<downharpoonright>(3*?\<alpha>+3*?\<gamma>)\<downharpoonleft>\<close> 
        by (smt (verit, ccfv_SIG) canon_ang_diff eq_pi)
      then have \<open>\<downharpoonright>(pi/3-\<downharpoonright>?\<beta>\<downharpoonleft>)\<downharpoonleft> = pi\<close>
        by (smt (verit, best) k0
            canon_ang_diff hhh t)
      then have k1:\<open>\<downharpoonright>?\<beta>\<downharpoonleft> \<in> {0<..<pi/3}\<close> 
        by (smt (verit, del_insts) arccos_one_half arcsin_one_half arcsin_plus_arccos
            canon_ang_id divide_nonneg_pos field_sum_of_halves inf_pi3(2) pi_ge_zero)
      then show False 
        using k1 add_divide_distrib canon_ang_id \<open>\<downharpoonright>pi / 3 - \<downharpoonright>angle_c C B A / 3\<downharpoonleft>\<downharpoonleft> = pi\<close> by auto
    qed
    have j3:\<open>?a2*?a3 \<noteq> 1\<close>
    proof(rule ccontr)
      assume \<open>\<not> cis (2 * (angle_c C B A / 3)) * cis (2 * (angle_c A C B / 3)) \<noteq> 1\<close>
      then have \<open>?a2*?a3 = cis 0\<close> 
        using cis_zero by presburger
      then have \<open>\<downharpoonright>2*(?\<beta>+?\<gamma>)\<downharpoonleft> = 0\<close> 
        by (metis arg_cis cis_mult distrib_left zero_canonical)
      then have t:\<open>\<downharpoonright>?\<beta>+?\<gamma>\<downharpoonleft> = pi \<or> \<downharpoonright>?\<beta>+?\<gamma>\<downharpoonleft> = 0\<close>
        by (smt (verit, del_insts) canon_ang(1) canon_ang_id canon_ang_sum canon_ang_uminus)
      then have k0:\<open>\<downharpoonright>?\<beta>+?\<gamma>\<downharpoonleft> = 0 \<Longrightarrow> False\<close> 
        by (smt (verit, ccfv_SIG) \<open>A \<noteq> B \<and> R \<notin> line A B\<close> \<open>A \<noteq> C \<and> Q \<notin> line A C\<close> 
            \<open>\<bar>angle_c B A C / 3 + angle_c C B A / 3 + angle_c A C B / 3\<bar> < pi\<close> 
            \<open>angle_c (axial_symmetry A B R) A B = angle_c B A C / 3\<close> \<open>angle_c R A B = - (angle_c B A C / 3)\<close> 
            \<open>angle_c R B A = angle_c C B A / 3\<close> ang_pos_pos assms(3) canon_ang_id f2 f30 f32 neq_0 z1_inv)

      then have \<open>\<downharpoonright>1/3*(3*?\<beta>+3*?\<gamma>)\<downharpoonleft>=pi\<close> using t by(auto simp:algebra_simps)
      then have \<open>\<downharpoonright>(pi-\<downharpoonright>3*?\<alpha>\<downharpoonleft>)\<downharpoonleft> = \<downharpoonright>(3*?\<beta>+3*?\<gamma>)\<downharpoonleft>\<close> 
        by (smt (verit, ccfv_SIG) canon_ang_diff eq_pi)
      then have \<open>\<downharpoonright>(pi/3-\<downharpoonright>?\<alpha>\<downharpoonleft>)\<downharpoonleft> = pi\<close>
        by (smt (verit, best) k0
            canon_ang_diff hhh t)
      then have k1:\<open>\<downharpoonright>?\<alpha>\<downharpoonleft> \<in> {0<..<pi/3}\<close> 
        by (smt (verit, del_insts) arccos_one_half arcsin_one_half arcsin_plus_arccos
            canon_ang_id divide_nonneg_pos field_sum_of_halves inf_pi3(1) pi_ge_zero)
      then show False 
        using k1 add_divide_distrib canon_ang_id \<open>\<downharpoonright>(pi/3-\<downharpoonright>?\<alpha>\<downharpoonleft>)\<downharpoonleft> = pi\<close> by auto
    qed
    have f21':\<open>rot3.r (rot1.r Q) = ?a3*?a1*Q + ?a3*?b1 +?b3\<close>
      apply(subst r_eq_all(1)) apply(subst r_eq_all(3)) by(auto simp:field_simps) 
    have f21'':\<open>rot1.r (rot2.r R) = ?a1*?a2*R + ?a1*?b2 +?b1\<close>
      apply(subst r_eq_all(1)) apply(subst r_eq_all(2)) by(auto simp:field_simps) 
    have jjj:\<open>?a1 \<noteq> 0 \<and> ?a2 \<noteq> 0 \<and> ?a3 \<noteq> 0\<close>
      using cis_neq_zero by blast
    then have eq_j:\<open>?a1*?a2*?a3 = root3\<close> 
      using j1 hhh by blast
    then have P_def:\<open>P = (?a2*?b3 + ?b2)/(1-?a2*?a3)\<close>(is \<open>_=?P\<close>)
      using j2 j3 by blast
    have n1: \<open>1-?a2*?a3 = (?a1 - root3)/?a1\<close>
      by (smt (verit, ccfv_threshold) cis_divide cis_times_cis_opposite cis_zero
          diff_divide_distrib eq_j minus_real_def mult_1 times_divide_eq_left)
    then have P_last:\<open>P = ?a1*(?a2*?b3 + ?b2)/(?a1-root3)\<close> 
      using P_def jjj by (simp add: )
    then have Q_def:\<open>Q = (?a3*?b1 + ?b3)/(1-?a3*?a1)\<close> (is \<open>_=?Q\<close>)
      using f21' j4 Q_inv by(auto simp:field_simps)  
    have n2: \<open>1-?a3*?a1 = (?a2 - root3)/?a2\<close>
      by (smt (verit, ccfv_threshold) cis_divide cis_times_cis_opposite cis_zero
          diff_divide_distrib eq_j minus_real_def mult_1 times_divide_eq_left)
    then have Q_last:\<open>Q = ?a2*(?a3*?b1 + ?b3)/(?a2-root3)\<close> 
      using Q_def jjj by simp
    then have R_def:\<open>R = (?a1*?b2 + ?b1)/(1-?a1*?a2)\<close> (is \<open>_=?R\<close>)
      using f21'' j5 R_inv by(auto simp:field_simps) 
    have n3:\<open>1-?a1*?a2 = (?a3 - root3)/?a3\<close>
      by (smt (verit, ccfv_threshold) cis_divide cis_times_cis_opposite cis_zero
          diff_divide_distrib eq_j minus_real_def mult_1 times_divide_eq_left)
    then have R_last:\<open>R = ?a3*(?a1*?b2 + ?b1)/(?a3-root3)\<close> 
      using R_def jjj by simp
    have \<open>?a1 - root3 \<noteq> 0 \<and> ?a2-root3\<noteq>0 \<and> ?a3-root3 \<noteq> 0\<close> 
      using eq_j j3 j4 j5 by auto
    have rule_s:\<open>c \<noteq> 0 \<Longrightarrow> a/c + b/c = (a+b)/c\<close> for a b c::real
      by argo
    define j' where 
      defs: \<open>j'\<equiv>root3\<close>
    have simp_rules_for_eq:\<open>P = (?a2*?b3 + ?b2)/(1-?a2*?a3)\<close> \<open>R = (?a1*?b2 + ?b1)/(1-?a1*?a2)\<close> 
      \<open>Q = (?a3*?b1 + ?b3)/(1-?a1*?a3)\<close> \<open>1-?a1*?a2 \<noteq> 0 \<and> 1-?a2*?a3\<noteq>0 \<and> 1-?a1*?a3 \<noteq> 0\<close> 
      \<open>?a1*?a2*?a3 = j' \<close> 
      \<open>1 + j' +j'^2 = 0\<close> \<open>((1 - ?a1 * ?a3) * ((1 - ?a1 * ?a2) * (1 - ?a2 * ?a3)))\<noteq>0\<close>
      \<open>j'^3 = 1\<close> \<open>j'*j'*j' = 1\<close> \<open>?a1\<noteq>0\<close> \<open>?a2\<noteq>0\<close> \<open>?a3\<noteq>0\<close>
      \<open>(1-?a1*?a2)*?a3 = (?a3-j')\<close> \<open>(1-?a2*?a3)*?a1 = (?a1-j')\<close> \<open>(1-?a1*?a3)*?a2 = (?a2-j')\<close>
      using Q_def P_def R_def eq_j j3 jjj j4 j5 root3_eq_0  root_unity_3  n1 n2 n3 
      by(auto simp add:mult.commute power3_eq_cube defs root3_def)   
    have graal:\<open>(?a1^2+?a1+1)*?b1 + ?a1^3*(?a2^2+?a2+1)*?b2 +?a1^3*?a2^3*(?a3^2+?a3+1)*?b3 =
      -j'*?a1^2*?a2*(?a1-j')*(?a2-j')*(?a3-j')*(?R +j'*?P +j'^2*?Q)\<close>
      using root_unity_carac[of ?a1 ?a2 ?a3 j' ?R ?b2 ?b1 ?P ?b3 ?Q]
      using simp_rules_for_eq  defs by(auto simp:) 
    then have \<open>(?a1^2+?a1+1)*?b1 + ?a1^3*(?a2^2+?a2+1)*?b2 +?a1^3*?a2^3*(?a3^2+?a3+1)*?b3 = 0\<close> 
      unfolding defs using very_imp by auto
    then have \<open>(?R +j'*?P +j'^2*?Q) = 0\<close>
      using graal simp_rules_for_eq(13) simp_rules_for_eq(14) 
        simp_rules_for_eq(15) simp_rules_for_eq(11) simp_rules_for_eq(12) simp_rules_for_eq(4) by force
    then have impp:\<open>R +j'*P +j'^2*Q = 0\<close>
      using R_def P_def Q_def 
      by (metis simp_rules_for_eq(1) simp_rules_for_eq(2) )
    have neq_all:\<open>A\<noteq>B \<and> B\<noteq>C \<and> C\<noteq>A\<close>
      using \<open>A \<noteq> B \<and> R \<notin> line A B\<close> \<open>A \<noteq> C \<and> Q \<notin> line A C\<close> f2 by argo
    have \<open>R \<noteq> Q\<close> 
    proof (rule ccontr)
      assume \<open>\<not> R \<noteq> Q\<close>
      then have q1:\<open>angle_c A B R =  angle_c A B Q\<close>
        \<open>angle_c B A R = angle_c B A Q\<close> \<open>angle_c C A Q = angle_c C A R\<close>
        \<open>angle_c A C Q = angle_c A C R\<close> 
        using assms by auto
      then have \<open>angle_c B A R = ?\<alpha>\<close> using assms by auto
      then have \<open>angle_c B A Q = ?\<alpha>\<close> 
        using q1 by auto
      then have \<open>angle_c A B Q = angle_c A B R + angle_c R B Q\<close>
        using \<open>\<not> R \<noteq> Q\<close> angle_c_neq0 by auto
      have \<open>angle_c C A B = - 3*?\<alpha>\<close> using assms 
        using \<open>angle_c C A Q = - (angle_c B A C / 3)\<close> by argo
      then have \<open>angle_c (axial_symmetry B A R) A B = ?\<alpha>\<close> 
        by (metis \<open>angle_c (axial_symmetry A B R) A B = angle_c B A C / 3\<close> axial_symmetry_eq)
      have \<open>C - A \<noteq> 0 \<and> Q - A \<noteq> 0 \<and>A - R \<noteq> 0 \<and> A - B \<noteq> 0\<close> 
        using \<open>A \<noteq> C \<and> Q \<notin> line A C\<close> \<open>angle_c A B Q = angle_c A B R + angle_c R B Q\<close>
          \<open>angle_c R B A = angle_c C B A / 3\<close> neq_0 q1(1) neq_all by fastforce
      then have \<open>angle_c C A B = angle_c C A Q + angle_c Q A R + angle_c R A B\<close> 
        using angle_c_sum[of C A Q R]  angle_c_sum[of C A R B] 
        by (smt (verit) \<open>\<not> R \<noteq> Q\<close> \<open>angle_c C A B = - 3 * (angle_c B A C / 3)\<close>
            \<open>angle_c C A Q = - (angle_c B A C / 3)\<close> \<open>angle_c R A B = - (angle_c B A C / 3)\<close>
            angle_c_neq0 canon_ang(1) canon_ang(2) canon_ang_id)
      then show False 
        using \<open>\<not> R \<noteq> Q\<close> 
        by (smt (verit, best) \<open>angle_c C A B = - 3 * (angle_c B A C / 3)\<close> 
            \<open>angle_c C A Q = - (angle_c B A C / 3)\<close> \<open>angle_c R A B = - (angle_c B A C / 3)\<close>
            angle_c_neq0 neq_0 zero_canonical)
    qed
    then have \<open>cdist R P = cdist R Q \<and> cdist R Q = cdist Q P\<close> 
      using equilateral_caracterization_neg[of R Q P] impp unfolding defs 
      by (metis cdist_commute)
    then have ?thesis 
      using cdist_commute by auto
  }note case_pi3=this
  then show ?thesis using hhh by auto
qed

theorem Morley_neg: 
  assumes\<open>\<not>collinear A B C\<close>
    \<open>angle_c A B R = angle_c A B C / 3\<close> (is \<open>?abr = ?abc\<close>)
    "angle_c B A R = angle_c B A C / 3" (is \<open>?bar = ?\<alpha>\<close>)
    "angle_c B C P = angle_c B C A / 3" (is \<open>?bcp = ?bca\<close>)
    "angle_c C B P = angle_c C B A / 3" (is \<open>?cbp = ?\<beta>\<close>)
    "angle_c C A Q = angle_c C A B / 3" (is \<open>?caq = ?cab\<close>)
    "angle_c A C Q = angle_c A C B / 3" (is \<open>?acq = ?\<gamma>\<close>)
    and hhh:\<open>\<downharpoonright>angle_c B A C / 3+angle_c C B A / 3+angle_c A C B / 3\<downharpoonleft> = -pi/3\<close>
  shows  \<open>cdist R P = cdist P Q \<and> cdist Q R = cdist P Q\<close>
proof -
  have \<open>\<downharpoonright>-angle_c B A C / 3+-angle_c C B A / 3+-angle_c A C B / 3\<downharpoonleft> = pi/3\<close>
    using hhh 
    by (metis (no_types, opaque_lifting) canon_ang(1) canon_ang_uminus less_eq_real_def 
        linorder_not_le minus_add_distrib minus_divide_left mult_le_0_iff  
        nonzero_mult_div_cancel_left not_numeral_le_zero pi_gt_zero times_divide_eq_right verit_minus_simplify(4) zero_canonical)
  then show ?thesis using Morley_pos[of C B A P Q R] 
    by (smt (verit, best) Morley_pos angle_c_commute assms(1) assms(2) assms(3) assms(4) assms(5)
        assms(6) assms(7) cdist_commute collinear_sin_neq_0 collinear_sym1 collinear_sym2 sin_pi)
qed

theorem Morley:
  assumes\<open>\<not>collinear A B C\<close>
    \<open>angle_c A B R = angle_c A B C / 3\<close> (is \<open>?abr = ?abc\<close>)
    "angle_c B A R = angle_c B A C / 3" (is \<open>?bar = ?\<alpha>\<close>)
    "angle_c B C P = angle_c B C A / 3" (is \<open>?bcp = ?bca\<close>)
    "angle_c C B P = angle_c C B A / 3" (is \<open>?cbp = ?\<beta>\<close>)
    "angle_c C A Q = angle_c C A B / 3" (is \<open>?caq = ?cab\<close>)
    "angle_c A C Q = angle_c A C B / 3" (is \<open>?acq = ?\<gamma>\<close>)
  shows  \<open>cdist R P = cdist P Q \<and> cdist Q R = cdist P Q\<close>
proof -
  {fix A B C \<gamma>
    assume ABC_nline:\<open>A \<notin> line B C\<close>
      and eq_3c:\<open>angle_c A C B = 3*\<gamma>\<close>
    then have neq_PI:\<open>abs \<gamma> < pi/3\<close> 
    proof - 
      have \<open>angle_c A C B \<noteq> pi\<close> using ABC_nline(1) unfolding line_def 
        by (metis angle_c_commute_pi collinear_iff mem_Collect_eq non_collinear_independant)
      then have \<open>angle_c A C B \<in> {-pi<..<pi}\<close> 
        using ang_c_in less_eq_real_def by auto
      then show \<open>abs \<gamma> < pi/3\<close> 
        using eq_3c by force
    qed}note ang_inf_pi3=this
  have \<open>\<downharpoonright>angle_c B A C + angle_c C B A  + angle_c A C B\<downharpoonleft> = pi\<close>
    by (metis Elementary_Complex_Geometry.collinear_def add.commute 
        angle_sum_triangle_c assms(1) collinear_sym1 collinear_sym2')
  have eq_pi:\<open>\<downharpoonright>3*?\<alpha> + 3*?\<beta> + 3*?\<gamma>\<downharpoonleft> = pi\<close>
    using \<open>\<downharpoonright>angle_c B A C + angle_c C B A + angle_c A C B\<downharpoonleft> = pi\<close> by force
  have \<open>A\<notin>line B C \<and> B\<notin> line A C \<and> C \<notin> line A B\<close>
    using assms(1) unfolding line_def using collinear_sym1 collinear_sym2' by(auto) 
  then have f2:\<open>abs ?\<alpha> < pi/3 \<and> abs ?\<beta> < pi/3 \<and> abs ?\<gamma> < pi/3\<close>
    using ang_inf_pi3 
    by (smt (verit, ccfv_SIG) ang_vec_bounded angle_c_def assms(1) collinear_sin_neq_0 
        collinear_sym1 collinear_sym2 divide_less_cancel minus_divide_left sin_pi)
  have possi_abc:\<open>\<downharpoonright>?\<alpha>+?\<beta>+?\<gamma>\<downharpoonleft> =pi/3 \<or> \<downharpoonright>?\<alpha>+?\<beta>+?\<gamma>\<downharpoonleft> = -pi/3\<close> 
  proof -
    have \<open>?\<alpha>+?\<beta>+?\<gamma> \<le> pi\<close> 
      using f2 by(auto simp:field_simps)
    then have \<open>\<downharpoonright>?\<alpha>+?\<beta>+?\<gamma>\<downharpoonleft> = ?\<alpha>+?\<beta>+?\<gamma>\<close>
      using canon_ang_id f2 by fastforce
    then have \<open>\<downharpoonright>3*\<downharpoonright>?\<alpha>+?\<beta>+?\<gamma>\<downharpoonleft>\<downharpoonleft> = pi\<close> 
      using eq_pi by force
    then show ?thesis 
      by (smt (verit) add_divide_distrib arccos_minus_one_half arccos_one_half arcsin_minus_one_half
 arcsin_one_half arcsin_plus_arccos canon_ang_id canon_ang_minus_3pi_minus_pi canon_ang_pi_3pi 
 eq_pi f2 field_sum_of_halves)
  qed
  then show ?thesis 
    using Morley_neg Morley_pos assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) assms(7) 
    by meson
qed

end