(*
    Author:     Wenda Li <wl302@cam.ac.uk / liwenda1990@hotmail.com>
*)
theory Count_Line imports
  CC_Polynomials_Extra
  Winding_Number_Eval.Winding_Number_Eval
  Extended_Sturm
  Budan_Fourier.Sturm_Multiple_Roots
begin


subsection \<open>Misc\<close>

lemma closed_segment_imp_Re_Im:
  fixes x::complex
  assumes "x\<in>closed_segment lb ub" 
  shows "Re lb \<le> Re ub \<Longrightarrow> Re lb \<le> Re x \<and> Re x \<le> Re ub" 
        "Im lb \<le> Im ub \<Longrightarrow> Im lb \<le> Im x \<and> Im x \<le> Im ub"
proof -
  obtain u where x_u:"x=(1 - u) *\<^sub>R lb + u *\<^sub>R ub " and "0 \<le> u" "u \<le> 1"
    using assms unfolding closed_segment_def by auto
  have "Re lb \<le> Re x" when "Re lb \<le> Re ub"
  proof -
    have "Re x = Re ((1 - u) *\<^sub>R lb + u *\<^sub>R ub)"
      using x_u by blast
    also have "... = Re (lb + u *\<^sub>R (ub - lb))" by (auto simp add:algebra_simps)
    also have "... = Re lb + u * (Re ub - Re lb)" by auto
    also have "... \<ge> Re lb" using \<open>u\<ge>0\<close> \<open>Re lb \<le> Re ub\<close> by auto
    finally show ?thesis .
  qed
  moreover have "Im lb \<le> Im x" when "Im lb \<le> Im ub"
  proof -
    have "Im x = Im ((1 - u) *\<^sub>R lb + u *\<^sub>R ub)"
      using x_u by blast
    also have "... = Im (lb + u *\<^sub>R (ub - lb))" by (auto simp add:algebra_simps)
    also have "... = Im lb + u * (Im ub - Im lb)" by auto
    also have "... \<ge> Im lb" using \<open>u\<ge>0\<close> \<open>Im lb \<le> Im ub\<close> by auto
    finally show ?thesis .
  qed
  moreover have "Re x \<le> Re ub" when "Re lb \<le> Re ub"
  proof -
    have "Re x = Re ((1 - u) *\<^sub>R lb + u *\<^sub>R ub)"
      using x_u by blast
    also have "... = (1 - u) * Re lb + u * Re ub" by auto
    also have "... \<le> (1 - u) * Re ub + u * Re ub"
      using \<open>u\<le>1\<close> \<open>Re lb \<le> Re ub\<close> by (auto simp add: mult_left_mono)
    also have "... = Re ub" by (auto simp add:algebra_simps)
    finally show ?thesis .
  qed
  moreover have "Im x \<le> Im ub" when "Im lb \<le> Im ub"
  proof -
    have "Im x = Im ((1 - u) *\<^sub>R lb + u *\<^sub>R ub)"
      using x_u by blast
    also have "... = (1 - u) * Im lb + u * Im ub" by auto
    also have "... \<le> (1 - u) * Im ub + u * Im ub"
      using \<open>u\<le>1\<close> \<open>Im lb \<le> Im ub\<close> by (auto simp add: mult_left_mono)
    also have "... = Im ub" by (auto simp add:algebra_simps)
    finally show ?thesis .
  qed
  ultimately show 
      "Re lb \<le> Re ub \<Longrightarrow> Re lb \<le> Re x \<and> Re x \<le> Re ub" 
      "Im lb \<le> Im ub \<Longrightarrow> Im lb \<le> Im x \<and> Im x \<le> Im ub" 
    by auto
qed
  
lemma closed_segment_degen_complex:
  "\<lbrakk>Re lb = Re ub; Im lb \<le> Im ub \<rbrakk> 
    \<Longrightarrow> x \<in> closed_segment lb ub \<longleftrightarrow> Re x = Re lb \<and> Im lb \<le> Im x \<and> Im x \<le> Im ub "
  "\<lbrakk>Im lb = Im ub; Re lb \<le> Re ub \<rbrakk> 
    \<Longrightarrow> x \<in> closed_segment lb ub \<longleftrightarrow> Im x = Im lb \<and> Re lb \<le> Re x \<and> Re x \<le> Re ub "  
proof -
  show "x \<in> closed_segment lb ub \<longleftrightarrow> Re x = Re lb \<and> Im lb \<le> Im x \<and> Im x \<le> Im ub"
    when "Re lb = Re ub" "Im lb \<le> Im ub"
  proof 
    show "Re x = Re lb \<and> Im lb \<le> Im x \<and> Im x \<le> Im ub" when "x \<in> closed_segment lb ub"
      using closed_segment_imp_Re_Im[OF that] \<open>Re lb = Re ub\<close> \<open>Im lb \<le> Im ub\<close> by fastforce
  next
    assume asm:"Re x = Re lb \<and> Im lb \<le> Im x \<and> Im x \<le> Im ub"
    define u where "u=(Im x - Im lb)/ (Im ub - Im lb)"
    have "x = (1 - u) *\<^sub>R lb + u *\<^sub>R ub"
      unfolding u_def using asm \<open>Re lb = Re ub\<close> \<open>Im lb \<le> Im ub\<close>
      apply (intro complex_eqI)
      apply (auto simp add:field_simps)
      apply (cases "Im ub - Im lb =0")
      apply (auto simp add:field_simps)
      done
    moreover have "0\<le>u" "u\<le>1" unfolding u_def 
      using \<open>Im lb \<le> Im ub\<close> asm
      by (cases "Im ub - Im lb =0",auto simp add:field_simps)+
    ultimately show "x \<in> closed_segment lb ub" unfolding closed_segment_def by auto
  qed
  show "x \<in> closed_segment lb ub \<longleftrightarrow> Im x = Im lb \<and> Re lb \<le> Re x \<and> Re x \<le> Re ub"
    when "Im lb = Im ub" "Re lb \<le> Re ub"
  proof 
    show "Im x = Im lb \<and> Re lb \<le> Re x \<and> Re x \<le> Re ub" when "x \<in> closed_segment lb ub"
      using closed_segment_imp_Re_Im[OF that] \<open>Im lb = Im ub\<close> \<open>Re lb \<le> Re ub\<close> by fastforce
  next
    assume asm:"Im x = Im lb \<and> Re lb \<le> Re x \<and> Re x \<le> Re ub"
    define u where "u=(Re x - Re lb)/ (Re ub - Re lb)"
    have "x = (1 - u) *\<^sub>R lb + u *\<^sub>R ub"
      unfolding u_def using asm \<open>Im lb = Im ub\<close> \<open>Re lb \<le> Re ub\<close>
      apply (intro complex_eqI)
       apply (auto simp add:field_simps)
      apply (cases "Re ub - Re lb =0")
       apply (auto simp add:field_simps)
      done
    moreover have "0\<le>u" "u\<le>1" unfolding u_def 
      using \<open>Re lb \<le> Re ub\<close> asm
      by (cases "Re ub - Re lb =0",auto simp add:field_simps)+
    ultimately show "x \<in> closed_segment lb ub" unfolding closed_segment_def by auto
  qed   
qed

(*refined version of the library one with the same name by dropping unnecessary assumptions*) 
corollary path_image_part_circlepath_subset:
  assumes "r\<ge>0"
  shows "path_image(part_circlepath z r st tt) \<subseteq> sphere z r"
proof (cases "st\<le>tt")
  case True
  then show ?thesis 
    by (auto simp: assms path_image_part_circlepath sphere_def dist_norm algebra_simps norm_mult) 
next
  case False
  then have "path_image(part_circlepath z r tt st) \<subseteq> sphere z r"
    by (auto simp: assms path_image_part_circlepath sphere_def dist_norm algebra_simps norm_mult)
  moreover have "path_image(part_circlepath z r tt st) = path_image(part_circlepath z r st tt)"
    using path_image_reversepath by fastforce
  ultimately show ?thesis by auto
qed

(*refined version of the library one with the same name by dropping unnecessary assumptions*)
proposition in_path_image_part_circlepath:
  assumes "w \<in> path_image(part_circlepath z r st tt)" "0 \<le> r"
  shows "norm(w - z) = r"
proof -
  have "w \<in> {c. dist z c = r}"
    by (metis (no_types) path_image_part_circlepath_subset sphere_def subset_eq assms)
  thus ?thesis
    by (simp add: dist_norm norm_minus_commute)
qed  

lemma infinite_ball:
  fixes a :: "'a::euclidean_space"
  assumes "r > 0" 
  shows "infinite (ball a r)"
  using uncountable_ball[OF assms, THEN uncountable_infinite] .

lemma infinite_cball:
  fixes a :: "'a::euclidean_space"
  assumes "r > 0" 
  shows "infinite (cball a r)"
  using uncountable_cball[OF assms, THEN uncountable_infinite,of a] .

(*FIXME: to generalise*)
lemma infinite_sphere:
  fixes a :: complex
  assumes "r > 0" 
  shows "infinite (sphere a r)" 
proof -
  have "uncountable (path_image (circlepath a r))"
    apply (rule simple_path_image_uncountable)
    using simple_path_circlepath assms by simp
  then have "uncountable (sphere a r)"
    using assms by simp
  from uncountable_infinite[OF this] show ?thesis .
qed

lemma infinite_halfspace_Im_gt: "infinite {x. Im x > b}"
  apply (rule connected_uncountable[THEN uncountable_infinite,of _ "(b+1)* \<i>" "(b+2)*\<i>"])
  by (auto intro!:convex_connected simp add: convex_halfspace_Im_gt)
       
lemma (in ring_1) Ints_minus2: "- a \<in> \<int> \<Longrightarrow> a \<in> \<int>"
  using Ints_minus[of "-a"] by auto

lemma dvd_divide_Ints_iff:
  "b dvd a \<or> b=0 \<longleftrightarrow> of_int a / of_int b \<in> (\<int> :: 'a :: {field,ring_char_0} set)"  
proof
  assume asm:"b dvd a \<or> b=0"
  let ?thesis = "of_int a / of_int b \<in> (\<int> :: 'a :: {field,ring_char_0} set)"
  have ?thesis when "b dvd a"
  proof -
    obtain c where "a=b * c" using \<open>b dvd a\<close> unfolding dvd_def by auto
    then show ?thesis by (auto simp add:field_simps)
  qed
  moreover have ?thesis when "b=0" 
    using that by auto
  ultimately show ?thesis using asm by auto
next
  assume "of_int a / of_int b \<in> (\<int> :: 'a :: {field,ring_char_0} set)"
  from Ints_cases[OF this] obtain c where *:"(of_int::_ \<Rightarrow> 'a) c= of_int a / of_int b"
    by metis 
  have "b dvd a" when "b\<noteq>0"
  proof -
    have "(of_int::_ \<Rightarrow> 'a) a = of_int b * of_int c" using that * by auto
    then have "a = b * c" using of_int_eq_iff by fastforce
    then show ?thesis unfolding dvd_def by auto
  qed
  then show " b dvd a \<or> b = 0" by auto
qed
 
lemma of_int_div_field:
  assumes "d dvd n"
  shows "(of_int::_\<Rightarrow>'a::field_char_0) (n div d) = of_int n / of_int d" 
  apply (subst (2) dvd_mult_div_cancel[OF assms,symmetric])
  by (auto simp add:field_simps)

lemma powr_eq_1_iff:
  assumes "a>0"
  shows "(a::real) powr b =1 \<longleftrightarrow> a=1 \<or> b=0"
proof 
  assume "a powr b = 1"
  have "b * ln a = 0"
    using \<open>a powr b = 1\<close> ln_powr[of a b] assms by auto
  then have "b=0 \<or> ln a =0" by auto
  then show "a = 1 \<or> b = 0" using assms by auto
qed (insert assms, auto)

lemma tan_inj_pi:
  "- (pi/2) < x \<Longrightarrow> x < pi/2 \<Longrightarrow> - (pi/2) < y \<Longrightarrow> y < pi/2 \<Longrightarrow> tan x = tan y \<Longrightarrow> x = y"
  by (metis arctan_tan)

(*TODO: can we avoid fcompose in the proof?*)
lemma finite_ReZ_segments_poly_circlepath:
          "finite_ReZ_segments (poly p \<circ> circlepath z0 r) 0"
proof (cases "\<forall>t\<in>({0..1} - {1/2}). Re ((poly p \<circ> circlepath z0 r) t) = 0")
  case True
  have "isCont (Re \<circ> poly p \<circ> circlepath z0 r) (1/2)"
    by (auto intro!:continuous_intros simp:circlepath)
  moreover have "(Re \<circ> poly p \<circ> circlepath z0 r)\<midarrow> 1/2 \<rightarrow> 0"
  proof -
    have "\<forall>\<^sub>F x in at (1 / 2). (Re \<circ> poly p \<circ> circlepath z0 r) x = 0" 
      unfolding eventually_at_le 
      apply (rule exI[where x="1/2"])
      unfolding dist_real_def abs_diff_le_iff
      by (auto intro!:True[rule_format, unfolded comp_def])
    then show ?thesis by (rule tendsto_eventually)
  qed
  ultimately have "Re ((poly p \<circ> circlepath z0 r) (1/2)) = 0"
    unfolding comp_def by (simp add: LIM_unique continuous_within)
  then have "\<forall>t\<in>{0..1}. Re ((poly p \<circ> circlepath z0 r) t) = 0"
    using True by blast
  then show ?thesis 
    apply (rule_tac finite_ReZ_segments_constI[THEN finite_ReZ_segments_congE])
    by auto
next
  case False
   define q1 q2 where "q1=fcompose p [:(z0+r)*\<i>,z0-r:] [:\<i>,1:]" and 
                      "q2=([:\<i>, 1:] ^ degree p)"
  define q1R q1I where "q1R=map_poly Re q1" and "q1I=map_poly Im q1"
  define q2R q2I where "q2R=map_poly Re q2" and "q2I=map_poly Im q2"
  define qq where "qq=q1R*q2R + q1I*q2I"
  
  have poly_eq:"Re ((poly p \<circ> circlepath z0 r) t) = 0 \<longleftrightarrow> poly qq (tan (pi * t)) = 0"
    when "0\<le>t" "t\<le>1" "t\<noteq>1/2" for t 
  proof -
    define tt where "tt=tan (pi * t)"
    have "Re ((poly p \<circ> circlepath z0 r) t) = 0 \<longleftrightarrow> Re (poly q1 tt / poly q2 tt) = 0"
      unfolding comp_def
      apply (subst poly_circlepath_tan_eq[of t p z0 r,folded q1_def q2_def tt_def])
      using that by simp_all
    also have "... \<longleftrightarrow> poly q1R tt * poly q2R tt + poly q1I tt * poly q2I tt = 0"
      unfolding q1I_def q1R_def q2R_def q2I_def
      by (simp add:Re_complex_div_eq_0 Re_poly_of_real Im_poly_of_real)
    also have "... \<longleftrightarrow> poly qq tt = 0"
      unfolding qq_def by simp
    finally show ?thesis unfolding tt_def .
  qed

  have "finite {t. Re ((poly p \<circ> circlepath z0 r) t) = 0 \<and> 0 \<le> t \<and> t \<le> 1}"
  proof - 
    define P where "P=(\<lambda>t. Re ((poly p \<circ> circlepath z0 r) t) = 0)"
    define A where "A= ({0..1}::real set)"
    define S where "S={t\<in>A-{1,1/2}. P t}"
    have "finite {t. poly qq (tan (pi * t)) = 0 \<and> 0 \<le> t \<and> t < 1 \<and> t\<noteq>1/2}"
    proof -
      define A where "A={t::real. 0 \<le> t \<and> t < 1 \<and> t \<noteq> 1 / 2}"
      have "finite ((\<lambda>t. tan (pi * t))  -`  {x. poly qq x=0} \<inter> A)"
      proof (rule finite_vimage_IntI)
        have "x = y" when "tan (pi * x) = tan (pi * y)" "x\<in>A" "y\<in>A" for x y
        proof -
          define x' where "x'=(if x<1/2 then x else x-1)"
          define y' where "y'=(if y<1/2 then y else y-1)"
          have "x'*pi = y'*pi" 
          proof (rule tan_inj_pi)
            have *:"- 1 / 2 < x'" "x' < 1 / 2" "- 1 / 2 < y'" "y' < 1 / 2" 
              using that(2,3) unfolding x'_def y'_def A_def by simp_all
            show "- (pi / 2) < x'  * pi" "x'  * pi < pi / 2" "- (pi / 2) < y'  * pi" 
                  "y'*pi < pi / 2"
              using mult_strict_right_mono[OF *(1),of pi] 
                    mult_strict_right_mono[OF *(2),of pi] 
                    mult_strict_right_mono[OF *(3),of pi] 
                    mult_strict_right_mono[OF *(4),of pi] 
              by auto
          next
            have "tan (x' * pi) = tan (x * pi)"
              unfolding x'_def using tan_periodic_int[of _ "- 1",simplified]
              by (auto simp add:algebra_simps)
            also have "... = tan (y * pi)"
              using \<open>tan (pi * x) = tan (pi * y)\<close> by (auto simp:algebra_simps)
            also have "... = tan (y' * pi)"
              unfolding y'_def using tan_periodic_int[of _ "- 1",simplified]
              by (auto simp add:algebra_simps)
            finally show "tan (x' * pi) = tan (y' * pi)" .
          qed
          then have "x'=y'" by auto
          then show ?thesis 
            using that(2,3) unfolding x'_def y'_def A_def by (auto split:if_splits)
        qed
        then show "inj_on (\<lambda>t. tan (pi * t)) A"
          unfolding inj_on_def by blast
      next
        have "qq\<noteq>0"
        proof (rule ccontr)
          assume "\<not> qq \<noteq> 0"
          then have "Re ((poly p \<circ> circlepath z0 r) t) = 0" when "t\<in>{0..1} - {1/2}" for t
            apply (subst poly_eq)
            using that by auto
          then show False using False by blast
        qed
        then show "finite {x. poly qq x = 0}" by (simp add: poly_roots_finite)
      qed
      then show ?thesis by (elim rev_finite_subset) (auto simp:A_def)
    qed
    moreover have "{t. poly qq (tan (pi * t)) = 0 \<and> 0 \<le> t \<and> t < 1 \<and> t\<noteq>1/2} = S"
      unfolding S_def P_def A_def using poly_eq by force
    ultimately have "finite S" by blast
    then have "finite (S \<union> (if P 1 then {1} else {}) \<union> (if P (1/2) then {1/2} else {}))"
      by auto
    moreover have "(S \<union> (if P 1 then {1} else {}) \<union> (if P (1/2) then {1/2} else {}))
                      = {t. P t \<and> 0 \<le> t \<and> t \<le> 1}" 
    proof -
      have "1\<in>A" "1/2 \<in>A" unfolding A_def by auto
      then have "(S \<union> (if P 1 then {1} else {}) \<union> (if P (1/2) then {1/2} else {}))
                      = {t\<in>A. P t}"
        unfolding S_def
        apply auto
        by (metis eq_divide_eq_numeral1(1) zero_neq_numeral)+
      also have "... = {t. P t \<and> 0 \<le> t \<and> t \<le> 1}"
        unfolding A_def by auto
      finally show ?thesis .
    qed
    ultimately have "finite {t. P t \<and> 0 \<le> t \<and> t \<le> 1}" by auto
    then show ?thesis unfolding P_def by simp
  qed
  then show ?thesis 
    apply (rule_tac finite_imp_finite_ReZ_segments)
    by auto
qed

lemma changes_itv_smods_ext_geq_0:
  assumes "a<b" "poly p a\<noteq>0" "poly p b \<noteq>0"
  shows "changes_itv_smods_ext a b p (pderiv p) \<ge>0"
  using sturm_ext_interval[OF assms] by auto

subsection \<open>Some useful conformal/@{term bij_betw} properties\<close>

lemma bij_betw_plane_ball:"bij_betw (\<lambda>x. (\<i>-x)/(\<i>+x)) {x. Im x>0} (ball 0 1)"
proof (rule bij_betw_imageI)
  have neq:"\<i> + x \<noteq>0" when "Im x>0" for x 
    using that 
    by (metis add_less_same_cancel2 add_uminus_conv_diff diff_0 diff_add_cancel 
        imaginary_unit.simps(2) not_one_less_zero uminus_complex.sel(2))
  then show "inj_on (\<lambda>x. (\<i> - x) / (\<i> + x)) {x. 0 < Im x}"
    unfolding inj_on_def by (auto simp add:divide_simps algebra_simps)
  have "cmod ((\<i> - x) / (\<i> + x)) < 1" when "0 < Im x " for x
  proof -
    have "cmod (\<i> - x) < cmod (\<i> + x)" 
      unfolding norm_lt inner_complex_def using that 
      by (auto simp add:algebra_simps)
    then show ?thesis
      unfolding norm_divide using neq[OF that] by auto
  qed
  moreover have "x \<in> (\<lambda>x. (\<i> - x) / (\<i> + x)) ` {x. 0 < Im x}" when "cmod x < 1" for x 
  proof (rule rev_image_eqI[of "\<i>*(1-x)/(1+x)"])
    have "1 + x\<noteq>0" "\<i> * 2 + \<i> * (x * 2) \<noteq>0" 
      subgoal using that by (metis complex_mod_triangle_sub norm_one norm_zero not_le pth_7(1))
      subgoal using that by (metis \<open>1 + x \<noteq> 0\<close> complex_i_not_zero div_mult_self4 mult_2 
            mult_zero_right nonzero_mult_div_cancel_left nonzero_mult_div_cancel_right 
            one_add_one zero_neq_numeral)
      done        
    then show "x = (\<i> - \<i> * (1 - x) / (1 + x)) / (\<i> + \<i> * (1 - x) / (1 + x))"
      by (auto simp add:field_simps)
    show " \<i> * (1 - x) / (1 + x) \<in> {x. 0 < Im x}"
      apply (auto simp:Im_complex_div_gt_0 algebra_simps)
      using that unfolding cmod_def by (auto simp:power2_eq_square)
  qed
  ultimately show "(\<lambda>x. (\<i> - x) / (\<i> + x)) ` {x. 0 < Im x} = ball 0 1"
    by auto
qed
    
lemma bij_betw_axis_sphere:"bij_betw (\<lambda>x. (\<i>-x)/(\<i>+x)) {x. Im x=0} (sphere 0 1 - {-1})"
proof (rule bij_betw_imageI)
  have neq:"\<i> + x \<noteq>0" when "Im x=0" for x 
    using that 
    by (metis add_diff_cancel_left' imaginary_unit.simps(2) minus_complex.simps(2) 
         right_minus_eq zero_complex.simps(2) zero_neq_one)
  then show "inj_on (\<lambda>x. (\<i> - x) / (\<i> + x)) {x. Im x = 0}"
    unfolding inj_on_def by (auto simp add:divide_simps algebra_simps)
  have "cmod ((\<i> - x) / (\<i> + x)) = 1" "(\<i> - x) / (\<i> + x) \<noteq> - 1" when "Im x = 0" for x 
  proof -
    have "cmod (\<i> + x) = cmod (\<i> - x)" 
      using that unfolding cmod_def by auto
    then show "cmod ((\<i> - x) / (\<i> + x)) = 1"
      unfolding norm_divide using neq[OF that] by auto
    show "(\<i> - x) / (\<i> + x) \<noteq> - 1" using neq[OF that] by (auto simp add:divide_simps)
  qed
  moreover have "x \<in> (\<lambda>x. (\<i> - x) / (\<i> + x)) ` {x. Im x = 0}" 
    when "cmod x = 1" "x\<noteq>-1" for x 
  proof (rule rev_image_eqI[of "\<i>*(1-x)/(1+x)"])
    have "1 + x\<noteq>0" "\<i> * 2 + \<i> * (x * 2) \<noteq>0" 
      subgoal using that(2) by algebra 
      subgoal using that by (metis \<open>1 + x \<noteq> 0\<close> complex_i_not_zero div_mult_self4 mult_2 
            mult_zero_right nonzero_mult_div_cancel_left nonzero_mult_div_cancel_right 
            one_add_one zero_neq_numeral)
      done        
    then show "x = (\<i> - \<i> * (1 - x) / (1 + x)) / (\<i> + \<i> * (1 - x) / (1 + x))"
      by (auto simp add:field_simps)
    show " \<i> * (1 - x) / (1 + x) \<in> {x. Im x = 0}"
      apply (auto simp:algebra_simps Im_complex_div_eq_0)
      using that(1) unfolding cmod_def by (auto simp:power2_eq_square)
  qed
  ultimately show "(\<lambda>x. (\<i> - x) / (\<i> + x)) ` {x. Im x = 0} = sphere 0 1 - {- 1}"
    by force
qed

lemma bij_betw_ball_uball:
  assumes "r>0"
  shows "bij_betw (\<lambda>x. complex_of_real r*x + z0) (ball 0 1) (ball z0 r)"
proof (rule bij_betw_imageI)
  show "inj_on (\<lambda>x. complex_of_real r * x + z0) (ball 0 1)"
    unfolding inj_on_def using assms by simp
  have "dist z0 (complex_of_real r * x + z0) < r" when "cmod x<1" for x 
    using that assms by (auto simp:dist_norm norm_mult abs_of_pos)
  moreover have "x \<in> (\<lambda>x. complex_of_real r * x + z0) ` ball 0 1" when "dist z0 x < r" for x 
    apply (rule rev_image_eqI[of "(x-z0)/r"])
    using that assms by (auto simp add: dist_norm norm_divide norm_minus_commute)
  ultimately show "(\<lambda>x. complex_of_real r  * x + z0) ` ball 0 1 = ball z0 r" 
    by auto
qed

lemma bij_betw_sphere_usphere:
  assumes "r>0"
  shows "bij_betw (\<lambda>x. complex_of_real r*x + z0) (sphere 0 1) (sphere z0 r)"
proof (rule bij_betw_imageI)
  show "inj_on (\<lambda>x. complex_of_real r * x + z0) (sphere 0 1)"
    unfolding inj_on_def using assms by simp
  have "dist z0 (complex_of_real r * x + z0) = r" when "cmod x=1" for x 
    using that assms by (auto simp:dist_norm norm_mult abs_of_pos)
  moreover have "x \<in> (\<lambda>x. complex_of_real r * x + z0) ` sphere 0 1" when "dist z0 x = r" for x 
    apply (rule rev_image_eqI[of "(x-z0)/r"])
    using that assms by (auto simp add: dist_norm norm_divide norm_minus_commute)
  ultimately show "(\<lambda>x. complex_of_real r  * x + z0) ` sphere 0 1 = sphere z0 r" 
    by auto
qed

lemma proots_ball_plane_eq:
  defines "q1\<equiv>[:\<i>,-1:]" and "q2\<equiv>[:\<i>,1:]"
  assumes "p\<noteq>0"
  shows "proots_count p (ball 0 1) = proots_count (fcompose p q1 q2) {x. 0 < Im x}"
  unfolding q1_def q2_def 
proof (rule proots_fcompose_bij_eq[OF _ \<open>p\<noteq>0\<close>])
  show "\<forall>x\<in>{x. 0 < Im x}. poly [:\<i>, 1:] x \<noteq> 0" 
    apply simp 
    by (metis add_less_same_cancel2 imaginary_unit.simps(2) not_one_less_zero 
          plus_complex.simps(2) zero_complex.simps(2))
  show "infinite (UNIV::complex set)" by (simp add: infinite_UNIV_char_0)
qed (use bij_betw_plane_ball in auto)

lemma proots_sphere_axis_eq:
  defines "q1\<equiv>[:\<i>,-1:]" and "q2\<equiv>[:\<i>,1:]"
  assumes "p\<noteq>0"
  shows "proots_count p (sphere 0 1 - {- 1}) = proots_count (fcompose p q1 q2) {x. 0 = Im x}"
unfolding q1_def q2_def 
proof (rule proots_fcompose_bij_eq[OF _ \<open>p\<noteq>0\<close>])
  show "\<forall>x\<in>{x. 0 = Im x}. poly [:\<i>, 1:] x \<noteq> 0" by (simp add: Complex_eq_0 plus_complex.code)
  show "infinite (UNIV::complex set)" by (simp add: infinite_UNIV_char_0)
qed (use bij_betw_axis_sphere in auto)

lemma proots_card_ball_plane_eq:
  defines "q1\<equiv>[:\<i>,-1:]" and "q2\<equiv>[:\<i>,1:]"
  assumes "p\<noteq>0"
  shows "card (proots_within p (ball 0 1)) = card (proots_within (fcompose p q1 q2) {x. 0 < Im x})"
unfolding q1_def q2_def
proof (rule proots_card_fcompose_bij_eq[OF _ \<open>p\<noteq>0\<close>])
  show "\<forall>x\<in>{x. 0 < Im x}. poly [:\<i>, 1:] x \<noteq> 0" 
    apply simp 
    by (metis add_less_same_cancel2 imaginary_unit.simps(2) not_one_less_zero 
          plus_complex.simps(2) zero_complex.simps(2))
qed (use bij_betw_plane_ball infinite_UNIV_char_0 in auto)

lemma proots_card_sphere_axis_eq:
  defines "q1\<equiv>[:\<i>,-1:]" and "q2\<equiv>[:\<i>,1:]"
  assumes "p\<noteq>0"
  shows "card (proots_within p (sphere 0 1 - {- 1})) 
            = card (proots_within (fcompose p q1 q2) {x. 0 = Im x})"
unfolding q1_def q2_def
proof (rule proots_card_fcompose_bij_eq[OF _ \<open>p\<noteq>0\<close>])
  show "\<forall>x\<in>{x. 0 = Im x}. poly [:\<i>, 1:] x \<noteq> 0" by (simp add: Complex_eq_0 plus_complex.code)
qed (use bij_betw_axis_sphere infinite_UNIV_char_0 in auto)

lemma proots_uball_eq:
  fixes z0::complex and r::real
  defines "q\<equiv>[:z0, of_real r:]"
  assumes "p\<noteq>0" and "r>0"
  shows "proots_count p (ball z0 r) = proots_count (p \<circ>\<^sub>p q) (ball 0 1)"
proof -
  show ?thesis
    apply (rule proots_pcompose_bij_eq[OF _ \<open>p\<noteq>0\<close>])
    subgoal unfolding q_def using bij_betw_ball_uball[OF \<open>r>0\<close>,of z0] by (auto simp:algebra_simps)
    subgoal unfolding q_def using \<open>r>0\<close> by auto
    done
qed

lemma proots_card_uball_eq:
  fixes z0::complex and r::real
  defines "q\<equiv>[:z0, of_real r:]"
  assumes "r>0"
  shows "card (proots_within p (ball z0 r)) = card (proots_within (p \<circ>\<^sub>p q) (ball 0 1))"
proof -
  have ?thesis 
    when "p=0"
  proof -
    have "card (ball z0 r) = 0" "card (ball (0::complex) 1) = 0"
      using infinite_ball[OF \<open>r>0\<close>,of z0] infinite_ball[of 1 "0::complex"] by auto 
    then show ?thesis using that by auto
  qed
  moreover have ?thesis 
    when "p\<noteq>0"
    apply (rule proots_card_pcompose_bij_eq[OF _ \<open>p\<noteq>0\<close>])
    subgoal unfolding q_def using bij_betw_ball_uball[OF \<open>r>0\<close>,of z0] by (auto simp:algebra_simps)
    subgoal unfolding q_def using \<open>r>0\<close> by auto
    done
  ultimately show ?thesis 
    by blast
qed

lemma proots_card_usphere_eq:
  fixes z0::complex and r::real
  defines "q\<equiv>[:z0, of_real r:]"
  assumes "r>0"
  shows "card (proots_within p (sphere z0 r)) = card (proots_within (p \<circ>\<^sub>p q) (sphere 0 1))"
proof -
  have ?thesis 
    when "p=0"
  proof -
    have "card (sphere z0 r) = 0" "card (sphere (0::complex) 1) = 0"
      using infinite_sphere[OF \<open>r>0\<close>,of z0] infinite_sphere[of 1 "0::complex"] by auto 
    then show ?thesis using that by auto
  qed
  moreover have ?thesis
    when "p\<noteq>0"
    apply (rule proots_card_pcompose_bij_eq[OF _ \<open>p\<noteq>0\<close>])
    subgoal unfolding q_def using bij_betw_sphere_usphere[OF \<open>r>0\<close>,of z0] 
      by (auto simp:algebra_simps)
    subgoal unfolding q_def using \<open>r>0\<close> by auto
    done
  ultimately show "card (proots_within p (sphere z0 r)) = card (proots_within (p \<circ>\<^sub>p q) (sphere 0 1))" 
    by blast
qed

subsection \<open>Number of roots on a (bounded or unbounded) segment\<close>

\<comment> \<open>1 dimensional hyperplane\<close>
definition unbounded_line::"'a::real_vector \<Rightarrow> 'a \<Rightarrow> 'a set" where 
   "unbounded_line a b = ({x. \<exists>u::real. x= (1 - u) *\<^sub>R a + u *\<^sub>R b})"

definition proots_line_card:: "complex poly \<Rightarrow> complex \<Rightarrow> complex \<Rightarrow> nat" where
  "proots_line_card p st tt = card (proots_within p (open_segment st tt))"

definition proots_unbounded_line_card:: "complex poly \<Rightarrow> complex \<Rightarrow> complex \<Rightarrow> nat" where
  "proots_unbounded_line_card p st tt = card (proots_within p (unbounded_line st tt))"

definition proots_unbounded_line :: "complex poly \<Rightarrow> complex \<Rightarrow> complex \<Rightarrow> nat" where
  "proots_unbounded_line p st tt = proots_count p (unbounded_line st tt)"

lemma card_proots_open_segments:
  assumes "poly p st \<noteq>0" "poly p tt \<noteq> 0"
  shows "card (proots_within p (open_segment st tt)) = 
                (let pc = pcompose p [:st, tt - st:];
                     pR = map_poly Re pc;
                     pI = map_poly Im pc;
                     g  = gcd pR pI
                 in changes_itv_smods 0 1 g (pderiv g))" (is "?L = ?R")
proof -
  define pc pR pI g where 
      "pc = pcompose p [:st, tt-st:]" and
      "pR = map_poly Re pc" and
      "pI = map_poly Im pc" and
      "g  = gcd pR pI"
  have poly_iff:"poly g t=0 \<longleftrightarrow> poly pc t =0" for t
  proof -
    have "poly g t = 0 \<longleftrightarrow> poly pR t =0 \<and> poly pI t =0" 
      unfolding g_def using poly_gcd_0_iff by auto
    also have "... \<longleftrightarrow> poly pc t =0"
    proof -
      have "cpoly_of pR pI = pc"
        unfolding pc_def pR_def pI_def using cpoly_of_decompose by auto
      then show ?thesis using poly_cpoly_of_real_iff by blast
    qed
    finally show ?thesis by auto
  qed      

  have "?R = changes_itv_smods 0 1 g (pderiv g)"
    unfolding pc_def g_def pI_def pR_def by (auto simp add:Let_def)
  also have "... = card {t. poly g t = 0 \<and> 0 < t \<and> t < 1}"
  proof -
    have "poly g 0 \<noteq> 0" 
      using poly_iff[of 0] assms unfolding pc_def by (auto simp add:poly_pcompose)
    moreover have "poly g 1 \<noteq> 0" 
      using poly_iff[of 1] assms unfolding pc_def by (auto simp add:poly_pcompose)
    ultimately show ?thesis using sturm_interval[of 0 1 g] by auto
  qed
  also have "... = card {t::real. poly pc (of_real t) = 0 \<and> 0 < t \<and> t < 1}"
    unfolding poly_iff by simp
  also have "... = ?L"
  proof (cases "st=tt")
    case True
    then show ?thesis unfolding pc_def poly_pcompose using \<open>poly p tt \<noteq> 0\<close>
      by auto
  next
    case False
    define ff where "ff = (\<lambda>t::real. st + t*(tt-st))"
    define ll where "ll = {t. poly pc (complex_of_real t) = 0 \<and> 0 < t \<and> t < 1}"
    have "ff ` ll = proots_within p (open_segment st tt)"
    proof (rule equalityI)
      show "ff ` ll \<subseteq> proots_within p (open_segment st tt)"
        unfolding ll_def ff_def pc_def poly_pcompose 
        by (auto simp add:in_segment False scaleR_conv_of_real algebra_simps)
    next
      show "proots_within p (open_segment st tt) \<subseteq> ff ` ll"
      proof clarify
        fix x assume asm:"x \<in> proots_within p (open_segment st tt)" 
        then obtain u where "0<u" and "u < 1" and u:"x = (1 - u) *\<^sub>R st + u *\<^sub>R tt"
          by (auto simp add:in_segment)
        then have "poly p ((1 - u) *\<^sub>R st + u *\<^sub>R tt) = 0" using asm by simp
        then have "u \<in> ll"
          unfolding ll_def pc_def poly_pcompose 
          by (simp add:scaleR_conv_of_real algebra_simps \<open>0<u\<close> \<open>u<1\<close>)
        moreover have "x = ff u"
          unfolding ff_def using u by (auto simp add:algebra_simps scaleR_conv_of_real)
        ultimately show "x \<in> ff ` ll" by (rule rev_image_eqI[of "u"])
      qed
    qed
    moreover have "inj_on ff ll"
      unfolding ff_def using False inj_on_def by fastforce
    ultimately show ?thesis unfolding ll_def 
      using card_image[of ff] by fastforce
  qed
  finally show ?thesis by simp
qed

lemma unbounded_line_closed_segment: "closed_segment a b \<subseteq> unbounded_line a b"
  unfolding unbounded_line_def closed_segment_def by auto

lemma card_proots_unbounded_line:
  assumes "st\<noteq>tt"
  shows "card (proots_within p (unbounded_line st tt)) = 
                (let pc = pcompose p [:st, tt - st:];
                     pR = map_poly Re pc;
                     pI = map_poly Im pc;
                     g  = gcd pR pI
                 in nat (changes_R_smods g (pderiv g)))" (is "?L = ?R")
proof -
  define pc pR pI g where 
      "pc = pcompose p [:st, tt-st:]" and
      "pR = map_poly Re pc" and
      "pI = map_poly Im pc" and
      "g  = gcd pR pI"
  have poly_iff:"poly g t=0 \<longleftrightarrow> poly pc t =0" for t
  proof -
    have "poly g t = 0 \<longleftrightarrow> poly pR t =0 \<and> poly pI t =0" 
      unfolding g_def using poly_gcd_0_iff by auto
    also have "... \<longleftrightarrow> poly pc t =0"
    proof -
      have "cpoly_of pR pI = pc"
        unfolding pc_def pR_def pI_def using cpoly_of_decompose by auto
      then show ?thesis using poly_cpoly_of_real_iff by blast
    qed
    finally show ?thesis by auto
  qed      

  have "?R = nat (changes_R_smods g (pderiv g))"
    unfolding pc_def g_def pI_def pR_def by (auto simp add:Let_def)
  also have "... = card {t. poly g t = 0}"
    using sturm_R[of g] by simp
  also have "... = card {t::real. poly pc t = 0}"
    unfolding poly_iff by simp
  also have "... = ?L"
  proof (cases "st=tt")
    case True
    then show ?thesis unfolding pc_def poly_pcompose unbounded_line_def using assms
      by (auto simp add:proots_within_def)
  next
    case False
    define ff where "ff = (\<lambda>t::real. st + t*(tt-st))"
    define ll where "ll = {t. poly pc (complex_of_real t) = 0}"
    have "ff ` ll = proots_within p (unbounded_line st tt)"
    proof (rule equalityI)
      show "ff ` ll \<subseteq> proots_within p (unbounded_line st tt)"
        unfolding ll_def ff_def pc_def poly_pcompose 
        by (auto simp add:unbounded_line_def False scaleR_conv_of_real algebra_simps)
    next
      show "proots_within p (unbounded_line st tt) \<subseteq> ff ` ll"
      proof clarify
        fix x assume asm:"x \<in> proots_within p (unbounded_line st tt)" 
        then obtain u where u:"x = (1 - u) *\<^sub>R st + u *\<^sub>R tt"
          by (auto simp add:unbounded_line_def)
        then have "poly p ((1 - u) *\<^sub>R st + u *\<^sub>R tt) = 0" using asm by simp
        then have "u \<in> ll"
          unfolding ll_def pc_def poly_pcompose 
          by (simp add:scaleR_conv_of_real algebra_simps unbounded_line_def)
        moreover have "x = ff u"
          unfolding ff_def using u by (auto simp add:algebra_simps scaleR_conv_of_real)
        ultimately show "x \<in> ff ` ll" by (rule rev_image_eqI[of "u"])
      qed
    qed
    moreover have "inj_on ff ll"
      unfolding ff_def using False inj_on_def by fastforce
    ultimately show ?thesis unfolding ll_def 
      using card_image[of ff] by metis
  qed  
  finally show ?thesis by simp
qed

lemma proots_count_gcd_eq:
  fixes p::"complex poly" and st tt::complex
    and g::"real poly"
  defines "pc \<equiv> pcompose p [:st, tt - st:]"
  defines "pR \<equiv> map_poly Re pc" and "pI \<equiv> map_poly Im pc"
  defines "g  \<equiv> gcd pR pI"
  assumes "st\<noteq>tt" "p\<noteq>0"
      and s1_def:"s1 = (\<lambda>x. poly [:st, tt - st:] (of_real x)) ` s2"
    shows "proots_count p s1 = proots_count g s2"
proof -
  have [simp]: "g\<noteq>0" "pc\<noteq>0"
  proof -
    show "pc\<noteq>0" using assms pc_def pcompose_eq_0 
      by (metis cancel_comm_monoid_add_class.diff_cancel degree_pCons_eq_if 
          diff_eq_diff_eq less_nat_zero_code pCons_eq_0_iff zero_less_Suc)
    then have "pR\<noteq>0 \<or> pI\<noteq>0" unfolding pR_def pI_def by (metis cpoly_of_decompose map_poly_0)
    then show "g\<noteq>0" unfolding g_def by simp
  qed
  have order_eq:"order t g = order t pc" for t
    apply (subst order_cpoly_gcd_eq[of pR pI,folded g_def,symmetric])
    subgoal using \<open>g\<noteq>0\<close> unfolding g_def by simp
    subgoal unfolding pR_def pI_def by (simp add:cpoly_of_decompose[symmetric])
    done

  have "proots_count g s2 = proots_count (map_poly complex_of_real g) 
            (of_real ` s2)"
    apply (subst proots_count_of_real)
    by auto
  also have "... = proots_count pc (of_real ` s2)" 
    apply (rule proots_count_cong)
    by (auto simp add: map_poly_order_of_real order_eq)
  also have "... = proots_count p s1"
    unfolding pc_def s1_def
    apply (subst proots_pcompose)
    using \<open>st\<noteq>tt\<close> \<open>p\<noteq>0\<close> by (simp_all add:image_image) 
  finally show ?thesis by simp
qed

lemma proots_unbounded_line:
  assumes "st\<noteq>tt" "p\<noteq>0"
  shows "(proots_count p (unbounded_line st tt)) = 
                (let pc = pcompose p [:st, tt - st:];
                     pR = map_poly Re pc;
                     pI = map_poly Im pc;
                     g  = gcd pR pI
                 in nat (changes_R_smods_ext g (pderiv g)))" (is "?L = ?R")
proof -
  define pc pR pI g where 
      "pc = pcompose p [:st, tt-st:]" and
      "pR = map_poly Re pc" and
      "pI = map_poly Im pc" and
      "g  = gcd pR pI"
  have [simp]: "g\<noteq>0" "pc\<noteq>0"
  proof -
    show "pc\<noteq>0" using assms(1) assms(2) pc_def pcompose_eq_0 
      by (metis cancel_comm_monoid_add_class.diff_cancel degree_pCons_eq_if 
          diff_eq_diff_eq less_nat_zero_code pCons_eq_0_iff zero_less_Suc)
    then have "pR\<noteq>0 \<or> pI\<noteq>0" unfolding pR_def pI_def by (metis cpoly_of_decompose map_poly_0)
    then show "g\<noteq>0" unfolding g_def by simp
  qed
  have order_eq:"order t g = order t pc" for t
    apply (subst order_cpoly_gcd_eq[of pR pI,folded g_def,symmetric])
    subgoal using \<open>g\<noteq>0\<close> unfolding g_def by simp
    subgoal unfolding pR_def pI_def by (simp add:cpoly_of_decompose[symmetric])
    done

  have "?R = nat (changes_R_smods_ext g (pderiv g))"
    unfolding pc_def g_def pI_def pR_def by (auto simp add:Let_def)
  also have "... = proots_count g UNIV"
    using sturm_ext_R[OF \<open>g\<noteq>0\<close>] by auto
  also have "... = proots_count (map_poly complex_of_real g) (of_real ` UNIV)"
    apply (subst proots_count_of_real)
    by auto
  also have "... = proots_count (map_poly complex_of_real g) {x. Im x = 0}"
    apply (rule arg_cong2[where f=proots_count])
    using Reals_def complex_is_Real_iff by auto
  also have "... = proots_count pc {x. Im x = 0}"
    apply (rule proots_count_cong)
    apply (metis (mono_tags) Im_complex_of_real Re_complex_of_real \<open>g \<noteq> 0\<close> complex_surj 
            map_poly_order_of_real mem_Collect_eq order_eq)
    by auto
  also have "... = proots_count p (unbounded_line st tt)"
  proof -
    have "poly [:st, tt - st:] ` {x. Im x = 0} = unbounded_line st tt"
      unfolding unbounded_line_def 
      apply safe
      subgoal for _ x 
        apply (rule_tac x="Re x" in exI) 
        apply (simp add:algebra_simps)
        by (simp add: mult.commute scaleR_complex.code times_complex.code)
      subgoal for _ u
        apply (rule rev_image_eqI[of "of_real u"])
        by (auto simp:scaleR_conv_of_real algebra_simps)
      done
    then show ?thesis 
      unfolding pc_def 
      apply (subst proots_pcompose)
      using \<open>p\<noteq>0\<close> \<open>st\<noteq>tt\<close> by auto
  qed
  finally show ?thesis by simp
qed

lemma proots_unbounded_line_card_code[code]:
  "proots_unbounded_line_card p st tt = 
              (if st\<noteq>tt then 
                (let pc = pcompose p [:st, tt - st:];
                     pR = map_poly Re pc;
                     pI = map_poly Im pc;
                     g  = gcd pR pI
                 in nat (changes_R_smods g (pderiv g))) 
              else 
                  Code.abort (STR ''proots_unbounded_line_card fails due to invalid hyperplanes.'') 
                      (\<lambda>_. proots_unbounded_line_card p st tt))"
  unfolding proots_unbounded_line_card_def using card_proots_unbounded_line[of st tt p] by auto

lemma proots_unbounded_line_code[code]:
  "proots_unbounded_line p st tt = 
              ( if st\<noteq>tt then 
                if p\<noteq>0 then 
                  (let pc = pcompose p [:st, tt - st:];
                     pR = map_poly Re pc;
                     pI = map_poly Im pc;
                     g  = gcd pR pI
                  in nat (changes_R_smods_ext g (pderiv g)))
                else 
                  Code.abort (STR ''proots_unbounded_line fails due to p=0'') 
                      (\<lambda>_. proots_unbounded_line p st tt)
                else 
                  Code.abort (STR ''proots_unbounded_line fails due to invalid hyperplanes.'') 
                      (\<lambda>_. proots_unbounded_line p st tt) )"
  unfolding proots_unbounded_line_def using proots_unbounded_line by auto

subsection \<open>Checking if there a polynomial root on a closed segment\<close>    
    
definition no_proots_line::"complex poly \<Rightarrow> complex \<Rightarrow> complex \<Rightarrow> bool" where
  "no_proots_line p st tt = (proots_within p (closed_segment st tt) = {})"

(*TODO: the proof can probably be simplified using Lemma card_proots_open_segments*)
lemma no_proots_line_code[code]: "no_proots_line p st tt = (if poly p st \<noteq>0 \<and> poly p tt \<noteq> 0 then 
                (let pc = pcompose p [:st, tt - st:];
                     pR = map_poly Re pc;
                     pI = map_poly Im pc;
                     g  = gcd pR pI
                 in if changes_itv_smods 0 1 g (pderiv g) = 0 then True else False) else False)"
            (is "?L = ?R")
proof (cases "poly p st \<noteq>0 \<and> poly p tt \<noteq> 0")
  case False
  thus ?thesis unfolding no_proots_line_def by auto
next
  case True
  then have "poly p st \<noteq> 0" "poly p tt \<noteq> 0" by auto
  define pc pR pI g where 
      "pc = pcompose p [:st, tt-st:]" and
      "pR = map_poly Re pc" and
      "pI = map_poly Im pc" and
      "g  = gcd pR pI"
  have poly_iff:"poly g t=0 \<longleftrightarrow> poly pc t =0" for t
  proof -
    have "poly g t = 0 \<longleftrightarrow> poly pR t =0 \<and> poly pI t =0" 
      unfolding g_def using poly_gcd_0_iff by auto
    also have "... \<longleftrightarrow> poly pc t =0"
    proof -
      have "cpoly_of pR pI = pc"
        unfolding pc_def pR_def pI_def using cpoly_of_decompose by auto
      then show ?thesis using poly_cpoly_of_real_iff by blast
    qed
    finally show ?thesis by auto
  qed      
  have "?R = (changes_itv_smods 0 1 g (pderiv g) = 0)" 
    using True unfolding pc_def g_def pI_def pR_def
    by (auto simp add:Let_def)      
  also have "... = (card {x. poly g x = 0 \<and> 0 < x \<and> x < 1} = 0)"  
  proof -
    have "poly g 0 \<noteq> 0" 
      using poly_iff[of 0] True unfolding pc_def by (auto simp add:poly_pcompose)
    moreover have "poly g 1 \<noteq> 0" 
      using poly_iff[of 1] True unfolding pc_def by (auto simp add:poly_pcompose)
    ultimately show ?thesis using sturm_interval[of 0 1 g] by auto
  qed
  also have "... = ({x. poly g (of_real x) = 0 \<and> 0 < x \<and> x < 1} = {})"
  proof -
    have "g\<noteq>0"
    proof (rule ccontr)
      assume "\<not> g \<noteq> 0"
      then have "poly pc 0 =0"
        using poly_iff[of 0] by auto
      then show False using True unfolding pc_def by (auto simp add:poly_pcompose)
    qed
    from poly_roots_finite[OF this] have "finite {x. poly g x = 0 \<and> 0 < x \<and> x < 1}"
      by auto
    then show ?thesis using card_eq_0_iff by auto
  qed
  also have "... = ?L"
  proof -
    have "(\<exists>t. poly g (of_real t) = 0 \<and> 0 < t \<and> t < 1) \<longleftrightarrow>
          (\<exists>t::real. poly pc (of_real t) = 0 \<and> 0 < t \<and> t < 1)"
      using poly_iff by auto
    also have "... \<longleftrightarrow> (\<exists>x. x \<in> closed_segment st tt \<and> poly p x = 0)" 
    proof 
      assume "\<exists>t. poly pc (complex_of_real t) = 0 \<and> 0 < t \<and> t < 1"
      then obtain t where *:"poly pc (of_real t) = 0" and "0 < t" "t < 1" by auto
      define x where "x=poly [:st, tt - st:] t"
      have "x \<in> closed_segment st tt" using \<open>0<t\<close> \<open>t<1\<close> unfolding x_def in_segment
        by (intro exI[where x=t],auto simp add: algebra_simps scaleR_conv_of_real)
      moreover have "poly p x=0" using * unfolding pc_def x_def
        by (auto simp add:poly_pcompose)
      ultimately show "\<exists>x. x \<in> closed_segment st tt \<and> poly p x = 0" by auto
    next
      assume "\<exists>x. x \<in> closed_segment st tt \<and> poly p x = 0"
      then obtain x where "x \<in> closed_segment st tt" "poly p x = 0" by auto
      then obtain t::real where *:"x = (1 - t) *\<^sub>R st + t *\<^sub>R tt" and "0\<le>t" "t\<le>1"  
        unfolding in_segment by auto
      then have "x=poly [:st, tt - st:] t" by (auto simp add: algebra_simps scaleR_conv_of_real)
      then have "poly pc (complex_of_real t) = 0" 
        using \<open>poly p x=0\<close> unfolding pc_def by (auto simp add:poly_pcompose)
      moreover have "t\<noteq>0" "t\<noteq>1" using True *  \<open>poly p x=0\<close> by auto
      then have "0<t" "t<1" using \<open>0\<le>t\<close> \<open>t\<le>1\<close> by auto
      ultimately show "\<exists>t. poly pc (complex_of_real t) = 0 \<and> 0 < t \<and> t < 1" by auto
    qed        
    finally show ?thesis
      unfolding no_proots_line_def proots_within_def 
      by blast
  qed
  finally show ?thesis by simp
qed

subsection \<open>Number of roots on a bounded open segment\<close>

definition proots_line:: "complex poly \<Rightarrow> complex \<Rightarrow> complex \<Rightarrow> nat" where
  "proots_line p st tt = proots_count p (open_segment st tt)"

lemma proots_line_commute:
  "proots_line p st tt = proots_line p tt st"
  unfolding proots_line_def by (simp add: open_segment_commute)  

lemma proots_line_smods:
  assumes "poly p st \<noteq>0" "poly p tt \<noteq> 0" "st\<noteq>tt"
  shows "proots_line p st tt = 
                        (let pc = pcompose p [:st, tt - st:];
                             pR = map_poly Re pc;
                             pI = map_poly Im pc;
                             g  = gcd pR pI
                         in nat (changes_itv_smods_ext 0 1 g (pderiv g)))"
  (is "_=?R")
proof -
  have "p\<noteq>0" using assms(2) poly_0 by blast

  define pc pR pI g where 
      "pc = pcompose p [:st, tt-st:]" and
      "pR = map_poly Re pc" and
      "pI = map_poly Im pc" and
      "g  = gcd pR pI"
  have [simp]: "g\<noteq>0" "pc\<noteq>0"
  proof -
    show "pc\<noteq>0" 
      by (metis assms(1) coeff_pCons_0 pCons_0_0 pc_def pcompose_coeff_0)
    then have "pR\<noteq>0 \<or> pI\<noteq>0" unfolding pR_def pI_def 
      by (metis cpoly_of_decompose map_poly_0)
    then show "g\<noteq>0" unfolding g_def by simp
  qed
  have order_eq:"order t g = order t pc" for t
    apply (subst order_cpoly_gcd_eq[of pR pI,folded g_def,symmetric])
    subgoal using \<open>g\<noteq>0\<close> unfolding g_def by simp
    subgoal unfolding pR_def pI_def by (simp add:cpoly_of_decompose[symmetric])
    done
  have poly_iff:"poly g t=0 \<longleftrightarrow> poly pc t =0" for t
    using order_eq by (simp add: order_root)
  have "poly g 0 \<noteq> 0" "poly g 1 \<noteq>0"
    unfolding poly_iff pc_def
    using assms by (simp_all add:poly_pcompose)


  have "?R = changes_itv_smods_ext 0 1 g (pderiv g)"
    unfolding Let_def
    apply (fold pc_def g_def pI_def pR_def)
    using assms changes_itv_smods_ext_geq_0[OF _ \<open>poly g  0\<noteq>0\<close> \<open>poly g 1\<noteq>0\<close>]
    by auto
  also have "... = int (proots_count g {x. 0 < x \<and> x < 1})"
    apply (rule sturm_ext_interval[symmetric])
    by simp fact+
  also have "... =  int (proots_count p (open_segment st tt))"
  proof -
    define f where "f = (\<lambda>x. poly [:st, tt - st:] (complex_of_real x))"
    have "x\<in>f ` {x. 0 < x \<and> x < 1}"  if "x\<in>open_segment st tt" for x
    proof -
      obtain u where u:"u>0" "u < 1" "x = (1 - u) *\<^sub>R st + u *\<^sub>R tt"
        using \<open>x\<in>open_segment st tt\<close> unfolding in_segment by auto
      show ?thesis 
        apply (rule rev_image_eqI[where x=u])
        using u unfolding f_def 
        by (auto simp:algebra_simps scaleR_conv_of_real)
    qed
    moreover have "x\<in>open_segment st tt" if "x\<in>f ` {x. 0 < x \<and> x < 1}" for x
      using that \<open>st\<noteq>tt\<close> unfolding in_segment f_def 
      by (auto simp:scaleR_conv_of_real algebra_simps)
    ultimately have "open_segment st tt = f ` {x. 0 < x \<and> x < 1}" 
      by auto
    then have "proots_count p (open_segment st tt) 
              = proots_count g {x. 0 < x \<and> x < 1}"
      using proots_count_gcd_eq[OF \<open>st\<noteq>tt\<close> \<open>p\<noteq>0\<close>,
              folded pc_def pR_def pI_def g_def] unfolding f_def
      by auto
    then show ?thesis by auto
  qed
  also have "... =proots_line p st tt"
    unfolding proots_line_def by simp
  finally show ?thesis by simp
qed


lemma proots_line_code[code]: 
    "proots_line p st tt = 
        (if poly p st \<noteq>0 \<and> poly p tt \<noteq> 0 then 
            (if st\<noteq>tt then 
                (let pc = pcompose p [:st, tt - st:];
                     pR = map_poly Re pc;
                     pI = map_poly Im pc;
                     g  = gcd pR pI
                 in nat (changes_itv_smods_ext 0 1 g (pderiv g)))
            else 0)
   else  Code.abort (STR ''prootsline does not handle vanishing endpoints for now'') 
                      (\<lambda>_. proots_line p st tt))" (is "?L = ?R")
proof (cases "poly p st \<noteq>0 \<and> poly p tt \<noteq> 0 \<and> st\<noteq>tt")
  case False
  moreover have ?thesis if "st=tt" "p\<noteq>0"
    using that unfolding proots_line_def by auto
  ultimately show ?thesis by fastforce
next
  case True
  then show ?thesis using proots_line_smods by auto
qed

end