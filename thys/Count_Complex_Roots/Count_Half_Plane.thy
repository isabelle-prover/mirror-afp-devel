(*
    Author:     Wenda Li <wl302@cam.ac.uk / liwenda1990@hotmail.com>
*)
theory Count_Half_Plane imports
  Count_Line
begin

subsection \<open>Polynomial roots on the upper half-plane\<close>

\<comment> \<open>Roots counted WITH multiplicity\<close>
definition proots_upper ::"complex poly \<Rightarrow> nat" where
  "proots_upper p= proots_count p {z. Im z>0}"

\<comment> \<open>Roots counted WITHOUT multiplicity\<close>
definition proots_upper_card::"complex poly \<Rightarrow> nat" where 
  "proots_upper_card p = card (proots_within p {x. Im x >0})"

lemma Im_Ln_tendsto_at_top: "((\<lambda>x. Im (Ln (Complex a x))) \<longlongrightarrow> pi/2 ) at_top " 
proof (cases "a=0")
  case False
  define f where "f=(\<lambda>x. if a>0 then arctan (x/a) else arctan (x/a) + pi)"
  define g where "g=(\<lambda>x. Im (Ln (Complex a x)))"
  have "(f \<longlongrightarrow> pi / 2) at_top"
  proof (cases "a>0")
    case True
    then have "(f \<longlongrightarrow> pi / 2) at_top \<longleftrightarrow> ((\<lambda>x. arctan (x * inverse a)) \<longlongrightarrow> pi / 2) at_top"
      unfolding f_def field_class.field_divide_inverse by auto
    also have "... \<longleftrightarrow> (arctan \<longlongrightarrow> pi / 2) at_top"
      apply (subst filterlim_at_top_linear_iff[of "inverse a" arctan 0 "nhds (pi/2)",simplified])
      using True by auto
    also have "..." using tendsto_arctan_at_top .
    finally show ?thesis .    
  next
    case False
    then have "(f \<longlongrightarrow> pi / 2) at_top \<longleftrightarrow> ((\<lambda>x. arctan (x * inverse a) + pi) \<longlongrightarrow> pi / 2) at_top"
      unfolding f_def field_class.field_divide_inverse by auto
    also have "... \<longleftrightarrow> ((\<lambda>x. arctan (x * inverse a)) \<longlongrightarrow> - pi / 2) at_top"
      apply (subst tendsto_add_const_iff[of "-pi",symmetric])
      by auto
    also have "... \<longleftrightarrow> (arctan \<longlongrightarrow> - pi / 2) at_bot"
      apply (subst filterlim_at_top_linear_iff[of "inverse a" arctan 0,simplified])
      using False \<open>a\<noteq>0\<close> by auto
    also have "..." using tendsto_arctan_at_bot by simp
    finally show ?thesis .
  qed
  moreover have "\<forall>\<^sub>F x in at_top. f x = g x"
    unfolding f_def g_def using \<open>a\<noteq>0\<close>
    apply (subst Im_Ln_eq)
    subgoal for x using Complex_eq_0 by blast
    subgoal unfolding eventually_at_top_linorder by auto
    done
  ultimately show ?thesis 
    using tendsto_cong[of f g at_top] unfolding g_def by auto
next
  case True
  show ?thesis
    apply (rule tendsto_eventually)
    apply (rule eventually_at_top_linorderI[of 1])
    using True by (subst Im_Ln_eq,auto simp add:Complex_eq_0) 
qed
  
lemma Im_Ln_tendsto_at_bot: "((\<lambda>x. Im (Ln (Complex a x))) \<longlongrightarrow> - pi/2 ) at_bot " 
proof (cases "a=0")
  case False
  define f where "f=(\<lambda>x. if a>0 then arctan (x/a) else arctan (x/a) - pi)"
  define g where "g=(\<lambda>x. Im (Ln (Complex a x)))"
  have "(f \<longlongrightarrow> - pi / 2) at_bot"
  proof (cases "a>0")
    case True
    then have "(f \<longlongrightarrow> - pi / 2) at_bot \<longleftrightarrow> ((\<lambda>x. arctan (x * inverse a)) \<longlongrightarrow> - pi / 2) at_bot"
      unfolding f_def field_class.field_divide_inverse by auto
    also have "... \<longleftrightarrow> (arctan \<longlongrightarrow> - pi / 2) at_bot"
      apply (subst filterlim_at_bot_linear_iff[of "inverse a" arctan 0,simplified])
      using True by auto
    also have "..." using tendsto_arctan_at_bot by simp
    finally show ?thesis .    
  next
    case False
    then have "(f \<longlongrightarrow> - pi / 2) at_bot \<longleftrightarrow> ((\<lambda>x. arctan (x * inverse a) - pi) \<longlongrightarrow> - pi / 2) at_bot"
      unfolding f_def field_class.field_divide_inverse by auto
    also have "... \<longleftrightarrow> ((\<lambda>x. arctan (x * inverse a)) \<longlongrightarrow> pi / 2) at_bot"
      apply (subst tendsto_add_const_iff[of "pi",symmetric])
      by auto
    also have "... \<longleftrightarrow> (arctan \<longlongrightarrow> pi / 2) at_top"
      apply (subst filterlim_at_bot_linear_iff[of "inverse a" arctan 0,simplified])
      using False \<open>a\<noteq>0\<close> by auto
    also have "..." using tendsto_arctan_at_top by simp
    finally show ?thesis .
  qed
  moreover have "\<forall>\<^sub>F x in at_bot. f x = g x"
    unfolding f_def g_def using \<open>a\<noteq>0\<close>
    apply (subst Im_Ln_eq)
    subgoal for x using Complex_eq_0 by blast
    subgoal unfolding eventually_at_bot_linorder by (auto intro:exI[where x="-1"])
    done
  ultimately show ?thesis 
    using tendsto_cong[of f g at_bot] unfolding g_def by auto
next
  case True
  show ?thesis
    apply (rule tendsto_eventually)  
    apply (rule eventually_at_bot_linorderI[of "-1"])
    using True by (subst Im_Ln_eq,auto simp add:Complex_eq_0)
qed
  
lemma Re_winding_number_tendsto_part_circlepath:
  shows "((\<lambda>r. Re (winding_number (part_circlepath z0 r 0 pi ) a)) \<longlongrightarrow> 1/2 ) at_top" 
proof (cases "Im z0\<le>Im a")
  case True
  define g1 where "g1=(\<lambda>r. part_circlepath z0 r 0 pi)"
  define g2 where "g2=(\<lambda>r. part_circlepath z0 r pi (2*pi))"
  define f1 where "f1=(\<lambda>r. Re (winding_number (g1 r ) a))"
  define f2 where "f2=(\<lambda>r. Re (winding_number (g2 r) a))"
  have "(f2 \<longlongrightarrow> 1/2 ) at_top" 
  proof -
    define h1 where "h1 = (\<lambda>r. Im (Ln (Complex ( Im a-Im z0) (Re z0 - Re a + r))))"
    define h2 where "h2= (\<lambda>r. Im (Ln (Complex (  Im a -Im z0) (Re z0 - Re a - r))))"
    have "\<forall>\<^sub>F x in at_top. f2 x = (h1 x - h2 x) / (2 * pi)"
    proof (rule eventually_at_top_linorderI[of "cmod (a-z0) + 1"])
      fix r assume asm:"r \<ge> cmod (a - z0) + 1"
      have "Im p \<le> Im a" when "p\<in>path_image (g2 r)" for p
      proof -
        obtain t where p_def:"p=z0 + of_real r * exp (\<i> * of_real t)" and "pi\<le>t" "t\<le>2*pi"
          using \<open>p\<in>path_image (g2 r)\<close> 
          unfolding g2_def path_image_part_circlepath[of pi "2*pi",simplified]  
          by auto
        then have "Im p=Im z0 + sin t * r" by (auto simp add:Im_exp)
        also have "... \<le> Im z0"
        proof -
          have "sin t\<le>0" using \<open>pi\<le>t\<close> \<open>t\<le>2*pi\<close> sin_le_zero by fastforce
          moreover have "r\<ge>0" 
            using asm by (metis add.inverse_inverse add.left_neutral add_uminus_conv_diff
                diff_ge_0_iff_ge norm_ge_zero order_trans zero_le_one)
          ultimately have "sin t * r\<le>0" using mult_le_0_iff by blast
          then show ?thesis by auto
        qed
        also have "... \<le> Im a" using True .
        finally show ?thesis .
      qed
      moreover have "valid_path (g2 r)" unfolding g2_def by auto
      moreover have "a \<notin> path_image (g2 r)"
        unfolding g2_def 
        apply (rule not_on_circlepathI)
        using asm by auto  
      moreover have [symmetric]:"Im (Ln (\<i> * pathfinish (g2 r) - \<i> * a)) = h1 r"
        unfolding h1_def g2_def
        apply (simp only:pathfinish_pathstart_partcirclepath_simps)
        apply (subst (4 10) complex_eq)
        by (auto simp add:algebra_simps Complex_eq)
      moreover have [symmetric]:"Im (Ln (\<i> * pathstart (g2 r) - \<i> * a)) = h2 r"
        unfolding h2_def g2_def
        apply (simp only:pathfinish_pathstart_partcirclepath_simps)
        apply (subst (4 10) complex_eq)
        by (auto simp add:algebra_simps Complex_eq)
      ultimately show "f2 r = (h1 r - h2 r) / (2 * pi)" 
        unfolding f2_def 
        apply (subst Re_winding_number_half_lower)
        by (auto simp add:exp_Euler algebra_simps)
    qed  
    moreover have "((\<lambda>x. (h1 x - h2 x) / (2 * pi)) \<longlongrightarrow> 1/2 ) at_top"
    proof -
      have "(h1 \<longlongrightarrow> pi/2) at_top"
        unfolding h1_def
        apply (subst filterlim_at_top_linear_iff[of 1 _ "Re a - Re z0" ,simplified,symmetric]) 
        using Im_Ln_tendsto_at_top by (simp del:Complex_eq)
      moreover have "(h2 \<longlongrightarrow> - pi/2) at_top"  
        unfolding h2_def
        apply (subst filterlim_at_bot_linear_iff[of "- 1" _ "- Re a + Re z0" ,simplified,symmetric])  
        using Im_Ln_tendsto_at_bot by (simp del:Complex_eq)  
      ultimately have "((\<lambda>x. h1 x- h2 x) \<longlongrightarrow> pi) at_top"    
        by (auto intro: tendsto_eq_intros)
      then show ?thesis
        by (auto intro: tendsto_eq_intros)
    qed
    ultimately show ?thesis by (auto dest:tendsto_cong)
  qed
  moreover have "\<forall>\<^sub>F r in at_top. f2 r = 1 - f1 r"
  proof (rule eventually_at_top_linorderI[of "cmod (a-z0) + 1"])
    fix r assume asm:"r \<ge> cmod (a - z0) + 1"
    have "f1 r + f2 r = Re(winding_number (g1 r +++ g2 r) a)" 
      unfolding f1_def f2_def g1_def g2_def
      apply (subst winding_number_join)
      using asm by (auto intro!:not_on_circlepathI)
    also have "... = Re(winding_number (circlepath z0 r) a)"
    proof -
      have "g1 r +++ g2 r = circlepath z0 r"
        unfolding circlepath_def g1_def g2_def joinpaths_def part_circlepath_def linepath_def
        by (auto simp add:field_simps)
      then show ?thesis by auto
    qed
    also have "... = 1"
    proof -
      have "winding_number (circlepath z0 r) a = 1"
        apply (rule winding_number_circlepath)
        using asm by auto
      then show ?thesis by auto
    qed
    finally have "f1 r+f2 r=1" .
    then show " f2 r = 1 - f1 r" by auto
  qed
  ultimately have "((\<lambda>r. 1 - f1 r) \<longlongrightarrow> 1/2 ) at_top"
    using tendsto_cong[of f2 "\<lambda>r. 1 - f1 r" at_top] by auto
  then have "(f1 \<longlongrightarrow> 1/2 ) at_top" 
    apply (rule_tac tendsto_minus_cancel)
    apply (subst tendsto_add_const_iff[of 1,symmetric])
    by auto
  then show ?thesis unfolding f1_def g1_def by auto
next
  case False
  define g where "g=(\<lambda>r. part_circlepath z0 r 0 pi)"
  define f where "f=(\<lambda>r. Re (winding_number (g r) a))"
  have "(f \<longlongrightarrow> 1/2 ) at_top" 
  proof -
    define h1 where "h1 = (\<lambda>r. Im (Ln (Complex ( Im z0-Im a) (Re a - Re z0 + r))))"
    define h2 where "h2= (\<lambda>r. Im (Ln (Complex (  Im z0 -Im a ) (Re a - Re z0 - r))))"
    have "\<forall>\<^sub>F x in at_top. f x = (h1 x - h2 x) / (2 * pi)"
    proof (rule eventually_at_top_linorderI[of "cmod (a-z0) + 1"])
      fix r assume asm:"r \<ge> cmod (a - z0) + 1"
      have "Im p \<ge> Im a" when "p\<in>path_image (g r)" for p
      proof -
        obtain t where p_def:"p=z0 + of_real r * exp (\<i> * of_real t)" and "0\<le>t" "t\<le>pi"
          using \<open>p\<in>path_image (g r)\<close> 
          unfolding g_def path_image_part_circlepath[of 0 pi,simplified]  
          by auto
        then have "Im p=Im z0 + sin t * r" by (auto simp add:Im_exp)    
        moreover have "sin t * r\<ge>0"
        proof -
          have "sin t\<ge>0" using \<open>0\<le>t\<close> \<open>t\<le>pi\<close> sin_ge_zero by fastforce
          moreover have "r\<ge>0" 
            using asm by (metis add.inverse_inverse add.left_neutral add_uminus_conv_diff
                diff_ge_0_iff_ge norm_ge_zero order_trans zero_le_one)
          ultimately have "sin t * r\<ge>0" by simp
          then show ?thesis by auto
        qed
        ultimately show ?thesis using False by auto
      qed
      moreover have "valid_path (g r)" unfolding g_def by auto
      moreover have "a \<notin> path_image (g r)"
        unfolding g_def 
        apply (rule not_on_circlepathI)
        using asm by auto  
      moreover have [symmetric]:"Im (Ln (\<i> * a - \<i> * pathfinish (g r))) = h1 r"
        unfolding h1_def g_def
        apply (simp only:pathfinish_pathstart_partcirclepath_simps)
        apply (subst (4 9) complex_eq)
        by (auto simp add:algebra_simps Complex_eq)
      moreover have [symmetric]:"Im (Ln (\<i> * a - \<i> * pathstart (g r))) = h2 r"
        unfolding h2_def g_def
        apply (simp only:pathfinish_pathstart_partcirclepath_simps)
        apply (subst (4 9) complex_eq)
        by (auto simp add:algebra_simps Complex_eq)
      ultimately show "f r = (h1 r - h2 r) / (2 * pi)" 
        unfolding f_def 
        apply (subst Re_winding_number_half_upper) 
        by (auto simp add:exp_Euler algebra_simps)
    qed  
    moreover have "((\<lambda>x. (h1 x - h2 x) / (2 * pi)) \<longlongrightarrow> 1/2 ) at_top"
    proof -
      have "(h1 \<longlongrightarrow> pi/2) at_top"
        unfolding h1_def
        apply (subst filterlim_at_top_linear_iff[of 1 _ "- Re a + Re z0" ,simplified,symmetric]) 
        using Im_Ln_tendsto_at_top by (simp del:Complex_eq)
      moreover have "(h2 \<longlongrightarrow> - pi/2) at_top"  
        unfolding h2_def
        apply (subst filterlim_at_bot_linear_iff[of "- 1" _ "Re a - Re z0" ,simplified,symmetric])  
        using Im_Ln_tendsto_at_bot by (simp del:Complex_eq)  
      ultimately have "((\<lambda>x. h1 x- h2 x) \<longlongrightarrow> pi) at_top"    
        by (auto intro: tendsto_eq_intros)
      then show ?thesis
        by (auto intro: tendsto_eq_intros)
    qed
    ultimately show ?thesis by (auto dest:tendsto_cong)
  qed
  then show ?thesis unfolding f_def g_def by auto
qed
  
lemma not_image_at_top_poly_part_circlepath:
  assumes "degree p>0"
  shows "\<forall>\<^sub>F r in at_top. b\<notin>path_image (poly p o part_circlepath z0 r st tt)"  
proof -
  have "finite (proots (p-[:b:]))" 
    apply (rule finite_proots)
    using assms by auto  
  from finite_ball_include[OF this]
  obtain R::real where "R>0" and R_ball:"proots (p-[:b:]) \<subseteq> ball z0 R" by auto
  show ?thesis
  proof (rule eventually_at_top_linorderI[of R])
    fix r assume "r\<ge>R"    
    show  "b\<notin>path_image (poly p o part_circlepath z0 r st tt)"
      unfolding path_image_compose 
    proof clarify
      fix x assume asm:"b = poly p x" "x \<in> path_image (part_circlepath z0 r st tt)"
      then have "x\<in>proots (p-[:b:])" unfolding proots_def by auto
      then have "x\<in>ball z0 r" using R_ball \<open>r\<ge>R\<close> by auto  
      then have "cmod (x- z0) < r" 
        by (simp add: dist_commute dist_norm)
      moreover have "cmod (x - z0) = r"
        using asm(2) in_path_image_part_circlepath \<open>R>0\<close> \<open>r\<ge>R\<close>  by auto  
      ultimately show False by auto
    qed
  qed
qed  

lemma not_image_poly_part_circlepath:
  assumes "degree p>0"
  shows "\<exists>r>0.  b\<notin>path_image (poly p o part_circlepath z0 r st tt)"
proof -
  have "finite (proots (p-[:b:]))" 
    apply (rule finite_proots)
    using assms by auto  
  from finite_ball_include[OF this]
  obtain r::real where "r>0" and r_ball:"proots (p-[:b:]) \<subseteq> ball z0 r" by auto
  have "b\<notin>path_image (poly p o part_circlepath z0 r st tt)"
    unfolding path_image_compose 
  proof clarify
    fix x assume asm:"b = poly p x" "x \<in> path_image (part_circlepath z0 r st tt)"
    then have "x\<in>proots (p-[:b:])" unfolding proots_def by auto
    then have "x\<in>ball z0 r" using r_ball by auto  
    then have "cmod (x- z0) < r" 
      by (simp add: dist_commute dist_norm)
    moreover have "cmod (x - z0) = r"
      using asm(2) in_path_image_part_circlepath \<open>r>0\<close> by auto  
    ultimately show False by auto
  qed
  then show ?thesis using \<open>r>0\<close> by blast
qed
   
lemma Re_winding_number_poly_part_circlepath:
  assumes "degree p>0"
  shows "((\<lambda>r. Re (winding_number (poly p o part_circlepath z0 r 0 pi) 0)) \<longlongrightarrow> degree p/2 ) at_top"
using assms
proof (induct rule:poly_root_induct_alt)
  case 0
  then show ?case by auto
next
  case (no_proots p)
  then have False 
    using Fundamental_Theorem_Algebra.fundamental_theorem_of_algebra constant_degree neq0_conv
    by blast
  then show ?case by auto
next
  case (root a p)
  define g where "g = (\<lambda>r. part_circlepath z0 r 0 pi)"
  define q where "q=[:- a, 1:] * p"
  define w where "w = (\<lambda>r. winding_number (poly q \<circ> g r) 0)"
  have ?case when "degree p=0"
  proof -
    obtain pc where pc_def:"p=[:pc:]" using \<open>degree p = 0\<close> degree_eq_zeroE by blast
    then have "pc\<noteq>0" using root(2) by auto
    have "\<forall>\<^sub>F r in at_top. Re (w r) = Re (winding_number (g r) a)" 
    proof (rule eventually_at_top_linorderI[of "cmod (( pc * a) / pc - z0) + 1"])
      fix r::real assume asm:"cmod ((pc * a) / pc - z0) + 1 \<le> r"
      have "w r =  winding_number ((\<lambda>x. pc*x - pc*a) \<circ> (g r)) 0"
        unfolding w_def pc_def g_def q_def
        apply auto
        by (metis (no_types, opaque_lifting) add.right_neutral mult.commute mult_zero_right 
            poly_0 poly_pCons uminus_add_conv_diff)
      also have "... =  winding_number (g r) a "
        apply (subst winding_number_comp_linear[where b="-pc*a",simplified])
        subgoal using \<open>pc\<noteq>0\<close> .
        subgoal unfolding g_def by auto
        subgoal unfolding g_def
          apply (rule not_on_circlepathI)
          using asm by auto
        subgoal using \<open>pc\<noteq>0\<close> by (auto simp add:field_simps)
        done
      finally have "w r = winding_number (g r) a " .
      then show "Re (w r) = Re (winding_number (g r) a)" by simp
    qed
    moreover have "((\<lambda>r. Re (winding_number (g r) a)) \<longlongrightarrow> 1/2) at_top"
      using Re_winding_number_tendsto_part_circlepath unfolding g_def by auto
    ultimately have "((\<lambda>r. Re (w r)) \<longlongrightarrow> 1/2) at_top"
      by (auto dest!:tendsto_cong)
    moreover have "degree ([:- a, 1:] * p) = 1" unfolding pc_def using \<open>pc\<noteq>0\<close> by auto
    ultimately show ?thesis unfolding w_def g_def comp_def q_def by simp
  qed
  moreover have ?case when "degree p>0"
  proof -
    have "\<forall>\<^sub>F r in at_top. 0 \<notin> path_image (poly q \<circ> g r)"  
      unfolding g_def
      apply (rule not_image_at_top_poly_part_circlepath)
      unfolding q_def using root.prems by blast
    then have "\<forall>\<^sub>F r in at_top. Re (w r) = Re (winding_number (g r) a) 
              + Re (winding_number (poly p \<circ> g r) 0)"
    proof (rule eventually_mono)
      fix r assume asm:"0 \<notin> path_image (poly q \<circ> g r)"
      define cc where "cc= 1 / (of_real (2 * pi) * \<i>)"  
      define pf where "pf=(\<lambda>w. deriv (poly p) w / poly p w)"
      define af where "af=(\<lambda>w. 1/(w-a))"  
      have "w r = cc * contour_integral (g r) (\<lambda>w. deriv (poly q) w / poly q w)"
        unfolding w_def 
        apply (subst winding_number_comp[of UNIV,simplified])
        using asm unfolding g_def cc_def  by auto
      also have "... = cc * contour_integral (g r) (\<lambda>w. deriv (poly p) w / poly p w + 1/(w-a))"  
      proof -
        have "contour_integral (g r) (\<lambda>w. deriv (poly q) w / poly q w) 
            = contour_integral (g r) (\<lambda>w. deriv (poly p) w / poly p w + 1/(w-a))"
        proof (rule contour_integral_eq)   
          fix x assume "x \<in> path_image (g r)"  
          have "deriv (poly q) x = deriv (poly p) x * (x-a) + poly p x" 
          proof -
            have "poly q = (\<lambda>x. (x-a) * poly p x)" 
              apply (rule ext)
              unfolding q_def by (auto simp add:algebra_simps) 
            then show ?thesis    
              apply simp
              apply (subst deriv_mult[of "\<lambda>x. x- a" _ "poly p"])
              by (auto intro:derivative_intros)
          qed
          moreover have "poly p x\<noteq>0 \<and> x-a\<noteq>0" 
          proof (rule ccontr)
            assume "\<not> (poly p x \<noteq> 0 \<and> x - a \<noteq> 0)"
            then have "poly q x=0" unfolding q_def by auto  
            then have "0\<in>poly q ` path_image (g r)"
              using \<open>x \<in> path_image (g r)\<close> by auto
            then show False using \<open>0 \<notin> path_image (poly q \<circ> g r)\<close> 
              unfolding path_image_compose by auto
          qed
          ultimately show "deriv (poly q) x / poly q x = deriv (poly p) x / poly p x + 1 / (x - a)" 
            unfolding q_def by (auto simp add:field_simps)  
        qed
        then show ?thesis by auto
      qed
      also have "... = cc * contour_integral (g r) (\<lambda>w. deriv (poly p) w / poly p w) 
          + cc * contour_integral (g r) (\<lambda>w. 1/(w-a))"  
      proof (subst contour_integral_add)
        have "continuous_on (path_image (g r)) (\<lambda>w. deriv (poly p) w)"
          unfolding deriv_pderiv by (intro continuous_intros)  
        moreover have "\<forall>w\<in>path_image (g r). poly p w \<noteq> 0" 
          using asm unfolding q_def path_image_compose by auto
        ultimately show "(\<lambda>w. deriv (poly p) w / poly p w) contour_integrable_on g r" 
          unfolding g_def
          by (auto intro!: contour_integrable_continuous_part_circlepath continuous_intros)
        show "(\<lambda>w. 1 / (w - a)) contour_integrable_on g r" 
          apply (rule contour_integrable_inversediff)
          subgoal unfolding g_def by auto
          subgoal using asm unfolding q_def path_image_compose by auto
          done
      qed (auto simp add:algebra_simps)
      also have "... =  winding_number (g r) a +  winding_number (poly p o g r) 0"
      proof -
        have "winding_number (poly p o g r) 0
            = cc * contour_integral (g r) (\<lambda>w. deriv (poly p) w / poly p w)"
          apply (subst winding_number_comp[of UNIV,simplified])
          using \<open>0 \<notin> path_image (poly q \<circ> g r)\<close> unfolding path_image_compose q_def g_def cc_def
          by auto
        moreover have "winding_number (g r) a = cc * contour_integral (g r) (\<lambda>w. 1/(w-a))"
          apply (subst winding_number_valid_path)
          using \<open>0 \<notin> path_image (poly q \<circ> g r)\<close> unfolding path_image_compose q_def g_def cc_def
          by auto
        ultimately show ?thesis by auto
      qed
      finally show "Re (w r) = Re (winding_number (g r) a) + Re (winding_number (poly p \<circ> g r) 0)"
        by auto
    qed
    moreover have "((\<lambda>r. Re (winding_number (g r) a) 
              + Re (winding_number (poly p \<circ> g r) 0)) \<longlongrightarrow> degree q / 2) at_top" 
    proof -
      have "((\<lambda>r. Re (winding_number (g r) a)) \<longlongrightarrow>1 / 2) at_top" 
        unfolding g_def by (rule Re_winding_number_tendsto_part_circlepath)  
      moreover have "((\<lambda>r. Re (winding_number (poly p \<circ> g r) 0)) \<longlongrightarrow> degree p / 2) at_top"
        unfolding g_def by (rule root(1)[OF that])
      moreover have "degree q = degree p + 1" 
        unfolding q_def
        apply (subst degree_mult_eq)
        using that by auto
      ultimately show ?thesis
        by (simp add: tendsto_add add_divide_distrib)
    qed
    ultimately have "((\<lambda>r. Re (w r)) \<longlongrightarrow> degree q/2) at_top"
      by (auto dest!:tendsto_cong)
    then show ?thesis unfolding w_def q_def g_def by blast
  qed
  ultimately show ?case by blast
qed     

lemma Re_winding_number_poly_linepth:
  fixes pp::"complex poly"
  defines "g \<equiv> (\<lambda>r. poly pp o linepath (-r) (of_real r))"
  assumes "lead_coeff pp=1" and no_real_zero:"\<forall>x\<in>proots pp. Im x\<noteq>0"
  shows "((\<lambda>r. 2*Re (winding_number (g r) 0) + cindex_pathE (g r) 0 ) \<longlongrightarrow> 0 ) at_top" 
proof -
  define p where "p=map_poly Re pp" 
  define q where "q=map_poly Im pp"
  define f where "f=(\<lambda>t. poly q t / poly p t)"
  have sgnx_top:"sgnx (poly p) at_top = 1"
    unfolding sgnx_poly_at_top sgn_pos_inf_def p_def using \<open>lead_coeff pp=1\<close>
    by (subst lead_coeff_map_poly_nz,auto)
  have not_g_image:"0 \<notin> path_image (g r)" for r
  proof (rule ccontr)
    assume "\<not> 0 \<notin> path_image (g r)"
    then obtain x where "poly pp x=0" "x\<in>closed_segment (- of_real r) (of_real r)"
      unfolding g_def path_image_compose of_real_linepath by auto
    then have "Im x=0" "x\<in>proots pp" 
      using closed_segment_imp_Re_Im(2) unfolding proots_def by fastforce+
    then show False using \<open>\<forall>x\<in>proots pp. Im x\<noteq>0\<close> by auto
  qed    
  have arctan_f_tendsto:"((\<lambda>r. (arctan (f r) -  arctan (f (-r))) / pi) \<longlongrightarrow> 0) at_top"
  proof (cases "degree p>0")
    case True
    have "degree p>degree q" 
    proof -
      have "degree p=degree pp"
        unfolding p_def using \<open>lead_coeff pp=1\<close>
        by (auto intro:map_poly_degree_eq)
      moreover then have "degree q<degree pp"
        unfolding q_def using \<open>lead_coeff pp=1\<close> True
        by (auto intro!:map_poly_degree_less)
      ultimately show ?thesis by auto
    qed
    then have "(f \<longlongrightarrow> 0) at_infinity"
      unfolding f_def using poly_divide_tendsto_0_at_infinity by auto
    then have "(f \<longlongrightarrow> 0) at_bot" "(f \<longlongrightarrow> 0) at_top"
      by (auto elim!:filterlim_mono simp add:at_top_le_at_infinity at_bot_le_at_infinity)
    then have "((\<lambda>r. arctan (f r))\<longlongrightarrow> 0) at_top" "((\<lambda>r. arctan (f (-r)))\<longlongrightarrow> 0) at_top"
      apply -
      subgoal by (auto intro:tendsto_eq_intros)
      subgoal 
        apply (subst tendsto_compose_filtermap[of _ uminus,unfolded comp_def])
        by (auto intro:tendsto_eq_intros simp add:at_bot_mirror[symmetric])
      done
    then show ?thesis 
      by (auto intro:tendsto_eq_intros)
  next
    case False
    obtain c where "f=(\<lambda>r. c)"
    proof -
      have "degree p=0" using False by auto
      moreover have "degree q\<le>degree p"
      proof -
        have "degree p=degree pp" 
          unfolding p_def using \<open>lead_coeff pp=1\<close>
          by (auto intro:map_poly_degree_eq)
        moreover have "degree q\<le>degree pp"
          unfolding q_def by simp
        ultimately show ?thesis by auto
      qed
      ultimately have "degree q=0" by simp
      then obtain pa qa where "p=[:pa:]" "q=[:qa:]"
        using \<open>degree p=0\<close> by (meson degree_eq_zeroE)
      then show ?thesis using that unfolding f_def by auto
    qed
    then show ?thesis by auto
  qed
  have [simp]:"valid_path (g r)" "path (g r)" "finite_ReZ_segments (g r) 0" for r
  proof -
    show "valid_path (g r)" unfolding g_def
      apply (rule valid_path_compose_holomorphic[where S=UNIV])
      by (auto simp add:of_real_linepath)
    then show "path (g r)" using valid_path_imp_path by auto
    show "finite_ReZ_segments (g r) 0"
      unfolding g_def of_real_linepath using finite_ReZ_segments_poly_linepath by simp
  qed
  have g_f_eq:"Im (g r t) / Re (g r t) = (f o (\<lambda>x. 2*r*x - r)) t" for r t 
  proof -
    have "Im (g r t) / Re (g r t) = Im ((poly pp o of_real o (\<lambda>x. 2*r*x - r)) t) 
        / Re ((poly pp o of_real o (\<lambda>x. 2*r*x - r)) t)"
      unfolding g_def linepath_def comp_def 
      by (auto simp add:algebra_simps)
    also have "... = (f o (\<lambda>x. 2*r*x - r)) t"
      unfolding comp_def
      by (simp only:Im_poly_of_real diff_0_right Re_poly_of_real f_def q_def p_def)
    finally show ?thesis .
  qed

  have ?thesis when "proots p={}"
  proof -
    have "\<forall>\<^sub>Fr in at_top. 2 * Re (winding_number (g r) 0) + cindex_pathE (g r) 0
        = (arctan (f r) -  arctan (f (-r))) / pi"
    proof (rule eventually_at_top_linorderI[of 1])
      fix r::real assume "r\<ge>1"
      have image_pos:"\<forall>p\<in>path_image (g r).  0<Re p "
      proof (rule ccontr)
        assume "\<not> (\<forall>p\<in>path_image (g r). 0 < Re p)"
        then obtain t where "poly p t\<le>0" 
          unfolding g_def path_image_compose of_real_linepath p_def 
          using Re_poly_of_real
          apply (simp add:closed_segment_def)
          by (metis not_less of_real_def real_vector.scale_scale scaleR_left_diff_distrib)  
        moreover have False when "poly p t<0"    
        proof -
          have "sgnx (poly p) (at_right t) = -1"  
            using sgnx_poly_nz that by auto
          then obtain x where "x>t" "poly p x = 0"
            using sgnx_at_top_IVT[of p t] sgnx_top by auto
          then have "x\<in>proots p" unfolding proots_def by auto
          then show False using \<open>proots p={}\<close> by auto
        qed
        moreover have False when "poly p t=0"
          using \<open>proots p={}\<close> that unfolding proots_def by auto
        ultimately show False by linarith
      qed
      have "Re (winding_number (g r) 0) = (Im (Ln (pathfinish (g r))) - Im (Ln (pathstart (g r)))) 
          / (2 * pi)"
        apply (rule Re_winding_number_half_right[of "g r" 0,simplified])
        subgoal using image_pos by auto
        subgoal by (auto simp add:not_g_image)
        done
      also have "... = (arctan (f r) - arctan (f (-r)))/(2*pi)"
      proof -
        have "Im (Ln (pathfinish (g r))) = arctan (f r)"
        proof -
          have "Re (pathfinish (g r)) > 0"
            by (auto intro: image_pos[rule_format])
          then have "Im (Ln (pathfinish (g r))) 
              = arctan (Im (pathfinish (g r)) / Re (pathfinish (g r)))" 
            by (subst Im_Ln_eq,auto)
          also have "... = arctan (f r)"
            unfolding path_defs by (subst g_f_eq,auto)
          finally show ?thesis .
        qed
        moreover have "Im (Ln (pathstart (g r))) = arctan (f (-r))"
        proof -
          have "Re (pathstart (g r)) > 0"
            by (auto intro: image_pos[rule_format])
          then have "Im (Ln (pathstart (g r))) 
              = arctan (Im (pathstart (g r)) / Re (pathstart (g r)))" 
            by (subst Im_Ln_eq,auto)
          also have "... = arctan (f (-r))"
            unfolding path_defs by (subst g_f_eq,auto)
          finally show ?thesis .
        qed  
        ultimately show ?thesis by auto
      qed
      finally have "Re (winding_number (g r) 0) = (arctan (f r) - arctan (f (-r)))/(2*pi)" . 
      moreover have "cindex_pathE (g r) 0 = 0"
      proof -
        have "cindex_pathE (g r) 0 = cindex_pathE (poly pp o of_real o (\<lambda>x. 2*r*x - r)) 0"
          unfolding g_def linepath_def comp_def 
          by (auto simp add:algebra_simps)
        also have "... = cindexE 0 1 (f o (\<lambda>x. 2*r*x - r)) "
          unfolding cindex_pathE_def comp_def
          by (simp only:Im_poly_of_real diff_0_right Re_poly_of_real f_def q_def p_def)
        also have "... = cindexE (-r) r f"
          apply (subst cindexE_linear_comp[of "2*r" 0 1 _ "-r",simplified])
          using \<open>r\<ge>1\<close> by auto
        also have "... = 0"
        proof -
          have "jumpF f (at_left x) =0" "jumpF f (at_right x) = 0" when "x\<in>{-r..r}" for x
          proof -
            have "poly p x\<noteq>0" using \<open>proots p={}\<close> unfolding proots_def by auto
            then show "jumpF f (at_left x) =0" "jumpF f (at_right x) = 0"
              unfolding f_def by (auto intro!: jumpF_not_infinity continuous_intros)
          qed
          then show ?thesis unfolding cindexE_def by auto
        qed
        finally show ?thesis .
      qed
      ultimately show "2 * Re (winding_number (g r) 0) + cindex_pathE (g r) 0 
          = (arctan (f r) -  arctan (f (-r))) / pi"   
        unfolding path_defs by (auto simp add:field_simps)
    qed
    with arctan_f_tendsto show ?thesis by (auto dest:tendsto_cong)
  qed
  moreover have ?thesis when "proots p\<noteq>{}"
  proof -
    define max_r where "max_r=Max (proots p)"
    define min_r where "min_r=Min (proots p)"
    have "max_r \<in>proots p" "min_r \<in>proots p" "min_r\<le>max_r" and 
      min_max_bound:"\<forall>p\<in>proots p. p\<in>{min_r..max_r}"
    proof -
      have "p\<noteq>0" 
      proof -
        have "(0::real) \<noteq> 1"
          by simp
        then show ?thesis
          by (metis (full_types) \<open>p \<equiv> map_poly Re pp\<close> assms(2) coeff_0 coeff_map_poly one_complex.simps(1) zero_complex.sel(1))
      qed
      then have "finite (proots p)" by auto
      then show "max_r \<in>proots p" "min_r \<in>proots p"  
        using Min_in Max_in that unfolding max_r_def min_r_def by fast+
      then show "\<forall>p\<in>proots p. p\<in>{min_r..max_r}"
        using Min_le Max_ge \<open>finite (proots p)\<close> unfolding max_r_def min_r_def by auto
      then show "min_r\<le>max_r" using \<open>max_r\<in>proots p\<close> by auto
    qed
    have "\<forall>\<^sub>Fr in at_top. 2 * Re (winding_number (g r) 0) + cindex_pathE (g r) 0
        = (arctan (f r) -  arctan (f (-r))) / pi"
    proof (rule eventually_at_top_linorderI[of "max (norm max_r) (norm min_r) + 1"])  
      fix r assume r_asm:"max (norm max_r) (norm min_r) + 1 \<le> r"
      then have "r\<noteq>0" "min_r>-r" "max_r<r" by auto
      define u where "u=(min_r + r)/(2*r)" 
      define v where "v=(max_r + r)/(2*r)"  
      have uv:"u\<in>{0..1}" "v\<in>{0..1}" "u\<le>v"   
        unfolding u_def v_def using r_asm  \<open>min_r\<le>max_r\<close> 
        by (auto simp add:field_simps)
      define g1 where "g1=subpath 0 u (g r)"
      define g2 where "g2=subpath u v (g r)"
      define g3 where "g3=subpath v 1 (g r)"
      have "path g1" "path g2" "path g3" "valid_path g1" "valid_path g2" "valid_path g3"
        unfolding g1_def g2_def g3_def using uv
        by (auto intro!:path_subpath valid_path_subpath)
      define wc_add where "wc_add = (\<lambda>g. 2*Re (winding_number g 0)  + cindex_pathE g 0)"
      have "wc_add (g r) = wc_add g1 + wc_add g2 + wc_add g3" 
      proof -
        have "winding_number (g r) 0 = winding_number g1 0 + winding_number g2 0 + winding_number g3 0"
          unfolding g1_def g2_def g3_def using \<open>u\<in>{0..1}\<close> \<open>v\<in>{0..1}\<close> not_g_image
          by (subst winding_number_subpath_combine,simp_all)+
        moreover have "cindex_pathE (g r) 0 = cindex_pathE g1 0 + cindex_pathE g2 0 + cindex_pathE g3 0"
          unfolding g1_def g2_def g3_def using \<open>u\<in>{0..1}\<close> \<open>v\<in>{0..1}\<close> \<open>u\<le>v\<close> not_g_image
          by (subst cindex_pathE_subpath_combine,simp_all)+
        ultimately show ?thesis unfolding wc_add_def by auto
      qed
      moreover have "wc_add g2=0"
      proof -
        have "2 * Re (winding_number g2 0) = - cindex_pathE g2 0"
          unfolding g2_def
          apply (rule winding_number_cindex_pathE_aux)
          subgoal using uv by (auto intro:finite_ReZ_segments_subpath)
          subgoal using uv by (auto intro:valid_path_subpath)
          subgoal using Path_Connected.path_image_subpath_subset \<open>\<And>r. path (g r)\<close> not_g_image uv 
            by blast 
          subgoal unfolding subpath_def v_def g_def linepath_def using r_asm \<open>max_r \<in>proots p\<close>
            by (auto simp add:field_simps Re_poly_of_real p_def)
          subgoal unfolding subpath_def u_def g_def linepath_def using r_asm \<open>min_r \<in>proots p\<close>
            by (auto simp add:field_simps Re_poly_of_real p_def)
          done
        then show ?thesis unfolding wc_add_def by auto
      qed
      moreover have "wc_add g1=- arctan (f (-r)) / pi" 
      proof -
        have g1_pq:
          "Re (g1 t) = poly p (min_r*t+r*t-r)"
          "Im (g1 t) = poly q (min_r*t+r*t-r)"
          "Im (g1 t)/Re (g1 t) = (f o (\<lambda>x. (min_r+r)*x - r)) t"
          for t
        proof -
          have "g1 t = poly pp (of_real (min_r*t+r*t-r))"
            using \<open>r\<noteq>0\<close>  unfolding g1_def g_def linepath_def subpath_def u_def p_def 
            by (auto simp add:field_simps)
          then show 
              "Re (g1 t) = poly p (min_r*t+r*t-r)"
              "Im (g1 t) = poly q (min_r*t+r*t-r)"
            unfolding p_def q_def 
            by (simp only:Re_poly_of_real Im_poly_of_real)+
          then show "Im (g1 t)/Re (g1 t) = (f o (\<lambda>x. (min_r+r)*x - r)) t"
            unfolding f_def by (auto simp add:algebra_simps) 
        qed
        have "Re(g1 1)=0"
          using \<open>r\<noteq>0\<close> Re_poly_of_real \<open>min_r\<in>proots p\<close> 
          unfolding g1_def subpath_def u_def g_def linepath_def 
          by (auto simp add:field_simps p_def)
        have "0 \<notin> path_image g1"
          by (metis (full_types) path_image_subpath_subset \<open>\<And>r. path (g r)\<close> 
              atLeastAtMost_iff g1_def le_less not_g_image subsetCE uv(1) zero_le_one)
            
        have wc_add_pos:"wc_add h = - arctan (poly q (- r) / poly p (-r)) / pi" when 
          Re_pos:"\<forall>x\<in>{0..<1}. 0 < (Re \<circ> h) x"
          and hp:"\<forall>t. Re (h t) = c*poly p (min_r*t+r*t-r)"
          and hq:"\<forall>t. Im (h t) = c*poly q (min_r*t+r*t-r)"
          and [simp]:"c\<noteq>0"
          (*and hpq:"\<forall>t. Im (h t)/Re (h t) = (f o (\<lambda>x. (min_r+r)*x - r)) t"*)
          and "Re (h 1) = 0"
          and "valid_path h"
          and h_img:"0 \<notin> path_image h"
          for h c
        proof -
          define f where "f=(\<lambda>t. c*poly q t / (c*poly p t))"
          define farg where "farg= (if 0 < Im (h 1) then pi / 2 else - pi / 2)"
          have "Re (winding_number h 0) = (Im (Ln (pathfinish h)) 
              - Im (Ln (pathstart h))) / (2 * pi)"
            apply (rule Re_winding_number_half_right[of h 0,simplified])
            subgoal using that \<open>Re (h 1) = 0\<close> unfolding path_image_def 
              by (auto simp add:le_less)
            subgoal using \<open>valid_path h\<close> .
            subgoal using h_img .
            done
          also have "... = (farg - arctan (f (-r))) / (2 * pi)"
          proof -
            have "Im (Ln (pathfinish h)) = farg"
              using \<open>Re(h 1)=0\<close> unfolding farg_def path_defs
              apply (subst Im_Ln_eq)
              subgoal using h_img unfolding path_defs by fastforce
              subgoal by simp
              done
            moreover have "Im (Ln (pathstart h)) = arctan (f (-r))"
            proof -
              have "pathstart h \<noteq> 0" 
                using h_img 
                by (metis pathstart_in_path_image)
              then have "Im (Ln (pathstart h)) = arctan (Im (pathstart h) / Re (pathstart h))"
                using Re_pos[rule_format,of 0]
                by (simp add: Im_Ln_eq path_defs)
              also have "... = arctan (f (-r))"
                unfolding f_def path_defs hp[rule_format] hq[rule_format] 
                by simp
              finally show ?thesis .
            qed
            ultimately show ?thesis by auto
          qed
          finally have "Re (winding_number h 0) = (farg - arctan (f (-r))) / (2 * pi)" .
          moreover have "cindex_pathE h 0 = (-farg/pi)"
          proof -
            have "cindex_pathE h 0 = cindexE 0 1 (f \<circ> (\<lambda>x. (min_r + r) * x - r))"
              unfolding cindex_pathE_def using \<open>c\<noteq>0\<close>
              by (auto simp add:hp hq f_def comp_def algebra_simps) 
            also have "... = cindexE (-r) min_r f"
              apply (subst cindexE_linear_comp[where b="-r",simplified])
              using r_asm by auto
            also have "... = - jumpF f (at_left min_r)"
            proof -
              define right where "right = {x. jumpF f (at_right x) \<noteq> 0 \<and> - r \<le> x \<and> x < min_r}"
              define left where "left = {x. jumpF f (at_left x) \<noteq> 0 \<and> - r < x \<and> x \<le> min_r}"
              have *:"jumpF f (at_right x) =0" "jumpF f (at_left x) =0" when "x\<in>{-r..<min_r}" for x
              proof -
                have False when "poly p x =0" 
                proof -
                  have "x\<ge>min_r"
                    using min_max_bound[rule_format,of x] that by auto
                  then show False using \<open>x\<in>{-r..<min_r}\<close> by auto
                qed
                then show "jumpF f (at_right x) =0" "jumpF f (at_left x) =0"
                  unfolding f_def by (auto intro!:jumpF_not_infinity continuous_intros) 
              qed
              then have "right = {}" 
                unfolding right_def by force
              moreover have "left = (if jumpF f (at_left min_r) = 0 then {} else {min_r})"  
                unfolding left_def le_less using * r_asm by force  
              ultimately show ?thesis
                unfolding cindexE_def by (fold left_def right_def,auto)
            qed
            also have "... = (-farg/pi)"
            proof -
              have p_pos:"c*poly p x > 0" when "x \<in> {- r<..<min_r}" for x
              proof -
                define hh where "hh=(\<lambda>t. min_r*t+r*t-r)"
                have "(x+r)/(min_r+r) \<in> {0..<1}"
                  using that r_asm by (auto simp add:field_simps)
                then have "0 < c*poly p (hh ((x+r)/(min_r+r)))"
                  apply (drule_tac Re_pos[rule_format])
                  unfolding comp_def hp[rule_format]  hq[rule_format] hh_def .
                moreover have "hh ((x+r)/(min_r+r)) = x"
                  unfolding hh_def using \<open>min_r>-r\<close> 
                  apply (auto simp add:divide_simps)
                  by (auto simp add:algebra_simps)
                ultimately show ?thesis by simp
              qed
              
              have "c*poly q min_r \<noteq>0"
                using no_real_zero \<open>c\<noteq>0\<close>
                by (metis Im_complex_of_real UNIV_I \<open>min_r \<in> proots p\<close> cpoly_of_decompose 
                    mult_eq_0_iff p_def poly_cpoly_of_real_iff proots_within_iff q_def)
                
              moreover have ?thesis when "c*poly q min_r > 0"
              proof -
                have "0 < Im (h 1)" unfolding hq[rule_format] hp[rule_format] using that by auto
                moreover have "jumpF f (at_left min_r) = 1/2"
                proof -
                  have "((\<lambda>t. c*poly p t) has_sgnx 1) (at_left min_r)"
                    unfolding has_sgnx_def
                    apply (rule eventually_at_leftI[of "-r"])
                    using p_pos \<open>min_r>-r\<close> by auto
                  then have "filterlim f at_top (at_left min_r)" 
                    unfolding f_def
                    apply (subst filterlim_divide_at_bot_at_top_iff[of _ "c*poly q min_r"])
                    using that \<open>min_r\<in>proots p\<close> by (auto intro!:tendsto_eq_intros)
                  then show ?thesis unfolding jumpF_def by auto
                qed
                ultimately show ?thesis unfolding farg_def by auto
              qed
              moreover have ?thesis when "c*poly q min_r < 0"
              proof -
                have "0 > Im (h 1)" unfolding hq[rule_format] hp[rule_format] using that by auto
                moreover have "jumpF f (at_left min_r) = - 1/2"
                proof -
                  have "((\<lambda>t. c*poly p t) has_sgnx 1) (at_left min_r)"
                    unfolding has_sgnx_def
                    apply (rule eventually_at_leftI[of "-r"])
                    using p_pos \<open>min_r>-r\<close> by auto
                  then have "filterlim f at_bot (at_left min_r)" 
                    unfolding f_def
                    apply (subst filterlim_divide_at_bot_at_top_iff[of _ "c*poly q min_r"])
                    using that \<open>min_r\<in>proots p\<close> by (auto intro!:tendsto_eq_intros)
                  then show ?thesis unfolding jumpF_def by auto
                qed
                ultimately show ?thesis unfolding farg_def by auto
              qed 
              ultimately show ?thesis by linarith
            qed
            finally show ?thesis .
          qed
          ultimately show ?thesis unfolding wc_add_def f_def by (auto simp add:field_simps)  
        qed
        
        have "\<forall>x\<in>{0..<1}. (Re \<circ> g1) x \<noteq> 0" 
        proof (rule ccontr)
          assume "\<not> (\<forall>x\<in>{0..<1}. (Re \<circ> g1) x \<noteq> 0)"
          then obtain t where t_def:"Re (g1 t) =0" "t\<in>{0..<1}"
            unfolding path_image_def by fastforce
          define m where "m=min_r*t+r*t-r"
          have "poly p m=0"
          proof -
            have "Re (g1 t) = Re (poly pp (of_real m))"
              unfolding m_def g1_def g_def linepath_def subpath_def u_def using \<open>r\<noteq>0\<close>
              by (auto simp add:field_simps)
            then show ?thesis using t_def unfolding Re_poly_of_real p_def by auto 
          qed
          moreover have "m<min_r"
          proof -
            have "min_r+r>0" using r_asm by simp
            then have "(min_r + r)*(t-1)<0" using \<open>t\<in>{0..<1}\<close> 
              by (simp add: mult_pos_neg)  
            then show ?thesis unfolding m_def by (auto simp add:algebra_simps)
          qed
          ultimately show False using min_max_bound unfolding proots_def by auto
        qed
        then have "(\<forall>x\<in>{0..<1}. 0 < (Re \<circ> g1) x) \<or> (\<forall>x\<in>{0..<1}. (Re \<circ> g1) x < 0)"
          apply (elim continuous_on_neq_split)
          using \<open>path g1\<close> unfolding path_def 
          by (auto intro!:continuous_intros elim:continuous_on_subset)
        moreover have ?thesis when "\<forall>x\<in>{0..<1}. (Re \<circ> g1) x < 0"
        proof -
          have "wc_add (uminus o g1) = - arctan (f (- r)) / pi"
            unfolding f_def
            apply (rule wc_add_pos[of _ "-1"])
            using g1_pq that \<open>min_r \<in>proots p\<close> \<open>valid_path g1\<close> \<open>0 \<notin> path_image g1\<close>  
            by (auto simp add:path_image_compose)
          moreover have "wc_add (uminus \<circ> g1) = wc_add g1"
            unfolding wc_add_def cindex_pathE_def
            apply (subst winding_number_uminus_comp)
            using \<open>valid_path g1\<close> \<open>0 \<notin> path_image g1\<close> by auto   
          ultimately show ?thesis by auto
        qed
        moreover have ?thesis when "\<forall>x\<in>{0..<1}. (Re \<circ> g1) x > 0"
          unfolding f_def
          apply (rule wc_add_pos[of _ "1"])
          using g1_pq that \<open>min_r \<in>proots p\<close> \<open>valid_path g1\<close> \<open>0 \<notin> path_image g1\<close>  
          by (auto simp add:path_image_compose)
        ultimately show ?thesis by blast
      qed
      moreover have "wc_add g3 = arctan (f r) / pi" 
      proof -
        have g3_pq:
          "Re (g3 t) = poly p ((r-max_r)*t + max_r)"
          "Im (g3 t) = poly q ((r-max_r)*t + max_r)"
          "Im (g3 t)/Re (g3 t) = (f o (\<lambda>x. (r-max_r)*x + max_r)) t"
          for t
        proof -
          have "g3 t = poly pp (of_real ((r-max_r)*t + max_r))"
            using \<open>r\<noteq>0\<close> \<open>max_r<r\<close>  unfolding g3_def g_def linepath_def subpath_def v_def p_def 
            by (auto simp add:algebra_simps)
          then show 
              "Re (g3 t) = poly p ((r-max_r)*t + max_r)"
              "Im (g3 t) = poly q ((r-max_r)*t + max_r)"
            unfolding p_def q_def 
            by (simp only:Re_poly_of_real Im_poly_of_real)+
          then show "Im (g3 t)/Re (g3 t) = (f o (\<lambda>x. (r-max_r)*x + max_r)) t"
            unfolding f_def by (auto simp add:algebra_simps) 
        qed
        have "Re(g3 0)=0"
          using \<open>r\<noteq>0\<close> Re_poly_of_real \<open>max_r\<in>proots p\<close> 
          unfolding g3_def subpath_def v_def g_def linepath_def 
          by (auto simp add:field_simps p_def)
        have "0 \<notin> path_image g3"
        proof -
          have "(1::real) \<in> {0..1}"
            by auto
          then show ?thesis
            using Path_Connected.path_image_subpath_subset \<open>\<And>r. path (g r)\<close> g3_def not_g_image uv(2) by blast
        qed
            
        have wc_add_pos:"wc_add h = arctan (poly q r / poly p r) / pi" when 
          Re_pos:"\<forall>x\<in>{0<..1}. 0 < (Re \<circ> h) x"
          and hp:"\<forall>t. Re (h t) = c*poly p ((r-max_r)*t + max_r)"
          and hq:"\<forall>t. Im (h t) = c*poly q ((r-max_r)*t + max_r)"
          and [simp]:"c\<noteq>0"
          (*and hpq:"\<forall>t. Im (h t)/Re (h t) = (f o (\<lambda>x. (min_r+r)*x - r)) t"*)
          and "Re (h 0) = 0"
          and "valid_path h"
          and h_img:"0 \<notin> path_image h"
          for h c
        proof -
          define f where "f=(\<lambda>t. c*poly q t / (c*poly p t))"
          define farg where "farg= (if 0 < Im (h 0) then pi / 2 else - pi / 2)"
          have "Re (winding_number h 0) = (Im (Ln (pathfinish h)) 
              - Im (Ln (pathstart h))) / (2 * pi)"
            apply (rule Re_winding_number_half_right[of h 0,simplified])
            subgoal using that \<open>Re (h 0) = 0\<close> unfolding path_image_def 
              by (auto simp add:le_less)
            subgoal using \<open>valid_path h\<close> .
            subgoal using h_img .
            done
          also have "... = (arctan (f r) - farg) / (2 * pi)"
          proof -
            have "Im (Ln (pathstart h)) = farg"
              using \<open>Re(h 0)=0\<close> unfolding farg_def path_defs
              apply (subst Im_Ln_eq)
              subgoal using h_img unfolding path_defs by fastforce
              subgoal by simp
              done
            moreover have "Im (Ln (pathfinish h)) = arctan (f r)"
            proof -
              have "pathfinish h \<noteq> 0" 
                using h_img 
                by (metis pathfinish_in_path_image)
              then have "Im (Ln (pathfinish h)) = arctan (Im (pathfinish h) / Re (pathfinish h))"
                using Re_pos[rule_format,of 1]
                by (simp add: Im_Ln_eq path_defs)
              also have "... = arctan (f r)"
                unfolding f_def path_defs hp[rule_format] hq[rule_format] 
                by simp
              finally show ?thesis .
            qed
            ultimately show ?thesis by auto
          qed
          finally have "Re (winding_number h 0) = (arctan (f r) - farg) / (2 * pi)" .
          moreover have "cindex_pathE h 0 = farg/pi"
          proof -
            have "cindex_pathE h 0 = cindexE 0 1 (f \<circ> (\<lambda>x. (r-max_r)*x + max_r))"
              unfolding cindex_pathE_def using \<open>c\<noteq>0\<close>
              by (auto simp add:hp hq f_def comp_def algebra_simps) 
            also have "... = cindexE max_r r f"
              apply (subst cindexE_linear_comp)
              using r_asm by auto
            also have "... = jumpF f (at_right max_r)"
            proof -
              define right where "right = {x. jumpF f (at_right x) \<noteq> 0 \<and> max_r \<le> x \<and> x < r}"
              define left where "left = {x. jumpF f (at_left x) \<noteq> 0 \<and> max_r < x \<and> x \<le> r}"
              have *:"jumpF f (at_right x) =0" "jumpF f (at_left x) =0" when "x\<in>{max_r<..r}" for x
              proof -
                have False when "poly p x =0" 
                proof -
                  have "x\<le>max_r"
                    using min_max_bound[rule_format,of x] that by auto
                  then show False using \<open>x\<in>{max_r<..r}\<close> by auto
                qed
                then show "jumpF f (at_right x) =0" "jumpF f (at_left x) =0"
                  unfolding f_def by (auto intro!:jumpF_not_infinity continuous_intros) 
              qed
              then have "left = {}" 
                unfolding left_def by force
              moreover have "right = (if jumpF f (at_right max_r) = 0 then {} else {max_r})"  
                unfolding right_def le_less using * r_asm by force  
              ultimately show ?thesis
                unfolding cindexE_def by (fold left_def right_def,auto)
            qed
            also have "... = farg/pi"
            proof -
              have p_pos:"c*poly p x > 0" when "x \<in> {max_r<..<r}" for x
              proof -
                define hh where "hh=(\<lambda>t. (r-max_r)*t + max_r)"
                have "(x-max_r)/(r-max_r) \<in> {0<..1}"
                  using that r_asm by (auto simp add:field_simps)
                then have "0 < c*poly p (hh ((x-max_r)/(r-max_r)))"
                  apply (drule_tac Re_pos[rule_format]) 
                  unfolding comp_def hp[rule_format]  hq[rule_format] hh_def .
                moreover have "hh ((x-max_r)/(r-max_r)) = x"
                  unfolding hh_def using \<open>max_r<r\<close> 
                  by (auto simp add:divide_simps)
                ultimately show ?thesis by simp
              qed
              
              have "c*poly q max_r \<noteq>0"
                using no_real_zero \<open>c\<noteq>0\<close>
                by (metis Im_complex_of_real UNIV_I \<open>max_r \<in> proots p\<close> cpoly_of_decompose 
                    mult_eq_0_iff p_def poly_cpoly_of_real_iff proots_within_iff q_def)
                
              moreover have ?thesis when "c*poly q max_r > 0"
              proof -
                have "0 < Im (h 0)" unfolding hq[rule_format] hp[rule_format] using that by auto
                moreover have "jumpF f (at_right max_r) = 1/2"
                proof -
                  have "((\<lambda>t. c*poly p t) has_sgnx 1) (at_right max_r)"
                    unfolding has_sgnx_def 
                    apply (rule eventually_at_rightI[of _ "r"])
                    using p_pos \<open>max_r<r\<close> by auto
                  then have "filterlim f at_top (at_right max_r)" 
                    unfolding f_def
                    apply (subst filterlim_divide_at_bot_at_top_iff[of _ "c*poly q max_r"])
                    using that \<open>max_r\<in>proots p\<close> by (auto intro!:tendsto_eq_intros)
                  then show ?thesis unfolding jumpF_def by auto
                qed
                ultimately show ?thesis unfolding farg_def by auto
              qed
              moreover have ?thesis when "c*poly q max_r < 0"
              proof -
                have "0 > Im (h 0)" unfolding hq[rule_format] hp[rule_format] using that by auto
                moreover have "jumpF f (at_right max_r) = - 1/2"
                proof -
                  have "((\<lambda>t. c*poly p t) has_sgnx 1) (at_right max_r)"
                    unfolding has_sgnx_def
                    apply (rule eventually_at_rightI[of _ "r"])
                    using p_pos \<open>max_r<r\<close> by auto
                  then have "filterlim f at_bot (at_right max_r)" 
                    unfolding f_def
                    apply (subst filterlim_divide_at_bot_at_top_iff[of _ "c*poly q max_r"])
                    using that \<open>max_r\<in>proots p\<close> by (auto intro!:tendsto_eq_intros)
                  then show ?thesis unfolding jumpF_def by auto
                qed
                ultimately show ?thesis unfolding farg_def by auto
              qed 
              ultimately show ?thesis by linarith
            qed
            finally show ?thesis .
          qed
          ultimately show ?thesis unfolding wc_add_def f_def by (auto simp add:field_simps)  
        qed
        
        have "\<forall>x\<in>{0<..1}. (Re \<circ> g3) x \<noteq> 0" 
        proof (rule ccontr)
          assume "\<not> (\<forall>x\<in>{0<..1}. (Re \<circ> g3) x \<noteq> 0)"
          then obtain t where t_def:"Re (g3 t) =0" "t\<in>{0<..1}"
            unfolding path_image_def by fastforce
          define m where "m=(r-max_r)*t + max_r"
          have "poly p m=0"
          proof -
            have "Re (g3 t) = Re (poly pp (of_real m))"
              unfolding m_def g3_def g_def linepath_def subpath_def v_def using \<open>r\<noteq>0\<close>
              by (auto simp add:algebra_simps)
            then show ?thesis using t_def unfolding Re_poly_of_real p_def by auto 
          qed
          moreover have "m>max_r"
          proof -
            have "r-max_r>0" using r_asm by simp
            then have "(r - max_r)*t>0" using \<open>t\<in>{0<..1}\<close> 
              by (simp add: mult_pos_neg)  
            then show ?thesis unfolding m_def by (auto simp add:algebra_simps)
          qed
          ultimately show False using min_max_bound unfolding proots_def by auto
        qed
        then have "(\<forall>x\<in>{0<..1}. 0 < (Re \<circ> g3) x) \<or> (\<forall>x\<in>{0<..1}. (Re \<circ> g3) x < 0)"
          apply (elim continuous_on_neq_split)
          using \<open>path g3\<close> unfolding path_def 
          by (auto intro!:continuous_intros elim:continuous_on_subset)
        moreover have ?thesis when "\<forall>x\<in>{0<..1}. (Re \<circ> g3) x < 0"
        proof -
          have "wc_add (uminus o g3) = arctan (f r) / pi"
            unfolding f_def
            apply (rule wc_add_pos[of _ "-1"])
            using g3_pq that \<open>max_r \<in>proots p\<close> \<open>valid_path g3\<close> \<open>0 \<notin> path_image g3\<close>  
            by (auto simp add:path_image_compose)
          moreover have "wc_add (uminus \<circ> g3) = wc_add g3"
            unfolding wc_add_def cindex_pathE_def
            apply (subst winding_number_uminus_comp)
            using \<open>valid_path g3\<close> \<open>0 \<notin> path_image g3\<close> by auto   
          ultimately show ?thesis by auto
        qed
        moreover have ?thesis when "\<forall>x\<in>{0<..1}. (Re \<circ> g3) x > 0"
          unfolding f_def
          apply (rule wc_add_pos[of _ "1"])
          using g3_pq that \<open>max_r \<in>proots p\<close> \<open>valid_path g3\<close> \<open>0 \<notin> path_image g3\<close>  
          by (auto simp add:path_image_compose)
        ultimately show ?thesis by blast
      qed  
      ultimately have "wc_add (g r) = (arctan (f r) - arctan (f (-r))) / pi " 
        by (auto simp add:field_simps)
      then show "2 * Re (winding_number (g r) 0) + cindex_pathE (g r) 0 
          = (arctan (f r) - arctan (f (- r))) / pi" 
        unfolding wc_add_def .
    qed
    with arctan_f_tendsto show ?thesis by (auto dest:tendsto_cong)
  qed
  ultimately show ?thesis by auto
qed
  
lemma proots_upper_cindex_eq:
  assumes "lead_coeff p=1" and no_real_roots:"\<forall>x\<in>proots p. Im x\<noteq>0" 
  shows "proots_upper p =
             (degree p - cindex_poly_ubd (map_poly Im p) (map_poly Re p)) /2"  
proof (cases "degree p = 0")
  case True
  then obtain c where "p=[:c:]" using degree_eq_zeroE by blast
  then have p_def:"p=[:1:]" using \<open>lead_coeff p=1\<close> by simp
  have "proots_count p {x. Im x>0} = 0" unfolding p_def proots_count_def by auto  
  moreover have "cindex_poly_ubd (map_poly Im p) (map_poly Re p) = 0"
    apply (subst cindex_poly_ubd_code)
    unfolding p_def 
    by (auto simp add:map_poly_pCons changes_R_smods_def changes_poly_neg_inf_def 
        changes_poly_pos_inf_def)  
  ultimately show ?thesis using True unfolding proots_upper_def by auto
next
  case False
  then have "degree p>0" "p\<noteq>0" by auto
  define w1 where "w1=(\<lambda>r. Re (winding_number (poly p \<circ> 
              (\<lambda>x. complex_of_real (linepath (- r) (of_real r) x))) 0))"  
  define w2 where "w2=(\<lambda>r. Re (winding_number (poly p \<circ> part_circlepath 0 r 0 pi) 0))"
  define cp where "cp=(\<lambda>r. cindex_pathE (poly p \<circ> (\<lambda>x. 
      of_real (linepath (- r) (of_real r) x))) 0)"
  define ci where "ci=(\<lambda>r. cindexE (-r) r (\<lambda>x. poly (map_poly Im p) x/poly (map_poly Re p) x))"
  define cubd where "cubd =cindex_poly_ubd (map_poly Im p) (map_poly Re p)"
  obtain R where "proots p \<subseteq> ball 0 R" and "R>0"
    using \<open>p\<noteq>0\<close> finite_ball_include[of "proots p" 0] by auto
  have "((\<lambda>r. w1 r  +w2 r+ cp r / 2 -ci r/2)
       \<longlongrightarrow> real (degree p) / 2 - of_int cubd / 2) at_top"  
  proof -
    have t1:"((\<lambda>r. 2 * w1 r + cp r) \<longlongrightarrow> 0) at_top"
      using Re_winding_number_poly_linepth[OF assms] unfolding w1_def cp_def by auto
    have t2:"(w2 \<longlongrightarrow> real (degree p) / 2) at_top"
      using Re_winding_number_poly_part_circlepath[OF \<open>degree p>0\<close>,of 0] unfolding w2_def by auto
    have t3:"(ci \<longlongrightarrow> of_int cubd) at_top"
      apply (rule tendsto_eventually)
      using cindex_poly_ubd_eventually[of "map_poly Im p" "map_poly Re p"] 
      unfolding ci_def cubd_def by auto
    from tendsto_add[OF tendsto_add[OF tendsto_mult_left[OF t3,of "-1/2",simplified] 
         tendsto_mult_left[OF t1,of "1/2",simplified]]
         t2]
    show ?thesis by (simp add:algebra_simps)
  qed
  moreover have "\<forall>\<^sub>F r in at_top. w1 r  +w2 r+ cp r / 2 -ci r/2 = proots_count p {x. Im x>0}" 
  proof (rule eventually_at_top_linorderI[of R])
    fix r assume "r\<ge>R"
    then have r_ball:"proots p \<subseteq> ball 0 r" and "r>0"
      using \<open>R>0\<close> \<open>proots p \<subseteq> ball 0 R\<close> by auto
    define ll where "ll=linepath (- complex_of_real r) r"
    define rr where "rr=part_circlepath 0 r 0 pi"
    define lr where "lr = ll +++ rr"
    have img_ll:"path_image ll \<subseteq> - proots p" and img_rr: "path_image rr \<subseteq> - proots p" 
      subgoal unfolding ll_def using \<open>0 < r\<close> closed_segment_degen_complex(2) no_real_roots by auto
      subgoal unfolding rr_def using in_path_image_part_circlepath \<open>0 < r\<close> r_ball by fastforce 
      done
    have [simp]:"valid_path (poly p o ll)" "valid_path (poly p o rr)"
        "valid_path ll" "valid_path rr" 
        "pathfinish rr=pathstart ll" "pathfinish ll = pathstart rr"
    proof -
      show "valid_path (poly p o ll)" "valid_path (poly p o rr)"
        unfolding ll_def rr_def by (auto intro:valid_path_compose_holomorphic)
      then show "valid_path ll" "valid_path rr" unfolding ll_def rr_def by auto
      show "pathfinish rr=pathstart ll" "pathfinish ll = pathstart rr"
        unfolding ll_def rr_def by auto
    qed
    have "proots_count p {x. Im x>0} = (\<Sum>x\<in>proots p. winding_number lr x * of_nat (order x p))"
    unfolding proots_count_def of_nat_sum
    proof (rule sum.mono_neutral_cong_left)
      show "finite (proots p)" "proots_within p {x. 0 < Im x} \<subseteq> proots p"
        using \<open>p\<noteq>0\<close> by auto
    next
      have "winding_number lr x=0" when "x\<in>proots p - proots_within p {x. 0 < Im x}" for x
      unfolding lr_def ll_def rr_def
      proof (eval_winding,simp_all)
        show *:"x \<notin> closed_segment (- complex_of_real r) (complex_of_real r)"
          using img_ll that unfolding ll_def by auto
        show "x \<notin> path_image (part_circlepath 0 r 0 pi)"
          using img_rr that unfolding rr_def by auto
        have xr_facts:"0 > Im x" "-r<Re x" "Re x<r" "cmod x<r"
        proof -
          have "Im x\<le>0" using that by auto
          moreover have "Im x\<noteq>0" using no_real_roots that by blast
          ultimately show "0 > Im x" by auto
        next
          show "cmod x<r" using that r_ball by auto
          then have "\<bar>Re x\<bar> < r"
            using abs_Re_le_cmod[of x] by argo  
          then show "-r<Re x" "Re x<r"  by linarith+
        qed
        then have "cindex_pathE ll x = 1"
          using \<open>r>0\<close> unfolding cindex_pathE_linepath[OF *] ll_def 
          by (auto simp add: mult_pos_neg)
        moreover have "cindex_pathE rr x=-1"
          unfolding rr_def using r_ball that
          by (auto intro!: cindex_pathE_circlepath_upper)
        ultimately show "-cindex_pathE (linepath (- of_real r) (of_real r)) x =
            cindex_pathE (part_circlepath 0 r 0 pi) x"
          unfolding ll_def rr_def by auto
      qed
      then show "\<forall>i\<in>proots p - proots_within p {x. 0 < Im x}. 
          winding_number lr i * of_nat (order i p) = 0"
        by auto
    next
      fix x assume x_asm:"x \<in> proots_within p {x. 0 < Im x}"
      have "winding_number lr x=1" unfolding lr_def ll_def rr_def
      proof (eval_winding,simp_all) 
        show *:"x \<notin> closed_segment (- complex_of_real r) (complex_of_real r)"
          using img_ll x_asm unfolding ll_def by auto
        show "x \<notin> path_image (part_circlepath 0 r 0 pi)"
          using img_rr x_asm unfolding rr_def by auto
        have xr_facts:"0 < Im x" "-r<Re x" "Re x<r" "cmod x<r"
        proof -
          show "0 < Im x" using x_asm by auto
        next
          show "cmod x<r" using x_asm r_ball by auto
          then have "\<bar>Re x\<bar> < r"
            using abs_Re_le_cmod[of x] by argo  
          then show "-r<Re x" "Re x<r"  by linarith+
        qed
        then have "cindex_pathE ll x = -1"
          using \<open>r>0\<close> unfolding cindex_pathE_linepath[OF *] ll_def 
          by (auto simp add: mult_less_0_iff)
        moreover have "cindex_pathE rr x=-1"
          unfolding rr_def using r_ball x_asm
          by (auto intro!: cindex_pathE_circlepath_upper)
        ultimately show "- of_real (cindex_pathE (linepath (- of_real r) (of_real r)) x) -
            of_real (cindex_pathE (part_circlepath 0 r 0 pi) x) = 2"  
          unfolding ll_def rr_def by auto 
      qed
      then show "of_nat (order x p) = winding_number lr x * of_nat (order x p)" by auto
    qed
    also have "... = 1/(2*pi*\<i>) * contour_integral lr (\<lambda>x. deriv (poly p) x / poly p x)"
      apply (subst argument_principle_poly[of p lr])
      using \<open>p\<noteq>0\<close> img_ll img_rr unfolding lr_def ll_def rr_def
      by (auto simp add:path_image_join)
    also have "... = winding_number (poly p \<circ> lr) 0"  
      apply (subst winding_number_comp[of UNIV "poly p" lr 0])
      using \<open>p\<noteq>0\<close> img_ll img_rr unfolding lr_def ll_def rr_def
      by (auto simp add:path_image_join path_image_compose)
    also have "... = Re (winding_number (poly p \<circ> lr) 0)" 
    proof -
      have "winding_number (poly p \<circ> lr) 0 \<in> Ints" 
        apply (rule integer_winding_number)
        using \<open>p\<noteq>0\<close> img_ll img_rr unfolding lr_def 
        by (auto simp add:path_image_join path_image_compose path_compose_join 
            pathstart_compose pathfinish_compose valid_path_imp_path)
      then show ?thesis by (simp add: complex_eqI complex_is_Int_iff)
    qed
    also have "... =  Re (winding_number (poly p \<circ> ll) 0) + Re (winding_number (poly p \<circ> rr) 0)"
      unfolding lr_def path_compose_join using img_ll img_rr
      apply (subst winding_number_join)
      by (auto simp add:valid_path_imp_path path_image_compose pathstart_compose pathfinish_compose)
    also have "... = w1 r  +w2 r"
      unfolding w1_def w2_def ll_def rr_def of_real_linepath by auto
    finally have "of_nat (proots_count p {x. 0 < Im x}) = complex_of_real (w1 r + w2 r)" .
    then have "proots_count p {x. 0 < Im x} = w1 r + w2 r" 
      using of_real_eq_iff by fastforce
    moreover have "cp r = ci r"
    proof -
      define f where "f=(\<lambda>x. Im (poly p (of_real x)) / Re (poly p x))"
      have "cp r = cindex_pathE (poly p \<circ> (\<lambda>x. 2*r*x - r)) 0"
        unfolding cp_def linepath_def by (auto simp add:algebra_simps)
      also have "... = cindexE 0 1 (f o (\<lambda>x. 2*r*x - r))"
        unfolding cp_def ci_def cindex_pathE_def f_def comp_def by auto
      also have "... = cindexE (-r) r f"
        apply (subst cindexE_linear_comp[of "2*r" 0 1 f "-r",simplified])
        using \<open>r>0\<close> by auto
      also have "... = ci r"
        unfolding ci_def f_def Im_poly_of_real Re_poly_of_real by simp
      finally show ?thesis .
    qed
    ultimately show "w1 r + w2 r + cp r / 2 - ci r / 2 = real (proots_count p {x. 0 < Im x})"
      by auto
  qed
  ultimately have "((\<lambda>r::real. real (proots_count p {x. 0 < Im x})) 
      \<longlongrightarrow> real (degree p) / 2 - of_int cubd / 2) at_top"
    by (auto dest: tendsto_cong)
  then show ?thesis
    apply (subst (asm) tendsto_const_iff)
    unfolding cubd_def proots_upper_def by auto
qed

lemma cindexE_roots_on_horizontal_border:
  fixes a::complex and s::real
  defines "g\<equiv>linepath a (a + of_real s)"
  assumes pqr:"p = q * r" and r_monic:"lead_coeff r=1" and r_proots:"\<forall>x\<in>proots r. Im x=Im a"
  shows "cindexE lb ub (\<lambda>t. Im ((poly p \<circ> g) t) / Re ((poly p \<circ> g) t)) =
          cindexE lb ub (\<lambda>t. Im ((poly q \<circ> g) t) / Re ((poly q \<circ> g) t))"
  using assms
proof (induct r arbitrary:p rule:poly_root_induct_alt)
  case 0
  then have False 
    by (metis Im_complex_of_real UNIV_I imaginary_unit.simps(2) proots_within_0 zero_neq_one)
  then show ?case by simp
next
  case (no_proots r)
  then obtain b where "b\<noteq>0" "r=[:b:]" 
    using fundamental_theorem_of_algebra_alt by blast 
  then have "r=1" using \<open>lead_coeff r = 1\<close> by simp 
  with \<open>p = q * r\<close> show ?case by simp
next
  case (root b r)
  then have ?case when "s=0" 
    using that(1) unfolding cindex_pathE_def by (simp add:cindexE_constI)
  moreover have ?case when "s\<noteq>0"
  proof -
    define qrg where "qrg = poly (q*r) \<circ> g"
    have "cindexE lb ub (\<lambda>t. Im ((poly p \<circ> g) t) / Re ((poly p \<circ> g) t))
          = cindexE lb ub (\<lambda>t. Im (qrg t * (g t - b)) / Re (qrg t * (g t - b)))"
      unfolding qrg_def \<open>p = q * ([:- b, 1:] * r)\<close> comp_def
      by (simp add:algebra_simps)
    also have "... = cindexE lb ub
        (\<lambda>t. ((Re a + t * s - Re b )* Im (qrg t)) /
           ((Re a + t * s - Re b )* Re (qrg t)))" 
    proof -
      have "Im b = Im a" 
        using \<open>\<forall>x\<in>proots ([:- b, 1:] * r). Im x = Im a\<close> by auto
      then show ?thesis 
        unfolding cindex_pathE_def g_def linepath_def
        by (simp add:algebra_simps)
    qed
    also have "... = cindexE lb ub (\<lambda>t. Im (qrg t) / Re (qrg t))"
    proof (rule cindexE_cong[of "{t. Re a + t * s - Re b = 0}"])
      show "finite {t. Re a + t * s - Re b = 0}"
      proof (cases "Re a= Re b")
        case True
        then have "{t. Re a + t * s - Re b = 0} = {0}"
          using \<open>s\<noteq>0\<close> by auto
        then show ?thesis by auto
      next
        case False
        then have "{t. Re a + t * s - Re b = 0} = {(Re b - Re a) / s}"
          using \<open>s\<noteq>0\<close> by (auto simp add:field_simps)
        then show ?thesis by auto
      qed
    next
      fix x assume asm:"x \<notin> {t. Re a + t * s - Re b = 0}" 
      define tt where "tt=Re a + x * s - Re b"
      have "tt\<noteq>0" using asm unfolding tt_def by auto 
      then show "tt * Im (qrg x) / (tt * Re (qrg x)) = Im (qrg x) / Re (qrg x)"
        by auto
    qed 
    also have "... = cindexE lb ub (\<lambda>t. Im ((poly q \<circ> g) t) / Re ((poly q \<circ> g) t))"
      unfolding qrg_def
    proof (rule root(1))
      show "lead_coeff r = 1" 
        by (metis lead_coeff_mult lead_coeff_pCons(1) mult_cancel_left2 one_poly_eq_simps(2) 
          root.prems(2) zero_neq_one)
    qed (use root in simp_all)
    finally show ?thesis .
  qed
  ultimately show ?case by auto
qed



lemma poly_decompose_by_proots:
  fixes p ::"'a::idom poly"
  assumes "p\<noteq>0"
  shows "\<exists>q r. p = q * r \<and> lead_coeff q=1 \<and> (\<forall>x\<in>proots q. P x) \<and> (\<forall>x\<in>proots r. \<not>P x)" using assms
proof (induct p rule:poly_root_induct_alt)
  case 0
  then show ?case by simp
next
  case (no_proots p)
  then show ?case 
    apply (rule_tac x=1 in exI)
    apply (rule_tac x=p in exI)
    by (simp add:proots_def)
next
  case (root a p)
  then obtain q r where pqr:"p = q * r" and leadq:"lead_coeff q=1" 
                    and qball:"\<forall>a\<in>proots q. P a" and rball:"\<forall>x\<in>proots r. \<not> P x" 
    using mult_zero_right by metis
  have ?case when "P a"
    apply (rule_tac x="[:- a, 1:] * q" in exI)
    apply (rule_tac x=r in exI)
    using pqr qball rball that leadq unfolding lead_coeff_mult 
    by (auto simp add:algebra_simps)
  moreover have ?case when "\<not> P a"
    apply (rule_tac x="q" in exI)
    apply (rule_tac x="[:- a, 1:] *r" in exI)
    using pqr qball rball that leadq unfolding lead_coeff_mult 
    by (auto simp add:algebra_simps)
  ultimately show ?case by blast
qed

lemma proots_upper_cindex_eq':
  assumes "lead_coeff p=1"
  shows "proots_upper p = (degree p - proots_count p {x. Im x=0} 
              - cindex_poly_ubd (map_poly Im p) (map_poly Re p)) /2"
proof -
  have "p\<noteq>0" using assms by auto
  from poly_decompose_by_proots[OF this,of "\<lambda>x. Im x\<noteq>0"] 
  obtain q r where pqr:"p = q * r" and leadq:"lead_coeff q=1"
              and qball: "\<forall>x\<in>proots q. Im x \<noteq>0" and rball:"\<forall>x\<in>proots r. Im x =0"
    by auto
  have "real_of_int (proots_upper p) = proots_upper q + proots_upper r"
    using \<open>p\<noteq>0\<close> unfolding proots_upper_def pqr by (auto simp add:proots_count_times)
  also have "... = proots_upper q"
  proof -
    have "proots_within r {z. 0 < Im z} = {}"
      using rball by auto
    then have "proots_upper r =0 " 
      unfolding proots_upper_def proots_count_def by simp
    then show ?thesis by auto
  qed
  also have "... =  (degree q - cindex_poly_ubd (map_poly Im q) (map_poly Re q)) / 2"
    by (rule proots_upper_cindex_eq[OF leadq qball])
  also have "... = (degree p - proots_count p {x. Im x=0} 
                      - cindex_poly_ubd (map_poly Im p) (map_poly Re p)) /2"
  proof -
    have "degree q = degree p - proots_count p {x. Im x=0}"
    proof -
      have "degree p= degree q + degree r"
        unfolding pqr
        apply (rule degree_mult_eq)
        using \<open>p \<noteq> 0\<close> pqr by auto
      moreover have "degree r = proots_count p {x. Im x=0}"
        unfolding degree_proots_count proots_count_def
      proof (rule sum.cong)
        fix x assume "x \<in> proots_within p {x. Im x = 0}" 
        then have "Im x=0" by auto
        then have "order x q = 0"
          using qball order_0I by blast
        then show "order x r = order x p" 
          using \<open>p\<noteq>0\<close> unfolding pqr by (simp add: order_mult)
      next 
        show "proots r = proots_within p {x. Im x = 0}"
          unfolding pqr proots_within_times using qball rball by auto
      qed
      ultimately show ?thesis by auto
    qed
    moreover have "cindex_poly_ubd (map_poly Im q) (map_poly Re q) 
            = cindex_poly_ubd (map_poly Im p) (map_poly Re p)"
    proof -
      define iq rq ip rp where "iq = map_poly Im q" and "rq=map_poly Re q" 
                           and "ip=map_poly Im p" and "rp = map_poly Re p"
      have "cindexE (- x) x (\<lambda>x. poly iq x / poly rq x) 
              = cindexE (- x) x (\<lambda>x. poly ip x / poly rp x)" for x
      proof -
        have "lead_coeff r = 1" 
          using pqr leadq \<open>lead_coeff p=1\<close> by (simp add: coeff_degree_mult)
        then have "cindexE (- x) x (\<lambda>t. Im (poly p (t *\<^sub>R 1)) / Re (poly p (t *\<^sub>R 1))) =
                      cindexE (- x) x (\<lambda>t. Im (poly q (t *\<^sub>R 1)) / Re (poly q (t *\<^sub>R 1)))"
          using cindexE_roots_on_horizontal_border[OF pqr,of 0 "-x" x 1
              ,unfolded linepath_def comp_def,simplified] rball by simp
        then show ?thesis
          unfolding scaleR_conv_of_real iq_def ip_def rq_def rp_def 
          by (simp add:Im_poly_of_real Re_poly_of_real)
      qed
      then have "\<forall>\<^sub>F r::real in at_top.
        real_of_int (cindex_poly_ubd iq rq) = cindex_poly_ubd ip rp"
        using eventually_conj[OF cindex_poly_ubd_eventually[of iq rq] 
                cindex_poly_ubd_eventually[of ip rp]]
        by (elim eventually_mono,auto)
      then show ?thesis
        apply (fold iq_def rq_def ip_def rp_def)
        by simp
    qed
    ultimately show ?thesis by auto
  qed
  finally show ?thesis by simp
qed

(*If we know that the polynomial p is squarefree, we can cope with the case when there're 
  roots on the border.*)
lemma proots_within_upper_squarefree:
  assumes "rsquarefree p"
  shows  "card (proots_within p {x. Im x >0}) = (let 
            pp = smult (inverse (lead_coeff p)) p;
            pI = map_poly Im pp;
            pR = map_poly Re pp;
            g = gcd pR pI
        in
            nat ((degree p - changes_R_smods g (pderiv g) - changes_R_smods pR pI) div 2)  
      )"
proof -
  define pp where "pp = smult (inverse (lead_coeff p)) p"
  define pI where "pI = map_poly Im pp"
  define pR where "pR = map_poly Re pp"
  define g where  "g = gcd pR pI"
  have "card (proots_within p {x. Im x >0}) = proots_upper p"
    unfolding proots_upper_def using card_proots_within_rsquarefree[OF assms] by auto
  also have "... = proots_upper pp"
    unfolding proots_upper_def pp_def
    apply (subst proots_count_smult)
    using assms by auto
  also have "... = (degree pp - proots_count pp {x. Im x = 0} - cindex_poly_ubd pI pR) div 2"
  proof -
    define rr where "rr = proots_count pp {x. Im x = 0}"
    define cpp where "cpp = cindex_poly_ubd pI pR"
    have *:"proots_upper pp = (degree pp - rr - cpp) / 2"
      apply (rule proots_upper_cindex_eq'[of pp,folded rr_def cpp_def pR_def pI_def])
      unfolding pp_def using assms by auto
    also have "... = (degree pp - rr - cpp) div 2"
    proof (subst real_of_int_div)
      define tt where "tt=int (degree pp - rr) - cpp"
      have "real_of_int tt=2*proots_upper pp"
        by (simp add:*[folded tt_def])
      then show "even tt" by (metis dvd_triv_left even_of_nat of_int_eq_iff of_int_of_nat_eq)
    qed simp
    finally show ?thesis unfolding rr_def cpp_def by simp
  qed
  also have "... = (degree pp - changes_R_smods g (pderiv g) 
                        - cindex_poly_ubd pI pR) div 2"
  proof -
    have "rsquarefree pp" 
      using assms rsquarefree_smult_iff unfolding pp_def 
      by (metis inverse_eq_imp_eq inverse_zero leading_coeff_neq_0 rsquarefree_0)
    from card_proots_within_rsquarefree[OF this] 
    have "proots_count pp {x. Im x = 0} = card (proots_within pp {x. Im x = 0})"
      by simp
    also have "... = card (proots_within pp (unbounded_line 0 1))"
    proof -
      have "{x. Im x = 0} = unbounded_line 0 1"
        unfolding unbounded_line_def 
        apply auto
        subgoal for x
          apply (rule_tac x="Re x" in exI)
          by (metis complex_is_Real_iff of_real_Re of_real_def)
        done
      then show ?thesis by simp
    qed
    also have "... = changes_R_smods g (pderiv g)"
      unfolding card_proots_unbounded_line[of 0 1 pp,simplified,folded pI_def pR_def] g_def
      by (auto simp add:Let_def sturm_R[symmetric])
    finally have "proots_count pp {x. Im x = 0} = changes_R_smods g (pderiv g)" .
    moreover have "degree pp \<ge> proots_count pp {x. Im x = 0}" 
      by (metis \<open>rsquarefree pp\<close> proots_count_leq_degree rsquarefree_0)
    ultimately show ?thesis 
      by auto
  qed
  also have "... = (degree p - changes_R_smods g (pderiv g) 
                        - changes_R_smods pR pI) div 2"
    using cindex_poly_ubd_code unfolding pp_def by simp
  finally have "card (proots_within p {x. 0 < Im x}) = (degree p - changes_R_smods g (pderiv g) -
                  changes_R_smods pR pI) div 2" .
  then show ?thesis unfolding Let_def
    apply (fold pp_def pR_def pI_def g_def)
    by (simp add: pp_def)
qed
    
lemma proots_upper_code1[code]:
  "proots_upper p = 
    (if p \<noteq> 0 then
       (let pp=smult (inverse (lead_coeff p)) p;
            pI=map_poly Im pp;
            pR=map_poly Re pp;
            g = gcd pI pR
        in
            nat ((degree p - nat (changes_R_smods_ext g (pderiv g)) - changes_R_smods pR pI) div 2) 
        )
    else 
      Code.abort (STR ''proots_upper fails when p=0.'') (\<lambda>_. proots_upper p))"
proof -
  define pp where "pp = smult (inverse (lead_coeff p)) p"
  define pI where "pI = map_poly Im pp"
  define pR where "pR=map_poly Re pp"
  define g where  "g = gcd pI pR"
  have ?thesis when "p=0"
    using that by auto
  moreover have ?thesis when "p\<noteq>0" 
  proof -
    have "pp\<noteq>0" unfolding pp_def using that by auto
    define rr where "rr=int (degree pp - proots_count pp {x. Im x = 0}) - cindex_poly_ubd pI pR"
    have "lead_coeff p\<noteq>0" using \<open>p\<noteq>0\<close> by simp
    then have "proots_upper pp = rr / 2" unfolding rr_def
      apply (rule_tac proots_upper_cindex_eq'[of pp, folded pI_def pR_def])
      unfolding pp_def lead_coeff_smult by auto
    then have "proots_upper pp = nat (rr div 2)" by linarith
    moreover have
      "rr = degree p - nat (changes_R_smods_ext g (pderiv g)) - changes_R_smods pR pI"
    proof -
      have "degree pp = degree p" unfolding pp_def by auto
      moreover have "proots_count pp {x. Im x = 0} = nat (changes_R_smods_ext g (pderiv g))"
      proof -
        have "{x. Im x = 0} = unbounded_line 0 1"
          unfolding unbounded_line_def by (simp add: complex_eq_iff)
        then show ?thesis 
          using proots_unbounded_line[of 0 1 pp,simplified, folded pI_def pR_def] \<open>pp\<noteq>0\<close>
          by (auto simp:Let_def g_def gcd.commute)
      qed
      moreover have "cindex_poly_ubd pI pR = changes_R_smods pR pI"
        using cindex_poly_ubd_code by auto
      ultimately show ?thesis unfolding rr_def by auto
    qed
    moreover have "proots_upper pp = proots_upper p"
      unfolding pp_def proots_upper_def 
      apply (subst proots_count_smult)
      using that by auto
    ultimately show ?thesis 
      unfolding Let_def using that
      apply (fold pp_def pI_def pR_def g_def)
      by argo
  qed
  ultimately show ?thesis by blast
qed

lemma proots_upper_card_code[code]:
  "proots_upper_card p = (if p=0 then 0 else
      (let
            pf = p div (gcd p (pderiv p));
            pp = smult (inverse (lead_coeff pf)) pf;
            pI = map_poly Im pp;
            pR = map_poly Re pp;
            g = gcd pR pI
        in
            nat ((degree pf - changes_R_smods g (pderiv g) - changes_R_smods pR pI) div 2)  
      ))"
proof (cases "p=0")
  case True
  then show ?thesis unfolding proots_upper_card_def using infinite_halfspace_Im_gt by auto
next
  case False
  define pf pp pI pR g where 
        "pf = p div (gcd p (pderiv p))"
    and "pp = smult (inverse (lead_coeff pf)) pf"
    and "pI = map_poly Im pp"
    and "pR = map_poly Re pp"
    and "g = gcd pR pI"
  have "proots_upper_card p = proots_upper_card pf"
  proof -
    have "proots_within p {x. 0 < Im x} = proots_within pf {x. 0 < Im x}"
      unfolding proots_within_def using poly_gcd_pderiv_iff[of p,folded pf_def]
      by auto
    then show ?thesis unfolding proots_upper_card_def by auto
  qed
  also have "... = nat ((degree pf - changes_R_smods g (pderiv g) - changes_R_smods pR pI) div 2)"
    using proots_within_upper_squarefree[OF rsquarefree_gcd_pderiv[OF \<open>p\<noteq>0\<close>]
        ,unfolded Let_def,folded pf_def,folded pp_def pI_def pR_def g_def]
    unfolding proots_upper_card_def by blast
  finally show ?thesis unfolding Let_def
    apply (fold pf_def,fold pp_def pI_def pR_def g_def)
    using False by auto
qed

subsection \<open>Polynomial roots on a general half-plane\<close>

text \<open>the number of roots of polynomial @{term p}, counted with multiplicity,
   on the left half plane of the vector @{term "b-a"}.\<close>
definition proots_half ::"complex poly \<Rightarrow> complex \<Rightarrow> complex \<Rightarrow> nat" where
  "proots_half p a b = proots_count p {w. Im ((w-a) / (b-a)) > 0}"    
  
lemma proots_half_empty:
  assumes "a=b"
  shows "proots_half p a b = 0"  
unfolding proots_half_def using assms by auto  

(*TODO: the proof can potentially simplified with some conformal properties.*)
lemma proots_half_proots_upper:
  assumes "a\<noteq>b" "p\<noteq>0"
  shows "proots_half p a b= proots_upper (pcompose p [:a, (b-a):])"
proof -
  define q where "q=[:a, (b - a):]"
  define f where "f=(\<lambda>x. (b-a)*x+ a)"
  have "(\<Sum>r\<in>proots_within p {w. Im ((w-a) / (b-a)) > 0}. order r p) 
      = (\<Sum>r\<in>proots_within (p \<circ>\<^sub>p q) {z. 0 < Im z}. order r (p \<circ>\<^sub>pq))"
  proof (rule sum.reindex_cong[of f])
    have "inj f"
      using assms unfolding f_def inj_on_def by fastforce
    then show "inj_on f (proots_within (p \<circ>\<^sub>p q) {z. 0 < Im z})"
      by (elim inj_on_subset,auto)
  next
    show "proots_within p {w. Im ((w-a) / (b-a)) > 0} = f ` proots_within (p \<circ>\<^sub>p q) {z. 0 < Im z}"
    proof safe
      fix x assume x_asm:"x \<in> proots_within p {w. Im ((w-a) / (b-a)) > 0}"
      define xx where "xx=(x -a) / (b - a)"
      have "poly (p \<circ>\<^sub>p q) xx = 0"  
        unfolding q_def xx_def poly_pcompose using assms x_asm by auto
      moreover have "Im xx > 0" 
        unfolding xx_def using x_asm by auto
      ultimately have "xx \<in> proots_within (p \<circ>\<^sub>p q) {z. 0 < Im z}" by auto
      then show "x \<in> f ` proots_within (p \<circ>\<^sub>p q) {z. 0 < Im z}" 
        apply (intro rev_image_eqI[of xx])
        unfolding f_def xx_def using assms by auto
    next
      fix x assume "x \<in> proots_within (p \<circ>\<^sub>p q) {z. 0 < Im z}"
      then show "f x \<in> proots_within p {w. 0 < Im ((w-a) / (b - a))}" 
        unfolding f_def q_def using assms 
        apply (auto simp add:poly_pcompose)
        by (auto simp add:algebra_simps)
    qed
  next
    fix x assume "x \<in> proots_within (p \<circ>\<^sub>p q) {z. 0 < Im z}"
    show "order (f x) p = order x (p \<circ>\<^sub>p q)" using \<open>p\<noteq>0\<close>
    proof (induct p rule:poly_root_induct_alt)
      case 0
      then show ?case by simp
    next
      case (no_proots p)
      have "order (f x) p = 0"
        apply (rule order_0I)        
        using no_proots by auto
      moreover have "order x (p \<circ>\<^sub>p q) = 0"
        apply (rule order_0I)
        unfolding poly_pcompose q_def using no_proots by auto
      ultimately show ?case by auto
    next
      case (root c p)
      have "order (f x) ([:- c, 1:] * p) = order (f x) [:-c,1:] + order (f x) p" 
        apply (subst order_mult)
        using root by auto
      also have "... =  order x ([:- c, 1:] \<circ>\<^sub>p q) +  order x (p \<circ>\<^sub>p q)" 
      proof -
        have "order (f x) [:- c, 1:] = order x ([:- c, 1:] \<circ>\<^sub>p q)" 
        proof (cases "f x=c")
          case True
          have "[:- c, 1:] \<circ>\<^sub>p q = smult (b-a) [:-x,1:]"
            using True unfolding q_def f_def pcompose_pCons by auto
          then have "order x ([:- c, 1:] \<circ>\<^sub>p q) = order x (smult (b-a) [:-x,1:])"
            by auto
          then have "order x ([:- c, 1:] \<circ>\<^sub>p q) = 1"
            apply (subst (asm) order_smult)
            using assms order_power_n_n[of _ 1,simplified] by auto   
          moreover have "order (f x) [:- c, 1:] = 1"
            using True order_power_n_n[of _ 1,simplified] by auto
          ultimately show ?thesis by auto
        next
          case False
          have "order (f x) [:- c, 1:] = 0"
            apply (rule order_0I)
            using False unfolding f_def by auto
          moreover have "order x ([:- c, 1:] \<circ>\<^sub>p q) = 0"
            apply (rule order_0I)
            using False unfolding f_def q_def poly_pcompose by auto
          ultimately show ?thesis by auto
        qed
        moreover have "order (f x) p = order x (p \<circ>\<^sub>p q)"
          apply (rule root)
          using root by auto 
        ultimately show ?thesis by auto
      qed
      also have "... = order x (([:- c, 1:] * p) \<circ>\<^sub>p q)" 
        unfolding pcompose_mult
        apply (subst order_mult)
        subgoal 
          unfolding q_def using assms(1) pcompose_eq_0 root.prems 
          by (metis One_nat_def degree_pCons_eq_if mult_eq_0_iff
              one_neq_zero pCons_eq_0_iff right_minus_eq) 
        by simp
      finally show ?case .
    qed
  qed
  then show ?thesis unfolding proots_half_def proots_upper_def proots_count_def q_def
    by auto
qed    
     
lemma proots_half_code1[code]:
  "proots_half p a b = (if a\<noteq>b then 
                        if p\<noteq>0 then proots_upper (p \<circ>\<^sub>p [:a, b - a:]) 
                        else Code.abort (STR ''proots_half fails when p=0.'') 
                          (\<lambda>_. proots_half p a b) 
                        else 0)"
proof -
  have ?thesis when "a=b"
    using proots_half_empty that by auto
  moreover have ?thesis when "a\<noteq>b" "p=0"
    using that by auto
  moreover have ?thesis when "a\<noteq>b" "p\<noteq>0"
    using proots_half_proots_upper[OF that] that by auto
  ultimately show ?thesis by auto
qed

end