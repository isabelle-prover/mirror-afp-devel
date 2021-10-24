theory Count_Rectangle imports Count_Line
begin


subsection \<open>Counting roots in a rectangle\<close>  
  
definition proots_rectangle ::"complex poly \<Rightarrow> complex \<Rightarrow> complex \<Rightarrow> nat" where
  "proots_rectangle p lb ub = proots_count p (box lb ub)"    
   
lemma complex_box_ne_empty: 
  fixes a b::complex
  shows 
    "cbox a b \<noteq> {} \<longleftrightarrow> (Re a \<le> Re b \<and> Im a \<le> Im b)"
    "box a b \<noteq> {} \<longleftrightarrow> (Re a < Re b \<and> Im a < Im b)"
  by (auto simp add:box_ne_empty Basis_complex_def)  
      
lemma proots_rectangle_code1:
  "proots_rectangle p lb ub = (if Re lb < Re ub \<and> Im lb < Im ub then 
            if p\<noteq>0 then 
            if no_proots_line p lb (Complex (Re ub) (Im lb))
            \<and> no_proots_line p (Complex (Re ub) (Im lb)) ub
            \<and> no_proots_line p ub (Complex (Re lb) (Im ub))
            \<and> no_proots_line p (Complex (Re lb) (Im ub)) lb then  
            (
            let p1 = pcompose p [:lb,  Complex (Re ub - Re lb) 0:];
                pR1 = map_poly Re p1; pI1 = map_poly Im p1; gc1 = gcd pR1 pI1;
                p2 = pcompose p [:Complex (Re ub) (Im lb), Complex 0 (Im ub - Im lb):];
                pR2 = map_poly Re p2; pI2 = map_poly Im p2; gc2 = gcd pR2 pI2;
                p3 = pcompose p [:ub, Complex (Re lb - Re ub) 0:];
                pR3 = map_poly Re p3; pI3 = map_poly Im p3; gc3 = gcd pR3 pI3;
                p4 = pcompose p [:Complex (Re lb) (Im ub), Complex 0 (Im lb - Im ub):];
                pR4 = map_poly Re p4; pI4 = map_poly Im p4; gc4 = gcd pR4 pI4
            in 
              nat (- (changes_alt_itv_smods 0 1 (pR1 div gc1) (pI1 div gc1)
                + changes_alt_itv_smods 0 1 (pR2 div gc2) (pI2 div gc2)
                + changes_alt_itv_smods 0 1 (pR3 div gc3) (pI3 div gc3)
                + changes_alt_itv_smods 0 1 (pR4 div gc4) (pI4 div gc4))  div 4)
            )
            else Code.abort (STR ''proots_rectangle fails when there is a root on the border.'') 
            (\<lambda>_. proots_rectangle p lb ub)
            else Code.abort (STR ''proots_rectangle fails when p=0.'') 
            (\<lambda>_. proots_rectangle p lb ub)
            else 0)"
proof -
  have ?thesis when "\<not> (Re lb < Re ub \<and> Im lb < Im ub)" 
  proof -
    have "box lb ub = {}" using complex_box_ne_empty[of lb ub] that by auto
    then have "proots_rectangle p lb ub = 0" unfolding proots_rectangle_def by auto
    then show ?thesis by (simp add:that) 
  qed
  moreover have ?thesis when "Re lb < Re ub \<and> Im lb < Im ub" "p=0"
    using that by simp
  moreover have ?thesis when     
            "Re lb < Re ub" "Im lb < Im ub" "p\<noteq>0" 
            and no_proots:
            "no_proots_line p lb (Complex (Re ub) (Im lb))"
            "no_proots_line p (Complex (Re ub) (Im lb)) ub"
            "no_proots_line p ub (Complex (Re lb) (Im ub))"
            "no_proots_line p (Complex (Re lb) (Im ub)) lb"
  proof -
    define l1 where "l1 = linepath lb (Complex (Re ub) (Im lb))"
    define l2 where "l2 = linepath (Complex (Re ub) (Im lb)) ub"
    define l3 where "l3 = linepath ub (Complex (Re lb) (Im ub))"
    define l4 where "l4 = linepath (Complex (Re lb) (Im ub)) lb"
    define rec where "rec = l1 +++ l2 +++ l3 +++ l4"
    have valid[simp]:"valid_path rec" and loop[simp]:"pathfinish rec = pathstart rec"
      unfolding rec_def l1_def l2_def l3_def l4_def by auto
    have path_no_proots:"path_image rec \<inter> proots p = {}" 
      unfolding rec_def l1_def l2_def l3_def l4_def
      apply (subst path_image_join,simp_all del:Complex_eq)+  
      using no_proots[unfolded no_proots_line_def] by (auto simp del:Complex_eq)
    
    define g1 where "g1 = poly p o l1" 
    define g2 where "g2 = poly p o l2" 
    define g3 where "g3 = poly p o l3" 
    define g4 where "g4 = poly p o l4"    
    have [simp]: "path g1" "path g2" "path g3" "path g4"
      "pathfinish g1 = pathstart g2" "pathfinish g2 = pathstart g3" "pathfinish g3 = pathstart g4"
      "pathfinish g4 = pathstart g1"
      unfolding g1_def g2_def g3_def g4_def l1_def l2_def l3_def l4_def
      by (auto intro!: path_continuous_image continuous_intros 
          simp add:pathfinish_compose pathstart_compose)
    have [simp]: "finite_ReZ_segments g1 0" "finite_ReZ_segments g2 0" 
         "finite_ReZ_segments g3 0" "finite_ReZ_segments g4 0"
      unfolding g1_def l1_def g2_def l2_def g3_def l3_def g4_def l4_def poly_linepath_comp 
      by (rule finite_ReZ_segments_poly_of_real)+
    define p1 pR1 pI1 gc1
           p2 pR2 pI2 gc2
           p3 pR3 pI3 gc3
           p4 pR4 pI4 gc4
      where "p1 = pcompose p [:lb,  Complex (Re ub - Re lb) 0:]"
             and "pR1 = map_poly Re p1" and "pI1 = map_poly Im p1" and "gc1 = gcd pR1 pI1"
             and "p2 = pcompose p [:Complex (Re ub) (Im lb), Complex 0 (Im ub - Im lb):]"
             and "pR2 = map_poly Re p2" and "pI2 = map_poly Im p2" and "gc2 = gcd pR2 pI2"
             and "p3 = pcompose p [:ub, Complex (Re lb - Re ub) 0:]"
             and "pR3 = map_poly Re p3" and "pI3 = map_poly Im p3" and "gc3 = gcd pR3 pI3"
             and "p4 = pcompose p [:Complex (Re lb) (Im ub), Complex 0 (Im lb - Im ub):]"
             and "pR4 = map_poly Re p4" and "pI4 = map_poly Im p4" and "gc4 = gcd pR4 pI4"
    have "gc1\<noteq>0" "gc2\<noteq>0" "gc3\<noteq>0" "gc4\<noteq>0"
    proof -
      show "gc1\<noteq>0" 
      proof (rule ccontr)
        assume "\<not> gc1 \<noteq> 0"
        then have "pI1 = 0" "pR1 = 0" unfolding gc1_def by auto
        then have "p1 = 0" unfolding pI1_def pR1_def 
          by (metis cpoly_of_decompose map_poly_0)
        then have "p=0" unfolding p1_def using \<open>Re lb < Re ub\<close>
          by (auto elim!:pcompose_eq_0 simp add:Complex_eq_0)
        then show False using \<open>p\<noteq>0\<close> by simp
      qed
      show "gc2\<noteq>0" 
      proof (rule ccontr)
        assume "\<not> gc2 \<noteq> 0"
        then have "pI2 = 0" "pR2 = 0" unfolding gc2_def by auto
        then have "p2 = 0" unfolding pI2_def pR2_def 
          by (metis cpoly_of_decompose map_poly_0)
        then have "p=0" unfolding p2_def using \<open>Im lb < Im ub\<close>
          by (auto elim!:pcompose_eq_0 simp add:Complex_eq_0)
        then show False using \<open>p\<noteq>0\<close> by simp
      qed 
      show "gc3\<noteq>0" 
      proof (rule ccontr)
        assume "\<not> gc3 \<noteq> 0"
        then have "pI3 = 0" "pR3 = 0" unfolding gc3_def by auto
        then have "p3 = 0" unfolding pI3_def pR3_def 
          by (metis cpoly_of_decompose map_poly_0)
        then have "p=0" unfolding p3_def using \<open>Re lb < Re ub\<close>
          by (auto elim!:pcompose_eq_0 simp add:Complex_eq_0)
        then show False using \<open>p\<noteq>0\<close> by simp
      qed
      show "gc4\<noteq>0" 
      proof (rule ccontr)
        assume "\<not> gc4 \<noteq> 0"
        then have "pI4 = 0" "pR4 = 0" unfolding gc4_def by auto
        then have "p4 = 0" unfolding pI4_def pR4_def 
          by (metis cpoly_of_decompose map_poly_0)
        then have "p=0" unfolding p4_def using \<open>Im lb < Im ub\<close>
          by (auto elim!:pcompose_eq_0 simp add:Complex_eq_0)
        then show False using \<open>p\<noteq>0\<close> by simp
      qed 
    qed
    define sms where 
      "sms = (changes_alt_itv_smods 0 1 (pR1 div gc1) (pI1 div gc1)
                + changes_alt_itv_smods 0 1 (pR2 div gc2) (pI2 div gc2)
                + changes_alt_itv_smods 0 1 (pR3 div gc3) (pI3 div gc3)
                + changes_alt_itv_smods 0 1 (pR4 div gc4) (pI4 div gc4))"
    have "proots_rectangle p lb ub = (\<Sum>r\<in>proots p. winding_number rec r * (order r p))" 
    proof -
      have "winding_number rec x * of_nat (order x p) = 0" 
        when "x\<in>proots p - proots_within p (box lb ub)" for x 
      proof -
        have *:"cbox lb ub = box lb ub \<union> path_image rec"
        proof -
          have "x\<in>cbox lb ub" when "x\<in>box lb ub \<union> path_image rec" for x
            using that \<open>Re lb<Re ub\<close> \<open>Im lb<Im ub\<close>
            unfolding box_def cbox_def Basis_complex_def rec_def l1_def l2_def l3_def l4_def
            apply (auto simp add:path_image_join closed_segment_degen_complex)          
                   apply (subst (asm) closed_segment_commute,simp add: closed_segment_degen_complex)+
            done  
          moreover have "x\<in>box lb ub \<union> path_image rec" when "x\<in>cbox lb ub" for x
            using that
            unfolding box_def cbox_def Basis_complex_def rec_def l1_def l2_def l3_def l4_def
            apply (auto simp add:path_image_join closed_segment_degen_complex)
             apply (subst (asm) (1 2) closed_segment_commute,simp add:closed_segment_degen_complex)+
            done
          ultimately show ?thesis by auto
        qed
        moreover have "x\<notin>path_image rec" 
          using path_no_proots that by auto
        ultimately have "x\<notin>cbox lb ub" using that by simp
        from winding_number_zero_outside[OF valid_path_imp_path[OF valid] _ loop this,simplified] * 
        have "winding_number rec x = 0" by auto
        then show ?thesis by auto
      qed
      moreover have "of_nat (order x p) = winding_number rec x * of_nat (order x p)" when 
        "x \<in> proots_within p (box lb ub)" for x 
      proof -
        have "x\<in>box lb ub" using that unfolding proots_within_def by auto 
        then have order_asms:"Re lb < Re x" "Re x < Re ub" "Im lb < Im x" "Im x < Im ub"  
          by (auto simp add:box_def Basis_complex_def)  
        have "winding_number rec x = 1"
          unfolding rec_def l1_def l2_def l3_def l4_def 
        proof eval_winding 
          let ?l1 = "linepath lb (Complex (Re ub) (Im lb))"
          and ?l2 = "linepath (Complex (Re ub) (Im lb)) ub"
          and ?l3 = "linepath ub (Complex (Re lb) (Im ub))"
          and ?l4 = "linepath (Complex (Re lb) (Im ub)) lb"
          show l1: "x \<notin> path_image ?l1" and l2: "x \<notin> path_image ?l2" and 
               l3: "x \<notin> path_image ?l3" and l4:"x \<notin> path_image ?l4"
            using no_proots that unfolding no_proots_line_def by auto
          show "- of_real (cindex_pathE ?l1 x + (cindex_pathE ?l2 x +
            (cindex_pathE ?l3 x + cindex_pathE ?l4 x))) = 2 * 1"
          proof -
            have "(Im x - Im ub) * (Re ub - Re lb) < 0" 
              using mult_less_0_iff order_asms(1) order_asms(2) order_asms(4) by fastforce
            then have "cindex_pathE ?l3 x = -1" 
              apply (subst cindex_pathE_linepath)
              using l3 by (auto simp add:algebra_simps order_asms)
            moreover have "(Im lb - Im x) * (Re ub - Re lb) <0" 
              using mult_less_0_iff order_asms(1) order_asms(2) order_asms(3) by fastforce
            then have "cindex_pathE ?l1 x = -1"    
              apply (subst cindex_pathE_linepath)
              using l1 by (auto simp add:algebra_simps order_asms)  
            moreover have "cindex_pathE ?l2 x = 0"    
              apply (subst cindex_pathE_linepath)
              using l2 order_asms by auto
            moreover have "cindex_pathE ?l4 x = 0"
              apply (subst cindex_pathE_linepath)
              using l4 order_asms by auto
            ultimately show ?thesis by auto
          qed
        qed
        then show ?thesis by auto
      qed 
      ultimately show ?thesis using \<open>p\<noteq>0\<close>
      unfolding proots_rectangle_def proots_count_def 
        by (auto intro!: sum.mono_neutral_cong_left[of "proots p" "proots_within p (box lb ub)"])
    qed    
    also have "... = 1/(2 * of_real pi * \<i>) *contour_integral rec (\<lambda>x. deriv (poly p) x / poly p x)"
    proof -
      have "contour_integral rec (\<lambda>x. deriv (poly p) x / poly p x) = 2 * of_real pi * \<i> 
              * (\<Sum>x | poly p x = 0. winding_number rec x * of_int (zorder (poly p) x))"
      proof (rule argument_principle[of UNIV "poly p" "{}" "\<lambda>_. 1" rec,simplified])
        show "connected (UNIV::complex set)" using connected_UNIV[where 'a=complex] .
        show "path_image rec \<subseteq> UNIV - {x. poly p x = 0}" 
          using path_no_proots unfolding proots_within_def by auto
        show "finite {x. poly p x = 0}" by (simp add: poly_roots_finite that(3))
      qed
      also have " ... = 2 * of_real pi * \<i> * (\<Sum>x\<in>proots p. winding_number rec x * (order x p))" 
        unfolding proots_within_def 
        apply (auto intro!:sum.cong simp add:order_zorder[OF \<open>p\<noteq>0\<close>] )
        by (metis nat_eq_iff2 of_nat_nat order_root order_zorder that(3))
      finally show ?thesis by auto
    qed  
    also have "... = winding_number (poly p \<circ> rec) 0"
    proof -
      have "0 \<notin> path_image (poly p \<circ> rec)" 
        using path_no_proots unfolding path_image_compose proots_within_def by fastforce
      from winding_number_comp[OF _ poly_holomorphic_on _ _ this,of UNIV,simplified]
      show ?thesis by auto
    qed
    also have winding_eq:"... = - cindex_pathE (poly p \<circ> rec) 0 / 2"
    proof (rule winding_number_cindex_pathE)
      show "finite_ReZ_segments (poly p \<circ> rec) 0"
        unfolding rec_def path_compose_join 
        apply (fold g1_def g2_def g3_def g4_def)
        by (auto intro!: finite_ReZ_segments_joinpaths path_join_imp)
      show "valid_path (poly p \<circ> rec)"
        by (rule valid_path_compose_holomorphic[where S=UNIV]) auto
      show "0 \<notin> path_image (poly p \<circ> rec)"
        using path_no_proots unfolding path_image_compose proots_def by fastforce
      show "pathfinish (poly p \<circ> rec) = pathstart (poly p \<circ> rec)"
        unfolding rec_def pathstart_compose pathfinish_compose  by (auto simp add:l1_def l4_def)   
    qed
    also have cindex_pathE_eq:"... = of_int (- sms) / of_int 4"
    proof -
      have "cindex_pathE (poly p \<circ> rec) 0 = cindex_pathE (g1+++g2+++g3+++g4) 0"
        unfolding rec_def path_compose_join g1_def g2_def g3_def g4_def by simp
      also have "... = cindex_pathE g1 0 + cindex_pathE g2 0 + cindex_pathE g3 0 + cindex_pathE g4 0"
        by (subst cindex_pathE_joinpaths,auto intro!:finite_ReZ_segments_joinpaths)+
      also have "... = cindex_polyE 0 1 (pI1 div gc1) (pR1 div gc1)
                     + cindex_polyE 0 1 (pI2 div gc2) (pR2 div gc2)
                     + cindex_polyE 0 1 (pI3 div gc3) (pR3 div gc3)
                     + cindex_polyE 0 1 (pI4 div gc4) (pR4 div gc4)"
      proof - 
        have "cindex_pathE g1 0 = cindex_polyE 0 1 (pI1 div gc1) (pR1 div gc1)"
        proof -
          have *:"g1 = poly p1 o of_real"
            unfolding g1_def p1_def l1_def poly_linepath_comp
            by (subst (5) complex_surj[symmetric],simp)
          then have "cindex_pathE g1 0  = cindexE 0 1 (\<lambda>t. poly pI1 t / poly pR1 t)"
            unfolding cindex_pathE_def pR1_def pI1_def 
            by (simp add:Im_poly_of_real Re_poly_of_real)
          also have "... = cindex_polyE 0 1 pI1 pR1"
            using cindexE_eq_cindex_polyE by auto
          also have "... = cindex_polyE 0 1 (pI1 div gc1) (pR1 div gc1)"
            using \<open>gc1\<noteq>0\<close>
            apply (subst (2) cindex_polyE_mult_cancel[of gc1,symmetric])
            by (simp_all add: gc1_def)  
          finally show ?thesis .
        qed
        moreover have "cindex_pathE g2 0 = cindex_polyE 0 1 (pI2 div gc2) (pR2 div gc2)"
        proof -
          have "g2 = poly p2 o of_real"
            unfolding g2_def p2_def l2_def poly_linepath_comp
            by (subst (5) complex_surj[symmetric],simp)
          then have "cindex_pathE g2 0  = cindexE 0 1 (\<lambda>t. poly pI2 t / poly pR2 t)"
            unfolding cindex_pathE_def pR2_def pI2_def 
            by (simp add:Im_poly_of_real Re_poly_of_real)
          also have "... = cindex_polyE 0 1 pI2 pR2"
            using cindexE_eq_cindex_polyE by auto
          also have "... = cindex_polyE 0 1 (pI2 div gc2) (pR2 div gc2)"
            using \<open>gc2\<noteq>0\<close>
            apply (subst (2) cindex_polyE_mult_cancel[of gc2,symmetric])
              by (simp_all add: gc2_def)
          finally show ?thesis .
        qed  
        moreover have "cindex_pathE g3 0 = cindex_polyE 0 1 (pI3 div gc3) (pR3 div gc3)"
        proof -
          have "g3 = poly p3 o of_real"
            unfolding g3_def p3_def l3_def poly_linepath_comp
            by (subst (5) complex_surj[symmetric],simp)
          then have "cindex_pathE g3 0  = cindexE 0 1 (\<lambda>t. poly pI3 t / poly pR3 t)"
            unfolding cindex_pathE_def pR3_def pI3_def 
            by (simp add:Im_poly_of_real Re_poly_of_real)
          also have "... = cindex_polyE 0 1 pI3 pR3"
            using cindexE_eq_cindex_polyE by auto
          also have "... = cindex_polyE 0 1 (pI3 div gc3) (pR3 div gc3)"
            using \<open>gc3\<noteq>0\<close>
            apply (subst (2) cindex_polyE_mult_cancel[of gc3,symmetric])
            by (simp_all add: gc3_def)
          finally show ?thesis .
        qed     
        moreover have "cindex_pathE g4 0 = cindex_polyE 0 1 (pI4 div gc4) (pR4 div gc4)"
        proof -
          have "g4 = poly p4 o of_real"
            unfolding g4_def p4_def l4_def poly_linepath_comp
            by (subst (5) complex_surj[symmetric],simp)
          then have "cindex_pathE g4 0  = cindexE 0 1 (\<lambda>t. poly pI4 t / poly pR4 t)"
            unfolding cindex_pathE_def pR4_def pI4_def 
            by (simp add:Im_poly_of_real Re_poly_of_real)
          also have "... = cindex_polyE 0 1 pI4 pR4"
            using cindexE_eq_cindex_polyE by auto
          also have "... = cindex_polyE 0 1 (pI4 div gc4) (pR4 div gc4)"
            using \<open>gc4\<noteq>0\<close>
            apply (subst (2) cindex_polyE_mult_cancel[of gc4,symmetric])
            by (simp_all add: gc4_def)
          finally show ?thesis .
        qed      
        ultimately show ?thesis by auto
      qed
      also have "... = sms / 2" 
      proof -
        have "cindex_polyE 0 1 (pI1 div gc1) (pR1 div gc1) 
            = changes_alt_itv_smods 0 1 (pR1 div gc1) (pI1 div gc1) / 2"
          apply (rule cindex_polyE_changes_alt_itv_mods)
          using \<open>gc1\<noteq>0\<close> unfolding gc1_def by (auto intro:div_gcd_coprime) 
        moreover have "cindex_polyE 0 1 (pI2 div gc2) (pR2 div gc2) 
            = changes_alt_itv_smods 0 1 (pR2 div gc2) (pI2 div gc2) / 2"
          apply (rule cindex_polyE_changes_alt_itv_mods)
          using \<open>gc2\<noteq>0\<close> unfolding gc2_def by (auto intro:div_gcd_coprime)    
        moreover have "cindex_polyE 0 1 (pI3 div gc3) (pR3 div gc3) 
            = changes_alt_itv_smods 0 1 (pR3 div gc3) (pI3 div gc3) / 2"
          apply (rule cindex_polyE_changes_alt_itv_mods)
          using \<open>gc3\<noteq>0\<close> unfolding gc3_def by (auto intro:div_gcd_coprime)    
        moreover have "cindex_polyE 0 1 (pI4 div gc4) (pR4 div gc4) 
            = changes_alt_itv_smods 0 1 (pR4 div gc4) (pI4 div gc4) / 2"
          apply (rule cindex_polyE_changes_alt_itv_mods)
          using \<open>gc4\<noteq>0\<close> unfolding gc4_def by (auto intro:div_gcd_coprime)
        ultimately show ?thesis unfolding sms_def by auto
      qed
      finally have *:"cindex_pathE (poly p \<circ> rec) 0 = real_of_int sms / 2" .
      show ?thesis 
        apply (subst *)
        by auto
    qed  
    finally have "(of_nat::_\<Rightarrow>complex) (proots_rectangle p lb ub) = of_int (- sms) / of_int 4" .
    moreover have "4 dvd sms" 
    proof -
      have "winding_number (poly p \<circ> rec) 0 \<in> \<int>"
      proof (rule integer_winding_number)
        show "path (poly p \<circ> rec)"
          by (auto intro!:valid_path_compose_holomorphic[where S=UNIV] valid_path_imp_path)
        show "pathfinish (poly p \<circ> rec) = pathstart (poly p \<circ> rec)"
          unfolding rec_def path_compose_join
          by (auto simp add:l1_def l4_def pathfinish_compose pathstart_compose)
        show "0 \<notin> path_image (poly p \<circ> rec)"
          using path_no_proots unfolding path_image_compose proots_def by fastforce
      qed         
      then have "of_int (- sms) / of_int 4 \<in> (\<int>::complex set)"
        by (simp only: winding_eq cindex_pathE_eq)
      then show ?thesis by (subst (asm) dvd_divide_Ints_iff[symmetric],auto) 
    qed
    ultimately have "proots_rectangle p lb ub = nat (- sms div 4)"
      apply (subst (asm) of_int_div_field[symmetric])
      by (simp,metis nat_int of_int_eq_iff of_int_of_nat_eq)
    then show ?thesis 
      unfolding Let_def
      apply (fold p1_def p2_def p3_def p4_def pI1_def pR1_def pI2_def pR2_def pI3_def pR3_def
          pI4_def pR4_def gc1_def gc2_def gc3_def gc4_def)
      apply (fold sms_def)
      using that by auto
  qed
  ultimately show ?thesis by fastforce
qed
  
(*further refinement*)
lemma proots_rectangle_code2[code]:
  "proots_rectangle p lb ub = (if Re lb < Re ub \<and> Im lb < Im ub then 
            if p\<noteq>0 then 
            if poly p lb \<noteq> 0 \<and> poly p (Complex (Re ub) (Im lb)) \<noteq>0 
               \<and> poly p ub \<noteq>0 \<and> poly p (Complex (Re lb) (Im ub)) \<noteq>0 
            then
              (let p1 = pcompose p [:lb,  Complex (Re ub - Re lb) 0:];
                pR1 = map_poly Re p1; pI1 = map_poly Im p1; gc1 = gcd pR1 pI1;
                p2 = pcompose p [:Complex (Re ub) (Im lb), Complex 0 (Im ub - Im lb):];
                pR2 = map_poly Re p2; pI2 = map_poly Im p2; gc2 = gcd pR2 pI2;
                p3 = pcompose p [:ub, Complex (Re lb - Re ub) 0:];
                pR3 = map_poly Re p3; pI3 = map_poly Im p3; gc3 = gcd pR3 pI3;
                p4 = pcompose p [:Complex (Re lb) (Im ub), Complex 0 (Im lb - Im ub):];
                pR4 = map_poly Re p4; pI4 = map_poly Im p4; gc4 = gcd pR4 pI4
              in
                if changes_itv_smods 0 1 gc1 (pderiv gc1) = 0
                   \<and> changes_itv_smods 0 1 gc2 (pderiv gc2) = 0 
                   \<and> changes_itv_smods 0 1 gc3 (pderiv gc3) = 0
                   \<and> changes_itv_smods 0 1 gc4 (pderiv gc4) = 0
                then 
                   nat (- (changes_alt_itv_smods 0 1 (pR1 div gc1) (pI1 div gc1)
                    + changes_alt_itv_smods 0 1 (pR2 div gc2) (pI2 div gc2)
                    + changes_alt_itv_smods 0 1 (pR3 div gc3) (pI3 div gc3)
                    + changes_alt_itv_smods 0 1 (pR4 div gc4) (pI4 div gc4)) div 4)
                else Code.abort (STR ''proots_rectangle fails when there is a root on the border.'') 
                        (\<lambda>_. proots_rectangle p lb ub))
            else Code.abort (STR ''proots_rectangle fails when there is a root on the border.'') 
              (\<lambda>_. proots_rectangle p lb ub)  
            else Code.abort (STR ''proots_rectangle fails when p=0.'') 
            (\<lambda>_. proots_rectangle p lb ub)
            else 0)"
proof -
  define p1 pR1 pI1 gc1
           p2 pR2 pI2 gc2
           p3 pR3 pI3 gc3
           p4 pR4 pI4 gc4
      where "p1 = pcompose p [:lb,  Complex (Re ub - Re lb) 0:]"
             and "pR1 = map_poly Re p1" and "pI1 = map_poly Im p1" and "gc1 = gcd pR1 pI1"
             and "p2 = pcompose p [:Complex (Re ub) (Im lb), Complex 0 (Im ub - Im lb):]"
             and "pR2 = map_poly Re p2" and "pI2 = map_poly Im p2" and "gc2 = gcd pR2 pI2"
             and "p3 = pcompose p [:ub, Complex (Re lb - Re ub) 0:]"
             and "pR3 = map_poly Re p3" and "pI3 = map_poly Im p3" and "gc3 = gcd pR3 pI3"
             and "p4 = pcompose p [:Complex (Re lb) (Im ub), Complex 0 (Im lb - Im ub):]"
             and "pR4 = map_poly Re p4" and "pI4 = map_poly Im p4" and "gc4 = gcd pR4 pI4" 
  define sms where 
      "sms = (- (changes_alt_itv_smods 0 1 (pR1 div gc1) (pI1 div gc1) +
                       changes_alt_itv_smods 0 1 (pR2 div gc2) (pI2 div gc2) +
                       changes_alt_itv_smods 0 1 (pR3 div gc3) (pI3 div gc3) +
                       changes_alt_itv_smods 0 1 (pR4 div gc4) (pI4 div gc4)) div
                    4)"
  have more_folds:"p1 = p \<circ>\<^sub>p [:lb, Complex (Re ub) (Im lb) - lb:]"
    "p2 = p \<circ>\<^sub>p [:Complex (Re ub) (Im lb), ub - Complex (Re ub) (Im lb):]"
    "p3 = p \<circ>\<^sub>p [:ub, Complex (Re lb) (Im ub) - ub:]"
    "p4 = p \<circ>\<^sub>p [:Complex (Re lb) (Im ub), lb - Complex (Re lb) (Im ub):]"
    subgoal unfolding p1_def 
      by (subst (10) complex_surj[symmetric],auto simp add:minus_complex.code)
    subgoal unfolding p2_def by (subst (10) complex_surj[symmetric],auto)
    subgoal unfolding p3_def by (subst (10) complex_surj[symmetric],auto simp add:minus_complex.code)
    subgoal unfolding p4_def by (subst (10) complex_surj[symmetric],auto)
    done    
  show ?thesis 
    apply (subst proots_rectangle_code1)
    apply (unfold no_proots_line_code Let_def)
    apply (fold p1_def p2_def p3_def p4_def pI1_def pR1_def pI2_def pR2_def pI3_def pR3_def
          pI4_def pR4_def gc1_def gc2_def gc3_def gc4_def more_folds)
    apply (fold sms_def)
    by presburger 
qed  

end