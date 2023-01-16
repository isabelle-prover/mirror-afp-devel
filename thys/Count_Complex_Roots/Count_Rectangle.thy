(*
Author:     Wenda Li <wl302@cam.ac.uk / liwenda1990@hotmail.com>
*)
theory Count_Rectangle imports Count_Line
begin

text \<open>Counting roots in a rectangular area can be in a purely algebraic approach 
  without introducing (analytic) winding number (@{term winding_number})
  nor the argument principle (@{thm argument_principle}). This has been illustrated
  by Michael Eisermann \<^cite>\<open>"eisermann2012fundamental"\<close>. We lightly make use of 
  @{term winding_number} here only to shorten the proof of one of the technical lemmas.\<close>    

subsection \<open>Misc\<close>

lemma proots_count_const:
  assumes "c\<noteq>0"
  shows "proots_count [:c:] s = 0"
  unfolding proots_count_def using assms by auto

lemma proots_count_nzero:
  assumes "\<And>x. x\<in>s \<Longrightarrow> poly p x\<noteq>0"
  shows "proots_count p s = 0"
  unfolding proots_count_def
  by(rule sum.neutral) (use assms in auto)

lemma complex_box_ne_empty: 
  fixes a b::complex
  shows 
    "cbox a b \<noteq> {} \<longleftrightarrow> (Re a \<le> Re b \<and> Im a \<le> Im b)"
    "box a b \<noteq> {} \<longleftrightarrow> (Re a < Re b \<and> Im a < Im b)"
  by (auto simp add:box_ne_empty Basis_complex_def) 

subsection \<open>Counting roots in a rectangle\<close>  
  
definition proots_rect ::"complex poly \<Rightarrow> complex \<Rightarrow> complex \<Rightarrow> nat" where
  "proots_rect p lb ub = proots_count p (box lb ub)"

definition proots_crect ::"complex poly \<Rightarrow> complex \<Rightarrow> complex \<Rightarrow> nat" where
  "proots_crect p lb ub = proots_count p (cbox lb ub)" 

definition proots_rect_ll ::"complex poly \<Rightarrow> complex \<Rightarrow> complex \<Rightarrow> nat" where
  "proots_rect_ll p lb ub = proots_count p (box lb ub \<union> {lb} 
                              \<union> open_segment lb (Complex (Re ub) (Im lb))
                              \<union> open_segment lb (Complex (Re lb) (Im ub)))" 

definition proots_rect_border::"complex poly \<Rightarrow> complex \<Rightarrow> complex \<Rightarrow> nat" where
  "proots_rect_border p a b = proots_count p (path_image (rectpath a b))"

definition not_rect_vertex::"complex \<Rightarrow> complex \<Rightarrow> complex \<Rightarrow> bool" where 
  "not_rect_vertex r a b = (r\<noteq>a \<and> r \<noteq> Complex (Re b) (Im a) \<and> r\<noteq>b \<and> r\<noteq>Complex (Re a) (Im b))"

definition not_rect_vanishing :: "complex poly \<Rightarrow> complex \<Rightarrow> complex \<Rightarrow> bool" where
  "not_rect_vanishing p a b = (poly p a\<noteq>0 \<and> poly p (Complex (Re b) (Im a)) \<noteq> 0 
                            \<and> poly p b \<noteq>0 \<and> poly p (Complex (Re a) (Im b))\<noteq> 0)"

lemma cindexP_rectpath_edge_base:
  assumes "Re a < Re b" "Im a < Im b"
    and "not_rect_vertex r a b"
    and "r\<in>path_image (rectpath a b)"
  shows "cindexP_pathE [:-r,1:] (rectpath a b) = -1"
proof -
  have r_nzero:"r\<noteq>a" "r\<noteq>Complex (Re b) (Im a)" "r\<noteq>b" "r\<noteq>Complex (Re a) (Im b)" 
    using \<open>not_rect_vertex r a b\<close> unfolding not_rect_vertex_def by auto

  define rr where "rr = [:-r,1:]"
  have rr_linepath:"cindexP_pathE rr (linepath a b) 
          = cindex_pathE (linepath (a - r) (b-r)) 0 " for a b
     unfolding rr_def 
     unfolding cindexP_lineE_def cindexP_pathE_def poly_linepath_comp
     by (simp add:poly_pcompose comp_def linepath_def scaleR_conv_of_real algebra_simps)

  have cindexP_pathE_eq:"cindexP_pathE rr (rectpath a b) = 
                 cindexP_pathE rr (linepath a (Complex (Re b) (Im a)))  
                 + cindexP_pathE rr (linepath (Complex (Re b) (Im a)) b) 
                 + cindexP_pathE rr (linepath b (Complex (Re a) (Im b))) 
                 + cindexP_pathE rr (linepath (Complex (Re a) (Im b)) a)"
    unfolding rectpath_def Let_def 
    by ((subst cindex_poly_pathE_joinpaths
            |subst finite_ReZ_segments_joinpaths
            |intro path_poly_comp conjI);
        (simp add:poly_linepath_comp finite_ReZ_segments_poly_of_real path_compose_join 
          pathfinish_compose pathstart_compose poly_pcompose)?)+

  have "(Im r = Im a \<and> Re a < Re r \<and> Re r < Re b)
        \<or> (Re r = Re b \<and> Im a < Im r \<and> Im r < Im b)
        \<or> (Im r = Im b \<and> Re a < Re r \<and> Re r < Re b)
        \<or> (Re r = Re a \<and> Im a < Im r \<and> Im r < Im b)"
  proof -
    have "r \<in> closed_segment a (Complex (Re b) (Im a)) 
          \<or> r \<in> closed_segment (Complex (Re b) (Im a)) b 
          \<or> r \<in> closed_segment b (Complex (Re a) (Im b)) 
          \<or> r \<in> closed_segment (Complex (Re a) (Im b)) a"
      using \<open>r\<in>path_image (rectpath a b)\<close>
      unfolding rectpath_def Let_def
      by (subst (asm) path_image_join;simp)+
    then show ?thesis 
      by (smt (verit, del_insts) assms(1) assms(2) r_nzero 
          closed_segment_commute closed_segment_imp_Re_Im(1) closed_segment_imp_Re_Im(2) 
          complex.sel(1) complex.sel(2) complex_eq_iff)
  qed
  moreover have "cindexP_pathE rr (rectpath a b) = -1" 
    if "Im r = Im a" "Re a < Re r" "Re r < Re b" 
  proof -
    have "cindexP_pathE rr (linepath a (Complex (Re b) (Im a))) = 0"
      unfolding rr_linepath
      apply (rule cindex_pathE_linepath_on)
      using closed_segment_degen_complex(2) that(1) that(2) that(3) by auto
    moreover have "cindexP_pathE rr (linepath (Complex (Re b) (Im a)) b) = 0"
      unfolding rr_linepath
      apply (subst cindex_pathE_linepath)  
      subgoal using closed_segment_imp_Re_Im(1) that(3) by fastforce
      subgoal using that assms unfolding Let_def by auto
      done
    moreover have "cindexP_pathE rr (linepath b (Complex (Re a) (Im b))) = -1"
      unfolding rr_linepath
      apply (subst cindex_pathE_linepath)
      subgoal using assms(2) closed_segment_imp_Re_Im(2) that(1) by fastforce
      subgoal using that assms unfolding Let_def by auto
      done
    moreover have "cindexP_pathE rr (linepath (Complex (Re a) (Im b)) a) = 0"
      unfolding rr_linepath
      apply (subst cindex_pathE_linepath)
      subgoal using closed_segment_imp_Re_Im(1) that(2) by fastforce
      subgoal using that assms unfolding Let_def by auto
      done
    ultimately show ?thesis unfolding cindexP_pathE_eq by auto
  qed
  moreover have "cindexP_pathE rr (rectpath a b) = -1" 
    if "Re r = Re b" "Im a < Im r" "Im r < Im b" 
  proof -
    have "cindexP_pathE rr (linepath a (Complex (Re b) (Im a))) = -1/2"
      unfolding rr_linepath
      apply (subst cindex_pathE_linepath) 
      subgoal using closed_segment_imp_Re_Im(2) that(2) by fastforce
      subgoal using that assms unfolding Let_def by auto 
      done
    moreover have "cindexP_pathE rr (linepath (Complex (Re b) (Im a)) b) = 0"
      unfolding rr_linepath
      apply (rule cindex_pathE_linepath_on)
      using closed_segment_degen_complex(1) that(1) that(2) that(3) by auto

    moreover have "cindexP_pathE rr (linepath b (Complex (Re a) (Im b))) = -1/2"
      unfolding rr_linepath
      apply (subst cindex_pathE_linepath)
      subgoal using closed_segment_imp_Re_Im(2) that(3) by fastforce
      subgoal using that assms unfolding Let_def by auto
      done
    moreover have "cindexP_pathE rr (linepath (Complex (Re a) (Im b)) a) = 0"
      unfolding rr_linepath
      apply (subst cindex_pathE_linepath)
      subgoal using assms(1) closed_segment_imp_Re_Im(1) that(1) by fastforce
      subgoal using that assms unfolding Let_def by auto
      done
    ultimately show ?thesis unfolding cindexP_pathE_eq by auto
  qed
  moreover have "cindexP_pathE rr (rectpath a b) = -1" 
    if "Im r = Im b" "Re a < Re r" "Re r < Re b" 
  proof -
    have "cindexP_pathE rr (linepath a (Complex (Re b) (Im a))) = -1"
      unfolding rr_linepath
      apply (subst cindex_pathE_linepath) 
      subgoal using assms(2) closed_segment_imp_Re_Im(2) that(1) by fastforce
      subgoal using that assms unfolding Let_def by auto 
      done
    moreover have "cindexP_pathE rr (linepath (Complex (Re b) (Im a)) b) = 0"
      unfolding rr_linepath
      apply (subst cindex_pathE_linepath) 
      subgoal using closed_segment_imp_Re_Im(1) that(3) by force
      subgoal using that assms unfolding Let_def by auto
      done
    moreover have "cindexP_pathE rr (linepath b (Complex (Re a) (Im b))) = 0"
      unfolding rr_linepath
      apply (rule cindex_pathE_linepath_on)
      by (smt (verit, del_insts) Im_poly_hom.base.hom_zero Re_poly_hom.base.hom_zero 
          closed_segment_commute closed_segment_degen_complex(2) complex.sel(1) 
          complex.sel(2) minus_complex.simps(1) minus_complex.simps(2) that(1) that(2) that(3))
    moreover have "cindexP_pathE rr (linepath (Complex (Re a) (Im b)) a) = 0"
      unfolding rr_linepath
      apply (subst cindex_pathE_linepath)
      subgoal using closed_segment_imp_Re_Im(1) that(2) by fastforce
      subgoal using that assms unfolding Let_def by auto
      done
    ultimately show ?thesis unfolding cindexP_pathE_eq by auto
  qed
  moreover have "cindexP_pathE rr (rectpath a b) = -1" 
    if "Re r = Re a" "Im a < Im r" "Im r < Im b" 
  proof -
    have "cindexP_pathE rr (linepath a (Complex (Re b) (Im a))) = -1/2"
      unfolding rr_linepath
      apply (subst cindex_pathE_linepath) 
      subgoal using closed_segment_imp_Re_Im(2) that(2) by fastforce
      subgoal using that assms unfolding Let_def by auto 
      done
    moreover have "cindexP_pathE rr (linepath (Complex (Re b) (Im a)) b) = 0"
      unfolding rr_linepath
      apply (subst cindex_pathE_linepath) 
      subgoal using assms(1) closed_segment_imp_Re_Im(1) that(1) by fastforce
      subgoal using that assms unfolding Let_def by auto
      done
    moreover have "cindexP_pathE rr (linepath b (Complex (Re a) (Im b))) = -1/2"
      unfolding rr_linepath
      apply (subst cindex_pathE_linepath) 
      subgoal using closed_segment_imp_Re_Im(2) that(3) by fastforce
      subgoal using that assms unfolding Let_def by auto
      done
    moreover have "cindexP_pathE rr (linepath (Complex (Re a) (Im b)) a) = 0"
      unfolding rr_linepath
      apply (rule cindex_pathE_linepath_on)
      by (smt (verit) Im_poly_hom.base.hom_zero Re_poly_hom.base.hom_zero 
          closed_segment_commute closed_segment_degen_complex(1) complex.sel(1) 
          complex.sel(2) minus_complex.simps(1) minus_complex.simps(2) that(1) that(2) that(3))
    ultimately show ?thesis unfolding cindexP_pathE_eq by auto
  qed
  ultimately show ?thesis unfolding rr_def by auto
qed

lemma cindexP_rectpath_vertex_base:
  assumes "Re a < Re b" "Im a < Im b"
    and "\<not> not_rect_vertex r a b" 
  shows "cindexP_pathE [:-r,1:] (rectpath a b) = -1/2"
proof -
  have r_cases:"r=a \<or> r=Complex (Re b) (Im a)\<or> r=b \<or> r=Complex (Re a) (Im b)" 
    using \<open>\<not> not_rect_vertex r a b\<close> unfolding not_rect_vertex_def by auto
  define rr where "rr = [:-r,1:]"
  have rr_linepath:"cindexP_pathE rr (linepath a b) 
          = cindex_pathE (linepath (a - r) (b-r)) 0 " for a b
     unfolding rr_def 
     unfolding cindexP_lineE_def cindexP_pathE_def poly_linepath_comp
     by (simp add:poly_pcompose comp_def linepath_def scaleR_conv_of_real algebra_simps)

  have cindexP_pathE_eq:"cindexP_pathE rr (rectpath a b) = 
                 cindexP_pathE rr (linepath a (Complex (Re b) (Im a)))  
                 + cindexP_pathE rr (linepath (Complex (Re b) (Im a)) b) 
                 + cindexP_pathE rr (linepath b (Complex (Re a) (Im b))) 
                 + cindexP_pathE rr (linepath (Complex (Re a) (Im b)) a)"
    unfolding rectpath_def Let_def 
    by ((subst cindex_poly_pathE_joinpaths
            |subst finite_ReZ_segments_joinpaths
            |intro path_poly_comp conjI);
        (simp add:poly_linepath_comp finite_ReZ_segments_poly_of_real path_compose_join 
          pathfinish_compose pathstart_compose poly_pcompose)?)+

  have "cindexP_pathE rr (rectpath a b) = -1/2" 
    if "r=a" 
  proof -
    have "cindexP_pathE rr (linepath a (Complex (Re b) (Im a))) = 0"
      unfolding rr_linepath
      apply (rule cindex_pathE_linepath_on)
      by (simp add: that)
    moreover have "cindexP_pathE rr (linepath (Complex (Re b) (Im a)) b) = 0"
      unfolding rr_linepath
      apply (subst cindex_pathE_linepath)  
      subgoal using assms(1) closed_segment_imp_Re_Im(1) that by fastforce
      subgoal using that assms unfolding Let_def by auto
      done
    moreover have "cindexP_pathE rr (linepath b (Complex (Re a) (Im b))) = -1/2"
      unfolding rr_linepath
      apply (subst cindex_pathE_linepath)
      subgoal using assms(2) closed_segment_imp_Re_Im(2) that(1) by fastforce
      subgoal using that assms unfolding Let_def by auto
      done
    moreover have "cindexP_pathE rr (linepath (Complex (Re a) (Im b)) a) = 0"
      unfolding rr_linepath
      apply (rule cindex_pathE_linepath_on)
      by (simp add: that)
    ultimately show ?thesis unfolding cindexP_pathE_eq by auto
  qed
  moreover have "cindexP_pathE rr (rectpath a b) = -1/2" 
    if "r=Complex (Re b) (Im a)" 
  proof -
    have "cindexP_pathE rr (linepath a (Complex (Re b) (Im a))) = 0"
      unfolding rr_linepath
      apply (rule cindex_pathE_linepath_on)
      by (simp add: that)
    moreover have "cindexP_pathE rr (linepath (Complex (Re b) (Im a)) b) = 0"
      unfolding rr_linepath
      apply (rule cindex_pathE_linepath_on)
      by (simp add: that)
    moreover have "cindexP_pathE rr (linepath b (Complex (Re a) (Im b))) = -1/2"
      unfolding rr_linepath
      apply (subst cindex_pathE_linepath)
      subgoal using assms(2) closed_segment_imp_Re_Im(2) that(1) by fastforce
      subgoal using that assms unfolding Let_def by auto
      done
    moreover have "cindexP_pathE rr (linepath (Complex (Re a) (Im b)) a) = 0"
      unfolding rr_linepath
      apply (subst cindex_pathE_linepath)
      subgoal using assms(1) closed_segment_imp_Re_Im(1) that by fastforce
      subgoal by (smt (z3) complex.sel(1) minus_complex.simps(1))
      done
    ultimately show ?thesis unfolding cindexP_pathE_eq by auto
  qed
  moreover have "cindexP_pathE rr (rectpath a b) = -1/2" 
    if "r=b" 
  proof -
    have "cindexP_pathE rr (linepath a (Complex (Re b) (Im a))) = -1/2"
      unfolding rr_linepath
      apply (subst cindex_pathE_linepath)
      subgoal using assms(2) closed_segment_imp_Re_Im(2) that by fastforce
      subgoal using assms(1) assms(2) that by auto
      done
    moreover have "cindexP_pathE rr (linepath (Complex (Re b) (Im a)) b) = 0"
      unfolding rr_linepath
      apply (rule cindex_pathE_linepath_on)
      by (simp add: that)
    moreover have "cindexP_pathE rr (linepath b (Complex (Re a) (Im b))) = 0"
      unfolding rr_linepath
      apply (rule cindex_pathE_linepath_on)
      by (simp add: that)
    moreover have "cindexP_pathE rr (linepath (Complex (Re a) (Im b)) a) = 0"
      unfolding rr_linepath
      apply (subst cindex_pathE_linepath)
      subgoal using assms(1) closed_segment_imp_Re_Im(1) that by fastforce
      subgoal by (smt (z3) complex.sel(1) minus_complex.simps(1))
      done
    ultimately show ?thesis unfolding cindexP_pathE_eq by auto
  qed
  moreover have "cindexP_pathE rr (rectpath a b) = -1/2" 
    if "r=Complex (Re a) (Im b)" 
  proof -
    have "cindexP_pathE rr (linepath a (Complex (Re b) (Im a))) = -1/2"
      unfolding rr_linepath
      apply (subst cindex_pathE_linepath)
      subgoal using assms(2) closed_segment_imp_Re_Im(2) that by fastforce
      subgoal using assms(1) assms(2) that by auto
      done
    moreover have "cindexP_pathE rr (linepath (Complex (Re b) (Im a)) b) = 0"
      unfolding rr_linepath
      apply (subst cindex_pathE_linepath)
      subgoal using assms(1) closed_segment_imp_Re_Im(1) that by fastforce
      subgoal by (smt (z3) complex.sel(1) minus_complex.simps(1))
      done
    moreover have "cindexP_pathE rr (linepath b (Complex (Re a) (Im b))) = 0"
      unfolding rr_linepath
      apply (rule cindex_pathE_linepath_on)
      by (simp add: that)
    moreover have "cindexP_pathE rr (linepath (Complex (Re a) (Im b)) a) = 0"
      unfolding rr_linepath
      apply (rule cindex_pathE_linepath_on)
      by (simp add: that)
    ultimately show ?thesis unfolding cindexP_pathE_eq by auto
  qed
  ultimately show ?thesis using r_cases unfolding rr_def by auto
qed

lemma cindexP_rectpath_interior_base:
  assumes "r\<in>box a b"
  shows "cindexP_pathE [:-r,1:] (rectpath a b) = -2"
proof -
  have inbox:"Re r \<in> {Re a<..<Re b} \<and> Im r \<in> {Im a<..<Im b}"
    using \<open>r\<in>box a b\<close> unfolding in_box_complex_iff by auto
  then have r_nzero:"r\<noteq>a" "r\<noteq>Complex (Re b) (Im a)" "r\<noteq>b" "r\<noteq>Complex (Re a) (Im b)" 
    by auto
  have "Re a < Re b" "Im a < Im b"
    using \<open>r\<in>box a b\<close> complex_box_ne_empty by blast+

  define rr where "rr = [:-r,1:]"
  have rr_linepath:"cindexP_pathE rr (linepath a b) 
          = cindex_pathE (linepath (a - r) (b-r)) 0 " for a b
     unfolding rr_def 
     unfolding cindexP_lineE_def cindexP_pathE_def poly_linepath_comp
     by (simp add:poly_pcompose comp_def linepath_def scaleR_conv_of_real algebra_simps)

  have "cindexP_pathE rr (rectpath a b) = 
                 cindexP_pathE rr (linepath a (Complex (Re b) (Im a)))  
                 + cindexP_pathE rr (linepath (Complex (Re b) (Im a)) b) 
                 + cindexP_pathE rr (linepath b (Complex (Re a) (Im b))) 
                 + cindexP_pathE rr (linepath (Complex (Re a) (Im b)) a)"
    unfolding rectpath_def Let_def 
    by ((subst cindex_poly_pathE_joinpaths
            |subst finite_ReZ_segments_joinpaths
            |intro path_poly_comp conjI);
        (simp add:poly_linepath_comp finite_ReZ_segments_poly_of_real path_compose_join 
          pathfinish_compose pathstart_compose poly_pcompose)?)+
  also have "... = -2"
  proof -
    have "cindexP_pathE rr (linepath a (Complex (Re b) (Im a))) = -1"
      unfolding rr_linepath
      apply (subst cindex_pathE_linepath)
      subgoal using closed_segment_imp_Re_Im(2) inbox by fastforce
      using inbox by auto
    moreover have "cindexP_pathE rr (linepath (Complex (Re b) (Im a)) b) = 0"
      unfolding rr_linepath
      apply (subst cindex_pathE_linepath)  
      subgoal using closed_segment_imp_Re_Im(1) inbox by fastforce
      using inbox by auto
    moreover have "cindexP_pathE rr (linepath b (Complex (Re a) (Im b))) = -1"
      unfolding rr_linepath
      apply (subst cindex_pathE_linepath)
      subgoal using closed_segment_imp_Re_Im(2) inbox by fastforce
      using inbox by auto
    moreover have "cindexP_pathE rr (linepath (Complex (Re a) (Im b)) a) = 0"
      unfolding rr_linepath
      apply (subst cindex_pathE_linepath)
      subgoal using closed_segment_imp_Re_Im(1) inbox by fastforce
      using inbox by auto
    ultimately show ?thesis by auto
  qed
  finally show ?thesis unfolding rr_def .
qed


lemma cindexP_rectpath_outside_base:
  assumes "Re a < Re b" "Im a < Im b" 
    and "r\<notin>cbox a b"
  shows "cindexP_pathE [:-r,1:] (rectpath a b) = 0"
proof -
  have not_cbox:"\<not> (Re r \<in> {Re a..Re b} \<and> Im r \<in> {Im a..Im b})"
    using \<open>r\<notin>cbox a b\<close> unfolding in_cbox_complex_iff by auto
  then have r_nzero:"r\<noteq>a" "r\<noteq>Complex (Re b) (Im a)" "r\<noteq>b" "r\<noteq>Complex (Re a) (Im b)" 
    using assms by auto

  define rr where "rr = [:-r,1:]"
  have rr_linepath:"cindexP_pathE rr (linepath a b) 
          = cindex_pathE (linepath (a - r) (b-r)) 0 " for a b
     unfolding rr_def 
     unfolding cindexP_lineE_def cindexP_pathE_def poly_linepath_comp
     by (simp add:poly_pcompose comp_def linepath_def scaleR_conv_of_real algebra_simps)

  have "cindexP_pathE rr (rectpath a b) = 
                 cindexP_pathE rr (linepath a (Complex (Re b) (Im a)))  
                 + cindexP_pathE rr (linepath (Complex (Re b) (Im a)) b) 
                 + cindexP_pathE rr (linepath b (Complex (Re a) (Im b))) 
                 + cindexP_pathE rr (linepath (Complex (Re a) (Im b)) a)"
    unfolding rectpath_def Let_def 
    by ((subst cindex_poly_pathE_joinpaths
            |subst finite_ReZ_segments_joinpaths
            |intro path_poly_comp conjI);
        (simp add:poly_linepath_comp finite_ReZ_segments_poly_of_real path_compose_join 
          pathfinish_compose pathstart_compose poly_pcompose)?)+
  have "cindexP_pathE rr (rectpath a b) = cindex_pathE (poly rr \<circ> rectpath a b) 0"
    unfolding cindexP_pathE_def by simp
  also have "...  = - 2 * winding_number (poly rr \<circ> rectpath a b) 0"
    \<comment>\<open>We don't need \<^term>\<open>winding_number\<close> to finish the proof, but thanks to Cauthy's
      Index theorem  (i.e., @{thm "winding_number_cindex_pathE"}) we can make the proof shorter.\<close>
  proof -
    have "winding_number (poly rr \<circ> rectpath a b) 0 
            = - cindex_pathE (poly rr \<circ> rectpath a b) 0 / 2"
    proof (rule winding_number_cindex_pathE)
      show "finite_ReZ_segments (poly rr \<circ> rectpath a b) 0"
        using finite_ReZ_segments_poly_rectpath  .
      show "valid_path (poly rr \<circ> rectpath a b)"
        using valid_path_poly_rectpath .
      show "0 \<notin> path_image (poly rr \<circ> rectpath a b)"
        by (smt (z3) DiffE add.right_neutral add_diff_cancel_left' add_uminus_conv_diff 
            assms(1) assms(2) assms(3) basic_cqe_conv1(1) diff_add_cancel imageE mult.right_neutral 
            mult_zero_right path_image_compose path_image_rectpath_cbox_minus_box poly_pCons rr_def)
      show "pathfinish (poly rr \<circ> rectpath a b) = pathstart (poly rr \<circ> rectpath a b)"
        by (simp add: pathfinish_compose pathstart_compose)
    qed
    then show ?thesis by auto
  qed
  also have "... = 0"
  proof -
    have "winding_number (poly rr \<circ> rectpath a b) 0 = 0"
    proof (rule winding_number_zero_outside)
      have "path_image (poly rr \<circ> rectpath a b) = poly rr ` path_image (rectpath a b)"
        using path_image_compose by simp
      also have "... = poly rr ` (cbox a b - box a b)"
        apply (subst path_image_rectpath_cbox_minus_box)
        using assms(1,2) by (simp|blast)+
      also have "... \<subseteq> (\<lambda>x. x -r) ` cbox a b"
        unfolding rr_def by (simp add: image_subset_iff)
      finally show "path_image (poly rr \<circ> rectpath a b) \<subseteq> (\<lambda>x. x -r) ` cbox a b" .
      show "0 \<notin> (\<lambda>x. x - r) ` cbox a b" using assms(3) by force
      show "path (poly rr \<circ> rectpath a b)" by (simp add: path_poly_comp)
      show " convex ((\<lambda>x. x - r) ` cbox a b)" 
        using convex_box(1) convex_translation_subtract_eq by blast
      show "pathfinish (poly rr \<circ> rectpath a b) = pathstart (poly rr \<circ> rectpath a b)"
        by (simp add: pathfinish_compose pathstart_compose)
    qed
    then show ?thesis by simp
  qed
  finally show ?thesis  unfolding rr_def by simp
qed

lemma cindexP_rectpath_add_one_root:
  assumes "Re a < Re b" "Im a < Im b"
    and "not_rect_vertex r a b"
    and "not_rect_vanishing p a b"
  shows "cindexP_pathE ([:-r,1:]*p) (rectpath a b) = 
                cindexP_pathE p (rectpath a b) 
          + (if r\<in>box a b then -2 else if r\<in>path_image (rectpath a b) then - 1 else 0)"
proof -
  define rr where "rr = [:-r,1:]"
  have rr_nzero:"poly rr a\<noteq>0" "poly rr (Complex (Re b) (Im a))\<noteq>0" 
                "poly rr b\<noteq>0" "poly rr (Complex (Re a) (Im b))\<noteq>0"
    using \<open>not_rect_vertex r a b\<close> unfolding rr_def not_rect_vertex_def by auto

  have p_nzero:"poly p a\<noteq>0" "poly p (Complex (Re b) (Im a))\<noteq>0" 
                "poly p b\<noteq>0" "poly p (Complex (Re a) (Im b))\<noteq>0"
    using \<open>not_rect_vanishing p a b\<close> unfolding not_rect_vanishing_def by auto

  define cindp where "cindp = (\<lambda>p a b. 
                                    cindexP_lineE p a (Complex (Re b) (Im a))
                                    + cindexP_lineE p (Complex (Re b) (Im a)) b
                                    + cindexP_lineE p b (Complex (Re a) (Im b))
                                    + cindexP_lineE p (Complex (Re a) (Im b)) a
                                )"
  define cdiff  where "cdiff = (\<lambda>rr p a b. 
                                     cdiff_aux rr p a (Complex (Re b) (Im a))
                                    + cdiff_aux rr p (Complex (Re b) (Im a)) b
                                    + cdiff_aux rr p b (Complex (Re a) (Im b))
                                    + cdiff_aux rr p (Complex (Re a) (Im b)) a 
                                )"

  have "cindexP_pathE (rr*p) (rectpath a b) = 
                 cindexP_pathE (rr*p) (linepath a (Complex (Re b) (Im a)))  
                 + cindexP_pathE (rr*p) (linepath (Complex (Re b) (Im a)) b) 
                 + cindexP_pathE (rr*p) (linepath b (Complex (Re a) (Im b))) 
                 + cindexP_pathE (rr*p) (linepath (Complex (Re a) (Im b)) a)"
    unfolding rectpath_def Let_def 
    by ((subst cindex_poly_pathE_joinpaths
            |subst finite_ReZ_segments_joinpaths
            |intro path_poly_comp conjI);
        (simp add:poly_linepath_comp finite_ReZ_segments_poly_of_real path_compose_join 
          pathfinish_compose pathstart_compose poly_pcompose)?)+
  also have "... = cindexP_lineE (rr*p) a (Complex (Re b) (Im a)) 
                      + cindexP_lineE (rr*p) (Complex (Re b) (Im a)) b 
                      + cindexP_lineE (rr*p) b (Complex (Re a) (Im b)) 
                      + cindexP_lineE (rr*p) (Complex (Re a) (Im b)) a"
    unfolding cindexP_lineE_def by simp
  also have "... = cindp rr a b + cindp p a b + cdiff rr p a b/2"
    unfolding cindp_def cdiff_def
    by (subst cindexP_lineE_times;
          (use rr_nzero p_nzero one_complex.code imaginary_unit.code in simp)?)+
  also have "... = cindexP_pathE p (rectpath a b) +(if r\<in>box a b then -2 else 
      if r\<in>path_image (rectpath a b) then - 1 else 0)"
  proof -
    have "cindp rr a b = cindexP_pathE rr (rectpath a b)" 
      unfolding rectpath_def Let_def cindp_def cindexP_lineE_def
      by ((subst cindex_poly_pathE_joinpaths
            |subst finite_ReZ_segments_joinpaths
            |intro path_poly_comp conjI);
        (simp add:poly_linepath_comp finite_ReZ_segments_poly_of_real path_compose_join 
          pathfinish_compose pathstart_compose poly_pcompose)?)+
    also have "... = (if r\<in>box a b then -2 else 
      if r\<in>path_image (rectpath a b) then - 1 else 0)" 
    proof -
      have ?thesis if "r\<in>box a b" 
        using cindexP_rectpath_interior_base rr_def that by presburger
      moreover have ?thesis if "r\<notin>box a b" "r\<in>path_image (rectpath a b)" 
        using cindexP_rectpath_edge_base[OF assms(1,2,3)] that unfolding rr_def by auto
      moreover have ?thesis if "r\<notin>box a b" "r\<notin>path_image (rectpath a b)" 
      proof -
        have "r\<notin>cbox a b"
          using that assms(1) assms(2) path_image_rectpath_cbox_minus_box by auto
        then show ?thesis unfolding rr_def
          using assms(1) assms(2) cindexP_rectpath_outside_base that(1) that(2) by presburger
      qed
      ultimately show ?thesis by auto
    qed
    finally have "cindp rr a b = (if r\<in>box a b then -2 else 
      if r\<in>path_image (rectpath a b) then - 1 else 0)" .
    moreover have "cindp p a b = cindexP_pathE p (rectpath a b)" 
      unfolding rectpath_def Let_def cindp_def cindexP_lineE_def
      by ((subst cindex_poly_pathE_joinpaths
            |subst finite_ReZ_segments_joinpaths
            |intro path_poly_comp conjI);
        (simp add:poly_linepath_comp finite_ReZ_segments_poly_of_real path_compose_join 
          pathfinish_compose pathstart_compose poly_pcompose)?)+
    moreover have "cdiff rr p a b = 0" 
      unfolding cdiff_def cdiff_aux_def by simp
    ultimately show ?thesis by auto
  qed
  finally show ?thesis unfolding rr_def .
qed

lemma proots_rect_cindexP_pathE:
  assumes "Re a < Re b" "Im a < Im b"
    and "not_rect_vanishing p a b"
  shows "proots_rect p a b = -(proots_rect_border p a b +cindexP_pathE p (rectpath a b)) / 2"
  using \<open>not_rect_vanishing p a b\<close>
proof (induct p rule:poly_root_induct_alt)
  case 0
  then have False unfolding not_rect_vanishing_def by auto
  then show ?case by simp
next
  case (no_proots p)
  then obtain c where pc:"p=[:c:]" "c\<noteq>0" 
    by (meson fundamental_theorem_of_algebra_alt)
  have "cindexP_pathE p (rectpath a b) = 0"
    using pc by (auto intro:cindexP_pathE_const)
  moreover have "proots_rect p a b = 0" "proots_rect_border p a b = 0"
    using pc proots_count_const 
    unfolding proots_rect_def proots_rect_border_def by auto
  ultimately show ?case by auto 
next
  case (root r p)
  define rr where "rr=[:-r,1:]"

  have hyps:"real (proots_rect p a b) =
              -(proots_rect_border p a b + cindexP_pathE p (rectpath a b)) / 2"
    apply (rule root(1))
    by (meson not_rect_vanishing_def poly_mult_zero_iff root.prems)

  have cind_eq:"cindexP_pathE (rr * p) (rectpath a b) =
          cindexP_pathE p (rectpath a b) +
            (if r \<in> box a b then - 2 else if r \<in> path_image (rectpath a b) then - 1 else 0)"
  proof (rule cindexP_rectpath_add_one_root[OF assms(1,2),of r p,folded rr_def])
    show " not_rect_vertex r a b" 
      using not_rect_vanishing_def not_rect_vertex_def root.prems by auto
    show "not_rect_vanishing p a b"
      using not_rect_vanishing_def root.prems by force
  qed

  have rect_eq:"proots_rect (rr * p) a b = proots_rect p a b
                                            + (if r\<in>box a b then 1 else 0)"
  proof -
    have "proots_rect (rr * p) a b 
            = proots_count rr (box a b) + proots_rect p a b"
      unfolding proots_rect_def
      apply (rule proots_count_times)
      by (metis not_rect_vanishing_def poly_0 root.prems rr_def)
    moreover have "proots_count rr (box a b) = (if r\<in>box a b then 1 else 0)"
      using proots_count_pCons_1_iff rr_def by blast
    ultimately show ?thesis by auto
  qed

  have border_eq:"proots_rect_border (rr * p) a b = 
              proots_rect_border p a b
                              + (if r \<in> path_image (rectpath a b) then 1 else 0)"
  proof -
    have "proots_rect_border (rr * p) a b = proots_count rr (path_image (rectpath a b)) 
                  +  proots_rect_border p a b"
      unfolding proots_rect_border_def
      apply (rule proots_count_times)
      by (metis not_rect_vanishing_def poly_0 root.prems rr_def)
    moreover have "proots_count rr (path_image (rectpath a b)) 
            = (if r \<in> path_image (rectpath a b) then 1 else 0)"
      using proots_count_pCons_1_iff rr_def by blast
    ultimately show ?thesis by auto
  qed

  have ?case if "r \<in> box a b" 
  proof -
    have "proots_rect (rr * p) a b = proots_rect p a b + 1" 
      unfolding rect_eq  using that by auto 
    moreover have "proots_rect_border (rr * p) a b = proots_rect_border p a b" 
      unfolding border_eq  using that
      using assms(1) assms(2) path_image_rectpath_cbox_minus_box by auto 
    moreover have "cindexP_pathE (rr * p) (rectpath a b) = cindexP_pathE p (rectpath a b) - 2"
      using cind_eq that by auto
    ultimately show ?thesis using hyps 
      by (fold rr_def)  simp
  qed
  moreover have ?case if "r \<notin> box a b" "r \<in> path_image (rectpath a b)" 
  proof -
    have "proots_rect (rr * p) a b = proots_rect p a b" 
      unfolding rect_eq  using that by auto 
    moreover have "proots_rect_border (rr * p) a b = proots_rect_border p a b + 1" 
      unfolding border_eq  using that
      using assms(1) assms(2) path_image_rectpath_cbox_minus_box by auto 
    moreover have "cindexP_pathE (rr * p) (rectpath a b) = cindexP_pathE p (rectpath a b) - 1"
      using cind_eq that by auto
    ultimately show ?thesis using hyps 
      by (fold rr_def)  auto
  qed
  moreover have ?case if "r \<notin> box a b" "r \<notin> path_image (rectpath a b)" 
  proof -
    have "proots_rect (rr * p) a b = proots_rect p a b" 
      unfolding rect_eq  using that by auto 
    moreover have "proots_rect_border (rr * p) a b = proots_rect_border p a b" 
      unfolding border_eq  using that
      using assms(1) assms(2) path_image_rectpath_cbox_minus_box by auto 
    moreover have "cindexP_pathE (rr * p) (rectpath a b) = cindexP_pathE p (rectpath a b)"
      using cind_eq that by auto
    ultimately show ?thesis using hyps 
      by (fold rr_def)  auto
  qed
  ultimately show ?case  by auto
qed

subsection \<open>Code generation\<close>

lemmas Complex_minus_eq = minus_complex.code

lemma cindexP_pathE_rect_smods:
  fixes p::"complex poly" and lb ub::complex
  assumes ab_le:"Re lb < Re ub" "Im lb < Im ub"
    and "not_rect_vanishing p lb  ub"
  shows "cindexP_pathE p (rectpath lb ub) = 
           (let p1 = pcompose p [:lb,  Complex (Re ub - Re lb) 0:];
                pR1 = map_poly Re p1; pI1 = map_poly Im p1; gc1 = gcd pR1 pI1;
                p2 = pcompose p [:Complex (Re ub) (Im lb), Complex 0 (Im ub - Im lb):];
                pR2 = map_poly Re p2; pI2 = map_poly Im p2; gc2 = gcd pR2 pI2;
                p3 = pcompose p [:ub, Complex (Re lb - Re ub) 0:];
                pR3 = map_poly Re p3; pI3 = map_poly Im p3; gc3 = gcd pR3 pI3;
                p4 = pcompose p [:Complex (Re lb) (Im ub), Complex 0 (Im lb - Im ub):];
                pR4 = map_poly Re p4; pI4 = map_poly Im p4; gc4 = gcd pR4 pI4
            in 
             (changes_alt_itv_smods 0 1 (pR1 div gc1) (pI1 div gc1)
                + changes_alt_itv_smods 0 1 (pR2 div gc2) (pI2 div gc2)
                + changes_alt_itv_smods 0 1 (pR3 div gc3) (pI3 div gc3)
                + changes_alt_itv_smods 0 1 (pR4 div gc4) (pI4 div gc4)
                ) / 2)" (is "?L=?R")
proof -
  have "cindexP_pathE p (rectpath lb ub) = 
                 cindexP_lineE p lb (Complex (Re ub) (Im lb)) 
                      + cindexP_lineE (p) (Complex (Re ub) (Im lb)) ub 
                      + cindexP_lineE (p) ub (Complex (Re lb) (Im ub)) 
                      + cindexP_lineE (p) (Complex (Re lb) (Im ub)) lb"
    unfolding rectpath_def Let_def cindexP_lineE_def
    by ((subst cindex_poly_pathE_joinpaths
            |subst finite_ReZ_segments_joinpaths
            |intro path_poly_comp conjI);
        (simp add:poly_linepath_comp finite_ReZ_segments_poly_of_real path_compose_join 
          pathfinish_compose pathstart_compose poly_pcompose)?)+
  also have "... = ?R"
    apply (subst (1 2 3 4)cindexP_lineE_changes)
    subgoal using assms(3) not_rect_vanishing_def by fastforce
    subgoal by (smt (verit) assms(2) complex.sel(2))
    subgoal by (metis assms(1) complex.sel(1) order_less_irrefl)
    subgoal by (smt (verit) assms(2) complex.sel(2))
    subgoal by (metis assms(1) complex.sel(1) order_less_irrefl)
    subgoal unfolding Let_def by (simp_all add:Complex_minus_eq)
    done
  finally show ?thesis .
qed

lemma open_segment_Im_equal:
  assumes "Re x \<noteq> Re y" "Im x=Im y"
  shows "open_segment x y = {z. Im z = Im x 
                                  \<and> Re z \<in> open_segment (Re x) (Re y)}" 
proof -
  have "open_segment x y = (\<lambda>u. (1 - u) *\<^sub>R x + u *\<^sub>R y) ` {0<..<1}"
    unfolding open_segment_image_interval
    using assms by auto
  also have "... = (\<lambda>u. Complex (Re x + u * (Re y - Re x)) 
                      (Im y)) ` {0<..<1}"
    apply (subst (1 2 3 4) complex_surj[symmetric])
    using assms by (simp add:scaleR_conv_of_real algebra_simps)
  also have "... = {z. Im z = Im x \<and> Re z \<in> open_segment (Re x) (Re y)}"
  proof -
    have "Re x + u * (Re y - Re x) \<in> open_segment (Re x) (Re y)"
      if "Re x \<noteq> Re y" "Im x = Im y"  "0 < u" "u < 1" for u
    proof -
      define yx where "yx = Re y - Re x"
      have "Re y = yx + Re x" "yx >0 \<or> yx<0" 
        unfolding yx_def using that by auto
      then show ?thesis
        unfolding open_segment_eq_real_ivl
        using that mult_pos_neg by auto
    qed
    moreover have "z \<in> (\<lambda>xa. Complex (Re x + xa * (Re y -  Re x)) (Im y)) 
                          ` {0<..<1}"
      if "Im x = Im y" "Im z = Im y" "Re z \<in> open_segment (Re x) (Re y)" for z
      apply (rule rev_image_eqI[of "(Re z - Re x)/(Re y - Re x)"])
      subgoal 
        using that unfolding open_segment_eq_real_ivl 
        by (auto simp:divide_simps)
      subgoal using \<open>Re x \<noteq> Re y\<close> complex_eq_iff that(2) by auto
      done
    ultimately show ?thesis using assms by auto
  qed
  finally show ?thesis .
qed

lemma open_segment_Re_equal:
  assumes "Re x = Re y" "Im x\<noteq>Im y"
  shows "open_segment x y = {z. Re z = Re x 
                                  \<and> Im z \<in> open_segment (Im x) (Im y)}" 
proof -
  have "open_segment x y = (\<lambda>u. (1 - u) *\<^sub>R x + u *\<^sub>R y) ` {0<..<1}"
    unfolding open_segment_image_interval
    using assms by auto
  also have "... = (\<lambda>u. Complex (Re y)  (Im x + u * (Im y - Im x)) 
                      ) ` {0<..<1}"
    apply (subst (1 2 3 4) complex_surj[symmetric])
    using assms by (simp add:scaleR_conv_of_real algebra_simps)
  also have "... = {z. Re z = Re x \<and> Im z \<in> open_segment (Im x) (Im y)}"
  proof -
    have "Im x + u * (Im y - Im x) \<in> open_segment (Im x) (Im y)"
      if "Im x \<noteq> Im y" "Re x = Re y"  "0 < u" "u < 1" for u
    proof -
      define yx where "yx = Im y - Im x"
      have "Im y = yx + Im x" "yx >0 \<or> yx<0" 
        unfolding yx_def using that by auto
      then show ?thesis
        unfolding open_segment_eq_real_ivl
        using that mult_pos_neg by auto
    qed
    moreover have "z \<in> (\<lambda>xa. Complex (Re y) (Im x + xa * (Im y -  Im x)) ) 
                          ` {0<..<1}"
      if "Re x = Re y" "Re z = Re y" "Im z \<in> open_segment (Im x) (Im y)" for z
      apply (rule rev_image_eqI[of "(Im z - Im x)/(Im y - Im x)"])
      subgoal 
        using that unfolding open_segment_eq_real_ivl 
        by (auto simp:divide_simps)
      subgoal using \<open>Im x \<noteq> Im y\<close> complex_eq_iff that(2) by auto
      done
    ultimately show ?thesis using assms by auto
  qed
  finally show ?thesis .
qed

lemma Complex_eq_iff:
  "x = Complex y z \<longleftrightarrow> Re x = y \<and> Im x = z"
  "Complex y z = x \<longleftrightarrow> Re x = y \<and> Im x = z"
  by auto

lemma proots_rect_border_eq_lines:
  fixes p::"complex poly" and lb ub::complex
  assumes ab_le:"Re lb < Re ub" "Im lb < Im ub"
    and not_van:"not_rect_vanishing p lb ub"
  shows "proots_rect_border p lb ub = 
                  proots_line p lb (Complex (Re ub) (Im lb)) 
                      +  proots_line p (Complex (Re ub) (Im lb)) ub 
                      +  proots_line p ub (Complex (Re lb) (Im ub)) 
                      +  proots_line p (Complex (Re lb) (Im ub)) lb"
proof -
  have "p\<noteq>0" 
    using not_rect_vanishing_def not_van order_root by blast

  define l1 l2 l3 l4 where  "l1 = open_segment lb (Complex (Re ub) (Im lb))"
                        and "l2 = open_segment (Complex (Re ub) (Im lb)) ub"
                        and "l3 = open_segment ub (Complex (Re lb) (Im ub))"
                        and "l4 = open_segment (Complex (Re lb) (Im ub)) lb"
  have ll_eq:
    "l1 = {z. Im z \<in> {Im lb} \<and> Re z \<in> {Re lb<..<Re ub}}"
    "l2 = {z. Re z \<in> {Re ub} \<and> Im z \<in> {Im lb<..<Im ub}}"
    "l3 = {z. Im z \<in> {Im ub} \<and> Re z \<in> {Re lb<..<Re ub}}"
    "l4 = {z. Re z \<in> {Re lb} \<and> Im z \<in> {Im lb<..<Im ub}}"
    subgoal unfolding l1_def
      apply (subst open_segment_Im_equal)
      using assms unfolding open_segment_eq_real_ivl by auto
    subgoal unfolding l2_def
      apply (subst open_segment_Re_equal)
      using assms unfolding open_segment_eq_real_ivl by auto
    subgoal unfolding l3_def
      apply (subst open_segment_Im_equal)
      using assms unfolding open_segment_eq_real_ivl by auto
    subgoal unfolding l4_def
      apply (subst open_segment_Re_equal)
      using assms unfolding open_segment_eq_real_ivl by auto
    done
  
  have ll_disj: "l1 \<inter> l2 = {}" "l1 \<inter> l3 = {}" "l1 \<inter> l4 = {}"
       "l2 \<inter> l3 = {}" "l2 \<inter> l4 = {}" "l3 \<inter> l4 = {}"
    using assms unfolding ll_eq by auto

  have "proots_rect_border p lb ub = proots_count p
           ({z. Re z \<in> {Re lb, Re ub} \<and> Im z \<in> {Im lb..Im ub}} \<union>
            {z. Im z \<in> {Im lb, Im ub} \<and> Re z \<in> {Re lb..Re ub}})"
    unfolding proots_rect_border_def
    apply (subst path_image_rectpath)
    using assms(1,2) by auto
  also have "... = proots_count p
           ({z. Re z \<in> {Re lb, Re ub} \<and> Im z \<in> {Im lb<..<Im ub}} \<union>
            {z. Im z \<in> {Im lb, Im ub} \<and> Re z \<in> {Re lb<..<Re ub}} 
            \<union> {lb,Complex (Re ub) (Im lb), ub,Complex (Re lb) (Im ub)})"
    apply (rule arg_cong2[where f=proots_count])
    unfolding not_rect_vanishing_def using assms(1,2) complex.exhaust_sel 
    by (auto simp add:order.order_iff_strict intro:complex_eqI)
  also have "... = proots_count p
           ({z. Re z \<in> {Re lb, Re ub} \<and> Im z \<in> {Im lb<..<Im ub}} \<union>
            {z. Im z \<in> {Im lb, Im ub} \<and> Re z \<in> {Re lb<..<Re ub}}) 
            + proots_count p 
            ({lb,Complex (Re ub) (Im lb), ub,Complex (Re lb) (Im ub)})"
    apply (subst proots_count_union_disjoint)
    using \<open>p\<noteq>0\<close> by auto
  also have "... = proots_count p
           ({z. Re z \<in> {Re lb, Re ub} \<and> Im z \<in> {Im lb<..<Im ub}} \<union>
            {z. Im z \<in> {Im lb, Im ub} \<and> Re z \<in> {Re lb<..<Re ub}})"
  proof -
    have "proots_count p 
            ({lb,Complex (Re ub) (Im lb), ub,Complex (Re lb) (Im ub)}) = 0"
      apply (rule proots_count_nzero)
      using not_van unfolding not_rect_vanishing_def by auto
    then show ?thesis by auto
  qed
  also have "... = proots_count p (l1 \<union> l2 \<union> l3 \<union> l4)"
    apply (rule arg_cong2[where f=proots_count])
    unfolding ll_eq by auto
  also have "... = proots_count p l1
                      + proots_count p l2
                      + proots_count p l3
                      + proots_count p l4"
    using ll_disj \<open>p\<noteq>0\<close>
    by (subst proots_count_union_disjoint;
        (simp add:Int_Un_distrib Int_Un_distrib2 )?)+
  also have "...  = proots_line p lb (Complex (Re ub) (Im lb)) 
                      +  proots_line p (Complex (Re ub) (Im lb)) ub 
                      +  proots_line p ub (Complex (Re lb) (Im ub)) 
                      +  proots_line p (Complex (Re lb) (Im ub)) lb"
    unfolding proots_line_def l1_def l2_def l3_def l4_def by simp_all
  finally show ?thesis .
qed

lemma proots_rect_border_smods:
  fixes p::"complex poly" and lb ub::complex
  assumes ab_le:"Re lb < Re ub" "Im lb < Im ub"
    and not_van:"not_rect_vanishing p lb ub"
  shows "proots_rect_border p lb ub = 
           (let p1 = pcompose p [:lb,  Complex (Re ub - Re lb) 0:];
                pR1 = map_poly Re p1; pI1 = map_poly Im p1; gc1 = gcd pR1 pI1;
                p2 = pcompose p [:Complex (Re ub) (Im lb), Complex 0 (Im ub - Im lb):];
                pR2 = map_poly Re p2; pI2 = map_poly Im p2; gc2 = gcd pR2 pI2;
                p3 = pcompose p [:ub, Complex (Re lb - Re ub) 0:];
                pR3 = map_poly Re p3; pI3 = map_poly Im p3; gc3 = gcd pR3 pI3;
                p4 = pcompose p [:Complex (Re lb) (Im ub), Complex 0 (Im lb - Im ub):];
                pR4 = map_poly Re p4; pI4 = map_poly Im p4; gc4 = gcd pR4 pI4
            in 
             nat (changes_itv_smods_ext 0 1 gc1 (pderiv gc1)
                + changes_itv_smods_ext 0 1 gc2 (pderiv gc2)
                + changes_itv_smods_ext 0 1 gc3 (pderiv gc3)
                + changes_itv_smods_ext 0 1 gc4 (pderiv gc4)
                ) )" (is "?L=?R")
proof -  
  have "proots_rect_border p lb ub =  proots_line p lb (Complex (Re ub) (Im lb)) 
                      +  proots_line p (Complex (Re ub) (Im lb)) ub 
                      +  proots_line p ub (Complex (Re lb) (Im ub)) 
                      +  proots_line p (Complex (Re lb) (Im ub)) lb"
    apply (rule proots_rect_border_eq_lines)
    by fact+
  also have "... = ?R"
  proof -
    define p1 pR1 pI1 gc1 C1 where pp1:
      "p1 = pcompose p [:lb,  Complex (Re ub - Re lb) 0:]"
      "pR1 = map_poly Re p1" 
      "pI1 = map_poly Im p1"
      "gc1 = gcd pR1 pI1"
      and 
      "C1=changes_itv_smods_ext 0 1 gc1 (pderiv gc1)"
    define p2 pR2 pI2 gc2 C2 where pp2:
      "p2 = pcompose p [:Complex (Re ub) (Im lb), Complex 0 (Im ub - Im lb):]"
      "pR2 = map_poly Re p2" 
      "pI2 = map_poly Im p2"
      "gc2 = gcd pR2 pI2"
      and 
      "C2=changes_itv_smods_ext 0 1 gc2 (pderiv gc2)"
    define p3 pR3 pI3 gc3 C3 where pp3:
      "p3 =pcompose p [:ub, Complex (Re lb - Re ub) 0:]"
      "pR3 = map_poly Re p3" 
      "pI3 = map_poly Im p3"
      "gc3 = gcd pR3 pI3"
      and 
      "C3=changes_itv_smods_ext 0 1 gc3 (pderiv gc3)"
    define p4 pR4 pI4 gc4 C4 where pp4:
      "p4 = pcompose p [:Complex (Re lb) (Im ub), Complex 0 (Im lb - Im ub):]"
      "pR4 = map_poly Re p4" 
      "pI4 = map_poly Im p4"
      "gc4 = gcd pR4 pI4"
      and 
      "C4=changes_itv_smods_ext 0 1 gc4 (pderiv gc4)"

    have  "poly gc1 0 \<noteq>0" "poly gc1 1\<noteq>0"
          "poly gc2 0 \<noteq>0" "poly gc2 1\<noteq>0"
          "poly gc3 0 \<noteq>0" "poly gc3 1\<noteq>0"
          "poly gc4 0 \<noteq>0" "poly gc4 1\<noteq>0"
      unfolding pp1 pp2 pp3 pp4 poly_gcd_0_iff
      using not_van[unfolded not_rect_vanishing_def]
      by (simp flip:Re_poly_of_real Im_poly_of_real add:poly_pcompose
              ; simp add: Complex_eq_iff zero_complex.code plus_complex.code)+

    have "proots_line p lb (Complex (Re ub) (Im lb)) = nat C1"
      apply (subst proots_line_smods)
      using not_van assms(1,2)  
      unfolding not_rect_vanishing_def C1_def pp1 Let_def
      by (simp_all add:Complex_eq_iff Complex_minus_eq)
    moreover have "proots_line p (Complex (Re ub) (Im lb)) ub = nat C2"
      apply (subst proots_line_smods)
      using not_van assms(1,2)  
      unfolding not_rect_vanishing_def C2_def pp2 Let_def
      by (simp_all add:Complex_eq_iff Complex_minus_eq)
    moreover have "proots_line p ub (Complex (Re lb) (Im ub))  = nat C3"
      apply (subst proots_line_smods)
      using not_van assms(1,2)  
      unfolding not_rect_vanishing_def C3_def pp3 Let_def
      by (simp_all add:Complex_eq_iff Complex_minus_eq)
    moreover have "proots_line p (Complex (Re lb) (Im ub)) lb = nat C4"
      apply (subst proots_line_smods)
      using not_van assms(1,2)  
      unfolding not_rect_vanishing_def C4_def pp4 Let_def
      by (simp_all add:Complex_eq_iff Complex_minus_eq)
    moreover have "C1 \<ge>0" "C2 \<ge>0" "C3 \<ge>0" "C4\<ge>0"
      unfolding C1_def C2_def C3_def C4_def
      by (rule changes_itv_smods_ext_geq_0;(fact|simp))+
    ultimately have "proots_line p lb (Complex (Re ub) (Im lb)) 
                    + proots_line p (Complex (Re ub) (Im lb)) ub 
                    + proots_line p ub (Complex (Re lb) (Im ub)) 
                    + proots_line p (Complex (Re lb) (Im ub)) lb 
                      = nat (C1+C2+C3+C4)"
      by linarith
    also have "...  = ?R"
      unfolding C1_def C2_def C3_def C4_def pp1 pp2 pp3 pp4 Let_def
      by simp
    finally show ?thesis .
  qed
  finally show ?thesis .
qed

lemma proots_rect_smods:
  assumes "Re lb < Re ub" "Im lb < Im ub" 
    and not_van:"not_rect_vanishing p lb ub"
  shows "proots_rect p lb ub = (
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
                + changes_alt_itv_smods 0 1 (pR4 div gc4) (pI4 div gc4)
                + 2*changes_itv_smods_ext 0 1 gc1 (pderiv gc1)
                + 2*changes_itv_smods_ext 0 1 gc2 (pderiv gc2)
                + 2*changes_itv_smods_ext 0 1 gc3 (pderiv gc3)
                + 2*changes_itv_smods_ext 0 1 gc4 (pderiv gc4))  div 4)
            )"
proof -
  define p1 pR1 pI1 gc1 C1 D1 where pp1:
        "p1 = pcompose p [:lb,  Complex (Re ub - Re lb) 0:]"
        "pR1 = map_poly Re p1" 
        "pI1 = map_poly Im p1"
        "gc1 = gcd pR1 pI1"
    and "C1=changes_itv_smods_ext 0 1 gc1 (pderiv gc1)"
    and "D1=changes_alt_itv_smods 0 1 (pR1 div gc1) (pI1 div gc1)"
  define p2 pR2 pI2 gc2 C2 D2 where pp2:
        "p2 = pcompose p [:Complex (Re ub) (Im lb), Complex 0 (Im ub - Im lb):]"
        "pR2 = map_poly Re p2" 
        "pI2 = map_poly Im p2"
        "gc2 = gcd pR2 pI2"
    and "C2=changes_itv_smods_ext 0 1 gc2 (pderiv gc2)"
    and "D2=changes_alt_itv_smods 0 1 (pR2 div gc2) (pI2 div gc2)"
  define p3 pR3 pI3 gc3 C3 D3 where pp3:
        "p3 =pcompose p [:ub, Complex (Re lb - Re ub) 0:]"
        "pR3 = map_poly Re p3" 
        "pI3 = map_poly Im p3"
        "gc3 = gcd pR3 pI3"
    and "C3=changes_itv_smods_ext 0 1 gc3 (pderiv gc3)"
    and "D3=changes_alt_itv_smods 0 1 (pR3 div gc3) (pI3 div gc3)"
  define p4 pR4 pI4 gc4 C4 D4 where pp4:
        "p4 = pcompose p [:Complex (Re lb) (Im ub), Complex 0 (Im lb - Im ub):]"
        "pR4 = map_poly Re p4" 
        "pI4 = map_poly Im p4"
        "gc4 = gcd pR4 pI4"
    and "C4=changes_itv_smods_ext 0 1 gc4 (pderiv gc4)"
    and "D4=changes_alt_itv_smods 0 1 (pR4 div gc4) (pI4 div gc4)"
  have "poly gc1 0 \<noteq>0" "poly gc1 1\<noteq>0"
          "poly gc2 0 \<noteq>0" "poly gc2 1\<noteq>0"
          "poly gc3 0 \<noteq>0" "poly gc3 1\<noteq>0"
          "poly gc4 0 \<noteq>0" "poly gc4 1\<noteq>0"
      unfolding pp1 pp2 pp3 pp4 poly_gcd_0_iff
      using not_van[unfolded not_rect_vanishing_def]
      by (simp flip:Re_poly_of_real Im_poly_of_real add:poly_pcompose
              ; simp add: Complex_eq_iff zero_complex.code plus_complex.code)+
  have "C1\<ge>0" "C2\<ge>0" "C3\<ge>0" "C4\<ge>0"
    unfolding C1_def C2_def C3_def C4_def
    by (rule changes_itv_smods_ext_geq_0;(fact|simp))+
  
  define CC DD where "CC=C1 + C2 + C3 + C4"
                 and "DD=D1 + D2 + D3 + D4"

  have "real (proots_rect p lb ub) = - (real (proots_rect_border p lb ub) 
                                        + cindexP_pathE p (rectpath lb ub)) / 2"
    apply (rule proots_rect_cindexP_pathE)
    by fact+
  also have "... =  -(nat CC +  DD / 2) / 2"
  proof -
    have "proots_rect_border p lb ub = nat CC" 
      apply (rule proots_rect_border_smods[
          of lb ub p,
          unfolded Let_def, 
          folded pp1 pp2 pp3 pp4,
          folded C1_def C2_def C3_def C4_def,
          folded CC_def])
      by fact+
    moreover have "cindexP_pathE p (rectpath lb ub) = (real_of_int DD) / 2"
      apply (rule cindexP_pathE_rect_smods[
          of lb ub p, 
          unfolded Let_def,
          folded pp1 pp2 pp3 pp4, 
          folded D1_def D2_def D3_def D4_def,
          folded DD_def])
      by fact+
    ultimately show ?thesis by auto
  qed
  also have "... = - (DD + 2*CC) /4"
    by (simp add: CC_def \<open>0 \<le> C1\<close> \<open>0 \<le> C2\<close> \<open>0 \<le> C3\<close> \<open>0 \<le> C4\<close>)
  finally have "real (proots_rect p lb ub) 
                  = real_of_int (- (DD + 2 * CC)) / 4" .
  then have  "proots_rect p lb ub = nat (- (DD + 2 * CC) div 4)"
    by simp
  then show ?thesis unfolding Let_def
    apply (fold pp1 pp2 pp3 pp4)
    apply (fold  C1_def C2_def C3_def C4_def D1_def D2_def D3_def D4_def)
    by (simp add:CC_def DD_def)
qed


lemma proots_rect_code[code]:
  "proots_rect p lb ub = 
          (if Re lb < Re ub \<and> Im lb < Im ub then
            if not_rect_vanishing p lb ub then
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
                + changes_alt_itv_smods 0 1 (pR4 div gc4) (pI4 div gc4)
                + 2*changes_itv_smods_ext 0 1 gc1 (pderiv gc1)
                + 2*changes_itv_smods_ext 0 1 gc2 (pderiv gc2)
                + 2*changes_itv_smods_ext 0 1 gc3 (pderiv gc3)
                + 2*changes_itv_smods_ext 0 1 gc4 (pderiv gc4))  div 4)
            )
          else Code.abort (STR ''proots_rect: the polynomial should not vanish 
                  at the four vertices for now'') (\<lambda>_. proots_rect p lb ub)
        else 0)"
proof (cases "Re lb < Re ub \<and> Im lb < Im ub \<and> not_rect_vanishing p lb ub")
  case False
  have ?thesis if "\<not> (Re lb < Re ub) \<or> \<not> ( Im lb < Im ub)"
  proof -
    have "box lb ub = {}" using that by (metis complex_box_ne_empty(2))
    then show ?thesis 
      unfolding proots_rect_def 
      using proots_count_emtpy that by fastforce
  qed
  then show ?thesis using False by auto
next
  case True
  then show ?thesis 
    apply (subst proots_rect_smods)
    unfolding Let_def by simp_all
qed

lemma proots_rect_ll_rect:
  assumes "Re lb < Re ub" "Im lb < Im ub" 
    and not_van:"not_rect_vanishing p lb ub"
  shows "proots_rect_ll p lb ub = proots_rect p lb ub 
                                    + proots_line p lb (Complex (Re ub) (Im lb))
                                    + proots_line p lb (Complex (Re lb) (Im ub))  
                                    "
proof -
  have "p\<noteq>0" 
    using not_rect_vanishing_def not_van order_root by blast

  define l1 l4 where  "l1 = open_segment lb (Complex (Re ub) (Im lb))"
                  and "l4 = open_segment lb (Complex (Re lb) (Im ub)) "
  have ll_eq:
    "l1 = {z. Im z \<in> {Im lb} \<and> Re z \<in> {Re lb<..<Re ub}}"
    "l4 = {z. Re z \<in> {Re lb} \<and> Im z \<in> {Im lb<..<Im ub}}"
    subgoal unfolding l1_def
      apply (subst open_segment_Im_equal)
      using assms unfolding open_segment_eq_real_ivl by auto
    subgoal unfolding l4_def
      apply (subst open_segment_Re_equal)
      using assms unfolding open_segment_eq_real_ivl by auto
    done
  
  have ll_disj: "l1 \<inter> l4 = {}" "box lb ub \<inter> {lb} = {}"
    "box lb ub \<inter> l1 = {}" "box lb ub \<inter> l4 = {}"
    "l1 \<inter> {lb} = {}" "l4 \<inter> {lb} = {}"
    using assms unfolding ll_eq 
    by (auto simp:in_box_complex_iff)

  have "proots_rect_ll p lb ub = proots_count p (box lb ub) 
                                    + proots_count p {lb}
                                    + proots_count p l1 
                                    + proots_count p l4"
    unfolding proots_rect_ll_def using ll_disj \<open>p\<noteq>0\<close>
    apply (fold l1_def l4_def)
    by (subst proots_count_union_disjoint
            ;(simp add:Int_Un_distrib Int_Un_distrib2 del: Un_insert_right)?)+
  also have "... = proots_rect p lb ub 
                      + proots_line p lb (Complex (Re ub) (Im lb))
                      + proots_line p lb (Complex (Re lb) (Im ub)) "
  proof -
    have "proots_count p {lb} = 0" 
      by (metis not_rect_vanishing_def not_van proots_count_nzero singleton_iff)
    then show ?thesis
      unfolding proots_rect_def l1_def l4_def proots_line_def by simp
  qed
  finally show ?thesis .
qed

lemma proots_rect_ll_smods:
  assumes "Re lb < Re ub" "Im lb < Im ub" 
    and not_van:"not_rect_vanishing p lb ub"
  shows "proots_rect_ll p lb ub = (
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
                + changes_alt_itv_smods 0 1 (pR4 div gc4) (pI4 div gc4)
                - 2*changes_itv_smods_ext 0 1 gc1 (pderiv gc1)
                + 2*changes_itv_smods_ext 0 1 gc2 (pderiv gc2)
                + 2*changes_itv_smods_ext 0 1 gc3 (pderiv gc3)
                - 2*changes_itv_smods_ext 0 1 gc4 (pderiv gc4)) div 4))"
proof -
  have "p\<noteq>0" 
    using not_rect_vanishing_def not_van order_root by blast

  define l1 l4 where  "l1 = open_segment lb (Complex (Re ub) (Im lb))"
                  and "l4 = open_segment lb (Complex (Re lb) (Im ub))"
  have l4_alt:"l4 = open_segment (Complex (Re lb) (Im ub)) lb "
    unfolding l4_def by (simp add: open_segment_commute)

  have ll_eq:
    "l1 = {z. Im z \<in> {Im lb} \<and> Re z \<in> {Re lb<..<Re ub}}"
    "l4 = {z. Re z \<in> {Re lb} \<and> Im z \<in> {Im lb<..<Im ub}}"
    subgoal unfolding l1_def
      apply (subst open_segment_Im_equal)
      using assms unfolding open_segment_eq_real_ivl by auto
    subgoal unfolding l4_def
      apply (subst open_segment_Re_equal)
      using assms unfolding open_segment_eq_real_ivl by auto
    done
  
  have ll_disj: "l1 \<inter> l4 = {}" "box lb ub \<inter> {lb} = {}"
    "box lb ub \<inter> l1 = {}" "box lb ub \<inter> l4 = {}"
    "l1 \<inter> {lb} = {}" "l4 \<inter> {lb} = {}"
    using assms unfolding ll_eq 
    by (auto simp:in_box_complex_iff)

  define p1 pR1 pI1 gc1 C1 D1 where pp1:
        "p1 = pcompose p [:lb,  Complex (Re ub - Re lb) 0:]"
        "pR1 = map_poly Re p1" 
        "pI1 = map_poly Im p1"
        "gc1 = gcd pR1 pI1"
    and "C1=changes_itv_smods_ext 0 1 gc1 (pderiv gc1)"
    and "D1=changes_alt_itv_smods 0 1 (pR1 div gc1) (pI1 div gc1)"
  define p2 pR2 pI2 gc2 C2 D2 where pp2:
        "p2 = pcompose p [:Complex (Re ub) (Im lb), Complex 0 (Im ub - Im lb):]"
        "pR2 = map_poly Re p2" 
        "pI2 = map_poly Im p2"
        "gc2 = gcd pR2 pI2"
    and "C2=changes_itv_smods_ext 0 1 gc2 (pderiv gc2)"
    and "D2=changes_alt_itv_smods 0 1 (pR2 div gc2) (pI2 div gc2)"
  define p3 pR3 pI3 gc3 C3 D3 where pp3:
        "p3 =pcompose p [:ub, Complex (Re lb - Re ub) 0:]"
        "pR3 = map_poly Re p3" 
        "pI3 = map_poly Im p3"
        "gc3 = gcd pR3 pI3"
    and "C3=changes_itv_smods_ext 0 1 gc3 (pderiv gc3)"
    and "D3=changes_alt_itv_smods 0 1 (pR3 div gc3) (pI3 div gc3)"
  define p4 pR4 pI4 gc4 C4 D4 where pp4:
        "p4 = pcompose p [:Complex (Re lb) (Im ub), Complex 0 (Im lb - Im ub):]"
        "pR4 = map_poly Re p4" 
        "pI4 = map_poly Im p4"
        "gc4 = gcd pR4 pI4"
    and "C4=changes_itv_smods_ext 0 1 gc4 (pderiv gc4)"
    and "D4=changes_alt_itv_smods 0 1 (pR4 div gc4) (pI4 div gc4)"
  have "poly gc1 0 \<noteq>0" "poly gc1 1\<noteq>0"
          "poly gc2 0 \<noteq>0" "poly gc2 1\<noteq>0"
          "poly gc3 0 \<noteq>0" "poly gc3 1\<noteq>0"
          "poly gc4 0 \<noteq>0" "poly gc4 1\<noteq>0"
      unfolding pp1 pp2 pp3 pp4 poly_gcd_0_iff
      using not_van[unfolded not_rect_vanishing_def]
      by (simp flip:Re_poly_of_real Im_poly_of_real add:poly_pcompose
              ; simp add: Complex_eq_iff zero_complex.code plus_complex.code)+
  have CC_pos:"C1\<ge>0" "C2\<ge>0" "C3\<ge>0" "C4\<ge>0"
    unfolding C1_def C2_def C3_def C4_def
    by (rule changes_itv_smods_ext_geq_0;(fact|simp))+
  
  define CC DD where "CC= C2 + C3 - C4 - C1"
                 and "DD=D1 + D2 + D3 + D4"

  define p1 p2 p3 p4 where pp:"p1=proots_line p lb (Complex (Re ub) (Im lb))" 
                              "p2 = proots_line p (Complex (Re ub) (Im lb)) ub"
                              "p3 = proots_line p ub (Complex (Re lb) (Im ub))"
                              "p4 = proots_line p (Complex (Re lb) (Im ub)) lb"
  have p4_alt:"p4 = proots_line p lb (Complex (Re lb) (Im ub))"
    unfolding pp by (simp add: proots_line_commute)
  

  have "real (proots_rect_ll p lb ub) = real (proots_rect p lb ub) + p1 + p4"
    unfolding pp by (simp add: proots_rect_ll_rect[OF assms]  proots_line_commute)
  also have "... = (p1 + p4 - real p2 - real p3 - cindexP_pathE p (rectpath lb ub)) /  2"
  proof -
    have "real (proots_rect p lb ub) = - (real (proots_rect_border p lb ub) 
                                        + cindexP_pathE p (rectpath lb ub)) / 2"
      apply (rule proots_rect_cindexP_pathE)
      by fact+
    also have "... = - (p1 + p2 + p3 + p4 + cindexP_pathE p (rectpath lb ub)) / 2"
      using proots_rect_border_eq_lines[OF assms,folded pp] by simp
    finally have "real (proots_rect p lb ub) =
                      - (real (p1 + p2 + p3 + p4) 
                          + cindexP_pathE p (rectpath lb ub)) / 2" .
    then show ?thesis by auto
  qed
  also have "... = (nat C1 + nat C4 - real (nat C2) - real (nat C3)
                       - ((real_of_int DD) / 2)) /  2"
  proof -
    have "p1 = nat C1" "p2 = nat C2" "p3 = nat C3" "p4 = nat C4"
      using not_van[unfolded not_rect_vanishing_def]  assms(1,2)
      unfolding pp C1_def pp1 C2_def pp2 C3_def pp3 C4_def pp4
      by (subst proots_line_smods
          ;simp_all add:Complex_eq_iff Let_def Complex_minus_eq)+
    moreover have "cindexP_pathE p (rectpath lb ub) = (real_of_int DD) / 2"
      apply (rule cindexP_pathE_rect_smods[
          of lb ub p, 
          unfolded Let_def,
          folded pp1 pp2 pp3 pp4, 
          folded D1_def D2_def D3_def D4_def,
          folded DD_def])
      by fact+
    ultimately show ?thesis by presburger
  qed
  also have "... = -(DD + 2*CC) / 4"
    unfolding CC_def using CC_pos by (auto simp add:divide_simps algebra_simps)
  finally have "real (proots_rect_ll p lb ub) 
                        = real_of_int (- (DD + 2 * CC)) / 4" .
  then have "proots_rect_ll p lb ub
                        = nat (- (DD + 2 * CC) div 4)"
    by simp
  then show ?thesis
    unfolding Let_def
    apply (fold pp1 pp2 pp3 pp4)
    apply (fold  C1_def C2_def C3_def C4_def D1_def D2_def D3_def D4_def)
    by (simp add:CC_def DD_def)
qed

lemma proots_rect_ll_code[code]:
  "proots_rect_ll p lb ub = 
          (if Re lb < Re ub \<and> Im lb < Im ub then
            if not_rect_vanishing p lb ub then
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
                + changes_alt_itv_smods 0 1 (pR4 div gc4) (pI4 div gc4)
                - 2*changes_itv_smods_ext 0 1 gc1 (pderiv gc1)
                + 2*changes_itv_smods_ext 0 1 gc2 (pderiv gc2)
                + 2*changes_itv_smods_ext 0 1 gc3 (pderiv gc3)
                - 2*changes_itv_smods_ext 0 1 gc4 (pderiv gc4))  div 4)
            )
          else Code.abort (STR ''proots_rect_ll: the polynomial should not vanish 
                  at the four vertices for now'') (\<lambda>_. proots_rect_ll p lb ub)
        else Code.abort (STR ''proots_rect_ll: the box is improper'') 
                (\<lambda>_. proots_rect_ll p lb ub))"
proof (cases "Re lb < Re ub \<and> Im lb < Im ub \<and> not_rect_vanishing p lb ub")
  case False
  then show ?thesis using False by auto
next
  case True
  then show ?thesis 
    apply (subst proots_rect_ll_smods)
    unfolding Let_def by simp_all
qed

end