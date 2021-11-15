(*
    Author:     Wenda Li <wl302@cam.ac.uk / liwenda1990@hotmail.com>
*)
theory Count_Circle imports 
  Count_Half_Plane
begin

subsection \<open>Polynomial roots within a circle (open ball)\<close>

\<comment> \<open>Roots counted WITH multiplicity\<close>
definition proots_ball::"complex poly \<Rightarrow> complex \<Rightarrow> real \<Rightarrow> nat" where
  "proots_ball p z0 r = proots_count p (ball z0 r)" 

\<comment> \<open>Roots counted WITHOUT multiplicity\<close>
definition proots_ball_card ::"complex poly \<Rightarrow> complex \<Rightarrow> real \<Rightarrow> nat" where
  "proots_ball_card p z0 r = card (proots_within p (ball z0 r))"

lemma proots_ball_code1[code]:
  "proots_ball p z0 r = ( if r \<le> 0 then 
                              0
                          else if p\<noteq>0 then
                              proots_upper (fcompose (p \<circ>\<^sub>p [:z0, of_real r:]) [:\<i>,-1:] [:\<i>,1:]) 
                          else 
                              Code.abort (STR ''proots_ball fails when p=0.'') 
                                (\<lambda>_. proots_ball p z0 r)
                        )" 
proof (cases "p=0 \<or> r\<le>0")
  case False
  have "proots_ball p z0 r = proots_count (p \<circ>\<^sub>p [:z0, of_real r:]) (ball 0 1)"
    unfolding proots_ball_def
    apply (rule proots_uball_eq[THEN arg_cong])
    using False by auto
  also have "... = proots_upper (fcompose (p \<circ>\<^sub>p [:z0, of_real r:]) [:\<i>,-1:] [:\<i>,1:])"
    unfolding proots_upper_def
    apply (rule proots_ball_plane_eq[THEN arg_cong])
    using False pcompose_eq_0[of p "[:z0, of_real r:]"] 
    by (simp add: pcompose_eq_0)
  finally show ?thesis using False by auto
qed (auto simp:proots_ball_def ball_empty)

lemma proots_ball_card_code1[code]:
  "proots_ball_card p z0 r = 
                ( if r \<le> 0 \<or> p=0 then 
                      0
                 else 
                    proots_upper_card (fcompose (p \<circ>\<^sub>p [:z0, of_real r:]) [:\<i>,-1:] [:\<i>,1:]) 
                        )" 
proof (cases "p=0 \<or> r\<le>0")
  case True
  moreover have ?thesis when "r\<le>0"
  proof -
    have "proots_within p (ball z0 r) = {}" 
      by (simp add: ball_empty that)
    then show ?thesis unfolding proots_ball_card_def using that by auto
  qed
  moreover have ?thesis when "r>0" "p=0"
    unfolding proots_ball_card_def using that infinite_ball[of r z0]
    by auto
  ultimately show ?thesis by argo
next
  case False
  then have "p\<noteq>0" "r>0" by auto
  
  have "proots_ball_card p z0 r = card (proots_within (p \<circ>\<^sub>p [:z0, of_real r:]) (ball 0 1))"
    unfolding proots_ball_card_def
    by (rule proots_card_uball_eq[OF \<open>r>0\<close>, THEN arg_cong])
  also have "... = proots_upper_card (fcompose (p \<circ>\<^sub>p [:z0, of_real r:]) [:\<i>,-1:] [:\<i>,1:])"
    unfolding proots_upper_card_def
    apply (rule proots_card_ball_plane_eq[THEN arg_cong])
    using False pcompose_eq_0[of p "[:z0, of_real r:]"] by (simp add: pcompose_eq_0)
  finally show ?thesis using False by auto
qed

subsection \<open>Polynomial roots on a circle (sphere)\<close>

\<comment> \<open>Roots counted WITH multiplicity\<close>
definition proots_sphere::"complex poly \<Rightarrow> complex \<Rightarrow> real \<Rightarrow> nat" where
  "proots_sphere p z0 r = proots_count p (sphere z0 r)" 

\<comment> \<open>Roots counted WITHOUT multiplicity\<close>
definition proots_sphere_card ::"complex poly \<Rightarrow> complex \<Rightarrow> real \<Rightarrow> nat" where
  "proots_sphere_card p z0 r = card (proots_within p (sphere z0 r))"

lemma proots_sphere_card_code1[code]:
  "proots_sphere_card p z0 r = 
                ( if r=0 then 
                      (if poly p z0=0 then 1 else 0) 
                  else if r < 0 \<or> p=0 then 
                      0
                  else 
                    (if poly p (z0-r) =0 then 1 else 0) +
                    proots_unbounded_line_card (fcompose (p \<circ>\<^sub>p [:z0, of_real r:]) [:\<i>,-1:] [:\<i>,1:])
                      0 1 
                )" 
proof -
  have ?thesis when "r=0"
  proof -
    have "proots_within p {z0} = (if poly p z0 = 0 then {z0} else {})"
      by auto
    then show ?thesis unfolding proots_sphere_card_def using that by simp
  qed
  moreover have ?thesis when "r\<noteq>0" "r < 0 \<or> p=0"
  proof -
    have ?thesis when "r<0"
    proof -
      have "proots_within p (sphere z0 r) = {}" 
        by (auto simp add: ball_empty that)
      then show ?thesis unfolding proots_sphere_card_def using that by auto
    qed
    moreover have ?thesis when "r>0" "p=0"
      unfolding proots_sphere_card_def using that infinite_sphere[of r z0]
      by auto
    ultimately show ?thesis using that by argo
  qed
  moreover have ?thesis when "r>0" "p\<noteq>0"
  proof -
    define pp where "pp = p \<circ>\<^sub>p [:z0, of_real r:]" 
    define ppp where "ppp=fcompose pp [:\<i>, - 1:] [:\<i>, 1:]"

    have "pp\<noteq>0" unfolding pp_def using that pcompose_eq_0 
      by force

    have "proots_sphere_card p z0 r = card (proots_within pp (sphere 0 1))"
      unfolding proots_sphere_card_def pp_def
      by (rule proots_card_usphere_eq[OF \<open>r>0\<close>, THEN arg_cong])
    also have "... = card (proots_within pp {-1} \<union> proots_within pp (sphere 0 1 - {-1}))"
      by (simp add: insert_absorb proots_within_union)
    also have "... = card (proots_within pp {-1}) + card (proots_within pp (sphere 0 1 - {-1}))"
      apply (rule card_Un_disjoint)
      using \<open>pp\<noteq>0\<close> by auto
    also have "... = card (proots_within pp {-1}) + card (proots_within ppp {x. 0 = Im x})"
      using proots_card_sphere_axis_eq[OF \<open>pp\<noteq>0\<close>,folded ppp_def] by simp
    also have "... = (if poly p (z0-r) =0 then 1 else 0) + proots_unbounded_line_card ppp 0 1"
    proof -
      have "proots_within pp {-1} = (if poly p (z0-r) =0 then {-1} else {})"
        unfolding pp_def by (auto simp:poly_pcompose)
      then have "card (proots_within pp {-1}) = (if poly p (z0-r) =0 then 1 else 0)"
        by auto
      moreover have "{x. Im x = 0} = unbounded_line 0 1" 
        unfolding unbounded_line_def 
        apply auto
        by (metis complex_is_Real_iff of_real_Re of_real_def)
      then have "card (proots_within ppp {x. 0 = Im x})
                        = proots_unbounded_line_card ppp 0 1"
        unfolding proots_unbounded_line_card_def by simp
      ultimately show ?thesis by auto
    qed
    finally show ?thesis 
      apply (fold pp_def,fold ppp_def)
      using that by auto
  qed
  ultimately show ?thesis by auto
qed

subsection \<open>Polynomial roots on a closed ball\<close>

\<comment> \<open>Roots counted WITH multiplicity\<close>
definition proots_cball::"complex poly \<Rightarrow> complex \<Rightarrow> real \<Rightarrow> nat" where
  "proots_cball p z0 r = proots_count p (cball z0 r)" 

\<comment> \<open>Roots counted WITHOUT multiplicity\<close>
definition proots_cball_card ::"complex poly \<Rightarrow> complex \<Rightarrow> real \<Rightarrow> nat" where
  "proots_cball_card p z0 r = card (proots_within p (cball z0 r))"

(*FIXME: this surely can be optimised/refined.*)
lemma proots_cball_card_code1[code]:
  "proots_cball_card p z0 r = 
                ( if r=0 then 
                      (if poly p z0=0 then 1 else 0) 
                  else if r < 0 \<or> p=0 then 
                      0
                  else 
                    ( let pp=fcompose (p \<circ>\<^sub>p [:z0, of_real r:]) [:\<i>,-1:] [:\<i>,1:] 
                      in 
                        (if poly p (z0-r) =0 then 1 else 0) 
                        + proots_unbounded_line_card pp 0 1 
                        + proots_upper_card pp
                    )
                )"
proof -
  have ?thesis when "r=0"
  proof -
    have "proots_within p {z0} = (if poly p z0 = 0 then {z0} else {})"
      by auto
    then show ?thesis unfolding proots_cball_card_def using that by simp
  qed
  moreover have ?thesis when "r\<noteq>0" "r < 0 \<or> p=0"
  proof -
    have ?thesis when "r<0"
    proof -
      have "proots_within p (cball z0 r) = {}" 
        by (auto simp add: ball_empty that)
      then show ?thesis unfolding proots_cball_card_def using that by auto
    qed
    moreover have ?thesis when "r>0" "p=0"
      unfolding proots_cball_card_def using that infinite_cball[of r z0]
      by auto
    ultimately show ?thesis using that by argo
  qed
  moreover have ?thesis when "p\<noteq>0" "r>0"
  proof -
    define pp where "pp=fcompose (p \<circ>\<^sub>p [:z0, of_real r:]) [:\<i>,-1:] [:\<i>,1:]"

    have "proots_cball_card p z0 r = card (proots_within p (sphere z0 r) 
                                        \<union> proots_within p (ball z0 r))" 
      unfolding proots_cball_card_def 
      apply (simp add:proots_within_union)
      by (metis Diff_partition cball_diff_sphere sphere_cball)
    also have "... = card (proots_within p (sphere z0 r)) + card (proots_within p (ball z0 r))"
      apply (rule card_Un_disjoint)
      using \<open>p\<noteq>0\<close> by auto
    also have "... = (if poly p (z0-r) =0 then 1 else 0) + proots_unbounded_line_card pp 0 1 
                        + proots_upper_card pp"
      using proots_sphere_card_code1[of p z0 r,folded pp_def,unfolded proots_sphere_card_def] 
        proots_ball_card_code1[of p z0 r,folded pp_def,unfolded proots_ball_card_def]
        that
      by simp
    finally show ?thesis 
      apply (fold pp_def)
      using that by auto
  qed
  ultimately show ?thesis by auto
qed

end