(* Title:      Kleene algebra with tests
   Author:     Alasdair Armstrong, Victor B. F. Gomes, Georg Struth
   Maintainer: Georg Struth <g.struth at sheffield.ac.uk>
*)

section {* Transformation Theorem for while Loops *}

theory FolkTheorem
  imports Conway KAT DRAT
begin

text {*
  We prove Kozen's transformation theorem for while loops \cite{Kozen97} in a weak setting that unifies
  previous proofs in Kleene algebra with tests, demonic refinement algebras and a variant of probabilistic
  Kleene algebra.
*}

context pre_conway
begin

abbreviation preservation :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "preserves" 60) where
  "x preserves p \<equiv> test p \<and> p\<cdot>x\<cdot>p = p\<cdot>x \<and> !p\<cdot>x\<cdot>!p = !p\<cdot>x"

lemma preserves_test_closed: "\<lbrakk>test p; x preserves q\<rbrakk> \<Longrightarrow> p\<cdot>x preserves q"
  apply (auto, metis mult.assoc test_mult_comm_var)
  by (metis mult.assoc test_comp_closed_var test_mult_comm_var)

lemma conditional_helper1:
  assumes  "test r1" 
          "x1 preserves q" "y1 preserves q"
          "x2 preserves q" "y2 preserves q"
  shows "p\<cdot>q\<cdot>x1\<cdot>(q\<cdot>r1\<cdot>y1 + !q\<cdot>r2\<cdot>y2)\<^sup>\<dagger>\<cdot>(q\<cdot>!r1 + !q\<cdot>!r2) = p\<cdot>q\<cdot>x1\<cdot>(r1\<cdot>y1)\<^sup>\<dagger>\<cdot>!r1"
proof - 
  let ?B = "q\<cdot>!r1 + !q\<cdot>!r2"
  have pres: "q\<cdot>(r1\<cdot>y1) = q \<cdot> (r1\<cdot>y1) \<cdot>q"
    by (metis assms preserves_test_closed)
  hence "q\<cdot>(q\<cdot>r1\<cdot>y1 + !q\<cdot>r2\<cdot>y2)\<^sup>\<dagger> = (q\<cdot>r1\<cdot>y1)\<^sup>\<dagger>\<cdot>q"
    by (metis assms(2-) test_preserve1 dagger_slide mult.assoc)
  hence "p\<cdot>q\<cdot>x1\<cdot>(q\<cdot>r1\<cdot>y1 + !q\<cdot>r2\<cdot>y2)\<^sup>\<dagger>\<cdot>?B = p\<cdot>q\<cdot>x1\<cdot>(q\<cdot>r1\<cdot>y1)\<^sup>\<dagger>\<cdot>q\<cdot>?B"
    by (metis assms(2) mult.assoc)
  also have "... = p\<cdot>q\<cdot>x1\<cdot>(q\<cdot>r1\<cdot>y1)\<^sup>\<dagger>\<cdot>q\<cdot>!r1"
    by (metis assms(5) mult.assoc weak_distrib_left_var test_comp_mult annil add_zeror test_mult_idem_var)
  also have "... = p\<cdot>q\<cdot>x1\<cdot>(r1\<cdot>y1)\<^sup>\<dagger>\<cdot>!r1"
    by (metis pres assms(2) mult.assoc test_preserve)
  finally show ?thesis .
qed 

lemma conditional_helper2:
  assumes  "test r2" 
          "x1 preserves q" "y1 preserves q"
          "x2 preserves q" "y2 preserves q"
  shows "p\<cdot>!q\<cdot>x2\<cdot>(q\<cdot>r1\<cdot>y1 + !q\<cdot>r2\<cdot>y2)\<^sup>\<dagger>\<cdot>(q\<cdot>!r1 + !q\<cdot>!r2) = p\<cdot>!q\<cdot>x2\<cdot>(r2\<cdot>y2)\<^sup>\<dagger>\<cdot>!r2"
proof - 
   let ?B = "q\<cdot>!r1 + !q\<cdot>!r2"
  have pres: "!q\<cdot>(r2\<cdot>y2) = !q \<cdot> (r2\<cdot>y2) \<cdot>!q"
    by (metis assms preserves_test_closed)
  hence "!q\<cdot>(q\<cdot>r1\<cdot>y1 + !q\<cdot>r2\<cdot>y2)\<^sup>\<dagger> = (!q\<cdot>r2\<cdot>y2)\<^sup>\<dagger>\<cdot>!q"
    by (metis assms(2-) test_preserve1[of "!q" "r2\<cdot>y2" "r1\<cdot>y1"] add.commute mult.assoc test_comp_closed_var test_double_comp_var)
  hence "p\<cdot>!q\<cdot>x2\<cdot>(q\<cdot>r1\<cdot>y1 + !q\<cdot>r2\<cdot>y2)\<^sup>\<dagger>\<cdot>?B = p\<cdot>!q\<cdot>x2\<cdot>(!q\<cdot>r2\<cdot>y2)\<^sup>\<dagger>\<cdot>!q\<cdot>?B"
    by (metis assms(4) mult.assoc)
  also have "... = p\<cdot>!q\<cdot>x2\<cdot>(!q\<cdot>r2\<cdot>y2)\<^sup>\<dagger>\<cdot>!q\<cdot>!r2"
    by (metis assms(5) mult.assoc test_comp_closed_var weak_distrib_left_var test_comp_mult2 test_mult_idem_var add_zerol annil)
  also have "... = p\<cdot>!q\<cdot>x2\<cdot>(r2\<cdot>y2)\<^sup>\<dagger>\<cdot>!r2"
    by (metis assms(4) mult.assoc pres test_comp_closed_var test_preserve)
  finally show ?thesis .
qed 

lemma cond_distr: 
  assumes "test p" "test q" "test r"
  shows "(p\<cdot>q + !p\<cdot>r)\<cdot>(p\<cdot>x + !p\<cdot>y) = p\<cdot>q\<cdot>x + !p\<cdot>r\<cdot>y" 
proof -
  have "(p\<cdot>q + !p\<cdot>r)\<cdot>(p\<cdot>x + !p\<cdot>y) = p\<cdot>q\<cdot>p\<cdot>x + p\<cdot>q\<cdot>!p\<cdot>y + !p\<cdot>r\<cdot>p\<cdot>x + !p\<cdot>r\<cdot>!p\<cdot>y"
    by (metis assms distrib_right' mult.assoc weak_distrib_left_var add.assoc test_comp_closed_var)
  thus ?thesis
    by (metis assms mult.assoc test2 test3 test4 annil add_zeror test_comp_closed_var)
qed

theorem conditional: 
  assumes "test p" "test r1" "test r2"
          "x1 preserves q" "y1 preserves q"
          "x2 preserves q" "y2 preserves q"
  shows "(p\<cdot>q + !p\<cdot>!q)\<cdot>(p\<cdot>x1\<cdot>(r1\<cdot>y1)\<^sup>\<dagger>\<cdot>!r1 + !p\<cdot>x2\<cdot>(r2\<cdot>y2)\<^sup>\<dagger>\<cdot>!r2) = 
      (p\<cdot>q + !p\<cdot>!q)\<cdot>(q\<cdot>x1 + !q\<cdot>x2)\<cdot>((q\<cdot>r1 + !q\<cdot>r2)\<cdot>(q\<cdot>y1 + !q\<cdot>y2))\<^sup>\<dagger>\<cdot>!(q\<cdot>r1 + !q\<cdot>r2)"
proof - 
  have "p\<cdot>q\<cdot>(x1\<cdot>(r1\<cdot>y1)\<^sup>\<dagger>\<cdot>!r1) = p\<cdot>q\<cdot>x1\<cdot>(q\<cdot>r1\<cdot>y1 + !q\<cdot>r2\<cdot>y2)\<^sup>\<dagger>\<cdot>(q\<cdot>!r1 + !q\<cdot>!r2)" and "!p\<cdot>!q\<cdot>(x2\<cdot>(r2\<cdot>y2)\<^sup>\<dagger>\<cdot>!r2) = !p\<cdot>!q\<cdot>x2\<cdot>(q\<cdot>r1\<cdot>y1 + !q\<cdot>r2\<cdot>y2)\<^sup>\<dagger>\<cdot>(q\<cdot>!r1 + !q\<cdot>!r2)" 
    apply (metis assms(2,4-) conditional_helper1[of r1 q x1 y1 x2 y2 p] mult.assoc)
    by (metis assms(3-) conditional_helper2[of r2 q x1 y1 x2 y2 "!p"] mult.assoc)   
  moreover have "(p\<cdot>q + !p\<cdot>!q)\<cdot>(p\<cdot>x1\<cdot>(r1\<cdot>y1)\<^sup>\<dagger>\<cdot>!r1 + !p\<cdot>x2\<cdot>(r2\<cdot>y2)\<^sup>\<dagger>\<cdot>!r2) = p\<cdot>q\<cdot>(x1\<cdot>(r1\<cdot>y1)\<^sup>\<dagger>\<cdot>!r1) + !p\<cdot>!q\<cdot>(x2\<cdot>(r2\<cdot>y2)\<^sup>\<dagger>\<cdot>!r2)"
    by (metis assms(1,4-) cond_distr mult.assoc test_def)
  moreover have "... = (p\<cdot>q\<cdot>x1 + !p\<cdot>!q\<cdot>x2)\<cdot>(q\<cdot>r1\<cdot>y1 + !q\<cdot>r2\<cdot>y2)\<^sup>\<dagger>\<cdot>(q\<cdot>!r1 + !q\<cdot>!r2)"
    by (metis calculation(1) calculation(2) distrib_right')
  moreover have "... = (q\<cdot>p\<cdot>x1 + !q\<cdot>!p\<cdot>x2)\<cdot>(q\<cdot>r1\<cdot>y1 + !q\<cdot>r2\<cdot>y2)\<^sup>\<dagger>\<cdot>(q\<cdot>!r1 + !q\<cdot>!r2)"
    by (metis assms(1) assms(5) test_comp_closed_var test_mult_comm_var)
  moreover have "... = (q\<cdot>p + !q\<cdot>!p)\<cdot>(q\<cdot>x1 + !q\<cdot>x2)\<cdot>((q\<cdot>r1 + !q\<cdot>r2)\<cdot>(q\<cdot>y1 + !q\<cdot>y2))\<^sup>\<dagger>\<cdot>!(q\<cdot>r1 + !q\<cdot>r2)"
    by (metis assms(1-3,5) cond_distr de_morgan_var2 test_comp_closed_var)
  ultimately show ?thesis 
    by (metis assms(1,5) test_comp_closed_var test_mult_comm_var)
qed

theorem nested_loops: 
  assumes "test p" "test q"
  shows "(p\<cdot>x\<cdot>(q\<cdot>y)\<^sup>\<dagger>\<cdot>!q)\<^sup>\<dagger>\<cdot>!p = p\<cdot>x\<cdot>((p + q)\<cdot>(q\<cdot>y + !q\<cdot>x))\<^sup>\<dagger>\<cdot>!(p + q) + !p"
proof -
  have "p\<cdot>x\<cdot>((p + q)\<cdot>(q\<cdot>y + !q\<cdot>x))\<^sup>\<dagger>\<cdot>!(p + q) + !p = p\<cdot>x\<cdot>(q\<cdot>y)\<^sup>\<dagger>\<cdot>(!q\<cdot>p\<cdot>x\<cdot>(q\<cdot>y)\<^sup>\<dagger>)\<^sup>\<dagger>\<cdot>!p\<cdot>!q + !p"
    by (metis assms test_distrib mult.assoc de_morgan2 dagger_denest2)
  thus ?thesis
    by (metis assms mult.assoc test_comp_closed_var test_mult_comm_var add.commute dagger_slide dagger_unfoldl_distr)
qed

lemma postcomputation:
  assumes "y preserves p"
  shows "(p\<cdot>x)\<^sup>\<dagger>\<cdot>!p\<cdot>y = !p\<cdot>y + p\<cdot>(p\<cdot>x\<cdot>(!p\<cdot>y + p))\<^sup>\<dagger>\<cdot>!p"
proof -
  have "p\<cdot>(p\<cdot>x\<cdot>(!p\<cdot>y + p))\<^sup>\<dagger>\<cdot>!p = p\<cdot>(1 + p\<cdot>x\<cdot>((!p\<cdot>y + p)\<cdot>p\<cdot>x)\<^sup>\<dagger>\<cdot>(!p\<cdot>y + p))\<cdot>!p"
    by (metis dagger_prod_unfold mult.assoc)
  also have "... = (p + p\<cdot>p\<cdot>x\<cdot>((!p\<cdot>y + p)\<cdot>p\<cdot>x)\<^sup>\<dagger>\<cdot>(!p\<cdot>y + p))\<cdot>!p"
    by (metis assms mult.assoc weak_distrib_left_var distrib_right' mult_1_left)
  also have "... = p\<cdot>!p + p\<cdot>x\<cdot>(!p\<cdot>y\<cdot>p\<cdot>x + p\<cdot>p\<cdot>x)\<^sup>\<dagger>\<cdot>(!p\<cdot>y + p)\<cdot>!p"
    by (metis assms mult.assoc distrib_right' test_mult_idem_var)
  also have "... = p\<cdot>!p + p\<cdot>x\<cdot>(!p\<cdot>y\<cdot>p\<cdot>x + p\<cdot>p\<cdot>x)\<^sup>\<dagger>\<cdot>(!p\<cdot>y\<cdot>!p + p\<cdot>!p)"
    by (metis distrib_right' mult.assoc)
  also have "... = p\<cdot>x\<cdot>(!p\<cdot>y\<cdot>!p\<cdot>p\<cdot>x + p\<cdot>x)\<^sup>\<dagger>\<cdot>(!p\<cdot>y)"
    by (metis assms test_comp_mult test_mult_idem_var add_zerol add_zeror)
  also have "... = p\<cdot>x\<cdot>(!p\<cdot>y\<cdot>0 + p\<cdot>x)\<^sup>\<dagger>\<cdot>!p\<cdot>y"
    by (metis assms mult.assoc test_double_comp_var test_mult_comp annil)
  moreover have "... = p \<cdot>x \<cdot>(p \<cdot>x)\<^sup>\<dagger>\<cdot>(!p \<cdot> y \<cdot> 0 \<cdot>(p \<cdot>x)\<^sup>\<dagger>)\<^sup>\<dagger>\<cdot>!p \<cdot> y"
    by (metis mult.assoc add.commute dagger_denest2)
  moreover have "... = p \<cdot>x \<cdot>(p \<cdot>x)\<^sup>\<dagger>\<cdot>!p \<cdot> y \<cdot> (0\<cdot>!p \<cdot> y)\<^sup>\<dagger>"
    by (metis annil dagger_slide mult.assoc)
  ultimately have "p\<cdot>(p\<cdot>x\<cdot>(!p\<cdot>y + p))\<^sup>\<dagger>\<cdot>!p = p \<cdot>x \<cdot>(p \<cdot>x)\<^sup>\<dagger>\<cdot>!p \<cdot> y"
    by (metis zero_dagger annil mult_1_right)
  thus "(p\<cdot>x)\<^sup>\<dagger>\<cdot>!p\<cdot>y = !p\<cdot>y + p\<cdot>(p\<cdot>x\<cdot>(!p\<cdot>y + p))\<^sup>\<dagger>\<cdot>!p"
    by (metis dagger_unfoldl_distr mult.assoc)
qed                      

lemma composition_helper: 
  assumes "test g" "test h" "g\<cdot>y = y\<cdot>g"
  shows "g\<cdot>(h\<cdot>y)\<^sup>\<dagger>\<cdot>!h\<cdot>g = g\<cdot>(h\<cdot>y)\<^sup>\<dagger>\<cdot>!h"
  apply (subgoal_tac "g\<cdot>(h\<cdot>y)\<^sup>\<dagger>\<cdot>!h \<le> (h\<cdot>y)\<^sup>\<dagger>\<cdot>!h\<cdot>g")
  apply (metis assms(1) test_eq3 mult.assoc)
  by (metis assms mult.assoc test_mult_comm_var order_refl dagger_simr mult_isor test_comp_closed_var)

theorem composition:
  assumes "test g" "test h" "g\<cdot>y = y\<cdot>g" "!g\<cdot>y = y\<cdot>!g"
  shows "(g\<cdot>x)\<^sup>\<dagger>\<cdot>!g\<cdot>(h\<cdot>y)\<^sup>\<dagger>\<cdot>!h = !g\<cdot>(h\<cdot>y)\<^sup>\<dagger>\<cdot>!h + g\<cdot>(g\<cdot>x\<cdot>(!g\<cdot>(h\<cdot>y)\<^sup>\<dagger>\<cdot>!h + g))\<^sup>\<dagger>\<cdot>!g"
  apply (subgoal_tac "(h\<cdot>y)\<^sup>\<dagger>\<cdot>!h preserves g")
  by (metis postcomputation mult.assoc, metis assms composition_helper test_comp_closed_var mult.assoc)  
  
end

text {*
  Kleene algebras with tests form pre-Conway algebras, therefore the transformation theorem is valid for KAT as well.
*}
sublocale  kat \<subseteq> pre_conway star
  apply (default, simp_all only: star_prod_unfold star_sim2)
  by (metis star_denest_var star_slide)

text {*
  Demonic refinement algebras form pre-Conway algebras, therefore the transformation theorem is valid for DRA as well.
*}
sublocale  dra_tests \<subseteq> pre_conway strong_iteration
  apply (default, metis iteration_denest iteration_slide)
  by (metis iteration_prod_unfold, metis iteration_sim)
  
text {*
  We do not currently consider an expansion of probabilistic Kleene algebra.
*}
end
