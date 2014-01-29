(* Title:      Kleene algebra with tests
   Author:     Alasdair Armstrong, Victor B. F. Gomes, Georg Struth
   Maintainer: Georg Struth <g.struth at sheffield.ac.uk>
*)

header {* Kleene Algebra with Tests *}

theory KAT
  imports "../DRA_Base" Test_Dioids
begin

text {*
  First, we study left Kleene algebras with tests which also have only a left zero.
  These structures can be expanded to demonic refinement algebras.
*}

class left_kat_zerol =  left_kleene_algebra_zerol + dioid_tests_zerol
begin

lemma star_test_export1: "test p \<Longrightarrow> (p\<cdot>x)\<^sup>\<star>\<cdot>p \<le> p\<cdot>x\<^sup>\<star>"
  by (metis mult_isol mult_oner star_iso star_slide test_eq3 test_one_var)

lemma star_test_export2: "test p \<Longrightarrow> (p\<cdot>x)\<^sup>\<star>\<cdot>p \<le> x\<^sup>\<star>\<cdot>p"
  by (metis mult_isor star2 star_denest star_invol star_iso star_slide star_subdist_var_2 star_subid test_ub_var)

lemma star_test_export_left: "\<lbrakk>test p; x\<cdot>p \<le> p\<cdot>x\<rbrakk> \<Longrightarrow> x\<^sup>\<star>\<cdot>p = p\<cdot>(x\<cdot>p)\<^sup>\<star>"
  apply (rule antisym)
  apply (metis mult_assoc mult_isol_var star_sim1 test_double_comp_var test_mult_idem_var test_mult_lb1)
  by (metis star_slide star_test_export2)

lemma star_test_export_right: "\<lbrakk>test p; x\<cdot>p \<le> p\<cdot>x\<rbrakk> \<Longrightarrow> x\<^sup>\<star>\<cdot>p = (p\<cdot>x)\<^sup>\<star>\<cdot>p"
  by (metis star_slide star_test_export_left)

lemma star_test_export2_left: "\<lbrakk>test p; p\<cdot>x = x\<cdot>p\<rbrakk> \<Longrightarrow> x\<^sup>\<star>\<cdot>p = p\<cdot>(p\<cdot>x)\<^sup>\<star>"
  by (metis order_refl star_test_export_left)

lemma star_test_export2_right: "\<lbrakk>test p; p\<cdot>x = x\<cdot>p\<rbrakk> \<Longrightarrow> x\<^sup>\<star>\<cdot>p = (x\<cdot>p)\<^sup>\<star>\<cdot>p"
  by (metis star_slide star_test_export2_left)

lemma star_test_folk: "\<lbrakk>test p; p\<cdot>x = x\<cdot>p; p\<cdot>y = y\<cdot>p\<rbrakk> \<Longrightarrow> (p\<cdot>x + !p\<cdot>y)\<^sup>\<star>\<cdot>p = p\<cdot>(p\<cdot>x)\<^sup>\<star>"
proof -
  assume assms: "test p" "p\<cdot>x = x\<cdot>p" "p\<cdot>y = y\<cdot>p"
  hence "(p\<cdot>x + !p\<cdot>y)\<^sup>\<star>\<cdot>p = p\<cdot>(p\<cdot>p\<cdot>x + p\<cdot>!p\<cdot>y)\<^sup>\<star>"
    by (metis comm_add_var test_comp_closed_var star_test_export2_left distrib_left mult_assoc)
  thus ?thesis
    by (metis assms(1) test_double_comp_var test_mult_comp test_mult_idem_var add_zeror annil)
qed

end

class kat_zerol = kleene_algebra_zerol + dioid_tests_zerol
begin

subclass left_kat_zerol
  by (unfold_locales)

lemma star_sim_right: "\<lbrakk>test p; p\<cdot>x = x\<cdot>p\<rbrakk> \<Longrightarrow> p\<cdot>x\<^sup>\<star> = (p\<cdot>x)\<^sup>\<star>\<cdot>p"
  by (metis mult_assoc star_sim3 test_mult_idem_var)

lemma star_sim_left: "\<lbrakk>test p; p\<cdot>x = x\<cdot>p\<rbrakk> \<Longrightarrow> p\<cdot>x\<^sup>\<star> = p\<cdot>(x\<cdot>p)\<^sup>\<star>"
  by (metis star_sim_right star_slide)

lemma comm_star: "\<lbrakk>test p; p\<cdot>x = x\<cdot>p; p\<cdot>y = y\<cdot>p\<rbrakk> \<Longrightarrow> p\<cdot>x\<cdot>(p\<cdot>y)\<^sup>\<star> = p\<cdot>x\<cdot>y\<^sup>\<star>"
  by (metis star_sim_right mult_assoc star_slide)

lemma star_sim_right_var: "\<lbrakk>test p; p\<cdot>x = x\<cdot>p\<rbrakk> \<Longrightarrow> x\<^sup>\<star>\<cdot>p = p\<cdot>(x\<cdot>p)\<^sup>\<star>"
  by (metis mult_assoc star_sim3 test_mult_idem_var)

lemma star_folk_var[simp]: "\<lbrakk>test p; p\<cdot>x = x\<cdot>p; p\<cdot>y = y\<cdot>p\<rbrakk> \<Longrightarrow> (p\<cdot>x + !p\<cdot>y)\<^sup>\<star>\<cdot>p = p\<cdot>x\<^sup>\<star>"
  by (metis star_test_folk comm_star mult_onel mult_oner)

lemma star_folk_var2[simp]: "\<lbrakk>test p; !p\<cdot>x = x\<cdot>!p; !p\<cdot>y = y\<cdot>!p\<rbrakk> \<Longrightarrow> (p\<cdot>x + !p\<cdot>y)\<^sup>\<star>\<cdot>!p = !p\<cdot>y\<^sup>\<star>"
  by (metis star_folk_var add_commute test_def)
end

text {*
  Finally, we define Kleene algebra with tests.
*}

class kat = kleene_algebra + dioid_tests
begin

subclass kat_zerol
  apply (unfold_locales)
  by (metis star_inductr)

end

end
