(* Title:      Kleene algebra with tests
   Author:     Alasdair Armstrong, Victor B. F. Gomes, Georg Struth
   Maintainer: Georg Struth <g.struth at sheffield.ac.uk>
*)

header {* Pre-Conway Algebra *}

theory Conway
  imports "../DRA_Base" Test_Dioids
begin

text {*
  We define a weak regular algebra with serves as a common basis for Kleene algebra and demonic reginement algebra.
  It is closely related to an axiomatisation given by Conway~\cite{Conway71}.
*}

class dagger_op =
  fixes dagger :: "'a \<Rightarrow> 'a" ("_\<^sup>\<dagger>" [101] 100)

class near_regalg_base_zerol = near_dioid_one_zerol + dagger_op +
  assumes dagger_denest: "(x + y)\<^sup>\<dagger> = (x\<^sup>\<dagger>\<cdot>y)\<^sup>\<dagger>\<cdot>x\<^sup>\<dagger>"
  and dagger_prod_unfold: "(x \<cdot>y)\<^sup>\<dagger> = 1 + x \<cdot>(y \<cdot>x)\<^sup>\<dagger>\<cdot>y"

begin

lemma dagger_unfoldl: "1 + x \<cdot> x\<^sup>\<dagger> = x\<^sup>\<dagger>"
  by (metis dagger_prod_unfold mult_1_left mult_1_right)

text {* Nitpick refutes the next lemma. *}

lemma dagger_unfoldl_distl: "y\<cdot>x\<^sup>\<dagger> = y + y\<cdot>x\<cdot>x\<^sup>\<dagger>"
  (* nitpick *) oops

lemma dagger_unfoldl_distr: "x\<^sup>\<dagger>\<cdot>y = y + x\<cdot>x\<^sup>\<dagger>\<cdot>y"
  by (metis distrib_right' mult_1_left dagger_unfoldl)

lemma dagger_unfoldr: "1 + x\<^sup>\<dagger> \<cdot> x = x\<^sup>\<dagger>"
  by (metis dagger_prod_unfold mult_1_right mult_1_left)

text {* Nitpick refutes the next lemma. *}

lemma dagger_unfoldr_distl: "y\<cdot>x\<^sup>\<dagger> = y + y\<cdot>x\<^sup>\<dagger>\<cdot>x"
  (* nitpick *) oops

lemma dagger_unfoldr_distr: "x\<^sup>\<dagger>\<cdot>y = y + x\<^sup>\<dagger>\<cdot>x\<cdot>y"
  by (metis dagger_unfoldr distrib_right' mult_1_left mult.assoc)

lemma dagger_annil[simp]: "(x\<cdot>0)\<^sup>\<dagger> = 1 + x\<cdot>0"
  by (metis annil dagger_unfoldl mult.assoc)

lemma zero_dagger[simp]: "0\<^sup>\<dagger> = 1"
  by (metis add_0_right annil dagger_annil)

text {* Nitpick refutes the next lemma. *}

lemma dagger_denest2: "(x + y)\<^sup>\<dagger> = x\<^sup>\<dagger>\<cdot>(y\<cdot>x\<^sup>\<dagger>)\<^sup>\<dagger>"
  (* (* nitpick *) *) oops

end

class near_conway_sim_right_zerol = near_regalg_base_zerol + plus_ord +
  assumes dagger_simr: "z\<cdot>x \<le> y\<cdot>z \<Longrightarrow> z\<cdot>x\<^sup>\<dagger> \<le> y\<^sup>\<dagger>\<cdot>z"
begin

lemma dagger_iso: "x \<le> y \<Longrightarrow> x\<^sup>\<dagger> \<le> y\<^sup>\<dagger>"
  by (metis dagger_simr mult_1_left mult_1_right)

lemma dagger_slide_var: "x\<cdot>(y\<cdot>x)\<^sup>\<dagger> \<le> (x\<cdot>y)\<^sup>\<dagger>\<cdot>x"
  by (metis eq_refl dagger_simr mult.assoc)

text {* Nitpick refutes the next lemma. *}

lemma dagger_slide: "x\<cdot>(y\<cdot>x)\<^sup>\<dagger> = (x\<cdot>y)\<^sup>\<dagger>\<cdot>x"
  (* nitpick *) oops

text {*
  We say that $y$ preserves $x$ if $x \cdot y \cdot x = x \cdot y$ and $!x \cdot y \cdot !x = !x \cdot y$. This definition is taken
  from Solin~\cite{Solin11}. It is useful for program transformation.
*}
  
lemma preservation: "x\<cdot>y\<cdot>x = x\<cdot>y \<Longrightarrow> x\<cdot>y\<^sup>\<dagger> \<le> (x\<cdot>y + z)\<^sup>\<dagger>\<cdot>x"
  by (metis add_ub1 dagger_simr mult_isor)

end

class near_conway_sim_right_zerol_tests = near_conway_sim_right_zerol + near_dioid_test_zerol_dist
begin

lemma test_preserve1_var: "\<lbrakk>test p; p\<cdot>x\<cdot>p = p\<cdot>x\<rbrakk> \<Longrightarrow> p\<cdot>(p\<cdot>x + !p\<cdot>y)\<^sup>\<dagger> \<le> (p\<cdot>x)\<^sup>\<dagger>\<cdot>p"
  by (metis eq_refl test_eq2 dagger_simr)

text {* The next lemma could neither be proved nor refuted by nitpick. *}

lemma test_preserve2_var: "\<lbrakk>test p; p\<cdot>x\<cdot>p = p\<cdot>x\<rbrakk> \<Longrightarrow> p\<cdot>(p\<cdot>x + !p\<cdot>y)\<^sup>\<dagger> \<le> x\<^sup>\<dagger>"
  oops (* couldn't proof neither (* nitpick *) *)

end

class pre_conway = near_conway_sim_right_zerol + pre_dioid_test_zerol
begin

subclass near_conway_sim_right_zerol_tests
  by (unfold_locales)

lemma dagger_slide: "x\<cdot>(y\<cdot>x)\<^sup>\<dagger> = (x\<cdot>y)\<^sup>\<dagger>\<cdot>x"
  by (metis add.commute dagger_prod_unfold add_lub_var mult_1_right mult.assoc subdistl dagger_slide_var dagger_unfoldl_distr antisym)

lemma dagger_denest2: "(x + y)\<^sup>\<dagger> = x\<^sup>\<dagger>\<cdot>(y\<cdot>x\<^sup>\<dagger>)\<^sup>\<dagger>"
  by (metis dagger_denest dagger_slide)

lemma test_preserve: "\<lbrakk>test p; p\<cdot>x\<cdot>p = p\<cdot>x\<rbrakk> \<Longrightarrow> p\<cdot>x\<^sup>\<dagger> = (p\<cdot>x)\<^sup>\<dagger>\<cdot>p"
proof (rule antisym, metis add_0_right dagger_slide mult.assoc preservation)
  assume "test p" "p\<cdot>x\<cdot>p = p\<cdot>x"
  hence "x\<cdot>p \<le> x"
    by (metis test_restrictr)
  hence "p\<cdot>(x\<cdot>p)\<^sup>\<dagger> \<le> p\<cdot>x\<^sup>\<dagger>"
    by (metis dagger_iso mult_isol)
  thus "(p \<cdot> x)\<^sup>\<dagger> \<cdot> p \<le> p \<cdot> x\<^sup>\<dagger>"
    by (metis dagger_slide)
qed

lemma test_dumb_var: "\<lbrakk>test p; p\<cdot>x\<cdot>p = p\<cdot>x\<rbrakk> \<Longrightarrow> p\<cdot>(p\<cdot>x + !p\<cdot>y)\<cdot>p = p\<cdot>(p\<cdot>x + !p\<cdot>y)"
proof - 
  assume assms: "test p" "p\<cdot>x\<cdot>p = p\<cdot>x"
  hence "p\<cdot>(p\<cdot>x + !p\<cdot>y)\<cdot>p = p\<cdot>x"
    by (metis mult.assoc weak_distrib_left_var test_mult_idem_var annil test_comp_mult add_zeror)
  moreover have "p\<cdot>(p\<cdot>x + !p\<cdot>y) = p\<cdot>x"
    by (metis assms mult.assoc weak_distrib_left_var test_mult_idem_var annil test_comp_mult add_zeror)
  ultimately show ?thesis
    by metis
qed

lemma test_preserve1: "\<lbrakk>test p; p\<cdot>x\<cdot>p = p\<cdot>x\<rbrakk> \<Longrightarrow> p\<cdot>(p\<cdot>x + !p\<cdot>y)\<^sup>\<dagger> = (p\<cdot>x)\<^sup>\<dagger>\<cdot>p"
proof -
  assume assms: "test p" "p\<cdot>x\<cdot>p = p\<cdot>x"
  have "p\<cdot>(p\<cdot>x + !p\<cdot>y)\<^sup>\<dagger>  = (p\<cdot>(p\<cdot>x + !p\<cdot>y))\<^sup>\<dagger>\<cdot>p"
    by (metis assms(1) assms(2) test_dumb_var test_preserve)
  thus ?thesis
   by (metis assms mult.assoc weak_distrib_left_var test_mult_idem_var annil test_comp_mult add_zeror)
qed

lemma test_preserve2: "\<lbrakk>test p; p\<cdot>x\<cdot>p = p\<cdot>x\<rbrakk> \<Longrightarrow> p\<cdot>(p\<cdot>x + !p\<cdot>y)\<^sup>\<dagger> \<le> x\<^sup>\<dagger>"
  by (metis test_preserve test_preserve1 test_restrictl)

end

end
