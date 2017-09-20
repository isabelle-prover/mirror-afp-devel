theory Examples_Poincare_Map
imports
  "HOL-ODE-Numerics.ODE_Numerics"
begin

subsection \<open>Van der Pol oscillator\<close>
experiment begin

schematic_goal vdp_fas:
  "[X!1, X!1 * (1 - (X!0)\<^sup>2) - X!0] = interpret_floatariths ?fas X"
  unfolding power2_eq_square\<comment>\<open>TODO: proper affine implementation of power\<close>
  by (reify_floatariths)

concrete_definition vdp_fas uses vdp_fas

interpretation vdp: ode_interpretation true_form UNIV vdp_fas "\<lambda>(x, y). (y, y * (1 - x\<^sup>2) - x)::real*real"
  "n::2" for n
  by standard
    (auto intro!: local_lipschitz_c1_euclideanI ext
      simp: split_beta' aform.ode_def vdp_fas_def power2_eq_square aform.Csafe_def aform.safe_def true_form_def
        isFDERIV_def less_Suc_eq_0_disj Basis_list_prod_def Basis_list_real_def eval_nat_numeral
        inverse_eq_divide eucl_of_list_prod)

lemma poincare_section_rep[poincare_tac_theorems]:
  "{(1, FloatR 9 (-2))..(2::real, FloatR 9 (-2))} = {eucl_of_list [1, FloatR 9 (-2)]..eucl_of_list [2, FloatR 9 (-2)]}"
  by (auto simp: eucl_of_list_prod)

abbreviation "vdp_ro \<equiv> ro 2 10 7 2 2 2"

lemma vdp_ro: "TAG_reach_optns vdp_ro" by simp

lemma vdp_start: "TAG_sctn True" by simp

lemma ninequarters: "2.25 = FloatR 9 (-2)"
  by auto

subsection \<open>No intermediate Poincare map\<close>

lemma vdp_pi_0: "vdp.guards_invar DIM(real \<times> real) []"
  by (auto simp: vdp.guards_invar_def)

lemma
  notes [poincare_tac_theorems] = vdp_pi_0 vdp_ro vdp_start
  shows "\<forall>x\<in>{(1.41, 2.25) .. (1.42, 2.25)}.
  vdp.returns_to   {(1, 2.25) .. (2, 2.25)} x \<and>
  vdp.poincare_map {(1, 2.25) .. (2, 2.25)} x \<in> {(1.41, 2.25) .. (1.42, 2.25)}"
  unfolding ninequarters
  by (tactic \<open>poincare_bnds_tac @{thm vdp_fas_def} 30 20 7 14 [(0, 1, "0x000000")] "" (* "out_p0_vdp_0.out" *)  @{context} 1\<close>)

lemma
  notes [poincare_tac_theorems] = vdp_pi_0 vdp_ro vdp_start
  shows "\<forall>x\<in>{(1.35, 2.25) .. (1.45, 2.25)}.
  vdp.returns_to   {(1, 2.25) .. (2, 2.25)} x \<and>
  vdp.poincare_map {(1, 2.25) .. (2, 2.25)} x \<in> {(1.35, 2.25) .. (1.45, 2.25)}"
  unfolding ninequarters
  by (tactic \<open>poincare_bnds_tac @{thm vdp_fas_def} 30 20 7 14 [(0, 1, "0x000000")] "" (* "out_p0_vdp_1.out" *)  @{context} 1\<close>)


subsection \<open>One intermediate Poincare map\<close>

lemma vdp_pi_1: "vdp.guards_invar DIM(real \<times> real) [([xsec2' 1 (-2, 0)], vdp_ro)]"
  by (auto simp: vdp.guards_invar_def)


lemma
  notes [poincare_tac_theorems] = vdp_ro vdp_start vdp_pi_1
  shows "\<forall>x\<in>{(1.41, 2.25) .. (1.42, 2.25)}.
  vdp.returns_to   {(1, 2.25) .. (2, 2.25)} x \<and>
  vdp.poincare_map {(1, 2.25) .. (2, 2.25)} x \<in> {(1.41, 2.25) .. (1.42, 2.25)}"
  unfolding ninequarters
  by (tactic \<open>poincare_bnds_tac @{thm vdp_fas_def} 30 20 7 14 [(0, 1, "0x000000")] "" (* "out_p1_vdp_0.out" *)  @{context} 1\<close>)

lemma
  notes [poincare_tac_theorems] = vdp_ro vdp_start vdp_pi_1
  shows "\<forall>x\<in>{(1.35, 2.25) .. (1.45, 2.25)}.
  vdp.returns_to   {(1, 2.25) .. (2, 2.25)} x \<and>
  vdp.poincare_map {(1, 2.25) .. (2, 2.25)} x \<in> {(1.35, 2.25) .. (1.45, 2.25)}"
  unfolding ninequarters
  by (tactic \<open>poincare_bnds_tac @{thm vdp_fas_def} 30 20 7 12 [(0, 1, "0x000000")] "" (* "out_p1_vdp_1.out" *) @{context} 1\<close>)

lemma
  notes [poincare_tac_theorems] = vdp_ro vdp_start vdp_pi_1
  shows "\<forall>x\<in>{(1.3, 2.25) .. (1.5, 2.25)}.
  vdp.returns_to   {(1, 2.25) .. (2, 2.25)} x \<and>
  vdp.poincare_map {(1, 2.25) .. (2, 2.25)} x \<in> {(1.3, 2.25) .. (1.5, 2.25)}"
  unfolding ninequarters
  by (tactic \<open>poincare_bnds_tac @{thm vdp_fas_def} 30 20 7 12 [(0, 1, "0x000000")] "" (* "out_p1_vdp_2.out" *) @{context} 1\<close>)

lemma
  notes [poincare_tac_theorems] = vdp_ro vdp_start vdp_pi_1
  shows "\<forall>x\<in>{(1.15, 2.25) .. (1.65, 2.25)}.
  vdp.returns_to   {(1, 2.25) .. (2, 2.25)} x \<and>
  vdp.poincare_map {(1, 2.25) .. (2, 2.25)} x \<in> {(1.15, 2.25) .. (1.65, 2.25)}"
  unfolding ninequarters
  by (tactic \<open>poincare_bnds_tac @{thm vdp_fas_def} 30 30 7 16 [(0, 1, "0x000000")] "" (* "out_p1_vdp_3.out" *) @{context} 1\<close>)

end


subsection \<open>Example Approximate JNF-Lorenz\<close>
experiment begin

schematic_goal
  lorenz_fas:
  "[11.8 * X!0 - 0.29 * (X!0 + X!1) * X!2,
    -22.8 * X!1 + 0.29*(X!0 + X!1) * X!2,
    -2.67*X!2 + (X!0 + X!1)*(2.2*X!0 - 1.3*X!1)] =
  interpret_floatariths ?fas X"
  by (reify_floatariths)
concrete_definition lorenz_fas uses lorenz_fas

interpretation lorenz: ode_interpretation true_form UNIV lorenz_fas
  "\<lambda>(x1, x2, x3).
    (11.8 * x1 - 0.29 * (x1 + x2) * x3,
    -22.8 * x2 + 0.29*(x1 + x2) * x3,
    -2.67*x3 + (x1 + x2)*(2.2*x1 - 1.3*x2))
    ::real*real*real"
  "three::3"
  by standard
    (auto intro!: local_lipschitz_c1_euclideanI ext
      simp: split_beta' aform.ode_def lorenz_fas_def power2_eq_square aform.safe_def true_form_def
        eucl_of_list_prod eval_nat_numeral
        isFDERIV_def less_Suc_eq_0_disj Basis_list_prod_def Basis_list_real_def aform.Csafe_def)

abbreviation "lorenz_ro \<equiv> ro 2 10 7 2 2 2"

lemma lorenz_ro: "TAG_reach_optns lorenz_ro" by simp

lemma lorenz_start: "TAG_sctn True" by simp

subsection \<open>No intermediate Poincare map\<close>

lemma lorenz_pi_0: "lorenz.guards_invar DIM(real \<times> real \<times> real) []"
  by (auto simp: lorenz.guards_invar_def)

abbreviation \<Sigma>::"(real * real * real) set"
  where "\<Sigma> \<equiv> {(-6, -6, 27) .. (6, 6, 27)}"

lemma poincare_section_rep[poincare_tac_theorems]:
  "\<Sigma> = {eucl_of_list [-6, -6, 27]..eucl_of_list [6, 6, 27]}"
  by (auto simp: eucl_of_list_prod)

abbreviation "lorenz_iv x y w \<equiv> {(x - w, y - w, 27)..(x + w, y + w, 27)::real*real*real}"

subsection \<open>With intermediate Poincare map\<close>

lemma lorenz_pi_1: "lorenz.guards_invar DIM(real \<times> real \<times> real) [([xsec 2 (-1, 1) (0, 10)], lorenz_ro)]"
  by (auto simp: lorenz.guards_invar_def)

lemma
  notes [poincare_tac_theorems] = lorenz_pi_1 lorenz_ro lorenz_start
  shows "\<forall>x\<in>lorenz_iv 0.84 2.21 0.005.
  lorenz.returns_to   \<Sigma> x \<and>
  lorenz.poincare_map \<Sigma> x \<in> lorenz_iv (-2.17) 0.98 0.3"
  by (tactic \<open>poincare_bnds_tac @{thm lorenz_fas_def} 30 30 9 14 [(0, 2, "0x000000"), (1, 2, "0xff0000")] "" (* "out_p1_lorenz_0.out" *) @{context} 1\<close>)

lemma
  notes [poincare_tac_theorems] = lorenz_pi_1 lorenz_ro lorenz_start
  shows "\<forall>x\<in>lorenz_iv 0.86 2.21 0.005.
  lorenz.returns_to   \<Sigma> x \<and>
  lorenz.poincare_map \<Sigma> x \<in> lorenz_iv (-1.8) 1.2 0.2"
  by (tactic \<open>poincare_bnds_tac @{thm lorenz_fas_def} 30 30 9 14 [(0, 2, "0x000000"), (1, 2, "0xff0000")] "" (* "out_p1_lorenz_1.out" *) @{context} 1\<close>)

lemma
  notes [poincare_tac_theorems] = lorenz_pi_1 lorenz_ro lorenz_start
  shows "\<forall>x\<in>lorenz_iv 0.88 2.21 0.005.
  lorenz.returns_to   \<Sigma> x \<and>
  lorenz.poincare_map \<Sigma> x \<in> lorenz_iv (-1.58) 1.3 0.1"
  by (tactic \<open>poincare_bnds_tac @{thm lorenz_fas_def} 30 30 9 14 [(0, 2, "0x000000"), (1, 2, "0xff0000")] "" (* "out_p1_lorenz_2.out" *) @{context} 1\<close>)

lemma
  notes [poincare_tac_theorems] = lorenz_pi_1 lorenz_ro lorenz_start
  shows "\<forall>x\<in>lorenz_iv 0.90 2.21 0.005.
  lorenz.returns_to   \<Sigma> x \<and>
  lorenz.poincare_map \<Sigma> x \<in> lorenz_iv (-1.4) 1.4 0.1"
  by (tactic \<open>poincare_bnds_tac @{thm lorenz_fas_def} 30 30 9 14 [(0, 2, "0x000000"), (1, 2, "0xff0000")] "" (* "out_p1_lorenz_3.out" *) @{context} 1\<close>)

lemma
  notes [poincare_tac_theorems] = lorenz_pi_1 lorenz_ro lorenz_start
  shows "\<forall>x\<in>lorenz_iv 0.92 2.21 0.005.
  lorenz.returns_to   \<Sigma> x \<and>
  lorenz.poincare_map \<Sigma> x \<in> lorenz_iv (-1.24) 1.45 0.1"
  by (tactic \<open>poincare_bnds_tac @{thm lorenz_fas_def} 30 30 9 14 [(0, 2, "0x000000"), (1, 2, "0xff0000")] "" (* "out_p1_lorenz_4.out" *) @{context} 1\<close>)

lemma
  notes [poincare_tac_theorems] = lorenz_pi_1 lorenz_ro lorenz_start
  shows "\<forall>x\<in>lorenz_iv 0.94 2.21 0.005.
  lorenz.returns_to   \<Sigma> x \<and>
  lorenz.poincare_map \<Sigma> x \<in> lorenz_iv (-1.11) 1.5 0.1"
  by (tactic \<open>poincare_bnds_tac @{thm lorenz_fas_def} 30 30 9 14 [(0, 2, "0x000000"), (1, 2, "0xff0000")] "" (* "out_p1_lorenz_5.out" *) @{context} 1\<close>)

end

end