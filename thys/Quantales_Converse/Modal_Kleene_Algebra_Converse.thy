(* 
Title: Modal Kleene Algebra with converse
Author: Cameron Calk, Georg Struth
Maintainer: Georg Struth <g.struth at sheffield.ac.uk>
*)

section \<open>Modal Kleene algebra with converse\<close>

theory "Modal_Kleene_Algebra_Converse"
  imports Modal_Kleene_Algebra_Var Kleene_Algebra_Converse

begin

text \<open>Here we mainly study the interaction of converse with domain and codomain.\<close>

subsection \<open>Involutive modal Kleene algebras\<close>

class involutive_domain_semiring = domain_semiring + involutive_dioid

begin

notation domain_op ("dom")

lemma strong_conv_conv: "dom x \<le> x \<cdot> x\<^sup>\<circ> \<Longrightarrow> x \<le> x \<cdot> x\<^sup>\<circ> \<cdot> x"
proof-
  assume h: "dom x \<le> x \<cdot> x\<^sup>\<circ>"
  have "x = dom x \<cdot> x"
    by simp
  also have "\<dots> \<le>  x \<cdot> x\<^sup>\<circ> \<cdot> x"
    using h local.mult_isor by presburger
  finally show ?thesis.
qed

end

class involutive_dr_modal_semiring  = dr_modal_semiring + involutive_dioid

class involutive_dr_modal_kleene_algebra = involutive_dr_modal_semiring + kleene_algebra


subsection \<open>Modal semirings algebras with converse\<close>

class dr_modal_semiring_converse = dr_modal_semiring + dioid_converse

begin

lemma d_conv [simp]: "(dom x)\<^sup>\<circ> = dom x"
proof-
  have "dom x \<le> dom x \<cdot> (dom x)\<^sup>\<circ> \<cdot> dom x"
    by (simp add: local.strong_gelfand)
  also have  "\<dots> \<le> 1 \<cdot> (dom x)\<^sup>\<circ> \<cdot> 1"
    by (simp add: local.subid_conv)
  finally have a: "dom x \<le> (dom x)\<^sup>\<circ>"
    by simp
  hence "(dom x)\<^sup>\<circ> \<le> dom x"
    by (simp add: local.inv_adj)
  thus ?thesis
    using a by auto
qed

lemma cod_conv: "(cod x)\<^sup>\<circ> = cod x"
  by (metis d_conv local.dc_compat)

lemma d_conv_cod [simp]: "dom (x\<^sup>\<circ>) = cod x"
proof-
  have "dom (x\<^sup>\<circ>) = dom ((x \<cdot> cod x)\<^sup>\<circ>)"
    by simp
  also have "\<dots> = dom ((cod x)\<^sup>\<circ> \<cdot> x\<^sup>\<circ>)"
    using local.inv_contrav by presburger
  also have "\<dots> = dom (cod x \<cdot> x\<^sup>\<circ>)"
    by (simp add: cod_conv)
  also have "\<dots> = dom (dom (cod x) \<cdot> x\<^sup>\<circ>)"
    by simp
  also have "\<dots> = dom (cod x) \<cdot> dom (x\<^sup>\<circ>)"
    using local.dsg3 by blast
  also have "\<dots> = cod x \<cdot> dom (x\<^sup>\<circ>)"
    by simp
  also have "\<dots> = cod x \<cdot> cod (dom (x\<^sup>\<circ>))"
    by simp
  also have "\<dots> = cod (x \<cdot> cod (dom (x\<^sup>\<circ>)))"
    using local.rdual.dsg3 by presburger
  also have "\<dots> = cod (x \<cdot> dom (x\<^sup>\<circ>))"
    by simp
  also have "\<dots> = cod ((x\<^sup>\<circ>)\<^sup>\<circ> \<cdot> (dom (x\<^sup>\<circ>))\<^sup>\<circ>)"
    by simp
  also have "\<dots> = cod ((dom (x\<^sup>\<circ>) \<cdot> x\<^sup>\<circ>)\<^sup>\<circ>)"
    using local.inv_contrav by presburger
  also have "\<dots> = cod ((x\<^sup>\<circ>)\<^sup>\<circ>)"
    by simp
  also have "\<dots> = cod x"
    by simp
  finally show ?thesis.
qed

lemma cod_conv_d: "cod (x\<^sup>\<circ>) = dom x"
  by (metis d_conv_cod local.inv_invol)

lemma "dom y = y \<Longrightarrow> fd (x\<^sup>\<circ>) y = bd x y"
proof-
  assume h: "dom y = y"
  have "fd (x\<^sup>\<circ>) y = dom (x\<^sup>\<circ> \<cdot> dom y)"
    by (simp add: local.fd_def)
  also have "\<dots> = dom ((dom y \<cdot> x)\<^sup>\<circ>)"
    by simp
  also have "\<dots> = cod (dom y \<cdot> x)"
    using d_conv_cod by blast
  also have "\<dots> = bd x y"
    by (simp add: h local.bd_def)
  finally show ?thesis.
qed

lemma "dom y = y \<Longrightarrow> bd (x\<^sup>\<circ>) y = fd x y"
  by (metis cod_conv_d d_conv local.bd_def local.fd_def local.inv_contrav)

end


subsection \<open>Modal Kleene algebras with converse\<close>

class dr_modal_kleene_algebra_converse = dr_modal_semiring_converse + kleene_algebra

class dr_modal_semiring_strong_converse = involutive_dr_modal_semiring + 
  assumes weak_dom_def: "dom x \<le> x \<cdot> x\<^sup>\<circ>"
  and weak_cod_def: "cod x \<le> x\<^sup>\<circ> \<cdot> x"

subclass (in dr_modal_semiring_strong_converse) dr_modal_semiring_converse
  by unfold_locales (metis local.ddual.mult_isol_var local.dsg1 local.eq_refl local.weak_dom_def)

class dr_modal_kleene_algebra_strong_converse = dr_modal_semiring_strong_converse + kleene_algebra

end
