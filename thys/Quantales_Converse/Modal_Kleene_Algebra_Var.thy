(* 
Title: Modal Kleene algebra based on domain and range semirings
Author: Georg Struth
Maintainer: Georg Struth <g.struth at sheffield.ac.uk>
*)

section \<open>Modal Kleene algebra based on domain and range semirings\<close>

theory "Modal_Kleene_Algebra_Var"
  imports KAD.Domain_Semiring KAD.Range_Semiring

begin

notation domain_op ("dom") 
notation range_op ("cod") 

subclass (in domain_semiring) dioid_one_zero..

subclass (in range_semiring) dioid_one_zero
  by unfold_locales simp

subsection \<open>Modal semirings\<close>

text \<open>The following modal semirings are based on domain and range semirings instead of antidomain and antirange semirings,
as in the AFP entry for Kleene algebra with domain.\<close>

class dr_modal_semiring = domain_semiring + range_semiring +
  assumes dc_compat [simp]: "dom (cod x) = cod x" 
  and cd_compat [simp]: "cod (dom x) = dom x" 

begin 

sublocale msrdual: dr_modal_semiring "(+)" "\<lambda>x y. y \<cdot> x" 1 0 cod "(\<le>)" "(<)" dom
  by unfold_locales simp_all

lemma d_cod_fix: "(dom x = x) = (x = cod x)"
  by (metis local.cd_compat local.dc_compat)

lemma local_var: "(x \<cdot> y = 0) = (cod x \<cdot> dom y = 0)"
  using local.dom_weakly_local local.rdual.dom_weakly_local by force

lemma fbdia_conjugation: "(fd x (dom p) \<cdot> dom q = 0) = (dom p \<cdot> bd x (dom q) = 0)"
  by (metis local.bd_def local.cd_compat local.ddual.mult_assoc local.dom_weakly_local local.fd_def local.rdual.dom_weakly_local local.rdual.dsg4)

end

subsection \<open>Modal Kleene algebra\<close>

class dr_modal_kleene_algebra = dr_modal_semiring + kleene_algebra

end
