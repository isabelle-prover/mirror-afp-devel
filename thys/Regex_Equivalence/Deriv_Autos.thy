(*  Author: Tobias Nipkow, Dmitriy Traytel *)

header "Framework Instantiations using (Partial) Derivatives"

(*<*)
theory Deriv_Autos
imports
  Automaton
  "../Regular-Sets/NDerivative"
  Deriv_PDeriv
  "~~/src/Tools/Permanent_Interpretation"
begin
(*>*)

subsection {* Brzozowski Derivatives Modulo ACI *}

lemma ACI_norm_derivs_alt: "\<guillemotleft>derivs w r\<guillemotright> = fold (\<lambda>a r. \<guillemotleft>deriv a r\<guillemotright>) w \<guillemotleft>r\<guillemotright>"
  by (induct w arbitrary: r) (auto simp: ACI_norm_deriv)

permanent_interpretation brzozowski: rexp_DFA "\<lambda>r. \<guillemotleft>r\<guillemotright>" "\<lambda>a r. \<guillemotleft>deriv a r\<guillemotright>" nullable lang
  defining brzozowski_closure = "rexp_DA.closure (\<lambda>a r. \<guillemotleft>deriv a r\<guillemotright>) (nullable :: 'a rexp \<Rightarrow> bool)"
    and check_eqv_brz = "rexp_DA.check_eqv (\<lambda>r. \<guillemotleft>r\<guillemotright>) (\<lambda>a r. \<guillemotleft>deriv a r\<guillemotright>) (nullable :: 'a rexp \<Rightarrow> bool)"
    and reachable_brz = "rexp_DA.reachable (\<lambda>r. \<guillemotleft>r :: 'a rexp\<guillemotright>) (\<lambda>a r. \<guillemotleft>deriv a r\<guillemotright>)"
    and automaton_brz = "rexp_DA.automaton (\<lambda>r. \<guillemotleft>r :: 'a rexp\<guillemotright>) (\<lambda>a r. \<guillemotleft>deriv a r\<guillemotright>)"
    and match_brz = "rexp_DA.match (\<lambda>r. \<guillemotleft>r\<guillemotright>) (\<lambda>a r. \<guillemotleft>deriv a r\<guillemotright>) (nullable :: 'a rexp \<Rightarrow> bool)"
proof unfold_locales
  case goal1 show ?case by (rule lang_ACI_norm)
next
  case goal2 show ?case by (rule trans[OF lang_ACI_norm lang_deriv])
next
  case goal3 show ?case by (rule nullable_iff)
next
  case goal4 show ?case by (simp only: ACI_norm_derivs_alt[symmetric] finite_derivs)
qed

subsection {* Brzozowski Derivatives Modulo ACI Operating on the Quotient Type *}

lemma derivs_alt: "derivs = fold deriv"
proof
  fix w :: "'a list" show "derivs w = fold deriv w" by (induct w) auto
qed

functor map_rexp by (simp_all only: o_def id_def map_map_rexp map_rexp_ident)

quotient_type 'a ACI_rexp = "'a rexp" / ACI
  morphisms rep_ACI_rexp ACI_class
  by (intro equivpI reflpI sympI transpI) (blast intro: ACI_refl ACI_sym ACI_trans)+

instantiation ACI_rexp :: ("{equal, linorder}") "{equal, linorder}"
begin
lift_definition less_eq_ACI_rexp :: "'a ACI_rexp \<Rightarrow> 'a ACI_rexp \<Rightarrow> bool" is "\<lambda>r s. less_eq \<guillemotleft>r\<guillemotright> \<guillemotleft>s\<guillemotright>"
   by (simp add: ACI_decidable)
lift_definition less_ACI_rexp :: "'a ACI_rexp \<Rightarrow> 'a ACI_rexp \<Rightarrow> bool" is "\<lambda>r s. less \<guillemotleft>r\<guillemotright> \<guillemotleft>s\<guillemotright>"
   by (simp add: ACI_decidable)
lift_definition equal_ACI_rexp :: "'a ACI_rexp \<Rightarrow> 'a ACI_rexp \<Rightarrow> bool" is "\<lambda>r s. \<guillemotleft>r\<guillemotright> = \<guillemotleft>s\<guillemotright>"
   by (simp add: ACI_decidable)
instance by intro_classes (transfer, force simp: ACI_decidable)+
end

lift_definition ACI_deriv :: "'a :: linorder \<Rightarrow> 'a ACI_rexp \<Rightarrow> 'a ACI_rexp" is deriv
  by (rule ACI_deriv)
lift_definition ACI_nullable :: "'a :: linorder ACI_rexp \<Rightarrow> bool" is nullable
  by (rule ACI_nullable)
lift_definition ACI_lang :: "'a :: linorder ACI_rexp \<Rightarrow> 'a lang" is lang
  by (rule ACI_lang)

lemma [transfer_rule]: "rel_fun (rel_set (pcr_ACI_rexp op=)) op = (finite o image ACI_norm) finite"
  unfolding rel_fun_def rel_set_def cr_ACI_rexp_def ACI_rexp.pcr_cr_eq
  apply (auto simp: elim!: finite_surj[of _ _ ACI_class] finite_surj[of _ _ "ACI_norm o rep_ACI_rexp"])
  apply (metis (hide_lams, no_types) ACI_norm_idem ACI_rexp.abs_eq_iff ACI_decidable imageI)
  apply (rule image_eqI)
  apply (rule trans[OF _ o_apply[symmetric]])
  apply (subst ACI_decidable[symmetric])
  apply (rule ACI_sym)
  apply (rule Quotient_rep_abs[OF Quotient_ACI_rexp, OF ACI_refl])
  apply blast
  done

permanent_interpretation brzozowski_quotient: rexp_DFA ACI_class ACI_deriv ACI_nullable ACI_lang
  defining brzozowski_quotient_closure = "rexp_DA.closure ACI_deriv (ACI_nullable :: 'a ACI_rexp \<Rightarrow> bool)"
    and check_eqv_brzq = "rexp_DA.check_eqv ACI_class ACI_deriv (ACI_nullable :: 'a ACI_rexp \<Rightarrow> bool)"
    and reachable_brzq = "rexp_DA.reachable (ACI_class :: 'a rexp \<Rightarrow> 'a ACI_rexp) ACI_deriv"
    and automaton_brzq = "rexp_DA.automaton (ACI_class :: 'a rexp \<Rightarrow> 'a ACI_rexp) ACI_deriv"
    and match_brzq = "rexp_DA.match (ACI_class :: 'a rexp \<Rightarrow> 'a ACI_rexp) ACI_deriv ACI_nullable"
proof unfold_locales
  case goal1 show ?case by transfer (rule refl)
next
  case goal2 show ?case by transfer (rule lang_deriv)
next
  case goal3 show ?case by transfer (rule nullable_iff)
next
  case goal4 show ?case by transfer
    (auto simp: ACI_decidable derivs_alt intro!: finite_subset[OF _ finite_derivs])
qed


subsection {* Brzozowski Derivatives Modulo ACI++ (Only Soundness) *}

permanent_interpretation nderiv: rexp_DA "\<lambda>x. norm x" nderiv nullable lang
  defining nderiv_closure = "rexp_DA.closure nderiv (nullable :: 'a rexp \<Rightarrow> bool)"
    and check_eqv_n = "rexp_DA.check_eqv (\<lambda>x. norm x) nderiv (nullable :: 'a rexp \<Rightarrow> bool)"
    and reachable_n = "rexp_DA.reachable (\<lambda>r :: 'a rexp. norm r) nderiv"
    and automaton_n = "rexp_DA.automaton (\<lambda>r :: 'a rexp. norm r) nderiv"
    and match_n = "rexp_DA.match (\<lambda>r. norm r) nderiv (nullable :: 'a rexp \<Rightarrow> bool)"
proof unfold_locales
  case goal1 show ?case by simp
next
  case goal2 show ?case by (rule lang_nderiv)
next
  case goal3 show ?case by (rule nullable_iff)
qed


subsection {* Partial Derivatives *}

permanent_interpretation pderiv: rexp_DFA "\<lambda>r. {r}" pderiv_set "\<lambda>P. EX p:P. nullable p" "\<lambda>P. \<Union>(lang ` P)"
  defining pderiv_closure = "rexp_DA.closure pderiv_set (\<lambda>P :: 'a rexp set. EX p:P. nullable p)"
    and check_eqv_p = "rexp_DA.check_eqv (\<lambda>r :: 'a rexp. {r}) pderiv_set (\<lambda>P. EX p:P. nullable p)"
    and reachable_p = "rexp_DA.reachable (\<lambda>r :: 'a rexp. {r}) pderiv_set"
    and automaton_p = "rexp_DA.automaton (\<lambda>r :: 'a rexp. {r}) pderiv_set"
    and match_p = "rexp_DA.match (\<lambda>r :: 'a rexp. {r}) pderiv_set (\<lambda>P. EX p:P. nullable p)"
proof unfold_locales
  case goal1 show ?case by simp
next
  case goal2 show ?case by (simp add: Deriv_pderiv)
next
  case goal3 show ?case by (simp add: nullable_iff)
next
  case goal4 note pderivs_lang_def[simp]
  { fix w :: "'a list"
    have "fold pderiv_set w = Union o image (pderivs_lang {w})" by (induct w) auto
  }
  hence "{fold pderiv_set w {s} |w. True} \<subseteq> Pow (pderivs_lang UNIV s)" by auto
  then show ?case by (rule finite_subset) (auto simp only: finite_pderivs_lang)
qed

permanent_interpretation pnderiv: rexp_DFA "\<lambda>r. r" pnderiv nullable lang
  defining pnderiv_closure = "rexp_DA.closure pnderiv (nullable :: 'a rexp \<Rightarrow> bool)"
    and check_eqv_pn = "rexp_DA.check_eqv (\<lambda>r :: 'a rexp. r) pnderiv nullable"
    and reachable_pn = "rexp_DA.reachable (\<lambda>r :: 'a rexp. r) pnderiv"
    and automaton_pn = "rexp_DA.automaton (\<lambda>r :: 'a rexp. r) pnderiv"
    and match_pn = "rexp_DA.match (\<lambda>r :: 'a rexp. r) pnderiv nullable"
proof unfold_locales
  case goal1 show ?case by simp
next
  case goal2 show ?case by (simp add: pnorm_def pset_deriv Deriv_pderiv pnderiv_alt)
next
  case goal3 show ?case by (simp add: nullable_iff)
next
  case goal4
  then show ?case unfolding pnderiv_alt[abs_def]
    by (rule finite_surj[OF pderiv.fin, of _ "flatten PLUS" s]) (auto simp: fold_pnorm_deriv)
qed

subsection {* Languages as States *}

text {* Not executable but still instructive. *}

lemma Derivs_alt_def: "Derivs w L = fold Deriv w L"
  by (induct w arbitrary: L) simp_all

interpretation language: rexp_DFA lang Deriv "\<lambda>L. [] \<in> L" id
proof unfold_locales
  case goal4
  have "{fold Deriv w (lang s) |w. True} \<subseteq> (\<lambda>X. UNION X lang) ` Pow (pderivs_lang UNIV s)"
    by (auto simp: sym[OF Derivs_alt_def] Derivs_pderivs pderivs_lang_def)
  then show ?case by (rule finite_surj[OF iffD2[OF finite_Pow_iff finite_pderivs_lang_UNIV]])
qed simp_all

definition str_eq :: "'a lang => ('a list \<times> 'a list) set" ("\<approx>_" [100] 100)
where "\<approx>A \<equiv> {(x, y).  (\<forall>z. x @ z \<in> A <-> y @ z \<in> A)}"

lemma str_eq_alt: "\<approx>A = {(x, y). fold Deriv x A = fold Deriv y A}"
  unfolding str_eq_def set_eq_iff in_fold_Deriv by simp

lemma Myhill_Nerode2: "finite (UNIV // \<approx>lang r)"
  unfolding str_eq_alt quotient_def Image_def
  by (rule finite_surj[OF language.fin, of _ "\<lambda>X. {y. X = fold Deriv y (lang r)}" r]) auto

(*<*)
end
(*>*)
