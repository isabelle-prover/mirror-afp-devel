(* Author: Dmitriy Traytel *)

header {* Deciding Equivalence of M2L Formulas *}

(*<*)
theory M2L_Equivalence_Checking
imports
  Pi_Equivalence_Checking
  PNormalization
  Init_Normalization
  M2L_Normalization
  Pi_Regular_Exp_Dual
begin
(*>*)

type_synonym 'a T = "'a atom"

definition [code del]: "\<DD> \<equiv> \<lambda>(\<Sigma>::'a::linorder list). embed.lderiv lookup (\<epsilon> \<Sigma>)"
definition [code del]: "Co\<DD> \<equiv> \<lambda>(\<Sigma>::'a::linorder list). embed.lderiv_dual lookup (\<epsilon> \<Sigma>)"

interpretation embed "set o \<sigma> \<Sigma>" "wf_atom \<Sigma>" \<pi> lookup "\<epsilon> \<Sigma>" for \<Sigma> :: "'a :: linorder list"
  where "embed.lderiv lookup (\<epsilon> \<Sigma>) = \<DD> \<Sigma>"
    and "embed.lderiv_dual lookup (\<epsilon> \<Sigma>) = Co\<DD> \<Sigma>"
  by unfold_locales (auto simp: \<sigma>_def \<pi>_def \<epsilon>_def \<DD>_def Co\<DD>_def)

lemma enum_not_empty[simp]: "Enum.enum \<noteq> []" (is "?enum \<noteq> []")
proof (rule notI)
  assume "?enum = []"
  hence "set ?enum = {}" by simp
  thus False unfolding UNIV_enum[symmetric] by simp
qed

definition pre_wf_formula where [code del]:
  "pre_wf_formula \<equiv> formula.pre_wf_formula Enum.enum"
definition wf_formula where [code del]:
  "wf_formula \<equiv> formula.wf_formula Enum.enum"
definition valid_ENC where [code del]: "valid_ENC \<equiv> formula.valid_ENC"
definition ENC where [code del]: "ENC \<equiv> formula.ENC"
definition dec_interp where [code del]: "dec_interp \<equiv> formula.dec_interp"
definition rexp_of where [code del]: "rexp_of \<equiv> formula.rexp_of"
definition rexp_of_alt where [code del]: "rexp_of_alt \<equiv> formula.rexp_of_alt"
definition rexp_of_alt' where [code del]: "rexp_of_alt' \<equiv> formula.rexp_of_alt'"
definition rexp_of' where [code del]: "rexp_of' \<equiv> formula.rexp_of'"
definition rexp_of'' where [code del]: "rexp_of'' \<equiv> formula.rexp_of''"

lemmas formula_defs = pre_wf_formula_def wf_formula_def
  rexp_of_def rexp_of'_def rexp_of''_def rexp_of_alt_def rexp_of_alt'_def
  ENC_def dec_interp_def valid_ENC_def FOV_def SOV_def

interpretation \<Phi>: formula "Enum.enum :: 'a :: {enum, linorder} list"
  where "\<Phi>.pre_wf_formula = pre_wf_formula"
  and   "\<Phi>.wf_formula = wf_formula"
  and   "\<Phi>.rexp_of = rexp_of"
  and   "\<Phi>.rexp_of_alt = rexp_of_alt"
  and   "\<Phi>.rexp_of_alt' = rexp_of_alt'"
  and   "\<Phi>.rexp_of' = rexp_of'"
  and   "\<Phi>.rexp_of'' = rexp_of''"
  and   "\<Phi>.valid_ENC = valid_ENC"
  and   "\<Phi>.ENC = ENC"
  and   "\<Phi>.dec_interp = dec_interp"
  by unfold_locales (auto simp: \<sigma>_def \<pi>_def formula_defs set_n_lists)

lemma lang_Plus_Zero: "lang \<Sigma> n (Plus r One) = lang \<Sigma> n (Plus s One) \<longleftrightarrow> lang \<Sigma> n r - {[]} = lang \<Sigma> n s - {[]}"
  by auto

lemmas lang\<^sub>M\<^sub>2\<^sub>L_rexp_of_norm = trans[OF sym[OF \<Phi>.lang\<^sub>M\<^sub>2\<^sub>L_norm] \<Phi>.lang\<^sub>M\<^sub>2\<^sub>L_rexp_of]
lemmas lang\<^sub>M\<^sub>2\<^sub>L_rexp_of'_norm = trans[OF sym[OF \<Phi>.lang\<^sub>M\<^sub>2\<^sub>L_norm] \<Phi>.lang\<^sub>M\<^sub>2\<^sub>L_rexp_of']
lemmas lang\<^sub>M\<^sub>2\<^sub>L_rexp_of''_norm = trans[OF sym[OF \<Phi>.lang\<^sub>M\<^sub>2\<^sub>L_norm] \<Phi>.lang\<^sub>M\<^sub>2\<^sub>L_rexp_of'']

setup {* Sign.map_naming (Name_Space.mandatory_path "slow") *}

definition [code del]: "test \<equiv> rexp_DA.test (final :: 'a :: linorder atom rexp \<Rightarrow> bool)"
definition [code del]: "step \<equiv> \<lambda>(\<Sigma>::'a::linorder list). rexp_DA.step (\<sigma> \<Sigma>) (\<lambda>a r. \<guillemotleft>\<DD> \<Sigma> a r\<guillemotright>) pnorm"
definition [code del]: "closure \<equiv> \<lambda>(\<Sigma>::'a::linorder list). rexp_DA.closure (\<sigma> \<Sigma>) (\<lambda>a r. \<guillemotleft>\<DD> \<Sigma> a r\<guillemotright>) final pnorm"
definition [code del]: "check_eqvRE \<equiv> \<lambda>(\<Sigma>::'a::linorder list). rexp_DA.check_eqv (\<sigma> \<Sigma>) (\<lambda>x. \<guillemotleft>pnorm (inorm x)\<guillemotright>) (\<lambda>a r. \<guillemotleft>\<DD> \<Sigma> a r\<guillemotright>) final pnorm"
definition test_invariant  :: "(('a::linorder \<times> bool list) list \<times> _) list \<times> _ \<Rightarrow> _" where
  [code del]: "test_invariant \<equiv> rexp_DA.test_invariant (final :: 'a atom rexp \<Rightarrow> bool)"
definition [code del]: "step_invariant \<equiv> \<lambda>(\<Sigma>::'a::linorder list). rexp_DA.step_invariant (\<sigma> \<Sigma>) (\<lambda>a r. \<guillemotleft>\<DD> \<Sigma> a r\<guillemotright>) pnorm"
definition [code del]: "closure_invariant \<equiv> \<lambda>(\<Sigma>::'a::linorder list). rexp_DA.closure_invariant (\<sigma> \<Sigma>) (\<lambda>a r. \<guillemotleft>\<DD> \<Sigma> a r\<guillemotright>) final pnorm"
definition [code del]: "counterexampleRE \<equiv> \<lambda>(\<Sigma>::'a::linorder list). rexp_DA.counterexample (\<sigma> \<Sigma>) (\<lambda>x. \<guillemotleft>pnorm (inorm x)\<guillemotright>) (\<lambda>a r. \<guillemotleft>\<DD> \<Sigma> a r\<guillemotright>) final pnorm"
definition [code del]: "reachable \<equiv> \<lambda>(\<Sigma>::'a::linorder list). rexp_DA.reachable (\<sigma> \<Sigma>) (\<lambda>x. \<guillemotleft>pnorm (inorm x)\<guillemotright>) (\<lambda>a r. \<guillemotleft>\<DD> \<Sigma> a r\<guillemotright>) pnorm"
definition [code del]: "automaton \<equiv> \<lambda>(\<Sigma>::'a::linorder list). rexp_DA.automaton (\<sigma> \<Sigma>) (\<lambda>x. \<guillemotleft>pnorm (inorm x)\<guillemotright>) (\<lambda>a r. \<guillemotleft>\<DD> \<Sigma> a r\<guillemotright>) pnorm"

lemmas rexp_DFA_defs = slow.test_invariant_def slow.test_def slow.step_invariant_def slow.step_def
  slow.closure_invariant_def slow.closure_def slow.check_eqvRE_def slow.counterexampleRE_def
  slow.reachable_def slow.automaton_def

interpretation D: rexp_DFA "\<sigma> \<Sigma>" "wf_atom \<Sigma>" \<pi> lookup "\<lambda>x. \<guillemotleft>pnorm (inorm x)\<guillemotright>"
  "\<lambda>a r. \<guillemotleft>\<DD> \<Sigma> a r\<guillemotright>" final "alphabet.wf (wf_atom \<Sigma>) n" pnorm "lang \<Sigma> n" n
  for \<Sigma> :: "'a :: linorder list" and n :: nat
  where "rexp_DA.test final = slow.test"
    and "rexp_DA.step (\<sigma> \<Sigma>) (\<lambda>a r. \<guillemotleft>\<DD> \<Sigma> a r\<guillemotright>) pnorm n = slow.step \<Sigma> n"
    and "rexp_DA.closure (\<sigma> \<Sigma>) (\<lambda>a r. \<guillemotleft>\<DD> \<Sigma> a r\<guillemotright>) final pnorm n = slow.closure \<Sigma> n"
    and "rexp_DA.check_eqv (\<sigma> \<Sigma>) (\<lambda>x. \<guillemotleft>pnorm (inorm x)\<guillemotright>) (\<lambda>a r. \<guillemotleft>\<DD> \<Sigma> a r\<guillemotright>) final pnorm n = slow.check_eqvRE \<Sigma> n"
    and "rexp_DA.test_invariant final = slow.test_invariant"
    and "rexp_DA.step_invariant (\<sigma> \<Sigma>) (\<lambda>a r. \<guillemotleft>\<DD> \<Sigma> a r\<guillemotright>) pnorm n = slow.step_invariant \<Sigma> n"
    and "rexp_DA.closure_invariant (\<sigma> \<Sigma>) (\<lambda>a r. \<guillemotleft>\<DD> \<Sigma> a r\<guillemotright>) final pnorm n = slow.closure_invariant \<Sigma> n"
    and "rexp_DA.counterexample (\<sigma> \<Sigma>) (\<lambda>x. \<guillemotleft>pnorm (inorm x)\<guillemotright>) (\<lambda>a r. \<guillemotleft>\<DD> \<Sigma> a r\<guillemotright>) final pnorm n = slow.counterexampleRE \<Sigma> n"
    and "rexp_DA.reachable (\<sigma> \<Sigma>) (\<lambda>x. \<guillemotleft>pnorm (inorm x)\<guillemotright>) (\<lambda>a r. \<guillemotleft>\<DD> \<Sigma> a r\<guillemotright>) pnorm n = slow.reachable \<Sigma> n"
    and "rexp_DA.automaton (\<sigma> \<Sigma>) (\<lambda>x. \<guillemotleft>pnorm (inorm x)\<guillemotright>) (\<lambda>a r. \<guillemotleft>\<DD> \<Sigma> a r\<guillemotright>) pnorm n = slow.automaton \<Sigma> n"
    by unfold_locales (auto simp only: comp_apply
      ACI_norm_wf ACI_norm_lang wf_inorm lang_inorm wf_pnorm lang_pnorm wf_lderiv lang_lderiv
      lang_final finite_fold_lderiv slow.rexp_DFA_defs dest!: lang_subset_lists)

definition check_eqv where
"check_eqv n \<phi> \<psi> \<longleftrightarrow> wf_formula n (FOr \<phi> \<psi>) \<and>
   slow.check_eqvRE Enum.enum n (Plus (rexp_of'' n (norm \<phi>)) One) (Plus (rexp_of'' n (norm \<psi>)) One)"

definition counterexample where
"counterexample n \<phi> \<psi> =
   map_option (\<lambda>w. dec_interp n (FOV (FOr \<phi> \<psi>)) w)
   (slow.counterexampleRE Enum.enum n (Plus (rexp_of'' n (norm \<phi>)) One) (Plus (rexp_of'' n (norm \<psi>)) One))"

lemma soundness: "slow.check_eqv n \<phi> \<psi> \<Longrightarrow> \<Phi>.lang\<^sub>M\<^sub>2\<^sub>L n \<phi> = \<Phi>.lang\<^sub>M\<^sub>2\<^sub>L n \<psi>"
  by (rule box_equals[OF iffD1[OF lang_Plus_Zero, OF slow.D.check_eqv_sound]
  sym[OF trans[OF lang\<^sub>M\<^sub>2\<^sub>L_rexp_of''_norm]] sym[OF trans[OF lang\<^sub>M\<^sub>2\<^sub>L_rexp_of''_norm]]])
   (auto simp: slow.check_eqv_def intro!: \<Phi>.wf_rexp_of'')

lemma completeness:
  assumes "\<Phi>.lang\<^sub>M\<^sub>2\<^sub>L n \<phi> = \<Phi>.lang\<^sub>M\<^sub>2\<^sub>L n \<psi>" "wf_formula n (FOr \<phi> \<psi>)"
  shows "slow.check_eqv n \<phi> \<psi>"
  using assms(2) unfolding slow.check_eqv_def
  by (intro conjI[OF assms(2) slow.D.check_eqv_complete[OF iffD2[OF lang_Plus_Zero]],
                OF box_equals[OF assms(1) lang\<^sub>M\<^sub>2\<^sub>L_rexp_of''_norm lang\<^sub>M\<^sub>2\<^sub>L_rexp_of''_norm]])
   (auto intro!: \<Phi>.wf_rexp_of'')

setup {* Sign.map_naming Name_Space.parent_path *}

setup {* Sign.map_naming (Name_Space.mandatory_path "fast") *}

definition [code del]: "test \<equiv> rexp_DA.test (final :: 'a :: linorder atom rexp \<Rightarrow> bool)"
definition [code del]: "step \<equiv> \<lambda>(\<Sigma>::'a::linorder list). rexp_DA.step (\<sigma> \<Sigma>) (\<lambda>a r. pnorm (\<DD> \<Sigma> a r)) id"
definition [code del]: "closure \<equiv> \<lambda>(\<Sigma>::'a::linorder list). rexp_DA.closure (\<sigma> \<Sigma>) (\<lambda>a r. pnorm (\<DD> \<Sigma> a r)) final id"
definition [code del]: "check_eqvRE \<equiv> \<lambda>(\<Sigma>::'a::linorder list). rexp_DA.check_eqv (\<sigma> \<Sigma>) (\<lambda>x. pnorm (inorm x)) (\<lambda>a r. pnorm (\<DD> \<Sigma> a r)) final id"
definition test_invariant  :: "(('a::linorder \<times> bool list) list \<times> _) list \<times> _ \<Rightarrow> _" where
  [code del]: "test_invariant \<equiv> rexp_DA.test_invariant (final :: 'a atom rexp \<Rightarrow> bool)"
definition [code del]: "step_invariant \<equiv> \<lambda>(\<Sigma>::'a::linorder list). rexp_DA.step_invariant (\<sigma> \<Sigma>) (\<lambda>a r. pnorm (\<DD> \<Sigma> a r)) id"
definition [code del]: "closure_invariant \<equiv> \<lambda>(\<Sigma>::'a::linorder list). rexp_DA.closure_invariant (\<sigma> \<Sigma>) (\<lambda>a r. pnorm (\<DD> \<Sigma> a r)) final id"
definition [code del]: "counterexampleRE \<equiv> \<lambda>(\<Sigma>::'a::linorder list). rexp_DA.counterexample (\<sigma> \<Sigma>) (\<lambda>x. pnorm (inorm x)) (\<lambda>a r. pnorm (\<DD> \<Sigma> a r)) final id"
definition [code del]: "reachable \<equiv> \<lambda>(\<Sigma>::'a::linorder list). rexp_DA.reachable (\<sigma> \<Sigma>) (\<lambda>x. pnorm (inorm x)) (\<lambda>a r. pnorm (\<DD> \<Sigma> a r)) id"
definition [code del]: "automaton \<equiv> \<lambda>(\<Sigma>::'a::linorder list). rexp_DA.automaton (\<sigma> \<Sigma>) (\<lambda>x. pnorm (inorm x)) (\<lambda>a r. pnorm (\<DD> \<Sigma> a r)) id"

lemmas rexp_DFA_defs = fast.test_invariant_def fast.test_def fast.step_invariant_def fast.step_def
  fast.closure_invariant_def fast.closure_def fast.check_eqvRE_def fast.counterexampleRE_def
  fast.reachable_def fast.automaton_def

interpretation D: rexp_DA_no_post "\<sigma> \<Sigma>" "wf_atom \<Sigma>" \<pi> lookup "\<lambda>x. pnorm (inorm x)"
  "\<lambda>a r. pnorm (\<DD> \<Sigma> a r)" final "alphabet.wf (wf_atom \<Sigma>) n" "lang \<Sigma> n" n
  for \<Sigma> :: "'a :: linorder list" and n :: nat
  where "rexp_DA.test final = fast.test"
    and "rexp_DA.step (\<sigma> \<Sigma>) (\<lambda>a r. pnorm (\<DD> \<Sigma> a r)) id n = fast.step \<Sigma> n"
    and "rexp_DA.closure (\<sigma> \<Sigma>) (\<lambda>a r. pnorm (\<DD> \<Sigma> a r)) final id n = fast.closure \<Sigma> n"
    and "rexp_DA.check_eqv (\<sigma> \<Sigma>) (\<lambda>x. pnorm (inorm x)) (\<lambda>a r. pnorm (\<DD> \<Sigma> a r)) final id n = fast.check_eqvRE \<Sigma> n"
    and "rexp_DA.test_invariant final = fast.test_invariant"
    and "rexp_DA.step_invariant (\<sigma> \<Sigma>) (\<lambda>a r. pnorm (\<DD> \<Sigma> a r)) id n = fast.step_invariant \<Sigma> n"
    and "rexp_DA.closure_invariant (\<sigma> \<Sigma>) (\<lambda>a r. pnorm (\<DD> \<Sigma> a r)) final id n = fast.closure_invariant \<Sigma> n"
    and "rexp_DA.counterexample (\<sigma> \<Sigma>) (\<lambda>x. pnorm (inorm x)) (\<lambda>a r. pnorm (\<DD> \<Sigma> a r)) final id n = fast.counterexampleRE \<Sigma> n"
    and "rexp_DA.reachable (\<sigma> \<Sigma>) (\<lambda>x. pnorm (inorm x)) (\<lambda>a r. pnorm (\<DD> \<Sigma> a r)) id n = fast.reachable \<Sigma> n"
    and "rexp_DA.automaton (\<sigma> \<Sigma>) (\<lambda>x. pnorm (inorm x)) (\<lambda>a r. pnorm (\<DD> \<Sigma> a r)) id n = fast.automaton \<Sigma> n"
    by unfold_locales (auto simp only: comp_apply
      ACI_norm_wf ACI_norm_lang wf_inorm lang_inorm wf_pnorm lang_pnorm wf_lderiv lang_lderiv id_apply
      lang_final fast.rexp_DFA_defs dest!: lang_subset_lists)
export_code fast.step in SML
definition check_eqv where
"check_eqv n \<phi> \<psi> \<longleftrightarrow> wf_formula n (FOr \<phi> \<psi>) \<and>
   fast.check_eqvRE Enum.enum n (Plus (rexp_of'' n (norm \<phi>)) One) (Plus (rexp_of'' n (norm \<psi>)) One)"

definition counterexample where
"counterexample n \<phi> \<psi> =
   map_option (\<lambda>w. dec_interp n (FOV (FOr \<phi> \<psi>)) w)
   (fast.counterexampleRE Enum.enum n (Plus (rexp_of'' n (norm \<phi>)) One) (Plus (rexp_of'' n (norm \<psi>)) One))"

lemma soundness: "fast.check_eqv n \<phi> \<psi> \<Longrightarrow> \<Phi>.lang\<^sub>M\<^sub>2\<^sub>L n \<phi> = \<Phi>.lang\<^sub>M\<^sub>2\<^sub>L n \<psi>"
  by (rule box_equals[OF iffD1[OF lang_Plus_Zero, OF fast.D.check_eqv_sound]
  sym[OF trans[OF lang\<^sub>M\<^sub>2\<^sub>L_rexp_of''_norm]] sym[OF trans[OF lang\<^sub>M\<^sub>2\<^sub>L_rexp_of''_norm]]])
   (auto simp: fast.check_eqv_def intro!: \<Phi>.wf_rexp_of'')

setup {* Sign.map_naming Name_Space.parent_path *}

setup {* Sign.map_naming (Name_Space.mandatory_path "dual") *}

definition [code del]: "test \<equiv> rexp_DA.test (final_dual :: 'a :: linorder atom rexp_dual \<Rightarrow> bool)"
definition [code del]: "step \<equiv> \<lambda>(\<Sigma>::'a::linorder list). rexp_DA.step (\<sigma> \<Sigma>) (\<lambda>a r. pnorm_dual (Co\<DD> \<Sigma> a r)) id"
definition [code del]: "closure \<equiv> \<lambda>(\<Sigma>::'a::linorder list). rexp_DA.closure (\<sigma> \<Sigma>) (\<lambda>a r. pnorm_dual (Co\<DD> \<Sigma> a r)) final_dual id"
definition [code del]: "check_eqvRE \<equiv> \<lambda>(\<Sigma>::'a::linorder list). rexp_DA.check_eqv (\<sigma> \<Sigma>) (\<lambda>x. pnorm_dual (rexp_dual_of (inorm x))) (\<lambda>a r. pnorm_dual (Co\<DD> \<Sigma> a r)) final_dual id"
definition test_invariant  :: "(('a::linorder \<times> bool list) list \<times> _) list \<times> _ \<Rightarrow> _" where
  [code del]: "test_invariant \<equiv> rexp_DA.test_invariant (final_dual :: 'a atom rexp_dual \<Rightarrow> bool)"
definition [code del]: "step_invariant \<equiv> \<lambda>(\<Sigma>::'a::linorder list). rexp_DA.step_invariant (\<sigma> \<Sigma>) (\<lambda>a r. pnorm_dual (Co\<DD> \<Sigma> a r)) id"
definition [code del]: "closure_invariant \<equiv> \<lambda>(\<Sigma>::'a::linorder list). rexp_DA.closure_invariant (\<sigma> \<Sigma>) (\<lambda>a r. pnorm_dual (Co\<DD> \<Sigma> a r)) final_dual id"
definition [code del]: "counterexampleRE \<equiv> \<lambda>(\<Sigma>::'a::linorder list). rexp_DA.counterexample (\<sigma> \<Sigma>) (\<lambda>x. pnorm_dual (rexp_dual_of (inorm x))) (\<lambda>a r. pnorm_dual (Co\<DD> \<Sigma> a r)) final_dual id"
definition [code del]: "reachable \<equiv> \<lambda>(\<Sigma>::'a::linorder list). rexp_DA.reachable (\<sigma> \<Sigma>) (\<lambda>x. pnorm_dual (rexp_dual_of (inorm x))) (\<lambda>a r. pnorm_dual (Co\<DD> \<Sigma> a r)) id"
definition [code del]: "automaton \<equiv> \<lambda>(\<Sigma>::'a::linorder list). rexp_DA.automaton (\<sigma> \<Sigma>) (\<lambda>x. pnorm_dual (rexp_dual_of (inorm x))) (\<lambda>a r. pnorm_dual (Co\<DD> \<Sigma> a r)) id"

lemmas rexp_dual_DFA_defs = dual.test_invariant_def dual.test_def dual.step_invariant_def dual.step_def
  dual.closure_invariant_def dual.closure_def dual.check_eqvRE_def dual.counterexampleRE_def
  dual.reachable_def dual.automaton_def

interpretation D: rexp_DA_no_post "\<sigma> \<Sigma>" "wf_atom \<Sigma>" \<pi> lookup "\<lambda>x. pnorm_dual (rexp_dual_of (inorm x))"
  "\<lambda>a r. pnorm_dual (Co\<DD> \<Sigma> a r)" final_dual "alphabet.wf_dual (wf_atom \<Sigma>) n" "lang_dual \<Sigma> n" n
  for \<Sigma> :: "'a :: linorder list" and n :: nat
  where "rexp_DA.test final_dual = dual.test"
    and "rexp_DA.step (\<sigma> \<Sigma>) (\<lambda>a r. pnorm_dual (Co\<DD> \<Sigma> a r)) id n = dual.step \<Sigma> n"
    and "rexp_DA.closure (\<sigma> \<Sigma>) (\<lambda>a r. pnorm_dual (Co\<DD> \<Sigma> a r)) final_dual id n = dual.closure \<Sigma> n"
    and "rexp_DA.check_eqv (\<sigma> \<Sigma>) (\<lambda>x. pnorm_dual (rexp_dual_of (inorm x))) (\<lambda>a r. pnorm_dual (Co\<DD> \<Sigma> a r)) final_dual id n = dual.check_eqvRE \<Sigma> n"
    and "rexp_DA.test_invariant final_dual = dual.test_invariant"
    and "rexp_DA.step_invariant (\<sigma> \<Sigma>) (\<lambda>a r. pnorm_dual (Co\<DD> \<Sigma> a r)) id n = dual.step_invariant \<Sigma> n"
    and "rexp_DA.closure_invariant (\<sigma> \<Sigma>) (\<lambda>a r. pnorm_dual (Co\<DD> \<Sigma> a r)) final_dual id n = dual.closure_invariant \<Sigma> n"
    and "rexp_DA.counterexample (\<sigma> \<Sigma>) (\<lambda>x. pnorm_dual (rexp_dual_of (inorm x))) (\<lambda>a r. pnorm_dual (Co\<DD> \<Sigma> a r)) final_dual id n = dual.counterexampleRE \<Sigma> n"
    and "rexp_DA.reachable (\<sigma> \<Sigma>) (\<lambda>x. pnorm_dual (rexp_dual_of (inorm x))) (\<lambda>a r. pnorm_dual (Co\<DD> \<Sigma> a r)) id n = dual.reachable \<Sigma> n"
    and "rexp_DA.automaton (\<sigma> \<Sigma>) (\<lambda>x. pnorm_dual (rexp_dual_of (inorm x))) (\<lambda>a r. pnorm_dual (Co\<DD> \<Sigma> a r)) id n = dual.automaton \<Sigma> n"
    by unfold_locales (auto simp only: comp_apply id_apply
      wf_inorm lang_inorm
      wf_dual_pnorm_dual lang_dual_pnorm_dual
      wf_dual_rexp_dual_of lang_dual_rexp_dual_of
      wf_dual_lderiv_dual lang_dual_lderiv_dual
      lang_dual_final_dual dual.rexp_dual_DFA_defs dest!: lang_dual_subset_lists)

definition check_eqv where
"check_eqv n \<phi> \<psi> \<longleftrightarrow> wf_formula n (FOr \<phi> \<psi>) \<and>
   dual.check_eqvRE Enum.enum n (Plus (rexp_of'' n (norm \<phi>)) One) (Plus (rexp_of'' n (norm \<psi>)) One)"

definition counterexample where
"counterexample n \<phi> \<psi> =
   map_option (\<lambda>w. dec_interp n (FOV (FOr \<phi> \<psi>)) w)
   (dual.counterexampleRE Enum.enum n (Plus (rexp_of'' n (norm \<phi>)) One) (Plus (rexp_of'' n (norm \<psi>)) One))"

lemma soundness: "dual.check_eqv n \<phi> \<psi> \<Longrightarrow> \<Phi>.lang\<^sub>M\<^sub>2\<^sub>L n \<phi> = \<Phi>.lang\<^sub>M\<^sub>2\<^sub>L n \<psi>"
  by (rule box_equals[OF iffD1[OF lang_Plus_Zero, OF dual.D.check_eqv_sound]
  sym[OF trans[OF lang\<^sub>M\<^sub>2\<^sub>L_rexp_of''_norm]] sym[OF trans[OF lang\<^sub>M\<^sub>2\<^sub>L_rexp_of''_norm]]])
   (auto simp: dual.check_eqv_def intro!: \<Phi>.wf_rexp_of'')

setup {* Sign.map_naming Name_Space.parent_path *}

(*<*)
end
(*>*)
