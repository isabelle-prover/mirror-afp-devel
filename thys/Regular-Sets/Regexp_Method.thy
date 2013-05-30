header {* Proving Relation (In)equalities via Regular Expressions *}

theory Regexp_Method
imports Equivalence_Checking Relation_Interpretation "~~/src/HOL/Library/Reflection"
begin

primrec rel_of_regexp :: "('a * 'a) set list \<Rightarrow> nat rexp \<Rightarrow> ('a * 'a) set" where
"rel_of_regexp vs Zero  = {}" |
"rel_of_regexp vs One  = Id" |
"rel_of_regexp vs (Atom i)  = vs ! i" |
"rel_of_regexp vs (Plus r s)  = rel_of_regexp vs r  \<union> rel_of_regexp vs s " |
"rel_of_regexp vs (Times r s)  = rel_of_regexp vs r O rel_of_regexp vs s" |
"rel_of_regexp vs (Star r)  = (rel_of_regexp vs r)^*"

lemma rel_of_regexp_rel: "rel_of_regexp vs r = rel (\<lambda>i. vs ! i) r"
by (induct r) auto

primrec rel_eq where
"rel_eq (r, s) vs = (rel_of_regexp vs r = rel_of_regexp vs s)"

lemma rel_eqI: "check_eqv r s \<Longrightarrow> rel_eq (r, s) vs"
unfolding rel_eq.simps rel_of_regexp_rel
by (rule Relation_Interpretation.soundness)
 (rule Equivalence_Checking.soundness)

lemmas regexp_reify = rel_of_regexp.simps rel_eq.simps
lemmas regexp_unfold = trancl_unfold_left subset_Un_eq

method_setup regexp = {*
  Scan.succeed (fn ctxt =>
    let
      val thy = Proof_Context.theory_of ctxt
      val regexp_conv = Code_Runtime.static_holds_conv thy
      [@{const_name Zero}, @{const_name One}, @{const_name Atom}, @{const_name Plus},
       @{const_name Times}, @{const_name Star}, 
       @{const_name check_eqv}, @{const_name Trueprop}]
    in
      SIMPLE_METHOD' (
        (TRY o etac @{thm rev_subsetD})
        THEN' (Subgoal.FOCUS_PARAMS (fn {context=ctxt', ...} =>
          TRY (Local_Defs.unfold_tac ctxt' @{thms regexp_unfold})
          THEN Reflection.reify_tac ctxt' @{thms regexp_reify} NONE 1
          THEN rtac @{thm rel_eqI} 1
          THEN CONVERSION regexp_conv 1
          THEN rtac TrueI 1) ctxt))
    end)
*} "decide relation equalities via regular expressions"

hide_const (open) le_rexp nPlus nTimes norm nullable bisimilar is_bisimulation closure step test
  step pre_bisim add_atoms check_eqv rel word_rel rel_eq

text {* Example: *}

lemma "(r \<union> s^+)^* = (r \<union> s)^*"
by regexp

end
