header {* Proving Relation (In)equalities via Regular Expressions *}

theory Regexp_Method
imports Equivalence_Checking Relation_Interpretation Reflection
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

code_reflect Regexp
  datatypes rexp = Zero | One | Atom | Plus | Times | Star
  and nat = "0::nat" | Suc
  functions check_eqv

declare check_eqv_def[code del] (* code is already generated *)

method_setup regexp = {*
  Scan.succeed (fn ctxt =>
    SIMPLE_METHOD' (
      (K (TRY (Local_Defs.unfold_tac ctxt @{thms regexp_unfold}))
      THEN' Reflection.genreify_tac ctxt 
        @{thms regexp_reify} NONE
      THEN' rtac @{thm rel_eqI}
      THEN' CONVERSION (Conv.params_conv (~1) 
        (K (Conv.concl_conv (~1) eval_oracle)) ctxt)
      THEN' rtac TrueI))) *}
"Decides relation equalities via regular expressions"

text {* Example: *}

lemma "(r \<union> s^+)^* = (r \<union> s)^*"
by regexp

end