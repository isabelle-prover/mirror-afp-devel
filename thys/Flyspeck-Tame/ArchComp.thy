(*  Author:  Tobias Nipkow  *)

header "Comparing Enumeration and Archive"

theory ArchComp
imports ArchCompProps "~~/src/HOL/Library/Efficient_Nat"
begin

method_setup cond_eval = {*
  Scan.succeed (fn ctxt =>
    SIMPLE_METHOD'
     (if getenv "FLYSPECK_SKIP_PROOFS" = "true" then
       SELECT_GOAL (Skip_Proof.cheat_tac (Proof_Context.theory_of ctxt))
      else eval_tac ctxt))
*} "solve goal by evaluation (skipped if FLYSPECK_SKIP_PROOFS=true)"


subsection {* Proofs by evaluation using generated code *}

lemma pre_iso_test3: "\<forall>g \<in> set Tri. pre_iso_test g"
by eval

lemma pre_iso_test4: "\<forall>g \<in> set Quad. pre_iso_test g"
by eval

lemma pre_iso_test5: "\<forall>g \<in> set Pent. pre_iso_test g"
by eval

lemma pre_iso_test6: "\<forall>g \<in> set Hex. pre_iso_test g"
by eval

lemma same3: "samet (tameEnumFilter 0) Tri"
by eval

lemma same4: "samet (tameEnumFilter 1) Quad"
by cond_eval

lemma same5: "samet (tameEnumFilter 2) Pent"
by cond_eval

lemma same6: "samet (tameEnumFilter 3) Hex"
by cond_eval

end
