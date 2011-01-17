(*  Author:  Tobias Nipkow  *)

header "Comparing Enumeration and Archive"

theory ArchComp
imports ArchCompAux Efficient_Nat
begin

subsection {* Proofs by evaluation using generated code *}

lemma pre_iso_test3: "\<forall>g \<in> set Tri. pre_iso_test g"
by eval

(* less than 134291356 iterations *)
lemma pre_iso_test4: "\<forall>g \<in> set Quad. pre_iso_test g"
by eval

(* less than 99334466383 iterations *)
lemma pre_iso_test5: "\<forall>g \<in> set Pent. pre_iso_test g"
by eval

(* less than 334466383 iterations *)
lemma pre_iso_test6: "\<forall>g \<in> set Hex. pre_iso_test g"
by eval

lemma same3: "same (tameEnum 0) Tri"
by eval

lemma same4: "same (tameEnum 1) Quad"
by eval

lemma same5: "same (tameEnum 2) Pent"
by eval

lemma same6: "same (tameEnum 3) Hex"
by eval

end
