(*  Author:  Tobias Nipkow  *)

header "Comparing Enumeration and Archive"

theory ArchComp
imports ArchCompAux Efficient_Nat
begin

subsection {* Proofs by evaluation using generated code *}

lemma pre_iso_test3: "\<forall>g \<in> set Tri. pre_iso_test g"
by eval

lemma pre_iso_test4: "\<forall>g \<in> set Quad. pre_iso_test g"
by eval

lemma pre_iso_test5: "\<forall>g \<in> set Pent. pre_iso_test g"
by eval

lemma pre_iso_test6: "\<forall>g \<in> set Hex. pre_iso_test g"
by eval

(* w/o Filter to keep that variant alive as well *)
lemma same3: "same (tameEnum 0) Tri"
by eval

lemma same4: "same (tameEnumFilter 1 134291356) Quad"
by eval

lemma same5: "same (tameEnumFilter 2 99334466383) Pent"
by eval

lemma same6: "same (tameEnumFilter 3 334466383) Hex"
by eval

end
