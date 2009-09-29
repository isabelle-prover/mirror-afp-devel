(*  ID:         $Id: ArchComp.thy,v 1.7 2008-10-09 13:27:29 fhaftmann Exp $
    Author:     Tobias Nipkow
*)

header {* Comparing Enumeration and Archive" *}

theory ArchComp
imports ArchCompAux Efficient_Nat 
begin

lemma pre_iso_test3: "\<forall>g \<in> set Tri. pre_iso_test g"
by eval

lemma pre_iso_test4: "\<forall>g \<in> set Quad. pre_iso_test g"
by eval

lemma pre_iso_test5: "\<forall>g \<in> set Pent. pre_iso_test g"
by eval

lemma pre_iso_test6: "\<forall>g \<in> set Hex. pre_iso_test g"
by eval

lemma pre_iso_test7: "\<forall>g \<in> set Hept. pre_iso_test g"
by eval

lemma pre_iso_test8: "\<forall>g \<in> set Oct. pre_iso_test g"
by eval

lemma same3: "same (tameEnum 0 800000) Tri"
by eval

lemma same4: "same (tameEnum 1 8000000) Quad"
by eval

lemma same5: "same (tameEnum 2 20000000) Pent"
by eval

lemma same6: "same (tameEnum 3 4000000) Hex"
by eval

lemma same7: "same (tameEnum 4 1000000) Hept"
by eval

lemma same8: "same (tameEnum 5 2000000) Oct"
by eval

end
