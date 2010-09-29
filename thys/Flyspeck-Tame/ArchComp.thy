(*  Author:  Tobias Nipkow  *)

header {* Comparing Enumeration and Archive" *}

theory ArchComp
imports ArchCompAux Efficient_Nat 
begin

subsection {* Provide hand-adapted code evaluation *}

text {*
  This precompiles all archive entries to ML and thus avoids recompiling
  them every time.  Compiling them separately avoids to generate all archive
  entries as one chunk when building the evaluation conversion, which might be too
  enormous for the ML runtime environment.
*}

code_reflect Archive_Tri
  functions Tri

code_reflect Archive_Quad
  functions Quad

code_reflect Archive_Pent
  functions Pent

code_reflect Archive_Hex
  functions Hex

code_reflect Archive_Hept
  functions Hept

code_reflect Archive_Oct
  functions Oct

text {*
  The compilation of the operations itself is too marginal that it
  would be worth its own @{text code_reflect}.
*}

text {*
  By providing a specific evaluation method, we do preprocessing etc. only once;
  generating and compilation ML however happens at every invocation, but due
  to the precompiled archive entries this is not very dramatic.
*}

method_setup archive_eval =  {*
let
  val conv = Code_Runtime.static_holds_conv @{theory}
    [@{const_name Tri}, @{const_name Quad}, @{const_name Pent},
      @{const_name Hex}, @{const_name Hept}, @{const_name Oct},
      @{const_name Trueprop}, @{const_name pre_iso_test}, @{const_name list_all},
      @{const_name tameEnum}, @{const_name same}];
in Scan.succeed (K (SIMPLE_METHOD' (CONVERSION conv THEN' rtac TrueI))) end
*} "solve Flyspeck archive problem by evaluation"


subsection {* Proofs by evaluation using generated code *}

lemma pre_iso_test3: "\<forall>g \<in> set Tri. pre_iso_test g"
  by archive_eval

lemma pre_iso_test4: "\<forall>g \<in> set Quad. pre_iso_test g"
  by archive_eval

lemma pre_iso_test5: "\<forall>g \<in> set Pent. pre_iso_test g"
  by archive_eval

lemma pre_iso_test6: "\<forall>g \<in> set Hex. pre_iso_test g"
  by archive_eval

lemma pre_iso_test7: "\<forall>g \<in> set Hept. pre_iso_test g"
  by archive_eval

lemma pre_iso_test8: "\<forall>g \<in> set Oct. pre_iso_test g"
  by archive_eval

lemma same3: "same (tameEnum 0 800000) Tri"
  by archive_eval

lemma same4: "same (tameEnum 1 8000000) Quad"
  by archive_eval

lemma same5: "same (tameEnum 2 20000000) Pent"
  by archive_eval

lemma same6: "same (tameEnum 3 4000000) Hex"
  by archive_eval

lemma same7: "same (tameEnum 4 1000000) Hept"
  by archive_eval

lemma same8: "same (tameEnum 5 2000000) Oct"
  by archive_eval

end
