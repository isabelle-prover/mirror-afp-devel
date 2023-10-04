(*  Title:      ML_Unification/higher_order_pattern_unification_tests.ML
    Author:     Kevin Kappelmann

Higher-order pattern unification tests.
*)
signature HIGHER_ORDER_PATTERN_UNIFICATION_TESTS =
sig
  val unit_tests_unifiable : Proof.context -> (term * term) list
end

structure Higher_Order_Pattern_Unification_Tests : HIGHER_ORDER_PATTERN_UNIFICATION_TESTS =
struct

fun unit_tests_unifiable ctxt =
  let val ctxt = Proof_Context.set_mode Proof_Context.mode_schematic ctxt
  in map (apply2 (Syntax.read_term ctxt)) [
      ("\<lambda> x. f x", "\<lambda> x. f x"),
      ("\<lambda> (x :: ?'X). (f :: ?'X \<Rightarrow> ?'Y) x", "\<lambda> (x :: ?'X1). (?y :: ?'X1 \<Rightarrow> ?'Y1) x"),
      ("\<lambda> x. r x ?X", "\<lambda> x. r x ?Y"),
      ("\<lambda> x. (x, (\<lambda> y. (y, \<lambda> z. ?x)))", "\<lambda> x. (x, (\<lambda> y. (y, \<lambda> z. g)))"),
      ("?f :: ?'Z \<Rightarrow> ?'X \<Rightarrow> ?'Y \<Rightarrow> ?'R", "\<lambda> (x :: ?'Z). (?f :: ?'Z \<Rightarrow> ?'X1 \<Rightarrow> ?'Y1 \<Rightarrow> ?'R1) x"),
      (
        "(?x :: ?'X, ?y :: ?'Y, ?z :: ?'Z)",
        "((f :: ?'Y \<Rightarrow> ?'X) (?y :: ?'Y), (g :: ?'Z \<Rightarrow> ?'Y) (?z :: ?'Z), c :: ?'C)"
      )
    ]
  end

end
