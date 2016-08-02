theory Example_Utilities
imports
  "../ODE_Numerics"
begin

method_setup eval_lhs = \<open>Scan.succeed (fn ctxt =>
  SIMPLE_METHOD (HEADGOAL
    (CONVERSION (HOLogic.Trueprop_conv (HOLogic.eq_conv (Code_Evaluation.dynamic_conv ctxt) Conv.all_conv))
    THEN' Classical.rule_tac ctxt [refl] [])))\<close>
  \<open>Evaluate left hand side of HOL equation with code generator and apply reflexifity (works with schematics on the right)\<close>

end