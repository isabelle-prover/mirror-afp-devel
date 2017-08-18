theory Example_Utilities
imports
  "HOL-ODE-Numerics.ODE_Numerics"
begin

method_setup guess_rhs = \<open>
let
  fun compute ctxt var lhs =
    let
      val lhs' = Code_Evaluation.dynamic_value_strict ctxt lhs;
      val clhs' = Thm.cterm_of ctxt lhs';
      val inst = Thm.instantiate ([], [(var, clhs')]);
    in PRIMITIVE inst end;
  fun eval_schematic_rhs ctxt t = (case try (HOLogic.dest_eq o HOLogic.dest_Trueprop) t of
      SOME (lhs, Var var) => compute ctxt var lhs
    | _ => no_tac);
in
  Scan.succeed (fn ctxt =>
    SIMPLE_METHOD (HEADGOAL (SUBGOAL (fn (t, _) => eval_schematic_rhs ctxt t))))
end
\<close>

end
