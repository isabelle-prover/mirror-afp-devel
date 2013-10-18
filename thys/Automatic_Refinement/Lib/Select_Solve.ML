** Obsolete. Moved to Select_Solve.thy **
signature SELECT_SOLVE = sig
  val PREFER_SOLVED: tactic -> tactic
  val IF_SUBGOAL_SOLVED: tactic -> tactic -> tactic -> tactic
  val TRY_SOLVE_FWD: tactic -> tactic
  val REPEAT_SOLVE_FWD_SELECT: tactic' -> Proof.context -> tactic' 
end

structure Select_Solve :SELECT_SOLVE = struct
  fun PREFER_SOLVED tac st = let
    val n = nprems_of st
    val res = tac st
    val res' = Seq.append 
      (Seq.filter (has_fewer_prems n) res)
      (Seq.filter (not o has_fewer_prems n) res)
  in
    res'
  end

  fun IF_SUBGOAL_SOLVED tac1 then_tac else_tac st = let
    val n = nprems_of st
  in
    (tac1 THEN COND (has_fewer_prems n) then_tac else_tac) st
  end

  fun TRY_SOLVE_FWD tac st = IF_UNSOLVED (
    IF_SUBGOAL_SOLVED tac (TRY_SOLVE_FWD tac) all_tac
  ) st

  fun REPEAT_SOLVE_FWD_SELECT tac ctxt i st = 
    IF_UNSOLVED (Subgoal.FOCUS_PARAMS (fn {context,...} => (*print_tac "AA" THEN*)
    PREFER_SOLVED (
      tac 1 THEN_ELSE (TRY_SOLVE_FWD (REPEAT_SOLVE_FWD_SELECT tac context 1), all_tac)
    )
  ) ctxt i) st
end
