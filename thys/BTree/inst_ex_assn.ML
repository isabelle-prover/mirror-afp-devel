signature INST_EX_ASSN =
sig
  val tac : Proof.context -> term list -> int -> tactic
end

structure Inst_Ex_Assn : INST_EX_ASSN =
struct
                                  
fun tac ctxt [] = TRY o REPEAT_ALL_NEW (assume_tac ctxt)
  | tac ctxt (t :: ts) =      
      (TRY o (
        let
          val thm = Drule.infer_instantiate' ctxt [NONE, NONE, SOME (Thm.cterm_of ctxt t)] @{thm Assertions.ent_ex_postI}
        in
          resolve_tac ctxt [thm] THEN' tac ctxt ts
        end))

end