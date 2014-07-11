(*  Title:       Inv_Cterms.thy
    License:     BSD 2-Clause. See LICENSE.
    Author:      Timothy Bourke
*)

header "A custom tactic for showing invariants via control terms"

theory Inv_Cterms
imports AWN_Labels
begin

text {*
  This tactic tries to solve a goal by reducing it to a problem over (local) cterms (using
  one of the cterms\_intros intro rules); expanding those to consider all process names (using
  one of the ctermsl\_cases destruction rules); simplifying each (using the
  cterms\_env simplification rules); splitting them up into separate subgoals; replacing the
  derivative term with a variable; `executing' a transition of each term; and then simplifying.

  The tactic can stop after applying introduction rule (``inv\_cterms (intro\_only)''), or after
  having generated the verification condition subgoals and before having simplified them
  (``inv\_cterms (vcs\_only)''). It takes arguments to add or remove simplification rules
  (``simp add: lemmanames''), to add forward rules on assumptions (to introduce previously
  proved invariants; ``inv add: lemmanames''), or to add elimination rules that solve any
  remaining subgoals (``solve: lemmanames'').

  To configure the tactic for a set of transition rules:
  \begin{enumerate}
  \item add elimination rules: declare seqpTEs [cterms\_seqte]
  \item add rules to replace derivative terms: declare elimders [cterms\_elimders]
  \end{enumerate}

  To configure the tactic for a process environment (@{text \<Gamma>}):
  \begin{enumerate}
  \item add simp rules: declare @{text \<Gamma>}.simps [cterms\_env]
  \item add case rules: declare aodv\_proc\_cases [ctermsl\_cases]
  \item add invariant intros
      declare
        seq\_invariant\_ctermsI [OF aodv\_wf aodv\_control\_within aodv\_simple\_labels, cterms\_intros]
        seq\_step\_invariant\_ctermsI [OF aodv\_wf aodv\_control\_within aodv\_simple\_labels, cterms\_intros]
  \end{enumerate}

*}

lemma has_ctermsl: "p \<in> ctermsl \<Gamma> \<Longrightarrow> p \<in> ctermsl \<Gamma>" .

ML {*
structure CtermsElimders = Named_Thms
  (val name = @{binding "cterms_elimders"}
   val description = "Rules for truncating sequential process terms")
val cterms_elimders_add = Thm.declaration_attribute CtermsElimders.add_thm
val cterms_elimders_del = Thm.declaration_attribute CtermsElimders.del_thm

structure CtermsTE = Named_Thms
  (val name = @{binding "cterms_seqte"}
   val description = "Elimination rules for sequential process terms")
val cterms_seqte_add = Thm.declaration_attribute CtermsTE.add_thm
val cterms_seqte_del = Thm.declaration_attribute CtermsTE.del_thm

structure CtermsEnvRules = Named_Thms
  (val name = @{binding "cterms_env"}
   val description = "Simplification rules for sequential process environments")
val cterms_env_add = Thm.declaration_attribute CtermsEnvRules.add_thm
val cterms_env_del = Thm.declaration_attribute CtermsEnvRules.del_thm

structure CtermslCases = Named_Thms
  (val name = @{binding "ctermsl_cases"}
   val description = "Destruction rules for case splitting ctermsl")
val ctermsl_cases_add = Thm.declaration_attribute CtermslCases.add_thm
val ctermsl_cases_del = Thm.declaration_attribute CtermslCases.del_thm

structure CtermsIntros = Named_Thms
  (val name = @{binding "cterms_intros"}
   val description = "Introduction rules from cterms")
val cterms_intros_add = Thm.declaration_attribute CtermsIntros.add_thm
val cterms_intros_del = Thm.declaration_attribute CtermsIntros.del_thm

structure CtermsInvs = Named_Thms
  (val name = @{binding "cterms_invs"}
   val description = "Invariants to try to apply at each vc")
val cterms_invs_add = Thm.declaration_attribute CtermsInvs.add_thm
val cterms_invs_del = Thm.declaration_attribute CtermsInvs.del_thm

structure CtermsFinal = Named_Thms
  (val name = @{binding "cterms_final"}
   val description = "Elimination rules to try on each vc after simplification")
val cterms_final_add = Thm.declaration_attribute CtermsFinal.add_thm
val cterms_final_del = Thm.declaration_attribute CtermsFinal.del_thm

fun simp_only thms ctxt =
  asm_full_simp_tac
     (Context.proof_map
        (Simplifier.map_ss (Raw_Simplifier.clear_simpset
                            #> fold Simplifier.add_simp thms))
        ctxt)

(* shallow_simp is useful for mopping up assumptions before really trying to simplify.
   Perhaps surprisingly, this saves minutes in some of the proofs that use a lot of
   invariants of the form (l = P-:n --> P). *)
fun shallow_simp ctxt =
  let val ctxt' = Config.put simp_depth_limit 2 ctxt in
    TRY o safe_asm_full_simp_tac ctxt'
  end

fun create_vcs ctxt i =
  let val main_simp_thms =  CtermsEnvRules.get ctxt
      val ctermsl_cases = CtermslCases.get ctxt
  in
    dtac @{thm has_ctermsl} i
    THEN_ELSE (dmatch_tac ctermsl_cases i
               THEN
               TRY (REPEAT_ALL_NEW (ematch_tac [@{thm disjE}]) i)
               THEN
               (PARALLEL_GOALS (ALLGOALS
                 (fn i => simp_only main_simp_thms ctxt i
                  THEN TRY (REPEAT_ALL_NEW (ematch_tac [@{thm disjE}]) i))
               )), all_tac)
  end

fun try_invs ctxt =
  let val inv_thms =  CtermsInvs.get ctxt
      fun fapp thm = TRY o (EVERY' (ftac thm :: replicate (Thm.nprems_of thm - 1) assume_tac))
  in
    EVERY' (map fapp inv_thms)
  end

fun try_final ctxt =
  let val final_thms =  CtermsFinal.get ctxt
      fun eapp thm = EVERY' (etac thm :: replicate (Thm.nprems_of thm - 1) assume_tac)
  in
    TRY o (FIRST' (map eapp final_thms))
  end

fun each ctxt =
  (EVERY' ((ematch_tac (CtermsElimders.get ctxt) :: replicate 2 assume_tac))
   THEN' simp_only @{thms labels_psimps} ctxt
   THEN' (ematch_tac (CtermsTE.get ctxt)
     THEN_ALL_NEW
       (fn j => simp_only [@{thm mem_Collect_eq}] ctxt j
                  THEN REPEAT (etac @{thm exE} j)
                  THEN REPEAT (etac @{thm conjE} j))))
  ORELSE' (SOLVED' (clarsimp_tac ctxt))

fun simp_all ctxt =
  let val ctxt' =
        ctxt |> fold Splitter.add_split [@{thm split_if_asm}]
  in
    (PARALLEL_GOALS o ALLGOALS o shallow_simp) ctxt
    THEN
    TRY ((CHANGED_PROP (PARALLEL_GOALS (ALLGOALS
           (asm_full_simp_tac ctxt' THEN' (try_final ctxt))))))
  end

fun intro_and_invs ctxt i =
  let val cterms_intros = CtermsIntros.get ctxt in
    match_tac cterms_intros i
    THEN (PARALLEL_GOALS (ALLGOALS (try_invs ctxt)))
  end

fun process_vcs ctxt _ =
  ALLGOALS (create_vcs ctxt ORELSE' (SOLVED' (clarsimp_tac ctxt)))
  THEN (PARALLEL_GOALS (ALLGOALS (TRY o (each ctxt))))

val intro_onlyN = "intro_only"
val vcs_onlyN = "vcs_only"
val invN = "inv"
val solveN = "solve"

val inv_cterms_options =
  (Args.parens (Args.$$$ intro_onlyN) >>  K intro_and_invs ||
   Args.parens (Args.$$$ vcs_onlyN) >>  K (fn ctxt => intro_and_invs ctxt
                                                      THEN' process_vcs ctxt) ||
   Scan.succeed (fn ctxt => intro_and_invs ctxt
                            THEN' process_vcs ctxt
                            THEN' K (simp_all ctxt)))

val inv_cterms_setup =
  Method.setup @{binding inv_cterms}
    (Scan.lift inv_cterms_options --| Method.sections
      ((Args.$$$ invN -- Args.add -- Args.colon >> K (I, cterms_invs_add))
       :: (Args.$$$ solveN -- Args.colon >> K (I, cterms_final_add))
       :: Simplifier.simp_modifiers)
      >> (fn tac => SIMPLE_METHOD' o tac))
    "Solve invariants by considering all (interesting) control terms."
*}
attribute_setup cterms_seqte    = {* Attrib.add_del cterms_seqte_add cterms_seqte_del *}
attribute_setup cterms_elimders = {* Attrib.add_del cterms_elimders_add cterms_elimders_del *}
attribute_setup cterms_env =      {* Attrib.add_del cterms_env_add cterms_env_del *}
attribute_setup ctermsl_cases =   {* Attrib.add_del ctermsl_cases_add ctermsl_cases_del *}
attribute_setup cterms_intros =   {* Attrib.add_del cterms_intros_add cterms_intros_del *}
setup {* inv_cterms_setup *}

declare
  insert_iff [cterms_env]                                                
  Un_insert_right [cterms_env]
  sup_bot_right [cterms_env]
  Product_Type.prod_cases [cterms_env]
  ctermsl.simps [cterms_env]

end
