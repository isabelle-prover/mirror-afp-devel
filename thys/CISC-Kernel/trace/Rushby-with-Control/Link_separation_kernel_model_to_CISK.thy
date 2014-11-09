subsection {* Link implementation to CISK: the specific separation kernel is an interpretation of the generic model.\label{sect:link_to_CISK} *}

theory Link_separation_kernel_model_to_CISK
  imports Separation_kernel_model         
begin

text {* We show that the separation kernel instantiation satisfies the 
specification of CISK.
*}

theorem CISK_proof_obligations_satisfied:
  shows
    "Controllable_Interruptible_Separation_Kernel
      rstep
      routput_f
      (\<up>s0)
      rcurrent
      rcswitch
      rkinvolved
      rifp
      rvpeq
      rAS_set
      rinvariant
      rprecondition
      raborting
      rwaiting
      rset_error_code"
proof (unfold_locales)
  --"show that rvpeq is equivalence relation"
  show "\<forall> a b c u. (rvpeq u a b \<and> rvpeq u b c) \<longrightarrow> rvpeq u a c"
   and "\<forall> a b u. rvpeq u a b \<longrightarrow> rvpeq u b a"
   and "\<forall> a u. rvpeq u a a"
    using inst_vpeq_rel by metis+
  --"show output consistency"
  show "\<forall> a s t. rvpeq (rcurrent s) s t \<and> rcurrent s = rcurrent t \<longrightarrow> routput_f s a = routput_f t a"
    using inst_output_consistency by metis
  --"show reflexivity of ifp"
  show "\<forall> u . rifp u u"
    using inst_ifp_refl by metis
  --"show step consistency"
  show "\<forall>s t u a. rvpeq u s t \<and> rvpeq (rcurrent s) s t \<and> True \<and> rprecondition s (rcurrent s) a \<and> True \<and> rprecondition t (rcurrent t) a \<and> rcurrent s = rcurrent t \<longrightarrow>
              rvpeq u (rstep s a) (rstep t a)"
    using inst_weakly_step_consistent by blast
  --"show step atomicity"
  show "\<forall> s a . rcurrent (rstep s a) = rcurrent s"
    using inst_step_atomicity by metis
  show " \<forall>a s u. \<not> rifp (rcurrent s) u \<and> True \<and> rprecondition s (rcurrent s) a \<longrightarrow> rvpeq u s (rstep s a)"
    using inst_local_respect by blast
  --"show cswitch is independent of state"
  show "\<forall>n s t. rcurrent s = rcurrent t \<longrightarrow> rcurrent (rcswitch n s) = rcurrent (rcswitch n t)"
    using inst_cswitch_independent_of_state by metis
  --"show cswitch consistency"
  show "\<forall>u s t n. rvpeq u s t \<longrightarrow> rvpeq u (rcswitch n s) (rcswitch n t)"
    using inst_cswitch_consistency by metis
  --"Show the empt action sequence is in @{term AS_set}"
  show "[] \<in> rAS_set"
    unfolding rAS_set_def
    by auto
  --"The invariant for the initial state, already encoded in @{term rstate_t}"
  show "True"
    by auto
  --"Step function of the invariant, already encoded in @{term rstate_t}"
  show "\<forall>s n. True \<longrightarrow> True"
    by auto
  --"The precondition does not change with a context switch"
  show "\<forall>s d n a. rprecondition s d a \<longrightarrow> rprecondition (rcswitch n s) d a"
    using precondition_after_cswitch by blast
  --"The precondition holds for the first action of each action sequence"
  show "\<forall>s d aseq. True \<and> aseq \<in> rAS_set \<and> aseq \<noteq> [] \<longrightarrow> rprecondition s d (hd aseq)"
    using prec_first_IPC_action prec_first_EV_WAIT_action prec_first_EV_SIGNAL_action
    unfolding rAS_set_def is_sub_seq_def 
    by auto
  --"The precondition holds for the next action in an action sequence, assuming the sequence is not aborted or delayed"
  show "\<forall>s a a'. (\<exists>aseq\<in>rAS_set. is_sub_seq a a' aseq) \<and> True \<and> rprecondition s (rcurrent s) a \<and> \<not> raborting s (rcurrent s) a \<and> \<not> rwaiting s (rcurrent s) a \<longrightarrow>
             rprecondition (rstep s a) (rcurrent s) a'"
    using prec_after_IPC_step prec_after_EV_SIGNAL_step prec_after_EV_WAIT_step
    unfolding rAS_set_def is_sub_seq_def
    by auto
  --"Steps of other domains do not influence the precondition"
  show "\<forall>s d a a'. rcurrent s \<noteq> d \<and> rprecondition s d a \<longrightarrow> rprecondition (rstep s a') d a"
    using prec_dom_independent by blast
  --"The invariant"
  show "\<forall>s a. True \<longrightarrow> True"
    by auto
  --"Aborting does not depend on a context switch"
  show "\<forall>n s. raborting (rcswitch n s) = raborting s"
    using aborting_switch_independent by auto
  --"Aborting does not depend on actions of other domains"
  show "\<forall>s a d. rcurrent s \<noteq> d \<longrightarrow> raborting (rstep s a) d = raborting s d"
    using aborting_dom_independent by auto
  --"Aborting is consistent"
  show "\<forall>s t u. rvpeq u s t \<longrightarrow> raborting s u = raborting t u"
    using raborting_consistent by auto
  --"Waiting does not depend on a context switch"
  show "\<forall>n s. rwaiting (rcswitch n s) = rwaiting s"
    using waiting_switch_independent by auto
  --"Waiting is consistent"
  show "\<forall>s t u a. rvpeq (rcurrent s) s t \<and> (\<forall> d \<in> rkinvolved a . rvpeq d s t) 
         \<and> rvpeq u s t  
         \<longrightarrow> rwaiting s u a = rwaiting t u a"
    unfolding Kernel.involved_def
    using waiting_consistent by auto
  --"Domains that are involved in an action may influence the domain of the action"
  show "\<forall>s a. \<forall> d \<in> rkinvolved a. rprecondition s (rcurrent s) a \<longrightarrow> rifp d (rcurrent s)"
    using involved_ifp by blast
  --"An action that is waiting does not change the state"
  show "\<forall>s a. rwaiting s (rcurrent s) a \<longrightarrow> rstep s a = s"
    using spec_of_waiting by blast
  --"Proof obligations for @{term set_error_code}. Right now, they are all trivial"
  show "\<forall>s d a' a. rcurrent s \<noteq> d \<and> raborting s d a \<longrightarrow> raborting (rset_error_code s a') d a"
    unfolding rset_error_code_def
    by auto
  show "\<forall>s t u a. rvpeq u s t \<longrightarrow> rvpeq u (rset_error_code s a) (rset_error_code t a)"
    unfolding rset_error_code_def
    by auto
  show "\<forall>s u a. \<not> rifp (rcurrent s) u \<longrightarrow> rvpeq u s (rset_error_code s a)"
    unfolding rset_error_code_def
    by (metis `\<forall>a u. rvpeq u a a`)
  show "\<forall>s a. rcurrent (rset_error_code s a) = rcurrent s"
    unfolding rset_error_code_def
    by auto
  show "\<forall>s d a a'. rprecondition s d a \<and> raborting s (rcurrent s) a' \<longrightarrow> rprecondition (rset_error_code s a') d a"
    unfolding rset_error_code_def
    by auto
  show "\<forall>s d a' a. rcurrent s \<noteq> d \<and> rwaiting s d a \<longrightarrow> rwaiting (rset_error_code s a') d a"
    unfolding rset_error_code_def
    by auto
qed

text {* Now we can instantiate CISK with some initial state, interrupt function, etc. *}

interpretation Inst:
  Controllable_Interruptible_Separation_Kernel
    rstep           -- "step function, without program stack"
    routput_f       -- "output function"
    "\<up>s0"           -- "initial state"
    rcurrent        -- "returns the currently active domain"
    rcswitch        -- "switches the currently active domain"
    "(op =) 42"     -- "interrupt function (yet unspecified)"
    rkinvolved      -- "returns a set of threads involved in the give action"
    rifp            -- "information flow policy"
    rvpeq           -- "view partitioning"
    rAS_set         -- "the set of valid action sequences"
    rinvariant      -- "the state invariant"
    rprecondition   -- "the precondition for doing an action"
    raborting       -- "condition under which an action is aborted"
    rwaiting        -- "condition under which an action is delayed"
    rset_error_code -- "updates the state. Has no meaning in the current model."
using CISK_proof_obligations_satisfied by auto

text {* The main theorem: the instantiation implements the information flow policy @{term ifp}. *}
theorem risecure:
  "Inst.isecure"
using Inst.unwinding_implies_isecure_CISK
by blast
      
end
