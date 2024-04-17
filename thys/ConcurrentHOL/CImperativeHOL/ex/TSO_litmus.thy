(*<*)
theory TSO_litmus
imports
  "../TSO_Code_Gen"
  "HOL-Library.Code_Target_Nat"
begin

(*>*)
subsection\<open> A TSO litmus test\label{sec:tso-litmus} \<close>

text\<open>

The classic TSO litmus test \<^citet>\<open>\<open>\S1\<close> in
"OwensSarkarSewell:2009"\<close>: write buffering allows both threads
to read zero, which is impossible under sequential consistency.

\<close>

definition iwp2_3_a :: "(nat \<times> nat) tso" where
  "iwp2_3_a = do {
       x \<leftarrow> tso.Ref.ref 0
     ; y \<leftarrow> tso.Ref.ref 0
     ; xvr \<leftarrow> tso.Ref.ref 0
     ; yvr \<leftarrow> tso.Ref.ref 0
     ; ( ( do { x := 1 ; yv \<leftarrow> !y ; yvr := yv } )
       \<parallel> ( do { y := 1 ; xv \<leftarrow> !x ; xvr := xv } ) )
     ; xv <- !xvr
     ; yv <- !yvr
     ; tso.return (xv, yv)
     }"

code_thms iwp2_3_a
export_code iwp2_3_a in Haskell

schematic_goal iwp2_3_a: \<comment>\<open> ``Can terminate with both threads reading 0'' \<close>
  shows "\<lblot>heap.empty, ?xs, Some (0, 0)\<rblot> \<le> prog.p2s (tso.t2p iwp2_3_a)"
supply heap.simps[simp]
apply (rule inhabits.I)
unfolding iwp2_3_a_def
apply (simp add: prog.p2s.t2p)
apply (rule inhabits.spec.bind') (* separate off the trailing MFENCE/return *)
 apply (rule inhabits.tso.bind')
  apply (rule inhabits.tso.Ref.ref[where r="Ref 0"], simp; fail)
 apply (simp add: tso.bind.returnL)
 apply (rule inhabits.tso.bind')
  apply (rule inhabits.tso.Ref.ref[where r="Ref 1"], simp)
 apply (simp add: tso.bind.returnL)
 apply (rule inhabits.tso.bind')
  apply (rule inhabits.tso.Ref.ref[where r="Ref 2"], simp)
 apply (simp add: tso.bind.returnL)
 apply (rule inhabits.tso.bind')
  apply (rule inhabits.tso.Ref.ref[where r="Ref 3"], simp)
 apply (simp add: tso.bind.returnL)
 apply (rule inhabits.tso.commit')+
 apply simp
 (* Strategy: execute the LHS, then the RHS, then drain the write buffers *)
 apply (rule inhabits.tso.bind')
  apply (simp add: tso.t2s.parallel prog.p2s.bind prog.p2s.parallel prog.p2s.t2p)
  apply (rule inhabits.spec.bind')
   (* LHS *)
   apply (rule inhabits.spec.parallelL')
     apply (rule inhabits.spec.bind')
      apply (rule inhabits.tso.bind')
       apply (rule inhabits.tso.Ref.update)
      apply (simp add: tso.bind.returnL)
      apply (rule inhabits.tso.bind')
       apply (rule inhabits.tso.Ref.lookup)
      apply (simp add: tso.bind.returnL)
      apply (rule inhabits.tso.Ref.update)
     apply (rule inhabits.tau)
     apply (simp add: spec.idle.bind_le_conv spec.idle.tso.t2s_le; fail)
    apply (simp add: spec.bind.mono spec.interference.tso.t2s_le flip: spec.bind.bind; fail)
   (* RHS *)
   apply (rule inhabits.spec.parallelR')
     apply (rule inhabits.spec.bind')
      apply (rule inhabits.tso.bind')
       apply (rule inhabits.tso.Ref.update)
      apply (simp add: tso.bind.returnL)
      apply (rule inhabits.tso.bind')
       apply (rule inhabits.tso.Ref.lookup)
      apply (simp add: tso.bind.returnL)
      apply (rule inhabits.tso.Ref.update)
     apply (rule inhabits.tau)
     apply (simp add: spec.idle.bind_le_conv spec.idle.tso.t2s_le; fail)
    apply (simp add: spec.bind.mono spec.interference.tso.t2s_le flip: spec.bind.bind; fail)
   apply clarsimp
   (* Drain LHS write buffer *)
   apply (rule inhabits.spec.parallelL')
     apply (rule inhabits.spec.bind'[OF inhabits.tso.commit])+
     apply (simp add: tso.t2s.return split_def prog.bind.returnL raw.MFENCE.Nil flip: prog.p2s.bind)
     apply (rule inhabits.tau) (* preserve interference; spec.return () is too small *)
     apply (simp add: spec.idle.p2s_le; fail)
    apply (simp add: spec.bind.mono spec.interference.tso.t2s_le flip: spec.bind.bind; fail)
   (* Drain RHS write buffer *)
   apply (rule inhabits.spec.parallelR')
     apply (rule inhabits.spec.bind'[OF inhabits.tso.commit])+
     apply (simp add: tso.t2s.return split_def prog.bind.returnL raw.MFENCE.Nil flip: prog.p2s.bind)
     apply (rule inhabits.tau) (* preserve interference; spec.return () is too small *)
     apply (simp add: spec.idle.p2s_le; fail)
    apply (simp add: prog.p2s.interference_wind_bind; fail)
   (* terminate parallel *)
   apply (simp add: prog.parallel.return flip: prog.p2s.parallel)
   apply (rule inhabits.tau)
   apply (simp add: spec.idle.p2s_le; fail)
  apply (simp add: prog.bind.returnL flip: prog.p2s.bind)
  apply (subst tso.t2s.return[symmetric])
  apply (rule inhabits.tau)
  apply (simp add: spec.idle.tso.t2s_le; fail)
 (* tail *)
 apply (simp add: tso.bind.return)
 apply (rule inhabits.tso.bind')
  apply (rule inhabits.tso.Ref.lookup)
 apply (simp add: Ref.get_def apply_writes_def tso.bind.return)
 apply (rule inhabits.tso.bind')
  apply (rule inhabits.tso.Ref.lookup)
 apply (simp add: Ref.get_def apply_writes_def tso.bind.return tso.t2s.return)
 apply (rule inhabits.prog.return)
apply (simp add: spec.bind.returnL spec.idle.p2s_le raw.MFENCE.Nil prog.bind.returnL)
apply (rule inhabits.prog.return)
done

thm iwp2_3_a[simplified apply_writes_def, simplified]

(*<*)

end
(*>*)
