(*
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory explosion imports
  "AutoCorres2_Main.AutoCorres_Main"
begin


install_C_file "explosion.c"

text \<open>The sequence of unitialised struct variables caused autocorres to explode in performace.\<close>



autocorres [] "explosion.c"

text \<open>Now it takes around 10-12 seconds on a 2,6 GHz Intel Core i7 Mac Pro. \<close>


context explosion_all_impl

begin

lemma "caller' n m k = do { ret <- return (same' n);
                    reta <- return (same' n);
                    retb <- return (same' n);
                    retc <- return (same' n);
                    retd <- return (same' n);
                    rete <- return (same' n);
                    retf <- return (same' n);
                    retg <- return (same' n);
                    reth <- return (same' n);
                    reti <- return (same' n);
                    retj <- return (same' n);
                    retk <- return (same' n);
                    glob_add' ret 1;
                    glob_add' reta 1;
                    glob_add' retb 1;
                    glob_add' retc 1;
                    glob_add' retd 1;
                    glob_add' rete 1;
                    glob_add' retf 1;
                    glob_add' retg 1;
                    glob_add' reth 1;
                    glob_add' reti 1;
                    glob_add' retj 1;
                    glob_add' retk 1;
                    gets (\<lambda>s. sint (G_'' s))
                 }"
  by (simp add:  caller'_def)
end

section \<open>What was going wrong before?\<close>

(* The simplifier explosion rule *)
thm L2_unknown_bind

text \<open>When local variables are not initialized this is represented by @{const "L2_unknown"} in
the monad, which models a nondeterministic value assigned to the variable. AutoCorres attempts to
simplify concerns by getting rid of the nondeterministic assignment in case the local variable will
properly be "assigned before use" in the code. This simplification was  building on 
@{thm L2_unknown_bind}. Note that the function @{term "f"} is duplicated in the precondition. Also
note that the simplifier will work buttom up. So whenever a sequence of unitialized variables 
appears, the simiplifiyer tries to simplify the last one first, in case this fails it goes one level
up and then attempts to simplify just the same goal again, as it works on the precondition.
The simplifier failed, because the initialisation of the struct was split into
two assignments which it did not fuse.

You can watch the following trace to see what as going on. Watch for

\<^verbatim>\<open>Applying instance of rewrite rule "L2Peephole.L2_unknown_bind"\<close>
\<close>
declare [[simp_trace=true, simp_depth_limit=50]]
unbundle clocals_string_embedding

lemma " 
     (L2_seq (L2_unknown [\<S> ''ret__int''])
       (\<lambda>ret__int.
           L2_seq (L2_unknown [\<S> ''p0''])
            (\<lambda>p0. L2_seq (L2_seq (L2_call (l2_same' undefined n) (\<lambda>x. x) []) (\<lambda>ret. L2_gets (\<lambda>s. ret) [\<S> ''retval'']))
                   (\<lambda>ret__int.
                       L2_seq (L2_gets (\<lambda>s. a_C_update (\<lambda>_. ret__int) p0) [\<S> ''p0''])
                        (\<lambda>p0. L2_seq (L2_gets (\<lambda>s. b_C_update (\<lambda>_. 1) p0) [\<S> ''p0''])
                               (\<lambda>p0. L2_seq (L2_seq (L2_call (l2_glob_add' undefined (A_C p0) (B_C p0)) (\<lambda>x. x) []) (\<lambda>ret. L2_skip))
                                      (\<lambda>_. L2_seq (L2_gets G_' [\<S> ''ret''])
                                            (\<lambda>ret__int.
                                                L2_seq (L2_gets (\<lambda>s. Return) [\<S> ''global_exn_var''])
                                                 (\<lambda>global_exn_var. L2_gets (\<lambda>_. ret__int) [\<S> ''ret''])))))))))
     = XXX"
  apply (tactic \<open>
simp_tac (put_simpset AUTOCORRES_SIMPSET @{context} addsimps @{thms  L2_unknown_bind}  ) 1
  \<close>)
  oops


declare [[simp_trace=false]]

text \<open>We improved that situation by augmenting the simplification rules for records 
(generated for structs) and propagating them via the simproc ML\<open>L2Opt.l2_gets_bind_simproc\<close>.


Sequences of record-updates that add up to a complete record are replaced by the constructor.
This captures the C-ideom that a struct is completely assigned before use, by a sequence of
assignments to its fields. 
\<close>

thm POINT_C_idupdates
lemma "b_C_update (\<lambda>_. b) (a_C_update (\<lambda>_. a) p) = POINT_C a b"
  by simp


text \<open>Moreover the specialised rule @{thm L2_unknown_bind_unbound} will simplify 
the @{term "L2_unknown"} without any precondition.
\<close>

thm L2_unknown_bind_unbound

lemma "(L2_seq (L2_unknown [\<S> ''ret__int''])
       (\<lambda>ret__int.
           L2_seq (L2_unknown [\<S> ''p0''])
            (\<lambda>p0. L2_seq (L2_seq (L2_call (l2_same' undefined n) (\<lambda>x. x) []) (\<lambda>ret. L2_gets (\<lambda>s. ret) [\<S> ''retval'']))
                   (\<lambda>ret__int.
                       L2_seq_gets (a_C_update (\<lambda>_. ret__int) p0) [\<S> ''p0'']
                        (\<lambda>p0. L2_seq_gets (b_C_update (\<lambda>_. 1) p0) [\<S> ''p0'']
                               (\<lambda>p0. L2_seq (L2_seq (L2_call (l2_glob_add' undefined (a_C p0) (b_C p0)) (\<lambda>x. x) []) (\<lambda>ret. L2_skip))
                                      (\<lambda>_. L2_seq (L2_gets G_' [\<S> ''ret''])
                                            (\<lambda>ret__int.
                                                L2_seq_gets (\<lambda>s. Return) [\<S> ''global_exn_var'']
                                                 (\<lambda>global_exn_var. L2_gets (\<lambda>_. ret__int) [\<S> ''ret''])))))))))
     = 
    L2_seq (L2_seq (L2_call (l2_same' undefined n) (\<lambda>x. x) []) (\<lambda>ret. L2_gets (\<lambda>s. ret) [\<S> ''retval'']))
     (\<lambda>ret__int.
         L2_seq
          (L2_seq (L2_call (l2_glob_add' undefined (a_C (POINT_C ret__int 1)) (b_C (POINT_C ret__int 1))) (\<lambda>x. x) []) (\<lambda>ret. L2_skip))
          (\<lambda>_. L2_seq (L2_gets G_' [\<S> ''ret'']) (\<lambda>ret__int. L2_gets (\<lambda>_. ret__int) [\<S> ''ret''])))"
  apply (tactic \<open>
let
val record_ss = RecursiveRecordPackage.get_simpset (Proof_Context.theory_of @{context});
val autocorres_record_ss = (merge_ss (AUTOCORRES_SIMPSET, record_ss));

in
simp_tac (put_simpset autocorres_record_ss @{context} addsimps @{thms L2_unknown_bind_unbound} 
  addsimprocs [L2Opt.l2_marked_gets_bind_simproc]  
  |> Simplifier.add_cong @{thm L2_marked_seq_gets_cong} ) 1
end
\<close>)
  done


end