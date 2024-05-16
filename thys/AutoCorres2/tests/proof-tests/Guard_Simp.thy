(*
 * Copyright (c) 2023 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)
theory Guard_Simp imports "AutoCorres2_Main.AutoCorres_Main" 
begin

install_C_file "guard_simp.c"

init-autocorres [   
  in_out_parameters = 
    inc(y:in_out) and
    inc2(y:in_out, z:in_out),
  in_out_globals = 
    shuffle,
  ts_force nondet = 
    shuffle
] "guard_simp.c"

autocorres guard_simp.c

section \<open>@{method monad_simp}\<close>

text \<open>
The idea of @{method monad_simp} is to simplify / normalise an expression of the
@{typ "('e::default, 'a, 's) spec_monad"} by using a custom setup to deal with congruence
rules which allows to propagate properties gathered by guards or conditions.
A central property of the spec monad is that partial correctness properties in the sense of
@{const runs_to_partial} can be used to obtain properties of an intermediate state that can
be utilized to derive derive equality of the remaining program. This is illustrated by
the following lemma:
\<close>

lemma 
  assumes partial[runs_to_vcg]: "f \<bullet> s ?\<lbrace>P\<rbrace>"
  assumes g: "\<And>r t. P (Result r) t \<Longrightarrow> run (g r) t = run (g' r) t"
  shows "run (f \<bind> g) s = run (f \<bind> g') s"
  apply (rule run_bind_cong)
  subgoal by simp
  subgoal by runs_to_vcg (rule g)
  done

text \<open>Note that the analog lemma does not hold for the legacy \<open>('s, 'a) nondet_monad\<close>. 
There you would need total correctness of @{term "f \<bullet> s \<lbrace>P\<rbrace>"}.
The problem there are the cases where @{term f} might fail, e.g. due to non-termination or
a failing guard. Those cases do not collapse the complete computation and we basically know
nothing about the rest of the computation and thus cannot derive equality. A
similar rule with partial correctness can be derived for 
refinement, but of course this is not as convenient as an
equality.
\<close>

text \<open>Here are examples of @{method monad_simp} propagating state dependent guards.\<close>
lemma 
"do {
   guard (\<lambda>s. IS_VALID(32 word) s y);
   guard (\<lambda>s. IS_VALID(32 word) s y) <catch> (\<lambda>_. guard (\<lambda>s. IS_VALID(32 word) s y))
 } = 
  guard (\<lambda>s. IS_VALID(32 word) s y)"
  apply (monad_simp)
  done


lemma "do {
    x \<leftarrow> guard (\<lambda>s. IS_VALID(32 word) s y0);
    _ \<leftarrow> guard (\<lambda>s. IS_VALID(32 word) s z0);
    (y, z) \<leftarrow> gets (\<lambda>s. (heap_w32 s y0, heap_w32 s z0));
    (y, z) \<leftarrow> return (inc2' y z);
    (y, z) \<leftarrow> return (y, z);
    _ \<leftarrow> guard (\<lambda>s. IS_VALID(32 word) s y0);
    _ \<leftarrow> modify (heap_w32_update (\<lambda>h. h(y0 := y)));
    _ \<leftarrow> guard (\<lambda>s. IS_VALID(32 word) s z0);
    modify (heap_w32_update (\<lambda>h. h(z0 := z)))
  } =
  do {
    _ \<leftarrow> guard (\<lambda>s. IS_VALID(32 word) s y0);
    _ \<leftarrow> guard (\<lambda>s. IS_VALID(32 word) s z0);
    (y, z) \<leftarrow> gets (\<lambda>s. (heap_w32 s y0, heap_w32 s z0));
    (y, z) \<leftarrow> return (inc2' y z);
    (y, z) \<leftarrow> return (y, z);
    _ \<leftarrow> modify (heap_w32_update (\<lambda>h. h(y0 := y)));
    modify (heap_w32_update (\<lambda>h. h(z0 := z)))
  }"
  apply (monad_simp)
  done

lemma fixes x::"32 word" shows "do {when (x > 42) (throw x); guard (\<lambda>_. \<not> x > 42); return x } = 
  do {when (x > 42) (throw x); return x }"
  apply monad_simp
  done

lemma fixes x::"32 word" shows "do {unless (x > 42) (throw x); guard (\<lambda>_. x > 42); return x } = 
  do {unless (x > 42) (throw x); return x }"
  apply monad_simp
  done

lemma "do {
    x \<leftarrow> guard (\<lambda>s::lifted_globals. IS_VALID(32 word) s y0);
    _ \<leftarrow> guard (\<lambda>s. IS_VALID(32 word) s z0);
    condition (\<lambda>_. c) (throw ()) skip;

    _ \<leftarrow> guard (\<lambda>s. IS_VALID(32 word) s y0);
    _ \<leftarrow> guard (\<lambda>s. IS_VALID(32 word) s z0);
    modify (heap_w32_update (\<lambda>h. h(z0 := z)))
  } =  
  do {
      _ \<leftarrow> guard (\<lambda>s. IS_VALID(32 word) s y0);
      _ \<leftarrow> guard (\<lambda>s. IS_VALID(32 word) s z0);
      _ \<leftarrow> when c (throw ());
      modify (heap_w32_update (\<lambda>h. h(z0 := z)))
    }"
  apply monad_simp
  done

text \<open>The \<open>simp_depth_limit\<close> is derived from the depth of the term.\<close>
lemma "do {
    _ \<leftarrow> guard (\<lambda>s::lifted_globals. IS_VALID(32 word) s y0);
    _ \<leftarrow> guard (\<lambda>s. IS_VALID(32 word) s z0);
    _ \<leftarrow> guard (\<lambda>s. IS_VALID(32 word) s y0);
      condition (\<lambda>_. c) (modify (heap_w32_update (\<lambda>h. h(z0 := z)))) ( modify (heap_w32_update (\<lambda>h. h(z0 := z))));
    _ \<leftarrow> guard (\<lambda>s. IS_VALID(32 word) s z0);
    _ \<leftarrow> guard (\<lambda>s. IS_VALID(32 word) s y0);
      condition (\<lambda>_. c) (modify (heap_w32_update (\<lambda>h. h(z0 := z)))) ( modify (heap_w32_update (\<lambda>h. h(z0 := z))));
    _ \<leftarrow> guard (\<lambda>s. IS_VALID(32 word) s z0);
    _ \<leftarrow> guard (\<lambda>s. IS_VALID(32 word) s y0);
      condition (\<lambda>_. c) (modify (heap_w32_update (\<lambda>h. h(z0 := z)))) ( modify (heap_w32_update (\<lambda>h. h(z0 := z))));
    _ \<leftarrow> guard (\<lambda>s. IS_VALID(32 word) s z0);
    _ \<leftarrow> guard (\<lambda>s. IS_VALID(32 word) s y0);
      condition (\<lambda>_. c) (modify (heap_w32_update (\<lambda>h. h(z0 := z)))) ( modify (heap_w32_update (\<lambda>h. h(z0 := z))));
    _ \<leftarrow> guard (\<lambda>s. IS_VALID(32 word) s z0);
    _ \<leftarrow> guard (\<lambda>s. IS_VALID(32 word) s y0);
      condition (\<lambda>_. c) (modify (heap_w32_update (\<lambda>h. h(z0 := z)))) ( modify (heap_w32_update (\<lambda>h. h(z0 := z))));
    _ \<leftarrow> guard (\<lambda>s. IS_VALID(32 word) s z0);
    _ \<leftarrow> guard (\<lambda>s. IS_VALID(32 word) s y0);
      condition (\<lambda>_. c) (modify (heap_w32_update (\<lambda>h. h(z0 := z)))) ( modify (heap_w32_update (\<lambda>h. h(z0 := z))));
    _ \<leftarrow> guard (\<lambda>s. IS_VALID(32 word) s z0);
    _ \<leftarrow> guard (\<lambda>s. IS_VALID(32 word) s y0);
      condition (\<lambda>_. c) (modify (heap_w32_update (\<lambda>h. h(z0 := z)))) ( modify (heap_w32_update (\<lambda>h. h(z0 := z))));
    _ \<leftarrow> guard (\<lambda>s. IS_VALID(32 word) s z0);
    _ \<leftarrow> guard (\<lambda>s. IS_VALID(32 word) s y0);
      condition (\<lambda>_. c) (modify (heap_w32_update (\<lambda>h. h(z0 := z)))) ( modify (heap_w32_update (\<lambda>h. h(z0 := z))));
    _ \<leftarrow> guard (\<lambda>s. IS_VALID(32 word) s z0);
    _ \<leftarrow> guard (\<lambda>s. IS_VALID(32 word) s y0);
      condition (\<lambda>_. c) (modify (heap_w32_update (\<lambda>h. h(z0 := z)))) ( modify (heap_w32_update (\<lambda>h. h(z0 := z))));
    _ \<leftarrow> guard (\<lambda>s. IS_VALID(32 word) s z0);
    _ \<leftarrow> guard (\<lambda>s. IS_VALID(32 word) s y0);
      condition (\<lambda>_. c) (modify (heap_w32_update (\<lambda>h. h(z0 := z)))) ( modify (heap_w32_update (\<lambda>h. h(z0 := z))));
    _ \<leftarrow> guard (\<lambda>s. IS_VALID(32 word) s z0);
    _ \<leftarrow> guard (\<lambda>s. IS_VALID(32 word) s y0);
      condition (\<lambda>_. c) (modify (heap_w32_update (\<lambda>h. h(z0 := z)))) ( modify (heap_w32_update (\<lambda>h. h(z0 := z))));
    _ \<leftarrow> guard (\<lambda>s. IS_VALID(32 word) s z0);
    _ \<leftarrow> guard (\<lambda>s. IS_VALID(32 word) s y0);
      condition (\<lambda>_. c) (modify (heap_w32_update (\<lambda>h. h(z0 := z)))) ( modify (heap_w32_update (\<lambda>h. h(z0 := z))));
    _ \<leftarrow> guard (\<lambda>s. IS_VALID(32 word) s z0);
    _ \<leftarrow> guard (\<lambda>s. IS_VALID(32 word) s y0);
      condition (\<lambda>_. c) (modify (heap_w32_update (\<lambda>h. h(z0 := z)))) ( modify (heap_w32_update (\<lambda>h. h(z0 := z))));
    _ \<leftarrow> guard (\<lambda>s. IS_VALID(32 word) s z0);
    _ \<leftarrow> guard (\<lambda>s. IS_VALID(32 word) s y0);
      condition (\<lambda>_. c) (modify (heap_w32_update (\<lambda>h. h(z0 := z)))) ( modify (heap_w32_update (\<lambda>h. h(z0 := z))));
    _ \<leftarrow> guard (\<lambda>s. IS_VALID(32 word) s z0);
    _ \<leftarrow> guard (\<lambda>s. IS_VALID(32 word) s y0);
      condition (\<lambda>_. c) (modify (heap_w32_update (\<lambda>h. h(z0 := z)))) ( modify (heap_w32_update (\<lambda>h. h(z0 := z))));
    _ \<leftarrow> guard (\<lambda>s. IS_VALID(32 word) s z0);
    _ \<leftarrow> guard (\<lambda>s. IS_VALID(32 word) s y0);
      condition (\<lambda>_. c) (modify (heap_w32_update (\<lambda>h. h(z0 := z)))) ( modify (heap_w32_update (\<lambda>h. h(z0 := z))));
    _ \<leftarrow> guard (\<lambda>s. IS_VALID(32 word) s y0);
    _ \<leftarrow> guard (\<lambda>s. IS_VALID(32 word) s z0);
    modify (heap_w32_update (\<lambda>h. h(z0 := z)))
  } =  
 do {
      _ \<leftarrow> guard (\<lambda>s. IS_VALID(32 word) s y0);
      _ \<leftarrow> guard (\<lambda>s. IS_VALID(32 word) s z0);
      _ \<leftarrow> condition (\<lambda>_. c)
             (modify (heap_w32_update (\<lambda>h. h(z0 := z))))
             (modify (heap_w32_update (\<lambda>h. h(z0 := z))));
      _ \<leftarrow> condition (\<lambda>_. c)
             (modify (heap_w32_update (\<lambda>h. h(z0 := z))))
             (modify (heap_w32_update (\<lambda>h. h(z0 := z))));
      _ \<leftarrow> condition (\<lambda>_. c)
             (modify (heap_w32_update (\<lambda>h. h(z0 := z))))
             (modify (heap_w32_update (\<lambda>h. h(z0 := z))));
      _ \<leftarrow> condition (\<lambda>_. c)
             (modify (heap_w32_update (\<lambda>h. h(z0 := z))))
             (modify (heap_w32_update (\<lambda>h. h(z0 := z))));
      _ \<leftarrow> condition (\<lambda>_. c)
             (modify (heap_w32_update (\<lambda>h. h(z0 := z))))
             (modify (heap_w32_update (\<lambda>h. h(z0 := z))));
      _ \<leftarrow> condition (\<lambda>_. c)
             (modify (heap_w32_update (\<lambda>h. h(z0 := z))))
             (modify (heap_w32_update (\<lambda>h. h(z0 := z))));
      _ \<leftarrow> condition (\<lambda>_. c)
             (modify (heap_w32_update (\<lambda>h. h(z0 := z))))
             (modify (heap_w32_update (\<lambda>h. h(z0 := z))));
      _ \<leftarrow> condition (\<lambda>_. c)
             (modify (heap_w32_update (\<lambda>h. h(z0 := z))))
             (modify (heap_w32_update (\<lambda>h. h(z0 := z))));
      _ \<leftarrow> condition (\<lambda>_. c)
             (modify (heap_w32_update (\<lambda>h. h(z0 := z))))
             (modify (heap_w32_update (\<lambda>h. h(z0 := z))));
      _ \<leftarrow> condition (\<lambda>_. c)
             (modify (heap_w32_update (\<lambda>h. h(z0 := z))))
             (modify (heap_w32_update (\<lambda>h. h(z0 := z))));
      _ \<leftarrow> condition (\<lambda>_. c)
             (modify (heap_w32_update (\<lambda>h. h(z0 := z))))
             (modify (heap_w32_update (\<lambda>h. h(z0 := z))));
      _ \<leftarrow> condition (\<lambda>_. c)
             (modify (heap_w32_update (\<lambda>h. h(z0 := z))))
             (modify (heap_w32_update (\<lambda>h. h(z0 := z))));
      _ \<leftarrow> condition (\<lambda>_. c)
             (modify (heap_w32_update (\<lambda>h. h(z0 := z))))
             (modify (heap_w32_update (\<lambda>h. h(z0 := z))));
      _ \<leftarrow> condition (\<lambda>_. c)
             (modify (heap_w32_update (\<lambda>h. h(z0 := z))))
             (modify (heap_w32_update (\<lambda>h. h(z0 := z))));
      _ \<leftarrow> condition (\<lambda>_. c)
             (modify (heap_w32_update (\<lambda>h. h(z0 := z))))
             (modify (heap_w32_update (\<lambda>h. h(z0 := z))));
      _ \<leftarrow> condition (\<lambda>_. c)
             (modify (heap_w32_update (\<lambda>h. h(z0 := z))))
             (modify (heap_w32_update (\<lambda>h. h(z0 := z))));
      modify (heap_w32_update (\<lambda>h. h(z0 := z)))
    }"
  apply monad_simp
  done

text \<open>
To achieve the goal to propagate even state dependent guards @{method monad_simp} is 
configured by supplying special congruence rules that contain syntactic markers to influence
how @{method monad_simp} descends into an expression. The basic idea is to gather
properties of guards or conditions as we descend into the expression and attempt to propagate
these properties by proving that they stay invariant.

The syntactic markers are:
\<^item> @{term "ADD_FACT P s"}: add the fact that property \<^term>\<open>P\<close> holds for the 
  current state \<^term>\<open>s\<close>.
\<^item> @{term "PRESERVED_FACTS f s r t"}: maintain those facts about state \<^term>\<open>s\<close> that 
  still hold in state \<^term>\<open>t\<close> when function \<^term>\<open>f\<close> transitions from state \<^term>\<open>s\<close> 
  to state \<^term>\<open>t\<close> while producing result \<^term>\<open>r\<close>. Moreover the theorems in @{attribute monad_simp_derive_rule} are used
  to derive facts that hold after the transition. This are added in the same mannor as
  with @{const ADD_FACT}.
\<^item> @{term "PRESERVED_FACTS_WHILE C B i s r t"}: maintain those facts about state \<^term>\<open>s\<close> that 
  still hold in state \<^term>\<open>t\<close> that can be reached by unrolling the while loop
   \<^term>\<open>whileLoop C B i\<close> and transitioning from state \<^term>\<open>s\<close> 
  to state \<^term>\<open>t\<close> while producing result \<^term>\<open>r\<close>.

Here is the set of rules that are configured:
\<close>
ML \<open>Monad_Cong_Simp.print_rules (Context.Proof @{context})\<close>
ML \<open>Monad_Cong_Simp.print_derive_rules (Context.Proof @{context})\<close>

ML \<open>Monad_Cong_Simp.print_stop_congs (Context.Proof @{context})\<close>
text \<open>The \<open>stop_congs\<close> are used to block the simplifier to descend into the subterms. They are
generated from the supplied congruence rules. In case of local definitions global congruence
rules can be supplied via @{attribute monad_simp_global_stop_cong}\<close>


text \<open>To facilitate the preservation proofs for those accumulated facts we use the 
collection of theorems @{thm monad_simp_simp}.
\<close>
thm monad_simp_simp

text \<open>Currently the setup is tuned towards preservation of \<^const>\<open>ptr_valid\<close> predicates.
To preserve such predicates we use the property that most programs do not change the 
typing information at all. Which can be expressed by a \<^const>\<open>runs_to_partial\<close> statement:

\<^term>\<open>f \<bullet> s ?\<lbrace> \<lambda>_. unchanged_typing_on UNIV s \<rbrace>\<close>

Note that autocorres attempts to prove those properties for all its outputs and collects
successful lemmas in @{thm unchanged_typing}.
\<close>
thm unchanged_typing
thm unchanged_typing_on_simps


text \<open>Autocorres applies @{method monad_simp} to all the final results. 
This is done in a staged approach: 
\<^item> First the an initial (raw) definition is derived
\<^item> Then an \<^const>\<open>unchanged_typing_on\<close> theorem is derived for that definition (if possible)
\<^item> Then this is used by @{method monad_simp} to simplify the raw definition and arrive
  at the final definition.
\<close>


context guard_simp_all_corres
begin
thm ts_def
thm raw.inc2_loop'_def inc2_loop'_def
thm raw.inc2_while'_def inc2_while'_def
thm raw.odd'.simps odd'.simps
thm raw.even'.simps even'.simps
thm raw.heap_inc2'_def heap_inc2'_def 
thm raw.cond'_def cond'_def

thm raw.fac_exit'.simps fac_exit'.simps
thm raw.dec'_def dec'_def

ML_val \<open>
Monad_Cong_Simp.print_rules (Context.Proof @{context})
\<close>

declare [[ML_print_depth=1000]]
ML_val \<open>
Monad_Cong_Simp.Data.get (Context.Proof @{context})
\<close>
lemma " heap_w32.assume_with_fresh_stack_ptr 1 (\<lambda>a. {[n]})
   (\<lambda>n\<^sub>p. heap_w32.assume_with_fresh_stack_ptr 1 (\<lambda>s. {[m]})
            (\<lambda>m\<^sub>p. do {
                  ret \<leftarrow> swap' n\<^sub>p m\<^sub>p;
                  x \<leftarrow> guard (\<lambda>s. IS_VALID(32 word) s n\<^sub>p);
                  _ \<leftarrow> guard (\<lambda>s. IS_VALID(32 word) s m\<^sub>p);
                  gets (\<lambda>s. heap_w32 s n\<^sub>p + heap_w32 s m\<^sub>p)
                })) = 
  heap_w32.assume_with_fresh_stack_ptr 1 (\<lambda>a. {[n]})
     (\<lambda>t. heap_w32.assume_with_fresh_stack_ptr 1 (\<lambda>s. {[m]}) (\<lambda>ta. do {
        ret \<leftarrow> swap' t ta;
        gets (\<lambda>s. heap_w32 s t + heap_w32 s ta)
      }))"
  supply [[verbose=6]]
  apply monad_simp
  done

lemma " heap_s32.with_fresh_stack_ptr 1 (\<lambda>a. {[n]})
   (\<lambda>n\<^sub>p. heap_s32.with_fresh_stack_ptr 1 (\<lambda>s. {[m]})
            (\<lambda>m\<^sub>p. do {
  
                  x \<leftarrow> guard (\<lambda>s. IS_VALID(32 signed word) s n\<^sub>p);
                  _ \<leftarrow> guard (\<lambda>s. IS_VALID(32 signed word) s m\<^sub>p);
                  gets (\<lambda>s. heap_s32 s n\<^sub>p + heap_s32 s m\<^sub>p)
                })) = 
    heap_s32.with_fresh_stack_ptr 1 (\<lambda>a. {[n]})
     (\<lambda>n\<^sub>p. heap_s32.with_fresh_stack_ptr 1 (\<lambda>s. {[m]}) (\<lambda>m\<^sub>p. gets (\<lambda>s. heap_s32 s n\<^sub>p + heap_s32 s m\<^sub>p)))"
  supply [[verbose=0]]
  apply monad_simp
  done


end


context ts_definition_shuffle
begin
thm shuffle'_def

text \<open>Here we use @{method monad_simp} to remove the nested guard about
\<^term>\<open> ptr_span (buf +\<^sub>p - i) \<subseteq> \<G>\<close>. So this kind of technique might be useful 
to propagate assumptions about the inputs of a function to simplify the
program, (e.g. by solving some guards) before running @{method runs_to_vcg} on
the program.
\<close>

lemma 
  assumes G: "\<And>i. i \<le> 4 \<Longrightarrow> ptr_span (buf +\<^sub>p - i) \<subseteq> \<G>"
  shows "shuffle' buf len = 
    condition (\<lambda>s. 4 < uint len)
      (Spec_Monad.return 0x2A)
      (do {
         (i, y) \<leftarrow>
           whileLoop (\<lambda>(i, tmp) s. i < uint len)
             (\<lambda>(i, tmp). do {
                   _ \<leftarrow> Spec_Monad.guard (\<lambda>s. 0 \<le> i);
                   _ \<leftarrow> Spec_Monad.guard (\<lambda>s. IS_VALID(8 word) s (buf +\<^sub>p - i));
                   tmp \<leftarrow>
                     Spec_Monad.gets
                      (\<lambda>s. tmp ||
                            (UCAST(8 \<rightarrow> 32) (heap_w8 s (buf +\<^sub>p - i)) <<
                             unat ((word_of_int i * 8)::32 signed word)));
                   Spec_Monad.return (i + 1, tmp)
                 })
            (0, 0);
         Spec_Monad.return y
       })"
  unfolding shuffle'_def
  apply (monad_simp simp add: G simp del: size_simps)
  done


lemma "do {x \<leftarrow> return n; 
         unless (x = 42) (throw e);
         (i, y) \<leftarrow>
           whileLoop (\<lambda>(i, tmp) s. i < uint len)
             (\<lambda>(i, tmp). do {
                   _ \<leftarrow> Spec_Monad.guard (\<lambda>s. 0 \<le> i);
                   _ \<leftarrow> Spec_Monad.guard (\<lambda>s. IS_VALID(8 word) s (buf +\<^sub>p - i));
                   tmp \<leftarrow>
                     Spec_Monad.gets
                      (\<lambda>s. tmp ||
                            (UCAST(8 \<rightarrow> 32) (heap_w8 s (buf +\<^sub>p - i)) <<
                             unat ((word_of_int i * 8)::32 signed word)));
                   Spec_Monad.return (i + 1, tmp)
                 })
            (0, x);
         return x} = 
   do {x \<leftarrow> return n; 
         unless (x = 42) (throw e);
         (i, y) \<leftarrow>
           whileLoop (\<lambda>(i, tmp) s. i < uint len)
             (\<lambda>(i, tmp). do {
                   _ \<leftarrow> Spec_Monad.guard (\<lambda>s. 0 \<le> i);
                   _ \<leftarrow> Spec_Monad.guard (\<lambda>s. IS_VALID(8 word) s (buf +\<^sub>p - i));
                   tmp \<leftarrow>
                     Spec_Monad.gets
                      (\<lambda>s. tmp ||
                            (UCAST(8 \<rightarrow> 32) (heap_w8 s (buf +\<^sub>p - i)) <<
                             unat ((word_of_int i * 8)::32 signed word)));
                   Spec_Monad.return (i + 1, tmp)
                 })
            (0, 42);
         return 42}"
  apply monad_simp
  done


lemma "do {x \<leftarrow> return n; 
         unless (x = 42) (throw e);
         (i, y, p) \<leftarrow>
           whileLoop (\<lambda>(i, tmp, p::(nat \<times> nat)) s. i < uint len)
             (\<lambda>(i, tmp, p). do {
                   _ \<leftarrow> Spec_Monad.guard (\<lambda>s. 0 \<le> i);
                   _ \<leftarrow> Spec_Monad.guard (\<lambda>s. IS_VALID(8 word) s (buf +\<^sub>p - i));
                   tmp \<leftarrow>
                     Spec_Monad.gets
                      (\<lambda>s. tmp ||
                            (UCAST(8 \<rightarrow> 32) (heap_w8 s (buf +\<^sub>p - i)) <<
                             unat ((word_of_int i * 8)::32 signed word)));
                   Spec_Monad.return (i + 1, tmp, p)
                 })
            (0, x, p);
         return x} = 
   do {
      x \<leftarrow> return n;
      _ \<leftarrow> unless (x = 42) (throw e);
      (i, y, x3, x4) \<leftarrow>
        whileLoop (\<lambda>(i, tmp, x3, x4) s. i < uint len)
          (\<lambda>(i, tmp, x3, x4). do {
                _ \<leftarrow> guard (\<lambda>s. 0 \<le> i);
                _ \<leftarrow> guard (\<lambda>s. IS_VALID(8 word) s (buf +\<^sub>p - i));
                tmp \<leftarrow>
                  gets (\<lambda>s. tmp || (UCAST(8 \<rightarrow> 32) (heap_w8 s (buf +\<^sub>p - i)) << unat ((word_of_int i * 8)::32 signed word)));
                return (i + 1, tmp, x3, x4)
              })
         (0, 42, p);
      return 42
    } "
  apply monad_simp
  done

lemma 
 "condition (\<lambda>s. n = g_'' s) 
   (return n) (return (n + 1)) = 
 condition (\<lambda>s. n = g_'' s) 
   (return n) (return (n + 1))"
  apply monad_simp
  done

text \<open>This lemma demonstrates the tupled-eta expansion of @{method monad_simp}. Note that on the
left hand side the initialiser of the \<^const>\<open>whileLoop\<close> is contracted. So there is no bound variables
in \<^const>\<open>bind\<close>.\<close>

lemma "(bind (return (0,0)) (
           whileLoop (\<lambda>(i, tmp) s. i < uint len)
             (\<lambda>(i, tmp). do {
                   _ \<leftarrow> Spec_Monad.guard (\<lambda>s. 0 \<le> i);
                   _ \<leftarrow> Spec_Monad.guard (\<lambda>s. IS_VALID(8 word) s (buf +\<^sub>p - i));
                   _ \<leftarrow> Spec_Monad.guard (\<lambda>s. 0 \<le> i);
                   tmp \<leftarrow>
                     Spec_Monad.gets
                      (\<lambda>s. tmp ||
                            (UCAST(8 \<rightarrow> 32) (heap_w8 s (buf +\<^sub>p - i)) <<
                             unat ((word_of_int i * 8)::32 signed word)));
                   Spec_Monad.return (i + 1, tmp)
                 })
  )) = do {
      (x1, x2) \<leftarrow> return (0, 0);
      whileLoop (\<lambda>(i, tmp) s. i < uint len)
        (\<lambda>(i, tmp). do {
              _ \<leftarrow> guard (\<lambda>s. 0 \<le> i);
              _ \<leftarrow> guard (\<lambda>s. IS_VALID(8 word) s (buf +\<^sub>p - i));
              tmp \<leftarrow>
                gets
                 (\<lambda>s. tmp ||
                       (UCAST(8 \<rightarrow> 32) (heap_w8 s (buf +\<^sub>p - i)) << unat ((word_of_int i * 8)::32 signed word)));
              return (i + 1, tmp)
            })
       (x1, x2)
    }"
  apply monad_simp
  done

end

lemma "condition (\<lambda>s. x < (5::nat)) (case v of (x, y) \<Rightarrow> (g x y::('a, 's) res_monad)) (h x) = 
       condition (\<lambda>s. x < (5::nat)) (case v of (x, y) \<Rightarrow> (g x y::('a, 's) res_monad)) (h x) "
  by (monad_simp)

lemma "condition (\<lambda>s. x < (5::nat)) 
         (case v of (x1, y1, z1) \<Rightarrow> (do {guard (\<lambda>_. x < 5); g x1 z1 y1})) 
         (h x) = 
       condition (\<lambda>s. x < 5)
         (case v of (x1, y1, z1) \<Rightarrow> g x1 z1 y1)
          (h x) "
  apply (monad_simp)
  done


lemma 
  assumes "X = Y"
  shows
"condition (\<lambda>s. x < (5::nat)) 
         (case v of (x1, y1, z1) \<Rightarrow> (do {guard (\<lambda>_. x < 5); g x1 z1 y1})) 
         (h x) = 
       condition (\<lambda>s. x < 5)
         (case v of (x1, y1, z1) \<Rightarrow> g x1 z1 y1)
          (h x)  \<Longrightarrow> X = Y"
  apply (monad_simp) \<comment> \<open>no \<^const>\<open>STOP\<close> should be in premises\<close>
  by (rule assms)

lemma "(when ((x::nat) > 2) (do {guard (\<lambda>_. x > 2); return ()})) = when (2 < x) skip"
  by (monad_simp)

end


