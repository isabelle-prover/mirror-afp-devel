(*
 * Copyright (C) 2014 NICTA
 * All rights reserved.
 *)

(* Author: David Cock - David.Cock@nicta.com.au *)

section "Loops"

theory LoopExamples imports "../pGCL" begin

text {* Reasoning about loops in pGCL is mostly familiar, in particular in the use of invariants.
Proving termination for truly probabilistic loops is slightly different: We appeal to a 0--1 law
to show that the loop terminates \emph{with probability 1}.  In our semantic model, terminating
with certainty and with probability 1 are exactly equivalent. *}

subsection {* Guaranteed Termination *}

text {* We start with a completely classical loop, to show that standard techniques apply. Here, we
have a program that simply decrements a counter until it hits zero: *}

definition countdown :: "int prog"
where
  "countdown = do (\<lambda>x. 0 < x) \<longrightarrow> Apply (\<lambda>s. s - 1) od"

text {* Clearly, this loop will only terminate from a state where @{term "0 \<le> x"}. This is, in fact,
also a loop invariant. *}

definition inv_count :: "int \<Rightarrow> bool"
where
  "inv_count = (\<lambda>x. 0 \<le> x)"

text {* Read @{term "wp_inv G body I"} as: @{term I} is an invariant of the loop
@{term "do G \<longrightarrow> body od"}, or @{term "\<guillemotleft>G\<guillemotright> && I \<tturnstile> wp body I"}. *}

lemma wp_inv_count:
  "wp_inv (\<lambda>x. 0 < x) (Apply (\<lambda>s. s - 1)) \<guillemotleft>inv_count\<guillemotright>"
  unfolding wp_inv_def inv_count_def wp_eval o_def
proof(clarify, cases)
  fix x::int
  assume "0 \<le> x"
  then show "\<guillemotleft>\<lambda>x. 0 < x\<guillemotright> x * \<guillemotleft>\<lambda>x. 0 \<le> x\<guillemotright> x \<le> \<guillemotleft>\<lambda>x. 0 \<le> x\<guillemotright> (x - 1)"
    by(simp add:embed_bool_def)
next
  fix x::int
  assume "\<not> 0 \<le> x"
  then show "\<guillemotleft>\<lambda>x. 0 < x\<guillemotright> x * \<guillemotleft>\<lambda>x. 0 \<le> x\<guillemotright> x \<le> \<guillemotleft>\<lambda>x. 0 \<le> x\<guillemotright> (x - 1)"
    by(simp add:embed_bool_def)
qed

text {* This example is contrived to give us an obvious variant, or measure function: the counter
itself. *}

lemma term_countdown:
  "\<guillemotleft>inv_count\<guillemotright> \<tturnstile> wp countdown (\<lambda>s. 1)"
  unfolding countdown_def
proof(intro loop_term_nat_measure[where m="\<lambda>x. nat (max x 0)"] wp_inv_count)
  let ?p = "Apply (\<lambda>x. x - 1::int)"

  txt {* As usual, well-definedness is trivial. *}
  show "well_def ?p"
    by(rule wd_intros)

  txt {* A measure of 0 imples termination. *}
  show "\<And>x. nat (max x 0) = 0 \<longrightarrow> \<not> 0 < x"
    by(auto)

  txt {* This is the meat of the proof: that the measure must decrease,
    whenever the invariant holds.  Note that the invariant is essential
    here, as if @{term "x \<le> 0"}, the measure will \emph{not} decrease.

    This is the kind of proof that the VCG is good at.  It leaves a purely
    logical goal, which we can solve with auto. *}
  show "\<And>n. \<guillemotleft>\<lambda>x. nat (max x 0) = Suc n\<guillemotright> && \<guillemotleft>inv_count\<guillemotright> \<tturnstile>
         wp ?p \<guillemotleft>\<lambda>x. nat (max x 0) = n\<guillemotright>"
    unfolding inv_count_def
    by(pvcg,
       auto simp:  o_def exp_conj_std_split[symmetric]
            intro: implies_entails)
qed

subsection {* Probabilistic Termination *}

text {* Loops need not terminate deterministically: it is sufficient to terminate with probability
1. Here we show the intuitively obvious result that by flipping a coin repeatedly, you will
eventually see heads. *}

type_synonym coin = bool
definition "Heads = True"
definition "Tails = False"

definition
  flip :: "coin prog"
where
  "flip = Apply (\<lambda>_. Heads) \<^bsub>(\<lambda>s. 1/2)\<^esub>\<oplus> Apply (\<lambda>_. Tails)"

text {* We can't define a measure here, as we did previously, as neither of the
  two possible states guarantee termination. *}
definition
  wait_for_heads :: "coin prog"
where
  "wait_for_heads = do (op \<noteq> Heads) \<longrightarrow> flip od"

text {* Nonetheless, we can show termination .*}
lemma wait_for_heads_term:
  "\<lambda>s. 1 \<tturnstile> wp wait_for_heads (\<lambda>s. 1)"
  unfolding wait_for_heads_def
  txt {* We use one of the zero-one laws for termination, specifically that
    if, from every state there is a nonzero probability of satisfying the
    guard (and thus terminating) in a single step, then the loop terminates
    from \emph{any} state, with probability 1. *}
proof(rule termination_0_1)
  show "well_def flip"
    unfolding flip_def
    by(auto intro:wd_intros)

  txt {* We must show that the loop body is deterministic, meaning that
    it cannot diverge by itself. *}
  show "maximal (wp flip)"
    unfolding flip_def by(auto intro:max_intros)

  txt {* The verification condition for the loop body is one-step-termination,
    here shown to hold with probability 1/2.  As usual, this result falls to
    the VCG. *}
  show "\<lambda>s. 1/2 \<tturnstile> wp flip \<guillemotleft>\<N> (op \<noteq> Heads)\<guillemotright>"
    unfolding flip_def
    by(pvcg, simp add:o_def Heads_def Tails_def)

  txt {* Finally, the one-step escape probability is non-zero. *}
  show "(0::real) < 1/2" by(simp)
qed

end
