(*  Title: thys/Rec_Ex.thy
    Author: Franz Regensburger (FABR) 03/2022
 *)

section \<open>Examples for Recursive Functions based on Rec\_def\<close>

theory Rec_Ex
  imports Rec_Def
begin


definition plus_2 :: "recf"
  where
    "plus_2 = (Cn 1 s [s])"

lemma "rec_exec plus_2 [0] = Suc (Suc 0)"
  unfolding plus_2_def
proof -
  have "rec_exec (Cn 1 s [s]) [0] = rec_exec s (map (\<lambda> a. rec_exec a [0]) [s])"
    by auto
  also have "... = rec_exec s [Suc 0]"
    by auto
  also have "... = Suc (Suc 0)"
    by auto
  finally show "rec_exec (Cn 1 s [s]) [0] = Suc (Suc 0)" .
qed

lemma "rec_exec plus_2 [2] = 4"
  unfolding plus_2_def
 by auto

lemma "rec_exec plus_2 [0] = 2"
  unfolding plus_2_def
 by auto

text \<open>The arity parameter given to the constructors of recursive functions
is not checked during execution by the interpreter.

See the next example where we
run @{term "pls_2"} with two arguments instead of only one.
\<close>

lemma "rec_exec plus_2 [2,3] = 4"
  unfolding plus_2_def
 by auto

lemma "rec_exec plus_2 [2,3] = 4"
  unfolding plus_2_def
 by auto

text \<open>What is the purpose of the arity parameter?

   The argument 1 of the constructors, which is supposed to be the arity,
   is completely ignored by @{term "rec_exec"}.
   However, for proofing termination, we need a correct arity specification.
\<close>

lemma "terminate plus_2 [2]"
  unfolding plus_2_def
proof (rule Rec_Def.terminate.termi_cn)
  show "terminate s (map (\<lambda>g. rec_exec g [2]) [s])"
  proof -
    have "(map (\<lambda>g. rec_exec g [2]) [s]) = [rec_exec s [2]]" by auto
    then show ?thesis using termi_s by auto
  qed
next
  show "\<forall>g\<in>set [s]. terminate g [2]" by (auto simp add: termi_s)
next
 (*  1. length [2] = 8
    ahh: we need the correct arity for proving the predicate termination
 *)
  show "length [2] = 1" by auto
qed

lemma "terminate plus_2 [2]"
  unfolding plus_2_def
  by (rule Rec_Def.terminate.termi_cn) (auto simp add: termi_s)

text \<open>If we try to proof termination of a run with superfluous arguments, we are stuck.
We need the correct arity for proving the predicate termination.\<close>

lemma "terminate plus_2 [2,3]"
  unfolding plus_2_def
proof (rule Rec_Def.terminate.termi_cn)
  show "terminate s (map (\<lambda>g. rec_exec g [2, 3]) [s])"
    by (auto simp add: termi_s)
next
  show "\<forall>g\<in>set [s]. terminate g [2, 3]"
  proof
    fix g
    assume "g \<in> set [s]"
    then show "terminate g [2, 3]"
    proof -
      have "terminate s [2, 3]"
        (* this, we cannot prove based on the inductive definition of s *)
        oops


end
