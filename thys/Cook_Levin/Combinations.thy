section \<open>Combining Turing machines\label{s:tm-combining}\<close>

theory Combinations
  imports Basics "HOL-Eisbach.Eisbach"
begin

text \<open>
This section describes how we can combine Turing machines in the way of
traditional control structures found in structured programming, namely
sequences, branching, and iterating. This allows us to build complex Turing
machines from simpler ones and analyze their behavior and running time.  Thanks
to some syntactic sugar the result may even look like a programming language,
but it is really more like a ``construction kit'' than a ``true'' programming
language with small and big step semantics or Hoare rules. Instead we will
merely have some lemmas for proving @{const transforms} statements for the
combined machines.

The remaining sections of this chapter will provide us with concrete Turing
machines to combine.
\<close>


subsection \<open>Relocated machines\<close>

text \<open>
If we use a Turing machine $M$ as part of another TM and there are $q$ commands
before $M$, then $M$'s target states will be off by $q$. This can be fixed by
adding $q$ to all target states of all commands in $M$, an operation we call
\emph{relocation}.
\<close>

definition relocate_cmd :: "nat \<Rightarrow> command \<Rightarrow> command" where
  "relocate_cmd q cmd rs \<equiv> (fst (cmd rs) + q, snd (cmd rs))"

lemma relocate_cmd_head: "relocate_cmd q cmd rs [~] j = cmd rs [~] j"
  using relocate_cmd_def by simp

lemma sem_relocate_cmd: "sem (relocate_cmd q cmd) cfg = (sem cmd cfg) <+=> q"
proof-
  let ?cmd' = "relocate_cmd q cmd"
  let ?rs = "read (snd cfg)"
  have "?cmd' ?rs = (fst (cmd ?rs) + q, snd (cmd ?rs))"
    by (simp add: relocate_cmd_def)
  then show ?thesis
    using sem by (metis (no_types, lifting) fst_conv snd_conv)
qed

definition relocate :: "nat \<Rightarrow> machine \<Rightarrow> machine" where
  "relocate q M \<equiv> map (relocate_cmd q) M"

lemma relocate:
  assumes "M' = relocate q M" and "i < length M"
  shows "(M' ! i) r = (fst ((M ! i) r) + q, snd ((M ! i) r))"
  using assms relocate_def relocate_cmd_def by simp

lemma sem_relocate:
  assumes "M' = relocate q M" and "i < length M"
  shows "sem (M' ! i) cfg = sem (M ! i) cfg <+=> q"
  using assms relocate_def sem_relocate_cmd by simp

lemma turing_command_relocate_cmd:
  assumes "turing_command k Q G cmd"
  shows "turing_command k (Q + q) G (relocate_cmd q cmd)"
  using assms relocate_cmd_def turing_commandD by auto

lemma turing_command_relocate:
  assumes "M' = relocate q M" and "turing_machine k G M" and "i < length M"
  shows "turing_command k (length M + q) G (M' ! i)"
proof
  fix gs :: "symbol list"
  assume gs: "length gs = k"
  have tc: "turing_command k (length M) G (M ! i)"
    using turing_machine_def assms(2,3) by simp
  show "length ([!!] (M' ! i) gs) = length gs"
    using gs turing_commandD(1)[OF tc] assms(1,3) relocate by simp
  show "(M' ! i) gs [.] 0 = gs ! 0" if "k > 0"
    using gs turing_commandD(3)[OF tc] assms(1,3) relocate that by simp
  show "[*] ((M' ! i) gs) \<le> length M + q"
    using gs turing_commandD(4)[OF tc] assms(1,3) relocate by simp
  show "(\<And>i. i < length gs \<Longrightarrow> gs ! i < G) \<Longrightarrow>
       j < length gs \<Longrightarrow> (M' ! i) gs [.] j < G" for j
    using gs turing_commandD(2)[OF tc] assms(1,3) relocate by simp
qed

lemma length_relocate: "length (relocate q M) = length M"
  by (simp add: relocate_def)

lemma relocate_jump_targets:
  assumes "turing_machine k G M"
    and "M' = relocate q M"
    and "i < length M"
    and "length rs = k"
  shows "fst ((M' ! i) rs) \<le> length M + q"
  using turing_machine_def relocate_def assms relocate
  by (metis turing_commandD(4) diff_add_inverse2 fst_conv le_diff_conv nth_mem)

lemma relocate_zero: "relocate 0 M = M"
  unfolding relocate_def relocate_cmd_def by simp


subsection \<open>Sequences\<close>

text \<open>
To execute two Turing machines sequentially we concatenate the two machines,
relocating the second one by the length of the first one. In this way the
halting state of the first machine becomes the start state of the second
machine.
\<close>

definition turing_machine_sequential :: "machine \<Rightarrow> machine \<Rightarrow> machine" (infixl ";;" 55) where
  "M1 ;; M2 \<equiv> M1 @ (relocate (length M1) M2)"

text \<open>
If the number of tapes and the alphabet size match, the concatenation of two
Turing machines is again a Turing machine.
\<close>

lemma turing_machine_sequential_turing_machine [intro, simp]:
  assumes "turing_machine k G M1" and "turing_machine k G M2"
  shows "turing_machine k G (M1 ;; M2)" (is "turing_machine k G ?M")
proof
  show 1: "k \<ge> 2"
    using assms(1) turing_machine_def by simp
  show 2: "G \<ge> 4"
    using assms(1) turing_machine_def by simp
  have len: "length ?M = length M1 + length M2"
    using relocate_def turing_machine_sequential_def by simp
  show 3: "turing_command k (length ?M) G (?M ! i)" if "i < length ?M" for i
  proof (cases "i < length M1")
    case True
    then show ?thesis
      using turing_machineD[OF assms(1)] turing_machine_sequential_def len turing_command_mono
      by (metis (no_types, lifting) le_add1 nth_append)
  next
    case False
    then have "i - (length M1) < length M2" (is "?i < length M2")
      using False that len by simp
    then have "turing_command k (length ?M) G ((relocate (length M1) M2) ! ?i)"
      using assms(2) turing_command_relocate len by (simp add: add.commute)
    moreover have "?M ! i = (relocate (length M1) M2) ! ?i"
      using False by (simp add: nth_append turing_machine_sequential_def)
    ultimately show ?thesis
      by simp
  qed
qed

lemma turing_machine_sequential_empty: "turing_machine_sequential [] M = M"
  unfolding turing_machine_sequential_def using relocate_zero by simp

lemma turing_machine_sequential_nth:
  assumes "M = M1 ;; M2" and "p < length M2"
  shows "M ! (p + length M1) = relocate_cmd (length M1) (M2 ! p)"
proof-
  let ?r = "relocate (length M1) M2"
  have "M = M1 @ ?r"
    using assms(1) turing_machine_sequential_def by simp
  then have "M ! (p + length M1) = ?r ! p"
    by (simp add: nth_append)
  then show ?thesis
    using assms(2) relocate_def by simp
qed

lemma turing_machine_sequential_nth':
  assumes "M = M1 ;; M2" and "length M1 \<le> q" and "q < length M"
  shows "M ! q = relocate_cmd (length M1) (M2 ! (q - length M1))"
  using assms turing_machine_sequential_nth length_relocate turing_machine_sequential_def
  by (metis (no_types, lifting) add.assoc diff_add length_append less_add_eq_less)

lemma "length_turing_machine_sequential":
  "length (turing_machine_sequential M1 M2) = length M1 + length M2"
  using turing_machine_sequential_def relocate_def by simp

lemma exe_relocate:
  "exe (M1 ;; M2) (cfg <+=> length M1) = (exe M2 cfg) <+=> length M1 "
  using sem_relocate_cmd sem_state_indep exe_def turing_machine_sequential_nth length_turing_machine_sequential
  by (smt (verit, ccfv_SIG) add.commute diff_add_inverse2 fst_conv le_add2 less_diff_conv2 snd_conv)

lemma execute_pre_append:
  assumes "halts M1 cfg" and "fst cfg = 0" and "t \<le> running_time M1 cfg "
  shows "execute ((M0 ;; M1) @ M2) (cfg <+=> length M0) t = (execute M1 cfg t) <+=> length M0"
  using assms(3)
proof (induction t)
  case 0
  then show ?case
    by simp
next
  case (Suc t)
  let ?l0 = "length M0"
  let ?M = "(M0 ;; M1) @ M2"
  let ?cfg_t = "execute ?M (cfg <+=> ?l0) t"
  let ?cfg1_t = "execute M1 cfg t"
  let ?cmd1 = "M1 ! (fst ?cfg1_t)"
  let ?cmd = "?M ! (fst ?cfg_t)"
  have *: "?cfg1_t <+=> ?l0 = ?cfg_t"
    using Suc by simp
  then have "fst (?cfg1_t <+=> ?l0) = fst ?cfg_t"
    by simp
  then have 2: "fst ?cfg1_t + ?l0 = fst ?cfg_t"
    by simp
  from * have sndeq: "snd ?cfg1_t = snd ?cfg_t"
    by (metis snd_conv)
  have "fst (execute M1 cfg t) \<le> length M1"
    using halts_impl_le_length assms(1) halts_def by blast
  moreover have "fst ?cfg1_t \<noteq> length M1"
    using Suc.prems running_time_def wellorder_Least_lemma(2) by fastforce
  ultimately have 1: "fst ?cfg1_t < length M1"
    by simp
  with 2 have "relocate_cmd ?l0 ?cmd1 = (M0 ;; M1) ! (fst ?cfg1_t + ?l0)"
    by (metis turing_machine_sequential_nth)
  then have "relocate_cmd ?l0 ?cmd1 = ?M ! (fst ?cfg1_t + ?l0)"
    by (simp add: "1" nth_append length_turing_machine_sequential)
  then have 3: "relocate_cmd ?l0 ?cmd1 = ?cmd"
    using 2 by simp
  with 1 have "execute M1 cfg (Suc t) = sem ?cmd1 ?cfg1_t"
    by (simp add: exe_def)
  then have "(execute M1 cfg (Suc t)) <+=> ?l0 = (sem ?cmd1 ?cfg1_t) <+=> ?l0"
    by simp
  then have "(execute M1 cfg (Suc t)) <+=> ?l0 = (sem (relocate_cmd ?l0 ?cmd1) ?cfg1_t)"
    using sem_relocate_cmd by simp
  then have rhs: "(execute M1 cfg (Suc t)) <+=> ?l0 = sem ?cmd ?cfg1_t"
    using 3 by simp
  have "execute ?M (cfg <+=> ?l0) (Suc t) = exe ?M ?cfg_t"
    by simp
  moreover have "fst ?cfg_t < length ?M"
    using 1 2 by (simp add: length_turing_machine_sequential)
  ultimately have lhs: "execute ?M (cfg <+=> ?l0) (Suc t) = sem ?cmd ?cfg_t"
    by (simp add: exe_lt_length)
  have "sem ?cmd ?cfg_t = sem ?cmd ?cfg1_t"
    using sem_state_indep sndeq by fastforce
  with lhs rhs show ?case
    by simp
qed

lemma transits_pre_append':
  assumes "transforms M1 tps t tps'"
  shows "transits ((M0 ;; M1) @ M2) (length M0, tps) t (length M0 + length M1, tps')"
proof-
  let ?rt = "running_time M1 (0, tps)"
  let ?M = "(M0 ;; M1) @ M2"
  have "?rt \<le> t"
    using assms transforms_running_time by simp
  have "fst (execute M1 (0, tps) t) = length M1"
    using assms(1) execute_after_halting_ge halting_config_def transforms_halting_config transforms_running_time
    by (metis (no_types, opaque_lifting) fst_conv)
  then have *: "halts M1 (0, tps)"
    using halts_def by auto
  have "transits M1 (0, tps) t (length M1, tps')"
    using assms(1) transits_def by (simp add: transforms_def)
  then have "execute M1 (0, tps) ?rt = (length M1, tps')"
    using assms(1) halting_config_def transforms_halting_config by auto
  moreover have "execute ?M (length M0, tps) ?rt = (execute M1 (0, tps) ?rt) <+=> length M0"
    using execute_pre_append * by auto
  ultimately have "execute ?M (length M0, tps) ?rt = (length M1, tps') <+=> length M0"
    by simp
  then have "execute ?M (length M0, tps) ?rt = (length M0 + length M1, tps')"
    by simp
  then show ?thesis
    using \<open>?rt \<le> t\<close> transits_def by blast
qed

corollary transits_prepend:
  assumes "transforms M1 tps t tps'"
  shows "transits (M0 ;; M1) (length M0, tps) t (length M0 + length M1, tps')"
  using transits_pre_append' assms by (metis append_Nil2)

corollary transits_append:
  assumes "transforms M1 tps t tps'"
  shows "transits (M1 @ M2) (0, tps) t (length M1, tps')"
  using transits_pre_append' turing_machine_sequential_empty assms
  by (metis gen_length_def length_code list.size(3))

corollary execute_append:
  assumes "fst cfg = 0" and "halts M1 cfg" and "t \<le> running_time M1 cfg"
  shows "execute (M1 @ M2) cfg t = execute M1 cfg t"
  using assms execute_pre_append turing_machine_sequential_empty
  by (metis add.right_neutral list.size(3) prod.collapse)

lemma execute_sequential:
  assumes "execute M1 cfg1 t1 = cfg1'"
    and "fst cfg1 = 0"
    and "t1 = running_time M1 cfg1"
    and "execute M2 cfg2 t2 = cfg2'"
    and "cfg1' = cfg2 <+=> length M1"
    and "halts M1 cfg1"
  shows "execute (M1 ;; M2) cfg1 (t1 + t2) = cfg2' <+=> length M1"
proof-
  let ?M = "M1 ;; M2"
  have 1: "execute ?M cfg1 t1 = cfg1'"
    using execute_append assms turing_machine_sequential_def by simp
  then have 2: "execute ?M cfg1 (t1 + t2) = execute ?M cfg1' t2"
    using execute_additive by simp
  have "execute M2 cfg2 t2 = cfg2' \<Longrightarrow> execute ?M cfg1' t2 = cfg2' <+=> length M1" for t2
  proof (induction t2 arbitrary: cfg2')
    case 0
    then show ?case
      using 1 assms(5) by simp
  next
    case (Suc t2)
    let ?cfg = "execute M2 cfg2 t2"
    have "execute ?M cfg1' (Suc t2) = exe ?M (execute ?M cfg1' t2)"
      by simp
    then have "execute ?M cfg1' (Suc t2) = exe ?M (?cfg <+=> length M1)"
      using Suc by simp
    moreover have "execute M2 cfg2 (Suc t2) = exe M2 ?cfg"
      by simp
    ultimately show ?case
      using exe_relocate Suc.prems by metis
  qed
  then show ?thesis
    using assms(4) 2 by simp
qed

text \<open>
The semantics and running time of the @{text ";;"} operator:
\<close>

lemma transforms_turing_machine_sequential:
  assumes "transforms M1 tps1 t1 tps2" and "transforms M2 tps2 t2 tps3"
  shows "transforms (M1 ;; M2) tps1 (t1 + t2) tps3"
proof-
  let ?M = "M1 ;; M2"
  let ?cfg1 = "(0, tps1)"
  let ?cfg1' = "(length M1, tps2)"
  let ?t1 = "running_time M1 ?cfg1"
  let ?cfg2 = "(0, tps2)"
  let ?cfg2' = "(length M2, tps3)"
  let ?t2 = "running_time M2 ?cfg2"
  have "fst (execute M1 ?cfg1 ?t1) = length M1"
    using assms(1) halting_config_def transforms_halting_config by (metis fst_conv)
  then have *: "halts M1 ?cfg1"
    using halts_def by auto
  have "execute M1 ?cfg1 ?t1 = ?cfg1'"
    using assms(1) halting_config_def transforms_halting_config by auto
  moreover have "fst ?cfg1 = 0"
    by simp
  moreover have "execute M2 ?cfg2 ?t2 = ?cfg2'"
    using assms(2) halting_config_def transforms_halting_config by auto
  moreover have "?cfg1' = ?cfg2 <+=> length M1"
    by simp
  ultimately have "execute ?M ?cfg1 (?t1 + ?t2) = ?cfg2' <+=> length M1"
    using execute_sequential * by blast
  then have "execute ?M ?cfg1 (?t1 + ?t2) = (length ?M, tps3)"
    by (simp add: length_turing_machine_sequential)
  then have "transits ?M ?cfg1 (?t1 + ?t2) (length ?M, tps3)"
    using transits_def by blast
  moreover have "?t1 + ?t2 \<le> t1 + t2"
    using add_le_mono assms(1,2) transforms_running_time by blast
  ultimately have "transits ?M ?cfg1 (t1 + t2) (length ?M, tps3)"
    using transits_monotone by simp
  then show ?thesis
    using transforms_def by simp
qed

corollary transforms_tm_sequentialI:
  assumes "transforms M1 tps1 t1 tps2" and "transforms M2 tps2 t2 tps3" and "t12 = t1 + t2"
  shows "transforms (M1 ;; M2) tps1 t12 tps3"
  using assms transforms_turing_machine_sequential by simp


subsection \<open>Branches\<close>

text \<open>
A branching Turing machine consists of a condition and two Turing machines, one
for each of the branches. The condition can be any predicate over the list of
symbols read from the tapes. The branching TM thus needs to perform conditional
jumps, for which we will have the following command:
\<close>

definition cmd_jump :: "(symbol list \<Rightarrow> bool) \<Rightarrow> state \<Rightarrow> state \<Rightarrow> command" where
  "cmd_jump cond q1 q2 rs \<equiv> (if cond rs then q1 else q2, map (\<lambda>r. (r, Stay)) rs)"

lemma turing_command_jump_1:
  assumes "q1 \<le> q2" and "k > 0"
  shows "turing_command k q2 G (cmd_jump cond q1 q2)"
  using assms cmd_jump_def turing_commandI by simp

lemma turing_command_jump_2:
  assumes "q2 \<le> q1" and "k > 0"
  shows "turing_command k q1 G (cmd_jump cond q1 q2)"
  using assms cmd_jump_def turing_commandI by simp

lemma sem_jump_snd: "snd (sem (cmd_jump cond q1 q2) cfg) = snd cfg"
proof-
  let ?k = "||cfg||"
  let ?cmd = "cmd_jump cond q1 q2"
  let ?cfg' = "sem ?cmd cfg"
  let ?rs = "read (snd cfg)"
  have 1: "proper_command ?k ?cmd"
    using cmd_jump_def by simp
  then have len: "||?cfg'|| = ||cfg||"
    using sem_num_tapes_raw by simp
  have "snd ?cfg' ! i = act (snd (?cmd ?rs) ! i) (snd cfg ! i)" if "i < ||cfg||" for i
    using sem_snd 1 that by simp
  moreover have "snd (?cmd ?rs) ! i = (?rs!i, Stay)" if "i < ||cfg||" for i
    using cmd_jump_def by (simp add: read_length that)
  ultimately have "snd ?cfg' ! i = act (?rs ! i, Stay) (snd cfg ! i)" if "i < ||cfg||" for i
    using that by simp
  then have "snd ?cfg' ! i = snd cfg ! i" if "i < ||cfg||" for i
    using that act_Stay by simp
  then show "snd ?cfg' = snd cfg"
    using len nth_equalityI by force
qed

lemma sem_jump_fst1:
  assumes "cond (read (snd cfg))"
  shows "fst (sem (cmd_jump cond q1 q2) cfg) = q1"
  using cmd_jump_def sem assms by simp

lemma sem_jump_fst2:
  assumes "\<not> cond (read (snd cfg))"
  shows "fst (sem (cmd_jump cond q1 q2) cfg) = q2"
  using cmd_jump_def sem assms by simp

lemma sem_jump:
  "sem (cmd_jump cond q1 q2) cfg = (if cond (config_read cfg) then q1 else q2, snd cfg)"
  using sem_def sem_jump_snd cmd_jump_def by simp

lemma transits_jump:
  "transits [cmd_jump cond q1 q2] (0, tps) 1 (if cond (read tps) then q1 else q2, tps)"
  using transits_def sem_jump exe_def by auto

definition turing_machine_branch :: "(symbol list \<Rightarrow> bool) \<Rightarrow> machine \<Rightarrow> machine \<Rightarrow> machine"
  ("IF _ THEN _ ELSE _ ENDIF" 60)
where
  "IF cond THEN M1 ELSE M2 ENDIF \<equiv>
    [cmd_jump cond 1 (length M1 + 2)] @
    (relocate 1 M1) @
    [cmd_jump (\<lambda>_. True) (length M1 + length M2 + 2) 0] @
    (relocate (length M1 + 2) M2)"

lemma turing_machine_branch_len:
  "length (IF cond THEN M1 ELSE M2 ENDIF) = length M1 + length M2 + 2"
  unfolding turing_machine_branch_def by (simp add: relocate_def)

text \<open>
If the Turing machines for both branches have the same number of tapes and
the same alphabet size, the branching machine is a Turing machine, too.
\<close>

lemma turing_machine_branch_turing_machine:
  assumes "turing_machine k G M1" and "turing_machine k G M2"
  shows "turing_machine k G (IF cond THEN M1 ELSE M2 ENDIF)"
    (is "turing_machine _ _ ?M")
proof
  show "k \<ge> 2"
    using assms(2) turing_machine_def by simp
  show "G \<ge> 4"
    using assms(2) turing_machine_def by simp
  let ?C1 = "[cmd_jump cond 1 (length M1 + 2)]"
  let ?C2 = "relocate 1 M1"
  let ?C3 = "[cmd_jump (\<lambda>_. True) (length M1 + length M2 + 2) 0]"
  let ?C4 = "relocate (length M1 + 2) M2"
  have parts: "?M = ?C1 @ ?C2 @ ?C3 @ ?C4"
    using turing_machine_branch_def by simp
  have len: "length ?M = length M1 + length M2 + 2"
    using turing_machine_branch_len by simp
  have "k > 0"
    using `k \<ge> 2` by simp
  show "turing_command k (length ?M) G (?M ! i)" if "i < length ?M" for i
  proof -
    consider
        "i < length ?C1"
      | "length ?C1 \<le> i \<and> i < length (?C1 @ ?C2)"
      | "length (?C1 @ ?C2) \<le> i \<and> i < length (?C1 @ ?C2 @ ?C3)"
      | "length (?C1 @ ?C2 @ ?C3) \<le> i \<and> i < length ?M"
      using `i < length ?M` by linarith
    then show ?thesis
    proof (cases)
      case 1
      then have "turing_command k (length M1 + 2) G (?C1 ! i)"
        using turing_command_jump_1 `k > 0` by simp
      then have "turing_command k (length ?M) G (?C1 ! i)"
        using turing_command_mono len by simp
      then show ?thesis
        using parts 1 by simp
    next
      case 2
      then have "i - length ?C1 < length ?C2"
        by auto
      then have "turing_command k (length M1 + 1) G (?C2 ! (i - length ?C1))"
        using turing_command_relocate assms length_relocate by metis
      then have "turing_command k (length ?M) G (?C2 ! (i - length ?C1))"
        using turing_command_mono len by simp
      then have "turing_command k (length ?M) G ((?C1 @ ?C2) ! i)"
        using 2 by simp
      then show ?thesis
        using parts 2 by (metis (no_types, lifting) append.assoc nth_append)
    next
      case 3
      then have "turing_command k (length ?M) G (?C3 ! (i - length (?C1 @ ?C2)))"
        using turing_command_jump_2 len `k > 0` by simp
      then have "turing_command k (length ?M) G ((?C1 @ ?C2 @ ?C3) ! i)"
        using 3 by (metis (no_types, lifting) append.assoc diff_is_0_eq' less_numeral_extra(3) nth_append zero_less_diff)
      then show ?thesis
        using parts 3 by (smt (verit, best) append.assoc nth_append)
    next
      case 4
      then have "i - length (?C1 @ ?C2 @ ?C3) < length ?C4"
        by (simp add: len less_diff_conv2 length_relocate)
      then have "turing_command k (length ?M) G (?C4 ! (i - length (?C1 @ ?C2 @ ?C3)))"
        using turing_command_relocate assms by (smt (verit, ccfv_SIG) add.assoc add.commute len length_relocate)
      then show ?thesis
        using parts 4 by (metis (no_types, lifting) append.assoc le_simps(3) not_less_eq_eq nth_append)
    qed
  qed
qed

text \<open>
If the condition is true, the branching TM executes $M_1$ and requires two extra
steps: one for evaluating the condition and one for the unconditional jump to
the halting state.
\<close>

lemma transforms_branch_true:
  assumes "transforms M1 tps t tps'" and "cond (read tps)"
  shows "transforms (IF cond THEN M1 ELSE M2 ENDIF) tps (t + 2) tps'"
    (is "transforms ?M _ _ _")
proof-
  let ?C1 = "[cmd_jump cond 1 (length M1 + 2)]"
  let ?C2 = "relocate 1 M1"
  let ?C3 = "[cmd_jump (\<lambda>_. True) (length M1 + length M2 + 2) 0]"
  let ?C4 = "relocate (length M1 + 2) M2"
  let ?C34 = "?C3 @ ?C4"
  have parts: "?M = ?C1 @ ?C2 @ ?C3 @ ?C4"
    using turing_machine_branch_def by simp
  then have "?M = ?C1 @ ?C2 @ ?C34"
    by simp
  moreover have "?C1 @ ?C2 = ?C1 ;; M1"
    using turing_machine_sequential_def by simp
  ultimately have parts2: "?M = (?C1 ;; M1) @ ?C34"
    by simp
  have "execute ?M (0, tps) 1 = exe ?M (0, tps)"
    by simp
  also have "... = sem (?M ! 0) (0, tps)"
    using exe_def by (simp add: turing_machine_branch_len)
  also have "... = sem (?C1 ! 0) (0, tps)"
    by (simp add: parts)
  also have "... = sem (cmd_jump cond 1 (length M1 + 2)) (0, tps)"
    by simp
  also have "... = (1, tps)"
    using sem_jump by (simp add: assms(2))
  finally have "execute ?M (0, tps) 1 = (1, tps)" .
  then have phase1: "transits ?M (0, tps) 1 (1, tps)"
    using transits_def by auto
  have "length ?C1 = 1"
    by simp
  moreover have "transits ((?C1 ;; M1) @ ?C34) (length ?C1, tps) t (length ?C1 + length M1, tps')"
    using transits_pre_append' assms by blast
  ultimately have "transits ?M (1, tps) t (1 + length M1, tps')"
    using parts2 by simp
  with phase1 have "transits ?M (0, tps) (t + 1) (1 + length M1, tps')"
    using transits_additive by fastforce
  then have phase2: "transits ?M (0, tps) (t + 1) (length (?C1 @ ?C2), tps')"
    by (simp add: relocate_def)
  let ?cfg = "(length (?C1 @ ?C2), tps')"
  have *: "?M ! (length (?C1 @ ?C2)) = ?C3 ! 0"
    using parts by simp
  then have "execute ?M ?cfg 1 = exe ?M ?cfg"
    by simp
  also have "... = sem (cmd_jump (\<lambda>_. True) (length M1 + length M2 + 2) 0) ?cfg"
    using exe_def relocate_def turing_machine_branch_len * by (simp add: Suc_le_lessD)
  also have "... = (length M1 + length M2 + 2, snd ?cfg)"
    using sem_jump by simp
  also have "... = (length ?M, tps')"
    by (simp add: turing_machine_branch_len)
  finally have "execute ?M ?cfg 1 = (length ?M, tps')" .
  then have "transits ?M ?cfg 1 (length ?M, tps')"
    using transits_def by auto
  with phase2 have "transits ?M (0, tps) (t + 2) (length ?M, tps')"
    using transits_additive by fastforce
  then show ?thesis
    by (simp add: transforms_def)
qed

text \<open>
If the condition is false, the branching TM executes $M_2$ and requires one
extra step to evaluate the condition.
\<close>

lemma transforms_branch_false:
  assumes "transforms M2 tps t tps'" and "\<not> cond (read tps)"
  shows "transforms (IF cond THEN M1 ELSE M2 ENDIF) tps (t + 1) tps'"
    (is "transforms ?M _ _ _")
proof-
  let ?C1 = "[cmd_jump cond 1 (length M1 + 2)]"
  let ?C2 = "relocate 1 M1"
  let ?C3 = "[cmd_jump (\<lambda>_. True) (length M1 + length M2 + 2) 0]"
  let ?C4 = "relocate (length M1 + 2) M2"
  let ?C123 = "?C1 @ ?C2 @ ?C3"
  have parts: "?M = ?C1 @ ?C2 @ ?C3 @ ?C4"
    using turing_machine_branch_def by simp
  moreover have len123: "length ?C123 = length M1 + 2"
    by (simp add: length_relocate)
  ultimately have seq: "?M = ?C123 ;; M2"
    by (simp add: turing_machine_sequential_def)
  have "execute ?M (0, tps) 1 = exe ?M (0, tps)"
    by simp
  also have "... = sem (?M ! 0) (0, tps)"
    using exe_def by (simp add: turing_machine_branch_len)
  also have "... = sem (cmd_jump cond 1 (length M1 + 2)) (0, tps)"
    by (simp add: parts)
  also have "... = (length M1 + 2, tps)"
    using assms(2) sem_jump by simp
  also have "... = (length ?C123, tps)"
    using len123 by simp
  finally have "execute ?M (0, tps) 1 = (length ?C123, tps)" .
  then have phase1: "transits ?M (0, tps) 1 (length ?C123, tps)"
    using transits_def by blast
  have "?M ! (length ?C123) = ?C4 ! 0"
    by (simp add: nth_append parts length_relocate)
  have "transits (?C123 ;; M2) (length ?C123, tps) t (length ?C123 + length M2, tps')"
    using transits_prepend assms by blast
  then have "transits ?M (length ?C123, tps) t (length ?M, tps')"
    by (simp add: seq length_turing_machine_sequential)
  with phase1 have "transits ?M (0, tps) (t + 1) (length ?M, tps')"
    using transits_additive by fastforce
  then show ?thesis
    using transforms_def by simp
qed

text \<open>
The behavior and running time of the branching Turing machine:
\<close>

lemma transforms_branch_full:
  assumes "c \<Longrightarrow> transforms M1 tps tT tpsT"
    and "\<not> c \<Longrightarrow> transforms M2 tps tF tpsF"
    and "c \<Longrightarrow> tT + 2 \<le> t"
    and "\<not> c \<Longrightarrow> tF + 1 \<le> t"
    and "c = cond (read tps)"
    and "tps' = (if c then tpsT else tpsF)"
  shows "transforms (IF cond THEN M1 ELSE M2 ENDIF) tps t tps'"
proof -
  have "transforms (IF cond THEN M1 ELSE M2 ENDIF)
      tps
      (if c then tT + 2 else tF + 1)
      (if c then tpsT else tpsF)"
    using assms(1,2,5) transforms_branch_true transforms_branch_false by simp
  moreover have "(if c then tT + 2 else tF + 1) \<le> t"
    using assms(3,4) by simp
  ultimately show ?thesis
    using transforms_monotone assms(6) by presburger
qed

corollary transforms_branchI:
  assumes "cond (read tps) \<Longrightarrow> transforms M1 tps tT tpsT"
    and "\<not> cond (read tps) \<Longrightarrow> transforms M2 tps tF tpsF"
    and "cond (read tps) \<Longrightarrow> tT + 2 \<le> t"
    and "\<not> cond (read tps) \<Longrightarrow> tF + 1 \<le> t"
    and "cond (read tps) \<Longrightarrow> tps' = tpsT"
    and "\<not> cond (read tps) \<Longrightarrow> tps' = tpsF"
  shows "transforms (IF cond THEN M1 ELSE M2 ENDIF) tps t tps'"
  using transforms_branch_full assms by (smt (z3))


subsection \<open>Loops\<close>

text \<open>
The loops are while loops consisting of a head and a body. The body is a Turing
machine that is executed in every iteration as long as the condition in the
head of the loop evaluates to true. The condition is of the same form as in
branching TMs, namely a predicate over the symbols read from the tapes.
Sometimes this is not expressive enough, and so we allow a Turing machine as
part of the loop head that is run prior to evaluating the condition. In most
cases, however, this TM is empty.
\<close>

definition turing_machine_loop :: "machine \<Rightarrow> (symbol list \<Rightarrow> bool) \<Rightarrow> machine \<Rightarrow> machine"
  ("WHILE _ ; _ DO _ DONE" 60)
where
  "WHILE M1 ; cond DO M2 DONE \<equiv>
    M1 @
    [cmd_jump cond (length M1 + 1) (length M1 + length M2 + 2)] @
    (relocate (length M1 + 1) M2) @
    [cmd_jump (\<lambda>_. True) 0 0]"

text \<open>
Intuitively the Turing machine @{term "WHILE M1 ; cond DO M2 DONE"}
first executes @{term M1} and then checks the condition @{term cond}. If it is
true, it executes @{term M2} and jumps back to the start state; otherwise it
jumps to the halting state.
\<close>

lemma turing_machine_loop_len:
  "length (WHILE M1 ; cond DO M2 DONE) = length M1 + length M2 + 2"
  unfolding turing_machine_loop_def by (simp add: relocate_def)

text \<open>
If both Turing machines have the same number of tapes and alphabet size,
then so does the looping Turing machine.
\<close>

lemma turing_machine_loop_turing_machine:
  assumes "turing_machine k G M1" and "turing_machine k G M2"
  shows "turing_machine k G (WHILE M1 ; cond DO M2 DONE)"
    (is "turing_machine _ _ ?M")
proof
  show 1: "k \<ge> 2"
    using assms(1) turing_machine_def by simp
  show 2: "G \<ge> 4"
    using assms(1) turing_machine_def by simp
  let ?C1 = "M1"
  let ?C2 = "[cmd_jump cond (length M1 + 1) (length M1 + length M2 + 2)]"
  let ?C3 = "relocate (length M1 + 1) M2"
  let ?C4 = "[cmd_jump (\<lambda>_. True) 0 0]"
  let ?C34 = "?C3 @ ?C4"
  have parts: "?M = ?C1 @ ?C2 @ ?C3 @ ?C4"
    using turing_machine_loop_def by simp
  have len: "length ?M = length M1 + length M2 + 2"
    using turing_machine_loop_len by simp
  have "k > 0"
    using `k \<ge> 2` by simp

  show "turing_command k (length ?M) G (?M ! i)" if "i < length ?M" for i
  proof -
    consider
        "i < length ?C1"
      | "length ?C1 \<le> i \<and> i < length (?C1 @ ?C2)"
      | "length (?C1 @ ?C2) \<le> i \<and> i < length (?C1 @ ?C2 @ ?C3)"
      | "length (?C1 @ ?C2 @ ?C3) \<le> i \<and> i < length ?M"
      using `i < length ?M` by linarith
    then show ?thesis
    proof (cases)
      case 1
      then have "turing_command k (length M1) G (?C1 ! i)"
        using turing_machineD(3) assms by simp
      then have "turing_command k (length ?M) G (?C1 ! i)"
        using turing_command_mono len by simp
      then show ?thesis
        using parts 1 by (simp add: nth_append)
    next
      case 2
      then have "turing_command k (length M1 + length M2 + 2) G (?C2 ! (i - length ?C1))"
        using turing_command_jump_1 `0 < k` by simp
      then have "turing_command k (length ?M) G (?C2 ! (i - length ?C1))"
        using len by simp
      then have "turing_command k (length ?M) G ((?C1 @ ?C2) ! i)"
        using "2" le_add_diff_inverse by (simp add: nth_append)
      then show ?thesis
        using 2 parts by (simp add: nth_append)
    next
      case 3
      then have "turing_command k (length M2 + (length M1 + 1)) G (?C3 ! (i - length (?C1 @ ?C2)))"
        using turing_command_relocate length_relocate assms(2)
        by (smt (verit, best) add.commute add.left_commute add_less_cancel_left le_add_diff_inverse length_append)
      then have "turing_command k (length ?M) G (?C3 ! (i - length (?C1 @ ?C2)))"
        using turing_command_mono len by simp
      then have "turing_command k (length ?M) G ((?C1 @ ?C2 @ ?C3) ! i)"
        using 3 by (simp add: nth_append)
      then show ?thesis
        using parts 3 by (smt (verit) append.assoc nth_append)
    next
      case 4
      then have "turing_command k 0 G (?C4 ! (i - length (?C1 @ ?C2 @ ?C3)))"
        using turing_command_jump_1 `0 < k` len length_relocate by simp
      then have "turing_command k (length ?M) G (?C4 ! (i - length (?C1 @ ?C2 @ ?C3)))"
        using turing_command_mono by blast
      then show ?thesis
        using parts 4 by (metis (no_types, lifting) append.assoc nth_append verit_comp_simplify1(3))
    qed
  qed
qed

lemma transits_turing_machine_loop_cond_false:
  assumes "transforms M1 tps t1 tps'" and "\<not> cond (read tps')"
  shows "transits
            (WHILE M1 ; cond DO M2 DONE)
            (0, tps)
            (t1 + 1)
            (length M1 + length M2 + 2, tps')"
    (is "transits ?M _ _ _")
proof-
  let ?C1 = "M1"
  let ?C2 = "[cmd_jump cond (length M1 + 1) (length M1 + length M2 + 2)]"
  let ?C3 = "relocate (length M1 + 1) M2"
  let ?C4 = "[cmd_jump (\<lambda>_. True) 0 0]"
  let ?C34 = "?C3 @ ?C4"
  have parts: "?M = ?C1 @ ?C2 @ ?C3 @ ?C4"
    using turing_machine_loop_def by simp
  then have "?M = ?C1 @ (?C2 @ ?C3 @ ?C4)"
    by simp
  then have "transits ?M (0, tps) t1 (length ?C1, tps')"
    using assms transits_append by simp
  moreover have "transits ?M (length M1, tps') 1 (length M1 + length M2 + 2, tps')"
  proof-
    have *: "?M ! (length ?C1) = cmd_jump cond (length M1 + 1) (length M1 + length M2 + 2)"
      using turing_machine_loop_def by simp
    have "execute ?M (length ?C1, tps') 1 = exe ?M (length ?C1, tps')"
      by simp
    also have "... = sem (?M ! (length ?C1)) (length ?C1, tps')"
      by (simp add: exe_lt_length turing_machine_loop_len)
    also have "... = sem (cmd_jump cond (length M1 + 1) (length M1 + length M2 + 2)) (length ?C1, tps')"
      using * by simp
    also have "... = (length M1 + length M2 + 2, tps')"
      using sem_jump assms(2) by simp
    finally have "execute ?M (length ?C1, tps') 1 = (length M1 + length M2 + 2, tps')" .
    then show ?thesis
      using transits_def by auto
  qed
  ultimately show "transits ?M (0, tps) (t1 + 1) (length M1 + length M2 + 2, tps')"
    using transits_additive by blast
qed

lemma transits_turing_machine_loop_cond_true:
  assumes "transforms M1 tps t1 tps'"
    and "transforms M2 tps' t2 tps''"
    and "cond (read tps')"
  shows "transits
            (WHILE M1 ; cond DO M2 DONE)
            (0, tps)
            (t1 + t2 + 2)
            (0, tps'')"
    (is "transits ?M _ _ _")
proof-
  let ?C1 = "M1"
  let ?C2 = "[cmd_jump cond (length M1 + 1) (length M1 + length M2 + 2)]"
  let ?C3 = "relocate (length M1 + 1) M2"
  let ?C4 = "[cmd_jump (\<lambda>_. True) 0 0]"
  let ?C34 = "?C3 @ ?C4"
  have parts: "?M = ?C1 @ ?C2 @ ?C3 @ ?C4"
    using turing_machine_loop_def by simp
  then have "?M = ?C1 @ (?C2 @ ?C3 @ ?C4)"
    by simp
  then have "transits ?M (0, tps) t1 (length ?C1, tps')"
    using assms(1,3) transits_append by simp
  moreover have "transits ?M (length ?C1, tps') 1 (length ?C1 + 1, tps')"
  proof-
    have *: "?M ! (length ?C1) = cmd_jump cond (length M1 + 1) (length M1 + length M2 + 2)"
      using turing_machine_loop_def by simp
    have "execute ?M (length ?C1, tps') 1 = exe ?M (length ?C1, tps')"
      by simp
    also have "... = sem (?M ! (length ?C1)) (length ?C1, tps')"
      by (simp add: exe_lt_length turing_machine_loop_len)
    also have "... = sem (cmd_jump cond (length M1 + 1) (length M1 + length M2 + 2)) (length ?C1, tps')"
      using * by simp
    also have "... = (length M1 + 1, tps')"
      using sem_jump assms(3) by simp
    finally have "execute ?M (length ?C1, tps') 1 = (length M1 + 1, tps')" .
    then show ?thesis
      using transits_def by auto
  qed
  ultimately have "transits ?M (0, tps) (t1 + 1) (length M1 + 1, tps')"
    using transits_additive by blast
  moreover have "transits ?M (length M1 + 1, tps') t2 (length M1 + length M2 + 1, tps'')"
  proof-
    have "?M = ((?C1 @ ?C2) ;; M2) @ ?C4"
      by (simp add: parts turing_machine_sequential_def)
    moreover have "length (?C1 @ ?C2) = length M1 + 1"
      by simp
    ultimately have "transits ?M (length M1 + 1, tps') t2 (length M1 + 1 + length M2, tps'')"
      using assms transits_pre_append' by metis
    then show ?thesis
      by simp
  qed
  ultimately have "transits ?M (0, tps) (t1 + t2 + 1) (length M1 + length M2 + 1, tps'')"
    using transits_additive by fastforce
  moreover have "transits ?M (length M1 + length M2 + 1, tps'') 1 (0, tps'')"
  proof-
    have *: "?M ! (length M1 + length M2 + 1) = cmd_jump (\<lambda>_. True) 0 0"
      by (simp add: nth_append parts length_relocate)
    have "execute ?M (length M1 + length M2 + 1, tps'') 1 = exe ?M (length M1 + length M2 + 1, tps'')"
      by simp
    also have "... = sem (?M ! (length M1 + length M2 + 1)) (length M1 + length M2 + 1, tps'')"
      by (simp add: exe_lt_length turing_machine_loop_len)
    also have "... = sem (cmd_jump (\<lambda>_. True) 0 0) (length M1 + length M2 + 1, tps'')"
      using * by simp
    also have "... = (0, tps'')"
      using sem_jump by simp
    finally have "execute ?M (length M1 + length M2 + 1, tps'') 1 = (0, tps'')" .
    then show ?thesis
      using transits_def by auto
  qed
  ultimately show "transits ?M (0, tps) (t1 + t2 + 2) (0, tps'')"
    using transits_additive by fastforce
qed

text \<open>
In this article we will only encounter while loops that are in fact for loops,
that is, where the number of iterations is known beforehand. Moreover, using the
same time bound for every iteration will lead to a good enough upper bound for
the entire loop.

The @{const transforms} rule for a loop with $m$ iterations where the running
time of both TMs is bounded by a constant:
\<close>

lemma transforms_loop_for:
  fixes m t1 t2 :: nat
    and M1 M2 :: machine
    and tps :: "nat \<Rightarrow> tape list"
    and tps' :: "nat \<Rightarrow> tape list"
  assumes "\<And>i. i \<le> m \<Longrightarrow> transforms M1 (tps i) t1 (tps' i)"
  assumes "\<And>i. i < m \<Longrightarrow> transforms M2 (tps' i) t2 (tps (Suc i))"
    and "\<And>i. i < m \<Longrightarrow> cond (read (tps' i))"
    and "\<not> cond (read (tps' m))"
  assumes "ttt \<ge> m * (t1 + t2 + 2) + t1 + 1"
  shows "transforms
            (WHILE M1 ; cond DO M2 DONE)
            (tps 0)
            ttt
            (tps' m)"
proof -
  define M where "M = WHILE M1 ; cond DO M2 DONE"
  define t where "t = t1 + t2 + 2"
  have "transits M (0, tps 0) (i * t) (0, tps i)" if "i \<le> m" for i
    using that
  proof (induction i)
    case 0
    then show ?case
      using transits_def by simp
  next
    case (Suc i)
    then have "i < m"
      by simp
    then have "transits M (0, tps i) t (0, tps (Suc i))"
      using M_def t_def assms transits_turing_machine_loop_cond_true by (metis le_eq_less_or_eq)
    moreover have "transits M (0, tps 0) (i * t) (0, tps i)"
      using Suc by simp
    ultimately have "transits M (0, tps 0) (i * t + t) (0, tps (Suc i))"
      using transits_additive by simp
    then show ?case
      by (metis add.commute mult_Suc)
  qed
  then have "transits M (0, tps 0) (m * t) (0, tps m)"
    by simp
  moreover have "transits M (0, tps m) (t1 + 1) (length M1 + length M2 + 2, tps' m)"
    using assms(1,4) transits_turing_machine_loop_cond_false M_def by simp
  ultimately have "transits M (0, tps 0) (m * t + t1 + 1) (length M1 + length M2 + 2, tps' m)"
    using transits_additive by fastforce
  then show ?thesis
    using transforms_def turing_machine_loop_len M_def assms(5) t_def transits_monotone
    by auto
qed

text \<open>
The rule becomes even simpler in the common case in which the Turing machine in
the loop head is empty.
\<close>

lemma transforms_loop_simple:
  fixes m t :: nat
    and M :: machine
    and tps :: "nat \<Rightarrow> tape list"
  assumes "\<And>i. i < m \<Longrightarrow> transforms M (tps i) t (tps (Suc i))"
    and "\<And>i. i < m \<Longrightarrow> cond (read (tps i))"
    and "\<not> cond (read (tps m))"
  assumes "ttt \<ge> m * (t + 2) + 1"
  shows "transforms
            (WHILE [] ; cond DO M DONE)
            (tps 0)
            ttt
            (tps m)"
  using transforms_loop_for[where ?tps'=tps and ?cond=cond and ?t1.0=0, OF _ assms(1) _ assms(3)]
    transforms_Nil assms(2,4)
  by simp


subsection \<open>A proof method\<close>

text \<open>
Statements about the behavior and running time of Turing machines, expressed via
the predicate @{const transforms}, are the most common ones we are going to
prove. The following proof method applies introduction rules for this
predicate. These rules are either the ones we proved for the control structures
(sequence, branching, loop) or the ones describing the semantics of concrete
Turing machines. The rules of the second kind are collected in the attribute
@{text transforms_intros}.

Applying such a rule usually leaves three kinds of goals: some simple ones
requiring only instantiation of schematic variables; one for the equality of two
tape lists; and one for the time bound. For the last two goals the proof method
offers parameters @{term tps} and @{term time}, respectively.

I have to admit that most of the details of the proof method were determined by
trial and error.

\null
\<close>

named_theorems transforms_intros
declare transforms_Nil [transforms_intros]

method tform uses tps time declares transforms_intros =
  (
   ((rule transforms_tm_sequentialI)+
    | rule transforms_branchI
    | rule transforms_loop_simple
    | rule transforms_loop_for
    | rule transforms_intros)
   ; (rule transforms_intros)?
   ; (simp only:; fail)?
   ; ((use tps in simp; fail) | (use time in simp; fail))?
   ; (match conclusion in "left = right" for left right :: "tape list"
        \<Rightarrow> \<open>(fastforce simp add: tps list_update_swap; fail)\<close>)?
   ; (match conclusion in "left = right" for left right :: nat
        \<Rightarrow> \<open>(use time in simp; fail)?\<close>)?
  )

text \<open>
These lemmas are sometimes helpful for proving the equality of tape lists:
\<close>

lemma list_update_swap_less: "i' < i \<Longrightarrow> ys[i := x, i' := x'] = ys[i' := x', i := x]"
  by (simp add: list_update_swap)

lemma nth_list_update_neq': "j \<noteq> i \<Longrightarrow> xs[i := x] ! j = xs ! j"
  by simp

end
