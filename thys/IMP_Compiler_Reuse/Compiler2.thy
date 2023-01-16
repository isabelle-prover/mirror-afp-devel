(*  Title:       A Reuse-Based Multi-Stage Compiler Verification for Language IMP
    Author:      Pasquale Noce
                 Senior Staff Engineer at HID Global, Italy
                 pasquale dot noce dot lavoro at gmail dot com
                 pasquale dot noce at hidglobal dot com
*)

section "Compiler verification"

theory Compiler2
  imports Compiler
begin

text \<open>
The reasoning toolbox introduced in the @{text Compiler2} theory of \<^cite>\<open>"Noce21"\<close> to cope with
the ``hard'' direction of the bisimulation proof can be outlined as follows.

First, predicate @{text execl_all} is defined to capture the notion of a \emph{complete small-step}
program execution -- an \emph{assembly} program execution in the current context --, where such an
execution is modeled as a list of program configurations. This predicate has the property that, for
any complete execution of program @{term "P @ P' @ P''"} making the program counter point to the
beginning of program @{term P'} in some step, there exists a sub-execution being also a complete
execution of @{term P'}. Under the further assumption that any complete execution of @{term P'}
fulfills a given predicate @{term Q}, this implies the existence of a sub-execution fulfilling
@{term Q} (as established by lemma @{text execl_all_sub} in \<^cite>\<open>"Noce21"\<close>).

The compilation of arithmetic/boolean expressions and commands, modeled by functions @{const acomp},
@{const bcomp}, and @{const ccomp}, produces programs matching pattern @{term "P @ P' @ P''"}, where
sub-programs @{term P}, @{term P'}, @{term P''} may either be empty or result from the compilation
of nested expressions or commands (possibly with the insertion of further instructions). Moreover,
simulation of compiled programs by source ones can be formalized as the statement that any complete
small-step execution of a compiled program meets a proper well-behavedness predicate @{text cpred}.
By proving this statement via structural induction over commands, the resulting subgoals assume its
validity for any nested command. If as many suitable well-behavedness predicates, @{text apred} and
@{text bpred}, have been proven to hold for any complete execution of a compiled arithmetic/boolean
expression, the above @{text execl_all}'s property entails that the complete execution targeted in
each subgoal is comprised of pieces satisfying @{text apred}, @{text bpred}, or @{text cpred}, which
enables to conclude that the whole execution satisfies @{text cpred}.

Can this machinery come in handy to generalize single-step assembly code simulation by machine code,
established by lemma @{thm [source] exec1_m_exec1}, to full program executions? Actually, the gap
to be filled in is showing that assembly program execution unfolds in such a way, that a machine
stack pointer starting from zero complies with @{thm [source] exec1_m_exec1}'s assumptions in each
intermediate step. The key insight, which provides the previous question with an affirmative answer,
is that this property can as well be formalized as a well-behavedness predicate @{text mpred}, so
that the pending task takes again the form of proving that such a predicate holds for any complete
small-step execution of an assembly program.

Following this insight, the present theory extends the @{text Compiler2} theory of \<^cite>\<open>"Noce21"\<close>
by reusing its reasoning toolbox to additionally prove that any such program execution is indeed
well-behaved in this respect, too.
\<close>


subsection "Preliminary definitions and lemmas"

text \<open>
To define predicate @{text mpred}, the value taken by the machine stack pointer in every program
execution step needs to be expressed as a function of just the initial configuration and the current
one, so that a quantification over each intermediate configuration can occur in the definition's
right-hand side. On the other hand, within @{thm [source] exec1_m_exec1}'s conclusion, the stack
pointer @{term sp'} resulting from single-step execution is @{term "sp + length stk' - length stk"},
where @{term stk} and @{term sp} are the assembly stack and the stack pointer prior to single-step
execution and @{term stk'} is the ensuing assembly stack. Thus, the aforesaid function must be such
that, by replacing @{term sp} with its value into the previous expression, @{term sp'}'s value is
obtained. If @{prop "sp = length stk - length stk\<^sub>0"}, where @{term stk\<^sub>0} is the initial assembly
stack, that expression gives @{prop "sp' = length stk - length stk\<^sub>0 + length stk' - length stk"},
and the right-hand side matches @{term "length stk' - length stk\<^sub>0"} by library lemma @{thm [source]
add_diff_assoc2} provided that @{prop "length stk\<^sub>0 \<le> length stk"}.

Thus, to meet @{thm [source] exec1_m_exec1}'s former assumption for an assembly program @{term P},
each intermediate configuration @{term "(pc, s, stk)"} in a list @{term cfs} must be such that (i)
@{term "length stk - length stk\<^sub>0"} is not less than the number of the operands taken by @{term P}'s
instruction at offset @{term pc}, and (ii) @{prop "length stk\<^sub>0 \<le> length stk"}. Since the subgoals
arising from structural induction will assume this to hold for pieces of a given complete execution,
it is convenient to make @{text mpred} take two offsets @{term m} and @{term n} as further inputs
besides @{term P} and @{term cfs}. This enables the quantification to only span the configurations
within @{term cfs} whose offsets are comprised in the interval @{term "{m..<n}"} (the upper bound is
excluded as intermediate configurations alone are relevant). Unlike @{text apred}, @{text bpred},
and @{text cpred}, @{text mpred} expresses a well-behavedness condition applying indiscriminately to
arithmetic/boolean expressions and commands, which is the reason why a single predicate suffices, as
long as it takes a list of assembly instructions as input instead of a specific source code token.

\null
\<close>

fun execl :: "instr list \<Rightarrow> config list \<Rightarrow> bool" (infix "\<Turnstile>" 55) where
"P \<Turnstile> cf # cf' # cfs = (P \<turnstile> cf \<rightarrow> cf' \<and> P \<Turnstile> cf' # cfs)" |
"P \<Turnstile> _ = True"

definition execl_all :: "instr list \<Rightarrow> config list \<Rightarrow> bool" ("(_/ \<Turnstile>/ _\<box>)" 55) where
"P \<Turnstile> cfs\<box> \<equiv> P \<Turnstile> cfs \<and> cfs \<noteq> [] \<and>
  fst (cfs ! 0) = 0 \<and> fst (cfs ! (length cfs - 1)) \<notin> {0..<size P}"

definition apred :: "aexp \<Rightarrow> config \<Rightarrow> config \<Rightarrow> bool" where
"apred \<equiv> \<lambda>a (pc, s, stk) (pc', s', stk').
  pc' = pc + size (acomp a) \<and> s' = s \<and> stk' = aval a s # stk"

definition bpred :: "bexp \<times> bool \<times> int \<Rightarrow> config \<Rightarrow> config \<Rightarrow> bool" where
"bpred \<equiv> \<lambda>(b, f, i) (pc, s, stk) (pc', s', stk').
  pc' = pc + size (bcomp (b, f, i)) + (if bval b s = f then i else 0) \<and>
    s' = s \<and> stk' = stk"

definition cpred :: "com \<Rightarrow> config \<Rightarrow> config \<Rightarrow> bool" where
"cpred \<equiv> \<lambda>c (pc, s, stk) (pc', s', stk').
  pc' = pc + size (ccomp c) \<and> (c, s) \<Rightarrow> s' \<and> stk' = stk"

definition mpred :: "instr list \<Rightarrow> config list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
"mpred P cfs m n \<equiv> case cfs ! 0 of (_, _, stk\<^sub>0) \<Rightarrow>
  \<forall>k \<in> {m..<n}. case cfs ! k of (pc, _, stk) \<Rightarrow>
    msp P pc \<le> length stk - length stk\<^sub>0 \<and> length stk\<^sub>0 \<le> length stk"

abbreviation off :: "instr list \<Rightarrow> config \<Rightarrow> config" where
"off P cf \<equiv> (fst cf - size P, snd cf)"

text \<open>
\null

By slightly extending their conclusions, the lemmas used to prove compiler correctness automatically
for constructors @{const N}, @{const V}, @{const Bc}, and @{const SKIP} can be reused for the new
well-behavedness proof as well. Actually, it is sufficient to additionally infer that (i) the given
complete execution consists of one or two steps and (ii) in the latter case, the initial program
counter is zero, so that the first inequality within @{const mpred}'s definition matches the trivial
one $0 \leq 0$.

\null
\<close>

lemma iexec_offset [intro]:
 "(ins, pc, s, stk) \<mapsto> (pc', s', stk') \<Longrightarrow>
    (ins, pc - i, s, stk) \<mapsto> (pc' - i, s', stk')"
by (auto simp: iexec_simp split: instr.split)

lemma execl_next:
 "\<lbrakk>P \<Turnstile> cfs; k < length cfs; k \<noteq> length cfs - 1\<rbrakk> \<Longrightarrow>
    (P !! fst (cfs ! k), cfs ! k) \<mapsto> cfs ! Suc k \<and>
      0 \<le> fst (cfs ! k) \<and> fst (cfs ! k) < size P"
by (induction cfs arbitrary: k rule: execl.induct, auto
 simp: nth_Cons exec1_def split: nat.split)

lemma execl_last:
 "\<lbrakk>P \<Turnstile> cfs; k < length cfs; fst (cfs ! k) \<notin> {0..<size P}\<rbrakk> \<Longrightarrow>
    length cfs - 1 = k"
by (induction cfs arbitrary: k rule: execl.induct, auto
 simp: nth_Cons exec1_def split: nat.split_asm)

lemma execl_take:
 "P \<Turnstile> cfs \<Longrightarrow> P \<Turnstile> take n cfs"
by (induction cfs arbitrary: n rule: execl.induct, simp_all (no_asm_simp)
 add: take_Cons split: nat.split, subst take_Suc_Cons [symmetric], fastforce)

lemma execl_drop:
 "P \<Turnstile> cfs \<Longrightarrow> P \<Turnstile> drop n cfs"
by (induction cfs arbitrary: n rule: execl.induct, simp_all
 add: drop_Cons split: nat.split)

lemma execl_all_N [simplified, dest]:
 "[LOADI i] \<Turnstile> cfs\<box> \<Longrightarrow> apred (N i) (cfs ! 0) (cfs ! (length cfs - 1)) \<and>
    length cfs = 2 \<and> fst (cfs ! 0) = 0"
by (clarsimp simp: execl_all_def apred_def, cases "cfs ! 0",
 subgoal_tac "length cfs - 1 = 1", frule_tac [!] execl_next,
 ((rule ccontr)?, fastforce, (rule execl_last)?)+)

lemma execl_all_V [simplified, dest]:
 "[LOAD x] \<Turnstile> cfs\<box> \<Longrightarrow> apred (V x) (cfs ! 0) (cfs ! (length cfs - 1)) \<and>
    length cfs = 2 \<and> fst (cfs ! 0) = 0"
by (clarsimp simp: execl_all_def apred_def, cases "cfs ! 0",
 subgoal_tac "length cfs - 1 = 1", frule_tac [!] execl_next,
 ((rule ccontr)?, fastforce, (rule execl_last)?)+)

lemma execl_all_Bc [simplified, dest]:
 "\<lbrakk>if v = f then [JMP i] else [] \<Turnstile> cfs\<box>; 0 \<le> i\<rbrakk> \<Longrightarrow>
    bpred (Bc v, f, i) (cfs ! 0) (cfs ! (length cfs - 1)) \<and>
    length cfs = (if v = f then 2 else 1) \<and> fst (cfs ! 0) = 0"
by (clarsimp simp: execl_all_def bpred_def split: if_split_asm, cases "cfs ! 0",
 subgoal_tac "length cfs - 1 = 1", frule_tac [1-2] execl_next,
 ((rule ccontr)?, force, (rule execl_last)?)+, rule execl.cases [of "([], cfs)"],
 auto simp: exec1_def)

lemma execl_all_SKIP [simplified, dest]:
 "[] \<Turnstile> cfs\<box> \<Longrightarrow> cpred SKIP (cfs ! 0) (cfs ! (length cfs - 1)) \<and> length cfs = 1"
by (rule execl.cases [of "([], cfs)"], auto simp: execl_all_def exec1_def cpred_def)

text \<open>
\null

In \<^cite>\<open>"Noce21"\<close>, part of the proof of lemma @{text execl_all_sub} is devoted to establishing the
fundamental property of predicate @{const execl_all} stated above: for any complete execution of
program @{term "P @ P' @ P''"} making the program counter point to the beginning of @{term P'} in
its @{term k}-th step, there exists a sub-execution starting from the @{term k}-th step and being a
complete execution of @{term P'}.

Here below, this property is proven as a lemma in its own respect, named @{text execl_all}, so that
besides @{text execl_all_sub}, it can be reused to prove a further lemma @{text execl_all_sub_m}.
This new lemma establishes that, if (i) @{text execl_all_sub}'s assumptions hold, (ii) any complete
execution of @{term P'} fulfills predicate @{const mpred}, and (iii) the initial assembly stack is
not longer than the one in the @{term k}-th step, then there exists a sub-execution starting from
the @{term k}-th step and fulfilling both predicates @{term Q} and @{const mpred}. Within the new
well-behavedness proof, this lemma will play the same role as @{text execl_all_sub} in the compiler
correctness proof; namely, for each structural induction subgoal, it will entail that the respective
complete execution is comprised of pieces fulfilling @{const mpred}. As with @{text execl_all_sub},
@{term Q} can be instantiated to @{const apred}, @{const bpred}, or @{const cpred}; indeed, knowing
that sub-executions satisfy these predicates in addition to @{const mpred} is necessary to show that
the whole execution satisfies @{const mpred}. For example, to draw the conclusion that the assembly
code @{term "acomp a @ [STORE x]"} for an assignment meets @{const mpred}, one needs to know that
@{term "acomp a"}'s sub-execution also meets @{const apred}, so that the assembly stack contains an
element more than the initial stack when instruction @{term "STORE x"} is executed.

\null
\<close>

lemma execl_sub_aux:
 "\<lbrakk>\<And>m n. \<forall>k \<in> {m..<n}. Q P' (((pc, s, stk) # cfs) ! k) \<Longrightarrow> P' \<Turnstile>
    map (off P) (case m of 0 \<Rightarrow> (pc, s, stk) # take n cfs | Suc m \<Rightarrow> F cfs m n);
    \<forall>k \<in> {m..<n+m+length cfs'}. Q P' ((cfs' @ (pc, s, stk) # cfs) ! (k-m))\<rbrakk> \<Longrightarrow>
  P' \<Turnstile> (pc - size P, s, stk) # map (off P) (take n cfs)"
  (is "\<lbrakk>\<And>_ _. \<forall>k \<in> _. Q P' (?F k) \<Longrightarrow> _; \<forall>k \<in> ?A. Q P' (?G k)\<rbrakk> \<Longrightarrow> _")
by (subgoal_tac "\<forall>k \<in> {0..<n}. Q P' (?F k)", fastforce, subgoal_tac
 "\<forall>k \<in> {0..<n}. k + m + length cfs' \<in> ?A \<and> ?F k = ?G (k + m + length cfs')",
 fastforce, simp add: nth_append)

lemma execl_sub:
 "\<lbrakk>P @ P' @ P'' \<Turnstile> cfs; \<forall>k \<in> {m..<n}.
     size P \<le> fst (cfs ! k) \<and> fst (cfs ! k) - size P < size P'\<rbrakk> \<Longrightarrow>
   P' \<Turnstile> map (off P) (drop m (take (Suc n) cfs))"
  (is "\<lbrakk>_; \<forall>k \<in> _. ?P P' cfs k\<rbrakk> \<Longrightarrow> P' \<Turnstile> map _ (?F cfs m (Suc n))")
proof (induction cfs arbitrary: m n rule: execl.induct [of _ P'], auto
 simp: take_Cons drop_Cons exec1_def split: nat.split, force, force, force,
 erule execl_sub_aux [where m = 0], subst append_Cons [of _ "[]"], simp,
 erule execl_sub_aux [where m = "Suc 0" and cfs' = "[]"], simp)
  fix P' pc s stk cfs m n
  let ?cf = "(pc, s, stk) :: config"
  assume "\<And>m n. \<forall>k \<in> {m..<n}. ?P P' (?cf # cfs) k \<Longrightarrow> P' \<Turnstile>
    map (off P) (case m of 0 \<Rightarrow> ?cf # take n cfs | Suc m \<Rightarrow> ?F cfs m n)"
  moreover assume "\<forall>k \<in> {Suc (Suc m)..<Suc n}. ?P P' cfs (k - Suc (Suc 0))"
  hence "\<forall>k \<in> {Suc m..<n}. ?P P' (?cf # cfs) k"
    by force
  ultimately show "P' \<Turnstile> map (off P) (?F cfs m n)"
    by fastforce
qed

lemma execl_all:
  assumes
    A: "P @ P' x @ P'' \<Turnstile> cfs\<box>" and
    B: "k < length cfs" and
    C: "fst (cfs ! k) = size P"
  shows "\<exists>k' \<in> {k..<length cfs}. P' x \<Turnstile> map (off P) (drop k (take (Suc k') cfs))\<box>"
    (is "\<exists>k' \<in> _. _ \<Turnstile> ?F k'\<box>")
proof -
  let ?P = "\<lambda>k. size P \<le> fst (cfs ! k) \<and> fst (cfs ! k) - size P < size (P' x)"
  let ?A = "{k'. k' \<in> {k..<length cfs} \<and> \<not> ?P k'}"
  have D: "Min ?A \<in> ?A"
    (is "?k' \<in> _")
    using A and B by (rule_tac Min_in, simp_all add: execl_all_def,
     rule_tac exI [of _ "length cfs - 1"], auto)
  moreover from this have "?F ?k' ! (length (?F ?k') - 1) = off P (cfs ! ?k')"
    by (auto dest!: min_absorb2 simp: less_eq_Suc_le)
  moreover have "\<not> (\<exists>k'. k' \<in> {k'. k' \<in> {k..<?k'} \<and> \<not> ?P k'})"
    by (rule notI, erule exE, frule rev_subsetD [of _ _ ?A], rule subsetI,
     insert D, simp, subgoal_tac "finite ?A", drule Min_le, force+)
  hence "P' x \<Turnstile> ?F ?k'"
    using A by (subst (asm) execl_all_def, rule_tac execl_sub, blast+)
  ultimately show ?thesis
    using C by (auto simp: execl_all_def)
qed

lemma execl_all_sub [rule_format]:
  assumes
    A: "P @ P' x @ P'' \<Turnstile> cfs\<box>" and
    B: "k < length cfs" and
    C: "fst (cfs ! k) = size P" and
    D: "\<forall>cfs. P' x \<Turnstile> cfs\<box> \<longrightarrow> Q x (cfs ! 0) (cfs ! (length cfs - 1))"
  shows "\<exists>k' < length cfs. Q x (off P (cfs ! k)) (off P (cfs ! k'))"
proof -
  have "\<exists>k' \<in> {k..<length cfs}. P' x \<Turnstile> map (off P) (drop k (take (Suc k') cfs))\<box>"
    (is "\<exists>k' \<in> _. _ \<Turnstile> ?F k'\<box>")
    using A and B and C by (rule execl_all)
  then obtain k' where "k' \<in> {k..<length cfs}" and
   "Q x (?F k' ! 0) (?F k' ! (length (?F k') - 1))"
    using D by blast
  moreover from this have "?F k' ! (length (?F k') - 1) = off P (cfs ! k')"
    by (auto dest!: min_absorb2 simp: less_eq_Suc_le)
  ultimately show ?thesis
    by auto
qed

lemma execl_all_sub2:
  assumes
    A: "P x @ P' x' @ P'' \<Turnstile> cfs\<box>"
      (is "?P \<Turnstile> _\<box>") and
    B: "\<And>cfs. P x \<Turnstile> cfs\<box> \<Longrightarrow> (\<lambda>(pc, s, stk) (pc', s', stk').
      pc' = pc + size (P x) + I s \<and> Q s s' \<and> stk' = F s stk)
        (cfs ! 0) (cfs ! (length cfs - 1))"
      (is "\<And>cfs. _ \<Longrightarrow> ?Q x (cfs ! 0) (cfs ! (length cfs - 1))") and
    C: "\<And>cfs. P' x' \<Turnstile> cfs\<box> \<Longrightarrow> (\<lambda>(pc, s, stk) (pc', s', stk').
      pc' = pc + size (P' x') + I' s \<and> Q' s s' \<and> stk' = F' s stk)
        (cfs ! 0) (cfs ! (length cfs - 1))"
      (is "\<And>cfs. _ \<Longrightarrow> ?Q' x' (cfs ! 0) (cfs ! (length cfs - 1))") and
    D: "I (fst (snd (cfs ! 0))) = 0"
  shows "\<exists>k < length cfs. \<exists>t. (\<lambda>(pc, s, stk) (pc', s', stk').
    pc = 0 \<and> pc' = size (P x) + size (P' x') + I' t \<and> Q s t \<and> Q' t s' \<and>
      stk' = F' t (F s stk)) (cfs ! 0) (cfs ! k)"
by (subgoal_tac "[] @ ?P \<Turnstile> cfs\<box>", drule execl_all_sub [where k = 0 and Q = ?Q],
 insert A B, (clarsimp simp: execl_all_def)+, insert A C D, drule execl_all_sub
 [where Q = ?Q'], simp+, clarify, rule exI, rule conjI, simp, rule exI, auto)

lemma execl_all_sub_m [rule_format]:
  assumes
    A: "P @ P' x @ P'' \<Turnstile> cfs\<box>" and
    B: "k < length cfs" and
    C: "fst (cfs ! k) = size P" and
    D: "length (snd (snd (cfs ! 0))) \<le> length (snd (snd (cfs ! k)))" and
    E: "\<forall>cfs. P' x \<Turnstile> cfs\<box> \<longrightarrow> Q x (cfs ! 0) (cfs ! (length cfs - 1))" and
    F: "\<forall>cfs. P' x \<Turnstile> cfs\<box> \<longrightarrow> mpred (P' x) cfs 0 (length cfs - 1)"
  shows "\<exists>k' < length cfs. Q x (off P (cfs ! k)) (off P (cfs ! k')) \<and>
    mpred (P @ P' x @ P'') cfs k k'"
proof -
  have "\<exists>k' \<in> {k..<length cfs}. P' x \<Turnstile> map (off P) (drop k (take (Suc k') cfs))\<box>"
    (is "\<exists>k' \<in> _. _ \<Turnstile> ?F k'\<box>")
    using A and B and C by (rule execl_all)
  then obtain k' where G: "k' \<in> {k..<length cfs}" and H: "P' x \<Turnstile> ?F k'\<box>" and
   "Q x (?F k' ! 0) (?F k' ! (length (?F k') - 1))"
    using E by blast
  moreover from this have "?F k' ! (length (?F k') - 1) = off P (cfs ! k')"
    by (auto dest!: min_absorb2 simp: less_eq_Suc_le)
  ultimately have I: "Q x (off P (cfs ! k)) (off P (cfs ! k'))"
    by auto
  have "mpred (P' x) (?F k') 0 (length (?F k') - 1)"
    using F and H by blast
  moreover have "length (?F k') - 1 = k' - k"
    using G by auto
  ultimately have "mpred (P @ P' x @ P'') cfs k k'"
  proof (auto del: conjI simp: mpred_def split: prod.split prod.split_asm)
    fix j s stk pc\<^sub>0 s\<^sub>0 stk\<^sub>0 pc' s' stk'
    assume "\<forall>j' \<in> {0..<k' - k}. \<forall>s' stk'. snd (cfs ! (k + j')) = (s', stk') \<longrightarrow>
      msp (P' x) (fst (cfs ! (k + j')) - size P) \<le> length stk' - length stk \<and>
      length stk \<le> length stk'" and
      J: "k \<le> j" and
      K: "j < k'" and
      L: "cfs ! 0 = (pc\<^sub>0, s\<^sub>0, stk\<^sub>0)" and
      M: "snd (cfs ! k) = (s, stk)" and
      N: "cfs ! j = (pc', s', stk')"
    moreover from this have "snd (cfs ! (k + (j - k))) = (s', stk')"
      by simp
    ultimately have "msp (P' x) (pc' - size P) \<le> length stk' - length stk \<and>
      length stk \<le> length stk'"
      by fastforce
    moreover have "0 \<le> pc' - size P \<and> pc' - size P < size (P' x)"
      using G and H and J and K and N by (insert execl_next
       [of "P' x" "?F k'" "j - k"], simp add: execl_all_def)
    ultimately show "msp (P @ P' x @ P'') pc' \<le> length stk' - length stk\<^sub>0 \<and>
      length stk\<^sub>0 \<le> length stk'"
      using D and L and M by (auto simp: msp_def split: instr.split)
  qed
  thus ?thesis
    using G and I by auto
qed

text \<open>
\null

The lemmas here below establish the properties of predicate @{const mpred} required for the new
well-behavedness proof. In more detail:

  \<^item> Lemma @{text mpred_merge} states that, if two consecutive sublists of a list of configurations
    are both well-behaved, then such is the merged sublist. This lemma is the means enabling to
    infer that a complete execution made of well-behaved pieces is itself well-behaved.

  \<^item> Lemma @{text mpred_drop} states that, under proper assumptions, if a sublist of a suffix of a
    list of configurations is well-behaved, then such is the matching sublist of the whole list. In
    the subgoal of the well-behavedness proof for loops where an iteration has been run, this lemma
    can be used to deduce the well-behavedness of the whole execution from that of the sub-execution
    following that iteration.

  \<^item> Lemma @{text mpred_execl_m_exec} states that, if a nonempty small-step assembly code execution
    is well-behaved, then the machine configurations corresponding to the initial and final assembly
    ones are linked by a machine code execution. Namely, this lemma proves that the well-behavedness
    property expressed by predicate @{const mpred} is sufficient to fulfill the assumptions of lemma
    @{thm [source] exec1_m_exec1} in each intermediate step. Once any complete small-step assembly
    program execution is proven to satisfy @{const mpred}, this lemma can then be used to achieve
    the final goal of establishing that source programs are simulated by machine ones.

\null
\<close>

lemma mpred_merge:
 "\<lbrakk>mpred P cfs k m; mpred P cfs m n\<rbrakk> \<Longrightarrow> mpred P cfs k n"
by (subgoal_tac "{k..<n} \<subseteq> {k..<m} \<union> {m..<n}",
 simp add: mpred_def split: prod.split_asm, rule ballI, auto)

lemma mpred_drop:
  assumes
    A: "k \<le> length cfs" and
    B: "length (snd (snd (cfs ! 0))) \<le> length (snd (snd (cfs ! k)))"
  shows "mpred P (drop k cfs) m n \<Longrightarrow> mpred P cfs (k + m) (k + n)"
proof (clarsimp simp: mpred_def)
  fix k' pc pc' pc'' s s' s'' stk stk'' and stk' :: stack
  assume "\<forall>k'' \<in> {m..<n}. case drop k cfs ! k'' of (pc'', s'', stk'') \<Rightarrow>
    msp P pc'' \<le> length stk'' - length stk' \<and> length stk' \<le> length stk''"
    (is "\<forall>k'' \<in> _. ?Q k''")
  hence "k' - k \<in> {m..<n} \<longrightarrow> ?Q (k' - k)"
    by simp
  moreover assume "k + m \<le> k'" and "k' < k + n" and "cfs ! 0 = (pc, s, stk)" and
   "drop k cfs ! 0 = (pc', s', stk')" and "cfs ! k' = (pc'', s'', stk'')"
  ultimately show
   "msp P pc'' \<le> length stk'' - length stk \<and> length stk \<le> length stk''"
    using A and B by auto
qed

lemma mpred_execl_m_exec [simplified Let_def]:
 "\<lbrakk>cfs \<noteq> []; P \<Turnstile> cfs; mpred P cfs 0 (length cfs - 1)\<rbrakk> \<Longrightarrow>
    case (cfs ! 0, cfs ! (length cfs - 1)) of ((pc, s, stk), (pc', s', stk')) \<Rightarrow>
      let sp' = length stk' - length stk in to_m_prog P \<^bold>\<turnstile>
        (pc, to_m_state (vars P) s, 0) \<^bold>\<rightarrow>\<^bold>*
        (pc', add_m_stack sp' stk' (to_m_state (vars P) s'), sp')"
proof (induction cfs rule: rev_nonempty_induct, force, rule rev_cases, erule notE,
 simp_all only: nth_append, auto simp: Let_def simp del: to_m_prog.simps)
  fix cfs pc pc' pc'' s s' s'' stk'' and stk :: stack and stk' :: stack
  let ?sp = "length stk' - length stk"
  assume "P \<Turnstile> cfs @ [(pc', s', stk')] \<Longrightarrow>
    mpred P (cfs @ [(pc', s', stk')]) 0 (length cfs) \<Longrightarrow>
      to_m_prog P \<^bold>\<turnstile>
        (pc, to_m_state (vars P) s, 0) \<^bold>\<rightarrow>\<^bold>*
        (pc', add_m_stack ?sp stk' (to_m_state (vars P) s'), ?sp)"
    (is "?P \<Longrightarrow> ?Q \<Longrightarrow> ?R")
  moreover assume A: "P \<Turnstile> cfs @ [(pc', s', stk'), (pc'', s'', stk'')]"
    (is "_ \<Turnstile> ?cfs")
  hence ?P
    by (drule_tac execl_take [where n = "Suc (length cfs)"], simp)
  moreover assume B: "mpred P ?cfs 0 (Suc (length cfs))"
  hence ?Q
    by (auto simp: mpred_def nth_append split: if_split_asm)
  ultimately have ?R
    by simp
  let ?sp' = "?sp + length stk'' - length stk'"
  let ?sp'' = "length stk'' - length stk"
  have "P \<turnstile> (pc', s', stk') \<rightarrow> (pc'', s'', stk'')"
    by (insert execl_drop [OF A, of "length cfs"], simp)
  moreover assume "(cfs @ [(pc', s', stk')]) ! 0 = (pc, s, stk)"
  hence C: "msp P pc' \<le> ?sp \<and> length stk \<le> length stk'"
    using B by (auto simp: mpred_def nth_append split: if_split_asm)
  ultimately have "to_m_prog P \<^bold>\<turnstile>
    (pc', add_m_stack ?sp stk' (to_m_state (vars P) s'), ?sp) \<^bold>\<rightarrow>
    (pc'', add_m_stack ?sp' stk'' (to_m_state (vars P) s''), ?sp')"
    by (rule_tac exec1_m_exec1, simp_all)
  thus "to_m_prog P \<^bold>\<turnstile>
    (pc, to_m_state (vars P) s, 0) \<^bold>\<rightarrow>\<^bold>*
    (pc'', add_m_stack ?sp'' stk'' (to_m_state (vars P) s''), ?sp'')"
    using `?R` and C by (auto intro: star_trans)
qed


subsection "Main theorems"

text \<open>
Here below is the proof that every complete small-step execution of an assembly program fulfills
predicate @{const cpred} (lemma @{text ccomp_correct}), which is reused as is from \<^cite>\<open>"Noce21"\<close>,
followed by the proof that every such execution satisfies predicate @{const mpred} as well (lemma
@{text ccomp_correct_m}), which closely resembles the former one.

\null
\<close>

lemma acomp_acomp:
 "\<lbrakk>acomp a\<^sub>1 @ acomp a\<^sub>2 @ P \<Turnstile> cfs\<box>;
    \<And>cfs. acomp a\<^sub>1 \<Turnstile> cfs\<box> \<Longrightarrow> apred a\<^sub>1 (cfs ! 0) (cfs ! (length cfs - 1));
    \<And>cfs. acomp a\<^sub>2 \<Turnstile> cfs\<box> \<Longrightarrow> apred a\<^sub>2 (cfs ! 0) (cfs ! (length cfs - 1))\<rbrakk> \<Longrightarrow>
  case cfs ! 0 of (pc, s, stk) \<Rightarrow> pc = 0 \<and> (\<exists>k < length cfs. cfs ! k =
    (size (acomp a\<^sub>1 @ acomp a\<^sub>2), s, aval a\<^sub>2 s # aval a\<^sub>1 s # stk))"
by (drule execl_all_sub2 [where I = "\<lambda>s. 0" and I' = "\<lambda>s. 0" and Q = "\<lambda>s s'. s' = s"
 and Q' = "\<lambda>s s'. s' = s" and F = "\<lambda>s stk. aval a\<^sub>1 s # stk"
 and F' = "\<lambda>s stk. aval a\<^sub>2 s # stk"], auto simp: apred_def)

lemma bcomp_bcomp:
 "\<lbrakk>bcomp (b\<^sub>1, f\<^sub>1, i\<^sub>1) @ bcomp (b\<^sub>2, f\<^sub>2, i\<^sub>2) \<Turnstile> cfs\<box>;
    \<And>cfs. bcomp (b\<^sub>1, f\<^sub>1, i\<^sub>1) \<Turnstile> cfs\<box> \<Longrightarrow>
      bpred (b\<^sub>1, f\<^sub>1, i\<^sub>1) (cfs ! 0) (cfs ! (length cfs - 1));
    \<And>cfs. bcomp (b\<^sub>2, f\<^sub>2, i\<^sub>2) \<Turnstile> cfs\<box> \<Longrightarrow>
      bpred (b\<^sub>2, f\<^sub>2, i\<^sub>2) (cfs ! 0) (cfs ! (length cfs - 1))\<rbrakk> \<Longrightarrow>
  case cfs ! 0 of (pc, s, stk) \<Rightarrow> pc = 0 \<and> (bval b\<^sub>1 s \<noteq> f\<^sub>1 \<longrightarrow>
    (\<exists>k < length cfs. cfs ! k = (size (bcomp (b\<^sub>1, f\<^sub>1, i\<^sub>1) @ bcomp (b\<^sub>2, f\<^sub>2, i\<^sub>2)) +
      (if bval b\<^sub>2 s = f\<^sub>2 then i\<^sub>2 else 0), s, stk)))"
by (clarify, rule conjI, simp add: execl_all_def, rule impI, subst (asm) append_Nil2
 [symmetric], drule execl_all_sub2 [where I = "\<lambda>s. if bval b\<^sub>1 s = f\<^sub>1 then i\<^sub>1 else 0"
 and I' = "\<lambda>s. if bval b\<^sub>2 s = f\<^sub>2 then i\<^sub>2 else 0" and Q = "\<lambda>s s'. s' = s"
 and Q' = "\<lambda>s s'. s' = s" and F = "\<lambda>s stk. stk" and F' = "\<lambda>s stk. stk"],
 auto simp: bpred_def)

lemma acomp_correct [simplified, intro]:
 "acomp a \<Turnstile> cfs\<box> \<Longrightarrow> apred a (cfs ! 0) (cfs ! (length cfs - 1))"
proof (induction a arbitrary: cfs, simp_all, frule_tac [3] acomp_acomp, auto)
  fix a\<^sub>1 a\<^sub>2 cfs s stk k
  assume A: "acomp a\<^sub>1 @ acomp a\<^sub>2 @ [ADD] \<Turnstile> cfs\<box>"
    (is "?ca\<^sub>1 @ ?ca\<^sub>2 @ ?i \<Turnstile> _\<box>")
  assume B: "k < length cfs" and
    C: "cfs ! k = (size ?ca\<^sub>1 + size ?ca\<^sub>2, s, aval a\<^sub>2 s # aval a\<^sub>1 s # stk)"
  hence "cfs ! Suc k = (size (?ca\<^sub>1 @ ?ca\<^sub>2 @ ?i), s, aval (Plus a\<^sub>1 a\<^sub>2) s # stk)"
    using A by (insert execl_next [of "?ca\<^sub>1 @ ?ca\<^sub>2 @ ?i" cfs k],
     simp add: execl_all_def, drule_tac impI, auto)
  thus "apred (Plus a\<^sub>1 a\<^sub>2) (0, s, stk) (cfs ! (length cfs - Suc 0))"
    using A and B and C by (insert execl_last [of "?ca\<^sub>1 @ ?ca\<^sub>2 @ ?i" cfs "Suc k"],
     simp add: execl_all_def apred_def, drule_tac impI, auto)
qed

lemma bcomp_correct [simplified, intro]:
 "\<lbrakk>bcomp x \<Turnstile> cfs\<box>; 0 \<le> snd (snd x)\<rbrakk> \<Longrightarrow> bpred x (cfs ! 0) (cfs ! (length cfs - 1))"
proof (induction x arbitrary: cfs rule: bcomp.induct, simp_all add: Let_def,
 frule_tac [4] acomp_acomp, frule_tac [3] bcomp_bcomp, auto, force simp: bpred_def)
  fix b\<^sub>1 b\<^sub>2 f i cfs s stk
  assume A: "bcomp (b\<^sub>1, False, size (bcomp (b\<^sub>2, f, i)) + (if f then 0 else i)) @
    bcomp (b\<^sub>2, f, i) \<Turnstile> cfs\<box>"
    (is "bcomp (_, _, ?n + ?i) @ ?cb \<Turnstile> _\<box>")
  moreover assume B: "cfs ! 0 = (0, s, stk)" and
   "\<And>cb cfs. \<lbrakk>cb = ?cb; bcomp (b\<^sub>1, False, ?n + ?i) \<Turnstile> cfs\<box>\<rbrakk> \<Longrightarrow>
      bpred (b\<^sub>1, False, ?n + ?i) (cfs ! 0) (cfs ! (length cfs - Suc 0))"
  ultimately have "\<exists>k < length cfs. bpred (b\<^sub>1, False, ?n + ?i)
    (off [] (cfs ! 0)) (off [] (cfs ! k))"
    by (rule_tac execl_all_sub, auto simp: execl_all_def)
  moreover assume C: "\<not> bval b\<^sub>1 s"
  ultimately obtain k where D: "k < length cfs" and
    E: "cfs ! k = (size (bcomp (b\<^sub>1, False, ?n + ?i)) + ?n + ?i, s, stk)"
    using B by (auto simp: bpred_def)
  assume "0 \<le> i"
  thus "bpred (And b\<^sub>1 b\<^sub>2, f, i) (0, s, stk) (cfs ! (length cfs - Suc 0))"
    using A and C and D and E by (insert execl_last, auto simp:
     execl_all_def bpred_def Let_def)
next
  fix b\<^sub>1 b\<^sub>2 f i cfs s stk k
  assume A: "bcomp (b\<^sub>1, False, size (bcomp (b\<^sub>2, f, i)) + (if f then 0 else i)) @
    bcomp (b\<^sub>2, f, i) \<Turnstile> cfs\<box>"
    (is "?cb\<^sub>1 @ ?cb\<^sub>2 \<Turnstile> _\<box>")
  assume "k < length cfs" and "0 \<le> i" and "bval b\<^sub>1 s" and
   "cfs ! k = (size ?cb\<^sub>1 + size ?cb\<^sub>2 + (if bval b\<^sub>2 s = f then i else 0), s, stk)"
  thus "bpred (And b\<^sub>1 b\<^sub>2, f, i) (0, s, stk) (cfs ! (length cfs - Suc 0))"
    using A by (insert execl_last, auto simp: execl_all_def bpred_def Let_def)
next
  fix a\<^sub>1 a\<^sub>2 f i cfs s stk k
  assume A: "acomp a\<^sub>1 @ acomp a\<^sub>2 @
    (if f then [JMPLESS i] else [JMPGE i]) \<Turnstile> cfs\<box>"
    (is "?ca\<^sub>1 @ ?ca\<^sub>2 @ ?i \<Turnstile> _\<box>")
  assume B: "k < length cfs" and
    C: "cfs ! k = (size ?ca\<^sub>1 + size ?ca\<^sub>2, s, aval a\<^sub>2 s # aval a\<^sub>1 s # stk)"
  hence D: "cfs ! Suc k =
    (size (?ca\<^sub>1 @ ?ca\<^sub>2 @ ?i) + (if bval (Less a\<^sub>1 a\<^sub>2) s = f then i else 0), s, stk)"
    using A by (insert execl_next [of "?ca\<^sub>1 @ ?ca\<^sub>2 @ ?i" cfs k],
     simp add: execl_all_def, drule_tac impI, auto split: if_split_asm)
  assume "0 \<le> i"
  with A and B and C and D have "length cfs - 1 = Suc k"
    by (rule_tac execl_last, auto simp: execl_all_def, simp split: if_split_asm)
  thus "bpred (Less a\<^sub>1 a\<^sub>2, f, i) (0, s, stk) (cfs ! (length cfs - Suc 0))"
    using D by (simp add: bpred_def)
qed


lemma bcomp_ccomp:
 "\<lbrakk>bcomp (b, f, i) @ ccomp c @ P \<Turnstile> cfs\<box>; 0 \<le> i;
    \<And>cfs. ccomp c \<Turnstile> cfs\<box> \<Longrightarrow> cpred c (cfs ! 0) (cfs ! (length cfs - 1))\<rbrakk> \<Longrightarrow>
  case cfs ! 0 of (pc, s, stk) \<Rightarrow> pc = 0 \<and> (bval b s \<noteq> f \<longrightarrow>
    (\<exists>k < length cfs. case cfs ! k of (pc', s', stk') \<Rightarrow>
      pc' = size (bcomp (b, f, i) @ ccomp c) \<and> (c, s) \<Rightarrow> s' \<and> stk' = stk))"
by (clarify, rule conjI, simp add: execl_all_def, rule impI, drule execl_all_sub2
 [where I = "\<lambda>s. if bval b s = f then i else 0" and I' = "\<lambda>s. 0"
 and Q = "\<lambda>s s'. s' = s" and Q' = "\<lambda>s s'. (c, s) \<Rightarrow> s'" and F = "\<lambda>s stk. stk"
 and F' = "\<lambda>s stk. stk"], insert bcomp_correct [of "(b, f, i)"],
 auto simp: bpred_def cpred_def)

lemma ccomp_ccomp:
 "\<lbrakk>ccomp c\<^sub>1 @ ccomp c\<^sub>2 \<Turnstile> cfs\<box>;
    \<And>cfs. ccomp c\<^sub>1 \<Turnstile> cfs\<box> \<Longrightarrow> cpred c\<^sub>1 (cfs ! 0) (cfs ! (length cfs - 1));
    \<And>cfs. ccomp c\<^sub>2 \<Turnstile> cfs\<box> \<Longrightarrow> cpred c\<^sub>2 (cfs ! 0) (cfs ! (length cfs - 1))\<rbrakk> \<Longrightarrow>
  case cfs ! 0 of (pc, s, stk) \<Rightarrow> pc = 0 \<and> (\<exists>k < length cfs. \<exists>t.
    case cfs ! k of (pc', s', stk') \<Rightarrow> pc' = size (ccomp c\<^sub>1 @ ccomp c\<^sub>2) \<and>
      (c\<^sub>1, s) \<Rightarrow> t \<and> (c\<^sub>2, t) \<Rightarrow> s' \<and> stk' = stk)"
by (subst (asm) append_Nil2 [symmetric], drule execl_all_sub2 [where I = "\<lambda>s. 0"
 and I' = "\<lambda>s. 0" and Q = "\<lambda>s s'. (c\<^sub>1, s) \<Rightarrow> s'" and Q' = "\<lambda>s s'. (c\<^sub>2, s) \<Rightarrow> s'"
 and F = "\<lambda>s stk. stk" and F' = "\<lambda>s stk. stk"], auto simp: cpred_def, force)

lemma while_correct [simplified, intro]:
 "\<lbrakk>bcomp (b, False, size (ccomp c) + 1) @ ccomp c @
    [JMP (- (size (bcomp (b, False, size (ccomp c) + 1) @ ccomp c) + 1))]
      \<Turnstile> cfs\<box>;
    \<And>cfs. ccomp c \<Turnstile> cfs\<box> \<Longrightarrow> cpred c (cfs ! 0) (cfs ! (length cfs - 1))\<rbrakk> \<Longrightarrow>
  cpred (WHILE b DO c) (cfs ! 0) (cfs ! (length cfs - Suc 0))"
  (is "\<lbrakk>?cb @ ?cc @ [JMP (- ?n)] \<Turnstile> _\<box>; \<And>_. _ \<Longrightarrow> _\<rbrakk> \<Longrightarrow> ?Q cfs")
proof (induction cfs rule: length_induct, frule bcomp_ccomp, auto)
  fix cfs s stk
  assume A: "?cb @ ?cc @ [JMP (- size ?cb - size ?cc - 1)] \<Turnstile> cfs\<box>"
  hence "\<exists>k < length cfs. bpred (b, False, size (ccomp c) + 1)
    (off [] (cfs ! 0)) (off [] (cfs ! k))"
    by (rule_tac execl_all_sub, auto simp: execl_all_def)
  moreover assume B: "\<not> bval b s" and "cfs ! 0 = (0, s, stk)"
  ultimately obtain k where "k < length cfs" and "cfs ! k = (?n, s, stk)"
    by (auto simp: bpred_def)
  thus "cpred (WHILE b DO c) (0, s, stk) (cfs ! (length cfs - Suc 0))"
    using A and B by (insert execl_last, auto simp: execl_all_def cpred_def Let_def)
next
  fix cfs s s' stk k
  assume A: "?cb @ ?cc @ [JMP (- size ?cb - size ?cc - 1)] \<Turnstile> cfs\<box>"
    (is "?P \<Turnstile> _\<box>")
  assume B: "k < length cfs" and "cfs ! k = (size ?cb + size ?cc, s', stk)"
  moreover from this have C: "k \<noteq> length cfs - 1"
    using A by (rule_tac notI, simp add: execl_all_def)
  ultimately have D: "cfs ! Suc k = (0, s', stk)"
    using A by (insert execl_next [of ?P cfs k], auto simp: execl_all_def)
  moreover have E: "Suc k + (length (drop (Suc k) cfs) - 1) = length cfs - 1"
    (is "_ + (length ?cfs - _) = _")
    using B and C by simp
  ultimately have "?P \<Turnstile> ?cfs\<box>"
    using A and B and C by (auto simp: execl_all_def intro: execl_drop)
  moreover assume "\<forall>cfs'. length cfs' < length cfs \<longrightarrow> ?P \<Turnstile> cfs'\<box> \<longrightarrow> ?Q cfs'"
  hence "length ?cfs < length cfs \<longrightarrow> ?P \<Turnstile> ?cfs\<box> \<longrightarrow> ?Q ?cfs" ..
  ultimately have "cpred (WHILE b DO c) (cfs ! Suc k) (cfs ! (length cfs - 1))"
    using B and C and E by simp
  moreover assume "bval b s" and "(c, s) \<Rightarrow> s'"
  ultimately show "cpred (WHILE b DO c) (0, s, stk) (cfs ! (length cfs - Suc 0))"
    using D by (auto simp: cpred_def)
qed

lemma ccomp_correct [simplified, intro]:
 "ccomp c \<Turnstile> cfs\<box> \<Longrightarrow> cpred c (cfs ! 0) (cfs ! (length cfs - 1))"
proof (induction c arbitrary: cfs, simp_all add: Let_def, frule_tac [4] bcomp_ccomp,
 frule_tac [3] ccomp_ccomp, auto)
  fix a x cfs
  assume A: "acomp a @ [STORE x] \<Turnstile> cfs\<box>"
  hence "\<exists>k < length cfs. apred a (off [] (cfs ! 0)) (off [] (cfs ! k))"
    by (rule_tac execl_all_sub, auto simp: execl_all_def)
  moreover obtain s stk where B: "cfs ! 0 = (0, s, stk)"
    using A by (cases "cfs ! 0", simp add: execl_all_def)
  ultimately obtain k where C: "k < length cfs" and
    D: "cfs ! k = (size (acomp a), s, aval a s # stk)"
    by (auto simp: apred_def)
  hence "cfs ! Suc k = (size (acomp a) + 1, s(x := aval a s), stk)"
    using A by (insert execl_next [of "acomp a @ [STORE x]" cfs k],
     simp add: execl_all_def, drule_tac impI, auto)
  thus "cpred (x ::= a) (cfs ! 0) (cfs ! (length cfs - Suc 0))"
    using A and B and C and D by (insert execl_last [of "acomp a @ [STORE x]"
     cfs "Suc k"], simp add: execl_all_def cpred_def, drule_tac impI, auto)
next
  fix c\<^sub>1 c\<^sub>2 cfs s s' t stk k
  assume "ccomp c\<^sub>1 @ ccomp c\<^sub>2 \<Turnstile> cfs\<box>" and "k < length cfs" and
   "cfs ! k = (size (ccomp c\<^sub>1) + size (ccomp c\<^sub>2), s', stk)"
  moreover assume "(c\<^sub>1, s) \<Rightarrow> t" and "(c\<^sub>2, t) \<Rightarrow> s'"
  ultimately show "cpred (c\<^sub>1;; c\<^sub>2) (0, s, stk) (cfs ! (length cfs - Suc 0))"
    by (insert execl_last, auto simp: execl_all_def cpred_def)
next
  fix b c\<^sub>1 c\<^sub>2 cfs s stk
  assume A: "bcomp (b, False, size (ccomp c\<^sub>1) + 1) @ ccomp c\<^sub>1 @
    JMP (size (ccomp c\<^sub>2)) # ccomp c\<^sub>2 \<Turnstile> cfs\<box>"
    (is "bcomp ?x @ ?cc\<^sub>1 @ _ # ?cc\<^sub>2 \<Turnstile> _\<box>")
  let ?P = "bcomp ?x @ ?cc\<^sub>1 @ [JMP (size ?cc\<^sub>2)]"
  have "\<exists>k < length cfs. bpred ?x (off [] (cfs ! 0)) (off [] (cfs ! k))"
    using A by (rule_tac execl_all_sub, auto simp: execl_all_def)
  moreover assume B: "\<not> bval b s" and "cfs ! 0 = (0, s, stk)"
  ultimately obtain k where C: "k < length cfs" and D: "cfs ! k = (size ?P, s, stk)"
    by (force simp: bpred_def)
  assume "\<And>cfs. ?cc\<^sub>2 \<Turnstile> cfs\<box> \<Longrightarrow> cpred c\<^sub>2 (cfs ! 0) (cfs ! (length cfs - Suc 0))"
  hence "\<exists>k' < length cfs. cpred c\<^sub>2 (off ?P (cfs ! k)) (off ?P (cfs ! k'))"
    using A and C and D by (rule_tac execl_all_sub [where P'' = "[]"], auto)
  then obtain k' where "k' < length cfs" and "case cfs ! k' of (pc', s', stk') \<Rightarrow>
    pc' = size (?P @ ?cc\<^sub>2) \<and> (c\<^sub>2, s) \<Rightarrow> s' \<and> stk' = stk"
    using D by (fastforce simp: cpred_def)
  thus "cpred (IF b THEN c\<^sub>1 ELSE c\<^sub>2) (0, s, stk) (cfs ! (length cfs - Suc 0))"
    using A and B by (insert execl_last, auto simp: execl_all_def cpred_def Let_def)
next
  fix b c\<^sub>1 c\<^sub>2 cfs s s' stk k
  assume A: "bcomp (b, False, size (ccomp c\<^sub>1) + 1) @ ccomp c\<^sub>1 @
    JMP (size (ccomp c\<^sub>2)) # ccomp c\<^sub>2 \<Turnstile> cfs\<box>"
    (is "?cb @ ?cc\<^sub>1 @ ?i # ?cc\<^sub>2 \<Turnstile> _\<box>")
  assume B: "k < length cfs" and C: "cfs ! k = (size ?cb + size ?cc\<^sub>1, s', stk)"
  hence D: "cfs ! Suc k = (size (?cb @ ?cc\<^sub>1 @ ?i # ?cc\<^sub>2), s', stk)"
    (is "_ = (size ?P, _, _)")
    using A by (insert execl_next [of ?P cfs k], simp add: execl_all_def,
     drule_tac impI, auto)
  assume "bval b s" and "(c\<^sub>1, s) \<Rightarrow> s'"
  thus "cpred (IF b THEN c\<^sub>1 ELSE c\<^sub>2) (0, s, stk) (cfs ! (length cfs - Suc 0))"
    using A and B and C and D by (insert execl_last [of ?P cfs "Suc k"],
     simp add: execl_all_def cpred_def Let_def, drule_tac impI, auto)
qed


lemma acomp_acomp_m:
  assumes
    A: "acomp a\<^sub>1 @ acomp a\<^sub>2 @ P \<Turnstile> cfs\<box>"
      (is "?P \<Turnstile> _\<box>") and
    B: "\<And>cfs. acomp a\<^sub>1 \<Turnstile> cfs\<box> \<Longrightarrow> mpred (acomp a\<^sub>1) cfs 0 (length cfs - 1)" and
    C: "\<And>cfs. acomp a\<^sub>2 \<Turnstile> cfs\<box> \<Longrightarrow> mpred (acomp a\<^sub>2) cfs 0 (length cfs - 1)"
  shows "case cfs ! 0 of (pc, s, stk) \<Rightarrow> \<exists>k < length cfs.
    cfs ! k = (size (acomp a\<^sub>1 @ acomp a\<^sub>2), s, aval a\<^sub>2 s # aval a\<^sub>1 s # stk) \<and>
    mpred ?P cfs 0 k"
proof -
  have "\<exists>k < length cfs. apred a\<^sub>1 (off [] (cfs ! 0)) (off [] (cfs ! k)) \<and>
    mpred ([] @ ?P) cfs 0 k"
    using A and B by (rule_tac execl_all_sub_m, insert execl_all_def, auto)
  then obtain k s stk where
   "cfs ! 0 = (0, s, stk) \<and> mpred ?P cfs 0 k \<and> k < length cfs" and
    D: "cfs ! k = (size (acomp a\<^sub>1), s, aval a\<^sub>1 s # stk)"
    using A by (auto simp: apred_def execl_all_def)
  moreover from this have "\<exists>k' < length cfs. apred a\<^sub>2 (off (acomp a\<^sub>1) (cfs ! k))
    (off (acomp a\<^sub>1) (cfs ! k')) \<and> mpred ?P cfs k k'"
    using A and C by (rule_tac execl_all_sub_m, insert execl_all_def, auto)
  then obtain k' where "k' < length cfs \<and> mpred ?P cfs k k' \<and>
    cfs ! k' = (size (acomp a\<^sub>1 @ acomp a\<^sub>2), s, aval a\<^sub>2 s # aval a\<^sub>1 s # stk)"
    using D by (fastforce simp: apred_def prod_eq_iff)
  ultimately show ?thesis
    by (auto intro: mpred_merge)
qed

lemma bcomp_bcomp_m [simplified, intro]:
  assumes A: "bcomp (b\<^sub>1, f\<^sub>1, i\<^sub>1) @ bcomp (b\<^sub>2, f\<^sub>2, i\<^sub>2) \<Turnstile> cfs\<box>"
    (is "bcomp ?x\<^sub>1 @ bcomp ?x\<^sub>2 \<Turnstile> _\<box>")
  assumes
    B: "\<And>cfs. bcomp ?x\<^sub>1 \<Turnstile> cfs\<box> \<Longrightarrow> mpred (bcomp ?x\<^sub>1) cfs 0 (length cfs - 1)" and
    C: "\<And>cfs. bcomp ?x\<^sub>2 \<Turnstile> cfs\<box> \<Longrightarrow> mpred (bcomp ?x\<^sub>2) cfs 0 (length cfs - 1)" and
    D: "size (bcomp ?x\<^sub>2) \<le> i\<^sub>1" and
    E: "0 \<le> i\<^sub>2"
  shows "mpred (bcomp ?x\<^sub>1 @ bcomp ?x\<^sub>2) cfs 0 (length cfs - 1)"
    (is "mpred ?P _ _ _")
proof -
  have "\<exists>k < length cfs. bpred ?x\<^sub>1 (off [] (cfs ! 0)) (off [] (cfs ! k)) \<and>
    mpred ([] @ ?P) cfs 0 k"
    using A and B and D by (rule_tac execl_all_sub_m, insert execl_all_def, auto)
  then obtain k s stk where
   "cfs ! 0 = (0, s, stk) \<and> mpred ?P cfs 0 k \<and> k < length cfs" and
    F: "cfs ! k = (size (bcomp ?x\<^sub>1) + (if bval b\<^sub>1 s = f\<^sub>1 then i\<^sub>1 else 0), s, stk)"
    using A by (auto simp: bpred_def execl_all_def)
  moreover from this have "bval b\<^sub>1 s \<noteq> f\<^sub>1 \<Longrightarrow> \<exists>k' < length cfs.
    bpred ?x\<^sub>2 (off (bcomp ?x\<^sub>1) (cfs ! k)) (off (bcomp ?x\<^sub>1) (cfs ! k')) \<and>
    mpred (bcomp ?x\<^sub>1 @ bcomp ?x\<^sub>2 @ []) cfs k k'"
    using A and C and E by (rule_tac execl_all_sub_m, insert execl_all_def, auto)
  then obtain k' where "bval b\<^sub>1 s \<noteq> f\<^sub>1 \<Longrightarrow> k' < length cfs \<and> mpred ?P cfs k k' \<and>
    fst (cfs ! k') = size ?P + (if bval b\<^sub>2 s = f\<^sub>2 then i\<^sub>2 else 0)"
    using F by (fastforce simp: bpred_def)
  ultimately have "\<exists>k < length cfs. fst (cfs ! k) = (if bval b\<^sub>1 s = f\<^sub>1 then
    size (bcomp ?x\<^sub>1) + i\<^sub>1 else size ?P + (if bval b\<^sub>2 s = f\<^sub>2 then i\<^sub>2 else 0)) \<and>
    mpred ?P cfs 0 k"
    (is "\<exists>k < _. ?Q k")
    by (fastforce intro: mpred_merge)
  then obtain k'' where "k'' < length cfs \<and> ?Q k''" ..
  with A and D and E show ?thesis
    by (insert execl_last [of ?P cfs k''], simp add: execl_all_def)
qed

lemma acomp_correct_m [simplified, intro]:
 "acomp a \<Turnstile> cfs\<box> \<Longrightarrow> mpred (acomp a) cfs 0 (length cfs - 1)"
proof (induction a arbitrary: cfs, (fastforce simp: mpred_def msp_def)+, simp,
 frule acomp_acomp_m, auto)
  fix a\<^sub>1 a\<^sub>2 cfs pc s stk k
  assume A: "acomp a\<^sub>1 @ acomp a\<^sub>2 @ [ADD] \<Turnstile> cfs\<box>"
    (is "?P \<Turnstile> _\<box>")
  assume "cfs ! 0 = (pc, s, stk)" and "mpred ?P cfs 0 k" and
    B: "k < length cfs" and 
    C: "cfs ! k = (size (acomp a\<^sub>1) + size (acomp a\<^sub>2), s,
      aval a\<^sub>2 s # aval a\<^sub>1 s # stk)"
  moreover from this have "mpred ?P cfs k (Suc k)"
    by (simp add: mpred_def msp_def)
  moreover have "cfs ! Suc k = (size ?P, s, aval (Plus a\<^sub>1 a\<^sub>2) s # stk)"
    using A and B and C by (insert execl_next [of ?P cfs k],
     simp add: execl_all_def, drule_tac impI, auto)
  ultimately show "mpred ?P cfs 0 (length cfs - Suc 0)"
    using A by (insert execl_last [of ?P cfs "Suc k"], simp add: execl_all_def,
     drule_tac impI, auto intro: mpred_merge)
qed

lemma bcomp_correct_m [simplified, intro]:
 "\<lbrakk>bcomp x \<Turnstile> cfs\<box>; 0 \<le> snd (snd x)\<rbrakk> \<Longrightarrow> mpred (bcomp x) cfs 0 (length cfs - 1)"
proof (induction x arbitrary: cfs rule: bcomp.induct, force simp: mpred_def msp_def,
 (simp add: Let_def)+, fastforce, subst (asm) bcomp.simps, frule acomp_acomp_m,
 auto simp del: bcomp.simps, subst bcomp.simps)
  fix a\<^sub>1 a\<^sub>2 f i cfs pc s stk k
  assume A: "acomp a\<^sub>1 @ acomp a\<^sub>2 @
    (if f then [JMPLESS i] else [JMPGE i]) \<Turnstile> cfs\<box>"
    (is "?P \<Turnstile> _\<box>")
  assume "cfs ! 0 = (pc, s, stk)" and "mpred ?P cfs 0 k" and
    B: "k < length cfs" and 
    C: "cfs ! k = (size (acomp a\<^sub>1) + size (acomp a\<^sub>2), s,
      aval a\<^sub>2 s # aval a\<^sub>1 s # stk)"
  moreover from this have "mpred ?P cfs k (Suc k)"
    by (simp add: mpred_def msp_def)
  moreover from this have D: "cfs ! Suc k =
    (size ?P + (if bval (Less a\<^sub>1 a\<^sub>2) s = f then i else 0), s, stk)"
    using A and B and C by (insert execl_next [of ?P cfs k],
     simp add: execl_all_def, drule_tac impI, auto)
  assume "0 \<le> i"
  with A and B and C and D have "length cfs - 1 = Suc k"
    by (rule_tac execl_last, auto simp: execl_all_def, simp split: if_split_asm)
  ultimately show "mpred ?P cfs 0 (length cfs - Suc 0)"
    by (auto intro: mpred_merge)
qed


lemma bcomp_ccomp_m:
  assumes A: "bcomp (b, f, i) @ ccomp c @ P \<Turnstile> cfs\<box>"
    (is "bcomp ?x @ ?cc @ _ \<Turnstile> _\<box>")
  assumes
    B: "\<And>cfs. ?cc \<Turnstile> cfs\<box> \<Longrightarrow> mpred ?cc cfs 0 (length cfs - 1)" and
    C: "0 \<le> i"
  shows "case cfs ! 0 of (pc, s, stk) \<Rightarrow> \<exists>k < length cfs. \<exists>s'.
    cfs ! k = (size (bcomp ?x) + (if bval b s = f then i else size ?cc), s', stk) \<and>
    mpred (bcomp ?x @ ?cc @ P) cfs 0 k"
proof -
  let ?P = "bcomp ?x @ ?cc @ P"
  have "\<exists>k < length cfs. bpred ?x (off [] (cfs ! 0)) (off [] (cfs ! k)) \<and>
    mpred ([] @ ?P) cfs 0 k"
    using A and C by (rule_tac execl_all_sub_m, insert execl_all_def, auto)
  then obtain s stk k where
   "cfs ! 0 = (0, s, stk) \<and> mpred ?P cfs 0 k \<and> k < length cfs" and
    D: "cfs ! k = (size (bcomp ?x) + (if bval b s = f then i else 0), s, stk)"
    using A by (auto simp: bpred_def execl_all_def)
  moreover from this have "bval b s \<noteq> f \<Longrightarrow> \<exists>k' < length cfs. cpred c
    (off (bcomp ?x) (cfs ! k)) (off (bcomp ?x) (cfs ! k')) \<and> mpred ?P cfs k k'"
    using A and B by (rule_tac execl_all_sub_m, insert execl_all_def, auto)
  then obtain k' s' where "bval b s \<noteq> f \<Longrightarrow> k' < length cfs \<and> mpred ?P cfs k k' \<and>
    cfs ! k' = (size (bcomp ?x @ ?cc), s', stk)"
    using D by (fastforce simp: cpred_def prod_eq_iff)
  ultimately show ?thesis
    by (auto intro: mpred_merge)
qed

lemma ccomp_ccomp_m [simplified, intro]:
  assumes
    A: "ccomp c\<^sub>1 @ ccomp c\<^sub>2 \<Turnstile> cfs\<box>"
      (is "?P \<Turnstile> _\<box>") and
    B: "\<And>cfs. ccomp c\<^sub>1 \<Turnstile> cfs\<box> \<Longrightarrow> mpred (ccomp c\<^sub>1) cfs 0 (length cfs - 1)" and
    C: "\<And>cfs. ccomp c\<^sub>2 \<Turnstile> cfs\<box> \<Longrightarrow> mpred (ccomp c\<^sub>2) cfs 0 (length cfs - 1)"
  shows "mpred ?P cfs 0 (length cfs - 1)"
proof -
  have "\<exists>k < length cfs. cpred c\<^sub>1 (off [] (cfs ! 0)) (off [] (cfs ! k)) \<and>
    mpred ([] @ ?P) cfs 0 k"
    using A and B by (rule_tac execl_all_sub_m, insert execl_all_def, auto)
  then obtain k s s' stk where
   "cfs ! 0 = (0, s, stk) \<and> mpred ?P cfs 0 k \<and> k < length cfs" and
    D: "cfs ! k = (size (ccomp c\<^sub>1), s', stk)"
    using A by (auto simp: cpred_def execl_all_def)
  moreover from this have "\<exists>k' < length cfs. cpred c\<^sub>2 (off (ccomp c\<^sub>1) (cfs ! k))
    (off (ccomp c\<^sub>1) (cfs ! k')) \<and> mpred (ccomp c\<^sub>1 @ ccomp c\<^sub>2 @ []) cfs k k'"
    using A and C by (rule_tac execl_all_sub_m, insert execl_all_def, auto)
  then obtain k' where
   "fst (cfs ! k') = size ?P \<and> mpred ?P cfs k k' \<and> k' < length cfs"
    using D by (fastforce simp: cpred_def)
  ultimately show ?thesis
    using A by (insert execl_last [of ?P cfs k'], simp add: execl_all_def,
     auto intro: mpred_merge)
qed

lemma while_correct_m [simplified, simplified Let_def, intro]:
 "\<lbrakk>bcomp (b, False, size (ccomp c) + 1) @ ccomp c @
    [JMP (- (size (bcomp (b, False, size (ccomp c) + 1) @ ccomp c) + 1))]
      \<Turnstile> cfs\<box>;
    \<And>cfs. ccomp c \<Turnstile> cfs\<box> \<Longrightarrow> mpred (ccomp c) cfs 0 (length cfs - 1)\<rbrakk> \<Longrightarrow>
  mpred (ccomp (WHILE b DO c)) cfs 0 (length cfs - Suc 0)"
  (is "\<lbrakk>?cb @ ?cc @ _ \<Turnstile> _\<box>; \<And>_. _ \<Longrightarrow> _\<rbrakk> \<Longrightarrow> _")
proof (induction cfs rule: length_induct, frule bcomp_ccomp_m,
 auto simp: Let_def split: if_split_asm)
  fix cfs s stk k
  assume "?cb @ ?cc @ [JMP (- size ?cb - size ?cc - 1)] \<Turnstile> cfs\<box>"
    (is "?P \<Turnstile> _\<box>")
  moreover assume "mpred ?P cfs 0 k" and "k < length cfs" and
   "cfs ! k = (size ?cb + (size ?cc + 1), s, stk)"
  ultimately show "mpred ?P cfs 0 (length cfs - Suc 0)"
    by (insert execl_last [of ?P cfs k], simp add: execl_all_def)
next
  fix cfs pc s s' stk k
  assume A: "?cb @ ?cc @ [JMP (- size ?cb - size ?cc - 1)] \<Turnstile> cfs\<box>"
    (is "?P \<Turnstile> _\<box>")
  assume B: "k < length cfs" and C: "cfs ! k = (size ?cb + size ?cc, s', stk)"
  moreover from this have D: "k \<noteq> length cfs - 1"
    using A by (rule_tac notI, simp add: execl_all_def)
  ultimately have E: "cfs ! Suc k = (0, s', stk)"
    using A by (insert execl_next [of ?P cfs k], auto simp: execl_all_def)
  moreover have F: "Suc k + (length (drop (Suc k) cfs) - 1) = length cfs - 1"
    (is "_ + (length ?cfs - _) = _")
    using B and D by simp
  ultimately have "?P \<Turnstile> ?cfs\<box>"
    using A and B and D by (auto simp: execl_all_def intro: execl_drop)
  moreover assume "\<forall>cfs'. length cfs' < length cfs \<longrightarrow> ?P \<Turnstile> cfs'\<box> \<longrightarrow>
    mpred ?P cfs' 0 (length cfs' - Suc 0)"
  ultimately have "mpred ?P ?cfs 0 (length ?cfs - 1)"
    using B by force
  moreover assume G: "cfs ! 0 = (pc, s, stk)"
  ultimately have "mpred ?P cfs (Suc k + 0) (Suc k + (length ?cfs - 1))"
    using B and E by (rule_tac mpred_drop, simp_all)
  hence "mpred ?P cfs (Suc k) (length cfs - 1)"
    by (subst (asm) F, simp)
  moreover assume "mpred ?P cfs 0 k"
  moreover have "mpred ?P cfs k (Suc k)"
    using C and G by (simp add: mpred_def msp_def)
  ultimately show "mpred ?P cfs 0 (length cfs - Suc 0)"
    by (auto intro: mpred_merge)
qed

lemma ccomp_correct_m:
 "ccomp c \<Turnstile> cfs\<box> \<Longrightarrow> mpred (ccomp c) cfs 0 (length cfs - 1)"
proof (induction c arbitrary: cfs, (fastforce simp: mpred_def)+,
 simp_all add: Let_def, frule_tac [3] bcomp_ccomp_m, auto split: if_split_asm)
  fix a x cfs
  assume A: "acomp a @ [STORE x] \<Turnstile> cfs\<box>"
    (is "?P \<Turnstile> _\<box>")
  hence "\<exists>k < length cfs. apred a (off [] (cfs ! 0)) (off [] (cfs ! k)) \<and>
    mpred ([] @ ?P) cfs 0 k"
    by (rule_tac execl_all_sub_m, insert execl_all_def, auto)
  then obtain k s stk where "cfs ! 0 = (0, s, stk) \<and> mpred ?P cfs 0 k" and
    B: "k < length cfs \<and> cfs ! k = (size (acomp a), s, aval a s # stk)"
    using A by (auto simp: apred_def execl_all_def)
  moreover from this have "mpred ?P cfs k (Suc k)"
    by (simp add: mpred_def msp_def)
  moreover have "cfs ! Suc k = (size (acomp a) + 1, s(x := aval a s), stk)"
    using A and B by (insert execl_next [of "acomp a @ [STORE x]" cfs k],
     simp add: execl_all_def, drule_tac impI, auto)
  ultimately show "mpred ?P cfs 0 (length cfs - Suc 0)"
    using A by (insert execl_last [of ?P cfs "Suc k"], simp add: execl_all_def,
     drule_tac impI, auto intro: mpred_merge)
next
  fix b c\<^sub>1 c\<^sub>2 cfs pc s s' stk k
  assume A: "bcomp (b, False, size (ccomp c\<^sub>1) + 1) @ ccomp c\<^sub>1 @
    JMP (size (ccomp c\<^sub>2)) # ccomp c\<^sub>2 \<Turnstile> cfs\<box>"
    (is "?cb @ ?cc\<^sub>1 @ ?i # ?cc\<^sub>2 \<Turnstile> _\<box>")
  let ?P = "?cb @ ?cc\<^sub>1 @ [?i]"
  assume B: "cfs ! k = (size ?cb + (size ?cc\<^sub>1 + 1), s', stk)"
  assume "cfs ! 0 = (pc, s, stk)" and "k < length cfs" and
   "\<And>cfs. ?cc\<^sub>2 \<Turnstile> cfs\<box> \<Longrightarrow> mpred ?cc\<^sub>2 cfs 0 (length cfs - Suc 0)"
  hence "\<exists>k' < length cfs. cpred c\<^sub>2 (off ?P (cfs ! k)) (off ?P (cfs ! k')) \<and>
    mpred (?P @ ?cc\<^sub>2 @ []) cfs k k'"
    using A and B by (rule_tac execl_all_sub_m, insert execl_all_def, auto)
  then obtain k' where "fst (cfs ! k') = size (?P @ ?cc\<^sub>2) \<and>
    mpred (?P @ ?cc\<^sub>2) cfs k k' \<and> k' < length cfs"
    using B by (fastforce simp: cpred_def)
  moreover assume "mpred (?cb @ ?cc\<^sub>1 @ ?i # ?cc\<^sub>2) cfs 0 k"
  ultimately show "mpred (?cb @ ?cc\<^sub>1 @ ?i # ?cc\<^sub>2) cfs 0 (length cfs - Suc 0)"
    using A by (insert execl_last [of "?P @ ?cc\<^sub>2" cfs k'], simp add: execl_all_def,
     auto intro: mpred_merge)
next
  fix b c\<^sub>1 c\<^sub>2 cfs pc s s' stk k
  assume A: "bcomp (b, False, size (ccomp c\<^sub>1) + 1) @ ccomp c\<^sub>1 @
    JMP (size (ccomp c\<^sub>2)) # ccomp c\<^sub>2 \<Turnstile> cfs\<box>"
    (is "?cb @ ?cc\<^sub>1 @ ?i # ?cc\<^sub>2 \<Turnstile> _\<box>")
  let ?P = "?cb @ ?cc\<^sub>1 @ ?i # ?cc\<^sub>2"
  assume B: "k < length cfs" and C: "cfs ! k = (size ?cb + size ?cc\<^sub>1, s', stk)"
  hence "cfs ! Suc k = (size ?P, s', stk)"
    using A by (insert execl_next [of "?P" cfs k], simp add: execl_all_def,
     drule_tac impI, auto)
  moreover assume "cfs ! 0 = (pc, s, stk)"
  hence "mpred ?P cfs k (Suc k)"
    using C by (simp add: mpred_def msp_def)
  moreover assume "mpred ?P cfs 0 k" 
  ultimately show "mpred ?P cfs 0 (length cfs - Suc 0)"
    using A and B by (insert execl_last [of ?P cfs "Suc k"], simp add: execl_all_def,
     drule_tac impI, auto intro: mpred_merge)
qed

text \<open>
\null

Here below are the proofs of theorems @{text m_ccomp_bigstep} and @{text m_ccomp_exec}, which
establish that machine programs simulate source ones and vice versa. The former theorem is inferred
from theorem @{thm [source] ccomp_bigstep} and lemmas @{thm [source] mpred_execl_m_exec},
@{thm [source] ccomp_correct_m}, the latter one from lemma @{thm [source] m_exec_exec} and theorem
@{text ccomp_exec}, in turn derived from lemma @{thm [source] ccomp_correct}.

\null
\<close>

lemma exec_execl [dest!]:
 "P \<turnstile> cf \<rightarrow>* cf' \<Longrightarrow> \<exists>cfs. P \<Turnstile> cfs \<and> cfs \<noteq> [] \<and> hd cfs = cf \<and> last cfs = cf'"
by (erule star.induct, force, erule exE, rule list.exhaust, blast,
 simp del: last.simps, rule exI, subst execl.simps(1), simp)

theorem m_ccomp_bigstep:
 "(c, s) \<Rightarrow> s' \<Longrightarrow>
    m_ccomp c \<^bold>\<turnstile> (0, m_state c s, 0) \<^bold>\<rightarrow>\<^bold>* (size (m_ccomp c), m_state c s', 0)"
by (drule ccomp_bigstep [where stk = "[]"], drule exec_execl, clarify,
 frule mpred_execl_m_exec, simp, rule ccomp_correct_m, simp_all add:
 hd_conv_nth last_conv_nth execl_all_def)


theorem ccomp_exec:
 "ccomp c \<turnstile> (0, s, stk) \<rightarrow>* (size (ccomp c), s', stk') \<Longrightarrow> (c, s) \<Rightarrow> s' \<and> stk' = stk"
by (insert ccomp_correct, force simp: hd_conv_nth last_conv_nth execl_all_def cpred_def)

theorem m_ccomp_exec:
 "m_ccomp c \<^bold>\<turnstile> (0, ms, 0) \<^bold>\<rightarrow>\<^bold>* (size (m_ccomp c), ms', sp) \<Longrightarrow>
    (c, state c ms) \<Rightarrow> state c ms' \<and> sp = 0"
by (drule m_exec_exec [where stk = "[]"], simp, drule ccomp_exec,
 cases "0 < sp", simp_all, drule add_stack_nnil, blast)

end
