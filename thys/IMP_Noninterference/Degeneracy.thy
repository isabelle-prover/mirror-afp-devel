(*  Title:       Information Flow Control via Stateful Intransitive Noninterference in Language IMP
    Author:      Pasquale Noce
                 Senior Staff Firmware Engineer at HID Global, Italy
                 pasquale dot noce dot lavoro at gmail dot com
                 pasquale dot noce at hidglobal dot com
*)

section "Degeneracy to stateless level-based information flow control"

theory Degeneracy
  imports Correctness "HOL-IMP.Sec_TypingT"
begin

text \<open>
\null

The goal of this concluding section is to prove the degeneracy of the information flow correctness
notion and the static type system defined in this paper to the classical counterparts addressed in
\<^cite>\<open>"Nipkow23-1"\<close>, section 9.2.6, and formalized in \<^cite>\<open>"Nipkow23-2"\<close> and \<^cite>\<open>"Nipkow23-3"\<close>, in
case of a stateless level-based information flow correctness policy.

First of all, locale @{locale noninterf} is interpreted within the context of the class @{class sec}
defined in \<^cite>\<open>"Nipkow23-2"\<close>, as follows.

  \<^item> Parameter @{text dom} is instantiated as function @{text sec}, which also sets the type variable
standing for the type of the domains to @{typ nat}.

  \<^item> Parameter @{text interf} is instantiated as the predicate such that for any program state, the
output is @{const True} just in case the former input level may interfere with, namely is not larger
than, the latter one.

  \<^item> Parameter @{text state} is instantiated as the empty set, consistently with the fact that the
policy is represented by a single, stateless interference predicate.

Next, the information flow security notion implied by theorem @{thm [source] noninterference} in
\<^cite>\<open>"Nipkow23-3"\<close> is formalized as a predicate @{text secure} taking a program as input. This
notion is then proven to be implied, in the degenerate interpretation described above, by the
information flow correctness notion formalized as predicate @{const [names_short] noninterf.correct} 
(theorem @{text correct_secure}). Particularly:

  \<^item> This theorem demands the additional assumption that the @{typ "state set"} @{term A} input to
@{const [names_short] noninterf.correct} is nonempty, since @{const [names_short] noninterf.correct}
is vacuously true for @{prop "A = {}"}.

  \<^item> In order for this theorem to hold, predicate @{text secure} needs to slight differ from the
information flow security notion implied by theorem @{thm [source] noninterference}, in that it
requires state @{term t'} to exist if there also exists some variable with a level not larger than
@{term l}, namely if condition @{prop "s = t (\<le> l)"} is satisfied \emph{nontrivially} -- actually,
no leakage may arise from two initial states disagreeing on the value of \emph{every} variable. In
fact, predicate @{const [names_short] noninterf.correct} requires a nontrivial configuration
@{term "(c\<^sub>2', t\<^sub>2)"} to exist in case condition @{prop "s\<^sub>1 = t\<^sub>1 (\<subseteq> sources cs s\<^sub>1 x)"} is satisfied
\emph{for some variable} \lstinline{x}.

Finally, the static type system @{const [names_short] noninterf.ctyping2} is proven to be equivalent
to the @{const sec_type} one defined in \<^cite>\<open>"Nipkow23-3"\<close> in the above degenerate interpretation
(theorems @{text ctyping2_sec_type} and @{text sec_type_ctyping2}). The former theorem, which proves
that a \emph{pass} verdict from @{const [names_short] noninterf.ctyping2} implies the issuance of a
\emph{pass} verdict from @{const sec_type} as well, demands the additional assumptions that (a) the
@{typ "state set"} input to @{const [names_short] noninterf.ctyping2} is nonempty, (b) the input
program does not contain any loop with @{term "Bc True"} as boolean condition, and (c) the input
program has undergone \emph{constant folding}, as addressed in \<^cite>\<open>"Nipkow23-1"\<close>, section 3.1.3
for arithmetic expressions and in \<^cite>\<open>"Nipkow23-1"\<close>, section 3.2.1 for boolean expressions. Why?

This need arises from the different ways in which the two type systems handle ``dead'' conditional
branches. Type system @{const sec_type} does not try to detect ``dead'' branches; it simply applies
its full range of information flow security checks to any conditional branch contained in the input
program, even if it actually is a ``dead'' one. On the contrary, type system @{const [names_short]
noninterf.ctyping2} detects ``dead'' branches whenever boolean conditions can be evaluated at
compile time, and applies only a subset of its information flow correctness checks to such branches.

As parameter @{text state} is instantiated as the empty set, boolean conditions containing variables
cannot be evaluated at compile time, yet they can if they only contain constants. Thus, assumption
(a) prevents @{const [names_short] noninterf.ctyping2} from handling the entire input program as a
``dead'' branch, while assumptions (b) and (c) ensure that @{const [names_short] noninterf.ctyping2}
will not detect any ``dead'' conditional branch within the program. On the whole, those assumptions
guarantee that @{const [names_short] noninterf.ctyping2}, like @{const sec_type}, applies its full
range of checks to \emph{any} conditional branch contained in the input program, as required for
theorem @{text ctyping2_sec_type} to hold.
\<close>


subsection "Global context definitions and proofs"

fun cgood :: "com \<Rightarrow> bool" where
"cgood (c\<^sub>1;; c\<^sub>2) = (cgood c\<^sub>1 \<and> cgood c\<^sub>2)" |
"cgood (IF _ THEN c\<^sub>1 ELSE c\<^sub>2) = (cgood c\<^sub>1 \<and> cgood c\<^sub>2)" |
"cgood (WHILE b DO c) = (b \<noteq> Bc True \<and> cgood c)" |
"cgood _ = True"


fun seq :: "com \<Rightarrow> com \<Rightarrow> com" where
"seq SKIP c = c" |
"seq c SKIP = c" |
"seq c\<^sub>1 c\<^sub>2 = c\<^sub>1;; c\<^sub>2"

fun ifc :: "bexp \<Rightarrow> com \<Rightarrow> com \<Rightarrow> com" where
"ifc (Bc True) c _ = c" |
"ifc (Bc False) _ c = c" |
"ifc b c\<^sub>1 c\<^sub>2 = (if c\<^sub>1 = c\<^sub>2 then c\<^sub>1 else IF b THEN c\<^sub>1 ELSE c\<^sub>2)"

fun while :: "bexp \<Rightarrow> com \<Rightarrow> com" where
"while (Bc False) _ = SKIP" |
"while b c = WHILE b DO c"

primrec csimp :: "com \<Rightarrow> com" where
"csimp SKIP = SKIP" |
"csimp (x ::= a) = x ::= asimp a" |
"csimp (c\<^sub>1;; c\<^sub>2) = seq (csimp c\<^sub>1) (csimp c\<^sub>2)" |
"csimp (IF b THEN c\<^sub>1 ELSE c\<^sub>2) = ifc (bsimp b) (csimp c\<^sub>1) (csimp c\<^sub>2)" |
"csimp (WHILE b DO c) = while (bsimp b) (csimp c)"


lemma not_size:
 "size (not b) \<le> Suc (size b)"
by (induction b rule: not.induct, simp_all)

lemma and_size:
 "size (and b\<^sub>1 b\<^sub>2) \<le> Suc (size b\<^sub>1 + size b\<^sub>2)"
by (induction b\<^sub>1 b\<^sub>2 rule: and.induct, simp_all)

lemma less_size:
 "size (less a\<^sub>1 a\<^sub>2) = 0"
by (induction a\<^sub>1 a\<^sub>2 rule: less.induct, simp_all)

lemma bsimp_size:
 "size (bsimp b) \<le> size b"
by (induction b, auto intro: le_trans not_size and_size simp: less_size)


lemma seq_size:
 "size (seq c\<^sub>1 c\<^sub>2) \<le> Suc (size c\<^sub>1 + size c\<^sub>2)"
by (induction c\<^sub>1 c\<^sub>2 rule: seq.induct, simp_all)

lemma ifc_size:
 "size (ifc b c\<^sub>1 c\<^sub>2) \<le> Suc (size c\<^sub>1 + size c\<^sub>2)"
by (induction b c\<^sub>1 c\<^sub>2 rule: ifc.induct, simp_all)

lemma while_size:
 "size (while b c) \<le> Suc (size c)"
by (induction b c rule: while.induct, simp_all)

lemma csimp_size:
 "size (csimp c) \<le> size c"
by (induction c, auto intro: le_trans seq_size ifc_size while_size)


lemma avars_asimp:
 "avars a = {} \<Longrightarrow> \<exists>i. asimp a = N i"
by (induction a, auto)

lemma seq_match [dest!]:
 "seq (csimp c\<^sub>1) (csimp c\<^sub>2) = c\<^sub>1;; c\<^sub>2 \<Longrightarrow> csimp c\<^sub>1 = c\<^sub>1 \<and> csimp c\<^sub>2 = c\<^sub>2"
by (rule seq.cases [of "(csimp c\<^sub>1, csimp c\<^sub>2)"],
 insert csimp_size [of c\<^sub>1], insert csimp_size [of c\<^sub>2], simp_all)

lemma ifc_match [dest!]:
 "ifc (bsimp b) (csimp c\<^sub>1) (csimp c\<^sub>2) = IF b THEN c\<^sub>1 ELSE c\<^sub>2 \<Longrightarrow>
    bsimp b = b \<and> (\<forall>v. b \<noteq> Bc v) \<and> csimp c\<^sub>1 = c\<^sub>1 \<and> csimp c\<^sub>2 = c\<^sub>2"
by (insert csimp_size [of c\<^sub>1], insert csimp_size [of c\<^sub>2],
 subgoal_tac "csimp c\<^sub>1 \<noteq> IF b THEN c\<^sub>1 ELSE c\<^sub>2", auto intro: ifc.cases
 [of "(bsimp b, csimp c\<^sub>1, csimp c\<^sub>2)"] split: if_split_asm)

lemma while_match [dest!]:
 "while (bsimp b) (csimp c) = WHILE b DO c \<Longrightarrow>
    bsimp b = b \<and> b \<noteq> Bc False \<and> csimp c = c"
by (rule while.cases [of "(bsimp b, csimp c)"], auto)


subsection "Local context definitions and proofs"

context sec
begin


interpretation noninterf "\<lambda>s. (\<le>)" sec "{}"
by (unfold_locales, simp)

notation interf_set  ("(_: _ \<leadsto> _)" [51, 51, 51] 50)
notation univ_states_if  ("(Univ? _ _)" [51, 75] 75)
notation atyping  ("(_ \<Turnstile> _ '(\<subseteq> _'))" [51, 51] 50)
notation btyping2_aux  ("(\<TTurnstile> _ '(\<subseteq> _, _'))" [51] 55)
notation btyping2  ("(\<Turnstile> _ '(\<subseteq> _, _'))" [51] 55)
notation ctyping1  ("(\<turnstile> _ '(\<subseteq> _, _'))" [51] 55)
notation ctyping2  ("(_ \<Turnstile> _ '(\<subseteq> _, _'))" [51, 51] 55)


abbreviation eq_le_ext :: "state \<Rightarrow> state \<Rightarrow> level \<Rightarrow> bool"
  ("(_ = _ '(\<^bold>\<le> _'))" [51, 51, 0] 50) where
"s = t (\<^bold>\<le> l) \<equiv> s = t (\<le> l) \<and> (\<exists>x :: vname. sec x \<le> l)"

definition secure :: "com \<Rightarrow> bool" where
"secure c \<equiv> \<forall>s s' t l. (c, s) \<Rightarrow> s' \<and> s = t (\<^bold>\<le> l) \<longrightarrow>
  (\<exists>t'. (c, t) \<Rightarrow> t' \<and> s' = t' (\<le> l))"

definition levels :: "config set \<Rightarrow> level set" where
"levels U \<equiv> insert 0 (sec ` \<Union> (snd ` {(B, Y) \<in> U. B \<noteq> {}}))"


lemma avars_finite:
 "finite (avars a)"
by (induction a, simp_all)

lemma avars_in:
 "n < sec a \<Longrightarrow> sec a \<in> sec ` avars a"
by (induction a, auto simp: max_def)

lemma avars_sec:
 "x \<in> avars a \<Longrightarrow> sec x \<le> sec a"
by (induction a, auto)

lemma avars_ub:
 "sec a \<le> l = (\<forall>x \<in> avars a. sec x \<le> l)"
by (induction a, auto)


lemma bvars_finite:
 "finite (bvars b)"
by (induction b, simp_all add: avars_finite)

lemma bvars_in:
 "n < sec b \<Longrightarrow> sec b \<in> sec ` bvars b"
by (induction b, auto dest!: avars_in simp: max_def)

lemma bvars_sec:
 "x \<in> bvars b \<Longrightarrow> sec x \<le> sec b"
by (induction b, auto dest: avars_sec)

lemma bvars_ub:
 "sec b \<le> l = (\<forall>x \<in> bvars b. sec x \<le> l)"
by (induction b, auto simp: avars_ub)


lemma levels_insert:
  assumes
    A: "A \<noteq> {}" and
    B: "finite (levels U)"
  shows "finite (levels (insert (A, bvars b) U)) \<and>
    Max (levels (insert (A, bvars b) U)) = max (sec b) (Max (levels U))"
    (is "finite (levels ?U') \<and> ?P")
proof -
  have C: "levels ?U' = sec ` bvars b \<union> levels U"
    using A by (auto simp: image_def levels_def univ_states_if_def)
  hence D: "finite (levels ?U')"
    using B by (simp add: bvars_finite)
  moreover have ?P
  proof (rule Max_eqI [OF D])
    fix l
    assume "l \<in> levels (insert (A, bvars b) U)"
    thus "l \<le> max (sec b) (Max (levels U))"
      using C by (auto dest: Max_ge [OF B] bvars_sec)
  next
    show "max (sec b) (Max (levels U)) \<in> levels (insert (A, bvars b) U)"
      using C by (insert Max_in [OF B],
       fastforce dest: bvars_in simp: max_def not_le levels_def)
  qed
  ultimately show ?thesis ..
qed

lemma sources_le:
 "y \<in> sources cs s x \<Longrightarrow> sec y \<le> sec x"
and sources_aux_le:
 "y \<in> sources_aux cs s x \<Longrightarrow> sec y \<le> sec x"
by (induction cs s x and cs s x rule: sources_induct,
 auto split: com_flow.split_asm if_split_asm, fastforce+)


lemma bsimp_btyping2_aux_not [intro]:
 "\<lbrakk>bsimp b = b \<Longrightarrow> \<forall>v. b \<noteq> Bc v \<Longrightarrow> \<TTurnstile> b (\<subseteq> A, X) = None;
    not (bsimp b) = Not b\<rbrakk> \<Longrightarrow> \<TTurnstile> b (\<subseteq> A, X) = None"
by (rule not.cases [of "bsimp b"], auto)

lemma bsimp_btyping2_aux_and [intro]:
  assumes
    A: "\<lbrakk>bsimp b\<^sub>1 = b\<^sub>1; \<forall>v. b\<^sub>1 \<noteq> Bc v\<rbrakk> \<Longrightarrow> \<TTurnstile> b\<^sub>1 (\<subseteq> A, X) = None" and
    B: "and (bsimp b\<^sub>1) (bsimp b\<^sub>2) = And b\<^sub>1 b\<^sub>2"
  shows "\<TTurnstile> b\<^sub>1 (\<subseteq> A, X) = None"
proof -
  {
    assume "bsimp b\<^sub>2 = And b\<^sub>1 b\<^sub>2"
    hence "Bc True = b\<^sub>1"
      by (insert bsimp_size [of b\<^sub>2], simp)
  }
  moreover {
    assume "bsimp b\<^sub>2 = And (Bc True) b\<^sub>2"
    hence False
      by (insert bsimp_size [of b\<^sub>2], simp)
  }
  moreover {
    assume "bsimp b\<^sub>1 = And b\<^sub>1 b\<^sub>2"
    hence False
      by (insert bsimp_size [of b\<^sub>1], simp)
  }
  ultimately have "bsimp b\<^sub>1 = b\<^sub>1 \<and> (\<forall>v. b\<^sub>1 \<noteq> Bc v)"
    using B by (auto intro: and.cases [of "(bsimp b\<^sub>1, bsimp b\<^sub>2)"])
  thus ?thesis
    using A by simp
qed

lemma bsimp_btyping2_aux_less [elim]:
 "\<lbrakk>less (asimp a\<^sub>1) (asimp a\<^sub>2) = Less a\<^sub>1 a\<^sub>2;
    avars a\<^sub>1 = {}; avars a\<^sub>2 = {}\<rbrakk> \<Longrightarrow> False"
by (fastforce dest: avars_asimp)

lemma bsimp_btyping2_aux:
 "\<lbrakk>bsimp b = b; \<forall>v. b \<noteq> Bc v\<rbrakk> \<Longrightarrow> \<TTurnstile> b (\<subseteq> A, X) = None"
by (induction b, auto split: option.split)

lemma bsimp_btyping2:
 "\<lbrakk>bsimp b = b; \<forall>v. b \<noteq> Bc v\<rbrakk> \<Longrightarrow> \<Turnstile> b (\<subseteq> A, X) = (A, A)"
by (auto dest: bsimp_btyping2_aux [of _ A X] simp: btyping2_def)


lemma csimp_ctyping2_if:
 "\<lbrakk>\<And>U' B B'. U' = U \<Longrightarrow> B = B\<^sub>1 \<Longrightarrow> {} = B' \<Longrightarrow> B\<^sub>1 \<noteq> {} \<Longrightarrow> False; s \<in> A;
    \<Turnstile> b (\<subseteq> A, X) = (B\<^sub>1, B\<^sub>2); bsimp b = b; \<forall>v. b \<noteq> Bc v\<rbrakk> \<Longrightarrow>
  False"
by (drule bsimp_btyping2 [of _ A X], auto)

lemma csimp_ctyping2_while:
 "\<lbrakk>(if P then Some (B\<^sub>2 \<union> B\<^sub>2', Y) else None) = Some ({}, Z); s \<in> A;
    \<Turnstile> b (\<subseteq> A, X) = (B\<^sub>1, B\<^sub>2); bsimp b = b; b \<noteq> Bc True; b \<noteq> Bc False\<rbrakk> \<Longrightarrow>
  False"
by (drule bsimp_btyping2 [of _ A X], auto split: if_split_asm)

lemma csimp_ctyping2:
 "\<lbrakk>(U, v) \<Turnstile> c (\<subseteq> A, X) = Some (B, Y); A \<noteq> {}; cgood c; csimp c = c\<rbrakk> \<Longrightarrow>
    B \<noteq> {}"
proof (induction "(U, v)" c A X arbitrary: B Y U v rule: ctyping2.induct)
  fix A X B Y U v c\<^sub>1 c\<^sub>2
  show
   "\<lbrakk>\<And>B Y. (U, v) \<Turnstile> c\<^sub>1 (\<subseteq> A, X) = Some (B, Y) \<Longrightarrow>
      A \<noteq> {} \<Longrightarrow> cgood c\<^sub>1 \<Longrightarrow> csimp c\<^sub>1 = c\<^sub>1 \<Longrightarrow>
      B \<noteq> {};
    \<And>p B Y C Z. (U, v) \<Turnstile> c\<^sub>1 (\<subseteq> A, X) = Some p \<Longrightarrow>
      (B, Y) = p \<Longrightarrow> (U, v) \<Turnstile> c\<^sub>2 (\<subseteq> B, Y) = Some (C, Z) \<Longrightarrow>
      B \<noteq> {} \<Longrightarrow> cgood c\<^sub>2 \<Longrightarrow> csimp c\<^sub>2 = c\<^sub>2 \<Longrightarrow>
      C \<noteq> {};
    (U, v) \<Turnstile> c\<^sub>1;; c\<^sub>2 (\<subseteq> A, X) = Some (B, Y);
    A \<noteq> {}; cgood (c\<^sub>1;; c\<^sub>2);
    csimp (c\<^sub>1;; c\<^sub>2) = c\<^sub>1;; c\<^sub>2\<rbrakk> \<Longrightarrow>
      B \<noteq> {}"
    by (fastforce split: option.split_asm)
next
  fix A X C Y U v b c\<^sub>1 c\<^sub>2
  show
   "\<lbrakk>\<And>U' p B\<^sub>1 B\<^sub>2 C Y.
      (U', p) = (insert (Univ? A X, bvars b) U, \<Turnstile> b (\<subseteq> A, X)) \<Longrightarrow>
      (B\<^sub>1, B\<^sub>2) = p \<Longrightarrow> (U', v) \<Turnstile> c\<^sub>1 (\<subseteq> B\<^sub>1, X) = Some (C, Y) \<Longrightarrow>
      B\<^sub>1 \<noteq> {} \<Longrightarrow> cgood c\<^sub>1 \<Longrightarrow> csimp c\<^sub>1 = c\<^sub>1 \<Longrightarrow>
      C \<noteq> {};
    \<And>U' p B\<^sub>1 B\<^sub>2 C Y.
      (U', p) = (insert (Univ? A X, bvars b) U, \<Turnstile> b (\<subseteq> A, X)) \<Longrightarrow>
      (B\<^sub>1, B\<^sub>2) = p \<Longrightarrow> (U', v) \<Turnstile> c\<^sub>2 (\<subseteq> B\<^sub>2, X) = Some (C, Y) \<Longrightarrow>
      B\<^sub>2 \<noteq> {} \<Longrightarrow> cgood c\<^sub>2 \<Longrightarrow> csimp c\<^sub>2 = c\<^sub>2 \<Longrightarrow>
      C \<noteq> {};
      (U, v) \<Turnstile> IF b THEN c\<^sub>1 ELSE c\<^sub>2 (\<subseteq> A, X) = Some (C, Y);
    A \<noteq> {}; cgood (IF b THEN c\<^sub>1 ELSE c\<^sub>2);
    csimp (IF b THEN c\<^sub>1 ELSE c\<^sub>2) = IF b THEN c\<^sub>1 ELSE c\<^sub>2\<rbrakk> \<Longrightarrow>
      C \<noteq> {}"
    by (auto split: option.split_asm prod.split_asm,
     rule csimp_ctyping2_if)
next
  fix A X B Z U v b c
  show
   "\<lbrakk>\<And>B\<^sub>1 B\<^sub>2 C Y B\<^sub>1' B\<^sub>2' B Z.
      (B\<^sub>1, B\<^sub>2) = \<Turnstile> b (\<subseteq> A, X) \<Longrightarrow>
      (C, Y) = \<turnstile> c (\<subseteq> B\<^sub>1, X) \<Longrightarrow>
      (B\<^sub>1', B\<^sub>2') = \<Turnstile> b (\<subseteq> C, Y) \<Longrightarrow>
      \<forall>(B, W) \<in> insert (Univ? A X \<union> Univ? C Y, bvars b) U.
        B: sec ` W \<leadsto> UNIV \<Longrightarrow>
      ({}, False) \<Turnstile> c (\<subseteq> B\<^sub>1, X) = Some (B, Z) \<Longrightarrow>
      B\<^sub>1 \<noteq> {} \<Longrightarrow> cgood c \<Longrightarrow> csimp c = c \<Longrightarrow>
      B \<noteq> {};
    \<And>B\<^sub>1 B\<^sub>2 C Y B\<^sub>1' B\<^sub>2' B Z.
      (B\<^sub>1, B\<^sub>2) = \<Turnstile> b (\<subseteq> A, X) \<Longrightarrow>
      (C, Y) = \<turnstile> c (\<subseteq> B\<^sub>1, X) \<Longrightarrow>
      (B\<^sub>1', B\<^sub>2') = \<Turnstile> b (\<subseteq> C, Y) \<Longrightarrow>
      \<forall>(B, W) \<in> insert (Univ? A X \<union> Univ? C Y, bvars b) U.
        B: sec ` W \<leadsto> UNIV \<Longrightarrow>
      ({}, False) \<Turnstile> c (\<subseteq> B\<^sub>1', Y) = Some (B, Z) \<Longrightarrow>
      B\<^sub>1' \<noteq> {} \<Longrightarrow> cgood c \<Longrightarrow> csimp c = c \<Longrightarrow>
      B \<noteq> {};
    (U, v) \<Turnstile> WHILE b DO c (\<subseteq> A, X) = Some (B, Z);
    A \<noteq> {}; cgood (WHILE b DO c);
    csimp (WHILE b DO c) = WHILE b DO c\<rbrakk> \<Longrightarrow>
      B \<noteq> {}"
    by (auto split: option.split_asm prod.split_asm,
     rule csimp_ctyping2_while)
qed (simp_all split: if_split_asm)


theorem correct_secure:
  assumes
    A: "correct c A X" and
    B: "A \<noteq> {}"
  shows "secure c"
proof -
  {
    fix s s' t l and x :: vname
    assume "(c, s) \<Rightarrow> s'"
    then obtain cfs where C: "(c, s) \<rightarrow>*{cfs} (SKIP, s')"
      by (auto dest: small_steps_stepsl simp: big_iff_small)
    assume D: "s = t (\<le> l)"
    have E: "\<forall>x. sec x \<le> l \<longrightarrow> s = t (\<subseteq> sources (flow cfs) s x)"
    proof (rule allI, rule impI)
      fix x :: vname
      assume "sec x \<le> l"
      moreover have "sources (flow cfs) s x \<subseteq> {y. sec y \<le> sec x}"
        by (rule subsetI, simp, rule sources_le)
      ultimately show "s = t (\<subseteq> sources (flow cfs) s x)"
        using D by auto
    qed
    assume "\<forall>s c\<^sub>1 c\<^sub>2 s\<^sub>1 s\<^sub>2 cfs.
      (c, s) \<rightarrow>* (c\<^sub>1, s\<^sub>1) \<and> (c\<^sub>1, s\<^sub>1) \<rightarrow>*{cfs} (c\<^sub>2, s\<^sub>2) \<longrightarrow>
        (\<forall>t\<^sub>1. \<exists>c\<^sub>2' t\<^sub>2. \<forall>x.
          s\<^sub>1 = t\<^sub>1 (\<subseteq> sources (flow cfs) s\<^sub>1 x) \<longrightarrow>
            (c\<^sub>1, t\<^sub>1) \<rightarrow>* (c\<^sub>2', t\<^sub>2) \<and> (c\<^sub>2 = SKIP) = (c\<^sub>2' = SKIP) \<and>
            s\<^sub>2 x = t\<^sub>2 x)"
    note F = this [rule_format]
    obtain t' where G: "\<forall>x.
      s = t (\<subseteq> sources (flow cfs) s x) \<longrightarrow>
        (c, t) \<rightarrow>* (SKIP, t') \<and> s' x = t' x"
      using F [of s c s cfs SKIP s' t] and C by blast
    assume H: "sec x \<le> l"
    {
      have "s = t (\<subseteq> sources (flow cfs) s x)"
        using E and H by simp
      hence "(c, t) \<Rightarrow> t'"
        using G by (simp add: big_iff_small)
    }
    moreover {
      fix x :: vname
      assume "sec x \<le> l"
      hence "s = t (\<subseteq> sources (flow cfs) s x)"
        using E by simp
      hence "s' x = t' x"
        using G by simp
    }
    ultimately have "\<exists>t'. (c, t) \<Rightarrow> t' \<and> s' = t' (\<le> l)"
      by auto
  }
  with A and B show ?thesis
    by (auto simp: correct_def secure_def split: if_split_asm)
qed


lemma ctyping2_sec_type_assign [elim]:
  assumes
    A: "(if ((\<exists>s. s \<in> Univ? A X) \<longrightarrow> (\<forall>y \<in> avars a. sec y \<le> sec x)) \<and>
      (\<forall>p \<in> U. \<forall>B Y. p = (B, Y) \<longrightarrow> B = {} \<or> (\<forall>y \<in> Y. sec y \<le> sec x))
      then Some (if x \<in> {} \<and> A \<noteq> {}
        then if v \<Turnstile> a (\<subseteq> X)
          then ({s(x := aval a s) |s. s \<in> A}, insert x X) else (A, X - {x})
        else (A, Univ?? A X))
      else None) = Some (B, Y)"
      (is "(if (_ \<longrightarrow> ?P) \<and> ?Q then _ else _) = _") and
    B: "s \<in> A" and
    C: "finite (levels U)"
  shows "Max (levels U) \<turnstile> x ::= a"
proof -
  have "?P \<and> ?Q"
    using A and B by (auto simp: univ_states_if_def split: if_split_asm)
  moreover from this have "Max (levels U) \<le> sec x"
    using C by (subst Max_le_iff, auto simp: levels_def, blast)
  ultimately show "Max (levels U) \<turnstile> x ::= a"
    by (auto intro: Assign simp: avars_ub)
qed

lemma ctyping2_sec_type_seq:
  assumes
    A: "\<And>B' s. B = B' \<Longrightarrow> s \<in> A \<Longrightarrow> Max (levels U) \<turnstile> c\<^sub>1" and
    B: "\<And>B' B'' C Z s'. B = B' \<Longrightarrow> B'' = B' \<Longrightarrow>
      (U, v) \<Turnstile> c\<^sub>2 (\<subseteq> B', Y) = Some (C, Z) \<Longrightarrow>
        s' \<in> B' \<Longrightarrow> Max (levels U) \<turnstile> c\<^sub>2" and
    C: "(U, v) \<Turnstile> c\<^sub>1 (\<subseteq> A, X) = Some (B, Y)" and
    D: "(U, v) \<Turnstile> c\<^sub>2 (\<subseteq> B, Y) = Some (C, Z)" and
    E: "s \<in> A" and
    F: "cgood c\<^sub>1" and
    G: "csimp c\<^sub>1 = c\<^sub>1"
  shows "Max (levels U) \<turnstile> c\<^sub>1;; c\<^sub>2"
proof -
  have "Max (levels U) \<turnstile> c\<^sub>1"
    using A and E by simp
  moreover from C and E and F and G have "B \<noteq> {}"
    by (erule_tac csimp_ctyping2, blast)
  hence "Max (levels U) \<turnstile> c\<^sub>2"
    using B and D by blast
  ultimately show ?thesis ..
qed

lemma ctyping2_sec_type_if:
  assumes
    A: "\<And>U' B C s. U' = insert (Univ? A X, bvars b) U \<Longrightarrow>
      B = B\<^sub>1 \<Longrightarrow> C\<^sub>1 = C \<Longrightarrow> s \<in> B\<^sub>1 \<Longrightarrow>
        finite (levels (insert (Univ? A X, bvars b) U)) \<Longrightarrow>
          Max (levels (insert (Univ? A X, bvars b) U)) \<turnstile> c\<^sub>1"
      (is "\<And>_ _ _ _. _ = ?U' \<Longrightarrow> _ \<Longrightarrow> _ \<Longrightarrow> _ \<Longrightarrow> _ \<Longrightarrow> _")
  assumes
    B: "\<And>U' B C s. U' = ?U' \<Longrightarrow> B = B\<^sub>1 \<Longrightarrow> C\<^sub>2 = C \<Longrightarrow> s \<in> B\<^sub>2 \<Longrightarrow>
      finite (levels ?U') \<Longrightarrow> Max (levels ?U') \<turnstile> c\<^sub>2" and
    C: "\<Turnstile> b (\<subseteq> A, X) = (B\<^sub>1, B\<^sub>2)" and
    D: "s \<in> A" and
    E: "bsimp b = b" and
    F: "\<forall>v. b \<noteq> Bc v" and
    G: "finite (levels U)"
  shows "Max (levels U) \<turnstile> IF b THEN c\<^sub>1 ELSE c\<^sub>2"
proof -
  from D and G have H: "finite (levels ?U') \<and>
    Max (levels ?U') = max (sec b) (Max (levels U))"
    using levels_insert by (auto simp: univ_states_if_def)
  moreover have I: "\<Turnstile> b (\<subseteq> A, X) = (A, A)"
    using E and F by (rule bsimp_btyping2)
  hence "Max (levels ?U') \<turnstile> c\<^sub>1"
    using A and C and D and H by auto
  moreover have "Max (levels ?U') \<turnstile> c\<^sub>2"
    using B and C and D and H and I by auto
  ultimately show ?thesis
    by (auto intro: If)
qed

lemma ctyping2_sec_type_while:
  assumes
    A: "\<And>B C' B' D' s. B = B\<^sub>1 \<Longrightarrow> C' = C \<Longrightarrow> B' = B\<^sub>1' \<Longrightarrow>
      ((\<exists>s. s \<in> Univ? A X \<or> s \<in> Univ? C Y) \<longrightarrow>
        (\<forall>x \<in> bvars b. All ((\<le>) (sec x)))) \<and>
      (\<forall>p \<in> U. case p of (B, W) \<Rightarrow> (\<exists>s. s \<in> B) \<longrightarrow>
        (\<forall>x \<in> W. All ((\<le>) (sec x)))) \<Longrightarrow>
        D = D' \<Longrightarrow> s \<in> B\<^sub>1 \<Longrightarrow> finite (levels {}) \<Longrightarrow> Max (levels {}) \<turnstile> c"
      (is "\<And>_ _ _ _ _. _ \<Longrightarrow> _ \<Longrightarrow> _ \<Longrightarrow>
        ?P \<and> (\<forall>p \<in> _. case p of (_, W) \<Rightarrow> _ \<longrightarrow> ?Q W) \<Longrightarrow>
          _ \<Longrightarrow> _ \<Longrightarrow> _ \<Longrightarrow> _")
  assumes
    B: "(if ?P \<and> (\<forall>p \<in> U. \<forall>B W. p = (B, W) \<longrightarrow> B = {} \<or> ?Q W)
      then Some (B\<^sub>2 \<union> B\<^sub>2', Univ?? B\<^sub>2 X \<inter> Y) else None) = Some (B, Z)"
      (is "(if ?R then _ else _) = _") and
    C: "\<Turnstile> b (\<subseteq> A, X) = (B\<^sub>1, B\<^sub>2)" and
    D: "s \<in> A" and
    E: "bsimp b = b" and
    F: "b \<noteq> Bc False" and
    G: "b \<noteq> Bc True" and
    H: "finite (levels U)"
  shows "Max (levels U) \<turnstile> WHILE b DO c"
proof -
  have ?R
    using B by (simp split: if_split_asm)
  hence "sec b \<le> 0"
    using D by (subst bvars_ub, auto simp: univ_states_if_def, fastforce)
  moreover have "\<Turnstile> b (\<subseteq> A, X) = (A, A)"
    using E and F and G by (blast intro: bsimp_btyping2)
  hence "0 \<turnstile> c"
    using A and C and D and `?R` by (fastforce simp: levels_def)
  moreover have "Max (levels U) = 0"
  proof (rule Max_eqI [OF H])
    fix l
    assume "l \<in> levels U"
    thus "l \<le> 0"
      using `?R` by (fastforce simp: levels_def)
  next
    show "0 \<in> levels U"
      by (simp add: levels_def)
  qed
  ultimately show ?thesis
    by (auto intro: While)
qed


theorem ctyping2_sec_type:
 "\<lbrakk>(U, v) \<Turnstile> c (\<subseteq> A, X) = Some (B, Y);
    s \<in> A; cgood c; csimp c = c; finite (levels U)\<rbrakk> \<Longrightarrow>
  Max (levels U) \<turnstile> c"
proof (induction "(U, v)" c A X arbitrary: B Y U v s rule: ctyping2.induct)
  fix U
  show "Max (levels U) \<turnstile> SKIP"
    by (rule Skip)
next
  fix A X C Z U v c\<^sub>1 c\<^sub>2 s
  show
   "\<lbrakk>\<And>B Y s. (U, v) \<Turnstile> c\<^sub>1 (\<subseteq> A, X) = Some (B, Y) \<Longrightarrow>
      s \<in> A \<Longrightarrow> cgood c\<^sub>1 \<Longrightarrow> csimp c\<^sub>1 = c\<^sub>1 \<Longrightarrow> finite (levels U) \<Longrightarrow>
      Max (levels U) \<turnstile> c\<^sub>1;
    \<And>p B Y C Z s. (U, v) \<Turnstile> c\<^sub>1 (\<subseteq> A, X) = Some p \<Longrightarrow>
      (B, Y) = p \<Longrightarrow> (U, v) \<Turnstile> c\<^sub>2 (\<subseteq> B, Y) = Some (C, Z) \<Longrightarrow>
      s \<in> B \<Longrightarrow> cgood c\<^sub>2 \<Longrightarrow> csimp c\<^sub>2 = c\<^sub>2 \<Longrightarrow> finite (levels U) \<Longrightarrow>
      Max (levels U) \<turnstile> c\<^sub>2;
    (U, v) \<Turnstile> c\<^sub>1;; c\<^sub>2 (\<subseteq> A, X) = Some (C, Z);
    s \<in> A; cgood (c\<^sub>1;; c\<^sub>2);
    csimp (c\<^sub>1;; c\<^sub>2) = c\<^sub>1;; c\<^sub>2;
    finite (levels U)\<rbrakk> \<Longrightarrow>
      Max (levels U) \<turnstile> c\<^sub>1;; c\<^sub>2"
    by (auto split: option.split_asm, rule ctyping2_sec_type_seq)
next
  fix A X B Y U v b c\<^sub>1 c\<^sub>2 s
  show
   "\<lbrakk>\<And>U' p B\<^sub>1 B\<^sub>2 C Y s.
      (U', p) = (insert (Univ? A X, bvars b) U, \<Turnstile> b (\<subseteq> A, X)) \<Longrightarrow>
      (B\<^sub>1, B\<^sub>2) = p \<Longrightarrow> (U', v) \<Turnstile> c\<^sub>1 (\<subseteq> B\<^sub>1, X) = Some (C, Y) \<Longrightarrow>
      s \<in> B\<^sub>1 \<Longrightarrow> cgood c\<^sub>1 \<Longrightarrow> csimp c\<^sub>1 = c\<^sub>1 \<Longrightarrow> finite (levels U') \<Longrightarrow>
      Max (levels U') \<turnstile> c\<^sub>1;
    \<And>U' p B\<^sub>1 B\<^sub>2 C Y s.
      (U', p) = (insert (Univ? A X, bvars b) U, \<Turnstile> b (\<subseteq> A, X)) \<Longrightarrow>
      (B\<^sub>1, B\<^sub>2) = p \<Longrightarrow> (U', v) \<Turnstile> c\<^sub>2 (\<subseteq> B\<^sub>2, X) = Some (C, Y) \<Longrightarrow>
      s \<in> B\<^sub>2 \<Longrightarrow> cgood c\<^sub>2 \<Longrightarrow> csimp c\<^sub>2 = c\<^sub>2 \<Longrightarrow> finite (levels U') \<Longrightarrow>
      Max (levels U') \<turnstile> c\<^sub>2;
    (U, v) \<Turnstile> IF b THEN c\<^sub>1 ELSE c\<^sub>2 (\<subseteq> A, X) = Some (B, Y);
    s \<in> A; cgood (IF b THEN c\<^sub>1 ELSE c\<^sub>2);
    csimp (IF b THEN c\<^sub>1 ELSE c\<^sub>2) = IF b THEN c\<^sub>1 ELSE c\<^sub>2;
    finite (levels U)\<rbrakk> \<Longrightarrow>
      Max (levels U) \<turnstile> IF b THEN c\<^sub>1 ELSE c\<^sub>2"
    by (auto split: option.split_asm prod.split_asm,
     rule ctyping2_sec_type_if)
next
  fix A X B Z U v b c s
  show
   "\<lbrakk>\<And>B\<^sub>1 B\<^sub>2 C Y B\<^sub>1' B\<^sub>2' D Z s.
      (B\<^sub>1, B\<^sub>2) = \<Turnstile> b (\<subseteq> A, X) \<Longrightarrow>
      (C, Y) = \<turnstile> c (\<subseteq> B\<^sub>1, X) \<Longrightarrow>
      (B\<^sub>1', B\<^sub>2') = \<Turnstile> b (\<subseteq> C, Y) \<Longrightarrow>
      \<forall>(B, W) \<in> insert (Univ? A X \<union> Univ? C Y, bvars b) U.
        B: sec ` W \<leadsto> UNIV \<Longrightarrow>
      ({}, False) \<Turnstile> c (\<subseteq> B\<^sub>1, X) = Some (D, Z) \<Longrightarrow>
      s \<in> B\<^sub>1 \<Longrightarrow> cgood c \<Longrightarrow> csimp c = c \<Longrightarrow> finite (levels {}) \<Longrightarrow>
      Max (levels {}) \<turnstile> c;
    \<And>B\<^sub>1 B\<^sub>2 C Y B\<^sub>1' B\<^sub>2' D' Z' s.
      (B\<^sub>1, B\<^sub>2) = \<Turnstile> b (\<subseteq> A, X) \<Longrightarrow>
      (C, Y) = \<turnstile> c (\<subseteq> B\<^sub>1, X) \<Longrightarrow>
      (B\<^sub>1', B\<^sub>2') = \<Turnstile> b (\<subseteq> C, Y) \<Longrightarrow>
      \<forall>(B, W) \<in> insert (Univ? A X \<union> Univ? C Y, bvars b) U.
        B: sec ` W \<leadsto> UNIV \<Longrightarrow>
      ({}, False) \<Turnstile> c (\<subseteq> B\<^sub>1', Y) = Some (D', Z') \<Longrightarrow>
      s \<in> B\<^sub>1' \<Longrightarrow> cgood c \<Longrightarrow> csimp c = c \<Longrightarrow> finite (levels {}) \<Longrightarrow>
      Max (levels {}) \<turnstile> c;
    (U, v) \<Turnstile> WHILE b DO c (\<subseteq> A, X) = Some (B, Z);
    s \<in> A; cgood (WHILE b DO c);
    csimp (WHILE b DO c) = WHILE b DO c;
    finite (levels U)\<rbrakk> \<Longrightarrow>
      Max (levels U) \<turnstile> WHILE b DO c"
    by (auto split: option.split_asm prod.split_asm,
     rule ctyping2_sec_type_while)
qed (auto split: prod.split_asm)


lemma sec_type_ctyping2_if:
  assumes
    A: "\<And>U' B\<^sub>1 B\<^sub>2. U' = insert (Univ? A X, bvars b) U \<Longrightarrow>
      (B\<^sub>1, B\<^sub>2) = \<Turnstile> b (\<subseteq> A, X) \<Longrightarrow>
        Max (levels (insert (Univ? A X, bvars b) U)) \<turnstile> c\<^sub>1 \<Longrightarrow>
          finite (levels (insert (Univ? A X, bvars b) U)) \<Longrightarrow>
      \<exists>C Y. (insert (Univ? A X, bvars b) U, v) \<Turnstile> c\<^sub>1 (\<subseteq> B\<^sub>1, X) =
        Some (C, Y)"
      (is "\<And>_ _ _. _ = ?U' \<Longrightarrow> _ \<Longrightarrow> _ \<Longrightarrow> _ \<Longrightarrow> _")
  assumes
    B: "\<And>U' B\<^sub>1 B\<^sub>2. U' = ?U' \<Longrightarrow> (B\<^sub>1, B\<^sub>2) = \<Turnstile> b (\<subseteq> A, X) \<Longrightarrow>
      Max (levels ?U') \<turnstile> c\<^sub>2 \<Longrightarrow> finite (levels ?U') \<Longrightarrow>
        \<exists>C Y. (?U', v) \<Turnstile> c\<^sub>2 (\<subseteq> B\<^sub>2, X) = Some (C, Y)" and
    C: "finite (levels U)" and
    D: "max (sec b) (Max (levels U)) \<turnstile> c\<^sub>1" and
    E: "max (sec b) (Max (levels U)) \<turnstile> c\<^sub>2"
  shows "\<exists>C Y. (U, v) \<Turnstile> IF b THEN c\<^sub>1 ELSE c\<^sub>2 (\<subseteq> A, X) = Some (C, Y)"
proof -
  obtain B\<^sub>1 B\<^sub>2 where F: "(B\<^sub>1, B\<^sub>2) = \<Turnstile> b (\<subseteq> A, X)"
    by (cases "\<Turnstile> b (\<subseteq> A, X)", simp)
  moreover have "\<exists>C\<^sub>1 C\<^sub>2 Y\<^sub>1 Y\<^sub>2. (?U', v) \<Turnstile> c\<^sub>1 (\<subseteq> B\<^sub>1, X) = Some (C\<^sub>1, Y\<^sub>1) \<and>
    (?U', v) \<Turnstile> c\<^sub>2 (\<subseteq> B\<^sub>2, X) = Some (C\<^sub>2, Y\<^sub>2)"
  proof (cases "A = {}")
    case True
    hence "levels ?U' = levels U"
      by (auto simp: levels_def univ_states_if_def)
    moreover have "Max (levels U) \<turnstile> c\<^sub>1"
      using D by (auto intro: anti_mono)
    moreover have "Max (levels U) \<turnstile> c\<^sub>2"
      using E by (auto intro: anti_mono)
    ultimately show ?thesis
      using A and B and C and F by simp
  next
    case False
    with C have "finite (levels ?U') \<and>
      Max (levels ?U') = max (sec b) (Max (levels U))"
      by (simp add: levels_insert univ_states_if_def)
    thus ?thesis
      using A and B and D and E and F by simp
  qed
  ultimately show ?thesis
    by (auto split: prod.split)
qed

lemma sec_type_ctyping2_while:
  assumes
    A: "\<And>B\<^sub>1 B\<^sub>2 C Y B\<^sub>1' B\<^sub>2'. (B\<^sub>1, B\<^sub>2) = \<Turnstile> b (\<subseteq> A, X) \<Longrightarrow>
      (C, Y) = \<turnstile> c (\<subseteq> B\<^sub>1, X) \<Longrightarrow> (B\<^sub>1', B\<^sub>2') = \<Turnstile> b (\<subseteq> C, Y) \<Longrightarrow>
        ((\<exists>s. s \<in> Univ? A X \<or> s \<in> Univ? C Y) \<longrightarrow>
          (\<forall>x \<in> bvars b. All ((\<le>) (sec x)))) \<and>
        (\<forall>p \<in> U. case p of (B, W) \<Rightarrow> (\<exists>s. s \<in> B) \<longrightarrow>
          (\<forall>x \<in> W. All ((\<le>) (sec x)))) \<Longrightarrow>
        Max (levels {}) \<turnstile> c \<Longrightarrow> finite (levels {}) \<Longrightarrow>
          \<exists>D Z. ({}, False) \<Turnstile> c (\<subseteq> B\<^sub>1, X) = Some (D, Z)"
      (is "\<And>_ _ C Y _ _. _ \<Longrightarrow> _ \<Longrightarrow> _ \<Longrightarrow> ?P C Y \<Longrightarrow> _ \<Longrightarrow> _ \<Longrightarrow> _")
  assumes
    B: "\<And>B\<^sub>1 B\<^sub>2 C Y B\<^sub>1' B\<^sub>2'. (B\<^sub>1, B\<^sub>2) = \<Turnstile> b (\<subseteq> A, X) \<Longrightarrow>
      (C, Y) = \<turnstile> c (\<subseteq> B\<^sub>1, X) \<Longrightarrow> (B\<^sub>1', B\<^sub>2') = \<Turnstile> b (\<subseteq> C, Y) \<Longrightarrow>
        ?P C Y \<Longrightarrow> Max (levels {}) \<turnstile> c \<Longrightarrow> finite (levels {}) \<Longrightarrow>
          \<exists>D Z. ({}, False) \<Turnstile> c (\<subseteq> B\<^sub>1', Y) = Some (D, Z)" and
    C: "finite (levels U)" and
    D: "Max (levels U) = 0" and
    E: "sec b = 0" and
    F: "0 \<turnstile> c"
  shows "\<exists>B Y. (U, v) \<Turnstile> WHILE b DO c (\<subseteq> A, X) = Some (B, Y)"
proof -
  obtain B\<^sub>1 B\<^sub>2 where G: "(B\<^sub>1, B\<^sub>2) = \<Turnstile> b (\<subseteq> A, X)"
    by (cases "\<Turnstile> b (\<subseteq> A, X)", simp)
  moreover obtain C Y where H: "(C, Y) = \<turnstile> c (\<subseteq> B\<^sub>1, X)"
    by (cases "\<turnstile> c (\<subseteq> B\<^sub>1, X)", simp)
  moreover obtain B\<^sub>1' B\<^sub>2' where I: "(B\<^sub>1', B\<^sub>2') = \<Turnstile> b (\<subseteq> C, Y)"
    by (cases "\<Turnstile> b (\<subseteq> C, Y)", simp)
  moreover {
    fix l x s B W
    assume J: "(B, W) \<in> U" and K: "x \<in> W" and L: "s \<in> B"
    have "sec x \<le> l"
    proof (rule le_trans, rule Max_ge [OF C])
      show "sec x \<in> levels U"
        using J and K and L by (fastforce simp: levels_def)
    next
      show "Max (levels U) \<le> l"
        using D by simp
    qed
  }
  hence J: "?P C Y"
    using E by (auto dest: bvars_sec)
  ultimately have "\<exists>D D' Z Z'. ({}, False) \<Turnstile> c (\<subseteq> B\<^sub>1, X) = Some (D, Z) \<and>
    ({}, False) \<Turnstile> c (\<subseteq> B\<^sub>1', Y) = Some (D', Z')"
    using A and B and F by (force simp: levels_def)
  thus ?thesis
    using G and H and I and J by (auto split: prod.split)
qed


theorem sec_type_ctyping2:
 "\<lbrakk>Max (levels U) \<turnstile> c; finite (levels U)\<rbrakk> \<Longrightarrow>
    \<exists>B Y. (U, v) \<Turnstile> c (\<subseteq> A, X) = Some (B, Y)"
proof (induction "(U, v)" c A X arbitrary: U v rule: ctyping2.induct)
  fix A X U v x a
  show "Max (levels U) \<turnstile> x ::= a \<Longrightarrow> finite (levels U) \<Longrightarrow>
    \<exists>B Y. (U, v) \<Turnstile> x ::= a (\<subseteq> A, X) = Some (B, Y)"
    by (fastforce dest: avars_sec simp: levels_def)
next
  fix A X U v b c\<^sub>1 c\<^sub>2
  show
   "\<lbrakk>\<And>U' p B\<^sub>1 B\<^sub>2.
      (U', p) = (insert (Univ? A X, bvars b) U, \<Turnstile> b (\<subseteq> A, X)) \<Longrightarrow>
      (B\<^sub>1, B\<^sub>2) = p \<Longrightarrow> Max (levels U') \<turnstile> c\<^sub>1 \<Longrightarrow> finite (levels U') \<Longrightarrow>
      \<exists>B Y. (U', v) \<Turnstile> c\<^sub>1 (\<subseteq> B\<^sub>1, X) = Some (B, Y);
    \<And>U' p B\<^sub>1 B\<^sub>2.
      (U', p) = (insert (Univ? A X, bvars b) U, \<Turnstile> b (\<subseteq> A, X)) \<Longrightarrow>
      (B\<^sub>1, B\<^sub>2) = p \<Longrightarrow> Max (levels U') \<turnstile> c\<^sub>2 \<Longrightarrow> finite (levels U') \<Longrightarrow>
      \<exists>B Y. (U', v) \<Turnstile> c\<^sub>2 (\<subseteq> B\<^sub>2, X) = Some (B, Y);
    Max (levels U) \<turnstile> IF b THEN c\<^sub>1 ELSE c\<^sub>2; finite (levels U)\<rbrakk> \<Longrightarrow>
      \<exists>B Y. (U, v) \<Turnstile> IF b THEN c\<^sub>1 ELSE c\<^sub>2 (\<subseteq> A, X) = Some (B, Y)"
    by (auto simp del: ctyping2.simps(4), rule sec_type_ctyping2_if)
next
  fix A X U v b c
  show
   "\<lbrakk>\<And>B\<^sub>1 B\<^sub>2 C Y B\<^sub>1' B\<^sub>2'.
      (B\<^sub>1, B\<^sub>2) = \<Turnstile> b (\<subseteq> A, X) \<Longrightarrow>
      (C, Y) = \<turnstile> c (\<subseteq> B\<^sub>1, X) \<Longrightarrow>
      (B\<^sub>1', B\<^sub>2') = \<Turnstile> b (\<subseteq> C, Y) \<Longrightarrow>
      \<forall>(B, W) \<in> insert (Univ? A X \<union> Univ? C Y, bvars b) U.
        B: sec ` W \<leadsto> UNIV \<Longrightarrow>
      Max (levels {}) \<turnstile> c \<Longrightarrow> finite (levels {}) \<Longrightarrow>
      \<exists>B Z. ({}, False) \<Turnstile> c (\<subseteq> B\<^sub>1, X) = Some (B, Z);
    \<And>B\<^sub>1 B\<^sub>2 C Y B\<^sub>1' B\<^sub>2'.
      (B\<^sub>1, B\<^sub>2) = \<Turnstile> b (\<subseteq> A, X) \<Longrightarrow>
      (C, Y) = \<turnstile> c (\<subseteq> B\<^sub>1, X) \<Longrightarrow>
      (B\<^sub>1', B\<^sub>2') = \<Turnstile> b (\<subseteq> C, Y) \<Longrightarrow>
      \<forall>(B, W) \<in> insert (Univ? A X \<union> Univ? C Y, bvars b) U.
        B: sec ` W \<leadsto> UNIV \<Longrightarrow>
      Max (levels {}) \<turnstile> c \<Longrightarrow> finite (levels {}) \<Longrightarrow>
      \<exists>B Z. ({}, False) \<Turnstile> c (\<subseteq> B\<^sub>1', Y) = Some (B, Z);
    Max (levels U) \<turnstile> WHILE b DO c; finite (levels U)\<rbrakk> \<Longrightarrow>
      \<exists>B Z. (U, v) \<Turnstile> WHILE b DO c (\<subseteq> A, X) = Some (B, Z)"
    by (auto simp del: ctyping2.simps(5), rule sec_type_ctyping2_while)
qed auto

end

end
