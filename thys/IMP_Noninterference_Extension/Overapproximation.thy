(*  Title:       Extension of Stateful Intransitive Noninterference with Inputs, Outputs, and Nondeterminism in Language IMP
    Author:      Pasquale Noce
                 Senior Staff Firmware Engineer at HID Global, Italy
                 pasquale dot noce dot lavoro at gmail dot com
                 pasquale dot noce at hidglobal dot com
*)

section "Overapproximation of program semantics by the main type system"

theory Overapproximation
  imports Idempotence
begin

text \<open>
\null

As in my previous paper \<^cite>\<open>"Noce24"\<close>, the purpose of this section is to prove that type system
@{const [names_short] noninterf.ctyping2} overapproximates program semantics, namely that if (a)
@{prop "(c, s, p) \<Rightarrow> (t, q)"}, (b) the type system outputs a @{typ "state set"} @{term B} and a
@{typ "vname set"} @{term Y} when it is input program @{term c}, @{typ "state set"} @{term A}, and
@{typ "vname set"} @{term X}, and (c) state @{term s} agrees with some state in @{term A} on the
value of each state variable in @{term X}, then @{term t} must agree with some state in @{term B} on
the value of each state variable in @{term Y} (lemma @{text ctyping2_approx}).

This proof makes use of the lemma @{text ctyping1_idem} proven in the previous section.
\<close>


subsection "Global context proofs"

lemma avars_aval:
 "s = t (\<subseteq> avars a) \<Longrightarrow> aval a s = aval a t"
by (induction a, simp_all)


subsection "Local context proofs"

context noninterf
begin


lemma interf_set_mono:
 "\<lbrakk>A' \<subseteq> A; X \<subseteq> X'; \<forall>(B', Y') \<in> U'. \<exists>(B, Y) \<in> U. B' \<subseteq> B \<and> Y' \<subseteq> Y;
    \<forall>(B, Y) \<in> insert (Univ? A X, Z) U. B: Y \<leadsto> W\<rbrakk> \<Longrightarrow>
  \<forall>(B, Y) \<in> insert (Univ? A' X', Z) U'. B: Y \<leadsto> W"
by (subgoal_tac "Univ? A' X' \<subseteq> Univ? A X", fastforce,
 auto simp: univ_states_if_def)


lemma btyping1_btyping2_aux_1 [elim]:
  assumes
    A: "avars a\<^sub>1 = {}" and
    B: "avars a\<^sub>2 = {}" and
    C: "aval a\<^sub>1 (\<lambda>x. 0) < aval a\<^sub>2 (\<lambda>x. 0)"
  shows "aval a\<^sub>1 s < aval a\<^sub>2 s"
proof -
  have "aval a\<^sub>1 s = aval a\<^sub>1 (\<lambda>x. 0) \<and> aval a\<^sub>2 s = aval a\<^sub>2 (\<lambda>x. 0)"
    using A and B by (blast intro: avars_aval)
  thus ?thesis
    using C by simp
qed

lemma btyping1_btyping2_aux_2 [elim]:
  assumes
    A: "avars a\<^sub>1 = {}" and
    B: "avars a\<^sub>2 = {}" and
    C: "\<not> aval a\<^sub>1 (\<lambda>x. 0) < aval a\<^sub>2 (\<lambda>x. 0)" and
    D: "aval a\<^sub>1 s < aval a\<^sub>2 s"
  shows False
proof -
  have "aval a\<^sub>1 s = aval a\<^sub>1 (\<lambda>x. 0) \<and> aval a\<^sub>2 s = aval a\<^sub>2 (\<lambda>x. 0)"
    using A and B by (blast intro: avars_aval)
  thus ?thesis
    using C and D by simp
qed

lemma btyping1_btyping2_aux:
 "\<turnstile> b = Some v \<Longrightarrow> \<TTurnstile> b (\<subseteq> A, X) = Some (if v then A else {})"
by (induction b arbitrary: v, auto split: if_split_asm option.split_asm)

lemma btyping1_btyping2:
 "\<turnstile> b = Some v \<Longrightarrow> \<Turnstile> b (\<subseteq> A, X) = (if v then (A, {}) else ({}, A))"
by (simp add: btyping2_def btyping1_btyping2_aux)

lemma btyping2_aux_subset:
 "\<TTurnstile> b (\<subseteq> A, X) = Some A' \<Longrightarrow> A' = {s. s \<in> A \<and> bval b s}"
by (induction b arbitrary: A', auto split: if_split_asm option.split_asm)

lemma btyping2_aux_diff:
 "\<lbrakk>\<TTurnstile> b (\<subseteq> A, X) = Some B; \<TTurnstile> b (\<subseteq> A', X') = Some B'; A' \<subseteq> A; B' \<subseteq> B\<rbrakk> \<Longrightarrow>
    A' - B' \<subseteq> A - B"
by (blast dest: btyping2_aux_subset)

lemma btyping2_aux_mono:
 "\<lbrakk>\<TTurnstile> b (\<subseteq> A, X) = Some B; A' \<subseteq> A; X \<subseteq> X'\<rbrakk> \<Longrightarrow>
    \<exists>B'. \<TTurnstile> b (\<subseteq> A', X') = Some B' \<and> B' \<subseteq> B"
by (induction b arbitrary: B, auto dest: btyping2_aux_diff split:
 if_split_asm option.split_asm)

lemma btyping2_mono:
 "\<lbrakk>\<Turnstile> b (\<subseteq> A, X) = (B\<^sub>1, B\<^sub>2); \<Turnstile> b (\<subseteq> A', X') = (B\<^sub>1', B\<^sub>2'); A' \<subseteq> A; X \<subseteq> X'\<rbrakk> \<Longrightarrow>
    B\<^sub>1' \<subseteq> B\<^sub>1 \<and> B\<^sub>2' \<subseteq> B\<^sub>2"
by (simp add: btyping2_def split: option.split_asm,
 frule_tac [3-4] btyping2_aux_mono, auto dest: btyping2_aux_subset)

lemma btyping2_un_eq:
 "\<Turnstile> b (\<subseteq> A, X) = (B\<^sub>1, B\<^sub>2) \<Longrightarrow> B\<^sub>1 \<union> B\<^sub>2 = A"
by (auto simp: btyping2_def dest: btyping2_aux_subset split: option.split_asm)

lemma btyping2_aux_eq:
 "\<lbrakk>\<TTurnstile> b (\<subseteq> A, X) = Some A'; s = t (\<subseteq> state \<inter> X)\<rbrakk> \<Longrightarrow> bval b s = bval b t"
proof (induction b arbitrary: A')
  fix A' v
  show
   "\<lbrakk>\<TTurnstile> Bc v (\<subseteq> A, X) = Some A'; s = t (\<subseteq> state \<inter> X)\<rbrakk> \<Longrightarrow>
      bval (Bc v) s = bval (Bc v) t"
    by simp
next
  fix A' b
  show
   "\<lbrakk>\<And>A'. \<TTurnstile> b (\<subseteq> A, X) = Some A' \<Longrightarrow> s = t (\<subseteq> state \<inter> X) \<Longrightarrow>
      bval b s = bval b t;
    \<TTurnstile> Not b (\<subseteq> A, X) = Some A'; s = t (\<subseteq> state \<inter> X)\<rbrakk> \<Longrightarrow>
      bval (Not b) s = bval (Not b) t"
    by (simp split: option.split_asm)
next
  fix A' b\<^sub>1 b\<^sub>2
  show
   "\<lbrakk>\<And>A'. \<TTurnstile> b\<^sub>1 (\<subseteq> A, X) = Some A' \<Longrightarrow> s = t (\<subseteq> state \<inter> X) \<Longrightarrow>
      bval b\<^sub>1 s = bval b\<^sub>1 t;
    \<And>A'. \<TTurnstile> b\<^sub>2 (\<subseteq> A, X) = Some A' \<Longrightarrow> s = t (\<subseteq> state \<inter> X) \<Longrightarrow>
      bval b\<^sub>2 s = bval b\<^sub>2 t;
    \<TTurnstile> And b\<^sub>1 b\<^sub>2 (\<subseteq> A, X) = Some A'; s = t (\<subseteq> state \<inter> X)\<rbrakk> \<Longrightarrow>
      bval (And b\<^sub>1 b\<^sub>2) s = bval (And b\<^sub>1 b\<^sub>2) t"
    by (simp split: option.split_asm)
next
  fix A' a\<^sub>1 a\<^sub>2
  show
   "\<lbrakk>\<TTurnstile> Less a\<^sub>1 a\<^sub>2 (\<subseteq> A, X) = Some A'; s = t (\<subseteq> state \<inter> X)\<rbrakk> \<Longrightarrow>
      bval (Less a\<^sub>1 a\<^sub>2) s = bval (Less a\<^sub>1 a\<^sub>2) t"
    by (subgoal_tac "aval a\<^sub>1 s = aval a\<^sub>1 t",
     subgoal_tac "aval a\<^sub>2 s = aval a\<^sub>2 t",
     auto intro!: avars_aval split: if_split_asm)
qed


lemma ctyping1_mono_fst:
 "\<lbrakk>\<turnstile> c (\<subseteq> A, X) = (B, Y); \<turnstile> c (\<subseteq> A', X') = (B', Y'); A' \<subseteq> A\<rbrakk> \<Longrightarrow>
    B' \<subseteq> B"
by (fastforce simp: ctyping1_def)

lemma ctyping1_mono:
  assumes
    A: "\<turnstile> c (\<subseteq> A, X) = (B, Y)" and
    B: "\<turnstile> c (\<subseteq> A', X') = (B', Y')" and
    C: "A' \<subseteq> A" and
    D: "X \<subseteq> X'"
  shows "B' \<subseteq> B \<and> Y \<subseteq> Y'"
proof (rule conjI, rule ctyping1_mono_fst [OF A B C])
  {
    fix x
    assume "x \<notin> Univ?? A' {x. \<forall>f \<in> {\<lambda>x. [y\<leftarrow>ys. fst y = x] | ys. ys \<in> \<turnstile> c}.
      if f x = [] then x \<in> X' else snd (last (f x)) \<noteq> None}"
    moreover from this have "A' \<noteq> {}"
      by (simp split: if_split_asm)
    ultimately have "\<not> (\<forall>f.
      (\<exists>ys. f = (\<lambda>x. [y\<leftarrow>ys. fst y = x]) \<and> ys \<in> \<turnstile> c) \<longrightarrow>
        (if f x = [] then x \<in> X' else snd (last (f x)) \<noteq> None))"
      (is "\<not> ?P X'")
      by (auto split: if_split_asm)
    moreover assume "?P X"
    hence "?P X'"
      using D by fastforce
    ultimately have False
      by contradiction
  }
  with A and B and C show "Y \<subseteq> Y'"
    by (cases "A = {}", auto simp: ctyping1_def)
qed


lemma ctyping2_mono_skip [elim!]:
 "\<lbrakk>(U, False) \<Turnstile> SKIP (\<subseteq> A, X) = Some (C, Z); A' \<subseteq> A; X \<subseteq> X'\<rbrakk> \<Longrightarrow>
    \<exists>C' Z'. (U', False) \<Turnstile> SKIP (\<subseteq> A', X') = Some (C', Z') \<and>
      C' \<subseteq> C \<and> Z \<subseteq> Z'"
by (clarsimp, subgoal_tac "Univ?? C X = X", force+)

lemma ctyping2_mono_assign [elim!]:
 "\<lbrakk>(U, False) \<Turnstile> x ::= a (\<subseteq> A, X) = Some (C, Z); A' \<subseteq> A; X \<subseteq> X';
    \<forall>(B', Y') \<in> U'. \<exists>(B, Y) \<in> U. B' \<subseteq> B \<and> Y' \<subseteq> Y\<rbrakk> \<Longrightarrow>
  \<exists>C' Z'. (U', False) \<Turnstile> x ::= a (\<subseteq> A', X') = Some (C', Z') \<and>
    C' \<subseteq> C \<and> Z \<subseteq> Z'"
by (frule interf_set_mono [where W = "{x}"], auto split: if_split_asm)

lemma ctyping2_mono_input [elim!]:
 "\<lbrakk>(U, False) \<Turnstile> IN x (\<subseteq> A, X) = Some (C, Z); A' \<subseteq> A; X \<subseteq> X';
    \<forall>(B', Y') \<in> U'. \<exists>(B, Y) \<in> U. B' \<subseteq> B \<and> Y' \<subseteq> Y\<rbrakk> \<Longrightarrow>
  \<exists>C' Z'. (U', False) \<Turnstile> IN x (\<subseteq> A', X') = Some (C', Z') \<and>
    C' \<subseteq> C \<and> Z \<subseteq> Z'"
by (frule interf_set_mono [where W = "{x}"], auto split: if_split_asm)

lemma ctyping2_mono_output [elim!]:
 "\<lbrakk>(U, False) \<Turnstile> OUT x (\<subseteq> A, X) = Some (C, Z); A' \<subseteq> A; X \<subseteq> X';
    \<forall>(B', Y') \<in> U'. \<exists>(B, Y) \<in> U. B' \<subseteq> B \<and> Y' \<subseteq> Y\<rbrakk> \<Longrightarrow>
  \<exists>C' Z'. (U', False) \<Turnstile> OUT x (\<subseteq> A', X') = Some (C', Z') \<and>
    C' \<subseteq> C \<and> Z \<subseteq> Z'"
by (frule interf_set_mono [where W = "{x}"], auto split: if_split_asm)

lemma ctyping2_mono_seq:
  assumes
    A: "\<And>A' B X' Y U'.
      (U, False) \<Turnstile> c\<^sub>1 (\<subseteq> A, X) = Some (B, Y) \<Longrightarrow> A' \<subseteq> A \<Longrightarrow> X \<subseteq> X' \<Longrightarrow>
        \<forall>(B', Y') \<in> U'. \<exists>(B, Y) \<in> U. B' \<subseteq> B \<and> Y' \<subseteq> Y \<Longrightarrow>
          \<exists>B' Y'. (U', False) \<Turnstile> c\<^sub>1 (\<subseteq> A', X') = Some (B', Y') \<and>
            B' \<subseteq> B \<and> Y \<subseteq> Y'" and
    B: "\<And>p B Y B' C Y' Z U'.
      (U, False) \<Turnstile> c\<^sub>1 (\<subseteq> A, X) = Some p \<Longrightarrow> (B, Y) = p \<Longrightarrow>
        (U, False) \<Turnstile> c\<^sub>2 (\<subseteq> B, Y) = Some (C, Z) \<Longrightarrow> B' \<subseteq> B \<Longrightarrow> Y \<subseteq> Y' \<Longrightarrow>
          \<forall>(B', Y') \<in> U'. \<exists>(B, Y) \<in> U. B' \<subseteq> B \<and> Y' \<subseteq> Y \<Longrightarrow>
            \<exists>C' Z'. (U', False) \<Turnstile> c\<^sub>2 (\<subseteq> B', Y') = Some (C', Z') \<and>
              C' \<subseteq> C \<and> Z \<subseteq> Z'" and
    C: "(U, False) \<Turnstile> c\<^sub>1;; c\<^sub>2 (\<subseteq> A, X) = Some (C, Z)" and
    D: "A' \<subseteq> A" and
    E: "X \<subseteq> X'" and
    F: "\<forall>(B', Y') \<in> U'. \<exists>(B, Y) \<in> U. B' \<subseteq> B \<and> Y' \<subseteq> Y"
  shows "\<exists>C' Z'. (U', False) \<Turnstile> c\<^sub>1;; c\<^sub>2 (\<subseteq> A', X') = Some (C', Z') \<and>
    C' \<subseteq> C \<and> Z \<subseteq> Z'"
proof -
  obtain B Y where "(U, False) \<Turnstile> c\<^sub>1 (\<subseteq> A, X) = Some (B, Y) \<and>
    (U, False) \<Turnstile> c\<^sub>2 (\<subseteq> B, Y) = Some (C, Z)"
    using C by (auto split: option.split_asm)
  moreover from this obtain B' Y' where
    G: "(U', False) \<Turnstile> c\<^sub>1 (\<subseteq> A', X') = Some (B', Y') \<and> B' \<subseteq> B \<and> Y \<subseteq> Y'"
    using A and D and E and F by fastforce
  ultimately obtain C' Z' where
   "(U', False) \<Turnstile> c\<^sub>2 (\<subseteq> B', Y') = Some (C', Z') \<and> C' \<subseteq> C \<and> Z \<subseteq> Z'"
    using B and F by fastforce
  thus ?thesis
    using G by simp
qed

lemma ctyping2_mono_or:
  assumes
    A: "\<And>A' C\<^sub>1 X' Y\<^sub>1 U'.
      (U, False) \<Turnstile> c\<^sub>1 (\<subseteq> A, X) = Some (C\<^sub>1, Y\<^sub>1) \<Longrightarrow> A' \<subseteq> A \<Longrightarrow> X \<subseteq> X' \<Longrightarrow>
        \<forall>(B', Y') \<in> U'. \<exists>(B, Y) \<in> U. B' \<subseteq> B \<and> Y' \<subseteq> Y \<Longrightarrow>
          \<exists>C\<^sub>1' Y\<^sub>1'. (U', False) \<Turnstile> c\<^sub>1 (\<subseteq> A', X') = Some (C\<^sub>1', Y\<^sub>1') \<and>
            C\<^sub>1' \<subseteq> C\<^sub>1 \<and> Y\<^sub>1 \<subseteq> Y\<^sub>1'" and
    B: "\<And>A' C\<^sub>2 X' Y\<^sub>2 U'.
      (U, False) \<Turnstile> c\<^sub>2 (\<subseteq> A, X) = Some (C\<^sub>2, Y\<^sub>2) \<Longrightarrow> A' \<subseteq> A \<Longrightarrow> X \<subseteq> X' \<Longrightarrow>
        \<forall>(B', Y') \<in> U'. \<exists>(B, Y) \<in> U. B' \<subseteq> B \<and> Y' \<subseteq> Y \<Longrightarrow>
          \<exists>C\<^sub>2' Y\<^sub>2'. (U', False) \<Turnstile> c\<^sub>2 (\<subseteq> A', X') = Some (C\<^sub>2', Y\<^sub>2') \<and>
            C\<^sub>2' \<subseteq> C\<^sub>2 \<and> Y\<^sub>2 \<subseteq> Y\<^sub>2'" and
    C: "(U, False) \<Turnstile> c\<^sub>1 OR c\<^sub>2 (\<subseteq> A, X) = Some (C, Y)" and
    D: "A' \<subseteq> A" and
    E: "X \<subseteq> X'" and
    F: "\<forall>(B', Y') \<in> U'. \<exists>(B, Y) \<in> U. B' \<subseteq> B \<and> Y' \<subseteq> Y"
  shows "\<exists>C' Y'. (U', False) \<Turnstile> c\<^sub>1 OR c\<^sub>2 (\<subseteq> A', X') = Some (C', Y') \<and>
    C' \<subseteq> C \<and> Y \<subseteq> Y'"
proof -
  obtain C\<^sub>1 C\<^sub>2 Y\<^sub>1 Y\<^sub>2 where
    G: "(C, Y) = (C\<^sub>1 \<union> C\<^sub>2, Y\<^sub>1 \<inter> Y\<^sub>2) \<and>
      Some (C\<^sub>1, Y\<^sub>1) = (U, False) \<Turnstile> c\<^sub>1 (\<subseteq> A, X) \<and>
      Some (C\<^sub>2, Y\<^sub>2) = (U, False) \<Turnstile> c\<^sub>2 (\<subseteq> A, X)"
    using C by (simp split: option.split_asm prod.split_asm)
  moreover have H: "\<forall>(B', Y') \<in> U'. \<exists>(B, Y) \<in> U. B' \<subseteq> B \<and> Y' \<subseteq> Y"
    using F by simp
  ultimately have "\<exists>C\<^sub>1' Y\<^sub>1'.
    (U', False) \<Turnstile> c\<^sub>1 (\<subseteq> A', X') = Some (C\<^sub>1', Y\<^sub>1') \<and> C\<^sub>1' \<subseteq> C\<^sub>1 \<and> Y\<^sub>1 \<subseteq> Y\<^sub>1'"
    using A and D and E by simp
  moreover have "\<exists>C\<^sub>2' Y\<^sub>2'.
    (U', False) \<Turnstile> c\<^sub>2 (\<subseteq> A', X') = Some (C\<^sub>2', Y\<^sub>2') \<and> C\<^sub>2' \<subseteq> C\<^sub>2 \<and> Y\<^sub>2 \<subseteq> Y\<^sub>2'"
    using B and D and E and G and H by simp
  ultimately show ?thesis
    using G by auto
qed

lemma ctyping2_mono_if:
  assumes
    A: "\<And>W p B\<^sub>1 B\<^sub>2 B\<^sub>1' C\<^sub>1 X' Y\<^sub>1 W'. (W, p) =
      (insert (Univ? A X, bvars b) U, \<Turnstile> b (\<subseteq> A, X)) \<Longrightarrow> (B\<^sub>1, B\<^sub>2) = p \<Longrightarrow>
        (W, False) \<Turnstile> c\<^sub>1 (\<subseteq> B\<^sub>1, X) = Some (C\<^sub>1, Y\<^sub>1) \<Longrightarrow> B\<^sub>1' \<subseteq> B\<^sub>1 \<Longrightarrow>
          X \<subseteq> X' \<Longrightarrow> \<forall>(B', Y') \<in> W'. \<exists>(B, Y) \<in> W. B' \<subseteq> B \<and> Y' \<subseteq> Y \<Longrightarrow>
            \<exists>C\<^sub>1' Y\<^sub>1'. (W', False) \<Turnstile> c\<^sub>1 (\<subseteq> B\<^sub>1', X') = Some (C\<^sub>1', Y\<^sub>1') \<and>
              C\<^sub>1' \<subseteq> C\<^sub>1 \<and> Y\<^sub>1 \<subseteq> Y\<^sub>1'" and
    B: "\<And>W p B\<^sub>1 B\<^sub>2 B\<^sub>2' C\<^sub>2 X' Y\<^sub>2 W'. (W, p) =
      (insert (Univ? A X, bvars b) U, \<Turnstile> b (\<subseteq> A, X)) \<Longrightarrow> (B\<^sub>1, B\<^sub>2) = p \<Longrightarrow>
        (W, False) \<Turnstile> c\<^sub>2 (\<subseteq> B\<^sub>2, X) = Some (C\<^sub>2, Y\<^sub>2) \<Longrightarrow> B\<^sub>2' \<subseteq> B\<^sub>2 \<Longrightarrow>
          X \<subseteq> X' \<Longrightarrow> \<forall>(B', Y') \<in> W'. \<exists>(B, Y) \<in> W. B' \<subseteq> B \<and> Y' \<subseteq> Y \<Longrightarrow>
            \<exists>C\<^sub>2' Y\<^sub>2'. (W', False) \<Turnstile> c\<^sub>2 (\<subseteq> B\<^sub>2', X') = Some (C\<^sub>2', Y\<^sub>2') \<and>
              C\<^sub>2' \<subseteq> C\<^sub>2 \<and> Y\<^sub>2 \<subseteq> Y\<^sub>2'" and
    C: "(U, False) \<Turnstile> IF b THEN c\<^sub>1 ELSE c\<^sub>2 (\<subseteq> A, X) = Some (C, Y)" and
    D: "A' \<subseteq> A" and
    E: "X \<subseteq> X'" and
    F: "\<forall>(B', Y') \<in> U'. \<exists>(B, Y) \<in> U. B' \<subseteq> B \<and> Y' \<subseteq> Y"
  shows "\<exists>C' Y'. (U', False) \<Turnstile> IF b THEN c\<^sub>1 ELSE c\<^sub>2 (\<subseteq> A', X') =
    Some (C', Y') \<and> C' \<subseteq> C \<and> Y \<subseteq> Y'"
proof -
  let ?W = "insert (Univ? A X, bvars b) U"
  let ?W' = "insert (Univ? A' X', bvars b) U'"
  obtain B\<^sub>1 B\<^sub>2 C\<^sub>1 C\<^sub>2 Y\<^sub>1 Y\<^sub>2 where
    G: "(C, Y) = (C\<^sub>1 \<union> C\<^sub>2, Y\<^sub>1 \<inter> Y\<^sub>2) \<and> (B\<^sub>1, B\<^sub>2) = \<Turnstile> b (\<subseteq> A, X) \<and>
      Some (C\<^sub>1, Y\<^sub>1) = (?W, False) \<Turnstile> c\<^sub>1 (\<subseteq> B\<^sub>1, X) \<and>
      Some (C\<^sub>2, Y\<^sub>2) = (?W, False) \<Turnstile> c\<^sub>2 (\<subseteq> B\<^sub>2, X)"
    using C by (simp split: option.split_asm prod.split_asm)
  moreover obtain B\<^sub>1' B\<^sub>2' where H: "(B\<^sub>1', B\<^sub>2') = \<Turnstile> b (\<subseteq> A', X')"
    by (cases "\<Turnstile> b (\<subseteq> A', X')", simp)
  ultimately have I: "B\<^sub>1' \<subseteq> B\<^sub>1 \<and> B\<^sub>2' \<subseteq> B\<^sub>2"
    by (metis btyping2_mono D E)
  moreover have J: "\<forall>(B', Y') \<in> ?W'. \<exists>(B, Y) \<in> ?W. B' \<subseteq> B \<and> Y' \<subseteq> Y"
    using D and E and F by (auto simp: univ_states_if_def)
  ultimately have "\<exists>C\<^sub>1' Y\<^sub>1'.
    (?W', False) \<Turnstile> c\<^sub>1 (\<subseteq> B\<^sub>1', X') = Some (C\<^sub>1', Y\<^sub>1') \<and> C\<^sub>1' \<subseteq> C\<^sub>1 \<and> Y\<^sub>1 \<subseteq> Y\<^sub>1'"
    using A and E and G by force
  moreover have "\<exists>C\<^sub>2' Y\<^sub>2'.
    (?W', False) \<Turnstile> c\<^sub>2 (\<subseteq> B\<^sub>2', X') = Some (C\<^sub>2', Y\<^sub>2') \<and> C\<^sub>2' \<subseteq> C\<^sub>2 \<and> Y\<^sub>2 \<subseteq> Y\<^sub>2'"
    using B and E and G and I and J by force
  ultimately show ?thesis
    using G and H by (auto split: prod.split)
qed

lemma ctyping2_mono_while:
  assumes
    A: "\<And>B\<^sub>1 B\<^sub>2 C Y B\<^sub>1' B\<^sub>2' D\<^sub>1 E X' V U'. (B\<^sub>1, B\<^sub>2) = \<Turnstile> b (\<subseteq> A, X) \<Longrightarrow>
      (C, Y) = \<turnstile> c (\<subseteq> B\<^sub>1, X) \<Longrightarrow> (B\<^sub>1', B\<^sub>2') = \<Turnstile> b (\<subseteq> C, Y) \<Longrightarrow>
        \<forall>(B, W) \<in> insert (Univ? A X \<union> Univ? C Y, bvars b) U.
          B: W \<leadsto> UNIV \<Longrightarrow>
          ({}, False) \<Turnstile> c (\<subseteq> B\<^sub>1, X) = Some (E, V) \<Longrightarrow> D\<^sub>1 \<subseteq> B\<^sub>1 \<Longrightarrow>
            X \<subseteq> X' \<Longrightarrow> \<forall>(B', Y') \<in> U'. \<exists>(B, Y) \<in> {}. B' \<subseteq> B \<and> Y' \<subseteq> Y \<Longrightarrow>
              \<exists>E' V'. (U', False) \<Turnstile> c (\<subseteq> D\<^sub>1, X') = Some (E', V') \<and>
                E' \<subseteq> E \<and> V \<subseteq> V'" and
    B: "\<And>B\<^sub>1 B\<^sub>2 C Y B\<^sub>1' B\<^sub>2' D\<^sub>1' F Y' W U'. (B\<^sub>1, B\<^sub>2) = \<Turnstile> b (\<subseteq> A, X) \<Longrightarrow>
      (C, Y) = \<turnstile> c (\<subseteq> B\<^sub>1, X) \<Longrightarrow> (B\<^sub>1', B\<^sub>2') = \<Turnstile> b (\<subseteq> C, Y) \<Longrightarrow>
        \<forall>(B, W) \<in> insert (Univ? A X \<union> Univ? C Y, bvars b) U.
          B: W \<leadsto> UNIV \<Longrightarrow>
          ({}, False) \<Turnstile> c (\<subseteq> B\<^sub>1', Y) = Some (F, W) \<Longrightarrow> D\<^sub>1' \<subseteq> B\<^sub>1' \<Longrightarrow>
            Y \<subseteq> Y' \<Longrightarrow> \<forall>(B', Y') \<in> U'. \<exists>(B, Y) \<in> {}. B' \<subseteq> B \<and> Y' \<subseteq> Y \<Longrightarrow>
              \<exists>F' W'. (U', False) \<Turnstile> c (\<subseteq> D\<^sub>1', Y') = Some (F', W') \<and>
                F' \<subseteq> F \<and> W \<subseteq> W'" and
    C: "(U, False) \<Turnstile> WHILE b DO c (\<subseteq> A, X) = Some (B, Z)" and
    D: "A' \<subseteq> A" and
    E: "X \<subseteq> X'" and
    F: "\<forall>(B', Y') \<in> U'. \<exists>(B, Y) \<in> U. B' \<subseteq> B \<and> Y' \<subseteq> Y"
  shows "\<exists>B' Z'. (U', False) \<Turnstile> WHILE b DO c (\<subseteq> A', X') = Some (B', Z') \<and>
    B' \<subseteq> B \<and> Z \<subseteq> Z'"
proof -
  obtain B\<^sub>1 B\<^sub>1' B\<^sub>2 B\<^sub>2' C E F V W Y where G: "(B\<^sub>1, B\<^sub>2) = \<Turnstile> b (\<subseteq> A, X) \<and>
    (C, Y) = \<turnstile> c (\<subseteq> B\<^sub>1, X) \<and> (B\<^sub>1', B\<^sub>2') = \<Turnstile> b (\<subseteq> C, Y) \<and>
    (\<forall>(B, W) \<in> insert (Univ? A X \<union> Univ? C Y, bvars b) U. B: W \<leadsto> UNIV) \<and>
    Some (E, V) = ({}, False) \<Turnstile> c (\<subseteq> B\<^sub>1, X) \<and>
    Some (F, W) = ({}, False) \<Turnstile> c (\<subseteq> B\<^sub>1', Y) \<and>
    (B, Z) = (B\<^sub>2 \<union> B\<^sub>2', Univ?? B\<^sub>2 X \<inter> Y)"
    using C by (force split: if_split_asm option.split_asm prod.split_asm)
  moreover obtain D\<^sub>1 D\<^sub>2 where H: "\<Turnstile> b (\<subseteq> A', X') = (D\<^sub>1, D\<^sub>2)"
    by (cases "\<Turnstile> b (\<subseteq> A', X')", simp)
  ultimately have I: "D\<^sub>1 \<subseteq> B\<^sub>1 \<and> D\<^sub>2 \<subseteq> B\<^sub>2"
    by (smt (verit) btyping2_mono D E)
  moreover obtain C' Y' where J: "\<turnstile> c (\<subseteq> D\<^sub>1, X') = (C', Y')"
    by (cases "\<turnstile> c (\<subseteq> D\<^sub>1, X')", simp)
  ultimately have K: "C' \<subseteq> C \<and> Y \<subseteq> Y'"
    by (smt (verit) ctyping1_mono E G)
  moreover obtain D\<^sub>1' D\<^sub>2' where L: "\<Turnstile> b (\<subseteq> C', Y') = (D\<^sub>1', D\<^sub>2')"
    by (cases "\<Turnstile> b (\<subseteq> C', Y')", simp)
  ultimately have M: "D\<^sub>1' \<subseteq> B\<^sub>1' \<and> D\<^sub>2' \<subseteq> B\<^sub>2'"
    by (smt (verit) btyping2_mono G)
  then obtain F' W' where
   "({}, False) \<Turnstile> c (\<subseteq> D\<^sub>1', Y') = Some (F', W') \<and> F' \<subseteq> F \<and> W \<subseteq> W'"
    using B and F and G and K by force
  moreover obtain E' V' where
   "({}, False) \<Turnstile> c (\<subseteq> D\<^sub>1, X') = Some (E', V') \<and> E' \<subseteq> E \<and> V \<subseteq> V'"
    using A and E and F and G and I by force
  moreover have "Univ? A' X' \<subseteq> Univ? A X"
    using D and E by (auto simp: univ_states_if_def)
  moreover have "Univ? C' Y' \<subseteq> Univ? C Y"
    using K by (auto simp: univ_states_if_def)
  ultimately have "(U', False) \<Turnstile> WHILE b DO c (\<subseteq> A', X') =
    Some (D\<^sub>2 \<union> D\<^sub>2', Univ?? D\<^sub>2 X' \<inter> Y')"
    using F and G and H and J and L by force
  moreover have "D\<^sub>2 \<union> D\<^sub>2' \<subseteq> B"
    using G and I and M by auto
  moreover have "Z \<subseteq> Univ?? D\<^sub>2 X' \<inter> Y'"
    using E and G and I and K by auto
  ultimately show ?thesis
    by simp
qed

lemma ctyping2_mono:
 "\<lbrakk>(U, False) \<Turnstile> c (\<subseteq> A, X) = Some (C, Z); A' \<subseteq> A; X \<subseteq> X';
    \<forall>(B', Y') \<in> U'. \<exists>(B, Y) \<in> U. B' \<subseteq> B \<and> Y' \<subseteq> Y\<rbrakk> \<Longrightarrow>
  \<exists>C' Z'. (U', False) \<Turnstile> c (\<subseteq> A', X') = Some (C', Z') \<and> C' \<subseteq> C \<and> Z \<subseteq> Z'"
  apply (induction "(U, False)" c A X arbitrary: A' C X' Z U U'
   rule: ctyping2.induct)
         apply fastforce
        apply fastforce
       apply fastforce
      apply fastforce
     apply (erule ctyping2_mono_seq, assumption+)
    apply (erule ctyping2_mono_or, assumption+)
   apply (erule ctyping2_mono_if, assumption+)
  apply (erule ctyping2_mono_while, assumption+)
  done


lemma ctyping1_ctyping2_fst_assign [elim!]:
  assumes
    A: "\<turnstile> x ::= a (\<subseteq> A, X) = (C, Z)" and
    B: "(U, False) \<Turnstile> x ::= a (\<subseteq> A, X) = Some (C', Z')"
  shows "C' \<subseteq> C"
proof -
  let ?F = "\<lambda>x' w. if x = x'
    then (x, w) # [y\<leftarrow>[]. fst y = x']
    else [y\<leftarrow>[]. fst y = x']"
  {
    fix s'
    assume "s' \<in> C'"
    moreover assume "x \<in> state" and C: "avars a = {}"
    ultimately obtain s where D: "s \<in> A" and E: "s' = s(x := aval a s)"
      using B by (auto split: if_split_asm)
    have "\<exists>s.
      (\<exists>t. s' = (\<lambda>x'. if ?F x' (Some (aval a (\<lambda>x. 0))) = []
        then s x'
        else case snd (last (?F x' (Some (aval a (\<lambda>x. 0))))) of
          None \<Rightarrow> t x' | Some i \<Rightarrow> i)) \<and>
      s \<in> A"
      apply (insert C E)
      apply (rule exI [of _ s])
      apply (rule conjI [OF _ D])
      apply (rule exI [of _ "\<lambda>x. 0"])
      by (fastforce intro: avars_aval)
  }
  moreover {
    fix s'
    assume "s' \<in> C'"
    moreover assume "x \<in> state" and "avars a \<noteq> {}"
    ultimately obtain s where C: "s \<in> A" and D: "s' = s"
      using B by (simp split: if_split_asm)
    have "\<exists>s.
      (\<exists>t. s' = (\<lambda>x'. if ?F x' None = []
        then s x'
        else case snd (last (?F x' None)) of
          None \<Rightarrow> t x' | Some i \<Rightarrow> i)) \<and>
      s \<in> A"
      apply (insert D)
      apply (rule exI [of _ s])
      apply (rule conjI [OF _ C])
      apply (rule exI [of _ s])
      by auto
  }
  moreover {
    fix s'
    assume "s' \<in> C'" and "x \<notin> state"
    hence "s' \<in> A"
      using B by (simp split: if_split_asm)
  }
  ultimately show ?thesis
    using A by (fastforce simp: ctyping1_def)
qed

lemma ctyping1_ctyping2_fst_input [elim!]:
  assumes
    A: "\<turnstile> IN x (\<subseteq> A, X) = (C, Z)" and
    B: "(U, False) \<Turnstile> IN x (\<subseteq> A, X) = Some (C', Z')"
  shows "C' \<subseteq> C"
proof -
  let ?F = "\<lambda>x'. if x = x'
    then (x, None) # [y\<leftarrow>[]. fst y = x']
    else [y\<leftarrow>[]. fst y = x']"
  {
    fix s'
    assume "s' \<in> C'"
    moreover assume "x \<in> state"
    ultimately obtain s where C: "s \<in> A" and D: "s' = s"
      using B by (simp split: if_split_asm)
    have "\<exists>s.
      (\<exists>t. s' = (\<lambda>x'. if ?F x' = []
        then s x'
        else case snd (last (?F x')) of
          None \<Rightarrow> t x' | Some i \<Rightarrow> i)) \<and>
      s \<in> A"
      apply (insert D)
      apply (rule exI [of _ s])
      apply (rule conjI [OF _ C])
      apply (rule exI [of _ s])
      by auto
  }
  moreover {
    fix s'
    assume "s' \<in> C'" and "x \<notin> state"
    hence "s' \<in> A"
      using B by (simp split: if_split_asm)
  }
  ultimately show ?thesis
    using A by (fastforce simp: ctyping1_def)
qed

lemma ctyping1_ctyping2_fst_output [elim!]:
 "\<lbrakk>\<turnstile> OUT x (\<subseteq> A, X) = (C, Z);
    (U, False) \<Turnstile> OUT x (\<subseteq> A, X) = Some (C', Z')\<rbrakk> \<Longrightarrow>
  C' \<subseteq> C"
by (simp add: ctyping1_def split: if_split_asm)

lemma ctyping1_ctyping2_fst_seq:
  assumes
    A: "\<turnstile> c\<^sub>1;; c\<^sub>2 (\<subseteq> A, X) = (C, Z)" and
    B: "(U, False) \<Turnstile> c\<^sub>1;; c\<^sub>2 (\<subseteq> A, X) = Some (C', Z')" and
    C: "\<And>B B' Y Y'. \<turnstile> c\<^sub>1 (\<subseteq> A, X) = (B, Y) \<Longrightarrow>
      (U, False) \<Turnstile> c\<^sub>1 (\<subseteq> A, X) = Some (B', Y') \<Longrightarrow> B' \<subseteq> B" and
    D: "\<And>p B' Y' D' C' W' Z'.
      (U, False) \<Turnstile> c\<^sub>1 (\<subseteq> A, X) = Some p \<Longrightarrow> (B', Y') = p \<Longrightarrow>
        \<turnstile> c\<^sub>2 (\<subseteq> B', Y') = (D', W') \<Longrightarrow>
          (U, False) \<Turnstile> c\<^sub>2 (\<subseteq> B', Y') = Some (C', Z') \<Longrightarrow> C' \<subseteq> D'"
  shows "C' \<subseteq> C"
proof -
  obtain B' Y' where E: "(U, False) \<Turnstile> c\<^sub>1 (\<subseteq> A, X) = Some (B', Y')" and
   "(U, False) \<Turnstile> c\<^sub>2 (\<subseteq> B', Y') = Some (C', Z')"
    using B by (auto split: option.split_asm)
  moreover obtain D' W' where F: "\<turnstile> c\<^sub>2 (\<subseteq> B', Y') = (D', W')"
    by (cases "\<turnstile> c\<^sub>2 (\<subseteq> B', Y')", simp)
  ultimately have G: "C' \<subseteq> D'"
    using D by simp
  obtain B Y where H: "\<turnstile> c\<^sub>1 (\<subseteq> A, X) = (B, Y)"
    by (cases "\<turnstile> c\<^sub>1 (\<subseteq> A, X)", simp)
  hence "B' \<subseteq> B"
    using C and E by simp
  moreover obtain D W where I: "\<turnstile> c\<^sub>2 (\<subseteq> B, Y) = (D, W)"
    by (cases "\<turnstile> c\<^sub>2 (\<subseteq> B, Y)", simp)
  ultimately have "D' \<subseteq> D"
    using F by (blast dest: ctyping1_mono_fst)
  moreover {
    fix ys ys' s t and t' :: state
    assume K: "s \<in> A"
    assume "ys \<in> \<turnstile> c\<^sub>1" and "ys' \<in> \<turnstile> c\<^sub>2"
    hence L: "ys @ ys' \<in> \<turnstile> c\<^sub>1 \<squnion>\<^sub>@ \<turnstile> c\<^sub>2"
      by (force simp: ctyping1_merge_append_def
       ctyping1_append_def ctyping1_merge_def)
    let ?f = "\<lambda>x. [y\<leftarrow>ys @ ys'. fst y = x]"
    let ?t = "\<lambda>x. if [y\<leftarrow>ys'. fst y = x] = [] then t x else t' x"
    have "\<exists>f s'.
      (\<exists>t''.
        (\<lambda>x. if [y\<leftarrow>ys'. fst y = x] = []
          then if [y\<leftarrow>ys. fst y = x] = []
            then s x
            else case snd (last [y\<leftarrow>ys. fst y = x]) of
              None \<Rightarrow> t x | Some i \<Rightarrow> i
          else case snd (last [y\<leftarrow>ys'. fst y = x]) of
            None \<Rightarrow> t' x | Some i \<Rightarrow> i) =
        (\<lambda>x. if f x = []
          then s' x
          else case snd (last (f x)) of None \<Rightarrow> t'' x | Some i \<Rightarrow> i)) \<and>
      (\<exists>ys''. f = (\<lambda>x. [y\<leftarrow>ys''. fst y = x]) \<and> ys'' \<in> \<turnstile> c\<^sub>1 \<squnion>\<^sub>@ \<turnstile> c\<^sub>2) \<and> s' \<in> A"
      apply (insert K L)
      apply (rule exI [of _ ?f])
      apply (rule exI [of _ s])
      apply (rule conjI)
       apply (rule exI [of _ ?t])
       apply fastforce
      apply (rule conjI)
       apply (rule exI [of _ "ys @ ys'"])
      by simp_all
  }
  hence "D \<subseteq> C"
    using A and H and I by (auto simp: ctyping1_def)
  ultimately show ?thesis
    using G by simp
qed

lemma ctyping1_ctyping2_fst_or:
  assumes
    A: "\<turnstile> c\<^sub>1 OR c\<^sub>2 (\<subseteq> A, X) = (C, Y)" and
    B: "(U, False) \<Turnstile> c\<^sub>1 OR c\<^sub>2 (\<subseteq> A, X) = Some (C', Y')" and
    C: "\<And>C C' Y Y'. \<turnstile> c\<^sub>1 (\<subseteq> A, X) = (C, Y) \<Longrightarrow>
      (U, False) \<Turnstile> c\<^sub>1 (\<subseteq> A, X) = Some (C', Y') \<Longrightarrow> C' \<subseteq> C" and
    D: "\<And>C C' Y Y'. \<turnstile> c\<^sub>2 (\<subseteq> A, X) = (C, Y) \<Longrightarrow>
      (U, False) \<Turnstile> c\<^sub>2 (\<subseteq> A, X) = Some (C', Y') \<Longrightarrow> C' \<subseteq> C"
  shows "C' \<subseteq> C"
proof -
  obtain C\<^sub>1' C\<^sub>2' Y\<^sub>1' Y\<^sub>2' where
    E: "(C', Y') = (C\<^sub>1' \<union> C\<^sub>2', Y\<^sub>1' \<inter> Y\<^sub>2')" and
    F: "(U, False) \<Turnstile> c\<^sub>1 (\<subseteq> A, X) = Some (C\<^sub>1', Y\<^sub>1')" and
    G: "(U, False) \<Turnstile> c\<^sub>2 (\<subseteq> A, X) = Some (C\<^sub>2', Y\<^sub>2')"
    using B by (auto split: option.split_asm prod.split_asm)
  obtain C\<^sub>1 Y\<^sub>1 where H: "\<turnstile> c\<^sub>1 (\<subseteq> A, X) = (C\<^sub>1, Y\<^sub>1)"
    by (cases "\<turnstile> c\<^sub>1 (\<subseteq> A, X)", simp)
  hence "C\<^sub>1' \<subseteq> C\<^sub>1"
    using C and F by simp
  moreover obtain C\<^sub>2 Y\<^sub>2 where I: "\<turnstile> c\<^sub>2 (\<subseteq> A, X) = (C\<^sub>2, Y\<^sub>2)"
    by (cases "\<turnstile> c\<^sub>2 (\<subseteq> A, X)", simp)
  hence "C\<^sub>2' \<subseteq> C\<^sub>2"
    using D and G by simp
  ultimately have "C' \<subseteq> C\<^sub>1 \<union> C\<^sub>2"
    using E by blast
  moreover {
    fix ys s t
    assume "s \<in> A"
    moreover assume "ys \<in> \<turnstile> c\<^sub>1"
    hence "ys \<in> \<turnstile> c\<^sub>1 \<squnion> \<turnstile> c\<^sub>2"
      by (force simp: ctyping1_merge_def)
    ultimately have "\<exists>f s'.
      (\<exists>t'.
        (\<lambda>x. if [y\<leftarrow>ys. fst y = x] = []
          then s x
          else case snd (last [y\<leftarrow>ys. fst y = x]) of
            None \<Rightarrow> t x | Some i \<Rightarrow> i) =
        (\<lambda>x. if f x = []
          then s' x
          else case snd (last (f x)) of None \<Rightarrow> t' x | Some i \<Rightarrow> i)) \<and>
      (\<exists>ys'. f = (\<lambda>x. [y\<leftarrow>ys'. fst y = x]) \<and> ys' \<in> \<turnstile> c\<^sub>1 \<squnion> \<turnstile> c\<^sub>2) \<and> s' \<in> A"
      by fastforce
  }
  hence "C\<^sub>1 \<subseteq> C"
    using A and H by (auto simp: ctyping1_def)
  moreover {
    fix ys s t
    assume "s \<in> A"
    moreover assume "ys \<in> \<turnstile> c\<^sub>2"
    hence "ys \<in> \<turnstile> c\<^sub>1 \<squnion> \<turnstile> c\<^sub>2"
      by (force simp: ctyping1_merge_def)
    ultimately have "\<exists>f s'.
      (\<exists>t'.
        (\<lambda>x. if [y\<leftarrow>ys. fst y = x] = []
          then s x
          else case snd (last [y\<leftarrow>ys. fst y = x]) of
            None \<Rightarrow> t x | Some i \<Rightarrow> i) =
        (\<lambda>x. if f x = []
          then s' x
          else case snd (last (f x)) of None \<Rightarrow> t' x | Some i \<Rightarrow> i)) \<and>
      (\<exists>ys'. f = (\<lambda>x. [y\<leftarrow>ys'. fst y = x]) \<and> ys' \<in> \<turnstile> c\<^sub>1 \<squnion> \<turnstile> c\<^sub>2) \<and> s' \<in> A"
      by fastforce
  }
  hence "C\<^sub>2 \<subseteq> C"
    using A and I by (auto simp: ctyping1_def)
  ultimately show ?thesis
    by blast
qed

lemma ctyping1_ctyping2_fst_if:
  assumes
    A: "\<turnstile> IF b THEN c\<^sub>1 ELSE c\<^sub>2 (\<subseteq> A, X) = (C, Y)" and
    B: "(U, False) \<Turnstile> IF b THEN c\<^sub>1 ELSE c\<^sub>2 (\<subseteq> A, X) = Some (C', Y')" and
    C: "\<And>U' p B\<^sub>1 B\<^sub>2 C C' Y Y'.
      (U', p) = (insert (Univ? A X, bvars b) U, \<Turnstile> b (\<subseteq> A, X)) \<Longrightarrow>
        (B\<^sub>1, B\<^sub>2) = p \<Longrightarrow> \<turnstile> c\<^sub>1 (\<subseteq> B\<^sub>1, X) = (C, Y) \<Longrightarrow>
          (U', False) \<Turnstile> c\<^sub>1 (\<subseteq> B\<^sub>1, X) = Some (C', Y') \<Longrightarrow> C' \<subseteq> C" and
    D: "\<And>U' p B\<^sub>1 B\<^sub>2 C C' Y Y'.
      (U', p) = (insert (Univ? A X, bvars b) U, \<Turnstile> b (\<subseteq> A, X)) \<Longrightarrow>
        (B\<^sub>1, B\<^sub>2) = p \<Longrightarrow> \<turnstile> c\<^sub>2 (\<subseteq> B\<^sub>2, X) = (C, Y) \<Longrightarrow>
          (U', False) \<Turnstile> c\<^sub>2 (\<subseteq> B\<^sub>2, X) = Some (C', Y') \<Longrightarrow> C' \<subseteq> C"
  shows "C' \<subseteq> C"
proof -
  let ?U' = "insert (Univ? A X, bvars b) U"
  obtain B\<^sub>1 B\<^sub>2 C\<^sub>1' C\<^sub>2' Y\<^sub>1' Y\<^sub>2' where
    E: "(C', Y') = (C\<^sub>1' \<union> C\<^sub>2', Y\<^sub>1' \<inter> Y\<^sub>2')" and
    F: "\<Turnstile> b (\<subseteq> A, X) = (B\<^sub>1, B\<^sub>2)" and
    G: "(?U', False) \<Turnstile> c\<^sub>1 (\<subseteq> B\<^sub>1, X) = Some (C\<^sub>1', Y\<^sub>1')" and
    H: "(?U', False) \<Turnstile> c\<^sub>2 (\<subseteq> B\<^sub>2, X) = Some (C\<^sub>2', Y\<^sub>2')"
    using B by (auto split: option.split_asm prod.split_asm)
  obtain C\<^sub>1 Y\<^sub>1 where I: "\<turnstile> c\<^sub>1 (\<subseteq> B\<^sub>1, X) = (C\<^sub>1, Y\<^sub>1)"
    by (cases "\<turnstile> c\<^sub>1 (\<subseteq> B\<^sub>1, X)", simp)
  hence "C\<^sub>1' \<subseteq> C\<^sub>1"
    using C and F and G by simp
  moreover obtain C\<^sub>2 Y\<^sub>2 where J: "\<turnstile> c\<^sub>2 (\<subseteq> B\<^sub>2, X) = (C\<^sub>2, Y\<^sub>2)"
    by (cases "\<turnstile> c\<^sub>2 (\<subseteq> B\<^sub>2, X)", simp)
  hence "C\<^sub>2' \<subseteq> C\<^sub>2"
    using D and F and H by simp
  ultimately have K: "C' \<subseteq> C\<^sub>1 \<union> C\<^sub>2"
    using E by blast
  {
    fix ys s t
    assume "s \<in> B\<^sub>1"
    hence "s \<in> A"
      using F by (blast dest: btyping2_un_eq)
    moreover assume "ys \<in> \<turnstile> c\<^sub>1"
    hence "ys \<in> \<turnstile> c\<^sub>1 \<squnion> \<turnstile> c\<^sub>2"
      by (force simp: ctyping1_merge_def)
    ultimately have "\<exists>f s'.
      (\<exists>t'.
        (\<lambda>x. if [y\<leftarrow>ys. fst y = x] = []
          then s x
          else case snd (last [y\<leftarrow>ys. fst y = x]) of
            None \<Rightarrow> t x | Some i \<Rightarrow> i) =
        (\<lambda>x. if f x = []
          then s' x
          else case snd (last (f x)) of None \<Rightarrow> t' x | Some i \<Rightarrow> i)) \<and>
      (\<exists>ys'. f = (\<lambda>x. [y\<leftarrow>ys'. fst y = x]) \<and> ys' \<in> \<turnstile> c\<^sub>1 \<squnion> \<turnstile> c\<^sub>2) \<and> s' \<in> A"
      by fastforce
  }
  moreover {
    fix ys s t
    assume "s \<in> B\<^sub>1"
    moreover assume "ys \<in> \<turnstile> c\<^sub>1"
    hence "ys \<in> \<turnstile> c\<^sub>1 \<squnion> {}"
      by (force simp: ctyping1_merge_def)
    ultimately have "\<exists>f s'.
      (\<exists>t'.
        (\<lambda>x. if [y\<leftarrow>ys. fst y = x] = []
          then s x
          else case snd (last [y\<leftarrow>ys. fst y = x]) of
            None \<Rightarrow> t x | Some i \<Rightarrow> i) =
        (\<lambda>x. if f x = []
          then s' x
          else case snd (last (f x)) of None \<Rightarrow> t' x | Some i \<Rightarrow> i)) \<and>
      (\<exists>ys'. f = (\<lambda>x. [y\<leftarrow>ys'. fst y = x]) \<and> ys' \<in> \<turnstile> c\<^sub>1 \<squnion> {}) \<and> s' \<in> B\<^sub>1"
      by fastforce
  }
  ultimately have L: "C\<^sub>1 \<subseteq> C"
    using A and F and I by (cases "\<turnstile> b", auto
     dest!: btyping1_btyping2 [of _ _ A X] simp: ctyping1_def)
  {
    fix ys s t
    assume "s \<in> B\<^sub>2"
    hence "s \<in> A"
      using F by (blast dest: btyping2_un_eq)
    moreover assume "ys \<in> \<turnstile> c\<^sub>2"
    hence "ys \<in> \<turnstile> c\<^sub>1 \<squnion> \<turnstile> c\<^sub>2"
      by (force simp: ctyping1_merge_def)
    ultimately have "\<exists>f s'.
      (\<exists>t'.
        (\<lambda>x. if [y\<leftarrow>ys. fst y = x] = []
          then s x
          else case snd (last [y\<leftarrow>ys. fst y = x]) of
            None \<Rightarrow> t x | Some i \<Rightarrow> i) =
        (\<lambda>x. if f x = []
          then s' x
          else case snd (last (f x)) of None \<Rightarrow> t' x | Some i \<Rightarrow> i)) \<and>
      (\<exists>ys'. f = (\<lambda>x. [y\<leftarrow>ys'. fst y = x]) \<and> ys' \<in> \<turnstile> c\<^sub>1 \<squnion> \<turnstile> c\<^sub>2) \<and> s' \<in> A"
      by fastforce
  }
  moreover {
    fix ys s t
    assume "s \<in> B\<^sub>2"
    moreover assume "ys \<in> \<turnstile> c\<^sub>2"
    hence "ys \<in> {} \<squnion> \<turnstile> c\<^sub>2"
      by (force simp: ctyping1_merge_def)
    ultimately have "\<exists>f s'.
      (\<exists>t'.
        (\<lambda>x. if [y\<leftarrow>ys. fst y = x] = []
          then s x
          else case snd (last [y\<leftarrow>ys. fst y = x]) of
            None \<Rightarrow> t x | Some i \<Rightarrow> i) =
        (\<lambda>x. if f x = []
          then s' x
          else case snd (last (f x)) of None \<Rightarrow> t' x | Some i \<Rightarrow> i)) \<and>
      (\<exists>ys'. f = (\<lambda>x. [y\<leftarrow>ys'. fst y = x]) \<and> ys' \<in> {} \<squnion> \<turnstile> c\<^sub>2) \<and> s' \<in> B\<^sub>2"
      by fastforce
  }
  ultimately have "C\<^sub>2 \<subseteq> C"
    using A and F and J by (cases "\<turnstile> b", auto
     dest!: btyping1_btyping2 [of _ _ A X] simp: ctyping1_def)
  with K and L show ?thesis
    by blast
qed

lemma ctyping1_ctyping2_fst_while:
  assumes
    A: "\<turnstile> WHILE b DO c (\<subseteq> A, X) = (B, Z)" and
    B: "(U, False) \<Turnstile> WHILE b DO c (\<subseteq> A, X) = Some (B', Z')"
  shows "B' \<subseteq> B"
proof -
  obtain B\<^sub>1 B\<^sub>1' B\<^sub>2 B\<^sub>2' C Y where
    C: "\<Turnstile> b (\<subseteq> A, X) = (B\<^sub>1, B\<^sub>2)" and
    D: "\<turnstile> c (\<subseteq> B\<^sub>1, X) = (C, Y)" and
    E: "\<Turnstile> b (\<subseteq> C, Y) = (B\<^sub>1', B\<^sub>2')" and
    F: "(B', Z') = (B\<^sub>2 \<union> B\<^sub>2', Univ?? B\<^sub>2 X \<inter> Y)"
    using B by (force split: if_split_asm option.split_asm prod.split_asm)
  {
    fix s
    assume "s \<in> B\<^sub>2"
    hence "s \<in> A"
      using C by (blast dest: btyping2_un_eq)
    hence "\<exists>f s'.
      (\<exists>t. s = (\<lambda>x. if f x = []
        then s' x
        else case snd (last (f x)) of None \<Rightarrow> t x | Some i \<Rightarrow> i)) \<and>
      (\<exists>ys. f = (\<lambda>x. [y\<leftarrow>ys. fst y = x]) \<and> (ys = [] \<or> ys \<in> \<turnstile> c)) \<and> s' \<in> A"
      by force
  }
  with A and C have G: "B\<^sub>2 \<subseteq> B"
    by (cases "\<turnstile> b", auto dest!: btyping1_btyping2 [of _ _ A X]
     simp: ctyping1_def)
  {
    fix s
    assume "s \<in> B\<^sub>2'"
    hence "s \<in> C"
      using E by (blast dest: btyping2_un_eq)
    then obtain f s' where H:
     "(\<exists>t. s = (\<lambda>x. if f x = []
        then s' x
        else case snd (last (f x)) of None \<Rightarrow> t x | Some i \<Rightarrow> i)) \<and>
      (\<exists>ys. f = (\<lambda>x. [y\<leftarrow>ys. fst y = x]) \<and> ys \<in> \<turnstile> c) \<and> s' \<in> B\<^sub>1"
      using D by (fastforce simp: ctyping1_def)
    hence I: "s' \<in> A"
      using C by (blast dest: btyping2_un_eq)
    have "\<exists>f s'.
      (\<exists>t. s = (\<lambda>x. if f x = []
        then s' x
        else case snd (last (f x)) of None \<Rightarrow> t x | Some i \<Rightarrow> i)) \<and>
      (\<exists>ys. f = (\<lambda>x. [y\<leftarrow>ys. fst y = x]) \<and> (ys = [] \<or> ys \<in> \<turnstile> c)) \<and> s' \<in> A"
      by (rule exI [of _ f], insert H I, auto)
  }
  moreover {
    fix s
    assume "s \<in> B\<^sub>2'"
    moreover assume "\<turnstile> b = Some True"
    ultimately have "\<exists>f s'.
      (\<exists>t. s = (\<lambda>x. if f x = []
        then s' x
        else case snd (last (f x)) of None \<Rightarrow> t x | Some i \<Rightarrow> i)) \<and>
      (\<exists>ys. f = (\<lambda>x. [y\<leftarrow>ys. fst y = x]) \<and> ys \<in> \<turnstile> c) \<and> s' \<in> A"
      using E by (auto dest: btyping1_btyping2 [of _ _ C Y])
  }
  moreover {
    fix s
    assume "s \<in> B\<^sub>2'"
    hence "C \<noteq> {}"
      using E by (blast dest: btyping2_un_eq) 
    hence "B\<^sub>1 \<noteq> {}"
      using D by (auto simp: ctyping1_def)
    moreover assume "\<turnstile> b = Some False"
    ultimately have "s \<in> A"
      using C by (auto dest: btyping1_btyping2 [of _ _ A X])
  }
  ultimately have "B\<^sub>2' \<subseteq> B"
    using A by (cases "\<turnstile> b", auto simp: ctyping1_def)
  with F and G show ?thesis
    by simp
qed

lemma ctyping1_ctyping2_fst:
 "\<lbrakk>\<turnstile> c (\<subseteq> A, X) = (C, Z); (U, False) \<Turnstile> c (\<subseteq> A, X) = Some (C', Z')\<rbrakk> \<Longrightarrow>
    C' \<subseteq> C"
  apply (induction "(U, False)" c A X arbitrary: C C' Z Z' U
   rule: ctyping2.induct)
         apply (fastforce simp: ctyping1_def)
        apply fastforce
       apply fastforce
      apply fastforce
     apply (erule ctyping1_ctyping2_fst_seq, assumption+)
    apply (erule ctyping1_ctyping2_fst_or, assumption+)
   apply (erule ctyping1_ctyping2_fst_if, assumption+)
  apply (erule ctyping1_ctyping2_fst_while, assumption+)
  done


lemma ctyping1_ctyping2_snd_skip [elim!]:
 "\<lbrakk>\<turnstile> SKIP (\<subseteq> A, X) = (C, Z);
    (U, False) \<Turnstile> SKIP (\<subseteq> A, X) = Some (C', Z')\<rbrakk> \<Longrightarrow>
  Z \<subseteq> Z'"
by (simp add: ctyping1_def split: if_split_asm)

lemma ctyping1_ctyping2_snd_assign [elim!]:
 "\<lbrakk>\<turnstile> x ::= a (\<subseteq> A, X) = (C, Z);
    (U, False) \<Turnstile> x ::= a (\<subseteq> A, X) = Some (C', Z')\<rbrakk> \<Longrightarrow>
  Z \<subseteq> Z'"
by (auto simp: ctyping1_def split: if_split_asm)

lemma ctyping1_ctyping2_snd_input [elim!]:
 "\<lbrakk>\<turnstile> IN x (\<subseteq> A, X) = (C, Z);
    (U, False) \<Turnstile> IN x (\<subseteq> A, X) = Some (C', Z')\<rbrakk> \<Longrightarrow>
  Z \<subseteq> Z'"
by (auto simp: ctyping1_def split: if_split_asm)

lemma ctyping1_ctyping2_snd_output [elim!]:
 "\<lbrakk>\<turnstile> OUT x (\<subseteq> A, X) = (C, Z);
    (U, False) \<Turnstile> OUT x (\<subseteq> A, X) = Some (C', Z')\<rbrakk> \<Longrightarrow>
  Z \<subseteq> Z'"
by (simp add: ctyping1_def split: if_split_asm)

lemma ctyping1_ctyping2_snd_seq:
  assumes
    A: "\<turnstile> c\<^sub>1;; c\<^sub>2 (\<subseteq> A, X) = (C, Z)" and
    B: "(U, False) \<Turnstile> c\<^sub>1;; c\<^sub>2 (\<subseteq> A, X) = Some (C', Z')" and
    C: "\<And>B B' Y Y'. \<turnstile> c\<^sub>1 (\<subseteq> A, X) = (B, Y) \<Longrightarrow>
      (U, False) \<Turnstile> c\<^sub>1 (\<subseteq> A, X) = Some (B', Y') \<Longrightarrow> Y \<subseteq> Y'" and
    D: "\<And>p B' Y' D' C' W' Z'.
      (U, False) \<Turnstile> c\<^sub>1 (\<subseteq> A, X) = Some p \<Longrightarrow> (B', Y') = p \<Longrightarrow>
        \<turnstile> c\<^sub>2 (\<subseteq> B', Y') = (D', W') \<Longrightarrow>
          (U, False) \<Turnstile> c\<^sub>2 (\<subseteq> B', Y') = Some (C', Z') \<Longrightarrow> W' \<subseteq> Z'"
  shows "Z \<subseteq> Z'"
proof -
  obtain B' Y' where E: "(U, False) \<Turnstile> c\<^sub>1 (\<subseteq> A, X) = Some (B', Y')" and
   "(U, False) \<Turnstile> c\<^sub>2 (\<subseteq> B', Y') = Some (C', Z')"
    using B by (auto split: option.split_asm)
  moreover obtain D' W' where F: "\<turnstile> c\<^sub>2 (\<subseteq> B', Y') = (D', W')"
    by (cases "\<turnstile> c\<^sub>2 (\<subseteq> B', Y')", simp)
  ultimately have G: "W' \<subseteq> Z'"
    using D by simp
  obtain B Y where H: "\<turnstile> c\<^sub>1 (\<subseteq> A, X) = (B, Y)"
    by (cases "\<turnstile> c\<^sub>1 (\<subseteq> A, X)", simp)
  hence "Y \<subseteq> Y'"
    using C and E by simp
  moreover have "B' \<subseteq> B"
    using H and E by (rule ctyping1_ctyping2_fst)
  moreover obtain D W where I: "\<turnstile> c\<^sub>2 (\<subseteq> B, Y) = (D, W)"
    by (cases "\<turnstile> c\<^sub>2 (\<subseteq> B, Y)", simp)
  ultimately have "W \<subseteq> W'"
    using F by (blast dest: ctyping1_mono)
  moreover {
    fix x
    assume J: "\<forall>f. (\<exists>ys. f = (\<lambda>x. [y\<leftarrow>ys. fst y = x]) \<and> ys \<in> \<turnstile> c\<^sub>1 \<squnion>\<^sub>@ \<turnstile> c\<^sub>2) \<longrightarrow>
      (if f x = [] then x \<in> X else snd (last (f x)) \<noteq> None)"
    {
      fix ys' ys
      assume "ys \<in> \<turnstile> c\<^sub>1" and "ys' \<in> \<turnstile> c\<^sub>2"
      hence "ys @ ys' \<in> \<turnstile> c\<^sub>1 \<squnion>\<^sub>@ \<turnstile> c\<^sub>2"
        by (force simp: ctyping1_merge_append_def
         ctyping1_append_def ctyping1_merge_def)
      moreover assume "[y\<leftarrow>ys. fst y = x] = []" and "[y\<leftarrow>ys'. fst y = x] = []"
      ultimately have "x \<in> X"
        using J by auto
    }
    moreover {
      fix ys ys'
      assume "ys \<in> \<turnstile> c\<^sub>1" and "ys' \<in> \<turnstile> c\<^sub>2"
      hence "ys @ ys' \<in> \<turnstile> c\<^sub>1 \<squnion>\<^sub>@ \<turnstile> c\<^sub>2"
        by (force simp: ctyping1_merge_append_def
         ctyping1_append_def ctyping1_merge_def)
      moreover assume "[y\<leftarrow>ys. fst y = x] \<noteq> []" and "[y\<leftarrow>ys'. fst y = x] = []"
      ultimately have "\<exists>i. snd (last [y\<leftarrow>ys. fst y = x]) = Some i"
        using J by auto
    }
    moreover {
      fix ys'
      assume "ys' \<in> \<turnstile> c\<^sub>2"
      moreover obtain ys where "ys \<in> \<turnstile> c\<^sub>1"
        by (insert ctyping1_aux_nonempty, blast)
      ultimately have "ys @ ys' \<in> \<turnstile> c\<^sub>1 \<squnion>\<^sub>@ \<turnstile> c\<^sub>2"
        by (force simp: ctyping1_merge_append_def
         ctyping1_append_def ctyping1_merge_def)
      moreover assume "[y\<leftarrow>ys'. fst y = x] \<noteq> []"
      ultimately have "\<exists>i. snd (last [y\<leftarrow>ys'. fst y = x]) = Some i"
        using J by auto
    }
    ultimately have "x \<in> {x. \<forall>f \<in> {\<lambda>x. [y\<leftarrow>ys. fst y = x] | ys. ys \<in> \<turnstile> c\<^sub>2}.
      if f x = []
      then x \<in> {x. \<forall>f. (\<exists>ys. f = (\<lambda>x. [y\<leftarrow>ys. fst y = x]) \<and> ys \<in> \<turnstile> c\<^sub>1) \<longrightarrow>
        (if f x = [] then x \<in> X else snd (last (f x)) \<noteq> None)}
      else snd (last (f x)) \<noteq> None}"
      (is "_ \<in> ?X")
      by auto
    moreover assume "x \<notin> (if \<forall>x f s.
      (\<forall>t. x \<noteq> (\<lambda>x. if f x = [] then s x else case snd (last (f x)) of
        None \<Rightarrow> t x | Some i \<Rightarrow> i)) \<or>
      (\<forall>ys. f = (\<lambda>x. [y\<leftarrow>ys. fst y = x]) \<longrightarrow> ys \<notin> \<turnstile> c\<^sub>1) \<or> s \<notin> A
        then UNIV else ?X)"
    hence "x \<notin> ?X"
      by (auto split: if_split_asm)
    ultimately have False
      by contradiction
  }
  hence "Z \<subseteq> W"
    using A and H and I by (cases "A = {}", auto simp: ctyping1_def)
  ultimately show ?thesis
    using G by simp
qed

lemma ctyping1_ctyping2_snd_or:
  assumes
    A: "\<turnstile> c\<^sub>1 OR c\<^sub>2 (\<subseteq> A, X) = (C, Y)" and
    B: "(U, False) \<Turnstile> c\<^sub>1 OR c\<^sub>2 (\<subseteq> A, X) = Some (C', Y')" and
    C: "\<And>C C' Y Y'. \<turnstile> c\<^sub>1 (\<subseteq> A, X) = (C, Y) \<Longrightarrow>
      (U, False) \<Turnstile> c\<^sub>1 (\<subseteq> A, X) = Some (C', Y') \<Longrightarrow> Y \<subseteq> Y'" and
    D: "\<And>C C' Y Y'. \<turnstile> c\<^sub>2 (\<subseteq> A, X) = (C, Y) \<Longrightarrow>
      (U, False) \<Turnstile> c\<^sub>2 (\<subseteq> A, X) = Some (C', Y') \<Longrightarrow> Y \<subseteq> Y'"
  shows "Y \<subseteq> Y'"
proof -
  obtain C\<^sub>1' C\<^sub>2' Y\<^sub>1' Y\<^sub>2' where
    E: "(C', Y') = (C\<^sub>1' \<union> C\<^sub>2', Y\<^sub>1' \<inter> Y\<^sub>2')" and
    F: "(U, False) \<Turnstile> c\<^sub>1 (\<subseteq> A, X) = Some (C\<^sub>1', Y\<^sub>1')" and
    G: "(U, False) \<Turnstile> c\<^sub>2 (\<subseteq> A, X) = Some (C\<^sub>2', Y\<^sub>2')"
    using B by (auto split: option.split_asm prod.split_asm)
  obtain C\<^sub>1 Y\<^sub>1 where H: "\<turnstile> c\<^sub>1 (\<subseteq> A, X) = (C\<^sub>1, Y\<^sub>1)"
    by (cases "\<turnstile> c\<^sub>1 (\<subseteq> A, X)", simp)
  hence "Y\<^sub>1 \<subseteq> Y\<^sub>1'"
    using C and F by simp
  moreover obtain C\<^sub>2 Y\<^sub>2 where I: "\<turnstile> c\<^sub>2 (\<subseteq> A, X) = (C\<^sub>2, Y\<^sub>2)"
    by (cases "\<turnstile> c\<^sub>2 (\<subseteq> A, X)", simp)
  hence "Y\<^sub>2 \<subseteq> Y\<^sub>2'"
    using D and G by simp
  ultimately have "Y\<^sub>1 \<inter> Y\<^sub>2 \<subseteq> Y'"
    using E by blast
  moreover {
    fix x ys
    assume "\<forall>f. (\<exists>ys. f = (\<lambda>x. [y\<leftarrow>ys. fst y = x]) \<and> ys \<in> \<turnstile> c\<^sub>1 \<squnion> \<turnstile> c\<^sub>2) \<longrightarrow>
      (if f x = [] then x \<in> X else snd (last (f x)) \<noteq> None)"
    moreover assume "ys \<in> \<turnstile> c\<^sub>1"
    hence "ys \<in> \<turnstile> c\<^sub>1 \<squnion> \<turnstile> c\<^sub>2"
      by (force simp: ctyping1_merge_def)
    ultimately have "if [y\<leftarrow>ys. fst y = x] = []
      then x \<in> X else snd (last [y\<leftarrow>ys. fst y = x]) \<noteq> None"
      (is ?P)
      by blast
    moreover assume "\<not> ?P"
    ultimately have False
      by contradiction
  }
  hence "Y \<subseteq> Y\<^sub>1"
    using A and H by (cases "A = {}", auto simp: ctyping1_def)
  moreover {
    fix x ys
    assume "\<forall>f. (\<exists>ys. f = (\<lambda>x. [y\<leftarrow>ys. fst y = x]) \<and> ys \<in> \<turnstile> c\<^sub>1 \<squnion> \<turnstile> c\<^sub>2) \<longrightarrow>
      (if f x = [] then x \<in> X else snd (last (f x)) \<noteq> None)"
    moreover assume "ys \<in> \<turnstile> c\<^sub>2"
    hence "ys \<in> \<turnstile> c\<^sub>1 \<squnion> \<turnstile> c\<^sub>2"
      by (force simp: ctyping1_merge_def)
    ultimately have "if [y\<leftarrow>ys. fst y = x] = []
      then x \<in> X else snd (last [y\<leftarrow>ys. fst y = x]) \<noteq> None"
      (is ?P)
      by blast
    moreover assume "\<not> ?P"
    ultimately have False
      by contradiction
  }
  hence "Y \<subseteq> Y\<^sub>2"
    using A and I by (cases "A = {}", auto simp: ctyping1_def)
  ultimately show ?thesis
    by blast
qed

lemma ctyping1_ctyping2_snd_if:
  assumes
    A: "\<turnstile> IF b THEN c\<^sub>1 ELSE c\<^sub>2 (\<subseteq> A, X) = (C, Y)" and
    B: "(U, False) \<Turnstile> IF b THEN c\<^sub>1 ELSE c\<^sub>2 (\<subseteq> A, X) = Some (C', Y')" and
    C: "\<And>U' p B\<^sub>1 B\<^sub>2 C C' Y Y'.
      (U', p) = (insert (Univ? A X, bvars b) U, \<Turnstile> b (\<subseteq> A, X)) \<Longrightarrow>
        (B\<^sub>1, B\<^sub>2) = p \<Longrightarrow> \<turnstile> c\<^sub>1 (\<subseteq> B\<^sub>1, X) = (C, Y) \<Longrightarrow>
          (U', False) \<Turnstile> c\<^sub>1 (\<subseteq> B\<^sub>1, X) = Some (C', Y') \<Longrightarrow> Y \<subseteq> Y'" and
    D: "\<And>U' p B\<^sub>1 B\<^sub>2 C C' Y Y'.
      (U', p) = (insert (Univ? A X, bvars b) U, \<Turnstile> b (\<subseteq> A, X)) \<Longrightarrow>
        (B\<^sub>1, B\<^sub>2) = p \<Longrightarrow> \<turnstile> c\<^sub>2 (\<subseteq> B\<^sub>2, X) = (C, Y) \<Longrightarrow>
          (U', False) \<Turnstile> c\<^sub>2 (\<subseteq> B\<^sub>2, X) = Some (C', Y') \<Longrightarrow> Y \<subseteq> Y'"
  shows "Y \<subseteq> Y'"
proof -
  let ?U' = "insert (Univ? A X, bvars b) U"
  obtain B\<^sub>1 B\<^sub>2 C\<^sub>1' C\<^sub>2' Y\<^sub>1' Y\<^sub>2' where
    E: "(C', Y') = (C\<^sub>1' \<union> C\<^sub>2', Y\<^sub>1' \<inter> Y\<^sub>2')" and
    F: "\<Turnstile> b (\<subseteq> A, X) = (B\<^sub>1, B\<^sub>2)" and
    G: "(?U', False) \<Turnstile> c\<^sub>1 (\<subseteq> B\<^sub>1, X) = Some (C\<^sub>1', Y\<^sub>1')" and
    H: "(?U', False) \<Turnstile> c\<^sub>2 (\<subseteq> B\<^sub>2, X) = Some (C\<^sub>2', Y\<^sub>2')"
    using B by (auto split: option.split_asm prod.split_asm)
  obtain C\<^sub>1 Y\<^sub>1 where I: "\<turnstile> c\<^sub>1 (\<subseteq> B\<^sub>1, X) = (C\<^sub>1, Y\<^sub>1)"
    by (cases "\<turnstile> c\<^sub>1 (\<subseteq> B\<^sub>1, X)", simp)
  hence "Y\<^sub>1 \<subseteq> Y\<^sub>1'"
    using C and F and G by simp
  moreover obtain C\<^sub>2 Y\<^sub>2 where J: "\<turnstile> c\<^sub>2 (\<subseteq> B\<^sub>2, X) = (C\<^sub>2, Y\<^sub>2)"
    by (cases "\<turnstile> c\<^sub>2 (\<subseteq> B\<^sub>2, X)", simp)
  hence "Y\<^sub>2 \<subseteq> Y\<^sub>2'"
    using D and F and H by simp
  ultimately have "Y\<^sub>1 \<inter> Y\<^sub>2 \<subseteq> Y'"
    using E by blast
  moreover have K: "B\<^sub>1 \<union> B\<^sub>2 = A"
    using F by (rule btyping2_un_eq)
  {
    fix x x' ys
    assume "x \<in> (if B\<^sub>1 = {} \<and> B\<^sub>2 = {} then UNIV else
      {x. \<forall>f \<in> {\<lambda>x. [y\<leftarrow>ys. fst y = x] | ys. ys \<in> \<turnstile> c\<^sub>1 \<squnion> \<turnstile> c\<^sub>2}.
        if f x = [] then x \<in> X else snd (last (f x)) \<noteq> None})" and
     "x' \<in> B\<^sub>1"
    hence "\<forall>f. (\<exists>ys. f = (\<lambda>x. [y\<leftarrow>ys. fst y = x]) \<and> ys \<in> \<turnstile> c\<^sub>1 \<squnion> \<turnstile> c\<^sub>2) \<longrightarrow>
      (if f x = [] then x \<in> X else snd (last (f x)) \<noteq> None)"
      by (auto split: if_split_asm)
    moreover assume "ys \<in> \<turnstile> c\<^sub>1"
    hence "ys \<in> \<turnstile> c\<^sub>1 \<squnion> \<turnstile> c\<^sub>2"
      by (force simp: ctyping1_merge_def)
    ultimately have "if [y\<leftarrow>ys. fst y = x] = []
      then x \<in> X else snd (last [y\<leftarrow>ys. fst y = x]) \<noteq> None"
      (is ?P)
      by blast
    moreover assume "\<not> ?P"
    ultimately have False
      by contradiction
  }
  note L = this
  {
    fix x x' ys v
    assume "x \<in> (if B\<^sub>1 = {} \<and> B\<^sub>2 = {} then UNIV else
      {x. \<forall>f \<in> {\<lambda>x. [y\<leftarrow>ys. fst y = x] | ys.
        ys \<in> (if v then \<turnstile> c\<^sub>1 else {}) \<squnion> (if \<not> v then \<turnstile> c\<^sub>2 else {})}.
          if f x = [] then x \<in> X else snd (last (f x)) \<noteq> None})"
    moreover assume M: "x' \<in> B\<^sub>1" and
     "(if v then (B\<^sub>1 \<union> B\<^sub>2, {}) else ({}, B\<^sub>1 \<union> B\<^sub>2)) = (B\<^sub>1, B\<^sub>2)"
    hence v
      by (simp split: if_split_asm)
    ultimately have
     "\<forall>f. (\<exists>ys. f = (\<lambda>x. [y\<leftarrow>ys. fst y = x]) \<and> ys \<in> \<turnstile> c\<^sub>1 \<squnion> {}) \<longrightarrow>
        (if f x = [] then x \<in> X else snd (last (f x)) \<noteq> None)"
      using M by (auto split: if_split_asm)
    moreover assume "ys \<in> \<turnstile> c\<^sub>1"
    hence "ys \<in> \<turnstile> c\<^sub>1 \<squnion> {}"
      by (force simp: ctyping1_merge_def)
    ultimately have "if [y\<leftarrow>ys. fst y = x] = []
      then x \<in> X else snd (last [y\<leftarrow>ys. fst y = x]) \<noteq> None"
      (is ?P)
      by blast
    moreover assume "\<not> ?P"
    ultimately have False
      by contradiction
  }
  note M = this
  from A and F and I and K have "Y \<subseteq> Y\<^sub>1"
    apply (cases "B\<^sub>1 = {}")
     apply (fastforce simp: ctyping1_def)
    apply (cases "\<turnstile> b")
    by (auto dest!: btyping1_btyping2 [of _ _ A X] L M simp: ctyping1_def)
  moreover {
    fix x x' ys
    assume "x \<in> (if B\<^sub>1 = {} \<and> B\<^sub>2 = {} then UNIV else
      {x. \<forall>f \<in> {\<lambda>x. [y\<leftarrow>ys. fst y = x] | ys. ys \<in> \<turnstile> c\<^sub>1 \<squnion> \<turnstile> c\<^sub>2}.
        if f x = [] then x \<in> X else snd (last (f x)) \<noteq> None})" and
     "x' \<in> B\<^sub>2"
    hence "\<forall>f. (\<exists>ys. f = (\<lambda>x. [y\<leftarrow>ys. fst y = x]) \<and> ys \<in> \<turnstile> c\<^sub>1 \<squnion> \<turnstile> c\<^sub>2) \<longrightarrow>
      (if f x = [] then x \<in> X else snd (last (f x)) \<noteq> None)"
      by (auto split: if_split_asm)
    moreover assume "ys \<in> \<turnstile> c\<^sub>2"
    hence "ys \<in> \<turnstile> c\<^sub>1 \<squnion> \<turnstile> c\<^sub>2"
      by (force simp: ctyping1_merge_def)
    ultimately have "if [y\<leftarrow>ys. fst y = x] = []
      then x \<in> X else snd (last [y\<leftarrow>ys. fst y = x]) \<noteq> None"
      (is ?P)
      by blast
    moreover assume "\<not> ?P"
    ultimately have False
      by contradiction
  }
  note N = this
  {
    fix x x' ys v
    assume "x \<in> (if B\<^sub>1 = {} \<and> B\<^sub>2 = {} then UNIV else
      {x. \<forall>f \<in> {\<lambda>x. [y\<leftarrow>ys. fst y = x] | ys.
        ys \<in> (if v then \<turnstile> c\<^sub>1 else {}) \<squnion> (if \<not> v then \<turnstile> c\<^sub>2 else {})}.
          if f x = [] then x \<in> X else snd (last (f x)) \<noteq> None})"
    moreover assume O: "x' \<in> B\<^sub>2" and
     "(if v then (B\<^sub>1 \<union> B\<^sub>2, {}) else ({}, B\<^sub>1 \<union> B\<^sub>2)) = (B\<^sub>1, B\<^sub>2)"
    hence "\<not> v"
      by (simp split: if_split_asm)
    ultimately have
     "\<forall>f. (\<exists>ys. f = (\<lambda>x. [y\<leftarrow>ys. fst y = x]) \<and> ys \<in> {} \<squnion> \<turnstile> c\<^sub>2) \<longrightarrow>
        (if f x = [] then x \<in> X else snd (last (f x)) \<noteq> None)"
      using O by (auto split: if_split_asm)
    moreover assume "ys \<in> \<turnstile> c\<^sub>2"
    hence "ys \<in> {} \<squnion> \<turnstile> c\<^sub>2"
      by (force simp: ctyping1_merge_def)
    ultimately have "if [y\<leftarrow>ys. fst y = x] = []
      then x \<in> X else snd (last [y\<leftarrow>ys. fst y = x]) \<noteq> None"
      (is ?P)
      by blast
    moreover assume "\<not> ?P"
    ultimately have False
      by contradiction
  }
  note O = this
  from A and F and J and K have "Y \<subseteq> Y\<^sub>2"
    apply (cases "B\<^sub>2 = {}")
     apply (fastforce simp: ctyping1_def)
    apply (cases "\<turnstile> b")
    by (auto dest!: btyping1_btyping2 [of _ _ A X] N O simp: ctyping1_def)
  ultimately show ?thesis
    by blast
qed

lemma ctyping1_ctyping2_snd_while:
  assumes
    A: "\<turnstile> WHILE b DO c (\<subseteq> A, X) = (B, Z)" and
    B: "(U, False) \<Turnstile> WHILE b DO c (\<subseteq> A, X) = Some (B', Z')"
  shows "Z \<subseteq> Z'"
proof -
  obtain B\<^sub>1 B\<^sub>1' B\<^sub>2 B\<^sub>2' C Y where
    C: "\<Turnstile> b (\<subseteq> A, X) = (B\<^sub>1, B\<^sub>2)" and
    D: "\<turnstile> c (\<subseteq> B\<^sub>1, X) = (C, Y)" and
    E: "\<Turnstile> b (\<subseteq> C, Y) = (B\<^sub>1', B\<^sub>2')" and
    F: "(B', Z') = (B\<^sub>2 \<union> B\<^sub>2', Univ?? B\<^sub>2 X \<inter> Y)"
    using B by (force split: if_split_asm option.split_asm prod.split_asm)
  have G: "B\<^sub>1 \<union> B\<^sub>2 = A"
    using C by (rule btyping2_un_eq)
  {
    fix x x'
    assume "x \<in> (if B\<^sub>1 = {} \<and> B\<^sub>2 = {} then UNIV else
      {x. \<forall>f \<in> {\<lambda>x. [y\<leftarrow>ys. fst y = x] | ys. ys = [] \<or> ys \<in> \<turnstile> c}.
        if f x = [] then x \<in> X else snd (last (f x)) \<noteq> None})" and
     "x' \<in> B\<^sub>2"
    hence "\<forall>f \<in> {\<lambda>x. [y\<leftarrow>ys. fst y = x] | ys. ys = [] \<or> ys \<in> \<turnstile> c}.
      (if f x = [] then x \<in> X else snd (last (f x)) \<noteq> None)"
      by (auto split: if_split_asm)
    hence "x \<in> X"
      by fastforce
    moreover assume "x \<notin> X"
    ultimately have False
      by contradiction
  }
  note H = this
  {
    fix x x' v
    assume "x \<in> (if B\<^sub>1 = {} \<and> B\<^sub>2 = {} then UNIV else
      {x. \<forall>f \<in> {\<lambda>x. [y\<leftarrow>ys. fst y = x] | ys.
        ys \<in> (if \<not> v then {[]} else {}) \<or> ys \<in> (if v then \<turnstile> c else {})}.
          if f x = [] then x \<in> X else snd (last (f x)) \<noteq> None})"
    moreover assume H: "x' \<in> B\<^sub>2" and
     "(if v then (B\<^sub>1 \<union> B\<^sub>2, {}) else ({}, B\<^sub>1 \<union> B\<^sub>2)) = (B\<^sub>1, B\<^sub>2)"
    hence "\<not> v"
      by (simp split: if_split_asm)
    ultimately have "x \<in> X"
      using H by (auto split: if_split_asm)
    moreover assume "x \<notin> X"
    ultimately have False
      by contradiction
  }
  note I = this
  from A and C and G have "Z \<subseteq> Univ?? B\<^sub>2 X"
    apply (cases "B\<^sub>2 = {}")
     apply fastforce
    apply (cases "\<turnstile> b")
    by (auto dest!: btyping1_btyping2 [of _ _ A X] H I simp: ctyping1_def)
  moreover {
    fix x
    assume "x \<notin> Univ?? B\<^sub>1 {x. \<forall>f \<in> {\<lambda>x. [y\<leftarrow>ys. fst y = x] | ys. ys \<in> \<turnstile> c}.
      if f x = [] then x \<in> X else snd (last (f x)) \<noteq> None}"
    moreover from this have "B\<^sub>1 \<noteq> {}"
      by (simp split: if_split_asm)
    ultimately have "\<not> (\<forall>f.
      (\<exists>ys. f = (\<lambda>x. [y\<leftarrow>ys. fst y = x]) \<and> (ys = [] \<or> ys \<in> \<turnstile> c)) \<longrightarrow>
        (if f x = [] then x \<in> X else snd (last (f x)) \<noteq> None))"
      (is "\<not> ?P")
      by (auto split: if_split_asm)
    moreover assume ?P
    ultimately have False
      by contradiction
  }
  note J = this
  {
    fix x v
    assume "x \<notin> Univ?? B\<^sub>1 {x. \<forall>f \<in> {\<lambda>x. [y\<leftarrow>ys. fst y = x] | ys. ys \<in> \<turnstile> c}.
      if f x = [] then x \<in> X else snd (last (f x)) \<noteq> None}"
    moreover from this have K: "B\<^sub>1 \<noteq> {}"
      by (simp split: if_split_asm)
    ultimately have L: "\<not> (\<forall>f.
      (\<exists>ys. f = (\<lambda>x. [y\<leftarrow>ys. fst y = x]) \<and> ys \<in> \<turnstile> c) \<longrightarrow>
        (if f x = [] then x \<in> X else snd (last (f x)) \<noteq> None))"
      (is "\<not> ?P")
      by (auto split: if_split_asm)
    assume "\<turnstile> b = Some v"
    with C and K have v
      by (auto dest: btyping1_btyping2 [of _ _ A X])
    moreover assume "\<forall>f. (\<exists>ys. f = (\<lambda>x. [y\<leftarrow>ys. fst y = x]) \<and>
      (ys \<in> (if \<not> v then {[]} else {}) \<or> ys \<in> (if v then \<turnstile> c else {}))) \<longrightarrow>
        (if f x = [] then x \<in> X else snd (last (f x)) \<noteq> None)"
    ultimately have ?P
      by simp
    with L have False
      by contradiction
  }
  note K = this
  from A and D and G have "Z \<subseteq> Y"
    apply (cases "A = {}")
     apply (fastforce simp: ctyping1_def)
    apply (cases "\<turnstile> b")
    by (auto dest: J K simp: ctyping1_def)
  ultimately show ?thesis
    using F by simp
qed

lemma ctyping1_ctyping2_snd:
 "\<lbrakk>\<turnstile> c (\<subseteq> A, X) = (C, Z); (U, False) \<Turnstile> c (\<subseteq> A, X) = Some (C', Z')\<rbrakk> \<Longrightarrow>
    Z \<subseteq> Z'"
  apply (induction "(U, False)" c A X arbitrary: C C' Z Z' U
   rule: ctyping2.induct)
         apply fastforce
        apply fastforce
       apply fastforce
      apply fastforce
     apply (erule ctyping1_ctyping2_snd_seq, assumption+)
    apply (erule ctyping1_ctyping2_snd_or, assumption+)
   apply (erule ctyping1_ctyping2_snd_if, assumption+)
  apply (erule ctyping1_ctyping2_snd_while, assumption+)
  done


lemma ctyping1_ctyping2:
 "\<lbrakk>\<turnstile> c (\<subseteq> A, X) = (C, Z); (U, False) \<Turnstile> c (\<subseteq> A, X) = Some (C', Z')\<rbrakk> \<Longrightarrow>
    C' \<subseteq> C \<and> Z \<subseteq> Z'"
by (blast dest: ctyping1_ctyping2_fst ctyping1_ctyping2_snd)


lemma btyping2_aux_approx_1 [elim]:
  assumes
    A: "\<TTurnstile> b\<^sub>1 (\<subseteq> A, X) = Some B\<^sub>1" and
    B: "\<TTurnstile> b\<^sub>2 (\<subseteq> A, X) = Some B\<^sub>2" and
    C: "bval b\<^sub>1 s" and
    D: "bval b\<^sub>2 s" and
    E: "r \<in> A" and
    F: "s = r (\<subseteq> state \<inter> X)"
  shows "\<exists>r' \<in> B\<^sub>1 \<inter> B\<^sub>2. r = r' (\<subseteq> state \<inter> X)"
proof -
  from A and C and E and F have "r \<in> B\<^sub>1"
    by (frule_tac btyping2_aux_subset, drule_tac btyping2_aux_eq, auto)
  moreover from B and D and E and F have "r \<in> B\<^sub>2"
    by (frule_tac btyping2_aux_subset, drule_tac btyping2_aux_eq, auto)
  ultimately show ?thesis
    by blast
qed

lemma btyping2_aux_approx_2 [elim]:
  assumes
    A: "avars a\<^sub>1 \<subseteq> state" and
    B: "avars a\<^sub>2 \<subseteq> state" and
    C: "avars a\<^sub>1 \<subseteq> X" and
    D: "avars a\<^sub>2 \<subseteq> X" and
    E: "aval a\<^sub>1 s < aval a\<^sub>2 s" and
    F: "r \<in> A" and
    G: "s = r (\<subseteq> state \<inter> X)"
  shows "\<exists>r'. r' \<in> A \<and> aval a\<^sub>1 r' < aval a\<^sub>2 r' \<and> r = r' (\<subseteq> state \<inter> X)"
proof -
  have "aval a\<^sub>1 s = aval a\<^sub>1 r \<and> aval a\<^sub>2 s = aval a\<^sub>2 r"
    using A and B and C and D and G by (blast intro: avars_aval)
  thus ?thesis
    using E and F by auto
qed

lemma btyping2_aux_approx_3 [elim]:
  assumes
    A: "avars a\<^sub>1 \<subseteq> state" and
    B: "avars a\<^sub>2 \<subseteq> state" and
    C: "avars a\<^sub>1 \<subseteq> X" and
    D: "avars a\<^sub>2 \<subseteq> X" and
    E: "\<not> aval a\<^sub>1 s < aval a\<^sub>2 s" and
    F: "r \<in> A" and
    G: "s = r (\<subseteq> state \<inter> X)"
  shows "\<exists>r' \<in> A - {s \<in> A. aval a\<^sub>1 s < aval a\<^sub>2 s}. r = r' (\<subseteq> state \<inter> X)"
proof -
  have "aval a\<^sub>1 s = aval a\<^sub>1 r \<and> aval a\<^sub>2 s = aval a\<^sub>2 r"
    using A and B and C and D and G by (blast intro: avars_aval)
  thus ?thesis
    using E and F by auto
qed

lemma btyping2_aux_approx:
 "\<lbrakk>\<TTurnstile> b (\<subseteq> A, X) = Some A'; s \<in> Univ A (\<subseteq> state \<inter> X)\<rbrakk> \<Longrightarrow>
    s \<in> Univ (if bval b s then A' else A - A') (\<subseteq> state \<inter> X)"
by (induction b arbitrary: A', auto dest: btyping2_aux_subset
 split: if_split_asm option.split_asm)

lemma btyping2_approx:
 "\<lbrakk>\<Turnstile> b (\<subseteq> A, X) = (B\<^sub>1, B\<^sub>2); s \<in> Univ A (\<subseteq> state \<inter> X)\<rbrakk> \<Longrightarrow>
    s \<in> Univ (if bval b s then B\<^sub>1 else B\<^sub>2) (\<subseteq> state \<inter> X)"
by (drule sym, simp add: btyping2_def split: option.split_asm,
 drule btyping2_aux_approx, auto)


lemma ctyping2_approx_assign [elim!]:
 "\<lbrakk>\<forall>t'. aval a s = t' x \<longrightarrow> (\<forall>s. t' = s(x := aval a s) \<longrightarrow> s \<notin> A) \<or>
    (\<exists>y \<in> state \<inter> X. y \<noteq> x \<and> t y \<noteq> t' y);
  v \<Turnstile> a (\<subseteq> X); t \<in> A; s = t (\<subseteq> state \<inter> X)\<rbrakk> \<Longrightarrow> False"
by (drule spec [of _ "t(x := aval a t)"], cases a,
 (fastforce simp del: aval.simps(3) intro: avars_aval)+)

lemma ctyping2_approx_if_1:
 "\<lbrakk>bval b s; \<Turnstile> b (\<subseteq> A, X) = (B\<^sub>1, B\<^sub>2); r \<in> A; s = r (\<subseteq> state \<inter> X);
    (insert (Univ? A X, bvars b) U, v) \<Turnstile> c\<^sub>1 (\<subseteq> B\<^sub>1, X) = Some (C\<^sub>1, Y\<^sub>1);
    \<And>A B X Y U v. (U, v) \<Turnstile> c\<^sub>1 (\<subseteq> A, X) = Some (B, Y) \<Longrightarrow>
      \<exists>r \<in> A. s = r (\<subseteq> state \<inter> X) \<Longrightarrow> \<exists>r' \<in> B. t = r' (\<subseteq> state \<inter> Y)\<rbrakk> \<Longrightarrow>
  \<exists>r' \<in> C\<^sub>1 \<union> C\<^sub>2. t = r' (\<subseteq> state \<inter> (Y\<^sub>1 \<inter> Y\<^sub>2))"
by (drule btyping2_approx, blast, fastforce)

lemma ctyping2_approx_if_2:
 "\<lbrakk>\<not> bval b s; \<Turnstile> b (\<subseteq> A, X) = (B\<^sub>1, B\<^sub>2); r \<in> A; s = r (\<subseteq> state \<inter> X);
    (insert (Univ? A X, bvars b) U, v) \<Turnstile> c\<^sub>2 (\<subseteq> B\<^sub>2, X) = Some (C\<^sub>2, Y\<^sub>2);
    \<And>A B X Y U v. (U, v) \<Turnstile> c\<^sub>2 (\<subseteq> A, X) = Some (B, Y) \<Longrightarrow>
      \<exists>r \<in> A. s = r (\<subseteq> state \<inter> X) \<Longrightarrow> \<exists>r' \<in> B. t = r' (\<subseteq> state \<inter> Y)\<rbrakk> \<Longrightarrow>
  \<exists>r' \<in> C\<^sub>1 \<union> C\<^sub>2. t = r' (\<subseteq> state \<inter> (Y\<^sub>1 \<inter> Y\<^sub>2))"
by (drule btyping2_approx, blast, fastforce)

lemma ctyping2_approx_while_1 [elim]:
 "\<lbrakk>\<not> bval b s; r \<in> A; s = r (\<subseteq> state \<inter> X); \<Turnstile> b (\<subseteq> A, X) = (B, {})\<rbrakk> \<Longrightarrow>
    \<exists>t \<in> C. s = t (\<subseteq> state \<inter> Y)"
by (drule btyping2_approx, blast, simp)

lemma ctyping2_approx_while_2 [elim]:
 "\<lbrakk>\<forall>t \<in> B\<^sub>2 \<union> B\<^sub>2'. \<exists>x \<in> state \<inter> (X \<inter> Y). r x \<noteq> t x; \<not> bval b s;
    r \<in> A; s = r (\<subseteq> state \<inter> X); \<Turnstile> b (\<subseteq> A, X) = (B\<^sub>1, B\<^sub>2)\<rbrakk> \<Longrightarrow> False"
by (drule btyping2_approx, blast, auto)

lemma ctyping2_approx_while_aux:
  assumes
    A: "\<Turnstile> b (\<subseteq> A, X) = (B\<^sub>1, B\<^sub>2)" and
    B: "\<turnstile> c (\<subseteq> B\<^sub>1, X) = (C, Y)" and
    C: "\<Turnstile> b (\<subseteq> C, Y) = (B\<^sub>1', B\<^sub>2')" and
    D: "({}, False) \<Turnstile> c (\<subseteq> B\<^sub>1, X) = Some (D, Z)" and
    E: "({}, False) \<Turnstile> c (\<subseteq> B\<^sub>1', Y) = Some (D', Z')" and
    F: "r\<^sub>1 \<in> A" and
    G: "s\<^sub>1 = r\<^sub>1 (\<subseteq> state \<inter> X)" and
    H: "bval b s\<^sub>1" and
    I: "\<And>C B Y W U. (case \<Turnstile> b (\<subseteq> C, Y) of (B\<^sub>1', B\<^sub>2') \<Rightarrow>
      case \<turnstile> c (\<subseteq> B\<^sub>1', Y) of (C', Y') \<Rightarrow>
      case \<Turnstile> b (\<subseteq> C', Y') of (B\<^sub>1'', B\<^sub>2'') \<Rightarrow> if
        (\<forall>s \<in> Univ? C Y \<union> Univ? C' Y'. \<forall>x \<in> bvars b. \<forall>y. s: dom x \<leadsto> dom y) \<and>
        (\<forall>p \<in> U. case p of (B, W) \<Rightarrow> \<forall>s \<in> B. \<forall>x \<in> W. \<forall>y. s: dom x \<leadsto> dom y)
        then case ({}, False) \<Turnstile> c (\<subseteq> B\<^sub>1', Y) of
          None \<Rightarrow> None | Some _ \<Rightarrow> case ({}, False) \<Turnstile> c (\<subseteq> B\<^sub>1'', Y') of
            None \<Rightarrow> None | Some _ \<Rightarrow> Some (B\<^sub>2' \<union> B\<^sub>2'', Univ?? B\<^sub>2' Y \<inter> Y')
        else None) = Some (B, W) \<Longrightarrow>
          \<exists>r \<in> C. s\<^sub>2 = r (\<subseteq> state \<inter> Y) \<Longrightarrow> \<exists>r \<in> B. s\<^sub>3 = r (\<subseteq> state \<inter> W)"
      (is "\<And>C B Y W U. ?P C B Y W U \<Longrightarrow> _ \<Longrightarrow> _") and
    J: "\<And>A B X Y U v. (U, v) \<Turnstile> c (\<subseteq> A, X) = Some (B, Y) \<Longrightarrow>
      \<exists>r \<in> A. s\<^sub>1 = r (\<subseteq> state \<inter> X) \<Longrightarrow> \<exists>r \<in> B. s\<^sub>2 = r (\<subseteq> state \<inter> Y)" and
    K: "\<forall>s \<in> Univ? A X \<union> Univ? C Y. \<forall>x \<in> bvars b. \<forall>y. s: dom x \<leadsto> dom y" and
    L: "\<forall>p \<in> U. \<forall>B W. p = (B, W) \<longrightarrow>
      (\<forall>s \<in> B. \<forall>x \<in> W. \<forall>y. s: dom x \<leadsto> dom y)"
  shows "\<exists>r \<in> B\<^sub>2 \<union> B\<^sub>2'. s\<^sub>3 = r (\<subseteq> state \<inter> Univ?? B\<^sub>2 X \<inter> Y)"
proof -
  obtain C' Y' where M: "\<turnstile> c (\<subseteq> B\<^sub>1', Y) = (C', Y')"
    by (cases "\<turnstile> c (\<subseteq> B\<^sub>1', Y)", simp)
  obtain B\<^sub>1'' B\<^sub>2'' where N: "(B\<^sub>1'', B\<^sub>2'') = \<Turnstile> b (\<subseteq> C', Y')"
    by (cases "\<Turnstile> b (\<subseteq> C', Y')", simp)
  let ?B = "B\<^sub>2' \<union> B\<^sub>2''"
  let ?W = "Univ?? B\<^sub>2' Y \<inter> Y'"
  have "\<turnstile> c (\<subseteq> C, Y) = (C, Y)"
    using ctyping1_idem and B by auto
  moreover have "B\<^sub>1' \<subseteq> C"
    using C by (blast dest: btyping2_un_eq)
  ultimately have O: "C' \<subseteq> C \<and> Y \<subseteq> Y'"
    by (rule ctyping1_mono [OF _ M], simp)
  hence "Univ? C' Y' \<subseteq> Univ? C Y"
    by (auto simp: univ_states_if_def)
  moreover from I have "?P C ?B Y ?W U \<Longrightarrow>
    \<exists>r \<in> C. s\<^sub>2 = r (\<subseteq> state \<inter> Y) \<Longrightarrow> \<exists>r \<in> ?B. s\<^sub>3 = r (\<subseteq> state \<inter> ?W)" .
  ultimately have "(case ({}, False) \<Turnstile> c (\<subseteq> B\<^sub>1'', Y') of
    None \<Rightarrow> None | Some _ \<Rightarrow> Some (?B, ?W)) = Some (?B, ?W) \<Longrightarrow>
      \<exists>r \<in> C. s\<^sub>2 = r (\<subseteq> state \<inter> Y) \<Longrightarrow> \<exists>r \<in> ?B. s\<^sub>3 = r (\<subseteq> state \<inter> ?W)"
    using C and E and K and L and M and N
     by (fastforce split: if_split_asm prod.split_asm)
  moreover have P: "B\<^sub>1'' \<subseteq> B\<^sub>1' \<and> B\<^sub>2'' \<subseteq> B\<^sub>2'"
    by (metis btyping2_mono C N O)
  hence "\<exists>D'' Z''. ({}, False) \<Turnstile> c (\<subseteq> B\<^sub>1'', Y') =
    Some (D'', Z'') \<and> D'' \<subseteq> D' \<and> Z' \<subseteq> Z''"
    using E and O by (auto intro: ctyping2_mono)
  ultimately have
   "\<exists>r \<in> C. s\<^sub>2 = r (\<subseteq> state \<inter> Y) \<Longrightarrow> \<exists>r \<in> ?B. s\<^sub>3 = r (\<subseteq> state \<inter> ?W)"
    by fastforce
  moreover from A and D and F and G and H and J obtain r\<^sub>2 where
   "r\<^sub>2 \<in> D" and "s\<^sub>2 = r\<^sub>2 (\<subseteq> state \<inter> Z)"
    by (drule_tac btyping2_approx, blast, force)
  moreover have "D \<subseteq> C \<and> Y \<subseteq> Z"
    using B and D by (rule ctyping1_ctyping2)
  ultimately obtain r\<^sub>3 where Q: "r\<^sub>3 \<in> ?B" and R: "s\<^sub>3 = r\<^sub>3 (\<subseteq> state \<inter> ?W)"
    by blast
  show ?thesis
  proof (rule bexI [of _ r\<^sub>3])
    show "s\<^sub>3 = r\<^sub>3 (\<subseteq> state \<inter> Univ?? B\<^sub>2 X \<inter> Y)"
      using O and R by auto
  next
    show "r\<^sub>3 \<in> B\<^sub>2 \<union> B\<^sub>2'"
      using P and Q by blast
  qed
qed

lemmas ctyping2_approx_while_3 =
  ctyping2_approx_while_aux [where B\<^sub>2 = "{}", simplified]

lemma ctyping2_approx_while_4:
 "\<lbrakk>\<Turnstile> b (\<subseteq> A, X) = (B\<^sub>1, B\<^sub>2);
  \<turnstile> c (\<subseteq> B\<^sub>1, X) = (C, Y);
  \<Turnstile> b (\<subseteq> C, Y) = (B\<^sub>1', B\<^sub>2');
  ({}, False) \<Turnstile> c (\<subseteq> B\<^sub>1, X) = Some (D, Z);
  ({}, False) \<Turnstile> c (\<subseteq> B\<^sub>1', Y) = Some (D', Z');
  r\<^sub>1 \<in> A; s\<^sub>1 = r\<^sub>1 (\<subseteq> state \<inter> X); bval b s\<^sub>1;
  \<And>C B Y W U. (case \<Turnstile> b (\<subseteq> C, Y) of (B\<^sub>1', B\<^sub>2') \<Rightarrow>
    case \<turnstile> c (\<subseteq> B\<^sub>1', Y) of (C', Y') \<Rightarrow>
    case \<Turnstile> b (\<subseteq> C', Y') of (B\<^sub>1'', B\<^sub>2'') \<Rightarrow>
      if (\<forall>s \<in> Univ? C Y \<union> Univ? C' Y'. \<forall>x \<in> bvars b. \<forall>y. s: dom x \<leadsto> dom y) \<and>
        (\<forall>p \<in> U. case p of (B, W) \<Rightarrow> \<forall>s \<in> B. \<forall>x \<in> W. \<forall>y. s: dom x \<leadsto> dom y)
      then case ({}, False) \<Turnstile> c (\<subseteq> B\<^sub>1', Y) of
        None \<Rightarrow> None | Some _ \<Rightarrow> case ({}, False) \<Turnstile> c (\<subseteq> B\<^sub>1'', Y') of
          None \<Rightarrow> None | Some _ \<Rightarrow> Some (B\<^sub>2' \<union> B\<^sub>2'', Univ?? B\<^sub>2' Y \<inter> Y')
      else None) = Some (B, W) \<Longrightarrow>
    \<exists>r \<in> C. s\<^sub>2 = r (\<subseteq> state \<inter> Y) \<Longrightarrow> \<exists>r \<in> B. s\<^sub>3 = r (\<subseteq> state \<inter> W);
  \<And>A B X Y U v. (U, v) \<Turnstile> c (\<subseteq> A, X) = Some (B, Y) \<Longrightarrow>
    \<exists>r \<in> A. s\<^sub>1 = r (\<subseteq> state \<inter> X) \<Longrightarrow> \<exists>r \<in> B. s\<^sub>2 = r (\<subseteq> state \<inter> Y);
  \<forall>s \<in> Univ? A X \<union> Univ? C Y. \<forall>x \<in> bvars b. \<forall>y. s: dom x \<leadsto> dom y;
  \<forall>p \<in> U. \<forall>B W. p = (B, W) \<longrightarrow> (\<forall>s \<in> B. \<forall>x \<in> W. \<forall>y. s: dom x \<leadsto> dom y);
  \<forall>r \<in> B\<^sub>2 \<union> B\<^sub>2'. \<exists>x \<in> state \<inter> (X \<inter> Y). s\<^sub>3 x \<noteq> r x\<rbrakk> \<Longrightarrow>
    False"
by (drule ctyping2_approx_while_aux, assumption+, auto)

lemma ctyping2_approx:
 "\<lbrakk>(c, s, p) \<Rightarrow> (t, q); (U, v) \<Turnstile> c (\<subseteq> A, X) = Some (B, Y);
    s \<in> Univ A (\<subseteq> state \<inter> X)\<rbrakk> \<Longrightarrow> t \<in> Univ B (\<subseteq> state \<inter> Y)"
proof (induction "(c, s, p)" "(t, q)" arbitrary: A B X Y U v c s p t q
 rule: big_step.induct)
  fix A C X Z U v c\<^sub>1 c\<^sub>2 s p t q and p' :: stage
  show
   "\<lbrakk>\<And>r q A B X Y U v. p' = (r, q) \<Longrightarrow>
      (U, v) \<Turnstile> c\<^sub>1 (\<subseteq> A, X) = Some (B, Y) \<Longrightarrow>
      s \<in> Univ A (\<subseteq> state \<inter> X) \<Longrightarrow> r \<in> Univ B (\<subseteq> state \<inter> Y);
    \<And>r q B C Y Z U v. p' = (r, q) \<Longrightarrow>
      (U, v) \<Turnstile> c\<^sub>2 (\<subseteq> B, Y) = Some (C, Z) \<Longrightarrow>
      r \<in> Univ B (\<subseteq> state \<inter> Y) \<Longrightarrow> t \<in> Univ C (\<subseteq> state \<inter> Z);
    (U, v) \<Turnstile> c\<^sub>1;; c\<^sub>2 (\<subseteq> A, X) = Some (C, Z);
    s \<in> Univ A (\<subseteq> state \<inter> X)\<rbrakk> \<Longrightarrow>
      t \<in> Univ C (\<subseteq> state \<inter> Z)"
    by (cases p', auto split: option.split_asm prod.split_asm)
next
  fix A C X Y U v c\<^sub>1 c\<^sub>2 s p t q
  show
   "\<lbrakk>\<And>A C X Y U v. (U, v) \<Turnstile> c\<^sub>1 (\<subseteq> A, X) = Some (C, Y) \<Longrightarrow>
      s \<in> Univ A (\<subseteq> state \<inter> X) \<Longrightarrow> t \<in> Univ C (\<subseteq> state \<inter> Y);
    (U, v) \<Turnstile> c\<^sub>1 OR c\<^sub>2 (\<subseteq> A, X) = Some (C, Y);
    s \<in> Univ A (\<subseteq> state \<inter> X)\<rbrakk> \<Longrightarrow>
      t \<in> Univ C (\<subseteq> state \<inter> Y)"
    by (fastforce split: option.split_asm)
next
  fix A C X Y U v c\<^sub>1 c\<^sub>2 s p t q
  show
   "\<lbrakk>\<And>A C X Y U v. (U, v) \<Turnstile> c\<^sub>2 (\<subseteq> A, X) = Some (C, Y) \<Longrightarrow>
      s \<in> Univ A (\<subseteq> state \<inter> X) \<Longrightarrow> t \<in> Univ C (\<subseteq> state \<inter> Y);
    (U, v) \<Turnstile> c\<^sub>1 OR c\<^sub>2 (\<subseteq> A, X) = Some (C, Y);
    s \<in> Univ A (\<subseteq> state \<inter> X)\<rbrakk> \<Longrightarrow>
      t \<in> Univ C (\<subseteq> state \<inter> Y)"
    by (fastforce split: option.split_asm)
next
  fix A B X Y U v b c\<^sub>1 c\<^sub>2 s p t q
  show
   "\<lbrakk>bval b s; (c\<^sub>1, s, p) \<Rightarrow> (t, q);
    \<And>A C X Y U v. (U, v) \<Turnstile> c\<^sub>1 (\<subseteq> A, X) = Some (C, Y) \<Longrightarrow>
      s \<in> Univ A (\<subseteq> state \<inter> X) \<Longrightarrow> t \<in> Univ C (\<subseteq> state \<inter> Y);
    (U, v) \<Turnstile> IF b THEN c\<^sub>1 ELSE c\<^sub>2 (\<subseteq> A, X) = Some (B, Y);
    s \<in> Univ A (\<subseteq> state \<inter> X)\<rbrakk> \<Longrightarrow>
      t \<in> Univ B (\<subseteq> state \<inter> Y)"
    by (auto split: option.split_asm prod.split_asm,
     rule ctyping2_approx_if_1)
next
  fix A B X Y U v b c\<^sub>1 c\<^sub>2 s p t q
  show
   "\<lbrakk>\<not> bval b s; (c\<^sub>2, s, p) \<Rightarrow> (t, q);
    \<And>A C X Y U v. (U, v) \<Turnstile> c\<^sub>2 (\<subseteq> A, X) = Some (C, Y) \<Longrightarrow>
      s \<in> Univ A (\<subseteq> state \<inter> X) \<Longrightarrow> t \<in> Univ C (\<subseteq> state \<inter> Y);
    (U, v) \<Turnstile> IF b THEN c\<^sub>1 ELSE c\<^sub>2 (\<subseteq> A, X) = Some (B, Y);
    s \<in> Univ A (\<subseteq> state \<inter> X)\<rbrakk> \<Longrightarrow>
      t \<in> Univ B (\<subseteq> state \<inter> Y)"
    by (auto split: option.split_asm prod.split_asm,
     rule ctyping2_approx_if_2)
next
  fix A B X Y U v b c s\<^sub>1 p\<^sub>1 s\<^sub>2 p\<^sub>2 s\<^sub>3 p\<^sub>3
  show
   "\<lbrakk>bval b s\<^sub>1; (c, s\<^sub>1, p\<^sub>1) \<Rightarrow> (s\<^sub>2, p\<^sub>2);
    \<And>A B X Y U v. (U, v) \<Turnstile> c (\<subseteq> A, X) = Some (B, Y) \<Longrightarrow>
      s\<^sub>1 \<in> Univ A (\<subseteq> state \<inter> X) \<Longrightarrow> s\<^sub>2 \<in> Univ B (\<subseteq> state \<inter> Y);
    (WHILE b DO c, s\<^sub>2, p\<^sub>2) \<Rightarrow> (s\<^sub>3, p\<^sub>3);
    \<And>A B X Y U v. (U, v) \<Turnstile> WHILE b DO c (\<subseteq> A, X) = Some (B, Y) \<Longrightarrow>
      s\<^sub>2 \<in> Univ A (\<subseteq> state \<inter> X) \<Longrightarrow> s\<^sub>3 \<in> Univ B (\<subseteq> state \<inter> Y);
    (U, v) \<Turnstile> WHILE b DO c (\<subseteq> A, X) = Some (B, Y);
    s\<^sub>1 \<in> Univ A (\<subseteq> state \<inter> X)\<rbrakk> \<Longrightarrow>
      s\<^sub>3 \<in> Univ B (\<subseteq> state \<inter> Y)"
  by (auto split: if_split_asm option.split_asm prod.split_asm,
   erule_tac [2] ctyping2_approx_while_4,
   erule ctyping2_approx_while_3)
qed (auto split: if_split_asm option.split_asm prod.split_asm)

end

end
