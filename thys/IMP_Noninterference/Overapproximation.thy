(*  Title:       Information Flow Control via Stateful Intransitive Noninterference in Language IMP
    Author:      Pasquale Noce
                 Senior Staff Firmware Engineer at HID Global, Italy
                 pasquale dot noce dot lavoro at gmail dot com
                 pasquale dot noce at hidglobal dot com
*)

section "Overapproximation of program semantics by the type system"

theory Overapproximation
  imports Idempotence
begin

text \<open>
\null

The purpose of this section is to prove that type system @{const [names_short] noninterf.ctyping2}
overapproximates program semantics, namely that if (a) @{prop "(c, s) \<Rightarrow> t"}, (b) the type system
outputs a @{typ "state set"} @{term B} and a @{typ "vname set"} @{term Y} when it is input program
@{term c}, @{typ "state set"} @{term A}, and @{typ "vname set"} @{term X}, and (c) state @{term s}
agrees with a state in @{term A} on the value of every state variable in @{term X}, then @{term t}
must agree with some state in @{term B} on the value of every state variable in @{term Y} (lemma
@{text ctyping2_approx}).

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
    \<forall>(B, Y) \<in> insert (Univ? A X, Z) U. B: dom ` Y \<leadsto> W\<rbrakk> \<Longrightarrow>
  \<forall>(B, Y) \<in> insert (Univ? A' X', Z) U'. B: dom ` Y \<leadsto> W"
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

lemma btyping2_fst_empty:
 "\<Turnstile> b (\<subseteq> {}, X) = ({}, {})"
by (auto simp: btyping2_def dest: btyping2_aux_subset split: option.split)

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


lemma ctyping1_merge_in:
 "xs \<in> A \<union> B \<Longrightarrow> xs \<in> A \<squnion> B"
by (force simp: ctyping1_merge_def)

lemma ctyping1_merge_append_in:
 "\<lbrakk>xs \<in> A; ys \<in> B\<rbrakk> \<Longrightarrow> xs @ ys \<in> A \<squnion>\<^sub>@ B"
by (force simp: ctyping1_merge_append_def ctyping1_append_def ctyping1_merge_in)

lemma ctyping1_aux_nonempty:
 "\<turnstile> c \<noteq> {}"
by (induction c, simp_all add: Let_def ctyping1_append_def
 ctyping1_merge_def ctyping1_merge_append_def, fastforce+)

lemma ctyping1_mono:
 "\<lbrakk>(B, Y) = \<turnstile> c (\<subseteq> A, X); (B', Y') = \<turnstile> c (\<subseteq> A', X'); A' \<subseteq> A; X \<subseteq> X'\<rbrakk> \<Longrightarrow>
    B' \<subseteq> B \<and> Y \<subseteq> Y'"
by (auto simp: ctyping1_def)

lemma ctyping2_fst_empty:
 "Some (B, Y) = (U, v) \<Turnstile> c (\<subseteq> {}, X) \<Longrightarrow> (B, Y) = ({}, UNIV)"
proof (induction "(U, v)" c "{} :: state set" X arbitrary: B Y U v
 rule: ctyping2.induct)
  fix C X Y U v b c\<^sub>1 c\<^sub>2
  show
   "\<lbrakk>\<And>U' p B\<^sub>2 C Y.
      (U', p) = (insert (Univ? {} X, bvars b) U, \<Turnstile> b (\<subseteq> {}, X)) \<Longrightarrow>
      ({}, B\<^sub>2) = p \<Longrightarrow> Some (C, Y) = (U', v) \<Turnstile> c\<^sub>1 (\<subseteq> {}, X) \<Longrightarrow>
      (C, Y) = ({}, UNIV);
    \<And>U' p B\<^sub>1 C Y.
      (U', p) = (insert (Univ? {} X, bvars b) U, \<Turnstile> b (\<subseteq> {}, X)) \<Longrightarrow>
      (B\<^sub>1, {}) = p \<Longrightarrow> Some (C, Y) = (U', v) \<Turnstile> c\<^sub>2 (\<subseteq> {}, X) \<Longrightarrow>
      (C, Y) = ({}, UNIV);
    Some (C, Y) = (U, v) \<Turnstile> IF b THEN c\<^sub>1 ELSE c\<^sub>2 (\<subseteq> {}, X)\<rbrakk> \<Longrightarrow>
      (C, Y) = ({}, UNIV)"
    by (fastforce simp: btyping2_fst_empty split: option.split_asm)
next
  fix B X Z U v b c
  show
   "\<lbrakk>\<And>B\<^sub>2 C Y B\<^sub>1' B\<^sub>2' B Z.
      ({}, B\<^sub>2) = \<Turnstile> b (\<subseteq> {}, X) \<Longrightarrow>
      (C, Y) = \<turnstile> c (\<subseteq> {}, X) \<Longrightarrow>
      (B\<^sub>1', B\<^sub>2') = \<Turnstile> b (\<subseteq> C, Y) \<Longrightarrow>
      \<forall>(B, W) \<in> insert (Univ? {} X \<union> Univ? C Y, bvars b) U.
        B: dom ` W \<leadsto> UNIV \<Longrightarrow>
      Some (B, Z) = ({}, False) \<Turnstile> c (\<subseteq> {}, X) \<Longrightarrow>
      (B, Z) = ({}, UNIV);
    \<And>B\<^sub>1 B\<^sub>2 C Y B\<^sub>2' B Z.
      (B\<^sub>1, B\<^sub>2) = \<Turnstile> b (\<subseteq> {}, X) \<Longrightarrow>
      (C, Y) = \<turnstile> c (\<subseteq> B\<^sub>1, X) \<Longrightarrow>
      ({}, B\<^sub>2') = \<Turnstile> b (\<subseteq> C, Y) \<Longrightarrow>
      \<forall>(B, W) \<in> insert (Univ? {} X \<union> Univ? C Y, bvars b) U.
        B: dom ` W \<leadsto> UNIV \<Longrightarrow>
      Some (B, Z) = ({}, False) \<Turnstile> c (\<subseteq> {}, Y) \<Longrightarrow>
      (B, Z) = ({}, UNIV);
    Some (B, Z) = (U, v) \<Turnstile> WHILE b DO c (\<subseteq> {}, X)\<rbrakk> \<Longrightarrow>
      (B, Z) = ({}, UNIV)"
    by (simp split: if_split_asm option.split_asm prod.split_asm,
     (fastforce simp: btyping2_fst_empty ctyping1_def)+)
qed (simp_all split: if_split_asm option.split_asm prod.split_asm)


lemma ctyping2_mono_assign [elim!]:
 "\<lbrakk>(U, False) \<Turnstile> x ::= a (\<subseteq> A, X) = Some (C, Z); A' \<subseteq> A; X \<subseteq> X';
    \<forall>(B', Y') \<in> U'. \<exists>(B, Y) \<in> U. B' \<subseteq> B \<and> Y' \<subseteq> Y\<rbrakk> \<Longrightarrow>
  \<exists>C' Z'. (U', False) \<Turnstile> x ::= a (\<subseteq> A', X') = Some (C', Z') \<and>
    C' \<subseteq> C \<and> Z \<subseteq> Z'"
by (frule interf_set_mono [where W = "{dom x}"], auto split: if_split_asm)

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
          B: dom ` W \<leadsto> UNIV \<Longrightarrow>
          ({}, False) \<Turnstile> c (\<subseteq> B\<^sub>1, X) = Some (E, V) \<Longrightarrow> D\<^sub>1 \<subseteq> B\<^sub>1 \<Longrightarrow>
            X \<subseteq> X' \<Longrightarrow> \<forall>(B', Y') \<in> U'. \<exists>(B, Y) \<in> {}. B' \<subseteq> B \<and> Y' \<subseteq> Y \<Longrightarrow>
              \<exists>E' V'. (U', False) \<Turnstile> c (\<subseteq> D\<^sub>1, X') = Some (E', V') \<and>
                E' \<subseteq> E \<and> V \<subseteq> V'" and
    B: "\<And>B\<^sub>1 B\<^sub>2 C Y B\<^sub>1' B\<^sub>2' D\<^sub>1' F Y' W U'. (B\<^sub>1, B\<^sub>2) = \<Turnstile> b (\<subseteq> A, X) \<Longrightarrow>
      (C, Y) = \<turnstile> c (\<subseteq> B\<^sub>1, X) \<Longrightarrow> (B\<^sub>1', B\<^sub>2') = \<Turnstile> b (\<subseteq> C, Y) \<Longrightarrow>
        \<forall>(B, W) \<in> insert (Univ? A X \<union> Univ? C Y, bvars b) U.
          B: dom ` W \<leadsto> UNIV \<Longrightarrow>
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
    (\<forall>(B, W) \<in> insert (Univ? A X \<union> Univ? C Y, bvars b) U.
      B: dom ` W \<leadsto> UNIV) \<and>
    Some (E, V) = ({}, False) \<Turnstile> c (\<subseteq> B\<^sub>1, X) \<and>
    Some (F, W) = ({}, False) \<Turnstile> c (\<subseteq> B\<^sub>1', Y) \<and>
    (B, Z) = (B\<^sub>2 \<union> B\<^sub>2', Univ?? B\<^sub>2 X \<inter> Y)"
    using C by (force split: if_split_asm option.split_asm prod.split_asm)
  moreover obtain D\<^sub>1 D\<^sub>2 where H: "\<Turnstile> b (\<subseteq> A', X') = (D\<^sub>1, D\<^sub>2)"
    by (cases "\<Turnstile> b (\<subseteq> A', X')", simp)
  ultimately have I: "D\<^sub>1 \<subseteq> B\<^sub>1 \<and> D\<^sub>2 \<subseteq> B\<^sub>2"
    by (smt (verit) btyping2_mono D E)
  moreover obtain C' Y' where J: "(C', Y') = \<turnstile> c (\<subseteq> D\<^sub>1, X')"
    by (cases "\<turnstile> c (\<subseteq> D\<^sub>1, X')", simp)
  ultimately have K: "C' \<subseteq> C \<and> Y \<subseteq> Y'"
    by (meson ctyping1_mono E G)
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
    using F and G and H and J [symmetric] and L by force
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
proof (induction "(U, False)" c A X arbitrary: A' C X' Z U U'
 rule: ctyping2.induct)
  fix A A' X X' U U' C Z c\<^sub>1 c\<^sub>2
  show
   "\<lbrakk>\<And>A' B X' Y U'.
      (U, False) \<Turnstile> c\<^sub>1 (\<subseteq> A, X) = Some (B, Y) \<Longrightarrow>
      A' \<subseteq> A \<Longrightarrow> X \<subseteq> X' \<Longrightarrow>
      \<forall>(B', Y') \<in> U'. \<exists>(B, Y) \<in> U. B' \<subseteq> B \<and> Y' \<subseteq> Y \<Longrightarrow>
      \<exists>B' Y'. (U', False) \<Turnstile> c\<^sub>1 (\<subseteq> A', X') = Some (B', Y') \<and>
        B' \<subseteq> B \<and> Y \<subseteq> Y';
    \<And>p B Y A' C X' Z U'. (U, False) \<Turnstile> c\<^sub>1 (\<subseteq> A, X) = Some p \<Longrightarrow>
      (B, Y) = p \<Longrightarrow> (U, False) \<Turnstile> c\<^sub>2 (\<subseteq> B, Y) = Some (C, Z) \<Longrightarrow>
      A' \<subseteq> B \<Longrightarrow> Y \<subseteq> X' \<Longrightarrow>
      \<forall>(B', Y') \<in> U'. \<exists>(B, Y) \<in> U. B' \<subseteq> B \<and> Y' \<subseteq> Y \<Longrightarrow>
      \<exists>C' Z'. (U', False) \<Turnstile> c\<^sub>2 (\<subseteq> A', X') = Some (C', Z') \<and>
        C' \<subseteq> C \<and> Z \<subseteq> Z';
    (U, False) \<Turnstile> c\<^sub>1;; c\<^sub>2 (\<subseteq> A, X) = Some (C, Z);
    A' \<subseteq> A; X \<subseteq> X';
    \<forall>(B', Y') \<in> U'. \<exists>(B, Y) \<in> U. B' \<subseteq> B \<and> Y' \<subseteq> Y\<rbrakk> \<Longrightarrow>
      \<exists>C' Z'. (U', False) \<Turnstile> c\<^sub>1;; c\<^sub>2 (\<subseteq> A', X') = Some (C', Z') \<and>
        C' \<subseteq> C \<and> Z \<subseteq> Z'"
    by (rule ctyping2_mono_seq)
next
  fix A A' X X' U U' C Z b c\<^sub>1 c\<^sub>2
  show
   "\<lbrakk>\<And>U'' p B\<^sub>1 B\<^sub>2 A' C X' Z U'.
      (U'', p) = (insert (Univ? A X, bvars b) U, \<Turnstile> b (\<subseteq> A, X)) \<Longrightarrow>
      (B\<^sub>1, B\<^sub>2) = p \<Longrightarrow> (U'', False) \<Turnstile> c\<^sub>1 (\<subseteq> B\<^sub>1, X) = Some (C, Z) \<Longrightarrow>
      A' \<subseteq> B\<^sub>1 \<Longrightarrow> X \<subseteq> X' \<Longrightarrow>
      \<forall>(B', Y') \<in> U'. \<exists>(B, Y) \<in> U''. B' \<subseteq> B \<and> Y' \<subseteq> Y \<Longrightarrow>
      \<exists>C' Z'. (U', False) \<Turnstile> c\<^sub>1 (\<subseteq> A', X') = Some (C', Z') \<and>
        C' \<subseteq> C \<and> Z \<subseteq> Z';
    \<And>U'' p B\<^sub>1 B\<^sub>2 A' C X' Z U'.
      (U'', p) = (insert (Univ? A X, bvars b) U, \<Turnstile> b (\<subseteq> A, X)) \<Longrightarrow>
      (B\<^sub>1, B\<^sub>2) = p \<Longrightarrow> (U'', False) \<Turnstile> c\<^sub>2 (\<subseteq> B\<^sub>2, X) = Some (C, Z) \<Longrightarrow>
      A' \<subseteq> B\<^sub>2 \<Longrightarrow> X \<subseteq> X' \<Longrightarrow>
      \<forall>(B', Y') \<in> U'. \<exists>(B, Y) \<in> U''. B' \<subseteq> B \<and> Y' \<subseteq> Y \<Longrightarrow>
      \<exists>C' Z'. (U', False) \<Turnstile> c\<^sub>2 (\<subseteq> A', X') = Some (C', Z') \<and>
        C' \<subseteq> C \<and> Z \<subseteq> Z';
    (U, False) \<Turnstile> IF b THEN c\<^sub>1 ELSE c\<^sub>2 (\<subseteq> A, X) = Some (C, Z);
    A' \<subseteq> A; X \<subseteq> X';
    \<forall>(B', Y') \<in> U'. \<exists>(B, Y) \<in> U. B' \<subseteq> B \<and> Y' \<subseteq> Y\<rbrakk> \<Longrightarrow>
      \<exists>C' Z'. (U', False) \<Turnstile> IF b THEN c\<^sub>1 ELSE c\<^sub>2 (\<subseteq> A', X') =
        Some (C', Z') \<and> C' \<subseteq> C \<and> Z \<subseteq> Z'"
    by (rule ctyping2_mono_if)
next
  fix A A' X X' U U' B Z b c
  show
   "\<lbrakk>\<And>B\<^sub>1 B\<^sub>2 C Y B\<^sub>1' B\<^sub>2' A' B X' Z U'.
      (B\<^sub>1, B\<^sub>2) = \<Turnstile> b (\<subseteq> A, X) \<Longrightarrow>
      (C, Y) = \<turnstile> c (\<subseteq> B\<^sub>1, X) \<Longrightarrow>
      (B\<^sub>1', B\<^sub>2') = \<Turnstile> b (\<subseteq> C, Y) \<Longrightarrow>
      \<forall>(B, W) \<in> insert (Univ? A X \<union> Univ? C Y, bvars b) U.
        B: dom ` W \<leadsto> UNIV \<Longrightarrow>
      ({}, False) \<Turnstile> c (\<subseteq> B\<^sub>1, X) = Some (B, Z) \<Longrightarrow>
      A' \<subseteq> B\<^sub>1 \<Longrightarrow> X \<subseteq> X' \<Longrightarrow>
      \<forall>(B', Y') \<in> U'. \<exists>(B, Y) \<in> {}. B' \<subseteq> B \<and> Y' \<subseteq> Y \<Longrightarrow>
        \<exists>B' Z'. (U', False) \<Turnstile> c (\<subseteq> A', X') = Some (B', Z') \<and>
          B' \<subseteq> B \<and> Z \<subseteq> Z';
    \<And>B\<^sub>1 B\<^sub>2 C Y B\<^sub>1' B\<^sub>2' A' B X' Z U'.
      (B\<^sub>1, B\<^sub>2) = \<Turnstile> b (\<subseteq> A, X) \<Longrightarrow>
      (C, Y) = \<turnstile> c (\<subseteq> B\<^sub>1, X) \<Longrightarrow>
      (B\<^sub>1', B\<^sub>2') = \<Turnstile> b (\<subseteq> C, Y) \<Longrightarrow>
      \<forall>(B, W) \<in> insert (Univ? A X \<union> Univ? C Y, bvars b) U.
        B: dom ` W \<leadsto> UNIV \<Longrightarrow>
      ({}, False) \<Turnstile> c (\<subseteq> B\<^sub>1', Y) = Some (B, Z) \<Longrightarrow>
      A' \<subseteq> B\<^sub>1' \<Longrightarrow> Y \<subseteq> X' \<Longrightarrow>
      \<forall>(B', Y') \<in> U'. \<exists>(B, Y) \<in> {}. B' \<subseteq> B \<and> Y' \<subseteq> Y \<Longrightarrow>
        \<exists>B' Z'. (U', False) \<Turnstile> c (\<subseteq> A', X') = Some (B', Z') \<and>
          B' \<subseteq> B \<and> Z \<subseteq> Z';
    (U, False) \<Turnstile> WHILE b DO c (\<subseteq> A, X) = Some (B, Z);
    A' \<subseteq> A; X \<subseteq> X';
    \<forall>(B', Y') \<in> U'. \<exists>(B, Y) \<in> U. B' \<subseteq> B \<and> Y' \<subseteq> Y\<rbrakk> \<Longrightarrow>
      \<exists>B' Z'. (U', False) \<Turnstile> WHILE b DO c (\<subseteq> A', X') =
        Some (B', Z') \<and> B' \<subseteq> B \<and> Z \<subseteq> Z'"
    by (rule ctyping2_mono_while)
qed fastforce+


lemma ctyping1_ctyping2_fst_assign [elim!]:
  assumes
    A: "(C, Z) = \<turnstile> x ::= a (\<subseteq> A, X)" and
    B: "Some (C', Z') = (U, False) \<Turnstile> x ::= a (\<subseteq> A, X)"
  shows "C' \<subseteq> C"
proof -
  {
    fix s
    assume "s \<in> A"
    moreover assume "avars a = {}"
    hence "aval a s = aval a (\<lambda>x. 0)"
      by (blast intro: avars_aval)
    ultimately have "\<exists>s'. (\<exists>t. s(x := aval a s) = (\<lambda>x'. case case
      if x' = x then Some (Some (aval a (\<lambda>x. 0))) else None of
        None \<Rightarrow> None | Some v \<Rightarrow> Some v of
          None \<Rightarrow> s' x' | Some None \<Rightarrow> t x' | Some (Some i) \<Rightarrow> i)) \<and> s' \<in> A"
      by fastforce
  }
  note C = this
  from A and B show ?thesis
    by (clarsimp simp: ctyping1_def ctyping1_seq_def split: if_split_asm,
     erule_tac C, simp, fastforce)
qed

lemma ctyping1_ctyping2_fst_seq:
  assumes
    A: "\<And>B B' Y Y'. (B, Y) = \<turnstile> c\<^sub>1 (\<subseteq> A, X) \<Longrightarrow>
      Some (B', Y') = (U, False) \<Turnstile> c\<^sub>1 (\<subseteq> A, X) \<Longrightarrow> B' \<subseteq> B" and
    B: "\<And>p B Y C C' Z Z'. (U, False) \<Turnstile> c\<^sub>1 (\<subseteq> A, X) = Some p \<Longrightarrow>
      (B, Y) = p \<Longrightarrow> (C, Z) = \<turnstile> c\<^sub>2 (\<subseteq> B, Y) \<Longrightarrow>
        Some (C', Z') = (U, False) \<Turnstile> c\<^sub>2 (\<subseteq> B, Y) \<Longrightarrow> C' \<subseteq> C" and
    C: "(C, Z) = \<turnstile> c\<^sub>1;; c\<^sub>2 (\<subseteq> A, X)" and
    D: "Some (C', Z') = (U, False) \<Turnstile> c\<^sub>1;; c\<^sub>2 (\<subseteq> A, X)"
  shows "C' \<subseteq> C"
proof -
  let ?f = "foldl (;;) (\<lambda>x. None)"
  let ?P = "\<lambda>r A S. \<exists>f s. (\<exists>t. r = (\<lambda>x. case f x of
    None \<Rightarrow> s x | Some None \<Rightarrow> t x | Some (Some i) \<Rightarrow> i)) \<and>
    (\<exists>ys. f = ?f ys \<and> ys \<in> S) \<and> s \<in> A"
  let ?F = "\<lambda>A S. {r. ?P r A S}"
  {
    fix s\<^sub>3 B' Y'
    assume
      E: "\<And>B'' B C C' Z'. B' = B'' \<Longrightarrow> B = B'' \<Longrightarrow> C = ?F B'' (\<turnstile> c\<^sub>2) \<Longrightarrow>
        Some (C', Z') = (U, False) \<Turnstile> c\<^sub>2 (\<subseteq> B'', Y') \<Longrightarrow>
          C' \<subseteq> ?F B'' (\<turnstile> c\<^sub>2)" and
      F: "\<And>B B''. B = ?F A (\<turnstile> c\<^sub>1) \<Longrightarrow> B'' = B' \<Longrightarrow> B' \<subseteq> ?F A (\<turnstile> c\<^sub>1)" and
      G: "Some (C', Z') = (U, False) \<Turnstile> c\<^sub>2 (\<subseteq> B', Y')" and
      H: "s\<^sub>3 \<in> C'"
    have "?P s\<^sub>3 A (\<turnstile> c\<^sub>1 \<squnion>\<^sub>@ \<turnstile> c\<^sub>2)"
    proof -
      obtain s\<^sub>2 and t\<^sub>2 and ys\<^sub>2 where
        I: "s\<^sub>3 = (\<lambda>x. case ?f ys\<^sub>2 x of
          None \<Rightarrow> s\<^sub>2 x | Some None \<Rightarrow> t\<^sub>2 x | Some (Some i) \<Rightarrow> i) \<and>
          s\<^sub>2 \<in> B' \<and> ys\<^sub>2 \<in> \<turnstile> c\<^sub>2"
        using E and G and H by fastforce
      from this obtain s\<^sub>1 and t\<^sub>1 and ys\<^sub>1 where
        J: "s\<^sub>2 = (\<lambda>x. case ?f ys\<^sub>1 x of
          None \<Rightarrow> s\<^sub>1 x | Some None \<Rightarrow> t\<^sub>1 x | Some (Some i) \<Rightarrow> i) \<and>
          s\<^sub>1 \<in> A \<and> ys\<^sub>1 \<in> \<turnstile> c\<^sub>1"
        using F by fastforce
      let ?t = "\<lambda>x. case ?f ys\<^sub>2 x of
        None \<Rightarrow> case ?f ys\<^sub>1 x of Some None \<Rightarrow> t\<^sub>1 x | _ \<Rightarrow> 0 |
        Some None \<Rightarrow> t\<^sub>2 x | _ \<Rightarrow> 0"
      from I and J have "s\<^sub>3 = (\<lambda>x. case ?f (ys\<^sub>1 @ ys\<^sub>2) x of
        None \<Rightarrow> s\<^sub>1 x | Some None \<Rightarrow> ?t x | Some (Some i) \<Rightarrow> i)"
        by (fastforce dest: last_in_set simp: Let_def ctyping1_seq_last
         split: option.split)
      moreover have "ys\<^sub>1 @ ys\<^sub>2 \<in> \<turnstile> c\<^sub>1 \<squnion>\<^sub>@ \<turnstile> c\<^sub>2"
        by (simp add: ctyping1_merge_append_in I J)
      ultimately show ?thesis
        using J by fastforce
    qed
  }
  note E = this
  from A and B and C and D show ?thesis
    by (auto simp: ctyping1_def split: option.split_asm, erule_tac E)
qed

lemma ctyping1_ctyping2_fst_if:
  assumes
    A: "\<And>U' p B\<^sub>1 B\<^sub>2 C\<^sub>1 C\<^sub>1' Y\<^sub>1 Y\<^sub>1'.
      (U', p) = (insert (Univ? A X, bvars b) U, \<Turnstile> b (\<subseteq> A, X)) \<Longrightarrow>
        (B\<^sub>1, B\<^sub>2) = p \<Longrightarrow> (C\<^sub>1, Y\<^sub>1) = \<turnstile> c\<^sub>1 (\<subseteq> B\<^sub>1, X) \<Longrightarrow>
          Some (C\<^sub>1', Y\<^sub>1') = (U', False) \<Turnstile> c\<^sub>1 (\<subseteq> B\<^sub>1, X) \<Longrightarrow> C\<^sub>1' \<subseteq> C\<^sub>1" and
    B: "\<And>U' p B\<^sub>1 B\<^sub>2 C\<^sub>2 C\<^sub>2' Y\<^sub>2 Y\<^sub>2'.
      (U', p) = (insert (Univ? A X, bvars b) U, \<Turnstile> b (\<subseteq> A, X)) \<Longrightarrow>
        (B\<^sub>1, B\<^sub>2) = p \<Longrightarrow> (C\<^sub>2, Y\<^sub>2) = \<turnstile> c\<^sub>2 (\<subseteq> B\<^sub>2, X) \<Longrightarrow>
          Some (C\<^sub>2', Y\<^sub>2') = (U', False) \<Turnstile> c\<^sub>2 (\<subseteq> B\<^sub>2, X) \<Longrightarrow> C\<^sub>2' \<subseteq> C\<^sub>2" and
    C: "(C, Y) = \<turnstile> IF b THEN c\<^sub>1 ELSE c\<^sub>2 (\<subseteq> A, X)" and
    D: "Some (C', Y') = (U, False) \<Turnstile> IF b THEN c\<^sub>1 ELSE c\<^sub>2 (\<subseteq> A, X)"
  shows "C' \<subseteq> C"
proof -
  let ?f = "foldl (;;) (\<lambda>x. None)"
  let ?P = "\<lambda>r A S. \<exists>f s. (\<exists>t. r = (\<lambda>x. case f x of
    None \<Rightarrow> s x | Some None \<Rightarrow> t x | Some (Some i) \<Rightarrow> i)) \<and>
    (\<exists>ys. f = ?f ys \<and> ys \<in> S) \<and> s \<in> A"
  let ?F = "\<lambda>A S. {r. ?P r A S}"
  let ?S\<^sub>1 = "\<lambda>f. if f = Some True \<or> f = None then \<turnstile> c\<^sub>1 else {}"
  let ?S\<^sub>2 = "\<lambda>f. if f = Some False \<or> f = None then \<turnstile> c\<^sub>2 else {}"
  {
    fix s' B\<^sub>1 B\<^sub>2 C\<^sub>1
    assume
      E: "\<And>U' B\<^sub>1' C\<^sub>1' C\<^sub>1''. U' = insert (Univ? A X, bvars b) U \<Longrightarrow>
        B\<^sub>1' = B\<^sub>1 \<Longrightarrow> C\<^sub>1' = ?F B\<^sub>1 (\<turnstile> c\<^sub>1) \<Longrightarrow> C\<^sub>1'' = C\<^sub>1 \<Longrightarrow>
          C\<^sub>1 \<subseteq> ?F B\<^sub>1 (\<turnstile> c\<^sub>1)" and
      F: "\<Turnstile> b (\<subseteq> A, X) = (B\<^sub>1, B\<^sub>2)" and
      G: "s' \<in> C\<^sub>1"
    have "?P s' A (let f = \<turnstile> b in ?S\<^sub>1 f \<squnion> ?S\<^sub>2 f)"
    proof -
      obtain s and t and ys where
        H: "s' = (\<lambda>x. case ?f ys x of
          None \<Rightarrow> s x | Some None \<Rightarrow> t x | Some (Some i) \<Rightarrow> i) \<and>
          s \<in> B\<^sub>1 \<and> ys \<in> \<turnstile> c\<^sub>1"
        using E and G by fastforce
      moreover from F and this have "s \<in> A"
        by (blast dest: btyping2_un_eq)
      moreover from F and H have "\<turnstile> b \<noteq> Some False"
        by (auto dest: btyping1_btyping2 [where A = A and X = X])
      hence "ys \<in> (let f = \<turnstile> b in ?S\<^sub>1 f \<union> ?S\<^sub>2 f)"
        using H by (auto simp: Let_def)
      hence "ys \<in> (let f = \<turnstile> b in ?S\<^sub>1 f \<squnion> ?S\<^sub>2 f)"
        by (auto simp: Let_def intro: ctyping1_merge_in)
      ultimately show ?thesis
        by blast
    qed
  }
  note E = this
  {
    fix s' B\<^sub>1 B\<^sub>2 C\<^sub>2
    assume
      F: "\<And>U' B\<^sub>2' C\<^sub>2' C\<^sub>2''. U' = insert (Univ? A X, bvars b) U \<Longrightarrow>
        B\<^sub>2' = B\<^sub>1 \<Longrightarrow> C\<^sub>2' = ?F B\<^sub>2 (\<turnstile> c\<^sub>2) \<Longrightarrow> C\<^sub>2'' = C\<^sub>2 \<Longrightarrow>
          C\<^sub>2 \<subseteq> ?F B\<^sub>2 (\<turnstile> c\<^sub>2)" and
      G: "\<Turnstile> b (\<subseteq> A, X) = (B\<^sub>1, B\<^sub>2)" and
      H: "s' \<in> C\<^sub>2"
    have "?P s' A (let f = \<turnstile> b in ?S\<^sub>1 f \<squnion> ?S\<^sub>2 f)"
    proof -
      obtain s and t and ys where
        I: "s' = (\<lambda>x. case ?f ys x of
          None \<Rightarrow> s x | Some None \<Rightarrow> t x | Some (Some i) \<Rightarrow> i) \<and>
          s \<in> B\<^sub>2 \<and> ys \<in> \<turnstile> c\<^sub>2"
        using F and H by fastforce
      moreover from G and this have "s \<in> A"
        by (blast dest: btyping2_un_eq)
      moreover from G and I have "\<turnstile> b \<noteq> Some True"
        by (auto dest: btyping1_btyping2 [where A = A and X = X])
      hence "ys \<in> (let f = \<turnstile> b in ?S\<^sub>1 f \<union> ?S\<^sub>2 f)"
        using I by (auto simp: Let_def)
      hence "ys \<in> (let f = \<turnstile> b in ?S\<^sub>1 f \<squnion> ?S\<^sub>2 f)"
        by (auto simp: Let_def intro: ctyping1_merge_in)
      ultimately show ?thesis
        by blast
    qed
  }
  note F = this
  from A and B and C and D show ?thesis
    by (auto simp: ctyping1_def split: option.split_asm prod.split_asm,
     erule_tac [2] F, erule_tac E)
qed

lemma ctyping1_ctyping2_fst_while:
  assumes
    A: "(C, Y) = \<turnstile> WHILE b DO c (\<subseteq> A, X)" and
    B: "Some (C', Y') = (U, False) \<Turnstile> WHILE b DO c (\<subseteq> A, X)"
  shows "C' \<subseteq> C"
proof -
  let ?f = "foldl (;;) (\<lambda>x. None)"
  let ?P = "\<lambda>r A S. \<exists>f s. (\<exists>t. r = (\<lambda>x. case f x of
    None \<Rightarrow> s x | Some None \<Rightarrow> t x | Some (Some i) \<Rightarrow> i)) \<and>
    (\<exists>ys. f = ?f ys \<and> ys \<in> S) \<and> s \<in> A"
  let ?F = "\<lambda>A S. {r. ?P r A S}"
  let ?S\<^sub>1 = "\<lambda>f. if f = Some False \<or> f = None then {[]} else {}"
  let ?S\<^sub>2 = "\<lambda>f. if f = Some True \<or> f = None then \<turnstile> c else {}"
  {
    fix s' B\<^sub>1 B\<^sub>2 B\<^sub>1' B\<^sub>2'
    assume
      C: "\<Turnstile> b (\<subseteq> A, X) = (B\<^sub>1, B\<^sub>2)" and
      D: "\<Turnstile> b (\<subseteq> ?F B\<^sub>1 (\<turnstile> c), Univ?? B\<^sub>1 {x. \<forall>f \<in> {?f ys |ys. ys \<in> \<turnstile> c}.
        f x \<noteq> Some None \<and> (f x = None \<longrightarrow> x \<in> X)}) = (B\<^sub>1', B\<^sub>2')"
        (is "\<Turnstile> _ (\<subseteq> ?C, ?Y) = _")
    assume "s' \<in> C'" and "Some (C', Y') = (if (\<forall>s \<in> Univ? A X \<union>
      Univ? ?C ?Y. \<forall>x \<in> bvars b. All (interf s (dom x))) \<and>
      (\<forall>p \<in> U. \<forall>B W. p = (B, W) \<longrightarrow> (\<forall>s \<in> B. \<forall>x \<in> W. All (interf s (dom x))))
        then Some (B\<^sub>2 \<union> B\<^sub>2', Univ?? B\<^sub>2 X \<inter> ?Y)
        else None)"
    hence "s' \<in> B\<^sub>2 \<union> B\<^sub>2'"
      by (simp split: if_split_asm)
    hence "?P s' A (let f = \<turnstile> b in ?S\<^sub>1 f \<union> ?S\<^sub>2 f)"
    proof
      assume E: "s' \<in> B\<^sub>2"
      hence "s' \<in> A"
        using C by (blast dest: btyping2_un_eq)
      moreover from C and E have "\<turnstile> b \<noteq> Some True"
        by (auto dest: btyping1_btyping2 [where A = A and X = X])
      hence "[] \<in> (let f = \<turnstile> b in ?S\<^sub>1 f \<union> ?S\<^sub>2 f)"
        by (auto simp: Let_def)
      ultimately show ?thesis
        by force
    next
      assume "s' \<in> B\<^sub>2'"
      then obtain s and t and ys where
        E: "s' = (\<lambda>x. case ?f ys x of
          None \<Rightarrow> s x | Some None \<Rightarrow> t x | Some (Some i) \<Rightarrow> i) \<and>
          s \<in> B\<^sub>1 \<and> ys \<in> \<turnstile> c"
        using D by (blast dest: btyping2_un_eq)
      moreover from C and this have "s \<in> A"
        by (blast dest: btyping2_un_eq)
      moreover from C and E have "\<turnstile> b \<noteq> Some False"
        by (auto dest: btyping1_btyping2 [where A = A and X = X])
      hence "ys \<in> (let f = \<turnstile> b in ?S\<^sub>1 f \<union> ?S\<^sub>2 f)"
        using E by (auto simp: Let_def)
      ultimately show ?thesis
        by blast
    qed
  }
  note C = this
  from A and B show ?thesis
    by (auto intro: C simp: ctyping1_def
     split: option.split_asm prod.split_asm)
qed

lemma ctyping1_ctyping2_fst:
 "\<lbrakk>(C, Z) = \<turnstile> c (\<subseteq> A, X); Some (C', Z') = (U, False) \<Turnstile> c (\<subseteq> A, X)\<rbrakk> \<Longrightarrow>
    C' \<subseteq> C"
proof (induction "(U, False)" c A X arbitrary: C C' Z Z' U
 rule: ctyping2.induct)
  fix A X C C' Z Z' U c\<^sub>1 c\<^sub>2
  show
   "\<lbrakk>\<And>C C' Z Z'.
      (C, Z) = \<turnstile> c\<^sub>1 (\<subseteq> A, X) \<Longrightarrow>
      Some (C', Z') = (U, False) \<Turnstile> c\<^sub>1 (\<subseteq> A, X) \<Longrightarrow>
      C' \<subseteq> C;
    \<And>p B Y C C' Z Z'. (U, False) \<Turnstile> c\<^sub>1 (\<subseteq> A, X) = Some p \<Longrightarrow>
      (B, Y) = p \<Longrightarrow> (C, Z) = \<turnstile> c\<^sub>2 (\<subseteq> B, Y) \<Longrightarrow>
      Some (C', Z') = (U, False) \<Turnstile> c\<^sub>2 (\<subseteq> B, Y) \<Longrightarrow>
      C' \<subseteq> C;
    (C, Z) = \<turnstile> c\<^sub>1;; c\<^sub>2 (\<subseteq> A, X);
    Some (C', Z') = (U, False) \<Turnstile> c\<^sub>1;; c\<^sub>2 (\<subseteq> A, X)\<rbrakk> \<Longrightarrow>
      C' \<subseteq> C"
    by (rule ctyping1_ctyping2_fst_seq)
next
  fix A X C C' Z Z' U b c\<^sub>1 c\<^sub>2
  show
   "\<lbrakk>\<And>U' p B\<^sub>1 B\<^sub>2 C C' Z Z'.
      (U', p) = (insert (Univ? A X, bvars b) U, \<Turnstile> b (\<subseteq> A, X)) \<Longrightarrow>
      (B\<^sub>1, B\<^sub>2) = p \<Longrightarrow> (C, Z) = \<turnstile> c\<^sub>1 (\<subseteq> B\<^sub>1, X) \<Longrightarrow>
      Some (C', Z') = (U', False) \<Turnstile> c\<^sub>1 (\<subseteq> B\<^sub>1, X) \<Longrightarrow>
      C' \<subseteq> C;
    \<And>U' p B\<^sub>1 B\<^sub>2 C C' Z Z'.
      (U', p) = (insert (Univ? A X, bvars b) U, \<Turnstile> b (\<subseteq> A, X)) \<Longrightarrow>
      (B\<^sub>1, B\<^sub>2) = p \<Longrightarrow> (C, Z) = \<turnstile> c\<^sub>2 (\<subseteq> B\<^sub>2, X) \<Longrightarrow>
      Some (C', Z') = (U', False) \<Turnstile> c\<^sub>2 (\<subseteq> B\<^sub>2, X) \<Longrightarrow>
      C' \<subseteq> C;
    (C, Z) = \<turnstile> IF b THEN c\<^sub>1 ELSE c\<^sub>2 (\<subseteq> A, X);
    Some (C', Z') = (U, False) \<Turnstile> IF b THEN c\<^sub>1 ELSE c\<^sub>2 (\<subseteq> A, X)\<rbrakk> \<Longrightarrow>
      C' \<subseteq> C"
    by (rule ctyping1_ctyping2_fst_if)
next
  fix A X B B' Z Z' U b c
  show
   "\<lbrakk>\<And>B\<^sub>1 B\<^sub>2 C Y B\<^sub>1' B\<^sub>2' B B' Z Z'.
      (B\<^sub>1, B\<^sub>2) = \<Turnstile> b (\<subseteq> A, X) \<Longrightarrow>
      (C, Y) = \<turnstile> c (\<subseteq> B\<^sub>1, X) \<Longrightarrow>
      (B\<^sub>1', B\<^sub>2') = \<Turnstile> b (\<subseteq> C, Y) \<Longrightarrow>
      \<forall>(B, W) \<in> insert (Univ? A X \<union> Univ? C Y, bvars b) U.
        B: dom ` W \<leadsto> UNIV \<Longrightarrow>
      (B, Z) = \<turnstile> c (\<subseteq> B\<^sub>1, X) \<Longrightarrow>
      Some (B', Z') = ({}, False) \<Turnstile> c (\<subseteq> B\<^sub>1, X) \<Longrightarrow>
      B' \<subseteq> B;
    \<And>B\<^sub>1 B\<^sub>2 C Y B\<^sub>1' B\<^sub>2' B B' Z Z'.
      (B\<^sub>1, B\<^sub>2) = \<Turnstile> b (\<subseteq> A, X) \<Longrightarrow>
      (C, Y) = \<turnstile> c (\<subseteq> B\<^sub>1, X) \<Longrightarrow>
      (B\<^sub>1', B\<^sub>2') = \<Turnstile> b (\<subseteq> C, Y) \<Longrightarrow>
      \<forall>(B, W) \<in> insert (Univ? A X \<union> Univ? C Y, bvars b) U.
        B: dom ` W \<leadsto> UNIV \<Longrightarrow>
      (B, Z) = \<turnstile> c (\<subseteq> B\<^sub>1', Y) \<Longrightarrow>
      Some (B', Z') = ({}, False) \<Turnstile> c (\<subseteq> B\<^sub>1', Y) \<Longrightarrow>
      B' \<subseteq> B;
    (B, Z) = \<turnstile> WHILE b DO c (\<subseteq> A, X);
    Some (B', Z') = (U, False) \<Turnstile> WHILE b DO c (\<subseteq> A, X)\<rbrakk> \<Longrightarrow>
      B' \<subseteq> B"
    by (rule ctyping1_ctyping2_fst_while)
qed (simp add: ctyping1_def, auto)


lemma ctyping1_ctyping2_snd_assign [elim!]:
 "\<lbrakk>(C, Z) = \<turnstile> x ::= a (\<subseteq> A, X);
    Some (C', Z') = (U, False) \<Turnstile> x ::= a (\<subseteq> A, X)\<rbrakk> \<Longrightarrow> Z \<subseteq> Z'"
by (auto simp: ctyping1_def ctyping1_seq_def split: if_split_asm)

lemma ctyping1_ctyping2_snd_seq:
  assumes
    A: "\<And>B B' Y Y'. (B, Y) = \<turnstile> c\<^sub>1 (\<subseteq> A, X) \<Longrightarrow>
      Some (B', Y') = (U, False) \<Turnstile> c\<^sub>1 (\<subseteq> A, X) \<Longrightarrow> Y \<subseteq> Y'" and
    B: "\<And>p B Y C C' Z Z'. (U, False) \<Turnstile> c\<^sub>1 (\<subseteq> A, X) = Some p \<Longrightarrow>
      (B, Y) = p \<Longrightarrow> (C, Z) = \<turnstile> c\<^sub>2 (\<subseteq> B, Y) \<Longrightarrow>
        Some (C', Z') = (U, False) \<Turnstile> c\<^sub>2 (\<subseteq> B, Y) \<Longrightarrow> Z \<subseteq> Z'" and
    C: "(C, Z) = \<turnstile> c\<^sub>1;; c\<^sub>2 (\<subseteq> A, X)" and
    D: "Some (C', Z') = (U, False) \<Turnstile> c\<^sub>1;; c\<^sub>2 (\<subseteq> A, X)"
  shows "Z \<subseteq> Z'"
proof -
  let ?f = "foldl (;;) (\<lambda>x. None)"
  let ?F = "\<lambda>A S. {r. \<exists>f s. (\<exists>t. r = (\<lambda>x. case f x of
    None \<Rightarrow> s x | Some None \<Rightarrow> t x | Some (Some i) \<Rightarrow> i)) \<and>
    (\<exists>ys. f = ?f ys \<and> ys \<in> S) \<and> s \<in> A}"
  let ?G = "\<lambda>X S. {x. \<forall>f \<in> {?f ys | ys. ys \<in> S}.
    f x \<noteq> Some None \<and> (f x = None \<longrightarrow> x \<in> X)}"
  {
    fix x B Y
    assume "\<And>B' B'' C C' Z'. B = B' \<Longrightarrow> B'' = B' \<Longrightarrow> C = ?F B' (\<turnstile> c\<^sub>2) \<Longrightarrow>
      Some (C', Z') = (U, False) \<Turnstile> c\<^sub>2 (\<subseteq> B', Y) \<Longrightarrow>
        Univ?? B' (?G Y (\<turnstile> c\<^sub>2)) \<subseteq> Z'" and
     "Some (C', Z') = (U, False) \<Turnstile> c\<^sub>2 (\<subseteq> B, Y)"
    hence E: "Univ?? B (?G Y (\<turnstile> c\<^sub>2)) \<subseteq> Z'"
      by simp
    assume "\<And>C B'. C = ?F A (\<turnstile> c\<^sub>1) \<Longrightarrow> B' = B \<Longrightarrow>
      Univ?? A (?G X (\<turnstile> c\<^sub>1)) \<subseteq> Y"
    hence F: "Univ?? A (?G X (\<turnstile> c\<^sub>1)) \<subseteq> Y"
      by simp
    assume G: "\<forall>f. (\<exists>zs. f = ?f zs \<and> zs \<in> \<turnstile> c\<^sub>1 \<squnion>\<^sub>@ \<turnstile> c\<^sub>2) \<longrightarrow>
      f x \<noteq> Some None \<and> (f x = None \<longrightarrow> x \<in> X)"
    {
      fix ys
      have "\<turnstile> c\<^sub>1 \<noteq> {}"
        by (rule ctyping1_aux_nonempty)
      then obtain xs where "xs \<in> \<turnstile> c\<^sub>1"
        by blast
      moreover assume "ys \<in> \<turnstile> c\<^sub>2"
      ultimately have "xs @ ys \<in> \<turnstile> c\<^sub>1 \<squnion>\<^sub>@ \<turnstile> c\<^sub>2"
        by (rule ctyping1_merge_append_in)
      moreover assume "?f ys x = Some None"
      hence "?f (xs @ ys) x = Some None"
        by (simp add: Let_def ctyping1_seq_last split: if_split_asm)
      ultimately have False
        using G by blast
    }
    hence H: "\<forall>ys \<in> \<turnstile> c\<^sub>2. ?f ys x \<noteq> Some None"
      by blast
    {
      fix xs ys
      assume "xs \<in> \<turnstile> c\<^sub>1" and "ys \<in> \<turnstile> c\<^sub>2"
      hence "xs @ ys \<in> \<turnstile> c\<^sub>1 \<squnion>\<^sub>@ \<turnstile> c\<^sub>2"
        by (rule ctyping1_merge_append_in)
      moreover assume "?f xs x = Some None" and "?f ys x = None"
      hence "?f (xs @ ys) x = Some None"
        by (auto dest: last_in_set simp: Let_def ctyping1_seq_last
         split: if_split_asm)
      ultimately have "(\<exists>ys \<in> \<turnstile> c\<^sub>2. ?f ys x = None) \<longrightarrow>
        (\<forall>xs \<in> \<turnstile> c\<^sub>1. ?f xs x \<noteq> Some None)"
        using G by blast
    }
    hence I: "(\<exists>ys \<in> \<turnstile> c\<^sub>2. ?f ys x = None) \<longrightarrow>
      (\<forall>xs \<in> \<turnstile> c\<^sub>1. ?f xs x \<noteq> Some None)"
      by blast
    {
      fix xs ys
      assume "xs \<in> \<turnstile> c\<^sub>1" and J: "ys \<in> \<turnstile> c\<^sub>2"
      hence "xs @ ys \<in> \<turnstile> c\<^sub>1 \<squnion>\<^sub>@ \<turnstile> c\<^sub>2"
        by (rule ctyping1_merge_append_in)
      moreover assume "?f xs x = None" and K: "?f ys x = None"
      hence "?f (xs @ ys) x = None"
        by (simp add: Let_def ctyping1_seq_last split: if_split_asm)
      ultimately have "x \<in> X"
        using G by blast
      moreover have "\<forall>xs \<in> \<turnstile> c\<^sub>1. ?f xs x \<noteq> Some None"
        using I and J and K by blast
      ultimately have "x \<in> Z'"
        using E and F and H by fastforce
    }
    moreover {
      fix ys
      assume "ys \<in> \<turnstile> c\<^sub>2" and "?f ys x = None"
      hence "\<forall>xs \<in> \<turnstile> c\<^sub>1. ?f xs x \<noteq> Some None"
        using I by blast
      moreover assume "\<forall>xs \<in> \<turnstile> c\<^sub>1. \<exists>v. ?f xs x = Some v"
      ultimately have "x \<in> Z'"
        using E and F and H by fastforce
    }
    moreover {
      assume "\<forall>ys \<in> \<turnstile> c\<^sub>2. \<exists>v. ?f ys x = Some v"
      hence "x \<in> Z'"
        using E and H by fastforce
    }
    ultimately have "x \<in> Z'"
      by (cases "\<exists>ys \<in> \<turnstile> c\<^sub>2. ?f ys x = None",
       cases "\<exists>xs \<in> \<turnstile> c\<^sub>1. ?f xs x = None", auto)
    moreover assume "x \<notin> Z'"
    ultimately have False
      by contradiction
  }
  note E = this
  from A and B and C and D show ?thesis
    by (auto dest: ctyping2_fst_empty ctyping2_fst_empty [OF sym]
     simp: ctyping1_def split: option.split_asm, erule_tac E)
qed

lemma ctyping1_ctyping2_snd_if:
  assumes
    A: "\<And>U' p B\<^sub>1 B\<^sub>2 C\<^sub>1 C\<^sub>1' Y\<^sub>1 Y\<^sub>1'.
      (U', p) = (insert (Univ? A X, bvars b) U, \<Turnstile> b (\<subseteq> A, X)) \<Longrightarrow>
        (B\<^sub>1, B\<^sub>2) = p \<Longrightarrow> (C\<^sub>1, Y\<^sub>1) = \<turnstile> c\<^sub>1 (\<subseteq> B\<^sub>1, X) \<Longrightarrow>
          Some (C\<^sub>1', Y\<^sub>1') = (U', False) \<Turnstile> c\<^sub>1 (\<subseteq> B\<^sub>1, X) \<Longrightarrow> Y\<^sub>1 \<subseteq> Y\<^sub>1'" and
    B: "\<And>U' p B\<^sub>1 B\<^sub>2 C\<^sub>2 C\<^sub>2' Y\<^sub>2 Y\<^sub>2'.
      (U', p) = (insert (Univ? A X, bvars b) U, \<Turnstile> b (\<subseteq> A, X)) \<Longrightarrow>
        (B\<^sub>1, B\<^sub>2) = p \<Longrightarrow> (C\<^sub>2, Y\<^sub>2) = \<turnstile> c\<^sub>2 (\<subseteq> B\<^sub>2, X) \<Longrightarrow>
          Some (C\<^sub>2', Y\<^sub>2') = (U', False) \<Turnstile> c\<^sub>2 (\<subseteq> B\<^sub>2, X) \<Longrightarrow> Y\<^sub>2 \<subseteq> Y\<^sub>2'" and
    C: "(C, Y) = \<turnstile> IF b THEN c\<^sub>1 ELSE c\<^sub>2 (\<subseteq> A, X)" and
    D: "Some (C', Y') = (U, False) \<Turnstile> IF b THEN c\<^sub>1 ELSE c\<^sub>2 (\<subseteq> A, X)"
  shows "Y \<subseteq> Y'"
proof -
  let ?f = "foldl (;;) (\<lambda>x. None)"
  let ?F = "\<lambda>A S. {r. \<exists>f s. (\<exists>t. r = (\<lambda>x. case f x of
    None \<Rightarrow> s x | Some None \<Rightarrow> t x | Some (Some i) \<Rightarrow> i)) \<and>
    (\<exists>ys. f = ?f ys \<and> ys \<in> S) \<and> s \<in> A}"
  let ?G = "\<lambda>X S. {x. \<forall>f \<in> {?f ys | ys. ys \<in> S}.
    f x \<noteq> Some None \<and> (f x = None \<longrightarrow> x \<in> X)}"
  let ?S\<^sub>1 = "\<lambda>f. if f = Some True \<or> f = None then \<turnstile> c\<^sub>1 else {}"
  let ?S\<^sub>2 = "\<lambda>f. if f = Some False \<or> f = None then \<turnstile> c\<^sub>2 else {}"
  let ?P = "\<lambda>x. \<forall>f. (\<exists>ys. f = ?f ys \<and> ys \<in> (let f = \<turnstile> b in ?S\<^sub>1 f \<squnion> ?S\<^sub>2 f)) \<longrightarrow>
    f x \<noteq> Some None \<and> (f x = None \<longrightarrow> x \<in> X)"
  let ?U = "insert (Univ? A X, bvars b) U"
  {
    fix B\<^sub>1 B\<^sub>2 Y\<^sub>1' Y\<^sub>2' and C\<^sub>1' :: "state set" and C\<^sub>2' :: "state set"
    assume "\<And>U' B\<^sub>1' C\<^sub>1 C\<^sub>1''. U' = ?U \<Longrightarrow> B\<^sub>1' = B\<^sub>1 \<Longrightarrow>
      C\<^sub>1 = ?F B\<^sub>1 (\<turnstile> c\<^sub>1) \<Longrightarrow> C\<^sub>1'' = C\<^sub>1' \<Longrightarrow> Univ?? B\<^sub>1 (?G X (\<turnstile> c\<^sub>1)) \<subseteq> Y\<^sub>1'"
    hence E: "Univ?? B\<^sub>1 (?G X (\<turnstile> c\<^sub>1)) \<subseteq> Y\<^sub>1'"
      by simp
    moreover assume "\<And>U' B\<^sub>1' C\<^sub>2 C\<^sub>2''. U' = ?U \<Longrightarrow> B\<^sub>1' = B\<^sub>1 \<Longrightarrow>
      C\<^sub>2 = ?F B\<^sub>2 (\<turnstile> c\<^sub>2) \<Longrightarrow> C\<^sub>2'' = C\<^sub>2' \<Longrightarrow> Univ?? B\<^sub>2 (?G X (\<turnstile> c\<^sub>2)) \<subseteq> Y\<^sub>2'"
    hence F: "Univ?? B\<^sub>2 (?G X (\<turnstile> c\<^sub>2)) \<subseteq> Y\<^sub>2'"
      by simp
    moreover assume G: "\<Turnstile> b (\<subseteq> A, X) = (B\<^sub>1, B\<^sub>2)"
    moreover {
      fix x
      assume "?P x"
      have "x \<in> Y\<^sub>1'"
      proof (cases "\<turnstile> b = Some False")
        case True
        with E and G show ?thesis
          by (drule_tac btyping1_btyping2 [where A = A and X = X], auto)
      next
        case False
        {
          fix xs
          assume "xs \<in> \<turnstile> c\<^sub>1"
          with False have "xs \<in> (let f = \<turnstile> b in ?S\<^sub>1 f \<squnion> ?S\<^sub>2 f)"
            by (auto intro: ctyping1_merge_in simp: Let_def)
          hence "?f xs x \<noteq> Some None \<and> (?f xs x = None \<longrightarrow> x \<in> X)"
            using `?P x` by auto
        }
        hence "x \<in> Univ?? B\<^sub>1 (?G X (\<turnstile> c\<^sub>1))"
          by auto
        thus ?thesis
          using E ..
      qed
    }
    moreover {
      fix x
      assume "?P x"
      have "x \<in> Y\<^sub>2'"
      proof (cases "\<turnstile> b = Some True")
        case True
        with F and G show ?thesis
          by (drule_tac btyping1_btyping2 [where A = A and X = X], auto)
      next
        case False
        {
          fix ys
          assume "ys \<in> \<turnstile> c\<^sub>2"
          with False have "ys \<in> (let f = \<turnstile> b in ?S\<^sub>1 f \<squnion> ?S\<^sub>2 f)"
            by (auto intro: ctyping1_merge_in simp: Let_def)
          hence "?f ys x \<noteq> Some None \<and> (?f ys x = None \<longrightarrow> x \<in> X)"
            using `?P x` by auto
        }
        hence "x \<in> Univ?? B\<^sub>2 (?G X (\<turnstile> c\<^sub>2))"
          by auto
        thus ?thesis
          using F ..
      qed
    }
    ultimately have "(A = {} \<longrightarrow> UNIV \<subseteq> Y\<^sub>1' \<and> UNIV \<subseteq> Y\<^sub>2') \<and>
      (A \<noteq> {} \<longrightarrow> {x. ?P x} \<subseteq> Y\<^sub>1' \<and> {x. ?P x} \<subseteq> Y\<^sub>2')"
      by (auto simp: btyping2_fst_empty)
  }
  note E = this
  from A and B and C and D show ?thesis
    by (clarsimp simp: ctyping1_def split: option.split_asm prod.split_asm,
     erule_tac E)
qed

lemma ctyping1_ctyping2_snd_while:
  assumes
    A: "(C, Y) = \<turnstile> WHILE b DO c (\<subseteq> A, X)" and
    B: "Some (C', Y') = (U, False) \<Turnstile> WHILE b DO c (\<subseteq> A, X)"
  shows "Y \<subseteq> Y'"
proof -
  let ?f = "foldl (;;) (\<lambda>x. None)"
  let ?F = "\<lambda>A S. {r. \<exists>f s. (\<exists>t. r = (\<lambda>x. case f x of
    None \<Rightarrow> s x | Some None \<Rightarrow> t x | Some (Some i) \<Rightarrow> i)) \<and>
    (\<exists>ys. f = ?f ys \<and> ys \<in> S) \<and> s \<in> A}"
  let ?S\<^sub>1 = "\<lambda>f. if f = Some False \<or> f = None then {[]} else {}"
  let ?S\<^sub>2 = "\<lambda>f. if f = Some True \<or> f = None then \<turnstile> c else {}"
  let ?P = "\<lambda>x. \<forall>f. (\<exists>ys. f = ?f ys \<and> ys \<in> (let f = \<turnstile> b in ?S\<^sub>1 f \<union> ?S\<^sub>2 f)) \<longrightarrow>
    f x \<noteq> Some None \<and> (f x = None \<longrightarrow> x \<in> X)"
  let ?Y = "\<lambda>A. Univ?? A {x. \<forall>f \<in> {?f ys |ys. ys \<in> \<turnstile> c}.
    f x \<noteq> Some None \<and> (f x = None \<longrightarrow> x \<in> X)}"
  {
    fix B\<^sub>1 B\<^sub>2 B\<^sub>1' B\<^sub>2'
    assume C: "\<Turnstile> b (\<subseteq> A, X) = (B\<^sub>1, B\<^sub>2)"
    assume "Some (C', Y') = (if (\<forall>s \<in> Univ? A X \<union>
      Univ? (?F B\<^sub>1 (\<turnstile> c)) (?Y B\<^sub>1). \<forall>x \<in> bvars b. All (interf s (dom x))) \<and>
      (\<forall>p \<in> U. \<forall>B W. p = (B, W) \<longrightarrow> (\<forall>s \<in> B. \<forall>x \<in> W. All (interf s (dom x))))
        then Some (B\<^sub>2 \<union> B\<^sub>2', Univ?? B\<^sub>2 X \<inter> ?Y B\<^sub>1)
        else None)"
    hence D: "Y' = Univ?? B\<^sub>2 X \<inter> ?Y B\<^sub>1"
      by (simp split: if_split_asm)
    {
      fix x
      assume "A = {}"
      hence "x \<in> Y'"
        using C and D by (simp add: btyping2_fst_empty)
    }
    moreover {
      fix x
      assume "?P x"
      {
        assume "\<turnstile> b \<noteq> Some True"
        hence "[] \<in> (let f = \<turnstile> b in ?S\<^sub>1 f \<union> ?S\<^sub>2 f)"
          by (auto simp: Let_def)
        hence "x \<in> X"
          using `?P x` by auto
      }
      hence E: "\<turnstile> b \<noteq> Some True \<longrightarrow> x \<in> Univ?? B\<^sub>2 X"
        by auto
      {
        fix ys
        assume "\<turnstile> b \<noteq> Some False" and "ys \<in> \<turnstile> c"
        hence "ys \<in> (let f = \<turnstile> b in ?S\<^sub>1 f \<union> ?S\<^sub>2 f)"
          by (auto simp: Let_def)
        hence "?f ys x \<noteq> Some None \<and> (?f ys x = None \<longrightarrow> x \<in> X)"
          using `?P x` by auto
      }
      hence F: "\<turnstile> b \<noteq> Some False \<longrightarrow> x \<in> ?Y B\<^sub>1"
        by auto
      have "x \<in> Y'"
      proof (cases "\<turnstile> b")
        case None
        thus ?thesis
          using D and E and F by simp
      next
        case (Some v)
        show ?thesis
        proof (cases v)
          case True
          with C and D and F and Some show ?thesis
            by (drule_tac btyping1_btyping2 [where A = A and X = X], simp)
        next
          case False
          with C and D and E and Some show ?thesis
            by (drule_tac btyping1_btyping2 [where A = A and X = X], simp)
        qed
      qed
    }
    ultimately have "(A = {} \<longrightarrow> UNIV \<subseteq> Y') \<and> (A \<noteq> {} \<longrightarrow> {x. ?P x} \<subseteq> Y')"
      by auto
  }
  note C = this
  from A and B show ?thesis
    by (auto intro!: C simp: ctyping1_def
     split: option.split_asm prod.split_asm)
qed

lemma ctyping1_ctyping2_snd:
 "\<lbrakk>(C, Z) = \<turnstile> c (\<subseteq> A, X); Some (C', Z') = (U, False) \<Turnstile> c (\<subseteq> A, X)\<rbrakk> \<Longrightarrow>
    Z \<subseteq> Z'"
proof (induction "(U, False)" c A X arbitrary: C C' Z Z' U
 rule: ctyping2.induct)
  fix A X C C' Z Z' U c\<^sub>1 c\<^sub>2
  show
   "\<lbrakk>\<And>B B' Y Y'.
      (B, Y) = \<turnstile> c\<^sub>1 (\<subseteq> A, X) \<Longrightarrow>
      Some (B', Y') = (U, False) \<Turnstile> c\<^sub>1 (\<subseteq> A, X) \<Longrightarrow>
      Y \<subseteq> Y';
    \<And>p B Y C C' Z Z'. (U, False) \<Turnstile> c\<^sub>1 (\<subseteq> A, X) = Some p \<Longrightarrow>
      (B, Y) = p \<Longrightarrow> (C, Z) = \<turnstile> c\<^sub>2 (\<subseteq> B, Y) \<Longrightarrow>
      Some (C', Z') = (U, False) \<Turnstile> c\<^sub>2 (\<subseteq> B, Y) \<Longrightarrow>
      Z \<subseteq> Z';
    (C, Z) = \<turnstile> c\<^sub>1;; c\<^sub>2 (\<subseteq> A, X);
    Some (C', Z') = (U, False) \<Turnstile> c\<^sub>1;; c\<^sub>2 (\<subseteq> A, X)\<rbrakk> \<Longrightarrow>
      Z \<subseteq> Z'"
    by (rule ctyping1_ctyping2_snd_seq)
next
  fix A X C C' Z Z' U b c\<^sub>1 c\<^sub>2
  show
   "\<lbrakk>\<And>U' p B\<^sub>1 B\<^sub>2 C C' Z Z'.
      (U', p) = (insert (Univ? A X, bvars b) U, \<Turnstile> b (\<subseteq> A, X)) \<Longrightarrow>
      (B\<^sub>1, B\<^sub>2) = p \<Longrightarrow> (C, Z) = \<turnstile> c\<^sub>1 (\<subseteq> B\<^sub>1, X) \<Longrightarrow>
      Some (C', Z') = (U', False) \<Turnstile> c\<^sub>1 (\<subseteq> B\<^sub>1, X) \<Longrightarrow>
      Z \<subseteq> Z';
    \<And>U' p B\<^sub>1 B\<^sub>2 C C' Z Z'.
      (U', p) = (insert (Univ? A X, bvars b) U, \<Turnstile> b (\<subseteq> A, X)) \<Longrightarrow>
      (B\<^sub>1, B\<^sub>2) = p \<Longrightarrow> (C, Z) = \<turnstile> c\<^sub>2 (\<subseteq> B\<^sub>2, X) \<Longrightarrow>
      Some (C', Z') = (U', False) \<Turnstile> c\<^sub>2 (\<subseteq> B\<^sub>2, X) \<Longrightarrow>
      Z \<subseteq> Z';
    (C, Z) = \<turnstile> IF b THEN c\<^sub>1 ELSE c\<^sub>2 (\<subseteq> A, X);
    Some (C', Z') = (U, False) \<Turnstile> IF b THEN c\<^sub>1 ELSE c\<^sub>2 (\<subseteq> A, X)\<rbrakk> \<Longrightarrow>
      Z \<subseteq> Z'"
    by (rule ctyping1_ctyping2_snd_if)
next
  fix A X B B' Z Z' U b c
  show
   "\<lbrakk>\<And>B\<^sub>1 B\<^sub>2 C Y B\<^sub>1' B\<^sub>2' B B' Z Z'.
      (B\<^sub>1, B\<^sub>2) = \<Turnstile> b (\<subseteq> A, X) \<Longrightarrow>
      (C, Y) = \<turnstile> c (\<subseteq> B\<^sub>1, X) \<Longrightarrow>
      (B\<^sub>1', B\<^sub>2') = \<Turnstile> b (\<subseteq> C, Y) \<Longrightarrow>
      \<forall>(B, W) \<in> insert (Univ? A X \<union> Univ? C Y, bvars b) U.
        B: dom ` W \<leadsto> UNIV \<Longrightarrow>
      (B, Z) = \<turnstile> c (\<subseteq> B\<^sub>1, X) \<Longrightarrow>
      Some (B', Z') = ({}, False) \<Turnstile> c (\<subseteq> B\<^sub>1, X) \<Longrightarrow>
      Z \<subseteq> Z';
    \<And>B\<^sub>1 B\<^sub>2 C Y B\<^sub>1' B\<^sub>2' B B' Z Z'.
      (B\<^sub>1, B\<^sub>2) = \<Turnstile> b (\<subseteq> A, X) \<Longrightarrow>
      (C, Y) = \<turnstile> c (\<subseteq> B\<^sub>1, X) \<Longrightarrow>
      (B\<^sub>1', B\<^sub>2') = \<Turnstile> b (\<subseteq> C, Y) \<Longrightarrow>
      \<forall>(B, W) \<in> insert (Univ? A X \<union> Univ? C Y, bvars b) U.
        B: dom ` W \<leadsto> UNIV \<Longrightarrow>
      (B, Z) = \<turnstile> c (\<subseteq> B\<^sub>1', Y) \<Longrightarrow>
      Some (B', Z') = ({}, False) \<Turnstile> c (\<subseteq> B\<^sub>1', Y) \<Longrightarrow>
      Z \<subseteq> Z';
    (B, Z) = \<turnstile> WHILE b DO c (\<subseteq> A, X);
    Some (B', Z') = (U, False) \<Turnstile> WHILE b DO c (\<subseteq> A, X)\<rbrakk> \<Longrightarrow>
      Z \<subseteq> Z'"
    by (rule ctyping1_ctyping2_snd_while)
qed (simp add: ctyping1_def, auto)


lemma ctyping1_ctyping2:
 "\<lbrakk>\<turnstile> c (\<subseteq> A, X) = (C, Z); (U, False) \<Turnstile> c (\<subseteq> A, X) = Some (C', Z')\<rbrakk> \<Longrightarrow>
    C' \<subseteq> C \<and> Z \<subseteq> Z'"
by (rule conjI, ((rule ctyping1_ctyping2_fst [OF sym sym] |
 rule ctyping1_ctyping2_snd [OF sym sym]), assumption+)+)


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
      case \<Turnstile> b (\<subseteq> C', Y') of (B\<^sub>1'', B\<^sub>2'') \<Rightarrow>
        if (\<forall>s \<in> Univ? C Y \<union> Univ? C' Y'. \<forall>x \<in> bvars b. All (interf s (dom x))) \<and>
          (\<forall>p \<in> U. case p of (B, W) \<Rightarrow> \<forall>s \<in> B. \<forall>x \<in> W. All (interf s (dom x)))
        then case ({}, False) \<Turnstile> c (\<subseteq> B\<^sub>1', Y) of
          None \<Rightarrow> None | Some _ \<Rightarrow> case ({}, False) \<Turnstile> c (\<subseteq> B\<^sub>1'', Y') of
            None \<Rightarrow> None | Some _ \<Rightarrow> Some (B\<^sub>2' \<union> B\<^sub>2'', Univ?? B\<^sub>2' Y \<inter> Y')
        else None) = Some (B, W) \<Longrightarrow>
          \<exists>r \<in> C. s\<^sub>2 = r (\<subseteq> state \<inter> Y) \<Longrightarrow> \<exists>r \<in> B. s\<^sub>3 = r (\<subseteq> state \<inter> W)"
      (is "\<And>C B Y W U. ?P C B Y W U \<Longrightarrow> _ \<Longrightarrow> _") and
    J: "\<And>A B X Y U v. (U, v) \<Turnstile> c (\<subseteq> A, X) = Some (B, Y) \<Longrightarrow>
      \<exists>r \<in> A. s\<^sub>1 = r (\<subseteq> state \<inter> X) \<Longrightarrow> \<exists>r \<in> B. s\<^sub>2 = r (\<subseteq> state \<inter> Y)" and
    K: "\<forall>s \<in> Univ? A X \<union> Univ? C Y. \<forall>x \<in> bvars b. All (interf s (dom x))" and
    L: "\<forall>p \<in> U. \<forall>B W. p  = (B, W) \<longrightarrow>
      (\<forall>s \<in> B. \<forall>x \<in> W. All (interf s (dom x)))"
  shows "\<exists>r \<in> B\<^sub>2 \<union> B\<^sub>2'. s\<^sub>3 = r (\<subseteq> state \<inter> Univ?? B\<^sub>2 X \<inter> Y)"
proof -
  obtain C' Y' where M: "(C', Y') = \<turnstile> c (\<subseteq> B\<^sub>1', Y)"
    by (cases "\<turnstile> c (\<subseteq> B\<^sub>1', Y)", simp)
  obtain B\<^sub>1'' B\<^sub>2'' where N: "(B\<^sub>1'', B\<^sub>2'') = \<Turnstile> b (\<subseteq> C', Y')"
    by (cases "\<Turnstile> b (\<subseteq> C', Y')", simp)
  let ?B = "B\<^sub>2' \<union> B\<^sub>2''"
  let ?W = "Univ?? B\<^sub>2' Y \<inter> Y'"
  have "(C, Y) = \<turnstile> c (\<subseteq> C, Y)"
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
      if (\<forall>s \<in> Univ? C Y \<union> Univ? C' Y'. \<forall>x \<in> bvars b. All (interf s (dom x))) \<and>
        (\<forall>p \<in> U. case p of (B, W) \<Rightarrow> \<forall>s \<in> B. \<forall>x \<in> W. All (interf s (dom x)))
      then case ({}, False) \<Turnstile> c (\<subseteq> B\<^sub>1', Y) of
        None \<Rightarrow> None | Some _ \<Rightarrow> case ({}, False) \<Turnstile> c (\<subseteq> B\<^sub>1'', Y') of
          None \<Rightarrow> None | Some _ \<Rightarrow> Some (B\<^sub>2' \<union> B\<^sub>2'', Univ?? B\<^sub>2' Y \<inter> Y')
      else None) = Some (B, W) \<Longrightarrow>
    \<exists>r \<in> C. s\<^sub>2 = r (\<subseteq> state \<inter> Y) \<Longrightarrow> \<exists>r \<in> B. s\<^sub>3 = r (\<subseteq> state \<inter> W);
  \<And>A B X Y U v. (U, v) \<Turnstile> c (\<subseteq> A, X) = Some (B, Y) \<Longrightarrow>
    \<exists>r \<in> A. s\<^sub>1 = r (\<subseteq> state \<inter> X) \<Longrightarrow> \<exists>r \<in> B. s\<^sub>2 = r (\<subseteq> state \<inter> Y);
  \<forall>s \<in> Univ? A X \<union> Univ? C Y. \<forall>x \<in> bvars b. All (interf s (dom x));
  \<forall>p \<in> U. \<forall>B W. p = (B, W) \<longrightarrow> (\<forall>s \<in> B. \<forall>x \<in> W. All (interf s (dom x)));
  \<forall>r \<in> B\<^sub>2 \<union> B\<^sub>2'. \<exists>x \<in> state \<inter> (X \<inter> Y). s\<^sub>3 x \<noteq> r x\<rbrakk> \<Longrightarrow>
    False"
by (drule ctyping2_approx_while_aux, assumption+, auto)

lemma ctyping2_approx:
 "\<lbrakk>(c, s) \<Rightarrow> t; (U, v) \<Turnstile> c (\<subseteq> A, X) = Some (B, Y);
    s \<in> Univ A (\<subseteq> state \<inter> X)\<rbrakk> \<Longrightarrow> t \<in> Univ B (\<subseteq> state \<inter> Y)"
proof (induction arbitrary: A B X Y U v rule: big_step_induct)
  fix A B X Y U v b c\<^sub>1 c\<^sub>2 s t
  show
   "\<lbrakk>bval b s; (c\<^sub>1, s) \<Rightarrow> t;
    \<And>A C X Y U v. (U, v) \<Turnstile> c\<^sub>1 (\<subseteq> A, X) = Some (C, Y) \<Longrightarrow>
      s \<in> Univ A (\<subseteq> state \<inter> X) \<Longrightarrow>
      t \<in> Univ C (\<subseteq> state \<inter> Y);
    (U, v) \<Turnstile> IF b THEN c\<^sub>1 ELSE c\<^sub>2 (\<subseteq> A, X) = Some (B, Y);
    s \<in> Univ A (\<subseteq> state \<inter> X)\<rbrakk> \<Longrightarrow>
      t \<in> Univ B (\<subseteq> state \<inter> Y)"
    by (auto split: option.split_asm prod.split_asm,
     rule ctyping2_approx_if_1)
next
  fix A B X Y U v b c\<^sub>1 c\<^sub>2 s t
  show
   "\<lbrakk>\<not> bval b s; (c\<^sub>2, s) \<Rightarrow> t;
    \<And>A C X Y U v. (U, v) \<Turnstile> c\<^sub>2 (\<subseteq> A, X) = Some (C, Y) \<Longrightarrow>
      s \<in> Univ A (\<subseteq> state \<inter> X) \<Longrightarrow>
      t \<in> Univ C (\<subseteq> state \<inter> Y);
    (U, v) \<Turnstile> IF b THEN c\<^sub>1 ELSE c\<^sub>2 (\<subseteq> A, X) = Some (B, Y);
    s \<in> Univ A (\<subseteq> state \<inter> X)\<rbrakk> \<Longrightarrow>
      t \<in> Univ B (\<subseteq> state \<inter> Y)"
    by (auto split: option.split_asm prod.split_asm,
     rule ctyping2_approx_if_2)
next
  fix A B X Y U v b c s\<^sub>1 s\<^sub>2 s\<^sub>3
  show
   "\<lbrakk>bval b s\<^sub>1; (c, s\<^sub>1) \<Rightarrow> s\<^sub>2;
    \<And>A B X Y U v. (U, v) \<Turnstile> c (\<subseteq> A, X) = Some (B, Y) \<Longrightarrow>
      s\<^sub>1 \<in> Univ A (\<subseteq> state \<inter> X) \<Longrightarrow>
      s\<^sub>2 \<in> Univ B (\<subseteq> state \<inter> Y);
    (WHILE b DO c, s\<^sub>2) \<Rightarrow> s\<^sub>3;
    \<And>A B X Y U v. (U, v) \<Turnstile> WHILE b DO c (\<subseteq> A, X) = Some (B, Y) \<Longrightarrow>
      s\<^sub>2 \<in> Univ A (\<subseteq> state \<inter> X) \<Longrightarrow>
      s\<^sub>3 \<in> Univ B (\<subseteq> state \<inter> Y);
    (U, v) \<Turnstile> WHILE b DO c (\<subseteq> A, X) = Some (B, Y);
    s\<^sub>1 \<in> Univ A (\<subseteq> state \<inter> X)\<rbrakk> \<Longrightarrow>
      s\<^sub>3 \<in> Univ B (\<subseteq> state \<inter> Y)"
  by (auto split: if_split_asm option.split_asm prod.split_asm,
   erule_tac [2] ctyping2_approx_while_4,
   erule ctyping2_approx_while_3)
qed (auto split: if_split_asm option.split_asm prod.split_asm)

end

end
