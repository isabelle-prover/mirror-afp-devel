(*  Title:       Extension of Stateful Intransitive Noninterference with Inputs, Outputs, and Nondeterminism in Language IMP
    Author:      Pasquale Noce
                 Senior Staff Firmware Engineer at HID Global, Italy
                 pasquale dot noce dot lavoro at gmail dot com
                 pasquale dot noce at hidglobal dot com
*)

section "Sufficiency of well-typedness for information flow correctness: main theorem"

theory Correctness_Theorem
  imports Correctness_Lemmas
begin

text \<open>
\null

The purpose of this section is to prove that type system @{const [names_short] noninterf.ctyping2}
is correct in that it guarantees that well-typed programs satisfy the information flow correctness
criterion expressed by predicate @{const [names_short] noninterf.correct}, namely that if the type
system outputs a value other than @{const None} (that is, a \emph{pass} verdict) when it is input
program @{term c}, @{typ "state set"} @{term A}, and @{typ "vname set"} @{term X}, then
@{prop "correct c A X"} (theorem @{text ctyping2_correct}).

This proof makes use of the lemma @{text ctyping2_approx} proven in a previous section.
\<close>


subsection "Local context proofs"

context noninterf
begin


lemma ctyping2_correct_aux_skip [elim!]:
 "\<lbrakk>(SKIP, s, f, vs\<^sub>0, ws\<^sub>0) \<rightarrow>*{cfs\<^sub>1} (c\<^sub>1, s\<^sub>1, f, vs\<^sub>1, ws\<^sub>1);
    (c\<^sub>1, s\<^sub>1, f, vs\<^sub>1, ws\<^sub>1) \<rightarrow>*{cfs\<^sub>2} (c\<^sub>2, s\<^sub>2, f, vs\<^sub>2, ws\<^sub>2)\<rbrakk> \<Longrightarrow>
  ok_flow_aux U c\<^sub>1 c\<^sub>2 s\<^sub>1 s\<^sub>2 f vs\<^sub>1 vs\<^sub>2 ws\<^sub>1 ws\<^sub>2 (flow cfs\<^sub>2)"
by (fastforce dest: small_stepsl_skip)

lemma ctyping2_correct_aux_assign:
  assumes
    A: "(U, v) \<Turnstile> x ::= a (\<subseteq> A, X) = Some (C, Y)" and
    B: "s \<in> Univ A (\<subseteq> state \<inter> X)" and
    C: "(x ::= a, s, f, vs\<^sub>0, ws\<^sub>0) \<rightarrow>*{cfs\<^sub>1} (c\<^sub>1, s\<^sub>1, f, vs\<^sub>1, ws\<^sub>1)" and
    D: "(c\<^sub>1, s\<^sub>1, f, vs\<^sub>1, ws\<^sub>1) \<rightarrow>*{cfs\<^sub>2} (c\<^sub>2, s\<^sub>2, f, vs\<^sub>2, ws\<^sub>2)"
  shows "ok_flow_aux U c\<^sub>1 c\<^sub>2 s\<^sub>1 s\<^sub>2 f vs\<^sub>1 vs\<^sub>2 ws\<^sub>1 ws\<^sub>2 (flow cfs\<^sub>2)"
proof -
  from A have E: "\<forall>(B, Y) \<in> insert (Univ? A X, avars a) U. B: Y \<leadsto> {x}"
    by (simp split: if_split_asm)
  have
   "(c\<^sub>1, s\<^sub>1, f, vs\<^sub>1, ws\<^sub>1) = (x ::= a, s, f, vs\<^sub>0, ws\<^sub>0) \<or>
    (c\<^sub>1, s\<^sub>1, f, vs\<^sub>1, ws\<^sub>1) = (SKIP, s(x := aval a s), f, vs\<^sub>0, ws\<^sub>0)"
    (is "?P \<or> ?Q")
    using C by (blast dest: small_stepsl_assign)
  thus ?thesis
  proof
    assume ?P
    hence "(x ::= a, s, f, vs\<^sub>0, ws\<^sub>0) \<rightarrow>*{cfs\<^sub>2} (c\<^sub>2, s\<^sub>2, f, vs\<^sub>2, ws\<^sub>2)"
      using D by simp
    hence
     "(c\<^sub>2, s\<^sub>2, f, vs\<^sub>2, ws\<^sub>2) = (x ::= a, s, f, vs\<^sub>0, ws\<^sub>0) \<and>
        flow cfs\<^sub>2 = [] \<or>
      (c\<^sub>2, s\<^sub>2, f, vs\<^sub>2, ws\<^sub>2) = (SKIP, s(x := aval a s), f, vs\<^sub>0, ws\<^sub>0) \<and>
        flow cfs\<^sub>2 = [x ::= a]"
      (is "?P' \<or> _")
      by (rule small_stepsl_assign)
    thus ?thesis
    proof (rule disjE, erule_tac [2] conjE)
      assume ?P'
      with `?P` show ?thesis
        by fastforce
    next
      assume
        F: "(c\<^sub>2, s\<^sub>2, f, vs\<^sub>2, ws\<^sub>2) = (SKIP, s(x := aval a s), f, vs\<^sub>0, ws\<^sub>0)" and
        G: "flow cfs\<^sub>2 = [x ::= a]"
          (is "?cs = _")
      show ?thesis
      proof (rule conjI, clarify)
        fix t\<^sub>1 f' vs\<^sub>1' ws\<^sub>1'
        let ?t\<^sub>2 = "t\<^sub>1(x := aval a t\<^sub>1)"
        show "\<exists>c\<^sub>2' t\<^sub>2 vs\<^sub>2' ws\<^sub>2'.
          ok_flow_aux_1 c\<^sub>1 c\<^sub>2 c\<^sub>2' s\<^sub>1 t\<^sub>1 t\<^sub>2 f f'
            vs\<^sub>1 vs\<^sub>1' vs\<^sub>2 vs\<^sub>2' ws\<^sub>1' ws\<^sub>2' ?cs \<and>
          ok_flow_aux_2 s\<^sub>1 s\<^sub>2 t\<^sub>1 t\<^sub>2 f f' vs\<^sub>1 vs\<^sub>1' ?cs \<and>
          ok_flow_aux_3 s\<^sub>1 t\<^sub>1 f f' vs\<^sub>1 vs\<^sub>1' ws\<^sub>1 ws\<^sub>1' ws\<^sub>2 ws\<^sub>2' ?cs"
        proof (rule exI [of _ SKIP], rule exI [of _ ?t\<^sub>2],
         rule exI [of _ vs\<^sub>1'], rule exI [of _ ws\<^sub>1'])
          {
            fix S
            assume "S \<subseteq> {y. s = t\<^sub>1 (\<subseteq> sources [x ::= a] vs\<^sub>0 s f y)}" and
             "x \<in> S"
            hence "s = t\<^sub>1 (\<subseteq> avars a)"
              using B by (rule eq_states_assign, insert E, simp)
            hence "aval a s = aval a t\<^sub>1"
              by (rule avars_aval)
          }
          moreover {
            fix S y
            assume "S \<subseteq> {y. s = t\<^sub>1 (\<subseteq> sources [x ::= a] vs\<^sub>0 s f y)}" and
             "y \<in> S"
            hence "s = t\<^sub>1 (\<subseteq> sources [x ::= a] vs\<^sub>0 s f y)"
              by blast
            moreover assume "y \<noteq> x"
            ultimately have "s y = t\<^sub>1 y"
              by (subst (asm) append_Nil [symmetric],
               simp only: sources.simps, simp)
          }
          ultimately show
           "ok_flow_aux_1 c\<^sub>1 c\<^sub>2 SKIP s\<^sub>1 t\<^sub>1 ?t\<^sub>2 f f'
              vs\<^sub>1 vs\<^sub>1' vs\<^sub>2 vs\<^sub>1' ws\<^sub>1' ws\<^sub>1' ?cs \<and>
            ok_flow_aux_2 s\<^sub>1 s\<^sub>2 t\<^sub>1 ?t\<^sub>2 f f' vs\<^sub>1 vs\<^sub>1' ?cs \<and>
            ok_flow_aux_3 s\<^sub>1 t\<^sub>1 f f' vs\<^sub>1 vs\<^sub>1' ws\<^sub>1 ws\<^sub>1' ws\<^sub>2 ws\<^sub>1' ?cs"
            using F and G and `?P` by auto
        qed
      qed (insert E G, fastforce)
    qed
  next
    assume ?Q
    moreover from this have
     "(c\<^sub>2, s\<^sub>2, f, vs\<^sub>2, ws\<^sub>2) = (SKIP, s\<^sub>1, f, vs\<^sub>1, ws\<^sub>1) \<and> flow cfs\<^sub>2 = []"
      using D by (blast intro!: small_stepsl_skip)
    ultimately show ?thesis
      by fastforce
  qed
qed

lemma ctyping2_correct_aux_input:
  assumes
    A: "(U, v) \<Turnstile> IN x (\<subseteq> A, X) = Some (C, Y)" and
    B: "(IN x, s, f, vs\<^sub>0, ws\<^sub>0) \<rightarrow>*{cfs\<^sub>1} (c\<^sub>1, s\<^sub>1, f, vs\<^sub>1, ws\<^sub>1)" and
    C: "(c\<^sub>1, s\<^sub>1, f, vs\<^sub>1, ws\<^sub>1) \<rightarrow>*{cfs\<^sub>2} (c\<^sub>2, s\<^sub>2, f, vs\<^sub>2, ws\<^sub>2)"
  shows "ok_flow_aux U c\<^sub>1 c\<^sub>2 s\<^sub>1 s\<^sub>2 f vs\<^sub>1 vs\<^sub>2 ws\<^sub>1 ws\<^sub>2 (flow cfs\<^sub>2)"
proof -
  from A have D: "\<forall>(B, Y) \<in> U. B: Y \<leadsto> {x}"
    by (simp split: if_split_asm)
  let ?n = "length [p\<leftarrow>vs\<^sub>0. fst p = x]"
  have
   "(c\<^sub>1, s\<^sub>1, f, vs\<^sub>1, ws\<^sub>1) = (IN x, s, f, vs\<^sub>0, ws\<^sub>0) \<or>
    (c\<^sub>1, s\<^sub>1, f, vs\<^sub>1, ws\<^sub>1) =
      (SKIP, s(x := f x ?n), f, vs\<^sub>0 @ [(x, f x ?n)], ws\<^sub>0)"
    (is "?P \<or> ?Q")
    using B by (auto dest: small_stepsl_input simp: Let_def)
  thus ?thesis
  proof
    assume ?P
    hence "(IN x, s, f, vs\<^sub>0, ws\<^sub>0) \<rightarrow>*{cfs\<^sub>2} (c\<^sub>2, s\<^sub>2, f, vs\<^sub>2, ws\<^sub>2)"
      using C by simp
    hence
     "(c\<^sub>2, s\<^sub>2, f, vs\<^sub>2, ws\<^sub>2) = (IN x, s, f, vs\<^sub>0, ws\<^sub>0) \<and>
        flow cfs\<^sub>2 = [] \<or>
      (c\<^sub>2, s\<^sub>2, f, vs\<^sub>2, ws\<^sub>2) =
        (SKIP, s(x := f x ?n), f, vs\<^sub>0 @ [(x, f x ?n)], ws\<^sub>0) \<and>
        flow cfs\<^sub>2 = [IN x]"
      (is "?P' \<or> _")
      by (auto dest: small_stepsl_input simp: Let_def)
    thus ?thesis
    proof (rule disjE, erule_tac [2] conjE)
      assume ?P'
      with `?P` show ?thesis
        by fastforce
    next
      assume
        E: "(c\<^sub>2, s\<^sub>2, f, vs\<^sub>2, ws\<^sub>2) =
          (SKIP, s(x := f x ?n), f, vs\<^sub>0 @ [(x, f x ?n)], ws\<^sub>0)" and
        F: "flow cfs\<^sub>2 = [IN x]"
          (is "?cs = _")
      show ?thesis
      proof (rule conjI, clarify)
        fix t\<^sub>1 f' vs\<^sub>1' ws\<^sub>1'
        let ?n' = "length [p\<leftarrow>vs\<^sub>1' :: inputs. fst p = x]"
        let ?t\<^sub>2 = "t\<^sub>1(x := f' x ?n') :: state" and
          ?vs\<^sub>2' = "vs\<^sub>1' @ [(x, f' x ?n')]"
        show "\<exists>c\<^sub>2' t\<^sub>2 vs\<^sub>2' ws\<^sub>2'.
          ok_flow_aux_1 c\<^sub>1 c\<^sub>2 c\<^sub>2' s\<^sub>1 t\<^sub>1 t\<^sub>2 f f'
            vs\<^sub>1 vs\<^sub>1' vs\<^sub>2 vs\<^sub>2' ws\<^sub>1' ws\<^sub>2' ?cs \<and>
          ok_flow_aux_2 s\<^sub>1 s\<^sub>2 t\<^sub>1 t\<^sub>2 f f' vs\<^sub>1 vs\<^sub>1' ?cs \<and>
          ok_flow_aux_3 s\<^sub>1 t\<^sub>1 f f' vs\<^sub>1 vs\<^sub>1' ws\<^sub>1 ws\<^sub>1' ws\<^sub>2 ws\<^sub>2' ?cs"
        proof (rule exI [of _ SKIP], rule exI [of _ ?t\<^sub>2],
         rule exI [of _ ?vs\<^sub>2'], rule exI [of _ ws\<^sub>1'])
          {
            fix S
            assume "f = f' (\<subseteq> vs\<^sub>0, vs\<^sub>1',
              \<Union> {tags [IN x] vs\<^sub>0 s f y | y. y \<in> S})"
                (is "_ = _ (\<subseteq> _, _, ?T)")
            moreover assume "x \<in> S"
            hence "tags [IN x] vs\<^sub>0 s f x \<subseteq> ?T"
              by blast
            ultimately have "f = f' (\<subseteq> vs\<^sub>0, vs\<^sub>1', tags [IN x] vs\<^sub>0 s f x)"
              by (rule eq_streams_subset)
            moreover have "tags [IN x] vs\<^sub>0 s f x = {(x, 0)}"
              by (subst append_Nil [symmetric],
               simp only: tags.simps, simp)
            ultimately have "f x (length [p\<leftarrow>vs\<^sub>0. fst p = x]) =
              f' x (length [p\<leftarrow>vs\<^sub>1'. fst p = x])"
              by (simp add: eq_streams_def)
          }
          moreover
          {
            fix S y
            assume "S \<subseteq> {y. s = t\<^sub>1 (\<subseteq> sources [IN x] vs\<^sub>0 s f y)}" and
             "y \<in> S"
            hence "s = t\<^sub>1 (\<subseteq> sources [IN x] vs\<^sub>0 s f y)"
              by blast
            moreover assume "y \<noteq> x"
            ultimately have "s y = t\<^sub>1 y"
              by (subst (asm) append_Nil [symmetric],
               simp only: sources.simps, simp)
          }
          ultimately show
           "ok_flow_aux_1 c\<^sub>1 c\<^sub>2 SKIP s\<^sub>1 t\<^sub>1 ?t\<^sub>2 f f'
              vs\<^sub>1 vs\<^sub>1' vs\<^sub>2 ?vs\<^sub>2' ws\<^sub>1' ws\<^sub>1' ?cs \<and>
            ok_flow_aux_2 s\<^sub>1 s\<^sub>2 t\<^sub>1 ?t\<^sub>2 f f' vs\<^sub>1 vs\<^sub>1' ?cs \<and>
            ok_flow_aux_3 s\<^sub>1 t\<^sub>1 f f' vs\<^sub>1 vs\<^sub>1' ws\<^sub>1 ws\<^sub>1' ws\<^sub>2 ws\<^sub>1' ?cs"
            using E and F and `?P` by auto
        qed
      qed (insert D F, fastforce)
    qed
  next
    assume ?Q
    moreover from this have
     "(c\<^sub>2, s\<^sub>2, f, vs\<^sub>2, ws\<^sub>2) = (SKIP, s\<^sub>1, f, vs\<^sub>1, ws\<^sub>1) \<and> flow cfs\<^sub>2 = []"
      using C by (blast intro!: small_stepsl_skip)
    ultimately show ?thesis
      by fastforce
  qed
qed

lemma ctyping2_correct_aux_output:
  assumes
    A: "(U, v) \<Turnstile> OUT x (\<subseteq> A, X) = Some (B, Y)" and
    B: "(OUT x, s, f, vs\<^sub>0, ws\<^sub>0) \<rightarrow>*{cfs\<^sub>1} (c\<^sub>1, s\<^sub>1, f, vs\<^sub>1, ws\<^sub>1)" and
    C: "(c\<^sub>1, s\<^sub>1, f, vs\<^sub>1, ws\<^sub>1) \<rightarrow>*{cfs\<^sub>2} (c\<^sub>2, s\<^sub>2, f, vs\<^sub>2, ws\<^sub>2)"
  shows "ok_flow_aux U c\<^sub>1 c\<^sub>2 s\<^sub>1 s\<^sub>2 f vs\<^sub>1 vs\<^sub>2 ws\<^sub>1 ws\<^sub>2 (flow cfs\<^sub>2)"
proof -
  from A have D: "\<forall>(B, Y) \<in> U. B: Y \<leadsto> {x}"
    by (simp split: if_split_asm)
  have
   "(c\<^sub>1, s\<^sub>1, f, vs\<^sub>1, ws\<^sub>1) = (OUT x, s, f, vs\<^sub>0, ws\<^sub>0) \<or>
    (c\<^sub>1, s\<^sub>1, f, vs\<^sub>1, ws\<^sub>1) = (SKIP, s, f, vs\<^sub>0, ws\<^sub>0 @ [(x, s x)])"
    (is "?P \<or> ?Q")
    using B by (blast dest: small_stepsl_output)
  thus ?thesis
  proof
    assume ?P
    hence "(OUT x, s, f, vs\<^sub>0, ws\<^sub>0) \<rightarrow>*{cfs\<^sub>2} (c\<^sub>2, s\<^sub>2, f, vs\<^sub>2, ws\<^sub>2)"
      using C by simp
    hence
     "(c\<^sub>2, s\<^sub>2, f, vs\<^sub>2, ws\<^sub>2) = (OUT x, s, f, vs\<^sub>0, ws\<^sub>0) \<and>
        flow cfs\<^sub>2 = [] \<or>
      (c\<^sub>2, s\<^sub>2, f, vs\<^sub>2, ws\<^sub>2) = (SKIP, s, f, vs\<^sub>0, ws\<^sub>0 @ [(x, s x)]) \<and>
        flow cfs\<^sub>2 = [OUT x]"
      (is "?P' \<or> _")
      by (rule small_stepsl_output)
    thus ?thesis
    proof (rule disjE, erule_tac [2] conjE)
      assume ?P'
      with `?P` show ?thesis
        by fastforce
    next
      assume
        E: "(c\<^sub>2, s\<^sub>2, f, vs\<^sub>2, ws\<^sub>2) = (SKIP, s, f, vs\<^sub>0, ws\<^sub>0 @ [(x, s x)])" and
        F: "flow cfs\<^sub>2 = [OUT x]"
          (is "?cs = _")
      show ?thesis
      proof (rule conjI, clarify)
        fix t\<^sub>1 f' vs\<^sub>1' ws\<^sub>1'
        let ?ws\<^sub>2' = "ws\<^sub>1' @ [(x, t\<^sub>1 x)] :: outputs"
        show "\<exists>c\<^sub>2' t\<^sub>2 vs\<^sub>2' ws\<^sub>2'.
          ok_flow_aux_1 c\<^sub>1 c\<^sub>2 c\<^sub>2' s\<^sub>1 t\<^sub>1 t\<^sub>2 f f'
            vs\<^sub>1 vs\<^sub>1' vs\<^sub>2 vs\<^sub>2' ws\<^sub>1' ws\<^sub>2' ?cs \<and>
          ok_flow_aux_2 s\<^sub>1 s\<^sub>2 t\<^sub>1 t\<^sub>2 f f' vs\<^sub>1 vs\<^sub>1' ?cs \<and>
          ok_flow_aux_3 s\<^sub>1 t\<^sub>1 f f' vs\<^sub>1 vs\<^sub>1' ws\<^sub>1 ws\<^sub>1' ws\<^sub>2 ws\<^sub>2' ?cs"
        proof (rule exI [of _ SKIP], rule exI [of _ t\<^sub>1],
         rule exI [of _ vs\<^sub>1'], rule exI [of _ ?ws\<^sub>2'])
          {
            fix S y
            assume "S \<subseteq> {y. s = t\<^sub>1 (\<subseteq> sources [OUT x] vs\<^sub>0 s f y)}" and
             "y \<in> S"
            hence "s = t\<^sub>1 (\<subseteq> sources [OUT x] vs\<^sub>0 s f y)"
              by blast
            hence "s y = t\<^sub>1 y"
              by (subst (asm) append_Nil [symmetric],
               simp only: sources.simps, simp)
          }
          moreover {
            fix S
            assume "S \<subseteq> {y. s = t\<^sub>1 (\<subseteq> sources_out [OUT x] vs\<^sub>0 s f y)}" and
             "x \<in> S"
            hence "s = t\<^sub>1 (\<subseteq> sources_out [OUT x] vs\<^sub>0 s f x)"
              by blast
            hence "s x = t\<^sub>1 x"
              by (subst (asm) append_Nil [symmetric],
               simp only: sources_out.simps, simp)
          }
          ultimately show
           "ok_flow_aux_1 c\<^sub>1 c\<^sub>2 SKIP s\<^sub>1 t\<^sub>1 t\<^sub>1 f f'
              vs\<^sub>1 vs\<^sub>1' vs\<^sub>2 vs\<^sub>1' ws\<^sub>1' ?ws\<^sub>2' ?cs \<and>
            ok_flow_aux_2 s\<^sub>1 s\<^sub>2 t\<^sub>1 t\<^sub>1 f f' vs\<^sub>1 vs\<^sub>1' ?cs \<and>
            ok_flow_aux_3 s\<^sub>1 t\<^sub>1 f f' vs\<^sub>1 vs\<^sub>1' ws\<^sub>1 ws\<^sub>1' ws\<^sub>2 ?ws\<^sub>2' ?cs"
            using E and F and `?P` by auto
        qed
      qed (insert D F, fastforce)
    qed
  next
    assume ?Q
    moreover from this have
     "(c\<^sub>2, s\<^sub>2, f, vs\<^sub>2, ws\<^sub>2) = (SKIP, s\<^sub>1, f, vs\<^sub>1, ws\<^sub>1) \<and> flow cfs\<^sub>2 = []"
      using C by (blast intro!: small_stepsl_skip)
    ultimately show ?thesis
      by fastforce
  qed
qed

lemma ctyping2_correct_aux_seq:
  assumes
    A: "(U, v) \<Turnstile> c\<^sub>1;; c\<^sub>2 (\<subseteq> A, X) = Some (C, Z)" and
    B: "\<And>B Y c' c'' s s\<^sub>1 s\<^sub>2 vs\<^sub>0 vs\<^sub>1 vs\<^sub>2 ws\<^sub>0 ws\<^sub>1 ws\<^sub>2 cfs\<^sub>1 cfs\<^sub>2.
      (U, v) \<Turnstile> c\<^sub>1 (\<subseteq> A, X) = Some (B, Y) \<Longrightarrow>
      s \<in> Univ A (\<subseteq> state \<inter> X) \<Longrightarrow>
      (c\<^sub>1, s, f, vs\<^sub>0, ws\<^sub>0) \<rightarrow>*{cfs\<^sub>1} (c', s\<^sub>1, f, vs\<^sub>1, ws\<^sub>1) \<Longrightarrow>
      (c', s\<^sub>1, f, vs\<^sub>1, ws\<^sub>1) \<rightarrow>*{cfs\<^sub>2} (c'', s\<^sub>2, f, vs\<^sub>2, ws\<^sub>2) \<Longrightarrow>
        ok_flow_aux U c' c'' s\<^sub>1 s\<^sub>2 f vs\<^sub>1 vs\<^sub>2 ws\<^sub>1 ws\<^sub>2 (flow cfs\<^sub>2)" and
    C: "\<And>p B Y C Z c' c'' s s\<^sub>1 s\<^sub>2 vs\<^sub>0 vs\<^sub>1 vs\<^sub>2 ws\<^sub>0 ws\<^sub>1 ws\<^sub>2 cfs\<^sub>1 cfs\<^sub>2.
      (U, v) \<Turnstile> c\<^sub>1 (\<subseteq> A, X) = Some p \<Longrightarrow> (B, Y) = p \<Longrightarrow>
      (U, v) \<Turnstile> c\<^sub>2 (\<subseteq> B, Y) = Some (C, Z) \<Longrightarrow>
      s \<in> Univ B (\<subseteq> state \<inter> Y) \<Longrightarrow>
      (c\<^sub>2, s, f, vs\<^sub>0, ws\<^sub>0) \<rightarrow>*{cfs\<^sub>1} (c', s\<^sub>1, f, vs\<^sub>1, ws\<^sub>1) \<Longrightarrow>
      (c', s\<^sub>1, f, vs\<^sub>1, ws\<^sub>1) \<rightarrow>*{cfs\<^sub>2} (c'', s\<^sub>2, f, vs\<^sub>2, ws\<^sub>2) \<Longrightarrow>
        ok_flow_aux U c' c'' s\<^sub>1 s\<^sub>2 f vs\<^sub>1 vs\<^sub>2 ws\<^sub>1 ws\<^sub>2 (flow cfs\<^sub>2)" and
    D: "s \<in> Univ A (\<subseteq> state \<inter> X)" and
    E: "(c\<^sub>1;; c\<^sub>2, s, f, vs\<^sub>0, ws\<^sub>0) \<rightarrow>*{cfs\<^sub>1} (c', s\<^sub>1, f, vs\<^sub>1, ws\<^sub>1)" and
    F: "(c', s\<^sub>1, f, vs\<^sub>1, ws\<^sub>1) \<rightarrow>*{cfs\<^sub>2} (c'', s\<^sub>2, f, vs\<^sub>2, ws\<^sub>2)"
  shows "ok_flow_aux U c' c'' s\<^sub>1 s\<^sub>2 f vs\<^sub>1 vs\<^sub>2 ws\<^sub>1 ws\<^sub>2 (flow cfs\<^sub>2)"
proof -
  from A obtain B and Y where
    G: "(U, v) \<Turnstile> c\<^sub>1 (\<subseteq> A, X) = Some (B, Y)" and
    H: "(U, v) \<Turnstile> c\<^sub>2 (\<subseteq> B, Y) = Some (C, Z)"
    by (auto split: option.split_asm)
  have
   "(\<exists>c cfs. c' = c;; c\<^sub>2 \<and>
      (c\<^sub>1, s, f, vs\<^sub>0, ws\<^sub>0) \<rightarrow>*{cfs} (c, s\<^sub>1, f, vs\<^sub>1, ws\<^sub>1)) \<or>
    (\<exists>s' p cfs cfs'.
      (c\<^sub>1, s, f, vs\<^sub>0, ws\<^sub>0) \<rightarrow>*{cfs} (SKIP, s', p) \<and>
      (c\<^sub>2, s', p) \<rightarrow>*{cfs'} (c', s\<^sub>1, f, vs\<^sub>1, ws\<^sub>1))"
    using E by (fastforce dest: small_stepsl_seq)
  thus ?thesis
  proof (rule disjE, (erule_tac exE)+, (erule_tac [2] exE)+,
   erule_tac [!] conjE)
    fix c\<^sub>1' cfs
    assume
      I: "c' = c\<^sub>1';; c\<^sub>2" and
      J: "(c\<^sub>1, s, f, vs\<^sub>0, ws\<^sub>0) \<rightarrow>*{cfs} (c\<^sub>1', s\<^sub>1, f, vs\<^sub>1, ws\<^sub>1)"
    hence "(c\<^sub>1';; c\<^sub>2, s\<^sub>1, f, vs\<^sub>1, ws\<^sub>1) \<rightarrow>*{cfs\<^sub>2} (c'', s\<^sub>2, f, vs\<^sub>2, ws\<^sub>2)"
      using F by simp
    hence
     "(\<exists>d cfs'. c'' = d;; c\<^sub>2 \<and>
        (c\<^sub>1', s\<^sub>1, f, vs\<^sub>1, ws\<^sub>1) \<rightarrow>*{cfs'} (d, s\<^sub>2, f, vs\<^sub>2, ws\<^sub>2) \<and>
        flow cfs\<^sub>2 = flow cfs') \<or>
      (\<exists>p cfs' cfs''.
        (c\<^sub>1', s\<^sub>1, f, vs\<^sub>1, ws\<^sub>1) \<rightarrow>*{cfs'} (SKIP, p) \<and>
        (c\<^sub>2, p) \<rightarrow>*{cfs''} (c'', s\<^sub>2, f, vs\<^sub>2, ws\<^sub>2) \<and>
        flow cfs\<^sub>2 = flow cfs' @ flow cfs'')"
      by (blast dest: small_stepsl_seq)
    thus ?thesis
    proof (rule disjE, (erule_tac exE)+, (erule_tac [2] exE)+,
     (erule_tac [!] conjE)+)
      fix c\<^sub>1'' cfs'
      assume
        K: "c'' = c\<^sub>1'';; c\<^sub>2" and
        L: "(c\<^sub>1', s\<^sub>1, f, vs\<^sub>1, ws\<^sub>1) \<rightarrow>*{cfs'} (c\<^sub>1'', s\<^sub>2, f, vs\<^sub>2, ws\<^sub>2)" and
        M: "flow cfs\<^sub>2 = flow cfs'"
          (is "?cs = ?cs'")
      have N: "ok_flow_aux U c\<^sub>1' c\<^sub>1'' s\<^sub>1 s\<^sub>2 f vs\<^sub>1 vs\<^sub>2 ws\<^sub>1 ws\<^sub>2 ?cs'"
        using B [OF G D J L] .
      show ?thesis
      proof (rule conjI, clarify)
        fix t\<^sub>1 f' vs\<^sub>1' ws\<^sub>1'
        obtain c\<^sub>2' and t\<^sub>2 and vs\<^sub>2' and ws\<^sub>2' where
         "ok_flow_aux_1 c\<^sub>1' c\<^sub>1'' c\<^sub>2' s\<^sub>1 t\<^sub>1 t\<^sub>2 f f'
            vs\<^sub>1 vs\<^sub>1' vs\<^sub>2 vs\<^sub>2' ws\<^sub>1' ws\<^sub>2' ?cs \<and>
          ok_flow_aux_2 s\<^sub>1 s\<^sub>2 t\<^sub>1 t\<^sub>2 f f' vs\<^sub>1 vs\<^sub>1' ?cs \<and>
          ok_flow_aux_3 s\<^sub>1 t\<^sub>1 f f' vs\<^sub>1 vs\<^sub>1' ws\<^sub>1 ws\<^sub>1' ws\<^sub>2 ws\<^sub>2' ?cs"
          (is "?P1 \<and> ?P2 \<and> ?P3")
          using M and N by fastforce
        hence ?P1 and ?P2 and ?P3 by auto
        show "\<exists>c\<^sub>2' t\<^sub>2 vs\<^sub>2' ws\<^sub>2'.
          ok_flow_aux_1 c' c'' c\<^sub>2' s\<^sub>1 t\<^sub>1 t\<^sub>2 f f'
            vs\<^sub>1 vs\<^sub>1' vs\<^sub>2 vs\<^sub>2' ws\<^sub>1' ws\<^sub>2' ?cs \<and>
          ok_flow_aux_2 s\<^sub>1 s\<^sub>2 t\<^sub>1 t\<^sub>2 f f' vs\<^sub>1 vs\<^sub>1' ?cs \<and>
          ok_flow_aux_3 s\<^sub>1 t\<^sub>1 f f' vs\<^sub>1 vs\<^sub>1' ws\<^sub>1 ws\<^sub>1' ws\<^sub>2 ws\<^sub>2' ?cs"
        proof (rule exI [of _ "c\<^sub>2';; c\<^sub>2"], rule exI [of _ t\<^sub>2],
         rule exI [of _ vs\<^sub>2'], rule exI [of _ ws\<^sub>2'])
          {
            fix S
            assume "S \<noteq> {}" and
             "S \<subseteq> {x. s\<^sub>1 = t\<^sub>1 (\<subseteq> sources_aux ?cs vs\<^sub>1 s\<^sub>1 f x)}" and
             "f = f' (\<subseteq> vs\<^sub>1, vs\<^sub>1', \<Union> {tags_aux ?cs vs\<^sub>1 s\<^sub>1 f x | x. x \<in> S})"
            hence
             "(c', t\<^sub>1, f', vs\<^sub>1', ws\<^sub>1') \<rightarrow>* (c\<^sub>2';; c\<^sub>2, t\<^sub>2, f', vs\<^sub>2', ws\<^sub>2') \<and>
              map fst [p\<leftarrow>drop (length vs\<^sub>1) vs\<^sub>2. fst p \<in> S] =
                map fst [p\<leftarrow>drop (length vs\<^sub>1') vs\<^sub>2'. fst p \<in> S]"
              using I and `?P1` by (blast intro: star_seq2)
          }
          thus
           "ok_flow_aux_1 c' c'' (c\<^sub>2';; c\<^sub>2) s\<^sub>1 t\<^sub>1 t\<^sub>2 f f'
              vs\<^sub>1 vs\<^sub>1' vs\<^sub>2 vs\<^sub>2' ws\<^sub>1' ws\<^sub>2' ?cs \<and>
            ok_flow_aux_2 s\<^sub>1 s\<^sub>2 t\<^sub>1 t\<^sub>2 f f' vs\<^sub>1 vs\<^sub>1' ?cs \<and>
            ok_flow_aux_3 s\<^sub>1 t\<^sub>1 f f' vs\<^sub>1 vs\<^sub>1' ws\<^sub>1 ws\<^sub>1' ws\<^sub>2 ws\<^sub>2' ?cs"
            using K and `?P2` and `?P3` by simp
        qed
      qed (simp add: M N)
    next
      fix p cfs' cfs''
      assume "(c\<^sub>1', s\<^sub>1, f, vs\<^sub>1, ws\<^sub>1) \<rightarrow>*{cfs'} (SKIP, p)"
      moreover from this obtain s\<^sub>1' and vs and ws where
        K: "p = (s\<^sub>1', f, vs, ws)"
        by (blast dest: small_stepsl_stream)
      ultimately have
        L: "(c\<^sub>1', s\<^sub>1, f, vs\<^sub>1, ws\<^sub>1) \<rightarrow>*{cfs'} (SKIP, s\<^sub>1', f, vs, ws)"
        by simp
      assume "(c\<^sub>2, p) \<rightarrow>*{cfs''} (c'', s\<^sub>2, f, vs\<^sub>2, ws\<^sub>2)"
      with K have
        M: "(c\<^sub>2, s\<^sub>1', f, vs, ws) \<rightarrow>*{cfs''} (c'', s\<^sub>2, f, vs\<^sub>2, ws\<^sub>2)"
        by simp
      assume N: "flow cfs\<^sub>2 = flow cfs' @ flow cfs''"
        (is "(?cs :: flow) = ?cs' @ ?cs''")
      have O: "ok_flow_aux U c\<^sub>1' SKIP s\<^sub>1 s\<^sub>1' f vs\<^sub>1 vs ws\<^sub>1 ws ?cs'"
        using B [OF G D J L] .
      have "(c\<^sub>1, s, f, vs\<^sub>0, ws\<^sub>0) \<rightarrow>*{cfs @ cfs'} (SKIP, s\<^sub>1', f, vs, ws)"
        using J and L by (simp add: small_stepsl_append)
      hence "(c\<^sub>1, s, f, vs\<^sub>0, ws\<^sub>0) \<Rightarrow> (s\<^sub>1', f, vs, ws)"
        by (auto dest: small_stepsl_steps simp: big_iff_small)
      hence P: "s\<^sub>1' \<in> Univ B (\<subseteq> state \<inter> Y)"
        using G and D by (rule ctyping2_approx)
      have Q: "ok_flow_aux U c\<^sub>2 c'' s\<^sub>1' s\<^sub>2 f vs vs\<^sub>2 ws ws\<^sub>2 ?cs''"
        using C [OF G _ H P _ M, of vs ws "[]"] by simp
      show ?thesis
      proof (rule conjI, clarify)
        fix t\<^sub>1 f' vs\<^sub>1' ws\<^sub>1'
        obtain c\<^sub>1'' and t\<^sub>1' and vs\<^sub>1'' and ws\<^sub>1'' where
         "ok_flow_aux_1 c\<^sub>1' SKIP c\<^sub>1'' s\<^sub>1 t\<^sub>1 t\<^sub>1' f f'
            vs\<^sub>1 vs\<^sub>1' vs vs\<^sub>1'' ws\<^sub>1' ws\<^sub>1'' ?cs' \<and>
          ok_flow_aux_2 s\<^sub>1 s\<^sub>1' t\<^sub>1 t\<^sub>1' f f' vs\<^sub>1 vs\<^sub>1' ?cs' \<and>
          ok_flow_aux_3 s\<^sub>1 t\<^sub>1 f f' vs\<^sub>1 vs\<^sub>1' ws\<^sub>1 ws\<^sub>1' ws ws\<^sub>1'' ?cs'"
          (is "_ \<and> ?P2 \<and> ?P3")
          using O by fastforce
        hence
         "ok_flow_aux_1 c\<^sub>1' SKIP SKIP s\<^sub>1 t\<^sub>1 t\<^sub>1' f f'
            vs\<^sub>1 vs\<^sub>1' vs vs\<^sub>1'' ws\<^sub>1' ws\<^sub>1'' ?cs'"
          (is ?P1) and ?P2 and ?P3 by auto
        obtain c\<^sub>2' and t\<^sub>2 and vs\<^sub>2' and ws\<^sub>2' where
         "ok_flow_aux_1 c\<^sub>2 c'' c\<^sub>2' s\<^sub>1' t\<^sub>1' t\<^sub>2 f f'
            vs vs\<^sub>1'' vs\<^sub>2 vs\<^sub>2' ws\<^sub>1'' ws\<^sub>2' ?cs'' \<and>
          ok_flow_aux_2 s\<^sub>1' s\<^sub>2 t\<^sub>1' t\<^sub>2 f f' vs vs\<^sub>1'' ?cs'' \<and>
          ok_flow_aux_3 s\<^sub>1' t\<^sub>1' f f' vs vs\<^sub>1'' ws ws\<^sub>1'' ws\<^sub>2 ws\<^sub>2' ?cs''"
          (is "?P1' \<and> ?P2' \<and> ?P3'")
          using Q by fastforce
        hence ?P1' and ?P2' and ?P3' by auto
        show "\<exists>c\<^sub>2' t\<^sub>2 vs\<^sub>2' ws\<^sub>2'.
          ok_flow_aux_1 c' c'' c\<^sub>2' s\<^sub>1 t\<^sub>1 t\<^sub>2 f f'
            vs\<^sub>1 vs\<^sub>1' vs\<^sub>2 vs\<^sub>2' ws\<^sub>1' ws\<^sub>2' ?cs \<and>
          ok_flow_aux_2 s\<^sub>1 s\<^sub>2 t\<^sub>1 t\<^sub>2 f f' vs\<^sub>1 vs\<^sub>1' ?cs \<and>
          ok_flow_aux_3 s\<^sub>1 t\<^sub>1 f f' vs\<^sub>1 vs\<^sub>1' ws\<^sub>1 ws\<^sub>1' ws\<^sub>2 ws\<^sub>2' ?cs"
        proof (rule exI [of _ c\<^sub>2'], rule exI [of _ t\<^sub>2],
         rule exI [of _ vs\<^sub>2'], rule exI [of _ ws\<^sub>2'])
          {
            fix S
            assume
              R: "S \<noteq> {}" and
              S: "S \<subseteq> {x. s\<^sub>1 = t\<^sub>1 (\<subseteq> sources_aux (?cs' @ ?cs'') vs\<^sub>1 s\<^sub>1 f x)}" and
              T: "f = f' (\<subseteq> vs\<^sub>1, vs\<^sub>1',
                \<Union> {tags_aux (?cs' @ ?cs'') vs\<^sub>1 s\<^sub>1 f x | x. x \<in> S})"
                (is "_ = _ (\<subseteq> _, _, ?T)")
            have "\<forall>x. sources_aux ?cs' vs\<^sub>1 s\<^sub>1 f x \<subseteq>
              sources_aux (?cs' @ ?cs'') vs\<^sub>1 s\<^sub>1 f x"
              by (blast intro: subsetD [OF sources_aux_append])
            hence "S \<subseteq> {x. s\<^sub>1 = t\<^sub>1 (\<subseteq> sources_aux ?cs' vs\<^sub>1 s\<^sub>1 f x)}"
              using S by blast
            moreover have "\<Union> {tags_aux ?cs' vs\<^sub>1 s\<^sub>1 f x | x. x \<in> S} \<subseteq> ?T"
              (is "?T' \<subseteq> _")
              by (blast intro: subsetD [OF tags_aux_append])
            with T have "f = f' (\<subseteq> vs\<^sub>1, vs\<^sub>1', ?T')"
              by (rule eq_streams_subset)
            ultimately have
             "(c\<^sub>1', t\<^sub>1, f', vs\<^sub>1', ws\<^sub>1') \<rightarrow>* (SKIP, t\<^sub>1', f', vs\<^sub>1'', ws\<^sub>1'') \<and>
              map fst [p\<leftarrow>drop (length vs\<^sub>1) vs. fst p \<in> S] =
                map fst [p\<leftarrow>drop (length vs\<^sub>1') vs\<^sub>1''. fst p \<in> S]"
              (is "?Q1 \<and> ?Q2")
              using R and `?P1` by simp
            hence ?Q1 and ?Q2 by auto
            have "S \<subseteq> {x. s\<^sub>1' = t\<^sub>1' (\<subseteq> sources_aux ?cs'' vs s\<^sub>1' f x)}"
              by (rule sources_aux_rhs [OF S T L `?P2`])
            moreover have "f = f' (\<subseteq> vs, vs\<^sub>1'',
              \<Union> {tags_aux ?cs'' vs s\<^sub>1' f x | x. x \<in> S})"
              by (rule tags_aux_rhs [OF S T L `?Q1` `?P1`])
            ultimately have
             "(c\<^sub>2, t\<^sub>1', f', vs\<^sub>1'', ws\<^sub>1'') \<rightarrow>* (c\<^sub>2', t\<^sub>2, f', vs\<^sub>2', ws\<^sub>2') \<and>
              (c'' = SKIP) = (c\<^sub>2' = SKIP) \<and>
              map fst [p\<leftarrow>drop (length vs) vs\<^sub>2. fst p \<in> S] =
                map fst [p\<leftarrow>drop (length vs\<^sub>1'') vs\<^sub>2'. fst p \<in> S]"
              (is "?Q1' \<and> ?R2 \<and> ?Q2'")
              using R and `?P1'` by simp
            hence ?Q1' and ?R2 and ?Q2' by auto
            from I and `?Q1` and `?Q1'` have
             "(c', t\<^sub>1, f', vs\<^sub>1', ws\<^sub>1') \<rightarrow>* (c\<^sub>2', t\<^sub>2, f', vs\<^sub>2', ws\<^sub>2')"
              (is ?R1)
              by (blast intro: star_seq2 star_trans)
            moreover have
             "map fst [p\<leftarrow>drop (length vs\<^sub>1) vs\<^sub>2. fst p \<in> S] =
                map fst [p\<leftarrow>drop (length vs\<^sub>1') vs\<^sub>2'. fst p \<in> S]"
              by (rule small_steps_inputs [OF L M `?Q1` `?Q1'` `?Q2` `?Q2'`])
            ultimately have "?R1 \<and> ?R2 \<and> ?this"
              using `?R2` by simp
          }
          moreover {
            fix S
            assume
              R: "S \<noteq> {}" and
              S: "S \<subseteq> {x. s\<^sub>1 = t\<^sub>1 (\<subseteq> sources (?cs' @ ?cs'') vs\<^sub>1 s\<^sub>1 f x)}" and
              T: "f = f' (\<subseteq> vs\<^sub>1, vs\<^sub>1',
                \<Union> {tags (?cs' @ ?cs'') vs\<^sub>1 s\<^sub>1 f x | x. x \<in> S})"
                (is "_ = _ (\<subseteq> _, _, ?T)")
            have "\<forall>x. sources_aux (?cs' @ ?cs'') vs\<^sub>1 s\<^sub>1 f x \<subseteq>
              sources (?cs' @ ?cs'') vs\<^sub>1 s\<^sub>1 f x"
              by (blast intro: subsetD [OF sources_aux_sources])
            moreover have "\<forall>x. sources_aux ?cs' vs\<^sub>1 s\<^sub>1 f x \<subseteq>
              sources_aux (?cs' @ ?cs'') vs\<^sub>1 s\<^sub>1 f x"
              by (blast intro: subsetD [OF sources_aux_append])
            ultimately have U: "S \<subseteq> {x. s\<^sub>1 = t\<^sub>1 (\<subseteq> sources_aux ?cs' vs\<^sub>1 s\<^sub>1 f x)}"
              using S by blast
            have "\<Union> {tags_aux (?cs' @ ?cs'') vs\<^sub>1 s\<^sub>1 f x | x. x \<in> S} \<subseteq> ?T"
              (is "?T' \<subseteq> _")
              by (blast intro: subsetD [OF tags_aux_tags])
            moreover have "\<Union> {tags_aux ?cs' vs\<^sub>1 s\<^sub>1 f x | x. x \<in> S} \<subseteq> ?T'"
              (is "?T'' \<subseteq> _")
              by (blast intro: subsetD [OF tags_aux_append])
            ultimately have "?T'' \<subseteq> ?T"
              by simp
            with T have "f = f' (\<subseteq> vs\<^sub>1, vs\<^sub>1', ?T'')"
              by (rule eq_streams_subset)
            hence V: "(c\<^sub>1', t\<^sub>1, f', vs\<^sub>1', ws\<^sub>1') \<rightarrow>* (SKIP, t\<^sub>1', f', vs\<^sub>1'', ws\<^sub>1'')"
              using R and U and `?P1` by simp
            have "S \<subseteq> {x. s\<^sub>1' = t\<^sub>1' (\<subseteq> sources ?cs'' vs s\<^sub>1' f x)}"
              by (rule sources_rhs [OF S T L `?P2`])
            moreover have "f = f' (\<subseteq> vs, vs\<^sub>1'',
              \<Union> {tags ?cs'' vs s\<^sub>1' f x | x. x \<in> S})"
              by (rule tags_rhs [OF S T L V `?P1`])
            ultimately have "s\<^sub>2 = t\<^sub>2 (\<subseteq> S)"
              using `?P2'` by blast
          }
          moreover {
            fix S
            assume
              R: "S \<noteq> {}" and
              S: "S \<subseteq> {x. s\<^sub>1 = t\<^sub>1 (\<subseteq> sources_out (?cs' @ ?cs'') vs\<^sub>1 s\<^sub>1 f x)}" and
              T: "f = f' (\<subseteq> vs\<^sub>1, vs\<^sub>1',
                \<Union> {tags_out (?cs' @ ?cs'') vs\<^sub>1 s\<^sub>1 f x | x. x \<in> S})"
                (is "_ = _ (\<subseteq> _, _, ?T)")
            have U: "\<forall>x. sources_aux (?cs' @ ?cs'') vs\<^sub>1 s\<^sub>1 f x \<subseteq>
              sources_out (?cs' @ ?cs'') vs\<^sub>1 s\<^sub>1 f x"
              by (blast intro: subsetD [OF sources_aux_sources_out])
            moreover have "\<forall>x. sources_aux ?cs' vs\<^sub>1 s\<^sub>1 f x \<subseteq>
              sources_aux (?cs' @ ?cs'') vs\<^sub>1 s\<^sub>1 f x"
              by (blast intro: subsetD [OF sources_aux_append])
            ultimately have V: "S \<subseteq> {x. s\<^sub>1 = t\<^sub>1 (\<subseteq> sources_aux ?cs' vs\<^sub>1 s\<^sub>1 f x)}"
              using S by blast
            have W: "\<Union> {tags_aux (?cs' @ ?cs'') vs\<^sub>1 s\<^sub>1 f x | x. x \<in> S} \<subseteq> ?T"
              (is "?T' \<subseteq> _")
              by (blast intro: subsetD [OF tags_aux_tags_out])
            moreover have "\<Union> {tags_aux ?cs' vs\<^sub>1 s\<^sub>1 f x | x. x \<in> S} \<subseteq> ?T'"
              (is "?T'' \<subseteq> _")
              by (blast intro: subsetD [OF tags_aux_append])
            ultimately have "?T'' \<subseteq> ?T"
              by simp
            with T have "f = f' (\<subseteq> vs\<^sub>1, vs\<^sub>1', ?T'')"
              by (rule eq_streams_subset)
            hence X: "(c\<^sub>1', t\<^sub>1, f', vs\<^sub>1', ws\<^sub>1') \<rightarrow>* (SKIP, t\<^sub>1', f', vs\<^sub>1'', ws\<^sub>1'')"
              using R and V and `?P1` by simp
            have Y: "S \<subseteq> {x. s\<^sub>1 = t\<^sub>1 (\<subseteq> sources_aux (?cs' @ ?cs'') vs\<^sub>1 s\<^sub>1 f x)}"
              using S and U by blast
            have Z: "f = f' (\<subseteq> vs\<^sub>1, vs\<^sub>1', ?T')"
              using T and W by (rule eq_streams_subset)
            have "S \<subseteq> {x. s\<^sub>1' = t\<^sub>1' (\<subseteq> sources_aux ?cs'' vs s\<^sub>1' f x)}"
              by (rule sources_aux_rhs [OF Y Z L `?P2`])
            moreover have "f = f' (\<subseteq> vs, vs\<^sub>1'',
              \<Union> {tags_aux ?cs'' vs s\<^sub>1' f x | x. x \<in> S})"
              by (rule tags_aux_rhs [OF Y Z L X `?P1`])
            ultimately have AA:
             "(c\<^sub>2, t\<^sub>1', f', vs\<^sub>1'', ws\<^sub>1'') \<rightarrow>* (c\<^sub>2', t\<^sub>2, f', vs\<^sub>2', ws\<^sub>2')"
              using R and `?P1'` by simp
            have "\<forall>x. sources_out ?cs' vs\<^sub>1 s\<^sub>1 f x \<subseteq>
              sources_out (?cs' @ ?cs'') vs\<^sub>1 s\<^sub>1 f x"
              by (blast intro: subsetD [OF sources_out_append])
            hence "S \<subseteq> {x. s\<^sub>1 = t\<^sub>1 (\<subseteq> sources_out ?cs' vs\<^sub>1 s\<^sub>1 f x)}"
              using S by blast
            moreover have "\<Union> {tags_out ?cs' vs\<^sub>1 s\<^sub>1 f x | x. x \<in> S} \<subseteq> ?T"
              (is "?T' \<subseteq> _")
              by (blast intro: subsetD [OF tags_out_append])
            with T have "f = f' (\<subseteq> vs\<^sub>1, vs\<^sub>1', ?T')"
              by (rule eq_streams_subset)
            ultimately have AB: "[p\<leftarrow>drop (length ws\<^sub>1) ws. fst p \<in> S] =
              [p\<leftarrow>drop (length ws\<^sub>1') ws\<^sub>1''. fst p \<in> S]"
              using R and `?P3` by simp
            have "S \<subseteq> {x. s\<^sub>1' = t\<^sub>1' (\<subseteq> sources_out ?cs'' vs s\<^sub>1' f x)}"
              by (rule sources_out_rhs [OF S T L `?P2`])
            moreover have "f = f' (\<subseteq> vs, vs\<^sub>1'',
              \<Union> {tags_out ?cs'' vs s\<^sub>1' f x | x. x \<in> S})"
              by (rule tags_out_rhs [OF S T L X `?P1`])
            ultimately have "[p\<leftarrow>drop (length ws) ws\<^sub>2. fst p \<in> S] =
              [p\<leftarrow>drop (length ws\<^sub>1'') ws\<^sub>2'. fst p \<in> S]"
              using R and `?P3'` by simp
            hence "[p\<leftarrow>drop (length ws\<^sub>1) ws\<^sub>2. fst p \<in> S] =
              [p\<leftarrow>drop (length ws\<^sub>1') ws\<^sub>2'. fst p \<in> S]"
              by (rule small_steps_outputs [OF L M X AA AB])
          }
          ultimately show
           "ok_flow_aux_1 c' c'' c\<^sub>2' s\<^sub>1 t\<^sub>1 t\<^sub>2 f f'
              vs\<^sub>1 vs\<^sub>1' vs\<^sub>2 vs\<^sub>2' ws\<^sub>1' ws\<^sub>2' ?cs \<and>
            ok_flow_aux_2 s\<^sub>1 s\<^sub>2 t\<^sub>1 t\<^sub>2 f f' vs\<^sub>1 vs\<^sub>1' ?cs \<and>
            ok_flow_aux_3 s\<^sub>1 t\<^sub>1 f f' vs\<^sub>1 vs\<^sub>1' ws\<^sub>1 ws\<^sub>1' ws\<^sub>2 ws\<^sub>2' ?cs"
            using N by auto
        qed
      qed (simp add: no_upd_append N O Q)
    qed
  next
    fix s' p cfs cfs'
    assume I: "(c\<^sub>1, s, f, vs\<^sub>0, ws\<^sub>0) \<rightarrow>*{cfs} (SKIP, s', p)"
    hence "(c\<^sub>1, s, f, vs\<^sub>0, ws\<^sub>0) \<Rightarrow> (s', p)"
      by (auto dest: small_stepsl_steps simp: big_iff_small)
    hence J: "s' \<in> Univ B (\<subseteq> state \<inter> Y)"
      using G and D by (rule ctyping2_approx)
    assume "(c\<^sub>2, s', p) \<rightarrow>*{cfs'} (c', s\<^sub>1, f, vs\<^sub>1, ws\<^sub>1)"
    moreover obtain vs and ws where "p = (f, vs, ws)"
      using I by (blast dest: small_stepsl_stream)
    ultimately have K: "(c\<^sub>2, s', f, vs, ws) \<rightarrow>*{cfs'} (c', s\<^sub>1, f, vs\<^sub>1, ws\<^sub>1)"
      by simp
    show ?thesis
      using C [OF G _ H J K F] by simp
  qed
qed

lemma ctyping2_correct_aux_or:
  assumes
    A: "(U, v) \<Turnstile> c\<^sub>1 OR c\<^sub>2 (\<subseteq> A, X) = Some (C, Y)" and
    B: "\<And>C Y c' c'' s s\<^sub>1 s\<^sub>2 vs\<^sub>0 vs\<^sub>1 vs\<^sub>2 ws\<^sub>0 ws\<^sub>1 ws\<^sub>2 cfs\<^sub>1 cfs\<^sub>2.
      (U, v) \<Turnstile> c\<^sub>1 (\<subseteq> A, X) = Some (C, Y) \<Longrightarrow>
      s \<in> Univ A (\<subseteq> state \<inter> X) \<Longrightarrow>
      (c\<^sub>1, s, f, vs\<^sub>0, ws\<^sub>0) \<rightarrow>*{cfs\<^sub>1} (c', s\<^sub>1, f, vs\<^sub>1, ws\<^sub>1) \<Longrightarrow>
      (c', s\<^sub>1, f, vs\<^sub>1, ws\<^sub>1) \<rightarrow>*{cfs\<^sub>2} (c'', s\<^sub>2, f, vs\<^sub>2, ws\<^sub>2) \<Longrightarrow>
        ok_flow_aux U c' c'' s\<^sub>1 s\<^sub>2 f vs\<^sub>1 vs\<^sub>2 ws\<^sub>1 ws\<^sub>2 (flow cfs\<^sub>2)" and
    C: "\<And>C Y c' c'' s s\<^sub>1 s\<^sub>2 vs\<^sub>0 vs\<^sub>1 vs\<^sub>2 ws\<^sub>0 ws\<^sub>1 ws\<^sub>2 cfs\<^sub>1 cfs\<^sub>2.
      (U, v) \<Turnstile> c\<^sub>2 (\<subseteq> A, X) = Some (C, Y) \<Longrightarrow>
      s \<in> Univ A (\<subseteq> state \<inter> X) \<Longrightarrow>
      (c\<^sub>2, s, f, vs\<^sub>0, ws\<^sub>0) \<rightarrow>*{cfs\<^sub>1} (c', s\<^sub>1, f, vs\<^sub>1, ws\<^sub>1) \<Longrightarrow>
      (c', s\<^sub>1, f, vs\<^sub>1, ws\<^sub>1) \<rightarrow>*{cfs\<^sub>2} (c'', s\<^sub>2, f, vs\<^sub>2, ws\<^sub>2) \<Longrightarrow>
        ok_flow_aux U c' c'' s\<^sub>1 s\<^sub>2 f vs\<^sub>1 vs\<^sub>2 ws\<^sub>1 ws\<^sub>2 (flow cfs\<^sub>2)" and
    D: "s \<in> Univ A (\<subseteq> state \<inter> X)" and
    E: "(c\<^sub>1 OR c\<^sub>2, s, f, vs\<^sub>0, ws\<^sub>0) \<rightarrow>*{cfs\<^sub>1} (c', s\<^sub>1, f, vs\<^sub>1, ws\<^sub>1)" and
    F: "(c', s\<^sub>1, f, vs\<^sub>1, ws\<^sub>1) \<rightarrow>*{cfs\<^sub>2} (c'', s\<^sub>2, f, vs\<^sub>2, ws\<^sub>2)"
  shows "ok_flow_aux U c' c'' s\<^sub>1 s\<^sub>2 f vs\<^sub>1 vs\<^sub>2 ws\<^sub>1 ws\<^sub>2 (flow cfs\<^sub>2)"
proof -
  from A obtain C\<^sub>1 and Y\<^sub>1 and C\<^sub>2 and Y\<^sub>2 where
    G: "(U, v) \<Turnstile> c\<^sub>1 (\<subseteq> A, X) = Some (C\<^sub>1, Y\<^sub>1)" and
    H: "(U, v) \<Turnstile> c\<^sub>2 (\<subseteq> A, X) = Some (C\<^sub>2, Y\<^sub>2)"
    by (auto split: option.split_asm)
  have
   "(c', s\<^sub>1, f, vs\<^sub>1, ws\<^sub>1) = (c\<^sub>1 OR c\<^sub>2, s, f, vs\<^sub>0, ws\<^sub>0) \<or>
    (c\<^sub>1, s, f, vs\<^sub>0, ws\<^sub>0) \<rightarrow>*{tl cfs\<^sub>1} (c', s\<^sub>1, f, vs\<^sub>1, ws\<^sub>1) \<or>
    (c\<^sub>2, s, f, vs\<^sub>0, ws\<^sub>0) \<rightarrow>*{tl cfs\<^sub>1} (c', s\<^sub>1, f, vs\<^sub>1, ws\<^sub>1)"
    (is "?P \<or> ?Q \<or> ?R")
    using E by (blast dest: small_stepsl_or)
  thus ?thesis
  proof (rule disjE, erule_tac [2] disjE)
    assume ?P
    hence "(c\<^sub>1 OR c\<^sub>2, s, f, vs\<^sub>0, ws\<^sub>0) \<rightarrow>*{cfs\<^sub>2} (c'', s\<^sub>2, f, vs\<^sub>2, ws\<^sub>2)"
      using F by simp
    hence
     "(c'', s\<^sub>2, f, vs\<^sub>2, ws\<^sub>2) = (c\<^sub>1 OR c\<^sub>2, s, f, vs\<^sub>0, ws\<^sub>0) \<and>
        flow cfs\<^sub>2 = [] \<or>
      (c\<^sub>1, s, f, vs\<^sub>0, ws\<^sub>0) \<rightarrow>*{tl cfs\<^sub>2} (c'', s\<^sub>2, f, vs\<^sub>2, ws\<^sub>2) \<and>
        flow cfs\<^sub>2 = flow (tl cfs\<^sub>2) \<or>
      (c\<^sub>2, s, f, vs\<^sub>0, ws\<^sub>0) \<rightarrow>*{tl cfs\<^sub>2} (c'', s\<^sub>2, f, vs\<^sub>2, ws\<^sub>2) \<and>
        flow cfs\<^sub>2 = flow (tl cfs\<^sub>2)"
      (is "?P' \<or> _")
      by (rule small_stepsl_or)
    thus ?thesis
    proof (rule disjE, erule_tac [2] disjE, erule_tac [2-3] conjE)
      assume ?P'
      with `?P` show ?thesis
        by fastforce
    next
      assume
        I: "(c\<^sub>1, s, f, vs\<^sub>0, ws\<^sub>0) \<rightarrow>*{tl cfs\<^sub>2} (c'', s\<^sub>2, f, vs\<^sub>2, ws\<^sub>2)" and
        J: "flow cfs\<^sub>2 = flow (tl cfs\<^sub>2)"
          (is "?cs = ?cs'")
      have K: "(c\<^sub>1, s, f, vs\<^sub>0, ws\<^sub>0) \<rightarrow>*{[]} (c\<^sub>1, s, f, vs\<^sub>0, ws\<^sub>0)"
        by simp
      hence L: "ok_flow_aux U c\<^sub>1 c'' s s\<^sub>2 f vs\<^sub>0 vs\<^sub>2 ws\<^sub>0 ws\<^sub>2 ?cs'"
        by (rule B [OF G D _ I])
      show ?thesis
      proof (rule conjI, clarify)
        fix t\<^sub>1 f' vs\<^sub>1' ws\<^sub>1'
        obtain c\<^sub>2' and t\<^sub>2 and vs\<^sub>2' and ws\<^sub>2' where
         "ok_flow_aux_1 c\<^sub>1 c'' c\<^sub>2' s t\<^sub>1 t\<^sub>2 f f'
            vs\<^sub>0 vs\<^sub>1' vs\<^sub>2 vs\<^sub>2' ws\<^sub>1' ws\<^sub>2' ?cs' \<and>
          ok_flow_aux_2 s s\<^sub>2 t\<^sub>1 t\<^sub>2 f f' vs\<^sub>0 vs\<^sub>1' ?cs' \<and>
          ok_flow_aux_3 s t\<^sub>1 f f' vs\<^sub>0 vs\<^sub>1' ws\<^sub>0 ws\<^sub>1' ws\<^sub>2 ws\<^sub>2' ?cs'"
          (is "?P1 \<and> ?P2 \<and> ?P3")
          using L by fastforce
        hence ?P1 and ?P2 and ?P3 by auto
        show "\<exists>c\<^sub>2' t\<^sub>2 vs\<^sub>2' ws\<^sub>2'.
          ok_flow_aux_1 c' c'' c\<^sub>2' s\<^sub>1 t\<^sub>1 t\<^sub>2 f f'
            vs\<^sub>1 vs\<^sub>1' vs\<^sub>2 vs\<^sub>2' ws\<^sub>1' ws\<^sub>2' ?cs \<and>
          ok_flow_aux_2 s\<^sub>1 s\<^sub>2 t\<^sub>1 t\<^sub>2 f f' vs\<^sub>1 vs\<^sub>1' ?cs \<and>
          ok_flow_aux_3 s\<^sub>1 t\<^sub>1 f f' vs\<^sub>1 vs\<^sub>1' ws\<^sub>1 ws\<^sub>1' ws\<^sub>2 ws\<^sub>2' ?cs"
        proof (rule exI [of _ "c\<^sub>2'"], rule exI [of _ t\<^sub>2],
         rule exI [of _ vs\<^sub>2'], rule exI [of _ ws\<^sub>2'])
          {
            fix S
            assume
             "S \<noteq> {}" and
             "S \<subseteq> {x. s\<^sub>1 = t\<^sub>1 (\<subseteq> sources_aux ?cs' vs\<^sub>1 s\<^sub>1 f x)}" and
             "f = f' (\<subseteq> vs\<^sub>1, vs\<^sub>1', \<Union> {tags_aux ?cs' vs\<^sub>1 s\<^sub>1 f x | x. x \<in> S})"
            hence
             "(c\<^sub>1, t\<^sub>1, f', vs\<^sub>1', ws\<^sub>1') \<rightarrow>* (c\<^sub>2', t\<^sub>2, f', vs\<^sub>2', ws\<^sub>2') \<and>
              (c'' = SKIP) = (c\<^sub>2' = SKIP) \<and>
              map fst [p\<leftarrow>drop (length vs\<^sub>1) vs\<^sub>2. fst p \<in> S] =
                map fst [p\<leftarrow>drop (length vs\<^sub>1') vs\<^sub>2'. fst p \<in> S]"
              (is "?Q1 \<and> ?Q2 \<and> ?Q3")
              using `?P` and `?P1` by simp
            hence ?Q1 and ?Q2 and ?Q3 by auto
            moreover have "(c\<^sub>1 OR c\<^sub>2, t\<^sub>1, f', vs\<^sub>1', ws\<^sub>1') \<rightarrow>
              (c\<^sub>1, t\<^sub>1, f', vs\<^sub>1', ws\<^sub>1')" ..
            hence "(c', t\<^sub>1, f', vs\<^sub>1', ws\<^sub>1') \<rightarrow>* (c\<^sub>2', t\<^sub>2, f', vs\<^sub>2', ws\<^sub>2')"
              using `?P` and `?Q1` by (blast intro: star_trans)
            ultimately have "?this \<and> ?Q2 \<and> ?Q3"
              by simp
          }
          moreover {
            fix S
            assume
             "S \<subseteq> {x. s\<^sub>1 = t\<^sub>1 (\<subseteq> sources ?cs' vs\<^sub>1 s\<^sub>1 f x)}" and
             "f = f' (\<subseteq> vs\<^sub>1, vs\<^sub>1', \<Union> {tags ?cs' vs\<^sub>1 s\<^sub>1 f x | x. x \<in> S})"
            hence "s\<^sub>2 = t\<^sub>2 (\<subseteq> S)"
              using `?P` and `?P2` by blast
          }
          moreover {
            fix S
            assume
             "S \<noteq> {}" and
             "S \<subseteq> {x. s\<^sub>1 = t\<^sub>1 (\<subseteq> sources_out ?cs' vs\<^sub>1 s\<^sub>1 f x)}" and
             "f = f' (\<subseteq> vs\<^sub>1, vs\<^sub>1', \<Union> {tags_out ?cs' vs\<^sub>1 s\<^sub>1 f x | x. x \<in> S})"
            hence "[p\<leftarrow>drop (length ws\<^sub>1) ws\<^sub>2. fst p \<in> S] =
              [p\<leftarrow>drop (length ws\<^sub>1') ws\<^sub>2'. fst p \<in> S]"
              using `?P` and `?P3` by simp
          }
          ultimately show
           "ok_flow_aux_1 c' c'' c\<^sub>2' s\<^sub>1 t\<^sub>1 t\<^sub>2 f f'
              vs\<^sub>1 vs\<^sub>1' vs\<^sub>2 vs\<^sub>2' ws\<^sub>1' ws\<^sub>2' ?cs \<and>
            ok_flow_aux_2 s\<^sub>1 s\<^sub>2 t\<^sub>1 t\<^sub>2 f f' vs\<^sub>1 vs\<^sub>1' ?cs \<and>
            ok_flow_aux_3 s\<^sub>1 t\<^sub>1 f f' vs\<^sub>1 vs\<^sub>1' ws\<^sub>1 ws\<^sub>1' ws\<^sub>2 ws\<^sub>2' ?cs"
            using J by auto
        qed
      qed (simp add: B [OF G D K I] J)
    next
      assume
        I: "(c\<^sub>2, s, f, vs\<^sub>0, ws\<^sub>0) \<rightarrow>*{tl cfs\<^sub>2} (c'', s\<^sub>2, f, vs\<^sub>2, ws\<^sub>2)" and
        J: "flow cfs\<^sub>2 = flow (tl cfs\<^sub>2)"
          (is "?cs = ?cs'")
      have K: "(c\<^sub>2, s, f, vs\<^sub>0, ws\<^sub>0) \<rightarrow>*{[]} (c\<^sub>2, s, f, vs\<^sub>0, ws\<^sub>0)"
        by simp
      hence L: "ok_flow_aux U c\<^sub>2 c'' s s\<^sub>2 f vs\<^sub>0 vs\<^sub>2 ws\<^sub>0 ws\<^sub>2 ?cs'"
        by (rule C [OF H D _ I])
      show ?thesis
      proof (rule conjI, clarify)
        fix t\<^sub>1 f' vs\<^sub>1' ws\<^sub>1'
        obtain c\<^sub>2' and t\<^sub>2 and vs\<^sub>2' and ws\<^sub>2' where
         "ok_flow_aux_1 c\<^sub>2 c'' c\<^sub>2' s t\<^sub>1 t\<^sub>2 f f'
            vs\<^sub>0 vs\<^sub>1' vs\<^sub>2 vs\<^sub>2' ws\<^sub>1' ws\<^sub>2' ?cs' \<and>
          ok_flow_aux_2 s s\<^sub>2 t\<^sub>1 t\<^sub>2 f f' vs\<^sub>0 vs\<^sub>1' ?cs' \<and>
          ok_flow_aux_3 s t\<^sub>1 f f' vs\<^sub>0 vs\<^sub>1' ws\<^sub>0 ws\<^sub>1' ws\<^sub>2 ws\<^sub>2' ?cs'"
          (is "?P1 \<and> ?P2 \<and> ?P3")
          using L by fastforce
        hence ?P1 and ?P2 and ?P3 by auto
        show "\<exists>c\<^sub>2' t\<^sub>2 vs\<^sub>2' ws\<^sub>2'.
          ok_flow_aux_1 c' c'' c\<^sub>2' s\<^sub>1 t\<^sub>1 t\<^sub>2 f f'
            vs\<^sub>1 vs\<^sub>1' vs\<^sub>2 vs\<^sub>2' ws\<^sub>1' ws\<^sub>2' ?cs \<and>
          ok_flow_aux_2 s\<^sub>1 s\<^sub>2 t\<^sub>1 t\<^sub>2 f f' vs\<^sub>1 vs\<^sub>1' ?cs \<and>
          ok_flow_aux_3 s\<^sub>1 t\<^sub>1 f f' vs\<^sub>1 vs\<^sub>1' ws\<^sub>1 ws\<^sub>1' ws\<^sub>2 ws\<^sub>2' ?cs"
        proof (rule exI [of _ "c\<^sub>2'"], rule exI [of _ t\<^sub>2],
         rule exI [of _ vs\<^sub>2'], rule exI [of _ ws\<^sub>2'])
          {
            fix S
            assume
             "S \<noteq> {}" and
             "S \<subseteq> {x. s\<^sub>1 = t\<^sub>1 (\<subseteq> sources_aux ?cs' vs\<^sub>1 s\<^sub>1 f x)}" and
             "f = f' (\<subseteq> vs\<^sub>1, vs\<^sub>1', \<Union> {tags_aux ?cs' vs\<^sub>1 s\<^sub>1 f x | x. x \<in> S})"
            hence
             "(c\<^sub>2, t\<^sub>1, f', vs\<^sub>1', ws\<^sub>1') \<rightarrow>* (c\<^sub>2', t\<^sub>2, f', vs\<^sub>2', ws\<^sub>2') \<and>
              (c'' = SKIP) = (c\<^sub>2' = SKIP) \<and>
              map fst [p\<leftarrow>drop (length vs\<^sub>1) vs\<^sub>2. fst p \<in> S] =
                map fst [p\<leftarrow>drop (length vs\<^sub>1') vs\<^sub>2'. fst p \<in> S]"
              (is "?Q1 \<and> ?Q2 \<and> ?Q3")
              using `?P` and `?P1` by simp
            hence ?Q1 and ?Q2 and ?Q3 by auto
            moreover have "(c\<^sub>1 OR c\<^sub>2, t\<^sub>1, f', vs\<^sub>1', ws\<^sub>1') \<rightarrow>
              (c\<^sub>2, t\<^sub>1, f', vs\<^sub>1', ws\<^sub>1')" ..
            hence "(c', t\<^sub>1, f', vs\<^sub>1', ws\<^sub>1') \<rightarrow>* (c\<^sub>2', t\<^sub>2, f', vs\<^sub>2', ws\<^sub>2')"
              using `?P` and `?Q1` by (blast intro: star_trans)
            ultimately have "?this \<and> ?Q2 \<and> ?Q3"
              by simp
          }
          moreover {
            fix S
            assume
             "S \<subseteq> {x. s\<^sub>1 = t\<^sub>1 (\<subseteq> sources ?cs' vs\<^sub>1 s\<^sub>1 f x)}" and
             "f = f' (\<subseteq> vs\<^sub>1, vs\<^sub>1', \<Union> {tags ?cs' vs\<^sub>1 s\<^sub>1 f x | x. x \<in> S})"
            hence "s\<^sub>2 = t\<^sub>2 (\<subseteq> S)"
              using `?P` and `?P2` by blast
          }
          moreover {
            fix S
            assume
             "S \<noteq> {}" and
             "S \<subseteq> {x. s\<^sub>1 = t\<^sub>1 (\<subseteq> sources_out ?cs' vs\<^sub>1 s\<^sub>1 f x)}" and
             "f = f' (\<subseteq> vs\<^sub>1, vs\<^sub>1', \<Union> {tags_out ?cs' vs\<^sub>1 s\<^sub>1 f x | x. x \<in> S})"
            hence "[p\<leftarrow>drop (length ws\<^sub>1) ws\<^sub>2. fst p \<in> S] =
              [p\<leftarrow>drop (length ws\<^sub>1') ws\<^sub>2'. fst p \<in> S]"
              using `?P` and `?P3` by simp
          }
          ultimately show
           "ok_flow_aux_1 c' c'' c\<^sub>2' s\<^sub>1 t\<^sub>1 t\<^sub>2 f f'
              vs\<^sub>1 vs\<^sub>1' vs\<^sub>2 vs\<^sub>2' ws\<^sub>1' ws\<^sub>2' ?cs \<and>
            ok_flow_aux_2 s\<^sub>1 s\<^sub>2 t\<^sub>1 t\<^sub>2 f f' vs\<^sub>1 vs\<^sub>1' ?cs \<and>
            ok_flow_aux_3 s\<^sub>1 t\<^sub>1 f f' vs\<^sub>1 vs\<^sub>1' ws\<^sub>1 ws\<^sub>1' ws\<^sub>2 ws\<^sub>2' ?cs"
            using J by auto
        qed
      qed (simp add: C [OF H D K I] J)
    qed
  next
    assume ?Q
    thus ?thesis
      by (rule B [OF G D _ F])
  next
    assume ?R
    thus ?thesis
      by (rule C [OF H D _ F])
  qed
qed

lemma ctyping2_correct_aux_if:
  assumes
    A: "(U, v) \<Turnstile> IF b THEN c\<^sub>1 ELSE c\<^sub>2 (\<subseteq> A, X) = Some (C, Y)" and
    B: "\<And>U' p B\<^sub>1 B\<^sub>2 C\<^sub>1 Y\<^sub>1 c' c'' s s\<^sub>1 s\<^sub>2 vs\<^sub>0 vs\<^sub>1 vs\<^sub>2 ws\<^sub>0 ws\<^sub>1 ws\<^sub>2 cfs\<^sub>1 cfs\<^sub>2.
      (U', p) = (insert (Univ? A X, bvars b) U, \<Turnstile> b (\<subseteq> A, X)) \<Longrightarrow>
      (B\<^sub>1, B\<^sub>2) = p \<Longrightarrow>
      (U', v) \<Turnstile> c\<^sub>1 (\<subseteq> B\<^sub>1, X) = Some (C\<^sub>1, Y\<^sub>1) \<Longrightarrow>
      s \<in> Univ B\<^sub>1 (\<subseteq> state \<inter> X) \<Longrightarrow>
      (c\<^sub>1, s, f, vs\<^sub>0, ws\<^sub>0) \<rightarrow>*{cfs\<^sub>1} (c', s\<^sub>1, f, vs\<^sub>1, ws\<^sub>1) \<Longrightarrow>
      (c', s\<^sub>1, f, vs\<^sub>1, ws\<^sub>1) \<rightarrow>*{cfs\<^sub>2} (c'', s\<^sub>2, f, vs\<^sub>2, ws\<^sub>2) \<Longrightarrow>
        ok_flow_aux U' c' c'' s\<^sub>1 s\<^sub>2 f vs\<^sub>1 vs\<^sub>2 ws\<^sub>1 ws\<^sub>2 (flow cfs\<^sub>2)" and
    C: "\<And>U' p B\<^sub>1 B\<^sub>2 C\<^sub>2 Y\<^sub>2 c' c'' s s\<^sub>1 s\<^sub>2 vs\<^sub>0 vs\<^sub>1 vs\<^sub>2 ws\<^sub>0 ws\<^sub>1 ws\<^sub>2 cfs\<^sub>1 cfs\<^sub>2.
      (U', p) = (insert (Univ? A X, bvars b) U, \<Turnstile> b (\<subseteq> A, X)) \<Longrightarrow>
      (B\<^sub>1, B\<^sub>2) = p \<Longrightarrow>
      (U', v) \<Turnstile> c\<^sub>2 (\<subseteq> B\<^sub>2, X) = Some (C\<^sub>2, Y\<^sub>2) \<Longrightarrow>
      s \<in> Univ B\<^sub>2 (\<subseteq> state \<inter> X) \<Longrightarrow>
      (c\<^sub>2, s, f, vs\<^sub>0, ws\<^sub>0) \<rightarrow>*{cfs\<^sub>1} (c', s\<^sub>1, f, vs\<^sub>1, ws\<^sub>1) \<Longrightarrow>
      (c', s\<^sub>1, f, vs\<^sub>1, ws\<^sub>1) \<rightarrow>*{cfs\<^sub>2} (c'', s\<^sub>2, f, vs\<^sub>2, ws\<^sub>2) \<Longrightarrow>
        ok_flow_aux U' c' c'' s\<^sub>1 s\<^sub>2 f vs\<^sub>1 vs\<^sub>2 ws\<^sub>1 ws\<^sub>2 (flow cfs\<^sub>2)" and
    D: "s \<in> Univ A (\<subseteq> state \<inter> X)" and
    E: "(IF b THEN c\<^sub>1 ELSE c\<^sub>2, s, f, vs\<^sub>0, ws\<^sub>0) \<rightarrow>*{cfs\<^sub>1}
      (c', s\<^sub>1, f, vs\<^sub>1, ws\<^sub>1)" and
    F: "(c', s\<^sub>1, f, vs\<^sub>1, ws\<^sub>1) \<rightarrow>*{cfs\<^sub>2} (c'', s\<^sub>2, f, vs\<^sub>2, ws\<^sub>2)"
  shows "ok_flow_aux U c' c'' s\<^sub>1 s\<^sub>2 f vs\<^sub>1 vs\<^sub>2 ws\<^sub>1 ws\<^sub>2 (flow cfs\<^sub>2)"
proof -
  let ?U' = "insert (Univ? A X, bvars b) U"
  from A obtain B\<^sub>1 and B\<^sub>2 and C\<^sub>1 and C\<^sub>2 and Y\<^sub>1 and Y\<^sub>2 where
    G: "\<Turnstile> b (\<subseteq> A, X) = (B\<^sub>1, B\<^sub>2)" and
    H: "(?U', v) \<Turnstile> c\<^sub>1 (\<subseteq> B\<^sub>1, X) = Some (C\<^sub>1, Y\<^sub>1)" and
    I: "(?U', v) \<Turnstile> c\<^sub>2 (\<subseteq> B\<^sub>2, X) = Some (C\<^sub>2, Y\<^sub>2)"
    by (auto split: option.split_asm prod.split_asm)
  have
   "(c', s\<^sub>1, f, vs\<^sub>1, ws\<^sub>1) = (IF b THEN c\<^sub>1 ELSE c\<^sub>2, s, f, vs\<^sub>0, ws\<^sub>0) \<or>
    bval b s \<and> (c\<^sub>1, s, f, vs\<^sub>0, ws\<^sub>0) \<rightarrow>*{tl cfs\<^sub>1} (c', s\<^sub>1, f, vs\<^sub>1, ws\<^sub>1) \<or>
    \<not> bval b s \<and> (c\<^sub>2, s, f, vs\<^sub>0, ws\<^sub>0) \<rightarrow>*{tl cfs\<^sub>1} (c', s\<^sub>1, f, vs\<^sub>1, ws\<^sub>1)"
    (is "?P \<or> _")
    using E by (blast dest: small_stepsl_if)
  thus ?thesis
  proof (rule disjE, erule_tac [2] disjE, erule_tac [2-3] conjE)
    assume ?P
    hence "(IF b THEN c\<^sub>1 ELSE c\<^sub>2, s, f, vs\<^sub>0, ws\<^sub>0) \<rightarrow>*{cfs\<^sub>2}
      (c'', s\<^sub>2, f, vs\<^sub>2, ws\<^sub>2)"
      using F by simp
    hence
     "(c'', s\<^sub>2, f, vs\<^sub>2, ws\<^sub>2) = (IF b THEN c\<^sub>1 ELSE c\<^sub>2, s, f, vs\<^sub>0, ws\<^sub>0) \<and>
        flow cfs\<^sub>2 = [] \<or>
      bval b s \<and> (c\<^sub>1, s, f, vs\<^sub>0, ws\<^sub>0) \<rightarrow>*{tl cfs\<^sub>2} (c'', s\<^sub>2, f, vs\<^sub>2, ws\<^sub>2) \<and>
        flow cfs\<^sub>2 = \<langle>bvars b\<rangle> # flow (tl cfs\<^sub>2) \<or>
      \<not> bval b s \<and> (c\<^sub>2, s, f, vs\<^sub>0, ws\<^sub>0) \<rightarrow>*{tl cfs\<^sub>2} (c'', s\<^sub>2, f, vs\<^sub>2, ws\<^sub>2) \<and>
        flow cfs\<^sub>2 = \<langle>bvars b\<rangle> # flow (tl cfs\<^sub>2)"
      (is "?P' \<or> _")
      by (rule small_stepsl_if)
    thus ?thesis
    proof (rule disjE, erule_tac [2] disjE, (erule_tac [2-3] conjE)+)
      assume ?P'
      with `?P` show ?thesis
        by fastforce
    next
      assume
        J: "bval b s" and
        K: "(c\<^sub>1, s, f, vs\<^sub>0, ws\<^sub>0) \<rightarrow>*{tl cfs\<^sub>2} (c'', s\<^sub>2, f, vs\<^sub>2, ws\<^sub>2)" and
        L: "flow cfs\<^sub>2 = \<langle>bvars b\<rangle> # flow (tl cfs\<^sub>2)"
          (is "?cs = _ # ?cs'")
      have M: "s \<in> Univ B\<^sub>1 (\<subseteq> state \<inter> X)"
        using J by (insert btyping2_approx [OF G D], simp)
      have N: "(c\<^sub>1, s, f, vs\<^sub>0, ws\<^sub>0) \<rightarrow>*{[]} (c\<^sub>1, s, f, vs\<^sub>0, ws\<^sub>0)"
        by simp
      show ?thesis
      proof (rule conjI, clarify)
        fix t\<^sub>1 f' vs\<^sub>1' ws\<^sub>1'
        show "\<exists>c\<^sub>2' t\<^sub>2 vs\<^sub>2' ws\<^sub>2'.
          ok_flow_aux_1 c' c'' c\<^sub>2' s\<^sub>1 t\<^sub>1 t\<^sub>2 f f'
            vs\<^sub>1 vs\<^sub>1' vs\<^sub>2 vs\<^sub>2' ws\<^sub>1' ws\<^sub>2' ?cs \<and>
          ok_flow_aux_2 s\<^sub>1 s\<^sub>2 t\<^sub>1 t\<^sub>2 f f' vs\<^sub>1 vs\<^sub>1' ?cs \<and>
          ok_flow_aux_3 s\<^sub>1 t\<^sub>1 f f' vs\<^sub>1 vs\<^sub>1' ws\<^sub>1 ws\<^sub>1' ws\<^sub>2 ws\<^sub>2' ?cs"
        proof (cases "bval b t\<^sub>1")
          assume O: "bval b t\<^sub>1"
          have "ok_flow_aux ?U' c\<^sub>1 c'' s s\<^sub>2 f vs\<^sub>0 vs\<^sub>2 ws\<^sub>0 ws\<^sub>2 ?cs'"
            using B [OF _ _ H M N K] and G by simp
          then obtain c\<^sub>2' and t\<^sub>2 and vs\<^sub>2' and ws\<^sub>2' where
           "ok_flow_aux_1 c\<^sub>1 c'' c\<^sub>2' s t\<^sub>1 t\<^sub>2 f f'
              vs\<^sub>0 vs\<^sub>1' vs\<^sub>2 vs\<^sub>2' ws\<^sub>1' ws\<^sub>2' ?cs' \<and>
            ok_flow_aux_2 s s\<^sub>2 t\<^sub>1 t\<^sub>2 f f' vs\<^sub>0 vs\<^sub>1' ?cs' \<and>
            ok_flow_aux_3 s t\<^sub>1 f f' vs\<^sub>0 vs\<^sub>1' ws\<^sub>0 ws\<^sub>1' ws\<^sub>2 ws\<^sub>2' ?cs'"
            (is "?P1 \<and> ?P2 \<and> ?P3")
            by fastforce
          hence ?P1 and ?P2 and ?P3 by auto
          show ?thesis
          proof (rule exI [of _ c\<^sub>2'], rule exI [of _ t\<^sub>2],
           rule exI [of _ vs\<^sub>2'], rule exI [of _ ws\<^sub>2'])
            {
              fix S
              assume
                P: "S \<noteq> {}" and
                Q: "S \<subseteq> {x. s\<^sub>1 = t\<^sub>1
                  (\<subseteq> sources_aux (\<langle>bvars b\<rangle> # ?cs') vs\<^sub>1 s\<^sub>1 f x)}" and
                R: "f = f' (\<subseteq> vs\<^sub>1, vs\<^sub>1',
                  \<Union> {tags_aux (\<langle>bvars b\<rangle> # ?cs') vs\<^sub>1 s\<^sub>1 f x | x. x \<in> S})"
              have "\<forall>x. sources_aux ?cs' vs\<^sub>1 s\<^sub>1 f x \<subseteq>
                sources_aux (\<langle>bvars b\<rangle> # ?cs') vs\<^sub>1 s\<^sub>1 f x"
                by (blast intro: subsetD [OF sources_aux_observe_tl])
              hence "S \<subseteq> {x. s\<^sub>1 = t\<^sub>1 (\<subseteq> sources_aux ?cs' vs\<^sub>1 s\<^sub>1 f x)}"
                using Q by blast
              moreover have "f = f' (\<subseteq> vs\<^sub>1, vs\<^sub>1',
                \<Union> {tags_aux ?cs' vs\<^sub>1 s\<^sub>1 f x | x. x \<in> S})"
                using R by (simp add: tags_aux_observe_tl)
              ultimately have
               "(c\<^sub>1, t\<^sub>1, f', vs\<^sub>1', ws\<^sub>1') \<rightarrow>* (c\<^sub>2', t\<^sub>2, f', vs\<^sub>2', ws\<^sub>2') \<and>
                (c'' = SKIP) = (c\<^sub>2' = SKIP) \<and>
                map fst [p\<leftarrow>drop (length vs\<^sub>1) vs\<^sub>2. fst p \<in> S] =
                  map fst [p\<leftarrow>drop (length vs\<^sub>1') vs\<^sub>2'. fst p \<in> S]"
                (is "?Q1 \<and> ?Q2 \<and> ?Q3")
                using P and `?P` and `?P1` by simp
              hence ?Q1 and ?Q2 and ?Q3 by auto
              moreover have "(IF b THEN c\<^sub>1 ELSE c\<^sub>2, t\<^sub>1, f', vs\<^sub>1', ws\<^sub>1') \<rightarrow>
                (c\<^sub>1, t\<^sub>1, f', vs\<^sub>1', ws\<^sub>1')"
                using O ..
              hence "(c', t\<^sub>1, f', vs\<^sub>1', ws\<^sub>1') \<rightarrow>* (c\<^sub>2', t\<^sub>2, f', vs\<^sub>2', ws\<^sub>2')"
                using `?P` and `?Q1` by (blast intro: star_trans)
              ultimately have "?this \<and> ?Q2 \<and> ?Q3"
                by simp
            }
            moreover {
              fix S
              assume
                P: "S \<subseteq> {x. s\<^sub>1 = t\<^sub>1
                  (\<subseteq> sources (\<langle>bvars b\<rangle> # ?cs') vs\<^sub>1 s\<^sub>1 f x)}" and
                Q: "f = f' (\<subseteq> vs\<^sub>1, vs\<^sub>1',
                  \<Union> {tags (\<langle>bvars b\<rangle> # ?cs') vs\<^sub>1 s\<^sub>1 f x | x. x \<in> S})"
              have "\<forall>x. sources ?cs' vs\<^sub>1 s\<^sub>1 f x \<subseteq>
                sources (\<langle>bvars b\<rangle> # ?cs') vs\<^sub>1 s\<^sub>1 f x"
                by (blast intro: subsetD [OF sources_observe_tl])
              hence "S \<subseteq> {x. s\<^sub>1 = t\<^sub>1 (\<subseteq> sources ?cs' vs\<^sub>1 s\<^sub>1 f x)}"
                using P by blast
              moreover have "f = f' (\<subseteq> vs\<^sub>1, vs\<^sub>1',
                \<Union> {tags ?cs' vs\<^sub>1 s\<^sub>1 f x | x. x \<in> S})"
                using Q by (simp add: tags_observe_tl)
              ultimately have "s\<^sub>2 = t\<^sub>2 (\<subseteq> S)"
                using `?P` and `?P2` by blast
            }
            moreover {
              fix S
              assume
                P: "S \<noteq> {}" and
                Q: "S \<subseteq> {x. s\<^sub>1 = t\<^sub>1
                  (\<subseteq> sources_out (\<langle>bvars b\<rangle> # ?cs') vs\<^sub>1 s\<^sub>1 f x)}" and
                R: "f = f' (\<subseteq> vs\<^sub>1, vs\<^sub>1',
                  \<Union> {tags_out (\<langle>bvars b\<rangle> # ?cs') vs\<^sub>1 s\<^sub>1 f x | x. x \<in> S})"
              have "\<forall>x. sources_out ?cs' vs\<^sub>1 s\<^sub>1 f x \<subseteq>
                sources_out (\<langle>bvars b\<rangle> # ?cs') vs\<^sub>1 s\<^sub>1 f x"
                by (blast intro: subsetD [OF sources_out_observe_tl])
              hence "S \<subseteq> {x. s\<^sub>1 = t\<^sub>1 (\<subseteq> sources_out ?cs' vs\<^sub>1 s\<^sub>1 f x)}"
                using Q by blast
              moreover have "f = f' (\<subseteq> vs\<^sub>1, vs\<^sub>1',
                \<Union> {tags_out ?cs' vs\<^sub>1 s\<^sub>1 f x | x. x \<in> S})"
                using R by (simp add: tags_out_observe_tl)
              ultimately have "[p\<leftarrow>drop (length ws\<^sub>1) ws\<^sub>2. fst p \<in> S] =
                [p\<leftarrow>drop (length ws\<^sub>1') ws\<^sub>2'. fst p \<in> S]"
                using P and `?P` and `?P3` by simp
            }
            ultimately show
             "ok_flow_aux_1 c' c'' c\<^sub>2' s\<^sub>1 t\<^sub>1 t\<^sub>2 f f'
                vs\<^sub>1 vs\<^sub>1' vs\<^sub>2 vs\<^sub>2' ws\<^sub>1' ws\<^sub>2' ?cs \<and>
              ok_flow_aux_2 s\<^sub>1 s\<^sub>2 t\<^sub>1 t\<^sub>2 f f' vs\<^sub>1 vs\<^sub>1' ?cs \<and>
              ok_flow_aux_3 s\<^sub>1 t\<^sub>1 f f' vs\<^sub>1 vs\<^sub>1' ws\<^sub>1 ws\<^sub>1' ws\<^sub>2 ws\<^sub>2' ?cs"
              using L by auto
          qed
        next
          assume O: "\<not> bval b t\<^sub>1"
          show ?thesis
          proof (cases "\<exists>S \<noteq> {}. S \<subseteq> {x. s\<^sub>1 = t\<^sub>1
           (\<subseteq> sources_aux (\<langle>bvars b\<rangle> # ?cs') vs\<^sub>1 s\<^sub>1 f x)}")
            from O have "(IF b THEN c\<^sub>1 ELSE c\<^sub>2, t\<^sub>1, f', vs\<^sub>1', ws\<^sub>1') \<rightarrow>
              (c\<^sub>2, t\<^sub>1, f', vs\<^sub>1', ws\<^sub>1')" ..
            moreover assume "\<exists>S \<noteq> {}. S \<subseteq> {x. s\<^sub>1 = t\<^sub>1
              (\<subseteq> sources_aux (\<langle>bvars b\<rangle> # ?cs') vs\<^sub>1 s\<^sub>1 f x)}"
            then obtain S where
              P: "S \<noteq> {}" and
              Q: "S \<subseteq> {x. s = t\<^sub>1
                (\<subseteq> sources_aux (\<langle>bvars b\<rangle> # ?cs') vs\<^sub>1 s f x)}"
              using `?P` by blast
            have R: "Univ? A X: bvars b \<leadsto>| S"
              using Q and D by (rule sources_aux_bval, insert J O, simp)
            have "\<exists>p. (c\<^sub>2, t\<^sub>1, f', vs\<^sub>1', ws\<^sub>1') \<Rightarrow> p"
              using I by (rule ctyping2_term, insert P R, auto)
            then obtain t\<^sub>2 and f'' and vs\<^sub>2' and ws\<^sub>2' where
              S: "(c\<^sub>2, t\<^sub>1, f', vs\<^sub>1', ws\<^sub>1') \<rightarrow>* (SKIP, t\<^sub>2, f'', vs\<^sub>2', ws\<^sub>2')"
              by (auto simp: big_iff_small)
            ultimately have
             "(c', t\<^sub>1, f', vs\<^sub>1', ws\<^sub>1') \<rightarrow>* (SKIP, t\<^sub>2, f', vs\<^sub>2', ws\<^sub>2')"
              (is ?Q1)
              using `?P` by (blast dest: small_steps_stream
               intro: star_trans)
            have T: "(c\<^sub>2, t\<^sub>1, f', vs\<^sub>1', ws\<^sub>1') \<Rightarrow> (t\<^sub>2, f'', vs\<^sub>2', ws\<^sub>2')"
              using S by (simp add: big_iff_small)
            show ?thesis
            proof (cases "c'' = SKIP")
              assume "c'' = SKIP"
                (is ?Q2)
              show ?thesis
              proof (rule exI [of _ SKIP], rule exI [of _ t\<^sub>2],
               rule exI [of _ vs\<^sub>2'], rule exI [of _ ws\<^sub>2'])
                {
                  fix S
                  assume "S \<subseteq> {x. s = t\<^sub>1
                    (\<subseteq> sources_aux (\<langle>bvars b\<rangle> # ?cs') vs\<^sub>1 s f x)}"
                  hence U: "Univ? A X: bvars b \<leadsto>| S"
                    using D by (rule sources_aux_bval, insert J O, simp)
                  hence "[p\<leftarrow>drop (length vs\<^sub>1') vs\<^sub>2'. fst p \<in> S] = []"
                    using I and T by (blast dest: ctyping2_confine)
                  moreover have "no_upd ?cs' S"
                    using B [OF _ _ H M N K] and G and U by simp
                  hence "[p\<leftarrow>in_flow ?cs' vs\<^sub>1 f. fst p \<in> S] = []"
                    by (rule no_upd_in_flow)
                  moreover have "vs\<^sub>2 = vs\<^sub>0 @ in_flow ?cs' vs\<^sub>0 f"
                    using K by (rule small_stepsl_in_flow)
                  ultimately have "[p\<leftarrow>drop (length vs\<^sub>1) vs\<^sub>2. fst p \<in> S] =
                    [p\<leftarrow>drop (length vs\<^sub>1') vs\<^sub>2'. fst p \<in> S]"
                    using `?P` by simp
                  hence "?Q1 \<and> ?Q2 \<and> ?this"
                    using `?Q1` and `?Q2` by simp
                }
                moreover {
                  fix S
                  assume U: "S \<subseteq> {x. s = t\<^sub>1
                    (\<subseteq> sources (\<langle>bvars b\<rangle> # ?cs') vs\<^sub>1 s f x)}"
                  moreover have
                   "\<forall>x. sources_aux (\<langle>bvars b\<rangle> # ?cs') vs\<^sub>1 s f x \<subseteq>
                      sources (\<langle>bvars b\<rangle> # ?cs') vs\<^sub>1 s f x"
                    by (blast intro: subsetD [OF sources_aux_sources])
                  ultimately have "S \<subseteq> {x. s = t\<^sub>1
                    (\<subseteq> sources_aux (\<langle>bvars b\<rangle> # ?cs') vs\<^sub>1 s f x)}"
                    by blast
                  hence V: "Univ? A X: bvars b \<leadsto>| S"
                    using D by (rule sources_aux_bval, insert J O, simp)
                  hence "t\<^sub>1 = t\<^sub>2 (\<subseteq> S)"
                    using I and T by (blast dest: ctyping2_confine)
                  moreover have W: "no_upd ?cs' S"
                    using B [OF _ _ H M N K] and G and V by simp
                  hence "run_flow ?cs' vs\<^sub>0 s f = s (\<subseteq> S)"
                    by (rule no_upd_run_flow)
                  moreover have "s\<^sub>2 = run_flow ?cs' vs\<^sub>0 s f"
                    using K by (rule small_stepsl_run_flow)
                  moreover have
                   "\<forall>x \<in> S. x \<in> sources (\<langle>bvars b\<rangle> # ?cs') vs\<^sub>1 s f x"
                    by (rule no_upd_sources, simp add: W)
                  hence "s = t\<^sub>1 (\<subseteq> S)"
                    using U by blast
                  ultimately have "s\<^sub>2 = t\<^sub>2 (\<subseteq> S)"
                    by simp
                }
                moreover {
                  fix S
                  assume "S \<subseteq> {x. s = t\<^sub>1
                    (\<subseteq> sources_out (\<langle>bvars b\<rangle> # ?cs') vs\<^sub>1 s f x)}"
                  moreover have
                   "\<forall>x. sources_aux (\<langle>bvars b\<rangle> # ?cs') vs\<^sub>1 s f x \<subseteq>
                      sources_out (\<langle>bvars b\<rangle> # ?cs') vs\<^sub>1 s f x"
                    by (blast intro: subsetD [OF sources_aux_sources_out])
                  ultimately have "S \<subseteq> {x. s = t\<^sub>1
                    (\<subseteq> sources_aux (\<langle>bvars b\<rangle> # ?cs') vs\<^sub>1 s f x)}"
                    by blast
                  hence U: "Univ? A X: bvars b \<leadsto>| S"
                    using D by (rule sources_aux_bval, insert J O, simp)
                  hence "[p\<leftarrow>drop (length ws\<^sub>1') ws\<^sub>2'. fst p \<in> S] = []"
                    using I and T by (blast dest: ctyping2_confine)
                  moreover have "no_upd ?cs' S"
                    using B [OF _ _ H M N K] and G and U by simp
                  hence "[p\<leftarrow>out_flow ?cs' vs\<^sub>1 s f. fst p \<in> S] = []"
                    by (rule no_upd_out_flow)
                  moreover have "ws\<^sub>2 = ws\<^sub>0 @ out_flow ?cs' vs\<^sub>0 s f"
                    using K by (rule small_stepsl_out_flow)
                  ultimately have
                   "[p\<leftarrow>drop (length ws\<^sub>1) ws\<^sub>2. fst p \<in> S] =
                    [p\<leftarrow>drop (length ws\<^sub>1') ws\<^sub>2'. fst p \<in> S]"
                    using `?P` by simp
                }
                ultimately show
                 "ok_flow_aux_1 c' c'' SKIP s\<^sub>1 t\<^sub>1 t\<^sub>2 f f'
                    vs\<^sub>1 vs\<^sub>1' vs\<^sub>2 vs\<^sub>2' ws\<^sub>1' ws\<^sub>2' ?cs \<and>
                  ok_flow_aux_2 s\<^sub>1 s\<^sub>2 t\<^sub>1 t\<^sub>2 f f' vs\<^sub>1 vs\<^sub>1' ?cs \<and>
                  ok_flow_aux_3 s\<^sub>1 t\<^sub>1 f f' vs\<^sub>1 vs\<^sub>1' ws\<^sub>1 ws\<^sub>1' ws\<^sub>2 ws\<^sub>2' ?cs"
                  using L and `?P` by auto
              qed
            next
              assume "c'' \<noteq> SKIP"
                (is ?Q2)
              show ?thesis
              proof (rule exI [of _ c'], rule exI [of _ t\<^sub>1],
               rule exI [of _ vs\<^sub>1'], rule exI [of _ ws\<^sub>1'])
                {
                  fix S
                  assume "S \<subseteq> {x. s = t\<^sub>1
                    (\<subseteq> sources_aux (\<langle>bvars b\<rangle> # ?cs') vs\<^sub>1 s f x)}"
                  hence "Univ? A X: bvars b \<leadsto>| S"
                    using D by (rule sources_aux_bval, insert J O, simp)
                  hence "no_upd ?cs' S"
                    using B [OF _ _ H M N K] and G by simp
                  hence "[p\<leftarrow>in_flow ?cs' vs\<^sub>1 f. fst p \<in> S] = []"
                    by (rule no_upd_in_flow)
                  moreover have "vs\<^sub>2 = vs\<^sub>0 @ in_flow ?cs' vs\<^sub>0 f"
                    using K by (rule small_stepsl_in_flow)
                  ultimately have
                   "[p\<leftarrow>drop (length vs\<^sub>1) vs\<^sub>2. fst p \<in> S] = []"
                    using `?P` by simp
                  hence "?Q2 \<and> ?this"
                    using `?Q2` by simp
                }
                moreover {
                  fix S
                  assume U: "S \<subseteq> {x. s = t\<^sub>1
                    (\<subseteq> sources (\<langle>bvars b\<rangle> # ?cs') vs\<^sub>1 s f x)}"
                  moreover have
                   "\<forall>x. sources_aux (\<langle>bvars b\<rangle> # ?cs') vs\<^sub>1 s f x \<subseteq>
                      sources (\<langle>bvars b\<rangle> # ?cs') vs\<^sub>1 s f x"
                    by (blast intro: subsetD [OF sources_aux_sources])
                  ultimately have "S \<subseteq> {x. s = t\<^sub>1
                    (\<subseteq> sources_aux (\<langle>bvars b\<rangle> # ?cs') vs\<^sub>1 s f x)}"
                    by blast
                  hence "Univ? A X: bvars b \<leadsto>| S"
                    using D by (rule sources_aux_bval, insert J O, simp)
                  hence V: "no_upd ?cs' S"
                    using B [OF _ _ H M N K] and G by simp
                  hence "run_flow ?cs' vs\<^sub>0 s f = s (\<subseteq> S)"
                    by (rule no_upd_run_flow)
                  moreover have "s\<^sub>2 = run_flow ?cs' vs\<^sub>0 s f"
                    using K by (rule small_stepsl_run_flow)
                  moreover have
                   "\<forall>x \<in> S. x \<in> sources (\<langle>bvars b\<rangle> # ?cs') vs\<^sub>1 s f x"
                    by (rule no_upd_sources, simp add: V)
                  hence "s = t\<^sub>1 (\<subseteq> S)"
                    using U by blast
                  ultimately have "s\<^sub>2 = t\<^sub>1 (\<subseteq> S)"
                    by simp
                }
                moreover {
                  fix S
                  assume "S \<subseteq> {x. s = t\<^sub>1
                    (\<subseteq> sources_out (\<langle>bvars b\<rangle> # ?cs') vs\<^sub>1 s f x)}"
                  moreover have
                   "\<forall>x. sources_aux (\<langle>bvars b\<rangle> # ?cs') vs\<^sub>1 s f x \<subseteq>
                      sources_out (\<langle>bvars b\<rangle> # ?cs') vs\<^sub>1 s f x"
                    by (blast intro: subsetD [OF sources_aux_sources_out])
                  ultimately have "S \<subseteq> {x. s = t\<^sub>1
                    (\<subseteq> sources_aux (\<langle>bvars b\<rangle> # ?cs') vs\<^sub>1 s f x)}"
                    by blast
                  hence "Univ? A X: bvars b \<leadsto>| S"
                    using D by (rule sources_aux_bval, insert J O, simp)
                  hence "no_upd ?cs' S"
                    using B [OF _ _ H M N K] and G by simp
                  hence "[p\<leftarrow>out_flow ?cs' vs\<^sub>1 s f. fst p \<in> S] = []"
                    by (rule no_upd_out_flow)
                  moreover have "ws\<^sub>2 = ws\<^sub>0 @ out_flow ?cs' vs\<^sub>0 s f"
                    using K by (rule small_stepsl_out_flow)
                  ultimately have
                   "[p\<leftarrow>drop (length ws\<^sub>1) ws\<^sub>2. fst p \<in> S] = []"
                    using `?P` by simp
                }
                ultimately show
                 "ok_flow_aux_1 c' c'' c' s\<^sub>1 t\<^sub>1 t\<^sub>1 f f'
                    vs\<^sub>1 vs\<^sub>1' vs\<^sub>2 vs\<^sub>1' ws\<^sub>1' ws\<^sub>1' ?cs \<and>
                  ok_flow_aux_2 s\<^sub>1 s\<^sub>2 t\<^sub>1 t\<^sub>1 f f' vs\<^sub>1 vs\<^sub>1' ?cs \<and>
                  ok_flow_aux_3 s\<^sub>1 t\<^sub>1 f f' vs\<^sub>1 vs\<^sub>1' ws\<^sub>1 ws\<^sub>1' ws\<^sub>2 ws\<^sub>1' ?cs"
                  using L and `?P` by auto
              qed
            qed
          next
            assume "\<nexists>S. S \<noteq> {} \<and> S \<subseteq> {x. s\<^sub>1 = t\<^sub>1
              (\<subseteq> sources_aux (\<langle>bvars b\<rangle> # ?cs') vs\<^sub>1 s\<^sub>1 f x)}"
            hence O: "\<forall>c\<^sub>2' t\<^sub>2 vs\<^sub>2' ws\<^sub>2'.
              ok_flow_aux_1 c' c'' c\<^sub>2' s\<^sub>1 t\<^sub>1 t\<^sub>2 f f'
                vs\<^sub>1 vs\<^sub>1' vs\<^sub>2 vs\<^sub>2' ws\<^sub>1' ws\<^sub>2' ?cs \<and>
              ok_flow_aux_2 s\<^sub>1 s\<^sub>2 t\<^sub>1 t\<^sub>2 f f' vs\<^sub>1 vs\<^sub>1' ?cs \<and>
              ok_flow_aux_3 s\<^sub>1 t\<^sub>1 f f' vs\<^sub>1 vs\<^sub>1' ws\<^sub>1 ws\<^sub>1' ws\<^sub>2 ws\<^sub>2' ?cs"
              using L by (auto intro!: ok_flow_aux_degen)
            show ?thesis
              by (rule exI [of _ SKIP], rule exI [of _ "\<lambda>x. 0"],
               rule exI [of _ "[]"], rule exI [of _ "[]"],
               simp add: O [rule_format, of SKIP "\<lambda>x. 0" "[]" "[]"])
          qed
        qed
      qed (simp add: B [OF _ _ H M N K] G L)
    next
      assume
        J: "\<not> bval b s" and
        K: "(c\<^sub>2, s, f, vs\<^sub>0, ws\<^sub>0) \<rightarrow>*{tl cfs\<^sub>2} (c'', s\<^sub>2, f, vs\<^sub>2, ws\<^sub>2)" and
        L: "flow cfs\<^sub>2 = \<langle>bvars b\<rangle> # flow (tl cfs\<^sub>2)"
          (is "?cs = _ # ?cs'")
      have M: "s \<in> Univ B\<^sub>2 (\<subseteq> state \<inter> X)"
        using J by (insert btyping2_approx [OF G D], simp)
      have N: "(c\<^sub>2, s, f, vs\<^sub>0, ws\<^sub>0) \<rightarrow>*{[]} (c\<^sub>2, s, f, vs\<^sub>0, ws\<^sub>0)"
        by simp
      show ?thesis
      proof (rule conjI, clarify)
        fix t\<^sub>1 f' vs\<^sub>1' ws\<^sub>1'
        show "\<exists>c\<^sub>2' t\<^sub>2 vs\<^sub>2' ws\<^sub>2'.
          ok_flow_aux_1 c' c'' c\<^sub>2' s\<^sub>1 t\<^sub>1 t\<^sub>2 f f'
            vs\<^sub>1 vs\<^sub>1' vs\<^sub>2 vs\<^sub>2' ws\<^sub>1' ws\<^sub>2' ?cs \<and>
          ok_flow_aux_2 s\<^sub>1 s\<^sub>2 t\<^sub>1 t\<^sub>2 f f' vs\<^sub>1 vs\<^sub>1' ?cs \<and>
          ok_flow_aux_3 s\<^sub>1 t\<^sub>1 f f' vs\<^sub>1 vs\<^sub>1' ws\<^sub>1 ws\<^sub>1' ws\<^sub>2 ws\<^sub>2' ?cs"
        proof (cases "bval b t\<^sub>1", cases "\<exists>S \<noteq> {}.
         S \<subseteq> {x. s\<^sub>1 = t\<^sub>1 (\<subseteq> sources_aux (\<langle>bvars b\<rangle> # ?cs') vs\<^sub>1 s\<^sub>1 f x)}")
          assume O: "\<not> bval b t\<^sub>1"
          have "ok_flow_aux ?U' c\<^sub>2 c'' s s\<^sub>2 f vs\<^sub>0 vs\<^sub>2 ws\<^sub>0 ws\<^sub>2 ?cs'"
            using C [OF _ _ I M N K] and G by simp
          then obtain c\<^sub>2' and t\<^sub>2 and vs\<^sub>2' and ws\<^sub>2' where
           "ok_flow_aux_1 c\<^sub>2 c'' c\<^sub>2' s t\<^sub>1 t\<^sub>2 f f'
              vs\<^sub>0 vs\<^sub>1' vs\<^sub>2 vs\<^sub>2' ws\<^sub>1' ws\<^sub>2' ?cs' \<and>
            ok_flow_aux_2 s s\<^sub>2 t\<^sub>1 t\<^sub>2 f f' vs\<^sub>0 vs\<^sub>1' ?cs' \<and>
            ok_flow_aux_3 s t\<^sub>1 f f' vs\<^sub>0 vs\<^sub>1' ws\<^sub>0 ws\<^sub>1' ws\<^sub>2 ws\<^sub>2' ?cs'"
            (is "?P1 \<and> ?P2 \<and> ?P3")
            by fastforce
          hence ?P1 and ?P2 and ?P3 by auto
          show ?thesis
          proof (rule exI [of _ c\<^sub>2'], rule exI [of _ t\<^sub>2],
           rule exI [of _ vs\<^sub>2'], rule exI [of _ ws\<^sub>2'])
            {
              fix S
              assume
                P: "S \<noteq> {}" and
                Q: "S \<subseteq> {x. s\<^sub>1 = t\<^sub>1
                  (\<subseteq> sources_aux (\<langle>bvars b\<rangle> # ?cs') vs\<^sub>1 s\<^sub>1 f x)}" and
                R: "f = f' (\<subseteq> vs\<^sub>1, vs\<^sub>1',
                  \<Union> {tags_aux (\<langle>bvars b\<rangle> # ?cs') vs\<^sub>1 s\<^sub>1 f x | x. x \<in> S})"
              have "\<forall>x. sources_aux ?cs' vs\<^sub>1 s\<^sub>1 f x \<subseteq>
                sources_aux (\<langle>bvars b\<rangle> # ?cs') vs\<^sub>1 s\<^sub>1 f x"
                by (blast intro: subsetD [OF sources_aux_observe_tl])
              hence "S \<subseteq> {x. s\<^sub>1 = t\<^sub>1 (\<subseteq> sources_aux ?cs' vs\<^sub>1 s\<^sub>1 f x)}"
                using Q by blast
              moreover have "f = f' (\<subseteq> vs\<^sub>1, vs\<^sub>1',
                \<Union> {tags_aux ?cs' vs\<^sub>1 s\<^sub>1 f x | x. x \<in> S})"
                using R by (simp add: tags_aux_observe_tl)
              ultimately have
               "(c\<^sub>2, t\<^sub>1, f', vs\<^sub>1', ws\<^sub>1') \<rightarrow>* (c\<^sub>2', t\<^sub>2, f', vs\<^sub>2', ws\<^sub>2') \<and>
                (c'' = SKIP) = (c\<^sub>2' = SKIP) \<and>
                map fst [p\<leftarrow>drop (length vs\<^sub>1) vs\<^sub>2. fst p \<in> S] =
                  map fst [p\<leftarrow>drop (length vs\<^sub>1') vs\<^sub>2'. fst p \<in> S]"
                (is "?Q1 \<and> ?Q2 \<and> ?Q3")
                using P and `?P` and `?P1` by simp
              hence ?Q1 and ?Q2 and ?Q3 by auto
              moreover have "(IF b THEN c\<^sub>1 ELSE c\<^sub>2, t\<^sub>1, f', vs\<^sub>1', ws\<^sub>1') \<rightarrow>
                (c\<^sub>2, t\<^sub>1, f', vs\<^sub>1', ws\<^sub>1')"
                using O ..
              hence "(c', t\<^sub>1, f', vs\<^sub>1', ws\<^sub>1') \<rightarrow>* (c\<^sub>2', t\<^sub>2, f', vs\<^sub>2', ws\<^sub>2')"
                using `?P` and `?Q1` by (blast intro: star_trans)
              ultimately have "?this \<and> ?Q2 \<and> ?Q3"
                by simp
            }
            moreover {
              fix S
              assume
                P: "S \<subseteq> {x. s\<^sub>1 = t\<^sub>1
                  (\<subseteq> sources (\<langle>bvars b\<rangle> # ?cs') vs\<^sub>1 s\<^sub>1 f x)}" and
                Q: "f = f' (\<subseteq> vs\<^sub>1, vs\<^sub>1',
                  \<Union> {tags (\<langle>bvars b\<rangle> # ?cs') vs\<^sub>1 s\<^sub>1 f x | x. x \<in> S})"
              have "\<forall>x. sources ?cs' vs\<^sub>1 s\<^sub>1 f x \<subseteq>
                sources (\<langle>bvars b\<rangle> # ?cs') vs\<^sub>1 s\<^sub>1 f x"
                by (blast intro: subsetD [OF sources_observe_tl])
              hence "S \<subseteq> {x. s\<^sub>1 = t\<^sub>1 (\<subseteq> sources ?cs' vs\<^sub>1 s\<^sub>1 f x)}"
                using P by blast
              moreover have "f = f' (\<subseteq> vs\<^sub>1, vs\<^sub>1',
                \<Union> {tags ?cs' vs\<^sub>1 s\<^sub>1 f x | x. x \<in> S})"
                using Q by (simp add: tags_observe_tl)
              ultimately have "s\<^sub>2 = t\<^sub>2 (\<subseteq> S)"
                using `?P` and `?P2` by blast
            }
            moreover {
              fix S
              assume
                P: "S \<noteq> {}" and
                Q: "S \<subseteq> {x. s\<^sub>1 = t\<^sub>1
                  (\<subseteq> sources_out (\<langle>bvars b\<rangle> # ?cs') vs\<^sub>1 s\<^sub>1 f x)}" and
                R: "f = f' (\<subseteq> vs\<^sub>1, vs\<^sub>1',
                  \<Union> {tags_out (\<langle>bvars b\<rangle> # ?cs') vs\<^sub>1 s\<^sub>1 f x | x. x \<in> S})"
              have "\<forall>x. sources_out ?cs' vs\<^sub>1 s\<^sub>1 f x \<subseteq>
                sources_out (\<langle>bvars b\<rangle> # ?cs') vs\<^sub>1 s\<^sub>1 f x"
                by (blast intro: subsetD [OF sources_out_observe_tl])
              hence "S \<subseteq> {x. s\<^sub>1 = t\<^sub>1 (\<subseteq> sources_out ?cs' vs\<^sub>1 s\<^sub>1 f x)}"
                using Q by blast
              moreover have "f = f' (\<subseteq> vs\<^sub>1, vs\<^sub>1',
                \<Union> {tags_out ?cs' vs\<^sub>1 s\<^sub>1 f x | x. x \<in> S})"
                using R by (simp add: tags_out_observe_tl)
              ultimately have "[p\<leftarrow>drop (length ws\<^sub>1) ws\<^sub>2. fst p \<in> S] =
                [p\<leftarrow>drop (length ws\<^sub>1') ws\<^sub>2'. fst p \<in> S]"
                using P and `?P` and `?P3` by simp
            }
            ultimately show
             "ok_flow_aux_1 c' c'' c\<^sub>2' s\<^sub>1 t\<^sub>1 t\<^sub>2 f f'
                vs\<^sub>1 vs\<^sub>1' vs\<^sub>2 vs\<^sub>2' ws\<^sub>1' ws\<^sub>2' ?cs \<and>
              ok_flow_aux_2 s\<^sub>1 s\<^sub>2 t\<^sub>1 t\<^sub>2 f f' vs\<^sub>1 vs\<^sub>1' ?cs \<and>
              ok_flow_aux_3 s\<^sub>1 t\<^sub>1 f f' vs\<^sub>1 vs\<^sub>1' ws\<^sub>1 ws\<^sub>1' ws\<^sub>2 ws\<^sub>2' ?cs"
              using L by auto
          qed
        next
          assume O: "bval b t\<^sub>1"
          hence "(IF b THEN c\<^sub>1 ELSE c\<^sub>2, t\<^sub>1, f', vs\<^sub>1', ws\<^sub>1') \<rightarrow>
            (c\<^sub>1, t\<^sub>1, f', vs\<^sub>1', ws\<^sub>1')" ..
          moreover assume "\<exists>S \<noteq> {}.
            S \<subseteq> {x. s\<^sub>1 = t\<^sub>1 (\<subseteq> sources_aux (\<langle>bvars b\<rangle> # ?cs') vs\<^sub>1 s\<^sub>1 f x)}"
          then obtain S where
            P: "S \<noteq> {}" and
            Q: "S \<subseteq> {x. s = t\<^sub>1 (\<subseteq> sources_aux (\<langle>bvars b\<rangle> # ?cs') vs\<^sub>1 s f x)}"
            using `?P` by blast
          have R: "Univ? A X: bvars b \<leadsto>| S"
            using Q and D by (rule sources_aux_bval, insert J O, simp)
          have "\<exists>p. (c\<^sub>1, t\<^sub>1, f', vs\<^sub>1', ws\<^sub>1') \<Rightarrow> p"
            using H by (rule ctyping2_term, insert P R, auto)
          then obtain t\<^sub>2 and f'' and vs\<^sub>2' and ws\<^sub>2' where
            S: "(c\<^sub>1, t\<^sub>1, f', vs\<^sub>1', ws\<^sub>1') \<rightarrow>* (SKIP, t\<^sub>2, f'', vs\<^sub>2', ws\<^sub>2')"
            by (auto simp: big_iff_small)
          ultimately have
           "(c', t\<^sub>1, f', vs\<^sub>1', ws\<^sub>1') \<rightarrow>* (SKIP, t\<^sub>2, f', vs\<^sub>2', ws\<^sub>2')"
            (is ?Q1)
            using `?P` by (blast dest: small_steps_stream intro: star_trans)
          have T: "(c\<^sub>1, t\<^sub>1, f', vs\<^sub>1', ws\<^sub>1') \<Rightarrow> (t\<^sub>2, f'', vs\<^sub>2', ws\<^sub>2')"
            using S by (simp add: big_iff_small)
          show ?thesis
          proof (cases "c'' = SKIP")
            assume "c'' = SKIP"
              (is ?Q2)
            show ?thesis
            proof (rule exI [of _ SKIP], rule exI [of _ t\<^sub>2],
             rule exI [of _ vs\<^sub>2'], rule exI [of _ ws\<^sub>2'])
              {
                fix S
                assume "S \<subseteq> {x. s = t\<^sub>1
                  (\<subseteq> sources_aux (\<langle>bvars b\<rangle> # ?cs') vs\<^sub>1 s f x)}"
                hence U: "Univ? A X: bvars b \<leadsto>| S"
                  using D by (rule sources_aux_bval, insert J O, simp)
                hence "[p\<leftarrow>drop (length vs\<^sub>1') vs\<^sub>2'. fst p \<in> S] = []"
                  using H and T by (blast dest: ctyping2_confine)
                moreover have "no_upd ?cs' S"
                  using C [OF _ _ I M N K] and G and U by simp
                hence "[p\<leftarrow>in_flow ?cs' vs\<^sub>1 f. fst p \<in> S] = []"
                  by (rule no_upd_in_flow)
                moreover have "vs\<^sub>2 = vs\<^sub>0 @ in_flow ?cs' vs\<^sub>0 f"
                  using K by (rule small_stepsl_in_flow)
                ultimately have "[p\<leftarrow>drop (length vs\<^sub>1) vs\<^sub>2. fst p \<in> S] =
                  [p\<leftarrow>drop (length vs\<^sub>1') vs\<^sub>2'. fst p \<in> S]"
                  using `?P` by simp
                hence "?Q1 \<and> ?Q2 \<and> ?this"
                  using `?Q1` and `?Q2` by simp
              }
              moreover {
                fix S
                assume U: "S \<subseteq> {x. s = t\<^sub>1
                  (\<subseteq> sources (\<langle>bvars b\<rangle> # ?cs') vs\<^sub>1 s f x)}"
                moreover have "\<forall>x. sources_aux (\<langle>bvars b\<rangle> # ?cs') vs\<^sub>1 s f x \<subseteq>
                  sources (\<langle>bvars b\<rangle> # ?cs') vs\<^sub>1 s f x"
                  by (blast intro: subsetD [OF sources_aux_sources])
                ultimately have "S \<subseteq> {x. s = t\<^sub>1
                  (\<subseteq> sources_aux (\<langle>bvars b\<rangle> # ?cs') vs\<^sub>1 s f x)}"
                  by blast
                hence V: "Univ? A X: bvars b \<leadsto>| S"
                  using D by (rule sources_aux_bval, insert J O, simp)
                hence "t\<^sub>1 = t\<^sub>2 (\<subseteq> S)"
                  using H and T by (blast dest: ctyping2_confine)
                moreover have W: "no_upd ?cs' S"
                  using C [OF _ _ I M N K] and G and V by simp
                hence "run_flow ?cs' vs\<^sub>0 s f = s (\<subseteq> S)"
                  by (rule no_upd_run_flow)
                moreover have "s\<^sub>2 = run_flow ?cs' vs\<^sub>0 s f"
                  using K by (rule small_stepsl_run_flow)
                moreover have "\<forall>x \<in> S. x \<in> sources (\<langle>bvars b\<rangle> # ?cs') vs\<^sub>1 s f x"
                  by (rule no_upd_sources, simp add: W)
                hence "s = t\<^sub>1 (\<subseteq> S)"
                  using U by blast
                ultimately have "s\<^sub>2 = t\<^sub>2 (\<subseteq> S)"
                  by simp
              }
              moreover {
                fix S
                assume "S \<subseteq> {x. s = t\<^sub>1
                  (\<subseteq> sources_out (\<langle>bvars b\<rangle> # ?cs') vs\<^sub>1 s f x)}"
                moreover have "\<forall>x. sources_aux (\<langle>bvars b\<rangle> # ?cs') vs\<^sub>1 s f x \<subseteq>
                  sources_out (\<langle>bvars b\<rangle> # ?cs') vs\<^sub>1 s f x"
                  by (blast intro: subsetD [OF sources_aux_sources_out])
                ultimately have "S \<subseteq> {x. s = t\<^sub>1
                  (\<subseteq> sources_aux (\<langle>bvars b\<rangle> # ?cs') vs\<^sub>1 s f x)}"
                  by blast
                hence U: "Univ? A X: bvars b \<leadsto>| S"
                  using D by (rule sources_aux_bval, insert J O, simp)
                hence "[p\<leftarrow>drop (length ws\<^sub>1') ws\<^sub>2'. fst p \<in> S] = []"
                  using H and T by (blast dest: ctyping2_confine)
                moreover have "no_upd ?cs' S"
                  using C [OF _ _ I M N K] and G and U by simp
                hence "[p\<leftarrow>out_flow ?cs' vs\<^sub>1 s f. fst p \<in> S] = []"
                  by (rule no_upd_out_flow)
                moreover have "ws\<^sub>2 = ws\<^sub>0 @ out_flow ?cs' vs\<^sub>0 s f"
                  using K by (rule small_stepsl_out_flow)
                ultimately have
                 "[p\<leftarrow>drop (length ws\<^sub>1) ws\<^sub>2. fst p \<in> S] =
                  [p\<leftarrow>drop (length ws\<^sub>1') ws\<^sub>2'. fst p \<in> S]"
                  using `?P` by simp
              }
              ultimately show
               "ok_flow_aux_1 c' c'' SKIP s\<^sub>1 t\<^sub>1 t\<^sub>2 f f'
                  vs\<^sub>1 vs\<^sub>1' vs\<^sub>2 vs\<^sub>2' ws\<^sub>1' ws\<^sub>2' ?cs \<and>
                ok_flow_aux_2 s\<^sub>1 s\<^sub>2 t\<^sub>1 t\<^sub>2 f f' vs\<^sub>1 vs\<^sub>1' ?cs \<and>
                ok_flow_aux_3 s\<^sub>1 t\<^sub>1 f f' vs\<^sub>1 vs\<^sub>1' ws\<^sub>1 ws\<^sub>1' ws\<^sub>2 ws\<^sub>2' ?cs"
                using L and `?P` by auto
            qed
          next
            assume "c'' \<noteq> SKIP"
              (is ?Q2)
            show ?thesis
            proof (rule exI [of _ c'], rule exI [of _ t\<^sub>1],
             rule exI [of _ vs\<^sub>1'], rule exI [of _ ws\<^sub>1'])
              {
                fix S
                assume "S \<subseteq> {x. s = t\<^sub>1
                  (\<subseteq> sources_aux (\<langle>bvars b\<rangle> # ?cs') vs\<^sub>1 s f x)}"
                hence "Univ? A X: bvars b \<leadsto>| S"
                  using D by (rule sources_aux_bval, insert J O, simp)
                hence "no_upd ?cs' S"
                  using C [OF _ _ I M N K] and G by simp
                hence "[p\<leftarrow>in_flow ?cs' vs\<^sub>1 f. fst p \<in> S] = []"
                  by (rule no_upd_in_flow)
                moreover have "vs\<^sub>2 = vs\<^sub>0 @ in_flow ?cs' vs\<^sub>0 f"
                  using K by (rule small_stepsl_in_flow)
                ultimately have "[p\<leftarrow>drop (length vs\<^sub>1) vs\<^sub>2. fst p \<in> S] = []"
                  using `?P` by simp
                hence "?Q2 \<and> ?this"
                  using `?Q2` by simp
              }
              moreover {
                fix S
                assume U: "S \<subseteq> {x. s = t\<^sub>1
                  (\<subseteq> sources (\<langle>bvars b\<rangle> # ?cs') vs\<^sub>1 s f x)}"
                moreover have "\<forall>x. sources_aux (\<langle>bvars b\<rangle> # ?cs') vs\<^sub>1 s f x \<subseteq>
                  sources (\<langle>bvars b\<rangle> # ?cs') vs\<^sub>1 s f x"
                  by (blast intro: subsetD [OF sources_aux_sources])
                ultimately have "S \<subseteq> {x. s = t\<^sub>1
                  (\<subseteq> sources_aux (\<langle>bvars b\<rangle> # ?cs') vs\<^sub>1 s f x)}"
                  by blast
                hence "Univ? A X: bvars b \<leadsto>| S"
                  using D by (rule sources_aux_bval, insert J O, simp)
                hence V: "no_upd ?cs' S"
                  using C [OF _ _ I M N K] and G by simp
                hence "run_flow ?cs' vs\<^sub>0 s f = s (\<subseteq> S)"
                  by (rule no_upd_run_flow)
                moreover have "s\<^sub>2 = run_flow ?cs' vs\<^sub>0 s f"
                  using K by (rule small_stepsl_run_flow)
                moreover have "\<forall>x \<in> S. x \<in> sources (\<langle>bvars b\<rangle> # ?cs') vs\<^sub>1 s f x"
                  by (rule no_upd_sources, simp add: V)
                hence "s = t\<^sub>1 (\<subseteq> S)"
                  using U by blast
                ultimately have "s\<^sub>2 = t\<^sub>1 (\<subseteq> S)"
                  by simp
              }
              moreover {
                fix S
                assume "S \<subseteq> {x. s = t\<^sub>1
                  (\<subseteq> sources_out (\<langle>bvars b\<rangle> # ?cs') vs\<^sub>1 s f x)}"
                moreover have "\<forall>x. sources_aux (\<langle>bvars b\<rangle> # ?cs') vs\<^sub>1 s f x \<subseteq>
                  sources_out (\<langle>bvars b\<rangle> # ?cs') vs\<^sub>1 s f x"
                  by (blast intro: subsetD [OF sources_aux_sources_out])
                ultimately have "S \<subseteq> {x. s = t\<^sub>1
                  (\<subseteq> sources_aux (\<langle>bvars b\<rangle> # ?cs') vs\<^sub>1 s f x)}"
                  by blast
                hence "Univ? A X: bvars b \<leadsto>| S"
                  using D by (rule sources_aux_bval, insert J O, simp)
                hence "no_upd ?cs' S"
                  using C [OF _ _ I M N K] and G by simp
                hence "[p\<leftarrow>out_flow ?cs' vs\<^sub>1 s f. fst p \<in> S] = []"
                  by (rule no_upd_out_flow)
                moreover have "ws\<^sub>2 = ws\<^sub>0 @ out_flow ?cs' vs\<^sub>0 s f"
                  using K by (rule small_stepsl_out_flow)
                ultimately have "[p\<leftarrow>drop (length ws\<^sub>1) ws\<^sub>2. fst p \<in> S] = []"
                  using `?P` by simp
              }
              ultimately show
               "ok_flow_aux_1 c' c'' c' s\<^sub>1 t\<^sub>1 t\<^sub>1 f f'
                  vs\<^sub>1 vs\<^sub>1' vs\<^sub>2 vs\<^sub>1' ws\<^sub>1' ws\<^sub>1' ?cs \<and>
                ok_flow_aux_2 s\<^sub>1 s\<^sub>2 t\<^sub>1 t\<^sub>1 f f' vs\<^sub>1 vs\<^sub>1' ?cs \<and>
                ok_flow_aux_3 s\<^sub>1 t\<^sub>1 f f' vs\<^sub>1 vs\<^sub>1' ws\<^sub>1 ws\<^sub>1' ws\<^sub>2 ws\<^sub>1' ?cs"
                using L and `?P` by auto
            qed
          qed
        next
          assume "\<nexists>S. S \<noteq> {} \<and>
            S \<subseteq> {x. s\<^sub>1 = t\<^sub>1 (\<subseteq> sources_aux (\<langle>bvars b\<rangle> # ?cs') vs\<^sub>1 s\<^sub>1 f x)}"
          hence O: "\<forall>c\<^sub>2' t\<^sub>2 vs\<^sub>2' ws\<^sub>2'.
            ok_flow_aux_1 c' c'' c\<^sub>2' s\<^sub>1 t\<^sub>1 t\<^sub>2 f f'
              vs\<^sub>1 vs\<^sub>1' vs\<^sub>2 vs\<^sub>2' ws\<^sub>1' ws\<^sub>2' ?cs \<and>
            ok_flow_aux_2 s\<^sub>1 s\<^sub>2 t\<^sub>1 t\<^sub>2 f f' vs\<^sub>1 vs\<^sub>1' ?cs \<and>
            ok_flow_aux_3 s\<^sub>1 t\<^sub>1 f f' vs\<^sub>1 vs\<^sub>1' ws\<^sub>1 ws\<^sub>1' ws\<^sub>2 ws\<^sub>2' ?cs"
            using L by (auto intro!: ok_flow_aux_degen)
          show ?thesis
            by (rule exI [of _ SKIP], rule exI [of _ "\<lambda>x. 0"],
             rule exI [of _ "[]"], rule exI [of _ "[]"],
             simp add: O [rule_format, of SKIP "\<lambda>x. 0" "[]" "[]"])
        qed
      qed (simp add: C [OF _ _ I M N K] G L)
    qed
  next
    assume "bval b s"
    hence J: "s \<in> Univ B\<^sub>1 (\<subseteq> state \<inter> X)"
      by (insert btyping2_approx [OF G D], simp)
    assume K: "(c\<^sub>1, s, f, vs\<^sub>0, ws\<^sub>0) \<rightarrow>*{tl cfs\<^sub>1} (c', s\<^sub>1, f, vs\<^sub>1, ws\<^sub>1)"
    show ?thesis
      using B [OF _ _ H J K F] and G by simp
  next
    assume "\<not> bval b s"
    hence J: "s \<in> Univ B\<^sub>2 (\<subseteq> state \<inter> X)"
      by (insert btyping2_approx [OF G D], simp)
    assume K: "(c\<^sub>2, s, f, vs\<^sub>0, ws\<^sub>0) \<rightarrow>*{tl cfs\<^sub>1} (c', s\<^sub>1, f, vs\<^sub>1, ws\<^sub>1)"
    show ?thesis
      using C [OF _ _ I J K F] and G by simp
  qed
qed

lemma ctyping2_correct_aux_while:
  assumes
    A: "(U, v) \<Turnstile> WHILE b DO c (\<subseteq> A, X) = Some (B, W)" and
    B: "\<And>B\<^sub>1 B\<^sub>2 C Y B\<^sub>1' B\<^sub>2' D Z c\<^sub>1 c\<^sub>2 s s\<^sub>1 s\<^sub>2 vs\<^sub>0 vs\<^sub>1 vs\<^sub>2 ws\<^sub>0 ws\<^sub>1 ws\<^sub>2 cfs\<^sub>1 cfs\<^sub>2.
      (B\<^sub>1, B\<^sub>2) = \<Turnstile> b (\<subseteq> A, X) \<Longrightarrow>
      (C, Y) = \<turnstile> c (\<subseteq> B\<^sub>1, X) \<Longrightarrow>
      (B\<^sub>1', B\<^sub>2') = \<Turnstile> b (\<subseteq> C, Y) \<Longrightarrow>
      \<forall>(B, W) \<in> insert (Univ? A X \<union> Univ? C Y, bvars b) U.
        B: W \<leadsto> UNIV \<Longrightarrow>
      ({}, False) \<Turnstile> c (\<subseteq> B\<^sub>1, X) = Some (D, Z) \<Longrightarrow>
      s \<in> Univ B\<^sub>1 (\<subseteq> state \<inter> X) \<Longrightarrow>
      (c, s, f, vs\<^sub>0, ws\<^sub>0) \<rightarrow>*{cfs\<^sub>1} (c\<^sub>1, s\<^sub>1, f, vs\<^sub>1, ws\<^sub>1) \<Longrightarrow>
      (c\<^sub>1, s\<^sub>1, f, vs\<^sub>1, ws\<^sub>1) \<rightarrow>*{cfs\<^sub>2} (c\<^sub>2, s\<^sub>2, f, vs\<^sub>2, ws\<^sub>2) \<Longrightarrow>
        ok_flow_aux {} c\<^sub>1 c\<^sub>2 s\<^sub>1 s\<^sub>2 f vs\<^sub>1 vs\<^sub>2 ws\<^sub>1 ws\<^sub>2 (flow cfs\<^sub>2)" and
    C: "\<And>B\<^sub>1 B\<^sub>2 C Y B\<^sub>1' B\<^sub>2' D' Z' c\<^sub>1 c\<^sub>2 s s\<^sub>1 s\<^sub>2 vs\<^sub>0 vs\<^sub>1 vs\<^sub>2 ws\<^sub>0 ws\<^sub>1 ws\<^sub>2 cfs\<^sub>1 cfs\<^sub>2.
      (B\<^sub>1, B\<^sub>2) = \<Turnstile> b (\<subseteq> A, X) \<Longrightarrow>
      (C, Y) = \<turnstile> c (\<subseteq> B\<^sub>1, X) \<Longrightarrow>
      (B\<^sub>1', B\<^sub>2') = \<Turnstile> b (\<subseteq> C, Y) \<Longrightarrow>
      \<forall>(B, W) \<in> insert (Univ? A X \<union> Univ? C Y, bvars b) U.
        B: W \<leadsto> UNIV \<Longrightarrow>
      ({}, False) \<Turnstile> c (\<subseteq> B\<^sub>1', Y) = Some (D', Z') \<Longrightarrow>
      s \<in> Univ B\<^sub>1' (\<subseteq> state \<inter> Y) \<Longrightarrow>
      (c, s, f, vs\<^sub>0, ws\<^sub>0) \<rightarrow>*{cfs\<^sub>1} (c\<^sub>1, s\<^sub>1, f, vs\<^sub>1, ws\<^sub>1) \<Longrightarrow>
      (c\<^sub>1, s\<^sub>1, f, vs\<^sub>1, ws\<^sub>1) \<rightarrow>*{cfs\<^sub>2} (c\<^sub>2, s\<^sub>2, f, vs\<^sub>2, ws\<^sub>2) \<Longrightarrow>
        ok_flow_aux {} c\<^sub>1 c\<^sub>2 s\<^sub>1 s\<^sub>2 f vs\<^sub>1 vs\<^sub>2 ws\<^sub>1 ws\<^sub>2 (flow cfs\<^sub>2)" and
    D: "s \<in> Univ A (\<subseteq> state \<inter> X)" and
    E: "(WHILE b DO c, s, f, vs\<^sub>0, ws\<^sub>0) \<rightarrow>*{cfs\<^sub>1} (c\<^sub>1, s\<^sub>1, f, vs\<^sub>1, ws\<^sub>1)" and
    F: "(c\<^sub>1, s\<^sub>1, f, vs\<^sub>1, ws\<^sub>1) \<rightarrow>*{cfs\<^sub>2} (c\<^sub>2, s\<^sub>2, f, vs\<^sub>2, ws\<^sub>2)"
 shows "ok_flow_aux U c\<^sub>1 c\<^sub>2 s\<^sub>1 s\<^sub>2 f vs\<^sub>1 vs\<^sub>2 ws\<^sub>1 ws\<^sub>2 (flow cfs\<^sub>2)"
proof -
  from A obtain B\<^sub>1 B\<^sub>2 C Y B\<^sub>1' B\<^sub>2' D Z D' Z' where
    G: "\<Turnstile> b (\<subseteq> A, X) = (B\<^sub>1, B\<^sub>2)" and
    H: "\<turnstile> c (\<subseteq> B\<^sub>1, X) = (C, Y)" and
    I: "\<Turnstile> b (\<subseteq> C, Y) = (B\<^sub>1', B\<^sub>2')" and
    J: "({}, False) \<Turnstile> c (\<subseteq> B\<^sub>1, X) = Some (D, Z)" and
    K: "({}, False) \<Turnstile> c (\<subseteq> B\<^sub>1', Y) = Some (D', Z')" and
    L: "\<forall>(B, W) \<in> insert (Univ? A X \<union> Univ? C Y, bvars b) U. B: W \<leadsto> UNIV"
    by (fastforce split: if_split_asm option.split_asm prod.split_asm)
  from UnI1 [OF D, of "Univ C (\<subseteq> state \<inter> Y)"] and E and F show ?thesis
  proof (induction "cfs\<^sub>1 @ cfs\<^sub>2" arbitrary: cfs\<^sub>1 cfs\<^sub>2 s vs\<^sub>0 ws\<^sub>0 c\<^sub>1 s\<^sub>1 vs\<^sub>1 ws\<^sub>1
   rule: length_induct)
    fix cfs\<^sub>1 cfs\<^sub>2 s vs\<^sub>0 ws\<^sub>0 c\<^sub>1 s\<^sub>1 vs\<^sub>1 ws\<^sub>1
    assume
      M: "\<forall>cfs. length cfs < length (cfs\<^sub>1 @ cfs\<^sub>2) \<longrightarrow>
        (\<forall>cfs' cfs''. cfs = cfs' @ cfs'' \<longrightarrow>
          (\<forall>s. s \<in> Univ A (\<subseteq> state \<inter> X) \<union> Univ C (\<subseteq> state \<inter> Y) \<longrightarrow>
            (\<forall>vs\<^sub>0 ws\<^sub>0 c\<^sub>1 s\<^sub>1 vs\<^sub>1 ws\<^sub>1.
              (WHILE b DO c, s, f, vs\<^sub>0, ws\<^sub>0) \<rightarrow>*{cfs'} (c\<^sub>1, s\<^sub>1, f, vs\<^sub>1, ws\<^sub>1) \<longrightarrow>
              (c\<^sub>1, s\<^sub>1, f, vs\<^sub>1, ws\<^sub>1) \<rightarrow>*{cfs''} (c\<^sub>2, s\<^sub>2, f, vs\<^sub>2, ws\<^sub>2) \<longrightarrow>
                ok_flow_aux U c\<^sub>1 c\<^sub>2 s\<^sub>1 s\<^sub>2 f vs\<^sub>1 vs\<^sub>2 ws\<^sub>1 ws\<^sub>2 (flow cfs''))))" and
      N: "s \<in> Univ A (\<subseteq> state \<inter> X) \<union> Univ C (\<subseteq> state \<inter> Y)" and
      O: "(c\<^sub>1, s\<^sub>1, f, vs\<^sub>1, ws\<^sub>1) \<rightarrow>*{cfs\<^sub>2} (c\<^sub>2, s\<^sub>2, f, vs\<^sub>2, ws\<^sub>2)"
    assume "(WHILE b DO c, s, f, vs\<^sub>0, ws\<^sub>0) \<rightarrow>*{cfs\<^sub>1} (c\<^sub>1, s\<^sub>1, f, vs\<^sub>1, ws\<^sub>1)"
    hence
     "(c\<^sub>1, s\<^sub>1, f, vs\<^sub>1, ws\<^sub>1) = (WHILE b DO c, s, f, vs\<^sub>0, ws\<^sub>0) \<and>
        flow cfs\<^sub>1 = [] \<or>
      bval b s \<and>
        (c;; WHILE b DO c, s, f, vs\<^sub>0, ws\<^sub>0) \<rightarrow>*{tl cfs\<^sub>1} (c\<^sub>1, s\<^sub>1, f, vs\<^sub>1, ws\<^sub>1) \<and>
        flow cfs\<^sub>1 = \<langle>bvars b\<rangle> # flow (tl cfs\<^sub>1) \<or>
      \<not> bval b s \<and>
        (c\<^sub>1, s\<^sub>1, f, vs\<^sub>1, ws\<^sub>1) = (SKIP, s, f, vs\<^sub>0, ws\<^sub>0) \<and>
        flow cfs\<^sub>1 = [\<langle>bvars b\<rangle>]"
      by (rule small_stepsl_while)
    thus "ok_flow_aux U c\<^sub>1 c\<^sub>2 s\<^sub>1 s\<^sub>2 f vs\<^sub>1 vs\<^sub>2 ws\<^sub>1 ws\<^sub>2 (flow cfs\<^sub>2)"
    proof (rule disjE, erule_tac [2] disjE, erule_tac conjE,
     (erule_tac [2-3] conjE)+)
      assume P: "(c\<^sub>1, s\<^sub>1, f, vs\<^sub>1, ws\<^sub>1) = (WHILE b DO c, s, f, vs\<^sub>0, ws\<^sub>0)"
      hence "(WHILE b DO c, s, f, vs\<^sub>0, ws\<^sub>0) \<rightarrow>*{cfs\<^sub>2} (c\<^sub>2, s\<^sub>2, f, vs\<^sub>2, ws\<^sub>2)"
        using O by simp
      hence
       "(c\<^sub>2, s\<^sub>2, f, vs\<^sub>2, ws\<^sub>2) = (WHILE b DO c, s, f, vs\<^sub>0, ws\<^sub>0) \<and>
          flow cfs\<^sub>2 = [] \<or>
        bval b s \<and>
          (c;; WHILE b DO c, s, f, vs\<^sub>0, ws\<^sub>0) \<rightarrow>*{tl cfs\<^sub>2}
            (c\<^sub>2, s\<^sub>2, f, vs\<^sub>2, ws\<^sub>2) \<and>
          flow cfs\<^sub>2 = \<langle>bvars b\<rangle> # flow (tl cfs\<^sub>2) \<or>
        \<not> bval b s \<and>
          (c\<^sub>2, s\<^sub>2, f, vs\<^sub>2, ws\<^sub>2) = (SKIP, s, f, vs\<^sub>0, ws\<^sub>0) \<and>
          flow cfs\<^sub>2 = [\<langle>bvars b\<rangle>]"
        by (rule small_stepsl_while)
      thus ?thesis
      proof (rule disjE, erule_tac [2] disjE, erule_tac conjE,
       (erule_tac [2-3] conjE)+)
        assume
         "(c\<^sub>2, s\<^sub>2, f, vs\<^sub>2, ws\<^sub>2) = (WHILE b DO c, s, f, vs\<^sub>0, ws\<^sub>0)" and
         "flow cfs\<^sub>2 = []"
        thus ?thesis
          using P by fastforce
      next
        assume
          Q: "bval b s" and
          R: "flow cfs\<^sub>2 = \<langle>bvars b\<rangle> # flow (tl cfs\<^sub>2)"
            (is "?cs = _ # ?cs'")
        assume "(c;; WHILE b DO c, s, f, vs\<^sub>0, ws\<^sub>0) \<rightarrow>*{tl cfs\<^sub>2}
          (c\<^sub>2, s\<^sub>2, f, vs\<^sub>2, ws\<^sub>2)"
        hence
         "(\<exists>c' cfs.
            c\<^sub>2 = c';; WHILE b DO c \<and>
            (c, s, f, vs\<^sub>0, ws\<^sub>0) \<rightarrow>*{cfs} (c', s\<^sub>2, f, vs\<^sub>2, ws\<^sub>2) \<and>
            ?cs' = flow cfs) \<or>
          (\<exists>p cfs' cfs''.
            length cfs'' < length (tl cfs\<^sub>2) \<and>
            (c, s, f, vs\<^sub>0, ws\<^sub>0) \<rightarrow>*{cfs'} (SKIP, p) \<and>
            (WHILE b DO c, p) \<rightarrow>*{cfs''} (c\<^sub>2, s\<^sub>2, f, vs\<^sub>2, ws\<^sub>2) \<and>
            ?cs' = flow cfs' @ flow cfs'')"
          by (rule small_stepsl_seq)
        thus ?thesis
          apply (rule disjE)
           apply (erule exE)+
           apply (erule conjE)+
          subgoal for c' cfs
          proof -
            assume
              S: "c\<^sub>2 = c';; WHILE b DO c" and
              T: "(c, s, f, vs\<^sub>0, ws\<^sub>0) \<rightarrow>*{cfs} (c', s\<^sub>2, f, vs\<^sub>2, ws\<^sub>2)" and
              U: "?cs' = flow cfs"
            have V: "(c, s, f, vs\<^sub>0, ws\<^sub>0) \<rightarrow>*{[]} (c, s, f, vs\<^sub>0, ws\<^sub>0)"
              by simp
            from N have
             "ok_flow_aux {} c c' s s\<^sub>2 f vs\<^sub>0 vs\<^sub>2 ws\<^sub>0 ws\<^sub>2 (flow cfs)"
            proof
              assume W: "s \<in> Univ A (\<subseteq> state \<inter> X)"
              have X: "s \<in> Univ B\<^sub>1 (\<subseteq> state \<inter> X)"
                using Q by (insert btyping2_approx [OF G W], simp)
              show ?thesis
                by (rule B [OF G [symmetric] H [symmetric] I [symmetric]
                 L J X V T])
            next
              assume W: "s \<in> Univ C (\<subseteq> state \<inter> Y)"
              have X: "s \<in> Univ B\<^sub>1' (\<subseteq> state \<inter> Y)"
                using Q by (insert btyping2_approx [OF I W], simp)
              show ?thesis
                by (rule C [OF G [symmetric] H [symmetric] I [symmetric]
                 L K X V T])
            qed
            hence W: "ok_flow_aux {} c c' s\<^sub>1 s\<^sub>2 f vs\<^sub>1 vs\<^sub>2 ws\<^sub>1 ws\<^sub>2 ?cs'"
              using P and U by simp
            show ?thesis
            proof (rule conjI, clarify)
              fix t\<^sub>1 f' vs\<^sub>1' ws\<^sub>1'
              obtain c\<^sub>2' and t\<^sub>2 and vs\<^sub>2' and ws\<^sub>2' where
               "ok_flow_aux_1 c c' c\<^sub>2' s\<^sub>1 t\<^sub>1 t\<^sub>2 f f'
                  vs\<^sub>1 vs\<^sub>1' vs\<^sub>2 vs\<^sub>2' ws\<^sub>1' ws\<^sub>2' ?cs' \<and>
                ok_flow_aux_2 s\<^sub>1 s\<^sub>2 t\<^sub>1 t\<^sub>2 f f' vs\<^sub>1 vs\<^sub>1' ?cs' \<and>
                ok_flow_aux_3 s\<^sub>1 t\<^sub>1 f f' vs\<^sub>1 vs\<^sub>1' ws\<^sub>1 ws\<^sub>1' ws\<^sub>2 ws\<^sub>2' ?cs'"
                (is "?P1 \<and> ?P2 \<and> ?P3")
                using W by fastforce
              hence ?P1 and ?P2 and ?P3 by auto
              show "\<exists>c\<^sub>2' t\<^sub>2 vs\<^sub>2' ws\<^sub>2'.
                ok_flow_aux_1 c\<^sub>1 c\<^sub>2 c\<^sub>2' s\<^sub>1 t\<^sub>1 t\<^sub>2 f f'
                  vs\<^sub>1 vs\<^sub>1' vs\<^sub>2 vs\<^sub>2' ws\<^sub>1' ws\<^sub>2' ?cs \<and>
                ok_flow_aux_2 s\<^sub>1 s\<^sub>2 t\<^sub>1 t\<^sub>2 f f' vs\<^sub>1 vs\<^sub>1' ?cs \<and>
                ok_flow_aux_3 s\<^sub>1 t\<^sub>1 f f' vs\<^sub>1 vs\<^sub>1' ws\<^sub>1 ws\<^sub>1' ws\<^sub>2 ws\<^sub>2' ?cs"
              proof (rule exI [of _ "c\<^sub>2';; WHILE b DO c"], rule exI [of _ t\<^sub>2],
               rule exI [of _ vs\<^sub>2'], rule exI [of _ ws\<^sub>2'])
                {
                  fix S
                  assume
                    X: "S \<noteq> {}" and
                    Y: "S \<subseteq> {x. s\<^sub>1 = t\<^sub>1
                      (\<subseteq> sources_aux (\<langle>bvars b\<rangle> # ?cs') vs\<^sub>1 s\<^sub>1 f x)}" and
                    Z: "f = f' (\<subseteq> vs\<^sub>1, vs\<^sub>1',
                      \<Union> {tags_aux (\<langle>bvars b\<rangle> # ?cs') vs\<^sub>1 s\<^sub>1 f x | x. x \<in> S})"
                  have "\<forall>x. sources_aux ?cs' vs\<^sub>1 s\<^sub>1 f x \<subseteq>
                    sources_aux (\<langle>bvars b\<rangle> # ?cs') vs\<^sub>1 s\<^sub>1 f x"
                    by (blast intro: subsetD [OF sources_aux_observe_tl])
                  hence "S \<subseteq> {x. s\<^sub>1 = t\<^sub>1 (\<subseteq> sources_aux ?cs' vs\<^sub>1 s\<^sub>1 f x)}"
                    using Y by blast
                  moreover have "f = f' (\<subseteq> vs\<^sub>1, vs\<^sub>1',
                    \<Union> {tags_aux ?cs' vs\<^sub>1 s\<^sub>1 f x | x. x \<in> S})"
                    using Z by (simp add: tags_aux_observe_tl)
                  ultimately have
                   "(c, t\<^sub>1, f', vs\<^sub>1', ws\<^sub>1') \<rightarrow>* (c\<^sub>2', t\<^sub>2, f', vs\<^sub>2', ws\<^sub>2') \<and>
                    map fst [p\<leftarrow>drop (length vs\<^sub>1) vs\<^sub>2. fst p \<in> S] =
                      map fst [p\<leftarrow>drop (length vs\<^sub>1') vs\<^sub>2'. fst p \<in> S]"
                    (is "?Q1 \<and> ?Q2")
                    using X and `?P1` by simp
                  hence ?Q1 and ?Q2 by auto
                  have "s\<^sub>1 = t\<^sub>1 (\<subseteq> bvars b)"
                    by (rule eq_states_while [OF Y X], insert L N P, simp+)
                  hence "bval b t\<^sub>1"
                    using P and Q by (blast dest: bvars_bval)
                  hence "(WHILE b DO c, t\<^sub>1, f', vs\<^sub>1', ws\<^sub>1') \<rightarrow>
                    (c;; WHILE b DO c, t\<^sub>1, f', vs\<^sub>1', ws\<^sub>1')" ..
                  hence "(c\<^sub>1, t\<^sub>1, f', vs\<^sub>1', ws\<^sub>1') \<rightarrow>*
                    (c\<^sub>2';; WHILE b DO c, t\<^sub>2, f', vs\<^sub>2', ws\<^sub>2')"
                    using P and `?Q1` by (blast intro: star_seq2 star_trans)
                  hence "?this \<and> ?Q2"
                    using `?Q2` by simp
                }
                moreover {
                  fix S
                  assume
                    X: "S \<subseteq> {x. s\<^sub>1 = t\<^sub>1
                      (\<subseteq> sources (\<langle>bvars b\<rangle> # ?cs') vs\<^sub>1 s\<^sub>1 f x)}" and
                    Y: "f = f' (\<subseteq> vs\<^sub>1, vs\<^sub>1',
                      \<Union> {tags (\<langle>bvars b\<rangle> # ?cs') vs\<^sub>1 s\<^sub>1 f x | x. x \<in> S})"
                  have "\<forall>x. sources ?cs' vs\<^sub>1 s\<^sub>1 f x \<subseteq>
                    sources (\<langle>bvars b\<rangle> # ?cs') vs\<^sub>1 s\<^sub>1 f x"
                    by (blast intro: subsetD [OF sources_observe_tl])
                  hence "S \<subseteq> {x. s\<^sub>1 = t\<^sub>1 (\<subseteq> sources ?cs' vs\<^sub>1 s\<^sub>1 f x)}"
                    using X by blast
                  moreover have "f = f' (\<subseteq> vs\<^sub>1, vs\<^sub>1',
                    \<Union> {tags ?cs' vs\<^sub>1 s\<^sub>1 f x | x. x \<in> S})"
                    using Y by (simp add: tags_observe_tl)
                  ultimately have "s\<^sub>2 = t\<^sub>2 (\<subseteq> S)"
                    using `?P2` by blast
                }
                moreover {
                  fix S
                  assume
                    X: "S \<noteq> {}" and
                    Y: "S \<subseteq> {x. s\<^sub>1 = t\<^sub>1
                      (\<subseteq> sources_out (\<langle>bvars b\<rangle> # ?cs') vs\<^sub>1 s\<^sub>1 f x)}" and
                    Z: "f = f' (\<subseteq> vs\<^sub>1, vs\<^sub>1',
                      \<Union> {tags_out (\<langle>bvars b\<rangle> # ?cs') vs\<^sub>1 s\<^sub>1 f x | x. x \<in> S})"
                  have "\<forall>x. sources_out ?cs' vs\<^sub>1 s\<^sub>1 f x \<subseteq>
                    sources_out (\<langle>bvars b\<rangle> # ?cs') vs\<^sub>1 s\<^sub>1 f x"
                    by (blast intro: subsetD [OF sources_out_observe_tl])
                  hence "S \<subseteq> {x. s\<^sub>1 = t\<^sub>1 (\<subseteq> sources_out ?cs' vs\<^sub>1 s\<^sub>1 f x)}"
                    using Y by blast
                  moreover have "f = f' (\<subseteq> vs\<^sub>1, vs\<^sub>1',
                    \<Union> {tags_out ?cs' vs\<^sub>1 s\<^sub>1 f x | x. x \<in> S})"
                    using Z by (simp add: tags_out_observe_tl)
                  ultimately have "[p\<leftarrow>drop (length ws\<^sub>1) ws\<^sub>2. fst p \<in> S] =
                    [p\<leftarrow>drop (length ws\<^sub>1') ws\<^sub>2'. fst p \<in> S]"
                    using X and `?P3` by simp
                }
                ultimately show
                 "ok_flow_aux_1 c\<^sub>1 c\<^sub>2 (c\<^sub>2';; WHILE b DO c) s\<^sub>1 t\<^sub>1 t\<^sub>2 f f'
                    vs\<^sub>1 vs\<^sub>1' vs\<^sub>2 vs\<^sub>2' ws\<^sub>1' ws\<^sub>2' ?cs \<and>
                  ok_flow_aux_2 s\<^sub>1 s\<^sub>2 t\<^sub>1 t\<^sub>2 f f' vs\<^sub>1 vs\<^sub>1' ?cs \<and>
                  ok_flow_aux_3 s\<^sub>1 t\<^sub>1 f f' vs\<^sub>1 vs\<^sub>1' ws\<^sub>1 ws\<^sub>1' ws\<^sub>2 ws\<^sub>2' ?cs"
                  using R and S by auto
              qed
            qed (insert L, auto simp: no_upd_empty)
          qed
          apply (erule exE)+
          apply (erule conjE)+
          subgoal for p cfs' cfs''
          proof -
            assume "(c, s, f, vs\<^sub>0, ws\<^sub>0) \<rightarrow>*{cfs'} (SKIP, p)"
            moreover from this obtain s\<^sub>1' and vs and ws where
              S: "p = (s\<^sub>1', f, vs, ws)"
              by (blast dest: small_stepsl_stream)
            ultimately have
              T: "(c, s\<^sub>1, f, vs\<^sub>1, ws\<^sub>1) \<rightarrow>*{cfs'} (SKIP, s\<^sub>1', f, vs, ws)"
              using P by simp
            assume "(WHILE b DO c, p) \<rightarrow>*{cfs''} (c\<^sub>2, s\<^sub>2, f, vs\<^sub>2, ws\<^sub>2)"
            with S have
              U: "(WHILE b DO c, s\<^sub>1', f, vs, ws) \<rightarrow>*{cfs''}
                (c\<^sub>2, s\<^sub>2, f, vs\<^sub>2, ws\<^sub>2)"
              by simp
            assume V: "?cs' = flow cfs' @ flow cfs''"
              (is "(_ :: flow) = ?cs\<^sub>1' @ ?cs\<^sub>2'")
            have W: "(c, s\<^sub>1, f, vs\<^sub>1, ws\<^sub>1) \<rightarrow>*{[]} (c, s\<^sub>1, f, vs\<^sub>1, ws\<^sub>1)"
              by simp
            from N have "ok_flow_aux {} c SKIP s\<^sub>1 s\<^sub>1' f vs\<^sub>1 vs ws\<^sub>1 ws ?cs\<^sub>1'"
            proof
              assume X: "s \<in> Univ A (\<subseteq> state \<inter> X)"
              have Y: "s\<^sub>1 \<in> Univ B\<^sub>1 (\<subseteq> state \<inter> X)"
                using P and Q by (insert btyping2_approx [OF G X], simp)
              show ?thesis
                by (rule B [OF G [symmetric] H [symmetric] I [symmetric]
                 L J Y W T])
            next
              assume X: "s \<in> Univ C (\<subseteq> state \<inter> Y)"
              have Y: "s\<^sub>1 \<in> Univ B\<^sub>1' (\<subseteq> state \<inter> Y)"
                using P and Q by (insert btyping2_approx [OF I X], simp)
              show ?thesis
                by (rule C [OF G [symmetric] H [symmetric] I [symmetric]
                 L K Y W T])
            qed
            hence X: "ok_flow_aux {} c SKIP s\<^sub>1 s\<^sub>1' f vs\<^sub>1 vs ws\<^sub>1 ws ?cs\<^sub>1'"
              using P by simp
            assume "length cfs'' < length (tl cfs\<^sub>2)"
            hence "length ([] @ cfs'') < length (cfs\<^sub>1 @ cfs\<^sub>2)"
              by simp
            moreover have "[] @ cfs'' = [] @ cfs''" ..
            moreover from T have "(c, s, f, vs\<^sub>0, ws\<^sub>0) \<Rightarrow> (s\<^sub>1', f, vs, ws)"
              using P by (auto dest: small_stepsl_steps simp: big_iff_small)
            hence "s\<^sub>1' \<in> Univ A (\<subseteq> state \<inter> X) \<union> Univ C (\<subseteq> state \<inter> Y)"
              by (rule univ_states_while [OF _ G H I J K Q N])
            moreover have "(WHILE b DO c, s\<^sub>1', f, vs, ws) \<rightarrow>*{[]}
              (WHILE b DO c, s\<^sub>1', f, vs, ws)"
              by simp
            ultimately have
              Y: "ok_flow_aux U (WHILE b DO c) c\<^sub>2 s\<^sub>1' s\<^sub>2 f vs vs\<^sub>2 ws ws\<^sub>2 ?cs\<^sub>2'"
              using U by (rule M [rule_format])
            show ?thesis
            proof (rule conjI, clarify)
              fix t\<^sub>1 f' vs\<^sub>1' ws\<^sub>1'
              obtain c\<^sub>1'' and t\<^sub>1' and vs\<^sub>1'' and ws\<^sub>1'' where
               "ok_flow_aux_1 c SKIP c\<^sub>1'' s\<^sub>1 t\<^sub>1 t\<^sub>1' f f'
                  vs\<^sub>1 vs\<^sub>1' vs vs\<^sub>1'' ws\<^sub>1' ws\<^sub>1'' ?cs\<^sub>1' \<and>
                ok_flow_aux_2 s\<^sub>1 s\<^sub>1' t\<^sub>1 t\<^sub>1' f f' vs\<^sub>1 vs\<^sub>1' ?cs\<^sub>1' \<and>
                ok_flow_aux_3 s\<^sub>1 t\<^sub>1 f f' vs\<^sub>1 vs\<^sub>1' ws\<^sub>1 ws\<^sub>1' ws ws\<^sub>1'' ?cs\<^sub>1'"
                (is "_ \<and> ?P2 \<and> ?P3")
                using X by fastforce
              hence
               "ok_flow_aux_1 c SKIP SKIP s\<^sub>1 t\<^sub>1 t\<^sub>1' f f'
                  vs\<^sub>1 vs\<^sub>1' vs vs\<^sub>1'' ws\<^sub>1' ws\<^sub>1'' ?cs\<^sub>1'"
                (is ?P1) and ?P2 and ?P3 by auto
              obtain c\<^sub>2' and t\<^sub>2 and vs\<^sub>2' and ws\<^sub>2' where
               "ok_flow_aux_1 (WHILE b DO c) c\<^sub>2 c\<^sub>2' s\<^sub>1' t\<^sub>1' t\<^sub>2 f f'
                  vs vs\<^sub>1'' vs\<^sub>2 vs\<^sub>2' ws\<^sub>1'' ws\<^sub>2' ?cs\<^sub>2' \<and>
                ok_flow_aux_2 s\<^sub>1' s\<^sub>2 t\<^sub>1' t\<^sub>2 f f' vs vs\<^sub>1'' ?cs\<^sub>2' \<and>
                ok_flow_aux_3 s\<^sub>1' t\<^sub>1' f f' vs vs\<^sub>1'' ws ws\<^sub>1'' ws\<^sub>2 ws\<^sub>2' ?cs\<^sub>2'"
                (is "?P1' \<and> ?P2' \<and> ?P3'")
                using Y by fastforce
              hence ?P1' and ?P2' and ?P3' by auto
              show "\<exists>c\<^sub>2' t\<^sub>2 vs\<^sub>2' ws\<^sub>2'.
                ok_flow_aux_1 c\<^sub>1 c\<^sub>2 c\<^sub>2' s\<^sub>1 t\<^sub>1 t\<^sub>2 f f'
                  vs\<^sub>1 vs\<^sub>1' vs\<^sub>2 vs\<^sub>2' ws\<^sub>1' ws\<^sub>2' ?cs \<and>
                ok_flow_aux_2 s\<^sub>1 s\<^sub>2 t\<^sub>1 t\<^sub>2 f f' vs\<^sub>1 vs\<^sub>1' ?cs \<and>
                ok_flow_aux_3 s\<^sub>1 t\<^sub>1 f f' vs\<^sub>1 vs\<^sub>1' ws\<^sub>1 ws\<^sub>1' ws\<^sub>2 ws\<^sub>2' ?cs"
              proof (rule exI [of _ c\<^sub>2'], rule exI [of _ t\<^sub>2],
               rule exI [of _ vs\<^sub>2'], rule exI [of _ ws\<^sub>2'])
                {
                  fix S
                  assume
                    Z: "S \<noteq> {}" and
                    AA: "S \<subseteq> {x. s\<^sub>1 = t\<^sub>1 (\<subseteq> sources_aux
                      (\<langle>bvars b\<rangle> # ?cs\<^sub>1' @ ?cs\<^sub>2') vs\<^sub>1 s\<^sub>1 f x)}" and
                    AB: "f = f' (\<subseteq> vs\<^sub>1, vs\<^sub>1', \<Union> {tags_aux
                      (\<langle>bvars b\<rangle> # ?cs\<^sub>1' @ ?cs\<^sub>2') vs\<^sub>1 s\<^sub>1 f x | x. x \<in> S})"
                  have "\<forall>x. sources_aux (?cs\<^sub>1' @ ?cs\<^sub>2') vs\<^sub>1 s\<^sub>1 f x \<subseteq>
                    sources_aux (\<langle>bvars b\<rangle> # ?cs\<^sub>1' @ ?cs\<^sub>2') vs\<^sub>1 s\<^sub>1 f x"
                    by (blast intro: subsetD [OF sources_aux_observe_tl])
                  hence AC: "S \<subseteq> {x. s\<^sub>1 = t\<^sub>1
                    (\<subseteq> sources_aux (?cs\<^sub>1' @ ?cs\<^sub>2') vs\<^sub>1 s\<^sub>1 f x)}"
                    using AA by blast
                  moreover have "\<forall>x. sources_aux ?cs\<^sub>1' vs\<^sub>1 s\<^sub>1 f x \<subseteq>
                    sources_aux (?cs\<^sub>1' @ ?cs\<^sub>2') vs\<^sub>1 s\<^sub>1 f x"
                    by (blast intro: subsetD [OF sources_aux_append])
                  ultimately have
                    AD: "S \<subseteq> {x. s\<^sub>1 = t\<^sub>1 (\<subseteq> sources_aux ?cs\<^sub>1' vs\<^sub>1 s\<^sub>1 f x)}"
                    by blast
                  have AE: "f = f' (\<subseteq> vs\<^sub>1, vs\<^sub>1',
                    \<Union> {tags_aux (?cs\<^sub>1' @ ?cs\<^sub>2') vs\<^sub>1 s\<^sub>1 f x | x. x \<in> S})"
                    (is "_ = _ (\<subseteq> _, _, ?T)")
                    using AB by (simp add: tags_aux_observe_tl)
                  moreover have
                   "\<Union> {tags_aux ?cs\<^sub>1' vs\<^sub>1 s\<^sub>1 f x | x. x \<in> S} \<subseteq> ?T"
                    (is "?T' \<subseteq> _")
                    by (blast intro: subsetD [OF tags_aux_append])
                  ultimately have "f = f' (\<subseteq> vs\<^sub>1, vs\<^sub>1', ?T')"
                    by (rule eq_streams_subset)
                  hence
                   "(c, t\<^sub>1, f', vs\<^sub>1', ws\<^sub>1') \<rightarrow>* (SKIP, t\<^sub>1', f', vs\<^sub>1'', ws\<^sub>1'') \<and>
                    map fst [p\<leftarrow>drop (length vs\<^sub>1) vs. fst p \<in> S] =
                      map fst [p\<leftarrow>drop (length vs\<^sub>1') vs\<^sub>1''. fst p \<in> S]"
                    (is "?Q1 \<and> ?Q2")
                    using Z and AD and `?P1` by simp
                  hence ?Q1 and ?Q2 by auto
                  have "S \<subseteq> {x. s\<^sub>1' = t\<^sub>1' (\<subseteq> sources_aux ?cs\<^sub>2' vs s\<^sub>1' f x)}"
                    by (rule sources_aux_rhs [OF AC AE T `?P2`])
                  moreover have "f = f' (\<subseteq> vs, vs\<^sub>1'',
                    \<Union> {tags_aux ?cs\<^sub>2' vs s\<^sub>1' f x | x. x \<in> S})"
                    by (rule tags_aux_rhs [OF AC AE T `?Q1` `?P1`])
                  ultimately have
                   "(WHILE b DO c, t\<^sub>1', f', vs\<^sub>1'', ws\<^sub>1'') \<rightarrow>*
                      (c\<^sub>2', t\<^sub>2, f', vs\<^sub>2', ws\<^sub>2') \<and>
                    (c\<^sub>2 = SKIP) = (c\<^sub>2' = SKIP) \<and>
                    map fst [p\<leftarrow>drop (length vs) vs\<^sub>2. fst p \<in> S] =
                      map fst [p\<leftarrow>drop (length vs\<^sub>1'') vs\<^sub>2'. fst p \<in> S]"
                    (is "?Q1' \<and> ?R2 \<and> ?Q2'")
                    using Z and `?P1'` by simp
                  hence ?Q1' and ?R2 and ?Q2' by auto
                  have "s\<^sub>1 = t\<^sub>1 (\<subseteq> bvars b)"
                    by (rule eq_states_while [OF AA Z], insert L N P, simp+)
                  hence "bval b t\<^sub>1"
                    using P and Q by (blast dest: bvars_bval)
                  hence "(WHILE b DO c, t\<^sub>1, f', vs\<^sub>1', ws\<^sub>1') \<rightarrow>
                    (c;; WHILE b DO c, t\<^sub>1, f', vs\<^sub>1', ws\<^sub>1')" ..
                  moreover have "(c;; WHILE b DO c, t\<^sub>1, f', vs\<^sub>1', ws\<^sub>1') \<rightarrow>*
                    (c\<^sub>2', t\<^sub>2, f', vs\<^sub>2', ws\<^sub>2')"
                    using `?Q1` and `?Q1'`
                     by (blast intro: star_seq2 star_trans)
                  ultimately have
                   "(c\<^sub>1, t\<^sub>1, f', vs\<^sub>1', ws\<^sub>1') \<rightarrow>* (c\<^sub>2', t\<^sub>2, f', vs\<^sub>2', ws\<^sub>2')"
                    (is ?R1)
                    using P by (blast intro: star_trans)
                  moreover have
                   "map fst [p\<leftarrow>drop (length vs\<^sub>1) vs\<^sub>2. fst p \<in> S] =
                      map fst [p\<leftarrow>drop (length vs\<^sub>1') vs\<^sub>2'. fst p \<in> S]"
                    by (rule small_steps_inputs
                     [OF T U `?Q1` `?Q1'` `?Q2` `?Q2'`])
                  ultimately have "?R1 \<and> ?R2 \<and> ?this"
                    using `?R2` by simp
                }
                moreover {
                  fix S
                  assume
                    Z: "S \<noteq> {}" and
                    AA: "S \<subseteq> {x. s\<^sub>1 = t\<^sub>1 (\<subseteq> sources
                      (\<langle>bvars b\<rangle> # ?cs\<^sub>1' @ ?cs\<^sub>2') vs\<^sub>1 s\<^sub>1 f x)}" and
                    AB: "f = f' (\<subseteq> vs\<^sub>1, vs\<^sub>1', \<Union> {tags
                      (\<langle>bvars b\<rangle> # ?cs\<^sub>1' @ ?cs\<^sub>2') vs\<^sub>1 s\<^sub>1 f x | x. x \<in> S})"
                  have "\<forall>x. sources (?cs\<^sub>1' @ ?cs\<^sub>2') vs\<^sub>1 s\<^sub>1 f x \<subseteq>
                    sources (\<langle>bvars b\<rangle> # ?cs\<^sub>1' @ ?cs\<^sub>2') vs\<^sub>1 s\<^sub>1 f x"
                    by (blast intro: subsetD [OF sources_observe_tl])
                  hence AC: "S \<subseteq> {x. s\<^sub>1 = t\<^sub>1
                    (\<subseteq> sources (?cs\<^sub>1' @ ?cs\<^sub>2') vs\<^sub>1 s\<^sub>1 f x)}"
                    using AA by blast
                  have "\<forall>x. sources_aux (?cs\<^sub>1' @ ?cs\<^sub>2') vs\<^sub>1 s\<^sub>1 f x \<subseteq>
                    sources (?cs\<^sub>1' @ ?cs\<^sub>2') vs\<^sub>1 s\<^sub>1 f x"
                    by (blast intro: subsetD [OF sources_aux_sources])
                  moreover have "\<forall>x. sources_aux ?cs\<^sub>1' vs\<^sub>1 s\<^sub>1 f x \<subseteq>
                    sources_aux (?cs\<^sub>1' @ ?cs\<^sub>2') vs\<^sub>1 s\<^sub>1 f x"
                    by (blast intro: subsetD [OF sources_aux_append])
                  ultimately have
                    AD: "S \<subseteq> {x. s\<^sub>1 = t\<^sub>1 (\<subseteq> sources_aux ?cs\<^sub>1' vs\<^sub>1 s\<^sub>1 f x)}"
                    using AC by blast
                  have AE: "f = f' (\<subseteq> vs\<^sub>1, vs\<^sub>1',
                    \<Union> {tags (?cs\<^sub>1' @ ?cs\<^sub>2') vs\<^sub>1 s\<^sub>1 f x | x. x \<in> S})"
                    (is "_ = _ (\<subseteq> _, _, ?T)")
                    using AB by (simp add: tags_observe_tl)
                  have
                   "\<Union> {tags_aux (?cs\<^sub>1' @ ?cs\<^sub>2') vs\<^sub>1 s\<^sub>1 f x | x. x \<in> S} \<subseteq> ?T"
                    (is "?T' \<subseteq> _")
                    by (blast intro: subsetD [OF tags_aux_tags])
                  moreover have
                   "\<Union> {tags_aux ?cs\<^sub>1' vs\<^sub>1 s\<^sub>1 f x | x. x \<in> S} \<subseteq> ?T'"
                    (is "?T'' \<subseteq> _")
                    by (blast intro: subsetD [OF tags_aux_append])
                  ultimately have "?T'' \<subseteq> ?T"
                    by simp
                  with AE have "f = f' (\<subseteq> vs\<^sub>1, vs\<^sub>1', ?T'')"
                    by (rule eq_streams_subset)
                  hence AF: "(c, t\<^sub>1, f', vs\<^sub>1', ws\<^sub>1') \<rightarrow>*
                    (SKIP, t\<^sub>1', f', vs\<^sub>1'', ws\<^sub>1'')"
                    using Z and AD and `?P1` by simp
                  have "S \<subseteq> {x. s\<^sub>1' = t\<^sub>1' (\<subseteq> sources ?cs\<^sub>2' vs s\<^sub>1' f x)}"
                    by (rule sources_rhs [OF AC AE T `?P2`])
                  moreover have "f = f' (\<subseteq> vs, vs\<^sub>1'',
                    \<Union> {tags ?cs\<^sub>2' vs s\<^sub>1' f x | x. x \<in> S})"
                    by (rule tags_rhs [OF AC AE T AF `?P1`])
                  ultimately have "s\<^sub>2 = t\<^sub>2 (\<subseteq> S)"
                    using `?P2'` by blast
                }
                moreover {
                  fix S
                  assume
                    Z: "S \<noteq> {}" and
                    AA: "S \<subseteq> {x. s\<^sub>1 = t\<^sub>1 (\<subseteq> sources_out
                      (\<langle>bvars b\<rangle> # ?cs\<^sub>1' @ ?cs\<^sub>2') vs\<^sub>1 s\<^sub>1 f x)}" and
                    AB: "f = f' (\<subseteq> vs\<^sub>1, vs\<^sub>1', \<Union> {tags_out
                      (\<langle>bvars b\<rangle> # ?cs\<^sub>1' @ ?cs\<^sub>2') vs\<^sub>1 s\<^sub>1 f x | x. x \<in> S})"
                  have "\<forall>x. sources_out (?cs\<^sub>1' @ ?cs\<^sub>2') vs\<^sub>1 s\<^sub>1 f x \<subseteq>
                    sources_out (\<langle>bvars b\<rangle> # ?cs\<^sub>1' @ ?cs\<^sub>2') vs\<^sub>1 s\<^sub>1 f x"
                    by (blast intro: subsetD [OF sources_out_observe_tl])
                  hence AC: "S \<subseteq> {x. s\<^sub>1 = t\<^sub>1
                    (\<subseteq> sources_out (?cs\<^sub>1' @ ?cs\<^sub>2') vs\<^sub>1 s\<^sub>1 f x)}"
                    using AA by blast
                  have AD: "\<forall>x. sources_aux (?cs\<^sub>1' @ ?cs\<^sub>2') vs\<^sub>1 s\<^sub>1 f x \<subseteq>
                    sources_out (?cs\<^sub>1' @ ?cs\<^sub>2') vs\<^sub>1 s\<^sub>1 f x"
                    by (blast intro: subsetD [OF sources_aux_sources_out])
                  moreover have "\<forall>x. sources_aux ?cs\<^sub>1' vs\<^sub>1 s\<^sub>1 f x \<subseteq>
                    sources_aux (?cs\<^sub>1' @ ?cs\<^sub>2') vs\<^sub>1 s\<^sub>1 f x"
                    by (blast intro: subsetD [OF sources_aux_append])
                  ultimately have
                    AE: "S \<subseteq> {x. s\<^sub>1 = t\<^sub>1 (\<subseteq> sources_aux ?cs\<^sub>1' vs\<^sub>1 s\<^sub>1 f x)}"
                    using AC by blast
                  have AF: "f = f' (\<subseteq> vs\<^sub>1, vs\<^sub>1',
                    \<Union> {tags_out (?cs\<^sub>1' @ ?cs\<^sub>2') vs\<^sub>1 s\<^sub>1 f x | x. x \<in> S})"
                    (is "_ = _ (\<subseteq> _, _, ?T)")
                    using AB by (simp add: tags_out_observe_tl)
                  have AG:
                   "\<Union> {tags_aux (?cs\<^sub>1' @ ?cs\<^sub>2') vs\<^sub>1 s\<^sub>1 f x | x. x \<in> S} \<subseteq> ?T"
                    (is "?T' \<subseteq> _")
                    by (blast intro: subsetD [OF tags_aux_tags_out])
                  moreover have
                   "\<Union> {tags_aux ?cs\<^sub>1' vs\<^sub>1 s\<^sub>1 f x | x. x \<in> S} \<subseteq> ?T'"
                    (is "?T'' \<subseteq> _")
                    by (blast intro: subsetD [OF tags_aux_append])
                  ultimately have "?T'' \<subseteq> ?T"
                    by simp
                  with AF have "f = f' (\<subseteq> vs\<^sub>1, vs\<^sub>1', ?T'')"
                    by (rule eq_streams_subset)
                  hence AH: "(c, t\<^sub>1, f', vs\<^sub>1', ws\<^sub>1') \<rightarrow>*
                    (SKIP, t\<^sub>1', f', vs\<^sub>1'', ws\<^sub>1'')"
                    using Z and AE and `?P1` by simp
                  have AI: "S \<subseteq> {x. s\<^sub>1 = t\<^sub>1
                    (\<subseteq> sources_aux (?cs\<^sub>1' @ ?cs\<^sub>2') vs\<^sub>1 s\<^sub>1 f x)}"
                    using AC and AD by blast
                  have AJ: "f = f' (\<subseteq> vs\<^sub>1, vs\<^sub>1', ?T')"
                    using AF and AG by (rule eq_streams_subset)
                  have "S \<subseteq> {x. s\<^sub>1' = t\<^sub>1' (\<subseteq> sources_aux ?cs\<^sub>2' vs s\<^sub>1' f x)}"
                    by (rule sources_aux_rhs [OF AI AJ T `?P2`])
                  moreover have "f = f' (\<subseteq> vs, vs\<^sub>1'',
                    \<Union> {tags_aux ?cs\<^sub>2' vs s\<^sub>1' f x | x. x \<in> S})"
                    by (rule tags_aux_rhs [OF AI AJ T AH `?P1`])
                  ultimately have AK:
                   "(WHILE b DO c, t\<^sub>1', f', vs\<^sub>1'', ws\<^sub>1'') \<rightarrow>*
                      (c\<^sub>2', t\<^sub>2, f', vs\<^sub>2', ws\<^sub>2')"
                    using Z and `?P1'` by simp
                  have "\<forall>x. sources_out ?cs\<^sub>1' vs\<^sub>1 s\<^sub>1 f x \<subseteq>
                    sources_out (?cs\<^sub>1' @ ?cs\<^sub>2') vs\<^sub>1 s\<^sub>1 f x"
                    by (blast intro: subsetD [OF sources_out_append])
                  hence "S \<subseteq> {x. s\<^sub>1 = t\<^sub>1 (\<subseteq> sources_out ?cs\<^sub>1' vs\<^sub>1 s\<^sub>1 f x)}"
                    using AC by blast
                  moreover have
                   "\<Union> {tags_out ?cs\<^sub>1' vs\<^sub>1 s\<^sub>1 f x | x. x \<in> S} \<subseteq> ?T"
                    (is "?T' \<subseteq> _")
                    by (blast intro: subsetD [OF tags_out_append])
                  with AF have "f = f' (\<subseteq> vs\<^sub>1, vs\<^sub>1', ?T')"
                    by (rule eq_streams_subset)
                  ultimately have AL:
                   "[p\<leftarrow>drop (length ws\<^sub>1) ws. fst p \<in> S] =
                    [p\<leftarrow>drop (length ws\<^sub>1') ws\<^sub>1''. fst p \<in> S]"
                    using Z and `?P3` by simp
                  have "S \<subseteq> {x. s\<^sub>1' = t\<^sub>1' (\<subseteq> sources_out ?cs\<^sub>2' vs s\<^sub>1' f x)}"
                    by (rule sources_out_rhs [OF AC AF T `?P2`])
                  moreover have "f = f' (\<subseteq> vs, vs\<^sub>1'',
                    \<Union> {tags_out ?cs\<^sub>2' vs s\<^sub>1' f x | x. x \<in> S})"
                    by (rule tags_out_rhs [OF AC AF T AH `?P1`])
                  ultimately have "[p\<leftarrow>drop (length ws) ws\<^sub>2. fst p \<in> S] =
                    [p\<leftarrow>drop (length ws\<^sub>1'') ws\<^sub>2'. fst p \<in> S]"
                    using Z and `?P3'` by simp
                  hence "[p\<leftarrow>drop (length ws\<^sub>1) ws\<^sub>2. fst p \<in> S] =
                    [p\<leftarrow>drop (length ws\<^sub>1') ws\<^sub>2'. fst p \<in> S]"
                    by (rule small_steps_outputs [OF T U AH AK AL])
                }
                ultimately show
                 "ok_flow_aux_1 c\<^sub>1 c\<^sub>2 c\<^sub>2' s\<^sub>1 t\<^sub>1 t\<^sub>2 f f'
                    vs\<^sub>1 vs\<^sub>1' vs\<^sub>2 vs\<^sub>2' ws\<^sub>1' ws\<^sub>2' ?cs \<and>
                  ok_flow_aux_2 s\<^sub>1 s\<^sub>2 t\<^sub>1 t\<^sub>2 f f' vs\<^sub>1 vs\<^sub>1' ?cs \<and>
                  ok_flow_aux_3 s\<^sub>1 t\<^sub>1 f f' vs\<^sub>1 vs\<^sub>1' ws\<^sub>1 ws\<^sub>1' ws\<^sub>2 ws\<^sub>2' ?cs"
                  using R and V by auto
              qed
            qed (insert L, auto simp: no_upd_empty)
          qed
          done
      next
        assume
          Q: "\<not> bval b s" and
          R: "flow cfs\<^sub>2 = [\<langle>bvars b\<rangle>]"
            (is "?cs = _")
        assume "(c\<^sub>2, s\<^sub>2, f, vs\<^sub>2, ws\<^sub>2) = (SKIP, s, f, vs\<^sub>0, ws\<^sub>0)"
        hence S: "(c\<^sub>2, s\<^sub>2, f, vs\<^sub>2, ws\<^sub>2) = (SKIP, s\<^sub>1, f, vs\<^sub>1, ws\<^sub>1)"
          using P by simp
        show ?thesis
        proof (rule conjI, clarify)
          fix t\<^sub>1 f' vs\<^sub>1' ws\<^sub>1'
          show "\<exists>c\<^sub>2' t\<^sub>2 vs\<^sub>2' ws\<^sub>2'.
            ok_flow_aux_1 c\<^sub>1 c\<^sub>2 c\<^sub>2' s\<^sub>1 t\<^sub>1 t\<^sub>2 f f'
              vs\<^sub>1 vs\<^sub>1' vs\<^sub>2 vs\<^sub>2' ws\<^sub>1' ws\<^sub>2' ?cs \<and>
            ok_flow_aux_2 s\<^sub>1 s\<^sub>2 t\<^sub>1 t\<^sub>2 f f' vs\<^sub>1 vs\<^sub>1' ?cs \<and>
            ok_flow_aux_3 s\<^sub>1 t\<^sub>1 f f' vs\<^sub>1 vs\<^sub>1' ws\<^sub>1 ws\<^sub>1' ws\<^sub>2 ws\<^sub>2' ?cs"
          proof (rule exI [of _ SKIP], rule exI [of _ t\<^sub>1],
           rule exI [of _ vs\<^sub>1'], rule exI [of _ ws\<^sub>1'])
            {
              fix S
              assume
               "S \<subseteq> {x. s\<^sub>1 = t\<^sub>1 (\<subseteq> sources_aux [\<langle>bvars b\<rangle>] vs\<^sub>1 s\<^sub>1 f x)}" and
               "S \<noteq> {}"
              hence "s\<^sub>1 = t\<^sub>1 (\<subseteq> bvars b)"
                by (rule eq_states_while, insert L N P, simp+)
              hence "\<not> bval b t\<^sub>1"
                using P and Q by (blast dest: bvars_bval)
              hence "(c\<^sub>1, t\<^sub>1, f', vs\<^sub>1', ws\<^sub>1') \<rightarrow>* (SKIP, t\<^sub>1, f', vs\<^sub>1', ws\<^sub>1')"
                using P by simp
            }
            moreover {
              fix S
              assume "S \<subseteq> {x. s\<^sub>1 = t\<^sub>1 (\<subseteq> sources [\<langle>bvars b\<rangle>] vs\<^sub>1 s\<^sub>1 f x)}"
              moreover have "\<forall>x. sources [] vs\<^sub>1 s\<^sub>1 f x \<subseteq>
                sources [\<langle>bvars b\<rangle>] vs\<^sub>1 s\<^sub>1 f x"
                by (blast intro!: sources_observe_tl)
              ultimately have "s\<^sub>1 = t\<^sub>1 (\<subseteq> S)"
                by auto
            }
            ultimately show
             "ok_flow_aux_1 c\<^sub>1 c\<^sub>2 SKIP s\<^sub>1 t\<^sub>1 t\<^sub>1 f f'
                vs\<^sub>1 vs\<^sub>1' vs\<^sub>2 vs\<^sub>1' ws\<^sub>1' ws\<^sub>1' ?cs \<and>
              ok_flow_aux_2 s\<^sub>1 s\<^sub>2 t\<^sub>1 t\<^sub>1 f f' vs\<^sub>1 vs\<^sub>1' ?cs \<and>
              ok_flow_aux_3 s\<^sub>1 t\<^sub>1 f f' vs\<^sub>1 vs\<^sub>1' ws\<^sub>1 ws\<^sub>1' ws\<^sub>2 ws\<^sub>1' ?cs"
              using R and S by auto
          qed
        qed (insert L, auto simp: no_upd_empty)
      qed
    next
      assume P: "bval b s"
      assume "(c;; WHILE b DO c, s, f, vs\<^sub>0, ws\<^sub>0) \<rightarrow>*{tl cfs\<^sub>1}
        (c\<^sub>1, s\<^sub>1, f, vs\<^sub>1, ws\<^sub>1)"
      hence
       "(\<exists>c' cfs.
          c\<^sub>1 = c';; WHILE b DO c \<and>
          (c, s, f, vs\<^sub>0, ws\<^sub>0) \<rightarrow>*{cfs} (c', s\<^sub>1, f, vs\<^sub>1, ws\<^sub>1) \<and>
          flow (tl cfs\<^sub>1) = flow cfs) \<or>
        (\<exists>p cfs' cfs''.
          length cfs'' < length (tl cfs\<^sub>1) \<and>
          (c, s, f, vs\<^sub>0, ws\<^sub>0) \<rightarrow>*{cfs'} (SKIP, p) \<and>
          (WHILE b DO c, p) \<rightarrow>*{cfs''} (c\<^sub>1, s\<^sub>1, f, vs\<^sub>1, ws\<^sub>1) \<and>
          flow (tl cfs\<^sub>1) = flow cfs' @ flow cfs'')"
        by (rule small_stepsl_seq)
      thus ?thesis
        apply (rule disjE)
         apply (erule exE)+
         apply (erule conjE)+
        subgoal for c' cfs
        proof -
          assume
            Q: "(c, s, f, vs\<^sub>0, ws\<^sub>0) \<rightarrow>*{cfs} (c', s\<^sub>1, f, vs\<^sub>1, ws\<^sub>1)" and
            R: "c\<^sub>1 = c';; WHILE b DO c"
          hence "(c';; WHILE b DO c, s\<^sub>1, f, vs\<^sub>1, ws\<^sub>1) \<rightarrow>*{cfs\<^sub>2}
            (c\<^sub>2, s\<^sub>2, f, vs\<^sub>2, ws\<^sub>2)"
            using O by simp
          hence
           "(\<exists>c'' cfs'.
              c\<^sub>2 = c'';; WHILE b DO c \<and>
              (c', s\<^sub>1, f, vs\<^sub>1, ws\<^sub>1) \<rightarrow>*{cfs'} (c'', s\<^sub>2, f, vs\<^sub>2, ws\<^sub>2) \<and>
              flow cfs\<^sub>2 = flow cfs') \<or>
            (\<exists>p cfs' cfs''.
              length cfs'' < length cfs\<^sub>2 \<and>
              (c', s\<^sub>1, f, vs\<^sub>1, ws\<^sub>1) \<rightarrow>*{cfs'} (SKIP, p) \<and>
              (WHILE b DO c, p) \<rightarrow>*{cfs''} (c\<^sub>2, s\<^sub>2, f, vs\<^sub>2, ws\<^sub>2) \<and>
              flow cfs\<^sub>2 = flow cfs' @ flow cfs'')"
            by (rule small_stepsl_seq)
          thus ?thesis
            apply (rule disjE)
             apply (erule exE)+
             apply (erule conjE)+
            subgoal for c'' cfs'
            proof -
              assume
                S: "c\<^sub>2 = c'';; WHILE b DO c" and
                T: "(c', s\<^sub>1, f, vs\<^sub>1, ws\<^sub>1) \<rightarrow>*{cfs'} (c'', s\<^sub>2, f, vs\<^sub>2, ws\<^sub>2)" and
                U: "flow cfs\<^sub>2 = flow cfs'"
                  (is "?cs = ?cs'")
              from N have "ok_flow_aux {} c' c'' s\<^sub>1 s\<^sub>2 f vs\<^sub>1 vs\<^sub>2 ws\<^sub>1 ws\<^sub>2 ?cs'"
              proof
                assume V: "s \<in> Univ A (\<subseteq> state \<inter> X)"
                have W: "s \<in> Univ B\<^sub>1 (\<subseteq> state \<inter> X)"
                  using P by (insert btyping2_approx [OF G V], simp)
                show ?thesis
                  by (rule B [OF G [symmetric] H [symmetric] I [symmetric]
                   L J W Q T])
              next
                assume V: "s \<in> Univ C (\<subseteq> state \<inter> Y)"
                have W: "s \<in> Univ B\<^sub>1' (\<subseteq> state \<inter> Y)"
                  using P by (insert btyping2_approx [OF I V], simp)
                show ?thesis
                  by (rule C [OF G [symmetric] H [symmetric] I [symmetric]
                   L K W Q T])
              qed
              hence V: "ok_flow_aux {} c' c'' s\<^sub>1 s\<^sub>2 f vs\<^sub>1 vs\<^sub>2 ws\<^sub>1 ws\<^sub>2 ?cs"
                using U by simp
              show ?thesis
              proof (rule conjI, clarify)
                fix t\<^sub>1 f' vs\<^sub>1' ws\<^sub>1'
                obtain c\<^sub>2' and t\<^sub>2 and vs\<^sub>2' and ws\<^sub>2' where
                 "ok_flow_aux_1 c' c'' c\<^sub>2' s\<^sub>1 t\<^sub>1 t\<^sub>2 f f'
                    vs\<^sub>1 vs\<^sub>1' vs\<^sub>2 vs\<^sub>2' ws\<^sub>1' ws\<^sub>2' ?cs \<and>
                  ok_flow_aux_2 s\<^sub>1 s\<^sub>2 t\<^sub>1 t\<^sub>2 f f' vs\<^sub>1 vs\<^sub>1' ?cs \<and>
                  ok_flow_aux_3 s\<^sub>1 t\<^sub>1 f f' vs\<^sub>1 vs\<^sub>1' ws\<^sub>1 ws\<^sub>1' ws\<^sub>2 ws\<^sub>2' ?cs"
                  (is "?P1 \<and> ?P2 \<and> ?P3")
                  using V by fastforce
                hence ?P1 and ?P2 and ?P3 by auto
                show "\<exists>c\<^sub>2' t\<^sub>2 vs\<^sub>2' ws\<^sub>2'.
                  ok_flow_aux_1 c\<^sub>1 c\<^sub>2 c\<^sub>2' s\<^sub>1 t\<^sub>1 t\<^sub>2 f f'
                    vs\<^sub>1 vs\<^sub>1' vs\<^sub>2 vs\<^sub>2' ws\<^sub>1' ws\<^sub>2' ?cs \<and>
                  ok_flow_aux_2 s\<^sub>1 s\<^sub>2 t\<^sub>1 t\<^sub>2 f f' vs\<^sub>1 vs\<^sub>1' ?cs \<and>
                  ok_flow_aux_3 s\<^sub>1 t\<^sub>1 f f' vs\<^sub>1 vs\<^sub>1' ws\<^sub>1 ws\<^sub>1' ws\<^sub>2 ws\<^sub>2' ?cs"
                proof (rule exI [of _ "c\<^sub>2';; WHILE b DO c"],
                 rule exI [of _ t\<^sub>2], rule exI [of _ vs\<^sub>2'], rule exI [of _ ws\<^sub>2'])
                  {
                    fix S
                    assume "S \<noteq> {}" and
                     "S \<subseteq> {x. s\<^sub>1 = t\<^sub>1 (\<subseteq> sources_aux ?cs vs\<^sub>1 s\<^sub>1 f x)}" and
                     "f = f' (\<subseteq> vs\<^sub>1, vs\<^sub>1',
                        \<Union> {tags_aux ?cs vs\<^sub>1 s\<^sub>1 f x | x. x \<in> S})"
                    hence
                     "(c\<^sub>1, t\<^sub>1, f', vs\<^sub>1', ws\<^sub>1') \<rightarrow>*
                        (c\<^sub>2';; WHILE b DO c, t\<^sub>2, f', vs\<^sub>2', ws\<^sub>2') \<and>
                      map fst [p\<leftarrow>drop (length vs\<^sub>1) vs\<^sub>2. fst p \<in> S] =
                        map fst [p\<leftarrow>drop (length vs\<^sub>1') vs\<^sub>2'. fst p \<in> S]"
                      using R and `?P1` by (blast intro: star_seq2)
                  }
                  thus
                   "ok_flow_aux_1 c\<^sub>1 c\<^sub>2 (c\<^sub>2';; WHILE b DO c) s\<^sub>1 t\<^sub>1 t\<^sub>2 f f'
                      vs\<^sub>1 vs\<^sub>1' vs\<^sub>2 vs\<^sub>2' ws\<^sub>1' ws\<^sub>2' ?cs \<and>
                    ok_flow_aux_2 s\<^sub>1 s\<^sub>2 t\<^sub>1 t\<^sub>2 f f' vs\<^sub>1 vs\<^sub>1' ?cs \<and>
                    ok_flow_aux_3 s\<^sub>1 t\<^sub>1 f f' vs\<^sub>1 vs\<^sub>1' ws\<^sub>1 ws\<^sub>1' ws\<^sub>2 ws\<^sub>2' ?cs"
                    using S and `?P2` and `?P3` by simp
                qed
              qed (insert L, auto simp: no_upd_empty)
            qed
            apply (erule exE)+
            apply (erule conjE)+
            subgoal for p cfs' cfs''
            proof -
              assume "(c', s\<^sub>1, f, vs\<^sub>1, ws\<^sub>1) \<rightarrow>*{cfs'} (SKIP, p)"
              moreover from this obtain s\<^sub>1' and vs and ws where
                S: "p = (s\<^sub>1', f, vs, ws)"
                by (blast dest: small_stepsl_stream)
              ultimately have
                T: "(c', s\<^sub>1, f, vs\<^sub>1, ws\<^sub>1) \<rightarrow>*{cfs'} (SKIP, s\<^sub>1', f, vs, ws)"
                by simp
              assume "(WHILE b DO c, p) \<rightarrow>*{cfs''} (c\<^sub>2, s\<^sub>2, f, vs\<^sub>2, ws\<^sub>2)"
              with S have
                U: "(WHILE b DO c, s\<^sub>1', f, vs, ws) \<rightarrow>*{cfs''}
                  (c\<^sub>2, s\<^sub>2, f, vs\<^sub>2, ws\<^sub>2)"
                by simp
              assume V: "flow cfs\<^sub>2 = flow cfs' @ flow cfs''"
                (is "(?cs :: flow) = ?cs\<^sub>1 @ ?cs\<^sub>2")
              from N have
                W: "ok_flow_aux {} c' SKIP s\<^sub>1 s\<^sub>1' f vs\<^sub>1 vs ws\<^sub>1 ws ?cs\<^sub>1"
              proof
                assume X: "s \<in> Univ A (\<subseteq> state \<inter> X)"
                have Y: "s \<in> Univ B\<^sub>1 (\<subseteq> state \<inter> X)"
                  using P by (insert btyping2_approx [OF G X], simp)
                show ?thesis
                  by (rule B [OF G [symmetric] H [symmetric] I [symmetric]
                   L J Y Q T])
              next
                assume X: "s \<in> Univ C (\<subseteq> state \<inter> Y)"
                have Y: "s \<in> Univ B\<^sub>1' (\<subseteq> state \<inter> Y)"
                  using P by (insert btyping2_approx [OF I X], simp)
                show ?thesis
                  by (rule C [OF G [symmetric] H [symmetric] I [symmetric]
                   L K Y Q T])
              qed
              assume "length cfs'' < length cfs\<^sub>2"
              hence "length ([] @ cfs'') < length (cfs\<^sub>1 @ cfs\<^sub>2)"
                by simp
              moreover have "[] @ cfs'' = [] @ cfs''" ..
              moreover have
               "(c, s, f, vs\<^sub>0, ws\<^sub>0) \<rightarrow>*{cfs @ cfs'} (SKIP, s\<^sub>1', f, vs, ws)"
                using Q and T by (rule small_stepsl_append)
              hence "(c, s, f, vs\<^sub>0, ws\<^sub>0) \<Rightarrow> (s\<^sub>1', f, vs, ws)"
                by (auto dest: small_stepsl_steps simp: big_iff_small)
              hence "s\<^sub>1' \<in> Univ A (\<subseteq> state \<inter> X) \<union> Univ C (\<subseteq> state \<inter> Y)"
                by (rule univ_states_while [OF _ G H I J K P N])
              moreover have "(WHILE b DO c, s\<^sub>1', f, vs, ws) \<rightarrow>*{[]}
                (WHILE b DO c, s\<^sub>1', f, vs, ws)"
                by simp
              ultimately have X:
               "ok_flow_aux U (WHILE b DO c) c\<^sub>2 s\<^sub>1' s\<^sub>2 f vs vs\<^sub>2 ws ws\<^sub>2 ?cs\<^sub>2"
                using U by (rule M [rule_format])
              show ?thesis
              proof (rule conjI, clarify)
                fix t\<^sub>1 f' vs\<^sub>1' ws\<^sub>1'
                obtain c\<^sub>1'' and t\<^sub>1' and vs\<^sub>1'' and ws\<^sub>1'' where
                 "ok_flow_aux_1 c' SKIP c\<^sub>1'' s\<^sub>1 t\<^sub>1 t\<^sub>1' f f'
                    vs\<^sub>1 vs\<^sub>1' vs vs\<^sub>1'' ws\<^sub>1' ws\<^sub>1'' ?cs\<^sub>1 \<and>
                  ok_flow_aux_2 s\<^sub>1 s\<^sub>1' t\<^sub>1 t\<^sub>1' f f' vs\<^sub>1 vs\<^sub>1' ?cs\<^sub>1 \<and>
                  ok_flow_aux_3 s\<^sub>1 t\<^sub>1 f f' vs\<^sub>1 vs\<^sub>1' ws\<^sub>1 ws\<^sub>1' ws ws\<^sub>1'' ?cs\<^sub>1"
                  (is "_ \<and> ?P2 \<and> ?P3")
                  using W by fastforce
                hence
                 "ok_flow_aux_1 c' SKIP SKIP s\<^sub>1 t\<^sub>1 t\<^sub>1' f f'
                    vs\<^sub>1 vs\<^sub>1' vs vs\<^sub>1'' ws\<^sub>1' ws\<^sub>1'' ?cs\<^sub>1"
                  (is ?P1) and ?P2 and ?P3 by auto
                obtain c\<^sub>2' and t\<^sub>2 and vs\<^sub>2' and ws\<^sub>2' where
                 "ok_flow_aux_1 (WHILE b DO c) c\<^sub>2 c\<^sub>2' s\<^sub>1' t\<^sub>1' t\<^sub>2 f f'
                    vs vs\<^sub>1'' vs\<^sub>2 vs\<^sub>2' ws\<^sub>1'' ws\<^sub>2' ?cs\<^sub>2 \<and>
                  ok_flow_aux_2 s\<^sub>1' s\<^sub>2 t\<^sub>1' t\<^sub>2 f f' vs vs\<^sub>1'' ?cs\<^sub>2 \<and>
                  ok_flow_aux_3 s\<^sub>1' t\<^sub>1' f f' vs vs\<^sub>1'' ws ws\<^sub>1'' ws\<^sub>2 ws\<^sub>2' ?cs\<^sub>2"
                  (is "?P1' \<and> ?P2' \<and> ?P3'")
                  using X by fastforce
                hence ?P1' and ?P2' and ?P3' by auto
                show "\<exists>c\<^sub>2' t\<^sub>2 vs\<^sub>2' ws\<^sub>2'.
                  ok_flow_aux_1 c\<^sub>1 c\<^sub>2 c\<^sub>2' s\<^sub>1 t\<^sub>1 t\<^sub>2 f f'
                    vs\<^sub>1 vs\<^sub>1' vs\<^sub>2 vs\<^sub>2' ws\<^sub>1' ws\<^sub>2' ?cs \<and>
                  ok_flow_aux_2 s\<^sub>1 s\<^sub>2 t\<^sub>1 t\<^sub>2 f f' vs\<^sub>1 vs\<^sub>1' ?cs \<and>
                  ok_flow_aux_3 s\<^sub>1 t\<^sub>1 f f' vs\<^sub>1 vs\<^sub>1' ws\<^sub>1 ws\<^sub>1' ws\<^sub>2 ws\<^sub>2' ?cs"
                proof (rule exI [of _ c\<^sub>2'], rule exI [of _ t\<^sub>2],
                 rule exI [of _ vs\<^sub>2'], rule exI [of _ ws\<^sub>2'])
                  {
                    fix S
                    assume
                      Y: "S \<noteq> {}" and
                      Z: "S \<subseteq> {x. s\<^sub>1 = t\<^sub>1
                        (\<subseteq> sources_aux (?cs\<^sub>1 @ ?cs\<^sub>2) vs\<^sub>1 s\<^sub>1 f x)}" and
                      AA: "f = f' (\<subseteq> vs\<^sub>1, vs\<^sub>1',
                        \<Union> {tags_aux (?cs\<^sub>1 @ ?cs\<^sub>2) vs\<^sub>1 s\<^sub>1 f x | x. x \<in> S})"
                        (is "_ = _ (\<subseteq> _, _, ?T)")
                    have "\<forall>x. sources_aux ?cs\<^sub>1 vs\<^sub>1 s\<^sub>1 f x \<subseteq>
                      sources_aux (?cs\<^sub>1 @ ?cs\<^sub>2) vs\<^sub>1 s\<^sub>1 f x"
                      by (blast intro: subsetD [OF sources_aux_append])
                    hence "S \<subseteq> {x. s\<^sub>1 = t\<^sub>1 (\<subseteq> sources_aux ?cs\<^sub>1 vs\<^sub>1 s\<^sub>1 f x)}"
                      using Z by blast
                    moreover have
                     "\<Union> {tags_aux ?cs\<^sub>1 vs\<^sub>1 s\<^sub>1 f x | x. x \<in> S} \<subseteq> ?T"
                      (is "?T' \<subseteq> _")
                      by (blast intro: subsetD [OF tags_aux_append])
                    with AA have "f = f' (\<subseteq> vs\<^sub>1, vs\<^sub>1', ?T')"
                      by (rule eq_streams_subset)
                    ultimately have
                     "(c', t\<^sub>1, f', vs\<^sub>1', ws\<^sub>1') \<rightarrow>*
                        (SKIP, t\<^sub>1', f', vs\<^sub>1'', ws\<^sub>1'') \<and>
                      map fst [p\<leftarrow>drop (length vs\<^sub>1) vs. fst p \<in> S] =
                        map fst [p\<leftarrow>drop (length vs\<^sub>1') vs\<^sub>1''. fst p \<in> S]"
                      (is "?Q1 \<and> ?Q2")
                      using Y and `?P1` by simp
                    hence ?Q1 and ?Q2 by auto
                    have "S \<subseteq> {x. s\<^sub>1' = t\<^sub>1' (\<subseteq> sources_aux ?cs\<^sub>2 vs s\<^sub>1' f x)}"
                      by (rule sources_aux_rhs [OF Z AA T `?P2`])
                    moreover have "f = f' (\<subseteq> vs, vs\<^sub>1'',
                      \<Union> {tags_aux ?cs\<^sub>2 vs s\<^sub>1' f x | x. x \<in> S})"
                      by (rule tags_aux_rhs [OF Z AA T `?Q1` `?P1`])
                    ultimately have
                     "(WHILE b DO c, t\<^sub>1', f', vs\<^sub>1'', ws\<^sub>1'') \<rightarrow>*
                        (c\<^sub>2', t\<^sub>2, f', vs\<^sub>2', ws\<^sub>2') \<and>
                      (c\<^sub>2 = SKIP) = (c\<^sub>2' = SKIP) \<and>
                      map fst [p\<leftarrow>drop (length vs) vs\<^sub>2. fst p \<in> S] =
                        map fst [p\<leftarrow>drop (length vs\<^sub>1'') vs\<^sub>2'. fst p \<in> S]"
                      (is "?Q1' \<and> ?R2 \<and> ?Q2'")
                      using Y and `?P1'` by simp
                    hence ?Q1' and ?R2 and ?Q2' by auto
                    from R and `?Q1` and `?Q1'` have
                     "(c\<^sub>1, t\<^sub>1, f', vs\<^sub>1', ws\<^sub>1') \<rightarrow>* (c\<^sub>2', t\<^sub>2, f', vs\<^sub>2', ws\<^sub>2')"
                      (is ?R1)
                      by (blast intro: star_seq2 star_trans)
                    moreover have
                     "map fst [p\<leftarrow>drop (length vs\<^sub>1) vs\<^sub>2. fst p \<in> S] =
                        map fst [p\<leftarrow>drop (length vs\<^sub>1') vs\<^sub>2'. fst p \<in> S]"
                      by (rule small_steps_inputs
                       [OF T U `?Q1` `?Q1'` `?Q2` `?Q2'`])
                    ultimately have "?R1 \<and> ?R2 \<and> ?this"
                      using `?R2` by simp
                  }
                  moreover {
                    fix S
                    assume
                      Y: "S \<noteq> {}" and
                      Z: "S \<subseteq> {x. s\<^sub>1 = t\<^sub>1
                        (\<subseteq> sources (?cs\<^sub>1 @ ?cs\<^sub>2) vs\<^sub>1 s\<^sub>1 f x)}" and
                      AA: "f = f' (\<subseteq> vs\<^sub>1, vs\<^sub>1',
                        \<Union> {tags (?cs\<^sub>1 @ ?cs\<^sub>2) vs\<^sub>1 s\<^sub>1 f x | x. x \<in> S})"
                        (is "_ = _ (\<subseteq> _, _, ?T)")
                    have "\<forall>x. sources_aux (?cs\<^sub>1 @ ?cs\<^sub>2) vs\<^sub>1 s\<^sub>1 f x \<subseteq>
                      sources (?cs\<^sub>1 @ ?cs\<^sub>2) vs\<^sub>1 s\<^sub>1 f x"
                      by (blast intro: subsetD [OF sources_aux_sources])
                    moreover have "\<forall>x. sources_aux ?cs\<^sub>1 vs\<^sub>1 s\<^sub>1 f x \<subseteq>
                      sources_aux (?cs\<^sub>1 @ ?cs\<^sub>2) vs\<^sub>1 s\<^sub>1 f x"
                      by (blast intro: subsetD [OF sources_aux_append])
                    ultimately have
                      AB: "S \<subseteq> {x. s\<^sub>1 = t\<^sub>1 (\<subseteq> sources_aux ?cs\<^sub>1 vs\<^sub>1 s\<^sub>1 f x)}"
                      using Z by blast
                    have
                     "\<Union> {tags_aux (?cs\<^sub>1 @ ?cs\<^sub>2) vs\<^sub>1 s\<^sub>1 f x | x. x \<in> S} \<subseteq> ?T"
                      (is "?T' \<subseteq> _")
                      by (blast intro: subsetD [OF tags_aux_tags])
                    moreover have
                     "\<Union> {tags_aux ?cs\<^sub>1 vs\<^sub>1 s\<^sub>1 f x | x. x \<in> S} \<subseteq> ?T'"
                      (is "?T'' \<subseteq> _")
                      by (blast intro: subsetD [OF tags_aux_append])
                    ultimately have "?T'' \<subseteq> ?T"
                      by simp
                    with AA have "f = f' (\<subseteq> vs\<^sub>1, vs\<^sub>1', ?T'')"
                      by (rule eq_streams_subset)
                    hence AC: "(c', t\<^sub>1, f', vs\<^sub>1', ws\<^sub>1') \<rightarrow>*
                      (SKIP, t\<^sub>1', f', vs\<^sub>1'', ws\<^sub>1'')"
                      using Y and AB and `?P1` by simp
                    have "S \<subseteq> {x. s\<^sub>1' = t\<^sub>1' (\<subseteq> sources ?cs\<^sub>2 vs s\<^sub>1' f x)}"
                      by (rule sources_rhs [OF Z AA T `?P2`])
                    moreover have "f = f' (\<subseteq> vs, vs\<^sub>1'',
                      \<Union> {tags ?cs\<^sub>2 vs s\<^sub>1' f x | x. x \<in> S})"
                      by (rule tags_rhs [OF Z AA T AC `?P1`])
                    ultimately have "s\<^sub>2 = t\<^sub>2 (\<subseteq> S)"
                      using `?P2'` by blast
                  }
                  moreover {
                    fix S
                    assume
                      Y: "S \<noteq> {}" and
                      Z: "S \<subseteq> {x. s\<^sub>1 = t\<^sub>1
                        (\<subseteq> sources_out (?cs\<^sub>1 @ ?cs\<^sub>2) vs\<^sub>1 s\<^sub>1 f x)}" and
                      AA: "f = f' (\<subseteq> vs\<^sub>1, vs\<^sub>1',
                        \<Union> {tags_out (?cs\<^sub>1 @ ?cs\<^sub>2) vs\<^sub>1 s\<^sub>1 f x | x. x \<in> S})"
                        (is "_ = _ (\<subseteq> _, _, ?T)")
                    have AB: "\<forall>x. sources_aux (?cs\<^sub>1 @ ?cs\<^sub>2) vs\<^sub>1 s\<^sub>1 f x \<subseteq>
                      sources_out (?cs\<^sub>1 @ ?cs\<^sub>2) vs\<^sub>1 s\<^sub>1 f x"
                      by (blast intro: subsetD [OF sources_aux_sources_out])
                    moreover have "\<forall>x. sources_aux ?cs\<^sub>1 vs\<^sub>1 s\<^sub>1 f x \<subseteq>
                      sources_aux (?cs\<^sub>1 @ ?cs\<^sub>2) vs\<^sub>1 s\<^sub>1 f x"
                      by (blast intro: subsetD [OF sources_aux_append])
                    ultimately have
                      AC: "S \<subseteq> {x. s\<^sub>1 = t\<^sub>1 (\<subseteq> sources_aux ?cs\<^sub>1 vs\<^sub>1 s\<^sub>1 f x)}"
                      using Z by blast
                    have AD:
                     "\<Union> {tags_aux (?cs\<^sub>1 @ ?cs\<^sub>2) vs\<^sub>1 s\<^sub>1 f x | x. x \<in> S} \<subseteq> ?T"
                      (is "?T' \<subseteq> _")
                      by (blast intro: subsetD [OF tags_aux_tags_out])
                    moreover have
                     "\<Union> {tags_aux ?cs\<^sub>1 vs\<^sub>1 s\<^sub>1 f x | x. x \<in> S} \<subseteq> ?T'"
                      (is "?T'' \<subseteq> _")
                      by (blast intro: subsetD [OF tags_aux_append])
                    ultimately have "?T'' \<subseteq> ?T"
                      by simp
                    with AA have "f = f' (\<subseteq> vs\<^sub>1, vs\<^sub>1', ?T'')"
                      by (rule eq_streams_subset)
                    hence AE: "(c', t\<^sub>1, f', vs\<^sub>1', ws\<^sub>1') \<rightarrow>*
                      (SKIP, t\<^sub>1', f', vs\<^sub>1'', ws\<^sub>1'')"
                      using Y and AC and `?P1` by simp
                    have AF: "S \<subseteq> {x. s\<^sub>1 = t\<^sub>1
                      (\<subseteq> sources_aux (?cs\<^sub>1 @ ?cs\<^sub>2) vs\<^sub>1 s\<^sub>1 f x)}"
                      using Z and AB by blast
                    have AG: "f = f' (\<subseteq> vs\<^sub>1, vs\<^sub>1', ?T')"
                      using AA and AD by (rule eq_streams_subset)
                    have "S \<subseteq> {x. s\<^sub>1' = t\<^sub>1' (\<subseteq> sources_aux ?cs\<^sub>2 vs s\<^sub>1' f x)}"
                      by (rule sources_aux_rhs [OF AF AG T `?P2`])
                    moreover have "f = f' (\<subseteq> vs, vs\<^sub>1'',
                      \<Union> {tags_aux ?cs\<^sub>2 vs s\<^sub>1' f x | x. x \<in> S})"
                      by (rule tags_aux_rhs [OF AF AG T AE `?P1`])
                    ultimately have
                      AH: "(WHILE b DO c, t\<^sub>1', f', vs\<^sub>1'', ws\<^sub>1'') \<rightarrow>*
                        (c\<^sub>2', t\<^sub>2, f', vs\<^sub>2', ws\<^sub>2')"
                      using Y and `?P1'` by simp
                    have "\<forall>x. sources_out ?cs\<^sub>1 vs\<^sub>1 s\<^sub>1 f x \<subseteq>
                      sources_out (?cs\<^sub>1 @ ?cs\<^sub>2) vs\<^sub>1 s\<^sub>1 f x"
                      by (blast intro: subsetD [OF sources_out_append])
                    hence "S \<subseteq> {x. s\<^sub>1 = t\<^sub>1 (\<subseteq> sources_out ?cs\<^sub>1 vs\<^sub>1 s\<^sub>1 f x)}"
                      using Z by blast
                    moreover have
                     "\<Union> {tags_out ?cs\<^sub>1 vs\<^sub>1 s\<^sub>1 f x | x. x \<in> S} \<subseteq> ?T"
                      (is "?T' \<subseteq> _")
                      by (blast intro: subsetD [OF tags_out_append])
                    with AA have "f = f' (\<subseteq> vs\<^sub>1, vs\<^sub>1', ?T')"
                      by (rule eq_streams_subset)
                    ultimately have AI:
                     "[p\<leftarrow>drop (length ws\<^sub>1) ws. fst p \<in> S] =
                      [p\<leftarrow>drop (length ws\<^sub>1') ws\<^sub>1''. fst p \<in> S]"
                      using Y and `?P3` by simp
                    have "S \<subseteq> {x. s\<^sub>1' = t\<^sub>1' (\<subseteq> sources_out ?cs\<^sub>2 vs s\<^sub>1' f x)}"
                      by (rule sources_out_rhs [OF Z AA T `?P2`])
                    moreover have "f = f' (\<subseteq> vs, vs\<^sub>1'',
                      \<Union> {tags_out ?cs\<^sub>2 vs s\<^sub>1' f x | x. x \<in> S})"
                      by (rule tags_out_rhs [OF Z AA T AE `?P1`])
                    ultimately have "[p\<leftarrow>drop (length ws) ws\<^sub>2. fst p \<in> S] =
                      [p\<leftarrow>drop (length ws\<^sub>1'') ws\<^sub>2'. fst p \<in> S]"
                      using Y and `?P3'` by simp
                    hence "[p\<leftarrow>drop (length ws\<^sub>1) ws\<^sub>2. fst p \<in> S] =
                      [p\<leftarrow>drop (length ws\<^sub>1') ws\<^sub>2'. fst p \<in> S]"
                      by (rule small_steps_outputs [OF T U AE AH AI])
                  }
                  ultimately show
                   "ok_flow_aux_1 c\<^sub>1 c\<^sub>2 c\<^sub>2' s\<^sub>1 t\<^sub>1 t\<^sub>2 f f'
                      vs\<^sub>1 vs\<^sub>1' vs\<^sub>2 vs\<^sub>2' ws\<^sub>1' ws\<^sub>2' ?cs \<and>
                    ok_flow_aux_2 s\<^sub>1 s\<^sub>2 t\<^sub>1 t\<^sub>2 f f' vs\<^sub>1 vs\<^sub>1' ?cs \<and>
                    ok_flow_aux_3 s\<^sub>1 t\<^sub>1 f f' vs\<^sub>1 vs\<^sub>1' ws\<^sub>1 ws\<^sub>1' ws\<^sub>2 ws\<^sub>2' ?cs"
                    using V by auto
                qed
              qed (insert L, auto simp: no_upd_empty)
            qed
            done
        qed
        apply (erule exE)+
        apply (erule conjE)+
        subgoal for p cfs' cfs''
        proof -
          assume "(c, s, f, vs\<^sub>0, ws\<^sub>0) \<rightarrow>*{cfs'} (SKIP, p)"
          moreover from this obtain s\<^sub>1' and vs and ws where
            Q: "p = (s\<^sub>1', f, vs, ws)"
            by (blast dest: small_stepsl_stream)
          ultimately have
            R: "(c, s, f, vs\<^sub>0, ws\<^sub>0) \<rightarrow>*{cfs'} (SKIP, s\<^sub>1', f, vs, ws)"
            by simp
          assume "(WHILE b DO c, p) \<rightarrow>*{cfs''} (c\<^sub>1, s\<^sub>1, f, vs\<^sub>1, ws\<^sub>1)"
          with Q have S:
           "(WHILE b DO c, s\<^sub>1', f, vs, ws) \<rightarrow>*{cfs''} (c\<^sub>1, s\<^sub>1, f, vs\<^sub>1, ws\<^sub>1)"
            by simp
          assume "length cfs'' < length (tl cfs\<^sub>1)"
          hence "length (cfs'' @ cfs\<^sub>2) < length (cfs\<^sub>1 @ cfs\<^sub>2)"
            by simp
          moreover have "cfs'' @ cfs\<^sub>2 = cfs'' @ cfs\<^sub>2" ..
          moreover have "(c, s, f, vs\<^sub>0, ws\<^sub>0) \<Rightarrow> (s\<^sub>1', f, vs, ws)"
            using R by (auto dest: small_stepsl_steps simp: big_iff_small)
          hence "s\<^sub>1' \<in> Univ A (\<subseteq> state \<inter> X) \<union> Univ C (\<subseteq> state \<inter> Y)"
            by (rule univ_states_while [OF _ G H I J K P N])
          ultimately show ?thesis
            using S and O by (rule M [rule_format])
        qed
        done
    next
      assume "(c\<^sub>1, s\<^sub>1, f, vs\<^sub>1, ws\<^sub>1) = (SKIP, s, f, vs\<^sub>0, ws\<^sub>0)"
      moreover from this have
       "(c\<^sub>2, s\<^sub>2, f, vs\<^sub>2, ws\<^sub>2) = (SKIP, s\<^sub>1, f, vs\<^sub>1, ws\<^sub>1) \<and> flow cfs\<^sub>2 = []"
        using O by (blast intro!: small_stepsl_skip)
      ultimately show ?thesis
        by (insert L, fastforce)
    qed
  qed
qed

lemma ctyping2_correct_aux:
 "\<lbrakk>(U, v) \<Turnstile> c (\<subseteq> A, X) = Some (B, Y); s \<in> Univ A (\<subseteq> state \<inter> X);
    (c, s, f, vs\<^sub>0, ws\<^sub>0) \<rightarrow>*{cfs\<^sub>1} (c\<^sub>1, s\<^sub>1, f, vs\<^sub>1, ws\<^sub>1);
    (c\<^sub>1, s\<^sub>1, f, vs\<^sub>1, ws\<^sub>1) \<rightarrow>*{cfs\<^sub>2} (c\<^sub>2, s\<^sub>2, f, vs\<^sub>2, ws\<^sub>2)\<rbrakk> \<Longrightarrow>
  ok_flow_aux U c\<^sub>1 c\<^sub>2 s\<^sub>1 s\<^sub>2 f vs\<^sub>1 vs\<^sub>2 ws\<^sub>1 ws\<^sub>2 (flow cfs\<^sub>2)"
  apply (induction "(U, v)" c A X arbitrary: B Y U v c\<^sub>1 c\<^sub>2 s s\<^sub>1 s\<^sub>2
   vs\<^sub>0 vs\<^sub>1 vs\<^sub>2 ws\<^sub>0 ws\<^sub>1 ws\<^sub>2 cfs\<^sub>1 cfs\<^sub>2 rule: ctyping2.induct)
         apply fastforce
        apply (erule ctyping2_correct_aux_assign, assumption+)
       apply (erule ctyping2_correct_aux_input, assumption+)
      apply (erule ctyping2_correct_aux_output, assumption+)
     apply (erule ctyping2_correct_aux_seq, assumption+)
    apply (erule ctyping2_correct_aux_or, assumption+)
   apply (erule ctyping2_correct_aux_if, assumption+)
  apply (erule ctyping2_correct_aux_while, assumption+)
  done


theorem ctyping2_correct:
  assumes A: "(U, v) \<Turnstile> c (\<subseteq> A, X) = Some (B, Y)"
  shows "correct c A X"
proof (subst correct_def, clarify)
  fix s t c\<^sub>1 c\<^sub>2 s\<^sub>1 s\<^sub>2 f vs vs\<^sub>1 vs\<^sub>2 ws ws\<^sub>1 ws\<^sub>2 cfs\<^sub>2 t\<^sub>1 f' vs\<^sub>1' ws\<^sub>1'
  let ?cs = "flow cfs\<^sub>2"
  assume "t \<in> A" and "s = t (\<subseteq> state \<inter> X)"
  hence "s \<in> Univ A (\<subseteq> state \<inter> X)"
    by blast
  moreover assume "(c, s, f, vs, ws) \<rightarrow>* (c\<^sub>1, s\<^sub>1, f, vs\<^sub>1, ws\<^sub>1)"
  then obtain cfs\<^sub>1 where "(c, s, f, vs, ws) \<rightarrow>*{cfs\<^sub>1} (c\<^sub>1, s\<^sub>1, f, vs\<^sub>1, ws\<^sub>1)"
    by (blast dest: small_steps_stepsl)
  moreover assume "(c\<^sub>1, s\<^sub>1, f, vs\<^sub>1, ws\<^sub>1) \<rightarrow>*{cfs\<^sub>2} (c\<^sub>2, s\<^sub>2, f, vs\<^sub>2, ws\<^sub>2)"
  ultimately have "ok_flow_aux U c\<^sub>1 c\<^sub>2 s\<^sub>1 s\<^sub>2 f vs\<^sub>1 vs\<^sub>2 ws\<^sub>1 ws\<^sub>2 ?cs"
    by (rule ctyping2_correct_aux [OF A])
  then obtain c\<^sub>2' and t\<^sub>2 and vs\<^sub>2' and ws\<^sub>2' where
   "ok_flow_aux_1 c\<^sub>1 c\<^sub>2 c\<^sub>2' s\<^sub>1 t\<^sub>1 t\<^sub>2 f f' vs\<^sub>1 vs\<^sub>1' vs\<^sub>2 vs\<^sub>2' ws\<^sub>1' ws\<^sub>2' ?cs \<and>
    ok_flow_aux_2 s\<^sub>1 s\<^sub>2 t\<^sub>1 t\<^sub>2 f f' vs\<^sub>1 vs\<^sub>1' ?cs \<and>
    ok_flow_aux_3 s\<^sub>1 t\<^sub>1 f f' vs\<^sub>1 vs\<^sub>1' ws\<^sub>1 ws\<^sub>1' ws\<^sub>2 ws\<^sub>2' ?cs"
    (is "?P1 \<and> ?P2 \<and> ?P3")
    by fastforce
  hence ?P1 and ?P2 and ?P3 by auto
  show "\<exists>c\<^sub>2' t\<^sub>2 vs\<^sub>2' ws\<^sub>2'.
    ok_flow_1 c\<^sub>1 c\<^sub>2 c\<^sub>2' s\<^sub>1 s\<^sub>2 t\<^sub>1 t\<^sub>2 f f' vs\<^sub>1 vs\<^sub>1' vs\<^sub>2 vs\<^sub>2' ws\<^sub>1' ws\<^sub>2' ?cs \<and>
    ok_flow_2 c\<^sub>1 c\<^sub>2 c\<^sub>2' s\<^sub>1 t\<^sub>1 t\<^sub>2 f f' vs\<^sub>1 vs\<^sub>1' vs\<^sub>2 vs\<^sub>2' ws\<^sub>1 ws\<^sub>1' ws\<^sub>2 ws\<^sub>2' ?cs"
  proof (rule exI [of _ c\<^sub>2'], rule exI [of _ t\<^sub>2],
   rule exI [of _ vs\<^sub>2'], rule exI [of _ ws\<^sub>2'])
    {
      fix S
      assume
        B: "S \<noteq> {}" and
        C: "S \<subseteq> {x. s\<^sub>1 = t\<^sub>1 (\<subseteq> sources ?cs vs\<^sub>1 s\<^sub>1 f x)}" and
        D: "f = f' (\<subseteq> vs\<^sub>1, vs\<^sub>1', \<Union> {tags ?cs vs\<^sub>1 s\<^sub>1 f x | x. x \<in> S})"
          (is "_ = _ (\<subseteq> _, _, ?T)")
      have "\<forall>x. sources_aux ?cs vs\<^sub>1 s\<^sub>1 f x \<subseteq> sources ?cs vs\<^sub>1 s\<^sub>1 f x"
        by (blast intro: subsetD [OF sources_aux_sources])
      hence "S \<subseteq> {x. s\<^sub>1 = t\<^sub>1 (\<subseteq> sources_aux ?cs vs\<^sub>1 s\<^sub>1 f x)}"
        using C by blast
      moreover have "\<Union> {tags_aux ?cs vs\<^sub>1 s\<^sub>1 f x | x. x \<in> S} \<subseteq> ?T"
        (is "?T' \<subseteq> _")
        by (blast intro: subsetD [OF tags_aux_tags])
      with D have "f = f' (\<subseteq> vs\<^sub>1, vs\<^sub>1', ?T')"
        by (rule eq_streams_subset)
      ultimately have
       "(c\<^sub>1, t\<^sub>1, f', vs\<^sub>1', ws\<^sub>1') \<rightarrow>* (c\<^sub>2', t\<^sub>2, f', vs\<^sub>2', ws\<^sub>2') \<and>
        (c\<^sub>2 = SKIP) = (c\<^sub>2' = SKIP) \<and>
        map fst [p\<leftarrow>drop (length vs\<^sub>1) vs\<^sub>2. fst p \<in> S] =
          map fst [p\<leftarrow>drop (length vs\<^sub>1') vs\<^sub>2'. fst p \<in> S]"
        (is ?Q)
        using B and `?P1` by simp
      moreover have "s\<^sub>2 = t\<^sub>2 (\<subseteq> S)"
        using B and C and D and `?P2` by simp
      ultimately have "?Q \<and> ?this" ..
    }
    moreover {
      fix S
      assume
        B: "S \<noteq> {}" and
        C: "S \<subseteq> {x. s\<^sub>1 = t\<^sub>1 (\<subseteq> sources_out ?cs vs\<^sub>1 s\<^sub>1 f x)}" and
        D: "f = f' (\<subseteq> vs\<^sub>1, vs\<^sub>1', \<Union> {tags_out ?cs vs\<^sub>1 s\<^sub>1 f x | x. x \<in> S})"
          (is "_ = _ (\<subseteq> _, _, ?T)")
      have "\<forall>x. sources_aux ?cs vs\<^sub>1 s\<^sub>1 f x \<subseteq> sources_out ?cs vs\<^sub>1 s\<^sub>1 f x"
        by (blast intro: subsetD [OF sources_aux_sources_out])
      hence "S \<subseteq> {x. s\<^sub>1 = t\<^sub>1 (\<subseteq> sources_aux ?cs vs\<^sub>1 s\<^sub>1 f x)}"
        using C by blast
      moreover have "\<Union> {tags_aux ?cs vs\<^sub>1 s\<^sub>1 f x | x. x \<in> S} \<subseteq> ?T"
        (is "?T' \<subseteq> _")
        by (blast intro: subsetD [OF tags_aux_tags_out])
      with D have "f = f' (\<subseteq> vs\<^sub>1, vs\<^sub>1', ?T')"
        by (rule eq_streams_subset)
      ultimately have
       "(c\<^sub>1, t\<^sub>1, f', vs\<^sub>1', ws\<^sub>1') \<rightarrow>* (c\<^sub>2', t\<^sub>2, f', vs\<^sub>2', ws\<^sub>2') \<and>
        (c\<^sub>2 = SKIP) = (c\<^sub>2' = SKIP) \<and>
        map fst [p\<leftarrow>drop (length vs\<^sub>1) vs\<^sub>2. fst p \<in> S] =
          map fst [p\<leftarrow>drop (length vs\<^sub>1') vs\<^sub>2'. fst p \<in> S]"
        (is ?Q)
        using B and `?P1` by simp
      moreover have
       "[p\<leftarrow>drop (length ws\<^sub>1) ws\<^sub>2. fst p \<in> S] =
          [p\<leftarrow>drop (length ws\<^sub>1') ws\<^sub>2'. fst p \<in> S]"
        using B and C and D and `?P3` by simp
      ultimately have "?Q \<and> ?this" ..
    }
    ultimately show
     "ok_flow_1 c\<^sub>1 c\<^sub>2 c\<^sub>2' s\<^sub>1 s\<^sub>2 t\<^sub>1 t\<^sub>2 f f' vs\<^sub>1 vs\<^sub>1' vs\<^sub>2 vs\<^sub>2' ws\<^sub>1' ws\<^sub>2' ?cs \<and>
      ok_flow_2 c\<^sub>1 c\<^sub>2 c\<^sub>2' s\<^sub>1 t\<^sub>1 t\<^sub>2 f f' vs\<^sub>1 vs\<^sub>1' vs\<^sub>2 vs\<^sub>2' ws\<^sub>1 ws\<^sub>1' ws\<^sub>2 ws\<^sub>2' ?cs"
      by auto
  qed
qed

end

end
