(*  Title:       Information Flow Control via Stateful Intransitive Noninterference in Language IMP
    Author:      Pasquale Noce
                 Senior Staff Firmware Engineer at HID Global, Italy
                 pasquale dot noce dot lavoro at gmail dot com
                 pasquale dot noce at hidglobal dot com
*)

section "Sufficiency of well-typedness for information flow correctness"

theory Correctness
  imports Overapproximation
begin

text \<open>
\null

The purpose of this section is to prove that type system @{const [names_short] noninterf.ctyping2}
is correct in that it guarantees that well-typed programs satisfy the information flow correctness
criterion expressed by predicate @{const [names_short] noninterf.correct}, namely that if the type
system outputs a value other than @{const None} (that is, a \emph{pass} verdict) when it is input
program @{term c}, @{typ "state set"} @{term A}, and @{typ "vname set"} @{term X}, then
@{prop "correct c A X"} (theorem @{text ctyping2_correct}).

This proof makes use of the lemmas @{text ctyping1_idem} and @{text ctyping2_approx} proven in the
previous sections.
\<close>


subsection "Global context proofs"

lemma flow_append_1:
  assumes A: "\<And>cfs' :: (com \<times> state) list.
    c # map fst (cfs :: (com \<times> state) list) = map fst cfs' \<Longrightarrow>
      flow_aux (map fst cfs' @ map fst cfs'') =
      flow_aux (map fst cfs') @ flow_aux (map fst cfs'')"
  shows "flow_aux (c # map fst cfs @ map fst cfs'') =
    flow_aux (c # map fst cfs) @ flow_aux (map fst cfs'')"
using A [of "(c, \<lambda>x. 0) # cfs"] by simp

lemma flow_append:
 "flow (cfs @ cfs') = flow cfs @ flow cfs'"
by (simp add: flow_def, induction "map fst cfs" arbitrary: cfs
 rule: flow_aux.induct, auto, rule flow_append_1)

lemma flow_cons:
 "flow (cf # cfs) = flow_aux (fst cf # []) @ flow cfs"
by (subgoal_tac "cf # cfs = [cf] @ cfs", simp only: flow_append,
 simp_all add: flow_def)

lemma small_stepsl_append:
 "\<lbrakk>(c, s) \<rightarrow>*{cfs} (c', s'); (c', s') \<rightarrow>*{cfs'} (c'', s'')\<rbrakk> \<Longrightarrow>
    (c, s) \<rightarrow>*{cfs @ cfs'} (c'', s'')"
by (induction c' s' cfs' c'' s'' rule: small_stepsl_induct,
 simp, simp only: append_assoc [symmetric] small_stepsl.simps)


lemma small_stepsl_cons_1:
 "(c, s) \<rightarrow>*{[cf]} (c'', s'') \<Longrightarrow>
    cf = (c, s) \<and>
    (\<exists>c' s'. (c, s) \<rightarrow> (c', s') \<and> (c', s') \<rightarrow>*{[]} (c'', s''))"
by (subst (asm) append_Nil [symmetric],
 simp only: small_stepsl.simps, simp)

lemma small_stepsl_cons_2:
 "\<lbrakk>(c, s) \<rightarrow>*{cf # cfs} (c'', s'') \<Longrightarrow>
    cf = (c, s) \<and>
    (\<exists>c' s'. (c, s) \<rightarrow> (c', s') \<and> (c', s') \<rightarrow>*{cfs} (c'', s''));
  (c, s) \<rightarrow>*{cf # cfs @ [(c'', s'')]} (c''', s''')\<rbrakk> \<Longrightarrow>
    cf = (c, s) \<and>
    (\<exists>c' s'. (c, s) \<rightarrow> (c', s') \<and>
      (c', s') \<rightarrow>*{cfs @ [(c'', s'')]} (c''', s'''))"
by (simp only: append_Cons [symmetric],
 simp only: small_stepsl.simps, simp)

lemma small_stepsl_cons:
 "(c, s) \<rightarrow>*{cf # cfs} (c'', s'') \<Longrightarrow>
    cf = (c, s) \<and>
    (\<exists>c' s'. (c, s) \<rightarrow> (c', s') \<and> (c', s') \<rightarrow>*{cfs} (c'', s''))"
by (induction c s cfs c'' s'' rule: small_stepsl_induct,
 erule small_stepsl_cons_1, rule small_stepsl_cons_2)


lemma small_steps_stepsl_1:
 "\<exists>cfs. (c, s) \<rightarrow>*{cfs} (c, s)"
by (rule exI [of _ "[]"], simp)

lemma small_steps_stepsl_2:
 "\<lbrakk>(c, s) \<rightarrow> (c', s'); (c', s') \<rightarrow>*{cfs} (c'', s'')\<rbrakk> \<Longrightarrow>
    \<exists>cfs'. (c, s) \<rightarrow>*{cfs'} (c'', s'')"
by (rule exI [of _ "[(c, s)] @ cfs"], rule small_stepsl_append
 [where c' = c' and s' = s'], subst append_Nil [symmetric],
 simp only: small_stepsl.simps)

lemma small_steps_stepsl:
 "(c, s) \<rightarrow>* (c', s') \<Longrightarrow> \<exists>cfs. (c, s) \<rightarrow>*{cfs} (c', s')"
by (induction c s c' s' rule: star_induct,
 rule small_steps_stepsl_1, blast intro: small_steps_stepsl_2)

lemma small_stepsl_steps:
 "(c, s) \<rightarrow>*{cfs} (c', s') \<Longrightarrow> (c, s) \<rightarrow>* (c', s')"
by (induction c s cfs c' s' rule: small_stepsl_induct,
 auto intro: star_trans)

lemma small_stepsl_skip:
 "(SKIP, s) \<rightarrow>*{cfs} (c, t) \<Longrightarrow>
    (c, t) = (SKIP, s) \<and> flow cfs = []"
by (induction SKIP s cfs c t rule: small_stepsl_induct,
 auto simp: flow_def)


lemma small_stepsl_assign_1:
 "(x ::= a, s) \<rightarrow>*{[]} (c', s') \<Longrightarrow>
    (c', s') = (x ::= a, s) \<and> flow [] = [] \<or>
    (c', s') = (SKIP, s(x := aval a s)) \<and> flow [] = [x ::= a]"
by (simp add: flow_def)

lemma small_stepsl_assign_2:
 "\<lbrakk>(x ::= a, s) \<rightarrow>*{cfs} (c', s') \<Longrightarrow>
    (c', s') = (x ::= a, s) \<and> flow cfs = [] \<or>
      (c', s') = (SKIP, s(x := aval a s)) \<and> flow cfs = [x ::= a];
    (x ::= a, s) \<rightarrow>*{cfs @ [(c', s')]} (c'', s'')\<rbrakk> \<Longrightarrow>
  (c'', s'') = (x ::= a, s) \<and>
    flow (cfs @ [(c', s')]) = [] \<or>
  (c'', s'') = (SKIP, s(x := aval a s)) \<and>
    flow (cfs @ [(c', s')]) = [x ::= a]"
by (auto, (simp add: flow_append, simp add: flow_def)+)

lemma small_stepsl_assign:
 "(x ::= a, s) \<rightarrow>*{cfs} (c, t) \<Longrightarrow>
    (c, t) = (x ::= a, s) \<and> flow cfs = [] \<or>
    (c, t) = (SKIP, s(x := aval a s)) \<and> flow cfs = [x ::= a]"
by (induction "x ::= a :: com" s cfs c t rule: small_stepsl_induct,
 erule small_stepsl_assign_1, rule small_stepsl_assign_2)


lemma small_stepsl_seq_1:
 "(c\<^sub>1;; c\<^sub>2, s) \<rightarrow>*{[]} (c', s') \<Longrightarrow>
    (\<exists>c'' cfs'. c' = c'';; c\<^sub>2 \<and>
      (c\<^sub>1, s) \<rightarrow>*{cfs'} (c'', s') \<and>
      flow [] = flow cfs') \<or>
    (\<exists>s'' cfs' cfs''. length cfs'' < length [] \<and>
      (c\<^sub>1, s) \<rightarrow>*{cfs'} (SKIP, s'') \<and>
      (c\<^sub>2, s'') \<rightarrow>*{cfs''} (c', s') \<and>
      flow [] = flow cfs' @ flow cfs'')"
by force

lemma small_stepsl_seq_2:
  assumes
    A: "(c\<^sub>1;; c\<^sub>2, s) \<rightarrow>*{cfs} (c', s') \<Longrightarrow>
      (\<exists>c'' cfs'. c' = c'';; c\<^sub>2 \<and>
        (c\<^sub>1, s) \<rightarrow>*{cfs'} (c'', s') \<and>
        flow cfs = flow cfs') \<or>
      (\<exists>s'' cfs' cfs''. length cfs'' < length cfs \<and>
        (c\<^sub>1, s) \<rightarrow>*{cfs'} (SKIP, s'') \<and>
        (c\<^sub>2, s'') \<rightarrow>*{cfs''} (c', s') \<and>
        flow cfs = flow cfs' @ flow cfs'')" and
    B: "(c\<^sub>1;; c\<^sub>2, s) \<rightarrow>*{cfs @ [(c', s')]} (c'', s'')"
  shows
   "(\<exists>d cfs'. c'' = d;; c\<^sub>2 \<and>
      (c\<^sub>1, s) \<rightarrow>*{cfs'} (d, s'') \<and>
      flow (cfs @ [(c', s')]) = flow cfs') \<or>
    (\<exists>t cfs' cfs''. length cfs'' < length (cfs @ [(c', s')]) \<and>
      (c\<^sub>1, s) \<rightarrow>*{cfs'} (SKIP, t) \<and>
      (c\<^sub>2, t) \<rightarrow>*{cfs''} (c'', s'') \<and>
      flow (cfs @ [(c', s')]) = flow cfs' @ flow cfs'')"
    (is "?P \<or> ?Q")
proof -
  {
    assume C: "(c', s') \<rightarrow> (c'', s'')"
    assume
     "(\<exists>d. c' = d;; c\<^sub>2 \<and> (\<exists>cfs'.
        (c\<^sub>1, s) \<rightarrow>*{cfs'} (d, s') \<and>
        flow cfs = flow cfs')) \<or>
      (\<exists>t cfs' cfs''. length cfs'' < length cfs \<and>
        (c\<^sub>1, s) \<rightarrow>*{cfs'} (SKIP, t) \<and>
        (c\<^sub>2, t) \<rightarrow>*{cfs''} (c', s') \<and>
        flow cfs = flow cfs' @ flow cfs'')"
      (is "(\<exists>d. ?R d \<and> (\<exists>cfs'. ?S d cfs')) \<or>
        (\<exists>t cfs' cfs''. ?T t cfs' cfs'')")
    hence ?thesis
    proof
      assume "\<exists>c''. ?R c'' \<and> (\<exists>cfs'. ?S c'' cfs')"
      then obtain d and cfs' where
        D: "c' = d;; c\<^sub>2" and
        E: "(c\<^sub>1, s) \<rightarrow>*{cfs'} (d, s')" and
        F: "flow cfs = flow cfs'"
        by blast
      hence "(d;; c\<^sub>2, s') \<rightarrow> (c'', s'')"
        using C by simp
      moreover {
        assume
          G: "d = SKIP" and
          H: "(c'', s'') = (c\<^sub>2, s')"
        have ?Q
        proof (rule exI [of _ s'], rule exI [of _ cfs'],
         rule exI [of _ "[]"])
          from D and E and F and G and H show
           "length [] < length (cfs @ [(c', s')]) \<and>
            (c\<^sub>1, s) \<rightarrow>*{cfs'} (SKIP, s') \<and>
            (c\<^sub>2, s') \<rightarrow>*{[]} (c'', s'') \<and>
            flow (cfs @ [(c', s')]) = flow cfs' @ flow []"
            by (simp add: flow_append, simp add: flow_def)
        qed
      }
      moreover {
        fix d' t'
        assume
          G: "(d, s') \<rightarrow> (d', t')" and
          H: "(c'', s'') = (d';; c\<^sub>2, t')"
        have ?P
        proof (rule exI [of _ d'], rule exI [of _ "cfs' @ [(d, s')]"])
          from D and E and F and G and H show
           "c'' = d';; c\<^sub>2 \<and>
            (c\<^sub>1, s) \<rightarrow>*{cfs' @ [(d, s')]} (d', s'') \<and>
            flow (cfs @ [(c', s')]) = flow (cfs' @ [(d, s')])"
            by (simp add: flow_append, simp add: flow_def)
        qed
      }
      ultimately show ?thesis
        by blast
    next
      assume "\<exists>t cfs' cfs''. ?T t cfs' cfs''"
      then obtain t and cfs' and cfs'' where
        D: "length cfs'' < length cfs" and
        E: "(c\<^sub>1, s) \<rightarrow>*{cfs'} (SKIP, t)" and
        F: "(c\<^sub>2, t) \<rightarrow>*{cfs''} (c', s')" and
        G: "flow cfs = flow cfs' @ flow cfs''"
        by blast
      show ?thesis
      proof (rule disjI2, rule exI [of _ t], rule exI [of _ cfs'],
       rule exI [of _ "cfs'' @ [(c', s')]"])
        from C and D and E and F and G show
         "length (cfs'' @ [(c', s')]) < length (cfs @ [(c', s')]) \<and>
          (c\<^sub>1, s) \<rightarrow>*{cfs'} (SKIP, t) \<and>
          (c\<^sub>2, t) \<rightarrow>*{cfs'' @ [(c', s')]} (c'', s'') \<and>
          flow (cfs @ [(c', s')]) =
            flow cfs' @ flow (cfs'' @ [(c', s')])"
          by (simp add: flow_append)
      qed
    qed
  }
  with A and B show ?thesis
    by simp
qed

lemma small_stepsl_seq:
 "(c\<^sub>1;; c\<^sub>2, s) \<rightarrow>*{cfs} (c, t) \<Longrightarrow>
    (\<exists>c' cfs'. c = c';; c\<^sub>2 \<and>
      (c\<^sub>1, s) \<rightarrow>*{cfs'} (c', t) \<and>
      flow cfs = flow cfs') \<or>
    (\<exists>s' cfs' cfs''. length cfs'' < length cfs \<and>
      (c\<^sub>1, s) \<rightarrow>*{cfs'} (SKIP, s') \<and> (c\<^sub>2, s') \<rightarrow>*{cfs''} (c, t) \<and>
      flow cfs = flow cfs' @ flow cfs'')"
by (induction "c\<^sub>1;; c\<^sub>2" s cfs c t arbitrary: c\<^sub>1 c\<^sub>2
 rule: small_stepsl_induct, erule small_stepsl_seq_1,
 rule small_stepsl_seq_2)


lemma small_stepsl_if_1:
 "(IF b THEN c\<^sub>1 ELSE c\<^sub>2, s) \<rightarrow>*{[]} (c', s') \<Longrightarrow>
    (c', s') = (IF b THEN c\<^sub>1 ELSE c\<^sub>2, s) \<and>
      flow [] = [] \<or>
    bval b s \<and> (c\<^sub>1, s) \<rightarrow>*{tl []} (c', s') \<and>
      flow [] = \<langle>bvars b\<rangle> # flow (tl []) \<or>
    \<not> bval b s \<and> (c\<^sub>2, s) \<rightarrow>*{tl []} (c', s') \<and>
      flow [] = \<langle>bvars b\<rangle> # flow (tl [])"
by (simp add: flow_def)

lemma small_stepsl_if_2:
  assumes
    A: "(IF b THEN c\<^sub>1 ELSE c\<^sub>2, s) \<rightarrow>*{cfs} (c', s') \<Longrightarrow>
      (c', s') = (IF b THEN c\<^sub>1 ELSE c\<^sub>2, s) \<and>
        flow cfs = [] \<or>
      bval b s \<and> (c\<^sub>1, s) \<rightarrow>*{tl cfs} (c', s') \<and>
        flow cfs = \<langle>bvars b\<rangle> # flow (tl cfs) \<or>
      \<not> bval b s \<and> (c\<^sub>2, s) \<rightarrow>*{tl cfs} (c', s') \<and>
        flow cfs = \<langle>bvars b\<rangle> # flow (tl cfs)" and
    B: "(IF b THEN c\<^sub>1 ELSE c\<^sub>2, s) \<rightarrow>*{cfs @ [(c', s')]} (c'', s'')"
  shows
   "(c'', s'') = (IF b THEN c\<^sub>1 ELSE c\<^sub>2, s) \<and>
      flow (cfs @ [(c', s')]) = [] \<or>
    bval b s \<and> (c\<^sub>1, s) \<rightarrow>*{tl (cfs @ [(c', s')])} (c'', s'') \<and>
      flow (cfs @ [(c', s')]) = \<langle>bvars b\<rangle> # flow (tl (cfs @ [(c', s')])) \<or>
    \<not> bval b s \<and> (c\<^sub>2, s) \<rightarrow>*{tl (cfs @ [(c', s')])} (c'', s'') \<and>
      flow (cfs @ [(c', s')]) = \<langle>bvars b\<rangle> # flow (tl (cfs @ [(c', s')]))"
    (is "_ \<or> ?P")
proof -
  {
    assume
      C: "(IF b THEN c\<^sub>1 ELSE c\<^sub>2, s) \<rightarrow>*{cfs} (c', s')" and
      D: "(c', s') \<rightarrow> (c'', s'')"
    assume
     "c' = IF b THEN c\<^sub>1 ELSE c\<^sub>2 \<and> s' = s \<and>
        flow cfs = [] \<or>
      bval b s \<and> (c\<^sub>1, s) \<rightarrow>*{tl cfs} (c', s') \<and>
        flow cfs = \<langle>bvars b\<rangle> # flow (tl cfs) \<or>
      \<not> bval b s \<and> (c\<^sub>2, s) \<rightarrow>*{tl cfs} (c', s') \<and>
        flow cfs = \<langle>bvars b\<rangle> # flow (tl cfs)"
      (is "?Q \<or> ?R \<or> ?S")
    hence ?P
    proof (rule disjE, erule_tac [2] disjE)
      assume ?Q
      moreover from this have "(IF b THEN c\<^sub>1 ELSE c\<^sub>2, s) \<rightarrow> (c'', s'')"
        using D by simp
      ultimately show ?thesis
        using C by (erule_tac IfE, auto dest: small_stepsl_cons
         simp: tl_append flow_cons split: list.split)
    next
      assume ?R
      with C and D show ?thesis
        by (auto simp: tl_append flow_cons split: list.split)
    next
      assume ?S
      with C and D show ?thesis
        by (auto simp: tl_append flow_cons split: list.split)
    qed
  }
  with A and B show ?thesis
    by simp
qed

lemma small_stepsl_if:
 "(IF b THEN c\<^sub>1 ELSE c\<^sub>2, s) \<rightarrow>*{cfs} (c, t) \<Longrightarrow>
    (c, t) = (IF b THEN c\<^sub>1 ELSE c\<^sub>2, s) \<and>
      flow cfs = [] \<or>
    bval b s \<and> (c\<^sub>1, s) \<rightarrow>*{tl cfs} (c, t) \<and>
      flow cfs = \<langle>bvars b\<rangle> # flow (tl cfs) \<or>
    \<not> bval b s \<and> (c\<^sub>2, s) \<rightarrow>*{tl cfs} (c, t) \<and>
      flow cfs = \<langle>bvars b\<rangle> # flow (tl cfs)"
by (induction "IF b THEN c\<^sub>1 ELSE c\<^sub>2" s cfs c t arbitrary: b c\<^sub>1 c\<^sub>2
 rule: small_stepsl_induct, erule small_stepsl_if_1,
 rule small_stepsl_if_2)


lemma small_stepsl_while_1:
 "(WHILE b DO c, s) \<rightarrow>*{[]} (c', s') \<Longrightarrow>
    (c', s') = (WHILE b DO c, s) \<and> flow [] = [] \<or>
    (IF b THEN c;; WHILE b DO c ELSE SKIP, s) \<rightarrow>*{tl []} (c', s') \<and>
      flow [] = flow (tl [])"
by (simp add: flow_def)

lemma small_stepsl_while_2:
  assumes
    A: "(WHILE b DO c, s) \<rightarrow>*{cfs} (c', s') \<Longrightarrow>
      (c', s') = (WHILE b DO c, s) \<and>
        flow cfs = [] \<or>
      (IF b THEN c;; WHILE b DO c ELSE SKIP, s) \<rightarrow>*{tl cfs} (c', s') \<and>
        flow cfs = flow (tl cfs)" and
    B: "(WHILE b DO c, s) \<rightarrow>*{cfs @ [(c', s')]} (c'', s'')"
  shows
   "(c'', s'') = (WHILE b DO c, s) \<and>
      flow (cfs @ [(c', s')]) = [] \<or>
    (IF b THEN c;; WHILE b DO c ELSE SKIP, s)
      \<rightarrow>*{tl (cfs @ [(c', s')])} (c'', s'') \<and>
      flow (cfs @ [(c', s')]) = flow (tl (cfs @ [(c', s')]))"
    (is "_ \<or> ?P")
proof -
  {
    assume
      C: "(WHILE b DO c, s) \<rightarrow>*{cfs} (c', s')" and
      D: "(c', s') \<rightarrow> (c'', s'')"
    assume
     "c' = WHILE b DO c \<and> s' = s \<and>
        flow cfs = [] \<or>
      (IF b THEN c;; WHILE b DO c ELSE SKIP, s) \<rightarrow>*{tl cfs} (c', s') \<and>
        flow cfs = flow (tl cfs)"
      (is "?Q \<or> ?R")
    hence ?P
    proof
      assume ?Q
      moreover from this have "(WHILE b DO c, s) \<rightarrow> (c'', s'')"
        using D by simp
      ultimately show ?thesis
        using C by (erule_tac WhileE, auto dest: small_stepsl_cons
         simp: tl_append flow_cons split: list.split)
    next
      assume ?R
      with C and D show ?thesis
        by (auto simp: tl_append flow_cons split: list.split)
    qed
  }
  with A and B show ?thesis
    by simp
qed

lemma small_stepsl_while:
 "(WHILE b DO c, s) \<rightarrow>*{cfs} (c', s') \<Longrightarrow>
    (c', s') = (WHILE b DO c, s) \<and>
      flow cfs = [] \<or>
    (IF b THEN c;; WHILE b DO c ELSE SKIP, s) \<rightarrow>*{tl cfs} (c', s') \<and>
      flow cfs = flow (tl cfs)"
by (induction "WHILE b DO c" s cfs c' s' arbitrary: b c
 rule: small_stepsl_induct, erule small_stepsl_while_1,
 rule small_stepsl_while_2)


lemma bvars_bval:
 "s = t (\<subseteq> bvars b) \<Longrightarrow> bval b s = bval b t"
by (induction b, simp_all, rule arg_cong2, auto intro: avars_aval)

lemma run_flow_append:
 "run_flow (cs @ cs') s = run_flow cs' (run_flow cs s)"
by (induction cs s rule: run_flow.induct, simp_all (no_asm))

lemma no_upd_append:
 "no_upd (cs @ cs') x = (no_upd cs x \<and> no_upd cs' x)"
by (induction cs, simp_all)

lemma no_upd_run_flow:
 "no_upd cs x \<Longrightarrow> run_flow cs s x = s x"
by (induction cs s rule: run_flow.induct, auto)

lemma small_stepsl_run_flow_1:
 "(c, s) \<rightarrow>*{[]} (c', s') \<Longrightarrow> s' = run_flow (flow []) s"
by (simp add: flow_def)

lemma small_stepsl_run_flow_2:
 "(c, s) \<rightarrow> (c', s') \<Longrightarrow> s' = run_flow (flow_aux [c]) s"
by (induction "[c]" arbitrary: c c' rule: flow_aux.induct, auto)

lemma small_stepsl_run_flow_3:
 "\<lbrakk>(c, s) \<rightarrow>*{cfs} (c', s') \<Longrightarrow> s' = run_flow (flow cfs) s;
    (c, s) \<rightarrow>*{cfs @ [(c', s')]} (c'', s'')\<rbrakk> \<Longrightarrow>
  s'' = run_flow (flow (cfs @ [(c', s')])) s"
by (simp add: flow_append run_flow_append,
 auto intro: small_stepsl_run_flow_2 simp: flow_def)

lemma small_stepsl_run_flow:
 "(c, s) \<rightarrow>*{cfs} (c', s') \<Longrightarrow> s' = run_flow (flow cfs) s"
by (induction c s cfs c' s' rule: small_stepsl_induct,
 erule small_stepsl_run_flow_1, rule small_stepsl_run_flow_3)


subsection "Local context proofs"

context noninterf
begin


lemma no_upd_sources:
 "no_upd cs x \<Longrightarrow> x \<in> sources cs s x"
by (induction cs rule: rev_induct, auto simp: no_upd_append
 split: com_flow.split)

lemma sources_aux_sources:
 "sources_aux cs s x \<subseteq> sources cs s x"
by (induction cs rule: rev_induct, auto split: com_flow.split)

lemma sources_aux_append:
 "sources_aux cs s x \<subseteq> sources_aux (cs @ cs') s x"
by (induction cs' rule: rev_induct, simp, subst append_assoc [symmetric],
 auto simp del: append_assoc split: com_flow.split)

lemma sources_aux_observe_hd_1:
 "\<forall>y \<in> X. s: dom y \<leadsto> dom x \<Longrightarrow> X \<subseteq> sources_aux [\<langle>X\<rangle>] s x"
by (subst append_Nil [symmetric], subst sources_aux.simps, auto)

lemma sources_aux_observe_hd_2:
 "(\<forall>y \<in> X. s: dom y \<leadsto> dom x \<Longrightarrow> X \<subseteq> sources_aux (\<langle>X\<rangle> # xs) s x) \<Longrightarrow>
    \<forall>y \<in> X. s: dom y \<leadsto> dom x \<Longrightarrow> X \<subseteq> sources_aux (\<langle>X\<rangle> # xs @ [x']) s x"
by (subst append_Cons [symmetric], subst sources_aux.simps,
 auto split: com_flow.split)

lemma sources_aux_observe_hd:
 "\<forall>y \<in> X. s: dom y \<leadsto> dom x \<Longrightarrow> X \<subseteq> sources_aux (\<langle>X\<rangle> # cs) s x"
by (induction cs rule: rev_induct,
 erule sources_aux_observe_hd_1, rule sources_aux_observe_hd_2)


lemma sources_observe_tl_1:
  assumes
    A: "\<And>z a. c = (x ::= a :: com_flow) \<Longrightarrow> z = x \<Longrightarrow>
      sources_aux cs s x \<subseteq> sources_aux (\<langle>X\<rangle> # cs) s x" and
    B: "\<And>z a y. c = (x ::= a :: com_flow) \<Longrightarrow> z = x \<Longrightarrow>
      sources cs s y \<subseteq> sources (\<langle>X\<rangle> # cs) s y" and
    C: "\<And>z a. c = (z ::= a :: com_flow) \<Longrightarrow> z \<noteq> x \<Longrightarrow>
      sources cs s x \<subseteq> sources (\<langle>X\<rangle> # cs) s x" and
    D: "\<And>Y y. c = \<langle>Y\<rangle> \<Longrightarrow>
      sources cs s y \<subseteq> sources (\<langle>X\<rangle> # cs) s y" and
    E: "z \<in> (case c of
      z ::= a \<Rightarrow> if z = x
        then sources_aux cs s x \<union> \<Union> {sources cs s y | y.
          run_flow cs s: dom y \<leadsto> dom x \<and> y \<in> avars a}
        else sources cs s x |
      \<langle>X\<rangle> \<Rightarrow>
        sources cs s x \<union> \<Union> {sources cs s y | y.
          run_flow cs s: dom y \<leadsto> dom x \<and> y \<in> X})"
  shows "z \<in> sources (\<langle>X\<rangle> # cs @ [c]) s x"
proof -
  {
    fix a
    assume
      F: "\<forall>A. (\<forall>y. run_flow cs s: dom y \<leadsto> dom x \<longrightarrow>
        A = sources (\<langle>X\<rangle> # cs) s y \<longrightarrow> y \<notin> avars a) \<or> z \<notin> A" and
      G: "c = x ::= a"
    have "z \<in> sources_aux cs s x \<union> \<Union> {sources cs s y | y.
      run_flow cs s: dom y \<leadsto> dom x \<and> y \<in> avars a}"
      using E and G by simp
    hence "z \<in> sources_aux (\<langle>X\<rangle> # cs) s x"
    using A and G proof (erule_tac UnE, blast)
      assume "z \<in> \<Union> {sources cs s y | y.
        run_flow cs s: dom y \<leadsto> dom x \<and> y \<in> avars a}"
      then obtain y where
        H: "z \<in> sources cs s y" and
        I: "run_flow cs s: dom y \<leadsto> dom x" and
        J: "y \<in> avars a"
        by blast
      have "z \<in> sources (\<langle>X\<rangle> # cs) s y"
        using B and G and H by blast
      hence "y \<notin> avars a"
        using F and I by blast
      thus ?thesis
        using J by contradiction
    qed
  }
  moreover {
    fix y a
    assume "c = y ::= a" and "y \<noteq> x"
    moreover from this have "z \<in> sources cs s x"
      using E by simp
    ultimately have "z \<in> sources (\<langle>X\<rangle> # cs) s x"
      using C by blast
  }
  moreover {
    fix Y
    assume
      F: "\<forall>A. (\<forall>y. run_flow cs s: dom y \<leadsto> dom x \<longrightarrow>
        A = sources (\<langle>X\<rangle> # cs) s y \<longrightarrow> y \<notin> Y) \<or> z \<notin> A" and
      G: "c = \<langle>Y\<rangle>"
    have "z \<in> sources cs s x \<union> \<Union> {sources cs s y | y.
      run_flow cs s: dom y \<leadsto> dom x \<and> y \<in> Y}"
      using E and G by simp
    hence "z \<in> sources (\<langle>X\<rangle> # cs) s x"
    using D and G proof (erule_tac UnE, blast)
      assume "z \<in> \<Union> {sources cs s y | y.
        run_flow cs s: dom y \<leadsto> dom x \<and> y \<in> Y}"
      then obtain y where
        H: "z \<in> sources cs s y" and
        I: "run_flow cs s: dom y \<leadsto> dom x" and
        J: "y \<in> Y"
        by blast
      have "z \<in> sources (\<langle>X\<rangle> # cs) s y"
        using D and G and H by blast
      hence "y \<notin> Y"
        using F and I by blast
      thus ?thesis
        using J by contradiction
    qed
  }
  ultimately show ?thesis
    by (simp only: append_Cons [symmetric] sources.simps,
     auto split: com_flow.split)
qed

lemma sources_observe_tl_2:
  assumes
    A: "\<And>z a. c = (z ::= a :: com_flow) \<Longrightarrow>
      sources_aux cs s x \<subseteq> sources_aux (\<langle>X\<rangle> # cs) s x" and
    B: "\<And>Y. c = \<langle>Y\<rangle> \<Longrightarrow>
      sources_aux cs s x \<subseteq> sources_aux (\<langle>X\<rangle> # cs) s x" and
    C: "\<And>Y y. c = \<langle>Y\<rangle> \<Longrightarrow>
      sources cs s y \<subseteq> sources (\<langle>X\<rangle> # cs) s y" and
    D: "z \<in> (case c of
      z ::= a \<Rightarrow>
        sources_aux cs s x |
      \<langle>X\<rangle> \<Rightarrow>
        sources_aux cs s x \<union> \<Union> {sources cs s y | y.
          run_flow cs s: dom y \<leadsto> dom x \<and> y \<in> X})"
  shows "z \<in> sources_aux (\<langle>X\<rangle> # cs @ [c]) s x"
proof -
  {
    fix y a
    assume "c = y ::= a"
    moreover from this have "z \<in> sources_aux cs s x"
      using D by simp
    ultimately have "z \<in> sources_aux (\<langle>X\<rangle> # cs) s x"
      using A by blast
  }
  moreover {
    fix Y
    assume
      E: "\<forall>A. (\<forall>y. run_flow cs s: dom y \<leadsto> dom x \<longrightarrow>
        A = sources (\<langle>X\<rangle> # cs) s y \<longrightarrow> y \<notin> Y) \<or> z \<notin> A" and
      F: "c = \<langle>Y\<rangle>"
    have "z \<in> sources_aux cs s x \<union> \<Union> {sources cs s y | y.
      run_flow cs s: dom y \<leadsto> dom x \<and> y \<in> Y}"
      using D and F by simp
    hence "z \<in> sources_aux (\<langle>X\<rangle> # cs) s x"
    using B and F proof (erule_tac UnE, blast)
      assume "z \<in> \<Union> {sources cs s y | y.
        run_flow cs s: dom y \<leadsto> dom x \<and> y \<in> Y}"
      then obtain y where
        H: "z \<in> sources cs s y" and
        I: "run_flow cs s: dom y \<leadsto> dom x" and
        J: "y \<in> Y"
        by blast
      have "z \<in> sources (\<langle>X\<rangle> # cs) s y"
        using C and F and H by blast
      hence "y \<notin> Y"
        using E and I by blast
      thus ?thesis
        using J by contradiction
    qed
  }
  ultimately show ?thesis
    by (simp only: append_Cons [symmetric] sources_aux.simps,
     auto split: com_flow.split)
qed

lemma sources_observe_tl:
 "sources cs s x \<subseteq> sources (\<langle>X\<rangle> # cs) s x"
and sources_aux_observe_tl:
 "sources_aux cs s x \<subseteq> sources_aux (\<langle>X\<rangle> # cs) s x"
proof (induction cs s x and cs s x rule: sources_induct)
  fix cs c s x
  show
   "\<lbrakk>\<And>z a. c = z ::= a \<Longrightarrow> z = x \<Longrightarrow>
      sources_aux cs s x \<subseteq> sources_aux (\<langle>X\<rangle> # cs) s x;
    \<And>z a b y. c = z ::= a \<Longrightarrow> z = x \<Longrightarrow>
      sources cs s y \<subseteq> sources (\<langle>X\<rangle> # cs) s y;
    \<And>z a. c = z ::= a \<Longrightarrow> z \<noteq> x \<Longrightarrow>
      sources cs s x \<subseteq> sources (\<langle>X\<rangle> # cs) s x;
    \<And>Y. c = \<langle>Y\<rangle> \<Longrightarrow>
      sources cs s x \<subseteq> sources (\<langle>X\<rangle> # cs) s x;
    \<And>Y a y. c = \<langle>Y\<rangle> \<Longrightarrow>
      sources cs s y \<subseteq> sources (\<langle>X\<rangle> # cs) s y\<rbrakk> \<Longrightarrow>
      sources (cs @ [c]) s x \<subseteq> sources (\<langle>X\<rangle> # cs @ [c]) s x"
    by (auto, rule sources_observe_tl_1)
next
  fix s x
  show "sources [] s x \<subseteq> sources [\<langle>X\<rangle>] s x"
    by (subst (3) append_Nil [symmetric],
     simp only: sources.simps, simp)
next
  fix cs c s x
  show
   "\<lbrakk>\<And>z a. c = z ::= a \<Longrightarrow>
      sources_aux cs s x \<subseteq> sources_aux (\<langle>X\<rangle> # cs) s x;
    \<And>Y. c = \<langle>Y\<rangle> \<Longrightarrow>
      sources_aux cs s x \<subseteq> sources_aux (\<langle>X\<rangle> # cs) s x;
    \<And>Y a y. c = \<langle>Y\<rangle> \<Longrightarrow>
      sources cs s y \<subseteq> sources (\<langle>X\<rangle> # cs) s y\<rbrakk> \<Longrightarrow>
      sources_aux (cs @ [c]) s x \<subseteq> sources_aux (\<langle>X\<rangle> # cs @ [c]) s x"
    by (auto, rule sources_observe_tl_2)
qed simp


lemma sources_member_1:
  assumes
    A: "\<And>z a. c = (x ::= a :: com_flow) \<Longrightarrow> z = x \<Longrightarrow>
      y \<in> sources_aux cs' (run_flow cs s) x \<Longrightarrow>
        sources cs s y \<subseteq> sources_aux (cs @ cs') s x" and
    B: "\<And>z a w. c = (x ::= a :: com_flow) \<Longrightarrow> z = x \<Longrightarrow>
      y \<in> sources cs' (run_flow cs s) w \<Longrightarrow>
        sources cs s y \<subseteq> sources (cs @ cs') s w" and
    C: "\<And>z a. c = (z ::= a :: com_flow) \<Longrightarrow> z \<noteq> x \<Longrightarrow>
      y \<in> sources cs' (run_flow cs s) x \<Longrightarrow>
        sources cs s y \<subseteq> sources (cs @ cs') s x" and
    D: "\<And>Y w. c = \<langle>Y\<rangle> \<Longrightarrow>
      y \<in> sources cs' (run_flow cs s) w \<Longrightarrow>
        sources cs s y \<subseteq> sources (cs @ cs') s w" and
    E: "y \<in> (case c of
      z ::= a \<Rightarrow> if z = x
        then sources_aux cs' (run_flow cs s) x \<union>
          \<Union> {sources cs' (run_flow cs s) y | y.
            run_flow cs' (run_flow cs s): dom y \<leadsto> dom x \<and> y \<in> avars a}
        else sources cs' (run_flow cs s) x |
      \<langle>X\<rangle> \<Rightarrow>
        sources cs' (run_flow cs s) x \<union>
          \<Union> {sources cs' (run_flow cs s) y | y.
            run_flow cs' (run_flow cs s): dom y \<leadsto> dom x \<and> y \<in> X})" and
    F: "z \<in> sources cs s y"
  shows "z \<in> sources (cs @ cs' @ [c]) s x"
proof -
  {
    fix a
    assume
      G: "\<forall>A. (\<forall>y. run_flow cs' (run_flow cs s): dom y \<leadsto> dom x \<longrightarrow>
        A = sources (cs @ cs') s y \<longrightarrow> y \<notin> avars a) \<or> z \<notin> A" and
      H: "c = x ::= a"
    have "y \<in> sources_aux cs' (run_flow cs s) x \<union>
      \<Union> {sources cs' (run_flow cs s) y | y.
        run_flow cs' (run_flow cs s): dom y \<leadsto> dom x \<and> y \<in> avars a}"
      using E and H by simp
    hence "z \<in> sources_aux (cs @ cs') s x"
    using A and F and H proof (erule_tac UnE, blast)
      assume "y \<in> \<Union> {sources cs' (run_flow cs s) y | y.
        run_flow cs' (run_flow cs s): dom y \<leadsto> dom x \<and> y \<in> avars a}"
      then obtain w where
        I: "y \<in> sources cs' (run_flow cs s) w" and
        J: "run_flow cs' (run_flow cs s): dom w \<leadsto> dom x" and
        K: "w \<in> avars a"
        by blast
      have "z \<in> sources (cs @ cs') s w"
        using B and F and H and I by blast
      hence "w \<notin> avars a"
        using G and J by blast
      thus ?thesis
        using K by contradiction
    qed
  }
  moreover {
    fix w a
    assume "c = w ::= a" and "w \<noteq> x"
    moreover from this have "y \<in> sources cs' (run_flow cs s) x"
      using E by simp
    ultimately have "z \<in> sources (cs @ cs') s x"
      using C and F by blast
  }
  moreover {
    fix Y
    assume
      G: "\<forall>A. (\<forall>y. run_flow cs' (run_flow cs s): dom y \<leadsto> dom x \<longrightarrow>
        A = sources (cs @ cs') s y \<longrightarrow> y \<notin> Y) \<or> z \<notin> A" and
      H: "c = \<langle>Y\<rangle>"
    have "y \<in> sources cs' (run_flow cs s) x \<union>
      \<Union> {sources cs' (run_flow cs s) y | y.
        run_flow cs' (run_flow cs s): dom y \<leadsto> dom x \<and> y \<in> Y}"
      using E and H by simp
    hence "z \<in> sources (cs @ cs') s x"
    using D and F and H proof (erule_tac UnE, blast)
      assume "y \<in> \<Union> {sources cs' (run_flow cs s) y | y.
        run_flow cs' (run_flow cs s): dom y \<leadsto> dom x \<and> y \<in> Y}"
      then obtain w where
        I: "y \<in> sources cs' (run_flow cs s) w" and
        J: "run_flow cs' (run_flow cs s): dom w \<leadsto> dom x" and
        K: "w \<in> Y"
        by blast
      have "z \<in> sources (cs @ cs') s w"
        using D and F and H and I by blast
      hence "w \<notin> Y"
        using G and J by blast
      thus ?thesis
        using K by contradiction
    qed
  }
  ultimately show ?thesis
    by (simp only: append_assoc [symmetric] sources.simps,
     auto simp: run_flow_append split: com_flow.split)
qed

lemma sources_member_2:
  assumes
    A: "\<And>z a. c = (z ::= a :: com_flow) \<Longrightarrow>
      y \<in> sources_aux cs' (run_flow cs s) x \<Longrightarrow>
        sources cs s y \<subseteq> sources_aux (cs @ cs') s x" and
    B: "\<And>Y. c = \<langle>Y\<rangle> \<Longrightarrow>
      y \<in> sources_aux cs' (run_flow cs s) x \<Longrightarrow>
        sources cs s y \<subseteq> sources_aux (cs @ cs') s x" and
    C: "\<And>Y w. c = \<langle>Y\<rangle> \<Longrightarrow>
      y \<in> sources cs' (run_flow cs s) w \<Longrightarrow>
        sources cs s y \<subseteq> sources (cs @ cs') s w" and
    D: "y \<in> (case c of
      z ::= a \<Rightarrow>
        sources_aux cs' (run_flow cs s) x |
      \<langle>X\<rangle> \<Rightarrow>
        sources_aux cs' (run_flow cs s) x \<union>
          \<Union> {sources cs' (run_flow cs s) y | y.
            run_flow cs' (run_flow cs s): dom y \<leadsto> dom x \<and> y \<in> X})" and
    E: "z \<in> sources cs s y"
  shows "z \<in> sources_aux (cs @ cs' @ [c]) s x"
proof -
  {
    fix w a
    assume "c = w ::= a"
    moreover from this have "y \<in> sources_aux cs' (run_flow cs s) x"
      using D by simp
    ultimately have "z \<in> sources_aux (cs @ cs') s x"
      using A and E by blast
  }
  moreover {
    fix Y
    assume
      G: "\<forall>A. (\<forall>y. run_flow cs' (run_flow cs s): dom y \<leadsto> dom x \<longrightarrow>
        A = sources (cs @ cs') s y \<longrightarrow> y \<notin> Y) \<or> z \<notin> A" and
      H: "c = \<langle>Y\<rangle>"
    have "y \<in> sources_aux cs' (run_flow cs s) x \<union>
      \<Union> {sources cs' (run_flow cs s) y | y.
        run_flow cs' (run_flow cs s): dom y \<leadsto> dom x \<and> y \<in> Y}"
      using D and H by simp
    hence "z \<in> sources_aux (cs @ cs') s x"
    using B and E and H proof (erule_tac UnE, blast)
      assume "y \<in> \<Union> {sources cs' (run_flow cs s) y | y.
        run_flow cs' (run_flow cs s): dom y \<leadsto> dom x \<and> y \<in> Y}"
      then obtain w where
        I: "y \<in> sources cs' (run_flow cs s) w" and
        J: "run_flow cs' (run_flow cs s): dom w \<leadsto> dom x" and
        K: "w \<in> Y"
        by blast
      have "z \<in> sources (cs @ cs') s w"
        using C and E and H and I by blast
      hence "w \<notin> Y"
        using G and J by blast
      thus ?thesis
        using K by contradiction
    qed
  }
  ultimately show ?thesis
    by (simp only: append_assoc [symmetric] sources_aux.simps,
     auto simp: run_flow_append split: com_flow.split)
qed

lemma sources_member:
 "y \<in> sources cs' (run_flow cs s) x \<Longrightarrow>
    sources cs s y \<subseteq> sources (cs @ cs') s x"
and sources_aux_member:
 "y \<in> sources_aux cs' (run_flow cs s) x \<Longrightarrow>
    sources cs s y \<subseteq> sources_aux (cs @ cs') s x"
proof (induction cs' s x and cs' s x rule: sources_induct)
  fix cs' c s x
  show
   "\<lbrakk>\<And>z a. c = z ::= a \<Longrightarrow> z = x \<Longrightarrow>
      y \<in> sources_aux cs' (run_flow cs s) x \<Longrightarrow>
        sources cs s y \<subseteq> sources_aux (cs @ cs') s x;
    \<And>z a b w. c = z ::= a \<Longrightarrow> z = x \<Longrightarrow>
      y \<in> sources cs' (run_flow cs s) w \<Longrightarrow>
        sources cs s y \<subseteq> sources (cs @ cs') s w;
    \<And>z a. c = z ::= a \<Longrightarrow> z \<noteq> x \<Longrightarrow>
      y \<in> sources cs' (run_flow cs s) x \<Longrightarrow>
        sources cs s y \<subseteq> sources (cs @ cs') s x;
    \<And>Y. c = \<langle>Y\<rangle> \<Longrightarrow>
      y \<in> sources cs' (run_flow cs s) x \<Longrightarrow>
        sources cs s y \<subseteq> sources (cs @ cs') s x;
    \<And>Y a w. c = \<langle>Y\<rangle> \<Longrightarrow>
      y \<in> sources cs' (run_flow cs s) w \<Longrightarrow>
        sources cs s y \<subseteq> sources (cs @ cs') s w;
    y \<in> sources (cs' @ [c]) (run_flow cs s) x\<rbrakk> \<Longrightarrow>
      sources cs s y \<subseteq> sources (cs @ cs' @ [c]) s x"
    by (auto, rule sources_member_1)
next
  fix cs' c s x
  show
   "\<lbrakk>\<And>z a. c = z ::= a \<Longrightarrow>
      y \<in> sources_aux cs' (run_flow cs s) x \<Longrightarrow>
        sources cs s y \<subseteq> sources_aux (cs @ cs') s x;
    \<And>Y. c = \<langle>Y\<rangle> \<Longrightarrow>
      y \<in> sources_aux cs' (run_flow cs s) x \<Longrightarrow>
        sources cs s y \<subseteq> sources_aux (cs @ cs') s x;
    \<And>Y a w. c = \<langle>Y\<rangle> \<Longrightarrow>
      y \<in> sources cs' (run_flow cs s) w \<Longrightarrow>
        sources cs s y \<subseteq> sources (cs @ cs') s w;
    y \<in> sources_aux (cs' @ [c]) (run_flow cs s) x\<rbrakk> \<Longrightarrow>
      sources cs s y \<subseteq> sources_aux (cs @ cs' @ [c]) s x"
    by (auto, rule sources_member_2)
qed simp_all


lemma ctyping2_confine:
 "\<lbrakk>(c, s) \<Rightarrow> s'; (U, v) \<Turnstile> c (\<subseteq> A, X) = Some (B, Y);
    \<exists>(C, Z) \<in> U. \<not> C: dom ` Z \<leadsto> {dom x}\<rbrakk> \<Longrightarrow> s' x = s x"
by (induction arbitrary: A B X Y U v rule: big_step_induct,
 auto split: if_split_asm option.split_asm prod.split_asm, fastforce+)

lemma ctyping2_term_if:
 "\<lbrakk>\<And>x' y' z'' s. x' = x \<Longrightarrow> y' = y \<Longrightarrow> z = z'' \<Longrightarrow> \<exists>s'. (c\<^sub>1, s) \<Rightarrow> s';
    \<And>x' y' z'' s. x' = x \<Longrightarrow> y' = y \<Longrightarrow> z' = z'' \<Longrightarrow> \<exists>s'. (c\<^sub>2, s) \<Rightarrow> s'\<rbrakk> \<Longrightarrow>
  \<exists>s'. (IF b THEN c\<^sub>1 ELSE c\<^sub>2, s) \<Rightarrow> s'"
by (cases "bval b s", fastforce+)

lemma ctyping2_term:
 "\<lbrakk>(U, v) \<Turnstile> c (\<subseteq> A, X) = Some (B, Y);
    \<exists>(C, Z) \<in> U. \<not> C: dom ` Z \<leadsto> UNIV\<rbrakk> \<Longrightarrow> \<exists>s'. (c, s) \<Rightarrow> s'"
by (induction "(U, v)" c A X arbitrary: B Y U v s rule: ctyping2.induct,
 auto split: if_split_asm option.split_asm prod.split_asm, fastforce,
 erule ctyping2_term_if)


lemma ctyping2_correct_aux_skip [elim]:
 "\<lbrakk>(SKIP, s) \<rightarrow>*{cfs\<^sub>1} (c\<^sub>1, s\<^sub>1); (c\<^sub>1, s\<^sub>1) \<rightarrow>*{cfs\<^sub>2} (c\<^sub>2, s\<^sub>2)\<rbrakk> \<Longrightarrow>
    (\<forall>t\<^sub>1. \<exists>c\<^sub>2' t\<^sub>2. \<forall>x.
      (s\<^sub>1 = t\<^sub>1 (\<subseteq> sources_aux (flow cfs\<^sub>2) s\<^sub>1 x) \<longrightarrow>
        (c\<^sub>1, t\<^sub>1) \<rightarrow>* (c\<^sub>2', t\<^sub>2) \<and> (c\<^sub>2 = SKIP) = (c\<^sub>2' = SKIP)) \<and>
      (s\<^sub>1 = t\<^sub>1 (\<subseteq> sources (flow cfs\<^sub>2) s\<^sub>1 x) \<longrightarrow> s\<^sub>2 x = t\<^sub>2 x)) \<and>
    (\<forall>x. (\<exists>p \<in> U. case p of (B, W) \<Rightarrow>
      \<exists>s \<in> B. \<exists>y \<in> W. \<not> s: dom y \<leadsto> dom x) \<longrightarrow> no_upd (flow cfs\<^sub>2) x)"
by (fastforce dest: small_stepsl_skip)

lemma ctyping2_correct_aux_assign [elim]:
  assumes
    A: "(if (\<forall>s \<in> Univ? A X. \<forall>y \<in> avars a. s: dom y \<leadsto> dom x) \<and>
          (\<forall>p \<in> U. \<forall>B Y. p = (B, Y) \<longrightarrow>
            (\<forall>s \<in> B. \<forall>y \<in> Y. s: dom y \<leadsto> dom x))
        then Some (if x \<in> state \<and> A \<noteq> {}
          then if v \<Turnstile> a (\<subseteq> X)
            then ({s(x := aval a s) |s. s \<in> A}, insert x X)
            else (A, X - {x})
          else (A, Univ?? A X))
        else None) = Some (B, Y)"
      (is "(if ?P then _ else _) = _") and
    B: "(x ::= a, s) \<rightarrow>*{cfs\<^sub>1} (c\<^sub>1, s\<^sub>1)" and
    C: "(c\<^sub>1, s\<^sub>1) \<rightarrow>*{cfs\<^sub>2} (c\<^sub>2, s\<^sub>2)" and
    D: "r \<in> A" and
    E: "s = r (\<subseteq> state \<inter> X)"
  shows
   "(\<forall>t\<^sub>1. \<exists>c\<^sub>2' t\<^sub>2. \<forall>x.
      (s\<^sub>1 = t\<^sub>1 (\<subseteq> sources_aux (flow cfs\<^sub>2) s\<^sub>1 x) \<longrightarrow>
        (c\<^sub>1, t\<^sub>1) \<rightarrow>* (c\<^sub>2', t\<^sub>2) \<and> (c\<^sub>2 = SKIP) = (c\<^sub>2' = SKIP)) \<and>
      (s\<^sub>1 = t\<^sub>1 (\<subseteq> sources (flow cfs\<^sub>2) s\<^sub>1 x) \<longrightarrow> s\<^sub>2 x = t\<^sub>2 x)) \<and>
    (\<forall>x. (\<exists>p \<in> U. case p of (B, Y) \<Rightarrow>
      \<exists>s \<in> B. \<exists>y \<in> Y. \<not> s: dom y \<leadsto> dom x) \<longrightarrow> no_upd (flow cfs\<^sub>2) x)"
proof -
  have ?P
    using A by (simp split: if_split_asm)
  have F: "avars a \<subseteq> {y. s: dom y \<leadsto> dom x}"
  proof (cases "state \<subseteq> X")
    case True
    with E have "interf s = interf r"
      by (blast intro: interf_state)
    with D and `?P` show ?thesis
      by (erule_tac conjE, drule_tac bspec, auto simp: univ_states_if_def)
  next
    case False
    with D and `?P` show ?thesis
      by (erule_tac conjE, drule_tac bspec, auto simp: univ_states_if_def)
  qed
  have "(c\<^sub>1, s\<^sub>1) = (x ::= a, s) \<or> (c\<^sub>1, s\<^sub>1) = (SKIP, s(x := aval a s))"
    using B by (blast dest: small_stepsl_assign)
  thus ?thesis
  proof
    assume "(c\<^sub>1, s\<^sub>1) = (x ::= a, s)"
    moreover from this have "(x ::= a, s) \<rightarrow>*{cfs\<^sub>2} (c\<^sub>2, s\<^sub>2)"
      using C by simp
    hence "(c\<^sub>2, s\<^sub>2) = (x ::= a, s) \<and> flow cfs\<^sub>2 = [] \<or>
      (c\<^sub>2, s\<^sub>2) = (SKIP, s(x := aval a s)) \<and> flow cfs\<^sub>2 = [x ::= a]"
      by (rule small_stepsl_assign)
    moreover {
      fix t
      have "\<exists>c' t'. \<forall>y.
        (y = x \<longrightarrow>
          (s = t (\<subseteq> sources_aux [x ::= a] s x) \<longrightarrow>
            (x ::= a, t) \<rightarrow>* (c', t') \<and> c' = SKIP) \<and>
          (s = t (\<subseteq> sources [x ::= a] s x) \<longrightarrow> aval a s = t' x)) \<and>
        (y \<noteq> x \<longrightarrow>
          (s = t (\<subseteq> sources_aux [x ::= a] s y) \<longrightarrow>
            (x ::= a, t) \<rightarrow>* (c', t') \<and> c' = SKIP) \<and>
          (s = t (\<subseteq> sources [x ::= a] s y) \<longrightarrow> s y = t' y))"
      proof (rule exI [of _ SKIP], rule exI [of _ "t(x := aval a t)"])
        {
          assume "s = t (\<subseteq> sources [x ::= a] s x)"
          hence "s = t (\<subseteq> {y. s: dom y \<leadsto> dom x \<and> y \<in> avars a})"
            by (subst (asm) append_Nil [symmetric],
             simp only: sources.simps, auto)
          hence "aval a s = aval a t"
            using F by (blast intro: avars_aval)
        }
        moreover {
          fix y
          assume "s = t (\<subseteq> sources [x ::= a] s y)" and "y \<noteq> x"
          hence "s y = t y"
            by (subst (asm) append_Nil [symmetric],
             simp only: sources.simps, auto)
        }
        ultimately show "\<forall>y.
          (y = x \<longrightarrow>
            (s = t (\<subseteq> sources_aux [x ::= a] s x) \<longrightarrow>
              (x ::= a, t) \<rightarrow>* (SKIP, t(x := aval a t)) \<and> SKIP = SKIP) \<and>
            (s = t (\<subseteq> sources [x ::= a] s x) \<longrightarrow>
              aval a s = (t(x := aval a t)) x)) \<and>
          (y \<noteq> x \<longrightarrow>
            (s = t (\<subseteq> sources_aux [x ::= a] s y) \<longrightarrow>
              (x ::= a, t) \<rightarrow>* (SKIP, t(x := aval a t)) \<and> SKIP = SKIP) \<and>
            (s = t (\<subseteq> sources [x ::= a] s y) \<longrightarrow>
              s y = (t(x := aval a t)) y))"
          by simp
      qed
    }
    ultimately show ?thesis
      using `?P` by fastforce
  next
    assume "(c\<^sub>1, s\<^sub>1) = (SKIP, s(x := aval a s))"
    moreover from this have "(SKIP, s(x := aval a s)) \<rightarrow>*{cfs\<^sub>2} (c\<^sub>2, s\<^sub>2)"
      using C by simp
    hence "(c\<^sub>2, s\<^sub>2) = (SKIP, s(x := aval a s)) \<and> flow cfs\<^sub>2 = []"
      by (rule small_stepsl_skip)
    ultimately show ?thesis
      by auto
  qed
qed

lemma ctyping2_correct_aux_seq:
  assumes
    A: "\<And>B' s c' c'' s\<^sub>1 s\<^sub>2 cfs\<^sub>1 cfs\<^sub>2. B = B' \<Longrightarrow>
      \<exists>r \<in> A. s = r (\<subseteq> state \<inter> X) \<Longrightarrow>
        (c\<^sub>1, s) \<rightarrow>*{cfs\<^sub>1} (c', s\<^sub>1) \<Longrightarrow> (c', s\<^sub>1) \<rightarrow>*{cfs\<^sub>2} (c'', s\<^sub>2) \<Longrightarrow>
          (\<forall>t\<^sub>1. \<exists>c\<^sub>2' t\<^sub>2. \<forall>x.
            (s\<^sub>1 = t\<^sub>1 (\<subseteq> sources_aux (flow cfs\<^sub>2) s\<^sub>1 x) \<longrightarrow>
              (c', t\<^sub>1) \<rightarrow>* (c\<^sub>2', t\<^sub>2) \<and> (c'' = SKIP) = (c\<^sub>2' = SKIP)) \<and>
            (s\<^sub>1 = t\<^sub>1 (\<subseteq> sources (flow cfs\<^sub>2) s\<^sub>1 x) \<longrightarrow> s\<^sub>2 x = t\<^sub>2 x)) \<and>
          (\<forall>x. (\<exists>p \<in> U. case p of (B, W) \<Rightarrow>
            \<exists>s \<in> B. \<exists>y \<in> W. \<not> s: dom y \<leadsto> dom x) \<longrightarrow>
              no_upd (flow cfs\<^sub>2) x)" and
    B: "\<And>B' B'' C Z s c' c'' s\<^sub>1 s\<^sub>2 cfs\<^sub>1 cfs\<^sub>2. B = B' \<Longrightarrow> B'' = B' \<Longrightarrow>
      (U, v) \<Turnstile> c\<^sub>2 (\<subseteq> B', Y) = Some (C, Z) \<Longrightarrow>
        \<exists>r \<in> B'. s = r (\<subseteq> state \<inter> Y) \<Longrightarrow>
          (c\<^sub>2, s) \<rightarrow>*{cfs\<^sub>1} (c', s\<^sub>1) \<Longrightarrow> (c', s\<^sub>1) \<rightarrow>*{cfs\<^sub>2} (c'', s\<^sub>2) \<Longrightarrow>
            (\<forall>t\<^sub>1. \<exists>c\<^sub>2' t\<^sub>2. \<forall>x.
              (s\<^sub>1 = t\<^sub>1 (\<subseteq> sources_aux (flow cfs\<^sub>2) s\<^sub>1 x) \<longrightarrow>
                (c', t\<^sub>1) \<rightarrow>* (c\<^sub>2', t\<^sub>2) \<and> (c'' = SKIP) = (c\<^sub>2' = SKIP)) \<and>
              (s\<^sub>1 = t\<^sub>1 (\<subseteq> sources (flow cfs\<^sub>2) s\<^sub>1 x) \<longrightarrow> s\<^sub>2 x = t\<^sub>2 x)) \<and>
            (\<forall>x. (\<exists>p \<in> U. case p of (B, W) \<Rightarrow>
              \<exists>s \<in> B. \<exists>y \<in> W. \<not> s: dom y \<leadsto> dom x) \<longrightarrow>
                no_upd (flow cfs\<^sub>2) x)" and
    C: "(U, v) \<Turnstile> c\<^sub>1 (\<subseteq> A, X) = Some (B, Y)" and
    D: "(U, v) \<Turnstile> c\<^sub>2 (\<subseteq> B, Y) = Some (C, Z)" and
    E: "(c\<^sub>1;; c\<^sub>2, s) \<rightarrow>*{cfs\<^sub>1} (c', s\<^sub>1)" and
    F: "(c', s\<^sub>1) \<rightarrow>*{cfs\<^sub>2} (c'', s\<^sub>2)" and
    G: "r \<in> A" and
    H: "s = r (\<subseteq> state \<inter> X)"
  shows
   "(\<forall>t\<^sub>1. \<exists>c\<^sub>2' t\<^sub>2. \<forall>x.
      (s\<^sub>1 = t\<^sub>1 (\<subseteq> sources_aux (flow cfs\<^sub>2) s\<^sub>1 x) \<longrightarrow>
        (c', t\<^sub>1) \<rightarrow>* (c\<^sub>2', t\<^sub>2) \<and> (c'' = SKIP) = (c\<^sub>2' = SKIP)) \<and>
      (s\<^sub>1 = t\<^sub>1 (\<subseteq> sources (flow cfs\<^sub>2) s\<^sub>1 x) \<longrightarrow> s\<^sub>2 x = t\<^sub>2 x)) \<and>
    (\<forall>x. (\<exists>p \<in> U. case p of (B, W) \<Rightarrow>
      \<exists>s \<in> B. \<exists>y \<in> W. \<not> s: dom y \<leadsto> dom x) \<longrightarrow> no_upd (flow cfs\<^sub>2) x)"
proof -
  have
   "(\<exists>d' cfs. c' = d';; c\<^sub>2 \<and>
      (c\<^sub>1, s) \<rightarrow>*{cfs} (d', s\<^sub>1)) \<or>
    (\<exists>s' cfs cfs'.
      (c\<^sub>1, s) \<rightarrow>*{cfs} (SKIP, s') \<and>
      (c\<^sub>2, s') \<rightarrow>*{cfs'} (c', s\<^sub>1))"
    using E by (blast dest: small_stepsl_seq)
  thus ?thesis
  proof (rule disjE, (erule_tac exE)+, (erule_tac [2] exE)+,
   erule_tac [!] conjE)
    fix d' cfs
    assume
      I: "c' = d';; c\<^sub>2" and
      J: "(c\<^sub>1, s) \<rightarrow>*{cfs} (d', s\<^sub>1)"
    hence "(d';; c\<^sub>2, s\<^sub>1) \<rightarrow>*{cfs\<^sub>2} (c'', s\<^sub>2)"
      using F by simp
    hence
     "(\<exists>d'' cfs'. c'' = d'';; c\<^sub>2 \<and>
        (d', s\<^sub>1) \<rightarrow>*{cfs'} (d'', s\<^sub>2) \<and>
        flow cfs\<^sub>2 = flow cfs') \<or>
      (\<exists>s' cfs' cfs''.
        (d', s\<^sub>1) \<rightarrow>*{cfs'} (SKIP, s') \<and>
        (c\<^sub>2, s') \<rightarrow>*{cfs''} (c'', s\<^sub>2) \<and>
        flow cfs\<^sub>2 = flow cfs' @ flow cfs'')"
      by (blast dest: small_stepsl_seq)
    thus ?thesis
    proof (rule disjE, (erule_tac exE)+, (erule_tac [2] exE)+,
     (erule_tac [!] conjE)+)
      fix d'' cfs'
      assume "(d', s\<^sub>1) \<rightarrow>*{cfs'} (d'', s\<^sub>2)"
      hence K:
       "(\<forall>t\<^sub>1. \<exists>c\<^sub>2' t\<^sub>2. \<forall>x.
          (s\<^sub>1 = t\<^sub>1 (\<subseteq> sources_aux (flow cfs') s\<^sub>1 x) \<longrightarrow>
            (d', t\<^sub>1) \<rightarrow>* (c\<^sub>2', t\<^sub>2) \<and> (d'' = SKIP) = (c\<^sub>2' = SKIP)) \<and>
          (s\<^sub>1 = t\<^sub>1 (\<subseteq> sources (flow cfs') s\<^sub>1 x) \<longrightarrow> s\<^sub>2 x = t\<^sub>2 x)) \<and>
        (\<forall>x. (\<exists>p \<in> U. case p of (B, W) \<Rightarrow>
          \<exists>s \<in> B. \<exists>y \<in> W. \<not> s: dom y \<leadsto> dom x) \<longrightarrow> no_upd (flow cfs') x)"
        using A [of B s cfs d' s\<^sub>1 cfs' d'' s\<^sub>2] and J and G and H by blast
      moreover assume "c'' = d'';; c\<^sub>2" and "flow cfs\<^sub>2 = flow cfs'"
      moreover {
        fix t\<^sub>1
        obtain c\<^sub>2' and t\<^sub>2 where L: "\<forall>x.
          (s\<^sub>1 = t\<^sub>1 (\<subseteq> sources_aux (flow cfs') s\<^sub>1 x) \<longrightarrow>
            (d', t\<^sub>1) \<rightarrow>* (c\<^sub>2', t\<^sub>2) \<and> (d'' = SKIP) = (c\<^sub>2' = SKIP)) \<and>
          (s\<^sub>1 = t\<^sub>1 (\<subseteq> sources (flow cfs') s\<^sub>1 x) \<longrightarrow> s\<^sub>2 x = t\<^sub>2 x)"
          using K by blast
        have "\<exists>c\<^sub>2' t\<^sub>2. \<forall>x.
          (s\<^sub>1 = t\<^sub>1 (\<subseteq> sources_aux (flow cfs') s\<^sub>1 x) \<longrightarrow>
            (d';; c\<^sub>2, t\<^sub>1) \<rightarrow>* (c\<^sub>2', t\<^sub>2) \<and> c\<^sub>2' \<noteq> SKIP) \<and>
          (s\<^sub>1 = t\<^sub>1 (\<subseteq> sources (flow cfs') s\<^sub>1 x) \<longrightarrow> s\<^sub>2 x = t\<^sub>2 x)"
        proof (rule exI [of _ "c\<^sub>2';; c\<^sub>2"], rule exI [of _ t\<^sub>2])
          show "\<forall>x.
            (s\<^sub>1 = t\<^sub>1 (\<subseteq> sources_aux (flow cfs') s\<^sub>1 x) \<longrightarrow>
              (d';; c\<^sub>2, t\<^sub>1) \<rightarrow>* (c\<^sub>2';; c\<^sub>2, t\<^sub>2) \<and> c\<^sub>2';; c\<^sub>2 \<noteq> SKIP) \<and>
            (s\<^sub>1 = t\<^sub>1 (\<subseteq> sources (flow cfs') s\<^sub>1 x) \<longrightarrow> s\<^sub>2 x = t\<^sub>2 x)"
            using L by (auto intro: star_seq2)
        qed
      }
      ultimately show ?thesis
        using I by auto
    next
      fix s' cfs' cfs''
      assume
        K: "(d', s\<^sub>1) \<rightarrow>*{cfs'} (SKIP, s')" and
        L: "(c\<^sub>2, s') \<rightarrow>*{cfs''} (c'', s\<^sub>2)"
      moreover have M: "s' = run_flow (flow cfs') s\<^sub>1"
        using K by (rule small_stepsl_run_flow)
      ultimately have N:
       "(\<forall>t\<^sub>1. \<exists>c\<^sub>2' t\<^sub>2. \<forall>x.
          (s\<^sub>1 = t\<^sub>1 (\<subseteq> sources_aux (flow cfs') s\<^sub>1 x) \<longrightarrow>
            (d', t\<^sub>1) \<rightarrow>* (c\<^sub>2', t\<^sub>2) \<and> (SKIP = SKIP) = (c\<^sub>2' = SKIP)) \<and>
          (s\<^sub>1 = t\<^sub>1 (\<subseteq> sources (flow cfs') s\<^sub>1 x) \<longrightarrow>
            run_flow (flow cfs') s\<^sub>1 x = t\<^sub>2 x)) \<and>
        (\<forall>x. (\<exists>p \<in> U. case p of (B, W) \<Rightarrow>
          \<exists>s \<in> B. \<exists>y \<in> W. \<not> s: dom y \<leadsto> dom x) \<longrightarrow> no_upd (flow cfs') x)"
        using A [of B s cfs d' s\<^sub>1 cfs' SKIP s'] and J and G and H by blast
      have O: "s\<^sub>2 = run_flow (flow cfs'') s'"
        using L by (rule small_stepsl_run_flow)
      moreover have "(c\<^sub>1, s) \<rightarrow>*{cfs @ cfs'} (SKIP, s')"
        using J and K by (simp add: small_stepsl_append)
      hence "(c\<^sub>1, s) \<Rightarrow> s'"
        by (auto dest: small_stepsl_steps simp: big_iff_small)
      hence "s' \<in> Univ B (\<subseteq> state \<inter> Y)"
        using C and G and H by (erule_tac ctyping2_approx, auto)
      ultimately have P:
       "(\<forall>t\<^sub>1. \<exists>c\<^sub>2' t\<^sub>2. \<forall>x.
          (run_flow (flow cfs') s\<^sub>1 = t\<^sub>1
            (\<subseteq> sources_aux (flow cfs'') (run_flow (flow cfs') s\<^sub>1) x) \<longrightarrow>
              (c\<^sub>2, t\<^sub>1) \<rightarrow>* (c\<^sub>2', t\<^sub>2) \<and> (c'' = SKIP) = (c\<^sub>2' = SKIP)) \<and>
          (run_flow (flow cfs') s\<^sub>1 = t\<^sub>1
            (\<subseteq> sources (flow cfs'') (run_flow (flow cfs') s\<^sub>1) x) \<longrightarrow>
              run_flow (flow cfs'') (run_flow (flow cfs') s\<^sub>1) x = t\<^sub>2 x)) \<and>
        (\<forall>x. (\<exists>p \<in> U. case p of (B, W) \<Rightarrow>
          \<exists>s \<in> B. \<exists>y \<in> W. \<not> s: dom y \<leadsto> dom x) \<longrightarrow> no_upd (flow cfs'') x)"
        using B [of B B C Z s' "[]" c\<^sub>2 s' cfs'' c'' s\<^sub>2]
         and D and L and M by simp
      moreover assume "flow cfs\<^sub>2 = flow cfs' @ flow cfs''"
      moreover {
        fix t\<^sub>1
        obtain c\<^sub>2' and t\<^sub>2 where Q: "\<forall>x.
          (s\<^sub>1 = t\<^sub>1 (\<subseteq> sources_aux (flow cfs') s\<^sub>1 x) \<longrightarrow>
            (d', t\<^sub>1) \<rightarrow>* (SKIP, t\<^sub>2) \<and> (SKIP = SKIP) = (c\<^sub>2' = SKIP)) \<and>
          (s\<^sub>1 = t\<^sub>1 (\<subseteq> sources (flow cfs') s\<^sub>1 x) \<longrightarrow>
            run_flow (flow cfs') s\<^sub>1 x = t\<^sub>2 x)"
          using N by blast
        obtain c\<^sub>3' and t\<^sub>3 where R: "\<forall>x.
          (run_flow (flow cfs') s\<^sub>1 = t\<^sub>2
            (\<subseteq> sources_aux (flow cfs'') (run_flow (flow cfs') s\<^sub>1) x) \<longrightarrow>
              (c\<^sub>2, t\<^sub>2) \<rightarrow>* (c\<^sub>3', t\<^sub>3) \<and> (c'' = SKIP) = (c\<^sub>3' = SKIP)) \<and>
          (run_flow (flow cfs') s\<^sub>1 = t\<^sub>2
            (\<subseteq> sources (flow cfs'') (run_flow (flow cfs') s\<^sub>1) x) \<longrightarrow>
              run_flow (flow cfs'') (run_flow (flow cfs') s\<^sub>1) x = t\<^sub>3 x)"
          using P by blast
        {
          fix x
          assume S: "s\<^sub>1 = t\<^sub>1
            (\<subseteq> sources_aux (flow cfs' @ flow cfs'') s\<^sub>1 x)"
          moreover have "sources_aux (flow cfs') s\<^sub>1 x \<subseteq>
            sources_aux (flow cfs' @ flow cfs'') s\<^sub>1 x"
            by (rule sources_aux_append)
          ultimately have "(d', t\<^sub>1) \<rightarrow>* (SKIP, t\<^sub>2)"
            using Q by blast
          hence "(d';; c\<^sub>2, t\<^sub>1) \<rightarrow>* (SKIP;; c\<^sub>2, t\<^sub>2)"
            by (rule star_seq2)
          hence "(d';; c\<^sub>2, t\<^sub>1) \<rightarrow>* (c\<^sub>2, t\<^sub>2)"
            by (blast intro: star_trans)
          moreover have "run_flow (flow cfs') s\<^sub>1 = t\<^sub>2
            (\<subseteq> sources_aux (flow cfs'') (run_flow (flow cfs') s\<^sub>1) x)"
          proof
            fix y
            assume "y \<in> sources_aux (flow cfs'')
              (run_flow (flow cfs') s\<^sub>1) x"
            hence "sources (flow cfs') s\<^sub>1 y \<subseteq>
              sources_aux (flow cfs' @ flow cfs'') s\<^sub>1 x"
              by (rule sources_aux_member)
            thus "run_flow (flow cfs') s\<^sub>1 y = t\<^sub>2 y"
              using Q and S by blast
          qed
          hence "(c\<^sub>2, t\<^sub>2) \<rightarrow>* (c\<^sub>3', t\<^sub>3) \<and> (c'' = SKIP) = (c\<^sub>3' = SKIP)"
            using R by simp
          ultimately have "(d';; c\<^sub>2, t\<^sub>1) \<rightarrow>* (c\<^sub>3', t\<^sub>3) \<and>
            (c'' = SKIP) = (c\<^sub>3' = SKIP)"
            by (blast intro: star_trans)
        }
        moreover {
          fix x
          assume S: "s\<^sub>1 = t\<^sub>1
            (\<subseteq> sources (flow cfs' @ flow cfs'') s\<^sub>1 x)"
          have "run_flow (flow cfs') s\<^sub>1 = t\<^sub>2
            (\<subseteq> sources (flow cfs'') (run_flow (flow cfs') s\<^sub>1) x)"
          proof
            fix y
            assume "y \<in> sources (flow cfs'')
              (run_flow (flow cfs') s\<^sub>1) x"
            hence "sources (flow cfs') s\<^sub>1 y \<subseteq>
              sources (flow cfs' @ flow cfs'') s\<^sub>1 x"
              by (rule sources_member)
            thus "run_flow (flow cfs') s\<^sub>1 y = t\<^sub>2 y"
              using Q and S by blast
          qed
          hence "run_flow (flow cfs'') (run_flow (flow cfs') s\<^sub>1) x = t\<^sub>3 x"
            using R by simp
        }
        ultimately have "\<exists>c\<^sub>2' t\<^sub>2. \<forall>x.
          (s\<^sub>1 = t\<^sub>1 (\<subseteq> sources_aux (flow cfs' @ flow cfs'') s\<^sub>1 x) \<longrightarrow>
            (d';; c\<^sub>2, t\<^sub>1) \<rightarrow>* (c\<^sub>2', t\<^sub>2) \<and> (c'' = SKIP) = (c\<^sub>2' = SKIP)) \<and>
          (s\<^sub>1 = t\<^sub>1 (\<subseteq> sources (flow cfs' @ flow cfs'') s\<^sub>1 x) \<longrightarrow>
            run_flow (flow cfs'') (run_flow (flow cfs') s\<^sub>1) x = t\<^sub>2 x)"
          by auto
      }
      ultimately show ?thesis
        using I and N and M and O by (auto simp: no_upd_append)
    qed
  next
    fix s' cfs cfs'
    assume "(c\<^sub>1, s) \<rightarrow>*{cfs} (SKIP, s')"
    hence "(c\<^sub>1, s) \<Rightarrow> s'"
      by (auto dest: small_stepsl_steps simp: big_iff_small)
    hence "s' \<in> Univ B (\<subseteq> state \<inter> Y)"
      using C and G and H by (erule_tac ctyping2_approx, auto)
    moreover assume "(c\<^sub>2, s') \<rightarrow>*{cfs'} (c', s\<^sub>1)"
    ultimately show ?thesis
      using B [of B B C Z s' cfs' c' s\<^sub>1 cfs\<^sub>2 c'' s\<^sub>2] and D and F by simp
  qed
qed

lemma ctyping2_correct_aux_if:
  assumes
    A: "\<And>U' B C s c' c'' s\<^sub>1 s\<^sub>2 cfs\<^sub>1 cfs\<^sub>2.
      U' = insert (Univ? A X, bvars b) U \<Longrightarrow> B = B\<^sub>1 \<Longrightarrow> C\<^sub>1 = C \<Longrightarrow>
        \<exists>r \<in> B\<^sub>1. s = r (\<subseteq> state \<inter> X) \<Longrightarrow>
          (c\<^sub>1, s) \<rightarrow>*{cfs\<^sub>1} (c', s\<^sub>1) \<Longrightarrow> (c', s\<^sub>1) \<rightarrow>*{cfs\<^sub>2} (c'', s\<^sub>2) \<Longrightarrow>
            (\<forall>t\<^sub>1. \<exists>c\<^sub>2' t\<^sub>2. \<forall>x.
              (s\<^sub>1 = t\<^sub>1 (\<subseteq> sources_aux (flow cfs\<^sub>2) s\<^sub>1 x) \<longrightarrow>
                (c', t\<^sub>1) \<rightarrow>* (c\<^sub>2', t\<^sub>2) \<and> (c'' = SKIP) = (c\<^sub>2' = SKIP)) \<and>
              (s\<^sub>1 = t\<^sub>1 (\<subseteq> sources (flow cfs\<^sub>2) s\<^sub>1 x) \<longrightarrow> s\<^sub>2 x = t\<^sub>2 x)) \<and>
            (\<forall>x.
              ((\<exists>s \<in> Univ? A X. \<exists>y \<in> bvars b. \<not> s: dom y \<leadsto> dom x) \<longrightarrow>
                no_upd (flow cfs\<^sub>2) x) \<and>
              ((\<exists>p \<in> U. case p of (B, W) \<Rightarrow>
                \<exists>s \<in> B. \<exists>y \<in> W. \<not> s: dom y \<leadsto> dom x) \<longrightarrow>
                  no_upd (flow cfs\<^sub>2) x))" and
    B: "\<And>U' B C s c' c'' s\<^sub>1 s\<^sub>2 cfs\<^sub>1 cfs\<^sub>2.
      U' = insert (Univ? A X, bvars b) U \<Longrightarrow> B = B\<^sub>1 \<Longrightarrow> C\<^sub>2 = C \<Longrightarrow>
        \<exists>r \<in> B\<^sub>2. s = r (\<subseteq> state \<inter> X) \<Longrightarrow>
          (c\<^sub>2, s) \<rightarrow>*{cfs\<^sub>1} (c', s\<^sub>1) \<Longrightarrow> (c', s\<^sub>1) \<rightarrow>*{cfs\<^sub>2} (c'', s\<^sub>2) \<Longrightarrow>
            (\<forall>t\<^sub>1. \<exists>c\<^sub>2' t\<^sub>2. \<forall>x.
              (s\<^sub>1 = t\<^sub>1 (\<subseteq> sources_aux (flow cfs\<^sub>2) s\<^sub>1 x) \<longrightarrow>
                (c', t\<^sub>1) \<rightarrow>* (c\<^sub>2', t\<^sub>2) \<and> (c'' = SKIP) = (c\<^sub>2' = SKIP)) \<and>
              (s\<^sub>1 = t\<^sub>1 (\<subseteq> sources (flow cfs\<^sub>2) s\<^sub>1 x) \<longrightarrow> s\<^sub>2 x = t\<^sub>2 x)) \<and>
            (\<forall>x.
              ((\<exists>s \<in> Univ? A X. \<exists>y \<in> bvars b. \<not> s: dom y \<leadsto> dom x) \<longrightarrow>
                no_upd (flow cfs\<^sub>2) x) \<and>
              ((\<exists>p \<in> U. case p of (B, W) \<Rightarrow>
                \<exists>s \<in> B. \<exists>y \<in> W. \<not> s: dom y \<leadsto> dom x) \<longrightarrow>
                  no_upd (flow cfs\<^sub>2) x))" and
    C: "\<Turnstile> b (\<subseteq> A, X) = (B\<^sub>1, B\<^sub>2)" and
    D: "(insert (Univ? A X, bvars b) U, v) \<Turnstile> c\<^sub>1 (\<subseteq> B\<^sub>1, X) =
      Some (C\<^sub>1, Y\<^sub>1)" and
    E: "(insert (Univ? A X, bvars b) U, v) \<Turnstile> c\<^sub>2 (\<subseteq> B\<^sub>2, X) =
      Some (C\<^sub>2, Y\<^sub>2)" and
    F: "(IF b THEN c\<^sub>1 ELSE c\<^sub>2, s) \<rightarrow>*{cfs\<^sub>1} (c', s\<^sub>1)" and
    G: "(c', s\<^sub>1) \<rightarrow>*{cfs\<^sub>2} (c'', s\<^sub>2)" and
    H: "r \<in> A" and
    I: "s = r (\<subseteq> state \<inter> X)"
  shows
   "(\<forall>t\<^sub>1. \<exists>c\<^sub>2' t\<^sub>2. \<forall>x.
      (s\<^sub>1 = t\<^sub>1 (\<subseteq> sources_aux (flow cfs\<^sub>2) s\<^sub>1 x) \<longrightarrow>
    (c', t\<^sub>1) \<rightarrow>* (c\<^sub>2', t\<^sub>2) \<and> (c'' = SKIP) = (c\<^sub>2' = SKIP)) \<and>
      (s\<^sub>1 = t\<^sub>1 (\<subseteq> sources (flow cfs\<^sub>2) s\<^sub>1 x) \<longrightarrow> s\<^sub>2 x = t\<^sub>2 x)) \<and>
    (\<forall>x. (\<exists>p \<in> U. case p of (B, W) \<Rightarrow>
      \<exists>s \<in> B. \<exists>y \<in> W. \<not> s: dom y \<leadsto> dom x) \<longrightarrow> no_upd (flow cfs\<^sub>2) x)"
proof -
  let ?U' = "insert (Univ? A X, bvars b) U"
  have J: "\<forall>cs t x. s = t (\<subseteq> sources_aux (\<langle>bvars b\<rangle> # cs) s x) \<longrightarrow>
    bval b s \<noteq> bval b t \<longrightarrow> \<not> Univ? A X: dom ` bvars b \<leadsto> {dom x}"
  proof (clarify del: notI)
    fix cs t x
    assume "s = t (\<subseteq> sources_aux (\<langle>bvars b\<rangle> # cs) s x)"
    moreover assume "bval b s \<noteq> bval b t"
    hence "\<not> s = t (\<subseteq> bvars b)"
      by (erule_tac contrapos_nn, auto dest: bvars_bval)
    ultimately have "\<not> (\<forall>y \<in> bvars b. s: dom y \<leadsto> dom x)"
      by (blast dest: sources_aux_observe_hd)
    moreover {
      fix r y
      assume "r \<in> A" and "y \<in> bvars b" and "\<not> s: dom y \<leadsto> dom x"
      moreover assume "state \<subseteq> X" and "s = r (\<subseteq> state \<inter> X)"
      hence "interf s = interf r"
        by (blast intro: interf_state)
      ultimately have "\<exists>s \<in> A. \<exists>y \<in> bvars b. \<not> s: dom y \<leadsto> dom x"
        by auto
    }
    ultimately show "\<not> Univ? A X: dom ` bvars b \<leadsto> {dom x}"
      using H and I by (auto simp: univ_states_if_def)
  qed
  have
   "(c', s\<^sub>1) = (IF b THEN c\<^sub>1 ELSE c\<^sub>2, s) \<or>
    bval b s \<and> (c\<^sub>1, s) \<rightarrow>*{tl cfs\<^sub>1} (c', s\<^sub>1) \<or>
    \<not> bval b s \<and> (c\<^sub>2, s) \<rightarrow>*{tl cfs\<^sub>1} (c', s\<^sub>1)"
    using F by (blast dest: small_stepsl_if)
  thus ?thesis
  proof (rule disjE, erule_tac [2] disjE, erule_tac [2-3] conjE)
    assume K: "(c', s\<^sub>1) = (IF b THEN c\<^sub>1 ELSE c\<^sub>2, s)"
    hence "(IF b THEN c\<^sub>1 ELSE c\<^sub>2, s) \<rightarrow>*{cfs\<^sub>2} (c'', s\<^sub>2)"
      using G by simp
    hence
     "(c'', s\<^sub>2) = (IF b THEN c\<^sub>1 ELSE c\<^sub>2, s) \<and>
        flow cfs\<^sub>2 = [] \<or>
      bval b s \<and> (c\<^sub>1, s) \<rightarrow>*{tl cfs\<^sub>2} (c'', s\<^sub>2) \<and>
        flow cfs\<^sub>2 = \<langle>bvars b\<rangle> # flow (tl cfs\<^sub>2) \<or>
      \<not> bval b s \<and> (c\<^sub>2, s) \<rightarrow>*{tl cfs\<^sub>2} (c'', s\<^sub>2) \<and>
        flow cfs\<^sub>2 = \<langle>bvars b\<rangle> # flow (tl cfs\<^sub>2)"
      by (rule small_stepsl_if)
    thus ?thesis
    proof (rule disjE, erule_tac [2] disjE, (erule_tac [2-3] conjE)+)
      assume "(c'', s\<^sub>2) = (IF b THEN c\<^sub>1 ELSE c\<^sub>2, s) \<and> flow cfs\<^sub>2 = []"
      thus ?thesis
        using K by auto
    next
      assume L: "bval b s"
      with C and H and I have "s \<in> Univ B\<^sub>1 (\<subseteq> state \<inter> X)"
        by (drule_tac btyping2_approx [where s = s], auto)
      moreover assume M: "(c\<^sub>1, s) \<rightarrow>*{tl cfs\<^sub>2} (c'', s\<^sub>2)"
      moreover from this have N: "s\<^sub>2 = run_flow (flow (tl cfs\<^sub>2)) s"
        by (rule small_stepsl_run_flow)
      ultimately have O:
       "(\<forall>t\<^sub>1. \<exists>c\<^sub>2' t\<^sub>2. \<forall>x.
          (s = t\<^sub>1 (\<subseteq> sources_aux (flow (tl cfs\<^sub>2)) s x) \<longrightarrow>
            (c\<^sub>1, t\<^sub>1) \<rightarrow>* (c\<^sub>2', t\<^sub>2) \<and> (c'' = SKIP) = (c\<^sub>2' = SKIP)) \<and>
          (s = t\<^sub>1 (\<subseteq> sources (flow (tl cfs\<^sub>2)) s x) \<longrightarrow>
            run_flow (flow (tl cfs\<^sub>2)) s x = t\<^sub>2 x)) \<and>
        (\<forall>x.
          ((\<exists>s \<in> Univ? A X. \<exists>y \<in> bvars b. \<not> s: dom y \<leadsto> dom x) \<longrightarrow>
            no_upd (flow (tl cfs\<^sub>2)) x) \<and>
          ((\<exists>p \<in> U. case p of (B, W) \<Rightarrow>
            \<exists>s \<in> B. \<exists>y \<in> W. \<not> s: dom y \<leadsto> dom x) \<longrightarrow>
              no_upd (flow (tl cfs\<^sub>2)) x))"
        using A [of ?U' B\<^sub>1 C\<^sub>1 s "[]" c\<^sub>1 s "tl cfs\<^sub>2" c'' s\<^sub>2] by simp
      moreover assume "flow cfs\<^sub>2 = \<langle>bvars b\<rangle> # flow (tl cfs\<^sub>2)"
      moreover {
        fix t\<^sub>1
        have "\<exists>c\<^sub>2' t\<^sub>2. \<forall>x.
          (s = t\<^sub>1 (\<subseteq> sources_aux (\<langle>bvars b\<rangle> # flow (tl cfs\<^sub>2)) s x) \<longrightarrow>
            (IF b THEN c\<^sub>1 ELSE c\<^sub>2, t\<^sub>1) \<rightarrow>* (c\<^sub>2', t\<^sub>2) \<and>
            (c'' = SKIP) = (c\<^sub>2' = SKIP)) \<and>
          (s = t\<^sub>1 (\<subseteq> sources (\<langle>bvars b\<rangle> # flow (tl cfs\<^sub>2)) s x) \<longrightarrow>
            run_flow (flow (tl cfs\<^sub>2)) s x = t\<^sub>2 x)"
        proof (cases "bval b t\<^sub>1")
          case True
          hence P: "(IF b THEN c\<^sub>1 ELSE c\<^sub>2, t\<^sub>1) \<rightarrow> (c\<^sub>1, t\<^sub>1)" ..
          obtain c\<^sub>2' and t\<^sub>2 where Q: "\<forall>x.
            (s = t\<^sub>1 (\<subseteq> sources_aux (flow (tl cfs\<^sub>2)) s x) \<longrightarrow>
              (c\<^sub>1, t\<^sub>1) \<rightarrow>* (c\<^sub>2', t\<^sub>2) \<and> (c'' = SKIP) = (c\<^sub>2' = SKIP)) \<and>
            (s = t\<^sub>1 (\<subseteq> sources (flow (tl cfs\<^sub>2)) s x) \<longrightarrow>
              run_flow (flow (tl cfs\<^sub>2)) s x = t\<^sub>2 x)"
            using O by blast
          {
            fix x
            assume "s = t\<^sub>1
              (\<subseteq> sources_aux (\<langle>bvars b\<rangle> # flow (tl cfs\<^sub>2)) s x)"
            moreover have "sources_aux (flow (tl cfs\<^sub>2)) s x \<subseteq>
              sources_aux (\<langle>bvars b\<rangle> # flow (tl cfs\<^sub>2)) s x"
              by (rule sources_aux_observe_tl)
            ultimately have "(IF b THEN c\<^sub>1 ELSE c\<^sub>2, t\<^sub>1) \<rightarrow>* (c\<^sub>2', t\<^sub>2) \<and>
              (c'' = SKIP) = (c\<^sub>2' = SKIP)"
              using P and Q by (blast intro: star_trans)
          }
          moreover {
            fix x
            assume "s = t\<^sub>1
              (\<subseteq> sources (\<langle>bvars b\<rangle> # flow (tl cfs\<^sub>2)) s x)"
            moreover have "sources (flow (tl cfs\<^sub>2)) s x \<subseteq>
              sources (\<langle>bvars b\<rangle> # flow (tl cfs\<^sub>2)) s x"
              by (rule sources_observe_tl)
            ultimately have "run_flow (flow (tl cfs\<^sub>2)) s x = t\<^sub>2 x"
              using Q by blast
          }
          ultimately show ?thesis
            by auto
        next
          assume P: "\<not> bval b t\<^sub>1"
          show ?thesis
          proof (cases "\<exists>x. s = t\<^sub>1
           (\<subseteq> sources_aux (\<langle>bvars b\<rangle> # flow (tl cfs\<^sub>2)) s x)")
            from P have "(IF b THEN c\<^sub>1 ELSE c\<^sub>2, t\<^sub>1) \<rightarrow> (c\<^sub>2, t\<^sub>1)" ..
            moreover assume "\<exists>x. s = t\<^sub>1
              (\<subseteq> sources_aux (\<langle>bvars b\<rangle> # flow (tl cfs\<^sub>2)) s x)"
            hence "\<exists>x. \<not> Univ? A X: dom ` bvars b \<leadsto> {dom x}"
              using J and L and P by blast
            then obtain t\<^sub>2 where Q: "(c\<^sub>2, t\<^sub>1) \<Rightarrow> t\<^sub>2"
              using E by (blast dest: ctyping2_term)
            hence "(c\<^sub>2, t\<^sub>1) \<rightarrow>* (SKIP, t\<^sub>2)"
              by (simp add: big_iff_small)
            ultimately have
              R: "(IF b THEN c\<^sub>1 ELSE c\<^sub>2, t\<^sub>1) \<rightarrow>* (SKIP, t\<^sub>2)"
              by (blast intro: star_trans)
            show ?thesis
            proof (cases "c'' = SKIP")
              case True
              show ?thesis
              proof (rule exI [of _ SKIP], rule exI [of _ t\<^sub>2])
                {
                  have "(IF b THEN c\<^sub>1 ELSE c\<^sub>2, t\<^sub>1) \<rightarrow>* (SKIP, t\<^sub>2) \<and>
                    (c'' = SKIP) = (SKIP = SKIP)"
                    using R and True by simp
                }
                moreover {
                  fix x
                  assume S: "s = t\<^sub>1
                    (\<subseteq> sources (\<langle>bvars b\<rangle> # flow (tl cfs\<^sub>2)) s x)"
                  moreover have
                   "sources_aux (\<langle>bvars b\<rangle> # flow (tl cfs\<^sub>2)) s x \<subseteq>
                    sources (\<langle>bvars b\<rangle> # flow (tl cfs\<^sub>2)) s x"
                    by (rule sources_aux_sources)
                  ultimately have "s = t\<^sub>1
                    (\<subseteq> sources_aux (\<langle>bvars b\<rangle> # flow (tl cfs\<^sub>2)) s x)"
                    by blast
                  hence T: "\<not> Univ? A X: dom ` bvars b \<leadsto> {dom x}"
                    using J and L and P by blast
                  hence U: "no_upd (\<langle>bvars b\<rangle> # flow (tl cfs\<^sub>2)) x"
                    using O by simp
                  hence "run_flow (flow (tl cfs\<^sub>2)) s x = s x"
                    by (simp add: no_upd_run_flow)
                  also from S and U have "\<dots> = t\<^sub>1 x"
                    by (blast dest: no_upd_sources)
                  also from E and Q and T have "\<dots> = t\<^sub>2 x"
                    by (drule_tac ctyping2_confine, auto)
                  finally have "run_flow (flow (tl cfs\<^sub>2)) s x = t\<^sub>2 x" .
                }
                ultimately show "\<forall>x.
                  (s = t\<^sub>1
                    (\<subseteq> sources_aux (\<langle>bvars b\<rangle> # flow (tl cfs\<^sub>2)) s x) \<longrightarrow>
                      (IF b THEN c\<^sub>1 ELSE c\<^sub>2, t\<^sub>1) \<rightarrow>* (SKIP, t\<^sub>2) \<and>
                        (c'' = SKIP) = (SKIP = SKIP)) \<and>
                  (s = t\<^sub>1
                    (\<subseteq> sources (\<langle>bvars b\<rangle> # flow (tl cfs\<^sub>2)) s x) \<longrightarrow>
                      run_flow (flow (tl cfs\<^sub>2)) s x = t\<^sub>2 x)"
                  by blast
              qed
            next
              case False
              show ?thesis
              proof (rule exI [of _ "IF b THEN c\<^sub>1 ELSE c\<^sub>2"],
               rule exI [of _ t\<^sub>1])
                {
                  have "(IF b THEN c\<^sub>1 ELSE c\<^sub>2, t\<^sub>1) \<rightarrow>*
                    (IF b THEN c\<^sub>1 ELSE c\<^sub>2, t\<^sub>1) \<and>
                      (c'' = SKIP) = (IF b THEN c\<^sub>1 ELSE c\<^sub>2 = SKIP)"
                    using False by simp
                }
                moreover {
                  fix x
                  assume S: "s = t\<^sub>1
                    (\<subseteq> sources (\<langle>bvars b\<rangle> # flow (tl cfs\<^sub>2)) s x)"
                  moreover have
                   "sources_aux (\<langle>bvars b\<rangle> # flow (tl cfs\<^sub>2)) s x \<subseteq>
                    sources (\<langle>bvars b\<rangle> # flow (tl cfs\<^sub>2)) s x"
                    by (rule sources_aux_sources)
                  ultimately have "s = t\<^sub>1
                    (\<subseteq> sources_aux (\<langle>bvars b\<rangle> # flow (tl cfs\<^sub>2)) s x)"
                    by blast
                  hence "\<not> Univ? A X: dom ` bvars b \<leadsto> {dom x}"
                    using J and L and P by blast
                  hence T: "no_upd (\<langle>bvars b\<rangle> # flow (tl cfs\<^sub>2)) x"
                    using O by simp
                  hence "run_flow (flow (tl cfs\<^sub>2)) s x = s x"
                    by (simp add: no_upd_run_flow)
                  also have "\<dots> = t\<^sub>1 x"
                    using S and T by (blast dest: no_upd_sources)
                  finally have "run_flow (flow (tl cfs\<^sub>2)) s x = t\<^sub>1 x" .
                }
                ultimately show "\<forall>x.
                  (s = t\<^sub>1
                    (\<subseteq> sources_aux (\<langle>bvars b\<rangle> # flow (tl cfs\<^sub>2)) s x) \<longrightarrow>
                      (IF b THEN c\<^sub>1 ELSE c\<^sub>2, t\<^sub>1) \<rightarrow>*
                        (IF b THEN c\<^sub>1 ELSE c\<^sub>2, t\<^sub>1) \<and>
                          (c'' = SKIP) = (IF b THEN c\<^sub>1 ELSE c\<^sub>2 = SKIP)) \<and>
                  (s = t\<^sub>1
                    (\<subseteq> sources (\<langle>bvars b\<rangle> # flow (tl cfs\<^sub>2)) s x) \<longrightarrow>
                      run_flow (flow (tl cfs\<^sub>2)) s x = t\<^sub>1 x)"
                  by blast
              qed
            qed
          qed blast
        qed
      }
      ultimately show ?thesis
        using K and N by auto
    next
      assume L: "\<not> bval b s"
      with C and H and I have "s \<in> Univ B\<^sub>2 (\<subseteq> state \<inter> X)"
        by (drule_tac btyping2_approx [where s = s], auto)
      moreover assume M: "(c\<^sub>2, s) \<rightarrow>*{tl cfs\<^sub>2} (c'', s\<^sub>2)"
      moreover from this have N: "s\<^sub>2 = run_flow (flow (tl cfs\<^sub>2)) s"
        by (rule small_stepsl_run_flow)
      ultimately have O:
       "(\<forall>t\<^sub>1. \<exists>c\<^sub>2' t\<^sub>2. \<forall>x.
          (s = t\<^sub>1 (\<subseteq> sources_aux (flow (tl cfs\<^sub>2)) s x) \<longrightarrow>
            (c\<^sub>2, t\<^sub>1) \<rightarrow>* (c\<^sub>2', t\<^sub>2) \<and> (c'' = SKIP) = (c\<^sub>2' = SKIP)) \<and>
          (s = t\<^sub>1 (\<subseteq> sources (flow (tl cfs\<^sub>2)) s x) \<longrightarrow>
            run_flow (flow (tl cfs\<^sub>2)) s x = t\<^sub>2 x)) \<and>
        (\<forall>x.
          ((\<exists>s \<in> Univ? A X. \<exists>y \<in> bvars b. \<not> s: dom y \<leadsto> dom x) \<longrightarrow>
            no_upd (flow (tl cfs\<^sub>2)) x) \<and>
          ((\<exists>p \<in> U. case p of (B, W) \<Rightarrow>
            \<exists>s \<in> B. \<exists>y \<in> W. \<not> s: dom y \<leadsto> dom x) \<longrightarrow>
              no_upd (flow (tl cfs\<^sub>2)) x))"
        using B [of ?U' B\<^sub>1 C\<^sub>2 s "[]" c\<^sub>2 s "tl cfs\<^sub>2" c'' s\<^sub>2] by simp
      moreover assume "flow cfs\<^sub>2 = \<langle>bvars b\<rangle> # flow (tl cfs\<^sub>2)"
      moreover {
        fix t\<^sub>1
        have "\<exists>c\<^sub>2' t\<^sub>2. \<forall>x.
          (s = t\<^sub>1 (\<subseteq> sources_aux (\<langle>bvars b\<rangle> # flow (tl cfs\<^sub>2)) s x) \<longrightarrow>
            (IF b THEN c\<^sub>1 ELSE c\<^sub>2, t\<^sub>1) \<rightarrow>* (c\<^sub>2', t\<^sub>2) \<and>
            (c'' = SKIP) = (c\<^sub>2' = SKIP)) \<and>
          (s = t\<^sub>1 (\<subseteq> sources (\<langle>bvars b\<rangle> # flow (tl cfs\<^sub>2)) s x) \<longrightarrow>
            run_flow (flow (tl cfs\<^sub>2)) s x = t\<^sub>2 x)"
        proof (cases "\<not> bval b t\<^sub>1")
          case True
          hence P: "(IF b THEN c\<^sub>1 ELSE c\<^sub>2, t\<^sub>1) \<rightarrow> (c\<^sub>2, t\<^sub>1)" ..
          obtain c\<^sub>2' and t\<^sub>2 where Q: "\<forall>x.
            (s = t\<^sub>1 (\<subseteq> sources_aux (flow (tl cfs\<^sub>2)) s x) \<longrightarrow>
              (c\<^sub>2, t\<^sub>1) \<rightarrow>* (c\<^sub>2', t\<^sub>2) \<and> (c'' = SKIP) = (c\<^sub>2' = SKIP)) \<and>
            (s = t\<^sub>1 (\<subseteq> sources (flow (tl cfs\<^sub>2)) s x) \<longrightarrow>
              run_flow (flow (tl cfs\<^sub>2)) s x = t\<^sub>2 x)"
            using O by blast
          {
            fix x
            assume "s = t\<^sub>1
              (\<subseteq> sources_aux (\<langle>bvars b\<rangle> # flow (tl cfs\<^sub>2)) s x)"
            moreover have "sources_aux (flow (tl cfs\<^sub>2)) s x \<subseteq>
              sources_aux (\<langle>bvars b\<rangle> # flow (tl cfs\<^sub>2)) s x"
              by (rule sources_aux_observe_tl)
            ultimately have "(IF b THEN c\<^sub>1 ELSE c\<^sub>2, t\<^sub>1) \<rightarrow>* (c\<^sub>2', t\<^sub>2) \<and>
              (c'' = SKIP) = (c\<^sub>2' = SKIP)"
              using P and Q by (blast intro: star_trans)
          }
          moreover {
            fix x
            assume "s = t\<^sub>1
              (\<subseteq> sources (\<langle>bvars b\<rangle> # flow (tl cfs\<^sub>2)) s x)"
            moreover have "sources (flow (tl cfs\<^sub>2)) s x \<subseteq>
              sources (\<langle>bvars b\<rangle> # flow (tl cfs\<^sub>2)) s x"
              by (rule sources_observe_tl)
            ultimately have "run_flow (flow (tl cfs\<^sub>2)) s x = t\<^sub>2 x"
              using Q by blast
          }
          ultimately show ?thesis
            by auto
        next
          case False
          hence P: "bval b t\<^sub>1"
            by simp
          show ?thesis
          proof (cases "\<exists>x. s = t\<^sub>1
           (\<subseteq> sources_aux (\<langle>bvars b\<rangle> # flow (tl cfs\<^sub>2)) s x)")
            from P have "(IF b THEN c\<^sub>1 ELSE c\<^sub>2, t\<^sub>1) \<rightarrow> (c\<^sub>1, t\<^sub>1)" ..
            moreover assume "\<exists>x. s = t\<^sub>1
              (\<subseteq> sources_aux (\<langle>bvars b\<rangle> # flow (tl cfs\<^sub>2)) s x)"
            hence "\<exists>x. \<not> Univ? A X: dom ` bvars b \<leadsto> {dom x}"
              using J and L and P by blast
            then obtain t\<^sub>2 where Q: "(c\<^sub>1, t\<^sub>1) \<Rightarrow> t\<^sub>2"
              using D by (blast dest: ctyping2_term)
            hence "(c\<^sub>1, t\<^sub>1) \<rightarrow>* (SKIP, t\<^sub>2)"
              by (simp add: big_iff_small)
            ultimately have
              R: "(IF b THEN c\<^sub>1 ELSE c\<^sub>2, t\<^sub>1) \<rightarrow>* (SKIP, t\<^sub>2)"
              by (blast intro: star_trans)
            show ?thesis
            proof (cases "c'' = SKIP")
              case True
              show ?thesis
              proof (rule exI [of _ SKIP], rule exI [of _ t\<^sub>2])
                {
                  have "(IF b THEN c\<^sub>1 ELSE c\<^sub>2, t\<^sub>1) \<rightarrow>* (SKIP, t\<^sub>2) \<and>
                    (c'' = SKIP) = (SKIP = SKIP)"
                    using R and True by simp
                }
                moreover {
                  fix x
                  assume S: "s = t\<^sub>1
                    (\<subseteq> sources (\<langle>bvars b\<rangle> # flow (tl cfs\<^sub>2)) s x)"
                  moreover have
                   "sources_aux (\<langle>bvars b\<rangle> # flow (tl cfs\<^sub>2)) s x \<subseteq>
                    sources (\<langle>bvars b\<rangle> # flow (tl cfs\<^sub>2)) s x"
                    by (rule sources_aux_sources)
                  ultimately have "s = t\<^sub>1
                    (\<subseteq> sources_aux (\<langle>bvars b\<rangle> # flow (tl cfs\<^sub>2)) s x)"
                    by blast
                  hence T: "\<not> Univ? A X: dom ` bvars b \<leadsto> {dom x}"
                    using J and L and P by blast
                  hence U: "no_upd (\<langle>bvars b\<rangle> # flow (tl cfs\<^sub>2)) x"
                    using O by simp
                  hence "run_flow (flow (tl cfs\<^sub>2)) s x = s x"
                    by (simp add: no_upd_run_flow)
                  also from S and U have "\<dots> = t\<^sub>1 x"
                    by (blast dest: no_upd_sources)
                  also from D and Q and T have "\<dots> = t\<^sub>2 x"
                    by (drule_tac ctyping2_confine, auto)
                  finally have "run_flow (flow (tl cfs\<^sub>2)) s x = t\<^sub>2 x" .
                }
                ultimately show "\<forall>x.
                  (s = t\<^sub>1
                    (\<subseteq> sources_aux (\<langle>bvars b\<rangle> # flow (tl cfs\<^sub>2)) s x) \<longrightarrow>
                      (IF b THEN c\<^sub>1 ELSE c\<^sub>2, t\<^sub>1) \<rightarrow>* (SKIP, t\<^sub>2) \<and>
                        (c'' = SKIP) = (SKIP = SKIP)) \<and>
                  (s = t\<^sub>1
                    (\<subseteq> sources (\<langle>bvars b\<rangle> # flow (tl cfs\<^sub>2)) s x) \<longrightarrow>
                      run_flow (flow (tl cfs\<^sub>2)) s x = t\<^sub>2 x)"
                  by blast
              qed
            next
              case False
              show ?thesis
              proof (rule exI [of _ "IF b THEN c\<^sub>1 ELSE c\<^sub>2"],
               rule exI [of _ t\<^sub>1])
                {
                  have "(IF b THEN c\<^sub>1 ELSE c\<^sub>2, t\<^sub>1) \<rightarrow>*
                    (IF b THEN c\<^sub>1 ELSE c\<^sub>2, t\<^sub>1) \<and>
                      (c'' = SKIP) = (IF b THEN c\<^sub>1 ELSE c\<^sub>2 = SKIP)"
                    using False by simp
                }
                moreover {
                  fix x
                  assume S: "s = t\<^sub>1
                    (\<subseteq> sources (\<langle>bvars b\<rangle> # flow (tl cfs\<^sub>2)) s x)"
                  moreover have
                   "sources_aux (\<langle>bvars b\<rangle> # flow (tl cfs\<^sub>2)) s x \<subseteq>
                    sources (\<langle>bvars b\<rangle> # flow (tl cfs\<^sub>2)) s x"
                    by (rule sources_aux_sources)
                  ultimately have "s = t\<^sub>1
                    (\<subseteq> sources_aux (\<langle>bvars b\<rangle> # flow (tl cfs\<^sub>2)) s x)"
                    by blast
                  hence "\<not> Univ? A X: dom ` bvars b \<leadsto> {dom x}"
                    using J and L and P by blast
                  hence T: "no_upd (\<langle>bvars b\<rangle> # flow (tl cfs\<^sub>2)) x"
                    using O by simp
                  hence "run_flow (flow (tl cfs\<^sub>2)) s x = s x"
                    by (simp add: no_upd_run_flow)
                  also have "\<dots> = t\<^sub>1 x"
                    using S and T by (blast dest: no_upd_sources)
                  finally have "run_flow (flow (tl cfs\<^sub>2)) s x = t\<^sub>1 x" .
                }
                ultimately show "\<forall>x.
                  (s = t\<^sub>1
                    (\<subseteq> sources_aux (\<langle>bvars b\<rangle> # flow (tl cfs\<^sub>2)) s x) \<longrightarrow>
                      (IF b THEN c\<^sub>1 ELSE c\<^sub>2, t\<^sub>1) \<rightarrow>*
                        (IF b THEN c\<^sub>1 ELSE c\<^sub>2, t\<^sub>1) \<and>
                        (c'' = SKIP) = (IF b THEN c\<^sub>1 ELSE c\<^sub>2 = SKIP)) \<and>
                  (s = t\<^sub>1
                    (\<subseteq> sources (\<langle>bvars b\<rangle> # flow (tl cfs\<^sub>2)) s x) \<longrightarrow>
                      run_flow (flow (tl cfs\<^sub>2)) s x = t\<^sub>1 x)"
                  by blast
              qed
            qed
          qed blast
        qed
      }
      ultimately show ?thesis
        using K and N by auto
    qed
  next
    assume "bval b s" and "(c\<^sub>1, s) \<rightarrow>*{tl cfs\<^sub>1} (c', s\<^sub>1)"
    moreover from this and C and H and I have "s \<in> Univ B\<^sub>1 (\<subseteq> state \<inter> X)"
      by (drule_tac btyping2_approx [where s = s], auto)
    ultimately show ?thesis
      using A [of ?U' B\<^sub>1 C\<^sub>1 s "tl cfs\<^sub>1" c' s\<^sub>1 cfs\<^sub>2 c'' s\<^sub>2] and G by simp
  next
    assume "\<not> bval b s" and "(c\<^sub>2, s) \<rightarrow>*{tl cfs\<^sub>1} (c', s\<^sub>1)"
    moreover from this and C and H and I have "s \<in> Univ B\<^sub>2 (\<subseteq> state \<inter> X)"
      by (drule_tac btyping2_approx [where s = s], auto)
    ultimately show ?thesis
      using B [of ?U' B\<^sub>1 C\<^sub>2 s "tl cfs\<^sub>1" c' s\<^sub>1 cfs\<^sub>2 c'' s\<^sub>2] and G by simp
  qed
qed

lemma ctyping2_correct_aux_while:
  assumes
    A: "\<And>B C' B' D' s c\<^sub>1 c\<^sub>2 s\<^sub>1 s\<^sub>2 cfs\<^sub>1 cfs\<^sub>2.
      B = B\<^sub>1 \<Longrightarrow> C' = C \<Longrightarrow> B' = B\<^sub>1' \<Longrightarrow>
      (\<forall>s \<in> Univ? A X \<union> Univ? C Y. \<forall>x \<in> bvars b. All (interf s (dom x))) \<and>
      (\<forall>p \<in> U. case p of (B, W) \<Rightarrow> \<forall>s \<in> B. \<forall>x \<in> W. All (interf s (dom x))) \<Longrightarrow>
        D = D' \<Longrightarrow> \<exists>r \<in> B\<^sub>1. s = r (\<subseteq> state \<inter> X) \<Longrightarrow>
          (c, s) \<rightarrow>*{cfs\<^sub>1} (c\<^sub>1, s\<^sub>1) \<Longrightarrow> (c\<^sub>1, s\<^sub>1) \<rightarrow>*{cfs\<^sub>2} (c\<^sub>2, s\<^sub>2) \<Longrightarrow>
            \<forall>t\<^sub>1. \<exists>c\<^sub>2' t\<^sub>2. \<forall>x.
              (s\<^sub>1 = t\<^sub>1 (\<subseteq> sources_aux (flow cfs\<^sub>2) s\<^sub>1 x) \<longrightarrow>
                (c\<^sub>1, t\<^sub>1) \<rightarrow>* (c\<^sub>2', t\<^sub>2) \<and> (c\<^sub>2 = SKIP) = (c\<^sub>2' = SKIP)) \<and>
              (s\<^sub>1 = t\<^sub>1 (\<subseteq> sources (flow cfs\<^sub>2) s\<^sub>1 x) \<longrightarrow> s\<^sub>2 x = t\<^sub>2 x)" and
    B: "\<And>B C' B' D'' s c\<^sub>1 c\<^sub>2 s\<^sub>1 s\<^sub>2 cfs\<^sub>1 cfs\<^sub>2.
      B = B\<^sub>1 \<Longrightarrow> C' = C \<Longrightarrow> B' = B\<^sub>1' \<Longrightarrow>
      (\<forall>s \<in> Univ? A X \<union> Univ? C Y. \<forall>x \<in> bvars b. All (interf s (dom x))) \<and>
      (\<forall>p \<in> U. case p of (B, W) \<Rightarrow> \<forall>s \<in> B. \<forall>x \<in> W. All (interf s (dom x))) \<Longrightarrow>
        D' = D'' \<Longrightarrow> \<exists>r \<in> B\<^sub>1'. s = r (\<subseteq> state \<inter> Y) \<Longrightarrow>
          (c, s) \<rightarrow>*{cfs\<^sub>1} (c\<^sub>1, s\<^sub>1) \<Longrightarrow> (c\<^sub>1, s\<^sub>1) \<rightarrow>*{cfs\<^sub>2} (c\<^sub>2, s\<^sub>2) \<Longrightarrow>
            \<forall>t\<^sub>1. \<exists>c\<^sub>2' t\<^sub>2. \<forall>x.
              (s\<^sub>1 = t\<^sub>1 (\<subseteq> sources_aux (flow cfs\<^sub>2) s\<^sub>1 x) \<longrightarrow>
                (c\<^sub>1, t\<^sub>1) \<rightarrow>* (c\<^sub>2', t\<^sub>2) \<and> (c\<^sub>2 = SKIP) = (c\<^sub>2' = SKIP)) \<and>
              (s\<^sub>1 = t\<^sub>1 (\<subseteq> sources (flow cfs\<^sub>2) s\<^sub>1 x) \<longrightarrow> s\<^sub>2 x = t\<^sub>2 x)" and
    C: "(if (\<forall>s \<in> Univ? A X \<union> Univ? C Y. \<forall>x \<in> bvars b. All (interf s (dom x))) \<and>
      (\<forall>p \<in> U. \<forall>B W. p = (B, W) \<longrightarrow> (\<forall>s \<in> B. \<forall>x \<in> W. All (interf s (dom x))))
        then Some (B\<^sub>2 \<union> B\<^sub>2', Univ?? B\<^sub>2 X \<inter> Y) else None) = Some (B, W)" and
    D: "\<Turnstile> b (\<subseteq> A, X) = (B\<^sub>1, B\<^sub>2)" and
    E: "\<turnstile> c (\<subseteq> B\<^sub>1, X) = (C, Y)" and
    F: "\<Turnstile> b (\<subseteq> C, Y) = (B\<^sub>1', B\<^sub>2')" and
    G: "({}, False) \<Turnstile> c (\<subseteq> B\<^sub>1, X) = Some (D, Z)" and
    H: "({}, False) \<Turnstile> c (\<subseteq> B\<^sub>1', Y) = Some (D', Z')"
  shows
   "\<lbrakk>(WHILE b DO c, s) \<rightarrow>*{cfs\<^sub>1} (c\<^sub>1, s\<^sub>1);
      (c\<^sub>1, s\<^sub>1) \<rightarrow>*{cfs\<^sub>2} (c\<^sub>2, s\<^sub>2);
      s \<in> Univ A (\<subseteq> state \<inter> X) \<union> Univ C (\<subseteq> state \<inter> Y)\<rbrakk> \<Longrightarrow>
    (\<forall>t\<^sub>1. \<exists>c\<^sub>2' t\<^sub>2. \<forall>x.
      (s\<^sub>1 = t\<^sub>1 (\<subseteq> sources_aux (flow cfs\<^sub>2) s\<^sub>1 x) \<longrightarrow>
        (c\<^sub>1, t\<^sub>1) \<rightarrow>* (c\<^sub>2', t\<^sub>2) \<and> (c\<^sub>2 = SKIP) = (c\<^sub>2' = SKIP)) \<and>
      (s\<^sub>1 = t\<^sub>1 (\<subseteq> sources (flow cfs\<^sub>2) s\<^sub>1 x) \<longrightarrow> s\<^sub>2 x = t\<^sub>2 x)) \<and>
    (\<forall>x. (\<exists>p \<in> U. case p of (B, W) \<Rightarrow>
      \<exists>s \<in> B. \<exists>y \<in> W. \<not> s: dom y \<leadsto> dom x) \<longrightarrow> no_upd (flow cfs\<^sub>2) x)"
proof (induction "cfs\<^sub>1 @ cfs\<^sub>2" arbitrary: cfs\<^sub>1 cfs\<^sub>2 s c\<^sub>1 s\<^sub>1 rule: length_induct)
  fix cfs\<^sub>1 cfs\<^sub>2 s c\<^sub>1 s\<^sub>1
  assume
    I: "(WHILE b DO c, s) \<rightarrow>*{cfs\<^sub>1} (c\<^sub>1, s\<^sub>1)" and
    J: "(c\<^sub>1, s\<^sub>1) \<rightarrow>*{cfs\<^sub>2} (c\<^sub>2, s\<^sub>2)"
  assume "\<forall>cfs. length cfs < length (cfs\<^sub>1 @ cfs\<^sub>2) \<longrightarrow>
      (\<forall>cfs\<^sub>1 cfs\<^sub>2. cfs = cfs\<^sub>1 @ cfs\<^sub>2 \<longrightarrow>
        (\<forall>s c\<^sub>1 s\<^sub>1. (WHILE b DO c, s) \<rightarrow>*{cfs\<^sub>1} (c\<^sub>1, s\<^sub>1) \<longrightarrow>
          (c\<^sub>1, s\<^sub>1) \<rightarrow>*{cfs\<^sub>2} (c\<^sub>2, s\<^sub>2) \<longrightarrow>
            s \<in> Univ A (\<subseteq> state \<inter> X) \<union> Univ C (\<subseteq> state \<inter> Y) \<longrightarrow>
              (\<forall>t\<^sub>1. \<exists>c\<^sub>2' t\<^sub>2. \<forall>x.
                (s\<^sub>1 = t\<^sub>1 (\<subseteq> sources_aux (flow cfs\<^sub>2) s\<^sub>1 x) \<longrightarrow>
                  (c\<^sub>1, t\<^sub>1) \<rightarrow>* (c\<^sub>2', t\<^sub>2) \<and> (c\<^sub>2 = SKIP) = (c\<^sub>2' = SKIP)) \<and>
                (s\<^sub>1 = t\<^sub>1 (\<subseteq> sources (flow cfs\<^sub>2) s\<^sub>1 x) \<longrightarrow> s\<^sub>2 x = t\<^sub>2 x)) \<and>
              (\<forall>x. (\<exists>(B, W) \<in> U. \<exists>s \<in> B. \<exists>y \<in> W. \<not> s: dom y \<leadsto> dom x) \<longrightarrow>
                no_upd (flow cfs\<^sub>2) x)))"
  note K = this [rule_format]
  assume L: "s \<in> Univ A (\<subseteq> state \<inter> X) \<union> Univ C (\<subseteq> state \<inter> Y)"
  moreover {
    fix s'
    assume "s \<in> Univ A (\<subseteq> state \<inter> X)" and "bval b s"
    hence N: "s \<in> Univ B\<^sub>1 (\<subseteq> state \<inter> X)"
      using D by (drule_tac btyping2_approx, auto)
    assume "(c, s) \<Rightarrow> s'"
    hence "s' \<in> Univ D (\<subseteq> state \<inter> Z)"
      using G and N by (rule ctyping2_approx)
    moreover have "D \<subseteq> C \<and> Y \<subseteq> Z"
      using E and G by (rule ctyping1_ctyping2)
    ultimately have "s' \<in> Univ C (\<subseteq> state \<inter> Y)"
      by blast
  }
  moreover {
    fix s'
    assume "s \<in> Univ C (\<subseteq> state \<inter> Y)" and "bval b s"
    hence N: "s \<in> Univ B\<^sub>1' (\<subseteq> state \<inter> Y)"
      using F by (drule_tac btyping2_approx, auto)
    assume "(c, s) \<Rightarrow> s'"
    hence "s' \<in> Univ D' (\<subseteq> state \<inter> Z')"
      using H and N by (rule ctyping2_approx)
    moreover obtain C' and Y' where O: "\<turnstile> c (\<subseteq> B\<^sub>1', Y) = (C', Y')"
      by (cases "\<turnstile> c (\<subseteq> B\<^sub>1', Y)", simp)
    hence "D' \<subseteq> C' \<and> Y' \<subseteq> Z'"
      using H by (rule ctyping1_ctyping2)
    ultimately have P: "s' \<in> Univ C' (\<subseteq> state \<inter> Y')"
      by blast
    have "\<turnstile> c (\<subseteq> C, Y) = (C, Y)"
      using E by (rule ctyping1_idem)
    moreover have "B\<^sub>1' \<subseteq> C"
      using F by (blast dest: btyping2_un_eq)
    ultimately have "C' \<subseteq> C \<and> Y \<subseteq> Y'"
      by (metis order_refl ctyping1_mono O)
    hence "s' \<in> Univ C (\<subseteq> state \<inter> Y)"
      using P by blast
  }
  ultimately have M:
   "\<forall>s'. (c, s) \<Rightarrow> s' \<longrightarrow> bval b s \<longrightarrow> s' \<in> Univ C (\<subseteq> state \<inter> Y)"
    by blast
  have N:
   "(\<forall>s \<in> Univ? A X \<union> Univ? C Y. \<forall>x \<in> bvars b. All (interf s (dom x))) \<and>
    (\<forall>p \<in> U. \<forall>B W. p = (B, W) \<longrightarrow> (\<forall>s \<in> B. \<forall>x \<in> W. All (interf s (dom x))))"
    using C by (simp split: if_split_asm)
  hence "\<forall>cs x. (\<exists>(B, Y) \<in> U.
    \<exists>s \<in> B. \<exists>y \<in> Y. \<not> s: dom y \<leadsto> dom x) \<longrightarrow> no_upd cs x"
    by auto
  moreover {
    fix r t\<^sub>1
    assume O: "r \<in> A" and P: "s = r (\<subseteq> state \<inter> X)"
    have Q: "\<forall>x. \<forall>y \<in> bvars b. s: dom y \<leadsto> dom x"
    proof (cases "state \<subseteq> X")
      case True
      with P have "interf s = interf r"
        by (blast intro: interf_state)
      with N and O show ?thesis
        by (erule_tac conjE, drule_tac bspec,
         auto simp: univ_states_if_def)
    next
      case False
      with N and O show ?thesis
        by (erule_tac conjE, drule_tac bspec,
         auto simp: univ_states_if_def)
    qed
    have "(c\<^sub>1, s\<^sub>1) = (WHILE b DO c, s) \<or>
      (IF b THEN c;; WHILE b DO c ELSE SKIP, s) \<rightarrow>*{tl cfs\<^sub>1} (c\<^sub>1, s\<^sub>1)"
      using I by (blast dest: small_stepsl_while)
    hence "\<exists>c\<^sub>2' t\<^sub>2. \<forall>x.
      (s\<^sub>1 = t\<^sub>1 (\<subseteq> sources_aux (flow cfs\<^sub>2) s\<^sub>1 x) \<longrightarrow>
        (c\<^sub>1, t\<^sub>1) \<rightarrow>* (c\<^sub>2', t\<^sub>2) \<and> (c\<^sub>2 = SKIP) = (c\<^sub>2' = SKIP)) \<and>
      (s\<^sub>1 = t\<^sub>1 (\<subseteq> sources (flow cfs\<^sub>2) s\<^sub>1 x) \<longrightarrow> s\<^sub>2 x = t\<^sub>2 x)"
    proof
      assume R: "(c\<^sub>1, s\<^sub>1) = (WHILE b DO c, s)"
      hence "(WHILE b DO c, s) \<rightarrow>*{cfs\<^sub>2} (c\<^sub>2, s\<^sub>2)"
        using J by simp
      hence
       "(c\<^sub>2, s\<^sub>2) = (WHILE b DO c, s) \<and>
          flow cfs\<^sub>2 = [] \<or>
        (IF b THEN c;; WHILE b DO c ELSE SKIP, s) \<rightarrow>*{tl cfs\<^sub>2} (c\<^sub>2, s\<^sub>2) \<and>
          flow cfs\<^sub>2 = flow (tl cfs\<^sub>2)"
        (is "?P \<or> ?Q \<and> ?R")
        by (rule small_stepsl_while)
      thus ?thesis
      proof (rule disjE, erule_tac [2] conjE)
        assume ?P
        with R show ?thesis
          by auto
      next
        assume ?Q and ?R
        have
         "(c\<^sub>2, s\<^sub>2) = (IF b THEN c;; WHILE b DO c ELSE SKIP, s) \<and>
            flow (tl cfs\<^sub>2) = [] \<or>
          bval b s \<and> (c;; WHILE b DO c, s) \<rightarrow>*{tl2 cfs\<^sub>2} (c\<^sub>2, s\<^sub>2) \<and>
            flow (tl cfs\<^sub>2) = \<langle>bvars b\<rangle> # flow (tl2 cfs\<^sub>2) \<or>
          \<not> bval b s \<and> (SKIP, s) \<rightarrow>*{tl2 cfs\<^sub>2} (c\<^sub>2, s\<^sub>2) \<and>
            flow (tl cfs\<^sub>2) = \<langle>bvars b\<rangle> # flow (tl2 cfs\<^sub>2)"
          using `?Q` by (rule small_stepsl_if)
        thus ?thesis
        proof (erule_tac disjE, erule_tac [2] disjE, (erule_tac [2-3] conjE)+)
          assume "(c\<^sub>2, s\<^sub>2) = (IF b THEN c;; WHILE b DO c ELSE SKIP, s) \<and>
            flow (tl cfs\<^sub>2) = []"
          with R and `?R` show ?thesis
            by auto
        next
          assume S: "bval b s"
          with D and O and P have T: "s \<in> Univ B\<^sub>1 (\<subseteq> state \<inter> X)"
            by (drule_tac btyping2_approx [where s = s], auto)
          assume U: "(c;; WHILE b DO c, s) \<rightarrow>*{tl2 cfs\<^sub>2} (c\<^sub>2, s\<^sub>2)"
          hence
           "(\<exists>c' cfs. c\<^sub>2 = c';; WHILE b DO c \<and>
              (c, s) \<rightarrow>*{cfs} (c', s\<^sub>2) \<and>
              flow (tl2 cfs\<^sub>2) = flow cfs) \<or>
            (\<exists>s' cfs cfs'. length cfs' < length (tl2 cfs\<^sub>2) \<and>
              (c, s) \<rightarrow>*{cfs} (SKIP, s') \<and>
              (WHILE b DO c, s') \<rightarrow>*{cfs'} (c\<^sub>2, s\<^sub>2) \<and>
              flow (tl2 cfs\<^sub>2) = flow cfs @ flow cfs')"
            by (rule small_stepsl_seq)
          moreover assume "flow (tl cfs\<^sub>2) = \<langle>bvars b\<rangle> # flow (tl2 cfs\<^sub>2)"
          moreover have "s\<^sub>2 = run_flow (flow (tl2 cfs\<^sub>2)) s"
            using U by (rule small_stepsl_run_flow)
          moreover {
            fix c' cfs
            assume "(c, s) \<rightarrow>*{cfs} (c', run_flow (flow cfs) s)"
            then obtain c\<^sub>2' and t\<^sub>2 where V: "\<forall>x.
              (s = t\<^sub>1 (\<subseteq> sources_aux (flow cfs) s x) \<longrightarrow>
                (c, t\<^sub>1) \<rightarrow>* (c\<^sub>2', t\<^sub>2) \<and> (c' = SKIP) = (c\<^sub>2' = SKIP)) \<and>
              (s = t\<^sub>1 (\<subseteq> sources (flow cfs) s x) \<longrightarrow>
                run_flow (flow cfs) s x = t\<^sub>2 x)"
              using A [of B\<^sub>1 C B\<^sub>1' D s "[]" c s cfs c'
               "run_flow (flow cfs) s"] and N and T by force
            {
              fix x
              assume W: "s = t\<^sub>1 (\<subseteq> sources_aux (\<langle>bvars b\<rangle> # flow cfs) s x)"
              moreover have "sources_aux (flow cfs) s x \<subseteq>
                sources_aux (\<langle>bvars b\<rangle> # (flow cfs)) s x"
                by (rule sources_aux_observe_tl)
              ultimately have "(c, t\<^sub>1) \<rightarrow>* (c\<^sub>2', t\<^sub>2)"
                using V by blast
              hence "(c;; WHILE b DO c, t\<^sub>1) \<rightarrow>* (c\<^sub>2';; WHILE b DO c, t\<^sub>2)"
                by (rule star_seq2)
              moreover have "s = t\<^sub>1 (\<subseteq> bvars b)"
                using Q and W by (blast dest: sources_aux_observe_hd)
              hence "bval b t\<^sub>1"
                using S by (blast dest: bvars_bval)
              hence "(WHILE b DO c, t\<^sub>1) \<rightarrow>* (c;; WHILE b DO c, t\<^sub>1)"
                by (blast intro: star_trans)
              ultimately have "(WHILE b DO c, t\<^sub>1) \<rightarrow>*
               (c\<^sub>2';; WHILE b DO c, t\<^sub>2) \<and> c\<^sub>2';; WHILE b DO c \<noteq> SKIP"
                by (blast intro: star_trans)
            }
            moreover {
              fix x
              assume "s = t\<^sub>1 (\<subseteq> sources (\<langle>bvars b\<rangle> # flow cfs) s x)"
              moreover have "sources (flow cfs) s x \<subseteq>
                sources (\<langle>bvars b\<rangle> # (flow cfs)) s x"
                by (rule sources_observe_tl)
              ultimately have "run_flow (flow cfs) s x = t\<^sub>2 x"
                using V by blast
            }
            ultimately have "\<exists>c\<^sub>2' t\<^sub>2. \<forall>x.
              (s = t\<^sub>1 (\<subseteq> sources_aux (\<langle>bvars b\<rangle> # flow cfs) s x) \<longrightarrow>
                (WHILE b DO c, t\<^sub>1) \<rightarrow>* (c\<^sub>2', t\<^sub>2) \<and> c\<^sub>2' \<noteq> SKIP) \<and>
              (s = t\<^sub>1 (\<subseteq> sources (\<langle>bvars b\<rangle> # flow cfs) s x) \<longrightarrow>
                run_flow (flow cfs) s x = t\<^sub>2 x)"
              by blast
          }
          moreover {
            fix s' cfs cfs'
            assume
              V: "length cfs' < length cfs\<^sub>2 - Suc (Suc 0)" and
              W: "(c, s) \<rightarrow>*{cfs} (SKIP, s')" and
              X: "(WHILE b DO c, s') \<rightarrow>*{cfs'}
                (c\<^sub>2, run_flow (flow cfs') (run_flow (flow cfs) s))"
            then obtain c\<^sub>2' and t\<^sub>2 where "\<forall>x.
              (s = t\<^sub>1 (\<subseteq> sources_aux (flow cfs) s x) \<longrightarrow>
                (c, t\<^sub>1) \<rightarrow>* (c\<^sub>2', t\<^sub>2) \<and> (SKIP = SKIP) = (c\<^sub>2' = SKIP)) \<and>
              (s = t\<^sub>1 (\<subseteq> sources (flow cfs) s x) \<longrightarrow> s' x = t\<^sub>2 x)"
              using A [of B\<^sub>1 C B\<^sub>1' D s "[]" c s cfs SKIP s']
               and N and T by force
            moreover have Y: "s' = run_flow (flow cfs) s"
              using W by (rule small_stepsl_run_flow)
            ultimately have Z: "\<forall>x.
              (s = t\<^sub>1 (\<subseteq> sources_aux (flow cfs) s x) \<longrightarrow>
                (c, t\<^sub>1) \<rightarrow>* (SKIP, t\<^sub>2)) \<and>
              (s = t\<^sub>1 (\<subseteq> sources (flow cfs) s x) \<longrightarrow>
                run_flow (flow cfs) s x = t\<^sub>2 x)"
              by blast
            assume "s\<^sub>2 = run_flow (flow cfs') (run_flow (flow cfs) s)"
            moreover have "(c, s) \<Rightarrow> s'"
              using W by (auto dest: small_stepsl_steps simp: big_iff_small)
            hence "s' \<in> Univ C (\<subseteq> state \<inter> Y)"
              using M and S by blast
            ultimately obtain c\<^sub>3' and t\<^sub>3 where AA: "\<forall>x.
              (run_flow (flow cfs) s = t\<^sub>2
                (\<subseteq> sources_aux (flow cfs') (run_flow (flow cfs) s) x) \<longrightarrow>
                  (WHILE b DO c, t\<^sub>2) \<rightarrow>* (c\<^sub>3', t\<^sub>3) \<and>
                  (c\<^sub>2 = SKIP) = (c\<^sub>3' = SKIP)) \<and>
              (run_flow (flow cfs) s = t\<^sub>2
                (\<subseteq> sources (flow cfs') (run_flow (flow cfs) s) x) \<longrightarrow>
                  run_flow (flow cfs') (run_flow (flow cfs) s) x = t\<^sub>3 x)"
              using K [of cfs' "[]" cfs' s' "WHILE b DO c" s']
               and V and X and Y by force
            {
              fix x
              assume AB: "s = t\<^sub>1
                (\<subseteq> sources_aux (\<langle>bvars b\<rangle> # flow cfs @ flow cfs') s x)"
              moreover have "sources_aux (flow cfs) s x \<subseteq>
                sources_aux (flow cfs @ flow cfs') s x"
                by (rule sources_aux_append)
              moreover have AC: "sources_aux (flow cfs @ flow cfs') s x \<subseteq>
                sources_aux (\<langle>bvars b\<rangle> # flow cfs @ flow cfs') s x"
                by (rule sources_aux_observe_tl)
              ultimately have "(c, t\<^sub>1) \<rightarrow>* (SKIP, t\<^sub>2)"
                using Z by blast
              hence "(c;; WHILE b DO c, t\<^sub>1) \<rightarrow>* (SKIP;; WHILE b DO c, t\<^sub>2)"
                by (rule star_seq2)
              moreover have "s = t\<^sub>1 (\<subseteq> bvars b)"
                using Q and AB by (blast dest: sources_aux_observe_hd)
              hence "bval b t\<^sub>1"
                using S by (blast dest: bvars_bval)
              hence "(WHILE b DO c, t\<^sub>1) \<rightarrow>* (c;; WHILE b DO c, t\<^sub>1)"
                by (blast intro: star_trans)
              ultimately have "(WHILE b DO c, t\<^sub>1) \<rightarrow>* (WHILE b DO c, t\<^sub>2)"
                by (blast intro: star_trans)
              moreover have "run_flow (flow cfs) s = t\<^sub>2
                (\<subseteq> sources_aux (flow cfs') (run_flow (flow cfs) s) x)"
              proof
                fix y
                assume "y \<in> sources_aux (flow cfs')
                  (run_flow (flow cfs) s) x"
                hence "sources (flow cfs) s y \<subseteq>
                  sources_aux (flow cfs @ flow cfs') s x"
                  by (rule sources_aux_member)
                hence "sources (flow cfs) s y \<subseteq>
                  sources_aux (\<langle>bvars b\<rangle> # flow cfs @ flow cfs') s x"
                  using AC by simp
                thus "run_flow (flow cfs) s y = t\<^sub>2 y"
                  using Z and AB by blast
              qed
              hence "(WHILE b DO c, t\<^sub>2) \<rightarrow>* (c\<^sub>3', t\<^sub>3) \<and>
                (c\<^sub>2 = SKIP) = (c\<^sub>3' = SKIP)"
                using AA by simp
              ultimately have "(WHILE b DO c, t\<^sub>1) \<rightarrow>* (c\<^sub>3', t\<^sub>3) \<and>
                (c\<^sub>2 = SKIP) = (c\<^sub>3' = SKIP)"
                by (blast intro: star_trans)
            }
            moreover {
              fix x
              assume AB: "s = t\<^sub>1
                (\<subseteq> sources (\<langle>bvars b\<rangle> # flow cfs @ flow cfs') s x)"
              have "run_flow (flow cfs) s = t\<^sub>2
                (\<subseteq> sources (flow cfs') (run_flow (flow cfs) s) x)"
              proof
                fix y
                assume "y \<in> sources (flow cfs')
                  (run_flow (flow cfs) s) x"
                hence "sources (flow cfs) s y \<subseteq>
                  sources (flow cfs @ flow cfs') s x"
                  by (rule sources_member)
                moreover have "sources (flow cfs @ flow cfs') s x \<subseteq>
                  sources (\<langle>bvars b\<rangle> # flow cfs @ flow cfs') s x"
                  by (rule sources_observe_tl)
                ultimately have "sources (flow cfs) s y \<subseteq>
                  sources (\<langle>bvars b\<rangle> # flow cfs @ flow cfs') s x"
                  by simp
                thus "run_flow (flow cfs) s y = t\<^sub>2 y"
                  using Z and AB by blast
              qed
              hence "run_flow (flow cfs') (run_flow (flow cfs) s) x = t\<^sub>3 x"
                using AA by simp
            }
            ultimately have "\<exists>c\<^sub>3' t\<^sub>3. \<forall>x.
              (s = t\<^sub>1
                (\<subseteq> sources_aux (\<langle>bvars b\<rangle> # flow cfs @ flow cfs') s x) \<longrightarrow>
                  (WHILE b DO c, t\<^sub>1) \<rightarrow>* (c\<^sub>3', t\<^sub>3) \<and>
                  (c\<^sub>2 = SKIP) = (c\<^sub>3' = SKIP)) \<and>
              (s = t\<^sub>1
                (\<subseteq> sources (\<langle>bvars b\<rangle> # flow cfs @ flow cfs') s x) \<longrightarrow>
                  run_flow (flow cfs') (run_flow (flow cfs) s) x = t\<^sub>3 x)"
              by auto
          }
          ultimately show ?thesis
            using R and `?R` by (auto simp: run_flow_append)
        next
          assume
            S: "\<not> bval b s" and
            T: "flow (tl cfs\<^sub>2) = \<langle>bvars b\<rangle> # flow (tl2 cfs\<^sub>2)"
          moreover assume "(SKIP, s) \<rightarrow>*{tl2 cfs\<^sub>2} (c\<^sub>2, s\<^sub>2)"
          hence U: "(c\<^sub>2, s\<^sub>2) = (SKIP, s) \<and> flow (tl2 cfs\<^sub>2) = []"
            by (rule small_stepsl_skip)
          show ?thesis
          proof (rule exI [of _ SKIP], rule exI [of _ t\<^sub>1])
            {
              fix x
              have "(WHILE b DO c, t\<^sub>1) \<rightarrow>
                (IF b THEN c;; WHILE b DO c ELSE SKIP, t\<^sub>1)" ..
              moreover assume "s = t\<^sub>1 (\<subseteq> sources_aux [\<langle>bvars b\<rangle>] s x)"
              hence "s = t\<^sub>1 (\<subseteq> bvars b)"
                using Q by (blast dest: sources_aux_observe_hd)
              hence "\<not> bval b t\<^sub>1"
                using S by (blast dest: bvars_bval)
              hence "(IF b THEN c;; WHILE b DO c ELSE SKIP, t\<^sub>1) \<rightarrow>
                (SKIP, t\<^sub>1)" ..
              ultimately have "(WHILE b DO c, t\<^sub>1) \<rightarrow>* (SKIP, t\<^sub>1)"
                by (blast intro: star_trans)
            }
            moreover {
              fix x
              assume "s = t\<^sub>1 (\<subseteq> sources [\<langle>bvars b\<rangle>] s x)"
              hence "s x = t\<^sub>1 x"
                by (subst (asm) append_Nil [symmetric],
                 simp only: sources.simps, auto)
            }
            ultimately show "\<forall>x.
              (s\<^sub>1 = t\<^sub>1 (\<subseteq> sources_aux (flow cfs\<^sub>2) s\<^sub>1 x) \<longrightarrow>
                (c\<^sub>1, t\<^sub>1) \<rightarrow>* (SKIP, t\<^sub>1) \<and> (c\<^sub>2 = SKIP) = (SKIP = SKIP)) \<and>
              (s\<^sub>1 = t\<^sub>1 (\<subseteq> sources (flow cfs\<^sub>2) s\<^sub>1 x) \<longrightarrow> s\<^sub>2 x = t\<^sub>1 x)"
              using R and T and U and `?R` by auto
          qed
        qed
      qed
    next
      assume "(IF b THEN c;; WHILE b DO c ELSE SKIP, s) \<rightarrow>*{tl cfs\<^sub>1} (c\<^sub>1, s\<^sub>1)"
      hence
       "(c\<^sub>1, s\<^sub>1) = (IF b THEN c;; WHILE b DO c ELSE SKIP, s) \<and>
          flow (tl cfs\<^sub>1) = [] \<or>
        bval b s \<and> (c;; WHILE b DO c, s) \<rightarrow>*{tl2 cfs\<^sub>1} (c\<^sub>1, s\<^sub>1) \<and>
          flow (tl cfs\<^sub>1) = \<langle>bvars b\<rangle> # flow (tl2 cfs\<^sub>1) \<or>
        \<not> bval b s \<and> (SKIP, s) \<rightarrow>*{tl2 cfs\<^sub>1} (c\<^sub>1, s\<^sub>1) \<and>
          flow (tl cfs\<^sub>1) = \<langle>bvars b\<rangle> # flow (tl2 cfs\<^sub>1)"
        by (rule small_stepsl_if)
      thus ?thesis
      proof (rule disjE, erule_tac [2] disjE, erule_tac conjE,
       (erule_tac [2-3] conjE)+)
        assume R: "(c\<^sub>1, s\<^sub>1) = (IF b THEN c;; WHILE b DO c ELSE SKIP, s)"
        hence "(IF b THEN c;; WHILE b DO c ELSE SKIP, s) \<rightarrow>*{cfs\<^sub>2} (c\<^sub>2, s\<^sub>2)"
          using J by simp
        hence
         "(c\<^sub>2, s\<^sub>2) = (IF b THEN c;; WHILE b DO c ELSE SKIP, s) \<and>
            flow cfs\<^sub>2 = [] \<or>
          bval b s \<and> (c;; WHILE b DO c, s) \<rightarrow>*{tl cfs\<^sub>2} (c\<^sub>2, s\<^sub>2) \<and>
            flow cfs\<^sub>2 = \<langle>bvars b\<rangle> # flow (tl cfs\<^sub>2) \<or>
          \<not> bval b s \<and> (SKIP, s) \<rightarrow>*{tl cfs\<^sub>2} (c\<^sub>2, s\<^sub>2) \<and>
            flow cfs\<^sub>2 = \<langle>bvars b\<rangle> # flow (tl cfs\<^sub>2)"
          by (rule small_stepsl_if)
        thus ?thesis
        proof (erule_tac disjE, erule_tac [2] disjE, (erule_tac [2-3] conjE)+)
          assume "(c\<^sub>2, s\<^sub>2) = (IF b THEN c;; WHILE b DO c ELSE SKIP, s) \<and>
            flow cfs\<^sub>2 = []"
          with R show ?thesis
            by auto
        next
          assume S: "bval b s"
          with D and O and P have T: "s \<in> Univ B\<^sub>1 (\<subseteq> state \<inter> X)"
            by (drule_tac btyping2_approx [where s = s], auto)
          assume U: "(c;; WHILE b DO c, s) \<rightarrow>*{tl cfs\<^sub>2} (c\<^sub>2, s\<^sub>2)"
          hence
           "(\<exists>c' cfs. c\<^sub>2 = c';; WHILE b DO c \<and>
              (c, s) \<rightarrow>*{cfs} (c', s\<^sub>2) \<and>
              flow (tl cfs\<^sub>2) = flow cfs) \<or>
            (\<exists>s' cfs cfs'. length cfs' < length (tl cfs\<^sub>2) \<and>
              (c, s) \<rightarrow>*{cfs} (SKIP, s') \<and>
              (WHILE b DO c, s') \<rightarrow>*{cfs'} (c\<^sub>2, s\<^sub>2) \<and>
              flow (tl cfs\<^sub>2) = flow cfs @ flow cfs')"
            by (rule small_stepsl_seq)
          moreover assume "flow cfs\<^sub>2 = \<langle>bvars b\<rangle> # flow (tl cfs\<^sub>2)"
          moreover have "s\<^sub>2 = run_flow (flow (tl cfs\<^sub>2)) s"
            using U by (rule small_stepsl_run_flow)
          moreover {
            fix c' cfs
            assume "(c, s) \<rightarrow>*{cfs} (c', run_flow (flow cfs) s)"
            then obtain c\<^sub>2' and t\<^sub>2 where V: "\<forall>x.
              (s = t\<^sub>1 (\<subseteq> sources_aux (flow cfs) s x) \<longrightarrow>
                (c, t\<^sub>1) \<rightarrow>* (c\<^sub>2', t\<^sub>2) \<and> (c' = SKIP) = (c\<^sub>2' = SKIP)) \<and>
              (s = t\<^sub>1 (\<subseteq> sources (flow cfs) s x) \<longrightarrow>
                run_flow (flow cfs) s x = t\<^sub>2 x)"
              using A [of B\<^sub>1 C B\<^sub>1' D s "[]" c s cfs c'
               "run_flow (flow cfs) s"] and N and T by force
            {
              fix x
              assume W: "s = t\<^sub>1 (\<subseteq> sources_aux (\<langle>bvars b\<rangle> # flow cfs) s x)"
              moreover have "sources_aux (flow cfs) s x \<subseteq>
                sources_aux (\<langle>bvars b\<rangle> # (flow cfs)) s x"
                by (rule sources_aux_observe_tl)
              ultimately have "(c, t\<^sub>1) \<rightarrow>* (c\<^sub>2', t\<^sub>2)"
                using V by blast
              hence "(c;; WHILE b DO c, t\<^sub>1) \<rightarrow>* (c\<^sub>2';; WHILE b DO c, t\<^sub>2)"
                by (rule star_seq2)
              moreover have "s = t\<^sub>1 (\<subseteq> bvars b)"
                using Q and W by (blast dest: sources_aux_observe_hd)
              hence "bval b t\<^sub>1"
                using S by (blast dest: bvars_bval)
              hence "(IF b THEN c;; WHILE b DO c ELSE SKIP, t\<^sub>1) \<rightarrow>
                (c;; WHILE b DO c, t\<^sub>1)" ..
              ultimately have
               "(IF b THEN c;; WHILE b DO c ELSE SKIP, t\<^sub>1) \<rightarrow>*
                  (c\<^sub>2';; WHILE b DO c, t\<^sub>2) \<and> c\<^sub>2';; WHILE b DO c \<noteq> SKIP"
                by (blast intro: star_trans)
            }
            moreover {
              fix x
              assume "s = t\<^sub>1 (\<subseteq> sources (\<langle>bvars b\<rangle> # flow cfs) s x)"
              moreover have "sources (flow cfs) s x \<subseteq>
                sources (\<langle>bvars b\<rangle> # (flow cfs)) s x"
                by (rule sources_observe_tl)
              ultimately have "run_flow (flow cfs) s x = t\<^sub>2 x"
                using V by blast
            }
            ultimately have "\<exists>c\<^sub>2' t\<^sub>2. \<forall>x.
              (s = t\<^sub>1 (\<subseteq> sources_aux (\<langle>bvars b\<rangle> # flow cfs) s x) \<longrightarrow>
                (IF b THEN c;; WHILE b DO c ELSE SKIP, t\<^sub>1) \<rightarrow>* (c\<^sub>2', t\<^sub>2) \<and>
                  c\<^sub>2' \<noteq> SKIP) \<and>
              (s = t\<^sub>1 (\<subseteq> sources (\<langle>bvars b\<rangle> # flow cfs) s x) \<longrightarrow>
                run_flow (flow cfs) s x = t\<^sub>2 x)"
              by blast
          }
          moreover {
            fix s' cfs cfs'
            assume
              V: "length cfs' < length cfs\<^sub>2 - Suc 0" and
              W: "(c, s) \<rightarrow>*{cfs} (SKIP, s')" and
              X: "(WHILE b DO c, s') \<rightarrow>*{cfs'}
                (c\<^sub>2, run_flow (flow cfs') (run_flow (flow cfs) s))"
            then obtain c\<^sub>2' and t\<^sub>2 where "\<forall>x.
              (s = t\<^sub>1 (\<subseteq> sources_aux (flow cfs) s x) \<longrightarrow>
                (c, t\<^sub>1) \<rightarrow>* (c\<^sub>2', t\<^sub>2) \<and> (SKIP = SKIP) = (c\<^sub>2' = SKIP)) \<and>
              (s = t\<^sub>1 (\<subseteq> sources (flow cfs) s x) \<longrightarrow> s' x = t\<^sub>2 x)"
              using A [of B\<^sub>1 C B\<^sub>1' D s "[]" c s cfs SKIP s']
               and N and T by force
            moreover have Y: "s' = run_flow (flow cfs) s"
              using W by (rule small_stepsl_run_flow)
            ultimately have Z: "\<forall>x.
              (s = t\<^sub>1 (\<subseteq> sources_aux (flow cfs) s x) \<longrightarrow>
                (c, t\<^sub>1) \<rightarrow>* (SKIP, t\<^sub>2)) \<and>
              (s = t\<^sub>1 (\<subseteq> sources (flow cfs) s x) \<longrightarrow>
                run_flow (flow cfs) s x = t\<^sub>2 x)"
              by blast
            assume "s\<^sub>2 = run_flow (flow cfs') (run_flow (flow cfs) s)"
            moreover have "(c, s) \<Rightarrow> s'"
              using W by (auto dest: small_stepsl_steps simp: big_iff_small)
            hence "s' \<in> Univ C (\<subseteq> state \<inter> Y)"
              using M and S by blast
            ultimately obtain c\<^sub>3' and t\<^sub>3 where AA: "\<forall>x.
              (run_flow (flow cfs) s = t\<^sub>2
                (\<subseteq> sources_aux (flow cfs') (run_flow (flow cfs) s) x) \<longrightarrow>
                  (WHILE b DO c, t\<^sub>2) \<rightarrow>* (c\<^sub>3', t\<^sub>3) \<and>
                  (c\<^sub>2 = SKIP) = (c\<^sub>3' = SKIP)) \<and>
              (run_flow (flow cfs) s = t\<^sub>2
                (\<subseteq> sources (flow cfs') (run_flow (flow cfs) s) x) \<longrightarrow>
                  run_flow (flow cfs') (run_flow (flow cfs) s) x = t\<^sub>3 x)"
              using K [of cfs' "[]" cfs' s' "WHILE b DO c" s']
               and V and X and Y by force
            {
              fix x
              assume AB: "s = t\<^sub>1
                (\<subseteq> sources_aux (\<langle>bvars b\<rangle> # flow cfs @ flow cfs') s x)"
              moreover have "sources_aux (flow cfs) s x \<subseteq>
                sources_aux (flow cfs @ flow cfs') s x"
                by (rule sources_aux_append)
              moreover have AC: "sources_aux (flow cfs @ flow cfs') s x \<subseteq>
                sources_aux (\<langle>bvars b\<rangle> # flow cfs @ flow cfs') s x"
                by (rule sources_aux_observe_tl)
              ultimately have "(c, t\<^sub>1) \<rightarrow>* (SKIP, t\<^sub>2)"
                using Z by blast
              hence "(c;; WHILE b DO c, t\<^sub>1) \<rightarrow>* (SKIP;; WHILE b DO c, t\<^sub>2)"
                by (rule star_seq2)
              moreover have "s = t\<^sub>1 (\<subseteq> bvars b)"
                using Q and AB by (blast dest: sources_aux_observe_hd)
              hence "bval b t\<^sub>1"
                using S by (blast dest: bvars_bval)
              hence "(IF b THEN c;; WHILE b DO c ELSE SKIP, t\<^sub>1) \<rightarrow>
                (c;; WHILE b DO c, t\<^sub>1)" ..
              ultimately have "(IF b THEN c;; WHILE b DO c ELSE SKIP, t\<^sub>1) \<rightarrow>*
                (WHILE b DO c, t\<^sub>2)"
                by (blast intro: star_trans)
              moreover have "run_flow (flow cfs) s = t\<^sub>2
                (\<subseteq> sources_aux (flow cfs') (run_flow (flow cfs) s) x)"
              proof
                fix y
                assume "y \<in> sources_aux (flow cfs')
                  (run_flow (flow cfs) s) x"
                hence "sources (flow cfs) s y \<subseteq>
                  sources_aux (flow cfs @ flow cfs') s x"
                  by (rule sources_aux_member)
                hence "sources (flow cfs) s y \<subseteq>
                  sources_aux (\<langle>bvars b\<rangle> # flow cfs @ flow cfs') s x"
                  using AC by simp
                thus "run_flow (flow cfs) s y = t\<^sub>2 y"
                  using Z and AB by blast
              qed
              hence "(WHILE b DO c, t\<^sub>2) \<rightarrow>* (c\<^sub>3', t\<^sub>3) \<and>
                (c\<^sub>2 = SKIP) = (c\<^sub>3' = SKIP)"
                using AA by simp
              ultimately have
               "(IF b THEN c;; WHILE b DO c ELSE SKIP, t\<^sub>1) \<rightarrow>*
                  (c\<^sub>3', t\<^sub>3) \<and> (c\<^sub>2 = SKIP) = (c\<^sub>3' = SKIP)"
                by (blast intro: star_trans)
            }
            moreover {
              fix x
              assume AB: "s = t\<^sub>1
                (\<subseteq> sources (\<langle>bvars b\<rangle> # flow cfs @ flow cfs') s x)"
              have "run_flow (flow cfs) s = t\<^sub>2
                (\<subseteq> sources (flow cfs') (run_flow (flow cfs) s) x)"
              proof
                fix y
                assume "y \<in> sources (flow cfs')
                  (run_flow (flow cfs) s) x"
                hence "sources (flow cfs) s y \<subseteq>
                  sources (flow cfs @ flow cfs') s x"
                  by (rule sources_member)
                moreover have "sources (flow cfs @ flow cfs') s x \<subseteq>
                  sources (\<langle>bvars b\<rangle> # flow cfs @ flow cfs') s x"
                  by (rule sources_observe_tl)
                ultimately have "sources (flow cfs) s y \<subseteq>
                  sources (\<langle>bvars b\<rangle> # flow cfs @ flow cfs') s x"
                  by simp
                thus "run_flow (flow cfs) s y = t\<^sub>2 y"
                  using Z and AB by blast
              qed
              hence "run_flow (flow cfs') (run_flow (flow cfs) s) x = t\<^sub>3 x"
                using AA by simp
            }
            ultimately have "\<exists>c\<^sub>3' t\<^sub>3. \<forall>x.
              (s = t\<^sub>1
                (\<subseteq> sources_aux (\<langle>bvars b\<rangle> # flow cfs @ flow cfs') s x) \<longrightarrow>
                  (IF b THEN c;; WHILE b DO c ELSE SKIP, t\<^sub>1) \<rightarrow>* (c\<^sub>3', t\<^sub>3) \<and>
                  (c\<^sub>2 = SKIP) = (c\<^sub>3' = SKIP)) \<and>
              (s = t\<^sub>1
                (\<subseteq> sources (\<langle>bvars b\<rangle> # flow cfs @ flow cfs') s x) \<longrightarrow>
                  run_flow (flow cfs') (run_flow (flow cfs) s) x = t\<^sub>3 x)"
              by auto
          }
          ultimately show ?thesis
            using R by (auto simp: run_flow_append)
        next
          assume
            S: "\<not> bval b s" and
            T: "flow cfs\<^sub>2 = \<langle>bvars b\<rangle> # flow (tl cfs\<^sub>2)"
          assume "(SKIP, s) \<rightarrow>*{tl cfs\<^sub>2} (c\<^sub>2, s\<^sub>2)"
          hence U: "(c\<^sub>2, s\<^sub>2) = (SKIP, s) \<and> flow (tl cfs\<^sub>2) = []"
            by (rule small_stepsl_skip)
          show ?thesis
          proof (rule exI [of _ SKIP], rule exI [of _ t\<^sub>1])
            {
              fix x
              assume "s = t\<^sub>1 (\<subseteq> sources_aux [\<langle>bvars b\<rangle>] s x)"
              hence "s = t\<^sub>1 (\<subseteq> bvars b)"
                using Q by (blast dest: sources_aux_observe_hd)
              hence "\<not> bval b t\<^sub>1"
                using S by (blast dest: bvars_bval)
              hence "(IF b THEN c;; WHILE b DO c ELSE SKIP, t\<^sub>1) \<rightarrow>
                (SKIP, t\<^sub>1)" ..
            }
            moreover {
              fix x
              assume "s = t\<^sub>1 (\<subseteq> sources [\<langle>bvars b\<rangle>] s x)"
              hence "s x = t\<^sub>1 x"
                by (subst (asm) append_Nil [symmetric],
                 simp only: sources.simps, auto)
            }
            ultimately show "\<forall>x.
              (s\<^sub>1 = t\<^sub>1 (\<subseteq> sources_aux (flow cfs\<^sub>2) s\<^sub>1 x) \<longrightarrow>
                (c\<^sub>1, t\<^sub>1) \<rightarrow>* (SKIP, t\<^sub>1) \<and> (c\<^sub>2 = SKIP) = (SKIP = SKIP)) \<and>
              (s\<^sub>1 = t\<^sub>1 (\<subseteq> sources (flow cfs\<^sub>2) s\<^sub>1 x) \<longrightarrow> s\<^sub>2 x = t\<^sub>1 x)"
              using R and T and U by auto
          qed
        qed
      next
        assume R: "bval b s"
        with D and O and P have S: "s \<in> Univ B\<^sub>1 (\<subseteq> state \<inter> X)"
          by (drule_tac btyping2_approx [where s = s], auto)
        assume "(c;; WHILE b DO c, s) \<rightarrow>*{tl2 cfs\<^sub>1} (c\<^sub>1, s\<^sub>1)"
        hence
         "(\<exists>c' cfs'. c\<^sub>1 = c';; WHILE b DO c \<and>
            (c, s) \<rightarrow>*{cfs'} (c', s\<^sub>1) \<and>
            flow (tl2 cfs\<^sub>1) = flow cfs') \<or>
          (\<exists>s' cfs' cfs''. length cfs'' < length (tl2 cfs\<^sub>1) \<and>
            (c, s) \<rightarrow>*{cfs'} (SKIP, s') \<and>
            (WHILE b DO c, s') \<rightarrow>*{cfs''} (c\<^sub>1, s\<^sub>1) \<and>
            flow (tl2 cfs\<^sub>1) = flow cfs' @ flow cfs'')"
          by (rule small_stepsl_seq)
        moreover {
          fix c' cfs
          assume
            T: "(c, s) \<rightarrow>*{cfs} (c', s\<^sub>1)" and
            U: "c\<^sub>1 = c';; WHILE b DO c"
          hence V: "(c';; WHILE b DO c, s\<^sub>1) \<rightarrow>*{cfs\<^sub>2} (c\<^sub>2, s\<^sub>2)"
            using J by simp
          hence W: "s\<^sub>2 = run_flow (flow cfs\<^sub>2) s\<^sub>1"
            by (rule small_stepsl_run_flow)
          have
           "(\<exists>c'' cfs'. c\<^sub>2 = c'';; WHILE b DO c \<and>
              (c', s\<^sub>1) \<rightarrow>*{cfs'} (c'', s\<^sub>2) \<and>
              flow cfs\<^sub>2 = flow cfs') \<or>
            (\<exists>s' cfs' cfs''. length cfs'' < length cfs\<^sub>2 \<and>
              (c', s\<^sub>1) \<rightarrow>*{cfs'} (SKIP, s') \<and>
              (WHILE b DO c, s') \<rightarrow>*{cfs''} (c\<^sub>2, s\<^sub>2) \<and>
              flow cfs\<^sub>2 = flow cfs' @ flow cfs'')"
            using V by (rule small_stepsl_seq)
          moreover {
            fix c'' cfs'
            assume "(c', s\<^sub>1) \<rightarrow>*{cfs'} (c'', s\<^sub>2)"
            then obtain c\<^sub>2' and t\<^sub>2 where X: "\<forall>x.
              (s\<^sub>1 = t\<^sub>1 (\<subseteq> sources_aux (flow cfs') s\<^sub>1 x) \<longrightarrow>
                (c', t\<^sub>1) \<rightarrow>* (c\<^sub>2', t\<^sub>2) \<and> (c'' = SKIP) = (c\<^sub>2' = SKIP)) \<and>
              (s\<^sub>1 = t\<^sub>1 (\<subseteq> sources (flow cfs') s\<^sub>1 x) \<longrightarrow>
                run_flow (flow cfs\<^sub>2) s\<^sub>1 x = t\<^sub>2 x)"
              using A [of B\<^sub>1 C B\<^sub>1' D s cfs c' s\<^sub>1 cfs' c''
               "run_flow (flow cfs\<^sub>2) s\<^sub>1"] and N and S and T and W by force
            assume
              Y: "c\<^sub>2 = c'';; WHILE b DO c" and
              Z: "flow cfs\<^sub>2 = flow cfs'"
            have ?thesis
            proof (rule exI [of _ "c\<^sub>2';; WHILE b DO c"], rule exI [of _ t\<^sub>2])
              from U and W and X and Y and Z show "\<forall>x.
                (s\<^sub>1 = t\<^sub>1 (\<subseteq> sources_aux (flow cfs\<^sub>2) s\<^sub>1 x) \<longrightarrow>
                  (c\<^sub>1, t\<^sub>1) \<rightarrow>* (c\<^sub>2';; WHILE b DO c, t\<^sub>2) \<and>
                    (c\<^sub>2 = SKIP) = (c\<^sub>2';; WHILE b DO c = SKIP)) \<and>
                (s\<^sub>1 = t\<^sub>1 (\<subseteq> sources (flow cfs\<^sub>2) s\<^sub>1 x) \<longrightarrow> s\<^sub>2 x = t\<^sub>2 x)"
                by (auto intro: star_seq2)
            qed
          }
          moreover {
            fix s' cfs' cfs''
            assume
              X: "length cfs'' < length cfs\<^sub>2" and
              Y: "(c', s\<^sub>1) \<rightarrow>*{cfs'} (SKIP, s')" and
              Z: "(WHILE b DO c, s') \<rightarrow>*{cfs''} (c\<^sub>2, s\<^sub>2)"
            then obtain c\<^sub>2' and t\<^sub>2 where "\<forall>x.
              (s\<^sub>1 = t\<^sub>1 (\<subseteq> sources_aux (flow cfs') s\<^sub>1 x) \<longrightarrow>
                (c', t\<^sub>1) \<rightarrow>* (c\<^sub>2', t\<^sub>2) \<and> (SKIP = SKIP) = (c\<^sub>2' = SKIP)) \<and>
              (s\<^sub>1 = t\<^sub>1 (\<subseteq> sources (flow cfs') s\<^sub>1 x) \<longrightarrow> s' x = t\<^sub>2 x)"
              using A [of B\<^sub>1 C B\<^sub>1' D s cfs c' s\<^sub>1 cfs' SKIP s']
               and N and S and T by force
            moreover have AA: "s' = run_flow (flow cfs') s\<^sub>1"
              using Y by (rule small_stepsl_run_flow)
            ultimately have AB: "\<forall>x.
              (s\<^sub>1 = t\<^sub>1 (\<subseteq> sources_aux (flow cfs') s\<^sub>1 x) \<longrightarrow>
                (c', t\<^sub>1) \<rightarrow>* (SKIP, t\<^sub>2)) \<and>
              (s\<^sub>1 = t\<^sub>1 (\<subseteq> sources (flow cfs') s\<^sub>1 x) \<longrightarrow>
                run_flow (flow cfs') s\<^sub>1 x = t\<^sub>2 x)"
              by blast
            have AC: "s\<^sub>2 = run_flow (flow cfs'') s'"
              using Z by (rule small_stepsl_run_flow)
            moreover have "(c, s) \<rightarrow>*{cfs @ cfs'} (SKIP, s')"
              using T and Y by (simp add: small_stepsl_append)
            hence "(c, s) \<Rightarrow> s'"
              by (auto dest: small_stepsl_steps simp: big_iff_small)
            hence "s' \<in> Univ C (\<subseteq> state \<inter> Y)"
              using M and R by blast
            ultimately obtain c\<^sub>2' and t\<^sub>3 where AD: "\<forall>x.
              (run_flow (flow cfs') s\<^sub>1 = t\<^sub>2
                (\<subseteq> sources_aux (flow cfs'') (run_flow (flow cfs') s\<^sub>1) x) \<longrightarrow>
                  (WHILE b DO c, t\<^sub>2) \<rightarrow>* (c\<^sub>2', t\<^sub>3) \<and>
                  (c\<^sub>2 = SKIP) = (c\<^sub>2' = SKIP)) \<and>
              (run_flow (flow cfs') s\<^sub>1 = t\<^sub>2
                (\<subseteq> sources (flow cfs'') (run_flow (flow cfs') s\<^sub>1) x) \<longrightarrow>
                  run_flow (flow cfs'') (run_flow (flow cfs') s\<^sub>1) x = t\<^sub>3 x)"
              using K [of cfs'' "[]" cfs'' s' "WHILE b DO c" s']
               and X and Z and AA by force
            moreover assume "flow cfs\<^sub>2 = flow cfs' @ flow cfs''"
            moreover {
              fix x
              assume AE: "s\<^sub>1 = t\<^sub>1
                (\<subseteq> sources_aux (flow cfs' @ flow cfs'') s\<^sub>1 x)"
              moreover have "sources_aux (flow cfs') s\<^sub>1 x \<subseteq>
                sources_aux (flow cfs' @ flow cfs'') s\<^sub>1 x"
                by (rule sources_aux_append)
              ultimately have "(c', t\<^sub>1) \<rightarrow>* (SKIP, t\<^sub>2)"
                using AB by blast
              hence "(c';; WHILE b DO c, t\<^sub>1) \<rightarrow>* (SKIP;; WHILE b DO c, t\<^sub>2)"
                by (rule star_seq2)
              hence "(c';; WHILE b DO c, t\<^sub>1) \<rightarrow>* (WHILE b DO c, t\<^sub>2)"
                by (blast intro: star_trans)
              moreover have "run_flow (flow cfs') s\<^sub>1 = t\<^sub>2
                (\<subseteq> sources_aux (flow cfs'') (run_flow (flow cfs') s\<^sub>1) x)"
              proof
                fix y
                assume "y \<in> sources_aux (flow cfs'')
                  (run_flow (flow cfs') s\<^sub>1) x"
                hence "sources (flow cfs') s\<^sub>1 y \<subseteq>
                  sources_aux (flow cfs' @ flow cfs'') s\<^sub>1 x"
                  by (rule sources_aux_member)
                thus "run_flow (flow cfs') s\<^sub>1 y = t\<^sub>2 y"
                  using AB and AE by blast
              qed
              hence "(WHILE b DO c, t\<^sub>2) \<rightarrow>* (c\<^sub>2', t\<^sub>3) \<and>
                (c\<^sub>2 = SKIP) = (c\<^sub>2' = SKIP)"
                using AD by simp
              ultimately have "(c';; WHILE b DO c, t\<^sub>1) \<rightarrow>* (c\<^sub>2', t\<^sub>3) \<and>
                (c\<^sub>2 = SKIP) = (c\<^sub>2' = SKIP)"
                by (blast intro: star_trans)
            }
            moreover {
              fix x
              assume AE: "s\<^sub>1 = t\<^sub>1
                (\<subseteq> sources (flow cfs' @ flow cfs'') s\<^sub>1 x)"
              have "run_flow (flow cfs') s\<^sub>1 = t\<^sub>2
                (\<subseteq> sources (flow cfs'') (run_flow (flow cfs') s\<^sub>1) x)"
              proof
                fix y
                assume "y \<in> sources (flow cfs'')
                  (run_flow (flow cfs') s\<^sub>1) x"
                hence "sources (flow cfs') s\<^sub>1 y \<subseteq>
                  sources (flow cfs' @ flow cfs'') s\<^sub>1 x"
                  by (rule sources_member)
                thus "run_flow (flow cfs') s\<^sub>1 y = t\<^sub>2 y"
                  using AB and AE by blast
              qed
              hence "run_flow (flow cfs'')
                (run_flow (flow cfs') s\<^sub>1) x = t\<^sub>3 x"
                using AD by simp
            }
            ultimately have ?thesis
              by (metis U AA AC)
          }
          ultimately have ?thesis
            by blast
        }
        moreover {
          fix s' cfs cfs'
          assume
           "length cfs' < length (tl2 cfs\<^sub>1)" and
           "(c, s) \<rightarrow>*{cfs} (SKIP, s')" and
           "(WHILE b DO c, s') \<rightarrow>*{cfs'} (c\<^sub>1, s\<^sub>1)"
          moreover from this have "(c, s) \<Rightarrow> s'"
            by (auto dest: small_stepsl_steps simp: big_iff_small)
          hence "s' \<in> Univ C (\<subseteq> state \<inter> Y)"
            using M and R by blast
          ultimately have ?thesis
            using K [of "cfs' @ cfs\<^sub>2" cfs' cfs\<^sub>2 s' c\<^sub>1 s\<^sub>1] and J by force
        }
        ultimately show ?thesis
          by blast
      next
        assume "(SKIP, s) \<rightarrow>*{tl2 cfs\<^sub>1} (c\<^sub>1, s\<^sub>1)"
        hence "(c\<^sub>1, s\<^sub>1) = (SKIP, s)"
          by (blast dest: small_stepsl_skip)
        moreover from this have "(c\<^sub>2, s\<^sub>2) = (SKIP, s) \<and> flow cfs\<^sub>2 = []"
          using J by (blast dest: small_stepsl_skip)
        ultimately show ?thesis
          by auto
      qed
    qed
  }
  moreover {
    fix r t\<^sub>1
    assume O: "r \<in> C" and P: "s = r (\<subseteq> state \<inter> Y)"
    have Q: "\<forall>x. \<forall>y \<in> bvars b. s: dom y \<leadsto> dom x"
    proof (cases "state \<subseteq> Y")
      case True
      with P have "interf s = interf r"
        by (blast intro: interf_state)
      with N and O show ?thesis
        by (erule_tac conjE, drule_tac bspec,
         auto simp: univ_states_if_def)
    next
      case False
      with N and O show ?thesis
        by (erule_tac conjE, drule_tac bspec,
         auto simp: univ_states_if_def)
    qed
    have "(c\<^sub>1, s\<^sub>1) = (WHILE b DO c, s) \<or>
      (IF b THEN c;; WHILE b DO c ELSE SKIP, s) \<rightarrow>*{tl cfs\<^sub>1} (c\<^sub>1, s\<^sub>1)"
      using I by (blast dest: small_stepsl_while)
    hence "\<exists>c\<^sub>2' t\<^sub>2. \<forall>x.
      (s\<^sub>1 = t\<^sub>1 (\<subseteq> sources_aux (flow cfs\<^sub>2) s\<^sub>1 x) \<longrightarrow>
        (c\<^sub>1, t\<^sub>1) \<rightarrow>* (c\<^sub>2', t\<^sub>2) \<and> (c\<^sub>2 = SKIP) = (c\<^sub>2' = SKIP)) \<and>
      (s\<^sub>1 = t\<^sub>1 (\<subseteq> sources (flow cfs\<^sub>2) s\<^sub>1 x) \<longrightarrow> s\<^sub>2 x = t\<^sub>2 x)"
    proof
      assume R: "(c\<^sub>1, s\<^sub>1) = (WHILE b DO c, s)"
      hence "(WHILE b DO c, s) \<rightarrow>*{cfs\<^sub>2} (c\<^sub>2, s\<^sub>2)"
        using J by simp
      hence
       "(c\<^sub>2, s\<^sub>2) = (WHILE b DO c, s) \<and>
          flow cfs\<^sub>2 = [] \<or>
        (IF b THEN c;; WHILE b DO c ELSE SKIP, s) \<rightarrow>*{tl cfs\<^sub>2} (c\<^sub>2, s\<^sub>2) \<and>
          flow cfs\<^sub>2 = flow (tl cfs\<^sub>2)"
        (is "?P \<or> ?Q \<and> ?R")
        by (rule small_stepsl_while)
      thus ?thesis
      proof (rule disjE, erule_tac [2] conjE)
        assume ?P
        with R show ?thesis
          by auto
      next
        assume ?Q and ?R
        have
         "(c\<^sub>2, s\<^sub>2) = (IF b THEN c;; WHILE b DO c ELSE SKIP, s) \<and>
            flow (tl cfs\<^sub>2) = [] \<or>
          bval b s \<and> (c;; WHILE b DO c, s) \<rightarrow>*{tl2 cfs\<^sub>2} (c\<^sub>2, s\<^sub>2) \<and>
            flow (tl cfs\<^sub>2) = \<langle>bvars b\<rangle> # flow (tl2 cfs\<^sub>2) \<or>
          \<not> bval b s \<and> (SKIP, s) \<rightarrow>*{tl2 cfs\<^sub>2} (c\<^sub>2, s\<^sub>2) \<and>
            flow (tl cfs\<^sub>2) = \<langle>bvars b\<rangle> # flow (tl2 cfs\<^sub>2)"
          using `?Q` by (rule small_stepsl_if)
        thus ?thesis
        proof (erule_tac disjE, erule_tac [2] disjE, (erule_tac [2-3] conjE)+)
          assume "(c\<^sub>2, s\<^sub>2) = (IF b THEN c;; WHILE b DO c ELSE SKIP, s) \<and>
            flow (tl cfs\<^sub>2) = []"
          with R and `?R` show ?thesis
            by auto
        next
          assume S: "bval b s"
          with F and O and P have T: "s \<in> Univ B\<^sub>1' (\<subseteq> state \<inter> Y)"
            by (drule_tac btyping2_approx [where s = s], auto)
          assume U: "(c;; WHILE b DO c, s) \<rightarrow>*{tl2 cfs\<^sub>2} (c\<^sub>2, s\<^sub>2)"
          hence
           "(\<exists>c' cfs. c\<^sub>2 = c';; WHILE b DO c \<and>
              (c, s) \<rightarrow>*{cfs} (c', s\<^sub>2) \<and>
              flow (tl2 cfs\<^sub>2) = flow cfs) \<or>
            (\<exists>s' cfs cfs'. length cfs' < length (tl2 cfs\<^sub>2) \<and>
              (c, s) \<rightarrow>*{cfs} (SKIP, s') \<and>
              (WHILE b DO c, s') \<rightarrow>*{cfs'} (c\<^sub>2, s\<^sub>2) \<and>
              flow (tl2 cfs\<^sub>2) = flow cfs @ flow cfs')"
            by (rule small_stepsl_seq)
          moreover assume "flow (tl cfs\<^sub>2) = \<langle>bvars b\<rangle> # flow (tl2 cfs\<^sub>2)"
          moreover have "s\<^sub>2 = run_flow (flow (tl2 cfs\<^sub>2)) s"
            using U by (rule small_stepsl_run_flow)
          moreover {
            fix c' cfs
            assume "(c, s) \<rightarrow>*{cfs} (c', run_flow (flow cfs) s)"
            then obtain c\<^sub>2' and t\<^sub>2 where V: "\<forall>x.
              (s = t\<^sub>1 (\<subseteq> sources_aux (flow cfs) s x) \<longrightarrow>
                (c, t\<^sub>1) \<rightarrow>* (c\<^sub>2', t\<^sub>2) \<and> (c' = SKIP) = (c\<^sub>2' = SKIP)) \<and>
              (s = t\<^sub>1 (\<subseteq> sources (flow cfs) s x) \<longrightarrow>
                run_flow (flow cfs) s x = t\<^sub>2 x)"
              using B [of B\<^sub>1 C B\<^sub>1' D' s "[]" c s cfs c'
               "run_flow (flow cfs) s"] and N and T by force
            {
              fix x
              assume W: "s = t\<^sub>1 (\<subseteq> sources_aux (\<langle>bvars b\<rangle> # flow cfs) s x)"
              moreover have "sources_aux (flow cfs) s x \<subseteq>
                sources_aux (\<langle>bvars b\<rangle> # (flow cfs)) s x"
                by (rule sources_aux_observe_tl)
              ultimately have "(c, t\<^sub>1) \<rightarrow>* (c\<^sub>2', t\<^sub>2)"
                using V by blast
              hence "(c;; WHILE b DO c, t\<^sub>1) \<rightarrow>* (c\<^sub>2';; WHILE b DO c, t\<^sub>2)"
                by (rule star_seq2)
              moreover have "s = t\<^sub>1 (\<subseteq> bvars b)"
                using Q and W by (blast dest: sources_aux_observe_hd)
              hence "bval b t\<^sub>1"
                using S by (blast dest: bvars_bval)
              hence "(WHILE b DO c, t\<^sub>1) \<rightarrow>* (c;; WHILE b DO c, t\<^sub>1)"
                by (blast intro: star_trans)
              ultimately have "(WHILE b DO c, t\<^sub>1) \<rightarrow>*
               (c\<^sub>2';; WHILE b DO c, t\<^sub>2) \<and> c\<^sub>2';; WHILE b DO c \<noteq> SKIP"
                by (blast intro: star_trans)
            }
            moreover {
              fix x
              assume "s = t\<^sub>1 (\<subseteq> sources (\<langle>bvars b\<rangle> # flow cfs) s x)"
              moreover have "sources (flow cfs) s x \<subseteq>
                sources (\<langle>bvars b\<rangle> # (flow cfs)) s x"
                by (rule sources_observe_tl)
              ultimately have "run_flow (flow cfs) s x = t\<^sub>2 x"
                using V by blast
            }
            ultimately have "\<exists>c\<^sub>2' t\<^sub>2. \<forall>x.
              (s = t\<^sub>1 (\<subseteq> sources_aux (\<langle>bvars b\<rangle> # flow cfs) s x) \<longrightarrow>
                (WHILE b DO c, t\<^sub>1) \<rightarrow>* (c\<^sub>2', t\<^sub>2) \<and> c\<^sub>2' \<noteq> SKIP) \<and>
              (s = t\<^sub>1 (\<subseteq> sources (\<langle>bvars b\<rangle> # flow cfs) s x) \<longrightarrow>
                run_flow (flow cfs) s x = t\<^sub>2 x)"
              by blast
          }
          moreover {
            fix s' cfs cfs'
            assume
              V: "length cfs' < length cfs\<^sub>2 - Suc (Suc 0)" and
              W: "(c, s) \<rightarrow>*{cfs} (SKIP, s')" and
              X: "(WHILE b DO c, s') \<rightarrow>*{cfs'}
                (c\<^sub>2, run_flow (flow cfs') (run_flow (flow cfs) s))"
            then obtain c\<^sub>2' and t\<^sub>2 where "\<forall>x.
              (s = t\<^sub>1 (\<subseteq> sources_aux (flow cfs) s x) \<longrightarrow>
                (c, t\<^sub>1) \<rightarrow>* (c\<^sub>2', t\<^sub>2) \<and> (SKIP = SKIP) = (c\<^sub>2' = SKIP)) \<and>
              (s = t\<^sub>1 (\<subseteq> sources (flow cfs) s x) \<longrightarrow> s' x = t\<^sub>2 x)"
              using B [of B\<^sub>1 C B\<^sub>1' D' s "[]" c s cfs SKIP s']
               and N and T by force
            moreover have Y: "s' = run_flow (flow cfs) s"
              using W by (rule small_stepsl_run_flow)
            ultimately have Z: "\<forall>x.
              (s = t\<^sub>1 (\<subseteq> sources_aux (flow cfs) s x) \<longrightarrow>
                (c, t\<^sub>1) \<rightarrow>* (SKIP, t\<^sub>2)) \<and>
              (s = t\<^sub>1 (\<subseteq> sources (flow cfs) s x) \<longrightarrow>
                run_flow (flow cfs) s x = t\<^sub>2 x)"
              by blast
            assume "s\<^sub>2 = run_flow (flow cfs') (run_flow (flow cfs) s)"
            moreover have "(c, s) \<Rightarrow> s'"
              using W by (auto dest: small_stepsl_steps simp: big_iff_small)
            hence "s' \<in> Univ C (\<subseteq> state \<inter> Y)"
              using M and S by blast
            ultimately obtain c\<^sub>3' and t\<^sub>3 where AA: "\<forall>x.
              (run_flow (flow cfs) s = t\<^sub>2
                (\<subseteq> sources_aux (flow cfs') (run_flow (flow cfs) s) x) \<longrightarrow>
                  (WHILE b DO c, t\<^sub>2) \<rightarrow>* (c\<^sub>3', t\<^sub>3) \<and>
                  (c\<^sub>2 = SKIP) = (c\<^sub>3' = SKIP)) \<and>
              (run_flow (flow cfs) s = t\<^sub>2
                (\<subseteq> sources (flow cfs') (run_flow (flow cfs) s) x) \<longrightarrow>
                  run_flow (flow cfs') (run_flow (flow cfs) s) x = t\<^sub>3 x)"
              using K [of cfs' "[]" cfs' s' "WHILE b DO c" s']
               and V and X and Y by force
            {
              fix x
              assume AB: "s = t\<^sub>1
                (\<subseteq> sources_aux (\<langle>bvars b\<rangle> # flow cfs @ flow cfs') s x)"
              moreover have "sources_aux (flow cfs) s x \<subseteq>
                sources_aux (flow cfs @ flow cfs') s x"
                by (rule sources_aux_append)
              moreover have AC: "sources_aux (flow cfs @ flow cfs') s x \<subseteq>
                sources_aux (\<langle>bvars b\<rangle> # flow cfs @ flow cfs') s x"
                by (rule sources_aux_observe_tl)
              ultimately have "(c, t\<^sub>1) \<rightarrow>* (SKIP, t\<^sub>2)"
                using Z by blast
              hence "(c;; WHILE b DO c, t\<^sub>1) \<rightarrow>* (SKIP;; WHILE b DO c, t\<^sub>2)"
                by (rule star_seq2)
              moreover have "s = t\<^sub>1 (\<subseteq> bvars b)"
                using Q and AB by (blast dest: sources_aux_observe_hd)
              hence "bval b t\<^sub>1"
                using S by (blast dest: bvars_bval)
              hence "(WHILE b DO c, t\<^sub>1) \<rightarrow>* (c;; WHILE b DO c, t\<^sub>1)"
                by (blast intro: star_trans)
              ultimately have "(WHILE b DO c, t\<^sub>1) \<rightarrow>* (WHILE b DO c, t\<^sub>2)"
                by (blast intro: star_trans)
              moreover have "run_flow (flow cfs) s = t\<^sub>2
                (\<subseteq> sources_aux (flow cfs') (run_flow (flow cfs) s) x)"
              proof
                fix y
                assume "y \<in> sources_aux (flow cfs')
                  (run_flow (flow cfs) s) x"
                hence "sources (flow cfs) s y \<subseteq>
                  sources_aux (flow cfs @ flow cfs') s x"
                  by (rule sources_aux_member)
                hence "sources (flow cfs) s y \<subseteq>
                  sources_aux (\<langle>bvars b\<rangle> # flow cfs @ flow cfs') s x"
                  using AC by simp
                thus "run_flow (flow cfs) s y = t\<^sub>2 y"
                  using Z and AB by blast
              qed
              hence "(WHILE b DO c, t\<^sub>2) \<rightarrow>* (c\<^sub>3', t\<^sub>3) \<and>
                (c\<^sub>2 = SKIP) = (c\<^sub>3' = SKIP)"
                using AA by simp
              ultimately have "(WHILE b DO c, t\<^sub>1) \<rightarrow>* (c\<^sub>3', t\<^sub>3) \<and>
                (c\<^sub>2 = SKIP) = (c\<^sub>3' = SKIP)"
                by (blast intro: star_trans)
            }
            moreover {
              fix x
              assume AB: "s = t\<^sub>1
                (\<subseteq> sources (\<langle>bvars b\<rangle> # flow cfs @ flow cfs') s x)"
              have "run_flow (flow cfs) s = t\<^sub>2
                (\<subseteq> sources (flow cfs') (run_flow (flow cfs) s) x)"
              proof
                fix y
                assume "y \<in> sources (flow cfs')
                  (run_flow (flow cfs) s) x"
                hence "sources (flow cfs) s y \<subseteq>
                  sources (flow cfs @ flow cfs') s x"
                  by (rule sources_member)
                moreover have "sources (flow cfs @ flow cfs') s x \<subseteq>
                  sources (\<langle>bvars b\<rangle> # flow cfs @ flow cfs') s x"
                  by (rule sources_observe_tl)
                ultimately have "sources (flow cfs) s y \<subseteq>
                  sources (\<langle>bvars b\<rangle> # flow cfs @ flow cfs') s x"
                  by simp
                thus "run_flow (flow cfs) s y = t\<^sub>2 y"
                  using Z and AB by blast
              qed
              hence "run_flow (flow cfs') (run_flow (flow cfs) s) x = t\<^sub>3 x"
                using AA by simp
            }
            ultimately have "\<exists>c\<^sub>3' t\<^sub>3. \<forall>x.
              (s = t\<^sub>1
                (\<subseteq> sources_aux (\<langle>bvars b\<rangle> # flow cfs @ flow cfs') s x) \<longrightarrow>
                  (WHILE b DO c, t\<^sub>1) \<rightarrow>* (c\<^sub>3', t\<^sub>3) \<and>
                  (c\<^sub>2 = SKIP) = (c\<^sub>3' = SKIP)) \<and>
              (s = t\<^sub>1
                (\<subseteq> sources (\<langle>bvars b\<rangle> # flow cfs @ flow cfs') s x) \<longrightarrow>
                  run_flow (flow cfs') (run_flow (flow cfs) s) x = t\<^sub>3 x)"
              by auto
          }
          ultimately show ?thesis
            using R and `?R` by (auto simp: run_flow_append)
        next
          assume
            S: "\<not> bval b s" and
            T: "flow (tl cfs\<^sub>2) = \<langle>bvars b\<rangle> # flow (tl2 cfs\<^sub>2)"
          assume "(SKIP, s) \<rightarrow>*{tl2 cfs\<^sub>2} (c\<^sub>2, s\<^sub>2)"
          hence U: "(c\<^sub>2, s\<^sub>2) = (SKIP, s) \<and> flow (tl2 cfs\<^sub>2) = []"
            by (rule small_stepsl_skip)
          show ?thesis
          proof (rule exI [of _ SKIP], rule exI [of _ t\<^sub>1])
            {
              fix x
              have "(WHILE b DO c, t\<^sub>1) \<rightarrow>
                (IF b THEN c;; WHILE b DO c ELSE SKIP, t\<^sub>1)" ..
              moreover assume "s = t\<^sub>1 (\<subseteq> sources_aux [\<langle>bvars b\<rangle>] s x)"
              hence "s = t\<^sub>1 (\<subseteq> bvars b)"
                using Q by (blast dest: sources_aux_observe_hd)
              hence "\<not> bval b t\<^sub>1"
                using S by (blast dest: bvars_bval)
              hence "(IF b THEN c;; WHILE b DO c ELSE SKIP, t\<^sub>1) \<rightarrow>
                (SKIP, t\<^sub>1)" ..
              ultimately have "(WHILE b DO c, t\<^sub>1) \<rightarrow>* (SKIP, t\<^sub>1)"
                by (blast intro: star_trans)
            }
            moreover {
              fix x
              assume "s = t\<^sub>1 (\<subseteq> sources [\<langle>bvars b\<rangle>] s x)"
              hence "s x = t\<^sub>1 x"
                by (subst (asm) append_Nil [symmetric],
                 simp only: sources.simps, auto)
            }
            ultimately show "\<forall>x.
              (s\<^sub>1 = t\<^sub>1 (\<subseteq> sources_aux (flow cfs\<^sub>2) s\<^sub>1 x) \<longrightarrow>
                (c\<^sub>1, t\<^sub>1) \<rightarrow>* (SKIP, t\<^sub>1) \<and> (c\<^sub>2 = SKIP) = (SKIP = SKIP)) \<and>
              (s\<^sub>1 = t\<^sub>1 (\<subseteq> sources (flow cfs\<^sub>2) s\<^sub>1 x) \<longrightarrow> s\<^sub>2 x = t\<^sub>1 x)"
              using R and T and U and `?R` by auto
          qed
        qed
      qed
    next
      assume "(IF b THEN c;; WHILE b DO c ELSE SKIP, s) \<rightarrow>*{tl cfs\<^sub>1} (c\<^sub>1, s\<^sub>1)"
      hence
       "(c\<^sub>1, s\<^sub>1) = (IF b THEN c;; WHILE b DO c ELSE SKIP, s) \<and>
          flow (tl cfs\<^sub>1) = [] \<or>
        bval b s \<and> (c;; WHILE b DO c, s) \<rightarrow>*{tl2 cfs\<^sub>1} (c\<^sub>1, s\<^sub>1) \<and>
          flow (tl cfs\<^sub>1) = \<langle>bvars b\<rangle> # flow (tl2 cfs\<^sub>1) \<or>
        \<not> bval b s \<and> (SKIP, s) \<rightarrow>*{tl2 cfs\<^sub>1} (c\<^sub>1, s\<^sub>1) \<and>
          flow (tl cfs\<^sub>1) = \<langle>bvars b\<rangle> # flow (tl2 cfs\<^sub>1)"
        by (rule small_stepsl_if)
      thus ?thesis
      proof (rule disjE, erule_tac [2] disjE, erule_tac conjE,
       (erule_tac [2-3] conjE)+)
        assume R: "(c\<^sub>1, s\<^sub>1) = (IF b THEN c;; WHILE b DO c ELSE SKIP, s)"
        hence "(IF b THEN c;; WHILE b DO c ELSE SKIP, s) \<rightarrow>*{cfs\<^sub>2} (c\<^sub>2, s\<^sub>2)"
          using J by simp
        hence
         "(c\<^sub>2, s\<^sub>2) = (IF b THEN c;; WHILE b DO c ELSE SKIP, s) \<and>
            flow cfs\<^sub>2 = [] \<or>
          bval b s \<and> (c;; WHILE b DO c, s) \<rightarrow>*{tl cfs\<^sub>2} (c\<^sub>2, s\<^sub>2) \<and>
            flow cfs\<^sub>2 = \<langle>bvars b\<rangle> # flow (tl cfs\<^sub>2) \<or>
          \<not> bval b s \<and> (SKIP, s) \<rightarrow>*{tl cfs\<^sub>2} (c\<^sub>2, s\<^sub>2) \<and>
            flow cfs\<^sub>2 = \<langle>bvars b\<rangle> # flow (tl cfs\<^sub>2)"
          by (rule small_stepsl_if)
        thus ?thesis
        proof (erule_tac disjE, erule_tac [2] disjE, (erule_tac [2-3] conjE)+)
          assume "(c\<^sub>2, s\<^sub>2) = (IF b THEN c;; WHILE b DO c ELSE SKIP, s) \<and>
            flow cfs\<^sub>2 = []"
          with R show ?thesis
            by auto
        next
          assume S: "bval b s"
          with F and O and P have T: "s \<in> Univ B\<^sub>1' (\<subseteq> state \<inter> Y)"
            by (drule_tac btyping2_approx [where s = s], auto)
          assume U: "(c;; WHILE b DO c, s) \<rightarrow>*{tl cfs\<^sub>2} (c\<^sub>2, s\<^sub>2)"
          hence
           "(\<exists>c' cfs. c\<^sub>2 = c';; WHILE b DO c \<and>
              (c, s) \<rightarrow>*{cfs} (c', s\<^sub>2) \<and>
              flow (tl cfs\<^sub>2) = flow cfs) \<or>
            (\<exists>s' cfs cfs'. length cfs' < length (tl cfs\<^sub>2) \<and>
              (c, s) \<rightarrow>*{cfs} (SKIP, s') \<and>
              (WHILE b DO c, s') \<rightarrow>*{cfs'} (c\<^sub>2, s\<^sub>2) \<and>
              flow (tl cfs\<^sub>2) = flow cfs @ flow cfs')"
            by (rule small_stepsl_seq)
          moreover assume "flow cfs\<^sub>2 = \<langle>bvars b\<rangle> # flow (tl cfs\<^sub>2)"
          moreover have "s\<^sub>2 = run_flow (flow (tl cfs\<^sub>2)) s"
            using U by (rule small_stepsl_run_flow)
          moreover {
            fix c' cfs
            assume "(c, s) \<rightarrow>*{cfs} (c', run_flow (flow cfs) s)"
            then obtain c\<^sub>2' and t\<^sub>2 where V: "\<forall>x.
              (s = t\<^sub>1 (\<subseteq> sources_aux (flow cfs) s x) \<longrightarrow>
                (c, t\<^sub>1) \<rightarrow>* (c\<^sub>2', t\<^sub>2) \<and> (c' = SKIP) = (c\<^sub>2' = SKIP)) \<and>
              (s = t\<^sub>1 (\<subseteq> sources (flow cfs) s x) \<longrightarrow>
                run_flow (flow cfs) s x = t\<^sub>2 x)"
              using B [of B\<^sub>1 C B\<^sub>1' D' s "[]" c s cfs c'
               "run_flow (flow cfs) s"] and N and T by force
            {
              fix x
              assume W: "s = t\<^sub>1 (\<subseteq> sources_aux (\<langle>bvars b\<rangle> # flow cfs) s x)"
              moreover have "sources_aux (flow cfs) s x \<subseteq>
                sources_aux (\<langle>bvars b\<rangle> # (flow cfs)) s x"
                by (rule sources_aux_observe_tl)
              ultimately have "(c, t\<^sub>1) \<rightarrow>* (c\<^sub>2', t\<^sub>2)"
                using V by blast
              hence "(c;; WHILE b DO c, t\<^sub>1) \<rightarrow>* (c\<^sub>2';; WHILE b DO c, t\<^sub>2)"
                by (rule star_seq2)
              moreover have "s = t\<^sub>1 (\<subseteq> bvars b)"
                using Q and W by (blast dest: sources_aux_observe_hd)
              hence "bval b t\<^sub>1"
                using S by (blast dest: bvars_bval)
              hence "(IF b THEN c;; WHILE b DO c ELSE SKIP, t\<^sub>1) \<rightarrow>
                (c;; WHILE b DO c, t\<^sub>1)" ..
              ultimately have
               "(IF b THEN c;; WHILE b DO c ELSE SKIP, t\<^sub>1) \<rightarrow>*
                  (c\<^sub>2';; WHILE b DO c, t\<^sub>2) \<and> c\<^sub>2';; WHILE b DO c \<noteq> SKIP"
                by (blast intro: star_trans)
            }
            moreover {
              fix x
              assume "s = t\<^sub>1 (\<subseteq> sources (\<langle>bvars b\<rangle> # flow cfs) s x)"
              moreover have "sources (flow cfs) s x \<subseteq>
                sources (\<langle>bvars b\<rangle> # (flow cfs)) s x"
                by (rule sources_observe_tl)
              ultimately have "run_flow (flow cfs) s x = t\<^sub>2 x"
                using V by blast
            }
            ultimately have "\<exists>c\<^sub>2' t\<^sub>2. \<forall>x.
              (s = t\<^sub>1 (\<subseteq> sources_aux (\<langle>bvars b\<rangle> # flow cfs) s x) \<longrightarrow>
                (IF b THEN c;; WHILE b DO c ELSE SKIP, t\<^sub>1) \<rightarrow>* (c\<^sub>2', t\<^sub>2) \<and>
                  c\<^sub>2' \<noteq> SKIP) \<and>
              (s = t\<^sub>1 (\<subseteq> sources (\<langle>bvars b\<rangle> # flow cfs) s x) \<longrightarrow>
                run_flow (flow cfs) s x = t\<^sub>2 x)"
              by blast
          }
          moreover {
            fix s' cfs cfs'
            assume
              V: "length cfs' < length cfs\<^sub>2 - Suc 0" and
              W: "(c, s) \<rightarrow>*{cfs} (SKIP, s')" and
              X: "(WHILE b DO c, s') \<rightarrow>*{cfs'}
                (c\<^sub>2, run_flow (flow cfs') (run_flow (flow cfs) s))"
            then obtain c\<^sub>2' and t\<^sub>2 where "\<forall>x.
              (s = t\<^sub>1 (\<subseteq> sources_aux (flow cfs) s x) \<longrightarrow>
                (c, t\<^sub>1) \<rightarrow>* (c\<^sub>2', t\<^sub>2) \<and> (SKIP = SKIP) = (c\<^sub>2' = SKIP)) \<and>
              (s = t\<^sub>1 (\<subseteq> sources (flow cfs) s x) \<longrightarrow> s' x = t\<^sub>2 x)"
              using B [of B\<^sub>1 C B\<^sub>1' D' s "[]" c s cfs SKIP s']
               and N and T by force
            moreover have Y: "s' = run_flow (flow cfs) s"
              using W by (rule small_stepsl_run_flow)
            ultimately have Z: "\<forall>x.
              (s = t\<^sub>1 (\<subseteq> sources_aux (flow cfs) s x) \<longrightarrow>
                (c, t\<^sub>1) \<rightarrow>* (SKIP, t\<^sub>2)) \<and>
              (s = t\<^sub>1 (\<subseteq> sources (flow cfs) s x) \<longrightarrow>
                run_flow (flow cfs) s x = t\<^sub>2 x)"
              by blast
            assume "s\<^sub>2 = run_flow (flow cfs') (run_flow (flow cfs) s)"
            moreover have "(c, s) \<Rightarrow> s'"
              using W by (auto dest: small_stepsl_steps simp: big_iff_small)
            hence "s' \<in> Univ C (\<subseteq> state \<inter> Y)"
              using M and S by blast
            ultimately obtain c\<^sub>3' and t\<^sub>3 where AA: "\<forall>x.
              (run_flow (flow cfs) s = t\<^sub>2
                (\<subseteq> sources_aux (flow cfs') (run_flow (flow cfs) s) x) \<longrightarrow>
                  (WHILE b DO c, t\<^sub>2) \<rightarrow>* (c\<^sub>3', t\<^sub>3) \<and>
                  (c\<^sub>2 = SKIP) = (c\<^sub>3' = SKIP)) \<and>
              (run_flow (flow cfs) s = t\<^sub>2
                (\<subseteq> sources (flow cfs') (run_flow (flow cfs) s) x) \<longrightarrow>
                  run_flow (flow cfs') (run_flow (flow cfs) s) x = t\<^sub>3 x)"
              using K [of cfs' "[]" cfs' s' "WHILE b DO c" s']
               and V and X and Y by force
            {
              fix x
              assume AB: "s = t\<^sub>1
                (\<subseteq> sources_aux (\<langle>bvars b\<rangle> # flow cfs @ flow cfs') s x)"
              moreover have "sources_aux (flow cfs) s x \<subseteq>
                sources_aux (flow cfs @ flow cfs') s x"
                by (rule sources_aux_append)
              moreover have AC: "sources_aux (flow cfs @ flow cfs') s x \<subseteq>
                sources_aux (\<langle>bvars b\<rangle> # flow cfs @ flow cfs') s x"
                by (rule sources_aux_observe_tl)
              ultimately have "(c, t\<^sub>1) \<rightarrow>* (SKIP, t\<^sub>2)"
                using Z by blast
              hence "(c;; WHILE b DO c, t\<^sub>1) \<rightarrow>* (SKIP;; WHILE b DO c, t\<^sub>2)"
                by (rule star_seq2)
              moreover have "s = t\<^sub>1 (\<subseteq> bvars b)"
                using Q and AB by (blast dest: sources_aux_observe_hd)
              hence "bval b t\<^sub>1"
                using S by (blast dest: bvars_bval)
              hence "(IF b THEN c;; WHILE b DO c ELSE SKIP, t\<^sub>1) \<rightarrow>
                (c;; WHILE b DO c, t\<^sub>1)" ..
              ultimately have "(IF b THEN c;; WHILE b DO c ELSE SKIP, t\<^sub>1) \<rightarrow>*
                (WHILE b DO c, t\<^sub>2)"
                by (blast intro: star_trans)
              moreover have "run_flow (flow cfs) s = t\<^sub>2
                (\<subseteq> sources_aux (flow cfs') (run_flow (flow cfs) s) x)"
              proof
                fix y
                assume "y \<in> sources_aux (flow cfs')
                  (run_flow (flow cfs) s) x"
                hence "sources (flow cfs) s y \<subseteq>
                  sources_aux (flow cfs @ flow cfs') s x"
                  by (rule sources_aux_member)
                hence "sources (flow cfs) s y \<subseteq>
                  sources_aux (\<langle>bvars b\<rangle> # flow cfs @ flow cfs') s x"
                  using AC by simp
                thus "run_flow (flow cfs) s y = t\<^sub>2 y"
                  using Z and AB by blast
              qed
              hence "(WHILE b DO c, t\<^sub>2) \<rightarrow>* (c\<^sub>3', t\<^sub>3) \<and>
                (c\<^sub>2 = SKIP) = (c\<^sub>3' = SKIP)"
                using AA by simp
              ultimately have
               "(IF b THEN c;; WHILE b DO c ELSE SKIP, t\<^sub>1) \<rightarrow>*
                  (c\<^sub>3', t\<^sub>3) \<and> (c\<^sub>2 = SKIP) = (c\<^sub>3' = SKIP)"
                by (blast intro: star_trans)
            }
            moreover {
              fix x
              assume AB: "s = t\<^sub>1
                (\<subseteq> sources (\<langle>bvars b\<rangle> # flow cfs @ flow cfs') s x)"
              have "run_flow (flow cfs) s = t\<^sub>2
                (\<subseteq> sources (flow cfs') (run_flow (flow cfs) s) x)"
              proof
                fix y
                assume "y \<in> sources (flow cfs')
                  (run_flow (flow cfs) s) x"
                hence "sources (flow cfs) s y \<subseteq>
                  sources (flow cfs @ flow cfs') s x"
                  by (rule sources_member)
                moreover have "sources (flow cfs @ flow cfs') s x \<subseteq>
                  sources (\<langle>bvars b\<rangle> # flow cfs @ flow cfs') s x"
                  by (rule sources_observe_tl)
                ultimately have "sources (flow cfs) s y \<subseteq>
                  sources (\<langle>bvars b\<rangle> # flow cfs @ flow cfs') s x"
                  by simp
                thus "run_flow (flow cfs) s y = t\<^sub>2 y"
                  using Z and AB by blast
              qed
              hence "run_flow (flow cfs') (run_flow (flow cfs) s) x = t\<^sub>3 x"
                using AA by simp
            }
            ultimately have "\<exists>c\<^sub>3' t\<^sub>3. \<forall>x.
              (s = t\<^sub>1
                (\<subseteq> sources_aux (\<langle>bvars b\<rangle> # flow cfs @ flow cfs') s x) \<longrightarrow>
                  (IF b THEN c;; WHILE b DO c ELSE SKIP, t\<^sub>1) \<rightarrow>* (c\<^sub>3', t\<^sub>3) \<and>
                  (c\<^sub>2 = SKIP) = (c\<^sub>3' = SKIP)) \<and>
              (s = t\<^sub>1
                (\<subseteq> sources (\<langle>bvars b\<rangle> # flow cfs @ flow cfs') s x) \<longrightarrow>
                  run_flow (flow cfs') (run_flow (flow cfs) s) x = t\<^sub>3 x)"
              by auto
          }
          ultimately show ?thesis
            using R by (auto simp: run_flow_append)
        next
          assume
            S: "\<not> bval b s" and
            T: "flow cfs\<^sub>2 = \<langle>bvars b\<rangle> # flow (tl cfs\<^sub>2)"
          assume "(SKIP, s) \<rightarrow>*{tl cfs\<^sub>2} (c\<^sub>2, s\<^sub>2)"
          hence U: "(c\<^sub>2, s\<^sub>2) = (SKIP, s) \<and> flow (tl cfs\<^sub>2) = []"
            by (rule small_stepsl_skip)
          show ?thesis
          proof (rule exI [of _ SKIP], rule exI [of _ t\<^sub>1])
            {
              fix x
              assume "s = t\<^sub>1 (\<subseteq> sources_aux [\<langle>bvars b\<rangle>] s x)"
              hence "s = t\<^sub>1 (\<subseteq> bvars b)"
                using Q by (blast dest: sources_aux_observe_hd)
              hence "\<not> bval b t\<^sub>1"
                using S by (blast dest: bvars_bval)
              hence "(IF b THEN c;; WHILE b DO c ELSE SKIP, t\<^sub>1) \<rightarrow>
                (SKIP, t\<^sub>1)" ..
            }
            moreover {
              fix x
              assume "s = t\<^sub>1 (\<subseteq> sources [\<langle>bvars b\<rangle>] s x)"
              hence "s x = t\<^sub>1 x"
                by (subst (asm) append_Nil [symmetric],
                 simp only: sources.simps, auto)
            }
            ultimately show "\<forall>x.
              (s\<^sub>1 = t\<^sub>1 (\<subseteq> sources_aux (flow cfs\<^sub>2) s\<^sub>1 x) \<longrightarrow>
                (c\<^sub>1, t\<^sub>1) \<rightarrow>* (SKIP, t\<^sub>1) \<and> (c\<^sub>2 = SKIP) = (SKIP = SKIP)) \<and>
              (s\<^sub>1 = t\<^sub>1 (\<subseteq> sources (flow cfs\<^sub>2) s\<^sub>1 x) \<longrightarrow> s\<^sub>2 x = t\<^sub>1 x)"
              using R and T and U by auto
          qed
        qed
      next
        assume R: "bval b s"
        with F and O and P have S: "s \<in> Univ B\<^sub>1' (\<subseteq> state \<inter> Y)"
          by (drule_tac btyping2_approx [where s = s], auto)
        assume "(c;; WHILE b DO c, s) \<rightarrow>*{tl2 cfs\<^sub>1} (c\<^sub>1, s\<^sub>1)"
        hence
         "(\<exists>c' cfs'. c\<^sub>1 = c';; WHILE b DO c \<and>
            (c, s) \<rightarrow>*{cfs'} (c', s\<^sub>1) \<and>
            flow (tl2 cfs\<^sub>1) = flow cfs') \<or>
          (\<exists>s' cfs' cfs''. length cfs'' < length (tl2 cfs\<^sub>1) \<and>
            (c, s) \<rightarrow>*{cfs'} (SKIP, s') \<and>
            (WHILE b DO c, s') \<rightarrow>*{cfs''} (c\<^sub>1, s\<^sub>1) \<and>
            flow (tl2 cfs\<^sub>1) = flow cfs' @ flow cfs'')"
          by (rule small_stepsl_seq)
        moreover {
          fix c' cfs
          assume
            T: "(c, s) \<rightarrow>*{cfs} (c', s\<^sub>1)" and
            U: "c\<^sub>1 = c';; WHILE b DO c"
          hence V: "(c';; WHILE b DO c, s\<^sub>1) \<rightarrow>*{cfs\<^sub>2} (c\<^sub>2, s\<^sub>2)"
            using J by simp
          hence W: "s\<^sub>2 = run_flow (flow cfs\<^sub>2) s\<^sub>1"
            by (rule small_stepsl_run_flow)
          have
           "(\<exists>c'' cfs'. c\<^sub>2 = c'';; WHILE b DO c \<and>
              (c', s\<^sub>1) \<rightarrow>*{cfs'} (c'', s\<^sub>2) \<and>
              flow cfs\<^sub>2 = flow cfs') \<or>
            (\<exists>s' cfs' cfs''. length cfs'' < length cfs\<^sub>2 \<and>
              (c', s\<^sub>1) \<rightarrow>*{cfs'} (SKIP, s') \<and>
              (WHILE b DO c, s') \<rightarrow>*{cfs''} (c\<^sub>2, s\<^sub>2) \<and>
              flow cfs\<^sub>2 = flow cfs' @ flow cfs'')"
            using V by (rule small_stepsl_seq)
          moreover {
            fix c'' cfs'
            assume "(c', s\<^sub>1) \<rightarrow>*{cfs'} (c'', s\<^sub>2)"
            then obtain c\<^sub>2' and t\<^sub>2 where X: "\<forall>x.
              (s\<^sub>1 = t\<^sub>1 (\<subseteq> sources_aux (flow cfs') s\<^sub>1 x) \<longrightarrow>
                (c', t\<^sub>1) \<rightarrow>* (c\<^sub>2', t\<^sub>2) \<and> (c'' = SKIP) = (c\<^sub>2' = SKIP)) \<and>
              (s\<^sub>1 = t\<^sub>1 (\<subseteq> sources (flow cfs') s\<^sub>1 x) \<longrightarrow>
                run_flow (flow cfs\<^sub>2) s\<^sub>1 x = t\<^sub>2 x)"
              using B [of B\<^sub>1 C B\<^sub>1' D' s cfs c' s\<^sub>1 cfs' c''
               "run_flow (flow cfs\<^sub>2) s\<^sub>1"] and N and S and T and W by force
            assume
              Y: "c\<^sub>2 = c'';; WHILE b DO c" and
              Z: "flow cfs\<^sub>2 = flow cfs'"
            have ?thesis
            proof (rule exI [of _ "c\<^sub>2';; WHILE b DO c"], rule exI [of _ t\<^sub>2])
              from U and W and X and Y and Z show "\<forall>x.
                (s\<^sub>1 = t\<^sub>1 (\<subseteq> sources_aux (flow cfs\<^sub>2) s\<^sub>1 x) \<longrightarrow>
                  (c\<^sub>1, t\<^sub>1) \<rightarrow>* (c\<^sub>2';; WHILE b DO c, t\<^sub>2) \<and>
                    (c\<^sub>2 = SKIP) = (c\<^sub>2';; WHILE b DO c = SKIP)) \<and>
                (s\<^sub>1 = t\<^sub>1 (\<subseteq> sources (flow cfs\<^sub>2) s\<^sub>1 x) \<longrightarrow> s\<^sub>2 x = t\<^sub>2 x)"
                by (auto intro: star_seq2)
            qed
          }
          moreover {
            fix s' cfs' cfs''
            assume
              X: "length cfs'' < length cfs\<^sub>2" and
              Y: "(c', s\<^sub>1) \<rightarrow>*{cfs'} (SKIP, s')" and
              Z: "(WHILE b DO c, s') \<rightarrow>*{cfs''} (c\<^sub>2, s\<^sub>2)"
            then obtain c\<^sub>2' and t\<^sub>2 where "\<forall>x.
              (s\<^sub>1 = t\<^sub>1 (\<subseteq> sources_aux (flow cfs') s\<^sub>1 x) \<longrightarrow>
                (c', t\<^sub>1) \<rightarrow>* (c\<^sub>2', t\<^sub>2) \<and> (SKIP = SKIP) = (c\<^sub>2' = SKIP)) \<and>
              (s\<^sub>1 = t\<^sub>1 (\<subseteq> sources (flow cfs') s\<^sub>1 x) \<longrightarrow> s' x = t\<^sub>2 x)"
              using B [of B\<^sub>1 C B\<^sub>1' D' s cfs c' s\<^sub>1 cfs' SKIP s']
               and N and S and T by force
            moreover have AA: "s' = run_flow (flow cfs') s\<^sub>1"
              using Y by (rule small_stepsl_run_flow)
            ultimately have AB: "\<forall>x.
              (s\<^sub>1 = t\<^sub>1 (\<subseteq> sources_aux (flow cfs') s\<^sub>1 x) \<longrightarrow>
                (c', t\<^sub>1) \<rightarrow>* (SKIP, t\<^sub>2)) \<and>
              (s\<^sub>1 = t\<^sub>1 (\<subseteq> sources (flow cfs') s\<^sub>1 x) \<longrightarrow>
                run_flow (flow cfs') s\<^sub>1 x = t\<^sub>2 x)"
              by blast
            have AC: "s\<^sub>2 = run_flow (flow cfs'') s'"
              using Z by (rule small_stepsl_run_flow)
            moreover have "(c, s) \<rightarrow>*{cfs @ cfs'} (SKIP, s')"
              using T and Y by (simp add: small_stepsl_append)
            hence "(c, s) \<Rightarrow> s'"
              by (auto dest: small_stepsl_steps simp: big_iff_small)
            hence "s' \<in> Univ C (\<subseteq> state \<inter> Y)"
              using M and R by blast
            ultimately obtain c\<^sub>2' and t\<^sub>3 where AD: "\<forall>x.
              (run_flow (flow cfs') s\<^sub>1 = t\<^sub>2
                (\<subseteq> sources_aux (flow cfs'') (run_flow (flow cfs') s\<^sub>1) x) \<longrightarrow>
                  (WHILE b DO c, t\<^sub>2) \<rightarrow>* (c\<^sub>2', t\<^sub>3) \<and>
                  (c\<^sub>2 = SKIP) = (c\<^sub>2' = SKIP)) \<and>
              (run_flow (flow cfs') s\<^sub>1 = t\<^sub>2
                (\<subseteq> sources (flow cfs'') (run_flow (flow cfs') s\<^sub>1) x) \<longrightarrow>
                  run_flow (flow cfs'') (run_flow (flow cfs') s\<^sub>1) x = t\<^sub>3 x)"
              using K [of cfs'' "[]" cfs'' s' "WHILE b DO c" s']
               and X and Z and AA by force
            moreover assume "flow cfs\<^sub>2 = flow cfs' @ flow cfs''"
            moreover {
              fix x
              assume AE: "s\<^sub>1 = t\<^sub>1
                (\<subseteq> sources_aux (flow cfs' @ flow cfs'') s\<^sub>1 x)"
              moreover have "sources_aux (flow cfs') s\<^sub>1 x \<subseteq>
                sources_aux (flow cfs' @ flow cfs'') s\<^sub>1 x"
                by (rule sources_aux_append)
              ultimately have "(c', t\<^sub>1) \<rightarrow>* (SKIP, t\<^sub>2)"
                using AB by blast
              hence "(c';; WHILE b DO c, t\<^sub>1) \<rightarrow>* (SKIP;; WHILE b DO c, t\<^sub>2)"
                by (rule star_seq2)
              hence "(c';; WHILE b DO c, t\<^sub>1) \<rightarrow>* (WHILE b DO c, t\<^sub>2)"
                by (blast intro: star_trans)
              moreover have "run_flow (flow cfs') s\<^sub>1 = t\<^sub>2
                (\<subseteq> sources_aux (flow cfs'') (run_flow (flow cfs') s\<^sub>1) x)"
              proof
                fix y
                assume "y \<in> sources_aux (flow cfs'')
                  (run_flow (flow cfs') s\<^sub>1) x"
                hence "sources (flow cfs') s\<^sub>1 y \<subseteq>
                  sources_aux (flow cfs' @ flow cfs'') s\<^sub>1 x"
                  by (rule sources_aux_member)
                thus "run_flow (flow cfs') s\<^sub>1 y = t\<^sub>2 y"
                  using AB and AE by blast
              qed
              hence "(WHILE b DO c, t\<^sub>2) \<rightarrow>* (c\<^sub>2', t\<^sub>3) \<and>
                (c\<^sub>2 = SKIP) = (c\<^sub>2' = SKIP)"
                using AD by simp
              ultimately have "(c';; WHILE b DO c, t\<^sub>1) \<rightarrow>* (c\<^sub>2', t\<^sub>3) \<and>
                (c\<^sub>2 = SKIP) = (c\<^sub>2' = SKIP)"
                by (blast intro: star_trans)
            }
            moreover {
              fix x
              assume AE: "s\<^sub>1 = t\<^sub>1
                (\<subseteq> sources (flow cfs' @ flow cfs'') s\<^sub>1 x)"
              have "run_flow (flow cfs') s\<^sub>1 = t\<^sub>2
                (\<subseteq> sources (flow cfs'') (run_flow (flow cfs') s\<^sub>1) x)"
              proof
                fix y
                assume "y \<in> sources (flow cfs'')
                  (run_flow (flow cfs') s\<^sub>1) x"
                hence "sources (flow cfs') s\<^sub>1 y \<subseteq>
                  sources (flow cfs' @ flow cfs'') s\<^sub>1 x"
                  by (rule sources_member)
                thus "run_flow (flow cfs') s\<^sub>1 y = t\<^sub>2 y"
                  using AB and AE by blast
              qed
              hence "run_flow (flow cfs'')
                (run_flow (flow cfs') s\<^sub>1) x = t\<^sub>3 x"
                using AD by simp
            }
            ultimately have ?thesis
              by (metis U AA AC)
          }
          ultimately have ?thesis
            by blast
        }
        moreover {
          fix s' cfs cfs'
          assume
           "length cfs' < length (tl2 cfs\<^sub>1)" and
           "(c, s) \<rightarrow>*{cfs} (SKIP, s')" and
           "(WHILE b DO c, s') \<rightarrow>*{cfs'} (c\<^sub>1, s\<^sub>1)"
          moreover from this have "(c, s) \<Rightarrow> s'"
            by (auto dest: small_stepsl_steps simp: big_iff_small)
          hence "s' \<in> Univ C (\<subseteq> state \<inter> Y)"
            using M and R by blast
          ultimately have ?thesis
            using K [of "cfs' @ cfs\<^sub>2" cfs' cfs\<^sub>2 s' c\<^sub>1 s\<^sub>1] and J by force
        }
        ultimately show ?thesis
          by blast
      next
        assume "(SKIP, s) \<rightarrow>*{tl2 cfs\<^sub>1} (c\<^sub>1, s\<^sub>1)"
        hence "(c\<^sub>1, s\<^sub>1) = (SKIP, s)"
          by (blast dest: small_stepsl_skip)
        moreover from this have "(c\<^sub>2, s\<^sub>2) = (SKIP, s) \<and> flow cfs\<^sub>2 = []"
          using J by (blast dest: small_stepsl_skip)
        ultimately show ?thesis
          by auto
      qed
    qed
  }
  ultimately show
   "(\<forall>t\<^sub>1. \<exists>c\<^sub>2' t\<^sub>2. \<forall>x.
      (s\<^sub>1 = t\<^sub>1 (\<subseteq> sources_aux (flow cfs\<^sub>2) s\<^sub>1 x) \<longrightarrow>
        (c\<^sub>1, t\<^sub>1) \<rightarrow>* (c\<^sub>2', t\<^sub>2) \<and> (c\<^sub>2 = SKIP) = (c\<^sub>2' = SKIP)) \<and>
      (s\<^sub>1 = t\<^sub>1 (\<subseteq> sources (flow cfs\<^sub>2) s\<^sub>1 x) \<longrightarrow> s\<^sub>2 x = t\<^sub>2 x)) \<and>
    (\<forall>x. (\<exists>(B, Y) \<in> U. \<exists>s \<in> B. \<exists>y \<in> Y. \<not> s: dom y \<leadsto> dom x) \<longrightarrow>
      no_upd (flow cfs\<^sub>2) x)"
    using L by auto
qed

lemma ctyping2_correct_aux:
 "\<lbrakk>(U, v) \<Turnstile> c (\<subseteq> A, X) = Some (B, Y); s \<in> Univ A (\<subseteq> state \<inter> X);
    (c, s) \<rightarrow>*{cfs\<^sub>1} (c\<^sub>1, s\<^sub>1); (c\<^sub>1, s\<^sub>1) \<rightarrow>*{cfs\<^sub>2} (c\<^sub>2, s\<^sub>2)\<rbrakk> \<Longrightarrow>
  ok_flow_aux U c\<^sub>1 c\<^sub>2 s\<^sub>1 s\<^sub>2 (flow cfs\<^sub>2)"
proof (induction "(U, v)" c A X arbitrary: B Y U v s c\<^sub>1 c\<^sub>2 s\<^sub>1 s\<^sub>2 cfs\<^sub>1 cfs\<^sub>2
 rule: ctyping2.induct)
  fix A X C Z U v c\<^sub>1 c\<^sub>2 c' c'' s s\<^sub>1 s\<^sub>2 cfs\<^sub>1 cfs\<^sub>2
  show
   "\<lbrakk>\<And>B Y s c' c'' s\<^sub>1 s\<^sub>2 cfs\<^sub>1 cfs\<^sub>2.
      (U, v) \<Turnstile> c\<^sub>1 (\<subseteq> A, X) = Some (B, Y) \<Longrightarrow>
      s \<in> Univ A (\<subseteq> state \<inter> X) \<Longrightarrow>
      (c\<^sub>1, s) \<rightarrow>*{cfs\<^sub>1} (c', s\<^sub>1) \<Longrightarrow>
      (c', s\<^sub>1) \<rightarrow>*{cfs\<^sub>2} (c'', s\<^sub>2) \<Longrightarrow>
      (\<forall>t\<^sub>1. \<exists>c\<^sub>2' t\<^sub>2. \<forall>x.
        (s\<^sub>1 = t\<^sub>1 (\<subseteq> sources_aux (flow cfs\<^sub>2) s\<^sub>1 x) \<longrightarrow>
          (c', t\<^sub>1) \<rightarrow>* (c\<^sub>2', t\<^sub>2) \<and> (c'' = SKIP) = (c\<^sub>2' = SKIP)) \<and>
        (s\<^sub>1 = t\<^sub>1 (\<subseteq> sources (flow cfs\<^sub>2) s\<^sub>1 x) \<longrightarrow> s\<^sub>2 x = t\<^sub>2 x)) \<and>
      (\<forall>x. (\<exists>(B, W) \<in> U. \<exists>s \<in> B. \<exists>y \<in> W. \<not> s: dom y \<leadsto> dom x) \<longrightarrow>
        no_upd (flow cfs\<^sub>2) x);
    \<And>p B Y C Z s c' c'' s\<^sub>1 s\<^sub>2 cfs\<^sub>1 cfs\<^sub>2.
      (U, v) \<Turnstile> c\<^sub>1 (\<subseteq> A, X) = Some p \<Longrightarrow>
      (B, Y) = p \<Longrightarrow>
      (U, v) \<Turnstile> c\<^sub>2 (\<subseteq> B, Y) = Some (C, Z) \<Longrightarrow>
      s \<in> Univ B (\<subseteq> state \<inter> Y) \<Longrightarrow>
      (c\<^sub>2, s) \<rightarrow>*{cfs\<^sub>1} (c', s\<^sub>1) \<Longrightarrow>
      (c', s\<^sub>1) \<rightarrow>*{cfs\<^sub>2} (c'', s\<^sub>2) \<Longrightarrow>
      (\<forall>t\<^sub>1. \<exists>c\<^sub>2'' t\<^sub>2. \<forall>x.
        (s\<^sub>1 = t\<^sub>1 (\<subseteq> sources_aux (flow cfs\<^sub>2) s\<^sub>1 x) \<longrightarrow>
          (c', t\<^sub>1) \<rightarrow>* (c\<^sub>2'', t\<^sub>2) \<and> (c'' = SKIP) = (c\<^sub>2'' = SKIP)) \<and>
        (s\<^sub>1 = t\<^sub>1 (\<subseteq> sources (flow cfs\<^sub>2) s\<^sub>1 x) \<longrightarrow> s\<^sub>2 x = t\<^sub>2 x)) \<and>
      (\<forall>x. (\<exists>(B, W) \<in> U. \<exists>s \<in> B. \<exists>y \<in> W. \<not> s: dom y \<leadsto> dom x) \<longrightarrow>
        no_upd (flow cfs\<^sub>2) x);
    (U, v) \<Turnstile> c\<^sub>1;; c\<^sub>2 (\<subseteq> A, X) = Some (C, Z);
    s \<in> Univ A (\<subseteq> state \<inter> X);
    (c\<^sub>1;; c\<^sub>2, s) \<rightarrow>*{cfs\<^sub>1} (c', s\<^sub>1);
    (c', s\<^sub>1) \<rightarrow>*{cfs\<^sub>2} (c'', s\<^sub>2)\<rbrakk> \<Longrightarrow>
      (\<forall>t\<^sub>1. \<exists>c\<^sub>2' t\<^sub>2. \<forall>x.
        (s\<^sub>1 = t\<^sub>1 (\<subseteq> sources_aux (flow cfs\<^sub>2) s\<^sub>1 x) \<longrightarrow>
          (c', t\<^sub>1) \<rightarrow>* (c\<^sub>2', t\<^sub>2) \<and> (c'' = SKIP) = (c\<^sub>2' = SKIP)) \<and>
        (s\<^sub>1 = t\<^sub>1 (\<subseteq> sources (flow cfs\<^sub>2) s\<^sub>1 x) \<longrightarrow> s\<^sub>2 x = t\<^sub>2 x)) \<and>
      (\<forall>x. (\<exists>(B, W) \<in> U. \<exists>s \<in> B. \<exists>y \<in> W. \<not> s: dom y \<leadsto> dom x) \<longrightarrow>
        no_upd (flow cfs\<^sub>2) x)"
    by (auto del: conjI split: option.split_asm,
     rule ctyping2_correct_aux_seq)
next
  fix A X C Y U v b c\<^sub>1 c\<^sub>2 c' c'' s s\<^sub>1 s\<^sub>2 cfs\<^sub>1 cfs\<^sub>2
  show
   "\<lbrakk>\<And>U' p B\<^sub>1 B\<^sub>2 C Y s c' c'' s\<^sub>1 s\<^sub>2 cfs\<^sub>1 cfs\<^sub>2.
      (U', p) = (insert (Univ? A X, bvars b) U, \<Turnstile> b (\<subseteq> A, X)) \<Longrightarrow>
      (B\<^sub>1, B\<^sub>2) = p \<Longrightarrow>
      (U', v) \<Turnstile> c\<^sub>1 (\<subseteq> B\<^sub>1, X) = Some (C, Y) \<Longrightarrow>
      s \<in> Univ B\<^sub>1 (\<subseteq> state \<inter> X) \<Longrightarrow>
      (c\<^sub>1, s) \<rightarrow>*{cfs\<^sub>1} (c', s\<^sub>1) \<Longrightarrow>
      (c', s\<^sub>1) \<rightarrow>*{cfs\<^sub>2} (c'', s\<^sub>2) \<Longrightarrow>
      (\<forall>t\<^sub>1. \<exists>c\<^sub>2' t\<^sub>2. \<forall>x.
        (s\<^sub>1 = t\<^sub>1 (\<subseteq> sources_aux (flow cfs\<^sub>2) s\<^sub>1 x) \<longrightarrow>
          (c', t\<^sub>1) \<rightarrow>* (c\<^sub>2', t\<^sub>2) \<and> (c'' = SKIP) = (c\<^sub>2' = SKIP)) \<and>
        (s\<^sub>1 = t\<^sub>1 (\<subseteq> sources (flow cfs\<^sub>2) s\<^sub>1 x) \<longrightarrow> s\<^sub>2 x = t\<^sub>2 x)) \<and>
      (\<forall>x. (\<exists>(B, W) \<in> U'. \<exists>s \<in> B. \<exists>y \<in> W. \<not> s: dom y \<leadsto> dom x) \<longrightarrow>
        no_upd (flow cfs\<^sub>2) x);
    \<And>U' p B\<^sub>1 B\<^sub>2 C Y s c' c'' s\<^sub>1 s\<^sub>2 cfs\<^sub>1 cfs\<^sub>2.
      (U', p) = (insert (Univ? A X, bvars b) U, \<Turnstile> b (\<subseteq> A, X)) \<Longrightarrow>
      (B\<^sub>1, B\<^sub>2) = p \<Longrightarrow>
      (U', v) \<Turnstile> c\<^sub>2 (\<subseteq> B\<^sub>2, X) = Some (C, Y) \<Longrightarrow>
      s \<in> Univ B\<^sub>2 (\<subseteq> state \<inter> X) \<Longrightarrow>
      (c\<^sub>2, s) \<rightarrow>*{cfs\<^sub>1} (c', s\<^sub>1) \<Longrightarrow>
      (c', s\<^sub>1) \<rightarrow>*{cfs\<^sub>2} (c'', s\<^sub>2) \<Longrightarrow>
      (\<forall>t\<^sub>1. \<exists>c\<^sub>2'' t\<^sub>2. \<forall>x.
        (s\<^sub>1 = t\<^sub>1 (\<subseteq> sources_aux (flow cfs\<^sub>2) s\<^sub>1 x) \<longrightarrow>
          (c', t\<^sub>1) \<rightarrow>* (c\<^sub>2'', t\<^sub>2) \<and> (c'' = SKIP) = (c\<^sub>2'' = SKIP)) \<and>
        (s\<^sub>1 = t\<^sub>1 (\<subseteq> sources (flow cfs\<^sub>2) s\<^sub>1 x) \<longrightarrow> s\<^sub>2 x = t\<^sub>2 x)) \<and>
      (\<forall>x. (\<exists>(B, W) \<in> U'. \<exists>s \<in> B. \<exists>y \<in> W. \<not> s: dom y \<leadsto> dom x) \<longrightarrow>
        no_upd (flow cfs\<^sub>2) x);
    (U, v) \<Turnstile> IF b THEN c\<^sub>1 ELSE c\<^sub>2 (\<subseteq> A, X) = Some (C, Y);
    s \<in> Univ A (\<subseteq> state \<inter> X);
    (IF b THEN c\<^sub>1 ELSE c\<^sub>2, s) \<rightarrow>*{cfs\<^sub>1} (c', s\<^sub>1);
    (c', s\<^sub>1) \<rightarrow>*{cfs\<^sub>2} (c'', s\<^sub>2)\<rbrakk> \<Longrightarrow>
      (\<forall>t\<^sub>1. \<exists>c\<^sub>2' t\<^sub>2. \<forall>x.
        (s\<^sub>1 = t\<^sub>1 (\<subseteq> sources_aux (flow cfs\<^sub>2) s\<^sub>1 x) \<longrightarrow>
          (c', t\<^sub>1) \<rightarrow>* (c\<^sub>2', t\<^sub>2) \<and> (c'' = SKIP) = (c\<^sub>2' = SKIP)) \<and>
        (s\<^sub>1 = t\<^sub>1 (\<subseteq> sources (flow cfs\<^sub>2) s\<^sub>1 x) \<longrightarrow> s\<^sub>2 x = t\<^sub>2 x)) \<and>
      (\<forall>x. (\<exists>(B, W) \<in> U. \<exists>s \<in> B. \<exists>y \<in> W. \<not> s: dom y \<leadsto> dom x) \<longrightarrow>
        no_upd (flow cfs\<^sub>2) x)"
    by (auto del: conjI split: option.split_asm prod.split_asm,
     rule ctyping2_correct_aux_if)
next
  fix A X B Y U v b c c\<^sub>1 c\<^sub>2 s s\<^sub>1 s\<^sub>2 cfs\<^sub>1 cfs\<^sub>2
  show
   "\<lbrakk>\<And>B\<^sub>1 B\<^sub>2 C Y B\<^sub>1' B\<^sub>2' D Z s c\<^sub>1 c\<^sub>2 s\<^sub>1 s\<^sub>2 cfs\<^sub>1 cfs\<^sub>2.
      (B\<^sub>1, B\<^sub>2) = \<Turnstile> b (\<subseteq> A, X) \<Longrightarrow>
      (C, Y) = \<turnstile> c (\<subseteq> B\<^sub>1, X) \<Longrightarrow>
      (B\<^sub>1', B\<^sub>2') = \<Turnstile> b (\<subseteq> C, Y) \<Longrightarrow>
      \<forall>(B, W) \<in> insert (Univ? A X \<union> Univ? C Y, bvars b) U.
        B: dom ` W \<leadsto> UNIV \<Longrightarrow>
      ({}, False) \<Turnstile> c (\<subseteq> B\<^sub>1, X) = Some (D, Z) \<Longrightarrow>
      s \<in> Univ B\<^sub>1 (\<subseteq> state \<inter> X) \<Longrightarrow>
      (c, s) \<rightarrow>*{cfs\<^sub>1} (c\<^sub>1, s\<^sub>1) \<Longrightarrow>
      (c\<^sub>1, s\<^sub>1) \<rightarrow>*{cfs\<^sub>2} (c\<^sub>2, s\<^sub>2) \<Longrightarrow>
      (\<forall>t\<^sub>1. \<exists>c\<^sub>2' t\<^sub>2. \<forall>B\<^sub>1.
        (s\<^sub>1 = t\<^sub>1 (\<subseteq> sources_aux (flow cfs\<^sub>2) s\<^sub>1 B\<^sub>1) \<longrightarrow>
          (c\<^sub>1, t\<^sub>1) \<rightarrow>* (c\<^sub>2', t\<^sub>2) \<and> (c\<^sub>2 = SKIP) = (c\<^sub>2' = SKIP)) \<and>
        (s\<^sub>1 = t\<^sub>1 (\<subseteq> sources (flow cfs\<^sub>2) s\<^sub>1 B\<^sub>1) \<longrightarrow> s\<^sub>2 B\<^sub>1 = t\<^sub>2 B\<^sub>1)) \<and>
      (\<forall>x. (\<exists>(B, W) \<in> {}. \<exists>s \<in> B. \<exists>y \<in> W. \<not> s: dom y \<leadsto> dom x) \<longrightarrow>
        no_upd (flow cfs\<^sub>2) x);
    \<And>B\<^sub>1 B\<^sub>2 C Y B\<^sub>1' B\<^sub>2' D' Z' s c\<^sub>1 c\<^sub>2 s\<^sub>1 s\<^sub>2 cfs\<^sub>1 cfs\<^sub>2.
      (B\<^sub>1, B\<^sub>2) = \<Turnstile> b (\<subseteq> A, X) \<Longrightarrow>
      (C, Y) = \<turnstile> c (\<subseteq> B\<^sub>1, X) \<Longrightarrow>
      (B\<^sub>1', B\<^sub>2') = \<Turnstile> b (\<subseteq> C, Y) \<Longrightarrow>
      \<forall>(B, W) \<in> insert (Univ? A X \<union> Univ? C Y, bvars b) U.
        B: dom ` W \<leadsto> UNIV \<Longrightarrow>
      ({}, False) \<Turnstile> c (\<subseteq> B\<^sub>1', Y) = Some (D', Z') \<Longrightarrow>
      s \<in> Univ B\<^sub>1' (\<subseteq> state \<inter> Y) \<Longrightarrow>
      (c, s) \<rightarrow>*{cfs\<^sub>1} (c\<^sub>1, s\<^sub>1) \<Longrightarrow>
      (c\<^sub>1, s\<^sub>1) \<rightarrow>*{cfs\<^sub>2} (c\<^sub>2, s\<^sub>2) \<Longrightarrow>
      (\<forall>t\<^sub>1. \<exists>c\<^sub>2' t\<^sub>2. \<forall>B\<^sub>1.
        (s\<^sub>1 = t\<^sub>1 (\<subseteq> sources_aux (flow cfs\<^sub>2) s\<^sub>1 B\<^sub>1) \<longrightarrow>
          (c\<^sub>1, t\<^sub>1) \<rightarrow>* (c\<^sub>2', t\<^sub>2) \<and> (c\<^sub>2 = SKIP) = (c\<^sub>2' = SKIP)) \<and>
        (s\<^sub>1 = t\<^sub>1 (\<subseteq> sources (flow cfs\<^sub>2) s\<^sub>1 B\<^sub>1) \<longrightarrow> s\<^sub>2 B\<^sub>1 = t\<^sub>2 B\<^sub>1)) \<and>
      (\<forall>x. (\<exists>(B, W) \<in> {}. \<exists>s \<in> B. \<exists>y \<in> W. \<not> s: dom y \<leadsto> dom x) \<longrightarrow>
        no_upd (flow cfs\<^sub>2) x);
    (U, v) \<Turnstile> WHILE b DO c (\<subseteq> A, X) = Some (B, Y);
    s \<in> Univ A (\<subseteq> state \<inter> X);
    (WHILE b DO c, s) \<rightarrow>*{cfs\<^sub>1} (c\<^sub>1, s\<^sub>1);
    (c\<^sub>1, s\<^sub>1) \<rightarrow>*{cfs\<^sub>2} (c\<^sub>2, s\<^sub>2)\<rbrakk> \<Longrightarrow>
      (\<forall>t\<^sub>1. \<exists>c\<^sub>2' t\<^sub>2. \<forall>x.
        (s\<^sub>1 = t\<^sub>1 (\<subseteq> sources_aux (flow cfs\<^sub>2) s\<^sub>1 x) \<longrightarrow>
          (c\<^sub>1, t\<^sub>1) \<rightarrow>* (c\<^sub>2', t\<^sub>2) \<and> (c\<^sub>2 = SKIP) = (c\<^sub>2' = SKIP)) \<and>
        (s\<^sub>1 = t\<^sub>1 (\<subseteq> sources (flow cfs\<^sub>2) s\<^sub>1 x) \<longrightarrow> s\<^sub>2 x = t\<^sub>2 x)) \<and>
      (\<forall>x. (\<exists>(B, W) \<in> U. \<exists>s \<in> B. \<exists>y \<in> W. \<not> s: dom y \<leadsto> dom x) \<longrightarrow>
        no_upd (flow cfs\<^sub>2) x)"
    by (auto del: conjI split: option.split_asm prod.split_asm,
     rule ctyping2_correct_aux_while, assumption+, blast)
qed (auto del: conjI split: prod.split_asm)


theorem ctyping2_correct:
  assumes A: "(U, v) \<Turnstile> c (\<subseteq> A, X) = Some (B, Y)"
  shows "correct c A X"
proof -
  {
    fix c\<^sub>1 c\<^sub>2 s\<^sub>1 s\<^sub>2 cfs t\<^sub>1
    assume "ok_flow_aux U c\<^sub>1 c\<^sub>2 s\<^sub>1 s\<^sub>2 (flow cfs)"
    then obtain c\<^sub>2' and t\<^sub>2 where A: "\<forall>x.
      (s\<^sub>1 = t\<^sub>1 (\<subseteq> sources_aux (flow cfs) s\<^sub>1 x) \<longrightarrow>
        (c\<^sub>1, t\<^sub>1) \<rightarrow>* (c\<^sub>2', t\<^sub>2) \<and> (c\<^sub>2 = SKIP) = (c\<^sub>2' = SKIP)) \<and>
      (s\<^sub>1 = t\<^sub>1 (\<subseteq> sources (flow cfs) s\<^sub>1 x) \<longrightarrow> s\<^sub>2 x = t\<^sub>2 x)"
      by blast
    have "\<exists>c\<^sub>2' t\<^sub>2. \<forall>x. s\<^sub>1 = t\<^sub>1 (\<subseteq> sources (flow cfs) s\<^sub>1 x) \<longrightarrow>
      (c\<^sub>1, t\<^sub>1) \<rightarrow>* (c\<^sub>2', t\<^sub>2) \<and> (c\<^sub>2 = SKIP) = (c\<^sub>2' = SKIP) \<and> s\<^sub>2 x = t\<^sub>2 x"
    proof (rule exI [of _ c\<^sub>2'], rule exI [of _ t\<^sub>2])
      have "\<forall>x. s\<^sub>1 = t\<^sub>1 (\<subseteq> sources (flow cfs) s\<^sub>1 x) \<longrightarrow>
        s\<^sub>1 = t\<^sub>1 (\<subseteq> sources_aux (flow cfs) s\<^sub>1 x)"
      proof (rule allI, rule impI)
        fix x
        assume "s\<^sub>1 = t\<^sub>1 (\<subseteq> sources (flow cfs) s\<^sub>1 x)"
        moreover have "sources_aux (flow cfs) s\<^sub>1 x \<subseteq>
          sources (flow cfs) s\<^sub>1 x"
          by (rule sources_aux_sources)
        ultimately show "s\<^sub>1 = t\<^sub>1 (\<subseteq> sources_aux (flow cfs) s\<^sub>1 x)"
          by blast
      qed
      with A show "\<forall>x. s\<^sub>1 = t\<^sub>1 (\<subseteq> sources (flow cfs) s\<^sub>1 x) \<longrightarrow>
        (c\<^sub>1, t\<^sub>1) \<rightarrow>* (c\<^sub>2', t\<^sub>2) \<and> (c\<^sub>2 = SKIP) = (c\<^sub>2' = SKIP) \<and> s\<^sub>2 x = t\<^sub>2 x"
        by auto
    qed
  }
  with A show ?thesis
    by (clarsimp dest!: small_steps_stepsl simp: correct_def,
     drule_tac ctyping2_correct_aux, auto)
qed

end

end
