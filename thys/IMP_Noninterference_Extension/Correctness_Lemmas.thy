(*  Title:       Extension of Stateful Intransitive Noninterference with Inputs, Outputs, and Nondeterminism in Language IMP
    Author:      Pasquale Noce
                 Senior Staff Firmware Engineer at HID Global, Italy
                 pasquale dot noce dot lavoro at gmail dot com
                 pasquale dot noce at hidglobal dot com
*)

section "Sufficiency of well-typedness for information flow correctness: propaedeutic lemmas"

theory Correctness_Lemmas
  imports Overapproximation
begin

text \<open>
\null

The purpose of this section is to prove some further lemmas used in the proof of the main theorem,
which is the subject of the next section.

The proof of one of these lemmas uses the lemmas @{text ctyping1_idem} and @{text ctyping2_approx}
proven in the previous sections.
\<close>


subsection "Global context proofs"

lemma bvars_bval:
 "s = t (\<subseteq> bvars b) \<Longrightarrow> bval b s = bval b t"
by (induction b, simp_all, rule arg_cong2, auto intro: avars_aval)

lemma eq_streams_subset:
 "\<lbrakk>f = f' (\<subseteq> vs, vs', T); T' \<subseteq> T\<rbrakk> \<Longrightarrow> f = f' (\<subseteq> vs, vs', T')"
by (auto simp: eq_streams_def)


lemma flow_append_1:
  assumes A: "\<And>cfs' :: (com \<times> stage) list.
    c # map fst (cfs :: (com \<times> stage) list) = map fst cfs' \<Longrightarrow>
      flow_aux (map fst cfs' @ map fst cfs'') =
      flow_aux (map fst cfs') @ flow_aux (map fst cfs'')"
  shows "flow_aux (c # map fst cfs @ map fst cfs'') =
    flow_aux (c # map fst cfs) @ flow_aux (map fst cfs'')"
using A [of "(c, \<lambda>x. 0, \<lambda>x n. 0, [], []) # cfs"] by simp

lemma flow_append:
 "flow (cfs @ cfs') = flow cfs @ flow cfs'"
by (simp add: flow_def, induction "map fst cfs" arbitrary: cfs
 rule: flow_aux.induct, auto, rule flow_append_1)

lemma flow_cons:
 "flow (cf # cfs) = flow_aux (fst cf # []) @ flow cfs"
by (subgoal_tac "cf # cfs = [cf] @ cfs", simp only: flow_append,
 simp_all add: flow_def)


lemma in_flow_length:
 "length [p\<leftarrow>in_flow cs vs f. fst p = x] = length [c\<leftarrow>cs. c = IN x]"
by (induction cs vs f rule: in_flow.induct, simp_all)

lemma in_flow_append:
 "in_flow (cs @ cs') vs f =
    in_flow cs vs f @ in_flow cs' (vs @ in_flow cs vs f) f"
by (induction cs' vs f rule: in_flow.induct,
 (simp only: append_assoc [symmetric] in_flow.simps,
 simp add: in_flow_length ac_simps)+)

lemma in_flow_one:
 "in_flow [c] vs f = (case c of
    IN x \<Rightarrow> [(x, f x (length [p\<leftarrow>vs. fst p = x]))] | _ \<Rightarrow> [])"
by (subst append_Nil [symmetric], cases c, simp_all only: in_flow.simps,
 simp_all)


lemma run_flow_append:
 "run_flow (cs @ cs') vs s f =
    run_flow cs' (vs @ in_flow cs vs f) (run_flow cs vs s f) f"
by (induction cs' vs s f rule: run_flow.induct,
 (simp only: append_assoc [symmetric] run_flow.simps,
 simp add: in_flow_length ac_simps)+)

lemma run_flow_one:
 "run_flow [c] vs s f = (case c of
    x ::= a \<Rightarrow> s(x := aval a s) |
    IN x \<Rightarrow> s(x := f x (length [p\<leftarrow>vs. fst p = x])) |
    _ \<Rightarrow> s)"
by (subst append_Nil [symmetric], cases c, simp_all only: run_flow.simps,
 simp_all)

lemma run_flow_observe:
 "run_flow (\<langle>X\<rangle> # cs) vs s f = run_flow cs vs s f"
  apply (rule subst [of "([] @ [\<langle>X\<rangle>]) @ cs" _
   "\<lambda>cs'. run_flow cs' vs s f = run_flow cs vs s f"])
   apply fastforce
by (subst run_flow_append, simp only: in_flow.simps run_flow.simps, simp)


lemma out_flow_append:
 "out_flow (cs @ cs') vs s f =
    out_flow cs vs s f @
    out_flow cs' (vs @ in_flow cs vs f) (run_flow cs vs s f) f"
by (induction cs' vs s f rule: out_flow.induct,
 (simp only: append_assoc [symmetric] out_flow.simps,
 simp add: run_flow_append)+)

lemma out_flow_one:
 "out_flow [c] vs s f = (case c of
    OUT x \<Rightarrow> [(x, s x)] | _ \<Rightarrow> [])"
by (subst append_Nil [symmetric], cases c, simp_all only: out_flow.simps,
 simp_all)


lemma no_upd_empty:
 "no_upd cs {}"
by (induction cs "{} :: vname set" rule: no_upd.induct, simp_all)

lemma no_upd_append:
 "no_upd (cs @ cs') X = (no_upd cs X \<and> no_upd cs' X)"
by (induction cs X rule: no_upd.induct, simp_all)

lemma no_upd_in_flow:
 "no_upd cs X \<Longrightarrow> [p\<leftarrow>in_flow cs vs f. fst p \<in> X] = []"
by (induction cs vs f rule: in_flow.induct, simp_all add: no_upd_append)

lemma no_upd_run_flow:
 "no_upd cs X \<Longrightarrow> run_flow cs vs s f = s (\<subseteq> X)"
by (induction cs vs s f rule: run_flow.induct, auto simp: Let_def no_upd_append)

lemma no_upd_out_flow:
 "no_upd cs X \<Longrightarrow> [p\<leftarrow>out_flow cs vs s f. fst p \<in> X] = []"
by (induction cs vs s f rule: out_flow.induct, simp_all add: no_upd_append)


lemma small_stepsl_append:
 "\<lbrakk>cf \<rightarrow>*{cfs} cf'; cf' \<rightarrow>*{cfs'} cf''\<rbrakk> \<Longrightarrow> cf \<rightarrow>*{cfs @ cfs'} cf''"
by (induction cf' cfs' cf'' rule: small_stepsl.induct, simp,
 simp only: append_assoc [symmetric] small_stepsl.simps)

lemma small_step_stream:
 "(c, s, f, vs, ws) \<rightarrow> (c', p) \<Longrightarrow> \<exists>s' vs' ws'. p = (s', f, vs', ws')"
by (induction "(c, s, f, vs, ws)" "(c', p)" arbitrary: c s f vs ws c' p
 rule: small_step.induct, simp_all)

lemma small_stepsl_stream:
 "(c, s, f, vs, ws) \<rightarrow>*{cfs} (c', p) \<Longrightarrow> \<exists>s' vs' ws'. p = (s', f, vs', ws')"
by (induction "(c, s, f, vs, ws)" cfs "(c', p)" arbitrary: c s f vs ws c' p
 rule: small_stepsl.induct, auto dest: small_step_stream)


lemma small_steps_stepsl_1:
 "\<exists>cfs. cf \<rightarrow>*{cfs} cf"
by (rule exI [of _ "[]"], simp)

lemma small_steps_stepsl_2:
 "\<lbrakk>cf \<rightarrow> cf'; cf' \<rightarrow>*{cfs} cf''\<rbrakk> \<Longrightarrow> \<exists>cfs'. cf \<rightarrow>*{cfs'} cf''"
by (rule exI [of _ "[cf] @ cfs"], rule small_stepsl_append,
 subst append_Nil [symmetric], simp only: small_stepsl.simps)

lemma small_steps_stepsl:
 "cf \<rightarrow>* cf' \<Longrightarrow> \<exists>cfs. cf \<rightarrow>*{cfs} cf'"
by (induction cf cf' rule: star.induct, rule small_steps_stepsl_1,
 blast intro: small_steps_stepsl_2)

lemma small_stepsl_steps:
 "cf \<rightarrow>*{cfs} cf' \<Longrightarrow> cf \<rightarrow>* cf'"
by (induction cf cfs cf' rule: small_stepsl.induct, auto intro: star_trans)

lemma small_steps_stream:
 "(c, s, f, vs, ws) \<rightarrow>* (c', p) \<Longrightarrow> \<exists>s' vs' ws'. p = (s', f, vs', ws')"
by (blast dest: small_steps_stepsl intro: small_stepsl_stream)


lemma small_stepsl_cons_1:
 "cf \<rightarrow>*{[cf']} cf'' \<Longrightarrow> cf' = cf \<and> (\<exists>cf'. cf \<rightarrow> cf' \<and> cf' \<rightarrow>*{[]} cf'')"
by (subst (asm) append_Nil [symmetric], simp only: small_stepsl.simps,
 cases cf'', simp)

lemma small_stepsl_cons_2:
 "\<lbrakk>cf \<rightarrow>*{cf' # cfs} cf'' \<Longrightarrow>
    cf' = cf \<and> (\<exists>cf'. cf \<rightarrow> cf' \<and> cf' \<rightarrow>*{cfs} cf'');
  cf \<rightarrow>*{cf' # cfs @ [cf'']} cf'''\<rbrakk> \<Longrightarrow>
    cf' = cf \<and> (\<exists>cf'. cf \<rightarrow> cf' \<and> cf' \<rightarrow>*{cfs @ [cf'']} cf''')"
by (simp only: append_Cons [symmetric], simp only: small_stepsl.simps, simp)

lemma small_stepsl_cons:
 "cf \<rightarrow>*{cf' # cfs} cf'' \<Longrightarrow>
    cf' = cf \<and>
    (\<exists>cf'. cf \<rightarrow> cf' \<and> cf' \<rightarrow>*{cfs} cf'')"
by (induction cf cfs cf'' rule: small_stepsl.induct,
 erule small_stepsl_cons_1, rule small_stepsl_cons_2)


lemma small_stepsl_skip:
 "(SKIP, p) \<rightarrow>*{cfs} cf \<Longrightarrow> cf = (SKIP, p) \<and> flow cfs = []"
by (induction "(SKIP, p)" cfs cf rule: small_stepsl.induct,
 auto simp: flow_def)

lemma small_stepsl_assign:
 "(x ::= a, s, p) \<rightarrow>*{cfs} cf \<Longrightarrow>
    cf = (x ::= a, s, p) \<and>
      flow cfs = [] \<or>
    cf = (SKIP, s(x := aval a s), p) \<and>
      flow cfs = [x ::= a]"
by (induction "(x ::= a :: com, s, p)" cfs cf rule: small_stepsl.induct,
 force simp: flow_def, auto simp: flow_append, simp_all add: flow_def)

lemma small_stepsl_input:
 "(IN x, s, f, vs, ws) \<rightarrow>*{cfs} cf \<Longrightarrow>
    cf = (IN x, s, f, vs, ws) \<and>
      flow cfs = [] \<or>
   (let n = length [p\<leftarrow>vs. fst p = x]
    in cf = (SKIP, s(x := f x n), f, vs @ [(x, f x n)], ws) \<and>
      flow cfs = [IN x])"
by (induction "(IN x :: com, s, f, vs, ws)" cfs cf rule:
 small_stepsl.induct, force simp: flow_def, auto simp: Let_def flow_append,
 simp_all add: flow_def)

lemma small_stepsl_output:
 "(OUT x, s, f, vs, ws) \<rightarrow>*{cfs} cf \<Longrightarrow>
    cf = (OUT x, s, f, vs, ws) \<and>
      flow cfs = [] \<or>
    cf = (SKIP, s, f, vs, ws @ [(x, s x)]) \<and>
      flow cfs = [OUT x]"
by (induction "(OUT x :: com, s, f, vs, ws)" cfs cf rule:
 small_stepsl.induct, force simp: flow_def, auto simp: flow_append,
 simp_all add: flow_def)


lemma small_stepsl_seq_1:
 "(c\<^sub>1;; c\<^sub>2, p) \<rightarrow>*{[]} (c, q) \<Longrightarrow>
    (\<exists>c' cfs'. c = c';; c\<^sub>2 \<and>
      (c\<^sub>1, p) \<rightarrow>*{cfs'} (c', q) \<and>
      flow [] = flow cfs') \<or>
    (\<exists>p' cfs' cfs''. length cfs'' < length [] \<and>
      (c\<^sub>1, p) \<rightarrow>*{cfs'} (SKIP, p') \<and>
      (c\<^sub>2, p') \<rightarrow>*{cfs''} (c, q) \<and>
      flow [] = flow cfs' @ flow cfs'')"
by force

lemma small_stepsl_seq_2:
  assumes A: "\<And>c' q'. cf = (c', q') \<Longrightarrow>
    (c\<^sub>1;; c\<^sub>2, p) \<rightarrow>*{cfs} (c', q') \<Longrightarrow>
      (\<exists>c'' cfs'. c' = c'';; c\<^sub>2 \<and>
        (c\<^sub>1, p) \<rightarrow>*{cfs'} (c'', q') \<and>
        flow cfs = flow cfs') \<or>
      (\<exists>p' cfs' cfs''. length cfs'' < length cfs \<and>
        (c\<^sub>1, p) \<rightarrow>*{cfs'} (SKIP, p') \<and>
        (c\<^sub>2, p') \<rightarrow>*{cfs''} (c', q') \<and>
        flow cfs = flow cfs' @ flow cfs'')"
    (is "\<And>c' q'. _ \<Longrightarrow> _ \<Longrightarrow>
      (\<exists>c'' cfs'. ?P c' q' c'' cfs') \<or>
      (\<exists>p' cfs' cfs''. ?Q c' q' p' cfs' cfs'')")
  assumes B: "(c\<^sub>1;; c\<^sub>2, p) \<rightarrow>*{cfs @ [cf]} (c, q)"
  shows
   "(\<exists>c' cfs'. c = c';; c\<^sub>2 \<and>
      (c\<^sub>1, p) \<rightarrow>*{cfs'} (c', q) \<and>
      flow (cfs @ [cf]) = flow cfs') \<or>
    (\<exists>p' cfs' cfs''. length cfs'' < length (cfs @ [cf]) \<and>
      (c\<^sub>1, p) \<rightarrow>*{cfs'} (SKIP, p') \<and>
      (c\<^sub>2, p') \<rightarrow>*{cfs''} (c, q) \<and>
      flow (cfs @ [cf]) = flow cfs' @ flow cfs'')"
    (is "?T \<or> ?U")
proof (cases cf)
  fix c' q'
  assume C: "cf = (c', q')"
  moreover {
    assume D: "(c', q') \<rightarrow> (c, q)"
    assume
     "(\<exists>c'' cfs'. ?P c' q' c'' cfs') \<or>
      (\<exists>p' cfs' cfs''. ?Q c' q' p' cfs' cfs'')"
    hence ?thesis
    proof
      assume "\<exists>c'' cfs'. ?P c' q' c'' cfs'"
      then obtain c'' and cfs' where
        E: "c' = c'';; c\<^sub>2" and
        F: "(c\<^sub>1, p) \<rightarrow>*{cfs'} (c'', q')" and
        G: "flow cfs = flow cfs'"
        by blast
      hence "(c'';; c\<^sub>2, q') \<rightarrow> (c, q)"
        using D by simp
      moreover {
        assume
          H: "c'' = SKIP" and
          I: "(c, q) = (c\<^sub>2, q')"
        have ?U
        proof (rule exI [of _ q'], rule exI [of _ cfs'],
         rule exI [of _ "[]"])
          from C and E and F and G and H and I show
           "length [] < length (cfs @ [cf]) \<and>
            (c\<^sub>1, p) \<rightarrow>*{cfs'} (SKIP, q') \<and>
            (c\<^sub>2, q') \<rightarrow>*{[]} (c, q) \<and>
            flow (cfs @ [cf]) = flow cfs' @ flow []"
            by (simp add: flow_append, simp add: flow_def)
        qed
      }
      moreover {
        fix d q''
        assume
          H: "(c'', q') \<rightarrow> (d, q'')" and
          I: "(c, q) = (d;; c\<^sub>2, q'')"
        have ?T
        proof (rule exI [of _ d],
         rule exI [of _ "cfs' @ [(c'', q')]"])
          from C and E and F and G and H and I show
           "c = d;; c\<^sub>2 \<and>
            (c\<^sub>1, p) \<rightarrow>*{cfs' @ [(c'', q')]} (d, q) \<and>
            flow (cfs @ [cf]) = flow (cfs' @ [(c'', q')])"
            by (simp add: flow_append, simp add: flow_def)
        qed
      }
      ultimately show ?thesis
        by blast
    next
      assume "\<exists>p' cfs' cfs''. ?Q c' q' p' cfs' cfs''"
      then obtain p' and cfs' and cfs'' where
        E: "length cfs'' < length cfs" and
        F: "(c\<^sub>1, p) \<rightarrow>*{cfs'} (SKIP, p')" and
        G: "(c\<^sub>2, p') \<rightarrow>*{cfs''} (c', q')" and
        H: "flow cfs = flow cfs' @ flow cfs''"
        by blast
      show ?thesis
      proof (rule disjI2, rule exI [of _ p'], rule exI [of _ cfs'],
       rule exI [of _ "cfs'' @ [(c', q')]"])
        from C and D and E and F and G and H show
         "length (cfs'' @ [(c', q')]) < length (cfs @ [cf]) \<and>
          (c\<^sub>1, p) \<rightarrow>*{cfs'} (SKIP, p') \<and>
          (c\<^sub>2, p') \<rightarrow>*{cfs'' @ [(c', q')]} (c, q) \<and>
          flow (cfs @ [cf]) = flow cfs' @ flow (cfs'' @ [(c', q')])"
          by (simp add: flow_append)
      qed
    qed
  }
  ultimately show ?thesis
    using A and B by simp
qed

lemma small_stepsl_seq:
 "(c\<^sub>1;; c\<^sub>2, p) \<rightarrow>*{cfs} (c, q) \<Longrightarrow>
    (\<exists>c' cfs'. c = c';; c\<^sub>2 \<and>
      (c\<^sub>1, p) \<rightarrow>*{cfs'} (c', q) \<and>
      flow cfs = flow cfs') \<or>
    (\<exists>p' cfs' cfs''. length cfs'' < length cfs \<and>
      (c\<^sub>1, p) \<rightarrow>*{cfs'} (SKIP, p') \<and> (c\<^sub>2, p') \<rightarrow>*{cfs''} (c, q) \<and>
      flow cfs = flow cfs' @ flow cfs'')"
by (induction "(c\<^sub>1;; c\<^sub>2, p)" cfs "(c, q)" arbitrary: c\<^sub>1 c\<^sub>2 p c q
 rule: small_stepsl.induct, erule small_stepsl_seq_1,
 rule small_stepsl_seq_2)


lemma small_stepsl_or_1:
  assumes A: "(c\<^sub>1 OR c\<^sub>2, p) \<rightarrow>*{cfs} cf \<Longrightarrow>
    cf = (c\<^sub>1 OR c\<^sub>2, p) \<and>
      flow cfs = [] \<or>
    (c\<^sub>1, p) \<rightarrow>*{tl cfs} cf \<and>
      flow cfs = flow (tl cfs) \<or>
    (c\<^sub>2, p) \<rightarrow>*{tl cfs} cf \<and>
      flow cfs = flow (tl cfs)"
    (is "_ \<Longrightarrow> ?P \<or> ?Q \<or> ?R")
  assumes B: "(c\<^sub>1 OR c\<^sub>2, p) \<rightarrow>*{cfs @ [cf]} cf'"
  shows
   "cf' = (c\<^sub>1 OR c\<^sub>2, p) \<and>
      flow (cfs @ [cf]) = [] \<or>
    (c\<^sub>1, p) \<rightarrow>*{tl (cfs @ [cf])} cf' \<and>
      flow (cfs @ [cf]) = flow (tl (cfs @ [cf])) \<or>
    (c\<^sub>2, p) \<rightarrow>*{tl (cfs @ [cf])} cf' \<and>
      flow (cfs @ [cf]) = flow (tl (cfs @ [cf]))"
    (is "_ \<or> ?T")
proof -
  {
    assume
      C: "(c\<^sub>1 OR c\<^sub>2, p) \<rightarrow>*{cfs} cf" and
      D: "cf \<rightarrow> cf'"
    assume "?P \<or> ?Q \<or> ?R"
    hence ?T
    proof (rule disjE, erule_tac [2] disjE)
      assume ?P
      moreover from this have "(c\<^sub>1 OR c\<^sub>2, p) \<rightarrow> cf'"
        using D by simp
      ultimately show ?thesis
        using C by (auto dest: small_stepsl_cons
         simp: tl_append flow_cons split: list.split)
    next
      assume ?Q
      with C and D show ?thesis
        by (auto simp: tl_append flow_cons split: list.split)
    next
      assume ?R
      with C and D show ?thesis
        by (auto simp: tl_append flow_cons split: list.split)
    qed
  }
  with A and B show ?thesis
    by simp
qed

lemma small_stepsl_or:
 "(c\<^sub>1 OR c\<^sub>2, p) \<rightarrow>*{cfs} cf \<Longrightarrow>
    cf = (c\<^sub>1 OR c\<^sub>2, p) \<and>
      flow cfs = [] \<or>
    (c\<^sub>1, p) \<rightarrow>*{tl cfs} cf \<and>
      flow cfs = flow (tl cfs) \<or>
    (c\<^sub>2, p) \<rightarrow>*{tl cfs} cf \<and>
      flow cfs = flow (tl cfs)"
by (induction "(c\<^sub>1 OR c\<^sub>2, p)" cfs cf rule: small_stepsl.induct,
 force simp: flow_def, rule small_stepsl_or_1)


lemma small_stepsl_if_1:
  assumes A: "(IF b THEN c\<^sub>1 ELSE c\<^sub>2, s, p) \<rightarrow>*{cfs} cf \<Longrightarrow>
    cf = (IF b THEN c\<^sub>1 ELSE c\<^sub>2, s, p) \<and>
      flow cfs = [] \<or>
    bval b s \<and> (c\<^sub>1, s, p) \<rightarrow>*{tl cfs} cf \<and>
      flow cfs = \<langle>bvars b\<rangle> # flow (tl cfs) \<or>
    \<not> bval b s \<and> (c\<^sub>2, s, p) \<rightarrow>*{tl cfs} cf \<and>
      flow cfs = \<langle>bvars b\<rangle> # flow (tl cfs)"
    (is "_ \<Longrightarrow> ?P \<or> ?Q \<or> ?R")
  assumes B: "(IF b THEN c\<^sub>1 ELSE c\<^sub>2, s, p) \<rightarrow>*{cfs @ [cf]} cf'"
  shows
   "cf' = (IF b THEN c\<^sub>1 ELSE c\<^sub>2, s, p) \<and>
      flow (cfs @ [cf]) = [] \<or>
    bval b s \<and> (c\<^sub>1, s, p) \<rightarrow>*{tl (cfs @ [cf])} cf' \<and>
      flow (cfs @ [cf]) = \<langle>bvars b\<rangle> # flow (tl (cfs @ [cf])) \<or>
    \<not> bval b s \<and> (c\<^sub>2, s, p) \<rightarrow>*{tl (cfs @ [cf])} cf' \<and>
      flow (cfs @ [cf]) = \<langle>bvars b\<rangle> # flow (tl (cfs @ [cf]))"
    (is "_ \<or> ?T")
proof -
  {
    assume
      C: "(IF b THEN c\<^sub>1 ELSE c\<^sub>2, s, p) \<rightarrow>*{cfs} cf" and
      D: "cf \<rightarrow> cf'"
    assume "?P \<or> ?Q \<or> ?R"
    hence ?T
    proof (rule disjE, erule_tac [2] disjE)
      assume ?P
      moreover from this have "(IF b THEN c\<^sub>1 ELSE c\<^sub>2, s, p) \<rightarrow> cf'"
        using D by simp
      ultimately show ?thesis
        using C by (auto dest: small_stepsl_cons
         simp: tl_append flow_cons split: list.split)
    next
      assume ?Q
      with D show ?thesis
        by (auto simp: tl_append flow_cons split: list.split)
    next
      assume ?R
      with D show ?thesis
        by (auto simp: tl_append flow_cons split: list.split)
    qed
  }
  with A and B show ?thesis
    by simp
qed

lemma small_stepsl_if:
 "(IF b THEN c\<^sub>1 ELSE c\<^sub>2, s, p) \<rightarrow>*{cfs} cf \<Longrightarrow>
    cf = (IF b THEN c\<^sub>1 ELSE c\<^sub>2, s, p) \<and>
      flow cfs = [] \<or>
    bval b s \<and> (c\<^sub>1, s, p) \<rightarrow>*{tl cfs} cf \<and>
      flow cfs = \<langle>bvars b\<rangle> # flow (tl cfs) \<or>
    \<not> bval b s \<and> (c\<^sub>2, s, p) \<rightarrow>*{tl cfs} cf \<and>
      flow cfs = \<langle>bvars b\<rangle> # flow (tl cfs)"
by (induction "(IF b THEN c\<^sub>1 ELSE c\<^sub>2, s, p)" cfs cf rule:
 small_stepsl.induct, force simp: flow_def, rule small_stepsl_if_1)


lemma small_stepsl_while_1:
  assumes A: "(WHILE b DO c, s, p) \<rightarrow>*{cfs} cf \<Longrightarrow>
    cf = (WHILE b DO c, s, p) \<and>
      flow cfs = [] \<or>
    bval b s \<and> (c;; WHILE b DO c, s, p) \<rightarrow>*{tl cfs} cf \<and>
      flow cfs = \<langle>bvars b\<rangle> # flow (tl cfs) \<or>
    \<not> bval b s \<and> cf = (SKIP, s, p) \<and>
      flow cfs = [\<langle>bvars b\<rangle>]"
    (is "_ \<Longrightarrow> ?P \<or> ?Q \<or> ?R")
  assumes B: "(WHILE b DO c, s, p) \<rightarrow>*{cfs @ [cf]} cf'"
  shows
   "cf' = (WHILE b DO c, s, p) \<and>
      flow (cfs @ [cf]) = [] \<or>
    bval b s \<and> (c;; WHILE b DO c, s, p) \<rightarrow>*{tl (cfs @ [cf])} cf' \<and>
      flow (cfs @ [cf]) = \<langle>bvars b\<rangle> # flow (tl (cfs @ [cf])) \<or>
    \<not> bval b s \<and> cf' = (SKIP, s, p) \<and>
      flow (cfs @ [cf]) = [\<langle>bvars b\<rangle>]"
    (is "_ \<or> ?T")
proof -
  {
    assume
      C: "(WHILE b DO c, s, p) \<rightarrow>*{cfs} cf" and
      D: "cf \<rightarrow> cf'"
    assume "?P \<or> ?Q \<or> ?R"
    hence ?T
    proof (rule disjE, erule_tac [2] disjE)
      assume ?P
      moreover from this have "(WHILE b DO c, s, p) \<rightarrow> cf'"
        using D by simp
      ultimately show ?thesis
        using C by (auto dest: small_stepsl_cons
         simp: tl_append flow_cons split: list.split)
    next
      assume ?Q
      with D show ?thesis
        by (auto simp: tl_append flow_cons split: list.split)
    next
      assume ?R
      with D show ?thesis
        by blast
    qed
  }
  with A and B show ?thesis
    by simp
qed

lemma small_stepsl_while:
 "(WHILE b DO c, s, p) \<rightarrow>*{cfs} cf \<Longrightarrow>
    cf = (WHILE b DO c, s, p) \<and>
      flow cfs = [] \<or>
    bval b s \<and> (c;; WHILE b DO c, s, p) \<rightarrow>*{tl cfs} cf \<and>
      flow cfs = \<langle>bvars b\<rangle> # flow (tl cfs) \<or>
    \<not> bval b s \<and> cf = (SKIP, s, p) \<and>
      flow cfs = [\<langle>bvars b\<rangle>]"
by (induction "(WHILE b DO c, s, p)" cfs cf rule: small_stepsl.induct,
 force simp: flow_def, rule small_stepsl_while_1)


lemma small_steps_in_flow_1:
 "\<lbrakk>(c, s, f, vs, ws) \<rightarrow> (c', s', f', vs', ws');
    vs'' = vs' @ drop (length vs') vs''\<rbrakk> \<Longrightarrow>
  vs'' = vs @ drop (length vs) vs''"
by (induction "(c, s, f, vs, ws)" "(c', s', f', vs', ws')"
 arbitrary: c c' s s' f f' vs vs' ws ws' rule: small_step.induct,
 auto elim: ssubst)

lemma small_steps_in_flow:
 "(c, s, f, vs, ws) \<rightarrow>* (c', s', f', vs', ws') \<Longrightarrow>
    vs' = vs @ drop (length vs) vs'"
by (induction "(c, s, f, vs, ws)" "(c', s', f', vs', ws')"
 arbitrary: c c' s s' f f' vs vs' ws ws' rule: star.induct,
 auto intro: small_steps_in_flow_1)


lemma small_steps_out_flow_1:
 "\<lbrakk>(c, s, f, vs, ws) \<rightarrow> (c', s', f', vs', ws');
    ws'' = ws' @ drop (length ws') ws''\<rbrakk> \<Longrightarrow>
  ws'' = ws @ drop (length ws) ws''"
by (induction "(c, s, f, vs, ws)" "(c', s', f', vs', ws')"
 arbitrary: c c' s s' f f' vs vs' ws ws' rule: small_step.induct,
 auto elim: ssubst)

lemma small_steps_out_flow:
 "(c, s, f, vs, ws) \<rightarrow>* (c', s', f', vs', ws') \<Longrightarrow>
    ws' = ws @ drop (length ws) ws'"
by (induction "(c, s, f, vs, ws)" "(c', s', f', vs', ws')"
 arbitrary: c c' s s' f f' vs vs' ws ws' rule: star.induct,
 auto intro: small_steps_out_flow_1)


lemma small_stepsl_in_flow_1:
  assumes
    A: "(c, s, f, vs, ws) \<rightarrow>*{cfs} (c', s', f', vs @ vs', ws')" and
    B: "(c', s', f', vs @ vs', ws') \<rightarrow> (c'', s'', f'', vs'', ws'')"
  shows "vs'' = vs @ vs' @
    in_flow (flow [(c', s', f', vs @ vs', ws')]) (vs @ vs') f"
using small_stepsl_stream [OF A] and B
by (induction "[c']" arbitrary: c' c'' rule: flow_aux.induct,
 auto simp: flow_def in_flow_one)

lemma small_stepsl_in_flow:
 "(c, s, f, vs, ws) \<rightarrow>*{cfs} (c', s', f', vs', ws') \<Longrightarrow>
    vs' = vs @ in_flow (flow cfs) vs f"
by (induction "(c, s, f, vs, ws)" cfs "(c', s', f', vs', ws')"
 arbitrary: c' s' f' vs' ws' rule: small_stepsl.induct, simp add: flow_def,
 auto intro: small_stepsl_in_flow_1 simp: flow_append in_flow_append)


lemma small_stepsl_run_flow_1:
  assumes
    A: "(c, s, f, vs, ws) \<rightarrow>*{cfs}
      (c', run_flow (flow cfs) vs s f, f', vs', ws')" and
    B: "(c', run_flow (flow cfs) vs s f, f', vs', ws') \<rightarrow>
      (c'', s'', f'', vs'', ws'')"
  shows "s'' = run_flow (flow [(c', run_flow (flow cfs) vs s f, f', vs', ws')])
    (vs @ in_flow (flow cfs) vs f) (run_flow (flow cfs) vs s f) f"
using small_stepsl_stream [OF A] and small_stepsl_in_flow [OF A] and B
by (induction "[c']" arbitrary: c' c'' rule: flow_aux.induct,
 auto simp: flow_def run_flow_one)

lemma small_stepsl_run_flow:
 "(c, s, f, vs, ws) \<rightarrow>*{cfs} (c', s', f', vs', ws') \<Longrightarrow>
    s' = run_flow (flow cfs) vs s f"
by (induction "(c, s, f, vs, ws)" cfs "(c', s', f', vs', ws')"
 arbitrary: c' s' f' vs' ws' rule: small_stepsl.induct, simp add: flow_def,
 auto intro: small_stepsl_run_flow_1 simp: flow_append run_flow_append)


lemma small_stepsl_out_flow_1:
  assumes
    A: "(c, s, f, vs, ws) \<rightarrow>*{cfs} (c', s', f', vs', ws @ ws')" and
    B: "(c', s', f', vs', ws @ ws') \<rightarrow> (c'', s'', f'', vs'', ws'')"
  shows "ws'' = ws @ ws' @
    out_flow (flow [(c', s', f', vs', ws @ ws')]) (vs @ in_flow (flow cfs) vs f)
      (run_flow (flow cfs) vs s f) f"
using small_stepsl_run_flow [OF A] and B
by (induction "[c']" arbitrary: c' c'' rule: flow_aux.induct,
 auto simp: flow_def out_flow_one)

lemma small_stepsl_out_flow:
 "(c, s, f, vs, ws) \<rightarrow>*{cfs} (c', s', f', vs', ws') \<Longrightarrow>
    ws' = ws @ out_flow (flow cfs) vs s f"
by (induction "(c, s, f, vs, ws)" cfs "(c', s', f', vs', ws')"
 arbitrary: c' s' f' vs' ws' rule: small_stepsl.induct, simp add: flow_def,
 auto intro: small_stepsl_out_flow_1 simp: flow_append out_flow_append)


lemma small_steps_inputs:
  assumes
    A: "(c, s, f, vs\<^sub>0, ws\<^sub>0) \<rightarrow>*{cfs\<^sub>1} (c\<^sub>0, s\<^sub>1, f, vs\<^sub>1, ws\<^sub>1)" and
    B: "(c\<^sub>1, s\<^sub>1, f, vs\<^sub>1, ws\<^sub>1) \<rightarrow>*{cfs\<^sub>2} (c\<^sub>2, s\<^sub>2, f, vs\<^sub>2, ws\<^sub>2)" and
    C: "(c, s', f', vs\<^sub>0', ws\<^sub>0') \<rightarrow>* (c\<^sub>0', s\<^sub>1', f', vs\<^sub>1', ws\<^sub>1')" and
    D: "(c\<^sub>1', s\<^sub>1', f', vs\<^sub>1', ws\<^sub>1') \<rightarrow>* (c\<^sub>2', s\<^sub>2', f', vs\<^sub>2', ws\<^sub>2')" and
    E: "map fst [p\<leftarrow>drop (length vs\<^sub>0) vs\<^sub>1. P p] =
      map fst [p\<leftarrow>drop (length vs\<^sub>0') vs\<^sub>1'. P p]" and
    F: "map fst [p\<leftarrow>drop (length vs\<^sub>1) vs\<^sub>2. P p] =
      map fst [p\<leftarrow>drop (length vs\<^sub>1') vs\<^sub>2'. P p]"
  shows "map fst [p\<leftarrow>drop (length vs\<^sub>0) vs\<^sub>2. P p] =
    map fst [p\<leftarrow>drop (length vs\<^sub>0') vs\<^sub>2'. P p]"
proof -
  have G: "vs\<^sub>1 = vs\<^sub>0 @ drop (length vs\<^sub>0) vs\<^sub>1"
    using small_stepsl_steps [OF A] by (rule small_steps_in_flow)
  have "vs\<^sub>2 = vs\<^sub>1 @ drop (length vs\<^sub>1) vs\<^sub>2"
    using small_stepsl_steps [OF B] by (rule small_steps_in_flow)
  hence H: "vs\<^sub>2 = vs\<^sub>0 @ drop (length vs\<^sub>0) vs\<^sub>1 @ drop (length vs\<^sub>1) vs\<^sub>2"
    by (subst (asm) G, simp)
  have I: "vs\<^sub>1' = vs\<^sub>0' @ drop (length vs\<^sub>0') vs\<^sub>1'"
    using C by (rule small_steps_in_flow)
  have "vs\<^sub>2' = vs\<^sub>1' @ drop (length vs\<^sub>1') vs\<^sub>2'"
    using D by (rule small_steps_in_flow)
  hence J: "vs\<^sub>2' = vs\<^sub>0' @ drop (length vs\<^sub>0') vs\<^sub>1' @ drop (length vs\<^sub>1') vs\<^sub>2'"
    by (subst (asm) I, simp)
  from E and F show ?thesis
    by (subst H, subst J, simp)
qed

lemma small_steps_outputs:
  assumes
    A: "(c, s, f, vs\<^sub>0, ws\<^sub>0) \<rightarrow>*{cfs\<^sub>1} (c\<^sub>0, s\<^sub>1, f, vs\<^sub>1, ws\<^sub>1)" and
    B: "(c\<^sub>1, s\<^sub>1, f, vs\<^sub>1, ws\<^sub>1) \<rightarrow>*{cfs\<^sub>2} (c\<^sub>2, s\<^sub>2, f, vs\<^sub>2, ws\<^sub>2)" and
    C: "(c, s', f', vs\<^sub>0', ws\<^sub>0') \<rightarrow>* (c\<^sub>0', s\<^sub>1', f', vs\<^sub>1', ws\<^sub>1')" and
    D: "(c\<^sub>1', s\<^sub>1', f', vs\<^sub>1', ws\<^sub>1') \<rightarrow>* (c\<^sub>2', s\<^sub>2', f', vs\<^sub>2', ws\<^sub>2')" and
    E: "[p\<leftarrow>drop (length ws\<^sub>0) ws\<^sub>1. P p] =
      [p\<leftarrow>drop (length ws\<^sub>0') ws\<^sub>1'. P p]" and
    F: "[p\<leftarrow>drop (length ws\<^sub>1) ws\<^sub>2. P p] =
      [p\<leftarrow>drop (length ws\<^sub>1') ws\<^sub>2'. P p]"
  shows "[p\<leftarrow>drop (length ws\<^sub>0) ws\<^sub>2. P p] =
    [p\<leftarrow>drop (length ws\<^sub>0') ws\<^sub>2'. P p]"
proof -
  have G: "ws\<^sub>1 = ws\<^sub>0 @ drop (length ws\<^sub>0) ws\<^sub>1"
    using small_stepsl_steps [OF A] by (rule small_steps_out_flow)
  have "ws\<^sub>2 = ws\<^sub>1 @ drop (length ws\<^sub>1) ws\<^sub>2"
    using small_stepsl_steps [OF B] by (rule small_steps_out_flow)
  hence H: "ws\<^sub>2 = ws\<^sub>0 @ drop (length ws\<^sub>0) ws\<^sub>1 @ drop (length ws\<^sub>1) ws\<^sub>2"
    by (subst (asm) G, simp)
  have I: "ws\<^sub>1' = ws\<^sub>0' @ drop (length ws\<^sub>0') ws\<^sub>1'"
    using C by (rule small_steps_out_flow)
  have "ws\<^sub>2' = ws\<^sub>1' @ drop (length ws\<^sub>1') ws\<^sub>2'"
    using D by (rule small_steps_out_flow)
  hence J: "ws\<^sub>2' = ws\<^sub>0' @ drop (length ws\<^sub>0') ws\<^sub>1' @ drop (length ws\<^sub>1') ws\<^sub>2'"
    by (subst (asm) I, simp)
  from E and F show ?thesis
    by (subst H, subst J, simp)
qed


subsection "Local context proofs"

context noninterf
begin


lemma no_upd_sources:
 "no_upd cs X \<Longrightarrow> \<forall>x \<in> X. x \<in> sources cs vs s f x"
by (induction cs rule: rev_induct, auto simp: no_upd_append
 split: com_flow.split)

lemma sources_aux_append:
 "sources_aux cs vs s f x \<subseteq> sources_aux (cs @ cs') vs s f x"
by (induction cs' rule: rev_induct, simp, subst append_assoc [symmetric],
 auto simp del: append_assoc split: com_flow.split)

lemma sources_out_append:
 "sources_out cs vs s f x \<subseteq> sources_out (cs @ cs') vs s f x"
by (induction cs' rule: rev_induct, simp, subst append_assoc [symmetric],
 auto simp del: append_assoc split: com_flow.split)

lemma sources_aux_sources:
 "sources_aux cs vs s f x \<subseteq> sources cs vs s f x"
by (induction cs rule: rev_induct, auto split: com_flow.split)

lemma sources_aux_sources_out:
 "sources_aux cs vs s f x \<subseteq> sources_out cs vs s f x"
by (induction cs rule: rev_induct, auto split: com_flow.split)

lemma sources_aux_observe_hd_1:
 "\<forall>y \<in> X. s: dom y \<leadsto> dom x \<Longrightarrow> X \<subseteq> sources_aux [\<langle>X\<rangle>] vs s f x"
by (subst append_Nil [symmetric], subst sources_aux.simps, auto)

lemma sources_aux_observe_hd_2:
 "\<lbrakk>\<forall>y \<in> X. s: dom y \<leadsto> dom x \<Longrightarrow> X \<subseteq> sources_aux (\<langle>X\<rangle> # xs) vs s f x;
    \<forall>y \<in> X. s: dom y \<leadsto> dom x\<rbrakk> \<Longrightarrow>
  X \<subseteq> sources_aux (\<langle>X\<rangle> # xs @ [x']) vs s f x"
by (subst append_Cons [symmetric], subst sources_aux.simps,
 auto split: com_flow.split)

lemma sources_aux_observe_hd:
 "\<forall>y \<in> X. s: dom y \<leadsto> dom x \<Longrightarrow> X \<subseteq> sources_aux (\<langle>X\<rangle> # cs) vs s f x"
by (induction cs rule: rev_induct,
 erule sources_aux_observe_hd_1, rule sources_aux_observe_hd_2)

lemma sources_aux_bval:
  assumes
    A: "S \<subseteq> {x. s = t (\<subseteq> sources_aux (\<langle>bvars b\<rangle> # cs) vs s f x)}" and
    B: "s \<in> Univ A (\<subseteq> state \<inter> X)" and
    C: "bval b s \<noteq> bval b t"
  shows "Univ? A X: bvars b \<leadsto>| S"
proof -
  have "\<not> s = t (\<subseteq> bvars b)"
    using A and C by (erule_tac contrapos_nn, auto dest: bvars_bval)
  hence "\<forall>x \<in> S. \<not> bvars b \<subseteq> sources_aux (\<langle>bvars b\<rangle> # cs) vs s f x"
    using A by blast
  hence D: "{s}: bvars b \<leadsto>| S"
    by (fastforce dest: sources_aux_observe_hd)
  {
    fix r y
    assume "r \<in> A" and "y \<in> S"
    moreover assume "s = r (\<subseteq> state \<inter> X)" and "state \<subseteq> X"
    hence "interf s = interf r"
      by (blast intro: interf_state)
    ultimately have "A: bvars b \<leadsto>| {y}"
      using D by fastforce
  }
  with B and D show ?thesis
    by (fastforce simp: univ_states_if_def)
qed

lemma ok_flow_aux_degen:
  assumes A: "\<nexists>S. S \<noteq> {} \<and> S \<subseteq> {x. s\<^sub>1 = t\<^sub>1 (\<subseteq> sources_aux cs vs\<^sub>1 s\<^sub>1 f x)}"
  shows "\<forall>c\<^sub>2' t\<^sub>2 vs\<^sub>2' ws\<^sub>2'.
    ok_flow_aux_1 c\<^sub>1 c\<^sub>2 c\<^sub>2' s\<^sub>1 t\<^sub>1 t\<^sub>2 f f' vs\<^sub>1 vs\<^sub>1' vs\<^sub>2 vs\<^sub>2' ws\<^sub>1' ws\<^sub>2' cs \<and>
    ok_flow_aux_2 s\<^sub>1 s\<^sub>2 t\<^sub>1 t\<^sub>2 f f' vs\<^sub>1 vs\<^sub>1' cs \<and>
    ok_flow_aux_3 s\<^sub>1 t\<^sub>1 f f' vs\<^sub>1 vs\<^sub>1' ws\<^sub>1 ws\<^sub>1' ws\<^sub>2 ws\<^sub>2' cs"
    (is "\<forall>c\<^sub>2' t\<^sub>2 vs\<^sub>2' ws\<^sub>2'. ?P1 c\<^sub>2' t\<^sub>2 vs\<^sub>2' ws\<^sub>2' \<and> ?P2 t\<^sub>2 \<and> ?P3 ws\<^sub>2'")
proof clarify
  fix c\<^sub>2' t\<^sub>2 vs\<^sub>2' ws\<^sub>2'
  {
    fix S
    assume "S \<noteq> {}" and "S \<subseteq> {x. s\<^sub>1 = t\<^sub>1 (\<subseteq> sources_aux cs vs\<^sub>1 s\<^sub>1 f x)}"
    hence "?P1 c\<^sub>2' t\<^sub>2 vs\<^sub>2' ws\<^sub>2'"
      using A by blast
  }
  moreover {
    fix S
    assume "S \<subseteq> {x. s\<^sub>1 = t\<^sub>1 (\<subseteq> sources cs vs\<^sub>1 s\<^sub>1 f x)}"
    moreover have "\<forall>x. sources_aux cs vs\<^sub>1 s\<^sub>1 f x \<subseteq> sources cs vs\<^sub>1 s\<^sub>1 f x"
      by (blast intro: subsetD [OF sources_aux_sources])
    ultimately have "S \<subseteq> {x. s\<^sub>1 = t\<^sub>1 (\<subseteq> sources_aux cs vs\<^sub>1 s\<^sub>1 f x)}"
      by blast
    moreover assume "S \<noteq> {}"
    ultimately have "?P2 t\<^sub>2"
      using A by blast
  }
  moreover {
    fix S
    assume "S \<subseteq> {x. s\<^sub>1 = t\<^sub>1 (\<subseteq> sources_out cs vs\<^sub>1 s\<^sub>1 f x)}"
    moreover have "\<forall>x. sources_aux cs vs\<^sub>1 s\<^sub>1 f x \<subseteq> sources_out cs vs\<^sub>1 s\<^sub>1 f x"
      by (blast intro: subsetD [OF sources_aux_sources_out])
    ultimately have "S \<subseteq> {x. s\<^sub>1 = t\<^sub>1 (\<subseteq> sources_aux cs vs\<^sub>1 s\<^sub>1 f x)}"
      by blast
    moreover assume "S \<noteq> {}"
    ultimately have "?P3 ws\<^sub>2'"
      using A by blast
  }
  ultimately show "?P1 c\<^sub>2' t\<^sub>2 vs\<^sub>2' ws\<^sub>2' \<and> ?P2 t\<^sub>2 \<and> ?P3 ws\<^sub>2'"
    by auto
qed


lemma tags_aux_append:
 "tags_aux cs vs s f x \<subseteq> tags_aux (cs @ cs') vs s f x"
by (induction cs' rule: rev_induct, simp, subst append_assoc [symmetric],
 auto simp del: append_assoc split: com_flow.split)

lemma tags_out_append:
 "tags_out cs vs s f x \<subseteq> tags_out (cs @ cs') vs s f x"
by (induction cs' rule: rev_induct, simp, subst append_assoc [symmetric],
 auto simp del: append_assoc split: com_flow.split)

lemma tags_aux_tags:
 "tags_aux cs vs s f x \<subseteq> tags cs vs s f x"
by (induction cs rule: rev_induct, auto split: com_flow.split)

lemma tags_aux_tags_out:
 "tags_aux cs vs s f x \<subseteq> tags_out cs vs s f x"
by (induction cs rule: rev_induct, auto split: com_flow.split)


lemma tags_ubound_1:
  assumes
    A: "(y, Suc (length [c\<leftarrow>cs. c = IN y] + n)) \<in> tags_aux cs vs s f x" and
    B: "\<And>z n. y = z \<Longrightarrow>
      (z, length [c\<leftarrow>cs. c = IN z] + n) \<notin> tags_aux cs vs s f x"
  shows False
proof -
  have "(y, length [c\<leftarrow>cs. c = IN y] + Suc n) \<notin> tags_aux cs vs s f x"
    using B by blast
  thus ?thesis
    using A by simp
qed

lemma tags_ubound_2:
  assumes
    A: "(y, Suc (length [c\<leftarrow>cs. c = IN y] + n)) \<in> tags cs vs s f x" and
    B: "\<And>z n. y = z \<Longrightarrow> z \<noteq> x \<Longrightarrow>
      (z, length [c\<leftarrow>cs. c = IN z] + n) \<notin> tags cs vs s f x" and
    C: "y \<noteq> x"
  shows False
proof -
  have "(y, length [c\<leftarrow>cs. c = IN y] + Suc n) \<notin> tags cs vs s f x"
    using B and C by blast
  thus ?thesis
    using A by simp
qed

lemma tags_ubound:
 "(y, length [c\<leftarrow>cs. c = IN y] + n) \<notin> tags cs vs s f x"
and tags_aux_ubound:
 "(y, length [c\<leftarrow>cs. c = IN y] + n) \<notin> tags_aux cs vs s f x"
by (induction cs vs s f x and cs vs s f x arbitrary: n and n
 rule: tags_induct, auto intro: tags_ubound_1 tags_ubound_2
 split: if_split_asm com_flow.split_asm)


lemma tags_out_ubound_1:
  assumes
    A: "(y, Suc (length [c\<leftarrow>cs. c = IN y] + n)) \<in> tags_out cs vs s f x" and
    B: "\<And>z n. y = z \<Longrightarrow>
      (z, length [c\<leftarrow>cs. c = IN z] + n) \<notin> tags_out cs vs s f x"
  shows False
proof -
  have "(y, length [c\<leftarrow>cs. c = IN y] + Suc n) \<notin> tags_out cs vs s f x"
    using B by blast
  thus ?thesis
    using A by simp
qed

lemma tags_out_ubound:
 "(y, length [c\<leftarrow>cs. c = IN y] + n) \<notin> tags_out cs vs s f x"
by (induction cs vs s f x arbitrary: n rule: tags_out.induct, auto
 intro: notE [OF tags_ubound] tags_out_ubound_1
 split: if_split_asm com_flow.split_asm)


lemma tags_less:
 "(y, n) \<in> tags cs vs s f x \<Longrightarrow> n < length [c\<leftarrow>cs. c = IN y]"
  apply (rule ccontr)
  apply (drule add_diff_inverse_nat)
  apply (drule ssubst, assumption)
by (simp add: tags_ubound)

lemma tags_aux_less:
 "(y, n) \<in> tags_aux cs vs s f x \<Longrightarrow> n < length [c\<leftarrow>cs. c = IN y]"
  apply (rule ccontr)
  apply (drule add_diff_inverse_nat)
  apply (drule ssubst, assumption)
by (simp add: tags_aux_ubound)

lemma tags_out_less:
 "(y, n) \<in> tags_out cs vs s f x \<Longrightarrow> n < length [c\<leftarrow>cs. c = IN y]"
  apply (rule ccontr)
  apply (drule add_diff_inverse_nat)
  apply (drule ssubst, assumption)
by (simp add: tags_out_ubound)


lemma sources_observe_tl_1:
  assumes
    A: "\<And>z a. c = (z ::= a :: com_flow) \<Longrightarrow> z = x \<Longrightarrow>
      sources_aux cs vs s f x \<subseteq> sources_aux (\<langle>X\<rangle> # cs) vs s f x" and
    B: "\<And>z a b w. c = (z ::= a :: com_flow) \<Longrightarrow> z = x \<Longrightarrow>
      sources cs vs s f w \<subseteq> sources (\<langle>X\<rangle> # cs) vs s f w" and
    C: "\<And>z a. c = (z ::= a :: com_flow) \<Longrightarrow> z \<noteq> x \<Longrightarrow>
      sources cs vs s f x \<subseteq> sources (\<langle>X\<rangle> # cs) vs s f x" and
    D: "\<And>z. c = (IN z :: com_flow) \<Longrightarrow> z = x \<Longrightarrow>
      sources_aux cs vs s f x \<subseteq> sources_aux (\<langle>X\<rangle> # cs) vs s f x" and
    E: "\<And>z. c = (IN z :: com_flow) \<Longrightarrow> z \<noteq> x \<Longrightarrow>
      sources cs vs s f x \<subseteq> sources (\<langle>X\<rangle> # cs) vs s f x" and
    F: "\<And>z. c = (OUT z :: com_flow) \<Longrightarrow>
      sources cs vs s f x \<subseteq> sources (\<langle>X\<rangle> # cs) vs s f x" and
    G: "\<And>Y b w. c = \<langle>Y\<rangle> \<Longrightarrow>
      sources cs vs s f w \<subseteq> sources (\<langle>X\<rangle> # cs) vs s f w"
  shows "sources (cs @ [c]) vs s f x \<subseteq> sources (\<langle>X\<rangle> # cs @ [c]) vs s f x"
    (is "_ \<subseteq> ?F c")
  apply (subst sources.simps)
  apply (split com_flow.split)
  apply (rule conjI)
  subgoal
  proof -
    show "\<forall>z a. c = z ::= a \<longrightarrow> (if z = x
      then sources_aux cs vs s f x \<union> \<Union> {sources cs vs s f y | y.
        run_flow cs vs s f: dom y \<leadsto> dom x \<and> y \<in> avars a}
      else sources cs vs s f x) \<subseteq> ?F c"
      (is "\<forall>_ a. _ \<longrightarrow> (if _ then ?A \<union> ?G a else ?B) \<subseteq> _")
    proof (clarify, split if_split_asm)
      fix y z a
      assume H: "c = z ::= a" and I: "z = x"
      hence "?F (z ::= a) = sources_aux (\<langle>X\<rangle> # cs) vs s f x \<union>
        \<Union> {sources (\<langle>X\<rangle> # cs) vs s f y | y.
          run_flow cs vs s f: dom y \<leadsto> dom x \<and> y \<in> avars a}"
        (is "_ = ?A' \<union> ?G' a")
        by (simp only: append_Cons [symmetric] sources.simps,
         simp add: run_flow_observe)
      moreover assume "y \<in> ?A \<union> ?G a"
      moreover {
        assume "y \<in> ?A"
        hence "y \<in> ?A'"
          using A and H and I by blast
      }
      moreover {
        assume "y \<in> ?G a"
        hence "y \<in> ?G' a"
          using B and H and I by blast
      }
      ultimately show "y \<in> ?F (z ::= a)"
        by blast
    next
      fix y z a
      assume "c = z ::= a" and "z \<noteq> x"
      moreover from this have "?F (z ::= a) = sources (\<langle>X\<rangle> # cs) vs s f x"
        by (simp only: append_Cons [symmetric] sources.simps, simp)
      moreover assume "y \<in> ?B"
      ultimately show "y \<in> ?F (z ::= a)"
        using C by blast
    qed
  qed
  apply (rule conjI)
  subgoal
  proof -
    show "\<forall>z. c = IN z \<longrightarrow> (if z = x
      then sources_aux cs vs s f x else sources cs vs s f x) \<subseteq> ?F c"
      (is "\<forall>_. _ \<longrightarrow> (if _ then ?A else ?B) \<subseteq> _")
    proof (clarify, split if_split_asm)
      fix y z
      assume "c = IN z" and "z = x"
      moreover from this have "?F (IN z) = sources_aux (\<langle>X\<rangle> # cs) vs s f x"
        by (simp only: append_Cons [symmetric] sources.simps, simp)
      moreover assume "y \<in> ?A"
      ultimately show "y \<in> ?F (IN z)"
        using D by blast
    next
      fix y z
      assume "c = IN z" and "z \<noteq> x"
      moreover from this have "?F (IN z) = sources (\<langle>X\<rangle> # cs) vs s f x"
        by (simp only: append_Cons [symmetric] sources.simps, simp)
      moreover assume "y \<in> ?B"
      ultimately show "y \<in> ?F (IN z)"
        using E by blast
    qed
  qed
  apply (rule conjI)
  subgoal by (simp only: append_Cons [symmetric] sources.simps, simp add: F)
  subgoal
  proof -
    show "\<forall>Y. c = \<langle>Y\<rangle> \<longrightarrow> sources cs vs s f x \<union>
      \<Union> {sources cs vs s f y | y.
        run_flow cs vs s f: dom y \<leadsto> dom x \<and> y \<in> Y} \<subseteq> ?F c"
      (is "\<forall>Y. _ \<longrightarrow> ?A \<union> ?G Y \<subseteq> _")
    proof clarify
      fix y Y
      assume H: "c = \<langle>Y\<rangle>"
      hence "?F (\<langle>Y\<rangle>) = sources (\<langle>X\<rangle> # cs) vs s f x \<union>
        \<Union> {sources (\<langle>X\<rangle> # cs) vs s f y | y.
          run_flow cs vs s f: dom y \<leadsto> dom x \<and> y \<in> Y}"
        (is "_ = ?A' \<union> ?G' Y")
        by (simp only: append_Cons [symmetric] sources.simps,
         simp add: run_flow_observe)
      moreover assume "y \<in> ?A \<union> ?G Y"
      moreover {
        assume "y \<in> ?A"
        hence "y \<in> ?A'"
          using G and H by blast
      }
      moreover {
        assume "y \<in> ?G Y"
        hence "y \<in> ?G' Y"
          using G and H by blast
      }
      ultimately show "y \<in> ?F (\<langle>Y\<rangle>)"
        by blast
    qed
  qed
  done 

lemma sources_observe_tl_2:
  assumes
    A: "\<And>z a. c = (z ::= a :: com_flow) \<Longrightarrow>
      sources_aux cs vs s f x \<subseteq> sources_aux (\<langle>X\<rangle> # cs) vs s f x" and
    B: "\<And>z. c = (IN z :: com_flow) \<Longrightarrow>
      sources_aux cs vs s f x \<subseteq> sources_aux (\<langle>X\<rangle> # cs) vs s f x" and
    C: "\<And>z. c = (OUT z :: com_flow) \<Longrightarrow>
      sources_aux cs vs s f x \<subseteq> sources_aux (\<langle>X\<rangle> # cs) vs s f x" and
    D: "\<And>Y. c = \<langle>Y\<rangle> \<Longrightarrow>
      sources_aux cs vs s f x \<subseteq> sources_aux (\<langle>X\<rangle> # cs) vs s f x" and
    E: "\<And>Y b w. c = \<langle>Y\<rangle> \<Longrightarrow>
      sources cs vs s f w \<subseteq> sources (\<langle>X\<rangle> # cs) vs s f w"
  shows "sources_aux (cs @ [c]) vs s f x \<subseteq>
    sources_aux (\<langle>X\<rangle> # cs @ [c]) vs s f x"
    (is "_ \<subseteq> ?F c")
  apply (subst sources_aux.simps)
  apply (split com_flow.split)
  apply (rule conjI)
   defer
   apply (rule conjI)
    defer
    apply (rule conjI)
     defer
  subgoal
  proof -
    show "\<forall>Y. c = \<langle>Y\<rangle> \<longrightarrow> sources_aux cs vs s f x \<union>
      \<Union> {sources cs vs s f y | y.
        run_flow cs vs s f: dom y \<leadsto> dom x \<and> y \<in> Y} \<subseteq> ?F c"
      (is "\<forall>Y. _ \<longrightarrow> ?A \<union> ?G Y \<subseteq> _")
    proof clarify
      fix y Y
      assume F: "c = \<langle>Y\<rangle>"
      hence "?F (\<langle>Y\<rangle>) = sources_aux (\<langle>X\<rangle> # cs) vs s f x \<union>
        \<Union> {sources (\<langle>X\<rangle> # cs) vs s f y | y.
          run_flow cs vs s f: dom y \<leadsto> dom x \<and> y \<in> Y}"
        (is "_ = ?A' \<union> ?G' Y")
        by (simp only: append_Cons [symmetric] sources_aux.simps,
         simp add: run_flow_observe)
      moreover assume "y \<in> ?A \<union> ?G Y"
      moreover {
        assume "y \<in> ?A"
        hence "y \<in> ?A'"
          using D and F by blast
      }
      moreover {
        assume "y \<in> ?G Y"
        hence "y \<in> ?G' Y"
          using E and F by blast
      }
      ultimately show "y \<in> ?F (\<langle>Y\<rangle>)"
        by blast
    qed
  qed
by (simp only: append_Cons [symmetric] sources_aux.simps, simp add: A B C)+

lemma sources_observe_tl:
 "sources cs vs s f x \<subseteq> sources (\<langle>X\<rangle> # cs) vs s f x"
and sources_aux_observe_tl:
 "sources_aux cs vs s f x \<subseteq> sources_aux (\<langle>X\<rangle> # cs) vs s f x"
   apply (induction cs vs s f x and cs vs s f x rule: sources_induct)
  subgoal by (erule sources_observe_tl_1, assumption+)
  subgoal by (simp, subst append_Nil [symmetric], subst sources.simps, simp)
  subgoal by (erule sources_observe_tl_2, assumption+)
  by simp


lemma sources_out_observe_tl_1:
  assumes
    A: "\<And>z a. c = (z ::= a :: com_flow) \<Longrightarrow>
      sources_out cs vs s f x \<subseteq> sources_out (\<langle>X\<rangle> # cs) vs s f x" and
    B: "\<And>z. c = (IN z :: com_flow) \<Longrightarrow>
      sources_out cs vs s f x \<subseteq> sources_out (\<langle>X\<rangle> # cs) vs s f x" and
    C: "\<And>z. c = (OUT z :: com_flow) \<Longrightarrow>
      sources_out cs vs s f x \<subseteq> sources_out (\<langle>X\<rangle> # cs) vs s f x" and
    D: "\<And>Y. c = \<langle>Y\<rangle> \<Longrightarrow>
      sources_out cs vs s f x \<subseteq> sources_out (\<langle>X\<rangle> # cs) vs s f x"
  shows "sources_out (cs @ [c]) vs s f x \<subseteq>
    sources_out (\<langle>X\<rangle> # cs @ [c]) vs s f x"
    (is "_ \<subseteq> ?F c")
  apply (subst sources_out.simps)
  apply (split com_flow.split)
  apply (rule conjI)
   defer
   apply (rule conjI)
    defer
  subgoal
  proof
    show "\<forall>z. c = OUT z \<longrightarrow> sources_out cs vs s f x \<union>
      (if z = x then sources cs vs s f x else {}) \<subseteq> ?F c"
      (is "\<forall>_. _ \<longrightarrow> ?A \<union> (if _ then ?B else _) \<subseteq> _")
    proof (clarify, split if_split_asm)
      fix y z
      assume E: "c = OUT z" and F: "z = x"
      assume "y \<in> ?A \<union> ?B"
      moreover {
        assume "y \<in> ?A"
        hence "y \<in> sources_out (\<langle>X\<rangle> # cs) vs s f x"
          using C and E by blast
      }
      moreover {
        assume "y \<in> ?B"
        hence "y \<in> sources (\<langle>X\<rangle> # cs) vs s f x"
          by (rule subsetD [OF sources_observe_tl])
      }
      ultimately show "y \<in> ?F (OUT z)"
        using F by (simp only: append_Cons [symmetric] sources_out.simps,
         auto)
    next
      fix y z
      assume "c = OUT z" and "y \<in> sources_out cs vs s f x \<union> {}"
      hence "y \<in> sources_out (\<langle>X\<rangle> # cs) vs s f x"
        using C by blast
      thus "y \<in> ?F (OUT z)"
        by (simp only: append_Cons [symmetric] sources_out.simps, simp)
    qed
  next
    show "\<forall>Y. c = \<langle>Y\<rangle> \<longrightarrow> sources_out cs vs s f x \<union>
      \<Union> {sources cs vs s f y | y.
        run_flow cs vs s f: dom y \<leadsto> dom x \<and> y \<in> Y} \<subseteq> ?F c"
      (is "\<forall>Y. _ \<longrightarrow> ?A \<union> ?G Y \<subseteq> _")
    proof clarify
      fix y Y
      assume E: "c = \<langle>Y\<rangle>"
      assume "y \<in> ?A \<union> ?G Y"
      moreover {
        assume "y \<in> ?A"
        hence "y \<in> sources_out (\<langle>X\<rangle> # cs) vs s f x"
          using D and E by blast
      }
      moreover {
        assume "y \<in> ?G Y"
        hence "y \<in> \<Union> {sources (\<langle>X\<rangle> # cs) vs s f y | y.
          run_flow (\<langle>X\<rangle> # cs) vs s f: dom y \<leadsto> dom x \<and> y \<in> Y}"
          by (auto intro: subsetD [OF sources_observe_tl]
           simp: run_flow_observe)
      }
      ultimately show "y \<in> ?F (\<langle>Y\<rangle>)"
        by (simp only: append_Cons [symmetric] sources_out.simps, auto)
    qed
  qed
by (simp only: append_Cons [symmetric] sources_out.simps, simp add: A B)+

lemma sources_out_observe_tl:
 "sources_out cs vs s f x \<subseteq> sources_out (\<langle>X\<rangle> # cs) vs s f x"
by (induction cs vs s f x rule: sources_out.induct,
 erule sources_out_observe_tl_1, simp_all)


lemma tags_observe_tl_1:
 "\<lbrakk>\<And>z a. c = z ::= a \<Longrightarrow> z = x \<Longrightarrow>
    tags_aux (\<langle>X\<rangle> # cs) vs s f x = tags_aux cs vs s f x;
  \<And>z a b w. c = z ::= a \<Longrightarrow> z = x \<Longrightarrow>
    tags (\<langle>X\<rangle> # cs) vs s f w = tags cs vs s f w;
  \<And>z a. c = z ::= a \<Longrightarrow> z \<noteq> x \<Longrightarrow>
    tags (\<langle>X\<rangle> # cs) vs s f x = tags cs vs s f x;
  \<And>z. c = IN z \<Longrightarrow> z = x \<Longrightarrow>
    tags_aux (\<langle>X\<rangle> # cs) vs s f x = tags_aux cs vs s f x;
  \<And>z. c = IN z \<Longrightarrow> z \<noteq> x \<Longrightarrow>
    tags (\<langle>X\<rangle> # cs) vs s f x = tags cs vs s f x;
  \<And>z. c = OUT z \<Longrightarrow>
    tags (\<langle>X\<rangle> # cs) vs s f x = tags cs vs s f x;
  \<And>Y b w. c = \<langle>Y\<rangle> \<Longrightarrow>
    tags (\<langle>X\<rangle> # cs) vs s f w = tags cs vs s f w\<rbrakk> \<Longrightarrow>
  tags (\<langle>X\<rangle> # cs @ [c]) vs s f x = tags (cs @ [c]) vs s f x"
by (subst tags.simps, split com_flow.split, simp_all only: append_Cons
 [symmetric] tags.simps, simp_all add: run_flow_observe)

lemma tags_observe_tl_2:
 "\<lbrakk>\<And>z a. c = z ::= a \<Longrightarrow>
    tags_aux (\<langle>X\<rangle> # cs) vs s f x = tags_aux cs vs s f x;
  \<And>z. c = IN z \<Longrightarrow>
    tags_aux (\<langle>X\<rangle> # cs) vs s f x = tags_aux cs vs s f x;
  \<And>z. c = OUT z \<Longrightarrow>
    tags_aux (\<langle>X\<rangle> # cs) vs s f x = tags_aux cs vs s f x;
  \<And>Y. c = \<langle>Y\<rangle> \<Longrightarrow>
    tags_aux (\<langle>X\<rangle> # cs) vs s f x = tags_aux cs vs s f x;
  \<And>Y b w. c = \<langle>Y\<rangle> \<Longrightarrow>
    tags (\<langle>X\<rangle> # cs) vs s f w = tags cs vs s f w\<rbrakk> \<Longrightarrow>
  tags_aux (\<langle>X\<rangle> # cs @ [c]) vs s f x = tags_aux (cs @ [c]) vs s f x"
by (subst tags_aux.simps, split com_flow.split, simp_all only: append_Cons
 [symmetric] tags_aux.simps, simp_all add: run_flow_observe)

lemma tags_observe_tl:
 "tags (\<langle>X\<rangle> # cs) vs s f x = tags cs vs s f x"
and tags_aux_observe_tl:
 "tags_aux (\<langle>X\<rangle> # cs) vs s f x = tags_aux cs vs s f x"
   apply (induction cs vs s f x and cs vs s f x rule: tags_induct)
  subgoal by (erule tags_observe_tl_1, assumption+)
  subgoal by (subst append_Nil [symmetric], subst tags.simps tags_aux.simps, simp)
  subgoal by (erule tags_observe_tl_2, assumption+)
  subgoal by (subst append_Nil [symmetric], subst tags.simps tags_aux.simps, simp)
  done

lemma tags_out_observe_tl_1:
 "\<lbrakk>\<And>z a. c = z ::= a \<Longrightarrow>
    tags_out (\<langle>X\<rangle> # cs) vs s f x = tags_out cs vs s f x;
  \<And>z. c = IN z \<Longrightarrow>
    tags_out (\<langle>X\<rangle> # cs) vs s f x = tags_out cs vs s f x;
  \<And>z. c = OUT z \<Longrightarrow>
    tags_out (\<langle>X\<rangle> # cs) vs s f x = tags_out cs vs s f x;
  \<And>Y. c = \<langle>Y\<rangle> \<Longrightarrow>
    tags_out (\<langle>X\<rangle> # cs) vs s f x = tags_out cs vs s f x\<rbrakk> \<Longrightarrow>
  tags_out (\<langle>X\<rangle> # cs @ [c]) vs s f x = tags_out (cs @ [c]) vs s f x"
by (subst tags_out.simps, split com_flow.split, simp_all only: append_Cons
 [symmetric] tags_out.simps, simp_all add: run_flow_observe tags_observe_tl)

lemma tags_out_observe_tl:
 "tags_out (\<langle>X\<rangle> # cs) vs s f x = tags_out cs vs s f x"
  apply (induction cs vs s f x rule: tags_out.induct)
   apply (erule tags_out_observe_tl_1, assumption+)
by (subst append_Nil [symmetric], subst tags_out.simps, simp)


lemma tags_sources_1:
  assumes
    A: "\<And>z a. c = (z ::= a :: com_flow) \<Longrightarrow> z = x \<Longrightarrow>
      (y, n) \<in> tags_aux cs vs s f x \<Longrightarrow>
        let m = Suc (Max {k. k \<le> length cs \<and>
          length [c\<leftarrow>take k cs. c = IN y] \<le> n})
        in y \<in> sources_aux (drop m cs) (vs @ in_flow (take m cs) vs f)
          (run_flow (take m cs) vs s f) f x"
      (is "\<And>_ _. _ \<Longrightarrow> _ \<Longrightarrow> _ \<Longrightarrow> let m = Suc (Max (?F cs)) in
        _ \<in> sources_aux _ (?G m cs) (?H m cs) _ _")
  assumes
    B: "\<And>z a b w. c = (z ::= a :: com_flow) \<Longrightarrow> z = x \<Longrightarrow>
      (y, n) \<in> tags cs vs s f w \<Longrightarrow> let m = Suc (Max (?F cs)) in
        y \<in> sources (drop m cs) (?G m cs) (?H m cs) f w" and
    C: "\<And>z a. c = (z ::= a :: com_flow) \<Longrightarrow> z \<noteq> x \<Longrightarrow>
      (y, n) \<in> tags cs vs s f x \<Longrightarrow> let m = Suc (Max (?F cs)) in
        y \<in> sources (drop m cs) (?G m cs) (?H m cs) f x" and
    D: "\<And>z. c = (IN z :: com_flow) \<Longrightarrow> z = x \<Longrightarrow>
      (y, n) \<in> tags_aux cs vs s f x \<Longrightarrow> let m = Suc (Max (?F cs)) in
        y \<in> sources_aux (drop m cs) (?G m cs) (?H m cs) f x" and
    E: "\<And>z. c = (IN z :: com_flow) \<Longrightarrow> z \<noteq> x \<Longrightarrow>
      (y, n) \<in> tags cs vs s f x \<Longrightarrow> let m = Suc (Max (?F cs)) in
        y \<in> sources (drop m cs) (?G m cs) (?H m cs) f x" and
    F: "\<And>z. c = (OUT z :: com_flow) \<Longrightarrow>
      (y, n) \<in> tags cs vs s f x \<Longrightarrow> let m = Suc (Max (?F cs)) in
        y \<in> sources (drop m cs) (?G m cs) (?H m cs) f x" and
    G: "\<And>X b w. c = \<langle>X\<rangle> \<Longrightarrow>
      (y, n) \<in> tags cs vs s f w \<Longrightarrow> let m = Suc (Max (?F cs)) in
        y \<in> sources (drop m cs) (?G m cs) (?H m cs) f w" and
    H: "(y, n) \<in> tags (cs @ [c]) vs s f x"
  shows "let m = Suc (Max (?F (cs @ [c]))) in
    y \<in> sources (drop m (cs @ [c])) (?G m (cs @ [c])) (?H m (cs @ [c])) f x"
proof -
  have I: "n < length [c\<leftarrow>cs @ [c]. c = IN y]"
    using H by (rule tags_less)
  hence "?F (cs @ [c]) = ?F cs"
    using le_Suc_eq by auto
  moreover have "c \<noteq> IN y \<or> n < length [c\<leftarrow>cs. c = IN y] \<Longrightarrow>
    Suc (Max (?F cs)) \<le> length cs"
    (is "_ \<Longrightarrow> ?m \<le> _")
    using I by (subst Suc_le_eq, subst Max_less_iff,
     auto elim: le_neq_implies_less)
  ultimately have J: "c \<noteq> IN y \<or> n < length [c\<leftarrow>cs. c = IN y] \<Longrightarrow>
    take (Suc (Max (?F (cs @ [c])))) (cs @ [c]) = take ?m cs \<and>
    drop (Suc (Max (?F (cs @ [c])))) (cs @ [c]) = drop ?m cs @ [c]"
    by simp
  from H show ?thesis
  proof (subst (asm) tags.simps, split com_flow.split_asm)
    fix z a
    assume K: "c = z ::= a"
    show "(y, n) \<in> (if z = x
      then tags_aux cs vs s f x \<union> \<Union> {tags cs vs s f y | y.
        run_flow cs vs s f: dom y \<leadsto> dom x \<and> y \<in> avars a}
      else tags cs vs s f x) \<Longrightarrow> ?thesis"
      (is "_ \<in> (if _ then ?A \<union> ?B else ?C) \<Longrightarrow> _")
    proof (split if_split_asm)
      assume L: "z = x" and "(y, n) \<in> ?A \<union> ?B"
      moreover {
        assume "(y, n) \<in> ?A"
        hence "y \<in> sources_aux (drop ?m cs) (?G ?m cs) (?H ?m cs) f x"
          using A and K and L by simp
      }
      moreover {
        assume "(y, n) \<in> ?B"
        hence "y \<in> \<Union> {sources (drop ?m cs) (?G ?m cs) (?H ?m cs) f y | y.
          run_flow (drop ?m cs) (?G ?m cs) (?H ?m cs) f:
            dom y \<leadsto> dom x \<and> y \<in> avars a}"
          using B and K and L by (auto simp: run_flow_append [symmetric])
      }
      ultimately show ?thesis
        using J and K by auto
    next
      assume "z \<noteq> x" and "(y, n) \<in> ?C"
      moreover from this have
       "y \<in> sources (drop ?m cs) (?G ?m cs) (?H ?m cs) f x"
        using C and K by simp
      ultimately show ?thesis
        using J and K by simp
    qed
  next
    fix z
    assume K: "c = IN z"
    show "(y, n) \<in> (if z = x
      then insert (x, length [c\<leftarrow>cs. c = IN x]) (tags_aux cs vs s f x)
      else tags cs vs s f x) \<Longrightarrow> ?thesis"
      (is "_ \<in> (if _ then insert _ ?A else ?B) \<Longrightarrow> _")
    proof (split if_split_asm, erule insertE)
      assume "(y, n) = (x, length [c\<leftarrow>cs. c = IN x])" and "z = x"
      moreover from this have "Max (?F (cs @ [c])) = length cs"
        using K by (subst Max_eq_iff, auto elim: le_SucE)
      ultimately show ?thesis
        by simp
    next
      assume L: "(y, n) \<in> tags_aux cs vs s f x" and "z = x"
      moreover from this have
       "y \<in> sources_aux (drop ?m cs) (?G ?m cs) (?H ?m cs) f x"
        using D and K by simp
      moreover have "n < length [c\<leftarrow>cs. c = IN y]"
        using L by (rule tags_aux_less)
      ultimately show ?thesis
        using J and K by simp
    next
      assume L: "(y, n) \<in> tags cs vs s f x" and "z \<noteq> x"
      moreover from this have
       "y \<in> sources (drop ?m cs) (?G ?m cs) (?H ?m cs) f x"
        using E and K by simp
      moreover have "n < length [c\<leftarrow>cs. c = IN y]"
        using L by (rule tags_less)
      ultimately show ?thesis
        using J and K by simp
    qed
  next
    fix z
    assume "c = OUT z" and "(y, n) \<in> tags cs vs s f x"
    moreover from this have
     "y \<in> sources (drop ?m cs) (?G ?m cs) (?H ?m cs) f x"
      using F by simp
    ultimately show ?thesis
      using J by simp
  next
    fix X
    assume K: "c = \<langle>X\<rangle>"
    assume "(y, n) \<in> tags cs vs s f x \<union> \<Union> {tags cs vs s f y | y.
      run_flow cs vs s f: dom y \<leadsto> dom x \<and> y \<in> X}"
      (is "_ \<in> ?A \<union> ?B")
    moreover {
      assume "(y, n) \<in> ?A"
      hence "y \<in> sources (drop ?m cs) (?G ?m cs) (?H ?m cs) f x"
        using G and K by simp
    }
    moreover {
      assume "(y, n) \<in> ?B"
      hence "y \<in> \<Union> {sources (drop ?m cs) (?G ?m cs) (?H ?m cs) f y | y.
        run_flow (drop ?m cs) (?G ?m cs) (?H ?m cs) f:
          dom y \<leadsto> dom x \<and> y \<in> X}"
        using G and K by (auto simp: run_flow_append [symmetric])
    }
    ultimately show ?thesis
      using J and K by auto
  qed
qed

lemma tags_sources_2:
  assumes
    A: "\<And>z a. c = (z ::= a :: com_flow) \<Longrightarrow>
      (y, n) \<in> tags_aux cs vs s f x \<Longrightarrow>
        let m = Suc (Max {k. k \<le> length cs \<and>
          length [c\<leftarrow>take k cs. c = IN y] \<le> n})
        in y \<in> sources_aux (drop m cs) (vs @ in_flow (take m cs) vs f)
          (run_flow (take m cs) vs s f) f x"
      (is "\<And>_ _. _ \<Longrightarrow> _ \<Longrightarrow> let m = Suc (Max (?F cs)) in
        _ \<in> sources_aux _ (?G m cs) (?H m cs) _ _")
  assumes
    B: "\<And>z. c = (IN z :: com_flow) \<Longrightarrow>
      (y, n) \<in> tags_aux cs vs s f x \<Longrightarrow> let m = Suc (Max (?F cs)) in
        y \<in> sources_aux (drop m cs) (?G m cs) (?H m cs) f x" and
    C: "\<And>z. c = (OUT z :: com_flow) \<Longrightarrow>
      (y, n) \<in> tags_aux cs vs s f x \<Longrightarrow> let m = Suc (Max (?F cs)) in
        y \<in> sources_aux (drop m cs) (?G m cs) (?H m cs) f x" and
    D: "\<And>X. c = \<langle>X\<rangle> \<Longrightarrow>
      (y, n) \<in> tags_aux cs vs s f x \<Longrightarrow> let m = Suc (Max (?F cs)) in
        y \<in> sources_aux (drop m cs) (?G m cs) (?H m cs) f x" and
    E: "\<And>X b w. c = \<langle>X\<rangle> \<Longrightarrow>
      (y, n) \<in> tags cs vs s f w \<Longrightarrow> let m = Suc (Max (?F cs)) in
        y \<in> sources (drop m cs) (?G m cs) (?H m cs) f w" and
    F: "(y, n) \<in> tags_aux (cs @ [c]) vs s f x"
  shows "let m = Suc (Max (?F (cs @ [c]))) in
    y \<in> sources_aux (drop m (cs @ [c])) (?G m (cs @ [c])) (?H m (cs @ [c])) f x"
proof -
  have G: "n < length [c\<leftarrow>cs @ [c]. c = IN y]"
    using F by (rule tags_aux_less)
  hence "?F (cs @ [c]) = ?F cs"
    using le_Suc_eq by auto
  moreover have "c \<noteq> IN y \<or> n < length [c\<leftarrow>cs. c = IN y] \<Longrightarrow>
    Suc (Max (?F cs)) \<le> length cs"
    (is "_ \<Longrightarrow> ?m \<le> _")
    using G by (subst Suc_le_eq, subst Max_less_iff,
     auto elim: le_neq_implies_less)
  ultimately have H: "c \<noteq> IN y \<or> n < length [c\<leftarrow>cs. c = IN y] \<Longrightarrow>
    take (Suc (Max (?F (cs @ [c])))) (cs @ [c]) = take ?m cs \<and>
    drop (Suc (Max (?F (cs @ [c])))) (cs @ [c]) = drop ?m cs @ [c]"
    by simp
  from F show ?thesis
  proof (subst (asm) tags_aux.simps, split com_flow.split_asm)
    fix z a
    assume "c = z ::= a" and "(y, n) \<in> tags_aux cs vs s f x"
    moreover from this have
     "y \<in> sources_aux (drop ?m cs) (?G ?m cs) (?H ?m cs) f x"
      using A by simp
    ultimately show ?thesis
      using H by simp
  next
    fix z
    assume "c = IN z" and I: "(y, n) \<in> tags_aux cs vs s f x"
    moreover from this have
     "y \<in> sources_aux (drop ?m cs) (?G ?m cs) (?H ?m cs) f x"
      using B by simp
    moreover have "n < length [c\<leftarrow>cs. c = IN y]"
      using I by (rule tags_aux_less)
    ultimately show ?thesis
      using H by simp
  next
    fix z
    assume "c = OUT z" and "(y, n) \<in> tags_aux cs vs s f x"
    moreover from this have
     "y \<in> sources_aux (drop ?m cs) (?G ?m cs) (?H ?m cs) f x"
      using C by simp
    ultimately show ?thesis
      using H by simp
  next
    fix X
    assume I: "c = \<langle>X\<rangle>"
    assume "(y, n) \<in> tags_aux cs vs s f x \<union> \<Union> {tags cs vs s f y | y.
      run_flow cs vs s f: dom y \<leadsto> dom x \<and> y \<in> X}"
      (is "_ \<in> ?A \<union> ?B")
    moreover {
      assume "(y, n) \<in> ?A"
      hence "y \<in> sources_aux (drop ?m cs) (?G ?m cs) (?H ?m cs) f x"
        using D and I by simp
    }
    moreover {
      assume "(y, n) \<in> ?B"
      hence "y \<in> \<Union> {sources (drop ?m cs) (?G ?m cs) (?H ?m cs) f y | y.
        run_flow (drop ?m cs) (?G ?m cs) (?H ?m cs) f:
          dom y \<leadsto> dom x \<and> y \<in> X}"
        using E and I by (auto simp: run_flow_append [symmetric])
    }
    ultimately show ?thesis
      using H and I by auto
  qed
qed

lemma tags_sources:
 "(y, n) \<in> tags cs vs s f x \<Longrightarrow>
    let m = Suc (Max {k. k \<le> length cs \<and>
      length [c\<leftarrow>take k cs. c = IN y] \<le> n})
    in y \<in> sources (drop m cs) (vs @ in_flow (take m cs) vs f)
      (run_flow (take m cs) vs s f) f x"
and tags_aux_sources_aux:
 "(y, n) \<in> tags_aux cs vs s f x \<Longrightarrow>
    let m = Suc (Max {k. k \<le> length cs \<and>
      length [c\<leftarrow>take k cs. c = IN y] \<le> n})
    in y \<in> sources_aux (drop m cs) (vs @ in_flow (take m cs) vs f)
      (run_flow (take m cs) vs s f) f x"
by (induction cs vs s f x and cs vs s f x rule: tags_induct,
 erule_tac [3] tags_sources_2, erule tags_sources_1, simp_all)


lemma tags_out_sources_out_1:
  assumes
    A: "\<And>z a. c = (z ::= a :: com_flow) \<Longrightarrow>
      (y, n) \<in> tags_out cs vs s f x \<Longrightarrow>
        let m = Suc (Max {k. k \<le> length cs \<and>
          length [c\<leftarrow>take k cs. c = IN y] \<le> n})
        in y \<in> sources_out (drop m cs) (vs @ in_flow (take m cs) vs f)
          (run_flow (take m cs) vs s f) f x"
      (is "\<And>_ _. _ \<Longrightarrow> _ \<Longrightarrow> let m = Suc (Max (?F cs)) in
        _ \<in> sources_out _ (?G m cs) (?H m cs) _ _")
  assumes
    B: "\<And>z. c = (IN z :: com_flow) \<Longrightarrow>
      (y, n) \<in> tags_out cs vs s f x \<Longrightarrow> let m = Suc (Max (?F cs)) in
        y \<in> sources_out (drop m cs) (?G m cs) (?H m cs) f x" and
    C: "\<And>z. c = (OUT z :: com_flow) \<Longrightarrow>
      (y, n) \<in> tags_out cs vs s f x \<Longrightarrow> let m = Suc (Max (?F cs)) in
        y \<in> sources_out (drop m cs) (?G m cs) (?H m cs) f x" and
    D: "\<And>X. c = \<langle>X\<rangle> \<Longrightarrow>
      (y, n) \<in> tags_out cs vs s f x \<Longrightarrow> let m = Suc (Max (?F cs)) in
        y \<in> sources_out (drop m cs) (?G m cs) (?H m cs) f x" and
    E: "(y, n) \<in> tags_out (cs @ [c]) vs s f x"
  shows "let m = Suc (Max (?F (cs @ [c]))) in
    y \<in> sources_out (drop m (cs @ [c])) (?G m (cs @ [c])) (?H m (cs @ [c])) f x"
proof -
  have F: "n < length [c\<leftarrow>cs @ [c]. c = IN y]"
    using E by (rule tags_out_less)
  hence "?F (cs @ [c]) = ?F cs"
    using le_Suc_eq by auto
  moreover have "c \<noteq> IN y \<or> n < length [c\<leftarrow>cs. c = IN y] \<Longrightarrow>
    Suc (Max (?F cs)) \<le> length cs"
    (is "_ \<Longrightarrow> ?m \<le> _")
    using F by (subst Suc_le_eq, subst Max_less_iff,
     auto elim: le_neq_implies_less)
  ultimately have G: "c \<noteq> IN y \<or> n < length [c\<leftarrow>cs. c = IN y] \<Longrightarrow>
    take (Suc (Max (?F (cs @ [c])))) (cs @ [c]) = take ?m cs \<and>
    drop (Suc (Max (?F (cs @ [c])))) (cs @ [c]) = drop ?m cs @ [c]"
    by simp
  from E show ?thesis
  proof (subst (asm) tags_out.simps, split com_flow.split_asm)
    fix z a
    assume "c = z ::= a" and "(y, n) \<in> tags_out cs vs s f x"
    moreover from this have
     "y \<in> sources_out (drop ?m cs) (?G ?m cs) (?H ?m cs) f x"
      using A by simp
    ultimately show ?thesis
      using G by simp
  next
    fix z
    assume "c = IN z" and H: "(y, n) \<in> tags_out cs vs s f x"
    moreover from this have
     "y \<in> sources_out (drop ?m cs) (?G ?m cs) (?H ?m cs) f x"
      using B by simp
    moreover have "n < length [c\<leftarrow>cs. c = IN y]"
      using H by (rule tags_out_less)
    ultimately show ?thesis
      using G by simp
  next
    fix z
    assume H: "c = OUT z"
    show "(y, n) \<in> tags_out cs vs s f x \<union>
      (if z = x then tags cs vs s f x else {}) \<Longrightarrow> ?thesis"
      (is "_ \<in> ?A \<union> (if _ then ?B else _) \<Longrightarrow> _")
    proof (split if_split_asm)
      assume "z = x" and "(y, n) \<in> ?A \<union> ?B"
      moreover {
        assume "(y, n) \<in> ?A"
        hence "y \<in> sources_out (drop ?m cs) (?G ?m cs) (?H ?m cs) f x"
          using C and H by simp
      }
      moreover {
        assume "(y, n) \<in> ?B"
        hence "y \<in> sources (drop ?m cs) (?G ?m cs) (?H ?m cs) f x"
          by (auto dest: tags_sources)
      }
      ultimately show ?thesis
        using G and H by auto
    next
      assume "(y, n) \<in> ?A \<union> {}"
      moreover from this have
       "y \<in> sources_out (drop ?m cs) (?G ?m cs) (?H ?m cs) f x"
        using C and H by simp
      ultimately show ?thesis
        using G and H by simp
    qed
  next
    fix X
    assume H: "c = \<langle>X\<rangle>"
    assume "(y, n) \<in> tags_out cs vs s f x \<union> \<Union> {tags cs vs s f y | y.
      run_flow cs vs s f: dom y \<leadsto> dom x \<and> y \<in> X}"
      (is "_ \<in> ?A \<union> ?B")
    moreover {
      assume "(y, n) \<in> ?A"
      hence "y \<in> sources_out (drop ?m cs) (?G ?m cs) (?H ?m cs) f x"
        using D and H by simp
    }
    moreover {
      assume "(y, n) \<in> ?B"
      hence "y \<in> \<Union> {sources (drop ?m cs) (?G ?m cs) (?H ?m cs) f y | y.
        run_flow (drop ?m cs) (?G ?m cs) (?H ?m cs) f:
          dom y \<leadsto> dom x \<and> y \<in> X}"
        by (fastforce dest: tags_sources simp: run_flow_append [symmetric])
    }
    ultimately show ?thesis
      using G and H by auto
  qed
qed

lemma tags_out_sources_out:
 "(y, n) \<in> tags_out cs vs s f x \<Longrightarrow>
    let m = Suc (Max {k. k \<le> length cs \<and>
      length [c\<leftarrow>take k cs. c = IN y] \<le> n})
    in y \<in> sources_out (drop m cs) (vs @ in_flow (take m cs) vs f)
      (run_flow (take m cs) vs s f) f x"
by (induction cs vs s f x rule: tags_out.induct,
 erule tags_out_sources_out_1, simp_all)


lemma sources_member_1:
  assumes
    A: "\<And>z a. c = (z ::= a :: com_flow) \<Longrightarrow> z = x \<Longrightarrow>
      y \<in> sources_aux cs' (vs @ in_flow cs vs f) (run_flow cs vs s f) f x \<Longrightarrow>
        sources cs vs s f y \<subseteq> sources_aux (cs @ cs') vs s f x"
      (is "\<And>_ _. _ \<Longrightarrow> _ \<Longrightarrow> _ \<in> sources_aux _ ?vs' ?s' _ _ \<Longrightarrow>
        _ \<subseteq> sources_aux ?cs _ _ _ _")
  assumes
    B: "\<And>z a b w. c = (z ::= a :: com_flow) \<Longrightarrow> z = x \<Longrightarrow>
      y \<in> sources cs' ?vs' ?s' f w \<Longrightarrow>
        sources cs vs s f y \<subseteq> sources ?cs vs s f w" and
    C: "\<And>z a. c = (z ::= a :: com_flow) \<Longrightarrow> z \<noteq> x \<Longrightarrow>
      y \<in> sources cs' ?vs' ?s' f x \<Longrightarrow>
        sources cs vs s f y \<subseteq> sources ?cs vs s f x" and
    D: "\<And>z. c = (IN z :: com_flow) \<Longrightarrow> z = x \<Longrightarrow>
      y \<in> sources_aux cs' ?vs' ?s' f x \<Longrightarrow>
        sources cs vs s f y \<subseteq> sources_aux ?cs vs s f x" and
    E: "\<And>z. c = (IN z :: com_flow) \<Longrightarrow> z \<noteq> x \<Longrightarrow>
      y \<in> sources cs' ?vs' ?s' f x \<Longrightarrow>
        sources cs vs s f y \<subseteq> sources ?cs vs s f x" and
    F: "\<And>z. c = (OUT z :: com_flow) \<Longrightarrow>
      y \<in> sources cs' ?vs' ?s' f x \<Longrightarrow>
        sources cs vs s f y \<subseteq> sources ?cs vs s f x" and
    G: "\<And>X b w. c = \<langle>X\<rangle> \<Longrightarrow>
      y \<in> sources cs' ?vs' ?s' f w \<Longrightarrow>
        sources cs vs s f y \<subseteq> sources ?cs vs s f w"
  shows "y \<in> sources (cs' @ [c]) ?vs' ?s' f x \<Longrightarrow>
    sources cs vs s f y \<subseteq> sources (cs @ cs' @ [c]) vs s f x"
proof (subst (asm) sources.simps, split com_flow.split_asm)
  fix z a
  assume H: "c = z ::= a"
  show "y \<in> (if z = x
    then sources_aux cs' ?vs' ?s' f x \<union> \<Union> {sources cs' ?vs' ?s' f w | w.
      run_flow cs' ?vs' ?s' f: dom w \<leadsto> dom x \<and> w \<in> avars a}
    else sources cs' ?vs' ?s' f x) \<Longrightarrow> ?thesis"
    (is "_ \<in> (if _ then ?A \<union> ?B else ?C) \<Longrightarrow> _")
  proof (split if_split_asm)
    assume I: "z = x" and "y \<in> ?A \<union> ?B"
    moreover {
      assume "y \<in> ?A"
      hence "sources cs vs s f y \<subseteq> sources_aux ?cs vs s f x"
        using A and H and I by simp
    }
    moreover {
      assume "y \<in> ?B"
      hence "sources cs vs s f y \<subseteq> \<Union> {sources ?cs vs s f w | w.
        run_flow ?cs vs s f: dom w \<leadsto> dom x \<and> w \<in> avars a}"
        using B and H and I by (fastforce simp: run_flow_append)
    }
    ultimately show ?thesis
      using H by (simp only: append_assoc [symmetric] sources.simps, auto)
  next
    assume "z \<noteq> x" and "y \<in> ?C"
    moreover from this have "sources cs vs s f y \<subseteq> sources ?cs vs s f x"
      using C and H by simp
    ultimately show ?thesis
      using H by (simp only: append_assoc [symmetric] sources.simps, auto)
  qed
next
  fix z
  assume H: "c = IN z"
  show "y \<in> (if z = x
    then sources_aux cs' ?vs' ?s' f x
    else sources cs' ?vs' ?s' f x) \<Longrightarrow> ?thesis"
    (is "_ \<in> (if _ then ?A else ?B) \<Longrightarrow> _")
  proof (split if_split_asm)
    assume "z = x" and "y \<in> ?A"
    moreover from this have "sources cs vs s f y \<subseteq> sources_aux ?cs vs s f x"
      using D and H by simp
    ultimately show ?thesis
      using H by (simp only: append_assoc [symmetric] sources.simps, auto)
  next
    assume "z \<noteq> x" and "y \<in> ?B"
    moreover from this have "sources cs vs s f y \<subseteq> sources ?cs vs s f x"
      using E and H by simp
    ultimately show ?thesis
      using H by (simp only: append_assoc [symmetric] sources.simps, auto)
  qed
next
  fix z
  assume "c = OUT z" and "y \<in> sources cs' ?vs' ?s' f x"
  moreover from this have "sources cs vs s f y \<subseteq> sources ?cs vs s f x"
    using F by simp
  ultimately show ?thesis
    by (simp only: append_assoc [symmetric] sources.simps, auto)
next
  fix X
  assume H: "c = \<langle>X\<rangle>"
  assume "y \<in> sources cs' ?vs' ?s' f x \<union> \<Union> {sources cs' ?vs' ?s' f w | w.
    run_flow cs' ?vs' ?s' f: dom w \<leadsto> dom x \<and> w \<in> X}"
    (is "_ \<in> ?A \<union> ?B")
  moreover {
    assume "y \<in> ?A"
    hence "sources cs vs s f y \<subseteq> sources ?cs vs s f x"
      using G and H by simp
  }
  moreover {
    assume "y \<in> ?B"
    hence "sources cs vs s f y \<subseteq> \<Union> {sources ?cs vs s f w | w.
      run_flow ?cs vs s f: dom w \<leadsto> dom x \<and> w \<in> X}"
      using G and H by (auto simp: run_flow_append)
  }
  ultimately show ?thesis
    using H by (simp only: append_assoc [symmetric] sources.simps, auto)
qed

lemma sources_member_2:
  assumes
    A: "\<And>z a. c = (z ::= a :: com_flow) \<Longrightarrow>
      y \<in> sources_aux cs' (vs @ in_flow cs vs f) (run_flow cs vs s f) f x \<Longrightarrow>
        sources cs vs s f y \<subseteq> sources_aux (cs @ cs') vs s f x"
      (is "\<And>_ _. _ \<Longrightarrow> _ \<in> sources_aux _ ?vs' ?s' _ _ \<Longrightarrow>
        _ \<subseteq> sources_aux ?cs _ _ _ _")
  assumes
    B: "\<And>z. c = (IN z :: com_flow) \<Longrightarrow>
      y \<in> sources_aux cs' ?vs' ?s' f x \<Longrightarrow>
        sources cs vs s f y \<subseteq> sources_aux ?cs vs s f x" and
    C: "\<And>z. c = (OUT z :: com_flow) \<Longrightarrow>
      y \<in> sources_aux cs' ?vs' ?s' f x \<Longrightarrow>
        sources cs vs s f y \<subseteq> sources_aux ?cs vs s f x" and
    D: "\<And>X. c = \<langle>X\<rangle> \<Longrightarrow>
      y \<in> sources_aux cs' ?vs' ?s' f x \<Longrightarrow>
        sources cs vs s f y \<subseteq> sources_aux ?cs vs s f x" and
    E: "\<And>X b w. c = \<langle>X\<rangle> \<Longrightarrow>
      y \<in> sources cs' ?vs' ?s' f w \<Longrightarrow>
        sources cs vs s f y \<subseteq> sources ?cs vs s f w"
  shows "y \<in> sources_aux (cs' @ [c]) ?vs' ?s' f x \<Longrightarrow>
    sources cs vs s f y \<subseteq> sources_aux (cs @ cs' @ [c]) vs s f x"
proof (subst (asm) sources_aux.simps, split com_flow.split_asm)
  fix z a
  assume "c = z ::= a" and "y \<in> sources_aux cs' ?vs' ?s' f x"
  moreover from this have "sources cs vs s f y \<subseteq> sources_aux ?cs vs s f x"
    using A by simp
  ultimately show ?thesis
    by (simp only: append_assoc [symmetric] sources_aux.simps, auto)
next
  fix z
  assume "c = IN z" and "y \<in> sources_aux cs' ?vs' ?s' f x"
  moreover from this have "sources cs vs s f y \<subseteq> sources_aux ?cs vs s f x"
    using B by simp
  ultimately show ?thesis
    by (simp only: append_assoc [symmetric] sources_aux.simps, auto)
next
  fix z
  assume "c = OUT z" and "y \<in> sources_aux cs' ?vs' ?s' f x"
  moreover from this have "sources cs vs s f y \<subseteq> sources_aux ?cs vs s f x"
    using C by simp
  ultimately show ?thesis
    by (simp only: append_assoc [symmetric] sources_aux.simps, auto)
next
  fix X
  assume F: "c = \<langle>X\<rangle>"
  assume "y \<in> sources_aux cs' ?vs' ?s' f x \<union> \<Union> {sources cs' ?vs' ?s' f w | w.
    run_flow cs' ?vs' ?s' f: dom w \<leadsto> dom x \<and> w \<in> X}"
    (is "_ \<in> ?A \<union> ?B")
  moreover {
    assume "y \<in> ?A"
    hence "sources cs vs s f y \<subseteq> sources_aux ?cs vs s f x"
      using D and F by simp
  }
  moreover {
    assume "y \<in> ?B"
    hence "sources cs vs s f y \<subseteq> \<Union> {sources ?cs vs s f w | w.
      run_flow ?cs vs s f: dom w \<leadsto> dom x \<and> w \<in> X}"
      using E and F by (auto simp: run_flow_append)
  }
  ultimately show ?thesis
    using F by (simp only: append_assoc [symmetric] sources_aux.simps, auto)
qed

lemma sources_member:
 "y \<in> sources cs' (vs @ in_flow cs vs f) (run_flow cs vs s f) f x \<Longrightarrow>
    sources cs vs s f y \<subseteq> sources (cs @ cs') vs s f x"
and sources_aux_member:
 "y \<in> sources_aux cs' (vs @ in_flow cs vs f) (run_flow cs vs s f) f x \<Longrightarrow>
    sources cs vs s f y \<subseteq> sources_aux (cs @ cs') vs s f x"
by (induction cs' vs s f x and cs' vs s f x rule: sources_induct,
 erule_tac [3] sources_member_2, erule sources_member_1, simp_all)


lemma sources_out_member_1:
  assumes
    A: "\<And>z a. c = (z ::= a :: com_flow) \<Longrightarrow>
      y \<in> sources_out cs' (vs @ in_flow cs vs f) (run_flow cs vs s f) f x \<Longrightarrow>
        sources cs vs s f y \<subseteq> sources_out (cs @ cs') vs s f x"
      (is "\<And>_ _. _ \<Longrightarrow> _ \<in> sources_out _ ?vs' ?s' _ _ \<Longrightarrow>
        _ \<subseteq> sources_out ?cs _ _ _ _")
  assumes
    B: "\<And>z. c = (IN z :: com_flow) \<Longrightarrow>
      y \<in> sources_out cs' ?vs' ?s' f x \<Longrightarrow>
        sources cs vs s f y \<subseteq> sources_out ?cs vs s f x" and
    C: "\<And>z. c = (OUT z :: com_flow) \<Longrightarrow>
      y \<in> sources_out cs' ?vs' ?s' f x \<Longrightarrow>
        sources cs vs s f y \<subseteq> sources_out ?cs vs s f x" and
    D: "\<And>X. c = \<langle>X\<rangle> \<Longrightarrow>
      y \<in> sources_out cs' ?vs' ?s' f x \<Longrightarrow>
        sources cs vs s f y \<subseteq> sources_out ?cs vs s f x"
  shows "y \<in> sources_out (cs' @ [c]) ?vs' ?s' f x \<Longrightarrow>
    sources cs vs s f y \<subseteq> sources_out (cs @ cs' @ [c]) vs s f x"
proof (subst (asm) sources_out.simps, split com_flow.split_asm)
  fix z a
  assume "c = z ::= a" and "y \<in> sources_out cs' ?vs' ?s' f x"
  moreover from this have "sources cs vs s f y \<subseteq> sources_out ?cs vs s f x"
    using A by simp
  ultimately show ?thesis
    by (simp only: append_assoc [symmetric] sources_out.simps, auto)
next
  fix z
  assume "c = IN z" and "y \<in> sources_out cs' ?vs' ?s' f x"
  moreover from this have "sources cs vs s f y \<subseteq> sources_out ?cs vs s f x"
    using B by simp
  ultimately show ?thesis
    by (simp only: append_assoc [symmetric] sources_out.simps, auto)
next
  fix z
  assume E: "c = OUT z"
  show "y \<in> sources_out cs' ?vs' ?s' f x \<union>
    (if z = x then sources cs' ?vs' ?s' f x else {}) \<Longrightarrow> ?thesis"
    (is "_ \<in> ?A \<union> (if _ then ?B else _) \<Longrightarrow> _")
  proof (split if_split_asm)
    assume "z = x" and "y \<in> ?A \<union> ?B"
    moreover {
      assume "y \<in> ?A"
      hence "sources cs vs s f y \<subseteq> sources_out ?cs vs s f x"
        using C and E by simp
    }
    moreover {
      assume "y \<in> ?B"
      hence "sources cs vs s f y \<subseteq> sources ?cs vs s f x"
        by (rule sources_member)
    }
    ultimately show ?thesis
      using E by (simp only: append_assoc [symmetric] sources_out.simps, auto)
  next
    assume "y \<in> ?A \<union> {}"
    moreover from this have "sources cs vs s f y \<subseteq> sources_out ?cs vs s f x"
      using C and E by simp
    ultimately show ?thesis
      using E by (simp only: append_assoc [symmetric] sources_out.simps, auto)
  qed
next
  fix X
  assume E: "c = \<langle>X\<rangle>"
  assume "y \<in> sources_out cs' ?vs' ?s' f x \<union> \<Union> {sources cs' ?vs' ?s' f w | w.
    run_flow cs' ?vs' ?s' f: dom w \<leadsto> dom x \<and> w \<in> X}"
    (is "_ \<in> ?A \<union> ?B")
  moreover {
    assume "y \<in> ?A"
    hence "sources cs vs s f y \<subseteq> sources_out ?cs vs s f x"
      using D and E by simp
  }
  moreover {
    assume "y \<in> ?B"
    hence "sources cs vs s f y \<subseteq> \<Union> {sources ?cs vs s f w | w.
      run_flow ?cs vs s f: dom w \<leadsto> dom x \<and> w \<in> X}"
      by (auto dest: sources_member simp: run_flow_append)
  }
  ultimately show ?thesis
    using E by (simp only: append_assoc [symmetric] sources_out.simps, auto)
qed

lemma sources_out_member:
 "y \<in> sources_out cs' (vs @ in_flow cs vs f) (run_flow cs vs s f) f x \<Longrightarrow>
    sources cs vs s f y \<subseteq> sources_out (cs @ cs') vs s f x"
by (induction cs' vs s f x rule: sources_out.induct,
 erule sources_out_member_1, simp_all)


lemma tags_member_1:
  assumes
    A: "\<And>z a. c = (z ::= a :: com_flow) \<Longrightarrow> z = x \<Longrightarrow>
      y \<in> sources_aux cs' (vs @ in_flow cs vs f) (run_flow cs vs s f) f x \<Longrightarrow>
        tags cs vs s f y \<subseteq> tags_aux (cs @ cs') vs s f x"
      (is "\<And>_ _. _ \<Longrightarrow> _ \<Longrightarrow> _ \<in> sources_aux _ ?vs' ?s' _ _ \<Longrightarrow>
        _ \<subseteq> tags_aux ?cs _ _ _ _")
  assumes
    B: "\<And>z a b w. c = (z ::= a :: com_flow) \<Longrightarrow> z = x \<Longrightarrow>
      y \<in> sources cs' ?vs' ?s' f w \<Longrightarrow>
        tags cs vs s f y \<subseteq> tags ?cs vs s f w" and
    C: "\<And>z a. c = (z ::= a :: com_flow) \<Longrightarrow> z \<noteq> x \<Longrightarrow>
      y \<in> sources cs' ?vs' ?s' f x \<Longrightarrow>
        tags cs vs s f y \<subseteq> tags ?cs vs s f x" and
    D: "\<And>z. c = (IN z :: com_flow) \<Longrightarrow> z = x \<Longrightarrow>
      y \<in> sources_aux cs' ?vs' ?s' f x \<Longrightarrow>
        tags cs vs s f y \<subseteq> tags_aux ?cs vs s f x" and
    E: "\<And>z. c = (IN z :: com_flow) \<Longrightarrow> z \<noteq> x \<Longrightarrow>
      y \<in> sources cs' ?vs' ?s' f x \<Longrightarrow>
        tags cs vs s f y \<subseteq> tags ?cs vs s f x" and
    F: "\<And>z. c = (OUT z :: com_flow) \<Longrightarrow>
      y \<in> sources cs' ?vs' ?s' f x \<Longrightarrow>
        tags cs vs s f y \<subseteq> tags ?cs vs s f x" and
    G: "\<And>X b w. c = \<langle>X\<rangle> \<Longrightarrow>
      y \<in> sources cs' ?vs' ?s' f w \<Longrightarrow>
        tags cs vs s f y \<subseteq> tags ?cs vs s f w"
  shows "y \<in> sources (cs' @ [c]) ?vs' ?s' f x \<Longrightarrow>
    tags cs vs s f y \<subseteq> tags (cs @ cs' @ [c]) vs s f x"
proof (subst (asm) sources.simps, split com_flow.split_asm)
  fix z a
  assume H: "c = z ::= a"
  show "y \<in> (if z = x
    then sources_aux cs' ?vs' ?s' f x \<union> \<Union> {sources cs' ?vs' ?s' f w | w.
      run_flow cs' ?vs' ?s' f: dom w \<leadsto> dom x \<and> w \<in> avars a}
    else sources cs' ?vs' ?s' f x) \<Longrightarrow> ?thesis"
    (is "_ \<in> (if _ then ?A \<union> ?B else ?C) \<Longrightarrow> _")
  proof (split if_split_asm)
    assume I: "z = x" and "y \<in> ?A \<union> ?B"
    moreover {
      assume "y \<in> ?A"
      hence "tags cs vs s f y \<subseteq> tags_aux ?cs vs s f x"
        using A and H and I by simp
    }
    moreover {
      assume "y \<in> ?B"
      hence "tags cs vs s f y \<subseteq> \<Union> {tags ?cs vs s f w | w.
        run_flow ?cs vs s f: dom w \<leadsto> dom x \<and> w \<in> avars a}"
        using B and H and I by (fastforce simp: run_flow_append)
    }
    ultimately show ?thesis
      using H by (simp only: append_assoc [symmetric] tags.simps, auto)
  next
    assume "z \<noteq> x" and "y \<in> ?C"
    moreover from this have "tags cs vs s f y \<subseteq> tags ?cs vs s f x"
      using C and H by simp
    ultimately show ?thesis
      using H by (simp only: append_assoc [symmetric] tags.simps, auto)
  qed
next
  fix z
  assume H: "c = IN z"
  show "y \<in> (if z = x
    then sources_aux cs' ?vs' ?s' f x
    else sources cs' ?vs' ?s' f x) \<Longrightarrow> ?thesis"
    (is "_ \<in> (if _ then ?A else ?B) \<Longrightarrow> _")
  proof (split if_split_asm)
    assume "z = x" and "y \<in> ?A"
    moreover from this have "tags cs vs s f y \<subseteq> tags_aux ?cs vs s f x"
      using D and H by simp
    ultimately show ?thesis
      using H by (simp only: append_assoc [symmetric] tags.simps, auto)
  next
    assume "z \<noteq> x" and "y \<in> ?B"
    moreover from this have "tags cs vs s f y \<subseteq> tags ?cs vs s f x"
      using E and H by simp
    ultimately show ?thesis
      using H by (simp only: append_assoc [symmetric] tags.simps, auto)
  qed
next
  fix z
  assume "c = OUT z" and "y \<in> sources cs' ?vs' ?s' f x"
  moreover from this have "tags cs vs s f y \<subseteq> tags ?cs vs s f x"
    using F by simp
  ultimately show ?thesis
    by (simp only: append_assoc [symmetric] tags.simps, auto)
next
  fix X
  assume H: "c = \<langle>X\<rangle>"
  assume "y \<in> sources cs' ?vs' ?s' f x \<union> \<Union> {sources cs' ?vs' ?s' f w | w.
    run_flow cs' ?vs' ?s' f: dom w \<leadsto> dom x \<and> w \<in> X}"
    (is "_ \<in> ?A \<union> ?B")
  moreover {
    assume "y \<in> ?A"
    hence "tags cs vs s f y \<subseteq> tags ?cs vs s f x"
      using G and H by simp
  }
  moreover {
    assume "y \<in> ?B"
    hence "tags cs vs s f y \<subseteq> \<Union> {tags ?cs vs s f w | w.
      run_flow ?cs vs s f: dom w \<leadsto> dom x \<and> w \<in> X}"
      using G and H by (auto simp: run_flow_append)
  }
  ultimately show ?thesis
    using H by (simp only: append_assoc [symmetric] tags.simps, auto)
qed

lemma tags_member_2:
  assumes
    A: "\<And>z a. c = (z ::= a :: com_flow) \<Longrightarrow>
      y \<in> sources_aux cs' (vs @ in_flow cs vs f) (run_flow cs vs s f) f x \<Longrightarrow>
        tags cs vs s f y \<subseteq> tags_aux (cs @ cs') vs s f x"
      (is "\<And>_ _. _ \<Longrightarrow> _ \<in> sources_aux _ ?vs' ?s' _ _ \<Longrightarrow>
        _ \<subseteq> tags_aux ?cs _ _ _ _")
  assumes
    B: "\<And>z. c = (IN z :: com_flow) \<Longrightarrow>
      y \<in> sources_aux cs' ?vs' ?s' f x \<Longrightarrow>
        tags cs vs s f y \<subseteq> tags_aux ?cs vs s f x" and
    C: "\<And>z. c = (OUT z :: com_flow) \<Longrightarrow>
      y \<in> sources_aux cs' ?vs' ?s' f x \<Longrightarrow>
        tags cs vs s f y \<subseteq> tags_aux ?cs vs s f x" and
    D: "\<And>X. c = \<langle>X\<rangle> \<Longrightarrow>
      y \<in> sources_aux cs' ?vs' ?s' f x \<Longrightarrow>
        tags cs vs s f y \<subseteq> tags_aux ?cs vs s f x" and
    E: "\<And>X b w. c = \<langle>X\<rangle> \<Longrightarrow>
      y \<in> sources cs' ?vs' ?s' f w \<Longrightarrow>
        tags cs vs s f y \<subseteq> tags ?cs vs s f w"
  shows "y \<in> sources_aux (cs' @ [c]) ?vs' ?s' f x \<Longrightarrow>
    tags cs vs s f y \<subseteq> tags_aux (cs @ cs' @ [c]) vs s f x"
proof (subst (asm) sources_aux.simps, split com_flow.split_asm)
  fix z a
  assume "c = z ::= a" and "y \<in> sources_aux cs' ?vs' ?s' f x"
  moreover from this have "tags cs vs s f y \<subseteq> tags_aux ?cs vs s f x"
    using A by simp
  ultimately show ?thesis
    by (simp only: append_assoc [symmetric] tags_aux.simps, auto)
next
  fix z
  assume "c = IN z" and "y \<in> sources_aux cs' ?vs' ?s' f x"
  moreover from this have "tags cs vs s f y \<subseteq> tags_aux ?cs vs s f x"
    using B by simp
  ultimately show ?thesis
    by (simp only: append_assoc [symmetric] tags_aux.simps, auto)
next
  fix z
  assume "c = OUT z" and "y \<in> sources_aux cs' ?vs' ?s' f x"
  moreover from this have "tags cs vs s f y \<subseteq> tags_aux ?cs vs s f x"
    using C by simp
  ultimately show ?thesis
    by (simp only: append_assoc [symmetric] tags_aux.simps, auto)
next
  fix X
  assume F: "c = \<langle>X\<rangle>"
  assume "y \<in> sources_aux cs' ?vs' ?s' f x \<union> \<Union> {sources cs' ?vs' ?s' f w | w.
    run_flow cs' ?vs' ?s' f: dom w \<leadsto> dom x \<and> w \<in> X}"
    (is "_ \<in> ?A \<union> ?B")
  moreover {
    assume "y \<in> ?A"
    hence "tags cs vs s f y \<subseteq> tags_aux ?cs vs s f x"
      using D and F by simp
  }
  moreover {
    assume "y \<in> ?B"
    hence "tags cs vs s f y \<subseteq> \<Union> {tags ?cs vs s f w | w.
      run_flow ?cs vs s f: dom w \<leadsto> dom x \<and> w \<in> X}"
      using E and F by (auto simp: run_flow_append)
  }
  ultimately show ?thesis
    using F by (simp only: append_assoc [symmetric] tags_aux.simps, auto)
qed

lemma tags_member:
 "y \<in> sources cs' (vs @ in_flow cs vs f) (run_flow cs vs s f) f x \<Longrightarrow>
    tags cs vs s f y \<subseteq> tags (cs @ cs') vs s f x"
and tags_aux_member:
 "y \<in> sources_aux cs' (vs @ in_flow cs vs f) (run_flow cs vs s f) f x \<Longrightarrow>
    tags cs vs s f y \<subseteq> tags_aux (cs @ cs') vs s f x"
by (induction cs' vs s f x and cs' vs s f x rule: tags_induct,
 erule_tac [3] tags_member_2, erule tags_member_1, simp_all)


lemma tags_out_member_1:
  assumes
    A: "\<And>z a. c = (z ::= a :: com_flow) \<Longrightarrow>
      y \<in> sources_out cs' (vs @ in_flow cs vs f) (run_flow cs vs s f) f x \<Longrightarrow>
        tags cs vs s f y \<subseteq> tags_out (cs @ cs') vs s f x"
      (is "\<And>_ _. _ \<Longrightarrow> _ \<in> sources_out _ ?vs' ?s' _ _ \<Longrightarrow>
        _ \<subseteq> tags_out ?cs _ _ _ _")
  assumes
    B: "\<And>z. c = (IN z :: com_flow) \<Longrightarrow>
      y \<in> sources_out cs' ?vs' ?s' f x \<Longrightarrow>
        tags cs vs s f y \<subseteq> tags_out ?cs vs s f x" and
    C: "\<And>z. c = (OUT z :: com_flow) \<Longrightarrow>
      y \<in> sources_out cs' ?vs' ?s' f x \<Longrightarrow>
        tags cs vs s f y \<subseteq> tags_out ?cs vs s f x" and
    D: "\<And>X. c = \<langle>X\<rangle> \<Longrightarrow>
      y \<in> sources_out cs' ?vs' ?s' f x \<Longrightarrow>
        tags cs vs s f y \<subseteq> tags_out ?cs vs s f x"
  shows "y \<in> sources_out (cs' @ [c]) ?vs' ?s' f x \<Longrightarrow>
    tags cs vs s f y \<subseteq> tags_out (cs @ cs' @ [c]) vs s f x"
proof (subst (asm) sources_out.simps, split com_flow.split_asm)
  fix z a
  assume "c = z ::= a" and "y \<in> sources_out cs' ?vs' ?s' f x"
  moreover from this have "tags cs vs s f y \<subseteq> tags_out ?cs vs s f x"
    using A by simp
  ultimately show ?thesis
    by (simp only: append_assoc [symmetric] tags_out.simps, auto)
next
  fix z
  assume "c = IN z" and "y \<in> sources_out cs' ?vs' ?s' f x"
  moreover from this have "tags cs vs s f y \<subseteq> tags_out ?cs vs s f x"
    using B by simp
  ultimately show ?thesis
    by (simp only: append_assoc [symmetric] tags_out.simps, auto)
next
  fix z
  assume E: "c = OUT z"
  show "y \<in> sources_out cs' ?vs' ?s' f x \<union>
    (if z = x then sources cs' ?vs' ?s' f x else {}) \<Longrightarrow> ?thesis"
    (is "_ \<in> ?A \<union> (if _ then ?B else _) \<Longrightarrow> _")
  proof (split if_split_asm)
    assume "z = x" and "y \<in> ?A \<union> ?B"
    moreover {
      assume "y \<in> ?A"
      hence "tags cs vs s f y \<subseteq> tags_out ?cs vs s f x"
        using C and E by simp
    }
    moreover {
      assume "y \<in> ?B"
      hence "tags cs vs s f y \<subseteq> tags ?cs vs s f x"
        by (rule tags_member)
    }
    ultimately show ?thesis
      using E by (simp only: append_assoc [symmetric] tags_out.simps, auto)
  next
    assume "y \<in> ?A \<union> {}"
    moreover from this have "tags cs vs s f y \<subseteq> tags_out ?cs vs s f x"
      using C and E by simp
    ultimately show ?thesis
      using E by (simp only: append_assoc [symmetric] tags_out.simps, auto)
  qed
next
  fix X
  assume E: "c = \<langle>X\<rangle>"
  assume "y \<in> sources_out cs' ?vs' ?s' f x \<union> \<Union> {sources cs' ?vs' ?s' f w | w.
    run_flow cs' ?vs' ?s' f: dom w \<leadsto> dom x \<and> w \<in> X}"
    (is "_ \<in> ?A \<union> ?B")
  moreover {
    assume "y \<in> ?A"
    hence "tags cs vs s f y \<subseteq> tags_out ?cs vs s f x"
      using D and E by simp
  }
  moreover {
    assume "y \<in> ?B"
    hence "tags cs vs s f y \<subseteq> \<Union> {tags ?cs vs s f w | w.
      run_flow ?cs vs s f: dom w \<leadsto> dom x \<and> w \<in> X}"
      by (auto dest: tags_member simp: run_flow_append)
  }
  ultimately show ?thesis
    using E by (simp only: append_assoc [symmetric] tags_out.simps, auto)
qed

lemma tags_out_member:
 "y \<in> sources_out cs' (vs @ in_flow cs vs f) (run_flow cs vs s f) f x \<Longrightarrow>
    tags cs vs s f y \<subseteq> tags_out (cs @ cs') vs s f x"
by (induction cs' vs s f x rule: tags_out.induct,
 erule tags_out_member_1, simp_all)


lemma tags_suffix_1:
  assumes
    A: "\<And>z a. c = (z ::= a :: com_flow) \<Longrightarrow> z = x \<Longrightarrow>
      tags_aux cs' (vs @ in_flow cs vs f) (run_flow cs vs s f) f x =
      {p. case p of (w, n) \<Rightarrow> (w, length [c\<leftarrow>cs. c = IN w] + n)
        \<in> tags_aux (cs @ cs') vs s f x}"
      (is "\<And>_ _. _ \<Longrightarrow> _ \<Longrightarrow> tags_aux _ ?vs' ?s' _ _ = _")
  assumes
    B: "\<And>z a b y. c = (z ::= a :: com_flow) \<Longrightarrow> z = x \<Longrightarrow>
      tags cs' ?vs' ?s' f y =
      {p. case p of (w, n) \<Rightarrow> (w, length [c\<leftarrow>cs. c = IN w] + n)
        \<in> tags (cs @ cs') vs s f y}" and
    C: "\<And>z a. c = (z ::= a :: com_flow) \<Longrightarrow> z \<noteq> x \<Longrightarrow>
      tags cs' ?vs' ?s' f x =
      {p. case p of (w, n) \<Rightarrow> (w, length [c\<leftarrow>cs. c = IN w] + n)
        \<in> tags (cs @ cs') vs s f x}" and
    D: "\<And>z. c = (IN z :: com_flow) \<Longrightarrow> z = x \<Longrightarrow>
      tags_aux cs' ?vs' ?s' f x =
      {p. case p of (w, n) \<Rightarrow> (w, length [c\<leftarrow>cs. c = IN w] + n)
        \<in> tags_aux (cs @ cs') vs s f x}" and
    E: "\<And>z. c = (IN z :: com_flow) \<Longrightarrow> z \<noteq> x \<Longrightarrow>
      tags cs' ?vs' ?s' f x =
      {p. case p of (w, n) \<Rightarrow> (w, length [c\<leftarrow>cs. c = IN w] + n)
        \<in> tags (cs @ cs') vs s f x}" and
    F: "\<And>z. c = (OUT z :: com_flow) \<Longrightarrow>
      tags cs' ?vs' ?s' f x =
      {p. case p of (w, n) \<Rightarrow> (w, length [c\<leftarrow>cs. c = IN w] + n)
        \<in> tags (cs @ cs') vs s f x}" and
    G: "\<And>X b y. c = \<langle>X\<rangle> \<Longrightarrow>
      tags cs' ?vs' ?s' f y =
      {p. case p of (w, n) \<Rightarrow> (w, length [c\<leftarrow>cs. c = IN w] + n)
        \<in> tags (cs @ cs') vs s f y}"
  shows "tags (cs' @ [c]) ?vs' ?s' f x =
    {p. case p of (w, n) \<Rightarrow> (w, length [c\<leftarrow>cs. c = IN w] + n)
      \<in> tags (cs @ cs' @ [c]) vs s f x}"
    (is "_ = {p. case p of (w, n) \<Rightarrow> ?P w n c}")
  apply (subst tags.simps)
  apply (split com_flow.split)
  apply (rule conjI)
  subgoal
  proof -
    show "\<forall>z a. c = z ::= a \<longrightarrow> (if z = x
      then tags_aux cs' ?vs' ?s' f x \<union> \<Union> {tags cs' ?vs' ?s' f y | y.
        run_flow cs' ?vs' ?s' f: dom y \<leadsto> dom x \<and> y \<in> avars a}
      else tags cs' ?vs' ?s' f x) =
      {(w, n). ?P w n c}"
      (is "\<forall>_ a. _ \<longrightarrow> (if _ then ?A \<union> ?F a else ?B) = _")
      apply clarify
      apply (split if_split)
      apply (rule conjI)
      subgoal for z a
      proof
        assume H: "z = x" and I: "c = z ::= a"
        hence "?A = {(w, n). (w, length [c\<leftarrow>cs. c = IN w] + n)
          \<in> tags_aux (cs @ cs') vs s f x}"
          using A by simp
        moreover have "\<forall>y. tags cs' ?vs' ?s' f y = {(w, n).
          (w, length [c\<leftarrow>cs. c = IN w] + n) \<in> tags (cs @ cs') vs s f y}"
          using B and H and I by simp
        hence "?F a = {(w, n). (w, length [c\<leftarrow>cs. c = IN w] + n)
          \<in> \<Union> {tags (cs @ cs') vs s f y | y.
            run_flow cs' ?vs' ?s' f: dom y \<leadsto> dom x \<and> y \<in> avars a}}"
          by blast
        ultimately show "?A \<union> ?F a = {(w, n). ?P w n (z ::= a)}"
          using H by (subst append_assoc [symmetric], subst tags.simps,
           auto simp: run_flow_append)
      qed
      subgoal for z a
      proof
        assume "z \<noteq> x" and "c = z ::= a"
        moreover from this have "?B = {(w, n).
          (w, length [c\<leftarrow>cs. c = IN w] + n) \<in> tags (cs @ cs') vs s f x}"
          using C by simp
        ultimately show "?B = {(w, n). ?P w n (z ::= a)}"
          by (subst append_assoc [symmetric], subst tags.simps, simp)
      qed
      done
  qed
  apply (rule conjI)
  subgoal
  proof -
    show "\<forall>z. c = IN z \<longrightarrow> (if z = x
      then insert (x, length [c\<leftarrow>cs'. c = IN x]) (tags_aux cs' ?vs' ?s' f x)
      else tags cs' ?vs' ?s' f x) =
      {(w, n). ?P w n c}"
      (is "\<forall>_. _ \<longrightarrow> (if _ then insert ?p ?A else ?B) = _")
      apply clarify
      apply (split if_split)
      apply (rule conjI)
      subgoal for z
      proof
        assume "z = x" and "c = IN z"
        moreover from this have "?A = {(w, n).
          (w, length [c\<leftarrow>cs. c = IN w] + n) \<in> tags_aux (cs @ cs') vs s f x}"
          using D by simp
        ultimately show "insert ?p ?A = {(w, n). ?P w n (IN z)}"
          by (subst append_assoc [symmetric], subst tags.simps, auto)
      qed
      subgoal for z
      proof
        assume "z \<noteq> x" and "c = IN z"
        moreover from this have "?B = {(w, n).
          (w, length [c\<leftarrow>cs. c = IN w] + n) \<in> tags (cs @ cs') vs s f x}"
          using E by simp
        ultimately show "?B = {(w, n). ?P w n (IN z)}"
          by (subst append_assoc [symmetric], subst tags.simps, simp)
      qed
      done
  qed
  apply (rule conjI)
  subgoal by (subst append_assoc [symmetric], subst tags.simps, simp add: F)
  subgoal
  proof -
    show "\<forall>X. c = \<langle>X\<rangle> \<longrightarrow>
      tags cs' ?vs' ?s' f x \<union> \<Union> {tags cs' ?vs' ?s' f y | y.
        run_flow cs' ?vs' ?s' f: dom y \<leadsto> dom x \<and> y \<in> X} =
      {(w, n). ?P w n c}"
      (is "\<forall>X. _ \<longrightarrow> ?A \<union> ?F X = _")
    proof clarify
      fix X
      assume H: "c = \<langle>X\<rangle>"
      hence "?A = {(w, n). (w, length [c\<leftarrow>cs. c = IN w] + n)
        \<in> tags (cs @ cs') vs s f x}"
        using G by simp
      moreover have "\<forall>y. tags cs' ?vs' ?s' f y = {(w, n).
        (w, length [c\<leftarrow>cs. c = IN w] + n) \<in> tags (cs @ cs') vs s f y}"
        using G and H by simp
      hence "?F X = {(w, n). (w, length [c\<leftarrow>cs. c = IN w] + n)
        \<in> \<Union> {tags (cs @ cs') vs s f y | y.
          run_flow cs' ?vs' ?s' f: dom y \<leadsto> dom x \<and> y \<in> X}}"
        by blast
      ultimately show "?A \<union> ?F X = {(w, n). ?P w n (\<langle>X\<rangle>)}"
        by (subst append_assoc [symmetric], subst tags.simps,
         auto simp: run_flow_append)
    qed
  qed
  done

lemma tags_suffix_2:
  assumes
    A: "\<And>z a. c = (z ::= a :: com_flow) \<Longrightarrow>
      tags_aux cs' (vs @ in_flow cs vs f) (run_flow cs vs s f) f x =
      {p. case p of (w, n) \<Rightarrow> (w, length [c\<leftarrow>cs. c = IN w] + n)
        \<in> tags_aux (cs @ cs') vs s f x}"
      (is "\<And>_ _. _ \<Longrightarrow> tags_aux _ ?vs' ?s' _ _ = _")
  assumes
    B: "\<And>z. c = (IN z :: com_flow) \<Longrightarrow>
      tags_aux cs' ?vs' ?s' f x =
      {p. case p of (w, n) \<Rightarrow> (w, length [c\<leftarrow>cs. c = IN w] + n)
        \<in> tags_aux (cs @ cs') vs s f x}" and
    C: "\<And>z. c = (OUT z :: com_flow) \<Longrightarrow>
      tags_aux cs' ?vs' ?s' f x =
      {p. case p of (w, n) \<Rightarrow> (w, length [c\<leftarrow>cs. c = IN w] + n)
        \<in> tags_aux (cs @ cs') vs s f x}" and
    D: "\<And>X. c = \<langle>X\<rangle> \<Longrightarrow>
      tags_aux cs' ?vs' ?s' f x =
      {p. case p of (w, n) \<Rightarrow> (w, length [c\<leftarrow>cs. c = IN w] + n)
        \<in> tags_aux (cs @ cs') vs s f x}" and
    E: "\<And>X b y. c = \<langle>X\<rangle> \<Longrightarrow>
      tags cs' ?vs' ?s' f y =
      {p. case p of (w, n) \<Rightarrow> (w, length [c\<leftarrow>cs. c = IN w] + n)
        \<in> tags (cs @ cs') vs s f y}"
  shows "tags_aux (cs' @ [c]) ?vs' ?s' f x =
    {p. case p of (w, n) \<Rightarrow> (w, length [c\<leftarrow>cs. c = IN w] + n)
      \<in> tags_aux (cs @ cs' @ [c]) vs s f x}"
    (is "_ = {p. case p of (w, n) \<Rightarrow> ?P w n c}")
  apply (subst tags_aux.simps)
  apply (split com_flow.split)
  apply (rule conjI)
   defer
   apply (rule conjI)
    defer
    apply (rule conjI)
     defer
  subgoal
  proof -
    show "\<forall>X. c = \<langle>X\<rangle> \<longrightarrow>
      tags_aux cs' ?vs' ?s' f x \<union> \<Union> {tags cs' ?vs' ?s' f y | y.
        run_flow cs' ?vs' ?s' f: dom y \<leadsto> dom x \<and> y \<in> X} =
      {(w, n). ?P w n c}"
      (is "\<forall>X. _ \<longrightarrow> ?A \<union> ?F X = _")
    proof clarify
      fix X
      assume F: "c = \<langle>X\<rangle>"
      hence "?A = {(w, n). (w, length [c\<leftarrow>cs. c = IN w] + n)
        \<in> tags_aux (cs @ cs') vs s f x}"
        using D by simp
      moreover have "\<forall>y. tags cs' ?vs' ?s' f y = {(w, n).
        (w, length [c\<leftarrow>cs. c = IN w] + n) \<in> tags (cs @ cs') vs s f y}"
        using E and F by simp
      hence "?F X = {(w, n). (w, length [c\<leftarrow>cs. c = IN w] + n)
        \<in> \<Union> {tags (cs @ cs') vs s f y | y.
          run_flow cs' ?vs' ?s' f: dom y \<leadsto> dom x \<and> y \<in> X}}"
        by blast
      ultimately show "?A \<union> ?F X = {(w, n). ?P w n (\<langle>X\<rangle>)}"
        by (subst append_assoc [symmetric], subst tags_aux.simps,
         auto simp: run_flow_append)
    qed
  qed
by (subst append_assoc [symmetric], subst tags_aux.simps, simp add: A B C)+

lemma tags_suffix:
 "tags cs' (vs @ in_flow cs vs f) (run_flow cs vs s f) f x = {(w, n).
    (w, length [c\<leftarrow>cs. c = IN w] + n) \<in> tags (cs @ cs') vs s f x}"
and tags_aux_suffix:
 "tags_aux cs' (vs @ in_flow cs vs f) (run_flow cs vs s f) f x = {(w, n).
    (w, length [c\<leftarrow>cs. c = IN w] + n) \<in> tags_aux (cs @ cs') vs s f x}"
by (induction cs' vs s f x and cs' vs s f x rule: tags_induct,
 erule_tac [3] tags_suffix_2, erule tags_suffix_1, simp_all
 add: tags_ubound tags_aux_ubound)


lemma tags_out_suffix_1:
  assumes
    A: "\<And>z a. c = (z ::= a :: com_flow) \<Longrightarrow>
      tags_out cs' (vs @ in_flow cs vs f) (run_flow cs vs s f) f x =
      {p. case p of (w, n) \<Rightarrow> (w, length [c\<leftarrow>cs. c = IN w] + n)
        \<in> tags_out (cs @ cs') vs s f x}"
      (is "\<And>_ _. _ \<Longrightarrow> tags_out _ ?vs' ?s' _ _ = _")
  assumes
    B: "\<And>z. c = (IN z :: com_flow) \<Longrightarrow>
      tags_out cs' ?vs' ?s' f x =
      {p. case p of (w, n) \<Rightarrow> (w, length [c\<leftarrow>cs. c = IN w] + n)
        \<in> tags_out (cs @ cs') vs s f x}" and
    C: "\<And>z. c = (OUT z :: com_flow) \<Longrightarrow>
      tags_out cs' ?vs' ?s' f x =
      {p. case p of (w, n) \<Rightarrow> (w, length [c\<leftarrow>cs. c = IN w] + n)
        \<in> tags_out (cs @ cs') vs s f x}" and
    D: "\<And>X. c = \<langle>X\<rangle> \<Longrightarrow>
      tags_out cs' ?vs' ?s' f x =
      {p. case p of (w, n) \<Rightarrow> (w, length [c\<leftarrow>cs. c = IN w] + n)
        \<in> tags_out (cs @ cs') vs s f x}"
  shows "tags_out (cs' @ [c]) ?vs' ?s' f x =
    {p. case p of (w, n) \<Rightarrow> (w, length [c\<leftarrow>cs. c = IN w] + n)
      \<in> tags_out (cs @ cs' @ [c]) vs s f x}"
    (is "_ = {p. case p of (w, n) \<Rightarrow> ?P w n c}")
  apply (subst tags_out.simps)
  apply (split com_flow.split)
  apply (rule conjI)
   defer
   apply (rule conjI)
    defer
  subgoal
  proof
    show "\<forall>z. c = OUT z \<longrightarrow>
      tags_out cs' ?vs' ?s' f x \<union>
        (if z = x then tags cs' ?vs' ?s' f x else {}) =
      {(w, n). ?P w n c}"
      (is "\<forall>_. _ \<longrightarrow> ?A \<union> (if _ then ?B else _) = _")
      apply clarify
      apply (split if_split)
      apply (rule conjI)
      subgoal for z
      proof
        assume "c = OUT z" and "z = x"
        moreover from this have "?A = {p. case p of (w, n) \<Rightarrow>
          (w, length [c\<leftarrow>cs. c = IN w] + n) \<in> tags_out (cs @ cs') vs s f x}"
          using C by simp
        moreover have "?B = {(w, n).
          (w, length [c\<leftarrow>cs. c = IN w] + n) \<in> tags (cs @ cs') vs s f x}"
          by (rule tags_suffix)
        ultimately show "?A \<union> ?B = {(w, n). ?P w n (OUT z)}"
          by (subst append_assoc [symmetric], subst tags_out.simps, auto)
      qed
      subgoal for z
      proof
        assume "c = OUT z" and "z \<noteq> x"
        moreover from this have "?A = {p. case p of (w, n) \<Rightarrow>
          (w, length [c\<leftarrow>cs. c = IN w] + n) \<in> tags_out (cs @ cs') vs s f x}"
          using C by simp
        ultimately show "?A \<union> {} = {(w, n). ?P w n (OUT z)}"
          by (subst append_assoc [symmetric], subst tags_out.simps, simp)
      qed
      done
  next
    show "\<forall>X. c = \<langle>X\<rangle> \<longrightarrow>
      tags_out cs' ?vs' ?s' f x \<union> \<Union> {tags cs' ?vs' ?s' f y | y.
        run_flow cs' ?vs' ?s' f: dom y \<leadsto> dom x \<and> y \<in> X} =
      {(w, n). ?P w n c}"
      (is "\<forall>X. _ \<longrightarrow> ?A \<union> ?F X = _")
    proof clarify
      fix X
      assume "c = \<langle>X\<rangle>"
      hence "?A = {(w, n). (w, length [c\<leftarrow>cs. c = IN w] + n)
        \<in> tags_out (cs @ cs') vs s f x}"
        using D by simp
      moreover have "\<forall>y. tags cs' ?vs' ?s' f y = {(w, n).
        (w, length [c\<leftarrow>cs. c = IN w] + n) \<in> tags (cs @ cs') vs s f y}"
        by (blast intro!: tags_suffix)
      hence "?F X = {(w, n). (w, length [c\<leftarrow>cs. c = IN w] + n)
        \<in> \<Union> {tags (cs @ cs') vs s f y | y.
          run_flow cs' ?vs' ?s' f: dom y \<leadsto> dom x \<and> y \<in> X}}"
        by blast
      ultimately show "?A \<union> ?F X = {(w, n). ?P w n (\<langle>X\<rangle>)}"
        by (subst append_assoc [symmetric], subst tags_out.simps,
         auto simp: run_flow_append)
    qed
  qed
by (subst append_assoc [symmetric], subst tags_out.simps, simp add: A B)+

lemma tags_out_suffix:
 "tags_out cs' (vs @ in_flow cs vs f) (run_flow cs vs s f) f x = {(w, n).
    (w, length [c\<leftarrow>cs. c = IN w] + n) \<in> tags_out (cs @ cs') vs s f x}"
by (induction cs' vs s f x rule: tags_out.induct,
 erule tags_out_suffix_1, simp_all add: tags_out_ubound)


lemma sources_aux_rhs:
  assumes
    A: "S \<subseteq> {x. s\<^sub>1 = t\<^sub>1 (\<subseteq> sources_aux (flow cfs @ cs') vs\<^sub>1 s\<^sub>1 f x)}"
      (is "_ \<subseteq> {_. _ = _ (\<subseteq> sources_aux (?cs @ _) _ _ _ _)}")
  assumes
    B: "f = f' (\<subseteq> vs\<^sub>1, vs\<^sub>1',
      \<Union> {tags_aux (?cs @ cs') vs\<^sub>1 s\<^sub>1 f x | x. x \<in> S})" and
    C: "(c\<^sub>1, s\<^sub>1, f, vs\<^sub>1, ws\<^sub>1) \<rightarrow>*{cfs} (c\<^sub>2, s\<^sub>2, f, vs\<^sub>2, ws\<^sub>2)" and
    D: "ok_flow_aux_2 s\<^sub>1 s\<^sub>2 t\<^sub>1 t\<^sub>2 f f' vs\<^sub>1 vs\<^sub>1' ?cs"
  shows "S \<subseteq> {x. s\<^sub>2 = t\<^sub>2 (\<subseteq> sources_aux cs' vs\<^sub>2 s\<^sub>2 f x)}"
proof clarify
  fix x y
  assume E: "y \<in> sources_aux cs' vs\<^sub>2 s\<^sub>2 f x"
  moreover have F: "s\<^sub>2 = run_flow ?cs vs\<^sub>1 s\<^sub>1 f"
    using C by (rule small_stepsl_run_flow)
  moreover have G: "vs\<^sub>2 = vs\<^sub>1 @ in_flow ?cs vs\<^sub>1 f"
    using C by (rule small_stepsl_in_flow)
  ultimately have "sources ?cs vs\<^sub>1 s\<^sub>1 f y \<subseteq> sources_aux (?cs @ cs') vs\<^sub>1 s\<^sub>1 f x"
    by (blast dest: sources_aux_member)
  moreover assume H: "x \<in> S"
  ultimately have "s\<^sub>1 = t\<^sub>1 (\<subseteq> sources ?cs vs\<^sub>1 s\<^sub>1 f y)"
    using A by blast
  moreover have "tags ?cs vs\<^sub>1 s\<^sub>1 f y \<subseteq> tags_aux (?cs @ cs') vs\<^sub>1 s\<^sub>1 f x"
    using E and F and G by (blast dest: tags_aux_member)
  hence "tags ?cs vs\<^sub>1 s\<^sub>1 f y \<subseteq> \<Union> {tags_aux (?cs @ cs') vs\<^sub>1 s\<^sub>1 f x | x. x \<in> S}"
    using H by blast
  with B have "f = f' (\<subseteq> vs\<^sub>1, vs\<^sub>1', tags ?cs vs\<^sub>1 s\<^sub>1 f y)"
    by (rule eq_streams_subset)
  ultimately show "s\<^sub>2 y = t\<^sub>2 y"
    using D [rule_format, of "{y}"] by simp
qed

lemma sources_rhs:
  assumes
    A: "S \<subseteq> {x. s\<^sub>1 = t\<^sub>1 (\<subseteq> sources (flow cfs @ cs') vs\<^sub>1 s\<^sub>1 f x)}"
      (is "_ \<subseteq> {_. _ = _ (\<subseteq> sources (?cs @ _) _ _ _ _)}")
  assumes
    B: "f = f' (\<subseteq> vs\<^sub>1, vs\<^sub>1',
      \<Union> {tags (?cs @ cs') vs\<^sub>1 s\<^sub>1 f x | x. x \<in> S})" and
    C: "(c\<^sub>1, s\<^sub>1, f, vs\<^sub>1, ws\<^sub>1) \<rightarrow>*{cfs} (c\<^sub>2, s\<^sub>2, f, vs\<^sub>2, ws\<^sub>2)" and
    D: "ok_flow_aux_2 s\<^sub>1 s\<^sub>2 t\<^sub>1 t\<^sub>2 f f' vs\<^sub>1 vs\<^sub>1' ?cs"
  shows "S \<subseteq> {x. s\<^sub>2 = t\<^sub>2 (\<subseteq> sources cs' vs\<^sub>2 s\<^sub>2 f x)}"
proof clarify
  fix x y
  assume E: "y \<in> sources cs' vs\<^sub>2 s\<^sub>2 f x"
  moreover have F: "s\<^sub>2 = run_flow ?cs vs\<^sub>1 s\<^sub>1 f"
    using C by (rule small_stepsl_run_flow)
  moreover have G: "vs\<^sub>2 = vs\<^sub>1 @ in_flow ?cs vs\<^sub>1 f"
    using C by (rule small_stepsl_in_flow)
  ultimately have "sources ?cs vs\<^sub>1 s\<^sub>1 f y \<subseteq> sources (?cs @ cs') vs\<^sub>1 s\<^sub>1 f x"
    by (blast dest: sources_member)
  moreover assume H: "x \<in> S"
  ultimately have "s\<^sub>1 = t\<^sub>1 (\<subseteq> sources ?cs vs\<^sub>1 s\<^sub>1 f y)"
    using A by blast
  moreover have "tags ?cs vs\<^sub>1 s\<^sub>1 f y \<subseteq> tags (?cs @ cs') vs\<^sub>1 s\<^sub>1 f x"
    using E and F and G by (blast dest: tags_member)
  hence "tags ?cs vs\<^sub>1 s\<^sub>1 f y \<subseteq> \<Union> {tags (?cs @ cs') vs\<^sub>1 s\<^sub>1 f x | x. x \<in> S}"
    using H by blast
  with B have "f = f' (\<subseteq> vs\<^sub>1, vs\<^sub>1', tags ?cs vs\<^sub>1 s\<^sub>1 f y)"
    by (rule eq_streams_subset)
  ultimately show "s\<^sub>2 y = t\<^sub>2 y"
    using D [rule_format, of "{y}"] by simp
qed

lemma sources_out_rhs:
  assumes
    A: "S \<subseteq> {x. s\<^sub>1 = t\<^sub>1 (\<subseteq> sources_out (flow cfs @ cs') vs\<^sub>1 s\<^sub>1 f x)}"
      (is "_ \<subseteq> {_. _ = _ (\<subseteq> sources_out (?cs @ _) _ _ _ _)}")
  assumes
    B: "f = f' (\<subseteq> vs\<^sub>1, vs\<^sub>1',
      \<Union> {tags_out (?cs @ cs') vs\<^sub>1 s\<^sub>1 f x | x. x \<in> S})" and
    C: "(c\<^sub>1, s\<^sub>1, f, vs\<^sub>1, ws\<^sub>1) \<rightarrow>*{cfs} (c\<^sub>2, s\<^sub>2, f, vs\<^sub>2, ws\<^sub>2)" and
    D: "ok_flow_aux_2 s\<^sub>1 s\<^sub>2 t\<^sub>1 t\<^sub>2 f f' vs\<^sub>1 vs\<^sub>1' ?cs"
  shows "S \<subseteq> {x. s\<^sub>2 = t\<^sub>2 (\<subseteq> sources_out cs' vs\<^sub>2 s\<^sub>2 f x)}"
proof clarify
  fix x y
  assume E: "y \<in> sources_out cs' vs\<^sub>2 s\<^sub>2 f x"
  moreover have F: "s\<^sub>2 = run_flow ?cs vs\<^sub>1 s\<^sub>1 f"
    using C by (rule small_stepsl_run_flow)
  moreover have G: "vs\<^sub>2 = vs\<^sub>1 @ in_flow ?cs vs\<^sub>1 f"
    using C by (rule small_stepsl_in_flow)
  ultimately have "sources ?cs vs\<^sub>1 s\<^sub>1 f y \<subseteq> sources_out (?cs @ cs') vs\<^sub>1 s\<^sub>1 f x"
    by (blast dest: sources_out_member)
  moreover assume H: "x \<in> S"
  ultimately have "s\<^sub>1 = t\<^sub>1 (\<subseteq> sources ?cs vs\<^sub>1 s\<^sub>1 f y)"
    using A by blast
  moreover have "tags ?cs vs\<^sub>1 s\<^sub>1 f y \<subseteq> tags_out (?cs @ cs') vs\<^sub>1 s\<^sub>1 f x"
    using E and F and G by (blast dest: tags_out_member)
  hence "tags ?cs vs\<^sub>1 s\<^sub>1 f y \<subseteq> \<Union> {tags_out (?cs @ cs') vs\<^sub>1 s\<^sub>1 f x | x. x \<in> S}"
    using H by blast
  with B have "f = f' (\<subseteq> vs\<^sub>1, vs\<^sub>1', tags ?cs vs\<^sub>1 s\<^sub>1 f y)"
    by (rule eq_streams_subset)
  ultimately show "s\<^sub>2 y = t\<^sub>2 y"
    using D [rule_format, of "{y}"] by simp
qed


lemma tags_aux_rhs:
  assumes
    A: "S \<subseteq> {x. s\<^sub>1 = t\<^sub>1 (\<subseteq> sources_aux (flow cfs @ cs') vs\<^sub>1 s\<^sub>1 f x)}"
      (is "_ \<subseteq> {_. _ = _ (\<subseteq> sources_aux (?cs @ _) _ _ _ _)}")
  assumes
    B: "f = f' (\<subseteq> vs\<^sub>1, vs\<^sub>1',
      \<Union> {tags_aux (?cs @ cs') vs\<^sub>1 s\<^sub>1 f x | x. x \<in> S})" and
    C: "(c\<^sub>1, s\<^sub>1, f, vs\<^sub>1, ws\<^sub>1) \<rightarrow>*{cfs} (c\<^sub>2, s\<^sub>2, f, vs\<^sub>2, ws\<^sub>2)" and
    D: "(c\<^sub>1', t\<^sub>1, f', vs\<^sub>1', ws\<^sub>1') \<rightarrow>* (c\<^sub>2', t\<^sub>2, f', vs\<^sub>2', ws\<^sub>2')" and
    E: "ok_flow_aux_1 c\<^sub>1 c\<^sub>2 c\<^sub>2' s\<^sub>1 t\<^sub>1 t\<^sub>2 f f' vs\<^sub>1 vs\<^sub>1' vs\<^sub>2 vs\<^sub>2' ws\<^sub>1' ws\<^sub>2' ?cs"
  shows "f = f' (\<subseteq> vs\<^sub>2, vs\<^sub>2', \<Union> {tags_aux cs' vs\<^sub>2 s\<^sub>2 f x | x. x \<in> S})"
proof (subst eq_streams_def, clarify)
  fix x y n
  have F: "vs\<^sub>2 = vs\<^sub>1 @ drop (length vs\<^sub>1) vs\<^sub>2"
    using small_stepsl_steps [OF C] by (rule small_steps_in_flow)
  have G: "vs\<^sub>2' = vs\<^sub>1' @ drop (length vs\<^sub>1') vs\<^sub>2'"
    using D by (rule small_steps_in_flow)
  assume "(y, n) \<in> tags_aux cs' vs\<^sub>2 s\<^sub>2 f x"
  moreover have "s\<^sub>2 = run_flow ?cs vs\<^sub>1 s\<^sub>1 f"
    using C by (rule small_stepsl_run_flow)
  moreover have H: "vs\<^sub>2 = vs\<^sub>1 @ in_flow ?cs vs\<^sub>1 f"
    using C by (rule small_stepsl_in_flow)
  ultimately have I: "(y, length [c\<leftarrow>?cs. c = IN y] + n)
    \<in> tags_aux (?cs @ cs') vs\<^sub>1 s\<^sub>1 f x"
    (is "(_, ?k + _) \<in> _")
    by (simp add: tags_aux_suffix)
  let ?m = "Suc (Max {k. k \<le> length (?cs @ cs') \<and>
    length [c\<leftarrow>take k (?cs @ cs'). c = IN y] \<le> ?k + n})"
  have J: "y \<in> sources_aux (drop ?m (?cs @ cs'))
    (vs\<^sub>1 @ in_flow (take ?m (?cs @ cs')) vs\<^sub>1 f)
    (run_flow (take ?m (?cs @ cs')) vs\<^sub>1 s\<^sub>1 f) f x"
    using I by (auto dest: tags_aux_sources_aux)
  hence "sources (take ?m (?cs @ cs')) vs\<^sub>1 s\<^sub>1 f y \<subseteq>
    sources_aux (take ?m (?cs @ cs') @ drop ?m (?cs @ cs')) vs\<^sub>1 s\<^sub>1 f x"
    by (rule sources_aux_member)
  moreover have K: "length ?cs \<le> ?m"
    by (rule le_SucI, rule Max_ge, simp_all)
  ultimately have
   "sources (?cs @ take (?m - length ?cs) cs') vs\<^sub>1 s\<^sub>1 f y \<subseteq>
    sources_aux (?cs @ cs') vs\<^sub>1 s\<^sub>1 f x"
    by simp
  moreover have
   "sources_aux (?cs @ take (?m - length ?cs) cs') vs\<^sub>1 s\<^sub>1 f y \<subseteq>
    sources (?cs @ take (?m - length ?cs) cs') vs\<^sub>1 s\<^sub>1 f y"
    by (rule sources_aux_sources)
  moreover have "sources_aux ?cs vs\<^sub>1 s\<^sub>1 f y \<subseteq>
    sources_aux (?cs @ take (?m - length ?cs) cs') vs\<^sub>1 s\<^sub>1 f y"
    by (rule sources_aux_append)
  moreover assume L: "x \<in> S"
  hence "s\<^sub>1 = t\<^sub>1 (\<subseteq> sources_aux (?cs @ cs') vs\<^sub>1 s\<^sub>1 f x)"
    using A by blast
  ultimately have M: "s\<^sub>1 = t\<^sub>1 (\<subseteq> sources_aux ?cs vs\<^sub>1 s\<^sub>1 f y)"
    by blast
  have "tags (take ?m (?cs @ cs')) vs\<^sub>1 s\<^sub>1 f y \<subseteq>
    tags_aux (take ?m (?cs @ cs') @ drop ?m (?cs @ cs')) vs\<^sub>1 s\<^sub>1 f x"
    using J by (rule tags_aux_member)
  hence "tags (?cs @ take (?m - length ?cs) cs') vs\<^sub>1 s\<^sub>1 f y \<subseteq>
    tags_aux (?cs @ cs') vs\<^sub>1 s\<^sub>1 f x"
    using K by simp
  moreover have
   "tags_aux (?cs @ take (?m - length ?cs) cs') vs\<^sub>1 s\<^sub>1 f y \<subseteq>
    tags (?cs @ take (?m - length ?cs) cs') vs\<^sub>1 s\<^sub>1 f y"
    by (rule tags_aux_tags)
  moreover have "tags_aux ?cs vs\<^sub>1 s\<^sub>1 f y \<subseteq>
    tags_aux (?cs @ take (?m - length ?cs) cs') vs\<^sub>1 s\<^sub>1 f y"
    by (rule tags_aux_append)
  ultimately have "tags_aux ?cs vs\<^sub>1 s\<^sub>1 f y \<subseteq>
    \<Union> {tags_aux (?cs @ cs') vs\<^sub>1 s\<^sub>1 f x | x. x \<in> S}"
    using L by blast
  with B have "f = f' (\<subseteq> vs\<^sub>1, vs\<^sub>1', tags_aux ?cs vs\<^sub>1 s\<^sub>1 f y)"
    by (rule eq_streams_subset)
  hence "map fst [p\<leftarrow>drop (length vs\<^sub>1) vs\<^sub>2. fst p = y] =
    map fst [p\<leftarrow>drop (length vs\<^sub>1') vs\<^sub>2'. fst p = y]"
    using E [rule_format, of "{y}"] and M by simp
  hence "length [p\<leftarrow>drop (length vs\<^sub>1) vs\<^sub>2. fst p = y] =
    length [p\<leftarrow>drop (length vs\<^sub>1') vs\<^sub>2'. fst p = y]"
    by (drule_tac arg_cong [where f = length],
     subst (asm) (1 2) length_map)
  hence "length [p\<leftarrow>drop (length vs\<^sub>1) vs\<^sub>2. fst p = y] = ?k \<and>
    length [p\<leftarrow>drop (length vs\<^sub>1') vs\<^sub>2'. fst p = y] = ?k"
    using H by (simp add: in_flow_length)
  moreover have "f y (length [p\<leftarrow>vs\<^sub>1. fst p = y] + ?k + n) =
    f' y (length [p\<leftarrow>vs\<^sub>1'. fst p = y] + ?k + n)"
    using B and I and L by (fastforce simp: eq_streams_def ac_simps)
  ultimately show "f y (length [p\<leftarrow>vs\<^sub>2. fst p = y] + n) =
    f' y (length [p\<leftarrow>vs\<^sub>2'. fst p = y] + n)"
    by (subst F, subst G, simp)
qed

lemma tags_rhs:
  assumes
    A: "S \<subseteq> {x. s\<^sub>1 = t\<^sub>1 (\<subseteq> sources (flow cfs @ cs') vs\<^sub>1 s\<^sub>1 f x)}"
      (is "_ \<subseteq> {_. _ = _ (\<subseteq> sources (?cs @ _) _ _ _ _)}")
  assumes
    B: "f = f' (\<subseteq> vs\<^sub>1, vs\<^sub>1',
      \<Union> {tags (?cs @ cs') vs\<^sub>1 s\<^sub>1 f x | x. x \<in> S})" and
    C: "(c\<^sub>1, s\<^sub>1, f, vs\<^sub>1, ws\<^sub>1) \<rightarrow>*{cfs} (c\<^sub>2, s\<^sub>2, f, vs\<^sub>2, ws\<^sub>2)" and
    D: "(c\<^sub>1', t\<^sub>1, f', vs\<^sub>1', ws\<^sub>1') \<rightarrow>* (c\<^sub>2', t\<^sub>2, f', vs\<^sub>2', ws\<^sub>2')" and
    E: "ok_flow_aux_1 c\<^sub>1 c\<^sub>2 c\<^sub>2' s\<^sub>1 t\<^sub>1 t\<^sub>2 f f' vs\<^sub>1 vs\<^sub>1' vs\<^sub>2 vs\<^sub>2' ws\<^sub>1' ws\<^sub>2' ?cs"
  shows "f = f' (\<subseteq> vs\<^sub>2, vs\<^sub>2', \<Union> {tags cs' vs\<^sub>2 s\<^sub>2 f x | x. x \<in> S})"
proof (subst eq_streams_def, clarify)
  fix x y n
  have F: "vs\<^sub>2 = vs\<^sub>1 @ drop (length vs\<^sub>1) vs\<^sub>2"
    using small_stepsl_steps [OF C] by (rule small_steps_in_flow)
  have G: "vs\<^sub>2' = vs\<^sub>1' @ drop (length vs\<^sub>1') vs\<^sub>2'"
    using D by (rule small_steps_in_flow)
  assume "(y, n) \<in> tags cs' vs\<^sub>2 s\<^sub>2 f x"
  moreover have "s\<^sub>2 = run_flow ?cs vs\<^sub>1 s\<^sub>1 f"
    using C by (rule small_stepsl_run_flow)
  moreover have H: "vs\<^sub>2 = vs\<^sub>1 @ in_flow ?cs vs\<^sub>1 f"
    using C by (rule small_stepsl_in_flow)
  ultimately have I: "(y, length [c\<leftarrow>?cs. c = IN y] + n)
    \<in> tags (?cs @ cs') vs\<^sub>1 s\<^sub>1 f x"
    (is "(_, ?k + _) \<in> _")
    by (simp add: tags_suffix)
  let ?m = "Suc (Max {k. k \<le> length (?cs @ cs') \<and>
    length [c\<leftarrow>take k (?cs @ cs'). c = IN y] \<le> ?k + n})"
  have J: "y \<in> sources (drop ?m (?cs @ cs'))
    (vs\<^sub>1 @ in_flow (take ?m (?cs @ cs')) vs\<^sub>1 f)
    (run_flow (take ?m (?cs @ cs')) vs\<^sub>1 s\<^sub>1 f) f x"
    using I by (auto dest: tags_sources)
  hence "sources (take ?m (?cs @ cs')) vs\<^sub>1 s\<^sub>1 f y \<subseteq>
    sources (take ?m (?cs @ cs') @ drop ?m (?cs @ cs')) vs\<^sub>1 s\<^sub>1 f x"
    by (rule sources_member)
  moreover have K: "length ?cs \<le> ?m"
    by (rule le_SucI, rule Max_ge, simp_all)
  ultimately have
   "sources (?cs @ take (?m - length ?cs) cs') vs\<^sub>1 s\<^sub>1 f y \<subseteq>
    sources (?cs @ cs') vs\<^sub>1 s\<^sub>1 f x"
    by simp
  moreover have
   "sources_aux (?cs @ take (?m - length ?cs) cs') vs\<^sub>1 s\<^sub>1 f y \<subseteq>
    sources (?cs @ take (?m - length ?cs) cs') vs\<^sub>1 s\<^sub>1 f y"
    by (rule sources_aux_sources)
  moreover have "sources_aux ?cs vs\<^sub>1 s\<^sub>1 f y \<subseteq>
    sources_aux (?cs @ take (?m - length ?cs) cs') vs\<^sub>1 s\<^sub>1 f y"
    by (rule sources_aux_append)
  moreover assume L: "x \<in> S"
  hence "s\<^sub>1 = t\<^sub>1 (\<subseteq> sources (?cs @ cs') vs\<^sub>1 s\<^sub>1 f x)"
    using A by blast
  ultimately have M: "s\<^sub>1 = t\<^sub>1 (\<subseteq> sources_aux ?cs vs\<^sub>1 s\<^sub>1 f y)"
    by blast
  have "tags (take ?m (?cs @ cs')) vs\<^sub>1 s\<^sub>1 f y \<subseteq>
    tags (take ?m (?cs @ cs') @ drop ?m (?cs @ cs')) vs\<^sub>1 s\<^sub>1 f x"
    using J by (rule tags_member)
  hence "tags (?cs @ take (?m - length ?cs) cs') vs\<^sub>1 s\<^sub>1 f y \<subseteq>
    tags (?cs @ cs') vs\<^sub>1 s\<^sub>1 f x"
    using K by simp
  moreover have
   "tags_aux (?cs @ take (?m - length ?cs) cs') vs\<^sub>1 s\<^sub>1 f y \<subseteq>
    tags (?cs @ take (?m - length ?cs) cs') vs\<^sub>1 s\<^sub>1 f y"
    by (rule tags_aux_tags)
  moreover have "tags_aux ?cs vs\<^sub>1 s\<^sub>1 f y \<subseteq>
    tags_aux (?cs @ take (?m - length ?cs) cs') vs\<^sub>1 s\<^sub>1 f y"
    by (rule tags_aux_append)
  ultimately have "tags_aux ?cs vs\<^sub>1 s\<^sub>1 f y \<subseteq>
    \<Union> {tags (?cs @ cs') vs\<^sub>1 s\<^sub>1 f x | x. x \<in> S}"
    using L by blast
  with B have "f = f' (\<subseteq> vs\<^sub>1, vs\<^sub>1', tags_aux ?cs vs\<^sub>1 s\<^sub>1 f y)"
    by (rule eq_streams_subset)
  hence "map fst [p\<leftarrow>drop (length vs\<^sub>1) vs\<^sub>2. fst p = y] =
    map fst [p\<leftarrow>drop (length vs\<^sub>1') vs\<^sub>2'. fst p = y]"
    using E [rule_format, of "{y}"] and M by simp
  hence "length [p\<leftarrow>drop (length vs\<^sub>1) vs\<^sub>2. fst p = y] =
    length [p\<leftarrow>drop (length vs\<^sub>1') vs\<^sub>2'. fst p = y]"
    by (drule_tac arg_cong [where f = length],
     subst (asm) (1 2) length_map)
  hence "length [p\<leftarrow>drop (length vs\<^sub>1) vs\<^sub>2. fst p = y] = ?k \<and>
    length [p\<leftarrow>drop (length vs\<^sub>1') vs\<^sub>2'. fst p = y] = ?k"
    using H by (simp add: in_flow_length)
  moreover have "f y (length [p\<leftarrow>vs\<^sub>1. fst p = y] + ?k + n) =
    f' y (length [p\<leftarrow>vs\<^sub>1'. fst p = y] + ?k + n)"
    using B and I and L by (fastforce simp: eq_streams_def ac_simps)
  ultimately show "f y (length [p\<leftarrow>vs\<^sub>2. fst p = y] + n) =
    f' y (length [p\<leftarrow>vs\<^sub>2'. fst p = y] + n)"
    by (subst F, subst G, simp)
qed

lemma tags_out_rhs:
  assumes
    A: "S \<subseteq> {x. s\<^sub>1 = t\<^sub>1 (\<subseteq> sources_out (flow cfs @ cs') vs\<^sub>1 s\<^sub>1 f x)}"
      (is "_ \<subseteq> {_. _ = _ (\<subseteq> sources_out (?cs @ _) _ _ _ _)}")
  assumes
    B: "f = f' (\<subseteq> vs\<^sub>1, vs\<^sub>1',
      \<Union> {tags_out (?cs @ cs') vs\<^sub>1 s\<^sub>1 f x | x. x \<in> S})" and
    C: "(c\<^sub>1, s\<^sub>1, f, vs\<^sub>1, ws\<^sub>1) \<rightarrow>*{cfs} (c\<^sub>2, s\<^sub>2, f, vs\<^sub>2, ws\<^sub>2)" and
    D: "(c\<^sub>1', t\<^sub>1, f', vs\<^sub>1', ws\<^sub>1') \<rightarrow>* (c\<^sub>2', t\<^sub>2, f', vs\<^sub>2', ws\<^sub>2')" and
    E: "ok_flow_aux_1 c\<^sub>1 c\<^sub>2 c\<^sub>2' s\<^sub>1 t\<^sub>1 t\<^sub>2 f f' vs\<^sub>1 vs\<^sub>1' vs\<^sub>2 vs\<^sub>2' ws\<^sub>1' ws\<^sub>2' ?cs"
  shows "f = f' (\<subseteq> vs\<^sub>2, vs\<^sub>2', \<Union> {tags_out cs' vs\<^sub>2 s\<^sub>2 f x | x. x \<in> S})"
proof (subst eq_streams_def, clarify)
  fix x y n
  have F: "vs\<^sub>2 = vs\<^sub>1 @ drop (length vs\<^sub>1) vs\<^sub>2"
    using small_stepsl_steps [OF C] by (rule small_steps_in_flow)
  have G: "vs\<^sub>2' = vs\<^sub>1' @ drop (length vs\<^sub>1') vs\<^sub>2'"
    using D by (rule small_steps_in_flow)
  assume "(y, n) \<in> tags_out cs' vs\<^sub>2 s\<^sub>2 f x"
  moreover have "s\<^sub>2 = run_flow ?cs vs\<^sub>1 s\<^sub>1 f"
    using C by (rule small_stepsl_run_flow)
  moreover have H: "vs\<^sub>2 = vs\<^sub>1 @ in_flow ?cs vs\<^sub>1 f"
    using C by (rule small_stepsl_in_flow)
  ultimately have I: "(y, length [c\<leftarrow>?cs. c = IN y] + n)
    \<in> tags_out (?cs @ cs') vs\<^sub>1 s\<^sub>1 f x"
    (is "(_, ?k + _) \<in> _")
    by (simp add: tags_out_suffix)
  let ?m = "Suc (Max {k. k \<le> length (?cs @ cs') \<and>
    length [c\<leftarrow>take k (?cs @ cs'). c = IN y] \<le> ?k + n})"
  have J: "y \<in> sources_out (drop ?m (?cs @ cs'))
    (vs\<^sub>1 @ in_flow (take ?m (?cs @ cs')) vs\<^sub>1 f)
    (run_flow (take ?m (?cs @ cs')) vs\<^sub>1 s\<^sub>1 f) f x"
    using I by (auto dest: tags_out_sources_out)
  hence "sources (take ?m (?cs @ cs')) vs\<^sub>1 s\<^sub>1 f y \<subseteq>
    sources_out (take ?m (?cs @ cs') @ drop ?m (?cs @ cs')) vs\<^sub>1 s\<^sub>1 f x"
    by (rule sources_out_member)
  moreover have K: "length ?cs \<le> ?m"
    by (rule le_SucI, rule Max_ge, simp_all)
  ultimately have
   "sources (?cs @ take (?m - length ?cs) cs') vs\<^sub>1 s\<^sub>1 f y \<subseteq>
    sources_out (?cs @ cs') vs\<^sub>1 s\<^sub>1 f x"
    by simp
  moreover have
   "sources_aux (?cs @ take (?m - length ?cs) cs') vs\<^sub>1 s\<^sub>1 f y \<subseteq>
    sources (?cs @ take (?m - length ?cs) cs') vs\<^sub>1 s\<^sub>1 f y"
    by (rule sources_aux_sources)
  moreover have "sources_aux ?cs vs\<^sub>1 s\<^sub>1 f y \<subseteq>
    sources_aux (?cs @ take (?m - length ?cs) cs') vs\<^sub>1 s\<^sub>1 f y"
    by (rule sources_aux_append)
  moreover assume L: "x \<in> S"
  hence "s\<^sub>1 = t\<^sub>1 (\<subseteq> sources_out (?cs @ cs') vs\<^sub>1 s\<^sub>1 f x)"
    using A by blast
  ultimately have M: "s\<^sub>1 = t\<^sub>1 (\<subseteq> sources_aux ?cs vs\<^sub>1 s\<^sub>1 f y)"
    by blast
  have "tags (take ?m (?cs @ cs')) vs\<^sub>1 s\<^sub>1 f y \<subseteq>
    tags_out (take ?m (?cs @ cs') @ drop ?m (?cs @ cs')) vs\<^sub>1 s\<^sub>1 f x"
    using J by (rule tags_out_member)
  hence "tags (?cs @ take (?m - length ?cs) cs') vs\<^sub>1 s\<^sub>1 f y \<subseteq>
    tags_out (?cs @ cs') vs\<^sub>1 s\<^sub>1 f x"
    using K by simp
  moreover have
   "tags_aux (?cs @ take (?m - length ?cs) cs') vs\<^sub>1 s\<^sub>1 f y \<subseteq>
    tags (?cs @ take (?m - length ?cs) cs') vs\<^sub>1 s\<^sub>1 f y"
    by (rule tags_aux_tags)
  moreover have "tags_aux ?cs vs\<^sub>1 s\<^sub>1 f y \<subseteq>
    tags_aux (?cs @ take (?m - length ?cs) cs') vs\<^sub>1 s\<^sub>1 f y"
    by (rule tags_aux_append)
  ultimately have "tags_aux ?cs vs\<^sub>1 s\<^sub>1 f y \<subseteq>
    \<Union> {tags_out (?cs @ cs') vs\<^sub>1 s\<^sub>1 f x | x. x \<in> S}"
    using L by blast
  with B have "f = f' (\<subseteq> vs\<^sub>1, vs\<^sub>1', tags_aux ?cs vs\<^sub>1 s\<^sub>1 f y)"
    by (rule eq_streams_subset)
  hence "map fst [p\<leftarrow>drop (length vs\<^sub>1) vs\<^sub>2. fst p = y] =
    map fst [p\<leftarrow>drop (length vs\<^sub>1') vs\<^sub>2'. fst p = y]"
    using E [rule_format, of "{y}"] and M by simp
  hence "length [p\<leftarrow>drop (length vs\<^sub>1) vs\<^sub>2. fst p = y] =
    length [p\<leftarrow>drop (length vs\<^sub>1') vs\<^sub>2'. fst p = y]"
    by (drule_tac arg_cong [where f = length],
     subst (asm) (1 2) length_map)
  hence "length [p\<leftarrow>drop (length vs\<^sub>1) vs\<^sub>2. fst p = y] = ?k \<and>
    length [p\<leftarrow>drop (length vs\<^sub>1') vs\<^sub>2'. fst p = y] = ?k"
    using H by (simp add: in_flow_length)
  moreover have "f y (length [p\<leftarrow>vs\<^sub>1. fst p = y] + ?k + n) =
    f' y (length [p\<leftarrow>vs\<^sub>1'. fst p = y] + ?k + n)"
    using B and I and L by (fastforce simp: eq_streams_def ac_simps)
  ultimately show "f y (length [p\<leftarrow>vs\<^sub>2. fst p = y] + n) =
    f' y (length [p\<leftarrow>vs\<^sub>2'. fst p = y] + n)"
    by (subst F, subst G, simp)
qed


lemma ctyping2_term_seq:
  assumes
    A: "\<And>B Y p. (U, v) \<Turnstile> c\<^sub>1 (\<subseteq> A, X) = Some (B, Y) \<Longrightarrow>
      \<exists>(C, Z) \<in> U. \<not> C: Z \<leadsto> UNIV \<Longrightarrow> \<exists>p'. (c\<^sub>1, p) \<Rightarrow> p'" and
    B: "\<And>q B Y B' Y' p. (U, v) \<Turnstile> c\<^sub>1 (\<subseteq> A, X) = Some q \<Longrightarrow> (B, Y) = q \<Longrightarrow>
      (U, v) \<Turnstile> c\<^sub>2 (\<subseteq> B, Y) = Some (B', Y') \<Longrightarrow>
        \<exists>(C, Z) \<in> U. \<not> C: Z \<leadsto> UNIV \<Longrightarrow> \<exists>p'. (c\<^sub>2, p) \<Rightarrow> p'" and
    C: "(U, v) \<Turnstile> c\<^sub>1;; c\<^sub>2 (\<subseteq> A, X) = Some (B', Y')" and
    D: "\<exists>(C, Z) \<in> U. \<not> C: Z \<leadsto> UNIV"
  shows "\<exists>p'. (c\<^sub>1;; c\<^sub>2, p) \<Rightarrow> p'"
proof -
  obtain B and Y where
    E: "(U, v) \<Turnstile> c\<^sub>1 (\<subseteq> A, X) = Some (B, Y)" and
    F: "(U, v) \<Turnstile> c\<^sub>2 (\<subseteq> B, Y) = Some (B', Y')"
    using C by (auto split: option.split_asm)
  obtain p' where "(c\<^sub>1, p) \<Rightarrow> p'"
    using A [OF E D] by blast
  moreover obtain p'' where "(c\<^sub>2, p') \<Rightarrow> p''"
    using B [OF E _ F D] by blast
  ultimately show ?thesis
    by blast
qed

lemma ctyping2_term_or:
  assumes
    A: "\<And>B Y p. (U, v) \<Turnstile> c\<^sub>1 (\<subseteq> A, X) = Some (B, Y) \<Longrightarrow>
      \<exists>(C, Z) \<in> U. \<not> C: Z \<leadsto> UNIV \<Longrightarrow> \<exists>p'. (c\<^sub>1, p) \<Rightarrow> p'" and
    B: "(U, v) \<Turnstile> c\<^sub>1 OR c\<^sub>2 (\<subseteq> A, X) = Some (B', Y')" and
    C: "\<exists>(C, Z) \<in> U. \<not> C: Z \<leadsto> UNIV"
  shows "\<exists>p'. (c\<^sub>1 OR c\<^sub>2, p) \<Rightarrow> p'"
proof -
  obtain B and Y where "(U, v) \<Turnstile> c\<^sub>1 (\<subseteq> A, X) = Some (B, Y)"
    using B by (auto split: option.split_asm)
  thus ?thesis
    using A and C by blast
qed

lemma ctyping2_term_if:
  assumes
    A: "\<And>U' q B\<^sub>1 B\<^sub>2 B Y p.
      (U', q) = (insert (Univ? A X, bvars b) U, \<Turnstile> b (\<subseteq> A, X)) \<Longrightarrow>
        (B\<^sub>1, B\<^sub>2) = q \<Longrightarrow> (U', v) \<Turnstile> c\<^sub>1 (\<subseteq> B\<^sub>1, X) = Some (B, Y) \<Longrightarrow>
          \<exists>(C, Z) \<in> U'. \<not> C: Z \<leadsto> UNIV \<Longrightarrow> \<exists>p'. (c\<^sub>1, p) \<Rightarrow> p'" and
    B: "\<And>U' q B\<^sub>1 B\<^sub>2 B Y p.
      (U', q) = (insert (Univ? A X, bvars b) U, \<Turnstile> b (\<subseteq> A, X)) \<Longrightarrow>
        (B\<^sub>1, B\<^sub>2) = q \<Longrightarrow> (U', v) \<Turnstile> c\<^sub>2 (\<subseteq> B\<^sub>2, X) = Some (B, Y) \<Longrightarrow>
          \<exists>(C, Z) \<in> U'. \<not> C: Z \<leadsto> UNIV \<Longrightarrow> \<exists>p'. (c\<^sub>2, p) \<Rightarrow> p'" and
    C: "(U, v) \<Turnstile> IF b THEN c\<^sub>1 ELSE c\<^sub>2 (\<subseteq> A, X) = Some (B, Y)" and
    D: "\<exists>(C, Z) \<in> U. \<not> C: Z \<leadsto> UNIV"
  shows "\<exists>p'. (IF b THEN c\<^sub>1 ELSE c\<^sub>2, p) \<Rightarrow> p'"
proof -
  let ?U' = "insert (Univ? A X, bvars b) U"
  obtain B\<^sub>1 and B\<^sub>1' and Y\<^sub>1 and B\<^sub>2 and B\<^sub>2' and Y\<^sub>2 where
    E: "\<Turnstile> b (\<subseteq> A, X) = (B\<^sub>1, B\<^sub>2)" and
    F: "(?U', v) \<Turnstile> c\<^sub>1 (\<subseteq> B\<^sub>1, X) = Some (B\<^sub>1', Y\<^sub>1)" and
    G: "(?U', v) \<Turnstile> c\<^sub>2 (\<subseteq> B\<^sub>2, X) = Some (B\<^sub>2', Y\<^sub>2)"
    using C by (auto split: option.split_asm prod.split_asm)
  obtain s and q where "p = (s, q)"
    by (cases p)
  moreover {
    assume "bval b s"
    moreover obtain p' where "(c\<^sub>1, s, q) \<Rightarrow> p'"
      using A [OF _ _ F, of _ B\<^sub>2 "(s, q)"] and D and E by auto
    ultimately have "\<exists>p'. (IF b THEN c\<^sub>1 ELSE c\<^sub>2, s, q) \<Rightarrow> p'"
      by blast
  }
  moreover {
    assume "\<not> bval b s"
    moreover obtain p' where "(c\<^sub>2, s, q) \<Rightarrow> p'"
      using B [OF _ _ G, of _ B\<^sub>1 "(s, q)"] and D and E by auto
    ultimately have "\<exists>p'. (IF b THEN c\<^sub>1 ELSE c\<^sub>2, s, q) \<Rightarrow> p'"
      by blast
  }
  ultimately show ?thesis
    by blast
qed

lemma ctyping2_term:
 "\<lbrakk>(U, v) \<Turnstile> c (\<subseteq> A, X) = Some (B, Y); \<exists>(C, Z) \<in> U. \<not> C: Z \<leadsto> UNIV\<rbrakk> \<Longrightarrow>
    \<exists>p'. (c, p) \<Rightarrow> p'"
proof (induction "(U, v)" c A X arbitrary: B Y U v p rule: ctyping2.induct,
 blast)
  fix A X B Y U v c\<^sub>1 c\<^sub>2 p
  show
   "\<lbrakk>\<And>B Y p. (U, v) \<Turnstile> c\<^sub>1 (\<subseteq> A, X) = Some (B, Y) \<Longrightarrow>
      \<exists>(C, Z) \<in> U. \<not> C: Z \<leadsto> UNIV \<Longrightarrow> \<exists>p'. (c\<^sub>1, p) \<Rightarrow> p';
    \<And>q B Y B' Y' p. (U, v) \<Turnstile> c\<^sub>1 (\<subseteq> A, X) = Some q \<Longrightarrow> (B, Y) = q \<Longrightarrow>
      (U, v) \<Turnstile> c\<^sub>2 (\<subseteq> B, Y) = Some (B', Y') \<Longrightarrow>
        \<exists>(C, Z) \<in> U. \<not> C: Z \<leadsto> UNIV \<Longrightarrow> \<exists>p'. (c\<^sub>2, p) \<Rightarrow> p';
    (U, v) \<Turnstile> c\<^sub>1;; c\<^sub>2 (\<subseteq> A, X) = Some (B, Y);
    \<exists>(C, Z) \<in> U. \<not> C: Z \<leadsto> UNIV\<rbrakk> \<Longrightarrow>
      \<exists>p'. (c\<^sub>1;; c\<^sub>2, p) \<Rightarrow> p'"
    by (rule ctyping2_term_seq)
next
  fix A X B Y U v c\<^sub>1 c\<^sub>2 p
  show
   "\<lbrakk>\<And>B Y p. (U, v) \<Turnstile> c\<^sub>1 (\<subseteq> A, X) = Some (B, Y) \<Longrightarrow>
      \<exists>(C, Z) \<in> U. \<not> C: Z \<leadsto> UNIV \<Longrightarrow> \<exists>p'. (c\<^sub>1, p) \<Rightarrow> p';
    (U, v) \<Turnstile> c\<^sub>1 OR c\<^sub>2 (\<subseteq> A, X) = Some (B, Y);
    \<exists>(C, Z) \<in> U. \<not> C: Z \<leadsto> UNIV\<rbrakk> \<Longrightarrow>
      \<exists>p'. (c\<^sub>1 OR c\<^sub>2, p) \<Rightarrow> p'"
    by (rule ctyping2_term_or)
next
  fix A X B Y U v b c\<^sub>1 c\<^sub>2 p
  show
   "\<lbrakk>\<And>U' q B\<^sub>1 B\<^sub>2 B Y p.
      (U', q) = (insert (Univ? A X, bvars b) U, \<Turnstile> b (\<subseteq> A, X)) \<Longrightarrow>
        (B\<^sub>1, B\<^sub>2) = q \<Longrightarrow> (U', v) \<Turnstile> c\<^sub>1 (\<subseteq> B\<^sub>1, X) = Some (B, Y) \<Longrightarrow>
          \<exists>(C, Z) \<in> U'. \<not> C: Z \<leadsto> UNIV \<Longrightarrow> \<exists>p'. (c\<^sub>1, p) \<Rightarrow> p';
    \<And>U' q B\<^sub>1 B\<^sub>2 B Y p.
      (U', q) = (insert (Univ? A X, bvars b) U, \<Turnstile> b (\<subseteq> A, X)) \<Longrightarrow>
        (B\<^sub>1, B\<^sub>2) = q \<Longrightarrow> (U', v) \<Turnstile> c\<^sub>2 (\<subseteq> B\<^sub>2, X) = Some (B, Y) \<Longrightarrow>
          \<exists>(C, Z) \<in> U'. \<not> C: Z \<leadsto> UNIV \<Longrightarrow> \<exists>p'. (c\<^sub>2, p) \<Rightarrow> p';
    (U, v) \<Turnstile> IF b THEN c\<^sub>1 ELSE c\<^sub>2 (\<subseteq> A, X) = Some (B, Y);
    \<exists>(C, Z) \<in> U. \<not> C: Z \<leadsto> UNIV\<rbrakk> \<Longrightarrow>
      \<exists>p'. (IF b THEN c\<^sub>1 ELSE c\<^sub>2, p) \<Rightarrow> p'"
    by (rule ctyping2_term_if)
qed (fastforce split: if_split_asm prod.split_asm)+


lemma ctyping2_confine_seq:
  assumes
    A: "\<And>s' f' vs' ws' A B X Y U v. p = (s', f', vs', ws') \<Longrightarrow>
      (U, v) \<Turnstile> c\<^sub>1 (\<subseteq> A, X) = Some (B, Y) \<Longrightarrow> \<exists>(C, Z) \<in> U. C: Z \<leadsto>| S \<Longrightarrow>
        s = s' (\<subseteq> S) \<and>
        [p\<leftarrow>drop (length vs) vs'. fst p \<in> S] = [] \<and>
        [p\<leftarrow>drop (length ws) ws'. fst p \<in> S] = []"
      (is "\<And>s' _ vs' ws' _ _ _ _ _ _. _ \<Longrightarrow> _ \<Longrightarrow> _ \<Longrightarrow>
        ?P s s' vs vs' ws ws'")
  assumes
    B: "\<And>s' f' vs' ws' A B X Y U v. p = (s', f', vs', ws') \<Longrightarrow>
      (U, v) \<Turnstile> c\<^sub>2 (\<subseteq> A, X) = Some (B, Y) \<Longrightarrow> \<exists>(C, Z) \<in> U. C: Z \<leadsto>| S \<Longrightarrow>
        ?P s' s'' vs' vs'' ws' ws''" and
    C: "(c\<^sub>1, s, f, vs, ws) \<Rightarrow> p" and
    D: "(c\<^sub>2, p) \<Rightarrow> (s'', f'', vs'', ws'')" and
    E: "(U, v) \<Turnstile> c\<^sub>1;; c\<^sub>2 (\<subseteq> A, X) = Some (B', Y')" and
    F: "\<exists>(C, Z) \<in> U. C: Z \<leadsto>| S"
  shows "?P s s'' vs vs'' ws ws''"
proof -
  obtain s' and f' and vs' and ws' where G: "p = (s', f', vs', ws')"
    by (cases p)
  have H: "(c\<^sub>1, s, f, vs, ws) \<rightarrow>* (SKIP, s', f', vs', ws')"
    using C and G by (simp add: big_iff_small)
  have I: "(c\<^sub>2, s', f', vs', ws') \<rightarrow>* (SKIP, s'', f'', vs'', ws'')"
    using D and G by (simp add: big_iff_small)
  have J: "vs' = vs @ drop (length vs) vs'"
    using H by (rule small_steps_in_flow)
  have "vs'' = vs' @ drop (length vs') vs''"
    using I by (rule small_steps_in_flow)
  hence K: "vs'' = vs @ drop (length vs) vs' @ drop (length vs') vs''"
    by (subst (asm) J, simp)
  have L: "ws' = ws @ drop (length ws) ws'"
    using H by (rule small_steps_out_flow)
  have "ws'' = ws' @ drop (length ws') ws''"
    using I by (rule small_steps_out_flow)
  hence M: "ws'' = ws @ drop (length ws) ws' @ drop (length ws') ws''"
    by (subst (asm) L, simp)
  obtain B and Y where
    N: "(U, v) \<Turnstile> c\<^sub>1 (\<subseteq> A, X) = Some (B, Y)" and
    O: "(U, v) \<Turnstile> c\<^sub>2 (\<subseteq> B, Y) = Some (B', Y')"
    using E by (auto split: option.split_asm)
  from A [OF G N F] and B [OF G O F] show ?thesis
    by (subst K, subst M, simp)
qed

lemma ctyping2_confine_or_lhs:
  assumes
    A: "\<And>A B X Y U v. (U, v) \<Turnstile> c\<^sub>1 (\<subseteq> A, X) = Some (B, Y) \<Longrightarrow>
      \<exists>(C, Z) \<in> U. C: Z \<leadsto>| S \<Longrightarrow>
        s = s' (\<subseteq> S) \<and>
        [p\<leftarrow>drop (length vs) vs'. fst p \<in> S] = [] \<and>
        [p\<leftarrow>drop (length ws) ws'. fst p \<in> S] = []"
      (is "\<And>_ _ _ _ _ _. _ \<Longrightarrow> _ \<Longrightarrow> ?P")
  assumes
    B: "(U, v) \<Turnstile> c\<^sub>1 OR c\<^sub>2 (\<subseteq> A, X) = Some (B', Y')" and
    C: "\<exists>(C, Z) \<in> U. C: Z \<leadsto>| S"
  shows ?P
proof -
  obtain B and Y where "(U, v) \<Turnstile> c\<^sub>1 (\<subseteq> A, X) = Some (B, Y)"
    using B by (auto split: option.split_asm)
  with A and C show ?thesis
    by simp
qed

lemma ctyping2_confine_or_rhs:
  assumes
    A: "\<And>A B X Y U v. (U, v) \<Turnstile> c\<^sub>2 (\<subseteq> A, X) = Some (B, Y) \<Longrightarrow>
      \<exists>(C, Z) \<in> U. C: Z \<leadsto>| S \<Longrightarrow>
        s = s' (\<subseteq> S) \<and>
        [p\<leftarrow>drop (length vs) vs'. fst p \<in> S] = [] \<and>
        [p\<leftarrow>drop (length ws) ws'. fst p \<in> S] = []"
      (is "\<And>_ _ _ _ _ _. _ \<Longrightarrow> _ \<Longrightarrow> ?P")
  assumes
    B: "(U, v) \<Turnstile> c\<^sub>1 OR c\<^sub>2 (\<subseteq> A, X) = Some (B', Y')" and
    C: "\<exists>(C, Z) \<in> U. C: Z \<leadsto>| S"
  shows ?P
proof -
  obtain B and Y where "(U, v) \<Turnstile> c\<^sub>2 (\<subseteq> A, X) = Some (B, Y)"
    using B by (auto split: option.split_asm)
  with A and C show ?thesis
    by simp
qed

lemma ctyping2_confine_if_true:
  assumes
    A: "\<And>A B X Y U v. (U, v) \<Turnstile> c\<^sub>1 (\<subseteq> A, X) = Some (B, Y) \<Longrightarrow>
      \<exists>(C, Z) \<in> U. C: Z \<leadsto>| S \<Longrightarrow>
        s = s' (\<subseteq> S) \<and>
        [p\<leftarrow>drop (length vs) vs'. fst p \<in> S] = [] \<and>
        [p\<leftarrow>drop (length ws) ws'. fst p \<in> S] = []"
      (is "\<And>_ _ _ _ _ _. _ \<Longrightarrow> _ \<Longrightarrow> ?P")
  assumes
    B: "(U, v) \<Turnstile> IF b THEN c\<^sub>1 ELSE c\<^sub>2 (\<subseteq> A, X) = Some (B, Y)" and
    C: "\<exists>(C, Z) \<in> U. C: Z \<leadsto>| S"
  shows ?P
proof -
  obtain B\<^sub>1 and B\<^sub>1' and Y\<^sub>1 where
   "(insert (Univ? A X, bvars b) U, v) \<Turnstile> c\<^sub>1 (\<subseteq> B\<^sub>1, X) = Some (B\<^sub>1', Y\<^sub>1)"
    using B by (auto split: option.split_asm prod.split_asm)
  with A and C show ?thesis
    by simp
qed

lemma ctyping2_confine_if_false:
  assumes
    A: "\<And>A B X Y U v. (U, v) \<Turnstile> c\<^sub>2 (\<subseteq> A, X) = Some (B, Y) \<Longrightarrow>
      \<exists>(C, Z) \<in> U. C: Z \<leadsto>| S \<Longrightarrow>
        s = s' (\<subseteq> S) \<and>
        [p\<leftarrow>drop (length vs) vs'. fst p \<in> S] = [] \<and>
        [p\<leftarrow>drop (length ws) ws'. fst p \<in> S] = []"
      (is "\<And>_ _ _ _ _ _. _ \<Longrightarrow> _ \<Longrightarrow> ?P")
  assumes
    B: "(U, v) \<Turnstile> IF b THEN c\<^sub>1 ELSE c\<^sub>2 (\<subseteq> A, X) = Some (B, Y)" and
    C: "\<exists>(C, Z) \<in> U. C: Z \<leadsto>| S"
  shows ?P
proof -
  obtain B\<^sub>2 and B\<^sub>2' and Y\<^sub>2 where
   "(insert (Univ? A X, bvars b) U, v) \<Turnstile> c\<^sub>2 (\<subseteq> B\<^sub>2, X) = Some (B\<^sub>2', Y\<^sub>2)"
    using B by (auto split: option.split_asm prod.split_asm)
  with A and C show ?thesis
    by simp
qed

lemma ctyping2_confine:
 "\<lbrakk>(c, s, f, vs, ws) \<Rightarrow> (s', f', vs', ws');
    (U, v) \<Turnstile> c (\<subseteq> A, X) = Some (B, Y); \<exists>(C, Z) \<in> U. C: Z \<leadsto>| S\<rbrakk> \<Longrightarrow>
  s = s' (\<subseteq> S) \<and>
  [p\<leftarrow>drop (length vs) vs'. fst p \<in> S] = [] \<and>
  [p\<leftarrow>drop (length ws) ws'. fst p \<in> S] = []"
  (is "\<lbrakk>_; _; _\<rbrakk> \<Longrightarrow> ?P s s' vs vs' ws ws'")
proof (induction "(c, s, f, vs, ws)" "(s', f', vs', ws')" arbitrary:
 c s f vs ws s' f' vs' ws' A B X Y U v rule: big_step.induct)
  fix A B X Y U v c\<^sub>1 c\<^sub>2 p s f vs ws s' f' vs' ws'
  show
   "\<lbrakk>\<And>s' f' vs' ws' A B X Y U v. p = (s', f', vs', ws') \<Longrightarrow>
      (U, v) \<Turnstile> c\<^sub>1 (\<subseteq> A, X) = Some (B, Y) \<Longrightarrow>
        \<exists>(C, Z) \<in> U. C: Z \<leadsto>| S \<Longrightarrow> ?P s s' vs vs' ws ws';
    \<And>s f vs ws A B X Y U v. p = (s, f, vs, ws) \<Longrightarrow>
      (U, v) \<Turnstile> c\<^sub>2 (\<subseteq> A, X) = Some (B, Y) \<Longrightarrow>
        \<exists>(C, Z) \<in> U. C: Z \<leadsto>| S \<Longrightarrow> ?P s s' vs vs' ws ws';
    (c\<^sub>1, s, f, vs, ws) \<Rightarrow> p;
    (c\<^sub>2, p) \<Rightarrow> (s', f', vs', ws');
    (U, v) \<Turnstile> c\<^sub>1;; c\<^sub>2 (\<subseteq> A, X) = Some (B, Y);
    \<exists>(C, Z) \<in> U. C: Z \<leadsto>| S\<rbrakk> \<Longrightarrow>
      ?P s s' vs vs' ws ws'"
    by (rule ctyping2_confine_seq)
next
  fix A B X Y U v c\<^sub>1 c\<^sub>2 s vs ws s' vs' ws'
  show
   "\<lbrakk>\<And>A B X Y U v. (U, v) \<Turnstile> c\<^sub>1 (\<subseteq> A, X) = Some (B, Y) \<Longrightarrow>
      \<exists>(C, Z) \<in> U. C: Z \<leadsto>| S \<Longrightarrow> ?P s s' vs vs' ws ws';
    (U, v) \<Turnstile> c\<^sub>1 OR c\<^sub>2 (\<subseteq> A, X) = Some (B, Y);
    \<exists>(C, Z) \<in> U. C: Z \<leadsto>| S\<rbrakk> \<Longrightarrow>
      ?P s s' vs vs' ws ws'"
    by (rule ctyping2_confine_or_lhs)
next
  fix A B X Y U v c\<^sub>1 c\<^sub>2 s vs ws s' vs' ws'
  show
   "\<lbrakk>\<And>A B X Y U v. (U, v) \<Turnstile> c\<^sub>2 (\<subseteq> A, X) = Some (B, Y) \<Longrightarrow>
      \<exists>(C, Z) \<in> U. C: Z \<leadsto>| S \<Longrightarrow> ?P s s' vs vs' ws ws';
    (U, v) \<Turnstile> c\<^sub>1 OR c\<^sub>2 (\<subseteq> A, X) = Some (B, Y);
    \<exists>(C, Z) \<in> U. C: Z \<leadsto>| S\<rbrakk> \<Longrightarrow>
      ?P s s' vs vs' ws ws'"
    by (rule ctyping2_confine_or_rhs)
next
  fix A B X Y U v b c\<^sub>1 c\<^sub>2 s vs ws s' vs' ws'
  show
   "\<lbrakk>\<And>A B X Y U v. (U, v) \<Turnstile> c\<^sub>1 (\<subseteq> A, X) = Some (B, Y) \<Longrightarrow>
      \<exists>(C, Z) \<in> U. C: Z \<leadsto>| S \<Longrightarrow> ?P s s' vs vs' ws ws';
    (U, v) \<Turnstile> IF b THEN c\<^sub>1 ELSE c\<^sub>2 (\<subseteq> A, X) = Some (B, Y);
    \<exists>(C, Z) \<in> U. C: Z \<leadsto>| S\<rbrakk> \<Longrightarrow>
      ?P s s' vs vs' ws ws'"
    by (rule ctyping2_confine_if_true)
next
  fix A B X Y U v b c\<^sub>1 c\<^sub>2 s vs ws s' vs' ws'
  show
   "\<lbrakk>\<And>A B X Y U v. (U, v) \<Turnstile> c\<^sub>2 (\<subseteq> A, X) = Some (B, Y) \<Longrightarrow>
      \<exists>(C, Z) \<in> U. C: Z \<leadsto>| S \<Longrightarrow> ?P s s' vs vs' ws ws';
    (U, v) \<Turnstile> IF b THEN c\<^sub>1 ELSE c\<^sub>2 (\<subseteq> A, X) = Some (B, Y);
    \<exists>(C, Z) \<in> U. C: Z \<leadsto>| S\<rbrakk> \<Longrightarrow>
      ?P s s' vs vs' ws ws'"
    by (rule ctyping2_confine_if_false)
qed (force split: if_split_asm prod.split_asm)+


lemma eq_states_assign:
  assumes
    A: "S \<subseteq> {y. s = t (\<subseteq> sources [x ::= a] vs s f y)}" and
    B: "x \<in> S" and
    C: "s \<in> Univ A (\<subseteq> state \<inter> X)" and
    D: "Univ? A X: avars a \<leadsto> {x}"
  shows "s = t (\<subseteq> avars a)"
proof -
  obtain r where E: "r \<in> A" and F: "s = r (\<subseteq> state \<inter> X)"
    using C by blast
  have "avars a \<subseteq> {y. s: dom y \<leadsto> dom x}"
  proof (cases "state \<subseteq> X")
    case True
    with F have "interf s = interf r"
      by (blast intro: interf_state)
    with D and E show ?thesis
      by (auto simp: univ_states_if_def split: if_split_asm)
  next
    case False
    with D and E show ?thesis
      by (auto simp: univ_states_if_def split: if_split_asm)
  qed
  moreover have "s = t (\<subseteq> sources [x ::= a] vs s f x)"
    using A and B by blast
  hence "s = t (\<subseteq> {y. s: dom y \<leadsto> dom x \<and> y \<in> avars a})"
    by (subst (asm) append_Nil [symmetric],
     simp only: sources.simps, auto)
  ultimately show ?thesis
    by blast
qed

lemma eq_states_while:
  assumes
    A: "S \<subseteq> {x. s = t (\<subseteq> sources_aux (\<langle>bvars b\<rangle> # cs) vs s f x)}" and
    B: "S \<noteq> {}" and
    C: "s \<in> Univ A (\<subseteq> state \<inter> X) \<union> Univ C (\<subseteq> state \<inter> Y)" and
    D: "Univ? A X \<union> Univ? C Y: bvars b \<leadsto> UNIV"
  shows "s = t (\<subseteq> bvars b)"
proof -
  from C have "{s}: bvars b \<leadsto> UNIV"
  proof
    assume "s \<in> Univ A (\<subseteq> state \<inter> X)"
    then obtain r where E: "r \<in> A" and F: "s = r (\<subseteq> state \<inter> X)"
      by blast
    show ?thesis
    proof (cases "state \<subseteq> X")
      case True
      with F have "interf s = interf r"
        by (blast intro: interf_state)
      with D and E show ?thesis
        by (auto simp: univ_states_if_def split: if_split_asm)
    qed (insert D E, auto simp: univ_states_if_def split: if_split_asm)
  next
    assume "s \<in> Univ C (\<subseteq> state \<inter> Y)"
    then obtain r where E: "r \<in> C" and F: "s = r (\<subseteq> state \<inter> Y)"
      by blast
    show ?thesis
    proof (cases "state \<subseteq> Y")
      case True
      with F have "interf s = interf r"
        by (blast intro: interf_state)
      with D and E show ?thesis
        by (auto simp: univ_states_if_def split: if_split_asm)
    qed (insert D E, auto simp: univ_states_if_def split: if_split_asm)
  qed
  hence "\<forall>x. bvars b \<subseteq> sources_aux (\<langle>bvars b\<rangle> # cs) vs s f x"
    by (blast intro!: sources_aux_observe_hd)
  thus ?thesis
    using A and B by blast
qed

lemma univ_states_while:
  assumes
    A: "(c, s, p) \<Rightarrow> (s', p')" and
    B: "\<Turnstile> b (\<subseteq> A, X) = (B\<^sub>1, B\<^sub>2)" and
    C: "\<turnstile> c (\<subseteq> B\<^sub>1, X) = (C, Y)" and
    D: "\<Turnstile> b (\<subseteq> C, Y) = (B\<^sub>1', B\<^sub>2')" and
    E: "({}, False) \<Turnstile> c (\<subseteq> B\<^sub>1, X) = Some (D, Z)" and
    F: "({}, False) \<Turnstile> c (\<subseteq> B\<^sub>1', Y) = Some (D', Z')" and
    G: "bval b s"
  shows "s \<in> Univ A (\<subseteq> state \<inter> X) \<union> Univ C (\<subseteq> state \<inter> Y) \<Longrightarrow>
    s' \<in> Univ A (\<subseteq> state \<inter> X) \<union> Univ C (\<subseteq> state \<inter> Y)"
proof (erule UnE)
  assume H: "s \<in> Univ A (\<subseteq> state \<inter> X)"
  have "s \<in> Univ B\<^sub>1 (\<subseteq> state \<inter> X)"
    using G by (insert btyping2_approx [OF B H], simp)
  with A and E have "s' \<in> Univ D (\<subseteq> state \<inter> Z)"
    by (rule ctyping2_approx)
  moreover have "D \<subseteq> C \<and> Y \<subseteq> Z"
    using C and E by (rule ctyping1_ctyping2)
  ultimately show ?thesis
    by blast
next
  assume H: "s \<in> Univ C (\<subseteq> state \<inter> Y)"
  have "s \<in> Univ B\<^sub>1' (\<subseteq> state \<inter> Y)"
    using G by (insert btyping2_approx [OF D H], simp)
  with A and F have "s' \<in> Univ D' (\<subseteq> state \<inter> Z')"
    by (rule ctyping2_approx)
  moreover obtain C' and Y' where I: "\<turnstile> c (\<subseteq> B\<^sub>1', Y) = (C', Y')"
    by (cases "\<turnstile> c (\<subseteq> B\<^sub>1', Y)", simp)
  hence "D' \<subseteq> C' \<and> Y' \<subseteq> Z'"
    using F by (rule ctyping1_ctyping2)
  ultimately have "s' \<in> Univ C' (\<subseteq> state \<inter> Y')"
    by blast
  moreover have J: "\<turnstile> c (\<subseteq> C, Y) = (C, Y)"
    using C by (rule ctyping1_idem)
  have "B\<^sub>1' \<subseteq> C"
    using D by (blast dest: btyping2_un_eq)
  with J and I have "C' \<subseteq> C \<and> Y \<subseteq> Y'"
    by (rule ctyping1_mono, simp)
  ultimately show ?thesis
    by blast
qed

end

end
