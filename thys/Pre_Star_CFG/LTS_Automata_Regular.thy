section \<open>Regular Language Constructions\<close>

theory LTS_Automata_Regular
imports
  LTS_Automata
  "Regular-Sets.Regular_Set"
begin

text \<open>The two lemmas below make the reflexive transitive executable in certain contexts.
Potentially they could be moved to \<open>Main\<close>.\<close>

lemma rtrancl_Image_code[code_unfold]: "R^* `` A = R^+ `` A \<union> A"
by (metis Image_Id Un_Image reflcl_trancl)

lemma rtrancl_converse_code[code_unfold]: "(R^*)^-1 `` A = (R^+)^-1 `` A \<union> A"
  by (metis rtrancl_Image_code rtrancl_converse trancl_converse)

text \<open>Regular language constructions on automata with epsilon transitions.
The label \<open>None\<close> denotes an epsilon transition and \<open>Some c\<close> a real letter \<open>c\<close>.\<close>

type_synonym ('s,'l)lts_eps = "('s,'l option)lts"
type_synonym ('s, 't) auto_eps = "('s, 't option) auto"


subsection\<open>Epsilon Closure\<close>

text\<open>The epsilon transitions of \<open>T\<close>, viewed as a plain relation on states:\<close>

definition eps_trans :: "('s,'l)lts_eps \<Rightarrow> ('s \<times> 's) set" where
"eps_trans T = {(p,q). (p,None,q) \<in> T}"

lemma eps_trans_code[code]: "eps_trans T = (\<lambda>(p,c,q). (p,q)) ` {(p,c,q) \<in> T. c = None}"
by(auto simp: eps_trans_def image_def split: prod.splits)

definition some_trans :: "('s,'l)lts_eps \<Rightarrow> ('s, 'l) lts" where
"some_trans T = (\<lambda>(p,co,q). (p, the co, q)) ` {(p,co,q) \<in> T. co \<noteq> None}"

abbreviation eps_clo :: "('s,'l)lts_eps \<Rightarrow> ('s \<times> 's) set" where
"eps_clo T \<equiv> (eps_trans T)\<^sup>*"

definition elim_eps_lts :: "('s,'l)lts_eps \<Rightarrow> ('s, 'l) lts" where
"elim_eps_lts T = {(p,c,q'). \<exists>p' q. (p,p') \<in> eps_clo T \<and> (p',Some c,q) \<in> T \<and> (q,q') \<in> eps_clo T}"

lemma elim_eps_lts_code[code]: "elim_eps_lts T = (
  \<Union>(p',c,q)\<in> some_trans T. \<Union>p \<in> (eps_clo T)^-1 `` {p'}. \<Union>q' \<in> eps_clo T `` {q}. {(p,c,q')})"
by(fastforce simp: elim_eps_lts_def some_trans_def Let_def)

definition elim_eps_auto :: "('s,'l)auto_eps \<Rightarrow> ('s, 'l) auto" where
"elim_eps_auto A = \<lparr>auto.lts = elim_eps_lts (auto.lts A),
    start = auto.start A,
    finals = (eps_clo (auto.lts A))\<inverse> `` auto.finals A \<rparr>"

definition Lang_auto_eps :: "('s, 'l) auto_eps \<Rightarrow> ('l list) set" where
"Lang_auto_eps = Lang_auto o elim_eps_auto"

definition auto_eps_of :: "('s,'l) auto \<Rightarrow> ('s,'l) auto_eps" where
"auto_eps_of A =
  \<lparr> auto.lts = (\<lambda>(p,c,q). (p, Some c, q)) ` auto.lts A,
   start = auto.start A, finals = auto.finals A\<rparr>"

lemma lts_elim_eps_auto[simp]: "auto.lts (elim_eps_auto A) = elim_eps_lts (auto.lts A)"
  by (simp add: elim_eps_auto_def)

lemma finals_auto_eps_of[simp]: "auto.finals (auto_eps_of A) = auto.finals A"
  by (simp add: auto_eps_of_def)

lemma elim_eps_auto_auto_eps_of: "elim_eps_auto (auto_eps_of A) = A"
by(cases A)
  (auto simp: auto_eps_of_def elim_eps_auto_def elim_eps_lts_def eps_trans_def image_def split: prod.splits)

lemma Lang_auto_eps_auto_eps_of: "Lang_auto_eps (auto_eps_of A) = Lang_auto A"
by(simp add:Lang_auto_eps_def elim_eps_auto_auto_eps_of)

lemma finite_lts_auto_eps_of: "finite(auto.lts A) \<Longrightarrow> finite(auto.lts (auto_eps_of A))"
  by (simp add: auto_eps_of_def)

lemma finite_eps_trans: "finite T \<Longrightarrow> finite(eps_trans T)"
  unfolding eps_trans_code
  by (metis (no_types, lifting) case_prodE finite_imageI finite_subset mem_Collect_eq subsetI)

lemma finite_some_trans: "finite T \<Longrightarrow> finite(some_trans T)"
  unfolding some_trans_def
  by (metis (no_types, lifting) case_prodE finite_imageI finite_subset mem_Collect_eq subsetI)

lemma finite_elim_eps_ltsI: "finite T \<Longrightarrow> finite(elim_eps_lts T)"
unfolding elim_eps_lts_code
by(auto simp: finite_UN_I finite_some_trans finite_eps_trans simp flip: rtrancl_converse)


lemma Lang_auto_eps_auto_eps_of_one_of_auto:
  "Lang_auto_eps (auto_eps_of (one_of_auto C)) = (\<lambda>c. [c]) ` C"
  by (simp add: Lang_auto_eps_auto_eps_of Lang_auto_one_of_auto)


subsection\<open>Runs of an epsilon-LTS\<close>

text\<open>\<open>runs T p w r\<close>: reading exactly the letters \<open>w\<close> one gets from \<open>p\<close> to \<open>r\<close>,
  with arbitrarily many silent (\<open>None\<close>) moves in between.\<close>

inductive runs :: "('s,'l)lts_eps \<Rightarrow> 's \<Rightarrow> 'l list \<Rightarrow> 's \<Rightarrow> bool" for T where
  Nil: "runs T p [] p"
| Eps: "(p,None,q) \<in> T \<Longrightarrow> runs T q w r \<Longrightarrow> runs T p w r"
| Sym: "(p,Some c,q) \<in> T \<Longrightarrow> runs T q w r \<Longrightarrow> runs T p (c#w) r"

lemma runs_imp_eps: "runs T p x r \<Longrightarrow> x = [] \<Longrightarrow> (p,r) \<in> eps_clo T"
  by (induction rule: runs.induct) (auto simp: eps_trans_def intro: converse_rtrancl_into_rtrancl)

lemma eps_imp_runs: "(p,r) \<in> eps_clo T \<Longrightarrow> runs T p [] r"
  by (induction rule: converse_rtrancl_induct) (auto simp: eps_trans_def intro: runs.intros)

lemma runs_Nil_iff: "runs T p [] r \<longleftrightarrow> (p,r) \<in> eps_clo T"
  by (meson runs_imp_eps eps_imp_runs)

lemma runs_append: "runs T a u b \<Longrightarrow> runs T b v r \<Longrightarrow> runs T a (u@v) r"
proof (induction rule: runs.induct)
  case (Nil p) thus ?case by simp
next
  case (Eps p q w r') thus ?case by (auto intro: runs.Eps)
next
  case (Sym p c q w r') thus ?case by (auto intro: runs.Sym)
qed

lemma runs_eps_pre: "(p,q) \<in> eps_clo T \<Longrightarrow> runs T q w r \<Longrightarrow> runs T p w r"
  by (metis append_Nil eps_imp_runs runs_append)

lemma runs_Cons_imp:
  "runs T p x r \<Longrightarrow> x = c#w \<Longrightarrow> \<exists>p' q. (p,p') \<in> eps_clo T \<and> (p',Some c,q) \<in> T \<and> runs T q w r"
proof (induction rule: runs.induct)
  case (Nil p) thus ?case by simp
next
  case (Eps p q x r) then show ?case
    by (meson runs.Eps runs_Nil_iff)
next
  case (Sym p c' q x r)
  then show ?case by blast
qed

lemma runs_Cons_iff:
  "runs T p (c#w) r \<longleftrightarrow> (\<exists>p' q. (p,p') \<in> eps_clo T \<and> (p',Some c,q) \<in> T \<and> runs T q w r)"
  by (meson runs_Cons_imp runs.Sym runs_eps_pre)


subsection\<open>Runs characterise the language\<close>

lemma steps_elim_runs: "q \<in> steps_lts (elim_eps_lts T) w s \<Longrightarrow> runs T s w q"
proof (induction w arbitrary: s)
  case Nil thus ?case by (simp add: runs.Nil)
next
  case (Cons c w)
  from Cons.prems obtain q0 where q0: "(s,c,q0) \<in> elim_eps_lts T" "q \<in> steps_lts (elim_eps_lts T) w q0"
    by (auto simp: steps_lts_Cons)
  then obtain p' q1 where p': "(s,p') \<in> eps_clo T" "(p',Some c,q1) \<in> T" "(q1,q0) \<in> eps_clo T"
    by (auto simp: elim_eps_lts_def)
  have "runs T q0 w q" using Cons.IH[OF q0(2)] .
  then show ?case using runs_eps_pre runs_Cons_iff p' by (metis)
qed

lemma runs_steps_elim: "runs T s w f \<Longrightarrow> \<exists>q. q \<in> steps_lts (elim_eps_lts T) w s \<and> (q,f) \<in> eps_clo T"
proof (induction w arbitrary: s)
  case Nil
  thus ?case by (auto simp add: runs_Nil_iff)
next
  case (Cons c w)
  from Cons.prems obtain p' q1 where p': "(s,p') \<in> eps_clo T" "(p',Some c,q1) \<in> T" "runs T q1 w f"
    by (auto simp: runs_Cons_iff)
  from Cons.IH[OF p'(3)] obtain q2 where q2: "q2 \<in> steps_lts (elim_eps_lts T) w q1" "(q2,f) \<in> eps_clo T"
    by blast
  have "(s,c,q1) \<in> elim_eps_lts T"
    using p'(1,2) by (auto simp: elim_eps_lts_def)
  then have "q2 \<in> steps_lts (elim_eps_lts T) (c#w) s"
    using q2(1) by (auto simp: steps_lts_Cons)
  then have "q2 \<in> steps_lts (elim_eps_lts T) (c#w) s \<and> (q2,f) \<in> eps_clo T"
    using q2(2) by (rule conjI)
  then show ?case ..
qed

lemma Lang_auto_eps_runs: "(w \<in> Lang_auto_eps A) = (\<exists>f\<in>auto.finals A. runs (auto.lts A) (auto.start A) w f)" (is "?L = ?R")
proof -
  let ?T = "auto.lts A" let ?F = "auto.finals A" let ?s = "auto.start A"
  have "?L = (\<exists>q f. q \<in> steps_lts (elim_eps_lts ?T) w ?s \<and> f \<in> ?F \<and> (q,f) \<in> eps_clo ?T)"
    by (auto simp: Lang_auto_eps_def elim_eps_auto_def Image_iff)
  also have "\<dots> = ?R" (is "?L = ?R")
  proof
    assume ?L
    then obtain q f where qf: "q \<in> steps_lts (elim_eps_lts ?T) w ?s" "f \<in> ?F" "(q,f) \<in> eps_clo ?T" by blast
    from qf(1) have "runs ?T ?s w q" by (rule steps_elim_runs)
    moreover from qf(3) have "runs ?T q [] f" by (rule eps_imp_runs)
    ultimately have "runs ?T ?s w f" by (metis append_Nil2 runs_append)
    thus ?R using qf(2) by blast
  next
    assume ?R
    then obtain f where f: "f \<in> ?F" "runs ?T ?s w f" by blast
    from runs_steps_elim[OF f(2)] obtain q
      where q: "q \<in> steps_lts (elim_eps_lts ?T) w ?s" "(q,f) \<in> eps_clo ?T" by blast
    have "q \<in> steps_lts (elim_eps_lts ?T) w ?s \<and> f \<in> ?F \<and> (q,f) \<in> eps_clo ?T"
      using q f(1) by (intro conjI)
    thus ?L by blast
  qed
  finally show ?thesis .
qed


subsection\<open>Sum-embedding of two epsilon-LTS\<close>

text\<open>Both concatenation and union embed \<open>T1\<close> and \<open>T2\<close> disjointly (as \<open>Inl\<close>/\<open>Inr\<close> states, leaving
  \<open>None\<close> spare) and then add a few silent bridges. We factor out the common embedding:\<close>

definition embed_lts :: "('s1,'l)lts_eps \<Rightarrow> ('s2,'l)lts_eps \<Rightarrow> (('s1 + 's2)option,'l)lts_eps" where
"embed_lts T1 T2 = (\<Union>(p,c,q) \<in> T1. {(Some(Inl p),c,Some(Inl q))})
  \<union> (\<Union>(p,c,q) \<in> T2. {(Some(Inr p),c,Some(Inr q))})"

lemma Inl_in_embed: "(p,a,q) \<in> T1 \<Longrightarrow> (Some(Inl p), a, Some(Inl q)) \<in> embed_lts T1 T2"
  by (auto simp: embed_lts_def)

lemma Inr_in_embed: "(p,a,q) \<in> T2 \<Longrightarrow> (Some(Inr p), a, Some(Inr q)) \<in> embed_lts T1 T2"
  by (auto simp: embed_lts_def)

lemma embed_Inl_src: "(Some(Inl p), a, Y) \<in> embed_lts T1 T2 \<Longrightarrow> \<exists>q. Y = Some(Inl q) \<and> (p,a,q) \<in> T1"
  by (auto simp: embed_lts_def)

lemma embed_Inr_src: "(Some(Inr p), a, Y) \<in> embed_lts T1 T2 \<Longrightarrow> \<exists>q. Y = Some(Inr q) \<and> (p,a,q) \<in> T2"
  by (auto simp: embed_lts_def)

lemma finite_embed_lts: "finite TA \<Longrightarrow> finite TB \<Longrightarrow> finite (embed_lts TA TB)"
  by(auto simp:embed_lts_def)

text\<open>Adding transitions only adds runs:\<close>

lemma runs_mono:
  assumes "T \<subseteq> T'" and "runs T p w q" shows "runs T' p w q"
  using assms(2)
proof (induction rule: runs.induct)
  case (Nil p) show ?case by (rule runs.Nil)
next
  case (Eps p q w r)
  then show ?case by (meson assms(1) runs.Eps subsetD)
next
  case (Sym p c q w r)
  then show ?case by (meson assms(1) runs.Sym subsetD)
qed

text\<open>\<open>T1\<close>/\<open>T2\<close>-runs embed as runs of the sum:\<close>

lemma runs_Inl_embed: "runs T1 p w q \<Longrightarrow> runs (embed_lts T1 T2) (Some(Inl p)) w (Some(Inl q))"
  by (induction rule: runs.induct) (auto intro: runs.intros Inl_in_embed)

lemma runs_Inr_embed: "runs T2 p w q \<Longrightarrow> runs (embed_lts T1 T2) (Some(Inr p)) w (Some(Inr q))"
  by (induction rule: runs.induct) (auto intro: runs.intros Inr_in_embed)

text\<open>If no transition leaves the \<open>Inl\<close> (resp.\ \<open>Inr\<close>) component of \<open>U\<close>, a run within it is a
  \<open>T1\<close> (resp.\ \<open>T2\<close>) run:\<close>

lemma runs_Inl_closed_gen:
  assumes "\<And>p a Y. (Some(Inl p), a, Y) \<in> U \<Longrightarrow> \<exists>q. Y = Some(Inl q) \<and> (p,a,q) \<in> T1"
  shows "runs U X w Q \<Longrightarrow> X = Some(Inl p) \<Longrightarrow> \<exists>q. Q = Some(Inl q) \<and> runs T1 p w q"
proof (induction arbitrary: p rule: runs.induct)
  case (Nil P)
  then show ?case by (auto intro: runs.Nil)
next
  case (Eps P P' w r)
  then show ?case by (meson assms runs.Eps)
next
  case (Sym P c P' w r)
  then show ?case by (meson assms runs.Sym)
qed

lemma runs_Inr_closed_gen:
  assumes "\<And>p a Y. (Some(Inr p), a, Y) \<in> U \<Longrightarrow> \<exists>q. Y = Some(Inr q) \<and> (p,a,q) \<in> T2"
  shows "runs U X w Q \<Longrightarrow> X = Some(Inr p) \<Longrightarrow> \<exists>q. Q = Some(Inr q) \<and> runs T2 p w q"
proof (induction arbitrary: p rule: runs.induct)
  case (Nil P)
  then show ?case by (auto intro: runs.Nil)
next
  case (Eps P P' w r)
  then show ?case by (metis assms runs.Eps)
next
  case (Sym P c P' w r)
  then show ?case by (meson assms runs.Sym)
qed


subsection\<open>Concatenation Automaton\<close>

definition conc_auto_eps_lts ::
  "('s1,'l)auto_eps \<Rightarrow> ('s2,'l)auto_eps \<Rightarrow> (('s1 + 's2)option,'l)lts_eps" where
"conc_auto_eps_lts A B =
   embed_lts (auto.lts A) (auto.lts B)
   \<union> (\<Union>f \<in> auto.finals A. {(Some(Inl f), None, Some(Inr (auto.start B)))})"

definition conc_auto_eps where "conc_auto_eps A B =
  \<lparr> auto.lts = conc_auto_eps_lts A B, start = Some(Inl (auto.start A)),
   finals = Some ` Inr ` auto.finals B \<rparr>"

lemma finite_conc_auto_eps_lts:
  "finite(auto.finals A) \<Longrightarrow> finite (conc_auto_eps_lts A B) \<longleftrightarrow>
     finite (embed_lts (auto.lts A) (auto.lts B))"
by (simp add: conc_auto_eps_lts_def)

lemma lts_conc_auto_eps: "auto.lts (conc_auto_eps A B) = conc_auto_eps_lts A B"
  by (simp add: conc_auto_eps_def)

lemma embed_sub_conc: "embed_lts (auto.lts A) (auto.lts B) \<subseteq> conc_auto_eps_lts A B"
  by (auto simp: conc_auto_eps_lts_def)

lemma bridge_in_conc:
  "f \<in> auto.finals A \<Longrightarrow> (Some(Inl f), None, Some(Inr (auto.start B))) \<in> conc_auto_eps_lts A B"
by (auto simp: conc_auto_eps_lts_def)

text\<open>Only edges out of an \<open>Inl\<close> state (a \<open>T1\<close> edge, or the bridge to \<open>Inr s2\<close>):\<close>

lemma conc_Inl_src:
  "(Some(Inl p), a, Y) \<in> conc_auto_eps_lts A B \<Longrightarrow>
     (\<exists>q. Y = Some(Inl q) \<and> (p,a,q) \<in> auto.lts A)
     \<or> (p \<in> auto.finals A \<and> a = None \<and> Y = Some(Inr (auto.start B)))"
by (auto simp: conc_auto_eps_lts_def embed_lts_def)

text\<open>Runs of \<open>T1\<close>/\<open>T2\<close> embed (via @{thm [source] runs_mono}), and the second component is closed:\<close>

lemma runs_Inl:
  assumes "runs (auto.lts A) p w q" shows "runs (conc_auto_eps_lts A B) (Some(Inl p)) w (Some(Inl q))"
  by (rule runs_mono[OF embed_sub_conc runs_Inl_embed[OF assms]])

lemma runs_Inr:
  assumes "runs (auto.lts B) p w q" shows "runs (conc_auto_eps_lts A B) (Some(Inr p)) w (Some(Inr q))"
  by (rule runs_mono[OF embed_sub_conc runs_Inr_embed[OF assms]])



text\<open>Once in the \<open>Inr\<close> (second) component, a run stays there and is a \<open>T2\<close>-run:\<close>

lemma runs_Inr_closed:
  assumes "runs (conc_auto_eps_lts A B) X w Q" and "X = Some(Inr p)"
  shows "\<exists>q. Q = Some(Inr q) \<and> runs (auto.lts B) p w q"
using runs_Inr_closed_gen[OF _ assms]
by (auto simp: conc_auto_eps_lts_def embed_lts_def)

text\<open>A run starting in the \<open>Inl\<close> (first) component either stays there (a \<open>T1\<close>-run), or crosses the
  bridge exactly once, splitting the word into a \<open>T1\<close>-part reaching a final of \<open>F1\<close> and a \<open>T2\<close>-part:\<close>

lemma runs_Inl_split:
  "runs (conc_auto_eps_lts A B) X w Q \<Longrightarrow> X = Some(Inl p)
    \<Longrightarrow> (\<exists>q. Q = Some(Inl q) \<and> runs (auto.lts A) p w q) \<or>
        (\<exists>u v f q. w = u@v \<and> runs (auto.lts A) p u f \<and> f \<in> (auto.finals A) \<and> Q = Some(Inr q) \<and> runs (auto.lts B) (auto.start B) v q)"
proof (induction arbitrary: p rule: runs.induct)
  case (Nil P)
  then show ?case by (auto intro: runs.Nil)
next
  case (Eps P P' w r)
  from Eps.prems Eps.hyps(1) have
    "(\<exists>p'. P' = Some(Inl p') \<and> (p,None,p') \<in> (auto.lts A)) \<or> (p \<in> auto.finals A \<and> P' = Some(Inr (auto.start B)))" (is "?A \<or> ?B")
    using conc_Inl_src by fastforce
  then show ?case
  proof (elim disjE)
    assume ?A
    then obtain p' where P': "P' = Some(Inl p')" and e: "(p,None,p') \<in> (auto.lts A)" by blast
    from Eps.IH[OF P'] show ?case by (metis e runs.Eps)
  next
    assume B: ?B
    then have "runs (conc_auto_eps_lts A B) (Some(Inr (auto.start B))) w r"
      using Eps.hyps(2) by simp
    from runs_Inr_closed[OF this refl]
    show ?case using B runs.Nil by fastforce
  qed
next
  case (Sym P c P' w r)
  from Sym.prems Sym.hyps(1) obtain p' where P': "P' = Some(Inl p')" and e: "(p,Some c,p') \<in> auto.lts A"
    using conc_Inl_src by fastforce
  from Sym.IH[OF P'] show ?case
    using e runs.Sym by fastforce
qed

theorem Lang_auto_eps_conc_auto_eps:
 "Lang_auto_eps (conc_auto_eps A B) = Lang_auto_eps A @@ Lang_auto_eps B"
proof (rule set_eqI)
  let ?T1 = "auto.lts A" let ?s1 = "auto.start A"  let ?F1 = "auto.finals A"
  let ?T2 = "auto.lts B" let ?s2 = "auto.start B" let ?F2 = "auto.finals B"
  fix w
  let ?AB = "conc_auto_eps A B"
  let ?TAB = "conc_auto_eps_lts A B"
  have L: "(w \<in> Lang_auto_eps ?AB)
         = (\<exists>f2\<in>?F2. runs ?TAB (Some(Inl ?s1)) w (Some(Inr f2)))" (is "_ = ?L")
    by (simp add: conc_auto_eps_def Lang_auto_eps_runs[of w])
  have R: "(w \<in> Lang_auto_eps A @@ Lang_auto_eps B)
     = (\<exists>u v. w = u@v \<and> (\<exists>f1\<in>?F1. runs ?T1 ?s1 u f1) \<and> (\<exists>f2\<in>?F2. runs ?T2 ?s2 v f2))" (is "_ = ?R")
    by (simp add: Lang_auto_eps_runs conc_def)
  show "(w \<in> Lang_auto_eps ?AB) = (w \<in> Lang_auto_eps A @@ Lang_auto_eps B)"
    unfolding L R
  proof
    assume "\<exists>f2\<in>?F2. runs ?TAB (Some(Inl ?s1)) w (Some(Inr f2))"
    thus ?R using runs_Inl_split by fastforce
  next
    assume "\<exists>u v. w = u@v \<and> (\<exists>f1\<in>?F1. runs ?T1 ?s1 u f1) \<and> (\<exists>f2\<in>?F2. runs ?T2 ?s2 v f2)"
    thus ?L by (meson Eps bridge_in_conc runs_Inl runs_Inr runs_append)
  qed
qed

subsection \<open>Union Automaton\<close>

text\<open>The union uses the otherwise unused state \<open>None\<close> as a fresh common start, with silent moves
  into both automata; the final states are those of \<open>T1\<close> and \<open>T2\<close>.\<close>

definition union_auto_eps_lts ::
  "('s1,'l)auto_eps \<Rightarrow> ('s2,'l)auto_eps \<Rightarrow> (('s1 + 's2)option,'l)lts_eps" where
"union_auto_eps_lts A B =
   embed_lts (auto.lts A) (auto.lts B)
   \<union> {(None, None, Some(Inl (auto.start A))), (None, None, Some(Inr (auto.start B)))}"

definition union_auto_eps ::
  "('s1,'l)auto_eps \<Rightarrow> ('s2,'l)auto_eps \<Rightarrow> (('s1 + 's2)option,'l)auto_eps" where
"union_auto_eps A B =
   \<lparr> auto.lts = union_auto_eps_lts A B, start = None,
     finals = Some ` Inl ` auto.finals A \<union> Some ` Inr ` auto.finals B\<rparr>"

lemma finite_union_auto_eps_lts:
  "finite (union_auto_eps_lts A B) = finite (embed_lts (auto.lts A) (auto.lts B))"
  by (simp add: union_auto_eps_lts_def)

lemma lts_union_auto_eps: "auto.lts (union_auto_eps A B) = union_auto_eps_lts A B"
  by (simp add: union_auto_eps_def)

lemma embed_sub_union: "embed_lts (auto.lts A) (auto.lts B) \<subseteq> union_auto_eps_lts A B"
  by (auto simp: union_auto_eps_lts_def)

lemma bridgeL_in_union: "(None, None, Some(Inl (auto.start A))) \<in> union_auto_eps_lts A B"
  by (auto simp: union_auto_eps_lts_def)

lemma bridgeR_in_union: "(None, None, Some(Inr (auto.start B))) \<in> union_auto_eps_lts A B"
  by (auto simp: union_auto_eps_lts_def)

text\<open>Edges out of \<open>Inl\<close>/\<open>Inr\<close> stay in that component; edges out of \<open>None\<close> are the two silent bridges:\<close>

lemma union_Inl_src:
  "(Some(Inl p), a, Y) \<in> union_auto_eps_lts A B \<Longrightarrow> \<exists>q. Y = Some(Inl q) \<and> (p,a,q) \<in> (auto.lts A)"
  by (auto simp: union_auto_eps_lts_def embed_lts_def)

lemma union_Inr_src:
  "(Some(Inr p), a, Y) \<in> union_auto_eps_lts A B \<Longrightarrow> \<exists>q. Y = Some(Inr q) \<and> (p,a,q) \<in> (auto.lts B)"
  by (auto simp: union_auto_eps_lts_def embed_lts_def)

lemma union_None_src:
  "(None, a, Y) \<in> union_auto_eps_lts A B \<Longrightarrow> a = None \<and> (Y = Some(Inl (auto.start A)) \<or> Y = Some(Inr (auto.start B)))"
  by (auto simp: union_auto_eps_lts_def embed_lts_def)

text\<open>Runs of \<open>T1\<close>/\<open>T2\<close> embed; with no cross edges, each component is closed (from the generics):\<close>

lemma runs_Inl_union:
  assumes "runs (auto.lts A) p w q" shows "runs (union_auto_eps_lts A B) (Some(Inl p)) w (Some(Inl q))"
  by (rule runs_mono[OF embed_sub_union runs_Inl_embed[OF assms]])

lemma runs_Inr_union:
  assumes "runs (auto.lts B) p w q" shows "runs (union_auto_eps_lts A B) (Some(Inr p)) w (Some(Inr q))"
  by (rule runs_mono[OF embed_sub_union runs_Inr_embed[OF assms]])

lemma runs_Inl_closed_union:
  assumes "runs (union_auto_eps_lts A B) X w Q" and "X = Some(Inl p)"
  shows "\<exists>q. Q = Some(Inl q) \<and> runs (auto.lts A) p w q"
  by (rule runs_Inl_closed_gen[OF _ assms]) (rule union_Inl_src)

lemma runs_Inr_closed_union:
  assumes "runs (union_auto_eps_lts A B) X w Q" and "X = Some(Inr p)"
  shows "\<exists>q. Q = Some(Inr q) \<and> runs (auto.lts B) p w q"
  by (rule runs_Inr_closed_gen[OF _ assms]) (rule union_Inr_src)


text\<open>A run from the fresh start \<open>None\<close> either does nothing, or takes a silent bridge into one
  component and stays there:\<close>

lemma runs_None_split:
  assumes "runs (union_auto_eps_lts A B) None w Q"
  shows "Q = None \<or> (\<exists>q. Q = Some(Inl q) \<and> runs (auto.lts A) (auto.start A) w q)
    \<or> (\<exists>q. Q = Some(Inr q) \<and> runs (auto.lts B) (auto.start B) w q)"
  using assms
proof (cases rule: runs.cases)
  case Nil
  then show ?thesis by simp
next
  case (Eps X')
  from union_None_src[OF Eps(1)] show ?thesis
    by (metis Eps(2) runs_Inl_closed_union runs_Inr_closed_union)
next
  case (Sym c X' v)
  from union_None_src[OF Sym(2)] show ?thesis by simp
qed

theorem Lang_auto_eps_union_auto_eps_lts:
 "Lang_auto_eps (union_auto_eps A B) = Lang_auto_eps A \<union> Lang_auto_eps B"
proof (rule set_eqI)
  let ?T1 = "auto.lts A" let ?s1 = "auto.start A" let ?F1 = "auto.finals A"
  let ?T2 = "auto.lts B" let ?s2 = "auto.start B" let ?F2 = "auto.finals B"
  let ?U = "union_auto_eps_lts A B"
  let ?UA = "union_auto_eps A B"
  fix w
  have L: "(w \<in> Lang_auto_eps ?UA)
         = (\<exists>f\<in>(Some ` Inl ` ?F1 \<union> Some ` Inr ` ?F2). runs ?U None w f)"
    by (simp add: Lang_auto_eps_runs union_auto_eps_def)
  show "(w \<in> Lang_auto_eps ?UA)
      = (w \<in> Lang_auto_eps A \<union> Lang_auto_eps B)"
    unfolding L
  proof
    assume "\<exists>f\<in>(Some ` Inl ` ?F1 \<union> Some ` Inr ` ?F2). runs ?U None w f"
    then obtain f where f: "f \<in> Some ` Inl ` ?F1 \<union> Some ` Inr ` ?F2" "runs ?U None w f" by blast
    from runs_None_split[OF f(2)] f(1)
    consider (l) q where "q \<in> ?F1" "runs ?T1 ?s1 w q" | (r) q where "q \<in> ?F2" "runs ?T2 ?s2 w q"
      by auto
    then show "w \<in> Lang_auto_eps A \<union> Lang_auto_eps B"
      by (metis Lang_auto_eps_runs UnCI)
  next
    assume "w \<in> Lang_auto_eps A \<union> Lang_auto_eps B"
    then show "\<exists>f\<in>(Some ` Inl ` ?F1 \<union> Some ` Inr ` ?F2). runs ?U None w f"
    proof
      assume "w \<in> Lang_auto_eps A" thus ?thesis
        using Lang_auto_eps_runs bridgeL_in_union runs_Inl_union runs.Eps by (metis UnCI image_eqI)
    next
      assume "w \<in> Lang_auto_eps B" thus ?thesis
        using Lang_auto_eps_runs bridgeR_in_union runs_Inr_union runs.Eps by (metis UnCI image_eqI)
    qed
  qed
qed


subsection\<open>Kleene Star\<close>

text\<open>The star reuses the spare state \<open>None\<close> as a fresh start that is also accepting (for the empty
  word): a silent move enters the body at \<open>s\<close>, and every final loops silently back to \<open>None\<close>.\<close>

definition star_auto_lts_eps :: "('s,'l)auto_eps \<Rightarrow> ('s option,'l)lts_eps" where
"star_auto_lts_eps A = (\<Union>(p,c,q) \<in> auto.lts A. {(Some p, c, Some q)})
  \<union> {(None, None, Some (auto.start A))}
  \<union> (\<Union>f \<in> auto.finals A. {(Some f, None, None)})"

definition star_auto_eps :: "('s,'l)auto_eps \<Rightarrow> ('s option,'l)auto_eps" where
"star_auto_eps A = \<lparr> auto.lts = star_auto_lts_eps A, start = None, finals = {None} \<rparr>"

lemma lts_star_auto_eps: "auto.lts (star_auto_eps A) = star_auto_lts_eps A"
  by (simp add: star_auto_eps_def)

lemma finite_finals_star_auto_eps: "finite (auto.finals (star_auto_eps A))"
  by (simp add: star_auto_eps_def)

text\<open>Membership of the three kinds of edges, and the shape of the edges leaving a state:\<close>

lemma Some_in_star: "(p,a,q) \<in> auto.lts A \<Longrightarrow> (Some p, a, Some q) \<in> star_auto_lts_eps A"
  by (auto simp: star_auto_lts_eps_def)

lemma entry_in_star: "(None, None, Some (auto.start A)) \<in> star_auto_lts_eps A"
  by (auto simp: star_auto_lts_eps_def)

lemma loopback_in_star: "f \<in> auto.finals A \<Longrightarrow> (Some f, None, None) \<in> star_auto_lts_eps A"
  by (auto simp: star_auto_lts_eps_def)

lemma star_None_src: "(None, a, Y) \<in> star_auto_lts_eps A \<Longrightarrow> a = None \<and> Y = Some (auto.start A)"
  by (auto simp: star_auto_lts_eps_def)

lemma star_Some_src:
  "(Some p, a, Y) \<in> star_auto_lts_eps A \<Longrightarrow>
     (\<exists>q. Y = Some q \<and> (p,a,q) \<in> auto.lts A) \<or> (a = None \<and> Y = None \<and> p \<in> auto.finals A)"
  by (auto simp: star_auto_lts_eps_def)

text\<open>A \<open>T\<close>-run embeds as a run within the \<open>Some\<close> component:\<close>

lemma runs_Some_embed:
  "runs (auto.lts A) p w q \<Longrightarrow> runs (star_auto_lts_eps A) (Some p) w (Some q)"
  by (induction rule: runs.induct) (auto intro: runs.intros Some_in_star)

text\<open>A run ending in \<open>None\<close> decomposes the word: from \<open>None\<close> it is a word of the star language;
  from \<open>Some p\<close> it is a \<open>T\<close>-run to some final of \<open>F\<close> followed by a star-language suffix.\<close>

lemma star_run_aux:
  "runs (star_auto_lts_eps A) x w r \<Longrightarrow> r = None \<Longrightarrow>
     (x = None \<longrightarrow> w \<in> star (Lang_auto_eps A)) \<and>
     (\<forall>p. x = Some p \<longrightarrow>
        (\<exists>u v f. w = u @ v \<and> runs (auto.lts A) p u f \<and> f \<in> auto.finals A \<and> v \<in> star (Lang_auto_eps A)))"
     (is "_ \<Longrightarrow> _ \<Longrightarrow> ?P x w \<and> ?Q x w")
proof (induction rule: runs.induct)
  case (Nil p)
  then show ?case by simp
next
  case (Eps p q w r)
  note IH = Eps.IH[OF Eps.prems]
  have "?P p w" using Eps.hyps(1) IH Lang_auto_eps_runs append_in_starI star_None_src star_if_lang
    by (metis)
  moreover have "?Q p w" using star_Some_src IH append_Nil runs.Eps runs.Nil Eps.hyps(1)
    by (metis)
  ultimately show ?case by blast
next
  case (Sym p c q w r)
  have "?P p (c#w)" using Sym.hyps(1) star_None_src by fastforce
  moreover have B: "?Q p (c#w)"
    using Sym.IH[OF Sym.prems] Sym.hyps(1) runs.Sym star_Some_src by(metis append_Cons option.discI)
  ultimately show ?case by blast
qed

theorem Lang_auto_eps_star_auto_lts_eps:
  "Lang_auto_eps (star_auto_eps A) = star (Lang_auto_eps A)" (is "?L = ?R")
proof (rule set_eqI)
  fix w
  have L: "(w \<in> ?L) = runs (star_auto_lts_eps A) None w None"
    by (simp add: Lang_auto_eps_runs star_auto_eps_def)
  show "(w \<in> ?L) = (w \<in> ?R)"
    unfolding L
  proof
    assume "runs (star_auto_lts_eps A) None w None"
    from star_run_aux[OF this refl] show "w \<in> ?R" by simp
  next
    assume "w \<in> ?R"
    then show "runs (star_auto_lts_eps A) None w None"
    proof (induction rule: star_induct)
      case Nil
      show ?case by (rule runs.Nil)
    next
      case (append u v) then show ?case
        using Lang_auto_eps_runs runs.Eps entry_in_star runs_Some_embed loopback_in_star runs_append
        by (metis)
    qed
  qed
qed

text \<open>Test for executability:\<close>

lemma "elim_eps_auto (star_auto_eps (auto_eps_of(word_auto [False,True]))) =
  \<lparr> auto.lts =
    {(Some 1, True, Some 0), (Some 1, True, None), (Some 1, True, Some 2), (Some 0, False, Some 1),
     (None, False, Some 1), (Some 2, False, Some 1)},
    start = None, finals = {Some 0, None}\<rparr>"
  by eval

end
