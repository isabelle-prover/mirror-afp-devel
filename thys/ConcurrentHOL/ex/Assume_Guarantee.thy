(*<*)
theory Assume_Guarantee
imports
  "ConcurrentHOL.ConcurrentHOL"
begin

(*>*)
section\<open> Assume/Guarantee rule sets\label{sec:ag} \<close>

text\<open>

The rules in \<^theory>\<open>ConcurrentHOL.Refinement\<close> are deficient in various ways:
 \<^item> redundant stability requirements
 \<^item> interleaving of program decomposition with stability goals
 \<^item> insufficiently instantiated

The following are some experimental rules aimed at practical assume/guarantee reasoning.

\<close>


subsection\<open> Implicit stabilisation\label{sec:ag-implicit_stabilisation} \<close>

text\<open>

We can define a relation \<open>ceilr P\<close> to be the largest (weakest assumption) for which \<open>P\<close> is stable.
This always yields a preorder (i.e., it is reflexive and transitive). Later we use this to inline
stability side conditions into assume/guarantee rules (\S\ref{sec:ag-iag}).

This relation is not very pleasant to work with: it is not monotonic
and does not have many useful algebraic properties. However it
suffices to defer the checking of assumes (see \S\ref{sec:ag-iag}).

This is a cognate of the \<^emph>\<open>strongest guarantee\<close> used by
\<^citet>\<open>\<open>Definition~8.31\<close> in "deRoeverEtAl:2001"\<close> in their completeness proof for the rely-guarantee
method.

\<close>

definition ceilr :: "'a pred \<Rightarrow> 'a rel" where
  "ceilr P = \<Squnion>{r. stable r P}"

lemma ceilr_alt_def:
  shows "ceilr P = {(s, s'). P s \<longrightarrow> P s'}"
by (auto simp: ceilr_def stable_def monotone_def le_bool_def order_eq_iff Sup_upper)

lemma ceilrE[elim]:
  assumes "(x, y) \<in> ceilr P"
  assumes "P x"
  shows "P y"
using assms by (simp add: ceilr_alt_def)

setup \<open>Sign.mandatory_path "ceilr"\<close>

named_theorems simps \<open>simp rules for \<^const>\<open>ceilr\<close>\<close>

lemma bot[ceilr.simps]:
  shows "ceilr \<bottom> = UNIV"
by (simp_all add: ceilr_alt_def)

lemma top[ceilr.simps]:
  shows "ceilr \<top> = UNIV"
by (simp_all add: ceilr_alt_def)

lemma const[ceilr.simps]:
  shows "ceilr \<langle>c\<rangle> = UNIV"
    and "ceilr (P \<^bold>\<and> \<langle>c\<rangle>) = (if c then ceilr P else UNIV)"
    and "ceilr (\<langle>c\<rangle> \<^bold>\<and> P) = (if c then ceilr P else UNIV)"
    and "ceilr (P \<^bold>\<and> \<langle>c\<rangle> \<^bold>\<and> P') = (if c then ceilr (P \<^bold>\<and> P') else UNIV)"
by (simp_all add: ceilr_alt_def)

lemma Id_le:
  shows "Id \<subseteq> ceilr P"
by (auto simp: ceilr_alt_def)

lemmas refl[iff] = ceilr.Id_le[folded refl_alt_def]

lemma trans[iff]:
  shows "trans (ceilr P)"
by (simp add: ceilr_alt_def trans_def)

lemma stable[stable.intro]:
  shows "stable (ceilr P) P"
by (simp add: ceilr_def stable.Union_conv)

lemma largest[stable.intro]:
  assumes "stable r P"
  shows "r \<subseteq> ceilr P"
by (simp add: ceilr_def assms Sup_upper)

lemma disj_subseteq: \<comment>\<open> Converse does not hold \<close>
  shows "ceilr (P \<^bold>\<or> Q) \<subseteq> ceilr P \<union> ceilr Q"
by (fastforce simp: ceilr_alt_def)

lemma Ex_subseteq: \<comment>\<open> Converse does not hold \<close>
  shows "ceilr (\<^bold>\<exists>x. P x) \<subseteq> (\<Union>x. ceilr (P x))"
by (fastforce simp: ceilr_alt_def)

lemma conj_subseteq: \<comment>\<open> Converse does not hold \<close>
  shows "ceilr P \<inter> ceilr Q \<subseteq> ceilr (P \<^bold>\<and> Q)"
by (fastforce simp: ceilr_alt_def)

lemma All_subseteq: \<comment>\<open> Converse does not hold \<close>
  shows "(\<Inter>x. ceilr (P x)) \<subseteq> ceilr (\<^bold>\<forall>x. P x)"
by (fastforce simp: ceilr_alt_def)

lemma const_implies[ceilr.simps]:
  shows "ceilr (\<langle>P\<rangle> \<^bold>\<longrightarrow> Q) = (if P then ceilr Q else UNIV)"
by (simp add: ceilr.simps)

lemma Id_proj_on:
  shows "(\<Inter>c. ceilr (\<langle>c\<rangle> \<^bold>= f)) = Id\<^bsub>f\<^esub>"
    and "(\<Inter>c. ceilr (f \<^bold>= \<langle>c\<rangle>)) = Id\<^bsub>f\<^esub>"
by (fastforce simp: ceilr_alt_def)+

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "stable"\<close>

lemma Inter_ceilr:
  shows "stable (\<Inter>v. ceilr (Q v)) (Q v)"
by (rule antimonoD[where y="ceilr (Q v)", OF stable.antimono_rel, unfolded le_bool_def, rule_format, rotated])
   (auto simp: ceilr.stable)

setup \<open>Sign.parent_path\<close>

text\<open>

We can internalize the stability conditions; see \S\ref{sec:ag-iag} for further discussion.

\<close>

setup \<open>Sign.mandatory_path "ag.prog"\<close>

lemma p2s_s2p_ag_ceilr:
  shows "prog.p2s (prog.s2p (\<lbrace>P\<rbrace>, ceilr P \<inter> (\<Inter>v. ceilr (Q v)) \<turnstile> G, \<lbrace>Q\<rbrace>))
       = \<lbrace>P\<rbrace>, ceilr P \<inter> (\<Inter>v. ceilr (Q v)) \<turnstile> G, \<lbrace>Q\<rbrace>"
by (simp add: ag.prog.p2s_s2p_ag_stable ceilr.stable stable.Inter_ceilr stable.infI)

setup \<open>Sign.parent_path\<close>


subsubsection\<open> Assume/guarantee rules using implicit stability\label{sec:ag-iag} \<close>

text\<open>

We use \<^const>\<open>ceilr\<close> to incorporate stability side conditions directly into the assume/guarantee
rules. In other words, instead of working with arbitrary relations, we work with the largest
(most general) \<^emph>\<open>assume\<close> that makes the relevant predicates \<^const>\<open>stable\<close>.

In practice this allows us to defer all stability obligations to the end of a proof, which may be
in any convenient context (typically a function). This approach could be considered a semantic
version of how \<^citet>\<open>"ZakowskiEtAl:2019"\<close> split sequential and assume/guarantee reasoning.
See \<^citet>\<open>\<open>\S4\<close> in "Vafeiadis:2008"\<close> for a discussion on when to check stability.

We defer the \<^emph>\<open>guarantee\<close> proofs by incorporating them into preconditions. This also allows
control flow context to be accumulated.

These are backchaining (``weakest precondition'') rules: the guarantee and post condition
need to be instantiated and the rules instantiate assume and pre condition schematics.

Note that the rule for \<^const>\<open>prog.bind\<close> duplicates stability goals.

See \S\ref{sec:ex_findP} for an example of using these rules.

\<close>

setup \<open>Sign.mandatory_path "iag"\<close>

named_theorems intro \<open>safe backchaining intro rules\<close>

lemma init:
  assumes "c \<le> \<lbrace>P\<rbrace>, A \<turnstile> G, \<lbrace>Q\<rbrace>"
  assumes "\<And>s. P' s \<Longrightarrow> P s"
  assumes "A' \<subseteq> A" \<comment>\<open> these rules use \<^const>\<open>ceilr\<close> which always yields a reflexive relation (@{thm [source] "ceilr.refl"} \<close>
  shows "c \<le> \<lbrace>P'\<rbrace>, A' \<turnstile> G, \<lbrace>Q\<rbrace>"
using assms(2,3) by (auto intro: ag.mono order.trans[OF assms(1)])

lemmas mono = ag.mono

lemmas gen_asm = ag.gen_asm

lemmas pre = ag.pre
lemmas pre_pre = ag.pre_pre
lemmas pre_post = ag.pre_post
lemmas pre_ag = ag.pre_ag
lemmas pre_a = ag.pre_a
lemmas pre_g = ag.pre_g

lemmas post_imp = ag.post_imp

lemmas conj_lift = ag.conj_lift
lemmas disj_lift = ag.disj_lift
lemmas all_lift = ag.all_lift

lemmas augment_a = ag.augment_a
lemmas augment_post = ag.augment_post
lemmas augment_post_imp = ag.augment_post_imp

lemmas stable_augment_base = ag.stable_augment_base
lemmas stable_augment = ag.stable_augment
lemmas stable_augment_post = ag.stable_augment_post
lemmas stable_augment_frame = ag.stable_augment_frame

lemma bind[iag.intro]:
  assumes "\<And>v. prog.p2s (g v) \<le> \<lbrace>Q' v\<rbrace>, A\<^sub>2 v \<turnstile> G, \<lbrace>Q\<rbrace>"
  assumes "prog.p2s f \<le> \<lbrace>P\<rbrace>, A\<^sub>1 \<turnstile> G, \<lbrace>Q'\<rbrace>"
  shows "prog.p2s (f \<bind> g) \<le> \<lbrace>P\<rbrace>, A\<^sub>1 \<inter> (\<Inter>v. A\<^sub>2 v) \<turnstile> G, \<lbrace>Q\<rbrace>"
by (auto simp: prog.p2s.simps intro: assms ag.spec.bind ag.pre)

lemmas rev_bind = iag.bind[rotated]

lemma read[iag.intro]:
  shows "prog.p2s (prog.read F) \<le> \<lbrace>\<lambda>s. Q (F s) s\<rbrace>, ceilr (\<lambda>s. Q (F s) s) \<inter> (\<Inter>s. ceilr (Q (F s))) \<turnstile> G, \<lbrace>Q\<rbrace>"
by (rule ag.pre[OF ag.prog.action[where P="\<lambda>s. Q (F s) s"
                                    and Q=Q
                                    and A="ceilr (\<lambda>s. Q (F s) s) \<inter> (\<Inter>s. ceilr (Q (F s)))"
                                    and G=G]];
    fastforce intro: stable.intro stable.Inter_ceilr stable.infI)

lemma return[iag.intro]:
  shows "prog.p2s (prog.return v) \<le> \<lbrace>Q v\<rbrace>, ceilr (Q v) \<turnstile> G, \<lbrace>Q\<rbrace>"
unfolding prog.return_alt_def by (rule iag.init[OF iag.read]; fastforce)

lemma "write"[iag.intro]: \<comment>\<open> this is where \<^emph>\<open>guarantee\<close> obligations arise \<close>
  shows "prog.p2s (prog.write F)
      \<le> \<lbrace>(\<lambda>s. Q () (F s) \<and> (s, F s) \<in> G)\<rbrace>, ceilr (\<lambda>s. Q () (F s) \<and> (s, F s) \<in> G) \<inter> ceilr (Q ()) \<turnstile> G, \<lbrace>Q\<rbrace>"
by (rule ag.prog.action; fastforce intro: stable.intro stable.Inter_ceilr stable.infI1 stable.infI2)

lemma parallel: \<comment>\<open> not in the \<open>iag\<close> format; instantiate the first two assumptions \<close>
  assumes "prog.p2s c\<^sub>1 \<le> \<lbrace>P\<^sub>1\<rbrace>, A\<^sub>1 \<turnstile> G\<^sub>1, \<lbrace>Q\<^sub>1\<rbrace>"
  assumes "prog.p2s c\<^sub>2 \<le> \<lbrace>P\<^sub>2\<rbrace>, A\<^sub>2 \<turnstile> G\<^sub>2, \<lbrace>Q\<^sub>2\<rbrace>"
  assumes "\<And>s. \<lbrakk>Q\<^sub>1 () s; Q\<^sub>2 () s\<rbrakk> \<Longrightarrow> Q () s"
  assumes "G\<^sub>2 \<subseteq> A\<^sub>1"
  assumes "G\<^sub>1 \<subseteq> A\<^sub>2"
  assumes "G\<^sub>1 \<union> G\<^sub>2 \<subseteq> G"
  shows "prog.p2s (prog.parallel c\<^sub>1 c\<^sub>2) \<le> \<lbrace>P\<^sub>1 \<^bold>\<and> P\<^sub>2\<rbrace>, A\<^sub>1 \<inter> A\<^sub>2 \<turnstile> G, \<lbrace>Q\<rbrace>"
by (rule order.trans[OF ag.prog.parallel[OF iag.pre_a[OF assms(1)] iag.pre_a[OF assms(2)],
                                         where A="A\<^sub>1 \<inter> A\<^sub>2", simplified, OF \<open>G\<^sub>2 \<subseteq> A\<^sub>1\<close> \<open>G\<^sub>1 \<subseteq> A\<^sub>2\<close>]];
    use assms(3,6) in \<open>force intro: iag.mono\<close>)

lemmas local = ag.prog.local \<comment>\<open> not in the \<open>iag\<close> format \<close>

lemma "if"[iag.intro]:
  assumes "b \<Longrightarrow> prog.p2s c\<^sub>1 \<le> \<lbrace>P\<^sub>1\<rbrace>, A\<^sub>1 \<turnstile> G, \<lbrace>Q\<rbrace>"
  assumes "\<not>b \<Longrightarrow> prog.p2s c\<^sub>2 \<le> \<lbrace>P\<^sub>2\<rbrace>, A\<^sub>2 \<turnstile> G, \<lbrace>Q\<rbrace>"
  shows "prog.p2s (if b then c\<^sub>1 else c\<^sub>2) \<le> \<lbrace>if b then P\<^sub>1 else P\<^sub>2\<rbrace>, A\<^sub>1 \<inter> A\<^sub>2 \<turnstile> G, \<lbrace>Q\<rbrace>"
using assms by (fastforce intro: ag.pre_ag)

lemma case_option[iag.intro]:
  assumes "x = None \<Longrightarrow> prog.p2s none \<le> \<lbrace>P\<^sub>n\<rbrace>, A\<^sub>n \<turnstile> G, \<lbrace>Q\<rbrace>"
  assumes "\<And>v. x = Some v \<Longrightarrow> prog.p2s (some v) \<le> \<lbrace>P\<^sub>s v\<rbrace>, A\<^sub>s v \<turnstile> G, \<lbrace>Q\<rbrace>"
  shows "prog.p2s (case_option none some x) \<le> \<lbrace>case x of None \<Rightarrow> P\<^sub>n | Some v \<Rightarrow> P\<^sub>s v\<rbrace>, case_option A\<^sub>n A\<^sub>s x \<turnstile> G, \<lbrace>Q\<rbrace>"
using assms by (fastforce intro: ag.pre_ag split: option.split)

lemma case_sum[iag.intro]:
  assumes "\<And>v. x = Inl v \<Longrightarrow> prog.p2s (left v) \<le> \<lbrace>P\<^sub>l v\<rbrace>, A\<^sub>l v \<turnstile> G, \<lbrace>Q\<rbrace>"
  assumes "\<And>v. x = Inr v \<Longrightarrow> prog.p2s (right v) \<le> \<lbrace>P\<^sub>r v\<rbrace>, A\<^sub>r v \<turnstile> G, \<lbrace>Q\<rbrace>"
  shows "prog.p2s (case_sum left right x) \<le> \<lbrace>case_sum P\<^sub>l P\<^sub>r x\<rbrace>, case_sum A\<^sub>l A\<^sub>r x \<turnstile> G, \<lbrace>Q\<rbrace>"
using assms by (fastforce intro: ag.pre_ag split: sum.split)

lemma case_list[iag.intro]:
  assumes "x = [] \<Longrightarrow> prog.p2s nil \<le> \<lbrace>P\<^sub>n\<rbrace>, A\<^sub>n \<turnstile> G, \<lbrace>Q\<rbrace>"
  assumes "\<And>v vs. x = v # vs \<Longrightarrow> prog.p2s (cons v vs) \<le> \<lbrace>P\<^sub>c v vs\<rbrace>, A\<^sub>c v vs \<turnstile> G, \<lbrace>Q\<rbrace>"
  shows "prog.p2s (case_list nil cons x) \<le> \<lbrace>case_list P\<^sub>n P\<^sub>c x\<rbrace>, case_list A\<^sub>n A\<^sub>c x \<turnstile> G, \<lbrace>Q\<rbrace>"
using assms by (fastforce intro: ag.pre_ag split: list.split)

lemma while:
  fixes c :: "'k \<Rightarrow> ('s, 'k + 'v) prog"
  assumes c: "\<And>k. prog.p2s (c k) \<le> \<lbrace>P k\<rbrace>, A \<turnstile> G, \<lbrace>case_sum I Q\<rbrace>"
  shows "prog.p2s (prog.while c k) \<le> \<lbrace>\<langle>\<forall>v s. I v s \<longrightarrow> P v s\<rangle> \<^bold>\<and> I k\<rbrace>, A \<inter> (\<Inter>v. ceilr (Q v)) \<turnstile> G, \<lbrace>Q\<rbrace>"
by (rule iag.gen_asm)
   (rule ag.prog.while[OF ag.pre_a[OF c]]; blast intro: stable.Inter_ceilr stable.infI2)

lemmas whenM = iag.if[where c\<^sub>1=c and A\<^sub>1=A and P\<^sub>1=P, OF _ iag.return[where v="()"]] for A c P

setup \<open>Sign.parent_path\<close>


subsection\<open> Refinement with relational assumes\label{sec:ag-rar} \<close>

text\<open>

Two sets of refinement rules:
 \<^item> relational assumes
 \<^item> relational assumes and \<open>prog.sinvmap\<close> (inverse state abstraction)

\<close>

setup \<open>Sign.mandatory_path "rar.prog"\<close>

lemma bind:
  assumes "\<And>v. prog.p2s (g v) \<le> \<lbrace>Q' v\<rbrace>, ag.assm A \<tturnstile> prog.p2s (g' v), \<lbrace>Q\<rbrace>"
  assumes "prog.p2s f \<le> \<lbrace>P\<rbrace>, ag.assm A \<tturnstile> prog.p2s f', \<lbrace>Q'\<rbrace>"
  shows "prog.p2s (f \<bind> g) \<le> \<lbrace>P\<rbrace>, ag.assm A \<tturnstile> prog.p2s (f' \<bind> g'), \<lbrace>Q\<rbrace>"
by (rule refinement.prog.bind[OF refinement.pre_a[OF assms(1) refinement.spec.bind.res.rel_le[OF order.refl]]])
   (simp add: spec.term.all.rel assms(2))

lemmas rev_bind = rar.prog.bind[rotated]

lemma action:
  fixes F :: "('v \<times> 's \<times> 's) set"
  fixes F' :: "('v \<times> 's \<times> 's) set"
  assumes Q: "\<And>v s s'. \<lbrakk>P s; (v, s, s') \<in> F\<rbrakk> \<Longrightarrow> Q v s'"
  assumes F': "\<And>v s s'. \<lbrakk>P s; (v, s, s') \<in> F\<rbrakk> \<Longrightarrow> (v, s, s') \<in> F'"
  assumes sP: "stable A P"
  assumes sQ: "\<And>v s s'. \<lbrakk>P s; (v, s, s') \<in> F\<rbrakk> \<Longrightarrow> stable A (Q v)"
  shows "prog.p2s (prog.action F) \<le> \<lbrace>P\<rbrace>, ag.assm A \<tturnstile> prog.p2s (prog.action F'), \<lbrace>Q\<rbrace>"
by (rule refinement.prog.action)
   (use assms in \<open>simp_all add: spec.steps.rel stable_def monotone_def\<close>)

lemma return:
  assumes sQ: "stable A (Q v)"
  shows "prog.p2s (prog.return v) \<le> \<lbrace>Q v\<rbrace>, ag.assm A \<tturnstile> prog.p2s (prog.return v), \<lbrace>Q\<rbrace>"
using assms by (simp add: refinement.prog.return spec.steps.rel stable_def monotone_def)

lemma parallel_refinement:
  assumes c\<^sub>1: "prog.p2s c\<^sub>1 \<le> \<lbrace>P\<^sub>1\<rbrace>, ag.assm (A \<union> G\<^sub>2) \<tturnstile> prog.p2s (c\<^sub>1' \<sqinter> prog.rel G\<^sub>1), \<lbrace>Q\<^sub>1\<rbrace>"
  assumes c\<^sub>2: "prog.p2s c\<^sub>2 \<le> \<lbrace>P\<^sub>2\<rbrace>, ag.assm (A \<union> G\<^sub>1) \<tturnstile> prog.p2s (c\<^sub>2' \<sqinter> prog.rel G\<^sub>2), \<lbrace>Q\<^sub>2\<rbrace>"
  shows "prog.p2s (c\<^sub>1 \<parallel> c\<^sub>2) \<le> \<lbrace>P\<^sub>1 \<^bold>\<and> P\<^sub>2\<rbrace>, ag.assm A \<tturnstile> prog.p2s (c\<^sub>1' \<sqinter> prog.rel G\<^sub>1 \<parallel> c\<^sub>2' \<sqinter> prog.rel G\<^sub>2), \<lbrace>\<lambda>v. Q\<^sub>1 v \<^bold>\<and> Q\<^sub>2 v\<rbrace>"
apply (rule refinement.prog.parallel[OF refinement.pre_a[OF c\<^sub>1] refinement.pre_a[OF c\<^sub>2]])
 apply (rule order.trans[OF refinement.spec.env_hyp.mono[OF order.refl] ag.spec.Parallel_assm[where a=True and as=UNIV and G="\<lambda>a. if a then G\<^sub>1 else G\<^sub>2", simplified]];
        simp add: ac_simps prog.p2s.simps; fail)
apply (rule order.trans[OF refinement.spec.env_hyp.mono[OF order.refl] ag.spec.Parallel_assm[where a=False and as=UNIV and G="\<lambda>a. if a then G\<^sub>1 else G\<^sub>2", simplified]];
       simp add: ac_simps prog.p2s.simps; fail)
done

lemma parallel:
  assumes "prog.p2s c\<^sub>1 \<le> \<lbrace>P\<^sub>1\<rbrace>, ag.assm (A \<union> G\<^sub>2) \<tturnstile> prog.p2s c\<^sub>1', \<lbrace>Q\<^sub>1\<rbrace>"
  assumes "prog.p2s c\<^sub>1 \<le> \<lbrace>P\<^sub>1\<rbrace>, A \<union> G\<^sub>2 \<turnstile> G\<^sub>1, \<lbrace>\<top>\<rbrace>"
  assumes "prog.p2s c\<^sub>2 \<le> \<lbrace>P\<^sub>2\<rbrace>, ag.assm (A \<union> G\<^sub>1) \<tturnstile> prog.p2s c\<^sub>2', \<lbrace>Q\<^sub>2\<rbrace>"
  assumes "prog.p2s c\<^sub>2 \<le> \<lbrace>P\<^sub>2\<rbrace>, A \<union> G\<^sub>1 \<turnstile> G\<^sub>2, \<lbrace>\<top>\<rbrace>"
  shows "prog.p2s (c\<^sub>1 \<parallel> c\<^sub>2) \<le> \<lbrace>P\<^sub>1 \<^bold>\<and> P\<^sub>2\<rbrace>, ag.assm A \<tturnstile> prog.p2s (c\<^sub>1' \<parallel> c\<^sub>2'), \<lbrace>\<lambda>v. Q\<^sub>1 v \<^bold>\<and> Q\<^sub>2 v\<rbrace>"
by (rule order.trans[OF rar.prog.parallel_refinement
                        refinement.mono[OF order.refl order.refl prog.p2s.mono[OF prog.parallel.mono[OF inf.cobounded1 inf.cobounded1]] order.refl]])
   (force simp: prog.p2s.simps refinement.infR_conv[where Q\<^sub>2=\<top>, simplified]
         simp flip: ag.refinement
             intro: assms)+

lemma while:
  fixes c :: "'k \<Rightarrow> ('s, 'k + 'v) prog"
  fixes c' :: "'k \<Rightarrow> ('s, 'k + 'v) prog"
  assumes c: "\<And>k. prog.p2s (c k) \<le> \<lbrace>P k\<rbrace>, ag.assm A \<tturnstile> prog.p2s (c' k), \<lbrace>case_sum I Q\<rbrace>"
  assumes IP: "\<And>s v. I v s \<Longrightarrow> P v s"
  assumes sQ: "\<And>v. stable A (Q v)"
  shows "prog.p2s (prog.while c k) \<le> \<lbrace>I k\<rbrace>, ag.assm A \<tturnstile> prog.p2s (prog.while c' k), \<lbrace>Q\<rbrace>"
proof -
  have "\<forall>k. prog.p2s (prog.while c k) \<le> \<lbrace>P k\<rbrace>, ag.assm A \<tturnstile> prog.p2s (prog.while c' k), \<lbrace>Q\<rbrace>"
  proof(induct rule: prog.while.fixp_induct[where P="\<lambda>R. \<forall>k. prog.p2s (R c k) \<le> \<lbrace>P k\<rbrace>, ag.assm A \<tturnstile> prog.p2s (prog.while c' k), \<lbrace>Q\<rbrace>", case_names adm bot step])
    case (step R) from sQ show ?case
      apply (subst prog.while.simps)
      apply (intro allI rar.prog.rev_bind[OF c]
                   refinement.pre_pre[OF refinement.prog.case_sum[OF step[rule_format]
                                                                     rar.prog.return[OF sQ]]])
      apply (simp add: IP split: sum.splits)
      done
  qed simp_all
  then show ?thesis
    by (meson IP refinement.pre_pre)
qed

lemma app:
  fixes xs :: "'a list"
  fixes f :: "'a \<Rightarrow> ('s, unit) prog"
  fixes P :: "'a list \<Rightarrow> 's pred"
  assumes "\<And>x ys zs. xs = ys @ x # zs \<Longrightarrow> prog.p2s (f x) \<le> \<lbrace>P ys\<rbrace>, ag.assm A \<tturnstile> prog.p2s (f' x), \<lbrace>\<lambda>_. P (ys @ [x])\<rbrace>"
  assumes "\<And>ys. prefix ys xs \<Longrightarrow> stable A (P ys)"
  shows "prog.p2s (prog.app f xs) \<le> \<lbrace>P []\<rbrace>, ag.assm A \<tturnstile> prog.p2s (prog.app f' xs), \<lbrace>\<lambda>_. P xs\<rbrace>"
using assms
by (induct xs rule: rev_induct;
    force intro: rar.prog.return
           simp: prog.app.append prog.app.simps spec.steps.rel prog.bind.return rar.prog.rev_bind)

lemmas "if" = refinement.prog.if[where A="ag.assm A" for A]
lemmas case_option = refinement.prog.case_option[where A="ag.assm A" for A]

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "rair.prog"\<close>

abbreviation (input) "absfn sf c \<equiv> prog.p2s (prog.sinvmap sf c)"

lemma bind:
  assumes "\<And>v. prog.p2s (g v) \<le> \<lbrace>Q' v\<rbrace>, ag.assm A \<tturnstile> rair.prog.absfn sf (g' v), \<lbrace>Q\<rbrace>"
  assumes "prog.p2s f \<le> \<lbrace>P\<rbrace>, ag.assm A \<tturnstile> rair.prog.absfn sf f', \<lbrace>Q'\<rbrace>"
  shows "prog.p2s (f \<bind> g) \<le> \<lbrace>P\<rbrace>, ag.assm A \<tturnstile> rair.prog.absfn sf (f' \<bind> g'), \<lbrace>Q\<rbrace>"
by (simp add: prog.invmap.bind rar.prog.bind[OF assms])

lemmas rev_bind = rair.prog.bind[rotated]

lemma action:
  fixes F :: "('v \<times> 's \<times> 's) set"
  fixes F' :: "('v \<times> 't \<times> 't) set"
  fixes sf :: "'s \<Rightarrow> 't"
  assumes Q: "\<And>v s s'. \<lbrakk>P s; (v, s, s') \<in> F\<rbrakk> \<Longrightarrow> Q v s'"
  assumes F': "\<And>v s s'. \<lbrakk>P s; (v, s, s') \<in> F\<rbrakk> \<Longrightarrow> (v, sf s, sf s') \<in> F'"
  assumes sP: "stable A P"
  assumes sQ: "\<And>v s s'. \<lbrakk>P s; (v, s, s') \<in> F\<rbrakk> \<Longrightarrow> stable A (Q v)"
  shows "prog.p2s (prog.action F) \<le> \<lbrace>P\<rbrace>, ag.assm A \<tturnstile> rair.prog.absfn sf (prog.action F'), \<lbrace>Q\<rbrace>"
by (strengthen ord_to_strengthen(2)[OF prog.action.invmap_le])
   (simp add: rar.prog.action assms)

lemma return:
  assumes sQ: "stable A (Q v)"
  shows "prog.p2s (prog.return v) \<le> \<lbrace>Q v\<rbrace>, ag.assm A \<tturnstile> rair.prog.absfn sf (prog.return v), \<lbrace>Q\<rbrace>"
using assms by (simp add: refinement.prog.invmap_return spec.steps.rel stable_def monotone_def)

lemma parallel:
  fixes sf :: "'s \<Rightarrow> 't"
  assumes "prog.p2s c\<^sub>1 \<le> \<lbrace>P\<^sub>1\<rbrace>, ag.assm (A \<union> G\<^sub>2) \<tturnstile> rair.prog.absfn sf c\<^sub>1', \<lbrace>Q\<^sub>1\<rbrace>"
  assumes "prog.p2s c\<^sub>1 \<le> \<lbrace>P\<^sub>1\<rbrace>, A \<union> G\<^sub>2 \<turnstile> G\<^sub>1, \<lbrace>\<top>\<rbrace>"
  assumes "prog.p2s c\<^sub>2 \<le> \<lbrace>P\<^sub>2\<rbrace>, ag.assm (A \<union> G\<^sub>1) \<tturnstile> rair.prog.absfn sf c\<^sub>2', \<lbrace>Q\<^sub>2\<rbrace>"
  assumes "prog.p2s c\<^sub>2 \<le> \<lbrace>P\<^sub>2\<rbrace>, A \<union> G\<^sub>1 \<turnstile> G\<^sub>2, \<lbrace>\<top>\<rbrace>"
  shows "prog.p2s (c\<^sub>1 \<parallel> c\<^sub>2) \<le> \<lbrace>P\<^sub>1 \<^bold>\<and> P\<^sub>2\<rbrace>, ag.assm A \<tturnstile> rair.prog.absfn sf (c\<^sub>1' \<parallel> c\<^sub>2'), \<lbrace>\<lambda>v. Q\<^sub>1 v \<^bold>\<and> Q\<^sub>2 v\<rbrace>"
unfolding prog.invmap.parallel by (rule rar.prog.parallel[OF assms])

lemma while:
  fixes c :: "'k \<Rightarrow> ('s, 'k + 'v) prog"
  fixes c' :: "'k \<Rightarrow> ('t, 'k + 'v) prog"
  fixes sf :: "'s \<Rightarrow> 't"
  assumes c: "\<And>k. prog.p2s (c k) \<le> \<lbrace>P k\<rbrace>, ag.assm A \<tturnstile> rair.prog.absfn sf (c' k), \<lbrace>case_sum I Q\<rbrace>"
  assumes IP: "\<And>s v. I v s \<Longrightarrow> P v s"
  assumes sQ: "\<And>v. stable A (Q v)"
  shows "prog.p2s (prog.while c k) \<le> \<lbrace>I k\<rbrace>, ag.assm A \<tturnstile> rair.prog.absfn sf (prog.while c' k), \<lbrace>Q\<rbrace>"
by (strengthen ord_to_strengthen(2)[OF prog.while.invmap_le])
   (simp add: assms map_sum.id rar.prog.while[OF c])

lemma app:
  fixes xs :: "'a list"
  fixes f :: "'a \<Rightarrow> ('s, unit) prog"
  fixes P :: "'a list \<Rightarrow> 's pred"
  assumes "\<And>x ys zs. xs = ys @ x # zs \<Longrightarrow> prog.p2s (f x) \<le> \<lbrace>P ys\<rbrace>, ag.assm A \<tturnstile> rair.prog.absfn sf (f' x), \<lbrace>\<lambda>_. P (ys @ [x])\<rbrace>"
  assumes "\<And>ys. prefix ys xs \<Longrightarrow> stable A (P ys)"
  shows "prog.p2s (prog.app f xs) \<le> \<lbrace>P []\<rbrace>, ag.assm A \<tturnstile> rair.prog.absfn sf (prog.app f' xs), \<lbrace>\<lambda>_. P xs\<rbrace>"
by (strengthen ord_to_strengthen(2)[OF prog.sinvmap.app_le])
   (simp add: rar.prog.app assms)

lemma "if":
  assumes "i \<Longrightarrow> prog.p2s t \<le> \<lbrace>P\<rbrace>, ag.assm A \<tturnstile> rair.prog.absfn sf t', \<lbrace>Q\<rbrace>"
  assumes "\<not>i \<Longrightarrow> prog.p2s e \<le> \<lbrace>P'\<rbrace>, ag.assm A \<tturnstile> rair.prog.absfn sf e', \<lbrace>Q\<rbrace>"
  shows "prog.p2s (if i then t else e) \<le> \<lbrace>if i then P else P'\<rbrace>, ag.assm A \<tturnstile> rair.prog.absfn sf (if i then t' else e'), \<lbrace>Q\<rbrace>"
using assms by fastforce

lemma case_option:
  assumes "opt = None \<Longrightarrow> prog.p2s none \<le> \<lbrace>P\<^sub>n\<rbrace>, ag.assm A \<tturnstile> rair.prog.absfn sf none', \<lbrace>Q\<rbrace>"
  assumes "\<And>v. opt = Some v \<Longrightarrow> prog.p2s (some v) \<le> \<lbrace>P\<^sub>s v\<rbrace>, ag.assm A \<tturnstile> rair.prog.absfn sf (some' v), \<lbrace>Q\<rbrace>"
  shows "prog.p2s (case_option none some opt) \<le> \<lbrace>case opt of None \<Rightarrow> P\<^sub>n | Some v \<Rightarrow> P\<^sub>s v\<rbrace>, ag.assm A \<tturnstile> rair.prog.absfn sf (case_option none' some' opt), \<lbrace>Q\<rbrace>"
using assms by (simp add: option.case_eq_if)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.parent_path\<close>
(*<*)

end
(*>*)
