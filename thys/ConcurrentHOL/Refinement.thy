(*<*)
theory Refinement
imports
  Constructions
  Next_Imp
  Stability
begin

(*>*)
section\<open> Refinement\label{sec:refinement} \<close>

text\<open>

We develop a refinement story for the \<^typ>\<open>('a, 's, 'v) spec\<close> lattice.

References:
 \<^item> \<^citet>\<open>"Vafeiadis:2008"\<close> (RGsep, program logic) and \<^citet>\<open>"LiangFenFu:2014"\<close> (RGsim, refinement)
 \<^item> \<^citet>\<open>"ArmstrongGomesStruth:2014"\<close>
 \<^item> \<^citet>\<open>"vanStaden:2015"\<close>

\<close>

definition refinement :: "'s pred \<Rightarrow> ('a, 's, 'v) spec \<Rightarrow> ('a, 's, 'v) spec \<Rightarrow> ('v \<Rightarrow> 's pred) \<Rightarrow> ('a, 's, 'v) spec" ("\<lbrace>_\<rbrace>, _ \<tturnstile> _, \<lbrace>_\<rbrace>" [0,0,0,0] 100) where
  "\<lbrace>P\<rbrace>, A \<tturnstile> G, \<lbrace>Q\<rbrace> = spec.pre P \<sqinter> A \<^bold>\<longrightarrow>\<^sub>+ G \<sqinter> spec.post Q"

text\<open>

An intuitive gloss on the proposition \<open>c \<le> \<lbrace>P\<rbrace>, A \<tturnstile> G, \<lbrace>Q\<rbrace>\<close> is: assuming the precondition \<open>P\<close> holds
and all steps conform to the process \<open>A\<close>, then \<open>c\<close> is a refinement of \<open>G\<close> and satisfies
the postcondition \<open>Q\<close>.

Observations:
 \<^item> We use \<^const>\<open>next_imp\<close> here;\<^const>\<open>heyting\<close> is (only) enough for an assume/guarantee program logic (see \S\ref{sec:refinement-ag})
 \<^item> \<open>A\<close> is arbitrary but is intended to constrain only \<^const>\<open>env\<close> steps
  \<^item> similarly termination can depend on \<open>A\<close>: a parallel composition can only terminate if all of its constituent processes terminate
 \<^item> As \<open>P \<^bold>\<longrightarrow>\<^sub>+ Q\<close> implies \<open>idle \<le> Q\<close>, in practice \<open>idle \<le> G\<close>
 \<^item> see \S\ref{sec:programs-refinement-intros} for some introduction rules

\<close>

setup \<open>Sign.mandatory_path "refinement"\<close>

lemma E:
  assumes "c \<le> \<lbrace>P\<rbrace>, A \<tturnstile> G, \<lbrace>Q\<rbrace>"
  obtains "c \<le> spec.pre P \<sqinter> A \<^bold>\<longrightarrow>\<^sub>+ G"
      and "c \<le> spec.pre P \<sqinter> A \<^bold>\<longrightarrow>\<^sub>+ spec.post Q"
using assms by (simp add: refinement_def spec.next_imp.infR)

lemma pre_post_cong:
  assumes "P = P'"
  assumes "Q = Q'"
  shows "\<lbrace>P\<rbrace>, A \<tturnstile> G, \<lbrace>Q\<rbrace> = \<lbrace>P'\<rbrace>, A \<tturnstile> G, \<lbrace>Q'\<rbrace>"
using assms by simp

lemma top:
  shows "\<lbrace>P\<rbrace>, A \<tturnstile> \<top>, \<lbrace>\<top>\<rbrace> = \<top>"
    and "\<lbrace>P\<rbrace>, A \<tturnstile> \<top>, \<lbrace>\<langle>\<top>\<rangle>\<rbrace> = \<top>"
    and "\<lbrace>P\<rbrace>, A \<tturnstile> \<top>, \<lbrace>\<lambda>_ _. True\<rbrace> = \<top>"
by (simp_all add: refinement_def)

lemma mcont2mcont[cont_intro]:
  assumes "mcont luba orda Sup (\<le>) G"
  shows "mcont luba orda Sup (\<le>) (\<lambda>x. \<lbrace>P\<rbrace>, A \<tturnstile> G x, \<lbrace>Q\<rbrace>)"
by (simp add: assms refinement_def)

lemma mono:
  assumes "P' \<le> P"
  assumes "A' \<le> A"
  assumes "G \<le> G'"
  assumes "Q \<le> Q'"
  shows "\<lbrace>P\<rbrace>, A \<tturnstile> G, \<lbrace>Q\<rbrace> \<le> \<lbrace>P'\<rbrace>, A' \<tturnstile> G', \<lbrace>Q'\<rbrace>"
unfolding refinement_def
apply (strengthen ord_to_strengthen(1)[OF assms(1)])
apply (strengthen ord_to_strengthen(1)[OF assms(2)])
apply (strengthen ord_to_strengthen(1)[OF assms(3)])
apply (strengthen ord_to_strengthen(1)[OF assms(4)])
apply simp
done

lemma strengthen[strg]:
  assumes "st_ord (\<not> F) P P'"
  assumes "st_ord (\<not> F) A A'"
  assumes "st_ord F G G'"
  assumes "st_ord F Q Q'"
  shows "st_ord F (\<lbrace>P\<rbrace>, A \<tturnstile> G, \<lbrace>Q\<rbrace>) (\<lbrace>P'\<rbrace>, A' \<tturnstile> G', \<lbrace>Q'\<rbrace>)"
using assms by (cases F; simp add: refinement.mono)

lemma mono_stronger:
  assumes "P' \<le> P"
  assumes "spec.pre P' \<sqinter> A' \<le> A"
  assumes "spec.pre P' \<sqinter> G \<le> A' \<^bold>\<longrightarrow>\<^sub>+ G'"
  assumes "Q \<le> Q'"
  assumes "spec.idle \<le> G'"
  shows "\<lbrace>P\<rbrace>, A \<tturnstile> G, \<lbrace>Q\<rbrace> \<le> \<lbrace>P'\<rbrace>, A' \<tturnstile> G', \<lbrace>Q'\<rbrace>"
unfolding refinement_def
apply (strengthen ord_to_strengthen(2)[OF assms(1)])
apply (strengthen ord_to_strengthen(2)[OF assms(2)])
apply (strengthen ord_to_strengthen(2)[OF assms(4)])
apply (simp add: spec.next_imp.infR)
apply (metis assms(3) heyting.commute le_infI1
             spec.next_imp.closure.cl spec.pre.next_imp_eq_heyting(2)[OF assms(5)])
done

lemmas pre_ag = order.trans[OF _ refinement.mono[OF order.refl _ _ order.refl], of c] for c
lemmas pre_a = refinement.pre_ag[OF _ _ order.refl]
lemmas pre_g = refinement.pre_ag[OF _ order.refl]

lemma pre:
  assumes "c \<le> \<lbrace>P\<rbrace>, A \<tturnstile> G, \<lbrace>Q\<rbrace>"
  assumes "\<And>s. P' s \<Longrightarrow> P s"
  assumes "A' \<le> A"
  assumes "G \<le> G'"
  assumes "\<And>s v. Q s v \<Longrightarrow> Q' s v"
  shows "c \<le> \<lbrace>P'\<rbrace>, A' \<tturnstile> G', \<lbrace>Q'\<rbrace>"
using assms(2-) by (blast intro: order.trans[OF assms(1) refinement.mono])

lemmas pre_pre_post = refinement.pre[OF _ _ order.refl order.refl, of c] for c

lemma pre_imp:
  assumes "\<And>s. P s \<Longrightarrow> P' s"
  assumes "c \<le> \<lbrace>P'\<rbrace>, A \<tturnstile> G, \<lbrace>Q\<rbrace>"
  shows "c \<le> \<lbrace>P\<rbrace>, A \<tturnstile> G, \<lbrace>Q\<rbrace>"
using assms refinement.pre by blast

lemmas pre_pre = refinement.pre_imp[rotated]

lemma post_imp:
  assumes "\<And>v s. Q v s \<Longrightarrow> R v s"
  assumes "c \<le> \<lbrace>P\<rbrace>, A \<tturnstile> G, \<lbrace>Q\<rbrace>"
  shows "c \<le> \<lbrace>P\<rbrace>, A \<tturnstile> G, \<lbrace>R\<rbrace>"
using assms refinement.pre by blast

lemmas pre_post = refinement.post_imp[rotated]
lemmas strengthen_post = refinement.pre_post

lemma pre_inf_assume:
  shows "\<lbrace>P\<rbrace>, A \<tturnstile> G, \<lbrace>Q\<rbrace> = \<lbrace>P\<rbrace>, A \<sqinter> spec.pre P \<tturnstile> G, \<lbrace>Q\<rbrace>"
by (simp add: refinement_def ac_simps)

lemma pre_assume_absorb:
  assumes "A \<le> spec.pre P"
  shows "\<lbrace>P\<rbrace>, A \<tturnstile> G, \<lbrace>Q\<rbrace> = \<lbrace>\<top>\<rbrace>, A \<tturnstile> G, \<lbrace>Q\<rbrace>"
by (simp add: assms refinement_def inf_absorb2)

lemmas sup = sup_least[where x="\<lbrace>P\<rbrace>, A \<tturnstile> G, \<lbrace>Q\<rbrace>"] for A G P Q

lemma
  shows supRL: "c \<le> \<lbrace>P\<rbrace>, A \<tturnstile> G\<^sub>1, \<lbrace>Q\<rbrace> \<Longrightarrow> c \<le> \<lbrace>P\<rbrace>, A \<tturnstile> G\<^sub>1 \<squnion> G\<^sub>2, \<lbrace>Q\<rbrace>"
    and supRR: "c \<le> \<lbrace>P\<rbrace>, A \<tturnstile> G\<^sub>2, \<lbrace>Q\<rbrace> \<Longrightarrow> c \<le> \<lbrace>P\<rbrace>, A \<tturnstile> G\<^sub>1 \<squnion> G\<^sub>2, \<lbrace>Q\<rbrace>"
by (simp_all add: refinement.pre_g)

lemma infR_conv:
  shows "\<lbrace>P\<rbrace>, A \<tturnstile> G\<^sub>1 \<sqinter> G\<^sub>2, \<lbrace>Q\<^sub>1 \<sqinter> Q\<^sub>2\<rbrace> = \<lbrace>P\<rbrace>, A \<tturnstile> G\<^sub>1, \<lbrace>Q\<^sub>1\<rbrace> \<sqinter> \<lbrace>P\<rbrace>, A \<tturnstile> G\<^sub>2, \<lbrace>Q\<^sub>2\<rbrace>"
by (simp add: refinement_def ac_simps spec.next_imp.infR spec.post.inf)

lemma inf_le:
  shows "X \<sqinter> \<lbrace>P\<rbrace>, A \<tturnstile> G, \<lbrace>Q\<rbrace> \<le> \<lbrace>P\<rbrace>, X \<sqinter> A \<tturnstile> X \<sqinter> G, \<lbrace>Q\<rbrace>"
by (simp add: refinement_def le_infI1 le_infI2
              spec.next_imp.infR spec.next_imp.mono spec.next_imp.contains)

lemma heyting_le:
  shows "\<lbrace>P\<rbrace>, A \<sqinter> B \<tturnstile> B \<^bold>\<longrightarrow>\<^sub>H G, \<lbrace>Q\<rbrace> \<le> B \<^bold>\<longrightarrow>\<^sub>H \<lbrace>P\<rbrace>, A \<tturnstile> G, \<lbrace>Q\<rbrace>"
by (simp add: refinement_def ac_simps heyting.infR heyting.commute
              spec.next_imp.heytingL_distrib spec.next_imp.mono)

lemma heyting_pre:
  assumes "spec.idle \<le> G"
  shows "spec.pre P \<^bold>\<longrightarrow>\<^sub>H \<lbrace>P'\<rbrace>, A \<tturnstile> G, \<lbrace>Q\<rbrace> = \<lbrace>P \<^bold>\<and> P'\<rbrace>, A \<tturnstile> G, \<lbrace>Q\<rbrace>"
by (simp add: ac_simps refinement_def spec.pre.conj assms spec.idle.post_le
        flip: spec.pre.next_imp_eq_heyting)

lemma sort_of_refl:
  assumes "c \<le> \<lbrace>P\<rbrace>, A \<tturnstile> G, \<lbrace>Q\<rbrace>"
  shows "c \<le> \<lbrace>P\<rbrace>, A \<tturnstile> c, \<lbrace>Q\<rbrace>"
using assms by (simp add: refinement_def spec.next_imp.infR spec.next_imp.closure.expansive)

lemma gen_asm_base:
  assumes "P \<Longrightarrow> c \<le> \<lbrace>P' \<^bold>\<and> P''\<rbrace>, A \<tturnstile> G, \<lbrace>Q\<rbrace>"
  assumes "spec.idle \<le> G"
  shows "c \<le> \<lbrace>P' \<^bold>\<and> \<langle>P\<rangle> \<^bold>\<and> P''\<rbrace>, A \<tturnstile> G, \<lbrace>Q\<rbrace>"
using assms by (simp add: refinement_def spec.pre.conj spec.pre.K spec.next_imp.botL spec.idle.post_le)

lemmas gen_asm =
  refinement.gen_asm_base[where P'="\<langle>True\<rangle>" and P''="\<langle>True\<rangle>", simplified]
  refinement.gen_asm_base[where P'="\<langle>True\<rangle>", simplified]
  refinement.gen_asm_base[where P''="\<langle>True\<rangle>", simplified]
  refinement.gen_asm_base

lemma post_conj:
  assumes "c \<le> \<lbrace>P\<rbrace>, A \<tturnstile> G, \<lbrace>Q\<rbrace>"
  assumes "c \<le> \<lbrace>P\<rbrace>, A \<tturnstile> G, \<lbrace>Q'\<rbrace>"
  shows "c \<le> \<lbrace>P\<rbrace>, A \<tturnstile> G, \<lbrace>\<lambda>rv. Q rv \<^bold>\<and> Q' rv\<rbrace>"
using assms unfolding refinement_def by (simp add: spec.post.conj spec.next_imp.infR)

lemma conj_lift:
  assumes "c \<le> \<lbrace>P\<rbrace>, A \<tturnstile> G, \<lbrace>Q\<rbrace>"
  assumes "c \<le> \<lbrace>P'\<rbrace>, A \<tturnstile> G, \<lbrace>Q'\<rbrace>"
  shows "c \<le> \<lbrace>P \<^bold>\<and> P'\<rbrace>, A \<tturnstile> G, \<lbrace>\<lambda>rv. Q rv \<^bold>\<and> Q' rv\<rbrace>"
using assms by (blast intro: refinement.post_conj refinement.pre)

lemma drop_imp:
  assumes "c \<le> \<lbrace>P\<rbrace>, A \<tturnstile> G, \<lbrace>Q\<rbrace>"
  shows "c \<le> \<lbrace>P\<rbrace>, A \<tturnstile> G, \<lbrace>\<lambda>rv. Q' rv \<^bold>\<longrightarrow> Q rv\<rbrace>"
using assms refinement.strengthen_post by fastforce

lemma "prop":
  shows "c \<le> \<lbrace>\<langle>P\<rangle>\<rbrace>, A \<tturnstile> c, \<lbrace>\<lambda>v. \<langle>P\<rangle>\<rbrace>"
by (simp add: refinement.sort_of_refl[where G=\<top>] refinement.gen_asm refinement.top)

lemma name_pre_state:
  assumes "\<And>s. P s \<Longrightarrow> c \<le> \<lbrace>(=) s\<rbrace>, A \<tturnstile> G, \<lbrace>Q\<rbrace>"
  assumes "spec.idle \<le> G"
  shows "c \<le> \<lbrace>P\<rbrace>, A \<tturnstile> G, \<lbrace>Q\<rbrace>" (is "?lhs \<le> ?rhs")
proof -
  have "\<lblot>\<sigma>\<rblot> \<le> G \<and> \<lblot>\<sigma>\<rblot> \<le> spec.post Q"
    if "\<lblot>\<sigma>\<rblot> \<le> c"
   and "\<forall>\<sigma>''<\<sigma>. \<lblot>\<sigma>''\<rblot> \<le> spec.pre P \<and> \<lblot>\<sigma>''\<rblot> \<le> A"
   for \<sigma>
  proof(cases "trace.rest \<sigma> = [] \<and> trace.term \<sigma> = None")
    case True with \<open>spec.idle \<le> G\<close> show ?thesis
      by (cases \<sigma>) (simp add: spec.singleton.le_conv order.trans[OF spec.idle.minimal_le])
  next
    case False with order.trans[OF \<open>\<lblot>\<sigma>\<rblot> \<le> c\<close> assms(1)[where s="trace.init \<sigma>"]] that(2)
    show ?thesis
      by (cases \<sigma>)
         (clarsimp simp: refinement_def spec.singleton.next_imp_le_conv spec.singleton.le_conv;
          fastforce simp: trace.less dest: spec[where x="trace.T (trace.init \<sigma>) [] None"])
  qed
  then show ?thesis
    by - (rule spec.singleton_le_extI;
          auto simp: refinement_def spec.singleton.next_imp_le_conv
              intro: order.trans[OF spec.singleton.mono])
qed

setup \<open>Sign.parent_path\<close>


subsection\<open> Geenral rules for the \<^emph>\<open>('a, 's, 'v) spec\<close> lattice\label{sec:refinement-spec} \<close>

setup \<open>Sign.mandatory_path "spec"\<close>

setup \<open>Sign.mandatory_path "term"\<close>

setup \<open>Sign.mandatory_path "all"\<close>

lemma refinement:
  shows "spec.term.all (\<lbrace>P\<rbrace>, A \<tturnstile> G, \<lbrace>Q\<rbrace>) = \<lbrace>P\<rbrace>, spec.term.all A \<tturnstile> spec.term.all G, \<lbrace>\<top>\<rbrace>"
by (simp add: refinement_def spec.term.all.next_imp spec.term.all.inf spec.term.all.pre spec.term.all.post)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "none"\<close>

lemma refinement_le:
  shows "spec.term.none (\<lbrace>P\<rbrace>, A \<tturnstile> G, \<lbrace>Q\<rbrace>) \<le> \<lbrace>P\<rbrace>, spec.term.all A \<tturnstile> spec.term.all G, \<lbrace>\<bottom>\<rbrace>"
by (simp add: spec.term.galois spec.term.all.refinement order.trans[OF spec.term.all.expansive])

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "invmap"\<close>

lemma refinement:
  fixes af :: "'a \<Rightarrow> 'b"
  fixes sf :: "'s \<Rightarrow> 't"
  fixes vf :: "'v \<Rightarrow> 'w"
  fixes A :: "('b, 't, 'w) spec"
  fixes G :: "('b, 't, 'w) spec"
  fixes P :: "'t pred"
  fixes Q :: "'w \<Rightarrow> 't pred"
  shows "spec.invmap af sf vf (\<lbrace>P\<rbrace>, A \<tturnstile> G, \<lbrace>Q\<rbrace>)
      = (\<lbrace>\<lambda>s. P (sf s)\<rbrace>, spec.invmap af sf vf A \<tturnstile> spec.invmap af sf vf G, \<lbrace>\<lambda>v s. Q (vf v) (sf s)\<rbrace>)"
unfolding refinement_def
by (simp only: spec.next_imp.invmap spec.invmap.inf spec.invmap.pre spec.invmap.post)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.parent_path\<close>


subsubsection\<open> Actions\label{sec:refinement-action} \<close>

text\<open>

Actions are anchored at the start of a trace, and therefore must be an initial step of the
assume \<open>A\<close>. However by the semantics of \<^const>\<open>spec.next_imp\<close> we may only know
that that initial state of the trace is acceptable to \<open>A\<close>
when showing that \<open>F\<close>-steps are \<open>F'\<close>-steps
(the second assumption). This hypothesis is vacuous when \<open>idle \<le> A\<close>.

\<close>

setup \<open>Sign.mandatory_path "refinement.spec"\<close>

lemma action:
  fixes F :: "('v \<times> 'a \<times> 's \<times> 's) set"
  assumes "\<And>v a s s'. \<lbrakk>P s; (v, a, s, s') \<in> F; (a, s, s') \<in> spec.initial_steps A\<rbrakk> \<Longrightarrow> Q v s'"
  assumes "\<And>v a s s'. \<lbrakk>P s; (v, a, s, s') \<in> F; (a, s, s) \<in> spec.initial_steps A\<rbrakk> \<Longrightarrow> (v, a, s, s') \<in> F'"
  shows "spec.action F \<le> \<lbrace>P\<rbrace>, A \<tturnstile> spec.action F', \<lbrace>Q\<rbrace>"
proof -
  have "spec.action (F \<inter> UNIV \<times> UNIV \<times> Pre P) \<le> A \<^bold>\<longrightarrow>\<^sub>+ spec.action F' \<sqinter> spec.post Q"
  proof(induct rule: spec.action_le)
    case idle show ?case
      by (simp add: spec.next_imp.contains spec.idle.action_le spec.idle.post_le)
  next
    case (step v a s s') then show ?case
      by (fastforce simp: spec.singleton.next_imp_le_conv trace.split_all spec.initial_steps_def
                          trace.less Cons_eq_append_conv spec.singleton.post_le_conv
                          order.trans[OF spec.idle.minimal_le spec.idle.action_le]
                    elim: assms trace.less_eqE prefixE
                   intro: spec.action.stepI)
  qed
  then show ?thesis
    by (simp add: refinement_def spec.pre.next_imp_eq_heyting spec.idle.post_le spec.idle.action_le
                  heyting order.trans[OF spec.pre.inf_action_le(2)])
qed

lemma return:
  shows "spec.return v \<le> \<lbrace>Q v\<rbrace>, A \<tturnstile> spec.return v, \<lbrace>Q\<rbrace>"
by (auto simp: spec.return_def intro: refinement.spec.action)

lemma action_rel:
  fixes F :: "('v \<times> 'a \<times> 's \<times> 's) set"
  assumes "\<And>v a s s'. \<lbrakk>P s; (v, a, s, s') \<in> F; (a, s, s') \<in> spec.initial_steps A\<rbrakk> \<Longrightarrow> Q v s'"
  assumes "\<And>v a s s'. \<lbrakk>P s; (v, a, s, s') \<in> F; (a, s, s) \<in> spec.initial_steps A; s \<noteq> s'\<rbrakk> \<Longrightarrow> (a, s, s') \<in> r"
  shows "spec.action F \<le> \<lbrace>P\<rbrace>, A \<tturnstile> spec.rel r, \<lbrace>Q\<rbrace>"
by (force simp: spec.rel_def spec.rel.act_def spec.term.all.action
         intro: assms refinement.supRL refinement.spec.action
                refinement.pre_g[OF _ spec.term.all.mono[OF spec.kleene.expansive_star]])

setup \<open>Sign.parent_path\<close>


subsubsection\<open> Bind\label{sec:refinement-bind} \<close>

text\<open>

Consider showing \<open>f \<bind> g \<le> f' \<bind> g'\<close> under the assume \<open>A\<close> and pre/post conditions \<open>P\<close>/\<open>Q\<close>.

The tricky part is to residuate the assume \<open>A\<close> wrt the process \<open>f\<close> for use in the refinement proof of \<open>g\<close>.
 \<^item> we want to preserve as much of the structure of \<open>A\<close> as possible
 \<^item> intuition: we want all the ways a trace can continue in \<open>A\<close> having started with a terminating trace in \<open>f\<close>
 \<^item> intuitively a right residual for \<^const>\<open>spec.bind\<close> should do the job
  \<^item> however unlike \<^citet>\<open>"HoareHe:1987"\<close> we have no chance of a right residual for \<^const>\<open>spec.bind\<close> as we use traces (they use relations)
   \<^item> i.e., if it is not the case that \<open>f \<bind> \<bottom> \<le> A\<close> then there is no continuation \<open>h\<close> such that \<open>f \<bind> h \<le> A\<close>.
   \<^item> also such a residual \<open>h\<close> has arbitrary behavior starting from states that \<open>f\<close> cannot reach
    \<^item> i.e., for traces \<open>\<not>\<sigma> \<le> f\<close> \<open>\<lblot>\<sigma>\<rblot> \<then> h \<le> A\<close> need not hold
    \<^item> and the user-provided assertions may be too weak to correct for this
 \<^item> in practice the termination information in the assume \<open>A\<close> is not useful

We therefore define an ad hoc residual that does the trick.

See \<^citet>\<open>\<open>\S4\<close> in "Emerson:1983"\<close> for some related concerns.

\<close>

setup \<open>Sign.mandatory_path "refinement.spec.bind"\<close>

definition res :: "('a, 's, 'v) spec \<Rightarrow> ('a, 's, 'w) spec \<Rightarrow> 'v \<Rightarrow> ('a, 's, 'w) spec" where
  "res f A v = \<Squnion>{\<lblot>trace.final' s xs, ys, w\<rblot> |s xs ys w. \<lblot>s, xs, Some v\<rblot> \<le> f \<and> \<lblot>s, xs @ ys, None\<rblot> \<le> A}"

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "spec.singleton.refinement.bind"\<close>

lemma res_le_conv[spec.singleton.le_conv]:
  shows "\<lblot>\<sigma>\<rblot> \<le> refinement.spec.bind.res f A v
    \<longleftrightarrow> (\<exists>s xs. \<lblot>s, xs, Some v\<rblot> \<le> f
              \<and> trace.init \<sigma> = trace.final' s xs
              \<and> \<lblot>s, xs @ trace.rest \<sigma>, None\<rblot> \<le> A)" (is "?lhs \<longleftrightarrow> ?rhs")
proof(rule iffI)
  show "?lhs \<Longrightarrow> ?rhs"
    by (fastforce simp: refinement.spec.bind.res_def trace.split_Ex spec.singleton_le_conv
                        trace.less_eq_None trace.natural'.append trace.natural_def
                  elim: trace.less_eqE order.trans[rotated])
  show "?rhs \<Longrightarrow> ?lhs"
    by (cases \<sigma>) (clarsimp simp: refinement.spec.bind.res_def; blast)
qed

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "spec.term.none.refinement.bind"\<close>

lemma resL:
  shows "refinement.spec.bind.res (spec.term.none f) A v = \<bottom>"
by (simp add: refinement.spec.bind.res_def spec.singleton.le_conv)

lemma resR:
  shows "refinement.spec.bind.res f (spec.term.none A) v = refinement.spec.bind.res f A v"
by (simp add: refinement.spec.bind.res_def spec.singleton.le_conv)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "spec.term.all.refinement.bind"\<close>

lemma resR_mono:
  shows "refinement.spec.bind.res f (spec.term.all A) v = refinement.spec.bind.res f A v"
by (simp add: refinement.spec.bind.res_def spec.singleton.le_conv)
   (meson dual_order.trans spec.singleton.less_eq_None)

lemma res:
  shows "spec.term.all (refinement.spec.bind.res f A v) = refinement.spec.bind.res f A v"
by (rule spec.singleton.antisym) (auto simp: spec.singleton.le_conv)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "spec.term.closed.refinement.bind"\<close>

lemma res:
  shows "refinement.spec.bind.res f A v \<in> spec.term.closed _"
by (subst spec.term.all.refinement.bind.res[symmetric]) (rule spec.term.all.closed)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "refinement.spec.bind.res"\<close>

lemma bot:
  shows botL: "refinement.spec.bind.res \<bottom> = \<bottom>"
    and botR: "refinement.spec.bind.res f \<bottom> = \<bottom>"
by (simp_all add: refinement.spec.bind.res_def fun_eq_iff spec.singleton.not_bot)

lemma mono:
  assumes "f \<le> f'"
  assumes "A \<le> A'"
  shows "refinement.spec.bind.res f A v \<le> refinement.spec.bind.res f' A' v"
using assms unfolding refinement.spec.bind.res_def by (fastforce intro!: Sup_subset_mono)

lemma strengthen[strg]:
  assumes "st_ord F f f'"
  assumes "st_ord F A A'"
  shows "st_ord F (refinement.spec.bind.res f A v) (refinement.spec.bind.res f' A' v)"
using assms by (cases F; simp add: refinement.spec.bind.res.mono)

lemma mono2mono[cont_intro, partial_function_mono]:
  assumes "monotone orda (\<le>) f"
  assumes "monotone orda (\<le>) A"
  shows "monotone orda (\<le>) (\<lambda>x. refinement.spec.bind.res (f x) (A x) v)"
using assms by (simp add: monotone_def refinement.spec.bind.res.mono)

lemma SupL:
  shows "refinement.spec.bind.res (\<Squnion>X) A v = (\<Squnion>x\<in>X. refinement.spec.bind.res x A v)"
by (rule antisym; simp add: refinement.spec.bind.res_def; blast)

lemma SupR:
  shows "refinement.spec.bind.res f (\<Squnion>X) v = (\<Squnion>x\<in>X. refinement.spec.bind.res f x v)"
by (rule antisym; simp add: refinement.spec.bind.res_def; blast)

lemma InfL_le:
  shows "refinement.spec.bind.res (\<Sqinter>X) A v \<le> (\<Sqinter>x\<in>X. refinement.spec.bind.res x A v)"
by (simp add: refinement.spec.bind.res_def le_Inf_iff) fast

lemma InfR_le:
  shows "refinement.spec.bind.res f (\<Sqinter>X) v \<le> (\<Sqinter>x\<in>X. refinement.spec.bind.res f x v)"
by (simp add: refinement.spec.bind.res_def le_Inf_iff) fast

lemma mcont2mcont[cont_intro]:
  assumes "mcont luba orda Sup (\<le>) f"
  assumes "mcont luba orda Sup (\<le>) A"
  shows "mcont luba orda Sup (\<le>) (\<lambda>x. refinement.spec.bind.res (f x) (A x) v)"
proof(rule ccpo.mcont2mcont'[OF complete_lattice_ccpo _ _ assms(1)])
  show "mcont Sup (\<le>) Sup (\<le>) (\<lambda>f. refinement.spec.bind.res f (A x) v)" for x
    by (intro mcontI contI monotoneI)
       (simp_all add: refinement.spec.bind.res.mono refinement.spec.bind.res.SupL)
  show "mcont luba orda Sup (\<le>) (\<lambda>x. refinement.spec.bind.res f (A x) v)" for f
    by (intro mcontI monotoneI contI)
       (simp_all add: mcont_monoD[OF assms(2)] refinement.spec.bind.res.mono contD[OF mcont_cont[OF assms(2)]]
                      refinement.spec.bind.res.SupR image_image)
qed

lemma returnL:
  assumes "spec.idle \<le> A"
  shows "refinement.spec.bind.res (spec.return v) A v = spec.term.all A" (is "?lhs = ?rhs")
proof(rule antisym[OF _ spec.singleton_le_extI])
  show "?lhs \<le> ?rhs"
    by (auto simp: refinement.spec.bind.res_def trace.split_all spec.singleton.le_conv)
  show "\<lblot>\<sigma>\<rblot> \<le> ?lhs" if "\<lblot>\<sigma>\<rblot> \<le> ?rhs" for \<sigma>
    using that
    by (auto simp: spec.singleton.le_conv
           intro!: exI[where x="trace.init \<sigma>"] exI[where x="[]"]
             elim: order.trans[rotated])
qed

lemma rel_le:
  assumes "r \<subseteq> r'"
  shows "refinement.spec.bind.res f (spec.rel r) v \<le> spec.rel r'"
using assms by (force intro: spec.singleton_le_extI simp: spec.singleton.le_conv trace.steps'.append)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "spec.steps.refinement.spec.bind"\<close>

lemma res_le: \<comment>\<open> we can always discard the extra structure \<close>
  shows "spec.steps (refinement.spec.bind.res f A v) \<subseteq> spec.steps A"
by (meson order_trans refinement.spec.bind.res.mono refinement.spec.bind.res.rel_le
          spec.rel.galois spec.rel.upper_lower_expansive)

setup \<open>Sign.parent_path\<close>


text\<open>

A refinement rule for \<^const>\<open>spec.bind\<close>.
The function \<open>vf\<close> abstracts interstitial monadic return values.

\<close>

setup \<open>Sign.mandatory_path "refinement.spec"\<close>

lemma bind_abstract:
  fixes f :: "('a, 's, 'v) spec"
  fixes f' :: "('a, 's, 'v') spec"
  fixes g :: "'v \<Rightarrow> ('a, 's, 'w) spec"
  fixes g' :: "'v' \<Rightarrow> ('a, 's, 'w) spec"
  fixes vf :: "'v \<Rightarrow> 'v'"
  assumes g: "\<And>v. g v \<le> \<lbrace>Q' (vf v)\<rbrace>, refinement.spec.bind.res (spec.pre P \<sqinter> spec.term.all A \<sqinter> f') A (vf v) \<tturnstile> g' (vf v), \<lbrace>Q\<rbrace>"
  assumes f: "f \<le> \<lbrace>P\<rbrace>, spec.term.all A \<tturnstile> spec.vinvmap vf f', \<lbrace>\<lambda>v. Q' (vf v)\<rbrace>"
  shows "f \<bind> g \<le> \<lbrace>P\<rbrace>, A \<tturnstile> f' \<bind> g', \<lbrace>Q\<rbrace>"
proof (rule order.trans[OF spec.bind.mono[OF f g]],
       unfold refinement_def spec.bind.inf_post,
       induct rule: spec.bind_le)
  case incomplete show ?case
    apply (simp add: spec.term.galois spec.term.all.next_imp spec.term.all.bind spec.term.all.inf
                     spec.term.all.post spec.term.all.pre)
    apply (simp add: spec.next_imp.mono[OF order.refl] le_supI1 le_infI1 spec.term.none.invmap
                     spec.invmap.id
               flip: spec.term.galois)
    done
next
  case (continue \<sigma>\<^sub>f \<sigma>\<^sub>g v)
  have "\<lblot>s, xs, w\<rblot> \<le> f' \<bind> (\<lambda>v. g' v \<sqinter> spec.post Q)"
    if le: "trace.T s xs w \<le> trace.T (trace.init \<sigma>\<^sub>f) (trace.rest \<sigma>\<^sub>f @ trace.rest \<sigma>\<^sub>g) (trace.term \<sigma>\<^sub>g)"
   and pre: "\<forall>\<sigma>''<trace.T s xs w. \<lblot>\<sigma>''\<rblot> \<le> spec.pre P \<sqinter> A"
   for s xs w
    using le
  proof(induct rule: trace.less_eq_extE)
    case prefix
    from prefix(3) show ?case
    proof(induct rule: prefix_append_not_NilE[case_names incomplete1 continue1])
      case incomplete1 with pre continue(1) prefix(1,2) show ?case
        apply (clarsimp simp: spec.singleton.next_imp_le_conv)
        apply (drule spec[where x="trace.T s xs None"],
               drule mp[where P="trace.T s xs None \<le> \<sigma>\<^sub>f"])
         apply (force simp: spec.singleton.le_conv spec.map.singleton
                            le_inf_iff trace.less trace.split_All trace.less_eq_None
                 simp flip: spec.map_invmap.galois
                    intro!: spec.bind.incompleteI)+
        done
    next
      case (continue1 us)
      from continue(1,3) prefix(2) continue1(1,2)
           spec[OF pre, where x="trace.T (trace.init \<sigma>\<^sub>f) (trace.rest \<sigma>\<^sub>f) None"]
      have "\<lblot>trace.init \<sigma>\<^sub>f, trace.rest \<sigma>\<^sub>f, Some (vf v)\<rblot> \<le> spec.pre P \<sqinter> spec.term.all A \<sqinter> f' \<sqinter> spec.post Q'"
        apply (cases \<sigma>\<^sub>f)
        apply (clarsimp simp: spec.singleton.le_conv spec.singleton.next_imp_le_conv
                              trace.less le_inf_iff exI[where x=None]
                       split: option.split_asm
                       dest!: spec[where x=\<sigma>\<^sub>f])
        apply (metis append_is_Nil_conv le_inf_iff pre trace.less_same_append_conv)
        done
      with pre continue(1,2,5) prefix(1,2) continue1
           spec[OF continue(4)[unfolded spec.singleton.next_imp_le_conv],
                where x="trace.T (trace.init \<sigma>\<^sub>g) us None"]
      show ?case
        apply clarsimp
        apply (rule spec.bind.continueI[where v="vf v"], assumption)
        apply (clarsimp simp: spec.singleton.le_conv trace.split_All trace.less_eq_None trace.less)
        apply (metis append.assoc)
        done
    qed
  next
    case (maximal w')
    from maximal(1-3) continue(1,3)
         spec[OF pre, where x="trace.T (trace.init \<sigma>\<^sub>f) (trace.rest \<sigma>\<^sub>f) None"]
    have "\<lblot>trace.init \<sigma>\<^sub>f, trace.rest \<sigma>\<^sub>f, Some (vf v)\<rblot> \<le> spec.pre P \<sqinter> spec.term.all A \<sqinter> f' \<sqinter> spec.post Q'"
      apply (cases \<sigma>\<^sub>f)
      apply (clarsimp simp: spec.singleton.le_conv spec.singleton.next_imp_le_conv le_inf_iff
                     split: option.split_asm)
      apply (force simp: trace.less spec.singleton.mono trace.less_eq_same_append_conv
                   elim: notE order.trans[rotated]
                  dest!: spec[where x=\<sigma>\<^sub>f] spec[where x=None])
      done
  with maximal(2-4) pre continue(2)
       spec[OF continue(4)[unfolded spec.singleton.next_imp_le_conv], where x="\<sigma>\<^sub>g"]
  show ?case
    by (cases \<sigma>\<^sub>g)
       (auto 0 2 intro!: spec.bind.continueI[where v="vf v"] exI[where x=s]
                  simp: spec.singleton.le_conv trace.split_All trace.less)
  qed
  then show ?case
    by (clarsimp simp: spec.singleton.next_imp_le_conv trace.split_all)
qed

lemmas bind = refinement.spec.bind_abstract[where vf=id, simplified spec.invmap.id, simplified]


subsubsection\<open> Interference\label{sec:refinement-interference} \<close>

lemma rel_mono:
  assumes "r \<subseteq> r'"
  assumes "stable (snd ` (spec.steps A \<inter> r)) P"
  shows "spec.rel r \<le> \<lbrace>P\<rbrace>, A \<tturnstile> spec.rel r', \<lbrace>\<lambda>_::unit. P\<rbrace>"
apply (subst (1) spec.rel.monomorphic_conv)
using assms(2)
proof(induct arbitrary: A rule: spec.kleene.star.fixp_induct[case_names adm bot step])
  case (step R A)
  have *: "spec.rel.act r \<le> \<lbrace>P\<rbrace>, spec.term.all A \<tturnstile> spec.rel r', \<lbrace>\<langle>P\<rangle>\<rbrace>"
    unfolding spec.rel.act_def
  proof(rule refinement.spec.action_rel)
    show "P s'"
      if "P s"
     and "(v, a, s, s') \<in> {()} \<times> (r \<union> UNIV \<times> Id)"
     and "(a, s, s') \<in> spec.initial_steps (spec.term.all A)"
     for v a s s'
      using that monotoneD[OF stable.antimono_rel, unfolded le_bool_def, rule_format, OF _ step.prems,
                           where x="{(s, s')}"]
      by (cases "s = s'";
          force simp: spec.initial_steps.term.all stable.singleton_conv
                dest: subsetD[OF spec.initial_steps.steps_le])
    show "(a, s, s') \<in> r'" if "(v, a, s, s') \<in> {()} \<times> (r \<union> UNIV \<times> Id)" and "s \<noteq> s'" for v a s s'
      using that assms(1) by fast
  qed
  show ?case
    apply (rule refinement.sup[OF _ refinement.pre_g[OF refinement.spec.return spec.return.rel_le]])
    apply (subst spec.rel.unwind_bind)
    apply (rule refinement.spec.bind[OF step.hyps *])
    apply (force intro: monotoneD[OF stable.antimono_rel, unfolded le_bool_def, rule_format, OF _ step.prems]
                  dest: subsetD[OF spec.steps.refinement.spec.bind.res_le])
    done
qed simp_all

setup \<open>Sign.parent_path\<close>


subsubsection\<open> Parallel\label{sec:refinement-parallel} \<close>

text\<open>

Our refinement rule for \<^const>\<open>spec.Parallel\<close> does not constrain the constituent processes in
any way, unlike Abadi and Plotkin's proposed rule (see \S\ref{sec:abadi_plotkin}).

\<close>

setup \<open>Sign.mandatory_path "refinement.spec"\<close>

definition \<comment>\<open> roughly the \<^const>\<open>spec.Parallel\<close> construction with roles reversed \<close>
  env_hyp :: "('a \<Rightarrow> 's pred) \<Rightarrow> (sequential, 's, unit) spec \<Rightarrow> 'a set \<Rightarrow>  ('a \<Rightarrow> (sequential, 's, unit) spec) \<Rightarrow> 'a \<Rightarrow> (sequential, 's, unit) spec"
where
  "env_hyp P A as Ps a =
    spec.pre (\<Sqinter> (P ` as))
      \<sqinter> spec.amap (toConcurrent_fn (proc a))
          (spec.rel (({env} \<union> proc ` as) \<times> UNIV)
            \<sqinter> (\<Sqinter>i\<in>as. spec.toConcurrent i (Ps i))
            \<sqinter> spec.ainvmap toSequential_fn A)"

setup \<open>Sign.mandatory_path "env_hyp"\<close>

lemma mono:
  assumes "\<And>a. a \<in> as \<Longrightarrow> P a \<le> P' a"
  assumes "A \<le> A'"
  assumes "\<And>a. a \<in> as \<Longrightarrow> Ps a \<le> Ps' a"
  shows "refinement.spec.env_hyp P A as Ps a \<le> refinement.spec.env_hyp P' A' as Ps' a"
unfolding refinement.spec.env_hyp_def
apply (strengthen ord_to_strengthen(2)[OF assms(1)], assumption)
apply (strengthen ord_to_strengthen(1)[OF assms(2)])
apply (strengthen ord_to_strengthen(1)[OF assms(3)], assumption)
apply simp
done

lemma strengthen[strg]:
  assumes "\<And>a. a \<in> as \<Longrightarrow> st_ord F (P a) (P' a)"
  assumes "st_ord F A A'"
  assumes "\<And>a. a \<in> as \<Longrightarrow> st_ord F (Ps a) (Ps' a)"
  shows "st_ord F (refinement.spec.env_hyp P A as Ps a) (refinement.spec.env_hyp P' A' as Ps' a)"
using assms by (cases F; simp add: refinement.spec.env_hyp.mono)

setup \<open>Sign.parent_path\<close>

lemma Parallel:
  fixes A :: "(sequential, 's, unit) spec"
  fixes Q :: "'a \<Rightarrow> 's \<Rightarrow> bool"
  fixes Ps :: "'a \<Rightarrow> (sequential, 's, unit) spec"
  fixes Ps' :: "'a \<Rightarrow> (sequential, 's, unit) spec"
  assumes "\<And>a. a \<in> as \<Longrightarrow> Ps a \<le> \<lbrace>P a\<rbrace>, refinement.spec.env_hyp P A as Ps' a \<tturnstile> Ps' a, \<lbrace>\<lambda>v. Q a\<rbrace>"
  shows "spec.Parallel as Ps \<le> \<lbrace>\<Sqinter>a\<in>as. P a\<rbrace>, A \<tturnstile> spec.Parallel as Ps', \<lbrace>\<lambda>v. \<Sqinter>a\<in>as. Q a\<rbrace>"
proof(cases "as = {}")
  case True then show ?thesis
    by (simp add: spec.Parallel.no_agents refinement.sort_of_refl[where G=\<top>] refinement.top)
next
  case False then show ?thesis
    unfolding refinement_def
    apply (subst (1) spec.Parallel_def)
    apply (simp only: spec.map_invmap.galois spec.invmap.inf
                      spec.next_imp.invmap spec.invmap.post spec.invmap.pre)
    apply (subst (1) spec.Parallel_def)
    apply (strengthen ord_to_strengthen(2)[OF spec.map_invmap.upper_lower_expansive])
    apply (subst inf.assoc)
    apply (subst spec.next_imp.infR)
    apply (simp only: spec.next_imp.contains inf.bounded_iff inf_le1)
    apply (strengthen ord_to_strengthen[OF assms], assumption)
    apply (simp only: spec.invmap.refinement id_apply simp_thms)
    apply (rule order.trans[rotated, OF spec.Abadi_Merz_Theorem4[where
               I=as
           and As="\<lambda>a. spec.pre (P a) \<sqinter> spec.toConcurrent a (refinement.spec.env_hyp P A as Ps' a)"
           and Cs="\<lambda>a. spec.toConcurrent a (Ps' a) \<sqinter> spec.post \<langle>Q a\<rangle>"]])
    apply (simp only: inf.bounded_iff)
    apply (intro conjI)
      \<comment>\<open> the meat of \<^const>\<open>refinement.spec.env_hyp\<close> \<close>
      apply (simp only: heyting)
      apply (rule INFI)
      apply (simp only: inf.bounded_iff
                  flip: INF_inf_distrib)
      apply (intro conjI)
       apply (force simp: ac_simps spec.pre.INF
                   intro: le_infI1 le_infI2)
      apply (simp add: refinement.spec.env_hyp_def ac_simps
                 flip: spec.map_invmap.galois)
      apply (rule conjI)
       apply (simp add: spec.map_invmap.galois spec.invmap.pre le_infI2
                   del: Inf_apply INF_apply; fail)
      apply (simp add: spec.map.mono le_infI2; fail)
     apply (simp add: spec.next_imp.contains heyting spec.post.INF flip: INF_inf_distrib; fail)
    apply (force simp: refinement_def)
    done
qed

setup \<open>Sign.parent_path\<close>


subsection\<open> A relational assume/guarantee program logic for the \<^emph>\<open>(sequential, 's, 'v) spec\<close> lattice\label{sec:refinement-ag} \<close>

text\<open>

Here we develop an assume/guarantee story based on abstracting processes
(represented as safety properties) to binary relations.

Observations:
 \<^item> this can be seen as a reconstruction of the algebraic account given by \<^citet>\<open>"vanStaden:2015"\<close> in our setting
 \<^item> we show Heyting implication suffices for relations (see \<open>ag.refinement\<close>)
   \<^item> the processes' agent type is required to be \<^typ>\<open>sequential\<close>
 \<^item> we use predicates and not relations for pre/post assertions
   \<^item> we can use the metalanguage to do some relational reasoning; see, for example, \<open>ag.name_pre_state\<close>
 \<^item> \<^const>\<open>Id\<close> is the smallest significant assume and guarantee relation here; processes can always stutter any state

\<close>

setup \<open>Sign.mandatory_path "ag"\<close>

abbreviation (input) assm :: "'s rel \<Rightarrow> (sequential, 's, 'v) spec" where
  "assm A \<equiv> spec.rel ({env} \<times> A \<union> {self} \<times> UNIV)"

abbreviation (input) guar :: "'s rel \<Rightarrow> (sequential, 's, 'v) spec" where
  "guar G \<equiv> spec.rel ({env} \<times> UNIV \<union> {self} \<times> G)"

setup \<open>Sign.parent_path\<close>

definition ag :: "'s pred \<Rightarrow> 's rel \<Rightarrow> 's rel \<Rightarrow> ('v \<Rightarrow> 's pred) \<Rightarrow> (sequential, 's, 'v) spec" ("\<lbrace>_\<rbrace>, _/ \<turnstile> _, \<lbrace>_\<rbrace>" [0,0,0,0] 100) where
  "\<lbrace>P\<rbrace>, A \<turnstile> G, \<lbrace>Q\<rbrace> = spec.pre P \<sqinter> ag.assm A \<^bold>\<longrightarrow>\<^sub>H ag.guar G \<sqinter> spec.post Q"

setup \<open>Sign.mandatory_path "spec.invmap"\<close>

lemma ag: \<comment>\<open> Note \<open>af = id\<close> \<close>
  fixes sf :: "'s \<Rightarrow> 't"
  fixes vf :: "'v \<Rightarrow> 'w"
  fixes A :: "'t rel"
  fixes G :: "'t rel"
  fixes P :: "'t pred"
  fixes Q :: "'w \<Rightarrow> 't pred"
  shows "spec.invmap id sf vf (\<lbrace>P\<rbrace>, A \<turnstile> G, \<lbrace>Q\<rbrace>) = \<lbrace>\<lambda>s. P (sf s)\<rbrace>, inv_image (A\<^sup>=) sf \<turnstile> inv_image (G\<^sup>=) sf, \<lbrace>\<lambda>v s. Q (vf v) (sf s)\<rbrace>"
proof -
  have "{self} \<times> UNIV \<union> ({env} \<times> inv_image A sf \<union> UNIV \<times> inv_image Id sf) = {self} \<times> UNIV \<union> {env} \<times> inv_image (A\<^sup>=) sf"
   and "{env} \<times> UNIV \<union> ({self} \<times> inv_image G sf \<union> UNIV \<times> inv_image Id sf) = {env} \<times> UNIV \<union> {self} \<times> inv_image (G\<^sup>=) sf"
    by auto
  then show ?thesis
    by (simp add: ag_def spec.invmap.heyting spec.invmap.inf spec.invmap.rel spec.invmap.pre spec.invmap.post
                  ac_simps map_prod_vimage_Times Sigma_Un_distrib2
            flip:  inv_image_alt_def)
qed

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "ag"\<close>

lemma refinement:
  shows "\<lbrace>P\<rbrace>, A \<turnstile> G, \<lbrace>Q\<rbrace> = \<lbrace>P\<rbrace>, ag.assm A \<tturnstile> ag.guar G, \<lbrace>Q\<rbrace>"
proof -
  have constrains_heyting_ag: "ag.assm A \<^bold>\<longrightarrow>\<^sub>+ ag.guar G = ag.assm A \<^bold>\<longrightarrow>\<^sub>H ag.guar G"
    apply (rule antisym[OF spec.next_imp.heyting_le])
    apply (simp add: spec.next_imp.heyting heyting)
    apply (subst inf.commute)
    apply (rule spec.composition_principle_half[where a\<^sub>1="{self}" and a\<^sub>2="{env}"];
           force simp: spec.idle_le spec.term.closed.rel)
    done
  have constrains_heyting_post: "P \<^bold>\<longrightarrow>\<^sub>+ spec.post Q = P \<^bold>\<longrightarrow>\<^sub>H spec.post Q"
    if "P \<in> spec.term.closed _"
   for P :: "(sequential, _, _) spec"
    apply (rule antisym[OF spec.next_imp.heyting_le])
    apply (clarsimp simp: spec.next_imp.heyting)
    apply (metis spec.term.all.closed_conv[OF that] heyting.topL order_refl spec.term.all.post
                 spec.term.all_none spec.term.heyting_noneL_allR_mono spec.term.lower_upper_lower(2))
    done
  show ?thesis
    by (simp add: ag_def refinement_def
                  spec.pre.next_imp_eq_heyting spec.idle_le
                  constrains_heyting_ag spec.next_imp.infR spec.term.closed.rel
                  constrains_heyting_post[OF spec.term.closed.rel] heyting.infR heyting.curry_conv)
qed

lemma E:
  assumes "c \<le> \<lbrace>P\<rbrace>, A \<turnstile> G, \<lbrace>Q\<rbrace>"
  obtains "c \<le> spec.pre P \<sqinter> ag.assm A \<^bold>\<longrightarrow>\<^sub>H ag.guar G"
      and "c \<le> spec.pre P \<sqinter> ag.assm A \<^bold>\<longrightarrow>\<^sub>H spec.post Q"
using assms by (simp add: ag_def heyting.infR)

lemma pre_post_cong:
  assumes "P = P'"
  assumes "Q = Q'"
  shows "\<lbrace>P\<rbrace>, A \<turnstile> G, \<lbrace>Q\<rbrace> = \<lbrace>P'\<rbrace>, A \<turnstile> G, \<lbrace>Q'\<rbrace>"
using assms by simp

lemma pre_bot:
  shows "\<lbrace>\<bottom>\<rbrace>, A \<turnstile> G, \<lbrace>Q\<rbrace> = \<top>"
    and "\<lbrace>\<langle>\<bottom>\<rangle>\<rbrace>, A \<turnstile> G, \<lbrace>Q\<rbrace> = \<top>"
    and "\<lbrace>\<langle>False\<rangle>\<rbrace>, A \<turnstile> G, \<lbrace>Q\<rbrace> = \<top>"
by (simp_all add: ag_def heyting.botL)

lemma post_top:
  shows "\<lbrace>P\<rbrace>, A \<turnstile> UNIV, \<lbrace>\<top>\<rbrace> = \<top>"
    and "\<lbrace>P\<rbrace>, A \<turnstile> UNIV, \<lbrace>\<langle>\<top>\<rangle>\<rbrace> = \<top>"
    and "\<lbrace>P\<rbrace>, A \<turnstile> UNIV, \<lbrace>\<lambda>_ _. True\<rbrace> = \<top>"
by (simp_all add: ag_def spec.rel.upper_top flip: Sigma_Un_distrib1)

lemma mono:
  assumes "P' \<le> P"
  assumes "A' \<le> A"
  assumes "G \<le> G'"
  assumes "Q \<le> Q'"
  shows "\<lbrace>P\<rbrace>, A \<turnstile> G, \<lbrace>Q\<rbrace> \<le> \<lbrace>P'\<rbrace>, A' \<turnstile> G', \<lbrace>Q'\<rbrace>"
unfolding ag_def
apply (strengthen ord_to_strengthen(1)[OF assms(1)])
apply (strengthen ord_to_strengthen(1)[OF assms(2)])
apply (strengthen ord_to_strengthen(1)[OF assms(3)])
apply (strengthen ord_to_strengthen(1)[OF assms(4)])
apply simp
done

lemma strengthen[strg]:
  assumes "st_ord (\<not> F) P P'"
  assumes "st_ord (\<not> F) A A'"
  assumes "st_ord F G G'"
  assumes "st_ord F Q Q'"
  shows "st_ord F (\<lbrace>P\<rbrace>, A \<turnstile> G, \<lbrace>Q\<rbrace>) (\<lbrace>P'\<rbrace>, A' \<turnstile> G', \<lbrace>Q'\<rbrace>)"
using assms by (cases F; simp add: ag.mono)

lemma strengthen_pre:
  assumes "st_ord (\<not> F) P P'"
  shows "st_ord F (\<lbrace>P\<rbrace>, A \<turnstile> G, \<lbrace>Q\<rbrace>) (\<lbrace>P'\<rbrace>, A \<turnstile> G, \<lbrace>Q\<rbrace>)"
using assms by (cases F; simp add: ag.mono)

lemmas pre_ag = order.trans[OF _ ag.mono[OF order.refl _ _ order.refl], of c] for c
lemmas pre_a = ag.pre_ag[OF _ _ order.refl]
lemmas pre_g = ag.pre_ag[OF _ order.refl]

lemma pre:
  assumes "c \<le> \<lbrace>P\<rbrace>, A \<turnstile> G, \<lbrace>Q\<rbrace>"
  assumes "\<And>s. P' s \<Longrightarrow> P s"
  assumes "A' \<subseteq> A"
  assumes "G \<subseteq> G'"
  assumes "\<And>v s. Q v s \<Longrightarrow> Q' v s"
  shows "c \<le> \<lbrace>P'\<rbrace>, A' \<turnstile> G', \<lbrace>Q'\<rbrace>"
using assms(2-) by (blast intro: order.trans[OF assms(1) ag.mono])

lemmas pre_pre_post = ag.pre[OF _ _ order.refl order.refl, of c] for c

lemma pre_imp:
  assumes "\<And>s. P s \<Longrightarrow> P' s"
  assumes "c \<le> \<lbrace>P'\<rbrace>, A \<turnstile> G, \<lbrace>Q\<rbrace>"
  shows "c \<le> \<lbrace>P\<rbrace>, A \<turnstile> G, \<lbrace>Q\<rbrace>"
using assms ag.pre by blast

lemmas pre_pre = ag.pre_imp[rotated]

lemma post_imp:
  assumes "\<And>v s . Q v s \<Longrightarrow> Q' v s"
  assumes "c \<le> \<lbrace>P\<rbrace>, A \<turnstile> G, \<lbrace>Q\<rbrace>"
  shows "c \<le> \<lbrace>P\<rbrace>, A \<turnstile> G, \<lbrace>Q'\<rbrace>"
using assms ag.pre by blast

lemmas pre_post = ag.post_imp[rotated]
lemmas strengthen_post = ag.pre_post

lemmas reflcl_ag = spec.invmap.ag[where sf=id and vf=id, simplified spec.invmap.id, simplified]

lemma
  shows reflcl_a: "\<lbrace>P\<rbrace>, A \<turnstile> G, \<lbrace>Q\<rbrace> = \<lbrace>P\<rbrace>, A\<^sup>= \<turnstile> G, \<lbrace>Q\<rbrace>"
    and reflcl_g: "\<lbrace>P\<rbrace>, A \<turnstile> G, \<lbrace>Q\<rbrace> = \<lbrace>P\<rbrace>, A \<turnstile> G\<^sup>=, \<lbrace>Q\<rbrace>"
by (metis ag.reflcl_ag sup.left_idem sup_commute)+

lemma gen_asm_base:
  assumes "P \<Longrightarrow> c \<le> \<lbrace>P' \<^bold>\<and> P''\<rbrace>, A \<turnstile> G, \<lbrace>Q\<rbrace>"
  shows "c \<le> \<lbrace>P' \<^bold>\<and> \<langle>P\<rangle> \<^bold>\<and> P''\<rbrace>, A \<turnstile> G, \<lbrace>Q\<rbrace>"
using assms by (simp add: ag_def spec.pre.conj spec.pre.K heyting.botL)

lemmas gen_asm =
  ag.gen_asm_base[where P'="\<langle>True\<rangle>" and P''="\<langle>True\<rangle>", simplified]
  ag.gen_asm_base[where P'="\<langle>True\<rangle>", simplified]
  ag.gen_asm_base[where P''="\<langle>True\<rangle>", simplified]
  ag.gen_asm_base

lemma post_conj:
  assumes "c \<le> \<lbrace>P\<rbrace>, A \<turnstile> G, \<lbrace>Q\<rbrace>"
  assumes "c \<le> \<lbrace>P\<rbrace>, A \<turnstile> G, \<lbrace>Q'\<rbrace>"
  shows "c \<le> \<lbrace>P\<rbrace>, A \<turnstile> G, \<lbrace>\<lambda>v. Q v \<^bold>\<and> Q' v\<rbrace>"
using assms by (simp add: ag_def spec.post.conj heyting)

lemma pre_disj:
  assumes "c \<le> \<lbrace>P\<rbrace>, A \<turnstile> G, \<lbrace>Q\<rbrace>"
  assumes "c \<le> \<lbrace>P'\<rbrace>, A \<turnstile> G, \<lbrace>Q\<rbrace>"
  shows "c \<le> \<lbrace>P \<^bold>\<or> P'\<rbrace>, A \<turnstile> G, \<lbrace>Q\<rbrace>"
using assms by (simp add: ag_def spec.pre.disj inf_sup_distrib heyting)

lemma drop_imp:
  assumes "c \<le> \<lbrace>P\<rbrace>, A \<turnstile> G, \<lbrace>Q\<rbrace>"
  shows "c \<le> \<lbrace>P\<rbrace>, A \<turnstile> G, \<lbrace>\<lambda>v. Q' v \<^bold>\<longrightarrow> Q v\<rbrace>"
using assms ag.strengthen_post by fastforce

lemma "prop":
  shows "c \<le> \<lbrace>\<langle>P\<rangle>\<rbrace>, A \<turnstile> UNIV, \<lbrace>\<lambda>v. \<langle>P\<rangle>\<rbrace>"
by (simp add: ag.gen_asm(1) ag.post_top(3))

lemma name_pre_state:
  assumes "\<And>s. P s \<Longrightarrow> c \<le> \<lbrace>(=) s\<rbrace>, A \<turnstile> G, \<lbrace>Q\<rbrace>"
  shows "c \<le> \<lbrace>P\<rbrace>, A \<turnstile> G, \<lbrace>Q\<rbrace>"
by (metis assms ag.refinement refinement.name_pre_state spec.idle.rel_le)

lemma conj_lift:
  assumes "c \<le> \<lbrace>P\<rbrace>, A \<turnstile> G, \<lbrace>Q\<rbrace>"
  assumes "c \<le> \<lbrace>P'\<rbrace>, A \<turnstile> G, \<lbrace>Q'\<rbrace>"
  shows "c \<le> \<lbrace>P \<^bold>\<and> P'\<rbrace>, A \<turnstile> G, \<lbrace>\<lambda>v. Q v \<^bold>\<and> Q' v\<rbrace>"
using assms by (blast intro: ag.post_conj ag.pre)

lemma disj_lift:
  assumes "c \<le> \<lbrace>P\<rbrace>, A \<turnstile> G, \<lbrace>Q\<rbrace>"
  assumes "c \<le> \<lbrace>P'\<rbrace>, A \<turnstile> G, \<lbrace>Q'\<rbrace>"
  shows "c \<le> \<lbrace>P \<^bold>\<or> P'\<rbrace>, A \<turnstile> G, \<lbrace>\<lambda>v. Q v \<^bold>\<or> Q' v\<rbrace>"
using assms by (simp add: ag_def spec.post.disj spec.pre.disj heyting inf_sup_distrib le_supI1 le_supI2)

lemma all_lift:
  assumes "\<And>x. c \<le> \<lbrace>P x\<rbrace>, A \<turnstile> G, \<lbrace>Q x\<rbrace>"
  shows "c \<le> \<lbrace>\<^bold>\<forall>x. P x\<rbrace>, A \<turnstile> G, \<lbrace>\<lambda>v. \<^bold>\<forall>x. Q x v\<rbrace>"
using assms
by (auto simp: ag_def spec.pre.All spec.post.All le_Inf_iff heyting
    simp flip: INF_inf_const1 INF_inf_const2)

lemma interference_le:
  shows "spec.rel ({env} \<times> UNIV) \<le> \<lbrace>P\<rbrace>, A \<turnstile> G, \<lbrace>\<top>\<rbrace>"
    and "spec.rel ({env} \<times> UNIV) \<le> \<lbrace>P\<rbrace>, A \<turnstile> G, \<lbrace>\<lambda>_. \<top>\<rbrace>"
    and "spec.rel ({env} \<times> UNIV) \<le> \<lbrace>P\<rbrace>, A \<turnstile> G, \<lbrace>\<lambda>_ _. True\<rbrace>"
by (auto simp: ag_def heyting spec.term.all.rel intro: spec.rel.mono inf.coboundedI1)

lemma assm_heyting:
  fixes Q :: "'v \<Rightarrow> 's pred"
  shows "ag.assm r \<^bold>\<longrightarrow>\<^sub>H \<lbrace>P\<rbrace>, A \<turnstile> G, \<lbrace>Q\<rbrace> = \<lbrace>P\<rbrace>, A \<inter> r \<turnstile> G, \<lbrace>Q\<rbrace>"
by (simp add: ag_def ac_simps Int_Un_distrib Times_Int_Times flip: heyting.curry_conv spec.rel.inf)

lemma augment_a: \<comment>\<open> instantiate \<open>A'\<close> \<close>
  assumes "c \<le> \<lbrace>P\<rbrace>, A \<turnstile> G, \<lbrace>Q\<rbrace>"
  shows "c \<le> \<lbrace>P\<rbrace>, A \<inter> A' \<turnstile> G, \<lbrace>Q\<rbrace>"
by (blast intro: ag.pre_a[OF assms])

lemma augment_post: \<comment>\<open> instantiate \<open>Q\<close> \<close>
  assumes "c \<le> \<lbrace>P\<rbrace>, A \<turnstile> G, \<lbrace>\<lambda>v. Q' v \<^bold>\<and> Q v\<rbrace>"
  shows "c \<le> \<lbrace>P\<rbrace>, A \<turnstile> G, \<lbrace>Q'\<rbrace>"
by (blast intro: ag.pre_post[OF assms])

lemma augment_post_imp: \<comment>\<open> instantiate \<open>Q\<close> \<close>
  assumes "c \<le> \<lbrace>P\<rbrace>, A \<turnstile> G, \<lbrace>\<lambda>v. (Q v \<^bold>\<longrightarrow> Q' v) \<^bold>\<and> Q v\<rbrace>"
  shows "c \<le> \<lbrace>P\<rbrace>, A \<turnstile> G, \<lbrace>Q'\<rbrace>"
by (blast intro: ag.pre_post[OF assms])

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "spec.term.none"\<close>

lemma ag_le:
  shows "spec.term.none (\<lbrace>P\<rbrace>, A \<turnstile> G, \<lbrace>Q\<rbrace>) \<le> \<lbrace>P\<rbrace>, A \<turnstile> G, \<lbrace>\<bottom>\<rbrace>"
by (simp add: ag.refinement spec.term.all.rel order.trans[OF spec.term.none.refinement_le])

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "ag.spec.term"\<close>

lemmas none_inteference =
  order.trans[OF spec.term.none.mono,
              OF ag.interference_le(1) ag.pre_post[where Q'=Q for Q, OF spec.term.none.ag_le, simplified]]

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "ag.spec"\<close>

lemma bind:
  assumes g: "\<And>v. g v \<le> \<lbrace>Q' v\<rbrace>, A \<turnstile> G, \<lbrace>Q\<rbrace>"
  assumes f: "f \<le> \<lbrace>P\<rbrace>, A \<turnstile> G, \<lbrace>Q'\<rbrace>"
  shows "f \<bind> g \<le> \<lbrace>P\<rbrace>, A \<turnstile> G, \<lbrace>Q\<rbrace>"
apply (subst ag.refinement)
apply (rule refinement.spec.bind[where f'="ag.guar G" and g'="\<langle>ag.guar G\<rangle>", simplified spec.rel.wind_bind])
 apply (rule refinement.pre_a[OF g[unfolded ag.refinement]])
 apply (simp_all add: refinement.spec.bind.res.rel_le spec.term.all.rel f[unfolded ag.refinement])
done

lemma action:
  fixes F :: "('v \<times> sequential \<times> 's \<times> 's) set"
  assumes Q: "\<And>v a s s'. \<lbrakk>P s; (v, a, s, s') \<in> F\<rbrakk> \<Longrightarrow> Q v s'"
  assumes G: "\<And>v s s'. \<lbrakk>P s; (v, self, s, s') \<in> F; s \<noteq> s'\<rbrakk> \<Longrightarrow> (s, s') \<in> G"
  shows "spec.action F \<le> \<lbrace>P\<rbrace>, A \<turnstile> G, \<lbrace>Q\<rbrace>"
proof -
  from G have *: "spec.pre P \<sqinter> spec.action F \<le> spec.rel ({env} \<times> UNIV \<union> {self} \<times> G)"
    by - (rule order.trans[OF spec.pre.inf_action_le(1) spec.action.rel_le]; auto)
  show ?thesis
    by (fastforce intro: order.trans[OF _ refinement.mono_stronger[OF order.refl _ _ order.refl]]
                         refinement.spec.action Q
                   simp: ag.refinement order.trans[OF *] spec.next_imp.closure.expansive spec.idle.rel_le)
qed

lemma return:
  shows "spec.return v \<le> \<lbrace>Q v\<rbrace>, A \<turnstile> G, \<lbrace>Q\<rbrace>"
by (auto simp: spec.return_def intro: ag.spec.action)

lemma Parallel_assm:
  shows "refinement.spec.env_hyp P (ag.assm A) as (ag.guar \<circ> G) a \<le> ag.assm (A \<union> \<Union> (G ` (as - {a})))"
by (simp add: refinement.spec.env_hyp_def spec.invmap.rel flip: spec.rel.upper_INF spec.rel.inf)
   (force intro!: le_infI2 order.trans[OF spec.map.rel_le] spec.rel.mono_reflcl)

lemma Parallel_guar:
  shows "spec.Parallel as (ag.guar \<circ> G) = ag.guar (\<Union>a\<in>as. G a)"
proof -
  have *: "{self} \<times> Id \<union> (insert env ((\<lambda>x. self) ` as) \<times> Id \<union> map_prod toSequential_fn id ` (insert env (proc ` as) \<times> UNIV \<inter> (\<Inter>x\<in>as. {proc x} \<times> G x \<union> (- {proc x}) \<times> UNIV)))
         = {env} \<times> UNIV \<union> ({self} \<times> Id \<union> {self} \<times> \<Union> (G ` as))"
    by (rule antisym, force simp: toSequential_fn_def, (safe; force simp: map_prod_conv))
  show ?thesis
    apply (simp add: spec.Parallel_def spec.invmap.rel
               flip: spec.rel.INF spec.rel.inf)
    apply (subst spec.map.rel)
     apply (clarsimp; blast)
    apply (subst (1 2) spec.rel.reflcl[where A="{self}", symmetric])
    apply (clarsimp simp: ac_simps inf_sup_distrib image_Un image_image *
                          map_prod_image_Times map_prod_vimage_Times Times_Int_Times)
    done
qed

lemma Parallel:
  fixes A :: "'s rel"
  fixes G :: "'a \<Rightarrow> 's rel"
  fixes Q :: "'a \<Rightarrow> 's \<Rightarrow> bool"
  fixes Ps :: "'a \<Rightarrow> (sequential, 's, unit) spec"
  assumes proc_ag: "\<And>a. a \<in> as \<Longrightarrow> Ps a \<le> \<lbrace>P a\<rbrace>, A \<union> (\<Union>a'\<in>as-{a}. G a') \<turnstile> G a, \<lbrace>\<lambda>v. Q a\<rbrace>"
  shows "spec.Parallel as Ps \<le> \<lbrace>\<Sqinter>a\<in>as. P a\<rbrace>, A \<turnstile> \<Union>a\<in>as. G a, \<lbrace>\<lambda>rv. \<Sqinter>a\<in>as. Q a\<rbrace>"
unfolding ag.refinement
apply (rule order.trans[OF _ refinement.mono[OF order.refl _ _ order.refl]])
  apply (rule refinement.spec.Parallel[where A="ag.assm A" and Ps'="ag.guar \<circ> G"])
  apply (rule order.trans[OF proc_ag, unfolded ag.refinement], assumption)
  apply (rule refinement.mono[OF order.refl _ _ order.refl])
   apply (force intro: ag.spec.Parallel_assm simp: ag.spec.Parallel_guar)+
done

setup \<open>Sign.parent_path\<close>


subsubsection\<open> Stability rules \<close>

setup \<open>Sign.mandatory_path "spec"\<close>

lemma stable_pre_post:
  fixes S :: "('a, 's, 'v) spec"
  assumes "stable (snd ` r) P"
  assumes "spec.steps S \<subseteq> r"
  shows "S \<le> spec.pre P \<^bold>\<longrightarrow>\<^sub>H spec.post \<langle>P\<rangle>"
proof -
  have "P (trace.final' s xs)"
    if "P s"
   and "trace.steps (trace.T s xs v) \<subseteq> r"
   for s :: 's and xs :: "('a \<times> 's) list" and v :: "'v option"
    using that
  proof(induct xs arbitrary: s)
    case (Cons x xs) with \<open>stable (snd ` r) P\<close> show ?case
      by (cases x; cases "snd x = s";
          force simp: stable_def monotone_def dest: le_boolD)
  qed simp
  from this \<open>spec.steps S \<subseteq> r\<close> show ?thesis
    by - (rule spec.singleton_le_extI;
          auto dest: order.trans[where b=S]
               simp: spec.singleton.le_conv spec.singleton.heyting_le_conv trace.split_all spec.rel.galois
              split: option.split)
qed

lemma pre_post_stable:
  fixes P :: "'s \<Rightarrow> bool"
  assumes "stable (snd ` r) P"
  shows "spec.rel r \<le> spec.pre P \<^bold>\<longrightarrow>\<^sub>H spec.post \<langle>P\<rangle>"
by (rule spec.stable_pre_post[OF assms spec.rel.lower_upper_contractive])

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "ag"\<close>

lemma stable_lift:
  assumes "stable (A \<union> G) P'" \<comment>\<open> anything stable over \<open>A \<union> G\<close> is invariant \<close>
  shows "\<lbrace>P \<^bold>\<and> P'\<rbrace>, A \<turnstile> G, \<lbrace>\<lambda>v. P' \<^bold>\<longrightarrow> Q v\<rbrace> \<le> \<lbrace>P \<^bold>\<and> P'\<rbrace>, A \<turnstile> G, \<lbrace>\<lambda>v. Q v \<^bold>\<and> P'\<rbrace>"
apply (simp add: ag_def spec.pre.conj heyting heyting.detachment le_infI2 flip: spec.heyting.post)
apply (simp add: ac_simps Sigma_Un_distrib2 Int_Un_distrib Times_Int_Times flip: spec.rel.inf)
apply (rule order.subgoal)
 apply (rule order.trans[OF _ spec.pre_post_stable[where r="{env} \<times> A \<union> {self} \<times> G", simplified image_Un, simplified, OF assms]])
 apply (simp add: le_infI2; fail)
apply (simp add: ac_simps spec.post.conj)
apply (simp add: heyting.discharge le_infI1 flip: inf.assoc)
done

lemma stable_augment_base:
  assumes "c \<le> \<lbrace>P \<^bold>\<and> P'\<rbrace>, A \<turnstile> G, \<lbrace>\<lambda>v. P' \<^bold>\<longrightarrow> Q v\<rbrace>"
  assumes "stable (A \<union> G) P'" \<comment>\<open> anything stable over \<open>A \<union> G\<close> is invariant \<close>
  shows "c \<le> \<lbrace>P \<^bold>\<and> P'\<rbrace>, A \<turnstile> G, \<lbrace>\<lambda>v. Q v \<^bold>\<and> P'\<rbrace>"
using order.trans[OF _ ag.stable_lift] assms by blast

lemma stable_augment:
  assumes "c \<le> \<lbrace>P'\<rbrace>, A \<turnstile> G, \<lbrace>Q'\<rbrace>"
  assumes "\<And>v s. \<lbrakk>P s; Q' v s\<rbrakk> \<Longrightarrow> Q v s"
  assumes "stable (A \<union> G) P"
  shows "c \<le> \<lbrace>P' \<^bold>\<and> P\<rbrace>, A \<turnstile> G, \<lbrace>Q\<rbrace>"
apply (rule ag.strengthen_post)
 apply (rule ag.stable_augment_base[where Q=Q, OF _ assms(3)])
 apply (auto intro: assms(2) ag.pre[OF assms(1)])
done

lemma stable_augment_post:
  assumes "c \<le> \<lbrace>P'\<rbrace>, A \<turnstile> G, \<lbrace>Q'\<rbrace>" \<comment>\<open> resolve before application\<close>
  assumes "\<And>v. stable (A \<union> G) (Q' v \<^bold>\<longrightarrow> Q v)"
  shows "c \<le> \<lbrace>(\<^bold>\<forall>v. Q' v \<^bold>\<longrightarrow> Q v) \<^bold>\<and> P'\<rbrace>, A \<turnstile> G, \<lbrace>Q\<rbrace>"
apply (rule ag.pre_pre_post)
 apply (rule ag.stable_augment_base[where P=P' and Q=Q' and P'="(\<^bold>\<forall>v. Q' v \<^bold>\<longrightarrow> Q v)"])
   apply (rule ag.pre_pre_post[OF assms(1)])
    using assms(2) apply (fast intro: stable.allI)+
done

lemma stable_augment_frame: \<comment>\<open> anything stable over \<open>A \<union> G\<close> is invariant\label{sec:refinement-frame} \<close>
  assumes "c \<le> \<lbrace>P\<rbrace>, A \<turnstile> G, \<lbrace>Q\<rbrace>"
  assumes "stable (A \<union> G) P'"
  shows "c \<le> \<lbrace>P \<^bold>\<and> P'\<rbrace>, A \<turnstile> G, \<lbrace>\<lambda>v. Q v \<^bold>\<and> P'\<rbrace>"
using assms by (blast intro: ag.stable_augment[OF assms(1)])

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "ag.spec"\<close>

lemma stable_interference:
  assumes "stable (A \<inter> r) P"
  shows "spec.rel ({env} \<times> r) \<le> \<lbrace>P\<rbrace>, A \<turnstile> G, \<lbrace>\<langle>P\<rangle>\<rbrace>"
using assms
by (auto simp: ag_def ac_simps heyting Int_Un_distrib Times_Int_Times
    simp flip: spec.rel.inf
        intro: le_infI2 spec.rel.mono spec.pre_post_stable[simplified heyting ac_simps])

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "spec"\<close>

setup \<open>Sign.mandatory_path "cam"\<close>

lemma closed_ag:
  shows "\<lbrace>P\<rbrace>, A \<turnstile> G, \<lbrace>Q\<rbrace> \<in> spec.cam.closed ({env} \<times> r)"
unfolding ag_def heyting.infR
by (blast intro: subsetD[OF spec.cam.closed.antimono, rotated])

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "interference"\<close>

lemma cl_ag_le:
  assumes P: "stable (A \<inter> r) P"
  assumes Q: "\<And>v. stable (A \<inter> r) (Q v)"
  shows "spec.interference.cl ({env} \<times> r) (\<lbrace>P\<rbrace>, A \<turnstile> G, \<lbrace>Q\<rbrace>) \<le> \<lbrace>P\<rbrace>, A \<turnstile> G, \<lbrace>Q\<rbrace>"
unfolding spec.interference.cl_def
by (rule ag.spec.bind ag.spec.return ag.spec.stable_interference spec.cam.least[OF _ spec.cam.closed_ag] assms order.refl)+

lemma closed_ag:
  assumes P: "stable (A \<inter> r) P"
  assumes Q: "\<And>v. stable (A \<inter> r) (Q v)"
  shows "\<lbrace>P\<rbrace>, A \<turnstile> G, \<lbrace>Q\<rbrace> \<in> spec.interference.closed ({env} \<times> r)"
by (rule spec.interference.closed_clI[OF spec.interference.cl_ag_le[OF assms]])

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.parent_path\<close>
(*<*)

end
(*>*)
