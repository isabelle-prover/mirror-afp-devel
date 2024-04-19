(*<*)
theory WickersonDoddsParkinson
imports
  "Assume_Guarantee"
begin

(*>*)
section\<open> Wickerson, Dodds and Parkinson: explicit stabilisation\label{sec:explicit_stabilisation} \<close>

text\<open>

Notes on \<^citet>\<open>"WickersonDoddsParkinson:2010"\<close> (all references here are to the technical report):
 \<^item> motivation: techniques for eliding redundant stability conditions
  \<^item> the standard rules check the interstitial assertion in \<open>c ; d\<close> twice
 \<^item> they claim in \S7 to supersede the ``mid stability'' of \<^citet>\<open>\<open>\S4.1\<close> in "Vafeiadis:2008"\<close> (wssa, sswa)
 \<^item> Appendix D:
  \<^item> not a complete set of rules
  \<^item> \textsc{AtomR-S} does not self-compose: consider \<open>c ; d\<close> -- the interstitial assertion is either a floor or ceiling
   \<^item> every step therefore requires a use of weakening/monotonicity

The basis of their approach is to make assertions a function of a
relation (a \<^emph>\<open>rely\<close>). By considering a set of
relations, a single rely-guarantee specification can satisfy several
call sites. Separately they tweak the RGSep rules of \<^citet>\<open>"Vafeiadis:2008"\<close>.

The definitions are formally motivated as follows (\S3):

\begin{quote}

Our operators can also be defined using Dijkstra's predicate
transformer semantics: \<open>\<lfloor>p\<rfloor>R\<close> is the
weakest precondition of \<open>R\<^sup>*\<close> given postcondition
\<open>p\<close>, while \<open>\<lceil>p\<rceil>R\<close> is the
strongest postcondition of \<open>R\<^sup>*\<close> given
pre-condition \<open>p\<close>.

\end{quote}

The following adapts their definitions and proofs to our setting.

\<close>

setup \<open>Sign.mandatory_path "wdp"\<close>

definition floor :: "'a rel \<Rightarrow> 'a pred \<Rightarrow> 'a pred" where \<comment>\<open> An interior operator, or a closure in the dual lattice \<close>
  "floor r P s \<longleftrightarrow> (\<forall>s'. (s, s') \<in> r\<^sup>* \<longrightarrow> P s')"

definition ceiling :: "'a rel \<Rightarrow> 'a pred \<Rightarrow> 'a pred" where \<comment>\<open> A closure operator \<close>
  "ceiling r P s \<longleftrightarrow> (\<exists>s'. (s', s) \<in> r\<^sup>* \<and> P s')"

setup \<open>Sign.mandatory_path "floor"\<close>

lemma empty_rel[simp]:
  shows "wdp.floor {} P = P"
by (simp add: wdp.floor_def fun_eq_iff)

lemma reflcl:
  shows "wdp.floor (r\<^sup>=) = wdp.floor r"
by (simp add: wdp.floor_def fun_eq_iff)

lemma const:
  shows "wdp.floor r \<langle>c\<rangle> = \<langle>c\<rangle>"
by (auto simp: wdp.floor_def fun_eq_iff)

lemma contractive:
  shows "wdp.floor r P \<le> P"
by (simp add: wdp.floor_def le_fun_def le_bool_def)

lemma idempotent:
  shows "wdp.floor r (wdp.floor r P) = wdp.floor r P"
by (auto simp: fun_eq_iff wdp.floor_def dest: rtrancl_trans)

lemma mono:
  assumes "r' \<subseteq> r"
  assumes "P \<le> P'"
  shows "wdp.floor r P \<le> wdp.floor r' P'"
using assms by (auto 6 0 simp add: wdp.floor_def le_bool_def le_fun_def dest: rtrancl_mono)

lemma strengthen[strg]:
  assumes "st_ord (\<not>F) r r'"
  assumes "st_ord F P P'"
  shows "st_ord F (wdp.floor r P) (wdp.floor r' P')"
using assms by (cases F; simp add: wdp.floor.mono)

lemma weakest:
  assumes "Q \<le> P"
  assumes "stable r Q"
  shows "Q \<le> wdp.floor r P"
using assms by (simp add: wdp.floor_def stable_def monotone_def le_fun_def le_bool_def) (metis rtrancl_induct)

lemma Chernoff:
  assumes "P \<le> Q"
  shows "(wdp.floor r P \<^bold>\<and> Q) \<le> wdp.floor r Q"
using assms by (simp add: wdp.floor_def le_fun_def le_bool_def)

lemma floor1:
  assumes "r \<subseteq> r'"
  shows "wdp.floor r' (wdp.floor r P) = wdp.floor r' P"
unfolding wdp.floor_def by (meson assms rtrancl_cl.cl_mono rtrancl_eq_or_trancl rtrancl_trans)

lemma floor2:
  assumes "r \<subseteq> r'"
  shows "wdp.floor r (wdp.floor r' P) = wdp.floor r' P"
by (metis assms antisym wdp.floor.contractive wdp.floor.idempotent wdp.floor.mono)

setup \<open>Sign.parent_path\<close>

interpretation ceiling: closure_complete_lattice_distributive_class "wdp.ceiling r" for r
by standard (auto 5 0 simp: wdp.ceiling_def le_fun_def le_bool_def dest: rtrancl_trans)

setup \<open>Sign.mandatory_path "ceiling"\<close>

lemma empty_rel[simp]:
  shows "wdp.ceiling {} P = P"
by (simp add: wdp.ceiling_def fun_eq_iff)

lemma reflcl:
  shows "wdp.ceiling (r\<^sup>=) = wdp.ceiling r"
by (simp add: wdp.ceiling_def fun_eq_iff)

lemma const:
  shows "wdp.ceiling r \<langle>c\<rangle> = \<langle>c\<rangle>"
by (auto simp: wdp.ceiling_def fun_eq_iff)

lemma mono:
  assumes "r \<subseteq> r'"
  assumes "P \<le> P'"
  shows "wdp.ceiling r P \<le> wdp.ceiling r' P'"
using assms by (auto 7 0 simp: wdp.ceiling_def le_bool_def le_fun_def dest: rtrancl_mono)

lemma strengthen[strg]:
  assumes "st_ord F r r'"
  assumes "st_ord F P P'"
  shows "st_ord F (wdp.ceiling r P) (wdp.ceiling r' P')"
using assms by (cases F; simp add: wdp.ceiling.mono)

lemma strongest:
  assumes "P \<le> Q"
  assumes "stable r Q"
  shows "wdp.ceiling r P \<le> Q"
using assms by (simp add: wdp.ceiling_def stable_def monotone_def le_fun_def le_bool_def) (metis rtrancl_induct)

lemma ceiling1:
  assumes "r \<subseteq> r'"
  shows "wdp.ceiling r' (wdp.ceiling r P) = wdp.ceiling r' P"
unfolding wdp.ceiling_def by (meson assms rtrancl_cl.cl_mono rtrancl_eq_or_trancl rtrancl_trans)

lemma ceiling2:
  assumes "r \<subseteq> r'"
  shows "wdp.ceiling r (wdp.ceiling r' P) = wdp.ceiling r' P"
by (metis assms antisym wdp.ceiling.ceiling1 wdp.ceiling.expansive wdp.ceiling.idempotent(1))

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "stable"\<close>

lemma floor:
  shows "stable r (wdp.floor r P)"
unfolding wdp.floor_def stable_def monotone_def by (simp add: converse_rtrancl_into_rtrancl le_boolI)

lemma ceiling:
  shows "stable r (wdp.ceiling r P)"
by (fastforce simp: wdp.ceiling_def stable_def monotone_def le_bool_def
              dest: rtrancl_into_rtrancl)

lemma floor_conv:
  assumes "stable r P"
  shows "P = wdp.floor r P"
using assms unfolding wdp.floor_def stable_def monotone_def le_bool_def fun_eq_iff
by (metis rtrancl_refl rtrancl_induct)

lemma ceiling_conv:
  assumes "stable r P"
  shows "P = wdp.ceiling r P"
using assms unfolding wdp.ceiling_def stable_def monotone_def le_bool_def fun_eq_iff
by (metis rtrancl_refl rtrancl_induct)

setup \<open>Sign.parent_path\<close>

lemma floor_alt_def: \<comment>\<open> \<^citet>\<open>\<open>\S3\<close> in "WickersonDoddsParkinson:2010"\<close> \<close>
  shows "wdp.floor r P = \<Squnion>{Q. Q \<le> P \<and> stable r Q}"
by (rule antisym)
   (auto simp: Sup_upper wdp.floor.contractive wdp.stable.floor
        intro: wdp.floor.weakest[unfolded le_bool_def le_fun_def, rule_format])

lemma ceiling_alt_def: \<comment>\<open> \<^citet>\<open>\<open>\S3\<close> in "WickersonDoddsParkinson:2010"\<close> \<close>
  shows "wdp.ceiling r P = \<Sqinter>{Q. P \<le> Q \<and> stable r Q}"
by (rule antisym)
   (auto simp: Inf_lower wdp.ceiling.expansive wdp.stable.ceiling
         dest: wdp.ceiling.strongest[unfolded le_bool_def le_fun_def, rule_format, rotated])

lemma duality_floor_ceiling:
  shows "wdp.ceiling r (\<^bold>\<not>P) = (\<^bold>\<not>wdp.floor (r\<inverse>) P)"
by (simp add: wdp.ceiling_def wdp.floor_def fun_eq_iff rtrancl_converse)

lemma ceiling_floor:
  assumes "r \<subseteq> r'"
  shows "wdp.ceiling r (wdp.floor r' P) = wdp.floor r' P"
by (metis assms wdp.ceiling.ceiling2 wdp.stable.ceiling_conv wdp.stable.floor)

lemma floor_ceiling:
  assumes "r \<subseteq> r'"
  shows "wdp.floor r (wdp.ceiling r' P) = wdp.ceiling r' P"
by (metis assms wdp.floor.floor2 wdp.stable.ceiling wdp.stable.floor_conv)

lemma floor_ceilr:
  shows "wdp.floor (ceilr P) P = P"
by (metis ceilr.stable wdp.stable.floor_conv)

lemma ceiling_ceilr:
  shows "wdp.ceiling (ceilr P) P = P"
by (metis ceilr.stable wdp.stable.ceiling_conv)

setup \<open>Sign.parent_path\<close>


subsection\<open> Assume/Guarantee rules\label{sec:explicit_stabilisation-ag} \<close>

paragraph\<open> \S3.2 traditional assume/guarantee rules \<close>

setup \<open>Sign.mandatory_path "wdp"\<close>

lemma action: \<comment>\<open> arbitrary \<open>A\<close> \<close>
  fixes F :: "('v \<times> 's \<times> 's) set"
  assumes Q: "\<And>v s s'. \<lbrakk>P s; (v, s, s') \<in> F\<rbrakk> \<Longrightarrow> Q v s'"
  assumes G: "\<And>v s s'. \<lbrakk>P s; s \<noteq> s'; (v, s, s') \<in> F\<rbrakk> \<Longrightarrow> (s, s') \<in> G"
  shows "prog.p2s (prog.action F) \<le> \<lbrace>wdp.floor A P\<rbrace>, A \<turnstile> G, \<lbrace>\<lambda>v. wdp.ceiling A (Q v)\<rbrace>"
by (rule ag.prog.action)
   (auto simp: wdp.stable.floor wdp.stable.ceiling
        intro: G
         dest: Q[rotated]
         elim: wdp.floor.contractive[unfolded le_fun_def le_bool_def, rule_format]
               wdp.ceiling.expansive[unfolded le_fun_def le_bool_def, rule_format])

lemmas mono = ag.mono
lemmas bind = ag.prog.bind

text\<open> etc. -- the other rules are stock \<close>

setup \<open>Sign.parent_path\<close>


paragraph\<open> \S4, Appendix C parametric specifications \<close>

definition pag :: "('s rel \<Rightarrow> 's pred) \<Rightarrow> 's rel set \<Rightarrow> 's rel \<Rightarrow> ('s rel \<Rightarrow> 'v \<Rightarrow> 's pred) \<Rightarrow> (sequential, 's, 'v) spec" ("\<lbrace>_\<rbrace>, _/ \<turnstile>\<^sub>P _, \<lbrace>_\<rbrace>" [0,0,0,0] 100) where
  "\<lbrace>P\<rbrace>, As \<turnstile>\<^sub>P G, \<lbrace>Q\<rbrace> = (\<Sqinter>A\<in>As. \<lbrace>P A\<rbrace>, A \<turnstile> G, \<lbrace>Q A\<rbrace>)"

setup \<open>Sign.mandatory_path "pag"\<close>

lemma empty:
  shows "\<lbrace>P\<rbrace>, {} \<turnstile>\<^sub>P G, \<lbrace>Q\<rbrace> = \<top>"
by (simp add: pag_def)

lemma singleton:
  shows "\<lbrace>P\<rbrace>, {A} \<turnstile>\<^sub>P G, \<lbrace>Q\<rbrace> = \<lbrace>P A\<rbrace>, A \<turnstile> G, \<lbrace>Q A\<rbrace>"
by (simp add: pag_def)

lemma mono: \<comment>\<open> strengthening of the \<^verbatim>\<open>WEAKEN\<close> rule in Figure~4, needed for the example  \<close>
  assumes "\<And>A. A \<in> As' \<Longrightarrow> P' A \<le> P A"
  assumes "As' \<le> As"
  assumes "G \<le> G'"
  assumes "\<And>A. A \<in> As' \<Longrightarrow> Q A \<le> Q' A"
  shows "\<lbrace>P\<rbrace>, As \<turnstile>\<^sub>P G, \<lbrace>Q\<rbrace> \<le> \<lbrace>P'\<rbrace>, As' \<turnstile>\<^sub>P G', \<lbrace>Q'\<rbrace>"
by (simp add: assms pag_def INF_superset_mono[OF \<open>As' \<le> As\<close> ag.mono] le_funD)

lemma action: \<comment>\<open> allow assertions to depend on assume \<open>A\<close>, needed for the example \<close>
  fixes F :: "('v \<times> 's \<times> 's) set"
  assumes Q: "\<And>A v s s'. \<lbrakk>A \<in> As; P A s; (v, s, s') \<in> F\<rbrakk> \<Longrightarrow> Q A v s'"
  assumes G: "\<And>A v s s'. \<lbrakk>A \<in> As; P A s; s \<noteq> s'; (v, s, s') \<in> F\<rbrakk> \<Longrightarrow> (s, s') \<in> G"
  shows "prog.p2s (prog.action F) \<le> \<lbrace>\<lambda>A. wdp.floor A (P A)\<rbrace>, As \<turnstile>\<^sub>P G, \<lbrace>\<lambda>A v. wdp.ceiling A (Q A v)\<rbrace>"
by (simp add: assms pag_def wdp.action INFI)

lemmas sup = ag.prog.sup

lemma bind:
  assumes "\<And>v. prog.p2s (g v) \<le> \<lbrace>\<lambda>A. Q' A v\<rbrace>, As \<turnstile>\<^sub>P G, \<lbrace>Q\<rbrace>"
  assumes "prog.p2s f \<le> \<lbrace>P\<rbrace>, As \<turnstile>\<^sub>P G, \<lbrace>Q'\<rbrace>"
  shows "prog.p2s (f \<bind> g) \<le> \<lbrace>P\<rbrace>, As \<turnstile>\<^sub>P G, \<lbrace>Q\<rbrace>"
unfolding pag_def
by (fastforce intro: INFI ag.prog.bind[rotated]
                     order.trans[OF assms(2) pag.mono[OF _ _ _ order.refl]]
                     order.trans[OF assms(1) pag.mono[where As'="{A}" for A], simplified pag.singleton]
          simp flip: pag.singleton)+

lemma parallel:
  assumes "prog.p2s c\<^sub>1 \<le> \<lbrace>P\<^sub>1\<rbrace>, (\<union>) G\<^sub>2 ` A \<turnstile>\<^sub>P G\<^sub>1, \<lbrace>Q\<^sub>1\<rbrace>"
  assumes "prog.p2s c\<^sub>2 \<le> \<lbrace>P\<^sub>2\<rbrace>, (\<union>) G\<^sub>1 ` A \<turnstile>\<^sub>P G\<^sub>2, \<lbrace>Q\<^sub>2\<rbrace>"
  shows "prog.p2s (prog.parallel c\<^sub>1 c\<^sub>2)
      \<le> \<lbrace>\<lambda>R. P\<^sub>1 (R \<union> G\<^sub>2) \<^bold>\<and> P\<^sub>2 (R \<union> G\<^sub>1)\<rbrace>, A \<turnstile>\<^sub>P G\<^sub>1 \<union> G\<^sub>2, \<lbrace>\<lambda>R v. Q\<^sub>1 (R \<union> G\<^sub>2) v \<^bold>\<and> Q\<^sub>2 (R \<union> G\<^sub>1) v\<rbrace>"
unfolding pag_def
by (force intro: INFI ag.prog.parallel order.trans[OF assms(1) pag.mono]
                 order.trans[OF assms(2) pag.mono]
      simp flip: pag.singleton)

text\<open> etc. -- the other rules follow similarly \<close>

setup \<open>Sign.parent_path\<close>


subsection\<open> Examples\label{sec:explicit_stabilisation_eg} \<close>

text\<open>

There is not always a single (traditional) most general assume/guarantee specification (\S2.1).

\<close>

type_synonym state = int \<comment>\<open> just \<open>x\<close> \<close>
abbreviation (input) "incr \<equiv> prog.write ((+) 1)" \<comment>\<open> atomic increment \<close>
abbreviation (input) increases :: "int rel" where "increases \<equiv> {(x, x'). x \<le> x'}"

lemma ag_incr1: \<comment>\<open> the precondition is stable as the rely is very strong \<close>
  shows "prog.p2s incr \<le> \<lbrace>(=) c\<rbrace>, {} \<turnstile> increases, \<lbrace>\<langle>(=) (c + 1)\<rangle>\<rbrace>"
by (rule ag.prog.action; simp add: stable.empty)

lemma ag_incr2: \<comment>\<open> note the weaker precondition due to the larger assume \<close>
  shows "prog.p2s incr \<le> \<lbrace>(\<le>) c\<rbrace>, increases \<turnstile> increases, \<lbrace>\<langle>(\<le>) (c + 1)\<rangle>\<rbrace>"
by (rule ag.prog.action; auto simp: stable_def monotone_def le_bool_def)

lemma ag_incr1_par_incr1:
  shows "prog.p2s (incr \<parallel> incr) \<le> \<lbrace>\<lambda>x. c \<le> x\<rbrace>, increases \<turnstile> increases, \<lbrace>\<lambda>_ x. c + 1 \<le> x\<rbrace>"
apply (rule ag.pre_pre)
 apply (rule ag.pre_post)
  apply (rule ag.prog.parallel[where P\<^sub>1="\<lambda>x. c \<le> x" and P\<^sub>2="\<lambda>x. c \<le> x"
                                 and Q\<^sub>1="\<lambda>_ x. c + 1 \<le> x" and Q\<^sub>2="\<lambda>_ x. c + 1 \<le> x"
                                 and G\<^sub>1="increases" and G\<^sub>2="increases", simplified])
    apply (rule ag.prog.action; simp add: stable_def monotone_def le_boolI; fail)
   apply (rule ag.prog.action; simp add: stable_def monotone_def le_boolI; fail)
  apply simp_all
done

text\<open>

Using explicit stabilisation we can squash the two specifications for \<^const>\<open>incr\<close> into a single one (\S4).

\<close>

lemma \<comment>\<open> postcondition cannot be simplified for arbitrary \<open>A\<close> \<close>
  shows "prog.p2s incr \<le> \<lbrace>wdp.ceiling A ((=) c)\<rbrace>, A \<turnstile> increases, \<lbrace>\<langle>wdp.ceiling A (\<lambda>s. wdp.ceiling A ((=) c) (s - 1))\<rangle>\<rbrace>"
by (rule ag.pre_pre[OF wdp.action]) (simp add: wdp.floor_ceiling)+

\<comment>\<open> The set of assumes that commute with the increment \<close>
abbreviation (input) comm_xpp :: "int rel set" where
  "comm_xpp \<equiv> {A. \<forall>p s. wdp.ceiling A p (s - 1) = wdp.ceiling A (\<lambda>s. p (s - 1)) s}"

lemma pag_incr: \<comment>\<open> postcondition can be simplified wrt \<open>comm_xpp\<close> \<close>
  shows "prog.p2s incr \<le> \<lbrace>\<lambda>A. wdp.ceiling A ((=) c)\<rbrace>, comm_xpp \<turnstile>\<^sub>P increases, \<lbrace>\<lambda>A. \<langle>wdp.ceiling A ((=) (c + 1))\<rangle>\<rbrace>"
apply (rule order.trans[OF _ pag.mono[OF _  order.refl order.refl]])
  apply (rule pag.action[where P="\<lambda>A. wdp.ceiling A ((=) c)"
                           and Q="\<lambda>A v s. wdp.ceiling A ((=) c) (s - 1)"])
   apply (simp_all add: wdp.floor_ceiling eq_diff_eq)
done

\<comment>\<open> the two earlier specifications can be recovered \<close>
lemma
  shows "prog.p2s incr \<le> \<lbrace>(=) c\<rbrace>, {} \<turnstile> increases, \<lbrace>\<langle>(=) (c + 1)\<rangle>\<rbrace>"
apply (rule order.trans[OF pag_incr])
apply (subst pag.singleton[symmetric])
apply (rule pag.mono; force)
done

lemma
  shows "prog.p2s incr \<le> \<lbrace>(\<le>) c\<rbrace>, increases \<turnstile> increases, \<lbrace>\<langle>(\<le>) (c + 1)\<rangle>\<rbrace>"
apply (rule order.trans[OF pag_incr[where c=c]])
apply (subst pag.singleton[symmetric])
apply (rule pag.mono; force simp: wdp.ceiling_def order_rtrancl dest: zless_imp_add1_zle)
done

(*<*)

end
(*>*)
