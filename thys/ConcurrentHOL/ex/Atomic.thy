(*<*)
theory Atomic
imports
  "ConcurrentHOL.ConcurrentHOL"
begin

(*>*)
section\<open> Atomic sections \label{sec:atomic} \<close>

text\<open>

By restricting the environment to stuttering steps we can consider arbitrary processes to be atomic,
i.e., free of interference.

\<close>

setup \<open>Sign.mandatory_path "spec"\<close>

definition atomic :: "'a \<Rightarrow> ('a, 's, 'v) spec \<Rightarrow> ('a, 's, 'v) spec" where
  "atomic a P = P \<sqinter> spec.rel ({a} \<times> UNIV)"

setup \<open>Sign.mandatory_path "idle"\<close>

lemma atomic_le_conv[spec.idle_le]:
  shows "spec.idle \<le> spec.atomic a P \<longleftrightarrow> spec.idle \<le> P"
by (simp add: spec.atomic_def spec.idle.rel_le)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "term"\<close>

setup \<open>Sign.mandatory_path "none"\<close>

lemma atomic:
  shows "spec.term.none (spec.atomic a P) = spec.atomic a (spec.term.none P)"
by (simp add: spec.atomic_def spec.term.none.inf spec.term.none.inf_rel)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "all"\<close>

lemma atomic:
  shows "spec.term.all (spec.atomic a P) = spec.atomic a (spec.term.all P)"
by (simp add: spec.atomic_def spec.term.all.inf spec.term.all.rel)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "atomic"\<close>

lemma bot[simp]:
  shows "spec.atomic a \<bottom> = \<bottom>"
by (simp add: spec.atomic_def)

lemma top[simp]:
  shows "spec.atomic a \<top> = spec.rel ({a} \<times> UNIV)"
by (simp add: spec.atomic_def)

lemma contractive:
  shows "spec.atomic a P \<le> P"
by (simp add: spec.atomic_def)

lemma idempotent[simp]:
  shows "spec.atomic a (spec.atomic a P) = spec.atomic a P"
by (simp add: spec.atomic_def)

lemma monotone:
  shows "mono (spec.atomic a)"
by (simp add: spec.atomic_def monoI le_infI1)

lemmas strengthen[strg] = st_monotone[OF spec.atomic.monotone]
lemmas mono = monotoneD[OF spec.atomic.monotone]
lemmas mono2mono[cont_intro, partial_function_mono]
  = monotone2monotone[OF spec.atomic.monotone, simplified, of orda P for orda P]

lemma Sup:
  shows "spec.atomic a (\<Squnion>X) = \<Squnion>(spec.atomic a ` X)"
by (simp add: spec.atomic_def ac_simps heyting.inf_Sup_distrib)

lemmas sup = spec.atomic.Sup[where X="{P, Q}" for P Q, simplified]

lemma mcont2mcont[cont_intro]:
  assumes "mcont luba orda Sup (\<le>) P"
  shows "mcont luba orda Sup (\<le>) (\<lambda>x. spec.atomic a (P x))"
by (simp add: spec.atomic_def assms)

lemma Inf_not_empty:
  assumes "X \<noteq> {}"
  shows "spec.atomic a (\<Sqinter>X) = \<Sqinter>(spec.atomic a ` X)"
using assms by (simp add: spec.atomic_def INF_inf_const2)

lemmas inf = spec.atomic.Inf_not_empty[where X="{P, Q}" for P Q, simplified]

lemma idle:
  shows "spec.atomic a spec.idle = spec.idle"
by (simp add: spec.atomic_def inf.absorb1 spec.idle.rel_le)

lemma action:
  shows "spec.atomic a (spec.action F) = spec.action (F \<inter> UNIV \<times> ({a} \<times> UNIV \<union> UNIV \<times> Id))"
by (simp add: spec.atomic_def spec.action.inf_rel_reflcl)

lemma return:
  shows "spec.atomic a (spec.return v) = spec.return v"
by (simp add: spec.return_def spec.atomic.action Times_Int_Times)

lemma bind:
  shows "spec.atomic a (f \<bind> g) = spec.atomic a f \<bind> (\<lambda>v. spec.atomic a (g v))"
by (simp add: spec.atomic_def spec.bind.inf_rel ac_simps)

lemma map_le:
  fixes af :: "'a \<Rightarrow> 'b"
  shows "spec.map af sf vf (spec.atomic a P) \<le> spec.atomic (af a) (spec.map af sf vf P)"
by (auto simp: spec.atomic_def spec.map.inf_rel
       intro!: spec.map.mono inf.mono order.refl spec.rel.mono)

lemma invmap:
  fixes af :: "'a \<Rightarrow> 'b"
  shows "spec.atomic a (spec.invmap af sf vf P) \<le> spec.invmap af sf vf (spec.atomic (af a) P)"
by (auto simp: spec.atomic_def spec.invmap.inf spec.invmap.rel
       intro!: le_infI2 spec.rel.mono)

lemma rel:
  shows "spec.atomic a (spec.rel r) = spec.rel (r \<inter> {a} \<times> UNIV)"
by (simp add: spec.atomic_def flip: spec.rel.inf)

lemma interference:
  shows "spec.atomic (proc a) (spec.rel ({env} \<times> UNIV)) = spec.rel {}"
by (simp add: spec.atomic.rel flip: Times_Int_distrib1)

setup \<open>Sign.mandatory_path "cam"\<close>

lemma cl:
  shows "spec.atomic (proc a) (spec.cam.cl ({env} \<times> UNIV) P) = spec.atomic (proc a) P"
by (simp add: spec.cam.cl_def spec.atomic.sup spec.atomic.bind spec.atomic.interference
              spec.rel.empty spec.term.none.bind spec.term.none.Sup spec.term.none.return
              image_image spec.bind.botR spec.bind.idleR sup_iff_le
        flip: spec.term.none.atomic spec.term.all.atomic)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "interference"\<close>

lemma cl:
  shows "spec.atomic (proc a) (spec.interference.cl ({env} \<times> UNIV) P) = spec.return () \<then> spec.atomic (proc a) P"
by (simp add: spec.interference.cl_def UNIV_unit spec.atomic.bind spec.atomic.interference
              spec.rel.empty spec.atomic.cam.cl spec.bind.return spec.atomic.return)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "prog"\<close>

lift_definition atomic :: "('s, 'v) prog \<Rightarrow> ('s, 'v) prog" is
  "\<lambda>P. spec.interference.cl ({env} \<times> UNIV) (spec.atomic self P)" ..

setup \<open>Sign.mandatory_path "atomic"\<close>

lemma bot[simp]:
  shows "prog.atomic \<bottom> = \<bottom>"
by transfer
   (simp add: spec.interference.cl.bot spec.atomic.interference spec.interference.cl.rel
        flip: spec.term.none.atomic spec.term.none.interference.cl)

lemma contractive:
  shows "prog.atomic P \<le> P"
by transfer (simp add: spec.atomic.contractive spec.interference.least)

lemma idempotent[simp]:
  shows "prog.atomic (prog.atomic P) = prog.atomic P"
by transfer (metis spec.atomic.idempotent spec.atomic.interference.cl spec.interference.closed_conv)

lemma monotone:
  shows "mono prog.atomic"
by (rule monoI) (transfer; simp add: spec.atomic.mono spec.interference.mono_cl)

lemmas strengthen[strg] = st_monotone[OF prog.atomic.monotone]
lemmas mono = monotoneD[OF prog.atomic.monotone]
lemmas mono2mono[cont_intro, partial_function_mono] = monotone2monotone[OF prog.atomic.monotone, simplified, of orda P for orda P]

lemma Sup:
  shows "prog.atomic (\<Squnion>X) = \<Squnion>(prog.atomic ` X)"
by transfer
   (simp add: spec.atomic.Sup spec.atomic.sup spec.interference.cl_Sup spec.interference.cl_sup
              image_image spec.interference.cl.bot spec.atomic.interference spec.interference.cl.rel
        flip: spec.term.none.atomic spec.term.none.interference.cl)

lemmas sup = prog.atomic.Sup[where X="{P, Q}" for P Q, simplified]

lemma mcont:
  shows "mcont Sup (\<le>) Sup (\<le>) prog.atomic"
by (simp add: mcontI contI prog.atomic.Sup)

lemmas mcont2mcont[cont_intro] = mcont2mcont[OF prog.atomic.mcont, of luba orda P for luba orda P]

lemma Inf_le:
  shows "prog.atomic (\<Sqinter>X) \<le> \<Sqinter>(prog.atomic ` X)"
by transfer (simp add: Inf_lower le_INF_iff spec.atomic.mono spec.interference.mono_cl)

lemmas inf_le = prog.atomic.Inf_le[where X="{P, Q}" for P Q, simplified]

lemma action:
  shows "prog.atomic (prog.action F) = prog.action F"
by transfer
   (simp add: spec.atomic.interference.cl spec.atomic.action spec.bind.returnL spec.idle.action_le;
    rule arg_cong; blast)

lemma return:
  shows "prog.atomic (prog.return v) = prog.return v"
by (simp add: prog.return_def prog.atomic.action)

lemma bind_le:
  shows "prog.atomic (f \<bind> g) \<le> prog.atomic f \<bind> (\<lambda>v. prog.atomic (g v))"
by transfer
   (simp add: spec.atomic.bind spec.bind.mono
              spec.interference.closed.bind spec.interference.expansive spec.interference.least)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "p2s"\<close>

lemmas atomic = prog.atomic.rep_eq

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.parent_path\<close>


subsection\<open> Inhabitation \<close>

setup \<open>Sign.mandatory_path "inhabits.spec"\<close>

lemma atomic:
  assumes "P -s, xs\<rightarrow> P'"
  assumes "trace.steps' s xs \<subseteq> {a} \<times> UNIV"
  shows "spec.atomic a P -s, xs\<rightarrow> spec.atomic a P'"
unfolding spec.atomic_def by (rule inhabits.inf[OF assms(1) inhabits.spec.rel.rel[OF assms(2)]])

lemma atomic_term:
  assumes "P -s, xs\<rightarrow> spec.return v"
  assumes "trace.steps' s xs \<subseteq> {a} \<times> UNIV"
  shows "spec.atomic a P -s, xs\<rightarrow> spec.return v"
by (rule inhabits.spec.atomic[where P'="spec.return v", simplified spec.atomic.return, OF assms])

lemma atomic_diverge:
  assumes "P -s, xs\<rightarrow> \<bottom>"
  assumes "trace.steps' s xs \<subseteq> {a} \<times> UNIV"
  shows "spec.atomic a P -s, xs\<rightarrow> \<bottom>"
by (rule inhabits.spec.atomic[where P'="\<bottom>", simplified spec.atomic.bot, OF assms])

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "inhabits.prog"\<close>

lemma atomic_term:
  assumes "prog.p2s P -s, xs\<rightarrow> spec.return v"
  assumes "trace.steps' s xs \<subseteq> {self} \<times> UNIV"
  shows "prog.p2s (prog.atomic P) -s, xs\<rightarrow> spec.return v"
unfolding prog.p2s.atomic
by (rule inhabits.mono[OF spec.interference.expansive order.refl
                          inhabits.spec.atomic_term[OF assms]])

lemma atomic_diverge:
  assumes "prog.p2s P -s, xs\<rightarrow> \<bottom>"
  assumes "trace.steps' s xs \<subseteq> {self} \<times> UNIV"
  shows "prog.p2s (prog.atomic P) -s, xs\<rightarrow> \<bottom>"
unfolding prog.p2s.atomic
by (rule inhabits.mono[OF spec.interference.expansive order.refl
                               inhabits.spec.atomic_diverge[OF assms]])

setup \<open>Sign.parent_path\<close>


subsection\<open> Assume/guarantee \<close>

setup \<open>Sign.mandatory_path "ag.prog"\<close>

lemma atomic:
  assumes "prog.p2s c \<le> \<lbrace>P\<rbrace>, Id \<turnstile> G, \<lbrace>Q\<rbrace>"
  assumes P: "stable A P"
  assumes Q: "\<And>v. stable A (Q v)"
  shows "prog.p2s (prog.atomic c) \<le> \<lbrace>P\<rbrace>, A \<turnstile> G, \<lbrace>Q\<rbrace>"
apply (subst ag.assm_heyting[where A=A and r=A, simplified, symmetric])
apply (simp add: prog.p2s.atomic)
apply (strengthen ord_to_strengthen[OF assms(1)])
apply (simp add: spec.atomic_def heyting ac_simps spec.interference.cl.inf_rel inf_sup_distrib Times_Int_Times
      flip: spec.rel.inf)
using assms
apply (force intro: order.trans[OF _ spec.interference.cl_ag_le[where A=A and r=A, simplified]]
                    spec.interference.cl.mono[OF order.refl] ag.pre_a
          simp add: heyting[symmetric] ag.assm_heyting[where r="{}", simplified])
done

setup \<open>Sign.parent_path\<close>
(*<*)

end
(*>*)
