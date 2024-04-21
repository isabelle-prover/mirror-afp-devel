(*<*)
theory TSO
imports
  Heap
begin

(*>*)
section\<open> Total store order (TSO)\label{sec:tso} \<close>

text\<open>

The total store order (TSO) memory model (\<^citet>\<open>"OwensSarkarSewell:2009"\<close>; valid on multicore
x86) can be modelled as a closure as demonstrated by \<^citet>\<open>\<open>p182\<close> in "JagadeesanEtAl:2012"\<close>.
Essentially this is done by incorporating a write buffer into each thread's local state and adding
buffer draining opportunities before and after every command.  The only subtlety is that the all
threads involved in a parallel composition need to start and end with empty write buffers (see
\S\ref{sec:tso-parallel}).

We configure the code generator in \S\ref{sec:tso-code_generation}.

Comparison with \<^citet>\<open>"JagadeesanEtAl:2012"\<close>:
 \<^item> We ignore mumbling-related issues and it doesn't make any difference
  \<^item> in our model we commit writes one at a time; mumbling allows several to be committed at once (p182) which we model as an uninterrupted sequence of individual writes
  \<^item> if we allowed \<open>commit_writes\<close> to commit multiple writes in a single step then \<open>tso_closure\<close> would not be idempotent
 \<^item> their semantics is for terminating computations only; ours is for safety only
 \<^item> their language is deterministic, ours is non-deterministic
 \<^item> They do not provide many general laws for TSO
 \<^item> Their claims that the semantics allows them to prove things (\S5) is not substantiated

\<close>

type_synonym write_buffer = "heap.write list"

definition apply_writes :: "write_buffer \<Rightarrow> heap.t \<Rightarrow> heap.t" where
  "apply_writes ws = fold (\<lambda>w. (\<circ>) (heap.apply_write w)) ws id"

lemma apply_write_present:
  assumes "heap.present r s"
  shows "heap.present r (heap.apply_write w s)"
using assms by (cases w) (simp split: heap.obj_at.splits)

lemma apply_writes_present:
  assumes "heap.present r s"
  shows "heap.present r (apply_writes wb s)"
using assms by (induct wb arbitrary: s) (simp_all add: apply_writes_def fold_fun apply_write_present)

setup \<open>Sign.mandatory_path "raw"\<close>

type_synonym 'v tso = "write_buffer \<Rightarrow> (heap.t, 'v \<times> write_buffer) prog"

definition bind :: "'a raw.tso \<Rightarrow> ('a \<Rightarrow> 'b raw.tso) \<Rightarrow> 'b raw.tso" where
  "bind f g = (\<lambda>wb. f wb \<bind> uncurry g)"

adhoc_overloading
  Monad_Syntax.bind raw.bind

definition prim_return :: "'a \<Rightarrow> 'a raw.tso" where
  "prim_return v = (\<lambda>wb. prog.return (v, wb))"

setup \<open>Sign.mandatory_path "bind"\<close>

lemma mono:
  assumes "f \<le> f'"
  assumes "\<And>x. g x \<le> g' x"
  shows "raw.bind f g \<le> raw.bind f' g'"
using assms by (fastforce simp: raw.bind_def prog.bind.mono le_fun_def intro: prog.bind.mono)

lemma strengthen[strg]:
  assumes "st_ord F f f'"
  assumes "\<And>x. st_ord F (g x) (g' x)"
  shows "st_ord F (raw.bind f g) (raw.bind f' g')"
using assms by (cases F; clarsimp intro!: raw.bind.mono)

lemma mono2mono[cont_intro, partial_function_mono]:
  assumes "monotone orda (\<le>) F"
  assumes "\<And>x. monotone orda (\<le>) (\<lambda>y. G y x)"
  shows "monotone orda (\<le>) (\<lambda>f. raw.bind (F f) (G f))"
using assms unfolding monotone_def by (meson raw.bind.mono)

lemma botL:
  shows "raw.bind \<bottom> g = \<bottom>"
by (simp add: raw.bind_def fun_eq_iff prog.bind.botL)

lemma bind:
  fixes f :: "_ raw.tso"
  shows "f \<bind> g \<bind> h = f \<bind> (\<lambda>x. g x \<bind> h)"
by (simp add: raw.bind_def fun_eq_iff split_def prog.bind.bind)

lemma prim_return:
  shows prim_returnL: "raw.bind (raw.prim_return v) = (\<lambda>g. g v)"
    and prim_returnR: "f \<bind> raw.prim_return = f"
by (simp_all add: fun_eq_iff raw.prim_return_def raw.bind_def split_def prog.bind.return)

lemma supL:
  fixes g :: "_ \<Rightarrow> _ raw.tso"
  shows "f\<^sub>1 \<squnion> f\<^sub>2 \<bind> g = (f\<^sub>1 \<bind> g) \<squnion> (f\<^sub>2 \<bind> g)"
by (simp add: raw.bind_def fun_eq_iff prog.bind.supL)

lemma supR:
  fixes f :: "_ raw.tso"
  shows "f \<bind> (\<lambda>v. g\<^sub>1 v \<squnion> g\<^sub>2 v) = (f \<bind> g\<^sub>1) \<squnion> (f \<bind> g\<^sub>2)"
by (simp add: raw.bind_def fun_eq_iff split_def prog.bind.supR)

lemma SUPL:
  fixes X :: "_ set"
  fixes f :: "_ \<Rightarrow> _ raw.tso"
  shows "(\<Squnion>x\<in>X. f x) \<bind> g = (\<Squnion>x\<in>X. f x \<bind> g)"
by (simp add: raw.bind_def fun_eq_iff prog.bind.SUPL image_image)

lemma SUPR:
  fixes X :: "_ set"
  fixes f :: "_ raw.tso"
  shows "f \<bind> (\<lambda>v. \<Squnion>x\<in>X. g x v) = (\<Squnion>x\<in>X. f \<bind> g x) \<squnion> (f \<bind> \<bottom>)"
by (simp add: raw.bind_def split_def fun_eq_iff image_image bot_fun_def prog.bind.SUPR)

lemma SUPR_not_empty:
  fixes f :: "_ raw.tso"
  assumes "X \<noteq> {}"
  shows "f \<bind> (\<lambda>v. \<Squnion>x\<in>X. g x v) = (\<Squnion>x\<in>X. f \<bind> g x)"
by (simp add: raw.bind_def split_def fun_eq_iff image_image prog.bind.SUPR_not_empty[OF assms])

lemma mcont2mcont[cont_intro]:
  assumes "mcont luba orda Sup (\<le>) f"
  assumes "\<And>v. mcont luba orda Sup (\<le>) (\<lambda>x. g x v)"
  shows "mcont luba orda Sup (\<le>) (\<lambda>x. raw.bind (f x) (g x))"
proof(rule ccpo.mcont2mcont'[OF complete_lattice_ccpo _ _ assms(1)])
  show "mcont Sup (\<le>) Sup (\<le>) (\<lambda>f. raw.bind f (g x))" for x
    by (intro mcontI contI monotoneI) (simp_all add: raw.bind.mono flip: raw.bind.SUPL)
  show "mcont luba orda Sup (\<le>) (\<lambda>x. raw.bind f (g x))" for f
    by (intro mcontI monotoneI contI)
       (simp_all add: mcont_monoD[OF assms(2)] raw.bind.mono flip: raw.bind.SUPR_not_empty contD[OF mcont_cont[OF assms(2)]])
qed

setup \<open>Sign.parent_path\<close>

interpretation kleene: kleene "raw.prim_return ()" "\<lambda>x y. raw.bind x \<langle>y\<rangle>"
by standard (simp_all add: raw.bind.prim_return raw.bind.botL raw.bind.bind raw.bind.supL raw.bind.supR)

primrec commit_write :: "unit raw.tso" where
  "commit_write [] = prog.return ((), [])"
| "commit_write (w # wb) = prog.action {(((), wb), h, heap.apply_write w h) |h. True}"

definition commit_writes :: "unit raw.tso" where
  "commit_writes = raw.kleene.star raw.commit_write"

setup \<open>Sign.mandatory_path "tso"\<close>

definition cl :: "'v raw.tso \<Rightarrow> 'v raw.tso" where
  "cl P = raw.commit_writes \<then> P \<bind> (\<lambda>v. raw.commit_writes \<then> raw.prim_return v)"

setup \<open>Sign.parent_path\<close>

definition action :: "(write_buffer \<Rightarrow> ('v \<times> write_buffer \<times> heap.t \<times> heap.t) set) \<Rightarrow> 'v raw.tso" where
  "action F = raw.tso.cl (\<lambda>wb. prog.action {((v, wb @ ws), ss') |v ss' ws. (v, ws, ss') \<in> F wb})"

definition return :: "'v \<Rightarrow> 'v raw.tso" where
  "return v = raw.action \<langle>{v} \<times> {[]} \<times> Id\<rangle>"

definition guard :: "(write_buffer \<Rightarrow> heap.t pred) \<Rightarrow> unit raw.tso" where
  "guard g = raw.action (\<lambda>wb. {()} \<times> {[]} \<times> Diag (g wb))"

definition MFENCE :: "unit raw.tso" where
  "MFENCE = raw.guard (\<lambda>wb s. wb = [])"

definition vmap :: "('v \<Rightarrow> 'w) \<Rightarrow> 'v raw.tso \<Rightarrow> 'w raw.tso" where
  "vmap vf P = (\<lambda>wb. prog.vmap (map_prod vf id) (P wb))"

\<comment>\<open> Parallel composition\label{sec:tso-parallel} \<close>
definition t2p :: "'v raw.tso \<Rightarrow> (heap.t, 'v) prog" where
  "t2p P = P [] \<bind> (\<lambda>(v, wb). raw.MFENCE wb \<then> prog.return v)"

\<comment>\<open> \<^citet>\<open>\<open>p184 rule \<^verbatim>\<open>PAR-CMD\<close>\<close> in "JagadeesanEtAl:2012"\<close>: perform \<^verbatim>\<open>MFENCE\<close> before fork \<close>
definition parallel :: "unit raw.tso \<Rightarrow> unit raw.tso \<Rightarrow> unit raw.tso" where
  "parallel P Q = raw.MFENCE \<then> \<langle>(raw.t2p P \<parallel> raw.t2p Q) \<then> prog.return ((), [])\<rangle>"

lemma return_alt_def:
  shows "raw.return = (\<lambda>v. raw.tso.cl (raw.prim_return v))"
by (fastforce simp: raw.return_def raw.action_def raw.prim_return_def prog.return_def
             intro: arg_cong[where f="\<lambda>P. raw.tso.cl P wb" for wb] arg_cong[where f="prog.action"])

setup \<open>Sign.mandatory_path "commit_writes"\<close>

lemma return_le:
  shows "raw.prim_return () \<le> raw.commit_writes"
unfolding raw.commit_writes_def by (subst raw.kleene.star.simps) simp

lemma return_le':
  shows "prog.return ((), wb) \<le> raw.commit_writes wb"
using raw.commit_writes.return_le by (simp add: raw.prim_return_def le_fun_def)

lemma commit_writes:
  shows "raw.commit_writes \<then> raw.commit_writes = raw.commit_writes"
by (simp add: raw.commit_writes_def raw.kleene.star_comp_star)

lemma Nil:
  shows "raw.commit_writes [] = prog.return ((), [])" (is "?lhs = ?rhs")
proof(rule antisym)
  show "?lhs \<le> ?rhs"
    unfolding raw.commit_writes_def
    by (induct rule: raw.kleene.star.fixp_induct)
       (simp_all add: raw.bind_def raw.prim_return_def prog.bind.returnL prog.p2s.bot spec.bind.mono)
  show "?rhs \<le> ?lhs"
    unfolding raw.commit_writes_def
    by (subst raw.kleene.star.simps) (simp add: raw.bind_def raw.prim_return_def)
qed

lemma Cons:
  shows "raw.commit_writes (w # wb)
       = (raw.commit_write [w] \<then> raw.commit_writes wb) \<squnion> raw.prim_return () (w # wb)"
apply (simp add: raw.commit_writes_def)
apply (subst (1) raw.kleene.star.simps)
apply (subst (1) raw.bind_def)
apply simp
apply (subst prog.action.return_const[where F="{(s, heap.apply_write w s) |s. True}" and V="{((), wb)}" and W="{((), [])}", simplified Pair_image[symmetric] image_def, simplified])
apply (simp add: prog.bind.bind prog.bind.returnL)
done

lemma Cons_le:
  shows "raw.commit_write [w] \<then> raw.commit_writes wb \<le> raw.commit_writes (w # wb)"
by (simp add: raw.commit_writes.Cons)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "spec.singleton.raw"\<close>

lemma prim_return_Nil_le:
  shows "\<lblot>s, [], Some ((), wb)\<rblot> \<le> prog.p2s (raw.prim_return () wb)"
by (simp add: raw.prim_return_def prog.p2s.return spec.interference.cl.return
              spec.bind.continueI[where xs="[]", simplified] spec.singleton.le_conv)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "spec.singleton.raw.commit_writes"\<close>

lemma noop_le:
  shows "\<lblot>s, [], Some ((), wb)\<rblot> \<le> prog.p2s (raw.commit_writes wb)"
unfolding raw.commit_writes_def
by (rule order.trans[OF spec.singleton.raw.prim_return_Nil_le
                        prog.p2s.mono[OF le_funD[OF raw.kleene.epsilon_star_le]]])

lemma wb_suffix:
  assumes "\<lblot>s, xs, Some ((), wb')\<rblot> \<le> prog.p2s (raw.commit_writes wb)"
  shows "suffix wb' wb"
using assms
by (induct wb arbitrary: s xs)
   (auto simp: raw.commit_writes.Nil raw.commit_writes.Cons raw.prim_return_def
               prog.p2s.simps prog.p2s.return spec.interference.cl.return
               trace.split_all spec.singleton.le_conv
               suffix_ConsI
        elim!: spec.singleton.bind_le)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "raw"\<close>

setup \<open>Sign.mandatory_path "tso.cl"\<close>

lemma bind_commit_writes_absorbL:
  fixes P :: "'v raw.tso"
  shows "raw.commit_writes \<then> raw.tso.cl P = raw.tso.cl P"
by (simp add: raw.tso.cl_def raw.commit_writes.commit_writes flip: raw.bind.bind)

lemma bind_commit_writes_absorb_unitR:
  fixes P :: "unit raw.tso"
  shows "raw.tso.cl P \<then> raw.commit_writes = raw.tso.cl P"
by (simp add: raw.tso.cl_def raw.bind.bind raw.commit_writes.commit_writes raw.bind.prim_returnR)

lemma bind_commit_writes_absorbR:
  fixes P :: "'v raw.tso"
  shows "raw.tso.cl P \<bind> (\<lambda>v. raw.commit_writes \<then> raw.prim_return v) = raw.tso.cl P"
by (simp add: raw.tso.cl_def raw.bind.bind raw.commit_writes.commit_writes raw.bind.prim_returnL)
   (simp add: raw.commit_writes.commit_writes flip: raw.bind.bind)

lemma bot:
  shows "raw.tso.cl \<bottom> = raw.commit_writes \<bind> \<bottom>"
by (simp add: raw.tso.cl_def raw.bind.bind raw.bind.botL flip: bot_fun_def)

lemma prim_return:
  shows "raw.tso.cl (raw.prim_return v) = raw.commit_writes \<then> raw.prim_return v"
by (simp add: raw.tso.cl_def raw.bind.bind raw.bind.prim_returnL)
   (simp add: raw.commit_writes.commit_writes flip: raw.bind.bind)

lemma Nil:
  shows "raw.tso.cl P [] = P [] \<bind> (\<lambda>v. raw.commit_writes (snd v) \<bind> (\<lambda>w. prog.return (fst v, snd w)))"
by (simp add: raw.tso.cl_def raw.bind_def raw.prim_return_def raw.commit_writes.Nil prog.bind.returnL split_def)

lemma commit:
  fixes wb :: write_buffer
  shows "raw.commit_write [w] \<then> f wb \<le> raw.tso.cl f (w # wb)"
apply (simp add: raw.tso.cl_def raw.bind_def raw.prim_return_def split_def)
apply (strengthen ord_to_strengthen[OF raw.commit_writes.Cons_le])
apply (simp add: prog.bind.bind)
apply (rule prog.bind.mono[OF order.refl])
apply (strengthen ord_to_strengthen[OF raw.commit_writes.return_le'])
apply (simp add: prog.bind.returnL prog.bind.returnR)
done

setup \<open>Sign.parent_path\<close>

interpretation tso: closure_complete_distrib_lattice_distributive_class raw.tso.cl
proof standard
  show "(x \<le> raw.tso.cl y) = (raw.tso.cl x \<le> raw.tso.cl y)" for x y :: "'a raw.tso"
  proof(intro iffD2[OF order_class.order.closure_axioms_alt_def[unfolded closure_axioms_def], rule_format, simplified conj_explode] allI)
    show "P \<le> raw.tso.cl P" for P :: "'a raw.tso"
      unfolding raw.tso.cl_def
      by (strengthen ord_to_strengthen[OF raw.commit_writes.return_le])
         (simp add: raw.bind.prim_returnL raw.bind.prim_returnR)
    show "mono raw.tso.cl"
    proof(rule monotoneI)
      fix P P' :: "'v raw.tso"
      assume "P \<le> P'" show "raw.tso.cl P \<le> raw.tso.cl P'"
        unfolding raw.tso.cl_def by (strengthen ord_to_strengthen(1)[OF \<open>P \<le> P'\<close>]) simp
    qed
    show "raw.tso.cl (raw.tso.cl P) = raw.tso.cl P" for P :: "'a raw.tso"
      by (simp add: raw.tso.cl_def raw.bind.bind raw.commit_writes.commit_writes raw.bind.prim_returnL)
         (simp add: raw.commit_writes.commit_writes flip: raw.bind.bind)
  qed
  show "raw.tso.cl (\<Squnion>X) \<le> \<Squnion> (raw.tso.cl ` X) \<squnion> raw.tso.cl \<bottom>" for X :: "'a raw.tso set"
    by (simp add: raw.tso.cl_def raw.bind.bind raw.bind.botL flip: bot_fun_def raw.bind.SUPR raw.bind.SUPL)
qed

setup \<open>Sign.mandatory_path "tso.cl"\<close>

lemma bind:
  fixes f :: "'v raw.tso"
  assumes "f \<in> raw.tso.closed"
  shows "raw.tso.cl (f \<bind> g) = f \<bind> (\<lambda>v. raw.tso.cl (g v))"
apply (simp add: raw.tso.cl_def raw.bind.bind)
apply (subst (1 2) raw.tso.closed_conv[OF assms(1)])
apply (simp add: raw.tso.cl.bind_commit_writes_absorbL flip: raw.bind.bind)
apply (subst (1) raw.tso.cl.bind_commit_writes_absorbR[symmetric])
apply (simp add: raw.bind.bind raw.bind.prim_returnL)
done

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "bind"\<close>

lemma commit_writes_absorbL:
  assumes "f \<in> raw.tso.closed"
  shows "raw.commit_writes \<then> f = f"
by (metis assms raw.tso.closed_conv raw.tso.cl.bind_commit_writes_absorbL)

lemma commit_writes_absorb_unitR:
  assumes "f \<in> raw.tso.closed"
  shows "f \<then> raw.commit_writes = f"
by (metis assms raw.tso.closed_conv raw.tso.cl.bind_commit_writes_absorb_unitR)

lemma returnL:
  assumes "g v \<in> raw.tso.closed"
  shows "raw.return v \<bind> g = g v"
by (simp add: assms raw.return_alt_def raw.bind.commit_writes_absorbL
              raw.tso.cl.prim_return raw.bind.bind raw.bind.prim_returnL)

lemma returnR:
  assumes "f \<in> raw.tso.closed"
  shows "f \<bind> raw.return = f"
by (simp add: raw.return_alt_def raw.tso.cl.prim_return
   raw.tso.cl.bind_commit_writes_absorbR[of f, simplified raw.tso.closed_conv[OF assms, symmetric]])

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "tso.closed"\<close>

lemma commit_writes:
  shows "raw.commit_writes \<in> raw.tso.closed"
by (rule raw.tso.closed_clI)
   (simp add: raw.tso.cl_def raw.commit_writes.commit_writes raw.bind.prim_returnR
        flip: raw.bind.bind)

lemma bind[intro]:
  fixes f :: "'v raw.tso"
  fixes g :: "'v \<Rightarrow> 'w raw.tso"
  assumes "f \<in> raw.tso.closed"
  assumes "\<And>x. g x \<in> raw.tso.closed"
  shows "f \<bind> g \<in> raw.tso.closed"
by (simp add: assms raw.tso.closed_clI raw.tso.cl.bind flip: raw.tso.closed_conv)

lemma action[intro]:
  shows "raw.action F \<in> raw.tso.closed"
by (simp add: raw.action_def)

lemma guard[intro]:
  shows "raw.guard g \<in> raw.tso.closed"
by (simp add: raw.guard_def raw.tso.closed.action)

lemma MFENCE[intro]:
  shows "raw.MFENCE \<in> raw.tso.closed"
by (simp add: raw.MFENCE_def raw.tso.closed.guard)

lemma parallel[intro]:
  assumes "P \<in> raw.tso.closed"
  assumes "Q \<in> raw.tso.closed"
  shows "raw.parallel P Q \<in> raw.tso.closed"
apply (rule raw.tso.closed_clI)
apply (clarsimp simp: raw.parallel_def raw.tso.cl_def raw.bind.prim_returnR le_fun_def)
apply (subst (2) raw.bind.commit_writes_absorbL[OF raw.tso.closed.MFENCE, symmetric])
apply (simp add: raw.bind_def split_def prog.bind.bind prog.bind.mono[OF order.refl]
                 prog.bind.returnL raw.commit_writes.Nil)
done

lemma vmap[intro]:
  assumes "P \<in> raw.tso.closed"
  shows "raw.vmap vf P \<in> raw.tso.closed"
proof(rule raw.tso.closed_clI)
  have "raw.tso.cl (raw.vmap vf P) \<le> raw.vmap vf (raw.tso.cl P)"
    by (simp add: le_funI raw.tso.cl_def raw.vmap_def raw.bind_def raw.prim_return_def split_def comp_def
                 prog.vmap.eq_return prog.bind.bind prog.bind.returnL)
  then show "raw.tso.cl (raw.vmap vf P) \<le> raw.vmap vf P"
    by (simp flip: raw.tso.closed_conv[OF assms])
qed

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "action"\<close>

lemma bot:
  shows "raw.action \<bottom> = raw.tso.cl \<bottom>"
by (simp add: raw.action_def prog.action.empty bot_fun_def)

lemma monotone:
  shows "mono raw.action"
unfolding raw.action_def
by (fastforce simp: le_fun_def intro: monoI prog.action.mono raw.tso.mono_cl)

lemmas strengthen[strg] = st_monotone[OF raw.action.monotone]
lemmas mono = monotoneD[OF raw.action.monotone]

lemma Sup:
  shows "raw.action (\<Squnion>Fs) = \<Squnion>(raw.action ` Fs) \<squnion> raw.tso.cl \<bottom>" (is "?lhs = ?rhs")
proof -
  have "?rhs = \<Squnion>(raw.tso.cl ` (\<lambda>F wb. prog.action {((v, wb @ ws), s, s') |v s s' ws. (v, ws, s, s') \<in> F wb}) ` Fs) \<squnion> raw.tso.cl \<bottom>"
    by (simp add: raw.action_def image_comp)
  also have "\<dots> = raw.tso.cl (\<Squnion>F\<in>Fs. (\<lambda>wb. prog.action {((v, wb @ ws), s, s') |v s s' ws. (v, ws, s, s') \<in> F wb}))"
    by (simp add: raw.tso.cl_Sup)
  also have "\<dots> = raw.tso.cl (\<lambda>wb. \<Squnion>(prog.action ` (\<lambda>F. {((v, wb @ ws), s, s') |v s s' ws. (v, ws, s, s') \<in> F wb}) ` Fs))"
    by (simp add: Sup_fun_def image_comp)
  also have "\<dots> = ?lhs"
    by (force simp: raw.action_def
         simp flip: prog.action.Sup
             intro: arg_cong[where f=raw.tso.cl] arg_cong[where f=prog.action])
  finally show ?thesis ..
qed

lemma sup:
  shows "raw.action (F \<squnion> G) = raw.action F \<squnion> raw.action G"
using raw.action.Sup[where Fs="{F, G}"]
by (simp add: sup.absorb1 le_supI1 raw.action.mono flip: raw.action.bot)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "guard"\<close>

lemma return_le:
  shows "raw.guard g \<le> raw.return ()"
by (fastforce simp add: raw.guard_def raw.return_def intro: le_funI raw.action.mono)

lemma monotone:
  shows "mono (raw.guard :: (write_buffer \<Rightarrow> heap.t pred) \<Rightarrow> _)"
proof(rule monoI)
  show "raw.guard g \<le> raw.guard h" if "g \<le> h" for g h :: "write_buffer \<Rightarrow> heap.t pred"
    unfolding raw.guard_def Diag_def
    by (blast intro: raw.action.mono le_funI predicate2D[OF that])
qed

lemmas strengthen[strg] = st_monotone[OF raw.guard.monotone]
lemmas mono = monotoneD[OF raw.guard.monotone]

lemma less: \<comment>\<open> Non-triviality; essentially replay @{thm [source] "prog.guard.less"} \<close>
  assumes "g < g'"
  shows "raw.guard g < raw.guard g'"
proof(rule le_neq_trans)
  show "raw.guard g \<le> raw.guard g'"
    by (strengthen ord_to_strengthen(1)[OF order_less_imp_le[OF assms]]) simp
  from assms obtain wb s where "g' wb s" "\<not>g wb s" by (metis leD predicate2I)
  from \<open>\<not>g wb s\<close> have "\<not>\<lblot>trace.T s [] (Some ((), wb))\<rblot> \<le> prog.p2s (raw.guard g wb)"
    by (auto simp: raw.guard_def raw.action_def raw.tso.cl_def raw.bind_def raw.prim_return_def
                   split_def trace.split_all
                   prog.p2s.simps prog.p2s.action prog.p2s.return
                   spec.interference.cl.action spec.interference.cl.return
                   spec.singleton.le_conv spec.singleton.action_le_conv trace.steps'.step_conv
                   suffix_order.antisym_conv
            elim!: spec.singleton.bind_le
            dest!: spec.singleton.raw.commit_writes.wb_suffix)
  moreover
  from \<open>g' wb s\<close> have "\<lblot>trace.T s [] (Some ((), wb))\<rblot> \<le> prog.p2s (raw.guard g' wb)"
    by (force simp: raw.guard_def raw.action_def raw.prim_return_def raw.tso.cl_def raw.bind_def
                    spec.bind.bind spec.singleton.le_conv
                    prog.p2s.bind prog.p2s.action prog.p2s.return
                    spec.interference.cl.action spec.interference.cl.return
             intro: spec.bind.continueI[where xs="[]", simplified] spec.action.stutterI
                    spec.singleton.raw.commit_writes.noop_le)
  ultimately show "raw.guard g \<noteq> raw.guard g'" by metis
qed

setup \<open>Sign.parent_path\<close>

lemma MFENCE_alt_def:
  shows "raw.MFENCE = raw.commit_writes \<then> (\<lambda>wb. prog.action ({((), wb)} \<times> Diag \<langle>wb = []\<rangle>))"
proof -
  have *: "prog.action {x. (\<exists>a. x = (((), wb), a, a)) \<and> wb = []} \<bind> (\<lambda>p. raw.commit_writes (snd p))
         = prog.action ({((), wb)} \<times> Diag (\<lambda>s. wb = [])) \<bind> prog.return"
   for wb
  proof(induct rule: refinement.prog.eqI[case_names l2r r2l])
    case l2r show ?case
      apply (rule refinement.prog.rev_bind)
       apply (rule refinement.prog.action[where Q="\<lambda>v s. snd v = []"];
              simp add: stable_def monotone_def; fail)
      apply (rule refinement.gen_asm; clarsimp simp: raw.commit_writes.Nil)
      apply (rule refinement.sort_of_refl)
       apply (subst refinement.top, simp; fail)
      apply (simp add: spec.idle.p2s_le; fail)
      done
  next
    case r2l show ?case
      apply (rule refinement.prog.rev_bind)
       apply (rule refinement.prog.action[where Q="\<lambda>v s. snd v = []"];
              simp add: stable_def monotone_def; fail)
      apply (rule refinement.gen_asm; clarsimp simp: raw.commit_writes.Nil)
      apply (rule refinement.sort_of_refl)
       apply (subst refinement.top, simp; fail)
      apply (simp add: spec.idle.p2s_le; fail)
      done
  qed
  show ?thesis
    by (simp add: raw.MFENCE_def raw.guard_def raw.action_def raw.tso.cl_def
                  raw.bind.bind raw.bind.prim_returnR)
       (simp add: * raw.bind_def raw.prim_return_def split_def prog.bind.return)
qed

setup \<open>Sign.mandatory_path "MFENCE"\<close>

lemma Nil:
  shows "raw.MFENCE [] = prog.return ((), [])"
by (simp add: raw.MFENCE_alt_def raw.bind_def raw.commit_writes.Nil prog.bind.returnL
        flip: Id_def prog.return_def)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "refinement.raw"\<close>

lemma MFENCE:
  shows "prog.p2s (raw.MFENCE wb) \<le> \<lbrace>P\<rbrace>, A \<tturnstile> prog.p2s (raw.MFENCE wb), \<lbrace>\<lambda>v s. snd v = []\<rbrace>"
apply (simp add: raw.MFENCE_alt_def raw.bind_def split_def)
apply (rule refinement.prog.rev_bind)
 apply (rule refinement.sort_of_refl)
 apply (subst refinement.top, simp; fail)
apply (rule refinement.prog.action; simp add: stable_def monotone_def)
done

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "raw"\<close>

setup \<open>Sign.mandatory_path "bind"\<close>

lemma MFENCEL:
  shows "raw.MFENCE wb \<bind> g = raw.MFENCE wb \<then> g ((), [])" (is "?lhs = ?rhs")
proof(induct rule: refinement.prog.eqI[case_names l2r r2l])
  case l2r show ?case
    apply (rule refinement.prog.rev_bind)
     apply (rule refinement.raw.MFENCE)
    apply (rule refinement.gen_asm; clarsimp)
     apply (rule refinement.sort_of_refl)
     apply (subst refinement.top, simp; fail)
    apply (rule spec.idle.p2s_le)
    done
  case r2l show ?case
    apply (rule refinement.prog.rev_bind)
     apply (rule refinement.raw.MFENCE)
    apply (rule refinement.gen_asm; clarsimp)
     apply (rule refinement.sort_of_refl)
     apply (subst refinement.top, simp; fail)
    apply (rule spec.idle.p2s_le)
    done
qed

lemma MFENCE_return:
  shows "raw.MFENCE wb \<then> prog.return ((), []) = raw.MFENCE wb"
by (simp add: prog.bind.returnR flip: raw.bind.MFENCEL)

lemma MFENCE_MFENCE:
  shows "raw.MFENCE \<then> raw.MFENCE = raw.MFENCE"
by (simp add: raw.bind_def raw.prim_return_def raw.MFENCE.Nil raw.bind.MFENCE_return
              raw.bind.MFENCEL[where g="(\<lambda>(_, y). raw.MFENCE y)"])

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "t2p"\<close>

lemma bot:
  shows "raw.t2p \<bottom> = \<bottom>"
by (simp add: raw.t2p_def prog.bind.botL)

lemma cl_bot:
  shows "raw.t2p (raw.tso.cl \<bottom>) = \<bottom>"
by (simp add: raw.t2p_def raw.tso.cl.bot raw.bind_def raw.commit_writes.Nil
              prog.bind.bind prog.bind.botL prog.bind.returnL)

lemma monotone:
  shows "mono raw.t2p"
by (rule monotoneI) (simp add: raw.t2p_def le_fun_def prog.bind.mono)

lemmas strengthen[strg] = st_monotone[OF raw.t2p.monotone]
lemmas mono = monotoneD[OF raw.t2p.monotone]
lemmas mono2mono[cont_intro, partial_function_mono] = monotone2monotone[OF raw.t2p.monotone, simplified]

lemma Sup:
  shows "raw.t2p (\<Squnion>X) = \<Squnion>(raw.t2p ` X)"
by (simp add: raw.t2p_def prog.bind.SUPL)

lemma sup:
  shows "raw.t2p (P \<squnion> Q) = raw.t2p P \<squnion> raw.t2p Q"
using raw.t2p.Sup[where X="{P, Q}"] by simp

lemma mcont2mcont[cont_intro]:
  fixes P :: "_ \<Rightarrow> _ raw.tso"
  assumes "mcont luba orda Sup (\<le>) F"
  shows "mcont luba orda Sup (\<le>) (\<lambda>x. raw.t2p (F x))"
proof -
  from assms have "mcont luba orda Sup (\<le>) (\<lambda>x. F x [])"
    by (fastforce intro!: mcontI contI monotoneI
                    dest: mcont_contD mcont_monoD
                    simp: le_funD
               simp flip: SUP_apply)
  then show ?thesis
    by (simp add: raw.t2p_def split_def)
qed

lemma return:
  shows "raw.t2p (raw.return v) = prog.return v"
by (simp add: raw.t2p_def raw.return_alt_def raw.tso.cl_def raw.bind_def raw.prim_return_def
              prog.p2s.simps prog.p2s.return
              spec.interference.cl.action spec.interference.cl.return
              spec.bind.bind spec.bind.return
              raw.commit_writes.Nil raw.MFENCE.Nil
        flip: prog.p2s_inject)
   (simp add: spec.rel.wind_bind flip: spec.bind.bind)

lemma MFENCE_bind:
  shows "raw.t2p (raw.MFENCE \<bind> P) = raw.t2p (P ())"
by (simp add: raw.t2p_def raw.bind_def split_def prog.bind.returnL raw.MFENCE.Nil)

lemma bind_return_unit:
  shows "raw.t2p (\<lambda>wb. prog.bind P (\<lambda>_::unit. prog.return ((), []))) = P"
by (simp add: raw.t2p_def raw.bind_def split_def
              prog.bind.bind prog.bind.returnL prog.bind.returnR raw.MFENCE.Nil)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "parallel"\<close>

lemma commute: \<comment>\<open> \<^citet>\<open>\<open>\S5 (3)\<close> in "JagadeesanEtAl:2012"\<close> \<close>
  shows "raw.parallel P Q = raw.parallel Q P"
by (simp add: raw.parallel_def prog.parallel.commute)

lemma assoc: \<comment>\<open> \<^citet>\<open>\<open>\S5 (4)\<close> in "JagadeesanEtAl:2012"\<close> \<close>
  shows "raw.parallel P (raw.parallel Q R) = raw.parallel (raw.parallel P Q) R"
by (simp add: raw.parallel_def raw.t2p.MFENCE_bind raw.t2p.bind_return_unit prog.parallel.assoc)

lemma mono:
  assumes "P \<le> P'"
  assumes "Q \<le> Q'"
  shows "raw.parallel P Q \<le> raw.parallel P' Q'"
unfolding raw.parallel_def
apply (strengthen ord_to_strengthen(1)[OF assms(1)])
apply (strengthen ord_to_strengthen(1)[OF assms(2)])
apply (rule order.refl)
done

lemma botL:
  shows "raw.parallel (raw.tso.cl \<bottom>) f = raw.MFENCE \<then> f \<then> raw.MFENCE \<then> raw.tso.cl \<bottom>"
apply (simp add: raw.parallel_def raw.t2p.cl_bot prog.parallel.bot prog.bind.bind prog.bind.botL)
apply (simp add: raw.t2p_def split_def raw.bind_def prog.bind.bind prog.bind.returnL)
apply (subst (3 4) raw.bind.MFENCEL)
apply (simp add: raw.tso.cl.Nil prog.bind.botL)
done

lemma returnL:
  shows "raw.parallel (raw.return ()) P = raw.MFENCE \<bind> (\<lambda>_. P) \<bind> (\<lambda>_. raw.MFENCE)"
apply (simp add: raw.parallel_def raw.t2p.return prog.parallel.return)
apply (simp add: raw.t2p_def split_def raw.bind_def prog.bind.bind prog.bind.returnL raw.bind.MFENCE_return)
apply (subst (2) raw.bind.MFENCEL)
apply simp
done

lemma SupL_not_empty:
  assumes "\<forall>x\<in>X. x \<in> raw.tso.closed"
  assumes "Q \<in> raw.tso.closed"
  assumes "X \<noteq> {}"
  shows "raw.parallel (\<Squnion>X \<squnion> raw.tso.cl \<bottom>) Q = (\<Squnion>P\<in>X. raw.parallel P Q) \<squnion> raw.tso.cl \<bottom>"
proof -
  from \<open>X \<noteq> {}\<close>
  have "raw.parallel (\<Squnion> X) Q = (\<Squnion>P\<in>X. raw.parallel P Q)"
    by (simp add: raw.parallel_def raw.t2p.Sup raw.t2p.sup
                  prog.parallel.SupL_not_empty prog.parallel.supL prog.bind.SUPL prog.bind.supL)
       (simp add: raw.bind_def split_def fun_eq_iff prog.bind.SUPR_not_empty image_image)
  moreover
  from assms have "raw.tso.cl \<bottom> \<le> (\<Squnion>P\<in>X. raw.parallel P Q)"
    by (force intro: less_eq_Sup raw.tso.least[OF _ raw.tso.closed.parallel])
  moreover note assms
  ultimately show ?thesis
    by (simp add: sup.absorb1 less_eq_Sup raw.tso.least)
qed

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.parent_path\<close>

typedef 'v tso = "raw.tso.closed :: 'v raw.tso set"
morphisms t2p' Abs_tso
by blast

setup_lifting type_definition_tso

instantiation tso :: (type) complete_distrib_lattice
begin

lift_definition bot_tso :: "'v tso" is "raw.tso.cl \<bottom>" ..
lift_definition top_tso :: "'v tso" is "\<top>" ..
lift_definition sup_tso :: "'v tso \<Rightarrow> 'v tso \<Rightarrow> 'v tso" is sup ..
lift_definition inf_tso :: "'v tso \<Rightarrow> 'v tso \<Rightarrow> 'v tso" is inf ..
lift_definition less_eq_tso :: "'v tso \<Rightarrow> 'v tso \<Rightarrow> bool" is less_eq .
lift_definition less_tso :: "'v tso \<Rightarrow> 'v tso \<Rightarrow> bool" is less .
lift_definition Inf_tso :: "'v tso set \<Rightarrow> 'v tso" is Inf ..
lift_definition Sup_tso :: "'v tso set \<Rightarrow> 'v tso" is "\<lambda>X. Sup X \<squnion> raw.tso.cl \<bottom>" ..

instance by (standard; transfer; auto simp: InfI Inf_lower le_supI1 SupI SupE raw.tso.least)

end

setup \<open>Sign.mandatory_path "tso"\<close>

lift_definition bind :: "'v tso \<Rightarrow> ('v \<Rightarrow> 'w tso) \<Rightarrow> 'w tso" is raw.bind ..
lift_definition action :: "(write_buffer \<Rightarrow> ('v \<times> write_buffer \<times> heap.t \<times> heap.t) set) \<Rightarrow> 'v tso" is raw.action ..
lift_definition MFENCE :: "unit tso" is raw.MFENCE ..
lift_definition parallel :: "unit tso \<Rightarrow> unit tso \<Rightarrow> unit tso" is raw.parallel ..
lift_definition vmap :: "('v \<Rightarrow> 'w) \<Rightarrow> 'v tso \<Rightarrow> 'w tso" is raw.vmap ..

lift_definition t2p :: "'v tso \<Rightarrow> (heap.t, 'v) prog" is raw.t2p .

adhoc_overloading
  Monad_Syntax.bind tso.bind
adhoc_overloading
  parallel tso.parallel

definition return :: "'v \<Rightarrow> 'v tso" where
  "return v = tso.action \<langle>{v} \<times> {[]} \<times> Id\<rangle>"

definition guard :: "(write_buffer \<Rightarrow> heap.t pred) \<Rightarrow> unit tso" where
  "guard g = tso.action (\<lambda>wb. {()} \<times> {[]} \<times> Diag (g wb))"

abbreviation (input) read :: "(heap.t \<Rightarrow> 'v) \<Rightarrow> 'v tso" where
  "read f \<equiv> tso.action (\<lambda>wb. {(f (apply_writes wb s), [], s, s) |s. True})"

abbreviation (input) "write" :: "(heap.t \<Rightarrow> heap.write) \<Rightarrow> unit tso" where
  "write f \<equiv> tso.action \<langle>{((), [f s], s, s) |s. True}\<rangle>"

lemma return_alt_def:
  shows "tso.return v = tso.read \<langle>v\<rangle>"
by (auto simp: tso.return_def intro: arg_cong[where f="tso.action"])

declare tso.bind_def[code del]
declare tso.action_def[code del]
declare tso.return_def[code del]
declare tso.MFENCE_def[code del]
declare tso.parallel_def[code del]
declare tso.vmap_def[code del]

setup \<open>Sign.mandatory_path "return"\<close>

lemma transfer[transfer_rule]:
  shows "rel_fun (=) cr_tso raw.return tso.return"
unfolding raw.return_def tso.return_def by transfer_prover

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "action"\<close>

lemma empty:
  shows bot: "tso.action \<bottom> = \<bottom>"
    and "tso.action (\<lambda>_. {}) = \<bottom>"
by (simp_all add: raw.action.bot[transferred, unfolded bot_fun_def] bot_fun_def)

lemmas monotone = raw.action.monotone[transferred]
lemmas strengthen[strg] = st_monotone[OF tso.action.monotone]
lemmas mono = monotoneD[OF tso.action.monotone]
lemmas mono2mono[cont_intro, partial_function_mono] = monotone2monotone[OF tso.action.monotone, simplified]

lemma Sup:
  shows "tso.action (\<Squnion>Fs) = \<Squnion>(tso.action ` Fs)"
by transfer (simp add: raw.action.Sup)

lemmas sup = tso.action.Sup[where Fs="{F, G}" for F G, simplified]

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "bind"\<close>

lemmas if_distrL = if_distrib[where f="\<lambda>f. tso.bind f g" for g] \<comment>\<open> \<^citet>\<open>\<open>\S5 (5)\<close> in "JagadeesanEtAl:2012"\<close> \<close>

lemmas mono = raw.bind.mono[transferred]

lemma strengthen[strg]:
  assumes "st_ord F f f'"
  assumes "\<And>x. st_ord F (g x) (g' x)"
  shows "st_ord F (tso.bind f g) (tso.bind f' g')"
using assms by (cases F; clarsimp intro!: tso.bind.mono)

lemmas mono2mono[cont_intro, partial_function_mono] = raw.bind.mono2mono[transferred]

lemma bind: \<comment>\<open> \<^citet>\<open>\<open>\S5 (2)\<close> in "JagadeesanEtAl:2012"\<close> \<close>
  shows "f \<bind> g \<bind> h = tso.bind f (\<lambda>x. g x \<bind> h)"
by transfer (simp add: raw.bind.bind)

lemma return: \<comment>\<open> \<^citet>\<open>\<open>\S5 (1)\<close> in "JagadeesanEtAl:2012"\<close> \<close>
  shows returnL: "tso.return v \<bind> g = g v"
    and returnR: "f \<bind> tso.return = f"
by (transfer; simp add: raw.bind.returnL raw.bind.returnR)+

lemma botL:
  shows "tso.bind \<bottom> g = \<bottom>"
by transfer (simp add: raw.tso.cl.bot raw.bind.bind raw.bind.botL flip: bot_fun_def)

lemma botR_le:
  shows "tso.bind f \<langle>\<bottom>\<rangle> \<le> f" (is ?thesis1)
    and "tso.bind f \<bottom> \<le> f" (is ?thesis2)
proof -
  show ?thesis1
    by (metis bot.extremum dual_order.refl tso.bind.mono tso.bind.returnR)
  then show ?thesis2
    by (simp add: bot_fun_def)
qed

lemma
  fixes f :: "_ tso"
  fixes f\<^sub>1 :: "_ tso"
  shows supL: "(f\<^sub>1 \<squnion> f\<^sub>2) \<bind> g = (f\<^sub>1 \<bind> g) \<squnion> (f\<^sub>2 \<bind> g)"
    and supR: "f \<bind> (\<lambda>x. g\<^sub>1 x \<squnion> g\<^sub>2 x) = (f \<bind> g\<^sub>1) \<squnion> (f \<bind> g\<^sub>2)"
by (transfer; blast intro: raw.bind.supL raw.bind.supR)+

lemma SUPL:
  fixes X :: "_ set"
  fixes f :: "_ \<Rightarrow> _ tso"
  shows "(\<Squnion>x\<in>X. f x) \<bind> g = (\<Squnion>x\<in>X. f x \<bind> g)"
by transfer
   (simp add: raw.bind.supL raw.bind.SUPL raw.tso.cl.bot raw.bind.bind raw.bind.botL
        flip: bot_fun_def)

lemma SUPR:
  fixes X :: "_ set"
  fixes f :: "_ tso"
  shows "f \<bind> (\<lambda>v. \<Squnion>x\<in>X. g x v) = (\<Squnion>x\<in>X. f \<bind> g x) \<squnion> (f \<bind> \<bottom>)"
unfolding bot_fun_def
by transfer
   (simp add: raw.bind.supR raw.bind.SUPR ac_simps
              sup.absorb2 le_supI1 raw.bind.mono raw.tso.closed.bind raw.tso.least)

lemma SupR:
  fixes X :: "_ set"
  fixes f :: "_ tso"
  shows "f \<then> (\<Squnion>X) = (\<Squnion>x\<in>X. f \<then> x) \<squnion> (f \<bind> \<bottom>)"
by (simp add: tso.bind.SUPR[where g="\<lambda>x v. x", simplified])

lemma SUPR_not_empty:
  fixes f :: "_ tso"
  assumes "X \<noteq> {}"
  shows "f \<bind> (\<lambda>v. \<Squnion>x\<in>X. g x v) = (\<Squnion>x\<in>X. f \<bind> g x)"
using iffD2[OF ex_in_conv assms]
by (subst trans[OF tso.bind.SUPR sup.absorb1]; force intro: SUPI tso.bind.mono)

lemma mcont2mcont[cont_intro]:
  assumes "mcont luba orda Sup (\<le>) f"
  assumes "\<And>v. mcont luba orda Sup (\<le>) (\<lambda>x. g x v)"
  shows "mcont luba orda Sup (\<le>) (\<lambda>x. tso.bind (f x) (g x))"
proof(rule ccpo.mcont2mcont'[OF complete_lattice_ccpo _ _ assms(1)])
  show "mcont Sup (\<le>) Sup (\<le>) (\<lambda>f. tso.bind f (g x))" for x
    by (intro mcontI contI monotoneI) (simp_all add: tso.bind.mono flip: tso.bind.SUPL)
  show "mcont luba orda Sup (\<le>) (\<lambda>x. tso.bind f (g x))" for f
    by (intro mcontI monotoneI contI)
       (simp_all add: mcont_monoD[OF assms(2)] tso.bind.mono
                flip: tso.bind.SUPR_not_empty contD[OF mcont_cont[OF assms(2)]])
qed

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "guard"\<close>

lemma transfer[transfer_rule]:
  shows "rel_fun (=) cr_tso raw.guard tso.guard"
unfolding raw.guard_def tso.guard_def by transfer_prover

lemma bot:
  shows "tso.guard \<bottom> = \<bottom>"
    and "tso.guard (\<lambda>_ _ .False) = \<bottom>"
by (simp_all add: tso.guard_def tso.action.empty)

lemma top:
  shows "tso.guard \<top> = tso.return ()" (is ?thesis1)
    and "tso.guard (\<lambda>_. \<top>) = tso.return ()" (is ?thesis2)
    and "tso.guard (\<lambda>_ _. True) = tso.return ()" (is ?thesis3)
proof -
  show ?thesis1
    by (simp add: tso.guard_def tso.return_def flip: Id_def)
  then show ?thesis2 and ?thesis3
    by (simp_all add: top_fun_def)
qed

lemma return_le:
  shows "tso.guard g \<le> tso.return ()"
by transfer (rule raw.guard.return_le)

lemma monotone:
  shows "mono tso.guard"
by transfer (rule raw.guard.monotone)

lemmas strengthen[strg] = st_monotone[OF tso.guard.monotone]
lemmas mono = monotoneD[OF tso.guard.monotone]
lemmas mono2mono[cont_intro, partial_function_mono] = monotone2monotone[OF tso.guard.monotone, simplified]

lemma less: \<comment>\<open> Non-triviality \<close>
  assumes "g < g'"
  shows "tso.guard g < tso.guard g'"
using assms by transfer (rule raw.guard.less)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "parallel"\<close>

lemma commute: \<comment>\<open> \<^citet>\<open>\<open>\S5 (3)\<close> in "JagadeesanEtAl:2012"\<close> \<close>
  shows "tso.parallel P Q = tso.parallel Q P"
by transfer (rule raw.parallel.commute)

lemma assoc: \<comment>\<open> \<^citet>\<open>\<open>\S5 (4)\<close> in "JagadeesanEtAl:2012"\<close> \<close>
  shows "tso.parallel P (tso.parallel Q R) = tso.parallel (tso.parallel P Q) R"
by transfer (rule raw.parallel.assoc)

lemmas mono = raw.parallel.mono[transferred]

lemma strengthen[strg]:
  assumes "st_ord F P P'"
  assumes "st_ord F Q Q'"
  shows "st_ord F (tso.parallel P Q) (tso.parallel P' Q')"
using assms by (cases F; simp add: tso.parallel.mono)

lemma mono2mono[cont_intro, partial_function_mono]:
  assumes "monotone orda (\<le>) F"
  assumes "monotone orda (\<le>) G"
  shows "monotone orda (\<le>) (\<lambda>f. tso.parallel (F f) (G f))"
using assms by (simp add: monotone_def tso.parallel.mono)

lemma bot:
  shows parallel_botL: "tso.parallel \<bottom> f = tso.MFENCE \<then> f \<then> tso.MFENCE \<bind> \<bottom>" (is ?thesis1)
    and parallel_botR: "tso.parallel f \<bottom> = tso.MFENCE \<then> f \<then> tso.MFENCE \<bind> \<bottom>" (is ?thesis2)
proof -
  show ?thesis1
    unfolding bot_fun_def by transfer (simp add: raw.parallel.botL raw.bind.bind)
  then show ?thesis2
    by (simp add: tso.parallel.commute)
qed

lemma return: \<comment>\<open> \<^citet>\<open>\<open>unnumbered\<close> in "JagadeesanEtAl:2012"\<close> \<close>
  shows returnL: "tso.return () \<parallel> P = tso.MFENCE \<then> P \<then> tso.MFENCE" (is ?thesis1)
    and returnR: "P \<parallel> tso.return () = tso.MFENCE \<then> P \<then> tso.MFENCE" (is ?thesis2)
proof -
  show ?thesis1
    by transfer (rule raw.parallel.returnL)
  then show ?thesis2
    by (simp add: tso.parallel.commute)
qed

lemma Sup_not_empty:
  fixes X :: "unit tso set"
  assumes "X \<noteq> {}"
  shows SupL_not_empty: "\<Squnion>X \<parallel> Q = (\<Squnion>P\<in>X. P \<parallel> Q)" (is "?thesis1 Q")
    and SupR_not_empty: "P \<parallel> \<Squnion>X = (\<Squnion>Q\<in>X. P \<parallel> Q)" (is ?thesis2)
proof -
  from assms show "?thesis1 Q" for Q
    by transfer (rule raw.parallel.SupL_not_empty)
  then show ?thesis2
    by (simp add: tso.parallel.commute)
qed

lemma sup:
  fixes P :: "unit tso"
  shows supL: "P \<squnion> Q \<parallel> R = (P \<parallel> R) \<squnion> (Q \<parallel> R)"
    and supR: "P \<parallel> Q \<squnion> R = (P \<parallel> Q) \<squnion> (P \<parallel> R)"
using tso.parallel.SupL_not_empty[where X="{P, Q}"] tso.parallel.SupR_not_empty[where X="{Q, R}"]
by simp_all

lemma mcont2mcont[cont_intro]:
  assumes "mcont luba orda Sup (\<le>) P"
  assumes "mcont luba orda Sup (\<le>) Q"
  shows "mcont luba orda Sup (\<le>) (\<lambda>x. tso.parallel (P x) (Q x))"
proof(rule ccpo.mcont2mcont'[OF complete_lattice_ccpo _ _ assms(1)])
  show "mcont Sup (\<le>) Sup (\<le>) (\<lambda>y. tso.parallel y (Q x))" for x
    by (intro mcontI contI monotoneI) (simp_all add: tso.parallel.mono tso.parallel.SupL_not_empty)
  show "mcont luba orda Sup (\<le>) (\<lambda>x. tso.parallel y (Q x))" for y
    by (simp add: mcontI monotoneI contI mcont_monoD[OF assms(2)]
                  spec.parallel.mono mcont_contD[OF assms(2)] tso.parallel.SupR_not_empty image_image)
qed

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "bind"\<close>

lemmas MFENCE_MFENCE = raw.bind.MFENCE_MFENCE[transferred]

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "t2p'"\<close>

lemma monotone:
  shows "mono (\<lambda>t. t2p' t wb)"
by (simp add: le_fun_def less_eq_tso.rep_eq monotone_def)

lemmas strengthen[strg] = st_monotone[OF tso.t2p'.monotone]
lemmas mono = monotoneD[OF tso.t2p'.monotone]

lemmas action = tso.action.rep_eq
lemma return:
  shows "t2p' (tso.return v) = raw.return v"
by transfer simp

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.parent_path\<close>


paragraph\<open> Combinators \<close>

setup \<open>Sign.mandatory_path "tso"\<close>

abbreviation guardM :: "bool \<Rightarrow> unit tso" where
  "guardM b \<equiv> if b then \<bottom> else tso.return ()"

abbreviation unlessM :: "bool \<Rightarrow> unit tso \<Rightarrow> unit tso" where
  "unlessM b c \<equiv> if b then tso.return () else c"

abbreviation whenM :: "bool \<Rightarrow> unit tso \<Rightarrow> unit tso" where
  "whenM b c \<equiv> if b then c else tso.return ()"

definition app :: "('a \<Rightarrow> unit tso) \<Rightarrow> 'a list \<Rightarrow> unit tso" where \<comment>\<open> Haskell's \<open>mapM_\<close> \<close>
  "app f xs = foldr (\<lambda>x m. f x \<then> m) xs (tso.return ())"

primrec fold_mapM :: "('a \<Rightarrow> 'b tso) \<Rightarrow> 'a list \<Rightarrow> 'b list tso" where
  "fold_mapM f [] = tso.return []"
| "fold_mapM f (x # xs) = do {
     y \<leftarrow> f x;
     ys \<leftarrow> fold_mapM f xs;
     tso.return (y # ys)
   }"

\<comment>\<open> \<^citet>\<open>\<open>\S5 (6) is \<open>tso.while.simps\<close>\<close> in "JagadeesanEtAl:2012"\<close> \<close>
partial_function (lfp) while :: "('k \<Rightarrow> ('k + 'v) tso) \<Rightarrow> 'k \<Rightarrow> 'v tso" where
  "while c k = c k \<bind> (\<lambda>rv. case rv of Inl k' \<Rightarrow> while c k' | Inr v \<Rightarrow> tso.return v)"

abbreviation (input) while' :: "((unit + 'v) tso) \<Rightarrow> 'v tso" where
  "while' c \<equiv> tso.while \<langle>c\<rangle> ()"

definition raise :: "String.literal \<Rightarrow> 'v tso" where
  "raise s = \<bottom>"

definition assert :: "bool \<Rightarrow> unit tso" where
  "assert P = (if P then tso.return () else tso.raise STR ''assert'')"

declare tso.raise_def[code del]

setup \<open>Sign.mandatory_path "fold_mapM"\<close>

lemma bot:
  shows "tso.fold_mapM \<bottom> = (\<lambda>xs. case xs of [] \<Rightarrow> tso.return [] | _ \<Rightarrow> \<bottom>)"
by (simp add: fun_eq_iff tso.bind.botL split: list.split)

lemma append:
  shows "tso.fold_mapM f (xs @ ys) = tso.fold_mapM f xs \<bind> (\<lambda>xs. tso.fold_mapM f ys \<bind> (\<lambda>ys. tso.return (xs @ ys)))"
by (induct xs) (simp_all add: tso.bind.bind tso.bind.returnL tso.bind.returnR)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "app"\<close>

lemma bot:
  shows "tso.app \<bottom> = (\<lambda>xs. case xs of [] \<Rightarrow> tso.return () | _ \<Rightarrow> \<bottom>)"
    and "tso.app (\<lambda>_. \<bottom>) = (\<lambda>xs. case xs of [] \<Rightarrow> tso.return () | _ \<Rightarrow> \<bottom>)"
by (simp_all add: fun_eq_iff tso.app_def tso.bind.botL split: list.split)

lemma Nil:
  shows "tso.app f [] = tso.return ()"
by (simp add: tso.app_def)

lemma Cons:
  shows "tso.app f (x # xs) = f x \<then> tso.app f xs"
by (simp add: tso.app_def)

lemmas simps =
  tso.app.bot
  tso.app.Nil
  tso.app.Cons

lemma append:
  shows "tso.app f (xs @ ys) = tso.app f xs \<then> tso.app f ys"
by (induct xs arbitrary: ys) (simp_all add: tso.app.simps tso.bind.returnL tso.bind.bind)

lemma monotone:
  shows "mono (\<lambda>f. tso.app f xs)"
by (induct xs) (simp_all add: tso.app.simps le_fun_def monotone_on_def tso.bind.mono)

lemmas strengthen[strg] = st_monotone[OF tso.app.monotone]
lemmas mono = monotoneD[OF tso.app.monotone]
lemmas mono2mono[cont_intro, partial_function_mono] = monotone2monotone[OF tso.app.monotone, simplified, of orda P for orda P]

lemma Sup_le:
  shows "(\<Squnion>f\<in>X. tso.app f xs) \<le> tso.app (\<Squnion>X) xs"
by (simp add: SUP_le_iff SupI tso.app.mono)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.parent_path\<close>


subsection\<open> References\label{sec:tso-refs} \<close>

text\<open>

Observe that allocation is global in this model. We allow the memory location to have an arbitrary
value and enqueue the initialising write in the TSO buffer.

\<close>

setup \<open>Sign.mandatory_path "tso.Ref"\<close>

definition ref :: "'a::heap.rep \<Rightarrow> 'a ref tso" where
  "ref v = tso.action (\<lambda>wb. {(r, [heap.Write (ref.addr_of r) 0 (heap.rep.to v)], s, s')
                            |r s s' v'. (r, s') \<in> Ref.alloc v' s})"

definition lookup :: "'a::heap.rep ref \<Rightarrow> 'a tso" ("!_" 61) where
  "lookup r = tso.read (Ref.get r)"

definition update :: "'a ref \<Rightarrow> 'a::heap.rep \<Rightarrow> unit tso" ("_ := _" 62) where
  "update r v = tso.write \<langle>heap.Write (ref.addr_of r) 0 (heap.rep.to v)\<rangle>"

declare tso.Ref.ref_def[code del]
declare tso.Ref.lookup_def[code del]
declare tso.Ref.update_def[code del]

setup \<open>Sign.parent_path\<close>


subsection\<open> Inhabitation\label{sec:tso-inhabitation} \<close>

text\<open> In order to obtain compositional rules we need to make the write buffer explicit. \<close>

setup \<open>Sign.mandatory_path "tso"\<close>

definition t2s :: "write_buffer \<Rightarrow> 'v tso \<Rightarrow> (sequential, heap.t, 'v \<times> write_buffer) spec" where
  "t2s wb P = prog.p2s (tso.t2p' P wb)"

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "spec.singleton.tso"\<close>

lemma t2s_commit:
  assumes "\<lblot>heap.apply_write w s, xs, v\<rblot> \<le> tso.t2s wb f"
  shows "\<lblot>s, (self, heap.apply_write w s) # xs, v\<rblot> \<le> tso.t2s (w # wb) f"
unfolding tso.t2s_def
by (subst raw.tso.closed_conv[OF tso.t2p'])
   (fastforce simp: prog.p2s.action simp add: prog.p2s.simps simp flip: tso.t2s_def
             intro: order.trans[OF _ prog.p2s.mono[OF raw.tso.cl.commit]]
                    spec.bind.continueI[where xs="[(self, heap.apply_write w s)]" and v="((), [])", simplified, OF _ assms]
                    order.trans[OF spec.action.stepI spec.interference.expansive])

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "spec.idle.tso"\<close>

lemma t2s_le:
  shows "spec.idle \<le> tso.t2s wb P"
by (simp add: tso.t2s_def spec.idle.p2s_le)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "spec.t2s"\<close>

lemmas minimal[iff] = order.trans[OF spec.idle.minimal_le spec.idle.tso.t2s_le]

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "spec.interference.tso"\<close>

lemma t2s_le:
  shows "spec.rel ({env} \<times> UNIV) \<bind> (\<lambda>_::unit. tso.t2s wb P) \<le> tso.t2s wb P"
by (simp add: tso.t2s_def prog.p2s.interference_wind_bind)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "prog.p2s"\<close>

lemma t2p[prog.p2s.simps]:
  shows "prog.p2s (tso.t2p P)
       = tso.t2s [] P \<bind> (\<lambda>vwb. prog.p2s (raw.MFENCE (snd vwb) \<then> prog.return (fst vwb)))"
by transfer (simp add: tso.t2p_def tso.t2s_def raw.t2p_def prog.p2s.simps split_def)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "tso.t2s"\<close>

lemma bind:
  shows "tso.t2s wb (f \<bind> g) = tso.t2s wb f \<bind> (\<lambda>x. tso.t2s (snd x) (g (fst x)))"
unfolding tso.t2s_def by transfer (simp add: raw.bind_def split_def prog.p2s.simps)

lemma parallel:
  shows "tso.t2s [] (P \<parallel> Q) = prog.p2s ((tso.t2p P \<parallel> tso.t2p Q) \<then> prog.return ((), []))"
unfolding tso.t2s_def
by transfer (simp add: raw.parallel_def raw.bind_def raw.MFENCE.Nil prog.bind.returnL)

lemma return:
  shows "tso.t2s [] (tso.return v) = prog.p2s (prog.return (v, []))"
unfolding tso.t2s_def
by transfer
   (simp add: raw.return_alt_def raw.tso.cl.Nil raw.prim_return_def prog.bind.returnL raw.commit_writes.Nil)

setup \<open>Sign.parent_path\<close>


paragraph\<open> Inhabitation rules. \<close>

setup \<open>Sign.mandatory_path "inhabits.tso"\<close>

lemma bind:
  assumes "tso.t2s wb f -s, xs\<rightarrow> tso.t2s wb' f'"
  shows "tso.t2s wb (f \<bind> g) -s, xs\<rightarrow> tso.t2s wb' (f' \<bind> g)"
by (simp add: tso.t2s.bind inhabits.spec.bind assms)

lemma commit:
  shows "tso.t2s (w # wb) f -s, [(self, heap.apply_write w s)]\<rightarrow> tso.t2s wb f"
by (clarsimp simp: inhabits_def spec.bind.singletonL spec.term.none.singleton trace.split_all
                   spec.singleton.tso.t2s_commit)

setup \<open>Sign.mandatory_path "Ref"\<close>

lemma ref:
  fixes r :: "'a::heap.rep ref"
  fixes s :: "heap.t"
  fixes v :: "'a"
  fixes v' :: "'a"
  assumes "\<not>heap.present r s"
  shows "tso.t2s wb (tso.Ref.ref v)
          -s, [(self, Ref.set r v' s)]\<rightarrow>
            tso.t2s (wb @ [heap.Write (ref.addr_of r) 0 (heap.rep.to v)]) (tso.return r)" (is "?lhs -s, ?step\<rightarrow> ?rhs")
proof -
  have rhs: "?rhs = prog.p2s (raw.commit_writes (wb @ [heap.Write (ref.addr_of r) 0 (heap.rep.to v)])
                          \<bind> (\<lambda>v. raw.prim_return r (snd v)))"
    apply (simp add: tso.t2s_def tso.t2p'.return raw.return_def raw.action_def)
    apply (subst (1) prog.return.cong)
    apply (simp_all add: image_iff split_def Sup_fst fst_image raw.tso.cl.prim_return raw.bind_def
                   flip: raw.prim_return_def)
    done
  note * = order.trans[OF _ spec.bind.mono[OF prog.p2s.mono[OF
               raw.commit_writes.return_le[unfolded le_fun_def raw.prim_return_def, rule_format]]
             order.refl]]
  note ** = spec.bind.mono[OF spec.action.stepI[where a=self and s=s
               and v="(r, wb @ [heap.Write (ref.addr_of r) 0 (heap.rep.to v)])"
               and s'="Ref.set r v' s"
               and w="Some (r, wb @ [heap.Write (ref.addr_of r) 0 (heap.rep.to v)])"]
             order.refl]
  have lhs: "\<lblot>s, [(self, Ref.set r v' s)], Some (r, wb @ [heap.Write (ref.addr_of r) 0 (heap.rep.to v)])\<rblot>
               \<bind> (\<lambda>v. prog.p2s (raw.commit_writes (snd v))
                 \<bind> (\<lambda>x. prog.p2s (raw.prim_return (fst v) (snd x))))
          \<le> ?lhs"
    apply (simp add: tso.Ref.ref_def tso.t2s_def split_def tso.t2p'.action
                     raw.action_def raw.tso.cl_def raw.bind_def prog.p2s.bind prog.bind.bind)
    apply (rule * )
    apply (simp flip: prog.p2s.bind)
    apply (force simp: assms Ref.alloc_def prog.p2s.simps prog.p2s.action prog.bind.returnL 
                intro: ** order.trans[OF _ spec.bind.mono[OF spec.interference.expansive order.refl]])
    done
  show ?thesis
    unfolding inhabits_def
    by (rule order.trans[OF _ lhs])
       (simp add: rhs prog.p2s.simps spec.bind.singletonL spec.term.none.singleton)
qed

lemma lookup:
  fixes r :: "'a::heap.rep ref"
  shows "tso.t2s wb (!r) -s, []\<rightarrow> tso.t2s wb (tso.return (Ref.get r (apply_writes wb s)))"
apply (clarsimp simp: tso.Ref.lookup_def  inhabits_def trace.split_all
                      tso.t2s_def tso.t2p'.action tso.t2p'.return
                      raw.action_def raw.return_alt_def raw.tso.cl.prim_return
                      spec.bind.singletonL spec.term.none.singleton)
apply (clarsimp simp: raw.tso.cl_def raw.bind_def split_def prog.bind.bind)
apply (rule order.trans[OF _ prog.p2s.mono[OF
  prog.bind.mono[OF raw.commit_writes.return_le[unfolded raw.prim_return_def le_fun_def, rule_format]
                    order.refl]]])
apply (force simp: prog.bind.return prog.p2s.bind prog.p2s.action
     intro: order.trans[OF spec.bind.continueI[where xs="[]", simplified, OF spec.action.stutterI]
  spec.bind.mono[OF spec.interference.expansive order.refl]])
done

lemma update:
  fixes r :: "'a::heap.rep ref"
  shows "tso.t2s wb (r := v)
          -s, []\<rightarrow>
            tso.t2s (wb @ [heap.Write (ref.addr_of r) 0 (heap.rep.to v)]) (tso.return ())"
proof -
  have *: "(\<lambda>p. raw.prim_return () (snd p)) = prog.return" (* ouch *)
    by (simp add: raw.prim_return_def fun_eq_iff)
  have "raw.tso.cl (\<lambda>wb. prog.return ((), wb)) (wb @ [heap.Write (ref.addr_of r) 0 (heap.rep.to v)])
     \<le> raw.tso.cl (\<lambda>wb. prog.action {(((), wb @ [heap.Write (ref.addr_of r) 0 (heap.rep.to v)]), s, s) |s. True}) wb"
    \<comment>\<open> LHS \<close>
    apply (simp add: raw.tso.cl_def raw.bind.prim_returnR raw.commit_writes.commit_writes
               flip: raw.prim_return_def
               cong: order.assms_cong)
    \<comment>\<open> RHS \<close>
    apply (simp add: * raw.tso.cl_def raw.bind_def split_def prog.bind.bind)
    apply (rule order.trans[OF _
            prog.bind.mono[OF raw.commit_writes.return_le[unfolded raw.prim_return_def le_fun_def, rule_format]
                              order.refl]])
    apply (simp add: prog.bind.returnL flip: prog.p2s.bind)
    apply (subst (1) prog.return.cong, force, force)
    apply (simp add: split_def Sup_fst fst_image prog.bind.return)
    done
  from prog.p2s.mono[OF this] show ?thesis
    by (fastforce simp: tso.Ref.update_def raw.action_def tso.t2s_def inhabits_def
                        tso.t2p'.return tso.t2p'.action
                        raw.return_alt_def raw.prim_return_def
                        spec.bind.singletonL spec.term.none.singleton)
qed

setup \<open>Sign.parent_path\<close>

lemmas bind' = inhabits.trans[OF inhabits.tso.bind]
lemmas commit' = inhabits.trans[OF inhabits.tso.commit]

setup \<open>Sign.parent_path\<close>
(*<*)

end
(*>*)
