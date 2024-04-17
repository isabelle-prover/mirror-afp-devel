(*<*)
theory BFS
imports
  "Assume_Guarantee"
begin

(*>*)
section\<open> Example: data refinement (search)\label{sec:ex-data_refinement} \<close>

text\<open>

We show a very simple example of data refinement: implementing sets with functional queues
for breadth-first search (BFS). The objective here is to transfer a simple correctness property
proven on the abstract level to the concrete level.

Observations:
 \<^item> there is no concurrency in the BFS: this is just about data refinement
  \<^item> however arbitrary interference is allowed
 \<^item> the abstract level does not require the implementation of the pending set to make progress
 \<^item> the concrete level does not require a representation invariant
 \<^item> depth optimality is not shown

References:
 \<^item> queue ADT: \<^file>\<open>$ISABELLE_HOME/src/Doc/Codegen/Introduction.thy\<close>
 \<^item> BFS verification:
  \<^item> J. C. Filliâtre \<^url>\<open>http://toccata.lri.fr/gallery/vstte12_bfs.en.html\<close>
  \<^item> \<^file>\<open>$AFP/Refine_Monadic/examples/Breadth_First_Search.thy\<close>
  \<^item> our model is quite different

\<close>

setup \<open>Sign.mandatory_path "pending"\<close>

record ('a, 's) interface =
  init :: "('s, unit) prog"
  enq :: "'a \<Rightarrow> ('s, unit) prog"
  deq :: "('s, 'a option) prog"

type_synonym 'a abstract = "'a set"

definition abstract :: "('a, 'a pending.abstract \<times> 's) pending.interface" where
  "abstract =
    \<lparr> pending.interface.init = prog.write (map_prod \<langle>{}\<rangle> id)
    , pending.interface.enq = \<lambda>x. prog.write (map_prod (insert x) id)
    , pending.interface.deq = prog.action ({(None, s, s) |s. fst s = {}}
                                         \<union> {(Some x, (insert x X, s), (X, s)) |X s x. True})
    \<rparr>"

type_synonym 'a concrete = "'a list \<times> 'a list" \<comment>\<open> a queue \<close>

fun cdeq_update :: "'a pending.concrete \<times> 's \<Rightarrow> 'a option \<times> 'a pending.concrete \<times> 's" where
  "cdeq_update (([], []), s) = (None, (([], []), s))"
| "cdeq_update ((xs, []), s) = cdeq_update (([], rev xs), s)"
| "cdeq_update ((xs, y # ys), s) = (Some y, ((xs, ys), s))"

definition concrete :: "('a, 'a pending.concrete \<times> 's) pending.interface" where
  "concrete =
    \<lparr> pending.interface.init = prog.write (map_prod \<langle>([], [])\<rangle> id)
    , pending.interface.enq = \<lambda>x. prog.write (map_prod (map_prod ((#) x) id) id)
    , pending.interface.deq = prog.det_action pending.cdeq_update
    \<rparr>"

abbreviation absfn' :: "'a pending.concrete \<Rightarrow> 'a list" where \<comment>\<open> queue as a list \<close>
  "absfn' s \<equiv> snd s @ rev (fst s)"

definition absfn :: "'a pending.concrete \<Rightarrow> 'a pending.abstract" where
  "absfn s = set (pending.absfn' s)"

setup \<open>Sign.mandatory_path "ag"\<close>

lemma init:
  fixes Q :: "unit \<Rightarrow> 'a pending.abstract \<times> 's \<Rightarrow> bool"
  fixes A :: "'s rel"
  assumes "stable (Id \<times>\<^sub>R A) (Q ())"
  shows "prog.p2s (pending.init pending.abstract) \<le> \<lbrace>\<lambda>s. Q () ({}, snd s)\<rbrace>, Id \<times>\<^sub>R A \<turnstile> UNIV \<times>\<^sub>R Id, \<lbrace>Q\<rbrace>"
using assms by (auto intro: ag.prog.action simp: pending.abstract_def stable_def monotone_def)

lemma enq:
  fixes x :: 'a
  fixes Q :: "unit \<Rightarrow> 'a pending.abstract \<times> 's \<Rightarrow> bool"
  fixes A :: "'s rel"
  assumes "stable (Id \<times>\<^sub>R A) (Q ())"
  shows "prog.p2s (pending.enq pending.abstract x) \<le> \<lbrace>\<lambda>s. Q () (insert x (fst s), snd s)\<rbrace>, Id \<times>\<^sub>R A \<turnstile> UNIV \<times>\<^sub>R Id, \<lbrace>Q\<rbrace>"
using assms by (auto intro: ag.prog.action simp: pending.abstract_def stable_def monotone_def)

lemma deq:
  fixes Q :: "'a option \<Rightarrow> 'a pending.abstract \<times> 's \<Rightarrow> bool"
  fixes A :: "'s rel"
  assumes "\<And>v. stable (Id \<times>\<^sub>R A) (Q v)"
  shows "prog.p2s (pending.deq pending.abstract) \<le> \<lbrace>\<lambda>s. if fst s = {} then Q None s else (\<forall>x X. fst s = insert x X \<longrightarrow> Q (Some x) (X, snd s))\<rbrace>, Id \<times>\<^sub>R A \<turnstile> UNIV \<times>\<^sub>R Id, \<lbrace>Q\<rbrace>"
unfolding pending.abstract_def pending.interface.simps
by (rule ag.prog.action)
   (use assms in \<open>auto simp: stable_def monotone_def le_bool_def split: if_split_asm\<close>)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "set"\<close>

record ('a, 's) interface =
  init :: "('s, unit) prog"
  ins :: "'a \<Rightarrow> ('s, unit) prog"
  mem :: "'a \<Rightarrow> ('s, bool) prog"

type_synonym 'a abstract = "'a list" \<comment>\<open> model finite sets \<close>

definition abstract :: "('a, 's \<times> 'a set.abstract \<times> 't) set.interface" where
  "abstract =
    \<lparr> set.interface.init = prog.write (map_prod id (map_prod \<langle>[]\<rangle> id))
    , set.interface.ins = \<lambda>x. prog.write (map_prod id (map_prod ((#) x) id))
    , set.interface.mem = \<lambda>x. prog.read (\<lambda>s. x \<in> set (fst (snd s)))
    \<rparr>"

setup \<open>Sign.mandatory_path "ag"\<close>

lemma init:
  fixes Q :: "unit \<Rightarrow> 's \<times> 'a set.abstract \<times> 't \<Rightarrow> bool"
  fixes A :: "'s rel"
  assumes "stable (A \<times>\<^sub>R Id \<times>\<^sub>R B) (Q ())"
  shows "prog.p2s (set.init set.abstract) \<le> \<lbrace>\<lambda>s. Q () (fst s, [], snd (snd s))\<rbrace>, A \<times>\<^sub>R Id \<times>\<^sub>R B \<turnstile> Id \<times>\<^sub>R UNIV \<times>\<^sub>R Id, \<lbrace>Q\<rbrace>"
using assms by (auto intro: ag.prog.action simp: set.abstract_def stable_def monotone_def)

lemma ins:
  fixes x :: 'a
  fixes Q :: "unit \<Rightarrow> 's \<times> 'a set.abstract \<times> 't \<Rightarrow> bool"
  fixes A :: "'s rel"
  assumes "stable (A \<times>\<^sub>R Id \<times>\<^sub>R B) (Q ())"
  shows "prog.p2s (set.ins set.abstract x) \<le> \<lbrace>\<lambda>s. Q () (fst s, x # fst (snd s), snd (snd s))\<rbrace>, A \<times>\<^sub>R Id \<times>\<^sub>R B \<turnstile> Id \<times>\<^sub>R UNIV \<times>\<^sub>R Id, \<lbrace>Q\<rbrace>"
using assms by (auto intro: ag.prog.action simp: set.abstract_def stable_def monotone_def)

lemma mem:
  fixes Q :: "bool \<Rightarrow> 's \<times> 'a set.abstract \<times> 't \<Rightarrow> bool"
  assumes "\<And>v. stable (A \<times>\<^sub>R Id \<times>\<^sub>R B) (Q v)"
  shows "prog.p2s (set.mem set.abstract x) \<le> \<lbrace>\<lambda>s. Q (x \<in> set (fst (snd s))) s\<rbrace>, A \<times>\<^sub>R Id \<times>\<^sub>R B \<turnstile> Id \<times>\<^sub>R UNIV \<times>\<^sub>R Id, \<lbrace>Q\<rbrace>"
using assms by (auto intro: ag.prog.action simp: set.abstract_def stable_def monotone_def)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.parent_path\<close>

context
  fixes pending :: "('a, 'p \<times> 'a set.abstract \<times> 's) pending.interface"
  fixes f :: "'a \<Rightarrow> 'a list"
begin

definition loop :: "'a pred \<Rightarrow> ('p \<times> 'a set.abstract \<times> 's, 'a option) prog" where
  "loop p =
    prog.while (\<lambda>_.
      do { aopt \<leftarrow> pending.deq pending
         ; case aopt of
             None \<Rightarrow> prog.return (Inr None)
           | Some x \<Rightarrow>
               if p x
               then prog.return (Inr (Some x))
               else do { prog.app (\<lambda>y. do { b \<leftarrow> set.mem set.abstract y;
                                            prog.unlessM b (do { set.ins set.abstract y
                                                               ; pending.enq pending y }) })
                                  (f x)
                       ; prog.return (Inl ())
                       }
       }) ()"

definition main :: "'a pred \<Rightarrow> 'a \<Rightarrow> ('p \<times> 'a set.abstract \<times> 's, 'a option) prog" where
  "main p x =
    do {
      set.init set.abstract
    ; pending.init pending
    ; set.ins set.abstract x
    ; pending.enq pending x
    ; loop p
    }"

definition search :: "'a pred \<Rightarrow> 'a \<Rightarrow> ('s, 'a option) prog" where
  "search p x = prog.local (prog.local (main p x))"

end

abbreviation (input) "aloop \<equiv> loop pending.abstract"
abbreviation (input) "amain \<equiv> main pending.abstract"
abbreviation (input) "asearch \<equiv> search pending.abstract"
abbreviation (input) "bfs \<equiv> search pending.concrete"

lemma
  shows pending_g: "UNIV \<times>\<^sub>R Id \<subseteq> UNIV \<times>\<^sub>R UNIV \<times>\<^sub>R Id"
    and set_g: "Id \<times>\<^sub>R UNIV \<times>\<^sub>R Id \<subseteq> UNIV \<times>\<^sub>R UNIV \<times>\<^sub>R Id"
by fastforce+

context
  fixes f :: "'a \<Rightarrow> 'a list"
  fixes P :: "'a pred"
  fixes x\<^sub>0 :: "'a"
begin

abbreviation (input) step :: "'a rel" where
  "step \<equiv> {(x, y). y \<in> set (f x)}"

abbreviation (input) path :: "'a rel" where
  "path \<equiv> step\<^sup>*"

definition aloop_invP :: "'a pending.abstract \<Rightarrow> 'a set.abstract \<Rightarrow> bool" where
  "aloop_invP q v \<longleftrightarrow>
        q \<subseteq> set v
      \<and> set v \<subseteq> path `` {x\<^sub>0}
      \<and> set v \<inter> Collect P \<subseteq> q
      \<and> x\<^sub>0 \<in> set v"

definition vclosureP :: "'a \<Rightarrow> 'a pending.abstract \<Rightarrow> 'a set.abstract \<Rightarrow> bool" where
  "vclosureP x q v \<longleftrightarrow> (x \<in> set v - q \<longrightarrow> step `` {x} \<subseteq> set v)"

definition search_postP :: "'a option \<Rightarrow> bool" where
  "search_postP rv = (case rv of
      None \<Rightarrow> finite (path `` {x\<^sub>0}) \<and> (path `` {x\<^sub>0} \<inter> Collect P = {})
    | Some y \<Rightarrow> (x\<^sub>0, y) \<in> path \<and> P y)"

abbreviation "aloop_inv s \<equiv> aloop_invP (fst s) (fst (snd s))"
abbreviation "vclosure x s \<equiv> vclosureP x (fst s) (fst (snd s))"
abbreviation "search_post rv \<equiv> \<langle>search_postP rv\<rangle>"

lemma vclosureP_closed:
  assumes "set v \<subseteq> path `` {x\<^sub>0}"
  assumes "\<forall>y. vclosureP y {} v"
  assumes "x\<^sub>0 \<in> set v"
  shows "path `` {x\<^sub>0} = set v"
proof -
  have "y \<in> set v" if "(x\<^sub>0, y) \<in> path" for y
    using that assms(2,3) by induct (auto simp: vclosureP_def)
  with assms(1) show ?thesis
    by fast
qed

lemma vclosureP_app:
  assumes "\<forall>y. x \<noteq> y \<longrightarrow> local.vclosureP y q v"
  assumes "set (f x) \<subseteq> set v"
  shows "vclosureP y q v"
using assms by (fastforce simp: vclosureP_def)

lemma vclosureP_init:
  shows "vclosureP x {x\<^sub>0} [x\<^sub>0]"
by (simp add: vclosureP_def)

lemma vclosureP_step:
  assumes "\<forall>z. x \<noteq> z \<longrightarrow> vclosureP z q v"
  assumes "x \<noteq> z"
  shows "vclosureP z (insert y q) (y # v)"
using assms by (fastforce simp: vclosureP_def)

lemma vclosureP_dequeue:
  assumes "\<forall>z. vclosureP z (insert x q) v"
  assumes "x \<noteq> z"
  shows "vclosureP z q v"
using assms by (fastforce simp: vclosureP_def)

lemma aloop_invPD:
  assumes "aloop_invP q v"
  assumes "x \<in> q"
  shows "(x\<^sub>0, x) \<in> path"
using assms by (auto simp: aloop_invP_def)

lemma aloop_invP_init:
  shows "aloop_invP {x\<^sub>0} [x\<^sub>0]"
by (simp add: aloop_invP_def)

lemma aloop_invP_step:
  assumes "aloop_invP q v"
  assumes "(x\<^sub>0, x) \<in> path"
  assumes "y \<in> set (f x) - set v"
  shows "aloop_invP (insert y q) (y # v)"
using assms by (auto simp: aloop_invP_def elim: rtrancl_into_rtrancl)

lemma aloop_invP_dequeue:
  assumes "aloop_invP (insert x q) v"
  assumes "\<not> P x"
  shows "aloop_invP q v"
using assms by (auto simp: aloop_invP_def)

lemma search_postcond_None:
  assumes "aloop_invP {} v"
  assumes "\<forall>y. vclosureP y {} v"
  shows "search_postP None"
using assms by (auto simp: search_postP_def aloop_invP_def dest: vclosureP_closed)

lemma search_postcond_Some:
  assumes "aloop_invP q v"
  assumes "x \<in> q"
  assumes "P x"
  shows "search_postP (Some x)"
using assms by (auto simp: search_postP_def aloop_invP_def)

lemmas stable_simps =
  prod.sel
  split_def
  sum.simps

lemma ag_aloop:
  shows "prog.p2s (aloop f P) \<le> \<lbrace>aloop_inv \<^bold>\<and> (\<^bold>\<forall>x. vclosure x)\<rbrace>, Id \<times>\<^sub>R Id \<times>\<^sub>R UNIV \<turnstile> UNIV \<times>\<^sub>R UNIV \<times>\<^sub>R Id, \<lbrace>search_post\<rbrace>"
unfolding loop_def
apply (rule ag.prog.while[OF _ _ stable.Id_fst_fst_snd])
 apply (rule ag.prog.bind)
  apply (rule ag.prog.case_option)
   apply (rule ag.prog.return)
   apply ((simp only: stable_simps)?; (rule stable.intro)+; fail)
  apply (rule ag.prog.if)
   apply (rule ag.prog.return)
   apply ((simp only: stable_simps)?; (rule stable.intro)+; fail)
  apply (rule ag.prog.bind)
   apply (rule ag.prog.return)
   apply ((simp only: stable_simps)?; (rule stable.intro)+; fail)
  apply (rename_tac x)
  apply (rule_tac Q="\<lambda>_. aloop_inv \<^bold>\<and> (\<^bold>\<forall>y. \<langle>x \<noteq> y\<rangle> \<^bold>\<longrightarrow> vclosure y) \<^bold>\<and> (\<lambda>s. set (f x) \<subseteq> set (fst (snd s)) \<and> (x\<^sub>0, x) \<in> path)" in ag.post_imp)
   apply (force elim: vclosureP_app)
  apply (rule ag.prog.app)
   apply (rule ag.prog.bind)
    apply (rule ag.prog.if)
     apply (rule ag.prog.return)
     apply ((simp only: stable_simps)?; (rule stable.intro)+; fail)
    apply (rule ag.prog.bind)
     apply (rule ag.pre_g[OF pending.ag.enq pending_g])
     apply ((simp only: stable_simps)?; (rule stable.intro)+; fail)
    apply (rule ag.pre_g[OF set.ag.ins set_g])
    apply ((simp only: stable_simps)?; (rule stable.intro)+; fail)
   apply (rule ag.pre_pre[OF ag.pre_g[OF set.ag.mem set_g]])
    apply ((simp only: stable_simps)?; (rule stable.intro)+; fail)
   apply (force simp: aloop_invP_step vclosureP_step)
  apply ((simp only: stable_simps)?; (rule stable.intro)+; fail)
 apply (rule ag.pre_g[OF pending.ag.deq pending_g])
 apply ((simp only: stable_simps)?; (rule stable.intro)+; fail)
apply (auto elim: search_postcond_Some search_postcond_None aloop_invP_dequeue
                  aloop_invPD vclosureP_dequeue)
done

lemma ag_amain:
  shows "prog.p2s (amain f P x\<^sub>0) \<le> \<lbrace>\<langle>True\<rangle>\<rbrace>, Id \<times>\<^sub>R Id \<times>\<^sub>R UNIV \<turnstile> UNIV \<times>\<^sub>R UNIV \<times>\<^sub>R Id, \<lbrace>search_post\<rbrace>"
unfolding main_def
apply (rule ag.pre_pre)
 apply (rule ag.prog.bind)+
     apply (rule ag_aloop)
    apply (rule ag.post_imp[where Q="\<langle>\<lambda>(q, v, _). q = {x\<^sub>0} \<and> v = [x\<^sub>0]\<rangle>"])
     apply (clarsimp simp: aloop_invP_init vclosureP_init; fail)
    apply (rule ag.pre_g[OF pending.ag.enq pending_g])
    apply ((simp only: stable_simps)?; (rule stable.intro)+; fail)
   apply (rule ag.pre_g[OF set.ag.ins set_g])
   apply ((simp only: stable_simps)?; (rule stable.intro)+; fail)
  apply (rule ag.pre_g[OF pending.ag.init pending_g])
  apply ((simp only: stable_simps)?; (rule stable.intro)+; fail)
 apply (rule ag.pre_g[OF set.ag.init set_g])
 apply ((simp only: stable_simps)?; (rule stable.intro)+; fail)
apply simp
done

lemma ag_asearch:
  shows "prog.p2s (asearch f P x\<^sub>0 :: ('s, 'a option) prog) \<le> \<lbrace>\<langle>True\<rangle>\<rbrace>, UNIV \<turnstile> Id, \<lbrace>search_post\<rbrace>"
unfolding search_def by (rule ag.prog.local ag_amain)+


paragraph\<open> Refinement \<close>

abbreviation "A \<equiv> ag.assm (Id \<times>\<^sub>R Id \<times>\<^sub>R UNIV)"
abbreviation "absfn c \<equiv> prog.sinvmap (map_prod pending.absfn id) c"
abbreviation "p2s_absfn c \<equiv> prog.p2s (absfn c)"

\<comment>\<open> visited set: reflexive \<close>
lemma ref_set_init:
  shows "prog.p2s (set.init set.abstract) \<le> \<lbrace>\<lambda>s. True\<rbrace>, A \<tturnstile> p2s_absfn (set.init set.abstract), \<lbrace>\<lambda>v s. True\<rbrace>"
by (auto simp: set.abstract_def intro: rair.prog.action stable.intro)

lemma ref_set_ins:
  shows "prog.p2s (set.ins set.abstract x) \<le> \<lbrace>\<lambda>s. True\<rbrace>, A \<tturnstile> p2s_absfn (set.ins set.abstract x), \<lbrace>\<lambda>v s. True\<rbrace>"
by (auto simp: set.abstract_def intro: rair.prog.action stable.intro)

lemma ref_set_mem:
  shows "prog.p2s (set.mem set.abstract x) \<le> \<lbrace>\<lambda>s. True\<rbrace>, A \<tturnstile> p2s_absfn (set.mem set.abstract x), \<lbrace>\<lambda>v s. True\<rbrace>"
by (auto simp: set.abstract_def intro: rair.prog.action stable.intro)

\<comment>\<open> queue \<close>
lemma ref_queue_init:
  shows "prog.p2s (pending.init pending.concrete) \<le> \<lbrace>\<lambda>s. True\<rbrace>, A \<tturnstile> p2s_absfn (pending.init pending.abstract), \<lbrace>\<lambda>v s. True\<rbrace>"
by (auto simp: pending.abstract_def pending.concrete_def pending.absfn_def intro: rair.prog.action stable.intro)

lemma ref_queue_enq:
  shows "prog.p2s (pending.enq pending.concrete x) \<le> \<lbrace>\<lambda>s. True\<rbrace>, A \<tturnstile> p2s_absfn (pending.enq pending.abstract x), \<lbrace>\<lambda>v s. True\<rbrace>"
by (auto simp: pending.abstract_def pending.concrete_def pending.absfn_def intro: rair.prog.action stable.intro)

lemma ref_queue_deq:
  shows "prog.p2s (pending.deq pending.concrete) \<le> \<lbrace>\<lambda>s. True\<rbrace>, A \<tturnstile> p2s_absfn (pending.deq pending.abstract), \<lbrace>\<lambda>v s. True\<rbrace>"
by (auto simp: pending.abstract_def pending.concrete_def pending.absfn_def
        intro: rair.prog.action stable.intro elim!: pending.cdeq_update.elims[OF sym])

\<comment>\<open> program \<close>
lemma ref_bfs_loop:
  shows "prog.p2s (loop pending.concrete f P) \<le> \<lbrace>\<lambda>s. True\<rbrace>, A \<tturnstile> p2s_absfn (loop pending.abstract f P), \<lbrace>\<lambda>v s. True\<rbrace>"
apply (simp add: loop_def)
apply (rule rair.prog.while)
  apply (rule rair.prog.rev_bind)
   apply (rule ref_queue_deq)
  apply (rule refinement.pre_pre[OF rair.prog.case_option])
    apply (rule rair.prog.return)
    apply ((simp only: stable_simps)?; (rule stable.intro)+; fail)
   apply (rule rair.prog.if)
    apply (rule rair.prog.return)
    apply ((simp only: stable_simps)?; (rule stable.intro)+; fail)
   apply (rule rair.prog.rev_bind)
    apply (rule rair.prog.app)
     apply (rule rair.prog.rev_bind)
      apply (rule ref_set_mem)
     apply (rule refinement.pre_pre[OF rair.prog.if])
       apply (rule rair.prog.return)
       apply ((simp only: stable_simps)?; (rule stable.intro)+; fail)
      apply (rule rair.prog.rev_bind)
       apply (rule ref_set_ins)
      apply (rule ref_queue_enq)
     apply (simp; fail)
    apply ((simp only: stable_simps)?; (rule stable.intro)+; fail)
   apply (rule refinement.pre_pre[OF rair.prog.return])
    apply ((simp only: stable_simps)?; (rule stable.intro)+; fail)
   apply (auto intro: stable.intro split: option.split)
done

lemma ref_bfs_main:
  shows "prog.p2s (main pending.concrete f P x) \<le> \<lbrace>\<langle>True\<rangle>\<rbrace>, A \<tturnstile> p2s_absfn (amain f P x), \<lbrace>\<lambda>v s. True\<rbrace>"
apply (simp add: main_def)
apply (rule rair.prog.rev_bind)
 apply (rule ref_set_init)
apply (rule rair.prog.rev_bind)
 apply (rule ref_queue_init)
apply (rule rair.prog.rev_bind)
 apply (rule ref_set_ins)
apply (rule rair.prog.rev_bind)
 apply (rule ref_queue_enq)
apply (rule ref_bfs_loop)
done

theorem ref_bfs:
  shows "bfs f P x \<le> asearch f P x"
unfolding search_def
apply (intro refinement.prog.leI refinement.prog.data[where sf=id])
apply (simp add: spec.invmap.id spec.localizeA.top)
apply (rule refinement.prog.data[where sf=pending.absfn])
apply (simp flip: prog.p2s.invmap)
apply (rule refinement.pre_a[OF ref_bfs_main])
apply (auto simp: spec.localizeA_def spec.invmap.rel
       simp flip: spec.rel.inf
           intro: spec.rel.mono)
done

theorem bfs_post_le:
  shows "prog.p2s (bfs f P x\<^sub>0) \<le> spec.post (search_post)"
apply (strengthen ord_to_strengthen[OF ref_bfs])
apply (strengthen ord_to_strengthen(1)[OF ag_asearch])
apply (simp add: ag_def spec.rel.UNIV flip: Sigma_Un_distrib1)
done

end
(*<*)

end
(*>*)
