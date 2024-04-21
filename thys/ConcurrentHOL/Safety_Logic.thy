(*<*)
theory Safety_Logic
imports
  Aczel_Sequences
  Galois
  Heyting
  Lifted_Predicates
begin

(*>*)
section\<open> Safety logic\label{sec:safety_logic} \<close>

text\<open>

Following \<^citet>\<open>"AbadiPlotkin:1991" and "AbadiPlotkin:1993" and "AbadiLamport:1995"\<close>
(see also \<^citet>\<open>\<open>\S5.5\<close> in "AbadiMerz:1996"\<close>), we work in the complete lattice of
stuttering-closed safety properties (i.e., stuttering-closed downsets)
and use this for logical purposes. We avoid many syntactic issues
via a shallow embedding into HOL.

\<close>


subsection\<open> Stuttering\label{sec:safety_logic-stuttering} \<close>

text\<open>

We define \<^emph>\<open>stuttering equivalence\<close> ala \<^citet>\<open>"Lamport:1994"\<close>. This allows any
agent to repeat any state at any time. We define a normalisation function \<open>(\<natural>)\<close> on
\<^typ>\<open>('a, 's, 'v) trace.t\<close> and extract the (matroidal) closure over sets of
these from the Galois connection \<^locale>\<open>galois.image_vimage\<close>.

\<close>

setup \<open>Sign.mandatory_path "trace"\<close>

primrec natural' :: "'s \<Rightarrow> ('a \<times> 's) list \<Rightarrow> ('a \<times> 's) list" where
  "natural' s [] = []"
| "natural' s (x # xs) = (if snd x = s then natural' s xs else x # natural' (snd x) xs)"

setup \<open>Sign.mandatory_path "final'"\<close>

lemma natural'[simp]:
  shows "trace.final' s (trace.natural' s xs) = trace.final' s xs"
by (induct xs arbitrary: s) simp_all

lemma natural'_cong:
  assumes "s = s'"
  assumes "trace.natural' s xs = trace.natural' s xs'"
  shows "trace.final' s xs = trace.final' s' xs'"
by (metis assms trace.final'.natural')

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "natural'"\<close>

lemma natural':
  shows "trace.natural' s (trace.natural' s xs) = trace.natural' s xs"
by (induct xs arbitrary: s) simp_all

lemma length:
  shows "length (trace.natural' s xs) \<le> length xs"
by (induct xs arbitrary: s) (simp_all add: le_SucI)

lemma subseq:
  shows "subseq (trace.natural' s xs) xs"
by (induct xs arbitrary: s) auto

lemma remdups_adj:
  shows "s # map snd (trace.natural' s xs) = remdups_adj (s # map snd xs)"
by (induct xs arbitrary: s) simp_all

lemma append:
  shows "trace.natural' s (xs @ ys) = trace.natural' s xs @ trace.natural' (trace.final' s xs) ys"
by (induct xs arbitrary: s) simp_all

lemma eq_Nil_conv:
  shows "trace.natural' s xs = [] \<longleftrightarrow> snd ` set xs \<subseteq> {s}"
    and "[] = trace.natural' s xs \<longleftrightarrow> snd ` set xs \<subseteq> {s}"
by (induct xs arbitrary: s) simp_all

lemma eq_Cons_conv:
  shows "trace.natural' s xs = y # ys
    \<longleftrightarrow> (\<exists>xs' ys'. xs = xs' @ y # ys' \<and> snd ` set xs' \<subseteq> {s} \<and> snd y \<noteq> s \<and> trace.natural' (snd y) ys' = ys)" (is "?lhs \<longleftrightarrow> ?rhs")
    and "y # ys = trace.natural' s xs
    \<longleftrightarrow> (\<exists>xs' ys'. xs = xs' @ y # ys' \<and> snd ` set xs' \<subseteq> {s} \<and> snd y \<noteq> s \<and> trace.natural' (snd y) ys' = ys)" (is ?thesis1)
proof -
  show "?lhs \<longleftrightarrow> ?rhs"
  proof(rule iffI)
    show "?lhs \<Longrightarrow> ?rhs"
    proof(induct xs)
      case (Cons x xs) show ?case
      proof(cases "s = snd x")
        case True with Cons
        obtain xs' ys'
         where "xs = xs' @ y # ys'" and "snd ` set xs' \<subseteq> {s}" and "snd y \<noteq> s"
           and "trace.natural' (snd y) ys' = ys"
          by auto
        with True show ?thesis by (simp add: exI[where x="x # xs'"])
      qed (use Cons.prems in force)
    qed simp
    show "?rhs \<Longrightarrow> ?lhs"
      by (auto simp: trace.natural'.append trace.natural'.eq_Nil_conv)
  qed
  then show ?thesis1
    by (rule eq_commute_conv)
qed

lemma eq_append_conv:
  shows "trace.natural' s xs = ys @ zs
     \<longleftrightarrow> (\<exists>ys' zs'. xs = ys' @ zs' \<and> trace.natural' s ys' = ys \<and> trace.natural' (trace.final' s ys) zs' = zs)" (is "?lhs = ?rhs")
    and "ys @ zs = trace.natural' s xs
     \<longleftrightarrow> (\<exists>ys' zs'. xs = ys' @ zs' \<and> trace.natural' s ys' = ys \<and> trace.natural' (trace.final' s ys) zs' = zs)" (is ?thesis1)
proof -
  show "?lhs \<longleftrightarrow> ?rhs"
  proof(rule iffI)
    show "?lhs \<Longrightarrow> ?rhs"
    proof(induct ys arbitrary: s xs)
      case (Cons y ys s xs)
      from Cons.prems
      obtain ys' zs'
       where "xs = ys' @ y # zs'" and "snd ` set ys' \<subseteq> {s}"
         and "snd y \<noteq> s" and "trace.natural' (snd y) zs' = ys @ zs"
        by (clarsimp simp: trace.natural'.eq_Cons_conv)
      with Cons.hyps[where s="snd y" and xs="zs'"] show ?case
        by (clarsimp simp: trace.natural'.eq_Cons_conv) (metis append.assoc append_Cons)
    qed fastforce
    show "?rhs \<Longrightarrow> ?lhs"
      by (auto simp: trace.natural'.append)
  qed
  then show ?thesis1
    by (rule eq_commute_conv)
qed

lemma replicate:
  shows "trace.natural' s (replicate i as) = (if snd as = s \<or> i = 0 then [] else [as])"
by (auto simp: gr0_conv_Suc trace.natural'.eq_Nil_conv)

lemma map_natural':
  shows "trace.natural' (sf s) (map (map_prod af sf) (trace.natural' s xs))
       = trace.natural' (sf s) (map (map_prod af sf) xs)"
by (induct xs arbitrary: s; simp; metis)

lemma map_inj_on_sf:
  assumes "inj_on sf (insert s (snd ` set xs))"
  shows "trace.natural' (sf s) (map (map_prod af sf) xs) = map (map_prod af sf) (trace.natural' s xs)"
using assms
proof(induct xs arbitrary: s)
  case (Cons x xs s)
  from Cons.prems have "sf (snd x) \<noteq> sf s" if "snd x \<noteq> s"
    by (meson image_eqI inj_onD insert_iff list.set_intros(1) that)
  with Cons.prems show ?case
    by (auto intro: Cons.hyps)
qed simp

lemma amap_noop:
  assumes "trace.natural' s xs = map (map_prod af id) zs"
  shows "trace.natural' s zs = zs"
using assms by (induct xs arbitrary: s zs) (auto split: if_split_asm)

lemma take:
  shows "\<exists>j\<le>length xs. take i (trace.natural' s xs) = trace.natural' s (take j xs)"
proof(induct xs arbitrary: s i)
  case (Cons x xs s i) then show ?case by (cases i; fastforce)
qed simp

lemma idle_prefix:
  assumes "snd ` set xs \<subseteq> {s}"
  shows "trace.natural' s (xs @ ys) = trace.natural' s ys"
using assms by (simp add: trace.natural'.append trace.natural'.eq_Nil_conv)

lemma prefixE:
  assumes "trace.natural' s ys = trace.natural' s (xs @ xsrest)"
  obtains xs' xs'rest where "trace.natural' s xs = trace.natural' s xs'" and "ys = xs' @ xs'rest"
by (metis assms trace.natural'.eq_append_conv(2))

lemma aset_conv:
  shows "a \<in> trace.aset (trace.T s (trace.natural' s xs) v)
    \<longleftrightarrow> (\<exists>s' s''. (a, s', s'') \<in> set (trace.transitions' s xs) \<and> s' \<noteq> s'')"
by (induct xs arbitrary: s) (auto simp: trace.aset.simps)

setup \<open>Sign.parent_path\<close>

definition natural :: "('a, 's, 'v) trace.t \<Rightarrow> ('a, 's, 'v) trace.t" ("\<natural>") where
  "\<natural>\<sigma> = trace.T (trace.init \<sigma>) (trace.natural' (trace.init \<sigma>) (trace.rest \<sigma>)) (trace.term \<sigma>)"

setup \<open>Sign.mandatory_path "natural"\<close>

lemma sel[simp]:
  shows "trace.init (\<natural>\<sigma>) = trace.init \<sigma>"
    and "trace.rest (\<natural>\<sigma>) = trace.natural' (trace.init \<sigma>) (trace.rest \<sigma>)"
    and "trace.term (\<natural>\<sigma>) = trace.term \<sigma>"
by (simp_all add: trace.natural_def)

lemma simps:
  shows "\<natural>(trace.T s [] v) = trace.T s [] v"
    and "\<natural>(trace.T s ((a, s) # xs) v) = \<natural>(trace.T s xs v)"
    and "\<natural>(trace.T s (trace.natural' s xs) v) = \<natural>(trace.T s xs v)"
by (simp_all add: trace.natural_def trace.natural'.natural')

lemma idempotent[simp]:
  shows "\<natural>(\<natural>\<sigma>) = \<natural>\<sigma>"
by (simp add: trace.natural_def trace.natural'.natural')

lemma idle:
  assumes "snd ` set xs \<subseteq> {s}"
  shows "\<natural>(trace.T s xs v) = trace.T s [] v"
by (simp add: assms trace.natural_def trace.natural'.eq_Nil_conv)

lemma trace_conv:
  shows "\<natural>(trace.T s xs v) = \<natural>\<sigma> \<longleftrightarrow> trace.init \<sigma> = s \<and> trace.natural' s xs = trace.natural' s (trace.rest \<sigma>) \<and> trace.term \<sigma> = v"
    and "\<natural>\<sigma> = \<natural>(trace.T s xs v) \<longleftrightarrow> trace.init \<sigma> = s \<and> trace.natural' s xs = trace.natural' s (trace.rest \<sigma>) \<and> trace.term \<sigma> = v"
by (cases \<sigma>; fastforce simp: trace.natural_def)+

lemma map_natural:
  shows "\<natural>(trace.map af sf vf (\<natural>\<sigma>)) = \<natural>(trace.map af sf vf \<sigma>)"
by (simp add: trace.natural_def trace.natural'.map_natural')

lemma continue:
  shows "\<natural>(\<sigma> @-\<^sub>S xsv) = \<natural>\<sigma> @-\<^sub>S (trace.natural' (trace.final \<sigma>) (fst xsv), snd xsv)"
by (simp add: trace.natural_def trace.natural'.append split: option.split)

lemma replicate:
  shows "\<natural>(trace.T s (replicate i as) v)
        = (trace.T s (if snd as = s \<or> i = 0 then [] else [as]) v)"
by (simp add: trace.natural_def trace.natural'.replicate)

lemma monotone:
  shows "mono \<natural>"
using trace.natural.continue by (fastforce intro: monoI simp: trace.less_eq_t_def)

lemmas strengthen[strg] = st_monotone[OF trace.natural.monotone]
lemmas mono = monotoneD[OF trace.natural.monotone]
lemmas mono2mono[cont_intro, partial_function_mono]
  = monotone2monotone[OF trace.natural.monotone, simplified, of orda P for orda P]

lemma less_eqE:
  assumes "t \<le> u"
  assumes "\<natural>u' = \<natural>u"
  obtains t' where "\<natural>t = \<natural>t'" and "t' \<le> u'"
using assms
by atomize_elim
   (fastforce simp: trace.natural_def trace.split_Ex trace.less_eq_None(2)[unfolded prefix_def]
             elim!: trace.less_eqE prefixE trace.natural'.prefixE)

lemma less_eq_natural:
  assumes "\<sigma>\<^sub>1 \<le> \<natural>\<sigma>\<^sub>2"
  shows "\<natural>\<sigma>\<^sub>1 = \<sigma>\<^sub>1"
using assms
by (cases \<sigma>\<^sub>1)
   (auto simp: trace.natural_def prefix_def trace.natural'.eq_append_conv trace.natural'.natural'
        elim!: trace.less_eqE)

lemma map_le:
  assumes "\<natural>\<sigma>\<^sub>1 \<le> \<natural>\<sigma>\<^sub>2"
  shows "\<natural>(trace.map af sf vf \<sigma>\<^sub>1) \<le> \<natural>(trace.map af sf vf \<sigma>\<^sub>2)"
using trace.natural.mono[OF trace.map.mono[OF assms], simplified trace.natural.map_natural] .

lemma map_inj_on_sf:
  assumes "inj_on sf (trace.sset \<sigma>)"
  shows "\<natural>(trace.map af sf vf \<sigma>) = trace.map af sf vf (\<natural>\<sigma>)"
using assms by (cases \<sigma>) (simp add: trace.natural_def trace.natural'.map_inj_on_sf trace.sset.simps)

lemma take:
  shows "\<exists>j. \<natural>(trace.take i \<sigma>) = trace.take j (\<natural>\<sigma>)"
by (meson trace.natural.mono trace.less_eq_take_def)

lemma take_natural:
  shows "\<natural>(trace.take i (\<natural>\<sigma>)) = trace.take i (\<natural>\<sigma>)"
using trace.natural.less_eq_natural by blast

lemma takeE:
  shows "\<lbrakk>\<sigma>\<^sub>1 = \<natural>(trace.take i \<sigma>\<^sub>2); \<And>j. \<lbrakk>\<sigma>\<^sub>1 = trace.take j (\<natural>\<sigma>\<^sub>2)\<rbrakk> \<Longrightarrow> thesis\<rbrakk> \<Longrightarrow> thesis"
    and "\<lbrakk>\<natural>(trace.take i \<sigma>\<^sub>2) = \<sigma>\<^sub>1; \<And>j. \<lbrakk>\<sigma>\<^sub>1 = trace.take j (\<natural>\<sigma>\<^sub>2)\<rbrakk> \<Longrightarrow> thesis\<rbrakk> \<Longrightarrow> thesis"
using trace.natural.take by blast+

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "aset"\<close>

lemma natural_conv:
  shows "a \<in> trace.aset (\<natural>\<sigma>) \<longleftrightarrow> (\<exists>s s'. (a, s, s') \<in> trace.steps \<sigma>)"
by (simp add: trace.natural_def trace.steps'_def trace.natural'.aset_conv)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "sset"\<close>

lemma natural'[simp]:
  shows "trace.sset (trace.T s\<^sub>0 (trace.natural' s\<^sub>0 xs) v) = trace.sset (trace.T s\<^sub>0 xs v)"
by (induct xs arbitrary: s\<^sub>0) (simp_all add: trace.sset.simps)

lemma natural[simp]:
  shows "trace.sset (\<natural>\<sigma>) = trace.sset \<sigma>"
by (simp add: trace.natural_def)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "vset"\<close>

lemma natural[simp]:
  shows "trace.vset (\<natural>\<sigma>) = trace.vset \<sigma>"
by (cases \<sigma>) (simp add: trace.natural_def trace.t.simps(8))

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "take"\<close>

lemma natural:
  shows "\<exists>j\<le>Suc (length (trace.rest \<sigma>)). trace.take i (\<natural>\<sigma>) = \<natural>(trace.take j \<sigma>)"
using trace.natural'.take[where i=i and s= "trace.init \<sigma>" and xs="trace.rest \<sigma>"]
by (auto simp: trace.natural_def trace.take_def not_le) (use Suc_n_not_le_n in blast)

lemma naturalE:
  shows "\<lbrakk>\<sigma>\<^sub>1 = trace.take i (\<natural>\<sigma>\<^sub>2); \<And>j. \<lbrakk>j \<le> Suc (length (trace.rest \<sigma>\<^sub>2)); \<sigma>\<^sub>1 = \<natural>(trace.take j \<sigma>\<^sub>2)\<rbrakk> \<Longrightarrow> thesis\<rbrakk> \<Longrightarrow> thesis"
    and "\<lbrakk>trace.take i (\<natural>\<sigma>\<^sub>2) = \<sigma>\<^sub>1; \<And>j. \<lbrakk>j \<le> Suc (length (trace.rest \<sigma>\<^sub>2)); \<natural>(trace.take j \<sigma>\<^sub>2) = \<sigma>\<^sub>1\<rbrakk> \<Longrightarrow> thesis\<rbrakk> \<Longrightarrow> thesis"
using trace.take.natural[of \<sigma>\<^sub>2 i] by force+

setup \<open>Sign.parent_path\<close>

lemma steps'_alt_def:
  shows "trace.steps' s xs = set (trace.transitions' s (trace.natural' s xs))"
by (induct xs arbitrary: s) auto

setup \<open>Sign.mandatory_path "steps'"\<close>

lemma natural':
  shows "trace.steps' s (trace.natural' s xs) = trace.steps' s xs"
unfolding trace.steps'_def by (induct xs arbitrary: s) auto

lemma asetD:
  assumes "trace.steps \<sigma> \<subseteq> r"
  shows "\<forall>a. a \<in> trace.aset (\<natural>\<sigma>) \<longrightarrow> a \<in> fst ` r"
using assms by (force simp: trace.aset.natural_conv)

lemma range_initE:
  assumes "trace.steps' s\<^sub>0 xs \<subseteq> range af \<times> range sf \<times> range sf"
  assumes "(a, s, s') \<in> trace.steps' s\<^sub>0 xs"
  obtains s\<^sub>0' where "s\<^sub>0 = sf s\<^sub>0'"
using assms by (induct xs arbitrary: s s\<^sub>0) (auto simp: trace.steps'_alt_def split: if_split_asm)

lemma map_range_conv:
  shows "trace.steps' (sf s) xs \<subseteq> range af \<times> range sf \<times> range sf
     \<longleftrightarrow> (\<exists>xs'. trace.natural' (sf s) xs = map (map_prod af sf) xs')" (is "?lhs \<longleftrightarrow> ?rhs")
proof(rule iffI)
  show "?lhs \<Longrightarrow> ?rhs"
    by (induct xs arbitrary: s) (auto 0 3 simp: Cons_eq_map_conv)
  show "?rhs \<Longrightarrow> ?lhs"
    by (force simp: trace.steps'_alt_def trace.transitions'.map map_prod_conv)
qed

lemma step_conv:
  shows "trace.steps' s xs = {x}
     \<longleftrightarrow> fst (snd x) = s \<and> fst (snd x) \<noteq> snd (snd x)
       \<and> (\<exists>ys zs. snd ` set ys \<subseteq> {s} \<and> snd ` set zs \<subseteq> {snd (snd x)}
                \<and> xs = ys @ [(fst x, snd (snd x))] @ zs)" (is "?lhs \<longleftrightarrow> ?rhs")
proof(rule iffI)
  show "?lhs \<Longrightarrow> ?rhs"
    by (fastforce dest!: arg_cong[where f="set"]
                   simp: trace.steps'_alt_def set_singleton_conv set_replicate_conv_if
                         trace.transitions'.eq_Nil_conv trace.transitions'.eq_Cons_conv
                         trace.natural'.eq_Nil_conv trace.natural'.eq_Cons_conv
                  split: if_split_asm)
  show "?rhs \<Longrightarrow> ?lhs"
    by (clarsimp simp: trace.steps'.append)
qed

setup \<open>Sign.parent_path\<close>

interpretation stuttering: galois.image_vimage_idempotent "\<natural>"
by (simp add: galois.image_vimage_idempotent.intro)

abbreviation stuttering_equiv_syn :: "('a, 's, 'v) trace.t \<Rightarrow> ('a, 's, 'v) trace.t \<Rightarrow> bool" (infix "\<simeq>\<^sub>S" 50) where
  "\<sigma>\<^sub>1 \<simeq>\<^sub>S \<sigma>\<^sub>2 \<equiv> trace.stuttering.equivalent \<sigma>\<^sub>1 \<sigma>\<^sub>2"

setup \<open>Sign.mandatory_path "stuttering"\<close>

setup \<open>Sign.mandatory_path "cl"\<close>

setup \<open>Sign.mandatory_path "downwards"\<close>

lemma cl:
  shows "trace.stuttering.cl (downwards.cl P) = downwards.cl (trace.stuttering.cl P)" (is "?lhs = ?rhs")
proof(rule antisym)
  show "?lhs \<subseteq> ?rhs"
    by (clarsimp simp: trace.stuttering.cl_alt_def downwards.cl_def trace.less_eq_t_def)
       (metis trace.final'.natural' trace.natural.continue trace.natural.sel(1,2))
next
  show "?rhs \<subseteq> ?lhs"
    by (clarsimp elim!: downwards.clE trace.stuttering.clE)
       (erule (1) trace.natural.less_eqE; fastforce)
qed

lemma closed:
  assumes "P \<in> downwards.closed"
  shows "trace.stuttering.cl P \<in> downwards.closed"
by (metis assms downwards.closedI downwards.closed_conv trace.stuttering.cl.downwards.cl)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "closed"\<close>

lemma downwards_imp: \<comment> \<open> \<^citet>\<open>\<open>p13\<close> in "AbadiPlotkin:1993"\<close> \<close>
  assumes "P \<in> trace.stuttering.closed"
  assumes "Q \<in> trace.stuttering.closed"
  shows "downwards.imp P Q \<in>  trace.stuttering.closed"
by (simp add: assms downwards.closed_imp downwards.heyting_imp downwards.imp_mp
              trace.stuttering.cl.downwards.closed trace.stuttering.closed_clI
              trace.stuttering.exchange_closed_inter trace.stuttering.least)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "equiv"\<close>

lemma simps:
  shows "snd ` set xs \<subseteq> {s} \<Longrightarrow> trace.T s (xs @ ys) v \<simeq>\<^sub>S trace.T s ys v"
    and "snd ` set ys \<subseteq> {trace.final' s xs} \<Longrightarrow> trace.T s (xs @ ys) v \<simeq>\<^sub>S trace.T s xs v"
    and "snd ` set xs \<subseteq> {snd x} \<Longrightarrow> trace.T s (x # xs @ ys) v \<simeq>\<^sub>S trace.T s (x # ys) v"
by (fastforce simp: trace.natural_def trace.natural'.append trace.natural'.eq_Nil_conv)+

lemma append_cong:
  assumes "s = s'"
  assumes "trace.natural' s xs = trace.natural' s xs'"
  assumes "trace.natural' (trace.final' s xs) ys = trace.natural' (trace.final' s xs) ys'"
  assumes "v = v'"
  shows "trace.T s (xs @ ys) v \<simeq>\<^sub>S trace.T s' (xs' @ ys') v'"
using assms by (simp add: trace.natural_def trace.natural'.append cong: trace.final'.natural'_cong)

lemma E:
  assumes "trace.T s xs v \<simeq>\<^sub>S trace.T s' xs' v'"
  obtains "trace.natural' s xs = trace.natural' s' xs'" and "s = s'" and "v = v'"
using assms by (fastforce simp: trace.natural_def)

lemma append_conv:
  shows "trace.T s (xs @ ys) v \<simeq>\<^sub>S \<sigma>
    \<longleftrightarrow> (\<exists>xs' ys'. \<sigma> = trace.T s (xs' @ ys') v \<and> trace.natural' s xs = trace.natural' s xs'
                 \<and> trace.natural' (trace.final' s xs) ys = trace.natural' (trace.final' s xs) ys')" (is ?thesis1)
    and "\<sigma> \<simeq>\<^sub>S trace.T s (xs @ ys) v
    \<longleftrightarrow> (\<exists>xs' ys'. \<sigma> = trace.T s (xs' @ ys') v \<and> trace.natural' s xs = trace.natural' s xs'
                 \<and> trace.natural' (trace.final' s xs) ys = trace.natural' (trace.final' s xs) ys')" (is ?thesis2)
proof -
  show ?thesis1
    by (cases \<sigma>)
       (fastforce simp: trace.natural'.append trace.natural'.eq_append_conv
                  elim: trace.stuttering.equiv.E
                 intro: trace.stuttering.equiv.append_cong)
  then show ?thesis2
    by (rule eq_commute_conv)
qed

lemma map:
  assumes "\<sigma>\<^sub>1 \<simeq>\<^sub>S \<sigma>\<^sub>2"
  shows "trace.map af sf vf \<sigma>\<^sub>1 \<simeq>\<^sub>S trace.map af sf vf \<sigma>\<^sub>2"
by (metis assms trace.natural.map_natural)

lemma steps:
  assumes "\<sigma>\<^sub>1 \<simeq>\<^sub>S \<sigma>\<^sub>2"
  shows "trace.steps \<sigma>\<^sub>1 = trace.steps \<sigma>\<^sub>2"
using assms by (force simp: trace.steps'_alt_def trace.natural_def)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.parent_path\<close>


subsection\<open> The \<^emph>\<open>('a, 's, 'v) spec\<close> lattice \label{sec:safety_logic-logic} \<close>

text\<open>

Our workhorse lattice consists of all sets of traces that are downwards and stuttering closed. This
combined closure is neither matroidal nor antimatroidal (\S\ref{sec:closures-matroids}).

We define the lattice as a type and instantiate the relevant type classes. In the following
read \<open>P \<le> Q\<close> (\<open>P \<subseteq> Q\<close> in the powerset model) as ``Q follows from P'' or ``P entails Q''.

\<close>

setup \<open>Sign.mandatory_path "raw"\<close>

setup \<open>Sign.mandatory_path "spec"\<close>

definition cl :: "('a, 's, 'v) trace.t set \<Rightarrow> ('a, 's, 'v) trace.t set" where
  "cl P = downwards.cl (trace.stuttering.cl P)"

setup \<open>Sign.parent_path\<close>

interpretation spec: closure_powerset_distributive raw.spec.cl
unfolding raw.spec.cl_def
by (simp add: closure_powerset_distributive_comp downwards.closure_powerset_distributive_axioms
              trace.stuttering.closure_powerset_distributive_axioms trace.stuttering.cl.downwards.cl)

setup \<open>Sign.mandatory_path "spec"\<close>

setup \<open>Sign.mandatory_path "cl"\<close>

lemma empty[simp]:
  shows "raw.spec.cl {} = {}"
by (simp add: raw.spec.cl_def downwards.cl_empty trace.stuttering.cl_bot)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "closed"\<close>

lemma I:
  assumes "P \<in> downwards.closed"
  assumes "P \<in> trace.stuttering.closed"
  shows "P \<in> raw.spec.closed"
by (metis assms raw.spec.cl_def downwards.closed_conv raw.spec.closed trace.stuttering.closed_conv)

lemma empty[intro]:
  shows "{} \<in> raw.spec.closed"
using raw.spec.cl.empty by blast

lemma downwards_closed:
  assumes "P \<in> raw.spec.closed"
  shows "P \<in> downwards.closed"
by (metis assms downwards.closed raw.spec.cl_def raw.spec.closed_conv)

lemma stuttering_closed:
  assumes "P \<in> raw.spec.closed"
  shows "P \<in> trace.stuttering.closed"
using assms raw.spec.cl_def raw.spec.closed_conv by fast

lemma downwards_imp:
  assumes "P \<in> raw.spec.closed"
  assumes "Q \<in> raw.spec.closed"
  shows "downwards.imp P Q \<in> raw.spec.closed"
by (meson assms downwards.closed_imp raw.spec.closed.I raw.spec.closed.stuttering_closed
          trace.stuttering.cl.closed.downwards_imp)

lemma heyting_downwards_imp:
  assumes "P \<in> raw.spec.closed"
  shows "P \<subseteq> downwards.imp Q R \<longleftrightarrow> P \<inter> Q \<subseteq> R"
by (simp add: assms downwards.heyting_imp raw.spec.closed.downwards_closed)

lemma takeE:
  assumes "\<sigma> \<in> P"
  assumes "P \<in> raw.spec.closed"
  shows "trace.take i \<sigma> \<in> P"
by (meson assms downwards.closed_in raw.spec.closed.downwards_closed trace.less_eq_take)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.parent_path\<close>

typedef ('a, 's, 'v) spec = "raw.spec.closed :: ('a, 's, 'v) trace.t set set"
morphisms unMkS MkS
by blast

setup_lifting type_definition_spec

instantiation spec :: (type, type, type) complete_distrib_lattice
begin

lift_definition bot_spec :: "('a, 's, 'v) spec" is empty ..
lift_definition top_spec :: "('a, 's, 'v) spec" is UNIV ..
lift_definition sup_spec :: "('a, 's, 'v) spec \<Rightarrow> ('a, 's, 'v) spec \<Rightarrow> ('a, 's, 'v) spec" is sup ..
lift_definition inf_spec :: "('a, 's, 'v) spec \<Rightarrow> ('a, 's, 'v) spec \<Rightarrow> ('a, 's, 'v) spec" is inf ..
lift_definition less_eq_spec :: "('a, 's, 'v) spec \<Rightarrow> ('a, 's, 'v) spec \<Rightarrow> bool" is less_eq .
lift_definition less_spec :: "('a, 's, 'v) spec \<Rightarrow> ('a, 's, 'v) spec \<Rightarrow> bool" is less .
lift_definition Inf_spec :: "('a, 's, 'v) spec set \<Rightarrow> ('a, 's, 'v) spec" is Inf ..
lift_definition Sup_spec :: "('a, 's, 'v) spec set \<Rightarrow> ('a, 's, 'v) spec" is "\<lambda>X. Sup X \<squnion> raw.spec.cl {}" ..

instance
by (standard; transfer; auto simp: raw.spec.closed_strict_complete_distrib_lattice_axiomI[OF raw.spec.cl.empty])

end

declare
  SUPE[where 'a="('a, 's, 'v) spec", intro!]
  SupE[where 'a="('a, 's, 'v) spec", intro!]
  Sup_le_iff[where 'a="('a, 's, 'v) spec", simp]
  SupI[where 'a="('a, 's, 'v) spec", intro]
  SUPI[where 'a="('a, 's, 'v) spec", intro]
  rev_SUPI[where 'a="('a, 's, 'v) spec", intro?]
  INFE[where 'a="('a, 's, 'v) spec", intro]

text\<open>

Observations about this type:
 \<^item> it is not a BNF (datatype) as it uses the powerset
 \<^item> it fails to be T0 or sober due to the lack of limit points (completeness) in \<^typ>\<open>('a, 's, 'v) trace.t\<close>
  \<^item> also stuttering closure precludes T0
 \<^item> the \<^class>\<open>complete_distrib_lattice\<close> instance shows that arbitrary/infinitary \<open>Sup\<close>s and \<open>Inf\<close>s distribute
  \<^item> in other words: safety properties are closed under arbitrary intersections and unions
  \<^item> in other words: Alexandrov
 \<^item> conclude: the lack of limit points makes this model easier to work in and adds expressivity
  \<^item> see \S\ref{sec:safety_closure} for further discussion

\<close>

setup \<open>Sign.mandatory_path "spec"\<close>

lemmas antisym = antisym[where 'a="('a, 's, 'v) spec"]
lemmas eq_iff = order.eq_iff[where 'a="('a, 's, 'v) spec"]

setup \<open>Sign.parent_path\<close>


subsection\<open> Irreducible elements\label{sec:safety_logic-singleton} \<close>

text\<open>

The irreducible elements of \<^typ>\<open>('a, 's, 'v) trace.t\<close> are the closures of singletons.

\<close>

setup \<open>Sign.mandatory_path "raw"\<close>

definition singleton :: "('a, 's, 'v) trace.t \<Rightarrow> ('a, 's, 'v) trace.t set" where
  "singleton \<sigma> = raw.spec.cl {\<sigma>}"

lemma singleton_le_conv:
  shows "raw.singleton \<sigma>\<^sub>1 \<le> raw.singleton \<sigma>\<^sub>2 \<longleftrightarrow> \<natural>\<sigma>\<^sub>1 \<le> \<natural> \<sigma>\<^sub>2" (is "?lhs \<longleftrightarrow> ?rhs")
proof(rule iffI)
  assume ?lhs
  then have "\<sigma> \<in> downwards.cl {\<natural> \<sigma>\<^sub>2}" if "\<sigma> \<le> \<natural> \<sigma>\<^sub>1" for \<sigma>
    using that trace.natural.mono
    by (force simp: raw.singleton_def raw.spec.cl_def
             intro: downwards.clI[where y="\<natural>\<sigma>\<^sub>1"]
             elim!: downwards.clE trace.stuttering.clE
             dest!: subsetD[where c=\<sigma>]
              dest: trace.natural.less_eq_natural)
  then show ?rhs
    by (fastforce simp flip: downwards.order_embedding[where x="\<natural>\<sigma>\<^sub>1"]
                       elim: downwards.clE trace.stuttering.clE)
next
  show "?rhs \<Longrightarrow> ?lhs"
    by (clarsimp simp: raw.singleton_def raw.spec.cl_def)
       (metis downwards.order_embedding trace.natural.idempotent trace.stuttering.cl.downwards.cl
              trace.stuttering.cl_mono trace.stuttering.equiv_cl_singleton)
qed

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "spec"\<close>

lift_definition singleton :: "('a, 's, 'v) trace.t \<Rightarrow> ('a, 's, 'v) spec" ("\<lblot>_\<rblot>") is raw.singleton
by (simp add: raw.singleton_def)

abbreviation singleton_trace_syn :: "'s \<Rightarrow> ('a \<times> 's) list \<Rightarrow> 'v option \<Rightarrow> ('a, 's, 'v) spec" ("\<lblot>_, _, _\<rblot>") where
  "\<lblot>s, xs, v\<rblot> \<equiv> \<lblot>trace.T s xs v\<rblot>"

setup \<open>Sign.mandatory_path "singleton"\<close>

lemma Sup_prime:
  shows "Sup_prime \<lblot>\<sigma>\<rblot>"
by (clarsimp simp: Sup_prime_on_def)
   (transfer; auto simp: raw.singleton_def elim!: Sup_prime_onE[OF raw.spec.Sup_prime_on_singleton])

lemma nchotomy:
  shows "\<exists>X\<in>raw.spec.closed. x = \<Squnion>(spec.singleton ` X)"
by transfer
   (use raw.spec.closed_conv in \<open>auto simp: raw.singleton_def
                                       simp flip: raw.spec.distributive[simplified]\<close>)

lemmas exhaust = bexE[OF spec.singleton.nchotomy]

lemma collapse[simp]:
  shows "\<Squnion>(spec.singleton ` {\<sigma>. \<lblot>\<sigma>\<rblot> \<le> P}) = P"
by (rule spec.singleton.exhaust[of P]; blast intro: antisym)

lemmas not_bot = Sup_prime_not_bot[OF spec.singleton.Sup_prime] \<comment>\<open> Non-triviality \<close>

setup \<open>Sign.parent_path\<close>

lemma singleton_le_ext_conv:
  shows "P \<le> Q \<longleftrightarrow> (\<forall>\<sigma>. \<lblot>\<sigma>\<rblot> \<le> P \<longrightarrow> \<lblot>\<sigma>\<rblot> \<le> Q)" (is "?lhs \<longleftrightarrow> ?rhs")
proof(rule iffI)
  show "?rhs \<Longrightarrow> ?lhs"
    by (rule spec.singleton.exhaust[where x=P]; rule spec.singleton.exhaust[where x=Q]; blast)
qed fastforce

lemmas singleton_le_conv = raw.singleton_le_conv[transferred]
lemmas singleton_le_extI = iffD2[OF spec.singleton_le_ext_conv, rule_format]

lemma singleton_eq_conv[simp]:
  shows "\<lblot>\<sigma>\<rblot> = \<lblot>\<sigma>'\<rblot> \<longleftrightarrow> \<sigma> \<simeq>\<^sub>S \<sigma>'"
by (auto simp: spec.eq_iff spec.singleton_le_conv)

lemma singleton_cong:
  assumes "\<sigma> \<simeq>\<^sub>S \<sigma>'"
  shows "\<lblot>\<sigma>\<rblot> = \<lblot>\<sigma>'\<rblot>"
using assms by simp

setup \<open>Sign.mandatory_path "singleton"\<close>

named_theorems le_conv \<open> simplification rules for \<open>\<lblot>\<sigma>\<rblot> \<le> const \<dots>\<close> \<close>

lemmas antisym = antisym[OF spec.singleton_le_extI spec.singleton_le_extI]

lemmas top = spec.singleton.collapse[of \<top>, simplified, symmetric]

lemma monotone:
  shows "mono spec.singleton"
by (simp add: monoI trace.natural.mono spec.singleton_le_conv)

lemmas strengthen[strg] = st_monotone[OF spec.singleton.monotone]
lemmas mono = monoD[OF spec.singleton.monotone]
lemmas mono2mono[cont_intro, partial_function_mono]
  = monotone2monotone[OF spec.singleton.monotone, simplified]

lemma simps[simp]:
  shows "\<lblot>\<natural>\<sigma>\<rblot> = \<lblot>\<sigma>\<rblot>"
    and "\<lblot>s, xs, v\<rblot> \<le> \<lblot>s, trace.natural' s xs, v\<rblot>"
    and "snd ` set xs \<subseteq> {s} \<Longrightarrow> \<lblot>s, xs @ ys, v\<rblot> = \<lblot>s, ys, v\<rblot>"
    and "snd ` set ys \<subseteq> {trace.final' s xs} \<Longrightarrow> \<lblot>s, xs @ ys, v\<rblot> = \<lblot>s, xs, v\<rblot>"
    and "snd ` set xs \<subseteq> {snd x} \<Longrightarrow> \<lblot>s, x # xs @ ys, v\<rblot> = \<lblot>s, x # ys, v\<rblot>"
    and "\<lblot>s, (a, s) # xs, v\<rblot> = \<lblot>s, xs, v\<rblot>"
by (simp_all add: antisym spec.singleton_le_conv trace.stuttering.equiv.simps trace.natural.simps)

lemma Cons: \<comment>\<open> self-applies, not usable by \<open>simp\<close> \<close>
  assumes "snd ` set as \<subseteq> {s'}"
  shows "\<lblot>s, (a, s') # as, v\<rblot> = \<lblot>s, [(a, s')], v\<rblot>"
by (simp add: assms spec.singleton.simps(4)[where xs="[(a, s')]" and ys="as", simplified])

lemmas Sup_irreducible = iffD1[OF heyting.Sup_prime_Sup_irreducible_iff spec.singleton.Sup_prime]
lemmas sup_irreducible = Sup_irreducible_on_imp_sup_irreducible_on[OF spec.singleton.Sup_irreducible, simplified]
lemmas Sup_leE[elim] = Sup_prime_onE[OF spec.singleton.Sup_prime, simplified]
lemmas sup_le_conv[simp] = sup_irreducible_le_conv[OF spec.singleton.sup_irreducible]
lemmas Sup_le_conv[simp] = Sup_prime_on_conv[OF spec.singleton.Sup_prime, simplified]
lemmas compact_point = Sup_prime_is_compact[OF spec.singleton.Sup_prime]
lemmas compact[cont_intro] = compact_points_are_ccpo_compact[OF spec.singleton.compact_point]

lemma Inf:
  shows "\<Sqinter>(spec.singleton ` X) = \<Squnion>(spec.singleton ` {\<sigma>. \<forall>\<sigma>\<^sub>1\<in>X. \<sigma> \<le> \<natural>\<sigma>\<^sub>1})"
by (fastforce simp: le_INF_iff spec.singleton_le_conv
              dest: spec.singleton.mono
             intro: spec.singleton.antisym)

lemmas inf = spec.singleton.Inf[where X="{\<sigma>\<^sub>1, \<sigma>\<^sub>2}", simplified] for \<sigma>\<^sub>1 \<sigma>\<^sub>2

lemma less_eq_Some[simp]:
  shows "\<lblot>s, xs, Some v\<rblot> \<le> \<lblot>\<sigma>\<rblot>
     \<longleftrightarrow> trace.term \<sigma> = Some v \<and> trace.init \<sigma> = s \<and> trace.natural' s (trace.rest \<sigma>) = trace.natural' s xs"
by (auto simp: spec.singleton_le_conv trace.natural_def)

lemma less_eq_None:
  shows [iff]: "\<lblot>s, xs, None\<rblot> \<le> \<lblot>s, xs, v'\<rblot>"
by (auto simp: spec.singleton_le_conv trace.natural_def trace.less_eq_None)

lemma map_cong:
  assumes "\<And>a. a \<in> trace.aset (\<natural>\<sigma>') \<Longrightarrow> af a = af' a"
  assumes "\<And>x. x \<in> trace.sset (\<natural>\<sigma>') \<Longrightarrow> sf x = sf' x"
  assumes "\<And>v. v \<in> trace.vset (\<natural>\<sigma>') \<Longrightarrow> vf v = vf' v"
  assumes "\<natural>\<sigma> = \<natural>\<sigma>'"
  shows "\<lblot>trace.map af sf vf \<sigma>\<rblot> = \<lblot>trace.map af' sf' vf' \<sigma>'\<rblot>"
proof -
  from assms have "trace.map af sf vf (\<natural> \<sigma>) \<simeq>\<^sub>S trace.map af' sf' vf' (\<natural> \<sigma>')"
    by (simp del: trace.sset.natural trace.vset.natural cong: trace.t.map_cong)
  then show ?thesis
    by (simp add: trace.natural.map_natural)
qed

lemma map_le:
  assumes "\<lblot>\<sigma>\<rblot> \<le> \<lblot>\<sigma>'\<rblot>"
  shows "\<lblot>trace.map af sf vf \<sigma>\<rblot> \<le> \<lblot>trace.map af sf vf \<sigma>'\<rblot>"
using assms by (simp add: spec.singleton_le_conv trace.natural.map_le)

lemma takeI:
  assumes "\<lblot>\<sigma>\<rblot> \<le> P"
  shows "\<lblot>trace.take i \<sigma>\<rblot> \<le> P"
by (meson assms order.trans spec.singleton.mono trace.less_eq_take)

setup \<open>Sign.parent_path\<close>

lemmas assms_cong = order.assms_cong[where 'a="('a, 's, 'v) spec"]
lemmas concl_cong = order.concl_cong[where 'a="('a, 's, 'v) spec"]

declare spec.singleton.transfer[transfer_rule del]

setup \<open>Sign.parent_path\<close>


subsection\<open> Maps\label{sec:safety_logic-maps} \<close>

text\<open>

Lift \<^const>\<open>trace.map\<close> to the \<^typ>\<open>('a, 's, 'v) spec\<close> lattice via image and inverse image.

Note that the image may yield a set that is not stuttering closed
(i.e., we need to close the obvious model-level definition of
\<open>spec.map\<close> under stuttering) as arbitrary
\<open>sf\<close> may introduce stuttering not present in
\<open>P\<close>. In contrast the inverse image preserves stuttering. These
issues are elided here through the use of
\<^const>\<open>spec.singleton\<close>.

\<close>

setup \<open>Sign.mandatory_path "spec"\<close>

definition map :: "('a \<Rightarrow> 'b) \<Rightarrow> ('s \<Rightarrow> 't) \<Rightarrow> ('v \<Rightarrow> 'w) \<Rightarrow> ('a, 's, 'v) spec \<Rightarrow> ('b, 't, 'w) spec" where
  "map af sf vf P = \<Squnion>(spec.singleton ` trace.map af sf vf ` {\<sigma>. \<lblot>\<sigma>\<rblot> \<le> P})"

definition invmap :: "('a \<Rightarrow> 'b) \<Rightarrow> ('s \<Rightarrow> 't) \<Rightarrow> ('v \<Rightarrow> 'w) \<Rightarrow> ('b, 't, 'w) spec \<Rightarrow> ('a, 's, 'v) spec" where
  "invmap af sf vf P = \<Squnion>(spec.singleton ` trace.map af sf vf -` {\<sigma>. \<lblot>\<sigma>\<rblot> \<le> P})"

abbreviation amap ::"('a \<Rightarrow> 'b) \<Rightarrow> ('a, 's, 'v) spec \<Rightarrow> ('b, 's, 'v) spec" where
  "amap af \<equiv> spec.map af id id"
abbreviation ainvmap ::"('a \<Rightarrow> 'b) \<Rightarrow> ('b, 's, 'v) spec \<Rightarrow> ('a, 's, 'v) spec" where
  "ainvmap af \<equiv> spec.invmap af id id"
abbreviation smap ::"('s \<Rightarrow> 't) \<Rightarrow> ('a, 's, 'v) spec \<Rightarrow> ('a, 't, 'v) spec" where
  "smap sf \<equiv> spec.map id sf id"
abbreviation sinvmap ::"('s \<Rightarrow> 't) \<Rightarrow> ('a, 't, 'v) spec \<Rightarrow> ('a, 's, 'v) spec" where
  "sinvmap sf \<equiv> spec.invmap id sf id"
abbreviation vmap ::"('v \<Rightarrow> 'w) \<Rightarrow> ('a, 's, 'v) spec \<Rightarrow> ('a, 's, 'w) spec" where \<comment>\<open> aka \<open>liftM\<close> \<close>
  "vmap vf \<equiv> spec.map id id vf"
abbreviation vinvmap ::"('v \<Rightarrow> 'w) \<Rightarrow> ('a, 's, 'w) spec \<Rightarrow> ('a, 's, 'v) spec" where
  "vinvmap vf \<equiv> spec.invmap id id vf"

interpretation map_invmap: galois.complete_lattice_distributive_class
  "spec.map af sf vf"
  "spec.invmap af sf vf" for af sf vf
proof standard
  show "spec.map af sf vf P \<le> Q \<longleftrightarrow> P \<le> spec.invmap af sf vf Q" (is "?lhs \<longleftrightarrow> ?rhs") for P Q
  proof(rule iffI)
    show "?lhs \<Longrightarrow> ?rhs"
      by (fastforce simp: spec.map_def spec.invmap_def intro: spec.singleton_le_extI)
    show "?rhs \<Longrightarrow> ?lhs"
      by (fastforce simp: spec.map_def spec.invmap_def
                    dest: order.trans[of _ P] spec.singleton.map_le[where af=af and sf=sf and vf=vf])
  qed
  show "spec.invmap af sf vf (\<Squnion>X) \<le> \<Squnion>(spec.invmap af sf vf ` X)" for X
    by (fastforce simp: spec.invmap_def)
qed

setup \<open>Sign.mandatory_path "singleton"\<close>

lemma map_le_conv[spec.singleton.le_conv]:
  shows "\<lblot>\<sigma>\<rblot> \<le> spec.map af sf vf P \<longleftrightarrow> (\<exists>\<sigma>'. \<lblot>\<sigma>'\<rblot> \<le> P \<and> \<lblot>\<sigma>\<rblot> \<le> \<lblot>trace.map af sf vf \<sigma>'\<rblot>)"
by (simp add: spec.map_def)

lemma invmap_le_conv[spec.singleton.le_conv]:
  shows "\<lblot>\<sigma>\<rblot> \<le> spec.invmap af sf vf P \<longleftrightarrow> \<lblot>trace.map af sf vf \<sigma>\<rblot> \<le> P"
by (simp add: spec.invmap_def) (meson order.refl order.trans spec.singleton.map_le)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "map"\<close>

lemmas bot = spec.map_invmap.lower_bot

lemmas monotone = spec.map_invmap.monotone_lower
lemmas mono = monotoneD[OF spec.map.monotone]

lemmas Sup = spec.map_invmap.lower_Sup
lemmas sup = spec.map_invmap.lower_sup

lemmas Inf_le = spec.map_invmap.lower_Inf_le \<comment>\<open> Converse does not hold \<close>
lemmas inf_le = spec.map_invmap.lower_inf_le \<comment>\<open> Converse does not hold \<close>

lemmas invmap_le = spec.map_invmap.lower_upper_contractive

lemma singleton:
  shows "spec.map af sf vf \<lblot>\<sigma>\<rblot> = \<lblot>trace.map af sf vf \<sigma>\<rblot>"
by (auto simp: spec.map_def spec.eq_iff spec.singleton_le_conv intro: trace.natural.map_le)

lemma top:
  assumes "surj af"
  assumes "surj sf"
  assumes "surj vf"
  shows "spec.map af sf vf \<top> = \<top>"
by (rule antisym)
   (auto simp: assms spec.singleton.top spec.map.Sup spec.map.singleton surj_f_inv_f
        intro: exI[where x="trace.map (inv af) (inv sf) (inv vf) \<sigma>" for \<sigma>])

lemma id:
  shows "spec.map id id id P = P"
    and "spec.map (\<lambda>x. x) (\<lambda>x. x) (\<lambda>x. x) P = P"
by (simp_all add: spec.map_def flip: id_def)

lemma comp:
  shows "spec.map af sf vf \<circ> spec.map ag sg vg = spec.map (af \<circ> ag) (sf \<circ> sg) (vf \<circ> vg)" (is "?lhs = ?rhs")
    and "spec.map af sf vf (spec.map ag sg vg P) = spec.map (\<lambda>a. af (ag a)) (\<lambda>s. sf (sg s)) (\<lambda>v. vf (vg v)) P" (is ?thesis1)
proof -
  have "?lhs P = ?rhs P" for P
    by (rule spec.singleton.exhaust[where x=P])
       (simp add: spec.map.Sup spec.map.singleton image_image comp_def)
  then show "?lhs = ?rhs" and ?thesis1 by (simp_all add: comp_def)
qed

lemmas map = spec.map.comp

lemma inf_distr:
  shows "spec.map af sf vf P \<sqinter> Q = spec.map af sf vf (P \<sqinter> spec.invmap af sf vf Q)" (is "?lhs = ?rhs")
    and "Q \<sqinter> spec.map af sf vf P = spec.map af sf vf (spec.invmap af sf vf Q \<sqinter> P)" (is ?thesis1)
proof -
  show "?lhs = ?rhs"
  proof(rule antisym)
    obtain X where Q: "Q = \<Squnion> (spec.singleton ` X)" using spec.singleton.nchotomy[of Q] by blast
    then have *: "\<lblot>trace.take j (\<natural> \<sigma>\<^sub>Q)\<rblot> \<le> ?rhs"
           if "\<lblot>\<sigma>\<^sub>P\<rblot> \<le> P"
          and "\<sigma>\<^sub>Q \<in> X"
          and " \<natural> (trace.take i (trace.map af sf vf \<sigma>\<^sub>P)) = trace.take j (\<natural> \<sigma>\<^sub>Q)"
          for \<sigma>\<^sub>P \<sigma>\<^sub>Q i j
      using that
      by (auto simp: spec.singleton.le_conv spec.singleton_le_conv heyting.inf_SUP_distrib
                     spec.map_def spec.singleton.inf trace.less_eq_take_def
                     trace.take.map spec.singleton.takeI trace.take.take trace.natural.take_natural
             intro!: exI[where x="trace.take i \<sigma>\<^sub>P"] exI[where x=j])
    with Q show "?lhs \<le> ?rhs"
      by (subst spec.map_def)
         (fastforce simp: heyting.inf_SUP_distrib spec.singleton.inf trace.less_eq_take_def
                    elim: trace.take.naturalE(2))
    show "?rhs \<le> ?lhs"
      by (simp add: le_infI1 spec.map_invmap.galois spec.map_invmap.upper_lower_expansive)
  qed
  then show ?thesis1
    by (simp add: inf.commute)
qed

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "smap"\<close>

lemma comp:
  shows "spec.smap sf \<circ> spec.smap sg = spec.smap (sf \<circ> sg)"
    and "spec.smap sf (spec.smap sg P) = spec.smap (\<lambda>s. sf (sg s)) P"
by (simp_all add: comp_def spec.map.comp id_def)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "invmap"\<close>

lemmas bot = spec.map_invmap.upper_bot
lemmas top = spec.map_invmap.upper_top

lemmas monotone = spec.map_invmap.monotone_upper
lemmas mono = monotoneD[OF spec.invmap.monotone]

lemmas Sup = spec.map_invmap.upper_Sup
lemmas sup = spec.map_invmap.upper_sup

lemmas Inf = spec.map_invmap.upper_Inf
lemmas inf = spec.map_invmap.upper_inf

lemma singleton:
  shows "spec.invmap af sf vf \<lblot>\<sigma>\<rblot> = \<Squnion>(spec.singleton ` {\<sigma>'. \<lblot>trace.map af sf vf \<sigma>'\<rblot> \<le> \<lblot>\<sigma>\<rblot>})"
by (simp add: spec.invmap_def)

lemma id:
  shows "spec.invmap id id id P = P"
    and "spec.invmap (\<lambda>x. x) (\<lambda>x. x) (\<lambda>x. x) P = P"
unfolding id_def[symmetric] by (metis spec.map.id(1) spec.map_invmap.lower_upper_lower(2))+

lemma comp:
  shows "spec.invmap af sf vf (spec.invmap ag sg vg P) = spec.invmap (\<lambda>x. ag (af x)) (\<lambda>s. sg (sf s)) (\<lambda>v. vg (vf v)) P"  (is "?lhs P = ?rhs P")
    and "spec.invmap af sf vf \<circ> spec.invmap ag sg vg = spec.invmap (ag \<circ> af) (sg \<circ> sf) (vg \<circ> vf)" (is ?thesis1)
proof -
  show "?lhs P = ?rhs P" for P
    by (auto intro: spec.singleton.antisym spec.singleton_le_extI simp: spec.singleton.le_conv)
  then show ?thesis1
    by (simp add: fun_eq_iff comp_def)
qed

lemmas invmap = spec.invmap.comp

(* converse seems unlikely *)
lemma invmap_inf_distr_le:
  fixes af :: "'a \<Rightarrow> 'b"
  fixes sf :: "'s \<Rightarrow> 't"
  fixes vf :: "'v \<Rightarrow> 'w"
  shows "spec.invmap af sf vf P \<sqinter> Q \<le> spec.invmap af sf vf (P \<sqinter> spec.map af sf vf Q)"
    and "Q \<sqinter> spec.invmap af sf vf P \<le> spec.invmap af sf vf (spec.map af sf vf Q \<sqinter> P)"
by (metis order.refl inf_mono spec.map_invmap.upper_inf spec.map_invmap.upper_lower_expansive)+

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "amap"\<close>

lemma invmap_le: \<comment>\<open> \<open>af = id\<close> in \<open>spec.invmap\<close> \<close>
  shows "spec.amap af (spec.invmap id sf vf P) \<le> spec.invmap id sf vf (spec.amap af P)"
proof -
  have "spec.invmap id sf vf P \<le> spec.invmap af sf vf (spec.amap af P)" (is "?lhs \<le> ?rhs")
  proof(rule spec.singleton_le_extI)
    show "\<lblot>\<sigma>\<rblot> \<le> ?rhs" if "\<lblot>\<sigma>\<rblot> \<le> ?lhs" for \<sigma>
      using that by (simp add: spec.singleton.le_conv exI[where x="trace.map id sf vf \<sigma>"] flip: id_def)
  qed
  then show ?thesis
    by (simp add: spec.map_invmap.galois spec.invmap.comp flip: id_def)
qed

lemma surj_invmap: \<comment>\<open> \<open>af = id\<close> in \<open>spec.invmap\<close> \<close>
  fixes P :: "('a, 't, 'w) spec"
  fixes af :: "'a \<Rightarrow> 'b"
  fixes sf :: "'s \<Rightarrow> 't"
  fixes vf :: "'v \<Rightarrow> 'w"
  assumes "surj af"
  shows "spec.amap af (spec.invmap id sf vf P) = spec.invmap id sf vf (spec.amap af P)" (is "?lhs = ?rhs")
proof(rule antisym[OF spec.amap.invmap_le spec.singleton_le_extI])
  have 1: "\<exists>\<sigma>\<^sub>3. \<sigma>\<^sub>2 = trace.map af id id \<sigma>\<^sub>3 \<and> \<sigma>\<^sub>1 \<simeq>\<^sub>S \<sigma>\<^sub>3"
    if "trace.map af id id \<sigma>\<^sub>1 \<simeq>\<^sub>S \<sigma>\<^sub>2"
   for \<sigma>\<^sub>1 :: "('a, 't, 'w) trace.t" and \<sigma>\<^sub>2
  proof -
    have **: "\<exists>ys'. ys = map (map_prod af id) ys' \<and> trace.natural' s xs = trace.natural' s ys'"
      if "trace.natural' s (map (map_prod af id) xs) = trace.natural' s ys"
     for s :: "'t" and xs ys
      using that
    proof(induct ys arbitrary: s xs)
      case Nil then show ?case
        by (fastforce simp: trace.natural'.eq_Nil_conv)
    next
      case (Cons y ys s xs) show ?case
      proof(cases "snd y = s")
        case True with Cons.prems show ?thesis
          by (fastforce dest: Cons.hyps
                        simp: iffD1[OF surj_iff \<open>surj af\<close>]
                   simp flip: id_def
                       intro: exI[where x="map_prod (inv af) id y # ys'" for ys'])
      next
        case False with Cons.prems show ?thesis
          by (force dest!: Cons.hyps
                     simp: trace.natural'.eq_Cons_conv trace.natural'.idle_prefix
                           map_eq_append_conv snd_image_map_prod
                simp flip: id_def
                    intro: exI[where x="(a, s) # xs" for a s xs])
      qed
    qed
    from that show ?thesis
      by (cases \<sigma>\<^sub>2) (clarsimp simp: ** trace.natural_def trace.split_Ex)
  qed
  have 2: "\<exists>zs. xs = map (map_prod af id) zs \<and> map (map_prod id sf) zs = ys"
    if xs_ys: "map (map_prod id sf) xs = map (map_prod af id) ys"
   for xs ys
  proof -
    have "\<exists>zs. xs' = map (map_prod af id) zs \<and> map (map_prod id sf) zs = ys'"
      if "length xs' = length ys'"
     and "prefix xs' xs"
     and "prefix ys' ys"
     and "map (map_prod id sf) xs = map (map_prod af id) ys" for xs' ys'
      using that
    proof(induct xs' ys' rule: rev_induct2)
      case (snoc x xs y ys) then show ?case
        by (cases x; cases y)
           (force simp: prefix_def simp flip: id_def intro: exI[where x="zs @ [(fst y, snd x)]" for zs])
    qed simp
    from this[OF map_eq_imp_length_eq[OF xs_ys] prefix_order.refl prefix_order.refl xs_ys]
    show ?thesis .
  qed
  fix \<sigma>
  assume "\<lblot>\<sigma>\<rblot> \<le> ?rhs"
  then obtain \<sigma>\<^sub>P where \<sigma>\<^sub>P: "\<lblot>\<sigma>\<^sub>P\<rblot> \<le> P" "\<lblot>trace.map id sf vf \<sigma>\<rblot> \<le> \<lblot>trace.map af id id \<sigma>\<^sub>P\<rblot>"
    by (clarsimp simp: spec.singleton.le_conv)
  then obtain i \<sigma>\<^sub>P' where \<sigma>\<^sub>P': "trace.map id sf vf \<sigma> = trace.map af id id \<sigma>\<^sub>P'" "trace.take i \<sigma>\<^sub>P \<simeq>\<^sub>S \<sigma>\<^sub>P'"
    by (fastforce simp: spec.singleton_le_conv trace.less_eq_take_def trace.take.map
                  dest: 1[OF sym]
                 elim!: trace.take.naturalE)
  then obtain zs where zs: "trace.rest \<sigma> = map (map_prod af id) zs" "map (map_prod id sf) zs = trace.rest \<sigma>\<^sub>P'"
    by (cases \<sigma>, cases \<sigma>\<^sub>P') (clarsimp dest!: 2)
  from \<open>\<lblot>\<sigma>\<^sub>P\<rblot> \<le> P\<close> \<sigma>\<^sub>P'(1) \<sigma>\<^sub>P'(2)[symmetric] zs show "\<lblot>\<sigma>\<rblot> \<le> ?lhs"
    by (cases \<sigma>, cases \<sigma>\<^sub>P')
       (clarsimp intro!: exI[where x="trace.T (trace.init \<sigma>) zs (trace.term \<sigma>)"]
                  elim!: order.trans[rotated]
                   simp: spec.singleton.le_conv spec.singleton_le_conv trace.natural.mono)
qed

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.parent_path\<close>


subsection\<open> The idle process\label{sec:safety_logic-idle} \<close>

text\<open>

As observed by \<^citet>\<open>"AbadiPlotkin:1991"\<close>, many laws
require the processes involved to accept all initial states (see, for
instance, \S\ref{sec:safety_logic-monad_laws}). We call the minimal
such process \<open>spec.idle\<close>. It is also the lower bound on
specification by transition relation (\S\ref{sec:safety_logic-trans_rel}).

\<close>

setup \<open>Sign.mandatory_path "spec"\<close>

definition idle :: "('a, 's, 'v) spec" where
  "idle = (\<Squnion>s. \<lblot>s, [], None\<rblot>)"

named_theorems idle_le \<open> rules for \<open>spec.idle \<le> const \<dots>\<close> \<close>

setup \<open>Sign.mandatory_path "singleton"\<close>

lemma idle_le_conv[spec.singleton.le_conv]:
  shows "\<lblot>\<sigma>\<rblot> \<le> spec.idle \<longleftrightarrow> trace.steps \<sigma> = {} \<and> trace.term \<sigma> = None"
by (auto simp: spec.idle_def spec.singleton_le_conv trace.natural.simps trace.natural'.eq_Nil_conv
               trace.less_eq_None)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "idle"\<close>

lemma minimal_le:
  shows "\<lblot>s, [], None\<rblot> \<le> spec.idle"
by (simp add: spec.singleton.idle_le_conv)

lemma map_le[spec.idle_le]:
  assumes "spec.idle \<le> P"
  assumes "surj sf"
  shows "spec.idle \<le> spec.map af sf vf P"
by (strengthen ord_to_strengthen(2)[OF assms(1)])
   (use \<open>surj sf\<close> in \<open>auto simp: spec.idle_def spec.map.Sup spec.map.singleton image_image
                                 spec.singleton_le_conv trace.natural.simps trace.less_eq_None\<close>)

lemma invmap_le:
  assumes "spec.idle \<le> P"
  shows "spec.idle \<le> spec.invmap af sf vf P"
by (strengthen ord_to_strengthen(2)[OF assms])
   (auto simp: spec.idle_def spec.map.Sup spec.map.singleton simp flip: spec.map_invmap.galois)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "map_invmap"\<close>

lemma cl_alt_def:
  shows "spec.map_invmap.cl _ _ _ af sf vf P
       = \<Squnion>{\<lblot>\<sigma>\<rblot> |\<sigma> \<sigma>'. \<lblot>\<sigma>'\<rblot> \<le> P \<and> \<lblot>trace.map af sf vf \<sigma>\<rblot> \<le> \<lblot>trace.map af sf vf \<sigma>'\<rblot>}" (is "?lhs = ?rhs")
proof(rule antisym)
  show "?lhs \<le> ?rhs"
    by (rule spec.singleton.exhaust[of P])
       (fastforce simp: spec.map_invmap.cl_def
                        spec.map.Sup spec.map.singleton spec.invmap.Sup spec.invmap.singleton
                 intro: spec.singleton.mono)
  show "?rhs \<le> ?lhs"
    by (clarsimp simp: spec.map_invmap.cl_def simp flip: spec.map.singleton)
       (simp add: order.trans[OF _ spec.map.mono] flip: spec.map_invmap.galois)
qed

lemma cl_le_conv[spec.singleton.le_conv]:
  shows "\<lblot>\<sigma>\<rblot> \<le> spec.map_invmap.cl _ _ _ af sf vf P \<longleftrightarrow> \<lblot>trace.map af sf vf \<sigma>\<rblot> \<le> spec.map af sf vf P"
by (simp add: spec.map_invmap.cl_def spec.singleton.invmap_le_conv)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.parent_path\<close>


subsection\<open> Actions\label{sec:safety_logic-actions} \<close>

text\<open>

Our primitive actions are arbitrary relations on the state, labelled by the agent performing the
state transition and a value to return.

For refinement purposes we need \<open>idle \<le> action a F\<close>; see \S\ref{sec:refinement-action}.

\<close>

setup \<open>Sign.mandatory_path "spec"\<close>

definition action :: "('v \<times> 'a \<times> 's \<times> 's) set \<Rightarrow> ('a, 's, 'v) spec" where
  "action F = (\<Squnion>(v, a, s, s')\<in>F. \<lblot>s, [(a, s')], Some v\<rblot>) \<squnion> spec.idle"

definition guard :: "('s \<Rightarrow> bool) \<Rightarrow> ('a, 's, unit) spec" where
  "guard g = spec.action ({()} \<times> UNIV \<times> Diag g)"

definition return :: "'v \<Rightarrow> ('a, 's, 'v) spec" where
  "return v = spec.action ({v} \<times> UNIV \<times> Id)"

abbreviation (input) read :: "('s \<Rightarrow> 'v option) \<Rightarrow> ('a, 's, 'v) spec" where
  "read f \<equiv> spec.action {(v, a, s, s) |a s v. f s = Some v}"

abbreviation (input) "write" :: "'a \<Rightarrow> ('s \<Rightarrow> 's) \<Rightarrow> ('a, 's, unit) spec" where
  "write a f \<equiv> spec.action {((), a, s, f s) |s. True}"

lemma action_le[case_names idle step]:
  assumes "spec.idle \<le> P"
  assumes "\<And>v a s s'. (v, a, s, s') \<in> F \<Longrightarrow> \<lblot>s, [(a, s')], Some v\<rblot> \<le> P"
  shows "spec.action F \<le> P"
by (simp add: assms spec.action_def split_def)

setup \<open>Sign.mandatory_path "idle"\<close>

lemma action_le[spec.idle_le]:
  shows "spec.idle \<le> spec.action F"
by (simp add: spec.action_def)

lemma guard_le[spec.idle_le]:
  shows "spec.idle \<le> spec.guard g"
by (simp add: spec.guard_def spec.idle_le)

lemma return_le[spec.idle_le]:
  shows "spec.idle \<le> spec.return v"
by (simp add: spec.return_def spec.idle_le)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "map"\<close>

lemma action_le:
  fixes F :: "('v \<times> 'a \<times> 's \<times> 's) set"
  shows "spec.map af sf vf (spec.action F) \<le> spec.action (map_prod vf (map_prod af (map_prod sf sf)) ` F)"
by (force simp: spec.action_def spec.idle_def spec.map.Sup spec.map.sup spec.map.singleton SUP_le_iff)

lemma action:
  fixes F :: "('v \<times> 'a \<times> 's \<times> 's) set"
  shows "spec.map af sf vf (spec.action F) \<squnion> spec.idle
       = spec.action (map_prod vf (map_prod af (map_prod sf sf)) ` F)" (is "?lhs = ?rhs")
proof(rule antisym)
  show "?lhs \<le> ?rhs"
    by (simp add: spec.idle_le spec.map.action_le)
  show "?rhs \<le> ?lhs"
    by (force simp: spec.action_def spec.idle_def spec.map.sup spec.map.singleton spec.map.Sup)
qed

lemma surj_sf_action:
  assumes "surj sf"
  shows "spec.map af sf vf (spec.action F) = spec.action (map_prod vf (map_prod af (map_prod sf sf)) ` F)"
by (simp add: assms sup.absorb1 spec.idle_le flip: spec.map.action)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "action"\<close>

lemma empty:
  shows "spec.action {} = spec.idle"
by (simp add: spec.action_def)

lemma idleI:
  assumes "snd ` set xs \<subseteq> {s}"
  shows "\<lblot>s, xs, None\<rblot> \<le> spec.action F"
using assms by (simp add: spec.action_def spec.singleton.le_conv)

lemma stepI:
  assumes "(v, a, s, s') \<in> F"
  assumes "\<forall>v''. w = Some v'' \<longrightarrow> v'' = v"
  shows "\<lblot>s, [(a, s')], w\<rblot> \<le> spec.action F"
using assms by (cases w; force simp: spec.action_def spec.singleton.mono trace.less_eq_None)

lemma stutterI:
  assumes "(v, a, s, s) \<in> F"
  shows "\<lblot>s, [], Some v\<rblot> \<le> spec.action F"
by (fastforce simp: spec.singleton_le_conv trace.natural.simps
             intro: order.trans[OF _ spec.action.stepI[OF assms]])

lemma stutter_stepI:
  assumes "(v, a, s, s) \<in> F"
  shows "\<lblot>s, [(b, s)], Some v\<rblot> \<le> spec.action F"
by (fastforce simp: spec.singleton_le_conv trace.natural.simps
             intro: order.trans[OF _ spec.action.stepI[OF assms]])

lemma stutter_stepsI:
  assumes "(v, a, s, s) \<in> F"
  assumes "snd ` set xs \<subseteq> {s}"
  shows "\<lblot>s, xs, Some v\<rblot> \<le> spec.action F"
by (simp add: assms trace.natural'.eq_Nil_conv order.trans[OF _ spec.action.stutterI[OF assms(1)]])

lemma monotone:
  shows "mono spec.action"
by (force simp: spec.action_def intro: monoI)

lemmas strengthen[strg] = st_monotone[OF spec.action.monotone]
lemmas mono = monotoneD[OF spec.action.monotone]
lemmas mono2mono[cont_intro, partial_function_mono]
  = monotone2monotone[OF spec.action.monotone, simplified]

lemma Sup:
  shows "spec.action (\<Union>X) = (\<Squnion>F\<in>X. spec.action F) \<squnion> spec.idle"
by (force simp: spec.eq_iff spec.action_def)

lemma
  shows SUP: "spec.action (\<Union>x\<in>X. F x) = (\<Squnion>x\<in>X. spec.action (F x)) \<squnion> spec.idle"
    and SUP_not_empty: "X \<noteq> {} \<Longrightarrow> spec.action (\<Union>x\<in>X. F x) = (\<Squnion>x\<in>X. spec.action (F x))"
by (auto simp: spec.action.Sup image_image sup.absorb1 SUPI spec.idle_le simp flip: ex_in_conv)

lemma sup:
  shows "spec.action (F \<union> G) = spec.action F \<squnion> spec.action G"
using spec.action.Sup[where X="{F, G}"] by (simp add: sup_absorb1 le_supI1 spec.idle_le)

(* the converse is complex *)
lemma Inf_le:
  shows "spec.action (\<Inter>Fs) \<le> \<Sqinter>(spec.action ` Fs)"
by (simp add: spec.action_def ac_simps SUP_le_iff SUP_upper le_INF_iff le_supI2)

lemma inf_le:
  shows "spec.action (F \<inter> G) \<le> spec.action F \<sqinter> spec.action G"
using spec.action.Inf_le[where Fs="{F, G}"] by simp

lemma stutter_agents_le:
  assumes "\<lbrakk>A \<noteq> {}; r \<noteq> {}\<rbrakk> \<Longrightarrow> B \<noteq> {}"
  assumes "r \<subseteq> Id"
  shows "spec.action ({v} \<times> A \<times> r) \<le> spec.action ({v} \<times> B \<times> r)"
using assms
by (subst spec.action_def) (fastforce simp: spec.idle_le intro!: spec.action.stutter_stepI)

lemma read_agents:
  assumes "A \<noteq> {}"
  assumes "B \<noteq> {}"
  assumes "r \<subseteq> Id"
  shows "spec.action ({v} \<times> A \<times> r) = spec.action ({v} \<times> B \<times> r)"
by (rule antisym[OF spec.action.stutter_agents_le spec.action.stutter_agents_le]; rule assms)

lemma invmap_le: \<comment>\<open> A typical refinement \<close>
  fixes af :: "'a \<Rightarrow> 'b"
  fixes sf :: "'s \<Rightarrow> 't"
  fixes vf :: "'v \<Rightarrow> 'w"
  shows "spec.action (map_prod vf (map_prod af (map_prod sf sf)) -` F) \<le> spec.invmap af sf vf (spec.action F)"
by (meson order.trans image_vimage_subset spec.action.mono spec.map.action_le spec.map_invmap.galois)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "singleton"\<close>

lemma action_le_conv:
  shows "\<lblot>\<sigma>\<rblot> \<le> spec.action F
    \<longleftrightarrow> (trace.steps \<sigma> = {} \<and> case_option True (\<lambda>v. \<exists>a. (v, a, trace.init \<sigma>, trace.init \<sigma>) \<in> F) (trace.term \<sigma>))
     \<or> (\<exists>x\<in>F. trace.steps \<sigma> = {snd x} \<and> case_option True ((=) (fst x)) (trace.term \<sigma>))" (is "?lhs \<longleftrightarrow> ?rhs")
proof(rule iffI)
  show "?lhs \<Longrightarrow> ?rhs"
    unfolding spec.action_def spec.singleton.sup_le_conv
  proof(induct rule: disjE[consumes 1, case_names step idle])
    case step
    then obtain v a s s' where *: "\<natural>\<sigma> \<le> \<natural>(trace.T s [(a, s')] (Some v))" and F: "(v, a, s, s') \<in> F"
      by (clarsimp simp: spec.singleton_le_conv)
    from * show ?case
    proof(induct rule: trace.less_eqE)
      case prefix with F show ?case
        by (clarsimp simp add: trace.natural'.eq_Nil_conv prefix_Cons split: if_splits)
           (force simp: trace.steps'_alt_def)
    next
      case (maximal v) with F show ?case
        by (clarsimp simp: trace.natural.trace_conv trace.natural'.eq_Nil_conv
                           trace.natural'.eq_Cons_conv trace.steps'.append split: if_splits;
            force)
    qed
  qed (simp add: spec.singleton.le_conv)
  show "?rhs \<Longrightarrow> ?lhs"
    by (cases \<sigma>)
       (auto simp: trace.steps'.step_conv
            intro: spec.action.idleI spec.action.stutter_stepsI spec.action.stepI
            elim!: order.trans[OF eq_refl[OF spec.singleton.Cons]]
            split: option.split_asm)
qed

lemma action_Some_leE:
  assumes "\<lblot>\<sigma>\<rblot> \<le> spec.action F"
  assumes "trace.term \<sigma> = Some v"
  obtains x
    where "x \<in> F"
      and "trace.init \<sigma> = fst (snd (snd x))"
      and "trace.final \<sigma> = snd (snd (snd x))"
      and "trace.steps \<sigma> \<subseteq> {snd x}"
      and "v = fst x"
using assms by (auto simp: spec.singleton.action_le_conv trace.steps'.step_conv trace.steps'.append)

lemma action_not_idle_leE:
 assumes "\<lblot>\<sigma>\<rblot> \<le> spec.action F"
 assumes "\<natural>\<sigma> \<noteq> trace.T (trace.init \<sigma>) [] None"
 obtains x
 where "x \<in> F"
   and "trace.init \<sigma> = fst (snd (snd x))"
   and "trace.final \<sigma> = snd (snd (snd x))"
   and "trace.steps \<sigma> \<subseteq> {snd x}"
   and "case_option True ((=) (fst x)) (trace.term \<sigma>)"
 using assms
by (cases \<sigma>)
   (auto 0 0 simp: spec.singleton.action_le_conv trace.natural.idle option.case_eq_if
                   trace.steps'.step_conv trace.steps'.append)

lemma action_not_idle_le_splitE:
  assumes "\<lblot>\<sigma>\<rblot> \<le> spec.action F"
  assumes "\<natural>\<sigma> \<noteq> trace.T (trace.init \<sigma>) [] None"
  obtains (return) v a
          where "(v, a, trace.init \<sigma>, trace.init \<sigma>) \<in> F"
            and "trace.steps \<sigma> = {}"
            and "trace.term \<sigma> = Some v"
        | (step) v a ys zs
          where "(v, a, trace.init \<sigma>, trace.final \<sigma>) \<in> F"
            and "trace.init \<sigma> \<noteq> trace.final \<sigma>"
            and "snd ` set ys \<subseteq> {trace.init \<sigma>}"
            and "snd ` set zs \<subseteq> {trace.final \<sigma>}"
            and "trace.rest \<sigma> = ys @ [(a, trace.final \<sigma>)] @ zs"
            and "case_option True ((=) v) (trace.term \<sigma>)"
using assms
by (cases \<sigma>)
   (auto 0 0 simp: spec.singleton.action_le_conv trace.natural.idle option.case_eq_if
                    trace.steps'.step_conv trace.steps'.append
             cong: if_cong)

lemma guard_le_conv[spec.singleton.le_conv]:
  shows "\<lblot>\<sigma>\<rblot> \<le> spec.guard g \<longleftrightarrow> trace.steps \<sigma> = {} \<and> (case_option True \<langle>g (trace.init \<sigma>)\<rangle> (trace.term \<sigma>))"
by (fastforce simp: spec.guard_def spec.singleton.action_le_conv trace.steps'.step_conv
             split: option.split)

lemma return_le_conv[spec.singleton.le_conv]:
  shows "\<lblot>\<sigma>\<rblot> \<le> spec.return v
     \<longleftrightarrow> trace.steps \<sigma> = {} \<and> (case_option True ((=) v) (trace.term \<sigma>))"
by (fastforce simp: spec.return_def spec.singleton.action_le_conv trace.steps'.step_conv
             split: option.split)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "action"\<close>

lemma mono_stronger:
  assumes "\<And>v a s s'. \<lbrakk>(v, a, s, s') \<in> F; s \<noteq> s'\<rbrakk> \<Longrightarrow> (v, a, s, s') \<in> F'"
  assumes "\<And>v a s. (v, a, s, s) \<in> F \<Longrightarrow> \<exists>a'. (v, a', s, s) \<in> F'"
  shows "spec.action F \<le> spec.action F'"
proof (induct rule: spec.action_le[OF spec.idle.action_le, case_names step])
  case (step v a s s') then show ?case
    by (cases "s = s'")
       (auto dest: assms intro: spec.action.stutterI spec.action.stepI)
qed

lemma cong:
  assumes "\<And>v a s s'. s \<noteq> s' \<Longrightarrow> (v, a, s, s') \<in> F \<longleftrightarrow> (v, a, s, s') \<in> F'"
  assumes "\<And>v a s. (v, a, s, s) \<in> F \<Longrightarrow> \<exists>a'. (v, a', s, s) \<in> F'"
  assumes "\<And>v a s. (v, a, s, s) \<in> F' \<Longrightarrow> \<exists>a'. (v, a', s, s) \<in> F"
  shows "spec.action F = spec.action F'"
using assms by (blast intro!: spec.antisym spec.action.mono_stronger)

lemma le_actionD:
  assumes "spec.action F \<le> spec.action F'"
  shows "\<lbrakk>(v, a, s, s') \<in> F; s \<noteq> s'\<rbrakk> \<Longrightarrow> (v, a, s, s') \<in> F'"
    and "(v, a, s, s) \<in> F \<Longrightarrow> \<exists>a'. (v, a', s, s) \<in> F'"
proof -
  fix v a s s'
  show "(v, a, s, s') \<in> F'" if "(v, a, s, s') \<in> F" and "s \<noteq> s'"
    using iffD1[OF spec.singleton_le_ext_conv assms] that
    by (fastforce simp: spec.singleton.action_le_conv
                  dest: spec[where x="trace.T s [(a, s')] (Some v)"])
  show "\<exists>a'. (v, a', s, s) \<in> F'" if "(v, a, s, s) \<in> F"
    using iffD1[OF spec.singleton_le_ext_conv assms] that
    by (fastforce simp: spec.singleton.action_le_conv
                  dest: spec[where x="trace.T s [] (Some v)"])
qed

lemma eq_action_conv:
  shows "spec.action F = spec.action F'
    \<longleftrightarrow> (\<forall>v a s s'. s \<noteq> s' \<longrightarrow> (v, a, s, s') \<in> F \<longleftrightarrow> (v, a, s, s') \<in> F')
      \<and> (\<forall>v a s. (v, a, s, s) \<in> F \<longrightarrow> (\<exists>a'. (v, a', s, s) \<in> F'))
      \<and> (\<forall>v a s. (v, a, s, s) \<in> F' \<longrightarrow> (\<exists>a'. (v, a', s, s) \<in> F))"
by (rule iffI, metis order.refl spec.action.le_actionD, blast intro!: spec.action.cong)

setup \<open>Sign.parent_path\<close>

lemma return_alt_def:
  assumes "A \<noteq> {}"
  shows "spec.return v = spec.action ({v} \<times> A \<times> Id)"
unfolding spec.return_def using assms by (blast intro: spec.action.cong)

setup \<open>Sign.mandatory_path "return"\<close>

lemma cong:
  assumes "\<And>v a s s'. (v, a, s, s') \<in> F \<Longrightarrow> s' = s"
  assumes "\<And>v s. v \<in> fst ` F \<Longrightarrow> \<exists>a. (v, a, s, s) \<in> F"
  shows "spec.action F = \<Squnion>(spec.return ` fst ` F) \<squnion> spec.idle"
by (simp add: spec.return_def image_image flip: spec.action.SUP)
   (rule spec.action.cong; auto intro: rev_bexI dest: assms(1) intro: assms(2))

lemma action_le:
  assumes "Id \<subseteq> snd ` snd ` F"
  shows "spec.return () \<le> spec.action F"
unfolding spec.return_def
proof(induct rule: spec.action_le)
  case (step v a s s') with subsetD[OF assms, where c="(s, s)"] show ?case
    by (force intro: spec.action.stutterI)
qed (simp add: spec.idle_le)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "guard"\<close>

lemma alt_def:
  assumes "A \<noteq> {}"
  shows "spec.guard g = spec.action ({()} \<times> A \<times> Diag g)"
unfolding spec.guard_def using assms by (fastforce simp: intro: spec.action.cong)

lemma bot:
  shows "spec.guard \<bottom> = spec.idle"
    and "spec.guard \<langle>False\<rangle> = spec.idle"
by (simp_all add: spec.guard_def spec.action.empty)

lemma top:
  shows "spec.guard \<top> = spec.return ()"
    and "spec.guard \<langle>True\<rangle> = spec.return ()"
by (simp_all add: spec.guard_def spec.return_def flip: Id_def)

lemma monotone:
  shows "mono spec.guard"
proof(rule monotoneI)
  show "spec.guard g \<le> spec.guard g'" if "g \<le> g'" for g g' :: "'s pred"
    unfolding spec.guard_def by (strengthen ord_to_strengthen(1)[OF \<open>g \<le> g'\<close>]) simp
qed

lemmas strengthen[strg] = st_monotone[OF spec.guard.monotone]
lemmas mono = monotoneD[OF spec.guard.monotone]
lemmas mono2mono[cont_intro, partial_function_mono] = monotone2monotone[OF spec.guard.monotone, simplified]

lemma Sup:
  shows "spec.guard (\<Squnion>X) = \<Squnion>(spec.guard ` X) \<squnion> spec.idle"
by (auto simp: spec.guard_def Diag_Sup
    simp flip: spec.action.Sup[where X="(\<lambda>x. {()} \<times> UNIV \<times> Diag x) ` X", simplified image_image]
        intro: arg_cong[where f=spec.action])

lemma sup:
  shows "spec.guard (g \<squnion> h) = spec.guard g \<squnion> spec.guard h"
by (simp add: spec.guard.Sup[where X="{g, h}" for g h, simplified]
              ac_simps sup_absorb2 le_supI2 spec.idle_le)

lemma return_le:
  shows "spec.guard g \<le> spec.return ()"
by (simp add: spec.guard_def spec.return_def Sigma_mono spec.action.mono)

lemma guard_less: \<comment>\<open> Non-triviality \<close>
  assumes "g < g'"
  shows "spec.guard g < spec.guard g'"
proof(rule le_neq_trans)
  show "spec.guard g \<le> spec.guard g'"
    by (strengthen ord_to_strengthen(1)[OF order_less_imp_le[OF assms]]) simp
  from assms obtain s where "g' s" "\<not>g s" by (metis leD predicate1I)
  from \<open>\<not>g s\<close> have "\<not>\<lblot>s, [], Some ()\<rblot> \<le> spec.guard g"
    by (clarsimp simp: spec.guard_def spec.action_def
                       spec.singleton_le_conv spec.singleton.le_conv trace.natural.simps)
  moreover
  from \<open>g' s\<close> have "\<lblot>s, [], Some ()\<rblot> \<le> spec.guard g'"
    by (simp add: spec.guard_def spec.action.stutterI)
  ultimately show "spec.guard g \<noteq> spec.guard g'" by metis
qed

lemma cong:
  assumes "\<And>v a s s'. (v, a, s, s') \<in> F \<Longrightarrow> s' = s"
  shows "spec.action F = spec.guard (\<lambda>s. s \<in> fst ` snd ` snd ` F)" (is "?lhs = ?rhs")
proof(rule antisym)
  show "?lhs \<le> ?rhs"
    by (force simp: spec.guard_def intro: spec.action.mono dest: assms)
  show "?rhs \<le> ?lhs"
    unfolding spec.guard_def
    by (rule spec.action_le;
        clarsimp simp: spec.idle_le; blast intro: spec.action.stutterI dest: assms)
qed

lemma action_le:
  assumes "Diag g \<subseteq> snd ` snd ` F"
  shows "spec.guard g \<le> spec.action F"
unfolding spec.guard_def
proof(induct rule: spec.action_le)
  case (step v a s s') with subsetD[OF assms, where c="(s, s)"] show ?case
    by (force intro: spec.action.stutterI)
qed (simp add: spec.idle_le)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.parent_path\<close>


subsection\<open> Operations on return values\label{sec:safety_logic-return_values} \<close>

text\<open>

For various purposes, including defining a history-respecting
sequential composition (bind, see \S\ref{sec:safety_logic-bind}), we
use a Galois pair of operations that saturate or eradicate return
values.

\<close>

setup \<open>Sign.mandatory_path "spec"\<close>

setup \<open>Sign.mandatory_path "term"\<close>

definition none :: "('a, 's, 'v) spec \<Rightarrow> ('a, 's, 'w) spec" where
  "none P = \<Squnion>{\<lblot>s, xs, None\<rblot> |s xs v. \<lblot>s, xs, v\<rblot> \<le> P}"

definition all :: "('a, 's, 'v) spec \<Rightarrow> ('a, 's, 'w) spec" where
  "all P = \<Squnion>{\<lblot>s, xs, v\<rblot> |s xs v. \<lblot>s, xs, None\<rblot> \<le> P}"

setup \<open>Sign.parent_path\<close>

interpretation "term": galois.complete_lattice_distributive_class spec.term.none spec.term.all
proof standard
  show "spec.term.none P \<le> Q \<longleftrightarrow> P \<le> spec.term.all Q" (is "?lhs \<longleftrightarrow> ?rhs")
   for P :: "('a, 'b, 'c) spec"
   and  Q :: "('a, 'b, 'f) spec"
  proof(rule iffI)
    show "?lhs \<Longrightarrow> ?rhs"
      by (fastforce simp: spec.term.none_def spec.term.all_def trace.split_all
                   intro: spec.singleton_le_extI)
    show "?rhs \<Longrightarrow> ?lhs"
      by (fastforce simp: spec.term.none_def spec.term.all_def
                          spec.singleton_le_conv trace.natural_def trace.less_eq_None
                    elim: trace.less_eqE order.trans[rotated]
                    dest: order.trans[of _ P])
  qed
  show "spec.term.all (\<Squnion> X) \<le> \<Squnion> (spec.term.all ` X)" for X :: "('a, 'b, 'f) spec set"
    by (auto 0 5 simp: spec.term.all_def)
qed

setup \<open>Sign.mandatory_path "singleton.term"\<close>

lemma none_le_conv[spec.singleton.le_conv]:
  shows "\<lblot>\<sigma>\<rblot> \<le> spec.term.none P \<longleftrightarrow> trace.term \<sigma> = None \<and> \<lblot>trace.init \<sigma>, trace.rest \<sigma>, None\<rblot> \<le> P" (is "?lhs \<longleftrightarrow> ?rhs")
proof(rule iffI)
  show "?lhs \<Longrightarrow> ?rhs"
    by (fastforce simp: spec.term.none_def trace.natural_def spec.singleton_le_conv trace.less_eq_None
                 intro: order.trans[rotated])
  show "?rhs \<Longrightarrow> ?lhs"
    by (cases \<sigma>) (fastforce simp: spec.term.none_def)
qed

lemma all_le_conv[spec.singleton.le_conv]:
  shows "\<lblot>\<sigma>\<rblot> \<le> spec.term.all P \<longleftrightarrow> (\<exists>w. \<lblot>trace.init \<sigma>, trace.rest \<sigma>, w\<rblot> \<le> P)" (is "?lhs \<longleftrightarrow> ?rhs")
proof(rule iffI)
  show "?lhs \<Longrightarrow> ?rhs"
    by (cases \<sigma>) (fastforce simp: spec.term.none_def simp flip: spec.term.galois)
  show "?rhs \<Longrightarrow> ?lhs"
    by (cases \<sigma>) (fastforce simp: spec.term.all_def intro: order.trans[rotated])
qed

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "term"\<close>

setup \<open>Sign.mandatory_path "none"\<close>

lemma singleton:
  shows "spec.term.none \<lblot>\<sigma>\<rblot> = \<lblot>trace.init \<sigma>, trace.rest \<sigma>, None\<rblot>"
by (force simp: spec.eq_iff spec.term.galois spec.singleton.le_conv spec.singleton.mono trace.less_eq_None)

lemmas bot[simp] = spec.term.lower_bot

lemmas monotone = spec.term.monotone_lower
lemmas mono = monotoneD[OF spec.term.none.monotone]

lemmas Sup = spec.term.lower_Sup
lemmas sup = spec.term.lower_sup

lemmas Inf_le = spec.term.lower_Inf_le

lemma Inf_not_empty:
  assumes "X \<noteq> {}"
  shows "spec.term.none (\<Sqinter>X) = (\<Sqinter>x\<in>X. spec.term.none x)"
by (rule antisym[OF spec.term.lower_Inf_le])
   (use assms in \<open>auto intro: spec.singleton_le_extI simp: spec.singleton.term.none_le_conv le_Inf_iff\<close>)

lemma inf:
  shows "spec.term.none (P \<sqinter> Q) = spec.term.none P \<sqinter> spec.term.none Q"
    and "spec.term.none (Q \<sqinter> P) = spec.term.none Q \<sqinter> spec.term.none P"
using spec.term.none.Inf_not_empty[where X="{P, Q}"] by (simp_all add: ac_simps)

lemma inf_unit:
  fixes P Q :: "(_, _, unit) spec"
  shows "spec.term.none (P \<sqinter> Q) = spec.term.none P \<sqinter> Q" (is "?thesis1 P Q")
    and "spec.term.none (P \<sqinter> Q) = P \<sqinter> spec.term.none Q" (is ?thesis2)
proof -
  show *: "?thesis1 P Q" for P Q
    by (rule spec.singleton.antisym; metis le_inf_iff spec.singleton.term.none_le_conv trace.t.collapse)
  from *[where P=Q and Q=P] show ?thesis2
    by (simp add: ac_simps)
qed

lemma idempotent[simp]:
  shows "spec.term.none (spec.term.none P) = spec.term.none P"
by (rule spec.singleton.exhaust[of P])
   (simp add: spec.term.none.Sup spec.term.none.singleton image_image)

lemma contractive[iff]:
  shows "spec.term.none P \<le> P"
by (rule spec.singleton_le_extI) (simp add: spec.singleton.le_conv trace.split_all)

lemma map_gen:
  fixes vf :: "'v \<Rightarrow> 'w"
  fixes vf' :: "'a \<Rightarrow> 'b" \<comment>\<open> arbitrary type \<close>
  shows "spec.term.none (spec.map af sf vf P) = spec.map af sf vf' (spec.term.none P)" (is "?lhs = ?rhs")
by (fastforce simp: spec.map_def spec.eq_iff image_image trace.split_all trace.split_Ex
                    spec.term.none.Sup spec.term.none.singleton spec.singleton.term.none_le_conv
              elim: order.trans[rotated])

lemmas map = spec.term.none.map_gen[where vf'=id] \<comment>\<open> \<open>simp\<close>-friendly \<close>

lemma invmap_gen:
  fixes vf :: "'v \<Rightarrow> 'w"
  fixes vf' :: "'a \<Rightarrow> 'b" \<comment>\<open> arbitrary type \<close>
  shows "spec.term.none (spec.invmap af sf vf P) = spec.invmap af sf vf' (spec.term.none P)" (is "?lhs = ?rhs")
proof(rule antisym)
  show "?lhs \<le> ?rhs"
    by (simp add: spec.map_invmap.lower_upper_contractive spec.term.none.mono
            flip: spec.map_invmap.galois spec.term.none.map_gen[where vf=vf])
  show "?rhs \<le> ?lhs"
    by (rule spec.singleton_le_extI)
       (clarsimp simp: spec.singleton.invmap_le_conv spec.singleton.term.none_le_conv)
qed

lemmas invmap = spec.term.none.invmap_gen[where vf'=id] \<comment>\<open> \<open>simp\<close>-friendly \<close>

lemma idle:
  shows "spec.term.none spec.idle = spec.idle"
by (simp add: spec.idle_def spec.term.none.Sup spec.term.none.singleton image_image)

lemma return:
  shows "spec.term.none (spec.return v) = spec.idle"
by (auto simp: spec.eq_iff spec.return_def spec.action_def spec.term.none.idle spec.singleton.idle_le_conv
               spec.term.none.sup spec.term.none.Sup spec.term.none.singleton)

lemma guard:
  shows "spec.term.none (spec.guard g) = spec.idle"
by (rule antisym[OF spec.term.none.mono[OF spec.guard.return_le, simplified spec.term.none.return]
                    spec.term.none.mono[OF spec.idle.guard_le, simplified spec.term.none.idle]])

setup \<open>Sign.parent_path\<close>

lemma none_all_le:
  shows "spec.term.none P \<le> spec.term.all P"
using spec.term.galois by fastforce

lemma none_all[simp]:
  shows "spec.term.none (spec.term.all P) = spec.term.none P"
by (metis spec.eq_iff spec.term.lower_upper_contractive
          spec.term.none.idempotent spec.term.none.mono spec.term.none_all_le)

lemma all_none[simp]:
  shows "spec.term.all (spec.term.none P) = spec.term.all P"
by (metis spec.eq_iff spec.term.galois spec.term.none_all)

setup \<open>Sign.mandatory_path "all"\<close>

lemmas bot[simp] = spec.term.upper_bot

lemmas top = spec.term.upper_top

lemmas monotone = spec.term.monotone_upper
lemmas mono = monotoneD[OF spec.term.all.monotone]

lemma expansive:
  shows "P \<le> spec.term.all P"
using spec.term.galois by blast

lemmas Sup = spec.term.upper_Sup
lemmas sup = spec.term.upper_sup

lemmas Inf = spec.term.upper_Inf
lemmas inf = spec.term.upper_inf

lemmas singleton = spec.term.all_def[where P="\<lblot>\<sigma>\<rblot>"] for \<sigma>

lemma monomorphic:
  shows "spec.term.cl _ = spec.term.all"
unfolding spec.term.cl_def by simp

lemma closed_conv:
  assumes "P \<in> spec.term.closed _"
  shows "P = spec.term.all P"
using assms spec.term.closed_conv by (auto simp: spec.term.all.monomorphic)

lemma closed[iff]:
  shows "spec.term.all P \<in> spec.term.closed _"
using spec.term.closed_upper by (auto simp: spec.term.all.monomorphic)

lemma idempotent[simp]:
  shows "spec.term.all (spec.term.all P) = spec.term.all P"
by (metis antisym spec.term.galois spec.term.lower_upper_contractive spec.term.none.idempotent)

lemma map: \<comment>\<open> \<open>vf = id\<close> on the RHS \<close>
  fixes vf :: "'v \<Rightarrow> 'w"
  shows "spec.term.all (spec.map af sf vf P) = spec.map af sf id (spec.term.all P)" (is "?lhs = ?rhs")
proof(rule antisym[OF spec.singleton_le_extI])
  fix \<sigma>
  assume "\<lblot>\<sigma>\<rblot> \<le> ?lhs"
  then obtain \<sigma>' i w
    where "\<lblot>\<sigma>'\<rblot> \<le> P"
      and "trace.T (trace.init \<sigma>) (trace.rest \<sigma>) w \<simeq>\<^sub>S trace.map af sf vf (trace.take i \<sigma>')"
    using that by (fastforce elim!: trace.less_eq_takeE trace.take.naturalE
                              simp: trace.take.map spec.singleton.le_conv spec.singleton_le_conv)
  then show "\<lblot>\<sigma>\<rblot> \<le> ?rhs"
    by (simp add: spec.singleton.le_conv spec.singleton_le_conv)
       (fastforce intro: exI[where x="trace.T (trace.init \<sigma>') (trace.rest (trace.take i \<sigma>')) (trace.term \<sigma>)"]
                         exI[where x=None]
                   elim: order.trans[rotated]
                   simp: trace.natural_def spec.singleton.mono trace.less_eq_None take_is_prefix)
next
  show "?rhs \<le> ?lhs"
    by (simp add: spec.term.none.map flip: spec.term.galois)
       (simp flip: spec.term.none.map[where vf=vf])
qed

lemma invmap: \<comment>\<open> \<open>vf = id\<close> on the RHS \<close>
  fixes vf :: "'v \<Rightarrow> 'w"
  shows "spec.term.all (spec.invmap af sf vf P) = spec.invmap af sf id (spec.term.all P)" (is "?lhs = ?rhs")
proof(rule antisym)
  show "?lhs \<le> ?rhs"
    by (simp add: order.trans[OF spec.term.none.contractive spec.map_invmap.lower_upper_contractive]
            flip: spec.map_invmap.galois spec.term.galois spec.term.all.map[where vf=vf])
  show "?rhs \<le> ?lhs"
    by (simp add: spec.term.none.invmap flip: spec.term.galois)
       (simp flip: spec.term.none.invmap_gen[where vf=vf])
qed

lemma vmap_unit_absorb:
  shows "spec.vmap \<langle>()\<rangle> (spec.term.all P) = spec.term.all P" (is "?lhs = ?rhs")
proof(rule antisym[OF _ spec.singleton_le_extI])
  show "?lhs \<le> ?rhs"
    by (simp add: spec.term.none.map spec.map.id flip: spec.term.galois)
  show "\<lblot>\<sigma>\<rblot> \<le> ?lhs" if "\<lblot>\<sigma>\<rblot> \<le> ?rhs" for \<sigma>
    using that
    by (clarsimp simp: spec.singleton.le_conv
               intro!: exI[where x="trace.map id id \<langle>undefined\<rangle> \<sigma>"])
       (metis (mono_tags) order.refl fun_unit_id trace.t.map_ident)
qed

lemma vmap_unit:
  shows "spec.vmap \<langle>()\<rangle> (spec.term.all P) = spec.term.all (spec.vmap \<langle>()\<rangle> P)"
by (simp add: spec.map.id spec.term.all.map spec.term.all.vmap_unit_absorb)

lemma idle:
  shows "spec.term.all spec.idle = (\<Squnion>v. spec.return v)" (is "?lhs = ?rhs")
proof(rule antisym)
  show "?lhs \<le> ?rhs"
    by (clarsimp simp: spec.term.all_def spec.singleton.le_conv option.case_eq_if)
  show "?rhs \<le> ?lhs"
    by (simp add: spec.term.none.Sup spec.term.none.return flip: spec.term.galois)
qed

lemma action:
  fixes F :: "('v \<times> 'a \<times> 's \<times> 's) set"
  shows "spec.term.all (spec.action F) = spec.action (UNIV \<times> snd ` F) \<squnion> (\<Squnion>v. spec.return v)" (is "?lhs = ?rhs")
proof(rule antisym)
  show "?lhs \<le> ?rhs"
    by (clarsimp simp: spec.term.all_def spec.singleton.le_conv spec.singleton.action_le_conv
                split: option.split)
       meson
  show "?rhs \<le> ?lhs"
    by (force simp: spec.action_def spec.idle_le spec.term.none.idle spec.term.none.return
                    spec.term.none.Sup spec.term.none.sup spec.term.none.singleton
         simp flip: spec.term.galois)
qed

lemma return:
  shows "spec.term.all (spec.return v) = (\<Squnion>v. spec.return v)"
by (auto simp: spec.return_def spec.term.all.action
    simp flip: spec.action.SUP_not_empty spec.action.sup
        intro: arg_cong[where f="spec.action"])

lemma guard:
  shows "spec.term.all (spec.guard g) = (\<Squnion>v. spec.return v)"
by (simp add: spec.eq_iff spec.idle.guard_le spec.term.none.Sup spec.term.none.return
              spec.term.all.mono[OF spec.guard.return_le, unfolded spec.term.all.return]
        flip: spec.term.galois)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "idle.term"\<close>

lemma none_le_conv[spec.idle_le]:
  shows "spec.idle \<le> spec.term.none P \<longleftrightarrow> spec.idle \<le> P"
by (metis spec.term.all.monomorphic spec.term.cl_def spec.term.galois spec.term.none.idle)

lemma all_le_conv[spec.idle_le]:
  shows "spec.idle \<le> spec.term.all P \<longleftrightarrow> spec.idle \<le> P"
by (simp add: spec.term.none.idle flip: spec.term.galois)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "term.closed"\<close>

lemma return_unit:
  shows "spec.return () \<in> spec.term.closed _"
by (rule spec.term.closed_clI) (simp add: spec.term.all.return spec.term.all.monomorphic)

lemma none_inf:
  fixes P :: "('a, 's, 'v) spec"
  fixes Q :: "('a, 's, 'w) spec"
  assumes "P \<in> spec.term.closed _"
  shows "P \<sqinter> spec.term.none Q = spec.term.none (spec.term.none P \<sqinter> Q)" (is "?lhs = ?rhs")
    and "spec.term.none Q \<sqinter> P = spec.term.none (Q \<sqinter> spec.term.none P)" (is ?thesis1)
proof -
  show "?lhs = ?rhs"
  proof(rule antisym[OF spec.singleton_le_extI])
    show "\<lblot>\<sigma>\<rblot> \<le> ?rhs" if "\<lblot>\<sigma>\<rblot> \<le> ?lhs" for \<sigma>
      using that by (cases \<sigma>) (simp add: spec.singleton.le_conv)
    show "?rhs \<le> ?lhs"
      by (auto simp: spec.term.galois intro: le_infI1 le_infI2 spec.term.none_all_le spec.term.all.expansive)
  qed
  then show ?thesis1
    by (simp add: ac_simps)
qed

lemma none_inf_monomorphic:
  fixes P :: "('a, 's, 'v) spec"
  fixes Q :: "('a, 's, 'v) spec"
  assumes "P \<in> spec.term.closed _"
  shows "P \<sqinter> spec.term.none Q = spec.term.none (P \<sqinter> Q)" (is ?thesis1)
    and "spec.term.none Q \<sqinter> P = spec.term.none (Q \<sqinter> P)" (is ?thesis2)
by (simp_all add: spec.term.closed.none_inf[OF assms, simplified] spec.term.none.inf)

lemma singleton_le_extI:
  assumes "Q \<in> spec.term.closed _"
  assumes "\<And>s xs. \<lblot>s, xs, None\<rblot> \<le> P \<Longrightarrow> \<lblot>s, xs, None\<rblot> \<le> Q"
  shows "P \<le> Q"
by (subst spec.term.closed_conv[OF assms(1)], rule spec.singleton_le_extI)
   (auto simp: trace.split_all spec.term.none.singleton spec.term.all.monomorphic
    simp flip: spec.term.galois
        intro: assms(2)
         elim: order.trans[rotated])

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.parent_path\<close>


subsection\<open> Bind\label{sec:safety_logic-bind} \<close>

text\<open>

We define monadic \<open>bind\<close> in terms of bi-strict \<open>continue\<close>. The latter supports left and right residuals
(see, amongst many others, \<^citet>\<open>"HoareHe:1987" and "HoareHeSanders:1987" and "Pratt:1990"\<close>), whereas
\<open>bind\<close> encodes the non-retractability of observable actions, i.e., \<open>spec.term.none f \<le> f \<bind> g\<close>, which
defeats a general right residual.

It is tempting to write this in a more direct style (using \<^const>\<open>case_option\<close>) but the set comprehension
syntax is not friendly to strengthen/monotonicity facts.

\<close>

setup \<open>Sign.mandatory_path "spec"\<close>

definition continue :: "('a, 's, 'v) spec \<Rightarrow> ('v \<Rightarrow> ('a, 's, 'w) spec) \<Rightarrow> ('a, 's, 'w) spec" where
  "continue f g =
    \<Squnion>{\<lblot>trace.init \<sigma>\<^sub>f, trace.rest \<sigma>\<^sub>f @ trace.rest \<sigma>\<^sub>g, trace.term \<sigma>\<^sub>g\<rblot>
        |\<sigma>\<^sub>f \<sigma>\<^sub>g v. \<lblot>\<sigma>\<^sub>f\<rblot> \<le> f \<and> trace.init \<sigma>\<^sub>g = trace.final \<sigma>\<^sub>f \<and> trace.term \<sigma>\<^sub>f = Some v \<and> \<lblot>\<sigma>\<^sub>g\<rblot> \<le> g v}"

definition bind :: "('a, 's, 'v) spec \<Rightarrow> ('v \<Rightarrow> ('a, 's, 'w) spec) \<Rightarrow> ('a, 's, 'w) spec" where
  "bind f g = spec.term.none f \<squnion> spec.continue f g"

adhoc_overloading
  Monad_Syntax.bind spec.bind

setup \<open>Sign.mandatory_path "singleton"\<close>

lemma continue_le_conv:
  shows "\<lblot>\<sigma>\<rblot> \<le> spec.continue f g
    \<longleftrightarrow> (\<exists>xs ys v w. \<lblot>trace.init \<sigma>, xs, Some v\<rblot> \<le> f
                   \<and> \<lblot>trace.final' (trace.init \<sigma>) xs, ys, w\<rblot> \<le> g v
                   \<and> \<sigma> \<le> trace.T (trace.init \<sigma>) (xs @ ys) w)" (is "?lhs \<longleftrightarrow> ?rhs")
proof(rule iffI)
  assume ?lhs
  then obtain s xs ys v w
        where \<sigma>: "\<natural>\<sigma> \<le> \<natural>(trace.T s (xs @ ys) w)"
          and f: "\<lblot>s, xs, Some v\<rblot> \<le> f"
          and g: "\<lblot>trace.final' s xs, ys, w\<rblot> \<le> g v"
    by (clarsimp simp: spec.continue_def trace.split_all spec.singleton_le_conv)
  from \<sigma> show ?rhs
  proof(cases rule: trace.less_eqE)
    case prefix
    from prefix(3)[simplified, simplified trace.natural'.append] show ?thesis
    proof(cases rule: prefix_append_not_NilE)
      case incomplete
      then obtain zs where zs: "trace.natural' s xs = trace.natural' (trace.init \<sigma>) (trace.rest \<sigma>) @ zs"
        by (rule prefixE)
      from f prefix(2) zs
      have "\<lblot>trace.init \<sigma>, trace.rest \<sigma> @ zs, Some v\<rblot> \<le> f"
        by (clarsimp elim!: order.trans[rotated])
           (metis trace.natural'.append trace.final'.natural' trace.natural'.natural')
      moreover
      from g prefix(2) zs
      have "\<lblot>trace.final' (trace.init \<sigma>) (trace.rest \<sigma> @ zs), ys, None\<rblot> \<le> g v"
        by (clarsimp elim!: order.trans[rotated])
           (metis spec.singleton.less_eq_None trace.final'.natural' trace.final'.simps(3))
      moreover note \<open>trace.term (\<natural>\<sigma>) = None\<close>
      ultimately show ?thesis
        by (fastforce simp: trace.less_eq_None)
    next
      case (continue us)
      from continue(1)
      obtain ys' zs'
        where "trace.rest \<sigma> = ys' @ zs'"
          and "trace.natural' (trace.init \<sigma>) ys' = trace.natural' s xs"
          and "trace.natural' (trace.final' (trace.init \<sigma>) (trace.natural' s xs)) zs' = us"
        by (clarsimp simp: trace.natural'.eq_append_conv)
      with f g prefix(1,2) continue(2-) show ?thesis
        by - (rule exI[where x="ys'"];
              force simp: spec.singleton_le_conv trace.less_eq_None trace.natural_def
                    cong: trace.final'.natural'_cong
                   elim!: order.trans[rotated]
                   intro: exI[where x="None"])
    qed
  next
    case (maximal x) with f g show ?thesis
      by (fastforce simp: trace.stuttering.equiv.append_conv
                    cong: trace.final'.natural'_cong
                   elim!: order.trans[rotated])
  qed
next
  show "?rhs \<Longrightarrow> ?lhs"
    using spec.singleton.mono by (auto 10 0 simp: spec.continue_def trace.split_Ex)
qed

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "continue"\<close>

lemma mono:
  assumes "f \<le> f'"
  assumes "\<And>v. g v \<le> g' v"
  shows "spec.continue f g \<le> spec.continue f' g'"
unfolding spec.continue_def
apply (strengthen ord_to_strengthen(1)[OF assms(1)])
apply (strengthen ord_to_strengthen(1)[OF assms(2)])
apply (rule order.refl)
done

lemma strengthen[strg]:
  assumes "st_ord F f f'"
  assumes "\<And>x. st_ord F (g x) (g' x)"
  shows "st_ord F (spec.continue f g) (spec.continue f' g')"
using assms by (cases F; simp add: spec.continue.mono)

lemma mono2mono[cont_intro, partial_function_mono]:
  assumes "monotone orda (\<le>) f"
  assumes "\<And>x. monotone orda (\<le>) (\<lambda>y. g y x)"
  shows "monotone orda (\<le>) (\<lambda>x. spec.continue (f x) (g x))"
using assms by (simp add: monotone_def spec.continue.mono)

definition resL :: "('v \<Rightarrow> ('a, 's, 'w) spec) \<Rightarrow> ('a, 's, 'w) spec \<Rightarrow> ('a, 's, 'v) spec" where
  "resL g P = \<Squnion>{f. spec.continue f g \<le> P}"

definition resR :: "('a, 's, 'v) spec \<Rightarrow> ('a, 's, 'w) spec \<Rightarrow> ('v \<Rightarrow> ('a, 's, 'w) spec)" where
  "resR f P = \<Squnion>{g. spec.continue f g \<le> P}"

interpretation L: galois.complete_lattice_class "\<lambda>f. spec.continue f g" "spec.continue.resL g" for g
proof
  show "spec.continue f g \<le> P \<longleftrightarrow> f \<le> spec.continue.resL g P" (is "?lhs \<longleftrightarrow> ?rhs") for f P
  proof(rule iffI)
    assume ?rhs
    then have "spec.continue f g \<le> spec.continue (spec.continue.resL g P) g"
      by (simp add: spec.continue.mono)
    also have "\<dots> \<le> P"
      by (auto simp: spec.continue.resL_def spec.continue_def)
    finally show ?lhs .
  qed (simp add: spec.continue.resL_def Sup_upper)
qed

interpretation R: galois.complete_lattice_class "\<lambda>g. spec.continue f g" "spec.continue.resR f"
  for f :: "('a, 's, 'v) spec"
proof
  show "spec.continue f g \<le> P \<longleftrightarrow> g \<le> spec.continue.resR f P" (is "?lhs \<longleftrightarrow> ?rhs")
   for g :: "'v \<Rightarrow> ('a, 's, 'w) spec"
   and P :: "('a, 's, 'w) spec"
  proof(rule iffI)
    assume ?rhs
    then have "spec.continue f g \<le> spec.continue f (spec.continue.resR f P)"
      by (simp add: le_fun_def spec.continue.mono)
    also have "\<dots> \<le> P"
      by (auto simp: spec.continue.resR_def spec.continue_def)
    finally show ?lhs .
  qed (simp add: spec.continue.resR_def Sup_upper)
qed

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "singleton"\<close>

lemma bind_le_conv:
  shows "\<lblot>\<sigma>\<rblot> \<le> spec.bind f g \<longleftrightarrow> \<lblot>\<sigma>\<rblot> \<le> spec.term.none f \<or> \<lblot>\<sigma>\<rblot> \<le> spec.continue f g"
by (simp add: spec.bind_def)

lemma bind_le[consumes 1]:
  assumes "\<lblot>\<sigma>\<rblot> \<le> f \<bind> g"
  obtains
    (incomplete) "\<lblot>\<sigma>\<rblot> \<le> spec.term.none f"
  | (continue) \<sigma>\<^sub>f \<sigma>\<^sub>g v\<^sub>f
    where "\<lblot>\<sigma>\<^sub>f\<rblot> \<le> f" and "trace.final \<sigma>\<^sub>f = trace.init \<sigma>\<^sub>g" and "trace.term \<sigma>\<^sub>f = Some v\<^sub>f"
      and "\<lblot>\<sigma>\<^sub>g\<rblot> \<le> g v\<^sub>f" and "\<natural>\<sigma>\<^sub>g \<noteq> trace.T (trace.init \<sigma>\<^sub>g) [] None"
      and "\<sigma> = trace.T (trace.init \<sigma>\<^sub>f) (trace.rest \<sigma>\<^sub>f @ trace.rest \<sigma>\<^sub>g) (trace.term \<sigma>\<^sub>g)"
using assms[unfolded spec.singleton.bind_le_conv]
proof(atomize_elim, induct rule: stronger_disjE[consumes 1, case_names incomplete continue])
  case continue
  from \<open>\<lblot>\<sigma>\<rblot> \<le> spec.continue f g\<close> obtain xs ys v w
    where f: "\<lblot>trace.init \<sigma>, xs, Some v\<rblot> \<le> f"
      and g: "\<lblot>trace.final' (trace.init \<sigma>) xs, ys, w\<rblot> \<le> g v"
      and \<sigma>: "\<sigma> \<le> trace.T (trace.init \<sigma>) (xs @ ys) w"
    by (clarsimp simp: spec.singleton.continue_le_conv)
  with \<open>\<not> \<lblot>\<sigma>\<rblot> \<le> spec.term.none f\<close> obtain ys'
    where "\<lblot>trace.final' (trace.init \<sigma>) xs, ys', trace.term \<sigma>\<rblot> \<le> g v"
      and "trace.rest \<sigma> = xs @ ys'"
      and "trace.natural' (trace.final' (trace.init \<sigma>) xs) ys' = [] \<longrightarrow> (\<exists>y. trace.term \<sigma> = Some y)"
    by (atomize_elim, cases \<sigma>)
       (auto elim!: trace.less_eqE prefix_append_not_NilE
              elim: order.trans[OF spec.singleton.mono, rotated]
              dest: spec.singleton.mono[OF iffD2[OF trace.less_eq_None(2)[where s="trace.init \<sigma>" and \<sigma>="trace.T (trace.init \<sigma>) xs (Some v)"], simplified]]
                    order.trans[OF spec.singleton.less_eq_None]
              simp: trace.less_eq_None spec.singleton.le_conv trace.natural'.eq_Nil_conv)+
  with f show ?case
    by (cases \<sigma>) (force simp: trace.natural_def)
qed blast

setup \<open>Sign.parent_path\<close>

lemma bind_le[case_names incomplete continue]:
  assumes "spec.term.none f \<le> P"
  assumes "\<And>\<sigma>\<^sub>f \<sigma>\<^sub>g v. \<lbrakk>\<lblot>\<sigma>\<^sub>f\<rblot> \<le> f; trace.init \<sigma>\<^sub>g = trace.final \<sigma>\<^sub>f; trace.term \<sigma>\<^sub>f = Some v; \<lblot>\<sigma>\<^sub>g\<rblot> \<le> g v;
                      \<natural>\<sigma>\<^sub>g \<noteq> trace.T (trace.init \<sigma>\<^sub>g) [] None\<rbrakk>
                 \<Longrightarrow> \<lblot>trace.init \<sigma>\<^sub>f, trace.rest \<sigma>\<^sub>f @ trace.rest \<sigma>\<^sub>g, trace.term \<sigma>\<^sub>g\<rblot> \<le> P"
  shows "f \<bind> g \<le> P"
by (rule spec.singleton_le_extI) (use assms in \<open>fastforce elim: spec.singleton.bind_le\<close>)

setup \<open>Sign.mandatory_path "bind"\<close>

definition resL :: "('v \<Rightarrow> ('a, 's, 'w) spec) \<Rightarrow> ('a, 's, 'w) spec \<Rightarrow> ('a, 's, 'v) spec" where
  "resL g P = \<Squnion>{f. f \<bind> g \<le> P}"

lemma incompleteI:
  assumes "\<lblot>s, xs, None\<rblot> \<le> f"
  shows "\<lblot>s, xs, None\<rblot> \<le> f \<bind> g"
using assms by (auto simp: spec.bind_def spec.singleton.term.none_le_conv)

lemma continueI:
  assumes f: "\<lblot>s, xs, Some v\<rblot> \<le> f"
  assumes g: "\<lblot>trace.final' s xs, ys, w\<rblot> \<le> g v"
  shows "\<lblot>s, xs @ ys, w\<rblot> \<le> f \<bind> g"
using assms by (force simp: spec.bind_def spec.continue_def intro!: disjI2)

lemma singletonL:
  shows "\<lblot>\<sigma>\<rblot> \<bind> g
      = spec.term.none \<lblot>\<sigma>\<rblot>
        \<squnion> \<Squnion>{\<lblot>trace.init \<sigma>, trace.rest \<sigma> @ trace.rest \<sigma>\<^sub>g, trace.term \<sigma>\<^sub>g\<rblot> |\<sigma>\<^sub>g.
               trace.final \<sigma> = trace.init \<sigma>\<^sub>g \<and> (\<exists>v. trace.term \<sigma> = Some v \<and> \<lblot>\<sigma>\<^sub>g\<rblot> \<le> g v)}" (is "?lhs = ?rhs")
proof(rule antisym)
  show "?lhs \<le> ?rhs"
  proof(induct rule: spec.bind_le)
    case (continue \<sigma>\<^sub>f \<sigma>\<^sub>g v) then show ?case
      by (cases \<sigma>\<^sub>f; cases \<sigma>\<^sub>g)
         (simp add: trace.split_Ex;
          metis order.refl spec.singleton.simps(1) trace.final'.natural' trace.stuttering.equiv.append_cong)
  qed force
  show "?rhs \<le> ?lhs"
    by (cases \<sigma>)
       (force simp: spec.term.none.singleton spec.singleton.bind_le_conv spec.singleton.continue_le_conv)
qed

lemma mono:
  assumes "f \<le> f'"
  assumes "\<And>v. g v \<le> g' v"
  shows "spec.bind f g \<le> spec.bind f' g'"
unfolding spec.bind_def
apply (strengthen ord_to_strengthen(1)[OF assms(1)])
apply (strengthen ord_to_strengthen(1)[OF assms(2)])
apply (rule order.refl)
done

lemma strengthen[strg]:
  assumes "st_ord F f f'"
  assumes "\<And>x. st_ord F (g x) (g' x)"
  shows "st_ord F (spec.bind f g) (spec.bind f' g')"
using assms by (cases F; simp add: spec.bind.mono)

lemma mono2mono[cont_intro, partial_function_mono]:
  assumes "monotone orda (\<le>) f"
  assumes "\<And>x. monotone orda (\<le>) (\<lambda>y. g y x)"
  shows "monotone orda (\<le>) (\<lambda>x. spec.bind (f x) (g x))"
using assms by (simp add: monotone_def spec.bind.mono)

interpretation L: galois.complete_lattice_class "\<lambda>f. f \<bind> g" "spec.bind.resL g" for g
proof
  show "f \<bind> g \<le> P \<longleftrightarrow> f \<le> spec.bind.resL g P" (is "?lhs \<longleftrightarrow> ?rhs") for f P
  proof(rule iffI)
    assume ?rhs
    then have "f \<bind> g \<le> spec.bind.resL g P \<bind> g"
      by (simp add: spec.bind.mono)
    also have "\<dots> \<le> P"
      by (simp add: spec.bind.resL_def spec.bind_def spec.term.none.Sup spec.continue.L.lower_Sup)
    finally show ?lhs .
  qed (simp add: spec.bind.resL_def Sup_upper)
qed

lemmas SUPL = spec.bind.L.lower_SUP
lemmas SupL = spec.bind.L.lower_Sup
lemmas supL = spec.bind.L.lower_sup[of f\<^sub>1 f\<^sub>2 g] for f\<^sub>1 f\<^sub>2 g

lemmas INFL_le = spec.bind.L.lower_INF_le
lemmas InfL_le = spec.bind.L.lower_Inf_le
lemmas infL_le = spec.bind.L.lower_inf_le[of f\<^sub>1 f\<^sub>2 g] for f\<^sub>1 f\<^sub>2 g

lemma SUPR:
  shows "spec.bind f (\<lambda>v. \<Squnion>x\<in>X. g x v) = (\<Squnion>x\<in>X. f \<bind> g x) \<squnion> (f \<bind> \<bottom>)" (is "?thesis1") \<comment>\<open> \<^const>\<open>Sup\<close> over \<^typ>\<open>('a, 's, 'v) spec\<close> \<close>
    and "spec.bind f (\<Squnion>x\<in>X. g x) = (\<Squnion>x\<in>X. f \<bind> g x) \<squnion> (f \<bind> \<bottom>)" (is ?thesis2) \<comment>\<open> \<^const>\<open>Sup\<close> over functions \<close>
proof -
  show ?thesis1
    by (cases "X = {}")
       (simp_all add: spec.bind_def spec.continue.R.lower_bot sup_SUP ac_simps
                      spec.continue.R.lower_SUP[where f=g and X=X, unfolded Sup_fun_def image_image]
                flip: bot_fun_def)
  then show ?thesis2
    by (simp add: Sup_fun_def image_image)
qed

lemma SUPR_not_empty:
  assumes "X \<noteq> {}"
  shows "spec.bind f (\<lambda>v. \<Squnion>x\<in>X. g x v) = (\<Squnion>x\<in>X. f \<bind> g x)"
using assms by (clarsimp simp: spec.bind.SUPR spec.bind.mono sup.absorb1 SUPI simp flip: ex_in_conv)

lemmas supR = spec.bind.SUPR_not_empty[where g=id and X="{g\<^sub>1, g\<^sub>2}" for g\<^sub>1 g\<^sub>2, simplified]

lemma InfR_le:
  shows "spec.bind f (\<lambda>v. \<Sqinter>x\<in>X. g x v) \<le> (\<Sqinter>x\<in>X. f \<bind> g x)"
by (meson INF_lower order.refl le_INF_iff spec.bind.mono)

lemma infR_le:
  shows "spec.bind f (g\<^sub>1 \<sqinter> g\<^sub>2) \<le> (f \<bind> g\<^sub>1) \<sqinter> (f \<bind> g\<^sub>2)"
    and "spec.bind f (\<lambda>v. g\<^sub>1 v \<sqinter> g\<^sub>2 v) \<le> (f \<bind> g\<^sub>1) \<sqinter> (f \<bind> g\<^sub>2)"
by (simp_all add: spec.bind.mono)

lemma Inf_le:
  shows "spec.bind (\<Sqinter>x\<in>X. f x) (\<lambda>v. (\<Sqinter>x\<in>X. g x v)) \<le> (\<Sqinter>x\<in>X. spec.bind (f x) (g x))"
by (auto simp: le_INF_iff intro: spec.bind.mono)

lemma inf_le:
  shows "spec.bind (f\<^sub>1 \<sqinter> f\<^sub>2) (\<lambda>v. g\<^sub>1 v \<sqinter> g\<^sub>2 v) \<le> spec.bind f\<^sub>1 g\<^sub>1 \<sqinter> spec.bind f\<^sub>2 g\<^sub>2"
by (simp add: spec.bind.mono)

lemma mcont2mcont[cont_intro]:
  assumes "mcont luba orda Sup (\<le>) f"
  assumes "\<And>v. mcont luba orda Sup (\<le>) (\<lambda>x. g x v)"
  shows "mcont luba orda Sup (\<le>) (\<lambda>x. spec.bind (f x) (g x))"
proof(rule ccpo.mcont2mcont'[OF complete_lattice_ccpo _ _ assms(1)])
  show "mcont Sup (\<le>) Sup (\<le>) (\<lambda>f. bind f (g x))" for x
    by (intro mcontI contI monotoneI) (simp_all add: spec.bind.mono flip: spec.bind.SUPL)
  show "mcont luba orda Sup (\<le>) (\<lambda>x. bind f (g x))" for f
    by (intro mcontI monotoneI contI)
       (simp_all add: mcont_monoD[OF assms(2)] spec.bind.mono
                flip: spec.bind.SUPR_not_empty contD[OF mcont_cont[OF assms(2)]])
qed

lemmas botL[simp] = spec.bind.L.lower_bot

lemma botR:
  shows "f \<bind> \<bottom> = spec.term.none f"
by (simp add: spec.bind_def spec.continue.R.lower_bot)

lemma eq_bot_conv:
  shows "spec.bind f g = \<bottom> \<longleftrightarrow> f = \<bottom>"
by (fastforce simp: spec.continue.L.lower_bot spec.bind_def spec.term.galois simp flip: bot.extremum_unique)

lemma idleL[simp]:
  shows "spec.idle \<bind> g = spec.idle"
by (simp add: spec.idle_def spec.bind.SupL image_image spec.bind.singletonL spec.term.none.singleton)

lemma idleR:
  shows "f \<then> spec.idle = f \<bind> \<bottom>" (is "?lhs = ?rhs")
proof(rule antisym)
  show "?lhs \<le> ?rhs"
    by (fastforce simp: spec.bind.botR trace.split_all spec.singleton.le_conv
                intro!: spec.bind_le
                 intro: spec.bind.incompleteI order.trans[rotated])
  show "?rhs \<le> ?lhs"
    by (simp add: spec.bind.mono)
qed

lemmas ifL = if_distrib[where f="\<lambda>f. spec.bind f g" for g]

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "idle"\<close>

lemma bind_le_conv[spec.idle_le]:
  shows "spec.idle \<le> f \<bind> g \<longleftrightarrow> spec.idle \<le> f" (is "?lhs \<longleftrightarrow> ?rhs")
proof(rule iffI)
  show "?lhs \<Longrightarrow> ?rhs"
    by (fastforce simp: spec.idle_def spec.singleton.mono trace.less_eq_None spec.singleton.bind_le_conv
                        spec.singleton.term.none_le_conv spec.singleton.continue_le_conv
                  elim: order.trans[rotated])
  show "?rhs \<Longrightarrow> ?lhs"
    by (simp add: spec.bind_def spec.idle.term.none_le_conv le_supI1)
qed

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "term"\<close>

setup \<open>Sign.mandatory_path "none"\<close>

lemma bindL_le[iff]:
  shows "spec.term.none f \<le> f \<bind> g"
by (simp add: spec.bind_def)

lemma bind:
  shows "spec.term.none (f \<bind> g) = f \<bind> (\<lambda>v. spec.term.none (g v))"
by (rule spec.singleton.antisym)
   (auto elim: spec.singleton.bind_le
         simp: trace.split_all spec.bind.incompleteI spec.bind.continueI spec.singleton.term.none_le_conv)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "all"\<close>

lemma bind:
  shows "spec.term.all (f \<bind> g) = spec.term.all f \<squnion> (f \<bind> (\<lambda>v. spec.term.all (g v)))" (is "?lhs = ?rhs")
proof(rule antisym[OF spec.singleton_le_extI])
  show "\<lblot>\<sigma>\<rblot> \<le> ?rhs" if "\<lblot>\<sigma>\<rblot> \<le> ?lhs" for \<sigma>
    using that
    by (cases \<sigma>)
       (fastforce simp: trace.split_all spec.singleton.le_conv
                 elim!: spec.singleton.bind_le
                 intro: spec.bind.continueI)
  show "?rhs \<le> ?lhs"
    by (simp add: spec.term.none.sup spec.term.none.bind spec.bind.mono flip: spec.term.galois)
qed

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.parent_path\<close>

paragraph\<open> The monad laws for \<^const>\<open>spec.bind\<close>. \label{sec:safety_logic-monad_laws} \<close>

setup \<open>Sign.mandatory_path "bind"\<close>

lemma bind:
  fixes f :: "(_, _, _) spec"
  shows "f \<bind> g \<bind> h = f \<bind> (\<lambda>v. g v \<bind> h)" (is "?lhs = ?rhs")
proof(rule antisym)
  show "?lhs \<le> ?rhs"
  proof(induct rule: spec.bind_le)
    case incomplete show ?case
      by (simp add: spec.bind.mono spec.term.none.bind)
  next
    case (continue \<sigma>\<^sub>f\<^sub>g \<sigma>\<^sub>h v) then show ?case
      by (cases \<sigma>\<^sub>h)
         (fastforce elim: spec.singleton.bind_le spec.bind.continueI
                    simp: spec.singleton.le_conv trace.split_all)
  qed
  show "?rhs \<le> ?lhs"
  proof(induct rule: spec.bind_le)
    case incomplete show ?case
      by (strengthen ord_to_strengthen(2)[OF spec.term.none.bindL_le])
         (simp add: spec.term.none.bind)
  next
    case (continue \<sigma>\<^sub>f \<sigma>\<^sub>g\<^sub>h v)
    note * = continue.hyps(1-3)
    from \<open>\<lblot>\<sigma>\<^sub>g\<^sub>h\<rblot> \<le> g v \<bind> h\<close> show ?case
    proof(cases rule: spec.singleton.bind_le)
      case incomplete with * show ?thesis
        by (cases \<sigma>\<^sub>f)
           (clarsimp simp: spec.singleton.le_conv spec.bind.incompleteI spec.bind.continueI)
    next
      case (continue \<sigma>\<^sub>g \<sigma>\<^sub>h v\<^sub>g) with * show ?thesis
        by (cases \<sigma>\<^sub>f; cases \<sigma>\<^sub>g)
           (simp flip: append_assoc; fastforce intro!: spec.bind.continueI)
    qed
  qed
qed

lemmas assoc = spec.bind.bind

lemma returnL_le:
  shows "g v \<le> spec.return v \<bind> g" (is "?lhs \<le> ?rhs")
proof(rule spec.singleton_le_extI)
  show "\<lblot>\<sigma>\<rblot> \<le> ?rhs" if "\<lblot>\<sigma>\<rblot> \<le> ?lhs" for \<sigma>
    by (rule spec.bind.continueI[where xs="[]" and s="trace.init \<sigma>" and ys="trace.rest \<sigma>" and w="trace.term \<sigma>" and v=v, simplified])
       (simp_all add: spec.return_def spec.action.stutterI that)
qed

lemma returnL:
  assumes "spec.idle \<le> g v"
  shows "spec.return v \<bind> g = g v"
by (rule antisym[OF spec.bind_le spec.bind.returnL_le])
   (simp_all add: assms spec.term.none.return spec.singleton.return_le_conv trace.split_all)

lemma returnR[simp]:
  shows "f \<bind> spec.return = f" (is "?lhs = ?rhs")
proof(rule antisym[OF _ spec.singleton_le_extI])
  show "?lhs \<le> ?rhs"
    by (auto intro: spec.bind_le
              simp: trace.split_all spec.singleton.return_le_conv order.trans[OF spec.singleton.less_eq_None(1)]
             split: option.split_asm)
  show "\<lblot>\<sigma>\<rblot> \<le> ?lhs" if "\<lblot>\<sigma>\<rblot> \<le> ?rhs" for \<sigma>
    using that
    by (cases "\<sigma>"; cases "trace.term \<sigma>";
        clarsimp simp: spec.bind.incompleteI spec.bind.continueI[where ys="[]", simplified] spec.singleton.le_conv)
qed

lemma return: \<comment>\<open> Does not require \<open>spec.idle \<le> g v\<close> \<close>
  fixes f :: "('a, 's, 'v) spec"
  fixes g :: "'v \<Rightarrow> 'x \<Rightarrow> ('a, 's, 'w) spec"
  shows "f \<bind> (\<lambda>v. spec.return x \<bind> g v) = f \<bind> (\<lambda>v. g v x)" (is "?lhs = ?rhs")
proof(rule antisym)
  show "?lhs \<le> ?rhs"
  proof(induct rule: spec.bind_le)
    case (continue \<sigma>\<^sub>f \<sigma>\<^sub>r\<^sub>g v)
    from \<open>\<lblot>\<sigma>\<^sub>r\<^sub>g\<rblot> \<le> spec.return x \<bind> g v\<close> show ?case
    proof(induct rule: spec.singleton.bind_le[case_names incomplete continue2])
      case incomplete with \<open>\<lblot>\<sigma>\<^sub>f\<rblot> \<le> f\<close> \<open>trace.init \<sigma>\<^sub>r\<^sub>g = trace.final \<sigma>\<^sub>f\<close> show ?thesis
        by (cases \<sigma>\<^sub>f)
           (auto simp: spec.term.none.return spec.singleton.le_conv
                intro: spec.bind.incompleteI order.trans[rotated])
    next
      case (continue2 \<sigma>\<^sub>r \<sigma>\<^sub>g v\<^sub>r) with continue show ?case
        by (cases \<sigma>\<^sub>f) (simp add: trace.split_all spec.singleton.le_conv spec.bind.continueI)
    qed
  qed simp
  show "?rhs \<le> ?lhs"
    by (simp add: spec.bind.mono spec.bind.returnL_le)
qed

setup \<open>Sign.mandatory_path "term"\<close>

lemma noneL[simp]:
  shows "spec.term.none f \<bind> g = spec.term.none f"
by (simp add: spec.bind.bind flip: spec.bind.botR bot_fun_def)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "map"\<close>

lemma bind_le: \<comment>\<open> Converse does not hold: it may be that no final states of \<open>f\<close> satisfy \<open>g\<close> \<close>
  fixes f :: "('a, 's, 'v) spec"
  fixes g :: "'v \<Rightarrow> ('a, 's, 'w) spec"
  fixes af :: "'a \<Rightarrow> 'b"
  fixes sf :: "'s \<Rightarrow> 't"
  fixes vf :: "'w \<Rightarrow> 'x"
  shows "spec.map af sf vf (f \<bind> g) \<le> spec.map af sf id f \<bind> (\<lambda>v. spec.map af sf vf (g v))"
by (subst (1) spec.map_def)
   (force simp: spec.singleton.le_conv trace.split_all trace.final'.map
         intro: spec.bind.incompleteI spec.bind.continueI
          elim: spec.singleton.bind_le)

lemma bind_inj_sf:
  fixes f :: "('a, 's, 'x) spec"
  fixes g :: "'x \<Rightarrow> ('a, 's, 'v) spec"
  assumes "inj sf"
  shows "spec.map af sf vf (f \<bind> g) = spec.map af sf id f \<bind> (\<lambda>v. spec.map af sf vf (g v))" (is "?lhs = ?rhs")
proof(rule antisym[OF spec.map.bind_le])
  show "?rhs \<le> ?lhs"
  proof(induct rule: spec.bind_le)
    case incomplete show ?case
      by (metis spec.map.mono spec.term.none.bindL_le spec.term.none.map_gen)
  next
    case (continue \<sigma>\<^sub>f \<sigma>\<^sub>g v)
    from continue(1,4) obtain \<sigma>\<^sub>f' \<sigma>\<^sub>g'
      where *: "\<lblot>\<sigma>\<^sub>f'\<rblot> \<le> f" "\<lblot>\<sigma>\<^sub>f\<rblot> \<le> \<lblot>trace.map af sf id \<sigma>\<^sub>f'\<rblot>"
               "\<lblot>\<sigma>\<^sub>g'\<rblot> \<le> g v" "\<lblot>\<sigma>\<^sub>g\<rblot> \<le> \<lblot>trace.map af sf vf \<sigma>\<^sub>g'\<rblot>"
      by (clarsimp simp: spec.singleton.le_conv)
    with continue(2,3)
    have "sf (trace.init \<sigma>\<^sub>g') = sf (trace.final \<sigma>\<^sub>f')"
      by (cases \<sigma>\<^sub>f; cases \<sigma>\<^sub>g; cases \<sigma>\<^sub>f'; cases \<sigma>\<^sub>g'; clarsimp)
         (clarsimp simp: spec.singleton_le_conv simp flip: trace.final'.map[where af=af and sf=sf];
          erule trace.less_eqE; simp add: trace.natural.trace_conv; metis trace.final'.natural')
    with continue(2,3) * show ?case
      by (cases \<sigma>\<^sub>f; cases \<sigma>\<^sub>g; cases \<sigma>\<^sub>f'; cases \<sigma>\<^sub>g')
         (fastforce dest: inj_onD[OF assms, simplified]
                    elim: trace.less_eqE spec.bind.continueI
                    simp: spec.singleton.le_conv trace.final'.map trace.less_eq_None
                          spec.singleton_le_conv trace.natural_def trace.natural'.append)
  qed
qed

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "vmap"\<close>

lemma eq_return: \<comment>\<open> generalizes @{thm [source] "spec.bind.returnR"} \<close>
  shows "spec.vmap vf P = P \<bind> spec.return \<circ> vf" (is ?thesis1)
    and "spec.vmap vf P = P \<bind> (\<lambda>v. spec.return (vf v))" (is "?lhs = ?rhs") \<comment>\<open> useful for flip/symmetric \<close>
proof -
  show "?lhs = ?rhs"
  proof(rule antisym)
    show "?lhs \<le> ?rhs"
      by (rule spec.singleton.exhaust[of P])
         (fastforce simp: trace.split_all spec.singleton.le_conv spec.map.Sup spec.map.singleton map_option_case
                   intro: spec.bind.incompleteI spec.bind.continueI[where ys="[]", simplified]
                   split: option.split)
next
    show "?rhs \<le> ?lhs"
      by (rule spec.bind_le)
         (force simp: trace.split_all spec.singleton.le_conv trace.less_eq_None trace.natural.mono
                      spec.term.galois spec.term.all.expansive spec.term.all.map spec.map.id
               split: option.split_asm)+
  qed
  then show ?thesis1
    by (simp add: comp_def)
qed

lemma unitL: \<comment>\<open> monomorphise ignored return values \<close>
  shows "f \<then> g = spec.vmap \<langle>()\<rangle> f \<then> g"
by (simp add: spec.vmap.eq_return comp_def spec.bind.bind spec.bind.return)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "invmap"\<close>

lemma bind:
  fixes f :: "('b, 't, 'v) spec"
  fixes g :: "'v \<Rightarrow> ('b, 't, 'x) spec"
  fixes af :: "'a \<Rightarrow> 'b"
  fixes sf :: "'s \<Rightarrow> 't"
  fixes vf :: "'w \<Rightarrow> 'x"
  shows "spec.invmap af sf vf (f \<bind> g) = spec.invmap af sf id f \<bind> (\<lambda>v. spec.invmap af sf vf (g v))" (is "?lhs = ?rhs")
proof(rule antisym[OF spec.singleton_le_extI])
  fix \<sigma> assume "\<lblot>\<sigma>\<rblot> \<le> ?lhs"
  then have "\<lblot>trace.map af sf vf \<sigma>\<rblot> \<le> f \<bind> g" by (simp add: spec.singleton.le_conv)
  then show "\<lblot>\<sigma>\<rblot> \<le> ?rhs"
  proof(induct rule: spec.singleton.bind_le)
    case incomplete then show ?case
      by (cases \<sigma>) (clarsimp simp: spec.singleton.le_conv spec.bind.incompleteI)
  next
    case (continue \<sigma>\<^sub>f \<sigma>\<^sub>g v\<^sub>f) then show ?case
      by (cases \<sigma>; cases \<sigma>\<^sub>f; cases \<sigma>\<^sub>g)
         (clarsimp simp: spec.bind.continueI map_eq_append_conv spec.singleton.le_conv trace.final'.map)
  qed
next
  show "?rhs \<le> ?lhs"
    by (simp add: order.trans[OF spec.map.bind_le] spec.bind.mono spec.map_invmap.lower_upper_contractive
            flip: spec.map_invmap.galois)
qed

lemma split_vinvmap:
  shows "spec.invmap af sf vf P = spec.invmap af sf id P \<bind> (\<lambda>v. \<Squnion>v'\<in>vf -` {v}. spec.return v')" (is "?lhs = ?rhs")
proof(rule antisym[OF spec.singleton_le_extI])
  show "\<lblot>\<sigma>\<rblot> \<le> ?rhs" if "\<lblot>\<sigma>\<rblot> \<le> ?lhs" for \<sigma>
    using that
    by (cases \<sigma>; cases "trace.term \<sigma>")
       (auto simp: spec.singleton.le_conv
            intro: spec.bind.incompleteI spec.bind.continueI[where ys="[]", simplified])
  show "?rhs \<le> ?lhs"
  proof(induct rule: spec.bind_le)
    case (continue \<sigma>\<^sub>f \<sigma>\<^sub>g v) then show ?case
      by (cases \<sigma>\<^sub>f; cases "trace.term \<sigma>\<^sub>g")
         (auto simp: spec.singleton.le_conv split: option.split_asm elim: order.trans[rotated])
  qed (simp add: spec.term.none.invmap_gen[where vf'=vf] spec.invmap.mono)
qed

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "action"\<close>

lemma return_const:
  assumes "V \<noteq> {}"
  assumes "W \<noteq> {}"
  shows "spec.action (V \<times> F) = spec.action (W \<times> F) \<then> (\<Squnion>v\<in>V. spec.return v)" (is "?lhs = ?rhs")
proof(rule antisym)
  from \<open>W \<noteq> {}\<close> show "?lhs \<le> ?rhs"
    by - (rule spec.action_le;
          fastforce intro: spec.bind.continueI[where xs="[x]" and v="SOME w. w \<in> W" for x, simplified]
                           spec.action.stepI
                     simp: some_in_eq spec.singleton.le_conv spec.singleton.action_le_conv
                           spec.idle.action_le spec.idle.bind_le_conv)
  from \<open>V \<noteq> {}\<close> show "?rhs \<le> ?lhs"
    by - (rule spec.bind_le,
           fastforce simp: spec.term.galois spec.term.all.action intro: le_supI1 spec.action.mono,
           auto 0 3 simp: spec.singleton.le_conv spec.singleton.action_le_conv
               simp flip: trace.steps'.empty_conv
                simp del: trace.steps'.simps split: option.splits)
qed

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "term.closed"\<close>

lemma bind_all_return:
  assumes "f \<in> spec.term.closed _"
  shows "f \<then> (\<Squnion>range spec.return) = spec.term.all f" (is "?lhs = ?rhs")
proof(rule antisym[OF _ spec.singleton_le_extI])
  show "?lhs \<le> ?rhs"
    by (subst (2) spec.term.closed_conv[OF assms])
       (simp add: spec.term.none.bind spec.term.none.Sup image_image spec.term.none.return
                  spec.bind.botR spec.bind.idleR
                  spec.term.all.monomorphic
            flip: spec.term.galois)
next
  fix \<sigma>
  assume "\<lblot>\<sigma>\<rblot> \<le> ?rhs"
  then obtain v where "\<lblot>trace.init \<sigma>, trace.rest \<sigma>, Some v\<rblot> \<le> f"
    by (subst (asm) spec.term.closed_conv[OF assms])
       (force simp: spec.singleton.le_conv spec.term.all.monomorphic)
  then show "\<lblot>\<sigma>\<rblot> \<le> ?lhs"
    by (cases \<sigma>; cases "trace.term \<sigma>")
       (auto simp: spec.singleton.le_conv spec.bind.continueI[where ys="[]", simplified]
            split: option.split)
qed

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.parent_path\<close>


subsection\<open> Kleene star \label{sec:safety_logic-kleene} \<close>

text\<open>

We instantiate the generic Kleene locale with monomorphic \<open>spec.return ()\<close>. The polymorphic
\<open>(\<Squnion>v. spec.return v)\<close> fails the \<open>comp_unitR\<close> axiom (\<open>\<epsilon> \<le> x \<Longrightarrow> x \<bullet> \<epsilon> = x"\<close>).

\<close>

setup \<open>Sign.mandatory_path "spec"\<close>

interpretation kleene: weak_kleene "spec.return ()" "\<lambda>x y. spec.bind x \<langle>y\<rangle>"
by standard (simp_all add: spec.bind.bind spec.bind.supL spec.bind.supR
                           spec.bind.returnL order.trans[OF spec.idle.return_le])

setup \<open>Sign.mandatory_path "idle.kleene"\<close>

lemmas star_le[spec.idle_le] = order.trans[OF spec.idle.return_le spec.kleene.epsilon_star_le]

lemmas rev_star_le[spec.idle_le] = spec.idle.kleene.star_le[unfolded spec.kleene.star_rev_star]

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "return.kleene"\<close>

lemmas star_le = spec.kleene.epsilon_star_le

lemmas rev_star_le = spec.return.kleene.star_le[unfolded spec.kleene.star_rev_star]

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "kleene"\<close>

lemma star_idle:
  shows "spec.kleene.star spec.idle = spec.return ()"
by (subst spec.kleene.star.simps) (simp add: sup.absorb2 spec.idle.return_le)

lemmas rev_star_idle = spec.kleene.star_idle[unfolded spec.kleene.star_rev_star]

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "term.all.kleene"\<close>

lemma star_closed_le:
  fixes P :: "(_, _, unit) spec"
  assumes "P \<in> spec.term.closed _"
  shows "spec.term.all (spec.kleene.star P) \<le> spec.kleene.star P" (is "_ \<le> ?rhs")
proof(induct rule: spec.kleene.star.fixp_induct[where P="\<lambda>R. spec.term.all (R P) \<le> ?rhs", case_names adm bot step])
  case (step R) show ?case
    by (auto simp: spec.term.all.sup spec.term.all.bind spec.kleene.expansive_star spec.term.all.return
        simp flip: spec.term.all.closed_conv[OF assms]
            intro: spec.kleene.epsilon_star_le
                   order.trans[OF spec.bind.mono[OF order.refl step] spec.kleene.fold_starL])
qed simp_all

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "term.closed.kleene"\<close>

lemma star:
  assumes "P \<in> spec.term.closed _"
  shows "spec.kleene.star P \<in> spec.term.closed _"
by (rule spec.term.closed_clI)
   (simp add: spec.term.all.kleene.star_closed_le[OF assms] spec.term.all.monomorphic)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.parent_path\<close>


subsection\<open> Transition relations \label{sec:safety_logic-trans_rel} \<close>

text\<open>

Using \<^const>\<open>spec.kleene.star\<close> we can specify the transitions each agent is allowed to perform.
These constraints (\<open>(\<sqinter>) spec.rel r\<close>) distribute through all program constructs (for suitable \<open>r\<close>).

Observations:
 \<^item> the Galois connection between \<open>spec.rel\<close> and \<open>spec.steps\<close> is much easier to show in the powerset model
  \<^item> see \<^citet>\<open>\<open>Footnote~2\<close> in "vanStaden:2015"\<close>
 \<^item> most useful facts about \<open>spec.steps\<close> depend on the model

\<close>

setup \<open>Sign.mandatory_path "spec"\<close>

setup \<open>Sign.mandatory_path "rel"\<close>

definition act :: "('a, 's) steps \<Rightarrow> ('a, 's, unit) spec" where \<comment>\<open> lift above \<^const>\<open>spec.return\<close> to ease some proofs \<close>
  "act r = spec.action ({()} \<times> (r \<union> UNIV \<times> Id))"

abbreviation monomorphic :: "('a, 's) steps \<Rightarrow> ('a, 's, unit) spec" where
  "monomorphic r \<equiv> spec.kleene.star (spec.rel.act r)"

lemma act_alt_def:
  shows "spec.rel.act r = spec.action ({()} \<times> r) \<squnion> spec.return ()"
by (simp add: spec.rel.act_def spec.return_def Sigma_Un_distrib2 flip: spec.action.sup)

setup \<open>Sign.parent_path\<close>

definition rel :: "('a, 's) steps \<Rightarrow> ('a, 's, 'v) spec" where
  "rel r = spec.term.all (spec.rel.monomorphic r)"

definition steps :: "('a, 's, 'v) spec \<Rightarrow> ('a, 's) steps" where
  "steps P = \<Inter>{r. P \<le> spec.rel r}"

setup \<open>Sign.mandatory_path "rel.act"\<close>

lemma monotone:
  shows "mono spec.rel.act"
proof(rule monotoneI)
  show "spec.rel.act r \<le> spec.rel.act r'" if "r \<subseteq> r'" for r r' :: "('a, 's) steps"
    using that unfolding spec.rel.act_def by (strengthen ord_to_strengthen(1)[OF \<open>r \<le> r'\<close>]) simp
qed

lemmas strengthen[strg] = st_monotone[OF spec.rel.act.monotone]
lemmas mono = monotoneD[OF spec.rel.act.monotone]

lemma empty:
  shows "spec.rel.act {} = spec.return ()"
by (simp add: spec.rel.act_def spec.return_def spec.action.empty)

lemma UNIV:
  shows "spec.rel.act UNIV = spec.action ({()} \<times> UNIV)"
by (simp add: spec.rel.act_def)

lemma sup:
  shows "spec.rel.act (r \<union> s) = spec.rel.act r \<squnion> spec.rel.act s"
by (fastforce simp: spec.rel.act_def simp flip: spec.action.sup intro: arg_cong[where f=spec.action])

lemma stutter:
  shows "spec.rel.act (UNIV \<times> Id) = spec.return ()"
by (simp add: spec.rel.act_def spec.return_def)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "term"\<close>

setup \<open>Sign.mandatory_path "all"\<close>

setup \<open>Sign.mandatory_path "rel"\<close>

lemma act_mono:
  shows "spec.term.all (spec.rel.act r) = spec.rel.act r"
by (simp add: spec.rel.act_alt_def spec.term.all.sup spec.term.all.action spec.term.all.return UNIV_unit)

setup \<open>Sign.parent_path\<close>

lemma rel:
  shows "spec.term.all (spec.rel r) = spec.rel r"
by (simp add: spec.rel_def)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "closed"\<close>

setup \<open>Sign.mandatory_path "rel"\<close>

lemma act:
  shows "spec.rel.act r \<in> spec.term.closed _"
by (metis spec.term.all.rel.act_mono spec.term.all.closed)

setup \<open>Sign.parent_path\<close>

lemma rel:
  shows "spec.rel r \<in> spec.term.closed _"
by (metis spec.term.all.closed spec.term.all.rel)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "none"\<close>

lemma inf_none_rel: \<comment>\<open> polymorphic constants \<close>
  shows "spec.term.none (spec.rel r :: ('a, 's, 'w) spec) \<sqinter> spec.term.none P
       = spec.rel r \<sqinter> (spec.term.none P :: ('a, 's, 'v) spec)" (is ?thesis1)
    and "spec.term.none P \<sqinter> spec.term.none (spec.rel r :: ('a, 's, 'w) spec)
       = spec.term.none P \<sqinter> (spec.rel r :: ('a, 's, 'v) spec)" (is ?thesis2)
proof -
  show ?thesis1
    by (metis spec.term.closed.rel spec.term.closed.none_inf(1)
              spec.term.none.idempotent spec.term.none.inf(2) spec.term.none_all spec.term.all.rel)
  then show ?thesis2
    by (simp add: ac_simps)
qed

lemma inf_rel:
  shows "spec.term.none P \<sqinter> spec.rel r = spec.term.none (P \<sqinter> spec.rel r)" (is ?thesis1)
    and "spec.rel r \<sqinter> spec.term.none P = spec.term.none (spec.rel r \<sqinter> P)" (is ?thesis2)
by (simp_all add: ac_simps spec.term.none.inf(2) spec.term.none.inf_none_rel(2))

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "return"\<close>

setup \<open>Sign.mandatory_path "rel"\<close>

lemma act_le:
  shows "spec.return () \<le> spec.rel.act r"
by (simp add: spec.rel.act.mono flip: spec.rel.act.empty)

setup \<open>Sign.parent_path\<close>

lemma rel_le:
  shows "spec.return v \<le> spec.rel r"
by (simp add: spec.rel_def spec.term.none.return spec.idle.kleene.star_le flip: spec.term.galois)

lemma Sup_rel_le:
  shows "\<Squnion>range spec.return \<le> spec.rel r"
by (simp add: spec.return.rel_le)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "idle"\<close>

setup \<open>Sign.mandatory_path "rel"\<close>

lemmas act_le[spec.idle_le] = order.trans[OF spec.idle.return_le spec.return.rel.act_le]

setup \<open>Sign.parent_path\<close>

lemmas rel_le[spec.idle_le] = order.trans[OF spec.idle.return_le spec.return.rel_le]

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "singleton"\<close>

setup \<open>Sign.mandatory_path "rel"\<close>

setup \<open>Sign.mandatory_path "act"\<close>

lemma le_conv[spec.singleton.le_conv]:
  shows "\<lblot>\<sigma>\<rblot> \<le> spec.rel.act r \<longleftrightarrow> trace.steps \<sigma> = {} \<or> (\<exists>x\<in>r. trace.steps \<sigma> = {x})"
by (auto simp: spec.rel.act_def spec.singleton.le_conv spec.singleton.action_le_conv trace.steps'.step_conv
        split: option.split)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "monomorphic"\<close>

lemma le_steps:
  assumes "trace.steps \<sigma> \<subseteq> r"
  shows "\<lblot>\<sigma>\<rblot> \<le> spec.rel.monomorphic r"
using assms
proof(induct "trace.rest \<sigma>" arbitrary: \<sigma> rule: rev_induct)
  case Nil then show ?case
    by (simp add: spec.singleton.rel.act.le_conv order.trans[OF _ spec.kleene.expansive_star])
next
  case (snoc x xs \<sigma>)
  from snoc(2,3)
  have *: "\<lblot>trace.init \<sigma>, xs, Some ()\<rblot> \<le> spec.rel.monomorphic r"
    by (cases \<sigma>) (fastforce intro: snoc(1) simp: trace.steps'.append)
  have **: "\<lblot>trace.final' (trace.init \<sigma>) xs, [x], trace.term \<sigma>\<rblot> \<le> spec.rel.act r"
  proof(cases "trace.final' (trace.init \<sigma>) xs = snd x")
    case True with snoc.prems snoc.hyps(2) show ?thesis
      by (simp add: spec.singleton.le_conv)
  next
    case False with snoc.prems snoc.hyps(2) show ?thesis
      by (cases \<sigma>) (clarsimp simp: spec.singleton.le_conv trace.steps'.append)
  qed
  show ?case
    by (rule order.trans[OF spec.bind.continueI[OF * **, simplified snoc.hyps(2) trace.t.collapse]
                            spec.kleene.fold_starR])
qed

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "rel.act"\<close>

lemmas mono_le = spec.kleene.expansive_star

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "rel.monomorphic"\<close>

lemma alt_def:
  shows "spec.rel.monomorphic r = \<Squnion>(spec.singleton ` {\<sigma>. trace.steps \<sigma> \<subseteq> r})" (is "?lhs = ?rhs")
proof(rule antisym)
  show "?lhs \<le> ?rhs"
  proof(induct rule: spec.kleene.star.fixp_induct[case_names adm bot step])
    case (step R)
    have "spec.return () \<le> ?rhs"
      by (force intro: spec.singleton_le_extI simp: spec.singleton.le_conv
                 dest: trace.steps'.simps(5))
    moreover
    have "spec.rel.act r \<then> ?rhs \<le> ?rhs"
    proof(induct rule: spec.bind_le)
      case incomplete show ?case
        by (rule spec.singleton_le_extI)
           (clarsimp simp: spec.singleton.le_conv;
            metis order.refl empty_subsetI insert_subsetI trace.steps'.empty_conv(1))
    next
      case (continue \<sigma>\<^sub>f \<sigma>\<^sub>g v) then show ?case
        by (fastforce intro!: exI[where x="trace.T (trace.init \<sigma>\<^sub>f) (trace.rest \<sigma>\<^sub>f @ trace.rest \<sigma>\<^sub>g) (trace.term \<sigma>\<^sub>g)"]
                       simp: trace.steps'.append spec.singleton.rel.act.le_conv
                       dest: trace.steps.mono[OF iffD1[OF spec.singleton_le_conv], simplified,
                                                             simplified trace.steps'.natural'])
    qed
    ultimately show ?case
      by - (strengthen ord_to_strengthen(1)[OF step]; simp)
  qed simp_all
  show "?rhs \<le> ?lhs"
    by (simp add: spec.singleton.rel.monomorphic.le_steps)
qed

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "singleton"\<close>

setup \<open>Sign.mandatory_path "rel"\<close>

lemma monomorphic_le_conv[spec.singleton.le_conv]:
  shows "\<lblot>\<sigma>\<rblot> \<le> spec.rel.monomorphic r \<longleftrightarrow> trace.steps \<sigma> \<subseteq> r"
by (fastforce simp: spec.rel.monomorphic.alt_def spec.singleton_le_conv trace.steps'.natural'
              dest: trace.steps.mono)

setup \<open>Sign.parent_path\<close>

lemma rel_le_conv[spec.singleton.le_conv]:
  shows "\<lblot>\<sigma>\<rblot> \<le> spec.rel r \<longleftrightarrow> trace.steps \<sigma> \<subseteq> r"
by (cases \<sigma>) (auto simp add: spec.rel_def spec.singleton.le_conv)

setup \<open>Sign.parent_path\<close>

interpretation rel: galois.complete_lattice_class spec.steps spec.rel
proof(rule galois.upper_preserves_InfI)
  show "mono spec.rel"
    by (simp add: monoD monotoneI spec.kleene.monotone_star spec.rel.act.mono spec.rel_def)
  show "(\<Sqinter>x\<in>X. spec.rel x) \<le> spec.rel (\<Inter>X)" for X :: "('a, 'b) steps set"
    by (fastforce intro: spec.singleton_le_extI simp: le_INF_iff spec.singleton.le_conv)
qed (simp add: spec.steps_def)

lemma rel_alt_def:
  shows "spec.rel r = \<Squnion>(spec.singleton ` {\<sigma>. trace.steps \<sigma> \<subseteq> r})"
by (simp flip: spec.singleton.rel_le_conv)

setup \<open>Sign.mandatory_path "vmap"\<close>

lemma unit_rel:
  shows "spec.vmap \<langle>()\<rangle> (spec.rel r) = spec.rel r"
by (simp add: spec.rel_def spec.term.all.vmap_unit_absorb)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "rel"\<close>

lemma monomorphic_conv: \<comment>\<open> if the return type is \<^typ>\<open>unit\<close> \<close>
  shows "spec.rel r = spec.rel.monomorphic r"
by (simp add: spec.rel_def
        flip: spec.term.all.closed_conv[OF spec.term.closed.kleene.star[OF spec.term.closed.rel.act]])

lemma monomorphic_act_le: \<comment>\<open> \<^typ>\<open>unit\<close> return type \<close>
  shows "spec.rel.act r \<le> spec.rel r"
by (simp add: spec.rel.monomorphic_conv spec.rel.act.mono_le)

lemma empty:
  shows "spec.rel {} = (\<Squnion>v. spec.return v)"
by (simp add: spec.rel_def spec.kleene.star_epsilon spec.rel.act.empty spec.term.all.return)

lemmas UNIV = spec.rel.upper_top
lemmas top = spec.rel.UNIV

lemmas INF = spec.rel.upper_INF
lemmas Inf = spec.rel.upper_Inf
lemmas inf = spec.rel.upper_inf

lemmas Sup_le = spec.rel.Sup_upper_le
lemmas sup_le = spec.rel.sup_upper_le \<comment>\<open> Converse does not hold: the RHS allows interleaving of \<open>r\<close> and \<open>s\<close> steps \<close>

lemma reflcl:
  shows "spec.rel (r \<union> A \<times> Id) = spec.rel r"
    and "spec.rel (A \<times> Id \<union> r) = spec.rel r"
by (simp_all add: spec.rel_def spec.rel.act_def ac_simps flip: Times_Un_distrib1)

lemma minus_Id:
  shows "spec.rel (r - A \<times> Id) = spec.rel r"
by (metis Un_Diff_cancel spec.rel.reflcl(2))

lemma Id:
  shows "spec.rel (A \<times> Id) = (\<Squnion>v. spec.return v)"
by (subst spec.rel.minus_Id[where A=A, symmetric]) (simp add: spec.rel.empty)

lemmas monotone = spec.rel.monotone_upper
lemmas mono = monotoneD[OF spec.rel.monotone, of r r' for r r']

lemma mono_reflcl:
  assumes "r \<subseteq> s \<union> UNIV \<times> Id"
  shows "spec.rel r \<le> spec.rel s"
by (metis assms spec.rel.mono spec.rel.reflcl(1))

lemma unfoldL:
  shows "spec.rel r = spec.rel.act r \<then> spec.rel r" (is "?lhs = ?rhs")
proof(rule antisym)
  show "?lhs \<le> ?rhs"
    by (rule order.trans[OF spec.bind.returnL_le spec.bind.mono[OF spec.return.rel.act_le order.refl]])
  show "?rhs \<le> ?lhs"
    by (subst (2) spec.rel_def, subst spec.kleene.star_unfoldL)
       (simp add: spec.term.all.sup spec.term.all.bind le_supI1 flip: spec.rel_def)
qed

lemma foldR: \<comment>\<open> arbitrary interstitial return type \<close>
  shows "spec.rel r \<then> spec.rel.act r = spec.rel r" (is "?lhs = ?rhs")
proof -
  have "?lhs = spec.rel.monomorphic r \<then> spec.rel.act r"
    by (subst spec.vmap.unitL) (simp add: spec.vmap.unit_rel spec.rel.monomorphic_conv)
  also have "\<dots> = ?rhs"
  proof(rule antisym)
    show "spec.rel.monomorphic r \<then> spec.rel.act r \<le> ?rhs"
      by (simp add: spec.kleene.fold_starR spec.rel.monomorphic_conv)
    show "?rhs \<le>spec.rel.monomorphic r \<then> spec.rel.act r"
      by (simp add: spec.rel.monomorphic_conv)
         (rule spec.bind.mono[OF order.refl spec.return.rel.act_le, where 'c=unit, simplified])
  qed
  finally show ?thesis .
qed

lemma wind_bind: \<comment>\<open> arbitrary interstitial return type \<close>
  shows "spec.rel r \<then> spec.rel r = spec.rel r" (is "?lhs = ?rhs")
proof(rule antisym)
  show "?lhs \<le> ?rhs"
  proof(induct rule: spec.bind_le)
    case incomplete show ?case
      by (simp add: spec.term.all.rel spec.term.galois)
  next
    case (continue \<sigma>\<^sub>f \<sigma>\<^sub>g v) then show ?case
      by (simp add: spec.singleton.rel_le_conv trace.steps'.append)
  qed
  show "?rhs \<le> ?lhs"
    by (meson order.trans order.refl spec.bind.mono spec.bind.returnL_le spec.return.rel_le)
qed

lemma wind_bind_leading: \<comment>\<open> arbitrary interstitial return type \<close>
  assumes "r' \<subseteq> r"
  shows "spec.rel r' \<then> spec.rel r = spec.rel r" (is "?lhs = ?rhs")
proof(rule antisym)
  from assms show "?lhs \<le> ?rhs"
    by (metis order.refl spec.bind.mono spec.rel.mono spec.rel.wind_bind)
  show "?rhs \<le> ?lhs"
    by (meson order.trans spec.eq_iff spec.bind.mono spec.bind.returnL_le spec.return.rel_le)
qed

lemma wind_bind_trailing: \<comment>\<open> arbitrary interstitial return type \<close>
  assumes "r' \<subseteq> r"
  shows "spec.rel r \<then> spec.rel r' = spec.rel r" (is "?lhs = ?rhs")
proof(rule antisym[OF _ spec.singleton_le_extI])
  from assms show "?lhs \<le> ?rhs"
    by (metis order_refl spec.bind.mono spec.rel.mono spec.rel.wind_bind)
  show "\<lblot>\<sigma>\<rblot> \<le> ?lhs" if "\<lblot>\<sigma>\<rblot> \<le> ?rhs" for \<sigma>
    using that
    by (cases \<sigma>)
       (force simp: spec.singleton.le_conv spec.singleton.bind_le_conv spec.singleton.continue_le_conv)
qed

text\<open> Interstitial unit, for unfolding \<close>

lemmas unwind_bind = spec.rel.wind_bind[where 'd=unit, symmetric]
lemmas unwind_bind_leading = spec.rel.wind_bind_leading[where 'd=unit, symmetric]
lemmas unwind_bind_trailing = spec.rel.wind_bind_trailing[where 'd=unit, symmetric]

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "invmap"\<close>

lemma rel:
  shows "spec.invmap af sf vf (spec.rel r) = spec.rel (map_prod af (map_prod sf sf) -` (r \<union> UNIV \<times> Id))"
by (fastforce intro: antisym spec.singleton_le_extI simp: spec.singleton.invmap_le_conv spec.singleton.rel_le_conv trace.steps'.map)

lemma range:
  shows "spec.invmap af sf vf P = spec.invmap af sf vf (P \<sqinter> spec.rel (range af \<times> range sf \<times> range sf))"
by (rule antisym[OF spec.singleton_le_extI])
    (auto simp: spec.singleton.le_conv trace.steps'.map spec.invmap.mono)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "map"\<close>

lemma inf_rel:
  shows "spec.map af sf vf P \<sqinter> spec.rel r
       = spec.map af sf vf (P \<sqinter> spec.rel (map_prod af (map_prod sf sf) -` (r \<union> UNIV \<times> Id)))"
    and "spec.rel r \<sqinter> spec.map af sf vf P
       = spec.map af sf vf (spec.rel (map_prod af (map_prod sf sf) -` (r \<union> UNIV \<times> Id)) \<sqinter> P)"
by (simp_all add: spec.invmap.rel spec.map.inf_distr ac_simps)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "action"\<close>

lemma rel_le:
  fixes F :: "('v \<times> 'a \<times> 's \<times> 's) set"
  fixes r :: "('a, 's) steps"
  assumes "\<And>v a s s'. (v, a, s, s') \<in> F \<Longrightarrow> (a, s, s') \<in> r \<or> s = s'"
  shows "spec.action F \<le> spec.rel r"
unfolding spec.rel_def
by (strengthen ord_to_strengthen(2)[OF spec.kleene.expansive_star])
   (fastforce simp: spec.rel.act_def spec.term.all.action intro: le_supI1 spec.action.mono dest: assms)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "kleene"\<close>

lemma star_le:
  assumes "S \<le> spec.rel r"
  shows "spec.kleene.star S \<le> spec.rel r"
by (strengthen ord_to_strengthen(1)[OF assms])
   (simp add: spec.rel_def spec.kleene.idempotent_star
        flip: spec.term.all.closed_conv[OF spec.term.closed.kleene.star[OF spec.term.closed.rel.act]])

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "bind"\<close>

lemma relL_le:
  shows "g x \<le> spec.rel r \<bind> g"
by (rule order.trans[OF spec.bind.returnL_le spec.bind.mono[OF spec.return.rel_le order.refl]])

lemma relR_le:
  shows "f \<le> f \<then> spec.rel r"
by (rule order.trans[OF eq_refl[OF spec.bind.returnR[symmetric]]
                        spec.bind.mono[OF order.refl spec.return.rel_le]])

lemma inf_rel:
  shows "(f \<bind> g) \<sqinter> spec.rel r = (spec.rel r \<sqinter> f) \<bind> (\<lambda>x. spec.rel r \<sqinter> g x)" (is ?thesis1)
    and "spec.rel r \<sqinter> (f \<bind> g) = (spec.rel r \<sqinter> f) \<bind> (\<lambda>x. spec.rel r \<sqinter> g x)" (is "?lhs = ?rhs")
proof -
  show "?lhs = ?rhs"
  proof(rule antisym[OF spec.singleton_le_extI])
    fix \<sigma> assume lhs: "\<lblot>\<sigma>\<rblot> \<le> ?lhs"
    then have "\<lblot>\<sigma>\<rblot> \<le> f \<bind> g" by simp
    then show "\<lblot>\<sigma>\<rblot> \<le> ?rhs"
    proof(cases rule: spec.singleton.bind_le)
      case incomplete with lhs show ?thesis
        by (cases \<sigma>) (simp add: spec.singleton.le_conv spec.bind.incompleteI)
    next
      case (continue \<sigma>\<^sub>f \<sigma>\<^sub>g v\<^sub>f) with lhs show ?thesis
        by (cases \<sigma>\<^sub>f) (simp add: spec.singleton.le_conv trace.steps'.append spec.bind.continueI)
    qed
  next
    show "?rhs \<le> ?lhs"
    proof(induct rule: spec.bind_le)
      case incomplete show ?case
        by (auto simp: spec.term.none.inf spec.term.galois spec.term.all.rel intro: le_infI1 le_infI2)
    next
      case (continue \<sigma>\<^sub>f \<sigma>\<^sub>g v) then show ?case
        by (cases \<sigma>\<^sub>f; cases \<sigma>\<^sub>g) (simp add: spec.singleton.rel_le_conv spec.bind.continueI trace.steps'.append)
    qed
  qed
  then show ?thesis1
    by (simp add: ac_simps)
qed

lemma inf_rel_distr_le:
  shows "(f \<sqinter> spec.rel r) \<bind> (\<lambda>v. g\<^sub>1 v \<sqinter> g\<^sub>2) \<le> (f \<bind> g\<^sub>1) \<sqinter> (spec.rel r \<bind> (\<lambda>_::unit. g\<^sub>2))"
by (rule spec.bind_le;
    force simp: trace.split_all spec.singleton.le_conv spec.term.galois spec.term.none.inf
                spec.term.all.bind spec.term.all.rel
         intro: le_infI1 le_infI2 spec.bind.continueI)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "singleton"\<close>

lemma inf_rel:
  shows "\<lblot>\<sigma>\<rblot> \<sqinter> spec.rel r = \<Squnion>(spec.singleton ` {\<sigma>'. \<sigma>' \<le> \<sigma> \<and> trace.steps \<sigma>' \<subseteq> r})" (is "?lhs = ?rhs")
    and "spec.rel r \<sqinter> \<lblot>\<sigma>\<rblot> = \<Squnion>(spec.singleton ` {\<sigma>'. \<sigma>' \<le> \<sigma> \<and> trace.steps \<sigma>' \<subseteq> r})" (is ?thesis2)
proof -
  show "?lhs = ?rhs"
  proof(rule antisym[OF spec.singleton_le_extI])
    show "\<lblot>\<sigma>'\<rblot> \<le> ?rhs" if "\<lblot>\<sigma>'\<rblot> \<le> ?lhs" for \<sigma>'
      using that
      by (fastforce simp: spec.singleton.le_conv spec.singleton_le_conv
                    elim: trace.natural.less_eqE[where u="\<natural>\<sigma>" and u'=\<sigma>, simplified]
                    dest: trace.stuttering.equiv.steps)
    show "?rhs \<le> ?lhs"
      by (clarsimp simp: spec.singleton.le_conv spec.singleton.mono)
  qed
  then show ?thesis2
    by (rule inf_commute_conv)
qed

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "action"\<close>

lemma inf_rel:
  fixes F :: "('v \<times> 'a \<times> 's \<times> 's) set"
  fixes r :: "('a, 's) steps"
  assumes "\<And>a. refl (r `` {a})"
  shows "spec.action F \<sqinter> spec.rel r = spec.action (F \<inter> UNIV \<times> r)" (is "?lhs = ?rhs")
    and "spec.rel r \<sqinter> spec.action F = spec.action (F \<inter> UNIV \<times> r)" (is ?thesis1)
proof -
  show "?lhs = ?rhs"
  proof(rule antisym[OF spec.singleton_le_extI])
    from reflD[OF assms] show "\<lblot>\<sigma>\<rblot> \<le> ?rhs" if "\<lblot>\<sigma>\<rblot> \<le> ?lhs" for \<sigma>
      using that
      by (auto 0 2 simp: spec.singleton.le_conv spec.singleton.action_le_conv
                    split: option.split_asm)
    show "?rhs \<le> ?lhs"
      by (rule order.trans[OF spec.action.inf_le inf.mono[OF order.refl spec.action.rel_le]]) simp
  qed
  then show ?thesis1
    by (rule inf_commute_conv)
qed

lemma inf_rel_reflcl:
  shows "spec.action F \<sqinter> spec.rel r = spec.action (F \<inter> UNIV \<times> (r \<union> UNIV \<times> Id))"
    and "spec.rel r \<sqinter> spec.action F = spec.action (F \<inter> UNIV \<times> (r \<union> UNIV \<times> Id))"
by (simp_all add: refl_on_def spec.rel.reflcl ac_simps flip: spec.action.inf_rel)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "return"\<close>

lemma inf_rel:
  shows "spec.rel r \<sqinter> spec.return v = spec.return v"
    and "spec.return v \<sqinter> spec.rel r = spec.return v"
by (simp_all add: spec.return_def ac_simps spec.action.inf_rel_reflcl
                  Sigma_Un_distrib2 Int_Un_distrib Times_Int_Times
            flip: Sigma_Un_distrib2)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "kleene.star"\<close>

lemma inf_rel:
  shows "spec.kleene.star P \<sqinter> spec.rel r = spec.kleene.star (P \<sqinter> spec.rel r)" (is "?lhs = ?rhs")
proof(rule antisym)
  show "?lhs \<le> ?rhs"
    by (induct rule: spec.kleene.star.fixp_induct)
       (simp_all add: ac_simps inf_sup_distrib1 spec.bind.inf_rel le_supI1 le_supI2 spec.bind.mono)
  show "?rhs \<le> ?lhs"
    by (induct rule: spec.kleene.star.fixp_induct)
       (simp_all add: ac_simps le_supI2 inf_sup_distrib1
                      spec.bind.inf_rel spec.bind.mono spec.return.inf_rel)
qed

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "steps"\<close>

lemma simps[simp]:
  shows "(a, s, s) \<notin> spec.steps P"
by (simp add: spec.steps_def exI[where x="UNIV \<times> -Id"]
              spec.rel.minus_Id[where r=UNIV and A=UNIV, simplified] spec.rel.UNIV)

lemma member_conv:
  shows "x \<in> spec.steps P \<longleftrightarrow> (\<exists>\<sigma>. \<lblot>\<sigma>\<rblot> \<le> P \<and> x \<in> trace.steps \<sigma>)"
by (meson spec.rel.galois spec.singleton.rel_le_conv spec.singleton_le_ext_conv subset_Compl_singleton)

setup \<open>Sign.mandatory_path "term"\<close>

lemma none:
  shows "spec.steps (spec.term.none P) = spec.steps P"
by (metis order.eq_iff spec.rel.galois spec.term.all.rel spec.term.galois)

lemma all:
  shows "spec.steps (spec.term.all P) = spec.steps P"
by (metis spec.steps.term.none spec.term.none_all)

setup \<open>Sign.parent_path\<close>

lemmas bot = spec.rel.lower_bot

lemmas monotone = spec.rel.monotone_lower
lemmas mono = monotoneD[OF spec.steps.monotone]

lemmas Sup = spec.rel.lower_Sup
lemmas sup = spec.rel.lower_sup
lemmas Inf_le = spec.rel.lower_Inf_le
lemmas inf_le = spec.rel.lower_inf_le

lemma singleton:
  shows "spec.steps \<lblot>\<sigma>\<rblot> = trace.steps \<sigma>"
by (meson subset_antisym order.refl spec.rel.galois spec.singleton.rel_le_conv)

lemma idle:
  shows "spec.steps spec.idle = {}"
by (simp add: spec.steps_def spec.idle.rel_le)

lemma action:
  shows "spec.steps (spec.action F) = snd ` F - UNIV \<times> Id"
by (force simp: spec.action_def split_def
                spec.steps.Sup spec.steps.sup spec.steps.singleton spec.steps.idle)

lemma return:
  shows "spec.steps (spec.return v) = {}"
by (simp add: spec.return_def spec.steps.action)

lemma bind_le: \<comment>\<open> see \<open>spec.steps.bind\<close> \<close>
  shows "spec.steps (f \<bind> g) \<subseteq> spec.steps f \<union> (\<Union>v. spec.steps (g v))"
by (force simp: spec.steps.member_conv spec.singleton.le_conv trace.split_all trace.steps'.append
         elim!: spec.singleton.bind_le)

lemma kleene_star:
  shows "spec.steps (spec.kleene.star P) = spec.steps P" (is "?lhs = ?rhs")
proof(rule antisym)
  show "?lhs \<le> ?rhs"
  proof(induct rule: spec.kleene.star.fixp_induct[case_names adm bot step])
    case (step S) then show ?case
      by (simp add: spec.steps.sup spec.steps.return order.trans[OF spec.steps.bind_le])
  qed (simp_all add: spec.steps.bot)
  show "?rhs \<le> ?lhs"
    by (simp add: spec.steps.mono spec.kleene.expansive_star)
qed

lemma map:
  shows "spec.steps (spec.map af sf vf P)
       = map_prod af (map_prod sf sf) ` spec.steps P - UNIV \<times> Id"
by (rule spec.singleton.exhaust[of P])
   (force simp: spec.map.Sup spec.map.singleton spec.steps.Sup spec.steps.singleton trace.steps'.map image_Union)

lemma invmap_le:
  shows "spec.steps (spec.invmap af sf vf P)
       \<subseteq> map_prod af (map_prod sf sf) -` (spec.steps (P \<sqinter> spec.rel (range af \<times> range sf \<times> range sf)) \<union> UNIV \<times> Id) - UNIV \<times> Id"
by (simp add: spec.rel.galois spec.rel.minus_Id
              order.trans[OF _ spec.invmap.mono[OF spec.rel.upper_lower_expansive]]
        flip: vimage_Un spec.invmap.rel[where vf=vf] spec.invmap.range)

setup \<open>Sign.mandatory_path "rel"\<close>

lemma monomorphic:
  fixes r :: "('a, 's) steps"
  shows "spec.steps (spec.rel.monomorphic r) = r - UNIV \<times> Id" (is "?lhs = ?rhs")
proof(rule antisym)
  show "?lhs \<subseteq> ?rhs"
    by (simp add: spec.rel.galois spec.rel.minus_Id flip: spec.rel.monomorphic_conv)
  show "?rhs \<subseteq> ?lhs"
    by (force simp: spec.rel.monomorphic.alt_def spec.term.all.Sup spec.term.all.singleton
                    spec.steps.Sup spec.steps.singleton
              dest: spec[where x="trace.T s [(a, s')] None" for a s s']
             split: if_splits)
qed

setup \<open>Sign.parent_path\<close>

lemma rel:
  fixes r :: "('a, 's) steps"
  shows "spec.steps (spec.rel r) = r - UNIV \<times> Id"
by (simp add: spec.rel_def spec.steps.term.all spec.steps.rel.monomorphic)

lemma top:
  shows "spec.steps \<top> = UNIV \<times> - Id"
using spec.steps.rel[where r=UNIV] by (simp add: spec.rel.UNIV)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.parent_path\<close>


subsection\<open> Sequential assertions \label{sec:safety_logic-pre_post} \<close>

text\<open>

We specify sequential behavior with preconditions and postconditions.

\<close>


subsubsection\<open> Preconditions \label{sec:safety_logic-pre_post-pre} \<close>

setup \<open>Sign.mandatory_path "spec"\<close>

definition pre :: "'s pred \<Rightarrow> ('a, 's, 'v) spec" where
  "pre P = \<Squnion>(spec.singleton ` {\<sigma>. P (trace.init \<sigma>)})"

setup \<open>Sign.mandatory_path "singleton"\<close>

lemma pre_le_conv[spec.singleton.le_conv]:
  shows "\<lblot>\<sigma>\<rblot> \<le> spec.pre P \<longleftrightarrow> P (trace.init \<sigma>)"
by (auto simp add: spec.pre_def spec.singleton_le_conv trace.natural_def elim: trace.less_eqE)

lemma inf_pre:
  shows "spec.pre P \<sqinter> \<lblot>\<sigma>\<rblot> = (if P (trace.init \<sigma>) then \<lblot>\<sigma>\<rblot> else \<bottom>)" (is ?thesis1)
    and "\<lblot>\<sigma>\<rblot> \<sqinter> spec.pre P = (if P (trace.init \<sigma>) then \<lblot>\<sigma>\<rblot> else \<bottom>)" (is ?thesis2)
proof -
  show ?thesis1
    by (cases \<sigma>; rule spec.singleton.antisym)
       (auto simp: spec.singleton.le_conv spec.singleton_le_conv spec.singleton.not_bot trace.natural.trace_conv
            split: if_split_asm
             elim: trace.less_eqE)
  then show ?thesis2
    by (rule inf_commute_conv)
qed

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "idle"\<close>

lemma pre_le_conv[spec.idle_le]:
  shows "spec.idle \<le> (spec.pre P :: ('a, 's, 'v) spec) \<longleftrightarrow> P = \<top>" (is "?lhs \<longleftrightarrow> ?rhs")
proof(rule iffI)
  show "?lhs \<Longrightarrow> ?rhs"
    by (rule ccontr)
       (simp add: fun_eq_iff spec.pre_def spec.idle_def trace.split_Ex
                  spec.singleton_le_conv trace.less_eq_None trace.natural.simps)
  show "?rhs \<Longrightarrow> ?lhs"
    by (rule spec.singleton_le_extI) (simp add: spec.singleton.le_conv)
qed

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "term"\<close>

setup \<open>Sign.mandatory_path "all"\<close>

lemma pre:
  shows "spec.term.all (spec.pre P) = spec.pre P"
by (rule spec.singleton.antisym; simp add: spec.singleton.le_conv)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "closed"\<close>

lemma pre:
  shows "spec.pre P \<in> spec.term.closed _"
by (rule spec.term.closed_upper[of "spec.pre P", simplified spec.term.all.pre])

lemma none_inf_pre:
  fixes P :: "'s pred"
  fixes Q :: "('a, 's, 'v) spec"
  shows "spec.term.none (Q \<sqinter> spec.pre P) = (spec.term.none Q \<sqinter> spec.pre P :: ('a, 's, 'w) spec)" (is "?lhs = ?rhs")
    and "spec.term.none (spec.pre P \<sqinter> Q) = (spec.pre P \<sqinter> spec.term.none Q :: ('a, 's, 'w) spec)" (is ?thesis2)
proof -
  show "?lhs = ?rhs"
    apply (subst spec.term.none_all[symmetric])
    apply (subst spec.term.all.inf)
    apply (subst spec.term.closed.none_inf_monomorphic(2)[symmetric])
    apply (simp_all add: spec.term.all.pre spec.term.closed.pre)
    done
  then show ?thesis2
    by (simp add: ac_simps)
qed

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "pre"\<close>

lemma bot[iff]:
  shows "spec.pre \<langle>False\<rangle> = \<bottom>"
    and "spec.pre \<bottom> = \<bottom>"
by (simp_all add: spec.pre_def)

lemma top[iff]:
  shows "spec.pre \<langle>True\<rangle> = \<top>"
    and "spec.pre \<top> = \<top>"
by (simp_all add: spec.pre_def full_SetCompr_eq spec.singleton.top)

lemma top_conv:
  shows "spec.pre P = (\<top> :: ('a, 's, 'v) spec) \<longleftrightarrow> P = \<top>"
by (auto intro: iffD1[OF spec.idle.pre_le_conv[where 'a='a and 's='s and 'v='v]])

lemma K:
  shows "spec.pre \<langle>P\<rangle> = (if P then \<top> else \<bottom>)"
by (simp add: spec.pre_def full_SetCompr_eq spec.singleton.top)

lemma monotone:
  shows "mono spec.pre"
by (fastforce simp: spec.pre_def intro: monoI)

lemmas strengthen[strg] = st_monotone[OF spec.pre.monotone]
lemmas mono = monotoneD[OF spec.pre.monotone]

lemma SUP:
  shows "spec.pre (\<Squnion>x\<in>X. P x) = (\<Squnion>x\<in>X. spec.pre (P x))"
by (auto simp: spec.pre_def spec.eq_iff intro: rev_SUPI)

lemma Sup:
  shows "spec.pre (\<Squnion>X) = (\<Squnion>x\<in>X. spec.pre x)"
by (metis image_ident image_image spec.pre.SUP)

lemma Bex:
  shows "spec.pre (\<lambda>s. \<exists>x\<in>X. P x s) = (\<Squnion>x\<in>X. spec.pre (P x))"
by (simp add: Sup_fun_def flip: spec.pre.SUP)

lemma Ex:
  shows "spec.pre (\<lambda>s. \<exists>x. P x s) = (\<Squnion>x. spec.pre (P x))"
by (simp add: Sup_fun_def flip: spec.pre.SUP)

lemma
  shows disj: "spec.pre (P \<^bold>\<or> Q) = spec.pre P \<squnion> spec.pre Q"
    and sup: "spec.pre (P \<squnion> Q) = spec.pre P \<squnion> spec.pre Q"
using spec.pre.Sup[where X="{P, Q}"] by (simp_all add: sup_fun_def)

lemma INF:
  shows "spec.pre (\<Sqinter>x\<in>X. P x) = (\<Sqinter>x\<in>X. spec.pre (P x))"
by (auto simp: spec.eq_iff spec.singleton.pre_le_conv le_INF_iff intro: spec.singleton_le_extI)

lemma Inf:
  shows "spec.pre (\<Sqinter>X) = (\<Sqinter>x\<in>X. spec.pre x)"
by (metis image_ident image_image spec.pre.INF)

lemma Ball:
  shows "spec.pre (\<lambda>s. \<forall>x\<in>X. P x s) = (\<Sqinter>x\<in>X. spec.pre (P x))"
by (simp add: Inf_fun_def flip: spec.pre.INF)

lemma All:
  shows "spec.pre (\<lambda>s. \<forall>x. P x s) = (\<Sqinter>x. spec.pre (P x))"
by (simp add: Inf_fun_def flip: spec.pre.INF)

lemma inf:
  shows conj: "spec.pre (P \<^bold>\<and> Q) = spec.pre P \<sqinter> spec.pre Q"
    and "spec.pre (P \<sqinter> Q) = spec.pre P \<sqinter> spec.pre Q"
using spec.pre.Inf[where X="{P, Q}"] by (simp_all add: inf_fun_def)

lemma inf_action_le: \<comment>\<open> Converse does not hold \<close>
  shows "spec.pre P \<sqinter> spec.action F \<le> spec.action (UNIV \<times> UNIV \<times> Collect P \<times> UNIV \<inter> F)" (is "?lhs \<le> ?rhs")
    and "spec.action F \<sqinter> spec.pre P \<le> spec.action (F \<inter> UNIV \<times> UNIV \<times> Collect P \<times> UNIV)" (is ?thesis2)
proof -
  show "?lhs \<le> ?rhs"
  proof(rule spec.singleton_le_extI)
    show "\<lblot>\<sigma>\<rblot> \<le> ?rhs" if "\<lblot>\<sigma>\<rblot> \<le> ?lhs" for \<sigma>
      using that[simplified, unfolded spec.singleton.action_le_conv spec.singleton.le_conv]
      by (cases \<sigma>;
          safe; clarsimp simp: trace.steps'.step_conv spec.action.idleI spec.action.stutter_stepsI
                        split: option.split_asm;
          subst spec.singleton.Cons; blast intro: spec.action.stepI)
  qed
  then show ?thesis2
    by (simp add: ac_simps)
qed

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "invmap"\<close>

lemma pre:
  shows "spec.invmap af sf vf (spec.pre P) = spec.pre (\<lambda>s. P (sf s))"
by (rule spec.singleton.antisym) (simp_all add: spec.singleton.le_conv)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "bind"\<close>

lemma inf_pre:
  shows "spec.pre P \<sqinter> (f \<bind> g) = (spec.pre P \<sqinter> f) \<bind> g" (is "?lhs = ?rhs")
    and "(f \<bind> g) \<sqinter> spec.pre P = (f \<sqinter> spec.pre P) \<bind> g" (is ?thesis1)
proof -
  show "?lhs = ?rhs"
  proof(rule antisym)
    show "?lhs \<le> ?rhs"
      by (fastforce simp: spec.bind_def spec.continue_def inf_sup_distrib1 inf_Sup spec.singleton.inf_pre
               simp flip: spec.term.closed.none_inf_pre spec.singleton.pre_le_conv)
    show "?rhs \<le> ?lhs"
      by (fastforce simp: spec.bind_def spec.continue_def inf_sup_distrib1 spec.singleton.pre_le_conv
               simp flip: spec.term.closed.none_inf_pre)
  qed
  then show ?thesis1
    by (simp add: ac_simps)
qed

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "steps"\<close>

lemma pre:
  assumes "P s\<^sub>0"
  shows "spec.steps (spec.pre P :: ('a, 's, 'v) spec) = UNIV \<times> - Id"
proof -
  have "(a, s, s') \<in> spec.steps (spec.pre P)" if "s \<noteq> s'" for a :: 'a and s s'
    using assms that
    by (simp add: spec.singleton.le_conv spec.steps.member_conv trace.steps'.Cons_eq_if
                  exI[where x="trace.T s\<^sub>0 [(undefined, s), (a, s')] None"])
  then show ?thesis
    by auto
qed

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.parent_path\<close>


subsubsection\<open> Postconditions\label{sec:safety_logic-pre_post-post} \<close>

text\<open>

Unlike \<^const>\<open>spec.pre\<close> \<open>spec.post\<close> can be expressed in terms of other constants.

\<close>

setup \<open>Sign.mandatory_path "spec"\<close>

setup \<open>Sign.mandatory_path "post"\<close>

definition act :: "('v \<Rightarrow> 's pred) \<Rightarrow> ('v \<times> 'a \<times> 's \<times> 's) set" where
  "act Q = {(v, a, s, s') |v a s s'. Q v s'}"

setup \<open>Sign.mandatory_path "act"\<close>

lemma simps[simp]:
  shows "spec.post.act \<langle>\<langle>False\<rangle>\<rangle> = {}"
    and "spec.post.act \<langle>\<bottom>\<rangle> = {}"
    and "spec.post.act \<bottom> = {}"
    and "spec.post.act \<langle>\<langle>True\<rangle>\<rangle> = UNIV"
    and "spec.post.act \<langle>\<top>\<rangle> = UNIV"
    and "spec.post.act \<top> = UNIV"
    and "spec.post.act (Q \<squnion> Q') = spec.post.act Q \<union> spec.post.act Q'"
    and "spec.post.act (\<Squnion>X) = (\<Union>x\<in>X. spec.post.act x)"
    and "spec.post.act (\<lambda>v. \<Squnion>x\<in>Y. R x v) = (\<Union>x\<in>Y. spec.post.act (R x))"
by (auto 0 2 simp: spec.post.act_def)

lemma monotone:
  shows "mono spec.post.act"
proof(rule monotoneI)
  show "spec.post.act Q \<le> spec.post.act Q'" if "Q \<le> Q'" for Q Q' :: "'v \<Rightarrow> 's pred"
    using that unfolding spec.post.act_def by blast
qed

lemmas strengthen[strg] = st_monotone[OF spec.post.act.monotone]
lemmas mono = monotoneD[OF spec.post.act.monotone]

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.parent_path\<close>

definition post :: "('v \<Rightarrow> 's pred) \<Rightarrow> ('a, 's, 'v) spec" where
  "post Q = \<top> \<bind> (\<lambda>_::unit. spec.action (spec.post.act Q))"

setup \<open>Sign.mandatory_path "singleton"\<close>

lemma post_le_conv[spec.singleton.le_conv]:
  fixes Q :: "'v \<Rightarrow> 's pred"
  shows "\<lblot>\<sigma>\<rblot> \<le> spec.post Q
    \<longleftrightarrow> (case trace.term \<sigma> of None \<Rightarrow> True | Some v \<Rightarrow> Q v (trace.final \<sigma>))" (is "?lhs \<longleftrightarrow> ?rhs")
proof(rule iffI)
  show "?lhs \<Longrightarrow> ?rhs"
    by (fastforce simp: spec.post_def spec.post.act_def
                        spec.singleton.le_conv spec.singleton.action_le_conv trace.steps'.step_conv
                 split: option.split
                  elim: spec.singleton.bind_le)
  show "?rhs \<Longrightarrow> ?lhs"
    by (cases \<sigma>)
       (simp add: spec.post_def spec.post.act_def spec.action.stutterI
                  spec.bind.incompleteI spec.bind.continueI[where ys="[]", simplified]
           split: option.splits)
qed

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "idle"\<close>

lemma post_le[spec.idle_le]:
  shows "spec.idle \<le> spec.post Q"
by (rule spec.singleton_le_extI) (simp add: spec.singleton.le_conv)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "term"\<close>

setup \<open>Sign.mandatory_path "none"\<close>

lemma post_le:
  shows "spec.term.none P \<le> spec.post Q"
by (rule spec.singleton_le_extI) (simp add: spec.singleton.le_conv)

lemma post:
  shows "spec.term.none (spec.post Q :: ('a, 's, 'v) spec)
       = spec.term.none (\<top> :: ('a, 's, unit) spec)"
by (metis spec.eq_iff spec.term.galois spec.term.none.post_le spec.term.none_all top_greatest)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "all"\<close>

lemma post:
  shows "spec.term.all (spec.post Q) = \<top>"
by (metis spec.term.all_none spec.term.none.post spec.term.upper_top)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "post"\<close>

lemma bot[iff]:
  shows "spec.post \<langle>\<langle>False\<rangle>\<rangle> = spec.term.none (\<top> :: (_, _, unit) spec)"
    and "spec.post \<langle>\<bottom>\<rangle> = spec.term.none (\<top> :: (_, _, unit) spec)"
    and "spec.post \<bottom> = spec.term.none (\<top> :: (_, _, unit) spec)"
by (simp_all add: spec.post_def spec.action.empty spec.bind.idleR spec.bind.botR)

lemma monotone:
  shows "mono spec.post"
by (simp add: spec.post_def monoI spec.action.mono spec.bind.mono spec.post.act.mono)

lemmas strengthen[strg] = st_monotone[OF spec.post.monotone]
lemmas mono = monotoneD[OF spec.post.monotone]

lemma SUP_not_empty:
  fixes X :: "'a set"
  fixes Q :: "'a \<Rightarrow> 'v \<Rightarrow> 's pred"
  assumes "X \<noteq> {}"
  shows "spec.post (\<lambda>v. \<Squnion>x\<in>X. Q x v) = (\<Squnion>x\<in>X. spec.post (Q x))"
by (simp add: assms spec.post_def flip: spec.bind.SUPR_not_empty spec.action.SUP_not_empty)

lemma disj:
  shows "spec.post (Q \<squnion> Q') = spec.post Q \<squnion> spec.post Q'"
    and "spec.post (\<lambda>rv. Q rv \<squnion> Q' rv) = spec.post Q \<squnion> spec.post Q'"
    and "spec.post (\<lambda>rv. Q rv \<^bold>\<or> Q' rv) = spec.post Q \<squnion> spec.post Q'"
using spec.post.SUP_not_empty[where X="UNIV" and Q="\<lambda>x. if x then Q' else Q"]
by (simp_all add: UNIV_bool sup_fun_def)

lemma INF:
  shows "spec.post (\<Sqinter>x\<in>X. Q x) = (\<Sqinter>x\<in>X. spec.post (Q x))"
    and "spec.post (\<lambda>v. \<Sqinter>x\<in>X. Q x v) = (\<Sqinter>x\<in>X. spec.post (Q x))"
    and "spec.post (\<lambda>v s. \<Sqinter>x\<in>X. Q x v s) = (\<Sqinter>x\<in>X. spec.post (Q x))"
by (fastforce intro: antisym spec.singleton_le_extI simp: spec.singleton.le_conv le_Inf_iff split: option.split)+

lemma Inf:
  shows "spec.post (\<Sqinter>X) = (\<Sqinter>x\<in>X. spec.post x)"
by (metis image_ident image_image spec.post.INF(1))

lemma Ball:
  shows "spec.post (\<lambda>v s. \<forall>x\<in>X. Q x v s) = (\<Sqinter>x\<in>X. spec.post (Q x))"
by (simp add: Inf_fun_def flip: spec.post.INF)

lemma All:
  shows "spec.post (\<lambda>v s. \<forall>x. Q x v s) = (\<Sqinter>x. spec.post (Q x))"
by (simp add: Inf_fun_def flip: spec.post.INF)

lemma inf:
  shows "spec.post (Q \<sqinter> Q') = spec.post Q \<sqinter> spec.post Q'"
    and "spec.post (\<lambda>rv. Q rv \<sqinter> Q' rv) = spec.post Q \<sqinter> spec.post Q'"
    and conj: "spec.post (\<lambda>rv. Q rv \<^bold>\<and> Q' rv) = spec.post Q \<sqinter> spec.post Q'"
by (simp_all add: inf_fun_def flip: spec.post.INF[where X="UNIV" and Q="\<lambda>x. if x then Q' else Q", simplified UNIV_bool, simplified])

lemma top[iff]:
  shows "spec.post \<langle>\<langle>True\<rangle>\<rangle> = \<top>"
    and "spec.post \<langle>\<top>\<rangle> = \<top>"
    and "spec.post \<top> = \<top>"
by (simp_all add: top_fun_def flip: spec.post.INF[where X="{}", simplified])

lemma top_conv:
  shows "spec.post Q = (\<top> :: ('a, 's, 'v) spec) \<longleftrightarrow> Q = \<top>"
by (fastforce simp: spec.singleton.post_le_conv
              dest: arg_cong[where f="\<lambda>x. \<forall>\<sigma>. \<lblot>\<sigma>\<rblot> \<le> x"] spec[where x="trace.T s [] (Some v)" for s v])

lemma K:
  shows "spec.post (\<lambda>_ _. Q) = (if Q then \<top> else \<top> \<bind> (\<lambda>_::unit. \<bottom>))"
by (auto  simp flip: spec.bind.botR bot_fun_def)

setup \<open>Sign.parent_path\<close>

lemma bind_post_pre:
  shows "f \<sqinter> spec.post Q \<bind> g = f \<bind> (\<lambda>v. g v \<sqinter> spec.pre (Q v))" (is "?lhs = ?rhs")
    and "spec.post Q \<sqinter> f \<bind> g = f \<bind> (\<lambda>v. spec.pre (Q v) \<sqinter> g v)" (is ?thesis1)
proof -
  show "?lhs = ?rhs"
  proof(rule spec.singleton.antisym)
    show "\<lblot>\<sigma>\<rblot> \<le> ?rhs" if "\<lblot>\<sigma>\<rblot> \<le> ?lhs" for \<sigma>
      using that
      by (induct rule: spec.singleton.bind_le)
         (cases \<sigma>; force simp: trace.split_all spec.singleton.le_conv
                        intro: spec.bind.incompleteI spec.bind.continueI)+
    show "\<lblot>\<sigma>\<rblot> \<le> ?lhs" if "\<lblot>\<sigma>\<rblot> \<le> ?rhs" for \<sigma>
      using that
      by (induct rule: spec.singleton.bind_le)
         (cases \<sigma>; force simp: trace.split_all spec.singleton.le_conv
                        intro: spec.bind.incompleteI spec.bind.continueI)+
qed
  then show ?thesis1
    by (simp add: ac_simps)
qed

setup \<open>Sign.mandatory_path "invmap"\<close>

lemma post:
  shows "spec.invmap af sf vf (spec.post Q) = spec.post (\<lambda>v s. Q (vf v) (sf s))"
by (rule antisym[OF spec.singleton_le_extI spec.singleton_le_extI])
   (simp_all add: spec.singleton.invmap_le_conv spec.singleton.post_le_conv trace.final'.map split: option.split_asm)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "action"\<close>

lemma post_le_conv:
  shows "spec.action F \<le> spec.post Q \<longleftrightarrow> (\<forall>v a s s'. (v, a, s, s') \<in> F \<longrightarrow> Q v s')"
by (fastforce simp: spec.action_def split_def spec.singleton.le_conv spec.idle.post_le)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "bind"\<close>

lemma post_le:
  assumes "\<And>v. g v \<le> spec.post Q"
  shows "f \<bind> g \<le> spec.post Q"
by (strengthen ord_to_strengthen(1)[OF assms])
   (simp add: spec.post_def spec.bind.mono flip: spec.bind.bind)

lemma inf_post:
  shows "(f \<bind> g) \<sqinter> spec.post Q = f \<bind> (\<lambda>v. g v \<sqinter> spec.post Q)" (is "?lhs = ?rhs")
    and "spec.post Q \<sqinter> (f \<bind> g) = f \<bind> (\<lambda>v. spec.post Q \<sqinter> g v)" (is ?thesis2)
proof -
  show "?lhs = ?rhs"
  proof(rule antisym[OF spec.singleton_le_extI])
    fix \<sigma>
    assume lhs: "\<lblot>\<sigma>\<rblot> \<le> ?lhs"
    from lhs[simplified, THEN conjunct1] lhs[simplified, THEN conjunct2] show "\<lblot>\<sigma>\<rblot> \<le> ?rhs"
    proof(induct rule: spec.singleton.bind_le)
      case (continue \<sigma>\<^sub>f \<sigma>\<^sub>g v\<^sub>f) then show ?case
        by (cases \<sigma>\<^sub>f)
           (force intro: spec.bind.continueI simp: spec.singleton.le_conv split: option.split)
    qed (simp add: spec.singleton.bind_le_conv)
  qed (simp add: spec.bind.mono spec.bind.post_le)
  then show ?thesis2
    by (simp add: ac_simps)
qed

lemma mono_stronger:
  assumes f: "f \<le> f' \<sqinter> spec.post Q"
  assumes g: "\<And>v. g v \<sqinter> spec.pre (Q v) \<le> g' v"
  shows "spec.bind f g \<le> spec.bind f' g'"
by (strengthen ord_to_strengthen(1)[OF f]) (simp add: g spec.bind.mono spec.bind_post_pre)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.parent_path\<close>


subsubsection\<open> Strongest postconditions\label{sec:safety_logic-strongest_post} \<close>

setup \<open>Sign.mandatory_path "spec.post"\<close>

definition strongest :: "('a, 's, 'v) spec \<Rightarrow> 'v \<Rightarrow> 's pred" where
  "strongest P = \<Sqinter>{Q. P \<le> spec.post Q}"

interpretation strongest: galois.complete_lattice_class "spec.post.strongest" "spec.post"
by (simp add: spec.post.strongest_def galois.upper_preserves_InfI spec.post.Inf spec.post.monotone)

lemma strongest_alt_def:
  shows "spec.post.strongest P = (\<lambda>v s. \<exists>\<sigma>. \<lblot>\<sigma>\<rblot> \<le> P \<and> trace.term \<sigma> = Some v \<and> trace.final \<sigma> = s)" (is "?lhs = ?rhs")
proof(rule antisym)
  show "?lhs \<le> ?rhs"
    by (rule spec.singleton.exhaust[of P])
       (fastforce simp: spec.post.strongest_def spec.singleton.le_conv
                  dest: spec[where x="\<lambda>v s. \<exists>\<sigma>\<in>X. trace.term \<sigma> = Some v \<and> trace.final \<sigma> = s" for X]
                 split: option.split)
  show "?rhs \<le> ?lhs"
    by (fastforce simp: spec.post.strongest_def spec.singleton.le_conv dest: order.trans)
qed

setup \<open>Sign.mandatory_path "strongest"\<close>

lemma singleton:
  shows "spec.post.strongest \<lblot>\<sigma>\<rblot>
      = (\<lambda>v s. case trace.term \<sigma> of None \<Rightarrow> False | Some v' \<Rightarrow> v' = v \<and> trace.final \<sigma> = s)"
by (auto simp: spec.post.strongest_alt_def fun_eq_iff trace.split_all
         cong: trace.final'.natural'_cong
        split: option.split)

lemmas monotone = spec.post.strongest.monotone_lower
lemmas mono = monoD[OF spec.post.strongest.monotone]
lemmas Sup = spec.post.strongest.lower_Sup
lemmas sup = spec.post.strongest.lower_sup

lemma top[iff]:
  shows "spec.post.strongest \<top> = \<top>"
by (simp add: spec.post.strongest_def spec.post.top_conv top.extremum_unique)

lemma action:
  shows "spec.post.strongest (spec.action F) = (\<lambda>v s'. \<exists>a s. (v, a, s, s') \<in> F)"
by (simp add: spec.post.strongest_def spec.action.post_le_conv) fast

lemma return:
  shows "spec.post.strongest (spec.return v) = (\<lambda>v' s. v' = v)"
by (simp add: spec.return_def spec.post.strongest.action)

setup \<open>Sign.mandatory_path "term"\<close>

lemma none:
  shows "spec.post.strongest (spec.term.none P) = \<bottom>"
by (clarsimp simp: spec.term.none_def spec.post.strongest.Sup spec.post.strongest.singleton fun_eq_iff)

lemma all:
  assumes "spec.idle \<le> P"
  shows "spec.post.strongest (spec.term.all P) = \<top>"
by (rule top_le[OF order.trans[OF _ spec.post.strongest.mono[OF spec.term.all.mono[OF assms]]]])
   (simp add: spec.term.all.idle spec.post.strongest.Sup spec.post.strongest.return Sup_fun_def top_fun_def)

lemma closed:
  assumes "spec.idle \<le> P"
  assumes "P \<in> spec.term.closed _"
  shows "spec.post.strongest P = \<top>"
by (metis spec.post.strongest.term.all[OF assms(1)] spec.term.all.closed_conv[OF assms(2)])

setup \<open>Sign.parent_path\<close>

lemma bind:
  shows "spec.post.strongest (f \<bind> g)
       = spec.post.strongest (\<Squnion>v. spec.pre (spec.post.strongest f v) \<sqinter> g v)" (is "?lhs = ?rhs")
proof(rule antisym)
  show "?lhs \<le> ?rhs"
    by (auto 0 4 simp: spec.post.strongest_alt_def spec.singleton.le_conv
                elim!: spec.singleton.bind_le)
  show "?rhs \<le> ?lhs"
    by (force simp: spec.post.strongest_alt_def spec.singleton.le_conv trace.split_all
              dest: spec.bind.continueI)
qed

lemma rel:
  shows "spec.post.strongest (spec.rel r) = \<top>"
by (simp add: spec.rel_def spec.post.strongest.term.all spec.idle.kleene.star_le)

lemma pre:
  shows "spec.post.strongest (spec.pre P) = (\<lambda>v s'. \<exists>s. P s)"
by (auto simp: spec.post.strongest_alt_def spec.singleton.le_conv trace.split_Ex fun_eq_iff
       intro!: exI[where x="[(undefined, s)]" for s])

lemma post:
  shows "spec.post.strongest (spec.post Q) = Q"
by (auto simp: spec.post.strongest_alt_def spec.singleton.le_conv trace.split_Ex fun_eq_iff
       intro!: exI[where x="[]"])

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.parent_path\<close>


subsection\<open> Initial steps\label{sec:safety_logic-initial_steps} \<close>

text\<open>

The initial transition of a process.

\<close>

setup \<open>Sign.mandatory_path "spec"\<close>

definition initial_steps :: "('a, 's, 'v) spec \<Rightarrow> ('a, 's) steps" where
  "initial_steps P = {(a, s, s'). \<lblot>s, [(a, s')], None\<rblot> \<le> P}"

setup \<open>Sign.mandatory_path "initial_steps"\<close>

lemma steps_le:
  shows "spec.initial_steps P \<subseteq> spec.steps P \<union> UNIV \<times> Id"
by (fastforce simp: spec.initial_steps_def spec.steps.member_conv split: if_splits)

lemma galois:
  shows "r \<subseteq> spec.initial_steps P \<and> spec.idle \<le> P \<longleftrightarrow> spec.action ({()} \<times> r) \<bind> \<bottom> \<le> P" (is "?lhs \<longleftrightarrow> ?rhs")
proof(rule iffI)
  show "?lhs \<Longrightarrow> ?rhs"
    by (auto simp: spec.action_def spec.initial_steps_def spec.bind.SupL spec.bind.supL
                   spec.bind.singletonL spec.singleton.not_bot spec.term.none.singleton)
  show "?rhs \<Longrightarrow> ?lhs"
    by (auto simp: spec.initial_steps_def spec.idle.action_le spec.idle.bind_le_conv
            elim!: order.trans[rotated]
            intro: spec.action.stepI spec.bind.incompleteI)
qed

lemma bot:
  shows "spec.initial_steps \<bottom> = {}"
by (auto simp: spec.initial_steps_def spec.singleton.not_bot)

lemma top:
  shows "spec.initial_steps \<top> = UNIV"
by (auto simp: spec.initial_steps_def spec.singleton.not_bot)

lemma monotone:
  shows "mono spec.initial_steps"
by (force intro: monoI simp: spec.initial_steps_def)

lemmas strengthen[strg] = st_monotone[OF spec.initial_steps.monotone]
lemmas mono = monotoneD[OF spec.initial_steps.monotone]

lemma Sup:
  shows "spec.initial_steps (\<Squnion>X) = \<Union>(spec.initial_steps ` X)"
by (auto simp: spec.initial_steps_def)

lemma Inf:
  shows "spec.initial_steps (\<Sqinter>X) = \<Inter>(spec.initial_steps ` X)"
by (auto simp: spec.initial_steps_def le_Inf_iff)

lemma idle:
  shows "spec.initial_steps spec.idle = UNIV \<times> Id"
by (auto simp: spec.initial_steps_def spec.singleton.le_conv)

lemma action:
  shows "spec.initial_steps (spec.action F) = snd ` F \<union> UNIV \<times> Id"
by (auto simp: spec.initial_steps_def spec.singleton.action_le_conv trace.steps'.step_conv)

lemma return:
  shows "spec.initial_steps (spec.return v) = UNIV \<times> Id"
by (auto simp: spec.initial_steps_def spec.singleton.le_conv)

lemma bind:
  shows "spec.initial_steps (f \<bind> g)
       = spec.initial_steps f
         \<union> spec.initial_steps (\<Squnion>v. spec.pre (spec.post.strongest (f \<sqinter> spec.return v) v) \<sqinter> g v)" (is "?lhs = ?rhs")
proof(rule antisym)
  show "?lhs \<le> ?rhs"
    by (fastforce simp: spec.initial_steps_def spec.post.strongest_alt_def spec.singleton.le_conv
                        trace.split_all Cons_eq_append_conv trace.natural.simps
                 elim!: spec.singleton.bind_le)
  show "?rhs \<le> ?lhs"
    by (auto simp: spec.initial_steps_def spec.post.strongest_alt_def spec.singleton.le_conv
                   trace.split_all spec.bind.incompleteI order.trans[OF _ spec.bind.continueI, rotated])
qed

lemma rel:
  shows "spec.initial_steps (spec.rel r) = r \<union> UNIV \<times> Id"
by (auto simp: spec.initial_steps_def spec.singleton.le_conv)

lemma pre:
  shows "spec.initial_steps (spec.pre P) = UNIV \<times> Pre P"
by (auto simp: spec.initial_steps_def spec.singleton.le_conv)

lemma post:
  shows "spec.initial_steps (spec.post Q) = UNIV"
by (auto simp: spec.initial_steps_def spec.singleton.le_conv)

setup \<open>Sign.mandatory_path "term"\<close>

lemma none:
  shows "spec.initial_steps (spec.term.none P) = spec.initial_steps P"
by (auto simp: spec.initial_steps_def spec.singleton.le_conv)

lemma all:
  shows "spec.initial_steps (spec.term.all P) = spec.initial_steps P"
by (auto simp: spec.initial_steps_def spec.singleton.le_conv order.trans[rotated]
               spec.singleton.mono trace.less_eq_None)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.parent_path\<close>


subsection\<open> Heyting implication\label{sec:safety_logic-heyting} \<close>

setup \<open>Sign.mandatory_path "spec"\<close>

setup \<open>Sign.mandatory_path "singleton"\<close>

lemma heyting_le_conv:
  shows "\<lblot>\<sigma>\<rblot> \<le> P \<^bold>\<longrightarrow>\<^sub>H Q \<longleftrightarrow> (\<forall>\<sigma>'\<le>\<sigma>. \<lblot>\<sigma>'\<rblot> \<le> P \<longrightarrow> \<lblot>\<sigma>'\<rblot> \<le> Q)" (is "?lhs \<longleftrightarrow> ?rhs")
proof(rule iffI)
  show "?lhs \<Longrightarrow> ?rhs"
    by (meson order.trans heyting.mp spec.singleton.mono)
  show "?rhs \<Longrightarrow> ?lhs"
    by (rule spec.singleton.exhaust[of P])
       (clarsimp simp: heyting inf_Sup spec.singleton.inf trace.less_eq_take_def spec.singleton_le_conv;
        metis spec.singleton.simps(1) trace.take.naturalE(2))
qed

setup \<open>Sign.parent_path\<close>

text\<open>

Connect the generic definition of Heyting implication to a concrete one in the model.

\<close>

lift_definition heyting :: "('a, 's, 'v) spec \<Rightarrow> ('a, 's, 'v) spec \<Rightarrow> ('a, 's, 'v) spec" is
  downwards.imp
by (rule raw.spec.closed.downwards_imp)

lemma heyting_alt_def:
  shows "(\<^bold>\<longrightarrow>\<^sub>H) = (spec.heyting :: _\<Rightarrow>_\<Rightarrow>('a, 's, 'v) spec)"
proof -
  have "P \<le> spec.heyting Q R \<longleftrightarrow> P \<sqinter> Q \<le> R" for P Q R :: "('a, 's, 'v) spec"
    by transfer (simp add: raw.spec.closed.heyting_downwards_imp)
  with heyting show ?thesis by (intro fun_eqI antisym; fast)
qed

declare spec.heyting.transfer[transfer_rule del]

setup \<open>Sign.mandatory_path "heyting"\<close>

lemma transfer_alt[transfer_rule]:
  shows "rel_fun (pcr_spec (=) (=) (=)) (rel_fun (pcr_spec (=) (=) (=)) (pcr_spec (=) (=) (=))) downwards.imp (\<^bold>\<longrightarrow>\<^sub>H)"
by (simp add: spec.heyting.transfer spec.heyting_alt_def)

text\<open>

An example due to \<^citet>\<open>\<open>p504\<close> in "AbadiMerz:1995"\<close>
where the (TLA) model validates a theorem that is not intuitionistically valid.
This is ``some kind of linearity'' and intuitively encodes disjunction elimination.

\<close>

lemma linearity:
  fixes Q :: "(_, _, _) spec"
  shows "((P \<^bold>\<longrightarrow>\<^sub>H Q) \<^bold>\<longrightarrow>\<^sub>H R) \<sqinter> ((Q \<^bold>\<longrightarrow>\<^sub>H P) \<^bold>\<longrightarrow>\<^sub>H R) \<le> R"
by transfer
   (clarsimp simp: downwards.imp_def;
    meson downwards.closed_in[OF _ _ raw.spec.closed.downwards_closed] trace.less_eq_same_cases order.refl)

lemma SupR:
  fixes P :: "(_, _, _) spec"
  assumes "X \<noteq> {}"
  shows "P \<^bold>\<longrightarrow>\<^sub>H (\<Squnion>x\<in>X. Q x) = (\<Squnion>x\<in>X. P \<^bold>\<longrightarrow>\<^sub>H Q x)" (is "?lhs = ?rhs")
proof(rule antisym[OF spec.singleton_le_extI heyting.SUPR_le])
  show "\<lblot>\<sigma>\<rblot> \<le> ?rhs" if "\<lblot>\<sigma>\<rblot> \<le> ?lhs" for \<sigma>
  proof(cases "\<lblot>\<sigma>\<rblot> \<le> P")
    case True with \<open>\<lblot>\<sigma>\<rblot> \<le> ?lhs\<close> show ?thesis by (simp add: heyting inf.absorb1)
  next
    case False show ?thesis
    proof(cases "\<lblot>trace.init \<sigma>, [], None\<rblot> \<le> P")
      case True with \<open>\<not> \<lblot>\<sigma>\<rblot> \<le> P\<close>
      obtain j where "\<forall>i\<le>j. \<lblot>trace.take i \<sigma>\<rblot> \<le> P"
                 and "\<not> \<lblot>trace.take (Suc j) \<sigma>\<rblot> \<le> P"
        using ex_least_nat_less[where P="\<lambda>i. \<not>\<lblot>trace.take i \<sigma>\<rblot> \<le> P" and n="Suc (length (trace.rest \<sigma>))"]
        by (clarsimp simp: less_Suc_eq_le simp flip: trace.take.Ex_all)
      with \<open>\<lblot>\<sigma>\<rblot> \<le> ?lhs\<close> show ?thesis
        by (clarsimp simp: spec.singleton.heyting_le_conv dest!: spec[where x="trace.take j \<sigma>"])
           (metis not_less_eq_eq order_refl spec.singleton.mono spec.singleton_le_ext_conv
                  trace.less_eq_takeE trace.take.mono)
    next
      case False with \<open>X \<noteq> {}\<close> \<open>\<lblot>\<sigma>\<rblot> \<le> ?lhs\<close> show ?thesis
        by (clarsimp simp: spec.singleton.heyting_le_conv simp flip: ex_in_conv)
           (metis "trace.take.0" spec.singleton.takeI trace.less_eq_take_def trace.take.sel(1))
    qed
  qed
qed

lemma cont:
  fixes P :: "(_, _, _) spec"
  shows "cont Sup (\<le>) Sup (\<le>) ((\<^bold>\<longrightarrow>\<^sub>H) P)"
by (rule contI) (simp add: spec.heyting.SupR[where Q=id, simplified])

lemma mcont:
  fixes P :: "(_, _, _) spec"
  shows "mcont Sup (\<le>) Sup (\<le>) ((\<^bold>\<longrightarrow>\<^sub>H) P)"
by (simp add: mcontI[OF _ spec.heyting.cont])

lemmas mcont2mcont[cont_intro] = mcont2mcont[OF spec.heyting.mcont, of luba orda Q P] for luba orda Q P

lemma non_triv:
  shows "P \<^bold>\<longrightarrow>\<^sub>H \<bottom> \<le> P \<longleftrightarrow> spec.idle \<le> P" (is "?lhs \<longleftrightarrow> ?rhs")
proof(rule iffI)
  show "?lhs \<Longrightarrow> ?rhs"
    by (rule spec.singleton.exhaust[of P])
       (fastforce dest: spec[where x="\<lblot>x, [], None\<rblot>" for x]
                  simp: spec.idle_def heyting_def heyting.inf_Sup_distrib trace.split_all
                        spec.singleton.inf spec.singleton_le_conv trace.less_eq_None trace.natural.simps)
  have "spec.idle \<^bold>\<longrightarrow>\<^sub>H \<bottom> \<le> spec.idle"
    by (fastforce intro: spec.singleton_le_extI
                   dest: spec[where x="trace.T (trace.init \<sigma>) [] None" for \<sigma>]
                   simp: spec.singleton.le_conv spec.singleton.heyting_le_conv spec.singleton.not_bot trace.less_eq_None)
  then show ?lhs if ?rhs
    by - (strengthen ord_to_strengthen(2)[OF \<open>?rhs\<close>])
qed

lemma post:
  shows "spec.post Q \<^bold>\<longrightarrow>\<^sub>H spec.post Q' = spec.post (\<lambda>v s. Q v s \<longrightarrow> Q' v s)" (is "?lhs = ?rhs")
proof(rule antisym)
  show "?lhs \<le> ?rhs"
    by (auto intro: spec.singleton_le_extI simp: spec.singleton.heyting_le_conv spec.singleton.le_conv split: option.splits)
  show "?rhs \<le> ?lhs"
    by (auto simp add: heyting simp flip: spec.post.conj intro: spec.post.mono)
qed

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "invmap"\<close>

lemma heyting:
  shows "spec.invmap af sf vf (P \<^bold>\<longrightarrow>\<^sub>H Q) = spec.invmap af sf vf P \<^bold>\<longrightarrow>\<^sub>H spec.invmap af sf vf Q" (is "?lhs = ?rhs")
proof(rule antisym)
  show "?lhs \<le> ?rhs" by (simp add: heyting heyting.detachment spec.invmap.mono flip: spec.invmap.inf)
  show "?rhs \<le> ?lhs"
    by (simp add: heyting heyting.detachment spec.map.inf_distr flip: spec.map_invmap.galois spec.invmap.inf)
       (simp add: spec.invmap.mono spec.map_invmap.galois)
qed

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "term"\<close>

lemma heyting_noneL_allR_mono:
  fixes P :: "(_, _, 'v) spec"
  fixes Q :: "(_, _, 'v) spec"
  shows "spec.term.none P \<^bold>\<longrightarrow>\<^sub>H Q = P \<^bold>\<longrightarrow>\<^sub>H spec.term.all Q" (is "?lhs = ?rhs")
proof(rule antisym)
  show "?lhs \<le> ?rhs"
    by (simp add: heyting spec.term.none.inf flip: spec.term.galois) (simp add: heyting.uncurry)
  show "?rhs \<le> ?lhs"
    by (simp add: heyting heyting.discharge spec.term.closed.none_inf_monomorphic spec.term.galois)
qed

setup \<open>Sign.mandatory_path "all"\<close>

lemma heyting: \<comment>\<open> polymorphic \<^const>\<open>spec.term.all\<close> \<close>
  fixes P :: "(_, _, 'v) spec"
  fixes Q :: "(_, _, 'v) spec"
  shows "(spec.term.all (P \<^bold>\<longrightarrow>\<^sub>H Q) :: (_, _, 'w) spec)
       = spec.term.none P \<^bold>\<longrightarrow>\<^sub>H spec.term.all Q" (is "?lhs = ?rhs")
proof(rule antisym)
  show "?lhs \<le> ?rhs"
    by (simp add: heyting spec.term.none.inf flip: spec.term.galois)
       (metis heyting.detachment(2) le_inf_iff spec.term.none.contractive spec.term.none.inf(2))
  have "spec.term.none (spec.term.none P \<^bold>\<longrightarrow>\<^sub>H spec.term.all Q :: (_, _, 'w) spec)
          \<sqinter> spec.term.none (spec.term.none P :: (_, _, 'w) spec)
     \<le> Q"
    by (metis heyting.detachment(2) inf_sup_ord(2) spec.term.galois spec.term.none.inf(2))
  then show "?rhs \<le> ?lhs"
    by (simp add: heyting flip: spec.term.galois)
       (metis spec.term.cl_def spec.term.all.monomorphic spec.term.none_all
              heyting.detachment(2) spec.term.heyting_noneL_allR_mono)
qed

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "none"\<close>

lemma heyting_le:
  shows "spec.term.none (P \<^bold>\<longrightarrow>\<^sub>H Q) \<le> spec.term.all P \<^bold>\<longrightarrow>\<^sub>H spec.term.none Q"
by (simp add: spec.term.galois spec.term.all.heyting heyting.mono spec.term.all.expansive)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "closed"\<close>

lemma heyting:
  assumes "Q \<in> spec.term.closed _"
  shows "P \<^bold>\<longrightarrow>\<^sub>H Q \<in> spec.term.closed _"
by (rule spec.term.closed_clI)
   (simp add: spec.term.all.heyting spec.term.heyting_noneL_allR_mono spec.term.all.monomorphic
        flip: spec.term.all.closed_conv[OF assms])

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.parent_path\<close>


subsection\<open> Miscellaneous algebra \<close>

setup \<open>Sign.mandatory_path "spec"\<close>

setup \<open>Sign.mandatory_path "steps"\<close>

lemma bind:
  shows "spec.steps (f \<bind> g)
       = spec.steps f \<union> (\<Union>v. spec.steps (spec.pre (spec.post.strongest f v) \<sqinter> g v))" (is "?lhs = ?rhs")
proof(rule antisym)
 show "?lhs \<le> ?rhs"
  unfolding spec.rel.galois
  by (rule spec.singleton_le_extI)
     (fastforce elim!: spec.singleton.bind_le
                 simp: spec.singleton.le_conv spec.steps.member_conv trace.steps'.append
                       spec.post.strongest_alt_def)
  show "?rhs \<le> ?lhs"
    by (fastforce simp: spec.post.strongest_alt_def spec.bind_def spec.continue_def
                        spec.steps.term.none spec.steps.Sup spec.steps.sup spec.steps.singleton
                        spec.steps.member_conv spec.singleton.le_conv trace.split_Ex trace.steps'.append)
qed

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "map"\<close>

lemma idle:
  shows "spec.map af sf vf spec.idle = spec.pre (\<lambda>s. s \<in> range sf) \<sqinter> spec.idle" (is "?lhs = ?rhs")
proof(rule antisym)
  show "?lhs \<le> ?rhs"
    by (auto simp: spec.idle_def spec.map.Sup spec.map.singleton spec.singleton.pre_le_conv)
  show "?rhs \<le> ?lhs"
    by (auto simp: spec.idle_def spec.pre_def trace.split_all image_image inf_Sup Sup_inf
                   spec.map.Sup spec.map.singleton spec.singleton.inf
            elim!: trace.less_eqE)
qed

lemma return:
  fixes F :: "('v \<times> 'a \<times> 's \<times> 's) set"
  shows "spec.map af sf vf (spec.return v)
       = spec.pre (\<lambda>s. s \<in> range sf) \<sqinter> spec.return (vf v)" (is "?lhs = ?rhs")
proof(rule antisym[OF _ spec.singleton_le_extI])
  show "?lhs \<le> ?rhs"
    by (force simp: spec.return_def spec.action_def spec.idle_def
                    spec.map.Sup spec.map.sup spec.map.singleton spec.singleton.pre_le_conv)
  fix \<sigma>
  assume "\<lblot>\<sigma>\<rblot> \<le> ?rhs"
  then obtain s where "trace.init \<sigma> = sf s" by (clarsimp simp: spec.singleton.le_conv)
  with \<open>\<lblot>\<sigma>\<rblot> \<le> ?rhs\<close> show "\<lblot>\<sigma>\<rblot> \<le> ?lhs"
    by (simp add: spec.singleton.le_conv exI[where x="trace.T s [] (Some v)"]
                  spec.singleton_le_conv trace.natural_def trace.less_eq_None
            flip: trace.natural'.eq_Nil_conv
           split: option.split_asm)
qed

lemma kleene_star_le:
  fixes P :: "('a, 's, unit) spec"
  fixes af :: "'a \<Rightarrow> 'b"
  fixes sf :: "'s \<Rightarrow> 't"
  fixes vf :: "unit \<Rightarrow> unit"
  shows "spec.map af sf vf (spec.kleene.star P) \<le> spec.kleene.star (spec.map af sf vf P)" (is "_ \<le> ?rhs")
proof(induct rule: spec.kleene.star.fixp_induct[where P="\<lambda>R. spec.map af sf vf (R P) \<le> ?rhs", case_names adm bot step])
  case (step R) show ?case
    apply (simp add: spec.map.sup spec.map.return order.trans[OF _ spec.kleene.epsilon_star_le])
    apply (subst spec.kleene.star.simps)
    apply (strengthen ord_to_strengthen(1)[OF spec.map.bind_le])
    apply (strengthen ord_to_strengthen(1)[OF step])
    apply (simp add: fun_unit_id[where f=vf])
    done
qed (simp_all add: spec.map.bot)

lemma rel_le:
  shows "spec.map af sf vf (spec.rel r) \<le> spec.rel (map_prod af (map_prod sf sf) ` r)"
apply (simp add: spec.rel_def spec.term.none.map flip: spec.term.galois)
apply (simp add: spec.rel.act_def flip: spec.term.none.map[where vf=id])
apply (strengthen ord_to_strengthen(1)[OF spec.map.kleene_star_le])
apply (strengthen ord_to_strengthen(1)[OF spec.map.action_le])
apply (strengthen ord_to_strengthen(1)[OF spec.term.none.contractive])
apply (auto intro!: monotoneD[OF spec.kleene.monotone_star] spec.action.mono)
done

text\<open>

General lemmas for \<^const>\<open>spec.map\<close> are elusive. We relate it to \<^const>\<open>spec.rel\<close>, \<^const>\<open>spec.pre\<close>
and \<^const>\<open>spec.post\<close> under a somewhat weak constraint. Intuitively we ask that, for
distinct representations (\<open>s\<^sub>0\<close> and \<open>s\<^sub>0'\<close>) of an abstract state (\<open>sf s\<^sub>0\<close> where \<open>sf s\<^sub>0' = sf s\<^sub>0\<close>),
if agent \<open>a\<close> can evolve \<open>s\<^sub>0\<close> to \<open>s\<^sub>1\<close> according to \<open>r\<close> (\<open>(a, s\<^sub>0, s\<^sub>1) \<in> r\<close>) then there is an agent
\<open>a'\<close> where \<open>af a' = af a\<close> that can evolve \<open>s\<^sub>0'\<close> to an \<open>s\<^sub>1'\<close> which represents the same abstract
state (\<open>sf s\<^sub>1' = sf s\<^sub>1\<close>).

All injective \<open>sf\<close> satisfy this condition.

\<close>

context
  fixes af :: "'a \<Rightarrow> 'b"
  fixes sf :: "'s \<Rightarrow> 't"
  fixes vf :: "'v \<Rightarrow> 'w"
begin

context
  fixes r :: "('a, 's) steps"
  assumes step_cong: "\<forall>a s\<^sub>0 s\<^sub>1 s\<^sub>0'. (a, s\<^sub>0, s\<^sub>1) \<in> r \<and> sf s\<^sub>1 \<noteq> sf s\<^sub>0 \<and> sf s\<^sub>0' = sf s\<^sub>0
                                \<longrightarrow> (\<exists>a' s\<^sub>1'. af a' = af a \<and> sf s\<^sub>1' = sf s\<^sub>1 \<and> (a', s\<^sub>0', s\<^sub>1') \<in> r)"
begin

private lemma map_relE[consumes 1]:
  fixes xs :: "('b \<times> 't) list"
  assumes "trace.steps' s xs \<subseteq> map_prod af (map_prod sf sf) ` r"
  obtains (Idle) "snd ` set xs \<subseteq> {s}"
        | (Step) s' xs'
          where "sf s' = s"
           and "trace.natural' s xs = map (map_prod af sf) xs'"
           and "trace.steps' s' xs' \<subseteq> r"
using assms
proof(atomize_elim, induct xs rule: prefix_induct)
  case (snoc xs x) show ?case
  proof(cases "snd x = trace.final' s xs")
    case True with snoc(2,3) show ?thesis
      by (fastforce simp: trace.steps'.append trace.natural'.append)
  next
    case False
    with snoc(2,3) consider
        (idle) "snd ` set xs \<subseteq> {s}"
      | (step) s' xs'
         where "sf s' = s"
           and "trace.natural' s xs = map (map_prod af sf) xs'"
           and "trace.steps' s' xs' \<subseteq> r"
      by (auto 0 0 simp: trace.steps'.append)
    then show ?thesis
    proof cases
      case idle with snoc(3) show ?thesis
        by (cases x)
           (clarsimp simp: trace.steps'.append trace.natural'.append Cons_eq_map_conv
                simp flip: trace.natural'.eq_Nil_conv ex_simps
                    split: if_splits;
            metis)
    next
      case (step s xs') with False snoc(3) step_cong show ?thesis
        by (cases x)
           (clarsimp simp: trace.steps'.append trace.natural'.append append_eq_map_conv Cons_eq_map_conv
                simp flip: ex_simps
                   intro!: exI[where x=s] exI[where x=xs'];
            metis trace.final'.map trace.final'.natural')
    qed
  qed
qed simp

lemma rel:
  shows "spec.map af sf vf (spec.rel r)
       = spec.rel (map_prod af (map_prod sf sf) ` r)
        \<sqinter> spec.pre (\<lambda>s. s \<in> range sf)
        \<sqinter> spec.post (\<lambda>v s. v \<in> range vf)" (is "?lhs = ?rhs")
proof(rule antisym[OF spec.singleton_le_extI spec.singleton_le_extI])
  show "\<lblot>\<sigma>\<rblot> \<le> ?rhs" if "\<lblot>\<sigma>\<rblot> \<le> ?lhs" for \<sigma>
  proof(intro le_infI)
    from that show "\<lblot>\<sigma>\<rblot> \<le> spec.rel (map_prod af (map_prod sf sf) ` r)"
      by (force simp: spec.singleton.le_conv spec.steps.singleton trace.steps'.map
                dest: spec.steps.mono)
    from that show "\<lblot>\<sigma>\<rblot> \<le> spec.pre (\<lambda>s. s \<in> range sf)"
      by (fastforce simp: spec.singleton.le_conv spec.singleton_le_conv trace.natural_def
                    elim: trace.less_eqE)
    from that show "\<lblot>\<sigma>\<rblot> \<le> spec.post (\<lambda>v s. v \<in> range vf)"
      by (cases \<sigma>) (clarsimp simp: spec.singleton.le_conv split: option.split)
  qed
  show "\<lblot>\<sigma>\<rblot> \<le> ?lhs" if "\<lblot>\<sigma>\<rblot> \<le> ?rhs" for \<sigma>
    using that[simplified, simplified spec.singleton.le_conv, THEN conjunct1]
          that[simplified, simplified spec.singleton.le_conv, THEN conjunct2]
  proof(induct rule: map_relE)
    case Idle then show ?case
      by (cases \<sigma>)
         (clarsimp simp: spec.singleton.le_conv;
          force simp: trace.natural.idle trace.natural.simps f_inv_into_f order_le_less
               split: option.split_asm
              intro!: exI[where x="trace.T s [] (map_option (inv vf) (trace.term \<sigma>))" for s])
  next
    case (Step s xs)
    from Step(1,3,4) Step(2)[symmetric] show ?case
      by (cases \<sigma>)
         (clarsimp simp: spec.singleton.le_conv f_inv_into_f[OF rangeI] trace.natural'.natural'
                         exI[where x="trace.T s xs (map_option (inv vf) (trace.term \<sigma>))"]
                  split: option.split_asm)
  qed
qed

lemma pre:
  fixes P :: "'t pred"
  shows "spec.map af sf vf (spec.pre (\<lambda>s. P (sf s)))
       = spec.pre (\<lambda>s. P s \<and> s \<in> range sf) \<sqinter> spec.post (\<lambda>v s. s \<in> range sf \<longrightarrow> v \<in> range vf)
          \<sqinter> spec.rel (range af \<times> range sf \<times> range sf)" (is "?lhs = ?rhs")
proof(rule antisym[OF _ spec.singleton_le_extI])
  show "?lhs \<le> ?rhs"
    by (simp add: spec.map_invmap.galois spec.invmap.pre spec.invmap.post spec.invmap.rel
                  map_prod_vimage_Times vimage_range spec.rel.UNIV)
  fix \<sigma>
  assume "\<lblot>\<sigma>\<rblot> \<le> ?rhs"
  then obtain s xs
    where "P (sf s)"
      and "trace.init \<sigma> = sf s"
      and "case trace.term \<sigma> of None \<Rightarrow> True
               | Some v \<Rightarrow> trace.final' (trace.init \<sigma>) (trace.rest \<sigma>) \<in> range sf \<longrightarrow> v \<in> range vf"
      and "map (map_prod af sf) xs = trace.natural' (sf s) (trace.rest \<sigma>)"
    by (clarsimp simp: spec.singleton.le_conv trace.steps'.map_range_conv)
  then show "\<lblot>\<sigma>\<rblot> \<le> ?lhs"
    by (cases \<sigma>)
       (fastforce intro: exI[where x="trace.T s xs (Some (inv vf (the (trace.term \<sigma>))))"]
                         range_eqI[where x="trace.final' s xs"]
                   dest: arg_cong[where f="trace.final' (sf s)"]
                   simp: spec.singleton.le_conv trace.final'.map f_inv_into_f trace.natural'.natural'
                         order.trans[OF spec.singleton.less_eq_None spec.singleton.simps(2)]
                  split: option.split_asm)
qed

lemma post:
  fixes Q :: "'w \<Rightarrow> 't pred"
  shows "spec.map af sf vf (spec.post (\<lambda>v s. Q (vf v) (sf s)))
       = spec.pre (\<lambda>s. s \<in> range sf) \<sqinter> spec.post (\<lambda>v s. s \<in> range sf \<longrightarrow> Q v s \<and> v \<in> range vf)
          \<sqinter> spec.rel (range af \<times> range sf \<times> range sf)" (is "?lhs = ?rhs")
proof(rule antisym[OF _ spec.singleton_le_extI])
  show "?lhs \<le> ?rhs"
    by (simp add: spec.map_invmap.galois spec.invmap.pre spec.invmap.post spec.invmap.rel
                  map_prod_vimage_Times vimage_range spec.rel.UNIV)
  fix \<sigma>
  assume "\<lblot>\<sigma>\<rblot> \<le> ?rhs"
  then obtain s xs
    where "trace.init \<sigma> = sf s"
      and "case trace.term \<sigma> of None \<Rightarrow> True | Some v \<Rightarrow> trace.final' (trace.init \<sigma>) (trace.rest \<sigma>) \<in> range sf \<longrightarrow> Q v (trace.final' (trace.init \<sigma>) (trace.rest \<sigma>)) \<and> v \<in> range vf"
      and "map (map_prod af sf) xs = trace.natural' (sf s) (trace.rest \<sigma>)"
    by (clarsimp simp: spec.singleton.le_conv trace.steps'.map_range_conv)
  then show "\<lblot>\<sigma>\<rblot> \<le> ?lhs"
    by (cases \<sigma>)
       (clarsimp simp: spec.singleton.le_conv trace.natural'.natural'
               intro!: exI[where x="trace.T s xs (map_option (inv vf) (trace.term \<sigma>))"]
                split: option.split_asm;
        clarsimp dest!: arg_cong[where f="trace.final' (sf s)"] simp: trace.final'.map;
        metis f_inv_into_f rangeI)
qed

end

end

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "invmap"\<close>

lemma idle:
  shows "spec.invmap af sf vf spec.idle
       = spec.term.none (spec.rel (UNIV \<times> map_prod sf sf -` Id) :: ('a, 's, unit) spec)" (is "?lhs = ?rhs")
proof(rule antisym[OF spec.singleton_le_extI spec.singleton_le_extI])
  have "sf s = sf s'"
    if "(a, s, s') \<in> trace.steps' s\<^sub>0 xs"
   and "(\<lambda>x. sf (snd x)) ` set xs \<subseteq> {sf s\<^sub>0}"
   for a :: 'a and s s' s\<^sub>0 :: 's and xs :: "('a \<times> 's) list"
    using that by (induct xs arbitrary: s\<^sub>0) (auto simp: trace.steps'.Cons_eq_if split: if_split_asm)
  then show "\<lblot>\<sigma>\<rblot> \<le> ?rhs" if "\<lblot>\<sigma>\<rblot> \<le> ?lhs" for \<sigma>
    using that by (clarsimp simp: spec.singleton.le_conv image_image)
  have "sf s' = sf s"
    if "trace.steps' s xs \<subseteq> UNIV \<times> map_prod sf sf -` Id"
   and "(a, s') \<in> set xs"
   for a s s' and xs :: "('a \<times> 's) list"
    using that
    by (induct xs arbitrary: s)
       (auto simp: Diff_subset_conv trace.steps'.Cons_eq_if split: if_split_asm)
  then show "\<lblot>\<sigma>\<rblot> \<le> ?lhs" if "\<lblot>\<sigma>\<rblot> \<le> ?rhs" for \<sigma>
    using that by (clarsimp simp: spec.singleton.le_conv)
qed

lemma inf_rel:
  shows "spec.rel (map_prod af (map_prod sf sf) -` (r \<union> UNIV \<times> Id)) \<sqinter> spec.invmap af sf vf P = spec.invmap af sf vf (spec.rel r \<sqinter> P)"
    and "spec.invmap af sf vf P \<sqinter> spec.rel (map_prod af (map_prod sf sf) -` (r \<union> UNIV \<times> Id)) = spec.invmap af sf vf (P \<sqinter> spec.rel r)"
by (simp_all add: inf_commute spec.invmap.rel spec.invmap.inf)

lemma action: \<comment>\<open> (* could restrict the stuttering expansion to \<open>range af\<close> or an arbitrary element of that \<close>
  fixes af :: "'a \<Rightarrow> 'b"
  fixes sf :: "'s \<Rightarrow> 't"
  fixes vf :: "'v \<Rightarrow> 'w"
  fixes F :: "('w \<times> 'b \<times> 't \<times> 't) set"
  defines "F' \<equiv> map_prod id (map_prod af (map_prod sf sf))
                  -` (F \<union> {(v, a', s, s) |v a a' s. (v, a, s, s) \<in> F \<and> \<not>surj af})"
  shows "spec.invmap af sf vf (spec.action F)
       =  spec.rel (UNIV \<times> map_prod sf sf -` Id)
          \<bind> (\<lambda>_::unit. spec.action F'
          \<bind> (\<lambda>v. spec.rel (UNIV \<times> map_prod sf sf -` Id)
          \<bind> (\<lambda>_::unit. \<Squnion>v'\<in>vf -` {v}. spec.return v')))" (is "?lhs = ?rhs")
proof(rule antisym[OF spec.singleton_le_extI], unfold spec.singleton.invmap_le_conv)
  have *: "sf x = sf y"
     if "(\<lambda>x. sf (snd x)) ` set xs \<subseteq> {sf s}"
    and "(a, x, y) \<in> trace.steps' s xs"
    for s a x y and v :: 'v and xs :: "('a \<times> 's) list"
    using that
    by (induct xs arbitrary: s; clarsimp simp: trace.steps'.Cons_eq_if split: if_split_asm; metis)
  show "\<lblot>\<sigma>\<rblot> \<le> ?rhs" if "\<lblot>trace.map af sf vf \<sigma>\<rblot> \<le> spec.action F" for \<sigma>
  proof(cases "\<natural> (trace.map af sf vf \<sigma>) = trace.T (trace.init (trace.map af sf vf \<sigma>)) [] None")
    case True then show ?thesis
      by (cases \<sigma>)
         (force simp: spec.singleton.le_conv trace.natural_def trace.natural'.eq_Nil_conv image_image
                dest: *
               intro: spec.bind.incompleteI)
  next
    case False with that show ?thesis
    proof(cases rule: spec.singleton.action_not_idle_le_splitE)
      case (return v a) then show ?thesis
        by (cases \<sigma>; clarsimp simp: image_image)
           ( rule spec.action.stutterI[where v=v and a="inv af a"]
                  spec.bind.continueI[where ys="[]", simplified]
           | ( fastforce simp: spec.singleton.le_conv F'_def trace.final'.map_idle surj_f_inv_f dest: * )
           )+
    next
      case (step v a ys zs) then show ?thesis
        by (cases \<sigma>; clarsimp simp: map_eq_append_conv image_image split: option.split_asm)
           (rule spec.bind.continueI
                 spec.bind.continueI[where xs="[x]" for x, simplified]
                 spec.bind.incompleteI[where g="\<langle>Sup X\<rangle>" for X]
                 spec.bind.continueI[where ys="[]", simplified]
           | ( rule spec.action.stepI; force simp: F'_def trace.final'.map_idle )
           | ( fastforce simp: spec.singleton.le_conv trace.final'.map_idle dest: * )
           )+
    qed
  qed
  have *: "map_prod af (map_prod sf sf) ` (UNIV \<times> map_prod sf sf -` Id) - UNIV \<times> Id = {}" by blast
  have "(v, a, s, s') \<in> F' \<Longrightarrow> \<lblot>sf s, [(af a, sf s')], None\<rblot> \<le> spec.action F" for v a s s'
    by (auto simp: F'_def spec.action.stepI intro: order.trans[OF spec.idle.minimal_le spec.idle.action_le])
  moreover
  have "\<lbrakk>(vf v, a, s, s') \<in> F'; sf s' = trace.init \<sigma>; \<lblot>\<sigma>\<rblot> \<le> spec.pre (\<lambda>s. s \<in> range sf); \<lblot>\<sigma>\<rblot> \<le> spec.return (vf v)\<rbrakk>
     \<Longrightarrow> \<lblot>sf s, (af a, trace.init \<sigma>) # trace.rest \<sigma>, trace.term \<sigma>\<rblot> \<le> spec.action F" for v a s s' \<sigma>
    by (auto simp: F'_def spec.action.stepI spec.action.stutterI spec.singleton.le_conv
                   spec.singleton.Cons[where as="trace.rest \<sigma>"]
            intro: order.trans[OF spec.idle.minimal_le spec.idle.action_le]
            split: option.split_asm)
  ultimately have "spec.action (map_prod id (map_prod af (map_prod sf sf)) ` F')
                     \<bind> (\<lambda>v. \<Squnion>x\<in>vf -` {v}. spec.pre (\<lambda>s. s \<in> range sf) \<sqinter> spec.return v)
                  \<le> spec.action F"
    by (subst spec.action_def)
       (auto simp: spec.bind.SupL spec.bind.supL spec.bind.singletonL spec.idle_le split_def spec.term.none.singleton)
  then show "?rhs \<le> ?lhs"
    apply (fold spec.map_invmap.galois)
    apply (strengthen ord_to_strengthen(1)[OF spec.map.bind_le])+
    apply (strengthen ord_to_strengthen[OF spec.map.rel_le])
    apply (strengthen ord_to_strengthen[OF spec.map.action_le])
    apply (subst (1 2) spec.rel.minus_Id[where A=UNIV, symmetric])
    apply (simp add: image_image * spec.map.return spec.rel.empty spec.bind.SupL spec.bind.returnL
                     spec.idle.action_le spec.idle.bind_le_conv spec.bind.SUPR_not_empty spec.bind.supR
                     spec.bind.return spec.map.Sup)
    done
qed

lemma return:
  fixes af :: "'a \<Rightarrow> 'b"
  fixes sf :: "'s \<Rightarrow> 't"
  fixes vf :: "'v \<Rightarrow> 'w"
  fixes F :: "('w \<times> 'b \<times> 't \<times> 't) set"
  shows "spec.invmap af sf vf (spec.return v)
       = spec.rel (UNIV \<times> map_prod sf sf -` Id) \<bind> (\<lambda>_::unit. \<Squnion>v'\<in>vf -` {v}. spec.return v')"
proof -
  have *: "spec.action ({()} \<times> UNIV \<times> map_prod sf sf -` Id) = spec.rel.act (UNIV \<times> map_prod sf sf -` Id)"
    by (auto simp: spec.rel.act_def intro: spec.action.cong)
  show ?thesis
    apply (subst spec.return_def)
    apply (simp add: spec.invmap.action map_prod_vimage_Times)
    apply (subst sup.absorb1, force)
    apply (simp add: spec.action.return_const[where V="{v}" and W="{()}"] spec.bind.bind spec.bind.return *)
    apply (simp add: spec.rel.wind_bind flip: spec.bind.bind spec.rel.unfoldL)
    done
qed

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.parent_path\<close>
(*<*)

end
(*>*)
