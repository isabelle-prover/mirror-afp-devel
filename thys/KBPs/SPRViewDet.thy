
(*
 * Knowledge-based programs.
 * (C)opyright 2011, Peter Gammie, peteg42 at gmail.com.
 * License: BSD
 *)

header {*Perfect Recall in Broadcast Environments with Deterministic Protocols*}

theory SPRViewDet
imports
  KBPsAlg List_local ODList
  Mapping AssocList Trie
begin


record ('a, 'es, 'as) BEState =
  es :: "'es"
  ps :: "('a \<times> 'as) odlist" -- {* Associates an agent with her private state. *}


instantiation BEState_ext :: (linorder, linorder, linorder, linorder) linorder
begin

definition less_eq_BEState_ext
  where "x \<le> y \<equiv> es x < es y \<or> (es x = es y \<and> (ps x < ps y \<or> (ps x = ps y \<and> more x \<le> more y)))"

definition less_BEState_ext
  where "x < y \<equiv> es x < es y \<or> (es x = es y \<and> (ps x < ps y \<or> (ps x = ps y \<and> more x < more y)))"

instance
  apply intro_classes
  apply (unfold less_eq_BEState_ext_def less_BEState_ext_def)
  apply auto
  done

end

instance BEState_ext :: ("{finite, linorder}", finite, "{finite, linorder}", finite) finite
proof
 let ?U = "UNIV :: ('a, 'b, 'c, 'd) BEState_ext set"
 { fix x :: "('a, 'b, 'c, 'd) BEState_scheme"
   have "\<exists>a b c. x = BEState_ext a b c"
     by (cases x) simp
 } then have U:
   "?U = (\<lambda>((a, b), c). BEState_ext a b c) ` ((UNIV \<times> UNIV) \<times> UNIV)"
   by (auto simp add: Set.image_def)
 show "finite ?U" by (simp add: U)
qed


locale DetBroadcastEnvironment =
  Environment jkbp envInit envAction envTrans envVal envObs
    for jkbp :: "'a \<Rightarrow> ('a :: {finite, linorder}, 'p, 'aAct) KBP"
    and envInit :: "('a, 'es :: {finite, linorder}, 'as :: {finite, linorder}) BEState list"
    and envAction :: "('a, 'es, 'as) BEState \<Rightarrow> 'eAct list"
    and envTrans :: "'eAct \<Rightarrow> ('a \<Rightarrow> 'aAct)
                     \<Rightarrow> ('a, 'es, 'as) BEState \<Rightarrow> ('a, 'es, 'as) BEState"
    and envVal :: "('a, 'es, 'as) BEState \<Rightarrow> 'p \<Rightarrow> bool"
    and envObs :: "'a \<Rightarrow> ('a, 'es, 'as) BEState \<Rightarrow> ('cobs \<times> 'as option)"

+ fixes agents :: "'a odlist"
    and envObsC :: "'es \<Rightarrow> 'cobs"
  defines "envObs a s \<equiv> (envObsC (es s), ODList.lookup (ps s) a)"
  assumes agents: "ODList.toSet agents = UNIV"
      and envTrans: "\<forall>s s' a eact eact' aact aact'.
              ODList.lookup (ps s) a = ODList.lookup (ps s') a \<and> aact a = aact' a
               \<longrightarrow> ODList.lookup (ps (envTrans eact aact s)) a
                 = ODList.lookup (ps (envTrans eact' aact' s')) a"
      and jkbpDet: "\<forall>a. \<forall>t \<in> jkbpC. length (jAction mkMC t a) \<le> 1"

context DetBroadcastEnvironment begin

lemma envObs_def_raw:
  "envObs a = (\<lambda>s. (envObsC (es s), ODList.lookup (ps s) a))"
  apply (rule ext)+
  apply (simp add: envObs_def)
  done

definition tObsC :: "('a, 'es, 'as) BEState Trace \<Rightarrow> 'cobs Trace" where
  "tObsC \<equiv> tMap (envObsC \<circ> es)"


definition tObsC_abs :: "('a, 'es, 'as) BEState Trace \<Rightarrow> ('a, 'es, 'as) BEState Relation" where
  "tObsC_abs t \<equiv> {(tFirst t', tLast t') |t'. t' \<in> jkbpC \<and> tObsC t' = tObsC t}"


lemma spr_jview_tObsC:
  assumes "spr_jview a t = spr_jview a t'"
  shows "tObsC t = tObsC t'"
  unfolding tObsC_def
  using spr_sync[OF assms] assms
  apply (induct rule: trace_induct2)
  apply (auto simp: Let_def envObs_def_raw)
  done

lemma tObsC_tLength:
  "tObsC t = tObsC t' \<Longrightarrow> tLength t = tLength t'"
  unfolding tObsC_def by (rule tMap_eq_imp_tLength_eq)

lemma tObsC_tStep_eq_inv:
  "tObsC t' = tObsC (t \<leadsto> s) \<Longrightarrow> \<exists>t'' s'. t' = t'' \<leadsto> s'"
  unfolding tObsC_def by auto

lemma tObsC_prefix_closed[dest]:
  "tObsC (t \<leadsto> s) = tObsC (t' \<leadsto> s') \<Longrightarrow> tObsC t = tObsC t'"
  unfolding tObsC_def by simp

lemma tObsC_tLast[iff]:
  "tLast (tObsC t) = envObsC (es (tLast t))"
  unfolding tObsC_def by simp

lemma tObsC_initial[iff]:
  "tFirst (tObsC t) = envObsC (es (tFirst t))"
  "tObsC (tInit s) = tInit (envObsC (es s))"
  "tObsC t = tInit cobs \<longleftrightarrow> (\<exists>s. t = tInit s \<and> envObsC (es s) = cobs)"
  unfolding tObsC_def by simp_all

lemma spr_tObsC_trc_aux:
  assumes "(t, t') \<in> (\<Union>a. relations mkMC a)\<^sup>*"
  shows "tObsC t = tObsC t'"
  using assms
  apply (induct)
   apply simp
  apply clarsimp
  apply (rule_tac a=x in spr_jview_tObsC)
  apply simp
  done

lemma tObsC_abs_jview_eq[dest]:
  "spr_jview a t' = spr_jview a t
    \<Longrightarrow> tObsC_abs t = tObsC_abs t'"
  unfolding tObsC_abs_def by (fastforce dest: spr_jview_tObsC)

lemma tObsC_abs_tObsC_eq[dest]:
  "tObsC t' = tObsC t
    \<Longrightarrow> tObsC_abs t = tObsC_abs t'"
  unfolding tObsC_abs_def by (fastforce dest: spr_jview_tObsC)

lemma spr_jview_tObsCI:
  assumes tt': "tObsC t = tObsC t'"
      and first: "envObs a (tFirst t) = envObs a (tFirst t')"
      and "tMap (\<lambda>s. ODList.lookup (ps s) a) t = tMap (\<lambda>s. ODList.lookup (ps s) a) t'"
  shows "spr_jview a t = spr_jview a t'"
  using tObsC_tLength[OF tt'] assms
  by (induct rule: trace_induct2, auto iff: tObsC_def envObs_def_raw spr_jview_def)

lemma tObsC_absI[intro]:
  "\<lbrakk> t' \<in> jkbpC; tObsC t' = tObsC t; u = tFirst t'; v = tLast t' \<rbrakk>
    \<Longrightarrow> (u, v) \<in> tObsC_abs t"
  unfolding tObsC_abs_def by blast

lemma tObsC_abs_conv:
  "(u, v) \<in> tObsC_abs t
    \<longleftrightarrow> (\<exists>t'. t' \<in> jkbpC \<and> tObsC t' = tObsC t \<and> u = tFirst t' \<and> v = tLast t')"
  unfolding tObsC_abs_def by blast

lemma tObsC_abs_tLast[simp]:
  "(u, v) \<in> tObsC_abs t \<Longrightarrow> envObsC (es v) = envObsC (es (tLast t))"
  unfolding tObsC_abs_def tObsC_def
  by (auto iff: o_def elim: tMap_tLast_inv)

lemma tObsC_abs_tInit[iff]:
  "tObsC_abs (tInit s)
 = { (s', s') |s'. s' \<in> set envInit \<and> envObsC (es s') = envObsC (es s) }"
  unfolding tObsC_abs_def
  apply auto
  apply (rule_tac x="tInit s'" in exI)
  apply simp
  done

end (* context *)

text{*

We can predict an agent's final private state on @{term "t' \<in> jkbpC"}
where @{term "tObsC t' = tObsC t"} from the agent's private state in
@{term "tFirst t'"} and @{term "tObsC_abs t"} due to the determinacy
requirement @{term "jkbpDet"} and the constraint @{term
"envTrans"}. Thus the agent's state of knowledge on @{term "t"} is
captured by the following simulation:

*}

record ('a, 'es, 'as) SPRstate =
  sprFst :: "('a, 'es, 'as) BEState"
  sprLst :: "('a, 'es, 'as) BEState"
  sprCRel :: "(('a, 'es, 'as) BEState \<times> ('a, 'es, 'as) BEState) set"

definition(in DetBroadcastEnvironment) spr_sim :: "('a, 'es, 'as) BEState Trace \<Rightarrow> ('a, 'es, 'as) SPRstate" where
  "spr_sim t \<equiv> \<lparr> sprFst = tFirst t, sprLst = tLast t, sprCRel = tObsC_abs t \<rparr>"


instance SPRstate_ext :: ("{finite, linorder}", finite, "{finite, linorder}", finite) finite
proof
 let ?U = "UNIV :: ('a, 'b, 'c, 'd) SPRstate_ext set"
 { fix x :: "('a, 'b, 'c, 'd) SPRstate_scheme"
   have "\<exists>a b c d. x = SPRstate_ext a b c d"
     by (cases x) simp
 } then have U:
   "?U = (\<lambda>(a, (b, (c, d))). SPRstate_ext a b c d) ` (UNIV \<times> (UNIV \<times> (UNIV \<times> UNIV)))"
   by (auto simp add: Set.image_def)
 show "finite ?U" by (simp add: U)
qed

context DetBroadcastEnvironment begin

lemma spr_sim_tFirst_tLast:
  "\<lbrakk> spr_sim t = s; t \<in> jkbpC \<rbrakk> \<Longrightarrow> (sprFst s, sprLst s) \<in> sprCRel s"
  unfolding spr_sim_def by auto

lemma spr_sim_tObsC:
  shows "tObsC_abs t = sprCRel (spr_sim t)"
  unfolding tObsC_abs_def spr_sim_def by simp

definition
  spr_sim_rels :: "'a \<Rightarrow> ('a, 'es, 'as) SPRstate Relation"
where
  "spr_sim_rels \<equiv> \<lambda>a. { (s, s') |s s'.
                         envObs a (sprFst s) = envObs a (sprFst s')
                       \<and> envObs a (sprLst s) = envObs a (sprLst s')
                       \<and> sprCRel s = sprCRel s' }"

definition
  spr_sim_val :: "('a, 'es, 'as) SPRstate \<Rightarrow> 'p \<Rightarrow> bool"
where
  "spr_sim_val \<equiv> envVal \<circ> sprLst"

lemma spr_sim_val_eq[iff]:
  "spr_sim_val (spr_sim t) = envVal (tLast t)"
  unfolding spr_sim_def spr_sim_val_def by simp

abbreviation
  "jkbpCSn n \<equiv> spr_sim ` jkbpCn n"

abbreviation
  "jkbpCS \<equiv> spr_sim ` jkbpC"

abbreviation
  "mkMCSn n \<equiv> mkKripke (jkbpCSn n) spr_sim_rels spr_sim_val"

abbreviation
  "mkMCS \<equiv> mkKripke jkbpCS spr_sim_rels spr_sim_val"

(* Show this setup has the simulation properties. *)

lemma spr_sim_range:
  "sim_range mkMC mkMCS spr_sim"
  by (rule sim_rangeI) (simp_all add: spr_sim_def)

lemma spr_sim_val:
  "sim_val mkMC mkMCS spr_sim"
  by (rule sim_valI) simp

lemma spr_sim_f:
  "sim_f mkMC mkMCS spr_sim"
  unfolding spr_sim_rels_def spr_sim_def_raw mkKripke_def mkM_def
  by (rule sim_fI, auto)

(*

Reverse simulation is the tricky party.

This is the critical lemma that shows that the final private state of
an agent on a trace is a function of its initial observation and the
common observation on the trace.

*)

lemma envDetJKBP':
  assumes tCn: "t \<in> jkbpCn n"
      and aact: "act \<in> set (jAction (mkMCn n) t a)"
  shows "jAction (mkMCn n) t a = [act]"
  using jkbpDet[rule_format, where t=t and a=a] assms
  apply -
  apply (cases "jAction mkMC t a")
   apply (auto iff: jkbpC_jkbpCn_jAction_eq[OF tCn] dest: jkbpCn_jkbpC_inc)
  done

lemma spr_jview_det_ps:
  assumes tt': "{t, t'} \<subseteq> jkbpC"
      and obsCtt': "tObsC t = tObsC t'"
      and first: "envObs a (tFirst t) = envObs a (tFirst t')"
  shows "tMap (\<lambda>s. ODList.lookup (ps s) a) t = tMap (\<lambda>s. ODList.lookup (ps s) a) t'"
using tObsC_tLength[OF obsCtt'] first tt' obsCtt'
proof(induct rule: trace_induct2)
  case (tInit s s') thus ?case
    unfolding envObs_def_raw by simp
next
  case (tStep s s' t t')

  from tStep
  have ts: "t \<leadsto> s \<in> jkbpCn (tLength (t \<leadsto> s))"
   and t's': "t' \<leadsto> s' \<in> jkbpCn (tLength (t' \<leadsto> s'))"
    by blast+

  from tStep have tt': "spr_jview a t = spr_jview a t'"
    by - (rule spr_jview_tObsCI, auto)

  with tStep have FIXME:
     "jAction (mkMCn (tLength t)) t a
    = jAction (mkMCn (tLength t')) t' a"
    apply -
    apply simp
    apply (rule S5n_jAction_eq)
      apply blast
     unfolding mkM_def
     apply simp
     apply blast
     done

   from tt' have tt'Last: "ODList.lookup (ps (tLast t)) a
                         = ODList.lookup (ps (tLast t')) a"
     by (auto iff: envObs_def_raw)

   from ts obtain eact aact
     where aact: "\<forall>a. aact a \<in> set (jAction (mkMCn (tLength t)) t a)"
       and s: "s = envTrans eact aact (tLast t)"
     by (auto iff: Let_def)

   from t's' obtain eact' aact'
     where aact': "\<forall>a. aact' a \<in> set (jAction (mkMCn (tLength t')) t' a)"
       and s': "s' = envTrans eact' aact' (tLast t')"
     by (auto iff: Let_def)

   from tStep have tCn: "t \<in> jkbpCn (tLength t)" by auto
   from aact
   obtain act
     where act: "jAction (mkMCn (tLength t)) t a = [act]"
     using envDetJKBP'[OF tCn, where a=a and act="aact a"]
     apply auto
     done
   hence "jAction (mkMCn (tLength t')) t' a = [act]"
     by (simp only: FIXME)
   with act aact aact'
   have "aact a = aact' a"
     apply -
     apply (erule allE[where x=a])
     apply (erule allE[where x=a])
     apply simp
     done
   with agents tt'Last s s'
   have "ODList.lookup (ps s) a = ODList.lookup (ps s') a"
     by (simp add: envTrans)
   moreover
   from tStep have "tMap (\<lambda>s. ODList.lookup (ps s) a) t = tMap (\<lambda>s. ODList.lookup (ps s) a) t'"
     by auto
   moreover
   from tStep have "envObsC (es s) = envObsC (es s')"
     unfolding tObsC_def by simp
   ultimately show ?case by simp
qed

lemma spr_sim_r:
  "sim_r mkMC mkMCS spr_sim"
proof(rule sim_rI)
  fix a p q'
  assume pT: "p \<in> worlds mkMC"
     and fpq': "(spr_sim p, q') \<in> relations mkMCS a"
  from fpq' obtain uq fq vq
    where q': "q' = \<lparr> sprFst = uq, sprLst = vq, sprCRel = tObsC_abs p \<rparr>"
      and uq: "envObs a (tFirst p) = envObs a uq"
      and vq: "envObs a (tLast p) = envObs a vq"
    unfolding mkKripke_def spr_sim_def_raw spr_sim_rels_def
    by fastforce

  from fpq' have "q' \<in> worlds mkMCS" by simp
  with q' have "(uq, vq) \<in> tObsC_abs p"
    using spr_sim_tFirst_tLast[where s=q']
    apply auto
    done
  then obtain t
    where tT: "t \<in> jkbpC"
      and tp: "tObsC t = tObsC p"
      and tuq: "tFirst t = uq"
      and tvq: "tLast t = vq"
    by (auto iff: tObsC_abs_conv)

  from pT tT tp tuq uq
  have "tMap (\<lambda>s. ODList.lookup (ps s) a) p = tMap (\<lambda>s. ODList.lookup (ps s) a) t"
    by (auto intro: spr_jview_det_ps)
  with tp tuq uq
  have "spr_jview a p = spr_jview a t"
    by (auto intro: spr_jview_tObsCI)

  with pT tT have pt: "(p, t) \<in> relations mkMC a"
    unfolding mkM_def
    apply simp
    done
  from q' uq vq tp tuq tvq have ftq': "spr_sim t = q'"
    unfolding spr_sim_def_raw by blast
  from pt ftq'
  show "\<exists>q. (p, q) \<in> relations mkMC a \<and> spr_sim q = q'"
    by blast
qed

lemma spr_sim[intro, simp]:
  "sim mkMC mkMCS spr_sim"
  using spr_sim_range spr_sim_val spr_sim_f spr_sim_r
  unfolding sim_def
  by blast


end

type_synonym
  ('a, 'es, 'as) SPRstate_ec_rep
    = "('a, 'es, 'as) BEState ODRelation"
type_synonym
  ('a, 'es, 'as) SPRstate_rep
    = "('a, 'es, 'as) SPRstate_ec_rep
     \<times> ('a, 'es, 'as) SPRstate_ec_rep"

definition
  spr_simInit :: "('a, 'es, 'as) BEState list \<Rightarrow> ('es \<Rightarrow> 'cobs) \<Rightarrow> ('a \<Rightarrow> ('a, 'es, 'as) BEState \<Rightarrow> 'cobs \<times> 'obs)
                     \<Rightarrow> 'a \<Rightarrow> ('cobs \<times> 'obs) \<Rightarrow> ('a :: linorder, 'es :: linorder, 'as :: linorder) SPRstate_rep"
where
 [code]: "spr_simInit envInit envObsC envObs \<equiv> \<lambda>a iobs.
             (ODList.fromList [ (s, s). s \<leftarrow> envInit, envObsC (es s) = fst iobs ],
              ODList.fromList [ (s, s). s \<leftarrow> envInit, envObs a s = iobs ])"

(* It takes some digging to get to a representative state. *)

definition
  spr_simObs :: "('es \<Rightarrow> 'cobs)
               \<Rightarrow> 'a \<Rightarrow> ('a :: linorder, 'es :: linorder, 'as :: linorder) SPRstate_rep \<Rightarrow> 'cobs \<times> 'as option"
where
  [code]: "spr_simObs envObsC \<equiv> \<lambda>a. (\<lambda>s. (envObsC (es s), ODList.lookup (ps s) a)) \<circ> snd \<circ> ODList.hd \<circ> snd"

function
  eval_rec :: "(('a, 'es, 'as) BEState \<Rightarrow> 'p \<Rightarrow> bool)
         \<Rightarrow> ('a :: linorder, 'es :: linorder, 'as :: linorder) SPRstate_ec_rep
         \<Rightarrow> ('a \<Rightarrow> ('a, 'es, 'as) BEState \<times> ('a, 'es, 'as) BEState \<Rightarrow> ('a, 'es, 'as) SPRstate_ec_rep)
         \<Rightarrow> ('a, 'p) Kform
         \<Rightarrow> ('a, 'es, 'as) SPRstate_ec_rep"
where
  "eval_rec val X R (Kprop p)  = ODList.filter (\<lambda>s. val (snd s) p) X"
| "eval_rec val X R (Knot \<phi>)   = ODList.difference X (eval_rec val X R \<phi>)"
| "eval_rec val X R (Kand \<phi> \<psi>) = ODList.intersection (eval_rec val X R \<phi>) (eval_rec val X R \<psi>)"
| "eval_rec val X R (\<^bold>K\<^sub>a \<phi>)     = ODList.filter (\<lambda>s. eval_rec val (R a s) R (Knot \<phi>) = ODList.empty) X"
  by pat_completeness auto
termination eval_rec by size_change

declare eval_rec.simps [code]

fun
  evalS
where
  "evalS val X R (Kprop p)  = undefined"
| "evalS val X R (Knot \<phi>)   = (\<not>evalS val X R \<phi>)"
| "evalS val X R (Kand \<phi> \<psi>) = (evalS val X R \<phi> \<and> evalS val X R \<psi>)"
| "evalS val X R (\<^bold>K\<^sub>a \<phi>)     = (eval_rec val X R (Knot \<phi>) = ODList.empty)"

(* Partition the common observation EC for each agent. *)

definition
  coEC_rels :: "('a \<Rightarrow> ('a, 'es, 'as) BEState \<Rightarrow> 'cobs \<times> 'as option)
              \<Rightarrow> 'a \<Rightarrow> ('a, 'es, 'as) BEState \<times> ('a, 'es, 'as) BEState
                    \<Rightarrow> ('a, 'es, 'as) BEState \<times> ('a, 'es, 'as) BEState \<Rightarrow> bool"
where
  "coEC_rels envObs \<equiv> \<lambda>a (u, v) (u', v').
     envObs a u = envObs a u' \<and> envObs a v = envObs a v'"

definition
  spr_coEC_relation_image :: "('a \<Rightarrow> ('a :: linorder, 'es :: linorder, 'as :: linorder) BEState \<Rightarrow> 'cobs \<times> 'as option)
                      \<Rightarrow> ('a, 'es, 'as) BEState ODRelation
                      \<Rightarrow> 'a \<Rightarrow> ('a, 'es, 'as) BEState \<times> ('a, 'es, 'as) BEState
                           \<Rightarrow> ('a, 'es, 'as) SPRstate_ec_rep"
where
  [code]: "spr_coEC_relation_image envObs coEC \<equiv> \<lambda>a s.
             fromList [ s' . s' \<leftarrow> toList coEC, coEC_rels envObs a s s' ]"

definition
  "eval envVal envObs \<equiv> \<lambda>(Y, X) \<phi>.
     evalS envVal X (spr_coEC_relation_image envObs Y) \<phi>"

definition
  spr_simAction :: "('a \<Rightarrow> ('a, 'p, 'aAct) KBP) \<Rightarrow> (('a, 'es, 'as) BEState \<Rightarrow> 'p \<Rightarrow> bool)
                     \<Rightarrow> ('a \<Rightarrow> ('a, 'es, 'as) BEState \<Rightarrow> 'cobs \<times> 'as option)
                     \<Rightarrow> ('a :: linorder, 'es :: linorder, 'as :: linorder) SPRstate_rep \<Rightarrow> 'a \<Rightarrow> 'aAct list"
where
  [code]: "spr_simAction jkbp envVal envObs \<equiv> \<lambda>ec a.
             [ action gc. gc \<leftarrow> jkbp a, eval envVal envObs ec (guard gc) ]"

(* Concretely enumerate all the agent action functions. Can't be too
abstract here as we want extensionality. *)

definition
  mkAact
where
  "mkAact xs \<equiv> foldr (\<lambda>(a, acts) M. [ m(a := act) . m \<leftarrow> M, act \<leftarrow> acts ]) xs [(\<lambda>_. undefined)]"

lemma mkAact_FIXME:
  "\<lbrakk> M \<in> set (mkAact xs); x \<in> fst ` set xs \<rbrakk>
     \<Longrightarrow> M x \<in> { y |y ys. (x, ys) \<in> set xs \<and> y \<in> set ys}"
  unfolding mkAact_def
  apply (induct xs arbitrary: M)
   apply simp_all
  apply (case_tac a)
  apply clarsimp
  apply (erule disjE)
  apply auto
  done

lemma FIXME_distinct_map_fst:
  "\<lbrakk> x \<notin> fst ` set xs; distinct (map fst xs) \<rbrakk> \<Longrightarrow> (x, y) \<notin> set xs"
  by (induct xs) auto

lemma mkAact_FIXME_rev:
  "\<lbrakk> \<And>x. M x \<in> (if x \<in> fst ` set xs then { y |y ys. (x, ys) \<in> set xs \<and> y \<in> set ys} else {undefined}); distinct (map fst xs) \<rbrakk>
      \<Longrightarrow> M \<in> set (mkAact xs)"
proof(induct xs arbitrary: M)
  case Nil thus ?case
    unfolding mkAact_def by simp
next
  case (Cons x xs)
  let ?M' = "M(fst x := undefined)"
  have M': "?M' \<in> set (mkAact xs)"
    apply (rule Cons.hyps)
     prefer 2
     using Cons(3)
     apply simp
    apply (case_tac "xa = fst x")
     using Cons(3)
     apply simp
    apply (case_tac "xa \<in> fst ` set xs")
     apply (cut_tac x=xa in Cons(2))
     apply (cases x)
     apply auto[1]
    apply (cut_tac x=xa in Cons(2))
    apply simp
    done
  then show ?case
    unfolding mkAact_def
    apply (cases x)
    apply simp
    apply (rule bexI[where x="?M'"])
     apply simp_all
    apply (rule_tac x="M a" in image_eqI)
     apply simp
    apply (cut_tac x=a in Cons(2))
    using Cons(3)
    apply clarsimp
    apply (erule disjE)
     apply simp
    apply (auto dest: FIXME_distinct_map_fst)
    done
qed

definition
  mkAacts :: "('a \<Rightarrow> 'b list) \<Rightarrow> 'a list \<Rightarrow> ('a \<Rightarrow> 'b) list"
where
  "mkAacts f \<equiv> mkAact \<circ> map (\<lambda>x. (x, f x))"

lemma FIXME_dumb:
  "\<lbrakk> set xs = UNIV \<rbrakk> \<Longrightarrow> x \<in> fst ` set (map (\<lambda>x. (x, f x)) xs)"
  apply (simp only: set_map[symmetric] map_map)
  apply simp
  done

lemma mkAacts_FIXME:
  assumes xs: "set xs = UNIV"
      and d: "distinct xs"
  shows "g \<in> set (mkAacts f xs) \<longleftrightarrow> (\<forall>x. g x \<in> set (f x))"
  unfolding mkAacts_def
  apply simp
  apply rule
   apply clarsimp
   apply (cut_tac x=x in mkAact_FIXME[where M=g, OF _ FIXME_dumb[OF xs]])
    apply simp
   apply clarsimp
  apply (rule mkAact_FIXME_rev)
   using FIXME_dumb[OF xs]
   apply auto[1]
   apply (rule_tac x="f xa" in exI)
   apply simp
   apply (rule_tac x=xa in image_eqI)
    apply simp
   apply simp
  using d
  apply (simp add: distinct_map)
  apply (auto intro: inj_onI)
  done

definition
  "spr_jAction jkbp envVal envObs coEC s \<equiv> \<lambda>a.
     spr_simAction jkbp envVal envObs (coEC, spr_coEC_relation_image envObs coEC a s) a"

definition
  spr_trans :: "'a odlist
              \<Rightarrow> ('a \<Rightarrow> ('a, 'p, 'aAct) KBP)
              \<Rightarrow> (('a, 'es, 'as) BEState \<Rightarrow> 'eAct list)
              \<Rightarrow> ('eAct \<Rightarrow> ('a \<Rightarrow> 'aAct) \<Rightarrow> ('a, 'es, 'as) BEState \<Rightarrow> ('a, 'es, 'as) BEState)
              \<Rightarrow> (('a, 'es, 'as) BEState \<Rightarrow> 'p \<Rightarrow> bool)
              \<Rightarrow> ('a \<Rightarrow> ('a, 'es, 'as) BEState \<Rightarrow> 'cobs \<times> 'as option)
                \<Rightarrow> ('a, 'es, 'as) SPRstate_ec_rep
                \<Rightarrow> ('a, 'es, 'as) SPRstate_ec_rep
                  \<Rightarrow> (('a :: linorder, 'es :: linorder, 'as :: linorder) BEState \<times> ('a, 'es, 'as) BEState) list"
where
  [code]: "spr_trans agents jkbp envAction envTrans envVal envObs \<equiv> \<lambda>coEC ec.
             [ (initialS, succS) .
                 (initialS, finalS) \<leftarrow> toList ec,
                 eact \<leftarrow> envAction finalS,
                 succS \<leftarrow> [ envTrans eact aact finalS .
                             aact \<leftarrow> mkAacts (spr_jAction jkbp envVal envObs coEC (initialS, finalS)) (toList agents) ] ]"

definition
  spr_simObsC :: "('es \<Rightarrow> 'cobs)
               \<Rightarrow> (('a :: linorder, 'es :: linorder, 'as :: linorder) BEState \<times> ('a, 'es, 'as) BEState) odlist
               \<Rightarrow> 'cobs"
where
  [code]: "spr_simObsC envObsC \<equiv> envObsC \<circ> es \<circ> snd \<circ> ODList.hd"

abbreviation
  envObs_rel :: "(('a, 'es, 'as) BEState \<Rightarrow> 'cobs \<times> 'as option)
               \<Rightarrow> (('a, 'es, 'as) BEState \<times> ('a, 'es, 'as) BEState) Relation"
where
  "envObs_rel envObs \<equiv> {(s, s'). envObs (snd s') = envObs (snd s)}"

lemma envObs_rel_equiv:
  "equiv UNIV (envObs_rel envObs)"
  by (rule equivI) (auto intro: refl_onI symI transI)

definition
  spr_simTrans :: "'a odlist
              \<Rightarrow> ('a \<Rightarrow> ('a, 'p, 'aAct) KBP)
              \<Rightarrow> (('a, 'es, 'as) BEState \<Rightarrow> 'eAct list)
              \<Rightarrow> ('eAct \<Rightarrow> ('a \<Rightarrow> 'aAct) \<Rightarrow> ('a, 'es, 'as) BEState \<Rightarrow> ('a, 'es, 'as) BEState)
              \<Rightarrow> (('a, 'es, 'as) BEState \<Rightarrow> 'p \<Rightarrow> bool)
              \<Rightarrow> ('es \<Rightarrow> 'cobs)
              \<Rightarrow> ('a \<Rightarrow> ('a, 'es, 'as) BEState \<Rightarrow> 'cobs \<times> 'as option)
                \<Rightarrow> 'a
                \<Rightarrow> ('a, 'es, 'as) SPRstate_rep
                  \<Rightarrow> ('a :: linorder, 'es :: linorder, 'as :: linorder) SPRstate_rep list"
where
  [code]: "spr_simTrans agents jkbp envAction envTrans envVal envObsC envObs \<equiv> \<lambda>a ec.
     let aSuccs = spr_trans agents jkbp envAction envTrans envVal envObs (fst ec) (snd ec);
         coEC' = fromList (spr_trans agents jkbp envAction envTrans envVal envObs (fst ec) (fst ec))
      in [ (ODList.filter (\<lambda>s. envObsC (es (snd s)) = spr_simObsC envObsC aEC') coEC', aEC')
             . aEC' \<leftarrow> map fromList (partition (envObs_rel (envObs a)) aSuccs) ]"

context DetBroadcastEnvironment
begin

(* Define a bunch of locale-local abbreviations. Note these aren't
polymorphic - these type variables and sorts and fixed by the
locale. The type (sort) errors can be confusing. *)

abbreviation
  spr_simInit :: "'a \<Rightarrow> ('cobs \<times> 'as option) \<Rightarrow> ('a, 'es, 'as) SPRstate_rep"
where
  "spr_simInit \<equiv> SPRViewDet.spr_simInit envInit envObsC envObs"

abbreviation
  spr_simObs :: "'a \<Rightarrow> ('a, 'es, 'as) SPRstate_rep \<Rightarrow> 'cobs \<times> 'as option"
where
  "spr_simObs \<equiv> SPRViewDet.spr_simObs envObsC"

abbreviation
  spr_simAction :: "('a, 'es, 'as) SPRstate_rep \<Rightarrow> 'a \<Rightarrow> 'aAct list"
where
  "spr_simAction \<equiv> SPRViewDet.spr_simAction jkbp envVal envObs"

abbreviation
  spr_trans :: "('a, 'es, 'as) SPRstate_ec_rep
              \<Rightarrow> ('a, 'es, 'as) SPRstate_ec_rep
              \<Rightarrow> (('a, 'es, 'as) BEState \<times> ('a, 'es, 'as) BEState) list"
where
  "spr_trans \<equiv> SPRViewDet.spr_trans agents jkbp envAction envTrans envVal envObs"

abbreviation
  spr_simTrans :: "'a \<Rightarrow> ('a, 'es, 'as) SPRstate_rep \<Rightarrow> ('a, 'es, 'as) SPRstate_rep list"
where
  "spr_simTrans \<equiv> SPRViewDet.spr_simTrans agents jkbp envAction envTrans envVal envObsC envObs"

(* Abstract from representations to sets of simulated equivalence
classes. *)

definition
  spr_simAbs :: "('a, 'es, 'as) SPRstate_rep \<Rightarrow> ('a, 'es, 'as) SPRstate set"
where
  "spr_simAbs \<equiv> \<lambda>(coEC, aEC). { \<lparr> sprFst = s, sprLst = s', sprCRel = toSet coEC \<rparr> |s s'. (s, s') \<in> toSet aEC }"

definition
  agent_equiv :: "'a \<Rightarrow> ('a, 'es, 'as) BEState Trace \<Rightarrow> ('a, 'es, 'as) BEState Relation"
where
  "agent_equiv a t \<equiv>
     { (tFirst t', tLast t') |t'. t' \<in> jkbpC \<and> spr_jview a t' = spr_jview a t }"

lemma agent_equivI[intro]:
  "\<lbrakk> spr_jview a t' = spr_jview a t; t' \<in> jkbpC; t \<in> jkbpC \<rbrakk>
      \<Longrightarrow> (tFirst t', tLast t') \<in> agent_equiv a t"
  unfolding agent_equiv_def by auto

lemma simAbs_ec_refl:
  assumes tC: "t \<in> jkbpC"
      and ec: "spr_simAbs ec = spr_sim ` equiv_class a (spr_jview a t)"
  shows "spr_sim t \<in> spr_simAbs ec"
  using assms by simp

lemma simAbs_ec_tObsC_abs[simp]:
  assumes tC: "t \<in> jkbpC"
      and ec: "spr_simAbs ec = spr_sim ` equiv_class a (spr_jview a t)"
  shows "toSet (fst ec) = tObsC_abs t"
  using tC simAbs_ec_refl[OF tC ec]
  unfolding spr_sim_def_raw spr_simAbs_def by auto

lemma simAbs_ec_agent_equiv[simp]:
  assumes tC: "t \<in> jkbpC"
      and ec: "spr_simAbs ec = spr_sim ` equiv_class a (spr_jview a t)"
  shows "toSet (snd ec) = agent_equiv a t" (is "?lhs = ?rhs")
  using tC ec
  unfolding spr_sim_def_raw spr_simAbs_def agent_equiv_def
  apply (cases ec)
  apply auto
  apply (subgoal_tac "\<lparr>sprFst = aaa, sprLst = ba, sprCRel = toSet aa\<rparr> \<in> {\<lparr>sprFst = s, sprLst = s', sprCRel = toSet aa\<rparr> |s s'. (s, s') \<in> toSet b}")
  apply auto
  done

(* simInit *)

lemma spr_simInit:
  "\<forall>a iobs. iobs \<in> envObs a ` set envInit
    \<longrightarrow> spr_simAbs (spr_simInit a iobs)
      = spr_sim ` equiv_class a (tInit iobs)"
  unfolding spr_simInit_def spr_simAbs_def spr_sim_def_raw
  apply (clarsimp simp add: Let_def split: split_split)
  apply rule
   apply clarsimp
   apply (rule_tac x="tInit s" in image_eqI)
  apply (auto iff: spr_jview_def envObs_def_raw)
  done

(* simObs *)

lemma spr_simObs_aux:
  assumes tC: "t \<in> jkbpC"
      and ec: "spr_simAbs ec = spr_sim ` equiv_class a (spr_jview a t)"
  shows "\<exists>x xs. toList (snd ec) = x # xs \<and> envObs a (snd x) = envObs a (tLast t)"
proof -
  obtain coEC aEC where ecp: "ec = (coEC, aEC)" by (cases ec)
  then show "\<exists>x xs. toList (snd ec) = x # xs \<and> envObs a (snd x) = envObs a (tLast t)"
    apply -
    apply (cases aEC)
     using simAbs_ec_refl[OF tC ec]
     apply (unfold spr_sim_def_raw spr_simAbs_def)[1]
     apply simp
    using simAbs_ec_agent_equiv[OF tC ec] ecp
    apply (auto simp add: Let_def toList_fromList sorted_Cons agent_equiv_def)
    apply (subgoal_tac "(aa, b) \<in> insert (aa, b) (set xs)")
     defer
     apply blast
    apply auto
    done
qed

lemma spr_simObs'[iff]:
  assumes tC: "t \<in> jkbpC"
      and ec: "spr_simAbs ec = spr_sim ` equiv_class a (spr_jview a t)"
  shows "spr_simObs a ec = envObs a (tLast t)"
  using simAbs_ec_agent_equiv[OF tC ec] spr_simObs_aux[OF tC ec]
  unfolding spr_simObs_def envObs_def_raw
  apply (cases ec)
  apply clarsimp
  apply (cut_tac xs="b" and y="(aa, ba)" and ys=xs in hd_toList)
   apply simp
  apply simp
  done

lemma spr_simObs:
  "\<forall>a ec t. t \<in> jkbpC \<and> spr_simAbs ec = spr_sim ` equiv_class a (spr_jview a t)
  \<longrightarrow> spr_simObs a ec = envObs a (tLast t)"
  by auto

(* simAction *)

definition
  spr_rep_rels :: "'a \<Rightarrow> (('a, 'es, 'as) BEState \<times> ('a, 'es, 'as) BEState) Relation"
where
  "spr_rep_rels \<equiv> \<lambda>a.
    { ((u, v), (u', v')) . coEC_rels envObs a (u, v) (u', v') }"

definition
  spr_rep_ks :: "('a, 'es, 'as) BEState Relation
               \<Rightarrow> ('a, 'p, ('a, 'es, 'as) BEState \<times> ('a, 'es, 'as) BEState) KripkeStructure"
where
  "spr_rep_ks \<equiv> \<lambda>tcobsR. mkKripke tcobsR spr_rep_rels (envVal \<circ> snd)"

lemma spr_rep_ks_kripke[intro, simp]: "kripke (spr_rep_ks X)"
  unfolding spr_rep_ks_def by (rule kripkeI) simp

lemma spr_rep_ks_S5n[intro, simp]: "S5n (spr_rep_ks X)"
  unfolding spr_rep_ks_def spr_rep_rels_def coEC_rels_def
  apply (rule S5nI, rule equivI)
  apply (auto intro: refl_onI symI transI)
  done

lemma spr_rep_ks_simps[simp]:
  "worlds (spr_rep_ks X) = X"
  "\<lbrakk> (s, s') \<in> relations (spr_rep_ks X) a \<rbrakk> \<Longrightarrow> envObs a (fst s) = envObs a (fst s')"
  "\<lbrakk> (s, s') \<in> relations (spr_rep_ks X) a \<rbrakk> \<Longrightarrow> envObs a (snd s) = envObs a (snd s')"
  "valuation (spr_rep_ks X) = envVal \<circ> snd"
  unfolding spr_rep_ks_def spr_rep_rels_def coEC_rels_def by auto

(* Show the eval function corresponds with the standard semantics. *)

lemma spr_coEC_relation_image_FIXME:
  "s \<in> toSet coEC
    \<Longrightarrow> toSet (spr_coEC_relation_image envObs coEC a s) = relations (spr_rep_ks (toSet coEC)) a `` {s}"
  unfolding spr_coEC_relation_image_def spr_rep_ks_def spr_rep_rels_def
  by (auto simp: toSet_def[symmetric])

lemma FIXME_rels_closed:
  "S5n M \<Longrightarrow> relations M a `` (relations M a `` X) \<subseteq> relations M a `` X"
  apply (drule S5nD[where a=a])
  apply (erule equivE)
  by (auto dest: refl_onD symD transD elim: equivE)

lemma eval_rec_models:
  assumes X: "relations (spr_rep_ks (toSet Y)) a `` toSet X \<subseteq> toSet X"
      and XY: "toSet X \<subseteq> toSet Y"
      and s: "s \<in> toSet X"
  shows "s \<in> toSet (eval_rec envVal X (spr_coEC_relation_image envObs Y) \<phi>)
     \<longleftrightarrow> spr_rep_ks (toSet Y), s \<Turnstile> \<phi>"
using X XY s
proof(induct \<phi> arbitrary: X s a)
  case (Knows a' \<phi> X s a)
  from Knows(4) show ?case
    using spr_coEC_relation_image_FIXME[OF set_mp[OF Knows(3) Knows(4)], where a=a']
    apply (simp add: Let_def)
    apply rule
     apply (drule arg_cong[where f="toSet"])
     apply (clarsimp simp: odlist_all_iff)
     apply (cut_tac a=a' and s="(a, b)" and X="spr_coEC_relation_image envObs Y a' (aa, ba)" in Knows.hyps)
      using Knows(2)
      apply simp_all
      apply (auto simp add: FIXME_rels_closed[OF spr_rep_ks_S5n])[1]
      apply (auto iff: spr_rep_ks_def)[1]
     apply auto[1]

    apply (clarsimp simp: toSet_eq_iff odlist_all_iff)
    apply (subst Knows.hyps[where a=a'])
     apply simp_all
     apply (auto simp add: FIXME_rels_closed[OF spr_rep_ks_S5n])[1]
     apply (auto iff: spr_rep_ks_def)[1]
    done
qed simp_all

lemma FIXME_X_closed:
  assumes tC: "t \<in> jkbpC"
      and ec: "spr_simAbs ec = spr_sim ` equiv_class a (spr_jview a t)"
  shows "relations (spr_rep_ks (toSet (fst ec))) a `` toSet (snd ec) \<subseteq> toSet (snd ec)"
  apply rule
  apply (simp add: simAbs_ec_agent_equiv[OF tC ec] simAbs_ec_tObsC_abs[OF tC ec])
  unfolding spr_rep_ks_def
  apply simp
  unfolding agent_equiv_def tObsC_abs_def spr_rep_rels_def coEC_rels_def
  apply auto
  apply (rule_tac x=t'b in exI)
  apply clarsimp
  apply (rule spr_jview_tObsCI)
  apply simp_all
  apply auto[1]
  apply (rule spr_jview_det_ps)
  using tC
  apply auto
  done

lemma FIXME_agent_equiv_tObsC_abs:
  "tObsC t' = tObsC t \<Longrightarrow> agent_equiv a t \<subseteq> tObsC_abs t'"
  unfolding agent_equiv_def tObsC_abs_def
  by (auto intro: spr_jview_tObsC)

lemma FIXME_X_Y:
  assumes tC: "t \<in> jkbpC"
      and ec: "spr_simAbs ec = spr_sim ` equiv_class a (spr_jview a t)"
  shows "toSet (snd ec) \<subseteq> toSet (fst ec)"
  using assms by (simp add: FIXME_agent_equiv_tObsC_abs)

lemma FIXME_rels:
  assumes tC: "t \<in> jkbpC"
      and ec: "spr_simAbs ec = spr_sim ` equiv_class a (spr_jview a t)"
      and x: "x \<in> agent_equiv a t"
      and xy: "(x, y) \<in> relations (spr_rep_ks (toSet (fst ec))) a"
  shows "y \<in> agent_equiv a t"
  using assms
  apply simp
  unfolding agent_equiv_def tObsC_abs_def spr_rep_ks_def spr_rep_rels_def coEC_rels_def
  apply auto
  apply (rule_tac x=t'b in exI)
  apply clarsimp
  apply (rule spr_jview_tObsCI)
   apply simp
  apply auto[1]
  apply (rule spr_jview_det_ps)
  using tC
  apply auto
  done

lemma FIXME_rels2:
  assumes tC: "t \<in> jkbpC"
      and x: "x \<in> agent_equiv a t"
      and y: "y \<in> agent_equiv a t"
  shows "(x, y) \<in> relations (spr_rep_ks (tObsC_abs t)) a"
  using assms
  unfolding agent_equiv_def spr_rep_ks_def spr_rep_rels_def coEC_rels_def
  apply clarsimp
  apply safe
  prefer 3
  apply (erule tObsC_absI) back
   apply simp_all
   apply (erule spr_jview_tObsC)
  prefer 3
  apply (erule tObsC_absI) back back
   apply simp_all
   apply (erule spr_jview_tObsC)
  apply (rule spr_tFirst)
   apply simp
  apply (rule spr_tLast)
   apply simp
  done

lemma evalS_models:
  assumes tC: "t \<in> jkbpC"
      and ec: "spr_simAbs ec = spr_sim ` equiv_class a (spr_jview a t)"
      and subj_phi: "subjective a \<phi>"
      and s: "s \<in> toSet (snd ec)"
  shows "evalS envVal (snd ec) (spr_coEC_relation_image envObs (fst ec)) \<phi>
     \<longleftrightarrow> spr_rep_ks (toSet (fst ec)), s \<Turnstile> \<phi>" (is "?lhs \<phi> = ?rhs \<phi>")
using subj_phi s ec
proof(induct \<phi> rule: subjective.induct[case_names Kprop Knot Kand Knows])
  case (Knows a a' \<psi>) thus ?case
    apply (simp add: toSet_eq_iff)
    apply rule
     apply clarsimp
     apply (subgoal_tac "(a, b) \<in> toSet (snd ec)")
     apply (drule_tac c="(a, b)" in subsetD)
       apply blast
      apply (simp only: eval_rec_models[OF FIXME_X_closed[OF tC ec] FIXME_X_Y[OF tC ec]])
     using tC Knows
     apply simp
     apply (erule FIXME_rels[OF tC])
     apply simp
     using tC ec
     apply simp

    apply clarsimp
    apply (simp only: eval_rec_models[OF FIXME_X_closed[OF tC ec] FIXME_X_Y[OF tC ec]])
    using tC ec
    apply simp
    apply (erule_tac x="(aa, b)" in ballE)
     apply simp
    using FIXME_rels2[OF tC]
    apply simp
    done
qed simp_all

lemma eval_models':
  assumes tC: "t \<in> jkbpC"
      and ec: "spr_simAbs ec = spr_sim ` equiv_class a (spr_jview a t)"
      and subj_phi: "subjective a \<phi>"
      and s: "s \<in> toSet (snd ec)"
  shows "eval envVal envObs ec \<phi>
     \<longleftrightarrow> spr_rep_ks (toSet (fst ec)), s \<Turnstile> \<phi>"
  unfolding eval_def
  using evalS_models[OF tC ec subj_phi s]
  apply auto
  done

(* This final lemma is specialised for the ultimate equivalence
proof. *)

lemma eval_models:
  assumes tC: "t \<in> jkbpC"
      and ec: "spr_simAbs ec = spr_sim ` equiv_class a (spr_jview a t)"
  shows "set (spr_simAction ec a)
       = set (jAction (spr_rep_ks (toSet (fst ec))) (tFirst t, tLast t) a)"
  unfolding spr_simAction_def jAction_def
  apply clarsimp
  apply rule
   apply clarsimp
   apply (rule_tac x=aa in bexI)
    apply simp
   apply clarsimp
   apply (subst eval_models'[OF tC ec, symmetric])
    using tC ec subj
    apply simp_all
    apply (rule agent_equivI)
    apply simp_all
  apply clarsimp
  apply (rule_tac x=aa in bexI)
   apply simp
  apply clarsimp
  apply (subst eval_models'[OF tC ec])
   using tC ec subj
   apply simp_all
  apply (rule agent_equivI)
   apply simp_all
  done

(* We need an intermediate Kripke structure that allows us to show we
have retained enough structure from @{term "mkMCS"} to decide the
formulas in the kbp.

This is a Kripke structure for the simulated temporal slice: the
subset of jkbpC under simulation relevant to @{term "t"}. *)

definition
  "spr_rep_sim \<equiv> \<lambda>s. (sprFst s, sprLst s)"

abbreviation
  "jkbpCSt_spr t \<equiv> spr_sim ` { t' . t' \<in> jkbpC \<and> tObsC t = tObsC t' }"

abbreviation
  "mkMCSt_spr t \<equiv> mkKripke (jkbpCSt_spr t) spr_sim_rels spr_sim_val"

lemma FIXME_spr_rep_sim_simps[simp]:
  "spr_rep_sim ` spr_sim ` T = (\<lambda>t. (tFirst t, tLast t)) ` T"
  "spr_rep_sim (spr_sim t) = (tFirst t, tLast t)"
  unfolding spr_rep_sim_def spr_sim_def_raw
  apply auto
  apply (rule_tac x="\<lparr> sprFst = tFirst t, sprLst = tLast t, sprCRel = tObsC_abs t \<rparr>" in image_eqI)
  apply auto
  done

lemma jkbpCSt_jkbpCS_subset:
  "jkbpCSt_spr t \<subseteq> spr_sim ` jkbpC"
  by auto

lemma spr_rep_sim:
  assumes tC: "t \<in> jkbpC"
  shows "sim (mkMCSt_spr t)
             ((spr_rep_ks \<circ> sprCRel) (spr_sim t))
             spr_rep_sim" (is "sim ?M ?M' ?f")
proof
  show "sim_range ?M ?M' ?f"
  proof
    show "worlds ?M' = ?f ` worlds ?M"
      apply (simp add: spr_sim_def_raw spr_rep_sim_def)
      apply (auto iff: tObsC_abs_def)
      apply (rule_tac x="\<lparr> sprFst = tFirst t', sprLst = tLast t', sprCRel = tObsC_abs t \<rparr>" in image_eqI)
       apply simp
      apply (rule_tac x=t' in image_eqI)
       apply (simp add: tObsC_abs_def)
      apply auto[1]
      done
  next
    fix a
    show "relations ?M' a \<subseteq> worlds ?M' \<times> worlds ?M'"
      by (simp add: spr_sim_def_raw spr_rep_sim_def spr_rep_ks_def)
  qed
next
  show "sim_val ?M ?M' ?f"
    by (rule, simp add: spr_sim_def spr_sim_val_def spr_rep_ks_def spr_rep_sim_def split: split_split)
next
  show "sim_f ?M ?M' ?f"
    apply rule
    unfolding spr_rep_ks_def spr_rep_rels_def spr_rep_sim_def spr_sim_rels_def coEC_rels_def
    apply (auto iff: spr_sim_def)
    done
next
  show "sim_r ?M ?M' ?f"
    apply rule
    unfolding spr_rep_ks_def spr_rep_rels_def spr_rep_sim_def spr_sim_rels_def spr_sim_def_raw coEC_rels_def
    apply clarsimp
    apply (rule_tac x="\<lparr> sprFst = aa, sprLst = b, sprCRel = tObsC_abs ta \<rparr>" in exI)
    apply (auto iff: tObsC_abs_def)
    apply (rule_tac x=t'a in image_eqI)
    apply auto
    done
qed

(* Connect the simulated temporal slice up to the set of all simulated
traces. *)

lemma FIXME_spr_submodel_aux:
  assumes tC: "t \<in> jkbpC"
      and s: "s \<in> worlds (mkMCSt_spr t)"
  shows "sub_model mkMCS s = sub_model (mkMCSt_spr t) s"
proof(rule sub_model_subset[where T="jkbpCSt_spr t"])
  fix a
  let ?X = "spr_sim ` { t' . t' \<in> jkbpC \<and> tObsC t = tObsC t' }"
  show "relations mkMCS a \<inter> ?X \<times> ?X
      = relations (mkMCSt_spr t) a \<inter> ?X \<times> ?X"
    by (simp add: Int_ac Int_absorb1
                  relation_mono[OF jkbpCSt_jkbpCS_subset jkbpCSt_jkbpCS_subset])
next
  let ?X = "spr_sim ` { t' . t' \<in> jkbpC \<and> tObsC t = tObsC t' }"
  from s show "(\<Union>a. relations (mkMCSt_spr t) a)\<^sup>* `` {s} \<subseteq> ?X"
    apply (clarsimp simp del: mkKripke_simps)
    apply (erule kripke_rels_trc_worlds)
    apply auto
    done
next
  let ?Y = "{ t' . t' \<in> jkbpC \<and> tObsC t = tObsC t' }"
  let ?X = "spr_sim ` ?Y"
  from s obtain t'
    where st': "s = spr_sim t'"
      and t'C: "t' \<in> jkbpC"
      and t'O: "tObsC t = tObsC t'"
    by fastforce
  { fix t''
    assume tt': "(t', t'') \<in> (\<Union>a. relations mkMC a)\<^sup>*"
    from t'C tt' have t''C: "t'' \<in> jkbpC"
      by - (erule kripke_rels_trc_worlds, simp_all)
    from t'O tt' have t''O: "tObsC t = tObsC t''"
      by (simp add: spr_tObsC_trc_aux)
    from t''C t''O have "t'' \<in> ?Y" by simp }
  hence "(\<Union>a. relations mkMC a)\<^sup>* `` {t'} \<subseteq> ?Y"
    by clarsimp
  hence "spr_sim ` ((\<Union>a. relations mkMC a)\<^sup>* `` {t'}) \<subseteq> ?X"
    by (rule image_mono)
  with st' t'C
  show "(\<Union>a. relations mkMCS a)\<^sup>* `` {s} \<subseteq> ?X"
    using sim_trc_commute[OF mkM_kripke spr_sim, where t=t'] by simp
qed (insert s, auto)

(* What we want to show. The proof is a straightforward chaining of
the above refinements. *)

lemma spr_simAction':
  assumes tC: "t \<in> jkbpC"
      and ec: "spr_simAbs ec = spr_sim ` equiv_class a (spr_jview a t)"
  shows "set (spr_simAction ec a) = set (jAction mkMC t a)" (is "?lhs = ?rhs")
proof -
  from tC ec
  have "?lhs = set (jAction (spr_rep_ks (toSet (fst ec))) (tFirst t, tLast t) a)"
    by (rule eval_models)
  also from tC ec have "... = set (jAction (mkMCSt_spr t) (spr_sim t) a)"
    by (simp add: simulation_jAction_eq[OF _ spr_rep_sim] spr_sim_tObsC)
  also from tC have "... = set (jAction mkMCS (spr_sim t) a)"
    using sub_model_jAction_eq[OF FIXME_spr_submodel_aux[OF tC, where s="spr_sim t"], where w'="spr_sim t"]
          sub_model_world_refl[where w="spr_sim t" and M="mkMCSt_spr t"]
    by simp
  also from tC have "... = set (jAction mkMC t a)"
    by (simp add: simulation_jAction_eq[OF _ spr_sim])
  finally show ?thesis .
qed

lemma spr_simAction:
  "\<forall>a ec t. t \<in> jkbpC \<and> spr_simAbs ec = spr_sim ` equiv_class a (spr_jview a t)
   \<longrightarrow> set (spr_simAction ec a) = set (jAction mkMC t a)"
  using spr_simAction' by auto

(* simTrans *)

lemma spr_jview_tObsC_trans:
  "\<lbrakk>spr_jview a t = spr_jview a t'; spr_jview a' t' = spr_jview a' t''\<rbrakk>
     \<Longrightarrow> tObsC t = tObsC t''"
  apply (drule spr_jview_tObsC)
  apply (drule spr_jview_tObsC)
  apply simp
  done

lemma FIXME_spr_trans_aEC:
  assumes tC: "t \<in> jkbpC"
      and ec: "spr_simAbs ec = spr_sim ` equiv_class a (spr_jview a t)"
  shows "set (spr_trans (fst ec) (snd ec))
       = { (tFirst t', s) |t' s. t' \<leadsto> s \<in> jkbpC \<and> spr_jview a t' = spr_jview a t }" (is "?lhs = ?rhs")
proof
  show "?lhs \<subseteq> ?rhs"
  proof
    fix x assume x: "x \<in> ?lhs"
    with assms show "x \<in> ?rhs"
      unfolding spr_trans_def
      apply (clarsimp simp del: split_paired_Ex split_paired_All simp add: toSet_def[symmetric] agent_equiv_def)
      apply (rule_tac x=t' in exI)
      apply simp
      apply (rule_tac n="Suc (tLength t')" in jkbpCn_jkbpC_inc)
      apply (auto iff: Let_def simp del: split_paired_Ex split_paired_All)
      apply (simp add: mkAacts_FIXME[OF agents[unfolded toSet_def]])

      apply (rule_tac x=aa in exI)
      apply (rule_tac x=x in exI)
      apply (simp add: spr_jAction_def)
      apply (subst (asm) spr_simAction')
        apply assumption
        apply rule
         apply clarsimp
         apply (clarsimp simp: spr_simAbs_def)
         apply (subst (asm) spr_coEC_relation_image_FIXME)
          apply (simp add: ec)
          apply (erule tObsC_absI)
          apply simp_all
          apply (erule spr_jview_tObsC)
          using ec
          apply (clarsimp simp: spr_rep_ks_def spr_rep_rels_def coEC_rels_def tObsC_abs_conv)
          apply (rule_tac x=t'b in image_eqI)
          apply (auto iff: spr_sim_def)[1]
          apply clarsimp
          apply (rule spr_jview_tObsCI[OF _ _ spr_jview_det_ps])
           apply simp_all
          apply (erule spr_jview_tObsC[symmetric])
          apply (erule spr_jview_tObsC[symmetric])
         apply clarsimp
         apply (clarsimp simp: spr_simAbs_def)
         apply (subst spr_coEC_relation_image_FIXME)
          apply (simp_all add: ec)
          apply (erule tObsC_absI)
          apply (erule spr_jview_tObsC)
          apply simp_all
         apply (rule_tac x="tFirst xb" in exI)
         apply (rule_tac x="tLast xb" in exI)
         apply (simp add: spr_sim_def)
         apply rule
          apply (drule tObsC_abs_jview_eq)
          apply simp
          apply (erule tObsC_abs_jview_eq[symmetric])
         apply (clarsimp simp: spr_rep_ks_def spr_rep_rels_def coEC_rels_def tObsC_abs_conv)
         apply rule
         apply (rule spr_tFirst)
          apply simp
         apply rule
         apply (rule spr_tLast)
          apply simp
         apply rule
         apply (rule_tac x=t' in exI)
         apply simp
         apply (erule spr_jview_tObsC)
         apply (rule_tac x=xb in exI)
         apply simp
         apply (drule spr_jview_tObsC)
         apply (drule spr_jview_tObsC)
         apply simp
      apply (subst jkbpC_jkbpCn_jAction_eq[symmetric])
      apply auto
      done
  qed
  show "?rhs \<subseteq> ?lhs"
  proof
    fix x assume x: "x \<in> ?rhs"
    then obtain t' s
      where x': "x = (tFirst t', s)"
        and t'sC: "t' \<leadsto> s \<in> jkbpC"
        and F: "spr_jview a t' = spr_jview a t"
      by blast
    from t'sC have t'Cn: "t' \<in> jkbpCn (tLength t')" by blast
    from t'sC obtain eact aact
      where eact: "eact \<in> set (envAction (tLast t'))"
        and aact: "\<forall>a. aact a \<in> set (jAction (mkM (jkbpCn (tLength t'))) t' a)"
        and s: "s = envTrans eact aact (tLast t')"
      using jkbpC_tLength_inv[where t="t' \<leadsto> s" and n="Suc (tLength t')"]
      by (auto iff: Let_def)
    from tC t'sC ec F x' s eact aact
    show "x \<in> ?lhs"
      unfolding spr_trans_def
      apply (clarsimp simp del: split_paired_Ex split_paired_All simp: toSet_def[symmetric])
      apply (rule bexI[where x="(tFirst t', tLast t')"])
      apply simp
      apply (rule bexI[where x="eact"])
      apply (rule_tac x="aact" in image_eqI)
      apply simp_all
      apply (simp add: mkAacts_FIXME[OF agents[unfolded toSet_def]])
      defer
      apply blast
      apply (simp add: spr_jAction_def)
      apply (subst spr_simAction'[where t=t'])
      apply blast
      defer
      apply (auto iff: jkbpC_jkbpCn_jAction_eq[OF t'Cn])[1]

      apply (clarsimp simp: spr_simAbs_def)
      apply (subst spr_coEC_relation_image_FIXME)
      apply (simp_all add: ec)
      apply (rule tObsC_absI[where t=t and t'=t'])
       apply simp_all
       apply blast
       apply (blast intro: spr_jview_tObsC)
      apply (clarsimp simp: spr_rep_ks_def spr_rep_rels_def coEC_rels_def tObsC_abs_conv)
      apply rule
       apply clarsimp
       apply (rule_tac x=t'aa in image_eqI)
        apply (auto iff: spr_sim_def)[1]
       apply simp
       apply (rule spr_jview_tObsCI[OF _ _ spr_jview_det_ps])
       apply simp_all
       apply (erule spr_jview_tObsC[symmetric])
       apply blast
       apply (erule spr_jview_tObsC[symmetric])
      apply (clarsimp simp: spr_sim_def)
      apply rule
       apply (drule tObsC_abs_jview_eq)
       apply (drule tObsC_abs_jview_eq)
       apply simp
      apply rule
      apply (rule spr_tFirst)
       apply simp
      apply rule
      apply (rule spr_tLast)
       apply simp
      apply rule
       apply (rule_tac x=t' in exI)
       apply (auto dest: spr_jview_tObsC intro: spr_jview_tObsC_trans)
      done
  qed
qed

lemma FIXME_spr_trans_coEC:
  assumes tC: "t \<in> jkbpC"
      and ec: "spr_simAbs ec = spr_sim ` equiv_class a (spr_jview a t)"
  shows "set (spr_trans (fst ec) (fst ec))
       = { (tFirst t', s) |t' s. t' \<leadsto> s \<in> jkbpC \<and> tObsC t' = tObsC t }" (is "?lhs = ?rhs")
proof
  show "?lhs \<subseteq> ?rhs"
  proof
    fix x assume x: "x \<in> ?lhs"
    with assms show "x \<in> ?rhs"
      unfolding spr_trans_def
      apply (clarsimp simp del: split_paired_Ex split_paired_All simp add: toSet_def[symmetric] tObsC_abs_def)
      apply (rule_tac x=t' in exI)
      apply simp
      apply (rule_tac n="Suc (tLength t')" in jkbpCn_jkbpC_inc)
      apply (auto iff: Let_def simp del: split_paired_Ex split_paired_All)
      apply (simp add: mkAacts_FIXME[OF agents[unfolded toSet_def]])

      apply (rule_tac x=aa in exI)
      apply (rule_tac x=x in exI)
      apply (simp add: spr_jAction_def)
      apply (subst (asm) spr_simAction')
        apply assumption
       apply rule
        apply clarsimp
        apply (clarsimp simp: spr_simAbs_def)
        apply (subst (asm) spr_coEC_relation_image_FIXME)
         apply (simp add: ec)
         apply (erule tObsC_absI)
          apply simp_all
        apply (clarsimp simp: spr_rep_ks_def spr_rep_rels_def coEC_rels_def tObsC_abs_conv ec)
        apply (rule_tac x=t'b in image_eqI)
         apply (auto iff: spr_sim_def ec)[1]
        apply clarsimp
        apply (rule spr_jview_tObsCI[OF _ _ spr_jview_det_ps])
         apply simp_all
       apply (clarsimp simp: spr_simAbs_def)
       apply (subst spr_coEC_relation_image_FIXME)
        apply (simp_all add: ec)
        apply (erule tObsC_absI)
        apply simp_all
       apply (rule_tac x="tFirst xb" in exI)
       apply (rule_tac x="tLast xb" in exI)
       apply (simp add: spr_sim_def)
       apply rule
        apply (drule tObsC_abs_jview_eq)
        apply auto[1]
       apply (clarsimp simp: spr_rep_ks_def spr_rep_rels_def coEC_rels_def tObsC_abs_conv)
       apply rule
        apply (rule spr_tFirst)
        apply simp
       apply rule
        apply (rule spr_tLast)
        apply simp
       apply rule
        apply (rule_tac x=t' in exI)
        apply simp
       apply (rule_tac x=xb in exI)
       apply simp
       apply (drule spr_jview_tObsC)
       apply simp
      apply (subst jkbpC_jkbpCn_jAction_eq[symmetric])
      apply auto
      done
  qed
  show "?rhs \<subseteq> ?lhs"
  proof
    fix x assume x: "x \<in> ?rhs"
    then obtain t' s
      where x': "x = (tFirst t', s)"
        and t'sC: "t' \<leadsto> s \<in> jkbpC"
        and F: "tObsC t' = tObsC t"
      by blast
    from t'sC have t'Cn: "t' \<in> jkbpCn (tLength t')" by blast
    from t'sC obtain eact aact
      where eact: "eact \<in> set (envAction (tLast t'))"
        and aact: "\<forall>a. aact a \<in> set (jAction (mkM (jkbpCn (tLength t'))) t' a)"
        and s: "s = envTrans eact aact (tLast t')"
      using jkbpC_tLength_inv[where t="t' \<leadsto> s" and n="Suc (tLength t')"]
      by (auto iff: Let_def)
    from tC t'sC ec F x' s eact aact
    show "x \<in> ?lhs"
      unfolding spr_trans_def
      apply (clarsimp simp del: split_paired_Ex split_paired_All simp: toSet_def[symmetric])
      apply (rule bexI[where x="(tFirst t', tLast t')"])
      apply simp
      apply (rule bexI[where x="eact"])
      apply (rule_tac x="aact" in image_eqI)
      apply simp_all
      apply (simp add: mkAacts_FIXME[OF agents[unfolded toSet_def]])
      defer
      apply blast
      apply (simp add: spr_jAction_def)
      apply (subst spr_simAction'[where t=t'])
      apply blast
      defer
      apply (auto iff: jkbpC_jkbpCn_jAction_eq[OF t'Cn])[1]

      apply (clarsimp simp: spr_simAbs_def)
      apply (subst spr_coEC_relation_image_FIXME)
      apply (simp_all add: ec)
      apply (rule tObsC_absI[where t=t and t'=t'])
       apply simp_all
       apply blast
      apply (clarsimp simp: spr_rep_ks_def spr_rep_rels_def coEC_rels_def tObsC_abs_conv)
      apply rule
       apply clarsimp
       apply (rule_tac x=t'aa in image_eqI)
        apply (auto iff: spr_sim_def_raw)[1]
       apply simp
       apply (rule spr_jview_tObsCI[OF _ _ spr_jview_det_ps])
       apply simp_all
       apply blast
      apply (clarsimp simp: spr_sim_def_raw)
      apply rule
       apply (drule tObsC_abs_jview_eq)
       apply simp
      apply rule
      apply (auto intro: spr_tFirst)[1]
      apply rule
      apply (auto intro: spr_tLast)[1]
      apply (auto intro: spr_tLast)[1]
      apply (rule_tac x=ta in exI)
      apply (auto dest: spr_jview_tObsC intro: spr_jview_tObsC_trans)[1]
      done
  qed
qed

lemma spr_simObsC:
    assumes t'sC: "t \<leadsto> s \<in> jkbpC"
        and aEC': "toSet aEC = (envObs_rel (envObs a) \<inter> X \<times> X) `` {(tFirst t, s)}"
        and X: "X = {(tFirst t', s) |t' s. t' \<leadsto> s \<in> jkbpC \<and> spr_jview a t' = spr_jview a t}"
    shows "spr_simObsC envObsC aEC = envObsC (es s)"
  unfolding spr_simObsC_def
  apply (cases aEC)
   using assms
   apply auto[1]
  using assms
  apply (simp add: ODList.hd_def toList_fromList)
  apply (subgoal_tac "x \<in> insert x (set xs)")
   apply (auto iff: envObs_def_raw)[1]
  apply blast
  done

lemma spr_simAbs_shuffle:
  "spr_simAbs ` X
 = (\<lambda>(coEC, aEC). {\<lparr>sprFst = s, sprLst = s', sprCRel = coEC\<rparr> |s s'. (s, s') \<in> aEC}) ` { (toSet x, toSet y) |x y. (x, y) \<in> X }"
  unfolding spr_simAbs_def
  apply auto
  done

lemma spr_simTrans':
  assumes tC: "t \<in> jkbpC"
      and ec: "spr_simAbs ec = spr_sim ` equiv_class a (spr_jview a t)"
  shows "spr_simAbs ` set (spr_simTrans a ec)
      = { spr_sim ` equiv_class a (spr_jview a (t' \<leadsto> s))
          |t' s. t' \<leadsto> s \<in> jkbpC \<and> spr_jview a t' = spr_jview a t}" (is "?lhs = ?rhs")
proof
  show "?lhs \<subseteq> ?rhs"
  proof
    fix x assume x: "x \<in> ?lhs"
    then obtain rx
      where xrx: "x = spr_simAbs rx"
        and rx: "rx \<in> set (spr_simTrans a ec)" by blast
    with tC ec obtain coEC' aEC' UV' t' s
      where rxp: "rx = (coEC', aEC')"
        and t'sC: "t' \<leadsto> s \<in> jkbpC"
        and tt': "spr_jview a t' = spr_jview a t"
        and aEC': "toSet aEC' = (envObs_rel (envObs a) \<inter> set (spr_trans (fst ec) (snd ec))
                                                       \<times> set (spr_trans (fst ec) (snd ec))) `` {(tFirst t', s)}"
        and coEC': "coEC' = ODList.filter (\<lambda>s. envObsC (es (snd s)) = spr_simObsC envObsC aEC') (fromList (local.spr_trans (fst ec) (fst ec)))"
      unfolding spr_simTrans_def
      using FIXME_spr_trans_aEC[OF assms]
      apply (auto split: split_split_asm)
      apply (drule imageI[where f=set])
      apply (simp add: partition[OF envObs_rel_equiv])
      apply (erule quotientE)
      apply fastforce
      done
    from t'sC tt' aEC' coEC'
    have "spr_simAbs (coEC', aEC') = spr_sim ` equiv_class a (spr_jview a (t' \<leadsto> s))"
      unfolding spr_simAbs_def
      apply clarsimp
      apply rule
       using FIXME_spr_trans_aEC[OF assms] FIXME_spr_trans_coEC[OF assms]
       apply clarsimp
       apply (rule_tac x="t'aa \<leadsto> s'" in image_eqI)
        apply (simp add: spr_sim_def)
        apply (cut_tac aEC=aEC' and t=t' and s=s in spr_simObsC[where a=a])
        apply simp_all
        apply rule
         apply clarsimp
         apply (erule_tac t'="t'b \<leadsto> sa" in tObsC_absI)
          apply simp_all
          apply (auto dest: spr_jview_tObsC iff: tObsC_def envObs_def_raw)[1]
        apply (clarsimp simp: envObs_def_raw tObsC_abs_conv)
        apply (case_tac t'b)
         apply (simp add: tObsC_def)
        apply clarsimp
        apply (rule_tac x=Trace in exI)
        apply (auto dest: spr_jview_tObsC simp: tObsC_def)[1]
       apply (simp add: spr_jview_def)
      using FIXME_spr_trans_aEC[OF assms] FIXME_spr_trans_coEC[OF assms]
      apply (clarsimp simp: spr_sim_def)
      apply (cut_tac aEC=aEC' and t=t' and s=s in spr_simObsC[where a=a])
       apply simp_all
      apply (frule spr_jview_tStep_eq_inv)
      apply clarsimp
      apply safe
       apply (clarsimp simp: tObsC_abs_conv)
       apply (case_tac t'a)
        apply (simp add: tObsC_def)
       apply clarsimp
       apply (rule_tac x="Trace" in exI)
       apply (drule spr_jview_prefix_closed)
       apply (auto dest: spr_jview_tObsC simp: tObsC_def)[1]

       apply (auto simp: spr_jview_def Let_def envObs_def_raw)[1]

       apply (erule_tac t'="t'a \<leadsto> sa" in tObsC_absI)
        apply simp_all

        apply (drule spr_jview_tObsC[symmetric])
        apply (frule spr_jview_prefix_closed)
        apply (auto dest: spr_jview_tObsC simp: tObsC_def)[1]

        apply (simp add: spr_jview_def)
        apply auto[1]
        apply (rule_tac x="t''" in exI)
        apply (drule spr_jview_prefix_closed)
        apply simp
        done
    with xrx rxp t'sC tt'
    show "x \<in> ?rhs"
      apply simp
      apply (rule_tac x=t' in exI)
      apply (rule_tac x=s in exI)
      apply simp
      done
  qed
next
  show "?rhs \<subseteq> ?lhs"
  proof
    fix x assume x: "x \<in> ?rhs"
    then obtain t' s
      where t'sC: "t' \<leadsto> s \<in> jkbpC"
        and tt': "spr_jview a t' = spr_jview a t"
        and xt's: "x = spr_sim ` equiv_class a (spr_jview a (t' \<leadsto> s))"
      by auto
    then have "(\<lambda>s. (sprFst s, sprLst s)) ` x \<in> set ` set (partition (envObs_rel (envObs a)) (spr_trans (fst ec) (snd ec)))"
      apply (simp add: partition[OF envObs_rel_equiv[where envObs="envObs a"]] FIXME_spr_trans_aEC[OF assms] spr_sim_def_raw)
      apply clarsimp
      apply (rule_tac x="(tFirst t', s)" in quotientI2)
       apply auto[1]
      apply (auto dest: spr_jview_tStep_eq_inv)
       apply (frule spr_jview_tStep_eq_inv)
       apply clarsimp
       apply (drule spr_jview_prefix_closed)
       apply auto[1]
      apply (rule_tac x="\<lparr>sprFst = tFirst t'aa, sprLst = sa, sprCRel = tObsC_abs (t'aa \<leadsto> sa)\<rparr>" in image_eqI)
       apply simp
      apply (rule_tac x="t'aa \<leadsto> sa" in image_eqI)
       apply simp
      apply (simp add: spr_jview_def)
      done
    then obtain rx
      where "rx \<in> set (partition (envObs_rel (envObs a)) (spr_trans (fst ec) (snd ec)))"
        and "set rx = (\<lambda>s. (sprFst s, sprLst s)) ` x"
      by auto
    with t'sC tt' xt's show "x \<in> ?lhs"
      unfolding spr_simTrans_def
      apply clarsimp
      apply (rule_tac x="(ODList.filter (\<lambda>s. envObsC (es (snd s)) = spr_simObsC envObsC (fromList rx)) (fromList (local.spr_trans (fst ec) (fst ec))), fromList rx)" in image_eqI)
       prefer 2
       apply (rule_tac x="rx" in image_eqI)
        apply simp
       apply simp

       apply (subst spr_simObsC[where a=a and t=t' and s=s, OF _ _ refl])
        apply simp_all
        apply rule
         apply clarsimp
         apply (frule spr_jview_tStep_eq_inv)
         apply (auto simp: spr_jview_def spr_sim_def_raw)[1]
        apply clarsimp
        apply (rule_tac x="spr_sim (t'aa \<leadsto> sa)" in image_eqI)
         apply (simp add: spr_sim_def_raw)
        apply (rule_tac x="t'aa \<leadsto> sa" in image_eqI)
         apply simp
        apply (simp add: spr_jview_def)

       apply (clarsimp simp: FIXME_spr_trans_coEC[OF assms] spr_sim_def_raw spr_simAbs_def)
       apply rule
        apply (auto iff: tObsC_abs_conv)[1]
         apply (frule spr_jview_tStep_eq_inv)
         apply clarsimp
         apply (frule tObsC_tStep_eq_inv)
         apply clarsimp
         apply (drule spr_jview_prefix_closed)
         apply (drule spr_jview_tObsC)
         apply (drule spr_jview_tObsC)
         apply (drule tObsC_prefix_closed)
         apply (rule_tac x=t''a in exI)
         apply simp

         apply (frule spr_jview_tStep_eq_inv)
         apply clarsimp
         apply (frule tObsC_tStep_eq_inv)
         apply clarsimp
         apply (drule spr_jview_tObsC) back
         apply (simp add: tObsC_def)

         apply (rule_tac x="t'a \<leadsto> sa" in exI)
         apply simp
         apply (frule spr_jview_tStep_eq_inv)
         apply clarsimp
         apply (drule spr_jview_tObsC)
         apply (frule spr_jview_tObsC)
         apply (simp add: tObsC_def)

         apply (rule_tac x="spr_sim ta" in image_eqI)
          apply (simp add: spr_sim_def_raw)
         apply (rule_tac x=ta in image_eqI)
          apply (simp add: spr_sim_def_raw)
         apply simp
       apply clarsimp
       apply (rule_tac x=ta in image_eqI)
        prefer 2
        apply simp
        apply (clarsimp simp: tObsC_abs_def)
        apply auto[1]

        apply (rule_tac x="t'a \<leadsto> sa" in exI)
        apply simp
        apply (frule spr_jview_tStep_eq_inv)
        apply clarsimp
        apply (drule spr_jview_tObsC)
        apply (frule spr_jview_tObsC)
        apply (simp add: tObsC_def)

        apply (frule spr_jview_tStep_eq_inv)
        apply clarsimp
        apply (frule tObsC_tStep_eq_inv)
        apply clarsimp
        apply (rule_tac x="t''a" in exI)
        apply (drule spr_jview_tObsC)
        apply (frule spr_jview_tObsC)
        apply (simp add: tObsC_def)

        apply (frule spr_jview_tStep_eq_inv)
        apply clarsimp
        apply (frule tObsC_tStep_eq_inv)
        apply clarsimp
        apply (drule spr_jview_tObsC) back
        apply (simp add: tObsC_def)
        done
  qed
qed

lemma spr_simTrans:
  "\<forall>a ec t. t \<in> jkbpC \<and> spr_simAbs ec = spr_sim ` equiv_class a (spr_jview a t)
     \<longrightarrow> spr_simAbs ` set (spr_simTrans a ec)
      = { spr_sim ` equiv_class a (spr_jview a (t' \<leadsto> s))
          |t' s. t' \<leadsto> s \<in> jkbpC \<and> spr_jview a t' = spr_jview a t}"
  using spr_simTrans' by auto

end

sublocale DetBroadcastEnvironment < SPRdet!: SimEnvironment
            jkbp envInit envAction envTrans envVal
            envObs spr_sim spr_sim_rels spr_sim_val
            spr_simAbs spr_simObs spr_simInit spr_simTrans spr_simAction

  apply unfold_locales

  apply simp

  apply (rule spr_simInit)
  apply (rule spr_simObs)
  apply (rule spr_simAction)
  apply (rule spr_simTrans)
  done

type_synonym
  ('a, 'es, 'obs, 'as) trans_trie
    = "(('a, 'es, 'as) BEState,
        (('a, 'es, 'as) BEState,
          (('a, 'es, 'as) BEState,
           (('a, 'es, 'as) BEState, ('obs, ('a, 'es, 'as) SPRstate_rep) mapping) trie) trie) trie) trie"

definition
  trans_MapOps_lookup :: "('a :: linorder, 'es :: linorder, 'obs, 'as :: linorder) trans_trie
                        \<Rightarrow> ('a, 'es, 'as) SPRstate_rep \<times> 'obs
                        \<rightharpoonup> ('a, 'es, 'as) SPRstate_rep"
where
  "trans_MapOps_lookup \<equiv> \<lambda>m ((coEC, aEC), obs).
     Option.bind (trie_lookup m (map fst (toList coEC)))
      (\<lambda>m. Option.bind (trie_lookup m (map snd (toList coEC)))
       (\<lambda>m. Option.bind (trie_lookup m (map fst (toList aEC)))
        (\<lambda>m. Option.bind (trie_lookup m (map snd (toList aEC)))
         (\<lambda>m. Mapping.lookup m obs))))"

definition
  trans_MapOps_update :: "('a, 'es, 'as) SPRstate_rep \<times> 'obs
                        \<Rightarrow> ('a, 'es, 'as) SPRstate_rep
                        \<Rightarrow> ('a :: linorder, 'es :: linorder, 'obs, 'as :: linorder) trans_trie
                        \<Rightarrow> ('a, 'es, 'obs, 'as) trans_trie"
where
  "trans_MapOps_update \<equiv> \<lambda>((coEC, aEC), obs) v m.
     trie_update_with' (map fst (toList coEC)) m trie_empty
      (\<lambda>m. trie_update_with' (map snd (toList coEC)) m trie_empty
       (\<lambda>m. trie_update_with' (map fst (toList aEC)) m trie_empty
        (\<lambda>m. trie_update_with' (map snd (toList aEC)) m Mapping.empty
         (\<lambda>m. Mapping.update obs v m))))"

definition
  trans_MapOps :: "(('a :: linorder, 'es :: linorder, 'obs, 'as :: linorder) trans_trie,
                    ('a, 'es, 'as) SPRstate_rep \<times> 'obs,
                    ('a, 'es, 'as) SPRstate_rep) MapOps"
where
  "trans_MapOps \<equiv>
     \<lparr> MapOps.empty = trie_empty,
       lookup = trans_MapOps_lookup,
       update = trans_MapOps_update \<rparr>"

lemma (in DetBroadcastEnvironment) spr_simAbs_inj_on[intro, simp]:
  "inj_on spr_simAbs { x . spr_simAbs x \<in> SPRdet.jkbpSEC }"
proof(rule inj_onI)
  fix x y
  assume x: "x \<in> { x . spr_simAbs x \<in> SPRdet.jkbpSEC }"
     and y: "y \<in> { x . spr_simAbs x \<in> SPRdet.jkbpSEC }"
     and xy: "spr_simAbs x = spr_simAbs y"
  from x obtain a t
    where tC: "t \<in> jkbpC"
      and ec: "spr_simAbs x = spr_sim ` equiv_class a (spr_jview a t)"
    by auto
  from simAbs_ec_tObsC_abs[OF tC ec] simAbs_ec_tObsC_abs[OF tC trans[OF xy[symmetric] ec], symmetric]
  have "fst x = fst y" by (blast intro: injD[OF toSet_inj])
  moreover
  from simAbs_ec_agent_equiv[OF tC ec] simAbs_ec_agent_equiv[OF tC trans[OF xy[symmetric] ec], symmetric]
  have "snd x = snd y" by (blast intro: injD[OF toSet_inj])
  ultimately show "x = y" by (simp add: prod_eqI)
qed

lemma (in DetBroadcastEnvironment) trans_MapOps[intro, simp]:
  "MapOps (\<lambda>k. (spr_simAbs (fst k), snd k)) (SPRdet.jkbpSEC \<times> UNIV) trans_MapOps"
proof
  fix k show "MapOps.lookup trans_MapOps (MapOps.empty trans_MapOps) k = None"
    unfolding trans_MapOps_def trans_MapOps_lookup_def
    by (auto split: split_split)
next
  fix e k k' M
  assume k: "(spr_simAbs (fst k), snd k) \<in> SPRdet.jkbpSEC \<times> (UNIV :: 'z set)"
     and k': "(spr_simAbs (fst k'), snd k') \<in> SPRdet.jkbpSEC \<times> (UNIV :: 'z set)"
  show "MapOps.lookup trans_MapOps (MapOps.update trans_MapOps k e M) k'
         = (if (spr_simAbs (fst k'), snd k') = (spr_simAbs (fst k), snd k)
             then Some e else MapOps.lookup trans_MapOps M k')"
  proof(cases "(spr_simAbs (fst k'), snd k') = (spr_simAbs (fst k), snd k)")
    case True hence "k = k'"
      using inj_onD[OF spr_simAbs_inj_on] k k' by (auto iff: prod_eqI)
    thus ?thesis
      unfolding trans_MapOps_def trans_MapOps_lookup_def trans_MapOps_update_def
      by (auto simp: trie_lookup_trie_update_with split: option.split split_split)
  next
    case False thus ?thesis
      unfolding trans_MapOps_def trans_MapOps_lookup_def trans_MapOps_update_def
      by (auto dest: map_prod_eq simp: trie_lookup_trie_update_with split: option.split split_split)
  qed
qed

(* A map for the agent actions. *)

type_synonym
  ('a, 'es, 'aAct, 'as) acts_trie
    = "(('a, 'es, 'as) BEState,
        (('a, 'es, 'as) BEState,
          (('a, 'es, 'as) BEState,
           (('a, 'es, 'as) BEState, 'aAct) trie) trie) trie) trie"

definition
  acts_MapOps_lookup :: "('a :: linorder, 'es :: linorder, 'aAct, 'as :: linorder) acts_trie
                       \<Rightarrow> ('a, 'es, 'as) SPRstate_rep
                       \<rightharpoonup> 'aAct"
where
  "acts_MapOps_lookup \<equiv> \<lambda>m (coEC, aEC).
     Option.bind (trie_lookup m (map fst (toList coEC)))
      (\<lambda>m. Option.bind (trie_lookup m (map snd (toList coEC)))
       (\<lambda>m. Option.bind (trie_lookup m (map fst (toList aEC)))
        (\<lambda>m. trie_lookup m (map snd (toList aEC)))))"

definition
  acts_MapOps_update :: "('a, 'es, 'as) SPRstate_rep
                       \<Rightarrow> 'aAct
                       \<Rightarrow> ('a :: linorder, 'es :: linorder, 'aAct, 'as :: linorder) acts_trie
                       \<Rightarrow> ('a, 'es, 'aAct, 'as) acts_trie"
where
  "acts_MapOps_update \<equiv> \<lambda>(coEC, aEC) pAct m.
     trie_update_with' (map fst (toList coEC)) m trie_empty
      (\<lambda>m. trie_update_with' (map snd (toList coEC)) m trie_empty
       (\<lambda>m. trie_update_with' (map fst (toList aEC)) m trie_empty
        (\<lambda>m. trie_update (map snd (toList aEC)) pAct m)))"

definition
  acts_MapOps :: "(('a :: linorder, 'es :: linorder, 'aAct, 'as :: linorder) acts_trie,
                   ('a, 'es, 'as) SPRstate_rep,
                   'aAct) MapOps"
where
  "acts_MapOps \<equiv>
     \<lparr> MapOps.empty = trie_empty,
       lookup = acts_MapOps_lookup,
       update = acts_MapOps_update \<rparr>"

lemma (in DetBroadcastEnvironment) acts_MapOps[intro, simp]:
  "MapOps spr_simAbs SPRdet.jkbpSEC acts_MapOps"
proof
  fix k show "MapOps.lookup acts_MapOps (MapOps.empty acts_MapOps) k = None"
    unfolding acts_MapOps_def acts_MapOps_lookup_def by auto
next
  fix e k k' M
  assume k: "spr_simAbs k \<in> SPRdet.jkbpSEC"
     and k': "spr_simAbs k' \<in> SPRdet.jkbpSEC"
  show "MapOps.lookup acts_MapOps (MapOps.update acts_MapOps k e M) k'
         = (if spr_simAbs k' = spr_simAbs k
             then Some e else MapOps.lookup acts_MapOps M k')"
  proof(cases "spr_simAbs k' = spr_simAbs k")
    case True hence "k = k'"
      using inj_onD[OF spr_simAbs_inj_on] k k' by (auto iff: prod_eqI)
    thus ?thesis
      unfolding acts_MapOps_def acts_MapOps_lookup_def acts_MapOps_update_def
      by (auto simp: trie_lookup_trie_update_with trie_lookup_trie_update split: option.split split_split)
  next
    case False thus ?thesis
      unfolding acts_MapOps_def acts_MapOps_lookup_def acts_MapOps_update_def
      by (auto dest: map_prod_eq simp: trie_lookup_trie_update_with trie_lookup_trie_update split: option.split split_split)
  qed
qed

sublocale DetBroadcastEnvironment < SPRdet!: Algorithm
            jkbp envInit envAction envTrans envVal
            envObs spr_sim spr_sim_rels spr_sim_val
            spr_simAbs spr_simObs spr_simInit spr_simTrans spr_simAction
            acts_MapOps trans_MapOps
  by (unfold_locales) blast+

definition
  SPRDetAutoDFS
where
  "SPRDetAutoDFS \<equiv> \<lambda>agents jkbp envInit envAction envTrans envVal envObsC envObs. \<lambda>a.
    alg_dfs acts_MapOps
            trans_MapOps
            (Algorithm.k_frontier_init envInit envObs (spr_simInit envInit envObsC envObs) a)
            (spr_simObs envObsC a)
            (spr_simTrans agents jkbp envAction envTrans envVal envObsC envObs a)
            (\<lambda>ss. spr_simAction jkbp envVal envObs ss a)"

definition
  mkSPRDetAuto
where
  "mkSPRDetAuto \<equiv> \<lambda>agents jkbp envInit envAction envTrans envVal envObsC envObs.
    mkAutoAlg acts_MapOps
              trans_MapOps
              (Algorithm.k_frontier_init envInit envObs (spr_simInit envInit envObsC envObs))
              (spr_simObs envObsC)
              (spr_simInit envInit envObsC envObs)
              (spr_simTrans agents jkbp envAction envTrans envVal envObsC envObs)
              (spr_simAction jkbp envVal envObs)"

lemma (in DetBroadcastEnvironment) mkSPRDetAuto_implements:
  "implements (mkSPRDetAuto agents jkbp envInit envAction envTrans envVal envObsC envObs)"
  using SPRdet.k_mkAutoAlg_implements
  unfolding mkSPRDetAuto_def mkAutoAlg_def
  by simp

(* This is the syntactic criterion mentioned in the Muddy Children example. *)

lemma (in Environment) jkbpDetI:
  assumes tC: "t \<in> jkbpC"
      and jkbpSynDet: "\<And>a. distinct (map guard (jkbp a))"
      and jkbpSemDet: "\<And>a gc gc'. \<lbrakk> gc \<in> set (jkbp a); gc' \<in> set (jkbp a); t \<in> jkbpC \<rbrakk>
                         \<Longrightarrow> guard gc = guard gc' \<or> \<not>(mkMC, t \<Turnstile> guard gc \<and> mkMC, t \<Turnstile> guard gc')"
  shows "length (jAction mkMC t a) \<le> 1"
proof -
  { fix a X
    assume "set X \<subseteq> set (jkbp a)"
       and "distinct (map guard X)"
    with tC have "length [ action gc . gc \<leftarrow> X, mkMC, t \<Turnstile> guard gc ] \<le> 1"
      by (induct X) (auto dest: jkbpSemDet) }
  from this[OF subset_refl jkbpSynDet] show ?thesis
    unfolding jAction_def by simp
qed

end

