
(*
 * Knowledge-based programs.
 * (C)opyright 2011, Peter Gammie, peteg42 at gmail.com.
 * License: BSD
 *)

theory SPRViewSingle
imports KBPsAlg List_local ODList
  "~~/src/HOL/Library/Mapping" "~~/src/HOL/Library/AssocList" Trie
begin


section{*Perfect Recall for a Single Agent*}


locale SingleAgentEnvironment =
  Environment jkbp envInit envAction envTrans envVal envObs
    for jkbp :: "'a \<Rightarrow> ('a, 'p, 'pAct) KBP"
    and envInit :: "('s :: {finite, linorder}) list"

    and envAction :: "'s \<Rightarrow> 'eAct list"
    and envTrans :: "'eAct \<Rightarrow> ('a \<Rightarrow> 'pAct) \<Rightarrow> 's \<Rightarrow> 's"
    and envVal :: "'s \<Rightarrow> 'p \<Rightarrow> bool"

    and envObs :: "'a \<Rightarrow> 's \<Rightarrow> 'obs"

+ fixes agent :: "'a"
  assumes envSingleAgent: "a = agent"
begin

definition spr_jview_abs :: "'s Trace \<Rightarrow> 's set" where
  "spr_jview_abs t \<equiv> tLast ` equiv_class agent (spr_jview agent t)"


definition spr_sim_single :: "'s Trace \<Rightarrow> 's set \<times> 's" where
  "spr_sim_single t \<equiv> (spr_jview_abs t, tLast t)"


type_synonym (in -) 's SPRsimState = "'s set \<times> 's"

lemma spr_jview_absI[elim]:
  "\<lbrakk> t' \<in> jkbpC; spr_jview a t' = spr_jview a t; v = tLast t' \<rbrakk>
    \<Longrightarrow> v \<in> spr_jview_abs t"
  unfolding spr_jview_abs_def
  using envSingleAgent[where a=a] by blast

lemma spr_jview_abs_tLastD[simp]:
  "v \<in> spr_jview_abs t \<Longrightarrow> envObs a v = envObs a (tLast t)"
  unfolding spr_jview_abs_def
  using envSingleAgent[where a=a] by auto

lemma spr_jview_abs_conv:
  "v \<in> spr_jview_abs t
    \<longleftrightarrow> (\<exists>t'. t' \<in> jkbpC \<and> spr_jview a t' = spr_jview a t \<and> v = tLast t')"
  unfolding spr_jview_abs_def
  using envSingleAgent[where a=a] by blast

lemma spr_jview_abs_eq[dest]:
  "spr_jview a t = spr_jview a t' \<Longrightarrow> spr_jview_abs t = spr_jview_abs t'"
  unfolding spr_jview_abs_def
  using envSingleAgent[where a=a] by auto

lemma spr_jview_abs_refl[intro]:
  "t \<in> jkbpC \<Longrightarrow> tLast t \<in> spr_jview_abs t"
  unfolding spr_jview_abs_def
  using envSingleAgent[where a=a] by auto

lemma spr_sim_single_FIXME:
  "\<lbrakk> spr_sim_single t = (vss, v); t \<in> jkbpC \<rbrakk> \<Longrightarrow> v \<in> vss"
  unfolding spr_sim_single_def_raw by auto

lemma spr_sim_single_simps[simp]:
  "fst (spr_sim_single t) = spr_jview_abs t"
  unfolding spr_sim_single_def_raw by simp

definition
  spr_sim_single_rels :: "'a \<Rightarrow> 's SPRsimState Relation"
where
  "spr_sim_single_rels \<equiv> \<lambda>a. { ((U, u), (V, v)) |U u V v.
                         U = V \<and> u \<in> U \<and> v \<in> V \<and> envObs a u = envObs a v }"

definition
  spr_sim_single_val :: "'s SPRsimState \<Rightarrow> 'p \<Rightarrow> bool"
where
  "spr_sim_single_val \<equiv> envVal \<circ> snd"

lemma spr_sim_singleVal[iff]:
  "spr_sim_single_val (spr_sim_single t) = envVal (tLast t)"
  unfolding spr_sim_single_def_raw spr_sim_single_val_def by simp

abbreviation "spr_sim_single_kripke_structure \<equiv> mkKripke (spr_sim_single ` jkbpC) spr_sim_single_rels spr_sim_single_val"

lemma spr_sim_single[intro, simp]:
  "sim mkMC spr_sim_single_kripke_structure spr_sim_single"
proof
  show "sim_f mkMC spr_sim_single_kripke_structure spr_sim_single"
    unfolding spr_sim_single_rels_def spr_sim_single_def_raw mkKripke_def mkM_def
    by (rule) auto
  show "sim_r mkMC spr_sim_single_kripke_structure spr_sim_single"
  proof
    fix a t v'
    let ?t' = "spr_sim_single t"
    assume t: "t \<in> worlds mkMC"
       and tv': "(?t', v') \<in> relations spr_sim_single_kripke_structure a"
    from tv' obtain s
      where vv': "v' = (spr_jview_abs t, s)"
        and st: "s \<in> spr_jview_abs t"
      unfolding spr_sim_single_rels_def spr_sim_single_def_raw mkKripke_def mkM_def
      by auto
    from st obtain v
      where "v \<in> jkbpC"
        and "spr_jview a v = spr_jview a t"
        and "tLast v = s"
      by (auto iff: spr_jview_abs_conv)
    with t vv'
    have "(t, v) \<in> relations mkMC a"
     and "spr_sim_single v = v'"
      unfolding spr_sim_single_rels_def spr_sim_single_def_raw mkKripke_def mkM_def
      by auto
    thus "\<exists>v. (t, v) \<in> relations mkMC a \<and> spr_sim_single v = v'" by blast
  qed
qed auto

abbreviation
  "jkbpCSn n \<equiv> spr_sim_single ` jkbpCn n"

abbreviation
  "jkbpCS \<equiv> spr_sim_single ` jkbpC"

abbreviation
  "mkMCSn n \<equiv> mkKripke (jkbpCSn n) spr_sim_single_rels spr_sim_single_val"

abbreviation
  "mkMCS \<equiv> mkKripke jkbpCS spr_sim_single_rels spr_sim_single_val"


type_synonym (in -) 's SPRsimState_rep = "'s odlist"

fun (in -)
  eval :: "('s \<Rightarrow> 'p \<Rightarrow> bool) \<Rightarrow> ('s :: linorder) odlist \<Rightarrow> ('a, 'p) Kform \<Rightarrow> 's odlist"
where
  "eval val X (Kprop p)      = ODList.filter (\<lambda>s. val s p) X"
| "eval val X (Knot \<phi>)       = ODList.difference X (eval val X \<phi>)"
| "eval val X (Kand \<phi> \<psi>)     = ODList.intersection (eval val X \<phi>) (eval val X \<psi>)"
| "eval val X (\<^bold>K\<^sub>a \<phi>)         = (if eval val X \<phi> = X then X else ODList.empty)"

declare eval.simps [code]

definition (in -)
  spr_sim_singleInit :: "'s list \<Rightarrow> ('a \<Rightarrow> 's \<Rightarrow> 'obs)
                     \<Rightarrow> 'a \<Rightarrow> 'obs \<Rightarrow> ('s :: linorder) SPRsimState_rep"
where
 [code]: "spr_sim_singleInit envInit envObs \<equiv> \<lambda>a iobs.
             ODList.fromList
               [ s. s \<leftarrow> envInit, envObs a s = iobs ]"

definition (in -)
  spr_sim_singleObs :: "('a \<Rightarrow> 's \<Rightarrow> 'obs)
               \<Rightarrow> 'a \<Rightarrow> ('s :: linorder) SPRsimState_rep \<Rightarrow> 'obs"
where
  [code]: "spr_sim_singleObs envObs \<equiv> \<lambda>a. envObs a \<circ> ODList.hd"

definition (in -)
  spr_sim_singleAction :: "('a, 'p, 'pAct) KBP \<Rightarrow> ('s \<Rightarrow> 'p \<Rightarrow> bool)
                     \<Rightarrow> ('s :: linorder) SPRsimState_rep \<Rightarrow> 'a \<Rightarrow> 'pAct list"
where
  [code]: "spr_sim_singleAction kbp envVal \<equiv> \<lambda>X a.
             [ action gc. gc \<leftarrow> kbp, eval envVal X (guard gc) \<noteq> ODList.empty ]"

definition (in -)
  spr_trans :: "('a, 'p, 'pAct) KBP
              \<Rightarrow> ('s \<Rightarrow> 'eAct list)
              \<Rightarrow> ('eAct \<Rightarrow> ('a \<Rightarrow> 'pAct) \<Rightarrow> 's \<Rightarrow> 's)
              \<Rightarrow> ('s \<Rightarrow> 'p \<Rightarrow> bool)
              \<Rightarrow> 'a \<Rightarrow> ('s :: linorder) SPRsimState_rep \<Rightarrow> 's list"
where
  [code]: "spr_trans kbp envAction envTrans val \<equiv> \<lambda>a X.
               [ envTrans eact (\<lambda>a'. aact) s.
                   s \<leftarrow> ODList.toList X, eact \<leftarrow> envAction s, aact \<leftarrow> spr_sim_singleAction kbp val X a ]"

abbreviation (in -)
  "envObs_rel \<equiv> \<lambda>envObs. {(s, s'). envObs s' = envObs s}"

lemma (in -) envObs_rel_equiv:
  "equiv UNIV (envObs_rel envObs)"
  by (rule equivI) (auto intro: refl_onI symI transI)

definition (in -)
  spr_sim_singleTrans :: "('a, 'p, 'pAct) KBP
                 \<Rightarrow> ('s \<Rightarrow> 'eAct list)
                 \<Rightarrow> ('eAct \<Rightarrow> ('a \<Rightarrow> 'pAct) \<Rightarrow> 's \<Rightarrow> 's)
                 \<Rightarrow> ('s \<Rightarrow> 'p \<Rightarrow> bool)
                 \<Rightarrow> ('a \<Rightarrow> 's \<Rightarrow> 'obs)
                 \<Rightarrow> 'a \<Rightarrow> ('s :: linorder) SPRsimState_rep \<Rightarrow> 's SPRsimState_rep list"
where
  [code]: "spr_sim_singleTrans kbp envAction envTrans val envObs \<equiv> \<lambda>a X.
              map ODList.fromList
                  (partition (envObs_rel (envObs a)) (spr_trans kbp envAction envTrans val a X))"

(* Define a bunch of locale-local abbreviations. *)

abbreviation
  spr_sim_singleInit :: "'a \<Rightarrow> 'obs \<Rightarrow> 's SPRsimState_rep"
where
  "spr_sim_singleInit \<equiv> SPRViewSingle.spr_sim_singleInit envInit envObs"

abbreviation
  spr_sim_singleObs :: "'a \<Rightarrow> 's SPRsimState_rep \<Rightarrow> 'obs"
where
  "spr_sim_singleObs \<equiv> SPRViewSingle.spr_sim_singleObs envObs"

abbreviation
  spr_sim_singleAction :: "'s SPRsimState_rep \<Rightarrow> 'a \<Rightarrow> 'pAct list"
where
  "spr_sim_singleAction \<equiv> SPRViewSingle.spr_sim_singleAction (jkbp agent) envVal"

abbreviation
  spr_trans :: "'a \<Rightarrow> 's SPRsimState_rep \<Rightarrow> 's list"
where
  "spr_trans \<equiv> SPRViewSingle.spr_trans (jkbp agent) envAction envTrans envVal"

abbreviation
  spr_sim_singleTrans :: "'a \<Rightarrow> 's SPRsimState_rep \<Rightarrow> 's SPRsimState_rep list"
where
  "spr_sim_singleTrans \<equiv> SPRViewSingle.spr_sim_singleTrans (jkbp agent) envAction envTrans envVal envObs"

definition
  spr_sim_singleAbs :: "'s SPRsimState_rep \<Rightarrow> 's SPRsimState set"
where
  "spr_sim_singleAbs \<equiv> \<lambda>ss. { (toSet ss, s) |s. s \<in> toSet ss }"

lemma spr_sim_singleAbs_inj[intro, simp]:
  "inj spr_sim_singleAbs"
  apply (rule injI)
  unfolding spr_sim_singleAbs_def
  apply (subgoal_tac "toSet x = toSet y")
  apply auto
  using toSet_inj
  apply (erule injD)
  done

lemma FIXME_ec_spr_sim_single[simp]:
  assumes ec: "spr_sim_singleAbs ec = spr_sim_single ` equiv_class agent (spr_jview agent t)"
  shows "toSet ec = fst (spr_sim_single t)" (is "?lhs = ?rhs")
proof
  show "?lhs \<subseteq> ?rhs"
  proof
    fix x assume x: "x \<in> toSet ec"
    hence "(toSet ec, x) \<in> spr_sim_singleAbs ec"
      unfolding spr_sim_singleAbs_def by simp
    with ec have "(toSet ec, x) \<in> spr_sim_single ` equiv_class agent (spr_jview agent t)" by simp
    with x show "x \<in> ?rhs"
      unfolding spr_sim_single_def_raw spr_jview_abs_def by auto
  qed
next
  show "?rhs \<subseteq> ?lhs"
  proof
    fix x assume x: "x \<in> fst (spr_sim_single t)"
    with ec show "x \<in> ?lhs"
      unfolding spr_sim_singleAbs_def spr_sim_single_def_raw spr_jview_abs_def by auto
  qed
qed

(* FIXME syntactic. *)
lemma FIXME_ec_spr_sim_single_syn[simp]:
  assumes ec: "spr_sim_singleAbs ec = spr_sim_single ` equiv_class agent (spr_jview agent t)"
  shows "set (toList ec) = fst (spr_sim_single t)"
  using FIXME_ec_spr_sim_single[OF ec] unfolding toSet_def by simp

lemma spr_sim_singleAbs_list:
  "spr_sim_singleAbs ` fromList ` X = (\<lambda>ss. { (ss, s) |s. s \<in> ss }) ` set ` X"
  unfolding spr_sim_singleAbs_def Set.image_def by auto

lemma spr_sim_singleInit':
  assumes "iobs \<in> envObs a ` set envInit"
  shows "spr_sim_singleAbs (spr_sim_singleInit a iobs)
       = spr_sim_single ` equiv_class a (tInit iobs)"
  using assms
  unfolding spr_sim_singleInit_def
  using envSingleAgent[where a=a]
  unfolding spr_sim_singleAbs_def spr_sim_single_def_raw spr_jview_abs_def
  apply (auto iff: spr_jview_def)
   apply (rule_tac x="tInit s" in image_eqI)
    apply (auto iff: spr_jview_def)[1]
    apply (rule_tac x="tInit xa" in image_eqI)
    apply auto[1]
   apply simp
   apply simp
  apply (rule_tac x="tInit xa" in image_eqI)
  apply auto
  done

lemma spr_sim_singleInit:
  "\<forall>a iobs. iobs \<in> envObs a ` set envInit
     \<longrightarrow> spr_sim_singleAbs (spr_sim_singleInit a iobs)
       = spr_sim_single ` equiv_class a (tInit iobs)"
  using spr_sim_singleInit' by blast

lemma spr_sim_singleObs_aux:
  assumes tC: "t \<in> jkbpC"
      and ec: "spr_sim_singleAbs ec = spr_sim_single ` equiv_class agent (spr_jview agent t)"
  obtains x xs where "toList ec = x # xs" and "envObs a x = envObs a (tLast t)"
proof -
  assume E: "\<And>x xs. \<lbrakk> toList ec = x # xs; envObs a x = envObs a (tLast t) \<rbrakk> \<Longrightarrow> thesis"
  from tC ec have "spr_sim_single t \<in> spr_sim_singleAbs ec" by auto
  hence "\<exists>x xs. toList ec = x # xs \<and> envObs a x = envObs a (tLast t)"
    unfolding spr_sim_single_def_raw spr_sim_singleAbs_def
    apply (cases ec)
     apply (simp add: toSet_def)
    apply (simp add: toList_fromList toSet_def)
    done
  with E show thesis by blast
qed

lemma spr_sim_singleObs'[iff]:
  assumes tC: "t \<in> jkbpC"
      and ec: "spr_sim_singleAbs ec = spr_sim_single ` equiv_class a (spr_jview a t)"
  shows "spr_sim_singleObs a ec = envObs a (tLast t)"
proof -
  from ec have ec': "spr_sim_singleAbs ec = spr_sim_single ` equiv_class agent (spr_jview agent t)"
    by (simp only: envSingleAgent[where a=a])
  show ?thesis
    apply (rule spr_sim_singleObs_aux[OF tC ec'])
    unfolding spr_sim_singleObs_def
    using envSingleAgent[where a=a]
    apply simp
    apply (cut_tac y=x and ys=xs in hd_toList[where xs=ec])
    apply auto
    done
qed

lemma spr_sim_singleObs:
  "\<forall>a ec t. t \<in> jkbpC \<and> spr_sim_singleAbs ec = spr_sim_single ` equiv_class a (spr_jview a t)
    \<longrightarrow> spr_sim_singleObs a ec = envObs a (tLast t)"
  using spr_sim_singleObs' by blast

definition
  spr_rep_rels :: "'a \<Rightarrow> 's \<times> 's \<Rightarrow> bool"
where
  "spr_rep_rels \<equiv> \<lambda>a. { (s, s'). envObs a s' = envObs a s }"

definition
  spr_rep_ks :: "'s set \<Rightarrow> ('a, 'p, 's) KripkeStructure"
where
  "spr_rep_ks \<equiv> \<lambda>X. mkKripke X spr_rep_rels envVal"

lemma spr_rep_ks_kripke[intro, simp]: "kripke (spr_rep_ks X)"
  unfolding spr_rep_ks_def by (rule kripkeI) simp

lemma spr_rep_ks_S5n[intro, simp]: "S5n (spr_rep_ks X)"
  unfolding spr_rep_ks_def spr_rep_rels_def
  apply (rule S5nI, rule equivI)
  apply (auto intro: refl_onI symI transI)
  done

lemma spr_rep_ks_simps[simp]:
  "worlds (spr_rep_ks X) = X"
  "\<lbrakk> (s, s') \<in> relations (spr_rep_ks X) a \<rbrakk> \<Longrightarrow> envObs a s = envObs a s'"
  "valuation (spr_rep_ks X) = envVal"
  unfolding spr_rep_ks_def spr_rep_rels_def by auto

lemma eval_ec_subseteq:
  shows "toSet (eval envVal ec \<phi>) \<subseteq> toSet ec"
  by (induct \<phi>) auto

lemma FIXME_subset_diff:
 "\<lbrakk> X \<subseteq> Y; X \<noteq> Y \<rbrakk> \<Longrightarrow> \<exists>x. x \<in> Y - X"
  by auto

lemma eval_models_aux:
  assumes ec: "spr_sim_singleAbs ec = spr_sim_single ` equiv_class agent (spr_jview agent t)"
      and s: "s \<in> toSet ec"
  shows "s \<in> toSet (eval envVal ec \<phi>) \<longleftrightarrow> spr_rep_ks (toSet ec), s \<Turnstile> \<phi>"
using s
proof(induct \<phi> arbitrary: s)
  case (Knows a \<phi> s) with ec envSingleAgent[where a=a] show ?case
    apply auto
    apply (simp only: inj_eq[OF toSet_inj, symmetric])
    apply (drule FIXME_subset_diff[OF eval_ec_subseteq])
    apply clarsimp
    apply (rule_tac x=x in bexI)
    apply auto
    unfolding spr_rep_ks_def spr_rep_rels_def
    apply auto
    done
qed simp_all

lemma eval_all_or_nothing:
  assumes subj_phi: "subjective agent \<phi>"
  shows "toSet (eval envVal ec \<phi>) = {} \<or> toSet (eval envVal ec \<phi>) = toSet ec"
  using subj_phi by (induct \<phi> rule: subjective.induct) auto

lemma eval_models:
  assumes ec: "spr_sim_singleAbs ec = spr_sim_single ` equiv_class agent (spr_jview agent t)"
      and subj: "subjective agent \<phi>"
      and s: "s \<in> toSet ec"
  shows "toSet (eval envVal ec \<phi>) \<noteq> {} \<longleftrightarrow> spr_rep_ks (toSet ec), s \<Turnstile> \<phi>"
  using eval_models_aux[OF ec s, symmetric] eval_all_or_nothing[OF subj] s
  by auto

lemma FIXME_eval_models:
  assumes tC: "t \<in> jkbpC"
      and ec: "spr_sim_singleAbs ec = spr_sim_single ` equiv_class agent (spr_jview agent t)"
  shows "set (spr_sim_singleAction ec agent)
       = set (jAction (spr_rep_ks (toSet ec)) (tLast t) agent)"
  unfolding spr_sim_singleAction_def jAction_def
  apply clarsimp
  apply rule
   apply clarsimp
   apply (rule_tac x=a in bexI)
    apply simp
   apply clarsimp
   apply (subst eval_models[symmetric])
    using tC ec subj
    apply simp_all
   apply (erule spr_jview_absI[where a=agent])
    apply simp
    apply simp
    apply clarsimp
    apply (simp only: toSet_empty[symmetric] injD[OF toSet_inj])
    apply simp
  apply clarsimp
  apply (rule_tac x=a in bexI)
   apply simp
  apply clarsimp
  apply (drule arg_cong[where f="toSet"])
  apply (simp only: toSet_empty)
  apply (subst (asm) eval_models[THEN arg_cong[where f=Not], simplified])
  apply auto
  done

abbreviation
  mkMCSt_spr :: "'s Trace \<Rightarrow> ('a, 'p, 's SPRsimState) KripkeStructure"
where
  "mkMCSt_spr t \<equiv> mkKripke (spr_sim_single ` equiv_class agent (spr_jview agent t)) spr_sim_single_rels spr_sim_single_val"

lemma jkbpCSt_jkbpCS_subset:
  "spr_sim_single ` equiv_class agent (spr_jview agent t) \<subseteq> spr_sim_single ` jkbpC"
  by auto

(* Connect the simulated temporal slice up to the computational Kripke
structure. Use a simulation for this purpose. *)

definition
  spr_rep_sim :: "'s SPRsimState \<Rightarrow> 's"
where
  "spr_rep_sim \<equiv> snd"

lemma FIXME_spr_sim_singleRep_sim_simps[simp]:
  "spr_rep_sim ` spr_sim_single ` T = tLast ` T"
  "spr_rep_sim (spr_sim_single t) = tLast t"
  unfolding spr_rep_sim_def spr_sim_single_def_raw Set.image_def by auto

lemma spr_rep_sim:
  assumes tC: "t \<in> jkbpC"
  shows "sim (mkMCSt_spr t)
             ((spr_rep_ks \<circ> fst) (spr_sim_single t))
             spr_rep_sim" (is "sim ?M ?M' ?f")
proof
  show "sim_range ?M ?M' ?f"
  proof
    show "worlds ?M' = ?f ` worlds ?M"
      unfolding spr_sim_single_def_raw spr_rep_sim_def spr_rep_ks_def spr_jview_abs_def Set.image_def
      by auto
  next
    fix a
    show "relations ?M' a \<subseteq> worlds ?M' \<times> worlds ?M'"
      unfolding spr_sim_single_def_raw spr_rep_sim_def spr_rep_ks_def by simp
  qed
next
  show "sim_val ?M ?M' ?f"
    unfolding spr_sim_single_def_raw spr_sim_single_val_def spr_rep_ks_def spr_rep_sim_def by auto
next
  from tC
  show "sim_f ?M ?M' ?f"
    unfolding spr_sim_single_def_raw spr_sim_single_val_def spr_rep_ks_def spr_rep_sim_def
    apply -
    apply rule
    apply (cut_tac a=a in envSingleAgent)
    apply (auto iff: spr_sim_single_def_raw spr_rep_rels_def)
    apply (rule spr_tLast)
    apply auto
    done
next
  show "sim_r ?M ?M' ?f"
    unfolding spr_sim_single_def_raw spr_sim_single_val_def spr_rep_ks_def spr_rep_sim_def
    apply -
    apply rule
    apply (cut_tac a=a in envSingleAgent)
    unfolding spr_jview_abs_def spr_sim_single_def_raw spr_rep_rels_def spr_sim_single_rels_def Set.image_def
    apply auto
    done
qed

(* Connect the simulated temporal slice up to the set of all simulated
traces. *)

lemma FIXME_spr_submodel_aux:
  assumes tC: "t \<in> jkbpC"
      and s: "s \<in> worlds (mkMCSt_spr t)"
  shows "sub_model mkMCS s = sub_model (mkMCSt_spr t) s"
proof(rule sub_model_subset[where T="spr_sim_single ` equiv_class agent (spr_jview agent t)"])
  fix a
  let ?X = "spr_sim_single ` equiv_class agent (spr_jview agent t)"
  show "relations mkMCS a \<inter> ?X \<times> ?X
      = relations (mkMCSt_spr t) a \<inter> ?X \<times> ?X"
    by (simp add: Int_ac Int_absorb1
                  relation_mono[OF jkbpCSt_jkbpCS_subset jkbpCSt_jkbpCS_subset])
next
  let ?X = "spr_sim_single ` equiv_class agent (spr_jview agent t)"
  from s show "(\<Union>a. relations (mkMCSt_spr t) a)\<^sup>* `` {s} \<subseteq> ?X"
    apply (clarsimp simp del: mkKripke_simps)
    apply (erule kripke_rels_trc_worlds)
    apply auto
    done
next
  let ?Y = "equiv_class agent (spr_jview agent t)"
  let ?X = "spr_sim_single ` ?Y"
  from s obtain t'
    where st': "s = spr_sim_single t'"
      and t'C: "t' \<in> jkbpC"
      and t'O: "spr_jview agent t = spr_jview agent t'"
    by fastsimp
  { fix t''
    assume tt': "(t', t'') \<in> (\<Union>a. relations mkMC a)\<^sup>*"
    from t'C tt' have t''C: "t'' \<in> jkbpC"
      by - (erule kripke_rels_trc_worlds, simp_all)
    from tt' t'O have t''O: "spr_jview agent t = spr_jview agent t''"
      apply induct
      unfolding mkM_def
      apply auto
      apply (cut_tac a=a in envSingleAgent)
      apply simp
      done
    from t''C t''O have "t'' \<in> ?Y" by simp }
  hence "(\<Union>a. relations mkMC a)\<^sup>* `` {t'} \<subseteq> ?Y"
    by clarsimp
  hence "spr_sim_single ` ((\<Union>a. relations mkMC a)\<^sup>* `` {t'}) \<subseteq> ?X"
    by (rule image_mono)
  with st' t'C
  show "(\<Union>a. relations mkMCS a)\<^sup>* `` {s} \<subseteq> ?X"
    using sim_trc_commute[OF mkM_kripke spr_sim_single, where t=t'] by simp
qed (insert s, auto)

lemma spr_sim_singleAction':
  assumes tC: "t \<in> jkbpC"
      and ec: "spr_sim_singleAbs ec = spr_sim_single ` equiv_class a (spr_jview a t)"
  shows "set (spr_sim_singleAction ec a) = set (jAction mkMC t a)" (is "?lhs = ?rhs")
proof -
  from ec have ec': "spr_sim_singleAbs ec = spr_sim_single ` equiv_class agent (spr_jview agent t)" by (simp only: envSingleAgent[where a=a])
  have "?lhs = set (spr_sim_singleAction ec agent)" by (simp only: envSingleAgent[where a=a])
  also from tC ec' have "... = set (jAction (spr_rep_ks (toSet ec)) (tLast t) agent)"
    by (rule FIXME_eval_models)
  also from tC ec' have "... = set (jAction (mkMCSt_spr t) (spr_sim_single t) agent)"
    by (simp add: simulation_jAction_eq[OF _ spr_rep_sim])
  also from tC have "... = set (jAction mkMCS (spr_sim_single t) agent)"
    using sub_model_jAction_eq[OF FIXME_spr_submodel_aux[OF tC, where s="spr_sim_single t"], where w'="spr_sim_single t"]
          sub_model_world_refl[where w="spr_sim_single t" and M="mkMCSt_spr t"]
    by simp
  also from tC have "... = set (jAction mkMC t agent)"
    by (simp add: simulation_jAction_eq[OF _ spr_sim_single])
  finally show ?thesis by (simp only: envSingleAgent[where a=a])
qed

lemma spr_sim_singleAction:
  "\<forall>a ec t. t \<in> jkbpC \<and> spr_sim_singleAbs ec = spr_sim_single ` equiv_class a (spr_jview a t)
    \<longrightarrow> set (spr_sim_singleAction ec a) = set (jAction mkMC t a)"
  using spr_sim_singleAction' by blast

lemma FIXME_spr_trans:
  assumes tC: "t \<in> jkbpC"
      and ec: "spr_sim_singleAbs ec = spr_sim_single ` equiv_class agent (spr_jview agent t)"
  shows "set (spr_trans agent ec)
       = { s |t' s. t' \<leadsto> s \<in> jkbpC \<and> spr_jview agent t' = spr_jview agent t }" (is "?lhs = ?rhs")
proof
  show "?lhs \<subseteq> ?rhs"
  proof
    fix x assume x: "x \<in> ?lhs"
    with assms show "x \<in> ?rhs"
      unfolding spr_trans_def
      apply (clarsimp simp del: split_paired_Ex split_paired_All)
      apply (frule FIXME_ec_spr_sim_single)
      unfolding toSet_def
      apply clarsimp

      apply (simp only: spr_jview_abs_conv[where a=agent])
      apply clarify

      apply (rule_tac x="t'" in exI)
      apply simp
      apply (rule_tac n="Suc (tLength t')" in jkbpCn_jkbpC_inc)
      apply (auto iff: Let_def simp del: split_paired_Ex split_paired_All)

      apply (rule_tac x="aa" in exI)
      apply (rule_tac x="\<lambda>a'. aact" in exI)
      apply auto
      apply (subst envSingleAgent)
      apply (simp add: spr_sim_singleAction'[where a=agent])
      apply (subst jkbpC_jkbpCn_jAction_eq[symmetric])
      apply auto
      apply (subst S5n_jAction_eq[where w'=t])
      apply simp_all
      unfolding mkM_def
      apply simp
      done
  qed
next
  show "?rhs \<subseteq> ?lhs"
  proof
    fix s assume s: "s \<in> ?rhs"
    then obtain t'
      where t'sC: "t' \<leadsto> s \<in> jkbpC"
        and tt': "spr_jview agent t' = spr_jview agent t"
      by blast
    from t'sC have t'Cn: "t' \<in> jkbpCn (tLength t')" by blast
    from t'sC obtain eact aact
      where eact: "eact \<in> set (envAction (tLast t'))"
        and aact: "\<forall>a. aact a \<in> set (jAction (mkM (jkbpCn (tLength t'))) t' a)"
        and s: "s = envTrans eact aact (tLast t')"
      using jkbpC_tLength_inv[where t="t' \<leadsto> s" and n="Suc (tLength t')"]
      by (auto iff: Let_def)
    from tC ec s eact aact tt' t'sC
    show "s \<in> ?lhs"
      unfolding spr_trans_def
      apply (clarsimp)
      apply (rule bexI[where x="tLast t'"])
      apply (rule bexI[where x=eact])
      apply simp_all
       prefer 2
       apply (blast intro: spr_jview_absI)
      apply (simp add: spr_sim_singleAction'[where a=agent])
      apply (rule image_eqI[where x="aact agent"])
       apply (subgoal_tac "(\<lambda>a'. aact agent) = aact")
        apply simp
       apply (rule ext)
       apply (cut_tac a=a' in envSingleAgent)
       apply simp
      apply (erule allE[where x=agent])
      apply (subst jkbpC_jkbpCn_jAction_eq)
      apply auto
      apply (subst S5n_jAction_eq[where w=t and w'=t'])
        apply simp
       apply (unfold mkM_def)[1]
       apply simp
       apply (auto dest: spr_sync)
      done
  qed
qed

lemma spr_sim_singleTrans':
  assumes tC: "t \<in> jkbpC"
      and ec: "spr_sim_singleAbs ec = spr_sim_single ` equiv_class a (spr_jview a t)"
  shows "spr_sim_singleAbs ` set (spr_sim_singleTrans a ec)
      = { spr_sim_single ` equiv_class a (spr_jview a (t' \<leadsto> s))
          |t' s. t' \<leadsto> s \<in> jkbpC \<and> spr_jview a t' = spr_jview a t}" (is "?lhs a = ?rhs a")
proof -
  from ec have ec': "spr_sim_singleAbs ec = spr_sim_single ` equiv_class agent (spr_jview agent t)" by (simp only: envSingleAgent[where a=a])
  from ec' have "?lhs agent = ?rhs agent"
    unfolding spr_sim_singleTrans_def
    apply clarsimp
    apply (simp only: spr_sim_singleAbs_list)
    apply (subst partition[OF envObs_rel_equiv])
     apply simp
    apply (simp only: FIXME_spr_trans[OF tC ec'])
    apply clarsimp
    apply rule

     (* left to right *)

     apply clarsimp
     apply (erule quotientE)
     apply clarsimp
     apply (rule_tac x=t' in exI)
     apply (rule_tac x=x in exI)
     apply clarsimp
     apply rule
      apply clarsimp
      apply (rule_tac x="t'a \<leadsto> s" in image_eqI)
       apply (unfold spr_sim_single_def_raw spr_jview_abs_def)[1]
       apply clarsimp
       apply (auto iff: spr_jview_def)[1]
        apply (rule_tac x="t'c \<leadsto> xa" in image_eqI)
         apply simp
        apply simp
       apply (simp add: spr_jview_def)
     apply clarsimp
     apply (frule spr_jview_tStep_eq_inv)
     apply clarsimp
     apply (rule_tac x=s' in exI)
     apply (unfold spr_sim_single_def_raw spr_jview_abs_def)[1]
     apply clarsimp
     apply (auto iff: spr_jview_def)[1]
      apply (rule_tac x="t'b \<leadsto> xa" in image_eqI)
       apply simp
       apply simp

     (* right to left *)

     apply clarsimp
     apply (rule_tac x="spr_jview_abs (t' \<leadsto> s)" in image_eqI)
      apply rule
       apply clarsimp
       apply (frule spr_jview_tStep_eq_inv)
       apply clarsimp
       apply (unfold spr_sim_single_def_raw)[1]
       apply clarsimp
       apply rule
        apply (erule spr_jview_abs_eq)
       apply (erule spr_jview_absI[where a=agent]) back
        apply simp
       apply simp
      apply clarsimp
      apply (simp only: spr_jview_abs_conv[where a=agent])
      apply clarsimp
      apply (frule spr_jview_tStep_eq_inv)
      apply clarsimp
      apply (rule_tac x="t'' \<leadsto> s'" in image_eqI)
       apply (unfold spr_sim_single_def_raw)[1]
       apply clarsimp
       apply blast
      apply blast
     apply (rule_tac x=s in quotientI2)
      apply auto[1]
     apply rule
      apply clarsimp
      apply rule
       apply blast
      apply (cut_tac v=x and t="t' \<leadsto> s" in spr_jview_abs_conv[where a=agent])
      apply clarsimp
      apply (frule spr_jview_tStep_eq_inv)
      apply clarsimp
      apply (rule_tac x=t'' in exI)
      apply (simp add: Let_def spr_jview_def)
     apply clarsimp
     apply (erule spr_jview_absI[where a=agent]) back back
     apply (auto iff: spr_jview_def)
     done
   thus "?lhs a = ?rhs a" by (simp only: envSingleAgent[where a=a])
qed

lemma spr_sim_singleTrans:
  "\<forall>a ec t. t \<in> jkbpC \<and> spr_sim_singleAbs ec = spr_sim_single ` equiv_class a (spr_jview a t)
    \<longrightarrow> spr_sim_singleAbs ` set (spr_sim_singleTrans a ec)
      = { spr_sim_single ` equiv_class a (spr_jview a (t' \<leadsto> s))
          |t' s. t' \<leadsto> s \<in> jkbpC \<and> spr_jview a t' = spr_jview a t}"
  using spr_sim_singleTrans' by blast

end (* context *)

sublocale SingleAgentEnvironment < SPRsingle!: SimEnvironment
            jkbp envInit envAction envTrans envVal
            envObs spr_sim_single spr_sim_single_rels spr_sim_single_val
            spr_sim_singleAbs spr_sim_singleObs spr_sim_singleInit spr_sim_singleTrans spr_sim_singleAction

  apply unfold_locales

  apply simp

  apply (rule spr_sim_singleInit)
  apply (rule spr_sim_singleObs)
  apply (rule spr_sim_singleAction)
  apply (rule spr_sim_singleTrans)
  done

definition
  trans_MapOps_lookup :: "('s, ('obs, 's odlist) mapping) trie
                        \<Rightarrow> ('s :: linorder) odlist \<times> 'obs \<rightharpoonup> 's odlist"
where
  "trans_MapOps_lookup \<equiv> \<lambda>m k.
     Option.bind (trie_odlist_lookup m (fst k)) (\<lambda>m'. Mapping.lookup m' (snd k))"

definition
  trans_MapOps_update :: "'s odlist \<times> 'obs \<Rightarrow> ('s :: linorder) odlist
                        \<Rightarrow> ('s, ('obs, 's odlist) mapping) trie
                        \<Rightarrow> ('s, ('obs, 's odlist) mapping) trie"
where
  "trans_MapOps_update \<equiv> \<lambda>k v m.
     trie_odlist_update_with (fst k) m Mapping.empty
      (\<lambda>m. Mapping.update (snd k) v m)"

definition
  trans_MapOps :: "(('s :: linorder, ('obs, 's odlist) mapping) trie, 's odlist \<times> 'obs, 's odlist) MapOps"
where
  "trans_MapOps \<equiv>
     \<lparr> MapOps.empty = trie_empty,
       lookup = trans_MapOps_lookup,
       update = trans_MapOps_update \<rparr>"

(* FIXME repair jkbpSEC here *)

lemma (in SingleAgentEnvironment) trans_MapOps[intro, simp]:
  "MapOps (\<lambda>k. (spr_sim_singleAbs (fst k), snd k)) (jkbpSEC \<times> UNIV) trans_MapOps"
proof
  fix k show "MapOps.lookup trans_MapOps (MapOps.empty trans_MapOps) k = None"
    unfolding trans_MapOps_def trans_MapOps_lookup_def trie_odlist_lookup_def
    by (auto split: split_split)
next
  fix e k k' M
  assume k: "(spr_sim_singleAbs (fst k), snd k) \<in> jkbpSEC \<times> (UNIV :: 'z set)"
     and k': "(spr_sim_singleAbs (fst k'), snd k') \<in> jkbpSEC \<times> (UNIV :: 'z set)"
  show "MapOps.lookup trans_MapOps (MapOps.update trans_MapOps k e M) k'
         = (if (spr_sim_singleAbs (fst k'), snd k') = (spr_sim_singleAbs (fst k), snd k)
             then Some e else MapOps.lookup trans_MapOps M k')"
  proof(cases "(spr_sim_singleAbs (fst k'), snd k') = (spr_sim_singleAbs (fst k), snd k)")
    case True hence "k = k'"
      using injD[OF spr_sim_singleAbs_inj] k k' by (auto iff: prod_eqI)
    thus ?thesis
      unfolding trans_MapOps_def trans_MapOps_lookup_def trans_MapOps_update_def trie_odlist_lookup_def trie_odlist_update_with_def
      by (auto simp: trie_lookup_trie_update_with split: option.split split_split)
  next
    case False thus ?thesis
      unfolding trans_MapOps_def trans_MapOps_lookup_def trans_MapOps_update_def trie_odlist_lookup_def trie_odlist_update_with_def
      by (auto simp: trie_lookup_trie_update_with split: option.split split_split)
  qed
qed

sublocale SingleAgentEnvironment < SPRsingle!: Algorithm
            jkbp envInit envAction envTrans envVal
            envObs spr_sim_single spr_sim_single_rels spr_sim_single_val
            spr_sim_singleAbs spr_sim_singleObs spr_sim_singleInit spr_sim_singleTrans spr_sim_singleAction
            trie_odlist_MapOps trans_MapOps
  apply unfold_locales
  apply (rule trie_odlist_MapOps[OF subset_inj_on[OF spr_sim_singleAbs_inj subset_UNIV]])
  apply (rule trans_MapOps)
  done

(* We can't display the output of the algorithm, only run it. Ergo we
want to look at the output of the DFS. *)

definition
  SPRSingleAutoDFS :: "('a, 'p, 'pAct) KBP
                     \<Rightarrow> ('s :: {finite, linorder}) list
                     \<Rightarrow> ('s \<Rightarrow> 'eAct list)
                     \<Rightarrow> ('eAct \<Rightarrow> ('a \<Rightarrow> 'pAct) \<Rightarrow> 's \<Rightarrow> 's)
                     \<Rightarrow> ('s \<Rightarrow> 'p \<Rightarrow> bool)
                     \<Rightarrow> ('a \<Rightarrow> 's \<Rightarrow> 'obs)
                     \<Rightarrow> 'a \<Rightarrow> ('s, 'pAct list) trie \<times> (('s, ('obs, 's odlist) mapping) trie)"
where
  "SPRSingleAutoDFS \<equiv> \<lambda>kbp envInit envAction envTrans envVal envObs. \<lambda>a.
    alg_dfs trie_odlist_MapOps
            trans_MapOps
            (Algorithm.k_frontier_init envInit envObs (spr_sim_singleInit envInit envObs) a)
            (spr_sim_singleObs envObs a)
            (spr_sim_singleTrans kbp envAction envTrans envVal envObs a)
            (\<lambda>ss. spr_sim_singleAction kbp envVal ss a)"

definition
  mkSPRSingleAuto :: "('a, 'p, 'pAct) KBP
                    \<Rightarrow> ('s :: {finite, linorder}) list
                    \<Rightarrow> ('s \<Rightarrow> 'eAct list)
                    \<Rightarrow> ('eAct \<Rightarrow> ('a \<Rightarrow> 'pAct) \<Rightarrow> 's \<Rightarrow> 's)
                    \<Rightarrow> ('s \<Rightarrow> 'p \<Rightarrow> bool)
                    \<Rightarrow> ('a \<Rightarrow> 's \<Rightarrow> 'obs)
                    \<Rightarrow> 'a \<Rightarrow> ('obs, 'pAct, 's odlist) Protocol"
where
  "mkSPRSingleAuto \<equiv> \<lambda>kbp envInit envAction envTrans envVal envObs.
    mkAutoAlg trie_odlist_MapOps
              trans_MapOps
              (Algorithm.k_frontier_init envInit envObs (spr_sim_singleInit envInit envObs))
              (spr_sim_singleObs envObs)
              (spr_sim_singleInit envInit envObs)
              (spr_sim_singleTrans kbp envAction envTrans envVal envObs)
              (spr_sim_singleAction kbp envVal)"

lemma (in SingleAgentEnvironment) mkSPRSingleAuto_implements:
  "implements (mkSPRSingleAuto (jkbp agent) envInit envAction envTrans envVal envObs)"
  using SPRsingle.k_mkAutoAlg_implements
  unfolding mkSPRSingleAuto_def mkAutoAlg_def alg_dfs_def SPRsingle.KBP.k_ins_def SPRsingle.KBP.k_empt_def SPRsingle.KBP.k_memb_def SPRsingle.KBP.trans_update_def SPRsingle.KBP.acts_update_def
  apply (simp add: Let_def)
  done

end

