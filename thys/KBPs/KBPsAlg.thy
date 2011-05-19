
(*
 * Knowledge-based programs.
 * (C)opyright 2011, Peter Gammie, peteg42 at gmail.com.
 * License: BSD
 *)

theory KBPsAlg
imports Main Extra KBPsAuto DFS MapOps
        "~~/src/HOL/Library/LaTeXsugar"
begin


subsection{* A synthesis algorithm *}

text (in Environment) {*

We now show how automata that implement @{term "jkbp"} can be
constructed using the operations specified in @{text
"SimEnvironment"}. Taking care with the definitions allows us to
extract an executable version via Isabelle/HOL's code generator.

We represent the automaton under construction by a pair of maps, one
for actions, mapping representations to lists of agent actions, and
the other for the transition function, mapping representations and
observations to representations. These maps are represented by the
types @{typ "'ma"} and @{typ "'mt"} respectively, with operations
collected in @{term "aOps"} and @{term "tOps"}. These @{term "MapOps"}
records contain @{term "empty"}, @{term "lookup"} and @{term "update"}
functions, specified in the standard way with the extra condition that
they respect @{term "simAbs"} on the domains of interest.

*}

abbreviation(in SimEnvironment) "jkbpSEC \<equiv> \<Union>a. { simf ` equiv_class a (spr_jview a t) |t. t \<in> jkbpC }"

locale Algorithm =
  SimEnvironment jkbp envInit envAction envTrans envVal envObs
                 simf simRels simVal simAbs simObs simInit simTrans simAction
    for jkbp :: "'a \<Rightarrow> ('a, 'p, 'aAct) KBP"


    and envInit :: "('s :: finite) list"
    and envAction :: "'s \<Rightarrow> 'eAct list"
    and envTrans :: "'eAct \<Rightarrow> ('a \<Rightarrow> 'aAct) \<Rightarrow> 's \<Rightarrow> 's"
    and envVal :: "'s \<Rightarrow> 'p \<Rightarrow> bool"

    and envObs :: "'a \<Rightarrow> 's \<Rightarrow> 'obs"

    and simf :: "'s Trace \<Rightarrow> 'ss :: finite"
    and simRels :: "'a \<Rightarrow> 'ss Relation"
    and simVal :: "'ss \<Rightarrow> 'p \<Rightarrow> bool"

    and simAbs :: "'rep \<Rightarrow> 'ss set"

    and simObs :: "'a \<Rightarrow> 'rep \<Rightarrow> 'obs"
    and simInit :: "'a \<Rightarrow> 'obs \<Rightarrow> 'rep"
    and simTrans :: "'a \<Rightarrow> 'rep \<Rightarrow> 'rep list"
    and simAction :: "'rep \<Rightarrow> 'a \<Rightarrow> 'aAct list"

-- {*... as for @{term "SimEnvironment"} ...*}

+ fixes aOps :: "('ma, 'rep, 'aAct list) MapOps"
    and tOps :: "('mt, 'rep \<times> 'obs, 'rep) MapOps"
  assumes aOps: "MapOps simAbs jkbpSEC aOps"
        and tOps: "MapOps (\<lambda>k. (simAbs (fst k), snd k)) (jkbpSEC \<times> UNIV) tOps"

text{*

@{term "UNIV"} is the set of all elements of a type. The repetition of
type signatures in these extended locales is tiresome but necessary to
bring the type variables into scope. As we construct one automaton per
agent, we introduce another locale:

*}

locale AlgorithmForAgent = Algorithm
            jkbp envInit envAction envTrans envVal envObs simf simRels
            simVal simAbs simObs simInit simTrans simAction aOps tOps
    for jkbp :: "'a \<Rightarrow> ('a, 'p, 'aAct) KBP"
    and envInit :: "('s :: finite) list"
    and envAction :: "'s \<Rightarrow> 'eAct list"
    and envTrans :: "'eAct \<Rightarrow> ('a \<Rightarrow> 'aAct) \<Rightarrow> 's \<Rightarrow> 's"
    and envVal :: "'s \<Rightarrow> 'p \<Rightarrow> bool"

    and envObs :: "'a \<Rightarrow> 's \<Rightarrow> 'obs"

    and simf :: "'s Trace \<Rightarrow> 'ss :: finite"
    and simRels :: "'a \<Rightarrow> 'ss Relation"
    and simVal :: "'ss \<Rightarrow> 'p \<Rightarrow> bool"

    and simAbs :: "'rep \<Rightarrow> 'ss set"

    and simObs :: "'a \<Rightarrow> 'rep \<Rightarrow> 'obs"
    and simInit :: "'a \<Rightarrow> 'obs \<Rightarrow> 'rep"
    and simTrans :: "'a \<Rightarrow> 'rep \<Rightarrow> 'rep list"
    and simAction :: "'rep \<Rightarrow> 'a \<Rightarrow> 'aAct list"

    and aOps :: "('ma, 'rep, 'aAct list) MapOps"
    and tOps :: "('mt, 'rep \<times> 'obs, 'rep) MapOps"
+ fixes a :: "'a"

begin

definition
  "k_is_node \<equiv> \<lambda>ec. simAbs ec \<in> sim_equiv_class a ` spr_jview a ` jkbpC"

lemma k_is_node_cong:
  "simAbs ec' = simAbs ec \<Longrightarrow> k_is_node ec' \<longleftrightarrow> k_is_node ec"
  unfolding k_is_node_def by simp

lemma alg_MapOps_empty[simp]:
  "k_is_node ec \<Longrightarrow> lookup aOps (empty aOps) ec = None"
  "k_is_node (fst k) \<Longrightarrow> lookup tOps (empty tOps) k = None"
  unfolding k_is_node_def
  using MapOps_emptyD[OF _ aOps] MapOps_emptyD[OF _ tOps] by blast+

lemma alg_aOps_lookup_update[simp]:
  "\<lbrakk> k_is_node ec; k_is_node ec' \<rbrakk> \<Longrightarrow> lookup aOps (update aOps ec e M) ec' = (if simAbs ec' = simAbs ec then Some e else lookup aOps M ec')"
  unfolding k_is_node_def
  using MapOps_lookup_updateD[OF _ _ aOps] by blast

lemma alg_tOps_lookup_update[simp]:
  "\<lbrakk> k_is_node (fst k); k_is_node (fst k') \<rbrakk> \<Longrightarrow> lookup tOps (update tOps k e M) k' = (if (simAbs (fst k'), snd k') = (simAbs (fst k), snd k) then Some e else lookup tOps M k')"
  unfolding k_is_node_def
  using MapOps_lookup_updateD[OF _ _ tOps] by blast

abbreviation
  "k_succs \<equiv> simTrans a"

lemma k_succs_is_node[intro, simp]:
  assumes x: "k_is_node x"
  shows "list_all k_is_node (k_succs x)"
proof -
  from x obtain t
    where tC: "t \<in> jkbpC"
      and sx: "simAbs x = sim_equiv_class a (spr_jview a t)"
    unfolding k_is_node_def by blast
  have F: "\<And>y. y \<in> set (k_succs x) \<Longrightarrow> simAbs y \<in> simAbs ` set (k_succs x)" by simp
  show ?thesis
    using simTrans'[OF tC sx]
    unfolding k_is_node_def
    apply (auto iff: list_all_iff)
    apply (frule F)
    apply auto
    done
qed

definition
  k_empt :: "'ma \<times> 'mt"
where
  "k_empt \<equiv> (empty aOps, empty tOps)"

definition
  k_memb :: "'rep \<Rightarrow> 'ma \<times> 'mt \<Rightarrow> bool"
where
  "k_memb \<equiv> \<lambda>s A. isSome (lookup aOps (fst A) s)"

lemma k_memb_empt[simp]:
  "k_is_node x \<Longrightarrow> \<not>k_memb x k_empt"
  unfolding k_memb_def k_empt_def by simp

definition
  acts_update :: "'rep \<Rightarrow> 'ma \<times> 'mt \<Rightarrow> 'ma"
where
  "acts_update \<equiv> \<lambda>ec A. update aOps ec (simAction ec a) (fst A)"

definition
  trans_update :: "'rep \<Rightarrow> 'rep \<Rightarrow> 'mt \<Rightarrow> 'mt"
where
  "trans_update \<equiv> \<lambda>ec ec' at. update tOps (ec, simObs a ec') ec' at"

definition
  k_ins :: "'rep \<Rightarrow> 'ma \<times> 'mt \<Rightarrow> 'ma \<times> 'mt"
where
  "k_ins \<equiv> \<lambda>ec A. (acts_update ec A, foldr (trans_update ec) (k_succs ec) (snd A))"

(* The extra gunk in the invariant is an artefact of how we abstract
   finite maps. *)

definition
  "k_invariant A \<equiv>
      (\<forall>ec ec'. k_is_node ec \<and> k_is_node ec' \<and> simAbs ec' = simAbs ec
         \<longrightarrow> lookup aOps (fst A) ec = lookup aOps (fst A) ec')
    \<and> (\<forall>ec ec' obs. k_is_node ec \<and> k_is_node ec' \<and> simAbs ec' = simAbs ec
         \<longrightarrow> lookup tOps (snd A) (ec, obs) = lookup tOps (snd A) (ec', obs))
    \<and> (\<forall>ec. k_is_node ec \<and> k_memb ec A
         \<longrightarrow> (\<exists>acts. lookup aOps (fst A) ec = Some acts \<and> set acts = set (simAction ec a)))
    \<and> (\<forall>ec obs. k_is_node ec \<and> k_memb ec A \<and> obs \<in> simObs a ` set (simTrans a ec)
         \<longrightarrow> (\<exists>ec'. lookup tOps (snd A) (ec, obs) = Some ec'
                  \<and> simAbs ec' \<in> simAbs ` set (simTrans a ec)
                  \<and> simObs a ec' = obs))"

lemma k_invariantI[intro]:
  "\<lbrakk> \<And>ec ec'. \<lbrakk> k_is_node ec; k_is_node ec'; simAbs ec' = simAbs ec \<rbrakk>
       \<Longrightarrow> lookup aOps (fst A) ec = lookup aOps (fst A) ec';
     \<And>ec ec' obs. \<lbrakk> k_is_node ec; k_is_node ec'; simAbs ec' = simAbs ec \<rbrakk>
       \<Longrightarrow> lookup tOps (snd A) (ec, obs) = lookup tOps (snd A) (ec', obs);
     \<And>ec. \<lbrakk> k_is_node ec; k_memb ec A \<rbrakk>
       \<Longrightarrow> \<exists>acts. lookup aOps (fst A) ec = Some acts \<and> set acts = set (simAction ec a);
     \<And>ec obs ecs'. \<lbrakk> k_is_node ec; k_memb ec A; obs \<in> simObs a ` set (simTrans a ec) \<rbrakk>
       \<Longrightarrow> \<exists>ec'. lookup tOps (snd A) (ec, obs) = Some ec'
               \<and> simAbs ec' \<in> simAbs ` set (simTrans a ec)
               \<and> simObs a ec' = obs \<rbrakk>
  \<Longrightarrow> k_invariant A"
  unfolding k_invariant_def by (simp (no_asm_simp))

lemma k_invariantAOD:
  "\<lbrakk> k_is_node ec; k_is_node ec'; simAbs ec' = simAbs ec; k_invariant A \<rbrakk>
     \<Longrightarrow> lookup aOps (fst A) ec = lookup aOps (fst A) ec'"
  unfolding k_invariant_def by blast

lemma k_invariantTOD:
  "\<lbrakk> k_is_node ec; k_is_node ec'; simAbs ec' = simAbs ec; k_invariant A \<rbrakk>
     \<Longrightarrow> lookup tOps (snd A) (ec, obs) = lookup tOps (snd A) (ec', obs)"
  unfolding k_invariant_def by blast

lemma k_invariantAD:
  "\<lbrakk> k_is_node ec; k_memb ec A; k_invariant A \<rbrakk>
     \<Longrightarrow> \<exists>acts. lookup aOps (fst A) ec = Some acts \<and> set acts = set (simAction ec a)"
  unfolding k_invariant_def by simp

lemma k_invariantTD:
  "\<lbrakk> k_is_node ec; k_memb ec A; obs \<in> simObs a ` set (simTrans a ec); k_invariant A \<rbrakk>
     \<Longrightarrow> \<exists>ec'. lookup tOps (snd A) (ec, obs) = Some ec'
             \<and> simAbs ec' \<in> simAbs ` set (simTrans a ec)
             \<and> simObs a ec' = obs"
  unfolding k_invariant_def by blast

lemma k_invariant_empt[simp]:
  "k_invariant k_empt"
  apply rule
  apply auto
  apply (auto iff: k_empt_def)
  done

lemma k_invariant_step_new_aux:
  assumes X: "set X \<subseteq> set (k_succs x)"
      and x: "k_is_node x"
      and ec: "k_is_node ec"
      and ec': "simAbs ec' \<in> simAbs ` set X"
      and S: "simAbs ec = simAbs x"
  shows "\<exists>r. lookup tOps (foldr (trans_update x) X Y) (ec, simObs a ec') = Some r
           \<and> simAbs r \<in> simAbs ` set (k_succs ec)
           \<and> simObs a r = simObs a ec'"
using X ec'
proof(induct X arbitrary: Y)
  case Nil thus ?case by simp
next
  case (Cons y ys) show ?case
  proof(cases "simAbs ec' = simAbs y")
    case False with x ec S Cons show ?thesis
      unfolding trans_update_def
      apply clarsimp
      unfolding k_is_node_def
      apply (erule imageE)+
      apply (cut_tac a=a and t=xaa and ec=x and ec'=ec in FIXME_simTrans_simAbs_cong[symmetric])
      apply simp_all
      done
  next
    case True
    with Cons have F: "simAbs y \<in> simAbs ` set (k_succs x)"
      by auto
    from x obtain t
      where tC: "t \<in> jkbpC"
        and x': "simAbs x = sim_equiv_class a (spr_jview a t)"
      unfolding k_is_node_def by blast
    from F obtain t' s
      where "simAbs y = sim_equiv_class a (spr_jview a (t' \<leadsto> s))"
        and tsC: "t' \<leadsto> s \<in> jkbpC"
        and tt': "spr_jview a t = spr_jview a t'"
      using simTrans'[OF tC x'] by auto
    with Cons True S x ec show ?thesis
      unfolding trans_update_def
      apply auto
      apply (subst FIXME_simTrans_simAbs_cong[where t=t' and ec'=x])
       apply blast

       using x' tt'
       apply auto[1]

       apply simp

       apply (rule image_eqI[where x=y])
        apply simp_all
       done
  qed
qed

lemma k_invariant_step_new:
  assumes x: "k_is_node x"
      and ec: "k_is_node ec"
      and ec': "ec' \<in> set (k_succs ec)"
      and S: "simAbs ec = simAbs x"
  shows "\<exists>ec''. lookup tOps (snd (k_ins x A)) (ec, simObs a ec') = Some ec''
              \<and> simAbs ec'' \<in> simAbs ` set (k_succs ec)
              \<and> simObs a ec'' = simObs a ec'"
proof -
  from x ec'
  have ec': "simAbs ec' \<in> simAbs ` set (k_succs x)"
    unfolding k_is_node_def
    apply clarsimp
    apply (subst FIXME_simTrans_simAbs_cong[OF _ _ S, symmetric])
    using S
    apply auto
    done
  thus ?thesis
    using k_invariant_step_new_aux[OF subset_refl x ec _ S, where ec'=ec']
    unfolding k_ins_def
    apply auto
    done
qed

lemma k_invariant_step_old_aux:
  assumes x: "k_is_node x"
      and ec: "k_is_node ec"
      and S: "simAbs ec \<noteq> simAbs x"
  shows "lookup tOps (foldr (trans_update x) X Y) (ec, obs)
       = lookup tOps Y (ec, obs)"
proof(induct X)
  case (Cons z zs) with x ec S show ?case
    by (cases "lookup tOps Y (ec, obs)") (simp_all add: trans_update_def)
qed simp

lemma k_invariant_step_old:
  assumes x: "k_is_node x"
      and ec: "k_is_node ec"
      and S: "simAbs ec \<noteq> simAbs x"
  shows "lookup tOps (snd (k_ins x A)) (ec, obs)
       = lookup tOps (snd A) (ec, obs)"
  unfolding k_ins_def
  using k_invariant_step_old_aux[OF x ec S]
  by simp

lemma k_invariant_frame_FIXME:
  assumes B: "lookup tOps Y (ec, obs) = lookup tOps Y (ec', obs)"
      and x: "k_is_node x"
      and ec: "k_is_node ec"
      and ec': "k_is_node ec'"
      and S: "simAbs ec' = simAbs ec"
  shows "lookup tOps (foldr (trans_update x) X Y) (ec, obs) = lookup tOps (foldr (trans_update x) X Y) (ec', obs)"
  apply (induct X)
  unfolding trans_update_def
   using B
   apply simp
  using x ec ec' S
  apply simp
  done

lemma k_invariant_step[simp]:
  assumes N: "k_is_node x"
      and I: "k_invariant A"
      and M: "\<not> k_memb x A"
  shows "k_invariant (k_ins x A)"
proof
  fix ec ec'
  assume ec: "k_is_node ec" and ec': "k_is_node ec'" and X: "simAbs ec' = simAbs ec"
  with N show "lookup aOps (fst (k_ins x A)) ec = lookup aOps (fst (k_ins x A)) ec'"
    unfolding k_ins_def acts_update_def
    using k_invariantAOD[OF ec ec' X I]
    apply simp
    done
next
  fix ec ec' obs
  assume ec: "k_is_node ec" and ec': "k_is_node ec'" and X: "simAbs ec' = simAbs ec"
  show "lookup tOps (snd (k_ins x A)) (ec, obs) = lookup tOps (snd (k_ins x A)) (ec', obs)"
    unfolding k_ins_def
    using k_invariant_frame_FIXME[OF k_invariantTOD[OF ec ec' X I] N ec ec' X]
    apply simp
    done
next
  fix ec obs ecs'
  assume n: "k_is_node ec"
    and ec: "k_memb ec (k_ins x A)"
    and obs: "obs \<in> simObs a ` set (simTrans a ec)"
  show "\<exists>ec'. lookup tOps (snd (k_ins x A)) (ec, obs) = Some ec'
            \<and> simAbs ec' \<in> simAbs ` set (k_succs ec)
            \<and> simObs a ec' = obs"
  proof(cases "simAbs ec = simAbs x")
    case True with N n obs show ?thesis
      using k_invariant_step_new[where A=A] by auto
  next
    case False with I N n ec obs show ?thesis
      apply (simp add: k_invariant_step_old)
      apply (rule k_invariantTD)
      apply simp_all
      unfolding k_ins_def k_memb_def acts_update_def
      apply simp
      done
  qed
next
  fix ec
  assume n: "k_is_node ec"
     and ec: "k_memb ec (k_ins x A)"
  show "\<exists>acts. lookup aOps (fst (k_ins x A)) ec = Some acts \<and> set acts = set (simAction ec a)"
  proof(cases "simAbs ec = simAbs x")
    case True with aOps N n show ?thesis
      unfolding k_ins_def acts_update_def
      apply clarsimp
      unfolding k_is_node_def
      apply clarsimp
      done
  next
    case False with aOps N I M n ec show ?thesis
      unfolding k_ins_def acts_update_def
      apply simp
      apply (rule k_invariantAD)
      unfolding k_memb_def
      apply simp_all
      done
  qed
qed

definition (in Algorithm)
  k_frontier_init :: "'a \<Rightarrow> 'rep list"
where
  "k_frontier_init \<equiv> \<lambda>a. map (simInit a \<circ> envObs a) envInit"

lemma k_frontier_init_is_node[intro, simp]:
  "list_all k_is_node (k_frontier_init a)"
  unfolding k_frontier_init_def k_is_node_def
  apply (clarsimp simp: simInit list_all_iff)
  apply (rule_tac x="tInit (envObs a x)" in image_eqI)
  apply (auto simp: spr_jview_def)
  done


(* FIXME I want the definition in the doc but want to use
   DFS.gen_dfs. For some reason this works without further ado: I
   would have expected to need to show that DFS.gen_dfs and this
   gen_dfs coincide and so forth. Presumably the simp rules are
   magically doing the right thing. *)

partial_function (tailrec) gen_dfs where
  "gen_dfs succs ins memb S wl = (case wl of
     [] \<Rightarrow> S
   | (x\<cdot>xs) \<Rightarrow> if memb x S then gen_dfs succs ins memb S xs
                                else gen_dfs succs ins memb (ins x S) (succs x @ xs))"

definition (in -)
 alg_dfs :: "('ma, 'rep, 'aAct list) MapOps \<Rightarrow> ('mt, 'rep \<times> 'obs, 'rep) MapOps
            \<Rightarrow> 'rep list \<Rightarrow> ('rep \<Rightarrow> 'obs) \<Rightarrow> ('rep \<Rightarrow> 'rep list) \<Rightarrow> ('rep \<Rightarrow> 'aAct list)
            \<Rightarrow> 'ma \<times> 'mt"
where "alg_dfs aOps tOps frontier_init simObs simTrans simAction \<equiv>
    let k_empt = (empty aOps, empty tOps);
        k_memb = (\<lambda>s A. isSome (lookup aOps (fst A) s));
        k_succs = simTrans;
        acts_update = (\<lambda>ec A. update aOps ec (simAction ec) (fst A));
        trans_update = (\<lambda>ec ec' at. update tOps (ec, simObs ec') ec' at);
        k_ins = (\<lambda>ec A. (acts_update ec A, foldr (trans_update ec) (k_succs ec) (snd A)))
     in gen_dfs k_succs k_ins k_memb k_empt frontier_init"


definition (in -)
  alg_mk_auto :: "('ma, 'rep, 'aAct list) MapOps
                \<Rightarrow> ('mt, 'rep \<times> 'obs, 'rep) MapOps
                \<Rightarrow> ('obs \<Rightarrow> 'rep)
                \<Rightarrow> 'ma \<times> 'mt
                \<Rightarrow> ('obs, 'aAct, 'rep) Protocol"
where
  "alg_mk_auto aOps tOps simInit k_dfs \<equiv>
    \<lparr> pInit = simInit,
      pTrans = \<lambda>obs ec. the (lookup tOps (snd k_dfs) (ec, obs)),
      pAct = \<lambda>ec. the (lookup aOps (fst k_dfs) ec)
    \<rparr>"

definition (in -)
  mkAutoAlg :: "('ma, 'rep, 'aAct list) MapOps
            \<Rightarrow> ('mt, 'rep \<times> 'obs, 'rep) MapOps
            \<Rightarrow> ('a \<Rightarrow> 'rep list)
            \<Rightarrow> ('a \<Rightarrow> 'rep \<Rightarrow> 'obs)
            \<Rightarrow> ('a \<Rightarrow> 'obs \<Rightarrow> 'rep)
            \<Rightarrow> ('a \<Rightarrow> 'rep \<Rightarrow> 'rep list)
            \<Rightarrow> ('rep \<Rightarrow> 'a \<Rightarrow> 'aAct list)
            \<Rightarrow> ('a \<Rightarrow> ('obs, 'aAct, 'rep) Protocol)"
where
  [code]:
  "mkAutoAlg aOps tOps frontier_init simObs simInit simTrans simAction \<equiv> \<lambda>a.
    alg_mk_auto aOps tOps (simInit a) (alg_dfs aOps tOps (frontier_init a) (simObs a) (simTrans a) (\<lambda>rep. simAction rep a))"

lemma (in -) mkAutoSim_simps[simp]:
  "pInit (mkAutoAlg aOps tOps frontier_init simObs simInit simTrans simAction a) = simInit a"
  "pTrans (mkAutoAlg aOps tOps frontier_init simObs simInit simTrans simAction a)
 = (\<lambda>obs ec. the (lookup tOps (snd (alg_dfs aOps tOps (frontier_init a) (simObs a) (simTrans a) (\<lambda>rep. simAction rep a))) (ec, obs)))"
  "pAct (mkAutoAlg aOps tOps frontier_init simObs simInit simTrans simAction a)
 = (\<lambda>ec. the (lookup aOps (fst (alg_dfs aOps tOps (frontier_init a) (simObs a) (simTrans a) (\<lambda>rep. simAction rep a))) ec))"
  unfolding mkAutoAlg_def alg_mk_auto_def
  apply (simp_all add: Let_def)
  done

abbreviation
  "k_alg_dfs \<equiv> alg_dfs aOps tOps (k_frontier_init a) (simObs a) (simTrans a) (\<lambda>ec. simAction ec a)"

end (* context *)


sublocale AlgorithmForAgent
        < KBPAlg!: DFS k_succs k_is_node k_invariant k_ins k_memb k_empt simAbs

  apply (unfold_locales)
  apply simp_all

  unfolding k_memb_def k_ins_def acts_update_def
  using aOps
  apply (auto iff: isSome_eq)[1]

  unfolding k_is_node_def
  apply clarsimp
  apply (erule FIXME_simTrans_simAbs_cong)
  apply auto
  done


context AlgorithmForAgent begin

(* This is a syntactic nightmare. *)

lemma k_alg_dfs_invariant:
  "k_invariant k_alg_dfs"
  unfolding alg_dfs_def
  using KBPAlg.dfs_invariant'[where S="k_empt" and xs="k_frontier_init a"]
  apply (simp add: Let_def)
  apply (fold k_empt_def k_memb_def)
  apply (unfold k_ins_def acts_update_def trans_update_def)
  apply simp
  done

lemma FIXME_ec_aux:
  "simAbs ` KBPAlg.reachable (set (k_frontier_init a))
 = sim_equiv_class a ` spr_jview a ` jkbpC" (is "?lhs = ?rhs")
proof
  show "?lhs \<subseteq> ?rhs"
  proof
    fix sx assume "sx \<in> ?lhs"
    then obtain x
      where x: "x \<in> KBPAlg.reachable (set (k_frontier_init a))"
        and sx: "simAbs x = sx"
      by auto
    hence "x \<in> ({ (x, y). y \<in> set (k_succs x) })\<^sup>*
                 `` set (map (simInit a \<circ> envObs a) envInit)"
      unfolding KBPAlg.reachable_def k_frontier_init_def by simp
    then obtain s iobs
      where R: "(simInit a iobs, x) \<in> ({ (x, y). y \<in> set (k_succs x)})\<^sup>*"
        and sI: "s \<in> set envInit"
        and iobs: "envObs a s = iobs"
      by (auto simp del: simInit)
    from R x have "simAbs x \<in> ?rhs"
    proof(induct arbitrary: sx rule: rtrancl_induct)
      case base
      with sI iobs show ?case
        using simInit'[where a=a and obs=iobs]
        apply clarsimp
        apply (rule image_eqI[where x="tInit (envObs a s)"])
        apply (auto simp: spr_jview_def)
        done
    next
      case (step x y)
      with sI iobs
      have "simAbs x \<in> (sim_equiv_class a \<circ> spr_jview a) ` jkbpC"
        unfolding KBPAlg.reachable_def Image_def k_frontier_init_def o_def
        by auto
      then obtain t
        where tC: "t \<in> jkbpC"
          and F: "simAbs x = sim_equiv_class a (spr_jview a t)"
        by auto
      from step
      have "simAbs y \<in> simAbs ` set (k_succs x)" by auto
      thus ?case
        using simTrans'[OF tC F] by auto
    qed
    with sx show "sx \<in> ?rhs" by simp
  qed
next
  show "?rhs \<subseteq> ?lhs"
  proof
    fix ec assume "ec \<in> ?rhs"
    then obtain t
      where tC: "t \<in> jkbpC"
        and ec: "ec = sim_equiv_class a (spr_jview a t)"
      by auto
    thus "ec \<in> ?lhs"
    proof(induct t arbitrary: ec)
      case (tInit s) thus ?case
        unfolding KBPAlg.reachable_def (* FIXME ouch this is touchy *)
        unfolding k_frontier_init_def
        apply (simp)
        apply (rule image_eqI[where x="simInit a (envObs a s)"])
         apply (auto simp: simInit spr_jview_def)[1]
        apply (rule ImageI[where a="simInit a (envObs a s)"])
        apply auto
        done
    next
      case (tStep t s)
      hence tsC: "t \<leadsto> s \<in> jkbpC"
        and ec: "ec = sim_equiv_class a (spr_jview a (t \<leadsto> s))"
        and "sim_equiv_class a (spr_jview a t)
           \<in> simAbs ` DFS.reachable k_succs (set (k_frontier_init a))"
        by auto
      then obtain rect
        where rect: "rect \<in> DFS.reachable k_succs (set (k_frontier_init a))"
          and srect: "simAbs rect = sim_equiv_class a (spr_jview a t)"
        by auto
      from tsC ec srect
      have "ec \<in> simAbs ` set (simTrans a rect)"
        using simTrans'[where a=a and ec=rect and t=t] by auto
      then obtain rec
        where rec: "ec = simAbs rec"
          and F: "rec \<in> set (simTrans a rect)"
        by auto
      from rect obtain rec0
        where rec0: "rec0 \<in> set (k_frontier_init a)"
          and rec0rect: "(rec0, rect) \<in> ({ (x, y). y \<in> set (k_succs x)})\<^sup>*"
        unfolding KBPAlg.reachable_def by auto
      show ?case
        apply -
        apply (rule image_eqI[where x="rec"])
         apply (rule rec)
        unfolding KBPAlg.reachable_def
        apply (rule ImageI[where a="rec0"])
         apply (rule rtrancl_into_rtrancl[where b="rect"])
          apply (rule rec0rect)
         apply clarsimp
         apply (rule F)
         apply (rule rec0)
         done
     qed
   qed
qed

(* Purely syntactic auxiliary lemma. *)

lemma FIXME_ec_syntax_aux[simp]:
  "k_alg_dfs = DFS.gen_dfs k_succs k_ins k_memb k_empt (k_frontier_init a)"
  unfolding alg_dfs_def k_empt_def k_ins_def acts_update_def trans_update_def
  by (simp add: Let_def k_memb_def[symmetric])

(* Every equivalence class has a representation visited by the DFS. *)

lemma k_memb_rep:
  assumes N: "k_is_node rec"
  shows "k_memb rec k_alg_dfs"
proof -
  from N obtain rec'
    where r: "rec' \<in> DFS.reachable k_succs (set (k_frontier_init a))"
      and rec': "simAbs rec = simAbs rec'"
    unfolding k_is_node_def by (auto iff: FIXME_ec_aux[symmetric])

  from N k_is_node_cong[OF rec', symmetric]
  have N': "k_is_node rec'"
    unfolding k_is_node_def by auto

  show "k_memb rec k_alg_dfs"
    using KBPAlg.reachable_imp_dfs[OF N' k_frontier_init_is_node r]
    apply clarsimp
    apply (subst k_memb_def)
    apply (subst (asm) k_memb_def)
    using k_invariantAOD[OF N' N rec' k_alg_dfs_invariant, symmetric]
    apply (cut_tac ec=y' and ec'=rec' in k_invariantAOD[OF _ _ _ k_alg_dfs_invariant, symmetric])
     apply simp_all

     apply (cut_tac ec=rec' and ec'=y' in k_is_node_cong)
     apply simp
     using N'
     apply simp
     apply (rule N')
     done
qed

end (* context *)


sublocale Algorithm < KBP!: AlgorithmForAgent
  jkbp envInit envAction envTrans envVal envObs simf simRels simVal
  simAbs simObs simInit simTrans simAction aOps tOps a for a
  by unfold_locales

abbreviation (in Algorithm)
  "k_mkAutoAlg \<equiv> mkAutoAlg aOps tOps k_frontier_init simObs simInit simTrans simAction"

context Algorithm begin

lemma FIXME_mkAutoSim_eq:
  assumes tC: "t \<in> jkbpC"
  shows "simAbs (runJP k_mkAutoAlg t a) = simAbs (runJP mkAutoSim t a)"
using tC
proof(induct t)
  case (tInit s) thus ?case by simp
next
  case (tStep t s)
  hence tC: "t \<in> jkbpC" by blast

  from tStep
  have N: "KBP.k_is_node a (runJP k_mkAutoAlg t a)"
    unfolding KBP.k_is_node_def
    by (simp only: mkAutoSim_ec) auto

  from tStep
  have ect: "simAbs (runJP k_mkAutoAlg t a) = sim_equiv_class a (spr_jview a t)"
    by (simp only: mkAutoSim_ec) auto

  from tStep
  have "sim_equiv_class a (spr_jview a (t \<leadsto> s)) \<in> simAbs ` set (simTrans a (runJP k_mkAutoAlg t a))"
    using simTrans'[OF tC ect] by auto
  then obtain ec
    where ec: "ec \<in> set (simTrans a (runJP k_mkAutoAlg t a))"
      and sec: "simAbs ec = sim_equiv_class a (spr_jview a (t \<leadsto> s))"
    by auto

  from tStep sec ec
  have F: "envObs a s \<in> simObs a ` set (simTrans a (runJP k_mkAutoAlg t a))"
    using simObs'[where a=a and t="t\<leadsto>s", symmetric] sec ec by (auto simp del: simObs')

  from KBP.k_memb_rep[OF N]
  have E: "KBP.k_memb (runJP k_mkAutoAlg t a) (KBP.k_alg_dfs a)" by blast

  have G: "simAbs (runJP k_mkAutoAlg (t \<leadsto> s) a) = sim_equiv_class a (spr_jview a (t \<leadsto> s))"
    using KBP.k_invariantTD[OF N E F KBP.k_alg_dfs_invariant]
    apply clarsimp
    using simTrans'[OF tC ect]
    apply (subgoal_tac "simAbs x \<in> simAbs ` set (simTrans a (runJP k_mkAutoAlg t a))")
     apply (clarsimp simp: spr_jview_def)
    apply blast
    done

  from tStep show ?case by (simp only: G mkAutoSim_ec)
qed

lemma FIXME_mkAutoSim_act_eq:
  assumes tC: "t \<in> jkbpC"
  shows "set \<circ> actJP k_mkAutoAlg t = set \<circ> actJP mkAutoSim t" (is "?lhs = ?rhs")
proof
  fix a
  let ?ec = "sim_equiv_class a (spr_jview a t)"
  let ?rec = "runJP k_mkAutoAlg t a"

  have ect: "?ec = simAbs ?rec"
    by (simp only: FIXME_mkAutoSim_eq[OF tC] mkAutoSim_ec[OF tC])

  from tC have E: "?ec \<in> (sim_equiv_class a \<circ> spr_jview a) ` jkbpC"
    by auto

  from tC E have N: "KBP.k_is_node a (runJP k_mkAutoAlg t a)"
    unfolding KBP.k_is_node_def
    using FIXME_mkAutoSim_eq[OF tC, where a=a] mkAutoSim_ec[OF tC]
    by auto

  from KBP.k_memb_rep[OF N]
  have E: "KBP.k_memb ?rec (KBP.k_alg_dfs a)" by blast

  obtain acts
    where "lookup aOps (fst (KBP.k_alg_dfs a)) ?rec = Some acts"
      and "set acts = set (simAction ?rec a)"
    using KBP.k_invariantAD[OF N E KBP.k_alg_dfs_invariant] by blast

  with tC show "?lhs a = ?rhs a"
    using FIXME_mkAutoSim_eq[OF tC, where a=a] mkAutoSim_ec[OF tC]
    apply clarsimp
    done
qed

lemma mkAutoSim_k_mkAutoAlg_be:
  shows "behaviourally_equiv mkAutoSim k_mkAutoAlg"
  by rule (simp only: FIXME_mkAutoSim_act_eq)

theorem (in Algorithm) k_mkAutoAlg_implements: "implements k_mkAutoAlg"
  using behaviourally_equiv_implements[OF mkAutoSim_k_mkAutoAlg_be]
        mkAutoSim_implements
  by simp

end (* context *)


end

