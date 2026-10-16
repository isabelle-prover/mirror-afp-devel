
(*
Title:         Rely-Guarantee Specification of a Concurrent Garbage Collector
Author(s):     Roger C. Su and Nisansala P. Yatapanage
Year:          2026
License:       BSD 2-Clause
Maintainer(s): Su <roger.c.su@proton.me>
               Yatapanage <Nisansala.Yatapanage@anu.edu.au>
*)

theory RG_Garbage_Collector imports Main begin

section \<open>Preliminaries\<close>

lemma holds_for_all:
  assumes "guar_b \<sigma> \<sigma>'"
      and "p s \<sigma>"
      and "\<forall> w. (guar_b \<sigma> \<sigma>' \<and> p w \<sigma> \<longrightarrow> q w \<sigma> \<sigma>')"
      and "p s \<sigma> \<and> q s \<sigma> \<sigma>' \<longrightarrow> rely_a \<sigma> \<sigma>'"
    shows "rely_a \<sigma> \<sigma>'"
  using assms by blast

definition reach
  :: "'a set \<Rightarrow> 'a rel \<Rightarrow> 'a set" where
  "reach S R \<equiv> rtrancl R `` S"

lemma reach_base:
  "w \<in> S \<Longrightarrow> w \<in> reach S R"
  unfolding reach_def by blast

lemma reach_step:
  "\<lbrakk> w \<in> reach S R ; (w,w') \<in> R \<rbrakk> \<Longrightarrow> w' \<in> reach S R"
  unfolding reach_def apply clarsimp
  by (meson ImageI rtrancl.simps)

lemma reach_induct:
  assumes "w \<in> reach S R"
      and "\<And> v. v \<in> S \<Longrightarrow> P v"
      and "\<And> u v. u \<in> reach S R \<Longrightarrow> P u \<Longrightarrow> (u,v) \<in> R \<Longrightarrow> P v"
    shows "P w"
  using assms unfolding reach_def apply clarsimp
  by (metis (full_types) ImageI rtrancl_induct)

section \<open>Definitions\<close>

text \<open>The \emph{nodes} in memory are represented as an arbitrary type @{typ 'a}.\<close>

text \<open>Part of the system state is the local variables of the Collector, 
which cannot be accessed by the Mutator.\<close>

record 'a localC =
    safe :: "'a set"
  consid :: "'a set"

text \<open>The state of the system is defined as the following record-type.\<close>

record 'a state =
   roots :: "'a set"
      hp :: "'a rel" \<comment> \<open>the heap is modelled as a directed graph (i.e.\ a relation)\<close>
    free :: "'a set"
  marked :: "'a set"
     tbm :: "'a option"
  localCvar :: "'a localC"

text \<open>Then we formulate the notion of ``a node being reachable in a state''.\<close>

definition reachable
  :: "'a state \<Rightarrow> 'a \<Rightarrow> bool" where
  "reachable \<sigma> x \<equiv> x \<in> reach (roots \<sigma>) (hp \<sigma>)"

lemma reachable_exists:
  "reachable \<sigma> y \<Longrightarrow> y \<in> roots \<sigma> \<or> (\<exists> x. reachable \<sigma> x \<and> (x,y) \<in> hp \<sigma>)"
  unfolding reachable_def reach_def apply clarsimp
  by (metis ImageI rtrancl.cases)

text \<open>We now define the various clauses that make up of our specification.\<close>

text \<open>In the definitions below, if @{term xy} is a pair in the heap, then
@{term "fst xy"} is the node in the domain (@{text "(a,j) \<in> dom hp"} in the paper),
and @{term "snd xy"} is any child of the node (@{text "hp(a,j)"} in the paper).\<close>

text \<open>All the marked nodes in the given set have marked children.\<close>

definition all_ok
  :: "'a set \<Rightarrow> 'a state \<Rightarrow> bool" where
  "all_ok s \<sigma> \<equiv>  \<forall> xy \<in> hp \<sigma>.
    fst xy \<in> marked \<sigma> \<and>
    fst xy \<in> s 
    \<longrightarrow> (snd xy \<in> marked \<sigma>)"

text \<open>For all marked nodes in the given set that have unmarked children,
there is another path to that child.\<close>

definition can_be_marked
  :: "'a set \<Rightarrow> 'a state \<Rightarrow> bool" where
  "can_be_marked s \<sigma> \<equiv> \<forall> xy \<in> hp \<sigma>.
    fst xy \<in> marked \<sigma> \<inter> s \<and>
    snd xy \<notin> marked \<sigma> \<and>
    reachable \<sigma> (snd xy) 
    \<longrightarrow> (\<exists> zw \<in> hp \<sigma>.
      (fst zw \<in>  reach (roots \<sigma>) (hp \<sigma>) \<or> fst zw \<in> reach (marked \<sigma> \<inter> -s) (hp \<sigma>)) \<and>
      (fst zw \<notin> s \<or> fst zw \<notin> marked \<sigma>) \<and>
       fst xy \<noteq> fst zw \<and>
       snd xy = snd zw)"

text \<open>The @{term tbm} field is the only child node that
(1) is unmarked and
(2) has a marked parent.\<close>

definition tbm_put
  :: "'a set \<Rightarrow> 'a state \<Rightarrow> bool" where
  "tbm_put s \<sigma> \<equiv> \<forall> xy \<in> hp \<sigma>.
    tbm \<sigma> \<noteq> Some (snd xy) \<and>
    fst xy \<in> s \<and>
    fst xy \<in> marked \<sigma>
    \<longrightarrow> (snd xy \<in> marked \<sigma>)"

text \<open>The rely condition of the collector.\<close>

definition rely_collector
  :: "'a state \<Rightarrow> 'a state \<Rightarrow> bool" where
 "rely_collector \<sigma> \<sigma>' \<equiv> marked \<sigma> \<subseteq> marked \<sigma>' \<and> localCvar \<sigma> = localCvar \<sigma>' \<and>
   (all_ok (safe (localCvar \<sigma>)) \<sigma> \<longrightarrow>
      can_be_marked (safe (localCvar \<sigma>)) \<sigma>' \<or> marked \<sigma> \<subset> marked \<sigma>')"

text \<open>The guarantee condition of the Propagate phase of the Collector.\<close>

definition guar_collector
  :: "'a state \<Rightarrow> 'a state  \<Rightarrow> bool" where
  "guar_collector \<sigma> \<sigma>' \<equiv> marked \<sigma> \<subseteq> marked \<sigma>' \<and>
    consid (localCvar \<sigma>) \<subseteq> consid (localCvar \<sigma>') \<and>
    safe (localCvar \<sigma>') \<subseteq> safe (localCvar \<sigma>) \<and>
    ((safe (localCvar \<sigma>') = consid (localCvar \<sigma>')) \<or>
     ((safe (localCvar \<sigma>') \<subset> consid (localCvar \<sigma>))) \<and> (marked \<sigma> \<subset> marked \<sigma>))"

text \<open>The post condition of the Propagate phase of the Collector.\<close>

definition post_propagate
  :: "'a state \<Rightarrow> 'a state  \<Rightarrow> bool" where
  "post_propagate \<sigma> \<sigma>' \<equiv> \<forall> (x,y) \<in> hp \<sigma>.
     x \<in> marked \<sigma>' \<inter> consid (localCvar \<sigma>') \<longrightarrow> 
    (y \<in> marked \<sigma>' \<or> (marked \<sigma> \<subset> marked \<sigma>'))"

text \<open>The post condition of the remove action of the Mutator.\<close>

definition post_change_remove
  :: "'a state \<Rightarrow> 'a state \<Rightarrow> bool" where
  "post_change_remove \<sigma> \<sigma>' \<equiv> \<exists> xy.
    xy \<notin> hp \<sigma>' \<and> hp \<sigma> = hp \<sigma>' \<union> {xy} \<and> reachable \<sigma> (fst xy) \<and>
    tbm \<sigma>' = None"

text \<open>The post condition of the redirect action of the Mutator.\<close>

definition post_change_redirect
  :: "'a state \<Rightarrow> 'a state \<Rightarrow> bool" where
  "post_change_redirect \<sigma> \<sigma>' \<equiv> \<exists> x y z.
    hp \<sigma> - hp \<sigma>' = {(x,y)} \<and> hp \<sigma>' - hp \<sigma> = {(x,z)} \<and> reachable \<sigma> x \<and>
    tbm \<sigma>' = Some z \<and> reachable \<sigma> z" 

text \<open>The common post condition of the remove and redirect actions of the Mutator.
It describes the behaviour when the edge @{term "(x,y)"} is removed or redirected
to @{term "(x,a)"}.\<close>

definition post_change
  :: "'a state \<Rightarrow> 'a state \<Rightarrow> bool" where
  "post_change \<sigma> \<sigma>' \<equiv> roots \<sigma> \<noteq> {} \<and>
   (post_change_remove \<sigma> \<sigma>' \<or> post_change_redirect \<sigma> \<sigma>') \<and> 
   (marked \<sigma> =  marked \<sigma>') \<and>
   (roots \<sigma> = roots \<sigma>') \<and>
   (tbm \<sigma> =  tbm \<sigma>') \<and>
   (localCvar \<sigma> = localCvar \<sigma>')"

text \<open>The post condition of the action of the Mutator that sets @{term tbm}.\<close>

definition post_mark_tbm
  :: "'a state \<Rightarrow> 'a state \<Rightarrow> bool" where
  "post_mark_tbm \<sigma> \<sigma>' \<equiv>
     ((tbm \<sigma> = None \<and> marked \<sigma>' = marked \<sigma>) \<or>
      (\<exists>x. tbm \<sigma> = Some x \<and> marked \<sigma>' = marked \<sigma> \<union> {x})) \<and>
     tbm \<sigma>' = None \<and> hp \<sigma> = hp \<sigma>' \<and> roots \<sigma> = roots \<sigma>' \<and>
     (localCvar \<sigma> = localCvar \<sigma>')"

text \<open>An invariant that the roots always remain marked.\<close>

definition inv_roots
  :: "'a state \<Rightarrow> bool" where
  "inv_roots \<sigma> \<equiv> roots \<sigma> \<subseteq> marked \<sigma>"

lemma inv_roots_change:
  "\<lbrakk> post_change \<sigma> \<sigma>' ; inv_roots \<sigma> \<rbrakk> \<Longrightarrow> inv_roots \<sigma>'"
  unfolding post_change_def inv_roots_def by blast

lemma inv_roots_mark:
  "\<lbrakk> post_mark_tbm \<sigma> \<sigma>' ; inv_roots \<sigma> \<rbrakk> \<Longrightarrow> inv_roots \<sigma>'"
  unfolding post_mark_tbm_def inv_roots_def by blast

text \<open>A Mutator step preserves the invariant.\<close>

lemma inv_roots_step:
  "\<lbrakk> post_change \<sigma> \<sigma>' \<or> post_mark_tbm \<sigma> \<sigma>' ; inv_roots \<sigma> \<rbrakk> \<Longrightarrow> inv_roots \<sigma>'"
  using inv_roots_change inv_roots_mark by blast

section \<open>Lemmas\<close>

text \<open>This lemma establishes one of the premises when instantiating
@{theory_text holds_for_all} to the concurrent garbage collector.\<close>

lemma p_q_gives_rely:
  assumes "all_ok (safe (localCvar \<sigma>)) \<sigma>"
      and "marked \<sigma> \<subseteq> marked \<sigma>' \<and> localCvar \<sigma> = localCvar \<sigma>' \<and>
              (can_be_marked (safe (localCvar \<sigma>)) \<sigma>' \<or> marked \<sigma> \<subset> marked \<sigma>')"
    shows "rely_collector \<sigma> \<sigma>'"
  using assms unfolding rely_collector_def by blast

lemma all_ok_conseqs:
  assumes "all_ok s \<sigma>"
    shows "can_be_marked s \<sigma>"
      and "tbm_put s \<sigma>"
  using assms unfolding all_ok_def can_be_marked_def tbm_put_def by auto

subsection \<open>Stability Lemmas\<close>

text \<open>A Mutator remove step preserves @{term all_ok}.\<close>

lemma stable_all_ok_remove:
  assumes "post_change \<sigma> \<sigma>' \<and> post_change_remove \<sigma> \<sigma>'"
      and "all_ok s \<sigma>"
    shows "all_ok s \<sigma>'"
  using assms unfolding post_change_remove_def post_change_def all_ok_def
  apply clarsimp
  by (metis (no_types, opaque_lifting) fst_conv snd_conv)

lemma reachable_post_pre:
  assumes assm_step: "post_change \<sigma> \<sigma>'"
      and assm_ok: "all_ok s \<sigma>"
    shows "\<forall> x. reachable \<sigma>' x \<longrightarrow> reachable \<sigma> x"
proof -
  from assm_step have "post_change_remove \<sigma> \<sigma>' \<or> post_change_redirect \<sigma> \<sigma>'"
    unfolding post_change_def by simp
  then show ?thesis
  proof (rule disjE, goal_cases case_remove case_redirect)
    case case_remove
    then show ?case
      unfolding post_change_remove_def reachable_def apply clarsimp
      by (smt (verit, ccfv_SIG) DiffE Diff_insert_absorb assm_step post_change_def
          reach_base reach_induct reach_step reachable_def)
  next
    case case_redirect
    then show ?case
      unfolding post_change_redirect_def reachable_def apply clarsimp
      by (smt (verit, ccfv_SIG) Diff_iff Diff_insert assm_step case_redirect
          insert_Diff_single insert_absorb insert_iff post_change_def reach_base reach_induct
          reach_step reachable_def singletonD singletonI snd_conv)
  qed
qed

text \<open>The @{text all_ok} property and a redirect step by the Mutator together
establishes @{term can_be_marked}.\<close>

lemma stable_can_be_marked_redirect:
  assumes assm_step: "post_change \<sigma> \<sigma>' \<and> post_change_redirect \<sigma> \<sigma>'"
      and assm_ok: "all_ok s \<sigma>"
      and assm_roots_marked: "roots \<sigma> \<subseteq> marked \<sigma>"
    shows "can_be_marked s \<sigma>'"
proof -
  from assm_step have ln_marked_eq: "marked \<sigma>' = marked \<sigma>"
    unfolding post_change_def by simp
  then have "roots \<sigma>' \<subseteq> marked \<sigma>'"
    using assm_step assm_roots_marked unfolding post_change_def by simp

  from assm_step obtain x y z where assm_xyz:
    "hp \<sigma>  - hp \<sigma>' = {(x,y)} \<and>
     hp \<sigma>' - hp \<sigma>  = {(x,z)} \<and>
     reachable \<sigma> x \<and>
     tbm \<sigma>' = Some z \<and>
     reachable \<sigma> z"
    unfolding post_change_redirect_def by force

  show ?thesis
  proof -
    { fix a b assume assm_ab: \<comment> \<open>The assumption-part of @{text can_be_marked}\<close>
        "(a,b) \<in> hp \<sigma>' \<and> (a \<in> marked \<sigma>' \<inter> s) \<and> b \<notin> marked \<sigma>' \<and> reachable \<sigma>' b"

      then have ln_ab: "(a \<in> marked \<sigma> \<inter> s) \<and> b \<notin> marked \<sigma> \<and> reachable \<sigma> b"
        using assm_ab ln_marked_eq reachable_post_pre assm_step assm_ok by blast
  
      \<comment> \<open>The assumptions on @{term "(a,b)"} imply that this edge is exactly
         @{term "(x,z)"} from earlier.\<close>
      then have ln_ab_xy: "(a,b) = (x,z)"
        using assm_ab assm_ok assm_xyz unfolding all_ok_def by fastforce
  
      \<comment> \<open>The node @{term z} must have another parent @{term c}\<close>
      have "z \<in> roots \<sigma> \<or> (\<exists> c. reachable \<sigma> c \<and> (c,z) \<in> hp \<sigma>)"
        using assm_xyz reachable_exists by fast
      moreover have "z \<notin> roots \<sigma>"
        using assm_roots_marked assm_ab ln_ab_xy ln_marked_eq by blast
      ultimately obtain c where ln_c:
        "reachable \<sigma> c \<and> (c,z) \<in> hp \<sigma>"
        by blast
      then have ln_c1: "c \<noteq> x \<and> (c,z) \<in> hp \<sigma>'"
        using assm_xyz by blast

      \<comment> \<open>We now establish the conclusion-part of @{term "can_be_marked s \<sigma>'"},
          using @{term "(c,z)"} as the witness to the existential quantifier.\<close>
      
      \<comment> \<open>Clause 2 of 3, done first because it is needed later\<close>
      have ln_c2: "c \<notin> s \<or> c \<notin> marked \<sigma>'"
        by (metis all_ok_def assm_ab assm_ok ln_ab_xy ln_c ln_marked_eq
            fst_conv snd_conv)
        
      \<comment> \<open>Clause 1 of 3\<close>
      moreover
      have "c \<in> reach (roots \<sigma>') (hp \<sigma>') \<or> c \<in> reach (marked \<sigma>' \<inter> - s) (hp \<sigma>')"
       (is "?Clause1 c")
      proof -
        define Q where "Q = (\<lambda>w. ?Clause1 w \<or> (w \<in> marked \<sigma>' \<and> w \<in> s))"
        have ln_marked_Q: "\<And> w. w \<in> marked \<sigma> \<Longrightarrow> Q w"
          by (metis reach_base assm_step post_change_def IntI Q_def Compl_iff)
        have "\<And> w. reachable \<sigma> w \<Longrightarrow> Q w"
        proof -
          fix w assume assm_reachable: "reachable \<sigma> w"
          show "Q w"
          proof (rule reach_induct[where P=Q and S="roots \<sigma>" and R="hp \<sigma>"],
                 goal_cases)
            case 1
            then show ?case by (meson assm_reachable reachable_def)
          next
            case 2
            then show ?case using assm_roots_marked ln_marked_Q by blast
          next
            case (3 u v)
            assume assm_ln_1: "u \<in> reach (roots \<sigma>) (hp \<sigma>)"
               and assm_ln_2: "Q u"
               and assm_ln_3: "(u,v) \<in> hp \<sigma>"
            have v_r: "reachable \<sigma> v"
              unfolding reachable_def by (rule reach_step[OF assm_ln_1 assm_ln_3])
            show ?case
            proof (cases "(u,v) = (x,y)")
              case True
              then have "v \<in> marked \<sigma>"
                by (metis assm_ab assm_ln_3 assm_ok all_ok_def ln_ab_xy ln_marked_eq
                          Int_iff fst_conv snd_conv)
              then show ?thesis using ln_marked_Q by simp
            next
              case False
              then have "(u,v) \<in> hp \<sigma>'"
                using assm_xyz assm_ln_3 by auto
              moreover have "Q u"
                using assm_ln_2 unfolding Q_def by auto
              ultimately show ?thesis unfolding Q_def
                apply (elim disjE)
                  apply (metis reach_step)
                 apply (metis reach_step)
                by (metis assm_ok all_ok_def assm_ln_3 ln_marked_Q ln_marked_eq
                          Q_def fst_conv snd_conv)
            qed
          qed
        qed \<comment> \<open>for @{theory_text "\<And> w. reachable \<sigma> w \<Longrightarrow> Q w"}\<close>
        then show ?thesis
          using ln_c ln_c2 unfolding Q_def by blast
      qed \<comment> \<open>for Clause 2 of 3\<close>

      \<comment> \<open>Clause 3 of 3\<close>
      moreover have "a \<noteq> c \<and> b = z"
        using ln_ab_xy ln_c1 by blast

      ultimately have "(\<exists> zw \<in> hp \<sigma>'.
              (fst zw \<in> reach (roots \<sigma>') (hp \<sigma>') \<or>
               fst zw \<in> reach (marked \<sigma>' \<inter> - s) (hp \<sigma>')) \<and>
              (fst zw \<notin> s \<or> fst zw \<notin> marked \<sigma>') \<and> a \<noteq> fst zw \<and> b = snd zw)"
        using ln_c1 by force
    }
    then show ?thesis unfolding can_be_marked_def by simp
  qed
qed

lemma stable_can_be_marked_remove:
  assumes "post_change \<sigma> \<sigma>' \<and> post_change_remove \<sigma> \<sigma>'"
      and "all_ok s \<sigma>"
    shows "can_be_marked s \<sigma>'"
  unfolding can_be_marked_def apply clarsimp
  by (metis all_ok_def assms fst_eqD snd_eqD stable_all_ok_remove)

subsection \<open>Lemma 1\<close>

text \<open>This subsection establishes Lemma 1 from the paper, which concerns the
properties that follow from a Mutator change.\<close>

lemma lemma_1_can_be_marked:
  assumes assm_step: "post_change \<sigma> \<sigma>'"
      and assm_all_ok: "all_ok s \<sigma>"
      and assm_roots_marked: "roots \<sigma> \<subseteq> marked \<sigma>"
    shows "can_be_marked s \<sigma>'"
proof -
  from assm_step have "post_change_remove \<sigma> \<sigma>' \<or> post_change_redirect \<sigma> \<sigma>'"
    using post_change_def by fast
  then show ?thesis
  proof (standard, goal_cases remove redirect)
    case remove
    then show ?case
      using stable_can_be_marked_remove 
      by (metis stable_can_be_marked_remove remove assm_step assm_all_ok)
  next
    case redirect
    then show ?case 
      using assms stable_can_be_marked_redirect post_change_def by blast
  qed
qed

lemma lemma_1_tbm_put:
  assumes assm_step:   "post_change \<sigma> \<sigma>'"
      and assm_all_ok: "all_ok s \<sigma>"
    shows "tbm_put s \<sigma>'"
proof -
  have "\<And> xy. xy \<in> hp \<sigma>' \<Longrightarrow> tbm \<sigma>' \<noteq> Some (snd xy) \<Longrightarrow> xy \<in> hp \<sigma>"
  proof -
    fix xy
    assume assm_local_hp: "xy \<in> hp \<sigma>'"
       and assm_local_tbm: "tbm \<sigma>' \<noteq> Some (snd xy)"
    have "post_change_remove \<sigma> \<sigma>' \<or> post_change_redirect \<sigma> \<sigma>'"
      using assm_step unfolding post_change_def by blast
    then show "xy \<in> hp \<sigma>"
      apply standard
      using assm_local_hp post_change_remove_def apply blast
      by (metis assm_local_hp assm_local_tbm post_change_redirect_def
                DiffI singletonD snd_conv)
  qed
  then show ?thesis
    using assm_all_ok assm_step
    unfolding all_ok_def post_change_def tbm_put_def
    by fastforce
qed

lemma lemma_1:
  assumes "post_change \<sigma> \<sigma>'"
      and "all_ok s \<sigma>"
      and "roots \<sigma> \<subseteq> marked \<sigma>"
    shows "can_be_marked s \<sigma>' \<and> tbm_put s \<sigma>'"
  using assms lemma_1_can_be_marked lemma_1_tbm_put by blast

subsection \<open>Lemma 2\<close>

text \<open>This subsection establishes Lemma 2 from the paper: after a Mutator step
that marks @{term tbm} and @{term tbm_put}, either @{term all_ok} holds or the
number of marked nodes increases.\<close>

lemma lemma_2:
  assumes "tbm_put s \<sigma>"
      and "post_mark_tbm \<sigma> \<sigma>'"
    shows "all_ok s \<sigma>' \<or> (marked \<sigma> \<subset> marked \<sigma>')"
  using assms unfolding tbm_put_def post_mark_tbm_def apply clarsimp
  by (metis all_ok_def antisym_conv1 insert_iff option.distinct(1) option.inject
      subset_insertI)

section \<open>Theorems\<close>

subsection \<open>Holds for All\<close>

text \<open>This establishes the @{text forall_guar_p_w} premise when instantiating
the @{text holds_for_all} lemma to the concurrent garbage collector.
Here, @{term p} is @{term "all_ok w \<sigma>"} and @{term q} is
@{text "can_be_marked w \<sigma>' \<or> marked \<sigma> \<subset> marked \<sigma>'"}.\<close>

lemma works_for_all_w:
  assumes "post_change \<sigma> \<sigma>' \<or> post_mark_tbm \<sigma> \<sigma>'"
      and "inv_roots \<sigma>"
      and "all_ok w \<sigma>"
    shows "can_be_marked w \<sigma>' \<or> marked \<sigma> \<subset> marked \<sigma>'"
  by (metis assms all_ok_conseqs inv_roots_def lemma_1 lemma_2)

text \<open>This lemma continues the @{text works_for_all_w} reasoning, 
but with @{text q} extended to include the case where the Collector's
local variables are unchanged and the marking only increases.\<close>

theorem works_for_all_w2:
  assumes "post_change \<sigma> \<sigma>' \<or> post_mark_tbm \<sigma> \<sigma>'"
      and "inv_roots \<sigma>"
      and "all_ok w \<sigma>"
    shows "marked \<sigma> \<subseteq> marked \<sigma>' \<and> localCvar \<sigma> = localCvar \<sigma>' \<and>
           (can_be_marked w \<sigma>' \<or> marked \<sigma> \<subset> marked \<sigma>')"
proof (intro conjI, goal_cases)
  case 1 show ?case
    using assms(1) unfolding post_change_def post_mark_tbm_def by blast
next
  case 2 show ?case
    using assms(1) unfolding post_change_def post_mark_tbm_def by blast
next
  case 3 show ?case
    using assms works_for_all_w by blast
qed

text \<open>This theorem shows that the rely of the Collector holds,
based on the @{theory_text holds_for_all} reasoning.\<close>

theorem using_holds_for_all2:
  assumes "post_change \<sigma> \<sigma>' \<or> post_mark_tbm \<sigma> \<sigma>'"
      and "all_ok s \<sigma>"
      and "\<forall> w. ((post_change \<sigma> \<sigma>' \<or> post_mark_tbm \<sigma> \<sigma>') \<and> all_ok w \<sigma>)
            \<longrightarrow> (marked \<sigma> \<subseteq> marked \<sigma>' \<and> localCvar \<sigma> = localCvar \<sigma>' \<and>
                 (can_be_marked w \<sigma>' \<or> marked \<sigma> \<subset> marked \<sigma>'))"
      and "all_ok s \<sigma> \<and> marked \<sigma> \<subseteq> marked \<sigma>' \<and> localCvar \<sigma> = localCvar \<sigma>' \<and>
           (can_be_marked s \<sigma>' \<or> marked \<sigma> \<subset> marked \<sigma>')
           \<longrightarrow> rely_collector \<sigma> \<sigma>'"
    shows "rely_collector \<sigma> \<sigma>'"
  using assms holds_for_all by force

subsection \<open>Propagate\<close>

lemma chain_mono:
  "\<lbrakk> \<And> m. f m \<subseteq> f (Suc m) ; a \<le> b \<rbrakk> \<Longrightarrow> f a \<subseteq> f b"
  using lift_Suc_mono_le by blast

lemma chain_anti:
  "\<lbrakk> \<And> m. f (Suc m) \<subseteq> f m ; a \<le> b \<rbrakk> \<Longrightarrow> f b \<subseteq> f a"
  using lift_Suc_antimono_le by blast

text \<open>This theorem shows that @{term post_propagate} holds over a sequence of steps, 
where each step either satisfies @{term rely_collector} or @{term guar_collector}, 
and the @{term safe} and @{term consid} sets are initially empty.\<close>

theorem propagate_seq:
    fixes st :: "nat \<Rightarrow> 'a state"
  assumes step: "\<And> m. rely_collector (st m) (st (Suc m))
                    \<or> guar_collector (st m) (st (Suc m))"
      and init_empty: "safe (localCvar (st 0)) = {} \<and>
                     consid (localCvar (st 0)) = {}"
    shows "post_propagate (st 0) (st n)"
proof -
  have init_eq: "safe (localCvar (st 0)) = consid (localCvar (st 0))"
    using init_empty by simp
  have ok0: "all_ok (safe (localCvar (st 0))) (st 0)"
    using init_empty all_ok_def by blast
  have mark_step: "\<And>m. marked (st m) \<subseteq> marked (st (Suc m))"
    by (metis rely_collector_def guar_collector_def local.step)
  have safe_step: "\<And>m. safe (localCvar (st (Suc m))) \<subseteq> safe (localCvar (st m))"
    by (metis rely_collector_def guar_collector_def local.step dual_order.refl)

  have "\<And>x y. (x,y) \<in> hp (st 0) \<Longrightarrow> x \<in> marked (st n) \<Longrightarrow>
                   x \<in> consid (localCvar (st n)) \<Longrightarrow>
                   y \<in> marked (st n) \<or> marked (st 0) \<subset> marked (st n)"
  proof -
    fix x y assume "(x,y) \<in> hp (st 0)"
               and "x \<in> marked (st n)"
               and local_assm3: "x \<in> consid (localCvar (st n))"
    show "y \<in> marked (st n) \<or> marked (st 0) \<subset> marked (st n)"
    proof -
      { assume "\<not> (marked (st 0) \<subset> marked (st n))"
        moreover have "marked (st 0) \<subseteq> marked (st n)"
          by (rule chain_mono[of "\<lambda>m. marked (st m)", OF mark_step, of 0 n]) simp
        ultimately have eqn: "marked (st 0) = marked (st n)"
          by simp

        \<comment> \<open>marked is constant on 0..n\<close>
        have eqm: "\<And>m. m \<le> n \<Longrightarrow> marked (st m) = marked (st 0)"
        proof -
          fix m assume assm: "m \<le> n"
          then have "marked (st m) \<subseteq> marked (st n)"
            by (rule chain_mono[of "\<lambda>m. marked (st m)", OF mark_step, of m n])
          moreover have "marked (st 0) \<subseteq> marked (st m)"
            apply (rule chain_mono[of "\<lambda>m. marked (st m)", OF mark_step, of 0 m])
            by simp
          ultimately show "marked (st m) = marked (st 0)"
            using eqn by blast
        qed

        \<comment> \<open>@{text "safe = consid"} holds at every state up to n, by induction from 0\<close>
        have all_eq: "\<And>m. m \<le> n \<Longrightarrow>
                       safe (localCvar (st m)) = consid (localCvar (st m))"
        proof -
          fix m show "m \<le> n \<Longrightarrow>
                      safe (localCvar (st m)) = consid (localCvar (st m))"
            apply (induction m)
             apply (rule init_eq)
            apply clarsimp
            by (metis rely_collector_def local.step guar_collector_def psubsetE)
        qed

        have "safe (localCvar (st n)) = consid (localCvar (st n))"
          by (rule all_eq[OF order_refl])
        moreover
        have s_down: "safe (localCvar (st n)) \<subseteq> safe (localCvar (st 0))"
          by (rule chain_anti[of "\<lambda>m. safe (localCvar (st m))",
              OF safe_step, of 0 n]) simp
        ultimately have "x \<in> safe (localCvar (st 0))"
          using local_assm3 by auto
        then have "y \<in> marked (st n)"
          using init_empty by blast
      }
      then show ?thesis by blast
    qed
  qed

  then show ?thesis unfolding post_propagate_def by force
qed

subsection \<open>Every Reachable Node Is Marked\<close>

text \<open>This final theorem establishes the overall post condition of the Collector,
that ``if a node is reachable initially, then it has been marked by the Collector.\<close>

theorem reachable_subset_marked:
  assumes assm_post: "post_propagate \<sigma> \<sigma>'"
      and assm_marked: "marked \<sigma>' = marked \<sigma>"
      and assm_roots: "roots \<sigma> \<subseteq> marked \<sigma>"
      and assm_consid: "consid (localCvar \<sigma>') = Field (hp \<sigma>)"
          \<comment> \<open>@{term consid} contains all the nodes in the heap.\<close>
    shows "\<forall> w. reachable \<sigma> w \<longrightarrow> w \<in> marked \<sigma>"
proof (intro allI impI)
  fix w assume "reachable \<sigma> w"
  hence hw: "w \<in> reach (roots \<sigma>) (hp \<sigma>)" unfolding reachable_def .
  show "w \<in> marked \<sigma>"
  proof (rule reach_induct[where P="\<lambda>u. u \<in> marked \<sigma>", OF hw])
    fix u assume "u \<in> roots \<sigma>"
    thus "u \<in> marked \<sigma>" using assm_roots by blast
  next
    fix u v
    assume "u \<in> marked \<sigma>" and "(u,v) \<in> hp \<sigma>"
    moreover from this have "u \<in> marked \<sigma>' \<and> u \<in> consid (localCvar \<sigma>')"
      using assm_marked Field_iff assm_consid by force
    ultimately show "v \<in> marked \<sigma>"
      by (metis assm_marked assm_post post_propagate_def Int_iff psubsetE split_conv)
  qed
qed

end