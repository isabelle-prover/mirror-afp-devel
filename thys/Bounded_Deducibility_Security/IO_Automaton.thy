subsection \<open>IO automata\<close>

text \<open>IO automata are defined. Since they are a particular kind of
transition systems, they inherit the notions of traces and reachability from those.
Various useful concepts and theorems are provided, including
invariants and the multi-step operator.\<close>

(*<*)
theory IO_Automaton
  imports Trivia Transition_System
begin
(*>*)


subsubsection \<open>IO automata as transition systems\<close>

text \<open>In this context, transitions are quadruples consisting of
a source state, an action (input), and output and a target state.\<close>

(* Design decision: transitions, hence traces, include the states too.
This is convenient for manipulating invariants. *)
(* transition: *)
datatype ('state,'act,'out) trans = Trans (srcOf: 'state) (actOf: 'act) (outOf: 'out) (tgtOf: 'state)

lemmas "srcOf_simps" = trans.sel(1)
lemmas "actOf_simps" = trans.sel(2)
lemmas "outOf_simps" = trans.sel(3)
lemmas "tgtOf_simps" = trans.sel(4)

locale IO_Automaton =
fixes istate :: "'state" (* initial step *)
  and step :: "'state \<Rightarrow> 'act \<Rightarrow> 'out * 'state"  (* transition function *)
begin

(* The output and effect of an action on a state: *)
definition out :: "'state \<Rightarrow> 'act \<Rightarrow> 'out" where "out s a \<equiv> fst (step s a)"
definition eff :: "'state \<Rightarrow> 'act \<Rightarrow> 'state" where "eff s a \<equiv> snd (step s a)"

fun validTrans :: "('state,'act,'out) trans \<Rightarrow> bool" where
"validTrans (Trans s a ou s') = (step s a = (ou, s'))"

lemma validTrans:
"validTrans trn =
 (step (srcOf trn) (actOf trn) = (outOf trn, tgtOf trn))"
by (cases trn) auto

sublocale Transition_System
  where istate = istate and validTrans = validTrans and srcOf = srcOf and tgtOf = tgtOf .

lemma reach_step:
  "reach s \<Longrightarrow> reach (snd (step s a))"
  using reach.Step[where trn = "Trans s a ou (snd (step s a))" for ou]
  by (cases "step s a") auto

lemma reach_PairI:
  assumes "reach s" and "step s a = (ou, s')"
  shows "reach s'"
  using assms
  by (auto intro: reach.Step[where trn = "Trans s a ou s'"])

lemma reach_step_induct[consumes 1, case_names Istate Step]:
  assumes s: "reach s"
    and istate: "P istate"
    and step: "\<And>s a. reach s \<Longrightarrow> P s \<Longrightarrow> P (snd (step s a))"
  shows "P s"
proof (use s in induction)
  case Istate
  then show ?case
    by (rule istate)
next
  case (Step s trn s')
  then obtain a ou where "trn = Trans s a ou s'"
    by (cases trn) auto
  then show ?case
    using Step step[of s a]
    by auto
qed

lemma reachFrom_step_induct[consumes 1, case_names Refl Step]:
  assumes s: "reachFrom s s'"
    and refl: "P s"
    and step: "\<And>s' a ou s''. reachFrom s s' \<Longrightarrow> P s' \<Longrightarrow> step s' a = (ou, s'') \<Longrightarrow> P s''"
  shows "P s'"
proof (use s in induction)
  case Refl
  then show ?case
    by (rule refl)
next
  case (Step s' trn s'')
  then obtain a ou where "trn = Trans s' a ou s''"
    by (cases trn) auto
  then show ?case
    using Step step[of s' a ou s'']
    by auto
qed

lemma valid_filter_no_state_change:
  "valid tr \<Longrightarrow> (\<And>trn. trn \<in>\<in> tr \<Longrightarrow> \<not>(PP trn) \<Longrightarrow> srcOf trn = tgtOf trn) \<Longrightarrow>
  \<exists>trn. trn \<in>\<in> tr \<and> PP trn \<Longrightarrow> valid (filter PP tr) \<and> srcOfTr tr = srcOfTr (filter PP tr)
  \<and> tgtOfTr tr = tgtOfTr (filter PP tr)"
proof (induct rule: valid.induct)
  case (Singl trn) then show ?case by auto
next
  case (Cons trn tr) then show ?case
   proof (cases "PP trn")
     case True note * = this show ?thesis
     proof (cases "\<exists>trn. trn \<in>\<in> tr \<and> PP trn")
       case True then show ?thesis using * Cons by fastforce
     next
       case False then show ?thesis
       proof -
        have **: "filter PP tr = []" using False by auto
        show ?thesis
        proof (cases "tr = []")
          case True then show ?thesis using Cons by simp
        next
          case False
            with Cons(3) Cons(5) ** have "srcOfTr tr = tgtOfTr tr"
            proof (induction tr)
              case (Singl a)
                have "\<not> (PP a)" using Singl(3) by auto
                then show ?case using Singl(2) by auto
            next
              case (Cons a as)
              have **: "\<not> (PP a)" using Cons(6) by auto
              then have *: "srcOf a = tgtOf a" using Cons(5) by auto
              show ?case
                proof (cases "as = []")
                  case True with * show ?thesis by simp
                next
                  case False
                    then have "srcOfTr as = tgtOfTr as"  using Cons ** by auto
                    then show ?thesis using * Cons(2) by auto
              qed
            qed
            then show ?thesis using * ** Cons False by simp
        qed
      qed
    qed
  next
    case False then show ?thesis using Cons by auto
  qed
qed

lemma validFrom_validTrans[intro]:
assumes "validTrans (Trans s a ou s')" and "validFrom s' tr"
shows "validFrom s (Trans s a ou s' # tr)"
using assms unfolding validFrom_def by auto

subsubsection \<open>State invariants\<close>

(* holds at the initial state: *)
definition holdsIstate :: "('state \<Rightarrow> bool) \<Rightarrow> bool" where
"holdsIstate \<phi> \<equiv> \<phi> istate"

(* is invariant: *)
definition invar :: "('state \<Rightarrow> bool) \<Rightarrow> bool" where
"invar \<phi> \<equiv> \<forall> s a. reach s \<and> \<phi> s \<longrightarrow> \<phi> (snd (step s a))"

lemma holdsIstate_invar:
  assumes h: "holdsIstate \<phi>" and i: "invar \<phi>" and a: "reach s"
  shows "\<phi> s"
  by (use a in \<open>induction rule: reach_step_induct\<close>)
     (use h i in \<open>auto simp: holdsIstate_def invar_def\<close>)


subsubsection \<open>Traces of actions\<close>

(* The trace given by a state and a ste of actions: *)
fun traceOf :: "'state \<Rightarrow> 'act list \<Rightarrow> ('state,'act,'out) trans trace" where
"traceOf s [] = []"
|
"traceOf s (a # al) =
 (case step s a of (ou,s1) \<Rightarrow> (Trans s a ou s1) # traceOf s1 al)"


(* Multi-step: *)
fun sstep :: "'state \<Rightarrow> 'act list \<Rightarrow> 'out list \<times> 'state" where
"sstep s [] = ([], s)"
|
"sstep s (a # al) = (case step s a of (ou,s') \<Rightarrow> (case sstep s' al of (oul, s'') \<Rightarrow> (ou # oul, s'')))"

lemma length_traceOf[simp]:
"length (traceOf s al) = length al"
by (induct al arbitrary: s) (auto split: prod.splits)

lemma traceOf_Nil[simp]:
"traceOf s al = [] \<longleftrightarrow> al = []"
by (metis length_traceOf length_0_conv)

lemma sstep_outOf_traceOf[simp]:
"sstep s al = (ou,s') \<Longrightarrow> map outOf (traceOf s al) = ou"
by (induct al arbitrary: s ou s') (auto split: prod.splits)

lemma sstep_tgtOf_traceOf[simp]:
"al \<noteq> [] \<Longrightarrow> sstep s al = (ou,s') \<Longrightarrow> tgtOf (last (traceOf s al)) = s'"
by (induct al arbitrary: s ou s') (auto split: prod.splits)

lemma srcOf_traceOf[simp]:
"al \<noteq> [] \<Longrightarrow> srcOf (hd (traceOf s al)) = s"
by (induct al arbitrary: s) (auto split: prod.splits)

lemma actOf_traceOf[simp]:
"map actOf (traceOf s al) = al"
by (induct al arbitrary: s) (auto split: prod.splits)


lemma traceOf_append:
"al \<noteq> [] \<Longrightarrow> s1 = tgtOf (last (traceOf s al)) \<Longrightarrow>
 traceOf s (al @ al1) = traceOf s al @ traceOf s1 al1"
by (induct al arbitrary: s s1 al1) (auto split: prod.splits)

lemma sstep_append:
assumes "sstep s al = (oul,s1)" and "sstep s1 al1 = (oul1,s2)"
shows "sstep s (al @ al1) = (oul @ oul1, s2)"
using assms by (induct al arbitrary: oul s s1 oul1 s2) (auto split: prod.splits)

lemma reach_sstep:
assumes "reach s" and "sstep s al = (ou,s1)"
shows "reach s1"
using assms apply(induction al arbitrary: ou s1 s)
by (auto split: prod.splits) (metis reach_PairI)

(* Alternative simp rules, from the left *)
lemma traceOf_consR[simp]:
assumes "al \<noteq> []" and "s1 = tgtOf (last (traceOf s al))" and "step s1 a = (ou,s2)"
shows "traceOf s (al ## a) = traceOf s al ## Trans s1 a ou s2"
using assms by (induct al arbitrary: s) (auto split: prod.splits)

lemma sstep_consR[simp]:
assumes "sstep s al = (oul,s1)" and "step s1 a = (ou,s2)"
shows "sstep s (al ## a) = (oul ## ou, s2)"
using assms by (induct al arbitrary: oul s s1 ou s2) (auto split: prod.splits)

lemma fst_sstep_consR:
"fst (sstep s (al ## a)) = fst (sstep s al) ## (fst (step (snd (sstep s al)) a))"
by (cases "sstep s al", cases "step (snd (sstep s al)) a") auto

lemma valid_traceOf[simp]: "al \<noteq> [] \<Longrightarrow> valid (traceOf s al)"
proof(induct al arbitrary: s)
  case (Cons a al)
  thus ?case by (cases "al = []") (auto split: prod.splits)
qed auto

lemma validFrom_traceOf[simp]: "validFrom s (traceOf s al)"
by (cases "al = []") auto

lemma validFrom_traceOf2:
  assumes "validFrom s tr"
  shows "tr = traceOf s (map actOf tr)"
  using assms
  by (induction tr arbitrary: s) (auto split: prod.splits simp: validFrom_def elim!: validTrans.elims)

lemma set_traceOf_validTrans:
assumes "trn \<in>\<in> traceOf s al"  shows "validTrans trn"
by (metis assms validFrom_traceOf validFrom_validTrans_set)

lemma traceOf_append_sstep: "traceOf s (al @ al1) = traceOf s al @ traceOf (snd (sstep s al)) al1"
by (induction al arbitrary: s al1) (auto split: prod.splits)

lemma snd_sstep_append: "snd (sstep s (al @ al1)) = snd (sstep (snd (sstep s al)) al1)"
by (cases "sstep s al", cases "sstep (snd (sstep s al)) al1") (auto simp add: sstep_append)

lemma snd_sstep_step_constant:
assumes "\<forall> a. a \<in>\<in> al \<longrightarrow> snd (step s a) = s"
shows "snd (sstep s al) = s"
using assms by (induction al) (auto split: prod.splits)

definition "const_tr tr \<equiv> \<forall>trn. trn \<in>\<in> tr \<longrightarrow> srcOf trn = tgtOf trn"

lemma const_tr_same_src_tgt:
  assumes "valid tr" "const_tr tr"
  shows "srcOfTr tr = tgtOfTr tr"
using assms unfolding const_tr_def by induction auto

lemma traceOf_snoc:
"traceOf s (al ## a) =
  traceOf s al ##
  Trans (snd (sstep s al))
        a
        (fst (step (snd (sstep s al)) a))
        (snd (step (snd (sstep s al)) a))"
by (metis (no_types, lifting) traceOf_Nil traceOf_append_sstep prod.case_eq_if traceOf.simps)

lemma traceOf_append_unfold:
"traceOf s (al1 @ al2) =
 traceOf s al1 @ traceOf (if al1 = [] then s else tgtOf (last (traceOf s al1))) al2"
using traceOf_append by (cases "al1 = []") auto

abbreviation "transOf s a \<equiv> Trans s a (fst (step s a)) (snd (step s a))"

lemma traceOf_Cons: "traceOf s (a # al) = transOf s a # traceOf (snd (step s a)) al"
by (auto split: prod.splits)

(* The notion of two actions commuting: *)
definition "commute s a1 a2
 \<equiv> snd (sstep s [a1, a2]) = snd (sstep s [a2, a1])"

(* The notion of one action absorbing another: *)
definition absorb :: "'state \<Rightarrow> 'act \<Rightarrow> 'act \<Rightarrow> bool" where
"absorb s a1 a2 \<equiv> snd (sstep s [a1, a2]) = snd (step s a2)"

lemma validFrom_commute:
  assumes "validFrom s0 (tr1 @ transOf s a # transOf (snd (step s a)) a' # tr2)"
      and "commute s a a'"
  shows "validFrom s0 (tr1 @ transOf s a' # transOf (snd (step s a')) a # tr2)"
using assms unfolding commute_def by (auto split: prod.splits simp add: validFrom_append validFrom_Cons)

lemma validFrom_absorb:
  assumes "validFrom s0 (tr1 @ transOf s a # transOf (snd (step s a)) a' # tr2)"
      and "absorb s a a'"
  shows "validFrom s0 (tr1 @ transOf s a' # tr2)"
using assms unfolding absorb_def by (auto split: prod.splits simp add: validFrom_append validFrom_Cons)

lemma validTrans_Trans_srcOf_actOf_tgtOf:
"validTrans trn \<Longrightarrow> Trans (srcOf trn) (actOf trn) (outOf trn) (tgtOf trn) = trn"
by (cases trn) auto

lemma validTrans_step_srcOf_actOf_tgtOf:
"validTrans trn \<Longrightarrow> step (srcOf trn) (actOf trn) = (outOf trn, tgtOf trn)"
by (cases trn) auto

lemma sstep_Cons:
"sstep s (a # al) = (fst (step s a) # fst (sstep (snd (step s a)) al), snd (sstep (snd (step s a)) al))"
by (auto split: prod.splits)
declare sstep.simps(2)[simp del]

lemma length_fst_sstep: "length (fst (sstep s al)) = length al"
by (induction al arbitrary: s) (auto simp: sstep_Cons)

(*<*)

end (* locale IO_Automaton *)

end

(*>*)
