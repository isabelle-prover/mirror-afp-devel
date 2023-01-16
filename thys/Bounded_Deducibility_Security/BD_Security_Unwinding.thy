(*<*)
theory BD_Security_Unwinding
  imports BD_Security_IO
begin
(*>*)

section \<open>Unwinding proof method\<close>

text \<open>This section formalizes the unwinding proof method for BD Security discussed in
\<^cite>\<open>\<open>Section 5.1\<close> in "cocon-CAV2014"\<close>\<close>

context BD_Security_IO
begin

definition consume :: "('state,'act,'out) trans \<Rightarrow> 'value list \<Rightarrow> 'value list \<Rightarrow> bool" where
"consume trn vl vl' \<equiv>
 if \<phi> trn then vl \<noteq> [] \<and> f trn = hd vl \<and> vl' = tl vl
 else vl' = vl"

definition consumeList :: "('state,'act,'out) trans trace \<Rightarrow> 'value list \<Rightarrow> 'value list \<Rightarrow> bool" where
"consumeList tr vl vl' \<equiv> vl = (V tr) @ vl'"

lemma length_consume[simp]:
"consume trn vl vl' \<Longrightarrow> length vl' < Suc (length vl)"
unfolding consume_def by (auto split: if_splits)

lemma ex_consume_\<phi>:
assumes "\<not> \<phi> trn"
obtains vl' where "consume trn vl vl'"
using assms unfolding consume_def by auto

lemma ex_consume_NO:
assumes "vl \<noteq> []" and "f trn = hd vl"
obtains vl' where "consume trn vl vl'"
using assms unfolding consume_def by (cases "\<phi> trn") auto

(* independent action: *)
definition iaction where
"iaction \<Delta> s vl s1 vl1 \<equiv>
 \<exists> al1 vl1'.
   let tr1 = traceOf s1 al1; s1' = tgtOf (last tr1) in
   list_ex \<phi> tr1 \<and> consumeList tr1 vl1 vl1' \<and>
   never \<gamma> tr1
   \<and>
   \<Delta> s vl s1' vl1'"

(* Multi-step intro, reflecting the improved def: *)
lemma iactionI_ms[intro?]:
assumes s: "sstep s1 al1 = (oul1, s1')"
and l: "list_ex \<phi> (traceOf s1 al1)"
and "consumeList (traceOf s1 al1) vl1 vl1'"
and "never \<gamma> (traceOf s1 al1)" and "\<Delta> s vl s1' vl1'"
shows "iaction \<Delta> s vl s1 vl1"
proof-
  have "al1 \<noteq> []" using l by auto
  from sstep_tgtOf_traceOf[OF this s] assms
  show ?thesis unfolding iaction_def by auto
qed

lemma sstep_eq_singleiff[simp]: "sstep s1 [a1] = ([ou1], s1') \<longleftrightarrow> step s1 a1 = (ou1, s1')"
using sstep_Cons by auto

(* The less expressive, single-step intro: *)
lemma iactionI[intro?]:
assumes "step s1 a1 = (ou1, s1')" and "\<phi> (Trans s1 a1 ou1 s1')"
and "consume (Trans s1 a1 ou1 s1') vl1 vl1'"
and "\<not> \<gamma> (Trans s1 a1 ou1 s1')" and "\<Delta> s vl s1' vl1'"
shows "iaction \<Delta> s vl s1 vl1"
using assms
by (intro iactionI_ms[of _ "[a1]" "[ou1]"]) (auto simp: consume_def consumeList_def)

definition match where
"match \<Delta> s s1 vl1 a ou s' vl' \<equiv>
 \<exists> al1 vl1'.
    let trn = Trans s a ou s'; tr1 = traceOf s1 al1; s1' = tgtOf (last tr1) in
    al1 \<noteq> [] \<and> consumeList tr1 vl1 vl1' \<and>
    O tr1 = O [trn] \<and>
    \<Delta> s' vl' s1' vl1'"

lemma matchI_ms[intro?]:
assumes s: "sstep s1 al1 = (oul1, s1')"
and l: "al1 \<noteq> []"
and "consumeList (traceOf s1 al1) vl1 vl1'"
and "O (traceOf s1 al1) = O [Trans s a ou s']"
and "\<Delta> s' vl' s1' vl1'"
shows "match \<Delta> s s1 vl1 a ou s' vl'"
proof-
  from sstep_tgtOf_traceOf[OF l s] assms
  show ?thesis unfolding match_def by (intro exI[of _ al1]) auto
qed

lemma matchI[intro?]:
assumes "validTrans (Trans s1 a1 ou1 s1')"
and "consume (Trans s1 a1 ou1 s1') vl1 vl1'" and "\<gamma> (Trans s a ou s') = \<gamma> (Trans s1 a1 ou1 s1')"
and "\<gamma> (Trans s a ou s') \<Longrightarrow> g (Trans s a ou s') = g (Trans s1 a1 ou1 s1')"
and "\<Delta> s' vl' s1' vl1'"
shows "match \<Delta> s s1 vl1 a ou s' vl'"
using assms by (intro matchI_ms[of s1 "[a1]" "[ou1]" s1'])
               (auto simp: consume_def consumeList_def split: if_splits)

definition ignore where
"ignore \<Delta> s s1 vl1 a ou s' vl' \<equiv>
 \<not> \<gamma> (Trans s a ou s') \<and>
 \<Delta> s' vl' s1 vl1"

lemma ignoreI[intro?]:
assumes "\<not> \<gamma> (Trans s a ou s')" and "\<Delta> s' vl' s1 vl1"
shows "ignore \<Delta> s s1 vl1 a ou s' vl'"
unfolding ignore_def using assms by auto

(* reaction: *)
definition reaction where
"reaction \<Delta> s vl s1 vl1 \<equiv>
 \<forall> a ou s' vl'.
   let trn = Trans s a ou s' in
   validTrans trn \<and> \<not> T trn \<and>
   consume trn vl vl'
   \<longrightarrow>
   match \<Delta> s s1 vl1 a ou s' vl'
   \<or>
   ignore \<Delta> s s1 vl1 a ou s' vl'"

lemma reactionI[intro?]:
assumes
"\<And>a ou s' vl'.
   \<lbrakk>step s a = (ou, s'); \<not> T (Trans s a ou s');
    consume (Trans s a ou s') vl vl'\<rbrakk>
   \<Longrightarrow>
   match \<Delta> s s1 vl1 a ou s' vl' \<or> ignore \<Delta> s s1 vl1 a ou s' vl'"
shows "reaction \<Delta> s vl s1 vl1"
using assms unfolding reaction_def by auto

definition "exit" :: "'state \<Rightarrow> 'value \<Rightarrow> bool" where
"exit s v \<equiv> \<forall> tr trn. validFrom s (tr ## trn) \<and> never T (tr ## trn) \<and> \<phi> trn \<longrightarrow> f trn \<noteq> v"

lemma exit_coind:
assumes K: "K s"
and I: "\<And> trn. \<lbrakk>K (srcOf trn); validTrans trn; \<not> T trn\<rbrakk>
        \<Longrightarrow> (\<phi> trn \<longrightarrow> f trn \<noteq> v) \<and> K (tgtOf trn)"
shows "exit s v"
using K unfolding exit_def proof(intro allI conjI impI)
  fix tr trn assume "K s" and "validFrom s (tr ## trn) \<and> never T (tr ## trn) \<and> \<phi> trn"
  thus "f trn \<noteq> v"
  using I unfolding validFrom_def by (induction tr arbitrary: s trn)
  (auto, metis neq_Nil_conv rotate1.simps(2) rotate1_is_Nil_conv valid_ConsE)
qed

definition noVal where
"noVal K v \<equiv>
 \<forall> s a ou s'. reachNT s \<and> K s \<and> step s a = (ou,s') \<and> \<phi> (Trans s a ou s') \<longrightarrow> f (Trans s a ou s') \<noteq> v"

lemma noVal_disj:
assumes "noVal Inv1 v" and "noVal Inv2 v"
shows "noVal (\<lambda> s. Inv1 s \<or> Inv2 s) v"
using assms unfolding noVal_def by metis

lemma noVal_conj:
assumes "noVal Inv1 v" and "noVal Inv2 v"
shows "noVal (\<lambda> s. Inv1 s \<and> Inv2 s) v"
using assms unfolding noVal_def by blast

(* Often encountered sufficient criterion for noVal: *)
definition no\<phi> where
"no\<phi> K \<equiv> \<forall> s a ou s'. reachNT s \<and> K s \<and> step s a = (ou,s') \<longrightarrow> \<not> \<phi> (Trans s a ou s')"

lemma no\<phi>_noVal: "no\<phi> K \<Longrightarrow> noVal K v"
unfolding no\<phi>_def noVal_def by auto

(* intro rule for quick inline checks: *)
lemma exitI[consumes 2, induct pred: "exit"]:
assumes rs: "reachNT s" and K: "K s"
and I:
"\<And> s a ou s'.
   \<lbrakk>reach s; reachNT s; step s a = (ou,s'); K s\<rbrakk>
   \<Longrightarrow> (\<phi> (Trans s a ou s') \<longrightarrow> f (Trans s a ou s') \<noteq> v) \<and> K s'"
shows "exit s v"
proof-
  let ?K = "\<lambda> s. reachNT s \<and> K s"
  show ?thesis using assms by (intro exit_coind[of ?K])
  (metis reachNT_reach IO_Automaton.validTrans reachNT.Step trans.exhaust_sel)+
qed

(* intro rule for more elaborate checks: *)
lemma exitI2:
assumes rs: "reachNT s" and K: "K s"
and "invarNT K" and "noVal K v"
shows "exit s v"
proof-
  let ?K = "\<lambda> s. reachNT s \<and> K s"
  show ?thesis using assms unfolding invarNT_def noVal_def apply(intro exit_coind[of ?K])
  by metis (metis IO_Automaton.validTrans reachNT.Step trans.exhaust_sel)
qed

(* Binary version of the invariant: *)
definition noVal2 where
"noVal2 K v \<equiv>
 \<forall> s a ou s'. reachNT s \<and> K s v \<and> step s a = (ou,s') \<and> \<phi> (Trans s a ou s') \<longrightarrow> f (Trans s a ou s') \<noteq> v"

lemma noVal2_disj:
assumes "noVal2 Inv1 v" and "noVal2 Inv2 v"
shows "noVal2 (\<lambda> s v. Inv1 s v \<or> Inv2 s v) v"
using assms unfolding noVal2_def by metis

lemma noVal2_conj:
assumes "noVal2 Inv1 v" and "noVal2 Inv2 v"
shows "noVal2 (\<lambda> s v. Inv1 s v \<and> Inv2 s v) v"
using assms unfolding noVal2_def by blast

lemma noVal_noVal2: "noVal K v \<Longrightarrow> noVal2 (\<lambda> s v. K s) v"
unfolding noVal_def noVal2_def by auto

lemma exitI_noVal2[consumes 2, induct pred: "exit"]:
assumes rs: "reachNT s" and K: "K s v"
and I:
"\<And> s a ou s'.
   \<lbrakk>reach s; reachNT s; step s a = (ou,s'); K s v\<rbrakk>
   \<Longrightarrow> (\<phi> (Trans s a ou s') \<longrightarrow> f (Trans s a ou s') \<noteq> v) \<and> K s' v"
shows "exit s v"
proof-
  let ?K = "\<lambda> s. reachNT s \<and> K s v"
  show ?thesis using assms by (intro exit_coind[of ?K])
  (metis reachNT_reach IO_Automaton.validTrans reachNT.Step trans.exhaust_sel)+
qed

lemma exitI2_noVal2:
assumes rs: "reachNT s" and K: "K s v"
and "invarNT (\<lambda> s. K s v)" and "noVal2 K v"
shows "exit s v"
proof-
  let ?K = "\<lambda> s. reachNT s \<and> K s v"
  show ?thesis using assms unfolding invarNT_def noVal2_def
  by (intro exit_coind[of ?K]) (metis IO_Automaton.validTrans reachNT.Step trans.exhaust_sel)+
qed

(* end binary version *)

lemma exit_validFrom:
assumes vl: "vl \<noteq> []" and i: "exit s (hd vl)" and v: "validFrom s tr" and V: "V tr = vl"
and T: "never T tr"
shows False
using i v V T proof(induction tr arbitrary: s)
  case Nil thus ?case by (metis V_simps(1) vl)
next
  case (Cons trn tr s)
  show ?case
  proof(cases "\<phi> trn")
    case True
    hence "f trn = hd vl" using Cons by (metis V_simps(3) hd_Cons_tl list.inject vl)
    moreover have "validFrom s [trn]" using \<open>validFrom s (trn # tr)\<close>
    unfolding validFrom_def by auto
    ultimately show ?thesis using Cons True unfolding exit_def
    by (elim allE[of _ "[]"]) auto
  next
    case False
    hence "V tr = vl" using Cons by auto
    moreover have "never T tr" by (metis Cons.prems list_all_simps)
    moreover from \<open>validFrom s (trn # tr)\<close> have "validFrom (tgtOf trn) tr" and s: "s = srcOf trn"
    by (metis list.distinct(1) validFrom_def valid_ConsE Cons.prems(2)
              validFrom_def list.discI list.sel(1))+
    moreover have "exit (tgtOf trn) (hd vl)" using \<open>exit s (hd vl)\<close>
    unfolding exit_def s by simp
    (metis (no_types) Cons.prems(2) Cons.prems(4) append_Cons list.sel(1)
           list.distinct list_all_simps valid.Cons validFrom_def valid_ConsE)
    ultimately show ?thesis using Cons(1) by auto
  qed
qed

definition unwind where
"unwind \<Delta> \<equiv>
 \<forall> s vl s1 vl1.
   reachNT s \<and> reach s1 \<and> \<Delta> s vl s1 vl1
   \<longrightarrow>
   (vl \<noteq> [] \<and> exit s (hd vl))
   \<or>
   iaction \<Delta> s vl s1 vl1
   \<or>
   ((vl \<noteq> [] \<or> vl1 = []) \<and> reaction \<Delta> s vl s1 vl1)"

lemma unwindI[intro?]:
assumes
"\<And> s vl s1 vl1.
   \<lbrakk>reachNT s; reach s1; \<Delta> s vl s1 vl1\<rbrakk>
   \<Longrightarrow>
   (vl \<noteq> [] \<and> exit s (hd vl))
   \<or>
   iaction \<Delta> s vl s1 vl1
   \<or>
   ((vl \<noteq> [] \<or> vl1 = []) \<and> reaction \<Delta> s vl s1 vl1)"
shows "unwind \<Delta>"
using assms unfolding unwind_def by auto

lemma unwind_trace:
assumes unwind: "unwind \<Delta>" and "reachNT s" and "reach s1" and "\<Delta> s vl s1 vl1"
and "validFrom s tr" and "never T tr" and "V tr = vl"
shows "\<exists>tr1. validFrom s1 tr1 \<and> O tr1 = O tr \<and> V tr1 = vl1"
proof-
  let ?S = "\<lambda> tr vl1.
  \<forall> s vl s1. reachNT s \<and> reach s1 \<and> \<Delta> s vl s1 vl1 \<and> validFrom s tr \<and> never T tr \<and> V tr = vl \<longrightarrow>
          (\<exists>tr1. validFrom s1 tr1 \<and> O tr1 = O tr \<and> V tr1 = vl1)"
  let ?f = "\<lambda> tr vl1. length tr + length vl1"
  have "?S tr vl1"
  proof(induct rule: measure_induct2[of ?f ?S])
    case (IH tr vl1)
    show ?case
    proof(intro allI impI, elim conjE)
      fix s vl s1 assume rs: "reachNT s" and rs1: "reach s1" and \<Delta>: "\<Delta> s vl s1 vl1"
      and v: "validFrom s tr" and NT: "never T tr" and V: "V tr = vl"
      hence "(vl \<noteq> [] \<and> exit s (hd vl)) \<or>
             iaction \<Delta> s vl s1 vl1 \<or>
             (reaction \<Delta> s vl s1 vl1 \<and> \<not> iaction \<Delta> s vl s1 vl1)"
      (is "?exit \<or> ?iact \<or> ?react \<and> _")
      using unwind unfolding unwind_def by metis
      thus "\<exists>tr1. validFrom s1 tr1 \<and> O tr1 = O tr \<and> V tr1 = vl1"
      proof safe
        assume "vl \<noteq> []" and "exit s (hd vl)"
        hence False using v V exit_validFrom NT by auto
        thus ?thesis by auto
      next
        assume ?iact
        thus ?thesis  unfolding iaction_def Let_def proof safe
          fix al1 :: "'act list" and vl1'
          let ?tr1 = "traceOf s1 al1"  let ?s1' = "tgtOf (last ?tr1)"
          assume \<phi>1: "list_ex \<phi> (traceOf s1 al1)" and c: "consumeList ?tr1 vl1 vl1'"
             and \<gamma>: "never \<gamma> ?tr1" and \<Delta>: "\<Delta> s vl ?s1' vl1'"
          from \<phi>1 have tr1: "?tr1 \<noteq> []" and len_V1: "length (V ?tr1) > 0"
            by (auto iff: list_ex_iff_length_V)
          with c have "length vl1' < length vl1" unfolding consumeList_def by auto
          moreover have "reach ?s1'" using rs1 tr1 by (intro validFrom_reach) auto
          ultimately obtain tr1' where "validFrom ?s1' tr1'" and "O tr1' = O tr" and "V tr1' = vl1'"
            using IH[of tr vl1'] rs \<Delta> v NT V by auto
          then show ?thesis using tr1 \<gamma> c unfolding consumeList_def
            by (intro exI[of _ "?tr1 @ tr1'"])
               (auto simp: O_append O_Nil_never V_append validFrom_append)
        qed
      next
        assume react: ?react and iact: "\<not> ?iact"
        show ?thesis
        proof(cases tr)
          case Nil note tr = Nil
          hence vl: "vl = []" using V by simp
          show ?thesis proof(cases vl1)
            case Nil note vl1 = Nil
            show ?thesis using IH[of tr vl1] \<Delta> V NT V unfolding tr vl1 by auto
          next
            case Cons
            hence False using vl unwind rs rs1 \<Delta> iact unfolding unwind_def by auto
            thus ?thesis by auto
          qed
        next
          case (Cons trn tr') note tr = Cons
          show ?thesis
          proof(cases trn)
            case (Trans ss a ou s') note trn = Trans let ?trn = "Trans s a ou s'"
            have ss: "ss = s" using trn v unfolding tr validFrom_def by auto
            have Ta: "\<not> T ?trn" and s: "s = srcOf trn" and vtrans: "validTrans ?trn"
            and v': "validFrom s' tr'" and NT': "never T tr'"
            using v NT V unfolding tr validFrom_def trn by auto
            have rs': "reachNT s'" using rs vtrans Ta by (auto intro: reachNT_PairI)
            {assume "\<phi> ?trn" hence "vl \<noteq> [] \<and> f ?trn = hd vl" using V unfolding tr trn ss by auto
            }
            then obtain vl' where c: "consume ?trn vl vl'"
            using ex_consume_\<phi> ex_consume_NO by metis
            have V': "V tr' = vl'" using V c unfolding tr trn ss consume_def
            by (cases "\<phi> ?trn") (simp_all, metis list.sel(2-3))
            have "match \<Delta> s s1 vl1 a ou s' vl' \<or> ignore \<Delta> s s1 vl1 a ou s' vl'" (is "?match \<or> ?ignore")
            using react unfolding reaction_def using vtrans Ta c by auto
            thus ?thesis proof safe
              assume ?match
              thus ?thesis unfolding match_def Let_def proof (elim exE conjE)
                fix al1 :: "'act list" and vl1'
                let ?tr = "traceOf s1 al1"
                let ?s1' = "tgtOf (last ?tr)"
                assume al1: "al1 \<noteq> []"
                   and c: "consumeList ?tr vl1 vl1'"
                   and O: "O ?tr = O [Trans s a ou s']"
                   and \<Delta>: "\<Delta> s' vl' ?s1' vl1'"
                from c have len: "length tr' + length vl1' < length tr + length vl1"
                  using tr unfolding consumeList_def by auto
                have "reach ?s1'" using rs1 al1 by (intro validFrom_reach) auto
                then obtain tr1' where "validFrom ?s1' tr1'" and "O tr1' = O tr'" and "V tr1' = vl1'"
                  using IH[OF len] rs' \<Delta> v' NT' V' tr by auto
                then show ?thesis using c O al1 unfolding consumeList_def tr trn ss
                  by (intro exI[of _ "?tr @ tr1'"])
                     (cases "\<gamma> ?trn"; auto simp: O_append O_Nil_never V_append validFrom_append)
              qed
            next
              assume ?ignore
              thus ?thesis unfolding ignore_def Let_def proof (elim exE conjE)
                assume \<gamma>: "\<not> \<gamma> ?trn" and \<Delta>: "\<Delta> s' vl' s1 vl1"
                obtain tr1 where v1: "validFrom s1 tr1" and O: "O tr1 = O tr'" and V: "V tr1 = vl1"
                using IH[of tr' vl1] rs' rs1 \<Delta> v' NT' V' c unfolding tr by auto
                show ?thesis
                apply(intro exI[of _ tr1])
                using v1 O V \<gamma> unfolding tr trn ss by auto
              qed
            qed
          qed
        qed
      qed
    qed
  qed
  thus ?thesis using assms by auto
qed

theorem unwind_secure:
assumes init: "\<And> vl vl1. B vl vl1 \<Longrightarrow> \<Delta> istate vl istate vl1"
and unwind: "unwind \<Delta>"
shows secure
using assms unwind_trace unfolding secure_def by (blast intro: reach.Istate reachNT.Istate)

end (* locale BD_Security_IO *)

(*<*)
end
(*>*)
