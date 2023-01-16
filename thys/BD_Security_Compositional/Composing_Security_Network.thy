section \<open>N-ary compositionality theorem\<close>

text \<open>This theory provides the n-ary version of
the compositionality theorem for BD security.
It corresponds to Theorem 3 from \<^cite>\<open>"cosmedis-SandP2017"\<close>
and to Theorem 7 (the System Compositionality Theorem, n-ary case) from
\<^cite>\<open>"BDsecurity-ITP2021"\<close>.
\<close>

theory Composing_Security_Network
imports Trivial_Security Transporting_Security Composing_Security
begin

text \<open>Definition of n-ary system composition:\<close>

type_synonym ('nodeid, 'state) nstate = "'nodeid \<Rightarrow> 'state"
datatype ('nodeid, 'state, 'trans) ntrans =
  LTrans "('nodeid, 'state) nstate" 'nodeid 'trans
| CTrans "('nodeid, 'state) nstate" 'nodeid 'trans 'nodeid 'trans
datatype ('nodeid, 'obs) nobs = LObs 'nodeid 'obs | CObs 'nodeid 'obs 'nodeid 'obs
datatype ('nodeid, 'val) nvalue = LVal 'nodeid 'val | CVal 'nodeid 'val 'nodeid 'val
datatype com = Send | Recv | Internal

locale TS_Network =
fixes
   istate :: "('nodeid, 'state) nstate" and validTrans :: "'nodeid \<Rightarrow> 'trans \<Rightarrow> bool"
 and
   srcOf :: "'nodeid \<Rightarrow> 'trans \<Rightarrow> 'state" and tgtOf :: "'nodeid \<Rightarrow> 'trans \<Rightarrow> 'state"
 and
   nodes :: "'nodeid set"
 and
   comOf :: "'nodeid \<Rightarrow> 'trans \<Rightarrow> com"
 and
   tgtNodeOf :: "'nodeid \<Rightarrow> 'trans \<Rightarrow> 'nodeid"
 and
   sync :: "'nodeid \<Rightarrow> 'trans \<Rightarrow> 'nodeid \<Rightarrow> 'trans \<Rightarrow> bool"
assumes
   finite_nodes: "finite nodes"
and
  isCom_tgtNodeOf: "\<And>nid trn.
    \<lbrakk>validTrans nid trn; comOf nid trn = Send \<or> comOf nid trn = Recv;
    Transition_System.reach (istate nid) (validTrans nid) (srcOf nid) (tgtOf nid) (srcOf nid trn)\<rbrakk>
    \<Longrightarrow> tgtNodeOf nid trn \<noteq> nid"
begin

abbreviation isCom :: "'nodeid \<Rightarrow> 'trans \<Rightarrow> bool"
where "isCom nid trn \<equiv> (comOf nid trn = Send \<or> comOf nid trn = Recv) \<and> tgtNodeOf nid trn \<in> nodes"

abbreviation lreach :: "'nodeid \<Rightarrow> 'state \<Rightarrow> bool"
where "lreach nid s \<equiv> Transition_System.reach (istate nid) (validTrans nid) (srcOf nid) (tgtOf nid) s"

text \<open>Two types of valid transitions in the network:

       \<^item> Local transitions of network nodes, i.e. transitions that are not communicating
         (with another node in the network. There might be external communication transitions
         with the outside world. These are kept as local transitions, and turn into
         synchronized communication transitions when the target node joins the network during
         the inductive proofs later on.)

       \<^item> Communication transitions between two network nodes; these are allowed if they are
         synchronized.\<close>

fun nValidTrans :: "('nodeid, 'state, 'trans) ntrans \<Rightarrow> bool" where
  Local: "nValidTrans (LTrans s nid trn) =
     (validTrans nid trn \<and> srcOf nid trn = s nid \<and> nid \<in> nodes \<and> \<not>isCom nid trn)"
| Comm: "nValidTrans (CTrans s nid1 trn1 nid2 trn2) =
     (validTrans nid1 trn1 \<and> srcOf nid1 trn1 = s nid1 \<and> comOf nid1 trn1 = Send \<and> tgtNodeOf nid1 trn1 = nid2 \<and>
      validTrans nid2 trn2 \<and> srcOf nid2 trn2 = s nid2 \<and> comOf nid2 trn2 = Recv \<and> tgtNodeOf nid2 trn2 = nid1 \<and>
      nid1 \<in> nodes \<and> nid2 \<in> nodes \<and> nid1 \<noteq> nid2 \<and>
      sync nid1 trn1 nid2 trn2)"

fun nSrcOf :: "('nodeid, 'state, 'trans) ntrans \<Rightarrow> ('nodeid, 'state) nstate" where
  "nSrcOf (LTrans s nid trn) = s"
| "nSrcOf (CTrans s nid1 trn1 nid2 trn2) = s"

fun nTgtOf :: "('nodeid, 'state, 'trans) ntrans \<Rightarrow> ('nodeid, 'state) nstate" where
  "nTgtOf (LTrans s nid trn) = s(nid := tgtOf nid trn)"
| "nTgtOf (CTrans s nid1 trn1 nid2 trn2) = s(nid1 := tgtOf nid1 trn1, nid2 := tgtOf nid2 trn2)"

sublocale Transition_System istate nValidTrans nSrcOf nTgtOf .

fun nSrcOfTrFrom where
  "nSrcOfTrFrom s [] = s"
| "nSrcOfTrFrom s (trn # tr) = nSrcOf trn"

lemma nSrcOfTrFrom_nSrcOf_hd:
  "tr \<noteq> [] \<Longrightarrow> nSrcOfTrFrom s tr = nSrcOf (hd tr)"
  by (cases tr) auto

fun nTgtOfTrFrom where
  "nTgtOfTrFrom s [] = s"
| "nTgtOfTrFrom s (trn # tr) = nTgtOfTrFrom (nTgtOf trn) tr"

lemma nTgtOfTrFrom_nTgtOf_last:
  "tr \<noteq> [] \<Longrightarrow> nTgtOfTrFrom s tr = nTgtOf (last tr)"
  by (induction s tr rule: nTgtOfTrFrom.induct) auto

lemma reach_lreach:
assumes "reach s"
obtains "lreach nid (s nid)"
proof -
  interpret Node: Transition_System "istate nid" "validTrans nid" "srcOf nid" "tgtOf nid" .
  from assms that show thesis
  proof induction
    case Istate then show thesis using Node.reach.Istate by auto
  next
    case (Step s trn s')
      show thesis proof (rule Step.IH)
        assume "Node.reach (s nid)"
        then show thesis using Step.hyps Node.reach.Step[of "s nid" _ "s' nid"]
          by (intro Step.prems, cases trn) (auto)
      qed
  qed
qed

text \<open>Alternative characterization of valid network traces as composition of valid node traces.\<close>

inductive comp :: "('nodeid, 'state) nstate \<Rightarrow> ('nodeid, 'state, 'trans) ntrans list \<Rightarrow> bool"
where
  Nil: "comp s []"
| Local: "\<And>s trn s' tr nid.
    \<lbrakk>comp s tr; tgtOf nid trn = s nid; s' = s(nid := srcOf nid trn); nid \<in> nodes; \<not>isCom nid trn\<rbrakk>
    \<Longrightarrow> comp s' (LTrans s' nid trn # tr)"
| Comm: "\<And>s trn1 trn2 s' tr nid1 nid2.
    \<lbrakk>comp s tr; tgtOf nid1 trn1 = s nid1; tgtOf nid2 trn2 = s nid2;
    s' = s(nid1 := srcOf nid1 trn1, nid2 := srcOf nid2 trn2);
    nid1 \<in> nodes; nid2 \<in> nodes; nid1 \<noteq> nid2;
    comOf nid1 trn1 = Send; tgtNodeOf nid1 trn1 = nid2;
    comOf nid2 trn2 = Recv; tgtNodeOf nid2 trn2 = nid1;
    sync nid1 trn1 nid2 trn2\<rbrakk>
    \<Longrightarrow> comp s' (CTrans s' nid1 trn1 nid2 trn2 # tr)"

abbreviation lValidFrom :: "'nodeid \<Rightarrow> 'state \<Rightarrow> 'trans list \<Rightarrow> bool" where
  "lValidFrom nid \<equiv> Transition_System.validFrom (validTrans nid) (srcOf nid) (tgtOf nid)"

fun decomp where
  "decomp (LTrans s nid' trn' # tr) nid = (if nid' = nid then trn' # decomp tr nid else decomp tr nid)"
| "decomp (CTrans s nid1 trn1 nid2 trn2 # tr) nid = (if nid1 = nid then trn1 # decomp tr nid else
                                                    (if nid2 = nid then trn2 # decomp tr nid else
                                                     decomp tr nid))"
| "decomp [] nid = []"

lemma decomp_append: "decomp (tr1 @ tr2) nid = decomp tr1 nid @ decomp tr2 nid"
proof (induction tr1)
  case (Cons trn tr1) then show ?case by (cases trn) auto
qed auto

lemma validFrom_comp: "validFrom s tr \<Longrightarrow> comp s tr"
proof (induction tr arbitrary: s)
  case Nil show ?case by (intro comp.Nil)
next
  case (Cons trn tr s)
  then have IH: "comp (nTgtOf trn) tr" by (auto simp: validFrom_Cons)
  then show ?case using Cons.prems by (cases trn) (auto simp: validFrom_Cons intro: comp.intros)
qed

lemma validFrom_lValidFrom:
assumes "validFrom s tr"
shows "lValidFrom nid (s nid) (decomp tr nid)"
proof -
  interpret Node: Transition_System "istate nid" "validTrans nid" "srcOf nid" "tgtOf nid" .
  from assms show ?thesis proof (induction tr arbitrary: s)
    case (Cons trn tr)
      have "lValidFrom nid (nTgtOf trn nid) (decomp tr nid)"
        using Cons.prems by (intro Cons.IH) (auto simp: validFrom_Cons)
      then show ?case using Cons.prems by (cases trn) (auto simp: validFrom_Cons Node.validFrom_Cons)
  qed auto
qed

lemma comp_validFrom:
assumes "comp s tr" and "\<And>nid. lValidFrom nid (s nid) (decomp tr nid)"
shows "validFrom s tr"
using assms proof induction
  case (Local s trn s' tr nid)
  interpret Node: Transition_System "istate nid" "validTrans nid" "srcOf nid" "tgtOf nid" .
  have "Node.validFrom (s' nid) (decomp (LTrans s' nid trn # tr) nid)" using Local by blast
  then have "nValidTrans (LTrans s' nid trn)" using Local by (auto simp: Node.validFrom_Cons)
  moreover have "validFrom s tr" proof (intro Local.IH)
    fix nid'
    have "lValidFrom nid' (s' nid') (decomp (LTrans s' nid trn # tr) nid')" using Local(7) .
    then show "lValidFrom nid' (s nid') (decomp tr nid')" using Local(2,3)
      by (cases "nid' = nid") (auto split: if_splits simp: Node.validFrom_Cons)
  qed
  ultimately show ?case using Local(2,3) unfolding validFrom_Cons by auto
next
  case (Comm s trn1 trn2 s' tr nid1 nid2)
  interpret Node1: Transition_System "istate nid1" "validTrans nid1" "srcOf nid1" "tgtOf nid1" .
  interpret Node2: Transition_System "istate nid2" "validTrans nid2" "srcOf nid2" "tgtOf nid2" .
  have "Node1.validFrom (s' nid1) (decomp (CTrans s' nid1 trn1 nid2 trn2 # tr) nid1)"
   and "Node2.validFrom (s' nid2) (decomp (CTrans s' nid1 trn1 nid2 trn2 # tr) nid2)" using Comm by blast+
  then have "nValidTrans (CTrans s' nid1 trn1 nid2 trn2)" using Comm
    by (auto simp: Node1.validFrom_Cons Node2.validFrom_Cons)
  moreover have "validFrom s tr" proof (intro Comm.IH)
    fix nid'
    have "lValidFrom nid' (s' nid') (decomp (CTrans s' nid1 trn1 nid2 trn2 # tr) nid')" using Comm(14) .
    then show "lValidFrom nid' (s nid') (decomp tr nid')"
      using Comm(2,3,4) Node1.validFrom_Cons Node2.validFrom_Cons
      by (cases "nid' = nid1 \<or> nid' = nid2") (auto split: if_splits)
  qed
  ultimately show ?case using Comm(2,3,4) unfolding validFrom_Cons by auto
qed auto


lemma validFrom_iff_comp:
"validFrom s tr \<longleftrightarrow> comp s tr \<and> (\<forall>nid. lValidFrom nid (s nid) (decomp tr nid))"
using validFrom_comp validFrom_lValidFrom comp_validFrom by blast

end

locale Empty_TS_Network = TS_Network where nodes = "{}"
begin

lemma nValidTransE: "nValidTrans trn \<Longrightarrow> P" by (cases trn) auto
lemma validE: "valid tr \<Longrightarrow> P" by (induction rule: valid.induct) (auto elim: nValidTransE)
lemma validFrom_iff_Nil: "validFrom s tr \<longleftrightarrow> tr = []" unfolding validFrom_def by (auto elim: validE)
lemma reach_istate: "reach s \<Longrightarrow> s = istate" by (induction rule: reach.induct) (auto elim: nValidTransE)

end

text \<open>Definition of n-ary security property composition:\<close>

locale BD_Security_TS_Network = TS_Network istate validTrans srcOf tgtOf nodes comOf tgtNodeOf sync
for
   istate :: "('nodeid, 'state) nstate" and validTrans :: "'nodeid \<Rightarrow> 'trans \<Rightarrow> bool"
 and
   srcOf :: "'nodeid \<Rightarrow> 'trans \<Rightarrow> 'state" and tgtOf :: "'nodeid \<Rightarrow> 'trans \<Rightarrow> 'state"
 and
   nodes :: "'nodeid set"
 and
   comOf :: "'nodeid \<Rightarrow> 'trans \<Rightarrow> com"
 and
   tgtNodeOf :: "'nodeid \<Rightarrow> 'trans \<Rightarrow> 'nodeid"
 and
   sync :: "'nodeid \<Rightarrow> 'trans \<Rightarrow> 'nodeid \<Rightarrow> 'trans \<Rightarrow> bool"
+
fixes
   \<phi> :: "'nodeid \<Rightarrow> 'trans \<Rightarrow> bool" and f :: "'nodeid \<Rightarrow> 'trans \<Rightarrow> 'val"
 and
   \<gamma> :: "'nodeid \<Rightarrow> 'trans \<Rightarrow> bool" and g :: "'nodeid \<Rightarrow> 'trans \<Rightarrow> 'obs"
 and
   T :: "'nodeid \<Rightarrow> 'trans \<Rightarrow> bool" and B :: "'nodeid \<Rightarrow> 'val list \<Rightarrow> 'val list \<Rightarrow> bool"
and
  comOfV :: "'nodeid \<Rightarrow> 'val \<Rightarrow> com"
and
  tgtNodeOfV :: "'nodeid \<Rightarrow> 'val \<Rightarrow> 'nodeid"
and
  syncV :: "'nodeid \<Rightarrow> 'val \<Rightarrow> 'nodeid \<Rightarrow> 'val \<Rightarrow> bool"
and
  comOfO :: "'nodeid \<Rightarrow> 'obs \<Rightarrow> com"
and
  tgtNodeOfO :: "'nodeid \<Rightarrow> 'obs \<Rightarrow> 'nodeid"
and
  syncO :: "'nodeid \<Rightarrow> 'obs \<Rightarrow> 'nodeid \<Rightarrow> 'obs \<Rightarrow> bool"
(*and
  cmpO :: "'nodeid \<Rightarrow> 'obs \<Rightarrow> 'nodeid \<Rightarrow> 'obs \<Rightarrow> 'nobs"*)
and
  source :: "'nodeid"
(*  *)
assumes
  comOfV_comOf[simp]:
  "\<And>nid trn. \<lbrakk>validTrans nid trn; lreach nid (srcOf nid trn); \<phi> nid trn\<rbrakk> \<Longrightarrow> comOfV nid (f nid trn) = comOf nid trn"
and
  tgtNodeOfV_tgtNodeOf[simp]:
  "\<And>nid trn. \<lbrakk>validTrans nid trn; lreach nid (srcOf nid trn); \<phi> nid trn; comOf nid trn = Send \<or> comOf nid trn = Recv\<rbrakk>
          \<Longrightarrow> tgtNodeOfV nid (f nid trn) = tgtNodeOf nid trn"
and
  comOfO_comOf[simp]:
  "\<And>nid trn. \<lbrakk>validTrans nid trn; lreach nid (srcOf nid trn); \<gamma> nid trn\<rbrakk> \<Longrightarrow> comOfO nid (g nid trn) = comOf nid trn"
and
  tgtNodeOfO_tgtNodeOf[simp]:
  "\<And>nid trn. \<lbrakk>validTrans nid trn; lreach nid (srcOf nid trn); \<gamma> nid trn; comOf nid trn = Send \<or> comOf nid trn = Recv\<rbrakk>
         \<Longrightarrow> tgtNodeOfO nid (g nid trn) = tgtNodeOf nid trn"
and
  sync_syncV:
  "\<And>nid1 trn1 nid2 trn2.
       validTrans nid1 trn1 \<Longrightarrow> lreach nid1 (srcOf nid1 trn1) \<Longrightarrow>
       validTrans nid2 trn2 \<Longrightarrow> lreach nid2 (srcOf nid2 trn2) \<Longrightarrow>
       comOf nid1 trn1 = Send \<Longrightarrow> tgtNodeOf nid1 trn1 = nid2 \<Longrightarrow>
       comOf nid2 trn2 = Recv \<Longrightarrow> tgtNodeOf nid2 trn2 = nid1 \<Longrightarrow>
       \<phi> nid1 trn1 \<Longrightarrow> \<phi> nid2 trn2 \<Longrightarrow>
       sync nid1 trn1 nid2 trn2 \<Longrightarrow> syncV nid1 (f nid1 trn1) nid2 (f nid2 trn2)"
and
  sync_syncO:
  "\<And>nid1 trn1 nid2 trn2.
       validTrans nid1 trn1 \<Longrightarrow> lreach nid1 (srcOf nid1 trn1) \<Longrightarrow>
       validTrans nid2 trn2 \<Longrightarrow> lreach nid2 (srcOf nid2 trn2) \<Longrightarrow>
       comOf nid1 trn1 = Send \<Longrightarrow> tgtNodeOf nid1 trn1 = nid2 \<Longrightarrow>
       comOf nid2 trn2 = Recv \<Longrightarrow> tgtNodeOf nid2 trn2 = nid1 \<Longrightarrow>
       \<gamma> nid1 trn1 \<Longrightarrow> \<gamma> nid2 trn2 \<Longrightarrow>
       sync nid1 trn1 nid2 trn2 \<Longrightarrow> syncO nid1 (g nid1 trn1) nid2 (g nid2 trn2)"
and
  sync_\<phi>1_\<phi>2:
  "\<And>nid1 trn1 nid2 trn2.
       validTrans nid1 trn1 \<Longrightarrow> lreach nid1 (srcOf nid1 trn1) \<Longrightarrow>
       validTrans nid2 trn2 \<Longrightarrow> lreach nid2 (srcOf nid2 trn2) \<Longrightarrow>
       comOf nid1 trn1 = Send \<Longrightarrow> tgtNodeOf nid1 trn1 = nid2 \<Longrightarrow>
       comOf nid2 trn2 = Recv \<Longrightarrow> tgtNodeOf nid2 trn2 = nid1 \<Longrightarrow>
       sync nid1 trn1 nid2 trn2 \<Longrightarrow> \<phi> nid1 trn1 \<longleftrightarrow> \<phi> nid2 trn2"
and
  sync_\<phi>_\<gamma>:
  "\<And>nid1 trn1 nid2 trn2.
     validTrans nid1 trn1 \<Longrightarrow> lreach nid1 (srcOf nid1 trn1) \<Longrightarrow>
     validTrans nid2 trn2 \<Longrightarrow> lreach nid2 (srcOf nid2 trn2) \<Longrightarrow>
     comOf nid1 trn1 = Send \<Longrightarrow> tgtNodeOf nid1 trn1 = nid2 \<Longrightarrow>
     comOf nid2 trn2 = Recv \<Longrightarrow> tgtNodeOf nid2 trn2 = nid1 \<Longrightarrow>
     \<gamma> nid1 trn1 \<Longrightarrow> \<gamma> nid2 trn2 \<Longrightarrow>
     syncO nid1 (g nid1 trn1) nid2 (g nid2 trn2) \<Longrightarrow>
     (\<phi> nid1 trn1 \<Longrightarrow> \<phi> nid2 trn2 \<Longrightarrow> syncV nid1 (f nid1 trn1) nid2 (f nid2 trn2))
     \<Longrightarrow>
     sync nid1 trn1 nid2 trn2"
and  (* Every communication is observable (which does not mean that everything in
       a communication is observable!): *)
  isCom_\<gamma>: "\<And>nid trn. validTrans nid trn \<Longrightarrow> lreach nid (srcOf nid trn) \<Longrightarrow> comOf nid trn = Send \<or> comOf nid trn = Recv \<Longrightarrow> \<gamma> nid trn"
and (* Lack of symmetry here: all the value-producing transitions of nodes that are not the primary
       source of values need to be communication transitions *with the source* (and hence proceed
       only synchronously) -- This tames shuffling... *)
  \<phi>_source: "\<And>nid trn. \<lbrakk>validTrans nid trn; lreach nid (srcOf nid trn); \<phi> nid trn; nid \<noteq> source; nid \<in> nodes\<rbrakk>
                        \<Longrightarrow> isCom nid trn \<and> tgtNodeOf nid trn = source \<and> source \<in> nodes"
begin

abbreviation "isComO nid obs \<equiv> (comOfO nid obs = Send \<or> comOfO nid obs = Recv) \<and> tgtNodeOfO nid obs \<in> nodes"
abbreviation "isComV nid val \<equiv> (comOfV nid val = Send \<or> comOfV nid val = Recv) \<and> tgtNodeOfV nid val \<in> nodes"

(* Observation and value setup for the network *)
fun n\<phi> :: "('nodeid, 'state, 'trans) ntrans \<Rightarrow> bool" where
  "n\<phi> (LTrans s nid trn) = \<phi> nid trn"
| "n\<phi> (CTrans s nid1 trn1 nid2 trn2) = (\<phi> nid1 trn1 \<or> \<phi> nid2 trn2)"

fun nf :: "('nodeid, 'state, 'trans) ntrans \<Rightarrow> ('nodeid, 'val) nvalue" where
  "nf (LTrans s nid trn) = LVal nid (f nid trn)"
| "nf (CTrans s nid1 trn1 nid2 trn2) = CVal nid1 (f nid1 trn1) nid2 (f nid2 trn2)"

fun n\<gamma> :: "('nodeid, 'state, 'trans) ntrans \<Rightarrow> bool" where
  "n\<gamma> (LTrans s nid trn) = \<gamma> nid trn"
| "n\<gamma> (CTrans s nid1 trn1 nid2 trn2) = (\<gamma> nid1 trn1 \<or> \<gamma> nid2 trn2)"

fun ng :: "('nodeid, 'state, 'trans) ntrans \<Rightarrow> ('nodeid, 'obs) nobs" where
  "ng (LTrans s nid trn) = LObs nid (g nid trn)"
| "ng (CTrans s nid1 trn1 nid2 trn2) = CObs nid1 (g nid1 trn1) nid2 (g nid2 trn2)"

fun nT :: "('nodeid, 'state, 'trans) ntrans \<Rightarrow> bool" where
  "nT (LTrans s nid trn) = T nid trn"
| "nT (CTrans s nid1 trn1 nid2 trn2) = (T nid1 trn1 \<or> T nid2 trn2)"
(* *)

fun decompV :: "('nodeid, 'val) nvalue list \<Rightarrow> 'nodeid \<Rightarrow> 'val list" where
  "decompV (LVal nid' v # vl) nid = (if nid' = nid then v # decompV vl nid else decompV vl nid)"
| "decompV (CVal nid1 v1 nid2 v2 # vl) nid = (if nid1 = nid then v1 # decompV vl nid else
                                             (if nid2 = nid then v2 # decompV vl nid else
                                              decompV vl nid))"
| "decompV [] nid = []"

fun nValidV :: "('nodeid, 'val) nvalue \<Rightarrow> bool" where
  "nValidV (LVal nid v) = (nid \<in> nodes \<and> \<not>isComV nid v)"
| "nValidV (CVal nid1 v1 nid2 v2) =
    (nid1 \<in> nodes \<and> nid2 \<in> nodes \<and> nid1 \<noteq> nid2 \<and> syncV nid1 v1 nid2 v2 \<and>
     comOfV nid1 v1 = Send \<and> tgtNodeOfV nid1 v1 = nid2 \<and> comOfV nid2 v2 = Recv \<and> tgtNodeOfV nid2 v2 = nid1)"


fun decompO :: "('nodeid, 'obs) nobs list \<Rightarrow> 'nodeid \<Rightarrow> 'obs list" where
  "decompO (LObs nid' obs # obsl) nid = (if nid' = nid then obs # decompO obsl nid else decompO obsl nid)"
| "decompO (CObs nid1 obs1 nid2 obs2 # obsl) nid = (if nid1 = nid then obs1 # decompO obsl nid else
                                                   (if nid2 = nid then obs2 # decompO obsl nid else
                                                    decompO obsl nid))"
| "decompO [] nid = []"

(* The declassification bound for the network *)
definition nB :: "('nodeid, 'val) nvalue list \<Rightarrow> ('nodeid, 'val) nvalue list \<Rightarrow> bool" where
"nB vl vl' \<equiv> (\<forall>nid \<in> nodes. B nid (decompV vl nid) (decompV vl' nid)) \<and>
             (list_all nValidV vl \<longrightarrow> list_all nValidV vl')"
(* *)

fun subDecompV :: "('nodeid, 'val) nvalue list \<Rightarrow> 'nodeid set \<Rightarrow> ('nodeid, 'val) nvalue list" where
  "subDecompV (LVal nid' v # vl) nds =
    (if nid' \<in> nds then LVal nid' v # subDecompV vl nds else subDecompV vl nds)"
| "subDecompV (CVal nid1 v1 nid2 v2 # vl) nds =
    (if nid1 \<in> nds \<and> nid2 \<in> nds then CVal nid1 v1 nid2 v2 # subDecompV vl nds else
    (if nid1 \<in> nds then LVal nid1 v1 # subDecompV vl nds else
    (if nid2 \<in> nds then LVal nid2 v2 # subDecompV vl nds else
     subDecompV vl nds)))"
| "subDecompV [] nds = []"

lemma decompV_subDecompV[simp]: "nid \<in> nds \<Longrightarrow> decompV (subDecompV vl nds) nid = decompV vl nid"
proof (induction vl)
  case (Cons v vl) then show ?case by (cases v) (auto split: if_splits)
qed auto

sublocale BD_Security_TS istate nValidTrans nSrcOf nTgtOf n\<phi> nf n\<gamma> ng nT nB .

(* Abbreviations for local BD Security setup of individual nodes *)
abbreviation lV :: "'nodeid \<Rightarrow> 'trans list \<Rightarrow> 'val list" where
  "lV nid \<equiv> BD_Security_TS.V (\<phi> nid) (f nid)"

abbreviation lO :: "'nodeid \<Rightarrow> 'trans list \<Rightarrow> 'obs list" where
  "lO nid \<equiv> BD_Security_TS.O (\<gamma> nid) (g nid)"

abbreviation lTT :: "'nodeid \<Rightarrow> 'trans list \<Rightarrow> bool" where
  "lTT nid \<equiv> never (T nid)"

abbreviation lsecure :: "'nodeid \<Rightarrow> bool" where
  "lsecure nid \<equiv> Abstract_BD_Security.secure (lValidFrom nid (istate nid)) (lV nid) (lO nid) (B nid) (lTT nid)"


lemma decompV_decomp:
assumes "validFrom s tr"
and "reach s"
shows "decompV (V tr) nid = lV nid (decomp tr nid)"
proof -
  interpret Node: BD_Security_TS "istate nid" "validTrans nid" "srcOf nid" "tgtOf nid"
                                 "\<phi> nid" "f nid" "\<gamma> nid" "g nid" "T nid" "B nid" .
  from assms show ?thesis proof (induction tr arbitrary: s)
    case (Cons trn tr s)
      then have tr: "decompV (V tr) nid = Node.V (decomp tr nid)"
        by (intro Cons.IH[of "nTgtOf trn"]) (auto intro: reach.Step)
      show ?case proof (cases trn)
        case (LTrans s' nid' trn') with Cons.prems tr show ?thesis by (cases "n\<phi> trn") auto
      next
        case (CTrans s' nid1 trn1 nid2 trn2)
          then have "lreach nid1 (s' nid1)" and "lreach nid2 (s' nid2)"
            using Cons.prems by (auto elim: reach_lreach)
          then have "\<phi> nid1 trn1 \<longleftrightarrow> \<phi> nid2 trn2"
            using Cons.prems CTrans by (intro sync_\<phi>1_\<phi>2) auto
          then show ?thesis using Cons.prems CTrans tr Node.V_Cons_unfold by (cases "n\<phi> trn") auto
      qed
  qed auto
qed

lemma decompO_decomp:
assumes "validFrom s tr"
and "reach s"
shows "decompO (O tr) nid = lO nid (decomp tr nid)"
proof -
  interpret Node: BD_Security_TS "istate nid" "validTrans nid" "srcOf nid" "tgtOf nid"
                                 "\<phi> nid" "f nid" "\<gamma> nid" "g nid" "T nid" "B nid" .
  from assms show ?thesis proof (induction tr arbitrary: s)
    case (Cons trn tr s)
      then have tr: "decompO (O tr) nid = Node.O (decomp tr nid)"
        by (intro Cons.IH[of "nTgtOf trn"]) (auto intro: reach.Step)
      show ?case proof (cases trn)
        case (LTrans s' nid' trn') with Cons.prems tr show ?thesis by (cases "n\<gamma> trn") auto
      next
        case (CTrans s' nid1 trn1 nid2 trn2)
          then have "lreach nid1 (s' nid1)" and "lreach nid2 (s' nid2)"
            using Cons.prems by (auto elim: reach_lreach)
          then have "\<gamma> nid1 trn1" and "\<gamma> nid2 trn2"
            using Cons.prems CTrans by (auto intro: isCom_\<gamma>)
          then show ?thesis using Cons.prems CTrans tr Node.O_Cons_unfold by (cases "n\<gamma> trn") auto
      qed
  qed auto
qed

lemma nTT_TT: "never nT tr \<Longrightarrow> never (T nid) (decomp tr nid)"
proof (induction tr)
  case (Cons trn tr) then show ?case by (cases trn) auto
qed auto

lemma validFrom_nValidV:
assumes "validFrom s tr"
and "reach s"
shows "list_all nValidV (V tr)"
using assms proof (induction tr arbitrary: s)
  case (Cons trn tr s)
    have tr: "list_all nValidV (V tr)" using Cons.IH[of "nTgtOf trn"] Cons.prems
      by (auto intro: reach.Step)
    then show ?case proof (cases trn)
      case (LTrans s' nid' trn')
        moreover then have "lreach nid' (s' nid')" using Cons.prems by (auto elim: reach_lreach)
        ultimately show ?thesis using Cons.prems tr by (cases "n\<phi> trn") auto
    next
      case (CTrans s' nid1 trn1 nid2 trn2)
        moreover then have "lreach nid1 (s' nid1)" and "lreach nid2 (s' nid2)"
          using Cons.prems by (auto elim: reach_lreach)
        moreover then have "\<phi> nid1 trn1 \<longleftrightarrow> \<phi> nid2 trn2"
          using Cons.prems CTrans by (intro sync_\<phi>1_\<phi>2) auto
        ultimately show ?thesis using Cons.prems tr by (cases "n\<phi> trn") (auto intro: sync_syncV)
    qed
qed auto

end

text \<open>An empty network is trivially secure.  This is useful as a base case in proofs.\<close>

locale BD_Security_Empty_TS_Network = BD_Security_TS_Network where nodes = "{}"
begin

sublocale Empty_TS_Network ..

lemma nValidVE: "nValidV v \<Longrightarrow> P" by (cases v) auto
lemma list_all_nValidV_Nil: "list_all nValidV vl \<Longrightarrow> vl = []" by (cases vl) (auto elim: nValidVE)

lemma trivially_secure: "secure"
by (intro B_id_secure) (auto iff: validFrom_iff_Nil simp: nB_def B_id_def elim: list_all_nValidV_Nil)

end

text \<open>Another useful base case: a singleton network with just the secret source node.\<close>

locale BD_Security_Singleton_Source_Network = BD_Security_TS_Network where nodes = "{source}"
begin

sublocale Node: BD_Security_TS "istate source" "validTrans source" "srcOf source" "tgtOf source"
                               "\<phi> source" "f source" "\<gamma> source" "g source" "T source" "B source" .

lemma [simp]: "decompV (map (LVal source) vl) source = vl"
by (induction vl) auto

lemma [simp]: "list_all nValidV vl' \<Longrightarrow> map (LVal source) (decompV vl' source) = vl'"
proof (induction vl')
  case (Cons v vl') then show ?case by (cases v) auto
qed auto

lemma Node_validFrom_nValidV:
  "Node.validFrom s tr \<Longrightarrow> Node.reach s \<Longrightarrow> list_all nValidV (map (LVal source) (Node.V tr))"
proof (induction tr arbitrary: s)
  case (Cons trn tr)
    then have "Node.reach (tgtOf source trn)" using Node.reach.Step[of s trn "tgtOf source trn"] by auto
    then show ?case using Cons.prems Cons.IH[of "tgtOf source trn"]
      using isCom_tgtNodeOf by (cases "\<phi> source trn") auto
qed auto

sublocale Trans?: BD_Security_TS_Trans
  where istate = "istate source" and validTrans = "validTrans source" and srcOf = "srcOf source" and tgtOf = "tgtOf source"
  and \<phi> = "\<phi> source" and f = "f source" and \<gamma> = "\<gamma> source" and g = "g source" and T = "T source" and B = "B source"
  and istate' = istate and validTrans' = nValidTrans and srcOf' = nSrcOf and tgtOf' = nTgtOf
  and \<phi>' = n\<phi> and f' = nf and \<gamma>' = n\<gamma> and g' = ng and T' = nT and B' = nB
  and translateState = "\<lambda>s. istate(source := s)"
  and translateTrans = "\<lambda>trn. LTrans (istate(source := srcOf source trn)) source trn"
  and translateObs = "\<lambda>obs. Some (LObs source obs)"
  and translateVal = "Some o LVal source"
using isCom_tgtNodeOf
proof (unfold_locales, goal_cases)
  case (2 trn' s) then show ?case by (cases trn') auto next
  case (11 vl' vl1' tr)
    then show ?case using Node.reach.Istate
      by (intro exI[of _ "decompV vl1' source"]) (auto simp: nB_def intro: Node_validFrom_nValidV)
qed auto

end

text \<open>Setup for changing the set of nodes in a network, e.g. adding a new one.
We re-check unique secret polarization, while the other assumptions about the observation and
secret infrastructure are inherited from the original setup.\<close>

locale BD_Security_TS_Network_Change_Nodes = Orig: BD_Security_TS_Network +
fixes nodes'
assumes finite_nodes': "finite nodes'"
and \<phi>_source':
    "\<And>nid trn. \<lbrakk>validTrans nid trn; Orig.lreach nid (srcOf nid trn); \<phi> nid trn; nid \<noteq> source; nid \<in> nodes'\<rbrakk>
            \<Longrightarrow> Orig.isCom nid trn \<and> tgtNodeOf nid trn = source \<and> source \<in> nodes'"
begin

sublocale BD_Security_TS_Network where nodes = nodes'
proof (unfold_locales, goal_cases)
  case 1 show ?case using finite_nodes' . next
  case 2 then show ?case using "Orig.isCom_tgtNodeOf" by auto next
  case 3 then show ?case by auto next
  case 4 then show ?case by auto next
  case 5 then show ?case by auto next
  case 6 then show ?case by auto next
  case 7 then show ?case using "Orig.sync_syncV" by auto next
  case 8 then show ?case using "Orig.sync_syncO" by auto next
  case 9 then show ?case using "Orig.sync_\<phi>1_\<phi>2" by auto next
  case 10 then show ?case using "Orig.sync_\<phi>_\<gamma>" by auto next
  case 11 then show ?case using "Orig.isCom_\<gamma>" by auto next
  case 12 then show ?case using \<phi>_source' by auto
qed

end

text \<open>Adding a new node to a network that is not the secret source:\<close>

locale BD_Security_TS_Network_New_Node_NoSource = Sub: BD_Security_TS_Network
where istate = istate and nodes = nodes and f = f and g = g (*and cmpV = cmpV and cmpO = cmpO*)
for istate :: "'nodeid \<Rightarrow> 'state" and nodes :: "'nodeid set"
and f :: "'nodeid \<Rightarrow> 'trans \<Rightarrow> 'val" and g :: "'nodeid \<Rightarrow> 'trans \<Rightarrow> 'obs"
(*and cmpV :: "'nodeid \<Rightarrow> 'val \<Rightarrow> 'nodeid \<Rightarrow> 'val \<Rightarrow> 'cval"
and cmpO :: "'nodeid \<Rightarrow> 'obs \<Rightarrow> 'nodeid \<Rightarrow> 'obs \<Rightarrow> 'cobs"*)
+
fixes NID :: "'nodeid"
assumes new_node: "NID \<notin> nodes"
and no_source: "NID \<noteq> source"
and \<phi>_NID_source:
    "\<And>trn. \<lbrakk>validTrans NID trn; Sub.lreach NID (srcOf NID trn); \<phi> NID trn\<rbrakk>
        \<Longrightarrow> Sub.isCom NID trn \<and> tgtNodeOf NID trn = source \<and> source \<in> nodes"
begin

sublocale Node: BD_Security_TS "istate NID" "validTrans NID" "srcOf NID" "tgtOf NID"
                               "\<phi> NID" "f NID" "\<gamma> NID" "g NID" "T NID" "B NID" .

sublocale BD_Security_TS_Network_Change_Nodes where nodes' = "insert NID nodes"
  using \<phi>_NID_source Sub.\<phi>_source Sub.finite_nodes
  by (unfold_locales) auto

fun isCom1 :: "('nodeid,'state,'trans) ntrans \<Rightarrow> bool" where
  "isCom1 (LTrans s nid trn) = (nid \<in> nodes \<and> isCom nid trn \<and> tgtNodeOf nid trn = NID)"
| "isCom1 _ = False"

definition "isCom2 trn = (\<exists>nid. nid \<in> nodes \<and> isCom NID trn \<and> tgtNodeOf NID trn = nid)"

fun Sync :: "('nodeid,'state,'trans) ntrans \<Rightarrow> 'trans \<Rightarrow> bool" where
  "Sync (LTrans s nid trn) trn' = (tgtNodeOf nid trn = NID \<and> tgtNodeOf NID trn' = nid \<and>
                                  ((sync nid trn NID trn' \<and> comOf nid trn = Send \<and> comOf NID trn' = Recv)
                                 \<or> (sync NID trn' nid trn \<and> comOf NID trn' = Send \<and> comOf nid trn = Recv)))"
| "Sync _ _ = False"

fun isComV1 :: "('nodeid,'val) nvalue \<Rightarrow> bool" where
  "isComV1 (LVal nid v) = (nid \<in> nodes \<and> isComV nid v \<and> tgtNodeOfV nid v = NID)"
| "isComV1 _ = False"

definition "isComV2 v = (\<exists>nid. nid \<in> nodes \<and> isComV NID v \<and> tgtNodeOfV NID v = nid)"

fun SyncV :: "('nodeid,'val) nvalue \<Rightarrow> 'val \<Rightarrow> bool" where
  "SyncV (LVal nid v1) v2 = (tgtNodeOfV nid v1 = NID \<and> tgtNodeOfV NID v2 = nid \<and>
                            ((syncV nid v1 NID v2 \<and> comOfV nid v1 = Send \<and> comOfV NID v2 = Recv)
                            \<or> (syncV NID v2 nid v1 \<and> comOfV NID v2 = Send \<and> comOfV nid v1 = Recv)))"
| "SyncV _ _ = False"

fun CmpV :: "('nodeid,'val) nvalue \<Rightarrow> 'val \<Rightarrow> ('nodeid,'val) nvalue" where
  "CmpV (LVal nid v1) v2 = (if comOfV nid v1 = Send then CVal nid v1 NID v2 else CVal NID v2 nid v1)"
| "CmpV cv v2 = cv"

fun isComO1 :: "('nodeid,'obs) nobs \<Rightarrow> bool" where
  "isComO1 (LObs nid obs) = (nid \<in> nodes \<and> isComO nid obs \<and> tgtNodeOfO nid obs = NID)"
| "isComO1 _ = False"

definition "isComO2 obs = (\<exists>nid. nid \<in> nodes \<and> isComO NID obs \<and> tgtNodeOfO NID obs = nid)"

fun SyncO :: "('nodeid,'obs) nobs \<Rightarrow> 'obs \<Rightarrow> bool" where
  "SyncO (LObs nid obs1) obs2 = (tgtNodeOfO nid obs1 = NID \<and> tgtNodeOfO NID obs2 = nid \<and>
                                ((syncO nid obs1 NID obs2 \<and> comOfO nid obs1 = Send \<and> comOfO NID obs2 = Recv)
                                \<or> (syncO NID obs2 nid obs1 \<and> comOfO NID obs2 = Send \<and> comOfO nid obs1 = Recv)))"
| "SyncO _ _ = False"

text \<open>We prove security using the binary composition theorem,
composing the existing network with the new node.\<close>

sublocale Comp: BD_Security_TS_Comp istate Sub.nValidTrans Sub.nSrcOf Sub.nTgtOf
  Sub.n\<phi> Sub.nf Sub.n\<gamma> Sub.ng Sub.nT Sub.nB
  "istate NID" "validTrans NID" "srcOf NID" "tgtOf NID" "\<phi> NID" "f NID" "\<gamma> NID" "g NID" "T NID" "B NID"
  isCom1 isCom2 Sync isComV1 isComV2 SyncV isComO1 isComO2 SyncO
proof
  fix trn1
  assume trn1: "Sub.nValidTrans trn1" "Sub.reach (Sub.nSrcOf trn1)" "Sub.n\<phi> trn1"
  then show "isCom1 trn1 = isComV1 (Sub.nf trn1)"
  proof (cases trn1)
    case (LTrans s nid trn)
      with trn1 have "lreach nid (srcOf nid trn)" by (auto elim!: Sub.reach_lreach)
      with trn1 show ?thesis using LTrans by auto
  qed auto
next
  fix trn1
  assume trn1: "Sub.nValidTrans trn1" "Sub.reach (Sub.nSrcOf trn1)" "Sub.n\<gamma> trn1"
  then show "isCom1 trn1 = isComO1 (Sub.ng trn1)"
  proof (cases trn1)
    case (LTrans s nid trn)
      with trn1 have "lreach nid (srcOf nid trn)" by (auto elim!: Sub.reach_lreach)
      with trn1 show ?thesis using LTrans by auto
  qed auto
next
  fix trn2
  assume trn2: "validTrans NID trn2" "Node.reach (srcOf NID trn2)" "\<phi> NID trn2"
  then show "isCom2 trn2 = isComV2 (f NID trn2)"
    unfolding isCom2_def isComV2_def by auto
next
  fix trn2
  assume trn2: "validTrans NID trn2" "Node.reach (srcOf NID trn2)" "\<gamma> NID trn2"
  then show "isCom2 trn2 = isComO2 (g NID trn2)"
    unfolding isCom2_def isComO2_def by auto
next
  fix trn1 trn2
  assume trn12: "Sub.nValidTrans trn1" "Sub.reach (Sub.nSrcOf trn1)" "validTrans NID trn2"
       "Node.reach (srcOf NID trn2)" "isCom1 trn1" "isCom2 trn2" "Sub.n\<phi> trn1" "\<phi> NID trn2" "Sync trn1 trn2"
  then show "SyncV (Sub.nf trn1) (f NID trn2)" proof (cases trn1)
    case (LTrans s nid trn)
      with trn12 have "lreach nid (srcOf nid trn)" by (auto elim: Sub.reach_lreach)
      with trn12 show ?thesis using LTrans by (auto intro: Sub.sync_syncV)
  qed auto
next
  fix trn1 trn2
  assume trn12: "Sub.nValidTrans trn1" "Sub.reach (Sub.nSrcOf trn1)" "validTrans NID trn2"
       "Node.reach (srcOf NID trn2)" "isCom1 trn1" "isCom2 trn2" "Sub.n\<gamma> trn1" "\<gamma> NID trn2" "Sync trn1 trn2"
  then show "SyncO (Sub.ng trn1) (g NID trn2)" proof (cases trn1)
    case (LTrans s nid trn)
      with trn12 have "lreach nid (srcOf nid trn)" by (auto elim: Sub.reach_lreach)
      with trn12 show ?thesis using LTrans by (auto intro: Sub.sync_syncO)
  qed auto
next
  fix trn1 trn2
  assume trn12: "Sub.nValidTrans trn1" "Sub.reach (Sub.nSrcOf trn1)" "validTrans NID trn2"
       "Node.reach (srcOf NID trn2)" "isCom1 trn1" "isCom2 trn2" "Sync trn1 trn2"
  then show "Sub.n\<phi> trn1 = \<phi> NID trn2" proof (cases trn1)
    case (LTrans s nid trn)
      with trn12 show ?thesis using Sub.sync_\<phi>1_\<phi>2[of nid trn NID trn2] Sub.sync_\<phi>1_\<phi>2[of NID trn2 nid trn]
        by (auto elim: Sub.reach_lreach)
  qed auto
next
  fix trn1 trn2
  assume trn12: "Sub.nValidTrans trn1" "Sub.reach (Sub.nSrcOf trn1)" "validTrans NID trn2"
       "Node.reach (srcOf NID trn2)" "isCom1 trn1" "isCom2 trn2"
       "Sub.n\<gamma> trn1" "\<gamma> NID trn2" "SyncO (Sub.ng trn1) (g NID trn2)"
       "Sub.n\<phi> trn1 \<Longrightarrow> \<phi> NID trn2 \<Longrightarrow> SyncV (Sub.nf trn1) (f NID trn2)"
  then show "Sync trn1 trn2" proof (cases trn1)
    case (LTrans s nid trn)
      with trn12 have "lreach nid (srcOf nid trn)" by (auto elim: Sub.reach_lreach)
      with trn12 show ?thesis using LTrans by (auto intro: Sub.sync_\<phi>_\<gamma>)
  qed auto
next
  fix trn1
  assume trn1: "Sub.nValidTrans trn1" "Sub.reach (Sub.nSrcOf trn1)" "isCom1 trn1"
  then show "Sub.n\<gamma> trn1" proof (cases trn1)
    case (LTrans s nid trn)
      with trn1 show ?thesis using Sub.isCom_\<gamma>[of nid trn] by (auto elim: Sub.reach_lreach)
  qed auto
next
  fix trn2
  assume "validTrans NID trn2" "Node.reach (srcOf NID trn2)" "isCom2 trn2"
  then show "\<gamma> NID trn2" unfolding isCom2_def by (auto intro: Sub.isCom_\<gamma>)
next
  fix trn2
  assume "validTrans NID trn2" "Node.reach (srcOf NID trn2)" "\<phi> NID trn2"
  then show "isCom2 trn2" using \<phi>_NID_source unfolding isCom2_def by auto
qed auto

text \<open>We then translate the canonical security property obtained from the binary compositionality
result back to the original observation and secret infrastructure using the transport theorem.\<close>

fun translateState :: "(('nodeid \<Rightarrow> 'state) \<times> 'state) \<Rightarrow> ('nodeid \<Rightarrow> 'state)" where
  "translateState (sSub, sNode) = (sSub(NID := sNode))"

fun translateTrans :: "('nodeid \<Rightarrow> 'state, ('nodeid, 'state, 'trans) ntrans, 'state, 'trans) ctrans \<Rightarrow> ('nodeid, 'state, 'trans) ntrans" where
  "translateTrans (Trans1 sNode (LTrans s nid trn)) = LTrans (s(NID := sNode)) nid trn"
| "translateTrans (Trans1 sNode (CTrans s nid1 trn1 nid2 trn2)) = CTrans (s(NID := sNode)) nid1 trn1 nid2 trn2"
| "translateTrans (Trans2 sSub trn) = LTrans (sSub(NID := srcOf NID trn)) NID trn"
| "translateTrans (ctrans.CTrans (LTrans s nid trn) trnNode) =
      (if comOf nid trn = Send
       then CTrans (s(NID := srcOf NID trnNode)) nid trn NID trnNode
       else CTrans (s(NID := srcOf NID trnNode)) NID trnNode nid trn)"
| "translateTrans _ = undefined"

fun translateObs :: "(('nodeid, 'obs) nobs, 'obs) cobs \<Rightarrow> ('nodeid, 'obs) nobs" where
  "translateObs (Obs1 obs) = obs"
| "translateObs (Obs2 obs) = (LObs NID obs)"
| "translateObs (cobs.CObs (LObs nid1 obs1) obs2) =
    (if comOfO nid1 obs1 = Send then CObs nid1 obs1 NID obs2 else CObs NID obs2 nid1 obs1)"
| "translateObs _ = undefined"

fun translateVal :: "(('nodeid, 'val) nvalue, 'val) cvalue \<Rightarrow> ('nodeid, 'val) nvalue" where
  "translateVal (Value1 v) = v"
| "translateVal (Value2 v) = (LVal NID v)"
| "translateVal (cvalue.CValue (LVal nid1 v1) v2) =
    (if comOfV nid1 v1 = Send then CVal nid1 v1 NID v2 else CVal NID v2 nid1 v1)"
| "translateVal _ = undefined"

fun invTranslateVal :: "('nodeid, 'val) nvalue \<Rightarrow> (('nodeid, 'val) nvalue, 'val) cvalue" where
  "invTranslateVal (LVal nid v) = (if nid = NID then Value2 v else Value1 (LVal nid v))"
| "invTranslateVal (CVal nid1 v1 nid2 v2) =
    (if nid1 \<in> nodes \<and> nid2 \<in> nodes then Value1 (CVal nid1 v1 nid2 v2)
     else (if nid1 = NID then CValue (LVal nid2 v2) v1
           else CValue (LVal nid1 v1) v2))"

lemma translateVal_invTranslateVal[simp]: "nValidV v \<Longrightarrow> (translateVal (invTranslateVal v)) = v"
by (elim nValidV.elims) auto

lemma map_translateVal_invTranslateVal[simp]:
  "list_all nValidV vl \<Longrightarrow> map (translateVal o invTranslateVal) vl = vl"
by (induction vl) auto

fun compValidV :: "(('nodeid, 'val) nvalue, 'val) cvalue \<Rightarrow> bool" where
  "compValidV (Value1 (LVal nid v)) = (Sub.nValidV (LVal nid v) \<and> (isComV nid v \<longrightarrow> tgtNodeOfV nid v \<noteq> NID))"
| "compValidV (Value1 (CVal nid1 v1 nid2 v2)) = Sub.nValidV (CVal nid1 v1 nid2 v2)"
| "compValidV (Value2 v2) = nValidV (LVal NID v2)"
| "compValidV (CValue (CVal nid1 v1 nid2 v2) v) = False"
| "compValidV (CValue (LVal nid1 v1) v2) = (nValidV (CVal nid1 v1 NID v2) \<or> nValidV (CVal NID v2 nid1 v1))"

lemma nValidV_compValidV: "nValidV v \<Longrightarrow> compValidV (invTranslateVal v)"
by (cases v) auto

lemma list_all_nValidV_compValidV: "list_all nValidV vl \<Longrightarrow> list_all compValidV (map invTranslateVal vl)"
by (induction vl) (auto intro: nValidV_compValidV)

lemma compValidV_nValidV: "compValidV v \<Longrightarrow> nValidV (translateVal v)"
by (cases v rule: "compValidV.cases") auto

lemma list_all_compValidV_nValidV: "list_all compValidV vl \<Longrightarrow> list_all nValidV (map translateVal vl)"
by (induction vl) (auto intro: compValidV_nValidV)

lemma nValidV_subDecompV: "list_all nValidV vl \<Longrightarrow> list_all Sub.nValidV (subDecompV vl nodes)"
proof (induction vl)
  case (Cons v vl) then show ?case by (cases v) auto
qed auto

lemma validTrans_compValidV:
assumes "Comp.validTrans trn" and "Comp.reach (Comp.srcOf trn)" and "Comp.\<phi> trn"
shows "compValidV (Comp.f trn)"
proof (cases trn)
  case (Trans1 sNode trnSub)
    show ?thesis proof (cases trnSub)
      case (LTrans s nid1 trn1)
        then have "lreach nid1 (s nid1)"
          using Trans1 assms Comp.reach_reach12[of "Comp.srcOf trn"]
          by (auto elim!: Sub.reach_lreach)
        then show ?thesis using LTrans Trans1 assms by auto
    next
      case (CTrans s nid1 trn1 nid2 trn2)
        then have "lreach nid1 (s nid1)" and "lreach nid2 (s nid2)"
          using Trans1 assms Comp.reach_reach12[of "Comp.srcOf trn"]
          by (auto elim!: Sub.reach_lreach)
        then show ?thesis using CTrans Trans1 assms
          using sync_syncV[of nid1 trn1 nid2 trn2] sync_\<phi>1_\<phi>2[of nid1 trn1 nid2 trn2] by auto
    qed
next
  case (Trans2 sSub trnNode)
    then have "lreach NID (srcOf NID trnNode)" using assms Comp.reach_reach12[of "Comp.srcOf trn"] by auto
    with assms Trans2 show ?thesis using \<phi>_NID_source by (auto simp: isCom2_def)
next
  case (CTrans trnSub trnNode)
    then obtain sSub nid1 trn1 where "trnSub = LTrans sSub nid1 trn1" using assms
      by (cases trnSub) auto
    moreover then have "lreach nid1 (sSub nid1)" and "lreach NID (srcOf NID trnNode)"
      using assms Comp.reach_reach12[of "Comp.srcOf trn"] CTrans by (auto elim!: Sub.reach_lreach)
    ultimately show ?thesis using assms CTrans
      using sync_syncV[of nid1 trn1 NID trnNode] sync_\<phi>1_\<phi>2[of nid1 trn1 NID trnNode]
      using sync_syncV[of NID trnNode nid1 trn1] sync_\<phi>1_\<phi>2[of NID trnNode nid1 trn1]
      by (cases "comOf NID trnNode = Send") auto
qed

lemma validFrom_compValidV: "Comp.reach s \<Longrightarrow> Comp.validFrom s tr \<Longrightarrow> list_all compValidV (Comp.V tr)"
proof (induction tr arbitrary: s)
  case (Cons trn tr)
    then have "Comp.reach (Comp.tgtOf trn)" using Comp.reach.Step[of s trn "Comp.tgtOf trn"] by auto
    then show ?case using Cons.prems Cons.IH[of "Comp.tgtOf trn"] validTrans_compValidV
      by (cases "Comp.\<phi> trn") auto
qed auto

lemma validFrom_istate_compValidV: "Comp.validFrom Comp.icstate tr \<Longrightarrow> list_all compValidV (Comp.V tr)"
using validFrom_compValidV Comp.reach.Istate by blast

lemma compV_decompV:
assumes "list_all compValidV vl"
shows "Comp.compV vl1 vl2 vl
   \<longleftrightarrow> vl1 = subDecompV (map translateVal vl) nodes \<and> vl2 = decompV (map translateVal vl) NID"
proof
  assume "Comp.compV vl1 vl2 vl"
  then show "vl1 = subDecompV (map translateVal vl) nodes \<and> vl2 = decompV (map translateVal vl) NID"
    using assms new_node
  proof (induction rule: Comp.compV.induct)
    case (Step1 vl1 vl2 vl v1) then show ?case by (cases v1) auto next
    case (Com vl1 vl2 vl v1 v2) then show ?case by (cases v1) auto
  qed auto
next
  assume "vl1 = subDecompV (map translateVal vl) nodes \<and> vl2 = decompV (map translateVal vl) NID"
  moreover have "Comp.compV (subDecompV (map translateVal vl) nodes) (decompV (map translateVal vl) NID) vl"
    using assms new_node
  proof (induction vl)
    case (Cons v vl)
      then show ?case proof (cases v)
        case (Value1 v1) with Cons show ?thesis by (cases v1) auto
      next
        case (Value2 v2)
          then have "\<not> isComV2 v2" using Cons unfolding isComV2_def by auto
          then show ?thesis using Cons Value2 by auto
      next
        case (CValue cv v2)
          then show ?thesis using Cons.prems proof (cases cv)
            case (LVal nid1 v1)
              then have "isComV2 v2" using LVal CValue Cons unfolding isComV2_def by auto
              then have "Comp.compV (LVal nid1 v1 # subDecompV (map translateVal vl) nodes)
                                    (v2 # decompV (map translateVal vl) NID)
                                    (CValue (LVal nid1 v1) v2 # vl)"
                using LVal CValue Cons by (intro Comp.compV.Com) auto
              then show ?thesis using LVal CValue Cons by auto
          qed auto
      qed
  qed auto
  ultimately show "Comp.compV vl1 vl2 vl" by auto
qed


sublocale Trans?: BD_Security_TS_Trans Comp.icstate Comp.validTrans Comp.srcOf Comp.tgtOf
  Comp.\<phi> Comp.f Comp.\<gamma> Comp.g Comp.T Comp.B
  istate nValidTrans nSrcOf nTgtOf n\<phi> nf n\<gamma> ng nT nB
  translateState translateTrans "Some o translateObs" "Some o translateVal"
proof
  fix trn
  assume trn: "Comp.validTrans trn" "Comp.reach (Comp.srcOf trn)"
  then show "nValidTrans (translateTrans trn)" using new_node
  proof (cases trn)
    case (Trans2 sSub trnNode)
      with trn have "Node.reach (srcOf NID trnNode)" by (auto elim: Comp.reach_reach12)
      with trn Trans2 show ?thesis using Sub.isCom_tgtNodeOf[of NID _] by (auto simp: isCom2_def)
  next
    case (CTrans trnSub trnNode)
      with trn obtain sSub nid trn1 where trnSub: "trnSub = LTrans sSub nid trn1"
        by (auto elim: Sync.elims)
      then have "lreach nid (srcOf nid trn1)" and "lreach NID (srcOf NID trnNode)"
        using CTrans trn by (auto elim!: Comp.reach_reach12 Sub.reach_lreach)
      (*then have "srcNodeOf trn1 = nid" and "srcNodeOf trnNode = NID"
        using trn trnSub CTrans by (auto simp: Sub.isCom_srcNodeOf)*)
      then show ?thesis using CTrans trn trnSub by (auto elim: Sub.nValidTrans.elims)
  qed (auto elim!: Sub.nValidTrans.elims split: if_split_asm)
next
  fix trn' s
  assume trn': "nValidTrans trn'" "nSrcOf trn' = translateState s" "Comp.reach s"
  then obtain trn where "Comp.validTrans trn" "Comp.srcOf trn = s" "translateTrans trn = trn'"
  proof (cases trn')
    case (LTrans s' nid trn)
      show thesis proof cases
        assume "nid = NID"
        then show thesis using trn' LTrans
          by (cases s; intro that[of "Trans2 (fst s) trn"]) (auto simp: isCom2_def)
      next
        assume "nid \<noteq> NID"
        then show thesis using trn' LTrans
          by (cases s;intro that[of "Trans1 (snd s) (LTrans (fst s) nid trn)"]) auto
      qed
  next
    case (CTrans s' nid1 trn1 nid2 trn2)
      show thesis proof cases
        assume "nid1 = NID \<or> nid2 = NID"
        then show thesis proof
          assume "nid1 = NID"
          then show thesis using trn' CTrans new_node
            by (cases s; intro that[of "ctrans.CTrans (LTrans (fst s) nid2 trn2) trn1"])
               (auto simp: isCom2_def)
        next
          assume "nid2 = NID"
          then show thesis using trn' CTrans new_node
            by (cases s; intro that[of "ctrans.CTrans (LTrans (fst s) nid1 trn1) trn2"])
               (auto simp: isCom2_def)
        qed
      next
        assume "\<not> (nid1 = NID \<or> nid2 = NID)"
        then show thesis using trn' CTrans
          by (cases s; intro that[of "Trans1 (snd s) (CTrans (fst s) nid1 trn1 nid2 trn2)"]) auto
      qed
  qed
  then show "\<exists>trn. Comp.validTrans trn \<and> Comp.srcOf trn = s \<and> translateTrans trn = trn'" by auto
next
  fix trn
  assume trn: "Comp.validTrans trn" "Comp.reach (Comp.srcOf trn)"
  show "nSrcOf (translateTrans trn) = translateState (Comp.srcOf trn)"
    using trn by (cases trn rule: translateTrans.cases) auto
  show "nTgtOf (translateTrans trn) = translateState (Comp.tgtOf trn)"
    using trn new_node by (cases trn rule: translateTrans.cases) (auto intro: fun_upd_twist)
next
  show "istate = translateState Comp.icstate" unfolding Comp.icstate_def by auto
next
  fix trn
  assume trn: "Comp.validTrans trn" "Comp.reach (Comp.srcOf trn)" "n\<gamma> (translateTrans trn)"
  then show "Comp.\<gamma> trn \<and> (Some o translateObs) (Comp.g trn) = Some (ng (translateTrans trn))"
  proof (cases trn rule: translateTrans.cases)
    case (4 sSub nid trnSub trnNode)
      with trn have "lreach nid (srcOf nid trnSub)" and "lreach NID (srcOf NID trnNode)"
        by (auto elim!: Comp.reach_reach12 Sub.reach_lreach)
      with trn 4 show ?thesis using isCom_\<gamma>[of nid trnSub] isCom_\<gamma>[of NID trnNode] by auto
  qed auto
next
  fix trn
  assume trn: "Comp.validTrans trn" "Comp.reach (Comp.srcOf trn)" "Comp.\<gamma> trn"
  then show "n\<gamma> (translateTrans trn) \<or> (Some o translateObs) (Comp.g trn) = None"
  proof (cases trn rule: translateTrans.cases)
    case (4 sSub nid trnSub trnNode)
      with trn have "lreach nid (srcOf nid trnSub)" and "lreach NID (srcOf NID trnNode)"
        by (auto elim!: Comp.reach_reach12 Sub.reach_lreach)
      with trn 4 show ?thesis by auto
  qed auto
next
  fix trn
  assume trn: "Comp.validTrans trn" "Comp.reach (Comp.srcOf trn)" "n\<phi> (translateTrans trn)"
  then show "Comp.\<phi> trn \<and> (Some o translateVal) (Comp.f trn) = Some (nf (translateTrans trn))"
  proof (cases trn rule: translateTrans.cases)
    case (4 sSub nid trnSub trnNode)
      with trn have "lreach nid (srcOf nid trnSub)" and "lreach NID (srcOf NID trnNode)"
        by (auto elim!: Comp.reach_reach12 Sub.reach_lreach)
      with trn 4 show ?thesis
        using sync_\<phi>1_\<phi>2[of nid trnSub NID trnNode] sync_\<phi>1_\<phi>2[of NID trnNode nid trnSub] by auto
  qed auto
next
  fix trn
  assume trn: "Comp.validTrans trn" "Comp.reach (Comp.srcOf trn)" "Comp.\<phi> trn"
  then show "n\<phi> (translateTrans trn) \<or> (Some o translateVal) (Comp.f trn) = None"
  proof (cases trn rule: translateTrans.cases)
    case (4 sSub nid trnSub trnNode)
      with trn have "lreach nid (srcOf nid trnSub)" and "lreach NID (srcOf NID trnNode)"
        by (auto elim!: Comp.reach_reach12 Sub.reach_lreach)
      with trn 4 show ?thesis by auto
  qed auto
next
  fix trn
  assume "Comp.T trn" "Comp.validTrans trn" "Comp.reach (Comp.srcOf trn)"
  then show "nT (translateTrans trn)" by (cases trn rule: translateTrans.cases) auto
next
  fix vl' vl1' tr
  let ?vl1 = "map invTranslateVal vl1'"
  assume nB: "nB vl' vl1'" and tr: "Comp.validFrom Comp.icstate tr"
     and vl':  "these (map (Some o translateVal) (Comp.V tr)) = vl'"
  moreover then have "list_all compValidV (Comp.V tr)" and "list_all compValidV ?vl1"
    by (auto intro: validFrom_istate_compValidV list_all_nValidV_compValidV list_all_compValidV_nValidV simp: nB_def)
  ultimately have "Comp.B (Comp.V tr) ?vl1" and "list_all nValidV vl1'"
    unfolding nB_def Comp.B_def Sub.nB_def
    by (auto simp: compV_decompV intro: nValidV_subDecompV list_all_compValidV_nValidV)
  then show "\<exists>vl1. these (map (Some o translateVal) vl1) = vl1' \<and> Comp.B (Comp.V tr) vl1"
    by (intro exI[of _ "?vl1"], auto)
       (metis list.map_comp map_translateVal_invTranslateVal these_map_Some)
qed

text \<open>Security for the composition of the network with the new node:\<close>

lemma secure_new_node:
assumes "Sub.secure" and "lsecure NID"
shows secure
using assms by (auto intro: Trans.translate_secure Comp.secure1_secure2_secure)

end

text \<open>Composing two sub-networks:\<close>

locale BD_Security_TS_Cut_Network = BD_Security_TS_Network
+
fixes nodesLeft and nodesRight
assumes
  nodesLeftRight_disjoint: "nodesLeft \<inter> nodesRight = {}"
and
  nodes_nodesLeftRight: "nodes = nodesLeft \<union> nodesRight"
and
  no_source_right: "source \<notin> nodesRight"
begin

lemma finite_nodesLeft: "finite nodesLeft" using finite_nodes nodes_nodesLeftRight by auto
lemma finite_nodesRight: "finite nodesRight" using finite_nodes nodes_nodesLeftRight by auto

sublocale Left: BD_Security_TS_Network_Change_Nodes where nodes' = "nodesLeft"
  using finite_nodesLeft no_source_right \<phi>_source nodes_nodesLeftRight
  by (unfold_locales) auto

text \<open>If the sub-network (potentially) containing the secret source is secure and all the nodes in
the other sub-network are locally secure, then the composition is secure.

The proof proceeds by finite set induction on the set of non-source nodes, using the above
infrastructure for adding new nodes to a network.\<close>

lemma merged_secure:
assumes "Left.secure"
and "\<forall>nid \<in> nodesRight. lsecure nid"
shows "secure"
using finite_nodesRight assms no_source_right nodesLeftRight_disjoint \<phi>_source unfolding nodes_nodesLeftRight
proof (induction rule: finite_induct)
  case (insert nid nodesMerged)
    interpret Left': BD_Security_TS_Network_Change_Nodes where nodes' = "nodesLeft \<union> nodesMerged"
      using finite_nodes nodes_nodesLeftRight insert by (unfold_locales) auto
    interpret Node: BD_Security_TS "istate nid" "validTrans nid" "srcOf nid" "tgtOf nid"
                                   "\<phi> nid" "f nid" "\<gamma> nid" "g nid" "T nid" "B nid" .
    have secure1: "Left'.secure" and secure2: "Node.secure" using insert by auto
    interpret Comp: BD_Security_TS_Network_New_Node_NoSource
      where nodes = "nodesLeft \<union> nodesMerged" and NID = nid
      using insert.prems insert.hyps by unfold_locales auto
    show ?case using secure1 secure2 using Comp.secure_new_node by auto
qed auto

end

context BD_Security_TS_Network
begin

text \<open>Putting it all together:\<close>

theorem network_secure:
assumes "\<forall>nid \<in> nodes. lsecure nid"
shows "secure"
proof (cases "source \<in> nodes")
  case True
    interpret BD_Security_TS_Cut_Network where nodesLeft = "{source}" and nodesRight = "nodes - {source}"
      using True by unfold_locales auto
    interpret Source_BD: BD_Security_Singleton_Source_Network by intro_locales

    show "secure" using assms Source_BD.translate_secure True by (intro merged_secure) auto
next
  case False
    interpret BD_Security_TS_Cut_Network where nodesLeft = "{}" and nodesRight = "nodes"
      using False by unfold_locales auto
    interpret Empty_BD: BD_Security_Empty_TS_Network by intro_locales

    show "secure" using assms Empty_BD.trivially_secure by (intro merged_secure)
qed

end

text \<open>Translating composite secrets using a function \<open>mergeSec\<close>:\<close>

datatype ('nodeid, 'sec, 'msec) merged_sec = LMSec 'nodeid 'sec | CMSec 'msec

locale BD_Security_TS_Network_MergeSec =
 Net?: BD_Security_TS_Network istate validTrans srcOf tgtOf nodes comOf tgtNodeOf sync \<phi> f
for istate :: "'nodeid \<Rightarrow> 'state"
and validTrans :: "'nodeid \<Rightarrow> 'trans \<Rightarrow> bool"
and srcOf :: "'nodeid \<Rightarrow> 'trans \<Rightarrow> 'state"
and tgtOf :: "'nodeid \<Rightarrow> 'trans \<Rightarrow> 'state"
and nodes :: "'nodeid set"
and comOf :: "'nodeid \<Rightarrow> 'trans \<Rightarrow> com"
and tgtNodeOf :: "'nodeid \<Rightarrow> 'trans \<Rightarrow> 'nodeid"
and sync :: "'nodeid \<Rightarrow> 'trans \<Rightarrow> 'nodeid \<Rightarrow> 'trans \<Rightarrow> bool"
and \<phi> :: "'nodeid \<Rightarrow> 'trans \<Rightarrow> bool"
and f :: "'nodeid \<Rightarrow> 'trans \<Rightarrow> 'sec" +
fixes mergeSec :: "'nodeid \<Rightarrow> 'sec \<Rightarrow> 'nodeid \<Rightarrow> 'sec \<Rightarrow> 'msec"
begin

inductive compSec :: "('nodeid \<Rightarrow> 'sec list) \<Rightarrow> ('nodeid, 'sec, 'msec) merged_sec list \<Rightarrow> bool"
where
  Nil: "compSec (\<lambda>_. []) []"
| Local: "\<lbrakk>compSec sls sl; isComV nid s \<longrightarrow> tgtNodeOfV nid s \<notin> nodes; nid \<in> nodes\<rbrakk>
          \<Longrightarrow> compSec (sls(nid := s # sls nid)) (LMSec nid s # sl)"
| Comm: "\<lbrakk>compSec sls sl; nid1 \<in> nodes; nid2 \<in> nodes; nid1 \<noteq> nid2;
          comOfV nid1 s1 = Send; tgtNodeOfV nid1 s1 = nid2;
          comOfV nid2 s2 = Recv; tgtNodeOfV nid2 s2 = nid1;
          syncV nid1 s1 nid2 s2\<rbrakk>
          \<Longrightarrow> compSec (sls(nid1 := s1 # sls nid1, nid2 := s2 # sls nid2))
                      (CMSec (mergeSec nid1 s1 nid2 s2) # sl)"

definition nB :: "('nodeid, 'sec, 'msec) merged_sec list \<Rightarrow> ('nodeid, 'sec, 'msec) merged_sec list \<Rightarrow> bool" where
"nB sl sl' \<equiv> \<forall>sls. compSec sls sl \<longrightarrow>
  (\<exists>sls'. compSec sls' sl' \<and> (\<forall>nid \<in> nodes. B nid (sls nid) (sls' nid)))"

fun nf :: "('nodeid, 'state, 'trans) ntrans \<Rightarrow> ('nodeid, 'sec, 'msec) merged_sec" where
  "nf (LTrans s nid trn) = LMSec nid (f nid trn)"
| "nf (CTrans s nid1 trn1 nid2 trn2) = CMSec (mergeSec nid1 (f nid1 trn1) nid2 (f nid2 trn2))"


sublocale BD_Security_TS istate nValidTrans nSrcOf nTgtOf n\<phi> nf n\<gamma> ng nT nB .


fun translateSec :: "('nodeid, 'sec) nvalue \<Rightarrow> ('nodeid, 'sec, 'msec) merged_sec" where
  "translateSec (LVal nid s) = LMSec nid s"
| "translateSec (CVal nid1 s1 nid2 s2) = CMSec (mergeSec nid1 s1 nid2 s2)"

lemma decompV_Cons_LVal: "decompV (LVal nid s # sl) = (decompV sl)(nid := s # decompV sl nid)"
by auto

lemma decompV_Cons_CVal:
assumes "nid1 \<noteq> nid2"
shows "decompV (CVal nid1 s1 nid2 s2 # sl) = (decompV sl)(nid1 := s1 # decompV sl nid1, nid2 := s2 # decompV sl nid2)"
using assms by auto

lemma nValidV_compSec:
assumes "list_all nValidV sl"
shows "compSec (decompV sl) (map translateSec sl)"
using assms proof (induction sl)
  case Nil then show ?case using compSec.Nil by auto
next
  case (Cons s sl)
  then have sl: "compSec (decompV sl) (map translateSec sl)" by auto
  show ?case proof (cases s)
    case (LVal nid1 s1)
    moreover with Cons sl have "compSec ((decompV sl)(nid1 := s1 # decompV sl nid1)) (LMSec nid1 s1 # map translateSec sl)"
      by (intro compSec.Local) auto
    ultimately show ?thesis unfolding LVal decompV_Cons_LVal[symmetric] by (auto simp del: decompV.simps)
  next
    case (CVal nid1 s1 nid2 s2)
    moreover with Cons sl have "compSec ((decompV sl)(nid1 := s1 # decompV sl nid1, nid2 := s2 # decompV sl nid2)) (CMSec (mergeSec nid1 s1 nid2 s2) # map translateSec sl)"
      by (intro compSec.Comm) auto
    moreover have n: "nid1 \<noteq> nid2" using CVal Cons by auto
    ultimately show ?thesis unfolding CVal decompV_Cons_CVal[OF n, symmetric] by (auto simp del: decompV.simps)
  qed
qed

lemma compSecE:
assumes "compSec sls sl"
obtains sl' where "decompV sl' = sls" and "map translateSec sl' = sl" and "list_all nValidV sl'"
using assms proof (induction)
  case Nil from this[of "[]"] show thesis by auto
next
  case (Local sls sl nid s)
  show thesis proof (rule Local.IH)
    fix sl'
    assume "decompV sl' = sls" and "map translateSec sl' = sl" and "list_all nValidV sl'"
    with Local.hyps show thesis by (intro Local.prems[of "LVal nid s # sl'"]) auto
  qed
next
  case (Comm sls sl nid1 nid2 s1 s2)
  show thesis proof (rule Comm.IH)
    fix sl'
    assume "decompV sl' = sls" and "map translateSec sl' = sl" and "list_all nValidV sl'"
    with Comm.hyps show thesis by (intro Comm.prems[of "CVal nid1 s1 nid2 s2 # sl'"]) auto
  qed
qed

interpretation Trans: BD_Security_TS_Trans istate nValidTrans nSrcOf nTgtOf n\<phi> Net.nf n\<gamma> ng nT Net.nB
                                           istate nValidTrans nSrcOf nTgtOf n\<phi> nf n\<gamma> ng nT nB
                                           id id Some "Some o translateSec"
proof (unfold_locales, goal_cases)
  case (8 trn)
  then show ?case by (cases trn) auto
next
  case (11 sl' sl1' tr)
  then have "list_all nValidV (Net.V tr)" by (auto intro: validFrom_nValidV reach.Istate)
  then have "compSec (decompV (Net.V tr)) (map translateSec (Net.V tr))" by (intro nValidV_compSec)
  then obtain sls1 where "compSec sls1 sl1'" and "\<forall>nid \<in> nodes. B nid (decompV (Net.V tr) nid) (sls1 nid)"
    using \<open>nB sl' sl1'\<close> \<open>these (map (Some \<circ> translateSec) (Net.V tr)) = sl'\<close> unfolding nB_def by auto
  moreover then obtain sl1 where "decompV sl1 = sls1" and "list_all nValidV sl1"
                             and "map translateSec sl1 = sl1'" by (elim compSecE)
  ultimately show ?case unfolding Net.nB_def by auto
qed auto

theorem network_secure:
assumes "\<forall>nid \<in> nodes. lsecure nid"
shows "secure"
using assms Net.network_secure Trans.translate_secure by blast

end

context BD_Security_TS_Network
begin

text \<open>In order to formalize a result about preserving the notion of secrets of the source node
upon composition, we define a notion of synchronization of secrets of the source and another node.\<close>

inductive srcSyncV :: "'nodeid \<Rightarrow> 'val list \<Rightarrow> 'val list \<Rightarrow> bool"
for nid :: "'nodeid"
where
  Nil: "srcSyncV nid [] []"
| Other: "\<lbrakk>srcSyncV nid vlSrc vlNode; \<not>isComV source v \<or> tgtNodeOfV source v \<noteq> nid\<rbrakk>
          \<Longrightarrow> srcSyncV nid (v # vlSrc) vlNode"
| Send: "\<lbrakk>srcSyncV nid vlSrc vlNode; comOfV source vSrc = Send; comOfV nid vNode = Recv;
          tgtNodeOfV source vSrc = nid; tgtNodeOfV nid vNode = source;
          syncV source vSrc nid vNode\<rbrakk> \<Longrightarrow> srcSyncV nid (vSrc # vlSrc) (vNode # vlNode)"
| Recv: "\<lbrakk>srcSyncV nid vlSrc vlNode; comOfV source vSrc = Recv; comOfV nid vNode = Send;
          tgtNodeOfV source vSrc = nid; tgtNodeOfV nid vNode = source;
          syncV nid vNode source vSrc\<rbrakk> \<Longrightarrow> srcSyncV nid (vSrc # vlSrc) (vNode # vlNode)"

text \<open>Sanity check that this is equivalent to a more general notion of binary secret
synchronisation applied to source secrets and target secrets, where the latter do not contain
internal secrets (in line with the assumption of unique secret polarization).\<close>

inductive binSyncV :: "'nodeid \<Rightarrow> 'nodeid \<Rightarrow> 'val list \<Rightarrow> 'val list \<Rightarrow> bool"
for nid1 nid2 :: "'nodeid"
where
  Nil: "binSyncV nid1 nid2 [] []"
| Int1: "\<lbrakk>binSyncV nid1 nid2 vl1 vl2; \<not>isComV nid1 v \<or> tgtNodeOfV nid1 v \<noteq> nid2\<rbrakk>
          \<Longrightarrow> binSyncV nid1 nid2 (v # vl1) vl2"
| Int2: "\<lbrakk>binSyncV nid1 nid2 vl1 vl2; \<not>isComV nid2 v \<or> tgtNodeOfV nid2 v \<noteq> nid1\<rbrakk>
          \<Longrightarrow> binSyncV nid1 nid2 vl1 (v # vl2)"
| Send: "\<lbrakk>binSyncV nid1 nid2 vl1 vl2; comOfV nid1 v1 = Send; comOfV nid2 v2 = Recv;
          tgtNodeOfV nid1 v1 = nid2; tgtNodeOfV nid2 v2 = nid1;
          syncV nid1 v1 nid2 v2\<rbrakk> \<Longrightarrow> binSyncV nid1 nid2 (v1 # vl1) (v2 # vl2)"
| Recv: "\<lbrakk>binSyncV nid1 nid2 vl1 vl2; comOfV nid1 v1 = Recv; comOfV nid2 v2 = Send;
          tgtNodeOfV nid1 v1 = nid2; tgtNodeOfV nid2 v2 = nid1;
          syncV nid2 v2 nid1 v1\<rbrakk> \<Longrightarrow> binSyncV nid1 nid2 (v1 # vl1) (v2 # vl2)"

lemma srcSyncV_binSyncV:
assumes "source \<in> nodes" and "nid2 \<in> nodes"
shows "srcSyncV nid2 vl1 vl2 \<longleftrightarrow> (binSyncV source nid2 vl1 vl2 \<and>
                                  list_all (\<lambda>v. isComV nid2 v \<and> tgtNodeOfV nid2 v = source) vl2)"
  (is "?l \<longleftrightarrow> ?r")
proof
  assume "?l"
  then show "?r" using assms by (induction rule: srcSyncV.induct) (auto intro: binSyncV.intros)
next
  assume "?r"
  then have "binSyncV source nid2 vl1 vl2"
        and "list_all (\<lambda>v. isComV nid2 v \<and> tgtNodeOfV nid2 v = source) vl2" by auto
  then show "?l" by (induction rule: binSyncV.induct) (auto intro: srcSyncV.intros)
qed

end

text \<open>We can obtain a security property for the network w.r.t. the original declassification bound
of the secret issuer node, if that bound is suitably reflected in the bounds of all the other nodes,
i.e. the bounds of the receiving nodes do not declassify any more confidential information than is
already declassified by the bound of the secret issuer node.\<close>

locale BD_Security_TS_Network_Preserve_Source_Security = Net?: BD_Security_TS_Network +
assumes source_in_nodes: "source \<in> nodes"
and source_secure: "lsecure source"
and B_source_in_B_sinks: "\<And>nid tr vl' vl1.
\<lbrakk>B source (lV source tr) vl1; srcSyncV nid (lV source tr) vl';
 lValidFrom source (istate source) tr; never (T source) tr;
 nid \<in> nodes; nid \<noteq> source\<rbrakk>
\<Longrightarrow> (\<exists>vl1'. B nid vl' vl1' \<and> srcSyncV nid vl1 vl1')"
begin

abbreviation "nodes' \<equiv> nodes - {source}"

fun nf' where
  "nf' (LTrans s nid trn) = f source trn"
| "nf' (CTrans s nid1 trn1 nid2 trn2) = (if nid1 = source then f source trn1 else f source trn2)"

fun translateVal where
  "translateVal (LVal nid v) = v"
| "translateVal (CVal nid1 v1 nid2 v2) = (if nid1 = source then v1 else v2)"

definition isProjectionOf where
  "isProjectionOf p vl = (\<forall>nid \<in> nodes'. srcSyncV nid vl (p nid))"

lemma nValidV_tgtNodeOf:
assumes "list_all nValidV vl'"
shows "list_all (\<lambda>v. isComV source v \<longrightarrow> tgtNodeOfV source v \<noteq> source) (decompV vl' source)"
using assms proof (induction vl')
  case (Cons v vl') then show ?case by (cases v) auto
qed auto

lemma lValidFrom_source_tgtNodeOfV:
assumes "lValidFrom source s tr"
and "lreach source s"
shows "list_all (\<lambda>v. isComV source v \<longrightarrow> tgtNodeOfV source v \<noteq> source) (lV source tr)"
     (is "?goal tr")
proof -
  interpret Node: BD_Security_TS "istate source" "validTrans source" "srcOf source" "tgtOf source"
                                 "\<phi> source" "f source" "\<gamma> source" "g source" "T source" "B source" .
  from assms show ?thesis proof (induction tr arbitrary: s)
    case (Cons trn tr s)
      have "?goal tr" using Cons.prems by (intro Cons.IH[of "tgtOf source trn"]) (auto intro: Node.reach.Step)
      then show ?case using Cons.prems isCom_tgtNodeOf by (cases "\<phi> source trn") auto
  qed auto
qed

lemma merge_projection:
assumes "isProjectionOf p vl"
and "list_all (\<lambda>v. isComV source v \<longrightarrow> tgtNodeOfV source v \<noteq> source) vl"
obtains vl' where "\<forall>nid \<in> nodes'. decompV vl' nid = p nid"
              and "decompV vl' source = vl"
              and "map translateVal vl' = vl"
              and "list_all nValidV vl'"
using assms proof (induction vl arbitrary: p)
  case (Nil p)
    from Nil.prems(2) show thesis
      by (intro Nil.prems(1)[of "[]"]) (auto simp: isProjectionOf_def elim!: ballE srcSyncV.cases)
next
  case (Cons v vl p)
    show thesis proof (cases "isComV source v \<and> tgtNodeOfV source v \<in> nodes")
      case False
        show thesis proof (rule Cons.IH[of p])
          show "isProjectionOf p vl"
            using Cons(3) False unfolding isProjectionOf_def by (auto elim: srcSyncV.cases)
          show "list_all (\<lambda>v. isComV source v \<longrightarrow> tgtNodeOfV source v \<noteq> source) vl"
            using Cons(4) by auto
        next
          fix vl'
          assume "\<forall>nid\<in>nodes'. decompV vl' nid = p nid" and "decompV vl' source = vl"
             and "map translateVal vl' = vl" and "list_all nValidV vl'"
          then show thesis
            using False source_in_nodes by (intro Cons(2)[of "LVal source v # vl'"]) auto
        qed
    next
      case True
        let ?tgt = "tgtNodeOfV source v"
        from True Cons(4) have nodes': "?tgt \<in> nodes'" by auto
        with Cons(3) obtain vn vln
        where p: "p ?tgt = vn # vln" and cmp: "srcSyncV ?tgt (v # vl) (vn # vln)"
          using True unfolding isProjectionOf_def
          by (cases "p ?tgt") (auto elim!: ballE elim: srcSyncV.cases)
        show thesis proof (rule Cons.IH[of "p(?tgt := vln)"])
          show "isProjectionOf (p(?tgt := vln)) vl"
            using Cons(3) True cmp unfolding isProjectionOf_def by (auto elim: srcSyncV.cases)
          show "list_all (\<lambda>v. isComV source v \<longrightarrow> tgtNodeOfV source v \<noteq> source) vl"
            using Cons(4) by auto
        next
          fix vl'
          assume vl': "\<forall>nid\<in>nodes'. decompV vl' nid = (p(?tgt := vln)) nid"
                      "decompV vl' source = vl" "map translateVal vl' = vl" "list_all nValidV vl'"
          show thesis proof cases
            assume "comOfV source v = Send"
            then show thesis using vl' p source_in_nodes True nodes' cmp
              by (intro Cons(2)[of "CVal source v ?tgt vn # vl'"]) (auto elim: srcSyncV.cases)
          next
            assume "comOfV source v \<noteq> Send"
            then show thesis using vl' p source_in_nodes True nodes' cmp
              by (intro Cons(2)[of "CVal ?tgt vn source v # vl'"]) (auto elim: srcSyncV.cases)
          qed
        qed
    qed
qed

lemma translateVal_decompV:
assumes "validFrom s tr"
and "reach s"
shows "map translateVal (V tr) = decompV (V tr) source"
using assms proof (induction tr arbitrary: s)
  case (Cons trn tr s)
    then have tr: "validFrom (nTgtOf trn) tr" and r: "reach (nTgtOf trn)"
      unfolding validFrom_Cons by (auto intro: reach.Step[of s trn])
    show ?case proof (cases trn)
      case (LTrans s' nid trn')
        moreover then have "\<phi> nid trn' \<longrightarrow> nid = source"
          using Cons.prems Net.\<phi>_source[of nid trn'] reach_lreach by auto
        ultimately show ?thesis using Cons.IH[OF tr r] by (cases "n\<phi> trn") auto
    next
      case (CTrans s' nid1 trn1 nid2 trn2)
        moreover then have "n\<phi> trn \<longrightarrow> (nid1 = source \<or> nid2 = source)"
          using Cons.prems Net.\<phi>_source[of nid1 trn1] Net.\<phi>_source[of nid2 trn2] reach_lreach
          by (cases "nid1 \<noteq> source") auto
        ultimately show ?thesis using Cons.IH[OF tr r] by (cases "n\<phi> trn") auto
    qed
qed auto

lemma srcSyncV_decompV:
assumes tr: "validFrom s tr"
and s: "reach s"
and "nid \<in> nodes" and "nid \<noteq> source"
shows "srcSyncV nid (decompV (V tr) source) (decompV (V tr) nid)"
using tr s proof (induction tr arbitrary: s)
  case (Cons trn tr s)
    then have trn: "nValidTrans trn" and tr: "validFrom (nTgtOf trn) tr" and r: "reach (nTgtOf trn)"
      unfolding validFrom_Cons by (auto intro: reach.Step[of s trn])
    show ?case proof (cases trn)
      case (LTrans s' nid' trn')
        show ?thesis proof (cases "\<phi> nid' trn'")
          case True
            then have "nid' = source"
              using Cons.prems Net.\<phi>_source[of nid' trn'] reach_lreach LTrans by auto
            then show ?thesis using Cons.IH[OF tr r] Cons.prems LTrans assms(3,4) True
              by (auto intro!: srcSyncV.Other elim: reach_lreach[of s nid'])
        next
          case False
            then show ?thesis using Cons.IH[OF tr r] LTrans by auto
        qed
    next
      case (CTrans s' nid1 trn1 nid2 trn2)
        have r1: "lreach nid1 (s' nid1)" and r2: "lreach nid2 (s' nid2)"
          using CTrans reach_lreach Cons.prems by auto
        show ?thesis proof (cases)
          assume \<phi>: "n\<phi> trn"
          then have "nid1 = source \<or> nid2 = source"
            using CTrans Cons.prems Net.\<phi>_source[of nid1 trn1] Net.\<phi>_source[of nid2 trn2] reach_lreach
            by (cases "nid1 \<noteq> source") auto
          moreover have "\<phi> nid1 trn1" and "\<phi> nid2 trn2" using CTrans trn r1 r2 \<phi> sync_\<phi>1_\<phi>2 by auto
          moreover then have "comOfV nid1 (f nid1 trn1) = comOf nid1 trn1"
                    and "isCom nid1 trn1 \<longrightarrow> tgtNodeOfV nid1 (f nid1 trn1) = tgtNodeOf nid1 trn1"
                    and "comOfV nid2 (f nid2 trn2) = comOf nid2 trn2"
                    and "isCom nid2 trn2 \<longrightarrow> tgtNodeOfV nid2 (f nid2 trn2) = tgtNodeOf nid2 trn2"
                    and "syncV nid1 (f nid1 trn1) nid2 (f nid2 trn2)"
            using CTrans trn r1 r2 by (auto intro: sync_syncV)
          ultimately show ?thesis
            using Cons.IH[OF tr r] trn assms(3,4) CTrans
            using srcSyncV.Send[OF Cons.IH[OF tr r], of "f nid1 trn1" "f nid2 trn2"]
            using srcSyncV.Recv[OF Cons.IH[OF tr r], of "f nid2 trn2" "f nid1 trn1"]
            using srcSyncV.Other[OF Cons.IH[OF tr r], of "f nid1 trn1"]
            using srcSyncV.Other[OF Cons.IH[OF tr r], of "f nid2 trn2"]
            by auto
        next
          assume "\<not>n\<phi> trn"
          with Cons.IH[OF tr r] show ?thesis by auto
        qed
    qed
qed (auto intro: srcSyncV.Nil)


sublocale BD_Security_TS_Trans istate nValidTrans nSrcOf nTgtOf n\<phi> nf n\<gamma> ng nT nB
                               istate nValidTrans nSrcOf nTgtOf n\<phi> nf' n\<gamma> ng nT "B source"
                               id id Some "Some o translateVal"
proof unfold_locales
  fix trn
  assume trn: "nValidTrans trn" and r: "reach (nSrcOf trn)" and \<phi>: "n\<phi> (id trn)"
  show "n\<phi> trn \<and> (Some \<circ> translateVal) (nf trn) = Some (nf' (id trn))"
  proof (cases trn)
    case (LTrans s nid trn')
      moreover then have "nid = source" using trn r \<phi> Net.\<phi>_source[of nid trn'] reach_lreach by auto
      ultimately show ?thesis using \<phi> by auto
  next
    case (CTrans s nid1 trn1 nid2 trn2)
      moreover then have "nid1 = source \<or> nid2 = source"
        using trn r \<phi> Net.\<phi>_source[of nid1 trn1] Net.\<phi>_source[of nid2 trn2] reach_lreach[OF r]
        by (cases "nid1 \<noteq> source") auto
      ultimately show ?thesis using \<phi> by auto
  qed
next
  fix vl' vl1' tr
  interpret Source: Transition_System "istate source" "validTrans source" "srcOf source" "tgtOf source" .
  assume "B source vl' vl1'" and tr: "validFrom istate tr" and nT: "never nT tr"
     and vl': "these (map (Some \<circ> translateVal) (V tr)) = vl'"
  then have B: "B source (decompV (V tr) source) vl1'"
    using reach.Istate by (auto simp: translateVal_decompV)
  then obtain tr1 where tr1: "lValidFrom source (istate source) tr1" and "lV source tr1 = vl1'"
    using source_secure validFrom_lValidFrom[OF tr, of source] decompV_decomp[OF tr reach.Istate] nT
    unfolding Abstract_BD_Security.secure_def by (auto intro: nTT_TT)
  then have "\<forall>nid \<in> nodes'. srcSyncV nid (decompV (V tr) source) (decompV (V tr) nid)"
        and tgt_vl1': "list_all (\<lambda>v. isComV source v \<longrightarrow> tgtNodeOfV source v \<noteq> source) vl1'"
    using B tr vl' reach.Istate srcSyncV_decompV nValidV_tgtNodeOf validFrom_nValidV
    using lValidFrom_source_tgtNodeOfV[OF tr1 Source.reach.Istate]
    by (auto simp: translateVal_decompV)
  then have "\<exists>p. \<forall>nid \<in> nodes'. B nid (decompV (V tr) nid) (p nid) \<and> srcSyncV nid vl1' (p nid)"
    using B B_source_in_B_sinks decompV_decomp[OF tr reach.Istate] validFrom_lValidFrom[OF tr, of source]
    using nT nTT_TT by (intro bchoice) auto
  then obtain p where "isProjectionOf p vl1'" and B': "\<forall>nid \<in> nodes'. B nid (decompV (V tr) nid) (p nid)"
    unfolding isProjectionOf_def by auto
  then obtain vl1 where p: "\<forall>nid \<in> nodes'. decompV vl1 nid = p nid" and vl1': "decompV vl1 source = vl1'"
                    and "map translateVal vl1 = vl1'" and "list_all nValidV vl1"
    using tgt_vl1' by (elim merge_projection) auto
  moreover have "\<forall>nid \<in> nodes. B nid (decompV (V tr) nid) (decompV vl1 nid)" proof
    fix nid
    assume "nid \<in> nodes"
    then show "B nid (decompV (V tr) nid) (decompV vl1 nid)"
      using B vl1' B' p by (cases "nid = source") auto
  qed
  ultimately show "\<exists>vl1. these (map (Some \<circ> translateVal) vl1) = vl1' \<and> nB (V tr) vl1"
    using B tr vl' reach.Istate
    by (intro exI[of _ vl1]) (auto simp: nB_def)
qed auto

theorem preserve_source_secure:
assumes "\<forall>nid \<in> nodes'. lsecure nid"
shows "secure"
using assms source_secure
by (intro translate_secure network_secure ballI) auto

end

text \<open>We can simplify the check that the bound of the source node is reflected in those of the
other nodes with the help of a function mapping secrets communicated by the source node to those
of the target nodes.\<close>

locale BD_Security_TS_Network_getTgtV = BD_Security_TS_Network +
fixes getTgtV
assumes getTgtV_Send: "comOfV source vSrc = Send \<Longrightarrow> tgtNodeOfV source vSrc = nid \<Longrightarrow> nid \<noteq> source \<Longrightarrow> (syncV source vSrc nid vn \<longleftrightarrow> vn = getTgtV vSrc) \<and> tgtNodeOfV nid (getTgtV vSrc) = source \<and> comOfV nid (getTgtV vSrc) = Recv"
and getTgtV_Recv: "comOfV source vSrc = Recv \<Longrightarrow> tgtNodeOfV source vSrc = nid \<Longrightarrow> nid \<noteq> source \<Longrightarrow> (syncV nid vn source vSrc \<longleftrightarrow> vn = getTgtV vSrc) \<and> tgtNodeOfV nid (getTgtV vSrc) = source \<and> comOfV nid (getTgtV vSrc) = Send"
begin

abbreviation "projectSrcV nid vlSrc
 \<equiv> map getTgtV (filter (\<lambda>v. isComV source v \<and> tgtNodeOfV source v = nid) vlSrc)"

lemma srcSyncV_projectSrcV:
assumes "nid \<in> nodes - {source}"
shows "srcSyncV nid vlSrc vln \<longleftrightarrow> vln = projectSrcV nid vlSrc"
proof
  assume "srcSyncV nid vlSrc vln"
  then show "vln = projectSrcV nid vlSrc" using assms getTgtV_Send getTgtV_Recv by induction auto
next
  assume "vln = projectSrcV nid vlSrc"
  moreover have "srcSyncV nid vlSrc (projectSrcV nid vlSrc)"
    using assms getTgtV_Send getTgtV_Recv by (induction vlSrc) (auto intro: srcSyncV.intros)
  ultimately show "srcSyncV nid vlSrc vln" by simp
qed

end

locale BD_Security_TS_Network_Preserve_Source_Security_getTgtV = Net?: BD_Security_TS_Network_getTgtV +
assumes source_in_nodes: "source \<in> nodes"
and source_secure: "lsecure source"
and B_source_in_B_sinks: "\<And>nid tr vl vl1.
\<lbrakk>B source vl vl1; vl = lV source tr; lValidFrom source (istate source) tr; never (T source) tr;
 nid \<in> nodes; nid \<noteq> source\<rbrakk>
\<Longrightarrow> B nid (projectSrcV nid vl) (projectSrcV nid vl1)"
begin

sublocale BD_Security_TS_Network_Preserve_Source_Security
using source_in_nodes source_secure B_source_in_B_sinks srcSyncV_projectSrcV
by (unfold_locales) auto

end

text \<open>An alternative composition setup that derives parameters \<open>comOfV\<close>, \<open>syncV\<close>, etc. from
\<open>comOf\<close>, \<open>sync\<close>, etc.\<close>

locale BD_Security_TS_Network' = TS_Network istate validTrans srcOf tgtOf nodes comOf tgtNodeOf sync
for
   istate :: "('nodeid, 'state) nstate" and validTrans :: "'nodeid \<Rightarrow> 'trans \<Rightarrow> bool"
 and
   srcOf :: "'nodeid \<Rightarrow> 'trans \<Rightarrow> 'state" and tgtOf :: "'nodeid \<Rightarrow> 'trans \<Rightarrow> 'state"
 and
   nodes :: "'nodeid set"
 and
   comOf :: "'nodeid \<Rightarrow> 'trans \<Rightarrow> com"
 and
   tgtNodeOf :: "'nodeid \<Rightarrow> 'trans \<Rightarrow> 'nodeid"
 and
   sync :: "'nodeid \<Rightarrow> 'trans \<Rightarrow> 'nodeid \<Rightarrow> 'trans \<Rightarrow> bool"
+
fixes
   \<phi> :: "'nodeid \<Rightarrow> 'trans \<Rightarrow> bool" and f :: "'nodeid \<Rightarrow> 'trans \<Rightarrow> 'val"
 and
   \<gamma> :: "'nodeid \<Rightarrow> 'trans \<Rightarrow> bool" and g :: "'nodeid \<Rightarrow> 'trans \<Rightarrow> 'obs"
 and
   T :: "'nodeid \<Rightarrow> 'trans \<Rightarrow> bool" and B :: "'nodeid \<Rightarrow> 'val list \<Rightarrow> 'val list \<Rightarrow> bool"
 and
   source :: "'nodeid"
assumes
  g_comOf: "\<And>nid trn1 trn2.
    \<lbrakk>validTrans nid trn1; lreach nid (srcOf nid trn1); \<gamma> nid trn1;
     validTrans nid trn2; lreach nid (srcOf nid trn2); \<gamma> nid trn2;
     g nid trn2 = g nid trn1\<rbrakk> \<Longrightarrow> comOf nid trn2 = comOf nid trn1"
and
  f_comOf: "\<And>nid trn1 trn2.
    \<lbrakk>validTrans nid trn1; lreach nid (srcOf nid trn1); \<phi> nid trn1;
     validTrans nid trn2; lreach nid (srcOf nid trn2); \<phi> nid trn2;
     f nid trn2 = f nid trn1\<rbrakk> \<Longrightarrow> comOf nid trn2 = comOf nid trn1"
and
  g_tgtNodeOf: "\<And>nid trn1 trn2.
    \<lbrakk>validTrans nid trn1; lreach nid (srcOf nid trn1); \<gamma> nid trn1;
     validTrans nid trn2; lreach nid (srcOf nid trn2); \<gamma> nid trn2;
     g nid trn2 = g nid trn1\<rbrakk> \<Longrightarrow> tgtNodeOf nid trn2 = tgtNodeOf nid trn1"
and
  f_tgtNodeOf: "\<And>nid trn1 trn2.
    \<lbrakk>validTrans nid trn1; lreach nid (srcOf nid trn1); \<phi> nid trn1;
     validTrans nid trn2; lreach nid (srcOf nid trn2); \<phi> nid trn2;
     f nid trn2 = f nid trn1\<rbrakk> \<Longrightarrow> tgtNodeOf nid trn2 = tgtNodeOf nid trn1"
and
  sync_\<phi>1_\<phi>2:
  "\<And>nid1 trn1 nid2 trn2.
       validTrans nid1 trn1 \<Longrightarrow> lreach nid1 (srcOf nid1 trn1) \<Longrightarrow>
       validTrans nid2 trn2 \<Longrightarrow> lreach nid2 (srcOf nid2 trn2) \<Longrightarrow>
       comOf nid1 trn1 = Send \<Longrightarrow> tgtNodeOf nid1 trn1 = nid2 \<Longrightarrow>
       comOf nid2 trn2 = Recv \<Longrightarrow> tgtNodeOf nid2 trn2 = nid1 \<Longrightarrow>
       sync nid1 trn1 nid2 trn2 \<Longrightarrow> \<phi> nid1 trn1 \<longleftrightarrow> \<phi> nid2 trn2"
and
  sync_\<phi>_\<gamma>:
  "\<And>nid1 trn1 nid2 trn2.
     validTrans nid1 trn1 \<Longrightarrow> lreach nid1 (srcOf nid1 trn1) \<Longrightarrow>
     validTrans nid2 trn2 \<Longrightarrow> lreach nid2 (srcOf nid2 trn2) \<Longrightarrow>
     comOf nid1 trn1 = Send \<Longrightarrow> tgtNodeOf nid1 trn1 = nid2 \<Longrightarrow>
     comOf nid2 trn2 = Recv \<Longrightarrow> tgtNodeOf nid2 trn2 = nid1 \<Longrightarrow>
     (\<gamma> nid1 trn1 \<Longrightarrow> \<gamma> nid2 trn2 \<Longrightarrow>
      \<exists>trn1' trn2'.
        validTrans nid1 trn1' \<and> lreach nid1 (srcOf nid1 trn1') \<and> \<gamma> nid1 trn1' \<and> g nid1 trn1' = g nid1 trn1 \<and>
        validTrans nid2 trn2' \<and> lreach nid2 (srcOf nid2 trn2') \<and> \<gamma> nid2 trn2' \<and> g nid2 trn2' = g nid2 trn2 \<and>
        sync nid1 trn1' nid2 trn2') \<Longrightarrow>
     (\<phi> nid1 trn1 \<Longrightarrow> \<phi> nid2 trn2 \<Longrightarrow>
      \<exists>trn1' trn2'.
        validTrans nid1 trn1' \<and> lreach nid1 (srcOf nid1 trn1') \<and> \<phi> nid1 trn1' \<and> f nid1 trn1' = f nid1 trn1 \<and>
        validTrans nid2 trn2' \<and> lreach nid2 (srcOf nid2 trn2') \<and> \<phi> nid2 trn2' \<and> f nid2 trn2' = f nid2 trn2 \<and>
        sync nid1 trn1' nid2 trn2')
     \<Longrightarrow>
     sync nid1 trn1 nid2 trn2"
and
  isCom_\<gamma>: "\<And>nid trn. validTrans nid trn \<Longrightarrow> lreach nid (srcOf nid trn) \<Longrightarrow> comOf nid trn = Send \<or> comOf nid trn = Recv \<Longrightarrow> \<gamma> nid trn"
and
  \<phi>_source: "\<And>nid trn. \<lbrakk>validTrans nid trn; lreach nid (srcOf nid trn); \<phi> nid trn; nid \<noteq> source; nid \<in> nodes\<rbrakk>
                        \<Longrightarrow> isCom nid trn \<and> tgtNodeOf nid trn = source \<and> source \<in> nodes"
begin

definition "reachableO nid obs = (\<exists>trn. validTrans nid trn \<and> lreach nid (srcOf nid trn) \<and> \<gamma> nid trn \<and> g nid trn = obs)"
definition "reachableV nid sec = (\<exists>trn. validTrans nid trn \<and> lreach nid (srcOf nid trn) \<and> \<phi> nid trn \<and> f nid trn = sec)"

definition "invO nid obs = inv_into {trn. validTrans nid trn \<and> lreach nid (srcOf nid trn) \<and> \<gamma> nid trn} (g nid) obs"
definition "invV nid sec = inv_into {trn. validTrans nid trn \<and> lreach nid (srcOf nid trn) \<and> \<phi> nid trn} (f nid) sec"

definition "comOfO nid obs = (if reachableO nid obs then comOf nid (invO nid obs) else Internal)"
definition "tgtNodeOfO nid obs = tgtNodeOf nid (invO nid obs)"
definition "comOfV nid sec = (if reachableV nid sec then comOf nid (invV nid sec) else Internal)"
definition "tgtNodeOfV nid sec = tgtNodeOf nid (invV nid sec)"
definition "syncO nid1 obs1 nid2 obs2 =
  (\<exists>trn1 trn2. validTrans nid1 trn1 \<and> lreach nid1 (srcOf nid1 trn1) \<and> \<gamma> nid1 trn1 \<and> g nid1 trn1 = obs1 \<and>
               validTrans nid2 trn2 \<and> lreach nid2 (srcOf nid2 trn2) \<and> \<gamma> nid2 trn2 \<and> g nid2 trn2 = obs2 \<and>
               sync nid1 trn1 nid2 trn2)"
definition "syncV nid1 sec1 nid2 sec2 =
  (\<exists>trn1 trn2. validTrans nid1 trn1 \<and> lreach nid1 (srcOf nid1 trn1) \<and> \<phi> nid1 trn1 \<and> f nid1 trn1 = sec1 \<and>
               validTrans nid2 trn2 \<and> lreach nid2 (srcOf nid2 trn2) \<and> \<phi> nid2 trn2 \<and> f nid2 trn2 = sec2 \<and>
               sync nid1 trn1 nid2 trn2)"

lemmas comp_O_V_defs = comOfO_def tgtNodeOfO_def comOfV_def tgtNodeOfV_def syncO_def syncV_def
                       reachableO_def reachableV_def

lemma reachableV_D:
assumes "reachableV nid sec"
shows "validTrans nid (invV nid sec)" and "lreach nid (srcOf nid (invV nid sec))"
  and "\<phi> nid (invV nid sec)" and "f nid (invV nid sec) = sec"
using assms unfolding reachableV_def invV_def inv_into_def by (auto intro: someI2_ex)

lemma reachableO_D:
assumes "reachableO nid obs"
shows "validTrans nid (invO nid obs)" and "lreach nid (srcOf nid (invO nid obs))"
  and "\<gamma> nid (invO nid obs)" and "g nid (invO nid obs) = obs"
using assms unfolding reachableO_def invO_def inv_into_def by (auto intro: someI2_ex)

sublocale BD_Security_TS_Network
where comOfV = comOfV and tgtNodeOfV = tgtNodeOfV and syncV = syncV
  and comOfO = comOfO and tgtNodeOfO = tgtNodeOfO and syncO = syncO
proof (unfold_locales, goal_cases)
  case (1 nid trn) then show ?case by (auto intro!: f_comOf reachableV_D simp: comp_O_V_defs) next
  case (2 nid trn) then show ?case by (auto intro!: f_tgtNodeOf reachableV_D simp: comp_O_V_defs) next
  case (3 nid trn) then show ?case by (auto intro!: g_comOf reachableO_D simp: comp_O_V_defs)
  case (4 nid trn) then show ?case by (auto intro!: g_tgtNodeOf reachableO_D simp: comp_O_V_defs) next
  case (5 nid1 trn1 nid2 trn2) then show ?case unfolding comp_O_V_defs by auto next
  case (6 nid1 trn1 nid2 trn2) then show ?case unfolding comp_O_V_defs by auto next
  case (7 nid1 trn1 nid2 trn2) then show ?case using sync_\<phi>1_\<phi>2 by blast next
  case (8 nid1 trn1 nid2 trn2) then show ?case unfolding comp_O_V_defs by (intro sync_\<phi>_\<gamma>) next
  case (9 nid trn) then show ?case by (intro isCom_\<gamma>) next
  case (10 nid trn) then show ?case by (intro \<phi>_source)
qed

lemma comOf_invV:
assumes "validTrans nid trn" and "lreach nid (srcOf nid trn)" and "\<phi> nid trn"
shows "comOf nid (invV nid (f nid trn)) = comOf nid trn"
using assms by (auto intro!: f_comOf reachableV_D simp: reachableV_def)

lemma comOfV_SendE:
assumes "comOfV nid v = Send"
obtains trn where "validTrans nid trn" and "lreach nid (srcOf nid trn)" and "\<phi> nid trn" and "f nid trn = v"
              and "comOf nid trn = Send"
using assms unfolding comOfV_def by (auto simp: reachableV_def comOf_invV split: if_splits)

lemma comOfV_RecvE:
assumes "comOfV nid v = Recv"
obtains trn where "validTrans nid trn" and "lreach nid (srcOf nid trn)" and "\<phi> nid trn" and "f nid trn = v"
              and "comOf nid trn = Recv"
using assms unfolding comOfV_def by (auto simp: reachableV_def comOf_invV split: if_splits)

fun secComp :: "('nodeid, 'val) nvalue list \<Rightarrow> bool" where
  "secComp [] = True"
| "secComp (LVal nid s # sl) =
    (secComp sl \<and> nid \<in> nodes \<and>
     \<not>(\<exists>trn. validTrans nid trn \<and> lreach nid (srcOf nid trn) \<and> \<phi> nid trn \<and> f nid trn = s \<and>
             (comOf nid trn = Send \<or> comOf nid trn = Recv) \<and> tgtNodeOf nid trn \<in> nodes))"
| "secComp (CVal nid1 s1 nid2 s2 # sl) =
    (secComp sl \<and> nid1 \<in> nodes \<and> nid2 \<in> nodes \<and> nid1 \<noteq> nid2 \<and>
     (\<exists>trn1 trn2. validTrans nid1 trn1 \<and> lreach nid1 (srcOf nid1 trn1) \<and> \<phi> nid1 trn1 \<and> f nid1 trn1 = s1 \<and>
                  validTrans nid2 trn2 \<and> lreach nid2 (srcOf nid2 trn2) \<and> \<phi> nid2 trn2 \<and> f nid2 trn2 = s2 \<and>
                  comOf nid1 trn1 = Send \<and> tgtNodeOf nid1 trn1 = nid2 \<and>
                  comOf nid2 trn2 = Recv \<and> tgtNodeOf nid2 trn2 = nid1 \<and>
                  sync nid1 trn1 nid2 trn2))"

lemma syncedSecs_iff_nValidV: "secComp sl \<longleftrightarrow> list_all nValidV sl"
proof (induction sl rule: secComp.induct)
  case 2 then show ?case by (auto elim!: comOfV_SendE comOfV_RecvE) next
  case (3 nid1 v1 nid2 v2 sl)
    have "nValidV (CVal nid1 v1 nid2 v2) =
            (\<exists>trn1 trn2. nid1 \<in> nodes \<and> nid2 \<in> nodes \<and> nid1 \<noteq> nid2 \<and>
               validTrans nid1 trn1 \<and> lreach nid1 (srcOf nid1 trn1) \<and> \<phi> nid1 trn1 \<and> f nid1 trn1 = v1 \<and>
               validTrans nid2 trn2 \<and> lreach nid2 (srcOf nid2 trn2) \<and> \<phi> nid2 trn2 \<and> f nid2 trn2 = v2 \<and>
               comOf nid1 trn1 = Send \<and> tgtNodeOf nid1 trn1 = nid2 \<and>
               comOf nid2 trn2 = Recv \<and> tgtNodeOf nid2 trn2 = nid1 \<and>
               sync nid1 trn1 nid2 trn2)"
      by (auto simp: syncV_def) blast
    with 3 show ?case by auto
qed auto

lemma nB_secComp:
  "nB sl sl1 \<longleftrightarrow> (\<forall>nid \<in> nodes. B nid (decompV sl nid) (decompV sl1 nid)) \<and>
                                (secComp sl \<longrightarrow> secComp sl1)"
unfolding nB_def syncedSecs_iff_nValidV ..

end


end
