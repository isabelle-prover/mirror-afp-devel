section \<open>Binary compositionality theorem\<close>

text \<open>This theory provides the binary version of
the compositionality theorem for BD security.
It corresponds to Theorem 1 from \<^cite>\<open>"cosmedis-SandP2017"\<close>
and to Theorem 5 (the System Compositionality Theorem) from
\<^cite>\<open>"BDsecurity-ITP2021"\<close>.
\<close>

theory Composing_Security
  imports Bounded_Deducibility_Security.BD_Security_TS
begin

(* Preliminaries *)


lemma list2_induct[case_names NilNil Cons1 Cons2]:
assumes NN: "P [] []"
and CN: "\<And>x xs ys. P xs ys \<Longrightarrow> P (x # xs) ys"
and NC: "\<And>xs y ys. P xs ys \<Longrightarrow> P xs (y # ys)"
shows "P xs ys"
proof (induction xs)
  case Nil show ?case using NN NC by (induction ys) auto next
  case (Cons x xs) then show ?case using CN by auto
qed

lemma list22_induct[case_names NilNil ConsNil NilCons ConsCons]:
assumes NN: "P [] []"
and CN: "\<And>x xs. P xs [] \<Longrightarrow> P (x # xs) []"
and NC: "\<And>y ys. P [] ys \<Longrightarrow> P [] (y # ys)"
and CC: "\<And>x xs y ys.
   P xs ys \<Longrightarrow>
   (\<And> ys'. length ys' \<le> Suc (length ys) \<Longrightarrow> P xs ys') \<Longrightarrow>
   (\<And> xs'. length xs' \<le> Suc (length xs) \<Longrightarrow> P xs' ys) \<Longrightarrow>
   P (x # xs) (y # ys)"
shows "P xs ys"
proof (induction rule: measure_induct2[of "\<lambda>xs ys. length xs + length ys", case_names IH])
  case (IH xs ys) with assms show ?case by (cases xs; cases ys) auto
qed


context BD_Security_TS begin

declare O_append[simp]
declare V_append[simp]
declare validFrom_Cons[simp]
declare validFrom_append[simp]

declare list_all_O_map[simp]
declare never_O_Nil[simp]
declare list_all_V_map[simp]
declare never_V_Nil[simp]

end (* BD_Security_NIO_Aut *)


locale Abstract_BD_Security_Comp =
  One: Abstract_BD_Security validSystemTraces1 V1 O1 B1 TT1 +
  Two: Abstract_BD_Security validSystemTraces2 V2 O2 B2 TT2 +
  Comp?: Abstract_BD_Security validSystemTraces V O B TT (* Note: the "Comp" prefix will be optional *)
for
   validSystemTraces1 :: "'traces1 \<Rightarrow> bool"
 and
   V1 :: "'traces1 \<Rightarrow> 'values1" and O1 :: "'traces1 \<Rightarrow> 'observations1"
 and
   TT1 :: "'traces1 \<Rightarrow> bool"
 and
   B1 :: "'values1 \<Rightarrow> 'values1 \<Rightarrow> bool"
 and
(*  *)
   validSystemTraces2 :: "'traces2 \<Rightarrow> bool"
 and
   V2 :: "'traces2 \<Rightarrow> 'values2" and O2 :: "'traces2 \<Rightarrow> 'observations2"
 and
   TT2 :: "'traces2 \<Rightarrow> bool"
 and
   B2 :: "'values2 \<Rightarrow> 'values2 \<Rightarrow> bool"
 and
 (*  *)
   validSystemTraces :: "'traces \<Rightarrow> bool"
 and
   V :: "'traces \<Rightarrow> 'values" and O :: "'traces \<Rightarrow> 'observations"
 and
   TT :: "'traces \<Rightarrow> bool"
 and
   B :: "'values \<Rightarrow> 'values \<Rightarrow> bool"
+
fixes
   comp :: "'traces1 \<Rightarrow> 'traces2 \<Rightarrow> 'traces \<Rightarrow> bool"
 and
   compO :: "'observations1 \<Rightarrow> 'observations2 \<Rightarrow> 'observations \<Rightarrow> bool"
 and
   compV :: "'values1 \<Rightarrow> 'values2 \<Rightarrow> 'values \<Rightarrow> bool"
assumes
validSystemTraces:
"\<And> tr. validSystemTraces tr \<Longrightarrow>
 (\<exists> tr1 tr2. validSystemTraces1 tr1 \<and> validSystemTraces2 tr2 \<and> comp tr1 tr2 tr)"
and
V_comp:
"\<And> tr1 tr2 tr.
   validSystemTraces1 tr1 \<Longrightarrow> validSystemTraces2 tr2 \<Longrightarrow> comp tr1 tr2 tr
   \<Longrightarrow> compV (V1 tr1) (V2 tr2) (V tr)"
and
O_comp:
"\<And> tr1 tr2 tr.
   validSystemTraces1 tr1 \<Longrightarrow> validSystemTraces2 tr2 \<Longrightarrow> comp tr1 tr2 tr
   \<Longrightarrow> compO (O1 tr1) (O2 tr2) (O tr)"
and
TT_comp:
"\<And> tr1 tr2 tr.
   validSystemTraces1 tr1 \<Longrightarrow> validSystemTraces2 tr2 \<Longrightarrow> comp tr1 tr2 tr
   \<Longrightarrow> TT tr \<Longrightarrow> TT1 tr1 \<and> TT2 tr2"
and
B_comp:
"\<And> vl1 vl2 vl vl'.
   compV vl1 vl2 vl \<Longrightarrow> B vl vl'
   \<Longrightarrow> \<exists> vl1' vl2'. compV vl1' vl2' vl' \<and> B1 vl1 vl1' \<and> B2 vl2 vl2'"
and
O_V_comp:
"\<And> tr1 tr2 vl ol.
   validSystemTraces1 tr1 \<Longrightarrow> validSystemTraces2 tr2 \<Longrightarrow>
   compV (V1 tr1) (V2 tr2) vl \<Longrightarrow> compO (O1 tr1) (O2 tr2) ol
   \<Longrightarrow> \<exists> tr. validSystemTraces tr \<and> O tr = ol \<and> V tr = vl"
begin

abbreviation secure where "secure \<equiv> Comp.secure"
abbreviation secure1 where "secure1 \<equiv> One.secure"
abbreviation secure2 where "secure2 \<equiv> Two.secure"

theorem secure1_secure2_secure:
assumes s1: secure1 and s2: secure2
shows secure
unfolding secure_def proof clarify
  fix tr vl vl'
  assume v: "validSystemTraces tr" and T: "TT tr" and B: "B (V tr) vl'"
  then obtain tr1 tr2 where v1: "validSystemTraces1 tr1" and v2: "validSystemTraces2 tr2"
  and tr: "comp tr1 tr2 tr" using validSystemTraces by blast
  have T1: "TT1 tr1" and T2: "TT2 tr2" using TT_comp[OF v1 v2 tr T] by auto
  have Vtr: "compV (V1 tr1) (V2 tr2) (V tr)" using V_comp[OF v1 v2 tr] .
  have Otr: "compO (O1 tr1) (O2 tr2) (O tr)" using O_comp[OF v1 v2 tr] .
  obtain vl1' vl2' where vl': "compV vl1' vl2' vl'" and
  B1: "B1 (V1 tr1) vl1'" and B2: "B2 (V2 tr2) vl2'" using B_comp[OF Vtr B] by auto
  obtain tr1' where v1': "validSystemTraces1 tr1'" and O1: "O1 tr1 = O1 tr1'" and vl1': "vl1' = V1 tr1'"
  using s1 v1 T1 B1 unfolding One.secure_def by fastforce
  obtain tr2' where v2': "validSystemTraces2 tr2'" and O2: "O2 tr2 = O2 tr2'" and vl2': "vl2' = V2 tr2'"
  using s2 v2 T2 B2 unfolding Two.secure_def by fastforce
  obtain tr' where "validSystemTraces tr' \<and> O tr' = O tr \<and> V tr' = vl'"
  using O_V_comp[OF v1' v2' vl'[unfolded vl1' vl2'] Otr[unfolded O1 O2]] by auto
  thus "\<exists>tr'. validSystemTraces tr' \<and> O tr' = O tr \<and> V tr' = vl'" by auto
qed

end (* context BD_Security_Comp *)


type_synonym ('state1,'state2) cstate = "'state1 \<times> 'state2"
datatype ('state1,'trans1,'state2,'trans2) ctrans = Trans1 'state2 'trans1 | Trans2 'state1 'trans2 | CTrans 'trans1 'trans2
datatype ('obs1,'obs2) cobs = Obs1 'obs1 | Obs2 'obs2 | CObs 'obs1 'obs2
datatype ('value1,'value2) "cvalue" = isValue1: Value1 'value1 | isValue2: Value2 'value2 | isCValue: CValue 'value1 'value2


locale BD_Security_TS_Comp =
  One: BD_Security_TS istate1 validTrans1 srcOf1 tgtOf1 \<phi>1 f1 \<gamma>1 g1 T1 B1 +
  Two: BD_Security_TS istate2 validTrans2 srcOf2 tgtOf2 \<phi>2 f2 \<gamma>2 g2 T2 B2
for
   istate1 :: "'state1" and validTrans1 :: "'trans1 \<Rightarrow> bool"
 and
   srcOf1 :: "'trans1 \<Rightarrow> 'state1" and tgtOf1 :: "'trans1 \<Rightarrow> 'state1"
 and
   \<phi>1 :: "'trans1 \<Rightarrow> bool" and f1 :: "'trans1 \<Rightarrow> 'value1"
 and
   \<gamma>1 :: "'trans1 \<Rightarrow> bool" and g1 :: "'trans1 \<Rightarrow> 'obs1"
 and
   T1 :: "'trans1 \<Rightarrow> bool" and B1 :: "'value1 list \<Rightarrow> 'value1 list \<Rightarrow> bool"
 and
 (*  *)
   istate2 :: "'state2" and validTrans2 :: "'trans2 \<Rightarrow> bool"
 and
   srcOf2 :: "'trans2 \<Rightarrow> 'state2" and tgtOf2 :: "'trans2 \<Rightarrow> 'state2"
 and
   \<phi>2 :: "'trans2 \<Rightarrow> bool" and f2 :: "'trans2 \<Rightarrow> 'value2"
 and
   \<gamma>2 :: "'trans2 \<Rightarrow> bool" and g2 :: "'trans2 \<Rightarrow> 'obs2"
 and
   T2 :: "'trans2 \<Rightarrow> bool" and B2 :: "'value2 list \<Rightarrow> 'value2 list \<Rightarrow> bool"
+
fixes (* An identification of the communication transitions and of the synchronization predicate:  *)
  isCom1 :: "'trans1 \<Rightarrow> bool" and isCom2 :: "'trans2 \<Rightarrow> bool"
and
  sync :: "'trans1 \<Rightarrow> 'trans2 \<Rightarrow> bool"
and
  isComV1 :: "'value1 \<Rightarrow> bool" and isComV2 :: "'value2 \<Rightarrow> bool"
and
  syncV :: "'value1 \<Rightarrow> 'value2 \<Rightarrow> bool"
and
  isComO1 :: "'obs1 \<Rightarrow> bool" and isComO2 :: "'obs2 \<Rightarrow> bool"
and
  syncO :: "'obs1 \<Rightarrow> 'obs2 \<Rightarrow> bool"
(*  *)
assumes
  isCom1_isComV1: "\<And> trn1. validTrans1 trn1 \<Longrightarrow> One.reach (srcOf1 trn1) \<Longrightarrow> \<phi>1 trn1 \<Longrightarrow> isCom1 trn1 \<longleftrightarrow> isComV1 (f1 trn1)"
and
  isCom1_isComO1: "\<And> trn1. validTrans1 trn1 \<Longrightarrow> One.reach (srcOf1 trn1) \<Longrightarrow> \<gamma>1 trn1 \<Longrightarrow> isCom1 trn1 \<longleftrightarrow> isComO1 (g1 trn1)"
and
  isCom2_isComV2: "\<And> trn2. validTrans2 trn2 \<Longrightarrow> Two.reach (srcOf2 trn2) \<Longrightarrow> \<phi>2 trn2 \<Longrightarrow> isCom2 trn2 \<longleftrightarrow> isComV2 (f2 trn2)"
and
  isCom2_isComO2: "\<And> trn2. validTrans2 trn2 \<Longrightarrow> Two.reach (srcOf2 trn2) \<Longrightarrow> \<gamma>2 trn2 \<Longrightarrow> isCom2 trn2 \<longleftrightarrow> isComO2 (g2 trn2)"
and
  sync_syncV:
  "\<And> trn1 trn2.
       validTrans1 trn1 \<Longrightarrow> One.reach (srcOf1 trn1) \<Longrightarrow>
       validTrans2 trn2 \<Longrightarrow> Two.reach (srcOf2 trn2) \<Longrightarrow>
       isCom1 trn1 \<Longrightarrow> isCom2 trn2 \<Longrightarrow> \<phi>1 trn1 \<Longrightarrow> \<phi>2 trn2 \<Longrightarrow>
       sync trn1 trn2 \<Longrightarrow> syncV (f1 trn1) (f2 trn2)"
and
  sync_syncO:
  "\<And> trn1 trn2.
       validTrans1 trn1 \<Longrightarrow> One.reach (srcOf1 trn1) \<Longrightarrow>
       validTrans2 trn2 \<Longrightarrow> Two.reach (srcOf2 trn2) \<Longrightarrow>
       isCom1 trn1 \<Longrightarrow> isCom2 trn2 \<Longrightarrow> \<gamma>1 trn1 \<Longrightarrow> \<gamma>2 trn2 \<Longrightarrow>
       sync trn1 trn2 \<Longrightarrow> syncO (g1 trn1) (g2 trn2)"
and
  sync_\<phi>1_\<phi>2:
  "\<And> trn1 trn2.
       validTrans1 trn1 \<Longrightarrow> One.reach (srcOf1 trn1) \<Longrightarrow>
       validTrans2 trn2 \<Longrightarrow> Two.reach (srcOf2 trn2) \<Longrightarrow>
       isCom1 trn1 \<Longrightarrow> isCom2 trn2 \<Longrightarrow>
       sync trn1 trn2 \<Longrightarrow> \<phi>1 trn1 \<longleftrightarrow> \<phi>2 trn2"
and
  sync_\<phi>_\<gamma>:
"\<And> trn1 trn2.
     validTrans1 trn1 \<Longrightarrow> One.reach (srcOf1 trn1) \<Longrightarrow>
     validTrans2 trn2 \<Longrightarrow> Two.reach (srcOf2 trn2) \<Longrightarrow>
     isCom1 trn1 \<Longrightarrow> isCom2 trn2 \<Longrightarrow>
     \<gamma>1 trn1 \<Longrightarrow> \<gamma>2 trn2 \<Longrightarrow>
     syncO (g1 trn1) (g2 trn2) \<Longrightarrow>
     (\<phi>1 trn1 \<Longrightarrow> \<phi>2 trn2 \<Longrightarrow> syncV (f1 trn1) (f2 trn2))
     \<Longrightarrow>
     sync trn1 trn2"
and  (* Every communication is observable (which does not mean that everything in
       a communication is observable!): *)
  isCom1_\<gamma>1: "\<And> trn1. validTrans1 trn1 \<Longrightarrow> One.reach (srcOf1 trn1) \<Longrightarrow> isCom1 trn1 \<Longrightarrow> \<gamma>1 trn1"
and
  isCom2_\<gamma>2: "\<And> trn2. validTrans2 trn2 \<Longrightarrow> Two.reach (srcOf2 trn2) \<Longrightarrow> isCom2 trn2 \<Longrightarrow> \<gamma>2 trn2"
and (* Lack of symmetry here: all the value-producing transitions of the second component
       need to be "communicating" (and hence proceed only synchronously) -- Technically, this tames shuffling...
       This restriction means that the only component that produces secrets is the first component -- the
       second component only receives secrets. *)
  isCom2_V2: "\<And> trn2. validTrans2 trn2 \<Longrightarrow> Two.reach (srcOf2 trn2) \<Longrightarrow> \<phi>2 trn2 \<Longrightarrow> isCom2 trn2"
and (* Added dummy assumption about the locale data not involved in any assumption: *)
  Dummy: "istate1 = istate1 \<and> srcOf1 = srcOf1 \<and> tgtOf1 = tgtOf1 \<and> T1 = T1 \<and> B1 = B1 \<and>
          istate2 = istate2 \<and> srcOf2 = srcOf2 \<and> tgtOf2 = tgtOf2 \<and> T2 = T2 \<and> B2 = B2"
begin

lemma sync_\<gamma>1_\<gamma>2:
 "\<And> trn1 trn2.
      validTrans1 trn1 \<Longrightarrow> One.reach (srcOf1 trn1) \<Longrightarrow>
      validTrans2 trn2 \<Longrightarrow> Two.reach (srcOf2 trn2) \<Longrightarrow>
      isCom1 trn1 \<Longrightarrow> isCom2 trn2 \<Longrightarrow>
      sync trn1 trn2 \<Longrightarrow> \<gamma>1 trn1 \<longleftrightarrow> \<gamma>2 trn2"
using isCom1_\<gamma>1 isCom2_\<gamma>2
by auto


definition icstate where "icstate = (istate1,istate2)"

fun validTrans :: "('state1, 'trans1, 'state2, 'trans2) ctrans \<Rightarrow> bool" where
 "validTrans(Trans1 s2 trn1) = (validTrans1 trn1 \<and> \<not> isCom1 trn1)"
|"validTrans (Trans2 s1 trn2) = (validTrans2 trn2 \<and> \<not> isCom2 trn2)"
|"validTrans (CTrans trn1 trn2) =
   (validTrans1 trn1 \<and> validTrans2 trn2 \<and> isCom1 trn1 \<and> isCom2 trn2 \<and> sync trn1 trn2)"

fun srcOf :: "('state1, 'trans1, 'state2, 'trans2) ctrans \<Rightarrow> 'state1 \<times> 'state2" where
 "srcOf (Trans1 s2 trn1) = (srcOf1 trn1, s2)"
|"srcOf (Trans2 s1 trn2) = (s1, srcOf2 trn2)"
|"srcOf (CTrans trn1 trn2) = (srcOf1 trn1, srcOf2 trn2)"

fun tgtOf :: "('state1, 'trans1, 'state2, 'trans2) ctrans \<Rightarrow> 'state1 \<times> 'state2" where
 "tgtOf (Trans1 s2 trn1) = (tgtOf1 trn1, s2)"
|"tgtOf (Trans2 s1 trn2) = (s1, tgtOf2 trn2)"
|"tgtOf (CTrans trn1 trn2) = (tgtOf1 trn1, tgtOf2 trn2)"

fun \<phi> :: "('state1, 'trans1, 'state2, 'trans2) ctrans \<Rightarrow> bool" where
 "\<phi> (Trans1 s2 trn1) = \<phi>1 trn1"
|"\<phi> (Trans2 s1 trn2) = \<phi>2 trn2"
|"\<phi> (CTrans trn1 trn2) = (\<phi>1 trn1 \<or> \<phi>2 trn2)"

fun f :: "('state1, 'trans1, 'state2, 'trans2) ctrans \<Rightarrow> ('value1,'value2) cvalue" where
 "f (Trans1 s2 trn1) = Value1 (f1 trn1)"
|"f (Trans2 s1 trn2) = Value2 (f2 trn2)"
|"f (CTrans trn1 trn2) = CValue (f1 trn1) (f2 trn2)"

fun \<gamma> :: "('state1, 'trans1, 'state2, 'trans2) ctrans \<Rightarrow> bool" where
 "\<gamma> (Trans1 s2 trn1) = \<gamma>1 trn1"
|"\<gamma> (Trans2 s1 trn2) = \<gamma>2 trn2"
|"\<gamma> (CTrans trn1 trn2) = (\<gamma>1 trn1 \<or> \<gamma>2 trn2)"

fun g :: "('state1, 'trans1, 'state2, 'trans2) ctrans \<Rightarrow> ('obs1,'obs2) cobs" where
 "g (Trans1 s2 trn1) = Obs1 (g1 trn1)"
|"g (Trans2 s1 trn2) = Obs2 (g2 trn2)"
|"g (CTrans trn1 trn2) = CObs (g1 trn1) (g2 trn2)"

fun T :: "('state1, 'trans1, 'state2, 'trans2) ctrans \<Rightarrow> bool"
where
"T (Trans1 s2 trn1) = T1 trn1"
|
"T (Trans2 s1 trn2) = T2 trn2"
|
"T (CTrans trn1 trn2) = (T1 trn1 \<or> T2 trn2)"

inductive compV :: "'value1 list \<Rightarrow> 'value2 list \<Rightarrow> ('value1, 'value2) cvalue list \<Rightarrow> bool"
where
 Nil[intro!,simp]: "compV [] [] []"
|Step1[intro]:
"compV vl1 vl2 vl \<Longrightarrow> \<not> isComV1 v1
 \<Longrightarrow> compV (v1 # vl1) vl2 (Value1 v1 # vl)"
|Step2[intro]:
"compV vl1 vl2 vl \<Longrightarrow> \<not> isComV2 v2
 \<Longrightarrow> compV vl1 (v2 # vl2) (Value2 v2 # vl)"
|Com[intro]:
"compV vl1 vl2 vl \<Longrightarrow> isComV1 v1 \<Longrightarrow> isComV2 v2 \<Longrightarrow> syncV v1 v2
 \<Longrightarrow> compV (v1 # vl1) (v2 # vl2) (CValue v1 v2 # vl)"

lemma compV_cases_V[consumes 3, case_names Nil Step1 Com]:
assumes v: "Two.validFrom s2 tr2"
and c: "compV vl1 (Two.V tr2) vl"
and rs2: "Two.reach s2"
and Nil: "vl1 = [] \<Longrightarrow> Two.V tr2 = [] \<Longrightarrow> vl = [] \<Longrightarrow> P"
and Step1:
"\<And>vll1 vll2 vll v1.
    vl1 = v1 # vll1 \<Longrightarrow>
    Two.V tr2 = vll2 \<Longrightarrow>
    vl = Value1 v1 # vll \<Longrightarrow>
    compV vll1 vll2 vll \<Longrightarrow> \<not> isComV1 v1 \<Longrightarrow> P"
and Com:
"\<And>vll1 vll2 vll v1 v2.
    vl1 = v1 # vll1 \<Longrightarrow>
    Two.V tr2 = v2 # vll2 \<Longrightarrow>
    vl = CValue v1 v2 # vll \<Longrightarrow>
    compV vll1 vll2 vll \<Longrightarrow>
    isComV1 v1 \<Longrightarrow> isComV2 v2 \<Longrightarrow> syncV v1 v2 \<Longrightarrow> P"
shows P
using c proof cases
  case (Step2 vll2 vll1 v2)
  obtain tr2a trn2 tr2b where tr2: "tr2 = tr2a @ trn2 # tr2b" and
  \<phi>2: "\<phi>2 trn2" and f2: "f2 trn2 = v2"
  using \<open>Two.V tr2 = v2 # vll2\<close> by (metis Two.V_eq_Cons append_Cons)
  have v2: "validTrans2 trn2" using tr2 v
  by (metis Nil_is_append_conv Two.validFrom_def Two.valid_ConsE
          Two.valid_append list.distinct(2) self_append_conv2)
  have rs2': "Two.reach (srcOf2 trn2)" using v rs2 unfolding tr2
    by (induction tr2a arbitrary: s2) (auto intro: Two.reach.Step)
  then have False using isCom2_V2[OF v2 rs2' \<phi>2] \<open>\<not> isComV2 v2\<close>
  using \<phi>2 f2 isCom2_isComV2 v2 by blast
  thus ?thesis by simp
qed (insert assms, auto)


inductive compO :: "'obs1 list \<Rightarrow> 'obs2 list \<Rightarrow> ('obs1, 'obs2) cobs list \<Rightarrow> bool"
where
 Nil[intro!,simp]: "compO [] [] []"
|Step1[intro]:
"compO ol1 ol2 ol \<Longrightarrow> \<not> isComO1 o1
 \<Longrightarrow> compO (o1 # ol1) ol2 (Obs1 o1 # ol)"
|Step2[intro]:
"compO ol1 ol2 ol \<Longrightarrow> \<not> isComO2 o2
 \<Longrightarrow> compO ol1 (o2 # ol2) (Obs2 o2 # ol)"
|Com[intro]:
"compO ol1 ol2 ol \<Longrightarrow> isComO1 o1 \<Longrightarrow> isComO2 o2 \<Longrightarrow> syncO o1 o2
 \<Longrightarrow> compO (o1 # ol1) (o2 # ol2) (CObs o1 o2 # ol)"

definition B :: "('value1,'value2) cvalue list \<Rightarrow> ('value1,'value2) cvalue list \<Rightarrow> bool" where
"B vl vl' \<equiv> \<forall> vl1 vl2. compV vl1 vl2 vl \<longrightarrow>
  (\<exists> vl1' vl2'. compV vl1' vl2' vl' \<and> B1 vl1 vl1' \<and> B2 vl2 vl2')"

inductive ccomp ::
"'state1 \<Rightarrow> 'state2 \<Rightarrow> 'trans1 trace \<Rightarrow> 'trans2 trace \<Rightarrow>
 ('state1, 'trans1, 'state2, 'trans2) ctrans trace \<Rightarrow> bool"
where
Nil[simp,intro!]: "ccomp s1 s2 [] [] []"
|
Step1[intro]:
"ccomp (tgtOf1 trn1) s2 tr1 tr2 tr \<Longrightarrow> \<not> isCom1 trn1 \<Longrightarrow>
 ccomp (srcOf1 trn1) s2 (trn1 # tr1) tr2 (Trans1 s2 trn1 # tr)"
|
Step2[intro]:
"ccomp s1 (tgtOf2 trn2) tr1 tr2 tr \<Longrightarrow> \<not> isCom2 trn2 \<Longrightarrow>
 ccomp s1 (srcOf2 trn2) tr1 (trn2 # tr2) (Trans2 s1 trn2 # tr)"
|
Com[intro]:
"ccomp (tgtOf1 trn1) (tgtOf2 trn2) tr1 tr2 tr \<Longrightarrow>
 isCom1 trn1 \<Longrightarrow> isCom2 trn2 \<Longrightarrow> sync trn1 trn2 \<Longrightarrow>
 ccomp (srcOf1 trn1) s2 (trn1 # tr1) (trn2 # tr2) (CTrans trn1 trn2 # tr)"


definition comp where "comp \<equiv> ccomp istate1 istate2"

end (* context BD_Security_TS_Comp *)

sublocale BD_Security_TS_Comp \<subseteq> BD_Security_TS icstate validTrans srcOf tgtOf \<phi> f \<gamma> g T B .

context BD_Security_TS_Comp
begin

lemma valid:
assumes "valid tr" and "srcOf (hd tr) = (s1,s2)"
shows
"\<exists>tr1 tr2.
   One.validFrom s1 tr1 \<and> Two.validFrom s2 tr2 \<and>
   ccomp s1 s2 tr1 tr2 tr"
using assms proof(induction arbitrary: s1 s2)
  case (Singl trn)
  show ?case proof(cases trn)
    case (Trans1 s22 trn1)
    show ?thesis using Singl unfolding Trans1
    by (intro exI[of _ "[trn1]"] exI[of _ "[]"]) auto
  next
    case (Trans2 s11 trn2)
    show ?thesis using Singl unfolding Trans2
    by (intro exI[of _ "[]::'trans1 trace"] exI[of _ "[trn2]"]) auto
  next
    case (CTrans trn1 trn2)
    show ?thesis using Singl unfolding CTrans
    by (intro exI[of _ "[trn1]"] exI[of _ "[trn2]"]) auto
  qed
next
  case (Cons trn tr)
  show ?case proof(cases trn)
    case (Trans1 s22 trn1)
    let ?s1 = "tgtOf1 trn1"
    have s22[simp]: "s22 = s2" using \<open>srcOf (hd (trn # tr)) = (s1, s2)\<close>
    unfolding Trans1 by simp
    hence "tgtOf trn = (?s1, s2)" unfolding Trans1 by simp
    hence "srcOf (hd tr) = (?s1, s2)" using Cons.hyps(2) by auto
    from Cons.IH[OF this] obtain tr1 tr2 where
    1: "One.validFrom ?s1 tr1 \<and> Two.validFrom s2 tr2 \<and>
        ccomp ?s1 s2 tr1 tr2 tr" by auto
    show ?thesis using Cons.prems Cons.hyps 1 unfolding Trans1
    by (intro exI[of _ "trn1 # tr1"] exI[of _ "tr2"], cases tr2) auto
  next
    case (Trans2 s11 trn2)
    let ?s2 = "tgtOf2 trn2"
    have s11[simp]: "s11 = s1" using \<open>srcOf (hd (trn # tr)) = (s1, s2)\<close>
    unfolding Trans2 by simp
    hence "tgtOf trn = (s1, ?s2)" unfolding Trans2 by simp
    hence "srcOf (hd tr) = (s1, ?s2)" using Cons.hyps(2) by auto
    from Cons.IH[OF this] obtain tr1 tr2 where
    1: "One.validFrom s1 tr1 \<and> Two.validFrom ?s2 tr2 \<and>
        ccomp s1 ?s2 tr1 tr2 tr" by auto
    show ?thesis using Cons.prems Cons.hyps 1 unfolding Trans2
    by (intro exI[of _ "tr1"] exI[of _ "trn2 # tr2"], cases tr1) auto
  next
    case (CTrans trn1 trn2)
    let ?s1 = "tgtOf1 trn1" let ?s2 = "tgtOf2 trn2"
    have "tgtOf trn = (?s1, ?s2)" unfolding CTrans by simp
    hence "srcOf (hd tr) = (?s1, ?s2)" using Cons.hyps(2) by auto
    from Cons.IH[OF this] obtain tr1 tr2 where
    1: "One.validFrom ?s1 tr1 \<and> Two.validFrom ?s2 tr2 \<and>
        ccomp ?s1 ?s2 tr1 tr2 tr" by auto
    show ?thesis using Cons.prems Cons.hyps 1 unfolding CTrans
    by (intro exI[of _ "trn1 # tr1"] exI[of _ "trn2 # tr2"], cases tr2) auto
  qed
qed

lemma validFrom:
assumes "validFrom icstate tr"
shows "\<exists>tr1 tr2. One.validFrom istate1 tr1 \<and> Two.validFrom istate2 tr2 \<and> comp tr1 tr2 tr"
using assms valid unfolding comp_def icstate_def validFrom_def by(cases tr) fastforce+

lemma reach_reach12:
assumes "reach s"
obtains "One.reach (fst s)" and "Two.reach (snd s)"
using assms proof (induction rule: reach.induct)
  case Istate
    then show thesis using One.reach.Istate Two.reach.Istate unfolding icstate_def by auto
next
  case (Step s trn s')
    then show thesis
      using One.reach.Step[of "fst s" _ "fst s'"] Two.reach.Step[of "snd s" _ "snd s'"]
      by (auto elim: validTrans.elims)
qed

lemma compV_ccomp:
assumes v: "One.validFrom s1 tr1" "Two.validFrom s2 tr2"
and c: "ccomp s1 s2 tr1 tr2 tr"
and rs1: "One.reach s1" and rs2: "Two.reach s2"
shows "compV (One.V tr1) (Two.V tr2) (V tr)"
using c v rs1 rs2 proof(induction)
  case (Step1 trn1 s2 tr1 tr2 tr)
  moreover then have "One.reach (tgtOf1 trn1)"
    using One.reach.Step[of "srcOf1 trn1" trn1 "tgtOf1 trn1"] by auto
  ultimately show ?case by (cases "\<phi>1 trn1") (auto simp: isCom1_isComV1)
next
  case (Step2 s1 trn2 tr1 tr2 tr)
  moreover then have "Two.reach (tgtOf2 trn2)"
    using Two.reach.Step[of "srcOf2 trn2" trn2 "tgtOf2 trn2"] by auto
  ultimately show ?case by (cases "\<phi>2 trn2") (auto simp: isCom2_isComV2)
next
  case (Com trn1 trn2 tr1 tr2 tr s2)
  moreover then have "One.reach (tgtOf1 trn1)" "Two.reach (tgtOf2 trn2)"
    using One.reach.Step[of "srcOf1 trn1" trn1 "tgtOf1 trn1"]
          Two.reach.Step[of "srcOf2 trn2" trn2 "tgtOf2 trn2"]
    by auto
  ultimately show ?case
    by (cases "\<phi>1 trn1"; cases "\<phi>2 trn2"; simp add: isCom1_isComV1 isCom2_isComV2)
       (use sync_\<phi>1_\<phi>2 sync_syncV Com in auto)
qed auto

lemma compV:
assumes "One.validFrom istate1 tr1" and "Two.validFrom istate2 tr2"
and "comp tr1 tr2 tr"
shows "compV (One.V tr1) (Two.V tr2) (V tr)"
using compV_ccomp assms One.reach.Istate Two.reach.Istate unfolding comp_def by auto

lemma compO_ccomp:
assumes v: "One.validFrom s1 tr1" "Two.validFrom s2 tr2"
and c: "ccomp s1 s2 tr1 tr2 tr"
and rs1: "One.reach s1" and rs2: "Two.reach s2"
shows "compO (One.O tr1) (Two.O tr2) (O tr)"
using c v rs1 rs2 proof(induction)
  case (Step1 trn1 s2 tr1 tr2 tr)
  moreover then have "One.reach (tgtOf1 trn1)"
    using One.reach.Step[of "srcOf1 trn1" trn1 "tgtOf1 trn1"] by auto
  ultimately show ?case by (cases "\<gamma>1 trn1") (auto simp: isCom1_isComO1)
next
  case (Step2 s1 trn2 tr1 tr2 tr)
  moreover then have "Two.reach (tgtOf2 trn2)"
    using Two.reach.Step[of "srcOf2 trn2" trn2 "tgtOf2 trn2"] by auto
  ultimately show ?case by (cases "\<gamma>2 trn2") (auto simp: isCom2_isComO2)
next
  case (Com trn1 trn2 tr1 tr2 tr s2)
  moreover then have "One.reach (tgtOf1 trn1)" "Two.reach (tgtOf2 trn2)"
    using One.reach.Step[of "srcOf1 trn1" trn1 "tgtOf1 trn1"]
          Two.reach.Step[of "srcOf2 trn2" trn2 "tgtOf2 trn2"]
    by auto
  ultimately show ?case
    by (cases "\<gamma>1 trn1"; cases "\<gamma>2 trn2"; simp add: isCom1_isComO1 isCom2_isComO2)
       (use sync_\<gamma>1_\<gamma>2 sync_syncO Com in auto)
qed auto

lemma compO:
assumes "One.validFrom istate1 tr1" and "Two.validFrom istate2 tr2"
and "comp tr1 tr2 tr"
shows "compO (One.O tr1) (Two.O tr2) (O tr)"
using compO_ccomp assms One.reach.Istate Two.reach.Istate unfolding comp_def by auto

lemma T_ccomp:
assumes v: "One.validFrom s1 tr1" "Two.validFrom s2 tr2"
and c: "ccomp s1 s2 tr1 tr2 tr" and n: "never T tr"
shows "never T1 tr1 \<and> never T2 tr2"
using c n v by (induction) auto

lemma T:
assumes "One.validFrom istate1 tr1" and "Two.validFrom istate2 tr2"
and "comp tr1 tr2 tr" and "never T tr"
shows "never T1 tr1 \<and> never T2 tr2"
using T_ccomp assms unfolding comp_def by auto

lemma B:
assumes "compV vl1 vl2 vl" and "B vl vl'"
shows "\<exists>vl1' vl2'. compV vl1' vl2' vl' \<and> B1 vl1 vl1' \<and> B2 vl2 vl2'"
using assms unfolding B_def by auto

lemma pullback_O_V_aux:
assumes "One.validFrom s1 tr1" "Two.validFrom s2 tr2"
and "One.reach s1" "Two.reach s2"
and "compV (One.V tr1) (Two.V tr2) vl"
and "compO (One.O tr1) (Two.O tr2) obl"
shows "\<exists>tr. validFrom (s1,s2) tr \<and> O tr = obl \<and> V tr = vl"
using assms proof(induction tr1 tr2 arbitrary: s1 s2 vl obl rule: list22_induct)
  case (NilNil s1 s2 vl obl)
  thus ?case by (intro exI[of _ "[]"]) (auto elim: compV.cases compO.cases)
next
  case (ConsNil trn1 tr1 s1 s2 vl obl)
  let ?s1 = "tgtOf1 trn1"
  have trn1: "validTrans1 trn1" and tr1: "One.validFrom ?s1 tr1"
  and s1: "srcOf1 trn1 = s1" "One.reach s1" and rs2: "Two.reach s2" using ConsNil.prems by auto
  then have rs1': "One.reach ?s1" by (intro One.reach.Step[of s1 trn1 ?s1]) auto
  show ?case proof(cases "isCom1 trn1")
    case True note com1 = True
    hence \<gamma>1: "\<gamma>1 trn1" using trn1 isCom1_\<gamma>1 s1 by auto
    hence "isComO1 (g1 trn1)" using \<gamma>1 com1 s1 isCom1_isComO1 trn1 by blast
    hence False using \<open>compO (One.O (trn1 # tr1)) (Two.O []) obl\<close>
    using \<gamma>1 by (auto elim: compO.cases)
    thus ?thesis by simp
  next
    case False note com1 = False
    show ?thesis proof(cases "\<phi>1 trn1")
      case True note \<phi>1 = True
      hence comv1: "\<not> isComV1 (f1 trn1)" using \<phi>1 com1 isCom1_isComV1 trn1 s1 by blast
      with \<open>compV (One.V (trn1 # tr1)) (Two.V []) vl\<close> \<phi>1
      obtain vll where vl: "vl = Value1 (f1 trn1) # vll"
      and vll: "compV (One.V tr1) (Two.V []) vll" by (auto elim: compV.cases)
      show ?thesis proof(cases "\<gamma>1 trn1")
        case True note \<gamma>1 = True
        hence "\<not> isComO1 (g1 trn1)" using \<gamma>1 com1 isCom1_isComO1 trn1 s1 by blast
        with \<open>compO (One.O (trn1 # tr1)) (Two.O []) obl\<close> \<gamma>1
        obtain obll where obl: "obl = Obs1 (g1 trn1) # obll"
        and obll: "compO (One.O tr1) (Two.O []) obll" by (auto elim: compO.cases)
        from ConsNil.IH[OF tr1 _ rs1' rs2 vll obll] obtain trr where
        "validFrom (?s1, s2) trr" and "O trr = obll \<and> V trr = vll" by auto
        thus ?thesis
        unfolding obl vl using trn1 com1 s1 \<phi>1 \<gamma>1
        by (intro exI[of _ "Trans1 s2 trn1 # trr"]) auto
      next
        case False note \<gamma>1 = False
        note obl = \<open>compO (One.O (trn1 # tr1)) (Two.O []) obl\<close>
        from ConsNil.IH[OF tr1 _ rs1' rs2 vll] obl \<gamma>1 obtain trr where
        "validFrom (?s1, s2) trr" and "O trr = obl \<and> V trr = vll" by auto
        thus ?thesis
        unfolding obl vl using trn1 com1 s1 \<phi>1 \<gamma>1
        by (intro exI[of _ "Trans1 s2 trn1 # trr"]) auto
      qed
    next
      case False note \<phi>1 = False
      note vl = \<open>compV (One.V (trn1 # tr1)) (Two.V []) vl\<close>
      show ?thesis proof(cases "\<gamma>1 trn1")
        case True note \<gamma>1 = True
        hence "\<not> isComO1 (g1 trn1)" using \<gamma>1 com1 isCom1_isComO1 trn1 s1 by blast
        with \<open>compO (One.O (trn1 # tr1)) (Two.O []) obl\<close> \<gamma>1
        obtain obll where obl: "obl = Obs1 (g1 trn1) # obll"
        and obll: "compO (One.O tr1) (Two.O []) obll" by (auto elim: compO.cases)
        from ConsNil.IH[OF tr1 _ rs1' rs2 _ obll] vl \<phi>1 obtain trr where
        "validFrom (?s1, s2) trr" and "O trr = obll \<and> V trr = vl" by auto
        thus ?thesis
        unfolding obl vl using trn1 com1 s1 \<phi>1 \<gamma>1
        by (intro exI[of _ "Trans1 s2 trn1 # trr"]) auto
      next
        case False note \<gamma>1 = False
        note obl = \<open>compO (One.O (trn1 # tr1)) (Two.O []) obl\<close>
        from ConsNil.IH[OF tr1 _ rs1' rs2 _] vl \<phi>1 obl \<gamma>1 obtain trr where
        "validFrom (?s1, s2) trr" and "O trr = obl \<and> V trr = vl" by fastforce
        thus ?thesis
        unfolding obl vl using trn1 com1 s1 \<phi>1 \<gamma>1
        by (intro exI[of _ "Trans1 s2 trn1 # trr"]) auto
      qed
    qed
  qed
next
  case (NilCons trn2 tr2 s1 s2 vl obl)
  let ?s2 = "tgtOf2 trn2"
  have trn2: "validTrans2 trn2" and tr2: "Two.validFrom ?s2 tr2"
  and s2: "srcOf2 trn2 = s2" "Two.reach s2" and rs1: "One.reach s1" using NilCons.prems by auto
  then have rs2': "Two.reach ?s2" by (intro Two.reach.Step[of s2 trn2 ?s2]) auto
  show ?case proof(cases "isCom2 trn2")
    case True note com2 = True
    hence \<gamma>2: "\<gamma>2 trn2" using trn2 isCom2_\<gamma>2 s2 by auto
    hence "isComO2 (g2 trn2)" using \<gamma>2 com2 isCom2_isComO2 trn2 s2 by blast
    hence False using \<open>compO (One.O []) (Two.O (trn2 # tr2)) obl\<close>
    using \<gamma>2 by (auto elim: compO.cases)
    thus ?thesis by simp
  next
    case False note com2 = False
    show ?thesis proof(cases "\<phi>2 trn2")
      case True note \<phi>2 = True
      hence comv1: "\<not> isComV2 (f2 trn2)" using \<phi>2 com2 isCom2_isComV2 trn2 s2 by blast
      with \<open>compV (One.V []) (Two.V (trn2 # tr2)) vl\<close> \<phi>2
      obtain vll where vl: "vl = Value2 (f2 trn2) # vll"
      and vll: "compV (One.V []) (Two.V tr2) vll" by (auto elim: compV.cases)
      show ?thesis proof(cases "\<gamma>2 trn2")
        case True note \<gamma>2 = True
        hence "\<not> isComO2 (g2 trn2)" using \<gamma>2 com2 isCom2_isComO2 trn2 s2 by blast
        with \<open>compO (One.O []) (Two.O (trn2 # tr2)) obl\<close> \<gamma>2
        obtain obll where obl: "obl = Obs2 (g2 trn2) # obll"
        and obll: "compO (One.O []) (Two.O tr2) obll" by (auto elim: compO.cases)
        from NilCons.IH[OF _ tr2 rs1 rs2' vll obll] obtain trr where
        "validFrom (s1, ?s2) trr" and "O trr = obll \<and> V trr = vll" by auto
        thus ?thesis
        unfolding obl vl using trn2 com2 s2 \<phi>2 \<gamma>2
        by (intro exI[of _ "Trans2 s1 trn2 # trr"]) auto
      next
        case False note \<gamma>2 = False
        note obl = \<open>compO (One.O []) (Two.O (trn2 # tr2)) obl\<close>
        from NilCons.IH[OF _ tr2 rs1 rs2' vll] obl \<gamma>2 obtain trr where
        "validFrom (s1, ?s2) trr" and "O trr = obl \<and> V trr = vll" by auto
        thus ?thesis
        unfolding obl vl using trn2 com2 s2 \<phi>2 \<gamma>2
        by (intro exI[of _ "Trans2 s1 trn2 # trr"]) auto
      qed
    next
      case False note \<phi>2 = False
      note vl = \<open>compV (One.V []) (Two.V (trn2 # tr2)) vl\<close>
      show ?thesis proof(cases "\<gamma>2 trn2")
        case True note \<gamma>2 = True
        hence "\<not> isComO2 (g2 trn2)" using \<gamma>2 com2 isCom2_isComO2 trn2 s2 by blast
        with \<open>compO (One.O []) (Two.O (trn2 # tr2)) obl\<close> \<gamma>2
        obtain obll where obl: "obl = Obs2 (g2 trn2) # obll"
        and obll: "compO (One.O []) (Two.O tr2) obll" by (auto elim: compO.cases)
        from NilCons.IH[OF _ tr2 rs1 rs2' _ obll] vl \<phi>2 obtain trr where
        "validFrom (s1, ?s2) trr" and "O trr = obll \<and> V trr = vl" by auto
        thus ?thesis
        unfolding obl vl using trn2 com2 s2 \<phi>2 \<gamma>2
        by (intro exI[of _ "Trans2 s1 trn2 # trr"]) auto
      next
        case False note \<gamma>2 = False
        note obl = \<open>compO (One.O []) (Two.O (trn2 # tr2)) obl\<close>
        from NilCons.IH[OF _ tr2 rs1 rs2' _] vl \<phi>2 obl \<gamma>2 obtain trr where
        "validFrom (s1, ?s2) trr" and "O trr = obl \<and> V trr = vl" by fastforce
        thus ?thesis
        unfolding obl vl using trn2 com2 s2 \<phi>2 \<gamma>2
        by (intro exI[of _ "Trans2 s1 trn2 # trr"]) auto
      qed
    qed
  qed
next
  case (ConsCons trn1 tr1 trn2 tr2 s1 s2 vl obl)
  let ?s1 = "tgtOf1 trn1"  let ?s2 = "tgtOf2 trn2"
  let ?tr1 = "trn1 # tr1" let ?tr2 = "trn2 # tr2"
  have trn1: "validTrans1 trn1" and tr1: "One.validFrom ?s1 tr1" and s1: "srcOf1 trn1 = s1" "One.reach s1"
  and trn2: "validTrans2 trn2" and tr2: "Two.validFrom ?s2 tr2" and s2: "srcOf2 trn2 = s2" "Two.reach s2"
  using ConsCons.prems by auto
  then have rs1': "One.reach ?s1" and rs2': "Two.reach ?s2"
    using One.reach.Step[of s1 trn1 ?s1] Two.reach.Step[of s2 trn2 ?s2] by auto
  note vl = \<open>compV (One.V ?tr1) (Two.V ?tr2) vl\<close>
  note obl = \<open>compO (One.O ?tr1) (Two.O ?tr2) obl\<close>
  note trr1 = \<open>One.validFrom s1 ?tr1\<close> note trr2 = \<open>Two.validFrom s2 ?tr2\<close>
  show ?case proof(cases "\<phi>1 trn1 \<or> \<gamma>1 trn1")
    case False note \<phi>\<gamma>1 = False
    hence com1: "\<not> isCom1 trn1" using isCom1_\<gamma>1 trn1 s1 by blast
    from ConsCons.IH(2)[of ?tr2, OF _ tr1 trr2 rs1' s2(2)] vl obl \<phi>\<gamma>1
    obtain trr where "validFrom (?s1, s2) trr" and "O trr = obl \<and> V trr = vl"
    by fastforce
    thus ?thesis
    unfolding obl vl using trn1 com1 s1 \<phi>\<gamma>1
    by (intro exI[of _ "Trans1 s2 trn1 # trr"]) auto
  next
    case True note \<phi>\<gamma>1 = True
    show ?thesis proof(cases "\<phi>2 trn2 \<or> \<gamma>2 trn2")
      case False note \<phi>\<gamma>2 = False
      hence com2: "\<not> isCom2 trn2" using isCom2_\<gamma>2 trn2 s2 by blast
      from ConsCons.IH(3)[of ?tr1, OF _ trr1 tr2 s1(2) rs2'] vl obl \<phi>\<gamma>2
      obtain trr where "validFrom (s1, ?s2) trr" and "O trr = obl \<and> V trr = vl"
      by fastforce
      thus ?thesis
      unfolding obl vl using trn2 com2 s2 \<phi>\<gamma>2
      by (intro exI[of _ "Trans2 s1 trn2 # trr"]) auto
    next
      case True note \<phi>\<gamma>2 = True
      show ?thesis using obl ConsCons proof cases
        case Nil hence \<gamma>12: "\<not> \<gamma>1 trn1 \<and> \<not> \<gamma>2 trn2" by auto
        hence obl: "compO (One.O tr1) (Two.O ?tr2) obl"
                   "compO (One.O tr1) (Two.O tr2) obl"
        using obl by auto
        have \<phi>12: "\<phi>1 trn1 \<and> \<phi>2 trn2" using \<phi>\<gamma>1 \<phi>\<gamma>2 \<gamma>12 by auto
        show ?thesis using trr2 vl s2(2) proof(cases rule: compV_cases_V)
          case Nil hence False using \<phi>12 by auto
          thus ?thesis by simp
        next
          case (Step1 vll1 vll2 vll v1)
          hence f1: "f1 trn1 = v1" and vll1: "One.V tr1 = vll1" using \<phi>12 by auto
          hence vll: "compV (One.V tr1) (Two.V ?tr2) vll" using Step1 by auto
          from ConsCons.IH(2)[OF _ tr1 trr2 rs1' s2(2) vll obl(1)]
          obtain trr where "validFrom (?s1, s2) trr" and "O trr = obl \<and> V trr = vll"
          by auto
          thus ?thesis using trn1 Step1 f1 \<phi>12 \<gamma>12 isCom2_V2 isCom2_\<gamma>2 trn2 s2
          by (intro exI[of _ "Trans1 s2 trn1 # trr"]) auto
        next
          case (Com vll1 vll2 vll v1 v2)
          hence f1: "f1 trn1 = v1" and vll1: "One.V tr1 = vll1"
          and f2: "f2 trn2 = v2" and vll2: "Two.V tr2 = vll2"
          using \<phi>12 by auto
          hence vll: "compV (One.V tr1) (Two.V tr2) vll" using Com by auto
          from ConsCons.IH(1)[OF tr1 tr2 rs1' rs2' vll obl(2)]
          obtain trr where "validFrom (?s1, ?s2) trr" and "O trr = obl \<and> V trr = vll"
          by auto
          thus ?thesis using trn1 Step1 f1 \<phi>12 \<gamma>12 isCom2_V2 isCom2_\<gamma>2 trn2 s2
          by (intro exI[of _ "Trans1 s2 trn1 # trr"]) auto
        qed
      next
        case (Step1 obll1 obll ob1) note Step1O = Step1
        show ?thesis proof(cases "\<gamma>1 trn1")
          case True note \<gamma>1 = True
          hence g1: "g1 trn1 = ob1" and "obll1 = One.O tr1" using Step1 by auto
          hence obll: "compO (One.O tr1) (Two.O ?tr2) obll" using Step1 by auto
          have com1: "\<not> isCom1 trn1" using Step1O \<gamma>1 g1 isCom1_isComO1 trn1 s1 by blast
          show ?thesis using trr2 vl s2(2) proof(cases rule: compV_cases_V)
            case Nil
            hence \<phi>12: "\<not> \<phi>1 trn1 \<and> \<not> \<phi>2 trn2" by auto
            hence vl: "compV (One.V tr1) (Two.V ?tr2) vl" using vl by auto
            from ConsCons.IH(2)[OF _ tr1 trr2 rs1' s2(2) vl obll]
            obtain trr where "validFrom (?s1, s2) trr" and "O trr = obll \<and> V trr = vl"
            by auto
            thus ?thesis using trn1 Step1O g1 \<phi>12 \<gamma>1 trn1 s1 isCom1_isComO1
            by (intro exI[of _ "Trans1 s2 trn1 # trr"]) auto
          next
            case (Step1 vll1 vll2 vll v1) note Step1V = Step1
            show ?thesis proof(cases "\<phi>1 trn1")
              case False note \<phi>1 = False
              hence vl: "compV (One.V tr1) (Two.V ?tr2) vl" using vl by auto
              from ConsCons.IH(2)[OF _ tr1 trr2 rs1' s2(2) vl obll]
              obtain trr where "validFrom (?s1, s2) trr" and "O trr = obll \<and> V trr = vl"
              by auto
              thus ?thesis using trn1 Step1O g1 \<phi>1 \<gamma>1 trn1 s1 isCom1_isComO1
              by (intro exI[of _ "Trans1 s2 trn1 # trr"]) auto
            next
              case True note \<phi>1 = True
              hence f1: "f1 trn1 = v1" and "vll1 = One.V tr1" using Step1V by auto
              hence vll: "compV (One.V tr1) (Two.V ?tr2) vll" using Step1V com1 by auto
              from ConsCons.IH(2)[OF _ tr1 trr2 rs1' s2(2) vll obll]
              obtain trr where "validFrom (?s1, s2) trr" and "O trr = obll \<and> V trr = vll"
              by auto
              thus ?thesis using trn1 Step1O Step1V f1 \<phi>1 g1 \<phi>1 \<gamma>1 trn1 s1 isCom1_isComO1
              by (intro exI[of _ "Trans1 s2 trn1 # trr"]) auto
            qed
          next
            case (Com vll1 vll2 vll v1 v2)
            hence \<phi>1: "\<not> \<phi>1 trn1" using com1 isCom1_isComV1[OF trn1] s1 by auto
            hence vl: "compV (One.V tr1) (Two.V ?tr2) vl" using vl by auto
            from ConsCons.IH(2)[OF _ tr1 trr2 rs1' s2(2) vl obll]
            obtain trr where "validFrom (?s1, s2) trr" and "O trr = obll \<and> V trr = vl"
            by auto
            thus ?thesis using trn1 Step1O g1 \<phi>1 \<gamma>1 trn1 s1 isCom1_isComO1
            by (intro exI[of _ "Trans1 s2 trn1 # trr"]) auto
          qed
        next
          case False note \<gamma>1 = False
          hence obl: "compO (One.O tr1) (Two.O ?tr2) obl" using obl by simp
          hence \<phi>1: "\<phi>1 trn1" and com1: "\<not> isCom1 trn1" using \<phi>\<gamma>1 \<gamma>1 isCom1_\<gamma>1 trn1 s1 by auto
          show ?thesis using trr2 vl s2(2) proof(cases rule: compV_cases_V)
            case Nil hence False using \<phi>1 by auto
            thus ?thesis by simp
          next
            case Com hence False using \<phi>1 com1 trn1 using isCom1_isComV1 s1 by auto
            thus ?thesis by simp
          next
            case (Step1 vll1 vll2 vll v1) note Step1V = Step1
            hence f1: "f1 trn1 = v1" and "vll1 = One.V tr1" using \<phi>1 by auto
            hence vll: "compV (One.V tr1) (Two.V ?tr2) vll" using Step1V com1 by auto
            from ConsCons.IH(2)[OF _ tr1 trr2 rs1' s2(2) vll obl]
            obtain trr where "validFrom (?s1, s2) trr" and "O trr = obl \<and> V trr = vll"
            by auto
            thus ?thesis using trn1 Step1O Step1V f1 \<phi>1 \<phi>1 \<gamma>1 trn1 s1 isCom1_isComV1
            by(intro exI[of _ "Trans1 s2 trn1 # trr"]) auto
          qed
        qed
      next
        case (Step2 obl2 obll ob2) note Step2O = Step2
        hence com2: "\<not> isCom2 trn2" using isCom2_\<gamma>2[OF trn2] isCom2_isComO2[OF trn2] s2 by auto
        hence \<phi>2: "\<not> \<phi>2 trn2" using isCom2_V2[OF trn2] s2 by auto
        hence vl: "compV (One.V ?tr1) (Two.V tr2) vl" using vl by simp
        have \<gamma>2: "\<gamma>2 trn2" using \<phi>\<gamma>2 \<phi>2 by simp
        hence g2: "g2 trn2 = ob2" and "obl2 = Two.O tr2" using Step2 by auto
        hence obll: "compO (One.O ?tr1) (Two.O tr2) obll" using Step2 by auto
        from ConsCons.IH(3)[OF _ trr1 tr2 s1(2) rs2' vl obll]
        obtain trr where "validFrom (s1, ?s2) trr" and "O trr = obll \<and> V trr = vl" by auto
        thus ?thesis using trn1 Step2O g2 \<phi>2 \<gamma>2 trn2 s2 isCom2_isComO2
        by (intro exI[of _ "Trans2 s1 trn2 # trr"]) auto
      next
        case (Com obll1 obll2 obll ob1 ob2) note ComO = Com
        show ?thesis
        proof(cases "\<gamma>1 trn1")
          case True note \<gamma>1 = True
          hence com1: "isCom1 trn1" using isCom1_isComO1[OF trn1] s1 ComO by auto
          show ?thesis proof(cases "\<gamma>2 trn2")
            case True note \<gamma>2 = True
            hence com2: "isCom2 trn2" using isCom2_isComO2[OF trn2] s2 ComO by auto
            have obll: "compO (One.O tr1) (Two.O tr2) obll" using obl ComO \<gamma>1 \<gamma>2 by auto
            have g1: "g1 trn1 = ob1" and "obll1 = One.O tr1" and
                 g2: "g2 trn2 = ob2" and "obll2 = Two.O tr2"
            using \<gamma>1 \<gamma>2 ComO by auto
            have rs1: "One.reach (srcOf1 trn1)" and rs2: "Two.reach (srcOf2 trn2)"
              using s1 s2 by auto
            have sync: "sync trn1 trn2" proof(rule sync_\<phi>_\<gamma>[OF trn1 rs1 trn2 rs2 com1 com2])
              show "syncO (g1 trn1) (g2 trn2)" using Com \<gamma>1 \<gamma>2 by auto
            next
              assume \<phi>12: "\<phi>1 trn1" "\<phi>2 trn2"
              hence comV: "isComV1 (f1 trn1) \<and> isComV2 (f2 trn2)"
              using com1 com2 isCom1_isComV1 isCom2_isComV2 trn1 trn2 rs1 rs2 by blast
              show "syncV (f1 trn1) (f2 trn2)" using vl \<phi>12 comV by cases auto
            qed(insert \<gamma>1 \<gamma>2, auto)
            show ?thesis
            proof(cases "\<phi>1 trn1")
              case True
              hence \<phi>12: "\<phi>1 trn1 \<and> \<phi>2 trn2" using sync_\<phi>1_\<phi>2[OF trn1 rs1 trn2 rs2 com1 com2 sync] by simp
              show ?thesis using trr2 vl s2(2) proof(cases rule: compV_cases_V)
                case Nil hence False using \<phi>12 by auto
                thus ?thesis by simp
              next
                case Step1 hence False using \<phi>12 com1 isCom1_isComV1[OF trn1] s1 by auto
                thus ?thesis by simp
              next
                case (Com vll1 vll2 vll v1 v2) note ComV = Com
                hence f1: "f1 trn1 = v1" and "vll1 = One.V tr1" and
                      f2: "f2 trn2 = v2" and "vll2 = Two.V tr2"
                using \<phi>12 by auto
                hence vll: "compV (One.V tr1) (Two.V tr2) vll" using ComV com1 com2 \<phi>12 by auto
                from ConsCons.IH(1)[OF tr1 tr2 rs1' rs2' vll obll]
                obtain trr where "validFrom (?s1, ?s2) trr" and "O trr = obll \<and> V trr = vll"
                by auto
                thus ?thesis using trn1 trn2 ComO ComV f1 f2 \<phi>12 g1 g2 \<gamma>1 \<gamma>2 com1 com2 sync s1 s2
                by (intro exI[of _ "CTrans trn1 trn2 # trr"]) auto
              qed
            next
              case False
              hence \<phi>12: "\<not> \<phi>1 trn1 \<and> \<not> \<phi>2 trn2" using sync_\<phi>1_\<phi>2[OF trn1 rs1 trn2 rs2 com1 com2 sync] by simp
              hence vl: "compV (One.V tr1) (Two.V tr2) vl" using vl by simp
              from ConsCons.IH(1)[OF tr1 tr2 rs1' rs2' vl obll]
              obtain trr where "validFrom (?s1, ?s2) trr" and "O trr = obll \<and> V trr = vl" by auto
              thus ?thesis using trn1 trn2 ComO \<phi>12 g1 g2 \<gamma>1 \<gamma>2 com1 com2 sync s1 s2
              by (intro exI[of _ "CTrans trn1 trn2 # trr"]) auto
            qed
          next
            case False
            hence \<phi>2: "\<phi>2 trn2" and com2: "\<not> isCom2 trn2" using \<phi>\<gamma>2 isCom2_\<gamma>2 trn2 s2 by auto
            have False using trr2 vl s2(2) \<phi>2 com2 isCom2_V2[OF trn2] s2 by (cases rule: compV_cases_V) auto
            thus ?thesis by simp
          qed
        next
          case False note \<gamma>1 = False
          hence obl: "compO (One.O tr1) (Two.O ?tr2) obl" using obl by simp
          have \<phi>1: "\<phi>1 trn1" and com1: "\<not> isCom1 trn1" using \<gamma>1 \<phi>\<gamma>1 isCom1_\<gamma>1 trn1 s1 by auto
          show ?thesis using trr2 vl s2(2) proof(cases rule: compV_cases_V)
            case Nil hence False using \<phi>1 by auto
            thus ?thesis by simp
          next
            case Com hence False using com1 \<phi>1 isCom1_isComV1[OF trn1] s1 by auto
            thus ?thesis by simp
          next
            case (Step1 vll1 vll2 vll v1) note Step1V = Step1
            hence f1: "f1 trn1 = v1" and "vll1 = One.V tr1" using \<phi>1 by auto
            hence vll: "compV (One.V tr1) (Two.V ?tr2) vll" using Step1V com1 by auto
            from ConsCons.IH(2)[OF _ tr1 trr2 rs1' s2(2) vll obl]
            obtain trr where "validFrom (?s1, s2) trr" and "O trr = obl \<and> V trr = vll"
            by auto
            thus ?thesis using trn1 Step1V f1 \<phi>1 \<gamma>1 trn1 s1 isCom1_isComO1 com1
            by (intro exI[of _ "Trans1 s2 trn1 # trr"]) auto
          qed
        qed
      qed
    qed
  qed
qed




lemma pullback_O_V:
assumes "One.validFrom istate1 tr1" and "Two.validFrom istate2 tr2"
and "compV (One.V tr1) (Two.V tr2) vl"
and "compO (One.O tr1) (Two.O tr2) ol"
shows "\<exists>tr. validFrom icstate tr \<and> O tr = ol \<and> V tr = vl"
using assms pullback_O_V_aux One.reach.Istate Two.reach.Istate unfolding icstate_def by auto

end (* context BD_Security_TS_Comp *)


sublocale BD_Security_TS_Comp \<subseteq> K? : Abstract_BD_Security_Comp where
  validSystemTraces1 = "One.validFrom istate1" and V1 = One.V and O1 = One.O
   and TT1 = "never T1" and B1 = B1 and
  validSystemTraces2 = "Two.validFrom istate2" and V2 = Two.V and O2 = Two.O
   and TT2 = "never T2" and B2 = B2 and
  validSystemTraces = "validFrom icstate" and V = V and O = O
   and TT = "never T" and B = B and
   comp = comp and compO = compO and compV = compV
  apply standard
  subgoal using validFrom by fastforce
  subgoal using compV by fastforce
  subgoal using compO by fastforce
  subgoal using T by fastforce
  subgoal using B by fastforce
  subgoal using pullback_O_V by fastforce
  done


context BD_Security_TS_Comp begin

(* Just contemplating the theorem provided as a
consequence of the sublocale inclusion: *)
theorem "secure1 \<Longrightarrow> secure2 \<Longrightarrow> secure"
using secure1_secure2_secure .

end (* context BD_Security_TS_Comp *)


end
