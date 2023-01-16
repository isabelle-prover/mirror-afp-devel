section \<open>Transporting BD Security\<close>

text \<open>This theory proves a transport theorem for BD security: from
a stronger to a weaker security model.
It corresponds to Theorem 2 from \<^cite>\<open>"cosmedis-SandP2017"\<close>
and to Theorem 6 (the Transport Theorem) from \<^cite>\<open>"BDsecurity-ITP2021"\<close>.
\<close>


theory Transporting_Security
imports Bounded_Deducibility_Security.BD_Security_TS
begin

locale Abstract_BD_Security_Trans =
  Orig: Abstract_BD_Security validSystemTrace V O B TT
+ Prime: Abstract_BD_Security validSystemTrace' V' O' B' TT'
for
  validSystemTrace :: "'traces \<Rightarrow> bool"
and
  V :: "'traces \<Rightarrow> 'values"
and
  O :: "'traces \<Rightarrow> 'observations"
and (* declassification bound: *)
  B :: "'values \<Rightarrow> 'values \<Rightarrow> bool"
and (* declassification trigger: *)
  TT :: "'traces \<Rightarrow> bool"
and
  validSystemTrace' :: "'traces' \<Rightarrow> bool"
and
  V' :: "'traces' \<Rightarrow> 'values'"
and
  O' :: "'traces' \<Rightarrow> 'observations'"
and (* declassification bound: *)
  B' :: "'values' \<Rightarrow> 'values' \<Rightarrow> bool"
and (* declassification trigger: *)
  TT' :: "'traces' \<Rightarrow> bool"
+
fixes
  translateTrace :: "'traces \<Rightarrow> 'traces'"
and
  translateObs :: "'observations \<Rightarrow> 'observations'"
and
  translateVal :: "'values \<Rightarrow> 'values'"
assumes
  vST_vST': "validSystemTrace tr \<Longrightarrow> validSystemTrace' (translateTrace tr)"
and
  vST'_vST: "validSystemTrace' tr' \<Longrightarrow> (\<exists>tr. validSystemTrace tr \<and> translateTrace tr = tr')"
and
  V'_V: "validSystemTrace tr \<Longrightarrow> V' (translateTrace tr) = translateVal (V tr)"
and
  O'_O: "validSystemTrace tr \<Longrightarrow> O' (translateTrace tr) = translateObs (O tr)"
and
  B'_B: "B' vl' vl1' \<Longrightarrow> validSystemTrace tr \<Longrightarrow> TT tr \<Longrightarrow> translateVal (V tr) = vl'
         \<Longrightarrow> (\<exists>vl1. translateVal vl1 = vl1' \<and> B (V tr) vl1)"
and
  TT'_TT: "TT' (translateTrace tr) \<Longrightarrow> validSystemTrace tr \<Longrightarrow> TT tr"
begin

lemma translate_secure:
assumes "Orig.secure"
shows "Prime.secure"
unfolding Prime.secure_def proof (intro allI impI, elim conjE)
  fix tr' vl' vl1'
  assume tr': "validSystemTrace' tr'" and TT': "TT' tr'" and B': "B' vl' vl1'" and vl': "V' tr' = vl'"
  from tr' obtain tr where tr: "validSystemTrace tr" "translateTrace tr = tr'"
    using vST'_vST by auto
  moreover have "TT tr" using TT' tr TT'_TT by auto
  moreover then obtain vl1 where "B (V tr) vl1" and vl1: "translateVal vl1 = vl1'"
    using tr B' B'_B[of vl' vl1' tr] vl' V'_V by auto
  ultimately obtain tr1 where "validSystemTrace tr1" "O tr1 = O tr" "V tr1 = vl1"
    using assms unfolding Orig.secure_def by auto
  then show "\<exists>tr1'. validSystemTrace' tr1' \<and> O' tr1' = O' tr' \<and> V' tr1' = vl1'"
    using vST_vST' O'_O V'_V tr vl1 by (intro exI[of _ "translateTrace tr1"]) auto
qed

end

locale BD_Security_TS_Trans =
  Orig: BD_Security_TS istate validTrans srcOf tgtOf \<phi> f \<gamma> g T B
+ Prime?: BD_Security_TS istate' validTrans' srcOf' tgtOf' \<phi>' f' \<gamma>' g' T' B'
for istate :: 'state and validTrans :: "'trans \<Rightarrow> bool"
and srcOf :: "'trans \<Rightarrow> 'state" and tgtOf :: "'trans \<Rightarrow> 'state"
and \<phi> :: "'trans \<Rightarrow> bool" and f :: "'trans \<Rightarrow> 'val"
and \<gamma> :: "'trans \<Rightarrow> bool" and g :: "'trans \<Rightarrow> 'obs"
and T :: "'trans \<Rightarrow> bool" and B :: "'val list \<Rightarrow> 'val list \<Rightarrow> bool"
and istate' :: 'state' and validTrans' :: "'trans' \<Rightarrow> bool"
and srcOf' :: "'trans' \<Rightarrow> 'state'" and tgtOf' :: "'trans' \<Rightarrow> 'state'"
and \<phi>' :: "'trans' \<Rightarrow> bool" and f' :: "'trans' \<Rightarrow> 'val'"
and \<gamma>' :: "'trans' \<Rightarrow> bool" and g' :: "'trans' \<Rightarrow> 'obs'"
and T' :: "'trans' \<Rightarrow> bool" and B' :: "'val' list \<Rightarrow> 'val' list \<Rightarrow> bool"
+
fixes
  translateState :: "'state \<Rightarrow> 'state'"
and
  translateTrans :: "'trans \<Rightarrow> 'trans'"
and
  translateObs :: "'obs \<Rightarrow> 'obs' option"
and
  translateVal :: "'val \<Rightarrow> 'val' option"
assumes
  vT_vT': "validTrans trn \<Longrightarrow> Orig.reach (srcOf trn) \<Longrightarrow> validTrans' (translateTrans trn)"
and
  vT'_vT: "validTrans' trn' \<Longrightarrow> srcOf' trn' = translateState s \<Longrightarrow> Orig.reach s \<Longrightarrow> (\<exists>trn. validTrans trn \<and> srcOf trn = s \<and> translateTrans trn = trn')"
and
  srcOf'_srcOf: "validTrans trn \<Longrightarrow> Orig.reach (srcOf trn) \<Longrightarrow> srcOf' (translateTrans trn) = translateState (srcOf trn)"
and
  tgtOf'_tgtOf: "validTrans trn \<Longrightarrow> Orig.reach (srcOf trn) \<Longrightarrow> tgtOf' (translateTrans trn) = translateState (tgtOf trn)"
and
  istate'_istate: "istate' = translateState istate"
and
  \<gamma>'_\<gamma>: "validTrans trn \<Longrightarrow> Orig.reach (srcOf trn) \<Longrightarrow> \<gamma>' (translateTrans trn) \<Longrightarrow> \<gamma> trn \<and> translateObs (g trn) = Some (g' (translateTrans trn))"
and
  \<gamma>_\<gamma>': "validTrans trn \<Longrightarrow> Orig.reach (srcOf trn) \<Longrightarrow> \<gamma> trn \<Longrightarrow> \<gamma>' (translateTrans trn) \<or> translateObs (g trn) = None"
and
  \<phi>'_\<phi>: "validTrans trn \<Longrightarrow> Orig.reach (srcOf trn) \<Longrightarrow> \<phi>' (translateTrans trn) \<Longrightarrow> \<phi> trn \<and> translateVal (f trn) = Some (f' (translateTrans trn))"
and
  \<phi>_\<phi>': "validTrans trn \<Longrightarrow> Orig.reach (srcOf trn) \<Longrightarrow> \<phi> trn \<Longrightarrow> \<phi>' (translateTrans trn) \<or> translateVal (f trn) = None"
and
  T_T': "T trn \<Longrightarrow> validTrans trn \<Longrightarrow> Orig.reach (srcOf trn) \<Longrightarrow> T' (translateTrans trn)"
and
  B'_B: "B' vl' vl1' \<Longrightarrow> Orig.validFrom istate tr \<Longrightarrow> never T tr \<Longrightarrow> these (map translateVal (Orig.V tr)) = vl'
         \<Longrightarrow> (\<exists>vl1. these (map translateVal vl1) = vl1' \<and> B (Orig.V tr) vl1)"
begin

definition translateTrace :: "'trans list \<Rightarrow> 'trans' list"
where "translateTrace = map translateTrans"

definition translateO :: "'obs list \<Rightarrow> 'obs' list"
where "translateO ol = these (map translateObs ol)"

definition translateV :: "'val list \<Rightarrow> 'val' list"
where "translateV vl = these (map translateVal vl)"

lemma validFrom_validFrom':
assumes "Orig.validFrom s tr"
and "Orig.reach s"
shows "Prime.validFrom (translateState s) (translateTrace tr)"
using assms unfolding translateTrace_def
proof (induction tr arbitrary: s)
  case (Cons trn tr s)
    then have tr: "Orig.validFrom (tgtOf trn) tr" and s': "Orig.reach (tgtOf trn)"
      unfolding Orig.validFrom_Cons by (auto intro: Orig.reach.Step)
    from Cons.IH[OF this] Cons.prems show ?case using vT_vT'
      by (auto simp: Orig.validFrom_Cons Prime.validFrom_Cons srcOf'_srcOf tgtOf'_tgtOf)
qed auto

lemma validFrom'_validFrom:
assumes "Prime.validFrom s' tr'"
and "s' = translateState s"
and "Orig.reach s"
obtains tr where "Orig.validFrom s tr" and "tr' = translateTrace tr"
using assms unfolding translateTrace_def
proof (induction tr' arbitrary: s' s)
  case (Cons trn' tr' s' s)
    obtain trn where trn: "validTrans trn" "srcOf trn = s" "trn' = translateTrans trn"
      using vT'_vT[of trn' s] Cons.prems unfolding Prime.validFrom_Cons by auto
    show thesis proof (rule Cons.IH)
      show "Prime.validFrom (tgtOf' trn') tr'" using Cons.prems unfolding Prime.validFrom_Cons by auto
      show "tgtOf' trn' = translateState (tgtOf trn)" using trn Cons.prems(4) tgtOf'_tgtOf by auto
      show "Orig.reach (tgtOf trn)" using trn Cons.prems(4)
        by (auto intro: Orig.reach.Step[of s trn "tgtOf trn"])
    next
      fix tr
      assume "Orig.validFrom (tgtOf trn) tr" "tr' = map translateTrans tr"
      then show thesis using trn Cons.prems
        by (intro Cons.prems(1)[of "trn # tr"]) (auto simp: Orig.validFrom_Cons)
    qed
qed auto

lemma V'_V:
assumes "Orig.validFrom s tr"
and "Orig.reach s"
shows "Prime.V (translateTrace tr) = translateV (Orig.V tr)"
using assms unfolding translateTrace_def translateV_def
proof (induction tr arbitrary: s)
  case (Cons trn tr s)
    then have "validTrans trn" "srcOf trn = s" "Orig.validFrom (tgtOf trn) tr" "Orig.reach (tgtOf trn)"
      unfolding Orig.validFrom_Cons by (auto intro: Orig.reach.Step[of s trn "tgtOf trn"])
    then show ?case using \<phi>'_\<phi>[of trn] \<phi>_\<phi>'[of trn] Cons(3) Cons.IH
      by (cases "\<phi> trn"; cases "\<phi>' (translateTrans trn)") auto
qed auto

lemma O'_O:
assumes "Orig.validFrom s tr"
and "Orig.reach s"
shows "Prime.O (translateTrace tr) = translateO (Orig.O tr)"
using assms unfolding translateTrace_def translateO_def
proof (induction tr arbitrary: s)
  case (Cons trn tr s)
    then have "validTrans trn" "srcOf trn = s" "Orig.validFrom (tgtOf trn) tr" "Orig.reach (tgtOf trn)"
      unfolding Orig.validFrom_Cons by (auto intro: Orig.reach.Step[of s trn "tgtOf trn"])
    then show ?case using \<gamma>'_\<gamma>[of trn] \<gamma>_\<gamma>'[of trn] Cons(3) Cons.IH
      by (cases "\<gamma> trn"; cases "\<gamma>' (translateTrans trn)") auto
qed auto

lemma TT'_TT:
assumes "never T' (translateTrace tr)"
and "Orig.validFrom s tr"
and "Orig.reach s"
shows "never T tr"
using assms unfolding translateTrace_def
proof (induction tr arbitrary: s)
  case (Cons trn tr s)
    moreover then have "never T tr" and "validTrans trn" and "srcOf trn = s"
      using Orig.reach.Step[of s trn "tgtOf trn"] unfolding Orig.validFrom_Cons by auto
    ultimately show ?case using T_T' by auto
qed auto

sublocale Abstract_BD_Security_Trans
where validSystemTrace = "Orig.validFrom istate" and O = Orig.O and V = Orig.V and TT = "never T"
and validSystemTrace' = "Prime.validFrom istate'" and O' = Prime.O and V' = Prime.V and TT' = "never T'"
and translateTrace = translateTrace and translateObs = translateO and translateVal = translateV
proof
  fix tr
  assume "Orig.validFrom istate tr"
  then show "Prime.validFrom istate' (translateTrace tr)"
    using Orig.reach.Istate unfolding istate'_istate by (intro validFrom_validFrom')
next
  fix tr'
  assume "Prime.validFrom istate' tr'"
  then show "\<exists>tr. Orig.validFrom istate tr \<and> translateTrace tr = tr'"
    using istate'_istate Orig.reach.Istate by (auto elim: validFrom'_validFrom)
next
  fix tr
  assume "Orig.validFrom istate tr"
  then show "Prime.V (translateTrace tr) = translateV (Orig.V tr)"
    using V'_V Orig.reach.Istate by blast
next
  fix tr
  assume "Orig.validFrom istate tr"
  then show "Prime.O (translateTrace tr) = translateO (Orig.O tr)"
    using O'_O Orig.reach.Istate by blast
next
  fix vl' vl1' tr
  assume "B' vl' vl1'" and "Orig.validFrom istate tr" and "translateV (Orig.V tr) = vl'"
     and "never T tr"
  then show "\<exists>vl1. translateV vl1 = vl1' \<and> B (Orig.V tr) vl1"
    using B'_B unfolding translateV_def by blast
next
  fix tr
  assume "never T' (translateTrace tr)" and "Orig.validFrom istate tr"
  then show "never T tr" using TT'_TT Orig.reach.Istate by blast
qed

theorem "Orig.secure \<Longrightarrow> Prime.secure" using translate_secure .

end


locale BD_Security_TS_Weaken_Observations =
  Orig: BD_Security_TS where g = g for g :: "'trans \<Rightarrow> 'obs"
+ fixes translateObs :: "'obs \<Rightarrow> 'obs' option"
begin

definition \<gamma>' :: "'trans \<Rightarrow> bool"
where "\<gamma>' trn \<equiv> \<gamma> trn \<and> translateObs (g trn) \<noteq> None"

definition g' :: "'trans \<Rightarrow> 'obs'"
where "g' trn \<equiv> the (translateObs (g trn))"

sublocale Prime?: BD_Security_TS istate validTrans srcOf tgtOf \<phi> f \<gamma>' g' T B .

sublocale BD_Security_TS_Trans istate validTrans srcOf tgtOf \<phi> f \<gamma> g T B
                               istate validTrans srcOf tgtOf \<phi> f \<gamma>' g' T B
                               id id translateObs Some
by (unfold_locales) (auto simp: \<gamma>'_def g'_def)

theorem "Orig.secure \<Longrightarrow> Prime.secure" using translate_secure .

end

end
