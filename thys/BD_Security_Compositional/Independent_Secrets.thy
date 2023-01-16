section \<open>Combining independent secret sources\<close>

text \<open>This theory formalizes the discussion about considering
combined sources of secrets from \<^cite>\<open>\<open>Appendix E\<close> in "cosmedis-SandP2017"\<close>.
\<close>

theory Independent_Secrets
imports Bounded_Deducibility_Security.BD_Security_TS
begin

locale Abstract_BD_Security_Two_Secrets =
  One: Abstract_BD_Security validSystemTrace V1 O1 B1 TT1
+ Two: Abstract_BD_Security validSystemTrace V2 O2 B2 TT2
for
  validSystemTrace :: "'traces \<Rightarrow> bool"
and
  V1 :: "'traces \<Rightarrow> 'values1"
and
  O1 :: "'traces \<Rightarrow> 'observations1"
and (* declassification bound: *)
  B1 :: "'values1 \<Rightarrow> 'values1 \<Rightarrow> bool"
and (* declassification trigger: *)
  TT1 :: "'traces \<Rightarrow> bool"
and
  V2 :: "'traces \<Rightarrow> 'values2"
and
  O2 :: "'traces \<Rightarrow> 'observations2"
and (* declassification bound: *)
  B2 :: "'values2 \<Rightarrow> 'values2 \<Rightarrow> bool"
and (* declassification trigger: *)
  TT2 :: "'traces \<Rightarrow> bool"
+
fixes
  O :: "'traces \<Rightarrow> 'observations"
assumes
  O1_O: "O1 tr = O1 tr' \<Longrightarrow> validSystemTrace tr \<Longrightarrow> validSystemTrace tr' \<Longrightarrow> O tr = O tr'"
and
  O2_O: "O2 tr = O2 tr' \<Longrightarrow> validSystemTrace tr \<Longrightarrow> validSystemTrace tr' \<Longrightarrow> O tr = O tr'"
and
  O1_V2: "O1 tr = O1 tr' \<Longrightarrow> validSystemTrace tr \<Longrightarrow> validSystemTrace tr' \<Longrightarrow> B1 (V1 tr) (V1 tr') \<Longrightarrow> V2 tr = V2 tr'"
and
  O2_V1: "O2 tr = O2 tr' \<Longrightarrow> validSystemTrace tr \<Longrightarrow> validSystemTrace tr' \<Longrightarrow> B2 (V2 tr) (V2 tr') \<Longrightarrow> V1 tr = V1 tr'"
and
  O1_TT2: "O1 tr = O1 tr' \<Longrightarrow> validSystemTrace tr \<Longrightarrow> validSystemTrace tr' \<Longrightarrow> B1 (V1 tr) (V1 tr') \<Longrightarrow> TT2 tr = TT2 tr'"
begin

definition "V tr = (V1 tr, V2 tr)"
definition "B vl vl' = (B1 (fst vl) (fst vl') \<and> B2 (snd vl) (snd vl'))"
definition "TT tr = (TT1 tr \<and> TT2 tr)"

sublocale Abstract_BD_Security validSystemTrace V O B TT .

theorem two_secure:
assumes "One.secure" and "Two.secure"
shows "secure"
unfolding secure_def
proof (intro allI impI, elim conjE)
  fix tr vl vl'
  assume tr: "validSystemTrace tr" and TT: "TT tr" and B: "B vl vl'" and V_tr: "V tr = vl"
  then obtain vl1' vl2' where vl: "vl = (V1 tr, V2 tr)" and vl': "vl' = (vl1', vl2')"
    by (cases vl, cases vl') (auto simp: V_def)
  obtain tr' where tr': "validSystemTrace tr'" and O1: "O1 tr' = O1 tr" and V1: "V1 tr' = vl1'"
    using assms(1) tr TT B by (auto elim: One.secureE simp: TT_def B_def V_def vl vl')
  then have O': "O tr' = O tr" and V2': "V2 tr = V2 tr'" and TT2': "TT2 tr = TT2 tr'"
    using B tr V1 by (auto intro: O1_O O1_V2 simp: O1_TT2 B_def vl vl')
  obtain tr'' where tr'': "validSystemTrace tr''" and O2: "O2 tr'' = O2 tr'" and V2: "V2 tr'' = vl2'"
    using assms(2) tr' TT2' TT B V2'
    by (elim Two.secureE[of tr' vl2']) (auto simp: TT_def B_def vl vl')
  moreover then have "O tr'' = O tr'" and "V1 tr' = V1 tr''"
    using B tr' V2 by (auto intro: O2_O O2_V1 simp: B_def V2' vl vl')
  ultimately show "\<exists>tr1. validSystemTrace tr1 \<and> O tr1 = O tr \<and> V tr1 = vl'"
    unfolding V_def V1 vl' O' by auto
qed

end

locale BD_Security_TS_Two_Secrets =
  One: BD_Security_TS istate validTrans srcOf tgtOf \<phi>1 f1 \<gamma>1 g1 T1 B1
+ Two: BD_Security_TS istate validTrans srcOf tgtOf \<phi>2 f2 \<gamma>2 g2 T2 B2
for istate :: 'state and validTrans :: "'trans \<Rightarrow> bool"
and srcOf :: "'trans \<Rightarrow> 'state" and tgtOf :: "'trans \<Rightarrow> 'state"
and \<phi>1 :: "'trans \<Rightarrow> bool" and f1 :: "'trans \<Rightarrow> 'val1"
and \<gamma>1 :: "'trans \<Rightarrow> bool" and g1 :: "'trans \<Rightarrow> 'obs1"
and T1 :: "'trans \<Rightarrow> bool" and B1 :: "'val1 list \<Rightarrow> 'val1 list \<Rightarrow> bool"
and \<phi>2 :: "'trans \<Rightarrow> bool" and f2 :: "'trans \<Rightarrow> 'val2"
and \<gamma>2 :: "'trans \<Rightarrow> bool" and g2 :: "'trans \<Rightarrow> 'obs2"
and T2 :: "'trans \<Rightarrow> bool" and B2 :: "'val2 list \<Rightarrow> 'val2 list \<Rightarrow> bool"
+
fixes \<gamma> :: "'trans \<Rightarrow> bool" and g :: "'trans \<Rightarrow> 'obs"
assumes \<gamma>_\<gamma>12: "\<And>tr trn. One.validFrom istate (tr ## trn) \<Longrightarrow> \<gamma> trn \<Longrightarrow> \<gamma>1 trn \<and> \<gamma>2 trn"
and O1_\<gamma>: "\<And>tr tr' trn trn'. One.O tr = One.O tr' \<Longrightarrow> One.validFrom istate (tr ## trn) \<Longrightarrow> One.validFrom istate (tr' ## trn') \<Longrightarrow> \<gamma>1 trn \<Longrightarrow> \<gamma>1 trn' \<Longrightarrow> g1 trn = g1 trn' \<Longrightarrow> \<gamma> trn = \<gamma> trn'"
and O1_g: "\<And>tr tr' trn trn'. One.O tr = One.O tr' \<Longrightarrow> One.validFrom istate (tr ## trn) \<Longrightarrow> One.validFrom istate (tr' ## trn') \<Longrightarrow> \<gamma>1 trn \<Longrightarrow> \<gamma>1 trn' \<Longrightarrow> g1 trn = g1 trn' \<Longrightarrow> \<gamma> trn \<Longrightarrow> \<gamma> trn' \<Longrightarrow> g trn = g trn'"
and O2_\<gamma>: "\<And>tr tr' trn trn'. Two.O tr = Two.O tr' \<Longrightarrow> One.validFrom istate (tr ## trn) \<Longrightarrow> One.validFrom istate (tr' ## trn') \<Longrightarrow> \<gamma>2 trn \<Longrightarrow> \<gamma>2 trn' \<Longrightarrow> g2 trn = g2 trn' \<Longrightarrow> \<gamma> trn = \<gamma> trn'"
and O2_g: "\<And>tr tr' trn trn'. Two.O tr = Two.O tr' \<Longrightarrow> One.validFrom istate (tr ## trn) \<Longrightarrow> One.validFrom istate (tr' ## trn') \<Longrightarrow> \<gamma>2 trn \<Longrightarrow> \<gamma>2 trn' \<Longrightarrow> g2 trn = g2 trn' \<Longrightarrow> \<gamma> trn \<Longrightarrow> \<gamma> trn' \<Longrightarrow> g trn = g trn'"
and \<phi>2_\<gamma>1: "\<And>tr trn. One.validFrom istate (tr ## trn) \<Longrightarrow> \<phi>2 trn \<Longrightarrow> \<gamma>1 trn"
and \<gamma>1_\<phi>2: "\<And>tr tr' trn trn'. One.O tr = One.O tr' \<Longrightarrow> One.validFrom istate (tr ## trn) \<Longrightarrow> One.validFrom istate (tr' ## trn') \<Longrightarrow> \<gamma>1 trn \<Longrightarrow> \<gamma>1 trn' \<Longrightarrow> g1 trn = g1 trn' \<Longrightarrow> \<phi>2 trn = \<phi>2 trn'"
and g1_f2: "\<And>tr tr' trn trn'. One.O tr = One.O tr' \<Longrightarrow> One.validFrom istate (tr ## trn) \<Longrightarrow> One.validFrom istate (tr' ## trn') \<Longrightarrow> \<gamma>1 trn \<Longrightarrow> \<gamma>1 trn' \<Longrightarrow> g1 trn = g1 trn' \<Longrightarrow> \<phi>2 trn \<Longrightarrow> \<phi>2 trn' \<Longrightarrow> f2 trn = f2 trn'"
and \<phi>1_\<gamma>2: "\<And>tr trn. One.validFrom istate (tr ## trn) \<Longrightarrow> \<phi>1 trn \<Longrightarrow> \<gamma>2 trn"
and \<gamma>2_\<phi>1: "\<And>tr tr' trn trn'. Two.O tr = Two.O tr' \<Longrightarrow> One.validFrom istate (tr ## trn) \<Longrightarrow> One.validFrom istate (tr' ## trn') \<Longrightarrow> \<gamma>2 trn \<Longrightarrow> \<gamma>2 trn' \<Longrightarrow> g2 trn = g2 trn' \<Longrightarrow> \<phi>1 trn = \<phi>1 trn'"
and g2_f1: "\<And>tr tr' trn trn'. Two.O tr = Two.O tr' \<Longrightarrow> One.validFrom istate (tr ## trn) \<Longrightarrow> One.validFrom istate (tr' ## trn') \<Longrightarrow> \<gamma>2 trn \<Longrightarrow> \<gamma>2 trn' \<Longrightarrow> g2 trn = g2 trn' \<Longrightarrow> \<phi>1 trn \<Longrightarrow> \<phi>1 trn' \<Longrightarrow> f1 trn = f1 trn'"
and T2_\<gamma>1: "\<And>tr trn. One.validFrom istate (tr ## trn) \<Longrightarrow> never T2 tr \<Longrightarrow> T2 trn \<Longrightarrow> \<gamma>1 trn"
and \<gamma>1_T2: "\<And>tr tr' trn trn'. One.O tr = One.O tr' \<Longrightarrow> One.validFrom istate (tr ## trn) \<Longrightarrow> One.validFrom istate (tr' ## trn') \<Longrightarrow> \<gamma>1 trn \<Longrightarrow> \<gamma>1 trn' \<Longrightarrow> g1 trn = g1 trn' \<Longrightarrow> T2 trn = T2 trn'"
begin

definition "O tr = map g (filter \<gamma> tr)"

lemma O_Nil_never: "O tr = [] \<longleftrightarrow> never \<gamma> tr" unfolding O_def by (induction tr) auto
lemma Nil_O_never: "[] = O tr \<longleftrightarrow> never \<gamma> tr" unfolding O_def by (induction tr) auto
lemma O_append: "O (tr @ tr') = O tr @ O tr'" unfolding O_def by auto

lemma never_\<gamma>12_never_\<gamma>: "One.validFrom istate (tr @ tr') \<Longrightarrow> never \<gamma>1 tr' \<or> never \<gamma>2 tr' \<Longrightarrow> never \<gamma> tr'"
proof (induction tr' rule: rev_induct)
  case (snoc trn tr')
  then show ?case using \<gamma>_\<gamma>12[of "tr @ tr'" trn] by (auto simp: One.validFrom_append)
qed auto

lemma never_\<gamma>1_never_\<phi>2: "One.validFrom istate (tr @ tr') \<Longrightarrow> never \<gamma>1 tr' \<Longrightarrow> never \<phi>2 tr'"
proof (induction tr' rule: rev_induct)
  case (snoc trn tr')
  then show ?case using \<phi>2_\<gamma>1[of "tr @ tr'" trn] by (auto simp: One.validFrom_append)
qed auto

lemma never_\<gamma>2_never_\<phi>1: "One.validFrom istate (tr @ tr') \<Longrightarrow> never \<gamma>2 tr' \<Longrightarrow> never \<phi>1 tr'"
proof (induction tr' rule: rev_induct)
  case (snoc trn tr')
  then show ?case using \<phi>1_\<gamma>2[of "tr @ tr'" trn] by (auto simp: One.validFrom_append)
qed auto

lemma never_\<gamma>1_never_T2: "One.validFrom istate (tr @ tr') \<Longrightarrow> never T2 tr \<Longrightarrow> never \<gamma>1 tr' \<Longrightarrow> never T2 tr'"
proof (induction tr' rule: rev_induct)
  case (snoc trn tr')
  then show ?case using T2_\<gamma>1[of "tr @ tr'" trn] by (auto simp: One.validFrom_append)
qed auto

sublocale Abstract_BD_Security_Two_Secrets "One.validFrom istate" One.V One.O B1 "never T1" Two.V Two.O B2 "never T2" O
proof
  fix tr tr'
  assume "One.O tr = One.O tr'" "One.validFrom istate tr" "One.validFrom istate tr'"
  then show "O tr = O tr'"
  proof (induction "One.O tr" arbitrary: tr tr' rule: rev_induct)
    case (Nil tr tr')
    then have tr: "O tr = []" using never_\<gamma>12_never_\<gamma>[of "[]" tr] by (auto simp: O_Nil_never One.O_Nil_never)
    show "O tr = O tr'" using Nil never_\<gamma>12_never_\<gamma>[of "[]" tr'] by (auto simp: tr Nil_O_never One.Nil_O_never)
  next
    case (snoc obs obsl tr tr')
    obtain tr1 trn tr2 where tr: "tr = tr1 @ [trn] @ tr2" and trn: "\<gamma>1 trn" "g1 trn = obs"
                         and tr1: "One.O tr1 = obsl" and tr2: "never \<gamma>1 tr2"
      using snoc(2) One.O_eq_RCons[of tr obsl obs] by auto
    obtain tr1' trn' tr2' where tr': "tr' = tr1' @ [trn'] @ tr2'" and trn': "\<gamma>1 trn'" "g1 trn' = obs"
                          and tr1': "One.O tr1' = obsl" and tr2': "never \<gamma>1 tr2'"
      using snoc(2,3) One.O_eq_RCons[of tr' obsl obs] by auto
    have "O tr1 = O tr1'" using snoc(1)[of tr1 tr1'] tr1 tr1' snoc(4,5) unfolding tr tr'
      by (auto simp: One.validFrom_append)
    moreover have "O [trn] = O [trn']" using O1_\<gamma>[of tr1 tr1' trn trn'] O1_g[of tr1 tr1' trn trn']
      using snoc(4,5) tr1 tr1' trn trn' by (auto simp: tr tr' O_def One.validFrom_append One.validFrom_Cons)
    moreover have "O tr2 = []" and "O tr2' = []" using tr2 tr2'
      using never_\<gamma>12_never_\<gamma>[of "tr1 ## trn" tr2] never_\<gamma>12_never_\<gamma>[of "tr1' ## trn'" tr2']
      using snoc(4,5) unfolding tr tr' by (auto simp: O_Nil_never)
    ultimately show "O tr = O tr'" unfolding tr tr' O_append by auto
  qed
next
  fix tr tr'
  assume "Two.O tr = Two.O tr'" "One.validFrom istate tr" "One.validFrom istate tr'"
  then show "O tr = O tr'"
  proof (induction "Two.O tr" arbitrary: tr tr' rule: rev_induct)
    case (Nil tr tr')
    then have tr: "O tr = []" using never_\<gamma>12_never_\<gamma>[of "[]" tr] by (auto simp: O_Nil_never Two.O_Nil_never)
    show "O tr = O tr'" using Nil never_\<gamma>12_never_\<gamma>[of "[]" tr'] by (auto simp: tr Nil_O_never Two.Nil_O_never)
  next
    case (snoc obs obsl tr tr')
    obtain tr1 trn tr2 where tr: "tr = tr1 @ [trn] @ tr2" and trn: "\<gamma>2 trn" "g2 trn = obs"
                         and tr1: "Two.O tr1 = obsl" and tr2: "never \<gamma>2 tr2"
      using snoc(2) Two.O_eq_RCons[of tr obsl obs] by auto
    obtain tr1' trn' tr2' where tr': "tr' = tr1' @ [trn'] @ tr2'" and trn': "\<gamma>2 trn'" "g2 trn' = obs"
                          and tr1': "Two.O tr1' = obsl" and tr2': "never \<gamma>2 tr2'"
      using snoc(2,3) Two.O_eq_RCons[of tr' obsl obs] by auto
    have "O tr1 = O tr1'" using snoc(1)[of tr1 tr1'] tr1 tr1' snoc(4,5) unfolding tr tr'
      by (auto simp: One.validFrom_append)
    moreover have "O [trn] = O [trn']" using O2_\<gamma>[of tr1 tr1' trn trn'] O2_g[of tr1 tr1' trn trn']
      using snoc(4,5) tr1 tr1' trn trn' by (auto simp: tr tr' O_def One.validFrom_append One.validFrom_Cons)
    moreover have "O tr2 = []" and "O tr2' = []" using tr2 tr2'
      using never_\<gamma>12_never_\<gamma>[of "tr1 ## trn" tr2] never_\<gamma>12_never_\<gamma>[of "tr1' ## trn'" tr2']
      using snoc(4,5) unfolding tr tr' by (auto simp: O_Nil_never)
    ultimately show "O tr = O tr'" unfolding tr tr' O_append by auto
  qed
next
  fix tr tr'
  assume "One.O tr = One.O tr'" "One.validFrom istate tr" "One.validFrom istate tr'"
  then show "Two.V tr = Two.V tr'"
  proof (induction "One.O tr" arbitrary: tr tr' rule: rev_induct)
    case (Nil tr tr')
    then have tr: "Two.V tr = []" using never_\<gamma>1_never_\<phi>2[of "[]" tr]
      unfolding Two.V_Nil_never One.Nil_O_never by auto
    show "Two.V tr = Two.V tr'" using never_\<gamma>1_never_\<phi>2[of "[]" tr'] using Nil
      unfolding tr Two.Nil_V_never One.O_Nil_never[symmetric] by auto
  next
    case (snoc obs obsl tr tr')
    obtain tr1 trn tr2 where tr: "tr = tr1 @ [trn] @ tr2" and trn: "\<gamma>1 trn" "g1 trn = obs"
                         and tr1: "One.O tr1 = obsl" and tr2: "never \<gamma>1 tr2"
      using snoc(2) One.O_eq_RCons[of tr obsl obs] by auto
    obtain tr1' trn' tr2' where tr': "tr' = tr1' @ [trn'] @ tr2'" and trn': "\<gamma>1 trn'" "g1 trn' = obs"
                          and tr1': "One.O tr1' = obsl" and tr2': "never \<gamma>1 tr2'"
      using snoc(2,3) One.O_eq_RCons[of tr' obsl obs] by auto
    have "Two.V tr1 = Two.V tr1'" using snoc(1)[of tr1 tr1'] tr1 tr1' snoc(4,5) unfolding tr tr'
      by (auto simp: One.validFrom_append)
    moreover have "Two.V [trn] = Two.V [trn']" using \<gamma>1_\<phi>2[of tr1 tr1' trn trn'] g1_f2[of tr1 tr1' trn trn']
      using snoc(4,5) tr1 tr1' trn trn' unfolding tr tr' Two.V_map_filter
      by (auto simp: One.validFrom_append One.validFrom_Cons)
    moreover have "Two.V tr2 = []" and "Two.V tr2' = []" using tr2 tr2'
      using never_\<gamma>1_never_\<phi>2[of "tr1 ## trn" tr2] never_\<gamma>1_never_\<phi>2[of "tr1' ## trn'" tr2']
      using snoc(4,5) unfolding tr tr' by (auto simp: Two.V_Nil_never)
    ultimately show "Two.V tr = Two.V tr'" unfolding tr tr' Two.V_append by auto
  qed
next
  fix tr tr'
  assume "Two.O tr = Two.O tr'" "One.validFrom istate tr" "One.validFrom istate tr'"
  then show "One.V tr = One.V tr'"
  proof (induction "Two.O tr" arbitrary: tr tr' rule: rev_induct)
    case (Nil tr tr')
    then have tr: "One.V tr = []" using never_\<gamma>2_never_\<phi>1[of "[]" tr]
      unfolding One.V_Nil_never Two.Nil_O_never by auto
    show "One.V tr = One.V tr'" using never_\<gamma>2_never_\<phi>1[of "[]" tr'] using Nil
      unfolding tr One.Nil_V_never Two.O_Nil_never[symmetric] by auto
  next
    case (snoc obs obsl tr tr')
    obtain tr1 trn tr2 where tr: "tr = tr1 @ [trn] @ tr2" and trn: "\<gamma>2 trn" "g2 trn = obs"
                         and tr1: "Two.O tr1 = obsl" and tr2: "never \<gamma>2 tr2"
      using snoc(2) Two.O_eq_RCons[of tr obsl obs] by auto
    obtain tr1' trn' tr2' where tr': "tr' = tr1' @ [trn'] @ tr2'" and trn': "\<gamma>2 trn'" "g2 trn' = obs"
                          and tr1': "Two.O tr1' = obsl" and tr2': "never \<gamma>2 tr2'"
      using snoc(2,3) Two.O_eq_RCons[of tr' obsl obs] by auto
    have "One.V tr1 = One.V tr1'" using snoc(1)[of tr1 tr1'] tr1 tr1' snoc(4,5) unfolding tr tr'
      by (auto simp: One.validFrom_append)
    moreover have "One.V [trn] = One.V [trn']" using \<gamma>2_\<phi>1[of tr1 tr1' trn trn'] g2_f1[of tr1 tr1' trn trn']
      using snoc(4,5) tr1 tr1' trn trn' unfolding tr tr' Two.V_map_filter
      by (auto simp: One.validFrom_append One.validFrom_Cons)
    moreover have "One.V tr2 = []" and "One.V tr2' = []" using tr2 tr2'
      using never_\<gamma>2_never_\<phi>1[of "tr1 ## trn" tr2] never_\<gamma>2_never_\<phi>1[of "tr1' ## trn'" tr2']
      using snoc(4,5) unfolding tr tr' by (auto simp: One.V_Nil_never)
    ultimately show "One.V tr = One.V tr'" unfolding tr tr' One.V_append by auto
  qed
next
  fix tr tr'
  assume "One.O tr = One.O tr'" "One.validFrom istate tr" "One.validFrom istate tr'"
  then show "never T2 tr = never T2 tr'"
  proof (induction "One.O tr" arbitrary: tr tr' rule: rev_induct)
    case (Nil tr tr')
    then have tr: "never T2 tr" using never_\<gamma>1_never_T2[of "[]" tr]
      unfolding Two.V_Nil_never One.Nil_O_never by auto
    then show "never T2 tr = never T2 tr'" using never_\<gamma>1_never_T2[of "[]" tr'] using Nil
      unfolding tr Two.Nil_V_never One.O_Nil_never[symmetric] by auto
  next
    case (snoc obs obsl tr tr')
    obtain tr1 trn tr2 where tr: "tr = tr1 @ [trn] @ tr2" and trn: "\<gamma>1 trn" "g1 trn = obs"
                         and tr1: "One.O tr1 = obsl" and tr2: "never \<gamma>1 tr2"
      using snoc(2) One.O_eq_RCons[of tr obsl obs] by auto
    obtain tr1' trn' tr2' where tr': "tr' = tr1' @ [trn'] @ tr2'" and trn': "\<gamma>1 trn'" "g1 trn' = obs"
                          and tr1': "One.O tr1' = obsl" and tr2': "never \<gamma>1 tr2'"
      using snoc(2,3) One.O_eq_RCons[of tr' obsl obs] by auto
    have "never T2 tr1 = never T2 tr1'" using snoc(1)[of tr1 tr1'] tr1 tr1' snoc(4,5) unfolding tr tr'
      by (auto simp: One.validFrom_append)
    moreover have "T2 trn = T2 trn'" using \<gamma>1_T2[of tr1 tr1' trn trn']
      using snoc(4,5) tr1 tr1' trn trn' unfolding tr tr' Two.V_map_filter
      by (auto simp: One.validFrom_append One.validFrom_Cons)
    moreover have "never T2 (tr1 ## trn) \<longrightarrow> never T2 tr2"
              and "never T2 (tr1' ## trn') \<longrightarrow> never T2 tr2'"
      using never_\<gamma>1_never_T2[of "tr1 ## trn" tr2] never_\<gamma>1_never_T2[of "tr1' ## trn'" tr2']
      using tr2 tr2' snoc(4,5) unfolding tr tr' by (auto simp: Two.V_Nil_never)
    ultimately show "never T2 tr = never T2 tr'" unfolding tr tr' by auto
  qed
qed

end

end
