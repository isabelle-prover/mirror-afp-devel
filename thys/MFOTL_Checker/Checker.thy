(*<*)
theory Checker
  imports Prelim Proof_System Proof_Object "HOL-Library.Simps_Case_Conv"
begin
(*>*)

section \<open>Proof Checker\<close>

unbundle MFOTL_notation

context fixes \<sigma> :: "('n, 'd :: {default, linorder}) trace"

begin

fun s_check :: "('n, 'd) env \<Rightarrow> ('n, 'd) formula \<Rightarrow> ('n, 'd) sproof \<Rightarrow> bool"
and v_check :: "('n, 'd) env \<Rightarrow> ('n, 'd) formula \<Rightarrow> ('n, 'd) vproof \<Rightarrow> bool" where
  "s_check v f p = (case (f, p) of
    (\<top>, STT i) \<Rightarrow> True
  | (r \<dagger> ts, SPred i s ts') \<Rightarrow>
    (r = s \<and> ts = ts' \<and> (r, v\<^bold>\<lbrakk>ts\<^bold>\<rbrakk>) \<in> \<Gamma> \<sigma> i)
  | (x \<^bold>\<approx> c, SEq_Const i x' c') \<Rightarrow>
    (c = c' \<and> x = x' \<and> v x = c)
  | (\<not>\<^sub>F \<phi>, SNeg vp) \<Rightarrow> v_check v \<phi> vp
  | (\<phi> \<or>\<^sub>F \<psi>, SOrL sp1) \<Rightarrow> s_check v \<phi> sp1
  | (\<phi> \<or>\<^sub>F \<psi>, SOrR sp2) \<Rightarrow> s_check v \<psi> sp2
  | (\<phi> \<and>\<^sub>F \<psi>, SAnd sp1 sp2) \<Rightarrow> s_check v \<phi> sp1 \<and> s_check v \<psi> sp2 \<and> s_at sp1 = s_at sp2
  | (\<phi> \<longrightarrow>\<^sub>F \<psi>, SImpL vp1) \<Rightarrow> v_check v \<phi> vp1
  | (\<phi> \<longrightarrow>\<^sub>F \<psi>, SImpR sp2) \<Rightarrow> s_check v \<psi> sp2
  | (\<phi> \<longleftrightarrow>\<^sub>F \<psi>, SIffSS sp1 sp2) \<Rightarrow> s_check v \<phi> sp1 \<and> s_check v \<psi> sp2 \<and> s_at sp1 = s_at sp2
  | (\<phi> \<longleftrightarrow>\<^sub>F \<psi>, SIffVV vp1 vp2) \<Rightarrow> v_check v \<phi> vp1 \<and> v_check v \<psi> vp2 \<and> v_at vp1 = v_at vp2
  | (\<exists>\<^sub>Fx.  \<phi>, SExists y val sp) \<Rightarrow> (x = y \<and> s_check (v (x := val)) \<phi> sp)
  | (\<forall>\<^sub>Fx.  \<phi>, SForall y sp_part) \<Rightarrow> (let i = s_at (part_hd sp_part)
      in x = y \<and> (\<forall>(sub, sp) \<in> SubsVals sp_part. s_at sp = i \<and> (\<forall>z \<in> sub. s_check (v (x := z)) \<phi> sp)))
  | (\<^bold>Y I \<phi>, SPrev sp) \<Rightarrow>
    (let j = s_at sp; i = s_at (SPrev sp) in
    i = j+1 \<and> mem (\<Delta> \<sigma> i) I \<and> s_check v \<phi> sp)
  | (\<^bold>X I \<phi>, SNext sp) \<Rightarrow>
    (let j = s_at sp; i = s_at (SNext sp) in
    j = i+1 \<and> mem (\<Delta> \<sigma> j) I \<and> s_check v \<phi> sp)
  | (\<^bold>P I \<phi>, SOnce i sp) \<Rightarrow>
    (let j = s_at sp in
    j \<le> i \<and> mem (\<tau> \<sigma> i - \<tau> \<sigma> j) I \<and> s_check v \<phi> sp)
  | (\<^bold>F I \<phi>, SEventually i sp) \<Rightarrow>
    (let j = s_at sp in
    j \<ge> i \<and> mem (\<tau> \<sigma> j - \<tau> \<sigma> i) I \<and> s_check v \<phi> sp)
  | (\<^bold>H I \<phi>, SHistoricallyOut i) \<Rightarrow>
    \<tau> \<sigma> i < \<tau> \<sigma> 0 + left I
  | (\<^bold>H I \<phi>, SHistorically i li sps) \<Rightarrow>
    (li = (case right I of \<infinity> \<Rightarrow> 0 | enat b \<Rightarrow> ETP \<sigma> (\<tau> \<sigma> i - b))
    \<and> \<tau> \<sigma> 0 + left I \<le> \<tau> \<sigma> i
    \<and> map s_at sps = [li ..< (LTP_p \<sigma> i I) + 1]
    \<and> (\<forall>sp \<in> set sps. s_check v \<phi> sp))
  | (\<^bold>G I \<phi>, SAlways i hi sps) \<Rightarrow>
    (hi = (case right I of enat b \<Rightarrow> LTP_f \<sigma> i b)
    \<and> right I \<noteq> \<infinity>
    \<and> map s_at sps = [(ETP_f \<sigma> i I) ..< hi + 1]
    \<and> (\<forall>sp \<in> set sps. s_check v \<phi> sp))
  | (\<phi> \<^bold>S I \<psi>, SSince sp2 sp1s) \<Rightarrow>
    (let i = s_at (SSince sp2 sp1s); j = s_at sp2 in
    j \<le> i \<and> mem (\<tau> \<sigma> i - \<tau> \<sigma> j) I
    \<and> map s_at sp1s = [j+1 ..< i+1]
    \<and> s_check v \<psi> sp2
    \<and> (\<forall>sp1 \<in> set sp1s. s_check v \<phi> sp1))
  | (\<phi> \<^bold>U I \<psi>, SUntil sp1s sp2) \<Rightarrow>
    (let i = s_at (SUntil sp1s sp2); j = s_at sp2 in
    j \<ge> i \<and> mem (\<tau> \<sigma> j - \<tau> \<sigma> i) I
    \<and> map s_at sp1s = [i ..< j] \<and> s_check v \<psi> sp2
    \<and> (\<forall>sp1 \<in> set sp1s. s_check v \<phi> sp1))
  | ( _ , _) \<Rightarrow> False)"
| "v_check v f p = (case (f, p) of
    (\<bottom>, VFF i) \<Rightarrow> True
  | (r \<dagger> ts, VPred i pred ts') \<Rightarrow>
    (r = pred \<and> ts = ts' \<and> (r, v\<^bold>\<lbrakk>ts\<^bold>\<rbrakk>) \<notin> \<Gamma> \<sigma> i)
  | (x \<^bold>\<approx> c, VEq_Const i x' c') \<Rightarrow>
    (c = c' \<and> x = x' \<and> v x \<noteq> c)
  | (\<not>\<^sub>F \<phi>, VNeg sp) \<Rightarrow> s_check v \<phi> sp
  | (\<phi> \<or>\<^sub>F \<psi>, VOr vp1 vp2) \<Rightarrow> v_check v \<phi> vp1 \<and> v_check v \<psi> vp2 \<and> v_at vp1 = v_at vp2
  | (\<phi> \<and>\<^sub>F \<psi>, VAndL vp1) \<Rightarrow> v_check v \<phi> vp1
  | (\<phi> \<and>\<^sub>F \<psi>, VAndR vp2) \<Rightarrow> v_check v \<psi> vp2
  | (\<phi> \<longrightarrow>\<^sub>F \<psi>, VImp sp1 vp2) \<Rightarrow> s_check v \<phi> sp1 \<and> v_check v \<psi> vp2 \<and> s_at sp1 = v_at vp2
  | (\<phi> \<longleftrightarrow>\<^sub>F \<psi>, VIffSV sp1 vp2) \<Rightarrow> s_check v \<phi> sp1 \<and> v_check v \<psi> vp2 \<and> s_at sp1 = v_at vp2
  | (\<phi> \<longleftrightarrow>\<^sub>F \<psi>, VIffVS vp1 sp2) \<Rightarrow> v_check v \<phi> vp1 \<and> s_check v \<psi> sp2 \<and> v_at vp1 = s_at sp2
  | (\<exists>\<^sub>Fx.  \<phi>, VExists y vp_part) \<Rightarrow> (let i = v_at (part_hd vp_part)
      in x = y \<and> (\<forall>(sub, vp) \<in> SubsVals vp_part. v_at vp = i \<and> (\<forall>z \<in> sub. v_check (v (x := z)) \<phi> vp)))
  | (\<forall>\<^sub>Fx.  \<phi>, VForall y val vp) \<Rightarrow> (x = y \<and> v_check (v (x := val)) \<phi> vp)
  | (\<^bold>Y I \<phi>, VPrev vp) \<Rightarrow>
    (let j = v_at vp; i = v_at (VPrev vp) in
    i = j+1 \<and> v_check v \<phi> vp)
  | (\<^bold>Y I \<phi>, VPrevZ) \<Rightarrow> True
  | (\<^bold>Y I \<phi>, VPrevOutL i) \<Rightarrow>
    i > 0 \<and> \<Delta> \<sigma> i < left I
  | (\<^bold>Y I \<phi>, VPrevOutR i) \<Rightarrow>
    i > 0 \<and> enat (\<Delta> \<sigma> i) > right I
  | (\<^bold>X I \<phi>, VNext vp) \<Rightarrow>
    (let j = v_at vp; i = v_at (VNext vp) in
    j = i+1 \<and> v_check v \<phi> vp)
  | (\<^bold>X I \<phi>, VNextOutL i) \<Rightarrow>
    \<Delta> \<sigma> (i+1) < left I
  | (\<^bold>X I \<phi>, VNextOutR i) \<Rightarrow>
    enat (\<Delta> \<sigma> (i+1)) > right I
  | (\<^bold>P I \<phi>, VOnceOut i) \<Rightarrow>
    \<tau> \<sigma> i < \<tau> \<sigma> 0 + left I
  | (\<^bold>P I \<phi>, VOnce i li vps) \<Rightarrow>
    (li = (case right I of \<infinity> \<Rightarrow> 0 | enat b \<Rightarrow> ETP_p \<sigma> i b)
    \<and> \<tau> \<sigma> 0 + left I \<le> \<tau> \<sigma> i
    \<and> map v_at vps = [li ..< (LTP_p \<sigma> i I) + 1]
    \<and> (\<forall>vp \<in> set vps. v_check v \<phi> vp))
  | (\<^bold>F I \<phi>, VEventually i hi vps) \<Rightarrow>
    (hi = (case right I of enat b \<Rightarrow> LTP_f \<sigma> i b) \<and> right I \<noteq> \<infinity>
    \<and> map v_at vps = [(ETP_f \<sigma> i I) ..< hi + 1]
    \<and> (\<forall>vp \<in> set vps. v_check v \<phi> vp))
  | (\<^bold>H I \<phi>, VHistorically i vp) \<Rightarrow>
    (let j = v_at vp in
    j \<le> i \<and> mem (\<tau> \<sigma> i - \<tau> \<sigma> j) I \<and> v_check v \<phi> vp)
  | (\<^bold>G I \<phi>, VAlways i vp) \<Rightarrow>
    (let j = v_at vp
    in j \<ge> i \<and> mem (\<tau> \<sigma> j - \<tau> \<sigma> i) I \<and> v_check v \<phi> vp)
  | (\<phi> \<^bold>S I \<psi>, VSinceOut i) \<Rightarrow>
    \<tau> \<sigma> i < \<tau> \<sigma> 0 + left I
  | (\<phi> \<^bold>S I \<psi>, VSince i vp1 vp2s) \<Rightarrow>
    (let j = v_at vp1 in
    (case right I of \<infinity> \<Rightarrow> True | enat b \<Rightarrow> ETP_p \<sigma> i b \<le> j) \<and> j \<le> i
    \<and> \<tau> \<sigma> 0 + left I \<le> \<tau> \<sigma> i
    \<and> map v_at vp2s = [j ..< (LTP_p \<sigma> i I) + 1] \<and> v_check v \<phi> vp1
    \<and> (\<forall>vp2 \<in> set vp2s. v_check v \<psi> vp2))
  | (\<phi> \<^bold>S I \<psi>, VSinceInf i li vp2s) \<Rightarrow>
    (li = (case right I of \<infinity> \<Rightarrow> 0 | enat b \<Rightarrow> ETP_p \<sigma> i b)
    \<and> \<tau> \<sigma> 0 + left I \<le> \<tau> \<sigma> i
    \<and> map v_at vp2s = [li ..< (LTP_p \<sigma> i I) + 1]
    \<and> (\<forall>vp2 \<in> set vp2s. v_check v \<psi> vp2))
  | (\<phi> \<^bold>U I \<psi>, VUntil i vp2s vp1) \<Rightarrow>
    (let j = v_at vp1 in
    (case right I of \<infinity> \<Rightarrow> True | enat b \<Rightarrow> j < LTP_f \<sigma> i b) \<and> i \<le> j
    \<and> map v_at vp2s = [ETP_f \<sigma> i I ..< j + 1] \<and> v_check v \<phi> vp1
    \<and> (\<forall>vp2 \<in> set vp2s. v_check v \<psi> vp2))
  | (\<phi> \<^bold>U I \<psi>, VUntilInf i hi vp2s) \<Rightarrow>
    (hi = (case right I of enat b \<Rightarrow> LTP_f \<sigma> i b) \<and> right I \<noteq> \<infinity>
    \<and> map v_at vp2s = [ETP_f \<sigma> i I ..< hi + 1]
    \<and> (\<forall>vp2 \<in> set vp2s. v_check v \<psi> vp2))
  | ( _ , _) \<Rightarrow> False)"

declare s_check.simps[simp del] v_check.simps[simp del]
simps_of_case s_check_simps[simp]: s_check.simps[unfolded prod.case] (splits: formula.split sproof.split)
simps_of_case v_check_simps[simp]: v_check.simps[unfolded prod.case] (splits: formula.split vproof.split)

subsection \<open>Checker Soundness\<close>

lemma check_soundness:
  "s_check v \<phi> sp \<Longrightarrow> SAT \<sigma> v (s_at sp) \<phi>"
  "v_check v \<phi> vp \<Longrightarrow> VIO \<sigma> v (v_at vp) \<phi>"
proof (induction sp and vp arbitrary: v \<phi> and v \<phi>)
  case STT
  then show ?case by (cases \<phi>) (auto intro: SAT_VIO.STT)
next
  case SPred
  then show ?case by (cases \<phi>) (auto intro: SAT_VIO.SPred)
next
  case SEq_Const
  then show ?case by (cases \<phi>) (auto intro: SAT_VIO.SEq_Const)
next
  case SNeg
  then show ?case by (cases \<phi>) (auto intro: SAT_VIO.SNeg)
next
  case SAnd
  then show ?case by (cases \<phi>) (auto intro: SAT_VIO.SAnd)
next
  case SOrL
  then show ?case by (cases \<phi>) (auto intro: SAT_VIO.SOrL)
next
  case SOrR
  then show ?case by (cases \<phi>) (auto intro: SAT_VIO.SOrR)
next
  case SImpR
  then show ?case by (cases \<phi>) (auto intro: SAT_VIO.SImpR)
next
  case SImpL
  then show ?case by (cases \<phi>) (auto intro: SAT_VIO.SImpL)
next
  case SIffSS
  then show ?case by (cases \<phi>) (auto intro: SAT_VIO.SIffSS)
next
  case SIffVV
  then show ?case by (cases \<phi>) (auto intro: SAT_VIO.SIffVV)
next
  case (SExists x z sp)
  with SExists(1)[of "v(x := z)"] show ?case
    by (cases \<phi>) (auto intro: SAT_VIO.SExists)
next
  case (SForall x part)
  then show ?case
  proof (cases \<phi>)
    case (Forall y \<psi>)
    show ?thesis unfolding Forall
    proof (intro SAT_VIO.SForall allI)
      fix z
      let ?sp = "lookup_part part z"
      from lookup_part_SubsVals[of z part] obtain D where "z \<in> D" "(D, ?sp) \<in> SubsVals part"
        by blast
      with SForall(2-) Forall have "s_check (v(y := z)) \<psi> ?sp" "s_at ?sp = s_at (SForall x part)"
        by auto
      then show "SAT \<sigma> (v(y := z)) (s_at (SForall x part)) \<psi>"
        by (auto simp del: fun_upd_apply dest!: SForall(1)[rotated])
    qed
  qed auto
next
  case (SSince spsi sps)
  then show ?case
  proof (cases \<phi>)
    case (Since \<phi> I \<psi>)
    show ?thesis
      using SSince(3)
      unfolding Since
    proof (intro SAT_VIO.SSince[of "s_at spsi"], goal_cases le mem SAT\<psi> SAT\<phi>)
      case (SAT\<phi> k)
      then show ?case
        by (cases "k \<le> s_at (hd sps)")
          (auto 0 3 simp: Let_def elim: map_setE[of _ _ _ k] intro: SSince(2) dest!: sym[of "s_at _" "Suc (s_at _)"])
    qed (auto simp: Let_def intro: SSince(1))
  qed auto
next
  case (SOnce i sp)
  then show ?case
  proof (cases \<phi>)
    case (Once I \<phi>)
    show ?thesis
      using SOnce
      unfolding Once
      by (intro SAT_VIO.SOnce[of "s_at sp"]) (auto simp: Let_def)
  qed auto
next
  case (SEventually i sp)
  then show ?case
  proof (cases \<phi>)
    case (Eventually I \<phi>)
    show ?thesis
      using SEventually
      unfolding Eventually
      by (intro SAT_VIO.SEventually[of _ "s_at sp"]) (auto simp: Let_def)
  qed auto
next
  case SHistoricallyOut
  then show ?case by (cases \<phi>) (auto intro: SAT_VIO.SHistoricallyOut)
next
  case (SHistorically i li sps)
  then show ?case
  proof (cases \<phi>)
    case (Historically I \<phi>)
    {fix k
      define j where j_def: "j \<equiv> case right I of \<infinity> \<Rightarrow> 0 | enat n \<Rightarrow> ETP \<sigma> (\<tau>  \<sigma> i - n)"
      assume k_def: "k \<ge> j \<and> k \<le> i \<and> k \<le> LTP \<sigma> (\<tau> \<sigma> i - left I)"
      from SHistorically Historically j_def have map: "set (map s_at sps) = set [j ..< Suc (LTP_p \<sigma> i I)]"
        by (auto simp: Let_def)
      then have kset: "k \<in> set ([j ..< Suc (LTP_p \<sigma> i I)])" using j_def k_def by auto
      then obtain x where x: "x \<in> set sps"  "s_at x = k" using k_def map
        unfolding set_map set_eq_iff image_iff
        by metis
      then have "SAT \<sigma> v k \<phi>" using SHistorically unfolding Historically
        by (auto simp: Let_def)
    } note * = this
    show ?thesis
      using SHistorically *
      unfolding Historically
      by (auto simp: Let_def intro!: SAT_VIO.SHistorically)
  qed (auto intro: SAT_VIO.intros)
next
  case (SAlways i hi sps)
  then show ?case
  proof (cases \<phi>)
    case (Always I \<phi>)
    obtain n where n_def: "right I = enat n"
      using SAlways
      by (auto simp: Always split: enat.splits)
    {fix k
      define j where j_def: "j \<equiv> LTP \<sigma> (\<tau> \<sigma> i + n)"
      assume k_def: "k \<le> j \<and> k \<ge> i \<and> k \<ge> ETP \<sigma> (\<tau> \<sigma> i + left I)"
      from SAlways Always j_def have map: "set (map s_at sps) = set [(ETP_f \<sigma> i I) ..< Suc j]"
        by (auto simp: Let_def n_def)
      then have kset: "k \<in> set ([(ETP_f \<sigma> i I) ..< Suc j])" using k_def j_def by auto
      then obtain x where x: "x \<in> set sps" "s_at x = k" using k_def map
        unfolding set_map set_eq_iff image_iff
        by metis
      then have "SAT \<sigma> v k \<phi>" using SAlways unfolding Always
        by (auto simp: Let_def n_def)
    } note * = this
    then show ?thesis
      using SAlways
      unfolding Always
      by (auto simp: Let_def n_def intro: SAT_VIO.SAlways split: if_splits enat.splits)
  qed(auto intro: SAT_VIO.intros)
next
  case (SUntil sps spsi)
  then show ?case
  proof (cases \<phi>)
    case (Until \<phi> I \<psi>)
    show ?thesis
      using SUntil(3)
      unfolding Until
    proof (intro SAT_VIO.SUntil[of _ "s_at spsi"], goal_cases le mem SAT\<psi> SAT\<phi>)
      case (SAT\<phi> k)
      then show ?case
        by (cases "k \<le> s_at (hd sps)")
          (auto 0 3 simp: Let_def elim: map_setE[of _ _ _ k] intro: SUntil(1))
    qed (auto simp: Let_def intro: SUntil(2))
  qed auto
next
  case (SNext sp)
  then show ?case by (cases \<phi>) (auto simp add: Let_def SAT_VIO.SNext)
next
  case (SPrev sp)
  then show ?case by (cases \<phi>) (auto simp add: Let_def SAT_VIO.SPrev)
next
  case VFF
  then show ?case by (cases \<phi>) (auto intro: SAT_VIO.VFF)
next
  case VPred
  then show ?case by (cases \<phi>) (auto intro: SAT_VIO.VPred)
next
  case VEq_Const
  then show ?case by (cases \<phi>) (auto intro: SAT_VIO.VEq_Const)
next
  case VNeg
  then show ?case by (cases \<phi>) (auto intro: SAT_VIO.VNeg)
next
  case VOr
  then show ?case by (cases \<phi>) (auto intro: SAT_VIO.VOr)
next
  case VAndL
  then show ?case by (cases \<phi>) (auto intro: SAT_VIO.VAndL)
next
  case VAndR
  then show ?case by (cases \<phi>) (auto intro: SAT_VIO.VAndR)
next
  case VImp
  then show ?case by (cases \<phi>) (auto intro: SAT_VIO.VImp)
next
  case VIffSV
  then show ?case by (cases \<phi>) (auto intro: SAT_VIO.VIffSV)
next
  case VIffVS
  then show ?case by (cases \<phi>) (auto intro: SAT_VIO.VIffVS)
next
  case (VExists x part)
  then show ?case
  proof (cases \<phi>)
    case (Exists y \<psi>)
    show ?thesis unfolding Exists
    proof (intro SAT_VIO.VExists allI)
      fix z
      let ?vp = "lookup_part part z"
      from lookup_part_SubsVals[of z part] obtain D where "z \<in> D" "(D, ?vp) \<in> SubsVals part"
        by blast
      with VExists(2-) Exists have "v_check (v(y := z)) \<psi> ?vp" "v_at ?vp = v_at (VExists x part)"
        by auto
      then show "VIO \<sigma> (v(y := z)) (v_at (VExists x part)) \<psi>"
        by (auto simp del: fun_upd_apply dest!: VExists(1)[rotated])
    qed
  qed auto
next
  case (VForall x z vp)
  with VForall(1)[of "v(x := z)"] show ?case
    by (cases \<phi>) (auto intro: SAT_VIO.VForall)
next
  case VOnceOut
  then show ?case by (cases \<phi>) (auto intro: SAT_VIO.VOnceOut)
next
  case (VOnce i li vps)
  then show ?case
  proof (cases \<phi>)
    case (Once I \<phi>)
    {fix k
      define j where j_def: "j \<equiv> case right I of \<infinity> \<Rightarrow> 0 | enat n \<Rightarrow> ETP \<sigma> (\<tau> \<sigma> i - n)"
      assume k_def: "k \<ge> j \<and> k \<le> i \<and> k \<le> LTP \<sigma> (\<tau> \<sigma> i - left I)"
      from VOnce Once j_def have map: "set (map v_at vps) = set [j ..< Suc (LTP_p \<sigma> i I)]"
        by (auto simp: Let_def)
      then have kset: "k \<in> set ([j ..< Suc (LTP_p \<sigma> i I)])" using j_def k_def by auto
      then obtain x where x: "x \<in> set vps"  "v_at x = k" using k_def map
        unfolding set_map set_eq_iff image_iff
        by metis
      then have "VIO \<sigma> v k \<phi>" using VOnce unfolding Once
        by (auto simp: Let_def)
    } note * = this
    show ?thesis
      using VOnce *
      unfolding Once
      by (auto simp: Let_def intro!: SAT_VIO.VOnce)
  qed (auto intro: SAT_VIO.intros)
next
  case (VEventually i hi vps)
  then show ?case
  proof (cases \<phi>)
    case (Eventually I \<phi>)
    obtain n where n_def: "right I = enat n"
      using VEventually
      by (auto simp: Eventually split: enat.splits)
    {fix k
      define j where j_def: "j \<equiv> LTP \<sigma> (\<tau> \<sigma> i + n)"
      assume k_def: "k \<le> j \<and> k \<ge> i \<and> k \<ge> ETP \<sigma> (\<tau> \<sigma> i + left I)"
      from VEventually Eventually j_def have map: "set (map v_at vps) = set [(ETP_f \<sigma> i I) ..< Suc j]"
        by (auto simp: Let_def n_def)
      then have kset: "k \<in> set ([(ETP_f \<sigma> i I) ..< Suc j])" using k_def j_def by auto
      then obtain x where x: "x \<in> set vps" "v_at x = k" using k_def map
        unfolding set_map set_eq_iff image_iff
        by metis
      then have "VIO \<sigma> v k \<phi>" using VEventually unfolding Eventually
        by (auto simp: Let_def n_def)
    } note * = this
    then show ?thesis
      using VEventually
      unfolding Eventually
      by (auto simp: Let_def n_def intro: SAT_VIO.VEventually split: if_splits enat.splits)
  qed(auto intro: SAT_VIO.intros)
next
  case (VHistorically i vp)
  then show ?case
  proof (cases \<phi>)
    case (Historically I \<phi>)
    show ?thesis
      using VHistorically
      unfolding Historically
      by (intro SAT_VIO.VHistorically[of "v_at vp"]) (auto simp: Let_def)
  qed auto
next
  case (VAlways i vp)
  then show ?case
  proof (cases \<phi>)
    case (Always I \<phi>)
    show ?thesis
      using VAlways
      unfolding Always
      by (intro SAT_VIO.VAlways[of _ "v_at vp"]) (auto simp: Let_def)
  qed auto
next
  case VNext
  then show ?case by (cases \<phi>) (auto intro: SAT_VIO.VNext)
next
  case VNextOutR
  then show ?case by (cases \<phi>) (auto intro: SAT_VIO.VNextOutR)
next
  case VNextOutL
  then show ?case by (cases \<phi>) (auto intro: SAT_VIO.VNextOutL)
next
  case VPrev
  then show ?case by (cases \<phi>) (auto intro: SAT_VIO.VPrev)
next
  case VPrevOutR
  then show ?case by (cases \<phi>) (auto intro: SAT_VIO.VPrevOutR)
next
  case VPrevOutL
  then show ?case by (cases \<phi>) (auto intro: SAT_VIO.VPrevOutL)
next
  case VPrevZ
  then show ?case by (cases \<phi>) (auto intro: SAT_VIO.VPrevZ)
next
  case VSinceOut
  then show ?case by (cases \<phi>) (auto intro: SAT_VIO.VSinceOut)
next
  case (VSince i vp vps)
  then show ?case
  proof (cases \<phi>)
    case (Since \<phi> I \<psi>)
    {fix k
      assume k_def: "k \<ge> v_at vp \<and> k \<le> i \<and> k \<le> LTP \<sigma> (\<tau> \<sigma> i - left I)"
      from VSince Since have map: "set (map v_at vps) = set ([(v_at vp) ..< Suc (LTP_p \<sigma> i I)])"
        by (auto simp: Let_def)
      then have kset: "k \<in> set ([(v_at vp) ..< Suc (LTP_p \<sigma> i I)])" using k_def by auto
      then obtain x where x: "x \<in> set vps" "v_at x = k" using k_def map kset
        unfolding set_map set_eq_iff image_iff
        by metis
      then have "VIO \<sigma> v k \<psi>" using VSince unfolding Since
        by (auto simp: Let_def)
    } note * = this
    show ?thesis
      using VSince *
      unfolding Since
      by (auto simp: Let_def split: enat.splits if_splits
          intro!: SAT_VIO.VSince[of _ i "v_at vp"])
  qed (auto intro: SAT_VIO.intros)
next
  case (VUntil i vps vp)
  then show ?case
  proof (cases \<phi>)
    case (Until \<phi> I \<psi>)
    {fix k
      assume k_def: "k \<le> v_at vp \<and> k \<ge> i \<and> k \<ge> ETP \<sigma> (\<tau> \<sigma> i + left I)"
      from VUntil Until have map: "set (map v_at vps) = set [(ETP_f \<sigma> i I) ..< Suc (v_at vp)]"
        by (auto simp: Let_def)
      then have kset: "k \<in> set ([(ETP_f \<sigma> i I) ..< Suc (v_at vp)])" using k_def by auto
      then obtain x where x: "x \<in> set vps" "v_at x = k" using k_def map kset
        unfolding set_map set_eq_iff image_iff
        by metis
      then have "VIO \<sigma> v k \<psi>" using VUntil unfolding Until
        by (auto simp: Let_def)
    } note * = this
    then show ?thesis
      using VUntil
      unfolding Until
      by (auto simp: Let_def split: enat.splits if_splits
          intro!: SAT_VIO.VUntil)
  qed(auto intro: SAT_VIO.intros)
next
  case (VSinceInf i li vps)
  then show ?case
  proof (cases \<phi>)
    case (Since \<phi> I \<psi>)
    {fix k
      define j where j_def: "j \<equiv> case right I of \<infinity> \<Rightarrow> 0 | enat n \<Rightarrow> ETP \<sigma> (\<tau> \<sigma> i - n)"
      assume k_def: "k \<ge> j \<and> k \<le> i \<and> k \<le> LTP \<sigma> (\<tau> \<sigma> i - left I)"
      from VSinceInf Since j_def have map: "set (map v_at vps) = set [j ..< Suc (LTP_p \<sigma> i I)]"
        by (auto simp: Let_def)
      then have kset: "k \<in> set ([j ..< Suc (LTP_p \<sigma> i I)])" using j_def k_def by auto
      then obtain x where x: "x \<in> set vps"  "v_at x = k" using k_def map
        unfolding set_map set_eq_iff image_iff
        by metis
      then have "VIO \<sigma> v k \<psi>" using VSinceInf unfolding Since
        by (auto simp: Let_def)
    } note * = this
    show ?thesis
      using VSinceInf *
      unfolding Since
      by (auto simp: Let_def intro!: SAT_VIO.VSinceInf)
  qed (auto intro: SAT_VIO.intros)
next
  case (VUntilInf i hi vps)
  then show ?case
  proof (cases \<phi>)
    case (Until \<phi> I \<psi>)
    obtain n where n_def: "right I = enat n"
      using VUntilInf
      by (auto simp: Until split: enat.splits)
    {fix k
      define j where j_def: "j \<equiv> LTP \<sigma> (\<tau> \<sigma> i + n)"
      assume k_def: "k \<le> j \<and> k \<ge> i \<and> k \<ge> ETP \<sigma> (\<tau> \<sigma> i + left I)"
      from VUntilInf Until j_def have map: "set (map v_at vps) = set [(ETP_f \<sigma> i I) ..< Suc j]"
        by (auto simp: Let_def n_def)
      then have kset: "k \<in> set ([(ETP_f \<sigma> i I) ..< Suc j])" using k_def j_def by auto
      then obtain x where x: "x \<in> set vps" "v_at x = k" using k_def map
        unfolding set_map set_eq_iff image_iff
        by metis
      then have "VIO \<sigma> v k \<psi>" using VUntilInf unfolding Until
        by (auto simp: Let_def n_def)
    } note * = this
    then show ?thesis
      using VUntilInf
      unfolding Until
      by (auto simp: Let_def n_def intro: SAT_VIO.VUntilInf split: if_splits enat.splits)
  qed(auto intro: SAT_VIO.intros)
qed

definition "compatible X vs v \<longleftrightarrow> (\<forall>x\<in>X. v x \<in> vs x)"

definition "compatible_vals X vs = {v. \<forall>x \<in> X. v x \<in> vs x}"

lemma compatible_alt:
  "compatible X vs v \<longleftrightarrow> v \<in> compatible_vals X vs"
  by (auto simp: compatible_def compatible_vals_def)

lemma compatible_empty_iff: "compatible {} vs v \<longleftrightarrow> True"
  by (auto simp: compatible_def)

lemma compatible_vals_empty_eq: "compatible_vals {} vs = UNIV"
  by (auto simp: compatible_vals_def)

lemma compatible_union_iff:
  "compatible (X \<union> Y) vs v \<longleftrightarrow> compatible X vs v \<and> compatible Y vs v"
  by (auto simp: compatible_def)

lemma compatible_vals_union_eq:
  "compatible_vals (X \<union> Y) vs = compatible_vals X vs \<inter> compatible_vals Y vs"
  by (auto simp: compatible_vals_def)

lemma compatible_antimono:
  "compatible X vs v \<Longrightarrow> Y \<subseteq> X \<Longrightarrow> compatible Y vs v"
  by (auto simp: compatible_def)

lemma compatible_vals_antimono:
  "Y \<subseteq> X \<Longrightarrow> compatible_vals X vs \<subseteq> compatible_vals Y vs"
  by (auto simp: compatible_vals_def)

lemma compatible_extensible:
  "(\<forall>x. vs x \<noteq> {}) \<Longrightarrow> compatible X vs v \<Longrightarrow> X \<subseteq> Y \<Longrightarrow> \<exists>v'. compatible Y vs v' \<and> (\<forall>x\<in>X. v x = v' x)"
  using some_in_eq[of "vs _"] by (auto simp: override_on_def compatible_def
      intro: exI[where x="override_on v (\<lambda>x. SOME y. y \<in> vs x) (Y-X)"])

lemmas compatible_vals_extensible = compatible_extensible[unfolded compatible_alt]

primrec mk_values :: "(('n, 'd) trm \<times> 'a set) list \<Rightarrow> 'a list set"
  where "mk_values [] = {[]}"
  | "mk_values (T # Ts) = (case T of
      (\<^bold>v x, X) \<Rightarrow>
        let terms = map fst Ts in
        if \<^bold>v x \<in> set terms then
          let fst_pos = hd (positions terms (\<^bold>v x)) in (\<lambda>xs. (xs ! fst_pos) # xs) ` (mk_values Ts)
        else set_Cons X (mk_values Ts)
    | (\<^bold>c a, X) \<Rightarrow> set_Cons X (mk_values Ts))"

lemma mk_values_nempty:
  "{} \<notin> set (map snd tXs) \<Longrightarrow> mk_values tXs \<noteq> {}"
  by (induct tXs)
    (auto simp: set_Cons_def image_iff split: trm.splits if_splits)

lemma mk_values_not_Nil:
  "{} \<notin> set (map snd tXs) \<Longrightarrow> tXs \<noteq> [] \<Longrightarrow> vs \<in> mk_values tXs \<Longrightarrow> vs \<noteq> []"
  by (induct tXs)
    (auto simp: set_Cons_def image_iff split: trm.splits if_splits)

lemma mk_values_nth_cong: "\<^bold>v x \<in> set (map fst tXs) \<Longrightarrow>
  n \<in> set (positions (map fst tXs) (\<^bold>v x)) \<Longrightarrow>
  m \<in> set (positions (map fst tXs) (\<^bold>v x)) \<Longrightarrow>
  vs \<in> mk_values tXs \<Longrightarrow>
  vs ! n = vs ! m"
proof (induct tXs arbitrary: n m vs x)
  case (Cons tX tXs)
  show ?case
  proof (cases n)
    case 0
    then show ?thesis
    proof (cases m)
      case (Suc m')
      with 0 show ?thesis
        using Cons(2-) Cons.hyps(1)[of x m' _ "tl vs"] positions_eq_nil_iff[of "map fst tXs" "trm.Var x"]
        by (fastforce split: if_splits simp: in_set_conv_nth
            Let_def nth_Cons' gr0_conv_Suc neq_Nil_conv)
    qed simp
  next
    case n: (Suc n')
    then show ?thesis
    proof (cases m)
      case 0
      with n show ?thesis
        using Cons(2-) Cons.hyps(1)[of x _ n' "tl vs"] positions_eq_nil_iff[of "map fst tXs" "trm.Var x"]
        by (fastforce split: if_splits simp: in_set_conv_nth
            Let_def nth_Cons' gr0_conv_Suc neq_Nil_conv)
    next
      case (Suc m')
      with n show ?thesis
        using Cons(1)[of x n' m' "tl vs"] Cons(2-)
        by (fastforce simp: set_Cons_def set_positions_eq split: trm.splits if_splits)
    qed
  qed
qed simp

definition "mk_values_subset p tXs X
  \<longleftrightarrow> (let (fintXs, inftXs) = partition (\<lambda>tX. finite (snd tX)) tXs in
  if inftXs = [] then {p} \<times> mk_values tXs \<subseteq> X
  else let inf_dups = filter (\<lambda>tX. (fst tX) \<in> set (map fst fintXs)) inftXs in
    if inf_dups = [] then (if finite X then False else Code.abort STR ''subset on infinite subset'' (\<lambda>_. {p} \<times> mk_values tXs \<subseteq> X))
    else if list_all (\<lambda>tX. Max (set (positions tXs tX)) < Max (set (positions (map fst tXs) (fst tX)))) inf_dups
      then {p} \<times> mk_values tXs \<subseteq> X
      else (if finite X then False else Code.abort STR ''subset on infinite subset'' (\<lambda>_. {p} \<times> mk_values tXs \<subseteq> X)))"

lemma mk_values_nemptyI: "\<forall>tX \<in> set tXs. snd tX \<noteq> {} \<Longrightarrow> mk_values tXs \<noteq> {}"
  by (induct tXs)
    (auto simp: Let_def set_Cons_eq split: prod.splits trm.splits)

lemma infinite_mk_values1: "\<forall>tX \<in> set tXs. snd tX \<noteq> {} \<Longrightarrow> tY \<in> set tXs \<Longrightarrow>
  \<forall>Y. (fst tY, Y) \<in> set tXs \<longrightarrow> infinite Y \<Longrightarrow> infinite (mk_values tXs)"
proof (induct tXs arbitrary: tY)
  case (Cons tX tXs)
  show ?case
    unfolding Let_def image_iff mk_values.simps split_beta
      trm.split[of infinite] if_split[of infinite]
  proof (safe, goal_cases var_in var_out const)
    case (var_in x)
    hence "\<forall>tX\<in>set tXs. snd tX \<noteq> {}"
      by (simp add: Cons.prems(1))
    moreover have "\<forall>Z. (trm.Var x, Z) \<in> set tXs \<longrightarrow> infinite Z"
      using Cons.prems(2,3) var_in
      by (cases "tY \<in> set tXs"; clarsimp)
        (metis (no_types, lifting) Cons.hyps Cons.prems(1)
          finite_imageD inj_on_def list.inject list.set_intros(2))
    ultimately have "infinite (mk_values tXs)"
      using Cons.hyps var_in
      by auto
    moreover have "inj (\<lambda>xs. xs ! hd (positions (map fst tXs) (trm.Var x)) # xs)"
      by (clarsimp simp: inj_on_def)
    ultimately show ?case
      using var_in(3) finite_imageD inj_on_subset
      by fastforce
  next
    case (var_out x)
    hence "infinite (snd tX)"
      using Cons
      by (metis infinite_set_ConsI(2) insert_iff list.simps(15) prod.collapse)
    moreover have "mk_values tXs \<noteq> {}"
      using Cons.prems
      by (auto intro!: mk_values_nemptyI)
    then show ?case
      using Cons var_out infinite_set_ConsI(1)[OF \<open>mk_values tXs \<noteq> {}\<close> \<open>infinite (snd tX)\<close>]
      by auto
  next
    case (const c)
    hence "infinite (snd tX)"
      using Cons
      by (metis infinite_set_ConsI(2) insert_iff list.simps(15) prod.collapse)
    moreover have "mk_values tXs \<noteq> {}"
      using Cons.prems
      by (auto intro!: mk_values_nemptyI)
    then show ?case
      using Cons const infinite_set_ConsI(1)[OF \<open>mk_values tXs \<noteq> {}\<close> \<open>infinite (snd tX)\<close>]
      by auto
  qed
qed simp

lemma infinite_mk_values2: "\<forall>tX\<in>set tXs. snd tX \<noteq> {} \<Longrightarrow>
  tY \<in> set tXs \<Longrightarrow> infinite (snd tY) \<Longrightarrow>
  Max (set (positions tXs tY)) \<ge> Max (set (positions (map fst tXs) (fst tY))) \<Longrightarrow>
  infinite (mk_values tXs)"
proof (induct tXs arbitrary: tY)
  case (Cons tX tXs)
  hence obs1: "\<forall>tX\<in>set tXs. snd tX \<noteq> {}"
    by (simp add: Cons.prems(1))
  note IH = Cons.hyps[OF obs1 _ \<open>infinite (snd tY)\<close>]
  have obs2: "tY \<in> set tXs \<Longrightarrow>
    Max (set (positions (map fst tXs) (fst tY))) \<le> Max (set (positions tXs tY))"
    using Cons.prems(4) unfolding list.map
    by (metis Max_set_positions_Cons_tl Suc_le_mono positions_eq_nil_iff set_empty2 subset_empty subset_positions_map_fst)
  show ?case
    unfolding Let_def image_iff mk_values.simps split_beta
      trm.split[of infinite] if_split[of infinite]
  proof (safe, goal_cases var_in var_out const)
    case (var_in x)
    then show ?case
    proof (cases "tY \<in> set tXs")
      case True
      hence "infinite ((\<lambda>Xs. Xs ! hd (positions (map fst tXs) (trm.Var x)) # Xs) ` mk_values tXs)"
        using IH[OF True obs2[OF True]] finite_imageD inj_on_def by blast
      then show "False"
        using var_in by blast
    next
      case False
      have "Max (set (positions (map fst (tX # tXs)) (fst tY)))
      = Suc (Max (set (positions (map fst tXs) (fst tY))))"
        using Cons.prems var_in
        by (simp only: list.map(2))
          (subst Max_set_positions_Cons_tl; force simp: image_iff)
      moreover have "tY \<notin> set tXs \<Longrightarrow> Max (set (positions (tX # tXs) tY)) = (0::nat)"
        using Cons.prems Max_set_positions_Cons_hd by fastforce
      ultimately show "False"
        using Cons.prems(4) False
        by linarith
    qed
  next
    case (var_out x)
    then show ?case
    proof (cases "tY \<in> set tXs")
      case True
      hence "infinite (mk_values tXs)"
        using IH obs2 by blast
      hence "infinite (set_Cons (snd tX) (mk_values tXs))"
        by (metis Cons.prems(1) infinite_set_ConsI(2) list.set_intros(1))
      then show "False"
        using var_out by blast
    next
      case False
      hence "snd tY = snd tX" and "infinite (snd tX)"
        using var_out Cons.prems
        by auto
      hence "infinite (set_Cons (snd tX) (mk_values tXs))"
        by (simp add: infinite_set_ConsI(1) mk_values_nemptyI obs1)
      then show "False"
        using var_out by blast
    qed
  next
    case (const c)
    then show ?case
    proof (cases "tY \<in> set tXs")
      case True
      hence "infinite (mk_values tXs)"
        using IH obs2 by blast
      hence "infinite (set_Cons (snd tX) (mk_values tXs))"
        by (metis Cons.prems(1) infinite_set_ConsI(2) list.set_intros(1))
      then show "False"
        using const by blast
    next
      case False
      hence "infinite (set_Cons (snd tX) (mk_values tXs))"
        using const Cons.prems
        by (simp add: infinite_set_ConsI(1) mk_values_nemptyI obs1)
      then show "False"
        using const by blast
    qed
  qed
qed simp

lemma mk_values_subset_iff: "\<forall>tX \<in> set tXs. snd tX \<noteq> {} \<Longrightarrow>
   mk_values_subset p tXs X \<longleftrightarrow> {p} \<times> mk_values tXs \<subseteq> X"
  unfolding mk_values_subset_def image_iff Let_def comp_def split_beta if_split_eq1
    partition_filter1 partition_filter2 o_def set_map set_filter filter_filter bex_simps
proof safe
  assume "\<forall>tX\<in>set tXs. snd tX \<noteq> {}" and "finite X"
    and filter1: "filter (\<lambda>xy. infinite (snd xy) \<and> (\<exists>ab. (ab \<in> set tXs \<and> finite (snd ab)) \<and> fst xy = fst ab)) tXs = []"
    and filter2: "filter (\<lambda>x. infinite (snd x)) tXs \<noteq> []"
  then obtain tY where "tY \<in> set tXs" and "infinite (snd tY)"
    by (meson filter_False)
  moreover have "\<forall>Y. (fst tY, Y) \<in> set tXs \<longrightarrow> infinite Y"
    using filter1 calculation
    by (auto simp: filter_empty_conv)
  ultimately have "infinite (mk_values tXs)"
    using infinite_mk_values1[OF \<open>\<forall>tX\<in>set tXs. snd tX \<noteq> {}\<close>]
    by auto
  hence "infinite ({p} \<times> mk_values tXs)"
    using finite_cartesian_productD2 by auto
  thus "{p} \<times> mk_values tXs \<subseteq> X \<Longrightarrow> False"
    using \<open>finite X\<close>
    by (simp add: finite_subset)
next
  assume "\<forall>tX\<in>set tXs. snd tX \<noteq> {}"
    and "finite X"
    and ex_dupl_inf: "\<not> list_all (\<lambda>tX. Max (set (positions tXs tX))
    < Max (set (positions (map fst tXs) (fst tX))))
        (filter (\<lambda>xy. infinite (snd xy) \<and> (\<exists>ab. (ab \<in> set tXs \<and> finite (snd ab)) \<and> fst xy = fst ab)) tXs)"
    and filter: "filter (\<lambda>x. infinite (snd x)) tXs \<noteq> []"
  then obtain tY and Z where "tY \<in> set tXs"
    and "infinite (snd tY)"
    and "(fst tY, Z) \<in> set tXs"
    and "finite Z"
    and "Max (set (positions tXs tY)) \<ge> Max (set (positions (map fst tXs) (fst tY)))"
    by (auto simp: list_all_iff)
  hence "infinite (mk_values tXs)"
    using infinite_mk_values2[OF \<open>\<forall>tX\<in>set tXs. snd tX \<noteq> {}\<close> \<open>tY \<in> set tXs\<close>]
    by auto
  hence "infinite ({p} \<times> mk_values tXs)"
    using finite_cartesian_productD2 by auto
  thus "{p} \<times> mk_values tXs \<subseteq> X \<Longrightarrow> False"
    using \<open>finite X\<close>
    by (simp add: finite_subset)
qed auto

lemma mk_values_sound: "cs \<in> mk_values (vs\<^bold>\<lbrace>ts\<^bold>\<rbrace>) \<Longrightarrow>
  \<exists>v\<in>compatible_vals (fv (r \<dagger> ts)) vs. cs = v\<^bold>\<lbrakk>ts\<^bold>\<rbrakk>"
proof (induct ts arbitrary: cs vs)
  case (Cons t ts)
  show ?case
  proof(cases t)
    case (Var x)
    let ?Ts = "vs\<^bold>\<lbrace>ts\<^bold>\<rbrace>"
    have "vs\<^bold>\<lbrace>(t # ts)\<^bold>\<rbrace> = (\<^bold>v x, vs x) # ?Ts"
      using Var by (simp add: eval_trms_set_def)
    show ?thesis
    proof (cases "\<^bold>v x \<in> set ts")
      case True
      then obtain n where n_in: "n \<in> set (positions ts (\<^bold>v x))"
        and nth_n: "ts ! n = \<^bold>v x"
        by (meson fst_pos_in_positions nth_fst_pos)
      hence n_in': "n \<in> set (positions (map fst ?Ts) (\<^bold>v x))"
        by (induct ts arbitrary: n)
          (auto simp: eval_trms_set_def split: if_splits)
      have key: "\<^bold>v x \<in> set (map fst ?Ts)"
        using True by (induct ts)
          (auto simp: eval_trms_set_def)
      then obtain a as
        where as_head: "as ! (hd (positions (map fst ?Ts) (\<^bold>v x))) = a"
          and as_tail: "as \<in> mk_values ?Ts"
          and as_shape: "cs = a # as"
        using Cons(2)
        by (clarsimp simp add: eval_trms_set_def Var image_iff)
      obtain v where v_hyps: "v \<in> compatible_vals (fv (r \<dagger> ts)) vs"
        "as = v\<^bold>\<lbrakk>ts\<^bold>\<rbrakk>"
        using Cons(1)[OF as_tail] by blast
      hence as'_nth: "as ! n = v x"
        using nth_n positions_length[OF n_in]
        by (simp add: eval_trms_def)
      have evals_neq_Nil: "?Ts \<noteq> []"
        using key by auto
      moreover have "positions (map fst ?Ts) (\<^bold>v x) \<noteq> []"
        using positions_eq_nil_iff[of "map fst ?Ts" "\<^bold>v x"] key
        by fastforce
      ultimately have as_hyp: "a = as ! n"
        using mk_values_nth_cong[OF key hd_in_set n_in' as_tail] as_head  by blast
      thus ?thesis
        using Var as_shape True v_hyps as'_nth
        by (auto simp: compatible_vals_def eval_trms_def intro!: exI[of _ v])
    next
      case False
      hence *: "\<^bold>v x \<notin> set (map fst ?Ts)"
      proof (induct ts arbitrary: x)
        case (Cons a ts)
        then show ?case
          by (cases a) (auto simp: eval_trms_set_def)
      qed (simp add: eval_trms_set_def)
      from Cons(2) False show ?thesis
        unfolding set_Cons_def eval_trms_set_def Let_def list.simps Var
          *[THEN eq_False[THEN iffD2], unfolded eval_trms_set_def] if_False
          mk_values.simps eval_trm_set.simps prod.case trm.case mem_Collect_eq
      proof (elim exE conjE, goal_cases)
        case (1 a as)
        with Cons(1)[of as vs] obtain v where "v \<in> compatible_vals (fv (r \<dagger> ts)) vs" "as = v\<^bold>\<lbrakk>ts\<^bold>\<rbrakk>"
          by (auto simp: eval_trms_set_def)
        with 1 show ?case
          by (auto simp: eval_trms_set_def eval_trms_def compatible_vals_def in_fv_trm_conv
            intro!: exI[of _ "v(x := a)"] eval_trm_fv_cong)
      qed
    qed
  next
    case (Const c)
    then show ?thesis
      using Cons(1)[of _ vs] Cons(2)
      by (auto simp: eval_trms_set_def set_Cons_def
          eval_trms_def compatible_def)
  qed
qed (simp add: eval_trms_set_def eval_trms_def compatible_vals_def)

lemma fst_eval_trm_set[simp]:
  "fst (vs\<lbrace>t\<rbrace>) = t"
  by (cases t; clarsimp)

lemma mk_values_complete: "cs = v\<^bold>\<lbrakk>ts\<^bold>\<rbrakk> \<Longrightarrow>
  v \<in> compatible_vals (fv (r \<dagger> ts)) vs \<Longrightarrow>
  cs \<in> mk_values (vs\<^bold>\<lbrace>ts\<^bold>\<rbrace>)"
proof (induct ts arbitrary: v cs vs)
  case (Cons t ts)
  then obtain a as
    where a_def: "a = v\<lbrakk>t\<rbrakk>"
      and as_def: "as = v\<^bold>\<lbrakk>ts\<^bold>\<rbrakk>"
      and cs_cons: "cs = a # as"
    by (auto simp: eval_trms_def)
  have compat_v_vs: "v \<in> compatible_vals (fv (r \<dagger> ts)) vs"
    using Cons.prems
    by (auto simp: compatible_vals_def)
  hence mk_values_ts: "as \<in> mk_values (vs\<^bold>\<lbrace>ts\<^bold>\<rbrace>)"
    using Cons.hyps[OF as_def]
    unfolding eval_trms_set_def by blast
  show ?case
  proof (cases "t")
    case (Var x)
    then show ?thesis
    proof (cases "\<^bold>v x \<in> set ts")
      case True
      then obtain n
        where n_head: "n = hd (positions ts (\<^bold>v x))"
          and n_in: "n \<in> set (positions ts (\<^bold>v x))"
          and nth_n: "ts ! n = \<^bold>v x"
        by (simp_all add: hd_positions_eq_fst_pos nth_fst_pos fst_pos_in_positions)
      hence n_in': "n = hd (positions (map fst (vs\<^bold>\<lbrace>ts\<^bold>\<rbrace>)) (\<^bold>v x))"
        by (clarsimp simp: eval_trms_set_def o_def)
      moreover have "as ! n = a"
        using a_def as_def nth_n Var n_in True positions_length
        by (fastforce simp: eval_trms_def)
      moreover have "\<^bold>v x \<in> set (map fst (vs\<^bold>\<lbrace>ts\<^bold>\<rbrace>))"
        using True by (induct ts)
          (auto simp: eval_trms_set_def)
      ultimately show ?thesis
        using mk_values_ts cs_cons
        by (clarsimp simp: eval_trms_set_def Var image_iff)
    next
      case False
      then show ?thesis
        using Var cs_cons mk_values_ts Cons.prems a_def
        by (clarsimp simp: eval_trms_set_def image_iff
            set_Cons_def compatible_vals_def split: trm.splits)
    qed
  next
    case (Const a)
    then show ?thesis
      using cs_cons mk_values_ts Cons.prems a_def
      by (clarsimp simp: eval_trms_set_def image_iff
          set_Cons_def compatible_vals_def split: trm.splits)
  qed
qed (simp add: compatible_vals_def
    eval_trms_set_def eval_trms_def)

definition "mk_values_subset_Compl r vs ts i = ({r} \<times> mk_values (vs\<^bold>\<lbrace>ts\<^bold>\<rbrace>) \<subseteq> - \<Gamma> \<sigma> i)"

fun check_values where
  "check_values _ _ _ None = None"
| "check_values vs (\<^bold>c c # ts) (u # us) f = (if c = u then check_values vs ts us f else None)"
| "check_values vs (\<^bold>v x # ts) (u # us) (Some v) = (if u \<in> vs x \<and> (v x = Some u \<or> v x = None) then check_values vs ts us (Some (v(x \<mapsto> u))) else None)"
| "check_values vs [] [] f = f"
| "check_values _ _ _ _ = None"

lemma mk_values_alt:
  "mk_values (vs\<^bold>\<lbrace>ts\<^bold>\<rbrace>) =
   {cs. \<exists>v\<in>compatible_vals (\<Union>(fv_trm ` set ts)) vs. cs = v\<^bold>\<lbrakk>ts\<^bold>\<rbrakk>}"
  by (auto dest!: mk_values_sound intro: mk_values_complete)

lemma check_values_neq_NoneI:
  assumes "v \<in> compatible_vals (\<Union> (fv_trm ` set ts) - dom f) vs" "\<And>x y. f x = Some y \<Longrightarrow> y \<in> vs x"
  shows "check_values vs ts ((\<lambda>x. case f x of None \<Rightarrow> v x | Some y \<Rightarrow> y)\<^bold>\<lbrakk>ts\<^bold>\<rbrakk>) (Some f) \<noteq> None"
  using assms
proof (induct ts arbitrary: f)
  case (Cons t ts)
  then show ?case
  proof (cases t)
    case (Var x)
    show ?thesis
    proof (cases "f x")
      case None
      with Cons(2) Var have v_in[simp]: "v x \<in> vs x"
        by (auto simp: compatible_vals_def)
      from Cons(2) have "v \<in> compatible_vals (\<Union> (fv_trm ` set ts) - dom (f(x \<mapsto> v x))) vs"
        by (auto simp: compatible_vals_def)
      then have "check_values vs ts
        ((\<lambda>z. case (f(x \<mapsto> v x)) z of None \<Rightarrow> v z | Some y \<Rightarrow> y)\<^bold>\<lbrakk>ts\<^bold>\<rbrakk>)
        (Some (f(x \<mapsto> v x))) \<noteq> None"
        using Cons(3) None Var
        by (intro Cons(1)) (auto simp: compatible_vals_def split: if_splits)
      then show ?thesis
        by (elim eq_neq_eq_imp_neq[OF _ _ refl, rotated])
          (auto simp add: eval_trms_def compatible_vals_def Var None split: if_splits option.splits
            intro!: arg_cong2[of _ _ _ _ "check_values vs ts"] eval_trm_fv_cong)
    next
      case (Some y)
      with Cons(1)[of f] Cons(2-) Var fun_upd_triv[of f x] show ?thesis
        by (auto simp: domI eval_trms_def compatible_vals_def split: option.splits)
    qed
  next
    case (Const c)
    with Cons show ?thesis
      by (auto simp: eval_trms_def compatible_vals_def split: option.splits)
  qed
qed (simp add: eval_trms_def)

lemma check_values_eq_NoneI:
  "\<forall>v\<in>compatible_vals (\<Union> (fv_trm ` set ts) - dom f) vs. us \<noteq> (\<lambda>x. case f x of None \<Rightarrow> v x | Some y \<Rightarrow> y)\<^bold>\<lbrakk>ts\<^bold>\<rbrakk> \<Longrightarrow>
  check_values vs ts us (Some f) = None"
proof (induct vs ts us "Some f" arbitrary: f rule: check_values.induct)
  case (3 vs x ts u us v)
  show ?case
    unfolding check_values.simps if_split_eq1 simp_thms
  proof (intro impI 3(1), safe, goal_cases)
    case (1 v')
    with 3(2) show ?case
      by (auto simp: insert_dom domI eval_trms_def intro!: eval_trm_fv_cong split: if_splits dest!: bspec[of _ _ "v'"])
  next
    case (2 v')
    with 3(2) show ?case
      by (auto simp: insert_dom domI compatible_vals_def eval_trms_def intro!: eval_trm_fv_cong split: if_splits option.splits dest!: spec[of _ "v'(x := u)"])
  qed
qed (auto simp: compatible_vals_def eval_trms_def)

lemma mk_values_subset_Compl_code[code]:
  "mk_values_subset_Compl r vs ts i = (\<forall>(q, us) \<in> \<Gamma> \<sigma> i. q \<noteq> r \<or> check_values vs ts us (Some Map.empty) = None)"
  unfolding mk_values_subset_Compl_def eval_trms_set_def[symmetric] mk_values_alt
proof (safe, goal_cases)
  case (1 _ us y)
  then show ?case
    by (auto simp: subset_eq check_values_eq_NoneI[where f=Map.empty, simplified] dest!: spec[of _ us])
qed (auto simp: subset_eq  dest!: check_values_neq_NoneI[where f=Map.empty, simplified])

subsection \<open>Executable Variant of the Checker\<close>

fun s_check_exec :: "('n, 'd) envset \<Rightarrow> ('n, 'd) formula \<Rightarrow> ('n, 'd) sproof \<Rightarrow> bool"
and v_check_exec :: "('n, 'd) envset \<Rightarrow> ('n, 'd) formula \<Rightarrow> ('n, 'd) vproof \<Rightarrow> bool" where
  "s_check_exec vs f p = (case (f, p) of
    (\<top>, STT i) \<Rightarrow> True
  | (r \<dagger> ts, SPred i s ts') \<Rightarrow>
    (r = s \<and> ts = ts' \<and> mk_values_subset r (vs\<^bold>\<lbrace>ts\<^bold>\<rbrace>) (\<Gamma> \<sigma> i))
  | (x \<^bold>\<approx> c, SEq_Const i x' c') \<Rightarrow>
    (c = c' \<and> x = x' \<and> vs x = {c})
  | (\<not>\<^sub>F \<phi>, SNeg vp) \<Rightarrow> v_check_exec vs \<phi> vp
  | (\<phi> \<or>\<^sub>F \<psi>, SOrL sp1) \<Rightarrow> s_check_exec vs \<phi> sp1
  | (\<phi> \<or>\<^sub>F \<psi>, SOrR sp2) \<Rightarrow> s_check_exec vs \<psi> sp2
  | (\<phi> \<and>\<^sub>F \<psi>, SAnd sp1 sp2) \<Rightarrow> s_check_exec vs \<phi> sp1 \<and> s_check_exec vs \<psi> sp2 \<and> s_at sp1 = s_at sp2
  | (\<phi> \<longrightarrow>\<^sub>F \<psi>, SImpL vp1) \<Rightarrow> v_check_exec vs \<phi> vp1
  | (\<phi> \<longrightarrow>\<^sub>F \<psi>, SImpR sp2) \<Rightarrow> s_check_exec vs \<psi> sp2
  | (\<phi> \<longleftrightarrow>\<^sub>F \<psi>, SIffSS sp1 sp2) \<Rightarrow> s_check_exec vs \<phi> sp1 \<and> s_check_exec vs \<psi> sp2 \<and> s_at sp1 = s_at sp2
  | (\<phi> \<longleftrightarrow>\<^sub>F \<psi>, SIffVV vp1 vp2) \<Rightarrow> v_check_exec vs \<phi> vp1 \<and> v_check_exec vs \<psi> vp2 \<and> v_at vp1 = v_at vp2
  | (\<exists>\<^sub>Fx.  \<phi>, SExists y val sp) \<Rightarrow> (x = y \<and> s_check_exec (vs (x := {val})) \<phi> sp)
  | (\<forall>\<^sub>Fx.  \<phi>, SForall y sp_part) \<Rightarrow> (let i = s_at (part_hd sp_part)
      in x = y \<and> (\<forall>(sub, sp) \<in> SubsVals sp_part. s_at sp = i \<and> s_check_exec (vs (x := sub)) \<phi> sp))
  | (\<^bold>Y I \<phi>, SPrev sp) \<Rightarrow>
    (let j = s_at sp; i = s_at (SPrev sp) in
    i = j+1 \<and> mem (\<Delta> \<sigma> i) I \<and> s_check_exec vs \<phi> sp)
  | (\<^bold>X I \<phi>, SNext sp) \<Rightarrow>
    (let j = s_at sp; i = s_at (SNext sp) in
    j = i+1 \<and> mem (\<Delta> \<sigma> j) I \<and> s_check_exec vs \<phi> sp)
  | (\<^bold>P I \<phi>, SOnce i sp) \<Rightarrow>
    (let j = s_at sp in
    j \<le> i \<and> mem (\<tau> \<sigma> i - \<tau> \<sigma> j) I \<and> s_check_exec vs \<phi> sp)
  | (\<^bold>F I \<phi>, SEventually i sp) \<Rightarrow>
    (let j = s_at sp in
    j \<ge> i \<and> mem (\<tau> \<sigma> j - \<tau> \<sigma> i) I \<and> s_check_exec vs \<phi> sp)
  | (\<^bold>H I \<phi>, SHistoricallyOut i) \<Rightarrow>
    \<tau> \<sigma> i < \<tau> \<sigma> 0 + left I
  | (\<^bold>H I \<phi>, SHistorically i li sps) \<Rightarrow>
    (li = (case right I of \<infinity> \<Rightarrow> 0 | enat b \<Rightarrow> ETP \<sigma> (\<tau> \<sigma> i - b))
    \<and> \<tau> \<sigma> 0 + left I \<le> \<tau> \<sigma> i
    \<and> map s_at sps = [li ..< (LTP_p \<sigma> i I) + 1]
    \<and> (\<forall>sp \<in> set sps. s_check_exec vs \<phi> sp))
  | (\<^bold>G I \<phi>, SAlways i hi sps) \<Rightarrow>
    (hi = (case right I of enat b \<Rightarrow> LTP_f \<sigma> i b)
    \<and> right I \<noteq> \<infinity>
    \<and> map s_at sps = [(ETP_f \<sigma> i I) ..< hi + 1]
    \<and> (\<forall>sp \<in> set sps. s_check_exec vs \<phi> sp))
  | (\<phi> \<^bold>S I \<psi>, SSince sp2 sp1s) \<Rightarrow>
    (let i = s_at (SSince sp2 sp1s); j = s_at sp2 in
    j \<le> i \<and> mem (\<tau> \<sigma> i - \<tau> \<sigma> j) I
    \<and> map s_at sp1s = [j+1 ..< i+1]
    \<and> s_check_exec vs \<psi> sp2
    \<and> (\<forall>sp1 \<in> set sp1s. s_check_exec vs \<phi> sp1))
  | (\<phi> \<^bold>U I \<psi>, SUntil sp1s sp2) \<Rightarrow>
    (let i = s_at (SUntil sp1s sp2); j = s_at sp2 in
    j \<ge> i \<and> mem (\<tau> \<sigma> j - \<tau> \<sigma> i) I
    \<and> map s_at sp1s = [i ..< j] \<and> s_check_exec vs \<psi> sp2
    \<and> (\<forall>sp1 \<in> set sp1s. s_check_exec vs \<phi> sp1))
  | ( _ , _) \<Rightarrow> False)"
| "v_check_exec vs f p = (case (f, p) of
    (\<bottom>, VFF i) \<Rightarrow> True
  | (r \<dagger> ts, VPred i pred ts') \<Rightarrow>
    (r = pred \<and> ts = ts' \<and> mk_values_subset_Compl r vs ts i)
  | (x \<^bold>\<approx> c, VEq_Const i x' c') \<Rightarrow>
    (c = c' \<and> x = x' \<and> c \<notin> vs x)
  | (\<not>\<^sub>F \<phi>, VNeg sp) \<Rightarrow> s_check_exec vs \<phi> sp
  | (\<phi> \<or>\<^sub>F \<psi>, VOr vp1 vp2) \<Rightarrow> v_check_exec vs \<phi> vp1 \<and> v_check_exec vs \<psi> vp2 \<and> v_at vp1 = v_at vp2
  | (\<phi> \<and>\<^sub>F \<psi>, VAndL vp1) \<Rightarrow> v_check_exec vs \<phi> vp1
  | (\<phi> \<and>\<^sub>F \<psi>, VAndR vp2) \<Rightarrow> v_check_exec vs \<psi> vp2
  | (\<phi> \<longrightarrow>\<^sub>F \<psi>, VImp sp1 vp2) \<Rightarrow> s_check_exec vs \<phi> sp1 \<and> v_check_exec vs \<psi> vp2 \<and> s_at sp1 = v_at vp2
  | (\<phi> \<longleftrightarrow>\<^sub>F \<psi>, VIffSV sp1 vp2) \<Rightarrow> s_check_exec vs \<phi> sp1 \<and> v_check_exec vs \<psi> vp2 \<and> s_at sp1 = v_at vp2
  | (\<phi> \<longleftrightarrow>\<^sub>F \<psi>, VIffVS vp1 sp2) \<Rightarrow> v_check_exec vs \<phi> vp1 \<and> s_check_exec vs \<psi> sp2 \<and> v_at vp1 = s_at sp2
  | (\<exists>\<^sub>Fx.  \<phi>, VExists y vp_part) \<Rightarrow> (let i = v_at (part_hd vp_part)
      in x = y \<and> (\<forall>(sub, vp) \<in> SubsVals vp_part. v_at vp = i \<and> v_check_exec (vs (x := sub)) \<phi> vp))
  | (\<forall>\<^sub>Fx.  \<phi>, VForall y val vp) \<Rightarrow> (x = y \<and> v_check_exec (vs (x := {val})) \<phi> vp)
  | (\<^bold>Y I \<phi>, VPrev vp) \<Rightarrow>
    (let j = v_at vp; i = v_at (VPrev vp) in
    i = j+1 \<and> v_check_exec vs \<phi> vp)
  | (\<^bold>Y I \<phi>, VPrevZ) \<Rightarrow> True
  | (\<^bold>Y I \<phi>, VPrevOutL i) \<Rightarrow>
    i > 0 \<and> \<Delta> \<sigma> i < left I
  | (\<^bold>Y I \<phi>, VPrevOutR i) \<Rightarrow>
    i > 0 \<and> enat (\<Delta> \<sigma> i) > right I
  | (\<^bold>X I \<phi>, VNext vp) \<Rightarrow>
    (let j = v_at vp; i = v_at (VNext vp) in
    j = i+1 \<and> v_check_exec vs \<phi> vp)
  | (\<^bold>X I \<phi>, VNextOutL i) \<Rightarrow>
    \<Delta> \<sigma> (i+1) < left I
  | (\<^bold>X I \<phi>, VNextOutR i) \<Rightarrow>
    enat (\<Delta> \<sigma> (i+1)) > right I
  | (\<^bold>P I \<phi>, VOnceOut i) \<Rightarrow>
    \<tau> \<sigma> i < \<tau> \<sigma> 0 + left I
  | (\<^bold>P I \<phi>, VOnce i li vps) \<Rightarrow>
    (li = (case right I of \<infinity> \<Rightarrow> 0 | enat b \<Rightarrow> ETP_p \<sigma> i b)
    \<and> \<tau> \<sigma> 0 + left I \<le> \<tau> \<sigma> i
    \<and> map v_at vps = [li ..< (LTP_p \<sigma> i I) + 1]
    \<and> (\<forall>vp \<in> set vps. v_check_exec vs \<phi> vp))
  | (\<^bold>F I \<phi>, VEventually i hi vps) \<Rightarrow>
    (hi = (case right I of enat b \<Rightarrow> LTP_f \<sigma> i b) \<and> right I \<noteq> \<infinity>
    \<and> map v_at vps = [(ETP_f \<sigma> i I) ..< hi + 1]
    \<and> (\<forall>vp \<in> set vps. v_check_exec vs \<phi> vp))
  | (\<^bold>H I \<phi>, VHistorically i vp) \<Rightarrow>
    (let j = v_at vp in
    j \<le> i \<and> mem (\<tau> \<sigma> i - \<tau> \<sigma> j) I \<and> v_check_exec vs \<phi> vp)
  | (\<^bold>G I \<phi>, VAlways i vp) \<Rightarrow>
    (let j = v_at vp
    in j \<ge> i \<and> mem (\<tau> \<sigma> j - \<tau> \<sigma> i) I \<and> v_check_exec vs \<phi> vp)
  | (\<phi> \<^bold>S I \<psi>, VSinceOut i) \<Rightarrow>
    \<tau> \<sigma> i < \<tau> \<sigma> 0 + left I
  | (\<phi> \<^bold>S I \<psi>, VSince i vp1 vp2s) \<Rightarrow>
    (let j = v_at vp1 in
    (case right I of \<infinity> \<Rightarrow> True | enat b \<Rightarrow> ETP_p \<sigma> i b \<le> j) \<and> j \<le> i
    \<and> \<tau> \<sigma> 0 + left I \<le> \<tau> \<sigma> i
    \<and> map v_at vp2s = [j ..< (LTP_p \<sigma> i I) + 1] \<and> v_check_exec vs \<phi> vp1
    \<and> (\<forall>vp2 \<in> set vp2s. v_check_exec vs \<psi> vp2))
  | (\<phi> \<^bold>S I \<psi>, VSinceInf i li vp2s) \<Rightarrow>
    (li = (case right I of \<infinity> \<Rightarrow> 0 | enat b \<Rightarrow> ETP_p \<sigma> i b)
    \<and> \<tau> \<sigma> 0 + left I \<le> \<tau> \<sigma> i
    \<and> map v_at vp2s = [li ..< (LTP_p \<sigma> i I) + 1]
    \<and> (\<forall>vp2 \<in> set vp2s. v_check_exec vs \<psi> vp2))
  | (\<phi> \<^bold>U I \<psi>, VUntil i vp2s vp1) \<Rightarrow>
    (let j = v_at vp1 in
    (case right I of \<infinity> \<Rightarrow> True | enat b \<Rightarrow> j < LTP_f \<sigma> i b) \<and> i \<le> j
    \<and> map v_at vp2s = [ETP_f \<sigma> i I ..< j + 1] \<and> v_check_exec vs \<phi> vp1
    \<and> (\<forall>vp2 \<in> set vp2s. v_check_exec vs \<psi> vp2))
  | (\<phi> \<^bold>U I \<psi>, VUntilInf i hi vp2s) \<Rightarrow>
    (hi = (case right I of enat b \<Rightarrow> LTP_f \<sigma> i b) \<and> right I \<noteq> \<infinity>
    \<and> map v_at vp2s = [ETP_f \<sigma> i I ..< hi + 1]
    \<and> (\<forall>vp2 \<in> set vp2s. v_check_exec vs \<psi> vp2))
  | ( _ , _) \<Rightarrow> False)"

declare s_check_exec.simps[simp del] v_check_exec.simps[simp del]
simps_of_case s_check_exec_simps[simp, code]: s_check_exec.simps[unfolded prod.case] (splits: formula.split sproof.split)
simps_of_case v_check_exec_simps[simp, code]: v_check_exec.simps[unfolded prod.case] (splits: formula.split vproof.split)


lemma check_fv_cong:
  assumes "\<forall>x \<in> fv \<phi>. v x = v' x"
  shows "s_check v \<phi> sp \<longleftrightarrow> s_check v' \<phi> sp" "v_check v \<phi> vp \<longleftrightarrow> v_check v' \<phi> vp"
  using assms
proof (induct \<phi> arbitrary: v v' sp vp)
  case TT
  {
    case 1
    then show ?case
      by (cases sp) auto
  next
    case 2
    then show ?case
      by (cases vp) auto
  }
next
  case FF
  {
    case 1
    then show ?case
      by (cases sp) auto
  next
    case 2
    then show ?case
      by (cases vp) auto
  }
next
  case (Pred p ts)
  {
    case 1
    with Pred show ?case using eval_trms_fv_cong[of ts v v']
      by (cases sp) auto
  next
    case 2
    with Pred show ?case using eval_trms_fv_cong[of ts v v']
      by (cases vp) auto
  }
  case (Eq_Const x c)
  {
    case 1
    then show ?case
      by (cases sp) auto
  next
    case 2
    then show ?case
      by (cases vp) auto
  }
next
  case (Neg \<phi>)
  {
    case 1
    with Neg[of v v'] show ?case
      by (cases sp) auto
  next
    case 2
    with Neg[of v v'] show ?case
      by (cases vp) auto
  }
next
  case (Or \<phi>1 \<phi>2)
  {
    case 1
    with Or[of v v'] show ?case
      by (cases sp) auto
  next
    case 2
    with Or[of v v'] show ?case
      by (cases vp) auto
  }
next
  case (And \<phi>1 \<phi>2)
  {
    case 1
    with And[of v v'] show ?case
      by (cases sp) auto
  next
    case 2
    with And[of v v'] show ?case
      by (cases vp) auto
  }
next
  case (Imp \<phi>1 \<phi>2)
  {
    case 1
    with Imp[of v v'] show ?case
      by (cases sp) auto
  next
    case 2
    with Imp[of v v'] show ?case
      by (cases vp) auto
  }
next
  case (Iff \<phi>1 \<phi>2)
  {
    case 1
    with Iff[of v v'] show ?case
      by (cases sp) auto
  next
    case 2
    with Iff[of v v'] show ?case
      by (cases vp) auto
  }
next
  case (Exists x \<phi>)
  {
    case 1
    with Exists[of "v(x := z)" "v'(x := z)" for z] show ?case
      by (cases sp) (auto simp: fun_upd_def)
  next
    case 2
    with Exists[of "v(x := z)" "v'(x := z)" for z] show ?case
      by (cases vp) (auto simp: fun_upd_def)
  }
next
  case (Forall x \<phi>)
  {
    case 1
    with Forall[of "v(x := z)" "v'(x := z)" for z] show ?case
      by (cases sp) (auto simp: fun_upd_def)
  next
    case 2
    with Forall[of "v(x := z)" "v'(x := z)" for z] show ?case
      by (cases vp) (auto simp: fun_upd_def)
  }
next
  case (Prev I \<phi>)
  {
    case 1
    with Prev[of v v'] show ?case
      by (cases sp) auto
  next
    case 2
    with Prev[of v v'] show ?case
      by (cases vp) auto
  }
next
  case (Next I \<phi>)
  {
    case 1
    with Next[of v v'] show ?case
      by (cases sp) auto
  next
    case 2
    with Next[of v v'] show ?case
      by (cases vp) auto
  }
next
  case (Once I \<phi>)
  {
    case 1
    with Once[of v v'] show ?case
      by (cases sp) auto
  next
    case 2
    with Once[of v v'] show ?case
      by (cases vp) auto
  }
next
  case (Historically I \<phi>)
  {
    case 1
    with Historically[of v v'] show ?case
      by (cases sp) auto
  next
    case 2
    with Historically[of v v'] show ?case
      by (cases vp) auto
  }
next
  case (Eventually I \<phi>)
  {
    case 1
    with Eventually[of v v'] show ?case
      by (cases sp) auto
  next
    case 2
    with Eventually[of v v'] show ?case
      by (cases vp) auto
  }
next
  case (Always I \<phi>)
  {
    case 1
    with Always[of v v'] show ?case
      by (cases sp) auto
  next
    case 2
    with Always[of v v'] show ?case
      by (cases vp) auto
  }
next
  case (Since \<phi>1 I \<phi>2)
  {
    case 1
    with Since[of v v'] show ?case
      by (cases sp) auto
  next
    case 2
    with Since[of v v'] show ?case
      by (cases vp) auto
  }
next
  case (Until \<phi>1 I \<phi>2)
  {
    case 1
    with Until[of v v'] show ?case
      by (cases sp) auto
  next
    case 2
    with Until[of v v'] show ?case
      by (cases vp) auto
  }
qed

lemma s_check_fun_upd_notin[simp]:
  "x \<notin> fv \<phi> \<Longrightarrow> s_check (v(x := t)) \<phi> sp = s_check v \<phi> sp"
  by (rule check_fv_cong) auto
lemma v_check_fun_upd_notin[simp]:
  "x \<notin> fv \<phi> \<Longrightarrow> v_check (v(x := t)) \<phi> sp = v_check v \<phi> sp"
  by (rule check_fv_cong) auto

lemma SubsVals_nonempty: "(X, t) \<in> SubsVals part \<Longrightarrow> X \<noteq> {}"
  by transfer (auto simp: partition_on_def image_iff)

lemma compatible_vals_nonemptyI: "\<forall>x. vs x \<noteq> {} \<Longrightarrow> compatible_vals A vs \<noteq> {}"
  by (auto simp: compatible_vals_def intro!: bchoice)

lemma compatible_vals_fun_upd: "compatible_vals A (vs(x := X)) =
  (if x \<in> A then {v \<in> compatible_vals (A - {x}) vs. v x \<in> X} else compatible_vals A vs)"
  unfolding compatible_vals_def
  by auto

lemma fun_upd_in_compatible_vals: "v \<in> compatible_vals (A - {x}) vs \<Longrightarrow> v(x := t) \<in> compatible_vals (A - {x}) vs"
  unfolding compatible_vals_def
  by auto

lemma fun_upd_in_compatible_vals_in: "v \<in> compatible_vals (A - {x}) vs \<Longrightarrow> t \<in> vs x \<Longrightarrow> v(x := t) \<in> compatible_vals A vs"
  unfolding compatible_vals_def
  by auto

lemma fun_upd_in_compatible_vals_notin: "x \<notin> A \<Longrightarrow> v \<in> compatible_vals A vs \<Longrightarrow> v(x := t) \<in> compatible_vals A vs"
  unfolding compatible_vals_def
  by auto

lemma check_exec_check:
  assumes "\<forall>x. vs x \<noteq> {}"
  shows "s_check_exec vs \<phi> sp \<longleftrightarrow> (\<forall>v \<in> compatible_vals (fv \<phi>) vs. s_check v \<phi> sp)"
    and "v_check_exec vs \<phi> vp \<longleftrightarrow> (\<forall>v \<in> compatible_vals (fv \<phi>) vs. v_check v \<phi> vp)"
  using assms
proof (induct \<phi> arbitrary: vs sp vp)
  case TT
  {
    case 1
    then show ?case using compatible_vals_nonemptyI
      by (cases sp)
        auto
  next
    case 2
    then show ?case using compatible_vals_nonemptyI
      by auto
  }
next
  case FF
  {
    case 1
    then show ?case using compatible_vals_nonemptyI
      by (cases sp)
        auto
  next
    case 2
    then show ?case using compatible_vals_nonemptyI
      by (cases vp)
        auto
  }
next
  case (Pred p ts)
  {
    case 1
    have obs: "\<forall>tX\<in>set (vs\<^bold>\<lbrace>ts\<^bold>\<rbrace>). snd tX \<noteq> {}"
      using \<open>\<forall>x. vs x \<noteq> {}\<close>
    proof (induct ts)
      case (Cons a ts)
      then show ?case
        by (cases a) (auto simp: eval_trms_set_def)
    qed (auto simp: eval_trms_set_def)
    show ?case
      using 1 compatible_vals_nonemptyI[OF 1]
        mk_values_complete[OF refl, of _ p ts vs] mk_values_sound[of _ vs ts p]
      by (cases sp)
        (auto 6 0 simp: mk_values_subset_iff[OF obs] simp del: fv.simps)
  next
    case 2
    then show ?case using compatible_vals_nonemptyI[OF 2]
        mk_values_complete[OF refl, of _ p ts vs] mk_values_sound[of _ vs ts p]
      by (cases vp)
        (auto 6 0 simp: mk_values_subset_Compl_def eval_trms_set_def simp del: fv.simps)
  }
next
  case (Eq_Const x c)
  {
    case 1
    then show ?case
      by (cases sp) (auto simp: compatible_vals_def)
  next
    case 2
    then show ?case
      by (cases vp) (auto simp: compatible_vals_def)
  }
next
  case (Neg \<phi>)
  {
    case 1
    then show ?case
      using Neg.hyps(2) compatible_vals_nonemptyI[OF 1]
      by (cases sp) auto
  next
    case 2
    then show ?case
      using Neg.hyps(1) compatible_vals_nonemptyI[OF 2]
      by (cases vp) auto
  }
next
  case (Or \<phi>1 \<phi>2)
  {
    case 1
    with compatible_vals_nonemptyI[OF 1, of "fv \<phi>1 \<union> fv \<phi>2"] show ?case
    proof (cases sp)
      case (SOrL sp')
      from check_fv_cong(1)[of \<phi>1 _ _ sp'] show ?thesis
        unfolding SOrL s_check_exec_simps s_check_simps fv.simps Or(1)[OF 1, of sp']
        by (metis (mono_tags, lifting) 1 IntE Un_upper1 compatible_vals_extensible compatible_vals_union_eq)
    next
      case (SOrR sp')
      from check_fv_cong(1)[of \<phi>2 _ _ sp'] show ?thesis
        unfolding SOrR s_check_exec_simps s_check_simps fv.simps Or(3)[OF 1, of sp']
        by (metis (mono_tags, lifting) 1 IntE Un_upper2 compatible_vals_extensible compatible_vals_union_eq)
    qed (auto simp: compatible_vals_union_eq)
  next
    case 2
    with compatible_vals_nonemptyI[OF 2, of "fv \<phi>1 \<union> fv \<phi>2"] show ?case
    proof (cases vp)
      case (VOr vp1 vp2)
      from check_fv_cong(2)[of \<phi>1 _ _ vp1] check_fv_cong(2)[of \<phi>2 _ _ vp2] show ?thesis
        unfolding VOr v_check_exec_simps v_check_simps fv.simps ball_conj_distrib
          Or(2)[OF 2, of vp1]  Or(4)[OF 2, of vp2]
          ball_triv_nonempty[OF compatible_vals_nonemptyI[OF 2, of "fv \<phi>1 \<union> fv \<phi>2"]]
      proof (intro arg_cong2[of _ _ _ _ "(\<and>)"] refl, goal_cases \<phi>1 \<phi>2)
        case \<phi>1
        then show ?case
          by (metis (mono_tags, lifting) 2 IntE Un_upper1 compatible_vals_extensible compatible_vals_union_eq)
      next
        case \<phi>2
        then show ?case
          by (metis (mono_tags, lifting) 2 IntE Un_upper2 compatible_vals_extensible compatible_vals_union_eq)
      qed
    qed (auto simp: compatible_vals_union_eq)
  }
next
  case (And \<phi>1 \<phi>2)
  {
    case 1
    with compatible_vals_nonemptyI[OF 1, of "fv \<phi>1 \<union> fv \<phi>2"] show ?case
    proof (cases sp)
      case (SAnd sp1 sp2)
      from check_fv_cong(1)[of \<phi>1 _ _ sp1] check_fv_cong(1)[of \<phi>2 _ _ sp2] show ?thesis
        unfolding SAnd s_check_exec_simps s_check_simps fv.simps ball_conj_distrib
          And(1)[OF 1, of sp1] And(3)[OF 1, of sp2]
          ball_triv_nonempty[OF compatible_vals_nonemptyI[OF 1, of "fv \<phi>1 \<union> fv \<phi>2"]]
      proof (intro arg_cong2[of _ _ _ _ "(\<and>)"] refl, goal_cases \<phi>1 \<phi>2)
        case \<phi>1
        then show ?case
          by (metis (mono_tags, lifting) 1 IntE Un_upper1 compatible_vals_extensible compatible_vals_union_eq)
      next
        case \<phi>2
        then show ?case
          by (metis (mono_tags, lifting) 1 IntE Un_upper2 compatible_vals_extensible compatible_vals_union_eq)
      qed
    qed (auto simp: compatible_vals_union_eq)
  next
    case 2
    with compatible_vals_nonemptyI[OF 2, of "fv \<phi>1 \<union> fv \<phi>2"] show ?case
    proof (cases vp)
      case (VAndL vp')
      from check_fv_cong(2)[of \<phi>1 _ _ vp'] show ?thesis
        unfolding VAndL v_check_exec_simps v_check_simps fv.simps And(2)[OF 2, of vp']
        by (metis (mono_tags, lifting) 2 IntE Un_upper1 compatible_vals_extensible compatible_vals_union_eq)
    next
      case (VAndR vp')
      from check_fv_cong(2)[of \<phi>2 _ _ vp'] show ?thesis
        unfolding VAndR v_check_exec_simps v_check_simps fv.simps And(4)[OF 2, of vp']
        by (metis (mono_tags, lifting) 2 IntE Un_upper2 compatible_vals_extensible compatible_vals_union_eq)
    qed (auto simp: compatible_vals_union_eq)
  }
next
  case (Imp \<phi>1 \<phi>2)
  {
    case 1
    with compatible_vals_nonemptyI[OF 1, of "fv \<phi>1 \<union> fv \<phi>2"] show ?case
    proof (cases sp)
      case (SImpL vp')
      from check_fv_cong(2)[of \<phi>1 _ _ vp'] show ?thesis
        unfolding SImpL s_check_exec_simps s_check_simps fv.simps Imp(2)[OF 1, of vp']
        by (metis (mono_tags, lifting) 1 IntE Un_upper1 compatible_vals_extensible compatible_vals_union_eq)
    next
      case (SImpR sp')
      from check_fv_cong(1)[of \<phi>2 _ _ sp'] show ?thesis
        unfolding SImpR s_check_exec_simps s_check_simps fv.simps Imp(3)[OF 1, of sp']
        by (metis (mono_tags, lifting) 1 IntE Un_upper2 compatible_vals_extensible compatible_vals_union_eq)
    qed (auto simp: compatible_vals_union_eq)
  next
    case 2
    with compatible_vals_nonemptyI[OF 2, of "fv \<phi>1 \<union> fv \<phi>2"] show ?case
    proof (cases vp)
      case (VImp sp1 vp2)
      from check_fv_cong(1)[of \<phi>1 _ _ sp1] check_fv_cong(2)[of \<phi>2 _ _ vp2] show ?thesis
        unfolding VImp v_check_exec_simps v_check_simps fv.simps ball_conj_distrib
          Imp(1)[OF 2, of sp1] Imp(4)[OF 2, of vp2]
          ball_triv_nonempty[OF compatible_vals_nonemptyI[OF 2, of "fv \<phi>1 \<union> fv \<phi>2"]]
      proof (intro arg_cong2[of _ _ _ _ "(\<and>)"] refl, goal_cases \<phi>1 \<phi>2)
        case \<phi>1
        then show ?case
          by (metis (mono_tags, lifting) 2 IntE Un_upper1 compatible_vals_extensible compatible_vals_union_eq)
      next
        case \<phi>2
        then show ?case
          by (metis (mono_tags, lifting) 2 IntE Un_upper2 compatible_vals_extensible compatible_vals_union_eq)
      qed
    qed (auto simp: compatible_vals_union_eq)
  }
next
  case (Iff \<phi>1 \<phi>2)
  {
    case 1
    with compatible_vals_nonemptyI[OF 1, of "fv \<phi>1 \<union> fv \<phi>2"] show ?case
    proof (cases sp)
      case (SIffSS sp1 sp2)
      from check_fv_cong(1)[of \<phi>1 _ _ sp1] check_fv_cong(1)[of \<phi>2 _ _ sp2] show ?thesis
        unfolding SIffSS s_check_exec_simps s_check_simps fv.simps ball_conj_distrib
          Iff(1)[OF 1, of sp1] Iff(3)[OF 1, of sp2]
          ball_triv_nonempty[OF compatible_vals_nonemptyI[OF 1, of "fv \<phi>1 \<union> fv \<phi>2"]]
      proof (intro arg_cong2[of _ _ _ _ "(\<and>)"] refl, goal_cases \<phi>1 \<phi>2)
        case \<phi>1
        then show ?case
          by (metis (mono_tags, lifting) 1 IntE Un_upper1 compatible_vals_extensible compatible_vals_union_eq)
      next
        case \<phi>2
        then show ?case
          by (metis (mono_tags, lifting) 1 IntE Un_upper2 compatible_vals_extensible compatible_vals_union_eq)
      qed
    next
      case (SIffVV vp1 vp2)
      from check_fv_cong(2)[of \<phi>1 _ _ vp1] check_fv_cong(2)[of \<phi>2 _ _ vp2] show ?thesis
        unfolding SIffVV s_check_exec_simps s_check_simps fv.simps ball_conj_distrib
          Iff(2)[OF 1, of vp1] Iff(4)[OF 1, of vp2]
          ball_triv_nonempty[OF compatible_vals_nonemptyI[OF 1, of "fv \<phi>1 \<union> fv \<phi>2"]]
      proof (intro arg_cong2[of _ _ _ _ "(\<and>)"] refl, goal_cases \<phi>1 \<phi>2)
        case \<phi>1
        then show ?case
          by (metis (mono_tags, lifting) 1 IntE Un_upper1 compatible_vals_extensible compatible_vals_union_eq)
      next
        case \<phi>2
        then show ?case
          by (metis (mono_tags, lifting) 1 IntE Un_upper2 compatible_vals_extensible compatible_vals_union_eq)
      qed
    qed (auto simp: compatible_vals_union_eq)
  next
    case 2
    with compatible_vals_nonemptyI[OF 2, of "fv \<phi>1 \<union> fv \<phi>2"] show ?case
    proof (cases vp)
      case (VIffSV sp1 vp2)
      from check_fv_cong(1)[of \<phi>1 _ _ sp1] check_fv_cong(2)[of \<phi>2 _ _ vp2] show ?thesis
        unfolding VIffSV v_check_exec_simps v_check_simps fv.simps ball_conj_distrib
          Iff(1)[OF 2, of sp1] Iff(4)[OF 2, of vp2]
          ball_triv_nonempty[OF compatible_vals_nonemptyI[OF 2, of "fv \<phi>1 \<union> fv \<phi>2"]]
      proof (intro arg_cong2[of _ _ _ _ "(\<and>)"] refl, goal_cases \<phi>1 \<phi>2)
        case \<phi>1
        then show ?case
          by (metis (mono_tags, lifting) 2 IntE Un_upper1 compatible_vals_extensible compatible_vals_union_eq)
      next
        case \<phi>2
        then show ?case
          by (metis (mono_tags, lifting) 2 IntE Un_upper2 compatible_vals_extensible compatible_vals_union_eq)
      qed
    next
      case (VIffVS vp1 sp2)
      from check_fv_cong(2)[of \<phi>1 _ _ vp1] check_fv_cong(1)[of \<phi>2 _ _ sp2] show ?thesis
        unfolding VIffVS v_check_exec_simps v_check_simps fv.simps ball_conj_distrib
          Iff(2)[OF 2, of vp1] Iff(3)[OF 2, of sp2]
          ball_triv_nonempty[OF compatible_vals_nonemptyI[OF 2, of "fv \<phi>1 \<union> fv \<phi>2"]]
      proof (intro arg_cong2[of _ _ _ _ "(\<and>)"] refl, goal_cases \<phi>1 \<phi>2)
        case \<phi>1
        then show ?case
          by (metis (mono_tags, lifting) 2 IntE Un_upper1 compatible_vals_extensible compatible_vals_union_eq)
      next
        case \<phi>2
        then show ?case
          by (metis (mono_tags, lifting) 2 IntE Un_upper2 compatible_vals_extensible compatible_vals_union_eq)
      qed
    qed (auto simp: compatible_vals_union_eq)
  }
next
  case (Exists x \<phi>)
  {
    case 1
    then have "(vs(x := Z)) y \<noteq> {}" if "Z \<noteq> {}" for Z y
      using that by auto
    with 1 have IH:
      "s_check_exec (vs(x := {z})) \<phi> sp = (\<forall>v\<in>compatible_vals (fv \<phi>) (vs(x := {z})). s_check v \<phi> sp)"
      for z sp
      by (intro Exists;
          auto simp: compatible_vals_fun_upd fun_upd_same
          simp del: fun_upd_apply intro: fun_upd_in_compatible_vals)
    from 1 show ?case
      using compatible_vals_nonemptyI[OF 1, of "fv \<phi> - {x}"]
      by (cases sp) (auto simp: SubsVals_nonempty IH fun_upd_in_compatible_vals_notin compatible_vals_fun_upd)
  next
    case 2
    then have "(vs(x := Z)) y \<noteq> {}" if "Z \<noteq> {}" for Z y
      using that by auto
    with 2 have IH:
      "Z \<noteq> {} \<Longrightarrow> v_check_exec (vs(x := Z)) \<phi> vp = (\<forall>v\<in>compatible_vals (fv \<phi>) (vs(x := Z)). v_check v \<phi> vp)"
      for Z vp
      by (intro Exists;
          auto simp: compatible_vals_fun_upd fun_upd_same
          simp del: fun_upd_apply intro: fun_upd_in_compatible_vals)
    show ?case
      using compatible_vals_nonemptyI[OF 2, of "fv \<phi> - {x}"]
      by (cases vp)
        (auto simp: SubsVals_nonempty IH[OF SubsVals_nonempty]
          fun_upd_in_compatible_vals fun_upd_in_compatible_vals_notin compatible_vals_fun_upd
          ball_conj_distrib 2[simplified] split: prod.splits if_splits |
          drule bspec, assumption)+
  }
next
  case (Forall x \<phi>)
  {
    case 1
    then have "(vs(x := Z)) y \<noteq> {}" if "Z \<noteq> {}" for Z y
      using that by auto
    with 1 have IH:
      "Z \<noteq> {} \<Longrightarrow> s_check_exec (vs(x := Z)) \<phi> sp = (\<forall>v\<in>compatible_vals (fv \<phi>) (vs(x := Z)). s_check v \<phi> sp)"
      for Z sp
      by (intro Forall;
          auto simp: compatible_vals_fun_upd fun_upd_same
          simp del: fun_upd_apply intro: fun_upd_in_compatible_vals)
    show ?case
      using compatible_vals_nonemptyI[OF 1, of "fv \<phi> - {x}"]
      by (cases sp)
        (auto simp: SubsVals_nonempty IH[OF SubsVals_nonempty]
          fun_upd_in_compatible_vals fun_upd_in_compatible_vals_notin compatible_vals_fun_upd
          ball_conj_distrib 1[simplified] split: prod.splits if_splits |
          drule bspec, assumption)+
  next
    case 2
    then have "(vs(x := Z)) y \<noteq> {}" if "Z \<noteq> {}" for Z y
      using that by auto
    with 2 have IH:
      "v_check_exec (vs(x := {z})) \<phi> vp = (\<forall>v\<in>compatible_vals (fv \<phi>) (vs(x := {z})). v_check v \<phi> vp)"
      for z vp
      by (intro Forall;
          auto simp: compatible_vals_fun_upd fun_upd_same
          simp del: fun_upd_apply intro: fun_upd_in_compatible_vals)
    from 2 show ?case
      using compatible_vals_nonemptyI[OF 2, of "fv \<phi> - {x}"]
      by (cases vp) (auto simp: SubsVals_nonempty IH fun_upd_in_compatible_vals_notin compatible_vals_fun_upd)
  }
next
  case (Prev I \<phi>)
  {
    case 1
    with Prev[of vs] show ?case
      using compatible_vals_nonemptyI[OF 1, of "fv \<phi>"]
      by (cases sp) auto
  next
    case 2
    with Prev[of vs] show ?case
      using compatible_vals_nonemptyI[OF 2, of "fv \<phi>"]
      by (cases vp) auto
  }
next
  case (Next I \<phi>)
  {
    case 1
    with Next[of vs] show ?case
      using compatible_vals_nonemptyI[OF 1, of "fv \<phi>"]
      by (cases sp) (auto simp: Let_def)
  next
    case 2
    with Next[of vs] show ?case
      using compatible_vals_nonemptyI[OF 2, of "fv \<phi>"]
      by (cases vp) auto
  }
next
  case (Once I \<phi>)
  {
    case 1
    with Once[of vs] show ?case
      using compatible_vals_nonemptyI[OF 1, of "fv \<phi>"]
      by (cases sp) (auto simp: Let_def)
  next
    case 2
    with Once[of vs] show ?case
      using compatible_vals_nonemptyI[OF 2, of "fv \<phi>"]
      by (cases vp) auto
  }
next
  case (Historically I \<phi>)
  {
    case 1
    with Historically[of vs] show ?case
      using compatible_vals_nonemptyI[OF 1, of "fv \<phi>"]
      by (cases sp) auto
  next
    case 2
    with Historically[of vs] show ?case
      using compatible_vals_nonemptyI[OF 2, of "fv \<phi>"]
      by (cases vp) (auto simp: Let_def)
  }
next
  case (Eventually I \<phi>)
  {
    case 1
    with Eventually[of vs] show ?case
      using compatible_vals_nonemptyI[OF 1, of "fv \<phi>"]
      by (cases sp) (auto simp: Let_def)
  next
    case 2
    with Eventually[of vs] show ?case
      using compatible_vals_nonemptyI[OF 2, of "fv \<phi>"]
      by (cases vp) auto
  }
next
  case (Always I \<phi>)
  {
    case 1
    with Always[of vs] show ?case
      using compatible_vals_nonemptyI[OF 1, of "fv \<phi>"]
      by (cases sp) auto
  next
    case 2
    with Always[of vs] show ?case
      using compatible_vals_nonemptyI[OF 2, of "fv \<phi>"]
      by (cases vp) (auto simp: Let_def)
  }
next
  case (Since \<phi>1 I \<phi>2)
  {
    case 1
    with compatible_vals_nonemptyI[OF 1, of "fv \<phi>1 \<union> fv \<phi>2"] show ?case
    proof (cases sp)
      case (SSince sp' sps)
      from check_fv_cong(1)[of \<phi>2 _ _ sp'] show ?thesis
        unfolding SSince s_check_exec_simps s_check_simps fv.simps ball_conj_distrib ball_swap[of _ "set sps"]
          Since(1)[OF 1] Since(3)[OF 1, of sp'] Let_def
          ball_triv_nonempty[OF compatible_vals_nonemptyI[OF 1, of "fv \<phi>1 \<union> fv \<phi>2"]]
      proof (intro arg_cong2[of _ _ _ _ "(\<and>)"] ball_cong[of "set sps", OF refl] refl, goal_cases \<phi>2 \<phi>1)
        case \<phi>2
        then show ?case
          by (metis (mono_tags, lifting) 1 IntE Un_upper2 compatible_vals_extensible compatible_vals_union_eq)
      next
        case (\<phi>1 sp)
        then show ?case using check_fv_cong(1)[of \<phi>1 _ _ sp]
          by (metis (mono_tags, lifting) 1 IntE Un_upper1 compatible_vals_extensible compatible_vals_union_eq)
      qed
    qed (auto simp: compatible_vals_union_eq)
  next
    case 2
    with compatible_vals_nonemptyI[OF 2, of "fv \<phi>1 \<union> fv \<phi>2"] show ?case
    proof (cases vp)
      case (VSince i vp' vps)
      from check_fv_cong(2)[of \<phi>1 _ _ vp'] show ?thesis
        unfolding VSince v_check_exec_simps v_check_simps fv.simps ball_conj_distrib ball_swap[of _ "set vps"]
          Since(2)[OF 2, of vp'] Since(4)[OF 2] Let_def
          ball_triv_nonempty[OF compatible_vals_nonemptyI[OF 2, of "fv \<phi>1 \<union> fv \<phi>2"]]
      proof (intro arg_cong2[of _ _ _ _ "(\<and>)"] ball_cong[of "set vps", OF refl] refl, goal_cases \<phi>1 \<phi>2)
        case \<phi>1
        then show ?case
          by (metis (mono_tags, lifting) 2 IntE Un_upper2 compatible_vals_extensible compatible_vals_union_eq)
      next
        case (\<phi>2 vp)
        then show ?case using check_fv_cong(2)[of \<phi>2 _ _ vp]
          by (metis (mono_tags, lifting) 2 IntE Un_upper1 compatible_vals_extensible compatible_vals_union_eq)
      qed
    next
      case (VSinceInf i j vps)
      show ?thesis
        unfolding VSinceInf v_check_exec_simps v_check_simps fv.simps ball_conj_distrib ball_swap[of _ "set vps"]
          Since(4)[OF 2] Let_def
          ball_triv_nonempty[OF compatible_vals_nonemptyI[OF 2, of "fv \<phi>1 \<union> fv \<phi>2"]]
      proof (intro arg_cong2[of _ _ _ _ "(\<and>)"] ball_cong[of "set vps", OF refl] refl, goal_cases \<phi>2)
        case (\<phi>2 vp)
        then show ?case using check_fv_cong(2)[of \<phi>2 _ _ vp]
          by (metis (mono_tags, lifting) 2 IntE Un_upper1 compatible_vals_extensible compatible_vals_union_eq)
      qed
    qed (auto simp: compatible_vals_union_eq)
  }
next
  case (Until \<phi>1 I \<phi>2)
  {
    case 1
    with compatible_vals_nonemptyI[OF 1, of "fv \<phi>1 \<union> fv \<phi>2"] show ?case
    proof (cases sp)
      case (SUntil sps sp')
      from check_fv_cong(1)[of \<phi>2 _ _ sp'] show ?thesis
        unfolding SUntil s_check_exec_simps s_check_simps fv.simps ball_conj_distrib ball_swap[of _ "set sps"]
          Until(1)[OF 1] Until(3)[OF 1, of sp'] Let_def
          ball_triv_nonempty[OF compatible_vals_nonemptyI[OF 1, of "fv \<phi>1 \<union> fv \<phi>2"]]
      proof (intro arg_cong2[of _ _ _ _ "(\<and>)"] ball_cong[of "set sps", OF refl] refl, goal_cases \<phi>2 \<phi>1)
        case \<phi>2
        then show ?case
          by (metis (mono_tags, lifting) 1 IntE Un_upper2 compatible_vals_extensible compatible_vals_union_eq)
      next
        case (\<phi>1 sp)
        then show ?case using check_fv_cong(1)[of \<phi>1 _ _ sp]
          by (metis (mono_tags, lifting) 1 IntE Un_upper1 compatible_vals_extensible compatible_vals_union_eq)
      qed
    qed (auto simp: compatible_vals_union_eq)
  next
    case 2
    with compatible_vals_nonemptyI[OF 2, of "fv \<phi>1 \<union> fv \<phi>2"] show ?case
    proof (cases vp)
      case (VUntil i vps vp')
      from check_fv_cong(2)[of \<phi>1 _ _ vp'] show ?thesis
        unfolding VUntil v_check_exec_simps v_check_simps fv.simps ball_conj_distrib ball_swap[of _ "set vps"]
          Until(2)[OF 2, of vp'] Until(4)[OF 2] Let_def
          ball_triv_nonempty[OF compatible_vals_nonemptyI[OF 2, of "fv \<phi>1 \<union> fv \<phi>2"]]
      proof (intro arg_cong2[of _ _ _ _ "(\<and>)"] ball_cong[of "set vps", OF refl] refl, goal_cases \<phi>1 \<phi>2)
        case \<phi>1
        then show ?case
          by (metis (mono_tags, lifting) 2 IntE Un_upper2 compatible_vals_extensible compatible_vals_union_eq)
      next
        case (\<phi>2 vp)
        then show ?case using check_fv_cong(2)[of \<phi>2 _ _ vp]
          by (metis (mono_tags, lifting) 2 IntE Un_upper1 compatible_vals_extensible compatible_vals_union_eq)
      qed
    next
      case (VUntilInf i j vps)
      show ?thesis
        unfolding VUntilInf v_check_exec_simps v_check_simps fv.simps ball_conj_distrib ball_swap[of _ "set vps"]
          Until(4)[OF 2] Let_def
          ball_triv_nonempty[OF compatible_vals_nonemptyI[OF 2, of "fv \<phi>1 \<union> fv \<phi>2"]]
      proof (intro arg_cong2[of _ _ _ _ "(\<and>)"] ball_cong[of "set vps", OF refl] refl, goal_cases \<phi>2)
        case (\<phi>2 vp)
        then show ?case using check_fv_cong(2)[of \<phi>2 _ _ vp]
          by (metis (mono_tags, lifting) 2 IntE Un_upper1 compatible_vals_extensible compatible_vals_union_eq)
      qed
    qed (auto simp: compatible_vals_union_eq)
  }
qed

lemma s_check_code[code]: "s_check v \<phi> sp = s_check_exec (\<lambda>x. {v x}) \<phi> sp"
  by (subst check_exec_check)
    (auto simp: compatible_vals_def elim: check_fv_cong[THEN iffD2, rotated])

lemma v_check_code[code]: "v_check v \<phi> vp = v_check_exec (\<lambda>x. {v x}) \<phi> vp"
  by (subst check_exec_check)
    (auto simp: compatible_vals_def elim: check_fv_cong[THEN iffD2, rotated])

subsection \<open>Latest Relevant Time-Point\<close>

fun LRTP :: "('n, 'd) formula \<Rightarrow> nat \<Rightarrow> nat option" where
  "LRTP \<top> i = Some i"
| "LRTP \<bottom> i = Some i"
| "LRTP (_ \<dagger> _) i = Some i"
| "LRTP (_ \<^bold>\<approx> _) i = Some i"
| "LRTP (\<not>\<^sub>F \<phi>) i = LRTP \<phi> i"
| "LRTP (\<phi> \<or>\<^sub>F \<psi>) i = max_opt (LRTP \<phi> i) (LRTP \<psi> i)"
| "LRTP (\<phi> \<and>\<^sub>F \<psi>) i = max_opt (LRTP \<phi> i) (LRTP \<psi> i)"
| "LRTP (\<phi> \<longrightarrow>\<^sub>F \<psi>) i = max_opt (LRTP \<phi> i) (LRTP \<psi> i)"
| "LRTP (\<phi> \<longleftrightarrow>\<^sub>F \<psi>) i = max_opt (LRTP \<phi> i) (LRTP \<psi> i)"
| "LRTP (\<exists>\<^sub>F_. \<phi>) i = LRTP \<phi> i"
| "LRTP (\<forall>\<^sub>F_. \<phi>) i = LRTP \<phi> i"
| "LRTP (\<^bold>Y I \<phi>) i = LRTP \<phi> (i-1)"
| "LRTP (\<^bold>X I \<phi>) i = LRTP \<phi> (i+1)"
| "LRTP (\<^bold>P I \<phi>) i = LRTP \<phi> (LTP_p_safe \<sigma> i I)"
| "LRTP (\<^bold>H I \<phi>) i = LRTP \<phi> (LTP_p_safe \<sigma> i I)"
| "LRTP (\<^bold>F I \<phi>) i = (case right I of \<infinity> \<Rightarrow> None | enat b \<Rightarrow> LRTP \<phi> (LTP_f \<sigma> i b))"
| "LRTP (\<^bold>G I \<phi>) i = (case right I of \<infinity> \<Rightarrow> None | enat b \<Rightarrow> LRTP \<phi> (LTP_f \<sigma> i b))" 
| "LRTP (\<phi> \<^bold>S I \<psi>) i = max_opt (LRTP \<phi> i) (LRTP \<psi> (LTP_p_safe \<sigma> i I))"
| "LRTP (\<phi> \<^bold>U I \<psi>) i = (case right I of \<infinity> \<Rightarrow> None | enat b \<Rightarrow> max_opt (LRTP \<phi> ((LTP_f \<sigma> i b)-1)) (LRTP \<psi> (LTP_f \<sigma> i b)))"

lemma fb_LRTP: 
  assumes "future_bounded \<phi>"
  shows "\<not> Option.is_none (LRTP \<phi> i)"
  using assms
  by (induction \<phi> i rule: LRTP.induct) 
    (auto simp add: max_opt_def Option.is_none_def)

lemma not_none_fb_LRTP:
  assumes "future_bounded \<phi>"
  shows "LRTP \<phi> i \<noteq> None"
  using assms fb_LRTP by (auto simp add: Option.is_none_def)

lemma is_some_fb_LRTP:
  assumes "future_bounded \<phi>"
  shows "\<exists>j. LRTP \<phi> i = Some j"
  using assms fb_LRTP by (auto simp add: Option.is_none_def)

lemma enat_trans[simp]: "enat i \<le> enat j \<and> enat j \<le> enat k \<Longrightarrow> enat i \<le> enat k"
  by auto

subsection \<open>Active Domain\<close>

definition AD :: "('n, 'd) formula \<Rightarrow> nat \<Rightarrow> 'd set"
  where "AD \<phi> i = consts \<phi> \<union> (\<Union> k \<le> the (LRTP \<phi> i). \<Union> (set ` snd ` \<Gamma> \<sigma> k))"

lemma val_in_AD_iff:
  "x \<in> fv \<phi> \<Longrightarrow> v x \<in> AD \<phi> i \<longleftrightarrow> v x \<in> consts \<phi> \<or>
  (\<exists>r ts k. k \<le> the (LRTP \<phi> i) \<and> (r, v\<^bold>\<lbrakk>ts\<^bold>\<rbrakk>) \<in> \<Gamma> \<sigma> k \<and> x \<in> \<Union> (set (map fv_trm ts)))"
  unfolding AD_def Un_iff UN_iff Bex_def atMost_iff set_map
    ex_comm[of "P :: _ \<Rightarrow> nat \<Rightarrow> _" for P] ex_simps image_iff
proof (safe intro!: arg_cong[of _ _ "\<lambda>x. _ \<or> x"] ex_cong, unfold snd_conv, goal_cases LR RL)
  case (LR i _ r ds)
  then show ?case
    by (intro exI[of _ r] conjI
        exI[of _ "map (\<lambda>d. if v x = d then (\<^bold>v x) else \<^bold>c d) ds"])
      (auto simp: eval_trms_def o_def map_idI)
next
  case (RL i r ts t)
  then show ?case
    by (intro exI[of _ "v\<^bold>\<lbrakk>ts\<^bold>\<rbrakk>"] conjI)
      (auto simp: eval_trms_def image_iff in_fv_trm_conv intro!: bexI[of _ t])
qed

lemma val_notin_AD_iff:
  "x \<in> fv \<phi> \<Longrightarrow> v x \<notin> AD \<phi> i \<longleftrightarrow> v x \<notin> consts \<phi> \<and>
    (\<forall>r ts k. k \<le> the (LRTP \<phi> i) \<and> x \<in> \<Union> (set (map fv_trm ts)) \<longrightarrow> (r, v\<^bold>\<lbrakk>ts\<^bold>\<rbrakk>) \<notin> \<Gamma> \<sigma> k)"
  using val_in_AD_iff by blast

lemma finite_values: "finite (\<Union> (set ` snd ` \<Gamma> \<sigma> k))"
  by (transfer, auto simp add: sfinite_def)

lemma finite_tps: "future_bounded \<phi> \<Longrightarrow> finite (\<Union> k < the (LRTP \<phi> i). {k})"
  using fb_LRTP[of \<phi>] finite_enat_bounded
  by simp

lemma finite_AD [simp]: "future_bounded \<phi> \<Longrightarrow> finite (AD \<phi> i)"
  using finite_tps finite_values
  by (simp add: AD_def enat_def)

lemma finite_AD_UNIV:
  assumes "future_bounded \<phi>" and "AD \<phi> i = (UNIV:: 'd set)"
  shows "finite (UNIV::'d set)"
proof -
  have "finite (AD \<phi> i)"
    using finite_AD[of \<phi> i, OF assms(1)] by simp
  then show ?thesis
    using assms(2) by simp
qed

subsection \<open>Congruence Modulo Active Domain\<close>

lemma AD_simps[simp]:
  "AD (\<not>\<^sub>F \<phi>) i = AD \<phi> i"
  "future_bounded (\<phi> \<or>\<^sub>F \<psi>) \<Longrightarrow> AD (\<phi> \<or>\<^sub>F \<psi>) i = AD \<phi> i \<union> AD \<psi> i"
  "future_bounded (\<phi> \<and>\<^sub>F \<psi>) \<Longrightarrow> AD (\<phi> \<and>\<^sub>F \<psi>) i = AD \<phi> i \<union> AD \<psi> i"
  "future_bounded (\<phi> \<longrightarrow>\<^sub>F \<psi>) \<Longrightarrow> AD (\<phi> \<longrightarrow>\<^sub>F \<psi>) i = AD \<phi> i \<union> AD \<psi> i"
  "future_bounded (\<phi> \<longleftrightarrow>\<^sub>F \<psi>) \<Longrightarrow> AD (\<phi> \<longleftrightarrow>\<^sub>F \<psi>) i = AD \<phi> i \<union> AD \<psi> i"
  "AD (\<exists>\<^sub>Fx.  \<phi>) i = AD \<phi> i"
  "AD (\<forall>\<^sub>Fx.  \<phi>) i = AD \<phi> i"
  "AD (\<^bold>Y I \<phi>) i = AD \<phi> (i - 1)"
  "AD (\<^bold>X I \<phi>) i = AD \<phi> (i + 1)"
  "future_bounded (\<^bold>F I \<phi>) \<Longrightarrow> AD (\<^bold>F I \<phi>) i = AD \<phi> (LTP_f \<sigma> i (the_enat (right I)))"
  "future_bounded (\<^bold>G I \<phi>) \<Longrightarrow> AD (\<^bold>G I \<phi>) i = AD \<phi> (LTP_f \<sigma> i (the_enat (right I)))"
  "AD (\<^bold>P I \<phi>) i = AD \<phi> (LTP_p_safe \<sigma> i I)"
  "AD (\<^bold>H I \<phi>) i = AD \<phi> (LTP_p_safe \<sigma> i I)"
  "future_bounded (\<phi> \<^bold>S I \<psi>) \<Longrightarrow> AD (\<phi> \<^bold>S I \<psi>) i = AD \<phi> i \<union> AD \<psi> (LTP_p_safe \<sigma> i I)"
  "future_bounded (\<phi> \<^bold>U I \<psi>) \<Longrightarrow> AD (\<phi> \<^bold>U I \<psi>) i = AD \<phi> (LTP_f \<sigma> i (the_enat (right I)) - 1) \<union> AD \<psi> (LTP_f \<sigma> i (the_enat (right I)))"
  by (auto 0 3 simp: AD_def max_opt_def not_none_fb_LRTP le_max_iff_disj Bex_def split: option.splits)


lemma LTP_p_mono: "i \<le> j \<Longrightarrow> LTP_p_safe \<sigma> i I \<le> LTP_p_safe \<sigma> j I"
  unfolding LTP_p_safe_def
  by (smt (verit, ccfv_threshold) \<tau>_mono bot_nat_0.extremum diff_le_mono order.trans i_LTP_tau le_cases3 min.bounded_iff)

lemma LTP_f_mono:
  assumes "i \<le> j"
  shows"LTP_f \<sigma> i b \<le> LTP_f \<sigma> j b"
  unfolding LTP_def
proof (rule Max_mono)
  show "finite {i. \<tau> \<sigma> i \<le> \<tau> \<sigma> j + b}"
    unfolding finite_nat_set_iff_bounded_le
    by (metis i_le_LTPi_add le_Suc_ex mem_Collect_eq)
qed (auto simp: assms intro!: exI[of _ i] elim: order_trans)

lemma LRTP_mono: "future_bounded \<phi> \<Longrightarrow> i \<le> j \<Longrightarrow> the (LRTP \<phi> i) \<le> the (LRTP \<phi> j)"
proof (induct \<phi> arbitrary: i j)
  case (Or \<phi>1 \<phi>2)
  from Or(1,2)[of i j] Or(3-) show ?case
    by (auto simp: max_opt_def not_none_fb_LRTP split: option.splits)
next
  case (And \<phi>1 \<phi>2)
  from And(1,2)[of i j] And(3-) show ?case
    by (auto simp: max_opt_def not_none_fb_LRTP split: option.splits)
next
  case (Imp \<phi>1 \<phi>2)
  from Imp(1,2)[of i j] Imp(3-) show ?case
    by (auto simp: max_opt_def not_none_fb_LRTP split: option.splits)
next
  case (Iff \<phi>1 \<phi>2)
  from Iff(1,2)[of i j] Iff(3-) show ?case
    by (auto simp: max_opt_def not_none_fb_LRTP split: option.splits)
next
  case (Since \<phi>1 I \<phi>2)
  from Since(1)[OF _ Since(4)] Since(2)[of "LTP_p_safe \<sigma> i I" "LTP_p_safe \<sigma> j I"] Since(3-)
  show ?case
    by (auto simp: max_opt_def not_none_fb_LRTP LTP_p_mono split: option.splits)
next
  case (Until \<phi>1 I \<phi>2)
  from Until(1)[of "LTP_f \<sigma> i (the_enat (right I)) - 1" "LTP_f \<sigma> j (the_enat (right I)) - 1"]
    Until(2)[of "LTP_f \<sigma> i (the_enat (right I))" "LTP_f \<sigma> j (the_enat (right I))"] Until(3-)
  show ?case
    by (auto simp: max_opt_def not_none_fb_LRTP LTP_f_mono diff_le_mono split: option.splits)
qed (auto simp: LTP_p_mono LTP_f_mono)

lemma AD_mono: "future_bounded \<phi> \<Longrightarrow> i \<le> j \<Longrightarrow> AD \<phi> i \<subseteq> AD \<phi> j"
  by (auto 0 3 simp: AD_def Bex_def intro: LRTP_mono elim!: order_trans)

lemma LTP_p_safe_le[simp]: "LTP_p_safe \<sigma> i I \<le> i"
  by (auto simp: LTP_p_safe_def)

lemma check_AD_cong:
  assumes "future_bounded \<phi>"
    and "(\<forall>x \<in> fv \<phi>. v x = v' x \<or> (v x \<notin> AD \<phi> i \<and> v' x \<notin> AD \<phi> i))"
  shows "(s_at sp = i \<Longrightarrow> s_check v \<phi> sp \<longleftrightarrow> s_check v' \<phi> sp)"
    "(v_at vp = i \<Longrightarrow> v_check v \<phi> vp \<longleftrightarrow> v_check v' \<phi> vp)"
  using assms
proof (induction v \<phi> sp and v \<phi> vp arbitrary: i v' and i v' rule: s_check_v_check.induct)
  case (1 v f sp)
  note IH = 1(1-23)[OF refl] and hyps = 1(24-26)
  show ?case
  proof (cases sp)
    case (SPred j r ts)
    then show ?thesis
    proof (cases f)
      case (Pred q us)
      with SPred hyps show ?thesis
        using eval_trms_fv_cong[of ts v v']
        by (force simp: val_notin_AD_iff dest!: spec[of _ i] spec[of _ r] spec[of _ ts])
    qed auto
  next
    case (SEq_Const j r ts)
    with hyps show ?thesis
      by (cases f) (auto simp: val_notin_AD_iff)
  next
    case (SNeg vp')
    then show ?thesis
      using IH(1)[of _ _ _ v'] hyps
      by (cases f) auto
  next
    case (SOrL sp')
    then show ?thesis
      using IH(2)[of _ _ _ _ v'] hyps
      by (cases f) auto
  next
    case (SOrR sp')
    then show ?thesis
      using IH(3)[of _ _ _ _ v'] hyps
      by (cases f) auto
  next
    case (SAnd sp1 sp2)
    then show ?thesis
      using IH(4,5)[of _ _ _ _ _ v'] hyps
      by (cases f) (auto 7 0)+
  next
    case (SImpL vp')
    then show ?thesis
      using IH(6)[of _ _ _ _ v'] hyps
      by (cases f) auto
  next
    case (SImpR sp')
    then show ?thesis
      using IH(7)[of _ _ _ _ v'] hyps
      by (cases f) auto
  next
    case (SIffSS sp1 sp2)
    then show ?thesis
      using IH(8,9)[of _ _ _ _ _ v'] hyps
      by (cases f) (auto 7 0)+
  next
    case (SIffVV vp1 vp2)
    then show ?thesis
      using IH(10,11)[of _ _ _ _ _ v'] hyps
      by (cases f) (auto 7 0)+
  next
    case (SExists x z sp')
    then show ?thesis
      using IH(12)[of x _ x z sp' i "v'(x := z)"] hyps
      by (cases f) (auto simp add: fun_upd_def)
  next
    case (SForall x part)
    then show ?thesis
      using IH(13)[of x _ x part _ _ D _ z _ "v'(x := z)" for D z, OF _ _ _ _  refl _ refl] hyps
      by (cases f) (auto simp add: fun_upd_def)
  next
    case (SPrev sp')
    then show ?thesis
      using IH(14)[of _ _ _ _ _ _ v'] hyps
      by (cases f) auto
  next
    case (SNext sp')
    then show ?thesis
      using IH(15)[of _ _ _ _ _ _ v'] hyps
      by (cases f) (auto simp add: Let_def)
  next
    case (SOnce j sp')
    then show ?thesis
    proof (cases f)
      case (Once I \<phi>)
      { fix k
        assume k: "k \<le> i" "\<tau> \<sigma> i - left I \<ge> \<tau> \<sigma> k"
        then have "\<tau> \<sigma> i - left I \<ge> \<tau> \<sigma> 0"
          by (meson \<tau>_mono le0 order_trans)
        with k have "k \<le> LTP_p_safe \<sigma> i I"
          unfolding LTP_p_safe_def by (auto simp: i_LTP_tau)
        with Once hyps(2,3) have "\<forall>x\<in>fv \<phi>. v x = v' x \<or> v x \<notin> AD \<phi> k \<and> v' x \<notin> AD \<phi> k"
          by (auto dest!: bspec dest: AD_mono[THEN set_mp, rotated -1])
      }
      with Once SOnce show ?thesis
        using IH(16)[OF Once SOnce refl refl, of v'] hyps(1,2)
        by (auto simp: Let_def le_diff_conv2)
    qed auto
  next
    case (SHistorically j k sps)
    then show ?thesis
    proof (cases f)
      case (Historically I \<phi>)
      { fix sp :: "('n, 'd) sproof"
        define l and u where "l = s_at sp" and "u = LTP_p \<sigma> i I"
        assume *: "sp \<in> set sps" "\<tau> \<sigma> 0 + left I \<le> \<tau> \<sigma> i"
        then have u_def: "u = LTP_p_safe \<sigma> i I"
          by (auto simp: LTP_p_safe_def u_def)
        from *(1) obtain j where j: "sp = sps ! j" "j < length sps"
          unfolding in_set_conv_nth by auto
        moreover
        assume eq: "map s_at sps = [k ..< Suc u]"
        then have len: "length sps = Suc u - k"
          by (auto dest!: arg_cong[where f=length])
        moreover
        have "s_at (sps ! j) = k + j"
          using arg_cong[where f="\<lambda>xs. nth xs j", OF eq] j len *(2)
          by (auto simp: nth_append)
        ultimately have "l \<le> u"
          unfolding l_def by auto
        with Historically hyps(2,3) have "\<forall>x\<in>fv \<phi>. v x = v' x \<or> v x \<notin> AD \<phi> l \<and> v' x \<notin> AD \<phi> l"
          by (auto simp: u_def dest!: bspec dest: AD_mono[THEN set_mp, rotated -1])
      }
      with Historically SHistorically show ?thesis
        using IH(17)[OF Historically SHistorically _ refl, of _ v'] hyps(1,2)
        by auto
    qed auto
  next
    case (SEventually j sp')
    then show ?thesis
    proof (cases f)
      case (Eventually I \<phi>)
      { fix k
        assume "\<tau> \<sigma> k \<le> the_enat (right I) + \<tau> \<sigma> i"
        then have "k \<le> LTP_f \<sigma> i (the_enat (right I))"
          by (metis add.commute i_le_LTPi_add le_add_diff_inverse)
        with Eventually hyps(2,3) have "\<forall>x\<in>fv \<phi>. v x = v' x \<or> v x \<notin> AD \<phi> k \<and> v' x \<notin> AD \<phi> k"
          by (auto dest!: bspec dest: AD_mono[THEN set_mp, rotated -1])
      }
      with Eventually SEventually show ?thesis
        using IH(18)[OF Eventually SEventually refl refl, of v'] hyps(1,2)
        by (auto simp: Let_def)
    qed auto
  next
    case (SAlways j k sps)
    then show ?thesis
    proof (cases f)
      case (Always I \<phi>)
      { fix sp :: "('n, 'd) sproof"
        define l and u where "l = s_at sp" and "u = LTP_f \<sigma> i (the_enat (right I))"
        assume *: "sp \<in> set sps"
        then obtain j where j: "sp = sps ! j" "j < length sps"
          unfolding in_set_conv_nth by auto
        assume eq: "map s_at sps = [ETP_f \<sigma> i I ..< Suc u]"
        then have "length sps = Suc u - ETP_f \<sigma> i I"
          by (auto dest!: arg_cong[where f=length])
        with j eq have "l \<le> LTP_f \<sigma> i (the_enat (right I))"
          by (auto simp: l_def u_def dest!: arg_cong[where f="\<lambda>xs. nth xs j"]
              simp del: upt.simps split: if_splits)
        with Always hyps(2,3) have "\<forall>x\<in>fv \<phi>. v x = v' x \<or> v x \<notin> AD \<phi> l \<and> v' x \<notin> AD \<phi> l"
          by (auto dest!: bspec dest: AD_mono[THEN set_mp, rotated -1])
      }
      with Always SAlways show ?thesis
        using IH(19)[OF Always SAlways _ refl, of _ v'] hyps(1,2)
        by auto
    qed auto
  next
    case (SSince sp' sps)
    then show ?thesis
    proof (cases f)
      case (Since \<phi> I \<psi>)
      { fix sp :: "('n, 'd) sproof"
        define l where "l = s_at sp"
        assume *: "sp \<in> set sps"
        from *(1) obtain j where j: "sp = sps ! j" "j < length sps"
          unfolding in_set_conv_nth by auto
        moreover
        assume eq: "map s_at sps = [Suc (s_at sp')  ..< Suc i]"
        then have len: "length sps = i - s_at sp'"
          by (auto dest!: arg_cong[where f=length])
        moreover
        have "s_at (sps ! j) = Suc (s_at sp') + j"
          using arg_cong[where f="\<lambda>xs. nth xs j", OF eq] j len
          by (auto simp: nth_append)
        ultimately have "l \<le> i"
          unfolding l_def by auto
        with Since hyps(2,3) have "\<forall>x\<in>fv \<phi>. v x = v' x \<or> v x \<notin> AD \<phi> l \<and> v' x \<notin> AD \<phi> l"
          by (auto simp: dest!: bspec dest: AD_mono[THEN set_mp, rotated -1])
      }
      moreover
      { fix k
        assume k: "k \<le> i" "\<tau> \<sigma> i - left I \<ge> \<tau> \<sigma> k"
        then have "\<tau> \<sigma> i - left I \<ge> \<tau> \<sigma> 0"
          by (meson \<tau>_mono le0 order_trans)
        with k have "k \<le> LTP_p_safe \<sigma> i I"
          unfolding LTP_p_safe_def by (auto simp: i_LTP_tau)
        with Since hyps(2,3) have "\<forall>x\<in>fv \<psi>. v x = v' x \<or> v x \<notin> AD \<psi> k \<and> v' x \<notin> AD \<psi> k"
          by (auto dest!: bspec dest: AD_mono[THEN set_mp, rotated -1])
      }
      ultimately show ?thesis
        using Since SSince IH(20)[OF Since SSince refl refl refl, of v'] IH(21)[OF Since SSince refl refl _ refl, of _ v'] hyps(1,2)
        by (auto simp: Let_def le_diff_conv2 simp del: upt.simps)
    qed auto
  next
    case (SUntil sps sp')
    then show ?thesis
    proof (cases f)
      case (Until \<phi> I \<psi>)
      { fix sp :: "('n, 'd) sproof"
        define l where "l = s_at sp"
        assume *: "sp \<in> set sps"
        from *(1) obtain j where j: "sp = sps ! j" "j < length sps"
          unfolding in_set_conv_nth by auto
        moreover
        assume "\<delta> \<sigma> (s_at sp') i \<le> the_enat (right I)"
        then have "s_at sp' \<le> LTP_f \<sigma> i (the_enat (right I))"
          by (metis add.commute i_le_LTPi_add le_add_diff_inverse le_diff_conv)
        moreover
        assume eq: "map s_at sps = [i ..< s_at sp']"
        then have len: "length sps = s_at sp' - i"
          by (auto dest!: arg_cong[where f=length])
        moreover
        have "s_at (sps ! j) = i + j"
          using arg_cong[where f="\<lambda>xs. nth xs j", OF eq] j len
          by (auto simp: nth_append)
        ultimately have "l \<le> LTP_f \<sigma> i (the_enat (right I)) - 1"
          unfolding l_def by auto
        with Until hyps(2,3) have "\<forall>x\<in>fv \<phi>. v x = v' x \<or> v x \<notin> AD \<phi> l \<and> v' x \<notin> AD \<phi> l"
          by (auto simp: dest!: bspec dest: AD_mono[THEN set_mp, rotated -1])
      }
      moreover
      { fix k
        assume "\<tau> \<sigma> k \<le> the_enat (right I) + \<tau> \<sigma> i"
        then have "k \<le> LTP_f \<sigma> i (the_enat (right I))"
          by (metis add.commute i_le_LTPi_add le_add_diff_inverse)
        with Until hyps(2,3) have "\<forall>x\<in>fv \<psi>. v x = v' x \<or> v x \<notin> AD \<psi> k \<and> v' x \<notin> AD \<psi> k"
          by (auto dest!: bspec dest: AD_mono[THEN set_mp, rotated -1])
      }
      ultimately show ?thesis
        using Until SUntil IH(22)[OF Until SUntil refl refl refl, of v'] IH(23)[OF Until SUntil refl refl _ refl, of _ v'] hyps(1,2)
        by (auto simp: Let_def le_diff_conv2 simp del: upt.simps)
    qed auto
  qed (cases f; simp_all)+
next
  case (2 v f vp)
  note IH = 2(1-25)[OF refl] and hyps = 2(26-28)
  show ?case
  proof (cases vp)
    case (VPred j r ts)
    then show ?thesis
    proof (cases f)
      case (Pred q us)
      with VPred hyps show ?thesis
        using eval_trms_fv_cong[of ts v v']
        by (force simp: val_notin_AD_iff dest!: spec[of _ i] spec[of _ r] spec[of _ ts])
    qed auto
  next
    case (VEq_Const j r ts)
    with hyps show ?thesis
      by (cases f) (auto simp: val_notin_AD_iff)
  next
    case (VNeg sp')
    then show ?thesis
      using IH(1)[of _ _ _ v'] hyps
      by (cases f) auto
  next
    case (VOr vp1 vp2)
    then show ?thesis
      using IH(2,3)[of _ _ _ _ _ v'] hyps
      by (cases f) (auto 7 0)+
  next
    case (VAndL vp')
    then show ?thesis
      using IH(4)[of _ _ _ _ v'] hyps
      by (cases f) auto
  next
    case (VAndR vp')
    then show ?thesis
      using IH(5)[of _ _ _ _ v'] hyps
      by (cases f) auto
  next
    case (VImp sp1 vp2)
    then show ?thesis
      using IH(6,7)[of _ _ _ _ _ v'] hyps
      by (cases f) (auto 7 0)+
  next
    case (VIffSV sp1 vp2)
    then show ?thesis
      using IH(8,9)[of _ _ _ _ _ v'] hyps
      by (cases f) (auto 7 0)+
  next
    case (VIffVS vp1 sp2)
    then show ?thesis
      using IH(10,11)[of _ _ _ _ _ v'] hyps
      by (cases f) (auto 7 0)+
  next
    case (VExists x part)
    then show ?thesis
      using IH(12)[of x _ x part _ _ D _ z _ "v'(x := z)" for D z, OF _ _ _ _  refl _ refl] hyps
      by (cases f) (auto simp add: fun_upd_def)
  next
    case (VForall x z vp')
    then show ?thesis
      using IH(13)[of x _ x z vp' i "v'(x := z)"] hyps
      by (cases f) (auto simp add: fun_upd_def)
  next
    case (VPrev vp')
    then show ?thesis
      using IH(14)[of _ _ _ _ _ _ v'] hyps
      by (cases f) auto
  next
    case (VNext vp')
    then show ?thesis
      using IH(15)[of _ _ _ _ _ _ v'] hyps
      by (cases f) auto
  next
    case (VOnce j k vps)
    then show ?thesis
    proof (cases f)
      case (Once I \<phi>)
      { fix vp :: "('n, 'd) vproof"
        define l and u where "l = v_at vp" and "u = LTP_p \<sigma> i I"
        assume *: "vp \<in> set vps" "\<tau> \<sigma> 0 + left I \<le> \<tau> \<sigma> i"
        then have u_def: "u = LTP_p_safe \<sigma> i I"
          by (auto simp: LTP_p_safe_def u_def)
        from *(1) obtain j where j: "vp = vps ! j" "j < length vps"
          unfolding in_set_conv_nth by auto
        moreover
        assume eq: "map v_at vps = [k ..< Suc u]"
        then have len: "length vps = Suc u - k"
          by (auto dest!: arg_cong[where f=length])
        moreover
        have "v_at (vps ! j) = k + j"
          using arg_cong[where f="\<lambda>xs. nth xs j", OF eq] j len *(2)
          by (auto simp: nth_append)
        ultimately have "l \<le> u"
          unfolding l_def by auto
        with Once hyps(2,3) have "\<forall>x\<in>fv \<phi>. v x = v' x \<or> v x \<notin> AD \<phi> l \<and> v' x \<notin> AD \<phi> l"
          by (auto simp: u_def dest!: bspec dest: AD_mono[THEN set_mp, rotated -1])
      }
      with Once VOnce show ?thesis
        using IH(16)[OF Once VOnce _ refl, of _ v'] hyps(1,2)
        by auto
    qed auto
  next
    case (VHistorically j vp')
    then show ?thesis
    proof (cases f)
      case (Historically I \<phi>)
      { fix k
        assume k: "k \<le> i" "\<tau> \<sigma> i - left I \<ge> \<tau> \<sigma> k"
        then have "\<tau> \<sigma> i - left I \<ge> \<tau> \<sigma> 0"
          by (meson \<tau>_mono le0 order_trans)
        with k have "k \<le> LTP_p_safe \<sigma> i I"
          unfolding LTP_p_safe_def by (auto simp: i_LTP_tau)
        with Historically hyps(2,3) have "\<forall>x\<in>fv \<phi>. v x = v' x \<or> v x \<notin> AD \<phi> k \<and> v' x \<notin> AD \<phi> k"
          by (auto dest!: bspec dest: AD_mono[THEN set_mp, rotated -1])
      }
      with Historically VHistorically show ?thesis
        using IH(17)[OF Historically VHistorically refl refl, of v'] hyps(1,2)
        by (auto simp: Let_def le_diff_conv2)
    qed auto
  next
    case (VEventually j k vps)
    then show ?thesis
    proof (cases f)
      case (Eventually I \<phi>)
      { fix vp :: "('n, 'd) vproof"
        define l and u where "l = v_at vp" and "u = LTP_f \<sigma> i (the_enat (right I))"
        assume *: "vp \<in> set vps"
        then obtain j where j: "vp = vps ! j" "j < length vps"
          unfolding in_set_conv_nth by auto
        assume eq: "map v_at vps = [ETP_f \<sigma> i I ..< Suc u]"
        then have "length vps = Suc u - ETP_f \<sigma> i I"
          by (auto dest!: arg_cong[where f=length])
        with j eq have "l \<le> LTP_f \<sigma> i (the_enat (right I))"
          by (auto simp: l_def u_def dest!: arg_cong[where f="\<lambda>xs. nth xs j"]
              simp del: upt.simps split: if_splits)
        with Eventually hyps(2,3) have "\<forall>x\<in>fv \<phi>. v x = v' x \<or> v x \<notin> AD \<phi> l \<and> v' x \<notin> AD \<phi> l"
          by (auto dest!: bspec dest: AD_mono[THEN set_mp, rotated -1])
      }
      with Eventually VEventually show ?thesis
        using IH(18)[OF Eventually VEventually _ refl, of _ v'] hyps(1,2)
        by auto
    qed auto
  next
    case (VAlways j vp')
    then show ?thesis
    proof (cases f)
      case (Always I \<phi>)
      { fix k
        assume "\<tau> \<sigma> k \<le> the_enat (right I) + \<tau> \<sigma> i"
        then have "k \<le> LTP_f \<sigma> i (the_enat (right I))"
          by (metis add.commute i_le_LTPi_add le_add_diff_inverse)
        with Always hyps(2,3) have "\<forall>x\<in>fv \<phi>. v x = v' x \<or> v x \<notin> AD \<phi> k \<and> v' x \<notin> AD \<phi> k"
          by (auto dest!: bspec dest: AD_mono[THEN set_mp, rotated -1])
      }
      with Always VAlways show ?thesis
        using IH(19)[OF Always VAlways refl refl, of v'] hyps(1,2)
        by (auto simp: Let_def)
    qed auto
  next
    case (VSince j vp' vps)
    then show ?thesis
    proof (cases f)
      case (Since \<phi> I \<psi>)
      { fix sp :: "('n, 'd) vproof"
        define l and u where "l = v_at sp" and "u = LTP_p \<sigma> i I"
        assume *: "sp \<in> set vps" "\<tau> \<sigma> 0 + left I \<le> \<tau> \<sigma> i"
        then have u_def: "u = LTP_p_safe \<sigma> i I"
          by (auto simp: LTP_p_safe_def u_def)
        from *(1) obtain j where j: "sp = vps ! j" "j < length vps"
          unfolding in_set_conv_nth by auto
        moreover
        assume eq: "map v_at vps = [v_at vp'  ..< Suc u]"
        then have len: "length vps = Suc u - v_at vp'"
          by (auto dest!: arg_cong[where f=length])
        moreover
        have "v_at (vps ! j) = v_at vp' + j"
          using arg_cong[where f="\<lambda>xs. nth xs j", OF eq] j len
          by (auto simp: nth_append)
        ultimately have "l \<le> u"
          unfolding l_def by auto
        with Since hyps(2,3) have "\<forall>x\<in>fv \<psi>. v x = v' x \<or> v x \<notin> AD \<psi> l \<and> v' x \<notin> AD \<psi> l"
          by (auto simp: u_def dest!: bspec dest: AD_mono[THEN set_mp, rotated -1])
      }
      moreover
      { fix k
        assume k: "k \<le> i"
        with Since hyps(2,3) have "\<forall>x\<in>fv \<phi>. v x = v' x \<or> v x \<notin> AD \<phi> k \<and> v' x \<notin> AD \<phi> k"
          by (auto dest!: bspec dest: AD_mono[THEN set_mp, rotated -1])
      }
      ultimately show ?thesis
        using Since VSince IH(20)[OF Since VSince refl refl, of v'] IH(21)[OF Since VSince refl _ refl, of _ v'] hyps(1,2)
        by (auto simp: Let_def le_diff_conv2 simp del: upt.simps)
    qed auto
  next
    case (VSinceInf j k vps)
    then show ?thesis
    proof (cases f)
      case (Since \<phi> I \<psi>)
      { fix vp :: "('n, 'd) vproof"
        define l and u where "l = v_at vp" and "u = LTP_p \<sigma> i I"
        assume *: "vp \<in> set vps" "\<tau> \<sigma> 0 + left I \<le> \<tau> \<sigma> i"
        then have u_def: "u = LTP_p_safe \<sigma> i I"
          by (auto simp: LTP_p_safe_def u_def)
        from *(1) obtain j where j: "vp = vps ! j" "j < length vps"
          unfolding in_set_conv_nth by auto
        moreover
        assume eq: "map v_at vps = [k ..< Suc u]"
        then have len: "length vps = Suc u - k"
          by (auto dest!: arg_cong[where f=length])
        moreover
        have "v_at (vps ! j) = k + j"
          using arg_cong[where f="\<lambda>xs. nth xs j", OF eq] j len *(2)
          by (auto simp: nth_append)
        ultimately have "l \<le> u"
          unfolding l_def by auto
        with Since hyps(2,3) have "\<forall>x\<in>fv \<psi>. v x = v' x \<or> v x \<notin> AD \<psi> l \<and> v' x \<notin> AD \<psi> l"
          by (auto simp: u_def dest!: bspec dest: AD_mono[THEN set_mp, rotated -1])
      }
      with Since VSinceInf show ?thesis
        using IH(22)[OF Since VSinceInf _ refl, of _ v'] hyps(1,2)
        by auto
    qed auto
  next
    case (VUntil j vps vp')
    then show ?thesis
    proof (cases f)
      case (Until \<phi> I \<psi>)
      { fix sp :: "('n, 'd) vproof"
        define l and u where "l = v_at sp" and "u = v_at vp'"
        assume *: "sp \<in> set vps" "v_at vp' \<le> LTP_f \<sigma> i (the_enat (right I))"
        from *(1) obtain j where j: "sp = vps ! j" "j < length vps"
          unfolding in_set_conv_nth by auto
        moreover
        assume eq: "map v_at vps = [ETP_f \<sigma> i I ..< Suc u]"
        then have "length vps = Suc u - ETP_f \<sigma> i I"
          by (auto dest!: arg_cong[where f=length])
        with j eq *(2) have "l \<le> LTP_f \<sigma> i (the_enat (right I))"
          by (auto simp: l_def u_def dest!: arg_cong[where f="\<lambda>xs. nth xs j"]
              simp del: upt.simps split: if_splits)
        with Until hyps(2,3) have "\<forall>x\<in>fv \<psi>. v x = v' x \<or> v x \<notin> AD \<psi> l \<and> v' x \<notin> AD \<psi> l"
          by (auto dest!: bspec dest: AD_mono[THEN set_mp, rotated -1])
      }
      moreover
      { fix k
        assume "k < LTP_f \<sigma> i (the_enat (right I))"
        then have "k \<le> LTP_f \<sigma> i (the_enat (right I)) - 1"
          by linarith
        with Until hyps(2,3) have "\<forall>x\<in>fv \<phi>. v x = v' x \<or> v x \<notin> AD \<phi> k \<and> v' x \<notin> AD \<phi> k"
          by (auto dest!: bspec dest: AD_mono[THEN set_mp, rotated -1])
      }
      ultimately show ?thesis
        using Until VUntil IH(23)[OF Until VUntil refl refl, of v'] IH(24)[OF Until VUntil refl _ refl, of _ v'] hyps(1,2)
        by (auto simp: Let_def le_diff_conv2 simp del: upt.simps)
    qed auto
  next
    case (VUntilInf j k vps)
    then show ?thesis
    proof (cases f)
      case (Until \<phi> I \<psi>)
      { fix vp :: "('n, 'd) vproof"
        define l and u where "l = v_at vp" and "u = LTP_f \<sigma> i (the_enat (right I))"
        assume *: "vp \<in> set vps"
        then obtain j where j: "vp = vps ! j" "j < length vps"
          unfolding in_set_conv_nth by auto
        assume eq: "map v_at vps = [ETP_f \<sigma> i I ..< Suc u]"
        then have "length vps = Suc u - ETP_f \<sigma> i I"
          by (auto dest!: arg_cong[where f=length])
        with j eq have "l \<le> LTP_f \<sigma> i (the_enat (right I))"
          by (auto simp: l_def u_def dest!: arg_cong[where f="\<lambda>xs. nth xs j"]
              simp del: upt.simps split: if_splits)
        with Until hyps(2,3) have "\<forall>x\<in>fv \<psi>. v x = v' x \<or> v x \<notin> AD \<psi> l \<and> v' x \<notin> AD \<psi> l"
          by (auto dest!: bspec dest: AD_mono[THEN set_mp, rotated -1])
      }
      with Until VUntilInf show ?thesis
        using IH(25)[OF Until VUntilInf _ refl, of _ v'] hyps(1,2)
        by auto
    qed auto
  qed (cases f; simp_all)+
qed

subsection \<open>Checker Completeness\<close>

lemma part_hd_tabulate: "distinct xs \<Longrightarrow> part_hd (tabulate xs f z) = (case xs of [] \<Rightarrow> z | (x # _) \<Rightarrow> (if set xs = UNIV then f x else z))"
  by (transfer, auto split: list.splits)

lemma s_at_tabulate:
  assumes "\<forall>z. s_at (mypick z) = i"
    and "mypart = tabulate (sorted_list_of_set (AD \<phi> i)) mypick (mypick (SOME z. z \<notin> AD \<phi> i))"
  shows "\<forall>(sub, vp) \<in> SubsVals mypart. s_at vp = i"
  using assms by (transfer, auto)

lemma v_at_tabulate:
  assumes "\<forall>z. v_at (mypick z) = i"
    and "mypart = tabulate (sorted_list_of_set (AD \<phi> i)) mypick (mypick (SOME z. z \<notin> AD \<phi> i))"
  shows "\<forall>(sub, vp) \<in> SubsVals mypart. v_at vp = i"
  using assms by (transfer, auto)

lemma s_check_tabulate:
  assumes "future_bounded \<phi>"
    and "\<forall>z. s_at (mypick z) = i"
    and "\<forall>z. s_check (v(x:=z)) \<phi> (mypick z)"
    and "mypart = tabulate (sorted_list_of_set (AD \<phi> i)) mypick (mypick (SOME z. z \<notin> AD \<phi> i))"
  shows "\<forall>(sub, vp) \<in> SubsVals mypart. \<forall>z \<in> sub. s_check (v(x := z)) \<phi> vp"
  using assms
proof (transfer fixing: \<sigma> \<phi> mypick i v x, goal_cases 1)
  case (1 mypart)
  { fix z
    assume s_at_assm: "\<forall>z. s_at (mypick z) = i"
      and s_check_assm: "\<forall>z. s_check (v(x := z)) \<phi> (mypick z)"
      and fb_assm: "future_bounded \<phi>"
      and z_notin_AD: "z \<notin> (AD \<phi> i)"
    have s_at_mypick: "s_at (mypick (SOME z. z \<notin> local.AD \<phi> i)) = i"
      using s_at_assm by simp
    have s_check_mypick: "Checker.s_check \<sigma> (v(x := SOME z. z \<notin> AD \<phi> i)) \<phi> (mypick (SOME z. z \<notin> AD \<phi> i))"
      using s_check_assm by simp
    have "s_check (v(x := z)) \<phi> (mypick (SOME z. z \<notin> AD \<phi> i))"
      using z_notin_AD
      by (subst check_AD_cong(1)[of \<phi> "v(x := z)" "v(x := (SOME z. z \<notin> Checker.AD \<sigma> \<phi> i))" i "mypick (SOME z. z \<notin> AD \<phi> i)", OF fb_assm _ s_at_mypick])
        (auto simp add: someI[of "\<lambda>z. z \<notin> AD \<phi> i" z] s_check_mypick fb_assm split: if_splits)
  }
  with 1 show ?case
    by auto
qed

lemma v_check_tabulate:
  assumes "future_bounded \<phi>"
    and "\<forall>z. v_at (mypick z) = i"
    and "\<forall>z. v_check (v(x:=z)) \<phi> (mypick z)"
    and "mypart = tabulate (sorted_list_of_set (AD \<phi> i)) mypick (mypick (SOME z. z \<notin> AD \<phi> i))"
  shows "\<forall>(sub, vp) \<in> SubsVals mypart. \<forall>z \<in> sub. v_check (v(x := z)) \<phi> vp"
  using assms
proof (transfer fixing: \<sigma> \<phi> mypick i v x, goal_cases 1)
  case (1 mypart)
  { fix z
    assume v_at_assm: "\<forall>z. v_at (mypick z) = i"
      and v_check_assm: "\<forall>z. v_check (v(x := z)) \<phi> (mypick z)"
      and fb_assm: "future_bounded \<phi>"
      and z_notin_AD: "z \<notin> (AD \<phi> i)"
    have v_at_mypick: "v_at (mypick (SOME z. z \<notin> local.AD \<phi> i)) = i"
      using v_at_assm by simp
    have v_check_mypick: "Checker.v_check \<sigma> (v(x := SOME z. z \<notin> AD \<phi> i)) \<phi> (mypick (SOME z. z \<notin> AD \<phi> i))"
      using v_check_assm by simp
    have "v_check (v(x := z)) \<phi> (mypick (SOME z. z \<notin> AD \<phi> i))"
      using z_notin_AD
      by (subst check_AD_cong(2)[of \<phi> "v(x := z)" "v(x := (SOME z. z \<notin> Checker.AD \<sigma> \<phi> i))" i "mypick (SOME z. z \<notin> AD \<phi> i)", OF fb_assm _ v_at_mypick])
        (auto simp add: someI[of "\<lambda>z. z \<notin> AD \<phi> i" z] v_check_mypick fb_assm split: if_splits)
  }
  with 1 show ?case
    by auto
qed

lemma s_at_part_hd_tabulate:
  assumes "future_bounded \<phi>"
    and "\<forall>z. s_at (f z) = i"
    and "mypart = tabulate (sorted_list_of_set (AD \<phi> i)) f (f (SOME z. z \<notin> AD \<phi> i))"
  shows "s_at (part_hd mypart) = i"
  using assms by (simp add: part_hd_tabulate split: list.splits)

lemma v_at_part_hd_tabulate:
  assumes "future_bounded \<phi>"
    and "\<forall>z. v_at (f z) = i"
    and "mypart = tabulate (sorted_list_of_set (AD \<phi> i)) f (f (SOME z. z \<notin> AD \<phi> i))"
  shows "v_at (part_hd mypart) = i"
  using assms by (simp add: part_hd_tabulate split: list.splits)

lemma check_completeness_aux:
  "(SAT \<sigma> v i \<phi> \<longrightarrow> future_bounded \<phi> \<longrightarrow> (\<exists>sp. s_at sp = i \<and> s_check v \<phi> sp)) \<and>
   (VIO \<sigma> v i \<phi> \<longrightarrow> future_bounded \<phi> \<longrightarrow> (\<exists>vp. v_at vp = i \<and> v_check v \<phi> vp))"
proof (induct v i \<phi> rule: SAT_VIO.induct)
  case (STT v i)
  then show ?case
    by (auto intro!: exI[of _ "STT i"])
next
  case (VFF v i)
  then show ?case
    by (auto intro!: exI[of _ "VFF i"])
next
  case (SPred r v ts i)
  then show ?case
    by (auto intro!: exI[of _ "SPred i r ts"])
next
  case (VPred r v ts i)
  then show ?case
    by (auto intro!: exI[of _ "VPred i r ts"])
next
  case (SEq_Const v x c i)
  then show ?case
    by (auto intro!: exI[of _ "SEq_Const i x c"])
next
  case (VEq_Const v x c i)
  then show ?case
    by (auto intro!: exI[of _ "VEq_Const i x c"])
next
  case (SNeg v i \<phi>)
  then show ?case
    by (auto intro: exI[of _ "SNeg _"])
next
  case (VNeg v i \<phi>)
  then show ?case
    by (auto intro: exI[of _ "VNeg _"])
next
  case (SOrL v i \<phi> \<psi>)
  then show ?case
    by (auto intro: exI[of _ "SOrL _"])
next
  case (SOrR v i \<psi> \<phi>)
  then show ?case
    by (auto intro: exI[of _ "SOrR _"])
next
  case (VOr v i \<phi> \<psi>)
  then show ?case
    by (auto 0 3 intro: exI[of _ "VOr _ _"])
next
  case (SAnd v i \<phi> \<psi>)
  then show ?case
    by (auto 0 3 intro: exI[of _ "SAnd _ _"])
next
  case (VAndL v i \<phi> \<psi>)
  then show ?case
    by (auto intro: exI[of _ "VAndL _"])
next
  case (VAndR v i \<psi> \<phi>)
  then show ?case
    by (auto intro: exI[of _ "VAndR _"])
next
  case (SImpL v i \<phi> \<psi>)
  then show ?case
    by (auto intro: exI[of _ "SImpL _"])
next
  case (SImpR v i \<psi> \<phi>)
  then show ?case
    by (auto intro: exI[of _ "SImpR _"])
next
  case (VImp v i \<phi> \<psi>)
  then show ?case
    by (auto 0 3 intro: exI[of _ "VImp _ _"])
next
  case (SIffSS v i \<phi> \<psi>)
  then show ?case
    by (auto 0 3 intro: exI[of _ "SIffSS _ _"])
next
  case (SIffVV v i \<phi> \<psi>)
  then show ?case
    by (auto 0 3 intro: exI[of _ "SIffVV _ _"])
next
  case (VIffSV v i \<phi> \<psi>)
  then show ?case
    by (auto 0 3 intro: exI[of _ "VIffSV _ _"])
next
  case (VIffVS v i \<phi> \<psi>)
  then show ?case
    by (auto 0 3 intro: exI[of _ "VIffVS _ _"])
next
  case (SExists v x i \<phi>)
  then show ?case
    by (auto 0 3 simp: fun_upd_def intro: exI[of _ "SExists x _ _"])
next
  case (VExists v x i \<phi>)
  show ?case
  proof
    assume "future_bounded (\<exists>\<^sub>Fx.  \<phi>)"
    then have fb: "future_bounded \<phi>"
      by simp
    obtain mypick where mypick_def: "v_at (mypick z) = i \<and> v_check (v(x:=z)) \<phi> (mypick z)" for z
      using VExists fb by metis
    define mypart where "mypart = tabulate (sorted_list_of_set (AD \<phi> i)) mypick (mypick (SOME z. z \<notin> (AD \<phi> i)))"
    have mypick_at: "\<forall>z. v_at (mypick z) = i"
      by (simp add: mypick_def)
    have mypick_v_check: "\<forall>z. v_check (v(x:=z)) \<phi> (mypick z)"
      by (simp add: mypick_def)
    have mypick_v_check2: "\<forall>z. v_check (v(x := (SOME z. z \<notin> AD \<phi> i))) \<phi> (mypick (SOME z. z \<notin> AD \<phi> i))"
      by (simp add: mypick_def)
    have v_at_myp: "v_at (VExists x mypart) = i"
      using v_at_part_hd_tabulate[OF fb, of mypick i]
      by (simp add: mypart_def mypick_def)
    have v_check_myp: "v_check v (\<exists>\<^sub>Fx.  \<phi>) (VExists x mypart)"
      using v_at_tabulate[of mypick i _ \<phi>, OF mypick_at]
        v_check_tabulate[OF fb mypick_at mypick_v_check]
      by (auto simp add: mypart_def v_at_part_hd_tabulate[OF fb mypick_at])
    show "\<exists>vp. v_at vp = i \<and> v_check v (\<exists>\<^sub>Fx.  \<phi>) vp"
      using v_at_myp v_check_myp by blast
  qed
next
  case (SForall v x i \<phi>)
  show ?case
  proof
    assume "future_bounded (\<forall>\<^sub>Fx.  \<phi>)"
    then have fb: "future_bounded \<phi>"
      by simp
    obtain mypick where mypick_def: "s_at (mypick z) = i \<and> s_check (v(x:=z)) \<phi> (mypick z)" for z
      using SForall fb by metis
    define mypart where "mypart = tabulate (sorted_list_of_set (AD \<phi> i)) mypick (mypick (SOME z. z \<notin> (AD \<phi> i)))"
    have mypick_at: "\<forall>z. s_at (mypick z) = i"
      by (simp add: mypick_def)
    have mypick_s_check: "\<forall>z. s_check (v(x:=z)) \<phi> (mypick z)"
      by (simp add: mypick_def)
    have mypick_s_check2: "\<forall>z. s_check (v(x := (SOME z. z \<notin> AD \<phi> i))) \<phi> (mypick (SOME z. z \<notin> AD \<phi> i))"
      by (simp add: mypick_def)
    have s_at_myp: "s_at (SForall x mypart) = i"
      using s_at_part_hd_tabulate[OF fb, of mypick i]
      by (simp add: mypart_def mypick_def)
    have s_check_myp: "s_check v (\<forall>\<^sub>Fx.  \<phi>) (SForall x mypart)"
      using s_at_tabulate[of mypick i _ \<phi>, OF mypick_at]
        s_check_tabulate[OF fb mypick_at mypick_s_check]
      by (auto simp add: mypart_def s_at_part_hd_tabulate[OF fb mypick_at])
    show "\<exists>sp. s_at sp = i \<and> s_check v (\<forall>\<^sub>Fx.  \<phi>) sp"
      using s_at_myp s_check_myp by blast
  qed
next
  case (VForall v x i \<phi>)
  then show ?case
    by (auto 0 3 simp: fun_upd_def intro: exI[of _ "VForall x _ _"])
next
  case (SPrev i I v \<phi>)
  then show ?case
    by (force intro: exI[of _ "SPrev _"])
next
  case (VPrev i v \<phi> I)
  then show ?case
    by (force intro: exI[of _ "VPrev _"])
next
  case (VPrevZ i v I \<phi>)
  then show ?case
    by (auto intro!: exI[of _ "VPrevZ"])
next
  case (VPrevOutL i I v \<phi>)
  then show ?case
    by (auto intro!: exI[of _ "VPrevOutL i"])
next
  case (VPrevOutR i I v \<phi>)
  then show ?case
    by (auto intro!: exI[of _ "VPrevOutR i"])
next
  case (SNext i I v \<phi>)
  then show ?case
    by (force simp: Let_def intro: exI[of _ "SNext _"])
next
  case (VNext v i \<phi> I)
  then show ?case
    by (force simp: Let_def intro: exI[of _ "VNext _"])
next
  case (VNextOutL i I v \<phi>)
  then show ?case
    by (auto intro!: exI[of _ "VNextOutL i"])
next
  case (VNextOutR i I v \<phi>)
  then show ?case
    by (auto intro!: exI[of _ "VNextOutR i"])
next
  case (SOnce j i I v \<phi>)
  then show ?case
    by (auto simp: Let_def intro: exI[of _ "SOnce i _"])
next
  case (VOnceOut i I v \<phi>)
  then show ?case
    by (auto intro!: exI[of _ "VOnceOut i"])
next
  case (VOnce j I i v \<phi>)
  show ?case
  proof
    assume "future_bounded (\<^bold>P I \<phi>)"
    then have fb: "future_bounded \<phi>"
      by simp
    obtain mypick where mypick_def: "\<forall>k \<in> {j .. LTP_p \<sigma> i I}. v_at (mypick k) = k \<and> v_check v \<phi> (mypick k)"
      using VOnce fb by metis
    then obtain vps where vps_def: "map (v_at) vps = [j ..< Suc (LTP_p \<sigma> i I)] \<and> (\<forall>vp \<in> set vps. v_check v \<phi> vp)"
      by atomize_elim (auto intro!: trans[OF list.map_cong list.map_id] exI[of _ "map mypick ([j ..< Suc (LTP_p \<sigma> i I)])"])
    then have "v_at (VOnce i j vps) = i \<and> v_check v (\<^bold>P I \<phi>) (VOnce i j vps)"
      using VOnce by auto
    then show "\<exists>vp. v_at vp = i \<and> v_check v (\<^bold>P I \<phi>) vp"
      by blast
  qed
next
  case (SEventually j i I v \<phi>)
  then show ?case
    by (auto simp: Let_def intro: exI[of _ "SEventually i _"])
next
  case (VEventually I i v \<phi>)
  show ?case
  proof
    assume fb_eventually: "future_bounded (\<^bold>F I \<phi>)"
    then have fb: "future_bounded \<phi>"
      by simp
    obtain b where b_def: "right I = enat b"
      using fb_eventually by (atomize_elim, cases "right I") auto
    define j where j_def: "j = LTP \<sigma> (\<tau> \<sigma> i + b)"
    obtain mypick where mypick_def: "\<forall>k \<in> {ETP_f \<sigma> i I .. j}. v_at (mypick k) = k \<and> v_check v \<phi> (mypick k)"
      using VEventually fb_eventually unfolding b_def j_def enat.simps
      by atomize_elim (rule bchoice, simp)
    then obtain vps where vps_def: "map (v_at) vps = [ETP_f \<sigma> i I ..< Suc j] \<and> (\<forall>vp \<in> set vps. v_check v \<phi> vp)"
      by atomize_elim (auto intro!: trans[OF list.map_cong list.map_id] exI[of _ "map mypick ([ETP_f \<sigma> i I ..< Suc j])"])
    then have "v_at (VEventually i j vps) = i \<and> v_check v (\<^bold>F I \<phi>) (VEventually i j vps)"
      using VEventually b_def j_def by simp
    then show "\<exists>vp. v_at vp = i \<and> v_check v (\<^bold>F I \<phi>) vp"
      by blast
  qed
next
  case (SHistorically j I i v \<phi>)
  show ?case
  proof
    assume fb_historically: "future_bounded (\<^bold>H I \<phi>)"
    then have fb: "future_bounded \<phi>"
      by simp
    obtain mypick where mypick_def: "\<forall>k \<in> {j .. LTP_p \<sigma> i I}. s_at (mypick k) = k \<and> s_check v \<phi> (mypick k)"
      using SHistorically fb by metis
    then obtain sps where sps_def: "map (s_at) sps = [j ..< Suc (LTP_p \<sigma> i I)] \<and> (\<forall>sp \<in> set sps. s_check v \<phi> sp)"
      by atomize_elim (auto intro!: trans[OF list.map_cong list.map_id] exI[of _ "map mypick ([j ..< Suc (LTP_p \<sigma> i I)])"])
    then have "s_at (SHistorically i j sps) = i \<and> s_check v (\<^bold>H I \<phi>) (SHistorically i j sps)"
      using SHistorically by auto
    then show "\<exists>sp. s_at sp = i \<and> s_check v (\<^bold>H I \<phi>) sp"
      by blast
  qed
next
  case (SHistoricallyOut i I v \<phi>)
  then show ?case
    by (auto intro!: exI[of _ "SHistoricallyOut i"])
next
  case (VHistorically j i I v \<phi>)
  then show ?case
    by (auto simp: Let_def intro: exI[of _ "VHistorically i _"])
next
  case (SAlways I i v \<phi>)
  show ?case
  proof
    assume fb_always: "future_bounded (\<^bold>G I \<phi>)"
    then have fb: "future_bounded \<phi>"
      by simp
    obtain b where b_def: "right I = enat b"
      using fb_always by (atomize_elim, cases "right I") auto
    define j where j_def: "j = LTP \<sigma> (\<tau> \<sigma> i + b)"
    obtain mypick where mypick_def: "\<forall>k \<in> {ETP_f \<sigma> i I .. j}. s_at (mypick k) = k \<and> s_check v \<phi> (mypick k)"
      using SAlways fb_always unfolding b_def j_def enat.simps
      by atomize_elim (rule bchoice, simp)
    then obtain sps where sps_def: "map (s_at) sps = [ETP_f \<sigma> i I ..< Suc j] \<and> (\<forall>sp \<in> set sps. s_check v \<phi> sp)"
      by atomize_elim (auto intro!: trans[OF list.map_cong list.map_id] exI[of _ "map mypick ([ETP_f \<sigma> i I ..< Suc j])"])
    then have "s_at (SAlways i j sps) = i \<and> s_check v (\<^bold>G I \<phi>) (SAlways i j sps)"
      using SAlways b_def j_def by simp
    then show "\<exists>sp. s_at sp = i \<and> s_check v (\<^bold>G I \<phi>) sp"
      by blast
  qed
next
  case (VAlways j i I v \<phi>)
  then show ?case
    by (auto simp: Let_def intro: exI[of _ "VAlways i _"])
next
  case (SSince j i I v \<psi> \<phi>)
  show ?case
  proof
    assume fb_since: "future_bounded (\<phi> \<^bold>S I \<psi>)"
    then have fb: "future_bounded \<phi>" "future_bounded \<psi>"
      by simp_all
    obtain sp2 where sp2_def: "s_at sp2 = j \<and> s_check v \<psi> sp2"
      using SSince fb_since by auto
    {
      assume "Suc j > i"
      then have "s_at (SSince sp2 []) = i \<and> s_check v (\<phi> \<^bold>S I \<psi>) (SSince sp2 [])"
        using sp2_def SSince by auto
      then have "\<exists>sp. s_at sp = i \<and> s_check v (\<phi> \<^bold>S I \<psi>) sp"
        by blast
    }
    moreover
    {
      assume sucj_leq_i: "Suc j \<le> i"
      obtain mypick where mypick_def: "\<forall>k \<in> {Suc j ..< Suc i}. s_at (mypick k) = k \<and> s_check v \<phi> (mypick k)"
        using SSince fb_since by atomize_elim (rule bchoice, simp)
      then obtain sp1s where sp1s_def: "map (s_at) sp1s = [Suc j ..< Suc i] \<and> (\<forall>sp \<in> set sp1s. s_check v \<phi> sp)"
        by atomize_elim (auto intro!: trans[OF list.map_cong list.map_id] exI[of _ "map mypick ([Suc j ..< Suc i])"])
      then have "sp1s \<noteq> []"
        using sucj_leq_i by auto
      then have "s_at (SSince sp2 sp1s) = i \<and> s_check v (\<phi> \<^bold>S I \<psi>) (SSince sp2 sp1s)"
        using SSince sucj_leq_i fb sp2_def sp1s_def
        by (clarsimp simp add:
          Cons_eq_upt_conv append_eq_Cons_conv map_eq_append_conv
          split: list.splits) auto
      then have "\<exists>sp. s_at sp = i \<and> s_check v (\<phi> \<^bold>S I \<psi>) sp"
        by blast
    }
    ultimately show "\<exists>sp. s_at sp = i \<and> s_check v (\<phi> \<^bold>S I \<psi>) sp"
      using not_less by blast
  qed
next
  case (VSinceOut i I v \<phi> \<psi>)
  then show ?case
    by (auto intro!: exI[of _ "VSinceOut i"])
next
  case (VSince I i j v \<phi> \<psi>)
  show ?case
  proof
    assume fb_since: "future_bounded (\<phi> \<^bold>S I \<psi>)"
    then have fb: "future_bounded \<phi>" "future_bounded \<psi>"
      by simp_all
    obtain vp1 where vp1_def: "v_at vp1 = j \<and> v_check v \<phi> vp1"
      using fb_since VSince by auto
    obtain mypick where mypick_def: "\<forall>k \<in> {j .. LTP_p \<sigma> i I}. v_at (mypick k) = k \<and> v_check v \<psi> (mypick k)"
      using VSince fb_since by atomize_elim (rule bchoice, simp)
    then obtain vp2s where vp2s_def: "map (v_at) vp2s = [j ..< Suc (LTP_p \<sigma> i I)] \<and> (\<forall>vp \<in> set vp2s. v_check v \<psi> vp)"
      by atomize_elim (auto intro!: trans[OF list.map_cong list.map_id] exI[of _ "map mypick ([j ..< Suc (LTP_p \<sigma> i I)])"])
    then have "v_at (VSince i vp1 vp2s) = i \<and> v_check v (\<phi> \<^bold>S I \<psi>) (VSince i vp1 vp2s)"
      using vp1_def VSince by auto
    then show "\<exists>vp. v_at vp = i \<and> v_check v (\<phi> \<^bold>S I \<psi>) vp"
      by blast
  qed
next
  case (VSinceInf j I i v \<psi> \<phi>)
  show ?case
  proof
    assume fb_since: "future_bounded (\<phi> \<^bold>S I \<psi>)"
    then have fb: "future_bounded \<phi>" "future_bounded \<psi>"
      by simp_all
    obtain mypick where mypick_def: "\<forall>k \<in> {j .. LTP_p \<sigma> i I}. v_at (mypick k) = k \<and> v_check v \<psi> (mypick k)"
      using VSinceInf fb_since by atomize_elim (rule bchoice, simp)
    then obtain vp2s where vp2s_def: "map (v_at) vp2s = [j ..< Suc (LTP_p \<sigma> i I)] \<and> (\<forall>vp \<in> set vp2s. v_check v \<psi> vp)"
      by atomize_elim (auto intro!: trans[OF list.map_cong list.map_id] exI[of _ "map mypick ([j ..< Suc (LTP_p \<sigma> i I)])"])
    then have "v_at (VSinceInf i j vp2s) = i \<and> v_check v (\<phi> \<^bold>S I \<psi>) (VSinceInf i j vp2s)"
      using VSinceInf by auto
    then show "\<exists>vp. v_at vp = i \<and> v_check v (\<phi> \<^bold>S I \<psi>) vp"
      by blast
  qed
next
  case (SUntil j i I v \<psi> \<phi>)
  show ?case
  proof
    assume fb_until: "future_bounded (\<phi> \<^bold>U I \<psi>)"
    then have fb: "future_bounded \<phi>" "future_bounded \<psi>"
      by simp_all
    obtain sp2 where sp2_def: "s_at sp2 = j \<and> s_check v \<psi> sp2"
      using fb SUntil by blast
    {
      assume "i \<ge> j"
      then have "s_at (SUntil [] sp2) = i \<and> s_check v (\<phi> \<^bold>U I \<psi>) (SUntil [] sp2)"
        using sp2_def SUntil by auto
      then have "\<exists>sp. s_at sp = i \<and> s_check v (\<phi> \<^bold>U I \<psi>) sp"
        by blast
    }
    moreover
    {
      assume i_l_j: "i < j"
      obtain mypick where mypick_def: "\<forall>k \<in> {i ..< j}. s_at (mypick k) = k \<and> s_check v \<phi> (mypick k)"
        using SUntil fb_until by atomize_elim (rule bchoice, simp)
      then obtain sp1s where sp1s_def: "map (s_at) sp1s = [i ..< j] \<and> (\<forall>sp \<in> set sp1s. s_check v \<phi> sp)"
        by atomize_elim (auto intro!: trans[OF list.map_cong list.map_id] exI[of _ "map mypick ([i ..< j])"])
      then have "s_at (SUntil sp1s sp2) = i \<and> s_check v (\<phi> \<^bold>U I \<psi>) (SUntil sp1s sp2)"
        using SUntil fb_until sp2_def sp1s_def i_l_j
        by (clarsimp simp add: append_eq_Cons_conv map_eq_append_conv split: list.splits)
          (auto simp: Cons_eq_upt_conv dest!: upt_eq_Nil_conv[THEN iffD1, OF sym])
      then have "\<exists>sp. s_at sp = i \<and> s_check v (\<phi> \<^bold>U I \<psi>) sp"
        by blast
    }
    ultimately show "\<exists>sp. s_at sp = i \<and> s_check v (\<phi> \<^bold>U I \<psi>) sp"
      using not_less by blast
  qed
next
  case (VUntil I j i v \<phi> \<psi>)
  show ?case
  proof
    assume fb_until: "future_bounded (\<phi> \<^bold>U I \<psi>)"
    then have fb: "future_bounded \<phi>" "future_bounded \<psi>"
      by simp_all
    obtain vp1 where vp1_def: "v_at vp1 = j \<and> v_check v \<phi> vp1"
      using VUntil fb_until by auto
    obtain mypick where mypick_def: "\<forall>k \<in> {ETP_f \<sigma> i I .. j}. v_at (mypick k) = k \<and> v_check v \<psi> (mypick k)"
      using VUntil fb_until by atomize_elim (rule bchoice, simp)
    then obtain vp2s where vp2s_def: "map (v_at) vp2s = [ETP_f \<sigma> i I ..< Suc j] \<and> (\<forall>vp \<in> set vp2s. v_check v \<psi> vp)"
      by atomize_elim (auto intro!: trans[OF list.map_cong list.map_id] exI[of _ "map mypick ([ETP_f \<sigma> i I ..< Suc j])"])
    then have "v_at (VUntil i vp2s vp1) = i \<and> v_check v (\<phi> \<^bold>U I \<psi>) (VUntil i vp2s vp1)"
      using VUntil fb_until vp1_def by simp
    then show "\<exists>vp. v_at vp = i \<and> v_check v (\<phi> \<^bold>U I \<psi>) vp"
      by blast
  qed
next
  case (VUntilInf I i v \<psi> \<phi>)
  show ?case
  proof
    assume fb_until: "future_bounded (\<phi> \<^bold>U I \<psi>)"
    then have fb: "future_bounded \<phi>" "future_bounded \<psi>"
      by simp_all
    obtain b where b_def: "right I = enat b"
      using fb_until by (atomize_elim, cases "right I") auto
    define j where j_def: "j = LTP \<sigma> (\<tau> \<sigma> i + b)"
    obtain mypick where mypick_def: "\<forall>k \<in> {ETP_f \<sigma> i I .. j}. v_at (mypick k) = k \<and> v_check v \<psi> (mypick k)"
      using VUntilInf fb_until unfolding b_def j_def by atomize_elim (rule bchoice, simp)
    then obtain vp2s where vp2s_def: "map (v_at) vp2s = [ETP_f \<sigma> i I ..< Suc j] \<and> (\<forall>vp \<in> set vp2s. v_check v \<psi> vp)"
      by atomize_elim (auto intro!: trans[OF list.map_cong list.map_id] exI[of _ "map mypick ([ETP_f \<sigma> i I ..< Suc j])"])
    then have "v_at (VUntilInf i j vp2s) = i \<and> v_check v (\<phi> \<^bold>U I \<psi>) (VUntilInf i j vp2s)"
      using VUntilInf b_def j_def by simp
    then show "\<exists>vp. v_at vp = i \<and> v_check v (\<phi> \<^bold>U I \<psi>) vp"
      by blast
  qed
qed

lemmas check_completeness =
  conjunct1[OF check_completeness_aux, rule_format]
  conjunct2[OF check_completeness_aux, rule_format]

definition "p_check v \<phi> p = (case p of Inl sp \<Rightarrow> s_check v \<phi> sp | Inr vp \<Rightarrow> v_check v \<phi> vp)"
definition "p_check_exec vs \<phi> p = (case p of Inl sp \<Rightarrow> s_check_exec vs \<phi> sp | Inr vp \<Rightarrow> v_check_exec vs \<phi> vp)"

definition valid :: "('n, 'd) envset \<Rightarrow> nat \<Rightarrow> ('n, 'd) formula \<Rightarrow> ('n, 'd) proof \<Rightarrow> bool" where
  "valid vs i \<phi> p =
    (case p of
      Inl p \<Rightarrow> s_check_exec vs \<phi> p \<and> s_at p = i
    | Inr p \<Rightarrow> v_check_exec vs \<phi> p \<and> v_at p = i)"

end

subsection \<open>Lifting the Checker to PDTs\<close>

fun check_one where
  "check_one \<sigma> v \<phi> (Leaf p) = p_check \<sigma> v \<phi> p"
| "check_one \<sigma> v \<phi> (Node x part) = check_one \<sigma> v \<phi> (lookup_part part (v x))"

fun check_all_aux where
  "check_all_aux \<sigma> vs \<phi> (Leaf p) = p_check_exec \<sigma> vs \<phi> p"
| "check_all_aux \<sigma> vs \<phi> (Node x part) = (\<forall>(D, e) \<in> set (subsvals part). check_all_aux \<sigma> (vs(x := D)) \<phi> e)"

fun collect_paths_aux where
  "collect_paths_aux DS \<sigma> vs \<phi> (Leaf p) = (if p_check_exec \<sigma> vs \<phi> p then {} else rev ` DS)"
| "collect_paths_aux DS \<sigma> vs \<phi> (Node x part) = (\<Union>(D, e) \<in> set (subsvals part). collect_paths_aux (Cons D ` DS) \<sigma> (vs(x := D)) \<phi> e)"

lemma check_one_cong: "\<forall>x\<in>fv \<phi> \<union> vars e. v x = v' x \<Longrightarrow> check_one \<sigma> v \<phi> e = check_one \<sigma> v' \<phi> e"
proof (induct e arbitrary: v v')
  case (Leaf x)
  then show ?case
    by (auto simp: p_check_def check_fv_cong split: sum.splits)
next
  case (Node x part)
  from Node(2) have *: "v x = v' x"
    by simp
  from Node(2) show ?case
    unfolding check_one.simps *
    by (intro Node(1)) auto
qed

lemma check_all_aux_check_one: "\<forall>x. vs x \<noteq> {} \<Longrightarrow> distinct_paths e \<Longrightarrow> (\<forall>x \<in> vars e. vs x = UNIV) \<Longrightarrow>
  check_all_aux \<sigma> vs \<phi> e \<longleftrightarrow> (\<forall>v \<in> compatible_vals (fv \<phi>) vs. check_one \<sigma> v \<phi> e)"
proof (induct e arbitrary: vs)
  case (Node x part)
  show ?case
    unfolding check_all_aux.simps check_one.simps split_beta
  proof (safe, unfold fst_conv snd_conv, goal_cases LR RL)
    case (LR v)
    from Node(2-) fst_lookup[of "v x" part] LR(1)[rule_format, OF lookup_subsvals[of _ "v x"]] LR(2) show ?case
      by (subst (asm) Node(1))
         (auto 0 3 simp: compatible_vals_fun_upd dest!: bspec[of _ _ v]
            elim!: compatible_vals_antimono[THEN set_mp, rotated])
  next
    case (RL D e)
    from RL(2) obtain d where "d \<in> D"
      by transfer (force simp: partition_on_def image_iff)
    with RL show ?case
      using Node(2-) lookup_subsvals[of part d] lookup_part_Vals[of part d]
        lookup_part_from_subvals[of D e part d]
    proof (intro Node(1)[THEN iffD2, OF _ _ _ _ ballI], goal_cases _ _ _ _ compatible)
      case (compatible v)
      from compatible(2-) compatible(1)[THEN bspec, of "v(x := d)"] compatible(1)[THEN bspec, of v]
      show ?case
        using lookup_part_from_subvals[of D e part "v x"]
          fun_upd_in_compatible_vals_in[of v "fv \<phi>" x vs "v x"]
          check_one_cong[THEN iffD1, rotated -1, of \<sigma> "v(x := d)" \<phi> e v, simplified]
        by (auto simp: compatible_vals_fun_upd fun_upd_apply[of _ _ _ x]
          fun_upd_in_compatible_vals_notin split: if_splits
          simp del: fun_upd_apply)
    qed auto
  qed
qed (auto simp: p_check_exec_def p_check_def check_exec_check split: sum.splits)

definition check_all :: "('n, 'd :: {default, linorder}) trace \<Rightarrow> ('n, 'd) formula \<Rightarrow> ('n, 'd) expl \<Rightarrow> bool" where
  "check_all \<sigma> \<phi> e = (distinct_paths e \<and> check_all_aux \<sigma> (\<lambda>_. UNIV) \<phi> e)"

lemma check_one_alt: "check_one \<sigma> v \<phi> e = p_check \<sigma> v \<phi> (eval_pdt v e)"
  by (induct e) auto

lemma check_all_alt: "check_all \<sigma> \<phi> e = (distinct_paths e \<and> (\<forall>v. p_check \<sigma> v \<phi> (eval_pdt v e)))"
  unfolding check_all_def
  by (rule conj_cong[OF refl], subst check_all_aux_check_one)
    (auto simp: compatible_vals_def check_one_alt)

fun pdt_at where
  "pdt_at i (Leaf l) = (p_at l = i)"
| "pdt_at i (Node x part) = (\<forall>pdt \<in> Vals part. pdt_at i pdt)"

lemma pdt_at_p_at_eval_pdt: "pdt_at i e \<Longrightarrow> p_at (eval_pdt v e) = i"
  by (induct e) auto

lemma check_all_completeness_aux:
  fixes \<phi> :: "('n, 'd :: {default, linorder}) formula"
  shows "set vs \<subseteq> fv \<phi> \<Longrightarrow> future_bounded \<phi> \<Longrightarrow> distinct vs \<Longrightarrow>
  \<exists>e. pdt_at i e \<and> vars_order vs e \<and> (\<forall>v. (\<forall>x. x \<notin> set vs \<longrightarrow> v x = w x) \<longrightarrow> p_check \<sigma> v \<phi> (eval_pdt v e))"
proof (induct vs arbitrary: w)
  case Nil
  then show ?case
  proof (cases "sat \<sigma> w i \<phi>")
    case True
    then have "SAT \<sigma> w i \<phi>" by (rule completeness)
    with Nil obtain sp where "s_at sp = i" "s_check \<sigma> w \<phi> sp" by (blast dest: check_completeness)
    then show ?thesis
      by (intro exI[of _ "Leaf (Inl sp)"]) (auto simp: vars_order.intros p_check_def p_at_def)
  next
    case False
    then have "VIO \<sigma> w i \<phi>" by (rule completeness)
    with Nil obtain vp where "v_at vp = i" "v_check \<sigma> w \<phi> vp" by (blast dest: check_completeness)
    then show ?thesis
      by (intro exI[of _ "Leaf (Inr vp)"]) (auto simp: vars_order.intros p_check_def p_at_def)
  qed
next
  case (Cons x vs)
  define eq :: "('n \<Rightarrow> 'd) \<Rightarrow> ('n \<Rightarrow> 'd) \<Rightarrow> bool" where "eq = rel_fun (eq_onp (\<lambda>x. x \<notin> set vs)) (=)"
  from Cons have "\<forall>w. \<exists>e. pdt_at i e \<and> vars_order vs e \<and>
    (\<forall>v. (\<forall>x. x \<notin> set vs \<longrightarrow> v x = w x) \<longrightarrow> p_check \<sigma> v \<phi> (eval_pdt v e))" by simp
  then obtain pick :: "'d \<Rightarrow> ('n, 'd) expl" where pick: "pdt_at i (pick a)" "vars_order vs (pick a)" and
    eq_pick: "\<And>v. eq v (w(x := a)) \<Longrightarrow> p_check \<sigma> v \<phi> (eval_pdt v (pick a))" for a
    unfolding eq_def rel_fun_def eq_onp_def choice_iff
  proof (atomize_elim, elim exE, goal_cases pick_val)
    case (pick_val f)
    then show ?case
      by (auto intro!: exI[of _ "\<lambda>a. f (w(x := a))"])
  qed
  let ?a = "SOME z. z \<notin> AD \<sigma> \<phi> i"
  let ?AD = "sorted_list_of_set (AD \<sigma> \<phi> i)"
  show ?case
  proof (intro exI[of _ "Node x (tabulate ?AD pick (pick ?a))"] conjI allI impI,
    goal_cases pdt_at vars_order p_check)
    case (p_check w')
    have "w' x \<notin> AD \<sigma> \<phi> i \<Longrightarrow> ?a \<notin> AD \<sigma> \<phi> i"
      by (metis some_eq_imp)
    moreover have "eq (w'(x := ?a)) (w(x := ?a))"
      using p_check by (auto simp: eq_def rel_fun_def eq_onp_def)
    moreover have "eq w' (w(x := w' x))"
      using p_check by (auto simp: eq_def rel_fun_def eq_onp_def)
    ultimately show ?case
      using pick Cons(2-) eq_pick[of w' "w' x"] eq_pick[of "w'(x := ?a)" ?a]
        pdt_at_p_at_eval_pdt[of "i" "pick ?a" w'] eval_pdt_fun_upd[of vs "pick ?a" x w' ?a]
      by (auto simp: p_check_def p_at_def
        elim!: check_AD_cong[THEN iffD1, rotated -1, of _ _ _ _ _ i]
        split: if_splits sum.splits sum.splits)
  qed (use Cons(2-) pick in \<open>simp_all add: vars_order.intros\<close>)
qed

lemma check_all_completeness:
  fixes \<phi> :: "('n, 'd :: {default, linorder}) formula"
  assumes "future_bounded \<phi>"
  shows "\<exists>e. pdt_at i e \<and> check_all \<sigma> \<phi> e"
proof -
  obtain vs where vs[simp]: "distinct vs" "set vs = fv \<phi>"
    by (meson finite_distinct_list finite_fv)
  have s: "s_check \<sigma> v \<phi> sp"
    if "vars_order vs e"
    and "\<forall>v. (\<forall>sp. eval_pdt v e = Inl sp \<longrightarrow> (\<exists>x. x \<notin> fv \<phi> \<and> v x \<noteq> undefined) \<or> s_check \<sigma> v \<phi> sp) \<and>
             (\<forall>vp. eval_pdt v e = Inr vp \<longrightarrow> (\<exists>x. x \<notin> fv \<phi> \<and> v x \<noteq> undefined) \<or> v_check \<sigma> v \<phi> vp)"
    and "eval_pdt v e = Inl sp" for e v sp
    using that eval_pdt_cong[of e v "\<lambda>x. if x \<in> fv \<phi> then v x else undefined"]
      check_fv_cong[of \<phi> v "\<lambda>x. if x \<in> fv \<phi> then v x else undefined"]
    by (auto dest!: spec[of _ sp] vars_order_vars simp: subset_eq)
  have v: "v_check \<sigma> v \<phi> vp"
    if "vars_order vs e"
    and "\<forall>v. (\<forall>sp. eval_pdt v e = Inl sp \<longrightarrow> (\<exists>x. x \<notin> fv \<phi> \<and> v x \<noteq> undefined) \<or> s_check \<sigma> v \<phi> sp) \<and>
             (\<forall>vp. eval_pdt v e = Inr vp \<longrightarrow> (\<exists>x. x \<notin> fv \<phi> \<and> v x \<noteq> undefined) \<or> v_check \<sigma> v \<phi> vp)"
    and "eval_pdt v e = Inr vp" for e v vp
    using that eval_pdt_cong[of e v "\<lambda>x. if x \<in> fv \<phi> then v x else undefined"]
      check_fv_cong[of \<phi> v "\<lambda>x. if x \<in> fv \<phi> then v x else undefined"]
    by (auto dest!: spec[of _ vp] vars_order_vars simp: subset_eq)
  show ?thesis
    using check_all_completeness_aux[of vs \<phi> i "\<lambda>_. undefined" \<sigma>] assms
    unfolding check_all_alt p_check_def
    by (auto elim!: exI [where P = "\<lambda>x. _ x \<and> _ x" , OF conjI] simp: vars_order_distinct_paths split: sum.splits intro: s v)
qed

lemma check_all_soundness_aux: "check_all \<sigma> \<phi> e \<Longrightarrow> p = eval_pdt v e \<Longrightarrow> isl p \<longleftrightarrow> sat \<sigma> v (p_at p) \<phi>"
  unfolding check_all_alt
  by (auto simp: isl_def p_check_def p_at_def dest!: spec[of _ v]
    dest: check_soundness soundness split: sum.splits)

lemma check_all_soundness: "check_all \<sigma> \<phi> e \<Longrightarrow> pdt_at i e \<Longrightarrow> isl (eval_pdt v e) \<longleftrightarrow> sat \<sigma> v i \<phi>"
  by (drule check_all_soundness_aux[OF _ refl, of _ _ _ v]) (auto simp: pdt_at_p_at_eval_pdt)

unbundle MFOTL_no_notation \<comment> \<open> disable notation \<close>

(*<*)
end
(*>*)