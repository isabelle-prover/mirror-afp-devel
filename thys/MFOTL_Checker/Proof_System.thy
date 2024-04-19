(*<*)
theory Proof_System
  imports Formula Partition
begin
(*>*)

section \<open>Proof System\<close>

unbundle MFOTL_notation

context begin

inductive SAT and VIO :: "('n, 'd) trace \<Rightarrow> ('n, 'd) env \<Rightarrow> nat \<Rightarrow> ('n, 'd) formula \<Rightarrow> bool" for \<sigma> where
  STT: "SAT \<sigma> v i TT"
| VFF: "VIO \<sigma> v i FF"
| SPred: "(r, eval_trms v ts) \<in> \<Gamma> \<sigma> i \<Longrightarrow> SAT \<sigma> v i (Pred r ts)"
| VPred: "(r, eval_trms v ts) \<notin> \<Gamma> \<sigma> i \<Longrightarrow> VIO \<sigma> v i (Pred r ts)"
| SEq_Const: "v x = c \<Longrightarrow> SAT \<sigma> v i (Eq_Const x c)"
| VEq_Const: "v x \<noteq> c \<Longrightarrow> VIO \<sigma> v i (Eq_Const x c)"
| SNeg: "VIO \<sigma> v i \<phi> \<Longrightarrow> SAT \<sigma> v i (Neg \<phi>)"
| VNeg: "SAT \<sigma> v i \<phi> \<Longrightarrow> VIO \<sigma> v i (Neg \<phi>)"
| SOrL: "SAT \<sigma> v i \<phi> \<Longrightarrow> SAT \<sigma> v i (Or \<phi> \<psi>)"
| SOrR: "SAT \<sigma> v i \<psi> \<Longrightarrow> SAT \<sigma> v i (Or \<phi> \<psi>)"
| VOr: "VIO \<sigma> v i \<phi> \<Longrightarrow> VIO \<sigma> v i \<psi> \<Longrightarrow> VIO \<sigma> v i (Or \<phi> \<psi>)"
| SAnd: "SAT \<sigma> v i \<phi> \<Longrightarrow> SAT \<sigma> v i \<psi> \<Longrightarrow> SAT \<sigma> v i (And \<phi> \<psi>)"
| VAndL: "VIO \<sigma> v i \<phi> \<Longrightarrow> VIO \<sigma> v i (And \<phi> \<psi>)"
| VAndR: "VIO \<sigma> v i \<psi> \<Longrightarrow> VIO \<sigma> v i (And \<phi> \<psi>)"
| SImpL: "VIO \<sigma> v i \<phi> \<Longrightarrow> SAT \<sigma> v i (Imp \<phi> \<psi>)"
| SImpR: "SAT \<sigma> v i \<psi> \<Longrightarrow> SAT \<sigma> v i (Imp \<phi> \<psi>)"
| VImp: "SAT \<sigma> v i \<phi> \<Longrightarrow> VIO \<sigma> v i \<psi> \<Longrightarrow> VIO \<sigma> v i (Imp \<phi> \<psi>)"
| SIffSS: "SAT \<sigma> v i \<phi> \<Longrightarrow> SAT \<sigma> v i \<psi> \<Longrightarrow> SAT \<sigma> v i (Iff \<phi> \<psi>)"
| SIffVV: "VIO \<sigma> v i \<phi> \<Longrightarrow> VIO \<sigma> v i \<psi> \<Longrightarrow> SAT \<sigma> v i (Iff \<phi> \<psi>)"
| VIffSV: "SAT \<sigma> v i \<phi> \<Longrightarrow> VIO \<sigma> v i \<psi> \<Longrightarrow> VIO \<sigma> v i (Iff \<phi> \<psi>)"
| VIffVS: "VIO \<sigma> v i \<phi> \<Longrightarrow> SAT \<sigma> v i \<psi> \<Longrightarrow> VIO \<sigma> v i (Iff \<phi> \<psi>)"
| SExists: "\<exists>z. SAT \<sigma> (v (x := z)) i \<phi> \<Longrightarrow> SAT \<sigma> v i (Exists x \<phi>)"
| VExists: "\<forall>z. VIO \<sigma> (v (x := z)) i \<phi> \<Longrightarrow> VIO \<sigma> v i (Exists x \<phi>)"
| SForall: "\<forall>z. SAT \<sigma> (v (x := z)) i \<phi> \<Longrightarrow> SAT \<sigma> v i (Forall x \<phi>)"
| VForall: "\<exists>z. VIO \<sigma> (v (x := z)) i \<phi> \<Longrightarrow> VIO \<sigma> v i (Forall x \<phi>)"
| SPrev: "i > 0 \<Longrightarrow> mem (\<Delta> \<sigma> i) I \<Longrightarrow> SAT \<sigma> v (i-1) \<phi> \<Longrightarrow> SAT \<sigma> v i (\<^bold>Y I \<phi>)"
| VPrev: "i > 0 \<Longrightarrow> VIO \<sigma> v (i-1) \<phi> \<Longrightarrow> VIO \<sigma> v i (\<^bold>Y I \<phi>)"
| VPrevZ: "i = 0 \<Longrightarrow> VIO \<sigma> v i (\<^bold>Y I \<phi>)"
| VPrevOutL: "i > 0 \<Longrightarrow> (\<Delta> \<sigma> i) < (left I) \<Longrightarrow> VIO \<sigma> v i (\<^bold>Y I \<phi>)"
| VPrevOutR: "i > 0 \<Longrightarrow> enat (\<Delta> \<sigma> i) > (right I) \<Longrightarrow> VIO \<sigma> v i (\<^bold>Y I \<phi>)"
| SNext: "mem (\<Delta> \<sigma> (i+1)) I \<Longrightarrow> SAT \<sigma> v (i+1) \<phi> \<Longrightarrow> SAT \<sigma> v i (\<^bold>X I \<phi>)"
| VNext: "VIO \<sigma> v (i+1) \<phi> \<Longrightarrow> VIO \<sigma> v i (\<^bold>X I \<phi>)"
| VNextOutL: "(\<Delta> \<sigma> (i+1)) < (left I) \<Longrightarrow> VIO \<sigma> v i (\<^bold>X I \<phi>)"
| VNextOutR: "enat (\<Delta> \<sigma> (i+1)) > (right I) \<Longrightarrow> VIO \<sigma> v i (\<^bold>X I \<phi>)"
| SOnce: "j \<le> i \<Longrightarrow> mem (\<delta> \<sigma> i j) I \<Longrightarrow> SAT \<sigma> v j \<phi> \<Longrightarrow> SAT \<sigma> v i (\<^bold>P I \<phi>)"
| VOnceOut: "\<tau> \<sigma> i < \<tau> \<sigma> 0 + left I \<Longrightarrow> VIO \<sigma> v i (\<^bold>P I \<phi>)"
| VOnce: "j = (case right I of \<infinity> \<Rightarrow> 0 
               | enat b \<Rightarrow> ETP_p \<sigma> i b) \<Longrightarrow>
          (\<tau> \<sigma> i) \<ge> (\<tau> \<sigma> 0) + left I \<Longrightarrow>
          (\<And>k. k \<in> {j .. LTP_p \<sigma> i I} \<Longrightarrow> VIO \<sigma> v k \<phi>) \<Longrightarrow> VIO \<sigma> v i (\<^bold>P I \<phi>)"
| SEventually: "j \<ge> i \<Longrightarrow> mem (\<delta> \<sigma> j i) I  \<Longrightarrow> SAT \<sigma> v j \<phi> \<Longrightarrow> SAT \<sigma> v i (\<^bold>F I \<phi>)"
| VEventually: "(\<And>k. k \<in> (case right I of \<infinity> \<Rightarrow> {ETP_f \<sigma> i I ..}
                           | enat b \<Rightarrow> {ETP_f \<sigma> i I .. LTP_f \<sigma> i b}) \<Longrightarrow> VIO \<sigma> v k \<phi>) \<Longrightarrow> 
                VIO \<sigma> v i (\<^bold>F I \<phi>)"
| SHistorically: "j = (case right I of \<infinity> \<Rightarrow> 0
                       | enat b \<Rightarrow> ETP_p \<sigma> i b) \<Longrightarrow>
                 (\<tau> \<sigma> i) \<ge> (\<tau> \<sigma> 0) + left I \<Longrightarrow>
                 (\<And>k. k \<in> {j .. LTP_p \<sigma> i I} \<Longrightarrow> SAT \<sigma> v k \<phi>) \<Longrightarrow> SAT \<sigma> v i (\<^bold>H I \<phi>)"
| SHistoricallyOut: "\<tau> \<sigma> i < \<tau> \<sigma> 0 + left I \<Longrightarrow> SAT \<sigma> v i (\<^bold>H I \<phi>)"
| VHistorically: "j \<le> i \<Longrightarrow> mem (\<delta> \<sigma> i j) I  \<Longrightarrow> VIO \<sigma> v j \<phi> \<Longrightarrow> VIO \<sigma> v i (\<^bold>H I \<phi>)"
| SAlways: "(\<And>k. k \<in> (case right I of \<infinity> \<Rightarrow> {ETP_f \<sigma> i I ..} 
                       | enat b \<Rightarrow> {ETP_f \<sigma> i I .. LTP_f \<sigma> i b}) \<Longrightarrow> SAT \<sigma> v k \<phi>) \<Longrightarrow>
            SAT \<sigma> v i (\<^bold>G I \<phi>)"
| VAlways: "j \<ge> i \<Longrightarrow> mem (\<delta> \<sigma> j i) I  \<Longrightarrow> VIO \<sigma> v j \<phi> \<Longrightarrow> VIO \<sigma> v i (\<^bold>G I \<phi>)"
| SSince: "j \<le> i \<Longrightarrow> mem (\<delta> \<sigma> i j) I  \<Longrightarrow> SAT \<sigma> v j \<psi> \<Longrightarrow> (\<And>k. k \<in> {j <.. i} \<Longrightarrow> 
           SAT \<sigma> v k \<phi>) \<Longrightarrow> SAT \<sigma> v i (\<phi> \<^bold>S I \<psi>)"
| VSinceOut: "\<tau> \<sigma> i < \<tau> \<sigma> 0 + left I \<Longrightarrow> VIO \<sigma> v i (\<phi> \<^bold>S I \<psi>)"
| VSince: "(case right I of \<infinity> \<Rightarrow> True 
            | enat b \<Rightarrow> ETP \<sigma> ((\<tau> \<sigma> i) - b) \<le> j) \<Longrightarrow> 
           j \<le> i \<Longrightarrow> (\<tau> \<sigma> 0) + left I \<le> (\<tau> \<sigma> i) \<Longrightarrow> VIO \<sigma> v j \<phi> \<Longrightarrow>
           (\<And>k. k \<in> {j .. (LTP_p \<sigma> i I)} \<Longrightarrow> VIO \<sigma> v k \<psi>) \<Longrightarrow> VIO \<sigma> v i (\<phi> \<^bold>S I \<psi>)"
| VSinceInf: "j = (case right I of \<infinity> \<Rightarrow> 0 
                   | enat b \<Rightarrow> ETP_p \<sigma> i b) \<Longrightarrow>
             (\<tau> \<sigma> i) \<ge> (\<tau> \<sigma> 0) + left I \<Longrightarrow> 
             (\<And>k. k \<in> {j .. LTP_p \<sigma> i I} \<Longrightarrow> VIO \<sigma> v k \<psi>) \<Longrightarrow> VIO \<sigma> v i (\<phi> \<^bold>S I \<psi>)"
| SUntil: "j \<ge> i \<Longrightarrow> mem (\<delta> \<sigma> j i) I  \<Longrightarrow> SAT \<sigma> v j \<psi> \<Longrightarrow> (\<And>k. k \<in> {i ..< j} \<Longrightarrow> SAT \<sigma> v k \<phi>) \<Longrightarrow> 
           SAT \<sigma> v i (\<phi> \<^bold>U I \<psi>)"
| VUntil: "(case right I of \<infinity> \<Rightarrow> True 
            | enat b \<Rightarrow> j < LTP_f \<sigma> i b) \<Longrightarrow> 
           j \<ge> i \<Longrightarrow> VIO \<sigma> v j \<phi> \<Longrightarrow> (\<And>k. k \<in> {ETP_f \<sigma> i I .. j} \<Longrightarrow> VIO \<sigma> v k \<psi>) \<Longrightarrow> 
           VIO \<sigma> v i (\<phi> \<^bold>U I \<psi>)"
| VUntilInf: "(\<And>k. k \<in> (case right I of \<infinity> \<Rightarrow> {ETP_f \<sigma> i I ..} 
                         | enat b \<Rightarrow> {ETP_f \<sigma> i I .. LTP_f \<sigma> i b}) \<Longrightarrow> VIO \<sigma> v k \<psi>) \<Longrightarrow>
              VIO \<sigma> v i (\<phi> \<^bold>U I \<psi>)"

subsection \<open>Soundness and Completeness\<close>

lemma not_sat_SinceD:
  assumes unsat: "\<not> \<langle>\<sigma>, v, i\<rangle> \<Turnstile> \<phi> \<^bold>S I \<psi>" and
    witness: "\<exists>j \<le> i. mem (\<tau> \<sigma> i - \<tau> \<sigma> j) I \<and> \<langle>\<sigma>, v, j\<rangle> \<Turnstile> \<psi>"
  shows "\<exists>j \<le> i. ETP \<sigma> (case right I of \<infinity> \<Rightarrow> 0 | enat n \<Rightarrow> \<tau> \<sigma> i - n) \<le> j \<and> \<not> \<langle>\<sigma>, v, j\<rangle> \<Turnstile> \<phi>
  \<and> (\<forall>k \<in> {j .. (min i (LTP \<sigma> (\<tau> \<sigma> i - left I)))}. \<not> \<langle>\<sigma>, v, k\<rangle> \<Turnstile> \<psi>)"
proof -
  define A and j where A_def: "A \<equiv> {j. j \<le> i \<and> mem (\<tau> \<sigma> i - \<tau> \<sigma> j) I \<and> \<langle>\<sigma>, v, j\<rangle> \<Turnstile> \<psi>}"
    and j_def: "j \<equiv> Max A"
  from witness have j: "j \<le> i" "\<langle>\<sigma>, v, j\<rangle> \<Turnstile> \<psi>" "mem (\<tau> \<sigma> i - \<tau> \<sigma> j) I"
    using Max_in[of A] unfolding j_def[symmetric] unfolding A_def
    by auto
  moreover
  from j(3) have "ETP \<sigma> (case right I of enat n \<Rightarrow> \<tau> \<sigma> i - n | \<infinity> \<Rightarrow> 0) \<le> j"
    unfolding ETP_def by (intro Least_le) (auto split: enat.splits)
  moreover
  { fix j
    assume j: "\<tau> \<sigma> j \<le> \<tau> \<sigma> i"
    then obtain k where k: "\<tau> \<sigma> i < \<tau> \<sigma> k"
      by (meson ex_le_\<tau> gt_ex less_le_trans)
    have "j \<le> ETP \<sigma> (Suc (\<tau> \<sigma> i))"
      unfolding ETP_def
    proof (intro LeastI2[of _ k "\<lambda>i. j \<le> i"])
      fix l
      assume "Suc (\<tau> \<sigma> i) \<le> \<tau> \<sigma> l"
      with j show "j \<le> l"
        by (metis lessI less_\<tau>D nless_le order_less_le_trans)
    qed (auto simp: Suc_le_eq k(1))
  } note * = this
  { fix k
    assume "k \<in> {j <.. (min i (LTP \<sigma> (\<tau> \<sigma> i - left I)))}"
    with j(3) have k: "j < k" "k \<le> i" "k \<le> Max {j. left I + \<tau> \<sigma> j \<le> \<tau> \<sigma> i}"
      by (auto simp: LTP_def le_diff_conv2 add.commute)
    with j(3) obtain l where "left I + \<tau> \<sigma> l \<le> \<tau> \<sigma> i" "k \<le> l"
      by (subst (asm) Max_ge_iff) (auto simp: le_diff_conv2 *
          intro!: finite_subset[of _ "{0 .. ETP \<sigma> (\<tau> \<sigma> i + 1)}"])
    then have "mem (\<tau> \<sigma> i - \<tau> \<sigma> k) I"
      using k(1,2) j(3)
      by (cases "right I") (auto simp: le_diff_conv le_diff_conv2 add.commute dest: \<tau>_mono
         elim: order_trans[rotated] order_trans)
    with Max_ge[of A k] k have "\<not> \<langle>\<sigma>, v, k\<rangle> \<Turnstile> \<psi>"
      unfolding j_def[symmetric] unfolding A_def
      by auto
  }
  ultimately show ?thesis using unsat
    by (auto dest!: spec[of _ j])
qed

lemma not_sat_UntilD:
  assumes unsat: "\<not> \<langle>\<sigma>, v, i\<rangle> \<Turnstile> \<phi> \<^bold>U I \<psi>"
    and witness: "\<exists>j \<ge> i. mem (\<delta> \<sigma> j i) I \<and> \<langle>\<sigma>, v, j\<rangle> \<Turnstile> \<psi>"
  shows "\<exists>j \<ge> i. (case right I of \<infinity> \<Rightarrow> True | enat n \<Rightarrow> j < LTP \<sigma> (\<tau> \<sigma> i + n))
  \<and> \<not> (\<langle>\<sigma>, v, j\<rangle> \<Turnstile> \<phi>) \<and> (\<forall>k \<in> {(max i (ETP \<sigma> (\<tau> \<sigma> i + left I))) .. j}.
   \<not> \<langle>\<sigma>, v, k\<rangle> \<Turnstile> \<psi>)"
proof -
  from \<tau>_mono have i0: "\<tau> \<sigma> 0 \<le> \<tau> \<sigma> i" by auto
  from witness obtain jmax where jmax: "jmax \<ge> i" "\<langle>\<sigma>, v, jmax\<rangle> \<Turnstile> \<psi>"
    "mem (\<delta> \<sigma> jmax i) I" by blast
  define A and j where A_def: "A \<equiv> {j. j \<ge> i \<and> j \<le> jmax
  \<and> mem (\<delta> \<sigma> j i) I \<and> \<langle>\<sigma>, v, j\<rangle> \<Turnstile> \<psi>}" and j_def: "j \<equiv> Min A"
  have j: "j \<ge> i" "\<langle>\<sigma>, v, j\<rangle> \<Turnstile> \<psi>" "mem (\<delta> \<sigma> j i) I"
    using A_def j_def jmax Min_in[of A]
    unfolding j_def[symmetric] unfolding A_def
    by fastforce+
  moreover have "case right I of \<infinity> \<Rightarrow> True | enat n \<Rightarrow> j \<le> LTP \<sigma> (\<tau> \<sigma> i + n)"
    using i0 j(1,3)
    by (auto simp: i_LTP_tau trans_le_add1 split: enat.splits)
  moreover
  { fix k
    assume k_def: "k \<in> {(max i (ETP \<sigma> (\<tau> \<sigma> i + left I))) ..< j}"
    then have ki: "\<tau> \<sigma> k \<ge> \<tau> \<sigma> i + left I" using i_ETP_tau by auto
    with k_def have kj: "k < j" by auto
    then have "\<tau> \<sigma> k \<le> \<tau> \<sigma> j" by auto
    then have "\<delta> \<sigma> k i \<le> \<delta> \<sigma> j i" by auto
    with this j(3) have "enat (\<delta> \<sigma> k i) \<le> right I"
      by (meson enat_ord_simps(1) order_subst2)
    with this ki j(3) have mem_k: "mem (\<delta> \<sigma> k i) I"
      unfolding ETP_def by (auto simp: Least_le)

    with j_def have "j \<le> jmax" using Min_in[of A]
      using jmax A_def
      by (metis (mono_tags, lifting) Collect_empty_eq
          finite_nat_set_iff_bounded_le mem_Collect_eq order_refl)
    with this k_def have kjm: "k \<le> jmax" by auto

    with this mem_k ki Min_le[of A k] k_def have "k \<notin> A"
      unfolding j_def[symmetric] unfolding A_def unfolding ETP_def
      using finite_nat_set_iff_bounded_le kj leD by blast
    with this mem_k k_def kjm have "\<not> \<langle>\<sigma>, v, k\<rangle> \<Turnstile> \<psi>"
      by (simp add: A_def) }
  ultimately show ?thesis using unsat
    by (auto split: enat.splits dest!: spec[of _ j])
qed

lemma soundness_raw: "(SAT \<sigma> v i \<phi> \<longrightarrow> \<langle>\<sigma>, v, i\<rangle> \<Turnstile> \<phi>) \<and> (VIO \<sigma> v i \<phi> \<longrightarrow> \<not> \<langle>\<sigma>, v, i\<rangle> \<Turnstile> \<phi>)"
proof (induct v i \<phi> rule: SAT_VIO.induct)
  case (VOnceOut i I v \<phi>)
  { fix j
    from \<tau>_mono have j0: "\<tau> \<sigma> 0 \<le> \<tau> \<sigma> j" by auto
    then have "\<tau> \<sigma> i < \<tau> \<sigma> j + left I" using VOnceOut by linarith
    then have "\<delta> \<sigma> i j < left I"
      using VOnceOut less_\<tau>D verit_comp_simplify1(3) by fastforce
    then have "\<not> mem (\<delta> \<sigma> i j) I" by auto }
  then show ?case
    by auto
next
  case (VOnce j I i v \<phi>)
  { fix k
    assume k_def: "\<langle>\<sigma>, v, k\<rangle> \<Turnstile> \<phi> \<and> mem (\<delta> \<sigma> i k) I \<and> k \<le> i"
    then have k_tau: "\<tau> \<sigma> k \<le> \<tau> \<sigma> i - left I"
      using diff_le_mono2 by fastforce
    then have k_ltp: "k \<le> LTP \<sigma> (\<tau> \<sigma> i - left I)"
      using VOnce i_LTP_tau add_le_imp_le_diff
      by blast
    then have "k \<notin> {j .. LTP_p \<sigma> i I}"
      using k_def VOnce k_tau
      by auto
    then have "k < j" using k_def k_ltp by auto }
  then show ?case
    using VOnce
    by (cases "right I = \<infinity>")
      (auto 0 0 simp: i_ETP_tau i_LTP_tau le_diff_conv2)
next
  case (VEventually I i v \<phi>)
  { fix k n
    assume r: "right I = enat n"
    from this have tin0: "\<tau> \<sigma> i + n \<ge> \<tau> \<sigma> 0"
      by (auto simp add: trans_le_add1)
    define j where "j = LTP \<sigma> ((\<tau> \<sigma> i) + n)"
    then have j_i: "i \<le> j"
      by (auto simp add: i_LTP_tau trans_le_add1 j_def)
    assume k_def: "\<langle>\<sigma>, v, k\<rangle> \<Turnstile> \<phi> \<and> mem (\<delta> \<sigma> k i) I \<and> i \<le> k"
    then have "\<tau> \<sigma> k \<ge> \<tau> \<sigma> i + left I"
      using le_diff_conv2 by auto
    then have k_etp: "k \<ge> ETP \<sigma> (\<tau> \<sigma> i + left I)"
      using i_ETP_tau by blast
    from this k_def VEventually have "k \<notin> {ETP_f \<sigma> i I .. j}"
      by (auto simp: r j_def)
    then have "j < k" using r k_def k_etp by auto
    from k_def r have "\<delta> \<sigma> k i \<le> n" by auto
    then have "\<tau> \<sigma> k \<le> \<tau> \<sigma> i + n" by auto
    then have "k \<le> j" using tin0 i_LTP_tau by (auto simp add: j_def) }
  note aux = this
  show ?case
  proof (cases "right I")
    case (enat n)
    show ?thesis
      using VEventually[unfolded enat, simplified] aux
      by (simp add: i_ETP_tau enat)
        (metis \<tau>_mono le_add_diff_inverse nat_add_left_cancel_le)
  next
    case infinity
    show ?thesis
      using VEventually
      by (auto simp: infinity i_ETP_tau le_diff_conv2)
  qed
next
  case (SHistorically j I i v \<phi>)
  { fix k
    assume k_def: "\<not> \<langle>\<sigma>, v, k\<rangle> \<Turnstile> \<phi> \<and> mem (\<delta> \<sigma> i k) I \<and> k \<le> i"
    then have k_tau: "\<tau> \<sigma> k \<le> \<tau> \<sigma> i - left I"
      using diff_le_mono2 by fastforce
    then have k_ltp: "k \<le> LTP \<sigma> (\<tau> \<sigma> i - left I)"
      using SHistorically i_LTP_tau add_le_imp_le_diff
      by blast
    then have "k \<notin> {j .. LTP_p \<sigma> i I}"
      using k_def SHistorically k_tau
      by auto
    then have "k < j" using k_def k_ltp by auto }
  then show ?case
    using SHistorically
    by (cases "right I = \<infinity>")
      (auto 0 0 simp add: le_diff_conv2 i_ETP_tau i_LTP_tau)
next
  case (SHistoricallyOut i I v \<phi>)
  { fix j
    from \<tau>_mono have j0: "\<tau> \<sigma> 0 \<le> \<tau> \<sigma> j" by auto
    then have "\<tau> \<sigma> i < \<tau> \<sigma> j + left I" using SHistoricallyOut by linarith
    then have "\<delta> \<sigma> i j < left I"
      using SHistoricallyOut less_\<tau>D not_le by fastforce
    then have "\<not> mem (\<delta> \<sigma> i j) I" by auto }
  then show ?case by auto
next
  case (SAlways I i v \<phi>)
  { fix k n
    assume r: "right I = enat n"
    from this SAlways have tin0: "\<tau> \<sigma> i + n \<ge> \<tau> \<sigma> 0"
      by (auto simp add: trans_le_add1)
    define j where "j = LTP \<sigma> ((\<tau> \<sigma> i) + n)"
    from SAlways have j_i: "i \<le> j"
      by (auto simp add: i_LTP_tau trans_le_add1 j_def)
    assume k_def: "\<not> \<langle>\<sigma>, v, k\<rangle> \<Turnstile> \<phi> \<and> mem (\<delta> \<sigma> k i) I \<and> i \<le> k"
    then have "\<tau> \<sigma> k \<ge> \<tau> \<sigma> i + left I"
      using le_diff_conv2 by auto
    then have k_etp: "k \<ge> ETP \<sigma> (\<tau> \<sigma> i + left I)"
      using SAlways i_ETP_tau by blast
    from this k_def SAlways have "k \<notin> {ETP_f \<sigma> i I .. j}"
      by (auto simp: r j_def)
    then have "j < k" using SAlways k_def k_etp by simp
    from k_def r have "\<delta> \<sigma> k i \<le> n" by simp
    then have "\<tau> \<sigma> k \<le> \<tau> \<sigma> i + n" by simp
    then have "k \<le> j"
      using tin0 i_LTP_tau  
      by (auto simp add: j_def) }
  note aux = this
  show ?case
  proof (cases "right I")
    case (enat n)
    show ?thesis
      using SAlways[unfolded enat, simplified] aux
      by (simp add: i_ETP_tau le_diff_conv2 enat)
        (metis Groups.ab_semigroup_add_class.add.commute add_le_imp_le_diff)
  next
    case infinity
    show ?thesis
      using SAlways
      by (auto simp: infinity i_ETP_tau le_diff_conv2)
  qed
next
  case (VSinceOut i I v \<phi> \<psi>)
  { fix j
    from \<tau>_mono have j0: "\<tau> \<sigma> 0 \<le> \<tau> \<sigma> j" by auto
    then have "\<tau> \<sigma> i < \<tau> \<sigma> j + left I" using VSinceOut by linarith
    then have "\<delta> \<sigma> i j < left I" using VSinceOut j0
      by (metis add.commute gr_zeroI leI less_\<tau>D less_diff_conv2 order_less_imp_not_less zero_less_diff)
    then have "\<not> mem (\<delta> \<sigma> i j) I" by auto }
  then show ?case using VSinceOut by auto
next
  case (VSince I i j v \<phi> \<psi>)
  { fix k
    assume k_def: "\<langle>\<sigma>, v, k\<rangle> \<Turnstile> \<psi> \<and> mem (\<delta> \<sigma> i k) I \<and> k \<le> i"
    then have "\<tau> \<sigma> k \<le> \<tau> \<sigma> i - left I" using diff_le_mono2 by fastforce
    then have k_ltp: "k \<le> LTP \<sigma> (\<tau> \<sigma> i - left I)"
      using VSince i_LTP_tau add_le_imp_le_diff
      by blast
    then have "k < j" using k_def VSince(7)[of k]
      by force
    then have "j \<in> {k <.. i} \<and> \<not> \<langle>\<sigma>, v, j\<rangle> \<Turnstile> \<phi>" using VSince
      by auto }
  then show ?case using VSince
    by force
next
  case (VSinceInf j I i v \<psi> \<phi>)
  { fix k
    assume k_def: "\<langle>\<sigma>, v, k\<rangle> \<Turnstile> \<psi> \<and> mem (\<delta> \<sigma> i k) I \<and> k \<le> i"
    then have k_tau: "\<tau> \<sigma> k \<le> \<tau> \<sigma> i - left I"
      using diff_le_mono2 by fastforce
    then have k_ltp: "k \<le> LTP \<sigma> (\<tau> \<sigma> i - left I)"
      using VSinceInf i_LTP_tau add_le_imp_le_diff
      by blast
    then have "k \<notin> {j .. LTP_p \<sigma> i I}"
      using k_def VSinceInf k_tau
      by auto
    then have "k < j" using k_def k_ltp by auto }
  then show ?case
    using VSinceInf
    by (cases "right I = \<infinity>")
      (auto 0 0 simp: i_ETP_tau i_LTP_tau le_diff_conv2)
next
  case (VUntil I j i v \<phi> \<psi>)
  { fix k
    assume k_def: "\<langle>\<sigma>, v, k\<rangle> \<Turnstile> \<psi> \<and> mem (\<delta> \<sigma> k i) I \<and> i \<le> k"
    then have "\<tau> \<sigma> k \<ge> \<tau> \<sigma> i + left I"
      using le_diff_conv2 by auto
    then have k_etp: "k \<ge> ETP \<sigma> (\<tau> \<sigma> i + left I)"
      using VUntil i_ETP_tau by blast
    from this k_def VUntil have "k \<notin> {ETP_f \<sigma> i I .. j}" by auto
    then have "j < k" using k_etp k_def by auto
    then have "j \<in> {i ..< k} \<and> VIO \<sigma> v j \<phi>" using VUntil k_def
      by auto }
  then show ?case
    using VUntil by force
next
  case (VUntilInf I i v \<psi> \<phi>)
  { fix k n
    assume r: "right I = enat n"
    from this VUntilInf have tin0: "\<tau> \<sigma> i + n \<ge> \<tau> \<sigma> 0"
      by (auto simp add: trans_le_add1)
    define j where "j = LTP \<sigma> ((\<tau> \<sigma> i) + n)"
    from VUntilInf have j_i: "i \<le> j"
      by (auto simp add: i_LTP_tau trans_le_add1 j_def)
    assume k_def: "\<langle>\<sigma>, v, k\<rangle> \<Turnstile> \<psi> \<and> mem (\<delta> \<sigma> k i) I \<and> i \<le> k"
    then have "\<tau> \<sigma> k \<ge> \<tau> \<sigma> i + left I"
      using le_diff_conv2 by auto
    then have k_etp: "k \<ge> ETP \<sigma> (\<tau> \<sigma> i + left I)"
      using VUntilInf i_ETP_tau by blast
    from this k_def VUntilInf have "k \<notin> {ETP_f \<sigma> i I .. j}"
      by (auto simp: r j_def)
    then have "j < k" using VUntilInf k_def k_etp by auto
    from k_def r have "\<delta> \<sigma> k i \<le> n" by auto
    then have "\<tau> \<sigma> k \<le> \<tau> \<sigma> i + n" by auto
    then have "k \<le> j"
      using tin0 VUntilInf i_LTP_tau r k_def 
      by (force simp add: j_def) }
  note aux = this
  show ?case
  proof (cases "right I")
    case (enat n)
    show ?thesis
      using VUntilInf[unfolded enat, simplified] aux
      by (simp add: i_ETP_tau enat)
        (metis \<tau>_mono le_add_diff_inverse nat_add_left_cancel_le)
  next
    case infinity
    show ?thesis
      using VUntilInf
      by (auto simp: infinity i_ETP_tau le_diff_conv2)
  qed
qed (auto simp: fun_upd_def split: nat.splits)

lemmas soundness = soundness_raw[THEN conjunct1, THEN mp] soundness_raw[THEN conjunct2, THEN mp]

lemma completeness_raw: "(\<langle>\<sigma>, v, i\<rangle> \<Turnstile> \<phi> \<longrightarrow> SAT \<sigma> v i \<phi>) \<and> (\<not> \<langle>\<sigma>, v, i\<rangle> \<Turnstile> \<phi> \<longrightarrow> VIO \<sigma> v i \<phi>)"
proof (induct \<phi> arbitrary: v i)
  case (Prev I \<phi>)
  show ?case using Prev
    by (auto intro: SAT_VIO.SPrev SAT_VIO.VPrev SAT_VIO.VPrevOutL SAT_VIO.VPrevOutR SAT_VIO.VPrevZ split: nat.splits)
next
  case (Once I \<phi>)
  { assume "\<langle>\<sigma>, v, i\<rangle> \<Turnstile> \<^bold>P I \<phi>"
    with Once have "SAT \<sigma> v i (\<^bold>P I \<phi>)"
      by (auto intro: SAT_VIO.SOnce) }
  moreover
  { assume i_l: "\<tau> \<sigma> i < \<tau> \<sigma> 0 + left I"
    with Once have "VIO \<sigma> v i (\<^bold>P I \<phi>)"
      by (auto intro: SAT_VIO.VOnceOut) }
  moreover
  { assume unsat: "\<not> \<langle>\<sigma>, v, i\<rangle> \<Turnstile> \<^bold>P I \<phi>"
      and i_ge: "\<tau> \<sigma> 0 + left I \<le> \<tau> \<sigma> i"
    with Once have "VIO \<sigma> v i (\<^bold>P I \<phi>)"
      by (auto intro!: SAT_VIO.VOnce simp: i_LTP_tau i_ETP_tau
          split: enat.splits) }
  ultimately show ?case
    by force
next
  case (Historically I \<phi>)
  from \<tau>_mono have i0: "\<tau> \<sigma> 0 \<le> \<tau> \<sigma> i" by auto
  { assume sat: "\<langle>\<sigma>, v, i\<rangle> \<Turnstile> \<^bold>H I \<phi>"
      and i_ge: "\<tau> \<sigma> i \<ge> \<tau> \<sigma> 0 + left I"
    with Historically have "SAT \<sigma> v i (\<^bold>H I \<phi>)"
      using le_diff_conv
      by (auto intro!: SAT_VIO.SHistorically simp: i_LTP_tau i_ETP_tau
          split: enat.splits) }
  moreover
  { assume "\<not> \<langle>\<sigma>, v, i\<rangle> \<Turnstile> \<^bold>H I \<phi>"
    with Historically have "VIO \<sigma> v i (\<^bold>H I \<phi>)"
      by (auto intro: SAT_VIO.VHistorically) }
  moreover
  { assume i_l: "\<tau> \<sigma> i < \<tau> \<sigma> 0 + left I"
    with Historically have "SAT \<sigma> v i (\<^bold>H I \<phi>)"
      by (auto intro: SAT_VIO.SHistoricallyOut) }
  ultimately show ?case
    by force
next
  case (Eventually I \<phi>)
  from \<tau>_mono have i0: "\<tau> \<sigma> 0 \<le> \<tau> \<sigma> i" by auto
  { assume "\<langle>\<sigma>, v, i\<rangle> \<Turnstile> \<^bold>F I \<phi>"
    with Eventually have "SAT \<sigma> v i (\<^bold>F I \<phi>)"
      by (auto intro: SAT_VIO.SEventually) }
  moreover
  { assume unsat: "\<not> \<langle>\<sigma>, v, i\<rangle> \<Turnstile> \<^bold>F I \<phi>"
    with Eventually have "VIO \<sigma> v i (\<^bold>F I \<phi>)"
      by (auto intro!: SAT_VIO.VEventually simp: add_increasing2 i0 i_LTP_tau i_ETP_tau
          split: enat.splits) }
  ultimately show ?case by auto
next
  case (Always I \<phi>)
    from \<tau>_mono have i0: "\<tau> \<sigma> 0 \<le> \<tau> \<sigma> i" by auto
  { assume "\<not> \<langle>\<sigma>, v, i\<rangle> \<Turnstile> \<^bold>G I \<phi>"
    with Always have "VIO \<sigma> v i (\<^bold>G I \<phi>)"
      by (auto intro: SAT_VIO.VAlways) }
  moreover
  { assume sat: "\<langle>\<sigma>, v, i\<rangle> \<Turnstile> \<^bold>G I \<phi>"
    with Always have "SAT \<sigma> v i (\<^bold>G I \<phi>)"
      by (auto intro!: SAT_VIO.SAlways simp: add_increasing2 i0 i_LTP_tau i_ETP_tau le_diff_conv split: enat.splits)}
  ultimately show ?case by auto
next
  case (Since \<phi> I \<psi>)
  { assume "\<langle>\<sigma>, v, i\<rangle> \<Turnstile> \<phi> \<^bold>S I \<psi>"
    with Since have "SAT \<sigma> v i (\<phi> \<^bold>S I \<psi>)"
      by (auto intro: SAT_VIO.SSince) }
  moreover
  { assume i_l: "\<tau> \<sigma> i < \<tau> \<sigma> 0 + left I"
    with Since have "VIO \<sigma> v i (\<phi> \<^bold>S I \<psi>)"
      by (auto intro: SAT_VIO.VSinceOut) }
  moreover
  { assume unsat: "\<not> \<langle>\<sigma>, v, i\<rangle> \<Turnstile> \<phi> \<^bold>S I \<psi>"
      and nw: "\<forall>j\<le>i. \<not> mem (\<delta> \<sigma> i j) I \<or> \<not> \<langle>\<sigma>, v, j\<rangle> \<Turnstile> \<psi>"
      and i_ge: "\<tau> \<sigma> 0 + left I \<le> \<tau> \<sigma> i"
    with Since have "VIO \<sigma> v i (\<phi> \<^bold>S I \<psi>)"
      by (auto intro!: SAT_VIO.VSinceInf simp: i_LTP_tau i_ETP_tau
          split: enat.splits)}
  moreover
  { assume unsat: "\<not> \<langle>\<sigma>, v, i\<rangle> \<Turnstile> \<phi> \<^bold>S I \<psi>"
      and jw: "\<exists>j\<le>i. mem (\<delta> \<sigma> i j) I \<and> \<langle>\<sigma>, v, j\<rangle> \<Turnstile> \<psi>"
      and i_ge: "\<tau> \<sigma> 0 + left I \<le> \<tau> \<sigma> i"
    from unsat jw not_sat_SinceD[of \<sigma> v i \<phi> I \<psi>]
    obtain j where j: "j \<le> i"
      "case right I of \<infinity> \<Rightarrow> True | enat n \<Rightarrow> ETP \<sigma> (\<tau> \<sigma> i - n) \<le> j"
      "\<not> \<langle>\<sigma>, v, j\<rangle> \<Turnstile> \<phi>" "(\<forall>k \<in> {j .. (min i (LTP \<sigma> (\<tau> \<sigma> i - left I)))}.
      \<not> \<langle>\<sigma>, v, k\<rangle> \<Turnstile> \<psi>)" by (auto split: enat.splits)
    with Since have "VIO \<sigma> v i (\<phi> \<^bold>S I \<psi>)"
      using i_ge unsat jw
      by (auto intro!: SAT_VIO.VSince) }
  ultimately show ?case
    by (force simp del: sat.simps)
next
  case (Until \<phi> I \<psi>)
  from \<tau>_mono have i0: "\<tau> \<sigma> 0 \<le> \<tau> \<sigma> i" by auto
  { assume "\<langle>\<sigma>, v, i\<rangle> \<Turnstile> \<phi> \<^bold>U I \<psi>"
    with Until have "SAT \<sigma> v i (\<phi> \<^bold>U I \<psi>)"
      by (auto intro: SAT_VIO.SUntil) }
  moreover
  { assume unsat: "\<not> \<langle>\<sigma>, v, i\<rangle> \<Turnstile> \<phi> \<^bold>U I \<psi>"
      and witness: "\<exists>j \<ge> i. mem (\<delta> \<sigma> j i) I \<and> \<langle>\<sigma>, v, j\<rangle> \<Turnstile> \<psi>"
    from this Until not_sat_UntilD[of \<sigma> v i \<phi> I \<psi>] obtain j
      where j: "j \<ge> i" "(case right I of \<infinity> \<Rightarrow> True | enat n
      \<Rightarrow> j < LTP \<sigma> (\<tau> \<sigma> i + n))" "\<not> (\<langle>\<sigma>, v, j\<rangle> \<Turnstile> \<phi>)"
        "(\<forall>k \<in> {(max i (ETP \<sigma> (\<tau> \<sigma> i + left I))) .. j}. \<not> \<langle>\<sigma>, v, k\<rangle> \<Turnstile> \<psi>)"
      by auto
    with Until have "VIO \<sigma> v i (\<phi> \<^bold>U I \<psi>)"
      using unsat witness 
      by (auto intro!: SAT_VIO.VUntil) }
  moreover
  { assume unsat: "\<not> \<langle>\<sigma>, v, i\<rangle> \<Turnstile> \<phi> \<^bold>U I \<psi>"
      and no_witness: "\<forall>j \<ge> i. \<not> mem (\<delta> \<sigma> j i) I \<or> \<not> \<langle>\<sigma>, v, j\<rangle> \<Turnstile> \<psi>"
    with Until have "VIO \<sigma> v i (\<phi> \<^bold>U I \<psi>)"
      by (auto intro!: SAT_VIO.VUntilInf simp: add_increasing2 i0 i_LTP_tau i_ETP_tau
          split: enat.splits)
  }
  ultimately show ?case by auto
qed (auto intro: SAT_VIO.intros)

lemmas completeness = completeness_raw[THEN conjunct1, THEN mp] completeness_raw[THEN conjunct2, THEN mp]

lemma SAT_or_VIO: "SAT \<sigma> v i \<phi> \<or> VIO \<sigma> v i \<phi>"
  using completeness[of \<sigma> v i \<phi>] by auto

end

unbundle MFOTL_no_notation

(*<*)
end
(*>*)