theory CLMM_Transformation imports CLMM_Description

(* Author: Mnacho Echenim. Grenoble INP - UGA, Kaiko *)
(* This research is part of the ANR project BlockFI - 2024-CES38 *)

begin

section \<open>CLMM transformations\<close>

subsection \<open>CLMM pool refinement\<close>

text \<open>Given a pool $P$ and a (square root) price $\pi$, the refinement operation consists
in defining a new grid (if necessary) in such a way that $\pi$ is one of the bounds on the
grid.\<close>

definition refine where
"refine P sqp = (let i = lower_tick P sqp in 
  (if (grd P i = sqp) then P else 
  (wedge (grd P) i sqp, wedge (lq P) i (lq P i), wedge (fee P) i (fee P i))))"

lemma refine_eq:
  assumes "i = lower_tick P sqp"
  and "grd P i = sqp"
shows "refine P sqp = P" using assms unfolding refine_def Let_def by simp

lemma refine_lq:
  assumes "i = lower_tick P sqp"
  and "grd P i \<noteq> sqp"
  and "P' = refine P sqp"
shows "lq P' = wedge (lq P) i (lq P i)" 
  using assms unfolding Let_def refine_def lq_def by simp

lemma refine_fee:
  assumes "i = lower_tick P sqp"
  and "grd P i \<noteq> sqp"
  and "P' = refine P sqp"
shows "fee P' = wedge (fee P) i (fee P i)" 
  using assms unfolding Let_def refine_def fee_def by simp

lemma refine_grd:
  assumes "i = lower_tick P sqp"
  and "P' = refine P sqp"
  and "grd P i \<noteq> sqp"
shows "grd P' = wedge (grd P) i sqp" 
  using assms unfolding refine_def grd_def Let_def by simp

lemma refine_grd_cong:
  assumes "P1 = refine P sqp"
  and "P2 = refine P' sqp"
  and "grd P = grd P'"
shows "grd P1 = grd P2" 
proof (cases "grd P (lower_tick P sqp) = sqp")
  case True
  hence "grd P' (lower_tick P' sqp) = sqp" 
    using assms unfolding lower_tick_def rng_blw_def by simp
  then show ?thesis using assms True unfolding refine_def Let_def by simp
next
  case False
  define i where "i = lower_tick P sqp"
  hence "i = lower_tick P' sqp" 
    using assms unfolding lower_tick_def rng_blw_def by simp
  have "grd P1 = wedge (grd P) i sqp" 
    using False assms unfolding refine_def grd_def i_def Let_def by simp
  also have "... = wedge (grd P') i sqp" using assms by simp
  also have "... = grd P2" 
    using False assms \<open>i = lower_tick P' sqp\<close> 
    unfolding refine_def grd_def i_def Let_def by simp
  finally show ?thesis .
qed

lemma refine_grd_arg_le:
  assumes "i = lower_tick P sqp"
  and "P' = refine P sqp"
  and "j \<le> i"
shows "grd P' j = grd P j"
proof (cases "grd P (lower_tick P sqp) = sqp")
  case True
  hence "P' = P" using assms refine_eq by simp
  then show ?thesis by simp
next
  case False
  hence "grd P' = wedge (grd P) i sqp" using assms refine_grd by simp
  then show ?thesis using assms by simp
qed

lemma refine_grd_arg_gt:
  assumes "i = lower_tick P sqp"
  and "P' = refine P sqp"
  and "grd P (lower_tick P sqp) \<noteq> sqp"
  and "i < j"
shows "grd P' (j+1) = grd P j"
proof -
  have "grd P' = wedge (grd P) i sqp" using assms refine_grd by simp
  then show ?thesis using assms by simp
qed

lemma refine_grd_arg_Suc:
  assumes "i = lower_tick P sqp"
  and "P' = refine P sqp"
  and "grd P (lower_tick P sqp) \<noteq> sqp"
shows "grd P' (i+1) = sqp"
proof -
  have "grd P' = wedge (grd P) i sqp" using assms refine_grd by simp
  then show ?thesis using assms by simp
qed

lemma refine_fee_arg_le:
  assumes "i = lower_tick P sqp"
  and "P' = refine P sqp"
  and "j \<le> i"
shows "fee P' j = fee P j"
proof (cases "grd P (lower_tick P sqp) = sqp")
  case True
  hence "P' = P" using assms refine_eq by simp
  then show ?thesis by simp
next
  case False
  hence "fee P' = wedge (fee P) i (fee P i)" using assms refine_fee by simp
  then show ?thesis using assms by simp
qed

lemma refine_fee_arg_gt:
  assumes "i = lower_tick P sqp"
  and "P' = refine P sqp"
  and "grd P (lower_tick P sqp) \<noteq> sqp"
  and "i < j"
shows "fee P' (j+1) = fee P j"
proof -
  have "fee P' = wedge (fee P) i (fee P i)" using assms refine_fee by simp
  then show ?thesis using assms by simp
qed

lemma refine_fee_arg_Suc:
  assumes "i = lower_tick P sqp"
  and "P' = refine P sqp"
  and "grd P (lower_tick P sqp) \<noteq> sqp"
shows "fee P' (i+1) = fee P i"
proof -
  have "fee P' = wedge (fee P) i (fee P i)" using assms refine_fee by simp
  then show ?thesis using assms by simp
qed

lemma refine_lq_arg_le:
  assumes "i = lower_tick P sqp"
  and "P' = refine P sqp"
  and "grd P i \<noteq> sqp"
  and "j \<le> i"
shows "lq P' j = lq P j"
proof -
  have "lq P' = wedge (lq P) i (lq P i)" 
    using refine_lq assms by simp
  thus ?thesis using assms by simp
qed

lemma refine_lq_arg_gt:
  assumes "i = lower_tick P sqp"
  and "P' = refine P sqp"
  and "grd P i \<noteq> sqp"
  and "i < j"
shows "lq P' (j+1) = lq P j"
proof -
  have "lq P' = wedge (lq P) i (lq P i)" 
    using refine_lq assms by simp
  thus ?thesis using assms by simp
qed

lemma refine_lq_arg_Suc:
  assumes "i = lower_tick P sqp"
  and "P' = refine P sqp"
  and "grd P i \<noteq> sqp"
shows "lq P' (i+1) = lq P i"
proof -
  have "lq P' = wedge (lq P) i (lq P i)" 
    using refine_lq assms by simp
  thus ?thesis using assms by simp
qed

lemma refine_on_grd:
  assumes "clmm_dsc P"
  and "grd P i = sqp"
  shows "refine P sqp = P"
proof -
  have "i = lower_tick P sqp" using assms lower_tick_eq by simp
  thus ?thesis using assms unfolding refine_def Let_def by simp
qed

lemma refine_encomp_at_grd:
  assumes "clmm_dsc P"
  and "P' = refine P sqp"
  and "grd P (lower_tick P sqp) = sqp"
shows "encomp_at (grd P') (grd P) j j" 
proof -
  have "P' = P" using refine_on_grd assms by simp
  have "encomp_at (grd P') (grd P) j j" 
  proof
    show "grd P j \<le> grd P' j" using \<open>P' = P\<close> by simp
    show "grd P' (j + 1) \<le> grd P (j + 1)" using \<open>P' = P\<close> by simp
  qed
  thus ?thesis by auto
qed

lemma refine_encomp_at_arg_le:
  assumes "clmm_dsc P"
  and "P' = refine P sqp"
  and "i = lower_tick P sqp"
  and "grd P i \<noteq> sqp"
  and "j \<le> i"
shows "encomp_at (grd P') (grd P) j j" 
proof -
  have grd: "grd P' = wedge (grd P) i sqp" 
    using assms unfolding Let_def refine_def grd_def by simp   
  hence "grd P' j = grd P j" using \<open>j \<le> i\<close> by (simp add: grd)
  moreover have "grd P' (j+1) \<le> grd P (j+1)"
  proof (cases "j = i")
    case True
    hence "grd P' (j+1) = sqp" using grd by simp
    also have "... < grd P (j+1)" using \<open>j = i\<close> assms
      by (meson lower_tick_ubound)
    finally show "grd P' (j+1) \<le> grd P (j+1)" by simp
  next
    case False
    hence "grd P' (j+1) \<le> grd P (j+1)" using \<open>j \<le> i\<close> grd by auto
    then show ?thesis by simp
  qed
  ultimately show ?thesis using encomp_atI[of "grd P" j "grd P'" j] by simp
qed

lemma refine_encomp_at_arg_ge_Suc:
  assumes "clmm_dsc P"
  and "P' = refine P sqp"
  and "i = lower_tick P sqp"
  and "grd P i \<noteq> sqp"
  and "i+1 \<le> j"
  and "0 < sqp"
shows "encomp_at (grd P') (grd P) j (j-1)" 
proof -
  have grd: "grd P' = wedge (grd P) i sqp" 
    using assms unfolding Let_def refine_def grd_def by simp 
  show ?thesis
  proof (cases "i+1 = j")
    case True
    hence "grd P i \<le> grd P' j" 
      using lower_tick_lbound assms grd
      by (metis wedge_arg_eq)
    moreover have "grd P' (j+1) \<le> grd P (i+1)" 
      using True wedge_arg_gt[of i "j+1" "grd P" sqp] grd
      by (simp add: add.commute) 
    ultimately show ?thesis using encomp_atI True by auto
  next
    case False
    hence "grd P (j - 1) \<le> grd P' j" using assms grd by fastforce
    moreover have "grd P' (j+1) \<le> grd P j" using grd False assms by simp
    ultimately show ?thesis using encomp_atI[of "grd P" "j-1"] by simp
  qed  
qed

lemma refine_finer_range:
  assumes "clmm_dsc P"
  and "0 < sqp"
  and "P' = refine P sqp"
shows "finer_range (grd P') (grd P)" 
proof -
  define i where "i = lower_tick P sqp"
  show ?thesis
  proof (cases "grd P i = sqp")
    case True
    then show ?thesis 
      using assms refine_encomp_at_grd i_def unfolding finer_range_def by metis
  next
    case False
    show ?thesis unfolding finer_range_def
    proof
      fix j
      show "\<exists>k. encomp_at (grd P') (grd P) j k"
      proof (cases "j \<le> i")
        case True
        then show ?thesis 
          using refine_encomp_at_arg_le[of P P'] assms i_def False by auto
      next
        case False
        show ?thesis
        proof (cases "j = i+1")
          case True
          then show ?thesis 
            using refine_encomp_at_arg_ge_Suc assms i_def
            by (meson dual_order.refl refine_encomp_at_grd)
        next
          case False
          hence "i+1 < j" using \<open>\<not> j \<le> i\<close> by simp
          then show ?thesis 
            using refine_encomp_at_arg_ge_Suc False assms i_def
            by (meson refine_encomp_at_grd zle_add1_eq_le zless_add1_eq)
        qed
      qed
    qed
  qed
qed

lemma refine_finite_liq:
  assumes "finite_liq P"
  and "P' = refine P sqp"
shows "finite_liq P'"
proof (cases "grd P (lower_tick P sqp) = sqp")
  case True
  then show ?thesis 
    using assms clmm_dsc_liq unfolding refine_def Let_def by simp
next
  case False
  define j where "j = lower_tick P sqp"
  have grd: "grd P' = wedge (grd P) j sqp" using j_def assms False 
    unfolding refine_def Let_def grd_def by simp
  have lq: "lq P' = wedge (lq P) j (lq P j)" using j_def assms False 
    unfolding refine_def Let_def lq_def by simp
  show ?thesis 
      using grd wedge_finite_nz_support assms clmm_dsc_liq(1) 
      unfolding finite_liq_def by (metis lq)
qed

lemma refine_clmm:
  assumes "clmm_dsc P"
  and "0 < sqp"
  and "P' = refine P sqp"
shows "clmm_dsc P'"
proof (cases "grd P (lower_tick P sqp) = sqp")
  case True
  then show ?thesis using assms unfolding refine_def Let_def by simp
next
  case False
  define j where "j = lower_tick P sqp"
  hence "grd P j \<le> sqp"
    by (simp add: assms lower_tick_lbound)
  hence "grd P j < sqp" using False j_def by simp
  have "sqp < grd P (j+1)" using j_def assms lower_tick_ubound by simp
  have grd: "grd P' = wedge (grd P) j sqp" using j_def assms False 
    unfolding refine_def Let_def grd_def by simp
  have lq: "lq P' = wedge (lq P) j (lq P j)" using j_def assms False 
    unfolding refine_def Let_def lq_def by simp
  have fee: "fee P' = wedge (fee P) j (fee P j)" using j_def assms False 
    unfolding refine_def Let_def fee_def by simp
  show ?thesis 
  proof
    show "span_grid P'"
    proof      
      show "strict_mono (grd P')"
      proof (rule wedge_strict_mono)
        show "grd P' = wedge (grd P) j sqp" using grd .
        show "grd P j < sqp" using \<open>grd P j < sqp\<close> .
        show "sqp < grd P (j+1)" using \<open>sqp < grd P (j+1)\<close> .
        show "strict_mono (grd P)" using assms by simp
      qed
      show "\<forall>i. 0 < grd P' i" 
        using grd assms wedge_gt by (metis clmm_dsc_grid(2)) 
      show "\<forall>r>0. \<exists>i. grd P' i < r" 
        using grd wedge_as_lbound by (simp add: assms(1))
      show "\<forall>r. \<exists>i. r < grd P' i" 
        using grd wedge_as_ubound by (simp add: assms(1))
    qed
    show "\<forall>i. 0 \<le> fee P' i" using wedge_ge fee assms
      by (metis clmm_dsc_fees)
    show "\<forall>i. fee P' i < 1" using wedge_lt fee assms 
      by (metis clmm_dsc_fees)
    show "\<forall>i. 0 \<le> lq P' i" using wedge_ge lq assms
      by (metis clmm_dsc_liq(2))
    show "finite_liq P'" 
      using refine_finite_liq assms clmm_dsc_liq by simp
  qed
qed

lemma refine_lower_tick_idx:
  assumes "clmm_dsc P" 
  and "0 < sqp"
  and "i = lower_tick P sqp"
  and "P' = refine P sqp"
  and "grd P (lower_tick P sqp) \<noteq> sqp"
shows "lower_tick P' sqp = i+1" 
proof -
  have "clmm_dsc P'" using refine_clmm assms by simp
  moreover have "grd P' (i+1) = sqp" 
    using refine_grd_arg_Suc assms by simp 
  ultimately show ?thesis using \<open>clmm_dsc P'\<close> lower_tick_eq by simp
qed

lemma refine_ge_lower_tick_eq:
  assumes "clmm_dsc P"
  and "0 < sqp"
  and "i = lower_tick P sqp'"
  and "P' = refine P sqp"
  and "grd P (lower_tick P sqp) \<noteq> sqp"
  and "sqp \<le> sqp'"
  and "lower_tick P sqp = lower_tick P sqp'"
shows "lower_tick P' sqp' = i+1"
proof (rule lower_tick_charact)
  show "clmm_dsc P'" using assms refine_clmm by simp
  show "grd P' (i + 1) \<le> sqp'" by (metis assms(3-7) refine_grd_arg_Suc)
  have "sqp' < grd P (i+1)"
    by (simp add: assms(1) assms(3) lower_tick_ubound)
  also have "... = grd P' (i + 1 + 1)"
    by (metis assms(3-5,7)less_add_one refine_grd_arg_gt)
  finally show "sqp' < grd P' (i + 1 + 1)" .
qed

lemma refine_ge_lower_tick_gt:
  assumes "clmm_dsc P"
  and "0 < sqp"
  and "sqp \<le> sqp'"
  and "i = lower_tick P sqp'"
  and "P' = refine P sqp"
  and "grd P (lower_tick P sqp) \<noteq> sqp"
  and "lower_tick P sqp < lower_tick P sqp'"
shows "lower_tick P' sqp' = i+1"
proof (rule lower_tick_charact)
  show "clmm_dsc P'" using assms refine_clmm by simp
  define j where "j = lower_tick P sqp"
  have "sqp < sqp'" using assms lower_tick_lt by simp
  have "grd P' = wedge (grd P) j sqp" using assms j_def refine_grd by simp
  hence "grd P' (i+1) = grd P i" using assms(4,7) j_def by force
  also have "... \<le> sqp'" using assms lower_tick_geq by simp
  finally show "grd P' (i+1) \<le> sqp'" .
  have "sqp' < grd P (i+1)"
    by (simp add: assms(1) assms(4) lower_tick_ubound)
  also have "... = grd P' (i+1 + 1)"
    by (metis assms(4-7) dual_order.strict_trans less_add_one refine_grd_arg_gt)
  finally show "sqp' < grd P' (i + 1 + 1)" .
qed

lemma refine_ge_lower_tick:
  assumes "clmm_dsc P" 
  and "0 < sqp"
  and "sqp \<le> sqp'"
  and "i = lower_tick P sqp'"
  and "P' = refine P sqp"
  and "grd P (lower_tick P sqp) \<noteq> sqp"
shows "lower_tick P' sqp' = i+1" 
proof (cases "lower_tick P sqp = lower_tick P sqp'")
  case True
  then show ?thesis using assms refine_ge_lower_tick_eq by simp
next
  case False
  then show ?thesis using assms refine_ge_lower_tick_gt
    by (smt (verit) lower_tick_mono)
qed

lemma refine_lower_tick:
  assumes "clmm_dsc P"
  and "P' = refine P sqp"
  and "0 < sqp"
  shows "grd P' (lower_tick P' sqp) = sqp"
proof (cases "grd P (lower_tick P sqp) = sqp")
  case True
  then show ?thesis using refine_eq assms by simp
next
  case False
  define i where "i = lower_tick P sqp"
  have "grd P' = wedge (grd P) i sqp" 
    using assms False refine_grd i_def by simp
  hence "grd P' (i+1) = sqp" using wedge_arg_eq assms by simp
  moreover have "clmm_dsc P'" using assms refine_clmm by simp
  ultimately show ?thesis by (simp add: lower_tick_eq) 
qed

lemma refine_finer_ranges:
  assumes "clmm_dsc P"
  and "0 < sqp"
  and "P' = refine P sqp"
  shows "finer_ranges (grd P') (grd P)"
proof (rule finer_ranges.intro)
  show "strict_mono (grd P')" 
    using refine_clmm clmm_dsc_grid assms by metis
  show "mono (grd P)" using assms clmm_dsc_grid
    by (simp add: strict_mono_mono) 
  show "finer_range (grd P') (grd P)" using assms refine_finer_range
    by (metis) 
qed

lemma refine_coarse_idx_grd:
  assumes "clmm_dsc P"
  and "P' = refine P sqp"
  and "grd P (lower_tick P sqp) = sqp"
shows "coarse_idx (grd P') (grd P) j = j" 
proof -
  interpret finer_ranges "grd P'" "grd P"
    using refine_finer_ranges[of P sqp P'] assms
    by (metis clmm_dsc_grid(2))
  show ?thesis using coarse_idx_eq refine_encomp_at_grd assms
    by (metis clmm_dsc_grd_Suc inf.cobounded1 inf.strict_order_iff 
        refine_on_grd)
qed

lemma refine_coarse_idx_arg_le:
  assumes "clmm_dsc P"
  and "P' = refine P sqp"
  and "i = lower_tick P sqp"
  and "grd P i \<noteq> sqp"
  and "j \<le> i"
  and "0 < sqp"
shows "coarse_idx (grd P') (grd P) j = j" 
proof -
  interpret finer_ranges "grd P'" "grd P"
    using refine_finer_ranges[of P sqp P'] assms by metis
  show ?thesis using coarse_idx_eq refine_encomp_at_arg_le assms
    by (metis coarse_idx_bounds encomp_idx_unique)
qed

lemma refine_coarse_idx_arg_gt:
  assumes "clmm_dsc P"
  and "0 < sqp"
  and "P' = refine P sqp"
  and "i = lower_tick P sqp"
  and "grd P i \<noteq> sqp"
  and "i+1 \<le> j"
shows "coarse_idx (grd P') (grd P) j = j-1" 
proof -
  interpret finer_ranges "grd P'" "grd P"
    using refine_finer_ranges[of P sqp P'] assms by metis
  show ?thesis 
    using coarse_idx_eq coarse_idx_bounds refine_encomp_at_arg_ge_Suc
    by (metis assms encomp_idx_unique)
qed

lemma refine_lq_idx_neq:
  assumes "clmm_dsc P" 
  and "0 < sqp"
  and "P' = refine P sqp"
  and "grd P (lower_tick P sqp) \<noteq> sqp"
  shows "lq P' j = lq P (pool_coarse_idx P' P j)"
proof -
  define i where "i = lower_tick P sqp"
  fix j
  {
    assume "j \<le> i"
    hence "pool_coarse_idx P' P j = j" 
      using refine_coarse_idx_arg_le assms i_def 
      unfolding pool_coarse_idx_def by simp
    moreover have "lq P' j = lq P j" 
      using \<open>j \<le> i\<close> refine_lq assms i_def by simp
    ultimately have "pool_coarse_idx P' P j = j" "lq P' j = lq P j"
      by auto
  } note a = this
  {
    assume "i+1 \<le> j"
    hence "pool_coarse_idx P' P j = j-1"
      using refine_coarse_idx_arg_gt assms i_def
      unfolding pool_coarse_idx_def by simp
    moreover have "lq P' j = lq P (j-1)"
    proof (cases "i+1 = j")
      case True
      then show ?thesis using refine_lq assms wedge_arg_eq unfolding i_def
        by auto
    next
      case False
      hence "i+1 < j" using \<open>i+1 \<le> j\<close> by simp
      then show ?thesis using refine_lq assms wedge_arg_gt unfolding i_def
        by simp
    qed
    ultimately have "pool_coarse_idx P' P j = j-1" "lq P' j = lq P (j-1)" 
      by auto
  } note b = this     
  show "lq P' j = lq P (pool_coarse_idx P' P j)" using a b by fastforce
qed

lemma refine_fee_idx_neq:
  assumes "clmm_dsc P" 
  and "0 < sqp"
  and "P' = refine P sqp"
  and "grd P (lower_tick P sqp) \<noteq> sqp"
  shows "fee P' j = fee P (pool_coarse_idx P' P j)"
proof -
  define i where "i = lower_tick P sqp"
  fix j
  {
    assume "j \<le> i"
    hence "pool_coarse_idx P' P j = j" 
      using refine_coarse_idx_arg_le assms i_def 
      unfolding pool_coarse_idx_def by simp
    moreover have "fee P' j = fee P j"
      using \<open>j \<le> i\<close> refine_fee assms i_def by simp
    ultimately have "pool_coarse_idx P' P j = j" "fee P' j = fee P j" by auto
  } note a = this
  {
    assume "i+1 \<le> j"
    hence "pool_coarse_idx P' P j = j-1"
      using refine_coarse_idx_arg_gt assms i_def
      unfolding pool_coarse_idx_def by simp
    moreover have "fee P' j = fee P (j-1)"
    proof (cases "i+1 = j")
      case True
      then show ?thesis using refine_fee assms wedge_arg_eq unfolding i_def
        by auto
    next
      case False
      hence "i+1 < j" using \<open>i+1 \<le> j\<close> by simp
      then show ?thesis using refine_fee assms wedge_arg_gt unfolding i_def
        by simp
    qed
    ultimately have "pool_coarse_idx P' P j = j-1" "fee P' j = fee P (j-1)"
      by auto
  } note b = this     
  show "fee P' j = fee P (pool_coarse_idx P' P j)" using a b by fastforce
qed

lemma refine_cst_fees:
  assumes "\<And>i. fee P i = phi"
and "P' = refine P sqp"
shows "\<And>i. fee P' i = phi"
  by (smt (verit, ccfv_SIG) assms refine_eq refine_fee refine_fee_arg_Suc 
      wedge_arg_gt wedge_arg_lt) 

lemma refine_finer_neq:
  assumes "clmm_dsc P" 
  and "0 < sqp"
  and "P' = refine P sqp"
  and "grd P (lower_tick P sqp) \<noteq> sqp"
  shows "finer_pool P' P"
proof (intro finer_poolI conjI allI)
  define i where "i = lower_tick P sqp"
  show "finer_range (grd P') (grd P)" using refine_finer_range assms by simp
  show "\<And>j. lq P' j = lq P (pool_coarse_idx P' P j)" 
    using refine_lq_idx_neq assms by simp
  show "\<And>j. fee P' j = fee P (pool_coarse_idx P' P j)" 
    using refine_fee_idx_neq assms by simp
qed

lemma refine_finer:
  assumes "clmm_dsc P" 
  and "0 < sqp"
  and "P' = refine P sqp"
shows "finer_pool P' P"
proof (cases "grd P (lower_tick P sqp) = sqp")
  case True
  hence "P' = P" using assms refine_on_grd by simp
  then show ?thesis using finer_pool_refl assms by simp
next
  case False
  then show ?thesis using assms refine_finer_neq by simp
qed

lemma refine_nz_lq_sub:
  assumes "clmm_dsc P"
  and "0 < sqp"
  and "P' = refine P sqp"
shows "(\<lambda>j. pool_coarse_idx P' P j) ` nz_support (lq P') \<subseteq> 
  nz_support (lq P)"
proof (cases "grd P (lower_tick P sqp) = sqp")
  case True
  then show ?thesis using refine_eq assms coarse_idx_refl
    by (simp add: pool_coarse_idx_def)
next
  case False
  show ?thesis
  proof
    fix l
    assume "l\<in> (\<lambda>j. pool_coarse_idx P' P j) ` nz_support (lq P')"
    hence "\<exists>k \<in> nz_support (lq P'). l = pool_coarse_idx P' P k" by auto
    from this obtain k where "k \<in> nz_support (lq P')" 
        and "l = pool_coarse_idx P' P k" by auto
    hence "lq P' k\<noteq> 0" unfolding nz_support_def by simp
    hence "lq P l \<noteq> 0" 
      using assms \<open>l = pool_coarse_idx P' P k\<close> refine_lq_idx_neq False by simp
    thus "l \<in> nz_support (lq P)" unfolding nz_support_def by simp
  qed
qed

lemma refine_nz_lq_ne:
  assumes "clmm_dsc P"
  and "P' = refine P sqp"
  and "nz_support (lq P) \<noteq> {}"
shows "nz_support (lq P') \<noteq> {}"
proof (cases "grd P (lower_tick P sqp) = sqp")
  case True
  then show ?thesis using refine_eq assms by simp
next
  case False
  have "\<exists>j. j\<in> (nz_support (lq P))" using assms by auto
  from this obtain j where "j \<in> nz_support (lq P)" by auto
  hence "lq P j\<noteq> 0" unfolding nz_support_def by simp
  hence "j\<in> nz_support (lq P') \<or> j+1 \<in> nz_support (lq P')" 
    unfolding nz_support_def
    by (smt (verit) False assms(2) mem_Collect_eq refine_lq refine_lq_arg_gt 
        wedge_arg_lt)
  thus "nz_support (lq P') \<noteq> {}" by auto
qed

lemma refine_nz_lq_emp:
  assumes "clmm_dsc P"
  and "P' = refine P sqp"
  and "nz_support (lq P) = {}"
shows "nz_support (lq P') = {}"
proof (cases "grd P (lower_tick P sqp) = sqp")
  case True
  then show ?thesis using refine_eq assms by simp
next
  case False
  {
    fix j
    have "lq P j = 0" "lq P (j-1) = 0" 
      using assms unfolding nz_support_def by simp+
    hence "lq P' j = 0" using assms refine_lq_arg_le refine_lq_arg_gt
      by (smt (verit, del_insts) False refine_lq wedge_arg_eq wedge_arg_gt)
  }
  thus ?thesis unfolding nz_support_def by simp
qed

lemma refine_idx_min_eq:
  assumes "clmm_dsc P"
  and "P' = refine P sqp"
  and "idx_min (lq P) \<le> lower_tick P sqp"
shows "idx_min (lq P') = idx_min (lq P)"
proof -
  interpret finite_liq_pool
    by (simp add: assms(1) clmm_dsc_liq(1) finite_liq_pool.intro)
  show ?thesis
  proof (cases "nz_support (lq P) = {}")
    case True
    hence "nz_support (lq P') = {}" using assms refine_nz_lq_emp by simp
    then show ?thesis by (simp add: True idx_min_def)
  next
    case False
    show ?thesis
    proof (rule idx_min_finiteI[symmetric])
      define i where "i = idx_min (lq P)"
      hence "lq P i \<noteq> 0" using False by (simp add: idx_min_mem nz_supportD)
      thus "lq P' i \<noteq> 0" using refine_lq_arg_le assms
        by (metis i_def refine_eq) 
      show "finite (nz_support (lq P'))" 
        using assms refine_finite_liq clmm_dsc_liq unfolding finite_liq_def 
        by simp
      fix j
      assume "j < i"
      hence "lq P j = 0" using i_def
        by (simp add: False fin_nz_sup idx_min_finite_lt)
      thus "lq P' j = 0" using refine_lq_arg_le assms
        by (metis \<open>j < i\<close> dual_order.strict_trans1 i_def leD nle_le refine_on_grd)
    qed
  qed
qed

lemma refine_idx_min_Suc_eq:
  assumes "clmm_dsc P"
  and "P' = refine P sqp"
  and "nz_support (lq P) \<noteq> {}"
  and "grd P (lower_tick P sqp) \<noteq> sqp"
  and "lower_tick P sqp < idx_min (lq P)"
shows "idx_min (lq P') = idx_min (lq P) + 1"
proof -
  interpret finite_liq_pool
    by (simp add: assms(1) clmm_dsc_liq(1) finite_liq_pool.intro)
  show ?thesis
  proof (rule idx_min_finiteI[symmetric])
    show "finite (nz_support (lq P'))" 
      using assms refine_finite_liq clmm_dsc_liq unfolding finite_liq_def 
      by simp
    define i where "i = idx_min (lq P)"
    hence "lq P i \<noteq> 0" using assms by (simp add: idx_min_mem nz_supportD)
    thus "lq P' (i+1) \<noteq> 0" using refine_lq_arg_gt assms i_def by simp
    fix j
    assume "j < i + 1"
    hence "lq P (j-1) = 0" using i_def
      by (simp add: assms fin_nz_sup idx_min_finite_lt)
    show "lq P' j = 0"
    proof (cases "j \<le> lower_tick P sqp")
      case True
      hence "lq P j = 0" using assms
        by (simp add: fin_nz_sup idx_min_finite_lt)
      thus "lq P' j = 0" using refine_lq_arg_le assms i_def True by simp
    next
      case False
      show ?thesis
      proof (cases "j = lower_tick P sqp + 1")
        case True
        then show ?thesis 
          using refine_lq_arg_Suc assms i_def \<open>lq P (j - 1) = 0\<close> by simp
      next
        case False
        hence "lower_tick P sqp < j - 1" using \<open>\<not> j \<le> lower_tick P sqp\<close> by simp
        thus ?thesis 
          using \<open>lq P (j-1) = 0\<close> refine_lq_arg_gt assms i_def by fastforce
      qed
    qed
  qed
qed

lemma refine_grd_min:
  assumes "clmm_dsc P"
  and "P' = refine P sqp"
  and "nz_support (lq P) \<noteq> {}"
shows "grd_min P = grd_min P'"
proof (cases "grd P (lower_tick P sqp) = sqp")
  case True
  hence "P = P'" using assms refine_eq by simp
  then show ?thesis by simp
next
  case False
  define i where "i = idx_min (lq P)"
  define k where "k = lower_tick P sqp"
  show ?thesis
  proof (cases "i \<le> k")
    case True
    hence "idx_min (lq P') = i" 
      using i_def refine_idx_min_eq k_def assms by simp
    moreover have "grd P' i = grd P i" 
      using refine_grd_arg_le assms k_def True by simp
    ultimately show ?thesis unfolding grd_min_def idx_min_img_def i_def by simp
  next
    case False
    hence "idx_min (lq P') = i+1" 
      using assms \<open>grd P (lower_tick P sqp) \<noteq> sqp\<close> refine_idx_min_Suc_eq 
        k_def i_def
      by simp
    moreover have "grd P' (i+1) = grd P i" 
      using refine_grd_arg_gt[of "lower_tick P sqp" P sqp P' i] \<open>\<not> i \<le> k\<close> 
        assms calculation i_def k_def refine_eq 
      by fastforce
    ultimately show ?thesis unfolding grd_min_def idx_min_img_def i_def by simp
  qed
qed

lemma refine_idx_max_eq:
  assumes "clmm_dsc P"
  and "P' = refine P sqp"
  and "idx_max (lq P) < lower_tick P sqp"
shows "idx_max (lq P') = idx_max (lq P)"
proof -
  interpret finite_liq_pool
    by (simp add: assms(1) clmm_dsc_liq(1) finite_liq_pool.intro)
  show ?thesis
  proof (cases "grd P (lower_tick P sqp) = sqp")
    case True
    hence "P' = P" using refine_eq assms by simp
    then show ?thesis by simp
  next
    case False
    show ?thesis
    proof (cases "nz_support (lq P) = {}")
      case True
      hence "nz_support (lq P') = {}" using assms refine_nz_lq_emp by simp
      then show ?thesis by (simp add: True idx_max_def)
    next
      case False
      show ?thesis
      proof (rule idx_max_finiteI[symmetric])
        define i where "i = idx_max (lq P)"
        hence "lq P i \<noteq> 0" using False by (simp add: idx_max_mem nz_supportD)
        thus "lq P' i \<noteq> 0" using refine_lq_arg_le assms
          by (metis i_def refine_on_grd zle_add1_eq_le zless_add1_eq)
        show "finite (nz_support (lq P'))" 
          using assms refine_finite_liq clmm_dsc_liq unfolding finite_liq_def 
          by simp
        fix j
        assume "i < j"
        hence "lq P j = 0" using i_def False fin_nz_sup idx_max_finite_gt by auto
        show "lq P' j = 0" 
        proof (cases "j \<le> lower_tick P sqp")
          case True
          then show ?thesis
            by (metis \<open>lq P j = 0\<close> assms(2) refine_eq refine_lq_arg_le)
        next
          case False
          show ?thesis
          proof (cases "j = lower_tick P sqp + 1")
            case True
            hence "lq P' j = lq P (lower_tick P sqp)" 
              using assms refine_lq_arg_Suc
              by (metis \<open>lq P j = 0\<close>  fin_nz_sup idx_max_finite_gt refine_eq)
            also have "... = 0" 
              using assms idx_max_finite_gt by (metis fin_nz_sup)
            finally show ?thesis .
          next
            case False
            hence "i < j-1" using i_def assms \<open>\<not> j \<le> lower_tick P sqp\<close> by simp
            have "lq P' j = lq P (j-1)" 
              using refine_lq_arg_gt[of _ P sqp P' "j-1"] False
                \<open>\<not> j \<le> lower_tick P sqp\<close> \<open>grd P (lower_tick P sqp) \<noteq> sqp\<close> assms 
              by simp
            also have "... = 0" 
              using \<open>i < j-1\<close> i_def False fin_nz_sup idx_max_finite_gt by metis
            finally show ?thesis .
          qed
        qed
      qed
    qed
  qed
qed

lemma refine_idx_max_Suc_eq:
  assumes "clmm_dsc P"
  and "P' = refine P sqp"
  and "nz_support (lq P) \<noteq> {}"
  and "grd P (lower_tick P sqp) \<noteq> sqp"
  and "lower_tick P sqp \<le> idx_max (lq P)"
shows "idx_max (lq P') = idx_max (lq P) + 1"
proof -
  interpret finite_liq_pool
    by (simp add: assms(1) clmm_dsc_liq(1) finite_liq_pool.intro)
  show ?thesis
  proof (rule idx_max_finiteI[symmetric])
    show "finite (nz_support (lq P'))" 
      using assms refine_finite_liq clmm_dsc_liq unfolding finite_liq_def 
      by simp
    define i where "i = idx_max (lq P)"
    hence "lq P i \<noteq> 0" using assms by (simp add: idx_max_mem nz_supportD)
    show "lq P' (i+1) \<noteq> 0"
    proof (cases "i = lower_tick P sqp")
      case True
      then show ?thesis 
        using refine_lq_arg_Suc assms \<open>lq P i \<noteq> 0\<close> unfolding i_def by simp
    next
      case False
      then show ?thesis using refine_lq_arg_gt assms \<open>lq P i \<noteq> 0\<close> i_def by simp
    qed
    fix j
    assume "i + 1 < j"
    hence "lq P' j = lq P (j-1)" 
      using refine_lq_arg_gt[of _ P _ P' "j-1"] assms i_def \<open>i + 1 < j\<close> 
        fin_nz_sup i_def 
      by force
    also have "... = 0" using i_def \<open>i + 1 < j\<close>
      by (simp add: assms fin_nz_sup idx_max_finite_gt)
    finally show "lq P' j = 0" .
  qed
qed

lemma refine_lower_tick_idx_max:
  assumes "clmm_dsc P"
  and "0 < sqp"
  and "P' = refine P sqp"
  and "nz_support (lq P) \<noteq> {}"
  and "lower_tick P sqp \<le> idx_max (lq P)"
shows "lower_tick P' sqp \<le> idx_max (lq P')"
proof (cases "grd P (lower_tick P sqp) = sqp")
  case True
  then show ?thesis using assms refine_eq by simp
next
  case False
  hence "idx_max (lq P') = idx_max (lq P) + 1" 
    using assms refine_idx_max_Suc_eq by simp
  moreover have "lower_tick P' sqp = lower_tick P sqp + 1" 
    using False refine_lower_tick_idx
    by (simp add: assms(1-3))
  ultimately show ?thesis using assms by simp
qed
  
lemma refine_grd_max:
  assumes "clmm_dsc P"
  and "P' = refine P sqp"
  and "nz_support (lq P) \<noteq> {}"
shows "grd_max P = grd_max P'"
proof (cases "grd P (lower_tick P sqp) = sqp")
  case True
  hence "P = P'" using assms refine_eq by simp
  then show ?thesis by simp
next
  case False
  define i where "i = idx_max (lq P)"
  define k where "k = lower_tick P sqp"
  show ?thesis
  proof (cases "i < k")
    case True
    hence "idx_max (lq P') = i" 
      using i_def refine_idx_max_eq k_def assms by simp
    moreover have "grd P' (i+1) = grd P (i+1)" 
      using refine_grd_arg_le assms k_def True by simp
    ultimately show ?thesis 
      unfolding grd_max_def idx_max_img_def i_def by simp
  next
    case False
    hence "idx_max (lq P') = i+1" 
      using assms \<open>grd P (lower_tick P sqp) \<noteq> sqp\<close> refine_idx_max_Suc_eq 
        k_def i_def
      by simp
    moreover have "grd P' (i+2) = grd P (i+1)" 
      using refine_grd_arg_gt[of "lower_tick P sqp" P sqp P' "i+1"] \<open>\<not> i < k\<close> 
        assms calculation i_def k_def refine_eq
      by (metis is_num_normalize(1) one_add_one verit_comp_simplify1(3) 
          zle_add1_eq_le)      
    ultimately show ?thesis unfolding grd_max_def idx_max_img_def i_def
      by (simp add: add.commute)
  qed
qed

lemma refine_quote_gross:
  assumes "clmm_dsc P"
  and "P' = refine P sqp"
  and "0 < sqp"
shows "quote_gross P' = quote_gross P"
proof (rule finer_clmm.finer_quote_gross_eq)
  show "finer_clmm P' P" 
  proof
    show "clmm_dsc P" using assms by simp
    show "clmm_dsc P'" using assms refine_clmm by simp
    show "finer_pool P' P" using assms refine_finer by simp
  qed
qed

lemma refine_nonzero_liq:
  assumes "clmm_dsc P"
  and "lower_tick P sqp \<le> i"
  and "grd P (lower_tick P sqp) \<noteq> sqp"
  and "P' = refine P sqp"
  and "L = lq P"
  and "L' = lq P'"
shows "{l. L' l \<noteq> 0 \<and> i+1 < l} = (\<lambda>i. i + 1) ` {k. L k \<noteq> 0 \<and> i < k}"
proof
  show "{l. L' l \<noteq> 0 \<and> i+1 < l} \<subseteq> (\<lambda>i. i + 1) ` {k. L k \<noteq> 0 \<and> i < k}"
  proof
    fix x
    assume "x \<in> {l. L' l \<noteq> 0 \<and> i+1 < l}"
    hence "L' x \<noteq> 0" and "i+1 < x" by simp+
    hence "L' x = L (x-1)" using assms(2-6) refine_lq by auto 
    moreover have "i < x-1" using \<open>i+1 < x\<close> by simp
    ultimately have "x-1 \<in> {k. L k \<noteq> 0 \<and> i < k}" using \<open>L' x \<noteq> 0\<close> by auto
    thus "x \<in> (\<lambda>i. i + 1) ` {k. L k \<noteq> 0 \<and> i < k}"
      by (simp add: rev_image_eqI)
  qed
next
  show "(\<lambda>i. i + 1) ` {k. L k \<noteq> 0 \<and> i < k} \<subseteq> {l. L' l \<noteq> 0 \<and> i + 1 < l}"
  proof
    fix x
    assume "x \<in> (\<lambda>i. i + 1) ` {k. L k \<noteq> 0 \<and> i < k}"
    hence "\<exists>y. y \<in> {k. L k \<noteq> 0 \<and> i < k} \<and> x = y+1" by auto
    from this obtain y where "y \<in> {k. L k \<noteq> 0 \<and> i < k}" and "x = y+1" by auto
    hence "L y \<noteq> 0" and "i < y" by simp+
    hence "L' x \<noteq> 0" using \<open>x = y + 1\<close> assms(2-6) refine_lq_arg_gt by auto 
    moreover have "i+1 < x" using \<open>x = y+1\<close> \<open>i < y\<close> by simp
    ultimately show "x\<in> {l. L' l \<noteq> 0 \<and> i + 1 < l}" by auto
  qed
qed

lemma refine_pool_base_net_grd_eq:
  assumes "clmm_dsc P"
  and "nz_support (lq P) \<noteq> {}"
  and "P' = refine P sqp"
  and "0 < sqp"
  and "sqp < grd_max P"
  and "grd P (lower_tick P sqp) \<noteq> sqp"
  and "sqp \<le> sqp'"
shows "base_net P' sqp' = base_net P sqp'"
proof -
  have "clmm_dsc P'" using assms refine_clmm by simp
  define L where "L = lq P"
  define L' where "L' = lq P'"
  define j where "j = lower_tick P' sqp'"
  define i where "i = lower_tick P sqp'" 
  have "lower_tick P sqp \<le> i" using assms(1,4,7) i_def lower_tick_mono by auto
  have "j = i + 1"  using refine_ge_lower_tick assms j_def i_def by simp
  have "base_net P' sqp' = L' j * (inverse sqp' - inverse (grd P' (j + 1))) + 
      (\<Sum>l | L' l \<noteq> 0 \<and> j < l. 
      L' l * (inverse (grd P' l) - inverse (grd P' (l + 1))))" 
    using base_net_sum j_def L'_def assms \<open>clmm_dsc P'\<close> by auto
  also have "... = L i * (inverse sqp' - inverse (grd P (i + 1))) + 
      (\<Sum>l | L' l \<noteq> 0 \<and> j < l. 
      L' l * (inverse (grd P' l) - inverse (grd P' (l + 1))))" 
  proof -
    have "grd P' (j+1) = grd P (i+1)" 
      using refine_grd_arg_gt \<open>j = i + 1\<close> assms(1,3,4,6,7) i_def lower_tick_mono 
        zle_add1_eq_le 
      by presburger
    moreover have "L i = L' j" using refine_lq_arg_Suc \<open>j = i + 1\<close>
      by (metis L'_def L_def assms(1,3,4,6,7) i_def lower_tick_mono refine_lq_arg_gt 
          zle_add1_eq_le zless_add1_eq)
    ultimately show ?thesis by simp
  qed
  also have "... = L i * (inverse sqp' - inverse (grd P (i + 1))) + 
      (\<Sum>k | L k \<noteq> 0 \<and> i < k. 
      L k * (inverse (grd P k) - inverse (grd P (k + 1))))"
  proof -
    have "(\<Sum>l | L' l \<noteq> 0 \<and> j < l. 
        L' l * (inverse (grd P' l) - inverse (grd P' (l + 1)))) = 
        (\<Sum>k | L k \<noteq> 0 \<and> i < k. 
        L k * (inverse (grd P k) - inverse (grd P (k + 1))))"
    proof (rule sum.reindex_cong)
      define sc where "sc = (\<lambda>(i::int). i + 1)"
      show "inj_on sc {k. L k \<noteq> 0 \<and> i < k}" using sc_def by simp
      have "{l. L' l \<noteq> 0 \<and> i+1 < l} = (\<lambda>i. i + 1) ` {k. L k \<noteq> 0 \<and> i < k}"
      proof (rule refine_nonzero_liq) 
        show "lower_tick P sqp \<le> i" 
          using i_def assms(1,4,7) lower_tick_mono by auto
      qed (simp add: assms L_def L'_def)+
      thus "{i. L' i \<noteq> 0 \<and> j < i} = (\<lambda>i. i + 1) ` {k. L k \<noteq> 0 \<and> i < k}" 
        using \<open>j = i+1\<close> by simp
      fix x
      assume asx: "x \<in> {k. L k \<noteq> 0 \<and> i < k}"
      hence " L' (x + 1) = L x" using \<open>lower_tick P sqp \<le> i\<close>
        by (simp add: L'_def L_def assms(3) assms(6) refine_lq_arg_gt)
      moreover have "grd P' (x + 1) = grd P x"
        using \<open>lower_tick P sqp \<le> i\<close> asx assms(3,6) refine_grd_arg_gt by auto 
      moreover have "grd P' (x + 1 + 1) = grd P (x + 1)" 
      proof -
        have "i < x + 1" using asx by simp
        thus ?thesis using \<open>lower_tick P sqp \<le> i\<close>
          by (metis assms(3) assms(6) order.strict_trans refine_grd_arg_gt 
              zle_add1_eq_le zless_add1_eq)
      qed
      ultimately show "L' (x + 1) * 
          (inverse (grd P' (x + 1)) - inverse (grd P' (x + 1 + 1))) = 
          L x * (inverse (grd P x) - inverse (grd P (x + 1)))" 
        by simp
    qed
    thus ?thesis by simp
  qed
  also have "... = base_net P sqp'" 
    using base_net_sum i_def L_def assms \<open>clmm_dsc P'\<close> by auto
  finally show ?thesis .
qed

lemma refine_base_net_eq:
  assumes "clmm_dsc P"
  and "nz_support (lq P) \<noteq> {}"
  and "P' = refine P sqp"
  and "0 < sqp"
  and "sqp < grd_max P"
  and "sqp \<le> sqp'"
shows "base_net P' sqp' = base_net P sqp'"
proof (cases "grd P (lower_tick P sqp) = sqp")
  case True
  then show ?thesis by (simp add: assms(3) refine_eq) 
next
  case False
  then show ?thesis using assms refine_pool_base_net_grd_eq by simp
qed

subsection \<open>CLMM pool restriction and slice\<close>

text \<open>The restriction operation intuitively consists in deleting all the liquidity 
potentially available below the index provided as an argument.\<close>

definition restrict_pool where
"restrict_pool i P = 
  (grd P, 
   (\<lambda>j. if j < i then 0 else lq P j), 
   (\<lambda>j.  fee P j))"

lemma restrict_pool_grd[simp]: 
  shows "grd (restrict_pool i P) = grd P" 
  unfolding restrict_pool_def grd_def by simp

lemma restrict_pool_lower_tick:
  assumes "P' = restrict_pool i P"
  shows "lower_tick P sqp = lower_tick P' sqp" 
  using assms unfolding lower_tick_def rng_blw_def by simp

lemma restrict_pool_lt:
  assumes "j < i"
  shows "lq (restrict_pool i P) j = 0" "fee (restrict_pool i P) j = fee P j"
  using assms unfolding restrict_pool_def lq_def fee_def by auto

lemma restrict_pool_ge:
  assumes "i \<le> j"
  shows "lq (restrict_pool i P) j = lq P j" 
    "fee (restrict_pool i P) j = fee P j"
  using assms unfolding restrict_pool_def lq_def fee_def by auto

lemma restrict_pool_lq_sub:
  assumes "P' = restrict_pool i P"
  shows "nz_support (lq P') \<subseteq> nz_support (lq P)"
proof
  fix j
  assume "j \<in> nz_support (lq P')"
  hence "i \<le> j" 
    using restrict_pool_lt assms linorder_le_less_linear 
    unfolding nz_support_def by blast
  hence "lq P j \<noteq> 0"
    by (metis \<open>j \<in> nz_support (lq P')\<close> assms nz_supportD restrict_pool_ge(1))
  thus "j \<in> nz_support (lq P)" unfolding nz_support_def by auto
qed

lemma restrict_pool_finite_liq:
  assumes "finite_liq P"
  and "P' = restrict_pool i P"
shows "finite_liq P'" using restrict_pool_lq_sub assms unfolding finite_liq_def
  by (metis rev_finite_subset) 

lemma restrict_pool_nz_liq:
  assumes "finite_liq P"
  and "P' = restrict_pool i P"
  and "i \<le> idx_max (lq P)"
  and "nz_support (lq P) \<noteq> {}"
shows "nz_support (lq P') \<noteq> {}"
proof -
  have "lq P' (idx_max (lq P)) \<noteq> 0"
    by (simp add: assms finite_liq_pool.idx_max_mem finite_liq_pool_def 
        nz_supportD restrict_pool_ge(1))
  thus ?thesis unfolding nz_support_def by auto
qed

lemma restrict_pool_idx_max:
  assumes "finite_liq P"
  and "P' = restrict_pool i P"
  and "i \<le> idx_max (lq P)"
  and "nz_support (lq P) \<noteq> {}"
shows "idx_max (lq P) = idx_max (lq P')"
proof (rule idx_max_finiteI)
  show "finite (nz_support (lq P'))" 
    using assms finite_liq_def restrict_pool_finite_liq by simp
  show "lq P' (idx_max (lq P)) \<noteq> 0" 
    by (simp add: assms finite_liq_pool.idx_max_mem finite_liq_pool_def 
        nz_supportD restrict_pool_ge(1))
  fix j
  assume "idx_max (lq P) < j"
  hence "lq P j = 0"
    using assms(1) assms(4) finite_liq_def idx_max_finite_gt by blast
  thus "lq P' j = 0"
    using \<open>idx_max (lq P) < j\<close> assms(2) assms(3) restrict_pool_ge(1) by auto
qed

lemma restrict_pool_clmm:
  assumes "clmm_dsc P"
and "P' = restrict_pool i P"
shows "clmm_dsc P'"
proof
  show "span_grid P'" using assms restrict_pool_grd span_grid_eq by auto
  show "finite_liq P'" 
    using assms restrict_pool_finite_liq clmm_dsc_liq by simp
  show "\<forall>i. 0 \<le> lq P' i"
    by (metis assms clmm_dsc_liq(2) not_le_imp_less order_refl 
        restrict_pool_ge(1) restrict_pool_lt(1)) 
  show "\<forall>i. 0 \<le> fee P' i"
    by (metis assms clmm_dsc_def leI restrict_pool_ge(2) 
        restrict_pool_lt(2))
  show "\<forall>i. fee P' i < 1"
    by (metis assms clmm_dsc_fees leI restrict_pool_ge(2) restrict_pool_lt(2))
qed

lemma restrict_pool_quote_gross_leq:
  assumes "mono (grd P)"
  and "sqp \<le> grd P i"
  and "P' = restrict_pool i P"
  shows "quote_gross P' sqp = 0" unfolding quote_gross_def
proof (rule gen_quote_zero)
  show "mono (grd P')" using assms restrict_pool_grd by simp
  fix j
  assume "grd P' j < sqp"
  hence "grd P j < sqp" using restrict_pool_grd assms by simp
  hence "grd P j < grd P i" using assms by simp
  hence "j < i" using assms mono_strict_invE by auto
  hence "lq P' j = 0" by (simp add: assms restrict_pool_lt)
  thus "gross_fct (lq P') (fee P') j = 0" unfolding gross_fct_def by simp
qed

lemma restrict_pool_quote_gross:
  assumes "clmm_dsc P"
  and "P' = restrict_pool j P"
  and "0 < sqp"
  and "j \<le> lower_tick P sqp"
shows "quote_gross P sqp - quote_gross P (grd P j) = quote_gross P' sqp" 
proof -
  define L where "L = gross_fct (lq P) (fee P)"
  define L' where "L' = gross_fct (lq P') (fee P')"
  define k where "k = lower_tick P sqp"
  have "clmm_dsc P'" using restrict_pool_clmm assms by simp
  have eq: "\<forall>k \<ge> j. L' k = L k" 
    using restrict_pool_ge gross_fct_cong L'_def L_def assms(2) by blast
  have "grd P k \<le> sqp" using lower_tick_geq assms unfolding k_def by simp
  have "j = lower_tick P (grd P j)"
    by (simp add: assms(1) lower_tick_eq)
  hence "j = lower_tick P' (grd P j)" 
    using restrict_pool_lower_tick[of P'] assms by simp
  have "k = lower_tick P' sqp" 
    using k_def assms restrict_pool_lower_tick by blast
  show ?thesis
  proof (cases "j = k")
    case True
    have "quote_gross P sqp - quote_gross P (grd P j) = L j * (sqp - grd P j)" 
      using clmm_quote_gross_diff_eq'[of P L j]
      by (metis L_def True \<open>grd P k \<le> sqp\<close> assms(1) clmm_dsc_grid(2) k_def 
          lower_tick_eq)
    also have "... = L' j * (sqp - grd P j)" using eq by simp
    also have "... = quote_gross P' sqp - quote_gross P' (grd P j)"
    proof (rule clmm_quote_gross_diff_eq'[symmetric])
      show "clmm_dsc P'" using \<open>clmm_dsc P'\<close> .
      show "L' = gross_fct (lq P') (fee P')" using L'_def by simp
      show "j = lower_tick P' sqp" 
        using True restrict_pool_lower_tick[of P'] assms k_def by simp
      show "j = lower_tick P' (grd P j)" using \<open>j = lower_tick P' (grd P j)\<close> .
      show "0 < grd P j" using assms by simp
      show "grd P j \<le> sqp" using True \<open>grd P k \<le> sqp\<close> k_def by auto
    qed
    also have "... = quote_gross P' sqp" 
      using assms restrict_pool_quote_gross_leq
      by (simp add: strict_mono_mono)
    finally show ?thesis .
  next
    case False
    define M where "M = {l. L l \<noteq> 0 \<and> j <l \<and> l < k}"
    define M' where "M' = {l. L' l \<noteq> 0 \<and> j <l \<and> l < k}"
    have "M = M'" using eq unfolding M_def M'_def by auto
    have "quote_gross P sqp - quote_gross P (grd P j) = L k * (sqp - grd P k) + 
        sum (\<lambda> l. L l * (grd P (l+1) - grd P l)) M + 
        L j * (grd P (j+1) - grd P j)" unfolding M_def
    proof (rule clmm_quote_gross_diff_eq)
      show "j < k" using assms k_def False by simp
      show "L = gross_fct (lq P) (fee P)" using L_def by simp
      show "j = lower_tick P (grd P j)" using assms lower_tick_eq by simp
      show "clmm_dsc P" using assms by simp
      show "k = lower_tick P sqp" using k_def by simp
      show "0 < grd P j" using assms by simp
      show "grd P j \<le> sqp"
        using \<open>grd P k \<le> sqp\<close> \<open>j < k\<close> assms(1) clmm_dsc_grd_smono by fastforce
    qed
    also have "... = L' k * (sqp - grd P' k) + 
        (\<Sum>l\<in>M'. L' l * (grd P' (l + 1) - grd P' l)) + 
        L' j * (grd P' (j + 1) - grd P' j)" 
    proof - 
      have "L' k = L k" using eq assms k_def by simp
      moreover have "L j = L' j" using eq by simp
      moreover have "(\<Sum>k\<in>M. L' k * (grd P' (k + 1) - grd P' k)) = 
          (\<Sum>k\<in>M. L k * (grd P (k + 1) - grd P k))"
        using eq sum.cong M_def assms by simp
      ultimately show ?thesis using assms \<open>M = M'\<close> by simp
    qed
    also have "... = quote_gross P' sqp - quote_gross P' (grd P' j)" 
      unfolding M'_def 
    proof (rule clmm_quote_gross_diff_eq[symmetric])
      show "clmm_dsc P'" using \<open>clmm_dsc P'\<close> .
      show "L' = gross_fct (lq P') (fee P')" using L'_def by simp
      show "j = lower_tick P' (grd P' j)" 
        using \<open>j = lower_tick P (grd P j)\<close>
        by (simp add: \<open>clmm_dsc P'\<close> lower_tick_eq)
      show "k = lower_tick P' sqp" using \<open>k = lower_tick P' sqp\<close> .
      show "0 < grd P' j" by (simp add: \<open>clmm_dsc P'\<close>)
      show "grd P' j \<le> sqp"
        using \<open>j = lower_tick P (grd P j)\<close> assms lower_tick_lt' by fastforce
      show "j < k" using assms False k_def by simp
    qed
    also have "... = quote_gross P' sqp"
    proof -
      have "quote_gross P' (grd P' j) = 0" 
        using assms restrict_pool_quote_gross_leq
        by (simp add: strict_mono_mono)
      thus ?thesis by simp
    qed
    finally show ?thesis .
  qed
qed

lemma restrict_pool_base_net_eq:
  assumes "clmm_dsc P"
  and "nz_support (lq P) \<noteq> {}"
  and "P' = restrict_pool i P"
  and "i \<le> idx_max (lq P)"
  and "grd P i \<le> sqp'"
shows "base_net P' sqp' = base_net P sqp'"
proof -
  have "clmm_dsc P'" using assms restrict_pool_clmm by simp
  have "0 < grd P i" using assms by simp
  hence "0 < sqp'" using assms by linarith
  define L where "L = lq P"
  define L' where "L' = lq P'"
  define j where "j = lower_tick P' sqp'"
  have "base_net P' sqp' = L' j * (inverse sqp' - inverse (grd P' (j + 1))) + 
      (\<Sum>i | L' i \<noteq> 0 \<and> j < i. 
      L' i * (inverse (grd P' i) - inverse (grd P' (i + 1))))" 
    using base_net_sum j_def L'_def assms \<open>clmm_dsc P'\<close> \<open>0 < sqp'\<close> by auto
  also have "... = L j * (inverse sqp' - inverse (grd P (j + 1))) + 
      (\<Sum>i | L i \<noteq> 0 \<and> j < i. 
      L i * (inverse (grd P i) - inverse (grd P (i + 1))))"
  proof -
    have grd: "\<And>k. i < k \<Longrightarrow> grd P k = grd P' k" using assms by simp
    have lq: "\<And>k. j \<le> k \<Longrightarrow> L k = L' k"
      by (metis L'_def L_def \<open>clmm_dsc P'\<close> assms(3) assms(5) clmm_dsc_grid(2) 
          j_def lower_tick_eq lower_tick_lt order.trans restrict_pool_ge(1) 
          restrict_pool_grd verit_comp_simplify1(3)) 
    hence "L' j * (inverse sqp' - inverse (grd P' (j + 1))) = 
        L j * (inverse sqp' - inverse (grd P (j + 1)))" 
      using grd assms(3) by simp
    moreover have "(\<Sum>i | L' i \<noteq> 0 \<and> j < i. 
        L' i * (inverse (grd P' i) - inverse (grd P' (i + 1)))) = 
        (\<Sum>i | L i \<noteq> 0 \<and> j < i. 
        L i * (inverse (grd P i) - inverse (grd P (i + 1))))" 
    proof (rule sum.cong)
      show "{i. L' i \<noteq> 0 \<and> j < i} = {i. L i \<noteq> 0 \<and> j < i}" 
        using lq by auto
      fix k
      assume "k \<in> {i. L i \<noteq> 0 \<and> j < i}"
      thus "L' k * (inverse (grd P' k) - inverse (grd P' (k + 1))) = 
          L k * (inverse (grd P k) - inverse (grd P (k + 1)))" 
        using lq grd assms(3) by simp
    qed
    ultimately show ?thesis by simp
  qed
  also have "... = base_net P sqp'" 
    using base_net_sum L_def assms j_def \<open>0 < sqp'\<close> restrict_pool_lower_tick 
    by presburger
  finally show ?thesis .
qed

lemma restrict_pool_grd_min_le:
  assumes "clmm_dsc P"
  and "nz_support (lq P) \<noteq> {}"
  and "P' = restrict_pool i P"
  and "i \<le> idx_max (lq P)"
shows "i \<le> idx_min (lq P')" 
  by (metis assms clmm_dsc_def finite_liq_def finite_subset idx_min_finite_in 
      leI restrict_pool_lq_sub restrict_pool_lt(1) restrict_pool_nz_liq)

definition slice_pool where
"slice_pool P sqp = (let P' = refine P sqp in restrict_pool (lower_tick P' sqp) P')"

lemma slice_poolD:
  assumes "P'' = refine P sqp"
shows "slice_pool P sqp = restrict_pool (lower_tick P'' sqp) P''" 
  using assms unfolding slice_pool_def Let_def by simp

lemma slice_pool_clmm_dsc:
  assumes "clmm_dsc P"
  and "0 < sqp"
  and "P' = slice_pool P sqp"
shows "clmm_dsc P'" 
proof -
  have "clmm_dsc (restrict_pool (lower_tick (refine P sqp) sqp) (refine P sqp))"    
  proof (rule restrict_pool_clmm)
    show "clmm_dsc (refine P sqp)"
      by (rule refine_clmm, (auto simp add: assms)+)
  qed simp
  thus ?thesis using assms unfolding slice_pool_def Let_def by simp
qed

lemma slice_pool_nz_liq:
  assumes "clmm_dsc P"
  and "0 < sqp"
  and "P' = slice_pool P sqp"
  and "lower_tick P sqp \<le> idx_max (lq P)"
  and "nz_support (lq P) \<noteq> {}"
shows "nz_support (lq P') \<noteq> {}" 
proof (rule restrict_pool_nz_liq)
  define Pr where "Pr = refine P sqp"
  define i where "i = lower_tick Pr sqp"
  show "P' = restrict_pool i Pr" 
    using slice_poolD assms Pr_def i_def by simp
  show "finite_liq Pr" using Pr_def
    by (meson assms(1) clmm_dsc_def refine_finite_liq)
  show "nz_support (lq (refine P sqp)) \<noteq> {}" 
    using restrict_pool_nz_liq
    by (meson assms(1) assms(5) refine_nz_lq_ne)
  show "i \<le> idx_max (lq Pr)" using i_def Pr_def refine_lower_tick_idx_max
    by (simp add: assms(1,2,4,5))
qed  

lemma slice_pool_tick_idx_max:
  assumes "clmm_dsc P"
  and "0 < sqp"
  and "P' = slice_pool P sqp"
  and "lower_tick P sqp \<le> idx_max (lq P)"
  and "nz_support (lq P) \<noteq> {}"
shows "lower_tick P' sqp \<le> idx_max (lq P')" 
proof -
  define Pr where "Pr = refine P sqp"
  define i where "i = lower_tick Pr sqp"
  have "lower_tick P' sqp = i" 
    using assms restrict_pool_lower_tick Pr_def i_def 
    unfolding slice_pool_def Let_def
    by presburger 
  also have "... \<le> idx_max (lq Pr)" using i_def Pr_def refine_lower_tick_idx_max
    by (simp add: assms(1,2,4,5))
  also have "... = idx_max (lq P')"
    using Pr_def assms(1-5) clmm_dsc_liq(1) refine_clmm refine_lower_tick_idx_max 
      refine_nz_lq_ne restrict_pool_idx_max slice_poolD 
    by presburger 
  finally show ?thesis .
qed

lemma slice_pool_nz_liq':
  assumes "clmm_dsc P"
  and "P' = slice_pool P sqp"
  and "nz_support (lq P) \<noteq> {}"
  and "0 < sqp"
  and "sqp < grd_max P"
shows "nz_support (lq P') \<noteq> {}" 
proof -
  have "lower_tick P sqp < idx_max (lq P) + 1" 
  proof (rule lower_tick_lt')
    show "clmm_dsc P" using assms by simp
    show "0 < sqp" using assms by simp
    show "idx_max (lq P) + 1 = lower_tick P (grd_max P)"
      by (simp add: assms(1) idx_max_img_def lower_tick_eq grd_max_def)
    show "sqp < grd_max P" using assms by simp
    show "grd P (idx_max (lq P) + 1) = grd_max P" 
      unfolding grd_max_def idx_max_img_def by simp
  qed simp
  thus ?thesis using slice_pool_nz_liq by (simp add: assms)
qed

lemma slice_pool_idx_min:
  assumes "clmm_dsc P"
  and "0 < sqp"
  and "nz_support (lq P) \<noteq> {}"
  and "P' = slice_pool P sqp"
  and "i = lower_tick P sqp"
  and "i \<le> idx_max (lq P)"
shows "i \<le> idx_min (lq P')" 
proof (rule idx_min_finite_max)
  show "nz_support (lq P') \<noteq> {}" using assms slice_pool_nz_liq by simp
  show "finite (nz_support (lq P'))"
    using assms clmm_dsc_liq(1) finite_liq_def slice_pool_clmm_dsc by simp
  fix j
  assume "j < i"
  thus "lq P' j = 0"
    by (metis assms(1,2,4,5) lower_tick_eq not_le_imp_less order.strict_trans2 
        order_less_imp_not_less refine_grd_arg_le refine_lower_tick 
        restrict_pool_lt(1) slice_poolD)
qed

lemma slice_pool_grd_min:
  assumes "clmm_dsc P"
  and "0 < sqp"
  and "nz_support (lq P) \<noteq> {}"
  and "P' = slice_pool P sqp"
  and "sqp < grd_max P"
shows "sqp \<le> grd_min P'"
proof -
  define Pr where "Pr = refine P sqp"
  define i where "i = lower_tick Pr sqp"
  have "P' = restrict_pool i Pr" using i_def Pr_def
    by (simp add: assms(4) slice_poolD)
  hence "i \<le> idx_min (lq P')" 
    using restrict_pool_grd_min_le Pr_def assms(1-3,5) i_def refine_clmm 
      refine_lower_tick_idx_max refine_nz_lq_ne sqp_lt_grd_max_imp_idx 
    by presburger
  moreover have "grd P' i = sqp"
    using Pr_def \<open>P' = restrict_pool i Pr\<close> assms(1,2) i_def refine_lower_tick 
    by auto 
  ultimately show ?thesis using grd_min_def idx_min_img_def
    by (metis Pr_def \<open>P' = restrict_pool i Pr\<close> assms(1,2) clmm_dsc_grd_mono 
        refine_clmm restrict_pool_clmm) 
qed

lemma slice_pool_grd_max:
  assumes "clmm_dsc P"
  and "0 < sqp"
  and "nz_support (lq P) \<noteq> {}"
  and "P' = slice_pool P sqp"
  and "lower_tick P sqp \<le> idx_max (lq P)"
shows "grd_max P = grd_max P'" using assms slice_pool_tick_idx_max
proof -
  define Pr where "Pr = refine P sqp"
  have "grd_max P = grd_max Pr" using assms refine_grd_max Pr_def by simp
  also have "... = grd_max P'" 
    using restrict_pool_idx_max Pr_def assms(1-5) clmm_dsc_liq(1) 
      refine_finite_liq refine_lower_tick_idx_max refine_nz_lq_ne 
      slice_poolD 
    unfolding grd_max_def idx_max_img_def 
    by auto
  finally show ?thesis .
qed

lemma slice_pool_grd_max':
  assumes "clmm_dsc P"
  and "nz_support (lq P) \<noteq> {}"
  and "P' = slice_pool P sqp"
  and "0 < sqp"
  and "sqp < grd_max P"
shows "grd_max P = grd_max P'" 
proof -
  define Pr where "Pr = refine P sqp"
  have "grd_max P = grd_max Pr" using assms refine_grd_max Pr_def by simp
  also have "... = grd_max P'" 
    using restrict_pool_idx_max  Pr_def assms(1-5) 
      clmm_dsc_liq(1) refine_finite_liq refine_lower_tick_idx_max refine_nz_lq_ne 
      slice_poolD restrict_pool_grd sqp_lt_grd_max_imp_idx 
    unfolding grd_max_def idx_max_img_def by auto 
  finally show ?thesis .
qed

lemma slice_pool_cst_fees:
  assumes "clmm_dsc P"
  and "P' = slice_pool P sqp"
  and "\<And>i. fee P i = phi"
shows "\<And>i. fee P' i = phi"
  by (metis assms(2,3) refine_cst_fees restrict_pool_ge(2) restrict_pool_lt(2) 
      slice_poolD verit_comp_simplify1(3))

lemma slice_pool_quote_gross_leq:
  assumes "clmm_dsc P"
  and "0 < sqp"
  and "sqp' \<le> sqp"
  and "P' = slice_pool P sqp"
shows "quote_gross P' sqp' = 0" 
proof (rule restrict_pool_quote_gross_leq)
  define Pr where "Pr = refine P sqp"
  define i where "i = lower_tick Pr sqp"
  show "P' = restrict_pool i Pr" using i_def Pr_def
    by (simp add: assms(4) slice_poolD)
  show "mono (grd Pr)" using Pr_def assms refine_clmm
    by (simp add: clmm_dsc_grd_mono monoI)
  show "sqp' \<le> grd Pr i"
    using Pr_def assms(1-3) i_def refine_lower_tick by auto
qed

lemma slice_pool_quote_gross:
  assumes "clmm_dsc P"
  and "0 < sqp"
  and "sqp \<le> sqp'"
  and "P' = slice_pool P sqp"
shows "quote_gross P' sqp' = quote_gross P sqp' - quote_gross P sqp" 
proof -
  define Pr where "Pr = refine P sqp"
  define i where "i = lower_tick Pr sqp"
  have "P' = restrict_pool i Pr" using i_def Pr_def
    by (simp add: assms(4) slice_poolD)
  have "quote_gross P' sqp' = quote_gross Pr sqp' - quote_gross Pr (grd Pr i)"
  proof (rule restrict_pool_quote_gross[symmetric])
    show "clmm_dsc Pr" using Pr_def assms(1,2) refine_clmm by auto
    show "P' = restrict_pool i Pr" using \<open>P' = restrict_pool i Pr\<close> .
    show "0 < sqp'" using assms by simp
    show "i \<le> lower_tick Pr sqp'"  
      using i_def \<open>clmm_dsc Pr\<close> assms(2,3) lower_tick_mono by auto 
  qed
  also have "... = quote_gross Pr sqp' - quote_gross Pr sqp"
  proof -
    have "quote_gross Pr (grd Pr i) = quote_gross Pr sqp"
      using Pr_def assms(1,2) i_def refine_lower_tick by auto
    thus ?thesis by simp
  qed
  also have "... = quote_gross P sqp' - quote_gross P sqp"
    using Pr_def assms(1,2) refine_quote_gross by auto
  finally show ?thesis .
qed
  
lemma slice_pool_quote_gross_max_eq:
  assumes "clmm_dsc P"
  and "P' = slice_pool P sqp"
  and "nz_support (lq P) \<noteq> {}"
  and "0 < sqp"
  and "sqp < grd_max P"
  and "i = lower_tick P sqp"
  and "grd P i = sqp"
shows "quote_gross P' (grd_max P') = quote_gross P (grd_max P) - quote_gross P sqp"
proof -
  have "grd_max P = grd_max P'"
    by (simp add: assms slice_pool_grd_max')
  define sqp' where "sqp' = grd_max P"
  have "quote_gross P' sqp' = quote_gross P sqp' - quote_gross P sqp" 
    using slice_pool_quote_gross assms sqp'_def by simp
  thus ?thesis using \<open>grd_max P = grd_max P'\<close> sqp'_def by simp
qed

lemma slice_pool_quote_gross_inv:
  assumes "clmm_dsc P"
  and "0 < sqp"
  and "nz_support (lq P) \<noteq> {}"
  and "sqp < grd_max P"
  and "0 < y"
  and "P' = slice_pool P sqp"
shows "quote_gross P' -`{y}  = quote_gross P -`{y + quote_gross P sqp}" 
proof 
  have "clmm_dsc P'" using assms slice_pool_clmm_dsc by simp
  have "nz_support (lq P') \<noteq> {}" using assms slice_pool_nz_liq' by simp
  show "quote_gross P' -` {y} \<subseteq> quote_gross P -` {y + quote_gross P sqp}"
  proof
    fix sqp'
    assume asm: "sqp' \<in> quote_gross P' -` {y}"
    hence "y = quote_gross P' sqp'" by simp
    also have "... = quote_gross P sqp' - quote_gross P sqp"
      by (metis assms(1,2,5,6) calculation dual_order.irrefl nle_le 
          slice_pool_quote_gross slice_pool_quote_gross_leq)
    finally have "y = quote_gross P sqp' - quote_gross P sqp" .
    hence "quote_gross P sqp' = y + quote_gross P sqp" by simp
    thus "sqp' \<in> quote_gross P -` {y + quote_gross P sqp}" by simp
  qed
  show "quote_gross P -` {y + quote_gross P sqp} \<subseteq> quote_gross P' -` {y}"
  proof
    fix sqp'
    assume asm: "sqp' \<in> quote_gross P -` {y + quote_gross P sqp}"
    hence eq: "quote_gross P sqp' = y + quote_gross P sqp" by simp
    hence "sqp \<le> sqp'"
      by (metis assms(1) assms(5) less_add_same_cancel2 order_less_imp_le 
          quote_gross_imp_sqp_lt)
    have "y = quote_gross P sqp' - quote_gross P sqp" using eq assms by simp
    also have "... = quote_gross P' sqp'" 
    proof (rule slice_pool_quote_gross[symmetric, of P], auto simp add: assms)
      show "sqp \<le> sqp'" using \<open>sqp \<le> sqp'\<close> .
    qed
    finally have "y = quote_gross P' sqp'" .
    thus "sqp' \<in> quote_gross P' -` {y}" by simp
  qed
qed

lemma slice_pool_quote_reach:
  assumes "clmm_dsc P"
  and "nz_support (lq P) \<noteq> {}"
  and "0 < sqp"
  and "sqp < grd_max P"
  and "0 < y"
  and "P' = slice_pool P sqp"
shows "quote_reach P' y = quote_reach P (y + quote_gross P sqp)" 
proof -
  have "quote_reach P' y =  Inf (quote_gross P' -` {y})"  
    using assms clmm_quote_gross_grd_min slice_pool_clmm_dsc slice_pool_nz_liq' 
    unfolding quote_reach_def by auto
  also have "... = Inf (quote_gross P -` {y + quote_gross P sqp})" 
    using assms slice_pool_quote_gross_inv by simp
  also have "... = quote_reach P (y + quote_gross P sqp)" 
    using assms unfolding quote_reach_def 
    by (metis add_pos_nonneg clmm_quote_gross_pos order_less_irrefl)
  finally show ?thesis .
qed

lemma slice_pool_base_net_eq:
  assumes "clmm_dsc P"
  and "nz_support (lq P) \<noteq> {}"
  and "P' = slice_pool P sqp"
  and "0 < sqp"
  and "sqp < grd_max P"
  and "sqp \<le> sqp'"
shows "base_net P' sqp' = base_net P sqp'"
proof -
  define Pr where "Pr = refine P sqp"
  define i where "i = lower_tick Pr sqp"
  hence "i \<le> idx_max (lq Pr)"
    using Pr_def assms(1,2,4,5) refine_lower_tick_idx_max sqp_lt_grd_max_imp_idx 
    by presburger
  have "P' = restrict_pool i Pr" using i_def Pr_def
    by (simp add: assms(3) slice_poolD)
  hence "base_net P' sqp' = base_net Pr sqp'" 
    using restrict_pool_base_net_eq assms Pr_def \<open>i \<le> idx_max (lq Pr)\<close>
    by (metis i_def refine_clmm refine_lower_tick refine_nz_lq_ne)
  also have "... = base_net P sqp'" using Pr_def assms refine_base_net_eq 
    by simp
  finally show ?thesis .
qed

 
lemma slice_pool_base_net_slice: 
  assumes "clmm_dsc P"
  and "nz_support (lq P) \<noteq> {}"
  and "i = lower_tick P sqp"
  and "P' = slice_pool P sqp"
  and "sqp < grd_max P"
  and "grd P i = sqp"
  and "sqp' \<le> sqp"
  and "0 < sqp'"
shows "base_net P' sqp' = base_net P' sqp" 
proof -
  have "clmm_dsc P'" using assms slice_pool_clmm_dsc by simp
  have "lower_tick P sqp \<le> idx_max (lq P)"
    by (metis assms(1) assms(2) assms(5) assms(6) clmm_dsc_grid(2) 
        sqp_lt_grd_max_imp_idx)
  hence "sqp \<le> grd_min P'" using assms slice_pool_grd_min by simp
  hence "sqp' \<le> grd_min P'" using assms by simp
  have "base_net P' sqp' = base_net P' (grd_min P')" 
    using base_net_grd_min_le \<open>sqp' \<le> grd_min P'\<close> assms \<open>clmm_dsc P'\<close> 
    by blast
  also have "... = base_net P' sqp"
    using base_net_grd_min_le \<open>sqp \<le> grd_min P'\<close> assms \<open>clmm_dsc P'\<close>
    by (metis clmm_dsc_grid(2))
  finally show ?thesis .
qed

lemma slice_pool_quote_swap_gt_zero:
  assumes "clmm_dsc P"
  and "nz_support (lq P) \<noteq> {}"
  and "grd P (lower_tick P sqp2) = sqp2"
  and "P' = slice_pool P sqp2"
  and "sqp1 \<le> sqp2"
  and "0 < y"
  and "0 <sqp1"
  and "y + quote_gross P sqp2 \<le> quote_gross P (grd_max P)"
shows " quote_swap P' sqp1 y = quote_swap P sqp2 y" 
proof -
  have "clmm_dsc P'" using slice_pool_clmm_dsc assms by simp
  have "sqp2 < grd_max P" using assms quote_gross_imp_sqp_lt by simp
  hence "quote_gross P' sqp1 = 0" 
    using assms slice_pool_quote_gross_leq by (simp add: strict_mono_mono)
  hence qeq: "quote_reach P' (y + quote_gross P' sqp1) = 
      quote_reach P (y + quote_gross P sqp2)"
    using assms \<open>sqp2 < grd_max P\<close> slice_pool_quote_reach by simp
  have "sqp2 \<le> quote_reach P (y + quote_gross P sqp2)" 
    using quote_reach_gt[of P y sqp2] assms by simp
  hence a: "base_net P' (quote_reach P' (y + quote_gross P' sqp1)) = 
      base_net P (quote_reach P (y + quote_gross P sqp2))"
    using qeq \<open>sqp2 < grd_max P\<close> assms slice_pool_base_net_eq by auto
  have "base_net P' sqp1 = base_net P' sqp2" using slice_pool_base_net_slice
    by (simp add: \<open>sqp2 < grd_max P\<close> assms)
  also have "... = base_net P sqp2" 
    using slice_pool_base_net_eq \<open>sqp2 < grd_max P\<close> assms 
    by auto
  finally have "base_net P' sqp1 = base_net P sqp2" .
  thus ?thesis using a unfolding quote_swap_def by simp
qed

lemma slice_pool_quote_swap:
  assumes "clmm_dsc P"
  and "nz_support (lq P) \<noteq> {}"
  and "grd P (lower_tick P sqp2) = sqp2"
  and "P' = slice_pool P sqp2"
  and "sqp1 \<le> sqp2"
  and "sqp2 < grd_max P"
  and "0 \<le> y"
  and "0 < sqp1"
  and "y + quote_gross P sqp2 \<le> quote_gross P (grd_max P)"
shows "quote_swap P' sqp1 y = quote_swap P sqp2 y" 
proof (cases "y = 0")
  case True
  have "quote_swap P' sqp1 0 = 0"
  proof (rule quote_swap_zero)
    show "clmm_dsc P'" using assms slice_pool_clmm_dsc by simp
    show "nz_support (lq P') \<noteq> {}"
      by (metis assms(1-4) assms(6) clmm_dsc_grid(2) 
          slice_pool_nz_liq') 
    show "0 < sqp1" using assms by simp
    show "sqp1 \<le> grd_max P'" using assms slice_pool_grd_max' by simp
  qed
  also have "... = quote_swap P sqp2 0"
    using quote_swap_zero assms by simp
  finally show ?thesis using True by simp
next
  case False
  then show ?thesis 
    using assms slice_pool_quote_swap_gt_zero by simp
qed

subsection \<open>CLMM pool join\<close>

text \<open>The join operation is meant to define a pool $P$ on which swap operations can be 
viewed as a combination of swap operations on its two arguments. 
We use the convention that the pool fee is $0$ on ranges where there is no liquidity.\<close>

definition pool_fee_join where
"pool_fee_join P1 P2 i = fee_union (lq P1 i) (lq P2 i) (fee P1 i) (fee P2 i)"

lemma pool_fee_join_com:
  shows "pool_fee_join P1 P2 i = pool_fee_join P2 P1 i" 
  unfolding pool_fee_join_def fee_union_def
  by (simp add: add.commute)

definition joint_pools where
"joint_pools P P1 P2 \<longleftrightarrow>  (grd P) = (grd P1) \<and> (grd P) = (grd P2) \<and>
  (\<forall>i. lq P i = lq P1 i + lq P2 i) \<and>
  (\<forall>i. fee P i = pool_fee_join P1 P2 i)"

definition pool_join where
"pool_join P1 P2 = 
  (grd P1, (\<lambda>i. lq P1 i + lq P2 i), (\<lambda>i. pool_fee_join P1 P2 i))"

lemma joint_poolsI[intro]:
  assumes "grd P = grd P1"
  and "grd P = grd P2"
  and "\<And>i. lq P i = lq P1 i + lq P2 i"
  and "\<And>i. fee P i = pool_fee_join P1 P2 i"
shows "joint_pools P P1 P2" using assms unfolding joint_pools_def by simp

lemma pool_join_joint:
  assumes "grd P1 = grd P2"
  and "P = pool_join P1 P2"
  shows "joint_pools P P1 P2" using assms unfolding pool_join_def
  by (simp add: fee_def grd_def joint_pools_def lq_def)

lemma joint_pools_grids:
  assumes "joint_pools P P1 P2"
  shows "(grd P) = (grd P1)" "(grd P) = (grd P2)"
  using assms unfolding joint_pools_def by simp+

lemma joint_pools_lq:
  assumes "joint_pools P P1 P2"
  shows "lq P i = lq P1 i + lq P2 i" 
  using assms unfolding joint_pools_def by simp

lemma joint_pools_fee:
  assumes "joint_pools P P1 P2"
  shows "fee P i = pool_fee_join P1 P2 i"
  using assms unfolding joint_pools_def by simp

lemma joint_pools_com:
  assumes "joint_pools P P1 P2"
  shows "joint_pools P P2 P1"
proof 
  show "grd P = grd P2" using assms joint_pools_grids by simp
  show "grd P = grd P1" using assms joint_pools_grids by simp
  fix i
  show "lq P i = lq P2 i + lq P1 i" using assms joint_pools_lq by simp
  show "fee P i = pool_fee_join P2 P1 i" 
    using pool_fee_join_com joint_pools_fee assms by simp
qed

lemma joint_pools_nz_liq_sub:
  assumes "joint_pools P P1 P2"
  shows "nz_support (lq P) \<subseteq> nz_support (lq P1) \<union> (nz_support (lq P2))"
  unfolding nz_support_def
proof -
  define F1 where "F1 = {i. lq P1 i \<noteq> 0}"
  define F2 where "F2 = {i. lq P2 i \<noteq> 0}"
  define F where "F = {i. lq P i \<noteq> 0}"
  show "F \<subseteq> F1 \<union> F2" 
  proof
    fix i
    assume "i\<in> F"
    hence "lq P1 i + lq P2 i \<noteq> 0" using F_def assms joint_pools_lq by auto 
    hence "lq P1 i \<noteq> 0 \<or> lq P2 i \<noteq> 0" by simp
    thus "i \<in> F1 \<union> F2" using F1_def F2_def by auto
  qed
qed

lemma joint_pools_nz_liq_sup:
  assumes "joint_pools P P1 P2"
  and "\<And>i. 0 \<le> lq P1 i"
  and "\<And>i. 0 \<le> lq P2 i"
  shows "nz_support (lq P1) \<union> (nz_support (lq P2)) \<subseteq> nz_support (lq P)"
  unfolding nz_support_def
proof -
  define F1 where "F1 = {i. lq P1 i \<noteq> 0}"
  define F2 where "F2 = {i. lq P2 i \<noteq> 0}"
  define F where "F = {i. lq P i \<noteq> 0}"
  show "F1 \<union> F2 \<subseteq> F"
  proof
    fix j
    assume "j\<in> F1\<union> F2"
    hence "lq P1 j \<noteq> 0 \<or> lq P2 j \<noteq> 0" unfolding F1_def F2_def by auto
    hence "lq P1 j + lq P2 j \<noteq> 0" using joint_pools_lq
      by (simp add: add_nonneg_eq_0_iff assms) 
    thus "j \<in> F" using F_def joint_pools_lq assms by auto
  qed
qed

lemma joint_pools_nz_liq:
  assumes "joint_pools P P1 P2"
  and "\<And>i. 0 \<le> lq P1 i"
  and "\<And>i. 0 \<le> lq P2 i"
shows "nz_support (lq P1) \<union> (nz_support (lq P2)) = nz_support (lq P)"
  using assms joint_pools_nz_liq_sup joint_pools_nz_liq_sub by blast

lemma clmm_joint_pools_nz_liq:
  assumes "clmm_dsc P1"
  and "clmm_dsc P2"
  and "joint_pools P P1 P2"
shows "nz_support (lq P1) \<union> (nz_support (lq P2)) = nz_support (lq P)"
  using assms joint_pools_nz_liq by (simp add: clmm_dsc_liq(2))

lemma joint_pools_finite_liq:
  assumes "finite_liq P1"
  and "finite_liq P2"
  and "joint_pools P P1 P2"
shows "finite_liq P" using assms joint_pools_nz_liq_sub
  by (meson finite_UnI finite_liq_def rev_finite_subset)

lemma joint_pools_idx_min_min:
  assumes "clmm_dsc P1"
  and "clmm_dsc P2"
  and "joint_pools P P1 P2"
  and "nz_support (lq P1) \<noteq> {}"
  and "idx_min (lq P1) \<le> idx_min (lq P2)"
shows "idx_min (lq P) = idx_min (lq P1)"
proof (rule idx_min_finiteI[symmetric])
  define i where "i = idx_min (lq P1)"
  show "finite (nz_support (lq P))" 
    using assms joint_pools_finite_liq by (meson clmm_dsc_def finite_liq_def)
  have "lq P1 i \<noteq> 0" using i_def idx_min_finite_in
    by (metis (full_types) \<open>finite (nz_support (lq P))\<close> assms(1-4) 
        clmm_joint_pools_nz_liq finite_Un)
  thus "lq P i \<noteq> 0"
    by (smt (verit) assms(1-3) clmm_dsc_liq(2) joint_pools_lq) 
  fix j
  assume "j < i"
  hence "j < idx_min (lq P2)" using assms i_def by simp
  have "lq P2 j = 0" 
    using assms idx_min_finite_lt[of "lq P2" j] clmm_dsc_liq finite_liq_def
    by (simp add: \<open>j < idx_min (lq P2)\<close>)
  moreover have "lq P1 j = 0" 
    using \<open>j < i\<close> i_def idx_max_finite_gt[of "lq P2" j]
    by (simp add: assms idx_min_lt_liq)
  ultimately show "lq P j = 0"
    using assms(3) joint_pools_lq by auto
qed

lemma joint_pools_idx_min:
  assumes "clmm_dsc P1"
  and "clmm_dsc P2"
  and "joint_pools P P1 P2"
  and "nz_support (lq P1) \<noteq> {}"
  and "nz_support (lq P2) \<noteq> {}"
shows "idx_min (lq P) = min (idx_min (lq P1)) (idx_min (lq P2))" 
  using joint_pools_idx_min_min
  by (smt (z3) assms max_def nle_le joint_pools_com)

lemma joint_pools_idx_max_max:
  assumes "clmm_dsc P1"
  and "clmm_dsc P2"
  and "joint_pools P P1 P2"
  and "nz_support (lq P2) \<noteq> {}"
  and "idx_max (lq P1) \<le> idx_max (lq P2)"
shows "idx_max (lq P) = idx_max (lq P2)"
proof (rule idx_max_finiteI[symmetric])
  define i where "i = idx_max (lq P2)"
  show "finite (nz_support (lq P))" 
    using assms joint_pools_finite_liq by (meson clmm_dsc_def finite_liq_def)
  have "lq P2 i \<noteq> 0" using i_def idx_max_finite_in
    by (metis (full_types) \<open>finite (nz_support (lq P))\<close> assms(1-4) 
        clmm_joint_pools_nz_liq finite_Un)
  thus "lq P i \<noteq> 0"
    by (smt (verit) assms(1-3) clmm_dsc_liq(2) joint_pools_lq) 
  fix j
  assume "i < j"
  hence "idx_max (lq P1) < j" using assms i_def by simp
  have "lq P1 j = 0" 
    using assms idx_max_finite_gt[of "lq P1" j] clmm_dsc_liq finite_liq_def
    by (simp add: \<open>idx_max (lq P1) < j\<close>)
  moreover have "lq P2 j = 0" 
    using \<open>i < j\<close> i_def idx_max_finite_gt[of "lq P2" j]
    by (simp add: assms(2) idx_max_gt_liq)
  ultimately show "lq P j = 0"
    using assms(3) joint_pools_lq by auto
qed

lemma joint_pools_idx_max:
  assumes "clmm_dsc P1"
  and "clmm_dsc P2"
  and "joint_pools P P1 P2"
  and "nz_support (lq P1) \<noteq> {}"
  and "nz_support (lq P2) \<noteq> {}"
shows "idx_max (lq P) = max (idx_max (lq P1)) (idx_max (lq P2))" 
  using joint_pools_idx_max_max
  by (smt (z3) assms max_def nle_le joint_pools_com)

lemma joint_pools_clmm_dsc:
  assumes "clmm_dsc P1"
  and "clmm_dsc P2"
  and "joint_pools P P1 P2"
shows "clmm_dsc P"
proof
  show "span_grid P" using assms clmm_dsc_grid[of P1] joint_pools_grids(1)
    by (simp add: span_grid_def)
  show "finite_liq P" using assms joint_pools_finite_liq clmm_dsc_liq by meson
  show "\<forall>i. 0 \<le> lq P i" using assms joint_pools_lq clmm_dsc_liq(2) by simp
  show "\<forall>i. 0 \<le> fee P i" using assms joint_pools_fee fee_union_pos
    by (simp add: clmm_dsc_def pool_fee_join_def)
  show "\<forall>i. fee P i < 1" using assms joint_pools_fee fee_union_lt_1
    by (simp add: clmm_dsc_def pool_fee_join_def)
qed

lemma join_gross_fct:
  assumes "clmm_dsc P1"
  and "clmm_dsc P2"
  and "joint_pools P P1 P2"
  shows "gross_fct (lq P) (fee P) i = gross_fct (lq P1) (fee P1) i + 
    gross_fct (lq P2) (fee P2) i"
proof (cases "lq P i = 0")
  case True
  hence "lq P1 i + lq P2 i = 0"
    using assms(3) joint_pools_lq by auto
  hence "lq P1 i = 0" "lq P2 i = 0"
    by (simp add: clmm_dsc_liq(2) add_nonneg_eq_0_iff assms(1) assms(2))+
  then show ?thesis using True gross_fct_zero_if by auto
next
  case False
  define L where "L = lq P"
  define F where "F = fee P"
  define l1 where "l1 = lq P1 i"
  define f1 where "f1 = fee P1 i"
  define l2 where "l2 = lq P2 i"
  define f2 where "f2 = fee P2 i"
  define df where "df = l1*(1-f2) + l2*(1-f1)"
  have "0 \<le> l1" using assms l1_def clmm_dsc_liq by simp
  have "0 < 1 - f2" using assms f2_def clmm_dsc_fees by simp
  have "0 < 1 - f1" using assms f1_def clmm_dsc_fees by simp
  have "0 \<le> l2" using assms l2_def clmm_dsc_liq by simp
  have "0 < lq P i" 
    using False \<open>0 \<le> l1\<close> \<open>0 \<le> l2\<close> assms(3) l1_def l2_def joint_pools_lq by auto
  hence "0 < l1 \<or> 0 < l2" using assms joint_pools_lq l1_def l2_def by auto
  hence "0 < df" using df_def l1_def f2_def l2_def f1_def
    by (smt (verit, best) \<open>0 < 1 - f1\<close> \<open>0 < 1 - f2\<close> \<open>0 \<le> l1\<close> \<open>0 \<le> l2\<close> 
        mult_nonneg_nonneg mult_pos_pos)
  have "gross_fct (lq P) (fee P) i = 
      (l1 + l2)/(one_cpl (pool_fee_join P1 P2) i)" 
    using assms joint_pools_lq joint_pools_fee
    unfolding gross_fct_def l1_def l2_def
    by (simp add: one_cpl_def)
  also have "... = (l1 + l2)/(1 - ((l1*f1*(1-f2) + l2*f2*(1-f1))/
      df))" 
    using one_cpl_def pool_fee_join_def fee_union_def l1_def l2_def f1_def f2_def df_def
    by simp
  also have "... = (l1 + l2)/((df - (l1*f1*(1-f2) + l2*f2*(1-f1))) / df)"
  proof -
    have "1 - ((l1*f1*(1-f2) + l2*f2*(1-f1)))/ df = 
        df/df - ((l1*f1*(1-f2) + l2*f2*(1-f1)))/ df" 
      using \<open>0 < df\<close> by simp
    also have "... = (df - (l1*f1*(1-f2) + l2*f2*(1-f1))) / df" 
      by (rule diff_divide_distrib[symmetric])
    finally have "1 - ((l1*f1*(1-f2) + l2*f2*(1-f1)))/ df = 
        (df - (l1*f1*(1-f2) + l2*f2*(1-f1))) / df" .
    thus ?thesis by simp
  qed
  also have "... = ((l1 + l2) * df)/ (df - (l1*f1*(1-f2) + l2*f2*(1-f1)))" 
    by (rule divide_divide_eq_right)
  also have "... = ((l1 + l2) * df)/ ((l1 + l2) * ((1 - f1) * (1 - f2)))" 
  proof -
    have "df - (l1*f1*(1-f2) + l2*f2*(1-f1)) = 
        l1*(1-f2) + l2*(1-f1) - l1*f1*(1-f2) - l2*f2*(1-f1)" 
      unfolding df_def by simp
    also have "... = l1*(1-f2) - l1*f1*(1-f2) + (l2*(1-f1) - l2*f2*(1-f1))" 
      by simp
    also have "... = (l1 - l1 * f1) * (1 - f2) + (l2*(1-f1) - l2*f2*(1-f1))"
      by (simp add: left_diff_distrib')
    also have "... = (l1 - l1 * f1) * (1 - f2) + ((l2 - l2 * f2) * (1 - f1))" 
      by (simp add: left_diff_distrib')
    also have "... = l1 * ((1 - f1) * (1 - f2)) + ((l2 - l2 * f2) * (1 - f1))"
      by (simp add: vector_space_over_itself.scale_right_diff_distrib)
    also have "... = l1 * ((1 - f1) * (1 - f2)) + (l2 * ((1 - f2) * (1 - f1)))"
      by (simp add: vector_space_over_itself.scale_right_diff_distrib)
    also have "... = l1 * ((1 - f1) * (1 - f2)) + (l2 * ((1 - f1) * (1 - f2)))" 
      by simp
    also have "... = (l1 + l2) * ((1 - f1) * (1 - f2))"
      by (simp add: distrib_right) 
    finally have "df - (l1*f1*(1-f2) + l2*f2*(1-f1)) = 
      (l1 + l2) * ((1 - f1) * (1 - f2))" .
    thus ?thesis by simp
  qed
  also have "... = df / ((1 - f1) * (1 - f2))"
    using \<open>0 < l1 \<or> 0 < l2\<close> \<open>0 \<le> l1\<close> \<open>0 \<le> l2\<close> by fastforce
  also have "... = l1*(1-f2)/((1 - f1) * (1 - f2))  + 
      l2*(1-f1)/ ((1 - f1) * (1 - f2))" 
    using df_def by (simp add: add_divide_distrib)
  also have "... = l1/(1-f1) + l2*(1-f1)/ ((1 - f1) * (1 - f2))"
    using \<open>0 < 1 - f2\<close> by auto
  also have "... = l1/(1-f1) + l2/(1-f2)" 
    using \<open>0 < 1 - f1\<close> by auto
  also have "... = gross_fct (lq P1) (fee P1) i + 
    gross_fct (lq P2) (fee P2) i"
    by (simp add: f1_def f2_def gross_fct_def l1_def l2_def one_cpl_def)
  finally show ?thesis .
qed

lemma quote_gross_join:
  assumes "clmm_dsc P1"
  and "clmm_dsc P2"
  and "joint_pools P P1 P2"
shows "quote_gross P x = quote_gross P1 x + quote_gross P2 x" 
proof -
  have "quote_gross P x = 
      gen_quote (grd P) (gross_fct (lq P1) (fee P1)) x + 
      gen_quote (grd P) (gross_fct (lq P2) (fee P2)) x" 
    unfolding quote_gross_def
  proof (rule finite_nz_support.gen_quote_plus)
    show "finite_nz_support (gross_fct (lq P) (fee P))" 
      using finite_liq_pool.finite_liq_gross_fct joint_pools_finite_liq assms
      by (metis clmm_dsc_liq(1) finite_liq_pool.intro finite_nz_support_def 
          nz_support_def)
    show "\<forall>i. 0 \<le> gross_fct (lq P1) (fee P1) i"
      using clmm_dsc_fees clmm_dsc_liq(2) assms(1) gross_fct_sgn by blast
    show "\<forall>i. 0 \<le> gross_fct (lq P2) (fee P2) i"
      using clmm_dsc_fees clmm_dsc_liq(2) assms(2) gross_fct_sgn by blast
    show "\<forall>i. gross_fct (lq P) (fee P) i = gross_fct (lq P1) (fee P1) i + 
        gross_fct (lq P2) (fee P2) i" 
      using join_gross_fct assms by auto
  qed
  also have "... = quote_gross P1 x + quote_gross P2 x" 
    using assms joint_pools_grids unfolding quote_gross_def by simp
  finally show ?thesis .
qed

lemma quote_net_join:
  assumes "clmm_dsc P1"
  and "clmm_dsc P2"
  and "joint_pools P P1 P2"
shows "quote_net P x = quote_net P1 x + quote_net P2 x" 
proof -
  have "quote_net P x = gen_quote (grd P) (lq P1) x + 
      gen_quote (grd P) (lq P2) x" 
    unfolding quote_net_def
  proof (rule finite_nz_support.gen_quote_plus)
    show "finite_nz_support (lq P)"
      by (meson clmm_dsc_def assms finite_liq_def finite_nz_support_def 
          joint_pools_finite_liq) 
    show "\<forall>i. 0 \<le> lq P1 i" using clmm_dsc_liq(2) assms(1) by auto
    show "\<forall>i. 0 \<le> lq P2 i" by (simp add: clmm_dsc_liq(2) assms(2))
    show "\<forall>i. lq P i = lq P1 i + lq P2 i" by (simp add: assms(3) joint_pools_lq)
  qed
  also have "... = quote_net P1 x + quote_net P2 x" 
    using assms joint_pools_grids unfolding quote_net_def by simp
  finally show ?thesis .
qed

lemma base_gross_join:
  assumes "clmm_dsc P1"
  and "clmm_dsc P2"
  and "joint_pools P P1 P2"
shows "base_gross P x = base_gross P1 x + base_gross P2 x" 
proof -
  have "base_gross P x = 
      gen_base (grd P) (gross_fct (lq P1) (fee P1)) x + 
      gen_base (grd P) (gross_fct (lq P2) (fee P2)) x" 
    unfolding base_gross_def
  proof (rule finite_nz_support.gen_base_gross)
    show "finite_nz_support (gross_fct (lq P) (fee P))" 
      using finite_liq_pool.finite_liq_gross_fct joint_pools_finite_liq assms
      by (metis clmm_dsc_liq(1) finite_liq_pool.intro finite_nz_support_def 
          nz_support_def)
    show "\<forall>i. 0 \<le> gross_fct (lq P1) (fee P1) i"
      using clmm_dsc_fees clmm_dsc_liq(2) assms(1) gross_fct_sgn by blast
    show "\<forall>i. 0 \<le> gross_fct (lq P2) (fee P2) i"
      using clmm_dsc_fees clmm_dsc_liq(2) assms(2) gross_fct_sgn by blast
    show "\<forall>i. gross_fct (lq P) (fee P) i = gross_fct (lq P1) (fee P1) i + 
        gross_fct (lq P2) (fee P2) i" 
      using join_gross_fct assms by auto
  qed
  also have "... = base_gross P1 x + base_gross P2 x" 
    using assms joint_pools_grids unfolding base_gross_def by simp
  finally show ?thesis .
qed

lemma base_net_join:
  assumes "clmm_dsc P1"
  and "clmm_dsc P2"
  and "joint_pools P P1 P2"
shows "base_net P x = base_net P1 x + base_net P2 x" 
proof -
  have "base_net P x = gen_base (grd P) (lq P1) x + 
      gen_base (grd P) (lq P2) x" 
    unfolding base_net_def
  proof (rule finite_nz_support.gen_base_gross)
    show "finite_nz_support (lq P)"
      by (meson clmm_dsc_def assms finite_liq_def finite_nz_support_def 
          joint_pools_finite_liq) 
    show "\<forall>i. 0 \<le> lq P1 i" using clmm_dsc_liq(2) assms(1) by auto
    show "\<forall>i. 0 \<le> lq P2 i" by (simp add: clmm_dsc_liq(2) assms(2))
    show "\<forall>i. lq P i = lq P1 i + lq P2 i" by (simp add: assms(3) joint_pools_lq)
  qed
  also have "... = base_net P1 x + base_net P2 x" 
    using assms joint_pools_grids unfolding base_net_def by simp
  finally show ?thesis .
qed

lemma mkt_depth_join:
  assumes "clmm_dsc P1"
  and "clmm_dsc P2"
  and "joint_pools P P1 P2"
shows "mkt_depth P x x' = mkt_depth P1 x x' + mkt_depth P2 x x'" 
  using assms unfolding mkt_depth_def
  by (simp add: quote_net_join base_net_join)

lemma joint_quote_gross_decomp:
  assumes "clmm_dsc P1"
  and "clmm_dsc P2"
  and "joint_pools P P1 P2"
  and "nz_support (lq P) \<noteq> {}"
  and "grd_min P \<le> x"
  and "0 \<le> y"
  and "y + quote_gross P x \<le> quote_gross P (grd_max P)"
  and "x' = quote_reach P (y + quote_gross P x)"
  and "y1 = quote_gross P1 x' - quote_gross P1 x"
  and "y2 = quote_gross P2 x' - quote_gross P2 x"
shows "y = y1 + y2"
proof -
  interpret finite_liq_pool P 
    using assms joint_pools_finite_liq clmm_dsc_liq finite_liq_pool.intro 
    by blast
  have "clmm_dsc P" using assms joint_pools_clmm_dsc[of P1] by simp
  have "y1 + y2 = quote_gross P1 x' + quote_gross P2 x' - 
      (quote_gross P1 x + quote_gross P2 x)" 
    using assms by simp
  also have "... = quote_gross P x' - quote_gross P x" 
    using quote_gross_join assms by auto
  also have "... = y"
  proof -
    have "quote_gross P (quote_reach P (y + quote_gross P x)) = 
        y + quote_gross P x" 
    proof (rule quote_gross_reach_eq)
      show "\<forall>i. fee P i < 1" using \<open>clmm_dsc P\<close>
        by (simp add: clmm_dsc_fees)
      show "mono (grd P)"
        by (simp add: \<open>clmm_dsc P\<close> clmm_dsc_grd_mono monoI)
      show "0 \<le> y + quote_gross P x"
        by (simp add: \<open>clmm_dsc P\<close> assms(6) clmm_quote_gross_pos)
      show "y + quote_gross P x \<le> quote_gross P (grd_max P)" 
        using assms by simp
      show "\<forall>i. 0 \<le> lq P i"
        by (simp add: \<open>clmm_dsc P\<close> clmm_dsc_liq(2))
    qed
    thus ?thesis using assms by simp
  qed
  finally show ?thesis by simp
qed

lemma joint_quote_gross_decomp':
  assumes "clmm_dsc P1"
  and "clmm_dsc P2"
  and "joint_pools P P1 P2"
  and "nz_support (lq P) \<noteq> {}"
  and "0 \<le> y"
  and "y \<le> quote_gross P (grd_max P)"
  and "x' = quote_reach P y"
  and "y1 = quote_gross P1 x'"
  and "y2 = quote_gross P2 x'"
shows "y = y1 + y2"
proof -
  interpret finite_liq_pool P 
    using assms joint_pools_finite_liq clmm_dsc_liq finite_liq_pool.intro 
    by blast
  have "clmm_dsc P" using assms joint_pools_clmm_dsc[of P1] by simp
  have "y1 + y2 = quote_gross P1 x' + quote_gross P2 x'" 
    using assms by simp
  also have "... = quote_gross P x'" 
    using quote_gross_join assms by auto
  also have "... = y"
  proof -
    have "quote_gross P (quote_reach P y) = y" 
    proof (rule quote_gross_reach_eq)
      show "\<forall>i. fee P i < 1" using \<open>clmm_dsc P\<close>
        by (simp add: clmm_dsc_fees)
      show "mono (grd P)"
        by (simp add: \<open>clmm_dsc P\<close> clmm_dsc_grd_mono monoI)
      show "0 \<le> y " using assms by simp
      show "y \<le> quote_gross P (grd_max P)" using assms by simp
      show "\<forall>i. 0 \<le> lq P i" by (simp add: \<open>clmm_dsc P\<close> clmm_dsc_liq(2)) 
    qed
    thus ?thesis using assms by simp
  qed
  finally show ?thesis by simp
qed

lemma joint_base_net_decomp':
  assumes "clmm_dsc P1"
  and "clmm_dsc P2"
  and "joint_pools P P1 P2"
  and "nz_support (lq P) \<noteq> {}"
  and "0 \<le> y"
  and "y \<le> quote_gross P (grd_max P)"
  and "x' = quote_reach P y"
  and "y1 = base_net P1 x'"
  and "y2 = base_net P2 x'"
shows "base_net P x' = y1 + y2"
proof -
  interpret finite_liq_pool P 
    using assms joint_pools_finite_liq clmm_dsc_liq finite_liq_pool.intro 
    by blast
  have "clmm_dsc P" using assms joint_pools_clmm_dsc[of P1] by simp
  have "y1 + y2 = base_net P1 x' + base_net P2 x'" 
    using assms by simp
  also have "... = base_net P x'" 
    using base_net_join assms by auto
  finally show ?thesis by simp
qed

lemma joint_base_gross_decomp:
  assumes "clmm_dsc P1"
  and "clmm_dsc P2"
  and "joint_pools P P1 P2"
  and "nz_support (lq P) \<noteq> {}"
  and "x \<le> grd_max P"
  and "0 \<le> y"
  and "y + base_gross P x \<le> base_gross P (grd_min P)"
  and "x' = base_reach P (y + base_gross P x)"
  and "y1 = base_gross P1 x' - base_gross P1 x"
  and "y2 = base_gross P2 x' - base_gross P2 x"
shows "y = y1 + y2"
proof -
  interpret finite_liq_pool P 
    using assms joint_pools_finite_liq clmm_dsc_liq finite_liq_pool.intro 
    by blast
  have "clmm_dsc P" using assms joint_pools_clmm_dsc[of P1] by simp
  have "y1 + y2 = base_gross P1 x' + base_gross P2 x' - 
      (base_gross P1 x + base_gross P2 x)" 
    using assms by simp
  also have "... = base_gross P x' - base_gross P x" 
    using base_gross_join assms by auto
  also have "... = y"
  proof -
    have "base_gross P (base_reach P (y + base_gross P x)) = 
        y + base_gross P x" 
    proof (rule base_gross_dwn)
      show "\<forall>i. fee P i < 1" using \<open>clmm_dsc P\<close> by (simp add: clmm_dsc_fees)
      show "mono (grd P)" by (simp add: \<open>clmm_dsc P\<close> clmm_dsc_grd_mono monoI) 
      show "grd_min P \<le> grd_max P" 
      proof (rule grd_min_max)
        show "nz_support (lq P) \<noteq> {}" using assms by simp
        show "mono (grd P)" using \<open>clmm_dsc P\<close> span_gridD clmm_dsc_grid
          by (simp add: strict_mono_on_imp_mono_on)
      qed
      have "base_gross P (grd_max P) \<le> base_gross P x" 
        using assms clmm_base_gross_antimono \<open>clmm_dsc P\<close> antimonoD by blast
      show "0 \<le> y + base_gross P x"
        using \<open>base_gross P (grd_max P) \<le> base_gross P x\<close> \<open>mono (grd P)\<close> assms(6) 
          base_gross_grd_max fin_nz_sup 
        by simp
      show "y + base_gross P x \<le> base_gross P (grd_min P)" 
        using assms by simp
      show "\<forall>i. grd P i \<le> grd P (i + 1)" 
        using \<open>clmm_dsc P\<close> span_gridD clmm_dsc_grid
        by (simp add: strict_mono_leD)
      show "\<forall>i. 0 < grd P i" 
        using \<open>clmm_dsc P\<close> span_gridD clmm_dsc_grid by presburger
      show "\<forall>i. 0 \<le> lq P i"
        by (simp add: \<open>clmm_dsc P\<close> clmm_dsc_liq(2))
    qed
    thus ?thesis using assms by simp
  qed
  finally show ?thesis by simp
qed

definition join_pools where
"join_pools P1 P2 =
  (grd P1, 
   (\<lambda>i. lq P1 i + lq P2 i),
   (\<lambda>i. pool_fee_join P1 P2 i))"

lemma join_pools_grd[simp]:
  assumes "P = join_pools P1 P2"
  shows "grd P = grd P1" using assms unfolding grd_def join_pools_def by simp

lemma join_pools_lq[simp]:
  assumes "P = join_pools P1 P2"
  shows "lq P i =  lq P1 i + lq P2 i" 
  using assms unfolding lq_def join_pools_def by simp

lemma join_pools_fee[simp]:
  assumes "P = join_pools P1 P2"
  shows "fee P i =  pool_fee_join P1 P2 i" 
  using assms unfolding fee_def join_pools_def by simp

lemma join_joint_pools:
  assumes "grd P1 = grd P2"
  shows "joint_pools (join_pools P1 P2) P1 P2"
proof
  show "grd (join_pools P1 P2) = grd P1" by simp
  show "grd (join_pools P1 P2) = grd P2" using assms by simp
  fix i
  show "lq (join_pools P1 P2) i = lq P1 i + lq P2 i" by simp
  show "fee (join_pools P1 P2) i = pool_fee_join P1 P2 i" by simp
qed

subsection \<open>CLMM pool combination\<close>

definition pool_comb where
"pool_comb P1 P2 sqp = (let P' = refine P1 sqp in
  pool_join P' (slice_pool P2 sqp))"

lemma pool_comb_joint:
  assumes "grd P1 = grd P2"
  shows "joint_pools (pool_comb P1 P2 sqp) (refine P1 sqp) 
    (slice_pool P2 sqp)" unfolding pool_comb_def Let_def
proof (rule pool_join_joint)
  show "grd (refine P1 sqp) = grd (slice_pool P2 sqp)" 
    using refine_grd_cong[of "refine P1 sqp"] assms
    by (simp add: slice_poolD) 
qed simp+

lemma pool_comb_refined_joint_nz_liq:
  assumes "grd P1 = grd P2"
  and "clmm_dsc P1"
  and "clmm_dsc P2"
  and "P = pool_comb P1 P2 sqp"
  and "grd P1 (lower_tick P1 sqp) = sqp"
shows "nz_support (lq P) = nz_support (lq P1) \<union> 
    (nz_support (lq (slice_pool P2 sqp)))"
  by (metis assms(1-5) clmm_dsc_grid(2) clmm_joint_pools_nz_liq pool_comb_joint 
      refine_eq slice_pool_clmm_dsc)

lemma pool_comb_joint_refined:
  assumes "grd P1 = grd P2"
  and "grd P1 (lower_tick P1 sqp) = sqp"
  shows "joint_pools (pool_comb P1 P2 sqp) P1 
    (slice_pool P2 sqp)" 
proof -
  have eq: "grd P2 (lower_tick P2 sqp) = sqp"
    by (metis assms(1) assms(2) grd_lower_tick_cong)
  have "refine P1 sqp = P1" using assms refine_eq by simp
  moreover have "refine P2 sqp = P2" using assms eq refine_eq by simp
  ultimately show ?thesis 
    using pool_join_joint assms unfolding pool_comb_def Let_def
    by (metis pool_comb_def pool_comb_joint)
qed

lemma pool_comb_clmm_dsc:
  assumes "clmm_dsc P1"
  and "clmm_dsc P2"
  and "grd P1 = grd P2"
  and "0 < sqp"
  and "P3 = pool_comb P1 P2 sqp"
shows "clmm_dsc P3" unfolding pool_comb_def Let_def
proof (rule joint_pools_clmm_dsc)
  define P where "P = refine P1 sqp"
  define P' where "P' = slice_pool (refine P2 sqp) sqp"
  show "clmm_dsc P" using refine_clmm assms unfolding P_def by simp
  show "clmm_dsc P'"
  proof (rule slice_pool_clmm_dsc)
    show "clmm_dsc (refine P2 sqp)" using refine_clmm assms by simp
    show "0 < sqp" using assms by simp
  qed (simp add: P'_def)
  show "joint_pools P3 P P'"
    using pool_join_joint assms P'_def P_def pool_comb_joint
    by (metis refine_eq refine_lower_tick slice_poolD)
qed 

lemma pool_comb_grd_min:
  assumes "clmm_dsc P1"
  and "clmm_dsc P2"
  and "grd P1 = grd P2"
  and "nz_support (lq P1) \<noteq> {}"
  and "nz_support (lq P2) \<noteq> {}"
  and "0 < sqp"
  and "sqp < grd_max P2"
  and "P = pool_comb P1 P2 sqp"
shows "grd_min P = min (grd_min P1) (grd_min (slice_pool P2 sqp))"
proof -
  define i where "i = idx_min (lq P)"
  define i1 where "i1 = idx_min (lq (refine P1 sqp))"
  define i2 where "i2 = idx_min (lq (slice_pool P2 sqp))"
  have "clmm_dsc P" using assms pool_comb_clmm_dsc[of P1] by simp
  have "i = min i1 i2" unfolding i_def i1_def i2_def
  proof (rule joint_pools_idx_min)
    show "clmm_dsc (refine P1 sqp)"
      by (meson assms(1) assms(6) refine_clmm)
    show "clmm_dsc (slice_pool P2 sqp)"
      by (meson assms(2) assms(6) refine_clmm slice_pool_clmm_dsc)
    show "nz_support (lq (refine P1 sqp)) \<noteq> {}"
      using assms(1) assms(4) refine_nz_lq_ne by auto
    show "nz_support (lq (slice_pool P2 sqp)) \<noteq> {}"
      using assms slice_pool_nz_liq' clmm_dsc_liq(1) finite_liq_pool.intro 
        refine_grd_max refine_clmm refine_nz_lq_ne 
      by presburger
    show "joint_pools P (refine P1 sqp) (slice_pool P2 sqp)"
      by (metis assms(3,8) pool_comb_joint)
  qed
  have "grd_min P = grd P i" 
    using grd_min_def idx_min_img_def i_def by simp
  also have "... = min (grd P i1) (grd P i2)" 
    using \<open>i = min i1 i2\<close>
    by (metis \<open>clmm_dsc P\<close> clmm_dsc_grd_smono linorder_not_less min.absorb4 
        min.order_iff min.strict_order_iff)
  also have "... = min (grd (refine P1 sqp) i1) 
      (grd (slice_pool P2 sqp) i2)" 
  proof -
    have "grd (refine P1 sqp) = grd P" using assms
      by (metis pool_comb_joint joint_pools_grids(1)) 
    moreover have "grd (slice_pool P2 sqp) = grd P"
      by (metis assms(3) assms(8) pool_comb_joint joint_pools_def)
    ultimately show ?thesis by simp
  qed
  also have "... = min (grd_min (refine P1 sqp)) 
      (grd_min (slice_pool P2 sqp))" 
    using i1_def i2_def unfolding grd_min_def idx_min_img_def by simp 
  also have "... = min (grd_min P1) (grd_min ( slice_pool P2 sqp))" 
    using refine_grd_min assms by simp
  finally show ?thesis .
qed

lemma pool_comb_le_grd_min:
  assumes "clmm_dsc P1"
  and "clmm_dsc P2"
  and "grd P1 = grd P2"
  and "nz_support (lq P1) \<noteq> {}"
  and "nz_support (lq P2) \<noteq> {}"
  and "0 < sqp"
  and "sqp < grd_max P2"
  and "grd_min P1 \<le> sqp"
  and "P = pool_comb P1 P2 sqp"
shows "grd_min P = grd_min P1"
proof -
  have "sqp \<le> grd_min (slice_pool P2 sqp)" 
    by (rule slice_pool_grd_min, auto simp add: assms)
  thus ?thesis using assms pool_comb_grd_min by simp
qed

lemma pool_comb_grd_max:
  assumes "clmm_dsc P1"
  and "clmm_dsc P2"
  and "grd P1 = grd P2"
  and "nz_support (lq P1) \<noteq> {}"
  and "nz_support (lq P2) \<noteq> {}"
  and "0 < sqp"
  and "sqp < grd_max P2"
  and "P = pool_comb P1 P2 sqp"
shows "grd_max P = max (grd_max P1) (grd_max P2)"
proof -
  define i where "i = idx_max (lq P)"
  define i1 where "i1 = idx_max (lq (refine P1 sqp))"
  define i2 where "i2 = idx_max (lq (slice_pool P2 sqp))"
  have "clmm_dsc P" using assms pool_comb_clmm_dsc[of P1] by simp
  have "i = max i1 i2" unfolding i_def i1_def i2_def
  proof (rule joint_pools_idx_max)
    show "clmm_dsc (refine P1 sqp)"
      by (meson assms(1) assms(6) refine_clmm)
    show "clmm_dsc (slice_pool P2 sqp)"
      by (meson assms(2) assms(6) refine_clmm slice_pool_clmm_dsc)
    show "nz_support (lq (refine P1 sqp)) \<noteq> {}"
      using assms(1) assms(4) refine_nz_lq_ne by auto
    show "nz_support (lq (slice_pool P2 sqp)) \<noteq> {}"
      using assms slice_pool_nz_liq' clmm_dsc_liq(1) finite_liq_pool.intro 
        refine_grd_max refine_clmm refine_nz_lq_ne 
      by presburger
    show "joint_pools P (refine P1 sqp) (slice_pool P2 sqp)"
      by (simp add: assms(3) assms(8) pool_comb_joint)
  qed
  hence "i+1 = max (i1+1) (i2+1)" by simp
  have "grd_max P = grd P (i+1)" 
    using grd_max_def idx_max_img_def i_def by simp
  also have "... = max (grd P (i1+1)) (grd P (i2+1))" 
    using \<open>i+1 = max (i1+1) (i2+1)\<close>
    by (metis \<open>clmm_dsc P\<close> clmm_dsc_grd_mono max.orderE max_absorb2 nle_le)
  also have "... = max (grd (refine P1 sqp) (i1+1)) 
      (grd (slice_pool P2 sqp) (i2+1))" 
  proof -
    have "grd (refine P1 sqp) = grd P" using assms
      by (metis pool_comb_joint joint_pools_grids(1)) 
    moreover have "grd (slice_pool P2 sqp) = grd P"
      by (metis assms(3) assms(8) pool_comb_joint joint_pools_def)
    ultimately show ?thesis by simp
  qed
  also have "... = max (grd_max (refine P1 sqp)) 
      (grd_max ( slice_pool P2 sqp))" 
    using i1_def i2_def unfolding grd_max_def idx_max_img_def by simp
  also have "... = max (grd_max P1) (grd_max P2)" 
    using refine_grd_max slice_pool_grd_max' assms(1) assms(2) assms(4-7) 
      refine_clmm refine_nz_lq_ne 
    by presburger
  finally show ?thesis .
qed

lemma pool_comb_grd_max_slice:
  assumes "clmm_dsc P1"
  and "clmm_dsc P2"
  and "grd P1 = grd P2"
  and "nz_support (lq P1) \<noteq> {}"
  and "nz_support (lq P2) \<noteq> {}"
  and "0 < sqp"
  and "sqp < grd_max P2"
  and "P = pool_comb P1 P2 sqp"
shows "sqp < grd_max P"
proof (cases "grd_max P1 \<le> grd_max P2")
  case True
  hence "grd_max P = grd_max P2" using assms pool_comb_grd_max
    by (metis max.absorb1 max.commute) 
  then show ?thesis using assms by simp
next
  case False
  hence "grd_max P = grd_max P1" using assms pool_comb_grd_max
    by (metis linorder_not_less max.absorb3)
  then show ?thesis using assms False by simp
qed

lemma pool_comb_quote_decomp:
  assumes "clmm_dsc P1"
  and "clmm_dsc P2"
  and "grd P1 = grd P2"
  and "grd P1 (lower_tick P1 sqp) = sqp"
  and "0 < sqp"
  and "sqp' \<le> grd_max P"
  and "P = pool_comb P1 P2 sqp"
  and "nz_support (lq P) \<noteq> {}"
shows "quote_gross P sqp' = quote_gross P1 sqp' + quote_gross (slice_pool P2 sqp) sqp'"
proof -
  define P'' where "P'' = slice_pool P2 sqp"
  have "clmm_dsc P" using pool_comb_clmm_dsc assms by simp
  interpret finite_liq_pool
    by (simp add: \<open>clmm_dsc P\<close> clmm_dsc_liq(1) finite_liq_pool.intro)
  define sqp'' where "sqp'' = quote_reach P (quote_gross P sqp')"
  have "quote_gross P sqp' = quote_gross P sqp''" unfolding sqp''_def
  proof (rule clmm_quote_gross_reach_eq[symmetric])
    show "clmm_dsc P" using \<open>clmm_dsc P\<close> .
    show "nz_support (lq P) \<noteq> {}" using assms by simp
    show "0 \<le> quote_gross P sqp'" 
      using clmm_quote_gross_pos \<open>clmm_dsc P\<close> by simp
    show "quote_gross P sqp' \<le> quote_gross P (grd_max P)" 
      using \<open>clmm_dsc P\<close> clmm_quote_gross_mono assms by (metis monoD)
  qed
  also have "... = quote_gross P1 sqp'' + quote_gross P'' sqp''" 
  proof (rule joint_quote_gross_decomp')
    show joint: "joint_pools P P1 P''" 
      using assms pool_comb_joint_refined unfolding P''_def by simp
    show "clmm_dsc P1" using assms by simp
    show "clmm_dsc P''" 
      using refine_clmm slice_pool_clmm_dsc assms 
      unfolding P''_def by auto
    show "nz_support (lq P) \<noteq> {}" using assms by simp
    show "0 \<le> quote_gross P sqp''" 
      using clmm_quote_gross_pos \<open>clmm_dsc P\<close> by simp
    show "sqp'' = quote_reach P (quote_gross P sqp'')" 
      using assms sqp''_def calculation by presburger
    show "quote_gross P sqp'' \<le> quote_gross P (grd_max P)" 
      using assms clmm_quote_gross_mono \<open>clmm_dsc P\<close> monoD calculation 
      by metis
  qed simp+
  also have "... = quote_gross P1 sqp' + quote_gross P'' sqp'"
    by (metis P''_def assms(1-5,7) calculation pool_comb_joint_refined 
        quote_gross_join slice_pool_clmm_dsc)
  finally show "quote_gross P sqp' = quote_gross P1 sqp' + quote_gross P'' sqp'" .
qed

lemma pool_comb_quote_le_slice:
  assumes "clmm_dsc P1"
  and "clmm_dsc P2"
  and "grd P1 = grd P2"
  and "grd P1 (lower_tick P1 sqp) = sqp"
  and "0 < sqp"
  and "sqp' \<le> sqp"
  and "sqp \<le> grd_max P"
  and "P = pool_comb P1 P2 sqp"
  and "nz_support (lq P) \<noteq> {}"
shows "quote_gross P sqp' = quote_gross P1 sqp'"
proof -
  have "quote_gross P sqp' = quote_gross P1 sqp' + 
      quote_gross (slice_pool P2 sqp) sqp'"
    using assms pool_comb_quote_decomp by simp
  moreover have "quote_gross (slice_pool P2 sqp) sqp' = 0"
    by (metis add_0 assms(2,5,6) clmm_quote_gross_pos quote_gross_imp_sqp_lt 
        eq_diff_eq' less_eq_real_def order_antisym_conv slice_pool_clmm_dsc 
        slice_pool_quote_gross)
  ultimately show ?thesis by simp
qed

lemma pool_comb_quote_diff_decomp:
  assumes "clmm_dsc P1"
  and "clmm_dsc P2"
  and "grd P1 = grd P2"
  and "grd P1 (lower_tick P1 sqp) = sqp"
  and "0 < sqp"
  and "0 < sqp'"
  and "0 < sqp1"
  and "sqp' \<le> grd_max P"
  and "sqp1 \<le> grd_max P"
  and "P = pool_comb P1 P2 sqp"
  and "nz_support (lq P) \<noteq> {}"
shows "quote_gross P sqp' - quote_gross P sqp1 = 
  quote_gross P1 sqp'- quote_gross P1 sqp1 + 
  quote_gross (slice_pool P2 sqp) sqp' - quote_gross (slice_pool P2 sqp) sqp1"
proof -
  define P'' where "P'' = slice_pool P2 sqp"
  have "clmm_dsc P" using pool_comb_clmm_dsc assms by simp
  interpret finite_liq_pool
    by (simp add: \<open>clmm_dsc P\<close> clmm_dsc_liq(1) finite_liq_pool.intro)
  have "quote_gross P sqp' = quote_gross P1 sqp' + quote_gross P'' sqp'" 
    using assms P''_def pool_comb_quote_decomp by simp
  moreover have "quote_gross P sqp1 = quote_gross P1 sqp1 + quote_gross P'' sqp1" 
    using assms P''_def pool_comb_quote_decomp by simp
  ultimately show ?thesis unfolding P''_def by linarith
qed

lemma pool_comb_base_net_plus:
  assumes "clmm_dsc P1"
  and "clmm_dsc P2"
  and "grd P1 = grd P2"
  and "grd P1 (lower_tick P1 sqp2) = sqp2"
  and "0 < sqp2"
  and "0 < y"
  and "y \<le> quote_gross P (grd_max P)"
  and "P = pool_comb P1 P2 sqp2"
  and "sqp' = quote_reach P y"
  and "sqp' \<le> sqp2"
  and "nz_support (lq P) \<noteq> {}"
shows "base_net P sqp' = base_net P1 sqp' + base_net (slice_pool P2 sqp2) sqp'"
proof -
  define P'' where "P'' = slice_pool P2 sqp2"
  have "clmm_dsc P" using pool_comb_clmm_dsc assms by simp
  interpret finite_liq_pool
    by (simp add: \<open>clmm_dsc P\<close> clmm_dsc_liq(1) finite_liq_pool.intro)
  have "y = quote_gross P sqp'" 
    using clmm_quote_gross_reach_eq assms \<open>clmm_dsc P\<close> by auto
  show "base_net P sqp' = base_net P1 sqp' + base_net P'' sqp'" 
  proof (rule joint_base_net_decomp')
    show joint: "joint_pools P P1 P''" 
      using assms pool_comb_joint_refined unfolding P''_def by simp
    show "clmm_dsc P1" using assms by simp
    show "clmm_dsc P''" 
      using refine_clmm slice_pool_clmm_dsc assms 
      unfolding P''_def by auto
    show "nz_support (lq P) \<noteq> {}" using assms by simp
    show "0 \<le> quote_gross P sqp'" 
      using clmm_quote_gross_pos \<open>clmm_dsc P\<close> by simp
    show "sqp' = quote_reach P (quote_gross P sqp')" 
      using assms \<open>y = quote_gross P sqp'\<close> by presburger
    show "quote_gross P sqp' \<le> quote_gross P (grd_max P)" 
      using assms \<open>y = quote_gross P sqp'\<close> by linarith    
  qed simp+
qed

lemma combo_quote_init1:
  assumes "clmm_dsc P1"
  and "clmm_dsc P2"
  and "grd P1 = grd P2"
  and "grd P1 (lower_tick P1 sqp2) = sqp2"
  and "0 < sqp2"
  and "P = pool_comb P1 P2 sqp2"
  and "0 < y"
  and "nz_support (lq P1) \<noteq> {}"    
  and "nz_support (lq P2) \<noteq> {}"    
  and "y + quote_gross P sqp1 \<le> quote_gross P (grd_max P)"
  and "sqp' = quote_reach P (y + quote_gross P sqp1)"
  and "sqp2 < grd_max P2"
  and "sqp1 \<le> sqp2"
shows "quote_gross P sqp1 = quote_gross P1 sqp1" 
proof (rule pool_comb_quote_le_slice)
  have "clmm_dsc P" using pool_comb_clmm_dsc assms by simp
  show "nz_support (lq P) \<noteq> {}" using pool_comb_refined_joint_nz_liq assms by simp
  hence qa: "quote_gross P sqp' = y + quote_gross P sqp1" 
    using assms clmm_quote_gross_reach_eq \<open>clmm_dsc P\<close> clmm_quote_gross_pos 
    by auto
  show "clmm_dsc P1" using assms by simp
  show "clmm_dsc P2" using assms by simp
  show "grd P1 = grd P2" using assms by simp
  show "grd P1 (lower_tick P1 sqp2) = sqp2" using assms by simp
  show "P = pool_comb P1 P2 sqp2" using assms by simp
  show "0 < sqp2" using assms assms by simp
  show "sqp1 \<le> sqp2" using assms by simp
  have "sqp2 < grd_max P" using pool_comb_grd_max_slice assms by simp
  thus "sqp2 \<le> grd_max P" by simp
qed

lemma combo_remain_quote_eq:
  assumes "clmm_dsc P1"
  and "clmm_dsc P2"
  and "grd P1 = grd P2"
  and "grd P1 (lower_tick P1 sqp2) = sqp2"
  and "0 < sqp2"
  and "P = pool_comb P1 P2 sqp2"
  and "nz_support (lq P) \<noteq> {}"
  and "nz_support (lq P2) \<noteq> {}"
  and "0 < y"
  and "0< sqp1"
  and "y + quote_gross P sqp1 \<le> quote_gross P (grd_max P)"
  and "sqp' = quote_reach P (y + quote_gross P sqp1)"
  and "y1 = quote_gross P1 sqp' - quote_gross P1 sqp1"
  and "sqp2 \<le> sqp'"
  and "sqp1 \<le> sqp2"
  and "rs1' = quote_reach P2 (y - y1 + quote_gross P2 sqp2)"
shows "quote_gross P2 sqp' = quote_gross P2 rs1'" 
proof -
  have "clmm_dsc P" using pool_comb_clmm_dsc assms by simp
  define P'' where "P'' = slice_pool P2 sqp2" 
  define i where "i = lower_tick P2 sqp2"
  hence "grd P2 i = sqp2"
    using assms lower_tick_eq  by metis
  hence "quote_gross P2 sqp' = quote_gross P'' sqp' + quote_gross P2 sqp2" 
    using slice_pool_quote_gross P''_def assms i_def
    by simp 
  also have "... = quote_gross P sqp' - quote_gross P1 sqp' + quote_gross P2 sqp2" 
  proof -
    have "quote_gross P sqp' = quote_gross P'' sqp'+ quote_gross P1 sqp'"
      using pool_comb_quote_decomp P''_def assms pool_comb_joint_refined 
        quote_gross_join slice_pool_clmm_dsc
      by (metis add.commute)
    thus ?thesis by simp
  qed
  also have "... = y - y1 + quote_gross P2 sqp2"
  proof -
    have "quote_gross P sqp' = y + quote_gross P sqp1" 
      using assms clmm_quote_gross_reach_eq \<open>clmm_dsc P\<close> clmm_quote_gross_pos 
      by auto
    moreover have "quote_gross P1 sqp' = y1 + quote_gross P1 sqp1" 
      using assms by simp
    moreover have "quote_gross P sqp1 = quote_gross P1 sqp1" 
    proof (rule pool_comb_quote_le_slice)
      show "clmm_dsc P1" using assms by simp
      show "clmm_dsc P2" using assms by simp
      show "grd P1 = grd P2" using assms by simp
      show "grd P1 (lower_tick P1 sqp2) = sqp2" using assms by simp
      show "nz_support (lq P) \<noteq> {}" using assms by simp
      show "P = pool_comb P1 P2 sqp2" using assms by simp
      show "0 < sqp2" using assms assms by simp
      show "sqp1 \<le> sqp2" using assms by simp
      show "sqp2 \<le> grd_max P" 
        by (metis \<open>clmm_dsc P\<close> assms(11) assms(12) assms(14) assms(7) 
            calculation(1) quote_gross_imp_sqp_lt quote_gross_grd_max_ge 
            grd_max_quote_reach linorder_not_less order_le_imp_less_or_eq)
    qed
    ultimately show ?thesis by simp
  qed
  also have "... = quote_gross P2 (quote_reach P2 (y - y1 + quote_gross P2 sqp2))"
  proof (rule clmm_quote_gross_reach_eq[symmetric])
    show "clmm_dsc P2" using assms by simp
    show "nz_support (lq P2) \<noteq> {}" using assms by simp
    show "0 \<le> y - y1 + quote_gross P2 sqp2"
      by (metis assms(2) calculation clmm_quote_gross_pos)
    show "y - y1 + quote_gross P2 sqp2 \<le> quote_gross P2 (grd_max P2)"
      by (metis assms(2) assms(8) calculation quote_gross_grd_max_max)
  qed
  finally show ?thesis using assms by simp
qed

lemma comb_quote_gross_le:
  assumes "clmm_dsc P1"
  and "clmm_dsc P2"
  and "grd P1 = grd P2"
  and "0 < sqp"
  and "sqp < grd_max P"
  and "0 < y"
  and "y \<le> quote_gross P sqp"
  and "y \<le> quote_gross P (grd_max P)"
  and "P = pool_comb P1 P2 sqp"
  and "sqp' = quote_reach P y"
  and "nz_support (lq P) \<noteq> {}"
shows "quote_gross P1 sqp' = y"
proof -
  define P' where "P' = refine P1 sqp"
  define P'' where "P'' = slice_pool P2 sqp"
  hence "quote_gross P'' sqp = 0" using slice_pool_quote_gross_leq
    by (metis assms(2) assms(4) dual_order.refl)
  have "clmm_dsc P" using pool_comb_clmm_dsc assms by simp
  interpret finite_liq_pool
    by (simp add: \<open>clmm_dsc P\<close> clmm_dsc_liq(1) finite_liq_pool.intro)
  have "y = quote_gross P sqp'" 
    using clmm_quote_gross_reach_eq assms \<open>clmm_dsc P\<close> by auto
  hence "sqp' \<le> sqp" 
    using \<open>clmm_dsc P\<close> quote_reach_le_gross assms order_less_imp_le 
    by blast
  hence "quote_gross P'' sqp' = 0" using slice_pool_quote_gross_leq
    by (metis P''_def assms(2,4))
  have "quote_gross P sqp' = quote_gross P' sqp' + quote_gross P'' sqp" 
  proof (rule joint_quote_gross_decomp')
    show joint: "joint_pools P P' P''" 
      using assms pool_comb_joint unfolding P'_def P''_def by simp
    show "clmm_dsc P'" 
      using refine_clmm  assms unfolding P'_def by simp
    show "clmm_dsc P''" 
      using refine_clmm slice_pool_clmm_dsc assms 
      unfolding P''_def by auto
    show "nz_support (lq P) \<noteq> {}" using assms by simp
    show "0 \<le> quote_gross P sqp'" 
      using clmm_quote_gross_pos \<open>clmm_dsc P\<close> by simp
    show "sqp' = quote_reach P (quote_gross P sqp')" 
      using assms \<open>y = quote_gross P sqp'\<close> by presburger
    show "quote_gross P sqp' \<le> quote_gross P (grd_max P)" 
      using assms \<open>y = quote_gross P sqp'\<close> by linarith
    show "quote_gross P'' sqp = quote_gross P'' sqp'"
      by (simp add: \<open>quote_gross P'' sqp = 0\<close> \<open>quote_gross P'' sqp' = 0\<close>) 
  qed simp
  also have "... = quote_gross P' sqp'" using \<open>quote_gross P'' sqp = 0\<close> by simp
  also have "... = quote_gross P1 sqp'" 
    using refine_quote_gross assms P'_def by simp
  finally show ?thesis using \<open>y = quote_gross P sqp'\<close> by simp
qed

locale combined_pools =
  fixes P1 P2 P sqp2
  assumes cmb_P1: "clmm_dsc P1"
  and cmb_P2: "clmm_dsc P2"
  and cmb_grd_eq: "grd P1 = grd P2"
  and cmb_on_grid: "grd P1 (lower_tick P1 sqp2) = sqp2"
  and cmb_nz1: "nz_support (lq P1) \<noteq> {}"
  and cmb_nz2: "nz_support (lq P2) \<noteq> {}"
  and cmb_comb: "P = pool_comb P1 P2 sqp2"
  and cmb_pos: "0 < sqp2"
  and cmb_max: "sqp2 < grd_max P2"
  
begin

lemma combined_P_prop:
  shows "clmm_dsc P" "nz_support (lq P) \<noteq> {}"
proof -
  show "clmm_dsc P" 
    using cmb_P1 cmb_P2 cmb_comb pool_comb_clmm_dsc cmb_grd_eq cmb_pos by blast
  show "nz_support (lq P) \<noteq> {}" 
    using  pool_comb_refined_joint_nz_liq cmb_P1 cmb_P2 cmb_comb cmb_grd_eq 
      cmb_nz1 cmb_on_grid 
    by blast 
qed

lemmas cmb_props = cmb_P1 cmb_P2 cmb_grd_eq cmb_on_grid cmb_nz1 cmb_nz2 
  cmb_comb cmb_pos cmb_max combined_P_prop 

lemma combo_joint_quote_gross_decomp:
  assumes "0 < y"
  and "0 < sqp1"
  and "y + quote_gross P sqp1 \<le> quote_gross P (grd_max P)"
  and "sqp' = quote_reach P (y + quote_gross P sqp1)"
  and "y1 = quote_gross P1 sqp' - quote_gross P1 sqp1"
  and "P'' = slice_pool P2 sqp2"  
  and "y2' = quote_gross P'' sqp' - quote_gross P'' sqp1"
shows "y = y1 + y2'" "y1 \<le> y" "0 \<le> y1"
  "y1 + quote_gross P1 sqp1 \<le> quote_gross P1 (grd_max P1)" 
  "y2'  \<le> quote_gross P'' (grd_max P2)"
proof -
  have "clmm_dsc P" using combined_P_prop by simp
  have "nz_support (lq P) \<noteq> {}" using combined_P_prop by simp     
  have "quote_gross P sqp1 < quote_gross P (grd_max P)" using assms by simp
  hence "sqp1 < grd_max P"
    using \<open>clmm_dsc P\<close> quote_gross_imp_sqp_lt by blast
  define sqp1' where "sqp1' = quote_reach P1 (quote_gross P1 sqp')"
  have "quote_gross P sqp1 < quote_gross P sqp'" 
    using quote_reach_add_gt assms \<open>clmm_dsc P\<close> 
      \<open>nz_support (lq P) \<noteq> {}\<close>
    by simp
  hence "sqp1 < sqp'"
    using \<open>clmm_dsc P\<close> quote_gross_imp_sqp_lt[of P] by simp
  hence "0 < sqp'"
    using assms liq_grd_min combined_pools_axioms 
    unfolding combined_pools_def by fastforce
  have "quote_gross P1 sqp' \<le> quote_gross P1 (grd_max P1)"
    by (simp add: cmb_P1 cmb_nz1 quote_gross_grd_max_max)
  thus "y1 + quote_gross P1 sqp1 \<le> quote_gross P1 (grd_max P1)"
    by (simp add: assms(5)) 
  have "clmm_dsc P''" using assms slice_pool_clmm_dsc cmb_P2 cmb_pos by simp
  have "grd_max P2 = grd_max P''" using slice_pool_grd_max'
    by (simp add: assms cmb_P2 cmb_max cmb_nz2 cmb_pos)
  have "nz_support (lq P'') \<noteq> {}" using slice_pool_nz_liq'
    by (simp add: assms cmb_P2 cmb_max cmb_nz2 cmb_pos)
  define sqp2' where "sqp2' = quote_reach P'' (quote_gross P'' sqp')"
  have "quote_gross P sqp1 < quote_gross P sqp'" 
    using quote_reach_add_gt assms \<open>clmm_dsc P\<close> 
      \<open>nz_support (lq P) \<noteq> {}\<close>
    by simp
  hence "sqp1 < sqp'"
    using \<open>clmm_dsc P\<close> quote_gross_imp_sqp_lt[of P] by simp
  have "0 \<le> y2'"
    by (metis \<open>clmm_dsc P''\<close> \<open>sqp1 < sqp'\<close> quote_gross_imp_sqp_lt 
        diff_ge_0_iff_ge eucl_less_le_not_le linorder_less_linear 
        verit_comp_simplify1(2) assms(7))
  show "y = y1 + y2'" 
  proof -
    have "quote_gross P sqp' = y + quote_gross P sqp1" 
      using assms clmm_quote_gross_reach_eq \<open>clmm_dsc P\<close> clmm_quote_gross_pos 
        \<open>nz_support (lq P) \<noteq> {}\<close> 
      by auto
    hence "y = quote_gross P sqp' - quote_gross P sqp1" by simp
    also have "... = quote_gross P1 sqp' - quote_gross P1 sqp1 +
        quote_gross (slice_pool P2 sqp2) sqp' - 
        quote_gross (slice_pool P2 sqp2) sqp1" 
    proof (rule pool_comb_quote_diff_decomp[OF cmb_P1 cmb_P2 cmb_grd_eq cmb_on_grid])
      show  "nz_support (lq P) \<noteq> {}" "P = pool_comb P1 P2 sqp2"
          "sqp1 \<le> grd_max P" 
        using \<open>nz_support (lq P) \<noteq> {}\<close> \<open>sqp1 < grd_max P\<close> cmb_comb by auto
      show "0 < sqp1" using assms liq_grd_min cmb_P1 cmb_nz1 by fastforce
      have "0 < grd_min P" 
        using \<open>nz_support (lq P) \<noteq> {}\<close> \<open>clmm_dsc P\<close> liq_grd_min by simp         
      thus "0 < sqp'" 
        using assms clmm_quote_reach_ge \<open>nz_support (lq P) \<noteq> {}\<close>
        by (metis \<open>clmm_dsc P\<close> \<open>quote_gross P sqp' = y + quote_gross P sqp1\<close> 
            add_less_le_mono clmm_quote_gross_pos less_add_same_cancel1) 
      show "sqp' \<le> grd_max P" 
        using quote_reach_leq_grd_max assms \<open>nz_support (lq P) \<noteq> {}\<close>
        by (simp add: \<open>clmm_dsc P\<close> clmm_quote_gross_pos)
      show "0 < sqp2" using cmb_pos by simp
    qed
    also have "... = y1 + y2'" using assms  by simp
    finally show ?thesis .
  qed
  show "y1 \<le> y" using \<open>0 \<le> y2'\<close> \<open>y = y1 + y2'\<close> by simp
  show "y2' \<le> quote_gross P'' (grd_max P2)"
    by (metis \<open>clmm_dsc P''\<close> \<open>nz_support (lq P'') \<noteq> {}\<close> 
        \<open>grd_max P2 = grd_max P''\<close> add.commute add_diff_cancel assms(7) 
        clmm_quote_gross_pos quote_gross_grd_max_max diff_add_cancel 
        diff_ge_0_iff_ge dual_order.trans)
  show "0 \<le> y1"
    by (metis \<open>sqp1 < sqp'\<close> assms(5) quote_gross_imp_sqp_lt 
        cmb_P1 eq_diff_eq' le_add_same_cancel2 less_eq_real_def 
        linorder_neqE_linordered_idom order.asym)
qed

lemma combo_joint_quote_gross_leq_max:
  assumes "0 < y"
  and "0 < sqp1"
  and "y + quote_gross P sqp1 \<le> quote_gross P (grd_max P)"
  and "sqp' = quote_reach P (y + quote_gross P sqp1)"
  and "y1 = quote_gross P1 sqp' - quote_gross P1 sqp1" 
shows "y- y1 + quote_gross P2 sqp2 \<le> quote_gross P2 (grd_max P2)"
proof -
  define P'' where "P'' = slice_pool P2 sqp2"  
  define y2' where "y2' = quote_gross P'' sqp' - quote_gross P'' sqp1"
  have "y - y1 = y2'" using y2'_def P''_def assms combo_joint_quote_gross_decomp
    by (metis add_diff_cancel_left') 
  also have "... \<le> quote_gross P'' (grd_max P2)" 
    using assms combo_joint_quote_gross_decomp 
    unfolding y2'_def P''_def 
    by metis
  also have "... = quote_gross P2 (grd_max P2) - quote_gross P2 sqp2" 
    unfolding P''_def
    using cmb_P2 cmb_grd_eq cmb_max cmb_on_grid cmb_pos lower_tick_eq 
      slice_pool_quote_gross 
    by auto
  finally have "y - y1 \<le> quote_gross P2 (grd_max P2) - quote_gross P2 sqp2" .
  thus ?thesis by simp
qed

lemma combo_joint_quote_gross_price_le:
  assumes "0 < y"
  and "grd_min P1 \<le> sqp1" 
  and "sqp1 \<le> sqp2"
  and "y + quote_gross P sqp1 \<le> quote_gross P (grd_max P)"
  and "sqp' = quote_reach P (y + quote_gross P sqp1)"
  and "y1 = quote_gross P1 sqp' - quote_gross P1 sqp1"
  and "rs1 = quote_reach P1 (y1 + quote_gross P1 sqp1)"
shows "rs1 \<le> sqp'"
proof (cases "y1 + quote_gross P1 sqp1 = 0")
  case True
  hence "rs1 = grd_min P1" using assms
    by (simp add: clmm_quote_reach_zero cmb_P1 cmb_nz1)
  also have "... = grd_min P" using assms pool_comb_le_grd_min
    by (simp add: cmb_P1 cmb_P2 cmb_comb cmb_grd_eq cmb_max cmb_nz1 cmb_nz2 
        cmb_pos)
  also have "... < sqp'"
  proof -
    have "0 < y + quote_gross P sqp1"
      by (simp add: add_pos_nonneg assms clmm_quote_gross_pos combined_P_prop)
    thus ?thesis using assms
      by (simp add: combined_P_prop quote_reach_gt_grd_min)
  qed
  finally show ?thesis by simp
next
  case False
  hence "0 < y1 + quote_gross P1 sqp1"
    by (metis assms(6) clmm_quote_gross_pos cmb_P1 diff_add_cancel 
        less_eq_real_def)
  show ?thesis
    by (smt (z3) \<open>0 < y1 + quote_gross P1 sqp1\<close> assms clmm_quote_gross_pos 
        quote_reach_le_gross quote_gross_grd_max_max clmm_quote_reach_ge 
        quote_reach_leq_grd_max liq_grd_min cmb_P1 cmb_nz1 combined_P_prop) 
qed

lemma combo_joint_quote_gross_decomp_leq:
  assumes "0 < y"
  and "0 < sqp1"
  and "y + quote_gross P sqp1 \<le> quote_gross P (grd_max P)"
  and "sqp' = quote_reach P (y + quote_gross P sqp1)"
  and "y1 = quote_gross P1 sqp' - quote_gross P1 sqp1"
  and "P'' = slice_pool P2 sqp2"  
  and "sqp1 \<le> sqp2"
  and "y2' = quote_gross P'' sqp'"
shows "y = y1 + y2'" "y1 \<le> y" "0 \<le> y1"
  "y1 + quote_gross P1 sqp1 \<le> quote_gross P1 (grd_max P1)" 
  "y2'  \<le> quote_gross P'' (grd_max P2)"
proof -
  have "quote_gross P'' sqp1 = 0"
    by (smt (verit) assms(2) assms(6) assms(7) sqp_lt_grd_max_imp_idx 
        clmm_quote_gross_grd_min_le cmb_P2 cmb_grd_eq cmb_max cmb_nz2 
        cmb_on_grid grd_lower_tick_cong slice_pool_clmm_dsc slice_pool_grd_min) 
  hence eq: "y2' = quote_gross P'' sqp' - quote_gross P'' sqp1" using assms by simp
  thus "y = y1 + y2'" using assms combo_joint_quote_gross_decomp by blast
  show "y1 \<le> y" using assms combo_joint_quote_gross_decomp(2) by blast
  show "y1 + quote_gross P1 sqp1 \<le> quote_gross P1 (grd_max P1)"  
    using assms combo_joint_quote_gross_decomp(4) by blast
  show "y2'  \<le> quote_gross P'' (grd_max P2)" 
    using eq assms combo_joint_quote_gross_decomp(5) by blast
  show "0 \<le> y1" 
    using eq assms combo_joint_quote_gross_decomp(3) by blast
qed

lemma combo_quote_swap_slice_eq:
  assumes "0 < sqp1"
  and "0 < y"
  and "y + quote_gross P sqp1 \<le> quote_gross P (grd_max P)"
  and "sqp' = quote_reach P (y + quote_gross P sqp1)"
  and "y1 = quote_gross P1 sqp' - quote_gross P1 sqp1"
shows "quote_swap P sqp1 y = quote_swap P1 sqp1 y1 + 
    quote_swap (slice_pool P2 sqp2) sqp1 (y - y1)" 
proof -
  have "clmm_dsc P" using combined_P_prop by simp
  have "nz_support (lq P) \<noteq> {}" using combined_P_prop by simp
  have "quote_gross P sqp1 < quote_gross P (grd_max P)" using assms by simp
  hence "sqp1 < grd_max P"
    using \<open>clmm_dsc P\<close> quote_gross_imp_sqp_lt by blast
  define sqp1' where "sqp1' = quote_reach P1 (quote_gross P1 sqp')"
  have "quote_gross P sqp1 < quote_gross P sqp'" 
    using quote_reach_add_gt assms \<open>clmm_dsc P\<close> 
      \<open>nz_support (lq P) \<noteq> {}\<close>
    by simp
  hence "sqp1 < sqp'"
    using \<open>clmm_dsc P\<close> quote_gross_imp_sqp_lt[of P] by simp
  hence "0 < sqp'"
    using assms liq_grd_min combined_pools_axioms 
    unfolding combined_pools_def by fastforce
  define P'' where "P'' = slice_pool P2 sqp2"  
  have "clmm_dsc P''" 
    using P''_def assms slice_pool_clmm_dsc cmb_pos by (simp add: cmb_P2)
  have "grd_max P2 = grd_max P''" using slice_pool_grd_max'
    by (simp add: P''_def cmb_P2 cmb_max cmb_nz2 cmb_pos)
  have "nz_support (lq P'') \<noteq> {}" using slice_pool_nz_liq'
    by (simp add: P''_def cmb_P2 cmb_max cmb_nz2 cmb_pos)
  define y2' where "y2' = quote_gross P'' sqp' - quote_gross P'' sqp1"
  define sqp2' where "sqp2' = quote_reach P'' (quote_gross P'' sqp')"
  have "quote_gross P sqp1 < quote_gross P sqp'" 
    using quote_reach_add_gt assms \<open>clmm_dsc P\<close> 
      \<open>nz_support (lq P) \<noteq> {}\<close>
    by simp
  hence "sqp1 < sqp'"
    using \<open>clmm_dsc P\<close> quote_gross_imp_sqp_lt[of P] by simp
  have "0 \<le> y2'"
    by (metis \<open>clmm_dsc P''\<close> \<open>sqp1 < sqp'\<close> quote_gross_imp_sqp_lt 
        diff_ge_0_iff_ge eucl_less_le_not_le linorder_less_linear 
        verit_comp_simplify1(2) y2'_def)
  have "y = y1 + y2'" using assms combo_joint_quote_gross_decomp y2'_def P''_def 
    by blast
  have "quote_swap P sqp1 y = base_net P sqp1 - base_net P sqp'" 
    using assms unfolding quote_swap_def by simp
  also have "... = base_net P1 sqp1 + base_net P'' sqp1 -
      (base_net P1 sqp' + base_net P'' sqp')"
    using assms pool_comb_base_net_plus combined_pools_axioms 
    unfolding combined_pools_def
    by (metis P''_def \<open>clmm_dsc P''\<close> base_net_join pool_comb_joint_refined)
  also have "... = base_net P1 sqp1 - base_net P1 sqp' + 
      base_net P'' sqp1 - base_net P'' sqp'"
    by linarith
  also have "... = quote_swap P1 sqp1 y1 + quote_swap P'' sqp1 y2'" 
  proof - 
    have "base_net P1 sqp1' = base_net P1 sqp'" 
      using quote_reach_base_net
      by (simp add: \<open>0 < sqp'\<close> cmb_P1 cmb_nz1 sqp1'_def)   
    moreover have "base_net P'' sqp2' = base_net P'' sqp'"  
      using quote_reach_base_net
      by (simp add: \<open>0 < sqp'\<close> \<open>clmm_dsc P''\<close> \<open>nz_support (lq P'') \<noteq> {}\<close> sqp2'_def)    
    ultimately show ?thesis
      unfolding quote_swap_def
      by (simp add: assms sqp1'_def sqp2'_def y2'_def)
  qed
  finally show ?thesis 
    using \<open>y = y1 + y2'\<close> P''_def by simp
qed

lemma combo_quote_swap_eq:
  assumes "0 < sqp1"
  and "0 < y"
  and "y + quote_gross P sqp1 \<le> quote_gross P (grd_max P)"
  and "sqp' = quote_reach P (y + quote_gross P sqp1)"
  and "y1 = quote_gross P1 sqp' - quote_gross P1 sqp1"
  and "sqp1 \<le> sqp2"
shows "quote_swap P sqp1 y = quote_swap P1 sqp1 y1 +
      quote_swap P2 sqp2 (y - y1)"
proof -
  define P'' where "P'' = slice_pool P2 sqp2"    
  define y2' where "y2' = quote_gross P'' sqp' - quote_gross P'' sqp1"
  have "y = y1 + y2'" using assms combo_joint_quote_gross_decomp y2'_def P''_def 
    by blast
  hence "y2' = y - y1" by simp
  have "y1 \<le> y" using assms combo_joint_quote_gross_decomp(2) by simp 
  hence "0 \<le> y2'" using \<open>y2' = y - y1\<close>  y2'_def by simp
  have "quote_swap P sqp1 y = quote_swap P1 sqp1 y1 + 
      quote_swap P'' sqp1 y2'" 
    using assms combo_quote_swap_slice_eq P''_def \<open>y2' = y - y1\<close> 
    by blast
  also have "... = quote_swap P1 sqp1 y1 +
      quote_swap P2 sqp2 y2'" 
  proof -
    have "quote_swap P'' sqp1 y2' = quote_swap P2 sqp2 y2'" 
    proof (rule slice_pool_quote_swap)
      show "clmm_dsc P2" using cmb_P2 by simp
      show "nz_support (lq P2) \<noteq> {}" using cmb_nz2 by simp
      show "grd P2 (lower_tick P2 sqp2) = sqp2"
        using cmb_P2 cmb_grd_eq cmb_on_grid lower_tick_eq by auto
      show "P'' = slice_pool P2 sqp2" using P''_def by simp
      show "sqp1 \<le> sqp2" using assms by simp
      show "sqp2 < grd_max P2" using cmb_max by simp
      show "0 < sqp1" using assms liq_grd_min cmb_P1 cmb_nz1 by fastforce 
      show "0 \<le> y2'" using \<open>0 \<le> y2'\<close> .
      have "y2' \<le> quote_gross P'' (grd_max P2)" 
        using combo_joint_quote_gross_decomp(5)
        by (simp add: P''_def assms(1-4) y2'_def)
      also have "... = quote_gross P2 (grd_max P2) - quote_gross P2 sqp2"
        using P''_def \<open>grd P2 (lower_tick P2 sqp2) = sqp2\<close> cmb_P2 assms(1-2) 
          slice_pool_quote_gross cmb_max cmb_pos 
        by auto
      finally show "y2' + quote_gross P2 sqp2 \<le> quote_gross P2 (grd_max P2)" 
        by simp
    qed
    thus ?thesis by simp
  qed
  finally show ?thesis using \<open>y = y1 + y2'\<close> P''_def by simp
qed

lemma comb_add_above_gt:
  assumes "0 < y"
  and "0< sqp1"
  and "y + quote_gross P sqp1 \<le> quote_gross P (grd_max P)"
  and "sqp' = quote_reach P (y + quote_gross P sqp1)"
  and "y1 = quote_gross P1 sqp' - quote_gross P1 sqp1"
  and "y1 < y"
  and "sqp1 \<le> sqp2"
shows "sqp2 < sqp'"
proof -
  define P'' where "P'' = slice_pool P2 sqp2"
  have "y + quote_gross P1 sqp1 = y + quote_gross P sqp1"
  proof -
    have "quote_gross P sqp1 = quote_gross P1 sqp1"
    proof (rule pool_comb_quote_le_slice)
      show "grd P1 (lower_tick P1 sqp2) = sqp2"
        using cmb_grd_eq cmb_on_grid by auto 
      show "sqp2 \<le> grd_max P" 
        using cmb_max pool_comb_grd_max
        by (simp add: cmb_P1 cmb_P2 cmb_comb cmb_grd_eq cmb_nz1 cmb_nz2 cmb_pos)
      show "nz_support (lq P) \<noteq> {}"
        using cmb_comb combined_P_prop(2) by auto
    qed (auto simp add: cmb_props assms)
    thus ?thesis by simp
  qed      
  also have "... = quote_gross P sqp'" 
    using clmm_quote_gross_reach_eq assms clmm_quote_gross_pos 
      combined_P_prop 
    by auto 
  also have "... = quote_gross P1 sqp' + quote_gross P'' sqp'" 
    using pool_comb_quote_decomp P''_def cmb_P1 cmb_P2 cmb_comb cmb_grd_eq cmb_pos
      cmb_on_grid pool_comb_joint_refined quote_gross_join slice_pool_clmm_dsc 
    by simp
  also have "... = y1 +  quote_gross P1 sqp1 + quote_gross P'' sqp'"
  proof -
    have "quote_gross P1 sqp' = y1 +  quote_gross P1 sqp1"
      using clmm_quote_gross_reach_eq assms by simp
    thus ?thesis by simp
  qed
  finally have "y + quote_gross P1 sqp1 = y1 +  quote_gross P1 sqp1 + 
      quote_gross P'' sqp'" .
  hence "quote_gross P'' sqp' = y - y1" by simp
  hence "0 < quote_gross P'' sqp'" using assms by simp
  hence "grd_min P'' < sqp'"
    by (metis P''_def cmb_P2 cmb_max cmb_nz2 cmb_pos quote_gross_pos_gt_grd_min 
        slice_pool_clmm_dsc slice_pool_nz_liq') 
  moreover have "sqp2 \<le> grd_min P''" 
    unfolding P''_def using slice_pool_grd_min
    by (metis cmb_P2 cmb_max cmb_nz2 cmb_pos)
  ultimately show ?thesis by simp
qed

lemma comb_add_above_add_eq:
  assumes "y1 = quote_gross P1 sqp' - quote_gross P1 sqp1"
  and "rs1 = quote_reach P1 (y1 + quote_gross P1 sqp1)"
shows "quote_gross P1 sqp' = quote_gross P1 rs1"
  by (simp add: assms clmm_quote_gross_pos quote_gross_grd_max_max 
      clmm_quote_gross_reach_eq cmb_P1 cmb_nz1)

lemma comb_add_above_add_eq2:
  assumes "0 < y"
  and "grd_min P1 \<le> sqp1"
  and "y + quote_gross P sqp1 \<le> quote_gross P (grd_max P)"
  and "sqp' = quote_reach P (y + quote_gross P sqp1)"
  and "y1 = quote_gross P1 sqp' - quote_gross P1 sqp1"
  and "sqp1 \<le> sqp2"
  and "y1 < y"
  and "rs1' = quote_reach P2 (y - y1 + quote_gross P2 sqp2)"
shows "quote_gross P2 sqp' = quote_gross P2 rs1'"
  using combo_remain_quote_eq comb_add_above_gt liq_grd_min combined_P_prop
    liq_grd_min cmb_props combined_P_prop
  by (smt (verit) assms(3-8) clmm_quote_gross_pos 
      quote_gross_grd_max_max clmm_quote_gross_reach_eq 
      joint_quote_gross_decomp' lower_tick_eq pool_comb_grd_max_slice 
      pool_comb_joint_refined pool_comb_quote_le_slice slice_pool_clmm_dsc 
      slice_pool_quote_gross)

lemma combo_joint_rest_qty_slice:
  assumes "0 < y"
  and "0 < sqp1" 
  and "sqp1 \<le> sqp2"
  and "y + quote_gross P sqp1 < quote_gross P (grd_max P)"
  and "sqp' = quote_reach P (y + quote_gross P sqp1)"
  and "y1 = quote_gross P1 sqp' - quote_gross P1 sqp1"
  and "P'' = slice_pool P2 sqp2" 
shows "y - y1 = quote_gross P'' sqp'"
  by (smt (verit, ccfv_SIG) assms combo_joint_quote_gross_decomp_leq(1) 
      combined_pools_axioms)

lemma combo_joint_rest_qty:
  assumes "0 < y"
  and "0 < sqp1" 
  and "sqp1 \<le> sqp2"
  and "y + quote_gross P sqp1 < quote_gross P (grd_max P)"
  and "sqp' = quote_reach P (y + quote_gross P sqp1)"
  and "y1 = quote_gross P1 sqp' - quote_gross P1 sqp1"
  and "sqp2 \<le> sqp'"
shows "y - y1 = quote_gross P2 sqp' - quote_gross P2 sqp2"
proof -
  define P'' where "P'' = slice_pool P2 sqp2" 
  have "y - y1 = quote_gross P'' sqp'" 
    using assms P''_def combo_joint_rest_qty_slice by simp
  also have "... = quote_gross P2 sqp' - quote_gross P2 sqp2" 
    using P''_def slice_pool_quote_gross assms(7) cmb_P2 cmb_grd_eq cmb_on_grid 
      cmb_pos lower_tick_eq 
    by auto
  finally show ?thesis .
qed

lemma combo_joint_rest_qty_le:
  assumes "0 < y"
  and "0 < sqp1" 
  and "sqp1 \<le> sqp2"
  and "y + quote_gross P sqp1 < quote_gross P (grd_max P)"
  and "sqp' = quote_reach P (y + quote_gross P sqp1)"
  and "y1 = quote_gross P1 sqp' - quote_gross P1 sqp1"
shows "y - y1 + quote_gross P2 sqp2 \<le> quote_gross P2 (grd_max P2)"
proof -
  define P'' where "P'' = slice_pool P2 sqp2" 
  have "y - y1 \<le> quote_gross P'' (grd_max P2)" 
  proof (rule combo_joint_quote_gross_decomp_leq(5))
    show "0 < y" using assms by simp
    show "0 < sqp1" using assms grd_min_pos cmb_P1 cmb_nz1 by fastforce
    show "y - y1 = quote_gross P'' sqp'"
      using combo_joint_rest_qty_slice assms P''_def by simp
    show "y + quote_gross P sqp1 \<le> quote_gross P (grd_max P)" using assms by simp
    show "sqp' = quote_reach P (y + quote_gross P sqp1)" using assms by simp
    show "sqp1 \<le> sqp2" using assms by simp
    show "y1  = quote_gross P1 sqp' - quote_gross P1 sqp1" using assms by simp
    show "P'' = slice_pool P2 sqp2" using P''_def by simp
  qed 
  also have "... = quote_gross P2 (grd_max P2) - quote_gross P2 sqp2"
    using P''_def cmb_P2 cmb_grd_eq cmb_max cmb_on_grid cmb_pos lower_tick_eq 
      slice_pool_quote_gross by simp
  finally have "y - y1 \<le> quote_gross P2 (grd_max P2) - quote_gross P2 sqp2" .
  thus ?thesis by simp
qed

lemma combo_joint_rest_price_pos:
  assumes "0 < y"
  and "grd_min P1 \<le> sqp1"
  and "y + quote_gross P sqp1 \<le> quote_gross P (grd_max P)"
  and "sqp' = quote_reach P (y + quote_gross P sqp1)"
  and "y1 = quote_gross P1 sqp' - quote_gross P1 sqp1"
  and "rs1' = quote_reach P2 (y - y1 + quote_gross P2 sqp2)"
  and "y1 < y"
shows "0 < rs1'" 
  using clmm_quote_reach_pos 
  by (metis (no_types, opaque_lifting) add_strict_increasing assms 
      clmm_quote_gross_pos liq_grd_min cmb_P1 cmb_P2 cmb_nz1 cmb_nz2 
      combo_joint_quote_gross_leq_max diff_gt_0_iff_gt less_add_same_cancel1 
      less_eq_real_def)

lemma combo_joint_quote_gross_price_le':
  assumes "0 < y"
  and "grd_min P1 \<le> sqp1" 
  and "sqp1 \<le> sqp2"
  and "y + quote_gross P sqp1 \<le> quote_gross P (grd_max P)"
  and "sqp' = quote_reach P (y + quote_gross P sqp1)"
  and "y1 = quote_gross P1 sqp' - quote_gross P1 sqp1"
  and "y1 < y"
  and "rs1' = quote_reach P2 (y - y1 + quote_gross P2 sqp2)"
shows "rs1' \<le> sqp'"
proof (rule clmm_quote_reach_le)  
  show "clmm_dsc P2" using cmb_P2 .
  show "nz_support (lq P2) \<noteq> {}" using cmb_nz2 .
  show "0 < y - y1 + quote_gross P2 sqp2"
    by (simp add: add_pos_nonneg assms(7) clmm_quote_gross_pos cmb_P2)
  show "rs1' = quote_reach P2 (y - y1 + quote_gross P2 sqp2)" 
    using assms by simp
  have primeq: "quote_gross P2 sqp' = quote_gross P2 rs1'"  
    using assms comb_add_above_add_eq2 by simp 
  have q1': "quote_gross P2 rs1' = y - y1 + quote_gross P2 sqp2"
    using clmm_quote_gross_reach_eq assms
      clmm_quote_gross_pos cmb_P2 cmb_nz2
    by (smt (verit, best) liq_grd_min cmb_P1 cmb_nz1 
        combo_joint_quote_gross_leq_max combined_pools_axioms)
  show "sqp' \<in> quote_gross P2 -` {y - y1 + quote_gross P2 sqp2}" 
    using primeq q1' by simp
qed

lemma comb_add_above_price1_leq:
  assumes "0 < y"
  and "grd_min P1 \<le> sqp1"
  and "y + quote_gross P sqp1 \<le> quote_gross P (grd_max P)"
  and "sqp' = quote_reach P (y + quote_gross P sqp1)"
  and "y1 = quote_gross P1 sqp' - quote_gross P1 sqp1"
  and "sqp1 \<le> sqp2"
  and "0 \<le> y2"
  and "y - y2 + quote_gross P2 sqp2 \<le> quote_gross P2 (grd_max P2)"
  and "y2 < y1"
  and "y1 < y"  
  and "rs1 = quote_reach P1 (y1 + quote_gross P1 sqp1)"
  and "rs2 = quote_reach P1 (y2 + quote_gross P1 sqp1)"
shows "rs2 \<le> rs1" 
proof (rule quote_reach_mono)
  have q1: "quote_gross P1 rs1 = y1 + quote_gross P1 sqp1" 
    using clmm_quote_gross_reach_eq
    by (simp add: assms clmm_quote_gross_pos quote_gross_grd_max_max 
        cmb_P1 cmb_nz1)
  show "clmm_dsc P1" using cmb_P1 by simp
  show "nz_support (lq P1) \<noteq> {}" using cmb_nz1 by simp
  show "y2 + quote_gross P1 sqp1 \<le> y1 + quote_gross P1 sqp1" using assms by simp
  show "y1 + quote_gross P1 sqp1 \<le> quote_gross P1 (grd_max P1)"
    by (metis quote_gross_grd_max_max cmb_P1 cmb_nz1 q1)       
  show "0 \<le> y2 + quote_gross P1 sqp1" using assms
    by (simp add: clmm_quote_gross_pos cmb_P1)
qed (simp add: assms)+

lemma comb_add_above_price2_geq:
  assumes "0 < y"
  and "grd_min P1 \<le> sqp1"
  and "y + quote_gross P sqp1 \<le> quote_gross P (grd_max P)"
  and "sqp' = quote_reach P (y + quote_gross P sqp1)"
  and "y1 = quote_gross P1 sqp' - quote_gross P1 sqp1"
  and "sqp1 \<le> sqp2"
  and "0 \<le> y2"
  and "y - y2 + quote_gross P2 sqp2 \<le> quote_gross P2 (grd_max P2)"
  and "y2 < y1"
  and "y1 < y"  
  and "rs1' = quote_reach P2 (y - y1 + quote_gross P2 sqp2)"
  and "rs2' = quote_reach P2 (y - y2 + quote_gross P2 sqp2)" 
shows "rs1' \<le> rs2'" 
proof (rule quote_reach_mono)
  show "clmm_dsc P2" using cmb_P2 by simp
  show "nz_support (lq P2) \<noteq> {}" using cmb_nz2 by simp
  have "0 \<le> y - y1" using assms by simp
  thus "0 \<le> y - y1 + quote_gross P2 sqp2"
    by (simp add: clmm_quote_gross_pos cmb_P2)
  show "y - y1 + quote_gross P2 sqp2 \<le> y - y2 + quote_gross P2 sqp2" 
    using assms by simp
  show "y - y2 + quote_gross P2 sqp2 \<le> quote_gross P2 (grd_max P2)"
    using assms by simp
qed (simp add: assms)+  

lemma comb_add_above_price2_geq':
  assumes "0 < y"
  and "grd_min P1 \<le> sqp1"
  and "y + quote_gross P sqp1 \<le> quote_gross P (grd_max P)"
  and "sqp' = quote_reach P (y + quote_gross P sqp1)"
  and "y1 = quote_gross P1 sqp' - quote_gross P1 sqp1"
  and "sqp1 \<le> sqp2"
  and "0 \<le> y2"
  and "y - y1 + quote_gross P2 sqp2 \<le> quote_gross P2 (grd_max P2)"
  and "y1 < y2"
  and "y2 \<le> y"  
  and "rs1' = quote_reach P2 (y - y1 + quote_gross P2 sqp2)"
  and "rs2' = quote_reach P2 (y - y2 + quote_gross P2 sqp2)" 
shows "rs2' \<le> rs1'" 
proof (rule quote_reach_mono)
  show "clmm_dsc P2" using cmb_P2 by simp
  show "nz_support (lq P2) \<noteq> {}" using cmb_nz2 by simp
  have "0 \<le> y - y2" using assms by simp
  thus "0 \<le> y - y2 + quote_gross P2 sqp2"
    by (simp add: clmm_quote_gross_pos cmb_P2)
  show "y - y2 + quote_gross P2 sqp2 \<le> y - y1 + quote_gross P2 sqp2" 
    using assms by simp
  show "y - y1 + quote_gross P2 sqp2 \<le> quote_gross P2 (grd_max P2)"
    using assms by simp
qed (simp add: assms)+  

lemma comb_add_above_price2_lt:
  assumes "0 < y"
  and "grd_min P1 \<le> sqp1"
  and "y + quote_gross P sqp1 \<le> quote_gross P (grd_max P)"
  and "sqp' = quote_reach P (y + quote_gross P sqp1)"
  and "y1 = quote_gross P1 sqp' - quote_gross P1 sqp1"
  and "sqp1 \<le> sqp2"
  and "0 \<le> y2"
  and "y - y2 + quote_gross P2 sqp2 \<le> quote_gross P2 (grd_max P2)"
  and "y2 < y1"
  and "y1 < y"  
  and "rs2' = quote_reach P2 (y - y2 + quote_gross P2 sqp2)"  
shows "sqp' < rs2'" 
proof (rule lt_quote_gross_imp_up_price) 
  define rs1' where "rs1' = quote_reach P2 (y - y1 + quote_gross P2 sqp2)"
  have primeq: "quote_gross P2 sqp' = quote_gross P2 rs1'"
    using assms comb_add_above_add_eq2 rs1'_def by simp 
  have q1': "quote_gross P2 rs1' = y - y1 + quote_gross P2 sqp2"
    unfolding rs1'_def 
    using clmm_quote_gross_reach_eq assms(8-10) 
      clmm_quote_gross_pos cmb_P2 cmb_nz2 by auto 
  show "clmm_dsc P2" using cmb_P2 .
  show "nz_support (lq P2) \<noteq> {}" using cmb_nz2 .
  show "0 < y - y2 + quote_gross P2 sqp2"
    by (metis add.commute add_strict_increasing2 assms(10) assms(9) 
        clmm_quote_gross_pos cmb_P2 diff_add_cancel less_add_same_cancel1 
        pos_add_strict) 
  show "y - y2 + quote_gross P2 sqp2 \<le> quote_gross P2 (grd_max P2)"
    using assms by simp
  show "quote_gross P2 sqp' < y - y2 + quote_gross P2 sqp2"
    by (simp add: assms(9) primeq q1')
  show "rs2' = quote_reach P2 (y - y2 + quote_gross P2 sqp2)" 
    using assms by simp
qed

lemma combo_joint_reached_price_pos:
  assumes "0 < y"
  and "y + quote_gross P sqp1 \<le> quote_gross P (grd_max P)"
  and "sqp' = quote_reach P (y + quote_gross P sqp1)"
shows "0 < sqp'" using clmm_quote_reach_pos
  using assms clmm_quote_gross_pos combined_P_prop by auto

lemma combo_joint_base_reached_eq:
  assumes "0 < y"
  and "grd_min P1 \<le> sqp1"
  and "y + quote_gross P sqp1 \<le> quote_gross P (grd_max P)"
  and "sqp' = quote_reach P (y + quote_gross P sqp1)"
  and "y1 = quote_gross P1 sqp' - quote_gross P1 sqp1"
  and "sqp1 \<le> sqp2"
  and "rs1 = quote_reach P1 (y1 + quote_gross P1 sqp1)"
shows "base_net P1 sqp' = base_net P1 rs1" 
proof (rule quote_gross_equiv_base_net[symmetric]) 
  show "quote_gross P1 rs1 = quote_gross P1 sqp'"
    using assms comb_add_above_add_eq by metis
  show "clmm_dsc P1" using cmb_P1 .
  show "0 < rs1" using clmm_quote_reach_pos
    by (simp add: assms(5) assms(7) clmm_quote_gross_pos 
        quote_gross_grd_max_max cmb_P1 cmb_nz1)
  show "rs1 \<le> sqp'"
    using assms combo_joint_quote_gross_price_le by blast
qed

lemma combo_joint_base_reached_eq2:
  assumes "0 < y"
  and "grd_min P1 \<le> sqp1"
  and "y + quote_gross P sqp1 \<le> quote_gross P (grd_max P)"
  and "sqp' = quote_reach P (y + quote_gross P sqp1)"
  and "y1 = quote_gross P1 sqp' - quote_gross P1 sqp1"
  and "sqp1 \<le> sqp2"
  and "y1 < y" 
  and "rs1' = quote_reach P2 (y - y1 + quote_gross P2 sqp2)"
shows "base_net P2 sqp' = base_net P2 rs1'" 
proof -
  have quoteq: "quote_gross P2 sqp' = quote_gross P2 rs1'"
    using assms comb_add_above_add_eq2 by simp 
  show ?thesis
  proof (cases "rs1' \<le> sqp'")
    case True
    show ?thesis
    proof (rule quote_gross_equiv_base_net[symmetric]) 
      show "clmm_dsc P2" using cmb_P2 .
      show "rs1' \<le> sqp'" using True .
      show "quote_gross P2 rs1' = quote_gross P2 sqp'" using quoteq by simp
      show "0 < rs1'" using combo_joint_rest_price_pos assms by simp
    qed
  next
    case False
    show ?thesis 
    proof (rule quote_gross_equiv_base_net)
      show "clmm_dsc P2" using cmb_P2 .
      show "sqp' \<le> rs1'" using False by simp
      show "quote_gross P2 sqp' = quote_gross P2 rs1'" using quoteq by simp
      show "0 < sqp'" using combo_joint_reached_price_pos assms by simp
    qed
  qed
qed

lemma quote_gross_price_eq1:
  assumes "y1 = quote_gross P1 sqp' - quote_gross P1 sqp1"
  and "rs1 = quote_reach P1 (y1 + quote_gross P1 sqp1)"
shows "quote_gross P1 rs1 = y1 + quote_gross P1 sqp1" 
    using clmm_quote_gross_reach_eq
    by (simp add: assms clmm_quote_gross_pos quote_gross_grd_max_max 
        cmb_P1 cmb_nz1)

lemma quote_gross_price_eq2:
  assumes "0 \<le> y2"
  and "y2 + quote_gross P1 sqp1 \<le> quote_gross P1 (grd_max P1)"
  and "rs2 = quote_reach P1 (y2 + quote_gross P1 sqp1)"
shows "quote_gross P1 rs2 = y2 + quote_gross P1 sqp1" 
  using clmm_quote_gross_reach_eq
  by (simp add: assms clmm_quote_gross_pos cmb_P1 cmb_nz1)

end

subsection \<open>Optimality result on quote tokens\<close>

text \<open>When the fees in two pools are constant and equal, swapping a given amount
of quote tokens in their combination permits to determine the optimal quantities
of quote tokens to swap in each individual pool.\<close>

locale combined_pools_cst_fee = combined_pools +
  fixes phi
  assumes fee1: "\<forall>i. fee P1 i = phi"
  and fee2: "\<forall>i. fee P2 i = phi"

begin

lemma fee_props:
  shows "0 \<le> phi" "phi < 1" using cmb_P1 clmm_dsc_fees[of P1] fee1 by auto

lemma quote_swap_opt_above:
  assumes "0 < y"
  and "grd_min P1 \<le> sqp1"
  and "y + quote_gross P sqp1 \<le> quote_gross P (grd_max P)"
  and "sqp' = quote_reach P (y + quote_gross P sqp1)"
  and "y1 = quote_gross P1 sqp' - quote_gross P1 sqp1"
  and "sqp1 \<le> sqp2"
  and "0 \<le> y2"
  and "y - y2 + quote_gross P2 sqp2 \<le> quote_gross P2 (grd_max P2)"
  and "y2 < y1"
  and "y1 < y"  
shows "quote_swap P1 sqp1 y2 + quote_swap P2 sqp2 (y - y2) \<le> quote_swap P sqp1 y"
proof -
  define rs1 where "rs1 = quote_reach P1 (y1 + quote_gross P1 sqp1)"
  define rs2 where "rs2 = quote_reach P1 (y2 + quote_gross P1 sqp1)"
  define rs1' where "rs1' = quote_reach P2 (y - y1 + quote_gross P2 sqp2)"
  define rs2' where "rs2' = quote_reach P2 (y - y2 + quote_gross P2 sqp2)"  
  have q1: "quote_gross P1 rs1 = y1 + quote_gross P1 sqp1" 
    unfolding rs1_def using quote_gross_price_eq1 assms by simp
  have q2: "quote_gross P1 rs2 = y2 + quote_gross P1 sqp1" 
    unfolding rs2_def using quote_gross_price_eq2
    by (smt (verit) assms(7) assms(9) clmm_quote_gross_pos 
        quote_gross_grd_max_max cmb_P1 cmb_nz1 q1)
  have q2': "quote_gross P2 rs2' = y - y2 + quote_gross P2 sqp2" 
    unfolding rs2'_def 
    using clmm_quote_gross_reach_eq assms(8-10) 
      clmm_quote_gross_pos cmb_P2 cmb_nz2 by auto 
  have q1': "quote_gross P2 rs1' = y - y1 + quote_gross P2 sqp2"
    unfolding rs1'_def 
    using clmm_quote_gross_reach_eq assms(8-10) 
      clmm_quote_gross_pos cmb_P2 cmb_nz2 by auto 
  have primeq: "quote_gross P2 sqp' = quote_gross P2 rs1'"
    using assms comb_add_above_add_eq2 rs1'_def by simp 
  have "rs1 \<le> sqp'"  
    using assms rs1_def combo_joint_quote_gross_price_le by simp  
  have "0 < sqp'" using combo_joint_reached_price_pos assms by simp
  have "0 < grd_min P1" 
    using assms grd_min_pos liq_grd_min cmb_P1 cmb_nz1 by blast
  have "sqp1 \<le> rs1" using quote_reach_strict_mono
    by (metis assms(7) assms(9) quote_gross_imp_sqp_lt cmb_P1 
        less_add_same_cancel2 linorder_not_less nle_le order.strict_trans q1)
  hence "0 < rs1" using \<open>0 < grd_min P1\<close> assms by simp
  hence "1/sqp' \<le> 1/rs1" using \<open>rs1 \<le> sqp'\<close> \<open>0 < sqp'\<close> by (simp add: frac_le) 
  have "rs2 \<le> rs1" using assms rs2_def rs1_def comb_add_above_price1_leq by simp
  have "rs1' \<le> rs2'" 
    using assms rs1'_def rs2'_def comb_add_above_price2_geq by simp
  have "sqp' < rs2'" using assms rs2'_def comb_add_above_price2_lt by simp    
  have "(1 -phi) * (quote_gross P1 rs1 - quote_gross P1 rs2)/(rs1 * rs1) - 
      (1 - phi) * (quote_gross P2 rs2' - quote_gross P2 sqp')/(sqp' * sqp') = 
      (1 - phi) * (y1 - y2)/(rs1 * rs1) - 
      (1 - phi) * (quote_gross P2 rs2' - quote_gross P2 sqp')/(sqp' * sqp')"
    using q1 q2 by simp
  also have "... = 
      (1 - phi) * (y1 + quote_gross P1 sqp1 - (y2 + quote_gross P1 sqp1))/(rs1 * rs1) - 
      (1 - phi) * (quote_gross P2 rs2' - quote_gross P2 sqp')/(sqp' * sqp')" 
    by simp      
  also have "... = 
      (1 - phi) * (y1 - y2)/(rs1 * rs1) - 
      (1 - phi) * (quote_gross P2 rs2' - quote_gross P2 rs1')/(sqp' * sqp')"
    using primeq by simp
  also have "... = (1 - phi) * (y1 - y2)/(rs1 * rs1) - 
      (1 - phi) * (y1 - y2)/(sqp' * sqp')"
    using q1' q2' by simp
  also have "... = (1 - phi) * (y1 - y2) * (1/(rs1 * rs1) - 1/(sqp' * sqp'))"
    by (simp add: vector_space_over_itself.scale_right_diff_distrib)
  finally have "(1 -phi) * (quote_gross P1 rs1 - quote_gross P1 rs2)/(rs1 * rs1) - 
      (1 - phi) * (quote_gross P2 rs2' - quote_gross P2 sqp')/(sqp' * sqp') =
      (1 - phi) * (y1 - y2) * (1/(rs1 * rs1) - 1/(sqp' * sqp'))" .
  moreover have "0 \<le>  (1 - phi) * (y1 - y2) * (1/(rs1 * rs1) - 1/(sqp' * sqp'))" 
  proof -
    have "rs1 * rs1 \<le> sqp' * sqp'" 
      using \<open>0 < rs1\<close> \<open>rs1 \<le> sqp'\<close> by (simp add: mult_mono')
    hence "0 \<le> 1/(rs1 * rs1) - 1/(sqp' * sqp')"
      by (simp add: \<open>0 < rs1\<close> frac_le)
    thus ?thesis
      using assms(9) fee_props(2) by fastforce
  qed
  ultimately have "0 \<le> (1 -phi) * 
      (quote_gross P1 rs1 - quote_gross P1 rs2)/(rs1 * rs1) - 
      (1 - phi) * (quote_gross P2 rs2' - quote_gross P2 sqp')/(sqp' * sqp')" 
    by simp
  also have "... \<le> base_net P1 rs2 - base_net P1 rs1 -
      (1 - phi) * (quote_gross P2 rs2' - quote_gross P2 sqp')/(sqp' * sqp')" 
  proof -
    have "(1 -phi) * (quote_gross P1 rs1 - quote_gross P1 rs2)/(rs1 * rs1) \<le> 
        base_net P1 rs2 - base_net P1 rs1"
    proof (rule base_net_quote_lbound)
      show "clmm_dsc P1" using cmb_P1 .
      show "\<And>i. fee P1 i = phi" by (simp add: fee1)
      show "0 < rs2" using clmm_quote_reach_pos
        by (metis clmm_quote_gross_pos quote_gross_grd_max_max cmb_P1 
            cmb_nz1 q2 rs2_def)
      show "rs2 \<le> rs1" using \<open>rs2 \<le> rs1\<close> .
    qed
    thus ?thesis by simp
  qed
  also have "... \<le> base_net P1 rs2 - base_net P1 rs1 - 
      (base_net P2 sqp' - base_net P2 rs2')" 
  proof -
    have "base_net P2 sqp' - base_net P2 rs2' \<le> 
        (1 - phi) * (quote_gross P2 rs2' - quote_gross P2 sqp')/(sqp' * sqp')" 
    proof (rule base_net_quote_ubound)
      show "clmm_dsc P2" using cmb_P2 .
      show "phi < 1" using fee_props(2) .
      show "sqp' \<le> rs2'" using \<open>sqp' < rs2'\<close> by simp
      show "\<And>i. fee P2 i = phi" by (simp add: fee2)
      show "0 < sqp'" using \<open>0 < sqp'\<close> .
    qed
    thus ?thesis by (simp add: diff_left_mono)
  qed
  also have "... = base_net P1 rs2 - base_net P1 rs1 - 
      (base_net P2 rs1' - base_net P2 rs2')"
  proof -
    have "base_net P2 sqp' = base_net P2 rs1'"
      using assms combo_joint_base_reached_eq2 order_less_imp_le rs1'_def by blast
    thus ?thesis by simp
  qed
  also have "... = quote_swap P1 sqp1 y1 - quote_swap P1 sqp1 y2- 
      (quote_swap P2 sqp2 (y - y2) - quote_swap P2 sqp2 (y - y1))" 
    unfolding quote_swap_def rs1_def rs2_def rs1'_def rs2'_def by simp
  also have "... = quote_swap P sqp1 y - 
      (quote_swap P1 sqp1 y2 + quote_swap P2 sqp2 (y - y2))"
    using assms combo_quote_swap_eq \<open>0 < grd_min P1\<close> by simp
  finally have "0 \<le> quote_swap P sqp1 y - 
      (quote_swap P1 sqp1 y2 + quote_swap P2 sqp2 (y - y2))" .
  thus ?thesis by simp
qed

lemma quote_swap_opt_above':
  assumes "0 < y"
  and "grd_min P1 \<le> sqp1"
  and "y + quote_gross P sqp1 \<le> quote_gross P (grd_max P)"
  and "sqp' = quote_reach P (y + quote_gross P sqp1)"
  and "y1 = quote_gross P1 sqp' - quote_gross P1 sqp1"
  and "sqp1 \<le> sqp2"
  and "y2 + quote_gross P1 sqp1 \<le> quote_gross P1 (grd_max P1)"
  and "0 \<le> y - y2"
  and "y1 < y2"
  and "y2 \<le> y" 
shows "quote_swap P1 sqp1 y2 + quote_swap P2 sqp2 (y - y2) \<le> quote_swap P sqp1 y"
proof -
  define lp1 where "lp1 = quote_reach P1 (quote_gross P1 sqp1)"
  have qlp: "quote_gross P1 lp1 = quote_gross P1 sqp1"
    by (simp add: clmm_quote_gross_pos quote_gross_grd_max_max 
        clmm_quote_gross_reach_eq cmb_P1 cmb_nz1 lp1_def)
  have lpgeq: "grd_min P1 \<le> lp1"
    by (simp add: clmm_quote_gross_pos quote_gross_grd_max_max 
        clmm_quote_reach_ge cmb_P1 cmb_nz1 lp1_def) 
  define rs1 where "rs1 = quote_reach P1 (y1 + quote_gross P1 lp1)"
  define rs2 where "rs2 = quote_reach P1 (y2 + quote_gross P1 lp1)"
  define rs1' where "rs1' = quote_reach P2 (y - y1 + quote_gross P2 sqp2)"
  define rs2' where "rs2' = quote_reach P2 (y - y2 + quote_gross P2 sqp2)" 
  have "0 < grd_min P1" 
    using assms grd_min_pos liq_grd_min cmb_P1 cmb_nz1 by blast
  have q': "quote_gross P1 sqp' = y1 + quote_gross P1 sqp1" using assms by simp
  have q1: "quote_gross P1 rs1 = y1 + quote_gross P1 sqp1" 
    unfolding rs1_def using quote_gross_price_eq1 assms qlp by simp
  have q2: "quote_gross P1 rs2 = y2 + quote_gross P1 sqp1" 
    unfolding rs2_def using quote_gross_price_eq2 qlp
    by (metis \<open>0 < grd_min P1\<close> assms(1-5) assms(7) assms(9) 
        combo_joint_quote_gross_decomp(3) leD nless_le order.trans)
  have "quote_gross P1 sqp' < quote_gross P1 rs2" using q' q2 assms by simp
  have "y - y1 + quote_gross P2 sqp2 \<le> quote_gross P2 (grd_max P2)"
    using \<open>0 < grd_min P1\<close> assms(1-5) combined_pools.combo_joint_quote_gross_leq_max 
      combined_pools_axioms 
    by auto
  hence q2': "quote_gross P2 rs2' = y - y2 + quote_gross P2 sqp2" 
    unfolding rs2'_def 
    using clmm_quote_gross_reach_eq assms(8-10) 
      clmm_quote_gross_pos cmb_P2 cmb_nz2 by auto 
  have q1': "quote_gross P2 rs1' = y - y1 + quote_gross P2 sqp2"
    unfolding rs1'_def 
    using clmm_quote_gross_reach_eq assms(8-10) 
      clmm_quote_gross_pos cmb_P2 cmb_nz2
    by (simp add: \<open>y - y1 + quote_gross P2 sqp2 \<le> quote_gross P2 (grd_max P2)\<close>) 
  have quoteq: "quote_gross P2 sqp' = quote_gross P2 rs1'"
    using assms comb_add_above_add_eq2 rs1'_def by simp   
  have "rs1 \<le> sqp'"  
    using assms rs1_def combo_joint_quote_gross_price_le qlp by force
  have "rs1' \<le> sqp'" using combo_joint_quote_gross_price_le' assms rs1'_def by simp
  have "0 < sqp'" using combo_joint_reached_price_pos assms by simp
  have "0 < rs1'" using assms rs1'_def
    by (metis quote_gross_imp_sqp_lt cmb_P2 cmb_pos diff_gt_0_iff_gt 
        dual_order.strict_trans less_add_same_cancel2 order_less_le_trans q1')
  have baseq2: "base_net P2 sqp' = base_net P2 rs1'" 
    using assms combo_joint_base_reached_eq2 rs1'_def by simp
  have baseq: "base_net P1 sqp' = base_net P1 rs1" 
    using assms combo_joint_base_reached_eq rs1_def qlp by simp
  have "0 < sqp'" using clmm_quote_reach_pos
    by (metis assms(1) assms(3) assms(4) clmm_quote_gross_pos combined_P_prop 
        dual_order.trans le_add_same_cancel1 less_eq_real_def)
  have "lp1 \<le> rs1"
  proof (rule quote_reach_mono)
    show "lp1 = quote_reach P1 (quote_gross P1 sqp1)" using lp1_def by simp
    show "clmm_dsc P1" using cmb_P1 .
    show "nz_support (lq P1) \<noteq> {}" using cmb_nz1 .
    show "0 \<le> quote_gross P1 sqp1" using clmm_quote_gross_pos cmb_P1 by simp
    show "rs1 = quote_reach P1 (y1 + quote_gross P1 lp1)" using rs1_def by simp
    show "quote_gross P1 sqp1 \<le> y1 + quote_gross P1 lp1" 
      using qlp \<open>0 < grd_min P1\<close> assms combo_joint_quote_gross_decomp(3) 
      by auto
    show "y1 + quote_gross P1 lp1 \<le> quote_gross P1 (grd_max P1)" 
      using qlp assms by simp
  qed    
  hence "0 < rs1" using \<open>0 < grd_min P1\<close> assms lpgeq by simp
  hence "1/sqp' \<le> 1/rs1" using \<open>rs1 \<le> sqp'\<close> \<open>0 < sqp'\<close> by (simp add: frac_le) 
  have "rs1 \<le> rs2" using assms rs2_def rs1_def 
    by (metis add_le_cancel_right quote_gross_imp_sqp_lt cmb_P1 
        linorder_not_less order.asym q1 q2)
  have "rs2' \<le> rs1'" 
  proof (rule comb_add_above_price2_geq'[of y sqp1 sqp' y1 y2])
    have "0 \<le> y1" 
      using combo_joint_quote_gross_decomp_leq(3) assms
      by (meson \<open>0 < grd_min P1\<close> order_less_imp_le order_less_le_trans)
    thus "0 \<le> y2" using assms by simp
    show "y - y1 + quote_gross P2 sqp2 \<le> quote_gross P2 (grd_max P2)" 
      using \<open>y - y1 + quote_gross P2 sqp2 \<le> quote_gross P2 (grd_max P2)\<close> .
    show "y1 < y2" using assms by simp
    show "y2 \<le> y" using assms by simp
    show "rs1' = quote_reach P2 (y - y1 + quote_gross P2 sqp2)" 
      using rs1'_def by simp
    show "rs2' = quote_reach P2 (y - y2 + quote_gross P2 sqp2)"
      using rs2'_def by simp
  qed (simp add: assms)+
  have "0 = (1 - phi) * (y2-y1)/(sqp' * sqp') - (1 - phi) * 
      (quote_gross P1 rs2 - quote_gross P1 sqp') / (sqp' * sqp')" 
    using assms q2 by simp
  also have "... = (1 - phi) * (quote_gross P2 sqp' - quote_gross P2 rs2') /
      (sqp' * sqp') - (1 - phi) * (quote_gross P1 rs2 - quote_gross P1 sqp') / 
      (sqp' * sqp')"  
    by (simp add: quoteq q1' q2') 
  also have "... \<le> (base_net P2 rs2' - base_net P2 sqp') - (1 - phi) * 
      (quote_gross P1 rs2 - quote_gross P1 sqp') / (sqp' * sqp')"
  proof -
    have "(1 - phi) * (quote_gross P2 sqp' - quote_gross P2 rs2') / 
        (sqp' * sqp') \<le> base_net P2 rs2' - base_net P2 sqp'" 
    proof (rule base_net_quote_lbound[of P2 phi rs2' sqp'])
      show "clmm_dsc P2" using cmb_P2 .
      show "\<And>i. fee P2 i = phi" using fee2 by simp
      show "rs2' \<le> sqp'" using \<open>rs1' \<le> sqp'\<close> \<open>rs2' \<le> rs1'\<close> by simp 
      show "0 < rs2'" using clmm_quote_reach_pos 
        by (metis clmm_quote_gross_pos quote_gross_grd_max_max cmb_P2 
            cmb_nz2 q2' rs2'_def)
    qed
    thus ?thesis by simp
  qed
  also have "... \<le> (base_net P2 rs2' - base_net P2 sqp') - 
      (base_net P1 sqp' - base_net P1 rs2)"
  proof -
    have "base_net P1 sqp' - base_net P1 rs2 \<le> (1 - phi) * 
        (quote_gross P1 rs2 - quote_gross P1 sqp') / (sqp' * sqp')" 
    proof (rule base_net_quote_ubound)
      show "clmm_dsc P1" using cmb_P1 .
      show "\<And>i. fee P1 i = phi" using fee1 by simp
      show "phi < 1" using fee_props by simp
      show "0 < sqp'" using \<open>0 < sqp'\<close> . 
      show "sqp' \<le> rs2"
        using \<open>quote_gross P1 sqp' < quote_gross P1 rs2\<close> 
          quote_gross_imp_sqp_lt cmb_P1 
        by fastforce 
    qed
    thus ?thesis by simp
  qed
  also have "... = (base_net P2 rs2' - base_net P2 rs1') - 
      (base_net P1 rs1 - base_net P1 rs2)" 
    using baseq2 baseq by simp
  also have "... = base_net P1 rs2 - base_net P1 rs1 - 
      (base_net P2 rs1' - base_net P2 rs2')" 
    by simp
  also have "... = quote_swap P1 sqp1 y1 - quote_swap P1 sqp1 y2- 
      (quote_swap P2 sqp2 (y - y2) - quote_swap P2 sqp2 (y - y1))" 
    unfolding quote_swap_def rs1_def rs2_def rs1'_def rs2'_def using qlp by simp
  also have "... = quote_swap P sqp1 y - 
      (quote_swap P1 sqp1 y2 + quote_swap P2 sqp2 (y - y2))"
    using assms combo_quote_swap_eq \<open>0 < grd_min P1\<close> by simp
  finally have "0 \<le> quote_swap P sqp1 y - 
      (quote_swap P1 sqp1 y2 + quote_swap P2 sqp2 (y - y2))" .
  thus ?thesis by simp
qed

lemma combo_slice_no_addition2:
  assumes "0 < y"
  and "y + quote_gross P sqp1 \<le> quote_gross P (grd_max P)"
  and "sqp' = quote_reach P (y + quote_gross P sqp1)"
  and "y1 = quote_gross P1 sqp' - quote_gross P1 sqp1"
  and "sqp1 \<le> sqp2"
  and "y1 = y"
  and "0 \<le> y2"
  and "y2 \<le> y"
  and "y - y2 + quote_gross P2 sqp2 \<le> quote_gross P2 (grd_max P2)"
  and "y1 \<noteq> y2"
  and "P'' = slice_pool P2 sqp2"
shows "quote_gross P'' sqp' = 0"
proof -
  have "y1 + quote_gross P1 sqp1 = y + quote_gross P sqp1"
  proof -
    have "quote_gross P sqp1 = quote_gross P1 sqp1" 
    proof (rule combo_quote_init1)
      show "clmm_dsc P1" using cmb_P1 .
      show "clmm_dsc P2" using cmb_P2 .
      show "grd P1 = grd P2" by (simp add: cmb_grd_eq) 
      show "0 < sqp2" by (simp add: cmb_pos) 
      show "grd P1 (lower_tick P1 sqp2) = sqp2" by (simp add: cmb_on_grid) 
      show "P = pool_comb P1 P2 sqp2" by (simp add: cmb_comb) 
      show "0 < y" using assms by simp
      show "y + quote_gross P sqp1 \<le> quote_gross P (grd_max P)" using assms by simp
      show "nz_support (lq P1) \<noteq> {}" using cmb_nz1 . 
      show "nz_support (lq P2) \<noteq> {}" using cmb_nz2 . 
      show "sqp' = quote_reach P (y + quote_gross P sqp1)" using assms by simp
      show "sqp1 \<le> sqp2" using assms by simp
      show "sqp2 < grd_max P2" by (simp add: cmb_max)
    qed
    thus ?thesis using assms by simp
  qed
  also have "... = quote_gross P sqp'" 
    using clmm_quote_gross_reach_eq assms clmm_quote_gross_pos combined_P_prop 
    by auto 
  also have "... = quote_gross P1 sqp' + quote_gross P'' sqp'"
    using pool_comb_quote_decomp cmb_P1 cmb_P2 cmb_comb cmb_grd_eq assms cmb_pos
      cmb_on_grid pool_comb_joint_refined quote_gross_join slice_pool_clmm_dsc 
    by presburger
  also have "... = y1 + quote_gross P1 sqp1 + quote_gross P'' sqp'" 
    using assms by simp
  finally have "y1 + quote_gross P1 sqp1 = 
      y1 + quote_gross P1 sqp1 + quote_gross P'' sqp'" .
  thus "quote_gross P'' sqp' = 0" by simp
qed

lemma quote_swap_opt_below:
  assumes "0 < y"
  and "grd_min P1 \<le> sqp1"
  and "y + quote_gross P sqp1 \<le> quote_gross P (grd_max P)"
  and "sqp' = quote_reach P (y + quote_gross P sqp1)"
  and "y1 = quote_gross P1 sqp' - quote_gross P1 sqp1"
  and "sqp1 \<le> sqp2"
  and "y1 = y"
  and "0 \<le> y2"
  and "y2 \<le> y"
  and "y - y2 + quote_gross P2 sqp2 \<le> quote_gross P2 (grd_max P2)"
  and "y1 \<noteq> y2"
shows "quote_swap P1 sqp1 y2 + quote_swap P2 sqp2 (y - y2) \<le> quote_swap P sqp1 y"
proof -
  define P'' where "P'' = slice_pool P2 sqp2"
  have "y2 < y1" using assms by simp
  define lp1 where "lp1 = quote_reach P1 (quote_gross P1 sqp1)"
  have qlp: "quote_gross P1 lp1 = quote_gross P1 sqp1"
    by (simp add: clmm_quote_gross_pos quote_gross_grd_max_max 
        clmm_quote_gross_reach_eq cmb_P1 cmb_nz1 lp1_def)
  have lpgeq: "grd_min P1 \<le> lp1"
    by (simp add: clmm_quote_gross_pos quote_gross_grd_max_max 
        clmm_quote_reach_ge cmb_P1 cmb_nz1 lp1_def) 
  define rs1 where "rs1 = quote_reach P1 (y1 + quote_gross P1 lp1)"
  define rs2 where "rs2 = quote_reach P1 (y2 + quote_gross P1 lp1)"
  define rs1' where "rs1' = quote_reach P2 (y - y1 + quote_gross P2 sqp2)"
  define rs2' where "rs2' = quote_reach P2 (y - y2 + quote_gross P2 sqp2)"
  define rs3' where "rs3' = quote_reach P'' (y - y2)"
  have "0 < grd_min P1" 
    using assms grd_min_pos liq_grd_min cmb_P1 cmb_nz1 by blast
  have q': "quote_gross P1 sqp' = y1 + quote_gross P1 sqp1" using assms by simp
  have q1: "quote_gross P1 rs1 = y1 + quote_gross P1 sqp1" 
    unfolding rs1_def using quote_gross_price_eq1 assms qlp by metis
  have q2: "quote_gross P1 rs2 = y2 + quote_gross P1 lp1" 
    unfolding rs2_def using clmm_quote_gross_reach_eq
    by (smt (z3) assms(7-9) clmm_quote_gross_pos quote_gross_grd_max_max 
        cmb_P1 cmb_nz1 q1 qlp)   
  have q2': "quote_gross P2 rs2' = y - y2 + quote_gross P2 sqp2" 
    unfolding rs2'_def 
    using clmm_quote_gross_reach_eq assms(8-10) 
      clmm_quote_gross_pos cmb_P2 cmb_nz2 by auto 
  have q1': "quote_gross P2 rs1' = y - y1 + quote_gross P2 sqp2"
    unfolding rs1'_def 
    using clmm_quote_gross_reach_eq assms(7-10) 
      clmm_quote_gross_pos cmb_P2 cmb_nz2 by auto   
  have "rs1 \<le> sqp'"  
    using assms rs1_def combo_joint_quote_gross_price_le eq_diff_eq' qlp by simp  
  have "0 < sqp'" using combo_joint_reached_price_pos assms by simp
  have "0 < grd_min P1" 
    using assms grd_min_pos liq_grd_min cmb_P1 cmb_nz1 by blast
  have "sqp1 < rs1" using quote_reach_strict_mono
    by (metis assms(1) assms(5) assms(7) quote_gross_imp_sqp_lt cmb_P1 
        diff_gt_0_iff_gt q' q1)
  hence "0 < rs1" using \<open>0 < grd_min P1\<close> assms by simp
  hence "1/sqp' \<le> 1/rs1" using \<open>rs1 \<le> sqp'\<close> \<open>0 < sqp'\<close> by (simp add: frac_le) 
  have "rs2 \<le> rs1" using assms rs2_def rs1_def \<open>y2 < y1\<close>
    by (smt (verit) quote_gross_imp_sqp_lt cmb_P1 q1 q2 qlp) 
  have "quote_gross P2 sqp2 < quote_gross P2 rs2'" 
    using q2' \<open>y2 < y1\<close> assms(7) by simp
  hence "sqp2 < rs2'" using quote_gross_imp_sqp_lt cmb_P2 by blast 
  have "quote_gross P'' sqp' = 0" 
    using assms P''_def combined_pools_cst_fee.combo_slice_no_addition2 
      combined_pools_cst_fee_axioms 
    by simp
  have "quote_gross P'' sqp2 = 0" using P''_def slice_pool_quote_gross
    by (simp add: cmb_P2 cmb_pos)
  have q3': "quote_gross P'' rs3' = y - y2" unfolding rs3'_def 
  proof (rule clmm_quote_gross_reach_eq)
    show "clmm_dsc P''" using P''_def cmb_P2 slice_pool_clmm_dsc cmb_pos by simp
    show "nz_support (lq P'') \<noteq> {}"
      using P''_def cmb_P2 cmb_max cmb_nz2 cmb_pos slice_pool_nz_liq' by auto
    have "quote_gross P'' (grd_max P'') = 
        quote_gross P2 (grd_max P2) - quote_gross P2 sqp2"
      using slice_pool_quote_gross_max_eq
      by (metis P''_def cmb_P2 cmb_grd_eq cmb_max cmb_nz2 cmb_on_grid cmb_pos 
          lower_tick_eq)
    thus "y - y2 \<le> quote_gross P'' (grd_max P'')" using assms by simp
    show "0 \<le> y - y2" using assms by simp
  qed
  hence "quote_gross P'' sqp' < quote_gross P'' rs3'" 
    using \<open>quote_gross P'' sqp' = 0\<close> assms by simp
  hence "sqp' < rs3'"
    using P''_def quote_gross_imp_sqp_lt cmb_P2 slice_pool_clmm_dsc cmb_pos 
    by blast 
  have "rs1 \<le> sqp'" using \<open>rs1 \<le> sqp'\<close> by simp
  hence "0 \<le> (1 - phi) * (y1-y2) * (1/(rs1 * rs1) - 1/(sqp' * sqp'))"
  proof -
    have f1: "0 \<le> 1 - phi"
      using fee_props(2) by force
    have f2: "0 \<le> rs1"
      using \<open>0 < rs1\<close> by linarith
    have "0 \<le> sqp'"
      using \<open>0 < sqp'\<close> by linarith
    then have "0 \<le> 1 / (rs1 * rs1) - 1 / (sqp' * sqp')"
      using f2 by (simp add: \<open>0 < rs1\<close> \<open>rs1 \<le> sqp'\<close> frac_le mult_mono)
    then show ?thesis
      using f1 \<open>y2 < y1\<close> by force
  qed
  also have "... =  (1 - phi) * (y1-y2)/(rs1 * rs1) - (1 - phi) * 
      (y1-y2) / (sqp' * sqp')"
    by (simp add: right_diff_distrib)
  also have "... = (1 - phi) * (quote_gross P1 rs1 - quote_gross P1 rs2) /
      (rs1 * rs1) - (1 - phi) * (quote_gross P'' rs3' - quote_gross P'' sqp') / 
      (sqp' * sqp')" 
    using q1 q2 qlp q3' assms \<open>quote_gross P'' sqp' = 0\<close> by simp
  also have "... \<le> (base_net P1 rs2 - base_net P1 rs1) - (1 - phi) * 
      (quote_gross P'' rs3' - quote_gross P'' sqp') / (sqp' * sqp')"
  proof -
    have "(1 - phi) * (quote_gross P1 rs1 - quote_gross P1 rs2) / 
        (rs1 * rs1) \<le> base_net P1 rs2 - base_net P1 rs1" 
    proof (rule base_net_quote_lbound)
      show "clmm_dsc P1" using cmb_P1 .
      show "\<And>i. fee P1 i = phi" using fee1 by simp
      show "rs2 \<le> rs1" using \<open>rs2 \<le> rs1\<close> . 
      show "0 < rs2" using clmm_quote_reach_pos
        by (metis clmm_quote_gross_pos quote_gross_grd_max_max 
            cmb_P1 cmb_nz1 q2 rs2_def) 
    qed
    thus ?thesis by simp
  qed
  also have "... \<le> (base_net P1 rs2 - base_net P1 rs1) - 
      (base_net P'' sqp' - base_net P'' rs3')"
  proof -
    have "base_net P'' sqp' - base_net P'' rs3' \<le> (1 - phi) * 
        (quote_gross P'' rs3' - quote_gross P'' sqp') / (sqp' * sqp')" 
    proof (rule base_net_quote_ubound)
      show "clmm_dsc P''" using cmb_P2 P''_def slice_pool_clmm_dsc cmb_pos by simp
      show "\<And>i. fee P'' i = phi" 
        using fee2 slice_pool_cst_fees P''_def cmb_P2 by simp
      show "phi < 1" using fee_props by simp
      show "0 < sqp'" using \<open>0 < sqp'\<close> . 
      show "sqp' \<le> rs3'" using \<open>sqp' < rs3'\<close> by simp
    qed
    thus ?thesis by simp
  qed
  also have "... = (base_net P1 rs2 - base_net P1 rs1) - 
      (base_net P'' sqp2 - base_net P'' rs3')"
  proof -
    have "base_net P'' sqp' = base_net P'' sqp2"
    proof (rule quote_gross_equiv_base_net')
      show "clmm_dsc P''" 
        using P''_def cmb_P2 slice_pool_clmm_dsc cmb_pos by simp
      show "quote_gross P'' sqp' = quote_gross P'' sqp2"
        by (simp add: \<open>quote_gross P'' sqp' = 0\<close> \<open>quote_gross P'' sqp2 = 0\<close>)
      show "0 < sqp2" by (simp add: cmb_pos) 
      show "0 < sqp'" using \<open>0 < sqp'\<close> .
    qed    
    thus ?thesis by simp
  qed
  also have "... = quote_swap P1 sqp1 y1 - quote_swap P1 sqp1 y2- 
      (base_net P'' sqp2 - base_net P'' rs3')"
    unfolding quote_swap_def rs1_def rs2_def using qlp by simp
  also have "... = quote_swap P1 sqp1 y1 - quote_swap P1 sqp1 y2- 
      (quote_swap P'' sqp2 (y - y2) - quote_swap P'' sqp2 (y - y1))" 
  proof -
    have "base_net P'' sqp2 = base_net P'' 
        (quote_reach P'' (y - y1 + quote_gross P'' sqp2))"
    proof (rule quote_gross_equiv_base_net')
      show "clmm_dsc P''" 
        using P''_def cmb_P2 slice_pool_clmm_dsc cmb_pos by simp
      show "0 < sqp2" by (simp add: cmb_pos) 
      have "y - y1 + quote_gross P'' sqp2 = 0"
        by (simp add: \<open>quote_gross P'' sqp2 = 0\<close> assms(7)) 
      hence "quote_reach P'' (y - y1 + quote_gross P'' sqp2) = grd_min P''"
        using clmm_quote_reach_zero
        by (metis P''_def cmb_P2 cmb_max cmb_nz2 cmb_pos slice_pool_clmm_dsc 
            slice_pool_nz_liq')
      moreover have "0 < grd_min P''" using grd_min_pos
        by (metis P''_def \<open>clmm_dsc P''\<close> liq_grd_min cmb_P2 cmb_max cmb_nz2 
            cmb_pos slice_pool_nz_liq')
      ultimately show "0 < quote_reach P'' (y - y1 + quote_gross P'' sqp2)"
        by simp
      have "quote_gross P'' (quote_reach P'' (y - y1 + quote_gross P'' sqp2)) = 0"
        using \<open>quote_reach P'' (y - y1 + quote_gross P'' sqp2) = grd_min P''\<close>
          \<open>0 < quote_reach P'' (y - y1 + quote_gross P'' sqp2)\<close> \<open>clmm_dsc P''\<close> 
          clmm_quote_gross_grd_min_le 
        by auto
      thus "quote_gross P'' sqp2 = 
          quote_gross P'' (quote_reach P'' (y - y1 + quote_gross P'' sqp2))"
        using \<open>quote_gross P'' sqp2 = 0\<close> by simp
    qed
    hence "base_net P'' sqp2 - base_net P'' rs3' = 
        quote_swap P'' sqp2 (y - y2) - quote_swap P'' sqp2 (y - y1)"
      unfolding quote_swap_def  rs3'_def using \<open>quote_gross P'' sqp2 = 0\<close> by simp
    thus ?thesis by simp
  qed
  also have "... = quote_swap P1 sqp1 y1 - quote_swap P1 sqp1 y2- 
      (quote_swap P'' sqp2 (y - y2))"
  proof -
    have "quote_swap P'' sqp2 (y - y1) = 0" 
      using quote_swap_zero assms P''_def cmb_P2 cmb_max cmb_nz2 cmb_pos 
        slice_pool_clmm_dsc slice_pool_nz_liq' slice_pool_grd_max' 
      by auto
    thus ?thesis by simp
  qed
  also have "... = quote_swap P sqp1 y - 
      (quote_swap P1 sqp1 y2 + quote_swap P'' sqp2 (y - y2))"
  proof -
    have "quote_swap P sqp1 y =  quote_swap P1 sqp1 y1 + 
        quote_swap P'' sqp1 (y - y1)"
      using assms combo_quote_swap_slice_eq \<open>0 < grd_min P1\<close> P''_def by simp
    moreover have "quote_swap P'' sqp1 (y - y1) = 0"
      using quote_swap_zero assms P''_def cmb_P2 cmb_max cmb_nz2 cmb_pos 
        slice_pool_clmm_dsc slice_pool_nz_liq' slice_pool_grd_max' \<open>0 < grd_min P1\<close>
      by auto
    ultimately show ?thesis by simp
  qed
  finally have "0 \<le> quote_swap P sqp1 y - 
      (quote_swap P1 sqp1 y2 + quote_swap P'' sqp2 (y - y2))" .
  moreover have "quote_swap P'' sqp2 (y - y2) = quote_swap P2 sqp2 (y - y2)"
    using assms P''_def slice_pool_quote_swap_gt_zero
    by (smt (z3) cmb_P2 cmb_grd_eq cmb_nz2 cmb_on_grid cmb_pos grd_lower_tick_cong) 
  ultimately show ?thesis by simp
qed

lemma quote_swap_optimum':
  assumes "0 < y"
  and "grd_min P1 \<le> sqp1"
  and "y + quote_gross P sqp1 \<le> quote_gross P (grd_max P)"
  and "sqp' = quote_reach P (y + quote_gross P sqp1)"
  and "y1 = quote_gross P1 sqp' - quote_gross P1 sqp1"
  and "sqp1 \<le> sqp2"
  and "0 \<le> y2"
  and "y2 \<le> y"
  and "y2 + quote_gross P1 sqp1 \<le> quote_gross P1 (grd_max P1)"
  and "y - y2 + quote_gross P2 sqp2 \<le> quote_gross P2 (grd_max P2)"
  and "y1 \<noteq> y2"
shows "quote_swap P1 sqp1 y2 + quote_swap P2 sqp2 (y - y2) \<le> quote_swap P sqp1 y"
proof (cases "y = y1")
  case True
  then show ?thesis using quote_swap_opt_below assms by simp
next
  case False
  have "y1 \<le> y" 
  proof (rule combo_joint_quote_gross_decomp_leq(2))
    show "0 < sqp1" using assms grd_min_pos cmb_P1 cmb_nz1 by fastforce
  qed (simp add: assms)+
  hence "y1 < y" using False by simp
  show ?thesis
  proof (cases "y2 < y1")
    case True
    show ?thesis 
    proof (rule quote_swap_opt_above)
      show "y2 < y1" using True .
      show "y1 < y" using \<open>y1 < y\<close> .
    qed (auto simp add: assms)
  next
    case False
    hence "y1 < y2" using assms by simp
    show ?thesis 
    proof (rule quote_swap_opt_above')
      show "y1 < y2" using \<open>y1 < y2\<close> .
    qed (auto simp add: assms)
  qed
qed

lemma quote_swap_optimum:
  assumes "0 < y"
  and "0 < sqp1"
  and "y + quote_gross P sqp1 \<le> quote_gross P (grd_max P)"
  and "sqp' = quote_reach P (y + quote_gross P sqp1)"
  and "y1 = quote_gross P1 sqp' - quote_gross P1 sqp1"
  and "sqp1 \<le> sqp2"
  and "grd_min P1 \<le> sqp2"
  and "0 \<le> y2"
  and "y2 \<le> y"
  and "y2 + quote_gross P1 sqp1 \<le> quote_gross P1 (grd_max P1)"
  and "y - y2 + quote_gross P2 sqp2 \<le> quote_gross P2 (grd_max P2)"
  and "y1 \<noteq> y2"
shows "quote_swap P1 sqp1 y2 + quote_swap P2 sqp2 (y - y2) \<le> quote_swap P sqp1 y"
proof (cases "grd_min P1 \<le> sqp1")
  case True
  then show ?thesis using quote_swap_optimum' assms by simp
next
  case False
  hence q1: "quote_gross P1 sqp1 = quote_gross P1 (grd_min P1)"
    using assms(2) clmm_quote_gross_grd_min_le cmb_P1 by auto
  have "grd_min P = grd_min P1" 
    using pool_comb_le_grd_min by (simp add: assms(7) cmb_props)
  hence q: "quote_gross P sqp1 = quote_gross P (grd_min P1)"
    using False assms(2) clmm_quote_gross_grd_min_le combined_P_prop(1) by auto
  have "quote_swap P1 sqp1 y2 + quote_swap P2 sqp2 (y - y2) =
      quote_swap P1 (grd_min P1) y2 + quote_swap P2 sqp2 (y - y2)"
    using quote_swap_grd_min False assms(2) cmb_P1 cmb_nz1 by simp
  also have "... \<le> quote_swap P (grd_min P1) y" using quote_swap_optimum'
    by (metis q1 q assms(1) assms(7-12) assms(3-5) order_refl)
  also have "... = quote_swap P sqp1 y" 
    using quote_swap_grd_min \<open>grd_min P = grd_min P1\<close> False assms(2) 
      combined_P_prop 
    by simp
  finally show ?thesis .
qed

end

end
