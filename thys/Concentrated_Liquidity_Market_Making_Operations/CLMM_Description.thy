theory CLMM_Description imports Grid_Information

(* Author: Mnacho Echenim. Grenoble INP - UGA, Kaiko *)
(* This research is part of the ANR project BlockFI - 2024-CES38 *)


begin
section \<open>CLMM description\<close>

text \<open>Definition of CLMMs (Concentrated Liquidity Market Makers)\<close>

subsection \<open>Preliminary results\<close>

definition clmm_dsc where
"clmm_dsc P \<longleftrightarrow> (span_grid P) \<and> (finite_liq P) \<and> (\<forall>i. 0 \<le> lq P i) \<and>
  (\<forall>i. 0 \<le> fee P i) \<and> (\<forall>i. fee P i < 1)"

lemma clmm_dscI[intro]:
  assumes "span_grid P"
  and "finite_liq P"
  and "\<forall>i. 0 \<le> lq P i" 
  and "\<forall>i. 0 \<le> fee P i"
  and "\<forall>i. fee P i < 1"
shows "clmm_dsc P" using assms unfolding clmm_dsc_def by simp

lemma clmm_dsc_span_grid:
  assumes "clmm_dsc P"
  shows "span_grid P" using assms unfolding clmm_dsc_def by simp

lemma clmm_dsc_grid[simp]:
  assumes "clmm_dsc P" 
  shows "strict_mono (grd P)" "(\<forall>i. 0 < grd P i)" 
    "(\<forall>r>0. \<exists>i. grd P i < r)" "(\<forall>r. \<exists>i. r < grd P i)" 
  using assms unfolding clmm_dsc_def span_grid_def by simp+

lemma clmm_dsc_grd_Suc:
  assumes "clmm_dsc P"
  shows "grd P i < grd P (i+1)" using assms clmm_dsc_grid(1) strict_mono_def
  by (simp add: strict_mono_less)

lemma clmm_dsc_grd_smono:
  assumes "clmm_dsc P"
  and "i < j"
  shows "grd P i < grd P j" using assms clmm_dsc_grid(1)
  by (simp add: strict_monoD) 

lemma clmm_dsc_grd_mono:
  assumes "clmm_dsc P"
  and "i \<le> j"
  shows "grd P i \<le> grd P j" using assms clmm_dsc_grd_smono
  by (metis linorder_not_less nle_le)

lemma clmm_dsc_liq:
  assumes "clmm_dsc P" 
  shows "finite_liq P" "0 \<le> lq P i" using assms unfolding clmm_dsc_def by simp+

lemma clmm_dsc_fees:
  assumes "clmm_dsc P" 
  shows "(\<forall>i. 0 \<le> fee P i) \<and> (\<forall>i. fee P i < 1)" using assms 
  unfolding clmm_dsc_def by simp

lemma clmm_dsc_fees_neq_1:
  assumes "clmm_dsc P"
  shows "\<forall>i. fee P i \<noteq> 1"
      by (metis assms clmm_dsc_def less_numeral_extra(4))

lemma clmm_dsc_gross_liq:
  assumes "clmm_dsc P"
  shows "nz_support (gross_fct (lq P) (fee P)) = nz_support (lq P)"
    using gross_nz_support_eq clmm_dsc_fees assms
    by (metis less_numeral_extra(4))

lemma clmm_dsc_gross_liq_zero_iff:
  assumes "clmm_dsc P"
  shows "(lq P i = 0) \<longleftrightarrow> (gross_fct (lq P) (fee P) i = 0)"
  by (simp add: assms clmm_dsc_fees_neq_1 gross_fct_nz_eq)

lemma gross_liq_gt:
  assumes "clmm_dsc P"
  and "lq P i \<noteq> 0"
  and "L = gross_fct (lq P) (fee P)"
shows "0 < L i" using assms
  by (metis clmm_dsc_fees clmm_dsc_liq(2) dual_order.irrefl 
      gross_fct_nz_eq gross_fct_sgn order.order_iff_strict)

lemma gross_liq_ge:
  assumes "clmm_dsc P"
  and "L = gross_fct (lq P) (fee P)"
shows "0 \<le> L i" using assms
  by (meson clmm_dsc_fees clmm_dsc_liq(2) gross_fct_sgn)

lemma rng_quote_net_ge:
  assumes "clmm_dsc P"
  shows "0 \<le> lq P i * (grd P (i+1) - grd P i)"
  by (simp add: assms clmm_dsc_grd_mono clmm_dsc_liq(2))

lemma rng_quote_gross_ge:
  assumes "clmm_dsc P"
  and "L = gross_fct (lq P) (fee P)"
  shows "0 \<le> L i * (grd P (i+1) - grd P i)"
  using assms clmm_dsc_grd_mono gross_liq_ge by auto

lemma clmm_quote_gross_pos:
  assumes "clmm_dsc P"
shows "0 \<le> quote_gross P sqp" using quote_gross_pos assms
  by (meson clmm_dsc_fees clmm_dsc_grd_mono clmm_dsc_liq(2) gross_fct_sgn 
      zle_add1_eq_le zless_add1_eq)
  
lemma clmm_quote_gross_mono:
  assumes "clmm_dsc P"
  shows "mono (quote_gross P)"
proof -
  interpret finite_liq_pool P
    by (simp add: assms clmm_dsc_liq(1) finite_liq_pool_def)
  show ?thesis 
  proof (rule quote_gross_mono_finite)
    show "\<forall>i. 0 \<le> lq P i" using assms clmm_dsc_liq by simp
    show "\<forall>i. fee P i < 1" using assms clmm_dsc_fees by simp
    show "\<forall>i. grd P i \<le> grd P (i + 1)" using assms clmm_dsc_grid span_gridD
      by (simp add: strict_mono_leD)
  qed
qed

lemma quote_gross_imp_sqp_lt:
  assumes "clmm_dsc P"
  and "quote_gross P sqp < quote_gross P sqp'"
shows "sqp < sqp'"
  using assms clmm_quote_gross_mono mono_strict_invE by blast

lemma clmm_quote_net_mono:
  assumes "clmm_dsc P"
  shows "mono (quote_net P)"
proof -
  interpret finite_liq_pool P
    by (simp add: assms clmm_dsc_liq(1) finite_liq_pool_def)
  show ?thesis 
  proof (rule quote_net_mono_finite_liq)
    show "\<forall>i. 0 \<le> lq P i" using assms clmm_dsc_liq by simp
    show "\<forall>i. fee P i < 1" using assms clmm_dsc_fees by simp
    show "\<forall>i. grd P i \<le> grd P (i + 1)" using assms clmm_dsc_grid span_gridD
      by (simp add: strict_mono_leD)
  qed
qed

lemma clmm_base_gross_antimono:
  assumes "clmm_dsc P"
  shows "antimono (base_gross P)"
proof -
  interpret finite_liq_pool P
    by (simp add: assms clmm_dsc_liq(1) finite_liq_pool_def)
  show ?thesis 
  proof (rule base_gross_antimono_finite)
    show "\<forall>i. 0 \<le> lq P i" using assms clmm_dsc_liq by simp
    show "\<forall>i. fee P i < 1" using assms clmm_dsc_fees by simp
    show "\<forall>i. grd P i \<le> grd P (i + 1)" using assms clmm_dsc_grid span_gridD
      by (simp add: strict_mono_leD)
    show "\<forall>i. 0 < grd P i" using assms clmm_dsc_grid span_gridD by simp
  qed
qed

lemma clmm_base_net_antimono:
  assumes "clmm_dsc P"
  shows "antimono (base_net P)"
proof -
  interpret finite_liq_pool P
    by (simp add: assms clmm_dsc_liq(1) finite_liq_pool_def)
  show ?thesis 
  proof (rule base_net_antimono_finite)
    show "\<forall>i. 0 \<le> lq P i" using assms clmm_dsc_liq by simp
    show "\<forall>i. grd P i \<le> grd P (i + 1)" using assms clmm_dsc_grid span_gridD
      by (simp add: strict_mono_leD)
    show "\<forall>i. 0 < grd P i" using assms clmm_dsc_grid span_gridD by simp
  qed
qed

lemma liq_grd_min:
  assumes "clmm_dsc P"
  and "nz_support (lq P) \<noteq> {}"
shows "0 < grd_min P" using grd_min_pos assms by simp

lemma liq_grd_min_max:
  assumes "clmm_dsc P"
  and "nz_support (lq P) \<noteq> {}"
shows "grd_min P < grd_max P" 
proof -
  have "finite_liq_pool P"
    by (simp add: assms(1) clmm_dsc_liq(1) finite_liq_pool.intro)
  hence "idx_min (lq P) \<le> idx_max (lq P)" 
    using idx_min_max_finite assms clmm_dsc_def finite_liq_def by auto
  thus ?thesis using assms
    unfolding grd_min_def grd_max_def idx_min_img_def idx_max_img_def
    by (simp add: clmm_dsc_grd_smono) 
qed

definition rng_blw where
"rng_blw P prc = {i. grd P i \<le> prc}"

lemma rng_blw_mem[simp]:
  assumes "i \<in> rng_blw P prc"
  shows "grd P i \<le> prc" using assms unfolding rng_blw_def by simp

lemma rng_blw_bdd_above:
  assumes "clmm_dsc P"
  shows "bdd_above (rng_blw P prc)" unfolding rng_blw_def   
proof -
  have "span_grid P" using assms clmm_dsc_def by simp
  thus "bdd_above {i. grd P i \<le> prc}" unfolding bdd_above_def span_grid_def
    by (metis dual_order.trans less_eq_real_def mem_Collect_eq 
        strict_mono_less_eq)
qed

lemma rng_blw_ne:
  assumes "clmm_dsc P"
  and "0 < prc"
  shows "rng_blw P prc \<noteq> {}" 
proof -
  have "\<exists>i. grd P i < prc" using assms clmm_dsc_grid span_grid_def by simp
  thus ?thesis unfolding rng_blw_def using less_eq_real_def by auto 
qed

definition lower_tick where
"lower_tick P prc = Sup (rng_blw P prc)"

lemma grd_lower_tick_cong:
  assumes "grd P1 = grd P2"
  shows "lower_tick P1 sqp = lower_tick P2 sqp" 
  using assms unfolding lower_tick_def rng_blw_def by simp

lemma lower_tick_mem:
  assumes "clmm_dsc P"
  and "0 < prc"
  shows "lower_tick P prc \<in> rng_blw P prc" unfolding lower_tick_def
proof (rule int_set_bdd_above)
  show "rng_blw P prc \<noteq> {}" using rng_blw_ne assms by simp
  show "bdd_above (rng_blw P prc)" using rng_blw_bdd_above assms by simp
qed

lemma lower_tick_geq:
  assumes "clmm_dsc P"
  and "0 < prc"
shows "grd P (lower_tick P prc) \<le> prc"
  using assms lower_tick_mem unfolding rng_blw_def by simp

lemma lower_tick_geq':
  assumes "clmm_dsc P"
  and "i \<in> rng_blw P prc"
shows "i \<le> lower_tick P prc" unfolding lower_tick_def
proof (rule cSup_upper)
  show "i \<in> rng_blw P prc" using assms by simp
  show "bdd_above (rng_blw P prc)" using assms rng_blw_bdd_above by simp
qed

lemma lower_tick_ubound:
  assumes "clmm_dsc P"
  and "i = lower_tick P prc"
  shows "prc < grd P (i+1)"
proof (rule ccontr)
  assume "\<not> prc < grd P (i + 1)"
  hence "grd P (i + 1) \<le> prc" by simp
  hence "i+1 \<in> (rng_blw P prc)" unfolding rng_blw_def by auto
  hence "i+1 \<le> i" using assms lower_tick_geq' by blast
  thus False by simp
qed

lemma lower_tick_lbound:
  assumes "clmm_dsc P"
  and "0 < prc"
  and "i = lower_tick P prc"
shows "grd P i \<le> prc" unfolding lower_tick_def
proof -
  have "lower_tick P prc \<in> rng_blw P prc" unfolding lower_tick_def 
  proof (rule int_set_bdd_above(1))
    show "bdd_above (rng_blw P prc)" using assms rng_blw_bdd_above by simp
    show "rng_blw P prc \<noteq> {}" using assms rng_blw_ne by simp
  qed
  thus "grd P i \<le> prc" using assms by simp
qed

lemma lower_tick_lt:
  assumes "clmm_dsc P"
  and "0 < sqp'"
  and "i = lower_tick P sqp"
  and "j = lower_tick P sqp'"
  and "i < j"
shows "sqp < sqp'"
proof -
  have "i+1 \<le> j" using assms by simp
  have "sqp < grd P (i+1)" using assms lower_tick_ubound by simp
  also have "... \<le> grd P j" using assms clmm_dsc_grid span_gridD(1)
    by (simp add: strict_mono_less_eq)
  also have "... \<le> sqp'" using assms lower_tick_lbound by simp
  finally show ?thesis .
qed

lemma lower_tick_lt':
  assumes "clmm_dsc P"
  and "0 < sqp'"
  and "i = lower_tick P sqp"
  and "j = lower_tick P sqp'"
  and "sqp' < sqp"
  and "grd P i = sqp"
shows "j < i"
proof -
  have "j \<le> i" using assms lower_tick_lt by fastforce
  moreover have "j\<noteq> i" 
  proof (rule ccontr)
    assume "\<not> j \<noteq> i"
    hence "sqp \<le> sqp'" using assms lower_tick_lbound by blast
    thus False using assms by simp
  qed
  ultimately show ?thesis by simp
qed

lemma lower_tick_mono:
  assumes "clmm_dsc P"
  and "0 < sqp"
  and "i = lower_tick P sqp"
  and "j = lower_tick P sqp'"
  and "sqp \<le> sqp'"
shows "i \<le> j"
  using assms lower_tick_lt by fastforce

lemma lower_tick_eq:
  assumes "clmm_dsc P"
  and "grd P i = sqp"
shows "lower_tick P sqp = i" 
proof -
  define j where "j = lower_tick P sqp"
  have "i \<in> rng_blw P sqp" using assms unfolding rng_blw_def by auto
  hence "i \<le> j" using assms lower_tick_geq' unfolding j_def by simp
  moreover have "j \<le> i"
  proof (rule ccontr)
    assume "\<not> j\<le> i"
    hence "i+1 \<le> j" by simp
    have "sqp = grd P i" using assms by simp
    also have "... < grd P (i+1)" using assms clmm_dsc_grd_Suc by blast
    also have "... \<le> grd P j" 
      using \<open>i+1 \<le> j\<close> by (simp add: assms(1) clmm_dsc_grd_mono)
    also have "... \<le> sqp"
      using assms clmm_dsc_grid(2) j_def lower_tick_lbound by blast
    finally have "sqp < sqp" .
    thus False by simp
  qed
  ultimately show "j = i" by simp
qed

lemma lower_tick_charact:
  assumes "clmm_dsc P"
  and "grd P i \<le> sqp"
  and "sqp < grd P (i+1)"
shows "lower_tick P sqp = i" 
proof (rule ccontr)
  assume "lower_tick P sqp \<noteq> i"
  hence "i < lower_tick P sqp"
    by (metis assms(1,2) clmm_dsc_grid(2) lower_tick_eq lower_tick_mono 
        order_le_imp_less_or_eq)
  hence "i+1 \<le> lower_tick P sqp" by simp
  hence "grd P (i+1) \<le> grd P (lower_tick P sqp)"
    by (simp add: assms(1) clmm_dsc_grd_mono)
  also have "... \<le> sqp"
    by (meson assms(1,2) clmm_dsc_grid(2) lower_tick_lbound order_less_le_trans)
  finally have "grd P (i+1) \<le> sqp" .
  thus False using assms by simp
qed

lemma lower_tick_grd_min:
  assumes "strict_mono (grd P)"
shows "idx_min (lq P) = lower_tick P (grd_min P)"  
proof -
  define A where "A = {i. grd P i \<le> grd P (idx_min (lq P))}"
  have "idx_min (lq P) \<in> A" using A_def by simp
  moreover have "\<forall> i\<in> A. i \<le> idx_min (lq P)" unfolding A_def using assms
    by (simp add: strict_mono_less_eq)
  ultimately show ?thesis 
    unfolding A_def lower_tick_def rng_blw_def grd_min_def idx_min_img_def
    by (metis cSup_eq_maximum)
qed

lemma lower_tick_grd_max:
  assumes "strict_mono (grd P)"
  shows "idx_max (lq P) + 1 = lower_tick P (grd_max P)"  
proof -
  define A where "A = {i. grd P i \<le> grd P (idx_max (lq P) + 1)}"
  have "idx_max (lq P) + 1 \<in> A" using A_def by simp
  moreover have "\<forall> i\<in> A. i \<le> idx_max (lq P) + 1" unfolding A_def using assms
    by (simp add: strict_mono_less_eq)
  ultimately show ?thesis 
    unfolding A_def lower_tick_def rng_blw_def grd_max_def idx_max_img_def
    by (metis cSup_eq_maximum)
qed

lemma grd_max_gt_if:
  assumes "clmm_dsc P"
  and "i = lower_tick P sqp"
  and "lq P i \<noteq> 0"
shows "sqp < grd_max P"
proof -
  have fin: "finite (nz_support (lq P))"
    by (meson assms(1) clmm_dsc_liq(1) finite_liq_def)
  have "sqp < grd P (i+1)" using assms lower_tick_ubound by auto
  also have "... \<le> grd_max P"
  proof -
    have "i \<le> idx_max (lq P)" using assms
      by (simp add: fin idx_max_finite_ge)
    thus ?thesis unfolding grd_max_def idx_max_img_def
      by (simp add: assms(1) clmm_dsc_grd_mono)
  qed
  finally show ?thesis .
qed

subsection \<open>Quote token addition and withdrawal in a CLMM\<close>

lemma (in finite_nz_support) clmm_gen_quote_sum:
  assumes "clmm_dsc P"
  and "0 < sqp"
  and "j = lower_tick P sqp"
shows "gen_quote (grd P) L sqp = 
    L j * (sqp - grd P j) + 
    sum (\<lambda> i. L i * (grd P (i+1) - grd P i)) {i. L i \<noteq> 0 \<and> i < j}"
proof -
  define df where "df = gamma_min_diff (grd P)"
  define A where "A = {i. L i \<noteq> 0 \<and> i \<le> j}"
  define B where "B = {i. L i \<noteq> 0 \<and> j < i}"
  define C where "C = {i. L i \<noteq> 0 \<and> i < j}"
  have un: "{i. L i \<noteq> 0} = A \<union> B" unfolding A_def B_def by auto
  have inter: "A \<inter> B = {}" unfolding A_def B_def by auto
  have fin: "finite {i. L i \<noteq> 0}" by (metis fin_nz_sup nz_support_def)
  have "gen_quote (grd P) L sqp = 
      sum (rng_token df L sqp) {i. L i \<noteq> 0}" 
    unfolding gen_quote_def df_def using gen_token_sum by simp
  also have "... = sum (rng_token df L sqp) A + sum (rng_token df L sqp) B"
    by (metis empty_iff fin finite_Un inter sum.union_inter_neutral un)
  also have "... = sum (rng_token df L sqp) A"
  proof -
    have "\<forall> i\<in> B. rng_token df L sqp i = 0" 
    proof
      fix i
      assume "i \<in> B"
      have "grd P i < grd P (i+1)" using assms clmm_dsc_grid span_gridD
        by (simp add: strict_mono_less)
      have "j + 1 \<le> i" using \<open>i \<in> B\<close> assms unfolding B_def by simp
      hence "grd P (j +1) \<le> grd P i" 
        using assms clmm_dsc_grid span_gridD
        by (simp add: strict_mono_leD)
      hence "sqp < grd P i" using lower_tick_ubound[of P] assms
        by (metis dual_order.strict_trans nless_le)  
      hence "sqp < grd P (i+1)" using \<open>grd P i < grd P (i+1)\<close> by simp
      hence "df sqp i = 0" 
        using \<open>sqp < grd P i\<close> unfolding df_def gamma_min_diff_def by simp
      thus "rng_token df L sqp i = 0" unfolding rng_token_def by simp
    qed
    thus ?thesis by simp
  qed
  also have "... = rng_token df L sqp j + sum (rng_token df L sqp) C"
  proof (cases "j \<in> A")
    case True
    hence "A = {j} \<union> C" unfolding A_def C_def by auto
    hence "sum (rng_token df L sqp) A = sum (rng_token df L sqp) ({j} \<union> C)"
      by simp
    also have "... = sum (rng_token df L sqp) {j} + sum (rng_token df L sqp) C" 
    proof (rule sum.union_inter_neutral)
      show "finite {j}" by simp
      show "finite C" using fin C_def by simp
      show "\<forall>x\<in>{j} \<inter> C. rng_token df L sqp x = 0" using C_def by simp
    qed
    also have "... = rng_token df L sqp j + sum (rng_token df L sqp) C" by simp
    finally show ?thesis .
  next
    case False
    hence "A = C" unfolding A_def C_def using Collect_cong by fastforce
    have "L j = 0" using False A_def by auto
    hence "rng_token df L sqp j = 0" unfolding rng_token_def by simp
    then show ?thesis using \<open>A = C\<close> by simp
  qed
  also have "... = L j * (sqp - grd P j) + sum (rng_token df L sqp) C"
  proof -
    have "min sqp (grd P (j + 1)) = sqp" using assms lower_tick_ubound by simp
    moreover have "min sqp (grd P j) = grd P j" 
      using assms lower_tick_lbound by simp 
    ultimately have "rng_token df L sqp j = L j * (sqp - grd P j)" 
      unfolding rng_token_def df_def gamma_min_diff_def by simp
    thus ?thesis by simp
  qed
  also have "... = L j * (sqp - grd P j) + sum (\<lambda> i. L i * (grd P (i+1) - grd P i)) C"     
  proof -
    have "\<forall>i \<in> C. rng_token df L sqp i = L i * (grd P (i+1) - grd P i)" 
    proof
      fix i
      assume "i \<in> C"
      hence "i+1 \<le> j" unfolding C_def by auto
      hence "grd P (i+1) \<le> grd P j" using assms clmm_dsc_grid(1) strict_monoD
        by (metis linorder_le_less_linear nless_le)
      hence "grd P (i+1) \<le> sqp" using lower_tick_lbound assms by fastforce
      have "grd P i < grd P (i+1)" using assms clmm_dsc_grd_Suc by simp
      hence "grd P i \<le> sqp" using \<open>grd P (i+1) \<le> sqp\<close> by simp
      thus "rng_token df L sqp i = L i * (grd P (i+1) - grd P i)" 
        unfolding df_def rng_token_def gamma_min_diff_def 
        using \<open>grd P (i+1) \<le> sqp\<close> by simp
    qed
    hence "sum (rng_token df L sqp) C = 
        sum (\<lambda> i. L i * (grd P (i+1) - grd P i)) C"  by simp
    thus ?thesis unfolding df_def gamma_min_diff_def rng_token_def by simp
  qed
  finally show "gen_quote (grd P) L sqp =  
      L j * (sqp - grd P j) + sum (\<lambda> i. L i * (grd P (i+1) - grd P i)) C" .
qed

lemma clmm_gen_quote_grd_min:
  assumes "clmm_dsc P"
  and "nz_support L \<noteq> {}"
  and "finite (nz_support L)"
  and "nz_support L = nz_support (lq P)"
shows "gen_quote (grd P) L (grd_min P) = 0" using gen_quote_grd_min
  by (meson assms clmm_dsc_grd_mono mono_onI)

lemma (in finite_nz_support) clmm_gen_quote_grd_min_le:
  assumes "clmm_dsc P"
  and "nz_support L = nz_support (lq P)"
  and "sqp \<le> grd_min P"
  and "0 < sqp"
shows "gen_quote (grd P) L sqp = 0"
proof -
  define j where "j = lower_tick P sqp"
  hence "j \<le> idx_min (lq P)" using lower_tick_grd_min[of P] assms
    by (simp add: lower_tick_mono)
  have "gen_quote (grd P) L sqp = 
      L j * (sqp - grd P j) + 
      (\<Sum>i | L i \<noteq> 0 \<and> i < j. L i * (grd P (i + 1) - grd P i))" 
    by (rule clmm_gen_quote_sum, (auto simp add: assms j_def))
  also have "... = L j * (sqp - grd P j)"
  proof -
    have "{i. L i \<noteq> 0 \<and> i < j} = {}" 
    proof -
      have "\<forall>i < j. L i = 0" using \<open>j <= idx_min (lq P)\<close> idx_min_def
        by (metis (mono_tags, opaque_lifting) assms(2) 
            dual_order.strict_trans fin_nz_sup idx_min_finite_le nless_le)
      thus ?thesis by auto
    qed
    hence "(\<Sum>i | L i \<noteq> 0 \<and> i < j. L i * (grd P (i + 1) - grd P i)) = 0"
      by (metis sum_clauses(1))
    thus ?thesis by simp
  qed
  also have "... = 0"
  proof (cases "sqp = grd_min P")
    case True
    hence "grd P j = grd_min P" 
      using \<open>j \<le> idx_min (lq P)\<close> assms unfolding grd_min_def idx_min_img_def
      by (simp add: j_def lower_tick_eq)
    thus ?thesis using True by simp
  next
    case False
    hence "j < idx_min (lq P)" using lower_tick_lt'
      by (metis \<open>j \<le> idx_min (lq P)\<close> assms(1) assms(4) assms(3) 
          idx_min_img_def j_def leI lower_tick_lbound grd_min_def 
          verit_la_disequality)
    hence "L j = 0" unfolding idx_min_def nz_support_def
      by (metis \<open>j < idx_min (lq P)\<close> assms(2) fin_nz_sup idx_min_def 
          idx_min_finite_le leD) 
    then show ?thesis by simp
  qed
  finally show ?thesis .
qed

lemma clmm_quote_gross_sum:
  assumes "clmm_dsc P"
  and "0 < sqp"
  and "L = gross_fct (lq P) (fee P)"
  and "j = lower_tick P sqp"
shows "quote_gross P sqp = 
    L j * (sqp - grd P j) + 
    sum (\<lambda> i. L i * (grd P (i+1) - grd P i)) {i. L i \<noteq> 0 \<and> i < j}"
proof -
  interpret finite_nz_support L
    using finite_liq_pool.finite_liq_gross_fct assms
    by (metis clmm_dsc_liq(1) finite_liq_pool.intro finite_nz_support_def 
        nz_support_def)
  show ?thesis unfolding quote_gross_def using clmm_gen_quote_sum assms by simp
qed

lemma clmm_quote_gross_grd_min:
  assumes "clmm_dsc P"
  and "nz_support (lq P) \<noteq> {}"
shows "quote_gross P (grd_min P) = 0" unfolding quote_gross_def 
proof (rule clmm_gen_quote_grd_min)
  show "finite (nz_support (gross_fct (lq P) (fee P)))"
    using finite_liq_pool.finite_liq_gross_fct assms
    by (metis clmm_dsc_liq(1) finite_liq_pool.intro nz_support_def)
  show "clmm_dsc P" using assms by simp
  show "nz_support (gross_fct (lq P) (fee P)) = nz_support (lq P)"
    using clmm_dsc_gross_liq assms by simp
  thus "nz_support (gross_fct (lq P) (fee P)) \<noteq> {}" using assms by simp
qed

lemma clmm_quote_gross_grd_min_le:
  assumes "clmm_dsc P"
  and "sqp \<le> grd_min P"
  and "0 < sqp"
shows "quote_gross P sqp = 0" unfolding quote_gross_def 
proof (rule finite_nz_support.clmm_gen_quote_grd_min_le)
  show "finite_nz_support (gross_fct (lq P) (fee P))"
    using finite_liq_pool.finite_liq_gross_fct assms
    by (metis clmm_dsc_liq(1) finite_liq_pool.intro finite_nz_support_def 
        nz_support_def)
  show "clmm_dsc P" using assms by simp
  show "nz_support (gross_fct (lq P) (fee P)) = nz_support (lq P)"
    using clmm_dsc_gross_liq assms by simp
qed (simp add: assms)+

lemma clmm_quote_reach_zero:
  assumes "clmm_dsc P"
  and "nz_support (lq P) \<noteq> {}"
shows "quote_reach P 0 = grd_min P" 
  using assms clmm_quote_gross_grd_min unfolding quote_reach_def by simp

lemma clmm_quote_reach_ge:
  assumes "clmm_dsc P"
  and "nz_support (lq P) \<noteq> {}"
  and "0 \<le> y"
  and "y \<le> quote_gross P (grd_max P)"
shows "grd_min P \<le> (quote_reach P y)" 
proof  -
  interpret finite_liq_pool
    by (simp add: assms(1) clmm_dsc_liq(1) finite_liq_pool.intro) 
  show ?thesis
  proof (cases "y = 0")
    case True
    then show ?thesis using assms clmm_quote_reach_zero by simp
  next
    case False
    hence "0 < y" using assms by simp
    then show ?thesis using assms quote_reach_ge
      by (simp add: clmm_dsc_fees clmm_dsc_liq(2) grd_min_max strict_mono_mono)
  qed
qed

lemma clmm_quote_reach_pos:
  assumes "clmm_dsc P"
  and "nz_support (lq P) \<noteq> {}"
  and "0 \<le> y"
  and "y \<le> quote_gross P (grd_max P)"
  and "sqp = quote_reach P y"
shows "0 < sqp"
proof  -
  have "0 < grd_min P" by (simp add: assms liq_grd_min) 
  thus "0 < sqp" using assms clmm_quote_reach_ge by fastforce
qed

lemma clmm_quote_reach_mem:
  assumes "clmm_dsc P"
  and "0 \<le> y"
  and "y \<le> quote_gross P (grd_max P)"
  and "nz_support (lq P) \<noteq> {}"
shows "quote_reach P y \<in> quote_gross P-` {y}" 
proof -
  interpret finite_liq_pool
    by (simp add: assms(1) clmm_dsc_liq(1) finite_liq_pool.intro) 
  show ?thesis
  proof (rule quote_reach_mem)
    show "\<forall>i. 0 \<le> lq P i" using assms(1) clmm_dsc_def by simp 
    show "\<forall>i. fee P i < 1" using clmm_dsc_fees assms by simp
    show "mono (grd P)"
      by (simp add: assms(1) clmm_dsc_grd_mono monoI)
    show "0 \<le> y" using assms by simp
    show "y \<le> quote_gross P (grd_max P)" using assms by simp
  qed
qed

lemma clmm_quote_reach_le:
  assumes "clmm_dsc P"
  and "nz_support (lq P) \<noteq> {}"
  and "0 < y"
  and "sqp \<in> quote_gross P -`{y}"
  and "sqp' = quote_reach P y"
shows "sqp' \<le> sqp" 
proof -
  interpret finite_liq_pool 
    by (simp add: assms(1) clmm_dsc_liq(1) finite_liq_pool.intro)
  have qs: "quote_gross P (grd_min P) = 0" 
    using assms clmm_quote_gross_grd_min by simp
  define sqp' where "sqp' = quote_reach P y"
  define X where "X = quote_gross P -` {y}"
  hence "sqp' = Inf X" 
    using assms qs unfolding sqp'_def quote_reach_def by simp
  have "\<forall>x\<in> X. Inf X \<le> x" 
  proof
    fix x
    assume "x \<in> X"
    show "Inf X \<le> x"
    proof (rule  cInf_lower)
      show "x\<in> X" using \<open>x\<in> X\<close> .
      show "bdd_below X" 
        using assms quote_gross_bdd_below X_def clmm_quote_gross_mono qs by simp
    qed
  qed
  thus ?thesis using assms X_def \<open>sqp' = Inf X\<close> sqp'_def by auto
qed

lemma clmm_quote_net_sum:
  assumes "clmm_dsc P"
  and "0 < sqp"
  and "L = lq P"
  and "j = lower_tick P sqp"
shows "quote_net P sqp = 
    L j * (sqp - grd P j) + 
    sum (\<lambda> i. L i * (grd P (i+1) - grd P i)) {i. L i \<noteq> 0 \<and> i < j}"
proof -
  interpret finite_nz_support L
    using finite_liq_pool.finite_liq_gross_fct assms clmm_dsc_def 
      finite_liq_def finite_nz_support_def 
    by blast
  show ?thesis unfolding quote_net_def using clmm_gen_quote_sum assms by simp
qed

lemma clmm_quote_net_grd_min:
  assumes "clmm_dsc P"
  and "nz_support (lq P) \<noteq> {}"
shows "quote_net P (grd_min P) = 0" unfolding quote_net_def
proof (rule clmm_gen_quote_grd_min)
  show "finite (nz_support (lq P))" 
    using clmm_dsc_liq finite_liqD assms 
    unfolding finite_nz_support_def nz_support_def by simp
qed (auto simp add: assms)

lemma clmm_quote_gross_reach_eq:
  assumes "clmm_dsc P"
  and "nz_support (lq P) \<noteq> {}"
  and "0 \<le> y"
  and "y \<le> quote_gross P (grd_max P)"
shows "quote_gross P (quote_reach P y) = y"
proof -
  interpret finite_liq_pool
    by (simp add: assms(1) clmm_dsc_liq(1) finite_liq_pool.intro)
  show ?thesis 
  proof (rule quote_gross_reach_eq)
    show "\<forall>i. 0 \<le> lq P i" by (simp add: assms(1) clmm_dsc_liq(2))
    show "\<forall>i. fee P i < 1" by (simp add: assms(1) clmm_dsc_fees)
    show "mono (grd P)"
      by (simp add: assms(1) clmm_dsc_grd_mono monoI)
    show "0 \<le> y" using assms by simp
    show "y \<le> quote_gross P (grd_max P)" using assms by simp
  qed
qed

definition gen_quote_diff where
"gen_quote_diff P L sqp sqp' = gen_quote (grd P) L sqp' - gen_quote (grd P) L sqp"

lemma (in finite_nz_support) clmm_gen_quote_diff_eq:
  assumes "clmm_dsc P"
  and "j = lower_tick P sqp"
  and "k = lower_tick P sqp'"
  and "0 < sqp"
  and "sqp \<le> sqp'"
  and "j < k"
shows "gen_quote_diff P L sqp sqp' = L k * (sqp' - grd P k) + 
  sum (\<lambda> i. L i * (grd P (i+1) - grd P i)) {i. L i \<noteq> 0 \<and> j <i \<and> i < k} +
  L j * (grd P (j+1) - sqp)" 
proof -
  have "0 < sqp" using assms by simp
  hence "sqp < sqp'" using lower_tick_lt assms by simp
  hence "0 < sqp'" using \<open>0 < sqp\<close> by simp
  define A where "A = {i. L i \<noteq> 0 \<and> i < k}"
  define B where "B = {i. L i \<noteq> 0 \<and> i < j}"
  define C where "C = {i. L i \<noteq> 0 \<and> j \<le>i \<and> i < k}"
  define Cj where "Cj = {i. L i \<noteq> 0 \<and> j <i \<and> i < k}"
  define df where "df = (\<lambda> i. L i * (grd P (i+1) - grd P i))" 
  have "finite A"
    unfolding A_def by (metis fin_nz_sup finite_Collect_conjI nz_support_def)
  have "A = B \<union> C" using assms unfolding A_def B_def C_def by auto
  have "Cj = C - {j}" unfolding C_def Cj_def by auto
  have "gen_quote_diff P L sqp sqp' = L k * (sqp' - grd P k) + 
      sum df A - (L j * (sqp - grd P j) + sum df B)"
    using assms \<open>0 < sqp\<close> clmm_gen_quote_sum \<open>0 < sqp'\<close> 
    unfolding gen_quote_diff_def df_def A_def B_def by simp
  also have "... = L k * (sqp' - grd P k) + sum df C - L j * (sqp - grd P j)"
  proof (rule diff_sum_dcomp)
    show "finite A" using \<open>finite A\<close> .
    show "A = B \<union> C" using \<open>A = B \<union> C\<close> .
    show "B \<inter> C = {}" unfolding B_def C_def by auto
  qed
  also have "... =  L k * (sqp' - grd P k) + sum df Cj + 
      df j - L j * (sqp - grd P j)"
  proof (cases "j \<in> C")
    case True
    have "sum df C = df j + sum df Cj"
    proof (rule sum_remove_el)
      show "finite C" using \<open>A = B \<union> C\<close> \<open>finite A\<close> by simp
      show "j \<in> C" using True .
      show "Cj = C - {j}" using \<open>Cj = C - {j}\<close> .
    qed
    then show ?thesis by simp
  next
    case False
    hence "L j = 0" using assms unfolding C_def by auto
    hence "df j = 0" unfolding df_def by simp
    moreover have "Cj = C" using False \<open>Cj = C - {j}\<close> by auto
    ultimately show ?thesis by simp
  qed
  also have "... = L k * (sqp' - grd P k) + sum df Cj +
      L j * (grd P (j+1) - sqp)"
  proof -
    have "df j - L j * (sqp - grd P j) = L j * (grd P (j+1) - sqp)" 
      unfolding df_def by (simp add: right_diff_distrib)
    thus ?thesis by simp
  qed
  finally show "gen_quote_diff P L sqp sqp' = L k * (sqp' - grd P k) + sum df Cj +
      L j * (grd P (j+1) - sqp)" .
qed

lemma (in finite_nz_support) clmm_gen_quote_diff_eq':
  assumes "clmm_dsc P"
  and "j = lower_tick P sqp"
  and "j = lower_tick P sqp'"
  and "0 < sqp"
  and "sqp \<le> sqp'"
  and "L' j = L j"
shows "gen_quote_diff P L sqp sqp' = L' j * (sqp' - sqp)" 
proof -
  have "0 < sqp" using assms liq_grd_min[of P] by simp
  hence "0 < sqp'" using assms by simp
  define A where "A = {i. L i \<noteq> 0 \<and> i < j}"
  define df where "df = (\<lambda> i. L i * (grd P (i+1) - grd P i))" 
  have "finite A"
    unfolding A_def by (metis fin_nz_sup finite_Collect_conjI nz_support_def)
  have "gen_quote_diff P L sqp sqp' = L j * (sqp' - grd P j) + 
      sum df A - (L j * (sqp - grd P j) + sum df A)"
    using assms \<open>0 < sqp\<close> clmm_gen_quote_sum \<open>0 < sqp'\<close> 
    unfolding gen_quote_diff_def df_def A_def by simp
  also have "... = L j * (sqp' - grd P j) - L j * (sqp - grd P j)" by simp
  also have "... = L j * (sqp' - sqp)"
    by (simp add: right_diff_distrib)
  finally show "gen_quote_diff P L sqp sqp' = L' j * (sqp' - sqp)" 
    using assms by simp
qed

lemma clmm_quote_gross_diff_eq:
  assumes "clmm_dsc P"
  and "L = gross_fct (lq P) (fee P)"
  and "j = lower_tick P sqp"
  and "k = lower_tick P sqp'"
  and "0 < sqp"
  and "sqp \<le> sqp'"
  and "j < k"
shows "quote_gross P sqp' - quote_gross P sqp = L k * (sqp' - grd P k) + 
  sum (\<lambda> i. L i * (grd P (i+1) - grd P i)) {i. L i \<noteq> 0 \<and> j <i \<and> i < k} +
  L j * (grd P (j+1) - sqp)" 
proof -
  interpret finite_nz_support L
    using finite_liq_pool.finite_liq_gross_fct assms
    by (metis clmm_dsc_liq(1) finite_liq_pool.intro finite_nz_support_def 
        nz_support_def)
  show ?thesis 
    using clmm_gen_quote_diff_eq assms 
    unfolding quote_gross_def gen_quote_diff_def by simp
qed

lemma clmm_rng_quote_strict_pos:
  assumes "clmm_dsc P"
  and "L = gross_fct (lq P) (fee P)"
  and "L i \<noteq> 0"
shows "0 < L i * (grd P (i+1) - grd P i)" using assms
  by (metis add_0 clmm_dsc_grd_smono gross_liq_ge less_add_one less_diff_eq 
      less_eq_real_def zero_less_mult_iff)

lemma clmm_sum_rng_quote_pos:
  assumes "clmm_dsc P"
  and "L = gross_fct (lq P) (fee P)"
shows "0 \<le> sum (\<lambda> i. L i * (grd P (i+1) - grd P i)) M" 
  using sum_nonneg rng_quote_gross_ge assms
  by (metis (mono_tags, lifting)) 

lemma clmm_sum_rng_quote_strict_pos:
  assumes "clmm_dsc P"
  and "L = gross_fct (lq P) (fee P)"
  and "L i \<noteq> 0"
  and "i \<in> M"
  and "finite M"
shows "0 < sum (\<lambda> i. L i * (grd P (i+1) - grd P i)) M"
proof (rule sum_pos2)
  show "finite M" using assms by simp
  show "i\<in> M" using assms by simp
  show "0 < L i * (grd P (i + 1) - grd P i)" 
    using assms clmm_rng_quote_strict_pos by simp
  show "\<And>i. i \<in> M \<Longrightarrow> 0 \<le> L i * (grd P (i + 1) - grd P i)" 
    using assms rng_quote_gross_ge by simp
qed

lemma clmm_quote_gross_eq_sum_only_if:
  assumes "clmm_dsc P"
  and "L = gross_fct (lq P) (fee P)"
  and "j = lower_tick P sqp"
  and "k = lower_tick P sqp'"
  and "0 < sqp"
  and "sqp \<le> sqp'"
  and "j < k"
  and "quote_gross P sqp' = quote_gross P sqp"
  and "j < i"
  and "i < k"
shows "L i = 0" 
proof (rule ccontr)
  assume "L i \<noteq> 0"
  define S where "S = L k * (sqp' - grd P k) + 
  sum (\<lambda> i. L i * (grd P (i+1) - grd P i)) {i. L i \<noteq> 0 \<and> j <i \<and> i < k} +
  L j * (grd P (j+1) - sqp)"
  have "S = quote_gross P sqp' - quote_gross P sqp" 
    unfolding S_def using clmm_quote_gross_diff_eq[OF assms(1-7)] by simp
  also have "... = 0" using assms by simp
  finally have "S = 0" .
  have "grd P k \<le> sqp'"
    using assms lower_tick_mem by auto 
  have "sqp < grd P (j+1)"
    by (metis assms(1) assms(3) lower_tick_ubound)
  have a: "0 \<le> L k * (sqp' - grd P k)" 
    using \<open>grd P k \<le> sqp'\<close> clmm_dsc_liq(2) assms
    by (simp add: gross_liq_ge)
  have b: "0 \<le> L j * (grd P (j+1) - sqp)" 
    using \<open>sqp < grd P (j+1)\<close>
    by (metis assms(1) assms(2) diff_ge_0_iff_ge gross_liq_ge less_eq_real_def 
        split_mult_pos_le)
  have c: "0 \<le> sum (\<lambda> i. L i * (grd P (i+1) - grd P i)) 
    {i. L i \<noteq> 0 \<and> j <i \<and> i < k}"
    using assms clmm_sum_rng_quote_pos by simp
  hence "sum (\<lambda> i. L i * (grd P (i+1) - grd P i)) 
      {i. L i \<noteq> 0 \<and> j <i \<and> i < k} = 0" 
    using a b c \<open>S = 0\<close> S_def by simp
  moreover have "0 < sum (\<lambda> i. L i * (grd P (i+1) - grd P i)) 
      {i. L i \<noteq> 0 \<and> j <i \<and> i < k}"
  proof (rule clmm_sum_rng_quote_strict_pos)
    show "clmm_dsc P" using assms by simp
    show "L = gross_fct (lq P) (fee P)" using assms by simp
    show "L i \<noteq> 0" using \<open>L i \<noteq> 0\<close> .
    thus "i \<in> {i. L i \<noteq> 0 \<and> j < i \<and> i < k}" using assms by simp
    show "finite {i. L i \<noteq> 0 \<and> j < i \<and> i < k}" by simp
  qed
  ultimately show False by simp
qed

lemma clmm_quote_gross_eq_sum_emp:
  assumes "clmm_dsc P"
  and "L = gross_fct (lq P) (fee P)"
  and "j = lower_tick P sqp"
  and "k = lower_tick P sqp'"
  and "0 < sqp"
  and "sqp \<le> sqp'"
  and "j < k"
  and "quote_gross P sqp' = quote_gross P sqp"
shows "{i. L i \<noteq> 0 \<and> j <i \<and> i < k} = {}" 
proof (rule ccontr)
  assume "{i. L i \<noteq> 0 \<and> j <i \<and> i < k} \<noteq> {}"
  hence "\<exists>i. L i \<noteq> 0 \<and> j < i \<and> i < k" by auto
  from this obtain i where "L i \<noteq> 0" and "j < i" and "i < k" by auto
  hence "L i = 0" using assms clmm_quote_gross_eq_sum_only_if by simp
  thus False using \<open>L i \<noteq> 0\<close> by simp
qed

lemma clmm_quote_gross_eq_lower_only_if:
  assumes "clmm_dsc P"
  and "L = gross_fct (lq P) (fee P)"
  and "j = lower_tick P sqp"
  and "k = lower_tick P sqp'"
  and "0 < sqp"
  and "sqp \<le> sqp'"
  and "j < k"
  and "quote_gross P sqp' = quote_gross P sqp"
shows "L j = 0" 
proof (rule ccontr)
  assume "L j \<noteq> 0"
  define S where "S = L k * (sqp' - grd P k) + 
  sum (\<lambda> i. L i * (grd P (i+1) - grd P i)) {i. L i \<noteq> 0 \<and> j <i \<and> i < k} +
  L j * (grd P (j+1) - sqp)"
  have "S = quote_gross P sqp' - quote_gross P sqp" 
    unfolding S_def using clmm_quote_gross_diff_eq[OF assms(1-7)] by simp
  also have "... = 0" using assms by simp
  finally have "S = 0" .
  have "grd P k \<le> sqp'"
    using assms lower_tick_mem by auto 
  have "sqp < grd P (j+1)"
    by (metis assms(1) assms(3) lower_tick_ubound)
  have a: "0 \<le> L k * (sqp' - grd P k)" 
    using \<open>grd P k \<le> sqp'\<close> clmm_dsc_liq(2) assms
    by (simp add: gross_liq_ge)
  have b: "0 \<le> L j * (grd P (j+1) - sqp)" 
    using \<open>sqp < grd P (j+1)\<close>
    by (metis assms(1) assms(2) diff_ge_0_iff_ge gross_liq_ge less_eq_real_def 
        split_mult_pos_le)
  have c: "0 \<le> sum (\<lambda> i. L i * (grd P (i+1) - grd P i)) 
    {i. L i \<noteq> 0 \<and> j <i \<and> i < k}"
    using assms clmm_sum_rng_quote_pos by simp
  hence "L j * (grd P (j+1) - sqp) = 0" 
    using a b c \<open>S = 0\<close> S_def by linarith
  moreover have "0 < L j * (grd P (j+1) - sqp)" 
    using \<open>L j \<noteq> 0\<close> \<open>sqp < grd P (j+1)\<close> calculation by auto
  ultimately show False by linarith
qed
    
lemma clmm_quote_gross_eq_upper_only_if:
  assumes "clmm_dsc P"
  and "L = gross_fct (lq P) (fee P)"
  and "j = lower_tick P sqp"
  and "k = lower_tick P sqp'"
  and "0 < sqp"
  and "sqp \<le> sqp'"
  and "j < k"
  and "quote_gross P sqp' = quote_gross P sqp"
shows "L k = 0 \<or> grd P k = sqp'" 
proof (rule ccontr)
  assume asm: "\<not> (L k = 0 \<or> grd P k = sqp')"
  hence "L k \<noteq> 0" by simp
  have "grd P k \<noteq> sqp" using asm
    using assms lower_tick_eq by fastforce 
  define S where "S = L k * (sqp' - grd P k) + 
  sum (\<lambda> i. L i * (grd P (i+1) - grd P i)) {i. L i \<noteq> 0 \<and> j <i \<and> i < k} +
  L j * (grd P (j+1) - sqp)"
  have "S = quote_gross P sqp' - quote_gross P sqp" 
    unfolding S_def using clmm_quote_gross_diff_eq[OF assms(1-7)] by simp
  also have "... = 0" using assms by simp
  finally have "S = 0" .
  have "grd P k < sqp'"
    using assms lower_tick_mem \<open>grd P k \<noteq> sqp\<close>
    by (metis asm linorder_not_less nle_le order.trans rng_blw_mem) 
  have "sqp < grd P (j+1)"
    by (metis assms(1) assms(3) lower_tick_ubound)
  have a: "0 \<le> L k * (sqp' - grd P k)" 
    using \<open>grd P k < sqp'\<close> clmm_dsc_liq(2) assms
    by (simp add: gross_liq_ge)
  have b: "0 \<le> L j * (grd P (j+1) - sqp)" 
    using \<open>sqp < grd P (j+1)\<close>
    by (metis assms(1) assms(2) diff_ge_0_iff_ge gross_liq_ge less_eq_real_def 
        split_mult_pos_le)
  have c: "0 \<le> sum (\<lambda> i. L i * (grd P (i+1) - grd P i)) 
    {i. L i \<noteq> 0 \<and> j <i \<and> i < k}"
    using assms clmm_sum_rng_quote_pos by simp
  hence "L k * (sqp' - grd P k) = 0" 
    using a b c \<open>S = 0\<close> S_def by linarith
  moreover have "0 < L k * (sqp' - grd P k)" 
    using \<open>L k \<noteq> 0\<close> \<open>sqp < grd P (j+1)\<close> calculation asm by force
  ultimately show False by linarith
qed

lemma clmm_quote_gross_diff_eq':
  assumes "clmm_dsc P"
  and "L = gross_fct (lq P) (fee P) "
  and "j = lower_tick P sqp"
  and "j = lower_tick P sqp'"
  and "0 < sqp"
  and "sqp \<le> sqp'"
shows "quote_gross P sqp' - quote_gross P sqp = L j * (sqp' - sqp)" 
proof -
  interpret finite_nz_support L
    using finite_liq_pool.finite_liq_gross_fct assms
    by (metis clmm_dsc_liq(1) finite_liq_pool.intro finite_nz_support_def 
        nz_support_def)
  show ?thesis using clmm_gen_quote_diff_eq' assms 
    unfolding quote_gross_def gen_quote_diff_def by simp
qed
  
lemma clmm_quote_gross_eq_lower_only_if':
  assumes "clmm_dsc P"
  and "L = gross_fct (lq P) (fee P) "
  and "j = lower_tick P sqp"
  and "j = lower_tick P sqp'"
  and "0 < sqp"
  and "sqp < sqp'"
  and "quote_gross P sqp' = quote_gross P sqp"
shows "L j = 0" 
proof -
  have "L j * (sqp' - sqp) = quote_gross P sqp' - quote_gross P sqp"
    using assms clmm_quote_gross_diff_eq'[OF assms(1-4)] by simp
  also have "... = 0" using assms by simp
  finally have "L j * (sqp' - sqp) = 0" .
  thus ?thesis using assms by simp
qed

lemma clmm_quote_reach_grd_liq:
  assumes "clmm_dsc P"
  and "nz_support (lq P) \<noteq> {}"
  and "0 < y"
  and "y \<le> quote_gross P (grd_max P)"
  and "j = lower_tick P sqp"
  and "grd P j = sqp"
  and "sqp = quote_reach P y" 
shows "lq P (j - 1) \<noteq> 0"
proof (rule ccontr)
  assume "\<not> lq P (j - 1) \<noteq> 0"
  define L where "L = gross_fct (lq P) (fee P)"
  have "quote_gross P sqp = y" using assms clmm_quote_gross_reach_eq by simp
  have "quote_gross P sqp - quote_gross P (grd P (j-1)) = 
      L j * (sqp - grd P j) + 
      (\<Sum>i | L i \<noteq> 0 \<and> j - 1 < i \<and> i < j. L i * (grd P (i + 1) - grd P i)) + 
      L (j - 1) * (grd P (j - 1 + 1) - grd P (j - 1))" 
  proof (rule clmm_quote_gross_diff_eq)
    show "clmm_dsc P" using assms(1) by simp
    show "L = gross_fct (lq P) (fee P)" using L_def by simp
    show "j - 1 = lower_tick P (grd P (j - 1))" 
      using assms lower_tick_eq by presburger
    show "j = lower_tick P sqp" using assms by simp
    show "0 < grd P (j - 1)" using assms by simp
    show "j - 1 < j" by simp
    show "grd P (j - 1) \<le> sqp"
      using \<open>j - 1 < j\<close> assms(1) assms(6) clmm_dsc_grd_mono order_less_imp_le 
      by blast
  qed
  also have "... = 0" 
  proof -
    have "L j * (sqp - grd P j) = 0" using assms by simp
    moreover have "L (j - 1) * (grd P (j - 1 + 1) - grd P (j - 1)) = 0" 
      using \<open>\<not> lq P (j - 1) \<noteq> 0\<close> by (simp add: L_def gross_fct_zero_if) 
    moreover have "(\<Sum>i | L i \<noteq> 0 \<and> j - 1 < i \<and> i < j. 
        L i * (grd P (i + 1) - grd P i)) = 0"
    proof -
      have "{i. L i \<noteq> 0 \<and> j - 1 < i \<and> i < j} = {}" by auto
      thus ?thesis by (metis sum_clauses(1)) 
    qed
    ultimately show ?thesis by (simp add: assms(6)) 
  qed
  finally have "quote_gross P sqp - quote_gross P (grd P (j-1)) = 0" .
  hence "grd P (j-1) \<in> quote_gross P -`{y}"
    by (simp add: \<open>quote_gross P sqp = y\<close>)
  hence "sqp \<le> grd P (j-1)" 
    using assms clmm_quote_reach_le by simp
  moreover have "grd P (j-1) < sqp" using assms
    by (metis clmm_dsc_grd_smono order_refl zle_diff1_eq)
  ultimately show False by simp
qed

lemma quote_gross_gt_grd_min:
  assumes "clmm_dsc P"
  and "nz_support (lq P) \<noteq> {}"
  and "grd_min P < sqp"
shows "0 < quote_gross P sqp"
proof -
  define L where "L = gross_fct (lq P) (fee P)"
  define sqpm where "sqpm = grd_min P"
  define j where "j = lower_tick P (grd_min P)"
  define k where "k = lower_tick P sqp"
  have "j = idx_min (lq P)" using lower_tick_grd_min
    by (simp add: assms(1) j_def)
  have "lq P (idx_min (lq P)) \<noteq> 0"  
  proof (rule idx_min_finite_in)
    show "finite (nz_support (lq P))" 
      using assms clmm_dsc_liq(1) finite_liq_def by auto
  qed (simp add: assms)
  hence "lq P j \<noteq> 0" using \<open>j = idx_min (lq P)\<close> by simp
  hence "0 < L j" using gross_liq_gt L_def assms by simp
  show ?thesis
  proof (cases "k = j")
    case True
    have "0 < L j * (sqp - sqpm)" using \<open>0 < L j\<close> assms sqpm_def by simp
    also have "... = quote_gross P sqp - quote_gross P sqpm" 
    proof (rule clmm_quote_gross_diff_eq'[symmetric])
      show "L = gross_fct (lq P) (fee P)" using L_def by simp
      show "j = lower_tick P sqpm" using j_def sqpm_def by simp
      show "j = lower_tick P sqp" using True k_def by simp
      show "0 < sqpm" using assms unfolding sqpm_def
        by (simp add: liq_grd_min)
      show "sqpm \<le> sqp" using assms unfolding sqpm_def by simp
    qed (simp add: assms)
    also have "... = quote_gross P sqp" 
    proof -
      have "quote_gross P sqpm = 0" unfolding sqpm_def
        by (simp add: assms clmm_quote_gross_grd_min)
      thus ?thesis by simp
    qed
    finally show "0 < quote_gross P sqp" .
  next
    case False
    hence "j < k" unfolding j_def k_def
      by (metis assms(1) assms(3) clmm_dsc_grid(2) idx_min_img_def 
          lower_tick_mono nless_le grd_min_def)
    have "0 < L j * (grd P (j+1) - sqpm)"
      using \<open>0 < L j\<close> assms(1) j_def lower_tick_ubound sqpm_def by auto
    also have "... \<le> L k * (sqp - grd P k) + 
        sum (\<lambda> i. L i * (grd P (i+1) - grd P i)) {i. L i \<noteq> 0 \<and> j <i \<and> i < k} +
        L j * (grd P (j+1) - sqpm)" 
    proof -
      have "0 \<le> L k * (sqp - grd P k)" using gross_liq_ge k_def
        by (metis L_def assms(1) assms(2) assms(3) liq_grd_min 
            diff_ge_0_iff_ge  k_def lower_tick_lbound order_less_trans 
            zero_le_mult_iff)
      moreover have "0 \<le> sum (\<lambda> i. L i * (grd P (i+1) - grd P i)) 
          {i. L i \<noteq> 0 \<and> j <i \<and> i < k}"
      proof (rule sum_nonneg)
        fix n
        assume "n \<in> {i. L i \<noteq> 0 \<and> j < i \<and> i < k}"
        thus "0 \<le> L n * (grd P (n + 1) - grd P n)"
          by (simp add: L_def assms(1) rng_quote_gross_ge)
      qed
      ultimately show ?thesis by simp
    qed
    also have "... = quote_gross P sqp - quote_gross P sqpm" 
    proof (rule clmm_quote_gross_diff_eq[symmetric])
      show "clmm_dsc P" using assms by simp
      show "L = gross_fct (lq P) (fee P)" using L_def by simp
      show "j < k" using \<open>j < k\<close> .
      show "0 < sqpm" using assms sqpm_def by (simp add: liq_grd_min)
      show "sqpm \<le> sqp" using sqpm_def assms by simp
    qed (simp add: j_def k_def sqpm_def)+
    also have "... = quote_gross P sqp" 
    proof -
      have "quote_gross P sqpm = 0" unfolding sqpm_def
        by (simp add: assms clmm_quote_gross_grd_min)
      thus ?thesis by simp
    qed
    finally show "0 < quote_gross P sqp" .
  qed
qed

lemma quote_gross_pos_gt_grd_min: 
  assumes "clmm_dsc P"
  and "nz_support (lq P) \<noteq> {}"
  and "0 < quote_gross P sqp"
shows "grd_min P < sqp"
proof (rule ccontr)
  assume "\<not> grd_min P < sqp"
  hence "quote_gross P sqp = 0" using assms
    by (metis quote_gross_imp_sqp_lt clmm_quote_gross_grd_min)
  thus False using assms by simp
qed

lemma quote_gross_disj_gt:
  assumes "clmm_dsc P"
  and "i = lower_tick P sqp"
  and "j = lower_tick P sqp'"
  and "i \<le> k"
  and "k < j"
  and "lq P k \<noteq> 0"
  and "0 < sqp" 
  and "0 < sqp'"
shows "quote_gross P sqp < quote_gross P sqp'"
proof -
  define L where "L = gross_fct (lq P) (fee P)"
  hence "L k \<noteq> 0" using assms gross_liq_gt by fastforce
  have "grd P j \<le> sqp'" using assms by (simp add: lower_tick_lbound)
  have "sqp < grd P (i+1)" using assms lower_tick_ubound by simp 
  have "sqp < sqp'" using lower_tick_lt assms by simp
  hence eq: "quote_gross P sqp' - quote_gross P sqp = L j * (sqp' - grd P j) + 
      (\<Sum>n | L n \<noteq> 0 \<and> i < n \<and> n < j. L n * (grd P (n + 1) - grd P n)) +
      L i * (grd P (i + 1) - sqp)"
    using clmm_quote_gross_diff_eq assms L_def by simp
  show ?thesis
  proof (cases "k = i")
    case True
    hence "0 < L i * (grd P (i + 1) - sqp)"
      using L_def assms gross_liq_gt lower_tick_ubound by auto
    also have "... \<le> L j * (sqp' - grd P j) + 
        (\<Sum>n | L n \<noteq> 0 \<and> i < n \<and> n < j. L n * (grd P (n + 1) - grd P n)) +
        L i * (grd P (i + 1) - sqp)"
    proof -
      have "0 \<le> L j * (sqp' - grd P j)" 
        using assms L_def gross_liq_ge lower_tick_lbound by auto
      moreover have "0 \<le> 
          (\<Sum>n | L n \<noteq> 0 \<and> i < n \<and> n < j. L n * (grd P (n + 1) - grd P n))"
      proof (rule sum_nonneg)
        fix n
        assume "n \<in> {n. L n \<noteq> 0 \<and> i < n \<and> n < j}"
        show "0 \<le> L n * (grd P (n + 1) - grd P n)"
          by (simp add: L_def assms(1) rng_quote_gross_ge)
      qed
      ultimately show ?thesis by simp
    qed
    also have "... = quote_gross P sqp' - quote_gross P sqp" using eq by simp
    finally have "0 < quote_gross P sqp' - quote_gross P sqp" .
    then show ?thesis by simp
  next
    case False
    have "0 < (\<Sum>n | L n \<noteq> 0 \<and> i < n \<and> n < j. L n * (grd P (n + 1) - grd P n))"
    proof (rule sum_ex_strict_pos)
      define M where "M = {n. L n \<noteq> 0 \<and> i < n \<and> n < j}"
      show "finite M" using M_def by simp
      have "k\<in> M" using assms False M_def \<open>L k \<noteq> 0\<close> by simp
      moreover have "0 < L k * (grd P (k+1) - grd P k)"
        using L_def assms clmm_dsc_grd_Suc gross_liq_gt by auto
      ultimately show "\<exists>a\<in>M. 0 < L a * (grd P (a + 1) - grd P a)" by auto
      show "\<forall>x\<in>M. 0 \<le> L x * (grd P (x + 1) - grd P x)"
        by (simp add: L_def assms(1) rng_quote_gross_ge)
    qed
    also have "... \<le> L j * (sqp' - grd P j) + 
        (\<Sum>n | L n \<noteq> 0 \<and> i < n \<and> n < j. L n * (grd P (n + 1) - grd P n)) +
        L i * (grd P (i + 1) - sqp)"
    proof -
      have "0 \<le> L j * (sqp' - grd P j)" 
        using \<open>grd P j \<le> sqp'\<close> L_def assms(1) gross_liq_ge by auto
      moreover have "0 \<le> L i * (grd P (i + 1) - sqp)" 
        using \<open>sqp < grd P (i+1)\<close> L_def assms(1) gross_liq_ge by auto
      ultimately show ?thesis by simp
    qed
    also have "... = quote_gross P sqp' - quote_gross P sqp" using eq by simp
    finally have "0 < quote_gross P sqp' - quote_gross P sqp" .
    thus ?thesis by simp
  qed
qed

lemma quote_gross_disj_gt':
  assumes "clmm_dsc P"
  and "i = lower_tick P sqp"
  and "j = lower_tick P sqp'"
  and "i < j"
  and "lq P j \<noteq> 0"
  and "grd P j < sqp'"
  and "0 < sqp" 
  and "0 < sqp'"
shows "quote_gross P sqp < quote_gross P sqp'"
proof -
  define L where "L = gross_fct (lq P) (fee P)"
  hence "0 < L j" using assms gross_liq_gt by fastforce
  have "sqp < grd P (i+1)" using assms lower_tick_ubound by simp 
  have "sqp < sqp'" using lower_tick_lt assms by simp
  have "0 < L j * (sqp' - grd P j)" using assms \<open>0 < L j\<close> by simp
  also have "... \<le> L j * (sqp' - grd P j) + 
      (\<Sum>n | L n \<noteq> 0 \<and> i < n \<and> n < j. L n * (grd P (n + 1) - grd P n)) +
      L i * (grd P (i + 1) - sqp)"
  proof -
    have "0 \<le> L i * (grd P (i + 1) - sqp)" 
      using \<open>sqp < grd P (i+1)\<close> L_def assms(1) gross_liq_ge by auto
    moreover have "0 \<le> 
        (\<Sum>n | L n \<noteq> 0 \<and> i < n \<and> n < j. L n * (grd P (n + 1) - grd P n))"
    proof (rule sum_nonneg)
      fix n
      assume "n \<in> {n. L n \<noteq> 0 \<and> i < n \<and> n < j}"
      show "0 \<le> L n * (grd P (n + 1) - grd P n)"
        by (simp add: L_def assms(1) rng_quote_gross_ge)
    qed
    ultimately show ?thesis by simp
  qed
  also have "... = quote_gross P sqp' - quote_gross P sqp"
    using clmm_quote_gross_diff_eq \<open>sqp < sqp'\<close> assms L_def by simp
  finally have "0 < quote_gross P sqp' - quote_gross P sqp" .
  thus ?thesis by simp
qed

lemma quote_gross_lower_eq_gt:
  assumes "clmm_dsc P"
  and "j = lower_tick P sqp"
  and "j = lower_tick P sqp'"
  and "lq P j \<noteq> 0"
  and "0 < sqp" 
  and "sqp < sqp'"
shows "quote_gross P sqp < quote_gross P sqp'"
proof -
  define L where "L = gross_fct (lq P) (fee P)"
  hence "0 < L j" using assms gross_liq_gt by fastforce
  have "sqp < sqp'" using lower_tick_lt assms by simp
  hence "0 < L j * (sqp' - sqp)" using assms \<open>0 < L j\<close> by simp
  also have "... = quote_gross P sqp' - quote_gross P sqp"
    using clmm_quote_gross_diff_eq' assms L_def by simp
  finally have "0 < quote_gross P sqp' - quote_gross P sqp" .
  thus ?thesis by simp
qed

lemma quote_reach_gt_grd_min:
  assumes "clmm_dsc P"
  and "nz_support (lq P) \<noteq> {}"
  and "0 < y"
  and "y \<le> quote_gross P (grd_max P)"
  and "sqp = quote_reach P y"
shows "grd_min P < sqp"
proof (rule ccontr)
  assume "\<not> grd_min P < sqp"
  hence "quote_gross P sqp \<le> quote_gross P (grd_min P)"
    using assms clmm_quote_gross_grd_min clmm_quote_gross_grd_min_le 
      clmm_quote_reach_pos 
    by auto
  hence "y \<le> 0"
    by (metis assms(1) assms(2) assms(4) assms(5) clmm_quote_gross_grd_min 
        clmm_quote_gross_reach_eq linorder_le_cases)
  thus False using assms by simp
qed

lemma sqp_lt_grd_max_imp_idx:
  assumes "clmm_dsc P"
  and "nz_support (lq P) \<noteq> {}"
  and "0 < sqp"
  and "sqp < grd_max P"
  and "i = lower_tick P sqp"
shows "i \<le> idx_max (lq P)"
proof -
  have lid: "lower_tick P (grd_max P) = idx_max (lq P) + 1"
      by (simp add: assms(1) idx_max_img_def lower_tick_eq grd_max_def)
  have "i < lower_tick P (grd_max P)" 
  proof (rule lower_tick_lt')
    show "clmm_dsc P" using assms by simp
    show "0 < sqp" using assms by simp
    show "sqp < grd_max P" using assms by simp    
    show "grd P (lower_tick P (grd_max P)) = grd_max P"
      using lid by (simp add: idx_max_img_def grd_max_def )
    show "i = lower_tick P sqp" using assms by simp
  qed simp
  also have "... = idx_max (lq P) + 1" using lid by simp
  finally show ?thesis by simp
qed

lemma quote_gross_lt_grd_max:
  assumes "clmm_dsc P"
  and "nz_support (lq P) \<noteq> {}"
  and "0 < sqp"
  and "sqp < grd_max P"
shows "quote_gross P sqp < quote_gross P (grd_max P)"
proof (rule quote_gross_disj_gt)
  define i where "i = lower_tick P sqp"
  thus "i = lower_tick P sqp" .
  define j where "j = lower_tick P (grd_max P)"
  thus "j = lower_tick P (grd_max P)" .
  define k where "k = j - 1"
  show "clmm_dsc P" using assms by simp
  show "0 < sqp" using assms by simp
  show "0 < grd_max P" using assms by simp
  show "k < j" unfolding k_def by simp
  have "j = idx_max (lq P) +1" using lower_tick_grd_max
    by (simp add: assms(1) j_def)
  have "lq P (idx_max (lq P)) \<noteq> 0"  
  proof (rule idx_max_finite_in)
    show "finite (nz_support (lq P))" 
      using assms clmm_dsc_liq(1) finite_liq_def by auto
  qed (simp add: assms)
  hence "lq P k \<noteq> 0" using \<open>j = idx_max (lq P) + 1\<close> k_def by simp
  thus "lq P (lower_tick P (grd_max P) - 1) \<noteq> 0"
    by (simp add: j_def k_def)
  have "i < j" 
  proof (rule lower_tick_lt'[of P sqp])
    show "j = lower_tick P (grd P j)" using j_def
      by (simp add: assms(1) lower_tick_eq)
    have "grd_max P = grd P j" 
      using \<open>j = idx_max (lq P) +1\<close> grd_max_def idx_max_img_def by metis
    thus "sqp < grd P j" using assms by simp
    show "i = lower_tick P sqp" using i_def by simp
  qed (simp add: assms k_def)+
  thus "lower_tick P sqp \<le> lower_tick P (grd_max P) - 1" 
    using i_def j_def by simp
qed

lemma idx_max_gt_liq:
  assumes "clmm_dsc P"
  and "j = idx_max (lq P)"
shows "\<forall>k > j. lq P k = 0" 
proof (intro allI impI)
  fix k
  assume "j < k"
  show "lq P k = 0"
  proof (rule idx_max_finite_gt[of "lq P"])
    show "finite (nz_support (lq P))" 
      using assms clmm_dsc_liq(1) finite_liq_def by simp
    show "idx_max (lq P) < k" using assms \<open>j < k\<close> by simp
  qed
qed

lemma idx_min_lt_liq:
  assumes "clmm_dsc P"
  and "j = idx_min (lq P)"
shows "\<forall>k < j. lq P k = 0" 
proof (intro allI impI)
  fix k
  assume "k < j"
  show "lq P k = 0"
  proof (rule idx_min_finite_lt[of "lq P"])
    show "finite (nz_support (lq P))" 
      using assms clmm_dsc_liq(1) finite_liq_def by simp
    show "k< idx_min (lq P)" using assms \<open>k < j\<close> by simp
  qed
qed

lemma quote_reach_le':
  assumes "clmm_dsc P"
  and "grd_min P < sqp"
  and "i = lower_tick P sqp"
  and "lq P i \<noteq> 0"
  and "y = quote_gross P sqp"
shows "quote_reach P y \<le> sqp" 
proof -
  interpret finite_liq_pool P
    by (simp add: assms clmm_dsc_liq(1) finite_liq_pool_def)
  show ?thesis
  proof (rule quote_reach_le)
    show "\<forall>i. 0 \<le> lq P i"
      by (simp add: assms(1) clmm_dsc_liq(2))
    show "sqp \<in> quote_gross P -` {y}" using assms by simp
    have "0 < quote_gross P sqp" 
    proof (rule quote_gross_gt_grd_min)
      show "grd_min P < sqp" using assms by simp
      show "nz_support (lq P) \<noteq> {}" 
        using assms unfolding nz_support_def by auto
    qed (simp add: assms)
    then show "0 < y" using assms by simp
    have "quote_gross P sqp < quote_gross P (grd_max P)" 
    proof (rule quote_gross_lt_grd_max)
      have "nz_support (lq P) \<noteq> {}" 
        using assms unfolding nz_support_def by auto
      hence "0 < grd_min P" using assms
        by (simp add: liq_grd_min)
      thus "0 < sqp" using assms by simp
      show "sqp < grd_max P" using assms grd_max_gt_if by simp
      show "nz_support (lq P) \<noteq> {}" 
        using assms unfolding nz_support_def by auto
    qed (simp add: assms)+
    show "\<forall>i. fee P i < 1" by (simp add: assms(1) clmm_dsc_fees)
    show "mono (grd P)" by (simp add: assms(1) strict_mono_mono)
  qed
qed

lemma quote_reach_gross_le:
  assumes "clmm_dsc P"
  and "grd_min P \<le> sqp"
shows "quote_reach P (quote_gross P sqp) \<le> sqp" 
proof (rule finite_liq_pool.quote_reach_gross_le)
  show "finite_liq_pool P"
    by (simp add: assms(1) clmm_dsc_liq(1) finite_liq_pool.intro)
  show "\<forall>i. 0 \<le> lq P i" by (simp add: assms(1) clmm_dsc_liq(2))
  show "\<forall>i. fee P i < 1" by (simp add: assms(1) clmm_dsc_fees)
  show "mono (grd P)" by (simp add: assms(1) clmm_dsc_grd_mono monoI)
  show "grd_min P \<le> sqp" using assms by simp
qed

lemma quote_reach_strict_mono:
  assumes "clmm_dsc P"
  and "nz_support (lq P) \<noteq> {}"
  and "0 \<le> y1"
  and "y1 < y2"
  and "y2 \<le> quote_gross P (grd_max P)"
  and "sqp = quote_reach P y1"
  and "sqp' = quote_reach P y2"
shows "sqp < sqp'"
proof (rule ccontr)
  assume "\<not> sqp < sqp'"
  hence "quote_gross P sqp' \<le> quote_gross P sqp" 
    using assms clmm_quote_gross_mono[of P] by (simp add: monoD)
  hence "y2 \<le> y1"
    using assms clmm_quote_gross_reach_eq by auto 
  thus False using assms by simp
qed

lemma quote_reach_mono:
  assumes "clmm_dsc P"
  and "nz_support (lq P) \<noteq> {}"
  and "0 \<le> y1"
  and "y1 \<le> y2"
  and "y2 \<le> quote_gross P (grd_max P)"
  and "sqp = quote_reach P y1"
  and "sqp' = quote_reach P y2"
shows "sqp \<le> sqp'"
proof (cases "y1 = y2")
  case True
  then show ?thesis using assms by simp
next
  case False
  hence "y1 < y2" using assms by simp
  then show ?thesis using assms quote_reach_strict_mono by fastforce
qed

lemma grd_max_quote_reach:
  assumes "clmm_dsc P"
  and "nz_support (lq P) \<noteq> {}"
shows "quote_reach P (quote_gross P (grd_max P)) = grd_max P"
proof (rule ccontr)
  define sqp where "sqp = quote_reach P (quote_gross P (grd_max P))"
  hence eq: "quote_gross P sqp = quote_gross P (grd_max P)"
    by (meson assms(1) assms(2) clmm_quote_gross_reach_eq liq_grd_min_max 
        dual_order.strict_trans linorder_le_less_linear order_less_irrefl 
        quote_gross_gt_grd_min) 
  define i where "i = lower_tick P sqp"
  assume "sqp \<noteq> grd_max P"  
  hence "sqp < grd_max P" 
    using clmm_quote_reach_le
    by (metis assms liq_grd_min_max order_le_imp_less_or_eq 
        quote_gross_gt_grd_min sqp_def vimage_singleton_eq)
  have "quote_gross P sqp < quote_gross P (grd_max P)" 
  proof (rule quote_gross_lt_grd_max)
    show "0 < sqp" using clmm_quote_reach_pos[OF assms(1-2)]
      by (metis assms liq_grd_min_max linorder_le_less_linear order.asym 
          quote_gross_gt_grd_min sqp_def)
    show "sqp < grd_max P" using \<open>sqp < grd_max P\<close> .
  qed (simp add: assms)+
  thus False using eq by simp
qed

lemma quote_reach_gt:
  assumes "clmm_dsc P"
  and "nz_support (lq P) \<noteq> {}"
  and "0 < y"
  and "y + quote_gross P sqp \<le> quote_gross P (grd_max P)"
  and "sqp' = quote_reach P (y + quote_gross P sqp)"
shows "sqp < sqp'"
proof (rule ccontr)
  assume "\<not> sqp < sqp'"
  have "y + quote_gross P sqp = quote_gross P sqp'" 
    using assms clmm_quote_gross_reach_eq
    by (simp add: clmm_quote_gross_pos) 
  also have "... \<le> quote_gross P sqp" 
    using assms \<open>\<not> sqp < sqp'\<close> quote_gross_imp_sqp_lt by fastforce
  finally show False using assms by simp
qed

lemma lt_quote_gross_imp_up_price:
  assumes "clmm_dsc P"
  and "nz_support (lq P) \<noteq> {}"
  and "0 < y"
  and "y \<le> quote_gross P (grd_max P)"
  and "quote_gross P sqp < y"
  and "sqp' = quote_reach P y"
shows "sqp < sqp'"
proof (rule ccontr)
  assume "\<not> sqp < sqp'"
  have "y  = quote_gross P sqp'" 
    using assms clmm_quote_gross_reach_eq
    by (simp add: clmm_quote_gross_pos) 
  also have "... \<le> quote_gross P sqp" 
    using assms \<open>\<not> sqp < sqp'\<close> quote_gross_imp_sqp_lt by fastforce
  finally show False using assms by simp
qed

lemma quote_reach_add_gt:
  assumes "clmm_dsc P"
  and "nz_support (lq P) \<noteq> {}"
  and "0 < y"
  and "y + quote_gross P sqp \<le> quote_gross P (grd_max P)"
  and "sqp' = quote_reach P (y + quote_gross P sqp)"
shows "quote_gross P sqp < quote_gross P sqp'"
proof -
  have "0 \<le> y +  quote_gross P sqp"
    using assms clmm_quote_gross_pos by simp
  hence "quote_gross P sqp' = y + quote_gross P sqp" 
    using assms clmm_quote_gross_reach_eq by simp
  thus ?thesis using assms by simp
qed

lemma quote_reach_leq_grd_max:
  assumes "clmm_dsc P"
  and "nz_support (lq P) \<noteq> {}"
  and "0 \<le> y"
  and "y \<le> quote_gross P (grd_max P)"
  and "sqp = quote_reach P y"
shows "sqp \<le> grd_max P" 
  using assms 
  by (metis quote_reach_mono grd_max_quote_reach 
      order_refl)

lemma quote_gross_grd_max_ge:
  assumes "clmm_dsc P"
  and "nz_support (lq P) \<noteq> {}"
  and "grd_max P < sqp"
shows "quote_gross P sqp = quote_gross P (grd_max P)" 
proof -
  define k where "k = lower_tick P sqp"
  define j where "j = idx_max (lq P) + 1"
  define L where "L = gross_fct (lq P) (fee P)"
  have zer: "\<forall>k \<ge> j. lq P k = 0" using assms idx_max_gt_liq j_def by simp
  hence eq: "\<forall>k \<ge> j. L k = 0"
    by (simp add: L_def gross_fct_zero_if)
  have "lower_tick P (grd_max P) = j"
    by (simp add: assms(1) lower_tick_grd_max j_def) 
  hence "j \<le> k" using assms
    by (metis clmm_dsc_grid(2) k_def lower_tick_mono order_less_imp_le 
        grd_max_gt)
  show ?thesis
  proof (cases "k = j")
    case True
    have "quote_gross P sqp - quote_gross P (grd_max P) = L k * (sqp - grd_max P)" 
    proof (rule clmm_quote_gross_diff_eq')
      show  "k = lower_tick P (grd_max P)" 
        using \<open>lower_tick P (grd_max P) = j\<close> 
        by (simp add: assms(1) lower_tick_eq True) 
      show "L = gross_fct (lq P) (fee P)" using L_def by simp
      show "clmm_dsc P" using assms by simp
      show "grd_max P \<le> sqp" using assms by simp
      show "k = lower_tick P sqp" using assms k_def  by simp
      show "0 < grd_max P" using assms grd_max_gt by simp
    qed
    also have "... = 0" 
      using zer L_def True by (simp add: gross_fct_zero_if)
    finally have "quote_gross P sqp - quote_gross P (grd_max P) = 0" .
    then show ?thesis using assms by simp
  next
    case False
    hence "j < k" using \<open>j \<le> k\<close> by simp
    have "quote_gross P sqp - quote_gross P (grd_max P) = L k * (sqp - grd P k) + 
        (\<Sum>i | L i \<noteq> 0 \<and> j < i \<and> i < k. L i * (grd P (i + 1) - grd P i)) + 
        L j * (grd P (j + 1) - grd_max P)" 
    proof (rule clmm_quote_gross_diff_eq)
      show  "j = lower_tick P (grd_max P)" 
        using \<open>lower_tick P (grd_max P) = j\<close> by simp
      show "L = gross_fct (lq P) (fee P)" using L_def by simp
      show "clmm_dsc P" using assms by simp
      show "grd_max P \<le> sqp" using assms by simp
      show "k = lower_tick P sqp" using assms k_def  by simp
      show "0 < grd_max P" using assms grd_max_gt by simp
      show "j < k" using \<open>j < k\<close> .
    qed
    also have "... = 0"
    proof -      
      have "{i. L i \<noteq> 0 \<and> j < i \<and> i < k} = {}" using eq by auto
      hence "(\<Sum>i | L i \<noteq> 0 \<and> j < i \<and> i < k. L i * (grd P (i + 1) - grd P i)) = 0" 
        by (metis (full_types) sum.empty)
      moreover have "L k = 0" using eq \<open>j < k\<close> by simp
      moreover have "L j * (grd P (j + 1) - grd_max P) = 0" using eq by simp
      ultimately show ?thesis by simp
    qed
    finally show ?thesis by simp
  qed
qed

lemma quote_gross_grd_max_max:
  assumes "clmm_dsc P"
  and "nz_support (lq P) \<noteq> {}"
shows "quote_gross P sqp \<le> quote_gross P (grd_max P)" 
proof (cases "sqp \<le> grd_max P")
  case True
  then show ?thesis
    using assms(1) quote_gross_imp_sqp_lt verit_comp_simplify1(3) by blast 
next
  case False
  then show ?thesis using assms quote_gross_grd_max_ge by simp
qed

lemma gross_grd_max_max':
  assumes "clmm_dsc P"
  and "nz_support (lq P) \<noteq> {}"
  and "sqp < grd_max P"
shows "quote_gross P sqp < quote_gross P (grd_max P)" 
using assms quote_gross_grd_max_ge
  by (metis antisym_conv3 liq_grd_min liq_grd_min_max order.strict_trans 
      quote_gross_gt_grd_min quote_gross_lt_grd_max quote_gross_pos_gt_grd_min) 

lemma quote_reach_le_gross:
  assumes "clmm_dsc P"
  and "0 < y"
  and "0 < sqp"
  and "y \<le> quote_gross P sqp"
  and "sqp \<le> grd_max P"
  and "sqp' = quote_reach P y"
  and "nz_support (lq P) \<noteq> {}"
shows "sqp' \<le> sqp"
proof -
  interpret finite_liq_pool P
    by (simp add: assms clmm_dsc_liq(1) finite_liq_pool_def)
  have lt: "quote_gross P sqp \<le> quote_gross P (grd_max P)"
    by (simp add: assms(1) assms(7) quote_gross_grd_max_max)
  show ?thesis 
  proof (cases "y = quote_gross P sqp")
    case True
    then show ?thesis using clmm_quote_reach_le lt assms by simp
  next
    case False
    hence "y < quote_gross P sqp" using assms by simp
    hence "quote_gross P sqp' < quote_gross P sqp" 
      using assms clmm_quote_gross_reach_eq lt by auto 
    then show ?thesis
      using assms(1) clmm_quote_gross_mono mono_invE by blast
  qed
qed

lemma quote_net_diff_eq:
  assumes "clmm_dsc P"
  and "L = lq P"
  and "j = lower_tick P sqp"
  and "k = lower_tick P sqp'"
  and "0 < sqp"
  and "sqp \<le> sqp'"
  and "j < k"
shows "quote_net P sqp' - quote_net P sqp = L k * (sqp' - grd P k) + 
  sum (\<lambda> i. L i * (grd P (i+1) - grd P i)) {i. L i \<noteq> 0 \<and> j <i \<and> i < k} +
  L j * (grd P (j+1) - sqp)" 
proof -
  interpret finite_nz_support L
    using finite_liq_pool.finite_liq_gross_fct assms clmm_dsc_def 
      finite_liq_def finite_nz_support_def 
    by blast
  show ?thesis 
    using clmm_gen_quote_diff_eq assms 
    unfolding quote_net_def gen_quote_diff_def by simp
qed

lemma quote_net_diff_eq':
  assumes "clmm_dsc P"
  and "L = lq P"
  and "j = lower_tick P sqp"
  and "j = lower_tick P sqp'"
  and "0 < sqp"
  and "sqp \<le> sqp'"
shows "quote_net P sqp' - quote_net P sqp = L j * (sqp' - sqp)" 
proof -
  interpret finite_nz_support L
    using finite_liq_pool.finite_liq_gross_fct assms clmm_dsc_def 
      finite_liq_def finite_nz_support_def 
    by blast
  show ?thesis using clmm_gen_quote_diff_eq' assms 
    unfolding quote_net_def gen_quote_diff_def by simp
qed

subsection \<open>Base token addition and withdrawal in a CLMM\<close>

lemma (in finite_nz_support) gen_base_sum:
  assumes "clmm_dsc P"
  and "0 < sqp"
  and "j = lower_tick P sqp"
shows "gen_base (grd P) L sqp = 
    L j * (inverse sqp - inverse (grd P (j+1))) + 
    sum (\<lambda>i. L i * (inverse (grd P i) - inverse (grd P (i+1)))) 
    {i. L i \<noteq> 0 \<and> j < i}"
proof -
  define df where "df = inv_gamma_max_diff (grd P)"
  define A where "A = {i. L i \<noteq> 0 \<and> j \<le> i}"
  define B where "B = {i. L i \<noteq> 0 \<and> j > i}"
  define C where "C = {i. L i \<noteq> 0 \<and> j < i}"
  have un: "{i. L i \<noteq> 0} = A \<union> B" unfolding A_def B_def by auto
  have inter: "A \<inter> B = {}" unfolding A_def B_def by auto
  have fin: "finite {i. L i \<noteq> 0}" by (metis fin_nz_sup nz_support_def)
  have "gen_base (grd P) L sqp = 
      sum (rng_token df L sqp) {i. L i \<noteq> 0}" 
    unfolding gen_base_def df_def using gen_token_sum by simp
  also have "... = sum (rng_token df L sqp) A + sum (rng_token df L sqp) B"
    by (metis empty_iff fin finite_Un inter sum.union_inter_neutral un)
  also have "... = sum (rng_token df L sqp) A"
  proof -
    have "\<forall> i\<in> B. rng_token df L sqp i = 0" 
    proof
      fix i
      assume "i \<in> B"
      have "grd P i < grd P (i+1)" using assms clmm_dsc_grid span_gridD
        by (simp add: strict_mono_less)
      have "i + 1 \<le> j" using \<open>i \<in> B\<close> assms unfolding B_def by simp
      hence "grd P (i +1) \<le> grd P j" 
        using assms clmm_dsc_grid span_gridD by (simp add: strict_mono_leD)
      hence "grd P (i+1) \<le> sqp" using assms
        by (meson dual_order.trans lower_tick_lbound)
      hence "grd P i < sqp" using \<open>grd P i < grd P (i+1)\<close> by simp
      hence "df sqp i = 0" 
        using \<open>grd P (i+1) \<le> sqp\<close> unfolding df_def inv_gamma_max_diff_def by simp
      thus "rng_token df L sqp i = 0" unfolding rng_token_def by simp
    qed
    thus ?thesis by simp
  qed
  also have "... = rng_token df L sqp j + sum (rng_token df L sqp) C"
  proof (cases "j \<in> A")
    case True
    hence "A = {j} \<union> C" unfolding A_def C_def by auto
    hence "sum (rng_token df L sqp) A = sum (rng_token df L sqp) ({j} \<union> C)"
      by simp
    also have "... = sum (rng_token df L sqp) {j} + sum (rng_token df L sqp) C" 
    proof (rule sum.union_inter_neutral)
      show "finite {j}" by simp
      show "finite C" using fin C_def by simp
      show "\<forall>x\<in>{j} \<inter> C. rng_token df L sqp x = 0" using C_def by simp
    qed
    also have "... = rng_token df L sqp j + sum (rng_token df L sqp) C" by simp
    finally show ?thesis .
  next
    case False
    hence "A = C" unfolding A_def C_def using Collect_cong by fastforce
    have "L j = 0" using False A_def by auto
    hence "rng_token df L sqp j = 0" unfolding rng_token_def by simp
    then show ?thesis using \<open>A = C\<close> by simp
  qed
  also have "... = L j * (inverse sqp - inverse (grd P (j+1))) + 
      sum (rng_token df L sqp) C"
  proof -
    have "max sqp (grd P (j + 1)) = grd P (j+1)" 
      using assms lower_tick_ubound by simp
    moreover have "max sqp (grd P j) = sqp" 
      using assms lower_tick_lbound by simp 
    ultimately have "rng_token df L sqp j = 
        L j * (inverse sqp - inverse (grd P (j+1)))" 
      unfolding rng_token_def df_def inv_gamma_max_diff_def by simp
    thus ?thesis by simp
  qed
  also have "... = L j * (inverse sqp - inverse (grd P (j+1))) + 
      sum (\<lambda>i. L i * (inverse (grd P i) - inverse (grd P (i+1)))) C"     
  proof -
    have "\<forall>i\<in> C. rng_token df L sqp i = 
        L i * (inverse (grd P i) - inverse (grd P (i+1)))" 
    proof
      fix i
      assume "i\<in> C"
      hence "j+1 \<le> i" using C_def by auto
      hence "grd P (j+1) \<le> grd P i" using assms clmm_dsc_grid(1) strict_monoD
        by (metis linorder_le_less_linear nless_le)
      hence "sqp \<le> grd P i" using lower_tick_ubound assms by fastforce
      hence "sqp \<le> grd P (i+1)" 
        using clmm_dsc_grd_Suc assms dual_order.strict_trans2 order_less_imp_le 
        by blast 
      thus "rng_token df L sqp i =  
          L i * (inverse (grd P i) - inverse (grd P (i+1)))" 
        unfolding rng_token_def df_def inv_gamma_max_diff_def
        using \<open>sqp \<le> grd P i\<close>
        by simp
    qed
    hence "sum (rng_token df L sqp) C = 
        sum (\<lambda>i. L i * (inverse (grd P i) - inverse (grd P (i+1)))) C" 
      by simp
    thus ?thesis by simp
  qed
  finally show "gen_base (grd P) L sqp =  
      L j * (inverse sqp - inverse (grd P (j+1))) + 
      sum (\<lambda>i. L i * (inverse (grd P i) - inverse (grd P (i+1)))) C" .
qed

lemma (in finite_nz_support) gen_base_grd_max:
  assumes "clmm_dsc P"
  and "nz_support L \<noteq> {}"
  and "nz_support L = nz_support (lq P)"
shows "gen_base (grd P) L (grd_max P) = 0"
proof -
  define j where "j = lower_tick P (grd_max P)"
  hence "j = idx_max (lq P) + 1" using lower_tick_grd_max[of P] assms by simp
  have "gen_base (grd P) L (grd_max P) = 
      L j * (inverse (grd_max P) - inverse (grd P (j + 1))) +
      (\<Sum>i | L i \<noteq> 0 \<and> j < i. 
      L i * (inverse (grd P i) - inverse (grd P (i + 1))))" 
  proof (rule gen_base_sum)
    show "0 < grd_max P" 
    proof (rule grd_max_gt)
      show "nz_support (lq P) \<noteq> {}" using assms by simp
      show "\<And>i. 0 < grd P i" using assms by simp
    qed
  qed (simp add: assms j_def)+
  also have "... =0"
  proof -
    have emp: "{i. L i \<noteq> 0 \<and> j \<le> i} = {}" 
    proof -
      have "\<forall>i \<ge> j. L i = 0" 
      proof (intro allI impI)
        fix i
        assume "j \<le> i"
        hence "idx_max (lq P) < i" using \<open>j = idx_max (lq P) + 1\<close> by simp
        hence "lq P i = 0" 
          using idx_max_finite_ge[of "lq P" i] fin_nz_sup assms(3) by auto
        thus "L i = 0" using assms unfolding nz_support_def by auto

      qed
      thus ?thesis by auto
    qed
    hence a: "L j * (inverse (grd_max P) - inverse (grd P (j + 1))) = 0" by auto
    have "{i. L i \<noteq> 0 \<and> j < i} = {}" using emp by auto
    hence "(\<Sum>i | L i \<noteq> 0 \<and> j < i. 
        L i * (inverse (grd P i) - inverse (grd P (i + 1)))) = 0"
      by (metis (full_types) sum_clauses(1))
    thus ?thesis using a by simp
  qed  
  finally show ?thesis .
qed

lemma base_gross_sum:
  assumes "clmm_dsc P"
  and "0 < sqp"
  and "L = gross_fct (lq P) (fee P)"
  and "j = lower_tick P sqp"
shows "base_gross P sqp = 
    L j * (inverse sqp - inverse (grd P (j+1))) + 
    sum (\<lambda>i. L i * (inverse (grd P i) - inverse (grd P (i+1)))) 
    {i. L i \<noteq> 0 \<and> j < i}"
proof -
  interpret finite_nz_support L
    using finite_liq_pool.finite_liq_gross_fct assms
    by (metis clmm_dsc_liq(1) finite_liq_pool.intro finite_nz_support_def 
        nz_support_def)
  show ?thesis unfolding base_gross_def using gen_base_sum assms by simp
qed

lemma clmm_base_gross_grd_max:
  assumes "clmm_dsc P"
  and "nz_support (lq P) \<noteq> {}"
shows "base_gross P (grd_max P) = 0" unfolding base_gross_def 
proof (rule finite_nz_support.gen_base_grd_max)
  show "finite_nz_support (gross_fct (lq P) (fee P))"
    using finite_liq_pool.finite_liq_gross_fct assms
    by (metis clmm_dsc_liq(1) finite_liq_pool.intro finite_nz_support_def 
        nz_support_def)
  show "clmm_dsc P" using assms by simp
  show "nz_support (gross_fct (lq P) (fee P)) = nz_support (lq P)"
    using clmm_dsc_gross_liq assms by simp
  thus "nz_support (gross_fct (lq P) (fee P)) \<noteq> {}" using assms by simp
qed

lemma liq_base_reach_max:
  assumes "clmm_dsc P"
  and "nz_support (lq P) \<noteq> {}"
shows "base_reach P 0 = grd_max P" 
  using assms clmm_base_gross_grd_max unfolding base_reach_def by simp

lemma base_net_sum:
  assumes "clmm_dsc P"
  and "0 < sqp"
  and "L = lq P"
  and "j = lower_tick P sqp"
shows "base_net P sqp = 
    L j * (inverse sqp - inverse (grd P (j+1))) + 
    sum (\<lambda>i. L i * (inverse (grd P i) - inverse (grd P (i+1)))) 
    {i. L i \<noteq> 0 \<and> j < i}"
proof -
  interpret finite_nz_support L
    using finite_liq_pool.finite_liq_gross_fct assms clmm_dsc_def finite_liq_def 
      finite_nz_support_def 
    by blast
  show ?thesis unfolding base_net_def using gen_base_sum assms by simp
qed

definition gen_base_diff where
"gen_base_diff P L sqp sqp' = gen_base (grd P) L sqp - gen_base (grd P) L sqp'"

lemma (in finite_nz_support) gen_base_diff_eq:
  assumes "clmm_dsc P"
  and "j = lower_tick P sqp"
  and "k = lower_tick P sqp'"
  and "0 < sqp"
  and "sqp \<le> sqp'"
  and "j < k"
shows "gen_base_diff P L sqp sqp' = 
  L j * (inverse sqp - inverse (grd P (j+1))) + 
  sum (\<lambda> i. L i * (inverse (grd P i) - inverse (grd P (i+1)))) 
  {i. L i \<noteq> 0 \<and> j <i \<and> i < k} +
  L k * (inverse (grd P k) - inverse sqp')" 
proof -
  have "0 < sqp" using assms by simp
  hence "sqp < sqp'" using lower_tick_lt assms by simp
  hence "0 < sqp'" using \<open>0 < sqp\<close> by simp
  define A where "A = {i. L i \<noteq> 0 \<and> j < i}"
  define B where "B = {i. L i \<noteq> 0 \<and> k < i}"
  define C where "C = {i. L i \<noteq> 0 \<and> j <i \<and> i \<le> k}"
  define Ck where "Ck = {i. L i \<noteq> 0 \<and> j <i \<and> i < k}"
  define df where "df = (\<lambda> i. L i * (inverse (grd P i) - inverse (grd P (i+1))))" 
  have "finite A"
    unfolding A_def by (metis fin_nz_sup finite_Collect_conjI nz_support_def)
  have "A = B \<union> C" using assms unfolding A_def B_def C_def by auto
  have "Ck = C - {k}" unfolding C_def Ck_def by auto
  have "gen_base_diff P L sqp sqp' = 
      L j * (inverse sqp - inverse (grd P (j+1))) + 
      sum df A - (L k * (inverse sqp' - inverse (grd P (k+1))) + sum df B)"
    using assms \<open>0 < sqp\<close> gen_base_sum \<open>0 < sqp'\<close> 
    unfolding gen_base_diff_def df_def A_def B_def by simp
  also have "... = L j * (inverse sqp - inverse (grd P (j+1))) + 
      sum df C - L k * (inverse sqp' - inverse (grd P (k+1)))"
  proof (rule diff_sum_dcomp)
    show "finite A" using \<open>finite A\<close> .
    show "A = B \<union> C" using \<open>A = B \<union> C\<close> .
    show "B \<inter> C = {}" unfolding B_def C_def by auto
  qed
  also have "... = L j * (inverse sqp - inverse (grd P (j+1))) + 
      df k + sum df Ck - L k * (inverse sqp' - inverse (grd P (k+1)))"
  proof (cases "k \<in> C")
    case True
    have "sum df C = df k + sum df Ck"
    proof (rule sum_remove_el)
      show "finite C" using \<open>A = B \<union> C\<close> \<open>finite A\<close> by simp
      show "k \<in> C" using True .
      show "Ck = C - {k}" using \<open>Ck = C - {k}\<close> .
    qed
    then show ?thesis by simp
  next
    case False
    hence "L k = 0" using assms unfolding C_def by auto
    hence "df k = 0" unfolding df_def by simp
    moreover have "Ck = C" using False \<open>Ck = C - {k}\<close> by auto
    ultimately show ?thesis by simp
  qed
  also have "... = L j * (inverse sqp - inverse (grd P (j+1))) + sum df Ck +
      L k * (inverse (grd P k) - inverse sqp')"
  proof -
    have "df k - L k * (inverse sqp' - inverse (grd P (k+1))) = 
        L k * (inverse (grd P k) - inverse sqp')" 
      unfolding df_def by (simp add: right_diff_distrib)
    thus ?thesis by simp
  qed
  finally show "gen_base_diff P L sqp sqp' = 
      L j * (inverse sqp - inverse (grd P (j+1))) + sum df Ck +
      L k * (inverse (grd P k) - inverse sqp')" .
qed

lemma (in finite_nz_support) gen_base_diff_eq':
  assumes "clmm_dsc P"
  and "j = lower_tick P sqp"
  and "j = lower_tick P sqp'"
  and "0 < sqp"
  and "sqp \<le> sqp'"
shows "gen_base_diff P L sqp sqp' = L j * (inverse sqp - inverse sqp')" 
proof -
  have "0 < sqp" using assms by simp
  hence "0 < sqp'" using assms by simp
  define A where "A = {i. L i \<noteq> 0 \<and> j < i}"
  define df where 
      "df = (\<lambda> i. L i * (inverse (grd P i) - inverse (grd P (i+1))))" 
  have "finite A"
    unfolding A_def by (metis fin_nz_sup finite_Collect_conjI nz_support_def)
  have "gen_base_diff P L sqp sqp' = 
      L j * (inverse sqp - inverse (grd P (j+1))) + sum df A - 
      (L j * (inverse sqp' - inverse (grd P (j+1))) + sum df A)"
    using assms \<open>0 < sqp\<close> gen_base_sum \<open>0 < sqp'\<close> 
    unfolding gen_base_diff_def df_def A_def by simp
  also have "... = L j * (inverse sqp - inverse (grd P (j+1))) - 
      L j * (inverse sqp' - inverse (grd P (j+1)))" 
    by simp
  also have "... = L j * (inverse sqp - inverse sqp')"
    by (simp add: right_diff_distrib)
  finally show "gen_base_diff P L sqp sqp' = 
      L j * (inverse sqp - inverse sqp')" .
qed

lemma lower_tick_lt_grd_min:
  assumes "clmm_dsc P"
  and "sqp < grd_min P"
  and "0 < sqp"
  and "j = lower_tick P sqp"
  shows "j < idx_min (lq P)"
proof (rule ccontr)
  have "j \<le> idx_min (lq P)" using lower_tick_grd_min[of P] assms  
    by (simp add: lower_tick_mono) 
  assume "\<not> j < idx_min (lq P)"
  hence "j = idx_min (lq P)" using assms \<open>j \<le> idx_min (lq P)\<close> by simp
  hence "grd_min P = grd P j" unfolding grd_min_def idx_min_img_def by simp
  also have "... \<le> sqp" using \<open>j = lower_tick P sqp\<close>
    by (simp add: assms lower_tick_mem)
  finally show False using assms by simp
qed
  
lemma (in finite_nz_support) gen_base_grd_min_le:
  assumes "clmm_dsc P"
  and "nz_support L = nz_support (lq P)"
  and "sqp < grd_min P"
  and "0 < sqp"
shows "gen_base (grd P) L sqp = gen_base (grd P) L (grd_min P)"
proof -
  define k where "k = idx_min (lq P)"
  hence "k = lower_tick P (grd_min P)"
    by (simp add: assms(1) idx_min_img_def lower_tick_eq grd_min_def)
  have "grd_min P = grd P k" 
    using k_def grd_min_def idx_min_img_def by simp
  define j where "j = lower_tick P sqp"
  hence "j < k" using lower_tick_lt_grd_min[of P] assms k_def
    by simp
  have eq: "\<forall>i < k. L i = 0" 
    using assms unfolding k_def idx_min_def
    by (metis fin_nz_sup idx_min_def idx_min_finite_le leD)
  have "gen_base_diff P L sqp (grd_min P) = 
      L j * (inverse sqp - inverse (grd P (j+1))) + 
      sum (\<lambda> i. L i * (inverse (grd P i) - inverse (grd P (i+1)))) 
      {i. L i \<noteq> 0 \<and> j <i \<and> i < k} +
      L k * (inverse (grd P k) - inverse (grd_min P))" 
  proof (rule gen_base_diff_eq)
    show "j = lower_tick P sqp" using j_def by simp
    show "k = lower_tick P (grd_min P)" using \<open>k = lower_tick P (grd_min P)\<close> .
    show "sqp \<le> grd_min P" using assms by simp
  qed (simp add: assms \<open>j < k\<close>)+
  also have "... = 0"
  proof -
    have "{i. L i \<noteq> 0 \<and> j <i \<and> i < k} = {}" using eq by auto
    hence "sum (\<lambda> i. L i * (inverse (grd P i) - inverse (grd P (i+1)))) 
        {i. L i \<noteq> 0 \<and> j <i \<and> i < k} = 0" 
      by (metis (full_types) sum.empty)
    moreover have "L j * (inverse sqp - inverse (grd P (j+1))) = 0"
      using \<open>j < k\<close> eq by simp
    moreover have " L k * (inverse (grd P k) - inverse (grd_min P)) = 0" 
      using \<open>grd_min P = grd P k\<close> by simp
    ultimately show ?thesis by linarith
  qed
  finally show ?thesis unfolding gen_base_diff_def by simp
qed

lemma base_net_grd_min_lt:
  assumes "clmm_dsc P"
  and "sqp < grd_min P"
  and "0 < sqp"
shows "base_net P sqp = base_net P (grd_min P)"
proof -
  interpret finite_nz_support "lq P"
    using assms(1) clmm_dsc_liq(1) finite_liq_def finite_nz_support.intro 
    by simp
  show ?thesis 
    using assms gen_base_grd_min_le unfolding base_net_def by simp
qed

lemma base_net_grd_min_le:
  assumes "clmm_dsc P"
  and "sqp \<le> grd_min P"
  and "0 < sqp"
shows "base_net P sqp = base_net P (grd_min P)"
proof -
  interpret finite_nz_support "lq P"
    using assms(1) clmm_dsc_liq(1) finite_liq_def finite_nz_support.intro 
    by simp
  show ?thesis 
  proof (cases "sqp = grd_min P")
    case True
    then show ?thesis by simp
  next
    case False
    then show ?thesis 
      using assms gen_base_grd_min_le unfolding base_net_def by simp
  qed
qed

lemma base_gross_diff_eq:
  assumes "clmm_dsc P"
  and "L = gross_fct (lq P) (fee P)"
  and "j = lower_tick P sqp"
  and "k = lower_tick P sqp'"
  and "0 < sqp"
  and "sqp \<le> sqp'"
  and "j < k"
shows "base_gross P sqp - base_gross P sqp' = 
  L j * (inverse sqp - inverse (grd P (j+1))) + 
  sum (\<lambda> i. L i * (inverse (grd P i) - inverse (grd P (i+1)))) 
  {i. L i \<noteq> 0 \<and> j <i \<and> i < k} +
  L k * (inverse (grd P k) - inverse sqp')" 
proof -
  interpret finite_nz_support L
    using finite_liq_pool.finite_liq_gross_fct assms
    by (metis clmm_dsc_liq(1) finite_liq_pool.intro finite_nz_support_def 
        nz_support_def)
  show ?thesis 
    using gen_base_diff_eq assms 
    unfolding base_gross_def gen_base_diff_def by simp
qed

lemma base_gross_diff_eq':
  assumes "clmm_dsc P"
  and "L = gross_fct (lq P) (fee P)"
  and "j = lower_tick P sqp"
  and "j = lower_tick P sqp'"
  and "0 < sqp"
  and "sqp \<le> sqp'"
shows "base_gross P sqp - base_gross P sqp' = L j * (inverse sqp - inverse sqp')" 
proof -
  interpret finite_nz_support L
    using finite_liq_pool.finite_liq_gross_fct assms
    by (metis clmm_dsc_liq(1) finite_liq_pool.intro finite_nz_support_def 
        nz_support_def)
  show ?thesis using gen_base_diff_eq' assms 
    unfolding base_gross_def gen_base_diff_def by simp
qed

lemma base_net_diff_eq:
  assumes "clmm_dsc P"
  and "L = lq P"
  and "j = lower_tick P sqp"
  and "k = lower_tick P sqp'"
  and "0 < sqp"
  and "sqp \<le> sqp'"
  and "j < k"
shows "base_net P sqp - base_net P sqp' = 
  L j * (inverse sqp - inverse (grd P (j+1))) + 
  sum (\<lambda> i. L i * (inverse (grd P i) - inverse (grd P (i+1)))) 
  {i. L i \<noteq> 0 \<and> j <i \<and> i < k} +
  L k * (inverse (grd P k) - inverse sqp')"
proof -
  interpret finite_nz_support L
    using finite_liq_pool.finite_liq_gross_fct assms clmm_dsc_def 
      finite_liq_def finite_nz_support_def 
    by blast
  show ?thesis 
    using gen_base_diff_eq assms 
    unfolding base_net_def gen_base_diff_def by simp
qed

lemma base_net_diff_eq':
  assumes "clmm_dsc P"
  and "L = lq P"
  and "j = lower_tick P sqp"
  and "j = lower_tick P sqp'"
  and "0 < sqp"
  and "sqp \<le> sqp'"
shows "base_net P sqp - base_net P sqp' = L j * (inverse sqp - inverse sqp')" 
proof -
  interpret finite_nz_support L
    using finite_liq_pool.finite_liq_gross_fct assms clmm_dsc_def 
      finite_liq_def finite_nz_support_def 
    by blast
  show ?thesis using gen_base_diff_eq' assms 
    unfolding base_net_def gen_base_diff_def by simp
qed 

lemma cst_fee_base_gross_net_tick_eq:
  assumes "clmm_dsc P"
  and "\<And>i. fee P i = phi"
  and "j = lower_tick P sqp"
  and "j = lower_tick P sqp'"
  and "0 < sqp"
  and "sqp \<le> sqp'"
shows "base_net P sqp - base_net P sqp' = 
    (1 - phi) * (base_gross P sqp - base_gross P sqp')" 
proof -
  define L where "L = gross_fct (lq P) (fee P)"
  have "phi \<noteq> 1" using assms clmm_dsc_fees by fastforce
  have  "\<And>i. L i = lq P i / (1 - phi)" using L_def
    by (simp add: assms(2) gross_fct_def one_cpl_def)
  hence leq: "\<And>i. lq P i = (1 - phi) * L i" using assms \<open>phi \<noteq> 1\<close> by simp
  have "base_net P sqp - base_net P sqp' =
      lq P j * (inverse sqp - inverse sqp')"
    using assms base_net_diff_eq' by simp
  also have "... = (1 - phi) * L j * (inverse sqp - inverse sqp')"
    using leq by simp
  also have "... = (1 - phi) * (L j * (inverse sqp - inverse sqp'))" by simp
  also have "... = (1 - phi) * (base_gross P sqp - base_gross P sqp')" 
    using L_def assms base_gross_diff_eq' by auto
  finally show ?thesis .
qed

lemma cst_fee_base_gross_net_tick_lt:
  assumes "clmm_dsc P"
  and "\<And>i. fee P i = phi"
  and "j = lower_tick P sqp"
  and "k = lower_tick P sqp'"
  and "0 < sqp"
  and "sqp \<le> sqp'"
  and "j < k"
shows "base_net P sqp - base_net P sqp' = 
    (1 - phi) * (base_gross P sqp - base_gross P sqp')"
proof -
  have "phi \<noteq> 1" using assms clmm_dsc_fees by fastforce
  define L where "L = gross_fct (lq P) (fee P)"
  have  "\<And>i. L i = lq P i / (1 - phi)" using L_def
    by (simp add: assms(2) gross_fct_def one_cpl_def)
  hence leq: "\<And>i. lq P i = (1 - phi) * L i" using assms \<open>phi \<noteq> 1\<close> by simp
  have "base_net P sqp - base_net P sqp' = 
      (lq P) j * (inverse sqp - inverse (grd P (j+1))) + 
      sum (\<lambda> i. (lq P) i * (inverse (grd P i) - inverse (grd P (i+1)))) 
      {i. (lq P) i \<noteq> 0 \<and> j <i \<and> i < k} +
      (lq P) k * (inverse (grd P k) - inverse sqp')"
    using assms base_net_diff_eq by simp
  also have "... = 
      (1 - phi) * L j * (inverse sqp - inverse (grd P (j+1))) + 
      sum (\<lambda> i. (1 - phi) * L i * (inverse (grd P i) - inverse (grd P (i+1)))) 
      {i. (lq P) i \<noteq> 0 \<and> j <i \<and> i < k} +
      (1 - phi) * L k * (inverse (grd P k) - inverse sqp')"  
    using leq by simp 
  also have "... = 
      (1 - phi) * L j * (inverse sqp - inverse (grd P (j+1))) + 
      (1 - phi) * sum (\<lambda> i. L i * (inverse (grd P i) - inverse (grd P (i+1)))) 
      {i. (lq P) i \<noteq> 0 \<and> j <i \<and> i < k} +
      (1 - phi) * L k * (inverse (grd P k) - inverse sqp')" 
  proof -
    have "sum (\<lambda> i. (1 - phi) * L i * (inverse (grd P i) - inverse (grd P (i+1)))) 
        {i. (lq P) i \<noteq> 0 \<and> j <i \<and> i < k} = 
        sum (\<lambda> i. (1 - phi) *( L i * (inverse (grd P i) - inverse (grd P (i+1))))) 
        {i. (lq P) i \<noteq> 0 \<and> j <i \<and> i < k}"
      by (meson ab_semigroup_mult_class.mult_ac(1))
    also have "... = 
        (1 - phi) * sum (\<lambda> i. L i * (inverse (grd P i) - inverse (grd P (i+1)))) 
        {i. (lq P) i \<noteq> 0 \<and> j <i \<and> i < k}"
      by (simp add: sum_distrib_left)
    finally have "sum (\<lambda> i. (1 - phi) * L i * (inverse (grd P i) - inverse (grd P (i+1)))) 
        {i. (lq P) i \<noteq> 0 \<and> j <i \<and> i < k} =
        (1 - phi) * sum (\<lambda> i. L i * (inverse (grd P i) - inverse (grd P (i+1)))) 
        {i. (lq P) i \<noteq> 0 \<and> j <i \<and> i < k}" .
    thus ?thesis by simp
  qed
  also have "... = 
      (1 - phi) * (L j * (inverse sqp - inverse (grd P (j+1)))) + 
      (1 - phi) * sum (\<lambda> i. L i * (inverse (grd P i) - inverse (grd P (i+1)))) 
      {i. (lq P) i \<noteq> 0 \<and> j <i \<and> i < k} +
      (1 - phi) * (L k * (inverse (grd P k) - inverse sqp'))" 
    by simp
  also have "... = (1 - phi) * 
      (L j * (inverse sqp - inverse (grd P (j+1))) + 
      sum (\<lambda> i. L i * (inverse (grd P i) - inverse (grd P (i+1)))) 
      {i. (lq P) i \<noteq> 0 \<and> j <i \<and> i < k} +
      L k * (inverse (grd P k) - inverse sqp'))"
    by (simp add: ring_class.ring_distribs(1))
  also have "... = (1 - phi) * (base_gross P sqp - base_gross P sqp')"
  proof -
    have "L j * (inverse sqp - inverse (grd P (j+1))) + 
        sum (\<lambda> i. L i * (inverse (grd P i) - inverse (grd P (i+1)))) 
        {i. (lq P) i \<noteq> 0 \<and> j <i \<and> i < k} +
        L k * (inverse (grd P k) - inverse sqp') = 
        L j * (inverse sqp - inverse (grd P (j+1))) + 
        sum (\<lambda> i. L i * (inverse (grd P i) - inverse (grd P (i+1)))) 
        {i. L i \<noteq> 0 \<and> j <i \<and> i < k} +
        L k * (inverse (grd P k) - inverse sqp')" 
    proof -
      have "{i. (lq P) i \<noteq> 0 \<and> j <i \<and> i < k} = {i. L i \<noteq> 0 \<and> j <i \<and> i < k}"
        using L_def assms(1) clmm_dsc_gross_liq_zero_iff by presburger
      thus ?thesis by simp
    qed
    also have "... = base_gross P sqp - base_gross P sqp'"
      using assms base_gross_diff_eq L_def by simp
    finally have "L j * (inverse sqp - inverse (grd P (j+1))) + 
        sum (\<lambda> i. L i * (inverse (grd P i) - inverse (grd P (i+1)))) 
        {i. (lq P) i \<noteq> 0 \<and> j <i \<and> i < k} +
        L k * (inverse (grd P k) - inverse sqp') =
        base_gross P sqp - base_gross P sqp'" .
    thus ?thesis by simp
  qed
  finally show ?thesis .
qed

lemma cst_fee_base_gross_net:
  assumes "clmm_dsc P"
  and "\<And>i. fee P i = phi"
  and "0 < sqp"
  and "sqp \<le> sqp'"
shows "base_net P sqp - base_net P sqp' = 
    (1 - phi) * (base_gross P sqp - base_gross P sqp')" 
proof (cases "lower_tick P sqp = lower_tick P sqp'")
  case True
  then show ?thesis using assms cst_fee_base_gross_net_tick_eq by simp
next
  case False
  hence "lower_tick P sqp < lower_tick P sqp'"
    using assms lower_tick_mono by fastforce
  then show ?thesis using assms cst_fee_base_gross_net_tick_lt by simp
qed

lemma base_net_eq_only_if:
  assumes "clmm_dsc P"
  and "j = lower_tick P sqp"
  and "k = lower_tick P sqp'"
  and "0 < sqp"
  and "sqp \<le> sqp'"
  and "j < k"
  and "quote_gross P sqp' = quote_gross P sqp"
shows "base_net P sqp' = base_net P sqp" 
proof -
  define L where "L = lq P"
  define L' where "L' = gross_fct (lq P) (fee P)"
  have "base_net P sqp - base_net P sqp' = 
      L j * (inverse sqp - inverse (grd P (j+1))) + 
      sum (\<lambda> i. L i * (inverse (grd P i) - inverse (grd P (i+1)))) 
      {i. L i \<noteq> 0 \<and> j <i \<and> i < k} +
      L k * (inverse (grd P k) - inverse sqp')"
    using assms base_net_diff_eq L_def by simp
  also have "... = L j * (inverse sqp - inverse (grd P (j+1))) +
      L k * (inverse (grd P k) - inverse sqp')"
  proof -
    have "{i. L i \<noteq> 0 \<and> j <i \<and> i < k} = {}" 
      using clmm_quote_gross_eq_sum_emp assms L_def clmm_dsc_gross_liq_zero_iff 
      by presburger
    hence "sum (\<lambda> i. L i * (inverse (grd P i) - inverse (grd P (i+1)))) 
        {i. L i \<noteq> 0 \<and> j <i \<and> i < k} = 0"
      by (metis (full_types) sum_clauses(1))
    thus ?thesis by simp
  qed
  also have "... = L k * (inverse (grd P k) - inverse sqp')"
  proof -
    have "L' j = 0" using assms L'_def clmm_quote_gross_eq_lower_only_if by simp
    hence "L j = 0" 
      using L_def L'_def clmm_dsc_gross_liq_zero_iff assms by simp
    thus ?thesis by simp
  qed
  also have "... = 0"
  proof -
    have "L k * (inverse (grd P k) - inverse sqp') = 0" 
      using clmm_quote_gross_eq_upper_only_if assms L_def 
        clmm_dsc_gross_liq_zero_iff 
      by auto
    thus ?thesis by simp
  qed
  finally show ?thesis by simp
qed

lemma base_net_eq_only_if':
  assumes "clmm_dsc P"
  and "L = lq P"
  and "j = lower_tick P sqp"
  and "j = lower_tick P sqp'"
  and "0 < sqp"
  and "sqp \<le> sqp'"
  and "quote_gross P sqp = quote_gross P sqp'"
shows "base_net P sqp = base_net P sqp'"
proof -
  have "base_net P sqp - base_net P sqp' = L j * (inverse sqp - inverse sqp')" 
    using base_net_diff_eq' assms by simp
  also have "... = 0"
  proof (cases "sqp = sqp'")
    case True
    then show ?thesis by simp
  next
    case False
    hence "gross_fct (lq P) (fee P) j = 0" 
      using assms clmm_quote_gross_eq_lower_only_if' by simp
    hence "L j = 0" using assms
      by (simp add: clmm_dsc_gross_liq_zero_iff) 
    then show ?thesis by simp
  qed
  finally show ?thesis by simp
qed

lemma quote_gross_equiv_base_net:
  assumes "clmm_dsc P"
  and "0 < sqp"
  and "sqp \<le> sqp'"
  and "quote_gross P sqp = quote_gross P sqp'"
shows "base_net P sqp = base_net P sqp'"
proof (cases "lower_tick P sqp = lower_tick P sqp'")
  case True
  then show ?thesis 
    using assms base_net_eq_only_if'[of P "lq P" _ sqp  sqp'] by simp
next
  case False
  hence "lower_tick P sqp < lower_tick P sqp'"
    by (meson antisym_conv3 assms(1-3) leD lower_tick_lt)
  then show ?thesis using assms base_net_eq_only_if by simp
qed

lemma quote_gross_equiv_base_net':
  assumes "clmm_dsc P"
  and "0 < sqp"
  and "0 < sqp'"
  and "quote_gross P sqp = quote_gross P sqp'"
shows "base_net P sqp = base_net P sqp'"
proof (cases "sqp \<le> sqp'")
  case True
  thus ?thesis using quote_gross_equiv_base_net assms by simp
next
  case False
  then show ?thesis using quote_gross_equiv_base_net assms
    by (metis linorder_le_cases)
qed

lemma (in finite_nz_support) gen_quote_le_badd:
  assumes "clmm_dsc P"
  and "\<And>i. 0 \<le> L i"
  and "0 < sqp"
  and "sqp \<le> sqp'"
shows "gen_quote_diff P L sqp sqp'/(sqp' * sqp') \<le> gen_base_diff P L sqp sqp'"
proof -
  have "0 < sqp'" using assms by simp
  define j where "j = lower_tick P sqp"
  define k where "k = lower_tick P sqp'"
  show ?thesis
  proof (cases "j = k")
    case True
    hence "gen_quote_diff P L sqp sqp' / (sqp' * sqp') = 
        L j * (sqp' - sqp)/ (sqp' * sqp')" 
      using assms j_def k_def clmm_gen_quote_diff_eq' by simp  
    also have "... \<le> L j * (inverse sqp - inverse sqp')"
      by (rule diff_inv_le', (auto simp add: assms))
    also have "... = gen_base_diff P L sqp sqp'"
      using assms j_def k_def gen_base_diff_eq' True by simp
    finally show ?thesis .
  next
    case False
    hence "j < k" using j_def k_def lower_tick_mono assms by fastforce
    hence "gen_quote_diff P L sqp sqp' / (sqp' * sqp') = 
        (L k * (sqp' - grd P k) + 
        (\<Sum>i | L i \<noteq> 0 \<and> j < i \<and> i < k. L i * (grd P (i + 1) - grd P i)) +
        L j * (grd P (j + 1) - sqp))/ (sqp' * sqp')" 
      using assms j_def k_def clmm_gen_quote_diff_eq by simp
    also have "... = L k * (sqp' - grd P k) / (sqp' * sqp') +
        (\<Sum>i | L i \<noteq> 0 \<and> j < i \<and> i < k. 
        L i * (grd P (i + 1) - grd P i)) / (sqp' * sqp') +
        L j * (grd P (j + 1) - sqp) / (sqp' * sqp')"
      by (simp add: add_divide_distrib)
    also have "... \<le> L k * (inverse (grd P k) - inverse sqp')  +
        (\<Sum>i | L i \<noteq> 0 \<and> j < i \<and> i < k. 
        L i * (inverse (grd P i) - inverse (grd P (i + 1)))) +
        L j * (inverse sqp - inverse (grd P (j + 1)))"
    proof -
      have "(\<Sum>i | L i \<noteq> 0 \<and> j < i \<and> i < k. 
        L i * (grd P (i + 1) - grd P i)) / (sqp' * sqp') \<le> 
        (\<Sum>i | L i \<noteq> 0 \<and> j < i \<and> i < k. 
          L i * (inverse (grd P i) - inverse (grd P (i + 1))))" 
      proof (rule diff_inv_sum_le')
        show "\<forall>i\<in>{i. L i \<noteq> 0 \<and> j < i \<and> i < k}. 0 < grd P i" using assms by simp
        show "\<forall>i\<in>{i. L i \<noteq> 0 \<and> j < i \<and> i < k}. 0 \<le> L i" using assms by simp
        show "\<forall>i\<in>{i. L i \<noteq> 0 \<and> j < i \<and> i < k}. grd P i \<le> grd P (i + 1)" 
          using assms clmm_dsc_grd_Suc[of P] less_eq_real_def by blast 
        {
          fix i
          assume "i\<in>{i. L i \<noteq> 0 \<and> j < i \<and> i < k}"
          hence "i+1 \<le> k" by simp
          hence "grd P (i+1) \<le> grd P k" 
            using assms clmm_dsc_grid(1) strict_mono_leD by blast
          hence "grd P (i + 1) \<le> sqp'" 
            using k_def lower_tick_lbound assms \<open>0 < sqp'\<close> by fastforce
        }
        thus "\<forall>i\<in>{i. L i \<noteq> 0 \<and> j < i \<and> i < k}. grd P (i + 1) \<le> sqp'" by simp
      qed      
      moreover have "L k * (sqp' - grd P k) / (sqp' * sqp') \<le> 
          L k * (inverse (grd P k) - inverse sqp')"
      proof (rule diff_inv_le') 
        show "grd P k \<le> sqp'" using k_def lower_tick_lbound assms by simp
      qed (simp add: assms)+     
      moreover have "L j * (grd P (j + 1) - sqp) / (sqp' * sqp') \<le>
          L j * (inverse sqp - inverse (grd P (j + 1)))"
      proof (rule diff_inv_le')
        show "sqp \<le> grd P (j + 1)" 
          using j_def lower_tick_ubound assms by fastforce
        have "j+1 \<le> k" using \<open>j < k\<close> by simp
        hence "grd P (j+1) \<le> grd P k" using assms
          by (simp add: strict_mono_leD) 
        thus "grd P (j + 1) \<le> sqp'" 
          using \<open>j < k\<close> k_def lower_tick_lbound assms \<open>0 < sqp'\<close> by fastforce
      qed (simp add: assms)+
      ultimately show ?thesis by simp
    qed
    also have "... =  L j * (inverse sqp - inverse (grd P (j + 1))) + 
        (\<Sum>i | L i \<noteq> 0 \<and> j < i \<and> i < k. 
        L i * (inverse (grd P i) - inverse (grd P (i + 1)))) +
        L k * (inverse (grd P k) - inverse sqp')" 
      by simp
    also have "... = gen_base_diff P L sqp sqp'" 
      using assms \<open>j < k\<close> j_def k_def gen_base_diff_eq by simp
    finally show ?thesis .
  qed
qed

lemma (in finite_nz_support) gen_base_le_qadd:
  assumes "clmm_dsc P"
  and "\<And>i. 0 \<le> L i"
  and "0 < sqp"
  and "sqp \<le> sqp'"
shows "gen_base_diff P L sqp sqp' \<le> gen_quote_diff P L sqp sqp'/(sqp * sqp)"
proof -
  define j where "j = lower_tick P sqp"
  define k where "k = lower_tick P sqp'"
  show ?thesis
  proof (cases "j = k")
    case True
    hence "gen_base_diff P L sqp sqp' = L j * (inverse sqp - inverse sqp')"
      using assms j_def k_def gen_base_diff_eq' True by simp
    also have "... \<le>  L j * (sqp' - sqp)/ (sqp * sqp)"
      by (rule diff_inv_ge', (auto simp add: assms))
    also have "... = gen_quote_diff P L sqp sqp' / (sqp * sqp)"
      using assms j_def k_def clmm_gen_quote_diff_eq' True by simp 
    finally show ?thesis .
  next
    case False
    hence "j < k" using j_def k_def lower_tick_mono assms by fastforce
    hence "gen_base_diff P L sqp sqp' = 
        L j * (inverse sqp - inverse (grd P (j + 1))) + 
        (\<Sum>i | L i \<noteq> 0 \<and> j < i \<and> i < k. 
        L i * (inverse (grd P i) - inverse (grd P (i + 1)))) +
        L k * (inverse (grd P k) - inverse sqp')" 
      using assms j_def k_def gen_base_diff_eq by simp
    also have "... = L k * (inverse (grd P k) - inverse sqp')  +
        (\<Sum>i | L i \<noteq> 0 \<and> j < i \<and> i < k. 
        L i * (inverse (grd P i) - inverse (grd P (i + 1)))) +
        L j * (inverse sqp - inverse (grd P (j + 1)))" 
      by simp
    also have "... \<le> L k * (sqp' - grd P k) / (sqp * sqp) +
        (\<Sum>i | L i \<noteq> 0 \<and> j < i \<and> i < k. 
        L i * (grd P (i + 1) - grd P i)) / (sqp * sqp) +
        L j * (grd P (j + 1) - sqp) / (sqp * sqp)" 
    proof -
      have "(\<Sum>i | L i \<noteq> 0 \<and> j < i \<and> i < k. 
          L i * (inverse (grd P i) - inverse (grd P (i + 1)))) \<le> 
          (\<Sum>i | L i \<noteq> 0 \<and> j < i \<and> i < k. 
          L i * (grd P (i + 1) - grd P i)) / (sqp * sqp)" 
      proof (rule diff_inv_sum_ge')
        show "0 < sqp" using assms by simp
        show "\<forall>i\<in>{i. L i \<noteq> 0 \<and> j < i \<and> i < k}. 0 \<le> L i" using assms by simp
        show "\<forall>i\<in>{i. L i \<noteq> 0 \<and> j < i \<and> i < k}. grd P i \<le> grd P (i + 1)" 
          using assms clmm_dsc_grd_Suc[of P] less_eq_real_def by blast 
        {
          fix i
          assume "i\<in>{i. L i \<noteq> 0 \<and> j < i \<and> i < k}"
          hence "j + 1 \<le> i" by simp
          hence "grd P (j+1) \<le> grd P i" using assms clmm_dsc_grid(1)
            by (simp add: strict_mono_leD)
          hence "sqp \<le> grd P i" 
            using assms j_def lower_tick_ubound by fastforce
        }
        thus "\<forall>i\<in>{i. L i \<noteq> 0 \<and> j < i \<and> i < k}. sqp \<le> grd P i" by simp
      qed      
      moreover have "L k * (inverse (grd P k) - inverse sqp') \<le> 
          L k * (sqp' - grd P k) / (sqp * sqp)"
      proof (rule diff_inv_ge') 
        show "grd P k \<le> sqp'" using k_def lower_tick_lbound assms by simp
        have "j+1 \<le> k" using \<open>j < k\<close> by simp
        hence "grd P (j+1) \<le> grd P k" using clmm_dsc_grd_mono assms by simp
        thus "sqp \<le> grd P k" using j_def lower_tick_ubound assms by fastforce
      qed (simp add: assms)+
      moreover have "L j * (inverse sqp - inverse (grd P (j + 1))) \<le> 
          L j * (grd P (j + 1) - sqp) / (sqp * sqp)"
      proof (rule diff_inv_ge')
        show "sqp \<le> grd P (j + 1)" 
          using j_def lower_tick_ubound assms by fastforce
      qed (simp add: assms)+
      ultimately show ?thesis by simp
    qed
    also have "... = (L k * (sqp' - grd P k) + 
        (\<Sum>i | L i \<noteq> 0 \<and> j < i \<and> i < k. L i * (grd P (i + 1) - grd P i)) +
        L j * (grd P (j + 1) - sqp))/ (sqp * sqp)"
      by (simp add: add_divide_distrib)
    also have "... = gen_quote_diff P L sqp sqp' / (sqp * sqp)"
      using assms j_def k_def clmm_gen_quote_diff_eq \<open>j < k\<close> by simp
    finally show ?thesis .
  qed
qed

lemma quote_swap_grd_min_zero:
  assumes "clmm_dsc P"
  and "nz_support (lq P) \<noteq> {}"
  and "grd_min P \<le> sqp"
  and "sqp \<le> grd_max P"
  shows "quote_swap P sqp 0 = 0" 
proof -
  define sqp' where "sqp' = quote_reach P (0 + quote_gross P sqp)"
  have "base_net P sqp = base_net P sqp'"
  proof (rule quote_gross_equiv_base_net[symmetric])
    show "clmm_dsc P" using assms by simp
    show "0 < sqp'" 
    proof (rule clmm_quote_reach_pos)
      show "clmm_dsc P" using assms by simp
      show "nz_support (lq P) \<noteq> {}" using assms by simp
      show "0 \<le> 0 + quote_gross P sqp"
        by (simp add: assms(1) clmm_quote_gross_pos)
      show "sqp' = quote_reach P (0 + quote_gross P sqp)" 
        using sqp'_def by simp
      show "0 + quote_gross P sqp \<le> quote_gross P (grd_max P)"
        by (metis add_0 assms(1) assms(4) quote_gross_imp_sqp_lt 
            less_eq_real_def nle_le)
    qed
    show "sqp' \<le> sqp" using sqp'_def clmm_quote_reach_le assms
      by (metis add_0 clmm_quote_gross_pos clmm_quote_reach_zero 
          order_le_imp_less_or_eq vimage_singleton_eq)
    show "quote_gross P sqp' = quote_gross P sqp"
      by (simp add: assms(1) assms(2) clmm_quote_gross_pos 
          quote_gross_grd_max_max clmm_quote_gross_reach_eq sqp'_def) 
  qed
  thus ?thesis unfolding quote_swap_def sqp'_def by simp
qed

lemma quote_swap_zero:
  assumes "clmm_dsc P"
  and "nz_support (lq P) \<noteq> {}"
  and "0< sqp"
  and "sqp \<le> grd_max P"
shows "quote_swap P sqp 0 = 0" 
proof (cases "sqp < grd_min P")
  case True
  hence a: "base_net P sqp = base_net P (grd_min P)"
    by (simp add: assms(1) assms(3) base_net_grd_min_lt)
  have "quote_gross P sqp = 0" using True
    by (simp add: assms(1) assms(3) clmm_quote_gross_grd_min_le)
  hence "quote_reach P (0 + quote_gross P sqp) = grd_min P" 
    using clmm_quote_reach_zero assms by simp
  then show ?thesis using a unfolding quote_swap_def by simp
next
  case False
  then show ?thesis using assms quote_swap_grd_min_zero by simp
qed

lemma quote_swap_grd_min_zero':
  assumes "clmm_dsc P"
  and "nz_support (lq P) \<noteq> {}"
  and "grd_min P \<le> sqp"
  and "quote_gross P sqp \<le> quote_gross P (grd_max P)"
  shows "quote_swap P sqp 0 = 0" 
proof -
  define sqp' where "sqp' = quote_reach P (0 + quote_gross P sqp)"
  have "base_net P sqp = base_net P sqp'"
  proof (rule quote_gross_equiv_base_net[symmetric])
    show "clmm_dsc P" using assms by simp
    show "0 < sqp'" 
    proof (rule clmm_quote_reach_pos)
      show "clmm_dsc P" using assms by simp
      show "nz_support (lq P) \<noteq> {}" using assms by simp
      show "0 \<le> 0 + quote_gross P sqp"
        by (simp add: assms(1) clmm_quote_gross_pos)
      show "sqp' = quote_reach P (0 + quote_gross P sqp)" 
        using sqp'_def by simp
      show "0 + quote_gross P sqp \<le> quote_gross P (grd_max P)"
        using assms by simp
    qed
    show "sqp' \<le> sqp" using sqp'_def clmm_quote_reach_le assms
      by (metis add_0 clmm_quote_gross_pos clmm_quote_reach_zero 
          order_le_imp_less_or_eq vimage_singleton_eq)
    show "quote_gross P sqp' = quote_gross P sqp"
      by (simp add: assms(1) assms(2) clmm_quote_gross_pos 
          quote_gross_grd_max_max clmm_quote_gross_reach_eq sqp'_def) 
  qed
  thus ?thesis unfolding quote_swap_def sqp'_def by simp
qed

lemma quote_swap_zero':
  assumes "clmm_dsc P"
  and "nz_support (lq P) \<noteq> {}"
  and "0< sqp"
  and "quote_gross P sqp \<le> quote_gross P (grd_max P)"
shows "quote_swap P sqp 0 = 0" 
proof (cases "sqp < grd_min P")
  case True
  hence a: "base_net P sqp = base_net P (grd_min P)"
    by (simp add: assms(1) assms(3) base_net_grd_min_lt)
  have "quote_gross P sqp = 0" using True
    by (simp add: assms(1) assms(3) clmm_quote_gross_grd_min_le)
  hence "quote_reach P (0 + quote_gross P sqp) = grd_min P" 
    using clmm_quote_reach_zero assms by simp
  then show ?thesis using a unfolding quote_swap_def by simp
next
  case False
  then show ?thesis using assms quote_swap_grd_min_zero' by simp
qed

lemma quote_swap_grd_min:
  assumes "clmm_dsc P"
  and "nz_support (lq P) \<noteq> {}"
  and "sqp < grd_min P"
  and "0 < sqp"
shows "quote_swap P sqp y = quote_swap P (grd_min P) y"
proof -
  have "quote_gross P sqp = quote_gross P (grd_min P)" using assms
    by (simp add: clmm_quote_gross_grd_min_le)
  moreover have "base_net P sqp = base_net P (grd_min P)" 
    using base_net_grd_min_lt assms by simp
  ultimately show ?thesis  unfolding quote_swap_def by simp
qed

lemma quote_reach_gross_base_net:
  assumes "clmm_dsc P"
  and "nz_support (lq P) \<noteq> {}"
  and "0 < quote_gross P sqp"
  and "sqp' = quote_reach P (quote_gross P sqp)"
shows "base_net P sqp' = base_net P sqp"
proof (rule quote_gross_equiv_base_net)
  have "quote_gross P sqp \<le> quote_gross P (grd_max P)" 
    using quote_gross_grd_max_max assms by simp
  thus "quote_gross P sqp' = quote_gross P sqp" 
    using clmm_quote_gross_reach_eq assms by simp
  show "clmm_dsc P" using assms by simp
  show "0 < sqp'" 
  proof (rule clmm_quote_reach_pos)
    show "clmm_dsc P" using assms by simp
    show "nz_support (lq P) \<noteq> {}" using assms by simp
    show "sqp' = quote_reach P (quote_gross P sqp)" 
      using assms by simp
    show "0 \<le> quote_gross P sqp"
      by (simp add: assms(1) clmm_quote_gross_pos) 
    show "quote_gross P sqp \<le> quote_gross P (grd_max P)" 
      using assms quote_gross_grd_max_max by simp
  qed
  show "sqp' \<le> sqp" using assms clmm_quote_reach_le by simp
qed

lemma quote_reach_base_net:
  assumes "clmm_dsc P"
  and "nz_support (lq P) \<noteq> {}"
  and "0 < sqp"
  and "sqp' = quote_reach P (quote_gross P sqp)"
shows "base_net P sqp' = base_net P sqp"
proof (cases "quote_gross P sqp = 0")
  case True
  hence "sqp' = grd_min P"
    by (simp add: assms clmm_quote_reach_zero)
  have "base_net P sqp = base_net P sqp'" 
  proof (rule quote_gross_equiv_base_net)
    show "sqp \<le> sqp'" using \<open>sqp' = grd_min P\<close> True
      by (metis assms(1) assms(2) linorder_not_less quote_gross_gt_grd_min 
          verit_comp_simplify1(1))
    show "clmm_dsc P" using assms by simp
    show "0 < sqp" using assms by simp
    show "quote_gross P sqp = quote_gross P sqp'" using True
      by (simp add: \<open>sqp' = grd_min P\<close> assms(1) assms(2) clmm_quote_gross_grd_min)
  qed
  thus ?thesis by simp
next
  case False
  hence "0 < quote_gross P sqp"
    by (meson assms(1) clmm_quote_gross_pos leI order_antisym_conv)
  then show ?thesis using assms quote_reach_gross_base_net by simp
qed

lemma base_le_quote_gross:
  assumes "clmm_dsc P'"  
  and "0 < sqp"
  and "sqp \<le> sqp'"
  shows "base_gross P' sqp - base_gross P' sqp' \<le> 
    (quote_gross P' sqp' - quote_gross P' sqp)/(sqp * sqp)"  
proof -
  define L where "L = gross_fct (lq P') (fee P')" 
  have "base_gross P' sqp - base_gross P' sqp' = gen_base_diff P' L sqp sqp'" 
    using gen_base_diff_def base_gross_def L_def by simp
  also have "...  \<le> gen_quote_diff P' L sqp sqp' / (sqp * sqp)"  
  proof (rule finite_nz_support.gen_base_le_qadd)
    show "finite_nz_support L" 
      using L_def assms(1) clmm_dsc_gross_liq clmm_dsc_liq(1) finite_liq_def 
        finite_nz_support.intro 
      by auto
    show "\<And>i. 0 \<le> L i" using L_def assms(1) gross_liq_ge by simp
  qed (simp add: assms)+
  also have "... = (quote_gross P' sqp' - quote_gross P' sqp)/(sqp * sqp)"
    using gen_quote_diff_def quote_gross_def L_def by simp
  finally show ?thesis .
qed

lemma quote_le_base_gross:
  assumes "clmm_dsc P'"  
  and "0 < sqp"
  and "sqp \<le> sqp'"
shows "(quote_gross P' sqp' - quote_gross P' sqp)/(sqp' * sqp') \<le> 
    base_gross P' sqp - base_gross P' sqp'"  
proof -
  define L where "L = gross_fct (lq P') (fee P')"
  have "(quote_gross P' sqp' - quote_gross P' sqp)/(sqp' * sqp') = 
      gen_quote_diff P' L sqp sqp' / (sqp' * sqp')" 
    using gen_quote_diff_def quote_gross_def L_def by simp
  also have "... \<le> gen_base_diff P' L sqp sqp'" 
  proof (rule finite_nz_support.gen_quote_le_badd)
    show "finite_nz_support L" 
      using L_def assms(1) clmm_dsc_gross_liq clmm_dsc_liq(1) finite_liq_def 
        finite_nz_support.intro 
      by auto
    show "\<And>i. 0 \<le> L i" using L_def assms(1) gross_liq_ge by simp
  qed (simp add: assms)+
  also have "... = base_gross P' sqp - base_gross P' sqp'"
    using gen_base_diff_def base_gross_def L_def by simp
  finally show ?thesis .
qed

lemma base_net_quote_ubound:
  assumes "clmm_dsc P'"
  and "\<And>i. fee P' i = phi"
  and "phi < 1"
  and "0 < sqp"
  and "sqp \<le> sqp'"
  shows "base_net P' sqp - base_net P' sqp' \<le> 
      (1 - phi) * (quote_gross P' sqp' - quote_gross P' sqp)/(sqp * sqp)"
proof -
  have "base_net P' sqp - base_net P' sqp' = 
      (1 - phi) * (base_gross P' sqp - base_gross P' sqp')"
    by (rule cst_fee_base_gross_net, (auto simp add: assms))
  also have "... \<le> (1 - phi) * (quote_gross P' sqp' - quote_gross P' sqp)/(sqp * sqp)"
    using base_le_quote_gross assms
    by (metis ge_iff_diff_ge_0 less_eq_real_def mult_left_mono 
        times_divide_eq_right) 
  finally show ?thesis .
qed

lemma base_net_quote_lbound:
  assumes "clmm_dsc P'"
  and "\<And>i. fee P' i = phi"  
  and "0 < sqp"
  and "sqp \<le> sqp'"
shows "(1 - phi) * (quote_gross P' sqp' - quote_gross P' sqp)/(sqp' * sqp') \<le> 
    base_net P' sqp - base_net P' sqp'" 
proof -
  have "phi < 1" using assms by (metis clmm_dsc_fees)
  hence "(1 - phi) * (quote_gross P' sqp' - quote_gross P' sqp)/(sqp' * sqp') \<le> 
      (1 - phi) * (base_gross P' sqp - base_gross P' sqp')"
    using quote_le_base_gross assms
    by (metis diff_gt_0_iff_gt mult_le_cancel_left_pos times_divide_eq_right)
  also have "... = base_net P' sqp - base_net P' sqp'"
    by (rule cst_fee_base_gross_net[symmetric], (auto simp add: assms))
  finally show ?thesis .
qed

subsection \<open>Market depth and slippage for finer CLMMs\<close>
subsubsection \<open>Finer pools\<close>

locale finer_clmm =
  fixes P1 P2
  assumes abs1: "clmm_dsc P1" and abs2: "clmm_dsc P2"
  and finer: "finer_pool P1 P2"

sublocale finer_clmm \<subseteq> finer_two_span_finite_liq
  by (meson abs1 abs2 clmm_dsc_def finer finer_pools.intro 
      finer_spanning_pool.intro finer_spanning_pool_axioms.intro 
      finer_two_span_finite_liq.intro finer_two_span_finite_liq_axioms.intro 
      finer_two_spanning_pools.intro finer_two_spanning_pools_axioms.intro)

context finer_clmm
begin

lemma finer_base_net_eq:
shows "base_net P1 = base_net P2"
proof -
  have "\<And>a b. a \<in> encompassed (grd P1) (grd P2) b \<Longrightarrow> lq P1 a = lq P2 b"
    using  encompassed_liq_eq
    by (simp add: mon stm)
  thus ?thesis unfolding base_net_def
    using spanning_finer_gen_base_eq[of "\<lambda>x. x" "\<lambda>x. x"] 
    clmm_dsc_grid clmm_dsc_liq by blast
qed

lemma finer_quote_net_eq:
shows "quote_net P1 = quote_net P2" 
proof -
  have "\<And>a b. a \<in> encompassed (grd P1) (grd P2) b \<Longrightarrow> lq P1 a = lq P2 b"
    using encompassed_liq_eq
    by (simp add: mon stm)
  thus ?thesis unfolding quote_net_def 
    using spanning_finer_gen_quote_eq[of "\<lambda>x. x" "\<lambda>x. x"] 
    clmm_dsc_grid clmm_dsc_liq by blast
qed

lemma finer_base_gross_eq:
shows "base_gross P1 = base_gross P2" 
proof -
  have "base_gross P1 = gen_base (grd P2) ((\<lambda>x. gross_fct x (fee P2)) (lq P2))"
    unfolding base_gross_def
  proof 
    fix x
    show "gen_base (grd P1) ((\<lambda>x. gross_fct x (fee P1)) (lq P1)) x =
      gen_base (grd P2) ((\<lambda>x. gross_fct x (fee P2)) (lq P2)) x" 
    proof (rule spanning_finer_gen_base_eq)
      show "\<And>i. lq P2 i = 0 \<Longrightarrow> gross_fct (lq P2) (fee P2) i = 0"
        using gross_fct_zero_if by simp
      show "\<And>i. lq P1 i = 0 \<Longrightarrow> gross_fct (lq P1) (fee P1) i = 0"
        using gross_fct_zero_if by simp
      show "\<And>a b. a \<in> encompassed (grd P1) (grd P2) b \<Longrightarrow> 
        gross_fct (lq P1) (fee P1) a = gross_fct (lq P2) (fee P2) b" 
      proof -
        fix a b
        assume asm: "a \<in> encompassed (grd P1) (grd P2) b"
        hence "lq P1 a = lq P2 b"
          by (simp add: span span2 encompassed_liq_eq 
              span_gridD(1) strict_mono_mono)
        moreover have "fee P1 a = fee P2 b"
          by (simp add: asm span span2 encompassed_fee_eq span_gridD(1) 
              strict_mono_mono)
        ultimately show "gross_fct (lq P1) (fee P1) a = 
          gross_fct (lq P2) (fee P2) b"
          using gross_fct_cong by metis
      qed
    qed
  qed 
  also have "... = base_gross P2" unfolding base_gross_def by simp
  finally show ?thesis .
qed

lemma finer_quote_gross_eq:
shows "quote_gross P1 = quote_gross P2" 
proof -
  have "quote_gross P1 = gen_quote (grd P2) ((\<lambda>x. gross_fct x (fee P2)) (lq P2))"
    unfolding quote_gross_def
  proof 
    fix x
    show "gen_quote (grd P1) ((\<lambda>x. gross_fct x (fee P1)) (lq P1)) x =
      gen_quote (grd P2) ((\<lambda>x. gross_fct x (fee P2)) (lq P2)) x" 
    proof (rule spanning_finer_gen_quote_eq)
      show "\<And>i. lq P2 i = 0 \<Longrightarrow> gross_fct (lq P2) (fee P2) i = 0"
        using gross_fct_zero_if by simp
      show "\<And>i. lq P1 i = 0 \<Longrightarrow> gross_fct (lq P1) (fee P1) i = 0"
        using gross_fct_zero_if by simp
      show "\<And>a b. a \<in> encompassed (grd P1) (grd P2) b \<Longrightarrow> 
        gross_fct (lq P1) (fee P1) a = gross_fct (lq P2) (fee P2) b" 
      proof -
        fix a b
        assume asm: "a \<in> encompassed (grd P1) (grd P2) b"
        hence "lq P1 a = lq P2 b"
          by (simp add: span span2 encompassed_liq_eq span_gridD(1) 
              strict_mono_mono)
        moreover have "fee P1 a = fee P2 b"
          by (simp add: asm span span2 encompassed_fee_eq span_gridD(1) 
              strict_mono_mono)
        ultimately show "gross_fct (lq P1) (fee P1) a = 
          gross_fct (lq P2) (fee P2) b"
          using gross_fct_cong by metis
      qed
    qed
  qed 
  also have "... = quote_gross P2" unfolding quote_gross_def by simp
  finally show ?thesis .
qed

lemma finer_mkt_depth:
shows "mkt_depth P1 = mkt_depth P2" 
  using  finer_base_net_eq finer_quote_net_eq unfolding mkt_depth_def by presburger

end

subsubsection \<open>Finer CLMMs with nonzero liquidity\<close>

locale finer_clmm_ne = finer_clmm +
  assumes nonempty_liq: "nz_support (lq P1) \<noteq> {}"

context finer_clmm_ne
begin

lemma id_max_Max_eq:
  assumes "i1 =  idx_max (lq P1)"
  and "k2 = pool_coarse_idx P1 P2 i1"
shows "i1 = Max (encompassed (grd P1) (grd P2) k2)" 
proof (rule ccontr)
  assume asm: "i1 \<noteq> Max (encompassed (grd P1) (grd P2) k2)"
  interpret finer_ranges "grd P1" "grd P2" 
  proof (rule finer_ranges.intro)
    show "strict_mono (grd P1)" using span span_gridD by simp
    show "mono (grd P2)" using span2
      by (simp add: span_gridD strict_mono_on_imp_mono_on)
    show "finer_range (grd P1) (grd P2)" using assms
      by (simp add: finer_pool_grid) 
  qed
  have "lq P1 (i1 + 1) = 0" using  idx_max_finite_gt assms clmm_dsc_liq 
      finite_liqD nz_support_def nonempty_liq
    by (metis less_add_one fin_liq)
  have "i1 \<in> encompassed (grd P1) (grd P2) k2" 
    using encompassed_bounds assms pool_coarse_idxD by auto
  hence "i1 < Max (encompassed (grd P1) (grd P2) k2)" using asm
    by (meson Max.coboundedI fin linorder_less_linear linorder_not_less 
        span_grid_encompassed)
  hence "i1 + 1 \<le> Max (encompassed (grd P1) (grd P2) k2)" by simp
  have "Max (encompassed (grd P1) (grd P2) k2) \<in> 
    encompassed (grd P1) (grd P2) k2"
    by (metis Max_in \<open>i1 \<in> encompassed (grd P1) (grd P2) k2\<close>  
        emptyE span_grid_encompassed)    
  hence "i1 + 1 \<in> encompassed (grd P1) (grd P2) k2" 
    using \<open>i1 \<in> encompassed (grd P1) (grd P2) k2\<close> encompassed_convex
    \<open>i1 + 1 \<le> Max (encompassed (grd P1) (grd P2) k2)\<close> stm strict_mono_mono 
    by fastforce
  hence "lq P1 (i1 + 1) = lq P2 k2"
    by (simp add: assms(2) encompassed_liq_eq mon stm)
  also have "... = lq P1 i1" 
    using \<open>i1 \<in> encompassed (grd P1) (grd P2) k2\<close> assms finer_pool_liq 
    by auto
  also have "... \<noteq> 0" using span assms nonempty_liq fin_liq finite_liq_def 
      idx_max_finite_in by blast
  finally show False using \<open>lq P1 (i1 + 1) = 0\<close> by simp
qed

lemma id_min_Min_eq:
  assumes "i1 =  idx_min (lq P1)"
  and "k2 = pool_coarse_idx P1 P2 i1"
shows "i1 = Min (encompassed (grd P1) (grd P2) k2)" 
proof (rule ccontr)
  assume asm: "i1 \<noteq> Min (encompassed (grd P1) (grd P2) k2)"
  have "lq P1 (i1 - 1) = 0" using  idx_min_finite_lt assms clmm_dsc_liq 
      finite_liqD nz_support_def nonempty_liq
    by (metis order_refl fin_liq zle_diff1_eq)
  have "i1 \<in> encompassed (grd P1) (grd P2) k2" 
    using encompassed_bounds assms pool_coarse_idxD by auto
  hence "Min (encompassed (grd P1) (grd P2) k2) < i1" using asm
    by (meson Min.coboundedI fin linorder_less_linear linorder_not_less 
        span_grid_encompassed)
  hence "Min (encompassed (grd P1) (grd P2) k2) \<le> i1-1" by simp
  have "Min (encompassed (grd P1) (grd P2) k2) \<in> 
    encompassed (grd P1) (grd P2) k2"
    by (metis Min_in \<open>i1 \<in> encompassed (grd P1) (grd P2) k2\<close> emptyE 
        span_grid_encompassed)    
  hence "i1 - 1 \<in> encompassed (grd P1) (grd P2) k2" 
    using \<open>i1 \<in> encompassed (grd P1) (grd P2) k2\<close> encompassed_convex
    \<open>Min (encompassed (grd P1) (grd P2) k2) \<le> i1 - 1\<close> stm strict_mono_mono 
    by fastforce
  hence "lq P1 (i1 - 1) = lq P2 k2"
    by (simp add: assms(2) encompassed_liq_eq mon stm)
  also have "... = lq P1 i1" 
    using \<open>i1 \<in> encompassed (grd P1) (grd P2) k2\<close> assms finer_pool_liq 
    by auto
  also have "... \<noteq> 0" using assms fin_liq finite_liq_def idx_min_finite_in 
      nonempty_liq by blast
  finally show False using \<open>lq P1 (i1 - 1) = 0\<close> by simp
qed

lemma idx_max_Suc_grd_eq:
  assumes "i1 =  idx_max (lq P1)"
  and "k2 = pool_coarse_idx P1 P2 i1"
shows "grd P1 (i1 + 1) = grd P2 (k2 + 1)" 
proof -
  have "i1 = Max (encompassed (grd P1) (grd P2) k2)" 
    using id_max_Max_eq assms clmm_dsc_grid by simp
  hence "grd P1 (i1 + 1) = grd P1 (Max (encompassed (grd P1) (grd P2) k2) + 1)"
    by simp
  also have "... = grd P2 (k2+1)"
  proof (rule encompassed_max_Suc_gamma_eq')
    show "\<exists>m. grd P1 m \<le> grd P2 k2"
      by (simp add: span_grids_ex_le)
    show "\<exists>M. grd P2 (k2 + 2) \<le> grd P1 M"
      by (simp add: span_grids_ex_ge)
    show "grd P2 k2 \<noteq> grd P2 (k2 + 1)" using span2 span_gridD
      by (simp add: strict_mono_eq)
    show "grd P2 (k2 + 1) \<noteq> grd P2 (k2 + 2)" using span2 span_gridD
      by (simp add: strict_mono_eq)
  qed
  finally show ?thesis .
qed

lemma idx_min_grd_eq:
  assumes "i1 =  idx_min (lq P1)"
  and "k2 = pool_coarse_idx P1 P2 i1"
shows "grd P1 i1 = grd P2 k2" 
  unfolding grd_max_def idx_max_img_def 
proof -
  have "i1 = Min (encompassed (grd P1) (grd P2) k2)" 
    using id_min_Min_eq assms clmm_dsc_grid by simp
  hence "grd P1 i1 = grd P1 (Min (encompassed (grd P1) (grd P2) k2))"
    by simp
  also have "... = grd P2 k2"
  proof (rule encompassed_min_gamma_eq')
    show "\<exists>m. grd P1 m \<le> grd P2 k2" by (simp add: span_grids_ex_le)
    show "\<exists>M. grd P2 (k2 + 1) \<le> grd P1 M" by (simp add: span_grids_ex_ge)
    show "grd P2 k2 \<noteq> grd P2 (k2 + 1)" using span2 span_gridD
      by (simp add: strict_mono_eq)
  qed
  finally show ?thesis .
qed

lemma abs_finer_idx_max_coarse:
  assumes "clmm_dsc P1"
  and "clmm_dsc P2" 
  and "finer_pool P1 P2"
  and "nz_support (lq P1) \<noteq> {}"
  and "i1 =  idx_max (lq P1)"
  and "k2 = pool_coarse_idx P1 P2 i1"
shows "k2 = idx_max (lq P2)"
proof -
  define m2 where "m2 = idx_max (lq P2)"
  have "lq P1 i1 \<noteq> 0"
    using assms(5) fin_liq finite_liq_def idx_max_finite_in nonempty_liq by blast
  hence "nz_support (lq P1) \<noteq> {}" unfolding nz_support_def by auto
  have "i1 \<in> encompassed (grd P1) (grd P2) k2" 
    using encompassed_bounds assms pool_coarse_idxD by auto
  hence "lq P1 i1 = lq P2 k2"
    by (simp add: assms finer_pool_liq)
  hence "lq P2 k2 \<noteq> 0" using \<open>lq P1 i1 \<noteq> 0\<close> by simp
  hence "nz_support (lq P2) \<noteq> {}" unfolding nz_support_def by auto
  have "finite_liq P1" using assms clmm_dsc_liq by simp
  have "finite_liq P2" using assms clmm_dsc_liq by simp
  hence "k2 \<le> m2" unfolding m2_def 
    using \<open>lq P2 k2 \<noteq> 0\<close> idx_max_finite_ge finite_liq_def
    by metis
  have "lq P2 m2 \<noteq> 0" using idx_max_finite_in m2_def
    by (simp add: \<open>finite_liq P2\<close> \<open>nz_support (lq P2) \<noteq> {}\<close> idx_max_mem 
        nz_supportD)  
  show "k2 = m2"
  proof (rule ccontr)
    assume "k2 \<noteq> m2"
    hence "k2 < m2" using \<open>k2 \<le>m2\<close> by auto
    have "\<exists>j1. encomp_at (grd P1) (grd P2) j1 m2" using ex_coarse_rep
      by (metis Max_in encompassed_unique finer_ranges.coarse_idx_bounds 
          finer_ranges_axioms span_grid_encompassed 
          span_grids_encompassed_ne)
    from this obtain j1 where "encomp_at (grd P1) (grd P2) j1 m2" by auto
    hence "lq P1 j1 = lq P2 m2"
      by (metis coarse_idx_bounds encomp_idx_unique finer_pool_liq 
          pool_coarse_idxD) 
    hence "lq P1 j1 \<noteq> 0" using \<open>lq P2 m2 \<noteq> 0\<close> by simp
    hence "j1 \<in> nz_support (lq P1)" unfolding nz_support_def by simp
    hence "j1 \<le> i1" using assms \<open>lq P1 j1 \<noteq> 0\<close> idx_max_finite_ge finite_liq_def 
      by (metis \<open>finite_liq P1\<close>)     
    moreover have "i1 < j1" 
      using encomp_idx_mono_conv \<open>encomp_at (grd P1) (grd P2) j1 m2\<close> 
        \<open>k2 < m2\<close> assms(6) coarse_idx_bounds pool_coarse_idxD by presburger
    ultimately show False by simp
  qed
qed

lemma abs_finer_idx_min_coarse:
  assumes "i1 =  idx_min (lq P1)"
  and "k2 = pool_coarse_idx P1 P2 i1"
shows "k2 = idx_min (lq P2)"
proof -
  define m2 where "m2 = idx_min (lq P2)"
  have "lq P1 i1 \<noteq> 0"
    using assms(1) fin_liq finite_liq_def idx_min_finite_in nonempty_liq by blast
  hence "nz_support (lq P1) \<noteq> {}" unfolding nz_support_def by auto
  have "i1 \<in> encompassed (grd P1) (grd P2) k2" 
    using encompassed_bounds assms pool_coarse_idxD by auto
  hence "lq P1 i1 = lq P2 k2"
    by (simp add: assms finer_pool_liq)
  hence "lq P2 k2 \<noteq> 0" using \<open>lq P1 i1 \<noteq> 0\<close> by simp
  hence "nz_support (lq P2) \<noteq> {}" unfolding nz_support_def by auto
  have "finite_liq P1" using fin_liq by simp
  have "finite_liq P2" using fin_liq by (simp add: span_grids_finite_liq')
  hence "m2 \<le> k2" unfolding m2_def 
    using \<open>lq P2 k2 \<noteq> 0\<close> idx_min_finite_le finite_liq_def
    by metis
  have "lq P2 m2 \<noteq> 0" using idx_max_finite_in m2_def
    by (simp add: \<open>finite_liq P2\<close> \<open>nz_support (lq P2) \<noteq> {}\<close> idx_min_mem 
        nz_supportD)  
  show "k2 = m2"
  proof (rule ccontr)
    assume "k2 \<noteq> m2"
    hence "m2 < k2" using \<open>m2 \<le>k2\<close> by auto
    have "\<exists>j1. encomp_at (grd P1) (grd P2) j1 m2" using ex_coarse_rep
      by (metis Max_in encompassed_unique finer_ranges.coarse_idx_bounds 
          finer_ranges_axioms span_grid_encompassed 
          span_grids_encompassed_ne)
    from this obtain j1 where "encomp_at (grd P1) (grd P2) j1 m2" by auto
    hence "lq P1 j1 = lq P2 m2"
      using coarse_idx_bounds encomp_idx_unique finer_pool_liq pool_coarse_idxD 
      by auto 
    hence "lq P1 j1 \<noteq> 0" using \<open>lq P2 m2 \<noteq> 0\<close> by simp
    hence "j1 \<in> nz_support (lq P1)" unfolding nz_support_def by simp
    hence "i1 \<le> j1" using assms \<open>lq P1 j1 \<noteq> 0\<close> idx_min_finite_le finite_liq_def         
      by (metis \<open>finite_liq P1\<close>)     
    moreover have "j1 < i1" 
      using encomp_idx_mono_conv \<open>encomp_at (grd P1) (grd P2) j1 m2\<close> 
        \<open>m2 < k2\<close> assms coarse_idx_bounds pool_coarse_idxD by presburger
    ultimately show False by simp
  qed
qed

lemma abs_finer_idx_max_img_eq:
shows "grd_max P1 = grd_max P2" 
proof -  
  define i1 where "i1 =  idx_max (lq P1)"
  define k2 where "k2 = pool_coarse_idx P1 P2 i1"
  have "k2 = idx_max (lq P2)"
    by (simp add: abs1 abs2 abs_finer_idx_max_coarse finer i1_def k2_def 
        nonempty_liq) 
  have "grd_max P1 = grd P2 (k2 + 1)" 
    unfolding grd_max_def idx_max_img_def
    using idx_max_Suc_grd_eq  i1_def k2_def span by simp
  also have "... = grd_max P2" using \<open>k2 = idx_max (lq P2)\<close>
    unfolding grd_max_def idx_max_img_def by simp
  finally show ?thesis .
qed

lemma abs_finer_idx_min_img_eq:
shows "grd_min P1 = grd_min P2" 
proof -  
  define i1 where "i1 =  idx_min (lq P1)"
  define k2 where "k2 = pool_coarse_idx P1 P2 i1" 
  have "k2 = idx_min (lq P2)"
    by (simp add: abs_finer_idx_min_coarse i1_def k2_def)
  have "grd_min P1 = grd P2 k2" 
    unfolding grd_min_def idx_min_img_def
    using idx_min_grd_eq i1_def k2_def by simp
  also have "... = grd_min P2" using \<open>k2 = idx_min (lq P2)\<close>
    unfolding grd_min_def idx_min_img_def by simp
  finally show ?thesis .
qed

lemma finer_base_reach_eq:
shows "base_reach P1 = base_reach P2" unfolding base_reach_def
  using clmm_dsc_grid finer_base_gross_eq abs_finer_idx_max_img_eq by presburger

lemma finer_quote_reach_eq:
shows "quote_reach P1 = quote_reach P2" unfolding quote_reach_def
  using clmm_dsc_grid finer_quote_gross_eq abs_finer_idx_min_img_eq by presburger

lemma finer_base_slippage:
shows "base_slippage P1 = base_slippage P2" 
  unfolding base_slippage_def base_swap_def
  using finer_quote_net_eq finer_base_reach_eq finer_base_gross_eq 
  by simp

lemma finer_quote_slippage:
shows "quote_slippage P1 = quote_slippage P2" 
  unfolding quote_slippage_def quote_swap_def
  using finer_base_net_eq finer_quote_reach_eq finer_quote_gross_eq
  by simp

end

section \<open>Inequalities related to fees\<close>

context finite_liq_pool 
begin

lemma gross_fct_le:
  assumes "0 \<le> f i"
  and "phi i \<le> phi' i"
  and "phi' i < 1"
shows "gross_fct f phi i \<le> gross_fct f phi' i" 
  unfolding gross_fct_def one_cpl_def
  by (metis assms diff_gt_0_iff_gt diff_left_mono frac_le linorder_not_less 
      order.asym)

lemma gross_fct_lt:
  assumes "0 < f i"
  and "phi i < phi' i"
  and "phi' i < 1"
shows "gross_fct f phi i < gross_fct f phi' i" 
  unfolding gross_fct_def one_cpl_def by (simp add: assms frac_less2)

lemma fee_diff_same_base_net:
  assumes "clmm_dsc P"
  and "clmm_dsc P'"
  and "I = {k. L k \<noteq> 0 \<and> j \<le> k}"
  and "fee_diff_on P P' I"
  and  "same_nz_liq_on P P' {k. j \<le> k}"
  and "0 < sqp"
  and "j = lower_tick P sqp"
  and "L = lq P"
  and "lower_tick P sqp = lower_tick P' sqp" 
shows "base_net P sqp = base_net P' sqp" 
proof -
  define L' where "L' = lq P'"
  have eq: "\<forall>i\<in> I. L i = L' i" using assms L'_def by auto
  have "base_net P sqp = L j * (inverse sqp - inverse (grd P (j + 1))) + 
      (\<Sum>i | L i \<noteq> 0 \<and> j < i. L i * (inverse (grd P i) - inverse (grd P (i + 1))))"
    using assms base_net_sum by simp
  also have "... = L' j * (inverse sqp - inverse (grd P (j + 1))) + 
      (\<Sum>i | L i \<noteq> 0 \<and> j < i. L i * (inverse (grd P i) - inverse (grd P (i + 1))))"
  proof (cases "j\<in> I")
    case True
    then show ?thesis using eq by simp
  next
    case False
    hence "L j = 0" using assms by simp
    then show ?thesis using L'_def assms(5,8) by auto
  qed
  also have "... = L' j * (inverse sqp - inverse (grd P (j + 1))) + 
      (\<Sum>i | L' i \<noteq> 0 \<and> j < i. L' i * (inverse (grd P i) - inverse (grd P (i + 1))))"
  proof -
    have "(\<Sum>i | L i \<noteq> 0 \<and> j< i. 
        L i * (inverse (grd P i) - inverse (grd P (i + 1)))) =
        (\<Sum>i | L' i \<noteq> 0 \<and> j < i. 
        L' i * (inverse (grd P i) - inverse (grd P (i + 1))))"
    proof (rule sum.cong)
      fix k
      assume "k \<in> {i. L' i \<noteq> 0 \<and> j < i}"
      hence "k\<in> I" using assms L'_def same_nz_liq_on_def by auto
      thus "L k * (inverse (grd P k) - inverse (grd P (k + 1))) = 
          L' k * (inverse (grd P k) - inverse (grd P (k + 1)))"
        using eq by simp
    next
      show "{i. L i \<noteq> 0 \<and> j < i} = {i. L' i \<noteq> 0 \<and> j < i}"
      proof
        show "{i. L i \<noteq> 0 \<and> j < i} \<subseteq> {i. L' i \<noteq> 0 \<and> j < i}" 
          using assms(3) eq by auto
      next
        show "{i. L' i \<noteq> 0 \<and> j < i} \<subseteq> {i. L i \<noteq> 0 \<and> j < i}"
        proof
          fix k
          assume "k \<in> {i. L' i \<noteq> 0 \<and> j < i}"
          hence "k\<in> I" using assms L'_def same_nz_liq_on_def by auto
          thus "k \<in> {i. L i \<noteq> 0 \<and> j < i}"
            using \<open>k \<in> {i. L' i \<noteq> 0 \<and> j < i}\<close> eq by auto
        qed
      qed
    qed
    thus ?thesis by simp
  qed  
  also have "... = L' j * (inverse sqp - inverse (grd P' (j + 1))) + 
      (\<Sum>i | L' i \<noteq> 0 \<and> j < i. 
      L' i * (inverse (grd P' i) - inverse (grd P' (i + 1))))"
  proof -
    have "(\<Sum>i | L' i \<noteq> 0 \<and> j < i. 
        L' i * (inverse (grd P i) - inverse (grd P (i + 1)))) =  
        (\<Sum>i | L' i \<noteq> 0 \<and> j < i. 
        L' i * (inverse (grd P' i) - inverse (grd P' (i + 1))))"
    proof (rule sum.cong)
      fix x
      assume "x \<in> {i. L' i \<noteq> 0 \<and> j < i}"
      hence "x \<in> {k. j \<le> k}" by auto
      hence "grd P x = grd P' x" using assms by (simp add: same_nz_liq_onD(1)) 
      have "x+1 \<in> {k. j \<le> k}" using \<open>x \<in> {i. L' i \<noteq> 0 \<and> j < i}\<close> by auto
      hence "grd P (x + 1) = grd P' (x + 1)" 
        using assms by (simp add: same_nz_liq_onD(1)) 
      thus "L' x * (inverse (grd P x) - inverse (grd P (x + 1))) = 
          L' x * (inverse (grd P' x) - inverse (grd P' (x + 1)))"
        using \<open>grd P x = grd P' x\<close> by simp
    qed simp
    moreover have "grd P (j + 1) = grd P' (j + 1)"
      using same_nz_liq_onD(1) assms(5) by auto
    ultimately show ?thesis by simp
  qed
  also have "... = base_net P' sqp" 
    by (rule base_net_sum[symmetric], (auto simp add: assms L'_def))
  finally show ?thesis .
qed

lemma fee_diff_le_imp_quote_gross:
  assumes "clmm_dsc P"
  and "clmm_dsc P'"
  and "{k. L k \<noteq> 0 \<and> k \<le> j} \<subseteq> I"
  and "fee_diff_on P P' I"
  and  "same_nz_liq_on P P' {k. k \<le> j}"
  and "0 < sqp"
  and "j = lower_tick P sqp"
  and "L = gross_fct (lq P) (fee P)"
  and "\<And>i. i \<in> I \<Longrightarrow> fee P i \<le> fee P' i"
  and "lower_tick P sqp = lower_tick P' sqp" 
shows "quote_gross P sqp \<le> quote_gross P' sqp" 
proof -
  define L' where "L' = gross_fct (lq P') (fee P')"
  have pos: "\<forall>i\<in> I. 0 \<le> L i" using assms gross_liq_ge by simp
  have le: "\<forall>i\<in> I. L i \<le> L' i"
  proof
    fix i
    assume "i \<in> I"
    hence "lq P i = lq P' i" using assms fee_diff_onD(2) by simp
    hence "L i = gross_fct (lq P') (fee P) i"
      using assms(8) gross_fct_cong by blast
    also have "... \<le> L' i" unfolding L'_def
    proof (rule gross_fct_le)
      show "0 \<le> lq P' i" by (simp add: assms(2) clmm_dsc_liq(2))
      show "fee P i \<le> fee P' i" using \<open>i \<in> I\<close> assms by simp
      show "fee P' i < 1" by (simp add: assms(2) clmm_dsc_fees)
    qed
    finally show "L i \<le> L' i" .
  qed
  have "quote_gross P sqp = L j * (sqp - grd P j) + 
      (\<Sum>i | L i \<noteq> 0 \<and> i < j. L i * (grd P (i + 1) - grd P i))"
    using assms clmm_quote_gross_sum by simp
  also have "... \<le> L' j * (sqp - grd P j) + 
      (\<Sum>i | L i \<noteq> 0 \<and> i < j. L i * (grd P (i + 1) - grd P i))"
  proof (cases "j\<in> I")
    case True
    then show ?thesis using lower_tick_lbound  le pos
      by (simp add: assms(1) assms(6) assms(7) mult_right_mono)
  next
    case False
    hence "L j = 0" using assms by auto
    then show ?thesis
      using L'_def lower_tick_geq gross_liq_ge
      by (simp add: assms(1,2,6,7)) 
  qed
  also have "... \<le> L' j * (sqp - grd P j) + 
      (\<Sum>i | L i \<noteq> 0 \<and> i < j. L' i * (grd P (i + 1) - grd P i))"
  proof -
    have "(\<Sum>i | L i \<noteq> 0 \<and> i < j. L i * (grd P (i + 1) - grd P i)) \<le>
        (\<Sum>i | L i \<noteq> 0 \<and> i < j. L' i * (grd P (i + 1) - grd P i))"
    proof (rule sum_mono)
      fix k
      assume "k \<in> {i. L i \<noteq> 0 \<and> i < j}"
      hence "k\<in> I" using assms by auto
      thus " L k * (grd P (k + 1) - grd P k) \<le> L' k * (grd P (k + 1) - grd P k)"
        using le
        by (simp add: assms(1) clmm_dsc_grd_mono mult_right_mono)
    qed
    thus ?thesis by simp
  qed
  also have "... = L' j * (sqp - grd P' j) + 
      (\<Sum>i | L' i \<noteq> 0 \<and> i < j. L' i * (grd P (i + 1) - grd P i))"
  proof -
    have ziff: "\<forall> i\<in> I. (L i = 0 \<longleftrightarrow> L' i = 0)" using assms le pos
      by (metis L'_def clmm_dsc_gross_liq_zero_iff fee_diff_onD(2))
    have "{i. L i \<noteq> 0 \<and> i < j} = {i. L' i \<noteq> 0 \<and> i < j}"
    proof
      show "{i. L i \<noteq> 0 \<and> i < j} \<subseteq> {i. L' i \<noteq> 0 \<and> i < j}" 
        using ziff assms(3) by auto
      show "{i. L' i \<noteq> 0 \<and> i < j} \<subseteq> {i. L i \<noteq> 0 \<and> i < j}"
      proof 
        fix i
        assume "i \<in> {i. L' i \<noteq> 0 \<and> i < j}"
        hence "L' i \<noteq> 0" and "i < j" by auto
        hence "L i \<noteq> 0" 
          using L'_def same_nz_liq_onD(2) assms clmm_dsc_gross_liq_zero_iff
          by (smt (verit, ccfv_threshold) mem_Collect_eq) 
        thus "i \<in> {i. L i \<noteq> 0 \<and> i < j}" using \<open>i < j\<close> by auto
      qed
    qed
    moreover have "grd P j = grd P' j" using assms by auto
    ultimately show ?thesis by simp
  qed
  also have "... = L' j * (sqp - grd P' j) + 
      (\<Sum>i | L' i \<noteq> 0 \<and> i < j. L' i * (grd P' (i + 1) - grd P' i))"
  proof -
    have "(\<Sum>i | L' i \<noteq> 0 \<and> i < j. L' i * (grd P (i + 1) - grd P i)) = 
        (\<Sum>i | L' i \<noteq> 0 \<and> i < j. L' i * (grd P' (i + 1) - grd P' i))"
    proof (rule sum.cong)
      fix x
      assume "x \<in> {i. L' i \<noteq> 0 \<and> i < j}"
      hence "x \<in> {k. k \<le> j}" by auto
      hence "grd P x = grd P' x" using assms by force
      have "x+1 \<in> {k. k \<le> j}" using \<open>x \<in> {i. L' i \<noteq> 0 \<and> i < j}\<close> by auto
      hence "grd P (x + 1) = grd P' (x + 1)" using assms by force
      thus "L' x * (grd P (x + 1) - grd P x) = L' x * (grd P' (x + 1) - grd P' x)"
        using \<open>grd P x = grd P' x\<close> by simp
    qed simp
    thus ?thesis by simp
  qed
  also have "... = quote_gross P' sqp" 
    by (rule clmm_quote_gross_sum[symmetric], (auto simp add: assms L'_def))
  finally show ?thesis .
qed

lemma fee_diff_le_imp_quote_gross_mono:
  assumes "clmm_dsc P"
  and "clmm_dsc P'"
  and "{k. L k \<noteq> 0 \<and> k \<le> j} \<subseteq> I"
  and "fee_diff_on P P' I"
  and "same_nz_liq_on P P' {k. k \<le> j}"
  and "0 < sqp"
  and "j = lower_tick P sqp"
  and "L = gross_fct (lq P) (fee P)"
  and "\<And>i. i \<in> I \<Longrightarrow> fee P i \<le> fee P' i"
  and "lower_tick P sqp = lower_tick P' sqp"
  and "sqp \<le> sqp'"
shows "quote_gross P sqp \<le> quote_gross P' sqp'" 
proof -
  have "quote_gross P sqp \<le> quote_gross P' sqp"
    using assms fee_diff_le_imp_quote_gross by simp
  also have "... \<le> quote_gross P' sqp'" 
    using clmm_quote_gross_mono[of P'] monoD assms(2,11) by simp
  finally show ?thesis .
qed

lemma fee_diff_quote_diff_expand:
  assumes "clmm_dsc P"
  and "clmm_dsc P'"
  and "L = gross_fct (lq P) (fee P)"
  and "j = lower_tick P sqp"
  and "k = lower_tick P sqp'"
  and "0 < sqp"
  and "sqp \<le> sqp'"
  and "j < k"
  and "{m. L m \<noteq> 0 \<and> j \<le> m \<and> m \<le> k} \<subseteq> I"
  and "fee_diff_on P P' I"
  and  "same_nz_liq_on P P' {m. j \<le> m \<and> m \<le> k+1}"
  and "\<And>i. i \<in> I \<Longrightarrow> fee P i \<le> fee P' i"
  and "lower_tick P sqp = lower_tick P' sqp" (*to relax?*)
  and "lower_tick P sqp' = lower_tick P' sqp'" (*to relax?*)
shows "quote_gross P sqp' - quote_gross P sqp \<le> quote_gross P' sqp' - quote_gross P' sqp" 
proof -
  define L' where "L' = gross_fct (lq P') (fee P')"
  have pos: "\<forall>i\<in> I. 0 \<le> L i" using assms gross_liq_ge by simp
  have le: "\<forall>i\<in> I. L i \<le> L' i"
  proof
    fix i
    assume "i \<in> I"
    hence "lq P i = lq P' i" using assms fee_diff_onD(2) by simp
    hence "L i = gross_fct (lq P') (fee P) i"
      using assms gross_fct_cong by blast
    also have "... \<le> L' i" unfolding L'_def
    proof (rule gross_fct_le)
      show "0 \<le> lq P' i" by (simp add: assms(2) clmm_dsc_liq(2))
      show "fee P i \<le> fee P' i" using \<open>i \<in> I\<close> assms by simp
      show "fee P' i < 1" by (simp add: assms(2) clmm_dsc_fees)
    qed
    finally show "L i \<le> L' i" .
  qed
  have "quote_gross P sqp' - quote_gross P sqp =  L k * (sqp' - grd P k) + 
  sum (\<lambda> i. L i * (grd P (i+1) - grd P i)) {i. L i \<noteq> 0 \<and> j <i \<and> i < k} +
  L j * (grd P (j+1) - sqp)"
    using assms clmm_quote_gross_diff_eq by simp
  also have "... \<le> L' k * (sqp' - grd P k) + 
      sum (\<lambda> i. L i * (grd P (i+1) - grd P i)) {i. L i \<noteq> 0 \<and> j <i \<and> i < k} +
  L j * (grd P (j+1) - sqp)"
  proof (cases "k\<in> I")
    case True
    then show ?thesis using lower_tick_lbound le pos
      by (smt (verit, best) assms(1) assms(5) assms(6) assms(7) mult_right_mono)
  next
    case False
    hence "L k = 0" using assms by auto
    then show ?thesis
      using L'_def lower_tick_geq gross_liq_ge assms(1,2,5-7) by auto
  qed
  also have "... \<le> L' k * (sqp' - grd P k) + 
      sum (\<lambda> i. L i * (grd P (i+1) - grd P i)) {i. L i \<noteq> 0 \<and> j <i \<and> i < k} +
      L' j * (grd P (j+1) - sqp)"
  proof (cases "j\<in> I")
    case True
    then show ?thesis using lower_tick_lbound le pos
      by (simp add: assms(1) assms(4) lower_tick_ubound)
  next
    case False
    hence "L j = 0" using assms by auto
    then show ?thesis
      using L'_def lower_tick_geq gross_liq_ge
      by (smt (verit, ccfv_SIG) assms(1,2,4) lower_tick_ubound mult_right_mono)
  qed
  also have "... \<le> L' k * (sqp' - grd P k) + 
      sum (\<lambda> i. L' i * (grd P (i+1) - grd P i)) {i. L i \<noteq> 0 \<and> j <i \<and> i < k} +
      L' j * (grd P (j+1) - sqp)"
  proof -
    have "sum (\<lambda> i. L i * (grd P (i+1) - grd P i)) {i. L i \<noteq> 0 \<and> j <i \<and> i < k} \<le>
        sum (\<lambda> i. L' i * (grd P (i+1) - grd P i)) {i. L i \<noteq> 0 \<and> j <i \<and> i < k}"
    proof (rule sum_mono)
      fix i
      assume "i \<in> {i. L i \<noteq> 0 \<and> j < i \<and> i < k}"
      hence "i\<in> I" using assms by auto
      thus " L i * (grd P (i + 1) - grd P i) \<le> L' i * (grd P (i + 1) - grd P i)"
        using le
        by (simp add: assms(1) clmm_dsc_grd_mono mult_right_mono)
    qed
    thus ?thesis by simp
  qed
  also have "... = L' k * (sqp' - grd P' k) + 
      sum (\<lambda> i. L' i * (grd P (i+1) - grd P i)) {i. L' i \<noteq> 0 \<and> j <i \<and> i < k} +
      L' j * (grd P' (j+1) - sqp)"
  proof -
    have ziff: "\<forall> i\<in> I. (L i = 0 \<longleftrightarrow> L' i = 0)" using assms le pos
      by (metis L'_def clmm_dsc_gross_liq_zero_iff fee_diff_onD(2))
    have "{i. L i \<noteq> 0 \<and> j <i \<and> i < k} = {i. L' i \<noteq> 0 \<and> j <i \<and> i < k}"
    proof
      show "{i. L i \<noteq> 0 \<and> j <i \<and> i < k} \<subseteq> {i. L' i \<noteq> 0 \<and> j <i \<and> i < k}" 
        using ziff assms(9) by auto
      show "{i. L' i \<noteq> 0 \<and> j <i \<and> i < k} \<subseteq> {i. L i \<noteq> 0 \<and> j <i \<and> i < k}"
      proof 
        fix i
        assume "i \<in> {i. L' i \<noteq> 0 \<and> j <i \<and> i < k}"
        hence "L' i \<noteq> 0" and "i < k" and "j < i" by auto
        hence "L i \<noteq> 0" 
          using L'_def same_nz_liq_onD(2) assms clmm_dsc_gross_liq_zero_iff
          by (smt (verit, ccfv_threshold) mem_Collect_eq) 
        thus "i \<in> {i. L i \<noteq> 0 \<and> j <i \<and> i < k}"
          using \<open>i < k\<close> \<open>j < i\<close> by simp 
      qed
    qed
    moreover have "grd P k = grd P' k"
      using assms(11) assms(8) same_nz_liq_onD(1) by auto
    moreover have "grd P (j+1) = grd P' (j+1)"
      using add1_zle_eq assms(11) assms(8) same_nz_liq_onD(1) by auto
    ultimately show ?thesis by simp
  qed
  also have "... = L' k * (sqp' - grd P' k) + 
      sum (\<lambda> i. L' i * (grd P' (i+1) - grd P' i)) {i. L' i \<noteq> 0 \<and> j <i \<and> i < k} +
      L' j * (grd P' (j+1) - sqp)"
  proof -
    have "sum (\<lambda> i. L' i * (grd P (i+1) - grd P i)) {i. L' i \<noteq> 0 \<and> j <i \<and> i < k} = 
        sum (\<lambda> i. L' i * (grd P' (i+1) - grd P' i)) {i. L' i \<noteq> 0 \<and> j <i \<and> i < k}"
    proof (rule sum.cong)
      fix x
      assume "x \<in> {i. L' i \<noteq> 0 \<and> j < i \<and> i < k}"
      hence "x \<in> {i. j \<le> i \<and> i \<le> k}" by auto
      hence "grd P x = grd P' x" using assms by force
      have "x+1 \<in> {i. j \<le> i \<and> i \<le> k}" 
        using \<open>x \<in> {i. L' i \<noteq> 0 \<and> j < i \<and> i < k}\<close> by auto
      hence "grd P (x + 1) = grd P' (x + 1)" using assms by force
      thus "L' x * (grd P (x + 1) - grd P x) = L' x * (grd P' (x + 1) - grd P' x)"
        using \<open>grd P x = grd P' x\<close> by simp
    qed simp
    thus ?thesis by simp
  qed
  also have "... = quote_gross P' sqp' - quote_gross P' sqp" 
  proof (rule clmm_quote_gross_diff_eq[symmetric])
    show "j < k" using assms by simp
  qed (simp add: assms L'_def)+
  finally show ?thesis .
qed

lemma fee_diff_quote_diff_expand':
  assumes "clmm_dsc P"
  and "clmm_dsc P'"
  and "L = gross_fct (lq P) (fee P)"
  and "j = lower_tick P sqp"
  and "j = lower_tick P sqp'"
  and "0 < sqp"
  and "sqp \<le> sqp'"
  and "L j \<noteq> 0 \<longrightarrow> j\<in> I"
  and "fee_diff_on P P' I"
  and "\<And>i. i \<in> I \<Longrightarrow> fee P i \<le> fee P' i"
  and "lower_tick P sqp = lower_tick P' sqp" (*to relax?*)
  and "lower_tick P sqp' = lower_tick P' sqp'" (*to relax?*)
shows "quote_gross P sqp' - quote_gross P sqp \<le> quote_gross P' sqp' - quote_gross P' sqp" 
proof -
  define L' where "L' = gross_fct (lq P') (fee P')"
  have le: "\<forall>i\<in> I. L i \<le> L' i"
  proof
    fix i
    assume "i \<in> I"
    hence "lq P i = lq P' i" using assms fee_diff_onD(2) by simp
    hence "L i = gross_fct (lq P') (fee P) i"
      using assms gross_fct_cong by blast
    also have "... \<le> L' i" unfolding L'_def
    proof (rule gross_fct_le)
      show "0 \<le> lq P' i" by (simp add: assms(2) clmm_dsc_liq(2))
      show "fee P i \<le> fee P' i" using \<open>i \<in> I\<close> assms by simp
      show "fee P' i < 1" by (simp add: assms(2) clmm_dsc_fees)
    qed
    finally show "L i \<le> L' i" .
  qed
  have "quote_gross P sqp' - quote_gross P sqp =  L j * (sqp' - sqp)"
    using assms clmm_quote_gross_diff_eq' by simp
  also have "... \<le> L' j * (sqp' - sqp)" using lower_tick_lbound le 
    by (metis L'_def assms(2,7,8) diff_ge_0_iff_ge gross_liq_ge 
        mult.commute ordered_comm_semiring_class.comm_mult_left_mono)
  also have "... = quote_gross P' sqp' - quote_gross P' sqp"
  proof (rule clmm_quote_gross_diff_eq'[symmetric])
    show "clmm_dsc P'" using assms by simp
    show "L' = gross_fct (lq P') (fee P')" using L'_def by simp 
    show "j = lower_tick P' sqp" using assms by simp
    show "j = lower_tick P' sqp'" using assms by simp
    show "0 < sqp" using assms by simp
    show "sqp \<le> sqp'" using assms by simp
  qed 
  finally show ?thesis .
qed

lemma fee_diff_quote_diff_le:
  assumes "clmm_dsc P"
  and "clmm_dsc P'"
  and "L = gross_fct (lq P) (fee P)"
  and "j = lower_tick P sqp"
  and "k = lower_tick P sqp'"
  and "0 < sqp"
  and "sqp \<le> sqp'"
  and "{m. L m \<noteq> 0 \<and> j \<le> m \<and> m \<le> k} \<subseteq> I"
  and "fee_diff_on P P' I"
  and  "same_nz_liq_on P P' {m. j \<le> m \<and> m \<le> k+1}"
  and "\<And>i. i \<in> I \<Longrightarrow> fee P i \<le> fee P' i"
  and "lower_tick P sqp = lower_tick P' sqp" (*to relax?*)
  and "lower_tick P sqp' = lower_tick P' sqp'" (*to relax?*)
shows "quote_gross P sqp' - quote_gross P sqp \<le> quote_gross P' sqp' - quote_gross P' sqp" 
proof (cases "j = k")
  case True
  have "L j\<noteq> 0 \<longrightarrow> j\<in> I" using True assms(8) by blast
  then show ?thesis using assms True fee_diff_quote_diff_expand' by simp
next
  case False
  hence "j < k" using lower_tick_mono assms(1,4-7) by fastforce
  then show ?thesis using fee_diff_quote_diff_expand assms by simp
qed

lemma same_nz_liq_on_nz_support:
  assumes "i \<in> I"
  and "lq P i \<noteq> 0"
  and  "same_nz_liq_on P P' I"
shows "nz_support (lq P') \<noteq> {}"
proof -
  have "lq P' i\<noteq> 0" using assms by blast
  thus ?thesis unfolding nz_support_def by auto
qed

lemma same_nz_liq_on_idx_max:
  assumes "finite_liq P'"
  and "nz_support (lq P) \<noteq> {}"
  and "I = {idx_min (lq P) .. idx_max (lq P) + 1}"
  and "same_nz_liq_on P P' I"
shows "idx_max (lq P) \<le> idx_max (lq P')"
proof -
  define i where "i = idx_max (lq P)"
  have "i\<in> I" using i_def assms
    by (simp add: fin_nz_sup idx_min_max_finite) 
  have "lq P i \<noteq> 0" using i_def by (simp add: assms(2) idx_max_mem nz_supportD)
  hence "lq P' i \<noteq> 0" using same_nz_liq_onD(2) \<open>i\<in> I\<close> assms by simp
  thus "i \<le> idx_max (lq P')"  
    using idx_max_finite_ge assms(1) finite_liq_def by simp
qed

lemma same_nz_liq_on_grd_max:
  assumes "finite_liq P'"
  and "mono (grd P')"
  and "nz_support (lq P) \<noteq> {}"
  and "I = {idx_min (lq P) .. idx_max (lq P) + 1}"
  and "same_nz_liq_on P P' I"
shows "grd_max P \<le> grd_max P'"
proof -  
  have "grd_max P = grd P (idx_max (lq P) + 1)" 
    using grd_max_def idx_max_img_def by simp
  also have "... = grd P' (idx_max (lq P) + 1)"
  proof -
    have "idx_max (lq P) + 1 \<in> I"
      by (simp add: add.commute add_increasing assms(3,4) fin_nz_sup 
          idx_min_max_finite) 
    thus ?thesis using same_nz_liq_onD(1) assms by auto
  qed
  also have "... \<le> grd P' (idx_max (lq P') + 1)"
  proof -
    have "idx_max (lq P) \<le> idx_max (lq P')" 
      using assms same_nz_liq_on_idx_max by simp
    thus ?thesis by (simp add: assms(2) monoD) 
  qed
  finally show ?thesis unfolding grd_max_def idx_max_img_def by simp
qed

lemma same_nz_liq_on_lower_tick:
  assumes "clmm_dsc P"
  and "clmm_dsc P'" 
  and "same_nz_liq_on P P' {i. i \<le> j+1}"
  and "0 < sqp"
  and "lower_tick P sqp \<le> j"
shows "lower_tick P' sqp = lower_tick P sqp" 
proof (rule lower_tick_charact)
  define i where "i = lower_tick P sqp"
  show "clmm_dsc P'" using assms by simp
  have "grd P' i = grd P i" 
    using assms i_def by (simp add: same_nz_liq_onD(1))
  also have "... \<le> sqp"
    by (simp add: assms(1,4) lower_tick_mem i_def) 
  finally show "grd P' i \<le> sqp" .
  have "sqp < grd P (i+1)"
    by (simp add: assms(1) i_def lower_tick_ubound) 
  also have "... = grd P' (i+1)"
    using assms i_def by (simp add: same_nz_liq_onD(1))
  finally show "sqp < grd P' (i+1)" .
qed

lemma same_nz_liq_on_lower_tick':
  assumes "clmm_dsc P'" 
  and "same_nz_liq_on P P' {i. i \<le> j}"
  and "grd P j = sqp"
shows "lower_tick P' sqp = j"
  using assms lower_tick_eq same_nz_liq_onD(1) by auto 

lemma fee_diff_le_grd_max:
  assumes "clmm_dsc P"
  and "clmm_dsc P'"
  and "nz_support (lq P) \<noteq> {}"
  and "{idx_min (lq P) .. idx_max (lq P) + 1} \<subseteq> I"
  and "fee_diff_on P P' I"
  and "same_nz_liq_on P P' {k. k \<le> idx_max (lq P) + 1}" 
  and "\<And>i. i \<in> I \<Longrightarrow> fee P i \<le> fee P' i"
shows "quote_gross P (grd_max P) \<le> quote_gross P' (grd_max P)"
proof -
  define j where "j = lower_tick P (grd_max P)"
  have "j = idx_max (lq P) +1"
    by (simp add: assms(1) j_def lower_tick_grd_max)
  hence "grd P j = grd_max P" unfolding grd_max_def idx_max_img_def by simp
  define L where "L = gross_fct (lq P) (fee P)"
  show "quote_gross P (grd_max P) \<le> quote_gross P' (grd_max P)"
  proof (rule fee_diff_le_imp_quote_gross)
    show "j = lower_tick P (grd_max P)" using j_def by simp
    show "L = gross_fct (lq P) (fee P)" using L_def by simp
    show "0 < grd_max P" by (simp add: assms(1) assms(3) grd_max_gt) 
    have "{k. L k \<noteq> 0 \<and> k \<le> j} \<subseteq> {idx_min (lq P) .. idx_max (lq P)+1}"
    proof
      fix k
      assume "k\<in> {k. L k \<noteq> 0 \<and> k \<le> j}"
      hence "L k \<noteq> 0" and "k \<le> j" by auto
      hence "k\<in> {idx_min (lq P) .. idx_max (lq P)}" 
        using non_zero_liq_interv L_def assms(1) clmm_dsc_gross_liq_zero_iff fin_nz_sup 
        by blast
      thus "k\<in> {idx_min (lq P) .. idx_max (lq P)+1}" by auto
    qed
    thus "{k. L k \<noteq> 0 \<and> k \<le> j} \<subseteq> I" using assms by simp
    show "fee_diff_on P P' I" using assms by simp
    show "same_nz_liq_on P P' {k. k \<le> j}" 
      using assms \<open>j = idx_max (lq P) +1\<close> by simp
    show "\<And>i. i \<in> I \<Longrightarrow> fee P i \<le> fee P' i" using assms by simp
    show "lower_tick P (grd_max P) = lower_tick P' (grd_max P)"
      using \<open>grd P j = grd_max P\<close> \<open>same_nz_liq_on P P' {k. k \<le> j}\<close> assms(2) j_def 
        same_nz_liq_on_lower_tick' 
      by auto
  qed (simp add: assms)+
qed

lemma fee_diff_le_grd_max':
  assumes "clmm_dsc P"
  and "clmm_dsc P'"
  and "nz_support (lq P) \<noteq> {}"
  and "{idx_min (lq P) .. idx_max (lq P) + 1} \<subseteq> I"
  and "fee_diff_on P P' I"
  and "same_nz_liq_on P P' {k. k \<le> idx_max (lq P) + 1}" 
  and "\<And>i. i \<in> I \<Longrightarrow> fee P i \<le> fee P' i"
shows "quote_gross P (grd_max P) \<le> quote_gross P' (grd_max P')"
proof -
  have "quote_gross P (grd_max P) \<le> quote_gross P' (grd_max P)"
    using assms fee_diff_le_grd_max by simp
  also have "... \<le> quote_gross P' (grd_max P')"
  proof (rule clmm_quote_gross_mono[THEN monoD])
    show "clmm_dsc P'" using assms by simp
    show "grd_max P \<le> grd_max P'" using same_nz_liq_on_grd_max
      by (meson assms(2-5) clmm_dsc_grd_mono clmm_dsc_liq(1) fee_diff_on_mono 
          fee_diff_on_nz_liq mono_onI)
  qed
  finally show ?thesis .
qed

lemma fee_diff_le_imp_quote_reach:
  assumes "clmm_dsc P"
  and "clmm_dsc P'"
  and "nz_support (lq P) \<noteq> {}"
  and "{idx_min (lq P) .. idx_max (lq P) + 1} \<subseteq> I"
  and "fee_diff_on P P' I"
  and "same_nz_liq_on P P' {i. i \<le> idx_max (lq P) + 1}"
  and "\<And>i. i \<in> I \<Longrightarrow> fee P i \<le> fee P' i"
  and "0 < y"
  and "y \<le> quote_gross P (grd_max P)"
shows "quote_reach P' y \<le> quote_reach P y" 
proof -
  define sqp' where "sqp' = quote_reach P' y"
  define sqp where "sqp = quote_reach P y"
  define L where "L = gross_fct (lq P) (fee P)"
  have "nz_support (lq P') \<noteq> {}"
  proof (rule same_nz_liq_on_nz_support)
    have "idx_min (lq P) \<in> {idx_min (lq P) .. idx_max (lq P) + 1}"
      using assms(3) fin_nz_sup idx_min_max_finite by fastforce 
    thus "idx_min (lq P) \<in> I" using assms by auto 
    show "lq P (idx_min (lq P)) \<noteq> 0"
      by (simp add: assms(3) idx_min_mem nz_supportD)
    show "same_nz_liq_on P P' I" using assms fee_diff_on_nz_liq by simp
  qed
  have "grd_max P \<le> grd_max P'"
    by (meson assms(2-5) clmm_dsc_grid(1) clmm_dsc_liq(1) fee_diff_on_mono 
        fee_diff_on_nz_liq same_nz_liq_on_grd_max strict_mono_mono)
  have "0 < grd_max P"
    by (meson assms(1) assms(3) liq_grd_min liq_grd_min_max 
        dual_order.strict_trans)
  have "quote_gross P' sqp' = y" unfolding sqp'_def
  proof (rule clmm_quote_gross_reach_eq)
    show "clmm_dsc P'" using assms by simp
    show "0 \<le> y" using assms by simp
    show "nz_support (lq P') \<noteq> {}" using \<open>nz_support (lq P') \<noteq> {}\<close> .
    have "y \<le> quote_gross P (grd_max P)" using assms by simp
    also have "... \<le> quote_gross P' (grd_max P')"
    proof (rule fee_diff_le_imp_quote_gross_mono[OF assms(1-2)])
      define j where "j = lower_tick P (grd_max P)"
      hence "j = idx_max (lq P) + 1"
        by (simp add: assms(1) idx_max_img_def lower_tick_eq grd_max_def)
      show "same_nz_liq_on P P' {k. k \<le> j}" 
        using assms \<open>j = idx_max (lq P) + 1\<close> by simp
      show "{k. L k \<noteq> 0 \<and> k \<le> j} \<subseteq> I" 
      proof
        fix x
        assume "x \<in> {k. L k \<noteq> 0 \<and> k \<le> j}"
        hence "L x \<noteq> 0" and "x \<le> j" by auto
        hence "idx_min (lq P) \<le> x"
          by (metis L_def assms(1) clmm_dsc_gross_liq_zero_iff 
              idx_min_lt_liq leI) 
        moreover have "x \<le> idx_max (lq P)"
          using L_def \<open>L x \<noteq> 0\<close> fin_nz_sup gross_fct_zero_if idx_max_finite_ge 
          by blast
        ultimately have "x \<in> {idx_min (lq P) .. idx_max (lq P) + 1}" by auto
        thus "x\<in> I" using assms by auto
      qed
      show "fee_diff_on P P' I" using assms by simp
      show  "0 < grd_max P" using \<open>0 < grd_max P\<close> .
      show "grd_max P \<le> grd_max P'" using \<open>grd_max P \<le> grd_max P'\<close> .
      show "j = lower_tick P' (grd_max P)" unfolding j_def 
      proof (rule same_nz_liq_on_lower_tick'[symmetric])
        show "grd P (lower_tick P (grd_max P)) = grd_max P" 
          using  \<open>j = idx_max (lq P) + 1\<close> unfolding j_def grd_max_def idx_max_img_def 
          by simp
        show "same_nz_liq_on P P' {i. i \<le>lower_tick P (grd_max P)}"
          using \<open>same_nz_liq_on P P' {k. k \<le> j}\<close> j_def by auto
      qed (simp add: assms)
      show "L = gross_fct (lq P) (fee P)" unfolding L_def by simp
      show "\<And>i. i \<in> I \<Longrightarrow> fee P i \<le> fee P' i" using assms by simp
    qed simp
    finally show "y \<le> quote_gross P' (grd_max P')" .
  qed
  also have "... = quote_gross P sqp" 
    using assms clmm_quote_gross_reach_eq sqp_def by simp
  also have "... \<le> quote_gross P' sqp" 
  proof (rule fee_diff_le_imp_quote_gross)
    define k where "k = lower_tick P sqp"
    thus "k = lower_tick P sqp" by simp
    show "0 < sqp" using clmm_quote_reach_pos assms sqp_def by simp
    show "fee_diff_on P P' I" using assms by simp
    show "L = gross_fct (lq P) (fee P)" using L_def by simp
    show "\<And>i. i \<in> I \<Longrightarrow> fee P i \<le> fee P' i" using assms by simp
    show "{l. L l \<noteq> 0 \<and> l \<le> k} \<subseteq> I" 
    proof
      fix x
      assume "x\<in> {l. L l \<noteq> 0 \<and> l \<le> k}"
      hence "L x \<noteq> 0" and "x \<le> k" by auto
      hence "idx_min (lq P) \<le> x"
        by (metis L_def assms(1) clmm_dsc_gross_liq_zero_iff idx_min_lt_liq 
            leI) 
      moreover have "x \<le> idx_max (lq P)" using \<open>L x \<noteq> 0\<close>
        by (metis L_def assms(1) idx_max_gt_liq gross_fct_zero_if leI)
      ultimately have "x \<in> {idx_min (lq P) .. idx_max (lq P) + 1}" by auto
      thus "x\<in> I" using assms by auto
    qed
    have "sqp \<le> grd_max P"
      by (metis \<open>y = quote_gross P sqp\<close> assms(1,3) quote_gross_grd_max_ge 
          grd_max_quote_reach order_less_irrefl sqp_def 
          verit_comp_simplify1(3)) 
    moreover have "lower_tick P (grd_max P) = idx_max (lq P) + 1"
      by (simp add: assms(1) lower_tick_grd_max) 
    ultimately have "k \<le> idx_max (lq P) +1" using k_def
      by (metis \<open>0 < sqp\<close> assms(1) lower_tick_mono)
    show "same_nz_liq_on P P' {l. l \<le> k}" 
    proof (rule same_nz_liq_on_mono)
      show "same_nz_liq_on P P' {i. i \<le> idx_max (lq P) + 1}" 
        using assms by simp      
      show "{l. l \<le> k} \<subseteq> {i. i \<le> idx_max (lq P) + 1}" 
        using \<open>k \<le> idx_max (lq P) +1\<close> by auto
    qed
    show "k = lower_tick P' sqp" 
    proof (cases "sqp = grd_max P")
      case True
      hence "k = idx_max (lq P) + 1" using k_def
        by (simp add: \<open>lower_tick P (grd_max P) = idx_max (lq P) + 1\<close>)
      show ?thesis 
      proof (rule same_nz_liq_on_lower_tick'[symmetric])
        show "clmm_dsc P'" using assms by simp
        show "same_nz_liq_on P P' {i. i \<le> k}" 
          using assms \<open>k = idx_max (lq P) + 1\<close> by simp
        show "grd P k = sqp" 
          using k_def True \<open>k = idx_max (lq P) + 1\<close> 
          unfolding grd_max_def idx_max_img_def by simp
      qed
    next
      case False
      hence "sqp < grd_max P" using \<open>sqp \<le> grd_max P\<close> by simp
      hence "k < lower_tick P (grd_max P)"
        using \<open>0 < sqp\<close> \<open>lower_tick P (grd_max P) = idx_max (lq P) + 1\<close> 
          assms(1,3) sqp_lt_grd_max_imp_idx k_def 
        by auto
      hence "k \<le> idx_max (lq P)"
        by (simp add: \<open>lower_tick P (grd_max P) = idx_max (lq P) + 1\<close>) 
      show ?thesis unfolding k_def
      proof (rule same_nz_liq_on_lower_tick[symmetric])
        show "lower_tick P sqp \<le> idx_max (lq P)" 
          using \<open>k \<le> idx_max (lq P)\<close> k_def by simp
        show "0 < sqp" using \<open>0 < sqp\<close> .
        show "same_nz_liq_on P P' {i. i \<le> idx_max (lq P) + 1}" using assms by simp
      qed (simp add: assms)+ 
    qed
  qed (simp add: assms)+
  finally have "quote_gross P' sqp' \<le> quote_gross P' sqp" .
  define sqp2 where "sqp2 = quote_reach P' (quote_gross P' sqp)"
  have "sqp' \<le> sqp2"
  proof (rule quote_reach_mono)
    show "clmm_dsc P'" using assms by simp
    show "nz_support (lq P') \<noteq> {}" using \<open>nz_support (lq P') \<noteq> {}\<close> .
    show "0 \<le> y" using assms by simp
    show "y \<le> quote_gross P' sqp" 
      using \<open>y = quote_gross P sqp\<close> \<open>quote_gross P sqp \<le> quote_gross P' sqp\<close> by simp
    show "sqp' = quote_reach P' y" using sqp'_def by simp
    show "sqp2 = quote_reach P' (quote_gross P' sqp)" using sqp2_def by simp
    show "quote_gross P' sqp \<le> quote_gross P' (grd_max P')" 
    proof -
      have "sqp \<le> grd_max P" 
        using sqp_def quote_reach_leq_grd_max
        by (simp add: \<open>0 \<le> y\<close> assms(1,3,9))
      also have "... \<le> grd_max P'" using \<open>grd_max P \<le> grd_max P'\<close> .
      finally have "sqp \<le> grd_max P'" .
      thus ?thesis
        by (simp add: \<open>nz_support (lq P') \<noteq> {}\<close> assms(2) 
            quote_gross_grd_max_max) 
    qed
  qed
  also have "... \<le> sqp" using clmm_quote_reach_le sqp2_def
    using \<open>nz_support (lq P') \<noteq> {}\<close> \<open>quote_gross P' sqp' = y\<close> 
      \<open>quote_gross P' sqp' \<le> quote_gross P' sqp\<close> assms(2,8) 
    by auto
  finally show ?thesis unfolding sqp'_def sqp_def .
qed

lemma same_nz_liq_on_if_simil:
  assumes "grd P = grd P'"
  and "nz_support (lq P) = nz_support (lq P')"
shows "same_nz_liq_on P P' I"
proof
  show "id_grid_on P P' I" using id_grid_onI assms by simp
  show "\<And>i. i \<in> I \<Longrightarrow> (lq P i = 0) = (lq P' i = 0)" 
  proof -
    fix i
    assume "i \<in> I"
    have "(i\<in> nz_support (lq P)) \<longleftrightarrow> (i \<in> nz_support (lq P'))" using assms by simp
    thus "(lq P i = 0) = (lq P' i = 0)" using nz_support_def by fastforce
  qed
qed

lemma fee_diff_simil_base_net:
  assumes "clmm_dsc P"
  and "clmm_dsc P'"
  and "nz_support (lq P) \<noteq> {}"
  and "{idx_min (lq P) .. idx_max (lq P) + 1} \<subseteq> I"
  and "fee_diff_on P P' I"
  and "nz_support (lq P) = nz_support (lq P')"
  and "grd P = grd P'"
  and "grd_min P \<le> sqp"
  and "sqp \<le> grd_max P"
shows "base_net P sqp = base_net P' sqp"
proof (rule fee_diff_same_base_net)
  define j where "j = lower_tick P sqp"
  define L where "L = lq P" 
  show "j = lower_tick P sqp" using j_def by simp
  show "0 < sqp" using grd_min_pos
    using assms(1) assms(3) assms(8) liq_grd_min order_less_le_trans by blast
  show "L = lq P" using L_def by simp
  show "same_nz_liq_on P P' {k. lower_tick P sqp \<le> k}" 
    using assms same_nz_liq_on_if_simil by simp 
  show "fee_diff_on P P' {k. lq P k \<noteq> 0 \<and> lower_tick P sqp \<le> k}"
  proof (rule fee_diff_on_mono)
    show "fee_diff_on P P' I" using assms by simp
    show "{k. lq P k \<noteq> 0 \<and> lower_tick P sqp \<le> k} \<subseteq> I"
    proof
      fix k
      assume "k \<in> {k. lq P k \<noteq> 0 \<and> lower_tick P sqp \<le> k}"
      hence "L k \<noteq> 0" and "lower_tick P sqp \<le> k" using L_def by auto
      hence "idx_min L \<le> k" using L_def
        by (metis assms(1) idx_min_lt_liq linorder_le_cases 
            order_le_imp_less_or_eq) 
      moreover have "k \<le> idx_max L" 
        using L_def \<open>L k \<noteq> 0\<close> fin_nz_sup idx_max_finite_ge by auto 
      ultimately have "k \<in> {idx_min (lq P) .. idx_max (lq P) + 1}" 
        using L_def by auto
      thus "k\<in> I" using assms by auto
    qed
  qed
  show "lower_tick P sqp = lower_tick P' sqp"
    using assms(7) grd_lower_tick_cong by blast
qed (simp add: assms)+

lemma fee_diff_le_price_cmp:
  assumes "clmm_dsc P"
  and "clmm_dsc P'"
  and "nz_support (lq P) \<noteq> {}"
  and "{idx_min (lq P) .. idx_max (lq P) + 1} \<subseteq> I"
  and "fee_diff_on P P' I"
  and "nz_support (lq P) = nz_support (lq P')"
  and "grd P = grd P'"
  and "\<And>i. i \<in> I \<Longrightarrow> fee P i \<le> fee P' i"
  and "0 < y"
  and "y + quote_gross P sqp \<le> quote_gross P (grd_max P)"
  and "grd_min P \<le> sqp"
  and "sqp1 = quote_reach P (y + quote_gross P sqp)"
  and "sqp2 = quote_reach P' (y + quote_gross P' sqp)"
shows "sqp2 \<le> sqp1" 
proof (rule quote_reach_le_gross)
  define L where "L = gross_fct (lq P) (fee P)"
  define j where "j = lower_tick P sqp"
  define k where "k = lower_tick P sqp1"
  have "sqp < sqp1" 
    using quote_reach_gt
    by (simp add: assms(1) assms(10) assms(12) assms(3) assms(9))
  have "0 < sqp" 
      using assms
      by (metis liq_grd_min less_add_same_cancel1 less_eq_real_def 
          pos_add_strict)
  show "sqp2 = quote_reach P' (y + quote_gross P' sqp)" using assms by simp
  have "y + quote_gross P sqp = quote_gross P sqp1"
    using assms(1,3,9,10,12) clmm_quote_gross_pos clmm_quote_gross_reach_eq 
    by auto
  hence "y = quote_gross P sqp1 - quote_gross P sqp" by simp
  also have "... \<le> quote_gross P' sqp1 - quote_gross P' sqp"
  proof (rule fee_diff_quote_diff_le)
    show "clmm_dsc P" using assms by simp
    show "clmm_dsc P'" using assms by simp
    show "L = gross_fct (lq P) (fee P)" using L_def by simp
    show "j = lower_tick P sqp" using j_def by simp
    show "k = lower_tick P sqp1" using k_def by simp
    show "fee_diff_on P P' I" using assms by simp
    show "same_nz_liq_on P P' {m. j \<le> m \<and> m \<le> k + 1}"
      by (simp add: assms(6) assms(7) same_nz_liq_on_if_simil) 
    show "lower_tick P sqp = lower_tick P' sqp"
      by (meson assms(7) grd_lower_tick_cong) 
    show "lower_tick P sqp1 = lower_tick P' sqp1"
      by (meson assms(7) grd_lower_tick_cong) 
    show "\<And>i. i \<in> I \<Longrightarrow> fee P i \<le> fee P' i" using assms by simp
    show "0 < sqp" using \<open>0 < sqp\<close> .
    show "{m. L m \<noteq> 0 \<and> j \<le> m \<and> m \<le> k} \<subseteq> I" 
     proof
      fix m
      assume "m \<in> {m. L m \<noteq> 0 \<and> j \<le> m \<and> m \<le> k}"
      hence "L m \<noteq> 0"  using L_def by auto
      hence "idx_min (lq P) \<le> m" using L_def
        by (meson assms(1) clmm_dsc_gross_liq_zero_iff 
            idx_min_lt_liq leI)
      moreover have "m \<le> idx_max (lq P)" 
        using L_def \<open>L m \<noteq> 0\<close> fin_nz_sup idx_max_finite_ge assms(1) 
          clmm_dsc_gross_liq_zero_iff 
          by blast 
      ultimately have "m \<in> {idx_min (lq P) .. idx_max (lq P) + 1}" 
        using L_def by auto
      thus "m\<in> I" using assms by auto
    qed  
    show "sqp \<le> sqp1" using \<open>sqp < sqp1\<close> by simp
  qed
  finally have "y \<le> quote_gross P' sqp1 - quote_gross P' sqp" .
  thus "y + quote_gross P' sqp \<le> quote_gross P' sqp1" by simp
  show "0 < sqp1" using \<open>0 < sqp\<close> \<open>sqp < sqp1\<close> by simp
  show "nz_support (lq P') \<noteq> {}" using assms by simp
  show "0 < y + quote_gross P' sqp"
    by (simp add: add_strict_increasing assms(2) assms(9)   
        clmm_quote_gross_pos) 
  show "clmm_dsc P'" using assms by simp
  have "sqp1 \<le> grd_max P" 
    using quote_reach_leq_grd_max assms(1,3,9,10,12) 
      clmm_quote_gross_pos 
    by auto
  also have "... \<le> grd_max P'" using same_nz_liq_on_grd_max
    by (meson assms(2) assms(3) assms(6) assms(7) clmm_dsc_grd_mono 
        clmm_dsc_liq(1) mono_onI same_nz_liq_on_if_simil)
  finally show "sqp1 \<le> grd_max P'" .
qed

lemma fee_diff_le_imp_quote_swap:
  assumes "clmm_dsc P"
  and "clmm_dsc P'"
  and "nz_support (lq P) \<noteq> {}"
  and "{idx_min (lq P) .. idx_max (lq P) + 1} \<subseteq> I"
  and "fee_diff_on P P' I"
  and "nz_support (lq P) = nz_support (lq P')"
  and "grd P = grd P'"
  and "\<And>i. i \<in> I \<Longrightarrow> fee P i \<le> fee P' i"
  and "0 < y"
  and "y + quote_gross P sqp \<le> quote_gross P (grd_max P)"
  and "grd_min P \<le> sqp"
shows "quote_swap P' sqp y \<le> quote_swap P sqp y" 
proof -
  have leq: "quote_reach P' (y + quote_gross P sqp) \<le> 
      quote_reach P (y + quote_gross P sqp)"  
  proof (rule fee_diff_le_imp_quote_reach[OF assms(1-5)])
    show "0 < y + quote_gross P sqp"
      by (simp add: add_pos_nonneg assms(1) assms(9) clmm_quote_gross_pos)
    show "y + quote_gross P sqp \<le> quote_gross P (grd_max P)" using assms by simp
    show "\<And>i. i \<in> I \<Longrightarrow> fee P i \<le> fee P' i" using assms by simp
    show "same_nz_liq_on P P' {i. i \<le> idx_max (lq P) + 1}"
      using assms same_nz_liq_on_if_simil assms by simp
  qed
  have leq': "quote_reach P' (y + quote_gross P' sqp) \<le> 
      quote_reach P (y + quote_gross P sqp)"
  proof (rule fee_diff_le_price_cmp[OF assms(1-5)])
    show "0 < y" using assms(9) .
    show "\<And>i. i \<in> I \<Longrightarrow> fee P i \<le> fee P' i" using assms by simp
    show "nz_support (lq P) = nz_support (lq P')" using assms by simp
    show "grd P = grd P'" using assms by simp
    show "grd_min P \<le> sqp" using assms by simp
    show "y + quote_gross P sqp \<le> quote_gross P (grd_max P)" using assms(10) .
  qed simp+
  have "base_net P' (quote_reach P (y + quote_gross P sqp)) \<le>
      base_net P' (quote_reach P' (y + quote_gross P' sqp))" 
    by (rule clmm_base_net_antimono[THEN antimonoD], (simp add: assms leq')+)
  hence "quote_swap P' sqp y \<le> base_net P' sqp -
      base_net P' (quote_reach P (y + quote_gross P sqp))" 
    unfolding quote_swap_def by simp
  also have "... = quote_swap P sqp y"
    using fee_diff_simil_base_net assms unfolding quote_swap_def
    by (smt (verit, ccfv_SIG) clmm_quote_gross_pos quote_reach_gt 
        quote_reach_leq_grd_max)
  finally show "quote_swap P' sqp y \<le> quote_swap P sqp y" .
qed

lemma fee_ge_quote_swap_le:
  assumes "clmm_dsc P"
  and "clmm_dsc P'"
  and "nz_support (lq P) \<noteq> {}"
  and "grd P = grd P'"
  and "lq P = lq P'"
  and "\<And>i. fee P i \<le> fee P' i"
  and "0 \<le> y"
  and "0 < sqp"
  and "y + quote_gross P sqp \<le> quote_gross P (grd_max P)"
shows "quote_swap P' sqp y \<le> quote_swap P sqp y" 
proof (cases "y = 0")
  case True
  then show ?thesis using quote_swap_zero'
    using assms(1-3,5,8) quote_gross_grd_max_max by auto
next
  case False
  show ?thesis 
  proof (cases "grd_min P \<le> sqp")
    case True
    show ?thesis 
    proof (rule fee_diff_le_imp_quote_swap)
      show "fee_diff_on P P' {idx_min (lq P')..idx_max (lq P') + 1}"
        by (simp add: assms(5) assms(4) fee_diff_onI id_grid_onI)
      show "nz_support (lq P) \<noteq> {}" using assms by simp
      show "grd_min P \<le> sqp" using True .
      show "0 < y" using assms \<open>\<not> y = 0\<close> by simp
    qed (simp add: assms)+
  next
    case False
    hence "sqp < grd_min P'" 
      using assms unfolding grd_min_def idx_min_img_def idx_min_def by simp
    have "grd_min P = grd_min P'" 
      using assms unfolding grd_min_def idx_min_img_def idx_min_def by simp
    have "quote_swap P' sqp y = quote_swap P' (grd_min P') y"
      using \<open>sqp < grd_min P'\<close> assms(2,3,5,8) quote_swap_grd_min by auto 
    also have "... \<le> quote_swap P (grd_min P') y"
    proof (rule fee_diff_le_imp_quote_swap)
      show "nz_support (lq P) \<noteq> {}" using assms(3,5) by simp
      show "fee_diff_on P P' {idx_min (lq P')..idx_max (lq P') + 1}"
        by (simp add: assms(5) assms(4) fee_diff_onI id_grid_onI)
      show "y + quote_gross P (grd_min P') \<le> quote_gross P (grd_max P)"
        using False assms(1,5,4,9,8) clmm_quote_gross_grd_min_le grd_min_def 
        by auto
      show "grd_min P \<le> grd_min P'" using \<open>grd_min P = grd_min P'\<close> by simp
      show "0 < y" using assms \<open>\<not> y = 0\<close> by simp
    qed (simp add: assms)+
    also have "... = quote_swap P sqp y"
      using quote_swap_grd_min
      by (simp add: \<open>grd_min P = grd_min P'\<close> \<open>sqp < grd_min P'\<close> assms(1,3,8))
    finally show ?thesis .
  qed
qed
 
end

end