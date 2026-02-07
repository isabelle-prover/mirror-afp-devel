theory Grid_Information imports CLMM_Misc


(* Author: Mnacho Echenim. Grenoble INP - UGA, Kaiko *)
(* This research is part of the ANR project BlockFI - 2024-CES38 *)


begin

section \<open>Grid information\<close>

subsection \<open>Definitions\<close>

text \<open>A grid information consists of three functions defining the way
a grid is associated to (square root) prices, the liquidity on each price range 
and the fees on each price range.\<close>

type_synonym grid_info = "(int\<Rightarrow> real) \<times> (int\<Rightarrow> real) \<times> (int\<Rightarrow>real)" 

definition grd::"grid_info \<Rightarrow> (int\<Rightarrow> real)" where
"grd P = fst P"

definition lq::"grid_info \<Rightarrow> (int\<Rightarrow> real)" where
"lq P = fst (snd P)"

definition fee::"grid_info \<Rightarrow> (int\<Rightarrow> real)" where
"fee P = snd (snd P)"

text \<open>Although several results are formalized in a generalized setting, the pools
of interest are those admitting a finite range with nonzero liquidity.\<close>

definition finite_liq where
"finite_liq P \<longleftrightarrow> finite (nz_support (lq P))"

lemma finite_liqI[intro]:
  assumes "finite {i. lq P i  \<noteq> 0}"
  shows "finite_liq P" using assms unfolding finite_liq_def nz_support_def 
  by simp

lemma finite_liqD:
  assumes "finite_liq P"
  shows "finite {i. lq P i  \<noteq> 0}" using assms 
  unfolding finite_liq_def nz_support_def 
  by simp

definition grd_min where
  "grd_min P = idx_min_img (grd P) (lq P)"

definition grd_max where
  "grd_max P = idx_max_img (grd P) (lq P)"

lemma grd_min_pos:
  assumes "nz_support (lq P) \<noteq> {}"
  and "\<And>i. 0 < grd P i"
shows "0 < grd_min P"
  by (simp add: assms(2) idx_min_img_def grd_min_def)

lemma grd_max_gt:
  assumes "nz_support (lq P) \<noteq> {}"
  and "\<And>i. 0 < grd P i"
shows "0 < grd_max P"
  by (simp add: assms(2) idx_max_img_def grd_max_def)

locale finite_nz_support =
  fixes L::"int \<Rightarrow> real"
  assumes fin_nz_sup: "finite (nz_support L)"

locale finite_liq_pool =
  fixes P
  assumes fin_liq: "finite_liq P"

sublocale finite_liq_pool \<subseteq> finite_nz_support "lq P"
  using fin_liq finite_liq_def finite_nz_support.intro by auto

context finite_liq_pool
begin

lemma idx_max_mem:
  assumes "nz_support (lq P) \<noteq> {}"
shows "idx_max (lq P) \<in> nz_support (lq P)"
proof -
  have "finite (nz_support (lq P))" 
    by (simp add: fin_liq finite_liqD nz_support_def)
  thus ?thesis using assms unfolding idx_max_def by (metis Max_in cSup_eq_Max)
qed

lemma idx_min_mem:
  assumes "nz_support (lq P) \<noteq> {}"
shows "idx_min (lq P) \<in> nz_support (lq P)"
proof -
  have "finite (nz_support (lq P))" 
    by (simp add: fin_liq finite_liqD nz_support_def)
  thus ?thesis using assms unfolding idx_min_def
    by (metis finite_less_Inf_iff nless_le not_le_imp_less) 
qed

lemma grd_min_max:
  assumes "nz_support (lq P) \<noteq> {}"
  and "mono (grd P)"
shows "grd_min P \<le> grd_max P" 
  unfolding grd_min_def grd_max_def idx_min_img_def idx_max_img_def 
    idx_max_def
  by (metis add.commute add_increasing assms fin_nz_sup idx_min_def 
      idx_min_mem le_cSup_finite zero_less_one_class.zero_le_one 
      monoD)

lemma finite_liq_gross_fct:
  shows "finite {i. gross_fct (lq P) (fee P) i \<noteq> 0}" 
  using finite_liqD fin_nz_sup unfolding gross_fct_def nz_support_def by auto

end

subsection \<open>Gross and net token quantities\<close>

subsubsection \<open>General definitions\<close>

text \<open>We define generic functions that are afterwards instantiated to represent
the gross (resp. net) quantities of base (resp. quote) tokens in a pool.\<close>

definition rng_token where
"rng_token = (\<lambda>dff L (pi::real) i. ((L i)::real) * (dff pi (i::int)))"

lemma rng_token_pos:
  assumes "0 \<le> L i"
  and "0 \<le> dff x i"
  shows "0 \<le> rng_token dff L x i" unfolding rng_token_def
  using zero_le_mult_iff assms by auto

lemma rng_token_continuous_on:
  assumes "continuous_on A (\<lambda>pi. dff pi i)"
  shows "continuous_on A (\<lambda>pi. rng_token dff L pi i)" unfolding rng_token_def 
  by (rule continuous_on_mult_left, simp add: assms)

text \<open>(Anti)-monotonicity is preserved by the generic function @{const rng_token}.\<close>

lemma rng_token_mono:
  assumes "0 \<le> L i"
  and "mono (\<lambda>pi. dff pi i)"
shows "mono (\<lambda>pi. rng_token dff L pi i)"
proof
  fix x y::real
  assume "x \<le> y"
  show "rng_token dff L x i \<le> rng_token dff L y i" 
    unfolding rng_token_def
  proof (rule ordered_comm_semiring_class.comm_mult_left_mono)
    show "0 \<le> L i" using assms by simp
    show "dff x i \<le> dff y i" using assms monoD \<open>x \<le> y\<close> by auto    
  qed
qed

lemma rng_token_strict_mono:
  assumes "(0::real) < L i"
  and "strict_mono (\<lambda>pi. dff pi i)"
shows "strict_mono (\<lambda>pi. rng_token dff L pi i)"
proof
  fix x y::real
  assume "x < y"
  hence "dff x i < dff y i" using assms strict_monoD by auto
  thus "rng_token dff L x i < rng_token dff L y i" 
    using assms unfolding rng_token_def by simp
qed

lemma rng_token_antimono:
  assumes "0 \<le> L i"
  and "antimono (\<lambda>pi. dff pi i)"
shows "antimono (\<lambda>pi. rng_token dff L pi i)"
proof
  fix x y::real
  assume "x \<le> y"
  show "rng_token dff L y i \<le> rng_token dff L x i" 
    unfolding rng_token_def
  proof (rule ordered_comm_semiring_class.comm_mult_left_mono)
    show "0 \<le> L i" using assms by simp
    show "dff y i \<le> dff x i" using assms antimonoD \<open>x \<le> y\<close> by auto    
  qed
qed

lemma rng_token_add:
  assumes "\<forall>i. L i = L1 i + L2 i"
  shows "rng_token dff L x i = rng_token dff L1 x i + 
    rng_token dff L2 x i"
  using assms unfolding rng_token_def
  by (simp add: ring_class.ring_distribs(2)) 

text \<open>The generic function for the gross or net token quantities on the entire
pool is obtained by summation of @{const rng_token} on all ranges.\<close>

definition gen_token where
"gen_token = (\<lambda>dff L pi. (infsum (rng_token dff L pi) UNIV))"

lemma gen_token_pos:
  assumes "\<forall>i. 0 \<le> L i"
  and "\<forall>i. 0 \<le> dff x i"
shows "0 \<le> gen_token dff L x" unfolding gen_token_def 
proof (rule infsum_nonneg)
  show "\<And>y. y \<in> UNIV \<Longrightarrow> 0 \<le> rng_token dff L x y" 
    using assms unfolding rng_token_def by simp
qed

lemma gen_token_mono:
  assumes "\<forall>i. 0 \<le> L i"
  and "\<forall>x. rng_token dff L x summable_on UNIV"
  and "\<forall>i. mono (\<lambda>pi. dff pi i)"
  shows "mono (\<lambda>pi. gen_token dff L pi)"
proof
  fix x y::real
  assume "x \<le> y"
  show "gen_token dff L x \<le> gen_token dff L y" unfolding gen_token_def
  proof (rule infsum_mono)
    show "rng_token dff L x summable_on UNIV" using assms by simp
    show "rng_token dff L y summable_on UNIV" using assms by simp
    show "\<And>i. i \<in> UNIV \<Longrightarrow> rng_token dff L x i \<le> rng_token dff L y i" 
      using rng_token_mono assms
      by (meson \<open>x \<le> y\<close> monotoneD)
  qed
qed

lemma gen_token_antimono:
  assumes "\<forall>i. 0 \<le> L i"
  and "\<forall>x. rng_token dff L x summable_on UNIV"
  and "\<forall>i. antimono (\<lambda>pi. dff pi i)"
  shows "antimono (\<lambda>pi. gen_token dff L pi)"
proof
  fix x y::real
  assume "x \<le> y"
  show "gen_token dff L y \<le> gen_token dff L x" unfolding gen_token_def
  proof (rule infsum_mono)
    show "rng_token dff L x summable_on UNIV" using assms by simp
    show "rng_token dff L y summable_on UNIV" using assms by simp
    show "\<And>i. i \<in> UNIV \<Longrightarrow> rng_token dff L y i \<le> rng_token dff L x i" 
    proof -
      fix i::int
      assume "i\<in> UNIV"
      have "antimono (\<lambda>pi. rng_token dff L pi i)" 
        using rng_token_antimono assms by simp
      thus "rng_token dff L y i \<le> rng_token dff L x i"
      using \<open>x \<le> y\<close> antimono_def by metis
    qed
  qed
qed

subsubsection \<open>Finite support restriction\<close>

context finite_nz_support 

begin

lemma finite_nonzero_summable:
  shows "rng_token dff L x summable_on UNIV"
proof (rule finite_nonzero_values_imp_summable_on)
  define rg where "rg = rng_token dff L x"
  define Lnz where "Lnz = {i. L i \<noteq> 0}"
  have "finite Lnz" using fin_nz_sup unfolding Lnz_def
    by (simp add: nz_support_def) 
  define Lz where "Lz = UNIV - Lnz"
  have "\<forall>i\<in> Lz. L i = 0" using Lnz_def Lz_def by simp
  hence "\<forall>i\<in> Lz. rg i = 0" unfolding rg_def rng_token_def by simp
  hence "\<forall>i. rg i \<noteq> 0 \<longrightarrow> i\<in> Lnz" using Lz_def Lnz_def by blast
  show "finite {x \<in> UNIV. rg x \<noteq> 0}" 
    using \<open>\<forall>i. rg i \<noteq> 0 \<longrightarrow> i\<in> Lnz\<close> \<open>finite Lnz\<close>
    by (metis (mono_tags, lifting) mem_Collect_eq rev_finite_subset subsetI)
qed

lemma gen_token_antimono_finite:
  assumes "\<forall>i. 0 \<le> L i"
  and "\<forall>i. antimono (\<lambda>pi. dff pi i)"
shows "antimono (\<lambda>pi. gen_token dff L pi)"
proof (rule gen_token_antimono)
  show "\<forall> x. rng_token dff L x summable_on UNIV"
    using finite_nonzero_summable assms by simp
qed (simp add: assms)+

lemma gen_token_sum:
  shows "gen_token dff L x = 
    sum (rng_token dff L x) {i. L i \<noteq> 0}"
proof -
  define rg where "rg = rng_token dff L x"
  define Lnz where "Lnz = {i. L i \<noteq> 0}"
  have "finite Lnz" using fin_nz_sup  
    unfolding Lnz_def nz_support_def by simp
  define Lz where "Lz = UNIV - Lnz"
  have "\<forall>i\<in> Lz. L i = 0" using Lnz_def Lz_def by simp
  hence "\<forall>i\<in> Lz. rg i = 0" unfolding rg_def rng_token_def by simp
  have "infsum rg UNIV = infsum rg (Lnz \<union> Lz)" unfolding Lz_def Lnz_def 
    by simp
  also have "... = infsum rg Lnz + infsum rg Lz"
  proof (rule infsum_Un_disjoint)
    show "rg summable_on Lz" 
      using \<open>\<forall>i\<in> Lz. rg i = 0\<close> summable_on_0[of Lz rg] by simp
    show "rg summable_on Lnz" using \<open>finite Lnz\<close> by simp
    show "Lnz \<inter> Lz = {}" unfolding Lz_def by simp
  qed
  also have "... = infsum rg Lnz" using infsum_0 \<open>\<forall>i\<in> Lz. rg i = 0\<close> 
    by fastforce
  also have "... = sum rg Lnz" using \<open>finite Lnz\<close> by simp
  finally show ?thesis using rg_def Lnz_def unfolding gen_token_def by simp
qed

lemma gen_token_continuous:
  assumes "\<forall>i. continuous_on A (\<lambda>pi. dff pi i)"
shows "continuous_on A (gen_token dff L)" 
proof -
  have "gen_token dff L = 
    (\<lambda>pi. sum (rng_token dff L pi) {i. L i \<noteq> 0})" 
    using gen_token_sum assms by auto
  moreover have "continuous_on A 
    (\<lambda>pi. sum (rng_token dff L pi) {i. L i \<noteq> 0})"
  proof (rule continuous_on_sum)
    fix i::int
    assume "i \<in> {i. L i \<noteq> 0}"
    show "continuous_on A (\<lambda>x. rng_token dff L x i)" 
      by (rule rng_token_continuous_on, simp add: assms)
  qed
  ultimately show ?thesis by simp
qed

lemma gen_token_strict_mono:
  assumes "\<forall>i. 0 \<le> L i"
  and "nz_support L \<noteq> {}"
  and "\<forall>i. strict_mono (\<lambda>pi. dff pi i)"
  shows "strict_mono (\<lambda>pi. gen_token dff L pi)"
proof
  fix x y::real
  assume "x < y"
  define M where "M = {i. L i \<noteq> 0}"
  have "gen_token dff L x = sum (rng_token dff L x) M"
    using gen_token_sum unfolding M_def by simp
  also have "... < sum (rng_token dff L y) M" 
  proof (rule sum_strict_mono)
    show "finite M" 
      unfolding M_def by (metis fin_nz_sup nz_support_def) 
    show "M \<noteq> {}" using assms unfolding nz_support_def M_def by simp
    fix j 
    assume "j \<in> M"
    hence "0 < L j" using assms less_eq_real_def unfolding M_def by auto
    hence "strict_mono (\<lambda>pi. rng_token dff L pi j)" 
      using assms rng_token_strict_mono by simp
    thus "rng_token dff L x j < rng_token dff L y j" 
      using \<open>x < y\<close> strict_monoD by auto
  qed
  also have "... = gen_token dff L y" 
    using gen_token_sum unfolding M_def by simp
  finally show "gen_token dff L x < gen_token dff L y" .
qed

lemma gen_token_add:
  assumes "\<forall>i. L i = L1 i + L2 i"
  and "\<forall>i. 0 \<le> L1 i"
  and "\<forall>i. 0 \<le> L2 i"
  shows "gen_token dff L x = gen_token dff L1 x + gen_token dff L2 x"
proof -
  have sub1: "{i. L1 i \<noteq> 0} \<subseteq> {i. L i \<noteq> 0}"
      by (simp add: Collect_mono add_nonneg_eq_0_iff assms)
  have sub2: "{i. L2 i \<noteq> 0} \<subseteq> {i. L i \<noteq> 0}"
    by (simp add: Collect_mono add_nonneg_eq_0_iff assms)
  have "gen_token dff L x = sum (rng_token dff L x) {i. L i \<noteq> 0}" 
    using gen_token_sum by simp
  also have "... = sum (\<lambda>i. rng_token dff L1 x i + rng_token dff L2 x i) 
      {i. L i \<noteq> 0}"
    by (rule sum.cong, (simp add: assms rng_token_add)+)
  also have "... = sum (rng_token dff L1 x) {i. L i \<noteq> 0} +
    sum (rng_token dff L2 x) {i. L i \<noteq> 0}"
    by (rule sum.distrib)
  also have "... = gen_token dff L1 x + gen_token dff L2 x"
  proof -
    have "gen_token dff L1 x = sum (rng_token dff L1 x) {i. L1 i \<noteq> 0}"
    proof (rule finite_nz_support.gen_token_sum)
      show "finite_nz_support L1" using sub1 fin_nz_sup
        by (metis finite_nz_support.intro nz_support_def rev_finite_subset)
    qed
    also have "... = 
        sum (rng_token dff L1 x) {i. L i \<noteq> 0}" 
    proof (rule sum.mono_neutral_left)
      show "finite {i. L i \<noteq> 0}" 
        using fin_nz_sup unfolding nz_support_def by simp
      show "{i. L1 i \<noteq> 0} \<subseteq> {i. L i \<noteq> 0}" using sub1 by simp
      show "\<forall>i\<in>{i. L i \<noteq> 0} - {i. L1 i \<noteq> 0}. rng_token dff L1 x i = 0" 
        unfolding rng_token_def by simp
    qed
    finally have 1: "gen_token dff L1 x = 
      sum (rng_token dff L1 x) {i. L i \<noteq> 0}" .
    have "gen_token dff L2 x = sum (rng_token dff L2 x) {i. L2 i \<noteq> 0}"
    proof (rule finite_nz_support.gen_token_sum)
      show "finite_nz_support L2" using sub2 fin_nz_sup
        by (metis finite_nz_support.intro nz_support_def rev_finite_subset)
    qed
    also have "... = sum (rng_token dff L2 x) {i. L i \<noteq> 0}" 
    proof (rule sum.mono_neutral_left)
      show "finite {i. L i \<noteq> 0}" 
        using fin_nz_sup unfolding nz_support_def by simp
      show "{i. L2 i \<noteq> 0} \<subseteq> {i. L i \<noteq> 0}" using sub2 by simp
      show "\<forall>i\<in>{i. L i \<noteq> 0} - {i. L2 i \<noteq> 0}. rng_token dff L2 x i = 0" 
        unfolding rng_token_def by simp
    qed
    finally have "gen_token dff L2 x = 
        sum (rng_token dff L2 x) {i. L i \<noteq> 0}" .
    thus ?thesis using 1 by simp
  qed
  finally show ?thesis .
qed

end

subsection \<open>Gross and net quantities of quote tokens\<close>

subsubsection \<open>Generic functions for quote tokens\<close>

definition gamma_min_diff where
"gamma_min_diff gamma = 
  (\<lambda>(pi::real) i. (min pi (gamma (i+(1::int)))) - (min pi (gamma i)))" 

lemma gamma_min_diff_pos:
  assumes "gamma i \<le> gamma (i+1)"
  shows "0 \<le> gamma_min_diff gamma x i" 
proof -
  show ?thesis
  proof (cases "x \<le> gamma i")
    case True
    hence "min x (gamma i) = x" by simp
    have "x \<le> gamma (i + 1)" using True assms by simp
    hence "min x (gamma (i + 1)) = x" by simp
    then show ?thesis using \<open>min x (gamma i) = x\<close> 
      unfolding gamma_min_diff_def by simp
  next
    case False
    hence "min x (gamma i) = gamma i" by simp
    show ?thesis 
    proof (cases "x \<le> gamma (i + 1)")
      case True
      hence "min x (gamma (i + 1)) = x" by simp
      then show ?thesis using \<open>min x (gamma i) = gamma i\<close> False 
        unfolding gamma_min_diff_def by simp
    next
      case False
      hence "min x (gamma (i + 1)) = gamma (i+1)" by simp
      then show ?thesis using assms unfolding gamma_min_diff_def by simp
    qed
  qed
qed

lemma gamma_min_diff_continuous:
  shows "continuous_on A (\<lambda>(pi::real). gamma_min_diff gamma pi i)" 
  unfolding gamma_min_diff_def
proof (rule continuous_on_diff)
  show "continuous_on A (\<lambda>x. min x (gamma (i + 1)))" using continuous_on_min
    continuous_on_const continuous_on_id by blast
  show "continuous_on A (\<lambda>x. min x (gamma i))" using continuous_on_min
    continuous_on_const continuous_on_id by blast
qed

lemma gamma_min_diff_mono:
  fixes gamma::"int \<Rightarrow> real"
  assumes "gamma i \<le> gamma (i+1)"
  shows "mono (\<lambda>pi. gamma_min_diff gamma pi i)" 
  unfolding gamma_min_diff_def
proof
  fix x y::real
  assume asm: "x \<le> y"
  show "min x (gamma (i + 1)) - min x (gamma i) \<le> 
      min y (gamma (i + 1)) - min y (gamma i)"
  proof (rule diff_min_le)
    show "x \<le> y" using asm .
    show "gamma i \<le> gamma (i + 1)" using assms by simp
  qed
qed

definition rng_gen_quote where
"rng_gen_quote gamma = (\<lambda>L pi i. rng_token (gamma_min_diff gamma) L pi i)"

lemma rng_gen_quote_pos:
  assumes "0 \<le> L i"
  and "gamma i \<le> gamma (i+1)"
  shows "0 \<le> rng_gen_quote gamma L x i" unfolding rng_gen_quote_def
  by (rule rng_token_pos, auto simp add: assms gamma_min_diff_pos)

lemma rng_gen_quote_continuous_on:
  shows "continuous_on A (\<lambda>pi. rng_gen_quote gamma L pi i)" 
  unfolding rng_gen_quote_def
  by (rule rng_token_continuous_on, rule gamma_min_diff_continuous)

lemma rng_gen_quote_mono:
  assumes "0 \<le> L i"
  and "gamma i \<le> gamma (i+1)"
  shows "mono (\<lambda>pi. rng_gen_quote gamma L pi i)" 
proof
  fix x y::real
  assume asm: "x \<le> y"
  show "rng_gen_quote gamma L x i \<le> rng_gen_quote gamma L y i" 
    unfolding rng_gen_quote_def rng_token_def
  proof (rule ordered_comm_semiring_class.comm_mult_left_mono)
    show "0 \<le> L i" using assms by simp
    show "gamma_min_diff gamma x i \<le> gamma_min_diff gamma y i" 
      using gamma_min_diff_mono asm monoD assms by blast    
  qed
qed

definition gen_quote where
"gen_quote = (\<lambda> gamma L pi. gen_token (gamma_min_diff gamma) L pi)"

lemma gen_quote_zero:
  assumes "mono gamma"
  and "\<And>i. gamma i < sqp \<Longrightarrow> L i = 0"
  shows "gen_quote gamma L sqp = 0" unfolding gen_quote_def gen_token_def
proof (rule infsum_0)
  fix i
  show "rng_token (gamma_min_diff gamma) L sqp i = 0" 
  proof (cases "sqp \<le> gamma i")
    case True
    hence "sqp \<le> gamma (i+1)" using assms monoD
      by (metis dual_order.trans zle_add1_eq_le zless_add1_eq)
    hence "gamma_min_diff gamma sqp i = 0" 
      using True unfolding gamma_min_diff_def by simp
    then show ?thesis unfolding rng_token_def by simp
  next
    case False
    hence "L i = 0" using assms by simp
    then show ?thesis unfolding rng_token_def by simp
  qed
qed

lemma gen_quote_pos:
  assumes "\<forall>i. 0 \<le> L i"
  and "\<forall>i. gamma i \<le> gamma (i+1)"
  shows "0 \<le> gen_quote gamma L x" unfolding gen_quote_def 
  using gen_token_pos gamma_min_diff_pos assms by simp

lemma gen_quote_mono:
  assumes "\<forall>i. 0 \<le> L i"
  and "\<forall>x. rng_token (gamma_min_diff gamma) L x summable_on UNIV"
  and "\<forall>i. gamma i \<le> gamma (i+1)"
  shows "mono (gen_quote gamma L)" unfolding gen_quote_def 
proof (rule gen_token_mono)
  show "\<forall>i. mono (\<lambda>pi. gamma_min_diff gamma pi i)" 
    using gamma_min_diff_mono assms by simp 
qed (simp add: assms)+

subsubsection \<open>Finite support restriction\<close>

context finite_nz_support
begin

lemma gen_quote_mono_finite:
  assumes "\<forall>i. 0 \<le> L i"
  and "\<forall>i. gamma i \<le> gamma (i+1)"
shows "mono (gen_quote gamma L)"
proof (rule gen_quote_mono)
  show "\<forall>x. rng_token (gamma_min_diff gamma) L x summable_on UNIV"
    using finite_nonzero_summable assms by simp
qed (simp add: assms)+

lemma gen_quote_continuous:
  shows "continuous_on A (gen_quote gamma L)" unfolding gen_quote_def
proof (rule gen_token_continuous)
  show "\<forall>i. continuous_on A (\<lambda>pi. gamma_min_diff gamma pi i)" using
      gamma_min_diff_continuous by simp
qed

lemma gen_quote_IVT:
  assumes "(idx_min_img gamma L) \<le> (idx_max_img gamma L)"
  and "gen_quote gamma L (idx_min_img gamma L) \<le> y"
  and "y \<le> gen_quote gamma L (idx_max_img gamma L)"
shows "\<exists>pi \<ge> (idx_min_img gamma L). pi \<le> idx_max_img gamma L \<and> 
  gen_quote gamma L pi = y" 
proof (rule IVT)
  show "\<forall>pi. idx_min_img gamma L \<le> pi \<and> pi \<le> idx_max_img gamma L \<longrightarrow> 
      isCont (gen_quote gamma L) pi"
  proof (intro allI impI)
    fix pi
    assume "(idx_min_img gamma L) \<le> pi \<and> pi \<le> (idx_max_img gamma L)"
    show "isCont (gen_quote gamma L) pi" using gen_quote_continuous
      by (simp add: continuous_on_eq_continuous_within assms)
  qed
qed (simp add: assms)+

lemma gen_quote_ne:
  assumes "(idx_min_img gamma L) \<le> (idx_max_img gamma L)"
  and "gen_quote gamma L (idx_min_img gamma L) \<le> y"
  and "y \<le> gen_quote gamma L (idx_max_img gamma L)"
shows "(gen_quote gamma L)-` {y} \<noteq> {}" using gen_quote_IVT assms by blast

lemma finite_support_sum:
  assumes "\<And>i. L i = 0 \<Longrightarrow> f L i = 0"
  shows "infsum (rng_token dff (f L) x) UNIV = 
    sum (rng_token dff (f L) x) {i. L i \<noteq> 0}"
proof -
  define rg where "rg = rng_token dff (f L) x"
  define Lnz where "Lnz = {i. L i \<noteq> 0}"
  have "finite Lnz" using assms  fin_nz_sup unfolding Lnz_def
    by (simp add: nz_support_def)
  define Lz where "Lz = UNIV - Lnz"
  have "\<forall>i\<in> Lz. (f L) i = 0" using assms Lnz_def Lz_def by simp
  hence "\<forall>i\<in> Lz. rg i = 0" unfolding rg_def rng_token_def by simp
  have "infsum rg UNIV = infsum rg (Lnz \<union> Lz)" unfolding Lz_def Lnz_def 
    by simp
  also have "... = infsum rg Lnz + infsum rg Lz"
  proof (rule infsum_Un_disjoint)
    show "rg summable_on Lz" 
      using \<open>\<forall>i\<in> Lz. rg i = 0\<close> summable_on_0[of Lz rg] by simp
    show "rg summable_on Lnz" using \<open>finite Lnz\<close> by simp
    show "Lnz \<inter> Lz = {}" unfolding Lz_def by simp
  qed
  also have "... = infsum rg Lnz" using infsum_0 \<open>\<forall>i\<in> Lz. rg i = 0\<close> 
    by fastforce
  also have "... = sum rg Lnz" using \<open>finite Lnz\<close> by simp
  finally show ?thesis using rg_def Lnz_def by simp
qed

lemma gen_quote_plus:
  assumes "\<forall>i. L i = L1 i + L2 i"
  and "\<forall>i. 0 \<le> L1 i"
  and "\<forall>i. 0 \<le> L2 i"
shows "gen_quote gam L x = gen_quote gam L1 x + gen_quote gam L2 x"
  using assms gen_token_add unfolding gen_quote_def by simp

end

subsection \<open>Gross quote token quantity into a pool\<close>

subsubsection \<open>Function specialization\<close>

text \<open>When the quote tokens are added to a pool, fees are to be taken into account: if
a user adds a quantity $q$ of tokens into a pool, the computation of the amount of base
tokens received is based in $q\cdot(1-\varphi)$.\<close>

definition rng_quote_gross where
"rng_quote_gross P = rng_gen_quote (grd P) (gross_fct (lq P) (fee P))"

lemma rng_quote_gross_pos:
  assumes "0 \<le> gross_fct (lq P) (fee P) i"
  and "grd P i \<le> grd P (i+1)"
  shows "0 \<le> rng_quote_gross P pi i" unfolding rng_quote_gross_def 
  using rng_gen_quote_pos assms by simp

lemma rng_quote_gross_continuous_on:
  shows "continuous_on A (\<lambda>pi. rng_quote_gross P pi i)" 
unfolding rng_quote_gross_def using rng_gen_quote_continuous_on by simp

lemma rng_quote_gross_mono:
  assumes "0 \<le> gross_fct (lq P) (fee P) i"
  and "grd P i \<le> grd P (i+1)"
  shows "mono (\<lambda>pi. rng_quote_gross P pi i)" unfolding rng_quote_gross_def 
  using rng_gen_quote_mono assms by simp

definition quote_gross where
"quote_gross P = gen_quote (grd P) (gross_fct (lq P) (fee P))"

lemma quote_gross_pos:
  assumes "\<forall>i. 0 \<le> gross_fct (lq P) (fee P) i"
  and "\<forall>i. grd P i \<le> grd P (i+1)"
  shows "0 \<le> quote_gross P x" unfolding quote_gross_def 
  using gen_quote_pos assms by simp 

lemma quote_gross_mono:
  assumes "\<forall>i. 0 \<le> (lq P) i"
  and "\<forall>i. (fee P) i < 1"
  and "\<forall>i. (grd P) i \<le> (grd P) (i+1)"
  and "\<forall>x. rng_token (gamma_min_diff (grd P)) (gross_fct (lq P) (fee P)) x 
    summable_on UNIV"
shows "mono (quote_gross P)" unfolding quote_gross_def 
proof (rule gen_quote_mono)
  show "\<forall>i. 0 \<le> gross_fct (lq P) (fee P) i" using gross_fct_sgn assms by blast
qed (simp add: assms)+

lemma gen_quote_grd_min:
  assumes "mono (grd P)"
  and "finite (nz_support L)"
  and "nz_support L \<noteq> {}"
  and "nz_support L = nz_support (lq P)"
shows "gen_quote (grd P) L (grd_min P) = 0" 
proof (rule gen_quote_zero)
  fix i
  assume "grd P i < grd_min P"
  hence "i < idx_min (lq P)" unfolding grd_min_def idx_min_img_def
    using assms(1) mono_strict_invE by blast
  hence "lq P i = 0" using assms idx_min_finite_lt by auto
  hence "i \<notin> nz_support (lq P)" unfolding nz_support_def by auto
  thus "L i = 0" using assms nz_support_def by fastforce
qed (simp add: assms)

text \<open>Definition of the grid point that is reached in a pool for a given gross 
 quantity of quote tokens.\<close>

definition quote_reach where
"quote_reach = (\<lambda>P y. 
  if y = 0 then (grd_min P) 
  else Inf ((quote_gross P)-` {y}))" 

subsubsection \<open>Restriction to pools with a finite liquidity\<close>

context finite_liq_pool

begin

lemma quote_gross_mono_finite:
  assumes "\<forall>i. 0 \<le> (lq P) i"
  and "\<forall>i. (fee P) i < 1"
  and "\<forall>i. (grd P) i \<le> (grd P) (i+1)"
shows "mono (quote_gross P)" 
proof (rule quote_gross_mono)
  show "\<forall>x. rng_token (gamma_min_diff (grd P)) (gross_fct (lq P) (fee P)) x
    summable_on UNIV"
  proof
    fix x
    show "rng_token (gamma_min_diff (grd P)) (gross_fct (lq P) (fee P)) x 
      summable_on UNIV" 
    proof (rule finite_nz_support.finite_nonzero_summable)
      show "finite_nz_support (gross_fct (lq P) (fee P))" 
        using assms finite_liq_gross_fct
        by (simp add: finite_nz_support.intro nz_support_def)
    qed
  qed
qed (simp add: assms)+

lemma quote_gross_mono_finite':
  assumes "\<forall>i. 0 \<le> (lq P) i"
  and "\<forall>i. (fee P) i < 1"
  and "mono (grd P)"
shows "mono (quote_gross P)" 
proof (rule quote_gross_mono_finite)
  show "\<forall>i. grd P i \<le> grd P (i+1)" using assms monoD by fastforce  
qed (simp add: assms)+

lemma quote_gross_continuous:
  shows "continuous_on A (quote_gross P)" unfolding quote_gross_def 
  using gen_quote_continuous finite_liq_gross_fct fin_liq finite_liqD
  by (simp add: finite_nz_support.gen_quote_continuous finite_nz_support.intro 
      nz_support_def)

lemma quote_gross_IVT:
  assumes "\<forall>i. fee P i \<noteq> 1"
  and "grd_min P \<le> grd_max P" 
  and "quote_gross P (grd_min P) \<le> y"
  and "y \<le> quote_gross P (grd_max P)"
shows "\<exists>pi \<ge> (grd_min P). pi \<le> (grd_max P) \<and> 
  quote_gross P pi = y" 
proof -
  have "grd_min P = idx_min_img (grd P) (gross_fct (lq P) (fee P))"
    by (simp add: assms gross_fct_nz_eq idx_min_img_eq grd_min_def)
  moreover have "grd_max P = idx_max_img (grd P) (gross_fct (lq P) (fee P))"
    by (simp add: assms gross_fct_nz_eq idx_max_img_eq grd_max_def)
  ultimately show ?thesis
    using gen_quote_IVT finite_liq_gross_fct assms unfolding quote_gross_def
    by (metis finite_nz_support.gen_quote_IVT finite_nz_support.intro 
        nz_support_def)
qed

lemma quote_gross_ne:
  assumes "\<forall>i. fee P i \<noteq> 1"
  and "grd_min P \<le> grd_max P" 
  and "quote_gross P (grd_min P) \<le> y"
  and "y \<le> quote_gross P (grd_max P)"
shows "quote_gross P-` {y} \<noteq> {}" using quote_gross_IVT assms by blast

lemma quote_gross_grd_min:
  assumes "mono (grd P)"
shows "quote_gross P (grd_min P) = 0" 
  using gen_quote_grd_min unfolding quote_gross_def
  by (smt (verit) assms(1) fin_nz_sup gen_quote_zero gross_fct_zero_if 
      idx_min_finite_le idx_min_img_def monoD grd_min_def)

lemma quote_reach_mem:
  assumes "\<forall>i. 0 \<le> lq P i"
  and "\<forall>i. fee P i < 1"
  and "mono (grd P)"
  and "0 \<le> y"
  and "y \<le> quote_gross P (grd_max P)"
shows "quote_reach P y \<in> quote_gross P-` {y}" 
proof (cases "y = 0")
  case True 
  then show ?thesis 
    using quote_gross_grd_min assms unfolding quote_reach_def by simp
next
  case False
  hence "quote_reach P y = Inf ((quote_gross P)-` {y})" 
    unfolding quote_reach_def by simp 
  also have "... \<in> (quote_gross P)-` {y}"
  proof (rule closed_contains_Inf)
    define X where "X = (quote_gross P)-` {y}"
    show "X \<noteq> {}" 
      using quote_gross_grd_min quote_gross_ne assms unfolding X_def
      by (smt (verit) False mono_invE quote_gross_mono_finite')
    show "closed ((quote_gross P) -` {y})" 
    proof (rule continuous_closed_vimage)
      show "closed {y}" by simp
      show "\<And>x. isCont (quote_gross P) x" using quote_gross_continuous assms
        by (simp add: continuous_on_eq_continuous_within) 
    qed
    show "bdd_below ((quote_gross P) -` {y})" 
    proof
      fix x
      assume "x \<in> (quote_gross P) -` {y}"
      hence "quote_gross P x = y" by simp
      hence "quote_gross P (grd_min P) < quote_gross P x" 
        using quote_gross_grd_min assms False by simp
      moreover have "mono (quote_gross P)" 
      proof (rule quote_gross_mono_finite)
        show "\<forall>i. grd P i \<le> grd P (i + 1)" using assms(3) monoD by fastforce
      qed (simp add: assms)+
      ultimately show "(grd_min P) \<le> x" using mono_invE assms by auto
    qed
  qed
  finally show ?thesis .
qed

lemma quote_gross_inv_strict_mono:
  assumes "mono (quote_gross P)"
  and "quote_gross P sqp' < y"
  and "sqp \<in> quote_gross P -` {y}"
shows "sqp' < sqp"
proof (rule ccontr)
  assume asm: "\<not> sqp' < sqp"
  have "quote_gross P sqp' < y" using assms by simp
  also have "... = quote_gross P sqp" using assms by simp
  also have "... \<le> quote_gross P sqp'" using asm assms mono_strict_invE by auto
  finally show False using assms by simp
qed

lemma quote_gross_inv_bounded:
  assumes "mono (quote_gross P)"
  and "quote_gross P (grd_min P) < y"
  and "y < quote_gross P (grd_max P)"
shows "\<forall> sqp' \<in> quote_gross P -` {y}. 
  dist (grd_min P) sqp' \<le> grd_max P - grd_min P"
proof
  fix sqp'
  assume "sqp' \<in> quote_gross P -` {y}"
  hence "grd_min P \<le> sqp'" using quote_gross_inv_strict_mono assms by fastforce
  have "sqp' \<le> grd_max P" 
    using quote_gross_inv_strict_mono assms \<open>sqp' \<in> quote_gross P -` {y}\<close> 
    by fastforce
  have "dist (grd_min P) sqp' = sqp' - (grd_min P)" using \<open>grd_min P \<le> sqp'\<close>
    by (simp add: dist_real_def)
  thus "dist (grd_min P) sqp' \<le> grd_max P - grd_min P"
    by (simp add: \<open>sqp' \<le> grd_max P\<close>)
qed

lemma quote_gross_bdd_below:
  assumes "mono (quote_gross P)"
  and "quote_gross P (grd_min P) < y"
  shows "bdd_below (quote_gross P -`{y})" using assms
  by (metis bdd_below.I mono_strict_invE order_less_imp_le vimage_singleton_eq)

lemma quote_reach_le:
  assumes "\<forall>i. 0 \<le> lq P i"
  and "\<forall>i. fee P i < 1"
  and "mono (grd P)"
  and "0 < y"  
  and "sqp \<in> quote_gross P -`{y}"
shows "quote_reach P y \<le> sqp" 
proof -
  define sqp' where "sqp' = quote_reach P y"
  define X where "X = quote_gross P -` {y}"
  hence "sqp' = Inf X" 
    using assms unfolding sqp'_def quote_reach_def by simp
  have "\<forall>x\<in> X. Inf X \<le> x" 
  proof
    fix x
    assume "x\<in> X"    
    show "Inf X \<le> x"
    proof (rule  cInf_lower)
      show "x\<in> X" using \<open>x\<in> X\<close> .
      show "bdd_below X" using assms quote_gross_bdd_below quote_gross_grd_min X_def
        by (simp add: quote_gross_mono_finite')
    qed
  qed
  thus ?thesis using assms X_def \<open>sqp' = Inf X\<close> sqp'_def by auto
qed

lemma quote_reach_gross_le:
  assumes "\<forall>i. 0 \<le> lq P i"
  and "\<forall>i. fee P i < 1"
  and "mono (grd P)"
  and "grd_min P \<le> sqp"
shows "quote_reach P (quote_gross P sqp) \<le> sqp" 
proof (cases "quote_gross P sqp = 0")
  case True
  then show ?thesis using assms(4) quote_reach_def by presburger
next
  case False
  then show ?thesis using quote_reach_le assms
    by (metis mono_invE nle_le order_le_imp_less_or_eq quote_gross_grd_min 
        quote_gross_mono_finite' vimage_singleton_eq)
qed


lemma quote_gross_reach_eq:
  assumes "\<forall>i. 0 \<le> lq P i"
  and "\<forall>i. fee P i < 1"
  and "mono (grd P)"
  and "0 \<le> y"
  and "y \<le> quote_gross P (grd_max P)"
shows "quote_gross P (quote_reach P y) = y"
  using assms quote_reach_mem by simp

lemma quote_reach_ge:
  assumes "\<forall>i. 0 \<le> lq P i"
  and "\<forall>i. fee P i < 1"
  and "mono (grd P)"
  and "grd_min P \<le> grd_max P" 
  and "0 < y"
  and "y \<le> quote_gross P (grd_max P)"
shows "grd_min P \<le> quote_reach P y"
proof (rule ccontr)
  assume "\<not> grd_min P \<le> quote_reach P y"
  hence "quote_gross P (quote_reach P y) \<le> quote_gross P (grd_min P)"
    by (smt (verit) assms quote_gross_inv_strict_mono quote_gross_mono_finite' 
        quote_gross_grd_min quote_reach_mem) 
  hence "y \<le> quote_gross P (grd_min P)" using assms quote_gross_reach_eq by simp
  thus False using assms
    by (simp add: quote_gross_grd_min)
qed

end

subsection \<open>Net quote token quantity in a pool\<close>

subsubsection \<open>Function specialization\<close>

text \<open>There are no fees to take into account when tokens are withdrawn from a pool.\<close>

definition rng_quote_net where
"rng_quote_net P = rng_gen_quote (grd P) (lq P)"

lemma rng_quote_net_pos:
  assumes "0 \<le> (lq P) i"
  and "grd P i \<le> grd P (i+1)"
  shows "0 \<le> rng_quote_net P x i" unfolding rng_quote_net_def 
  using rng_gen_quote_pos assms by simp

lemma rng_quote_net_continuous_on:
  shows "continuous_on A (\<lambda>pi. rng_quote_net P pi i)" 
unfolding rng_quote_net_def using rng_gen_quote_continuous_on by simp

lemma rng_quote_net_mono:
  assumes "0 \<le> (lq P) i"
  and "grd P i \<le> grd P (i+1)"
  shows "mono (\<lambda>pi. rng_quote_net P pi i)" unfolding rng_quote_net_def 
  using rng_gen_quote_mono assms by simp

definition quote_net where
"quote_net P = gen_quote (grd P) (lq P)"

lemma quote_net_pos:
  assumes "\<forall>i. 0 \<le> (lq P) i"
  and "\<forall>i. grd P i \<le> grd P (i+1)"
  shows "0 \<le> quote_net P x" unfolding quote_net_def 
  using gen_quote_pos assms by simp

lemma quote_net_mono:
  assumes "\<forall>i. 0 \<le> (lq P) i"
  and "\<forall>i. (fee P) i < 1"
  and "\<forall>i. (grd P) i \<le> (grd P) (i+1)"
  and "\<forall>x. rng_token (gamma_min_diff (grd P)) (lq P) x summable_on UNIV"
  shows "mono (quote_net P)" unfolding quote_net_def 
  using gen_quote_mono assms by simp

subsubsection \<open>Restriction to pools with a finite liquidity\<close>

context finite_liq_pool
begin

lemma quote_net_continuous:
  shows "continuous_on A (quote_net P)" unfolding quote_net_def 
  using gen_quote_continuous finite_liqD by simp

lemma quote_net_IVT:
  assumes "\<forall>i. fee P i \<noteq> 1"
  and "grd_min P \<le> grd_max P" 
  and "quote_net P (grd_min P) \<le> y"
  and "y \<le> quote_net P (grd_max P)"
shows "\<exists>pi \<ge> (grd_min P). pi \<le> (grd_max P) \<and> 
  quote_net P pi = y" 
  using gen_quote_IVT assms finite_liqD
  unfolding quote_net_def grd_min_def grd_max_def by simp

lemma quote_net_ne:
  assumes "\<forall>i. fee P i \<noteq> 1"
  and "grd_min P \<le> grd_max P" 
  and "quote_net P (grd_min P) \<le> y"
  and "y \<le> quote_net P (grd_max P)"
shows "quote_net P-` {y} \<noteq> {}" using quote_net_IVT assms by blast

lemma quote_net_mono_finite_liq:
  assumes "\<forall>i. 0 \<le> (lq P) i"
  and "\<forall>i. (fee P) i < 1"
  and "\<forall>i. (grd P) i \<le> (grd P) (i+1)"
  shows "mono (quote_net P)" unfolding quote_net_def 
  using gen_quote_mono_finite finite_liqD assms by simp

end

subsection \<open>Gross and net quantities of base tokens\<close>

subsubsection \<open>Generic functions for base tokens\<close>

definition inv_gamma_max_diff where
"inv_gamma_max_diff = (\<lambda>gamma (pi::real) i. inverse (max pi (gamma i)) - 
  inverse (max pi (gamma (i+(1::int)))))"

lemma inv_max_pos:
  assumes "0 < a"
  and "(a::real) \<le> b"
  shows "0 \<le> inverse (max x a) - inverse (max x b)"
proof (cases "b \<le> x")
  case True
  thus ?thesis using assms by auto
next
  case False
  hence "max x b = b" by simp
  show ?thesis 
  proof (cases "a \<le> x")
    case True
    hence "max x a = x" by simp
    then show ?thesis using \<open>max x b = b\<close> False using assms by fastforce
  next
    case False
    hence "max x a = a" by simp
    then show ?thesis
      by (simp add: \<open>max x b = b\<close> assms le_imp_inverse_le)
  qed
qed

lemma inv_gamma_max_diff_pos:
  assumes "gamma i \<le> gamma (i +(1::int))"
  and "0 < gamma i"
  shows "0 \<le> inv_gamma_max_diff gamma x i" unfolding inv_gamma_max_diff_def
  by (rule inv_max_pos, (simp add: assms)+)

lemma inv_gamma_max_diff_continuous:
  assumes "gamma i \<le> gamma (i +(1::int))"
  and "0 < gamma i"
  shows "continuous_on A (\<lambda>pi. inv_gamma_max_diff gamma pi i)" 
  unfolding inv_gamma_max_diff_def 
proof (rule continuous_on_diff)
  show "continuous_on A (\<lambda>x. inverse (max x (gamma i)))"
  proof (rule continuous_on_inverse)
    show "continuous_on A (\<lambda>x. max x (gamma i))" using continuous_on_max
    continuous_on_const continuous_on_id by blast
    show "\<forall>x\<in>A. max x (gamma i) \<noteq> 0" using assms
      by (metis leD max.cobounded2)
  qed
  show "continuous_on A (\<lambda>x. inverse (max x (gamma (i+1))))" 
  proof (rule continuous_on_inverse)
    show "continuous_on A (\<lambda>x. max x (gamma (i+1)))" using continuous_on_max
    continuous_on_const continuous_on_id by blast
    show "\<forall>x\<in>A. max x (gamma (i+1)) \<noteq> 0" using assms by force
  qed
qed

lemma inv_gamma_max_diff_antimono:
  assumes "gamma i \<le> gamma (i +(1::int))"
  and "0 < gamma i"
  shows "antimono (\<lambda>pi. inv_gamma_max_diff gamma pi i)" 
  unfolding inv_gamma_max_diff_def
proof
  fix x y::real
  assume asm: "x \<le> y"
  show "inverse (max y (gamma i)) - inverse (max y (gamma (i + 1))) \<le>
          inverse (max x (gamma i)) - inverse (max x (gamma (i + 1)))"
  proof (rule diff_inv_max_le)
    show "x \<le> y" using asm .
    show "gamma i \<le> gamma (i + 1)" using assms by simp
    show "0 < gamma i" using assms by simp
  qed
qed

definition rng_gen_base where
"rng_gen_base = 
  (\<lambda>gamma L pi i. rng_token (inv_gamma_max_diff gamma) L pi i)"

lemma rng_gen_base_pos:
  assumes "gamma i \<le> gamma (i +(1::int))"
  and "0 < gamma i"
  and "0 \<le> L i"
  shows "0 \<le> rng_gen_base gamma L x i" unfolding rng_gen_base_def
  by (rule rng_token_pos, auto simp add: assms inv_gamma_max_diff_pos)

lemma rng_gen_base_continuous_on:
  assumes "gamma i \<le> gamma (i +(1::int))"
  and "0 < gamma i"
shows "continuous_on A (\<lambda>pi. rng_gen_base gamma L pi i)" unfolding rng_gen_base_def
  by (rule rng_token_continuous_on, 
      simp add: inv_gamma_max_diff_continuous assms)

lemma rng_gen_base_antimono:
  assumes "gamma i \<le> gamma (i +(1::int))"
  and "0 < gamma i"
  and "0 \<le> L i"
  shows "antimono (\<lambda>pi. rng_gen_base gamma L pi i)" 
proof
  fix x y::real
  assume asm: "x \<le> y"
  show "rng_gen_base gamma L y i \<le> rng_gen_base gamma L x i" 
    unfolding rng_gen_base_def rng_token_def
  proof (rule ordered_comm_semiring_class.comm_mult_left_mono)
    show "0 \<le> L i" using assms by simp
    show "inv_gamma_max_diff gamma y i \<le> inv_gamma_max_diff gamma x i"
    using inv_gamma_max_diff_antimono[of gamma] asm antimonoD assms by auto    
  qed
qed

definition gen_base where
"gen_base = (\<lambda>gamma L pi. gen_token (inv_gamma_max_diff gamma) L pi)"

lemma gen_base_pos:
  assumes "\<forall>i. gamma i \<le> gamma (i +(1::int))"
  and "\<forall>i. 0 < gamma i"
  and "\<forall>i. 0 \<le> L i"
  shows "0 \<le> gen_base gamma L x" unfolding gen_base_def 
  using gen_token_pos inv_gamma_max_diff_pos assms by simp

lemma gen_base_antimono:
  assumes "\<forall>x. rng_token (inv_gamma_max_diff gamma) L x summable_on UNIV"
  and "\<forall>i. gamma i \<le> gamma (i +(1::int))"
  and "\<forall>i. 0 < gamma i"
  and "\<forall>i. 0 \<le> L i"
  shows "antimono (gen_base gamma L)" using gen_token_antimono assms 
    inv_gamma_max_diff_antimono
  by (simp add: gen_base_def) 

lemma gen_base_zero:
  assumes "mono gamma"
  and "\<And>i. sqp < gamma (i+1) \<Longrightarrow> L i = 0"
  shows "gen_base gamma L sqp = 0" unfolding gen_base_def gen_token_def
proof (rule infsum_0)
  fix i
  show "rng_token (inv_gamma_max_diff gamma) L sqp i = 0" 
  proof (cases "gamma (i+1) \<le> sqp")
    case True
    hence "gamma i \<le> sqp" by (smt (verit) assms(1) mono_invE)
    hence "inv_gamma_max_diff gamma sqp i = 0" 
      using True unfolding inv_gamma_max_diff_def by simp
    then show ?thesis unfolding rng_token_def by simp
  next
    case False
    hence "L i = 0" using assms by simp
    then show ?thesis unfolding rng_token_def by simp
  qed
qed

lemma gen_base_grd_max:
  assumes "mono (grd P)"
  and "finite (nz_support L)"
  and "nz_support L \<noteq> {}"
  and "nz_support L = nz_support (lq P)"
shows "gen_base (grd P) L (grd_max P) = 0" 
proof (rule gen_base_zero)
  fix i
  assume "grd_max P < grd P (i + 1)"
  hence "idx_max (lq P) < i" unfolding grd_max_def idx_max_img_def
    using assms(1)mono_strict_invE by fastforce
  hence "lq P i = 0" using assms idx_max_finite_gt by auto
  hence "i \<notin> nz_support (lq P)" unfolding nz_support_def by auto
  thus "L i = 0" using assms nz_support_def by fastforce
qed (simp add: assms)

subsubsection \<open>Finite support restriction\<close>

context finite_nz_support
begin

lemma gen_base_continuous:
  assumes "\<forall>i. gamma i \<le> gamma (i +(1::int))"
  and "\<forall>i. 0 < gamma i"
  shows "continuous_on A (gen_base gamma L)" unfolding gen_base_def
  using gen_token_continuous inv_gamma_max_diff_continuous assms by simp

lemma gen_base_IVT:
  assumes "\<forall>i. gamma i \<le> gamma (i +(1::int))"
  and "\<forall>i. 0 < gamma i"
  and "(idx_min_img gamma L) \<le> (idx_max_img gamma L)"
  and "gen_base gamma L (idx_max_img gamma L) \<le> y"
  and "y \<le> gen_base gamma L (idx_min_img gamma L)"
shows "\<exists>pi \<ge> (idx_min_img gamma L). pi \<le> (idx_max_img gamma L) \<and> 
  gen_base gamma L pi = y" 
proof (rule IVT2)
  show "\<forall>pi. idx_min_img gamma L \<le> pi \<and> pi \<le> idx_max_img gamma L \<longrightarrow> 
      isCont (gen_base gamma L) pi"
  proof (intro allI impI)
    fix pi
    assume "(idx_min_img gamma L) \<le> pi \<and> pi \<le> (idx_max_img gamma L)"
    show "isCont (gen_base gamma L) pi" using gen_base_continuous assms
      by (simp add: continuous_on_eq_continuous_within)
  qed
qed (simp add: assms)+

lemma gen_base_ne:
  assumes "\<forall>i. gamma i \<le> gamma (i +(1::int))"
  and "\<forall>i. 0 < gamma i"
  and "(idx_min_img gamma L) \<le> (idx_max_img gamma L)"
  and "gen_base gamma L (idx_max_img gamma L) \<le> y"
  and "y \<le> gen_base gamma L (idx_min_img gamma L)"
shows "(gen_base gamma L)-` {y} \<noteq> {}" using gen_base_IVT assms by blast

lemma gen_base_antimono_finite:
  assumes "\<forall>i. gamma i \<le> gamma (i +(1::int))"
  and "\<forall>i. 0 < gamma i"
  and "\<forall>i. 0 \<le> L i"
shows "antimono (gen_base gamma L)"
proof (rule gen_base_antimono)
  show "\<forall>x. rng_token (inv_gamma_max_diff gamma) L x summable_on UNIV"
    using finite_nonzero_summable assms by simp
qed (simp add: assms)+

lemma gen_base_gross:
  assumes "\<forall>i. L i = L1 i + L2 i"
  and "\<forall>i. 0 \<le> L1 i"
  and "\<forall>i. 0 \<le> L2 i"
shows "gen_base gam L x = gen_base gam L1 x + gen_base gam L2 x"
  using assms gen_token_add unfolding gen_base_def by simp

end

subsection \<open>Gross base token quantity in a pool\<close>

subsubsection \<open>Function specialization\<close>

definition rng_base_gross where
"rng_base_gross P = rng_gen_base (grd P) (gross_fct (lq P) (fee P))"

lemma rng_base_gross_pos:
  assumes "0 \<le> gross_fct (lq P) (fee P) i"
  and "grd P i \<le> grd P (i+1)"
  and "0 < grd P i"
  shows "0 \<le> rng_base_gross P x i" unfolding rng_base_gross_def 
  using rng_gen_base_pos assms by simp

lemma rng_base_gross_continuous_on:
  assumes "grd P i \<le> grd P (i+1)"
  and "0 < grd P i"
  shows "continuous_on A (\<lambda>pi. rng_base_gross P pi i)" 
  unfolding rng_base_gross_def 
  using rng_gen_base_continuous_on assms by simp

lemma rng_base_gross_mono:
  assumes "0 \<le> gross_fct (lq P) (fee P) i"
  and "grd P i \<le> grd P (i+1)"
  and "0 < grd P i"
  shows "antimono (\<lambda>pi. rng_base_gross P pi i)" unfolding rng_base_gross_def 
  using rng_gen_base_antimono assms by simp

definition base_gross where
"base_gross P = gen_base (grd P) (gross_fct (lq P) (fee P))"

lemma base_gross_pos:
  assumes "\<forall>i. 0 \<le> gross_fct (lq P) (fee P) i"
  and "\<forall>i. grd P i \<le> grd P (i+1)"
  and "\<forall>i. 0 < grd P i"
  shows "0 \<le> base_gross P x" unfolding base_gross_def 
  using gen_base_pos assms by simp

lemma base_gross_antimono:
  assumes "\<forall>i. 0 \<le> (lq P) i"
  and "\<forall>i. (fee P) i < 1"
  and "\<forall>i. (grd P) i \<le> (grd P) (i+1)"
  and "\<forall>i. 0 < grd P i"
  and "\<forall>x. rng_token (inv_gamma_max_diff (grd P)) (gross_fct (lq P) (fee P)) x 
    summable_on UNIV"
shows "antimono (base_gross P)" unfolding base_gross_def 
proof (rule gen_base_antimono)
  show "\<forall>i. 0 \<le> gross_fct (lq P) (fee P) i" using gross_fct_sgn assms by blast
qed (simp add: assms)+

lemma base_gross_grd_max:
  assumes "mono (grd P)"
  and "finite (nz_support (lq P))"
shows "base_gross P (grd_max P) = 0" 
  using gen_base_grd_max assms gen_base_zero gross_fct_zero_if 
      idx_max_finite_ge idx_max_img_def monoD grd_max_def 
  unfolding quote_gross_def
  by (smt (z3) base_gross_def)

definition base_reach where
"base_reach = (\<lambda>P y. 
  if y = 0 
  then (grd_max P) 
  else Sup ((base_gross P)-` {y}))"

subsubsection \<open>Restriction to pools with a finite liquidity\<close>

context finite_liq_pool
begin

lemma base_gross_continuous:
  assumes "\<forall>i. grd P i \<le> grd P (i+1)"
  and "\<forall>i. 0 < grd P i"
shows "continuous_on A (base_gross P)" unfolding base_gross_def
proof (rule finite_nz_support.gen_base_continuous)
  show "finite_nz_support (gross_fct (lq P) (fee P))" 
    using finite_liq_gross_fct
    by (simp add: finite_nz_support.intro nz_support_def)
qed (simp add: assms)+

lemma base_gross_IVT:
  assumes "\<forall>i. grd P i \<le> grd P (i+1)"
  and "\<forall>i. 0 < grd P i"
  and "\<forall>i. fee P i \<noteq> 1"
  and "grd_min P \<le> grd_max P" 
  and "base_gross P (grd_max P) \<le> y"
  and "y \<le> base_gross P (grd_min P)"
shows "\<exists>pi \<ge> (grd_min P). pi \<le> (grd_max P) \<and> 
  base_gross P pi = y" 
proof -
  define L' where "L' = gross_fct (lq P) (fee P)"
  have 1: "grd_min P = idx_min_img (grd P) L'"
    by (simp add: assms gross_fct_nz_eq idx_min_img_eq grd_min_def L'_def)
  have 2: "grd_max P = idx_max_img (grd P) L'"
    by (simp add: assms gross_fct_nz_eq idx_max_img_eq grd_max_def L'_def)
  have "\<exists>pi\<ge>idx_min_img (grd P) L'.
       pi \<le> idx_max_img (grd P) L' \<and> gen_base (grd P) L' pi = y"
  proof (rule finite_nz_support.gen_base_IVT)
    show "idx_min_img (grd P) L' \<le> idx_max_img (grd P) L'" using 1 2 assms by simp
    show "gen_base (grd P) L' (idx_max_img (grd P) L') \<le> y" using 2 assms
      by (simp add: L'_def base_gross_def)
    show "y \<le> gen_base (grd P) L' (idx_min_img (grd P) L')" using 1 assms
      by (simp add: L'_def base_gross_def)
    show "finite_nz_support L'" using L'_def finite_liq_gross_fct
      by (simp add: finite_nz_support.intro nz_support_def)
  qed (simp add: assms)+
  thus ?thesis by (simp add: 1 2 L'_def base_gross_def)
qed

lemma base_gross_ne:
  assumes "\<forall>i. grd P i \<le> grd P (i+1)"
  and "\<forall>i. 0 < grd P i"
  and "\<forall>i. fee P i \<noteq> 1"
  and "grd_min P \<le> grd_max P" 
  and "base_gross P (grd_max P) \<le> y"
  and "y \<le> base_gross P (grd_min P)"  
shows "base_gross P-` {y} \<noteq> {}" using base_gross_IVT assms by blast

lemma base_gross_antimono_finite:
  assumes "\<forall>i. 0 \<le> (lq P) i"
  and "\<forall>i. grd P i \<le> grd P (i+1)"
  and "\<forall>i. 0 < grd P i"
  and "\<forall>i. (fee P) i < 1"
shows "antimono (base_gross P)" unfolding base_gross_def 
proof (rule finite_nz_support.gen_base_antimono_finite)
  show "\<forall>i. 0 \<le> gross_fct (lq P) (fee P) i"
    using gross_fct_sgn assms by blast
  show "finite_nz_support (gross_fct (lq P) (fee P))"
    by (simp add: finite_liq_gross_fct finite_nz_support_def nz_support_def)
qed (simp add: assms)+

lemma base_reach_mem:
  assumes "\<forall>i. grd P i \<le> grd P (i+1)"
  and "\<forall>i. 0 < grd P i"
  and "\<forall>i. fee P i < 1"
  and "\<forall>i. 0 \<le> lq P i"
  and "mono (grd P)"
  and "grd_min P \<le> grd_max P" 
  and "0 \<le> y"
  and "y \<le> base_gross P (grd_min P)"
shows "base_reach P y \<in> base_gross P-` {y}" 
proof (cases "y = 0")
  case True
  then show ?thesis unfolding base_reach_def
    by (simp add: assms(5) base_gross_grd_max fin_nz_sup)
next
  case False
  hence "base_reach P y = Sup ((base_gross P)-` {y})" 
    unfolding base_reach_def by simp 
  also have "... \<in> (base_gross P)-` {y}"
  proof (rule closed_contains_Sup)
    have "antimono (base_gross P)" using base_gross_antimono_finite assms by simp
    define X where "X = (base_gross P)-` {y}"
    show "X \<noteq> {}" using base_gross_ne assms unfolding X_def
      by (metis add_cancel_left_right add_less_same_cancel1 base_gross_grd_max 
          fin_nz_sup less_int_code(1) mono_strict_invE)
    show "closed ((base_gross P) -` {y})" 
    proof (rule continuous_closed_vimage)
      show "closed {y}" by simp
      show "\<And>x. isCont (base_gross P) x" using base_gross_continuous
        by (simp add: continuous_on_eq_continuous_within assms) 
    qed
    show "bdd_above ((base_gross P) -` {y})" 
    proof
      fix x
      assume "x \<in> (base_gross P) -` {y}"
      hence "base_gross P x = y" by simp
      hence "base_gross P (grd_max P) < base_gross P x" 
        using assms False
        by (simp add: base_gross_grd_max fin_nz_sup)
      thus "x \<le> (grd_max P)" using \<open>antimono (base_gross P)\<close>
        by (metis antimonoD incseq_const less_eq_real_def less_irrefl_nat 
            mono_strict_invE nle_le)
    qed
  qed
  finally show ?thesis .
qed

lemma base_gross_dwn:
  assumes "\<forall>i. grd P i \<le> grd P (i+1)"
  and "\<forall>i. 0 < grd P i"
  and "\<forall>i. fee P i < 1"
  and "\<forall>i. 0 \<le> lq P i"
  and "mono (grd P)"
  and "grd_min P \<le> grd_max P" 
  and "0 \<le> y"
  and "y \<le> base_gross P (grd_min P)"
shows "base_gross P (base_reach P y) = y"
  using assms base_reach_mem by simp

end

subsection \<open>Net base token quantity in a pool\<close>

subsubsection \<open>Function specialization\<close>

definition rng_base_net where
"rng_base_net P = rng_gen_base (grd P) (lq P)"

lemma rng_base_net_pos:
  assumes "grd P i \<le> grd P (i +(1::int))"
  and "0 < grd P i"
  and "0 \<le> lq P i"
  shows "0 \<le> rng_base_net P x i" unfolding rng_base_net_def 
  using rng_gen_base_pos assms by simp

lemma rng_base_net_continuous_on:
  assumes "grd P i \<le> grd P (i +(1::int))"
  and "0 < grd P i" 
  shows "continuous_on A (\<lambda>pi. rng_base_net P pi i)" 
unfolding rng_base_net_def using rng_gen_base_continuous_on assms by simp

lemma rng_base_net_mono:
  assumes "grd P i \<le> grd P (i +(1::int))"
  and "0 < grd P i"
  and "0 \<le> lq P i"
  shows "antimono (\<lambda>pi. rng_base_net P pi i)" unfolding rng_base_net_def 
  using rng_gen_base_antimono assms by simp

definition base_net where
"base_net P = gen_base (grd P) (lq P)"

lemma base_net_pos:
  assumes "\<forall>i. grd P i \<le> grd P (i +(1::int))"
  and "\<forall>i. 0 < grd P i"
  and "\<forall>i. 0 \<le> lq P i"
  shows "0 \<le> base_net P x" unfolding base_net_def 
  using gen_base_pos assms by simp

subsubsection \<open>Restriction to pools with a finite liquidity\<close>

context finite_liq_pool
begin

lemma base_net_continuous:
  assumes "\<forall>i. grd P i \<le> grd P (i +(1::int))"
  and "\<forall>i. 0 < grd P i"
  shows "continuous_on A (base_net P)" unfolding base_net_def 
  using gen_base_continuous assms finite_liqD by simp

lemma base_net_IVT:
  assumes "\<forall>i. grd P i \<le> grd P (i +(1::int))"
  and "\<forall>i. 0 < grd P i"
  and "grd_min P \<le> grd_max P" 
  and  "base_net P (grd_max P) \<le> y"
  and "y \<le> base_net P (grd_min P)"
shows "\<exists>pi \<ge> (grd_min P). pi \<le> (grd_max P) \<and> 
  base_net P pi = y" 
  using gen_base_IVT assms finite_liqD
  unfolding base_net_def grd_min_def grd_max_def by simp

lemma base_net_ne:
  assumes "\<forall>i. grd P i \<le> grd P (i +(1::int))"
  and "\<forall>i. 0 < grd P i"
  and "grd_min P \<le> grd_max P" 
  and  "base_net P (grd_max P) \<le> y"
  and "y \<le> base_net P (grd_min P)"
shows "base_net P-` {y} \<noteq> {}" using base_net_IVT assms by blast

lemma base_net_antimono_finite:
  assumes "\<forall>i. grd P i \<le> grd P (i +(1::int))"
  and "\<forall>i. 0 < grd P i"
  and "\<forall>i. 0 \<le> lq P i"
  shows "antimono (base_net P)" unfolding base_net_def 
  using gen_base_antimono_finite finite_liqD assms by simp

end

subsection \<open>Swapping tokens, market depth and slippage\<close>

text \<open>Given a grid point $\pi$ and a quantity $y$ of quote tokens to add to the
pool, this function computes the amount of base tokens that are retrieved from the pool.\<close>

definition quote_swap where
"quote_swap P = (\<lambda>pi y. 
  base_net P pi - base_net P (quote_reach P (y + quote_gross P pi)))"

text \<open>Given a grid point $\pi$ and a quantity $x$ of base tokens to add to the
pool, this function computes the amount of quote tokens that are retrieved from the pool.\<close>

definition base_swap where
"base_swap P = (\<lambda>pi x. 
  quote_net P pi - quote_net P (base_reach P (x + base_gross P pi)))"

text \<open>The market depth in a pool takes as arguments two grid points $\pi$ and $\pi'$, 
and returns the amounts of base or quote tokens that have to be added to the pool 
for its state to get from $\pi$ to $\pi'$.\<close>

definition mkt_depth where
"mkt_depth P = (\<lambda> pi pi'. if pi < pi' then (base_net P pi - base_net P pi')
  else (quote_net P pi - quote_net P pi'))"

text \<open>Base and quote slippages relate the amount of tokens withdrawn from the pool from
those given by an infinitesimally small amount of tokens and that can be
deduced from the grid point.\<close>

definition quote_slippage where
"quote_slippage P = (\<lambda>pi y. y/(quote_swap P pi y * pi * pi) - 1)"

definition base_slippage where
"base_slippage P = (\<lambda>pi x. base_swap P pi x/(x * pi * pi) - 1)"

subsection \<open>Identical profiles\<close>

definition id_grid_on where
"id_grid_on P P' I \<longleftrightarrow> (\<forall>i\<in> I. grd P i = grd P' i)"

lemma id_grid_onI[intro]:
  assumes "\<And>i. i\<in> I \<Longrightarrow> grd P i = grd P' i"
  shows "id_grid_on P P' I" using assms unfolding id_grid_on_def by simp

lemma id_grid_onD[dest]:
  assumes "id_grid_on P P' I"
  and "i\<in> I"
shows "grd P i = grd P' i" using assms unfolding id_grid_on_def by simp

lemma id_grid_on_comm:
  assumes "id_grid_on P P' I"
  shows "id_grid_on P' P I"
  using assms unfolding id_grid_on_def by simp

lemma id_grid_on_mono:
  assumes "id_grid_on P P' I"
  and "I' \<subseteq> I"
shows "id_grid_on P P' I'" using assms unfolding id_grid_on_def by auto

definition same_nz_liq_on where
"same_nz_liq_on P P' I \<longleftrightarrow> id_grid_on P P' I \<and>
    (\<forall>i \<in> I. (lq P i = 0) \<longleftrightarrow> (lq P' i = 0))" 

lemma same_nz_liq_onI[intro]:
  assumes "id_grid_on P P' I"
  and "\<And>i. i\<in> I \<Longrightarrow> ((lq P i = 0) \<longleftrightarrow> (lq P' i = 0))"
shows "same_nz_liq_on P P' I" using assms unfolding same_nz_liq_on_def by simp

lemma same_nz_liq_onD[dest]:
  assumes "same_nz_liq_on P P' I"
  and "i\<in> I"
shows "grd P i = grd P' i" "(lq P i = 0) \<longleftrightarrow> (lq P' i = 0)" 
  using assms unfolding same_nz_liq_on_def by auto

lemma same_nz_liq_on_comm:
  assumes "same_nz_liq_on P P' I"
  shows "same_nz_liq_on P' P I" 
  using assms id_grid_on_comm unfolding same_nz_liq_on_def by simp

lemma same_nz_liq_on_mono:
  assumes "same_nz_liq_on P P' I"
  and "I'\<subseteq> I"
  shows "same_nz_liq_on P P' I'" 
  using assms id_grid_on_mono unfolding same_nz_liq_on_def
  by (meson id_grid_on_comm in_mono)

definition fee_diff_on where
"fee_diff_on P P' I \<longleftrightarrow> id_grid_on P P' I \<and> (\<forall>i \<in> I. lq P i = lq P' i)"

lemma fee_diff_onI[intro]:
  assumes "id_grid_on P P' I"
  and "\<And>i. i\<in> I \<Longrightarrow> lq P i = lq P' i"
shows "fee_diff_on P P' I" 
  using assms unfolding fee_diff_on_def by simp

lemma fee_diff_onD[dest]:
  assumes "fee_diff_on P P' I"
  shows "id_grid_on P P' I" "\<forall>i \<in> I. lq P i = lq P' i"  
proof-
  show "id_grid_on P P' I" 
    using assms unfolding fee_diff_on_def by simp
  show "\<forall>i\<in>I. lq P i = lq P' i" 
    using assms unfolding fee_diff_on_def by simp
qed

lemma fee_diff_on_nz_liq:
  assumes "fee_diff_on P P' I"
  shows "same_nz_liq_on P P' I" unfolding same_nz_liq_on_def
proof
  show "id_grid_on P P' I" using assms fee_diff_onD(1) by simp
  show " \<forall>i\<in>I. (lq P i = 0) = (lq P' i = 0)" using assms fee_diff_onD(2) by simp
qed

lemma fee_diff_on_comm:
  assumes "fee_diff_on P P' I"
  shows "fee_diff_on P' P I"
  using assms fee_diff_on_def id_grid_on_comm by simp

lemma fee_diff_on_mono:
  assumes "fee_diff_on P P' I"
  and "I'\<subseteq> I"
  shows "fee_diff_on P P' I'"
  using assms id_grid_on_mono unfolding fee_diff_on_def by blast

section \<open>Grid refinement\<close>

text \<open>We define the notion of pool refinement, that characterizes when a pool admits
a finer price grid than another one but exhibits the same behavior.\<close>

subsection \<open>Encompassement properties\<close>

definition encomp_at where
"encomp_at gamma1 gamma2 i k \<equiv> gamma2 k \<le> gamma1 i \<and> 
  gamma1 (i+1) \<le> gamma2 (k+1)"

lemma encomp_atD1:
  assumes "encomp_at gamma1 gamma2 i k" 
  shows "gamma2 k \<le> gamma1 i" 
  using assms unfolding encomp_at_def by simp

lemma encomp_atD2:
  assumes "encomp_at gamma1 gamma2 i k" 
  shows "gamma1 (i+1) \<le> gamma2 (k+1)" 
  using assms unfolding encomp_at_def by simp

lemma encomp_atI[intro]:
  assumes "gamma2 k \<le> gamma1 i"
  and "gamma1 (i+1) \<le> gamma2 (k+1)" 
shows "encomp_at gamma1 gamma2 i k" using assms unfolding encomp_at_def by simp

definition encompassed where
"encompassed gamma1 gamma2 k = {i::int. encomp_at gamma1 gamma2 i k}"

lemma encompassed_convex:
  assumes "(i::int) \<in> encompassed gamma1 gamma2 k"
  and "j \<in> encompassed gamma1 gamma2 k"
  and "i \<le> l"
  and "l \<le> j"
  and "mono gamma1"
shows "l \<in> encompassed gamma1 gamma2 k" unfolding encompassed_def encomp_at_def
proof 
  have "gamma2 k \<le> gamma1 i" using assms encompassed_def encomp_at_def by blast
  hence "gamma2 k \<le> gamma1 l" using assms
    by (meson dual_order.trans monotoneD)
  have "gamma1 (j+1) \<le> gamma2 (k+1)"  
    using assms encompassed_def encomp_at_def by blast
  hence "gamma1 (l+1) \<le> gamma2 (k+1)"
    using assms dual_order.trans monoD by fastforce
  thus "gamma2 k \<le> gamma1 l \<and> gamma1 (l + 1) \<le> gamma2 (k + 1)" 
    using \<open>gamma2 k \<le> gamma1 l\<close> by simp
qed

lemma encompassed_interval:
  assumes "mono gamma1"
  and "finite (encompassed gamma1 gamma2 k)"
  and "encompassed gamma1 gamma2 k \<noteq> {}"
shows "encompassed gamma1 gamma2 k = 
  {Min (encompassed gamma1 gamma2 k).. Max (encompassed gamma1 gamma2 k)}"
proof
  define E where "E = (encompassed gamma1 gamma2 k)"
  define m where "m = Min E"
  define M where "M = Max E"
  have "m\<in> E" using m_def E_def assms by simp
  have "M \<in> E" using M_def E_def assms by simp
  show "{m..M} \<subseteq> E" 
  proof
    fix x
    assume "x\<in> {m..M}"
    hence "m \<le> x \<and> x \<le> M" by simp
    show "x\<in> E" using assms encompassed_convex
      E_def \<open>M \<in> E\<close> \<open>m \<in> E\<close> \<open>m \<le> x \<and> x \<le> M\<close> by blast
  qed
  show "E \<subseteq> {m..M}" using m_def M_def assms
    by (simp add: E_def subset_eq)
qed
  
lemma encomp_at_idx_leq:
  fixes gamma1::"int \<Rightarrow> real" and gamma2::"int \<Rightarrow> real"
  assumes "strict_mono (gamma1::int \<Rightarrow> real)"
  and "mono (gamma2::int \<Rightarrow> real)"
  and "encomp_at gamma1 gamma2 i k"
  and "gamma2 k' \<le> gamma1 i"
shows "k' \<le> k"
proof (rule ccontr)
  assume "\<not> k' \<le> k"
  hence "k < k'" by simp
  hence "k+1 \<le> k'" by simp
  hence "gamma2 (k+1) \<le> gamma2 k'" using assms
    by (simp add: monotoneD)
  hence "gamma1 (i+1) \<le> gamma2 k'" using assms encomp_atD2 by fastforce
  hence "gamma1 (i+1) \<le> gamma1 i" using assms by simp
  thus False using assms(1) by (simp add: strict_mono_less_eq)
qed

lemma encomp_at_unique:
  assumes "strict_mono (gamma1::int \<Rightarrow> real)"
  and "mono (gamma2::int \<Rightarrow> real)"
  and "encomp_at gamma1 gamma2 i k"
  and "encomp_at gamma1 gamma2 i k'"
shows "k = k'"
proof -
  have "k \<le> k'" using assms encomp_at_idx_leq
    by (simp add: encomp_atD1) 
  moreover have "k' \<le> k" using assms encomp_at_idx_leq 
    by (simp add: encomp_atD1) 
  ultimately show ?thesis by simp
qed

lemma encomp_at_unique':
  assumes "strict_mono (gamma1::int \<Rightarrow> real)"
  and "mono (gamma2::int \<Rightarrow> real)"
  and "encomp_at gamma1 gamma2 i k"
  and "gamma2 k' \<le> gamma1 i"
  and "gamma1 i < gamma2 (k'+1)"
shows "k = k'"
proof (rule ccontr)
  assume "k\<noteq> k'"
  have "k' \<le> k" using assms encomp_at_idx_leq by simp 
  hence "k' < k" using \<open>k\<noteq> k'\<close> by simp
  hence "k'+1 \<le> k" by simp
  hence "gamma2 (k'+1) \<le> gamma2 k" using assms monoE by blast
  moreover have "gamma2 k < gamma2 (k'+1)" 
    using assms encomp_atD1 by fastforce
  ultimately show False by simp
qed

lemma encomp_at_refl:
  fixes gamma::"'a::{one, plus}\<Rightarrow> real"
  shows "encomp_at gamma gamma i i"
proof
  show "gamma i \<le> gamma i" by simp
  show "gamma (i+1) \<le> gamma (i+1)" by simp
qed

subsection \<open>Finer price grids\<close>

definition finer_range:: "(int \<Rightarrow> real) \<Rightarrow> (int \<Rightarrow> real) \<Rightarrow> bool" where
"finer_range gamma1 gamma2 \<equiv> (\<forall>i. \<exists>k. encomp_at gamma1 gamma2 i k)"

definition finer_grid where
"finer_grid P1 P2 \<equiv> finer_range (grd P1) (grd P2)"

lemma finer_grid_range[simp]:
  assumes "finer_grid P1 P2"
  shows "finer_range (grd P1) (grd P2)" 
  using assms unfolding finer_grid_def by simp

definition coarse_idx where
"coarse_idx gamma1 gamma2 i = 
  (THE k. encomp_at gamma1 gamma2 i k)"

definition finer_idx_bound where
"finer_idx_bound gamma1 gamma2 i = 
  (THE k. gamma1 k = gamma2 (coarse_idx gamma1 gamma2 i))"

lemma finer_range_refl:
  shows "finer_range gamma gamma" using encomp_at_refl 
  unfolding finer_range_def by auto

locale finer_ranges =
  fixes gamma1::"int \<Rightarrow> real" and gamma2::"int \<Rightarrow> real"
  assumes stm: "strict_mono gamma1"
  and mon: "mono gamma2"
  and fin: "finer_range gamma1 gamma2"

begin

lemma encomp_idx_unique:
  shows "\<exists>!k. encomp_at gamma1 gamma2 i k"
proof -
  have ex: "\<exists>k. encomp_at gamma1 gamma2 i k"
    using stm mon fin unfolding finer_range_def by simp
  {
    fix k k'
    assume "encomp_at gamma1 gamma2 i k'"
      and "encomp_at gamma1 gamma2 i k"
    hence "k = k'" using encomp_at_unique stm mon fin by auto
  }
  thus ?thesis using ex by auto
qed

lemma coarse_idx_bounds:
shows "encomp_at gamma1 gamma2 i (coarse_idx gamma1 gamma2 i)"
proof -
  define P where "P = (\<lambda>k. encomp_at gamma1 gamma2 i k)"
  have "P (coarse_idx gamma1 gamma2 i)" unfolding P_def coarse_idx_def 
    by (metis (no_types, lifting) encomp_idx_unique the_equality)
  thus ?thesis using P_def by simp 
qed

lemma encompassed_bounds:
  shows "i \<in> encompassed gamma1 gamma2 (coarse_idx gamma1 gamma2 i)"
  using fin coarse_idx_bounds unfolding encompassed_def by auto

lemma encompassed_unique:
  assumes "i \<in> encompassed gamma1 gamma2 k"
  shows "k = coarse_idx gamma1 gamma2 i"
  using assms coarse_idx_bounds encompassed_def encomp_idx_unique by blast

lemma encompassed_inj:
  assumes "k\<noteq> k'"
  shows "encompassed gamma1 gamma2 k \<inter> encompassed gamma1 gamma2 k' = {}"
proof (rule ccontr)
  assume "encompassed gamma1 gamma2 k \<inter> encompassed gamma1 gamma2 k' \<noteq> {}"
  hence "\<exists>i. i \<in> encompassed gamma1 gamma2 k \<inter> encompassed gamma1 gamma2 k'"
    by auto
  from this obtain i where "i \<in> encompassed gamma1 gamma2 k" and
    "i \<in> encompassed gamma1 gamma2 k'" by auto
  hence "k = k'" using encompassed_unique by auto
  thus False using assms by simp
qed

lemma coarse_idx_eq:
  assumes "gamma2 k' \<le> gamma1 i"
  and "gamma1 i < gamma2 (k'+1)"
shows "k' = coarse_idx gamma1 gamma2 i"
proof (rule ccontr)
  assume "k' \<noteq> coarse_idx gamma1 gamma2 i"
  define k where "k = coarse_idx gamma1 gamma2 i"
  have gam: "encomp_at gamma1 gamma2 i k"
    using k_def assms by (simp add: coarse_idx_bounds) 
  hence "k' \<le> k" 
    using stm mon fin assms encomp_at_idx_leq encomp_idx_unique by blast 
  hence "k' < k" using \<open>k'\<noteq> coarse_idx gamma1 gamma2 i\<close> k_def by simp
  hence "k'+1 \<le> k" by simp
  hence "gamma2 (k'+1) \<le> gamma2 k" using assms stm mon monoE by blast
  moreover have "gamma2 k < gamma2 (k'+1)" 
    using assms gam \<open>k' \<noteq> coarse_idx gamma1 gamma2 i\<close> encomp_idx_unique 
      k_def encomp_atD1 by fastforce
  ultimately show False by simp
qed

lemma coarse_idx_reached:
  assumes "gamma1 m \<le> gamma2 k"
  and "gamma2 k < gamma1 M"
  and "k = coarse_idx gamma1 gamma2 i"
shows "\<exists>j. gamma1 j = gamma2 k"
proof (rule ccontr)
  assume "\<not>(\<exists>j. gamma1 j = gamma2 k)"
  hence "\<forall>j. gamma1 j \<noteq> gamma2 k" by simp 
  have "gamma2 k \<le> gamma1 i" using coarse_idx_bounds assms
    by (simp add: encomp_atD1)
  define X where "X = gamma1`{j. m \<le> j \<and> gamma1 j \<le> gamma2 k}"
  have "gamma1 m\<in> X" using assms X_def by simp
  hence "X \<noteq> {}" by auto
  have "X \<subseteq> gamma1`{m..M}" 
  proof
    fix x
    assume "x\<in> X"
    hence "\<exists>l. l\<in> {j. m \<le> j \<and> gamma1 j \<le> gamma2 k} \<and> x  = gamma1 l" 
      unfolding X_def by auto
    from this obtain l where "m \<le> l" and "gamma1 l \<le> gamma2 k" 
      and "x = gamma1 l" by auto
    hence "l \<le> M" using assms stm 
      by (meson linorder_not_less nle_le order_trans strict_mono_less_eq)
    hence "l \<in> {m..M}" using \<open>m \<le> l\<close> by simp
    thus "x \<in> gamma1 ` {m..M}" using \<open>x = gamma1 l\<close> by simp
  qed
  hence "finite X" using finite_surj by blast 
  hence "Sup X \<in> X"
    by (metis \<open>X \<noteq> {}\<close> infinite_growing le_cSup_finite less_cSupD nless_le)
  hence "\<exists>l. l\<in> {j. m \<le> j \<and> gamma1 j \<le> gamma2 k} \<and> Sup X  = gamma1 l" 
    unfolding X_def by auto
  from this obtain l where "m \<le> l" and "gamma1 l \<le> gamma2 k" 
    and "Sup X = gamma1 l" by auto
  hence "gamma1 l < gamma2 k" using \<open>\<forall>j. gamma1 j \<noteq> gamma2 k\<close>
    by (simp add:  less_eq_real_def) 
  have "bdd_above X" unfolding X_def using assms by auto
  have "gamma1 l < gamma1 (l+1)" using assms stm  by (simp add: monotoneD)
  hence "gamma1 (l+1) \<notin> X" using \<open>Sup X  = gamma1 l\<close> cSup_upper \<open>bdd_above X\<close> 
    by fastforce
  hence "gamma2 k < gamma1 (l+1)" using \<open>m\<le> l\<close> unfolding X_def
    by fastforce
  show False
  proof (cases "gamma2 (k-1) \<le> gamma1 l")
    case True
    hence "k-1 = coarse_idx gamma1 gamma2 l" 
      using \<open>gamma1 l < gamma2 k\<close> coarse_idx_eq assms encomp_atI  by simp
    hence "gamma1 (l+1) \<le> gamma2 k" using coarse_idx_bounds assms
      by (metis (mono_tags, opaque_lifting) add_diff_cancel diff_add_eq 
          encomp_atD2) 
    then show ?thesis using \<open>gamma2 k < gamma1 (l+1)\<close> by simp
  next
    case False
    hence "gamma1 l < gamma2 (k-1)" by simp
    define k' where "k' = coarse_idx gamma1 gamma2 l"
    have gam2: "gamma2 k' \<le> gamma1 l \<and> gamma1 (l+1) \<le> gamma2 (k'+1)" 
      using assms k'_def encomp_atD1 encomp_atD2 coarse_idx_bounds
      by metis
    hence "gamma2 k' < gamma2 (k-1)" using \<open>gamma1 l < gamma2 (k-1)\<close> by simp
    hence "k' < k-1" using assms stm mon mono_strict_invE by blast 
    have "gamma2 k < gamma2 (k'+1)" 
      using gam2 \<open>gamma2 k < gamma1 (l+1)\<close> by simp
    hence "k < k'+1" using assms stm mon mono_strict_invE by blast 
    then show ?thesis using \<open>k' < k-1\<close> by simp
  qed
qed

lemma coarse_idx_reached_unique:
  assumes "gamma1 m \<le> gamma2 k"
  and "gamma2 k < gamma1 M"
  and "k = coarse_idx gamma1 gamma2 i"
shows "\<exists>!j. gamma1 j = gamma2 k"
proof -
  have "\<exists>j. gamma1 j = gamma2 k" using assms coarse_idx_reached by simp
  from this obtain j where "gamma1 j = gamma2 k" by auto
  {
      fix i
    assume "gamma1 i = gamma2 k"
    hence "gamma1 i = gamma1 j" using \<open>gamma1 j = gamma2 k\<close> by simp
    hence "i = j" using assms stm by (simp add: strict_mono_eq)
  }
  thus ?thesis using \<open>gamma1 j = gamma2 k\<close> by blast
qed

lemma encomp_idx_mono:
  assumes "i < j"
  and "encomp_at gamma1 gamma2 i k"
  and "encomp_at gamma1 gamma2 j l"
  and "k\<noteq> l"
  shows "k < l"
proof (rule ccontr)
  assume "\<not> k < l"
  hence "l \<le> k" by simp
  hence "l < k" using assms by simp
  hence "l+1 \<le> k" by simp
  hence "gamma2 (l+1) \<le> gamma2 k" using mon
    by (meson leD linorder_le_less_linear mono_strict_invE)
  also have "... \<le> gamma1 i" using encomp_atD1[of gamma1 gamma2] assms 
    by simp
  also have "... < gamma1 (i+1)" using stm
    by (simp add: strict_mono_less)
  also have "... \<le> gamma1 j" using assms stm strict_mono_less_eq 
      zless_imp_add1_zle by blast 
  also have "... < gamma1 (j+1)" using stm
    by (simp add: strict_mono_less)
  also have "... \<le> gamma2 (l+1)" using assms encomp_atD2[of gamma1 gamma2] 
    by simp
  finally show False by simp
qed

lemma encomp_idx_mono':
  assumes "i \<le> j"
  and "encomp_at gamma1 gamma2 i k"
  and "encomp_at gamma1 gamma2 j l"
shows "k \<le> l"
proof (cases "i = j")
  case True
  then show ?thesis
    using assms encomp_idx_unique by auto 
next
  case False
  hence "i < j" using assms by simp
  show ?thesis 
  proof (cases "k = l")
    case True
    then show ?thesis by simp
  next
    case False
    then show ?thesis using \<open>i < j\<close> assms encomp_idx_mono[of i j k l] 
      by simp
  qed
qed

lemma encomp_idx_mono_conv:
  assumes "k < l"
  and "encomp_at gamma1 gamma2 i k"
  and "encomp_at gamma1 gamma2 j l"
  shows "i < j"
proof (rule ccontr)
  assume "\<not> i < j"
  hence "j < i" using assms \<open>\<not> i < j\<close> encomp_at_unique 
      linorder_less_linear mon stm by blast 
  hence "l < k" using encomp_idx_mono assms by simp
  thus False using assms by simp
qed

lemma finer_idx_bound_eq:
  assumes "gamma1 m \<le> gamma2 (coarse_idx gamma1 gamma2 i)"
  and "gamma2 (coarse_idx gamma1 gamma2 i) < gamma1 M"
shows "gamma1 (finer_idx_bound gamma1 gamma2 i) =
  gamma2 (coarse_idx gamma1 gamma2 i)"
proof -
  define P where "P = (\<lambda>i. gamma1 (finer_idx_bound gamma1 gamma2 i) =
    gamma2 (coarse_idx gamma1 gamma2 i))"
  have "P i" unfolding P_def finer_idx_bound_def
  proof (rule theI', rule coarse_idx_reached_unique)
    show "gamma1 m \<le> gamma2 (coarse_idx gamma1 gamma2 i)" using assms by simp
    show "gamma2 (coarse_idx gamma1 gamma2 i) < gamma1 M" using assms by simp
  qed (simp add: assms)
  thus ?thesis using assms P_def by simp 
qed

lemma finer_idx_bound_exists_eq:
  assumes "\<exists>m. gamma1 m \<le> gamma2 (coarse_idx gamma1 gamma2 i)"
  and "\<exists>M. gamma2 (coarse_idx gamma1 gamma2 i) < gamma1 M"
shows "gamma1 (finer_idx_bound gamma1 gamma2 i) =
  gamma2 (coarse_idx gamma1 gamma2 i)" using assms finer_idx_bound_eq by auto

lemma finer_idx_bound_eq':
  assumes "i \<in> encompassed gamma1 gamma2 k" 
  and "gamma1 m \<le> gamma2 k"
  and "gamma2 k < gamma1 M"
shows "gamma1 (finer_idx_bound gamma1 gamma2 i) = gamma2 k"
proof -
  have "k = coarse_idx gamma1 gamma2 i" using encompassed_unique assms by simp
  thus ?thesis using finer_idx_bound_eq assms by simp
qed

lemma finer_idx_bound_exists_eq':
  assumes "i \<in> encompassed gamma1 gamma2 k" 
  and "\<exists>m. gamma1 m \<le> gamma2 k"
  and "\<exists>M. gamma2 k < gamma1 M"
shows "gamma1 (finer_idx_bound gamma1 gamma2 i) = gamma2 k"
  using assms finer_idx_bound_eq' by auto

lemma finer_idx_bound_mem:
  assumes "gamma1 m \<le> gamma2 (coarse_idx gamma1 gamma2 i)"
  and "gamma2 (coarse_idx gamma1 gamma2 i + 1) \<le> gamma1 M"
  and "gamma2 (coarse_idx gamma1 gamma2 i) \<noteq> 
    gamma2 (coarse_idx gamma1 gamma2 i + 1)"
shows "finer_idx_bound gamma1 gamma2 i \<in> 
  encompassed gamma1 gamma2 (coarse_idx gamma1 gamma2 i)"
proof -
  define k where "k = coarse_idx gamma1 gamma2 i"
  have "gamma2 k < gamma2 (k+1)" using mon assms
    by (metis k_def less_eq_real_def monotoneD zle_add1_eq_le zless_add1_eq)
  hence "gamma2 k < gamma1 M" using assms k_def by simp
  define idx where "idx = finer_idx_bound gamma1 gamma2 i"
  have "gamma1 idx = gamma2 k"
    using assms finer_idx_bound_eq idx_def k_def \<open>gamma2 k < gamma1 M\<close> 
    by simp
  hence "gamma1 (idx + 1) \<le> gamma2 (k+1)"
    by (metis \<open>gamma2 k < gamma2 (k + 1)\<close> coarse_idx_bounds coarse_idx_eq 
        encomp_at_def less_eq_real_def)
  thus ?thesis 
    using \<open>gamma1 idx = gamma2 k\<close> coarse_idx_eq encompassed_bounds 
      idx_def k_def
    by (metis \<open>gamma2 k < gamma2 (k + 1)\<close> order_refl)
qed

lemma finer_idx_bound_reached:
  assumes "gamma1 m \<le> gamma2 (coarse_idx gamma1 gamma2 i)"
  and "gamma2 (coarse_idx gamma1 gamma2 i) < gamma1 M"
  and "gamma1 i = gamma2 (coarse_idx gamma1 gamma2 i)"
shows "i = finer_idx_bound gamma1 gamma2 i"
  using assms coarse_idx_reached_unique finer_idx_bound_eq by blast

lemma finer_idx_bound_leq:
  assumes "gamma1 m \<le> gamma2 (coarse_idx gamma1 gamma2 i)"
  and "gamma2 (coarse_idx gamma1 gamma2 i) < gamma1 M"
shows "finer_idx_bound gamma1 gamma2 i \<le> i"
proof-
  have "gamma1 (finer_idx_bound gamma1 gamma2 i) =
    gamma2 (coarse_idx gamma1 gamma2 i)" 
    using assms finer_idx_bound_eq by simp
  also have "... \<le> gamma1 i" using assms coarse_idx_bounds
    by (simp add: encomp_atD1)
  finally have "gamma1 (finer_idx_bound gamma1 gamma2 i) \<le> gamma1 i" .
  thus ?thesis using assms stm by (simp add: strict_mono_less_eq)
qed

lemma finer_idx_bound_proj:
  assumes "i \<in> encompassed gamma1 gamma2 k"
  and "j \<in> encompassed gamma1 gamma2 k"
  and "gamma1 m \<le> gamma2 k"
  and "gamma2 k < gamma1 M"
shows "finer_idx_bound gamma1 gamma2 i = finer_idx_bound gamma1 gamma2 j"
proof (rule ccontr)
  define fi where "fi = finer_idx_bound gamma1 gamma2 i"
  define fj where "fj = finer_idx_bound gamma1 gamma2 j"
  assume "fi \<noteq> fj"
  have "gamma1 fi = gamma2 k" using finer_idx_bound_eq' assms fi_def by simp
  moreover have "gamma1 fj = gamma2 k" 
    using finer_idx_bound_eq' assms fj_def by simp
  ultimately show False using stm by (metis \<open>fi \<noteq> fj\<close> strict_mono_eq)
qed

lemma finer_idx_bound_min:
  assumes "i \<in> encompassed gamma1 gamma2 k"
  and "j \<in> encompassed gamma1 gamma2 k"
  and "gamma1 m \<le> gamma2 k"
  and "gamma2 k < gamma1 M"
shows "finer_idx_bound gamma1 gamma2 i \<le> j"
  using assms finer_idx_bound_proj finer_idx_bound_leq
  by (metis encompassed_unique)

lemma coarse_idx_finer_bound:
  assumes "gamma1 m \<le> gamma2 (coarse_idx gamma1 gamma2 i)"
  and "gamma2 (coarse_idx gamma1 gamma2 i) < gamma1 M"
shows "coarse_idx gamma1 gamma2 (finer_idx_bound gamma1 gamma2 i) =
  coarse_idx gamma1 gamma2 i"
proof -
  define j where "j = finer_idx_bound gamma1 gamma2 i"
  define k where "k = coarse_idx gamma1 gamma2 i"
  have "j \<le> i" 
    using j_def assms finer_ranges.finer_idx_bound_leq finer_ranges_axioms 
    by blast
  hence "gamma1 (j+1) \<le> gamma1 (i+1)" using stm
    by (simp add: strict_mono_less_eq)
  hence "gamma1 (j+1) \<le> gamma2 (k+1)" 
    using k_def encomp_atD2 coarse_idx_bounds order.trans by metis
  moreover have "gamma2 k \<le> gamma1 j" using assms k_def j_def
    by (simp add: finer_idx_bound_eq)  
  ultimately show ?thesis using k_def j_def encomp_at_unique
    using assms stm mon coarse_idx_bounds encomp_atI by blast
qed

lemma finer_idx_bound_invol:
  assumes "gamma1 m \<le> gamma2 (coarse_idx gamma1 gamma2 i)"
  and "gamma2 (coarse_idx gamma1 gamma2 i) < gamma1 M"
shows "finer_idx_bound gamma1 gamma2 (finer_idx_bound gamma1 gamma2 i) =
  finer_idx_bound gamma1 gamma2 i"
  using assms coarse_idx_finer_bound finer_idx_bound_eq finer_idx_bound_reached 
  by auto

lemma reached_imp_coarse:
  assumes "gamma1 i = gamma2 k"
  and "gamma2 k \<noteq> gamma2 (k+1)"
shows "gamma1 (i+1) \<le> gamma2 (k+1)"
proof (rule ccontr)
  assume "\<not> gamma1 (i + 1) \<le> gamma2 (k + 1)"
  hence asm: "gamma2 (k+1) < gamma1 (i+1)" by simp
  have "gamma2 k < gamma2 (k+1)" using assms mon
    by (metis linorder_neqE_linordered_idom mono_strict_invE 
        order.asym zless_add1_eq)
  have "\<exists>j. encomp_at gamma1 gamma2 i j" 
    using fin finer_range_def by simp
  hence "\<exists>j. gamma2 j \<le> gamma1 i \<and> gamma1 (i+1) \<le> gamma2 (j+1)" 
    using encomp_atD1 encomp_atD2 by blast
  from this obtain j where "gamma2 j \<le> gamma1 i" 
    and "gamma1 (i+1) \<le> gamma2 (j+1)"
    by auto note jpr = this
  have "gamma2 j \<le> gamma2 k" using jpr assms by simp
  moreover have "gamma2 (k+1) < gamma2 (j+1)" using jpr asm by simp
  ultimately show False using mon
    by (metis assms(2) dual_order.trans mono_strict_invE monotoneD 
        order_antisym_conv zle_add1_eq_le zless_add1_eq)
qed

lemma less_imp_coarse:
  assumes "gamma1 m < gamma2 k"
  and "gamma2 k \<le> gamma1 M"
  and "gamma2 k \<noteq> gamma2 (k+1)" 
shows "\<exists>i. encomp_at gamma1 gamma2 i k"
proof (rule ccontr)
  assume "\<not>(\<exists>i. encomp_at gamma1 gamma2 i k)"
  hence asm: "\<forall>i. gamma1 i < gamma2 k \<or> gamma2 (k+1) < gamma1 (i+1)"
    using not_le_imp_less unfolding encomp_at_def by auto
  define B where "B = {i. m \<le> i \<and> gamma1 i < gamma2 k}"
  define A where "A = {i. gamma2 (k+1) < gamma1 (i+1)}"
  have "m \<in> B" using assms B_def by simp
  define j1 where "j1 = Sup B + 1"
  have "\<forall>j\<in> B. m\<le> j" using B_def stm by simp
  moreover have "\<forall>j\<in> B. j \<le> M" 
    using assms stm B_def linorder_not_less strict_monoD by fastforce 
  ultimately have "B\<subseteq> {m..M}" by auto
  hence "finite B" using finite_subset by auto 
  hence "Sup B \<in> B"
    by (metis \<open>m \<in> B\<close> dual_order.strict_iff_order finite_imp_Sup_less 
        le_cSup_finite) 
  hence "j1 \<notin> B"
    using \<open>finite B\<close> j1_def le_cSup_finite zle_add1_eq_le by blast
  hence "j1 \<in> A" using asm A_def B_def \<open>Sup B \<in> B\<close> j1_def by force
  hence "gamma2 (k+1) < gamma1 (j1 + 1)" using A_def by simp
  have "\<exists>l. gamma2 l \<le> gamma1 j1 \<and> gamma1 (j1+1) \<le> gamma2 (l+1)" 
    using fin finer_range_def encomp_atD1 encomp_atD2 by metis
  from this obtain l1 where "gamma2 l1 \<le> gamma1 j1" 
    and "gamma1 (j1 + 1) \<le> gamma2 (l1+1)"
    by auto note lppr = this
  show False
  proof (cases "gamma2 (k+1) \<le> gamma1 j1")
    case True
    define j where "j = Sup B"
    have "j1 = j+1" using j_def j1_def by simp
    have "\<exists>l. gamma2 l \<le> gamma1 j \<and> gamma1 (j+1) \<le> gamma2 (l+1)" 
      using fin finer_range_def encomp_atD1 encomp_atD2 by metis
    from this obtain l where "gamma2 l \<le> gamma1 j" 
      and "gamma1 (j + 1) \<le> gamma2 (l+1)"
      by auto note lpr = this
    have "gamma2 l < gamma2 k" using \<open>Sup B \<in> B\<close> j_def lpr
      by (simp add: B_def)
    hence "l < k" using mon mono_strict_invE by blast 
    hence "l+1 \<le> k" by simp
    hence "gamma2 (l+1) \<le> gamma2 k" using mon
      by (meson leI less_le_not_le mono_strict_invE)
    moreover have "gamma2 (k+1) \<le> gamma2 (l+1)" 
      using lpr True \<open>j1 = j + 1\<close> dual_order.trans by blast
    ultimately have "gamma2 (k+1) \<le> gamma2 k" by simp
    hence "gamma2 (k+1) = gamma2 k" 
      using mon
      by (meson assms(3) dual_order.order_iff_strict mono_strict_invE 
          order_less_imp_not_less zless_add1_eq)
    thus ?thesis using assms by simp
  next
    case False
    hence "gamma1 j1 < gamma2 (k+1)" by simp    
    have "gamma2 (k+1) < gamma2 (l1 + 1)" using lppr \<open>j1\<in> A\<close> A_def by auto
    hence "k +1 < l1+ 1" using mon mono_strict_invE by blast
    hence "k+1 \<le> l1" by simp
    hence "gamma2 (k+1) \<le> gamma2 l1" using mon by (simp add: monotoneD)
    hence "gamma1 j1 < gamma2 l1" using \<open>gamma1 j1 < gamma2 (k+1)\<close> by simp
    thus ?thesis using lppr by simp
  qed
qed

lemma ex_coarse_rep:
  assumes "gamma1 m \<le> gamma2 k"
  and "gamma2 k \<le> gamma1 M"
  and "gamma2 k \<noteq> gamma2 (k+1)" 
shows "\<exists>i. encomp_at gamma1 gamma2 i k"
proof (cases "gamma1 m = gamma2 k")
  case True
  then show ?thesis using assms reached_imp_coarse
    by (metis encomp_at_def)
next
  case False
  hence "gamma1 m < gamma2 k" using assms by simp
  then show ?thesis using less_imp_coarse assms by simp
qed

lemma encompassed_ne:
  assumes "gamma1 m \<le> gamma2 k"
  and "gamma2 k \<le> gamma1 M"
  and "gamma2 k \<noteq> gamma2 (k+1)" 
shows "encompassed gamma1 gamma2 k \<noteq> {}" 
  using assms ex_coarse_rep unfolding encompassed_def by simp

lemma encompassed_ne':
  assumes "\<exists>m. gamma1 m \<le> gamma2 k"
  and "\<exists>M. gamma2 k \<le> gamma1 M"
  and "gamma2 k \<noteq> gamma2 (k+1)" 
shows "encompassed gamma1 gamma2 k \<noteq> {}" 
  using assms encompassed_ne by auto

lemma encompassed_finite:
  assumes "gamma1 m \<le> gamma2 k"
  and "gamma2 (k+1) \<le> gamma1 M"
  and "gamma2 k \<noteq> gamma2 (k+1)" 
shows "finite (encompassed gamma1 gamma2 k)"
proof -
  have "gamma2 k < gamma2 (k+1)" using mon assms
    by (metis linorder_neqE_linordered_idom mono_strict_invE 
        order.asym zless_add1_eq)
  hence lt: "gamma2 k < gamma1 M" using  assms by simp
  have "encompassed gamma1 gamma2 k \<noteq> {}" using assms encompassed_ne lt
    by (meson nless_le)
  hence "\<exists>i. i \<in> encompassed gamma1 gamma2 k" by auto
  from this obtain i where "i \<in> encompassed gamma1 gamma2 k" by auto
  hence "k = coarse_idx gamma1 gamma2 i" using encompassed_unique by simp
  define j where "j = finer_idx_bound gamma1 gamma2 i"
  hence "gamma1 j = gamma2 k" 
    using finer_idx_bound_eq assms \<open>k = coarse_idx gamma1 gamma2 i\<close> lt
    by simp
  have "\<forall>l\<in> encompassed gamma1 gamma2 k. j \<le> l" 
    using finer_idx_bound_min j_def assms \<open>i \<in> encompassed gamma1 gamma2 k\<close> lt
    by auto
  moreover have "\<forall>l\<in> encompassed gamma1 gamma2 k. l < M"
  proof
    fix l
    assume "l\<in> encompassed gamma1 gamma2 k"
    hence "gamma1 (l+1) \<le> gamma1 M" using encomp_at_def assms
      by (metis (mono_tags, opaque_lifting) coarse_idx_bounds 
          dual_order.strict_trans2 encompassed_unique linorder_not_le)
    thus "l < M" using stm
      by (simp add: strict_mono_less_eq)
  qed
  ultimately have "encompassed gamma1 gamma2 k \<subseteq> {j..< M}" by auto
  thus ?thesis by (simp add: finite_subset) 
qed

lemma encompassed_finite':
  assumes "\<exists>m. gamma1 m \<le> gamma2 k"
  and "\<exists>M. gamma2 (k+1) \<le> gamma1 M"
  and "gamma2 k \<noteq> gamma2 (k+1)" 
shows "finite (encompassed gamma1 gamma2 k)" using assms encompassed_finite 
  by auto

lemma encompassed_Min_in:
  assumes "gamma1 m \<le> gamma2 k"
  and "gamma2 (k+1) \<le> gamma1 M"
  and "gamma2 k \<noteq> gamma2 (k+1)"
shows "Min (encompassed gamma1 gamma2 k) \<in> encompassed gamma1 gamma2 k"
proof -
  define j where "j = Min (encompassed gamma1 gamma2 k)"
  have "gamma2 k \<le> gamma2 (k+1)" using mon by (simp add: monoD)
  hence "gamma2 k \<le> gamma1 M" using assms by simp 
  hence "encompassed gamma1 gamma2 k \<noteq> {}" using assms encompassed_ne by simp
  thus "j\<in> encompassed gamma1 gamma2 k" 
    using encompassed_finite encompassed_ne j_def assms by simp 
qed

lemma encompassed_Max_in:
  assumes "gamma1 m \<le> gamma2 k"
  and "gamma2 (k+1) \<le> gamma1 M"
  and "gamma2 k \<noteq> gamma2 (k+1)"
shows "Max (encompassed gamma1 gamma2 k) \<in> encompassed gamma1 gamma2 k"
proof -
  define j where "j = Max (encompassed gamma1 gamma2 k)"
  have "gamma2 k \<le> gamma2 (k+1)" using mon by (simp add: monoD)
  hence "gamma2 k \<le> gamma1 M" using assms by simp 
  hence "encompassed gamma1 gamma2 k \<noteq> {}" using assms encompassed_ne by simp
  thus "j\<in> encompassed gamma1 gamma2 k" 
    using encompassed_finite encompassed_ne j_def assms by simp 
qed

lemma encompassed_min_gamma_eq:
  assumes "gamma1 m \<le> gamma2 k"
  and "gamma2 (k+1) \<le> gamma1 M"
  and "gamma2 k \<noteq> gamma2 (k+1)"
shows "gamma1 (Min (encompassed gamma1 gamma2 k)) = gamma2 k"
proof -
  have "gamma2 k < gamma2 (k+1)" using mon assms
    by (metis less_eq_real_def monotoneD zle_add1_eq_le zless_add1_eq)
  hence "gamma2 k < gamma1 M" using assms by simp
  define me where "me = Min (encompassed gamma1 gamma2 k)"
  define fb where "fb = finer_idx_bound gamma1 gamma2 me"
  have "fb \<in> encompassed gamma1 gamma2 k" using fb_def finer_idx_bound_mem
    by (metis assms(1) assms(2) assms(3) encompassed_Min_in encompassed_unique 
        me_def)
  hence "me \<le> fb" using me_def
    using assms finer_ranges.encompassed_finite finer_ranges_axioms by auto 
  have "me \<in> encompassed gamma1 gamma2 k" 
    using encompassed_Min_in[of m k M] assms me_def by simp
  hence "fb \<le> me" using finer_idx_bound_min assms \<open>gamma2 k < gamma1 M\<close> fb_def
    by blast
  hence "fb = me" using \<open>me \<le> fb\<close> by simp
  thus ?thesis using assms fb_def \<open>gamma2 k < gamma1 M\<close> 
      \<open>fb \<in> encompassed gamma1 gamma2 k\<close> me_def finer_idx_bound_eq'[of fb]
    by simp
qed

lemma encompassed_min_gamma_eq':
  assumes "\<exists>m. gamma1 m \<le> gamma2 k"
  and "\<exists>M. gamma2 (k+1) \<le> gamma1 M"
  and "gamma2 k \<noteq> gamma2 (k+1)"
shows "gamma1 (Min (encompassed gamma1 gamma2 k)) = gamma2 k"
  using assms encompassed_min_gamma_eq by auto

lemma coarse_idx_upper: 
  assumes "gamma2 k < gamma1 j"
  and "j\<notin> encompassed gamma1 gamma2 k"
shows "k < coarse_idx gamma1 gamma2 j"
proof (rule ccontr)
  define k' where "k' = coarse_idx gamma1 gamma2 j"
  assume "\<not> k < coarse_idx gamma1 gamma2 j"
  hence "k' \<le> k" using k'_def by simp
  have "j\<in> encompassed gamma1 gamma2 k'"
    by (simp add: encompassed_bounds k'_def)
  hence "k'\<noteq> k" using assms by auto
  hence "k' < k" using \<open>k' \<le> k\<close> by simp
  hence "k'+1 < k+1" by simp
  have "\<not> encomp_at gamma1 gamma2 j k" using assms encompassed_def by auto
  hence "\<not> gamma2 k \<le> gamma1 j \<or> \<not> gamma1 (j + 1) \<le> gamma2 (k + 1)"
    using encomp_atI by auto
  hence "\<not> gamma1 (j + 1) \<le> gamma2 (k + 1)" using assms by simp
  hence "gamma2 (k+1) < gamma1 (j+1)" by simp
  moreover have "gamma1 (j+1) \<le> gamma2 (k' + 1)" 
    using \<open>j\<in> encompassed gamma1 gamma2 k'\<close> coarse_idx_bounds 
      encomp_at_def k'_def 
    by blast
  ultimately have "gamma2 (k+1) < gamma2 (k'+1)" by simp
  thus False using \<open>k'+1 < k+1\<close> mon mono_strict_invE by fastforce
qed

lemma encompassed_max_Suc_eq:
  assumes "gamma1 m \<le> gamma2 k"
  and "gamma2 (k+1) \<le> gamma1 M"
  and "gamma2 k \<noteq> gamma2 (k+1)"
  and "gamma2 (k+1) \<noteq> gamma2 (k+2)"
  shows "Max (encompassed gamma1 gamma2 k) + 1 \<in> 
    encompassed gamma1 gamma2 (k+1)"
proof -
  define j where "j = Max (encompassed gamma1 gamma2 k)"
  have "j\<in> encompassed gamma1 gamma2 k" 
    using encompassed_Max_in j_def assms by simp 
  hence "gamma1 (j+1) \<le> gamma2 (k+1)" using encompassed_def encomp_at_def 
    by blast
  have "gamma1 j < gamma1 (j+1)" using stm
    by (simp add: strict_mono_less) 
  hence "gamma2 k < gamma1 (j+1)" 
    using \<open>j\<in> encompassed gamma1 gamma2 k\<close>  encomp_at_def
    by (metis coarse_idx_bounds dual_order.trans encompassed_unique 
        less_eq_real_def nle_le) 
  have "gamma2 (k+1) \<le> gamma2 (k+2)" using mon
    by (simp add: monotoneD)
  hence "gamma2 (k+1) < gamma2 (k+2)" using assms by simp
  define k' where "k' = coarse_idx gamma1 gamma2 (j+1)"
  have "gamma2 k' \<le> gamma1 (j+1)" using k'_def
    by (simp add: coarse_idx_bounds encomp_atD1)
  hence "gamma2 k' \<le> gamma2 (k+1)" using \<open>gamma1 (j+1) \<le> gamma2 (k+1)\<close> by simp
  have "j+1 \<notin> encompassed gamma1 gamma2 k" using j_def
    by (meson Max_ge assms encompassed_finite linorder_not_less zless_add1_eq)
  hence "k < k'" using coarse_idx_upper k'_def \<open>gamma2 k < gamma1 (j+1)\<close> by simp
  hence "k+1 \<le> k'" by simp
  hence "gamma2 (k+1) \<le> gamma2 k'" using mon by (simp add: monoD)
  hence "gamma2 k' = gamma2 (k+1)" using \<open>gamma2 k' \<le> gamma2 (k+1)\<close> by simp
  hence "gamma2 k' < gamma2 (k+2)" using \<open>gamma2 (k+1) < gamma2 (k+2)\<close> by simp
  hence "k' \<le> k+1" using mon mono_strict_invE by fastforce
  hence "k' = k+1" using \<open>k+1 \<le> k'\<close> by simp
  thus ?thesis using j_def encompassed_bounds k'_def by fastforce
qed

lemma encompassed_max_Suc_gamma_eq:
  assumes "gamma1 m \<le> gamma2 k"
  and "gamma2 (k+2) \<le> gamma1 M"
  and "gamma2 k \<noteq> gamma2 (k+1)"
  and "gamma2 (k+1) \<noteq> gamma2 (k+2)"
shows "gamma1 (Max (encompassed gamma1 gamma2 k) + 1) = gamma2 (k+1)"
proof -
  have "gamma2 (k+1) \<le> gamma2 (k+2)" using assms mon
    by (simp add: monotoneD)
  hence "gamma2 (k+1) \<le> gamma1 M" using assms by simp
  have "gamma2 k \<le> gamma2 (k+1)" using assms mon
    by (simp add: monotoneD)
  hence "gamma1 m \<le> gamma2 (k+1)" using assms by simp
  have maxin: "Max (encompassed gamma1 gamma2 k) \<in> 
    encompassed gamma1 gamma2 k"
    using encompassed_Max_in assms \<open>gamma2 (k+1) \<le> gamma1 M\<close> by simp
  define sm where "sm = Max (encompassed gamma1 gamma2 k)+1"
  have "sm \<in> encompassed gamma1 gamma2 (k+1)"
    using encompassed_max_Suc_eq sm_def assms \<open>gamma2 (k+1) \<le> gamma1 M\<close> 
    by simp
  have "sm = Min (encompassed gamma1 gamma2 (k+1))" 
  proof (rule Min_eqI[symmetric])
    show "finite (encompassed gamma1 gamma2 (k + 1))"
    proof (rule encompassed_finite)
      show "gamma1 m \<le> gamma2 (k+1)" using \<open>gamma1 m \<le> gamma2 (k+1)\<close> .
      show "gamma2 (k + 1) \<noteq> gamma2 (k + 1 + 1)" using assms
        by (simp add: add.assoc)
      show "gamma2 (k + 1 + 1) \<le> gamma1 M" using \<open>gamma2 (k+2) \<le> gamma1 M\<close>
        by (simp add: add.assoc)
    qed
    show "sm \<in> encompassed gamma1 gamma2 (k + 1)" 
      using \<open>sm \<in> encompassed gamma1 gamma2 (k + 1)\<close> .
    fix j
    assume "j\<in> encompassed gamma1 gamma2 (k+1)"
    hence "coarse_idx gamma1 gamma2 j = k+1"
      using encompassed_unique by auto 
    show "sm \<le> j"
    proof (rule ccontr)
      assume "\<not> sm \<le> j"
      hence "j < sm" by simp
      hence "j \<le> Max (encompassed gamma1 gamma2 k)" using sm_def by simp
      hence "k+1 \<le> k"
      proof (rule encomp_idx_mono')
        show "encomp_at gamma1 gamma2 j (k + 1)"
          using \<open>j\<in> encompassed gamma1 gamma2 (k+1)\<close> unfolding encompassed_def 
          by auto
        show "encomp_at gamma1 gamma2 (Max (encompassed gamma1 gamma2 k)) k"
          using maxin unfolding encompassed_def by auto
      qed
      thus False by simp
    qed
  qed
  thus ?thesis using sm_def
    by (metis \<open>sm \<in> encompassed gamma1 gamma2 (k + 1)\<close> coarse_idx_bounds 
        dual_order.order_iff_strict encomp_atD1 encomp_atD2 encompassed_unique 
        less_le_not_le maxin)
qed
  
lemma encompassed_max_Suc_gamma_eq':
  assumes "\<exists>m. gamma1 m \<le> gamma2 k"
  and "\<exists>M. gamma2 (k+2) \<le> gamma1 M"
  and "gamma2 k \<noteq> gamma2 (k+1)"
  and "gamma2 (k+1) \<noteq> gamma2 (k+2)"
shows "gamma1 (Max (encompassed gamma1 gamma2 k) + 1) = gamma2 (k+1)"
  using assms encompassed_max_Suc_gamma_eq by auto

end

lemma coarse_idx_refl:
  fixes gamma::"int \<Rightarrow> real"
  assumes "strict_mono gamma"
  shows "i = coarse_idx gamma gamma i" 
proof (rule finer_ranges.coarse_idx_eq) 
  show "finer_ranges gamma gamma" unfolding finer_ranges_def
  proof (intro conjI)
    show "strict_mono gamma" using assms by simp
    thus "mono gamma" by (simp add: strict_mono_mono) 
    show "finer_range gamma gamma" using finer_range_refl by simp
  qed
  show "gamma i \<le> gamma i" by simp
  show "gamma i < gamma (i+1)" using assms unfolding strict_mono_def by simp
qed

subsection \<open>Pools with finer grids and coinciding profiles\<close>

definition pool_coarse_idx where
"pool_coarse_idx = (\<lambda>P1 P2 i. coarse_idx (grd P1) (grd P2) i)" 

lemma pool_coarse_idxD:
  assumes "k = pool_coarse_idx P1 P2 i"
  shows "k = coarse_idx (grd P1) (grd P2) i" 
  using assms unfolding pool_coarse_idx_def by simp

definition pool_finer_idx_bound where
"pool_finer_idx_bound = (\<lambda>P1 P2 i. finer_idx_bound (grd P1) (grd P2) i)"

lemma pool_finer_idx_boundD:
  assumes "l = pool_finer_idx_bound P1 P2 i"
  shows "l = finer_idx_bound (grd P1) (grd P2) i" 
  using assms unfolding pool_finer_idx_bound_def by simp

definition finer_pool where
"finer_pool P1 P2 \<equiv> finer_grid P1 P2 \<and>
  (\<forall>i. lq P1 i = lq P2 (pool_coarse_idx P1 P2 i)) \<and>
  (\<forall>i. fee P1 i = fee P2 (pool_coarse_idx P1 P2 i))"

lemma finer_poolI[intro]:
  assumes "finer_range (grd P1) (grd P2)"
  and "(\<forall>i. lq P1 i = lq P2 (pool_coarse_idx P1 P2 i))"
  and "(\<forall>i. fee P1 i = fee P2 (pool_coarse_idx P1 P2 i))"
shows "finer_pool P1 P2" 
  using assms unfolding finer_pool_def finer_grid_def by simp

lemma finer_poolD:
  assumes "finer_pool P1 P2" shows
  "finer_range (grd P1) (grd P2)"
  "\<forall>i. lq P1 i = lq P2 (pool_coarse_idx P1 P2 i)"
  "\<forall>i. fee P1 i = fee P2 (pool_coarse_idx P1 P2 i)" 
  using assms unfolding finer_pool_def by auto

lemma finer_pool_refl:
  assumes "strict_mono (grd P)"
  shows "finer_pool P P"
proof
  show "finer_range (grd P) (grd P)" using finer_range_refl by simp
  have i: "\<forall>i. pool_coarse_idx P P i = i" 
    using coarse_idx_refl assms unfolding pool_coarse_idx_def by simp
  thus "\<forall>i. lq P i = lq P (pool_coarse_idx P P i)" by simp
  show "\<forall>i. fee P i = fee P (pool_coarse_idx P P i)" using i by simp
qed

locale finer_pools = 
  fixes P1 P2
  assumes fin_pool: "finer_pool P1 P2"

begin

lemma finer_pool_grid:
  shows "finer_range (grd P1) (grd P2)" using fin_pool unfolding finer_pool_def 
  by simp

lemma finer_pool_liq:
  shows "\<forall>i. lq P1 i = lq P2 (pool_coarse_idx P1 P2 i)" 
  using fin_pool unfolding finer_pool_def 
  by simp

lemma finer_pool_fee:
  shows "\<forall>i. fee P1 i = fee P2 (pool_coarse_idx P1 P2 i)" 
  using fin_pool unfolding finer_pool_def 
  by simp

lemma encompassed_liq_eq:
  assumes "strict_mono (grd P1)"
  and "mono (grd P2)"
and "i \<in> encompassed (grd P1) (grd P2) k"
shows "lq P1 i = lq P2 k" 
proof -
  have "k = coarse_idx (grd P1) (grd P2) i"
    using assms finer_ranges.encompassed_unique finer_pool_grid
    by (simp add: finer_ranges.intro) 
  thus ?thesis using finer_pool_liq assms pool_coarse_idx_def by metis
qed

lemma encompassed_fee_eq:
  assumes "strict_mono (grd P1)"
  and "mono (grd P2)"
and "i \<in> encompassed (grd P1) (grd P2) k"
shows "fee P1 i = fee P2 k" 
proof -
  have "k = coarse_idx (grd P1) (grd P2) i"
    using assms finer_ranges.encompassed_unique finer_pool_grid
    by (simp add: finer_ranges.intro) 
  thus ?thesis using finer_pool_fee assms pool_coarse_idx_def by metis
qed

lemma sum_rng_token: 
  assumes "strict_mono (grd P1)"
  and "mono (grd P2)"
  and "grd P1 m1 \<le> grd P2 k"
  and "grd P2 (k+1) \<le> grd P1 M1"
  and "grd P2 k \<noteq> grd P2 (k + 1)"
  and "\<And> a b.  a \<in> encompassed (grd P1) (grd P2) b \<Longrightarrow> 
    g (lq P1) a = g' (lq P2) b"
  and "\<forall>i \<in> encompassed (grd P1) (grd P2) k. dff x i = f (i+1) - f i"
shows "sum (rng_token dff (g (lq P1)) x) 
    (encompassed (grd P1) (grd P2) k) =
    (g' (lq P2)) k * (f (Max (encompassed (grd P1) (grd P2) k) + 1) - 
    f (Min (encompassed (grd P1) (grd P2) k)))" 
proof -
  interpret finer_ranges "grd P1" "grd P2" 
    using assms finer_pool_grid by (simp add: finer_ranges_def)
  define Ek where "Ek = encompassed (grd P1) (grd P2) k"
  define m where "m = Min Ek"
  define M where "M = Max Ek"
  have "m \<le> M" using m_def M_def encompassed_Min_in encompassed_Max_in assms
    by (metis Ek_def Min.coboundedI encompassed_finite)
  have "Ek = {m..M}" unfolding Ek_def m_def M_def 
    proof (rule encompassed_interval)
      show "mono (grd P1)"
        by (simp add: assms strict_mono_on_imp_mono_on)
      show "finite (encompassed (grd P1) (grd P2) k)" 
        using encompassed_finite assms by blast
      show "encompassed (grd P1) (grd P2) k \<noteq> {}" 
        using encompassed_ne assms encompassed_Max_in by fastforce
    qed
  have "(\<Sum>i\<in>Ek. (g (lq P1)) i * dff x i) = (\<Sum>i\<in>Ek. (g' (lq P2)) k * dff x i)"
  proof (rule sum.cong)
    fix i
    assume "i \<in> Ek"
    hence "g (lq P1) i = g' (lq P2) k" using assms Ek_def by simp
    thus "(g (lq P1)) i * dff x i = (g' (lq P2)) k * dff x i" by simp
  qed simp
  also have "... = (g' (lq P2)) k * (\<Sum>i\<in>Ek. dff x i)"
    by (simp add: sum_distrib_left)
  also have "... = (g' (lq P2)) k * (\<Sum>i\<in>{m..M}. dff x i)" using \<open>Ek = {m..M}\<close> 
    by simp
  also have "... = (g' (lq P2)) k * (f (M+1) - f m)"
  proof -
    have "(\<Sum>i\<in>{m..M}. dff x i) = (\<Sum>i\<in>{m..M}. (f (i+1) - f i))" 
    proof (rule sum.cong)
      fix y
      assume "y\<in> {m..M}"
      thus "dff x y = f (y+1) - f y" using assms \<open>Ek = {m..M}\<close> Ek_def by simp
    qed simp
    also have "... = f (M+1) - f m" using int_telescoping_sum_le' \<open>m \<le> M\<close>
      by auto
    finally show ?thesis by simp
  qed
  finally have "(\<Sum>i\<in>Ek. (g (lq P1)) i * dff x i) = 
    (g' (lq P2)) k * (f (M+1) - f m)" .
  thus ?thesis unfolding Ek_def M_def m_def rng_token_def by simp
qed

lemma sum_rng_gen_quote: 
  assumes "strict_mono (grd P1)"
  and "mono (grd P2)"
  and "grd P1 m1 \<le> grd P2 k"
  and "grd P2 (k+2) \<le> grd P1 M1"
  and "grd P2 k \<noteq> grd P2 (k + 1)"
  and "grd P2 (k+1) \<noteq> grd P2 (k + 2)"
  and "\<And> a b.  a \<in> encompassed (grd P1) (grd P2) b \<Longrightarrow> 
    f (lq P1) a = f' (lq P2) b"
shows "sum (rng_gen_quote (grd P1) (f (lq P1)) x) 
  (encompassed (grd P1) (grd P2) k) =
  rng_gen_quote (grd P2) (f' (lq P2)) x k" 
proof -
  interpret finer_ranges "grd P1" "grd P2" 
    using assms finer_pool_grid by (simp add: finer_ranges_def)
  have "grd P2 (k+1) \<le> grd P2 (k+2)" using mon
    by (simp add: monotoneD) 
  hence "grd P2 (k + 1) \<le> grd P1 M1" using assms by simp
  have "sum (rng_gen_quote (grd P1) (f (lq P1)) x) 
      (encompassed (grd P1) (grd P2) k) =
    (f' (lq P2)) k *
    (min x ((grd P1) (Max (encompassed (grd P1) (grd P2) k) + 1)) -
     min x ((grd P1) (Min (encompassed (grd P1) (grd P2) k))))"
    unfolding rng_gen_quote_def
  proof (rule sum_rng_token)
    show "grd P1 m1 \<le> grd P2 k" using assms by simp
    show "grd P2 (k + 1) \<le> grd P1 M1" using \<open>grd P2 (k + 1) \<le> grd P1 M1\<close> .
    show "grd P2 k \<noteq> grd P2 (k + 1)" using assms by simp
    show "\<forall>i\<in>encompassed (grd P1) (grd P2) k.
      gamma_min_diff (grd P1) x i = min x (grd P1 (i + 1))- min x (grd P1 i)"
      unfolding gamma_min_diff_def by simp
    show "\<And> a b.  a \<in> encompassed (grd P1) (grd P2) b \<Longrightarrow> 
      f (lq P1) a = f' (lq P2) b" using assms 
      by simp
  qed (simp add: assms)+
  also have "... = (f' (lq P2)) k * (min x (grd P2 (k+1)) - min x (grd P2 k))" 
  proof -
    have "(grd P1) (Min (encompassed (grd P1) (grd P2) k)) = grd P2 k"
      by (meson assms encompassed_min_gamma_eq \<open>grd P2 (k + 1) \<le> grd P1 M1\<close>)
    moreover have "(grd P1) (Max (encompassed (grd P1) (grd P2) k) + 1) = 
      grd P2 (k+1)"
      using assms encompassed_max_Suc_gamma_eq by auto
    ultimately show ?thesis by simp
  qed
  finally show ?thesis 
    unfolding rng_token_def gamma_min_diff_def rng_gen_quote_def .
qed

lemma sum_rng_gen_base: 
  assumes "strict_mono (grd P1)"
  and "mono (grd P2)"
  and "grd P1 m1 \<le> grd P2 k"
  and "grd P2 (k+2) \<le> grd P1 M1"
  and "grd P2 k \<noteq> grd P2 (k + 1)"
  and "grd P2 (k+1) \<noteq> grd P2 (k + 2)"
  and "\<And> a b.  a \<in> encompassed (grd P1) (grd P2) b \<Longrightarrow> 
    f (lq P1) a = f' (lq P2) b"
shows "sum (rng_gen_base (grd P1) (f (lq P1)) x) 
  (encompassed (grd P1) (grd P2) k) =
  rng_gen_base (grd P2) (f' (lq P2)) x k" 
proof -
  interpret finer_ranges "grd P1" "grd P2" 
    using assms finer_pool_grid by (simp add: finer_ranges_def)
  have "grd P2 (k+1) \<le> grd P2 (k+2)" using mon
    by (simp add: monotoneD) 
  hence "grd P2 (k + 1) \<le> grd P1 M1" using assms by simp
  have "sum (rng_gen_base (grd P1) (f (lq P1)) x) 
      (encompassed (grd P1) (grd P2) k) =
    (f' (lq P2)) k *
    (-inverse (max x ((grd P1) (Max (encompassed (grd P1) (grd P2) k) + 1))) -
     (-inverse (max x ((grd P1) (Min (encompassed (grd P1) (grd P2) k))))))"
    unfolding rng_gen_base_def 
  proof (rule sum_rng_token)
    show "grd P1 m1 \<le> grd P2 k" using assms by simp
    show "grd P2 (k + 1) \<le> grd P1 M1" using \<open>grd P2 (k + 1) \<le> grd P1 M1\<close> .
    show "grd P2 k \<noteq> grd P2 (k + 1)" using assms by simp
    show "\<forall>i\<in>encompassed (grd P1) (grd P2) k.
      inv_gamma_max_diff (grd P1) x i = 
      - inverse (max x (grd P1 (i + 1))) - - inverse (max x (grd P1 i))"
      unfolding inv_gamma_max_diff_def by simp
    show "\<And> a b.  a \<in> encompassed (grd P1) (grd P2) b \<Longrightarrow> 
      f (lq P1) a = f' (lq P2) b" using assms by simp
  qed (simp add: assms)+
  also have "... = (f' (lq P2)) k *
    (inverse (max x ((grd P1) (Min (encompassed (grd P1) (grd P2) k)))) -
    inverse (max x ((grd P1) (Max (encompassed (grd P1) (grd P2) k) + 1))))"
    by simp
  also have "... = (f' (lq P2)) k * 
    (inverse (max x (grd P2 k)) - inverse (max x (grd P2 (k+1))))" 
  proof -
    have "(grd P1) (Min (encompassed (grd P1) (grd P2) k)) = grd P2 k"
      by (meson assms encompassed_min_gamma_eq \<open>grd P2 (k + 1) \<le> grd P1 M1\<close>)
    moreover have "(grd P1) (Max (encompassed (grd P1) (grd P2) k) + 1) = 
      grd P2 (k+1)"
      using assms encompassed_max_Suc_gamma_eq by auto
    ultimately show ?thesis by simp
  qed
  finally show ?thesis 
    unfolding rng_token_def inv_gamma_max_diff_def rng_gen_base_def .
qed

lemma finer_imp_finite_liq:
  assumes "strict_mono (grd P1)"
  and "mono (grd P2)"
  and "finite_liq P2"
  and "\<And>k. lq P2 k \<noteq> 0 \<Longrightarrow> finite (encompassed (grd P1) (grd P2) k)"
  shows "finite_liq P1"
proof -
  interpret finer_ranges "grd P1" "grd P2" 
    using assms finer_pool_grid by (simp add: finer_ranges_def)
  have "{i. lq P1 i \<noteq> 0} \<subseteq> 
    (\<Union> (encompassed (grd P1) (grd P2) ` {k. lq P2 k \<noteq> 0}))"
  proof  
    fix i
    assume "i\<in> {i. lq P1 i \<noteq> 0}"
    hence "lq P1 i \<noteq> 0" by simp
    define k where "k = coarse_idx (grd P1) (grd P2) i"
    have "i \<in> encompassed (grd P1) (grd P2) k" using k_def encompassed_bounds 
      by simp
    moreover have "lq P2 k \<noteq> 0" using \<open>lq P1 i \<noteq> 0\<close> k_def finer_pool_liq
      by (metis pool_coarse_idx_def) 
    ultimately show "i \<in> (\<Union> (encompassed (grd P1) (grd P2)` {k. lq P2 k \<noteq> 0}))"
      by auto
  qed
  thus ?thesis
    by (metis (mono_tags, lifting) assms(3) assms(4) finite_UN_I 
        finite_liqD finite_liqI finite_subset mem_Collect_eq)
qed

lemma finer_imp_finite_liq':
  assumes "finer_pool P1 P2"
  and "strict_mono (grd P1)"
  and "mono (grd P2)"
  and "finite_liq P1"
  and "finite {k. encompassed (grd P1) (grd P2) k = {}}"
  shows "finite_liq P2"
proof -
  interpret finer_ranges "grd P1" "grd P2" 
    using assms finer_pool_grid by (simp add: finer_ranges_def)
  have "{k. lq P2 k \<noteq> 0} \<subseteq> 
    {k. encompassed (grd P1) (grd P2) k = {}} \<union>
    coarse_idx (grd P1) (grd P2) `{i. lq P1 i \<noteq> 0}"
  proof  
    fix k
    assume "k\<in> {i. lq P2 i \<noteq> 0}"
    hence "lq P2 k \<noteq> 0" by simp
    show "k \<in> {k. encompassed (grd P1) (grd P2) k = {}} \<union>
      coarse_idx (grd P1) (grd P2) `{i. lq P1 i \<noteq> 0}"
    proof
      assume asm: "k \<notin> coarse_idx (grd P1) (grd P2) ` {i. lq P1 i \<noteq> 0}"
      show "k \<in> {k. encompassed (grd P1) (grd P2) k = {}}"
      proof (rule ccontr)
        assume "k \<notin> {k. encompassed (grd P1) (grd P2) k = {}}"
        hence "encompassed (grd P1) (grd P2) k \<noteq> {}" by simp
        hence "\<exists>i. i \<in> encompassed (grd P1) (grd P2) k" by auto
        from this obtain i where "i \<in> encompassed (grd P1) (grd P2) k" by auto
        hence "k = coarse_idx (grd P1) (grd P2) i" 
          by (simp add: encompassed_unique)
        hence "lq P1 i \<noteq> 0" 
          using assms \<open>lq P2 k \<noteq> 0\<close> finer_pool_liq pool_coarse_idx_def 
          by presburger
        hence "k \<in> coarse_idx (grd P1) (grd P2) ` {i. lq P1 i \<noteq> 0}"
          using \<open>k = coarse_idx (grd P1) (grd P2) i\<close> by blast
        thus False using asm by simp
      qed
    qed
  qed
  moreover have "finite (coarse_idx (grd P1) (grd P2) `{i. lq P1 i \<noteq> 0})"
    using assms finite_liqD by auto
  ultimately show ?thesis using assms
    by (metis finite_UnI finite_liqI rev_finite_subset)
qed

end

subsection \<open>Spanning grids\<close>

definition span_grid where
"span_grid P \<longleftrightarrow> strict_mono (grd P) \<and> (\<forall>i. 0 < grd P i) \<and>
    (\<forall>r>0. \<exists>i. grd P i < r) \<and> (\<forall> r. \<exists>i. r < grd P i)"

lemma span_gridD:
  assumes "span_grid P"
  shows "strict_mono (grd P)" "\<forall>i. 0 < grd P i"
    "\<forall>r>0. \<exists>i. grd P i < r" "\<forall> r. \<exists>i. r < grd P i"
  using assms unfolding span_grid_def by simp+

lemma span_gridI[intro]:
  assumes "strict_mono (grd P)" 
  and "\<forall>i. 0 < grd P i"
  and "\<forall>r>0. \<exists>i. grd P i < r" 
  and "\<forall> r. \<exists>i. r < grd P i"
shows "span_grid P" using assms unfolding span_grid_def by simp

lemma span_grid_eq:
  assumes "span_grid P"
  and "grd P = grd P'"
shows "span_grid P'" using assms unfolding span_grid_def by simp

locale finer_spanning_pool = finer_pools +
  assumes span: "span_grid P1"

begin

lemma finer_spanning_gt:
shows "\<exists>i. r < grd P2 i"
proof -
  have "\<exists>i. r < grd P1 i" using span span_gridD by simp
  from this obtain i where "r < grd P1 i" by auto
  hence "r < grd P1 (i+1)" using span
    by (metis dual_order.strict_trans less_add_one monotoneD 
        span_gridD(1))
  have "\<exists>k. encomp_at (grd P1) (grd P2) i k" using span finer_range_def
    finer_pool_grid by simp
  from this obtain k where "encomp_at (grd P1) (grd P2) i k" by auto
  hence "grd P1 (i+1) \<le> grd P2 (k+1)" using encomp_atD2[of "grd P1" _ i k] 
    by simp
  hence "r < grd P2 (k+1)" using \<open>r < grd P1 (i + 1)\<close> by auto
  thus ?thesis by auto
qed

lemma finer_spanning_lt:
  assumes "0 < r"
shows "\<exists>i. grd P2 i < r"
proof -
  have "\<exists>i. grd P1 i < r" using assms finer_pool_grid span_gridD
    by (simp add: span) 
  from this obtain i where "grd P1 i < r" by auto
  have "\<exists>k. encomp_at (grd P1) (grd P2) i k" using assms finer_pool_grid span
    by (simp add: finer_range_def)
  from this obtain k where "encomp_at (grd P1) (grd P2) i k" by auto
  hence "grd P2 k \<le> grd P1 i" using encomp_atD1[of "grd P1" _ i k] 
    by simp
  hence "grd P2 k < r" using \<open>grd P1 i < r\<close> by auto
  thus ?thesis by auto
qed

lemma finer_span_grid:
  assumes "\<forall>i. 0 < grd P2 i"
  and "strict_mono (grd P2)"
shows "span_grid P2"
proof
  show "strict_mono (grd P2)" using assms by simp
  show "\<forall>i. 0 < grd P2 i" using assms by simp 
  show "\<forall>r. \<exists>i. r < grd P2 i" using finer_spanning_gt assms by simp
  show "\<forall>r>0. \<exists>i. grd P2 i < r" using finer_spanning_lt assms by simp
qed

end 

locale finer_two_spanning_pools = finer_spanning_pool +
  assumes span2: "span_grid P2"

sublocale finer_two_spanning_pools \<subseteq> finer_ranges "grd P1" "grd P2"
proof (rule finer_ranges.intro)
  show "strict_mono (grd P1)" using span span_gridD by simp
  show "mono (grd P2)" using span span2
    by (simp add: span_gridD(1) strict_mono_on_imp_mono_on)
  show "finer_range (grd P1) (grd P2)" using  finer_pool_grid by simp
qed

context finer_two_spanning_pools
begin

lemma spanning_sum_rng_gen_quote: 
  assumes "\<And> a b.  a \<in> encompassed (grd P1) (grd P2) b \<Longrightarrow> 
    f (lq P1) a = f' (lq P2) b"
shows "sum (rng_gen_quote (grd P1) (f (lq P1)) x) 
  (encompassed (grd P1) (grd P2) k) =
  rng_gen_quote (grd P2) (f' (lq P2)) x k"
proof -
  have b: "strict_mono (grd P1)" using assms span_gridD span by simp
  have c: "mono (grd P2)" using span2 span_gridD
    by (simp add: strict_mono_mono)
  have d: "grd P2 k \<noteq> grd P2 (k + 1)" using span2 span_gridD
    by (simp add: strict_mono_eq)
  have e: "grd P2 (k + 1) \<noteq> grd P2 (k + 2)" using span2 span_gridD 
    by (simp add: strict_mono_eq)
  have "\<exists>m. grd P1 m \<le> grd P2 k" using span2 span_gridD span
    by (meson order_less_imp_le)
  moreover have "\<exists>M. grd P2 k \<le> grd P1 M" using assms span_gridD span
    by (meson order_less_imp_le)
  ultimately show ?thesis using sum_rng_gen_quote[OF b c _ _ d e]
    by (meson assms less_eq_real_def span span_gridD(4))
qed

lemma spanning_sum_rng_gen_base: 
  assumes "\<And> a b.  a \<in> encompassed (grd P1) (grd P2) b \<Longrightarrow> 
    f (lq P1) a = f' (lq P2) b"
shows "sum (rng_gen_base (grd P1) (f (lq P1)) x) 
  (encompassed (grd P1) (grd P2) k) =
  rng_gen_base (grd P2) (f' (lq P2)) x k"
proof -
  have b: "strict_mono (grd P1)" using assms span span_gridD by simp
  have c: "mono (grd P2)" using span2 span_gridD
    by (simp add: strict_mono_mono)
  have d: "grd P2 k \<noteq> grd P2 (k + 1)" using span2 span_gridD
    by (simp add: strict_mono_eq)
  have e: "grd P2 (k + 1) \<noteq> grd P2 (k + 2)" using span2 span_gridD 
    by (simp add: strict_mono_eq)
  have "\<exists>m. grd P1 m \<le> grd P2 k" using span2 span span_gridD
    by (meson order_less_imp_le)
  moreover have "\<exists>M. grd P2 k \<le> grd P1 M" using assms span span_gridD
    by (meson order_less_imp_le)
  ultimately show ?thesis using sum_rng_gen_base[OF b c _ _ d e]
    by (meson assms span less_eq_real_def span_grid_def)
qed

lemma span_grid_encompassed:
shows "finite (encompassed (grd P1) (grd P2) k)"
proof (rule finer_ranges.encompassed_finite')
  show "\<exists>m. grd P1 m \<le> grd P2 k" using span2 span span_gridD
    by (meson order_less_imp_le)
  show "\<exists>M. grd P2 (k+1) \<le> grd P1 M" using span2 span span_gridD
    by (meson order_less_imp_le)
  show "grd P2 k \<noteq> grd P2 (k + 1)" using span2 span_gridD(1)
    by (simp add: strict_mono_eq)
  show "finer_ranges (grd P1) (grd P2)" unfolding finer_ranges_def
    by (simp add: finer_pool_grid span span2 span_gridD(1) 
        strict_mono_mono)
qed

lemma span_grids_finite_liq:
  assumes "finite_liq P2"
shows "finite_liq P1" 
proof (rule finer_imp_finite_liq)
  show "strict_mono (grd P1)" using assms span span_gridD by simp
  show "finite_liq P2" using assms by simp
  show "mono (grd P2)" using assms span2 span_gridD
    by (simp add: strict_mono_on_imp_mono_on)
  show "\<And>k. lq P2 k \<noteq> 0 \<Longrightarrow> finite (encompassed (grd P1) (grd P2) k)"
    using assms span_grid_encompassed finer_pool_grid by simp
qed

lemma span_grids_ex_le:
shows "\<exists>m. grd P1 m \<le> grd P2 k" 
by (meson span span2 linorder_le_less_linear order.asym 
    span_gridD(2) span_gridD(3))

lemma span_grids_ex_ge:
shows "\<exists>M. grd P2 k \<le> grd P1 M"
  by (meson span nless_le span_gridD(4))

lemma span_grids_encompassed_ne:  
shows "encompassed (grd P1) (grd P2) k \<noteq> {}"
proof (rule encompassed_ne')
  show "\<exists>m. grd P1 m \<le> grd P2 k" using span_grids_ex_le span by simp
  show "\<exists>M. grd P2 k \<le> grd P1 M" using span_grids_ex_ge span by simp
  show "grd P2 k \<noteq> grd P2 (k + 1)" using span2 span_gridD
    by (simp add: strict_mono_eq)
qed

end

subsection \<open>Spanning grids and finite liquidity\<close>

locale finer_two_span_finite_liq = finer_two_spanning_pools +
  assumes fin_liq: "finite_liq P1"

sublocale finer_two_span_finite_liq \<subseteq> finite_liq_pool P1 
  by (unfold_locales, (simp add: fin_liq))

lemma (in finer_two_span_finite_liq) span_grids_finite_liq':
shows "finite_liq P2" 
proof (rule finer_imp_finite_liq')
  show "finer_pool P1 P2" using fin_pool fin_pool by simp
  show "strict_mono (grd P1)" using span span_gridD by simp
  show "finite_liq P1" using fin_liq by simp
  show "mono (grd P2)" using span2 span_gridD
    by (simp add: strict_mono_on_imp_mono_on)
  have "\<forall>k. encompassed (grd P1) (grd P2) k \<noteq> {}" 
    using span_grids_encompassed_ne
    by (simp add: finer_pool_grid)
  thus "finite {k. encompassed (grd P1) (grd P2) k = {}}" by simp
qed

sublocale finer_two_span_finite_liq \<subseteq> finite_liq_pool P2 
  by (unfold_locales, (simp add: span_grids_finite_liq'))

context finer_two_span_finite_liq
begin

lemma finer_pool_encompassed_Union:
shows "(\<Union> (encompassed (grd P1) (grd P2) `{i. lq P2 i \<noteq> 0})) = 
  {i. lq P1 i \<noteq> 0}"
proof
  show "\<Union> (encompassed (grd P1) (grd P2) `{i. lq P2 i \<noteq> 0}) \<subseteq> {i. lq P1 i \<noteq> 0}"
  proof
    fix j
    assume "j \<in> \<Union> (encompassed (grd P1) (grd P2) ` {i. lq P2 i \<noteq> 0})"
    hence "\<exists>k. lq P2 k \<noteq> 0 \<and> j \<in> encompassed (grd P1) (grd P2) k" by auto
    from this obtain k where "lq P2 k \<noteq> 0" and 
      "j \<in> encompassed (grd P1) (grd P2) k" by auto
    hence "k = pool_coarse_idx P1 P2 j" 
      using pool_coarse_idx_def encompassed_unique by metis
    hence "lq P1 j = lq P2 k" using span_grids_finite_liq' finer_pool_liq 
      by simp
    hence "lq P1 j \<noteq> 0" using \<open>lq P2 k \<noteq> 0\<close> by simp
    thus "j\<in> {i. lq P1 i \<noteq> 0}" by simp
  qed
  show "{i. lq P1 i \<noteq> 0} \<subseteq> \<Union> (encompassed (grd P1) (grd P2)` {i. lq P2 i \<noteq> 0})"
  proof
    fix j
    assume "j\<in> {i. lq P1 i\<noteq> 0}"
    hence "lq P1 j \<noteq> 0" by simp
    hence "lq P2 (pool_coarse_idx P1 P2 j) \<noteq> 0" 
      using pool_coarse_idx_def finer_pool_liq by simp
    hence "pool_coarse_idx P1 P2 j \<in> {i. lq P2 i \<noteq> 0}" by simp
    moreover have "j \<in> encompassed (grd P1) (grd P2) (pool_coarse_idx P1 P2 j)"
      using encompassed_bounds unfolding pool_coarse_idx_def by auto 
    ultimately show "j \<in> \<Union> (encompassed (grd P1) (grd P2)` {i. lq P2 i \<noteq> 0})"
      by auto
  qed
qed

lemma spanning_finer_gen_quote_eq:
  assumes "\<And> a b.  a \<in> encompassed (grd P1) (grd P2) b \<Longrightarrow> 
    f (lq P1) a = f' (lq P2) b"
  and "\<And>i. lq P2 i = 0 \<Longrightarrow> f' (lq P2) i = 0"         
  and "\<And>i. lq P1 i = 0 \<Longrightarrow> f (lq P1) i = 0"
  shows "gen_quote (grd P1) (f (lq P1)) x = gen_quote (grd P2) (f' (lq P2)) x"
proof -
  define rg2 where "rg2 = rng_token (gamma_min_diff (grd P2)) (f' (lq P2)) x"
  define Lnz2 where "Lnz2 = {i. lq P2 i \<noteq> 0}"
  define Lnz1 where "Lnz1 = {i. lq P1 i \<noteq> 0}"
  have "finite_liq P1" using fin_liq by simp
  have sm: "\<And> x k. sum (rng_gen_quote (grd P1) (f (lq P1)) x) 
    (encompassed (grd P1) (grd P2) k) =
    rng_gen_quote (grd P2) (f' (lq P2)) x k" 
    using spanning_sum_rng_gen_quote assms by simp
  have "gen_quote (grd P2) (f' (lq P2)) x = sum rg2 Lnz2" 
    unfolding gen_quote_def gen_token_def rg2_def Lnz2_def 
    by (rule finite_support_sum, (simp add: assms)+)
  also have "... = sum (\<lambda>k. sum (rng_gen_quote (grd P1) (f (lq P1)) x) 
    (encompassed (grd P1) (grd P2) k)) Lnz2" 
  proof (rule sum.cong)
    show "\<And>xa. xa \<in> Lnz2 \<Longrightarrow> rg2 xa = sum (rng_gen_quote (grd P1) (f (lq P1)) x) 
      (encompassed (grd P1) (grd P2) xa)" 
    proof -
      fix k
      assume "k\<in> Lnz2"
      show "rg2 k = sum (rng_gen_quote (grd P1) (f (lq P1)) x) 
      (encompassed (grd P1) (grd P2) k)" 
        using sm unfolding rg2_def rng_gen_quote_def by simp
    qed
  qed simp
  also have "... = sum (rng_gen_quote (grd P1) (f (lq P1)) x) 
    (\<Union> (encompassed (grd P1) (grd P2) ` Lnz2))"
  proof (rule sum.UNION_disjoint[symmetric])
    show "finite Lnz2" using Lnz2_def span_grids_finite_liq' finite_liqD 
      by simp
    show "\<forall>i\<in>Lnz2. finite (encompassed (grd P1) (grd P2) i)"
      using assms span_grid_encompassed
      by (simp add: finer_pool_grid) 
    show "\<forall>i\<in>Lnz2. \<forall>j\<in>Lnz2. i \<noteq> j \<longrightarrow> 
      encompassed (grd P1) (grd P2) i \<inter> encompassed (grd P1) (grd P2) j = {}"
      using encompassed_inj by simp
  qed
  also have "... = sum (rng_gen_quote (grd P1) (f (lq P1)) x) Lnz1" 
  proof -
    have "(\<Union> (encompassed (grd P1) (grd P2) ` Lnz2)) = Lnz1" 
      using finer_pool_encompassed_Union Lnz1_def Lnz2_def assms by simp
    thus ?thesis by simp
  qed
  also have "... = infsum (rng_gen_quote (grd P1) (f (lq P1)) x) UNIV" 
    unfolding Lnz1_def rng_gen_quote_def 
  proof (rule finite_nz_support.finite_support_sum[symmetric])
    show "finite_nz_support (lq P1)"
      using fin_liq finite_liq_def finite_nz_support.intro by auto
  qed (simp add: assms)
  finally show ?thesis unfolding gen_quote_def gen_token_def rng_gen_quote_def 
    by simp
qed

lemma spanning_finer_gen_base_eq:
  assumes "\<And> a b.  a \<in> encompassed (grd P1) (grd P2) b \<Longrightarrow> 
    f (lq P1) a = f' (lq P2) b"
  and "\<And>i. lq P2 i = 0 \<Longrightarrow> f' (lq P2) i = 0"         
  and "\<And>i. lq P1 i = 0 \<Longrightarrow> f (lq P1) i = 0"
  shows "gen_base (grd P1) (f (lq P1)) x = gen_base (grd P2) (f' (lq P2)) x"
proof -
  define rg2 where "rg2 =rng_token (inv_gamma_max_diff (grd P2)) (f' (lq P2)) x"
  define Lnz2 where "Lnz2 = {i. lq P2 i \<noteq> 0}"
  define Lnz1 where "Lnz1 = {i. lq P1 i \<noteq> 0}"
  have "finite_liq P1" using fin_liq by simp
  have sm: "\<And> x k. sum (rng_gen_base (grd P1) (f (lq P1)) x) 
    (encompassed (grd P1) (grd P2) k) =
    rng_gen_base (grd P2) (f' (lq P2)) x k" 
    using spanning_sum_rng_gen_base assms by simp
  have "gen_base (grd P2) (f' (lq P2)) x = sum rg2 Lnz2" 
    unfolding gen_base_def gen_token_def rg2_def Lnz2_def 
    by (rule finite_support_sum, (simp add: assms)+)
  also have "... = sum (\<lambda>k. sum (rng_gen_base (grd P1) (f (lq P1)) x) 
    (encompassed (grd P1) (grd P2) k)) Lnz2" 
  proof (rule sum.cong)
    show "\<And>xa. xa \<in> Lnz2 \<Longrightarrow> rg2 xa = sum (rng_gen_base (grd P1) (f (lq P1)) x) 
      (encompassed (grd P1) (grd P2) xa)" 
    proof -
      fix k
      assume "k\<in> Lnz2"
      show "rg2 k = sum (rng_gen_base (grd P1) (f (lq P1)) x) 
      (encompassed (grd P1) (grd P2) k)" 
        using sm unfolding rg2_def rng_gen_base_def by simp
    qed
  qed simp
  also have "... = sum (rng_gen_base (grd P1) (f (lq P1)) x) 
    (\<Union> (encompassed (grd P1) (grd P2) ` Lnz2))"
  proof (rule sum.UNION_disjoint[symmetric])
    show "finite Lnz2" using Lnz2_def assms finite_liqD
      span_grids_finite_liq' by auto
    show "\<forall>i\<in>Lnz2. finite (encompassed (grd P1) (grd P2) i)"
      using assms span_grid_encompassed
      by (simp add: finer_pool_grid) 
    show "\<forall>i\<in>Lnz2. \<forall>j\<in>Lnz2. i \<noteq> j \<longrightarrow> 
      encompassed (grd P1) (grd P2) i \<inter> encompassed (grd P1) (grd P2) j = {}"
      using encompassed_inj by simp
  qed
  also have "... = sum (rng_gen_base (grd P1) (f (lq P1)) x) Lnz1" 
  proof -
    have "(\<Union> (encompassed (grd P1) (grd P2) ` Lnz2)) = Lnz1" 
      using finer_pool_encompassed_Union Lnz1_def Lnz2_def assms by simp
    thus ?thesis by simp
  qed
  also have "... = infsum (rng_gen_base (grd P1) (f (lq P1)) x) UNIV" 
    unfolding Lnz1_def rng_gen_base_def 
  proof (rule finite_nz_support.finite_support_sum[symmetric])
    show "finite_nz_support (lq P1)"
      using fin_liq finite_liq_def finite_nz_support.intro by auto
  qed (simp add: assms)
  finally show ?thesis unfolding gen_base_def gen_token_def rng_gen_base_def 
    by simp
qed

end

end