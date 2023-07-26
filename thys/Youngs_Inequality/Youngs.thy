section \<open>Young's Inequality for Increasing Functions\<close>

text \<open>From the following paper: 
Cunningham, F., and Nathaniel Grossman. ``On Young's Inequality.'' 
The American Mathematical Monthly 78, no. 7 (1971): 781--83. 
\url{https://doi.org/10.2307/2318018}\<close>

theory Youngs imports
  "HOL-Analysis.Analysis" 
   
begin

subsection \<open>Toward Young's inequality\<close>

lemma strict_mono_image_endpoints:
  fixes f :: "'a::linear_continuum_topology \<Rightarrow> 'b::linorder_topology"
  assumes "strict_mono_on {a..b} f" and f: "continuous_on {a..b} f" and "a \<le> b"
  shows "f ` {a..b} = {f a..f b}"
proof
  show "f ` {a..b} \<subseteq> {f a..f b}"
    using assms(1) strict_mono_on_leD by fastforce
  show "{f a..f b} \<subseteq> f ` {a..b}"
    using assms IVT'[OF _ _ _ f] by (force simp: Bex_def)
qed

text \<open>Generalisations of the type of @{term f} are not obvious\<close>
lemma strict_mono_continuous_invD:
  fixes f :: "real \<Rightarrow> real"
  assumes sm: "strict_mono_on {a..} f" and contf: "continuous_on {a..} f" 
    and fim: "f ` {a..} = {f a..}" and g: "\<And>x. x \<ge> a \<Longrightarrow> g (f x) = x"
  shows "continuous_on {f a..} g"
proof (clarsimp simp add: continuous_on_eq_continuous_within)
  fix y
  assume "f a \<le> y"
  then obtain u where u: "y+1 = f u" "u \<ge> a"
    by (smt (verit, best) atLeast_iff fim imageE)
  have "continuous_on {f a..y+1} g" 
  proof -
    obtain "continuous_on {a..u} f"  "strict_mono_on {a..u} f"
      using contf sm continuous_on_subset by (force simp add: strict_mono_on_def)
    moreover have "continuous_on (f ` {a..u}) g"
      using assms continuous_on_subset
      by (intro continuous_on_inv) fastforce+
    ultimately show ?thesis
      using strict_mono_image_endpoints [of _ _ f]
      by (simp add: strict_mono_image_endpoints u)
  qed
  then have *: "continuous (at y within {f a..y+1}) g"
    by (simp add: \<open>f a \<le> y\<close> continuous_on_imp_continuous_within)
  show "continuous (at y within {f a..}) g"
  proof (clarsimp simp add: continuous_within_topological Ball_def)
    fix B
    assume "open B" and "g y \<in> B"
    with * obtain A where A: "open A" "y \<in> A" and "\<And>x. f a \<le> x \<and> x \<le> y+1 \<Longrightarrow> x \<in> A \<longrightarrow> g x \<in> B"
      by (force simp: continuous_within_topological)
    then have "\<forall>x\<ge>f a. x \<in> A \<inter> ball y 1 \<longrightarrow> g x \<in> B"
      by (smt (verit, ccfv_threshold) IntE dist_norm mem_ball real_norm_def)
    then show "\<exists>A. open A \<and> y \<in> A \<and> (\<forall>x\<ge>f a. x \<in> A \<longrightarrow> g x \<in> B)"
      by (metis Elementary_Metric_Spaces.open_ball Int_iff A centre_in_ball open_Int zero_less_one)
  qed
qed

subsection \<open>Regular divisions\<close>

text \<open>Our lack of the Riemann integral forces us to construct explicitly
the step functions mentioned in the text.\<close>

definition "segment \<equiv> \<lambda>n k. {real k / real n..(1 + k) / real n}"

lemma segment_nonempty: "segment n k \<noteq> {}"
  by (auto simp: segment_def divide_simps)

lemma segment_Suc: "segment n ` {..<Suc k} = insert {k/n..(1 + real k) / n} (segment n ` {..<k})"
  by (simp add: segment_def lessThan_Suc)

lemma Union_segment_image: "\<Union> (segment n ` {..<k}) = (if k=0 then {} else {0..real k/real n})"
proof (induction k)
  case (Suc k)
  then show ?case
    by (simp add: divide_simps segment_Suc Un_commute ivl_disj_un_two_touch split: if_split_asm)
qed (auto simp: segment_def)

definition "segments \<equiv> \<lambda>n. segment n ` {..<n}"

lemma card_segments [simp]: "card (segments n) = n"
  by (simp add: segments_def segment_def card_image divide_right_mono inj_on_def)

lemma segments_0 [simp]: "segments 0 = {}"
  by (simp add: segments_def)

lemma Union_segments: "\<Union> (segments n) = (if n=0 then {} else {0..1})"
  by (simp add: segments_def Union_segment_image)

definition "regular_division \<equiv> \<lambda>a b n. (image ((+) a \<circ> (*) (b-a))) ` (segments n)"

lemma translate_scale_01:
  assumes "a \<le> b" 
  shows "(\<lambda>x. a + (b - a) * x) ` {0..1} = {a..b::real}"
  using closed_segment_real_eq [of a b] assms closed_segment_eq_real_ivl by auto

lemma finite_regular_division [simp]: "finite (regular_division a b n)"
  by (simp add: regular_division_def segments_def)

lemma card_regular_division [simp]: 
  assumes "a<b"
  shows "card (regular_division a b n) = n"
proof -
  have "inj_on ((`) ((+) a \<circ> (*) (b - a))) (segments n)"
  proof
    fix x y
    assume "((+) a \<circ> (*) (b - a)) ` x = ((+) a \<circ> (*) (b - a)) ` y"
    then have "(+) (-a) ` ((+) a \<circ> (*) (b - a)) ` x = (+) (-a) ` ((+) a \<circ> (*) (b - a)) ` y"
      by simp
    then have "((*) (b - a)) ` x = ((*) (b - a)) ` y"
      by (simp add: image_comp)
    then have "(*) (inverse(b - a)) ` (*) (b - a) ` x = (*) (inverse(b - a)) ` (*) (b - a) ` y"
      by simp
    then show "x = y"
      using assms by (simp add: image_comp mult_ac)
  qed
  then show ?thesis
    by (metis card_image card_segments regular_division_def)
qed

lemma Union_regular_division:
  assumes "a \<le> b" 
  shows "\<Union>(regular_division a b n) = (if n=0 then {} else {a..b})"
  using assms
  by (auto simp: regular_division_def Union_segments translate_scale_01 simp flip: image_Union)

lemma regular_division_eqI:
  assumes K: "K = {a + (b-a)*(real k / n) .. a + (b-a)*((1 + real k) / n)}"
    and "a<b" "k < n"
  shows "K \<in> regular_division a b n" 
  unfolding regular_division_def segments_def image_comp
proof
  have "K = (\<lambda>x. (b-a) * x + a) ` {real k / real n..(1 + real k) / real n}"
    using K \<open>a<b\<close> by (simp add: image_affinity_atLeastAtMost divide_simps)
  then show "K = ((`) ((+) a \<circ> (*) (b - a)) \<circ> segment n) k" 
    by (simp add: segment_def add.commute)
qed (use assms in auto)

lemma regular_divisionE:
  assumes "K \<in> regular_division a b n" "a<b"
  obtains k where "k<n" "K = {a + (b-a)*(real k / n) .. a + (b-a)*((1 + real k) / n)}"
proof -
  have eq: "(\<lambda>x. a + (b - a) * x) = (\<lambda>x. a + x) \<circ> (\<lambda>x. (b - a) * x)"
    by (simp add: o_def)
  obtain k where "k<n" "K = ((\<lambda>x. a+x) \<circ> (\<lambda>x. (b-a) * x)) ` {k/n .. (1 + real k) / n}"
    using assms by (auto simp: regular_division_def segments_def segment_def)
  with that \<open>a<b\<close> show ?thesis
    unfolding image_comp [symmetric]  by auto
qed

lemma regular_division_division_of:
  assumes "a < b" "n>0"
  shows "(regular_division a b n) division_of {a..b}"
proof (rule division_ofI)
  show "finite (regular_division a b n)"
    by (simp add: regular_division_def segments_def)
  show \<section>: "\<Union> (regular_division a b n) = {a..b}"
    using Union_regular_division assms by simp
  fix K
  assume K: "K \<in> regular_division a b n"
  then obtain k where Keq: "K = {a + (b-a)*(k/n) .. a + (b-a)*((1 + real k) / n)}" 
    using \<open>a<b\<close> regular_divisionE by meson
  show "K \<subseteq> {a..b}"
    using K Union_regular_division \<open>n>0\<close> by (metis Union_upper \<section>)
  show "K \<noteq> {}"
    using K by (auto simp: regular_division_def segment_nonempty segments_def)
  show "\<exists>a b. K = cbox a b"
    by (metis K \<open>a<b\<close> box_real(2) regular_divisionE)
  fix K'
  assume K': "K' \<in> regular_division a b n" and "K \<noteq> K'"
  then obtain k' where Keq': "K' = {a + (b-a)*(k'/n) .. a + (b-a)*((1 + real k') / n)}" 
    using K \<open>a<b\<close> regular_divisionE by meson
  consider "1 + real k \<le> k'" | "1 + real k' \<le> k"
    using Keq Keq' \<open>K \<noteq> K'\<close> by force
  then show "interior K \<inter> interior K' = {}"
  proof cases
    case 1
    then show ?thesis
      by (simp add: Keq Keq' min_def max_def divide_right_mono assms)
  next
    case 2
    then have "interior K' \<inter> interior K = {}"
      by (simp add: Keq Keq' min_def max_def divide_right_mono assms)
    then show ?thesis
      by (simp add: inf_commute)
  qed
qed

subsection \<open>Special cases of Young's inequality\<close>

lemma weighted_nesting_sum:
  fixes g :: "nat \<Rightarrow> 'a::comm_ring_1"
  shows "(\<Sum>k<n. (1 + of_nat k) * (g (Suc k) - g k)) = of_nat n * g n - (\<Sum>i<n. g i)"
  by (induction n) (auto simp: algebra_simps)

theorem Youngs_exact:
  fixes f :: "real \<Rightarrow> real"
  assumes sm: "strict_mono_on {0..} f" and cont: "continuous_on {0..} f" and a: "a\<ge>0" 
    and f: "f 0 = 0" "f a = b"
    and g: "\<And>x. \<lbrakk>0 \<le> x; x \<le> a\<rbrakk> \<Longrightarrow> g (f x) = x"
  shows "a*b = integral {0..a} f + integral {0..b} g" 
proof (cases "a=0")
  case False
  with \<open>a \<ge> 0\<close> have "a > 0" by linarith
  then have "b \<ge> 0"
    by (smt (verit, best) atLeast_iff f sm strict_mono_onD)
  have sm_0a: "strict_mono_on {0..a} f"
    by (metis atLeastAtMost_iff atLeast_iff sm strict_mono_on_def)
  have cont_0a: "continuous_on {0..a} f"
    using cont continuous_on_subset by fastforce
  with sm_0a have "continuous_on {0..b} g"
    by (metis a atLeastAtMost_iff compact_Icc continuous_on_inv f g strict_mono_image_endpoints)
  then have intgb_g: "g integrable_on {0..b}"
    using integrable_continuous_interval by blast
  have intgb_f: "f integrable_on {0..a}"
    using cont_0a integrable_continuous_real by blast

  have f_iff [simp]: "f x < f y \<longleftrightarrow> x < y" "f x \<le> f y \<longleftrightarrow> x \<le> y"
    if "x \<ge> 0" "y \<ge> 0" for x y
    using that by (smt (verit, best) atLeast_iff sm strict_mono_onD)+
  have fim: "f ` {0..a} = {0..b}"
    by (simp add: \<open>a \<ge> 0\<close> cont_0a strict_mono_image_endpoints strict_mono_on_def f)
  have "uniformly_continuous_on {0..a} f"
    using compact_uniformly_continuous cont_0a by blast
  then obtain del where del_gt0: "\<And>e. e>0 \<Longrightarrow> del e > 0" 
        and del:  "\<And>e x x'. \<lbrakk>\<bar>x'-x\<bar> < del e; e>0; x \<in> {0..a}; x' \<in> {0..a}\<rbrakk> \<Longrightarrow> \<bar>f x' - f x\<bar> < e"
    unfolding uniformly_continuous_on_def dist_real_def by metis

  have *: "\<bar>a * b - integral {0..a} f - integral {0..b} g\<bar> < 2*\<epsilon>" if "\<epsilon> > 0" for \<epsilon>
  proof -
    define \<delta> where "\<delta> = min a (del (\<epsilon>/a)) / 2"
    have "\<delta> > 0" "\<delta> \<le> a"
      using \<open>a > 0\<close> \<open>\<epsilon> > 0\<close> del_gt0 by (auto simp: \<delta>_def)
    define n where "n \<equiv> nat\<lfloor>a / \<delta>\<rfloor>"
    define a_seg where "a_seg \<equiv> \<lambda>u::real. u * a/n"
    have "n > 0"
      using  \<open>a > 0\<close> \<open>\<delta> > 0\<close> \<open>\<delta> \<le> a\<close> by (simp add: n_def)
    have a_seg_ge_0 [simp]: "a_seg x \<ge> 0 \<longleftrightarrow> x \<ge> 0" 
     and a_seg_le_a [simp]: "a_seg x \<le> a \<longleftrightarrow> x \<le> n" for x
      using \<open>n > 0\<close> \<open>a > 0\<close> by (auto simp: a_seg_def zero_le_mult_iff divide_simps)
    have a_seg_le_iff [simp]: "a_seg x \<le> a_seg y \<longleftrightarrow> x \<le> y" 
      and a_seg_less_iff [simp]: "a_seg x < a_seg y \<longleftrightarrow> x < y" for x y
      using \<open>n > 0\<close> \<open>a > 0\<close> by (auto simp: a_seg_def zero_le_mult_iff divide_simps)
    have "strict_mono a_seg"
      by (simp add: strict_mono_def)
    have a_seg_eq_a_iff: "a_seg x = a \<longleftrightarrow> x=n" for x
      using \<open>0 < n\<close> \<open>a > 0\<close> by (simp add: a_seg_def nonzero_divide_eq_eq)
    have fa_eq_b: "f (a_seg n) = b"
      using a_seg_eq_a_iff f by fastforce

    have "a/d < real_of_int \<lfloor>a * 2 / min a d\<rfloor>" if "d>0" for d
      by (smt (verit) \<open>0 < \<delta>\<close> \<open>\<delta> \<le> a\<close> add_divide_distrib divide_less_eq_1_pos floor_eq_iff that)
    then have an_less_del: "a/n < del (\<epsilon>/a)"
      using \<open>a > 0\<close> \<open>\<epsilon> > 0\<close> del_gt0  by (simp add: n_def \<delta>_def field_simps)

    define lower where "lower \<equiv> \<lambda>x. a_seg\<lfloor>(real n * x) / a\<rfloor>"
    define f1 where "f1 \<equiv> f \<circ> lower"
    have f1_lower: "f1 x \<le> f x" if "0 \<le> x" "x \<le> a" for x
    proof -
      have "lower x \<le> x"
        using \<open>n > 0\<close> floor_divide_lower [OF \<open>a > 0\<close>] 
        by (auto simp: lower_def a_seg_def field_simps)
      moreover have "lower x \<ge> 0"
        unfolding lower_def using \<open>n > 0\<close> \<open>a \<ge> 0\<close> \<open>0 \<le> x\<close> by force
      ultimately show ?thesis
        using sm strict_mono_on_leD by (fastforce simp add: f1_def)
    qed
    define upper where "upper \<equiv> \<lambda>x. a_seg\<lceil>real n * x / a\<rceil>"
    define f2 where "f2 \<equiv> f \<circ> upper"
    have f2_upper: "f2 x \<ge> f x" if "0 \<le> x" "x \<le> a" for x
    proof -
      have "x \<le> upper x"
        using \<open>n > 0\<close> ceiling_divide_upper [OF \<open>a > 0\<close>] by (simp add: upper_def a_seg_def field_simps)
      then show ?thesis
        using sm strict_mono_on_leD \<open>0 \<le> x\<close> by (force simp: f2_def)
    qed
    let ?\<D> = "regular_division 0 a n"
    have div: "?\<D> division_of {0..a}"
      using \<open>a > 0\<close> \<open>n > 0\<close> regular_division_division_of zero_less_nat_eq by presburger

    have int_f1_D: "(f1 has_integral f(Inf K) * (a/n)) K" 
      and int_f2_D: "(f2 has_integral f(Sup K) * (a/n)) K" and less: "\<bar>f(Sup K) - f(Inf K)\<bar> < \<epsilon>/a"
      if "K\<in>?\<D>" for K
    proof -
      from regular_divisionE [OF that] \<open>a > 0\<close>
      obtain k where "k<n" and k: "K = {a_seg(real k)..a_seg(Suc k)}"
        by (auto simp: a_seg_def mult.commute)
      define u where "u \<equiv> a_seg k"
      define v where "v \<equiv> a_seg (Suc k)"
      have "u < v" "0 \<le> u" "0 \<le> v" "u \<le> a" "v \<le> a" and Kuv: "K = {u..v}"
        using \<open>n > 0\<close> \<open>k < n\<close> \<open>a > 0\<close> by (auto simp: k u_def v_def divide_simps)
      have InfK: "Inf K = u" and SupK: "Sup K = v"
        using Kuv \<open>u < v\<close> apply force
        using \<open>n > 0\<close> \<open>a > 0\<close> by (auto simp: divide_right_mono k u_def v_def)
      have f1: "f1 x = f (Inf K)" if "x \<in> K - {v}" for x
      proof -
        have "x \<in> {u..<v}"
          using that Kuv atLeastLessThan_eq_atLeastAtMost_diff by blast
        then have "\<lfloor>real_of_int n * x / a\<rfloor> = int k"
          using \<open>n > 0\<close> \<open>a > 0\<close> by (simp add: field_simps u_def v_def a_seg_def floor_eq_iff)
        then show ?thesis
          by (simp add: InfK f1_def lower_def a_seg_def mult.commute u_def) 
      qed
      have "((\<lambda>x. f (Inf K)) has_integral (f (Inf K) * (a/n))) K"
        using has_integral_const_real [of "f (Inf K)" u v] 
              \<open>n > 0\<close> \<open>a > 0\<close> by (simp add: Kuv field_simps a_seg_def u_def v_def)
      then show "(f1 has_integral (f (Inf K) * (a/n))) K"
        using has_integral_spike_finite_eq [of "{v}" K "\<lambda>x. f (Inf K)" f1] f1 by simp
      have f2: "f2 x = f (Sup K)" if "x \<in> K - {u}" for x
      proof -
        have "x \<in> {u<..v}"
          using that Kuv greaterThanAtMost_eq_atLeastAtMost_diff by blast 
        then have "\<lceil>x * real_of_int n / a\<rceil>  = 1 + int k"
          using \<open>n > 0\<close> \<open>a > 0\<close> by (simp add: field_simps u_def v_def a_seg_def ceiling_eq_iff)
        then show ?thesis 
          by (simp add: mult.commute f2_def upper_def a_seg_def SupK v_def)
      qed
      have "((\<lambda>x. f (Sup K)) has_integral (f (Sup K) * (a/n))) K"
        using  \<open>n > 0\<close> \<open>a > 0\<close> has_integral_const_real [of "f (Sup K)" u v]
        by (simp add: Kuv field_simps u_def v_def a_seg_def)
      then show "(f2 has_integral (f (Sup K) * (a/n))) K"
        using has_integral_spike_finite_eq [of "{u}" K "\<lambda>x. f (Sup K)" f2] f2 by simp
      have "\<bar>v - u\<bar> < del (\<epsilon>/a)"
        using \<open>n > 0\<close> \<open>a > 0\<close> by (simp add: v_def u_def a_seg_def field_simps an_less_del)
      then have "\<bar>f v - f u\<bar> < \<epsilon>/a"
        using \<open>\<epsilon> > 0\<close> \<open>a > 0\<close> \<open>0 \<le> u\<close> \<open>u \<le> a\<close> \<open>0 \<le> v\<close> \<open>v \<le> a\<close>
        by (intro del) auto
      then show "\<bar>f(Sup K) - f(Inf K)\<bar> < \<epsilon>/a"
        using InfK SupK by blast
    qed

    have int_21_D: "((\<lambda>x. f2 x - f1 x) has_integral (f(Sup K) - f(Inf K)) * (a/n)) K" if "K\<in>?\<D>" for K
      using that has_integral_diff [OF int_f2_D int_f1_D] by (simp add: algebra_simps)

    have D_ne: "?\<D> \<noteq> {}"
      by (metis \<open>0 < a\<close> \<open>n > 0\<close> card_gt_0_iff card_regular_division)
    have f12: "((\<lambda>x. f2 x - f1 x) has_integral (\<Sum>K\<in>?\<D>. (f(Sup K) - f(Inf K)) * (a/n))) {0..a}"
      by (intro div int_21_D has_integral_combine_division)
    moreover have "(\<Sum>K\<in>?\<D>. (f(Sup K) - f(Inf K)) * (a/n)) < \<epsilon>"
    proof -
      have "(\<Sum>K\<in>?\<D>. (f(Sup K) - f(Inf K)) * (a/n)) \<le> (\<Sum>K\<in>?\<D>. \<bar>f(Sup K) - f(Inf K)\<bar> * (a/n))"
        using \<open>n > 0\<close> \<open>a > 0\<close>
        by (smt (verit) divide_pos_pos of_nat_0_less_iff sum_mono zero_le_mult_iff)
      also have "\<dots> < (\<Sum>K\<in>?\<D>. \<epsilon>/n)"
        using \<open>n > 0\<close> \<open>a > 0\<close> less
        by (intro sum_strict_mono finite_regular_division D_ne) (simp add: field_simps)
      also have "\<dots> = \<epsilon>"
        using \<open>n > 0\<close> \<open>a > 0\<close> by simp
      finally show ?thesis .
    qed
    ultimately have f2_near_f1: "integral {0..a} (\<lambda>x. f2 x - f1 x) < \<epsilon>"
      by (simp add: integral_unique)

    define yidx where "yidx \<equiv> \<lambda>y. LEAST k. y < f (a_seg (Suc k))"
    have fa_yidx_le: "f (a_seg (yidx y)) \<le> y" and yidx_gt: "y < f (a_seg (Suc (yidx y)))" 
      if "y \<in> {0..b}" for y
    proof -
      obtain x where x: "f x = y" "x \<in> {0..a}"
        using Topological_Spaces.IVT' [OF _ _ _ cont_0a] assms
        by (metis \<open>y \<in> {0..b}\<close> atLeastAtMost_iff)
      define k where "k \<equiv> nat \<lfloor>x/a * n\<rfloor>"
      have x_lims: "a_seg k \<le> x" "x < a_seg (Suc k)"
        using \<open>n > 0\<close> \<open>0 < a\<close> floor_divide_lower floor_divide_upper [of a "x*n"] x
        by (auto simp: k_def a_seg_def field_simps)
      with that x obtain f_lims: "f (a_seg k) \<le> y" "y < f (a_seg (Suc k))"
        using strict_mono_onD [OF sm] by force
      then have "a_seg (yidx y) \<le> a_seg k"
        by (simp add: Least_le \<open>strict_mono a_seg\<close> strict_mono_less_eq yidx_def)
      then have "f (a_seg (yidx y)) \<le> f (a_seg k)"
        using strict_mono_onD [OF sm] by simp
      then show "f (a_seg (yidx y)) \<le> y"
        using f_lims by linarith
      show "y < f (a_seg (Suc (yidx y)))"
        by (metis LeastI f_lims(2) yidx_def) 
    qed

    have yidx_equality: "yidx y = k" if "y \<in> {0..b}" "y \<in> {f (a_seg k)..<f (a_seg (Suc k))}" for y k
    proof (rule antisym)
      show "yidx y \<le> k"
        unfolding yidx_def by (metis atLeastLessThan_iff that(2) Least_le)
      have "(a_seg (real k)) < a_seg (1 + real (yidx y))"
        using yidx_gt [OF that(1)] that(2) strict_mono_onD [OF sm] order_le_less_trans by fastforce
      then have "real k < 1 + real (yidx y)"
        by (simp add: \<open>strict_mono a_seg\<close> strict_mono_less)
      then show "k \<le> yidx y"
        by simp 
    qed
    have "yidx b = n"
    proof -
      have "a < (1 + real n) * a / real n"
        using \<open>0 < n\<close> \<open>0 < a\<close> by (simp add: divide_simps)
      then have "b < f (a_seg (1 + real n))"
        using f \<open>a \<ge> 0\<close> a_seg_def sm strict_mono_onD by fastforce
      then show ?thesis
        using \<open>0 \<le> b\<close> by (auto simp: f a_seg_def yidx_equality)
    qed
    moreover have yidx_less_n: "yidx y < n" if "y < b" for y
      by (metis \<open>0 < n\<close> fa_eq_b gr0_conv_Suc less_Suc_eq_le that Least_le yidx_def)
    ultimately have yidx_le_n: "yidx y \<le> n" if "y \<le> b" for y
      by (metis dual_order.order_iff_strict that)

    have zero_to_b_eq: "{0..b} = (\<Union>k<n. {f(a_seg k)..f(a_seg (Suc k))})" (is "?lhs = ?rhs")
    proof
      show "?lhs \<subseteq> ?rhs"
      proof
        fix y assume y: "y \<in> {0..b}"
        have fn: "f (a_seg n) = b"
          using a_seg_eq_a_iff \<open>f a = b\<close> by fastforce
        show "y \<in> ?rhs"
        proof (cases "y=b")
          case True
          with fn \<open>n>0\<close> show ?thesis
            by (rule_tac a="n-1" in UN_I) auto
        next
          case False
          with y show ?thesis 
            apply (simp add: subset_iff Bex_def)
            by (metis atLeastAtMost_iff of_nat_Suc order_le_less yidx_gt fa_yidx_le yidx_less_n)
        qed
      qed
      show "?rhs \<subseteq> ?lhs"
        apply clarsimp
        by (smt (verit, best) a_seg_ge_0 a_seg_le_a f f_iff(2) nat_less_real_le of_nat_0_le_iff)
    qed

    define g1 where "g1 \<equiv> \<lambda>y. if y=b then a else a_seg (Suc (yidx y))"
    define g2 where "g2 \<equiv> \<lambda>y. if y=0 then 0 else a_seg (yidx y)"
    have g1: "g1 y \<in> {0..a}" if "y \<in> {0..b}" for y
      using that \<open>a > 0\<close> yidx_less_n [of y] by (auto simp: g1_def a_seg_def divide_simps)
    have g2: "g2 y \<in> {0..a}" if "y \<in> {0..b}" for y
      using that \<open>a > 0\<close> yidx_le_n [of y] by (simp add: g2_def a_seg_def divide_simps)

    have g2_le_g: "g2 y \<le> g y" if "y \<in> {0..b}" for y
    proof -
      have "f (g2 y) \<le> y"
        using \<open>f 0 = 0\<close> g2_def that fa_yidx_le by presburger
      then have "f (g2 y) \<le> f (g y)"
        using that g by (smt (verit, best) atLeastAtMost_iff fim image_iff)
      then show ?thesis
        by (smt (verit, best) atLeastAtMost_iff fim g g2 imageE sm_0a strict_mono_onD that)
    qed
    have g_le_g1: "g y \<le> g1 y" if "y \<in> {0..b}" for y
    proof -
      have "y \<le> f (g1 y)"
        by (smt (verit, best) \<open>f a = b\<close> g1_def that yidx_gt)
      then have "f (g y) \<le> f (g1 y)"
        using that g by (smt (verit, best) atLeastAtMost_iff fim image_iff)
      then show ?thesis
        by (smt (verit, ccfv_threshold) atLeastAtMost_iff f_iff(1) g1 that)
    qed

    define DN where "DN \<equiv> \<lambda>K. nat \<lfloor>Inf K * real n / a\<rfloor>"
    have [simp]: "DN {a * real k / n..a * (1 + real k) / n} = k" for k
      using \<open>n > 0\<close> \<open>a > 0\<close> by (simp add: DN_def divide_simps)
    have DN: "bij_betw DN ?\<D> {..<n}"
    proof (intro bij_betw_imageI)
      show "inj_on DN (regular_division 0 a n)"
      proof
        fix K K'
        assume "K \<in> regular_division 0 a n"
        with \<open>a > 0\<close> obtain k where k: "K = {a * (real k / n) .. a * (1 + real k) / n}"
          by (force elim: regular_divisionE)
        assume "K' \<in> regular_division 0 a n"
        with \<open>a > 0\<close> obtain k' where k': "K' = {a * (real k' / n) .. a * (1 + real k') / n}"
          by (force elim: regular_divisionE)
        assume "DN K = DN K'"
        then show "K = K'" by (simp add: k k')
      qed
      have "\<exists>K\<in>regular_division 0 a n. k = nat \<lfloor>Inf K * real n / a\<rfloor>" if "k < n" for k
        using \<open>n > 0\<close> \<open>a > 0\<close> that
        by (force simp: divide_simps intro: regular_division_eqI [OF refl])
      with \<open>a>0\<close> show "DN ` regular_division 0 a n = {..<n}"
        by (auto simp: DN_def bij_betw_def image_iff frac_le elim!: regular_divisionE)
    qed
 
    have int_f1: "(f1 has_integral (\<Sum>k<n. f(a_seg k)) * (a/n)) {0..a}"
    proof -
      have "a_seg (real (DN K)) = Inf K" if "K \<in> ?\<D>" for K
        using that \<open>a>0\<close> by (auto simp: DN_def field_simps a_seg_def elim: regular_divisionE)
      then have "(\<Sum>K\<in>?\<D>. f(Inf K) * (a/n)) = (\<Sum>k<n. (f(a_seg k)) * (a/n))"
        by (simp flip: sum.reindex_bij_betw [OF DN])
      moreover have "(f1 has_integral (\<Sum>K\<in>?\<D>. f(Inf K) * (a/n))) {0..a}"
        by (intro div int_f1_D has_integral_combine_division)
      ultimately show ?thesis
        by (metis sum_distrib_right)
    qed
    text \<open>The claim @{term "(f2 has_integral (\<Sum>k<n. f(a_seg(Suc k))) * (a/n)) {0..a}"} can similarly be proved\<close>

    have int_g1_D: "(g1 has_integral a_seg (Suc k) * (f (a_seg (Suc k)) - f (a_seg k))) 
                    {f(a_seg k)..f(a_seg (Suc k))}" 
     and int_g2_D: "(g2 has_integral a_seg k * (f (a_seg (Suc k)) - f (a_seg k))) 
                    {f(a_seg k)..f(a_seg (Suc k))}" 
      if "k < n" for k
    proof -
      define u where "u \<equiv> f (a_seg k)"
      define v where "v \<equiv> f (a_seg (Suc k))"
      obtain "u < v" "0 \<le> u" "0 \<le> v"
        unfolding u_def v_def assms
        by (smt (verit, best) a_seg_ge_0 a_seg_le_iff f(1) f_iff(1) of_nat_0_le_iff of_nat_Suc)
      have "u \<le> b" "v \<le> b"
        using \<open>k < n\<close> \<open>a \<ge> 0\<close> by (simp_all add: u_def v_def flip: \<open>f a = b\<close>)
      have yidx_eq: "yidx x = k" if "x \<in> {u..<v}" for x
        using \<open>0 \<le> u\<close> \<open>v \<le> b\<close> that u_def v_def yidx_equality by auto

      have "g1 x = a_seg (Suc k)" if "x \<in> {u..<v}" for x
        using that \<open>v \<le> b\<close> by (simp add: g1_def yidx_eq)
      moreover have "((\<lambda>x. a_seg (Suc k)) has_integral (a_seg (Suc k) * (v-u))) {u..v}"
        using has_integral_const_real \<open>u < v\<close>
        by (metis content_real_if less_eq_real_def mult.commute real_scaleR_def)
      ultimately show "(g1 has_integral (a_seg (Suc k) * (v-u))) {u..v}"
        using has_integral_spike_finite_eq [of "{v}" "{u..v}" "\<lambda>x. a_seg (Suc k)" g1] by simp

      have g2: "g2 x = a_seg k" if "x \<in> {u<..<v}" for x
        using that \<open>0 \<le> u\<close> by (simp add: g2_def yidx_eq)
      moreover have "((\<lambda>x. a_seg k) has_integral (a_seg k * (v-u))) {u..v}"
        using has_integral_const_real \<open>u < v\<close>
        by (metis content_real_if less_eq_real_def mult.commute real_scaleR_def)
      ultimately show "(g2 has_integral (a_seg k * (v-u))) {u..v}"
        using has_integral_spike_finite_eq [of "{u,v}" "{u..v}" "\<lambda>x. a_seg k" g2] by simp
    qed

    have int_g1: "(g1 has_integral (\<Sum>k<n. a_seg (Suc k) * (f (a_seg (Suc k)) - f (a_seg k)))) {0..b}"
    and int_g2: "(g2 has_integral (\<Sum>k<n. a_seg k * (f (a_seg (Suc k)) - f (a_seg k)))) {0..b}"
      unfolding zero_to_b_eq using int_g1_D int_g2_D
      by (auto simp: min_def pairwise_def intro!: has_integral_UN negligible_atLeastAtMostI)

    have "(\<Sum>k<n. a_seg (Suc k) * (f (a_seg (Suc k)) - f (a_seg k)))
        = (\<Sum>k<n. (Suc k) * (f (a_seg (Suc k)) - f (a_seg k))) * (a/n)"
      unfolding a_seg_def sum_distrib_right sum_divide_distrib by (simp add: mult_ac)
    also have "\<dots> = (n * f (a_seg n) - (\<Sum>k<n. f (a_seg k))) * a / n"
      using weighted_nesting_sum [where g = "f o a_seg"] by simp
    also have "\<dots> = a * b - (\<Sum>k<n. f (a_seg k)) * a / n"
      using \<open>n > 0\<close> by (simp add: fa_eq_b field_simps)
    finally have int_g1': "(g1 has_integral a * b - (\<Sum>k<n. f (a_seg k)) * a / n) {0..b}"
      using int_g1 by simp
    text \<open>The claim @{term "(g2 has_integral a * b - (\<Sum>k<n. f (a_seg (Suc k))) * a / n) {0..b}"} can similarly be proved.\<close> 

    have a_seg_diff: "a_seg (Suc k) - a_seg k = a/n" for k
      by (simp add: a_seg_def field_split_simps)
    have f_a_seg_diff: "\<bar>f (a_seg (Suc k)) - f (a_seg k)\<bar> < \<epsilon>/a" if "k<n" for k
      using that \<open>a > 0\<close> a_seg_diff an_less_del \<open>\<epsilon> > 0\<close>
      by (intro del) auto

    have "((\<lambda>x. g1 x - g2 x) has_integral (\<Sum>k<n. (f (a_seg (Suc k)) - f (a_seg k)) * (a/n))) {0..b}"
      using has_integral_diff [OF int_g1 int_g2] a_seg_diff
      apply (simp flip: sum_subtractf left_diff_distrib)
      apply (simp add: field_simps)
      done
    moreover have "(\<Sum>k<n. (f (a_seg (Suc k)) - f (a_seg k)) * (a/n)) < \<epsilon>"
    proof -
      have "(\<Sum>k<n. (f (a_seg (Suc k)) - f (a_seg k)) * (a/n)) 
         \<le> (\<Sum>k<n. \<bar>f (a_seg (Suc k)) - f (a_seg k)\<bar> * (a/n))"
        by simp
      also have "\<dots> < (\<Sum>k<n. (\<epsilon>/a) * (a/n))"
      proof (rule sum_strict_mono)
        fix k assume "k \<in> {..<n}"
        with \<open>n > 0\<close> \<open>a > 0\<close> divide_strict_right_mono f_a_seg_diff pos_less_divide_eq
        show "\<bar>f (a_seg (Suc k)) - f (a_seg k)\<bar> * (a/n) < \<epsilon>/a * (a/n)" by fastforce
      qed (use \<open>n > 0\<close> in auto)
      also have "\<dots> = \<epsilon>"
        using \<open>n > 0\<close> \<open>a > 0\<close> by simp
      finally show ?thesis .
    qed
    ultimately have g2_near_g1: "integral {0..b} (\<lambda>x. g1 x - g2 x) < \<epsilon>"
      by (simp add: integral_unique)

    have ab1: "integral {0..a} f1 + integral {0..b} g1 = a*b"
      using int_f1 int_g1' by (simp add: integral_unique)

    have "integral {0..a} (\<lambda>x. f x - f1 x) \<le> integral {0..a} (\<lambda>x. f2 x - f1 x)"
    proof (rule integral_le)
      show "(\<lambda>x. f x - f1 x) integrable_on {0..a}" "(\<lambda>x. f2 x - f1 x) integrable_on {0..a}"
        using Henstock_Kurzweil_Integration.integrable_diff int_f1 intgb_f f12 by blast+
    qed (auto simp: f2_upper)
    with f2_near_f1 have "integral {0..a} (\<lambda>x. f x - f1 x) < \<epsilon>"
      by simp
    moreover have "integral {0..a} f1 \<le> integral {0..a} f"
      by (intro integral_le has_integral_integral intgb_f has_integral_integrable [OF int_f1]) 
         (simp add: f1_lower)
    ultimately have f_error: "\<bar>integral {0..a} f - integral {0..a} f1\<bar> < \<epsilon>"
      using Henstock_Kurzweil_Integration.integral_diff int_f1 intgb_f by fastforce

    have "integral {0..b} (\<lambda>x. g1 x - g x) \<le> integral {0..b} (\<lambda>x. g1 x - g2 x)"
    proof (rule integral_le)
      show "(\<lambda>x. g1 x - g x) integrable_on {0..b}" "(\<lambda>x. g1 x - g2 x) integrable_on {0..b}"
        using Henstock_Kurzweil_Integration.integrable_diff int_g1 int_g2 intgb_g by blast+
    qed (auto simp: g2_le_g)
    with g2_near_g1 have "integral {0..b} (\<lambda>x. g1 x - g x) < \<epsilon>"
      by simp
    moreover have "integral {0..b} g \<le> integral {0..b} g1"
      by (intro integral_le has_integral_integral intgb_g has_integral_integrable [OF int_g1]) 
         (simp add: g_le_g1)
    ultimately have g_error: "\<bar>integral {0..b} g1 - integral {0..b} g\<bar> < \<epsilon>"
      using integral_diff int_g1 intgb_g by fastforce
    show ?thesis
      using f_error g_error ab1 by linarith
  qed
  show ?thesis
    using * [of "\<bar>a * b - integral {0..a} f - integral {0..b} g\<bar> / 2"] by fastforce
qed (use assms in force)



corollary Youngs_strict:
  fixes f :: "real \<Rightarrow> real"
  assumes sm: "strict_mono_on {0..} f" and cont: "continuous_on {0..} f" and "a>0" "b\<ge>0"
    and f: "f 0 = 0" "f a \<noteq> b" and fim: "f ` {0..} = {0..}"
    and g: "\<And>x. 0 \<le> x \<Longrightarrow> g (f x) = x"
  shows "a*b < integral {0..a} f + integral {0..b} g"
proof -
  have f_iff [simp]: "f x < f y \<longleftrightarrow> x < y" "f x \<le> f y \<longleftrightarrow> x \<le> y"
    if "x \<ge> 0" "y \<ge> 0" for x y
    using that by (smt (verit, best) atLeast_iff sm strict_mono_onD)+
  let ?b' = "f a"
  have "?b' \<ge> 0"
    by (smt (verit, best) \<open>0 < a\<close> atLeast_iff f sm strict_mono_onD)
  then have sm_gx: "strict_mono_on {0..} g"
    unfolding strict_mono_on_def
    by (smt (verit, best) atLeast_iff f_iff(1) f_inv_into_f fim g inv_into_into)
  show ?thesis
  proof (cases "?b' < b")
    case True
    have gt_a: "a < g y" if "y \<in> {?b'<..b}" for y
    proof -
      have "a = g ?b'"
        using \<open>a > 0\<close> g by force
      also have "\<dots> < g y"
        using \<open>0 \<le> ?b'\<close> sm_gx strict_mono_onD that by fastforce
      finally show ?thesis .
    qed
    have "continuous_on {0..} g"
      by (metis cont f(1) fim g sm strict_mono_continuous_invD)
    then have contg: "continuous_on {?b'..b} g"
      by (meson Icc_subset_Ici_iff \<open>0 \<le> f a\<close> continuous_on_subset)
    have "mono_on {0..} g"
      by (simp add: sm_gx strict_mono_on_imp_mono_on)
    then have int_g0b: "g integrable_on {0..b}"
      by (simp add: integrable_on_mono_on mono_on_subset)
    then have int_gb'b: "g integrable_on {?b'..b}"
      by (simp add: \<open>0 \<le> ?b'\<close> integrable_on_subinterval)
    have "a * (b - ?b') = integral {?b'..b} (\<lambda>y. a)"
      using True by force
    also have "\<dots> < integral {?b'..b} g"
      using contg True gt_a by (intro integral_less_real) auto
    finally have *: "a * (b - ?b') < integral {?b'..b} g" .
    have "a*b = a * ?b' + a * (b - ?b')"
      by (simp add: algebra_simps)
    also have "\<dots> = integral {0..a} f + integral {0..?b'} g + a * (b - ?b')"
      using Youngs_exact \<open>a > 0\<close> cont \<open>f 0 = 0\<close> g sm by force
    also have "\<dots> < integral {0..a} f + integral {0..?b'} g + integral {?b'..b} g"
      by (simp add: *)
    also have "\<dots> = integral {0..a} f + integral {0..b} g"
      by (smt (verit) Henstock_Kurzweil_Integration.integral_combine True \<open>0 \<le> ?b'\<close> int_g0b)
    finally show ?thesis .
  next
    case False
    with f have "b < ?b'" by force
    obtain a' where "f a' = b" "a' \<ge> 0"
      using fim \<open>b \<ge> 0\<close> by force 
    then have "a' < a"
      using \<open>b < f a\<close> \<open>a > 0\<close> by force
    have gt_b: "b < f x" if "x \<in> {a'<..a}" for x
      using \<open>0 \<le> a'\<close> \<open>f a' = b\<close> that by fastforce
    have int_f0a: "f integrable_on {0..a}"
      by (simp add: integrable_on_mono_on mono_on_def)
    then have int_fa'a: "f integrable_on {a'..a}"
      by (simp add: \<open>0 \<le> a'\<close> integrable_on_subinterval)
    have cont_f': "continuous_on {a'..a} f"
      by (meson Icc_subset_Ici_iff \<open>0 \<le> a'\<close> cont continuous_on_subset)
    have "b * (a - a') = integral {a'..a} (\<lambda>x. b)"
      using \<open>a' < a\<close> by simp
    also have "\<dots> < integral {a'..a} f"
      using cont_f' \<open>a' < a\<close> gt_b by (intro integral_less_real) auto
    finally have *: "b * (a - a') < integral {a'..a} f" .
    have "a*b = a' * b + b * (a - a')"
      by (simp add: algebra_simps)
    also have "\<dots> = integral {0..a'} f + integral {0..b} g + b * (a - a')"
      by (simp add: Youngs_exact \<open>0 \<le> a'\<close> \<open>f a' = b\<close> cont f g sm)
    also have "\<dots> < integral {0..a'} f + integral {0..b} g + integral {a'..a} f"
      by (simp add: *)
    also have "\<dots> = integral {0..a} f + integral {0..b} g"
      by (smt (verit) Henstock_Kurzweil_Integration.integral_combine \<open>0 \<le> a'\<close> \<open>a' < a\<close> int_f0a)
    finally show ?thesis .
  qed
qed

corollary Youngs_inequality:
  fixes f :: "real \<Rightarrow> real"
  assumes sm: "strict_mono_on {0..} f" and cont: "continuous_on {0..} f" and "a\<ge>0" "b\<ge>0"
    and f: "f 0 = 0" and fim: "f ` {0..} = {0..}"
    and g: "\<And>x. 0 \<le> x \<Longrightarrow> g (f x) = x"
  shows "a*b \<le> integral {0..a} f + integral {0..b} g"
proof (cases "a=0")
  case True
  have "g x \<ge> 0" if "x \<ge> 0" for x
    by (metis atLeast_iff fim g imageE that)
  then have "0 \<le> integral {0..b} g"
    by (metis Henstock_Kurzweil_Integration.integral_nonneg atLeastAtMost_iff 
              not_integrable_integral order_refl)
  then show ?thesis 
    by (simp add: True)
next
  case False
  then show ?thesis
    by (smt (verit) assms Youngs_exact Youngs_strict)
qed

end
