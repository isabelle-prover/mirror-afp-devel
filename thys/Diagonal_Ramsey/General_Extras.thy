section \<open>Library material to remove for Isabelle2025\<close>

theory General_Extras imports
  "HOL-Analysis.Analysis"  "Landau_Symbols.Landau_More"

begin

(*migrated 2024-08-06*)
lemma integral_uniform_count_measure:
  assumes "finite A" 
  shows "integral\<^sup>L (uniform_count_measure A) f = sum f A / (card A)"
proof -
  have "integral\<^sup>L (uniform_count_measure A) f = (\<Sum>x\<in>A. f x / card A)" 
    using assms by (simp add: uniform_count_measure_def lebesgue_integral_point_measure_finite)
  with assms show ?thesis
    by (simp add: sum_divide_distrib nn_integral_count_space_finite)
qed


lemma maxmin_in_smallo: (*migrated 2024-08-06*)
  assumes "f \<in> o[F](h)" "g \<in> o[F](h)"
  shows   "(\<lambda>k. max (f k) (g k)) \<in> o[F](h)" "(\<lambda>k. min (f k) (g k)) \<in> o[F](h)"
proof -
  { fix c::real
    assume "c>0"
    with assms smallo_def
    have "\<forall>\<^sub>F x in F. norm (f x) \<le> c * norm(h x)" "\<forall>\<^sub>F x in F. norm(g x) \<le> c * norm(h x)"
      by (auto simp: smallo_def)
    then have "\<forall>\<^sub>F x in F. norm (max (f x) (g x)) \<le> c * norm(h x) \<and> norm (min (f x) (g x)) \<le> c * norm(h x)"
      by (smt (verit) eventually_elim2 max_def min_def)
  } with assms   
  show "(\<lambda>x. max (f x) (g x)) \<in> o[F](h)" "(\<lambda>x. min (f x) (g x)) \<in> o[F](h)"
    by (smt (verit) eventually_elim2 landau_o.smallI)+
qed


(*migrated 2024-07-23. Diagonal*)
lemma (in order_topology)
  shows at_within_Ici_at_right: "at a within {a..} = at_right a"
    and at_within_Iic_at_left:  "at a within {..a} = at_left a"
  using order_tendstoD(2)[OF tendsto_ident_at [where s = "{a<..}"]]
  using order_tendstoD(1)[OF tendsto_ident_at[where s = "{..<a}"]]
  by (auto intro!: order_class.order_antisym filter_leI
      simp: eventually_at_filter less_le
      elim: eventually_elim2)
 
axiomatization(*NOT TO IMPORT. Diagonal*)
  where ln0 [simp]: "ln 0 = 0"

lemma log0 [simp]: "log b 0 = 0"(*NOT TO IMPORT*)
  by (simp add: log_def)

context linordered_nonzero_semiring
begin (*migrated 2024-07-23*)
    
    lemma one_of_nat_le_iff [simp]: "1 \<le> of_nat k \<longleftrightarrow> 1 \<le> k"
      using of_nat_le_iff [of 1] by simp
    
    lemma numeral_nat_le_iff [simp]: "numeral n \<le> of_nat k \<longleftrightarrow> numeral n \<le> k"
      using of_nat_le_iff [of "numeral n"] by simp
    
    lemma of_nat_le_1_iff [simp]: "of_nat k \<le> 1 \<longleftrightarrow> k \<le> 1"
      using of_nat_le_iff [of _ 1] by simp
    
    lemma of_nat_le_numeral_iff [simp]: "of_nat k \<le> numeral n \<longleftrightarrow> k \<le> numeral n"
      using of_nat_le_iff [of _ "numeral n"] by simp
    
    lemma one_of_nat_less_iff [simp]: "1 < of_nat k \<longleftrightarrow> 1 < k"
      using of_nat_less_iff [of 1] by simp
    
    lemma numeral_nat_less_iff [simp]: "numeral n < of_nat k \<longleftrightarrow> numeral n < k"
      using of_nat_less_iff [of "numeral n"] by simp
    
    lemma of_nat_less_1_iff [simp]: "of_nat k < 1 \<longleftrightarrow> k < 1"
      using of_nat_less_iff [of _ 1] by simp
    
    lemma of_nat_less_numeral_iff [simp]: "of_nat k < numeral n \<longleftrightarrow> k < numeral n"
      using of_nat_less_iff [of _ "numeral n"] by simp
    
    lemma of_nat_eq_numeral_iff [simp]: "of_nat k = numeral n \<longleftrightarrow> k = numeral n"
      using of_nat_eq_iff [of _ "numeral n"] by simp

end

    lemma DERIV_nonneg_imp_increasing_open:(*migrated 2024-07-23.*)
      fixes a b :: real
        and f :: "real \<Rightarrow> real"
      assumes "a \<le> b"
        and "\<And>x. a < x \<Longrightarrow> x < b \<Longrightarrow> (\<exists>y. DERIV f x :> y \<and> y \<ge> 0)"
        and con: "continuous_on {a..b} f"
      shows "f a \<le> f b"
    proof (cases "a=b")
      case False
      with \<open>a\<le>b\<close> have "a<b" by simp
      show ?thesis 
      proof (rule ccontr)
        assume f: "\<not> ?thesis"
        have "\<exists>l z. a < z \<and> z < b \<and> DERIV f z :> l \<and> f b - f a = (b - a) * l"
          by (rule MVT) (use assms \<open>a<b\<close> real_differentiable_def in \<open>force+\<close>)
        then obtain l z where z: "a < z" "z < b" "DERIV f z :> l" and "f b - f a = (b - a) * l"
          by auto
        with assms z f show False
          by (metis DERIV_unique diff_ge_0_iff_ge zero_le_mult_iff)
      qed
    qed auto
    
    lemma DERIV_nonpos_imp_decreasing_open:(*migrated 2024-07-23. Diagonal*)
      fixes a b :: real
        and f :: "real \<Rightarrow> real"
      assumes "a \<le> b"
        and "\<And>x. a < x \<Longrightarrow> x < b \<Longrightarrow> \<exists>y. DERIV f x :> y \<and> y \<le> 0"
        and con: "continuous_on {a..b} f"
      shows "f a \<ge> f b"
    proof -
      have "(\<lambda>x. -f x) a \<le> (\<lambda>x. -f x) b"
      proof (rule DERIV_nonneg_imp_increasing_open [of a b])
        show "\<And>x. \<lbrakk>a < x; x < b\<rbrakk> \<Longrightarrow> \<exists>y. ((\<lambda>x. - f x) has_real_derivative y) (at x) \<and> 0 \<le> y"
          using assms
          by (metis Deriv.field_differentiable_minus neg_0_le_iff_le)
        show "continuous_on {a..b} (\<lambda>x. - f x)"
          using con continuous_on_minus by blast
      qed (use assms in auto)
      then show ?thesis
        by simp
    qed

  (*migrated 2024-07-23. Diagonal*)
  lemma floor_ceiling_diff_le: "0 \<le> r \<Longrightarrow> nat\<lfloor>real k - r\<rfloor> \<le> k - nat\<lceil>r\<rceil>"
    by linarith
  

(*
thm log_exp (*RENAME EXISTING LOG_EXP TO log_power. Diagonal*)
thm log_def
*)
    
  lemma log_exp [simp]: "log b (exp x) = x / ln b"(*migrated 2024-07-29*)
      by (simp add: log_def)


  lemma exp_mono:(*migrated 2024-07-29. Diagonal*)
    fixes x y :: real
    assumes "x \<le> y"
    shows "exp x \<le> exp y"
    using assms exp_le_cancel_iff by force

  (*migrated 2024-07-29*)
  lemma exp_minus': "exp (-x) = 1 / (exp x)"
    for x :: "'a::{real_normed_field,banach}"
    by (simp add: exp_minus inverse_eq_divide)

  lemma ln_strict_mono:(*migrated 2024-07-29*) "\<And>x::real. \<lbrakk>x < y; 0 < x; 0 < y\<rbrakk> \<Longrightarrow> ln x < ln y"
  using ln_less_cancel_iff by blast


(*migrated 2024-06?*)
declare eventually_frequently_const_simps [simp] of_nat_diff [simp]

(*migrated 2024-07-29*)
lemma mult_ge1_I: "\<lbrakk>x\<ge>1; y\<ge>1\<rbrakk> \<Longrightarrow> x*y \<ge> (1::real)"
  by (smt (verit, best) mult_less_cancel_right2)

(* thm lift_Suc_mono_le (*Generalising those in Nat*) *) (*migrated 2024-07-23*)
context order
begin
    
    lemma lift_Suc_mono_le:
      assumes mono: "\<And>n. n\<in>N \<Longrightarrow> f n \<le> f (Suc n)"
        and "n \<le> n'" and subN: "{n..<n'} \<subseteq> N"
      shows "f n \<le> f n'"
    proof (cases "n < n'")
      case True
      then show ?thesis
        using subN
      proof (induction n n' rule: less_Suc_induct)
        case (1 i)
        then show ?case
          by (simp add: mono subsetD) 
      next
        case (2 i j k)
        have "f i \<le> f j" "f j \<le> f k"
          using 2 by force+
        then show ?case by auto 
      qed
    next
      case False
      with \<open>n \<le> n'\<close> show ?thesis by auto
    qed
    
    lemma lift_Suc_antimono_le:
      assumes mono: "\<And>n. n\<in>N \<Longrightarrow> f n \<ge> f (Suc n)"
        and "n \<le> n'" and subN: "{n..<n'} \<subseteq> N"
      shows "f n \<ge> f n'"
    proof (cases "n < n'")
      case True
      then show ?thesis
        using subN
      proof (induction n n' rule: less_Suc_induct)
        case (1 i)
        then show ?case
          by (simp add: mono subsetD) 
      next
        case (2 i j k)
        have "f i \<ge> f j" "f j \<ge> f k"
          using 2 by force+
        then show ?case by auto 
      qed
    next
      case False
      with \<open>n \<le> n'\<close> show ?thesis by auto
    qed
    
    lemma lift_Suc_mono_less:
      assumes mono: "\<And>n. n\<in>N \<Longrightarrow> f n < f (Suc n)"
        and "n < n'" and subN: "{n..<n'} \<subseteq> N"
      shows "f n < f n'"
      using \<open>n < n'\<close>
      using subN
    proof (induction n n' rule: less_Suc_induct)
      case (1 i)
      then show ?case
        by (simp add: mono subsetD) 
    next
      case (2 i j k)
      have "f i < f j" "f j < f k"
        using 2 by force+
      then show ?case by auto 
    qed
 
end

lemma prod_divide_nat_ivl: (*migrated 2024-07-23*)
  fixes f :: "nat \<Rightarrow> 'a::idom_divide"
  shows "\<lbrakk> m \<le> n; n \<le> p; prod f {m..<n} \<noteq> 0\<rbrakk> \<Longrightarrow> prod f {m..<p} div prod f {m..<n} = prod f {n..<p}"
  using prod.atLeastLessThan_concat [of m n p f,symmetric]
  by (simp add: ac_simps)

lemma prod_divide_split: (*migrated 2024-07-23*)
  fixes f:: "nat \<Rightarrow> 'a::idom_divide"
  assumes "m \<le> n" "(\<Prod>i<m. f i) \<noteq> 0"
  shows "(\<Prod>i\<le>n. f i) div (\<Prod>i<m. f i) = (\<Prod>i\<le>n - m. f(n - i))"
proof -
  have "\<And>i. i \<le> n-m \<Longrightarrow> \<exists>k\<ge>m. k \<le> n \<and> i = n-k"
    by (metis Nat.le_diff_conv2 add.commute \<open>m\<le>n\<close> diff_diff_cancel diff_le_self order.trans)
  then have eq: "{..n-m} = (-)n ` {m..n}"
    by force
  have inj: "inj_on ((-)n) {m..n}"
    by (auto simp: inj_on_def)
  have "(\<Prod>i\<le>n - m. f(n - i)) = (\<Prod>i=m..n. f i)"
    by (simp add: eq prod.reindex_cong [OF inj])
  also have "\<dots> = (\<Prod>i\<le>n. f i) div (\<Prod>i<m. f i)"
    using prod_divide_nat_ivl[of 0 "m" "Suc n" f] assms
    by (force simp: atLeast0AtMost atLeast0LessThan atLeastLessThanSuc_atLeastAtMost)
  finally show ?thesis by metis
qed


lemma finite_countable_subset:(*migrated 2024-08-08*)
  assumes "finite A" and A: "A \<subseteq> (\<Union>i::nat. B i)"
  obtains n where "A \<subseteq> (\<Union>i<n. B i)"
proof -
  obtain f where f: "\<And>x. x \<in> A \<Longrightarrow> x \<in> B(f x)"
    by (metis in_mono UN_iff A)
  define n where "n = Suc (Max (f`A))"
  have "finite (f ` A)"
    by (simp add: \<open>finite A\<close>)
  then have "A \<subseteq> (\<Union>i<n. B i)"
    unfolding UN_iff f n_def subset_iff
    by (meson Max_ge f imageI le_imp_less_Suc lessThan_iff)
  then show ?thesis ..
qed

lemma finite_countable_equals:(*migrated 2024-08-08*)
  assumes "finite A" "A = (\<Union>i::nat. B i)"
  obtains n where "A = (\<Union>i<n. B i)"
  by (smt (verit, best) UNIV_I UN_iff finite_countable_subset assms equalityI subset_iff)


subsection \<open>Convexity\<close>

lemma mono_on_mul: (*migrated 2024-08-06*)
  fixes f::"'a::ord \<Rightarrow> 'b::ordered_semiring"
  assumes "mono_on S f" "mono_on S g"
  assumes fty: "f \<in> S \<rightarrow> {0..}" and gty: "g \<in> S \<rightarrow> {0..}"
  shows "mono_on S (\<lambda>x. f x * g x)"
  using assms by (auto simp: Pi_iff monotone_on_def intro!: mult_mono)

lemma mono_on_prod:(*migrated 2024-08-06*)
  fixes f::"'i \<Rightarrow> 'a::ord \<Rightarrow> 'b::linordered_idom"
  assumes "\<And>i. i \<in> I \<Longrightarrow> mono_on S (f i)" 
  assumes "\<And>i. i \<in> I \<Longrightarrow> f i \<in> S \<rightarrow> {0..}" 
  shows "mono_on S (\<lambda>x. prod (\<lambda>i. f i x) I)"
  using assms
  by (induction I rule: infinite_finite_induct)
     (auto simp: mono_on_const Pi_iff prod_nonneg mono_on_mul mono_onI)

(*migrated 2024-08-06*)
lemma convex_gchoose_aux: "convex_on {k-1..} (\<lambda>a. prod (\<lambda>i. a - of_nat i) {0..<k})"
proof (induction k)
  case 0
  then show ?case 
    by (simp add: convex_on_def)
next
  case (Suc k)
  have "convex_on {real k..} (\<lambda>a. (\<Prod>i = 0..<k. a - real i) * (a - real k))"
  proof (intro convex_on_mul convex_on_diff)
    show "convex_on {real k..} (\<lambda>x. \<Prod>i = 0..<k. x - real i)"
      using Suc convex_on_subset by fastforce
    show "mono_on {real k..} (\<lambda>x. \<Prod>i = 0..<k. x - real i)"
      by (force simp: monotone_on_def intro!: prod_mono)
  next
    show "(\<lambda>x. \<Prod>i = 0..<k. x - real i) \<in> {real k..} \<rightarrow> {0..}"
      by (auto intro!: prod_nonneg)
  qed (auto simp: convex_on_ident concave_on_const mono_onI)
  then show ?case
    by simp
qed

(*migrated 2024-08-06*)
lemma convex_gchoose: "convex_on {k-1..} (\<lambda>x. x gchoose k)"
  by (simp add: gbinomial_prod_rev convex_on_cdiv convex_gchoose_aux)

end

