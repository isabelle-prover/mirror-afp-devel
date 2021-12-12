theory Hahn_Jordan_Prelims imports  
  "HOL-Analysis.Analysis" 
  Extended_Reals_Sums_Compl
begin

section \<open>Preliminary results\<close>

lemma diff_union:
  shows "A - (\<Union> i \<le> n. B i) - B (Suc n) = A - (\<Union> i \<le> (Suc n). B i)"
  using atMost_Suc by auto

lemma disj_subsets:
  assumes "B 0 = A 0"
    and "\<And>(i::nat). B (Suc i) = A (Suc i) - (\<Union> j\<in>{..i}. A j)"
  shows "(\<Union>i. B i) = (\<Union>i. A i)"
proof 
  have "B i \<subseteq> A i" for i
  proof (cases "i = 0")
    case True
    thus ?thesis using assms by simp
  next
    case False
    hence "\<exists>j. i = Suc j" by (simp add: not0_implies_Suc) 
    from this obtain j where "i = Suc j" by auto
    thus "B i \<subseteq> A i" using assms by auto
  qed
  thus "\<Union> (range B) \<subseteq> \<Union> (range A)" by auto
next
  have ale: "\<And>n. A (Suc n) \<subseteq> B (Suc n) \<union> (\<Union> j\<in>{0..n}. A j)" using assms by auto    
  have inc: "\<And>n. (\<Union> i\<in> {0..n}. A i) \<subseteq> (\<Union> i \<in> {0..n}. B i)"
  proof -
    fix n
    show "(\<Union> i\<in> {0..n}. A i) \<subseteq> (\<Union> i \<in> {0..n}. B i)"
    proof (induct n)
      case 0
      then show ?case using assms by auto
    next
      case (Suc n)
      have "\<Union> (A ` {0..Suc n}) = (\<Union> (A ` {0.. n})) \<union> A (Suc n)"
        by (simp add: Un_commute atLeast0_atMost_Suc) 
      also have "... \<subseteq> (\<Union> (B ` {0.. n})) \<union> A (Suc n)" using Suc by auto
      also have "... \<subseteq> (\<Union> (B ` {0.. n})) \<union> B (Suc n) \<union> (\<Union> j\<in>{0..n}. A j)" using ale by auto
      also have "... \<subseteq> (\<Union> (B ` {0.. n})) \<union> B (Suc n) \<union> (\<Union> (B ` {0.. n}))" using Suc by auto
      also have "... = (\<Union> (B ` {0.. n})) \<union> B (Suc n)" by auto
      also have "... = (\<Union> (B ` {0.. Suc n}))" by (simp add: Un_commute atLeast0_atMost_Suc) 
      finally show ?case .
    qed
  qed
  have "\<And>n. (\<Union> i\<in> {0..<n}. A i) \<subseteq> (\<Union> i \<in> {0..<n}. B i)"
  proof -
    fix n
    show "(\<Union> i\<in> {0..<n}. A i) \<subseteq> (\<Union> i \<in> {0..<n}. B i)"
    proof (cases "n = 0")
      case True
      hence "{0..<n} = {}" by simp
      thus ?thesis by simp
    next
      case False
      hence "\<exists>m. n = Suc m" by (simp add: not0_implies_Suc)
      from this obtain m where "n = Suc m" by auto
      hence "{0..<n} = {0..m}" by auto
      have "(\<Union> i\<in> {0..m}. A i) \<subseteq> (\<Union> i \<in> {0..m}. B i)" using inc by simp
      thus ?thesis using \<open>{0..<n} = {0..m}\<close> by simp
    qed
  qed
  thus "\<Union> (range A) \<subseteq> \<Union> (range B)" using UN_finite2_subset[of A B 0] by simp
qed

lemma disj_Union2:
  assumes "\<And>i. A i \<in> sets M"
  obtains B where "disjoint_family B" and "(\<Union>(i::nat). B i) = (\<Union>(i::nat). A i)" 
    and "\<And>i. B i \<in> sets M" and "\<And>i. B i \<subseteq> A i"
proof
  define B where "B = (\<lambda>(i::nat). A i - (\<Union> j\<in>{..<i}. A j))"
  show "\<And>i. B i \<subseteq> A i" 
  proof -
    fix i 
    show "B i \<subseteq> A i"
    proof (cases "i = 0")
      case True
      thus ?thesis unfolding B_def by simp
    next
      case False
      hence "\<exists>j. i = Suc j" by (simp add: not0_implies_Suc) 
      from this obtain j where "i = Suc j" by auto
      thus "B i \<subseteq> A i" unfolding B_def by auto
    qed
  qed
  show "disjoint_family B" unfolding disjoint_family_on_def
  proof -
    {
      fix n m::nat
      assume "n <m"
      hence "B n \<subseteq> (\<Union> j\<in>{..<m}. A j)" using \<open>\<And>i. B i \<subseteq> A i\<close> by auto
      hence "B n \<inter> B m = {}" unfolding B_def by auto
    }
    thus "\<forall>m\<in>UNIV. \<forall>n\<in>UNIV. m \<noteq> n \<longrightarrow> B m \<inter> B n = {}" by (metis Int_commute antisym_conv3)
  qed
  show "(\<Union>(i::nat). B i) = (\<Union>(i::nat). A i)" 
  proof (rule disj_subsets)
    show "B 0 = A 0" unfolding B_def by simp
    show "\<And>i. B (Suc i) = A (Suc i) - \<Union> (A ` {..i})" unfolding B_def by auto
  qed
  show "\<And>i. B i \<in> sets M" unfolding B_def using assms by auto
qed

lemma conv_0_half:
  assumes "f \<longlonglongrightarrow> (0::real)"
    and "\<And>n. 0 \<le> f n"
  shows "\<exists>N. \<forall>n \<ge> N. f n < 1/2"
proof -
  have "\<forall>r>0. \<exists>no. \<forall>n\<ge>no. dist (f n) 0 < r" using assms by (simp add: lim_sequentially)
  hence "\<exists>no. \<forall>n\<ge> no. dist (f n) 0 < 1/2" using half_gt_zero_iff zero_less_one by blast 
  from this obtain N where "\<forall>n \<ge> N. dist (f n) 0 < 1/2" by auto
  have "\<And>n. dist (f n) 0 = f n" using assms
  proof -
    fix n
    have "dist (f n) 0 = \<bar>f n\<bar>" by simp
    also have "... = f n" using assms by simp
    finally show "dist (f n) 0 = f n" .
  qed
  hence "\<forall>n \<ge> N. f n < 1/2" using \<open>\<forall>n \<ge> N. dist (f n) 0 < 1/2\<close> by simp
  thus ?thesis by auto
qed

lemma e2ennreal_add:
  fixes x::ereal
  assumes "0 \<le> x"
    and "0 \<le> y"
  shows "e2ennreal (x+y) = e2ennreal x + e2ennreal y" 
proof (rule ereal_ennreal_cases[of x])
  show "x < 0 \<Longrightarrow> e2ennreal (x + y) = e2ennreal x + e2ennreal y" using assms by simp
  show "\<And>b. 0 \<le> x \<Longrightarrow> x = enn2ereal b \<Longrightarrow> e2ennreal (x + y) = e2ennreal x + e2ennreal y"
  proof -
    fix b
    assume "0 \<le> x" and "x = enn2ereal b"
    hence "e2ennreal x= b" by simp
    show "e2ennreal (x + y) = e2ennreal x + e2ennreal y"
    proof (rule ereal_ennreal_cases[of y])
      show "y < 0 \<Longrightarrow> e2ennreal (x + y) = e2ennreal x + e2ennreal y" using assms by simp
      show "\<And>b. 0 \<le> y \<Longrightarrow> y = enn2ereal b \<Longrightarrow> e2ennreal (x + y) = e2ennreal x + e2ennreal y"
      proof -
        fix c
        assume "0 \<le> y" and "y = enn2ereal c"
        hence "e2ennreal y = c" by simp
        show "e2ennreal (x + y) = e2ennreal x + e2ennreal y"
        proof (rule ereal_ennreal_cases[of "x+y"])
          show "x + y < 0 \<Longrightarrow> e2ennreal (x + y) = e2ennreal x + e2ennreal y" using assms
            by (simp add: leD) 
          show "\<And>b. 0 \<le> x + y \<Longrightarrow> x + y = enn2ereal b \<Longrightarrow> e2ennreal (x + y) = 
            e2ennreal x + e2ennreal y"
          proof -
            fix d
            assume "0 \<le> x+y" and "x+y = enn2ereal d"
            hence "e2ennreal (x+y) = d" by simp
            show "e2ennreal (x + y) = e2ennreal x + e2ennreal y"
              using \<open>e2ennreal (x+y) = d\<close> \<open>e2ennreal x= b\<close> \<open>e2ennreal y= c\<close>
              by (metis \<open>x = enn2ereal b\<close> \<open>y = enn2ereal c\<close> e2ennreal_enn2ereal plus_ennreal.rep_eq)
          qed
        qed
      qed
    qed
  qed
qed

lemma e2ennreal_finite_sum:
  shows "finite I \<Longrightarrow> (\<And>i. i\<in> I \<Longrightarrow> 0 \<le> ((A i)::ereal)) \<Longrightarrow> 
(\<Sum> i\<in> I. e2ennreal (A i)) = e2ennreal (\<Sum>i\<in> I. A i)"
proof (induct rule: finite_induct)
  case empty
  then show ?case by (simp add: zero_ennreal.abs_eq)
next
  case (insert x F)
  hence "(\<Sum> i\<in> (insert x F). e2ennreal (A i)) = e2ennreal (A x) + (\<Sum> i\<in> F. e2ennreal (A i))" 
    by simp
  also have "... = e2ennreal (A x) + e2ennreal (\<Sum>i\<in> F. A i)" using insert by simp
  also have "... = e2ennreal (A x + (\<Sum>i\<in> F. A i))" 
  proof (rule e2ennreal_add[symmetric])
    show "0 \<le> A x" using insert by simp
    show "0 \<le> sum A F" using insert by (simp add: sum_nonneg) 
  qed
  also have "... = e2ennreal (\<Sum>i\<in> insert x F. A i)" using insert by simp
  finally show ?case .
qed

lemma e2ennreal_less_top: 
  fixes x::ereal
  assumes "x < \<infinity>"
  shows "e2ennreal x < \<infinity>"
proof (rule ereal_ennreal_cases[of x])
  assume "x < 0"
  hence "e2ennreal x = 0" using e2ennreal_neg by simp
  thus "e2ennreal x < \<infinity>" by simp
next
  fix b
  assume "0 \<le>  x" and "x = enn2ereal b"
  hence "b = e2ennreal x" by simp
  have "b < \<infinity>" 
  proof (rule ccontr)
    assume "\<not> b < \<infinity>"
    hence "b = \<infinity>" by (simp add: less_ennreal.rep_eq) 
    hence "x = \<infinity>" using enn2ereal_eq_top_iff \<open>x = enn2ereal b\<close> by simp
    thus False using assms by simp
  qed
  thus "e2ennreal x < \<infinity>" using \<open>b = e2ennreal x\<close> by simp
qed

lemma pos_e2ennreal_additive:
  assumes "measure_space (space M) (sets M) (\<lambda>x. e2ennreal (m1 x))"
    and "\<forall>x\<in> sets M. 0 \<le> m1 x"
  shows "additive (sets M) m1"
proof (auto simp add: additive_def)
  fix A B
  assume "A\<in> sets M" and "B\<in> sets M" and "A\<inter> B = {}" note abprops = this
  define M1 where "M1 = (\<lambda>x. e2ennreal (m1 x))"
  have "additive (sets M) M1" using ring_of_sets.countably_additive_additive
      sets.ring_of_sets_axioms assms unfolding measure_space_def M1_def by auto
  have "A\<union>B \<in> sets M" using abprops by simp
  hence "m1 (A\<union> B) = enn2ereal (M1 (A\<union> B))" unfolding M1_def using assms enn2ereal_e2ennreal 
      abprops by presburger
  also have "... = enn2ereal (M1 A + M1 B)" using \<open>additive (sets M) M1\<close> abprops 
    unfolding additive_def by simp
  also have "... = enn2ereal (M1 A) + enn2ereal (M1 B)" by (simp add: plus_ennreal.rep_eq)
  also have "... = m1 A + m1 B" unfolding M1_def using assms enn2ereal_e2ennreal 
      abprops by presburger
  finally show "m1 (A\<union> B) = m1 A + m1 B" .
qed

subsection \<open>Some summability properties\<close>

lemma shift_denum:
  shows "1/(x i - (1::nat)) \<le> 2/x i"
proof (cases "x i \<le> 1")
  case True
  hence "x i - 1 = 0" by simp
  thus ?thesis by simp
next
  case False
  hence "2 \<le> x i" by simp
  hence "0 < x i * (x i - 1)" by simp
  hence "0 \<le> (2 * (x i - 1) - x i)/(x i * (x i - 1))" using \<open>2 \<le> x i\<close> by simp
  also have "... = (real (2 * (x i - 1)) - real (x i))/(x i * (x i - 1))"
    using of_nat_diff by auto 
  also have "... = (2 * (x i - 1))/(x i * (x i - 1)) - x i/(x i * (x i - 1))" 
    using diff_divide_distrib[of "2 * (x i - 1)" "x i" "x i * (x i - 1)"] by simp
  also have "... = 2/x i - x i/(x i * (x i - 1))"  using \<open>2 \<le> x i\<close> by auto 
  also have "... = 2/x i - 1/(x i - 1)" by simp
  finally have "0 \<le> 2/x i - 1/(x i - 1)" .
  thus ?thesis by simp
qed

lemma shift_denum':
  assumes "\<And>i. k \<le> x i \<Longrightarrow> k +e  \<le> ((x i)::nat)"
    and "\<And>i. 0 < x i"
    and "\<And>i. x i < p"
    and "0 < e"
  shows "\<exists>c. \<forall>i. 1/(x i - k) \<le> c/(x i)"
proof 
  have "\<And>i. k \<le> x i \<Longrightarrow> e \<le> x i - k" 
  proof -
    fix i
    assume "k \<le> x i"
    hence "k + e \<le> x i" using assms by simp
    thus "e \<le> x i - k" using assms by simp
  qed
  have "\<And>i. k \<le> x i \<Longrightarrow> 0 < (x i)*(x i - k)" 
  proof -
    fix i
    assume "k \<le> x i"
    thus "0 < (x i)*(x i - k)" using assms by force
  qed
  define cw where "cw = p/e"
  have "0 < p" using assms  using neq0_conv by blast
  hence "0 < cw" unfolding cw_def by (simp add: assms(4))
  show "\<forall>i. 1 / (x i - k) \<le> cw / x i"
  proof
    fix i
    show "1 / (x i - k) \<le> cw / x i"
    proof (cases "k \<le> x i")
      case True
      hence "0 \<le> (p - x i)/((x i) * (x i - k))" using \<open>\<And>i. k \<le> x i \<Longrightarrow>0 < x i * (x i - k)\<close> assms(3) 
          divide_nonneg_pos[of "p - x i" "x i * (x i - k)"] by (simp add: less_eq_real_def)
      also have "... = (cw * e - x i)/((x i) * (x i - k))" unfolding cw_def using assms True
        by (metis divide_less_cancel division_ring_divide_zero eq_divide_imp nat_less_le 
            of_nat_0_less_iff of_nat_diff times_divide_eq_left) 
      also have "... \<le> (cw * (x i - k) - x i)/((x i) * (x i - k))"
      proof -
        have "cw * (x i - k) - x i \<ge> cw * e - x i" using \<open>k \<le> x i \<Longrightarrow> e \<le> x i - k\<close> \<open>0 < cw\<close> True  
          by simp
        thus ?thesis using \<open>k \<le> x i \<Longrightarrow> 0 < (x i)*(x i - k)\<close> 
            divide_right_mono[of "cw * e - x i" "cw * (x i - k) - x i" "(x i) * (x i - k)"] by simp
      qed
      also have "... = (cw * (x i -k))/((x i)*(x i - k)) - x i/((x i) * (x i - k))"
        using assms diff_divide_distrib by blast
      also have "... = cw / x i - 1/(x i-k)"
      proof -
        have "1/(x i-k) = x i/((x i) * (x i - k))" using assms(2) less_imp_neq by fastforce
        thus ?thesis using \<open>\<And>i. k \<le> x i \<Longrightarrow> 0 < x i * (x i - k)\<close> assms(2) zero_less_mult_pos
        proof -
          have f1: "\<forall>r ra. (1::real) / (ra / r) = r / ra"
            by simp
          have "real (x i * (x i - k)) \<noteq> 0"
            by (metis True  \<open>\<And>i. k \<le> x i \<Longrightarrow> 0 < x i * (x i - k)\<close> neq0_conv of_nat_0 of_nat_le_0_iff)
          thus ?thesis using f1 by (metis \<open>1 / real (x i - k) = real (x i) / real (x i * (x i - k))\<close> 
                div_by_1 divide_divide_eq_right nonzero_mult_div_cancel_left)
        qed 
      qed
      finally have "0 \<le> cw / x i - 1/(x i-k)" .
      thus "1 / (x i - k) \<le> cw / x i" by simp
    next
      case False
      hence "real (x i - k) = 0" by simp
      hence "1/ real (x i - k) = 0" by simp
      thus "1 / real (x i - k) \<le> cw / real (x i)" by (simp add: cw_def)
    qed
  qed
qed

lemma sum_le:
  assumes "\<And>i. f i \<le> ((g i) :: real)"
  shows "sum f {.. (n::nat)} \<le> sum g {.. n}"
proof (induct n)
  case 0
  then show ?case using assms by simp
next
  case (Suc n)
  have "sum f {..Suc n} = sum f {.. n} + f (Suc n)" by simp
  also have "... \<le> sum g {.. n} + f (Suc n)" using Suc by simp
  also have "... \<le> sum g {.. n} + g (Suc n)" using assms by simp
  also have "... = sum g {.. Suc n}" by simp
  finally show ?case .
qed

lemma summable_bounded:
  assumes "\<And>i. 0 \<le> ((f i)::real)"
    and "\<And>i. f i \<le> g i"
    and "summable g"
  shows "summable f" 
proof (rule bounded_imp_summable, (auto simp add: assms))
  fix n
  have "\<And>i. 0 \<le> g i" using assms dual_order.trans by blast 
  have "sum f {.. n} \<le> sum g {.. n}" using assms sum_le by simp
  also have "... \<le> suminf g" by (rule sum_le_suminf, (auto simp add: assms \<open>\<And>i. 0 \<le> g i\<close>))
  finally show "sum f {.. n} \<le> suminf g" .
qed

lemma sum_shift_denum:
  assumes "summable (\<lambda>i. 1/((f i)::nat))"
  shows "summable (\<lambda>i. 1/(f i - 1))"
proof -
  have "\<forall>i. 1/(f i - 1) \<le> 2 / f i" using shift_denum[of f] by auto
  have "summable (\<lambda>i. 2/ f i)" using assms summable_mult[of "\<lambda>n. 1/ f n"] by simp
  thus ?thesis using summable_bounded[of "\<lambda>i. 1/(f i - 1)" "\<lambda>i. 2 * 1/f i"]
      \<open>\<forall>i. 1 / real (f i - 1) \<le> 2 / real (f i)\<close> by auto
qed

lemma sum_shift_denum':
  assumes "summable (\<lambda>i. 1/(f i))"
    and "0 < e"
    and "\<And>i. k \<le> f i \<Longrightarrow> k + e \<le> ((f i)::nat)"
    and "\<And>i. 0 < f i"
    and "\<And>i. f i < p"
  shows "summable (\<lambda>i. 1/(f i - k))"
proof -
  have "\<And>i. 0 \<le> 1/(f i - k)"
  proof -
    fix i
    have "0 \<le> f i - k" using assms by simp 
    thus "0 \<le> 1/(f i - k)" by simp
  qed
  have "\<exists>c. \<forall>i. 1/(f i - k) \<le> c / f i" using shift_denum'[of k f e p] assms by simp
  from this obtain c where "\<forall>i. 1/(f i - k) \<le> c / f i" by auto
  have "summable (\<lambda>i. c * 1/ f i)" using assms summable_mult[of "\<lambda>n. 1/ f n"] by simp
  thus ?thesis using summable_bounded[of "\<lambda>i. 1/(f i - k)" "\<lambda>i. c * 1/f i"]
      \<open>\<And>i. 0 \<le> 1/(f i - k)\<close> by (simp add: \<open>\<forall>i. 1 / (f i - k) \<le> c / f i\<close>) 
qed

end