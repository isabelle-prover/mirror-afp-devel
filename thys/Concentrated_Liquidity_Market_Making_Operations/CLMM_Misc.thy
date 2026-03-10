theory CLMM_Misc imports "HOL-Analysis.Analysis"


(* Author: Mnacho Echenim. Grenoble INP - UGA, Kaiko *)
(* This research is part of the ANR project BlockFI - 2024-CES38 *)

begin
section \<open>Preliminary definitions and results\<close>

subsection \<open>Misc\<close>


lemma diff_min_le:
  assumes "(a::real) \<le> b"
and "x \<le> y"
shows "min x b - min x a \<le> min y b - min y a"
  using assms by linarith

lemma sum_ex_strict_pos: 
fixes f g :: "'i \<Rightarrow> 'a::ordered_cancel_comm_monoid_add"
  assumes "finite A"
    and "\<forall>x\<in>A. 0 \<le> f x"
    and "\<exists>a\<in>A. 0 < f a"
  shows "0 < sum f A"
proof -
  obtain a where "0 < f a" and "a\<in> A" using assms by auto note aprop = this
  define B where "B = A - {a}"
  hence "A = insert a B" using aprop by auto
  have "0 < f a" using aprop by simp
  also have "... \<le> f a + sum f B"
  proof -
    have "0 \<le> sum f B"
    proof (rule sum_nonneg)
      fix x
      assume "x\<in> B"
      thus "0 \<le> f x" using B_def assms by simp
    qed
    thus ?thesis by (simp add: add_increasing2) 
  qed
  also have "... = sum f (insert a B)"
  proof (rule sum.insert[symmetric])
    show "finite B" using assms B_def by simp
    show "a\<notin> B" using B_def by simp
  qed
  also have "... = sum f A" using \<open>A = insert a B\<close> by simp
  finally show ?thesis .
qed

lemma diff_inv_max_le:
  assumes "0 < a"
  and "(a::real) \<le> b"
  and "x \<le> y"
shows "inverse (max y a) - inverse (max y b) \<le> 
  inverse (max x a) - inverse (max x b)"
proof (cases "b \<le> y")
  case True
  thus ?thesis using assms by auto
next
  case False
  hence "max y b = b" by simp
  have "max x b = b" using False assms by auto
  show ?thesis using \<open>max y b = b\<close> assms by fastforce 
qed

lemma int_interval_insert:
  fixes a::int
  assumes "a \<le> b"
  shows "{a..< (b+1)} = insert b {a..< b}"
proof
  show "{a..<b + 1} \<subseteq> insert b {a..<b}"
  proof
    fix x
    assume "x \<in> {a..<b + 1}"
    show "x \<in> insert b {a..<b}"
    proof (cases "x = b")
      case True
      then show ?thesis by simp
    next
      case False
      hence "x < b" using \<open>x \<in> {a..<b + 1}\<close> by simp
      then show ?thesis using \<open>x \<in> {a..<b + 1}\<close> by simp
    qed
  qed
next
  show "insert b {a..<b} \<subseteq> {a..<b + 1}" by (simp add: assms)
qed

lemma int_telescoping_sum:
  fixes f::"int \<Rightarrow> 'a::ab_group_add"
  assumes "a \<le> b"
  shows "(\<Sum>i \<in>{a..<b}. (f i - f (i+1))) = f a - (f b)" using \<open>a \<le> b\<close>
proof (induct rule: int_ge_induct )
  case base
  then show ?case by simp
next
  case (step i)
  have "{a..<i + 1} = insert i {a..<i}" 
    using int_interval_insert \<open>a \<le> i\<close> by simp
  hence "(\<Sum>i \<in> {a..<i + 1}. f i - f (i + 1)) = 
    (\<Sum>i \<in> (insert i {a..<i}). f i - f (i + 1))" by simp
  also have "... = f i - f (i+1) + (\<Sum>i = a..<i. f i - f (i + 1))" 
    by (rule sum.insert, auto)
  also have "... = f i - f (i+1) + f a - f i" using step by simp
  also have "... = f a - f (i+1)" by simp
  finally show ?case .
qed

lemma int_telescoping_sum':
  fixes f::"int \<Rightarrow> 'a::ab_group_add"
  assumes "a \<le> b"
  shows "(\<Sum>i \<in>{a..<b}. (f (i+1) - f i)) = f b - (f a)"
proof -
  define g where "g = (\<lambda>x. - f x)"
  have "(\<Sum>i \<in>{a..<b}. (f (i+1) - f i)) = (\<Sum>i \<in>{a..<b}. (g i - g (i+1)))"
    by (rule sum.cong, auto simp add: g_def)
  also have "... = g a - g b" using assms int_telescoping_sum[of a b] by simp
  also have "... = f b - f a" using g_def by simp
  finally show ?thesis .
qed

lemma int_telescoping_sum_le':
  fixes f::"int \<Rightarrow> 'a::ab_group_add"
  assumes "a \<le> b"
  shows "(\<Sum>i \<in>{a..b}. (f (i+1) - f i)) = f (b+1) - (f a)"
proof -
  have "{a..b} = {a..< b+1}" by auto
  thus ?thesis using assms int_telescoping_sum'[of a "b+1"] by simp
qed

lemma diff_sum_dcomp:
  fixes f::"'a \<Rightarrow> real"
  assumes "finite A"
  and "A = B \<union> C"
  and "B \<inter> C = {}"  
shows "x + sum f A - (y + sum f B) = x + sum f C - y"
proof -
  have "sum f A = sum f (B \<union> C)" using assms by simp
  also have "... = sum f B + sum f C" 
  proof (rule sum.union_inter_neutral)
    show "finite B" using assms by simp
    show "finite C" using assms by simp
    show "\<forall>x\<in>B \<inter> C. f x = 0" using assms by simp
  qed
  finally have "sum f A = sum f B + sum f C" .
  thus ?thesis by simp
qed

lemma sum_remove_el:
  assumes "finite A"
  and "x\<in> A"
  and "B = A - {x}"
  shows "sum f A = f x + sum f B"
proof -
  have "A = insert x B" using assms by auto
  hence "sum f A = sum f (insert x B)" by simp
  also have "... = f x + sum f B"
  proof (rule sum.insert)
    show "finite B" using assms by simp
    show "x\<notin> B" using assms by simp
  qed
  finally show ?thesis .
qed

lemma int_set_bdd_above:
  fixes X::"int set"
  assumes "X \<noteq> {}"
    and "bdd_above X"
  shows "Sup X \<in> X" "\<forall>x \<in> X. x \<le> Sup X"
proof -
  from assms obtain x y where "x \<in> X" and "X \<subseteq> {..y}"
    by (auto simp: bdd_above_def)
  hence *: "finite (X \<inter> {x..y})" "X \<inter> {x..y} \<noteq> {}" and "x \<le> y"
    by (auto simp: subset_eq)
  have "\<exists>!x\<in>X. (\<forall>y\<in>X. y \<le> x)"
  proof
    { fix z assume "z \<in> X"
      have "z \<le> Max (X \<inter> {x..y})"
      proof cases
        assume "x \<le> z" with \<open>z \<in> X\<close> \<open>X \<subseteq> {..y}\<close> *(1) show ?thesis
          by (auto intro!: Max_ge)
      next
        assume "\<not> x \<le> z"
        then have "z < x" by simp
        also have "x \<le> Max (X \<inter> {x..y})"
          using \<open>x \<in> X\<close> *(1) \<open>x \<le> y\<close> by (intro Max_ge) auto
        finally show ?thesis by simp
      qed }
    note le = this
    with Max_in[OF *] show 
        ex: "Max (X \<inter> {x..y}) \<in> X \<and> (\<forall>z\<in>X. z \<le> Max (X \<inter> {x..y}))" 
      by auto    
      fix z assume *: "z \<in> X \<and> (\<forall>y\<in>X. y \<le> z)"
      with le have "z \<le> Max (X \<inter> {x..y})"
        by auto
      moreover have "Max (X \<inter> {x..y}) \<le> z"
        using * ex by auto
      ultimately show "z = Max (X \<inter> {x..y})"
        by auto
    qed
    hence "Sup X \<in> X \<and> (\<forall>y\<in>X. y \<le> Sup X)"
    unfolding Sup_int_def by (rule theI')
  thus "Sup X \<in> X" "\<forall>x \<in> X. x \<le> Sup X" by auto
qed

definition wedge where
"wedge f (i::int) sqp = (\<lambda>n. if n \<le> i then f n else f (n-1))(i+1:=sqp)"

lemma wedge_arg_lt[simp]:
  assumes "n \<le> i"
  shows "wedge f i sqp n = f n" using assms unfolding wedge_def by simp

lemma wedge_arg_gt[simp]:
  assumes "i+1 < n"
  shows "wedge f i sqp n = f (n-1)" using assms unfolding wedge_def by simp

lemma wedge_arg_eq[simp]:
  shows "wedge f i sqp (i+1) = sqp" unfolding wedge_def by simp

lemma wedge_strict_mono:
  assumes "strict_mono f"
  and "f i < sqp"
  and "sqp < f (i+1)"
  and "g = wedge f i sqp"
shows "strict_mono g" unfolding strict_mono_def
proof (intro allI impI)
  fix x y
  assume "(x::int) < y"
  show "g x < g y" 
  proof (cases "y < i+1")
    case True
    then show ?thesis
      using \<open>x < y\<close> assms strict_mono_less by fastforce
  next
    case False
    show ?thesis
    proof (cases "y = i+1")
      case True
      hence "wedge f i sqp y = sqp" by simp
      have "x \<le> i" using True \<open>x < y\<close> by simp
      hence "wedge f i sqp x = f x" by simp
      then show ?thesis using \<open>wedge f i sqp y = sqp\<close> assms
        by (metis \<open>x \<le> i\<close> monoE order_le_less_trans strict_mono_mono)
    next
      case False
      hence "i+1 < y" using \<open>\<not> y < i+1\<close> by simp
      hence "wedge f i sqp y = f (y - 1)" by simp
      show ?thesis
      proof (cases "x = i+1")
        case True
        then show ?thesis
          by (metis (mono_tags, lifting) \<open>wedge f i sqp y = f (y - 1)\<close> 
              \<open>x < y\<close> assms(1) assms(3) assms(4) monoD order_less_le_subst1 
              strict_mono_on_imp_mono_on wedge_arg_eq zle_diff1_eq) 
      next
        case False
        then show ?thesis
          by (metis \<open>i + 1 < y\<close> \<open>x < y\<close> assms(1) assms(4) diff_strict_right_mono 
              linorder_le_less_linear order_le_imp_less_or_eq strict_monoD 
              wedge_arg_gt wedge_arg_lt zle_diff1_eq zless_imp_add1_zle) 
      qed
    qed
  qed
qed

lemma wedge_gt:
  assumes "\<forall>i. x < f i"
  and "x < sqp"
  shows "\<forall>i. x < wedge f j sqp i"
  by (smt (verit) assms wedge_arg_eq wedge_arg_gt wedge_arg_lt)

lemma wedge_ge:
  assumes "\<forall>i. x \<le> f i"
  and "x \<le> sqp"
  shows "\<forall>i. x \<le> wedge f j sqp i"
  by (smt (verit) assms wedge_arg_eq wedge_arg_gt wedge_arg_lt)

lemma wedge_lt:
  assumes "\<forall>i. f i < x"
  and "sqp < x"
  shows "\<forall>i. wedge f j sqp i < x"
  by (smt (verit) assms wedge_arg_eq wedge_arg_gt wedge_arg_lt)

lemma wedge_le:
  assumes "\<forall>i. f i \<le> x"
  and "sqp \<le> x"
  shows "\<forall>i. wedge f j sqp i \<le> x"
  by (smt (verit) assms wedge_arg_eq wedge_arg_gt wedge_arg_lt)

lemma wedge_images:
  shows "\<forall>j. \<exists>k. f j = wedge f i sqp k"
proof
  fix j
  show "\<exists>k. f j = wedge f i sqp k"
  proof (cases "j \<le> i")
    case True
    hence "wedge f i sqp j = f j" by simp
    then show ?thesis by metis
  next
    case False
    hence "i+1 \<le> j" by simp
    hence "wedge f i sqp (j+1) = f j" by simp
    then show ?thesis by metis
  qed
qed

lemma wedge_images':
  assumes "A = {j. j \<le> i}"
  and "B = {j. i+1 < j}" 
shows "wedge f i sqp k \<in> f`A \<union> (f`((\<lambda>i. i-1)`B)) \<union> {sqp}"
proof (cases "k \<le> i")
  case True
  hence "wedge f i sqp k = f k" by simp
  hence "wedge f i sqp k \<in> f`A" using assms True by simp
  then show ?thesis by simp 
next
  case False
  show ?thesis 
  proof (cases "k = i+1")
    case True
    then show ?thesis by simp
  next
    case False
    hence "i+1 < k" using \<open>\<not> k \<le> i\<close> by simp
    then show ?thesis by (simp add: \<open>i + 1 < k\<close> assms(2))
  qed
qed

lemma wedge_as_ubound:
  assumes "\<forall>(r::real). \<exists>(i::int). r < f i"
  shows "\<forall>r. \<exists>k. r < wedge f i sqp k" using assms 
  by (metis wedge_images) 

lemma wedge_as_lbound:
  assumes "\<forall>(r::real) > 0. \<exists>(i::int). f i < r"
  shows "\<forall>r > 0. \<exists>k. wedge f i sqp k < r" using assms 
  by (metis wedge_images) 

lemma wedge_arg_prop:
  shows "{j. P (wedge f i sqp j)} \<subseteq> {j. j \<le> i \<and> P (f j)} \<union> 
    {j. i+1 < j \<and> P (f (j-1))} \<union> {i+1}"
proof
  fix j
  assume "j\<in> {j. P (wedge f i sqp j)}"
  hence pr: "P (wedge f i sqp j)" by auto
  show "j \<in> {j. j \<le> i \<and> P (f j)} \<union> {j. i+1 < j \<and> P (f (j-1))} \<union> {i+1}"
  proof (cases "j \<le> i")
    case True
    hence "wedge f i sqp j = f j" by simp
    then show ?thesis using pr True by simp
  next
    case False
    show ?thesis
    proof (cases "j = i+1")
      case True
      then show ?thesis using pr by simp
    next
      case False
      hence "i+1 < j" using \<open>\<not> j \<le> i\<close> by simp
      hence "wedge f i sqp j = f (j-1)" by simp
      then show ?thesis using pr \<open>i+1 < j\<close> by simp
    qed
  qed
qed

definition one_cpl where
"one_cpl phi = (\<lambda>(i::int). (1::real) - (phi i))"

definition gross_fct where
"gross_fct f phi = (\<lambda>i. f i / (one_cpl phi i))"

lemma gross_fct_sgn:
  assumes "phi i < (1::real)"
  shows "((0::real) \<le> f i) \<longleftrightarrow> (0 \<le> gross_fct f phi i)" unfolding gross_fct_def
  by (metis assms diff_ge_0_iff_ge eucl_less_le_not_le le_iff_diff_le_0 
      one_cpl_def zero_le_divide_iff)

lemma gross_fct_nz_eq:
  assumes "phi i \<noteq> (1::real)"
  shows "f i = 0 \<longleftrightarrow> gross_fct f phi i = 0" using assms unfolding gross_fct_def
  by (simp add: one_cpl_def)

lemma gross_fct_cong:
  assumes "f a = f' b"
  and "phi a = phi' b"
shows "gross_fct f phi a = gross_fct f' phi' b" using assms 
  unfolding gross_fct_def by (simp add: one_cpl_def)

lemma gross_fct_zero_if:
  assumes "f a = 0"
  shows "gross_fct f phi a = 0" using assms unfolding gross_fct_def by simp

definition fee_union where
"fee_union (l1::real) l2 f1 f2 = (l1*f1*(1-f2) + l2*f2*(1-f1))/
  (l1*(1-f2) + l2*(1-f1))"

lemma fee_union_pos:
  assumes "0 \<le> l1"
  and "0 \<le> l2"
  and "0 \<le> f1"
  and "0 \<le> f2"
  and "f1 < 1"
  and "f2 < 1"
shows "0 \<le> fee_union l1 l2 f1 f2" using assms unfolding fee_union_def by simp

lemma fee_union_lt_1:
  assumes "0 \<le> l1"
  and "0 \<le> l2"
  and "0 \<le> f1"
  and "0 \<le> f2"
  and "f1 < 1"
  and "f2 < 1"
shows "fee_union l1 l2 f1 f2 < 1" 
proof (cases "l1 = 0")
  case True
  thus ?thesis unfolding fee_union_def by (simp add: assms(6))
next
  case False
  show ?thesis 
  proof (cases "l2 = 0")
    case True
    then show ?thesis unfolding fee_union_def by (simp add: assms(5))
  next
    case False
    hence "0 < l1*(1-f2) + l2*(1-f1)" using assms \<open>\<not> l1 = 0\<close>
      by (simp add: less_eq_real_def pos_add_strict) 
    moreover have "l1*f1*(1-f2) + l2*f2*(1-f1) < l1*(1-f2) + l2*(1-f1)"
      using assms False \<open>\<not> l1 = 0\<close>
      by (smt (verit, best) mult_less_cancel_left2 mult_less_cancel_right)
    ultimately show ?thesis unfolding fee_union_def by simp
  qed
qed

lemma diff_inv_le:
  assumes "0 < (x::real)"
  and "x \<le> y"
  and "y \<le> z"
shows "(y - x)/(z*z) \<le> inverse x - inverse y"
proof -
  have "0 < y" using assms by simp
  hence "0 < z" using assms by simp
  have "(y - x)/(z*z) \<le> (y - x) / (x * y)" using assms
    by (simp add: frac_le mult_mono)
  also have "... = inverse x - inverse y"
    using \<open>0 < x\<close> \<open>0 < y\<close>
    by (simp add: divide_real_def division_ring_inverse_diff)
  finally show ?thesis .
qed

lemma diff_inv_le':
  assumes "0 < (x::real)"
  and "x \<le> y"
  and "y \<le> z"
  and "0 \<le> a"
shows " a * (y - x)/(z*z) \<le> a * (inverse x - inverse y)"
proof -
  have "0 < y" using assms by simp
  hence "0 < z" using assms by simp
  have "(y - x)/(z*z) \<le> (y - x) / (x * y)" using assms
    by (simp add: frac_le mult_mono)
  also have "... = inverse x - inverse y"
    using \<open>0 < x\<close> \<open>0 < y\<close>
    by (simp add: divide_real_def division_ring_inverse_diff)
  finally show ?thesis
    by (metis assms(4) mult_left_mono times_divide_eq_right) 
qed

lemma diff_inv_sum_le':
  assumes "\<forall>i \<in> I. (0::real) < f i"
  and "\<forall>i \<in> I. f i \<le> f (i+1)"
  and "\<forall>i\<in> I. f (i+1) \<le> z"
  and "\<forall>i \<in> I. 0 \<le> g i"
  shows  "sum (\<lambda>i. g i * (f (i+1) - f i)) I / (z * z) \<le> 
    sum (\<lambda>i. g i * (inverse (f i) - inverse (f (i+1)))) I"
proof -
  have "sum (\<lambda>i. g i * (f (i+1) - f i)) I / (z * z) = 
      sum (\<lambda>i. g i * (f (i+1) - f i)/ (z * z)) I"
    by (rule sum_divide_distrib)
  also have "... \<le> sum (\<lambda>i. g i * (inverse (f i) - inverse (f (i+1)))) I"
  proof (rule sum_mono)
    fix i 
    assume "i \<in> I"
    show "g i * (f (i + 1) - f i) / (z * z) \<le> 
        g i * (inverse (f i) - inverse (f (i + 1)))"
      by (rule diff_inv_le', (auto simp add: assms \<open>i \<in> I\<close>))
  qed
  finally show ?thesis .
qed

lemma diff_inv_ge:
  assumes "0 < (x::real)"
  and "x \<le> y"
  and "y \<le> z"
shows "inverse y - inverse z \<le> (z - y)/(x*x)"
proof -
  have "0 < y" using assms by simp
  hence "0 < z" using assms by simp
  hence "inverse y - inverse z = (z - y) / (y * z)"
    using \<open>0 < y\<close> by (simp add: divide_real_def division_ring_inverse_diff)
  also have "... \<le> (z - y)/(x*x)" using assms
    by (simp add: frac_le mult_mono)
  finally show ?thesis .
qed

lemma diff_inv_ge':
  assumes "0 < (x::real)"
  and "x \<le> y"
  and "y \<le> z"
  and "0 \<le> a"
shows "a * (inverse y - inverse z) \<le> a * (z - y)/(x*x)"
proof -
  have "0 < y" using assms by simp
  hence "0 < z" using assms by simp
  hence "inverse y - inverse z = (z - y) / (y * z)"
    using \<open>0 < y\<close> by (simp add: divide_real_def division_ring_inverse_diff)
  also have "... \<le> (z - y)/(x*x)" using assms
    by (simp add: frac_le mult_mono)
  finally show ?thesis
    by (metis assms(4) mult_left_mono times_divide_eq_right) 
qed

lemma diff_inv_sum_ge':
  assumes "(0::real) < z"
  and "\<forall>i \<in> I. f i \<le> f (i+1)"
  and "\<forall>i\<in> I. z \<le> f i"
  and "\<forall>i \<in> I. 0 \<le> g i"
shows  "sum (\<lambda>i. g i * (inverse (f i) - inverse (f (i+1)))) I \<le> 
  sum (\<lambda>i. g i * (f (i+1) - f i)) I / (z * z)"
proof -
  have "sum (\<lambda>i. g i * (inverse (f i) - inverse (f (i+1)))) I \<le> 
      sum (\<lambda>i. g i * (f (i+1) - f i)/ (z * z)) I"
  proof (rule sum_mono)
    fix i
    assume "i \<in> I"
    show "g i * (inverse (f i) - inverse (f (i + 1))) \<le> 
        g i * (f (i + 1) - f i) / (z * z)"
      by (rule diff_inv_ge', (auto simp add: assms \<open>i \<in> I\<close>))
  qed
  also have "... = sum (\<lambda>i. g i * (f (i+1) - f i)) I / (z * z)"
    by (rule sum_divide_distrib[symmetric])
  finally show ?thesis .
qed

subsection \<open>Support of a discrete function\<close>

definition nz_support where
"nz_support f = {i. f i \<noteq> 0}"

lemma nz_supportD:
  assumes "i\<in> nz_support f"
  shows "f i \<noteq> 0" using assms unfolding nz_support_def by simp

lemma wedge_finite_nz_support:
  assumes "finite (nz_support f)"
  shows "finite (nz_support (wedge f i sqp))" 
proof -
  define A where "A = {j. j \<le> i \<and> f j \<noteq> 0}"
  define B where  "B = {j. i+1 < j \<and> f (j-1) \<noteq> 0}" 
  have inc: "nz_support (wedge f i sqp) \<subseteq> A \<union> B \<union> {i+1}" 
    using wedge_arg_prop[of "\<lambda>x. x \<noteq> 0"] 
    unfolding nz_support_def A_def B_def by auto
  have "finite A" using assms unfolding nz_support_def A_def by auto
  have "B\<subseteq> (\<lambda>j. j+1)`{j. f j \<noteq> 0}"
  proof
    fix j
    assume "j\<in> B"
    hence "i+1 < j" and "f (j-1) \<noteq> 0" unfolding B_def by auto note asm = this
    define k where "k = j-1"
    hence "f k \<noteq> 0" using asm by simp
    hence "k \<in> {j. f j\<noteq> 0}" by simp
    thus "j \<in> (\<lambda>j. j+1)`{j. f j \<noteq> 0}" using \<open>k = j-1\<close> by force
  qed
  hence "finite B" using assms finite_surj unfolding nz_support_def by auto
  thus ?thesis using assms \<open>finite A\<close> inc
    by (meson finite.simps finite_UnI finite_subset)
qed

lemma gross_nz_support_eq:
  assumes "\<forall>i \<in> nz_support f. phi i \<noteq> 1"
  shows "nz_support f = nz_support (gross_fct f phi)" 
  using assms gross_fct_nz_eq gross_fct_zero_if unfolding nz_support_def
  by blast

definition idx_min where
"idx_min f = Inf (nz_support f)"

definition idx_max where
"idx_max f = Sup (nz_support f)"

lemma idx_max_bdd_above_ge:
  fixes f::"'a::conditionally_complete_linorder \<Rightarrow> 'b::zero"
  assumes "f i \<noteq> 0"
  and "bdd_above (nz_support f)"
shows "i \<le> idx_max f" 
proof -
  have "i \<in> nz_support f" unfolding nz_support_def using assms by simp
  thus ?thesis unfolding idx_max_def
    by (simp add: assms cSup_upper)
qed

lemma idx_min_bdd_below_le:
  fixes f::"'a::conditionally_complete_linorder \<Rightarrow> 'b::zero"
  assumes "f i \<noteq> 0"
  and "bdd_below (nz_support f)"
shows "idx_min f \<le> i" 
proof -
  have "i \<in> nz_support f" unfolding nz_support_def using assms by simp
  thus ?thesis unfolding idx_min_def
    by (simp add: assms cInf_lower)
qed

lemma idx_max_finite_ge:
  fixes f::"'a::conditionally_complete_linorder \<Rightarrow> 'b::zero"
  assumes "f i \<noteq> 0"
  and "finite (nz_support f)"
shows "i \<le> idx_max f" using assms
  by (simp add: idx_max_bdd_above_ge)

lemma idx_min_finite_le:
  fixes f::"'a::conditionally_complete_linorder \<Rightarrow> 'b::zero"
  assumes "f i \<noteq> 0"
  and "finite (nz_support f)"
shows "idx_min f \<le> i" using assms
  by (simp add: idx_min_bdd_below_le)

lemma idx_max_finite:
  fixes f::"'a::conditionally_complete_linorder \<Rightarrow> 'b::zero"
  assumes "nz_support f \<noteq> {}"
  and "finite (nz_support f)"
shows "idx_max f = Max (nz_support f)" using assms unfolding idx_max_def 
  by (simp add: cSup_eq_Max)

lemma idx_min_finite:
  fixes f::"'a::conditionally_complete_linorder \<Rightarrow> 'b::zero"
  assumes "nz_support f \<noteq> {}"
  and "finite (nz_support f)"
shows "idx_min f = Min (nz_support f)" using assms unfolding idx_min_def 
  by (simp add: cInf_eq_Min)

lemma idx_max_finite_in:
  fixes f::"'a::conditionally_complete_linorder \<Rightarrow> 'b::zero"
  assumes "nz_support f \<noteq> {}"
  and "finite (nz_support f)"
shows "f (idx_max f) \<noteq> 0" using assms idx_max_finite 
  by (metis Max_in nz_supportD)

lemma idx_min_finite_in:
  fixes f::"'a::conditionally_complete_linorder \<Rightarrow> 'b::zero"
  assumes "nz_support f \<noteq> {}"
  and "finite (nz_support f)"
shows "f (idx_min f) \<noteq> 0" using assms idx_min_finite
  by (metis Min_in nz_supportD)

lemma idx_max_finite_gt:
  fixes f::"'a::conditionally_complete_linorder \<Rightarrow> 'b::zero"
  assumes "finite (nz_support f)"
and "idx_max f < i"
shows "f i = 0" 
proof -
  have "i \<notin> nz_support f" using assms idx_max_finite
    by (metis Max_ge emptyE linorder_not_less)
  thus ?thesis by (simp add: nz_support_def) 
qed

lemma idx_min_finite_lt:
  fixes f::"'a::conditionally_complete_linorder \<Rightarrow> 'b::zero"
  assumes "finite (nz_support f)"
and "i < idx_min f"
shows "f i = 0" 
proof -
  have "i \<notin> nz_support f" using assms idx_min_finite
    by (metis Min_le emptyE linorder_not_less)
  thus ?thesis by (simp add: nz_support_def) 
qed

lemma idx_min_finite_max:
fixes f::"'a::conditionally_complete_linorder \<Rightarrow> 'b::zero"
assumes "nz_support f \<noteq> {}"
and "finite (nz_support f)"
and "\<And>j. j < i \<Longrightarrow> f j = 0"
shows "i \<le> idx_min f" 
proof (rule ccontr)
  assume "\<not> i \<le> idx_min f"
  hence "idx_min f < i" by simp
  hence "f (idx_min f) = 0" using assms by simp
  thus False using idx_min_finite_in assms by metis
qed

lemma idx_min_max_finite:
  fixes f::"'a::conditionally_complete_linorder \<Rightarrow> 'b::zero"
  assumes "nz_support f \<noteq> {}"
  and "finite (nz_support f)"
shows "idx_min f\<le> idx_max f" 
proof -
  have "idx_max f \<in> nz_support f" 
    using idx_max_finite_in assms unfolding nz_support_def by simp  
  thus "idx_min f \<le> idx_max f" 
    using idx_min_finite_le assms unfolding nz_support_def by simp
qed

lemma idx_min_finiteI:
  fixes f::"'a::conditionally_complete_linorder \<Rightarrow> 'b::zero"
  assumes "finite (nz_support f)"
  and "f i \<noteq> 0"
  and "\<And>j. j < i\<Longrightarrow> f j = 0"
shows "i = idx_min f"
proof -
  have "nz_support f \<noteq> {}" using assms unfolding nz_support_def by auto
  thus ?thesis
    using assms idx_min_finite_le nless_le by (metis idx_min_finite_in)
qed

lemma idx_min_finite_ge:
  fixes f::"'a::conditionally_complete_linorder \<Rightarrow> 'b::zero"
  assumes "finite (nz_support f)"
  and "nz_support f \<noteq> {}"
  and "\<And>j. j \<le> i\<Longrightarrow> f j = 0"
shows "i \<le> idx_min f"
  by (meson assms idx_min_finite_in nle_le)

lemma idx_max_finiteI:
  fixes f::"'a::conditionally_complete_linorder \<Rightarrow> 'b::zero"
  assumes "finite (nz_support f)"
  and "f i \<noteq> 0"
  and "\<And>j. j > i \<Longrightarrow> f j = 0"
shows "i = idx_max f"
proof -
  have "nz_support f \<noteq> {}" using assms unfolding nz_support_def by auto
  thus ?thesis using assms
    by (meson idx_max_finite_gt idx_max_finite_in linorder_less_linear)
qed

lemma idx_max_finite_le:
  fixes f::"'a::conditionally_complete_linorder \<Rightarrow> 'b::zero"
  assumes "finite (nz_support f)"
  and "nz_support f \<noteq> {}"
  and "\<And>j. i\<le> j \<Longrightarrow> f j = 0"
shows "idx_max f \<le> i"
  using assms idx_max_finite_in linorder_linear by auto

definition idx_min_img where
"idx_min_img g f = g (idx_min f)"

lemma idx_min_img_eq:
  assumes "\<forall>x. f x = 0 \<longleftrightarrow> f' x = 0"
  shows "idx_min_img g f = idx_min_img g f'" unfolding idx_min_img_def using assms
  by (simp add: idx_min_def nz_support_def) 

definition idx_max_img where
"idx_max_img g f = g (idx_max f + 1)"

lemma idx_max_img_eq:
  assumes "\<forall>x. f x = 0 \<longleftrightarrow> f' x = 0"
  shows "idx_max_img g f = idx_max_img g f'" unfolding idx_max_img_def using assms
  by (simp add: idx_max_def nz_support_def) 

lemma non_zero_liq_interv:
  fixes i::"'a::conditionally_complete_linorder"
  assumes "finite (nz_support L)"
  and "L i \<noteq> 0"
  shows "i \<in> {idx_min L .. idx_max L}"
  using assms idx_max_finite_ge idx_min_finite_le by auto

end