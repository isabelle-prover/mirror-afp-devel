(*  Author:  Sébastien Gouëzel   sebastien.gouezel@univ-rennes1.fr
    License: BSD
*)

theory SG_Library_Complement
  imports "~ ~/src/HOL/Probability/Probability"
begin


section {*SG Libary complements*}

text {* In this file are included many statements that were useful to me, but belong rather
naturally to existing theories. In a perfect world, some of these statements would get included
into these files.

I tried to indicate to which of these classical theories the statements could be added.
*}

subsection {*Basic logic*}

text {* This one is certainly available, but I could not locate it... *}
lemma equiv_neg:
  "\<lbrakk> P \<Longrightarrow> Q; \<not>P \<Longrightarrow> \<not>Q \<rbrakk> \<Longrightarrow> (P\<longleftrightarrow>Q)"
by blast


subsection {*Basic set theory*}

abbreviation sym_diff :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a set" (infixl "\<Delta>" 70) where
  "sym_diff A B \<equiv> ((A - B) \<union> (B-A))"

text {* Not sure the next lemmas are useful, as they are proved solely by auto, so they
could be reproved automatically whenever necessary.*}

lemma sym_diff_inc:
  "A \<Delta> C \<subseteq> A \<Delta> B \<union> B \<Delta> C"
by auto

lemma sym_diff_vimage [simp]:
  "f-`(A \<Delta> B) = (f-`A) \<Delta> (f-`B)"
by auto

lemma card_finite_union:
  assumes "finite I"
  shows "card(\<Union>i\<in>I. A i) \<le> (\<Sum>i\<in>I. card(A i))"
using assms apply (induct, auto)
using card_Un_le nat_add_left_cancel_le order_trans by blast


subsection {*Set-Interval.thy*}

text{* The next two lemmas belong naturally to \verb+Set_Interval.thy+, next to
\verb+UN_le_add_shift+. They are not trivially equivalent to the corresponding lemmas
with large inequalities, due to the difference when $n=0$. *}

lemma UN_le_add_shift_strict:
  "(\<Union>i<n::nat. M(i+k)) = (\<Union>i\<in>{k..<n+k}. M i)" (is "?A = ?B")
proof
  show "?B \<subseteq> ?A"
  proof
    fix x assume "x \<in> ?B"
    then obtain i where i: "i \<in> {k..<n+k}" "x \<in> M(i)" by auto
    then have "i - k < n \<and> x \<in> M((i-k) + k)" by auto
    then show "x \<in> ?A" using UN_le_add_shift by blast
  qed
qed (fastforce)

lemma UN_le_eq_Un0_strict:
  "(\<Union>i<n+1::nat. M i) = (\<Union>i\<in>{1..<n+1}. M i) \<union> M 0" (is "?A = ?B")
proof
  show "?A \<subseteq> ?B"
  proof
    fix x assume "x \<in> ?A"
    then obtain i where i: "i<n+1" "x \<in> M i" by auto
    show "x \<in> ?B"
    proof(cases i)
      case 0 with i show ?thesis by simp
    next
      case (Suc j) with i show ?thesis by auto
    qed
  qed
qed (auto)

text {* I use repeatedly this one, but I could not find it directly *}

lemma union_insert_0:
  "(\<Union>n::nat. A n) = A 0 \<union> (\<Union>n\<in>{1..}. A n)"
by (metis UN_insert Un_insert_left sup_bot.left_neutral One_nat_def atLeast_0 atLeast_Suc_greaterThan ivl_disj_un_singleton(1))

text {*Next one could be close to \verb+sum_nat_group+*}

lemma sum_arith_progression:
  "(\<Sum>r<(N::nat). (\<Sum>i<a. f (i*N+r))) = (\<Sum>j<a*N. f j)"
proof -
  have *: "(\<Sum>r<N. f (i*N+r)) = (\<Sum> j \<in> {i*N..<i*N + N}. f j)" for i
    by (rule sum.reindex_bij_betw, rule bij_betw_byWitness[where ?f'= "\<lambda>r. r-i*N"], auto)

  have "(\<Sum>r<N. (\<Sum>i<a. f (i*N+r))) = (\<Sum>i<a. (\<Sum>r<N. f (i*N+r)))"
    using sum.commute by auto
  also have "... = (\<Sum>i<a. (\<Sum> j \<in> {i*N..<i*N + N}. f j))"
    using * by auto
  also have "... = (\<Sum>j<a*N. f j)"
    by (rule sum_nat_group)
  finally show ?thesis by simp
qed


subsection {*Miscellanous basic results*}

lemma ind_from_1 [case_names 1 Suc, consumes 1]:
  assumes "n > 0"
  assumes "P 1"
      and "\<And>n. n > 0 \<Longrightarrow> P n \<Longrightarrow> P (Suc n)"
  shows "P n"
proof -
  have "(n = 0) \<or> P n"
  proof (induction n)
    case 0 then show ?case by auto
  next
    case (Suc k)
    consider "Suc k = 1" | "Suc k > 1" by linarith
    then show ?case
      apply (cases) using assms Suc.IH by auto
  qed
  then show ?thesis using `n > 0` by auto
qed

lemma Inf_nat_def0:
  fixes K::"nat set"
  assumes "n\<in>K"
          "\<And> i. i<n \<Longrightarrow> i\<notin>K"
  shows "Inf K = n"
using assms cInf_eq_minimum not_less by blast

lemma Inf_nat_def1:
  fixes K::"nat set"
  assumes "K \<noteq> {}"
  shows "Inf K \<in> K"
by (auto simp add: Min_def Inf_nat_def) (meson LeastI assms bot.extremum_unique subsetI)

text{* This lemma is certainly available somewhere, but I couldn't
locate it *}

lemma tends_to_real_e:
  fixes u::"nat \<Rightarrow> real"
  assumes "u \<longlonglongrightarrow> l"
          "e>0"
  shows "\<exists>N. \<forall>n>N. abs(u n -l) < e"
proof-
  have "eventually (\<lambda>n. dist (u n) l < e) sequentially" using assms tendstoD by auto
  then have "\<forall>\<^sub>F n in sequentially. abs(u n - l) < e" using dist_real_def by auto
  then show ?thesis by (simp add: eventually_at_top_dense)
qed

lemma nat_mod_cong:
  assumes "a=b+(c::nat)"
          "a mod n = b mod n"
  shows "c mod n = 0"
proof -
  let ?k = "a mod n"
  obtain a1 where "a = a1*n + ?k" by (metis div_mult_mod_eq)
  moreover obtain b1 where "b = b1*n + ?k" using assms(2) by (metis div_mult_mod_eq)
  ultimately have "a1 * n + ?k = b1 * n + ?k + c" using assms(1) by arith
  then have "c = (a1 - b1) * n" by (simp add: diff_mult_distrib)
  then show ?thesis by simp
qed

text {*The next two lemmas are not directly equivalent, since $f$ might
not be injective.*}

lemma abs_Max_sum:
  fixes A::"real set"
  assumes "finite A" "A \<noteq> {}"
  shows "abs(Max A) \<le> (\<Sum>a\<in>A. abs(a))"
using assms by (induct rule: finite_ne_induct, auto)

lemma abs_Max_sum2:
  fixes f::"_ \<Rightarrow> real"
  assumes "finite A" "A \<noteq> {}"
  shows "abs(Max (f`A)) \<le> (\<Sum>a\<in>A. abs(f a))"
using assms by (induct rule: finite_ne_induct, auto)


subsection {*Fun.thy*}

lemma inj_fn:
  fixes f::"'a \<Rightarrow> 'a"
  assumes "inj f"
  shows "inj (f^^n)"
proof (induction n)
  case (Suc n)
  have "inj (f o (f^^n))"
    using inj_comp[OF assms Suc.IH] by simp
  then show "inj (f^^(Suc n))"
    by auto
qed (auto)

lemma surj_fn:
  fixes f::"'a \<Rightarrow> 'a"
  assumes "surj f"
  shows "surj (f^^n)"
proof (induction n)
  case (Suc n)
  have "surj (f o (f^^n))"
    using assms Suc.IH by (simp add: comp_surj)
  then show "surj (f^^(Suc n))"
    by auto
qed (auto)

lemma bij_fn:
  fixes f::"'a \<Rightarrow> 'a"
  assumes "bij f"
  shows "bij (f^^n)"
by (rule bijI[OF inj_fn[OF bij_is_inj[OF assms]] surj_fn[OF bij_is_surj[OF assms]]])

lemma inv_fn_o_fn_is_id:
  fixes f::"'a \<Rightarrow> 'a"
  assumes "bij f"
  shows "((inv f)^^n) o (f^^n) = (\<lambda>x. x)"
proof -
  have "((inv f)^^n)((f^^n) x) = x" for x n
  proof (induction n)
    case (Suc n)
    have *: "(inv f) (f y) = y" for y
      by (simp add: assms bij_is_inj)
    have "(inv f ^^ Suc n) ((f ^^ Suc n) x) = (inv f^^n) (inv f (f ((f^^n) x)))"
      by (simp add: funpow_swap1)
    also have "... = (inv f^^n) ((f^^n) x)"
      using * by auto
    also have "... = x" using Suc.IH by auto
    finally show ?case by simp
  qed (auto)
  then show ?thesis unfolding o_def by blast
qed

lemma fn_o_inv_fn_is_id:
  fixes f::"'a \<Rightarrow> 'a"
  assumes "bij f"
  shows "(f^^n) o ((inv f)^^n) = (\<lambda>x. x)"
proof -
  have "(f^^n) (((inv f)^^n) x) = x" for x n
  proof (induction n)
    case (Suc n)
    have *: "f(inv f y) = y" for y
      using assms by (meson bij_inv_eq_iff)
    have "(f ^^ Suc n) ((inv f ^^ Suc n) x) = (f^^n) (f (inv f ((inv f^^n) x)))"
      by (simp add: funpow_swap1)
    also have "... = (f^^n) ((inv f^^n) x)"
      using * by auto
    also have "... = x" using Suc.IH by auto
    finally show ?case by simp
  qed (auto)
  then show ?thesis unfolding o_def by blast
qed

lemma inv_fn:
  fixes f::"'a \<Rightarrow> 'a"
  assumes "bij f"
  shows "inv (f^^n) = ((inv f)^^n)"
proof -
  have "inv (f^^n) x = ((inv f)^^n) x" for x
  apply (rule inv_into_f_eq, auto simp add: inj_fn[OF bij_is_inj[OF assms]])
  using fn_o_inv_fn_is_id[OF assms, of n] by (metis comp_apply)
  then show ?thesis by auto
qed


subsection {*Complete-lattices.thy*}

text {* We improve \verb+mono_Inf+ (in \verb+Complete_lattices.thy+) under a bijection assumption*}

lemma mono_inv:
  fixes f::"'a::linorder \<Rightarrow> 'b::linorder"
  assumes "mono f" "bij f"
  shows "mono (inv f)"
proof
  fix x y::'b assume "x \<le> y"
  then show "inv f x \<le> inv f y"
    by (metis (no_types, lifting) assms bij_is_surj eq_iff le_cases mono_def surj_f_inv_f)
qed

lemma mono_bij_Inf:
  fixes f :: "'a::complete_linorder \<Rightarrow> 'b::complete_linorder"
  assumes "mono f" "bij f"
  shows "f (Inf A) = Inf (f`A)"
proof -
  have "(inv f) (Inf (f`A)) \<le> Inf ((inv f)`(f`A))"
    using mono_Inf[OF mono_inv[OF assms], of "f`A"] by simp
  then have "Inf (f`A) \<le> f (Inf ((inv f)`(f`A)))"
    by (metis (no_types, lifting) assms mono_def bij_inv_eq_iff)
  also have "... = f(Inf A)"
    using assms by (simp add: bij_is_inj)
  finally show ?thesis using mono_Inf[OF assms(1), of A] by auto
qed


subsection {*Topological-spaces.thy*}

lemma open_diagonal_complement:
  "open {(x,y) | x y. x \<noteq> (y::('a::t2_space))}"
proof (rule topological_space_class.openI)
  fix t assume "t \<in> {(x, y) | x y. x \<noteq> (y::'a)}"
  then obtain x y where "t = (x,y)" "x \<noteq> y" by blast
  then obtain U V where *: "open U \<and> open V \<and> x \<in> U \<and> y \<in> V \<and> U \<inter> V = {}"
    by (auto simp add: separation_t2)
  define T where "T = U \<times> V"
  have "open T" using * open_Times T_def by auto
  moreover have "t \<in> T" unfolding T_def using `t = (x,y)` * by auto
  moreover have "T \<subseteq> {(x, y) | x y. x \<noteq> y}" unfolding T_def using * by auto
  ultimately show "\<exists>T. open T \<and> t \<in> T \<and> T \<subseteq> {(x, y) | x y. x \<noteq> y}" by auto
qed

lemma closed_diagonal:
  "closed {y. \<exists> x::('a::t2_space). y = (x,x)}"
proof -
  have "{y. \<exists> x::'a. y = (x,x)} = UNIV - {(x,y) | x y. x \<noteq> y}" by auto
  then show ?thesis using open_diagonal_complement closed_Diff by auto
qed

lemma open_superdiagonal:
  "open {(x,y) | x y. x > (y::'a::{linorder_topology})}"
proof (rule topological_space_class.openI)
  fix t assume "t \<in> {(x, y) | x y. y < (x::'a)}"
  then obtain x y where "t = (x, y)" "x > y" by blast
  show "\<exists>T. open T \<and> t \<in> T \<and> T \<subseteq> {(x, y) | x y. y < x}"
  proof (cases)
    assume "\<exists>z. y < z \<and> z < x"
    then obtain z where z: "y < z \<and> z < x" by blast
    define T where "T = {z<..} \<times> {..<z}"
    have "open T" unfolding T_def by (simp add: open_Times)
    moreover have "t \<in> T" using T_def z `t = (x,y)` by auto
    moreover have "T \<subseteq> {(x, y) | x y. y < x}" unfolding T_def by auto
    ultimately show ?thesis by auto
  next
    assume "\<not>(\<exists>z. y < z \<and> z < x)"
    then have *: "{x ..} = {y<..}" "{..< x} = {..y}"
      using `x > y` apply auto using leI by blast
    define T where "T = {x ..} \<times> {.. y}"
    then have "T = {y<..} \<times> {..< x}" using * by simp
    then have "open T" unfolding T_def by (simp add: open_Times)
    moreover have "t \<in> T" using T_def `t = (x,y)` by auto
    moreover have "T \<subseteq> {(x, y) | x y. y < x}" unfolding T_def using `x > y` by auto
    ultimately show ?thesis by auto
  qed
qed

lemma closed_subdiagonal:
  "closed {(x,y) | x y. x \<le> (y::'a::{linorder_topology})}"
proof -
  have "{(x,y) | x y. x \<le> (y::'a)} = UNIV - {(x,y) | x y. x > (y::'a)}" by auto
  then show ?thesis using open_superdiagonal closed_Diff by auto
qed

lemma open_subdiagonal:
  "open {(x,y) | x y. x < (y::'a::{linorder_topology})}"
proof (rule topological_space_class.openI)
  fix t assume "t \<in> {(x, y) | x y. y > (x::'a)}"
  then obtain x y where "t = (x, y)" "x < y" by blast
  show "\<exists>T. open T \<and> t \<in> T \<and> T \<subseteq> {(x, y) | x y. y > x}"
  proof (cases)
    assume "\<exists>z. y > z \<and> z > x"
    then obtain z where z: "y > z \<and> z > x" by blast
    define T where "T = {..<z} \<times> {z<..}"
    have "open T" unfolding T_def by (simp add: open_Times)
    moreover have "t \<in> T" using T_def z `t = (x,y)` by auto
    moreover have "T \<subseteq> {(x, y) |x y. y > x}" unfolding T_def by auto
    ultimately show ?thesis by auto
  next
    assume "\<not>(\<exists>z. y > z \<and> z > x)"
    then have *: "{..x} = {..<y}" "{x<..} = {y..}"
      using `x < y` apply auto using leI by blast
    define T where "T = {..x} \<times> {y..}"
    then have "T = {..<y} \<times> {x<..}" using * by simp
    then have "open T" unfolding T_def by (simp add: open_Times)
    moreover have "t \<in> T" using T_def `t = (x,y)` by auto
    moreover have "T \<subseteq> {(x, y) |x y. y > x}" unfolding T_def using `x < y` by auto
    ultimately show ?thesis by auto
  qed
qed

lemma closed_superdiagonal:
  "closed {(x,y) | x y. x \<ge> (y::('a::{linorder_topology}))}"
proof -
  have "{(x,y) | x y. x \<ge> (y::'a)} = UNIV - {(x,y) | x y. x < y}" by auto
  then show ?thesis using open_subdiagonal closed_Diff by auto
qed

text {*The next statements come from the same statements for true subsequences*}

lemma eventually_weak_subseq:
  fixes u::"nat \<Rightarrow> nat"
  assumes "(\<lambda>n. real(u n)) \<longlonglongrightarrow> \<infinity>" "eventually P sequentially"
  shows "eventually (\<lambda>n. P (u n)) sequentially"
proof -
  obtain N where *: "\<forall>n\<ge>N. P n" using assms(2) unfolding eventually_sequentially by auto
  obtain M where "\<forall>m\<ge>M. ereal(u m) \<ge> N" using assms(1) by (meson Lim_PInfty)
  then have "\<And>m. m \<ge> M \<Longrightarrow> u m \<ge> N" by auto
  then have "\<And>m. m \<ge> M \<Longrightarrow> P(u m)" using `\<forall>n\<ge>N. P n` by simp
  then show ?thesis unfolding eventually_sequentially by auto
qed

lemma filterlim_weak_subseq:
  fixes u::"nat \<Rightarrow> nat"
  assumes "(\<lambda>n. real(u n)) \<longlonglongrightarrow> \<infinity>"
  shows "LIM n sequentially. u n:> at_top"
unfolding filterlim_iff by (metis assms eventually_weak_subseq)

lemma limit_along_weak_subseq:
  fixes u::"nat \<Rightarrow> nat" and v::"nat \<Rightarrow> _"
  assumes "(\<lambda>n. real(u n)) \<longlonglongrightarrow> \<infinity>" "v \<longlonglongrightarrow> l"
  shows "(\<lambda> n. v(u n)) \<longlonglongrightarrow> l"
using filterlim_compose[of v, OF _ filterlim_weak_subseq] assms by auto


subsection {*Series*}


subsection {*Transcendental.thy*}

text {*In \verb+Transcendental.thy+, the assumptions of the next two lemmas are
$x > 0$ and $y > 0$, while large inequalities are sufficient, with the same proof.*}

lemma powr_divide: "0 \<le> x \<Longrightarrow> 0 \<le> y \<Longrightarrow> (x / y) powr a = (x powr a) / (y powr a)"
  for a b x :: real
  apply (simp add: divide_inverse positive_imp_inverse_positive powr_mult)
  apply (simp add: powr_def exp_minus [symmetric] exp_add [symmetric] ln_inverse)
  done

lemma powr_mult_base: "0 \<le> x \<Longrightarrow>x * x powr y = x powr (1 + y)"
  for x :: real
  by (auto simp: powr_add)


subsection {*Limits*}

text {* The next lemma deserves to exist by itself, as it is so common and useful. Note that it is
not a direct consequence of \verb+tendsto_inverse+, contrary to what might think at first...*}

lemma tendsto_inverse_real [tendsto_intros]:
  fixes u::"_ \<Rightarrow> real"
  assumes "(u \<longlongrightarrow> l) F" "l \<noteq> 0"
  shows "((\<lambda>x. 1/ u x) \<longlongrightarrow> 1/l) F"
by (rule tendsto_divide[OF _ assms, where ?f = "\<lambda>_. 1" and ?a = 1], auto)

text {*The next lemmas are not very natural, but I needed them several times*}

lemma tendsto_shift_1_over_n:
  fixes f::"nat \<Rightarrow> real"
  assumes "(\<lambda>n. f n / n) \<longlonglongrightarrow> l"
  shows "(\<lambda>n. f (n+k) / n) \<longlonglongrightarrow> l"
proof -
  have "(1+k*(1/n))* (f(n+k)/(n+k)) = f(n+k)/n" if "n>0" for n using that by (auto simp add: divide_simps)
  with eventually_mono[OF eventually_gt_at_top[of "0::nat"] this]
  have "eventually (\<lambda>n.(1+k*(1/n))* (f(n+k)/(n+k)) = f(n+k)/n) sequentially"
    by auto
  moreover have "(\<lambda>n. (1+k*(1/n))* (f(n+k)/(n+k))) \<longlonglongrightarrow> (1+real k*0) * l"
    apply (rule tendsto_mult)
    apply (rule tendsto_add, simp, rule tendsto_mult, simp, simp add: lim_1_over_n)
    apply (rule LIMSEQ_ignore_initial_segment[OF assms, of k])
    done
  ultimately show ?thesis using Lim_transform_eventually by auto
qed

lemma tendsto_shift_1_over_n':
  fixes f::"nat \<Rightarrow> real"
  assumes "(\<lambda>n. f n / n) \<longlonglongrightarrow> l"
  shows "(\<lambda>n. f (n-k) / n) \<longlonglongrightarrow> l"
proof -
  have "(1-k*(1/(n+k)))* (f n/ n) = f n/(n+k)" if "n>0" for n using that by (auto simp add: divide_simps)
  with eventually_mono[OF eventually_gt_at_top[of "0::nat"] this]
  have "eventually (\<lambda>n. (1-k*(1/(n+k)))* (f n/ n) = f n/(n+k)) sequentially"
    by auto
  moreover have "(\<lambda>n. (1-k*(1/(n+k)))* (f n/ n)) \<longlonglongrightarrow> (1-real k*0) * l"
    apply (rule tendsto_mult)
    apply (rule tendsto_diff, simp, rule tendsto_mult, simp, rule LIMSEQ_ignore_initial_segment[OF lim_1_over_n, of k])
    apply (simp add: assms)
    done
  ultimately have "(\<lambda>n. f n / (n+k)) \<longlonglongrightarrow> l" using Lim_transform_eventually by auto
  then have a: "(\<lambda>n. f(n-k)/(n-k+k)) \<longlonglongrightarrow> l" using seq_offset_neg by auto

  have "f(n-k)/(n-k+k) = f(n-k)/n" if "n>k" for n
    using that by auto
  with eventually_mono[OF eventually_gt_at_top[of k] this]
  have "eventually (\<lambda>n. f(n-k)/(n-k+k) = f(n-k)/n) sequentially"
    by auto
  with Lim_transform_eventually[OF this a]
  show ?thesis by auto
qed

subsection {*Topology-Euclidean-Space*}

lemma countable_separating_set_linorder1:
  shows "\<exists>B::('a::{linorder_topology, second_countable_topology} set). countable B \<and> (\<forall>x y. x < y \<longrightarrow> (\<exists>b \<in> B. x < b \<and> b \<le> y))"
proof -
  obtain A::"'a set set" where "countable A" "topological_basis A" using ex_countable_basis by auto
  define B1 where "B1 = {(LEAST x. x \<in> U)| U. U \<in> A}"
  then have "countable B1" using `countable A` by (simp add: Setcompr_eq_image)
  define B2 where "B2 = {(SOME x. x \<in> U)| U. U \<in> A}"
  then have "countable B2" using `countable A` by (simp add: Setcompr_eq_image)
  have "\<exists>b \<in> B1 \<union> B2. x < b \<and> b \<le> y" if "x < y" for x y
  proof (cases)
    assume "\<exists>z. x < z \<and> z < y"
    then obtain z where z: "x < z \<and> z < y" by auto
    define U where "U = {x<..<y}"
    then have "open U" by simp
    moreover have "z \<in> U" using z U_def by simp
    ultimately obtain V where "V \<in> A" "z \<in> V" "V \<subseteq> U" using topological_basisE[OF `topological_basis A`] by auto
    define w where "w = (SOME x. x \<in> V)"
    then have "w \<in> V" using `z \<in> V` by (metis someI2)
    then have "x < w \<and> w \<le> y" using `w \<in> V` `V \<subseteq> U` U_def by fastforce
    moreover have "w \<in> B1 \<union> B2" using w_def B2_def `V \<in> A` by auto
    ultimately show ?thesis by auto
  next
    assume "\<not>(\<exists>z. x < z \<and> z < y)"
    then have *: "\<And>z. z > x \<Longrightarrow> z \<ge> y" by auto
    define U where "U = {x<..}"
    then have "open U" by simp
    moreover have "y \<in> U" using `x < y` U_def by simp
    ultimately obtain "V" where "V \<in> A" "y \<in> V" "V \<subseteq> U" using topological_basisE[OF `topological_basis A`] by auto
    have "U = {y..}" unfolding U_def using * `x < y` by auto
    then have "V \<subseteq> {y..}" using `V \<subseteq> U` by simp
    then have "(LEAST w. w \<in> V) = y" using `y \<in> V` by (meson Least_equality atLeast_iff subsetCE)
    then have "y \<in> B1 \<union> B2" using `V \<in> A` B1_def by auto
    moreover have "x < y \<and> y \<le> y" using `x < y` by simp
    ultimately show ?thesis by auto
  qed
  moreover have "countable (B1 \<union> B2)" using `countable B1` `countable B2` by simp
  ultimately show ?thesis by auto
qed

lemma countable_separating_set_linorder2:
  shows "\<exists>B::('a::{linorder_topology, second_countable_topology} set). countable B \<and> (\<forall>x y. x < y \<longrightarrow> (\<exists>b \<in> B. x \<le> b \<and> b < y))"
proof -
  obtain A::"'a set set" where "countable A" "topological_basis A" using ex_countable_basis by auto
  define B1 where "B1 = {(GREATEST x. x \<in> U) | U. U \<in> A}"
  then have "countable B1" using `countable A` by (simp add: Setcompr_eq_image)
  define B2 where "B2 = {(SOME x. x \<in> U)| U. U \<in> A}"
  then have "countable B2" using `countable A` by (simp add: Setcompr_eq_image)
  have "\<exists>b \<in> B1 \<union> B2. x \<le> b \<and> b < y" if "x < y" for x y
  proof (cases)
    assume "\<exists>z. x < z \<and> z < y"
    then obtain z where z: "x < z \<and> z < y" by auto
    define U where "U = {x<..<y}"
    then have "open U" by simp
    moreover have "z \<in> U" using z U_def by simp
    ultimately obtain "V" where "V \<in> A" "z \<in> V" "V \<subseteq> U" using topological_basisE[OF `topological_basis A`] by auto
    define w where "w = (SOME x. x \<in> V)"
    then have "w \<in> V" using `z \<in> V` by (metis someI2)
    then have "x \<le> w \<and> w < y" using `w \<in> V` `V \<subseteq> U` U_def by fastforce
    moreover have "w \<in> B1 \<union> B2" using w_def B2_def `V \<in> A` by auto
    ultimately show ?thesis by auto
  next
    assume "\<not>(\<exists>z. x < z \<and> z < y)"
    then have *: "\<And>z. z < y \<Longrightarrow> z \<le> x" using leI by blast
    define U where "U = {..<y}"
    then have "open U" by simp
    moreover have "x \<in> U" using `x < y` U_def by simp
    ultimately obtain "V" where "V \<in> A" "x \<in> V" "V \<subseteq> U" using topological_basisE[OF `topological_basis A`] by auto
    have "U = {..x}" unfolding U_def using * `x < y` by auto
    then have "V \<subseteq> {..x}" using `V \<subseteq> U` by simp
    then have "(GREATEST x. x \<in> V) = x" using `x \<in> V` by (meson Greatest_equality atMost_iff subsetCE)
    then have "x \<in> B1 \<union> B2" using `V \<in> A` B1_def by auto
    moreover have "x \<le> x \<and> x < y" using `x < y` by simp
    ultimately show ?thesis by auto
  qed
  moreover have "countable (B1 \<union> B2)" using `countable B1` `countable B2` by simp
  ultimately show ?thesis by auto
qed

lemma countable_separating_set_dense_linorder:
  shows "\<exists>B::('a::{linorder_topology, dense_linorder, second_countable_topology} set). countable B \<and> (\<forall>x y. x < y \<longrightarrow> (\<exists>b \<in> B. x < b \<and> b < y))"
proof -
  obtain B::"'a set" where B: "countable B" "\<And>x y. x < y \<Longrightarrow> (\<exists>b \<in> B. x < b \<and> b \<le> y)"
    using countable_separating_set_linorder1 by auto
  have "\<exists>b \<in> B. x < b \<and> b < y" if "x < y" for x y
  proof -
    obtain z where "x < z" "z < y" using `x < y` dense by blast
    then obtain b where "b \<in> B" "x < b \<and> b \<le> z" using B(2) by auto
    then have "x < b \<and> b < y" using `z < y` by auto
    then show ?thesis using `b \<in> B` by auto
  qed
  then show ?thesis using B(1) by auto
qed

lemma Inf_as_limit:
  fixes A::"'a::{linorder_topology, first_countable_topology, complete_linorder} set"
  assumes "A \<noteq> {}"
  shows "\<exists>u. (\<forall>n. u n \<in> A) \<and> u \<longlonglongrightarrow> Inf A"
proof (cases "Inf A \<in> A")
  case True
  show ?thesis
    by (rule exI[of _ "\<lambda>n. Inf A"], auto simp add: True)
next
  case False
  obtain y where "y \<in> A" using assms by auto
  then have "Inf A < y" using False Inf_lower less_le by auto
  obtain F :: "nat \<Rightarrow> 'a set" where F: "\<And>i. open (F i)" "\<And>i. Inf A \<in> F i"
                                       "\<And>u. (\<forall>n. u n \<in> F n) \<Longrightarrow> u \<longlonglongrightarrow> Inf A"
    by (metis first_countable_topology_class.countable_basis)
  define u where "u = (\<lambda>n. SOME z. z \<in> F n \<and> z \<in> A)"
  have "\<exists>z. z \<in> U \<and> z \<in> A" if "Inf A \<in> U" "open U" for U
  proof -
    obtain b where "b > Inf A" "{Inf A ..<b} \<subseteq> U"
      using open_right[OF `open U` `Inf A \<in> U` `Inf A < y`] by auto
    obtain z where "z < b" "z \<in> A"
      using `Inf A < b` Inf_less_iff by auto
    then have "z \<in> {Inf A ..<b}"
      by (simp add: Inf_lower)
    then show ?thesis using `z \<in> A` `{Inf A ..<b} \<subseteq> U` by auto
  qed
  then have *: "u n \<in> F n \<and> u n \<in> A" for n
    using `Inf A \<in> F n` `open (F n)` unfolding u_def by (metis (no_types, lifting) someI_ex)
  then have "u \<longlonglongrightarrow> Inf A" using F(3) by simp
  then show ?thesis using * by auto
qed

text {*A (more usable) variation around \verb+continuous_on_closure_sequentially+. The assumption
that the spaces are metric spaces is definitely too strong, but sufficient for most applications.*}

lemma continuous_on_closure_sequentially':
  fixes f::"'a::metric_space \<Rightarrow> 'b::metric_space"
  assumes "continuous_on (closure C) f"
          "\<And>(n::nat). u n \<in> C"
          "u \<longlonglongrightarrow> l"
  shows "(\<lambda>n. f (u n)) \<longlonglongrightarrow> f l"
proof -
  have "l \<in> closure C" unfolding closure_sequential using assms by auto
  then show ?thesis
    using `continuous_on (closure C) f` unfolding comp_def continuous_on_closure_sequentially
    using assms by auto
qed


subsection {*Convexity*}

lemma convex_on_mean_ineq:
  fixes f::"real \<Rightarrow> real"
  assumes "convex_on A f" "x \<in> A" "y \<in> A"
  shows "f ((x+y)/2) \<le> (f x + f y) / 2"
using convex_onD[OF assms(1), of "1/2" x y] using assms by (auto simp add: divide_simps)

lemma convex_on_closure:
  assumes "convex (C::'a::real_normed_vector set)"
          "convex_on C f"
          "continuous_on (closure C) f"
  shows "convex_on (closure C) f"
proof (rule convex_onI)
  fix x y::'a and t::real
  assume "x \<in> closure C" "y \<in> closure C" "0 < t" "t < 1"
  obtain u v::"nat \<Rightarrow> 'a" where *: "\<And>n. u n \<in> C" "u \<longlonglongrightarrow> x"
                                   "\<And>n. v n \<in> C" "v \<longlonglongrightarrow> y"
    using `x \<in> closure C` `y \<in> closure C` unfolding closure_sequential by blast
  define w where "w = (\<lambda>n. (1-t) *\<^sub>R (u n) + t *\<^sub>R (v n))"
  have "w n \<in> C" for n
    using `0 < t` `t< 1` convexD[OF `convex C` *(1)[of n] *(3)[of n]] unfolding w_def by auto
  have "w \<longlonglongrightarrow> ((1-t) *\<^sub>R x + t *\<^sub>R y)"
    unfolding w_def using *(2) *(4) by (auto intro!: tendsto_intros)

  have *: "f(w n) \<le> (1-t) * f(u n) + t * f (v n)" for n
    using *(1) *(3) `convex_on C f` `0<t` `t<1` less_imp_le unfolding w_def
    convex_on_alt[OF assms(1)] by (simp add: add.commute)
  have i: "(\<lambda>n. f (w n)) \<longlonglongrightarrow> f ((1-t) *\<^sub>R x + t *\<^sub>R y)"
    by (rule continuous_on_closure_sequentially'[OF assms(3) `\<And>n. w n \<in> C` `w \<longlonglongrightarrow> ((1-t) *\<^sub>R x + t *\<^sub>R y)`])
  have ii: "(\<lambda>n. (1-t) * f(u n) + t * f (v n)) \<longlonglongrightarrow> (1-t) * f x + t * f y"
    apply (auto intro!: tendsto_intros)
    apply (rule continuous_on_closure_sequentially'[OF assms(3) `\<And>n. u n \<in> C` `u \<longlonglongrightarrow> x`])
    apply (rule continuous_on_closure_sequentially'[OF assms(3) `\<And>n. v n \<in> C` `v \<longlonglongrightarrow> y`])
    done
  show "f ((1 - t) *\<^sub>R x + t *\<^sub>R y) \<le> (1 - t) * f x + t * f y"
    apply (rule LIMSEQ_le[OF i ii]) using * by auto
qed

lemma convex_on_norm:
  "convex_on UNIV (\<lambda>(x::'a::real_normed_vector). norm x)"
using convex_on_dist[of UNIV "0::'a"] by auto

lemma continuous_abs_powr [continuous_intros]:
  assumes "p > 0"
  shows "continuous_on UNIV (\<lambda>(x::real). \<bar>x\<bar> powr p)"
apply (rule continuous_on_powr') using assms by (auto intro: continuous_intros)

lemma continuous_mult_sgn [continuous_intros]:
  fixes f::"real \<Rightarrow> real"
  assumes "continuous_on UNIV f" "f 0 = 0"
  shows "continuous_on UNIV (\<lambda>x. sgn x * f x)"
proof -
  have *: "continuous_on {0..} (\<lambda>x. sgn x * f x)"
    apply (subst continuous_on_cong[of "{0..}" "{0..}" _ f], auto simp add: sgn_real_def assms(2))
    by (rule continuous_on_subset[OF assms(1)], auto)
  have **: "continuous_on {..0} (\<lambda>x. sgn x * f x)"
    apply (subst continuous_on_cong[of "{..0}" "{..0}" _ "\<lambda>x. -f x"], auto simp add: sgn_real_def assms(2))
    by (rule continuous_on_subset[of UNIV], auto simp add: assms intro!: continuous_intros)
  show ?thesis
    using continuous_on_closed_Un[OF _ _ * **] apply (auto intro: continuous_intros)
    using continuous_on_subset by fastforce
qed

lemma DERIV_abs_powr [derivative_intros]:
  assumes "p > (1::real)"
  shows "DERIV (\<lambda>x. \<bar>x\<bar> powr p) x :> p * sgn x * \<bar>x\<bar> powr (p - 1)"
proof -
  consider "x = 0" | "x>0" | "x < 0" by linarith
  then show ?thesis
  proof (cases)
    case 1
    have "continuous_on UNIV (\<lambda>x. sgn x * \<bar>x\<bar> powr (p - 1))"
      by (auto simp add: assms intro!:continuous_intros)
    then have "(\<lambda>h. sgn h * \<bar>h\<bar> powr (p-1)) \<midarrow>0\<rightarrow> (\<lambda>h. sgn h * \<bar>h\<bar> powr (p-1)) 0"
      using continuous_on_def by blast
    moreover have "\<bar>h\<bar> powr p / h = sgn h * \<bar>h\<bar> powr (p-1)" for h
    proof -
      have "\<bar>h\<bar> powr p / h = sgn h * \<bar>h\<bar> powr p / \<bar>h\<bar>"
        by (auto simp add: algebra_simps divide_simps sgn_real_def)
      also have "... = sgn h * \<bar>h\<bar> powr (p-1)"
        using assms apply (cases "h=0") apply (auto)
        by (metis abs_ge_zero powr_divide2 powr_one_gt_zero_iff times_divide_eq_right)
      finally show ?thesis by simp
    qed
    ultimately have "(\<lambda>h. \<bar>h\<bar> powr p / h) \<midarrow>0\<rightarrow> 0" by auto
    then show ?thesis unfolding DERIV_def by (auto simp add: `x=0`)
  next
    case 2
    have *: "\<forall>\<^sub>F y in nhds x. \<bar>y\<bar> powr p = y powr p"
      unfolding eventually_nhds apply (rule exI[of _ "{0<..}"]) using `x > 0` by auto
    show ?thesis
      apply (subst DERIV_cong_ev[of _ x _ "(\<lambda>x. x powr p)" _ "p * x powr (p-1)"])
      using `x > 0` by (auto simp add: * has_real_derivative_powr)
  next
    case 3
    have *: "\<forall>\<^sub>F y in nhds x. \<bar>y\<bar> powr p = (-y) powr p"
      unfolding eventually_nhds apply (rule exI[of _ "{..<0}"]) using `x < 0` by auto
    show ?thesis
      apply (subst DERIV_cong_ev[of _ x _ "(\<lambda>x. (-x) powr p)" _ "p * (- x) powr (p - real 1) * - 1"])
      using `x < 0` apply (simp, simp add: *, simp)
      apply (rule DERIV_fun_powr[of "\<lambda>y. -y" "-1" "x" p]) using `x < 0` by (auto simp add: derivative_intros)
  qed
qed

lemma convex_abs_powr:
  assumes "p \<ge> 1"
  shows "convex_on UNIV (\<lambda>x::real. \<bar>x\<bar> powr p)"
proof (cases "p=1")
  case True
  have "convex_on UNIV (\<lambda>x::real. norm x)"
    by (rule convex_on_norm)
  moreover have "\<bar>x\<bar> powr p = norm x" for x using True by auto
  ultimately show ?thesis by simp
next
  case False
  then have "p > 1" using assms by auto
  define g where "g = (\<lambda>x::real. p * sgn x * \<bar>x\<bar> powr (p - 1))"
  have *: "DERIV (\<lambda>x. \<bar>x\<bar> powr p) x :> g x" for x
    unfolding g_def using `p>1` by (auto intro!:derivative_intros)
  have **: "g x \<le> g y" if "x \<le> y" for x y
  proof -
    consider "x \<ge> 0 \<and> y \<ge> 0" | "x \<le> 0 \<and> y \<le> 0" | "x < 0 \<and> y > 0" using `x \<le> y` by linarith
    then show ?thesis
    proof (cases)
      case 1
      then show ?thesis unfolding g_def sgn_real_def using `p>1` `x \<le> y` by (auto simp add: powr_mono2)
    next
      case 2
      then show ?thesis unfolding g_def sgn_real_def using `p>1` `x \<le> y` by (auto simp add: powr_mono2)
    next
      case 3
      then have "g x \<le> 0" "0 \<le> g y" unfolding g_def using `p > 1` by auto
      then show ?thesis by simp
    qed
  qed
  show ?thesis
    apply (rule convex_on_realI[of _ _ g]) using * ** by auto
qed

lemma convex_powr:
  assumes "p \<ge> 1"
  shows "convex_on {0..} (\<lambda>x::real. x powr p)"
proof -
  have "convex_on {0..} (\<lambda>x::real. \<bar>x\<bar> powr p)"
    using convex_abs_powr[OF `p \<ge> 1`] convex_on_subset by auto
  moreover have "\<bar>x\<bar> powr p = x powr p" if "x \<in> {0..}" for x using that by auto
  ultimately show ?thesis by (simp add: convex_on_def)
qed

lemma convex_powr':
  assumes "p > 0" "p \<le> 1"
  shows "convex_on {0..} (\<lambda>x::real. - (x powr p))"
proof -
  have "convex_on {0<..} (\<lambda>x::real. - (x powr p))"
    apply (rule convex_on_realI[of _ _ "\<lambda>x. -p * x powr (p-1)"])
    apply (auto intro!:derivative_intros simp add: has_real_derivative_powr)
    using `p > 0` `p \<le> 1` by (auto simp add: algebra_simps divide_simps powr_mono2')
  moreover have "continuous_on {0..} (\<lambda>x::real. - (x powr p))"
    by (rule continuous_on_minus, rule continuous_on_powr', auto simp add: `p > 0` intro!: continuous_intros)
  moreover have "{(0::real)..} = closure {0<..}" "convex {(0::real)<..}" by auto
  ultimately show ?thesis using convex_on_closure by metis
qed

lemma convex_fx_plus_fy_ineq:
  fixes f::"real \<Rightarrow> real"
  assumes "convex_on {0..} f"
          "x \<ge> 0" "y \<ge> 0" "f 0 = 0"
  shows "f x + f y \<le> f (x+y)"
proof -
  have *: "f a + f b \<le> f (a+b)" if "a \<ge> 0" "b \<ge> a" for a b
  proof (cases "a = 0")
    case False
    then have "a > 0" "b > 0" using `b \<ge> a` `a \<ge> 0` by auto
    have "(f 0 - f a) / (0 - a) \<le> (f 0 - f (a+b))/ (0 - (a+b))"
      apply (rule convex_on_diff[OF `convex_on {0..} f`]) using `a > 0` `b > 0` by auto
    also have "... \<le> (f b - f (a+b)) / (b - (a+b))"
      apply (rule convex_on_diff[OF `convex_on {0..} f`]) using `a > 0` `b > 0` by auto
    finally show ?thesis
      using `a > 0` `b > 0` `f 0 = 0` by (auto simp add: divide_simps algebra_simps)
  qed (simp add: `f 0 = 0`)
  then show ?thesis
    using `x \<ge> 0` `y \<ge> 0` by (metis add.commute le_less not_le)
qed

lemma x_plus_y_p_le_xp_plus_yp:
  fixes p x y::real
  assumes "p > 0" "p \<le> 1" "x \<ge> 0" "y \<ge> 0"
  shows "(x + y) powr p \<le> x powr p + y powr p"
using convex_fx_plus_fy_ineq[OF convex_powr'[OF `p > 0` `p \<le> 1`] `x \<ge> 0` `y \<ge> 0`] by auto


subsection {*Liminf-Limsup.thy*}

lemma limsup_shift:
  "limsup (\<lambda>n. u (n+1)) = limsup u"
proof -
  have "(SUP m:{n+1..}. u m) = (SUP m:{n..}. u (m + 1))" for n
    apply (rule SUP_eq) using Suc_le_D by auto
  then have a: "(INF n. SUP m:{n..}. u (m + 1)) = (INF n. (SUP m:{n+1..}. u m))" by auto
  have b: "(INF n. (SUP m:{n+1..}. u m)) = (INF n:{1..}. (SUP m:{n..}. u m))"
    apply (rule INF_eq) using Suc_le_D by auto
  have "(INF n:{1..}. v n) = (INF n. v n)" if "decseq v" for v::"nat \<Rightarrow> 'a"
    apply (rule INF_eq) using `decseq v` decseq_Suc_iff by auto
  moreover have "decseq (\<lambda>n. (SUP m:{n..}. u m))" by (simp add: SUP_subset_mono decseq_def)
  ultimately have c: "(INF n:{1..}. (SUP m:{n..}. u m)) = (INF n. (SUP m:{n..}. u m))" by simp
  have "(INF n. SUPREMUM {n..} u) = (INF n. SUP m:{n..}. u (m + 1))" using a b c by simp
  then show ?thesis by (auto cong: limsup_INF_SUP)
qed

lemma limsup_shift_k:
  "limsup (\<lambda>n. u (n+k)) = limsup u"
proof (induction k)
  case (Suc k)
  have "limsup (\<lambda>n. u (n+k+1)) = limsup (\<lambda>n. u (n+k))" using limsup_shift[where ?u="\<lambda>n. u(n+k)"] by simp
  then show ?case using Suc.IH by simp
qed (auto)

lemma liminf_shift:
  "liminf (\<lambda>n. u (n+1)) = liminf u"
proof -
  have "(INF m:{n+1..}. u m) = (INF m:{n..}. u (m + 1))" for n
    apply (rule INF_eq) using Suc_le_D by (auto)
  then have a: "(SUP n. INF m:{n..}. u (m + 1)) = (SUP n. (INF m:{n+1..}. u m))" by auto
  have b: "(SUP n. (INF m:{n+1..}. u m)) = (SUP n:{1..}. (INF m:{n..}. u m))"
    apply (rule SUP_eq) using Suc_le_D by (auto)
  have "(SUP n:{1..}. v n) = (SUP n. v n)" if "incseq v" for v::"nat \<Rightarrow> 'a"
    apply (rule SUP_eq) using `incseq v` incseq_Suc_iff by auto
  moreover have "incseq (\<lambda>n. (INF m:{n..}. u m))" by (simp add: INF_superset_mono mono_def)
  ultimately have c: "(SUP n:{1..}. (INF m:{n..}. u m)) = (SUP n. (INF m:{n..}. u m))" by simp
  have "(SUP n. INFIMUM {n..} u) = (SUP n. INF m:{n..}. u (m + 1))" using a b c by simp
  then show ?thesis by (auto cong: liminf_SUP_INF)
qed

lemma liminf_shift_k:
  "liminf (\<lambda>n. u (n+k)) = liminf u"
proof (induction k)
  case (Suc k)
  have "liminf (\<lambda>n. u (n+k+1)) = liminf (\<lambda>n. u (n+k))" using liminf_shift[where ?u="\<lambda>n. u(n+k)"] by simp
  then show ?case using Suc.IH by simp
qed (auto)

lemma Limsup_obtain:
  fixes u::"_ \<Rightarrow> 'a :: complete_linorder"
  assumes "Limsup F u > c"
  shows "\<exists>i. u i > c"
proof -
  have "(INF P:{P. eventually P F}. SUP x:{x. P x}. u x) > c" using assms by (simp add: Limsup_def)
  then show ?thesis by (metis eventually_True mem_Collect_eq less_INF_D less_SUP_iff)
qed

lemma Liminf_obtain:
  fixes u::"_ \<Rightarrow> 'a :: complete_linorder"
  assumes "Liminf F u < c"
  shows "\<exists>i. u i < c"
proof -
  have "(SUP P:{P. eventually P F}. INF x:{x. P x}. u x) < c" using assms by (simp add: Liminf_def)
  then show ?thesis by (metis eventually_True mem_Collect_eq SUP_lessD INF_less_iff)
qed

lemma Limsup_eventually_bounded:
  assumes "eventually (\<lambda>x. u x \<le> l) F"
  shows "Limsup F u \<le> l"
unfolding Limsup_def using assms by (simp add: INF_lower2 SUP_le_iff)

lemma Liminf_eventually_bounded:
  assumes "eventually (\<lambda>x. u x \<ge> l) F"
  shows "Liminf F u \<ge> l"
unfolding Liminf_def using assms by (simp add: SUP_upper2 le_INF_iff)

text {* The next lemma is extremely useful, as it often makes it possible to reduce statements
about limsups to statements about limits.*}

lemma limsup_subseq_lim:
  fixes u::"nat \<Rightarrow> 'a :: {complete_linorder, linorder_topology}"
  shows "\<exists>r. subseq r \<and> (u o r) \<longlonglongrightarrow> limsup u"
proof (cases)
  assume "\<forall>n. \<exists>p>n. \<forall>m\<ge>p. u m \<le> u p"
  then have "\<exists>r. \<forall>n. (\<forall>m\<ge>r n. u m \<le> u (r n)) \<and> r n < r (Suc n)"
    by (intro dependent_nat_choice) (auto simp: conj_commute)
  then obtain r where "subseq r" and mono: "\<And>n m. r n \<le> m \<Longrightarrow> u m \<le> u (r n)"
    by (auto simp: subseq_Suc_iff)
  define umax where "umax = (\<lambda>n. (SUP m:{n..}. u m))"
  have "decseq umax" unfolding umax_def by (simp add: SUP_subset_mono antimono_def)
  then have "umax \<longlonglongrightarrow> limsup u" unfolding umax_def by (metis LIMSEQ_INF limsup_INF_SUP)
  then have *: "(umax o r) \<longlonglongrightarrow> limsup u" by (simp add: LIMSEQ_subseq_LIMSEQ `subseq r`)
  have "\<And>n. umax(r n) = u(r n)" unfolding umax_def using mono
    by (metis SUP_le_iff antisym atLeast_def mem_Collect_eq order_refl)
  then have "umax o r = u o r" unfolding o_def by simp
  then have "(u o r) \<longlonglongrightarrow> limsup u" using * by simp
  then show ?thesis using `subseq r` by blast
next
  assume "\<not> (\<forall>n. \<exists>p>n. (\<forall>m\<ge>p. u m \<le> u p))"
  then obtain N where N: "\<And>p. p > N \<Longrightarrow> \<exists>m>p. u p < u m" by (force simp: not_le le_less)
  have "\<exists>r. \<forall>n. N < r n \<and> r n < r (Suc n) \<and> (\<forall>i\<in> {N<..r (Suc n)}. u i \<le> u (r (Suc n)))"
  proof (rule dependent_nat_choice)
    fix x assume "N < x"
    then have a: "finite {N<..x}" "{N<..x} \<noteq> {}" by simp_all
    have "Max {u i |i. i \<in> {N<..x}} \<in> {u i |i. i \<in> {N<..x}}" apply (rule Max_in) using a by (auto)
    then obtain p where "p \<in> {N<..x}" and upmax: "u p = Max{u i |i. i \<in> {N<..x}}" by auto
    define U where "U = {m. m > p \<and> u p < u m}"
    have "U \<noteq> {}" unfolding U_def using N[of p] `p \<in> {N<..x}` by auto
    define y where "y = Inf U"
    then have "y \<in> U" using `U \<noteq> {}` by (simp add: Inf_nat_def1)
    have a: "\<And>i. i \<in> {N<..x} \<Longrightarrow> u i \<le> u p"
    proof -
      fix i assume "i \<in> {N<..x}"
      then have "u i \<in> {u i |i. i \<in> {N<..x}}" by blast
      then show "u i \<le> u p" using upmax by simp
    qed
    moreover have "u p < u y" using `y \<in> U` U_def by auto
    ultimately have "y \<notin> {N<..x}" using not_le by blast
    moreover have "y > N" using `y \<in> U` U_def `p \<in> {N<..x}` by auto
    ultimately have "y > x" by auto

    have "\<And>i. i \<in> {N<..y} \<Longrightarrow> u i \<le> u y"
    proof -
      fix i assume "i \<in> {N<..y}" show "u i \<le> u y"
      proof (cases)
        assume "i = y"
        then show ?thesis by simp
      next
        assume "\<not>(i=y)"
        then have i:"i \<in> {N<..<y}" using `i \<in> {N<..y}` by simp
        have "u i \<le> u p"
        proof (cases)
          assume "i \<le> x"
          then have "i \<in> {N<..x}" using i by simp
          then show ?thesis using a by simp
        next
          assume "\<not>(i \<le> x)"
          then have "i > x" by simp
          then have *: "i > p" using `p \<in> {N<..x}` by simp
          have "i < Inf U" using i y_def by simp
          then have "i \<notin> U" using Inf_nat_def not_less_Least by auto
          then show ?thesis using U_def * by auto
        qed
        then show "u i \<le> u y" using `u p < u y` by auto
      qed
    qed
    then have "N < y \<and> x < y \<and> (\<forall>i\<in>{N<..y}. u i \<le> u y)" using `y > x` `y > N` by auto
    then show "\<exists>y>N. x < y \<and> (\<forall>i\<in>{N<..y}. u i \<le> u y)" by auto
  qed (auto)
  then obtain r where r: "\<forall>n. N < r n \<and> r n < r (Suc n) \<and> (\<forall>i\<in> {N<..r (Suc n)}. u i \<le> u (r (Suc n)))" by auto
  have "subseq r" using r by (auto simp: subseq_Suc_iff)
  have "incseq (u o r)" unfolding o_def using r by (simp add: incseq_SucI order.strict_implies_order)
  then have "(u o r) \<longlonglongrightarrow> (SUP n. (u o r) n)" using LIMSEQ_SUP by blast
  then have "limsup (u o r) = (SUP n. (u o r) n)" by (simp add: lim_imp_Limsup)
  moreover have "limsup (u o r) \<le> limsup u" using `subseq r` by (simp add: limsup_subseq_mono)
  ultimately have "(SUP n. (u o r) n) \<le> limsup u" by simp

  {
    fix i assume i: "i \<in> {N<..}"
    obtain n where "i < r (Suc n)" using `subseq r` using Suc_le_eq seq_suble by blast
    then have "i \<in> {N<..r(Suc n)}" using i by simp
    then have "u i \<le> u (r(Suc n))" using r by simp
    then have "u i \<le> (SUP n. (u o r) n)" unfolding o_def by (meson SUP_upper2 UNIV_I)
  }
  then have "(SUP i:{N<..}. u i) \<le> (SUP n. (u o r) n)" using SUP_least by blast
  then have "limsup u \<le> (SUP n. (u o r) n)" unfolding Limsup_def
    by (metis (mono_tags, lifting) INF_lower2 atLeast_Suc_greaterThan atLeast_def eventually_ge_at_top mem_Collect_eq)
  then have "limsup u = (SUP n. (u o r) n)" using `(SUP n. (u o r) n) \<le> limsup u` by simp
  then have "(u o r) \<longlonglongrightarrow> limsup u" using `(u o r) \<longlonglongrightarrow> (SUP n. (u o r) n)` by simp
  then show ?thesis using `subseq r` by auto
qed

lemma liminf_subseq_lim:
  fixes u::"nat \<Rightarrow> 'a :: {complete_linorder, linorder_topology}"
  shows "\<exists>r. subseq r \<and> (u o r) \<longlonglongrightarrow> liminf u"
proof (cases)
  assume "\<forall>n. \<exists>p>n. \<forall>m\<ge>p. u m \<ge> u p"
  then have "\<exists>r. \<forall>n. (\<forall>m\<ge>r n. u m \<ge> u (r n)) \<and> r n < r (Suc n)"
    by (intro dependent_nat_choice) (auto simp: conj_commute)
  then obtain r where "subseq r" and mono: "\<And>n m. r n \<le> m \<Longrightarrow> u m \<ge> u (r n)"
    by (auto simp: subseq_Suc_iff)
  define umin where "umin = (\<lambda>n. (INF m:{n..}. u m))"
  have "incseq umin" unfolding umin_def by (simp add: INF_superset_mono incseq_def)
  then have "umin \<longlonglongrightarrow> liminf u" unfolding umin_def by (metis LIMSEQ_SUP liminf_SUP_INF)
  then have *: "(umin o r) \<longlonglongrightarrow> liminf u" by (simp add: LIMSEQ_subseq_LIMSEQ `subseq r`)
  have "\<And>n. umin(r n) = u(r n)" unfolding umin_def using mono
    by (metis le_INF_iff antisym atLeast_def mem_Collect_eq order_refl)
  then have "umin o r = u o r" unfolding o_def by simp
  then have "(u o r) \<longlonglongrightarrow> liminf u" using * by simp
  then show ?thesis using `subseq r` by blast
next
  assume "\<not> (\<forall>n. \<exists>p>n. (\<forall>m\<ge>p. u m \<ge> u p))"
  then obtain N where N: "\<And>p. p > N \<Longrightarrow> \<exists>m>p. u p > u m" by (force simp: not_le le_less)
  have "\<exists>r. \<forall>n. N < r n \<and> r n < r (Suc n) \<and> (\<forall>i\<in> {N<..r (Suc n)}. u i \<ge> u (r (Suc n)))"
  proof (rule dependent_nat_choice)
    fix x assume "N < x"
    then have a: "finite {N<..x}" "{N<..x} \<noteq> {}" by simp_all
    have "Min {u i |i. i \<in> {N<..x}} \<in> {u i |i. i \<in> {N<..x}}" apply (rule Min_in) using a by (auto)
    then obtain p where "p \<in> {N<..x}" and upmin: "u p = Min{u i |i. i \<in> {N<..x}}" by auto
    define U where "U = {m. m > p \<and> u p > u m}"
    have "U \<noteq> {}" unfolding U_def using N[of p] `p \<in> {N<..x}` by auto
    define y where "y = Inf U"
    then have "y \<in> U" using `U \<noteq> {}` by (simp add: Inf_nat_def1)
    have a: "\<And>i. i \<in> {N<..x} \<Longrightarrow> u i \<ge> u p"
    proof -
      fix i assume "i \<in> {N<..x}"
      then have "u i \<in> {u i |i. i \<in> {N<..x}}" by blast
      then show "u i \<ge> u p" using upmin by simp
    qed
    moreover have "u p > u y" using `y \<in> U` U_def by auto
    ultimately have "y \<notin> {N<..x}" using not_le by blast
    moreover have "y > N" using `y \<in> U` U_def `p \<in> {N<..x}` by auto
    ultimately have "y > x" by auto

    have "\<And>i. i \<in> {N<..y} \<Longrightarrow> u i \<ge> u y"
    proof -
      fix i assume "i \<in> {N<..y}" show "u i \<ge> u y"
      proof (cases)
        assume "i = y"
        then show ?thesis by simp
      next
        assume "\<not>(i=y)"
        then have i:"i \<in> {N<..<y}" using `i \<in> {N<..y}` by simp
        have "u i \<ge> u p"
        proof (cases)
          assume "i \<le> x"
          then have "i \<in> {N<..x}" using i by simp
          then show ?thesis using a by simp
        next
          assume "\<not>(i \<le> x)"
          then have "i > x" by simp
          then have *: "i > p" using `p \<in> {N<..x}` by simp
          have "i < Inf U" using i y_def by simp
          then have "i \<notin> U" using Inf_nat_def not_less_Least by auto
          then show ?thesis using U_def * by auto
        qed
        then show "u i \<ge> u y" using `u p > u y` by auto
      qed
    qed
    then have "N < y \<and> x < y \<and> (\<forall>i\<in>{N<..y}. u i \<ge> u y)" using `y > x` `y > N` by auto
    then show "\<exists>y>N. x < y \<and> (\<forall>i\<in>{N<..y}. u i \<ge> u y)" by auto
  qed (auto)
  then obtain r where r: "\<forall>n. N < r n \<and> r n < r (Suc n) \<and> (\<forall>i\<in> {N<..r (Suc n)}. u i \<ge> u (r (Suc n)))" by auto
  have "subseq r" using r by (auto simp: subseq_Suc_iff)
  have "decseq (u o r)" unfolding o_def using r by (simp add: decseq_SucI order.strict_implies_order)
  then have "(u o r) \<longlonglongrightarrow> (INF n. (u o r) n)" using LIMSEQ_INF by blast
  then have "liminf (u o r) = (INF n. (u o r) n)" by (simp add: lim_imp_Liminf)
  moreover have "liminf (u o r) \<ge> liminf u" using `subseq r` by (simp add: liminf_subseq_mono)
  ultimately have "(INF n. (u o r) n) \<ge> liminf u" by simp

  {
    fix i assume i: "i \<in> {N<..}"
    obtain n where "i < r (Suc n)" using `subseq r` using Suc_le_eq seq_suble by blast
    then have "i \<in> {N<..r(Suc n)}" using i by simp
    then have "u i \<ge> u (r(Suc n))" using r by simp
    then have "u i \<ge> (INF n. (u o r) n)" unfolding o_def by (meson INF_lower2 UNIV_I)
  }
  then have "(INF i:{N<..}. u i) \<ge> (INF n. (u o r) n)" using INF_greatest by blast
  then have "liminf u \<ge> (INF n. (u o r) n)" unfolding Liminf_def
    by (metis (mono_tags, lifting) SUP_upper2 atLeast_Suc_greaterThan atLeast_def eventually_ge_at_top mem_Collect_eq)
  then have "liminf u = (INF n. (u o r) n)" using `(INF n. (u o r) n) \<ge> liminf u` by simp
  then have "(u o r) \<longlonglongrightarrow> liminf u" using `(u o r) \<longlonglongrightarrow> (INF n. (u o r) n)` by simp
  then show ?thesis using `subseq r` by auto
qed


subsection {*Extended-Real.thy*}

text{* The proof of this one is copied from \verb+ereal_add_mono+. *}
lemma ereal_add_strict_mono2:
  fixes a b c d :: ereal
  assumes "a < b"
    and "c < d"
  shows "a + c < b + d"
using assms
apply (cases a)
apply (cases rule: ereal3_cases[of b c d], auto)
apply (cases rule: ereal3_cases[of b c d], auto)
done

text {* The next ones are analogues of \verb+mult_mono+ and \verb+mult_mono'+ in ereal.*}

lemma ereal_mult_mono:
  fixes a b c d::ereal
  assumes "b \<ge> 0" "c \<ge> 0" "a \<le> b" "c \<le> d"
  shows "a * c \<le> b * d"
by (metis ereal_mult_right_mono mult.commute order_trans assms)

lemma ereal_mult_mono':
  fixes a b c d::ereal
  assumes "a \<ge> 0" "c \<ge> 0" "a \<le> b" "c \<le> d"
  shows "a * c \<le> b * d"
by (metis ereal_mult_right_mono mult.commute order_trans assms)

lemma ereal_mult_mono_strict:
  fixes a b c d::ereal
  assumes "b > 0" "c > 0" "a < b" "c < d"
  shows "a * c < b * d"
proof -
  have "c < \<infinity>" using `c < d` by auto
  then have "a * c < b * c" by (metis ereal_mult_strict_left_mono[OF assms(3) assms(2)] mult.commute)
  moreover have "b * c \<le> b * d" using assms(2) assms(4) by (simp add: assms(1) ereal_mult_left_mono less_imp_le)
  ultimately show ?thesis by simp
qed

lemma ereal_mult_mono_strict':
  fixes a b c d::ereal
  assumes "a > 0" "c > 0" "a < b" "c < d"
  shows "a * c < b * d"
apply (rule ereal_mult_mono_strict, auto simp add: assms) using assms by auto

lemma ereal_abs_add:
  fixes a b::ereal
  shows "abs(a+b) \<le> abs a + abs b"
by (cases rule: ereal2_cases[of a b]) (auto)

lemma ereal_abs_diff:
  fixes a b::ereal
  shows "abs(a-b) \<le> abs a + abs b"
by (cases rule: ereal2_cases[of a b]) (auto)

lemma sum_constant_ereal:
  fixes a::ereal
  shows "(\<Sum>i\<in>I. a) = a * card I"
apply (cases "finite I", induct set: finite, simp_all)
apply (cases a, auto, metis (no_types, hide_lams) add.commute mult.commute semiring_normalization_rules(3))
done

lemma real_lim_then_eventually_real:
  assumes "(u \<longlongrightarrow> ereal l) F"
  shows "eventually (\<lambda>n. u n = ereal(real_of_ereal(u n))) F"
proof -
  have "ereal l \<in> {-\<infinity><..<(\<infinity>::ereal)}" by simp
  moreover have "open {-\<infinity><..<(\<infinity>::ereal)}" by simp
  ultimately have "eventually (\<lambda>n. u n \<in> {-\<infinity><..<(\<infinity>::ereal)}) F" using assms tendsto_def by blast
  moreover have "\<And>x. x \<in> {-\<infinity><..<(\<infinity>::ereal)} \<Longrightarrow> x = ereal(real_of_ereal x)" using ereal_real by auto
  ultimately show ?thesis by (metis (mono_tags, lifting) eventually_mono)
qed

lemma ereal_Inf_cmult:
  assumes "c>(0::real)"
  shows "Inf {ereal c * x |x. P x} = ereal c * Inf {x. P x}"
proof -
  have "(\<lambda>x::ereal. c * x) (Inf {x::ereal. P x}) = Inf ((\<lambda>x::ereal. c * x)`{x::ereal. P x})"
    apply (rule mono_bij_Inf)
    apply (simp add: assms ereal_mult_left_mono less_imp_le mono_def)
    apply (rule bij_betw_byWitness[of _ "\<lambda>x. (x::ereal) / c"], auto simp add: assms ereal_mult_divide)
    using assms ereal_divide_eq apply auto
    done
  then show ?thesis by (simp only: setcompr_eq_image[symmetric])
qed


subsubsection {*Continuity of addition*}

text {*The next few lemmas remove an unnecessary assumption in \verb+tendsto_add_ereal+, culminating
in \verb+tendsto_add_ereal_general+ which essentially says that the addition
is continuous on ereal times ereal, except at $(-\infty, \infty)$ and $(\infty, -\infty)$.
It is much more convenient in many situations, see for instance the proof of
\verb+tendsto_sum_ereal+ below. *}

lemma tendsto_add_ereal_PInf:
  fixes y :: ereal
  assumes y: "y \<noteq> -\<infinity>"
  assumes f: "(f \<longlongrightarrow> \<infinity>) F" and g: "(g \<longlongrightarrow> y) F"
  shows "((\<lambda>x. f x + g x) \<longlongrightarrow> \<infinity>) F"
proof -
  have "\<exists>C. eventually (\<lambda>x. g x > ereal C) F"
  proof (cases y)
    case (real r)
    have "y > y-1" using y real by (simp add: ereal_between(1))
    then have "eventually (\<lambda>x. g x > y - 1) F" using g y order_tendsto_iff by auto
    moreover have "y-1 = ereal(real_of_ereal(y-1))"
      by (metis real ereal_eq_1(1) ereal_minus(1) real_of_ereal.simps(1))
    ultimately have "eventually (\<lambda>x. g x > ereal(real_of_ereal(y - 1))) F" by simp
    then show ?thesis by auto
  next
    case (PInf)
    have "eventually (\<lambda>x. g x > ereal 0) F" using g PInf by (simp add: tendsto_PInfty)
    then show ?thesis by auto
  qed (simp add: y)
  then obtain C::real where ge: "eventually (\<lambda>x. g x > ereal C) F" by auto

  {
    fix M::real
    have "eventually (\<lambda>x. f x > ereal(M - C)) F" using f by (simp add: tendsto_PInfty)
    then have "eventually (\<lambda>x. (f x > ereal (M-C)) \<and> (g x > ereal C)) F"
      by (auto simp add: ge eventually_conj_iff)
    moreover have "\<And>x. ((f x > ereal (M-C)) \<and> (g x > ereal C)) \<Longrightarrow> (f x + g x > ereal M)"
      using ereal_add_strict_mono2 by fastforce
    ultimately have "eventually (\<lambda>x. f x + g x > ereal M) F" using eventually_mono by force
  }
  then show ?thesis by (simp add: tendsto_PInfty)
qed

text{* One would like to deduce the next lemma from the previous one, but the fact
that $-(x+y)$ is in general different from $(-x) + (-y)$ in ereal creates difficulties,
so it is more efficient to copy the previous proof.*}

lemma tendsto_add_ereal_MInf:
  fixes y :: ereal
  assumes y: "y \<noteq> \<infinity>"
  assumes f: "(f \<longlongrightarrow> -\<infinity>) F" and g: "(g \<longlongrightarrow> y) F"
  shows "((\<lambda>x. f x + g x) \<longlongrightarrow> -\<infinity>) F"
proof -
  have "\<exists>C. eventually (\<lambda>x. g x < ereal C) F"
  proof (cases y)
    case (real r)
    have "y < y+1" using y real by (simp add: ereal_between(1))
    then have "eventually (\<lambda>x. g x < y + 1) F" using g y order_tendsto_iff by force
    moreover have "y+1 = ereal(real_of_ereal (y+1))" by (simp add: real)
    ultimately have "eventually (\<lambda>x. g x < ereal(real_of_ereal(y + 1))) F" by simp
    then show ?thesis by auto
  next
    case (MInf)
    have "eventually (\<lambda>x. g x < ereal 0) F" using g MInf by (simp add: tendsto_MInfty)
    then show ?thesis by auto
  qed (simp add: y)
  then obtain C::real where ge: "eventually (\<lambda>x. g x < ereal C) F" by auto

  {
    fix M::real
    have "eventually (\<lambda>x. f x < ereal(M - C)) F" using f by (simp add: tendsto_MInfty)
    then have "eventually (\<lambda>x. (f x < ereal (M- C)) \<and> (g x < ereal C)) F"
      by (auto simp add: ge eventually_conj_iff)
    moreover have "\<And>x. ((f x < ereal (M-C)) \<and> (g x < ereal C)) \<Longrightarrow> (f x + g x < ereal M)"
      using ereal_add_strict_mono2 by fastforce
    ultimately have "eventually (\<lambda>x. f x + g x < ereal M) F" using eventually_mono by force
  }
  then show ?thesis by (simp add: tendsto_MInfty)
qed

lemma tendsto_add_ereal_general1:
  fixes x y :: ereal
  assumes y: "\<bar>y\<bar> \<noteq> \<infinity>"
  assumes f: "(f \<longlongrightarrow> x) F" and g: "(g \<longlongrightarrow> y) F"
  shows "((\<lambda>x. f x + g x) \<longlongrightarrow> x + y) F"
proof (cases x)
  case (real r)
  have a: "\<bar>x\<bar> \<noteq> \<infinity>" by (simp add: real)
  show ?thesis by (rule tendsto_add_ereal[OF a, OF y, OF f, OF g])
next
  case PInf
  then show ?thesis using tendsto_add_ereal_PInf assms by force
next
  case MInf
  then show ?thesis using tendsto_add_ereal_MInf assms
    by (metis abs_ereal.simps(3) ereal_MInfty_eq_plus)
qed

lemma tendsto_add_ereal_general2:
  fixes x y :: ereal
  assumes x: "\<bar>x\<bar> \<noteq> \<infinity>"
      and f: "(f \<longlongrightarrow> x) F" and g: "(g \<longlongrightarrow> y) F"
  shows "((\<lambda>x. f x + g x) \<longlongrightarrow> x + y) F"
proof -
  have "((\<lambda>x. g x + f x) \<longlongrightarrow> x + y) F"
    using tendsto_add_ereal_general1[OF x, OF g, OF f] add.commute[of "y", of "x"] by simp
  moreover have "\<And>x. g x + f x = f x + g x" using add.commute by auto
  ultimately show ?thesis by simp
qed

text {* The next lemma says that the addition is continuous on ereal, except at
the pairs $(-\infty, \infty)$ and $(\infty, -\infty)$. *}

lemma tendsto_add_ereal_general [tendsto_intros]:
  fixes x y :: ereal
  assumes "\<not>((x=\<infinity> \<and> y=-\<infinity>) \<or> (x=-\<infinity> \<and> y=\<infinity>))"
      and f: "(f \<longlongrightarrow> x) F" and g: "(g \<longlongrightarrow> y) F"
  shows "((\<lambda>x. f x + g x) \<longlongrightarrow> x + y) F"
proof (cases x)
  case (real r)
  show ?thesis
    apply (rule tendsto_add_ereal_general2) using real assms by auto
next
  case (PInf)
  then have "y \<noteq> -\<infinity>" using assms by simp
  then show ?thesis using tendsto_add_ereal_PInf PInf assms by auto
next
  case (MInf)
  then have "y \<noteq> \<infinity>" using assms by simp
  then show ?thesis using tendsto_add_ereal_MInf MInf f g by (metis ereal_MInfty_eq_plus)
qed

subsubsection {*Continuity of multiplication*}

text {* In the same way as for addition, we prove that the multiplication is continuous on
ereal times ereal, except at $(\infty, 0)$ and $(-\infty, 0)$ and $(0, \infty)$ and $(0, -\infty)$,
starting with specific situations.*}

lemma tendsto_mult_real_ereal:
  assumes "(u \<longlongrightarrow> ereal l) F" "(v \<longlongrightarrow> ereal m) F"
  shows "((\<lambda>n. u n * v n) \<longlongrightarrow> ereal l * ereal m) F"
proof -
  have ureal: "eventually (\<lambda>n. u n = ereal(real_of_ereal(u n))) F" by (rule real_lim_then_eventually_real[OF assms(1)])
  then have "((\<lambda>n. ereal(real_of_ereal(u n))) \<longlongrightarrow> ereal l) F" using assms by auto
  then have limu: "((\<lambda>n. real_of_ereal(u n)) \<longlongrightarrow> l) F" by auto
  have vreal: "eventually (\<lambda>n. v n = ereal(real_of_ereal(v n))) F" by (rule real_lim_then_eventually_real[OF assms(2)])
  then have "((\<lambda>n. ereal(real_of_ereal(v n))) \<longlongrightarrow> ereal m) F" using assms by auto
  then have limv: "((\<lambda>n. real_of_ereal(v n)) \<longlongrightarrow> m) F" by auto

  {
    fix n assume "u n = ereal(real_of_ereal(u n))" "v n = ereal(real_of_ereal(v n))"
    then have "ereal(real_of_ereal(u n) * real_of_ereal(v n)) = u n * v n" by (metis times_ereal.simps(1))
  }
  then have *: "eventually (\<lambda>n. ereal(real_of_ereal(u n) * real_of_ereal(v n)) = u n * v n) F"
    using eventually_elim2[OF ureal vreal] by auto

  have "((\<lambda>n. real_of_ereal(u n) * real_of_ereal(v n)) \<longlongrightarrow> l * m) F" using tendsto_mult[OF limu limv] by auto
  then have "((\<lambda>n. ereal(real_of_ereal(u n)) * real_of_ereal(v n)) \<longlongrightarrow> ereal(l * m)) F" by auto
  then show ?thesis using * filterlim_cong by fastforce
qed

lemma tendsto_mult_ereal_PInf:
  fixes f g::"_ \<Rightarrow> ereal"
  assumes "(f \<longlongrightarrow> l) F" "l>0" "(g \<longlongrightarrow> \<infinity>) F"
  shows "((\<lambda>x. f x * g x) \<longlongrightarrow> \<infinity>) F"
proof -
  obtain a::real where "0 < ereal a" "a < l" using assms(2) using ereal_dense2 by blast
  have *: "eventually (\<lambda>x. f x > a) F" using `a < l` assms(1) by (simp add: order_tendsto_iff)
  {
    fix K::real
    define M where "M = max K 1"
    then have "M > 0" by simp
    then have "ereal(M/a) > 0" using `ereal a > 0` by simp
    then have "\<And>x. ((f x > a) \<and> (g x > M/a)) \<Longrightarrow> (f x * g x > ereal a * ereal(M/a))"
      using ereal_mult_mono_strict'[where ?c = "M/a", OF `0 < ereal a`] by auto
    moreover have "ereal a * ereal(M/a) = M" using `ereal a > 0` by simp
    ultimately have "\<And>x. ((f x > a) \<and> (g x > M/a)) \<Longrightarrow> (f x * g x > M)" by simp
    moreover have "M \<ge> K" unfolding M_def by simp
    ultimately have Imp: "\<And>x. ((f x > a) \<and> (g x > M/a)) \<Longrightarrow> (f x * g x > K)"
      using ereal_less_eq(3) le_less_trans by blast

    have "eventually (\<lambda>x. g x > M/a) F" using assms(3) by (simp add: tendsto_PInfty)
    then have "eventually (\<lambda>x. (f x > a) \<and> (g x > M/a)) F"
      using * by (auto simp add: eventually_conj_iff)
    then have "eventually (\<lambda>x. f x * g x > K) F" using eventually_mono Imp by force
  }
  then show ?thesis by (auto simp add: tendsto_PInfty)
qed

lemma tendsto_mult_ereal_pos:
  fixes f g::"_ \<Rightarrow> ereal"
  assumes "(f \<longlongrightarrow> l) F" "(g \<longlongrightarrow> m) F" "l>0" "m>0"
  shows "((\<lambda>x. f x * g x) \<longlongrightarrow> l * m) F"
proof (cases)
  assume *: "l = \<infinity> \<or> m = \<infinity>"
  then show ?thesis
  proof (cases)
    assume "m = \<infinity>"
    then show ?thesis using tendsto_mult_ereal_PInf assms by auto
  next
    assume "\<not>(m = \<infinity>)"
    then have "l = \<infinity>" using * by simp
    then have "((\<lambda>x. g x * f x) \<longlongrightarrow> l * m) F" using tendsto_mult_ereal_PInf assms by auto
    moreover have "\<And>x. g x * f x = f x * g x" using mult.commute by auto
    ultimately show ?thesis by simp
  qed
next
  assume "\<not>(l = \<infinity> \<or> m = \<infinity>)"
  then have "l < \<infinity>" "m < \<infinity>" by auto
  then obtain lr mr where "l = ereal lr" "m = ereal mr"
    using `l>0` `m>0` by (metis ereal_cases ereal_less(6) not_less_iff_gr_or_eq)
  then show ?thesis using tendsto_mult_real_ereal assms by auto
qed

text {*We reduce the general situation to the positive case by multiplying by suitable signs.
Unfortunately, as ereal is not a ring, all the neat sign lemmas are not available there. We
give the bare minimum we need.*}

lemma ereal_sgn_abs:
  fixes l::ereal
  shows "sgn(l) * l = abs(l)"
apply (cases l) by (auto simp add: sgn_if ereal_less_uminus_reorder)

lemma sgn_squared_ereal:
  assumes "l \<noteq> (0::ereal)"
  shows "sgn(l) * sgn(l) = 1"
apply (cases l) using assms by (auto simp add: one_ereal_def sgn_if)

lemma tendsto_mult_ereal [tendsto_intros]:
  fixes f g::"_ \<Rightarrow> ereal"
  assumes "(f \<longlongrightarrow> l) F" "(g \<longlongrightarrow> m) F" "\<not>((l=0 \<and> abs(m) = \<infinity>) \<or> (m=0 \<and> abs(l) = \<infinity>))"
  shows "((\<lambda>x. f x * g x) \<longlongrightarrow> l * m) F"
proof (cases)
  assume "l=0 \<or> m=0"
  then have "abs(l) \<noteq> \<infinity>" "abs(m) \<noteq> \<infinity>" using assms(3) by auto
  then obtain lr mr where "l = ereal lr" "m = ereal mr" by auto
  then show ?thesis using tendsto_mult_real_ereal assms by auto
next
  have sgn_finite: "\<And>a::ereal. abs(sgn a) \<noteq> \<infinity>"
    by (metis MInfty_neq_ereal(2) PInfty_neq_ereal(2) abs_eq_infinity_cases ereal_times(1) ereal_times(3) ereal_uminus_eq_reorder sgn_ereal.elims)
  then have sgn_finite2: "\<And>a b::ereal. abs(sgn a * sgn b) \<noteq> \<infinity>"
    by (metis abs_eq_infinity_cases abs_ereal.simps(2) abs_ereal.simps(3) ereal_mult_eq_MInfty ereal_mult_eq_PInfty)
  assume "\<not>(l=0 \<or> m=0)"
  then have "l \<noteq> 0" "m \<noteq> 0" by auto
  then have "abs(l) > 0" "abs(m) > 0"
    by (metis abs_ereal_ge0 abs_ereal_less0 abs_ereal_pos ereal_uminus_uminus ereal_uminus_zero less_le not_less)+
  then have "sgn(l) * l > 0" "sgn(m) * m > 0" using ereal_sgn_abs by auto
  moreover have "((\<lambda>x. sgn(l) * f x) \<longlongrightarrow> (sgn(l) * l)) F"
    by (rule tendsto_cmult_ereal, auto simp add: sgn_finite assms(1))
  moreover have "((\<lambda>x. sgn(m) * g x) \<longlongrightarrow> (sgn(m) * m)) F"
    by (rule tendsto_cmult_ereal, auto simp add: sgn_finite assms(2))
  ultimately have *: "((\<lambda>x. (sgn(l) * f x) * (sgn(m) * g x)) \<longlongrightarrow> (sgn(l) * l) * (sgn(m) * m)) F"
    using tendsto_mult_ereal_pos by force
  have "((\<lambda>x. (sgn(l) * sgn(m)) * ((sgn(l) * f x) * (sgn(m) * g x))) \<longlongrightarrow> (sgn(l) * sgn(m)) * ((sgn(l) * l) * (sgn(m) * m))) F"
    by (rule tendsto_cmult_ereal, auto simp add: sgn_finite2 *)
  moreover have "\<And>x. (sgn(l) * sgn(m)) * ((sgn(l) * f x) * (sgn(m) * g x)) = f x * g x"
    by (metis mult.left_neutral sgn_squared_ereal[OF `l \<noteq> 0`] sgn_squared_ereal[OF `m \<noteq> 0`] mult.assoc mult.commute)
  moreover have "(sgn(l) * sgn(m)) * ((sgn(l) * l) * (sgn(m) * m)) = l * m"
    by (metis mult.left_neutral sgn_squared_ereal[OF `l \<noteq> 0`] sgn_squared_ereal[OF `m \<noteq> 0`] mult.assoc mult.commute)
  ultimately show ?thesis by auto
qed

lemma tendsto_cmult_ereal_general [tendsto_intros]:
  fixes f::"_ \<Rightarrow> ereal" and c::ereal
  assumes "(f \<longlongrightarrow> l) F" "\<not> (l=0 \<and> abs(c) = \<infinity>)"
  shows "((\<lambda>x. c * f x) \<longlongrightarrow> c * l) F"
by (cases "c = 0", auto simp add: assms tendsto_mult_ereal)


subsubsection {*Continuity of division*}

lemma tendsto_inverse_ereal_PInf:
  fixes u::"_ \<Rightarrow> ereal"
  assumes "(u \<longlongrightarrow> \<infinity>) F"
  shows "((\<lambda>x. 1/ u x) \<longlongrightarrow> 0) F"
proof -
  {
    fix e::real assume "e>0"
    have "1/e < \<infinity>" by auto
    then have "eventually (\<lambda>n. u n > 1/e) F" using assms(1) by (simp add: tendsto_PInfty)
    moreover
    {
      fix z::ereal assume "z>1/e"
      then have "z>0" using `e>0` using less_le_trans not_le by fastforce
      then have "1/z \<ge> 0" by auto
      moreover have "1/z < e" using `e>0` `z>1/e`
        apply (cases z) apply auto
        by (metis (mono_tags, hide_lams) less_ereal.simps(2) less_ereal.simps(4) divide_less_eq ereal_divide_less_pos ereal_less(4)
            ereal_less_eq(4) less_le_trans mult_eq_0_iff not_le not_one_less_zero times_ereal.simps(1))
      ultimately have "1/z \<ge> 0" "1/z < e" by auto
    }
    ultimately have "eventually (\<lambda>n. 1/u n<e) F" "eventually (\<lambda>n. 1/u n\<ge>0) F" by (auto simp add: eventually_mono)
  } note * = this
  show ?thesis
  proof (subst order_tendsto_iff, auto)
    fix a::ereal assume "a<0"
    then show "eventually (\<lambda>n. 1/u n > a) F" using *(2) eventually_mono less_le_trans linordered_field_no_ub by fastforce
  next
    fix a::ereal assume "a>0"
    then obtain e::real where "e>0" "a>e" using ereal_dense2 ereal_less(2) by blast
    then have "eventually (\<lambda>n. 1/u n < e) F" using *(1) by auto
    then show "eventually (\<lambda>n. 1/u n < a) F" using `a>e` by (metis (mono_tags, lifting) eventually_mono less_trans)
  qed
qed

lemma tendsto_inverse_ereal [tendsto_intros]:
  fixes u::"_ \<Rightarrow> ereal"
  assumes "(u \<longlongrightarrow> l) F" "l \<noteq> 0"
  shows "((\<lambda>x. 1/ u x) \<longlongrightarrow> 1/l) F"
proof (cases l)
  case (real r)
  then have "r \<noteq> 0" using assms(2) by auto
  then have "1/l = ereal(1/r)" using real by (simp add: one_ereal_def)
  define v where "v = (\<lambda>n. real_of_ereal(u n))"
  have ureal: "eventually (\<lambda>n. u n = ereal(v n)) F" unfolding v_def using real_lim_then_eventually_real assms(1) real by auto
  then have "((\<lambda>n. ereal(v n)) \<longlongrightarrow> ereal r) F" using assms real v_def by auto
  then have *: "((\<lambda>n. v n) \<longlongrightarrow> r) F" by auto
  then have "((\<lambda>n. 1/v n) \<longlongrightarrow> 1/r) F" using \<open>r \<noteq> 0\<close> tendsto_inverse_real by auto
  then have lim: "((\<lambda>n. ereal(1/v n)) \<longlongrightarrow> 1/l) F" using \<open>1/l = ereal(1/r)\<close> by auto

  have "r \<in> -{0}" "open (-{(0::real)})" using \<open>r \<noteq> 0\<close> by auto
  then have "eventually (\<lambda>n. v n \<in> -{0}) F" using * using topological_tendstoD by blast
  then have "eventually (\<lambda>n. v n \<noteq> 0) F" by auto
  moreover
  {
    fix n assume H: "v n \<noteq> 0" "u n = ereal(v n)"
    then have "ereal(1/v n) = 1/ereal(v n)" by (simp add: one_ereal_def)
    then have "ereal(1/v n) = 1/u n" using H(2) by simp
  }
  ultimately have "eventually (\<lambda>n. ereal(1/v n) = 1/u n) F" using ureal eventually_elim2 by force
  with Lim_transform_eventually[OF this lim] show ?thesis by simp
next
  case (PInf)
  then have "1/l = 0" by auto
  then show ?thesis using tendsto_inverse_ereal_PInf assms PInf by auto
next
  case (MInf)
  then have "1/l = 0" by auto
  have "1/z = -1/ -z" if "z < 0" for z::ereal
    apply (cases z) using divide_ereal_def \<open> z < 0 \<close> by auto
  moreover have "eventually (\<lambda>n. u n < 0) F" by (metis (no_types) MInf assms(1) tendsto_MInfty zero_ereal_def)
  ultimately have *: "eventually (\<lambda>n. -1/-u n = 1/u n) F" by (simp add: eventually_mono)

  define v where "v = (\<lambda>n. - u n)"
  have "(v \<longlongrightarrow> \<infinity>) F" unfolding v_def using MInf assms(1) tendsto_uminus_ereal by fastforce
  then have "((\<lambda>n. 1/v n) \<longlongrightarrow> 0) F" using tendsto_inverse_ereal_PInf by auto
  then have "((\<lambda>n. -1/v n) \<longlongrightarrow> 0) F" using tendsto_uminus_ereal by fastforce
  then show ?thesis unfolding v_def using Lim_transform_eventually[OF *] \<open> 1/l = 0 \<close> by auto
qed

lemma tendsto_divide_ereal [tendsto_intros]:
  fixes f g::"_ \<Rightarrow> ereal"
  assumes "(f \<longlongrightarrow> l) F" "(g \<longlongrightarrow> m) F" "m \<noteq> 0" "\<not>(abs(l) = \<infinity> \<and> abs(m) = \<infinity>)"
  shows "((\<lambda>x. f x / g x) \<longlongrightarrow> l / m) F"
proof -
  define h where "h = (\<lambda>x. 1/ g x)"
  have *: "(h \<longlongrightarrow> 1/m) F" unfolding h_def using assms(2) assms(3) tendsto_inverse_ereal by auto
  have "((\<lambda>x. f x * h x) \<longlongrightarrow> l * (1/m)) F"
    apply (rule tendsto_mult_ereal[OF assms(1) *]) using assms(3) assms(4) by (auto simp add: divide_ereal_def)
  moreover have "f x * h x = f x / g x" for x unfolding h_def by (simp add: divide_ereal_def)
  moreover have "l * (1/m) = l/m" by (simp add: divide_ereal_def)
  ultimately show ?thesis unfolding h_def using Lim_transform_eventually by auto
qed


subsubsection {*Further limits*}

lemma id_nat_ereal_tendsto_PInf [tendsto_intros]:
  "(\<lambda> n::nat. real n) \<longlonglongrightarrow> \<infinity>"
by (simp add: filterlim_real_sequentially tendsto_PInfty_eq_at_top)

lemma tendsto_at_top_pseudo_inverse [tendsto_intros]:
  fixes u::"nat \<Rightarrow> nat"
  assumes "LIM n sequentially. u n :> at_top"
  shows "LIM n sequentially. Inf {N. u N \<ge> n} :> at_top"
proof -
  {
    fix C::nat
    define M where "M = Max {u n| n. n \<le> C}+1"
    {
      fix n assume "n \<ge> M"
      have "eventually (\<lambda>N. u N \<ge> n) sequentially" using assms
        by (simp add: filterlim_at_top)
      then have *: "{N. u N \<ge> n} \<noteq> {}" by force

      have "N > C" if "u N \<ge> n" for N
      proof (rule ccontr)
        assume "\<not>(N > C)"
        have "u N \<le> Max {u n| n. n \<le> C}"
          apply (rule Max_ge) using `\<not>(N > C)` by auto
        then show False using `u N \<ge> n` `n \<ge> M` unfolding M_def by auto
      qed
      then have **: "{N. u N \<ge> n} \<subseteq> {C..}" by fastforce
      have "Inf {N. u N \<ge> n} \<ge> C"
        by (metis "*" "**" Inf_nat_def1 atLeast_iff subset_eq)
    }
    then have "eventually (\<lambda>n. Inf {N. u N \<ge> n} \<ge> C) sequentially"
      using eventually_sequentially by auto
  }
  then show ?thesis using filterlim_at_top by auto
qed

lemma pseudo_inverse_finite_set:
  fixes u::"nat \<Rightarrow> nat"
  assumes "LIM n sequentially. u n :> at_top"
  shows "finite {N. u N \<le> n}"
proof -
  fix n
  have "eventually (\<lambda>N. u N \<ge> n+1) sequentially" using assms
    by (simp add: filterlim_at_top)
  then obtain N1 where N1: "\<And>N. N \<ge> N1 \<Longrightarrow> u N \<ge> n + 1"
    using eventually_sequentially by auto
  have "{N. u N \<le> n} \<subseteq> {..<N1}"
    apply auto using N1 by (metis Suc_eq_plus1 not_less not_less_eq_eq)
  then show "finite {N. u N \<le> n}" by (simp add: finite_subset)
qed

lemma tendsto_at_top_pseudo_inverse2 [tendsto_intros]:
  fixes u::"nat \<Rightarrow> nat"
  assumes "LIM n sequentially. u n :> at_top"
  shows "LIM n sequentially. Max {N. u N \<le> n} :> at_top"
proof -
  {
    fix N0::nat
    have "N0 \<le> Max {N. u N \<le> n}" if "n \<ge> u N0" for n
      apply (rule Max.coboundedI) using pseudo_inverse_finite_set[OF assms] that by auto
    then have "eventually (\<lambda>n. N0 \<le> Max {N. u N \<le> n}) sequentially"
      using eventually_sequentially by blast
  }
  then show ?thesis using filterlim_at_top by auto
qed

lemma ereal_truncation_top [tendsto_intros]:
  fixes x::ereal
  shows "(\<lambda>n::nat. min x n) \<longlonglongrightarrow> x"
proof (cases x)
  case (real r)
  then obtain K::nat where "K>0" "K > abs(r)" using reals_Archimedean2 gr0I by auto
  then have "min x n = x" if "n \<ge> K" for n apply (subst real, subst real, auto) using that eq_iff by fastforce
  then have "eventually (\<lambda>n. min x n = x) sequentially" using eventually_at_top_linorder by blast
  then show ?thesis by (simp add: Lim_eventually)
next
  case (PInf)
  then have "min x n = n" for n::nat by (auto simp add: min_def)
  then show ?thesis using id_nat_ereal_tendsto_PInf PInf by auto
next
  case (MInf)
  then have "min x n = x" for n::nat by (auto simp add: min_def)
  then show ?thesis by auto
qed

lemma ereal_truncation_real_top [tendsto_intros]:
  fixes x::ereal
  assumes "x \<noteq> - \<infinity>"
  shows "(\<lambda>n::nat. real_of_ereal(min x n)) \<longlonglongrightarrow> x"
proof (cases x)
  case (real r)
  then obtain K::nat where "K>0" "K > abs(r)" using reals_Archimedean2 gr0I by auto
  then have "min x n = x" if "n \<ge> K" for n apply (subst real, subst real, auto) using that eq_iff by fastforce
  then have "real_of_ereal(min x n) = r" if "n \<ge> K" for n using real that by auto
  then have "eventually (\<lambda>n. real_of_ereal(min x n) = r) sequentially" using eventually_at_top_linorder by blast
  then have "(\<lambda>n. real_of_ereal(min x n)) \<longlonglongrightarrow> r" by (simp add: Lim_eventually)
  then show ?thesis using real by auto
next
  case (PInf)
  then have "real_of_ereal(min x n) = n" for n::nat by (auto simp add: min_def)
  then show ?thesis using id_nat_ereal_tendsto_PInf PInf by auto
qed (simp add: assms)

lemma ereal_truncation_bottom [tendsto_intros]:
  fixes x::ereal
  shows "(\<lambda>n::nat. max x (- real n)) \<longlonglongrightarrow> x"
proof (cases x)
  case (real r)
  then obtain K::nat where "K>0" "K > abs(r)" using reals_Archimedean2 gr0I by auto
  then have "max x (-real n) = x" if "n \<ge> K" for n apply (subst real, subst real, auto) using that eq_iff by fastforce
  then have "eventually (\<lambda>n. max x (-real n) = x) sequentially" using eventually_at_top_linorder by blast
  then show ?thesis by (simp add: Lim_eventually)
next
  case (MInf)
  then have "max x (-real n) = (-1)* ereal(real n)" for n::nat by (auto simp add: max_def)
  moreover have "(\<lambda>n. (-1)* ereal(real n)) \<longlonglongrightarrow> -\<infinity>"
    using tendsto_cmult_ereal[of "-1", OF _ id_nat_ereal_tendsto_PInf] by (simp add: one_ereal_def)
  ultimately show ?thesis using MInf by auto
next
  case (PInf)
  then have "max x (-real n) = x" for n::nat by (auto simp add: max_def)
  then show ?thesis by auto
qed

lemma ereal_truncation_real_bottom [tendsto_intros]:
  fixes x::ereal
  assumes "x \<noteq> \<infinity>"
  shows "(\<lambda>n::nat. real_of_ereal(max x (- real n))) \<longlonglongrightarrow> x"
proof (cases x)
  case (real r)
  then obtain K::nat where "K>0" "K > abs(r)" using reals_Archimedean2 gr0I by auto
  then have "max x (-real n) = x" if "n \<ge> K" for n apply (subst real, subst real, auto) using that eq_iff by fastforce
  then have "real_of_ereal(max x (-real n)) = r" if "n \<ge> K" for n using real that by auto
  then have "eventually (\<lambda>n. real_of_ereal(max x (-real n)) = r) sequentially" using eventually_at_top_linorder by blast
  then have "(\<lambda>n. real_of_ereal(max x (-real n))) \<longlonglongrightarrow> r" by (simp add: Lim_eventually)
  then show ?thesis using real by auto
next
  case (MInf)
  then have "real_of_ereal(max x (-real n)) = (-1)* ereal(real n)" for n::nat by (auto simp add: max_def)
  moreover have "(\<lambda>n. (-1)* ereal(real n)) \<longlonglongrightarrow> -\<infinity>"
    using tendsto_cmult_ereal[of "-1", OF _ id_nat_ereal_tendsto_PInf] by (simp add: one_ereal_def)
  ultimately show ?thesis using MInf by auto
qed (simp add: assms)

text {* the next one is copied from \verb+tendsto_sum+. *}
lemma tendsto_sum_ereal [tendsto_intros]:
  fixes f :: "'a \<Rightarrow> 'b \<Rightarrow> ereal"
  assumes "\<And>i. i \<in> S \<Longrightarrow> (f i \<longlongrightarrow> a i) F"
          "\<And>i. abs(a i) \<noteq> \<infinity>"
  shows "((\<lambda>x. \<Sum>i\<in>S. f i x) \<longlongrightarrow> (\<Sum>i\<in>S. a i)) F"
proof (cases "finite S")
  assume "finite S" then show ?thesis using assms
    by (induct, simp, simp add: tendsto_add_ereal_general2 assms)
qed(simp)

subsubsection {*Limsups and liminfs*}

lemma limsup_finite_then_bounded:
  fixes u::"nat \<Rightarrow> real"
  assumes "limsup u < \<infinity>"
  shows "\<exists>C. \<forall>n. u n \<le> C"
proof -
  obtain C where C: "limsup u < C" "C < \<infinity>" using assms ereal_dense2 by blast
  then have "C = ereal(real_of_ereal C)" using ereal_real by force
  have "eventually (\<lambda>n. u n < C) sequentially" using C(1) unfolding Limsup_def
    apply (auto simp add: INF_less_iff)
    using SUP_lessD eventually_mono by fastforce
  then obtain N where N: "\<And>n. n \<ge> N \<Longrightarrow> u n < C" using eventually_sequentially by auto
  define D where "D = max (real_of_ereal C) (Max {u n |n. n \<le> N})"
  have "\<And>n. u n \<le> D"
  proof -
    fix n show "u n \<le> D"
    proof (cases)
      assume *: "n \<le> N"
      have "u n \<le> Max {u n |n. n \<le> N}" by (rule Max_ge, auto simp add: *)
      then show "u n \<le> D" unfolding D_def by linarith
    next
      assume "\<not>(n \<le> N)"
      then have "n \<ge> N" by simp
      then have "u n < C" using N by auto
      then have "u n < real_of_ereal C" using `C = ereal(real_of_ereal C)` less_ereal.simps(1) by fastforce
      then show "u n \<le> D" unfolding D_def by linarith
    qed
  qed
  then show ?thesis by blast
qed

lemma liminf_finite_then_bounded_below:
  fixes u::"nat \<Rightarrow> real"
  assumes "liminf u > -\<infinity>"
  shows "\<exists>C. \<forall>n. u n \<ge> C"
proof -
  obtain C where C: "liminf u > C" "C > -\<infinity>" using assms using ereal_dense2 by blast
  then have "C = ereal(real_of_ereal C)" using ereal_real by force
  have "eventually (\<lambda>n. u n > C) sequentially" using C(1) unfolding Liminf_def
    apply (auto simp add: less_SUP_iff)
    using eventually_elim2 less_INF_D by fastforce
  then obtain N where N: "\<And>n. n \<ge> N \<Longrightarrow> u n > C" using eventually_sequentially by auto
  define D where "D = min (real_of_ereal C) (Min {u n |n. n \<le> N})"
  have "\<And>n. u n \<ge> D"
  proof -
    fix n show "u n \<ge> D"
    proof (cases)
      assume *: "n \<le> N"
      have "u n \<ge> Min {u n |n. n \<le> N}" by (rule Min_le, auto simp add: *)
      then show "u n \<ge> D" unfolding D_def by linarith
    next
      assume "\<not>(n \<le> N)"
      then have "n \<ge> N" by simp
      then have "u n > C" using N by auto
      then have "u n > real_of_ereal C" using `C = ereal(real_of_ereal C)` less_ereal.simps(1) by fastforce
      then show "u n \<ge> D" unfolding D_def by linarith
    qed
  qed
  then show ?thesis by blast
qed

lemma liminf_upper_bound:
  fixes u:: "nat \<Rightarrow> ereal"
  assumes "liminf u < l"
  shows "\<exists>N>k. u N < l"
by (metis assms gt_ex less_le_trans liminf_bounded_iff not_less)

text {* The following statement about limsups is reduced to a statement about limits using
subsequences thanks to \verb+limsup_subseq_lim+. The statement for limits follows for instance from
\verb+tendsto_add_ereal_general+.*}

lemma ereal_limsup_add_mono:
  fixes u v::"nat \<Rightarrow> ereal"
  shows "limsup (\<lambda>n. u n + v n) \<le> limsup u + limsup v"
proof (cases)
  assume "(limsup u = \<infinity>) \<or> (limsup v = \<infinity>)"
  then have "limsup u + limsup v = \<infinity>" by simp
  then show ?thesis by auto
next
  assume "\<not>((limsup u = \<infinity>) \<or> (limsup v = \<infinity>))"
  then have "limsup u < \<infinity>" "limsup v < \<infinity>" by auto

  define w where "w = (\<lambda>n. u n + v n)"
  obtain r where r: "subseq r" "(w o r) \<longlonglongrightarrow> limsup w" using limsup_subseq_lim by auto
  obtain s where s: "subseq s" "(u o r o s) \<longlonglongrightarrow> limsup (u o r)" using limsup_subseq_lim by auto
  obtain t where t: "subseq t" "(v o r o s o t) \<longlonglongrightarrow> limsup (v o r o s)" using limsup_subseq_lim by auto

  define a where "a = r o s o t"
  have "subseq a" using r s t by (simp add: a_def subseq_o)
  have l:"(w o a) \<longlonglongrightarrow> limsup w"
         "(u o a) \<longlonglongrightarrow> limsup (u o r)"
         "(v o a) \<longlonglongrightarrow> limsup (v o r o s)"
  apply (metis (no_types, lifting) r(2) s(1) t(1) LIMSEQ_subseq_LIMSEQ a_def comp_assoc)
  apply (metis (no_types, lifting) s(2) t(1) LIMSEQ_subseq_LIMSEQ a_def comp_assoc)
  apply (metis (no_types, lifting) t(2) a_def comp_assoc)
  done

  have "limsup (u o r) \<le> limsup u" by (simp add: limsup_subseq_mono r(1))
  then have a: "limsup (u o r) \<noteq> \<infinity>" using `limsup u < \<infinity>` by auto
  have "limsup (v o r o s) \<le> limsup v" by (simp add: comp_assoc limsup_subseq_mono r(1) s(1) subseq_o)
  then have b: "limsup (v o r o s) \<noteq> \<infinity>" using `limsup v < \<infinity>` by auto

  have "(\<lambda>n. (u o a) n + (v o a) n) \<longlonglongrightarrow> limsup (u o r) + limsup (v o r o s)"
    using l tendsto_add_ereal_general a b by fastforce
  moreover have "(\<lambda>n. (u o a) n + (v o a) n) = (w o a)" unfolding w_def by auto
  ultimately have "(w o a) \<longlonglongrightarrow> limsup (u o r) + limsup (v o r o s)" by simp
  then have "limsup w = limsup (u o r) + limsup (v o r o s)" using l(1) LIMSEQ_unique by blast
  then have "limsup w \<le> limsup u + limsup v"
    using `limsup (u o r) \<le> limsup u` `limsup (v o r o s) \<le> limsup v` ereal_add_mono by simp
  then show ?thesis unfolding w_def by simp
qed

text {* There is an asymmetry between liminfs and limsups in ereal, as $\infty + (-\infty) = \infty$.
This explains why there are more assumptions in the next lemma dealing with liminfs that in the
previous one about limsups.*}

lemma ereal_liminf_add_mono:
  fixes u v::"nat \<Rightarrow> ereal"
  assumes "\<not>((liminf u = \<infinity> \<and> liminf v = -\<infinity>) \<or> (liminf u = -\<infinity> \<and> liminf v = \<infinity>))"
  shows "liminf (\<lambda>n. u n + v n) \<ge> liminf u + liminf v"
proof (cases)
  assume "(liminf u = -\<infinity>) \<or> (liminf v = -\<infinity>)"
  then have *: "liminf u + liminf v = -\<infinity>" using assms by auto
  show ?thesis by (simp add: *)
next
  assume "\<not>((liminf u = -\<infinity>) \<or> (liminf v = -\<infinity>))"
  then have "liminf u > -\<infinity>" "liminf v > -\<infinity>" by auto

  define w where "w = (\<lambda>n. u n + v n)"
  obtain r where r: "subseq r" "(w o r) \<longlonglongrightarrow> liminf w" using liminf_subseq_lim by auto
  obtain s where s: "subseq s" "(u o r o s) \<longlonglongrightarrow> liminf (u o r)" using liminf_subseq_lim by auto
  obtain t where t: "subseq t" "(v o r o s o t) \<longlonglongrightarrow> liminf (v o r o s)" using liminf_subseq_lim by auto

  define a where "a = r o s o t"
  have "subseq a" using r s t by (simp add: a_def subseq_o)
  have l:"(w o a) \<longlonglongrightarrow> liminf w"
         "(u o a) \<longlonglongrightarrow> liminf (u o r)"
         "(v o a) \<longlonglongrightarrow> liminf (v o r o s)"
  apply (metis (no_types, lifting) r(2) s(1) t(1) LIMSEQ_subseq_LIMSEQ a_def comp_assoc)
  apply (metis (no_types, lifting) s(2) t(1) LIMSEQ_subseq_LIMSEQ a_def comp_assoc)
  apply (metis (no_types, lifting) t(2) a_def comp_assoc)
  done

  have "liminf (u o r) \<ge> liminf u" by (simp add: liminf_subseq_mono r(1))
  then have a: "liminf (u o r) \<noteq> -\<infinity>" using `liminf u > -\<infinity>` by auto
  have "liminf (v o r o s) \<ge> liminf v" by (simp add: comp_assoc liminf_subseq_mono r(1) s(1) subseq_o)
  then have b: "liminf (v o r o s) \<noteq> -\<infinity>" using `liminf v > -\<infinity>` by auto

  have "(\<lambda>n. (u o a) n + (v o a) n) \<longlonglongrightarrow> liminf (u o r) + liminf (v o r o s)"
    using l tendsto_add_ereal_general a b by fastforce
  moreover have "(\<lambda>n. (u o a) n + (v o a) n) = (w o a)" unfolding w_def by auto
  ultimately have "(w o a) \<longlonglongrightarrow> liminf (u o r) + liminf (v o r o s)" by simp
  then have "liminf w = liminf (u o r) + liminf (v o r o s)" using l(1) LIMSEQ_unique by blast
  then have "liminf w \<ge> liminf u + liminf v"
    using `liminf (u o r) \<ge> liminf u` `liminf (v o r o s) \<ge> liminf v` ereal_add_mono by simp
  then show ?thesis unfolding w_def by simp
qed

lemma ereal_limsup_lim_add:
  fixes u v::"nat \<Rightarrow> ereal"
  assumes "u \<longlonglongrightarrow> a" "abs(a) \<noteq> \<infinity>"
  shows "limsup (\<lambda>n. u n + v n) = a + limsup v"
proof -
  have "limsup u = a" using assms(1) using tendsto_iff_Liminf_eq_Limsup trivial_limit_at_top_linorder by blast
  have "(\<lambda>n. -u n) \<longlonglongrightarrow> -a" using assms(1) by auto
  then have "limsup (\<lambda>n. -u n) = -a" using tendsto_iff_Liminf_eq_Limsup trivial_limit_at_top_linorder by blast

  have "limsup (\<lambda>n. u n + v n) \<le> limsup u + limsup v"
    by (rule ereal_limsup_add_mono)
  then have up: "limsup (\<lambda>n. u n + v n) \<le> a + limsup v" using `limsup u = a` by simp

  have a: "limsup (\<lambda>n. (u n + v n) + (-u n)) \<le> limsup (\<lambda>n. u n + v n) + limsup (\<lambda>n. -u n)"
    by (rule ereal_limsup_add_mono)
  have "eventually (\<lambda>n. u n = ereal(real_of_ereal(u n))) sequentially" using assms
    real_lim_then_eventually_real by auto
  moreover have "\<And>x. x = ereal(real_of_ereal(x)) \<Longrightarrow> x + (-x) = 0"
    by (metis plus_ereal.simps(1) right_minus uminus_ereal.simps(1) zero_ereal_def)
  ultimately have "eventually (\<lambda>n. u n + (-u n) = 0) sequentially"
    by (metis (mono_tags, lifting) eventually_mono)
  moreover have "\<And>n. u n + (-u n) = 0 \<Longrightarrow> u n + v n + (-u n) = v n"
    by (metis add.commute add.left_commute add.left_neutral)
  ultimately have "eventually (\<lambda>n. u n + v n + (-u n) = v n) sequentially"
    using eventually_mono by force
  then have "limsup v = limsup (\<lambda>n. u n + v n + (-u n))" using Limsup_eq by force
  then have "limsup v \<le> limsup (\<lambda>n. u n + v n) -a" using a `limsup (\<lambda>n. -u n) = -a` by (simp add: minus_ereal_def)
  then have "limsup (\<lambda>n. u n + v n) \<ge> a + limsup v" using assms(2) by (metis add.commute ereal_le_minus)
  then show ?thesis using up by simp
qed

lemma ereal_liminf_lim_add:
  fixes u v::"nat \<Rightarrow> ereal"
  assumes "u \<longlonglongrightarrow> a" "abs(a) \<noteq> \<infinity>"
  shows "liminf (\<lambda>n. u n + v n) = a + liminf v"
proof -
  have "liminf u = a" using assms(1) tendsto_iff_Liminf_eq_Limsup trivial_limit_at_top_linorder by blast
  then have *: "abs(liminf u) \<noteq> \<infinity>" using assms(2) by auto
  have "(\<lambda>n. -u n) \<longlonglongrightarrow> -a" using assms(1) by auto
  then have "liminf (\<lambda>n. -u n) = -a" using tendsto_iff_Liminf_eq_Limsup trivial_limit_at_top_linorder by blast
  then have **: "abs(liminf (\<lambda>n. -u n)) \<noteq> \<infinity>" using assms(2) by auto

  have "liminf (\<lambda>n. u n + v n) \<ge> liminf u + liminf v"
    apply (rule ereal_liminf_add_mono) using * by auto
  then have up: "liminf (\<lambda>n. u n + v n) \<ge> a + liminf v" using `liminf u = a` by simp

  have a: "liminf (\<lambda>n. (u n + v n) + (-u n)) \<ge> liminf (\<lambda>n. u n + v n) + liminf (\<lambda>n. -u n)"
    apply (rule ereal_liminf_add_mono) using ** by auto
  have "eventually (\<lambda>n. u n = ereal(real_of_ereal(u n))) sequentially" using assms
    real_lim_then_eventually_real by auto
  moreover have "\<And>x. x = ereal(real_of_ereal(x)) \<Longrightarrow> x + (-x) = 0"
    by (metis plus_ereal.simps(1) right_minus uminus_ereal.simps(1) zero_ereal_def)
  ultimately have "eventually (\<lambda>n. u n + (-u n) = 0) sequentially"
    by (metis (mono_tags, lifting) eventually_mono)
  moreover have "\<And>n. u n + (-u n) = 0 \<Longrightarrow> u n + v n + (-u n) = v n"
    by (metis add.commute add.left_commute add.left_neutral)
  ultimately have "eventually (\<lambda>n. u n + v n + (-u n) = v n) sequentially"
    using eventually_mono by force
  then have "liminf v = liminf (\<lambda>n. u n + v n + (-u n))" using Liminf_eq by force
  then have "liminf v \<ge> liminf (\<lambda>n. u n + v n) -a" using a `liminf (\<lambda>n. -u n) = -a` by (simp add: minus_ereal_def)
  then have "liminf (\<lambda>n. u n + v n) \<le> a + liminf v" using assms(2) by (metis add.commute ereal_minus_le)
  then show ?thesis using up by simp
qed

lemma ereal_liminf_limsup_add:
  fixes u v::"nat \<Rightarrow> ereal"
  shows "liminf (\<lambda>n. u n + v n) \<le> liminf u + limsup v"
proof (cases)
  assume "limsup v = \<infinity> \<or> liminf u = \<infinity>"
  then show ?thesis by auto
next
  assume "\<not>(limsup v = \<infinity> \<or> liminf u = \<infinity>)"
  then have "limsup v < \<infinity>" "liminf u < \<infinity>" by auto

  define w where "w = (\<lambda>n. u n + v n)"
  obtain r where r: "subseq r" "(u o r) \<longlonglongrightarrow> liminf u" using liminf_subseq_lim by auto
  obtain s where s: "subseq s" "(w o r o s) \<longlonglongrightarrow> liminf (w o r)" using liminf_subseq_lim by auto
  obtain t where t: "subseq t" "(v o r o s o t) \<longlonglongrightarrow> limsup (v o r o s)" using limsup_subseq_lim by auto

  define a where "a = r o s o t"
  have "subseq a" using r s t by (simp add: a_def subseq_o)
  have l:"(u o a) \<longlonglongrightarrow> liminf u"
         "(w o a) \<longlonglongrightarrow> liminf (w o r)"
         "(v o a) \<longlonglongrightarrow> limsup (v o r o s)"
  apply (metis (no_types, lifting) r(2) s(1) t(1) LIMSEQ_subseq_LIMSEQ a_def comp_assoc)
  apply (metis (no_types, lifting) s(2) t(1) LIMSEQ_subseq_LIMSEQ a_def comp_assoc)
  apply (metis (no_types, lifting) t(2) a_def comp_assoc)
  done

  have "liminf (w o r) \<ge> liminf w" by (simp add: liminf_subseq_mono r(1))
  have "limsup (v o r o s) \<le> limsup v" by (simp add: comp_assoc limsup_subseq_mono r(1) s(1) subseq_o)
  then have b: "limsup (v o r o s) < \<infinity>" using `limsup v < \<infinity>` by auto

  have "(\<lambda>n. (u o a) n + (v o a) n) \<longlonglongrightarrow> liminf u + limsup (v o r o s)"
    apply (rule tendsto_add_ereal_general) using b `liminf u < \<infinity>` l(1) l(3) by force+
  moreover have "(\<lambda>n. (u o a) n + (v o a) n) = (w o a)" unfolding w_def by auto
  ultimately have "(w o a) \<longlonglongrightarrow> liminf u + limsup (v o r o s)" by simp
  then have "liminf (w o r) = liminf u + limsup (v o r o s)" using l(2) using LIMSEQ_unique by blast
  then have "liminf w \<le> liminf u + limsup v"
    using `liminf (w o r) \<ge> liminf w` `limsup (v o r o s) \<le> limsup v`
    by (metis add_mono_thms_linordered_semiring(2) le_less_trans not_less)
  then show ?thesis unfolding w_def by simp
qed

lemma ereal_liminf_limsup_minus:
  fixes u v::"nat \<Rightarrow> ereal"
  shows "liminf (\<lambda>n. u n - v n) \<le> limsup u - limsup v"
  unfolding minus_ereal_def
  apply (subst add.commute)
  apply (rule order_trans[OF ereal_liminf_limsup_add])
  using ereal_Limsup_uminus[of sequentially "\<lambda>n. - v n"]
  apply (simp add: add.commute)
  done

lemma liminf_minus_ennreal:
  fixes u v::"nat \<Rightarrow> ennreal"
  shows "(\<And>n. v n \<le> u n) \<Longrightarrow> liminf (\<lambda>n. u n - v n) \<le> limsup u - limsup v"
  unfolding liminf_SUP_INF limsup_INF_SUP
  including ennreal.lifting
proof (transfer, clarsimp)
  fix v u :: "nat \<Rightarrow> ereal" assume *: "\<forall>x. 0 \<le> v x" "\<forall>x. 0 \<le> u x" "\<And>n. v n \<le> u n"
  moreover have "0 \<le> limsup u - limsup v"
    using * by (intro ereal_diff_positive Limsup_mono always_eventually) simp
  moreover have "0 \<le> (SUPREMUM {x..} v)" for x
    using * by (intro SUP_upper2[of x]) auto
  moreover have "0 \<le> (SUPREMUM {x..} u)" for x
    using * by (intro SUP_upper2[of x]) auto
  ultimately show "(SUP n. INF n:{n..}. max 0 (u n - v n))
            \<le> max 0 ((INF x. max 0 (SUPREMUM {x..} u)) - (INF x. max 0 (SUPREMUM {x..} v)))"
    by (auto simp: * ereal_diff_positive max.absorb2 liminf_SUP_INF[symmetric] limsup_INF_SUP[symmetric] ereal_liminf_limsup_minus)
qed

lemma ereal_limsup_lim_mult:
  fixes u v::"nat \<Rightarrow> ereal"
  assumes "u \<longlonglongrightarrow> a" "a>0" "a \<noteq> \<infinity>"
  shows "limsup (\<lambda>n. u n * v n) = a * limsup v"
proof -
  define w where "w = (\<lambda>n. u n * v n)"
  obtain r where r: "subseq r" "(v o r) \<longlonglongrightarrow> limsup v" using limsup_subseq_lim by auto
  have "(u o r) \<longlonglongrightarrow> a" using assms(1) LIMSEQ_subseq_LIMSEQ r by auto
  with tendsto_mult_ereal[OF this r(2)] have "(\<lambda>n. (u o r) n * (v o r) n) \<longlonglongrightarrow> a * limsup v" using assms(2) assms(3) by auto
  moreover have "\<And>n. (w o r) n = (u o r) n * (v o r) n" unfolding w_def by auto
  ultimately have "(w o r) \<longlonglongrightarrow> a * limsup v" unfolding w_def by presburger
  then have "limsup (w o r) = a * limsup v" by (simp add: tendsto_iff_Liminf_eq_Limsup)
  then have I: "limsup w \<ge> a * limsup v" by (metis limsup_subseq_mono r(1))

  obtain s where s: "subseq s" "(w o s) \<longlonglongrightarrow> limsup w" using limsup_subseq_lim by auto
  have *: "(u o s) \<longlonglongrightarrow> a" using assms(1) LIMSEQ_subseq_LIMSEQ s by auto
  have "eventually (\<lambda>n. (u o s) n > 0) sequentially" using assms(2) * order_tendsto_iff by blast
  moreover have "eventually (\<lambda>n. (u o s) n < \<infinity>) sequentially" using assms(3) * order_tendsto_iff by blast
  moreover have "(w o s) n / (u o s) n = (v o s) n" if "(u o s) n > 0" "(u o s) n < \<infinity>" for n
    unfolding w_def using that by (auto simp add: ereal_divide_eq)
  ultimately have "eventually (\<lambda>n. (w o s) n / (u o s) n = (v o s) n) sequentially" using eventually_elim2 by force
  moreover have "(\<lambda>n. (w o s) n / (u o s) n) \<longlonglongrightarrow> (limsup w) / a"
    apply (rule tendsto_divide_ereal[OF s(2) *]) using assms(2) assms(3) by auto
  ultimately have "(v o s) \<longlonglongrightarrow> (limsup w) / a" using Lim_transform_eventually by fastforce
  then have "limsup (v o s) = (limsup w) / a" by (simp add: tendsto_iff_Liminf_eq_Limsup)
  then have "limsup v \<ge> (limsup w) / a" by (metis limsup_subseq_mono s(1))
  then have "a * limsup v \<ge> limsup w" using assms(2) assms(3) by (simp add: ereal_divide_le_pos)
  then show ?thesis using I unfolding w_def by auto
qed

lemma ereal_liminf_lim_mult:
  fixes u v::"nat \<Rightarrow> ereal"
  assumes "u \<longlonglongrightarrow> a" "a>0" "a \<noteq> \<infinity>"
  shows "liminf (\<lambda>n. u n * v n) = a * liminf v"
proof -
  define w where "w = (\<lambda>n. u n * v n)"
  obtain r where r: "subseq r" "(v o r) \<longlonglongrightarrow> liminf v" using liminf_subseq_lim by auto
  have "(u o r) \<longlonglongrightarrow> a" using assms(1) LIMSEQ_subseq_LIMSEQ r by auto
  with tendsto_mult_ereal[OF this r(2)] have "(\<lambda>n. (u o r) n * (v o r) n) \<longlonglongrightarrow> a * liminf v" using assms(2) assms(3) by auto
  moreover have "\<And>n. (w o r) n = (u o r) n * (v o r) n" unfolding w_def by auto
  ultimately have "(w o r) \<longlonglongrightarrow> a * liminf v" unfolding w_def by presburger
  then have "liminf (w o r) = a * liminf v" by (simp add: tendsto_iff_Liminf_eq_Limsup)
  then have I: "liminf w \<le> a * liminf v" by (metis liminf_subseq_mono r(1))

  obtain s where s: "subseq s" "(w o s) \<longlonglongrightarrow> liminf w" using liminf_subseq_lim by auto
  have *: "(u o s) \<longlonglongrightarrow> a" using assms(1) LIMSEQ_subseq_LIMSEQ s by auto
  have "eventually (\<lambda>n. (u o s) n > 0) sequentially" using assms(2) * order_tendsto_iff by blast
  moreover have "eventually (\<lambda>n. (u o s) n < \<infinity>) sequentially" using assms(3) * order_tendsto_iff by blast
  moreover have "(w o s) n / (u o s) n = (v o s) n" if "(u o s) n > 0" "(u o s) n < \<infinity>" for n
    unfolding w_def using that by (auto simp add: ereal_divide_eq)
  ultimately have "eventually (\<lambda>n. (w o s) n / (u o s) n = (v o s) n) sequentially" using eventually_elim2 by force
  moreover have "(\<lambda>n. (w o s) n / (u o s) n) \<longlonglongrightarrow> (liminf w) / a"
    apply (rule tendsto_divide_ereal[OF s(2) *]) using assms(2) assms(3) by auto
  ultimately have "(v o s) \<longlonglongrightarrow> (liminf w) / a" using Lim_transform_eventually by fastforce
  then have "liminf (v o s) = (liminf w) / a" by (simp add: tendsto_iff_Liminf_eq_Limsup)
  then have "liminf v \<le> (liminf w) / a" by (metis liminf_subseq_mono s(1))
  then have "a * liminf v \<le> liminf w" using assms(2) assms(3) by (simp add: ereal_le_divide_pos)
  then show ?thesis using I unfolding w_def by auto
qed


subsection {*Nonnegative-extended-real.thy*}

lemma e2ennreal_mult:
  fixes a b::ereal
  assumes "a \<ge> 0"
  shows "e2ennreal(a * b) = e2ennreal a * e2ennreal b"
by (metis assms e2ennreal_neg eq_onp_same_args ereal_mult_le_0_iff linear times_ennreal.abs_eq)

lemma e2ennreal_mult':
  fixes a b::ereal
  assumes "b \<ge> 0"
  shows "e2ennreal(a * b) = e2ennreal a * e2ennreal b"
using e2ennreal_mult[OF assms, of a] by (simp add: mult.commute)

lemma SUP_real_ennreal:
  assumes "A \<noteq> {}" "bdd_above (f`A)"
  shows "(SUP a:A. ennreal (f a)) = ennreal(SUP a:A. f a)"
apply (rule antisym, simp add: SUP_least assms(2) cSUP_upper ennreal_leI)
by (metis assms(1) ennreal_SUP ennreal_less_top le_less)

lemma ennreal_Inf_cmult:
  assumes "c>(0::real)"
  shows "Inf {ennreal c * x |x. P x} = ennreal c * Inf {x. P x}"
proof -
  have "(\<lambda>x::ennreal. c * x) (Inf {x::ennreal. P x}) = Inf ((\<lambda>x::ennreal. c * x)`{x::ennreal. P x})"
    apply (rule mono_bij_Inf)
    apply (simp add: monoI mult_left_mono)
    apply (rule bij_betw_byWitness[of _ "\<lambda>x. (x::ennreal) / c"], auto simp add: assms)
    apply (metis assms ennreal_lessI ennreal_neq_top mult.commute mult_divide_eq_ennreal not_less_zero)
    apply (metis assms divide_ennreal_def ennreal_less_zero_iff ennreal_neq_top less_irrefl mult.assoc mult.left_commute mult_divide_eq_ennreal)
    done
  then show ?thesis by (simp only: setcompr_eq_image[symmetric])
qed

lemma continuous_on_const_minus_ennreal:
  fixes f :: "'a :: topological_space \<Rightarrow> ennreal"
  shows "continuous_on A f \<Longrightarrow> continuous_on A (\<lambda>x. a - f x)"
  including ennreal.lifting
proof (transfer fixing: A; clarsimp)
  fix f :: "'a \<Rightarrow> ereal" and a :: "ereal" assume "0 \<le> a" "\<forall>x. 0 \<le> f x" and f: "continuous_on A f"
  then show "continuous_on A (\<lambda>x. max 0 (a - f x))"
  proof cases
    assume "\<exists>r. a = ereal r"
    with f show ?thesis
      by (auto simp: continuous_on_def minus_ereal_def ereal_Lim_uminus[symmetric]
              intro!: tendsto_add_ereal_general tendsto_max)
  next
    assume "\<nexists>r. a = ereal r"
    with \<open>0 \<le> a\<close> have "a = \<infinity>"
      by (cases a) auto
    then show ?thesis
      by (simp add: continuous_on_const)
  qed
qed

lemma const_minus_Liminf_ennreal:
  fixes a :: ennreal
  shows "F \<noteq> bot \<Longrightarrow> a - Liminf F f = Limsup F (\<lambda>x. a - f x)"
by (intro Limsup_compose_continuous_antimono[symmetric])
   (auto simp: antimono_def ennreal_mono_minus continuous_on_id continuous_on_const_minus_ennreal)

lemma tendsto_mult_ennreal [tendsto_intros]:
  fixes f g::"_ \<Rightarrow> ennreal"
  assumes "(f \<longlongrightarrow> l) F" "(g \<longlongrightarrow> m) F" "\<not>((l = 0 \<and> m = \<infinity>) \<or> (m = 0 \<and> l = \<infinity>))"
  shows "((\<lambda>x. f x * g x) \<longlongrightarrow> l * m) F"
proof -
  have "((\<lambda>x. enn2ereal(f x) * enn2ereal(g x)) \<longlongrightarrow> enn2ereal l * enn2ereal m) F"
    apply (auto intro!: tendsto_intros simp add: assms)
    by (insert assms le_zero_eq less_eq_ennreal.rep_eq, fastforce)+
  then have "((\<lambda>x. enn2ereal(f x * g x)) \<longlongrightarrow> enn2ereal(l * m)) F"
    using times_ennreal.rep_eq by auto
  then show ?thesis
    by (auto intro!: tendsto_intros)
qed

lemma tendsto_cmult_ennreal [tendsto_intros]:
  fixes c l::ennreal
  assumes "\<not>(c = \<infinity> \<and> l = 0)"
          "(f \<longlongrightarrow> l) F"
  shows "((\<lambda>x. c * f x) \<longlongrightarrow> c * l) F"
by (cases "c = 0", insert assms, auto intro!: tendsto_intros)


subsection {*Indicator.thy*}

text {*There is something weird with \verb+sum_mult_indicator+: it is defined both
in Indicator.thy and BochnerIntegration.thy, with a different meaning. I am surprised
there is no name collision... Here, I am using the version from BochnerIntegration.*}

lemma sum_indicator_eq_card2:
  assumes "finite I"
  shows "(\<Sum>i\<in>I. (indicator (P i) x)::nat) = card {i\<in>I. x \<in> P i}"
using sum_mult_indicator [OF assms, of "\<lambda>y. 1::nat" P "\<lambda>y. x"]
unfolding card_eq_sum by auto


subsection {*sigma-algebra.thy*}

lemma algebra_intersection:
  assumes "algebra \<Omega> A"
          "algebra \<Omega> B"
  shows "algebra \<Omega> (A \<inter> B)"
apply (subst algebra_iff_Un) using assms by (auto simp add: algebra_iff_Un)

lemma sigma_algebra_intersection:
  assumes "sigma_algebra \<Omega> A"
          "sigma_algebra \<Omega> B"
  shows "sigma_algebra \<Omega> (A \<inter> B)"
apply (subst sigma_algebra_iff) using assms by (auto simp add: sigma_algebra_iff algebra_intersection)

text {* The next one is \verb+disjoint_family_Suc+ with inclusions reversed.*}

lemma disjoint_family_Suc2:
  assumes Suc: "\<And>n. A (Suc n) \<subseteq> A n"
  shows "disjoint_family (\<lambda>i. A i - A (Suc i))"
proof -
  have "A (m+n) \<subseteq> A n" for m n
  proof (induct m)
    case 0 show ?case by simp
  next
    case (Suc m) then show ?case
      by (metis Suc_eq_plus1 assms add.commute add.left_commute subset_trans)
  qed
  then have "A m \<subseteq> A n" if "m > n" for m n
    by (metis that add.commute le_add_diff_inverse nat_less_le)
  then show ?thesis
    by (auto simp add: disjoint_family_on_def)
       (metis insert_absorb insert_subset le_SucE le_antisym not_le_imp_less)
qed

text {* the next few lemmas give useful measurability statements*}

text {* The next one is a reformulation of \verb+borel_measurable_Max+.*}

lemma borel_measurable_Max2[measurable (raw)]:
  fixes f::"_ \<Rightarrow> _ \<Rightarrow> 'a::{second_countable_topology, dense_linorder, linorder_topology}"
  assumes "finite I"
    and [measurable]: "\<And>i. f i \<in> borel_measurable M"
  shows "(\<lambda>x. Max{f i x |i. i \<in> I}) \<in> borel_measurable M"
by (simp add: borel_measurable_Max[OF assms(1), where ?f=f and ?M=M] Setcompr_eq_image)

lemma measurable_compose_n [measurable (raw)]:
  assumes "T \<in> measurable M M"
  shows "(T^^n) \<in> measurable M M"
by (induction n, auto simp add: measurable_compose[OF _ assms])

lemma measurable_real_imp_nat:
  fixes f::"'a \<Rightarrow> nat"
  assumes [measurable]: "(\<lambda>x. real(f x)) \<in> borel_measurable M"
  shows "f \<in> measurable M (count_space UNIV)"
proof -
  let ?g = "(\<lambda>x. real(f x))"
  have "\<And>(n::nat). ?g-`({real n}) \<inter> space M = f-`{n} \<inter> space M" by auto
  moreover have "\<And>(n::nat). ?g-`({real n}) \<inter> space M \<in> sets M" using assms by measurable
  ultimately have "\<And>(n::nat). f-`{n} \<inter> space M \<in> sets M" by simp
  then show ?thesis using measurable_count_space_eq2_countable by blast
qed

lemma measurable_equality_set [measurable]:
  fixes f g::"_\<Rightarrow> 'a::{second_countable_topology, t2_space}"
  assumes [measurable]: "f \<in> borel_measurable M" "g \<in> borel_measurable M"
  shows "{x \<in> space M. f x = g x} \<in> sets M"
proof -
  define A where "A = {x \<in> space M. f x = g x}"
  define B where "B = {y. \<exists>x::'a. y = (x,x)}"
  have "A = (\<lambda>x. (f x, g x))-`B \<inter> space M" unfolding A_def B_def by auto
  moreover have "(\<lambda>x. (f x, g x)) \<in> borel_measurable M" by simp
  moreover have "B \<in> sets borel" unfolding B_def by (simp add: closed_diagonal)
  ultimately have "A \<in> sets M" by simp
  then show ?thesis unfolding A_def by simp
qed

lemma measurable_inequality_set [measurable]:
  fixes f g::"_ \<Rightarrow> 'a::{second_countable_topology, linorder_topology}"
  assumes [measurable]: "f \<in> borel_measurable M" "g \<in> borel_measurable M"
  shows "{x \<in> space M. f x \<le> g x} \<in> sets M"
        "{x \<in> space M. f x < g x} \<in> sets M"
        "{x \<in> space M. f x \<ge> g x} \<in> sets M"
        "{x \<in> space M. f x > g x} \<in> sets M"
proof -
  define F where "F = (\<lambda>x. (f x, g x))"
  have * [measurable]: "F \<in> borel_measurable M" unfolding F_def by simp

  have "{x \<in> space M. f x \<le> g x} = F-`{(x, y) | x y. x \<le> y} \<inter> space M" unfolding F_def by auto
  moreover have "{(x, y) | x y. x \<le> (y::'a)} \<in> sets borel" using closed_subdiagonal borel_closed by blast
  ultimately show "{x \<in> space M. f x \<le> g x} \<in> sets M" using * by (metis (mono_tags, lifting) measurable_sets)

  have "{x \<in> space M. f x < g x} = F-`{(x, y) | x y. x < y} \<inter> space M" unfolding F_def by auto
  moreover have "{(x, y) | x y. x < (y::'a)} \<in> sets borel" using open_subdiagonal borel_open by blast
  ultimately show "{x \<in> space M. f x < g x} \<in> sets M" using * by (metis (mono_tags, lifting) measurable_sets)

  have "{x \<in> space M. f x \<ge> g x} = F-`{(x, y) | x y. x \<ge> y} \<inter> space M" unfolding F_def by auto
  moreover have "{(x, y) | x y. x \<ge> (y::'a)} \<in> sets borel" using closed_superdiagonal borel_closed by blast
  ultimately show "{x \<in> space M. f x \<ge> g x} \<in> sets M" using * by (metis (mono_tags, lifting) measurable_sets)

  have "{x \<in> space M. f x > g x} = F-`{(x, y) | x y. x > y} \<inter> space M" unfolding F_def by auto
  moreover have "{(x, y) | x y. x > (y::'a)} \<in> sets borel" using open_superdiagonal borel_open by blast
  ultimately show "{x \<in> space M. f x > g x} \<in> sets M" using * by (metis (mono_tags, lifting) measurable_sets)
qed

lemma measurable_limit [measurable]:
  fixes f::"nat \<Rightarrow> 'a \<Rightarrow> 'b::first_countable_topology"
  assumes [measurable]: "\<And>n::nat. f n \<in> borel_measurable M"
  shows "Measurable.pred M (\<lambda>x. (\<lambda>n. f n x) \<longlonglongrightarrow> c)"
proof -
  obtain A :: "nat \<Rightarrow> 'b set" where A:
    "\<And>i. open (A i)"
    "\<And>i. c \<in> A i"
    "\<And>S. open S \<Longrightarrow> c \<in> S \<Longrightarrow> eventually (\<lambda>i. A i \<subseteq> S) sequentially"
  by (rule countable_basis_at_decseq) blast

  have [measurable]: "\<And>N i. (f N)-`(A i) \<inter> space M \<in> sets M" using A(1) by auto
  then have mes: "(\<Inter>i. \<Union>n. \<Inter>N\<in>{n..}. (f N)-`(A i) \<inter> space M) \<in> sets M" by blast

  have "(u \<longlonglongrightarrow> c) \<longleftrightarrow> (\<forall>i. eventually (\<lambda>n. u n \<in> A i) sequentially)" for u::"nat \<Rightarrow> 'b"
  proof
    assume "u \<longlonglongrightarrow> c"
    then have "eventually (\<lambda>n. u n \<in> A i) sequentially" for i using A(1)[of i] A(2)[of i]
      by (simp add: topological_tendstoD)
    then show "(\<forall>i. eventually (\<lambda>n. u n \<in> A i) sequentially)" by auto
  next
    assume H: "(\<forall>i. eventually (\<lambda>n. u n \<in> A i) sequentially)"
    show "(u \<longlonglongrightarrow> c)"
    proof (rule topological_tendstoI)
      fix S assume "open S" "c \<in> S"
      with A(3)[OF this] obtain i where "A i \<subseteq> S"
        using eventually_False_sequentially eventually_mono by blast
      moreover have "eventually (\<lambda>n. u n \<in> A i) sequentially" using H by simp
      ultimately show "\<forall>\<^sub>F n in sequentially. u n \<in> S"
        by (simp add: eventually_mono subset_eq)
    qed
  qed
  then have "{x. (\<lambda>n. f n x) \<longlonglongrightarrow> c} = (\<Inter>i. \<Union>n. \<Inter>N\<in>{n..}. (f N)-`(A i))"
    by (auto simp add: atLeast_def eventually_at_top_linorder)
  then have "{x \<in> space M. (\<lambda>n. f n x) \<longlonglongrightarrow> c} = (\<Inter>i. \<Union>n. \<Inter>N\<in>{n..}. (f N)-`(A i) \<inter> space M)"
    by auto
  then have "{x \<in> space M. (\<lambda>n. f n x) \<longlonglongrightarrow> c} \<in> sets M" using mes by simp
  then show ?thesis by auto
qed

lemma measurable_limit2 [measurable]:
  fixes u::"nat \<Rightarrow> 'a \<Rightarrow> real"
  assumes [measurable]: "\<And>n. u n \<in> borel_measurable M" "v \<in> borel_measurable M"
  shows "Measurable.pred M (\<lambda>x. (\<lambda>n. u n x) \<longlonglongrightarrow> v x)"
proof -
  define w where "w = (\<lambda>n x. u n x - v x)"
  have [measurable]: "w n \<in> borel_measurable M" for n unfolding w_def by auto
  have "((\<lambda>n. u n x) \<longlonglongrightarrow> v x) \<longleftrightarrow> ((\<lambda>n. w n x) \<longlonglongrightarrow> 0)" for x
    unfolding w_def using Lim_null by auto
  then show ?thesis using measurable_limit by auto
qed

lemma measurable_P_restriction [measurable (raw)]:
  assumes [measurable]: "Measurable.pred M P" "A \<in> sets M"
  shows "{x \<in> A. P x} \<in> sets M"
proof -
  have "A \<subseteq> space M" using sets.sets_into_space[OF assms(2)].
  then have "{x \<in> A. P x} = A \<inter> {x \<in> space M. P x}" by blast
  then show ?thesis by auto
qed

lemma measurable_sum_nat [measurable (raw)]:
  fixes f :: "'c \<Rightarrow> 'a \<Rightarrow> nat"
  assumes "\<And>i. i \<in> S \<Longrightarrow> f i \<in> measurable M (count_space UNIV)"
  shows "(\<lambda>x. \<Sum>i\<in>S. f i x) \<in> measurable M (count_space UNIV)"
proof cases
  assume "finite S"
  then show ?thesis using assms by induct auto
qed simp


lemma measurable_abs_powr [measurable]:
  fixes p::real
  assumes [measurable]: "f \<in> borel_measurable M"
  shows "(\<lambda>x. \<bar>f x\<bar> powr p) \<in> borel_measurable M"
unfolding powr_def by auto

text {* The next one is a variation around \verb+measurable_restrict_space+.*}

lemma measurable_restrict_space3:
  assumes "f \<in> measurable M N" and
          "f \<in> A \<rightarrow> B"
  shows "f \<in> measurable (restrict_space M A) (restrict_space N B)"
proof -
  have "f \<in> measurable (restrict_space M A) N" using assms(1) measurable_restrict_space1 by auto
  then show ?thesis by (metis Int_iff funcsetI funcset_mem
      measurable_restrict_space2[of f, of "restrict_space M A", of B, of N] assms(2) space_restrict_space)
qed

text {* The next one is a variation around \verb+measurable_piecewise_restrict+.*}

lemma measurable_piecewise_restrict2:
  assumes [measurable]: "\<And>n. A n \<in> sets M"
      and "space M = (\<Union>(n::nat). A n)"
          "\<And>n. \<exists>h \<in> measurable M N. (\<forall>x \<in> A n. f x = h x)"
  shows "f \<in> measurable M N"
proof (rule measurableI)
  fix B assume [measurable]: "B \<in> sets N"
  {
    fix n::nat
    obtain h where [measurable]: "h \<in> measurable M N" and "\<forall>x \<in> A n. f x = h x" using assms(3) by blast
    then have *: "f-`B \<inter> A n = h-`B \<inter> A n" by auto
    have "h-`B \<inter> A n = h-`B \<inter> space M \<inter> A n" using assms(2) sets.sets_into_space by auto
    then have "h-`B \<inter> A n \<in> sets M" by simp
    then have "f-`B \<inter> A n \<in> sets M" using * by simp
  }
  then have "(\<Union>n. f-`B \<inter> A n) \<in> sets M" by measurable
  moreover have "f-`B \<inter> space M = (\<Union>n. f-`B \<inter> A n)" using assms(2) by blast
  ultimately show "f-`B \<inter> space M \<in> sets M" by simp
next
  fix x assume "x \<in> space M"
  then obtain n where "x \<in> A n" using assms(2) by blast
  obtain h where [measurable]: "h \<in> measurable M N" and "\<forall>x \<in> A n. f x = h x" using assms(3) by blast
  then have "f x = h x" using `x \<in> A n` by blast
  moreover have "h x \<in> space N" by (metis measurable_space `x \<in> space M` `h \<in> measurable M N`)
  ultimately show "f x \<in> space N" by simp
qed


subsection {*Measure-Space.thy *}

lemma emeasure_union_inter:
  assumes "A \<in> sets M" "B \<in> sets M"
  shows "emeasure M A + emeasure M B = emeasure M (A \<union> B) + emeasure M (A \<inter> B)"
proof -
  have "A = (A-B) \<union> (A \<inter> B)" by auto
  then have 1: "emeasure M A = emeasure M (A-B) + emeasure M (A \<inter> B)"
    by (metis Diff_Diff_Int Diff_disjoint assms(1) assms(2) plus_emeasure sets.Diff)

  have "A \<union> B = (A-B) \<union> B" by auto
  then have 2: "emeasure M (A \<union> B) = emeasure M (A-B) + emeasure M B"
    by (metis Diff_disjoint Int_commute assms(1) assms(2) plus_emeasure sets.Diff)

  show ?thesis using 1 2 by (metis add.assoc add.commute)
qed

lemma AE_equal_sum:
  assumes "\<And>i. AE x in M. f i x = g i x"
  shows "AE x in M. (\<Sum>i\<in>I. f i x) = (\<Sum>i\<in>I. g i x)"
proof (cases)
  assume "finite I"
  have "\<exists>A. A \<in> null_sets M \<and> (\<forall>x\<in> (space M - A). f i x = g i x)" for i
    using assms(1)[of i] by (metis (mono_tags, lifting) AE_E3)
  then obtain A where A: "\<And>i. A i \<in> null_sets M \<and> (\<forall>x\<in> (space M -A i). f i x = g i x)"
    by metis
  define B where "B = (\<Union>i\<in>I. A i)"
  have "B \<in> null_sets M" using `finite I` A B_def by blast
  then have "AE x in M. x \<in> space M - B" by (simp add: AE_not_in)
  moreover
  {
    fix x assume "x \<in> space M - B"
    then have "\<And>i. i \<in> I \<Longrightarrow> f i x = g i x" unfolding B_def using A by auto
    then have "(\<Sum>i\<in>I. f i x) = (\<Sum>i\<in>I. g i x)" by auto
  }
  ultimately show ?thesis by auto
qed (simp)

lemma emeasure_pos_unionE:
  assumes "\<And> (N::nat). A N \<in> sets M"
          "emeasure M (\<Union>N. A N) > 0"
  shows "\<exists>N. emeasure M (A N) > 0"
proof (rule ccontr)
  assume "\<not>(\<exists>N. emeasure M (A N) > 0)"
  then have "\<And>N. A N \<in> null_sets M"
    using assms(1) by auto
  then have "(\<Union>N. A N) \<in> null_sets M" by auto
  then show False using assms(2) by auto
qed

lemma (in prob_space) emeasure_intersection:
  fixes e::"nat \<Rightarrow> real"
  assumes [measurable]: "\<And>n. U n \<in> sets M"
      and [simp]: "\<And>n. 0 \<le> e n" "summable e"
      and ge: "\<And>n. emeasure M (U n) \<ge> 1 - (e n)"
  shows "emeasure M (\<Inter>n. U n) \<ge> 1 - (\<Sum>n. e n)"
proof -
  define V where "V = (\<lambda>n. space M - (U n))"
  have [measurable]: "V n \<in> sets M" for n
    unfolding V_def by auto
  have *: "emeasure M (V n) \<le> e n" for n
    unfolding V_def using ge[of n] by (simp add: emeasure_eq_measure prob_compl ennreal_leI)
  have "emeasure M (\<Union>n. V n) \<le> (\<Sum>n. emeasure M (V n))"
    by (rule emeasure_subadditive_countably, auto)
  also have "... \<le> (\<Sum>n. ennreal (e n))"
    using * by (intro suminf_le) auto
  also have "... = ennreal (\<Sum>n. e n)"
    by (intro suminf_ennreal_eq) auto
  finally have "emeasure M (\<Union>n. V n) \<le> suminf e" by simp
  then have "1 - suminf e \<le> emeasure M (space M - (\<Union>n. V n))"
    by (simp add: emeasure_eq_measure prob_compl suminf_nonneg)
  also have "... \<le> emeasure M (\<Inter>n. U n)"
    by (rule emeasure_mono) (auto simp: V_def)
  finally show ?thesis by simp
qed

lemma (in sigma_finite_measure) approx_PInf_emeasure_with_finite:
  fixes C::real
  assumes W_meas: "W \<in> sets M"
      and W_inf: "emeasure M W = \<infinity>"
  obtains Z where "Z \<in> sets M" "Z \<subseteq> W" "emeasure M Z < \<infinity>" "emeasure M Z > C"
proof -
  obtain A :: "nat \<Rightarrow> 'a set"
    where A: "range A \<subseteq> sets M" "(\<Union>i. A i) = space M" "\<And>i. emeasure M (A i) \<noteq> \<infinity>" "incseq A"
    using sigma_finite_incseq by blast
  define B where "B = (\<lambda>i. W \<inter> A i)"
  have B_meas: "\<And>i. B i \<in> sets M" using W_meas `range A \<subseteq> sets M` B_def by blast
  have b: "\<And>i. B i \<subseteq> W" using B_def by blast

  { fix i
    have "emeasure M (B i) \<le> emeasure M (A i)"
      using A by (intro emeasure_mono) (auto simp: B_def)
    also have "emeasure M (A i) < \<infinity>"
      using `\<And>i. emeasure M (A i) \<noteq> \<infinity>` by (simp add: less_top)
    finally have "emeasure M (B i) < \<infinity>" . }
  note c = this

  have "W = (\<Union>i. B i)" using B_def `(\<Union>i. A i) = space M` W_meas by auto
  moreover have "incseq B" using B_def `incseq A` by (simp add: incseq_def subset_eq)
  ultimately have "(\<lambda>i. emeasure M (B i)) \<longlonglongrightarrow> emeasure M W" using W_meas B_meas
    by (simp add: B_meas Lim_emeasure_incseq image_subset_iff)
  then have "(\<lambda>i. emeasure M (B i)) \<longlonglongrightarrow> \<infinity>" using W_inf by simp
  from order_tendstoD(1)[OF this, of C]
  obtain i where d: "emeasure M (B i) > C"
    by (auto simp: eventually_sequentially)
  have "B i \<in> sets M" "B i \<subseteq> W" "emeasure M (B i) < \<infinity>" "emeasure M (B i) > C"
    using B_meas b c d by auto
  then show ?thesis using that by blast
qed


lemma null_sets_inc:
  assumes "A \<in> null_sets M" "B \<in> sets M" "B \<subseteq> A"
  shows "B \<in> null_sets M"
by (metis Int_absorb1 assms(1) assms(2) assms(3) null_set_Int2)

lemma null_sym_diff_transitive:
  assumes "A \<Delta> B \<in> null_sets M" "B \<Delta> C \<in> null_sets M"
      and [measurable]: "A \<in> sets M" "C \<in> sets M"
  shows "A \<Delta> C \<in> null_sets M"
proof -
  have "A \<Delta> B \<union> B \<Delta> C \<in> null_sets M" using assms(1) assms(2) by auto
  moreover have "A \<Delta> C \<subseteq> A \<Delta> B \<union> B \<Delta> C" by auto
  ultimately show ?thesis by (meson null_sets_inc assms(3) assms(4) sets.Diff sets.Un)
qed

lemma Delta_null_of_null_is_null:
  assumes "B \<in> sets M" "A \<Delta> B \<in> null_sets M" "A \<in> null_sets M"
  shows "B \<in> null_sets M"
proof -
  have "B \<subseteq> A \<union> (A \<Delta> B)" by auto
  then show ?thesis using assms by (meson null_sets.Un null_sets_inc)
qed

lemma Delta_null_same_emeasure:
  assumes "A \<Delta> B \<in> null_sets M" and [measurable]: "A \<in> sets M" "B \<in> sets M"
  shows "emeasure M A = emeasure M B"
proof -
  have "A = (A \<inter> B) \<union> (A-B)" by blast
  moreover have "A-B \<in> null_sets M" using assms null_sets_inc by blast
  ultimately have a: "emeasure M A = emeasure M (A \<inter> B)" using emeasure_Un_null_set by (metis assms(2) assms(3) sets.Int)

  have "B = (A \<inter> B) \<union> (B-A)" by blast
  moreover have "B-A \<in> null_sets M" using assms null_sets_inc by blast
  ultimately have "emeasure M B = emeasure M (A \<inter> B)" using emeasure_Un_null_set by (metis assms(2) assms(3) sets.Int)
  then show ?thesis using a by auto
qed

lemma AE_upper_bound_inf_ereal:
  fixes F G::"'a \<Rightarrow> ereal"
  assumes "\<And>e. (e::real) > 0 \<Longrightarrow> AE x in M. F x \<le> G x + e"
  shows "AE x in M. F x \<le> G x"
proof -
  have "AE x in M. \<forall>n::nat. F x \<le> G x + ereal (1 / Suc n)"
    using assms by (auto simp: AE_all_countable)
  then show ?thesis
  proof (eventually_elim)
    fix x assume x: "\<forall>n::nat. F x \<le> G x + ereal (1 / Suc n)"
    show "F x \<le> G x"
    proof (intro ereal_le_epsilon2[of _ "G x"] allI impI)
      fix e :: real assume "0 < e"
      then obtain n where n: "1 / Suc n < e"
        by (blast elim: nat_approx_posE)
      have "F x \<le> G x + 1 / Suc n"
        using x by simp
      also have "\<dots> \<le> G x + e"
        using n by (intro add_mono ennreal_leI) auto
      finally show "F x \<le> G x + ereal e" .
    qed
  qed
qed

subsection {*Nonnegative-Lebesgue-Integration.thy*}

text{* The next lemma is a variant of \verb+nn_integral_density+,
with the density on the right instead of the left, as seems more common. *}

lemma nn_integral_densityR:
  assumes [measurable]: "f \<in> borel_measurable F" "g \<in> borel_measurable F" and
          "AE x in F. g x \<ge> 0"
  shows "(\<integral>\<^sup>+ x. f x * g x \<partial>F) = (\<integral>\<^sup>+ x. f x \<partial>(density F g))"
proof -
  have "(\<integral>\<^sup>+ x. f x * g x \<partial>F) = (\<integral>\<^sup>+ x. g x * f x \<partial>F)" by (simp add: mult.commute)
  also have "... = (\<integral>\<^sup>+ x. f x \<partial>(density F g))"
    by (rule nn_integral_density[symmetric], simp_all add: assms)
  finally show ?thesis by simp
qed

lemma not_AE_zero_int_ennreal_E:
  fixes f::"'a \<Rightarrow> ennreal"
  assumes "(\<integral>\<^sup>+x. f x \<partial>M) > 0"
      and [measurable]: "f \<in> borel_measurable M"
  shows "\<exists>A\<in>sets M. \<exists>e::real>0. emeasure M A > 0 \<and> (\<forall>x \<in> A. f x \<ge> e)"
proof (rule not_AE_zero_ennreal_E, auto simp add: assms)
  assume *: "AE x in M. f x = 0"
  have "(\<integral>\<^sup>+x. f x \<partial>M) = (\<integral>\<^sup>+x. 0 \<partial>M)" by (rule nn_integral_cong_AE, simp add: *)
  then have "(\<integral>\<^sup>+x. f x \<partial>M) = 0" by simp
  then show False using assms by simp
qed

lemma (in finite_measure) nn_integral_bounded_eq_bound_then_AE:
  assumes "AE x in M. f x \<le> ennreal c" "(\<integral>\<^sup>+x. f x \<partial>M) = c * emeasure M (space M)"
      and [measurable]: "f \<in> borel_measurable M"
  shows "AE x in M. f x = c"
proof (cases)
  assume "emeasure M (space M) = 0"
  then show ?thesis by (rule emeasure_0_AE)
next
  assume "emeasure M (space M) \<noteq> 0"
  have fin: "AE x in M. f x \<noteq> top" using assms by (auto simp: top_unique)
  define g where "g = (\<lambda>x. c - f x)"
  have [measurable]: "g \<in> borel_measurable M" unfolding g_def by auto
  have "(\<integral>\<^sup>+x. g x \<partial>M) = (\<integral>\<^sup>+x. c \<partial>M) - (\<integral>\<^sup>+x. f x \<partial>M)"
    unfolding g_def by (rule nn_integral_diff, auto simp add: assms ennreal_mult_eq_top_iff)
  also have "\<dots> = 0" using assms(2) by (auto simp: ennreal_mult_eq_top_iff)
  finally have "AE x in M. g x = 0"
    by (subst nn_integral_0_iff_AE[symmetric]) auto
  then have "AE x in M. c \<le> f x" unfolding g_def using fin by (auto simp: ennreal_minus_eq_0)
  then show ?thesis using assms(1) by auto
qed


subsection {*Lebesgue-Measure.thy*}

text{* The next lemma is the same as \verb+lborel_distr_plus+ which is only formulated
on the real line, but on any euclidean space *}

lemma lborel_distr_plus2:
  fixes c :: "'a::euclidean_space"
  shows "distr lborel borel (op + c) = lborel"
by (subst lborel_affine[of 1 c], auto simp: density_1)



text{* I introduce a notation for positive set integrals, which is not available in
\verb+Set_Integral.thy+. The notation I use is not directly in line with the
notations in this file, they are more in line with sum, and more readable I think. *}

abbreviation "set_nn_integral M A f \<equiv> nn_integral M (\<lambda>x. f x * indicator A x)"

syntax
"_set_nn_integral" :: "pttrn => 'a set => 'a measure => ereal => ereal"
("(\<integral>\<^sup>+((_)\<in>(_)./ _)/\<partial>_)" [0,60,110,61] 60)

"_set_lebesgue_integral" :: "pttrn => 'a set => 'a measure => ereal => ereal"
("(\<integral>((_)\<in>(_)./ _)/\<partial>_)" [0,60,110,61] 60)

translations
"\<integral>\<^sup>+x \<in> A. f \<partial>M" == "CONST set_nn_integral M A (\<lambda>x. f)"
"\<integral>x \<in> A. f \<partial>M" == "CONST set_lebesgue_integral M A (\<lambda>x. f)"

lemma nn_integral_disjoint_pair:
  assumes [measurable]: "f \<in> borel_measurable M"
          "B \<in> sets M" "C \<in> sets M"
          "B \<inter> C = {}"
  shows "(\<integral>\<^sup>+x \<in> B \<union> C. f x \<partial>M) = (\<integral>\<^sup>+x \<in> B. f x \<partial>M) + (\<integral>\<^sup>+x \<in> C. f x \<partial>M)"
proof -
  have mes: "\<And>D. D \<in> sets M \<Longrightarrow> (\<lambda>x. f x * indicator D x) \<in> borel_measurable M" by simp
  have pos: "\<And>D. AE x in M. f x * indicator D x \<ge> 0" using assms(2) by auto
  have "\<And>x. f x * indicator (B \<union> C) x = f x * indicator B x + f x * indicator C x" using assms(4)
    by (auto split: split_indicator)
  then have "(\<integral>\<^sup>+x. f x * indicator (B \<union> C) x \<partial>M) = (\<integral>\<^sup>+x. f x * indicator B x + f x * indicator C x \<partial>M)"
    by simp
  also have "... = (\<integral>\<^sup>+x. f x * indicator B x \<partial>M) + (\<integral>\<^sup>+x. f x * indicator C x \<partial>M)"
    by (rule nn_integral_add) (auto simp add: assms mes pos)
  finally show ?thesis by simp
qed

lemma nn_integral_disjoint_pair_countspace:
  assumes "B \<inter> C = {}"
  shows "(\<integral>\<^sup>+x \<in> B \<union> C. f x \<partial>count_space UNIV) = (\<integral>\<^sup>+x \<in> B. f x \<partial>count_space UNIV) + (\<integral>\<^sup>+x \<in> C. f x \<partial>count_space UNIV)"
by (rule nn_integral_disjoint_pair) (simp_all add: assms)

lemma nn_integral_null_delta:
  assumes "A \<in> sets M" "B \<in> sets M"
          "A \<Delta> B \<in> null_sets M"
  shows "(\<integral>\<^sup>+x \<in> A. f x \<partial>M) = (\<integral>\<^sup>+x \<in> B. f x \<partial>M)"
proof (rule nn_integral_cong_AE, auto simp add: indicator_def)
  have *: "AE a in M. a \<notin> A \<Delta> B"
    using assms(3) AE_not_in by blast
  then show "AE a in M. a \<notin> A \<longrightarrow> a \<in> B \<longrightarrow> f a = 0"
    by auto
  show "AE x\<in>A in M. x \<notin> B \<longrightarrow> f x = 0"
    using * by auto
qed

lemma nn_integral_disjoint_family:
  assumes [measurable]: "f \<in> borel_measurable M" "\<And>(n::nat). B n \<in> sets M"
      and "disjoint_family B"
  shows "(\<integral>\<^sup>+x \<in> (\<Union>n. B n). f x \<partial>M) = (\<Sum>n. (\<integral>\<^sup>+x \<in> B n. f x \<partial>M))"
proof -
  have "(\<integral>\<^sup>+ x. (\<Sum>n. f x * indicator (B n) x) \<partial>M) = (\<Sum>n. (\<integral>\<^sup>+ x. f x * indicator (B n) x \<partial>M))"
    by (rule nn_integral_suminf) simp
  moreover have "(\<Sum>n. f x * indicator (B n) x) = f x * indicator (\<Union>n. B n) x" for x
  proof (cases)
    assume "x \<in> (\<Union>n. B n)"
    then obtain n where "x \<in> B n" by blast
    have a: "finite {n}" by simp
    have "\<And>i. i \<noteq> n \<Longrightarrow> x \<notin> B i" using `x \<in> B n` assms(3) disjoint_family_on_def
      by (metis IntI UNIV_I empty_iff)
    then have "\<And>i. i \<notin> {n} \<Longrightarrow> indicator (B i) x = (0::ennreal)" using indicator_def by simp
    then have b: "\<And>i. i \<notin> {n} \<Longrightarrow> f x * indicator (B i) x = (0::ennreal)" by simp

    define h where "h = (\<lambda>i. f x * indicator (B i) x)"
    then have "\<And>i. i \<notin> {n} \<Longrightarrow> h i = 0" using b by simp
    then have "(\<Sum>i. h i) = (\<Sum>i\<in>{n}. h i)"
      by (metis sums_unique[OF sums_finite[OF a]])
    then have "(\<Sum>i. h i) = h n" by simp
    then have "(\<Sum>n. f x * indicator (B n) x) = f x * indicator (B n) x" using h_def by simp
    then have "(\<Sum>n. f x * indicator (B n) x) = f x" using `x \<in> B n` indicator_def by simp
    then show ?thesis using `x \<in> (\<Union>n. B n)` by auto
  next
    assume "x \<notin> (\<Union>n. B n)"
    then have "\<And>n. f x * indicator (B n) x = 0" by simp
    have "(\<Sum>n. f x * indicator (B n) x) = 0"
      by (simp add: `\<And>n. f x * indicator (B n) x = 0`)
    then show ?thesis using `x \<notin> (\<Union>n. B n)` by auto
  qed
  ultimately show ?thesis by simp
qed

lemma nn_set_integral_add:
  assumes [measurable]: "f \<in> borel_measurable M" "g \<in> borel_measurable M"
          "A \<in> sets M"
  shows "(\<integral>\<^sup>+x \<in> A. (f x + g x) \<partial>M) = (\<integral>\<^sup>+x \<in> A. f x \<partial>M) + (\<integral>\<^sup>+x \<in> A. g x \<partial>M)"
proof -
  have "(\<integral>\<^sup>+x \<in> A. (f x + g x) \<partial>M) = (\<integral>\<^sup>+x. (f x * indicator A x + g x * indicator A x) \<partial>M)"
    by (auto simp add: indicator_def intro!: nn_integral_cong)
  also have "... = (\<integral>\<^sup>+x. f x * indicator A x \<partial>M) + (\<integral>\<^sup>+x. g x * indicator A x \<partial>M)"
    apply (rule nn_integral_add) using assms(1) assms(2) by auto
  finally show ?thesis by simp
qed

lemma nn_set_integral_cong:
  assumes "AE x in M. f x = g x"
  shows "(\<integral>\<^sup>+x \<in> A. f x \<partial>M) = (\<integral>\<^sup>+x \<in> A. g x \<partial>M)"
apply (rule nn_integral_cong_AE) using assms(1) by auto

lemma nn_set_integral_set_mono:
  "A \<subseteq> B \<Longrightarrow> (\<integral>\<^sup>+ x \<in> A. f x \<partial>M) \<le> (\<integral>\<^sup>+ x \<in> B. f x \<partial>M)"
by (auto intro!: nn_integral_mono split: split_indicator)

lemma nn_set_integral_mono:
  assumes [measurable]: "f \<in> borel_measurable M" "g \<in> borel_measurable M"
          "A \<in> sets M"
      and "AE x\<in>A in M. f x \<le> g x"
  shows "(\<integral>\<^sup>+x \<in> A. f x \<partial>M) \<le> (\<integral>\<^sup>+x \<in> A. g x \<partial>M)"
by (auto intro!: nn_integral_mono_AE split: split_indicator simp: assms)

lemma nn_set_integral_space [simp]:
  shows "(\<integral>\<^sup>+ x \<in> space M. f x \<partial>M) = (\<integral>\<^sup>+x. f x \<partial>M)"
by (metis (mono_tags, lifting) indicator_simps(1) mult.right_neutral nn_integral_cong)

lemma nn_integral_count_compose_inj:
  assumes "inj_on g A"
  shows "(\<integral>\<^sup>+x \<in> A. f (g x) \<partial>count_space UNIV) = (\<integral>\<^sup>+y \<in> g`A. f y \<partial>count_space UNIV)"
proof -
  have "(\<integral>\<^sup>+x \<in> A. f (g x) \<partial>count_space UNIV) = (\<integral>\<^sup>+x. f (g x) \<partial>count_space A)"
    by (auto simp add: nn_integral_count_space_indicator[symmetric])
  also have "... = (\<integral>\<^sup>+y. f y \<partial>count_space (g`A))"
    by (simp add: assms nn_integral_bij_count_space inj_on_imp_bij_betw)
  also have "... = (\<integral>\<^sup>+y \<in> g`A. f y \<partial>count_space UNIV)"
    by (auto simp add: nn_integral_count_space_indicator[symmetric])
  finally show ?thesis by simp
qed

lemma nn_integral_count_compose_bij:
  assumes "bij_betw g A B"
  shows "(\<integral>\<^sup>+x \<in> A. f (g x) \<partial>count_space UNIV) = (\<integral>\<^sup>+y \<in> B. f y \<partial>count_space UNIV)"
proof -
  have "inj_on g A" using assms bij_betw_def by auto
  then have "(\<integral>\<^sup>+x \<in> A. f (g x) \<partial>count_space UNIV) = (\<integral>\<^sup>+y \<in> g`A. f y \<partial>count_space UNIV)"
    by (rule nn_integral_count_compose_inj)
  then show ?thesis using assms by (simp add: bij_betw_def)
qed

lemma set_integral_null_delta:
  fixes f::"_ \<Rightarrow> _ :: {banach, second_countable_topology}"
  assumes [measurable]: "integrable M f" "A \<in> sets M" "B \<in> sets M"
    and "A \<Delta> B \<in> null_sets M"
  shows "(\<integral>x \<in> A. f x \<partial>M) = (\<integral>x \<in> B. f x \<partial>M)"
proof (rule set_integral_cong_set, auto)
  have *: "AE a in M. a \<notin> A \<Delta> B"
    using assms(4) AE_not_in by blast
  then show "AE x in M. (x \<in> B) = (x \<in> A)"
    by auto
qed

lemma set_integral_space:
  assumes "integrable M f"
  shows "(\<integral>x \<in> space M. f x \<partial>M) = (\<integral>x. f x \<partial>M)"
by (metis (mono_tags, lifting) indicator_simps(1) Bochner_Integration.integral_cong real_vector.scale_one)

lemma null_if_pos_func_has_zero_nn_int:
  fixes f::"'a \<Rightarrow> ennreal"
  assumes [measurable]: "f \<in> borel_measurable M" "A \<in> sets M"
    and "AE x\<in>A in M. f x > 0" "(\<integral>\<^sup>+x\<in>A. f x \<partial>M) = 0"
  shows "A \<in> null_sets M"
proof -
  have "AE x in M. f x * indicator A x = 0"
    by (subst nn_integral_0_iff_AE[symmetric], auto simp add: assms(4))
  then have "AE x\<in>A in M. False" using assms(3) by auto
  then show "A \<in> null_sets M" using assms(2) by (simp add: AE_iff_null_sets)
qed



text {* The next lemma shows that $L^1$ convergence of a sequence of functions follows from almost
everywhere convergence and the weaker condition of the convergence of the integrated norms (or even
just the nontrivial inequality about them). Useful in a lot of contexts! This statement (or its
variations) are known as Scheffe lemma.

Informal quick textbook proof:
Let $G_n(x) = \norm{f x} + \norm{F_n x} - \norm{(f-F_n)(x)}$. Then $\int \liminf G_n \leq
\liminf \int G_n$ by Fatou, i.e., $2 \int \norm{f} \leq 2 \int \norm{f} + \liminf (- \int \norm{f-F_n})$,
then have $\limsup \int \norm{f-F_n} \leq 0$. QED

The formalization is more painful as one should jump back and forth between reals and ereals and justify
all the time positivity or integrability (thankfully, measurability is handled more or less automatically).*}

lemma Scheffe_lemma1:
  assumes "\<And>n. integrable M (F n)" "integrable M f"
          "AE x in M. (\<lambda>n. F n x) \<longlonglongrightarrow> f x"
          "limsup (\<lambda>n. \<integral>\<^sup>+ x. norm(F n x) \<partial>M) \<le> (\<integral>\<^sup>+ x. norm(f x) \<partial>M)"
  shows "(\<lambda>n. \<integral>\<^sup>+ x. norm(F n x - f x) \<partial>M) \<longlonglongrightarrow> 0"
proof -
  have [measurable]: "\<And>n. F n \<in> borel_measurable M" "f \<in> borel_measurable M"
    using assms(1) assms(2) by simp_all
  define G where "G = (\<lambda>n x. norm(f x) + norm(F n x) - norm(F n x - f x))"
  have [measurable]: "\<And>n. G n \<in> borel_measurable M" unfolding G_def by simp
  have G_pos[simp]: "\<And>n x. G n x \<ge> 0"
    unfolding G_def by (metis ge_iff_diff_ge_0 norm_minus_commute norm_triangle_ineq4)
  have finint: "(\<integral>\<^sup>+ x. norm(f x) \<partial>M) \<noteq> \<infinity>"
    using has_bochner_integral_implies_finite_norm[OF has_bochner_integral_integrable[OF \<open>integrable M f\<close>]]
    by simp
  then have fin2: "2 * (\<integral>\<^sup>+ x. norm(f x) \<partial>M) \<noteq> \<infinity>"
    by (auto simp: ennreal_mult_eq_top_iff)

  {
    fix x assume *: "(\<lambda>n. F n x) \<longlonglongrightarrow> f x"
    then have "(\<lambda>n. norm(F n x)) \<longlonglongrightarrow> norm(f x)" using tendsto_norm by blast
    moreover have "(\<lambda>n. norm(F n x - f x)) \<longlonglongrightarrow> 0" using * Lim_null tendsto_norm_zero_iff by fastforce
    ultimately have a: "(\<lambda>n. norm(F n x) - norm(F n x - f x)) \<longlonglongrightarrow> norm(f x)" using tendsto_diff by fastforce
    have "(\<lambda>n. norm(f x) + (norm(F n x) - norm(F n x - f x))) \<longlonglongrightarrow> norm(f x) + norm(f x)"
      by (rule tendsto_add) (auto simp add: a)
    moreover have "\<And>n. G n x = norm(f x) + (norm(F n x) - norm(F n x - f x))" unfolding G_def by simp
    ultimately have "(\<lambda>n. G n x) \<longlonglongrightarrow> 2 * norm(f x)" by simp
    then have "(\<lambda>n. ennreal(G n x)) \<longlonglongrightarrow> ennreal(2 * norm(f x))" by simp
    then have "liminf (\<lambda>n. ennreal(G n x)) = ennreal(2 * norm(f x))"
      using sequentially_bot tendsto_iff_Liminf_eq_Limsup by blast
  }
  then have "AE x in M. liminf (\<lambda>n. ennreal(G n x)) = ennreal(2 * norm(f x))" using assms(3) by auto
  then have "(\<integral>\<^sup>+ x. liminf (\<lambda>n. ennreal (G n x)) \<partial>M) = (\<integral>\<^sup>+ x. 2 * ennreal(norm(f x)) \<partial>M)"
    by (simp add: nn_integral_cong_AE ennreal_mult)
  also have "... = 2 * (\<integral>\<^sup>+ x. norm(f x) \<partial>M)" by (rule nn_integral_cmult) auto
  finally have int_liminf: "(\<integral>\<^sup>+ x. liminf (\<lambda>n. ennreal (G n x)) \<partial>M) = 2 * (\<integral>\<^sup>+ x. norm(f x) \<partial>M)"
    by simp

  have "(\<integral>\<^sup>+x. ennreal(norm(f x)) + ennreal(norm(F n x)) \<partial>M) = (\<integral>\<^sup>+x. norm(f x) \<partial>M) + (\<integral>\<^sup>+x. norm(F n x) \<partial>M)" for n
    by (rule nn_integral_add) (auto simp add: assms)
  then have "limsup (\<lambda>n. (\<integral>\<^sup>+x. ennreal(norm(f x)) + ennreal(norm(F n x)) \<partial>M)) =
      limsup (\<lambda>n. (\<integral>\<^sup>+x. norm(f x) \<partial>M) + (\<integral>\<^sup>+x. norm(F n x) \<partial>M))"
    by simp
  also have "... = (\<integral>\<^sup>+x. norm(f x) \<partial>M) + limsup (\<lambda>n. (\<integral>\<^sup>+x. norm(F n x) \<partial>M))"
    by (rule Limsup_const_add, auto simp add: finint)
  also have "... \<le> (\<integral>\<^sup>+x. norm(f x) \<partial>M) + (\<integral>\<^sup>+x. norm(f x) \<partial>M)"
    using assms(4) by (simp add: add_left_mono)
  also have "... = 2 * (\<integral>\<^sup>+x. norm(f x) \<partial>M)"
    unfolding one_add_one[symmetric] distrib_right by simp
  ultimately have a: "limsup (\<lambda>n. (\<integral>\<^sup>+x. ennreal(norm(f x)) + ennreal(norm(F n x)) \<partial>M)) \<le>
    2 * (\<integral>\<^sup>+x. norm(f x) \<partial>M)" by simp

  have le: "ennreal (norm (F n x - f x)) \<le> ennreal (norm (f x)) + ennreal (norm (F n x))" for n x
    by (simp add: norm_minus_commute norm_triangle_ineq4 ennreal_plus[symmetric] ennreal_minus del: ennreal_plus)
  then have le2: "(\<integral>\<^sup>+ x. ennreal (norm (F n x - f x)) \<partial>M) \<le> (\<integral>\<^sup>+ x. ennreal (norm (f x)) + ennreal (norm (F n x)) \<partial>M)" for n
    by (rule nn_integral_mono)

  have "2 * (\<integral>\<^sup>+ x. norm(f x) \<partial>M) = (\<integral>\<^sup>+ x. liminf (\<lambda>n. ennreal (G n x)) \<partial>M)"
    by (simp add: int_liminf)
  also have "\<dots> \<le> liminf (\<lambda>n. (\<integral>\<^sup>+x. G n x \<partial>M))"
    by (rule nn_integral_liminf) auto
  also have "liminf (\<lambda>n. (\<integral>\<^sup>+x. G n x \<partial>M)) =
    liminf (\<lambda>n. (\<integral>\<^sup>+x. ennreal(norm(f x)) + ennreal(norm(F n x)) \<partial>M) - (\<integral>\<^sup>+x. norm(F n x - f x) \<partial>M))"
  proof (intro arg_cong[where f=liminf] ext)
    fix n
    have "\<And>x. ennreal(G n x) = ennreal(norm(f x)) + ennreal(norm(F n x)) - ennreal(norm(F n x - f x))"
      unfolding G_def by (simp add: ennreal_plus[symmetric] ennreal_minus del: ennreal_plus)
    moreover have "(\<integral>\<^sup>+x. ennreal(norm(f x)) + ennreal(norm(F n x)) - ennreal(norm(F n x - f x)) \<partial>M)
            = (\<integral>\<^sup>+x. ennreal(norm(f x)) + ennreal(norm(F n x)) \<partial>M) - (\<integral>\<^sup>+x. norm(F n x - f x) \<partial>M)"
    proof (rule nn_integral_diff)
      from le show "AE x in M. ennreal (norm (F n x - f x)) \<le> ennreal (norm (f x)) + ennreal (norm (F n x))"
        by simp
      from le2 have "(\<integral>\<^sup>+x. ennreal (norm (F n x - f x)) \<partial>M) < \<infinity>" using assms(1) assms(2)
        by (metis has_bochner_integral_implies_finite_norm integrable.simps Bochner_Integration.integrable_diff)
      then show "(\<integral>\<^sup>+x. ennreal (norm (F n x - f x)) \<partial>M) \<noteq> \<infinity>" by simp
    qed (auto simp add: assms)
    ultimately show "(\<integral>\<^sup>+x. G n x \<partial>M) = (\<integral>\<^sup>+x. ennreal(norm(f x)) + ennreal(norm(F n x)) \<partial>M) - (\<integral>\<^sup>+x. norm(F n x - f x) \<partial>M)"
      by simp
  qed
  finally have "2 * (\<integral>\<^sup>+ x. norm(f x) \<partial>M) + limsup (\<lambda>n. (\<integral>\<^sup>+x. norm(F n x - f x) \<partial>M)) \<le>
    liminf (\<lambda>n. (\<integral>\<^sup>+x. ennreal(norm(f x)) + ennreal(norm(F n x)) \<partial>M) - (\<integral>\<^sup>+x. norm(F n x - f x) \<partial>M)) +
    limsup (\<lambda>n. (\<integral>\<^sup>+x. norm(F n x - f x) \<partial>M))"
    by (intro add_mono) auto
  also have "\<dots> \<le> (limsup (\<lambda>n. \<integral>\<^sup>+x. ennreal(norm(f x)) + ennreal(norm(F n x)) \<partial>M) - limsup (\<lambda>n. \<integral>\<^sup>+x. norm (F n x - f x) \<partial>M)) +
    limsup (\<lambda>n. (\<integral>\<^sup>+x. norm(F n x - f x) \<partial>M))"
    by (intro add_mono liminf_minus_ennreal le2) auto
  also have "\<dots> = limsup (\<lambda>n. (\<integral>\<^sup>+x. ennreal(norm(f x)) + ennreal(norm(F n x)) \<partial>M))"
    by (intro diff_add_cancel_ennreal Limsup_mono always_eventually allI le2)
  also have "\<dots> \<le> 2 * (\<integral>\<^sup>+x. norm(f x) \<partial>M)"
    by fact
  finally have "limsup (\<lambda>n. (\<integral>\<^sup>+x. norm(F n x - f x) \<partial>M)) = 0"
    using fin2 by simp
  then show ?thesis
    by (rule tendsto_0_if_Limsup_eq_0_ennreal)
qed

lemma Scheffe_lemma2:
  fixes F::"nat \<Rightarrow> 'a \<Rightarrow> 'b::{banach, second_countable_topology}"
  assumes "\<And> n::nat. F n \<in> borel_measurable M" "integrable M f"
          "AE x in M. (\<lambda>n. F n x) \<longlonglongrightarrow> f x"
          "\<And>n. (\<integral>\<^sup>+ x. norm(F n x) \<partial>M) \<le> (\<integral>\<^sup>+ x. norm(f x) \<partial>M)"
  shows "(\<lambda>n. \<integral>\<^sup>+ x. norm(F n x - f x) \<partial>M) \<longlonglongrightarrow> 0"
proof (rule Scheffe_lemma1)
  fix n::nat
  have "(\<integral>\<^sup>+ x. norm(f x) \<partial>M) < \<infinity>" using assms(2) by (metis has_bochner_integral_implies_finite_norm integrable.cases)
  then have "(\<integral>\<^sup>+ x. norm(F n x) \<partial>M) < \<infinity>" using assms(4)[of n] by auto
  then show "integrable M (F n)" by (subst integrable_iff_bounded, simp add: assms(1)[of n])
qed (auto simp add: assms Limsup_bounded)


text {*There is a \verb+LIM_zero_cancel+ both in \verb+Levy+ and \verb+Limits+, with the same
statement...*}

end
