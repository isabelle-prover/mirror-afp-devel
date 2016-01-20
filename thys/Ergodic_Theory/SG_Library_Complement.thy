(*  Author:  Sébastien Gouëzel   sebastien.gouezel@univ-rennes1.fr
    License: BSD
*)

theory SG_Library_Complement
imports Complex_Main Topological_Spaces  "~~/src/HOL/Multivariate_Analysis/Extended_Real_Limits"
 "~~/src/HOL/Probability/Probability_Measure" "~~/src/HOL/Probability/Set_Integral"
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
    hence "i - k < n \<and> x \<in> M((i-k) + k)" by auto
    thus "x \<in> ?A" using UN_le_add_shift by blast
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

text {*Next one could be close to \verb+setsum_nat_group+*}

lemma setsum_arith_progression:
  "(\<Sum>r<(N::nat). (\<Sum>i<a. f (i*N+r))) = (\<Sum>j<a*N. f j)"
proof -
  have *: "(\<Sum>r<N. f (i*N+r)) = (\<Sum> j \<in> {i*N..<i*N + N}. f j)" for i
    by (rule setsum.reindex_bij_betw, rule bij_betw_byWitness[where ?f'= "\<lambda>r. r-i*N"], auto)

  have "(\<Sum>r<N. (\<Sum>i<a. f (i*N+r))) = (\<Sum>i<a. (\<Sum>r<N. f (i*N+r)))"
    using setsum.commute by auto
  also have "... = (\<Sum>i<a. (\<Sum> j \<in> {i*N..<i*N + N}. f j))"
    using * by auto
  also have "... =  (\<Sum>j<a*N. f j)"
    by (rule setsum_nat_group)
  finally show ?thesis by simp
qed



subsection {*Miscellanous basic results*}


lemma ind_from_1[consumes 1]:
  assumes "n > 0"
  assumes "P 1"
  assumes "\<And>n. n > 0 \<Longrightarrow> P n \<Longrightarrow> P (Suc n)"
  shows "P n"
proof -
  have "(n = 0) \<or> P n"
  proof (induction n)
    case 0 thus ?case by auto
  next
    case (Suc k)
    {
      assume "Suc k = 1"
      hence ?case using assms(2) by auto
    }
    also
    {
      assume "Suc k > 1"
      then have "k > 0" by auto
      then have ?case using Suc.IH assms(3) by auto
    }
    ultimately show ?case by arith
  qed
  then show ?thesis using assms(1) by auto
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
  shows "\<exists>N. \<forall>n>N. abs(u n -l ) < e"
proof-
  have "eventually (\<lambda>n. dist (u n) l < e) sequentially" using assms tendstoD by auto
  hence "\<forall>\<^sub>F n in sequentially. abs(u n - l) < e" using dist_real_def by auto
  thus ?thesis by (simp add: eventually_at_top_dense)
qed

lemma nat_mod_cong:
  assumes "a=b+(c::nat)"
          "a mod n = b mod n"
  shows "c mod n = 0"
proof -
  let ?k = "a mod n"
  obtain a1 where "a = a1*n + ?k"  by (metis mod_div_equality)
  moreover obtain b1 where "b = b1*n + ?k" using assms(2) by (metis mod_div_equality)
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


subsection {*Topological-spaces.thy*}

lemma open_diagonal_complement:
  "open {(x,y) | x y. x \<noteq> (y::('a::t2_space))}"
proof (rule openI)
  fix t assume "t \<in> {(x, y) | x y. x \<noteq> (y::'a)}"
  then obtain x y where "t = (x,y)" "x \<noteq> y" by blast
  then obtain U V where *: "open U \<and> open V \<and> x \<in> U \<and> y \<in> V \<and> U \<inter> V = {}"
    by (auto simp add: separation_t2)
  def T \<equiv> "U \<times> V"
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
  "open  {(x,y) | x y. x > (y::'a::{linorder_topology})}"
proof (rule openI)
  fix t assume "t \<in> {(x, y) | x y. y < (x::'a)}"
  then obtain x y where "t = (x, y)" "x > y" by blast
  show "\<exists>T. open T \<and> t \<in> T \<and> T \<subseteq> {(x, y) | x y. y < x}"
  proof (cases)
    assume "\<exists>z. y < z \<and> z < x"
    then obtain z where z: "y < z \<and> z < x" by blast
    def T \<equiv> "{z<..} \<times> {..<z}"
    have "open T" unfolding T_def by (simp add: open_Times)
    moreover have "t \<in> T" using T_def z `t = (x,y)` by auto
    moreover have "T \<subseteq> {(x, y) | x y. y < x}" unfolding T_def by auto
    ultimately show ?thesis by auto
  next
    assume "\<not>(\<exists>z. y < z \<and> z < x)"
    then have *: "{x ..} =  {y<..}" "{..< x} = {..y}"
      using `x > y` apply auto using leI by blast
    def T \<equiv> "{x ..} \<times> {.. y}"
    then have "T = {y<..} \<times> {..< x}" using * by simp
    then have "open T" unfolding T_def by (simp add: open_Times)
    moreover have "t \<in> T" using T_def  `t = (x,y)` by auto
    moreover have "T \<subseteq> {(x, y) | x y. y < x}" unfolding T_def using `x > y` by auto
    ultimately show ?thesis by auto
  qed
qed

lemma closed_subdiagonal:
  "closed {(x,y) | x y. x \<le> (y::'a::{linorder_topology})}"
proof -
  have " {(x,y) | x y. x \<le> (y::'a)} = UNIV - {(x,y) | x y. x > (y::'a)}" by auto
  then show ?thesis using open_superdiagonal  closed_Diff by auto
qed

lemma open_subdiagonal:
  "open  {(x,y) | x y. x < (y::'a::{linorder_topology})}"
proof (rule openI)
  fix t assume "t \<in> {(x, y) | x y. y > (x::'a)}"
  then obtain x y where "t = (x, y)" "x < y" by blast
  show "\<exists>T. open T \<and> t \<in> T \<and> T \<subseteq> {(x, y) | x y. y > x}"
  proof (cases)
    assume "\<exists>z. y > z \<and> z > x"
    then obtain z where z: "y > z \<and> z > x" by blast
    def T \<equiv> "{..<z} \<times> {z<..}"
    have "open T" unfolding T_def by (simp add: open_Times)
    moreover have "t \<in> T" using T_def z `t = (x,y)` by auto
    moreover have "T \<subseteq> {(x, y) |x y. y > x}" unfolding T_def by auto
    ultimately show ?thesis by auto
  next
    assume "\<not>(\<exists>z. y > z \<and> z > x)"
    then have *: "{..x} =  {..<y}" "{x<..} = {y..}"
      using `x < y` apply auto using leI by blast
    def T \<equiv> "{..x} \<times> {y..}"
    then have "T = {..<y} \<times> {x<..}" using * by simp
    then have "open T" unfolding T_def by (simp add: open_Times)
    moreover have "t \<in> T" using T_def  `t = (x,y)` by auto
    moreover have "T \<subseteq> {(x, y) |x y. y > x}" unfolding T_def using `x < y` by auto
    ultimately show ?thesis by auto
  qed
qed

lemma closed_superdiagonal:
  "closed {(x,y) | x y. x \<ge> (y::('a::{linorder_topology}))}"
proof -
  have " {(x,y) | x y. x \<ge> (y::'a)} = UNIV - {(x,y) | x y. x < y}" by auto
  then show ?thesis using open_subdiagonal  closed_Diff by auto
qed

text {*The next statements come from the same statements for true subsequences*}

lemma eventually_weak_subseq:
   fixes u::"nat \<Rightarrow> nat"
   assumes "(\<lambda>n. real(u n)) \<longlonglongrightarrow> \<infinity>" "eventually P sequentially"
  shows  "eventually (\<lambda>n. P (u n)) sequentially"
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
   shows  "LIM n sequentially. u n:> at_top"
unfolding filterlim_iff by (metis assms eventually_weak_subseq)

lemma limit_along_weak_subseq:
  fixes u::"nat \<Rightarrow> nat" and v::"nat \<Rightarrow> _"
  assumes "(\<lambda>n. real(u n)) \<longlonglongrightarrow> \<infinity>" "v \<longlonglongrightarrow> l"
  shows "(\<lambda> n. v(u n)) \<longlonglongrightarrow> l"
using filterlim_compose[of v, OF _ filterlim_weak_subseq] assms by auto


subsection {*Series*}

text {*The next lemma is a more natural reformulation of \verb+ suminf_exist_split+*}

context
  fixes f :: "nat \<Rightarrow> 'a::real_normed_vector"
begin

lemma suminf_exist_split2:
  assumes "summable f"
  shows "(\<lambda>n. (\<Sum>k. f(k+n))) \<longlonglongrightarrow> 0"
by (subst lim_sequentially, auto simp add: dist_norm suminf_exist_split[OF _ assms])

end


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

   have "f(n-k)/(n-k+k) = f(n-k)/n"
     if "n>k" for n using that by auto
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
  def B1 \<equiv> "{(LEAST x. x \<in> U)| U. U \<in> A}"
  then have "countable B1" using `countable A` by (simp add: simple_image)
  def B2 \<equiv> "{(SOME x. x \<in> U)| U. U \<in> A}"
  then have "countable B2" using `countable A` by (simp add: simple_image)
  have "\<And>x y. x < y \<Longrightarrow>  (\<exists>b \<in> B1 \<union> B2. x < b \<and> b \<le> y)"
  proof -
    fix x y::'a assume "x < y"
    show "\<exists>b \<in> B1 \<union> B2. x < b \<and> b \<le> y"
    proof (cases)
      assume "\<exists>z. x < z \<and> z < y"
      then obtain z where z: "x < z \<and> z < y" by auto
      def U \<equiv> "{x<..<y}"
      then have "open U" by simp
      moreover have "z \<in> U" using z U_def by simp
      ultimately obtain "V" where  "V \<in> A" "z \<in> V" "V \<subseteq> U" using topological_basisE[OF `topological_basis A`] by auto
      def w \<equiv> "(SOME x. x \<in> V)"
      then have "w \<in> V" using `z \<in> V` by (metis someI2)
      then have "x < w \<and> w \<le> y" using `w \<in> V` `V \<subseteq> U` U_def by fastforce
      moreover have "w \<in> B1 \<union> B2" using w_def B2_def `V \<in> A` by auto
      ultimately show ?thesis by auto
    next
      assume "\<not>(\<exists>z. x < z \<and> z < y)"
      then have *: "\<And>z. z > x \<Longrightarrow> z \<ge> y" by auto
      def U \<equiv> "{x<..}"
      then have "open U" by simp
      moreover have "y \<in> U" using `x < y` U_def by simp
      ultimately obtain "V" where  "V \<in> A" "y \<in> V" "V \<subseteq> U" using topological_basisE[OF `topological_basis A`] by auto
      have "U = {y..}" unfolding U_def using * `x < y` by auto
      then have "V \<subseteq> {y..}" using `V \<subseteq> U` by simp
      then have "(LEAST w. w \<in> V) = y" using `y \<in> V` by (meson Least_equality atLeast_iff subsetCE)
      then have "y \<in> B1 \<union> B2" using `V \<in> A` B1_def by auto
      moreover have "x < y \<and> y \<le> y" using `x < y` by simp
      ultimately show ?thesis by auto
    qed
  qed
  moreover have "countable (B1 \<union> B2)" using `countable B1` `countable B2` by simp
  ultimately show ?thesis by auto
qed

lemma countable_separating_set_linorder2:
  shows "\<exists>B::('a::{linorder_topology, second_countable_topology} set). countable B \<and> (\<forall>x y. x < y \<longrightarrow> (\<exists>b \<in> B. x \<le> b \<and> b < y))"
proof -
  obtain A::"'a set set" where "countable A" "topological_basis A" using ex_countable_basis by auto
  def B1 \<equiv> "{(GREATEST x. x \<in> U) | U. U \<in> A}"
  then have "countable B1" using `countable A` by (simp add: simple_image)
  def B2 \<equiv> "{(SOME x. x \<in> U)| U. U \<in> A}"
  then have "countable B2" using `countable A` by (simp add: simple_image)
  have "\<And>x y. x < y \<Longrightarrow>  (\<exists>b \<in> B1 \<union> B2. x \<le> b \<and> b < y)"
  proof -
    fix x y::'a assume "x < y"
    show "\<exists>b \<in> B1 \<union> B2. x \<le> b \<and> b < y"
    proof (cases)
      assume "\<exists>z. x < z \<and> z < y"
      then obtain z where z: "x < z \<and> z < y" by auto
      def U \<equiv> "{x<..<y}"
      then have "open U" by simp
      moreover have "z \<in> U" using z U_def by simp
      ultimately obtain "V" where  "V \<in> A" "z \<in> V" "V \<subseteq> U" using topological_basisE[OF `topological_basis A`] by auto
      def w \<equiv> "(SOME x. x \<in> V)"
      then have "w \<in> V" using `z \<in> V` by (metis someI2)
      then have "x \<le> w \<and> w < y" using `w \<in> V` `V \<subseteq> U` U_def by fastforce
      moreover have "w \<in> B1 \<union> B2" using w_def B2_def `V \<in> A` by auto
      ultimately show ?thesis by auto
    next
      assume "\<not>(\<exists>z. x < z \<and> z < y)"
      then have *: "\<And>z. z < y \<Longrightarrow> z \<le> x" using leI by blast
      def U \<equiv> "{..<y}"
      then have "open U" by simp
      moreover have "x \<in> U" using `x < y` U_def by simp
      ultimately obtain "V" where  "V \<in> A" "x \<in> V" "V \<subseteq> U" using topological_basisE[OF `topological_basis A`] by auto
      have "U = {..x}" unfolding U_def using * `x < y` by auto
      then have "V \<subseteq> {..x}" using `V \<subseteq> U` by simp
      then have "(GREATEST x. x \<in> V) = x" using `x \<in> V` by (meson Greatest_equality atMost_iff subsetCE)
      then have "x \<in> B1 \<union> B2" using `V \<in> A` B1_def by auto
      moreover have "x \<le> x \<and> x < y" using `x < y` by simp
      ultimately show ?thesis by auto
    qed
  qed
  moreover have "countable (B1 \<union> B2)" using `countable B1` `countable B2` by simp
  ultimately show ?thesis by auto
qed

subsection {*Liminf-Limsup.thy*}

lemma limsup_shift:
  "limsup (\<lambda>n. u (n+1)) = limsup u"
proof -
  {
    fix n
    have "(SUP m:{n+1..}. u m) = (SUP m:{n..}. u (m + 1))"
        apply (rule SUP_eq) using Suc_le_D by (auto)
  }
  then have a: "(INF n. SUP m:{n..}. u (m + 1)) = (INF n. (SUP m:{n+1..}. u m))" by auto
  have b: "(INF n. (SUP m:{n+1..}. u m)) = (INF n:{1..}.  (SUP m:{n..}. u m))"
    apply (rule INF_eq) using Suc_le_D by (auto)
  {
    fix v::"nat \<Rightarrow> 'a" assume "decseq v"
    have  "(INF n:{1..}. v n) =  (INF n. v n)"
      apply (rule INF_eq) using `decseq v` decseq_Suc_iff by auto
  }
  moreover have "decseq (\<lambda>n. (SUP m:{n..}. u m))" by (simp add: SUP_subset_mono decseq_def)
  ultimately have c: "(INF n:{1..}.  (SUP m:{n..}. u m)) =  (INF n.  (SUP m:{n..}. u m))" by simp
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
  {
    fix n
    have "(INF m:{n+1..}. u m) = (INF m:{n..}. u (m + 1))"
        apply (rule INF_eq) using Suc_le_D by (auto)
  }
  then have a: "(SUP n. INF m:{n..}. u (m + 1)) = (SUP n. (INF m:{n+1..}. u m))" by auto
  have b: "(SUP n. (INF m:{n+1..}. u m)) = (SUP n:{1..}.  (INF m:{n..}. u m))"
    apply (rule SUP_eq) using Suc_le_D by (auto)
  {
    fix v::"nat \<Rightarrow> 'a" assume "incseq v"
    have  "(SUP n:{1..}. v n) =  (SUP n. v n)"
      apply (rule SUP_eq) using `incseq v` incseq_Suc_iff by auto
  }
  moreover have "incseq (\<lambda>n. (INF m:{n..}. u m))" by (simp add: INF_superset_mono mono_def)
  ultimately have c: "(SUP n:{1..}.  (INF m:{n..}. u m)) =  (SUP n.  (INF m:{n..}. u m))" by simp
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
  fixes u::"nat \<Rightarrow>  'a :: {complete_linorder, linorder_topology}"
  shows "\<exists>r. subseq r \<and> (u o r) \<longlonglongrightarrow> limsup u"
proof (cases)
  assume "\<forall>n. \<exists>p>n. \<forall>m\<ge>p. u m \<le> u p"
  then have "\<exists>r. \<forall>n. (\<forall>m\<ge>r n. u m \<le> u (r n)) \<and> r n < r (Suc n)"
    by (intro dependent_nat_choice) (auto simp: conj_commute)
  then obtain r where "subseq r" and mono: "\<And>n m. r n \<le> m \<Longrightarrow> u m \<le> u (r n)"
    by (auto simp: subseq_Suc_iff)
  def umax \<equiv> "\<lambda>n. (SUP m:{n..}. u m)"
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
    def U \<equiv> "{m. m > p \<and> u p < u m}"
    have "U \<noteq> {}" unfolding U_def using N[of p] `p \<in> {N<..x}` by auto
    def y \<equiv> "Inf U"
    then have "y \<in> U" using `U \<noteq> {}` by (simp add: Inf_nat_def1)
    have a: "\<And>i. i \<in> {N<..x} \<Longrightarrow> u i \<le> u p"
    proof -
      fix i assume "i \<in> {N<..x}"
      then have "u i \<in> {u i |i. i \<in> {N<..x}}" by blast
      then show "u i \<le> u p" using upmax by simp
    qed
    moreover have "u p < u y" using `y \<in> U` U_def by auto
    ultimately have "y \<notin>  {N<..x}" using not_le by blast
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
        then have i:"i \<in> {N<..<y}" using `i \<in>  {N<..y}` by simp
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
  then show ?thesis using  `subseq r` by auto
qed

lemma liminf_subseq_lim:
  fixes u::"nat \<Rightarrow>  'a :: {complete_linorder, linorder_topology}"
  shows "\<exists>r. subseq r \<and> (u o r) \<longlonglongrightarrow> liminf u"
proof (cases)
  assume "\<forall>n. \<exists>p>n. \<forall>m\<ge>p. u m \<ge> u p"
  then have "\<exists>r. \<forall>n. (\<forall>m\<ge>r n. u m \<ge> u (r n)) \<and> r n < r (Suc n)"
    by (intro dependent_nat_choice) (auto simp: conj_commute)
  then obtain r where "subseq r" and mono: "\<And>n m. r n \<le> m \<Longrightarrow> u m \<ge> u (r n)"
    by (auto simp: subseq_Suc_iff)
  def umin \<equiv> "\<lambda>n. (INF m:{n..}. u m)"
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
    def U \<equiv> "{m. m > p \<and> u p > u m}"
    have "U \<noteq> {}" unfolding U_def using N[of p] `p \<in> {N<..x}` by auto
    def y \<equiv> "Inf U"
    then have "y \<in> U" using `U \<noteq> {}` by (simp add: Inf_nat_def1)
    have a: "\<And>i. i \<in> {N<..x} \<Longrightarrow> u i \<ge> u p"
    proof -
      fix i assume "i \<in> {N<..x}"
      then have "u i \<in> {u i |i. i \<in> {N<..x}}" by blast
      then show "u i \<ge> u p" using upmin by simp
    qed
    moreover have "u p > u y" using `y \<in> U` U_def by auto
    ultimately have "y \<notin>  {N<..x}" using not_le by blast
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
        then have i:"i \<in> {N<..<y}" using `i \<in>  {N<..y}` by simp
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
  then show ?thesis using  `subseq r` by auto
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
  assumes "b \<ge> 0" "c \<ge> 0"
     "a \<le> b" "c \<le> d"
  shows "a * c \<le> b * d"
by (metis ereal_mult_right_mono mult.commute order_trans assms)

lemma ereal_mult_mono':
  fixes a b c d::ereal
  assumes "a \<ge> 0" "c \<ge> 0"
     "a \<le> b" "c \<le> d"
  shows "a * c \<le> b * d"
by (metis ereal_mult_right_mono mult.commute order_trans assms)

lemma ereal_mult_mono_strict:
  fixes a b c d::ereal
  assumes "b > 0" "c > 0"
     "a < b" "c < d"
  shows "a * c < b * d"
proof -
  have "c < \<infinity>" using `c < d` by auto
  then have "a * c < b * c" by (metis ereal_mult_strict_left_mono[OF assms(3) assms(2)] mult.commute)
  moreover have "b * c \<le> b * d" using assms(2) assms(4) by (simp add: assms(1) ereal_mult_left_mono less_imp_le)
  ultimately show ?thesis by simp
qed

lemma ereal_mult_mono_strict':
  fixes a b c d::ereal
  assumes "a > 0" "c > 0"
     "a < b" "c < d"
  shows "a * c < b * d"
apply (rule ereal_mult_mono_strict, auto simp add: assms) using assms by auto

lemma ereal_ineq_diff_add:
  assumes "b \<noteq> (-\<infinity>::ereal)" "a \<ge> b"
  shows "a = b + (a-b)"
by (metis add.commute assms(1) assms(2) ereal_eq_minus_iff ereal_minus_le_iff ereal_plus_eq_PInfty)

lemma ereal_abs_add:
  fixes a b::ereal
  shows "abs(a+b) \<le> abs a + abs b"
by (cases rule: ereal2_cases[of a b]) (auto)

lemma ereal_abs_diff:
  fixes a b::ereal
  shows "abs(a-b) \<le> abs a + abs b"
by (cases rule: ereal2_cases[of a b]) (auto)

lemma setsum_constant_ereal:
  fixes a::ereal
  shows "(\<Sum>i\<in>I. a) = a * card I"
proof (cases "finite I", induct set: finite, simp_all)
  fix x :: 'a and F :: "'a set"
  have "\<forall>n. 0 \<le> real n" by linarith
  moreover have "(0::real) \<le> 1" by auto
  moreover have "\<forall>x0. (x0::real) + 1 = 1 + x0" by auto
  ultimately show "a + a * ereal (real (card F)) = a * ereal (1 + real (card F))"
    by (metis ereal_less_eq(5) ereal_plus_1(1) ereal_right_distrib one_ereal_def times_ereal_1)
qed

lemma real_lim_then_eventually_real:
  assumes "(u \<longlongrightarrow> ereal l) F"
  shows "eventually (\<lambda>n. u n = ereal(real_of_ereal(u n))) F"
proof -
  have "ereal l \<in> {-\<infinity><..<(\<infinity>::ereal)}" by simp
  moreover have "open {-\<infinity><..<(\<infinity>::ereal)}" by simp
  ultimately have "eventually (\<lambda>n. u n \<in> {-\<infinity><..<(\<infinity>::ereal)}) F" using assms tendsto_def by blast
  moreover have "\<And>x. x \<in>  {-\<infinity><..<(\<infinity>::ereal)} \<Longrightarrow> x = ereal(real_of_ereal x)" using ereal_real by auto
  ultimately show ?thesis by (metis (mono_tags, lifting) eventually_mono)
qed

subsubsection {*Continuity of addition*}

text {*The next few lemmas remove an unnecessary assumption in \verb+tendsto_add_ereal+, culminating
in \verb+tendsto_add_ereal_general+ which essentially says that the addition
is continuous on ereal times ereal, except at $(-\infty, \infty)$ and $(\infty, -\infty)$.
It is much more convenient in many situations, see for instance the proof of
\verb+tendsto_setsum_ereal+ below. *}

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
    hence "eventually (\<lambda>x. g x > y - 1) F" using g y order_tendsto_iff by auto
    moreover have "y-1 = ereal(real_of_ereal(y-1))"
      by (metis real ereal_eq_1(1) ereal_minus(1) real_of_ereal.simps(1))
    ultimately have "eventually (\<lambda>x. g x > ereal(real_of_ereal(y - 1))) F" by simp
    thus ?thesis by auto
  next
    case (PInf)
    have "eventually (\<lambda>x. g x > ereal 0) F" using g PInf by (simp add: tendsto_PInfty)
    thus ?thesis by auto
  qed (simp add: y)
  then obtain C::real where ge: "eventually (\<lambda>x. g x > ereal C) F" by auto

  {
    fix M::real
    have "eventually (\<lambda>x. f x > ereal(M - C)) F" using f by (simp add: tendsto_PInfty)
    hence "eventually (\<lambda>x. (f x > ereal (M-C)) \<and> (g x > ereal C)) F"
      by (auto simp add: ge eventually_conj_iff)
    moreover have "\<And>x. ((f x > ereal (M-C)) \<and> (g x > ereal C)) \<Longrightarrow> (f x + g x > ereal M)"
      using ereal_add_strict_mono2 by fastforce
    ultimately have "eventually (\<lambda>x. f x + g x > ereal M) F" using eventually_mono by force
  }
  thus ?thesis by (simp add: tendsto_PInfty)
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
    hence "eventually (\<lambda>x. g x < y + 1) F" using g y order_tendsto_iff by force
    moreover have "y+1 = ereal( real_of_ereal (y+1))" by (simp add: real)
    ultimately have "eventually (\<lambda>x. g x < ereal(real_of_ereal(y + 1))) F" by simp
    thus ?thesis by auto
  next
    case (MInf)
    have "eventually (\<lambda>x. g x < ereal 0) F" using g MInf by (simp add: tendsto_MInfty)
    thus ?thesis by auto
  qed (simp add: y)
  then obtain C::real where ge: "eventually (\<lambda>x. g x < ereal C) F" by auto

  {
    fix M::real
    have "eventually (\<lambda>x. f x < ereal(M - C)) F" using f by (simp add: tendsto_MInfty)
    hence "eventually (\<lambda>x. (f x < ereal (M- C)) \<and> (g x < ereal C)) F"
      by (auto simp add: ge eventually_conj_iff)
    moreover have  "\<And>x. ((f x < ereal (M-C)) \<and> (g x < ereal C)) \<Longrightarrow> (f x + g x < ereal M)"
      using ereal_add_strict_mono2 by fastforce
    ultimately have "eventually (\<lambda>x. f x + g x < ereal M) F" using eventually_mono by force
  }
  thus ?thesis by (simp add: tendsto_MInfty)
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
  thus ?thesis using tendsto_add_ereal_PInf assms by force
next
  case MInf
  thus ?thesis using tendsto_add_ereal_MInf assms
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

lemma tendsto_add_ereal_general:
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
  then have "((\<lambda>n. ereal(real_of_ereal(u n))) \<longlongrightarrow> ereal l)  F" using assms by auto
  then have limu: "((\<lambda>n. real_of_ereal(u n)) \<longlongrightarrow> l) F" by auto
  have vreal: "eventually (\<lambda>n. v n = ereal(real_of_ereal(v n))) F" by (rule real_lim_then_eventually_real[OF assms(2)])
  then have "((\<lambda>n. ereal(real_of_ereal(v n))) \<longlongrightarrow> ereal m)  F" using assms by auto
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
    def M \<equiv> "max K 1"
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
    hence "eventually (\<lambda>x. (f x > a) \<and> (g x > M/a)) F"
      using * by (auto simp add: eventually_conj_iff)
    then have "eventually (\<lambda>x. f x * g x > K) F" using eventually_mono Imp by force
  }
  thus ?thesis by (auto simp add: tendsto_PInfty)
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
apply (cases l) using assms by (auto simp add: assms sgn_if ereal_less_uminus_reorder)

lemma sgn_squared_ereal:
  assumes "l \<noteq> (0::ereal)"
  shows "sgn(l) * sgn(l) = 1"
apply (cases l) using assms by (auto simp add: one_ereal_def sgn_if)

lemma tendsto_mult_ereal:
  fixes f g::"_ \<Rightarrow> ereal"
  assumes "(f \<longlongrightarrow> l) F" "(g \<longlongrightarrow> m) F" "\<not>((l=0 \<and> abs(m) = \<infinity>) \<or> (m=0 \<and> abs(l) = \<infinity>))"
  shows  "((\<lambda>x. f x * g x) \<longlongrightarrow> l * m) F"
proof (cases)
  assume "l=0 \<or> m=0"
  then have "abs(l) \<noteq> \<infinity>" "abs(m) \<noteq> \<infinity>" using assms(3) by auto
  then obtain lr mr where "l = ereal lr" "m = ereal mr"  by auto
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
  have "((\<lambda>x. (sgn(l) * sgn(m)) * ((sgn(l) * f x) * (sgn(m) * g x))) \<longlongrightarrow>  (sgn(l) * sgn(m)) * ((sgn(l) * l) * (sgn(m) * m))) F"
    by (rule tendsto_cmult_ereal, auto simp add: sgn_finite2 *)
  moreover have "\<And>x. (sgn(l) * sgn(m)) * ((sgn(l) * f x) * (sgn(m) * g x)) = f x * g x"
    by (metis mult.left_neutral sgn_squared_ereal[OF `l \<noteq> 0`] sgn_squared_ereal[OF `m \<noteq> 0`] mult.assoc mult.commute)
  moreover have "(sgn(l) * sgn(m)) * ((sgn(l) * l) * (sgn(m) * m)) = l * m"
    by (metis mult.left_neutral sgn_squared_ereal[OF `l \<noteq> 0`] sgn_squared_ereal[OF `m \<noteq> 0`] mult.assoc mult.commute)
  ultimately show ?thesis by auto
qed


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
      moreover have "1/z < e" using `e>0`  `z>1/e`
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

lemma tendsto_inverse_ereal:
  fixes u::"_ \<Rightarrow> ereal"
  assumes "(u \<longlongrightarrow> l) F" "l \<noteq> 0"
  shows "((\<lambda>x. 1/ u x) \<longlongrightarrow> 1/l) F"
proof (cases l)
  case (real r)
  then have "r \<noteq> 0" using assms(2) by auto
  then have "1/l = ereal(1/r)" using real by (simp add: one_ereal_def)
  def v \<equiv> "\<lambda>n. real_of_ereal(u n)"
  have ureal: "eventually (\<lambda>n. u n = ereal(v n)) F" unfolding v_def using real_lim_then_eventually_real assms(1) real by auto
  then have "((\<lambda>n. ereal(v n)) \<longlongrightarrow> ereal r)  F" using assms real v_def by auto
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
  ultimately have *: "eventually (\<lambda>n.  -1/-u n =  1/u n) F" by (simp add: eventually_mono)

  def v \<equiv> "\<lambda>n. - u n"
  have "(v \<longlongrightarrow> \<infinity>) F" unfolding v_def using MInf assms(1) tendsto_uminus_ereal by fastforce
  then have "((\<lambda>n. 1/v n) \<longlongrightarrow> 0) F" using  tendsto_inverse_ereal_PInf by auto
  then have "((\<lambda>n. -1/v n) \<longlongrightarrow> 0) F" using tendsto_uminus_ereal by fastforce
  then show ?thesis unfolding v_def using Lim_transform_eventually[OF *] \<open> 1/l = 0 \<close> by auto
qed

lemma tendsto_divide_ereal:
  fixes f g::"_ \<Rightarrow> ereal"
  assumes "(f \<longlongrightarrow> l) F" "(g \<longlongrightarrow> m) F" "m \<noteq> 0" "\<not>(abs(l) = \<infinity> \<and> abs(m) = \<infinity>)"
  shows  "((\<lambda>x. f x / g x) \<longlongrightarrow> l / m) F"
proof -
  def h \<equiv> "\<lambda>x. 1/ g x"
  have *: "(h \<longlongrightarrow> 1/m) F" unfolding h_def using assms(2) assms(3) tendsto_inverse_ereal by auto
  have "((\<lambda>x. f x * h x) \<longlongrightarrow> l * (1/m)) F"
    apply (rule tendsto_mult_ereal[OF assms(1) *]) using assms(3) assms(4) by (auto simp add: divide_ereal_def)
  moreover have "f x * h x = f x / g x" for x unfolding h_def by (simp add: divide_ereal_def)
  moreover have "l * (1/m) = l/m" by (simp add: divide_ereal_def)
  ultimately show ?thesis unfolding h_def using Lim_transform_eventually by auto
qed


subsubsection {*Further limits*}

lemma id_nat_ereal_tendsto_PInf:
  "(\<lambda> n::nat. real n) \<longlonglongrightarrow> \<infinity>"
by (simp add: filterlim_real_sequentially tendsto_PInfty_eq_at_top)

lemma ereal_truncation_top:
  fixes x::ereal
  shows "(\<lambda>n::nat. min x n) \<longlonglongrightarrow> x"
proof (cases x)
  case (real r)
  then obtain K::nat where "K>0" "K > abs(r)" using ex_less_of_nat gr0I by auto
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

lemma ereal_truncation_real_top:
  fixes x::ereal
  assumes "x \<noteq> - \<infinity>"
  shows "(\<lambda>n::nat. real_of_ereal(min x n)) \<longlonglongrightarrow> x"
proof (cases x)
  case (real r)
  then obtain K::nat where "K>0" "K > abs(r)" using ex_less_of_nat gr0I by auto
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

lemma ereal_truncation_bottom:
  fixes x::ereal
  shows "(\<lambda>n::nat. max x (- real n)) \<longlonglongrightarrow> x"
proof (cases x)
  case (real r)
  then obtain K::nat where "K>0" "K > abs(r)" using ex_less_of_nat gr0I by auto
  then have "max x (-real n) = x" if "n \<ge> K" for n apply (subst real, subst real, auto) using that eq_iff by fastforce
  then have "eventually (\<lambda>n. max x (-real n) = x) sequentially" using eventually_at_top_linorder by blast
  then show ?thesis by (simp add: Lim_eventually)
next
  case (MInf)
  then have "max x (-real n) = (-1)* ereal(real n)" for n::nat by (auto simp add: max_def)
  moreover have "(\<lambda>n.  (-1)* ereal(real n)) \<longlonglongrightarrow> -\<infinity>"
    using tendsto_cmult_ereal[of "-1", OF _  id_nat_ereal_tendsto_PInf] by (simp add: one_ereal_def)
  ultimately show ?thesis using MInf by auto
next
  case (PInf)
  then have "max x (-real n) = x" for n::nat  by (auto simp add: max_def)
  then show ?thesis by auto
qed

lemma ereal_truncation_real_bottom:
  fixes x::ereal
  assumes "x \<noteq> \<infinity>"
  shows "(\<lambda>n::nat. real_of_ereal(max x (- real n))) \<longlonglongrightarrow> x"
proof (cases x)
  case (real r)
  then obtain K::nat where "K>0" "K > abs(r)" using ex_less_of_nat gr0I by auto
  then have "max x (-real n) = x" if "n \<ge> K" for n apply (subst real, subst real, auto) using that eq_iff by fastforce
  then have "real_of_ereal(max x (-real n)) = r" if "n \<ge> K" for n using real that by auto
  then have "eventually (\<lambda>n. real_of_ereal(max x (-real n)) = r) sequentially" using eventually_at_top_linorder by blast
  then have "(\<lambda>n. real_of_ereal(max x (-real n))) \<longlonglongrightarrow> r" by (simp add: Lim_eventually)
  then show ?thesis using real by auto
next
  case (MInf)
  then have "real_of_ereal(max x (-real n)) = (-1)* ereal(real n)" for n::nat by (auto simp add: max_def)
  moreover have "(\<lambda>n.  (-1)* ereal(real n)) \<longlonglongrightarrow> -\<infinity>"
    using tendsto_cmult_ereal[of "-1", OF _  id_nat_ereal_tendsto_PInf] by (simp add: one_ereal_def)
  ultimately show ?thesis using MInf by auto
qed (simp add: assms)

text {* the next one is copied from \verb+tendsto_setsum+. *}
lemma tendsto_setsum_ereal:
  fixes f :: "'a \<Rightarrow> 'b \<Rightarrow> ereal"
  assumes "\<And>i. i \<in> S \<Longrightarrow> (f i \<longlongrightarrow> a i) F"
          "\<And>i. abs(a i) \<noteq> \<infinity>"
  shows "((\<lambda>x. \<Sum>i\<in>S. f i x) \<longlongrightarrow> (\<Sum>i\<in>S. a i)) F"
proof (cases "finite S")
  assume "finite S" thus ?thesis using assms
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
  def D \<equiv> "max (real_of_ereal C) (Max {u n |n. n \<le> N})"
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
  def D \<equiv> "min (real_of_ereal C) (Min {u n |n. n \<le> N})"
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

  def w \<equiv> "\<lambda>n. u n + v n"
  obtain r where r: "subseq r" "(w o r) \<longlonglongrightarrow> limsup w" using limsup_subseq_lim by auto
  obtain s where s: "subseq s" "(u o r o s) \<longlonglongrightarrow> limsup (u o r)" using limsup_subseq_lim by auto
  obtain t where t: "subseq t" "(v o r o s o t) \<longlonglongrightarrow> limsup (v o r o s)" using limsup_subseq_lim by auto

  def a \<equiv> "r o s o t"
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
  then have b: "limsup (v o r o s)  \<noteq> \<infinity>" using `limsup v < \<infinity>` by auto

  have "(\<lambda>n. (u o a) n + (v o a) n) \<longlonglongrightarrow> limsup (u o r) + limsup (v o r o s)"
    using l tendsto_add_ereal_general a b by fastforce
  moreover have "(\<lambda>n. (u o a) n + (v o a) n) = (w o a)" unfolding w_def by auto
  ultimately have "(w o a) \<longlonglongrightarrow>  limsup (u o r) + limsup (v o r o s)" by simp
  then have "limsup w =  limsup (u o r) + limsup (v o r o s)" using l(1) using LIMSEQ_unique by blast
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

  def w \<equiv> "\<lambda>n. u n + v n"
  obtain r where r: "subseq r" "(w o r) \<longlonglongrightarrow> liminf w" using liminf_subseq_lim by auto
  obtain s where s: "subseq s" "(u o r o s) \<longlonglongrightarrow> liminf (u o r)" using liminf_subseq_lim by auto
  obtain t where t: "subseq t" "(v o r o s o t) \<longlonglongrightarrow> liminf (v o r o s)" using liminf_subseq_lim by auto

  def a \<equiv> "r o s o t"
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
  then have b: "liminf (v o r o s)  \<noteq> -\<infinity>" using `liminf v > -\<infinity>` by auto

  have "(\<lambda>n. (u o a) n + (v o a) n) \<longlonglongrightarrow> liminf (u o r) + liminf (v o r o s)"
    using l tendsto_add_ereal_general a b by fastforce
  moreover have "(\<lambda>n. (u o a) n + (v o a) n) = (w o a)" unfolding w_def by auto
  ultimately have "(w o a) \<longlonglongrightarrow>  liminf (u o r) + liminf (v o r o s)" by simp
  then have "liminf w =  liminf (u o r) + liminf (v o r o s)" using l(1) using LIMSEQ_unique by blast
  then have "liminf w \<ge> liminf u + liminf v"
    using `liminf (u o r) \<ge> liminf u` `liminf (v o r o s) \<ge> liminf v` ereal_add_mono by simp
  then show ?thesis unfolding w_def by simp
qed

lemma ereal_limsup_lim_add:
  fixes u v::"nat \<Rightarrow> ereal"
  assumes "u \<longlonglongrightarrow> a" "abs(a) \<noteq> \<infinity>"
  shows "limsup (\<lambda>n. u n + v n) = a + limsup v"
proof -
  have "limsup u = a" using assms(1) using tendsto_iff_Liminf_eq_Limsup trivial_limit_at_top_linorder by auto
  have "(\<lambda>n. -u n) \<longlonglongrightarrow> -a" using assms(1) by auto
  then have "limsup (\<lambda>n. -u n) = -a" using tendsto_iff_Liminf_eq_Limsup trivial_limit_at_top_linorder by auto

  have "limsup (\<lambda>n. u n + v n) \<le> limsup u + limsup v"
    by (rule ereal_limsup_add_mono)
  then have up: "limsup (\<lambda>n. u n + v n) \<le> a + limsup v" using `limsup u = a` by simp

  have a: "limsup (\<lambda>n. (u n + v n) + (-u n)) \<le> limsup (\<lambda>n. u n + v n) + limsup (\<lambda>n. -u n)"
    by (rule ereal_limsup_add_mono)
  have "eventually (\<lambda>n.  u n = ereal(real_of_ereal(u n))) sequentially" using assms
    real_lim_then_eventually_real by auto
  moreover have "\<And>x. x = ereal(real_of_ereal(x)) \<Longrightarrow> x + (-x) = 0"
    by (metis plus_ereal.simps(1) right_minus uminus_ereal.simps(1) zero_ereal_def)
  ultimately have "eventually (\<lambda>n. u n + (-u n) = 0) sequentially"
    by (metis (mono_tags, lifting) eventually_mono)
  moreover have "\<And>n. u n + (-u n) = 0 \<Longrightarrow> u n + v n + (-u n) = v n"
    by (metis add.commute add.left_commute add.left_neutral)
  ultimately have "eventually (\<lambda>n. u n + v n + (-u n) = v n) sequentially"
    using eventually_mono by force
  then have "limsup v = limsup (\<lambda>n.  u n + v n + (-u n))" using Limsup_eq by force
  then have "limsup v \<le> limsup (\<lambda>n. u n + v n) -a" using a `limsup (\<lambda>n. -u n) = -a` by (simp add: minus_ereal_def)
  then have "limsup (\<lambda>n. u n + v n) \<ge> a + limsup v" using assms(2) by (metis add.commute ereal_le_minus)
  then show ?thesis using up by simp
qed

lemma ereal_liminf_lim_add:
  fixes u v::"nat \<Rightarrow> ereal"
  assumes "u \<longlonglongrightarrow> a" "abs(a) \<noteq> \<infinity>"
  shows "liminf (\<lambda>n. u n + v n) = a + liminf v"
proof -
  have "liminf u = a" using assms(1) using tendsto_iff_Liminf_eq_Limsup trivial_limit_at_top_linorder by auto
  then have *: "abs(liminf u) \<noteq> \<infinity>" using assms(2) by auto
  have "(\<lambda>n. -u n) \<longlonglongrightarrow> -a" using assms(1) by auto
  then have "liminf (\<lambda>n. -u n) = -a" using tendsto_iff_Liminf_eq_Limsup trivial_limit_at_top_linorder by auto
  then have **: "abs(liminf  (\<lambda>n. -u n)) \<noteq> \<infinity>" using assms(2) by auto

  have "liminf (\<lambda>n. u n + v n) \<ge> liminf u + liminf v"
    apply (rule ereal_liminf_add_mono) using * by auto
  then have up: "liminf  (\<lambda>n. u n + v n)  \<ge> a + liminf v" using `liminf u = a` by simp

  have a: "liminf (\<lambda>n. (u n + v n) + (-u n)) \<ge> liminf (\<lambda>n. u n + v n) + liminf (\<lambda>n. -u n)"
    apply (rule ereal_liminf_add_mono) using ** by auto
  have "eventually (\<lambda>n.  u n = ereal(real_of_ereal(u n))) sequentially" using assms
    real_lim_then_eventually_real by auto
  moreover have "\<And>x. x = ereal(real_of_ereal(x)) \<Longrightarrow> x + (-x) = 0"
    by (metis plus_ereal.simps(1) right_minus uminus_ereal.simps(1) zero_ereal_def)
  ultimately have "eventually (\<lambda>n. u n + (-u n) = 0) sequentially"
    by (metis (mono_tags, lifting) eventually_mono)
  moreover have "\<And>n. u n + (-u n) = 0 \<Longrightarrow> u n + v n + (-u n) = v n"
    by (metis add.commute add.left_commute add.left_neutral)
  ultimately have "eventually (\<lambda>n. u n + v n + (-u n) = v n) sequentially"
    using eventually_mono by force
  then have "liminf v = liminf (\<lambda>n.  u n + v n + (-u n))" using Liminf_eq by force
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

  def w \<equiv> "\<lambda>n. u n + v n"
  obtain r where r: "subseq r" "(u o r) \<longlonglongrightarrow> liminf u" using liminf_subseq_lim by auto
  obtain s where s: "subseq s" "(w o r o s) \<longlonglongrightarrow> liminf (w o r)" using liminf_subseq_lim by auto
  obtain t where t: "subseq t" "(v o r o s o t) \<longlonglongrightarrow> limsup (v o r o s)" using limsup_subseq_lim by auto

  def a \<equiv> "r o s o t"
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
  then have b: "limsup (v o r o s)  < \<infinity>" using `limsup v < \<infinity>` by auto

  have "(\<lambda>n. (u o a) n + (v o a) n) \<longlonglongrightarrow> liminf u + limsup (v o r o s)"
   apply (rule tendsto_add_ereal_general) using b  `liminf u < \<infinity>` l(1) l(3) by force+
  moreover have "(\<lambda>n. (u o a) n + (v o a) n) = (w o a)" unfolding w_def by auto
  ultimately have "(w o a) \<longlonglongrightarrow>  liminf u + limsup (v o r o s)" by simp
  then have "liminf (w o r) =  liminf u + limsup (v o r o s)" using l(2) using LIMSEQ_unique by blast
  then have "liminf w \<le> liminf u + limsup v"
    using `liminf (w o r) \<ge> liminf w` `limsup (v o r o s) \<le> limsup v`
    by (metis add_mono_thms_linordered_semiring(2) le_less_trans not_less)
  then show ?thesis unfolding w_def by simp
qed

lemma ereal_limsup_lim_mult:
  fixes u v::"nat \<Rightarrow> ereal"
  assumes "u \<longlonglongrightarrow> a" "a>0" "a \<noteq> \<infinity>"
  shows "limsup (\<lambda>n. u n * v n) = a * limsup v"
proof -
  def w \<equiv> "\<lambda>n. u n * v n"
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
  moreover
  {
     fix n assume "(u o s) n > 0" "(u o s) n < \<infinity>"
     then have "(w o s) n / (u o s) n = (v o s) n" unfolding w_def by (auto simp add: ereal_divide_eq)
  }
  ultimately have "eventually (\<lambda>n. (w o s) n / (u o s) n = (v o s) n) sequentially" using eventually_elim2 by force
  moreover have "(\<lambda>n. (w o s) n / (u o s) n) \<longlonglongrightarrow> (limsup w) / a"
    apply (rule tendsto_divide_ereal[OF s(2) *]) using assms(2) assms(3) by auto
  ultimately have "(v o s) \<longlonglongrightarrow> (limsup w) / a" using Lim_transform_eventually by fastforce
  then have "limsup (v o s) =  (limsup w) / a" by (simp add: tendsto_iff_Liminf_eq_Limsup)
  then have "limsup v \<ge> (limsup w) / a" by (metis limsup_subseq_mono s(1))
  then have "a * limsup v \<ge> limsup w" using assms(2) assms(3) by (simp add: ereal_divide_le_pos)
  then show ?thesis using I unfolding w_def by auto
qed

lemma ereal_liminf_lim_mult:
  fixes u v::"nat \<Rightarrow> ereal"
  assumes "u \<longlonglongrightarrow> a" "a>0" "a \<noteq> \<infinity>"
  shows "liminf (\<lambda>n. u n * v n) = a * liminf v"
proof -
  def w \<equiv> "\<lambda>n. u n * v n"
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
  moreover
  {
     fix n assume "(u o s) n > 0" "(u o s) n < \<infinity>"
     then have "(w o s) n / (u o s) n = (v o s) n" unfolding w_def by (auto simp add: ereal_divide_eq)
  }
  ultimately have "eventually (\<lambda>n. (w o s) n / (u o s) n = (v o s) n) sequentially" using eventually_elim2 by force
  moreover have "(\<lambda>n. (w o s) n / (u o s) n) \<longlonglongrightarrow> (liminf w) / a"
    apply (rule tendsto_divide_ereal[OF s(2) *]) using assms(2) assms(3) by auto
  ultimately have "(v o s) \<longlonglongrightarrow> (liminf w) / a" using Lim_transform_eventually by fastforce
  then have "liminf (v o s) =  (liminf w) / a" by (simp add: tendsto_iff_Liminf_eq_Limsup)
  then have "liminf v \<le> (liminf w) / a" by (metis liminf_subseq_mono s(1))
  then have "a * liminf v \<le> liminf w" using assms(2) assms(3) by (simp add: ereal_le_divide_pos)
  then show ?thesis using I unfolding w_def by auto
qed


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
  {
    fix m
    have "\<And>n. A (m+n) \<subseteq> A n"
    proof (induct m)
      case 0 show ?case by simp
    next
      case (Suc m) thus ?case
        by (metis Suc_eq_plus1 assms add.commute add.left_commute subset_trans)
    qed
  }
  hence "\<And>m n. m > n \<Longrightarrow> A m \<subseteq> A n"
    by (metis add.commute le_add_diff_inverse nat_less_le)
  thus ?thesis
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
proof -
  {
    fix x
    have "{f i x |i. i \<in> I} =  (\<lambda>i. f i x)`I" by blast
    then have "Max {f i x |i. i \<in> I} = Max ((\<lambda>i. f i x)`I)" by simp
  }
  moreover have "(\<lambda>x. Max ((\<lambda>i. f i x)`I)) \<in> borel_measurable M"
    using borel_measurable_Max[OF assms(1), where ?f=f and ?M=M] assms by simp
  ultimately show ?thesis by simp
qed

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
  ultimately have "\<And>(n::nat). f-`{n} \<inter> space M  \<in> sets M" by simp
  thus ?thesis using measurable_count_space_eq2_countable by blast
qed

lemma measurable_equality_set [measurable]:
  fixes f g::"_\<Rightarrow> 'a::{second_countable_topology, t2_space}"
  assumes [measurable]: "f \<in> borel_measurable M" "g \<in> borel_measurable M"
  shows "{x \<in> space M. f x = g x} \<in> sets M"
proof -
  def A \<equiv> "{x \<in> space M. f x = g x}"
  def B \<equiv> "{y. \<exists>x::'a. y = (x,x)}"
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
  def F \<equiv> "(\<lambda>x. (f x, g x))"
  have * [measurable]: "F \<in> borel_measurable M" unfolding F_def by simp

  have "{x \<in> space M. f x \<le> g x} = F-`{(x, y) | x y. x \<le> y} \<inter> space M" unfolding F_def by auto
  moreover have "{(x, y) | x y. x \<le> (y::'a)} \<in> sets borel"  using closed_subdiagonal borel_closed by blast
  ultimately show "{x \<in> space M. f x \<le> g x} \<in> sets M" using * by (metis (mono_tags, lifting) measurable_sets)

  have "{x \<in> space M. f x < g x} = F-`{(x, y) | x y. x < y} \<inter> space M" unfolding F_def by auto
  moreover have "{(x, y) | x y. x < (y::'a)} \<in> sets borel"  using open_subdiagonal borel_open by blast
  ultimately show "{x \<in> space M. f x < g x} \<in> sets M" using * by (metis (mono_tags, lifting) measurable_sets)

  have "{x \<in> space M. f x \<ge> g x} = F-`{(x, y) | x y. x \<ge> y} \<inter> space M" unfolding F_def by auto
  moreover have "{(x, y) | x y. x \<ge> (y::'a)} \<in> sets borel"  using closed_superdiagonal borel_closed by blast
  ultimately show "{x \<in> space M. f x \<ge> g x} \<in> sets M" using * by (metis (mono_tags, lifting) measurable_sets)

  have "{x \<in> space M. f x > g x} = F-`{(x, y) | x y. x > y} \<inter> space M" unfolding F_def by auto
  moreover have "{(x, y) | x y. x > (y::'a)} \<in> sets borel"  using open_superdiagonal borel_open by blast
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

  {
    fix u::"nat \<Rightarrow> 'b"
    have "(u \<longlonglongrightarrow> c) \<longleftrightarrow> (\<forall>i. eventually (\<lambda>n. u n \<in> A i) sequentially)"
    proof
      assume "u \<longlonglongrightarrow> c"
      {
        fix i
        have "eventually (\<lambda>n. u n \<in> A i) sequentially" using A(1)[of i] A(2)[of i] `u \<longlonglongrightarrow> c`
          by (simp add: topological_tendstoD)
      }
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
  }
  then have "{x. (\<lambda>n. f n x) \<longlonglongrightarrow> c} = (\<Inter>i. \<Union>n. \<Inter>N\<in>{n..}. (f N)-`(A i))"
    by (auto simp add: atLeast_def eventually_at_top_linorder)
  then have "{x \<in> space M. (\<lambda>n. f n x) \<longlonglongrightarrow> c} = (\<Inter>i. \<Union>n. \<Inter>N\<in>{n..}. (f N)-`(A i) \<inter> space M)"
    by auto
  then have "{x \<in> space M. (\<lambda>n. f n x) \<longlonglongrightarrow> c} \<in> sets M" using mes by simp
  then show ?thesis by auto
qed

lemma measurable_P_restriction [measurable (raw)]:
  assumes [measurable]: "Measurable.pred M P" "A \<in> sets M"
  shows "{x \<in> A. P x} \<in> sets M"
proof -
  have "A \<subseteq> space M" using sets.sets_into_space[OF assms(2)].
  then have "{x \<in> A. P x} = A \<inter> {x \<in> space M. P x}" by blast
  then show ?thesis by auto
qed

lemma measurable_setsum_nat [measurable (raw)]:
  fixes f :: "'c \<Rightarrow> 'a \<Rightarrow> nat"
  assumes "\<And>i. i \<in> S \<Longrightarrow> f i \<in> measurable M (count_space UNIV)"
  shows "(\<lambda>x. \<Sum>i\<in>S. f i x) \<in> measurable M (count_space UNIV)"
proof cases
  assume "finite S"
  thus ?thesis using assms by induct auto
qed simp

lemma measurable_limsup [measurable (raw)]:
  assumes [measurable]: "\<And>n. A n \<in> sets M"
  shows "limsup A \<in> sets M"
by (subst limsup_INF_SUP, auto)

lemma measurable_liminf [measurable (raw)]:
  assumes [measurable]: "\<And>n. A n \<in> sets M"
  shows "liminf A \<in> sets M"
by (subst liminf_SUP_INF, auto)


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
     then have *: "f-`B \<inter> A n = h-`B \<inter> A n"  by auto
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

lemma AE_E3:
  assumes "AE x in M. P x"
  obtains N where "\<And>x. x \<in> space M - N \<Longrightarrow> P x" "N \<in> null_sets M"
using assms unfolding eventually_ae_filter by auto

lemma AE_equal_setsum:
  assumes "\<And>i. AE x in M. f i x = g i x"
  shows "AE x in M. (\<Sum>i\<in>I. f i x) = (\<Sum>i\<in>I. g i x)"
proof (cases)
  assume "finite I"
  have "\<exists>A. A \<in> null_sets M \<and> (\<forall>x\<in> (space M - A). f i x = g i x)" for i
    using assms(1)[of i] by (metis (mono_tags, lifting) AE_E3)
  then obtain A where A: "\<And>i. A i \<in> null_sets M \<and> (\<forall>x\<in> (space M -A i). f i x = g i x)"
    by metis
  def B \<equiv> "(\<Union>i\<in>I. A i)"
  have "B \<in> null_sets M" using `finite I` A B_def by blast
  then have "AE x in M. x \<in> space M - B" by (simp add: null_setsD_AE)
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
    using assms(1) emeasure_less_0_iff linorder_cases by blast
  then have "(\<Union>N. A N) \<in> null_sets M" by auto
  then show False using assms(2) by auto
qed


lemma emeasure_union_summable:
  assumes [measurable]: "\<And>n. A n \<in> sets M" and "\<And>n. emeasure M (A n) < \<infinity>" "summable (\<lambda>n. measure M (A n))"
  shows "emeasure M (\<Union>n. A n) < \<infinity>" "emeasure M (\<Union>n. A n) \<le> (\<Sum>n. measure M (A n))"
proof -
  def B \<equiv> "\<lambda>N. (\<Union>n\<in>{..<N}. A n)"
  have [measurable]: "B N \<in> sets M" for N unfolding B_def by auto
  have "(\<lambda>N. emeasure M (B N)) \<longlonglongrightarrow> emeasure M (\<Union>N. B N)"
    apply (rule Lim_emeasure_incseq) unfolding B_def by (auto simp add: SUP_subset_mono incseq_def)
  moreover have "emeasure M (B N) \<le> ereal (\<Sum>n. measure M (A n))" for N
  proof -
    have *: "(\<Sum>n\<in>{..<N}. measure M (A n)) \<le> (\<Sum>n. measure M (A n))"
      using assms(3) measure_nonneg setsum_le_suminf by blast

    have "emeasure M (B N) \<le> (\<Sum>n\<in>{..<N}. emeasure M (A n))"
      unfolding B_def by (rule emeasure_subadditive_finite, auto)
    also have "... = (\<Sum>n\<in>{..<N}. ereal(measure M (A n)))"
      using assms(2) by (simp add: emeasure_eq_ereal_measure)
    also have "... = ereal (\<Sum>n\<in>{..<N}. measure M (A n))"
      by auto
    also have "... \<le> ereal (\<Sum>n. measure M (A n))"
      using * by auto
    finally show ?thesis by simp
  qed
  ultimately have "emeasure M (\<Union>N. B N) \<le> ereal (\<Sum>n. measure M (A n))"
    by (simp add: Lim_bounded_ereal)
  then show "emeasure M (\<Union>n. A n) \<le> (\<Sum>n. measure M (A n))"
    unfolding B_def by (metis UN_UN_flatten UN_lessThan_UNIV)
  then show "emeasure M (\<Union>n. A n) < \<infinity>" by auto
qed

lemma (in sigma_finite_measure) approx_PInf_emeasure_with_finite:
  fixes C::real
  assumes W_meas: "W \<in> sets M"
     and  W_inf: "emeasure M W = \<infinity>"
  obtains Z where "Z \<in> sets M" "Z \<subseteq> W" "emeasure M Z < \<infinity>" "emeasure M Z > C"
proof -
  obtain A :: "nat \<Rightarrow> 'a set"
    where "range A \<subseteq> sets M" "(\<Union>i. A i) = space M" "\<And>i. emeasure M (A i) \<noteq> \<infinity>" "incseq A"
    using sigma_finite_incseq by auto
  def B \<equiv> "\<lambda>i. W \<inter> A i"
  have B_meas: "\<And>i. B i \<in> sets M" using W_meas `range A \<subseteq> sets M` B_def by blast
  have b: "\<And>i. B i \<subseteq> W" using B_def by blast
  have "\<And>i. emeasure M (A i) < \<infinity>" using `\<And>i. emeasure M (A i) \<noteq> \<infinity>` by simp
  moreover have "\<And>i. A i \<in> sets M" using `range A \<subseteq> sets M` by simp
  ultimately have c: "\<And>i. emeasure M (B i) < \<infinity>"
    by (metis ereal_infty_less(1) ereal_infty_less_eq(1) le_inf_iff subsetI B_def emeasure_mono)

  have "W = (\<Union>i. B i)" using B_def `(\<Union>i. A i) = space M` W_meas by auto
  moreover have "incseq B" using B_def `incseq A` by (simp add: incseq_def subset_eq)
  ultimately have "(\<lambda>i. emeasure M (B i)) \<longlonglongrightarrow> emeasure M W" using W_meas B_meas
    by (simp add: B_meas Lim_emeasure_incseq image_subset_iff)
  then have "(\<lambda>i. emeasure M (B i)) \<longlonglongrightarrow> \<infinity>" using W_inf by simp
  moreover have "C < \<infinity>" by auto
  ultimately obtain i where d: "emeasure M (B i) > C" by (meson Lim_bounded_PInfty not_le)
  have "B i \<in> sets M" "B i \<subseteq> W" "emeasure M (B i) < \<infinity>" "emeasure M (B i) > C" using B_meas b c d by auto
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


lemma AE_count_union:
  assumes "\<And>(N::nat). N \<in> I \<Longrightarrow> AE x in M. P N x" "countable I"
  shows "AE x in M. \<forall>N \<in> I. P N x"
proof -
  def C \<equiv> "\<lambda>N. {x. P N x}"
  have "AE x in M. x \<in> C N" if "N \<in> I" for N unfolding C_def using assms that by auto
  then have "\<exists>D. D \<in> null_sets M \<and> (space M - D) \<subseteq> C N" if "N \<in> I" for N
     by (metis that AE_E3 subsetI)
  then obtain D where D: "\<And>N. N \<in> I \<Longrightarrow> D N \<in> null_sets M" "\<And>N. N \<in> I \<Longrightarrow>(space M - D N) \<subseteq> C N"
    by metis
  def E \<equiv> "(\<Union>N\<in>I. D N)"
  have "E \<in> null_sets M" unfolding E_def using D(1) assms(2) by (simp add: null_sets_UN')
  then have "AE x in M. x \<in> space M - E" unfolding eventually_ae_filter by blast
  moreover
  {
    fix x assume "x \<in> space M - E"
    then have "x \<in> C N" if "N \<in> I" for N unfolding E_def using D(2) that by blast
    then have "\<forall>N\<in>I. P N x" unfolding C_def by auto
  }
  ultimately show ?thesis by auto
qed

lemma AE_upper_bound_inf_ereal:
  fixes F G::"'a \<Rightarrow> ereal"
  assumes "\<And>e. e > 0 \<Longrightarrow> AE x in M. F x \<le> G x + e"
  shows "AE x in M. F x \<le> G x"
proof -
  have "AE x in M. F x \<le> G x +  1/real (n+1)" for n::nat
    by (rule assms, auto)
  then have "AE x in M. \<forall>n::nat \<in> UNIV. F x \<le> G x +  1/real (n+1)"
    by (rule AE_count_union, auto)
  moreover
  {
    fix x assume i: "\<forall>n::nat \<in> UNIV. F x \<le> G x +  1/real (n+1)"
    have "(\<lambda>n. (1/(real (n+1)))) \<longlonglongrightarrow> 0" using lim_1_over_n LIMSEQ_ignore_initial_segment by blast
    then have *: "(\<lambda>n. ereal(1/(real (n+1)))) \<longlonglongrightarrow> 0" by (simp add: zero_ereal_def)
    have "(\<lambda>n. G x +  1/real (n+1)) \<longlonglongrightarrow> G x + 0"
      apply (rule tendsto_add_ereal_general) using * by auto
    then have "F x \<le> G x" using i LIMSEQ_le_const by fastforce
  }
  ultimately show ?thesis by auto
qed

lemma AE_upper_bound_inf_ereal2:
  fixes F G::"'a \<Rightarrow> ereal"
  assumes "\<And>e. e > (0::real) \<Longrightarrow> AE x in M. F x \<le> G x + e"
  shows "AE x in M. F x \<le> G x"
proof -
  have "AE x in M. F x \<le> G x + e" if "e > (0::ereal)" for e
    apply (cases e) using `e > 0` assms by auto
  then show ?thesis using AE_upper_bound_inf_ereal by auto
qed

lemma AE_upper_bound_inf:
  fixes F G::"'a \<Rightarrow> real"
  assumes "\<And>e. e > 0 \<Longrightarrow> AE x in M. F x \<le> G x + e"
  shows "AE x in M. F x \<le> G x"
proof -
  have "AE x in M. F x \<le> G x +  1/real (n+1)" for n::nat
    by (rule assms, auto)
  then have "AE x in M. \<forall>n::nat \<in> UNIV. F x \<le> G x +  1/real (n+1)"
    by (rule AE_count_union, auto)
  moreover
  {
    fix x assume i: "\<forall>n::nat \<in> UNIV. F x \<le> G x +  1/real (n+1)"
    have *: "(\<lambda>n. (1/(real (n+1)))) \<longlonglongrightarrow> 0" using lim_1_over_n LIMSEQ_ignore_initial_segment by blast
    have "(\<lambda>n. G x +  1/real (n+1)) \<longlonglongrightarrow> G x + 0"
      apply (rule tendsto_add) using * by auto
    then have "F x \<le> G x" using i LIMSEQ_le_const by fastforce
  }
  ultimately show ?thesis by auto
qed

lemma not_AE_zero_ereal_E:
  fixes f::"'a \<Rightarrow> ereal"
  assumes "AE x in M. f x \<ge> 0"
          "\<not>(AE x in M. f x = 0)"
    and [measurable]: "f \<in> borel_measurable M"
 shows "\<exists>A e. A \<in> sets M \<and> e>(0::real) \<and> emeasure M A > 0 \<and> (\<forall>x \<in> A. f x \<ge> e)"
proof -
  have "\<exists>e. e > (0::real) \<and> {x \<in> space M. f x \<ge> e} \<notin> null_sets M"
  proof (rule ccontr)
    assume *: "\<not>(\<exists>e. e > (0::real) \<and> {x \<in> space M. f x \<ge> e} \<notin> null_sets M)"
    {
      fix e::real assume "e > 0"
      then have "{x \<in> space M. f x \<ge> e} \<in> null_sets M" using * by blast
      then have "AE x in M. x \<notin> {x \<in> space M. f x \<ge> e}" using null_setsD_AE by blast
      then have "AE x in M. f x \<le> e" by auto
    }
    then have "AE x in M. f x \<le> 0" using AE_upper_bound_inf_ereal2[where ?F = f and ?G = "\<lambda>x. 0" and ?M= M] by auto
    then have "AE x in M. f x = 0" using assms(1) by auto
    then show False using assms(2) by auto
  qed
  then obtain e::real where e: "e>0" "{x \<in> space M. f x \<ge> e} \<notin> null_sets M" by auto
  def A \<equiv> "{x \<in> space M. f x \<ge> e}"
  have 1 [measurable]: "A \<in> sets M" unfolding A_def by auto
  have 2: "emeasure M A > 0"
    using e(2) A_def \<open>A \<in> sets M\<close> emeasure_less_0_iff linorder_cases by blast
  have 3: "\<And>x. x \<in> A \<Longrightarrow> f x \<ge> e" unfolding A_def by auto
  show ?thesis using e(1) 1 2 3 by blast
qed

lemma not_AE_zero_E:
  fixes f::"'a \<Rightarrow> real"
  assumes "AE x in M. f x \<ge> 0"
          "\<not>(AE x in M. f x = 0)"
    and [measurable]: "f \<in> borel_measurable M"
 shows "\<exists>A e. A \<in> sets M \<and> e>0 \<and> emeasure M A > 0 \<and> (\<forall>x \<in> A. f x \<ge> e)"
proof -
  have "\<exists>e. e > 0 \<and> {x \<in> space M. f x \<ge> e} \<notin> null_sets M"
  proof (rule ccontr)
    assume *: "\<not>(\<exists>e. e > 0 \<and> {x \<in> space M. f x \<ge> e} \<notin> null_sets M)"
    {
      fix e::real assume "e > 0"
      then have "{x \<in> space M. f x \<ge> e} \<in> null_sets M" using * by blast
      then have "AE x in M. x \<notin> {x \<in> space M. f x \<ge> e}" using null_setsD_AE by blast
      then have "AE x in M. f x \<le> e" by auto
    }
    then have "AE x in M. f x \<le> 0" by (rule AE_upper_bound_inf, auto)
    then have "AE x in M. f x = 0" using assms(1) by auto
    then show False using assms(2) by auto
  qed
  then obtain e where e: "e>0" "{x \<in> space M. f x \<ge> e} \<notin> null_sets M" by auto
  def A \<equiv> "{x \<in> space M. f x \<ge> e}"
  have 1 [measurable]: "A \<in> sets M" unfolding A_def by auto
  have 2: "emeasure M A > 0"
    using e(2) A_def \<open>A \<in> sets M\<close> emeasure_less_0_iff linorder_cases by blast
  have 3: "\<And>x. x \<in> A \<Longrightarrow> f x \<ge> e" unfolding A_def by auto
  show ?thesis
    using e(1) 1 2 3 by blast
qed

lemma borel_cantelli_limsup1:
  assumes [measurable]: "\<And>n. A n \<in> sets M" and "\<And>n. emeasure M (A n) < \<infinity>" "summable (\<lambda>n. measure M (A n))"
  shows "limsup A \<in> null_sets M"
proof -
  have "(\<lambda>n. (\<Sum>k. measure M (A (k+n)))) \<longlonglongrightarrow> 0" by (rule suminf_exist_split2[OF assms(3)])
  then have "(\<lambda>n. ereal (\<Sum>k. measure M (A (k+n)))) \<longlonglongrightarrow> 0" by (simp add: zero_ereal_def)
  moreover have "emeasure M (limsup A) \<le> (\<Sum>k. measure M (A (k+n)))" for n
  proof -
    have I: "(\<Union>k\<in>{n..}. A k) =  (\<Union>k. A (k+n))" by (auto, metis le_add_diff_inverse2, fastforce)
    have "emeasure M (limsup A) \<le> emeasure M (\<Union>k\<in>{n..}. A k)"
      by (rule emeasure_mono, auto simp add: limsup_INF_SUP)
    also have "... = emeasure M (\<Union>k. A (k+n))"
      using I by auto
    also have "... \<le> (\<Sum>k. measure M (A (k+n)))"
      apply (rule emeasure_union_summable) using assms summable_ignore_initial_segment[OF assms(3), of n] by auto
    finally show ?thesis by simp
  qed
  ultimately have "emeasure M (limsup A) \<le> 0" by (simp add: LIMSEQ_le_const)
  then show ?thesis using emeasure_le_0_iff assms(1) measurable_limsup by blast
qed

lemma borel_cantelli_AE1:
  assumes [measurable]: "\<And>n. A n \<in> sets M" and "\<And>n. emeasure M (A n) < \<infinity>" "summable (\<lambda>n. measure M (A n))"
  shows "AE x in M. eventually (\<lambda>n. x \<in> space M - A n) sequentially"
proof -
  have "AE x in M. x \<notin> limsup A" using borel_cantelli_limsup1[OF assms] unfolding eventually_ae_filter by auto
  moreover
  {
    fix x assume "x \<notin> limsup A"
    then obtain N where "x \<notin> (\<Union>n\<in>{N..}. A n)" unfolding limsup_INF_SUP by blast
    then have "eventually (\<lambda>n. x \<notin> A n) sequentially" using eventually_sequentially by auto
  }
  ultimately show ?thesis by auto
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
    by (rule nn_integral_density[symmetric]) (simp_all add: assms)
  finally show ?thesis by simp
qed

lemma not_AE_zero_int_ereal_E:
  fixes f::"'a \<Rightarrow> ereal"
  assumes "AE x in M. f x \<ge> 0"
          "(\<integral>\<^sup>+x. f x \<partial>M) > 0"
    and [measurable]: "f \<in> borel_measurable M"
 shows "\<exists>A e. A \<in> sets M \<and> e>(0::real) \<and> emeasure M A > 0 \<and> (\<forall>x \<in> A. f x \<ge> e)"
proof (rule not_AE_zero_ereal_E, auto simp add: assms)
  assume *: "AE x in M. f x = 0"
  have "(\<integral>\<^sup>+x. f x \<partial>M) = (\<integral>\<^sup>+x. 0 \<partial>M)" by (rule nn_integral_cong_AE, simp add: *)
  then have "(\<integral>\<^sup>+x. f x \<partial>M) = 0" by simp
  then show False using assms(2) by simp
qed

lemma (in finite_measure) nn_integral_bounded_eq_bound_then_AE:
  assumes "AE x in M. f x \<le> ereal c" "AE x in M. f x \<ge> 0"
     "(\<integral>\<^sup>+x. f x \<partial>M) = c * emeasure M (space M)"
   and [measurable]: "f \<in> borel_measurable M"
  shows "AE x in M. f x = c"
proof (cases)
  assume "emeasure M (space M) = 0"
  then show ?thesis using eventually_ae_filter by blast
next
  assume "\<not>(emeasure M (space M) = 0)"
  then have "c \<ge> 0"
    by (metis assms(3) emeasure_le_0_iff ereal_less_eq(5) ereal_zero_le_0_iff nn_integral_nonneg)
  have fin: "AE x in M. abs(f x) \<noteq> \<infinity>" using assms by auto
  def g \<equiv> "\<lambda>x. c - f x"
  have [measurable]: "g \<in> borel_measurable M" unfolding g_def by auto
  have "(\<integral>\<^sup>+x. g x \<partial>M) = (\<integral>\<^sup>+x. c \<partial>M) - (\<integral>\<^sup>+x. f x \<partial>M)"
    unfolding g_def by (rule nn_integral_diff, auto simp add: assms)
  then have *: "(\<integral>\<^sup>+x. g x \<partial>M) = 0" using assms(3) `c \<ge> 0` by auto
  have "AE x in M. g x \<le> 0"
    by (subst nn_integral_0_iff_AE[symmetric], auto simp add: *)
  then have "AE x in M. c \<le> f x" unfolding g_def using fin by auto
  then show ?thesis using assms(1) by auto
qed


subsection {*Lebesgue-Measure.thy*}

text{* The next lemma is the same as \verb+lborel_distr_plus+ which is only formulated
on the real line, but on any euclidean space *}

lemma lborel_distr_plus2:
  fixes c :: "'a::euclidean_space"
  shows "distr lborel borel (op + c) = lborel"
by (subst lborel_affine[of 1 c]) (auto simp: density_1 one_ereal_def[symmetric])


subsection {*Set-Integral.thy *}

text{* I introduce a notation for positive set integrals, which is not available in
 \verb+Set_Integral.thy+. The notation I use is not directly in line with the
notations in this file, they are more in line with setsum, and more readable I think. *}

abbreviation "set_nn_integral M A f \<equiv> nn_integral M (\<lambda>x. f x * indicator A x)"

syntax
"_set_nn_integral" :: "pttrn => 'a set => 'a measure => ereal => ereal"
("(\<integral>\<^sup>+((_)\<in>(_)./ _)/\<partial>_)" [0,60,110,61] 60)

"_set_lebesgue_integral" :: "pttrn => 'a set => 'a measure => ereal => ereal"
("(\<integral>((_)\<in>(_)./ _)/\<partial>_)" [0,60,110,61] 60)

translations
"\<integral>\<^sup>+x \<in> A. f \<partial>M" == "CONST set_nn_integral M A (\<lambda>x. f)"
"\<integral>x \<in> A. f \<partial>M"  == "CONST set_lebesgue_integral M A (\<lambda>x. f)"

lemma nn_integral_disjoint_pair:
  assumes [measurable]: "f \<in> borel_measurable M" and
          "AE x in M. f x \<ge> 0"
          "B \<in> sets M" "C \<in> sets M"
          "B \<inter> C = {}"
  shows "(\<integral>\<^sup>+x \<in> B \<union> C. f x \<partial>M) = (\<integral>\<^sup>+x \<in> B. f x \<partial>M) + (\<integral>\<^sup>+x \<in> C. f x \<partial>M)"
proof -
  have mes: "\<And>D. D \<in> sets M \<Longrightarrow> (\<lambda>x. f x * indicator D x) \<in> borel_measurable M" by simp
  have pos: "\<And>D. AE x in M. f x * indicator D x \<ge> 0" using assms(2) by auto
  have "\<And>x. f x * indicator (B \<union> C) x = f x * indicator B x + f x * indicator C x" using assms(5)
    by (metis ereal_indicator_nonneg ereal_right_distrib indicator_add)
  hence "(\<integral>\<^sup>+x. f x * indicator (B \<union> C) x \<partial>M) = (\<integral>\<^sup>+x. f x * indicator B x + f x * indicator C x \<partial>M)"
    by simp
  also have "... = (\<integral>\<^sup>+x. f x * indicator B x \<partial>M) +  (\<integral>\<^sup>+x. f x * indicator C x \<partial>M)"
    by (rule nn_integral_add) (auto simp add: assms mes pos)
  finally show ?thesis by simp
qed

lemma nn_integral_disjoint_pair_countspace:
  assumes "\<And>x. f x \<ge> 0"
          "B \<inter> C = {}"
  shows "(\<integral>\<^sup>+x \<in> B \<union> C. f x \<partial>count_space UNIV) = (\<integral>\<^sup>+x \<in> B. f x \<partial>count_space UNIV) + (\<integral>\<^sup>+x \<in> C. f x \<partial>count_space UNIV)"
by (rule nn_integral_disjoint_pair) (simp_all add: assms)

lemma nn_integral_null_delta:
  assumes "A \<in> sets M" "B \<in> sets M"
          "A \<Delta> B \<in> null_sets M"
  shows "(\<integral>\<^sup>+x \<in> A. f x \<partial>M) = (\<integral>\<^sup>+x \<in> B. f x \<partial>M)"
proof (rule nn_integral_cong_AE, auto simp add: indicator_def)
  have *: "AE a in M. a \<notin> A \<Delta> B"
    using assms(3) null_setsD_AE by blast
  thus "AE a in M. a \<notin> A \<longrightarrow> a \<in> B \<longrightarrow> f a = 0"
    by auto
  show "AE x\<in>A in M. x \<notin> B \<longrightarrow> f x = 0"
    using * by auto
qed

lemma nn_integral_disjoint_family:
  assumes [measurable]: "f \<in> borel_measurable M"
          "\<And>(n::nat). B n \<in> sets M"
      and "disjoint_family B"
          "AE x in M. f x \<ge> 0"
   shows "(\<integral>\<^sup>+x \<in> (\<Union>n. B n). f x \<partial>M) = (\<Sum>n. (\<integral>\<^sup>+x \<in> B n. f x \<partial>M))"
proof -
  have [measurable]: "\<And>n. (\<lambda>x. f x * indicator (B n) x) \<in> borel_measurable M" by simp
  moreover have "\<And>n. AE x in M. f x * indicator (B n) x \<ge> 0" using assms(4) by auto
  ultimately have "(\<integral>\<^sup>+ x. (\<Sum>n. f x * indicator (B n) x) \<partial>M) = (\<Sum>n. (\<integral>\<^sup>+ x. f x * indicator (B n) x \<partial>M))"
    by (rule nn_integral_suminf)
  moreover have "\<And>x. (\<Sum>n. f x * indicator (B n) x) = f x * indicator (\<Union>n. B n) x"
  proof -
    fix x
    show "(\<Sum>n. f x * indicator (B n) x) = f x * indicator (\<Union>n. B n) x"
    proof (cases)
      assume "x \<in> (\<Union>n. B n)"
      then obtain n where "x \<in> B n" by blast
      have a: "finite {n}" by simp
      have "\<And>i. i \<noteq> n \<Longrightarrow> x \<notin> B i" using `x \<in> B n` assms(3) disjoint_family_on_def
        by (metis IntI UNIV_I empty_iff)
      hence "\<And>i. i \<notin> {n} \<Longrightarrow> indicator (B i) x = (0::ereal)" using indicator_def by simp
      hence b: "\<And>i. i \<notin> {n} \<Longrightarrow> f x * indicator (B i) x = (0::ereal)" by simp

      def h \<equiv> "\<lambda>i. f x * indicator (B i) x"
      hence "\<And>i. i \<notin> {n} \<Longrightarrow> h i = 0" using b by simp
      hence "(\<Sum>i. h i) = (\<Sum>i\<in>{n}. h i)"
        by (metis sums_unique[OF sums_finite[OF a]])
      hence "(\<Sum>i. h i) = h n" by simp
      hence "(\<Sum>n. f x * indicator (B n) x) = f x * indicator (B n) x" using h_def by simp
      hence "(\<Sum>n. f x * indicator (B n) x) = f x" using `x \<in> B n` indicator_def by simp
      thus ?thesis using `x \<in> (\<Union>n. B n)` by auto
    next
      assume "x \<notin> (\<Union>n. B n)"
      hence "\<And>n. f x * indicator (B n) x = 0" by simp
      have "(\<Sum>n. f x * indicator (B n) x) = 0"
        by (simp add: `\<And>n. f x * indicator (B n) x = 0`)
      thus ?thesis using `x \<notin> (\<Union>n. B n)` by auto
    qed
  qed
  ultimately show ?thesis by simp
qed

lemma nn_set_integral_add:
  assumes "AE x in M. f x \<ge> 0" "AE x in M. g x \<ge> 0" and
          [measurable]: "f \<in> borel_measurable M" "g \<in> borel_measurable M"
          "A \<in> sets M"
  shows "(\<integral>\<^sup>+x \<in> A. (f x + g x) \<partial>M) = (\<integral>\<^sup>+x \<in> A. f x \<partial>M) + (\<integral>\<^sup>+x \<in> A. g x \<partial>M)"
proof -
  have "(\<integral>\<^sup>+x \<in> A. (f x + g x) \<partial>M) = (\<integral>\<^sup>+x. (f x * indicator A x + g x * indicator A x) \<partial>M)"
    by (simp add: indicator_def nn_integral_cong_pos)
  also have "... = (\<integral>\<^sup>+x. f x * indicator A x \<partial>M) + (\<integral>\<^sup>+x. g x * indicator A x \<partial>M)"
  proof (rule nn_integral_add)
    show "AE x in M. 0 \<le> f x * indicator A x" using assms(1) by auto
    show "AE x in M. 0 \<le> g x * indicator A x" using assms(2) by auto
  qed (auto simp add: assms)
  finally show ?thesis by simp
qed

lemma nn_set_integral_cong:
  assumes "AE x in M. f x = g x"
  shows "(\<integral>\<^sup>+x \<in> A. f x \<partial>M) = (\<integral>\<^sup>+x \<in> A. g x \<partial>M)"
proof -
  have "AE x in M. f x * indicator A x = g x * indicator A x" using assms(1) by auto
  then show ?thesis by (rule nn_integral_cong_AE)
qed

lemma nn_set_integral_set_mono:
  assumes "A \<subseteq> B"
  shows "(\<integral>\<^sup>+ x \<in> A. f x \<partial>M) \<le> (\<integral>\<^sup>+ x \<in> B. f x \<partial>M)"
proof -
  def g \<equiv> "\<lambda>x. max (f x) 0"
  have g_pos: "\<And>x. g x \<ge> 0" unfolding g_def by simp
  have "(\<integral>\<^sup>+ x \<in> A. f x \<partial>M) = (\<integral>\<^sup>+ x \<in> A. g x \<partial>M)"
    unfolding g_def by (simp add: indicator_def max_def nn_integral_cong_pos)
  also have "... \<le>  (\<integral>\<^sup>+ x \<in> B. g x \<partial>M)"
    apply (rule nn_integral_mono_AE[where ?u = "\<lambda>x. g x * indicator A x" and ?v = "\<lambda>x. g x * indicator B x"] )
    using assms by (simp add: g_pos ereal_mult_left_mono subset_eq)
  also have "... =  (\<integral>\<^sup>+ x \<in> B. f x \<partial>M)"
    unfolding g_def by (simp add: indicator_def max_def nn_integral_cong_pos)
  finally show ?thesis by simp
qed

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
  hence "(\<integral>\<^sup>+x \<in> A. f (g x) \<partial>count_space UNIV) = (\<integral>\<^sup>+y \<in> g`A. f y \<partial>count_space UNIV)"
    by (rule nn_integral_count_compose_inj)
  thus ?thesis using assms by (simp add: bij_betw_def)
qed

lemma set_integral_null_delta:
  fixes f::"_ \<Rightarrow> _ :: {banach, second_countable_topology}"
  assumes [measurable]: "integrable M f" "A \<in> sets M" "B \<in> sets M"
    and "A \<Delta> B \<in> null_sets M"
  shows "(\<integral>x \<in> A. f x \<partial>M) = (\<integral>x \<in> B. f x \<partial>M)"
proof (rule set_integral_cong_set, auto)
  have *: "AE a in M. a \<notin> A \<Delta> B"
    using assms(4) null_setsD_AE by blast
  thus "AE x in M. (x \<in> B) = (x \<in> A)"
    by auto
qed

lemma set_integral_space:
  assumes "integrable M f"
  shows "(\<integral> x \<in> space M. f x \<partial>M) = (\<integral> x. f x \<partial>M)"
by (metis (mono_tags, lifting) indicator_simps(1) integral_cong real_vector.scale_one)

lemma null_if_pos_func_has_zero_nn_int:
  fixes f::"'a \<Rightarrow> ereal"
  assumes [measurable]: "f \<in> borel_measurable M" "A \<in> sets M"
   and "AE x\<in>A in M. f x > 0" "(\<integral>\<^sup>+x\<in>A. f x \<partial>M) = 0"
  shows "A \<in> null_sets M"
proof -
  have "AE x in M. f x * indicator A x \<le> 0"
    by (subst nn_integral_0_iff_AE[symmetric], auto simp add: assms(4))
  then have "AE x\<in>A in M. f x \<le> 0" by auto
  then have "AE x\<in>A in M. False" using assms(3) by auto
  then show "A \<in> null_sets M" using assms(2) by (simp add: AE_iff_null_sets)
qed


subsection {*Radon-Nikodym.thy*}

text{*The next lemma is a variant of \verb+density_unique+. Note that it uses the notation
for nonnegative set integrals introduced earlier.*}

lemma (in sigma_finite_measure) density_unique2:
  assumes f: "f \<in> borel_measurable M" "AE x in M. 0 \<le> f x"
  assumes f': "f' \<in> borel_measurable M" "AE x in M. 0 \<le> f' x"
  assumes density_eq:  "\<And>A. A \<in> sets M \<Longrightarrow> (\<integral>\<^sup>+ x \<in> A. f x \<partial>M) = (\<integral>\<^sup>+ x \<in> A. f' x \<partial>M)"
  shows "AE x in M. f x = f' x"
proof (rule density_unique)
  show "density M f = density M f'"
    by (metis (no_types, lifting) density_eq emeasure_density f'(1) f(1) measure_eqI nn_integral_cong_pos sets_density)
qed (auto simp add: assms)

subsection {*Bochner-Integration.thy*}

lemma not_AE_zero_int_E:
  fixes f::"'a \<Rightarrow> real"
  assumes "AE x in M. f x \<ge> 0"
          "(\<integral>x. f x \<partial>M) > 0"
    and [measurable]: "f \<in> borel_measurable M"
 shows "\<exists>A e. A \<in> sets M \<and> e>0 \<and> emeasure M A > 0 \<and> (\<forall>x \<in> A. f x \<ge> e)"
proof (rule not_AE_zero_E, auto simp add: assms)
  assume *: "AE x in M. f x = 0"
  have "(\<integral>x. f x \<partial>M) = (\<integral>x. 0 \<partial>M)" by (rule integral_cong_AE, auto simp add: *)
  then have "(\<integral>x. f x \<partial>M) = 0" by simp
  then show False using assms(2) by simp
qed

lemma null_if_pos_func_has_zero_int:
  assumes [measurable]: "integrable M f" "A \<in> sets M"
   and "AE x\<in>A in M. f x > 0" "(\<integral>x\<in>A. f x \<partial>M) = (0::real)"
  shows "A \<in> null_sets M"
proof -
  have "AE x in M. indicator A x * f x = 0"
    apply (subst integral_nonneg_eq_0_iff_AE[symmetric])
    using assms integrable_mult_indicator[OF `A \<in> sets M` assms(1)] by auto
  then have "AE x\<in>A in M. f x = 0" by auto
  then have "AE x\<in>A in M. False" using assms(3) by auto
  then show "A \<in> null_sets M" using assms(2) by (simp add: AE_iff_null_sets)
qed

lemma (in finite_measure) integral_bounded_eq_bound_then_AE:
  assumes "AE x in M. f x \<le> (c::real)"
    "integrable M f" "(\<integral>x. f x \<partial>M) = c * measure M (space M)"
  shows "AE x in M. f x = c"
proof -
  def g \<equiv> "\<lambda>x. c - f x"
  have "AE x in M. g x = 0"
    apply (subst integral_nonneg_eq_0_iff_AE[symmetric])
    unfolding g_def using assms by auto
  then show ?thesis unfolding g_def by auto
qed


text {* The next lemma implies the same statement for Banach-space valued functions
using Hahn-Banach theorem and linear forms. Since they are not yet easily available, I
only formulate it for real-valued functions.*}

lemma density_unique_real:
  fixes f f'::"_ \<Rightarrow> real"
  assumes [measurable]: "integrable M f" "integrable M f'"
  assumes density_eq: "\<And>A. A \<in> sets M \<Longrightarrow> (\<integral>x \<in> A. f x \<partial>M) = (\<integral>x \<in> A. f' x \<partial>M)"
  shows "AE x in M. f x = f' x"
proof -
  def A \<equiv> "{x \<in> space M. f x < f' x}"
  then have [measurable]: "A \<in> sets M" by simp
  have "(\<integral>x \<in> A. (f' x - f x) \<partial>M) = (\<integral>x \<in> A. f' x \<partial>M) - (\<integral>x \<in> A. f x \<partial>M)"
    using `A \<in> sets M` assms(1) assms(2) integrable_mult_indicator by blast
  then have "(\<integral>x \<in> A. (f' x - f x) \<partial>M) = 0" using assms(3) by simp
  then have "A \<in> null_sets M"
    using A_def null_if_pos_func_has_zero_int[where ?f = "\<lambda>x. f' x - f x" and ?A = A] assms by auto
  then have "AE x in M. x \<notin> A" by (simp add: null_setsD_AE)
  then have *: "AE x in M. f' x \<le> f x" unfolding A_def by auto


  def B \<equiv> "{x \<in> space M. f' x < f x}"
  then have [measurable]: "B \<in> sets M" by simp
  have "(\<integral>x \<in> B. (f x - f' x) \<partial>M) = (\<integral>x \<in> B. f x \<partial>M) - (\<integral>x \<in> B. f' x \<partial>M)"
    using `B \<in> sets M` assms(1) assms(2) integrable_mult_indicator by blast
  then have "(\<integral>x \<in> B. (f x - f' x) \<partial>M) = 0" using assms(3) by simp
  then have "B \<in> null_sets M"
    using B_def null_if_pos_func_has_zero_int[where ?f = "\<lambda>x. f x - f' x" and ?A = B] assms by auto
  then have "AE x in M. x \<notin> B" by (simp add: null_setsD_AE)
  then have "AE x in M. f' x \<ge> f x" unfolding B_def by auto

  then show ?thesis using * by auto
qed

lemma integrable_Max:
  fixes f::"_ \<Rightarrow> 'a \<Rightarrow> real"
  assumes [measurable]: "\<And>i. integrable M (f i)"
      and "finite I" "I\<noteq>{}"
   shows "integrable M (\<lambda>x. Max {f i x|i. i\<in>I})"
proof (rule integrable_bound[where ?f = "\<lambda>x. (\<Sum>i\<in>I. abs(f i x))"])
  show "integrable M (\<lambda>x. \<Sum>i\<in>I. \<bar>f i x\<bar>)" by (rule integrable_setsum, auto simp add: assms)
  {
    fix x
    have "\<bar>Max {f i x |i. i \<in> I}\<bar> \<le> (\<Sum>i\<in>I. \<bar>f i x\<bar>)"
      by (metis simple_image abs_Max_sum2[OF assms(2) assms(3), of "\<lambda>i. f i x"])
  }
  then show "AE x in M. norm (Max {f i x |i. i \<in> I}) \<le> norm (\<Sum>i\<in>I. \<bar>f i x\<bar>)" by auto
qed (simp add: assms)

lemma tendsto_L1_int:
  fixes u :: "_ \<Rightarrow> _ \<Rightarrow> 'b::{banach, second_countable_topology}"
  assumes [measurable]: "\<And>n. integrable M (u n)" "integrable M f"
          and "((\<lambda>n. (\<integral>\<^sup>+x. norm(u n x - f x) \<partial>M)) \<longlongrightarrow> 0) F"
  shows "((\<lambda>n. (\<integral>x. u n x \<partial>M)) \<longlongrightarrow> (\<integral>x. f x \<partial>M)) F"
proof -
  have "((\<lambda>n. norm((\<integral>x. u n x \<partial>M) - (\<integral>x. f x \<partial>M))) \<longlongrightarrow> (0::ereal)) F"
  proof (rule tendsto_sandwich[of "\<lambda>_. 0", where ?h = "\<lambda>n. (\<integral>\<^sup>+x. norm(u n x - f x) \<partial>M)"], auto simp add: assms)
    {
      fix n
      have "(\<integral>x. u n x \<partial>M) - (\<integral>x. f x \<partial>M) = (\<integral>x. u n x - f x \<partial>M)"
        apply (rule integral_diff[symmetric]) using assms by auto
      then have "norm((\<integral>x. u n x \<partial>M) - (\<integral>x. f x \<partial>M)) = norm (\<integral>x. u n x - f x \<partial>M)"
        by auto
      also have "... \<le> (\<integral>x. norm(u n x - f x) \<partial>M)"
        apply (rule integral_norm_bound) using assms by auto
      finally have "ereal(norm((\<integral>x. u n x \<partial>M) - (\<integral>x. f x \<partial>M))) \<le> (\<integral>x. norm(u n x - f x) \<partial>M)"
        by simp
      also have "... = (\<integral>\<^sup>+x. norm(u n x - f x) \<partial>M)"
        apply (rule nn_integral_eq_integral[symmetric]) using assms by auto
      finally have "norm((\<integral>x. u n x \<partial>M) - (\<integral>x. f x \<partial>M)) \<le>  (\<integral>\<^sup>+x. norm(u n x - f x) \<partial>M)" by simp
    }
    then show "eventually (\<lambda>n. norm((\<integral>x. u n x \<partial>M) - (\<integral>x. f x \<partial>M)) \<le>  (\<integral>\<^sup>+x. norm(u n x - f x) \<partial>M)) F"
      by auto
  qed
  then have "((\<lambda>n. norm((\<integral>x. u n x \<partial>M) - (\<integral>x. f x \<partial>M))) \<longlongrightarrow> 0) F" by (simp add: zero_ereal_def)
  then have "((\<lambda>n. ((\<integral>x. u n x \<partial>M) - (\<integral>x. f x \<partial>M))) \<longlongrightarrow> 0) F" using tendsto_norm_zero_iff by blast
  then show ?thesis using Lim_null by auto
qed

lemma tendsto_L1_AE_subseq:
  fixes u :: "nat \<Rightarrow> 'a \<Rightarrow> 'b::{banach, second_countable_topology}"
  assumes [measurable]: "\<And>n. integrable M (u n)"
     and "(\<lambda>n. (\<integral>x. norm(u n x) \<partial>M)) \<longlonglongrightarrow> 0"
  shows "\<exists>r. subseq r \<and> (AE x in M. (\<lambda>n. u (r n) x) \<longlonglongrightarrow> 0)"
proof -
  {
    fix k
    have "eventually (\<lambda>n. (\<integral>x. norm(u n x) \<partial>M) < (1/2)^k) sequentially"
      using order_tendstoD(2)[OF assms(2)] by auto
    with eventually_elim2[OF eventually_gt_at_top[of k] this]
    have "\<exists>n>k. (\<integral>x. norm(u n x) \<partial>M) < (1/2)^k"
      by (metis eventually_False_sequentially)
  }
  then have "\<exists>r. \<forall>n. True \<and> (r (Suc n) > r n \<and> (\<integral>x. norm(u (r (Suc n)) x) \<partial>M) < (1/2)^(r n))"
    by (intro dependent_nat_choice, auto)
  then obtain r0 where r0: "subseq r0" "\<And>n. (\<integral>x. norm(u (r0 (Suc n)) x) \<partial>M) < (1/2)^(r0 n)"
    by (auto simp: subseq_Suc_iff)
  def r \<equiv> "\<lambda>n. r0(n+1)"
  have "subseq r" unfolding r_def using r0(1) by (simp add: subseq_Suc_iff)
  have I: "(\<integral>\<^sup>+x. norm(u (r n) x) \<partial>M) < ereal((1/2)^n)" for n
  proof -
    have "r0 n \<ge> n" using `subseq r0` by (simp add: seq_suble)
    have "(1/2::real)^(r0 n) \<le> (1/2)^n" by (rule power_decreasing[OF `r0 n \<ge> n`], auto)
    then have "(\<integral>x. norm(u (r0 (Suc n)) x) \<partial>M) < (1/2)^n" using r0(2) less_le_trans by auto
    then have "(\<integral>x. norm(u (r n) x) \<partial>M) < (1/2)^n" unfolding r_def by auto
    moreover have "(\<integral>\<^sup>+x. norm(u (r n) x) \<partial>M) = (\<integral>x. norm(u (r n) x) \<partial>M)"
      by (rule nn_integral_eq_integral, auto simp add: integrable_norm[OF assms(1)[of "r n"]])
    ultimately show ?thesis by auto
  qed

  {
    fix e::real assume "e > 0"
    def A \<equiv> "\<lambda>n. {x \<in> space M. norm(u (r n) x) \<ge> e}"
    have A_meas [measurable]: "\<And>n. A n \<in> sets M" unfolding A_def by auto
    have A_bound: "emeasure M (A n) < (1/e) * ereal((1/2)^n)" for n
    proof -
      have *: "indicator (A n) x \<le> (1/e) * ereal(norm(u (r n) x))" for x
        apply (cases "x \<in> A n") unfolding A_def using \<open>0 < e\<close> by auto
      have "emeasure M (A n) = (\<integral>\<^sup>+x. indicator (A n) x \<partial>M)" by auto
      also have "... \<le> (\<integral>\<^sup>+x. (1/e) * ereal(norm(u (r n) x)) \<partial>M)"
        apply (rule nn_integral_mono) using * by auto
      also have "... = (1/e) * (\<integral>\<^sup>+x. norm(u (r n) x) \<partial>M)"
        apply (rule nn_integral_cmult) using `e > 0` by auto
      also have "... < (1/e) * ereal((1/2)^n)"
        apply (rule ereal_mult_strict_left_mono) using I[of n] `e > 0` by auto
      finally show ?thesis by simp
    qed
    then have A_fin: "emeasure M (A n) < \<infinity>" for n using `e>0` by (metis ereal_infty_less(1) less_ereal.simps(2))

    have A_sum: "summable (\<lambda>n. measure M (A n))"
    proof (rule summable_comparison_test'[of "\<lambda>n. (1/e) * (1/2)^n" 0])
      have "summable (\<lambda>n. (1/(2::real))^n)"  by (simp add: summable_geometric)
      then show "summable (\<lambda>n. (1/e) * (1/2)^n)" using summable_mult by blast
      fix n::nat assume "n \<ge> 0"
      have "norm(measure M (A n)) = measure M (A n)" by (simp add: measure_nonneg)
      also have "... = real_of_ereal(emeasure M (A n))" unfolding measure_def by simp
      also have "... < real_of_ereal( (1/e) * ereal((1/2)^n))" using A_bound[of n]
        by (metis \<open>\<And>n. emeasure M (A n) < \<infinity>\<close> emeasure_eq_ereal_measure ereal_infty_less(1)
        less_ereal.simps(1) real_of_ereal.simps(1) times_ereal.simps(1))
      also have "... = (1/e) * (1/2)^n" by auto
      finally show "norm(measure M (A n)) \<le> (1/e) * (1/2)^n" by simp
    qed

    have "AE x in M. eventually (\<lambda>n. x \<in> space M - A n) sequentially"
      by (rule borel_cantelli_AE1[OF A_meas A_fin A_sum])
    moreover
    {
      fix x assume "eventually (\<lambda>n. x \<in> space M - A n) sequentially"
      moreover have "norm(u (r n) x) \<le> ereal e" if "x \<in> space M - A n" for n
        using that unfolding A_def by auto
      ultimately have "eventually (\<lambda>n. norm(u (r n) x) \<le> ereal e) sequentially"
        by (simp add: eventually_mono)
      then have "limsup (\<lambda>n. norm(u (r n) x)) \<le> e"
        by (simp add: Limsup_bounded)
    }
    ultimately have "AE x in M. limsup (\<lambda>n. norm(u (r n) x)) \<le> 0 + ereal e" by auto
  }
  with AE_upper_bound_inf_ereal2[OF this] have "AE x in M. limsup (\<lambda>n. norm(u (r n) x)) \<le> 0" by auto
  moreover
  {
    fix x assume "limsup (\<lambda>n. norm(u (r n) x)) \<le> 0"
    moreover have "liminf (\<lambda>n. norm(u (r n) x)) \<ge> 0" by (rule Liminf_bounded, auto)
    ultimately have "(\<lambda>n. norm(u (r n) x)) \<longlonglongrightarrow> (0::ereal)" by (simp add: limsup_le_liminf_real zero_ereal_def)
    then have "(\<lambda>n. norm(u (r n) x)) \<longlonglongrightarrow> 0" by (simp add: zero_ereal_def)
    then have "(\<lambda>n. u (r n) x) \<longlonglongrightarrow> 0" by (simp add: tendsto_norm_zero_iff)
  }
  ultimately have "AE x in M. (\<lambda>n. u (r n) x) \<longlonglongrightarrow> 0" by auto
  then show ?thesis using `subseq r` by auto
qed

text {* The next lemma shows that $L^1$ convergence of a sequence of functions follows from almost
everywhere convergence and the weaker condition of the convergence of the integrated norms (or even
just the nontrivial inequality about them). Useful in a lot of contexts! This statement (or its
variations) are known as Scheffe lemma.

Informal quick textbook proof:
Let $G_n(x) = \norm{f x} + \norm{F_n x} - \norm{(f-F_n)(x)}$. Then $\int \liminf G_n \leq
\liminf \int G_n$ by Fatou, i.e., $2 \int \norm{f} \leq 2 \int \norm{f} + \liminf (- \int \norm{f-F_n})$,
hence $\limsup \int \norm{f-F_n} \leq 0$. QED

The formalization is more painful as one should jump back and forth between reals and ereals and justify
all the time positivity or integrability (thankfully, measurability is handled more or less automatically).*}

lemma Scheffe_lemma1:
   assumes "\<And> n. integrable M (F n)" "integrable M f"
           "AE x in M. (\<lambda>n. F n x) \<longlonglongrightarrow> f x"
           "limsup (\<lambda>n. \<integral>\<^sup>+ x. norm(F n x) \<partial>M) \<le> (\<integral>\<^sup>+ x. norm(f x) \<partial>M)"
    shows "(\<lambda>n. \<integral>\<^sup>+ x. norm(F n x - f x) \<partial>M) \<longlonglongrightarrow> 0"
proof -
  have [measurable]: "\<And>n. (\<lambda>x. norm(F n x)) \<in> borel_measurable M"
                     "(\<lambda>x. norm(f x)) \<in> borel_measurable M"
                     "\<And>n. (\<lambda>x. norm(F n x - f x)) \<in> borel_measurable M"
    using assms(1) assms(2) by simp_all
  def G \<equiv> "\<lambda>n x. norm(f x) + norm(F n x) - norm(F n x - f x)"
  have [measurable]: "\<And>n. G n \<in> borel_measurable M" unfolding G_def by simp
  have G_pos: "\<And>n x. G n x \<ge> 0" unfolding G_def by (metis ge_iff_diff_ge_0 norm_minus_commute norm_triangle_ineq4)
  have finint: "(\<integral>\<^sup>+ x. norm(f x) \<partial>M) \<noteq> \<infinity>"
    using assms(2) ereal_infty_less(1) has_bochner_integral_implies_finite_norm has_bochner_integral_integrable by blast
  then have fin2: "abs(2 * (\<integral>\<^sup>+ x. norm(f x) \<partial>M)) \<noteq> \<infinity>" by auto

  {
    fix x assume *: "(\<lambda>n. F n x) \<longlonglongrightarrow> f x"
    then have "(\<lambda>n. norm(F n x)) \<longlonglongrightarrow> norm(f x)" using tendsto_norm by blast
    moreover have "(\<lambda>n. norm(F n x - f x)) \<longlonglongrightarrow> 0"  using * Lim_null tendsto_norm_zero_iff by fastforce
    ultimately have a: "(\<lambda>n. norm(F n x) - norm(F n x - f x)) \<longlonglongrightarrow> norm(f x)" using tendsto_diff by fastforce
    have "(\<lambda>n. norm(f x) + (norm(F n x) - norm(F n x - f x))) \<longlonglongrightarrow> norm(f x) + norm(f x)"
      by (rule tendsto_add) (auto simp add: a)
    moreover have "\<And>n. G n x =  norm(f x) + (norm(F n x) - norm(F n x - f x))" unfolding G_def by simp
    ultimately have "(\<lambda>n. G n x) \<longlonglongrightarrow>  2 * norm(f x)" by simp
    then have "(\<lambda>n. ereal(G n x)) \<longlonglongrightarrow> 2 * ereal(norm(f x))" by simp
    then have "liminf (\<lambda>n. ereal(G n x)) = 2 * ereal(norm(f x))"
      using sequentially_bot tendsto_iff_Liminf_eq_Limsup by blast
  }
  then have "AE x in M. liminf (\<lambda>n. ereal(G n x)) = 2 * ereal(norm(f x))"  using assms(3) by auto
  then have "(\<integral>\<^sup>+ x. liminf (\<lambda>n. G n x) \<partial>M) = (\<integral>\<^sup>+ x. 2 * ereal(norm(f x)) \<partial>M)" by (simp add: nn_integral_cong_AE)
  also have "... = 2 * (\<integral>\<^sup>+ x. norm(f x) \<partial>M)" by (rule nn_integral_cmult, auto)
  finally have int_liminf: "(\<integral>\<^sup>+ x. liminf (\<lambda>n. G n x) \<partial>M) = 2 * (\<integral>\<^sup>+ x. norm(f x) \<partial>M)" by simp

  {
    fix n
    have "(\<integral>\<^sup>+x. ereal(norm(f x)) + ereal(norm(F n x)) \<partial>M) =  (\<integral>\<^sup>+x. norm(f x) \<partial>M) +  (\<integral>\<^sup>+x. norm(F n x) \<partial>M)"
      by (rule nn_integral_add) (auto simp add: assms)
  }
  then have "limsup (\<lambda>n. (\<integral>\<^sup>+x. ereal(norm(f x)) + ereal(norm(F n x)) \<partial>M)) = limsup (\<lambda>n.  (\<integral>\<^sup>+x. norm(f x) \<partial>M) +  (\<integral>\<^sup>+x. norm(F n x) \<partial>M))"
    by simp
  also have "... = (\<integral>\<^sup>+x. norm(f x) \<partial>M) + limsup (\<lambda>n. (\<integral>\<^sup>+x. norm(F n x) \<partial>M))"
    by (rule ereal_limsup_lim_add, auto simp add: finint)
  also have "... \<le> (\<integral>\<^sup>+x. norm(f x) \<partial>M) +  (\<integral>\<^sup>+x. norm(f x) \<partial>M)"
    using assms(4) by (simp add: add_left_mono)
  also have "... = 2 * (\<integral>\<^sup>+x. norm(f x) \<partial>M)"
    by (metis ereal_left_distrib lambda_one one_add_one zero_less_one_ereal)
  ultimately have a: "limsup (\<lambda>n. (\<integral>\<^sup>+x. ereal(norm(f x)) + ereal(norm(F n x)) \<partial>M)) \<le> 2 * (\<integral>\<^sup>+x. norm(f x) \<partial>M)" by simp

  {
    fix n
    have "\<And>x. ereal(G n x) = ereal(norm(f x)) + ereal(norm(F n x)) - ereal(norm(F n x - f x))"
      unfolding G_def by simp
    moreover have "(\<integral>\<^sup>+x. ereal(norm(f x)) + ereal(norm(F n x)) - ereal(norm(F n x - f x)) \<partial>M)
           = (\<integral>\<^sup>+x. ereal(norm(f x)) + ereal(norm(F n x)) \<partial>M) - (\<integral>\<^sup>+x.  norm(F n x - f x) \<partial>M)"
    proof (rule nn_integral_diff)
      have "\<And>x. ereal (norm (F n x - f x)) \<le> ereal (norm (f x)) + ereal (norm (F n x))"
         by (simp add: norm_minus_commute norm_triangle_ineq4)
      then show "AE x in M. ereal (norm (F n x - f x)) \<le> ereal (norm (f x)) + ereal (norm (F n x))"
        by simp
      then have "(\<integral>\<^sup>+x. ereal (norm (F n x - f x)) \<partial>M) \<le>  (\<integral>\<^sup>+x. ereal(norm(f x)) + ereal(norm(F n x)) \<partial>M)"
        by (simp add: nn_integral_mono_AE)
      then have "(\<integral>\<^sup>+x. ereal (norm (F n x - f x)) \<partial>M) < \<infinity>" using assms(1) assms(2)
        by (metis has_bochner_integral_implies_finite_norm integrable.simps integrable_diff)
      then show "(\<integral>\<^sup>+x. ereal (norm (F n x - f x)) \<partial>M) \<noteq> \<infinity>" by simp
    qed (auto simp add: assms)
    ultimately have "(\<integral>\<^sup>+x. G n x \<partial>M) = - (\<integral>\<^sup>+x. norm(F n x - f x) \<partial>M) + (\<integral>\<^sup>+x. ereal(norm(f x)) + ereal(norm(F n x)) \<partial>M)"
      using add.commute minus_ereal_def by auto
  }
  then have "liminf (\<lambda>n. (\<integral>\<^sup>+x. G n x \<partial>M)) = liminf (\<lambda>n. - (\<integral>\<^sup>+x. norm(F n x - f x) \<partial>M) + (\<integral>\<^sup>+x. ereal(norm(f x)) + ereal(norm(F n x)) \<partial>M))"
    by simp
  also have "... \<le> liminf (\<lambda>n. - (\<integral>\<^sup>+x. norm(F n x - f x) \<partial>M)) + limsup (\<lambda>n. (\<integral>\<^sup>+x. ereal(norm(f x)) + ereal(norm(F n x)) \<partial>M))"
    by (rule ereal_liminf_limsup_add)
  also have "... \<le> liminf (\<lambda>n. - (\<integral>\<^sup>+x. norm(F n x - f x) \<partial>M)) +  2 * (\<integral>\<^sup>+x. norm(f x) \<partial>M)"
    using a by (simp add: add_left_mono)
  also have "... = - limsup (\<lambda>n. (\<integral>\<^sup>+x.  norm(F n x - f x) \<partial>M)) + 2 * (\<integral>\<^sup>+x. norm(f x) \<partial>M) "
    by (simp add: ereal_Liminf_uminus minus_ereal_def)
  finally have liminf_int: "liminf (\<lambda>n. (\<integral>\<^sup>+x. G n x \<partial>M)) \<le> - limsup (\<lambda>n. (\<integral>\<^sup>+x. norm(F n x - f x) \<partial>M)) + 2 * (\<integral>\<^sup>+x. norm(f x) \<partial>M) "
    using add.commute by simp

  have "(\<integral>\<^sup>+ x. liminf (\<lambda>n. G n x) \<partial>M) \<le> liminf (\<lambda>n. (\<integral>\<^sup>+x. G n x \<partial>M))"
    by (rule nn_integral_liminf) (auto simp add: G_pos)
  then have "2 * (\<integral>\<^sup>+x. norm(f x) \<partial>M) \<le>  - limsup (\<lambda>n. (\<integral>\<^sup>+x. norm(F n x - f x) \<partial>M)) + 2 * (\<integral>\<^sup>+x. norm(f x) \<partial>M)"
    using int_liminf liminf_int by simp
  then have "2 * (\<integral>\<^sup>+x. norm(f x) \<partial>M) - 2 * (\<integral>\<^sup>+x. norm(f x) \<partial>M) \<le>  - limsup (\<lambda>n. (\<integral>\<^sup>+x. norm(F n x - f x) \<partial>M))"
    using fin2 ereal_minus_le by presburger
  then have i: "limsup (\<lambda>n. (\<integral>\<^sup>+x. norm(F n x - f x) \<partial>M)) \<le> 0"
    using fin2 by auto

  have r: "\<And>a b. a \<le> b \<Longrightarrow> b \<le> (0::ereal) \<Longrightarrow> 0 \<le> a \<Longrightarrow> a = 0 \<and> b = 0" by auto
  have "liminf (\<lambda>n. (\<integral>\<^sup>+x. norm(F n x - f x) \<partial>M)) = 0 \<and> limsup (\<lambda>n. (\<integral>\<^sup>+x. norm(F n x - f x) \<partial>M)) = 0"
  proof (rule r)
    have *: "\<forall>n. (\<integral>\<^sup>+x. norm(F n x - f x) \<partial>M) \<ge> 0" using nn_integral_nonneg by auto
    have "liminf (\<lambda>n. (\<integral>\<^sup>+x. norm(F n x - f x) \<partial>M)) \<ge> liminf (\<lambda>n. 0)"
      using always_eventually[OF *] Liminf_mono by force
    then show "liminf (\<lambda>n. (\<integral>\<^sup>+x. norm(F n x - f x) \<partial>M)) \<ge> 0"
      by (metis (mono_tags) sequentially_bot tendsto_const tendsto_iff_Liminf_eq_Limsup)
  qed (auto simp add: Liminf_le_Limsup i)
  then show ?thesis using tendsto_iff_Liminf_eq_Limsup trivial_limit_sequentially by blast
qed

lemma Scheffe_lemma2:
  fixes F::"nat \<Rightarrow> 'a \<Rightarrow> 'b::{banach, second_countable_topology}"
   assumes "\<And> n::nat. F n \<in> borel_measurable M" "integrable M f"
           "AE x in M. (\<lambda>n. F n x) \<longlonglongrightarrow> f x"
           "\<And>n. (\<integral>\<^sup>+ x. norm(F n x) \<partial>M) \<le> (\<integral>\<^sup>+ x. norm(f x) \<partial>M)"
    shows "(\<lambda>n. \<integral>\<^sup>+ x. norm(F n x - f x) \<partial>M) \<longlonglongrightarrow> 0"
proof (rule Scheffe_lemma1)
  fix n::nat
  have " (\<integral>\<^sup>+ x. norm(f x) \<partial>M) < \<infinity>" using assms(2) by (metis has_bochner_integral_implies_finite_norm integrable.cases)
  then have " (\<integral>\<^sup>+ x. norm(F n x) \<partial>M) < \<infinity>" using assms(4)[of n] by auto
  then show "integrable M (F n)" by (subst integrable_iff_bounded, simp add: assms(1)[of n])
qed (auto simp add: assms Limsup_bounded)

end
