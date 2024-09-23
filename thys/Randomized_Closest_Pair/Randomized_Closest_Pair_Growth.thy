section \<open>Growth of Close Points\<close>

text \<open>This section verifies a result similar to (but more general than)
Lemma~2 by Rabin~\cite{rabin1976}. Let $N(d)$ denote the number of pairs from the point sequence
$p_1,\ldots,p_n$, with distance less than $d$:

\[
  N(d) := | \{ (i,j) | d(p_i, p_j) < d \wedge 1 \leq i,j \leq n \} |
\]

Obviously, $N(d)$ is monotone. It is possible to show that the growth of
$N(d)$ is bounded.

In particular:
\[
  N(ad) \leq (2a \sqrt{2}+3)^2 N(d)
\]
for all $a > 0$, $d > 0$. As far as we can tell the proof below is new.

\emph{Proof:} Consider a 2D-grid with size $\alpha := \frac{d}{\sqrt{2}}$ and let us denote by $G(x,y)$
the number of points that fall in the cell $(x,y) \in \mathbb Z \times \mathbb Z$, i.e.:

\[
G(x,y) := \left| \left\{ i \middle | \left\lfloor \frac{p_{i,1}}{\alpha} \right\rfloor = x \wedge
  \left\lfloor \frac{p_{i,2}}{\alpha} \right\rfloor = x \right\} \right| \textrm{,}
\]
where $p_{i,1}$ (resp. $p_{i,2}$) denote the first (resp. second) component of point p.

Let also $s := \lceil a \sqrt{2} \rceil$.

Then we can observe that
\begin{eqnarray*}
N(ad) & \leq & \sum_{(x,y)\in\mathbb Z\times\mathbb Z} \sum_{i=-s}^{s} \sum_{j=-s}^{s} G(x,y) G(x+i,y+j) \\
& = & \sum_{i=-s}^{s} \sum_{j=-s}^{s} \sum_{(x,y)\in\mathbb Z\times\mathbb Z} G(x,y) G(x+i,y+j)\\
& \leq & \sum_{i=-s}^{s} \sum_{j=-s}^{s} \left(\left(\sum_{(x,y)\in\mathbb Z\times\mathbb Z} G(x,y)^2 \right) \left(\sum_{(x,y)\in\mathbb Z\times\mathbb Z} G(x+i,y+j)^2\right) \right)^{1/2}\\
& \leq & \sum_{i=-s}^{s} \sum_{j=-s}^{s} \left(\left(\sum_{(x,y)\in\mathbb Z\times\mathbb Z} G(x,y)^2 \right) \left(\sum_{(x,y)\in\mathbb Z\times\mathbb Z} G(x,y)^2\right) \right)^{1/2}\\
& \leq & (2s+1)^2 \sum_{(x,y)\in\mathbb Z\times\mathbb Z} G(x,y)^2 \\
& \leq & (2a \sqrt(2)+3)^2 \sum_{(x,y)\in\mathbb Z\times\mathbb Z} G(x,y)^2 \\
& \leq & (2a \sqrt(2)+3)^2 N(d)
\end{eqnarray*}

The first inequality follows from the fact that if two points are $ad$ close,
their x-coordinates and y-coordinates will differ by at most $ad$. I.e. their grid coordinates will
differ at most by $s$. This means the pair will be accounted for in the right hand side of the
inequality.

The third inequality is an application of the Cauchy--Schwarz inequality.

The last inequality follows from the fact that the largest possible distance of two points
in the same grid cell is $d$. \qed\<close>

theory Randomized_Closest_Pair_Growth
  imports
    "HOL-Library.Sublist"
    Randomized_Closest_Pair_Correct
begin

lemma inj_translate:
  fixes a b :: int
  shows "inj (\<lambda>x. (fst x + a, snd x + b))"
proof -
  have 0:"(\<lambda>x. (fst x + a, snd x + b)) = (\<lambda>x. x + (a,b))" by auto
  show ?thesis unfolding 0 by simp
qed

lemma of_nat_sum':
  "(of_nat (sum' f S) :: ('a :: {semiring_char_0})) = sum' (\<lambda>x. of_nat (f x)) S"
  unfolding sum.G_def by simp

lemma sum'_nonneg:
  fixes f :: "'a \<Rightarrow> 'b :: {ordered_comm_monoid_add}"
  assumes "\<And>x. x \<in> S \<Longrightarrow> f x \<ge> 0"
  shows "sum' f S \<ge> 0"
proof -
  have "0 \<le> sum f {x \<in> S. f x \<noteq> 0}" using assms by (intro sum_nonneg) auto
  thus ?thesis unfolding sum.G_def by simp
qed

lemma sum'_mono:
  fixes f :: "'a \<Rightarrow> 'b :: {ordered_comm_monoid_add}"
  assumes "\<And>x. x \<in> S \<Longrightarrow> f x \<le> g x"
  assumes "finite {x \<in> S. f x \<noteq> 0}"
  assumes "finite {x \<in> S. g x \<noteq> 0}"
  shows "sum' f S \<le> sum' g S" (is "?L \<le> ?R")
proof -
  let ?S = "{i \<in> S. f i \<noteq> 0} \<union> {i \<in> S. g i \<noteq> 0}"

  have "?L = sum' f ?S" by (intro sum.mono_neutral_right') auto
  also have "... = (\<Sum>i \<in> ?S. f i)" using assms by (intro sum.eq_sum) auto
  also have "... \<le> (\<Sum>i \<in> ?S. g i)" using assms by (intro sum_mono) auto
  also have "... = sum' g ?S" using assms by (intro sum.eq_sum[symmetric]) auto
  also have "... = ?R"  by (intro sum.mono_neutral_left') auto
  finally show ?thesis by simp
qed

lemma cauchy_schwarz':
  assumes "finite {i \<in> S. f i \<noteq> 0}"
  assumes "finite {i \<in> S. g i \<noteq> 0}"
  shows "sum' (\<lambda>i. f i * g i) S \<le> sqrt (sum' (\<lambda>i. f i^2) S) * sqrt (sum' (\<lambda>i. g i^2) S)"
    (is "?L \<le> ?R")
proof -
  let ?S = "{i \<in> S. f i \<noteq> 0} \<union> {i \<in> S. g i \<noteq> 0}"

  have "?L = sum' (\<lambda>i. f i * g i) ?S" by (intro sum.mono_neutral_right') auto
  also have "... = (\<Sum>i \<in> ?S. f i * g i)" using assms by (intro sum.eq_sum) auto
  also have "... \<le> (\<Sum>i \<in> ?S. \<bar>f i\<bar> * \<bar>g i\<bar>)" by (intro sum_mono) (metis abs_ge_self abs_mult)
  also have "... \<le> L2_set f ?S * L2_set g ?S" by (rule L2_set_mult_ineq)
  also have "... = sqrt (sum' (\<lambda>i. f i^2) ?S) * sqrt (sum' (\<lambda>i. g i^2) ?S)"
    unfolding L2_set_def using assms sum.eq_sum by simp
  also have "... = ?R"
    by (intro arg_cong2[where f="(\<lambda>x y. sqrt x * sqrt y)"] sum.mono_neutral_left') auto
  finally show ?thesis by simp
qed

context comm_monoid_set
begin

lemma reindex_bij_betw':
  assumes "bij_betw h S T"
  shows "G (\<lambda>x. g (h x)) S = G g T"
proof -
  have "h ` {x \<in> S. g (h x) \<noteq> \<^bold>1} = {x \<in> T. g x \<noteq> \<^bold>1}"
    using bij_betw_imp_surj_on[OF assms] by auto
  hence 0: "bij_betw h {x \<in> S. g (h x) \<noteq> \<^bold>1} {x \<in> T. g x \<noteq> \<^bold>1}"
    by (intro bij_betw_subset[OF assms]) auto
  hence "finite {x \<in> S. g (h x) \<noteq> \<^bold>1} = finite {x \<in> T. g x \<noteq> \<^bold>1}"
    using bij_betw_finite by auto
  thus ?thesis unfolding G_def using reindex_bij_betw[OF 0] by simp
qed

end


definition "close_point_size xs d = length (filter (\<lambda>(p,q). dist p q < d) (List.product xs xs))"

lemma grid_dist_upper:
  fixes p q :: point
  assumes "d > 0"
  shows "dist p q < sqrt (\<Sum>i\<in>UNIV.(d*(\<bar>\<lfloor>p$i/d\<rfloor>-\<lfloor>q$i/d\<rfloor>\<bar>+1))^2)"
    (is "?L < ?R")
proof -
  have a:"\<bar>x - y\<bar> < \<bar>d * real_of_int (\<bar>\<lfloor>x/d\<rfloor> - \<lfloor>y/d\<rfloor>\<bar> + 1)\<bar>" for x y :: real
  proof -
    have "\<bar>x - y\<bar> = d * \<bar>x/d - y/d\<bar>"
      using assms by (simp add: abs_mult_pos' right_diff_distrib)
    also have "... < d * real_of_int (\<bar>\<lfloor>x/d\<rfloor> - \<lfloor>y/d\<rfloor>\<bar> + 1)"
      by (intro mult_strict_left_mono assms) linarith
    also have "... = \<bar>d * real_of_int (\<bar>\<lfloor>x/d\<rfloor> - \<lfloor>y/d\<rfloor>\<bar> + 1)\<bar>"
      using assms by simp
    finally show ?thesis by simp
  qed
  have "?L =  sqrt (\<Sum>i\<in>UNIV. (p $ i - q $ i)\<^sup>2)"
    unfolding dist_vec_def dist_real_def L2_set_def by simp
  also have "... < ?R"
    using assms by (intro real_sqrt_less_mono sum_strict_mono power2_strict_mono a) auto
  finally show ?thesis by simp
qed

lemma grid_dist_upperI:
  fixes p q :: point
  fixes d :: real
  assumes "d > 0"
  assumes "\<And>k. \<bar>\<lfloor>p$k/d\<rfloor>-\<lfloor>q$k/d\<rfloor>\<bar> \<le> s"
  shows "dist p q < d * (s+1) * sqrt 2"
proof -
  have s_ge_0: "s \<ge> 0" using assms(2)[where k="0"] by simp
  have "dist p q < sqrt (\<Sum>i \<in> UNIV. (d*(\<bar>\<lfloor>p$i/d\<rfloor>-\<lfloor>q$i/d\<rfloor>\<bar>+1))^2)"
    by (intro grid_dist_upper assms)
  also have "... \<le> sqrt (\<Sum>i \<in> (UNIV::2 set). (d*(s+1))^2)"
    using assms
    by (intro real_sqrt_le_mono sum_mono power_mono mult_left_mono iffD2[OF of_int_le_iff]) auto
  also have "... = sqrt (2 * (d*(s+1))^2)" by simp
  also have "... = sqrt 2 * sqrt ((d*(s+1))^2)" by (simp add:real_sqrt_mult)
  also have "... = sqrt 2 * (d * (s+1))" using assms s_ge_0 by simp
  also have "... =  d * (s+1) * sqrt 2" by simp
  finally show ?thesis by simp
qed

lemma close_point_approx_upper:
  fixes xs :: "point list"
  fixes G :: "int \<times> int \<Rightarrow> real"
  assumes "d > 0" "e > 0"
  defines "s \<equiv> \<lceil>d / e\<rceil>"
  defines "G \<equiv> (\<lambda>x. real (length (filter (\<lambda>p. to_grid e p = x)  xs)))"
  shows "close_point_size xs d \<le> (\<Sum>i \<in> {-s..s}\<times>{-s..s}. sum' (\<lambda>x. G x * G (x+i)) UNIV)"
    (is "?L \<le> ?R")
proof -
  let ?f = "to_grid e"
  let ?pairs = "mset (List.product xs xs)"

  define T where "T = {-s..s} \<times> {-s..s}"

  have "s \<ge> 1" unfolding s_def using assms by simp
  hence s_ge_0: "s \<ge> 0" by simp

  have 0: "finite T" unfolding T_def by simp

  have a: "size {#p \<in># ?pairs. ?f (fst p)-?f (snd p) = i #} = sum' (\<lambda>x. G x * G (x+i)) UNIV"
    (is "?L1 = ?R1") for i
  proof -
    have "?L1 = size {#p \<in># ?pairs. (?f (fst p),?f (snd p)) \<in> {(x,y). x - y = i} #}"
      by simp
    also have "... = sum' (\<lambda>q. size {# p \<in># ?pairs. (?f (fst p), ?f (snd p))= q #} ) {(x,y). x-y=i}"
      unfolding size_filter_mset_decompose' by simp
    also have "... = sum' (\<lambda>q. size {# p \<in># ?pairs. (?f (fst p), ?f (snd p)) = (q+i,q) #}) UNIV"
      by (intro arg_cong[where f="real"] sum.reindex_bij_betw'[symmetric] bij_betwI[where g="snd"])
        auto
    also have "... =
      sum' (\<lambda>q. length (filter (\<lambda>p. ?f (fst p) = q+i \<and> ?f (snd p) = q) (List.product xs xs))) UNIV"
      by (simp flip: size_mset mset_filter conj_commute)
    also have "... = sum' (\<lambda>x. G (x+i) * G x) UNIV"
      by (subst filter_product)
        (simp add:G_def build_grid_def of_nat_sum' case_prod_beta' prod_eq_iff)
    finally show ?thesis by (simp add:algebra_simps)
  qed

  have b:"f (?f p) - f (?f q) \<in> {-s..s}" if "f = fst \<or> f = snd" "dist p q < d" for p q f
  proof -
    have "\<bar>f (?f p) - f (?f q)\<bar> \<le> \<lceil>dist p q/e\<rceil>"
      using grid_dist[OF assms(2), where p="p" and q="q"] that(1) unfolding to_grid_def by auto
    also have "... \<le> s"
      unfolding s_def using that(2) assms(1,2)
      by (simp add: ceiling_mono divide_le_cancel)
    finally have "\<bar>f (?f p) - f (?f q)\<bar> \<le> s" by simp
    thus ?thesis using s_ge_0 by auto
  qed

  have c:"?f p - ?f q \<in> T" if "dist p q < d" for p q
    unfolding T_def using b[OF _ that] unfolding mem_Times_iff by simp

  have "?L = size (filter_mset (\<lambda>(p,q). dist p q < d) ?pairs)"
    unfolding close_point_size_def by (metis mset_filter size_mset)
  also have "... \<le> size (filter_mset (\<lambda>p. ?f (fst p) - ?f (snd p) \<in> T) ?pairs)"
    using c by (intro size_mset_mono of_nat_mono multiset_filter_mono_2) auto
  also have "... = (\<Sum>i \<in> T. size (filter_mset (\<lambda>p. ?f (fst p) - ?f (snd p) = i) ?pairs))"
    by (intro size_filter_mset_decompose arg_cong[where f="of_nat"] 0)
  also have "... = (\<Sum>i \<in> T. sum' (\<lambda>x. G x * G (x+i)) UNIV)"
    unfolding of_nat_sum by (intro sum.cong a refl)
  also have "... = ?R" unfolding T_def by simp
  finally show ?thesis by simp
qed

lemma close_point_approx_lower:
  fixes xs :: "point list"
  fixes G :: "int \<times> int \<Rightarrow> real"
  fixes d :: real
  assumes "d > 0"
  defines "G \<equiv> (\<lambda>x. real (length (filter (\<lambda>p. to_grid d p = x)  xs)))"
  shows "sum' (\<lambda>x. G x ^ 2) UNIV \<le> close_point_size xs (d * sqrt 2)"
    (is "?L \<le> ?R")
proof -
  let ?f = "to_grid d"
  let ?pairs = "mset (List.product xs xs)"

  have "?L = sum' (\<lambda>x. length (filter (\<lambda>p. ?f p = x) xs)^2) UNIV "
    unfolding build_grid_def G_def by (simp add:of_nat_sum' prod_eq_iff case_prod_beta')
  also have "... = sum'(\<lambda>x. length(List.product (filter(\<lambda>p. ?f p=x)xs) (filter(\<lambda>p. ?f p=x)xs)))UNIV"
    unfolding length_product by (simp add:power2_eq_square)
  also have "... = sum' (\<lambda>x. length (filter(\<lambda>p. ?f(fst p)=x\<and>?f(snd p)=x)(List.product xs xs))) UNIV"
    by (subst filter_product) simp
  also have "... = sum' (\<lambda>x. size {# p \<in># ?pairs. ?f (fst p) = x \<and> ?f (snd p) = x #}) UNIV"
    by (intro arg_cong2[where f="sum'"] arg_cong[where f="real"] refl ext)
     (metis (no_types, lifting) mset_filter size_mset)
  also have "... = sum' (\<lambda>x. size {# p \<in>#{# p\<in>#?pairs. ?f(fst p)=?f(snd p) #}. ?f(fst p)=x #}) UNIV"
    unfolding filter_filter_mset
    by (intro sum.cong' arg_cong[where f="real"] arg_cong[where f="size"] filter_mset_cong) auto
  also have "... = size {# p \<in># {# p \<in># ?pairs. ?f (fst p) = ?f (snd p) #}. ?f (fst p) \<in> UNIV #}"
    by (intro arg_cong[where f="real"] size_filter_mset_decompose'[symmetric])
  also have "... \<le> size {# p \<in># ?pairs. ?f (fst p) = ?f (snd p) #}" by simp
  also have "... = size {# p \<in># ?pairs. \<forall>k. \<lfloor>fst p $ k/d\<rfloor> = \<lfloor>snd p $ k/d\<rfloor> #}"
    unfolding to_grid_def prod.inject
    by (intro arg_cong[where f="size"] arg_cong[where f="of_nat"] filter_mset_cong refl)
     (metis (full_types) exhaust_2 one_neq_zero)
  also have "... \<le> size {# p \<in># ?pairs. dist (fst p) (snd p) < d * of_int (0+1) * sqrt 2 #}"
    by (intro of_nat_mono size_mset_mono multiset_filter_mono_2 grid_dist_upperI[OF assms(1)]) simp
  also have "... = ?R" unfolding close_point_size_def
    by (simp add:case_prod_beta') (metis (no_types, lifting) mset_filter size_mset)
  finally show ?thesis by simp
qed

lemma build_grid_finite:
  assumes "inj f"
  shows "finite {x. filter (\<lambda>p. to_grid d p = f x) xs \<noteq> []}"
proof -
  have 0:"finite (to_grid d ` set xs)" by (intro finite_imageI) auto
  have "finite {x. filter (\<lambda>p. to_grid d p = x) xs \<noteq> []}"
    unfolding filter_empty_conv by (intro finite_subset[OF _ 0]) blast
  hence "finite (f -` {x. filter (\<lambda>p. to_grid d p = x) xs \<noteq> []})" by (intro finite_vimageI assms)
  thus ?thesis by (simp add:vimage_def)
qed

text \<open>Main result of this section:\<close>

lemma growth_lemma:
  fixes xs :: "point list"
  assumes "a > 0" "d > 0"
  shows "close_point_size xs (a * d) \<le> (2 * sqrt 2 * a + 3)^2 * close_point_size xs d"
    (is "?L \<le> ?R")
proof -
  let ?s = "\<lceil>a * sqrt 2\<rceil>"
  let ?G = "(\<lambda>x. real (length (filter (\<lambda>p. to_grid (d/sqrt 2) p = x)  xs)))"
  let ?I = "{-?s..?s}\<times>{-?s..?s}"

  have "?s \<ge> 1" using assms by auto
  hence s_ge_0: "?s \<ge> 0" by simp

  have a: "?s = \<lceil>a * d / (d / sqrt 2)\<rceil>" using assms by simp

  have "?L \<le> (\<Sum>i\<in>{-?s..?s}\<times>{-?s..?s}. sum' (\<lambda>x. ?G x * ?G (x+i)) UNIV)"
    using assms unfolding a by (intro close_point_approx_upper) auto
  also have "... \<le> (\<Sum>i\<in>?I. sqrt (sum' (\<lambda>x. ?G x^2) UNIV) * sqrt (sum' (\<lambda>x. ?G (x+i)^2) UNIV))"
    by (intro sum_mono cauchy_schwarz') (auto intro: inj_translate build_grid_finite)
  also have "... = (\<Sum>i\<in>?I. sqrt (sum' (\<lambda>x. ?G x^2) UNIV) * sqrt (sum' (\<lambda>x. ?G x^2) UNIV))"
    by (intro arg_cong2[where f="(\<lambda>x y. sqrt x * sqrt y)"] sum.cong refl
        sum.reindex_bij_betw' bij_plus_right)
  also have "... = (\<Sum>i\<in>?I. \<bar>sum' (\<lambda>x. ?G x^2) UNIV\<bar>)" by simp
  also have "... = (2* ?s + 1)^2 * \<bar>sum' (\<lambda>x. ?G x^2) UNIV\<bar>"
    using s_ge_0 by (auto simp: power2_eq_square)
  also have "... = (2* ?s + 1)^2 * sum' (\<lambda>x. ?G x^2) UNIV"
    by (intro arg_cong2[where f="(*)"] refl abs_of_nonneg sum'_nonneg) auto
  also have "... \<le> (2*?s+1)^2 * real (close_point_size xs ((d/sqrt 2)* sqrt 2))"
    using assms by (intro mult_left_mono close_point_approx_lower) auto
  also have "... =  (2 * of_int ?s+1)^2 * real (close_point_size xs d)" by simp
  also have "... \<le> (2 * (a * sqrt 2 + 1) + 1)^2 * real (close_point_size xs d)"
    using s_ge_0 by (intro mult_right_mono power_mono add_mono mult_left_mono) auto
  also have "... = ?R" by (auto simp:algebra_simps)
  finally show ?thesis by simp
qed

end