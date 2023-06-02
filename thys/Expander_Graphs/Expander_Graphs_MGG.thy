section \<open>Margulis Gabber Galil Construction\label{sec:margulis}\<close>

text \<open>This section formalizes the Margulis-Gabber-Galil expander graph, which is defined on the
product space $\mathbb Z_n \times \mathbb Z_n$. The construction is an adaptation of graph
introduced by Margulis~\cite{margulis1973}, for which he gave a non-constructive proof of its
spectral gap. Later Gabber and Galil~\cite{gabber1981} adapted the graph and derived an explicit
spectral gap, i.e., that the second largest eigenvalue is bounded by $\frac{5}{8} \sqrt{2}$. The
proof was later improved by Jimbo and Marouka~\cite{jimbo1987} using Fourier Analysis. 
Hoory et al.~\cite[\S 8]{hoory2006} present a slight simplification of that proof (due to Boppala)
which this formalization is based on.\<close>

theory Expander_Graphs_MGG
  imports 
    "HOL-Analysis.Complex_Transcendental"
    "HOL-Decision_Procs.Approximation"
    Expander_Graphs_Definition
begin

datatype ('a, 'b) arc = Arc (arc_tail: 'a)  (arc_head: 'a) (arc_label: 'b)  

fun mgg_graph_step :: "nat \<Rightarrow> (int \<times> int) \<Rightarrow> (nat \<times> int) \<Rightarrow> (int \<times> int)"
  where "mgg_graph_step n (i,j) (l,\<sigma>) = 
  [ ((i+\<sigma>*(2*j+0)) mod int n, j), (i, (j+\<sigma>*(2*i+0)) mod int n)
  , ((i+\<sigma>*(2*j+1)) mod int n, j), (i, (j+\<sigma>*(2*i+1)) mod int n) ] ! l"

definition mgg_graph :: "nat \<Rightarrow> (int \<times> int, (int \<times> int, nat \<times> int) arc) pre_digraph" where 
  "mgg_graph n =
    \<lparr> verts = {0..<n} \<times> {0..<n}, 
      arcs = (\<lambda>(t,l). (Arc t (mgg_graph_step n t l) l))`(({0..<int n}\<times>{0..<int n})\<times>({..<4}\<times>{-1,1})), 
      tail = arc_tail,
      head = arc_head \<rparr>"

locale margulis_gaber_galil =
  fixes m :: nat
  assumes m_gt_0: "m > 0"
begin

abbreviation G where "G \<equiv> mgg_graph m"

lemma wf_digraph: "wf_digraph (mgg_graph m)"
proof -
  have 
    "tail (mgg_graph m) e \<in> verts (mgg_graph m)" (is "?A") 
    "head (mgg_graph m) e \<in> verts (mgg_graph m)" (is "?B")
    if a:"e \<in> arcs (mgg_graph m)" for e
  proof -
    obtain t l \<sigma> where tl_def: 
      "t \<in> {0..<int m} \<times> {0..<int m}" "l \<in> {..<4}" "\<sigma> \<in> {-1,1}" 
      "e = Arc t (mgg_graph_step m t (l,\<sigma>)) (l,\<sigma>)"
      using a mgg_graph_def by auto 
    thus ?A
      unfolding mgg_graph_def by auto
    have "mgg_graph_step m (fst t, snd t) (l,\<sigma>) \<in> {0..<int m} \<times> {0..<int m}" 
      unfolding mgg_graph_step.simps using tl_def(1,2) m_gt_0
      by (intro set_mp[OF _ nth_mem])  auto
    hence "arc_head e \<in> {0..<int m} \<times> {0..<int m}" 
      unfolding tl_def(4) by simp
    thus ?B
      unfolding mgg_graph_def by simp
  qed
  thus ?thesis
    by unfold_locales auto
qed

lemma mgg_finite: "fin_digraph (mgg_graph m)"
proof -
  have "finite (verts (mgg_graph m))" "finite (arcs (mgg_graph m))"
    unfolding mgg_graph_def by auto
  thus ?thesis
    using wf_digraph
    unfolding fin_digraph_def fin_digraph_axioms_def by auto
qed

interpretation fin_digraph "mgg_graph m"
  using mgg_finite by simp

definition arcs_pos :: "(int \<times> int, nat \<times> int) arc set" 
    where "arcs_pos = (\<lambda>(t,l). (Arc t (mgg_graph_step m t (l,1)) (l, 1)))`(verts G\<times>{..<4})"
definition arcs_neg :: "(int \<times> int, nat \<times> int) arc set" 
    where "arcs_neg = (\<lambda>(h,l). (Arc (mgg_graph_step m h (l,1)) h (l,-1)))`(verts G\<times>{..<4})"

lemma arcs_sym:
  "arcs G = arcs_pos \<union> arcs_neg"
proof -
  have 0: "x \<in> arcs G" if "x \<in> arcs_pos" for x 
    using that unfolding arcs_pos_def mgg_graph_def by auto 
  have 1: "a \<in> arcs G" if t:"a \<in> arcs_neg" for a 
  proof -
    obtain h l where hl_def: "h \<in> verts G" "l \<in> {..<4}" "a = Arc (mgg_graph_step m h (l,1)) h (l,-1)"
      using t unfolding arcs_neg_def by auto

    define t where "t = mgg_graph_step m h (l,1)"

    have h_ran: "h \<in> {0..<int m} \<times> {0..<int m}" 
      using hl_def(1) unfolding mgg_graph_def by simp
    have l_ran: "l \<in> set [0,1,2,3]" 
      using hl_def(2) by auto

    have "t \<in> {0..<int m} \<times> {0..<int m}" 
      using h_ran l_ran
      unfolding t_def by (cases h, auto simp add:mod_simps)
    hence t_ran: "t \<in> verts G" 
      unfolding mgg_graph_def by simp

    have "h = mgg_graph_step m t (l,-1)" 
      using h_ran l_ran unfolding t_def by (cases h, auto simp add:mod_simps)
    hence "a = Arc t (mgg_graph_step m t (l,-1)) (l,-1)"
      unfolding t_def hl_def(3) by simp
    thus ?thesis 
      using t_ran hl_def(2) mgg_graph_def by (simp add:image_iff)
  qed

  have "card (arcs_pos \<union> arcs_neg) = card arcs_pos + card arcs_neg"
    unfolding arcs_pos_def arcs_neg_def by (intro card_Un_disjoint finite_imageI) auto
  also have "... = card (verts G\<times>{..<4::nat}) + card (verts G\<times>{..<4::nat})"
    unfolding arcs_pos_def arcs_neg_def
    by (intro arg_cong2[where f="(+)"] card_image inj_onI) auto
  also have "... = card (verts G\<times>{..<4::nat}\<times>{-1,1::int})"
    by simp
  also have "... = card ((\<lambda>(t, l). Arc t (mgg_graph_step m t l) l) ` (verts G \<times>{..<4}\<times>{-1,1}))"
    by (intro card_image[symmetric] inj_onI) auto
  also have "... = card (arcs G)"
    unfolding mgg_graph_def by simp
  finally have "card (arcs_pos \<union> arcs_neg) = card (arcs G)" 
    by simp
  hence "arcs_pos \<union> arcs_neg = arcs G"
    using 0 1 by (intro card_subset_eq, auto) 
  thus ?thesis by simp
qed

lemma sym: "symmetric_multi_graph (mgg_graph m)"
proof -
  define f :: "(int \<times> int, nat \<times> int) arc \<Rightarrow> (int \<times> int, nat \<times> int) arc"  
    where "f a = Arc (arc_head a) (arc_tail a) (apsnd (\<lambda>x. (-1) * x) (arc_label a))" for a 

  have a: "bij_betw f arcs_pos arcs_neg"
    by (intro bij_betwI[where g="f"])
     (auto simp add:f_def image_iff arcs_pos_def arcs_neg_def)

  have b: "bij_betw f arcs_neg arcs_pos"
    by (intro bij_betwI[where g="f"])
     (auto simp add:f_def image_iff  arcs_pos_def arcs_neg_def)

  have c:"bij_betw f (arcs_pos \<union> arcs_neg) (arcs_neg \<union> arcs_pos)"
    by (intro bij_betw_combine[OF a b])  (auto simp add:arcs_pos_def arcs_neg_def)

  hence c:"bij_betw f (arcs G) (arcs G)"
    unfolding arcs_sym by (subst (2) sup_commute, simp)
  show ?thesis
    by (intro symmetric_multi_graphI[where f="f"] fin_digraph_axioms c) 
     (simp add:f_def mgg_graph_def)
qed

lemma out_deg:
  assumes "v \<in> verts G"
  shows "out_degree G v = 8"
proof -
  have "out_degree (mgg_graph m) v = card (out_arcs (mgg_graph m) v)"
    unfolding out_degree_def by simp
  also have "... = card {e. (\<exists>w \<in> verts (mgg_graph m). \<exists>l \<in> {..<4} \<times> {-1,1}. 
    e = Arc w (mgg_graph_step m w l) l \<and> arc_tail e = v)}" 
    unfolding mgg_graph_def out_arcs_def by (simp add:image_iff)
  also have "... = card {e. (\<exists>l \<in> {..<4} \<times> {-1,1}. e = Arc v (mgg_graph_step m v l) l)}"
    using assms by (intro arg_cong[where f="card"] iffD2[OF set_eq_iff] allI)  auto
  also have "... = card ((\<lambda>l. Arc v (mgg_graph_step m v l) l) ` ({..<4} \<times> {-1,1}))"
    by (intro arg_cong[where f="card"]) (auto simp add:image_iff)
  also have "... = card ({..<4::nat} \<times> {-1,1::int})"
    by (intro card_image inj_onI) simp
  also have "... = 8" by simp
  finally show ?thesis by simp
qed

lemma verts_ne:
  "verts G \<noteq> {}" 
  using m_gt_0 unfolding mgg_graph_def by simp

sublocale regular_graph "mgg_graph m"
  using out_deg verts_ne
  by (intro regular_graphI[where d="8"] sym) auto

lemma d_eq_8: "d = 8"
proof -
  obtain v where v_def: "v \<in> verts G"
    using verts_ne by auto
  hence 0:"(SOME v. v \<in> verts G) \<in> verts G"
    by (rule someI[where x="v"])
  show ?thesis
    using out_deg[OF 0]
    unfolding d_def by simp
qed

text \<open>We start by introducing Fourier Analysis on the torus $\mathbb Z_n \times \mathbb Z_n$. The
following is too specialized for a general AFP entry.\<close>

lemma g_inner_sum_left:
  assumes "finite I"
  shows "g_inner (\<lambda>x. (\<Sum>i \<in> I. f i x)) g = (\<Sum>i\<in> I. g_inner (f i) g)"
  using assms by (induction I rule:finite_induct) (auto simp add:g_inner_simps)

lemma g_inner_sum_right:
  assumes "finite I"
  shows "g_inner f (\<lambda>x. (\<Sum>i \<in> I. g i x)) = (\<Sum>i\<in> I. g_inner f (g i))"
  using assms by (induction I rule:finite_induct) (auto simp add:g_inner_simps)

lemma g_inner_reindex:
  assumes "bij_betw h (verts G) (verts G)"
  shows "g_inner f g = g_inner (\<lambda>x. (f (h x))) (\<lambda>x. (g (h x)))"
  unfolding g_inner_def
  by (subst sum.reindex_bij_betw[OF assms,symmetric]) simp
  
definition \<omega>\<^sub>F :: "real \<Rightarrow> complex" where "\<omega>\<^sub>F x = cis (2*pi*x/m)"

lemma \<omega>\<^sub>F_simps:
  "\<omega>\<^sub>F (x + y) = \<omega>\<^sub>F x * \<omega>\<^sub>F y"
  "\<omega>\<^sub>F (x - y) = \<omega>\<^sub>F x * \<omega>\<^sub>F (-y)"
  "cnj (\<omega>\<^sub>F x) = \<omega>\<^sub>F (-x)"
  unfolding \<omega>\<^sub>F_def by (auto simp add:algebra_simps diff_divide_distrib 
      add_divide_distrib cis_mult cis_divide cis_cnj)

lemma \<omega>\<^sub>F_cong:
  fixes x y :: int
  assumes "x mod m = y mod m" 
  shows "\<omega>\<^sub>F (of_int x) = \<omega>\<^sub>F (of_int y)"
proof -
  obtain z :: int where "y = x + m*z" using mod_eqE[OF assms] by auto
  hence "\<omega>\<^sub>F (of_int y) = \<omega>\<^sub>F (of_int x + of_int (m*z))"
    by simp
  also have "... = \<omega>\<^sub>F (of_int x) * \<omega>\<^sub>F (of_int (m*z))"
    by (simp add:\<omega>\<^sub>F_simps)
  also have "... = \<omega>\<^sub>F (of_int x) * cis (2 * pi * of_int (z))"
    unfolding \<omega>\<^sub>F_def  using m_gt_0 
    by (intro arg_cong2[where f="(*)"] arg_cong[where f="cis"]) auto
  also have "... = \<omega>\<^sub>F (of_int x) * 1"
    by (intro arg_cong2[where f="(*)"] cis_multiple_2pi) auto
  finally show ?thesis by simp
qed

lemma cis_eq_1_imp:
  assumes "cis (2 * pi * x) = 1"
  shows "x \<in> \<int>"
proof -
  have "cos (2 * pi * x) = Re (cis (2*pi*x))" 
    using cis.simps by simp
  also have "... = 1" 
    unfolding assms by simp
  finally have "cos (2 * pi * x) = 1" by simp
  then obtain y where "2 * pi * x = of_int y * 2 * pi"
    using cos_one_2pi_int by auto
  hence "y = x" by simp
  thus ?thesis by auto
qed

lemma \<omega>\<^sub>F_eq_1_iff:
  fixes x :: int
  shows "\<omega>\<^sub>F x = 1 \<longleftrightarrow> x mod m = 0"
proof
  assume "\<omega>\<^sub>F (real_of_int x) = 1"
  hence "cis (2 * pi * real_of_int x / real m) = 1"
    unfolding \<omega>\<^sub>F_def by simp
  hence "real_of_int x / real m \<in> \<int>"
    using cis_eq_1_imp by simp
  then obtain z :: int where "of_int x / real m = z"
    using Ints_cases by auto
  hence "x = z * real m"
    using m_gt_0 by (simp add: nonzero_divide_eq_eq)
  hence "x = z * m" using of_int_eq_iff by fastforce
  thus "x mod m = 0" by simp
next
  assume "x mod m = 0"
  hence "\<omega>\<^sub>F x = \<omega>\<^sub>F (of_int 0)"
    by (intro \<omega>\<^sub>F_cong) auto
  also have "... = 1" unfolding \<omega>\<^sub>F_def by simp
  finally show "\<omega>\<^sub>F x= 1" by simp
qed

definition FT :: "(int \<times> int \<Rightarrow> complex) \<Rightarrow> (int \<times> int \<Rightarrow> complex)"
  where "FT f v = g_inner f (\<lambda>x. \<omega>\<^sub>F (fst x * fst v + snd x * snd v))"

lemma FT_altdef: "FT f (u,v) = g_inner f (\<lambda>x. \<omega>\<^sub>F (fst x * u + snd x * v))"
  unfolding FT_def by (simp add:case_prod_beta)

lemma FT_add: "FT (\<lambda>x. f x + g x) v = FT f v + FT g v"
  unfolding FT_def by (simp add:g_inner_simps algebra_simps)

lemma FT_zero: "FT (\<lambda>x. 0) v = 0"
  unfolding FT_def g_inner_def by simp

lemma FT_sum: 
  assumes "finite I" 
  shows "FT (\<lambda>x. (\<Sum>i \<in> I. f i x)) v = (\<Sum>i \<in> I. FT (f i) v)"
  using assms by (induction rule: finite_induct, auto simp add:FT_zero FT_add)

lemma FT_scale: "FT (\<lambda>x. c * f x) v = c * FT f v"
  unfolding FT_def by (simp add: g_inner_simps)

lemma FT_cong:
  assumes "\<And>x. x \<in> verts G \<Longrightarrow> f x = g x"
  shows "FT f = FT g"
  unfolding FT_def by (intro ext g_inner_cong assms refl)

lemma parseval:
  "g_inner f g = g_inner (FT f) (FT g)/m^2" (is "?L = ?R")
proof -
  define \<delta> :: "(int \<times> int) \<Rightarrow> (int \<times> int) \<Rightarrow> complex" where "\<delta> x y = of_bool (x = y)" for x y

  have FT_\<delta>: "FT (\<delta> v) x = \<omega>\<^sub>F (-(fst v *fst x +snd v * snd x))" if "v \<in> verts G" for v x
    using that by (simp add:FT_def g_inner_def \<delta>_def \<omega>\<^sub>F_simps)

  have 1: "(\<Sum>x=0..<int m. \<omega>\<^sub>F (z*x)) = m * of_bool(z mod m = 0)" (is "?L1 = ?R1") for z :: int
  proof (cases "z mod m = 0")
    case True
    have "(\<Sum>x=0..<int m. \<omega>\<^sub>F (z*x)) = (\<Sum>x=0..<int m. \<omega>\<^sub>F (of_int 0))"
      using True by (intro sum.cong \<omega>\<^sub>F_cong refl) auto
    also have "... = m * of_bool(z mod m = 0)"
      unfolding \<omega>\<^sub>F_def True by simp
    finally show ?thesis by simp
  next
    case False
    have "(1-\<omega>\<^sub>F z) * ?L1 = (1-\<omega>\<^sub>F z) * (\<Sum>x \<in> int ` {..<m}. \<omega>\<^sub>F(z*x))"
      by (intro arg_cong2[where f="(*)"] sum.cong refl)
       (simp add: image_atLeastZeroLessThan_int)
    also have "... = (\<Sum>x<m. \<omega>\<^sub>F(z*real x) - \<omega>\<^sub>F(z*(real (Suc x))))"
      by (subst sum.reindex, auto simp add:algebra_simps sum_distrib_left \<omega>\<^sub>F_simps)
    also have "... = \<omega>\<^sub>F (z * 0) - \<omega>\<^sub>F (z * m)"
      by (subst sum_lessThan_telescope') simp
    also have "... = \<omega>\<^sub>F (of_int 0) - \<omega>\<^sub>F (of_int 0)"
      by (intro arg_cong2[where f="(-)"] \<omega>\<^sub>F_cong) auto
    also have "... = 0"
      by simp
    finally have "(1- \<omega>\<^sub>F z) * ?L1 = 0" by simp
    moreover have "\<omega>\<^sub>F z \<noteq> 1" using \<omega>\<^sub>F_eq_1_iff False by simp
    hence "(1- \<omega>\<^sub>F z) \<noteq> 0" by simp
    ultimately have "?L1 = 0" by simp
    then show ?thesis using False by simp
  qed

  have 0:"g_inner (\<delta> v) (\<delta> w) = g_inner (FT (\<delta> v)) (FT (\<delta> w))/m^2" (is "?L1 = ?R1/_")
    if "v \<in> verts G" "w \<in> verts G" for v w
  proof -
    have "?R1=g_inner(\<lambda>x. \<omega>\<^sub>F(-(fst v *fst x +snd v * snd x)))(\<lambda>x. \<omega>\<^sub>F(-(fst w *fst x +snd w * snd x)))"
      using that by (intro g_inner_cong, auto simp add:FT_\<delta>)
    also have "...=(\<Sum>(x,y)\<in>{0..<int m}\<times>{0..<int m}. \<omega>\<^sub>F((fst w-fst v)*x)*\<omega>\<^sub>F((snd w - snd v)* y))"
      unfolding g_inner_def by (simp add:\<omega>\<^sub>F_simps algebra_simps case_prod_beta mgg_graph_def)
    also have "...=(\<Sum>x=0..<int m. \<Sum>y = 0..<int m. \<omega>\<^sub>F((fst w - fst v)*x)*\<omega>\<^sub>F((snd w - snd v) * y))"
      by (subst sum.cartesian_product[symmetric]) simp
    also have "...=(\<Sum>x=0..<int m. \<omega>\<^sub>F((fst w - fst v)*x))*(\<Sum>y = 0..<int m. \<omega>\<^sub>F((snd w - snd v) * y))"
      by (subst sum.swap) (simp add:sum_distrib_left sum_distrib_right)
    also have "... = of_nat (m * of_bool(fst v mod m = fst w mod m)) * 
      of_nat (m * of_bool(snd v mod m = snd w mod m))"
      using m_gt_0 unfolding 1 
      by (intro arg_cong2[where f="(*)"] arg_cong[where f="of_bool"] 
          arg_cong[where f="of_nat"] refl) (auto simp add:algebra_simps cong:mod_diff_cong)
    also have "... = m^2 * of_bool(v = w)"
      using that by (auto simp add:prod_eq_iff mgg_graph_def power2_eq_square)
    also have "... = m^2 * ?L1" 
      using that unfolding g_inner_def \<delta>_def by simp
    finally have "?R1 = m^2 * ?L1" by simp
    thus ?thesis using m_gt_0 by simp
  qed

  have "?L = g_inner (\<lambda>x. (\<Sum>v \<in> verts G. (f v) * \<delta> v x)) (\<lambda>x. (\<Sum>v \<in> verts G. (g v) * \<delta> v x))"
    unfolding \<delta>_def by (intro g_inner_cong) auto
  also have "... = (\<Sum>v\<in>verts G. (f v) * (\<Sum>w\<in>verts G. cnj (g w) * g_inner (\<delta> v) (\<delta> w)))"
    by (simp add:g_inner_simps g_inner_sum_left g_inner_sum_right)
  also have "... = (\<Sum>v\<in>verts G. (f v) * (\<Sum>w\<in>verts G. cnj (g w) * g_inner(FT (\<delta> v)) (FT (\<delta> w))))/m^2"
    by (simp add:0 sum_divide_distrib sum_distrib_left algebra_simps)
  also have "...=g_inner(\<lambda>x.(\<Sum>v\<in>verts G. (f v)*FT (\<delta> v) x))(\<lambda>x.(\<Sum>v\<in>verts G. (g v)*FT (\<delta> v) x))/m\<^sup>2"
    by (simp add:g_inner_simps g_inner_sum_left g_inner_sum_right)
  also have "...=g_inner(FT(\<lambda>x.(\<Sum>v\<in>verts G.(f v)*\<delta> v x)))(FT(\<lambda>x.(\<Sum>v\<in>verts G.(g v)*\<delta> v x)))/m\<^sup>2"
    by (intro g_inner_cong arg_cong2[where f="(/)"]) (simp_all add: FT_sum FT_scale)
  also have "... = g_inner (FT f) (FT g)/m^2 "
    unfolding \<delta>_def comp_def
    by (intro g_inner_cong arg_cong2[where f="(/)"] fun_cong[OF FT_cong]) auto
  finally show ?thesis by simp
qed

lemma plancharel:
  "(\<Sum>v \<in> verts G. norm (f v)^2) = (\<Sum>v \<in> verts G. norm (FT f v)^2)/m^2" (is "?L = ?R")
proof -
  have "complex_of_real ?L = g_inner f f"
    by (simp flip:of_real_power add:complex_norm_square g_inner_def algebra_simps)
  also have "... = g_inner (FT f) (FT f) / m^2"
    by (subst parseval) simp
  also have "... = complex_of_real ?R"
    by (simp flip:of_real_power add:complex_norm_square g_inner_def algebra_simps) simp
  finally have "complex_of_real ?L = complex_of_real ?R" by simp
  thus ?thesis 
    using of_real_eq_iff by blast
qed

lemma FT_swap:
  "FT (\<lambda>x. f (snd x, fst x)) (u,v) = FT f (v,u)"
proof -
  have 0:"bij_betw (\<lambda>(x::int \<times> int). (snd x, fst x)) (verts G) (verts G)"
    by (intro bij_betwI[where g="(\<lambda>(x::int \<times> int). (snd x, fst x))"])
     (auto simp add:mgg_graph_def)
  show ?thesis
    unfolding FT_def
    by (subst g_inner_reindex[OF 0]) (simp add:algebra_simps)
qed

lemma mod_add_mult_eq:
  fixes a x y :: int
  shows "(a + x * (y mod m)) mod m = (a+x*y) mod m"
  using mod_add_cong mod_mult_right_eq by blast

definition periodic where "periodic f = (\<forall>x y. f (x,y) = f (x mod int m, y mod int m))"

lemma periodicD:
  assumes "periodic f"
  shows "f (x,y) = f (x mod m, y mod m)"
  using assms unfolding periodic_def by simp

lemma periodic_comp:
  assumes "periodic f"
  shows "periodic (\<lambda>x. g (f x))"
  using assms unfolding periodic_def by simp

lemma periodic_cong:
  fixes x y u v :: int
  assumes "periodic f"
  assumes "x mod m = u mod m" "y mod m = v mod m" 
  shows "f (x,y) = f (u, v)"
  using periodicD[OF assms(1)] assms(2,3) by metis

lemma periodic_FT: "periodic (FT f)"
proof -
  have "FT f (x,y) = FT f (x mod m,y mod m)" for x y
    unfolding FT_altdef by (intro g_inner_cong \<omega>\<^sub>F_cong ext) 
     (auto simp add:mod_simps cong:mod_add_cong)
  thus ?thesis 
    unfolding periodic_def by simp
qed

lemma FT_sheer_aux:
  fixes u v c d :: int
  assumes "periodic f" 
  shows  "FT (\<lambda>x. f (fst x,snd x+c*fst x+d)) (u,v) = \<omega>\<^sub>F (d* v) * FT f (u-c* v,v)" 
    (is "?L = ?R")
proof -
  define s where "s = (\<lambda>(x,y). (x, (y - c * x-d) mod m))"
  define s0 where "s0 = (\<lambda>(x,y). (x, (y-c*x) mod m))"
  define s1 where "s1 = (\<lambda>(x::int,y). (x, (y-d) mod m))"

  have 0:"bij_betw s0 (verts G) (verts G)"
    by (intro bij_betwI[where g="\<lambda>(x,y). (x,(y+c*x) mod m)"])
     (auto simp add:mgg_graph_def s0_def Pi_def mod_simps)
  have 1:"bij_betw s1 (verts G) (verts G)"
    by (intro bij_betwI[where g="\<lambda>(x,y). (x,(y+d) mod m)"])
     (auto simp add:mgg_graph_def s1_def Pi_def mod_simps)
  have 2: "s = (s1 \<circ> s0)"
    by (simp add:s1_def s0_def s_def comp_def mod_simps case_prod_beta ext)
  have 3:"bij_betw s (verts G) (verts G)"
    unfolding 2 using bij_betw_trans[OF 0 1] by simp

  have 4:"(snd (s x) + c * fst x + d) mod int m = snd x mod m" for x
    unfolding s_def by (simp add:case_prod_beta cong:mod_add_cong) (simp add:algebra_simps)
  have 5: "fst (s x) = fst x" for x
    unfolding s_def by (cases x, simp)

  have "?L = g_inner (\<lambda>x. f (fst x, snd x + c*fst x+d)) (\<lambda>x. \<omega>\<^sub>F (fst x*u + snd x* v))"
    unfolding FT_altdef by simp
  also have "... = g_inner (\<lambda>x. f (fst x, (snd x + c*fst x+d) mod m)) (\<lambda>x. \<omega>\<^sub>F (fst x*u + snd x* v))"
    by (intro g_inner_cong  periodic_cong[OF assms]) (auto simp add:algebra_simps)
  also have "... = g_inner (\<lambda>x. f (fst x, snd x mod m)) (\<lambda>x. \<omega>\<^sub>F (fst x*u+ snd (s x)* v))"
    by (subst g_inner_reindex[OF 3]) (simp add:4 5)
  also have "... =
    g_inner (\<lambda>x. f (fst x, snd x mod m)) (\<lambda>x. \<omega>\<^sub>F (fst x*u+ ((snd x-c*fst x-d) mod m)* v))"
    by (simp add:s_def case_prod_beta)
  also have "... = g_inner f (\<lambda>x. \<omega>\<^sub>F (fst x* (u-c * v) + snd x * v-d * v))"
    by (intro g_inner_cong \<omega>\<^sub>F_cong) (auto simp add:mgg_graph_def algebra_simps mod_add_mult_eq) 
  also have "... = g_inner f (\<lambda>x. \<omega>\<^sub>F (-d* v)*\<omega>\<^sub>F (fst x*(u-c* v) + snd x * v))"
    by (simp add: \<omega>\<^sub>F_simps   algebra_simps)
  also have "... = \<omega>\<^sub>F (d* v)*g_inner f (\<lambda>x. \<omega>\<^sub>F (fst x*(u-c* v) + snd x * v))"
    by (simp add:g_inner_simps \<omega>\<^sub>F_simps)
  also have "... = ?R"
    unfolding FT_altdef by simp 
  finally show ?thesis by simp
qed

lemma FT_sheer:
  fixes u v c d :: int
  assumes "periodic f" 
  shows 
    "FT (\<lambda>x. f (fst x,snd x+c*fst x+d)) (u,v) = \<omega>\<^sub>F (d* v) * FT f (u-c* v,v)" (is "?A")
    "FT (\<lambda>x. f (fst x,snd x+c*fst x)) (u,v) = FT f (u-c* v,v)" (is "?B")
    "FT (\<lambda>x. f (fst x+c* snd x+d,snd x)) (u,v) = \<omega>\<^sub>F (d* u) * FT f (u,v-c*u)" (is "?C")
    "FT (\<lambda>x. f (fst x+c* snd x,snd x)) (u,v) = FT f (u,v-c*u)" (is "?D")
proof -
  have 1: "periodic (\<lambda>x. f (snd x, fst x))" 
    using assms unfolding periodic_def by simp

  have 0:"\<omega>\<^sub>F 0 = 1"
    unfolding \<omega>\<^sub>F_def by simp
  show ?A
    using FT_sheer_aux[OF assms] by simp
  show ?B
    using 0 FT_sheer_aux[OF assms, where d="0"] by simp
  show ?C
    using FT_sheer_aux[OF 1] by (subst (1 2) FT_swap[symmetric], simp)
  show ?D
    using 0 FT_sheer_aux[OF 1, where d="0"] by (subst (1 2) FT_swap[symmetric], simp)
qed

definition T\<^sub>1 :: "int \<times> int \<Rightarrow> int \<times> int" where "T\<^sub>1 x = ((fst x + 2 * snd x) mod m, snd x)"
definition S\<^sub>1 :: "int \<times> int \<Rightarrow> int \<times> int" where "S\<^sub>1 x = ((fst x - 2 * snd x) mod m, snd x)"
definition T\<^sub>2 :: "int \<times> int \<Rightarrow> int \<times> int" where "T\<^sub>2 x = (fst x, (snd x + 2 * fst x) mod m)"
definition S\<^sub>2 :: "int \<times> int \<Rightarrow> int \<times> int" where "S\<^sub>2 x = (fst x, (snd x - 2 * fst x) mod m)"

definition \<gamma>_aux :: "int \<times> int \<Rightarrow> real \<times> real" 
    where "\<gamma>_aux x = (\<bar>fst x/m-1/2\<bar>,\<bar>snd x/m-1/2\<bar>)"

definition compare :: "real \<times> real \<Rightarrow> real \<times> real \<Rightarrow> bool"
  where "compare x y = (fst x \<le> fst y \<and> snd x \<le> snd y \<and> x \<noteq> y)"

text \<open>The value here is different from the value in the source material. This is because the proof 
in Hoory~\cite[\S 8]{hoory2006} only establishes the bound $\frac{73}{80}$ while this formalization
establishes the improved bound of $\frac{5}{8} \sqrt 2$.\<close>

definition \<alpha> :: real where "\<alpha> = sqrt 2" 

lemma \<alpha>_inv: "1/\<alpha> = \<alpha>/2" 
  unfolding \<alpha>_def by (simp add: real_div_sqrt)

definition \<gamma> :: "int \<times> int \<Rightarrow> int \<times> int \<Rightarrow> real" 
  where "\<gamma> x y = (if compare (\<gamma>_aux x) (\<gamma>_aux y) then \<alpha> else (if compare  (\<gamma>_aux y) (\<gamma>_aux x) then (1 / \<alpha>) else 1))"

lemma \<gamma>_sym: "\<gamma> x y * \<gamma> y x = 1" 
  unfolding \<gamma>_def \<alpha>_def compare_def by (auto simp add:prod_eq_iff)

lemma \<gamma>_nonneg: "\<gamma> x y \<ge> 0"
  unfolding \<gamma>_def \<alpha>_def by auto

definition \<tau> :: "int \<Rightarrow> real" where "\<tau> x = \<bar>cos(pi*x/m)\<bar>"

definition \<gamma>' :: "real \<Rightarrow> real \<Rightarrow> real" 
  where "\<gamma>' x y = (if abs (x - 1/2) < abs (y - 1/2) then \<alpha> else (if abs (x-1/2) > abs (y-1/2) then (1 / \<alpha>) else 1))"

definition \<phi> :: "real \<Rightarrow> real \<Rightarrow> real"
  where "\<phi> x y = \<gamma>' y (frac(y-2*x))+\<gamma>' y (frac (y+2*x))"

lemma \<gamma>'_cases:
  "abs (x-1/2) = abs (y-1/2) \<Longrightarrow> \<gamma>' x y = 1"
  "abs (x-1/2) > abs (y-1/2) \<Longrightarrow> \<gamma>' x y = 1/\<alpha>"
  "abs (x-1/2) < abs (y-1/2) \<Longrightarrow> \<gamma>' x y = \<alpha>"
  unfolding \<gamma>'_def by auto

lemma if_cong_direct:
  assumes "a = b"
  assumes "c = d'"
  assumes "e = f"
  shows "(if a then c else e) = (if b then d' else f)"
  using assms by (intro if_cong) auto

lemma \<gamma>'_cong:
  assumes "abs (x-1/2) = abs (u-1/2)"
  assumes "abs (y-1/2) = abs (v-1/2)"
  shows "\<gamma>' x y = \<gamma>' u v"
  unfolding \<gamma>'_def
  using assms by (intro if_cong_direct refl) auto

lemma add_swap_cong:
  fixes x y u v :: "'a :: ab_semigroup_add"
  assumes "x = y" "u = v"
  shows "x + u = v + y"
  using assms by (simp add:algebra_simps)

lemma frac_cong:
  fixes x y :: real
  assumes "x - y \<in> \<int>"
  shows "frac x = frac y"
proof -
  obtain k where x_eq: "x = y + of_int k"
    using Ints_cases[OF assms] by (metis add_minus_cancel uminus_add_conv_diff)
  thus ?thesis
    unfolding x_eq  unfolding frac_def by simp
qed

lemma frac_expand:
  fixes x :: real
  shows "frac x = (if x < (-1) then (x-\<lfloor>x\<rfloor>) else (if x < 0 then (x+1) else (if x < 1 then x else (if x < 2 then (x-1) else  (x-\<lfloor>x\<rfloor>)))))"
proof -
  have "real_of_int y = -1 \<longleftrightarrow> y= -1" for y
    by auto
  thus ?thesis
    unfolding frac_def  by (auto simp add:not_less floor_eq_iff) 
qed

lemma one_minus_frac:
  fixes x :: real
  shows "1 - frac x = (if x \<in> \<int> then 1 else frac (-x))"
  unfolding frac_neg by simp

lemma abs_rev_cong:
  fixes x y :: real
  assumes "x = - y"
  shows "abs x = abs y"
  using assms by simp

lemma cos_pi_ge_0:
  assumes "x \<in>{-1/2.. 1/2}"
  shows "cos (pi * x) \<ge> 0"
proof -
  have "pi * x \<in> ((*) pi ` {-1/2..1/2})"
    by (intro imageI assms)
  also have "... =  {-pi/2..pi/2}" 
    by (subst image_mult_atLeastAtMost[OF pi_gt_zero])  simp
  finally have "pi * x \<in> {-pi/2..pi/2}" by simp
  thus ?thesis
    by (intro cos_ge_zero) auto 
qed

text \<open>The following is the first step in establishing Eq. 15 in Hoory et al.~\cite[\S 8]{hoory2006}.
Afterwards using various symmetries (diagonal, x-axis, y-axis) the result will follow for the entire
square $[0,1] \times [0,1]$.\<close>

lemma fun_bound_real_3:
  assumes "0 \<le> x"  "x \<le> y" "y \<le> 1/2" "(x,y) \<noteq> (0,0)"
  shows "\<bar>cos(pi*x)\<bar>*\<phi> x y + \<bar>cos(pi*y)\<bar>*\<phi> y x \<le> 2.5 * sqrt 2" (is "?L \<le> ?R")
proof -
  have apx:"4 \<le> 5 * sqrt (2::real)" "8 * cos (pi / 4) \<le> 5 * sqrt (2::real)"
    by (approximation 5)+

  have "cos (pi * x) \<ge> 0" 
    using assms(1,2,3)  by (intro cos_pi_ge_0) simp
  moreover have "cos (pi * y) \<ge> 0" 
    using assms(1,2,3)  by (intro cos_pi_ge_0) simp
  ultimately have 0:"?L = cos(pi*x)*\<phi> x y + cos(pi*y)*\<phi> y x"  (is "_ = ?T")
    by simp

  consider (a) "x+y < 1/2" | (b) "y = 1/2- x" | (c) "x+y > 1/2" by argo
  hence "?T \<le> 2.5 * sqrt 2" (is "?T \<le> ?R")
  proof (cases)
    case a
    consider 
      (1) "x < y" "x > 0" | 
      (2) "x=0" "y < 1/2" | 
      (3) "y=x" "x > 0" 
      using assms(1,2,3,4) a by fastforce
    thus ?thesis 
    proof (cases)
      case 1
      have "\<phi> x y = \<alpha> + 1/\<alpha>"
        unfolding \<phi>_def using 1 a
        by (intro arg_cong2[where f="(+)"] \<gamma>'_cases) (auto simp add:frac_expand) 
      moreover have "\<phi> y x = 1/\<alpha> + 1/\<alpha>"
        unfolding \<phi>_def using 1 a
        by (intro arg_cong2[where f="(+)"] \<gamma>'_cases) (auto simp add:frac_expand) 
      ultimately have "?T = cos (pi * x) * (\<alpha> + 1/\<alpha>) + cos (pi * y) * (1/\<alpha> + 1/\<alpha>)"
        by simp
      also have "... \<le> 1 * (\<alpha> + 1/\<alpha>) + 1 * (1/\<alpha> + 1/\<alpha>)"
        unfolding \<alpha>_def by (intro add_mono mult_right_mono) auto
      also have "... = ?R"
        unfolding \<alpha>_def by (simp add:divide_simps) 
      finally show ?thesis by simp
    next
      case 2
      have y_range: "y \<in> {0<..<1/2}" 
        using assms 2 by simp
      have "\<phi> 0 y = 1 + 1"
        unfolding \<phi>_def using y_range
        by (intro arg_cong2[where f="(+)"] \<gamma>'_cases) (auto simp add:frac_expand) 
      moreover 
      have "\<bar>x\<bar> * 2 < 1 \<longleftrightarrow> x < 1/2 \<and> -x < 1/2" for x :: real by auto
      hence "\<phi> y 0 = 1 / \<alpha> + 1/ \<alpha>"
        unfolding \<phi>_def using y_range
        by (intro arg_cong2[where f="(+)"] \<gamma>'_cases) (simp_all add:frac_expand)
      ultimately have "?T = 2 + cos (pi * y) * (2 / \<alpha>)"
        unfolding 2 by simp
      also have "... \<le> 2 + 1 * (2 / \<alpha>)"
        unfolding \<alpha>_def by (intro add_mono mult_right_mono) auto
      also have "... \<le> ?R" 
        unfolding \<alpha>_def by (approximation 10)
      finally show ?thesis by simp
    next
      case 3
      have "\<phi> x y = 1 + 1/\<alpha>"
        unfolding \<phi>_def using 3 a
        by (intro arg_cong2[where f="(+)"] \<gamma>'_cases) (auto simp add:frac_expand) 
      moreover have "\<phi> y x = 1 + 1/\<alpha>"
        unfolding \<phi>_def using 3 a
        by (intro arg_cong2[where f="(+)"] \<gamma>'_cases) (auto simp add:frac_expand) 
      ultimately have "?T = cos (pi * x) * (2*(1+1/ \<alpha>))"
        unfolding 3 by simp
      also have "... \<le> 1 * (2*(1+1/ \<alpha>))"
        unfolding \<alpha>_def by (intro mult_right_mono) auto
      also have "... \<le> ?R"
        unfolding \<alpha>_def by (approximation 10)
      finally show ?thesis by simp
    qed
  next
    case b
    have x_range: "x \<in> {0..1/4}"
      using assms b by simp
    then consider (1) "x = 0" | (2) "x = 1/4" | (3) "x \<in> {0<..<1/4}" by fastforce
    thus ?thesis 
    proof (cases)
      case 1
      hence y_eq: "y = 1/2" using b by simp
      show ?thesis using apx unfolding 1 y_eq \<phi>_def by (simp add:\<gamma>'_def \<alpha>_def frac_def) 
    next
      case 2
      hence y_eq: "y = 1/4" using b by simp
      show ?thesis using apx unfolding y_eq 2 \<phi>_def by (simp add:\<gamma>'_def frac_def)
    next
      case 3
      have "\<phi> x y = \<alpha> + 1"
        unfolding \<phi>_def b using 3
        by (intro arg_cong2[where f="(+)"] \<gamma>'_cases) (auto simp add:frac_expand) 
      moreover have "\<phi> y x = 1/\<alpha> + 1"
        unfolding \<phi>_def b using 3
        by (intro arg_cong2[where f="(+)"] \<gamma>'_cases) (auto simp add:frac_expand) 
      ultimately have "?T = cos (pi * x) * (\<alpha> + 1) + cos (pi * (1 / 2 - x)) * (1/\<alpha> + 1)"
        unfolding b by simp
      also have "... \<le> ?R"
        unfolding \<alpha>_def using x_range
        by (approximation 10 splitting: x=10)
      finally show ?thesis by simp
    qed
  next
    case c
    consider 
      (1) "x < y" "y < 1/2" | 
      (2) "y=1/2" "x < 1/2" | 
      (3) "y=x" "x < 1/2" | 
      (4) "x=1/2" "y =1/2"
      using assms(2,3) c  by fastforce
    thus ?thesis
    proof (cases)
      case 1
      define \<theta> :: real where "\<theta> = arcsin (6 / 10)"
      have "cos \<theta> = sqrt (1-0.6^2)"
        unfolding \<theta>_def by (intro cos_arcsin) auto
      also have "... = sqrt ( 0.8^2)"
        by (intro arg_cong[where f="sqrt"]) (simp add:power2_eq_square)
      also have "... = 0.8" by simp
      finally have cos_\<theta>: "cos \<theta> = 0.8" by simp
      have sin_\<theta>: "sin \<theta> = 0.6"
        unfolding \<theta>_def by simp

      have "\<phi> x y = \<alpha> + \<alpha>"
        unfolding \<phi>_def using c 1
        by (intro arg_cong2[where f="(+)"] \<gamma>'_cases) (auto simp add:frac_expand)
      moreover have "\<phi> y x = 1/\<alpha> + \<alpha>"
        unfolding \<phi>_def using c 1
        by (intro arg_cong2[where f="(+)"] \<gamma>'_cases) (auto simp add:frac_expand)
      ultimately have "?T = cos (pi * x) * (2 * \<alpha>) + cos (pi * y) * (\<alpha> + 1 / \<alpha>)"
        by simp
      also have "... \<le> cos (pi * (1/2-y)) * (2*\<alpha>) + cos (pi * y) * (\<alpha>+1 / \<alpha>)"
        unfolding \<alpha>_def using assms(1,2,3) c
        by (intro add_mono mult_right_mono order.refl iffD2[OF cos_mono_le_eq]) auto
      also have "... = (2.5*\<alpha>)* (sin (pi * y) * 0.8 + cos (pi * y) * 0.6)"
        unfolding sin_cos_eq \<alpha>_inv by (simp add:algebra_simps)
      also have "... = (2.5*\<alpha>)* sin(pi*y + \<theta>)"
        unfolding sin_add cos_\<theta> sin_\<theta>
        by (intro arg_cong2[where f="(*)"] arg_cong2[where f="(+)"] refl)
      also have "... \<le> (?R) * 1"
        unfolding \<alpha>_def by (intro mult_left_mono) auto
      finally show ?thesis by simp
    next
      case 2
      have x_range: "x > 0" "x < 1/2"
        using c 2 by auto
      have "\<phi> x y = \<alpha> + \<alpha>"
        unfolding \<phi>_def 2 using x_range
        by (intro arg_cong2[where f="(+)"] \<gamma>'_cases) (auto simp add:frac_expand)
      moreover have "\<phi> y x = 1 + 1"
        unfolding \<phi>_def 2 using x_range
        by (intro arg_cong2[where f="(+)"] \<gamma>'_cases) (auto simp add:frac_expand)
      ultimately have "?T = cos (pi * x) * (2*\<alpha>)"
        unfolding 2 by simp
      also have "... \<le> 1 * (2* sqrt 2)"
        unfolding \<alpha>_def by (intro mult_right_mono) auto
      also have "... \<le> ?R" 
        by (approximation 5)
      finally show ?thesis by simp
    next
      case 3
      have x_range: "x \<in> {1/4..1/2}" using 3 c by simp
      hence cos_bound: "cos (pi * x) \<le> 0.71"
        by (approximation 10)
      have "\<phi> x y = 1+\<alpha>"
        unfolding \<phi>_def 3 using 3 c
        by (intro arg_cong2[where f="(+)"] \<gamma>'_cases) (auto simp add:frac_expand)
      moreover have "\<phi> y x = 1+\<alpha>"
        unfolding \<phi>_def 3 using 3 c
        by (intro arg_cong2[where f="(+)"] \<gamma>'_cases) (auto simp add:frac_expand)
      ultimately have "?T = 2 * cos (pi * x) * (1+\<alpha>)"
        unfolding 3 by simp
      also have "... \<le> 2 * 0.71 * (1+sqrt 2)"
        unfolding \<alpha>_def by (intro mult_right_mono mult_left_mono cos_bound) auto
      also have "... \<le> ?R"
        by (approximation 6)
      finally show ?thesis by simp
    next 
      case 4
      show ?thesis  unfolding 4 by simp
    qed
  qed
  thus ?thesis using 0 by simp
qed

text \<open>Extend to square $[0, \frac{1}{2}] \times [0,\frac{1}{2}]$ using symmetry around x=y axis.\<close>

lemma fun_bound_real_2:
  assumes "x \<in> {0..1/2}" "y \<in> {0..1/2}" "(x,y) \<noteq> (0,0)"
  shows "\<bar>cos(pi*x)\<bar>*\<phi> x y + \<bar>cos(pi*y)\<bar>*\<phi> y x \<le> 2.5 * sqrt 2"  (is "?L \<le> ?R")
proof (cases "y < x")
  case True
  have "?L = \<bar>cos(pi*y)\<bar>*\<phi> y x + \<bar>cos(pi*x)\<bar>*\<phi> x y"
    by simp
  also have "... \<le> ?R"
    using True assms
    by (intro fun_bound_real_3)  auto
  finally show ?thesis by simp
next
  case False
  then show ?thesis using assms
    by (intro fun_bound_real_3) auto
qed

text \<open>Extend to $x > \frac{1}{2}$ using symmetry around $x=\frac{1}{2}$ axis.\<close>

lemma fun_bound_real_1:
  assumes "x \<in> {0..<1}" "y \<in> {0..1/2}" "(x,y) \<noteq> (0,0)"
  shows "\<bar>cos(pi*x)\<bar>*\<phi> x y + \<bar>cos(pi*y)\<bar>*\<phi> y x \<le> 2.5 * sqrt 2" (is "?L \<le> ?R")
proof (cases "x > 1/2")
  case True
  define x' where "x' = 1-x"

  have "\<bar>frac (x - 2 * y) - 1 / 2\<bar> = \<bar>frac (1 - x + 2 * y) - 1 / 2\<bar>"
  proof (cases "x - 2 * y \<in> \<int>")
    case True
    then obtain k where x_eq: "x = 2*y + of_int k" using Ints_cases[OF True] 
      by (metis add_minus_cancel uminus_add_conv_diff)
    show ?thesis unfolding x_eq frac_def by simp
  next
    case False
    hence "1 - x + 2 * y \<notin> \<int>" 
      using Ints_1 Ints_diff by fastforce
    thus ?thesis 
      by (intro abs_rev_cong) (auto intro:frac_cong simp:one_minus_frac)
  qed

  moreover have "\<bar>frac (x + 2 * y) - 1 / 2\<bar> = \<bar>frac (1 - x - 2 * y) - 1 / 2\<bar>" 
  proof (cases "x + 2 * y \<in> \<int>")
    case True
    then obtain k where x_eq: "x = of_int k - 2*y" using Ints_cases[OF True] 
      by (metis add.right_neutral add_diff_eq cancel_comm_monoid_add_class.diff_cancel)
    show ?thesis unfolding x_eq frac_def by simp
  next
    case False
    hence "1 - x - 2 * y \<notin> \<int>" 
      using Ints_1 Ints_diff by fastforce
    thus ?thesis 
      by (intro abs_rev_cong) (auto intro:frac_cong simp:one_minus_frac)
  qed
  ultimately have "\<phi> y x = \<phi> y x'" 
    unfolding \<phi>_def  x'_def by (intro \<gamma>'_cong add_swap_cong) simp_all 

  moreover have "\<phi> x y = \<phi> x' y"
    unfolding \<phi>_def x'_def  
    by (intro \<gamma>'_cong add_swap_cong refl arg_cong[where f="(\<lambda>x. abs (x-1/2))"] frac_cong) 
     (simp_all add:algebra_simps)

  moreover have "\<bar>cos(pi*x)\<bar> = \<bar>cos(pi*x')\<bar>"
    unfolding x'_def by (intro abs_rev_cong) (simp add:algebra_simps)

  ultimately have "?L = \<bar>cos(pi*x')\<bar>*\<phi> x' y + \<bar>cos(pi*y)\<bar>*\<phi> y x'"
    by simp
  also have "... \<le> ?R"
    using assms True by (intro fun_bound_real_2) (auto simp add:x'_def)
  finally show ?thesis by simp
next
  case False
  thus ?thesis using assms fun_bound_real_2 by simp 
qed

text \<open>Extend to $y > \frac{1}{2}$ using symmetry around $y=\frac{1}{2}$ axis.\<close>

lemma fun_bound_real:
  assumes "x \<in> {0..<1}" "y \<in> {0..<1}" "(x,y) \<noteq> (0,0)"
  shows "\<bar>cos(pi*x)\<bar>*\<phi> x y + \<bar>cos(pi*y)\<bar>*\<phi> y x \<le> 2.5 * sqrt 2"  (is "?L \<le> ?R")
proof (cases "y > 1/2")
  case True
  define y' where "y' = 1-y"

  have "\<bar>frac (y - 2 * x) - 1 / 2\<bar> = \<bar>frac (1 - y + 2 * x) - 1 / 2\<bar>"
  proof (cases "y - 2 * x \<in> \<int>")
    case True
    then obtain k where y_eq: "y = 2*x + of_int k" using Ints_cases[OF True] 
      by (metis add_minus_cancel uminus_add_conv_diff)
    show ?thesis unfolding y_eq frac_def by simp
  next
    case False
    hence "1 - y + 2 * x \<notin> \<int>" 
      using Ints_1 Ints_diff by fastforce
    thus ?thesis 
      by (intro abs_rev_cong) (auto intro:frac_cong simp:one_minus_frac)
  qed

  moreover have "\<bar>frac (y + 2 * x) - 1 / 2\<bar> = \<bar>frac (1 - y - 2 * x) - 1 / 2\<bar>" 
  proof (cases "y + 2 * x \<in> \<int>")
    case True
    then obtain k where y_eq: "y = of_int k - 2*x" using Ints_cases[OF True] 
      by (metis add.right_neutral add_diff_eq cancel_comm_monoid_add_class.diff_cancel)
    show ?thesis unfolding y_eq frac_def by simp
  next
    case False
    hence "1 - y - 2 * x \<notin> \<int>" 
      using Ints_1 Ints_diff by fastforce
    thus ?thesis 
      by (intro abs_rev_cong) (auto intro:frac_cong simp:one_minus_frac)
  qed
  ultimately have "\<phi> x y = \<phi> x y'" 
    unfolding \<phi>_def  y'_def  by (intro \<gamma>'_cong add_swap_cong) simp_all

  moreover have "\<phi> y x = \<phi> y' x"
    unfolding \<phi>_def y'_def  
    by (intro \<gamma>'_cong add_swap_cong refl arg_cong[where f="(\<lambda>x. abs (x-1/2))"] frac_cong) 
     (simp_all add:algebra_simps)

  moreover have "\<bar>cos(pi*y)\<bar> = \<bar>cos(pi*y')\<bar>"
    unfolding y'_def by (intro abs_rev_cong) (simp add:algebra_simps)

  ultimately have "?L = \<bar>cos(pi*x)\<bar>*\<phi> x y' + \<bar>cos(pi*y')\<bar>*\<phi> y' x"
    by simp
  also have "... \<le> ?R"
    using assms True by (intro fun_bound_real_1) (auto simp add:y'_def)
  finally show ?thesis by simp
next
  case False
  thus ?thesis using assms fun_bound_real_1 by simp 
qed

lemma mod_to_frac: 
  fixes x :: int
  shows "real_of_int (x mod m) = m * frac (x/m)" (is "?L = ?R")
proof -
  obtain y where y_def: "x mod m = x + int m* y"
    by (metis mod_eqE mod_mod_trivial) 

  have 0: "x mod int m < m" "x mod int m \<ge> 0"
    using m_gt_0 by auto

  have "?L = real m * (of_int (x mod m) / m )"
    using m_gt_0 by (simp add:algebra_simps)
  also have "... = real m * frac (of_int (x mod m) / m)"
    using 0 by (subst iffD2[OF frac_eq]) auto
  also have "... = real m * frac (x / m + y)"
    unfolding y_def using m_gt_0 by (simp add:divide_simps mult.commute)
  also have "... = ?R" 
    unfolding frac_def by simp
  finally show ?thesis by simp
qed

lemma fun_bound:
  assumes "v \<in> verts G" "v \<noteq> (0,0)"
  shows "\<tau>(fst v)*(\<gamma> v (S\<^sub>2 v)+\<gamma> v (T\<^sub>2 v))+\<tau>(snd v)*(\<gamma> v (S\<^sub>1 v)+\<gamma> v (T\<^sub>1 v)) \<le> 2.5 * sqrt 2" 
    (is "?L \<le> ?R")
proof -
  obtain x y where v_def: "v = (x,y)" by (cases v) auto
  define x' where "x' = x/real m"
  define y' where "y' = y/real m"

  have 0:"\<gamma> v (S\<^sub>1 v) = \<gamma>' x' (frac(x'-2*y'))"
    unfolding \<gamma>_def \<gamma>'_def compare_def v_def \<gamma>_aux_def T\<^sub>1_def S\<^sub>1_def x'_def y'_def using m_gt_0
    by (intro if_cong_direct refl) (auto simp add:case_prod_beta mod_to_frac divide_simps) 
  have 1:"\<gamma> v (T\<^sub>1 v) = \<gamma>' x' (frac(x'+2*y'))"
    unfolding \<gamma>_def \<gamma>'_def compare_def v_def \<gamma>_aux_def T\<^sub>1_def x'_def y'_def using m_gt_0
    by (intro if_cong_direct refl) (auto simp add:case_prod_beta mod_to_frac divide_simps) 
  have 2:"\<gamma> v (S\<^sub>2 v) = \<gamma>' y' (frac(y'-2*x'))"
    unfolding \<gamma>_def \<gamma>'_def compare_def v_def \<gamma>_aux_def S\<^sub>2_def x'_def y'_def using m_gt_0
    by (intro if_cong_direct refl) (auto simp add:case_prod_beta mod_to_frac divide_simps) 
  have 3:"\<gamma> v (T\<^sub>2 v) = \<gamma>' y' (frac(y'+2*x'))"
    unfolding \<gamma>_def \<gamma>'_def compare_def v_def \<gamma>_aux_def T\<^sub>2_def x'_def y'_def using m_gt_0
    by (intro if_cong_direct refl) (auto simp add:case_prod_beta mod_to_frac divide_simps) 
  have 4: "\<tau> (fst v)  = \<bar>cos(pi*x')\<bar>" "\<tau> (snd v)  = \<bar>cos(pi*y')\<bar>"
    unfolding \<tau>_def v_def x'_def y'_def by auto

  have "x \<in> {0..<int m}" "y \<in> {0..<int m}" "(x,y) \<noteq> (0,0)"
    using assms  unfolding v_def mgg_graph_def by auto
  hence 5:"x' \<in> {0..<1}" "y' \<in> {0..<1}" "(x',y') \<noteq> (0,0)" 
    unfolding x'_def y'_def by auto

  have "?L = \<bar>cos(pi*x')\<bar>*\<phi> x' y' + \<bar>cos(pi*y')\<bar>*\<phi> y' x'"
    unfolding 0 1 2 3 4 \<phi>_def by simp
  also have "... \<le> ?R"
    by (intro fun_bound_real 5) 
  finally show ?thesis by simp
qed

text \<open>Equation 15 in Proof of Theorem 8.8\<close>

lemma hoory_8_8:
  fixes f :: "int \<times> int \<Rightarrow> real"
  assumes "\<And>x. f x \<ge> 0"
  assumes "f (0,0) = 0"
  assumes "periodic f"
  shows "g_inner f (\<lambda>x. f(S\<^sub>2 x)*\<tau> (fst x)+f(S\<^sub>1 x)*\<tau> (snd x))\<le>1.25* sqrt 2*g_norm f^2"
    (is "?L \<le> ?R")
proof -
  have 0: "2 * f x * f y \<le> \<gamma> x y * f x^2 + \<gamma> y x * f y^2" (is "?L1 \<le> ?R1") for x y
  proof - 
    have "0 \<le> ((sqrt (\<gamma> x y) * f x) - (sqrt (\<gamma> y x) * f y))^2"
      by simp
    also have "... = ?R1 - 2 * (sqrt (\<gamma> x y) * f x) * (sqrt (\<gamma> y x) * f y)"
      unfolding power2_diff using \<gamma>_nonneg assms(1)
      by (intro arg_cong2[where f="(-)"] arg_cong2[where f="(+)"]) (auto simp add: power2_eq_square)
    also have "... = ?R1 -2 * sqrt (\<gamma> x y * \<gamma> y x) * f x * f y"
      unfolding real_sqrt_mult by simp
    also have "... = ?R1 - ?L1"
      unfolding \<gamma>_sym by simp
    finally have "0 \<le> ?R1 - ?L1" by simp
    thus ?thesis by simp
  qed

  have [simp]: "fst (S\<^sub>2 x) = fst x"  "snd (S\<^sub>1 x) = snd x" for x
    unfolding S\<^sub>1_def S\<^sub>2_def by auto

  have S_2_inv [simp]: "T\<^sub>2 (S\<^sub>2 x) = x" if "x \<in> verts G" for x
    using that unfolding T\<^sub>2_def S\<^sub>2_def mgg_graph_def 
    by (cases x,simp add:mod_simps)
  have S_1_inv [simp]: "T\<^sub>1 (S\<^sub>1 x) = x" if "x \<in> verts G" for x
    using that unfolding T\<^sub>1_def S\<^sub>1_def mgg_graph_def 
    by (cases x,simp add:mod_simps)

  have S2_inj: "inj_on S\<^sub>2 (verts G)"
    using S_2_inv by (intro inj_on_inverseI[where g="T\<^sub>2"])
  have S1_inj: "inj_on S\<^sub>1 (verts G)"
    using S_1_inv by (intro inj_on_inverseI[where g="T\<^sub>1"])

  have "S\<^sub>2 ` verts G \<subseteq> verts G"
    unfolding mgg_graph_def S\<^sub>2_def
    by (intro image_subsetI)  auto
  hence S2_ran: "S\<^sub>2 ` verts G = verts G" 
    by (intro card_subset_eq card_image S2_inj) auto

  have "S\<^sub>1 ` verts G \<subseteq> verts G"
    unfolding mgg_graph_def S\<^sub>1_def
    by (intro image_subsetI)  auto
  hence S1_ran: "S\<^sub>1 ` verts G = verts G"
    by (intro card_subset_eq card_image S1_inj) auto 

  have 2: "g v * f v^2 \<le> 2.5 * sqrt 2 * f v^2" if "g v \<le> 2.5 * sqrt 2 \<or> v = (0,0)" for v g
  proof (cases "v=(0,0)")
    case True
    then show ?thesis using assms(2) by simp
  next
    case False
    then show ?thesis using that by (intro mult_right_mono) auto
  qed

  have "2*?L=(\<Sum>v\<in>verts G. \<tau>(fst v)*(2*f v *f(S\<^sub>2 v)))+(\<Sum>v\<in>verts G. \<tau>(snd v) * (2 * f v * f (S\<^sub>1 v)))"
    unfolding g_inner_def by (simp add: algebra_simps sum_distrib_left sum.distrib)
  also have "... \<le>
    (\<Sum>v\<in>verts G. \<tau>(fst v)*(\<gamma> v (S\<^sub>2 v) * f v^2 + \<gamma> (S\<^sub>2 v) v * f(S\<^sub>2 v)^2))+
    (\<Sum>v\<in>verts G. \<tau>(snd v)*(\<gamma> v (S\<^sub>1 v) * f v^2 + \<gamma> (S\<^sub>1 v) v * f(S\<^sub>1 v)^2))"
    unfolding \<tau>_def by (intro add_mono sum_mono mult_left_mono 0) auto
  also have "... = 
    (\<Sum>v\<in>verts G. \<tau>(fst v)*\<gamma> v (S\<^sub>2 v)*f v^2)+(\<Sum>v\<in>verts G. \<tau>(fst v) * \<gamma> (S\<^sub>2 v) v * f(S\<^sub>2 v)^2)+
    (\<Sum>v\<in>verts G. \<tau>(snd v)*\<gamma> v (S\<^sub>1 v)*f v^2)+(\<Sum>v\<in>verts G. \<tau>(snd v) * \<gamma> (S\<^sub>1 v) v * f(S\<^sub>1 v)^2)"
    by (simp add:sum.distrib algebra_simps)
  also have "... = 
    (\<Sum>v\<in>verts G. \<tau>(fst v)*\<gamma> v (S\<^sub>2 v)*f v^2)+
    (\<Sum>v\<in>verts G. \<tau>(fst (S\<^sub>2 v)) * \<gamma> (S\<^sub>2 v) (T\<^sub>2 (S\<^sub>2 v)) * f(S\<^sub>2 v)^2)+
    (\<Sum>v\<in>verts G. \<tau>(snd v)*\<gamma> v (S\<^sub>1 v)*f v^2)+
    (\<Sum>v\<in>verts G. \<tau>(snd (S\<^sub>1 v)) * \<gamma> (S\<^sub>1 v) (T\<^sub>1 (S\<^sub>1 v)) * f(S\<^sub>1 v)^2)"
    by (intro arg_cong2[where f="(+)"] sum.cong refl) simp_all
  also have "... =
    (\<Sum>v\<in>verts G. \<tau>(fst v)*\<gamma> v (S\<^sub>2 v)*f v^2)+ (\<Sum>v\<in>S\<^sub>2 ` verts G. \<tau>(fst v) * \<gamma> v (T\<^sub>2 v) * f v^2)+
    (\<Sum>v\<in>verts G. \<tau>(snd v)*\<gamma> v (S\<^sub>1 v)*f v^2)+ (\<Sum>v\<in>S\<^sub>1 ` verts G. \<tau>(snd v) * \<gamma> v (T\<^sub>1 v) * f v^2)"
    using S1_inj S2_inj by (simp add:sum.reindex)
  also have "... = 
    (\<Sum>v\<in>verts G. (\<tau>(fst v)*(\<gamma> v (S\<^sub>2 v)+\<gamma> v (T\<^sub>2 v))+\<tau>(snd v)*(\<gamma> v (S\<^sub>1 v)+\<gamma> v (T\<^sub>1 v))) *f v^2)"
    unfolding S1_ran S2_ran by (simp add:algebra_simps sum.distrib)
  also have "... \<le> (\<Sum>v\<in>verts G. 2.5 * sqrt 2 * f v^2)"
    using fun_bound by (intro sum_mono 2) auto
  also have "... \<le>  2.5 * sqrt 2 * g_norm f^2" 
    unfolding g_norm_sq g_inner_def 
    by (simp add:algebra_simps power2_eq_square sum_distrib_left)
  finally have "2 * ?L \<le> 2.5 * sqrt 2 * g_norm f^2" by simp
  thus ?thesis by simp
qed

lemma hoory_8_7:
  fixes f :: "int\<times>int \<Rightarrow> complex"
  assumes "f (0,0) = 0"
  assumes "periodic f"
  shows "norm(g_inner f (\<lambda>x. f (S\<^sub>2 x) * (1+\<omega>\<^sub>F (fst x)) + f (S\<^sub>1 x) * (1+\<omega>\<^sub>F (snd x))))
    \<le> (2.5 * sqrt 2) * (\<Sum>v \<in> verts G. norm (f v)^2)" (is "?L \<le> ?R")
proof -
  define g :: "int\<times>int \<Rightarrow> real" where "g x = norm (f x)" for x

  have g_zero: "g (0,0) = 0"
    using assms(1) unfolding g_def by simp
  have g_nonneg: "g x \<ge> 0" for x
    unfolding g_def by simp
  have g_periodic: "periodic g"
    unfolding g_def by (intro periodic_comp[OF assms(2)])

  have 0: "norm(1+\<omega>\<^sub>F x) = 2*\<tau> x" for x :: int
  proof -
    have "norm(1+\<omega>\<^sub>F x) = norm(\<omega>\<^sub>F (-x/2)*(\<omega>\<^sub>F 0 + \<omega>\<^sub>F x))"
      unfolding \<omega>\<^sub>F_def norm_mult by simp
    also have "... = norm (\<omega>\<^sub>F (0-x/2) + \<omega>\<^sub>F (x-x/2))"
      unfolding \<omega>\<^sub>F_simps by (simp add: algebra_simps)
    also have "... = norm (\<omega>\<^sub>F (x/2) + cnj (\<omega>\<^sub>F (x/2)))"
      unfolding \<omega>\<^sub>F_simps(3) by (simp add:algebra_simps)
    also have "... = \<bar>2*Re (\<omega>\<^sub>F (x/2))\<bar>"
      unfolding complex_add_cnj norm_of_real by simp
    also have "... =  2*\<bar>cos(pi*x/m)\<bar>"
      unfolding \<omega>\<^sub>F_def cis.simps by simp
    also have "... = 2*\<tau> x" unfolding \<tau>_def by simp
    finally show ?thesis by simp
  qed

  have "?L\<le>norm(\<Sum>v\<in>verts G. f v * cnj(f(S\<^sub>2 v)*(1+\<omega>\<^sub>F (fst v))+f(S\<^sub>1 v )*(1+\<omega>\<^sub>F (snd v))))"
    unfolding g_inner_def by (simp add:case_prod_beta)
  also have "...\<le>(\<Sum>v\<in>verts G. norm(f v * cnj(f (S\<^sub>2 v) *(1+\<omega>\<^sub>F (fst v))+f (S\<^sub>1 v)*(1+\<omega>\<^sub>F (snd v)))))"
    by (intro norm_sum)
  also have "...=(\<Sum>v\<in>verts G. g v * norm(f (S\<^sub>2 v) *(1+\<omega>\<^sub>F (fst v))+f (S\<^sub>1 v)*(1+\<omega>\<^sub>F (snd v))))"
    unfolding norm_mult g_def complex_mod_cnj by simp
  also have "...\<le>(\<Sum>v\<in>verts G. g v * (norm (f(S\<^sub>2 v)*(1+\<omega>\<^sub>F (fst v)))+norm(f(S\<^sub>1 v)*(1+\<omega>\<^sub>F(snd v)))))"
    by (intro sum_mono norm_triangle_ineq mult_left_mono g_nonneg)
  also have "...=2*g_inner g (\<lambda>x. g (S\<^sub>2 x)*\<tau> (fst x)+g(S\<^sub>1 x)*\<tau> (snd x))"
    unfolding g_def g_inner_def norm_mult 0 
    by (simp add:sum_distrib_left algebra_simps case_prod_beta)
  also have "... \<le>2*(1.25* sqrt 2*g_norm g^2)"
    by (intro mult_left_mono hoory_8_8 g_nonneg g_zero g_periodic) auto
  also have "... = ?R"
    unfolding g_norm_sq g_def g_inner_def by (simp add:power2_eq_square)
  finally show ?thesis by simp
qed

lemma hoory_8_3:
  assumes "g_inner f (\<lambda>_. 1) = 0"
  assumes "periodic f"
  shows "\<bar>(\<Sum>(x,y)\<in>verts G. f(x,y)*(f(x+2*y,y)+f(x+2*y+1,y)+f(x,y+2*x)+f(x,y+2*x+1)))\<bar> 
    \<le> (2.5 * sqrt 2) * g_norm f^2" (is "\<bar>?L\<bar> \<le> ?R")
proof -
  let ?f = "(\<lambda>x. complex_of_real (f x))"

  define Ts :: "(int \<times> int \<Rightarrow> int \<times> int) list" where 
    "Ts = [(\<lambda>(x,y).(x+2*y,y)),(\<lambda>(x,y).(x+2*y+1,y)),(\<lambda>(x,y).(x,y+2*x)),(\<lambda>(x,y).(x,y+2*x+1))]"
  have p: "periodic ?f" 
    by (intro periodic_comp[OF assms(2)])

  have 0: "(\<Sum>T\<leftarrow>Ts. FT (?f\<circ>T) v) = FT ?f (S\<^sub>2 v)*(1+\<omega>\<^sub>F (fst v))+FT ?f (S\<^sub>1 v)*(1+\<omega>\<^sub>F (snd v))" 
    (is "?L1 = ?R1") for v :: "int \<times> int"
  proof -
    obtain x y where v_def: "v = (x,y)" by (cases v, auto)
    have "?L1 = (\<Sum>T\<leftarrow>Ts. FT (?f\<circ>T) (x,y))"
      unfolding v_def by simp
    also have "... = FT ?f (x,y-2*x)*(1+\<omega>\<^sub>F x) + FT ?f (x-2*y,y)*(1+\<omega>\<^sub>F y)"
      unfolding Ts_def by (simp add:FT_sheer[OF p] case_prod_beta comp_def) (simp add:algebra_simps)
    also have "... = ?R1"
      unfolding v_def S\<^sub>2_def S\<^sub>1_def
      by (intro arg_cong2[where f="(+)"] arg_cong2[where f="(*)"] periodic_cong[OF periodic_FT]) auto
    finally show ?thesis by simp
  qed

  have "cmod ((of_nat m)^2) = cmod (of_real (of_nat m^2))" by simp
  also have "... = abs (of_nat m^2)" by (intro norm_of_real)
  also have "... = real m^2" by simp
  finally have 1: "cmod ((of_nat m)\<^sup>2) = (real m)\<^sup>2" by simp

  have "FT (\<lambda>x. complex_of_real (f x)) (0, 0) = complex_of_real (g_inner f (\<lambda>_ . 1))"
    unfolding FT_def g_inner_def g_inner_def \<omega>\<^sub>F_def by simp
  also have "... = 0"
    unfolding assms by simp
  finally have 2: "FT (\<lambda>x. complex_of_real (f x)) (0, 0) = 0"
    by simp

  have "abs ?L = norm (complex_of_real ?L)" 
    unfolding norm_of_real by simp
  also have "... = norm (\<Sum>T \<leftarrow> Ts. (g_inner ?f (?f \<circ> T)))"
    unfolding Ts_def by (simp add:algebra_simps g_inner_def  sum.distrib comp_def case_prod_beta)
  also have "... = norm (\<Sum>T \<leftarrow> Ts. (g_inner (FT ?f) (FT (?f \<circ> T)))/m^2)" 
    by (subst parseval) simp
  also have "... = norm (g_inner (FT ?f) (\<lambda>x. (\<Sum>T \<leftarrow> Ts. (FT (?f \<circ> T) x)))/m^2)"
    unfolding Ts_def by (simp add:g_inner_simps case_prod_beta add_divide_distrib)
  also have "...=norm(g_inner(FT ?f)(\<lambda>x.(FT ?f(S\<^sub>2 x)*(1+\<omega>\<^sub>F (fst x))+FT f(S\<^sub>1 x)*(1+\<omega>\<^sub>F (snd x)))))/m^2"
    by (subst 0) (simp add:norm_divide 1)
  also have "... \<le> (2.5 * sqrt 2) * (\<Sum>v \<in> verts G. norm (FT f v)^2) / m^2"
    by (intro divide_right_mono hoory_8_7[where f="FT f"] 2 periodic_FT) auto 
  also have "... = (2.5 * sqrt 2) * (\<Sum>v \<in> verts G. cmod (f v)^2)"
    by (subst (2) plancharel) simp
  also have "... = (2.5 * sqrt 2) * (g_inner f f)"
    unfolding g_inner_def norm_of_real by (simp add: power2_eq_square)
  also have "... = ?R" 
    using g_norm_sq by auto
  finally show ?thesis by simp
qed

text \<open>Inequality stated before Theorem 8.3 in Hoory.\<close> 

lemma mgg_numerical_radius_aux:
  assumes "g_inner f (\<lambda>_. 1) = 0"
  shows "\<bar>(\<Sum>a \<in> arcs G. f (head G a) * f (tail G a))\<bar> \<le> (5 * sqrt 2) * g_norm f^2"  (is "?L \<le> ?R")
proof -
  define g where "g x = f (fst x mod m, snd x mod m)" for x :: "int \<times> int"
  have 0:"g x = f x" if "x \<in> verts G" for x 
    unfolding g_def using that
    by (auto simp add:mgg_graph_def mem_Times_iff)

  have g_mod_simps[simp]: "g (x, y mod m) = g (x, y)" "g (x mod m, y) = g (x, y)" for x y :: int
    unfolding g_def by auto

  have periodic_g: "periodic g"
    unfolding periodic_def by simp

  have "g_inner g (\<lambda>_. 1) = g_inner f (\<lambda>_. 1)"
    by (intro g_inner_cong 0) auto
  also have "... = 0"
    using assms by simp
  finally have 1:"g_inner g (\<lambda>_. 1) = 0" by simp

  have 2:"g_norm g = g_norm f"
    by (intro g_norm_cong 0) (auto)

  have "?L = \<bar>(\<Sum>a \<in> arcs G. g (head G a) * g (tail G a))\<bar>"
    using wellformed
    by (intro arg_cong[where f="abs"] sum.cong arg_cong2[where f="(*)"] 0[symmetric]) auto
  also have "...=\<bar>(\<Sum>a\<in>arcs_pos. g(head G a)*g(tail G a))+(\<Sum>a\<in>arcs_neg. g(head G a)*g(tail G a))\<bar>"
    unfolding arcs_sym arcs_pos_def arcs_neg_def
    by (intro arg_cong[where f="abs"] sum.union_disjoint) auto
  also have "... = \<bar>2 * (\<Sum>(v,l)\<in>verts G \<times> {..<4}. g v * g (mgg_graph_step m v (l, 1)))\<bar>"
    unfolding arcs_pos_def arcs_neg_def
    by (simp add:inj_on_def sum.reindex case_prod_beta mgg_graph_def algebra_simps)
  also have "... = 2 * \<bar>(\<Sum>v \<in> verts G. (\<Sum>l \<in> {..<4}. g v * g (mgg_graph_step m v (l, 1))))\<bar>"
    by (subst sum.cartesian_product)  (simp add:abs_mult)
  also have "... = 2*\<bar>(\<Sum>(x,y)\<in>verts G. (\<Sum>l\<leftarrow>[0..<4]. g(x,y)* g (mgg_graph_step m (x,y) (l,1))))\<bar>"
    by (subst interv_sum_list_conv_sum_set_nat)
      (auto simp add:atLeast0LessThan case_prod_beta simp del:mgg_graph_step.simps) 
  also have "... =2*\<bar>\<Sum>(x,y)\<in>verts G. g (x,y)* (g(x+2*y,y)+g(x+2*y+1,y)+g(x,y+2*x)+g(x,y+2*x+1))\<bar>"
    by (simp add:case_prod_beta numeral_eq_Suc algebra_simps) 
  also have "... \<le> 2* ((2.5 * sqrt 2) * g_norm g^2)"
    by (intro mult_left_mono hoory_8_3 1 periodic_g) auto
  also have "... \<le> ?R" unfolding 2 by simp
  finally show ?thesis by simp
qed

definition MGG_bound :: real
  where "MGG_bound = 5 * sqrt 2 / 8"

text \<open>Main result: Theorem 8.2 in Hoory.\<close> 

lemma mgg_numerical_radius: "\<Lambda>\<^sub>a \<le> MGG_bound"
proof -
  have "\<Lambda>\<^sub>a \<le> (5 * sqrt 2)/real d"
    by (intro expander_intro mgg_numerical_radius_aux) auto
  also have "... = MGG_bound"
    unfolding MGG_bound_def d_eq_8 by simp 
  finally show ?thesis by simp
qed

end

end