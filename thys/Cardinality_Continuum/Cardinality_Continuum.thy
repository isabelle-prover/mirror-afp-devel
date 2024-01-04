(*
  File:     Cardinality_Continuum/Cardinality_Continuum.thy
  Author:   Manuel Eberl (University of Innsbruck)

  The cardinality of the continuum, i.e. the real numbers, in a few different variations.
*)
section \<open>The Cardinality of the Continuum\<close>
theory Cardinality_Continuum
  imports Complex_Main Cardinality_Continuum_Library
begin

subsection \<open>$|\mathbb{R}| \leq |2^\mathbb{Q}|$ via Dedekind cuts\<close>

lemma le_cSup_iff:
  fixes A :: "'a :: conditionally_complete_linorder set"
  assumes "A \<noteq> {}" "bdd_above A"
  shows   "Sup A \<ge> c \<longleftrightarrow> (\<forall>x<c. \<exists>y\<in>A. y > x)"
  using assms by (meson less_cSup_iff not_le_imp_less order_less_irrefl order_less_le_trans)

text \<open>
  We show that the function mapping a real number to all the rational numbers below it is an
  injective map from the reals to $2^\mathbb{Q}$. This is the same idea that is used in
  the Dedekind cut definition of the reals.
\<close>
lemma inj_Dedekind_cut:
  fixes f :: "real \<Rightarrow> rat set"
  defines "f \<equiv> (\<lambda>x::real. {r::rat. of_rat r < x})"
  shows   "inj f"
proof
  fix x y :: real
  assume "f x = f y"

  have *: "Sup (real_of_rat ` {r. real_of_rat r < z}) = z" for z :: real
  proof -
    have "real_of_rat ` {r. real_of_rat r < z} = {r\<in>\<rat>. r < z}"
      by (auto elim!: Rats_cases)
    also have "Sup \<dots> = z"
    proof (rule antisym)
      have "{r \<in> \<rat>. r < z} \<noteq> {}"
        using Rats_no_bot_less less_eq_real_def by blast
      hence "Sup {r\<in>\<rat>. r < z} \<le> Sup {..z}"
        by (rule cSup_subset_mono) auto
      also have "\<dots> = z"
        by simp
      finally show "Sup {r\<in>\<rat>. r < z} \<le> z" .
    next
      show "Sup {r\<in>\<rat>. r < z} \<ge> z"
      proof (subst le_cSup_iff)
        show "{r\<in>\<rat>. r < z} \<noteq> {}"
          using Rats_no_bot_less less_eq_real_def by blast
        show "\<forall>y<z. \<exists>r\<in>{r\<in>\<rat>. r < z}. y < r"
          using Rats_dense_in_real by fastforce
        show "bdd_above {r \<in> \<rat>. r < z}"
          by (rule bdd_aboveI[of _ z]) auto
      qed
    qed
    finally show ?thesis .
  qed

  from \<open>f x = f y\<close> have "Sup (real_of_rat ` f x) = Sup (real_of_rat ` f y)"
    by simp
  thus "x = y"
    by (simp only: * f_def)
qed


subsection \<open>$2^{|\mathbb{N}|} \leq |\mathbb{R}|$ via ternary fractions\<close>

text \<open>
  For the other direction, we construct an injective function that maps a set of natural numbers
  \<open>A\<close> to a real number by constructing a ternary decimal number of the form
  $d_0. d_1 d_2 d_3 \ldots$ where $d_m$ is 1 if \<open>m \<in> A\<close> and 0 otherwise.

  We will first show a few more general results about such \<open>n\<close>-ary fraction expansions.
\<close>

lemma geometric_sums':
  fixes c :: "'a :: real_normed_field"
  assumes "norm c < 1"
  shows   "(\<lambda>n. c ^ (n + m)) sums (c ^ m / (1 - c))"
proof -
  have "(\<lambda>n. c ^ m * c ^ n) sums (c ^ m * (1 / (1 - c)))"
    by (intro sums_mult geometric_sums assms)
  thus ?thesis
    by (simp add: power_add field_simps)
qed

lemma summable_nary_fraction:
  fixes d :: real and f :: "nat \<Rightarrow> real"
  assumes "\<And>n. norm (f n) \<le> c" "d > 1"
  shows   "summable (\<lambda>n. f n / d ^ n)"
proof (rule summable_comparison_test)
  show "\<exists>N. \<forall>n\<ge>N. norm (f n / d ^ n :: real) \<le> c * (1 / d) ^ n"
    using assms by (intro exI[of _ 0]) (auto simp: field_simps)
  show "summable (\<lambda>n. c * (1 / d) ^ n :: real)"
    using assms by (intro summable_mult summable_geometric) auto
qed    

text \<open>
  Consider two \<open>n\<close>-ary fraction expansions $u = u_1. u_2 u_3 \ldots$ and
  $v = v_1. v_2 v_3 \ldots$ with \<open>n \<ge> 2\<close>.
  Suppose that all the $u_i$ and $v_i$ are between 0 and \<open>n - 2\<close> (i.e. the highest digit
  does not occur).
  Then \<open>u\<close> and \<open>v\<close> are equal if and only if all $u_i = v_i$ for all \<open>i\<close>.

  Note that without the additional restriction the result does not hold, as e.g.
  the decimal numbers $0.2$ and $0.1\overline{9}$ are equal.

  The reasoning boils down to showing that if \<open>m\<close> is the smallest index where the two sequences
  differ, then $|u-v| \geq \frac{1}{d-1} > 0$.
\<close>
lemma nary_fraction_unique:
  fixes u v :: "nat \<Rightarrow> nat"
  assumes f_eq: "(\<Sum>n. real (u n) / real d ^ n) = (\<Sum>n. real (v n) / real d ^ n)"
  assumes uv: "\<And>n. u n \<le> d - 2" "\<And>n. v n \<le> d - 2" and d: "d \<ge> 2"
  shows   "u = v"
proof -
  define f :: "(nat \<Rightarrow> nat) \<Rightarrow> real" where
    "f = (\<lambda>u. \<Sum>n. real (u n) / real d ^ n)"

  have "u m = v m" for m
  proof (induction m rule: less_induct)
    case (less m)
    show "u m = v m"
    proof (rule ccontr)
      assume "u m \<noteq> v m"

      show False
        using \<open>u m \<noteq> v m\<close> uv less.IH f_eq
      proof (induction "u m" "v m" arbitrary: u v rule: linorder_wlog)
        case (sym u v)
        from sym(1)[of v u] sym(2-) show ?case
          by (simp add: eq_commute)
      next
        case (le u v)
        have uv': "real (u n) \<le> real d - 2" "real (v n) \<le> real d - 2" for n
          by (metis d of_nat_diff of_nat_le_iff of_nat_numeral le(3,4))+
        have "f u - f v - (real (u m) - real (v m)) / real d ^ m \<le> 
                (real d - 2) * ((1 / real d) ^ m / (real d - 1))"
        proof (rule sums_le)
          have "(\<lambda>n. (real (u n) - real (v n)) / real d ^ n) sums (f u - f v)"
            unfolding diff_divide_distrib f_def using le d uv'
            by (intro sums_diff summable_sums summable_nary_fraction[where c = "real d - 2"]) auto
          hence "(\<lambda>n. (real (u (n + m)) - real (v (n + m))) / real d ^ (n + m)) sums
                   (f u - f v - (\<Sum>n<m. (real (u n) - real (v n)) / real d ^ n))"
            by (rule sums_split_initial_segment)
          also have "(\<Sum>n<m. (real (u n) - real (v n)) / real d ^ n) = 0"
            by (intro sum.neutral) (use le in auto)
          finally have "(\<lambda>n. (real (u (n + m)) - real (v (n + m))) / real d ^ (n + m)) sums (f u - f v)"
            by simp
          thus "(\<lambda>n. (real (u (Suc n + m)) - real (v (Suc n + m))) / real d ^ (Suc n + m)) sums
                   (f u - f v - (real (u m) - real (v m)) / real d ^ m)"
            by (subst sums_Suc_iff) auto
        next
          have "(\<lambda>n. (real d - 2) * ((1 / real d) ^ (n + Suc m))) sums
                  ((real d - 2) * ((1 / real d) ^ Suc m / (1 - 1 / real d)))"
            using d by (intro sums_mult geometric_sums') auto
          thus "(\<lambda>n. (real d - 2) * ((1 / real d) ^ (n + Suc m))) sums
                  ((real d - 2) * ((1 / real d) ^ m / (real d - 1)) :: real)"
            using d by (simp add: sums_iff field_simps)
        next
          fix n :: nat
          have "(real (u (Suc n + m)) - real (v (Suc n + m))) / real d ^ (Suc n + m) \<le>
                  ((real d - 2) - 0) / real d ^ (Suc n + m)"
            using uv' by (intro divide_right_mono diff_mono) auto
          thus "(real (u (Suc n + m)) - real (v (Suc n + m))) / real d ^ (Suc n + m) \<le>
                  (real d - 2) * (1 / real d) ^ (n + Suc m)"
            by (simp add: field_simps)
        qed
        hence "f u - f v \<le>
                 (real d - 2) / (real d - 1) / real d ^ m + (real (u m) - real (v m)) / real d ^ m"
          by (simp add: field_simps)
        also have "\<dots> = ((real d - 2) / (real d - 1) + real (u m) - real (v m)) / real d ^ m"
          by (simp add: add_divide_distrib diff_divide_distrib)
        also have "\<dots> = ((real d - 2) / (real d - 1) + real_of_int (int (u m) - int (v m))) / real d ^ m"
          using \<open>u m \<le> v m\<close> by simp
        also have "\<dots> \<le> ((real d - 2) / (real d - 1) + -1) / real d ^ m"
          using le d by (intro divide_right_mono add_mono) auto
        also have "(real d - 2) / (real d - 1) + -1 = -1 / (real d - 1)"
          using d by (simp add: field_simps)
        also have "\<dots> < 0"
          using d by (simp add: field_simps)
        finally have "f u - f v < 0"
          using d by (simp add: field_simps)
        with le show False
          by (simp add: f_def)
      qed
    qed
  qed
  thus ?thesis
    by blast
qed

text \<open>
  It now follows straightforwardly that mapping sets of natural numbers to ternary fraction
  expansions is indeed injective. For binary fractions, this would not work due to the
  aforementioned issue.
\<close>
lemma inj_nat_set_to_ternary:
  fixes f :: "nat set \<Rightarrow> real"
  defines "f \<equiv> (\<lambda>A. \<Sum>n. (if n \<in> A then 1 else 0) / 3 ^ n)"
  shows   "inj f"
proof
  fix A B :: "nat set"
  assume "f A = f B"
  have "(\<lambda>n. if n \<in> A then 1 else 0 :: nat) = (\<lambda>n. if n \<in> B then 1 else 0 :: nat)"
  proof (rule nary_fraction_unique)
    have *: "(\<Sum>n. (if n \<in> A then 1 else 0) / 3 ^ n) =
             (\<Sum>n. real (if n \<in> A then 1 else 0) / real 3 ^ n)"
      for A by (intro suminf_cong) auto
    show "(\<Sum>n. real (if n \<in> A then 1 else 0) / real 3 ^ n) =
           (\<Sum>n. real (if n \<in> B then 1 else 0) / real 3 ^ n)"
      using \<open>f A = f B\<close> by (simp add: f_def *)
  qed auto
  thus "A = B"
    by (metis equalityI subsetI zero_neq_one)
qed


subsection \<open>Equipollence proof\<close>

theorem eqpoll_UNIV_real: "(UNIV :: real set) \<approx> (UNIV :: nat set set)"
proof (rule lepoll_antisym)
  show "(UNIV :: nat set set) \<lesssim> (UNIV :: real set)"
    unfolding lepoll_def using inj_nat_set_to_ternary by blast
next
  have "(UNIV :: real set) \<lesssim> (UNIV :: rat set set)"
    unfolding lepoll_def using inj_Dedekind_cut by blast
  also have "\<dots> = Pow (UNIV :: rat set)"
    by simp
  also have "\<dots> \<approx> Pow (UNIV :: nat set)"
    by (rule eqpoll_Pow) (auto simp: infinite_UNIV_char_0 eqpoll_UNIV_nat_iff)
  also have "\<dots> = (UNIV :: nat set set)"
    by simp
  finally show "(UNIV :: real set) \<lesssim> (UNIV :: nat set set)" .
qed

text \<open>
  We can also write the language in the language of cardinal numbers as
  $|\mathbb{R}| = 2^{\aleph_0}$ using Isabelle's cardinal number library:
\<close>
corollary card_of_UNIV_real: "|UNIV :: real set| =o ctwo ^c natLeq"
proof -
  have "|UNIV :: real set| =o |UNIV :: nat set set|"
    using eqpoll_UNIV_real by (simp add: eqpoll_iff_card_of_ordIso)
  also have "|UNIV :: nat set set| =o cpow |UNIV :: nat set|"
    by (simp add: cpow_def)
  also have "cpow |UNIV :: nat set| =o ctwo ^c |UNIV :: nat set|"
    by (rule cpow_cexp_ctwo)
  also have "ctwo ^c |UNIV :: nat set| =o ctwo ^c natLeq"
    by (intro cexp_cong2) (simp_all add: card_of_nat Card_order_ctwo)
  finally show ?thesis .
qed


subsection \<open>Corollaries for real intervals\<close>

text \<open>
  It is easy to show that any real interval (whether open, closed, or infinite) is equipollent
  to the full set of real numbers.
\<close>
lemma eqpoll_Ioo_real:
  fixes a b :: real
  assumes "a < b"
  shows   "{a<..<b} \<approx> (UNIV :: real set)"
proof -
  have Ioo: "{a<..<b} \<approx> {0::real<..<1}" if "a < b" for a b :: real
  proof -
    have "bij_betw (\<lambda>x. x * (b - a) + a) {0<..<1} {a<..<b}"
    proof (rule bij_betwI[of _ _ _ "\<lambda>y. (y - a) / (b - a)"], goal_cases)
      case 1
      show ?case
      proof
        fix x :: real assume x: "x \<in> {0<..<1}"
        have "x * (b - a) + a > 0 + a"
          using x \<open>a < b\<close> by (intro add_strict_right_mono mult_pos_pos) auto
        moreover have "x * (b - a) + a < 1 * (b - a) + a"
          using x \<open>a < b\<close> by (intro add_strict_right_mono mult_strict_right_mono) auto
        ultimately show "x * (b - a) + a \<in> {a<..<b}"
          by simp
      qed
    qed (use \<open>a < b\<close> in \<open>auto simp: field_simps\<close>)
    thus ?thesis
      using eqpoll_def eqpoll_sym by blast
  qed

  have "{a<..<b} \<approx> {-pi/2<..<pi/2}"
    using eqpoll_trans[OF Ioo[of a b] eqpoll_sym[OF Ioo[of "-pi/2" "pi/2"]]] assms
    by simp
  also have "bij_betw tan {-pi/2<..<pi/2} (UNIV :: real set)"
    by (rule bij_betwI[of _ _ _ arctan]) 
       (use arctan_lbound arctan_ubound in \<open>auto simp: arctan_tan tan_arctan\<close>)
  hence "{-pi/2<..<pi/2} \<approx> (UNIV :: real set)"
    using eqpoll_def by blast
  finally show ?thesis .
qed

lemma eqpoll_real: 
  assumes "{a::real<..<b} \<subseteq> X" "a < b"
  shows   "X \<approx> (UNIV :: real set)"
  using eqpoll_Ioo_real[OF assms(2)] assms(1)
  by (meson eqpoll_sym lepoll_antisym lepoll_trans1 subset_UNIV subset_imp_lepoll)
  
lemma eqpoll_Icc_real: "(a::real) < b \<Longrightarrow> {a..b} \<approx> (UNIV :: real set)"
  and eqpoll_Ioc_real: "(a::real) < b \<Longrightarrow> {a<..b} \<approx> (UNIV :: real set)"
  and eqpoll_Ico_real: "(a::real) < b \<Longrightarrow> {a..<b} \<approx> (UNIV :: real set)"
  by (rule eqpoll_real[of a b]; force)+

lemma eqpoll_Ici_real: "{a::real..} \<approx> (UNIV :: real set)"
  and eqpoll_Ioi_real: "{a::real<..} \<approx> (UNIV :: real set)"
  by (rule eqpoll_real[of a "a + 1"]; force)+

lemma eqpoll_Iic_real: "{..a::real} \<approx> (UNIV :: real set)"
  and eqpoll_Iio_real: "{..<a::real} \<approx> (UNIV :: real set)"
  by (rule eqpoll_real[of "a - 1" a]; force)+

lemmas eqpoll_real_ivl =
  eqpoll_Ioo_real eqpoll_Ioc_real eqpoll_Ico_real eqpoll_Icc_real
  eqpoll_Iio_real eqpoll_Iic_real eqpoll_Ici_real eqpoll_Ioi_real

lemmas card_of_ivl_real = 
  eqpoll_real_ivl[THEN eqpoll_imp_card_of_ordIso, THEN ordIso_transitive[OF _ card_of_UNIV_real]]


subsection \<open>Corollaries for vector spaces\<close>

text \<open>
  We will now also show some results about the cardinality of vector spaces. To do this,
  we use the obvious isomorphism between a vector space \<open>V\<close> with a basis \<open>B\<close> and the set of 
  finite-support functions \<open>B \<rightarrow> V\<close>.
\<close>
lemma (in vector_space) card_of_span:
  assumes "independent B"
  shows   "|span B| =o |Func_finsupp 0 B (UNIV :: 'a set)|"
proof -
  define f :: "('b \<Rightarrow> 'a) \<Rightarrow> 'b" where "f = (\<lambda>g. \<Sum>b | g b \<noteq> 0. scale (g b) b)"
  define g :: "'b \<Rightarrow> 'b \<Rightarrow> 'a" where "g = representation B"
  have "bij_betw g (span B) (Func_finsupp 0 B UNIV)"
  proof (rule bij_betwI[of _ _ _ f], goal_cases)
    case 1
    thus ?case
      by (auto simp: g_def Func_finsupp_def finite_representation intro: representation_ne_zero)
  next
    case 2
    thus ?case
      by (auto simp: f_def Func_finsupp_def intro!: span_sum span_scale intro: span_base)
  next
    case (3 x)
    show "f (g x) = x" unfolding g_def f_def
      by (intro sum_nonzero_representation_eq) (use 3 assms in auto)
  next
    case (4 v)
    show "g (f v) = v" unfolding g_def using 4
      by (intro representation_eqI)
         (auto simp: assms f_def Func_finsupp_def intro: span_base
               intro!: sum.cong span_sum span_scale split: if_splits)
  qed
  thus "|span B| =o |Func_finsupp 0 B (UNIV :: 'a set)|"
    by (simp add: card_of_ordIsoI)
qed

text \<open>
  We can now easily show the following: Let \<open>K\<close> be an infinite field and $V$ a non-trivial
  finite-dimensional \<open>K\<close>-vector space. Then \<open>|V| = |K|\<close>.
\<close>
lemma (in vector_space) card_of_span_finite_dim_infinite_field:
  assumes "independent B" and "finite B" and "B \<noteq> {}" and "infinite (UNIV :: 'a set)"
  shows   "|span B| =o |UNIV :: 'a set|"
proof -
  have "|span B| =o |Func_finsupp 0 B (UNIV :: 'a set)|"
    by (rule card_of_span) fact
  also have "|Func_finsupp 0 B (UNIV :: 'a set)| =o cmax |B| |UNIV :: 'a set|"
  proof (rule card_of_Func_finsupp_infinite)
    show "UNIV - {0 :: 'a} \<noteq> {}"
      using assms by (metis finite.emptyI infinite_remove)
  qed (use assms in auto)
  also have "cmax |B| |UNIV :: 'a set| =o |UNIV :: 'a set|"
    using assms by (intro cmax2 ordLeq3_finite_infinite) auto
  finally show ?thesis .
qed

text \<open>
  Similarly, we can show the following: Let \<open>V\<close> be an infinite-dimensional vector space \<open>V\<close> over 
  some (not necessarily infinite) field \<open>K\<close>. Then $|V| = \text{max}(\text{dim}_K(V), |K|)$.
\<close>
lemma (in vector_space) card_of_span_infinite_dim_infinite_field:
  assumes "independent B" "infinite B"
  shows   "|span B| =o cmax |B| |UNIV :: 'a set|"
proof -
  have "|span B| =o |Func_finsupp 0 B (UNIV :: 'a set)|"
    by (rule card_of_span) fact
  also have "|Func_finsupp 0 B (UNIV :: 'a set)| =o cmax |B| |UNIV :: 'a set|"
  proof (rule card_of_Func_finsupp_infinite)
    have "(1 :: 'a) \<in> UNIV" "(1 :: 'a) \<noteq> 0"
      by auto
    thus "UNIV - {0 :: 'a} \<noteq> {}"
      by blast
  qed (use assms in auto)
  finally show "|span B| =o cmax |B| |UNIV :: 'a set|" .
qed

end