theory DigitsInBase
  imports "HOL-Computational_Algebra.Computational_Algebra" "HOL-Number_Theory.Number_Theory"
begin

section\<open>Infinite sums\<close>
text\<open>In this section, it is shown that an infinite series \emph{of natural numbers} converges if
and only if its terms are eventually zero. Additionally, the notion of a summation starting from an
index other than zero is defined. A few obvious lemmas about these notions are established.\<close>

definition eventually_zero :: "(nat \<Rightarrow> _) \<Rightarrow> bool" where
"eventually_zero (D :: nat \<Rightarrow> _) \<longleftrightarrow> (\<forall>\<^sub>\<infinity> n. D n = 0)"

lemma eventually_zero_char:
  shows "eventually_zero D \<longleftrightarrow> (\<exists>s. \<forall>i\<ge>s. D i = 0)"
  unfolding eventually_zero_def
  using MOST_nat_le .

text\<open>There's a lot of commonality between this setup and univariate polynomials, but drawing out
the similarities and proving them is beyond the scope of the current version of this theory except
for the following lemma.\<close>
lemma eventually_zero_poly:
  shows "eventually_zero D \<longleftrightarrow> D = poly.coeff (Abs_poly D)"
  by (metis Abs_poly_inverse MOST_coeff_eq_0 eventually_zero_def mem_Collect_eq)

lemma eventually_zero_imp_summable [simp]:
  assumes "eventually_zero D"
  shows "summable D"
  using summable_finite assms eventually_zero_char
  by (metis (mono_tags) atMost_iff finite_atMost nat_le_linear)

lemma summable_bounded:
  fixes my_seq :: "nat \<Rightarrow> nat" and n :: nat
  assumes "\<And> i . i \<ge> n \<longrightarrow> my_seq i = 0"
  shows "summable my_seq"
  using assms eventually_zero_char eventually_zero_imp_summable by blast

lemma sum_bounded:
  fixes my_seq :: "nat \<Rightarrow> nat" and n :: nat
  assumes "\<And> i . i \<ge> n \<longrightarrow> my_seq i = 0"
  shows "(\<Sum>i. my_seq i) = (\<Sum>i<n. my_seq i)"
  by (meson assms finite_lessThan lessThan_iff linorder_not_le suminf_finite)  

lemma product_seq_eventually_zero:
  fixes seq1 seq2 :: "nat \<Rightarrow> nat"
  assumes "eventually_zero seq1"
  shows "eventually_zero (\<lambda> i. seq1 i * seq2 i)"
  using mult_0 eventually_zero_char
  by (metis (no_types, lifting) assms)

abbreviation upper_sum
  where "upper_sum seq n \<equiv> \<Sum>i. seq (i + n)"
syntax
  "_from_sum" :: "idt \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b"  ("(3\<Sum>_\<ge>_./ _)" [0,0,10] 10)
translations
  "\<Sum>i\<ge>n. t" == "CONST upper_sum (\<lambda>i. t) n"

text \<open>The following two statements are proved as a sanity check. They are not intended to be used
anywhere.\<close>
corollary
  fixes seq :: "nat \<Rightarrow> nat" and a :: nat
  assumes seq_def: "\<And> i. seq i = (if i = 0 then a else 0)"
  shows "(\<Sum>i\<ge>0. seq i) = upper_sum (\<lambda> i. seq i) 0"
  by simp

corollary
  fixes seq :: "nat \<Rightarrow> nat" and a :: nat
  assumes seq_def: "\<And> i. seq i = (if i = 0 then a else 0)"
  shows "(\<Sum>i\<ge>0. seq i) = a"
  by (smt (verit) group_cancel.rule0 lessI lessThan_0 linorder_not_less seq_def sum.empty
      sum.lessThan_Suc_shift sum_bounded)

lemma bounded_sum_from:
  fixes seq :: "nat \<Rightarrow> nat" and n s :: nat
  assumes "\<forall>i>s. seq i = 0" and "n \<le> s"
  shows "(\<Sum>i\<ge>n. seq i) = (\<Sum>i=n..s. seq i)"
proof -  
  have "\<And>i. i > (s - n) \<Longrightarrow> seq (i + n) = 0"
    using assms by (meson less_diff_conv2)
  then have "(\<Sum>i\<ge>n. seq i) = (\<Sum>i\<le>s-n. seq (i + n))"
    by (meson atMost_iff finite_atMost leI suminf_finite)
  also have "\<dots> = (\<Sum>i=n..s. seq i)"
  proof -
    have "\<And>na. (\<Sum>na\<le>na. seq (na + n)) = sum seq {0 + n..na + n}"
      by (metis (no_types) atLeast0AtMost sum.shift_bounds_cl_nat_ivl)
    then show ?thesis
      by (simp add: assms(2))
  qed
  finally show ?thesis .
qed

lemma split_suminf:
  fixes seq :: "nat \<Rightarrow> nat" and n :: nat
  assumes "eventually_zero seq"
  shows "(\<Sum>i. seq i) = (\<Sum>i<n. seq i) + (\<Sum>i\<ge>n. seq i)"
proof -
  obtain s where s: "\<And>i. i\<ge>s \<longrightarrow> seq i = 0"
    using assms unfolding eventually_zero_char by presburger
  then have sum_s: "(\<Sum>i. seq i) = (\<Sum>i<s. seq i)"
    using sum_bounded by presburger
  show "(\<Sum>i. seq i) = (\<Sum>i<n. seq i) + (\<Sum>i\<ge>(n). seq i)"
  proof (cases "n \<ge> s")
    case True
    then have "(\<Sum>i\<ge>(n). seq i) = 0"
      using s by force
    moreover have "(\<Sum>i<n. seq i) = (\<Sum>i<s. seq i)"
      by (metis True dual_order.trans s sum_bounded sum_s)
    ultimately show ?thesis using sum_s by simp
  next
    case False
    have 0: "(\<Sum>i=n..s. seq i) = (\<Sum>i\<ge>n. seq i)"
      by (metis False bounded_sum_from le_eq_less_or_eq nle_le s)
    from False have "n \<le> s"
      by simp
    then have "(\<Sum>i<s. seq i) = (\<Sum>i<n. seq i) + (\<Sum>i=n..s. seq i)"
      by (metis add_cancel_left_right nat_le_iff_add s sum.atLeastLessThan_concat add_0 
          lessThan_atLeast0 sum.last_plus)
    then show ?thesis using 0 sum_s
      by presburger
  qed
qed

lemma dvd_suminf:
  fixes seq :: "nat \<Rightarrow> nat" and b :: nat
  assumes "eventually_zero seq" and "\<And>i. b dvd seq i"
  shows "b dvd (\<Sum>i. seq i)"
proof -
  obtain s::nat where s: "i \<ge> s \<Longrightarrow> seq i = 0" for i
    using assms(1) eventually_zero_char by blast
  then have "(\<Sum>i. seq i) = (\<Sum>i<s. seq i)"
    using sum_bounded by blast
  moreover have "b dvd (\<Sum>i<s. seq i)"
    using assms(2) by (simp add: dvd_sum)
  ultimately show ?thesis by presburger
qed

lemma eventually_zero_shifted:
  assumes "eventually_zero seq"
  shows "eventually_zero (\<lambda> i. seq (i + n))"
  by (meson assms eventually_zero_char trans_le_add1)

section\<open>Modular arithmetic\<close>
text\<open>This section establishes a number of lemmas about modular arithmetic, including that modular
division distributes over an ``infinite'' sum whose terms are eventually zero.\<close>

lemma pmod_int_char:
  fixes a b d :: int
  shows "[a = b] (mod d) \<longleftrightarrow> (\<exists>(n::int). a = b + n*d)"
  by (metis cong_iff_lin cong_sym mult.commute)

lemma equiv_conj_if:
  assumes "P \<Longrightarrow> Q" and "P \<Longrightarrow> R" and "Q \<Longrightarrow> R \<Longrightarrow> P"
  shows "P \<longleftrightarrow> Q \<and> R"
  using assms by auto

lemma mod_successor_char:
  fixes k k' i b :: nat
  assumes "(b::nat) \<ge> 2"
  shows "[k = k'] (mod b^(Suc i)) \<longleftrightarrow> [k div b^i = k' div b^i] (mod b) \<and> [k = k'] (mod b^i)"
proof (rule equiv_conj_if)
  assume kk'_cong: "[k = k'] (mod b ^ Suc i)"
  then show "[k div b^i = k' div b^i] (mod b)"
    by (smt (verit, ccfv_SIG) Groups.mult_ac(2) add_diff_cancel_right' cong_def div_mult_mod_eq
        mod_mult2_eq mod_mult_self4 mult_cancel1 power_Suc2)
  from kk'_cong show "[k = k'] (mod b ^ i)"
    using Cong.cong_dvd_modulus_nat
    by (meson Suc_n_not_le_n le_imp_power_dvd nat_le_linear)
next
  assume "[k div b^i = k' div b^i] (mod b)"
  moreover assume "[k = k'] (mod b^i)"
  ultimately show "[k = k'] (mod b ^ Suc i)"
    by (metis (mono_tags, lifting) cong_def mod_mult2_eq power_Suc2)
qed

lemma mod_1:
  fixes k k' b :: nat
  shows "[k = k'] (mod b^0)"
  by simp

lemma mod_distributes:
  fixes seq :: "nat \<Rightarrow> nat" and b :: nat
  assumes "\<exists>n. \<forall>i\<ge>n. seq i = 0"
  shows "[(\<Sum>i. seq i) = (\<Sum>i. seq i mod b)] (mod b)"
proof -
  obtain n where n: "\<And>i. i\<ge>n \<longrightarrow> seq i = 0"
    using assms by presburger
  from n have "(\<Sum>i. seq i) = (\<Sum>i<n. seq i)"
    using sum_bounded by presburger
  moreover from n have "(\<Sum>i. seq i mod b) = (\<Sum>i<n. seq i mod b)"
    using sum_bounded by presburger
  ultimately show ?thesis
    unfolding cong_def
    by (metis mod_sum_eq)
qed

lemma another_mod_cancellation_int:
  fixes a b c d m :: int
  assumes "d > 0" and "[m = a + b] (mod c * d)" and "a div d = 0" and "d dvd b"
  shows "[m div d = b div d] (mod c)"
proof (subst pmod_int_char)
  obtain k::int where k: "m = a + b + k*c*d"
    using pmod_int_char assms(2) by (metis mult.assoc)
  have "d dvd (b + k*c*d)" using \<open>d dvd b\<close>
    by simp
  from k have "m div d = (a + b + k*c*d) div d"
    by presburger
  also have "\<dots> = (b + k*c*d) div d"
    using \<open>a div d = 0\<close> \<open>d dvd (b + k*c*d)\<close>
    by fastforce
  also have "\<dots> = (b div d) + k*c"
    using \<open>d dvd b\<close> \<open>d > 0\<close> by auto
  finally show "\<exists>n. m div d = b div d + n * c"
    by blast
qed

lemma another_mod_cancellation:
  fixes a b c d m :: nat
  assumes "d > 0" and "[m = a + b] (mod c * d)" and "a div d = 0" and "d dvd b"
  shows "[m div d = b div d] (mod c)"
  by (smt (verit) another_mod_cancellation_int assms cong_int_iff of_nat_0 of_nat_0_less_iff
      of_nat_add of_nat_dvd_iff of_nat_mult zdiv_int)

section\<open>Digits as sequence\<close>
text\<open>Rules are introduced for computing the $i^{\text{th}}$ digit of a base-$b$ representation
and the number of digits required to represent a given number. (The latter is essentially an integer
version of the base-$b$ logarithm.) It is shown that the sum of the terms $d_i b^i$ converges to
$m$ if $d_i$ is the $i^{\text{th}}$ digit $m$. It is shown that the sequence of digits defined is
the unique sequence of digits less than $b$ with this property 

Additionally, the \texttt{digits\_in\_base} locale is introduced, which specifies a single symbol
@{term b} referring to a natural number greater than one (the base of the digits). Consequently
this symbol is omitted from many of the following lemmas and definitions.
\<close>

locale digits_in_base =
  fixes b :: nat
  assumes b_gte_2: "b \<ge> 2"
begin

lemma b_facts [simp]:
  shows "b > 1" and "b > 0" and "b \<noteq> 1" and "b \<noteq> 0" and "1 mod b = 1" and "1 div b = 0"
  using b_gte_2 by force+

text\<open>Definition based on @{cite ThreeDivides}.\<close>
abbreviation ith_digit :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"ith_digit m i \<equiv> (m div b^i) mod b"

lemma ith_digit_lt_base:
  fixes m i :: nat
  shows "0 \<le> ith_digit m i" and "ith_digit m i < b"
  apply (rule Nat.le0)
  using b_facts(2) mod_less_divisor by presburger

definition num_digits :: "nat \<Rightarrow> nat"
  where "num_digits m = (LEAST i. m < b^i)"

lemma num_digits_works:
  shows "m < b ^ (num_digits m)"
  by (metis LeastI One_nat_def b_facts(1) num_digits_def power_gt_expt)

lemma num_digits_le:
  assumes "m < b^i"
  shows "num_digits m \<le> i"
  using assms num_digits_works[of m] Least_le num_digits_def
  by metis

lemma num_digits_zero:
  fixes m :: nat
  assumes "num_digits m = 0"
  shows "m = 0"
  using num_digits_works[of m]
  unfolding assms
  by simp

lemma num_digits_gt:
  assumes "m \<ge> b^i"
  shows "num_digits m > i"
  by (meson assms b_facts(2) dual_order.strict_trans2 nat_power_less_imp_less num_digits_works)

lemma num_digits_eqI [intro]:
  assumes "m \<ge> b^i" and "m < b^(i+1)"
  shows "num_digits m = i + 1"
proof -
  {
    fix j :: nat
    assume "j < i + 1"
    then have "m \<ge> b^j"
      by (metis Suc_eq_plus1 assms(1) b_facts(1) less_Suc_eq_le order_trans power_increasing_iff)
  }
  then show ?thesis
    using num_digits_works
    unfolding num_digits_def
    by (meson assms(2) leD linorder_neqE_nat not_less_Least)
qed

lemma num_digits_char:
  assumes "m \<ge> 1"
  shows "num_digits m = i + 1 \<longleftrightarrow> m \<ge> b^i \<and> m < b^(i+1)"
  by (metis add_diff_cancel_right' assms b_gte_2 ex_power_ivl1 num_digits_eqI)


text\<open>Statement based on @{cite ThreeDivides}.\<close>
lemma num_digits_recurrence:
  fixes m :: nat
  assumes "m \<ge> 1"
  shows "num_digits m = num_digits (m div b) + 1"
proof -
  define nd where "nd = num_digits m"
  then have lb: "m \<ge> b^(nd-1)" and ub: "m < b^nd"
    using num_digits_char[OF assms]
     apply (metis assms diff_is_0_eq le_add_diff_inverse2 nat_le_linear power_0)
    using nd_def num_digits_works by presburger
  from ub have ub2: "m div b < b^(nd-1)"
    by (metis Suc_eq_plus1 add.commute add_diff_inverse_nat assms less_mult_imp_div_less less_one
        linorder_not_less mult.commute power.simps(2) power_0)
  from lb have lb2: "m div b \<ge> b^(nd - 1) div b"
    using div_le_mono by presburger
  show ?thesis
  proof (cases "m \<ge> b")
    assume "m \<ge> b"
    then have "nd \<ge> 2"
      unfolding nd_def
      by (metis One_nat_def assms less_2_cases_iff linorder_not_le nd_def power_0 power_one_right
          ub)
    then have "m div b \<ge> b^(nd-2)"
      using lb2
      by (smt (verit) One_nat_def add_le_imp_le_diff b_facts(4) diff_diff_left le_add_diff_inverse2
          nonzero_mult_div_cancel_left numeral_2_eq_2 plus_1_eq_Suc power_add power_commutes
          power_one_right)
    then show ?thesis
      using ub2 num_digits_char assms nd_def
      by (smt (verit) \<open>2 \<le> nd\<close> add_diff_cancel_right' add_leD2 add_le_imp_le_diff diff_diff_left
          eq_diff_iff le_add2 nat_1_add_1 num_digits_eqI)
  next
    assume "\<not> b \<le> m"
    then have "m < b"
      by simp
    then have "num_digits m = 1"
      using assms
      by (metis One_nat_def Suc_eq_plus1 num_digits_char power_0 power_one_right)
    from \<open>m < b\<close> have "m div b = 0"
      using div_less by presburger
    then have "num_digits (m div b) = 0"
      using Least_eq_0 num_digits_def by presburger
    show ?thesis
      using \<open>num_digits (m div b) = 0\<close> \<open>num_digits m = 1\<close> by presburger
  qed
qed

lemma num_digits_zero_2 [simp]: "num_digits 0 = 0"
  by (simp add: num_digits_def)

end (* digits_in_base *)

locale base_10
begin
text\<open>As a sanity check, the number of digits in base ten is computed for several natural numbers.\<close>

sublocale digits_in_base 10
  by (unfold_locales, simp)

corollary
  shows "num_digits 0 = 0"
        and "num_digits 1 = 1"
        and "num_digits 9 = 1"
        and "num_digits 10 = 2"
        and "num_digits 99 = 2"
        and "num_digits 100 = 3"
  by (simp_all add: num_digits_recurrence)

end (* base_10 *)

context digits_in_base
begin

lemma high_digits_zero_helper:
  fixes m i :: nat
  shows "i < num_digits m \<or> ith_digit m i = 0"
proof (cases "i < num_digits m")
  case True
  then show ?thesis by meson
next
  case False
  then have "i \<ge> num_digits m" by force
  then have "m < b^i"
    by (meson b_facts(1) num_digits_works order_less_le_trans power_increasing_iff)
  then show ?thesis
    by simp
qed

lemma high_digits_zero:
  fixes m i :: nat
  assumes "i \<ge> num_digits m"
  shows "ith_digit m i = 0"
  using high_digits_zero_helper assms leD by blast

lemma digit_expansion_bound:
  fixes i :: nat and A :: "nat \<Rightarrow> nat"
  assumes "\<And>j. A j < b"
  shows "(\<Sum>j<i. A j * b^j) < b^i"
proof (induct i)
  case (Suc i)
  show ?case
  proof (subst Set_Interval.comm_monoid_add_class.sum.lessThan_Suc)
    have "A i * b^i \<le> (b-1) * b^i" using assms
      by (metis One_nat_def Suc_pred b_facts(2) le_simps(2) mult_le_mono1)
    then have "(\<Sum>j<i. A j * b ^ j) + A i * b ^ i < b^i + (b-1) * b^i"
      using Suc add_less_le_mono by blast
    also have "\<dots> \<le> b ^ Suc i"
      using assms(1) mult_eq_if by auto
    finally show "(\<Sum>j<i. A j * b ^ j) + A i * b ^ i < b ^ Suc i" .
  qed
qed simp

text\<open>Statement and proof based on @{cite ThreeDivides}.\<close>
lemma num_digits_suc:
  fixes n m :: nat
  assumes "Suc n = num_digits m"
  shows "n = num_digits (m div b)"
  using num_digits_recurrence assms
  by (metis One_nat_def Suc_eq_plus1 Suc_le_lessD le_add2 linorder_not_less num_digits_le
      old.nat.inject power_0)

text\<open>Proof (and to some extent statement) based on @{cite ThreeDivides}.\<close>
lemma digit_expansion_bounded_seq:
  fixes m :: nat
  shows "m = (\<Sum>j<num_digits m. ith_digit m j * b^j)"
proof (induct "num_digits m" arbitrary: m)
  case 0
  then show "m = (\<Sum>j<num_digits m. ith_digit m j * b^j)"
    using lessThan_0 sum.empty num_digits_zero by metis
next
  case (Suc nd m)
  assume nd: "Suc nd = num_digits m"
  define c where "c = m mod b"
  then have mexp: "m = b * (m div b) + c" and "c < b"
    by force+
  show "m = (\<Sum>j<num_digits m. ith_digit m j * b^j)"
  proof -
    have "nd = num_digits (m div b)"
      using num_digits_suc[OF nd] .
    with Suc have "m div b = (\<Sum>j<nd. ith_digit (m div b) j * b^j)"
      by presburger
    with mexp have "m = b * (\<Sum>j<nd. ith_digit (m div b) j * b^j) + c"
      by presburger
    also have "\<dots> = (\<Sum>j<nd. ith_digit (m div b) j * b^Suc j) + c"
      by (simp add: sum_distrib_left mult.assoc mult.commute)
    also have "\<dots> = (\<Sum>j<nd. ith_digit m (Suc j) * b^Suc j) + c"
      by (simp add: div_mult2_eq)
    also have "\<dots> = (\<Sum>j=Suc 0..<Suc nd. ith_digit m j * b^j) + ith_digit m 0"
      unfolding sum.shift_bounds_Suc_ivl c_def atLeast0LessThan
      by simp
    also have "\<dots> = (\<Sum>j<Suc nd. ith_digit m j * b^j)"
      by (smt (verit) One_nat_def Zero_not_Suc add.commute add_diff_cancel_right' atLeast0LessThan
          calculation div_by_Suc_0 mult.commute nonzero_mult_div_cancel_left power_0
          sum.lessThan_Suc_shift sum.shift_bounds_Suc_ivl)
    also note nd
    finally show "m = (\<Sum>j<num_digits m. ith_digit m j * b^j)" .
  qed
qed

text\<open>A natural number can be obtained from knowing all its base-$b$ digits by the formula
$\sum_j d_j b^j$.\<close>
theorem digit_expansion_seq:
  fixes m :: nat
  shows "m = (\<Sum>j. ith_digit m j * b^j)"
  using digit_expansion_bounded_seq[of m] high_digits_zero[of m] sum_bounded mult_0
  by (metis (no_types, lifting))

lemma lower_terms:
  fixes a c i :: nat
  assumes "c < b^i" and "a < b"
  shows "ith_digit (a * b^i + c) i = a"
  using assms by force

lemma upper_terms:
  fixes A a i :: nat
  assumes "b*b^i dvd A" and "a < b"
  shows "ith_digit (A + a * b^i) i = a"
  using assms by force

lemma current_term:
  fixes A a c i :: nat
  assumes "b*b^i dvd A" and "c < b^i" and "a < b"
  shows "ith_digit (A + a*b^i + c) i = a"
proof -
  have "(A + a*b^i + c) div b^i mod b = (a*b^i + c) div b^i mod b"
    using assms(1)
    by (metis (no_types, lifting) div_eq_0_iff add_cancel_right_right
        assms(2) assms(3) div_plus_div_distrib_dvd_left dvd_add_times_triv_right_iff
        dvd_mult_right lower_terms upper_terms)
  also have "\<dots> = a"
    using assms by force
  finally show "(A + a*b^i + c) div b^i mod b = a" .
qed

text\<open>Given that
\begin{equation*}
m = \sum_i d_i b^i
\end{equation*}
where the $d_i$ are all natural numbers less than $b$, it follows that $d_j$ is the $j^{\text{th}}$
digit of $m$.\<close>
theorem seq_uniqueness:
  fixes m j :: nat and D :: "nat \<Rightarrow> nat"
  assumes "eventually_zero D" and "m = (\<Sum>i. D i * b^i)" and "\<And>i. D i < b"
  shows "D j = ith_digit m j"
proof -
  have "eventually_zero (ith_digit m)"
    using high_digits_zero
    by (meson eventually_zero_char)
  then have term_eventually_zero: "eventually_zero (\<lambda> i. D i * b^i)"
    using product_seq_eventually_zero assms(1) by auto
  then have shifted_term_eventually_zero:
    "eventually_zero (\<lambda> i. D (i + n) * b ^ (i + n))" for n
    using eventually_zero_shifted
    by blast
  note \<open>m = (\<Sum>i. D i * b^i)\<close>
  then have two_sums: "m = (\<Sum>i<Suc j. D i * b^i) + (\<Sum>i\<ge>Suc j. D i * b^i)"
    using split_suminf[OF term_eventually_zero] by presburger
  have "i\<ge>Suc j \<Longrightarrow> b*b^j dvd (D i * b^i)" for i
    by (metis dvd_mult2 le_imp_power_dvd mult.commute power_Suc)
  then have "b*b^j dvd (\<Sum>i\<ge>Suc j. D i * b^i)"
    using dvd_suminf shifted_term_eventually_zero le_add2
    by presburger
  with two_sums have "[m = (\<Sum>i<Suc j. D i * b^i)] (mod b*b^j)"
    by (meson cong_def Cong.cong_dvd_modulus_nat mod_add_self2)
  then have one_sum: "[m = (\<Sum>i<j. D i * b^i) + D j * b^j] (mod b*b^j)"
    by simp
  have "(\<Sum>i<j. D i * b^i) < b^j"
    using assms(3) digit_expansion_bound by blast
  with one_sum have "[m div b^j = (D j)] (mod b)"
    using another_mod_cancellation dual_order.strict_trans1
    unfolding cong_def
    by auto
  then show "D j = ith_digit m j"
    using assms(3) mod_less unfolding cong_def by presburger
qed


end (* digits_in_base *)

section\<open>Little Endian notation\<close>
text\<open>In this section we begin to define finite digit expansions. Ultimately we want to write digit
expansions in ``big endian'' notation, by which we mean with the highest place digit on the left
and the ones digit on the write, since this ordering is standard in informal mathematics. However,
it is easier to first define ``little endian'' expansions with the ones digit on the left since that
way the list indexing agrees with the sequence indexing used in the previous section (whenever both
are defined).

Notation, definitions, and lemmas in this section typically start with the prefix \texttt{LE} (for
``little endian'') to distinguish them from the big endian versions in the next section.
\<close>

fun LEeval_as_base ("_\<^bsub>LEbase _\<^esub>" [65, 65] 70)
  where "[] \<^bsub>LEbase b\<^esub> = 0"
  | "(d # d_list) \<^bsub>LEbase b\<^esub>  = d + b * (d_list\<^bsub>LEbase b\<^esub>)"

corollary shows "[2, 4] \<^bsub>LEbase 5\<^esub> = (22::nat)"
  by simp

lemma LEbase_one_digit [simp]: shows "[a::nat] \<^bsub>LEbase b\<^esub> = a"
  by simp

lemma LEbase_two_digits [simp]: shows "[a\<^sub>0::nat, a\<^sub>1] \<^bsub>LEbase b\<^esub> = a\<^sub>0 + a\<^sub>1 * b"
  by simp

lemma LEbase_three_digits [simp]: shows "[a\<^sub>0::nat, a\<^sub>1, a\<^sub>2] \<^bsub>LEbase b\<^esub> = a\<^sub>0 + a\<^sub>1*b + a\<^sub>2*b^2"
proof -
  have "[a\<^sub>0::nat, a\<^sub>1, a\<^sub>2] \<^bsub>LEbase b\<^esub> = a\<^sub>0 + ([a\<^sub>1, a\<^sub>2] \<^bsub>LEbase b\<^esub>) * b"
    by simp
  also have "\<dots> = a\<^sub>0 + (a\<^sub>1 + a\<^sub>2*b) * b"
    by simp
  also have "\<dots> = a\<^sub>0 + a\<^sub>1*b + a\<^sub>2*b^2"
    by (simp add: add_mult_distrib power2_eq_square)
  finally show ?thesis .
qed


lemma LEbase_closed_form:
shows "(A :: nat list) \<^bsub>LEbase b\<^esub> = (\<Sum>i < length A . A!i * b^i)"
proof (induct A)
  case Nil
  show ?case
    by simp
next
  case (Cons a A)
  show ?case
  proof -
    have "(a # A)\<^bsub>LEbase b\<^esub> = a + b * (A\<^bsub>LEbase b\<^esub>)"
      by simp
    also have "\<dots> = a + b * (\<Sum>i<length A. A!i * b ^ i)"
      using Cons by simp
    also have "\<dots> = a + (\<Sum>i<length A. b * A!i * b^i)"
      by (smt (verit) mult.assoc sum.cong sum_distrib_left)
    also have "\<dots> = a + (\<Sum>i<length A. A!i * b^(i+1))"
      by (simp add: mult.assoc mult.left_commute)
    also have "\<dots> = a + (\<Sum>i<length A. (a#A)!(i+1) * b^(i+1))"
      by force
    also have "\<dots> = (a#A)!0 * b^0 + (\<Sum>i<length A. (a#A)!(Suc i) * b^(Suc i))"
      by force
    also have "\<dots> = (\<Sum>i<length (a # A). (a#A)!i * b^i)"
      using sum.lessThan_Suc_shift
      by (smt (verit) length_Cons sum.cong)
    finally show ?thesis .
  qed
qed

lemma LEbase_concatenate:
  fixes A D :: "nat list" and b :: nat
  shows "(A @ D)\<^bsub>LEbase b\<^esub> = (A\<^bsub>LEbase b\<^esub>) + b^(length A) * (D\<^bsub>LEbase b\<^esub>)"
proof (induct A)
  case Nil
  show ?case
    by simp
next
  case (Cons a A)
  show ?case
  proof -
    have "((a # A) @ D)\<^bsub>LEbase b\<^esub> = ((a # (A @ D)) \<^bsub>LEbase b\<^esub>)"
      by simp
    also have "\<dots> = a + b * ((A @ D) \<^bsub>LEbase b\<^esub>)"
      by simp
    also have "\<dots> = a + b * (A\<^bsub>LEbase b\<^esub> + b ^ length A * (D\<^bsub>LEbase b\<^esub>))"
      unfolding Cons by rule
    also have "\<dots> = (a + b * (A\<^bsub>LEbase b\<^esub>)) + b ^ (length (a#A)) * (D\<^bsub>LEbase b\<^esub>)"
      by (simp add: distrib_left)
    also have "\<dots> = ((a # A)\<^bsub>LEbase b\<^esub>) + b ^ length (a # A) * (D\<^bsub>LEbase b\<^esub>)"
      by simp
    finally show ?thesis .
  qed
qed

context digits_in_base
begin

definition LEdigits :: "nat \<Rightarrow> nat list" where
"LEdigits m = [ith_digit m i. i \<leftarrow> [0..<(num_digits m)]]"

lemma length_is_num_digits:
  fixes m :: nat
  shows "length (LEdigits m) = num_digits m"
  unfolding LEdigits_def by simp

lemma ith_list_element [simp]:
  assumes "(i::nat) < length (LEdigits m)"
  shows "(LEdigits m) ! i = ith_digit m i"
  using assms
  by (simp add: length_is_num_digits LEdigits_def)

lemma LEbase_infinite_sum:
  fixes m :: nat
  shows "(\<Sum>i. ith_digit m i  * b^i) = (LEdigits m)\<^bsub>LEbase b\<^esub>"
proof (unfold LEdigits_def LEbase_closed_form)
  have
    "(\<Sum>i<length (map (ith_digit m) [0..<num_digits m]).
                                                  map (ith_digit m) [0..<num_digits m] ! i * b ^ i)
     = (\<Sum>i<num_digits m. map (ith_digit m) [0..<num_digits m] ! i * b ^ i)"
    using LEdigits_def length_is_num_digits by presburger
  also have "\<dots>= (\<Sum>i<num_digits m. ith_digit m i * b^i)"
    by force
  also have "\<dots>=(\<Sum>i. ith_digit m i * b ^ i)" 
    using sum_bounded high_digits_zero mult_0
    by (metis (no_types, lifting))
  finally show
    "(\<Sum>i. ith_digit m i * b ^ i) =
     (\<Sum>i<length (map (ith_digit m) [0..<num_digits m]). map (ith_digit m) [0..<num_digits m] ! i * b ^ i)"
    by presburger
qed

lemma digit_expansion_LElist:
  fixes m :: nat
  shows "(LEdigits m)\<^bsub>LEbase b\<^esub> = m"
  using digit_expansion_seq LEbase_infinite_sum
  by presburger

lemma LElist_uniqueness:
  fixes D :: "nat list"
  assumes "\<forall> i < length D. D!i < b" and "D = [] \<or> last D \<noteq> 0"
  shows "LEdigits (D\<^bsub>LEbase b\<^esub>) = D"
proof -
  define seq where "seq i = (if i < length D then D!i else 0)" for i
  then have seq_bound: "i \<ge> length D \<Longrightarrow> seq i = 0" for i
    by simp
  then have seq_eventually_zero: "eventually_zero seq"
    using eventually_zero_char by blast
  have ith_digit_connection: "i < num_digits m \<Longrightarrow> (LEdigits m)!i = ith_digit m i" for m i
    unfolding LEdigits_def by simp
  let ?m = "D\<^bsub>LEbase b\<^esub>"
  have length_bounded_sum: "D\<^bsub>LEbase b\<^esub> = (\<Sum>i<length D. seq i * b^i)"
    unfolding LEbase_closed_form seq_def by force
  also have "\<dots> = (\<Sum>i. seq i * b^i)"
    using seq_bound sum_bounded by fastforce
  finally have seq_is_digits: "seq j = ith_digit ?m j" for j
    using seq_uniqueness[OF seq_eventually_zero] assms(1)
    by (metis b_facts(2) seq_def)
  then have "i < length D \<Longrightarrow> ith_digit ?m i = D!i" for i
    using seq_def by presburger
  then have "i < length D \<Longrightarrow> i < num_digits ?m \<Longrightarrow> (LEdigits ?m)!i = D!i" for i
    using ith_digit_connection[of i ?m] by presburger
  moreover have "length D = num_digits ?m"
  proof (rule le_antisym)
    show "length D \<le> num_digits ?m"
    proof (cases "D = []")
      assume "D \<noteq> []"
      then have "last D \<noteq> 0" using assms(2) by auto
      then have "last D \<ge> 1" by simp
      have "?m \<ge> seq (length D - 1) * b^(length D - 1)"
        using length_bounded_sum
        by (smt (z3) One_nat_def Suc_pred diff_is_0_eq diff_le_self dual_order.strict_trans1 le_add2
            linorder_le_less_linear mult.right_neutral mult_cancel1 seq_def sum.lessThan_Suc
            zero_less_diff)
      then have "?m \<ge> (last D) * b^(length D - 1)"
        by (simp add: \<open>D \<noteq> []\<close> last_conv_nth seq_def)
      with \<open>last D \<ge> 1\<close> have "?m \<ge> b^(length D - 1)"
        by (metis le_trans mult_1 mult_le_mono1)
      then show "num_digits ?m \<ge> length D"
        using num_digits_gt not_less_eq
        by (metis One_nat_def Suc_pred \<open>D \<noteq> []\<close> bot_nat_0.extremum_uniqueI leI length_0_conv)
    qed simp
    show "num_digits ?m \<le> length D"
      by (metis length_bounded_sum seq_is_digits digit_expansion_bound ith_digit_lt_base(2)
          num_digits_le)
  qed
  ultimately show ?thesis
    by (simp add: length_is_num_digits list_eq_iff_nth_eq)
qed

lemma LE_digits_zero [simp]: "LEdigits 0 = []"
  using LEdigits_def by auto

lemma LE_units_digit [simp]:
  assumes "(m::nat) \<in> {1..<b}"
  shows "LEdigits m = [m]"
  using assms LEdigits_def num_digits_recurrence by auto

end (* digits_in_base *)

section\<open>Big Endian notation\<close>
text\<open>In this section the desired representation of natural numbers, as finite lists of digits
with the highest place on the left, is finally realized.\<close>

definition BEeval_as_base ("_\<^bsub>base _\<^esub>" [65, 65] 70)
  where [simp]: "D\<^bsub>base b\<^esub> = (rev D)\<^bsub>LEbase b\<^esub>"

corollary shows "[4, 2]\<^bsub>base 5\<^esub> = (22::nat)"
  by simp

lemma BEbase_one_digit [simp]: shows "[a::nat] \<^bsub>base b\<^esub> = a"
  by simp

lemma BEbase_two_digits [simp]: shows "[a\<^sub>1::nat, a\<^sub>0] \<^bsub>base b\<^esub> = a\<^sub>1*b + a\<^sub>0"
  by simp

lemma BEbase_three_digits [simp]: shows "[a\<^sub>2::nat, a\<^sub>1, a\<^sub>0] \<^bsub>base b\<^esub> = a\<^sub>2*b^2 + a\<^sub>1*b + a\<^sub>0"
proof -
  have "b * (a\<^sub>1 + b * a\<^sub>2) = a\<^sub>2 * b\<^sup>2 + a\<^sub>1 * b"
    apply (subst mult.commute)
    unfolding add_mult_distrib power2_eq_square
    by simp
  then show ?thesis by simp
qed

lemma BEbase_closed_form:
  fixes A :: "nat list" and b :: nat
  shows "A\<^bsub>base b\<^esub> = (\<Sum>i<length A. A!i * b^(length A - Suc i))"
  unfolding LEbase_closed_form BEeval_as_base_def
  apply (subst sum.nat_diff_reindex[symmetric])
  apply (subst length_rev)
  using rev_nth
  by (metis (no_types, lifting) length_rev lessThan_iff rev_rev_ident sum.cong)

lemma BEbase_concatenate:
  fixes A D :: "nat list" and b :: nat
  shows "(A @ D) \<^bsub>base b\<^esub> = (A\<^bsub>base b\<^esub>)*b^(length D) + (D\<^bsub>base b\<^esub>)"
  using LEbase_concatenate by simp

context digits_in_base
begin

definition digits :: "nat \<Rightarrow> nat list" where
"digits m = rev (LEdigits m)"

lemma length_is_num_digits_2:
  fixes m :: nat
  shows "length (digits m) = num_digits m"
  using length_is_num_digits digits_def by simp

lemma LE_BE_equivalence:
  fixes m :: nat
  shows "(digits m) \<^bsub>base b\<^esub> = (LEdigits m) \<^bsub>LEbase b\<^esub>"
  by (simp add: digits_def)

lemma BEbase_infinite_sum:
  fixes m :: nat
  shows "(\<Sum>i. ith_digit m i * b^i) = (digits m)\<^bsub>base b\<^esub>"
  using LE_BE_equivalence LEbase_infinite_sum by presburger

text\<open>Every natural number can be represented in base $b$, specifically by the digits sequence
defined earlier.\<close>
theorem digit_expansion_list:
  fixes m :: nat
  shows "(digits m)\<^bsub>base b\<^esub> = m"
  using LE_BE_equivalence digit_expansion_LElist by auto

text\<open>If two natural numbers have the same base-$b$ representation, then they are equal.\<close>
lemma digits_cancellation:
  fixes k m :: nat
  assumes "digits k = digits m"
  shows "k = m"
  by (metis assms digit_expansion_list)

text\<open>Suppose we have a finite (possibly empty) sequence $D_1, \dotsc, D_n$ of natural numbers such
that $0 \le D_i < b$ for all $i$ and such that $D_1$, if it exists, is nonzero. Then this sequence
is the base-$b$ representation for $\sum_i D_i b^{n-i}$.\<close>
theorem list_uniqueness:
  fixes D :: "nat list"
  assumes "\<forall> d \<in> set D. d < b" and "D = [] \<or> D!0 \<noteq> 0"
  shows "digits (D\<^bsub>base b\<^esub>) = D"
  unfolding digits_def BEeval_as_base_def
  using LElist_uniqueness
  by (metis Nil_is_rev_conv One_nat_def assms last_conv_nth length_greater_0_conv
      nth_mem rev_nth rev_swap set_rev)

text\<open>We now prove some simplification rules (including a reccurrence relation) to make it easier for
Isabelle/HOL to compute the base-$b$ representation of a natural number.\<close>

text\<open>The base-b representation of $0$ is empty, at least following the conventions of this theory
file.\<close>
lemma digits_zero [simp]:
  shows "digits 0 = []"
  by (simp add: digits_def)

text\<open>If $0 < m < b$, then the base-$b$ representation of $m$ consists of a single digit, namely
$m$ itself.\<close>
lemma single_digit_number [simp]:
  assumes "m \<in> {0<..<b}"
  shows "digits m = [m]"
  using assms digits_def by auto

text\<open>For all $m \ge b$, the base-$b$ representation of $m$ consists of the base-$b$ representation
of $\lfloor m / b \rfloor$ followed by (as the last digit) the remainder of $m$ when divided by
$b$.\<close>
lemma digits_recurrence [simp]:
  assumes "m \<ge> b"
  shows "digits m = (digits (m div b)) @ [m mod b]"
proof -
  have "num_digits m > 1"
    using assms by (simp add: num_digits_gt)
  then have "num_digits m > 0"
    by simp
  then have "num_digits (m div b) = num_digits m - 1"
    by (metis Suc_diff_1 num_digits_suc)
  have "k > 0 \<Longrightarrow> last (rev [0..<k]) = 0" for k::nat
    by (simp add: last_rev)
  have "[Suc 0..<Suc k] = [Suc i. i \<leftarrow> [0..<k]]" for k::nat
    using map_Suc_upt by presburger
  then have "rev [Suc 0..<Suc k] = [Suc i. i \<leftarrow> rev [0..<k]]" for k::nat
    by (metis rev_map)
  then have "[f i. i \<leftarrow> rev [Suc 0..<Suc k]] = [f (Suc i). i \<leftarrow> rev [0..<k]]" for f and k::nat
    by simp
  then have map_shift: "k > 0 \<Longrightarrow> [f i. i \<leftarrow> rev [1..<k]] = [f (Suc i). i \<leftarrow> rev [0..<(k-1)]]"
                       for f and k::nat
    by (metis One_nat_def Suc_diff_1)
  have digit_down: "ith_digit m (Suc i) = ith_digit (m div b) i" for i::nat
    by (simp add: div_mult2_eq)
  have "digits m = rev [ith_digit m i. i \<leftarrow> [0..<num_digits m]]"
    using LEdigits_def digits_def by presburger
  also have "\<dots> = [ith_digit m i. i \<leftarrow> rev [0..<num_digits m]]"
    using rev_map by blast
  also have "\<dots> = [ith_digit m i. i \<leftarrow> butlast (rev [0..<num_digits m])] @
                  [ith_digit m (last (rev [0..<num_digits m]))]"
    by (metis (no_types, lifting) Nil_is_map_conv Nil_is_rev_conv \<open>1 < num_digits m\<close>
        bot_nat_0.extremum_strict dual_order.strict_trans1 last_map map_butlast snoc_eq_iff_butlast
        upt_eq_Nil_conv)
  also have "\<dots> = [ith_digit m i. i \<leftarrow> rev [1..<num_digits m]] @
                  [ith_digit m 0]"
    using \<open>1 < num_digits m\<close> \<open>\<And>k. 0 < k \<Longrightarrow> last (rev [0..<k]) = 0\<close> by fastforce
  also have "\<dots> = [ith_digit m (Suc i). i \<leftarrow> rev [0..<(num_digits m - 1)]] @
                  [ith_digit m 0]"
    using map_shift[OF \<open>num_digits m > 0\<close>] by blast
  also have "\<dots> = [ith_digit (m div b) i. i \<leftarrow> rev [0..<(num_digits m - 1)]] @
                  [ith_digit m 0]"
    using digit_down by presburger
  also have "\<dots> = (digits (m div b)) @ [ith_digit m 0]"
    by (simp add: LEdigits_def \<open>num_digits (m div b) = num_digits m - 1\<close> digits_def rev_map)
  also have "\<dots> = (digits (m div b)) @ [m mod b]"
    by simp
  finally show ?thesis .
qed

end (* digits_in_base *)

section\<open>Exercises\<close>
text\<open>This section contains demonstrations of how to denote certain facts with the notation of the
previous sections, and how to quickly prove those facts using the lemmas and theorems above.
\<close>

text\<open>The base-5 representation of $22$ is $42_5$.\<close>
corollary "digits_in_base.digits 5 22 = [4, 2]"
proof -
  interpret digits_in_base 5
    by (simp add: digits_in_base.intro)
  show "digits 22 = [4, 2]"
    by simp
qed

text\<open>A different proof of the same statement.\<close>
corollary "digits_in_base.digits 5 22 = [4, 2]"
proof -
  interpret digits_in_base 5
    by (simp add: digits_in_base.intro)
  have "[4, 2]\<^bsub>base 5\<^esub> = (22::nat)"
    by simp
  have "d \<in> set [4, 2] \<Longrightarrow> d < 5" for d::nat
    by fastforce
  then show ?thesis
    using list_uniqueness
    by (metis \<open>[4, 2]\<^bsub>base 5\<^esub> = 22\<close> nth_Cons_0 numeral_2_eq_2 zero_neq_numeral)
qed

end
