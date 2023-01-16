section \<open>Introduction\label{sec:intro}\<close>

theory Prefix_Free_Code_Combinators
  imports
    "HOL-Library.Extended_Real"
    "HOL-Library.Float"
    "HOL-Library.FuncSet"
    "HOL-Library.List_Lexorder"
    "HOL-Library.Log_Nat"
    "HOL-Library.Sublist"
begin

text \<open>The encoders are represented as partial prefix-free functions. The advantage of
prefix free codes is that they can be easily combined by concatenation. The approach
of using prefix free codes (on the byte-level) for the representation of complex data
structures is common in many industry encoding libraries (cf. \<^cite>\<open>"rfc8949"\<close>).

The reason for representing encoders using partial functions, stems from some use-cases
where the objects to be encoded may be in a much smaller sets, as their type may suggest.
For example a natural number may be known to have a given range, or a function may be
encodable because it has a finite domain.

Note: Prefix-free codes can also be automatically derived using Huffmans' algorithm, which was
formalized by Blanchette~\<^cite>\<open>"Huffman-AFP"\<close>. This is especially useful if it is possible to transmit
a dictionary before the data. On the other hand these standard codes are useful, when the above is
impractical and/or the distribution of the input is unknown or expected to be close to the one's
implied by standard codes.

The following section contains general definitions and results, followed by
Section~\ref{sec:dep_enc} to \ref{sec:float_enc} where encoders for primitive types
and combinators are defined. Each construct is accompanied by lemmas verifying that they
form prefix free codes as well as bounds on the bit count to encode the data.
Section~\ref{sec:examples} concludes with a few examples.\<close>

section \<open>Encodings\<close>

fun opt_prefix where
  "opt_prefix (Some x) (Some y) = prefix x y" |
  "opt_prefix _ _ = False"

definition "opt_comp x y = (opt_prefix x y \<or> opt_prefix y x)"

fun opt_append :: "bool list option \<Rightarrow> bool list option \<Rightarrow> bool list option"
  where
    "opt_append (Some x) (Some y) = Some (x@y)" |
    "opt_append _ _ = None"

lemma opt_comp_sym: "opt_comp x y = opt_comp y x"
  by (simp add:opt_comp_def, blast)

lemma opt_comp_append:
  assumes "opt_comp (opt_append x y) z"
  shows "opt_comp x z"
proof -
  obtain x' y' z' where a: "x = Some x'" "y = Some y'" "z = Some z'"
    using assms
    by (cases x, case_tac[!] y, case_tac[!] z, auto simp: opt_comp_def)
  have "prefix (x'@y') z' \<or> prefix z' (x'@y')"
    using a assms by (simp add:opt_comp_def)
  hence "prefix x' z' \<or> prefix z' x'"
    using prefix_same_cases append_prefixD by blast
  thus ?thesis
    using a by (simp add:opt_comp_def)
qed

lemma opt_comp_append_2:
  assumes "opt_comp x (opt_append y z)"
  shows "opt_comp x y"
  using opt_comp_append opt_comp_sym assms by blast

lemma opt_comp_append_3:
  assumes "opt_comp (opt_append x y) (opt_append x z)"
  shows "opt_comp y z"
  using assms
  by (cases x, case_tac[!] y, case_tac[!] z, auto simp: opt_comp_def)

type_synonym 'a encoding = "'a \<rightharpoonup> bool list"

definition is_encoding :: "'a encoding \<Rightarrow> bool"
  where "is_encoding f = (\<forall>x y. opt_prefix (f x) (f y) \<longrightarrow> x = y)"

text \<open>An encoding function is represented as partial functions into lists of booleans, where
each list element represents a bit. Such a function is defined to be an encoding, if it is
prefix-free on its domain. This is similar to the formalization by Hibon and
Paulson~\<^cite>\<open>"Source_Coding_Theorem-AFP"\<close> except for the use of partial functions for the
practical reasons described in Section~\ref{sec:intro}.\<close>

lemma is_encodingI:
  assumes "\<And>x x' y y'. e x = Some x' \<Longrightarrow> e y = Some y' \<Longrightarrow>
    prefix x' y' \<Longrightarrow> x = y"
  shows "is_encoding e"
proof -
  have "opt_prefix (e x) (e y) \<Longrightarrow> x = y" for x y
    using assms by (cases "e x", case_tac[!] "e y", auto)
  thus ?thesis by (simp add:is_encoding_def)
qed

lemma is_encodingI_2:
  assumes "\<And>x y . opt_comp (e x) (e y) \<Longrightarrow> x = y"
  shows "is_encoding e"
  using assms by (simp add:opt_comp_def is_encoding_def)

lemma encoding_triv: "is_encoding Map.empty"
  by (rule is_encodingI_2, simp add:opt_comp_def)

lemma is_encodingD:
  assumes "is_encoding e"
  assumes "opt_comp (e x) (e y)"
  shows "x = y"
  using assms by (auto simp add:opt_comp_def is_encoding_def)

lemma encoding_imp_inj:
  assumes "is_encoding f"
  shows "inj_on f (dom f)"
  using assms
  by (intro inj_onI, simp add:is_encoding_def, force)

fun bit_count :: "bool list option \<Rightarrow> ereal" where
  "bit_count None = \<infinity>" |
  "bit_count (Some x) = ereal (length x)"

lemma bit_count_finite_imp_dom:
  "bit_count (f x) < \<infinity> \<Longrightarrow> x \<in> dom f"
  by (cases "f x", auto)

lemma bit_count_append:
  "bit_count (opt_append x y) = bit_count x + bit_count y"
  by (cases x, case_tac[!] "y", simp_all)

section \<open>(Dependent) Products\label{sec:dep_enc}\<close>

definition encode_dependent_prod ::
  "'a encoding \<Rightarrow> ('a \<Rightarrow> 'b encoding) \<Rightarrow> ('a \<times> 'b) encoding"
  (infixr "\<Join>\<^sub>e" 65)
  where
    "encode_dependent_prod e f x =
      opt_append (e (fst x)) (f (fst x) (snd x))"

lemma dependent_encoding:
  assumes "is_encoding e1"
  assumes "\<And>x. x \<in> dom e1 \<Longrightarrow> is_encoding (e2 x)"
  shows "is_encoding (e1 \<Join>\<^sub>e e2)"
proof (rule is_encodingI_2)
  fix x y
  assume a:"opt_comp ((e1 \<Join>\<^sub>e e2) x) ((e1 \<Join>\<^sub>e e2) y)"
  have d:"opt_comp (e1 (fst x)) (e1 (fst y))"
    using a unfolding encode_dependent_prod_def
    by (metis opt_comp_append opt_comp_append_2)
  hence b:"fst x = fst y"
    using is_encodingD[OF assms(1)] by simp
  hence "opt_comp (e2 (fst x) (snd x)) (e2 (fst x) (snd y))"
    using a unfolding encode_dependent_prod_def by (metis opt_comp_append_3)
  moreover have "fst x \<in> dom e1" using d b
    by (cases "e1 (fst x)", simp_all add:opt_comp_def dom_def)
  ultimately have c:"snd x = snd y"
    using is_encodingD[OF assms(2)] by simp
  show "x = y"
    using b c by (simp add: prod_eq_iff)
qed

lemma dependent_bit_count:
  "bit_count ((e\<^sub>1 \<Join>\<^sub>e e\<^sub>2) (x\<^sub>1,x\<^sub>2)) =
    bit_count (e\<^sub>1 x\<^sub>1) + bit_count (e\<^sub>2 x\<^sub>1 x\<^sub>2)"
  by (simp add: encode_dependent_prod_def bit_count_append)

lemma dependent_bit_count_2:
  "bit_count ((e\<^sub>1 \<Join>\<^sub>e e\<^sub>2) x) =
    bit_count (e\<^sub>1 (fst x)) + bit_count (e\<^sub>2 (fst x) (snd x))"
  by (simp add: encode_dependent_prod_def bit_count_append)

text \<open>This abbreviation is for non-dependent products.\<close>

abbreviation encode_prod ::
  "'a encoding \<Rightarrow> 'b encoding \<Rightarrow> ('a \<times> 'b) encoding"
  (infixr "\<times>\<^sub>e" 65)
  where
    "encode_prod e1 e2 \<equiv> e1 \<Join>\<^sub>e (\<lambda>_. e2)"

section \<open>Composition\<close>

lemma encoding_compose:
  assumes "is_encoding f"
  assumes "inj_on g {x. p x}"
  shows "is_encoding (\<lambda>x. if p x then f (g x) else None)"
  using assms by (simp add:comp_def is_encoding_def inj_onD)

lemma encoding_compose_2:
  assumes "is_encoding f"
  assumes "inj g"
  shows "is_encoding (\<lambda>x. f (g x))"
  using assms by (simp add:comp_def is_encoding_def inj_onD)

section \<open>Natural Numbers\<close>

fun encode_bounded_nat :: "nat \<Rightarrow> nat \<Rightarrow> bool list" where
  "encode_bounded_nat (Suc l) n =
    (let r = n \<ge> (2^l) in r#encode_bounded_nat l (n-of_bool r*2^l))" |
  "encode_bounded_nat 0 _ = []"

lemma encode_bounded_nat_prefix_free:
  fixes u v l :: nat
  assumes "u < 2^l"
  assumes "v < 2^l"
  assumes "prefix (encode_bounded_nat l u) (encode_bounded_nat l v)"
  shows "u = v"
  using assms
proof (induction l arbitrary: u v)
  case 0
  then show ?case by simp
next
  case (Suc l)
  have "prefix (encode_bounded_nat l (u - of_bool (u \<ge> 2^l)*2^l))
    (encode_bounded_nat l (v - of_bool (v \<ge> 2^l)*2^l))"
    and a:"(u \<ge> 2^l) = (v \<ge> 2^l)"
    using Suc(4) by (simp_all add: Let_def split: split_of_bool_asm)
  moreover have "u - of_bool (u \<ge> 2^l)*2^l < 2^l"
    using Suc(2) by (cases "u < 2^l", auto simp add:of_bool_def)
  moreover have "v - of_bool (v \<ge> 2^l)*2^l < 2^l"
    using Suc(3) by (cases "v < 2^l", auto simp add:of_bool_def)
  ultimately have
    "u - of_bool (u \<ge> 2^l)*2^l = v - of_bool (v \<ge> 2^l)*2^l"
    by (intro Suc(1), simp_all)
  thus "u = v" using a by (simp split: split_of_bool_asm)
qed

definition Nb\<^sub>e :: "nat \<Rightarrow> nat encoding"
  where "Nb\<^sub>e l n = (
    if n < l
      then Some (encode_bounded_nat (floorlog 2 (l-1)) n)
      else None)"

text \<open>@{term "Nb\<^sub>e l"} is  encoding for natural numbers strictly smaller than
  @{term "l"} using a fixed length encoding.\<close>

lemma bounded_nat_bit_count:
  "bit_count (Nb\<^sub>e l y) = (if y < l then floorlog 2 (l-1) else \<infinity>)"
proof -
  have a:"length (encode_bounded_nat h m) = h" for h m
    by (induction h arbitrary: m, simp, simp add:Let_def)
  show ?thesis
    using a by (simp add:Nb\<^sub>e_def)
qed

lemma bounded_nat_bit_count_2:
  assumes "y < l"
  shows "bit_count (Nb\<^sub>e l y) = floorlog 2 (l-1)"
  using assms bounded_nat_bit_count by simp

lemma "dom (Nb\<^sub>e l) = {..<l}"
  by (simp add:Nb\<^sub>e_def dom_def lessThan_def)

lemma bounded_nat_encoding: "is_encoding (Nb\<^sub>e l)"
proof -
  have "x < l \<Longrightarrow> x < 2 ^ floorlog 2 (l-1)" for x :: nat
    by (intro floorlog_leD floorlog_mono, auto)
  thus ?thesis
    using encode_bounded_nat_prefix_free
    by (intro is_encodingI, simp add:Nb\<^sub>e_def split:if_splits, blast)
qed

fun encode_unary_nat :: "nat \<Rightarrow> bool list" where
  "encode_unary_nat (Suc l) = False#(encode_unary_nat l)" |
  "encode_unary_nat 0 = [True]"

lemma encode_unary_nat_prefix_free:
  fixes u v :: nat
  assumes "prefix (encode_unary_nat u) (encode_unary_nat v)"
  shows "u = v"
  using assms
proof (induction u arbitrary: v)
  case 0
  then show ?case by (cases v, simp_all)
next
  case (Suc u)
  then show ?case by (cases v, simp_all)
qed

definition Nu\<^sub>e :: "nat encoding"
  where "Nu\<^sub>e n = Some (encode_unary_nat n)"

text \<open>@{term "Nu\<^sub>e"} is encoding for natural numbers using unary encoding. It is
inefficient except for special cases, where the probability of large numbers decreases
exponentially with its magnitude.\<close>

lemma unary_nat_bit_count:
  "bit_count (Nu\<^sub>e n) = Suc n"
  unfolding Nu\<^sub>e_def by (induction n, auto)

lemma unary_encoding: "is_encoding Nu\<^sub>e"
    using encode_unary_nat_prefix_free
    by (intro is_encodingI, simp add:Nu\<^sub>e_def)

text \<open>Encoding for positive numbers using Elias-Gamma code.\<close>

definition Ng\<^sub>e :: "nat encoding" where
  "Ng\<^sub>e n =
    (if n > 0
      then (Nu\<^sub>e \<Join>\<^sub>e (\<lambda>r. Nb\<^sub>e (2^r)))
        (let r = floorlog 2 n - 1 in (r, n - 2^r))
      else None)"

text \<open>@{term "Ng\<^sub>e"} is an encoding for positive numbers using Elias-Gamma encoding\<^cite>\<open>"elias1975"\<close>.\<close>

lemma elias_gamma_bit_count:
  "bit_count (Ng\<^sub>e n) = (if n > 0 then 2 * \<lfloor>log 2 n\<rfloor> + 1 else (\<infinity>::ereal))"
proof (cases "n > 0")
  case True
  define r where "r = floorlog 2 n - Suc 0"
  have "floorlog 2 n \<noteq> 0"
    using True
    by (simp add:floorlog_eq_zero_iff)
  hence a:"floorlog 2 n > 0" by simp

  have "n < 2^(floorlog 2 n)"
    using True floorlog_bounds by simp
  also have "... = 2^(r+1)"
    using a by (simp add:r_def)
  finally have "n < 2^(r+1)" by simp
  hence b:"n - 2^r < 2^r" by simp
  have "floorlog 2 (2 ^ r - Suc 0) \<le> r"
    by (rule floorlog_leI, auto)
  moreover have "r \<le> floorlog 2 (2 ^ r - Suc 0)"
    by (cases r, simp, auto intro: floorlog_geI)
  ultimately have c:"floorlog 2 (2 ^ r - Suc 0) = r"
    using order_antisym by blast

  have "bit_count (Ng\<^sub>e n) = bit_count (Nu\<^sub>e r) +
    bit_count (Nb\<^sub>e (2 ^ r) (n - 2 ^ r))"
    using True by (simp add:Ng\<^sub>e_def r_def[symmetric] dependent_bit_count)
  also have "... = ereal (r + 1) + ereal (r)"
    using b c
    by (simp add: unary_nat_bit_count bounded_nat_bit_count)
  also have "... = 2 * r + 1" by simp
  also have "... = 2 * \<lfloor>log 2 n\<rfloor> + 1"
    using True by (simp add:floorlog_def r_def)
  finally show ?thesis using True by simp
next
  case False
  then show ?thesis by (simp add:Ng\<^sub>e_def)
qed

lemma elias_gamma_encoding: "is_encoding Ng\<^sub>e"
proof -
  have a: "inj_on (\<lambda>x. let r = floorlog 2 x - 1 in (r, x - 2 ^ r))
    {n. 0 < n}"
  proof (rule inj_onI)
    fix x y :: nat
    assume "x \<in> {n. 0 < n}"
    hence x_pos: "0 < x" by simp
    assume "y \<in> {n. 0 < n}"
    hence y_pos: "0 < y" by simp
    define r where "r = floorlog 2 x - Suc 0"
    assume b:"(let r = floorlog 2 x - 1 in (r, x - 2 ^ r)) =
      (let r = floorlog 2 y - 1 in (r, y - 2 ^ r))"
    hence c:"r = floorlog 2 y - Suc 0"
      by (simp_all add:Let_def r_def)
    have "x - 2^r = y - 2^r" using b
      by (simp add:Let_def r_def[symmetric] c[symmetric]  prod_eq_iff)
    moreover have "x \<ge> 2^r"
      using r_def x_pos floorlog_bounds by simp
    moreover have "y \<ge> 2^r"
      using c floorlog_bounds y_pos by simp
    ultimately show "x = y" using eq_diff_iff by blast
  qed

  have "is_encoding (\<lambda>n. Ng\<^sub>e n)"
    unfolding Ng\<^sub>e_def using a
    by (intro encoding_compose[where f="Nu\<^sub>e \<Join>\<^sub>e (\<lambda>r. Nb\<^sub>e (2^r))"]
        dependent_encoding unary_encoding bounded_nat_encoding) auto
  thus ?thesis by simp
qed

definition N\<^sub>e :: "nat encoding" where "N\<^sub>e x = Ng\<^sub>e (x+1)"

text \<open>@{term "N\<^sub>e"} is an encoding for all natural numbers using exponential Golomb
encoding~\<^cite>\<open>"teuhola1978"\<close>. Exponential Golomb codes are also used in video compression
applications~\<^cite>\<open>"richardson2010"\<close>.\<close>

lemma exp_golomb_encoding: "is_encoding N\<^sub>e"
proof -
  have "is_encoding (\<lambda>n. N\<^sub>e n)"
    unfolding N\<^sub>e_def
    by (intro encoding_compose_2[where g="(\<lambda>n. n + 1)"] elias_gamma_encoding, auto)
  thus ?thesis by simp
qed

lemma exp_golomb_bit_count_exact:
  "bit_count (N\<^sub>e n) = 2 * \<lfloor>log 2 (n+1)\<rfloor> + 1"
  by (simp add:N\<^sub>e_def elias_gamma_bit_count)

lemma exp_golomb_bit_count:
  "bit_count (N\<^sub>e n) \<le> (2 * log 2 (real n+1) + 1)"
  by (simp add:exp_golomb_bit_count_exact add.commute)

lemma exp_golomb_bit_count_est:
  assumes "n \<le> m "
  shows "bit_count (N\<^sub>e n) \<le> (2 * log 2 (real m+1) + 1)"
proof -
  have "bit_count (N\<^sub>e n) \<le> (2 * log 2 (real n+1) + 1)"
    using exp_golomb_bit_count by simp
  also have "... \<le> (2 * log 2 (real m+1) + 1)"
    using assms by simp
  finally show ?thesis by simp
qed

section \<open>Integers\<close>

definition I\<^sub>e :: "int encoding" where
  "I\<^sub>e x = N\<^sub>e (nat (if x \<le>0 then (-2 * x) else (2*x-1)))"

text \<open>@{term "I\<^sub>e"} is an encoding for integers using exponential Golomb codes by embedding
the integers into the natural numbers, specifically the positive numbers are embedded into
the odd-numbers and the negative numbers are embedded into the even numbers. The embedding
has the benefit, that the bit count for an integer only depends on its absolute value.\<close>

lemma int_encoding: "is_encoding I\<^sub>e"
proof -
  have "inj (\<lambda>x. nat (if x \<le> 0 then - 2 * x else 2 * x - 1))"
    by (rule inj_onI, auto simp add:eq_nat_nat_iff, presburger)
  thus ?thesis
    unfolding I\<^sub>e_def
    by (intro exp_golomb_encoding encoding_compose_2[where f="N\<^sub>e"])
      auto
qed

lemma int_bit_count: "bit_count (I\<^sub>e n) = 2 * \<lfloor>log 2 (2*\<bar>n\<bar>+1)\<rfloor> +1"
proof -
  have a:"m > 0 \<Longrightarrow>
    \<lfloor>log (real 2) (real (2 * m))\<rfloor> = \<lfloor>log (real 2) (real (2 * m + 1))\<rfloor>"
    for m :: nat by (rule  floor_log_eq_if, auto)
  have "n > 0 \<Longrightarrow>
    \<lfloor>log 2 (2 * real_of_int n)\<rfloor> = \<lfloor>log 2 (2 * real_of_int n + 1)\<rfloor>"
    using  a[where m="nat n"] by (simp add:add.commute)
  thus ?thesis
    by (simp add:I\<^sub>e_def exp_golomb_bit_count_exact floorlog_def)
qed

lemma int_bit_count_1:
  assumes "abs n > 0"
  shows "bit_count (I\<^sub>e n) = 2 * \<lfloor>log 2 \<bar>n\<bar>\<rfloor> +3"
proof -
  have a:"m > 0 \<Longrightarrow>
    \<lfloor>log (real 2) (real (2 * m))\<rfloor> = \<lfloor>log (real 2) (real (2 * m + 1))\<rfloor>"
    for m :: nat by (rule  floor_log_eq_if, auto)
  have "n < 0 \<Longrightarrow>
    \<lfloor>log 2 (-2 * real_of_int n)\<rfloor> = \<lfloor>log 2 (1-2 * real_of_int n)\<rfloor>"
    using a[where m="nat (-n)"] by (simp add:add.commute)
  hence "bit_count (I\<^sub>e n) = 2 * \<lfloor>log 2 (2*real_of_int \<bar>n\<bar>)\<rfloor> +1"
    using assms
    by (simp add:I\<^sub>e_def exp_golomb_bit_count_exact floorlog_def)
  also have "... = 2 * \<lfloor>log 2 \<bar>n\<bar>\<rfloor> + 3"
    using assms by (subst log_mult, auto)
  finally show ?thesis by simp
qed

lemma int_bit_count_est_1:
  assumes "\<bar>n\<bar> \<le> r"
  shows "bit_count (I\<^sub>e n) \<le> 2 * log 2 (r+1) +3"
proof (cases "abs n > 0")
  case True
  have "real_of_int \<lfloor>log 2 \<bar>real_of_int n\<bar>\<rfloor> \<le> log 2  \<bar>real_of_int n\<bar>"
    using of_int_floor_le by blast
  also have "... \<le> log 2 (real_of_int r+1)"
    using True assms by force
  finally have
    "real_of_int \<lfloor>log 2 \<bar>real_of_int n\<bar>\<rfloor> \<le> log 2 (real_of_int r + 1)"
    by simp
  then show ?thesis
    using True assms by (simp add:int_bit_count_1)
next
  case False
  have "r \<ge> 0" using assms by simp
  moreover have "n = 0" using False by simp
  ultimately show ?thesis by (simp add:I\<^sub>e_def exp_golomb_bit_count_exact)
qed

lemma int_bit_count_est:
  assumes "\<bar>n\<bar> \<le> r"
  shows "bit_count (I\<^sub>e n) \<le> 2 * log 2 (2*r+1) +1"
proof -
  have "bit_count (I\<^sub>e n) \<le> 2 * log 2 (2*\<bar>n\<bar>+1) +1"
    by (simp add:int_bit_count)
  also have "... \<le> 2 * log 2 (2* r + 1) + 1"
    using assms by simp
  finally show ?thesis by simp
qed

section \<open>Lists\<close>

definition Lf\<^sub>e where
  "Lf\<^sub>e e n xs =
    (if length xs = n
      then fold (\<lambda>x y. opt_append y (e x)) xs (Some [])
      else None)"

text \<open>@{term "Lf\<^sub>e e n"} is an encoding for lists of length @{term"n"},
where the elements are encoding using the encoder @{term "e"}.\<close>

lemma fixed_list_encoding:
  assumes "is_encoding e"
  shows "is_encoding (Lf\<^sub>e e n)"
proof (induction n)
  case 0
  then show ?case
    by (rule is_encodingI_2, simp_all add:Lf\<^sub>e_def opt_comp_def split:if_splits)
next
  case (Suc n)
  show ?case
  proof (rule is_encodingI_2)
    fix x y
    assume a:"opt_comp (Lf\<^sub>e e (Suc n) x) (Lf\<^sub>e e (Suc n) y)"
    have b:"length x = Suc n" using a
      by (cases "length x = Suc n", simp_all add:Lf\<^sub>e_def opt_comp_def)
    then obtain x1 x2 where x_def: "x = x1@[x2]" "length x1 = n"
      by (metis length_append_singleton lessI nat.inject order.refl
          take_all take_hd_drop)
    have c:"length y = Suc n" using a
      by (cases "length y = Suc n", simp_all add:Lf\<^sub>e_def opt_comp_def)
    then obtain y1 y2 where y_def: "y = y1@[y2]" "length y1 = n"
      by (metis length_append_singleton lessI nat.inject order.refl
          take_all take_hd_drop)
    have d: "opt_comp (opt_append (Lf\<^sub>e e n x1) (e x2))
      (opt_append (Lf\<^sub>e e n y1) (e y2)) "
      using a b c by (simp add:Lf\<^sub>e_def x_def y_def)
    hence "opt_comp (Lf\<^sub>e e n x1)  (Lf\<^sub>e e n y1)"
      using opt_comp_append opt_comp_append_2 by blast
    hence e:"x1 = y1"
      using is_encodingD[OF Suc] by blast
    hence "opt_comp (e x2) (e y2)"
      using opt_comp_append_3 d by simp
    hence "x2 = y2"
      using is_encodingD[OF assms] by blast
    thus "x = y" using e x_def y_def by simp
  qed
qed

lemma fixed_list_bit_count:
  "bit_count (Lf\<^sub>e e n xs) =
    (if length xs = n then (\<Sum>x \<leftarrow> xs. (bit_count (e x))) else \<infinity>)"
proof (induction n arbitrary: xs)
  case 0
  then show ?case by (simp add:Lf\<^sub>e_def)
next
  case (Suc n)
  show ?case
  proof (cases "length xs = Suc n")
    case True
    then obtain x1 x2 where x_def: "xs = x1@[x2]" "length x1 = n"
      by (metis length_append_singleton lessI nat.inject order.refl
          take_all take_hd_drop)
    have "bit_count (Lf\<^sub>e e n x1) = (\<Sum>x\<leftarrow>x1. bit_count (e x))"
      using x_def(2) Suc by simp
    then show ?thesis by (simp add:Lf\<^sub>e_def x_def bit_count_append)
  next
    case False
    then show ?thesis by (simp add:Lf\<^sub>e_def)
  qed
qed

definition L\<^sub>e
  where "L\<^sub>e e xs = (Nu\<^sub>e \<Join>\<^sub>e (\<lambda>n. Lf\<^sub>e e n)) (length xs, xs)"

text \<open>@{term "L\<^sub>e e"} is an encoding for arbitrary length lists, where the elements are encoding using the
encoder @{term "e"}.\<close>

lemma list_encoding:
  assumes "is_encoding e"
  shows "is_encoding (L\<^sub>e e)"
proof -
  have "inj (\<lambda>xs. (length xs, xs))"
    by (simp add: inj_on_def)

  hence "is_encoding (\<lambda>xs. L\<^sub>e e xs)"
    using assms unfolding L\<^sub>e_def
    by (intro encoding_compose_2[where g=" (\<lambda>x. (length x, x))"]
        dependent_encoding unary_encoding fixed_list_encoding) auto
  thus ?thesis by simp
qed

lemma sum_list_triv_ereal:
  fixes a :: ereal
  shows "sum_list (map (\<lambda>_. a) xs) = length xs * a"
  apply (cases a, simp add:sum_list_triv)
  by (induction xs, simp, simp)+

lemma list_bit_count:
  "bit_count (L\<^sub>e e xs) = (\<Sum>x \<leftarrow> xs. bit_count (e x) + 1) + 1"
proof -
  have "bit_count (L\<^sub>e e xs) =
    ereal (1 + real (length xs)) + (\<Sum>x\<leftarrow>xs. bit_count (e x))"
    by (simp add: L\<^sub>e_def dependent_bit_count fixed_list_bit_count unary_nat_bit_count)
  also have "... = (\<Sum>x\<leftarrow>xs. bit_count (e x)) +  (\<Sum>x \<leftarrow> xs. 1) + 1"
    by (simp add:ac_simps group_cancel.add1 sum_list_triv_ereal)
  also have "... = (\<Sum>x \<leftarrow> xs. bit_count (e x) + 1) + 1"
    by (simp add:sum_list_addf)
  finally show ?thesis by simp
qed

section \<open>Functions\<close>

definition encode_fun :: "'a list \<Rightarrow> 'b encoding \<Rightarrow> ('a \<Rightarrow> 'b) encoding"
  (infixr "\<rightarrow>\<^sub>e" 65)  where
  "encode_fun xs e f =
    (if f \<in> extensional (set xs)
      then (Lf\<^sub>e e (length xs) (map f xs))
      else None)"

text \<open>@{term "xs \<rightarrow>\<^sub>e e"} is an encoding for functions whose domain is @{term "set xs"},
where the values are encoding using the encoder @{term "e"}.\<close>

lemma fun_encoding:
  assumes "is_encoding e"
  shows "is_encoding (xs \<rightarrow>\<^sub>e e)"
proof -
  have a:"inj_on (\<lambda>x. map x xs) {x. x \<in> extensional (set xs)}"
    by (rule inj_onI) (simp add: extensionalityI)
  have "is_encoding (\<lambda>x. (xs \<rightarrow>\<^sub>e e) x)"
    unfolding encode_fun_def
    by (intro encoding_compose[where f="Lf\<^sub>e e (length xs)"]
        fixed_list_encoding assms a)
  thus ?thesis by simp
qed

lemma fun_bit_count:
  "bit_count ((xs \<rightarrow>\<^sub>e e) f) =
    (if f \<in> extensional (set xs) then (\<Sum>x \<leftarrow> xs. bit_count (e (f x))) else \<infinity>)"
  by (simp add:encode_fun_def fixed_list_bit_count comp_def)

lemma fun_bit_count_est:
  assumes "f \<in> extensional (set xs)"
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> bit_count (e (f x)) \<le> a"
  shows "bit_count  ((xs \<rightarrow>\<^sub>e e) f)  \<le> ereal (real (length xs)) * a"
proof -
  have "bit_count  ((xs \<rightarrow>\<^sub>e e) f) = (\<Sum>x \<leftarrow> xs. bit_count (e (f x)))"
    using assms(1) by (simp add:fun_bit_count)
  also have "... \<le> (\<Sum>x \<leftarrow> xs. a)"
    by (intro sum_list_mono assms(2), simp)
  also have "... =  ereal (real (length xs)) * a"
    by (simp add:sum_list_triv_ereal)
  finally show ?thesis by simp
qed

section \<open>Finite Sets\<close>

definition S\<^sub>e :: "'a encoding \<Rightarrow> 'a set encoding" where
  "S\<^sub>e e S =
    (if finite S \<and> S \<subseteq> dom e
      then (L\<^sub>e e (linorder.sorted_key_list_of_set (\<le>) (the \<circ> e) S))
      else None)"

text \<open>@{term "S\<^sub>e e"} is an encoding for finite sets whose elements are encoded using the
  encoder @{term "e"}.\<close>

lemma set_encoding:
  assumes "is_encoding e"
  shows "is_encoding (S\<^sub>e e)"
proof -
  have a:"inj_on (the \<circ> e) (dom e)"
    using inj_on_def
    by (intro comp_inj_on encoding_imp_inj assms, fastforce)

  interpret folding_insort_key "(\<le>)" "(<)" "(dom e)" "(the \<circ> e)"
    using a by (unfold_locales) auto
  have "is_encoding (\<lambda>S. S\<^sub>e e S)"
    unfolding S\<^sub>e_def using sorted_key_list_of_set_inject
    by (intro encoding_compose[where f="L\<^sub>e e"] list_encoding assms(1) inj_onI, simp)
  thus ?thesis by simp
qed

lemma set_bit_count:
  assumes "is_encoding e"
  shows "bit_count (S\<^sub>e e S) = (if finite S then (\<Sum>x \<in> S. bit_count (e x)+1)+1 else \<infinity>)"
proof (cases "finite S")
  case f:True
  have "bit_count (S\<^sub>e e S) = (\<Sum>x\<in>S. bit_count (e x)+1)+1"
  proof (cases "S \<subseteq> dom e")
    case True

    have a:"inj_on (the \<circ> e) (dom e)"
      using inj_on_def by (intro comp_inj_on encoding_imp_inj[OF assms], fastforce)

    interpret folding_insort_key "(\<le>)" "(<)" "(dom e)" "(the \<circ> e)"
      using a by (unfold_locales) auto

    have b:"distinct (linorder.sorted_key_list_of_set (\<le>) (the \<circ> e) S)"
      (is "distinct ?l") using distinct_sorted_key_list_of_set True
        distinct_if_distinct_map by auto

    have "bit_count (S\<^sub>e e S) = (\<Sum>x\<leftarrow>?l. bit_count (e x) + 1) + 1"
      using f True by (simp add:S\<^sub>e_def list_bit_count)
    also have "... = (\<Sum>x\<in>S. bit_count (e x)+1)+1"
      by (simp add: sum_list_distinct_conv_sum_set[OF b]
          set_sorted_key_list_of_set[OF True f])
    finally show ?thesis by simp
  next
    case False
    hence "\<exists>i\<in>S. e i = None" by force
    hence "\<exists>i\<in>S. bit_count (e i) = \<infinity>" by force
    hence "(\<Sum>x\<in>S. bit_count (e x) + 1) = \<infinity>"
      by (simp add:sum_Pinfty f)
    then show ?thesis using False by (simp add:S\<^sub>e_def)
  qed
  thus ?thesis using f by simp
next
  case False
  then show ?thesis by (simp add:S\<^sub>e_def)
qed

lemma sum_triv_ereal:
  fixes a :: ereal
  assumes "finite S"
  shows "(\<Sum>_ \<in> S. a) = card S * a"
proof (cases a)
  case (real r)
  then show ?thesis by simp
next
  case PInf
  show ?thesis using assms PInf
    by (induction S rule:finite_induct, auto)
next
  case MInf
  show ?thesis using assms MInf
    by (induction S rule:finite_induct, auto)
qed

lemma set_bit_count_est:
  assumes "is_encoding f"
  assumes "finite S"
  assumes "card S \<le> m"
  assumes "0 \<le> a"
  assumes "\<And>x. x \<in> S \<Longrightarrow> bit_count (f x) \<le> a"
  shows "bit_count (S\<^sub>e f S) \<le> ereal (real m) * (a+1) + 1"
proof -
  have "bit_count (S\<^sub>e f S) = (\<Sum>x\<in>S. bit_count (f x) + 1) + 1"
    using assms by (simp add:set_bit_count)
  also have "... \<le> (\<Sum>x\<in>S. a + 1) + 1"
    using assms by (intro sum_mono add_mono) auto
  also have "... = ereal (real (card S)) * (a + 1) + 1"
    by (simp add:sum_triv_ereal[OF assms(2)])
  also have "... \<le> ereal (real m) * (a+1) + 1"
    using assms(3,4) by (intro add_mono ereal_mult_right_mono) auto
  finally show ?thesis by simp
qed

section \<open>Floating point numbers\label{sec:float_enc}\<close>
definition F\<^sub>e where "F\<^sub>e f = (I\<^sub>e \<times>\<^sub>e I\<^sub>e) (mantissa f,exponent f)"

lemma float_encoding:
  "is_encoding F\<^sub>e"
proof -
  have "inj (\<lambda>x. (mantissa x, exponent x))" (is "inj ?g")
  proof (rule injI)
    fix x y
    assume "(mantissa x, exponent x) = (mantissa y, exponent y)"
    hence "real_of_float x = real_of_float y"
      by (simp add:mantissa_exponent)
    thus "x = y"
      by (metis real_of_float_inverse)
  qed
  thus "is_encoding (\<lambda>f. F\<^sub>e f)"
    unfolding F\<^sub>e_def
    by (intro encoding_compose_2[where g="?g"]
        dependent_encoding int_encoding) auto
qed

lemma suc_n_le_2_pow_n:
  fixes n :: nat
  shows "n + 1 \<le> 2 ^ n"
  by (induction n, simp, simp)

lemma float_bit_count_1:
  "bit_count (F\<^sub>e f) \<le> 6 + 2 * (log 2 (\<bar>mantissa f\<bar> + 1) +
    log 2 (\<bar>exponent f\<bar> + 1))" (is "?lhs \<le> ?rhs")
proof -
  have "?lhs = bit_count (I\<^sub>e (mantissa f)) +
    bit_count (I\<^sub>e (exponent f))"
    by (simp add:F\<^sub>e_def dependent_bit_count)
  also have "... \<le>
    ereal (2 * log 2 (real_of_int (\<bar>mantissa f\<bar> + 1)) + 3) +
    ereal (2 * log 2 (real_of_int (\<bar>exponent f\<bar> + 1)) + 3)"
    by (intro int_bit_count_est_1 add_mono) auto
  also have "... = ?rhs"
    by simp
  finally show ?thesis by simp
qed

text \<open>The following establishes an estimate for the bit count of a floating
point number in non-normalized representation:\<close>

lemma float_bit_count_2:
  fixes m :: int
  fixes e :: int
  defines "f \<equiv> float_of (m * 2 powr e)"
  shows "bit_count (F\<^sub>e f) \<le>
    6 + 2 * (log 2 (\<bar>m\<bar> + 2) + log 2 (\<bar>e\<bar> + 1))"
proof -
  have b:" (r + 1) * int i \<le> r * (2 ^ i - 1) + 1"
    if b_assms: "r \<ge> 1" for r :: int and i :: nat
  proof (cases "i > 0")
    case True
    have "(r + 1) * int i = r * i + 2 * int ((i-1)+1) - i"
      using True by (simp add:algebra_simps)
    also have "... \<le> r * i + int (2^1) * int (2^(i-1)) - i"
      using b_assms
      by (intro add_mono diff_mono mult_mono of_nat_mono suc_n_le_2_pow_n)
        simp_all
    also have "... = r * i + 2^i - i"
      using True
      by (subst of_nat_mult[symmetric], subst power_add[symmetric])
        simp
    also have "... = r *i + 1 * (2 ^ i - int i - 1) + 1"  by simp
    also have "... \<le> r *i + r * (2 ^ i - int i - 1) + 1"
      using b_assms
      by (intro add_mono mult_mono, simp_all)
    also have "... = r * (2 ^ i - 1) + 1"
      by (simp add:algebra_simps)
    finally show ?thesis by simp
  next
    case False
    hence "i = 0" by simp
    then show ?thesis by simp
  qed

  have a:"log 2 (\<bar>mantissa f\<bar> + 1) + log 2 (\<bar>exponent f\<bar> + 1) \<le>
    log 2 (\<bar>m\<bar>+2) + log 2 (\<bar>e\<bar>+1)"
  proof (cases "f=0")
    case True then show ?thesis by simp
  next
    case False
    moreover have "f = Float m e"
      by (simp add:f_def Float.abs_eq)
    ultimately obtain i :: nat
      where m_def: "m = mantissa f * 2 ^ i"
        and e_def: "e = exponent f - i"
      using denormalize_shift by blast

    have mantissa_ge_1: "1 \<le> \<bar>mantissa f\<bar>"
      using False mantissa_noteq_0 by fastforce

    have "(\<bar>mantissa f\<bar> + 1) * (\<bar>exponent f\<bar> + 1) =
      (\<bar>mantissa f\<bar> + 1) * (\<bar>e+i\<bar>+1)"
      by (simp add:e_def)
    also have "...  \<le> (\<bar>mantissa f\<bar> + 1) * ((\<bar>e\<bar>+\<bar>i\<bar>)+1)"
      by (intro mult_mono add_mono, simp_all)
    also have "... = (\<bar>mantissa f\<bar> + 1) * ((\<bar>e\<bar>+1)+i)"
      by simp
    also have "... = (\<bar>mantissa f\<bar> + 1) * (\<bar>e\<bar>+1) + (\<bar>mantissa f\<bar>+1)*i"
      by (simp add:algebra_simps)
    also have "... \<le> (\<bar>mantissa f\<bar> + 1) * (\<bar>e\<bar>+1) + (\<bar>mantissa f\<bar> * (2^i-1)+1)"
      by (intro add_mono b mantissa_ge_1, simp)
    also have "... = (\<bar>mantissa f\<bar> + 1) * (\<bar>e\<bar>+1) + (\<bar>mantissa f\<bar> * (2^i-1)+1)*(1)"
      by simp
    also have
      "... \<le> (\<bar>mantissa f\<bar> + 1) * (\<bar>e\<bar>+1) + (\<bar>mantissa f\<bar>*  (2^i-1)+1)*(\<bar>e\<bar>+1)"
      by (intro add_mono mult_left_mono, simp_all)
    also have "... = ((\<bar>mantissa f\<bar> + 1)+(\<bar>mantissa f\<bar>*  (2^i-1)+1))*(\<bar>e\<bar>+1)"
      by (simp add:algebra_simps)
    also have "... = (\<bar>mantissa f\<bar>*2^i+2)*(\<bar>e\<bar>+1)"
      by (simp add:algebra_simps)
    also have "... = (\<bar>m\<bar>+2)*(\<bar>e\<bar>+1)"
      by (simp add:m_def abs_mult)
    finally have "(\<bar>mantissa f\<bar> + 1) * (\<bar>exponent f\<bar> + 1) \<le> (\<bar>m\<bar>+2)*(\<bar>e\<bar>+1)"
      by simp

    hence "(\<bar>real_of_int (mantissa f)\<bar> + 1) * (\<bar>of_int (exponent f)\<bar> + 1) \<le>
      (\<bar>of_int m\<bar>+2)*(\<bar>of_int e\<bar>+1)"
      by (simp flip:of_int_abs) (metis (mono_tags, opaque_lifting) numeral_One
          of_int_add of_int_le_iff of_int_mult of_int_numeral)
    then show ?thesis by (simp add:log_mult[symmetric])
  qed
  have "bit_count (F\<^sub>e f) \<le>
    6 + 2 * (log 2 (\<bar>mantissa f\<bar> + 1) + log 2 (\<bar>exponent f\<bar> + 1))"
    using float_bit_count_1 by simp
  also have "... \<le> 6 + 2 * (log 2 (\<bar>m\<bar> + 2) + log 2 (\<bar>e\<bar> + 1))"
    using a by simp
  finally show ?thesis by simp
qed

lemma float_bit_count_zero:
  "bit_count (F\<^sub>e (float_of 0)) = 2"
  by (simp add:F\<^sub>e_def dependent_bit_count int_bit_count
      zero_float.abs_eq[symmetric])



end