(*
  File:      Perfect_Fields/Perfect_Fields.thy
  Authors:   Katharina Kreuzer (TU München)
             Manuel Eberl (University of Innsbruck)

  Typeclasses for fields of prime characteristic
  Frobenius endomorphism on a field type
  Fields with a surjective Frobenius endomorphism
  Typeclass for perfect fields and some basic results about them
*)
section \<open>Perfect Fields\<close>
theory Perfect_Fields
imports
  "Berlekamp_Zassenhaus.Finite_Field" 
  Perfect_Field_Library
begin

subsection \<open>Rings and fields with prime characteristic\<close>

text \<open>
  We introduce some type classes for rings and fields with prime characteristic.
\<close>

class semiring_prime_char = semiring_1 +
  assumes prime_char_aux: "\<exists>n. prime n \<and> of_nat n = (0 :: 'a)"
begin

lemma CHAR_pos [intro, simp]: "CHAR('a) > 0"
  using local.CHAR_pos_iff local.prime_char_aux prime_gt_0_nat by blast

lemma CHAR_nonzero [simp]: "CHAR('a) \<noteq> 0"
  using CHAR_pos by auto

lemma CHAR_prime [intro, simp]: "prime CHAR('a)"
  by (metis (mono_tags, lifting) gcd_nat.order_iff_strict local.of_nat_1 local.of_nat_eq_0_iff_char_dvd
        local.one_neq_zero local.prime_char_aux prime_nat_iff)

end

lemma semiring_prime_charI [intro?]:
  "prime CHAR('a :: semiring_1) \<Longrightarrow> OFCLASS('a, semiring_prime_char_class)"
  by standard auto


lemma idom_prime_charI [intro?]:
  assumes "CHAR('a :: idom) > 0"
  shows   "OFCLASS('a, semiring_prime_char_class)"
proof
  show "prime CHAR('a)"
    using assms prime_CHAR_semidom by blast
qed

class comm_semiring_prime_char = comm_semiring_1 + semiring_prime_char
class comm_ring_prime_char = comm_ring_1 + semiring_prime_char
begin
subclass comm_semiring_prime_char ..
end
class idom_prime_char = idom + semiring_prime_char
begin
subclass comm_ring_prime_char ..
end

class field_prime_char = field +
  assumes pos_char_exists: "\<exists>n>0. of_nat n = (0 :: 'a)"
begin
subclass idom_prime_char
  apply standard
  using pos_char_exists local.CHAR_pos_iff local.of_nat_CHAR local.prime_CHAR_semidom by blast
end


lemma field_prime_charI [intro?]:
  "n > 0 \<Longrightarrow> of_nat n = (0 :: 'a :: field) \<Longrightarrow> OFCLASS('a, field_prime_char_class)"
  by standard auto

lemma field_prime_charI' [intro?]:
  "CHAR('a :: field) > 0 \<Longrightarrow> OFCLASS('a, field_prime_char_class)"
  by standard auto


text \<open>
  Typical functors like polynomials, formal power seires, and formal Laurent series
  preserve the characteristic of the coefficient ring.
\<close>
instance poly :: ("{semiring_prime_char,comm_semiring_1}") semiring_prime_char
  by (rule semiring_prime_charI) auto
instance poly :: ("{comm_semiring_prime_char,comm_semiring_1}") comm_semiring_prime_char
  by standard
instance poly :: ("{comm_ring_prime_char,comm_semiring_1}") comm_ring_prime_char
  by standard
instance poly :: ("{idom_prime_char,comm_semiring_1}") idom_prime_char
  by standard

instance fps :: ("{semiring_prime_char,comm_semiring_1}") semiring_prime_char
  by (rule semiring_prime_charI) auto
instance fps :: ("{comm_semiring_prime_char,comm_semiring_1}") comm_semiring_prime_char
  by standard
instance fps :: ("{comm_ring_prime_char,comm_semiring_1}") comm_ring_prime_char
  by standard
instance fps :: ("{idom_prime_char,comm_semiring_1}") idom_prime_char
  by standard

instance fls :: ("{semiring_prime_char,comm_semiring_1}") semiring_prime_char
  by (rule semiring_prime_charI) auto
instance fls :: ("{comm_semiring_prime_char,comm_semiring_1}") comm_semiring_prime_char
  by standard
instance fls :: ("{comm_ring_prime_char,comm_semiring_1}") comm_ring_prime_char
  by standard
instance fls :: ("{idom_prime_char,comm_semiring_1}") idom_prime_char
  by standard
instance fls :: ("{field_prime_char,comm_semiring_1}") field_prime_char
  by (rule field_prime_charI') auto


subsection \<open>Finite fields\<close>

class finite_field = field_prime_char + finite

lemma finite_fieldI [intro?]:
  assumes "finite (UNIV :: 'a :: field set)"
  shows   "OFCLASS('a, finite_field_class)"
proof standard
  show "\<exists>n>0. of_nat n = (0 :: 'a)"
    using assms prime_CHAR_semidom[where ?'a = 'a] finite_imp_CHAR_pos[OF assms]
    by (intro exI[of _ "CHAR('a)"]) auto
qed fact+

class enum_finite_field = finite_field +
  fixes enum_finite_field :: "nat \<Rightarrow> 'a"
  assumes enum_finite_field: "enum_finite_field ` {..<CARD('a)} = UNIV"
begin

lemma inj_on_enum_finite_field: "inj_on enum_finite_field {..<CARD('a)}"
  using enum_finite_field by (simp add: eq_card_imp_inj_on)

end

instance mod_ring :: (prime_card) finite_field
  by standard simp_all

instantiation mod_ring :: (prime_card) enum_finite_field
begin

definition enum_finite_field_mod_ring :: "nat \<Rightarrow> 'a mod_ring" where
  "enum_finite_field_mod_ring n = of_int_mod_ring (int n)"

instance proof
  interpret type_definition "Rep_mod_ring :: 'a mod_ring \<Rightarrow> int" Abs_mod_ring "{0..<CARD('a)}"
    by (rule type_definition_mod_ring)
  have "enum_finite_field ` {..<CARD('a mod_ring)} = of_int_mod_ring ` int ` {..<CARD('a mod_ring)}"
    unfolding enum_finite_field_mod_ring_def by (simp add: image_image o_def)
  also have "int ` {..<CARD('a mod_ring)} = {0..<int CARD('a mod_ring)}"
    by (simp add: image_atLeastZeroLessThan_int)
  also have "of_int_mod_ring ` \<dots> = (Abs_mod_ring ` \<dots> :: 'a mod_ring set)"
    by (intro image_cong refl) (auto simp: of_int_mod_ring_def)
  also have "\<dots> = (UNIV :: 'a mod_ring set)"
    using Abs_image by simp
  finally show "enum_finite_field ` {..<CARD('a mod_ring)} = (UNIV :: 'a mod_ring set)" .
qed

end



text \<open>
  On a finite field with \<open>n\<close> elements, taking the \<open>n\<close>-th power of an element
  is the identity. This is an obvious consequence of the fact that the multiplicative group of
  the field is a finite group of order \<open>n - 1\<close>, so \<open>x^n = 1\<close> for any non-zero \<open>x\<close>.

  Note that this result is sharp in the sense that the multiplicative group of a
  finite field is cyclic, i.e.\ it contains an element of order \<open>n - 1\<close>.
  (We don't prove this here.)
\<close>
lemma finite_field_power_card_eq_same:
  fixes x :: "'a :: finite_field"
  shows   "x ^ CARD('a) = x"
proof (cases "x = 0")
  case False
  let ?R = "\<lparr>carrier = (UNIV :: 'a set), monoid.mult = (*), one = 1, zero = 0, add = (+)\<rparr>"
  interpret field "?R" rewrites "([^]\<^bsub>?R\<^esub>) = (^)"
  proof -
    show "field ?R"
      by unfold_locales (auto simp: Units_def add_eq_0_iff ring_distribs
                              intro!: exI[of _ "inverse x" for x] left_inverse right_inverse)
    have "x [^]\<^bsub>?R\<^esub> n = x ^ n" for x n
      by (induction n) auto
    thus "([^]\<^bsub>?R\<^esub>) = (^)"
      by blast
  qed

  note fin [intro] = finite_class.finite_UNIV[where ?'a = 'a]
  have "x ^ (CARD('a) - 1) * x = x ^ CARD('a)"
    using finite_UNIV_card_ge_0 power_minus_mult by blast
  also have "x ^ (CARD('a) - 1) = 1"
    using units_power_order_eq_one[of x] fin False
    by (simp add: field_Units)
  finally show ?thesis
    by simp
qed (use finite_class.finite_UNIV[where ?'a = 'a] in \<open>auto simp: card_gt_0_iff\<close>)

lemma finite_field_power_card_power_eq_same:
  fixes x :: "'a :: finite_field"
  assumes "m = CARD('a) ^ n"
  shows   "x ^ m = x"
  unfolding assms
  by (induction n) (simp_all add: finite_field_power_card_eq_same power_mult)


typedef (overloaded) 'a :: semiring_1 ring_char = "if CHAR('a) = 0 then UNIV else {0..<CHAR('a)}"
  by auto

lemma CARD_ring_char [simp]: "CARD ('a :: semiring_1 ring_char) = CHAR('a)"
proof -
  let ?A = "if CHAR('a) = 0 then UNIV else {0..<CHAR('a)}"
  interpret type_definition "Rep_ring_char :: 'a ring_char \<Rightarrow> nat" Abs_ring_char ?A
    by (rule type_definition_ring_char)
  from card show ?thesis
    by auto
qed

instance ring_char :: (semiring_prime_char) nontriv
proof
  show "CARD('a ring_char) > 1"
    using prime_nat_iff by auto
qed

instance ring_char :: (semiring_prime_char) prime_card
proof
  from CARD_ring_char show "prime CARD('a ring_char)"
    by auto
qed

lemma to_int_mod_ring_add:
  "to_int_mod_ring (x + y :: 'a :: finite mod_ring) = (to_int_mod_ring x + to_int_mod_ring y) mod CARD('a)"
  by transfer auto

lemma to_int_mod_ring_mult:
  "to_int_mod_ring (x * y :: 'a :: finite mod_ring) = (to_int_mod_ring x * to_int_mod_ring y) mod CARD('a)"
  by transfer auto

lemma of_nat_mod_CHAR [simp]: "of_nat (x mod CHAR('a :: semiring_1)) = (of_nat x :: 'a)"
  by (metis (no_types, opaque_lifting) comm_monoid_add_class.add_0 div_mod_decomp
         mult_zero_right of_nat_CHAR of_nat_add of_nat_mult)

lemma of_int_mod_CHAR [simp]: "of_int (x mod int CHAR('a :: ring_1)) = (of_int x :: 'a)"
  by (simp add: of_int_eq_iff_cong_CHAR)

lemma (in vector_space) bij_betw_representation:
  assumes [simp]: "independent B" "finite B"
  shows   "bij_betw (\<lambda>v. \<Sum>b\<in>B. scale (v b) b) (B \<rightarrow>\<^sub>E UNIV) (span B)"
proof (rule bij_betwI)
  show "(\<lambda>v. \<Sum>b\<in>B. v b *s b) \<in> (B \<rightarrow>\<^sub>E UNIV) \<rightarrow> local.span B"
    (is "?f \<in> _")
    by (auto intro: span_sum span_scale span_base)
  show "(\<lambda>x. restrict (representation B x) B) \<in> local.span B \<rightarrow> B \<rightarrow>\<^sub>E UNIV"
    (is "?g \<in> _") by auto
  show "?g (?f v) = v" if "v \<in> B \<rightarrow>\<^sub>E UNIV" for v
  proof
    fix b :: 'b
    show "?g (?f v) b = v b"
    proof (cases "b \<in> B")
      case b: True
      have "?g (?f v) b = (\<Sum>i\<in>B. local.representation B (v i *s i) b)"
        using b by (subst representation_sum) (auto intro: span_scale span_base)
      also have "\<dots> = (\<Sum>i\<in>B. v i * local.representation B i b)"
        by (intro sum.cong) (auto simp: representation_scale span_base)
      also have "\<dots> = (\<Sum>i\<in>{b}. v i * local.representation B i b)"
        by (intro sum.mono_neutral_right) (auto simp: representation_basis b)
      also have "\<dots> = v b"
        by (simp add: representation_basis b)
      finally show "?g (?f v) b = v b" .
    qed (use that in auto)
  qed
  show "?f (?g v) = v" if "v \<in> span B" for v
    using that by (simp add: sum_representation_eq)
qed

lemma (in vector_space) card_span:
  assumes [simp]: "independent B" "finite B"
  shows   "card (span B) = CARD('a) ^ card B"
proof -
  have "card (B \<rightarrow>\<^sub>E (UNIV :: 'a set)) = card (span B)"
    by (rule bij_betw_same_card, rule bij_betw_representation) fact+
  thus ?thesis
    by (simp add: card_PiE dim_span_eq_card_independent)
qed

lemma (in zero_neq_one) CARD_neq_1: "CARD('a) \<noteq> Suc 0"
proof
  assume "CARD('a) = Suc 0"
  have "{0, 1} \<subseteq> (UNIV :: 'a set)"
    by simp
  also have "is_singleton (UNIV :: 'a set)"
    by (simp add: is_singleton_altdef \<open>CARD('a) = _\<close>)
  then obtain x :: 'a where "UNIV = {x}"
    by (elim is_singletonE)
  finally have "0 = (1 :: 'a)"
    by blast
  thus False
    using zero_neq_one by contradiction
qed

theorem CARD_finite_field_is_CHAR_power: "\<exists>n>0. CARD('a :: finite_field) = CHAR('a) ^ n"
proof -
  define s :: "'a ring_char mod_ring \<Rightarrow> 'a \<Rightarrow> 'a" where
    "s = (\<lambda>x y. of_int (to_int_mod_ring x) * y)"
  interpret vector_space s
    by unfold_locales (auto simp: s_def algebra_simps to_int_mod_ring_add to_int_mod_ring_mult)
  obtain B where B: "independent B" "span B = UNIV"
    by (rule basis_exists[of UNIV]) auto
  have [simp]: "finite B"
    by simp
  have "card (span B) = CHAR('a) ^ card B"
    using B by (subst card_span) auto
  hence *: "CARD('a) = CHAR('a) ^ card B"
    using B by simp
  from * have "card B \<noteq> 0"
    by (auto simp: B(2) CARD_neq_1)
  with * show ?thesis
    by blast
qed


subsection \<open>The Freshman's Dream in rings of non-zero characteristic\<close>

lemma (in comm_semiring_1) freshmans_dream:
  fixes x y :: 'a and n :: nat
  assumes "prime CHAR('a)"
  assumes n_def: "n = CHAR('a)"
  shows   "(x + y) ^ n = x ^ n + y ^ n"
proof -
  interpret comm_semiring_prime_char
    by standard (auto intro!: exI[of _ "CHAR('a)"] assms)
  have "n > 0"
    unfolding n_def by simp
  have "(x + y) ^ n = (\<Sum>k\<le>n. of_nat (n choose k) * x ^ k * y ^ (n - k))"
    by (rule binomial_ring)
  also have "\<dots> = (\<Sum>k\<in>{0,n}. of_nat (n choose k) * x ^ k * y ^ (n - k))"
  proof (intro sum.mono_neutral_right ballI)
    fix k assume "k \<in> {..n} - {0, n}"
    hence k: "k > 0" "k < n"
      by auto
    have "CHAR('a) dvd (n choose k)"
      unfolding n_def
      by (rule dvd_choose_prime) (use k in \<open>auto simp: n_def\<close>)
    hence "of_nat (n choose k) = (0 :: 'a)"
      using of_nat_eq_0_iff_char_dvd by blast
    thus "of_nat (n choose k) * x ^ k * y ^ (n - k) = 0"
      by simp
  qed auto
  finally show ?thesis
    using \<open>n > 0\<close> by (simp add: add_ac)
qed

lemma (in comm_semiring_1) freshmans_dream':
  assumes [simp]: "prime CHAR('a)" and "m = CHAR('a) ^ n"
  shows "(x + y :: 'a) ^ m = x ^ m + y ^ m"
  unfolding assms(2)
proof (induction n)
  case (Suc n)
  have "(x + y) ^ (CHAR('a) ^ n * CHAR('a)) = ((x + y) ^ (CHAR('a) ^ n)) ^ CHAR('a)"
    by (rule power_mult)
  thus ?case
    by (simp add: Suc.IH freshmans_dream Groups.mult_ac flip: power_mult)
qed auto

lemma (in comm_semiring_1) freshmans_dream_sum:
  fixes f :: "'b \<Rightarrow> 'a"
  assumes "prime CHAR('a)" and "n = CHAR('a)"
  shows "sum f A ^ n = sum (\<lambda>i. f i ^ n) A"
  using assms
  by (induct A rule: infinite_finite_induct)
     (auto simp add: power_0_left freshmans_dream)

lemma (in comm_semiring_1) freshmans_dream_sum':
  fixes f :: "'b \<Rightarrow> 'a"
  assumes "prime CHAR('a)" "m = CHAR('a) ^ n"
  shows   "sum f A ^ m = sum (\<lambda>i. f i ^ m) A"
  using assms
  by (induction A rule: infinite_finite_induct)
     (auto simp: freshmans_dream' power_0_left)


subsection \<open>The Frobenius endomorphism\<close>

definition (in semiring_1) frob :: "'a \<Rightarrow> 'a" where
  "frob x = x ^ CHAR('a)"

definition (in semiring_1) inv_frob :: "'a \<Rightarrow> 'a" where
  "inv_frob x = (if x \<in> {0, 1} then x else if x \<in> range frob then inv_into UNIV frob x else x)"

lemma (in semiring_1) inv_frob_0 [simp]: "inv_frob 0 = 0"
  and inv_frob_1 [simp]: "inv_frob 1 = 1"
  by (simp_all add: inv_frob_def)

lemma (in semiring_prime_char) frob_0 [simp]: "frob (0 :: 'a) = 0"
  by (simp add: frob_def power_0_left)

lemma (in semiring_1) frob_1 [simp]: "frob 1 = 1"
  by (simp add: frob_def)

lemma (in comm_semiring_1) frob_mult: "frob (x * y) = frob x * frob (y :: 'a)"
  by (simp add: frob_def power_mult_distrib)

lemma (in comm_semiring_1)
  frob_add: "prime CHAR('a) \<Longrightarrow> frob (x + y :: 'a) = frob x + frob (y :: 'a)"
  by (simp add: frob_def freshmans_dream)

lemma (in comm_ring_1) frob_uminus: "prime CHAR('a) \<Longrightarrow> frob (-x :: 'a) = -frob x"
proof -
  assume "prime CHAR('a)"
  hence "frob (-x) + frob x = 0"
    by (subst frob_add [symmetric]) (auto simp: frob_def power_0_left)
  thus ?thesis
    by (simp add: add_eq_0_iff)
qed

lemma (in comm_ring_prime_char) frob_diff:
  "prime CHAR('a) \<Longrightarrow> frob (x - y :: 'a) = frob x - frob (y :: 'a)"
  using frob_add[of x "-y"] by (simp add: frob_uminus)

interpretation frob_sr: semiring_hom "frob :: 'a :: {comm_semiring_prime_char} \<Rightarrow> 'a"
  by standard (auto simp: frob_add frob_mult)

interpretation frob: ring_hom "frob :: 'a :: {comm_ring_prime_char} \<Rightarrow> 'a"
  by standard auto

interpretation frob: field_hom "frob :: 'a :: {field_prime_char} \<Rightarrow> 'a"
  by standard auto

lemma frob_mod_ring' [simp]: "(x :: 'a :: prime_card mod_ring) ^ CARD('a) = x"
  by (metis CARD_mod_ring finite_field_power_card_eq_same)

lemma frob_mod_ring [simp]: "frob (x :: 'a :: prime_card mod_ring) = x"
  by (simp add: frob_def)

context semiring_1_no_zero_divisors
begin

lemma frob_eq_0D:
  "frob (x :: 'a) = 0 \<Longrightarrow> x = 0"
  by (auto simp: frob_def)

lemma frob_eq_0_iff [simp]:
  "frob (x :: 'a) = 0 \<longleftrightarrow> x = 0 \<and> CHAR('a) > 0"
  by (auto simp: frob_def)

end


context idom_prime_char
begin

lemma inj_frob: "inj (frob :: 'a \<Rightarrow> 'a)"
proof
  fix x y :: 'a
  assume "frob x = frob y"
  hence "frob (x - y) = 0"
    by (simp add: frob_diff del: frob_eq_0_iff)
  thus "x = y"
    by simp
qed

lemma frob_eq_frob_iff [simp]:
  "frob (x :: 'a) = frob y \<longleftrightarrow> x = y"
  using inj_frob by (auto simp: inj_def)

lemma frob_eq_1_iff [simp]: "frob (x :: 'a) = 1 \<longleftrightarrow> x = 1"
  using frob_eq_frob_iff by fastforce

lemma inv_frob_frob [simp]: "inv_frob (frob (x :: 'a)) = x"
  by (simp add: inj_frob inv_frob_def)

lemma frob_inv_frob [simp]:
  assumes "x \<in> range frob"
  shows   "frob (inv_frob x) = (x :: 'a)"
  using assms by (auto simp: inj_frob inv_frob_def)

lemma inv_frob_eqI: "frob y = x \<Longrightarrow> inv_frob x = y"
  using inv_frob_frob local.frob_def by force

lemma inv_frob_eq_0_iff [simp]: "inv_frob (x :: 'a) = 0 \<longleftrightarrow> x = 0"
  using inj_frob by (auto simp: inv_frob_def split: if_splits)

end




class surj_frob = field_prime_char +
  assumes surj_frob [simp]: "surj (frob :: 'a \<Rightarrow> 'a)"
begin

lemma in_range_frob [simp, intro]: "(x :: 'a) \<in> range frob"
  using surj_frob by blast

lemma inv_frob_eq_iff [simp]: "inv_frob (x :: 'a) = y \<longleftrightarrow> frob y = x"
  using frob_inv_frob inv_frob_frob by blast

end


text \<open>
  The following type class describes a field with a surjective Frobenius endomorphism
  that is effectively computable. This includes all finite fields.
\<close>
class inv_frob = surj_frob +
  fixes inv_frob_code :: "'a \<Rightarrow> 'a"
  assumes inv_frob_code: "inv_frob x = inv_frob_code x"

lemmas [code] = inv_frob_code


context finite_field
begin

subclass surj_frob
proof
  show "surj (frob :: 'a \<Rightarrow> 'a)"
    using inj_frob finite_UNIV by (simp add: finite_UNIV_inj_surj)
qed

end


lemma inv_frob_mod_ring [simp]: "inv_frob (x :: 'a :: prime_card mod_ring) = x"
  by (auto simp: frob_def)

instantiation mod_ring :: (prime_card) inv_frob
begin

definition inv_frob_code_mod_ring :: "'a mod_ring \<Rightarrow> 'a mod_ring" where
  "inv_frob_code_mod_ring x = x"

instance 
  by standard (auto simp: inv_frob_code_mod_ring_def)

end



subsection \<open>Inverting the Frobenius endomorphism on polynomials\<close>

text \<open>
  If \<open>K\<close> is a field of prime characteristic \<open>p\<close> with a surjective Frobenius endomorphism,
  every polynomial \<open>P\<close> with \<open>P' = 0\<close> has a \<open>p\<close>-th root.

  To see that, let $\phi(a) = a^p$ denote the Frobenius endomorphism of \<open>K\<close>
  and its extension to \<open>K[X]\<close>.

  If \<open>P' = 0\<close> for some \<open>P \<in> K[X]\<close>, then \<open>P\<close> must be of the form
  \[P = a_0 + a_p x^p + a_{2p} x^{2p} + \ldots + a_{kp} x^{kp}\ .\]
  If we now set
  \[Q := \phi^{-1}(a_0) + \phi^{-1}(a_p) x + \phi^{-1}(a_{2p}) x^2 + \ldots + \phi^{-1}(a_{kp}) x^k\]
  we get $\phi(Q) = P$, i.e.\ $Q$ is the $p$-th root of $P(x)$.
\<close>

lift_definition inv_frob_poly :: "'a :: field poly \<Rightarrow> 'a poly" is
  "\<lambda>p i. if CHAR('a) = 0 then p i else inv_frob (p (i * CHAR('a)) :: 'a)"
proof goal_cases
  case (1 f)
  show ?case
  proof (cases "CHAR('a) > 0")
    case True
    from 1 obtain N where N: "f i = 0" if "i \<ge> N" for i
      using cofinite_eq_sequentially eventually_sequentially by auto
    have "inv_frob (f (i * CHAR('a))) = 0" if "i \<ge> N" for i
    proof -
      have "f (i * CHAR('a)) = 0"
      proof (rule N)
        show "N \<le> i * CHAR('a)"
          using that True 
          by (metis One_nat_def Suc_leI le_trans mult.right_neutral mult_le_mono2)
      qed
      thus "inv_frob (f (i * CHAR('a))) = 0"
        by (auto simp: power_0_left)
    qed
    thus ?thesis using True
      unfolding cofinite_eq_sequentially eventually_sequentially by auto
  qed (use 1 in auto)
qed

lemma coeff_inv_frob_poly [simp]:
  fixes p :: "'a :: field poly"
  assumes "CHAR('a) > 0"
  shows "poly.coeff (inv_frob_poly p) i = inv_frob (poly.coeff p (i * CHAR('a)))"
  using assms by transfer auto

lemma inv_frob_poly_0 [simp]: "inv_frob_poly 0 = 0"
  by transfer (auto simp: fun_eq_iff power_0_left)

lemma inv_frob_poly_1 [simp]: "inv_frob_poly 1 = 1"
  by transfer (auto simp: fun_eq_iff power_0_left)

lemma degree_inv_frob_poly_le:
  fixes p :: "'a :: field poly"
  assumes "CHAR('a) > 0"
  shows "Polynomial.degree (inv_frob_poly p) \<le> Polynomial.degree p div CHAR('a)"
proof (intro degree_le allI impI)
  fix i assume "Polynomial.degree p div CHAR('a) < i"
  hence "i * CHAR('a) > Polynomial.degree p"
    using assms div_less_iff_less_mult by blast
  thus "Polynomial.coeff (inv_frob_poly p) i = 0"
    by (simp add: coeff_eq_0 power_0_left assms)
qed

context
  assumes "SORT_CONSTRAINT('a :: comm_ring_1)"
  assumes prime_char: "prime CHAR('a)"
begin

lemma poly_power_prime_char_as_sum_of_monoms:
  fixes h :: "'a poly"
  shows "h ^ CHAR('a) = (\<Sum>i\<le>Polynomial.degree h. Polynomial.monom (Polynomial.coeff h i ^ CHAR('a)) (CHAR('a)*i))"
proof -
  have "h ^ CHAR('a) = (\<Sum>i\<le>Polynomial.degree h. Polynomial.monom (Polynomial.coeff h i) i) ^ CHAR('a)"
    by (simp add: poly_as_sum_of_monoms)
  also have "... = (\<Sum>i\<le>Polynomial.degree h. (Polynomial.monom (Polynomial.coeff h i) i) ^ CHAR('a))"
    by (simp add: freshmans_dream_sum prime_char)
  also have "... = (\<Sum>i\<le>Polynomial.degree h. Polynomial.monom (Polynomial.coeff h i ^ CHAR('a)) (CHAR('a)*i))"
  proof (rule sum.cong, rule)
    fix x assume x: "x \<in> {..Polynomial.degree h}"
    show "Polynomial.monom (Polynomial.coeff h x) x ^ CHAR('a) = Polynomial.monom (Polynomial.coeff h x ^ CHAR('a)) (CHAR('a) * x)"
      by (unfold poly_eq_iff, auto simp add: monom_power)
  qed
  finally show ?thesis .
qed

lemma coeff_of_prime_char_power [simp]:
  fixes y :: "'a poly"
  shows "poly.coeff (y ^ CHAR('a)) (i * CHAR('a)) = poly.coeff y i ^ CHAR('a)"
  using prime_char
  by (subst poly_power_prime_char_as_sum_of_monoms, subst Polynomial.coeff_sum)
     (auto intro: le_degree simp: power_0_left)

lemma coeff_of_prime_char_power':
  fixes y :: "'a poly"
  shows "poly.coeff (y ^ CHAR('a)) i =
           (if CHAR('a) dvd i then poly.coeff y (i div CHAR('a)) ^ CHAR('a) else 0)"
proof -
  have "poly.coeff (y ^ CHAR('a)) i =
          (\<Sum>j\<le>Polynomial.degree y. Polynomial.coeff (Polynomial.monom (Polynomial.coeff y j ^ CHAR('a)) (CHAR('a) * j)) i)"
    by (subst poly_power_prime_char_as_sum_of_monoms, subst Polynomial.coeff_sum) auto
  also have "\<dots> = (\<Sum>j\<in>(if CHAR('a) dvd i \<and> i div CHAR('a) \<le> Polynomial.degree y then {i div CHAR('a)} else {}).
                    Polynomial.coeff (Polynomial.monom (Polynomial.coeff y j ^ CHAR('a)) (CHAR('a) * j)) i)"
    by (intro sum.mono_neutral_right) (use prime_char in auto)
  also have "\<dots> = (if CHAR('a) dvd i then poly.coeff y (i div CHAR('a)) ^ CHAR('a) else 0)"
  proof (cases "CHAR('a) dvd i \<and> i div CHAR('a) > Polynomial.degree y")
    case True
    hence "Polynomial.coeff y (i div CHAR('a)) ^ CHAR('a) = 0"
      using prime_char by (simp add: coeff_eq_0 zero_power power_0_left)
    thus ?thesis
      by auto
  qed auto
  finally show ?thesis .
qed

end


context
  assumes "SORT_CONSTRAINT('a :: field)"
  assumes pos_char: "CHAR('a) > 0"
begin

interpretation field_prime_char "(/)" inverse "(*)" "1 :: 'a" "(+)" 0 "(-)" uminus
  rewrites "semiring_1.frob 1 (*) (+) (0 :: 'a) = frob" and
           "semiring_1.inv_frob 1 (*) (+) (0 :: 'a) = inv_frob" and
           "semiring_1.semiring_char 1 (+) 0 TYPE('a) = CHAR('a)"
proof unfold_locales
  have *: "class.semiring_1 (1 :: 'a) (*) (+) 0" ..
  have [simp]: "semiring_1.of_nat (1 :: 'a) (+) 0 = of_nat"
    by (auto simp: of_nat_def semiring_1.of_nat_def[OF *])
  thus "\<exists>n>0. semiring_1.of_nat (1 :: 'a) (+) 0 n = 0"
    by (intro exI[of _ "CHAR('a)"]) (use pos_char in auto)
  show "semiring_1.semiring_char 1 (+) 0 TYPE('a) = CHAR('a)"
    by (simp add: fun_eq_iff semiring_char_def semiring_1.semiring_char_def[OF *])
  show [simp]: "semiring_1.frob (1 :: 'a) (*) (+) 0 = frob"
    by (simp add: frob_def semiring_1.frob_def[OF *] fun_eq_iff
                  power.power_def power_def semiring_char_def semiring_1.semiring_char_def[OF *])
  show "semiring_1.inv_frob (1 :: 'a) (*) (+) 0 = inv_frob"
    by (simp add: inv_frob_def semiring_1.inv_frob_def[OF *] fun_eq_iff)
qed

lemma inv_frob_poly_power': "inv_frob_poly (p ^ CHAR('a) :: 'a poly) = p"
  using prime_CHAR_semidom[OF pos_char] pos_char
  by (auto simp: poly_eq_iff simp flip: frob_def)

lemma inv_frob_poly_power:
  fixes p :: "'a poly"
  assumes "is_nth_power CHAR('a) p" and "n = CHAR('a)"
  shows   "inv_frob_poly p ^ CHAR('a) = p"
proof -
  from assms(1) obtain q where q: "p = q ^ CHAR('a)"
    by (elim is_nth_powerE)
  thus ?thesis using assms
    by (simp add: q inv_frob_poly_power')
qed

theorem pderiv_eq_0_imp_nth_power:
  assumes "pderiv (p :: 'a poly) = 0"
  assumes [simp]: "surj (frob :: 'a \<Rightarrow> 'a)"
  shows   "is_nth_power CHAR('a) p"
proof -
  have *: "poly.coeff p n = 0" if n: "\<not>CHAR('a) dvd n" for n
  proof (cases "n = 0")
    case False
    have "poly.coeff (pderiv p) (n - 1) = of_nat n * poly.coeff p n"
      using False by (auto simp: coeff_pderiv)
    with assms and n show "poly.coeff p n = 0"
      by (auto simp: of_nat_eq_0_iff_char_dvd)
  qed (use that in auto)

  have **: "inv_frob_poly p ^ CHAR('a) = p"
  proof (rule poly_eqI)
    fix n :: nat
    show "poly.coeff (inv_frob_poly p ^ CHAR('a)) n = poly.coeff p n"
      using * CHAR_dvd_CARD[where ?'a = 'a] 
      by (subst coeff_of_prime_char_power')
         (auto simp: poly_eq_iff frob_def [symmetric]
                     coeff_of_prime_char_power'[where ?'a = 'a] simp flip: power_mult)
  qed
  
  show ?thesis
    by (subst **[symmetric]) auto
qed

end


subsection \<open>Code generation\<close>

text \<open>
  We now also make this notion of ``taking the \<open>p\<close>-th root of a polynomial''
  executable. For this, we need an auxiliary function that takes a list
  $[x_0, \ldots, x_m]$ and returns the list of every \<open>n\<close>-th element, i.e.\ it
  throws away all elements except those $x_i$ where $i$ is a multiple of $n$.
\<close>

(* TODO: Move this function to a library? *)
fun take_every :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "take_every _ [] = []"
| "take_every n (x # xs) = x # take_every n (drop (n - 1) xs)"

lemma take_every_0 [simp]: "take_every 0 xs = xs"
  by (induction xs) auto

lemma take_every_1 [simp]: "take_every (Suc 0) xs = xs"
  by (induction xs) auto

lemma int_length_take_every: "n > 0 \<Longrightarrow> int (length (take_every n xs)) = ceiling (length xs / n)"
proof (induction n xs rule: take_every.induct)
  case (2 n x xs)
  show ?case
  proof (cases "Suc (length xs) \<ge> n")
    case True
    thus ?thesis using 2
      by (auto simp: dvd_imp_le of_nat_diff diff_divide_distrib split: if_splits)
  next
    case False
    hence "\<lceil>(1 + real (length xs)) / real n\<rceil> = 1"
      by (intro ceiling_unique) auto
    thus ?thesis using False
      by auto
  qed
qed auto

lemma length_take_every:
  "n > 0 \<Longrightarrow> length (take_every n xs) = nat (ceiling (length xs / n))"
  using int_length_take_every[of n xs] by simp

lemma take_every_nth [simp]:
  "n > 0 \<Longrightarrow> i < length (take_every n xs) \<Longrightarrow> take_every n xs ! i = xs ! (n * i)"
proof (induction n xs arbitrary: i rule: take_every.induct)
  case (2 n x xs i)
  show ?case
  proof (cases i)
    case (Suc j)
    have "n - Suc 0 \<le> length xs"
      using Suc "2.prems" nat_le_linear by force
    hence "drop (n - Suc 0) xs ! (n * j) = xs ! (n - 1 + n * j)"
      using Suc by (subst nth_drop) auto
    also have "n - 1 + n * j = n + n * j - 1"
      using \<open>n > 0\<close> by linarith
    finally show ?thesis
      using "2.IH"[of j] "2.prems" Suc by simp
  qed auto
qed auto

lemma coeffs_eq_strip_whileI:
  assumes "\<And>i. i < length xs \<Longrightarrow> Polynomial.coeff p i = xs ! i"
  assumes "p \<noteq> 0 \<Longrightarrow> length xs > Polynomial.degree p"
  shows   "Polynomial.coeffs p = strip_while ((=) 0) xs"
proof (rule coeffs_eqI)
  fix n :: nat
  show "Polynomial.coeff p n = nth_default 0 (strip_while ((=) 0) xs) n"
    using assms
    by (metis coeff_0 coeff_Poly_eq coeffs_Poly le_degree nth_default_coeffs_eq 
      nth_default_eq_dflt_iff nth_default_nth order_le_less_trans)
qed auto

text \<open>This implements the code equation for \<open>inv_frob_poly\<close>.\<close>
lemma inv_frob_poly_code [code]:
  "Polynomial.coeffs (inv_frob_poly (p :: 'a :: field_prime_char poly)) =
     (if CHAR('a) = 0 then Polynomial.coeffs p else 
        map inv_frob (strip_while ((=) 0) (take_every CHAR('a) (Polynomial.coeffs p))))"
    (is "_ = If _ _ ?rhs")
proof (cases "CHAR('a) = 0 \<or> p = 0")
  case False
  from False have "p \<noteq> 0"
    by auto
  have "Polynomial.coeffs (inv_frob_poly p) =
          strip_while ((=) 0) (map inv_frob (take_every CHAR('a) (Polynomial.coeffs p)))"
  proof (rule coeffs_eq_strip_whileI)
    fix i assume i: "i < length (map inv_frob (take_every CHAR('a) (Polynomial.coeffs p)))"
    show "Polynomial.coeff (inv_frob_poly p) i = map inv_frob (take_every CHAR('a) (Polynomial.coeffs p)) ! i"
    proof -
      have "i < length (take_every CHAR('a) (Polynomial.coeffs p))"
        using i by simp
      also have "length (take_every CHAR('a) (Polynomial.coeffs p)) =
                   nat \<lceil>(Polynomial.degree p + 1) / real CHAR('a)\<rceil>"
        using False CHAR_pos[where ?'a = 'a]
        by (simp add: length_take_every length_coeffs)
      finally have "i < real (Polynomial.degree p + 1) / real CHAR('a)"
        by linarith
      hence "real i * real CHAR('a) < real (Polynomial.degree p + 1)"
        using False CHAR_pos[where ?'a = 'a] by (simp add: field_simps)
      hence "i * CHAR('a) \<le> Polynomial.degree p"
        unfolding of_nat_mult [symmetric] by linarith
      hence "Polynomial.coeffs p ! (i * CHAR('a)) = Polynomial.coeff p (i * CHAR('a))"
        using False by (intro coeffs_nth) (auto simp: length_take_every)
      thus ?thesis using False i CHAR_pos[where ?'a = 'a]
        by (auto simp: nth_default_def mult.commute)
    qed
  next
    assume nz: "inv_frob_poly p \<noteq> 0"
    have "Polynomial.degree (inv_frob_poly p) \<le> Polynomial.degree p div CHAR('a)"
      by (rule degree_inv_frob_poly_le) (fact CHAR_pos)
    also have "\<dots> < nat \<lceil>(real (Polynomial.degree p) + 1) / real CHAR('a)\<rceil>"
      using CHAR_pos[where ?'a = 'a]
      by (metis div_less_iff_less_mult linorder_not_le nat_le_real_less of_nat_0_less_iff
                of_nat_ceiling of_nat_mult pos_less_divide_eq)
    also have "\<dots> = length (take_every CHAR('a) (Polynomial.coeffs p))"
      using CHAR_pos[where ?'a = 'a] \<open>p \<noteq> 0\<close> by (simp add: length_take_every length_coeffs add_ac)
    finally show "length (map inv_frob (take_every CHAR('a) (Polynomial.coeffs p))) > Polynomial.degree (inv_frob_poly p)"
      by simp_all
  qed
  also have "strip_while ((=) 0) (map inv_frob (take_every CHAR('a) (Polynomial.coeffs p))) =
             map inv_frob (strip_while ((=) 0 \<circ> inv_frob) (take_every CHAR('a) (Polynomial.coeffs p)))"
    by (rule strip_while_map)
  also have "(=) 0 \<circ> inv_frob = (=) (0 :: 'a)"
    by (auto simp: fun_eq_iff)
  finally show ?thesis
    using False by metis
qed auto




subsection \<open>Perfect fields\<close>

text \<open>
  We now introduce perfect fields. The textbook definition of a perfect field
  is that every irreducible polynomial is separable, i.e.\ if a polynomial $P$
  has no non-trivial divisors then $\text{gcd}(P, P') = 0$.

  For technical reasons, this is somewhat difficult to express in Isabelle/HOL's typeclass system.
  We therefore use the following much simpler equivalent definition (and prove equivalence later):
  a field is perfect if it either has characteristic 0 or its Frobenius endomorphism
  is surjective.
\<close>

class perfect_field = field +
  assumes perfect_field: "CHAR('a) = 0 \<or> surj (frob :: 'a \<Rightarrow> 'a)"

context field_char_0
begin
subclass perfect_field
  by standard auto
end

context surj_frob
begin
subclass perfect_field
  by standard auto
end

theorem irreducible_imp_pderiv_nonzero:
  assumes "irreducible (p :: 'a :: perfect_field poly)"
  shows   "pderiv p \<noteq> 0"
proof (cases "CHAR('a) = 0")
  case True
  interpret A: semiring_1 "1 :: 'a" "(*)" "(+)" "0 :: 'a" ..
  have *: "class.semiring_1 (1 :: 'a) (*) (+) 0" ..
  interpret A: field_char_0 "(/)" inverse "(*)" "1 :: 'a" "(+)" 0 "(-)" uminus
  proof
    have "inj (of_nat :: nat \<Rightarrow> 'a)"
      by (auto simp: inj_on_def of_nat_eq_iff_cong_CHAR True)
    also have "of_nat = semiring_1.of_nat (1 :: 'a) (+) 0"
      by (simp add: of_nat_def [abs_def] semiring_1.of_nat_def [OF *, abs_def])
    finally show "inj \<dots>" .
  qed

  show ?thesis
  proof
    assume "pderiv p = 0"
    hence **: "poly.coeff p (Suc n) = 0" for n
      by (auto simp: poly_eq_iff coeff_pderiv of_nat_eq_0_iff_char_dvd True simp del: of_nat_Suc)
    have "poly.coeff p n = 0" if "n > 0" for n
      using **[of "n - 1"] that by (cases n) auto
    hence "Polynomial.degree p = 0"
      by force
    thus False
      using assms by force
  qed

next
  case False
  hence [simp]: "surj (frob :: 'a \<Rightarrow> 'a)"
    by (meson perfect_field)

  interpret A: field_prime_char "(/)" inverse "(*)" "1 :: 'a" "(+)" 0 "(-)" uminus
  proof
    have *: "class.semiring_1 1 (*) (+) (0 :: 'a)" ..
    have "semiring_1.of_nat 1 (+) (0 :: 'a) = of_nat"
      by (simp add: fun_eq_iff of_nat_def semiring_1.of_nat_def[OF *])
    thus "\<exists>n>0. semiring_1.of_nat 1 (+) 0 n = (0 :: 'a)"
      by (intro exI[of _ "CHAR('a)"]) (use False in auto)
  qed

  show ?thesis
  proof
    assume "pderiv p = 0"
    hence "is_nth_power CHAR('a) p"
      using pderiv_eq_0_imp_nth_power[of p] surj_frob False by simp
    then obtain q where "p = q ^ CHAR('a)"
      by (elim is_nth_powerE)
    with assms show False
      by auto
  qed
qed

corollary irreducible_imp_separable:
  assumes "irreducible (p :: 'a :: perfect_field poly)"
  shows   "coprime p (pderiv p)"
proof (rule coprimeI)
  fix q assume q: "q dvd p" "q dvd pderiv p"
  have "\<not>p dvd q"
  proof
    assume "p dvd q"
    hence "p dvd pderiv p"
      using q dvd_trans by blast
    hence "Polynomial.degree p \<le> Polynomial.degree (pderiv p)"
      by (rule dvd_imp_degree_le) (use assms irreducible_imp_pderiv_nonzero in auto)
    also have "\<dots> \<le> Polynomial.degree p - 1"
      using degree_pderiv_le by auto
    finally have "Polynomial.degree p = 0"
      by simp
    with assms show False
      using irreducible_imp_pderiv_nonzero is_unit_iff_degree by blast
  qed
  with \<open>q dvd p\<close> show "is_unit q"
    using assms comm_semiring_1_class.irreducibleD' by blast
qed
 
end