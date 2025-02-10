(*  Title:      Uint_Common.thy
    Author:     Andreas Lochbihler, ETH Zurich
    Author:     Florian Haftmann, TU Muenchen
*)

chapter \<open>Common logic auxiliary for all fixed-width word types\<close>

theory Uint_Common
  imports
    "HOL-Library.Word"
    "Word_Lib.Signed_Division_Word"
    "Word_Lib.Most_significant_bit"
    "Word_Lib.Bit_Comprehension"
begin

section \<open>Some abstract nonsense\<close>

lemmas [transfer_rule] =
  identity_quotient
  fun_quotient
  Quotient_integer[folded integer.pcr_cr_eq]

lemma undefined_transfer:
  assumes "Quotient R Abs Rep T"
  shows "T (Rep undefined) undefined"
using assms unfolding Quotient_alt_def by blast

bundle undefined_transfer = undefined_transfer[transfer_rule]


section \<open>Establishing type class instances for type copies of word type\<close>

text \<open>The lifting machinery is not localized, hence the abstract proofs are carried out using morphisms.\<close>

locale word_type_copy =
  fixes of_word :: \<open>'b::len word \<Rightarrow> 'a\<close>
    and word_of :: \<open>'a \<Rightarrow> 'b word\<close>
  assumes type_definition: \<open>type_definition word_of of_word UNIV\<close>
begin

lemma word_of_word:
  \<open>word_of (of_word w) = w\<close>
  using type_definition by (simp add: type_definition_def)

lemma of_word_of [code abstype]:
  \<open>of_word (word_of p) = p\<close>
    \<comment> \<open>Use an abstract type for code generation to disable pattern matching on \<^term>\<open>of_word\<close>.\<close>
  using type_definition by (simp add: type_definition_def)

lemma word_of_eqI:
  \<open>p = q\<close> if \<open>word_of p = word_of q\<close>
proof -
  from that have \<open>of_word (word_of p) = of_word (word_of q)\<close>
    by simp
  then show ?thesis
    by (simp add: of_word_of)
qed

lemma eq_iff_word_of:
  \<open>p = q \<longleftrightarrow> word_of p = word_of q\<close>
  by (auto intro: word_of_eqI)

end

bundle constraintless
begin

declaration \<open>
  let
    val cs = map (rpair NONE o fst o dest_Const)
      [\<^term>\<open>0\<close>, \<^term>\<open>(+)\<close>, \<^term>\<open>uminus\<close>, \<^term>\<open>(-)\<close>,
       \<^term>\<open>1\<close>, \<^term>\<open>(*)\<close>, \<^term>\<open>(div)\<close>, \<^term>\<open>(mod)\<close>,
       \<^term>\<open>HOL.equal\<close>, \<^term>\<open>(\<le>)\<close>, \<^term>\<open>(<)\<close>,
       \<^term>\<open>(dvd)\<close>, \<^term>\<open>of_bool\<close>, \<^term>\<open>numeral\<close>, \<^term>\<open>of_nat\<close>,
       \<^term>\<open>bit\<close>,
       \<^term>\<open>Bit_Operations.not\<close>, \<^term>\<open>Bit_Operations.and\<close>, \<^term>\<open>Bit_Operations.or\<close>, \<^term>\<open>Bit_Operations.xor\<close>, \<^term>\<open>mask\<close>,
       \<^term>\<open>push_bit\<close>, \<^term>\<open>drop_bit\<close>, \<^term>\<open>take_bit\<close>,
       \<^term>\<open>Bit_Operations.set_bit\<close>, \<^term>\<open>unset_bit\<close>, \<^term>\<open>flip_bit\<close>,
       \<^term>\<open>msb\<close>, \<^term>\<open>size\<close>, \<^term>\<open>set_bits\<close>]
  in
    K (Context.mapping I (fold Proof_Context.add_const_constraint cs))
  end
\<close>

end

locale word_type_copy_ring = word_type_copy
  opening constraintless +
  constrains word_of :: \<open>'a \<Rightarrow> 'b::len word\<close>
  assumes word_of_0 [code]: \<open>word_of 0 = 0\<close>
    and word_of_1 [code]: \<open>word_of 1 = 1\<close>
    and word_of_add [code]: \<open>word_of (p + q) = word_of p + word_of q\<close>
    and word_of_minus [code]: \<open>word_of (- p) = - (word_of p)\<close>
    and word_of_diff [code]: \<open>word_of (p - q) = word_of p - word_of q\<close>
    and word_of_mult [code]: \<open>word_of (p * q) = word_of p * word_of q\<close>
    and word_of_div [code]: \<open>word_of (p div q) = word_of p div word_of q\<close>
    and word_of_mod [code]: \<open>word_of (p mod q) = word_of p mod word_of q\<close>
    and equal_iff_word_of [code]: \<open>HOL.equal p q \<longleftrightarrow> HOL.equal (word_of p) (word_of q)\<close>
    and less_eq_iff_word_of [code]: \<open>p \<le> q \<longleftrightarrow> word_of p \<le> word_of q\<close>
    and less_iff_word_of [code]: \<open>p < q \<longleftrightarrow> word_of p < word_of q\<close>
begin

lemma of_class_comm_ring_1:
  \<open>OFCLASS('a, comm_ring_1_class)\<close>
  by standard (simp_all add: eq_iff_word_of word_of_0 word_of_1
    word_of_add word_of_minus word_of_diff word_of_mult algebra_simps)

lemma of_class_semiring_modulo:
  \<open>OFCLASS('a, semiring_modulo_class)\<close>
  by standard (simp_all add: eq_iff_word_of word_of_0 word_of_1
    word_of_add word_of_minus word_of_diff word_of_mult word_of_mod word_of_div algebra_simps
    mod_mult_div_eq)

lemma of_class_equal:
  \<open>OFCLASS('a, equal_class)\<close>
  by standard (simp add: eq_iff_word_of equal_iff_word_of equal)

lemma of_class_linorder:
  \<open>OFCLASS('a, linorder_class)\<close>
  by standard (auto simp add: eq_iff_word_of less_eq_iff_word_of less_iff_word_of)

end

locale word_type_copy_bits = word_type_copy_ring
  opening constraintless and bit_operations_syntax +
  constrains word_of :: \<open>'a::{comm_ring_1, semiring_modulo, equal, linorder} \<Rightarrow> 'b::len word\<close>
  fixes signed_drop_bit :: \<open>nat \<Rightarrow> 'a \<Rightarrow> 'a\<close>
  assumes bit_eq_word_of [code]: \<open>bit p = bit (word_of p)\<close>
    and word_of_not [code]: \<open>word_of (NOT p) = NOT (word_of p)\<close>
    and word_of_and [code]: \<open>word_of (p AND q) = word_of p AND word_of q\<close>
    and word_of_or [code]: \<open>word_of (p OR q) = word_of p OR word_of q\<close>
    and word_of_xor [code]: \<open>word_of (p XOR q) = word_of p XOR word_of q\<close>
    and word_of_mask [code]: \<open>word_of (mask n) = mask n\<close>
    and word_of_push_bit [code]: \<open>word_of (push_bit n p) = push_bit n (word_of p)\<close>
    and word_of_drop_bit [code]: \<open>word_of (drop_bit n p) = drop_bit n (word_of p)\<close>
    and word_of_signed_drop_bit [code]: \<open>word_of (signed_drop_bit n p) = Word.signed_drop_bit n (word_of p)\<close>
    and word_of_take_bit [code]: \<open>word_of (take_bit n p) = take_bit n (word_of p)\<close>
    and word_of_set_bit [code]: \<open>word_of (Bit_Operations.set_bit n p) = Bit_Operations.set_bit n (word_of p)\<close>
    and word_of_unset_bit [code]: \<open>word_of (unset_bit n p) = unset_bit n (word_of p)\<close>
    and word_of_flip_bit [code]: \<open>word_of (flip_bit n p) = flip_bit n (word_of p)\<close>
begin

lemma word_of_bool:
  \<open>word_of (of_bool n) = of_bool n\<close>
  by (simp add: word_of_0 word_of_1)

lemma word_of_nat:
  \<open>word_of (of_nat n) = of_nat n\<close>
  by (induction n) (simp_all add: word_of_0 word_of_1 word_of_add)

lemma word_of_numeral [simp]:
  \<open>word_of (numeral n) = numeral n\<close>
proof -
  have \<open>word_of (of_nat (numeral n)) = of_nat (numeral n)\<close>
    by (simp only: word_of_nat)
  then show ?thesis by simp
qed

lemma word_of_power:
  \<open>word_of (p ^ n) = word_of p ^ n\<close>
  by (induction n) (simp_all add: word_of_1 word_of_mult)

lemma even_iff_word_of:
  \<open>2 dvd p \<longleftrightarrow> 2 dvd word_of p\<close> (is \<open>?P \<longleftrightarrow> ?Q\<close>)
proof
  assume ?P
  then obtain q where \<open>p = 2 * q\<close> ..
  then show ?Q by (simp add: word_of_mult)
next
  assume ?Q
  then obtain w where \<open>word_of p = 2 * w\<close> ..
  then have \<open>of_word (word_of p) = of_word (2 * w)\<close>
    by simp
  then have \<open>p = 2 * of_word w\<close>
    by (simp add: eq_iff_word_of word_of_word word_of_mult)
  then show ?P
    by simp
qed

lemma of_class_ring_bit_operations:
  \<open>OFCLASS('a, ring_bit_operations_class)\<close>
proof -
  have induct: \<open>P p\<close> if stable: \<open>(\<And>p. p div 2 = p \<Longrightarrow> P p)\<close>
      and rec: \<open>(\<And>p b. P p \<Longrightarrow> (of_bool b + 2 * p) div 2 = p \<Longrightarrow> P (of_bool b + 2 * p))\<close>
    for p :: 'a and P
  proof -
    from stable have stable': \<open>(\<And>p. word_of p div 2 = word_of p \<Longrightarrow> P p)\<close>
      by (simp add: eq_iff_word_of word_of_div)
    from rec have rec': \<open>(\<And>p b. P p \<Longrightarrow> (of_bool b + 2 * word_of p) div 2 = word_of p \<Longrightarrow> P (of_bool b + 2 * p))\<close>
      by (simp add: eq_iff_word_of word_of_add word_of_bool word_of_mult word_of_div)
    define w where \<open>w = word_of p\<close>
    then have \<open>p = of_word w\<close>
      by (simp add: of_word_of)
    also have \<open>P (of_word w)\<close>
    proof (induction w rule: bit_induct)
      case (stable w)
      show ?case
        by (rule stable') (simp add: word_of_word stable)
    next
      case (rec w b)
      have \<open>P (of_bool b + 2 * of_word w)\<close>
        by (rule rec') (simp_all add: word_of_word rec)
      also have \<open>of_bool b + 2 * of_word w = of_word (of_bool b + 2 * w)\<close>
        by (simp add: eq_iff_word_of word_of_word word_of_add word_of_1 word_of_mult word_of_0)
      finally show ?case .
    qed
    finally show \<open>P p\<close> .
  qed
  have \<open>class.semiring_parity_axioms (+) (0::'a) (*) 1 (div) (mod)\<close>
    by standard
      (simp_all add: eq_iff_word_of word_of_0 word_of_1 even_iff_word_of word_of_add word_of_div word_of_mod even_iff_mod_2_eq_zero)
  with of_class_semiring_modulo have \<open>OFCLASS('a, semiring_parity_class)\<close>
    by (rule semiring_parity_class.intro) 
  moreover have \<open>OFCLASS('a, semiring_modulo_trivial_class)\<close>
    apply standard
      apply (simp_all only: eq_iff_word_of word_of_0 word_of_1 word_of_div)
      apply simp_all
    done
  moreover have \<open>class.semiring_bits_axioms (+) (0::'a) (*) 1 (div) (mod) bit\<close>
    apply standard
             apply (fact induct)
            apply (simp_all only: eq_iff_word_of word_of_0 word_of_1 word_of_bool word_of_numeral
              word_of_add word_of_diff word_of_mult word_of_div word_of_mod word_of_power
              bit_eq_word_of push_bit_take_bit drop_bit_take_bit even_iff_word_of
              fold_possible_bit
              flip: push_bit_eq_mult drop_bit_eq_div take_bit_eq_mod mask_eq_exp_minus_1 drop_bit_Suc)
           apply (simp_all add: bit_simps even_drop_bit_iff_not_bit not_less)
    done
  ultimately have \<open>OFCLASS('a, semiring_bits_class)\<close>
    by (rule semiring_bits_class.intro)
  moreover have \<open>class.semiring_bit_operations_axioms (+) (-) (0::'a) (*) (1::'a) (div) (mod) (AND) (OR) (XOR) mask Bit_Operations.set_bit unset_bit flip_bit push_bit drop_bit take_bit\<close>
    apply standard
    apply (simp_all add: eq_iff_word_of word_of_add word_of_push_bit word_of_power
      bit_eq_word_of word_of_and word_of_or word_of_xor word_of_mask word_of_diff
      word_of_0 word_of_1 bit_simps
      word_of_set_bit set_bit_eq_or word_of_unset_bit unset_bit_eq_or_xor word_of_flip_bit flip_bit_eq_xor
      word_of_mult
      word_of_drop_bit word_of_div word_of_take_bit word_of_mod
      and_rec [of \<open>word_of a\<close> \<open>word_of b\<close> for a b]
      or_rec [of \<open>word_of a\<close> \<open>word_of b\<close> for a b]
      xor_rec [of \<open>word_of a\<close> \<open>word_of b\<close> for a b] even_iff_word_of
      flip: mask_eq_exp_minus_1 push_bit_eq_mult drop_bit_eq_div take_bit_eq_mod)
    done
  ultimately have \<open>OFCLASS('a, semiring_bit_operations_class)\<close>
    by (rule semiring_bit_operations_class.intro)
  moreover have \<open>OFCLASS('a, ring_parity_class)\<close>
    using \<open>OFCLASS('a, semiring_parity_class)\<close> by (rule ring_parity_class.intro) standard
  moreover have \<open>class.ring_bit_operations_axioms (-) (1::'a) uminus NOT\<close>
    by standard
      (simp add: eq_iff_word_of word_of_not word_of_diff word_of_minus word_of_1 not_eq_complement)
  ultimately show \<open>OFCLASS('a, ring_bit_operations_class)\<close>
    by (rule ring_bit_operations_class.intro)
qed

lemma [code]:
  \<open>take_bit n a = a AND mask n\<close> for a :: 'a
  by (simp add: eq_iff_word_of word_of_take_bit word_of_and word_of_mask take_bit_eq_mask)

lemma [code]:
  \<open>mask (Suc n) = push_bit n (1 :: 'a) OR mask n\<close>
  \<open>mask 0 = (0 :: 'a)\<close>
  by (simp_all add: eq_iff_word_of word_of_mask word_of_or word_of_push_bit word_of_0 word_of_1 mask_Suc_exp)

lemma [code]:
  \<open>Bit_Operations.set_bit n w = w OR push_bit n 1\<close> for w :: 'a
  by (simp add: eq_iff_word_of word_of_set_bit word_of_or word_of_push_bit word_of_1 set_bit_eq_or)

lemma [code]:
  \<open>unset_bit n w = w AND NOT (push_bit n 1)\<close> for w :: 'a
  by (simp add: eq_iff_word_of word_of_unset_bit word_of_and word_of_not word_of_push_bit word_of_1 unset_bit_eq_and_not)

lemma [code]:
  \<open>flip_bit n w = w XOR push_bit n 1\<close> for w :: 'a
  by (simp add: eq_iff_word_of word_of_flip_bit word_of_xor word_of_push_bit word_of_1 flip_bit_eq_xor)

end

locale word_type_copy_more = word_type_copy_bits +
  constrains word_of :: \<open>'a::{ring_bit_operations, equal, linorder} \<Rightarrow> 'b::len word\<close>
  fixes of_nat :: \<open>nat \<Rightarrow> 'a\<close> and nat_of :: \<open>'a \<Rightarrow> nat\<close>
    and of_int :: \<open>int \<Rightarrow> 'a\<close> and int_of :: \<open>'a \<Rightarrow> int\<close>
    and of_integer :: \<open>integer \<Rightarrow> 'a\<close> and integer_of :: \<open>'a \<Rightarrow> integer\<close>
  assumes word_of_nat_eq: \<open>word_of (of_nat n) = word_of_nat n\<close>
    and nat_of_eq_word_of: \<open>nat_of p = unat (word_of p)\<close>
    and word_of_int_eq: \<open>word_of (of_int k) = word_of_int k\<close>
    and int_of_eq_word_of: \<open>int_of p = uint (word_of p)\<close>
    and word_of_integer_eq: \<open>word_of (of_integer l) = word_of_int (int_of_integer l)\<close>
    and integer_of_eq_word_of: \<open>integer_of p = unsigned (word_of p)\<close>
begin

lemma of_word_numeral [code_post]:
  \<open>of_word (numeral n) = numeral n\<close>
  by (simp add: eq_iff_word_of word_of_word)

lemma of_word_0 [code_post]:
  \<open>of_word 0 = 0\<close>
  by (simp add: eq_iff_word_of word_of_0 word_of_word)

lemma of_word_1 [code_post]:
  \<open>of_word 1 = 1\<close>
  by (simp add: eq_iff_word_of word_of_1 word_of_word)

text \<open>Use pretty numerals from integer for pretty printing\<close>

lemma numeral_eq_integer [code_unfold]:
  \<open>numeral n = of_integer (numeral n)\<close>
  by (simp add: eq_iff_word_of word_of_integer_eq)

lemma neg_numeral_eq_integer [code_unfold]:
  \<open>- numeral n = of_integer (- numeral n)\<close>
  by (simp add: eq_iff_word_of word_of_integer_eq word_of_minus)

end

locale word_type_copy_misc = word_type_copy_more
  opening constraintless and bit_operations_syntax +
  constrains word_of :: \<open>'a::{ring_bit_operations, equal, linorder} \<Rightarrow> 'b::len word\<close>
  fixes size :: nat and set_bits_aux :: \<open>(nat \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a\<close>
    assumes size_eq_length: \<open>size = LENGTH('b::len)\<close>
    and msb_iff_word_of [code]: \<open>msb p \<longleftrightarrow> msb (word_of p)\<close>
    and size_eq_word_of: \<open>Nat.size (p :: 'a) = Nat.size (word_of p)\<close>
    and word_of_set_bits: \<open>word_of (set_bits P) = set_bits P\<close>
    and word_of_set_bits_aux: \<open>word_of (set_bits_aux P n p) = Bit_Comprehension.set_bits_aux P n (word_of p)\<close>
begin

lemma size_eq [code]:
  \<open>Nat.size p = size\<close> for p :: 'a
  by (simp add: size_eq_length size_eq_word_of word_size)

lemma set_bits_aux_code [code]:
  \<open>set_bits_aux f n w =
  (if n = 0 then w 
   else let n' = n - 1 in set_bits_aux f n' (push_bit 1 w OR (if f n' then 1 else 0)))\<close>
  by (simp add: eq_iff_word_of word_of_set_bits_aux Let_def word_of_mult word_of_or word_of_0 word_of_1 set_bits_aux_rec [of f n])

lemma set_bits_code [code]: \<open>set_bits P = set_bits_aux P size 0\<close>
  by (simp add: fun_eq_iff eq_iff_word_of word_of_set_bits word_of_set_bits_aux word_of_0 size_eq_length set_bits_conv_set_bits_aux)

lemma of_class_bit_comprehension:
  \<open>OFCLASS('a, bit_comprehension_class)\<close>
  by standard (simp add: eq_iff_word_of word_of_set_bits bit_eq_word_of set_bits_bit_eq)

end

section \<open>Establishing operation variants tailored towards target languages\<close>

locale word_type_copy_target_language = word_type_copy_misc +
  constrains word_of :: \<open>'a::{ring_bit_operations, equal, linorder} \<Rightarrow> 'b::len word\<close>
  fixes size_integer :: integer
    and almost_size :: nat
  assumes size_integer_eq_length: \<open>size_integer = Nat.of_nat LENGTH('b::len)\<close>
    and almost_size_eq_decr_length: \<open>almost_size = LENGTH('b::len) - Suc 0\<close>
begin

definition shiftl :: \<open>'a \<Rightarrow> integer \<Rightarrow> 'a\<close>
  where \<open>shiftl w k = (if k < 0 \<or> size_integer \<le> k then undefined (push_bit :: nat \<Rightarrow> 'a \<Rightarrow> 'a) w k
    else push_bit (nat_of_integer k) w)\<close>

lemma word_of_shiftl [code abstract]:
  \<open>word_of (shiftl w k) =
  (if k < 0 \<or> size_integer \<le> k then word_of (undefined (push_bit :: _ \<Rightarrow> _ \<Rightarrow> 'a) w k)
   else push_bit (nat_of_integer k) (word_of w))\<close>
  by (simp add: shiftl_def word_of_push_bit)

lemma push_bit_code [code]:
  \<open>push_bit k w = (if k < size then shiftl w (integer_of_nat k) else 0)\<close>
  by (rule word_of_eqI)
    (simp add: integer_of_nat_eq_of_nat word_of_push_bit word_of_0 shiftl_def, simp add: size_eq_length size_integer_eq_length)

definition shiftr :: \<open>'a \<Rightarrow> integer \<Rightarrow> 'a\<close>
  where \<open>shiftr w k = (if k < 0 \<or> size_integer \<le> k then undefined (drop_bit :: nat \<Rightarrow> 'a \<Rightarrow> 'a) w k
    else drop_bit (nat_of_integer k) w)\<close>

lemma word_of_shiftr [code abstract]:
  \<open>word_of (shiftr w k) =
  (if k < 0 \<or> size_integer \<le> k then word_of (undefined (drop_bit :: _ \<Rightarrow> _ \<Rightarrow> 'a) w k)
   else drop_bit (nat_of_integer k) (word_of w))\<close>
  by (simp add: shiftr_def word_of_drop_bit)

lemma drop_bit_code [code]:
  \<open>drop_bit k w = (if k < size then shiftr w (integer_of_nat k) else 0)\<close>
  by (rule word_of_eqI)
    (simp add: integer_of_nat_eq_of_nat word_of_drop_bit word_of_0 shiftr_def, simp add: size_eq_length size_integer_eq_length)

definition sshiftr :: \<open>'a \<Rightarrow> integer \<Rightarrow> 'a\<close>
  where \<open>sshiftr w k = (if k < 0 \<or> size_integer \<le> k then undefined (signed_drop_bit :: _ \<Rightarrow> _ \<Rightarrow> 'a) w k
    else signed_drop_bit (nat_of_integer k) w)\<close>

lemma word_of_sshiftr [code abstract]:
  \<open>word_of (sshiftr w k) =
  (if k < 0 \<or> size_integer \<le> k then word_of (undefined (signed_drop_bit :: _ \<Rightarrow> _ \<Rightarrow> 'a) w k)
   else Word.signed_drop_bit (nat_of_integer k) (word_of w))\<close>
  by (simp add: sshiftr_def word_of_signed_drop_bit)

lemma signed_drop_bit_code [code]:
  \<open>signed_drop_bit k w = (if k < size then sshiftr w (integer_of_nat k)
    else if (bit w almost_size) then - 1 else 0)\<close>
  by (rule word_of_eqI)
    (simp add: integer_of_nat_eq_of_nat word_of_signed_drop_bit
    word_of_0 word_of_1 word_of_minus sshiftr_def bit_eq_word_of not_less,
    simp add: size_eq_length size_integer_eq_length almost_size_eq_decr_length signed_drop_bit_beyond)

definition test_bit :: \<open>'a \<Rightarrow> integer \<Rightarrow> bool\<close>
  where \<open>test_bit w k = (if k < 0 \<or> size_integer \<le> k then undefined (bit :: 'a \<Rightarrow> _) w k
   else bit w (nat_of_integer k))\<close>

lemma test_bit_eq [code]:
  \<open>test_bit w k = (if k < 0 \<or> size_integer \<le> k then undefined (bit :: 'a \<Rightarrow> _) w k
    else bit (word_of w) (nat_of_integer k))\<close>
  by (simp add: test_bit_def bit_eq_word_of)

lemma bit_code [code]:
  \<open>bit w n \<longleftrightarrow> n < size \<and> test_bit w (integer_of_nat n)\<close>
  by (simp add: test_bit_def integer_of_nat_eq_of_nat)
    (simp add: bit_eq_word_of size_eq_length size_integer_eq_length impossible_bit)

end

subsection \<open>Division by signed division\<close>

text \<open>Division on @{typ "'a word"} is unsigned, but Scala and OCaml only have signed division and modulus.\<close>

context
begin

private lemma div_half_nat:
  fixes m n :: nat
  assumes "n \<noteq> 0"
  shows "(m div n, m mod n) = (
    let
      q = 2 * (drop_bit 1 m div n);
      r = m - q * n
    in if n \<le> r then (q + 1, r - n) else (q, r))"
proof -
  let ?q = "2 * (drop_bit 1 m div n)"
  have q: "?q = m div n - m div n mod 2"
    by (simp add: modulo_nat_def drop_bit_Suc, simp flip: div_mult2_eq add: ac_simps)
  let ?r = "m - ?q * n"
  have r: "?r = m mod n + m div n mod 2 * n"
    by (simp add: q algebra_simps modulo_nat_def drop_bit_Suc, simp flip: div_mult2_eq add: ac_simps)
  show ?thesis
  proof (cases "n \<le> m - ?q * n")
    case True
    with assms q have "m div n mod 2 \<noteq> 0"
      unfolding r by simp (metis add.right_neutral mod_less_divisor mult_eq_0_iff not_less not_mod2_eq_Suc_0_eq_0)
    hence "m div n = ?q + 1" unfolding q
      by simp
    moreover have "m mod n = ?r - n" using \<open>m div n = ?q + 1\<close>
      by (simp add: modulo_nat_def)
    ultimately show ?thesis
      using True by (simp add: Let_def)
  next
    case False
    hence "m div n mod 2 = 0"
      unfolding r by (simp add: not_le) (metis Nat.add_0_right assms div_less div_mult_self2 mod_div_trivial mult.commute)
    hence "m div n = ?q"
      unfolding q by simp
    moreover have "m mod n = ?r" using \<open>m div n = ?q\<close>
      by (simp add: modulo_nat_def)
    ultimately show ?thesis
      using False by (simp add: Let_def)
  qed
qed

private lemma div_half_word:
  fixes x y :: "'a :: len word"
  assumes "y \<noteq> 0"
  shows "(x div y, x mod y) = (
    let
      q = push_bit 1 (drop_bit 1 x div y);
      r = x - q * y
    in if y \<le> r then (q + 1, r - y) else (q, r))"
proof -
  obtain n where n: "x = of_nat n" "n < 2 ^ LENGTH('a)"
    by (rule that [of \<open>unat x\<close>]) simp_all
  moreover obtain m where m: "y = of_nat m" "m < 2 ^ LENGTH('a)"
    by (rule that [of \<open>unat y\<close>]) simp_all
  ultimately have [simp]: \<open>unat (of_nat n :: 'a word) = n\<close> \<open>unat (of_nat m :: 'a word) = m\<close>
    by (transfer, simp add: take_bit_of_nat take_bit_nat_eq_self_iff)+
  let ?q = "push_bit 1 (drop_bit 1 x div y)"
  let ?q' = "2 * (drop_bit 1 n div m)"
  have "drop_bit 1 n div m < 2 ^ LENGTH('a)"
    using n by (simp add: drop_bit_Suc) (meson div_le_dividend le_less_trans)
  hence q: "?q = of_nat ?q'" using n m
    by (auto simp add: drop_bit_eq_div word_arith_nat_div uno_simps take_bit_nat_eq_self unsigned_of_nat)
  from assms have "m \<noteq> 0" using m by - (rule notI, simp)
  from n have "?q' < 2 ^ LENGTH('a)"
    by (simp add: drop_bit_Suc) (metis div_le_dividend le_less_trans less_mult_imp_div_less linorder_not_le mult.commute)
  moreover
  have "2 * (drop_bit 1 n div m) * m < 2 ^ LENGTH('a)"
    using n by (simp add: drop_bit_Suc ac_simps flip: div_mult2_eq)
      (metis le_less_trans mult.assoc times_div_less_eq_dividend)
  moreover have "2 * (drop_bit 1 n div m) * m \<le> n"
    by (simp add: drop_bit_Suc flip: div_mult2_eq ac_simps)
  ultimately
  have r: "x - ?q * y = of_nat (n - ?q' * m)"
    and "y \<le> x - ?q * y \<Longrightarrow> of_nat (n - ?q' * m) - y = of_nat (n - ?q' * m - m)"
    using n m unfolding q
     apply simp_all
    apply (cases \<open>LENGTH('a) \<ge> 2\<close>)
     apply (simp_all add: word_le_nat_alt take_bit_nat_eq_self unat_sub_if' unat_word_ariths unsigned_of_nat)
    done
  then show ?thesis using n m div_half_nat [OF \<open>m \<noteq> 0\<close>, of n] unfolding q
    by (simp add: word_le_nat_alt word_div_def word_mod_def Let_def take_bit_nat_eq_self unsigned_of_nat
      flip: zdiv_int zmod_int
      split del: if_split split: if_split_asm)
qed


text \<open>
  This algorithm implements unsigned division in terms of signed division.
  Taken from Hacker's Delight.
\<close>

lemma divmod_via_sdivmod:
  fixes x y :: "'a :: len word"
  assumes "y \<noteq> 0"
  shows "(x div y, x mod y) = (
    if push_bit (LENGTH('a) - 1) 1 \<le> y then
      if x < y then (0, x) else (1, x - y)
    else let
      q = (push_bit 1 (drop_bit 1 x sdiv y));
      r = x - q * y
    in if y \<le> r then (q + 1, r - y) else (q, r))"
proof (cases "push_bit (LENGTH('a) - 1) 1 \<le> y")
  case True
  note y = this
  show ?thesis
  proof (cases "x < y")
    case True
    with y show ?thesis
      by (simp add: word_div_less mod_word_less)
  next
    case False
    obtain n where n: "y = of_nat n" "n < 2 ^ LENGTH('a)"
      by (rule that [of \<open>unat y\<close>]) simp_all
    have "unat x < 2 ^ LENGTH('a)" by (rule unsigned_less)
    also have "\<dots> = 2 * 2 ^ (LENGTH('a) - 1)"
      by(metis Suc_pred len_gt_0 power_Suc One_nat_def)
    also have "\<dots> \<le> 2 * n" using y n
      by transfer (simp add: take_bit_eq_mod)
    finally have div: "x div of_nat n = 1" using False n
      by (simp add: take_bit_nat_eq_self unsigned_of_nat word_div_eq_1_iff)
    moreover have "x mod y = x - x div y * y"
      by (simp add: minus_div_mult_eq_mod)
    with div n have "x mod y = x - y" by simp
    ultimately show ?thesis using False y n by simp
  qed
next
  case False
  note y = this
  obtain n where n: "x = of_nat n" "n < 2 ^ LENGTH('a)"
    by (rule that [of \<open>unat x\<close>]) simp_all
  hence "int n div 2 + 2 ^ (LENGTH('a) - Suc 0) < 2 ^ LENGTH('a)"
    by (cases \<open>LENGTH('a)\<close>)
      (auto dest: less_imp_of_nat_less [where ?'a = int])
  with y n have "sint (drop_bit 1 x) = uint (drop_bit 1 x)"
    by (cases \<open>LENGTH('a)\<close>)
      (auto simp add: sint_uint drop_bit_eq_div take_bit_nat_eq_self uint_div_distrib
        signed_take_bit_int_eq_self_iff unsigned_of_nat)
  moreover have "uint y + 2 ^ (LENGTH('a) - Suc 0) < 2 ^ LENGTH('a)"
    using y by (cases \<open>LENGTH('a)\<close>)
      (simp_all add: not_le word_less_alt uint_power_lower)
  then have "sint y = uint y"
    apply (cases \<open>LENGTH('a)\<close>)
     apply (auto simp add: sint_uint signed_take_bit_int_eq_self_iff)
    using uint_ge_0 [of y]
    by linarith 
  ultimately show ?thesis using y
    apply (subst div_half_word [OF assms])
    apply (simp add: sdiv_word_def signed_divide_int_def flip: uint_div)
    done
qed

end


subsection \<open>Conversion from \<^typ>\<open>int\<close> to \<^typ>\<open>'a word\<close>\<close>

lemma word_of_int_via_signed:
  includes bit_operations_syntax
  assumes shift_def: "shift = push_bit LENGTH('a) 1"
  and overflow_def:"overflow = push_bit (LENGTH('a) - 1) 1"
  shows
  "(word_of_int i :: 'a :: len word) =
   (let i' = i AND mask LENGTH('a)
    in if bit i' (LENGTH('a) - 1) then
         if i' - shift < - overflow \<or> overflow \<le> i' - shift then arbitrary1 i' else word_of_int (i' - shift)
       else if i' < - overflow \<or> overflow \<le> i' then arbitrary2 i' else word_of_int i')"
proof -
  define i' where "i' = i AND mask LENGTH('a)"
  have "shift = mask LENGTH('a) + 1" unfolding assms
    by (simp add: mask_eq_exp_minus_1) 
  hence "i' < shift"
    by (simp add: i'_def)
  show ?thesis
  proof(cases "bit i' (LENGTH('a) - 1)")
    case True
    then have unf: "i' = overflow OR i'"
      apply (simp add: assms i'_def flip: take_bit_eq_mask)
      apply (rule bit_eqI)
      apply (auto simp add: bit_take_bit_iff bit_or_iff bit_exp_iff)
      done
    have \<open>overflow \<le> overflow OR i'\<close>
      by (simp add: i'_def or_greater_eq)
    then have "overflow \<le> i'"
      by (subst unf)
    hence "i' - shift < - overflow \<longleftrightarrow> False" unfolding assms
      by(cases "LENGTH('a)")(simp_all add: not_less)
    moreover
    have "overflow \<le> i' - shift \<longleftrightarrow> False" using \<open>i' < shift\<close> unfolding assms
      by(cases "LENGTH('a)")(auto simp add: not_le elim: less_le_trans)
    moreover
    have "word_of_int (i' - shift) = (word_of_int i :: 'a word)" using \<open>i' < shift\<close>
      by (simp add: i'_def shift_def word_of_int_eq_iff flip: take_bit_eq_mask)
    ultimately show ?thesis using True by(simp add: Let_def i'_def)
  next
    case False
    have "i' = i AND mask (LENGTH('a) - 1)"
      apply (rule bit_eqI)
      apply (use False in \<open>auto simp add: bit_simps assms i'_def\<close>)
      apply (auto simp add: less_le)
      done
    also have "\<dots> \<le> Bit_Operations.mask (LENGTH('a) - 1)"
      using AND_upper2 mask_nonnegative_int by blast
    also have "\<dots> < overflow"
      by (simp add: mask_int_def overflow_def)
    also
    have "- overflow \<le> 0" unfolding overflow_def by simp
    have "0 \<le> i'" by (simp add: i'_def)
    hence "- overflow \<le> i'" using \<open>- overflow \<le> 0\<close> by simp
    moreover
    have "word_of_int i' = (word_of_int i :: 'a word)"
      by (simp add: i'_def of_int_and_eq of_int_mask_eq)
    ultimately show ?thesis using False by(simp add: Let_def i'_def)
  qed
qed


subsection \<open>Quickcheck conversion functions\<close>

context
  includes state_combinator_syntax
begin

definition qc_random_cnv ::
  "(natural \<Rightarrow> 'a::term_of) \<Rightarrow> natural \<Rightarrow> Random.seed
    \<Rightarrow> ('a \<times> (unit \<Rightarrow> Code_Evaluation.term)) \<times> Random.seed"
  where "qc_random_cnv a_of_natural i = Random.range (i + 1) \<circ>\<rightarrow> (\<lambda>k. Pair (
       let n = a_of_natural k
       in (n, \<lambda>_. Code_Evaluation.term_of n)))"

end

definition qc_exhaustive_cnv :: "(natural \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> (bool \<times> term list) option)
  \<Rightarrow> natural \<Rightarrow> (bool \<times> term list) option"
where
  "qc_exhaustive_cnv a_of_natural f d =
   Quickcheck_Exhaustive.exhaustive (%x. f (a_of_natural x)) d"

definition qc_full_exhaustive_cnv ::
  "(natural \<Rightarrow> ('a::term_of)) \<Rightarrow> ('a \<times> (unit \<Rightarrow> term) \<Rightarrow> (bool \<times> term list) option)
  \<Rightarrow> natural \<Rightarrow> (bool \<times> term list) option"
where
  "qc_full_exhaustive_cnv a_of_natural f d = Quickcheck_Exhaustive.full_exhaustive
  (%(x, xt). f (a_of_natural x, %_. Code_Evaluation.term_of (a_of_natural x))) d"

declare [[quickcheck_narrowing_ghc_options = "-XTypeSynonymInstances"]]

definition qc_narrowing_drawn_from :: "'a list \<Rightarrow> integer \<Rightarrow> _"
where
  "qc_narrowing_drawn_from xs =
   foldr Quickcheck_Narrowing.sum (map Quickcheck_Narrowing.cons (butlast xs)) (Quickcheck_Narrowing.cons (last xs))"

locale quickcheck_narrowing_samples =
  fixes a_of_integer :: "integer \<Rightarrow> 'a \<times> 'a :: {partial_term_of, term_of}"
  and zero :: "'a"
  and tr :: "typerep"
begin

function narrowing_samples :: "integer \<Rightarrow> 'a list"
where
  "narrowing_samples i =
   (if i > 0 then let (a, a') = a_of_integer i in narrowing_samples (i - 1) @ [a, a'] else [zero])"
by pat_completeness auto
termination including integer.lifting
proof(relation "measure nat_of_integer")
  fix i :: integer
  assume "0 < i"
  thus "(i - 1, i) \<in> measure nat_of_integer"
    by simp(transfer, simp)
qed simp

definition partial_term_of_sample :: "integer \<Rightarrow> 'a"
where
  "partial_term_of_sample i =
  (if i < 0 then undefined
   else if i = 0 then zero
   else if i mod 2 = 0 then snd (a_of_integer (i div 2))
   else fst (a_of_integer (i div 2 + 1)))"

lemma partial_term_of_code:
  "partial_term_of (ty :: 'a itself) (Quickcheck_Narrowing.Narrowing_variable p t) \<equiv>
    Code_Evaluation.Free (STR ''_'') tr"
  "partial_term_of (ty :: 'a itself) (Quickcheck_Narrowing.Narrowing_constructor i []) \<equiv>
   Code_Evaluation.term_of (partial_term_of_sample i)"
by (rule partial_term_of_anything)+

end

lemmas [code] =
  quickcheck_narrowing_samples.narrowing_samples.simps
  quickcheck_narrowing_samples.partial_term_of_sample_def


subsection \<open>Code generator setup\<close>

code_identifier code_module Uint_Common \<rightharpoonup>
  (SML) Word and (Haskell) Word and (OCaml) Word and (Scala) Word

end
