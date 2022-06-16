(*  Title:      Word_Type_Copies.thy
    Author:     Florian Haftmann, TU Muenchen
*)

chapter \<open>Systematic approach towards type copies of word type\<close>

theory Word_Type_Copies
  imports
    "HOL-Library.Word"
    "Word_Lib.Most_significant_bit"
    "Word_Lib.Least_significant_bit"
    "Word_Lib.Generic_set_bit"
    "Word_Lib.Bit_Comprehension"
    "Code_Target_Word_Base"
begin

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
       \<^term>\<open>msb\<close>, \<^term>\<open>lsb\<close>, \<^term>\<open>size\<close>, \<^term>\<open>Generic_set_bit.set_bit\<close>, \<^term>\<open>set_bits\<close>]
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
  opening constraintless bit_operations_syntax +
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
    proof (induction w rule: bits_induct)
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
  have \<open>class.semiring_parity_axioms (+) (0::'a) (*) 1 (mod)\<close>
    by standard (simp_all add: eq_iff_word_of word_of_0 word_of_1 even_iff_word_of word_of_mod even_iff_mod_2_eq_zero)
  with of_class_semiring_modulo have \<open>OFCLASS('a, semiring_parity_class)\<close>
    by (rule semiring_parity_class.intro) 
  moreover have \<open>class.semiring_bits_axioms (+) (-) (0::'a) (*) 1 (div) (mod) bit\<close>
    apply (standard, fact induct)
    apply (simp_all only: eq_iff_word_of word_of_0 word_of_1 word_of_bool word_of_numeral
      word_of_add word_of_diff word_of_mult word_of_div word_of_mod word_of_power even_iff_word_of
      bit_eq_word_of push_bit_take_bit drop_bit_take_bit
      even_drop_bit_iff_not_bit
      flip: push_bit_eq_mult drop_bit_eq_div take_bit_eq_mod mask_eq_exp_minus_1)
               apply (auto simp add: ac_simps bit_simps drop_bit_exp_eq)
    done
  ultimately have \<open>OFCLASS('a, semiring_bits_class)\<close>
    by (rule semiring_bits_class.intro)
  moreover have \<open>class.semiring_bit_operations_axioms (+) (-) (*) (1::'a) (div) (mod) bit (AND) (OR) (XOR) mask Bit_Operations.set_bit unset_bit flip_bit push_bit drop_bit take_bit\<close>
    by standard
      (simp_all add: eq_iff_word_of word_of_push_bit word_of_power
      bit_eq_word_of word_of_and word_of_or word_of_xor word_of_mask word_of_diff word_of_1 bit_simps
      word_of_set_bit set_bit_eq_or word_of_unset_bit word_of_flip_bit flip_bit_eq_xor
      word_of_mult
      word_of_drop_bit word_of_div word_of_take_bit word_of_mod
      flip: mask_eq_exp_minus_1 push_bit_eq_mult drop_bit_eq_div take_bit_eq_mod)
  ultimately have \<open>OFCLASS('a, semiring_bit_operations_class)\<close>
    by (rule semiring_bit_operations_class.intro)
  moreover have \<open>OFCLASS('a, ring_parity_class)\<close>
    using \<open>OFCLASS('a, semiring_parity_class)\<close> by (rule ring_parity_class.intro) standard
  moreover have \<open>class.ring_bit_operations_axioms (+) (-) (0::'a) (*) 1 bit uminus NOT\<close>
    by standard (simp_all add: eq_iff_word_of word_of_power
      bit_eq_word_of word_of_diff word_of_1 bit_simps linorder_not_le
      word_of_not word_of_0
      word_of_minus minus_eq_not_minus_1)
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
    and word_of_integer_eq: \<open>word_of (of_integer l) = word_of_integer l\<close>
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
  opening constraintless bit_operations_syntax +
  constrains word_of :: \<open>'a::{ring_bit_operations, equal, linorder} \<Rightarrow> 'b::len word\<close>
  fixes size :: nat and set_bits_aux :: \<open>(nat \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a\<close>
    assumes size_eq_length: \<open>size = LENGTH('b::len)\<close>
    and msb_iff_word_of [code]: \<open>msb p \<longleftrightarrow> msb (word_of p)\<close>
    and lsb_iff_word_of [code]: \<open>lsb p \<longleftrightarrow> lsb (word_of p)\<close>
    and size_eq_word_of: \<open>Nat.size (p :: 'a) = Nat.size (word_of p)\<close>
    and word_of_generic_set_bit [code]: \<open>word_of (Generic_set_bit.set_bit p n b) = Generic_set_bit.set_bit (word_of p) n b\<close>
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

lemma of_class_lsb:
  \<open>OFCLASS('a, lsb_class)\<close>
  by standard (simp add: fun_eq_iff lsb_iff_word_of even_iff_word_of lsb_odd)

lemma of_class_set_bit:
  \<open>OFCLASS('a, set_bit_class)\<close>
  by standard (simp add: eq_iff_word_of word_of_generic_set_bit bit_eq_word_of word_of_power word_of_0 bit_simps linorder_not_le)

lemma of_class_bit_comprehension:
  \<open>OFCLASS('a, bit_comprehension_class)\<close>
  by standard (simp add: eq_iff_word_of word_of_set_bits bit_eq_word_of set_bits_bit_eq)

end

end
