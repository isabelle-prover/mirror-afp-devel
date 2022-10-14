(*  Title:      Code_Target_Word_Base.thy
    Author:     Andreas Lochbihler, ETH Zurich
*)

chapter \<open>Common base for target language implementations of word types\<close>

theory Code_Target_Word_Base
  imports
    "HOL-Library.Word"
    "Word_Lib.Signed_Division_Word"
    "Word_Lib.More_Word"
begin

subsection \<open>More on conversions\<close>

lemma int_of_integer_unsigned_eq [simp]:
  \<open>int_of_integer (unsigned w) = uint w\<close>
  by transfer simp

lemma int_of_integer_signed_eq [simp]:
  \<open>int_of_integer (signed w) = sint w\<close>
  by transfer simp

abbreviation word_of_integer :: \<open>integer \<Rightarrow> 'a::len word\<close>
  where \<open>word_of_integer k \<equiv> word_of_int (int_of_integer k)\<close>


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


subsection \<open>More on division\<close>

lemma div_half_nat:
  fixes x y :: nat
  assumes "y \<noteq> 0"
  shows "(x div y, x mod y) = (let q = 2 * (x div 2 div y); r = x - q * y in if y \<le> r then (q + 1, r - y) else (q, r))"
proof -
  let ?q = "2 * (x div 2 div y)"
  have q: "?q = x div y - x div y mod 2"
    by(metis div_mult2_eq mult.commute minus_mod_eq_mult_div [symmetric])
  let ?r = "x - ?q * y"
  have r: "?r = x mod y + x div y mod 2 * y"
    by(simp add: q diff_mult_distrib minus_mod_eq_div_mult [symmetric])(metis diff_diff_cancel mod_less_eq_dividend mod_mult2_eq add.commute mult.commute)

  show ?thesis
  proof(cases "y \<le> x - ?q * y")
    case True
    with assms q have "x div y mod 2 \<noteq> 0" unfolding r
      by (metis Nat.add_0_right diff_0_eq_0 diff_Suc_1 le_div_geq mod2_gr_0 mod_div_trivial mult_0 neq0_conv numeral_1_eq_Suc_0 numerals(1)) 
    hence "x div y = ?q + 1" unfolding q
      by simp
    moreover hence "x mod y = ?r - y"
      by simp(metis minus_div_mult_eq_mod [symmetric] diff_commute diff_diff_left mult_Suc)
    ultimately show ?thesis using True by(simp add: Let_def)
  next
    case False
    hence "x div y mod 2 = 0" unfolding r
      by(simp add: not_le)(metis Nat.add_0_right assms div_less div_mult_self2 mod_div_trivial mult.commute)
    hence "x div y = ?q" unfolding q by simp
    moreover hence "x mod y = ?r" by (metis minus_div_mult_eq_mod [symmetric])
    ultimately show ?thesis using False by(simp add: Let_def)
  qed
qed

lemma div_half_word:
  fixes x y :: "'a :: len word"
  assumes "y \<noteq> 0"
  shows "(x div y, x mod y) = (let q = push_bit 1 (drop_bit 1 x div y); r = x - q * y in if y \<le> r then (q + 1, r - y) else (q, r))"
proof -
  obtain n where n: "x = of_nat n" "n < 2 ^ LENGTH('a)"
    by (rule that [of \<open>unat x\<close>]) simp_all
  moreover obtain m where m: "y = of_nat m" "m < 2 ^ LENGTH('a)"
    by (rule that [of \<open>unat y\<close>]) simp_all
  ultimately have [simp]: \<open>unat (of_nat n :: 'a word) = n\<close> \<open>unat (of_nat m :: 'a word) = m\<close>
    by (transfer, simp add: take_bit_of_nat take_bit_nat_eq_self_iff)+
  let ?q = "push_bit 1 (drop_bit 1 x div y)"
  let ?q' = "2 * (n div 2 div m)"
  have "n div 2 div m < 2 ^ LENGTH('a)"
    using n by (metis of_nat_inverse uno_simps(2) unsigned_less)
  hence q: "?q = of_nat ?q'" using n m
    by (auto simp add: drop_bit_eq_div word_arith_nat_div uno_simps take_bit_nat_eq_self unsigned_of_nat)
  from assms have "m \<noteq> 0" using m by -(rule notI, simp)

  from n have "2 * (n div 2 div m) < 2 ^ LENGTH('a)"
    by (metis mult.commute div_mult2_eq minus_mod_eq_mult_div [symmetric] less_imp_diff_less of_nat_inverse unsigned_less uno_simps(2))
  moreover
  have "2 * (n div 2 div m) * m < 2 ^ LENGTH('a)" using n unfolding div_mult2_eq[symmetric]
    by(subst (2) mult.commute)(simp add: minus_mod_eq_div_mult [symmetric] diff_mult_distrib minus_mod_eq_mult_div [symmetric] div_mult2_eq)
  moreover have "2 * (n div 2 div m) * m \<le> n"
    by (simp flip: div_mult2_eq ac_simps)
  ultimately
  have r: "x - ?q * y = of_nat (n - ?q' * m)"
    and "y \<le> x - ?q * y \<Longrightarrow> of_nat (n - ?q' * m) - y = of_nat (n - ?q' * m - m)"
    using n m unfolding q
     apply (simp_all add: of_nat_diff)
    apply (subst of_nat_diff)
    apply (cases \<open>LENGTH('a) \<ge> 2\<close>)
     apply (simp_all add: word_le_nat_alt take_bit_nat_eq_self unat_sub_if' unat_word_ariths unsigned_of_nat)
    done
  then show ?thesis using n m div_half_nat [OF \<open>m \<noteq> 0\<close>, of n] unfolding q
    by (simp add: word_le_nat_alt word_div_def word_mod_def Let_def take_bit_nat_eq_self unsigned_of_nat
      flip: zdiv_int zmod_int
      split del: if_split split: if_split_asm)
qed

text \<open>Division on @{typ "'a word"} is unsigned, but Scala and OCaml only have signed division and modulus.\<close>

lemma [code]:
  "x sdiv y =
   (let x' = sint x; y' = sint y;
        negative = (x' < 0) \<noteq> (y' < 0);
        result = abs x' div abs y'
    in word_of_int (if negative then -result else result))"
  for x y :: \<open>'a::len word\<close>
  by (simp add: sdiv_word_def signed_divide_int_def sgn_if Let_def not_less not_le)

lemma [code]:
  "x smod y =
   (let x' = sint x; y' = sint y;
        negative = (x' < 0);
        result = abs x' mod abs y'
    in word_of_int (if negative then -result else result))"
  for x y :: \<open>'a::len word\<close>
proof -
  have *: \<open>k mod l = k - k div l * l\<close> for k l :: int
    by (simp add: minus_div_mult_eq_mod)
  show ?thesis
    by (simp add: smod_word_def signed_modulo_int_def signed_divide_int_def * sgn_if Let_def)
qed

text \<open>
  This algorithm implements unsigned division in terms of signed division.
  Taken from Hacker's Delight.
\<close>

lemma divmod_via_sdivmod:
  fixes x y :: "'a :: len word"
  assumes "y \<noteq> 0"
  shows
  "(x div y, x mod y) =
  (if push_bit (LENGTH('a) - 1) 1 \<le> y then if x < y then (0, x) else (1, x - y)
   else let q = (push_bit 1 (drop_bit 1 x sdiv y));
            r = x - q * y
        in if r \<ge> y then (q + 1, r - y) else (q, r))"
proof(cases "push_bit (LENGTH('a) - 1) 1 \<le> y")
  case True
  note y = this
  show ?thesis
  proof(cases "x < y")
    case True
    then have "x mod y = x"
      by transfer simp
    then show ?thesis using True y
      using bits_mod_div_trivial [of x y] by simp
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


subsection \<open>More on misc operations\<close>

context
  includes bit_operations_syntax
begin

lemma word_of_int_code:
  "uint (word_of_int x :: 'a word) = x AND mask (LENGTH('a :: len))"
  by (simp add: unsigned_of_int take_bit_eq_mask)

lemma word_and_mask_or_conv_and_mask:
  "bit n index \<Longrightarrow> (n AND mask index) OR (push_bit index 1) = n AND mask (index + 1)"
  for n :: \<open>'a::len word\<close>
  by (rule bit_eqI) (auto simp add: bit_simps)

lemma uint_and_mask_or_full:
  fixes n :: "'a :: len word"
  assumes "bit n (LENGTH('a) - 1)"
  and "mask1 = mask (LENGTH('a) - 1)"
  and "mask2 = push_bit (LENGTH('a) - 1) 1"
  shows "uint (n AND mask1) OR mask2 = uint n"
proof -
  have "mask2 = uint (push_bit (LENGTH('a) - 1) 1 :: 'a word)" using assms
    by transfer (simp add: take_bit_push_bit)
  hence "uint (n AND mask1) OR mask2 = uint (n AND mask1 OR (push_bit (LENGTH('a) - 1) 1 :: 'a word))"
    by(simp add: uint_or)
  also have "\<dots> = uint (n AND mask (LENGTH('a) - 1 + 1))"
    using assms by(simp only: word_and_mask_or_conv_and_mask)
  also have "\<dots> = uint n" by simp
  finally show ?thesis .
qed

lemma word_of_int_via_signed:
  fixes mask
  assumes mask_def: "mask = Bit_Operations.mask LENGTH('a)"
  and shift_def: "shift = push_bit LENGTH('a) 1"
  and index_def: "index = LENGTH('a) - 1"
  and overflow_def:"overflow = push_bit (LENGTH('a) - 1) 1"
  and least_def: "least = - overflow"
  shows
  "(word_of_int i :: 'a :: len word) =
   (let i' = i AND mask
    in if bit i' index then
         if i' - shift < least \<or> overflow \<le> i' - shift then arbitrary1 i' else word_of_int (i' - shift)
       else if i' < least \<or> overflow \<le> i' then arbitrary2 i' else word_of_int i')"
proof -
  define i' where "i' = i AND mask"
  have "shift = mask + 1" unfolding assms
    by (simp add: mask_eq_exp_minus_1) 
  hence "i' < shift"
    by (simp add: mask_def i'_def)
  show ?thesis
  proof(cases "bit i' index")
    case True
    then have unf: "i' = overflow OR i'"
      apply (simp add: assms i'_def flip: take_bit_eq_mask)
      apply (rule bit_eqI)
      apply (auto simp add: bit_take_bit_iff bit_or_iff bit_exp_iff)
      done
    have \<open>overflow \<le> overflow OR i'\<close>
      by (simp add: i'_def mask_def or_greater_eq)
    then have "overflow \<le> i'"
      by (subst unf)
    hence "i' - shift < least \<longleftrightarrow> False" unfolding assms
      by(cases "LENGTH('a)")(simp_all add: not_less)
    moreover
    have "overflow \<le> i' - shift \<longleftrightarrow> False" using \<open>i' < shift\<close> unfolding assms
      by(cases "LENGTH('a)")(auto simp add: not_le elim: less_le_trans)
    moreover
    have "word_of_int (i' - shift) = (word_of_int i :: 'a word)" using \<open>i' < shift\<close>
      by (simp add: i'_def shift_def mask_def word_of_int_eq_iff flip: take_bit_eq_mask)
    ultimately show ?thesis using True by(simp add: Let_def i'_def)
  next
    case False
    have "i' = i AND Bit_Operations.mask (LENGTH('a) - 1)"
      apply (rule bit_eqI)
      apply (use False in \<open>auto simp add: bit_simps assms i'_def\<close>)
      apply (auto simp add: less_le)
      done
    also have "\<dots> \<le> Bit_Operations.mask (LENGTH('a) - 1)"
      using AND_upper2 mask_nonnegative_int by blast
    also have "\<dots> < overflow"
      by (simp add: mask_int_def overflow_def)
    also
    have "least \<le> 0" unfolding least_def overflow_def by simp
    have "0 \<le> i'" by (simp add: i'_def mask_def)
    hence "least \<le> i'" using \<open>least \<le> 0\<close> by simp
    moreover
    have "word_of_int i' = (word_of_int i :: 'a word)"
      by (simp add: i'_def mask_def of_int_and_eq of_int_mask_eq)
    ultimately show ?thesis using False by(simp add: Let_def i'_def)
  qed
qed

end


subsection \<open>Code generator setup\<close>

text \<open>
  The separate code target \<open>SML_word\<close> collects setups for the
  code generator that PolyML does not provide.
\<close>

setup \<open>Code_Target.add_derived_target ("SML_word", [(Code_ML.target_SML, I)])\<close>

code_identifier code_module Code_Target_Word_Base \<rightharpoonup>
  (SML) Word and (Haskell) Word and (OCaml) Word and (Scala) Word


text \<open>Misc\<close>

lemmas word_sdiv_def = sdiv_word_def
lemmas word_smod_def = smod_word_def

end
