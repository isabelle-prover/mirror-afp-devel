(*
 * Copyright Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(* Author: Jeremy Dawson, NICTA *)

section \<open>Operation variants with traditional syntax\<close>

theory Traditional_Infix_Syntax
  imports "HOL-Library.Word" More_Word Signed_Words Syntax_Bundles
begin

class semiring_bit_syntax = semiring_bit_shifts
begin

definition shiftl :: \<open>'a \<Rightarrow> nat \<Rightarrow> 'a\<close>  (infixl "<<" 55)
  where shiftl_eq_push_bit: \<open>a << n = push_bit n a\<close>

definition shiftr :: \<open>'a \<Rightarrow> nat \<Rightarrow> 'a\<close>  (infixl ">>" 55)
  where shiftr_eq_drop_bit: \<open>a >> n = drop_bit n a\<close>

end

instance word :: (len) semiring_bit_syntax ..

context
  includes lifting_syntax
begin

lemma shiftl_word_transfer [transfer_rule]:
  \<open>(pcr_word ===> (=) ===> pcr_word) (\<lambda>k n. push_bit n k) shiftl\<close>
  by (unfold shiftl_eq_push_bit) transfer_prover

lemma shiftr_word_transfer [transfer_rule]:
  \<open>(pcr_word ===> (=) ===> pcr_word) (\<lambda>k n. (drop_bit n \<circ> take_bit LENGTH('a)) k) (shiftr :: 'a::len word \<Rightarrow> _)\<close>
  by (unfold shiftr_eq_drop_bit) transfer_prover

end

lemma shiftl_word_eq:
  \<open>w << n = push_bit n w\<close> for w :: \<open>'a::len word\<close>
  by (fact shiftl_eq_push_bit)

lemma shiftr_word_eq:
  \<open>w >> n = drop_bit n w\<close> for w :: \<open>'a::len word\<close>
  by (fact shiftr_eq_drop_bit)

lemma uint_shiftr_eq:
  \<open>uint (w >> n) = uint w div 2 ^ n\<close>
  by transfer (simp flip: drop_bit_eq_div add: drop_bit_take_bit min_def le_less less_diff_conv)

lemma bit_shiftl_word_iff [bit_simps]:
  \<open>bit (w << m) n \<longleftrightarrow> m \<le> n \<and> n < LENGTH('a) \<and> bit w (n - m)\<close>
  for w :: \<open>'a::len word\<close>
  by (simp add: shiftl_word_eq bit_push_bit_iff not_le)

lemma shiftl_def:
  \<open>w << n = ((*) 2 ^^ n) w\<close> for w :: \<open>'a::len word\<close>
proof -
  have \<open>push_bit n = (((*) 2 ^^ n) :: int \<Rightarrow> int)\<close> for n
    by (induction n) (simp_all add: fun_eq_iff funpow_swap1, simp add: ac_simps)
  then show ?thesis
    by transfer simp
qed

lemma shiftr_def:
  \<open>w >> n = ((\<lambda>w. w div 2) ^^ n) w\<close> for w :: \<open>'a::len word\<close>
proof -
  have \<open>(\<lambda>w. w div 2) ^^ n = (drop_bit n :: 'a word \<Rightarrow> 'a word)\<close>
    by (induction n) (simp_all add: drop_bit_half drop_bit_Suc)
  then show ?thesis
    by (simp add: shiftr_eq_drop_bit)
qed

lemma bit_shiftr_word_iff [bit_simps]:
  \<open>bit (w >> m) n \<longleftrightarrow> bit w (m + n)\<close>
  for w :: \<open>'a::len word\<close>
  by (simp add: shiftr_word_eq bit_drop_bit_eq)

lift_definition sshiftr :: \<open>'a::len word \<Rightarrow> nat \<Rightarrow> 'a word\<close>  (infixl \<open>>>>\<close> 55)
  is \<open>\<lambda>k n. take_bit LENGTH('a) (drop_bit n (signed_take_bit (LENGTH('a) - Suc 0) k))\<close>
  by (simp flip: signed_take_bit_decr_length_iff)

lemma sshiftr_eq [code]:
  \<open>w >>> n = signed_drop_bit n w\<close>
  by transfer simp

lemma sshiftr_eq_funpow_sshiftr1:
  \<open>w >>> n = (signed_drop_bit (Suc 0) ^^ n) w\<close>
  apply (rule sym)
  apply (simp add: sshiftr_eq)
  apply (induction n)
   apply simp_all
  done

lemma uint_sshiftr_eq:
  \<open>uint (w >>> n) = take_bit LENGTH('a) (sint w div 2 ^  n)\<close>
  for w :: \<open>'a::len word\<close>
  by transfer (simp flip: drop_bit_eq_div)

lemma sshiftr_0 [simp]: "0 >>> n = 0"
  by transfer simp

lemma sshiftr_n1 [simp]: "-1 >>> n = -1"
  by transfer simp

lemma bit_sshiftr_word_iff [bit_simps]:
  \<open>bit (w >>> m) n \<longleftrightarrow> bit w (if LENGTH('a) - m \<le> n \<and> n < LENGTH('a) then LENGTH('a) - 1 else (m + n))\<close>
  for w :: \<open>'a::len word\<close>
  apply transfer
  apply (auto simp add: bit_take_bit_iff bit_drop_bit_eq bit_signed_take_bit_iff min_def not_le simp flip: bit_Suc)
  using le_less_Suc_eq apply fastforce
  using le_less_Suc_eq apply fastforce
  done

lemma nth_sshiftr :
  "bit (w >>> m) n =
    (n < size w \<and> (if n + m \<ge> size w then bit w (size w - 1) else bit w (n + m)))"
  apply transfer
  apply (auto simp add: bit_take_bit_iff bit_drop_bit_eq bit_signed_take_bit_iff min_def not_le ac_simps)
  using le_less_Suc_eq apply fastforce
  using le_less_Suc_eq apply fastforce
  done

lemma sshiftr_numeral [simp]:
  \<open>(numeral k >>> numeral n :: 'a::len word) =
    word_of_int (drop_bit (numeral n) (signed_take_bit (LENGTH('a) - 1) (numeral k)))\<close>
  apply (rule bit_word_eqI)
   apply (simp add: word_size nth_sshiftr ac_simps bit_simps)
  done

setup \<open>
  Context.theory_map (fold SMT_Word.add_word_shift' [
    (\<^term>\<open>shiftl :: 'a::len word \<Rightarrow> _\<close>, "bvshl"),
    (\<^term>\<open>shiftr :: 'a::len word \<Rightarrow> _\<close>, "bvlshr"),
    (\<^term>\<open>sshiftr :: 'a::len word \<Rightarrow> _\<close>, "bvashr")
  ])
\<close>

lemma revcast_down_us [OF refl]:
  "rc = revcast \<Longrightarrow> source_size rc = target_size rc + n \<Longrightarrow> rc w = ucast (w >>> n)"
  for w :: "'a::len word"
  apply (simp add: source_size_def target_size_def)
  apply (rule bit_word_eqI)
  apply (simp add: bit_revcast_iff bit_ucast_iff bit_sshiftr_word_iff ac_simps)
  done

lemma revcast_down_ss [OF refl]:
  "rc = revcast \<Longrightarrow> source_size rc = target_size rc + n \<Longrightarrow> rc w = scast (w >>> n)"
  for w :: "'a::len word"
  apply (simp add: source_size_def target_size_def)
  apply (rule bit_word_eqI)
  apply (simp add: bit_revcast_iff bit_word_scast_iff bit_sshiftr_word_iff ac_simps)
  done

lemma sshiftr_div_2n: "sint (w >>> n) = sint w div 2 ^ n"
  using sint_signed_drop_bit_eq [of n w]
  by (simp add: drop_bit_eq_div sshiftr_eq)

lemma mask_eq:
  \<open>mask n = (1 << n) - (1 :: 'a::len word)\<close>
  by transfer (simp add: mask_eq_exp_minus_1 push_bit_of_1)

lemma shiftl_0 [simp]: "(0::'a::len word) << n = 0"
  by transfer simp

lemma shiftr_0 [simp]: "(0::'a::len word) >> n = 0"
  by transfer simp

lemma nth_shiftl': "bit (w << m) n \<longleftrightarrow> n < size w \<and> n >= m \<and> bit w (n - m)"
  for w :: "'a::len word"
  by transfer (auto simp add: bit_push_bit_iff)

lemmas nth_shiftl = nth_shiftl' [unfolded word_size]

lemma nth_shiftr: "bit (w >> m) n = bit w (n + m)"
  for w :: "'a::len word"
  by (simp add: bit_simps ac_simps)

lemma shiftr_div_2n: "uint (shiftr w n) = uint w div 2 ^ n"
  by (fact uint_shiftr_eq)

lemma shiftl_rev: "shiftl w n = word_reverse (shiftr (word_reverse w) n)"
  by (rule bit_word_eqI) (auto simp add: bit_simps)

lemma rev_shiftl: "word_reverse w << n = word_reverse (w >> n)"
  by (simp add: shiftl_rev)

lemma shiftr_rev: "w >> n = word_reverse (word_reverse w << n)"
  by (simp add: rev_shiftl)

lemma rev_shiftr: "word_reverse w >> n = word_reverse (w << n)"
  by (simp add: shiftr_rev)

lemma shiftl_numeral [simp]:
  \<open>numeral k << numeral l = (push_bit (numeral l) (numeral k) :: 'a::len word)\<close>
  by (fact shiftl_word_eq)

lemma shiftl_zero_size: "size x \<le> n \<Longrightarrow> x << n = 0"
  for x :: "'a::len word"
  apply transfer
  apply (simp add: take_bit_push_bit)
  done

lemma shiftl_t2n: "shiftl w n = 2 ^ n * w"
  for w :: "'a::len word"
  by (simp add: shiftl_eq_push_bit push_bit_eq_mult)

lemma shiftr_numeral [simp]:
  \<open>(numeral k >> numeral n :: 'a::len word) = drop_bit (numeral n) (numeral k)\<close>
  by (fact shiftr_word_eq)

lemma shiftr_numeral_Suc [simp]:
  \<open>(numeral k >> Suc 0 :: 'a::len word) = drop_bit (Suc 0) (numeral k)\<close>
  by (fact shiftr_word_eq)

lemma slice_shiftr: "slice n w = ucast (w >> n)"
  apply (rule bit_word_eqI)
  apply (cases \<open>n \<le> LENGTH('b)\<close>)
   apply (auto simp add: bit_slice_iff bit_ucast_iff bit_shiftr_word_iff ac_simps
    dest: bit_imp_le_length)
  done

lemma revcast_down_uu [OF refl]:
  "rc = revcast \<Longrightarrow> source_size rc = target_size rc + n \<Longrightarrow> rc w = ucast (w >> n)"
  for w :: "'a::len word"
  apply (simp add: source_size_def target_size_def)
  apply (rule bit_word_eqI)
  apply (simp add: bit_revcast_iff bit_ucast_iff bit_shiftr_word_iff ac_simps)
  done

lemma revcast_down_su [OF refl]:
  "rc = revcast \<Longrightarrow> source_size rc = target_size rc + n \<Longrightarrow> rc w = scast (w >> n)"
  for w :: "'a::len word"
  apply (simp add: source_size_def target_size_def)
  apply (rule bit_word_eqI)
  apply (simp add: bit_revcast_iff bit_word_scast_iff bit_shiftr_word_iff ac_simps)
  done

lemma cast_down_rev [OF refl]:
  "uc = ucast \<Longrightarrow> source_size uc = target_size uc + n \<Longrightarrow> uc w = revcast (w << n)"
  for w :: "'a::len word"
  apply (simp add: source_size_def target_size_def)
  apply (rule bit_word_eqI)
  apply (simp add: bit_revcast_iff bit_word_ucast_iff bit_shiftl_word_iff)
  done

lemma revcast_up [OF refl]:
  "rc = revcast \<Longrightarrow> source_size rc + n = target_size rc \<Longrightarrow>
    rc w = (ucast w :: 'a::len word) << n"
  apply (simp add: source_size_def target_size_def)
  apply (rule bit_word_eqI)
  apply (simp add: bit_revcast_iff bit_word_ucast_iff bit_shiftl_word_iff)
  apply auto
  apply (metis add.commute add_diff_cancel_right)
  apply (metis diff_add_inverse2 diff_diff_add)
  done

lemmas rc1 = revcast_up [THEN
  revcast_rev_ucast [symmetric, THEN trans, THEN word_rev_gal, symmetric]]
lemmas rc2 = revcast_down_uu [THEN
  revcast_rev_ucast [symmetric, THEN trans, THEN word_rev_gal, symmetric]]

lemmas ucast_up =
  rc1 [simplified rev_shiftr [symmetric] revcast_ucast [symmetric]]
lemmas ucast_down =
  rc2 [simplified rev_shiftr revcast_ucast [symmetric]]

\<comment> \<open>problem posed by TPHOLs referee:
      criterion for overflow of addition of signed integers\<close>

lemma sofl_test:
  \<open>sint x + sint y = sint (x + y) \<longleftrightarrow>
    (x + y XOR x) AND (x + y XOR y) >> (size x - 1) = 0\<close>
  for x y :: \<open>'a::len word\<close>
proof -
  obtain n where n: \<open>LENGTH('a) = Suc n\<close>
    by (cases \<open>LENGTH('a)\<close>) simp_all
  have *: \<open>sint x + sint y + 2 ^ Suc n > signed_take_bit n (sint x + sint y) \<Longrightarrow> sint x + sint y \<ge> - (2 ^ n)\<close>
    \<open>signed_take_bit n (sint x + sint y) > sint x + sint y - 2 ^ Suc n \<Longrightarrow> 2 ^ n > sint x + sint y\<close>
    using signed_take_bit_int_greater_eq [of \<open>sint x + sint y\<close> n] signed_take_bit_int_less_eq [of n \<open>sint x + sint y\<close>]
    by (auto intro: ccontr)
  have \<open>sint x + sint y = sint (x + y) \<longleftrightarrow>
    (sint (x + y) < 0 \<longleftrightarrow> sint x < 0) \<or>
    (sint (x + y) < 0 \<longleftrightarrow> sint y < 0)\<close>
    using sint_less [of x] sint_greater_eq [of x] sint_less [of y] sint_greater_eq [of y]
    signed_take_bit_int_eq_self [of \<open>LENGTH('a) - 1\<close> \<open>sint x + sint y\<close>]
    apply (auto simp add: not_less)
       apply (unfold sint_word_ariths)
       apply (subst signed_take_bit_int_eq_self)
         prefer 4
         apply (subst signed_take_bit_int_eq_self)
           prefer 7
           apply (subst signed_take_bit_int_eq_self)
             prefer 10
             apply (subst signed_take_bit_int_eq_self)
               apply (auto simp add: signed_take_bit_int_eq_self signed_take_bit_eq_take_bit_minus take_bit_Suc_from_most n not_less intro!: *)
       apply (smt (z3) take_bit_nonnegative)
      apply (smt (z3) take_bit_int_less_exp)
     apply (smt (z3) take_bit_nonnegative)
    apply (smt (z3) take_bit_int_less_exp)
    done
  then show ?thesis
    apply (simp only: One_nat_def word_size shiftr_word_eq drop_bit_eq_zero_iff_not_bit_last bit_and_iff bit_xor_iff)
    apply (simp add: bit_last_iff)
    done
qed

lemma shiftr_zero_size: "size x \<le> n \<Longrightarrow> x >> n = 0"
  for x :: "'a :: len word"
  by (rule word_eqI) (auto simp add: nth_shiftr dest: test_bit_size)

lemma shiftr_x_0 [iff]: "x >> 0 = x"
  for x :: "'a::len word"
  by transfer simp

lemma shiftl_x_0 [simp]: "x << 0 = x"
  for x :: "'a::len word"
  by (simp add: shiftl_t2n)

lemma shiftl_1 [simp]: "(1::'a::len word) << n = 2^n"
  by (simp add: shiftl_t2n)

lemma shiftr_1[simp]: "(1::'a::len word) >> n = (if n = 0 then 1 else 0)"
  by (induct n) (auto simp: shiftr_def)

lemma shiftl0:
  "x << 0 = (x :: 'a :: len word)"
  by (fact shiftl_x_0)

lemma word_ops_nth:
  fixes x y :: \<open>'a::len word\<close>
  shows
  word_or_nth:  "bit (x OR y) n = (bit x n \<or> bit y n)" and
  word_and_nth: "bit (x AND y) n = (bit x n \<and> bit y n)" and
  word_xor_nth: "bit (x XOR y) n = (bit x n \<noteq> bit y n)"
  by (simp_all add: bit_simps)

lemma and_not_mask:
  "w AND NOT (mask n) = (w >> n) << n"
  for w :: \<open>'a::len word\<close>
  by (rule bit_word_eqI) (auto simp add: bit_simps)

lemma and_mask:
  "w AND mask n = (w << (size w - n)) >> (size w - n)"
  for w :: \<open>'a::len word\<close>
  by (rule bit_word_eqI) (auto simp add: bit_simps word_size)

lemma shiftr_div_2n_w: "n < size w \<Longrightarrow> w >> n = w div (2^n :: 'a :: len word)"
  apply (unfold word_div_def)
  apply (simp add: uint_2p_alt word_size)
  apply (metis uint_shiftr_eq word_of_int_uint)
  done

lemma le_shiftr:
  "u \<le> v \<Longrightarrow> u >> (n :: nat) \<le> (v :: 'a :: len word) >> n"
  apply transfer
  apply (simp add: take_bit_drop_bit)
  apply (simp add: drop_bit_eq_div zdiv_mono1)
  done

lemma shiftr_mask_le:
  "n <= m \<Longrightarrow> mask n >> m = (0 :: 'a::len word)"
  by (rule bit_word_eqI) (auto simp add: bit_simps)

lemma shiftr_mask [simp]:
  \<open>mask m >> m = (0::'a::len word)\<close>
  by (rule shiftr_mask_le) simp

lemma le_mask_iff:
  "(w \<le> mask n) = (w >> n = 0)"
  for w :: \<open>'a::len word\<close>
  apply safe
   apply (rule word_le_0_iff [THEN iffD1])
   apply (rule xtrans(3))
    apply (erule_tac [2] le_shiftr)
   apply simp
  apply (rule word_leI)
  apply (rename_tac n')
  apply (drule_tac x = "n' - n" in word_eqD)
  apply (simp add : nth_shiftr word_size bit_simps)
  apply (case_tac "n <= n'")
  by auto

lemma and_mask_eq_iff_shiftr_0:
  "(w AND mask n = w) = (w >> n = 0)"
  for w :: \<open>'a::len word\<close>
  apply (unfold test_bit_eq_iff [THEN sym])
  apply (rule iffI)
   apply (rule ext)
   apply (rule_tac [2] ext)
   apply (auto simp add : word_ao_nth nth_shiftr)
    apply (drule arg_cong)
    apply (drule iffD2)
     apply assumption
    apply (simp add : word_ao_nth)
   prefer 2
   apply (simp add : word_size test_bit_bin)
  apply transfer
  apply (auto simp add: fun_eq_iff bit_simps)
  apply (metis add_diff_inverse_nat)
  done

lemma mask_shiftl_decompose:
  "mask m << n = mask (m + n) AND NOT (mask n :: 'a::len word)"
  by (rule bit_word_eqI) (auto simp add: bit_simps)

lemma shiftl_over_and_dist:
  fixes a::"'a::len word"
  shows "(a AND b) << c = (a << c) AND (b << c)"
  apply(rule word_eqI)
  apply(simp add: word_ao_nth nth_shiftl, safe)
  done

lemma shiftr_over_and_dist:
  fixes a::"'a::len word"
  shows "a AND b >> c = (a >> c) AND (b >> c)"
  apply(rule word_eqI)
  apply(simp add:nth_shiftr word_ao_nth)
  done

lemma sshiftr_over_and_dist:
  fixes a::"'a::len word"
  shows "a AND b >>> c = (a >>> c) AND (b >>> c)"
  apply(rule word_eqI)
  apply(simp add:nth_sshiftr word_ao_nth word_size)
  done

lemma shiftl_over_or_dist:
  fixes a::"'a::len word"
  shows "a OR b << c = (a << c) OR (b << c)"
  apply(rule word_eqI)
  apply(simp add:nth_shiftl word_ao_nth, safe)
  done

lemma shiftr_over_or_dist:
  fixes a::"'a::len word"
  shows "a OR b >> c = (a >> c) OR (b >> c)"
  apply(rule word_eqI)
  apply(simp add:nth_shiftr word_ao_nth)
  done

lemma sshiftr_over_or_dist:
  fixes a::"'a::len word"
  shows "a OR b >>> c = (a >>> c) OR (b >>> c)"
  apply(rule word_eqI)
  apply(simp add:nth_sshiftr word_ao_nth word_size)
  done

lemmas shift_over_ao_dists =
  shiftl_over_or_dist shiftr_over_or_dist
  sshiftr_over_or_dist shiftl_over_and_dist
  shiftr_over_and_dist sshiftr_over_and_dist

lemma shiftl_shiftl:
  fixes a::"'a::len word"
  shows "a << b << c = a << (b + c)"
  apply(rule word_eqI)
  apply(auto simp:word_size nth_shiftl add.commute add.left_commute)
  done

lemma shiftr_shiftr:
  fixes a::"'a::len word"
  shows "a >> b >> c = a >> (b + c)"
  apply(rule word_eqI)
  apply(simp add:word_size nth_shiftr add.left_commute add.commute)
  done

lemma shiftl_shiftr1:
  fixes a::"'a::len word"
  shows "c \<le> b \<Longrightarrow> a << b >> c = a AND (mask (size a - b)) << (b - c)"
  apply(rule word_eqI)
  apply(auto simp:nth_shiftr nth_shiftl word_size word_ao_nth bit_simps)
  done

lemma shiftl_shiftr2:
  fixes a::"'a::len word"
  shows "b < c \<Longrightarrow> a << b >> c = (a >> (c - b)) AND (mask (size a - c))"
  apply(rule word_eqI)
  apply(auto simp:nth_shiftr nth_shiftl word_size word_ao_nth bit_simps)
  done

lemma shiftr_shiftl1:
  fixes a::"'a::len word"
  shows "c \<le> b \<Longrightarrow> a >> b << c = (a >> (b - c)) AND (NOT (mask c))"
  by (rule bit_word_eqI) (auto simp add: bit_simps)

lemma shiftr_shiftl2:
  fixes a::"'a::len word"
  shows "b < c \<Longrightarrow> a >> b << c = (a << (c - b)) AND (NOT (mask c))"
  apply(rule word_eqI)
  apply(auto simp:nth_shiftr nth_shiftl word_size word_ops_nth_size bit_simps)
  done

lemmas multi_shift_simps =
  shiftl_shiftl shiftr_shiftr
  shiftl_shiftr1 shiftl_shiftr2
  shiftr_shiftl1 shiftr_shiftl2

lemma shiftr_mask2:
  "n \<le> LENGTH('a) \<Longrightarrow> (mask n >> m :: ('a :: len) word) = mask (n - m)"
  by (rule bit_word_eqI) (auto simp add: bit_simps)

lemma word_shiftl_add_distrib:
  fixes x :: "'a :: len word"
  shows "(x + y) << n = (x << n) + (y << n)"
  by (simp add: shiftl_t2n ring_distribs)

lemma mask_shift:
  "(x AND NOT (mask y)) >> y = x >> y"
  for x :: \<open>'a::len word\<close>
  apply (rule bit_eqI)
  apply (simp add: bit_and_iff bit_not_iff bit_shiftr_word_iff bit_mask_iff not_le)
  using bit_imp_le_length apply auto
  done

lemma shiftr_div_2n':
  "unat (w >> n) = unat w div 2 ^ n"
  apply (unfold unat_eq_nat_uint)
  apply (subst shiftr_div_2n)
  apply (subst nat_div_distrib)
   apply simp
  apply (simp add: nat_power_eq)
  done

lemma shiftl_shiftr_id:
  assumes nv: "n < LENGTH('a)"
  and     xv: "x < 2 ^ (LENGTH('a) - n)"
  shows "x << n >> n = (x::'a::len word)"
  apply (simp add: shiftl_t2n)
  apply (rule word_eq_unatI)
  apply (subst shiftr_div_2n')
  apply (cases n)
   apply simp
  apply (subst iffD1 [OF unat_mult_lem])+
   apply (subst unat_power_lower[OF nv])
   apply (rule nat_less_power_trans [OF _ order_less_imp_le [OF nv]])
   apply (rule order_less_le_trans [OF unat_mono [OF xv] order_eq_refl])
   apply (rule unat_power_lower)
   apply simp
  apply (subst unat_power_lower[OF nv])
  apply simp
  done

lemma ucast_shiftl_eq_0:
  fixes w :: "'a :: len word"
  shows "\<lbrakk> n \<ge> LENGTH('b) \<rbrakk> \<Longrightarrow> ucast (w << n) = (0 :: 'b :: len word)"
  by transfer (simp add: take_bit_push_bit)

lemma word_shift_nonzero:
  "\<lbrakk> (x::'a::len word) \<le> 2 ^ m; m + n < LENGTH('a::len); x \<noteq> 0\<rbrakk>
   \<Longrightarrow> x << n \<noteq> 0"
  apply (simp only: word_neq_0_conv word_less_nat_alt
                    shiftl_t2n mod_0 unat_word_ariths
                    unat_power_lower word_le_nat_alt)
  apply (subst mod_less)
   apply (rule order_le_less_trans)
    apply (erule mult_le_mono2)
   apply (subst power_add[symmetric])
   apply (rule power_strict_increasing)
    apply simp
   apply simp
  apply simp
  done

lemma word_shiftr_lt:
  fixes w :: "'a::len word"
  shows "unat (w >> n) < (2 ^ (LENGTH('a) - n))"
  apply (subst shiftr_div_2n')
  apply transfer
  apply (simp flip: drop_bit_eq_div add: drop_bit_nat_eq drop_bit_take_bit)
  done

lemma shiftr_less_t2n':
  "\<lbrakk> x AND mask (n + m) = x; m < LENGTH('a) \<rbrakk> \<Longrightarrow> x >> n < 2 ^ m" for x :: "'a :: len word"
  apply (simp add: word_size mask_eq_iff_w2p [symmetric] flip: take_bit_eq_mask)
  apply transfer
  apply (simp add: take_bit_drop_bit ac_simps)
  done

lemma shiftr_less_t2n:
  "x < 2 ^ (n + m) \<Longrightarrow> x >> n < 2 ^ m" for x :: "'a :: len word"
  apply (rule shiftr_less_t2n')
   apply (erule less_mask_eq)
  apply (rule ccontr)
  apply (simp add: not_less)
  apply (subst (asm) p2_eq_0[symmetric])
  apply (simp add: power_add)
  done

lemma shiftr_eq_0:
  "n \<ge> LENGTH('a) \<Longrightarrow> ((w::'a::len word) >> n) = 0"
  apply (cut_tac shiftr_less_t2n'[of w n 0], simp)
   apply (simp add: mask_eq_iff)
  apply (simp add: lt2p_lem)
  apply simp
  done

lemma shiftl_less_t2n:
  fixes x :: "'a :: len word"
  shows "\<lbrakk> x < (2 ^ (m - n)); m < LENGTH('a) \<rbrakk> \<Longrightarrow> (x << n) < 2 ^ m"
  apply (simp add: word_size mask_eq_iff_w2p [symmetric] flip: take_bit_eq_mask)
  apply transfer
  apply (simp add: take_bit_push_bit)
  done

lemma shiftl_less_t2n':
  "(x::'a::len word) < 2 ^ m \<Longrightarrow> m+n < LENGTH('a) \<Longrightarrow> x << n < 2 ^ (m + n)"
  by (rule shiftl_less_t2n) simp_all

lemma scast_bit_test [simp]:
    "scast ((1 :: 'a::len signed word) << n) = (1 :: 'a word) << n"
  by (clarsimp simp: word_eq_iff)

lemma signed_shift_guard_to_word:
  "\<lbrakk> n < len_of TYPE ('a); n > 0 \<rbrakk>
    \<Longrightarrow> (unat (x :: 'a :: len word) * 2 ^ y < 2 ^ n)
    = (x = 0 \<or> x < (1 << n >> y))"
  apply (simp only: nat_mult_power_less_eq)
  apply (cases "y \<le> n")
   apply (simp only: shiftl_shiftr1)
   apply (subst less_mask_eq)
    apply (simp add: word_less_nat_alt word_size)
    apply (rule order_less_le_trans[rotated], rule power_increasing[where n=1])
      apply simp
     apply simp
    apply simp
   apply (simp add: nat_mult_power_less_eq word_less_nat_alt word_size)
   apply auto[1]
  apply (simp only: shiftl_shiftr2, simp add: unat_eq_0)
  done

lemma shiftr_not_mask_0:
  "n+m \<ge> LENGTH('a :: len) \<Longrightarrow> ((w::'a::len word) >> n) AND NOT (mask m) = 0"
  by (rule bit_word_eqI) (auto simp add: bit_simps word_size dest: bit_imp_le_length)

lemma shiftl_mask_is_0[simp]:
  "(x << n) AND mask n = 0"
  for x :: \<open>'a::len word\<close>
  by (simp flip: take_bit_eq_mask add: shiftl_eq_push_bit take_bit_push_bit)

lemma rshift_sub_mask_eq:
  "(a >> (size a - b)) AND mask b = a >> (size a - b)"
  for a :: \<open>'a::len word\<close>
  using shiftl_shiftr2[where a=a and b=0 and c="size a - b"]
  apply (cases "b < size a")
   apply simp
  apply (simp add: linorder_not_less mask_eq_decr_exp word_size
                   p2_eq_0[THEN iffD2])
  done

lemma shiftl_shiftr3:
  "b \<le> c \<Longrightarrow> a << b >> c = (a >> c - b) AND mask (size a - c)"
  for a :: \<open>'a::len word\<close>
  apply (cases "b = c")
   apply (simp add: shiftl_shiftr1)
  apply (simp add: shiftl_shiftr2)
  done

lemma and_mask_shiftr_comm:
  "m \<le> size w \<Longrightarrow> (w AND mask m) >> n = (w >> n) AND mask (m-n)"
  for w :: \<open>'a::len word\<close>
  by (simp add: and_mask shiftr_shiftr) (simp add: word_size shiftl_shiftr3)

lemma and_mask_shiftl_comm:
  "m+n \<le> size w \<Longrightarrow> (w AND mask m) << n = (w << n) AND mask (m+n)"
  for w :: \<open>'a::len word\<close>
  by (simp add: and_mask word_size shiftl_shiftl) (simp add: shiftl_shiftr1)

lemma le_mask_shiftl_le_mask: "s = m + n \<Longrightarrow> x \<le> mask n \<Longrightarrow> x << m \<le> mask s"
  for x :: \<open>'a::len word\<close>
  by (simp add: le_mask_iff shiftl_shiftr3)

lemma word_and_1_shiftl:
  "x AND (1 << n) = (if bit x n then (1 << n) else 0)" for x :: "'a :: len word"
  apply (rule bit_word_eqI; transfer)
  apply (auto simp add: bit_simps not_le ac_simps)
  done

lemmas word_and_1_shiftls'
    = word_and_1_shiftl[where n=0]
      word_and_1_shiftl[where n=1]
      word_and_1_shiftl[where n=2]

lemmas word_and_1_shiftls = word_and_1_shiftls' [simplified]

lemma word_and_mask_shiftl:
  "x AND (mask n << m) = ((x >> m) AND mask n) << m"
  for x :: \<open>'a::len word\<close>
  apply (rule bit_word_eqI; transfer)
  apply (auto simp add: bit_simps not_le ac_simps)
  done

lemma shift_times_fold:
  "(x :: 'a :: len word) * (2 ^ n) << m = x << (m + n)"
  by (simp add: shiftl_t2n ac_simps power_add)

lemma of_bool_nth:
  "of_bool (bit x v) = (x >> v) AND 1"
  for x :: \<open>'a::len word\<close>
  by (simp add: bit_iff_odd_drop_bit shiftr_word_eq word_and_1)

lemma shiftr_mask_eq:
  "(x >> n) AND mask (size x - n) = x >> n" for x :: "'a :: len word"
  apply (simp flip: take_bit_eq_mask)
  apply transfer
  apply (simp add: take_bit_drop_bit)
  done

lemma shiftr_mask_eq':
  "m = (size x - n) \<Longrightarrow> (x >> n) AND mask m = x >> n" for x :: "'a :: len word"
  by (simp add: shiftr_mask_eq)

lemma and_eq_0_is_nth:
  fixes x :: "'a :: len word"
  shows "y = 1 << n \<Longrightarrow> ((x AND y) = 0) = (\<not> (bit x n))"
  by (simp add: and_exp_eq_0_iff_not_bit)

lemma word_shift_zero:
  "\<lbrakk> x << n = 0; x \<le> 2^m; m + n < LENGTH('a)\<rbrakk> \<Longrightarrow> (x::'a::len word) = 0"
  apply (rule ccontr)
  apply (drule (2) word_shift_nonzero)
  apply simp
  done

lemma mask_shift_and_negate[simp]:"(w AND mask n << m) AND NOT (mask n << m) = 0"
  for w :: \<open>'a::len word\<close>
  by (clarsimp simp add: mask_eq_decr_exp Parity.bit_eq_iff bit_and_iff bit_not_iff shiftl_word_eq bit_push_bit_iff)

(* The seL4 bitfield generator produces functions containing mask and shift operations, such that
 * invoking two of them consecutively can produce something like the following.
 *)
lemma bitfield_op_twice:
  "(x AND NOT (mask n << m) OR ((y AND mask n) << m)) AND NOT (mask n << m) = x AND NOT (mask n << m)"
  for x :: \<open>'a::len word\<close>
  by (induct n arbitrary: m) (auto simp: word_ao_dist)

lemma bitfield_op_twice'':
  "\<lbrakk>NOT a = b << c; \<exists>x. b = mask x\<rbrakk> \<Longrightarrow> (x AND a OR (y AND b << c)) AND a = x AND a"
  for a b :: \<open>'a::len word\<close>
  apply clarsimp
  apply (cut_tac n=xa and m=c and x=x and y=y in bitfield_op_twice)
  apply (clarsimp simp:mask_eq_decr_exp)
  apply (drule not_switch)
  apply clarsimp
  done

lemma shiftr1_unfold: "x div 2 = x >> 1"
  by (simp add: drop_bit_eq_div shiftr_eq_drop_bit)

lemma shiftr1_is_div_2: "(x::('a::len) word) >> 1 = x div 2"
  by (simp add: drop_bit_eq_div shiftr_eq_drop_bit)

lemma shiftl1_is_mult: "(x << 1) = (x :: 'a::len word) * 2"
  by (metis One_nat_def mult_2 mult_2_right one_add_one
        power_0 power_Suc shiftl_t2n)

lemma shiftr1_lt:"x \<noteq> 0 \<Longrightarrow> (x::('a::len) word) >> 1 < x"
  apply (subst shiftr1_is_div_2)
  apply (rule div_less_dividend_word)
   apply simp+
  done

lemma shiftr1_0_or_1:"(x::('a::len) word) >> 1 = 0 \<Longrightarrow> x = 0 \<or> x = 1"
  apply (subst (asm) shiftr1_is_div_2)
  apply (drule word_less_div)
  apply (case_tac "LENGTH('a) = 1")
   apply (simp add:degenerate_word)
  apply (erule disjE)
   apply (subgoal_tac "(2::'a word) \<noteq> 0")
    apply simp
   apply (rule not_degenerate_imp_2_neq_0)
   apply (subgoal_tac "LENGTH('a) \<noteq> 0")
    apply arith
   apply simp
  apply (rule x_less_2_0_1', simp+)
  done

lemma shiftr1_irrelevant_lsb: "bit (x::('a::len) word) 0 \<or> x >> 1 = (x + 1) >> 1"
  apply (cases \<open>LENGTH('a)\<close>; transfer)
   apply (simp_all add: take_bit_drop_bit)
  apply (simp add: drop_bit_take_bit drop_bit_Suc)
  done

lemma shiftr1_0_imp_only_lsb:"((x::('a::len) word) + 1) >> 1 = 0 \<Longrightarrow> x = 0 \<or> x + 1 = 0"
  by (metis One_nat_def shiftr1_0_or_1 word_less_1 word_overflow)

lemma shiftr1_irrelevant_lsb': "\<not> (bit (x::('a::len) word) 0) \<Longrightarrow> x >> 1 = (x + 1) >> 1"
  by (metis shiftr1_irrelevant_lsb)

(* Perhaps this one should be a simp lemma, but it seems a little dangerous. *)
lemma cast_chunk_assemble_id:
  "\<lbrakk>n = LENGTH('a::len); m = LENGTH('b::len); n * 2 = m\<rbrakk> \<Longrightarrow>
  (((ucast ((ucast (x::'b word))::'a word))::'b word) OR (((ucast ((ucast (x >> n))::'a word))::'b word) << n)) = x"
  apply (subgoal_tac "((ucast ((ucast (x >> n))::'a word))::'b word) = x >> n")
   apply clarsimp
   apply (subst and_not_mask[symmetric])
   apply (subst ucast_ucast_mask)
   apply (subst word_ao_dist2[symmetric])
   apply clarsimp
  apply (rule ucast_ucast_len)
  apply (rule shiftr_less_t2n')
   apply (subst and_mask_eq_iff_le_mask)
   apply (simp_all add: mask_eq_decr_exp flip: mult_2_right)
  apply (metis add_diff_cancel_left' len_gt_0 mult_2_right zero_less_diff)
  done

lemma cast_chunk_scast_assemble_id:
  "\<lbrakk>n = LENGTH('a::len); m = LENGTH('b::len); n * 2 = m\<rbrakk> \<Longrightarrow>
  (((ucast ((scast (x::'b word))::'a word))::'b word) OR
   (((ucast ((scast (x >> n))::'a word))::'b word) << n)) = x"
  apply (subgoal_tac "((scast x)::'a word) = ((ucast x)::'a word)")
   apply (subgoal_tac "((scast (x >> n))::'a word) = ((ucast (x >> n))::'a word)")
    apply (simp add:cast_chunk_assemble_id)
   apply (subst down_cast_same[symmetric], subst is_down, arith, simp)+
  done

end
