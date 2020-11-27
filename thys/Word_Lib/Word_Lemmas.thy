(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

section "Lemmas with Generic Word Length"

theory Word_Lemmas
  imports
    Type_Syntax
    Signed_Division_Word
    Signed_Words
    More_Word
    Most_significant_bit
    Enumeration_Word
    Aligned
begin

text \<open>Lemmas about words\<close>

lemma nth_bounded:
  "\<lbrakk>(x :: 'a :: len word) !! n; x < 2 ^ m; m \<le> len_of TYPE ('a)\<rbrakk> \<Longrightarrow> n < m"
  apply (rule ccontr)
  apply (auto simp add: not_less test_bit_word_eq)
  apply (meson bit_imp_le_length bit_uint_iff less_2p_is_upper_bits_unset test_bit_bin)
  done

lemma shiftl_mask_is_0[simp]:
  "(x << n) AND mask n = 0"
  for x :: \<open>'a::len word\<close>
  apply (rule iffD1 [OF is_aligned_mask])
  apply (rule is_aligned_shiftl_self)
  done

lemma is_aligned_addD1:
  assumes al1: "is_aligned (x + y) n"
  and     al2: "is_aligned (x::'a::len word) n"
  shows "is_aligned y n"
  using al2
proof (rule is_aligned_get_word_bits)
  assume "x = 0" then show ?thesis using al1 by simp
next
  assume nv: "n < LENGTH('a)"
  from al1 obtain q1
    where xy: "x + y = 2 ^ n * of_nat q1" and "q1 < 2 ^ (LENGTH('a) - n)"
    by (rule is_alignedE)
  moreover from al2 obtain q2
    where x: "x = 2 ^ n * of_nat q2" and "q2 < 2 ^ (LENGTH('a) - n)"
    by (rule is_alignedE)
  ultimately have "y = 2 ^ n * (of_nat q1 - of_nat q2)"
    by (simp add: field_simps)
  then show ?thesis using nv by (simp add: is_aligned_mult_triv1)
qed

lemmas is_aligned_addD2 =
       is_aligned_addD1[OF subst[OF add.commute,
                                 of "%x. is_aligned x n" for n]]

lemma is_aligned_add:
  "\<lbrakk>is_aligned p n; is_aligned q n\<rbrakk> \<Longrightarrow> is_aligned (p + q) n"
  by (simp add: is_aligned_mask mask_add_aligned)

lemmas word_unat_Rep_inject1 = word_unat.Rep_inject[where y=1]
lemmas unat_eq_1 = unat_eq_0 word_unat_Rep_inject1[simplified]


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

lemma and_not_mask_twice:
  "(w AND NOT (mask n)) AND NOT (mask m) = w AND NOT (mask (max m n))"
  for w :: \<open>'a::len word\<close>
  apply (simp add: and_not_mask)
  apply (case_tac "n<m";
         simp add: shiftl_shiftr2 shiftl_shiftr1 not_less max_def shiftr_shiftr shiftl_shiftl)
   apply (cut_tac and_mask_shiftr_comm [where w=w and m="size w" and n=m, simplified,symmetric])
   apply (simp add: word_size mask_eq_decr_exp)
  apply (cut_tac and_mask_shiftr_comm [where w=w and m="size w" and n=n, simplified,symmetric])
  apply (simp add: word_size mask_eq_decr_exp)
  done

lemma word_less_cases:
  "x < y \<Longrightarrow> x = y - 1 \<or> x < y - (1 ::'a::len word)"
  apply (drule word_less_sub_1)
  apply (drule order_le_imp_less_or_eq)
  apply auto
  done

lemma eq_eqI:
  "a = b \<Longrightarrow> (a = x) = (b = x)"
  by simp

lemma mask_and_mask:
  "mask a AND mask b = (mask (min a b) :: 'a::len word)"
  by (simp flip: take_bit_eq_mask ac_simps)

lemma mask_eq_0_eq_x:
  "(x AND w = 0) = (x AND NOT w = x)"
  for x w :: \<open>'a::len word\<close>
  using word_plus_and_or_coroll2[where x=x and w=w]
  by auto

lemma mask_eq_x_eq_0:
  "(x AND w = x) = (x AND NOT w = 0)"
  for x w :: \<open>'a::len word\<close>
  using word_plus_and_or_coroll2[where x=x and w=w]
  by auto

lemma compl_of_1: "NOT 1 = (-2 :: 'a :: len word)"
  by (fact not_one)

lemma split_word_eq_on_mask:
  "(x = y) = (x AND m = y AND m \<and> x AND NOT m = y AND NOT m)"
  for x y m :: \<open>'a::len word\<close>
  apply transfer
  apply (simp add: bit_eq_iff)
  apply (auto simp add: bit_simps ac_simps)
  done

lemma map2_Cons_2_3:
  "(map2 f xs (y # ys) = (z # zs)) = (\<exists>x xs'. xs = x # xs' \<and> f x y = z \<and> map2 f xs' ys = zs)"
  by (case_tac xs, simp_all)

lemma map2_xor_replicate_False:
  "map2 (\<lambda>x y. x \<longleftrightarrow> \<not> y) xs (replicate n False) = take n xs"
  apply (induct xs arbitrary: n, simp)
  apply (case_tac n; simp)
  done

lemma word_and_1_shiftl:
  "x AND (1 << n) = (if x !! n then (1 << n) else 0)" for x :: "'a :: len word"
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

lemma plus_Collect_helper:
  "(+) x ` {xa. P (xa :: 'a :: len word)} = {xa. P (xa - x)}"
  by (fastforce simp add: image_def)

lemma plus_Collect_helper2:
  "(+) (- x) ` {xa. P (xa :: 'a :: len word)} = {xa. P (x + xa)}"
  using plus_Collect_helper [of "- x" P] by (simp add: ac_simps)

lemma word_FF_is_mask:
  "0xFF = (mask 8 :: 'a::len word)"
  by (simp add: mask_eq_decr_exp)

lemma word_1FF_is_mask:
  "0x1FF = (mask 9 :: 'a::len word)"
  by (simp add: mask_eq_decr_exp)

lemma ucast_of_nat_small:
  "x < 2 ^ LENGTH('a) \<Longrightarrow> ucast (of_nat x :: 'a :: len word) = (of_nat x :: 'b :: len word)"
  apply (rule sym, subst word_unat.inverse_norm)
  apply (simp add: ucast_eq of_nat_nat[symmetric] take_bit_eq_mod)
  done

lemma word_le_make_less:
  fixes x :: "'a :: len word"
  shows "y \<noteq> -1 \<Longrightarrow> (x \<le> y) = (x < (y + 1))"
  apply safe
  apply (erule plus_one_helper2)
  apply (simp add: eq_diff_eq[symmetric])
  done

lemmas finite_word = finite [where 'a="'a::len word"]

lemma word_to_1_set:
  "{0 ..< (1 :: 'a :: len word)} = {0}"
  by fastforce

lemma range_subset_eq2:
  "{a :: 'a :: len word .. b} \<noteq> {} \<Longrightarrow> ({a .. b} \<subseteq> {c .. d}) = (c \<le> a \<and> b \<le> d)"
  by simp

lemma word_leq_minus_one_le:
  fixes x :: "'a::len word"
  shows "\<lbrakk>y \<noteq> 0; x \<le> y - 1 \<rbrakk> \<Longrightarrow> x < y"
  using le_m1_iff_lt word_neq_0_conv by blast

lemma word_count_from_top:
  "n \<noteq> 0 \<Longrightarrow> {0 ..< n :: 'a :: len word} = {0 ..< n - 1} \<union> {n - 1}"
  apply (rule set_eqI, rule iffI)
   apply simp
   apply (drule word_le_minus_one_leq)
   apply (rule disjCI)
   apply simp
  apply simp
  apply (erule word_leq_minus_one_le)
  apply fastforce
  done

lemma word_minus_one_le_leq:
  "\<lbrakk> x - 1 < y \<rbrakk> \<Longrightarrow> x \<le> (y :: 'a :: len word)"
  apply (cases "x = 0")
   apply simp
  apply (simp add: word_less_nat_alt word_le_nat_alt)
  apply (subst(asm) unat_minus_one)
   apply (simp add: word_less_nat_alt)
  apply (cases "unat x")
   apply (simp add: unat_eq_zero)
  apply arith
  done

lemma word_div_less:
  "m < n \<Longrightarrow> m div n = 0" for m :: "'a :: len word"
  by (simp add: unat_mono word_arith_nat_defs(6))

lemma word_must_wrap:
  "\<lbrakk> x \<le> n - 1; n \<le> x \<rbrakk> \<Longrightarrow> n = (0 :: 'a :: len word)"
  using dual_order.trans sub_wrap word_less_1 by blast

lemma range_subset_card:
  "\<lbrakk> {a :: 'a :: len word .. b} \<subseteq> {c .. d}; b \<ge> a \<rbrakk> \<Longrightarrow> d \<ge> c \<and> d - c \<ge> b - a"
  using word_sub_le word_sub_mono by fastforce

lemma less_1_simp:
  "n - 1 < m = (n \<le> (m :: 'a :: len word) \<and> n \<noteq> 0)"
  by unat_arith

lemma nat_mod_power_lem:
  fixes a :: nat
  shows "1 < a \<Longrightarrow> a ^ n mod a ^ m = (if m \<le> n then 0 else a ^ n)"
  apply (clarsimp)
  apply (clarsimp simp add: le_iff_add power_add)
  done

lemma word_power_mod_div:
  fixes x :: "'a::len word"
  shows "\<lbrakk> n < LENGTH('a); m < LENGTH('a)\<rbrakk>
  \<Longrightarrow> x mod 2 ^ n div 2 ^ m = x div 2 ^ m mod 2 ^ (n - m)"
  apply (simp add: word_arith_nat_div unat_mod power_mod_div)
  apply (subst unat_arith_simps(3))
  apply (subst unat_mod)
  apply (subst unat_of_nat)+
  apply (simp add: mod_mod_power min.commute)
  done

lemma word_range_minus_1':
  fixes a :: "'a :: len word"
  shows "a \<noteq> 0 \<Longrightarrow> {a - 1<..b} = {a..b}"
  by (simp add: greaterThanAtMost_def atLeastAtMost_def greaterThan_def atLeast_def less_1_simp)

lemma word_range_minus_1:
  fixes a :: "'a :: len word"
  shows "b \<noteq> 0 \<Longrightarrow> {a..b - 1} = {a..<b}"
  apply (simp add: atLeastLessThan_def atLeastAtMost_def atMost_def lessThan_def)
  apply (rule arg_cong [where f = "\<lambda>x. {a..} \<inter> x"])
  apply rule
   apply clarsimp
   apply (erule contrapos_pp)
   apply (simp add: linorder_not_less linorder_not_le word_must_wrap)
  apply (clarsimp)
  apply (drule word_le_minus_one_leq)
  apply (auto simp: word_less_sub_1)
  done

lemma ucast_nat_def:
  "of_nat (unat x) = (ucast :: 'a :: len word \<Rightarrow> 'b :: len word) x"
  by transfer simp

lemma i_hate_words_helper:
  "i \<le> (j - k :: nat) \<Longrightarrow> i \<le> j"
  by simp

lemma i_hate_words:
  "unat (a :: 'a word) \<le> unat (b :: 'a :: len word) - Suc 0
    \<Longrightarrow> a \<noteq> -1"
  apply (frule i_hate_words_helper)
  apply (subst(asm) word_le_nat_alt[symmetric])
  apply (clarsimp simp only: word_minus_one_le)
  apply (simp only: linorder_not_less[symmetric])
  apply (erule notE)
  apply (rule diff_Suc_less)
  apply (subst neq0_conv[symmetric])
  apply (subst unat_eq_0)
  apply (rule notI, drule arg_cong[where f="(+) 1"])
  apply simp
  done

lemma overflow_plus_one_self:
  "(1 + p \<le> p) = (p = (-1 :: 'a :: len word))"
  apply rule
  apply (rule ccontr)
   apply (drule plus_one_helper2)
   apply (rule notI)
   apply (drule arg_cong[where f="\<lambda>x. x - 1"])
   apply simp
   apply (simp add: field_simps)
  apply simp
  done

lemma plus_1_less:
  "(x + 1 \<le> (x :: 'a :: len word)) = (x = -1)"
  apply (rule iffI)
   apply (rule ccontr)
   apply (cut_tac plus_one_helper2[where x=x, OF order_refl])
    apply simp
   apply clarsimp
   apply (drule arg_cong[where f="\<lambda>x. x - 1"])
   apply simp
  apply simp
  done

lemma pos_mult_pos_ge:
  "[|x > (0::int); n>=0 |] ==> n * x >= n*1"
  apply (simp only: mult_left_mono)
  done

lemma If_eq_obvious:
  "x \<noteq> z \<Longrightarrow> ((if P then x else y) = z) = (\<not> P \<and> y = z)"
  by simp

lemma Some_to_the:
  "v = Some x \<Longrightarrow> x = the v"
  by simp

lemma dom_if_Some:
  "dom (\<lambda>x. if P x then Some (f x) else g x) = {x. P x} \<union> dom g"
  by fastforce

lemma dom_insert_absorb:
  "x \<in> dom f \<Longrightarrow> insert x (dom f) = dom f" by auto

lemma emptyE2:
  "\<lbrakk> S = {}; x \<in> S \<rbrakk> \<Longrightarrow> P"
  by simp

lemma mod_div_equality_div_eq:
  "a div b * b = (a - (a mod b) :: int)"
  by (simp add: field_simps)

lemma zmod_helper:
  "n mod m = k \<Longrightarrow> ((n :: int) + a) mod m = (k + a) mod m"
  by (metis add.commute mod_add_right_eq)

lemma int_div_sub_1:
  "\<lbrakk> m \<ge> 1 \<rbrakk> \<Longrightarrow> (n - (1 :: int)) div m = (if m dvd n then (n div m) - 1 else n div m)"
  apply (subgoal_tac "m = 0 \<or> (n - (1 :: int)) div m = (if m dvd n then (n div m) - 1 else n div m)")
   apply fastforce
  apply (subst mult_cancel_right[symmetric])
  apply (simp only: left_diff_distrib split: if_split)
  apply (simp only: mod_div_equality_div_eq)
  apply (clarsimp simp: field_simps)
  apply (clarsimp simp: dvd_eq_mod_eq_0)
  apply (cases "m = 1")
   apply simp
  apply (subst mod_diff_eq[symmetric], simp add: zmod_minus1)
  apply clarsimp
  apply (subst diff_add_cancel[where b=1, symmetric])
  apply (subst mod_add_eq[symmetric])
  apply (simp add: field_simps)
  apply (rule mod_pos_pos_trivial)
   apply (subst add_0_right[where a=0, symmetric])
   apply (rule add_mono)
    apply simp
   apply simp
  apply (cases "(n - 1) mod m = m - 1")
   apply (drule zmod_helper[where a=1])
   apply simp
  apply (subgoal_tac "1 + (n - 1) mod m \<le> m")
   apply simp
  apply (subst field_simps, rule zless_imp_add1_zle)
  apply simp
  done

lemma ptr_add_image_multI:
  "\<lbrakk> \<And>x y. (x * val = y * val') = (x * val'' = y); x * val'' \<in> S \<rbrakk> \<Longrightarrow>
     ptr_add ptr (x * val) \<in> (\<lambda>p. ptr_add ptr (p * val')) ` S"
  apply (simp add: image_def)
  apply (erule rev_bexI)
  apply (rule arg_cong[where f="ptr_add ptr"])
  apply simp
  done

lemma shift_times_fold:
  "(x :: 'a :: len word) * (2 ^ n) << m = x << (m + n)"
  by (simp add: shiftl_t2n ac_simps power_add)

lemma word_plus_strict_mono_right:
  fixes x :: "'a :: len word"
  shows "\<lbrakk>y < z; x \<le> x + z\<rbrakk> \<Longrightarrow> x + y < x + z"
  by unat_arith

lemma replicate_minus:
  "k < n \<Longrightarrow> replicate n False = replicate (n - k) False @ replicate k False"
  by (subst replicate_add [symmetric]) simp

lemmas map_prod_split_imageI'
  = map_prod_imageI[where f="case_prod f" and g="case_prod g"
                    and a="(a, b)" and b="(c, d)" for a b c d f g]
lemmas map_prod_split_imageI = map_prod_split_imageI'[simplified]

lemma word_div_mult:
  "0 < c \<Longrightarrow> a < b * c \<Longrightarrow> a div c < b" for a b c :: "'a::len word"
  by (rule classical)
     (use div_to_mult_word_lt [of b a c] in
      \<open>auto simp add: word_less_nat_alt word_le_nat_alt unat_div\<close>)

lemma word_less_power_trans_ofnat:
  "\<lbrakk>n < 2 ^ (m - k); k \<le> m; m < LENGTH('a)\<rbrakk>
   \<Longrightarrow> of_nat n * 2 ^ k < (2::'a::len word) ^ m"
  apply (subst mult.commute)
  apply (rule word_less_power_trans)
    apply (simp_all add: word_less_nat_alt less_le_trans take_bit_eq_mod)
  done

lemma word_1_le_power:
  "n < LENGTH('a) \<Longrightarrow> (1 :: 'a :: len word) \<le> 2 ^ n"
  by (rule inc_le[where i=0, simplified], erule iffD2[OF p2_gt_0])

lemma of_bool_nth:
  "of_bool (x !! v) = (x >> v) AND 1"
  for x :: \<open>'a::len word\<close>
  by (simp add: test_bit_word_eq shiftr_word_eq bit_eq_iff)
    (auto simp add: bit_1_iff bit_and_iff bit_drop_bit_eq intro: ccontr)

lemma unat_1_0:
  "1 \<le> (x::'a::len word) = (0 < unat x)"
  by (auto simp add: word_le_nat_alt)

lemma x_less_2_0_1':
  fixes x :: "'a::len word"
  shows "\<lbrakk>LENGTH('a) \<noteq> 1; x < 2\<rbrakk> \<Longrightarrow> x = 0 \<or> x = 1"
  apply (cases \<open>2 \<le> LENGTH('a)\<close>)
  apply simp_all
  apply transfer
  apply auto
  apply (metis add.commute add.right_neutral even_two_times_div_two mod_div_trivial mod_pos_pos_trivial mult.commute mult_zero_left not_less not_take_bit_negative odd_two_times_div_two_succ) 
  done

lemmas word_add_le_iff2 = word_add_le_iff [folded no_olen_add_nat]

lemma of_nat_power:
  shows "\<lbrakk> p < 2 ^ x; x < len_of TYPE ('a) \<rbrakk> \<Longrightarrow> of_nat p < (2 :: 'a :: len word) ^ x"
  apply (rule order_less_le_trans)
   apply (rule of_nat_mono_maybe)
    apply (erule power_strict_increasing)
    apply simp
   apply assumption
  apply (simp add: word_unat_power del: of_nat_power)
  done

lemma of_nat_n_less_equal_power_2:
  "n < LENGTH('a::len) \<Longrightarrow> ((of_nat n)::'a word) < 2 ^ n"
  apply (induct n)
   apply clarsimp
  apply clarsimp
  apply (metis of_nat_power n_less_equal_power_2 of_nat_Suc power_Suc)
  done

lemma eq_mask_less:
  fixes w :: "'a::len word"
  assumes eqm: "w = w AND mask n"
  and      sz: "n < len_of TYPE ('a)"
  shows "w < (2::'a word) ^ n"
  by (subst eqm, rule and_mask_less' [OF sz])

lemma of_nat_mono_maybe':
  fixes Y :: "nat"
  assumes xlt: "x < 2 ^ len_of TYPE ('a)"
  assumes ylt: "y < 2 ^ len_of TYPE ('a)"
  shows   "(y < x) = (of_nat y < (of_nat x :: 'a :: len word))"
  apply (subst word_less_nat_alt)
  apply (subst unat_of_nat)+
  apply (subst mod_less)
   apply (rule ylt)
  apply (subst mod_less)
   apply (rule xlt)
  apply simp
  done

lemma shiftr_mask_eq:
  "(x >> n) AND mask (size x - n) = x >> n" for x :: "'a :: len word"
  apply (simp flip: take_bit_eq_mask)
  apply transfer
  apply (simp add: take_bit_drop_bit)
  done

lemma shiftr_mask_eq':
  "m = (size x - n) \<Longrightarrow> (x >> n) AND mask m = x >> n" for x :: "'a :: len word"
  by (simp add: shiftr_mask_eq)

lemma dom_if:
  "dom (\<lambda>a. if a \<in> addrs then Some (f a) else g a)  = addrs \<union> dom g"
  by (auto simp: dom_def split: if_split)

lemma of_nat_mono_maybe_le:
  "\<lbrakk>x < 2 ^ LENGTH('a); y < 2 ^ LENGTH('a)\<rbrakk> \<Longrightarrow>
  (y \<le> x) = ((of_nat y :: 'a :: len word) \<le> of_nat x)"
  apply (clarsimp simp: le_less)
  apply (rule disj_cong)
   apply (rule of_nat_mono_maybe', assumption+)
  apply (simp add: word_unat.norm_eq_iff [symmetric])
  done

lemma mask_AND_NOT_mask:
  "(w AND NOT (mask n)) AND mask n = 0"
  for w :: \<open>'a::len word\<close>
  by (rule bit_word_eqI) (simp add: bit_simps)

lemma AND_NOT_mask_plus_AND_mask_eq:
  "(w AND NOT (mask n)) + (w AND mask n) = w"
  for w :: \<open>'a::len word\<close>
  apply (subst disjunctive_add)
  apply (auto simp add: bit_simps)
  apply (rule bit_word_eqI)
  apply (auto simp add: bit_simps)
  done

lemma mask_eqI:
  fixes x :: "'a :: len word"
  assumes m1: "x AND mask n = y AND mask n"
  and     m2: "x AND NOT (mask n) = y AND NOT (mask n)"
  shows "x = y"
proof (subst bang_eq, rule allI)
  fix m

  show "x !! m = y !! m"
  proof (cases "m < n")
    case True
    then have "x !! m = ((x AND mask n) !! m)"
      by (simp add: word_size test_bit_conj_lt)
    also have "\<dots> = ((y AND mask n) !! m)" using m1 by simp
    also have "\<dots> = y !! m" using True
      by (simp add: word_size test_bit_conj_lt)
    finally show ?thesis .
  next
    case False
    then have "x !! m = ((x AND NOT (mask n)) !! m)"
      by (simp add: neg_mask_test_bit test_bit_conj_lt)
    also have "\<dots> = ((y AND NOT (mask n)) !! m)" using m2 by simp
    also have "\<dots> = y !! m" using False
      by (simp add: neg_mask_test_bit test_bit_conj_lt)
    finally show ?thesis .
  qed
qed

lemma nat_less_power_trans2:
  fixes n :: nat
  shows "\<lbrakk>n < 2 ^ (m - k); k \<le> m\<rbrakk> \<Longrightarrow> n * 2 ^ k  < 2 ^ m"
  by (subst mult.commute, erule (1) nat_less_power_trans)

lemma nat_move_sub_le: "(a::nat) + b \<le> c \<Longrightarrow> a \<le> c - b" by arith

lemma neq_0_no_wrap:
  fixes x :: "'a :: len word"
  shows "\<lbrakk> x \<le> x + y; x \<noteq> 0 \<rbrakk> \<Longrightarrow> x + y \<noteq> 0"
  by clarsimp

lemma plus_minus_one_rewrite:
  "v + (- 1 :: ('a :: {ring, one, uminus})) \<equiv> v - 1"
  by (simp add: field_simps)

lemma power_minus_is_div:
  "b \<le> a \<Longrightarrow> (2 :: nat) ^ (a - b) = 2 ^ a div 2 ^ b"
  apply (induct a arbitrary: b)
   apply simp
  apply (erule le_SucE)
   apply (clarsimp simp:Suc_diff_le le_iff_add power_add)
  apply simp
  done

lemma two_pow_div_gt_le:
  "v < 2 ^ n div (2 ^ m :: nat) \<Longrightarrow> m \<le> n"
  by (clarsimp dest!: less_two_pow_divD)

lemma unatSuc2:
  fixes n :: "'a :: len word"
  shows "n + 1 \<noteq> 0 \<Longrightarrow> unat (n + 1) = Suc (unat n)"
  by (simp add: add.commute unatSuc)

lemma word_of_nat_le:
  "n \<le> unat x \<Longrightarrow> of_nat n \<le> x"
  apply (simp add: word_le_nat_alt unat_of_nat)
  apply (erule order_trans[rotated])
  apply (simp add: take_bit_eq_mod)
  done

lemma word_unat_less_le:
   "a \<le> of_nat b \<Longrightarrow> unat a \<le> b"
   by (metis eq_iff le_cases le_unat_uoi word_of_nat_le)

lemma and_eq_0_is_nth:
  fixes x :: "'a :: len word"
  shows "y = 1 << n \<Longrightarrow> ((x AND y) = 0) = (\<not> (x !! n))"
  apply safe
   apply (drule_tac u="(x AND (1 << n))" and x=n in word_eqD)
   apply (simp add: nth_w2p)
   apply (simp add: test_bit_bin)
  apply (rule bit_word_eqI)
  apply (auto simp add: bit_simps test_bit_eq_bit)
  done

lemmas arg_cong_Not = arg_cong [where f=Not]
lemmas and_neq_0_is_nth = arg_cong_Not [OF and_eq_0_is_nth, simplified]

lemma nth_is_and_neq_0:
  "(x::'a::len word) !! n = (x AND 2 ^ n \<noteq> 0)"
  by (subst and_neq_0_is_nth; rule refl)

lemma mask_Suc_0 : "mask (Suc 0) = (1 :: 'a::len word)"
  by (simp add: mask_eq_decr_exp)

lemma ucast_ucast_add:
  fixes x :: "'a :: len word"
  fixes y :: "'b :: len word"
  shows
  "LENGTH('b) \<ge> LENGTH('a) \<Longrightarrow>
    ucast (ucast x + y) = x + ucast y"
  apply (rule word_unat.Rep_eqD)
  apply (simp add: unat_ucast unat_word_ariths mod_mod_power
                   min.absorb2 unat_of_nat)
  apply (subst mod_add_left_eq[symmetric])
  apply (simp add: mod_mod_power min.absorb2)
  apply (subst mod_add_right_eq)
  apply simp
  done

lemma word_shift_zero:
  "\<lbrakk> x << n = 0; x \<le> 2^m; m + n < LENGTH('a)\<rbrakk> \<Longrightarrow> (x::'a::len word) = 0"
  apply (rule ccontr)
  apply (drule (2) word_shift_nonzero)
  apply simp
  done

lemma bool_mask':
  fixes x :: "'a :: len word"
  shows "2 < LENGTH('a) \<Longrightarrow> (0 < x AND 1) = (x AND 1 = 1)"
  by (simp add: and_one_eq mod_2_eq_odd)

lemma scast_eq_ucast:
  "\<not> msb x \<Longrightarrow> scast x = ucast x"
  apply (cases \<open>LENGTH('a)\<close>)
  apply simp
  apply (rule bit_word_eqI)
  apply (auto simp add: bit_signed_iff bit_unsigned_iff min_def msb_word_eq)
  apply (erule notE)
  apply (metis le_less_Suc_eq test_bit_bin test_bit_word_eq)
  done

lemma lt1_neq0:
  fixes x :: "'a :: len word"
  shows "(1 \<le> x) = (x \<noteq> 0)" by unat_arith

lemma word_plus_one_nonzero:
  fixes x :: "'a :: len word"
  shows "\<lbrakk>x \<le> x + y; y \<noteq> 0\<rbrakk> \<Longrightarrow> x + 1 \<noteq> 0"
  apply (subst lt1_neq0 [symmetric])
  apply (subst olen_add_eqv [symmetric])
  apply (erule word_random)
  apply (simp add: lt1_neq0)
  done

lemma word_sub_plus_one_nonzero:
  fixes n :: "'a :: len word"
  shows "\<lbrakk>n' \<le> n; n' \<noteq> 0\<rbrakk> \<Longrightarrow> (n - n') + 1 \<noteq> 0"
  apply (subst lt1_neq0 [symmetric])
  apply (subst olen_add_eqv [symmetric])
  apply (rule word_random [where x' = n'])
   apply simp
   apply (erule word_sub_le)
  apply (simp add: lt1_neq0)
  done

lemma word_le_minus_mono_right:
  fixes x :: "'a :: len word"
  shows "\<lbrakk> z \<le> y; y \<le> x; z \<le> x \<rbrakk> \<Longrightarrow> x - y \<le> x - z"
  apply (rule word_sub_mono)
     apply simp
    apply assumption
   apply (erule word_sub_le)
  apply (erule word_sub_le)
  done

lemma drop_append_miracle:
  "n = length xs \<Longrightarrow> drop n (xs @ ys) = ys"
  by simp

lemma foldr_does_nothing_to_xf:
  "\<lbrakk> \<And>x s. x \<in> set xs \<Longrightarrow> xf (f x s) = xf s \<rbrakk> \<Longrightarrow> xf (foldr f xs s) = xf s"
  by (induct xs, simp_all)

lemma nat_less_mult_monoish: "\<lbrakk> a < b; c < (d :: nat) \<rbrakk> \<Longrightarrow> (a + 1) * (c + 1) <= b * d"
  apply (drule Suc_leI)+
  apply (drule(1) mult_le_mono)
  apply simp
  done

lemma word_0_sle_from_less:
  \<open>0 \<le>s x\<close> if \<open>x < 2 ^ (LENGTH('a) - 1)\<close> for x :: \<open>'a::len word\<close>
  using that
  apply transfer
  apply (cases \<open>LENGTH('a)\<close>)
   apply simp_all
  apply (metis bit_take_bit_iff min_def nat_less_le not_less_eq take_bit_int_eq_self_iff take_bit_take_bit)
  done

lemma ucast_sub_ucast:
  fixes x :: "'a::len word"
  assumes "y \<le> x"
  assumes T: "LENGTH('a) \<le> LENGTH('b)"
  shows "ucast (x - y) = (ucast x - ucast y :: 'b::len word)"
proof -
  from T
  have P: "unat x < 2 ^ LENGTH('b)" "unat y < 2 ^ LENGTH('b)"
    by (fastforce intro!: less_le_trans[OF unat_lt2p])+
  then show ?thesis
    by (simp add: unat_arith_simps unat_ucast assms[simplified unat_arith_simps])
qed

lemma word_1_0:
  "\<lbrakk>a + (1::('a::len) word) \<le> b; a < of_nat x\<rbrakk> \<Longrightarrow> a < b"
  apply transfer
  apply (subst (asm) take_bit_incr_eq)
   apply (auto simp add: diff_less_eq)
  using take_bit_int_less_exp le_less_trans by blast

lemma unat_of_nat_less:"\<lbrakk> a < b; unat b = c \<rbrakk> \<Longrightarrow> a < of_nat c"
  by fastforce

lemma word_le_plus_1: "\<lbrakk> (y::('a::len) word) < y + n; a < n \<rbrakk> \<Longrightarrow> y + a \<le> y + a + 1"
  by unat_arith

lemma word_le_plus:"\<lbrakk>(a::('a::len) word) < a + b; c < b\<rbrakk> \<Longrightarrow> a \<le> a + c"
by (metis order_less_imp_le word_random)

(*
 * Basic signed arithemetic properties.
 *)

lemma sint_minus1 [simp]: "(sint x = -1) = (x = -1)"
  by (metis sint_n1 word_sint.Rep_inverse')

lemma sint_0 [simp]: "(sint x = 0) = (x = 0)"
  by (metis sint_0 word_sint.Rep_inverse')

(* It is not always that case that "sint 1 = 1", because of 1-bit word sizes.
 * This lemma produces the different cases. *)
lemma sint_1_cases:
  P if \<open>\<lbrakk> len_of TYPE ('a::len) = 1; (a::'a word) = 0; sint a = 0 \<rbrakk> \<Longrightarrow> P\<close>
     \<open>\<lbrakk> len_of TYPE ('a) = 1; a = 1; sint (1 :: 'a word) = -1 \<rbrakk> \<Longrightarrow> P\<close>
     \<open>\<lbrakk> len_of TYPE ('a) > 1; sint (1 :: 'a word) = 1 \<rbrakk> \<Longrightarrow> P\<close>
proof (cases \<open>LENGTH('a) = 1\<close>)
  case True
  then have \<open>a = 0 \<or> a = 1\<close>
    by transfer auto
  with True that show ?thesis
    by auto
next
  case False
  with that show ?thesis
    by (simp add: less_le Suc_le_eq)
qed

lemma sint_int_min:
  "sint (- (2 ^ (LENGTH('a) - Suc 0)) :: ('a::len) word) = - (2 ^ (LENGTH('a) - Suc 0))"
  apply (subst word_sint.Abs_inverse' [where r="- (2 ^ (LENGTH('a) - Suc 0))"])
    apply (clarsimp simp: sints_num)
   apply (clarsimp simp: wi_hom_syms word_of_int_2p)
  apply clarsimp
  done

lemma sint_int_max_plus_1:
  "sint (2 ^ (LENGTH('a) - Suc 0) :: ('a::len) word) = - (2 ^ (LENGTH('a) - Suc 0))"
  apply (cases \<open>LENGTH('a)\<close>)
   apply simp_all
  apply (subst word_of_int_2p [symmetric])
  apply (subst int_word_sint)
  apply simp
  done

lemma sbintrunc_eq_in_range:
  "(sbintrunc n x = x) = (x \<in> range (sbintrunc n))"
  "(x = sbintrunc n x) = (x \<in> range (sbintrunc n))"
  apply (simp_all add: image_def)
  apply (metis sbintrunc_sbintrunc)+
  done

lemma sbintrunc_If:
  "- 3 * (2 ^ n) \<le> x \<and> x < 3 * (2 ^ n)
    \<Longrightarrow> sbintrunc n x = (if x < - (2 ^ n) then x + 2 * (2 ^ n)
        else if x \<ge> 2 ^ n then x - 2 * (2 ^ n) else x)"
  apply (simp add: no_sbintr_alt2, safe)
   apply (simp add: mod_pos_geq)
  apply (subst mod_add_self1[symmetric], simp)
  done

lemma signed_arith_eq_checks_to_ord:
  "(sint a + sint b = sint (a + b ))
    = ((a <=s a + b) = (0 <=s b))"
  "(sint a - sint b = sint (a - b ))
    = ((0 <=s a - b) = (b <=s a))"
  "(- sint a = sint (- a)) = (0 <=s (- a) = (a <=s 0))"
  using sint_range'[where x=a] sint_range'[where x=b]
  by (simp_all add: sint_word_ariths word_sle_eq word_sless_alt sbintrunc_If)

(* Signed word arithmetic overflow constraints. *)

lemma signed_arith_ineq_checks_to_eq:
  "((- (2 ^ (size a - 1)) \<le> (sint a + sint b)) \<and> (sint a + sint b \<le> (2 ^ (size a - 1) - 1)))
    = (sint a + sint b = sint (a + b ))"
  "((- (2 ^ (size a - 1)) \<le> (sint a - sint b)) \<and> (sint a - sint b \<le> (2 ^ (size a - 1) - 1)))
    = (sint a - sint b = sint (a - b))"
  "((- (2 ^ (size a - 1)) \<le> (- sint a)) \<and> (- sint a) \<le> (2 ^ (size a - 1) - 1))
    = ((- sint a) = sint (- a))"
  "((- (2 ^ (size a - 1)) \<le> (sint a * sint b)) \<and> (sint a * sint b \<le> (2 ^ (size a - 1) - 1)))
    = (sint a * sint b = sint (a * b))"
  "((- (2 ^ (size a - 1)) \<le> (sint a sdiv sint b)) \<and> (sint a sdiv sint b \<le> (2 ^ (size a - 1) - 1)))
    = (sint a sdiv sint b = sint (a sdiv b))"
  "((- (2 ^ (size a - 1)) \<le> (sint a smod sint b)) \<and> (sint a smod sint b \<le> (2 ^ (size a - 1) - 1)))
    = (sint a smod sint b = sint (a smod b))"
  by (auto simp: sint_word_ariths word_size signed_div_arith signed_mod_arith
                    sbintrunc_eq_in_range range_sbintrunc)

lemma signed_arith_sint:
  "((- (2 ^ (size a - 1)) \<le> (sint a + sint b)) \<and> (sint a + sint b \<le> (2 ^ (size a - 1) - 1)))
    \<Longrightarrow> sint (a + b) = (sint a + sint b)"
  "((- (2 ^ (size a - 1)) \<le> (sint a - sint b)) \<and> (sint a - sint b \<le> (2 ^ (size a - 1) - 1)))
    \<Longrightarrow> sint (a - b) = (sint a - sint b)"
  "((- (2 ^ (size a - 1)) \<le> (- sint a)) \<and> (- sint a) \<le> (2 ^ (size a - 1) - 1))
    \<Longrightarrow> sint (- a) = (- sint a)"
  "((- (2 ^ (size a - 1)) \<le> (sint a * sint b)) \<and> (sint a * sint b \<le> (2 ^ (size a - 1) - 1)))
    \<Longrightarrow> sint (a * b) = (sint a * sint b)"
  "((- (2 ^ (size a - 1)) \<le> (sint a sdiv sint b)) \<and> (sint a sdiv sint b \<le> (2 ^ (size a - 1) - 1)))
    \<Longrightarrow> sint (a sdiv b) = (sint a sdiv sint b)"
  "((- (2 ^ (size a - 1)) \<le> (sint a smod sint b)) \<and> (sint a smod sint b \<le> (2 ^ (size a - 1) - 1)))
    \<Longrightarrow> sint (a smod b) = (sint a smod sint b)"
  by (subst (asm) signed_arith_ineq_checks_to_eq; simp)+

lemma signed_mult_eq_checks_double_size:
  assumes mult_le: "(2 ^ (len_of TYPE ('a) - 1) + 1) ^ 2 \<le> (2 :: int) ^ (len_of TYPE ('b) - 1)"
           and le: "2 ^ (LENGTH('a) - 1) \<le> (2 :: int) ^ (len_of TYPE ('b) - 1)"
  shows "(sint (a :: 'a :: len word) * sint b = sint (a * b))
       = (scast a * scast b = (scast (a * b) :: 'b :: len word))"
proof -
  have P: "sbintrunc (size a - 1) (sint a * sint b) \<in> range (sbintrunc (size a - 1))"
    by simp

  have abs: "!! x :: 'a word. abs (sint x) < 2 ^ (size a - 1) + 1"
    apply (cut_tac x=x in sint_range')
    apply (simp add: abs_le_iff word_size)
    done
  have abs_ab: "abs (sint a * sint b) < 2 ^ (LENGTH('b) - 1)"
    using abs_mult_less[OF abs[where x=a] abs[where x=b]] mult_le
    by (simp add: abs_mult power2_eq_square word_size)
  define r s where \<open>r = LENGTH('a) - 1\<close> \<open>s = LENGTH('b) - 1\<close>
  then have \<open>LENGTH('a) = Suc r\<close> \<open>LENGTH('b) = Suc s\<close>
    \<open>size a = Suc r\<close> \<open>size b = Suc r\<close>
    by (simp_all add: word_size)
  then show ?thesis
    using P[unfolded range_sbintrunc] abs_ab le
    apply clarsimp
    apply (transfer fixing: r s)
    apply (auto simp add: signed_take_bit_int_eq_self simp flip: signed_take_bit_eq_iff_take_bit_eq)
    done
qed

(* Properties about signed division. *)

lemma int_sdiv_simps [simp]:
    "(a :: int) sdiv 1 = a"
    "(a :: int) sdiv 0 = 0"
    "(a :: int) sdiv -1 = -a"
  apply (auto simp: signed_divide_int_def sgn_if)
  done

lemma sgn_div_eq_sgn_mult:
    "a div b \<noteq> 0 \<Longrightarrow> sgn ((a :: int) div b) = sgn (a * b)"
  apply (clarsimp simp: sgn_if zero_le_mult_iff neg_imp_zdiv_nonneg_iff not_less)
  apply (metis less_le mult_le_0_iff neg_imp_zdiv_neg_iff not_less pos_imp_zdiv_neg_iff zdiv_eq_0_iff)
  done

lemma sgn_sdiv_eq_sgn_mult:
  "a sdiv b \<noteq> 0 \<Longrightarrow> sgn ((a :: int) sdiv b) = sgn (a * b)"
  by (auto simp: signed_divide_int_def sgn_div_eq_sgn_mult sgn_mult)

lemma int_sdiv_same_is_1 [simp]:
    "a \<noteq> 0 \<Longrightarrow> ((a :: int) sdiv b = a) = (b = 1)"
  apply (rule iffI)
   apply (clarsimp simp: signed_divide_int_def)
   apply (subgoal_tac "b > 0")
    apply (case_tac "a > 0")
     apply (clarsimp simp: sgn_if)
    apply (clarsimp simp: algebra_split_simps not_less)
    apply (metis int_div_same_is_1 le_neq_trans minus_minus neg_0_le_iff_le neg_equal_0_iff_equal)
   apply (case_tac "a > 0")
    apply (case_tac "b = 0")
     apply clarsimp
    apply (rule classical)
    apply (clarsimp simp: sgn_mult not_less)
    apply (metis le_less neg_0_less_iff_less not_less_iff_gr_or_eq pos_imp_zdiv_neg_iff)
   apply (rule classical)
   apply (clarsimp simp: algebra_split_simps sgn_mult not_less sgn_if split: if_splits)
   apply (metis antisym less_le neg_imp_zdiv_nonneg_iff)
  apply (clarsimp simp: signed_divide_int_def sgn_if)
  done

lemma int_sdiv_negated_is_minus1 [simp]:
    "a \<noteq> 0 \<Longrightarrow> ((a :: int) sdiv b = - a) = (b = -1)"
  apply (clarsimp simp: signed_divide_int_def)
  apply (rule iffI)
   apply (subgoal_tac "b < 0")
    apply (case_tac "a > 0")
     apply (clarsimp simp: sgn_if algebra_split_simps not_less)
    apply (case_tac "sgn (a * b) = -1")
     apply (clarsimp simp: not_less algebra_split_simps)
    apply (clarsimp simp: algebra_split_simps not_less)
   apply (rule classical)
   apply (case_tac "b = 0")
    apply (clarsimp simp: not_less sgn_mult)
   apply (case_tac "a > 0")
    apply (clarsimp simp: not_less sgn_mult)
    apply (metis less_le neg_less_0_iff_less not_less_iff_gr_or_eq pos_imp_zdiv_neg_iff)
   apply (clarsimp simp: not_less sgn_mult)
   apply (metis antisym_conv div_minus_right neg_imp_zdiv_nonneg_iff neg_le_0_iff_le not_less)
  apply (clarsimp simp: sgn_if)
  done

lemma sdiv_int_range:
    "(a :: int) sdiv b \<in> { - (abs a) .. (abs a) }"
  apply (unfold signed_divide_int_def)
  apply (subgoal_tac "(abs a) div (abs b) \<le> (abs a)")
   apply (auto simp add: sgn_if not_less)
      apply (metis le_less le_less_trans neg_equal_0_iff_equal neg_less_iff_less not_le pos_imp_zdiv_neg_iff)
     apply (metis add.inverse_neutral div_int_pos_iff le_less neg_le_iff_le order_trans)
    apply (metis div_minus_right le_less_trans neg_imp_zdiv_neg_iff neg_less_0_iff_less not_le)
  using div_int_pos_iff apply fastforce
  apply (metis abs_0_eq abs_ge_zero div_by_0 zdiv_le_dividend zero_less_abs_iff)
  done

lemma word_sdiv_div1 [simp]:
    "(a :: ('a::len) word) sdiv 1 = a"
  apply (rule sint_1_cases [where a=a])
    apply (clarsimp simp: sdiv_word_def signed_divide_int_def)
   apply (clarsimp simp: sdiv_word_def signed_divide_int_def simp del: sint_minus1)
  apply (clarsimp simp: sdiv_word_def)
  done

lemma sdiv_int_div_0 [simp]:
  "(x :: int) sdiv 0 = 0"
  by (clarsimp simp: signed_divide_int_def)

lemma sdiv_int_0_div [simp]:
  "0 sdiv (x :: int) = 0"
  by (clarsimp simp: signed_divide_int_def)

lemma word_sdiv_div0 [simp]:
    "(a :: ('a::len) word) sdiv 0 = 0"
  apply (auto simp: sdiv_word_def signed_divide_int_def sgn_if)
  done

lemma word_sdiv_div_minus1 [simp]:
    "(a :: ('a::len) word) sdiv -1 = -a"
  apply (auto simp: sdiv_word_def signed_divide_int_def sgn_if)
  done

lemmas word_sdiv_0 = word_sdiv_div0

lemma sdiv_word_min:
    "- (2 ^ (size a - 1)) \<le> sint (a :: ('a::len) word) sdiv sint (b :: ('a::len) word)"
  apply (clarsimp simp: word_size)
  apply (cut_tac sint_range' [where x=a])
  apply (cut_tac sint_range' [where x=b])
  apply clarsimp
  apply (insert sdiv_int_range [where a="sint a" and b="sint b"])
  apply (clarsimp simp: max_def abs_if split: if_split_asm)
  done

lemma sdiv_word_max:
    "(sint (a :: ('a::len) word) sdiv sint (b :: ('a::len) word) < (2 ^ (size a - 1))) =
          ((a \<noteq> - (2 ^ (size a - 1)) \<or> (b \<noteq> -1)))"
    (is "?lhs = (\<not> ?a_int_min \<or> \<not> ?b_minus1)")
proof (rule classical)
  assume not_thesis: "\<not> ?thesis"

  have not_zero: "b \<noteq> 0"
    using not_thesis
    by (clarsimp)

  have result_range: "sint a sdiv sint b \<in> (sints (size a)) \<union> {2 ^ (size a - 1)}"
    apply (cut_tac sdiv_int_range [where a="sint a" and b="sint b"])
    apply (erule rev_subsetD)
    using sint_range' [where x=a]  sint_range' [where x=b]
    apply (auto simp: max_def abs_if word_size sints_num)
    done

  have result_range_overflow: "(sint a sdiv sint b = 2 ^ (size a - 1)) = (?a_int_min \<and> ?b_minus1)"
    apply (rule iffI [rotated])
     apply (clarsimp simp: signed_divide_int_def sgn_if word_size sint_int_min)
    apply (rule classical)
    apply (case_tac "?a_int_min")
     apply (clarsimp simp: word_size sint_int_min)
     apply (metis diff_0_right
              int_sdiv_negated_is_minus1 minus_diff_eq minus_int_code(2)
              power_eq_0_iff sint_minus1 zero_neq_numeral)
    apply (subgoal_tac "abs (sint a) < 2 ^ (size a - 1)")
     apply (insert sdiv_int_range [where a="sint a" and b="sint b"])[1]
     apply (clarsimp simp: word_size)
    apply (insert sdiv_int_range [where a="sint a" and b="sint b"])[1]
    apply (insert word_sint.Rep [where x="a"])[1]
    apply (clarsimp simp: minus_le_iff word_size abs_if sints_num split: if_split_asm)
    apply (metis minus_minus sint_int_min word_sint.Rep_inject)
    done

  have result_range_simple: "(sint a sdiv sint b \<in> (sints (size a))) \<Longrightarrow> ?thesis"
    apply (insert sdiv_int_range [where a="sint a" and b="sint b"])
    apply (clarsimp simp: word_size sints_num sint_int_min)
    done

  show ?thesis
    apply (rule UnE [OF result_range result_range_simple])
     apply simp
    apply (clarsimp simp: word_size)
    using result_range_overflow
    apply (clarsimp simp: word_size)
    done
qed

lemmas sdiv_word_min' = sdiv_word_min [simplified word_size, simplified]
lemmas sdiv_word_max' = sdiv_word_max [simplified word_size, simplified]

lemmas word_sdiv_numerals_lhs = sdiv_word_def[where v="numeral x" for x]
    sdiv_word_def[where v=0] sdiv_word_def[where v=1]

lemmas word_sdiv_numerals = word_sdiv_numerals_lhs[where w="numeral y" for y]
    word_sdiv_numerals_lhs[where w=0] word_sdiv_numerals_lhs[where w=1]

(*
 * Signed modulo properties.
 *)

lemma smod_int_alt_def:
     "(a::int) smod b = sgn (a) * (abs a mod abs b)"
  apply (clarsimp simp: signed_modulo_int_def signed_divide_int_def)
  apply (clarsimp simp: minus_div_mult_eq_mod [symmetric] abs_sgn sgn_mult sgn_if algebra_split_simps)
  done

lemma smod_int_range:
  "b \<noteq> 0 \<Longrightarrow> (a::int) smod b \<in> { - abs b + 1 .. abs b - 1 }"
  apply (case_tac  "b > 0")
   apply (insert pos_mod_conj [where a=a and b=b])[1]
   apply (insert pos_mod_conj [where a="-a" and b=b])[1]
   apply (auto simp: smod_int_alt_def algebra_simps sgn_if
              abs_if not_less add1_zle_eq [simplified add.commute])[1]
    apply (metis add_nonneg_nonneg int_one_le_iff_zero_less le_less less_add_same_cancel2 not_le pos_mod_conj)
  apply (metis (full_types) add.inverse_inverse eucl_rel_int eucl_rel_int_iff le_less_trans neg_0_le_iff_le)
  apply (insert neg_mod_conj [where a=a and b="b"])[1]
  apply (insert neg_mod_conj [where a="-a" and b="b"])[1]
  apply (clarsimp simp: smod_int_alt_def algebra_simps sgn_if
            abs_if not_less add1_zle_eq [simplified add.commute])
  apply (metis neg_0_less_iff_less neg_mod_conj not_le not_less_iff_gr_or_eq order_trans pos_mod_conj)
  done

lemma smod_int_compares:
   "\<lbrakk> 0 \<le> a; 0 < b \<rbrakk> \<Longrightarrow> (a :: int) smod b < b"
   "\<lbrakk> 0 \<le> a; 0 < b \<rbrakk> \<Longrightarrow> 0 \<le> (a :: int) smod b"
   "\<lbrakk> a \<le> 0; 0 < b \<rbrakk> \<Longrightarrow> -b < (a :: int) smod b"
   "\<lbrakk> a \<le> 0; 0 < b \<rbrakk> \<Longrightarrow> (a :: int) smod b \<le> 0"
   "\<lbrakk> 0 \<le> a; b < 0 \<rbrakk> \<Longrightarrow> (a :: int) smod b < - b"
   "\<lbrakk> 0 \<le> a; b < 0 \<rbrakk> \<Longrightarrow> 0 \<le> (a :: int) smod b"
   "\<lbrakk> a \<le> 0; b < 0 \<rbrakk> \<Longrightarrow> (a :: int) smod b \<le> 0"
   "\<lbrakk> a \<le> 0; b < 0 \<rbrakk> \<Longrightarrow> b \<le> (a :: int) smod b"
  apply (insert smod_int_range [where a=a and b=b])
  apply (auto simp: add1_zle_eq smod_int_alt_def sgn_if)
  done

lemma smod_int_mod_0 [simp]:
  "x smod (0 :: int) = x"
  by (clarsimp simp: signed_modulo_int_def)

lemma smod_int_0_mod [simp]:
  "0 smod (x :: int) = 0"
  by (clarsimp simp: smod_int_alt_def)

lemma smod_word_mod_0 [simp]:
  "x smod (0 :: ('a::len) word) = x"
  by (clarsimp simp: smod_word_def)

lemma smod_word_0_mod [simp]:
  "0 smod (x :: ('a::len) word) = 0"
  by (clarsimp simp: smod_word_def)

lemma smod_word_max:
    "sint (a::'a word) smod sint (b::'a word) < 2 ^ (LENGTH('a::len) - Suc 0)"
  apply (case_tac "b = 0")
   apply (insert word_sint.Rep [where x=a, simplified sints_num])[1]
   apply (clarsimp)
  apply (insert word_sint.Rep [where x="b", simplified sints_num])[1]
  apply (insert smod_int_range [where a="sint a" and b="sint b"])
  apply (clarsimp simp: abs_if split: if_split_asm)
  done

lemma smod_word_min:
    "- (2 ^ (LENGTH('a::len) - Suc 0)) \<le> sint (a::'a word) smod sint (b::'a word)"
  apply (case_tac "b = 0")
   apply (insert word_sint.Rep [where x=a, simplified sints_num])[1]
   apply clarsimp
  apply (insert word_sint.Rep [where x=b, simplified sints_num])[1]
  apply (insert smod_int_range [where a="sint a" and b="sint b"])
  apply (clarsimp simp: abs_if add1_zle_eq split: if_split_asm)
  done

lemma smod_word_alt_def:
  "(a :: ('a::len) word) smod b = a - (a sdiv b) * b"
  apply (cases \<open>a \<noteq> - (2 ^ (LENGTH('a) - 1)) \<or> b \<noteq> - 1\<close>)
   apply (clarsimp simp: smod_word_def sdiv_word_def signed_modulo_int_def
     simp flip: wi_hom_sub wi_hom_mult)
  apply (clarsimp simp: smod_word_def signed_modulo_int_def)
  done

lemmas word_smod_numerals_lhs = smod_word_def[where v="numeral x" for x]
    smod_word_def[where v=0] smod_word_def[where v=1]

lemmas word_smod_numerals = word_smod_numerals_lhs[where w="numeral y" for y]
    word_smod_numerals_lhs[where w=0] word_smod_numerals_lhs[where w=1]

lemma sint_of_int_eq:
  "\<lbrakk> - (2 ^ (LENGTH('a) - 1)) \<le> x; x < 2 ^ (LENGTH('a) - 1) \<rbrakk> \<Longrightarrow> sint (of_int x :: ('a::len) word) = x"
  by (simp add: signed_take_bit_int_eq_self)

lemma of_int_sint:
  "of_int (sint a) = a"
  by simp

lemma nth_w2p_scast [simp]:
  "((scast ((2::'a::len signed word) ^ n) :: 'a word) !! m)
         \<longleftrightarrow> ((((2::'a::len  word) ^ n) :: 'a word) !! m)"
  by transfer (auto simp add: bit_simps)

lemma scast_2_power [simp]: "scast ((2 :: 'a::len signed word) ^ x) = ((2 :: 'a word) ^ x)"
  by (clarsimp simp: word_eq_iff)

lemma scast_bit_test [simp]:
    "scast ((1 :: 'a::len signed word) << n) = (1 :: 'a word) << n"
  by (clarsimp simp: word_eq_iff)

lemma ucast_nat_def':
  "of_nat (unat x) = (ucast :: 'a :: len word \<Rightarrow> ('b :: len) signed word) x"
  by (fact ucast_nat_def)

lemma mod_mod_power_int:
  fixes k :: int
  shows "k mod 2 ^ m mod 2 ^ n = k mod 2 ^ (min m n)"
  by (metis bintrunc_bintrunc_min bintrunc_mod2p min.commute)

(* Normalise combinations of scast and ucast. *)

lemma ucast_distrib:
  fixes M :: "'a::len word \<Rightarrow> 'a::len word \<Rightarrow> 'a::len word"
  fixes M' :: "'b::len word \<Rightarrow> 'b::len word \<Rightarrow> 'b::len word"
  fixes L :: "int \<Rightarrow> int \<Rightarrow> int"
  assumes lift_M: "\<And>x y. uint (M x y) = L (uint x) (uint y)  mod 2 ^ LENGTH('a)"
  assumes lift_M': "\<And>x y. uint (M' x y) = L (uint x) (uint y)  mod 2 ^ LENGTH('b)"
  assumes distrib: "\<And>x y. (L (x mod (2 ^ LENGTH('b))) (y mod (2 ^ LENGTH('b)))) mod (2 ^ LENGTH('b))
                               = (L x y) mod (2 ^ LENGTH('b))"
  assumes is_down: "is_down (ucast :: 'a word \<Rightarrow> 'b word)"
  shows "ucast (M a b) = M' (ucast a) (ucast b)"
  apply (simp only: ucast_eq)
  apply (subst lift_M)
  apply (subst of_int_uint [symmetric], subst lift_M')
  apply (subst (1 2) int_word_uint)
  apply (subst word_ubin.norm_eq_iff [symmetric])
  apply (subst (1 2) bintrunc_mod2p)
  apply (insert is_down)
  apply (unfold is_down_def)
  apply (clarsimp simp: target_size source_size)
  apply (clarsimp simp: mod_mod_power_int min_def)
  apply (rule distrib [symmetric])
  done

lemma ucast_down_add:
    "is_down (ucast:: 'a word \<Rightarrow> 'b word) \<Longrightarrow>  ucast ((a :: 'a::len word) + b) = (ucast a + ucast b :: 'b::len word)"
  by (rule ucast_distrib [where L="(+)"], (clarsimp simp: uint_word_ariths)+, presburger, simp)

lemma ucast_down_minus:
    "is_down (ucast:: 'a word \<Rightarrow> 'b word) \<Longrightarrow>  ucast ((a :: 'a::len word) - b) = (ucast a - ucast b :: 'b::len word)"
  apply (rule ucast_distrib [where L="(-)"], (clarsimp simp: uint_word_ariths)+)
  apply (metis mod_diff_left_eq mod_diff_right_eq)
  apply simp
  done

lemma ucast_down_mult:
    "is_down (ucast:: 'a word \<Rightarrow> 'b word) \<Longrightarrow>  ucast ((a :: 'a::len word) * b) = (ucast a * ucast b :: 'b::len word)"
  apply (rule ucast_distrib [where L="(*)"], (clarsimp simp: uint_word_ariths)+)
  apply (metis mod_mult_eq)
  apply simp
  done

lemma scast_distrib:
  fixes M :: "'a::len word \<Rightarrow> 'a::len word \<Rightarrow> 'a::len word"
  fixes M' :: "'b::len word \<Rightarrow> 'b::len word \<Rightarrow> 'b::len word"
  fixes L :: "int \<Rightarrow> int \<Rightarrow> int"
  assumes lift_M: "\<And>x y. uint (M x y) = L (uint x) (uint y)  mod 2 ^ LENGTH('a)"
  assumes lift_M': "\<And>x y. uint (M' x y) = L (uint x) (uint y)  mod 2 ^ LENGTH('b)"
  assumes distrib: "\<And>x y. (L (x mod (2 ^ LENGTH('b))) (y mod (2 ^ LENGTH('b)))) mod (2 ^ LENGTH('b))
                               = (L x y) mod (2 ^ LENGTH('b))"
  assumes is_down: "is_down (scast :: 'a word \<Rightarrow> 'b word)"
  shows "scast (M a b) = M' (scast a) (scast b)"
  apply (subst (1 2 3) down_cast_same [symmetric])
   apply (insert is_down)
   apply (clarsimp simp: is_down_def target_size source_size is_down)
  apply (rule ucast_distrib [where L=L, OF lift_M lift_M' distrib])
  apply (insert is_down)
  apply (clarsimp simp: is_down_def target_size source_size is_down)
  done

lemma scast_down_add:
    "is_down (scast:: 'a word \<Rightarrow> 'b word) \<Longrightarrow>  scast ((a :: 'a::len word) + b) = (scast a + scast b :: 'b::len word)"
  by (rule scast_distrib [where L="(+)"], (clarsimp simp: uint_word_ariths)+, presburger, simp)

lemma scast_down_minus:
    "is_down (scast:: 'a word \<Rightarrow> 'b word) \<Longrightarrow>  scast ((a :: 'a::len word) - b) = (scast a - scast b :: 'b::len word)"
  apply (rule scast_distrib [where L="(-)"], (clarsimp simp: uint_word_ariths)+)
  apply (metis mod_diff_left_eq mod_diff_right_eq)
  apply simp
  done

lemma scast_down_mult:
    "is_down (scast:: 'a word \<Rightarrow> 'b word) \<Longrightarrow>  scast ((a :: 'a::len word) * b) = (scast a * scast b :: 'b::len word)"
  apply (rule scast_distrib [where L="(*)"], (clarsimp simp: uint_word_ariths)+)
  apply (metis mod_mult_eq)
  apply simp
  done

lemma scast_ucast_1:
  "\<lbrakk> is_down (ucast :: 'a word \<Rightarrow> 'b word); is_down (ucast :: 'b word \<Rightarrow> 'c word) \<rbrakk> \<Longrightarrow>
         (scast (ucast (a :: 'a::len word) :: 'b::len word) :: 'c::len word) = ucast a"
  by (metis down_cast_same ucast_eq ucast_down_wi)

lemma scast_ucast_3:
  "\<lbrakk> is_down (ucast :: 'a word \<Rightarrow> 'c word); is_down (ucast :: 'b word \<Rightarrow> 'c word) \<rbrakk> \<Longrightarrow>
         (scast (ucast (a :: 'a::len word) :: 'b::len word) :: 'c::len word) = ucast a"
  by (metis down_cast_same ucast_eq ucast_down_wi)

lemma scast_ucast_4:
  "\<lbrakk> is_up (ucast :: 'a word \<Rightarrow> 'b word); is_down (ucast :: 'b word \<Rightarrow> 'c word) \<rbrakk> \<Longrightarrow>
         (scast (ucast (a :: 'a::len word) :: 'b::len word) :: 'c::len word) = ucast a"
  by (metis down_cast_same ucast_eq ucast_down_wi)

lemma scast_scast_b:
  "\<lbrakk> is_up (scast :: 'a word \<Rightarrow> 'b word) \<rbrakk> \<Longrightarrow>
     (scast (scast (a :: 'a::len word) :: 'b::len word) :: 'c::len word) = scast a"
  by (metis scast_eq sint_up_scast)

lemma ucast_scast_1:
  "\<lbrakk> is_down (scast :: 'a word \<Rightarrow> 'b word); is_down (ucast :: 'b word \<Rightarrow> 'c word) \<rbrakk> \<Longrightarrow>
            (ucast (scast (a :: 'a::len word) :: 'b::len word) :: 'c::len word) = scast a"
  by (metis scast_eq ucast_down_wi)

lemma ucast_scast_3:
  "\<lbrakk> is_down (scast :: 'a word \<Rightarrow> 'c word); is_down (ucast :: 'b word \<Rightarrow> 'c word) \<rbrakk> \<Longrightarrow>
     (ucast (scast (a :: 'a::len word) :: 'b::len word) :: 'c::len word) = scast a"
  by (metis scast_eq ucast_down_wi)

lemma ucast_scast_4:
  "\<lbrakk> is_up (scast :: 'a word \<Rightarrow> 'b word); is_down (ucast :: 'b word \<Rightarrow> 'c word) \<rbrakk> \<Longrightarrow>
     (ucast (scast (a :: 'a::len word) :: 'b::len word) :: 'c::len word) = scast a"
  by (metis down_cast_same scast_eq sint_up_scast)

lemma ucast_ucast_a:
  "\<lbrakk> is_down (ucast :: 'b word \<Rightarrow> 'c word) \<rbrakk> \<Longrightarrow>
        (ucast (ucast (a :: 'a::len word) :: 'b::len word) :: 'c::len word) = ucast a"
  by (metis down_cast_same ucast_eq ucast_down_wi)

lemma ucast_ucast_b:
  "\<lbrakk> is_up (ucast :: 'a word \<Rightarrow> 'b word) \<rbrakk> \<Longrightarrow>
     (ucast (ucast (a :: 'a::len word) :: 'b::len word) :: 'c::len word) = ucast a"
  by (metis ucast_up_ucast)

lemma scast_scast_a:
  "\<lbrakk> is_down (scast :: 'b word \<Rightarrow> 'c word) \<rbrakk> \<Longrightarrow>
            (scast (scast (a :: 'a::len word) :: 'b::len word) :: 'c::len word) = scast a"
  apply (simp only: scast_eq)
  apply (metis down_cast_same is_up_down scast_eq ucast_down_wi)
  done

lemma scast_down_wi [OF refl]:
  "uc = scast \<Longrightarrow> is_down uc \<Longrightarrow> uc (word_of_int x) = word_of_int x"
  by (metis down_cast_same is_up_down ucast_down_wi)

lemmas cast_simps =
  is_down is_up
  scast_down_add scast_down_minus scast_down_mult
  ucast_down_add ucast_down_minus ucast_down_mult
  scast_ucast_1 scast_ucast_3 scast_ucast_4
  ucast_scast_1 ucast_scast_3 ucast_scast_4
  ucast_ucast_a ucast_ucast_b
  scast_scast_a scast_scast_b
  ucast_down_wi scast_down_wi
  ucast_of_nat scast_of_nat
  uint_up_ucast sint_up_scast
  up_scast_surj up_ucast_surj

lemma smod_mod_positive:
    "\<lbrakk> 0 \<le> (a :: int); 0 \<le> b \<rbrakk> \<Longrightarrow> a smod b = a mod b"
  by (clarsimp simp: smod_int_alt_def zsgn_def)

lemma nat_mult_power_less_eq:
  "b > 0 \<Longrightarrow> (a * b ^ n < (b :: nat) ^ m) = (a < b ^ (m - n))"
  using mult_less_cancel2[where m = a and k = "b ^ n" and n="b ^ (m - n)"]
        mult_less_cancel2[where m="a * b ^ (n - m)" and k="b ^ m" and n=1]
  apply (simp only: power_add[symmetric] nat_minus_add_max)
  apply (simp only: power_add[symmetric] nat_minus_add_max ac_simps)
  apply (simp add: max_def split: if_split_asm)
  done

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

lemma sint_ucast_eq_uint:
    "\<lbrakk> \<not> is_down (ucast :: ('a::len word \<Rightarrow> 'b::len word)) \<rbrakk>
            \<Longrightarrow> sint ((ucast :: ('a::len word \<Rightarrow> 'b::len word)) x) = uint x"
  apply (subst sint_eq_uint)
   apply (simp add: msb_word_eq)
   apply transfer
   apply (simp add: bit_take_bit_iff)
  apply transfer
  apply simp
  done

lemma word_less_nowrapI':
  "(x :: 'a :: len word) \<le> z - k \<Longrightarrow> k \<le> z \<Longrightarrow> 0 < k \<Longrightarrow> x < x + k"
  by uint_arith

lemma mask_plus_1:
  "mask n + 1 = (2 ^ n :: 'a::len word)"
  by (clarsimp simp: mask_eq_decr_exp)

lemma unat_inj: "inj unat"
  by (metis eq_iff injI word_le_nat_alt)

lemma unat_ucast_upcast:
  "is_up (ucast :: 'b word \<Rightarrow> 'a word)
      \<Longrightarrow> unat (ucast x :: ('a::len) word) = unat (x :: ('b::len) word)"
  unfolding ucast_eq unat_eq_nat_uint
  apply (subst int_word_uint)
  apply (subst mod_pos_pos_trivial)
    apply simp
   apply (rule lt2p_lem)
   apply (clarsimp simp: is_up)
  apply simp
  done

lemma ucast_mono:
  "\<lbrakk> (x :: 'b :: len word) < y; y < 2 ^ LENGTH('a) \<rbrakk>
   \<Longrightarrow> ucast x < ((ucast y) :: 'a :: len word)"
  apply (simp only: flip: ucast_nat_def)
  apply (rule of_nat_mono_maybe)
  apply (rule unat_less_helper)
  apply (simp add: Power.of_nat_power)
  apply (simp add: word_less_nat_alt)
  done

lemma ucast_mono_le:
  "\<lbrakk>x \<le> y; y < 2 ^ LENGTH('b)\<rbrakk> \<Longrightarrow> (ucast (x :: 'a :: len word) :: 'b :: len word) \<le> ucast y"
  apply (simp only: flip: ucast_nat_def)
  apply (subst of_nat_mono_maybe_le[symmetric])
    apply (rule unat_less_helper)
    apply (simp add: Power.of_nat_power)
   apply (rule unat_less_helper)
   apply (erule le_less_trans)
   apply (simp add: Power.of_nat_power)
  apply (simp add: word_le_nat_alt)
  done

lemma ucast_mono_le':
  "\<lbrakk> unat y < 2 ^ LENGTH('b); LENGTH('b::len) < LENGTH('a::len); x \<le> y \<rbrakk>
   \<Longrightarrow> UCAST('a \<rightarrow> 'b) x \<le> UCAST('a \<rightarrow> 'b) y"
  by (auto simp: word_less_nat_alt intro: ucast_mono_le)

lemma zero_sle_ucast_up:
  "\<not> is_down (ucast :: 'a word \<Rightarrow> 'b signed word) \<Longrightarrow>
          (0 <=s ((ucast (b::('a::len) word)) :: ('b::len) signed word))"
  by transfer (simp add: bit_simps)

lemma word_le_ucast_sless:
  "\<lbrakk> x \<le> y; y \<noteq> -1; LENGTH('a) < LENGTH('b) \<rbrakk> \<Longrightarrow>
    UCAST (('a :: len) \<rightarrow> ('b :: len) signed) x <s ucast (y + 1)"
  by (clarsimp simp: word_le_make_less word_sless_alt sint_ucast_eq_uint is_down word_less_def)

lemma msb_ucast_eq:
    "LENGTH('a) = LENGTH('b) \<Longrightarrow>
         msb (ucast x :: ('a::len) word) = msb (x :: ('b::len) word)"
  by (simp add: msb_word_eq bit_simps)

lemma msb_big:
     "msb (a :: ('a::len) word) = (a \<ge> 2 ^ (LENGTH('a)  - Suc 0))"
  apply (rule iffI)
   apply (clarsimp simp: msb_nth)
   apply (drule bang_is_le)
   apply simp
  apply (rule ccontr)
  apply (subgoal_tac "a = a AND mask (LENGTH('a) - Suc 0)")
   apply (cut_tac and_mask_less' [where w=a and n="LENGTH('a) - Suc 0"])
    apply (clarsimp simp: word_not_le [symmetric])
   apply clarsimp
  apply (rule sym, subst and_mask_eq_iff_shiftr_0)
  apply (clarsimp simp: msb_shift)
  done

lemma zero_sle_ucast:
  "(0 <=s ((ucast (b::('a::len) word)) :: ('a::len) signed word))
                = (uint b < 2 ^ (LENGTH('a) - 1))"
  apply transfer
  apply (cases \<open>LENGTH('a)\<close>)
   apply (simp_all add: take_bit_Suc_from_most bit_simps)
  apply (simp_all add: bit_simps disjunctive_add)
  done

lemma aligned_shift:
  "\<lbrakk>x < 2 ^ n; is_aligned (y :: 'a :: len word) n;n \<le> LENGTH('a)\<rbrakk>
   \<Longrightarrow> x + y >> n = y >> n"
  apply (subst word_plus_and_or_coroll; rule bit_word_eqI)
   apply (auto simp add: bit_simps is_aligned_nth test_bit_eq_bit)
   apply (metis nth_bounded test_bit_eq_bit)
  apply (metis bit_imp_le_length le_add1 less_2p_is_upper_bits_unset test_bit_eq_bit)
  done

lemma aligned_shift':
  "\<lbrakk>x < 2 ^ n; is_aligned (y :: 'a :: len word) n;n \<le> LENGTH('a)\<rbrakk>
   \<Longrightarrow> y + x >> n = y >> n"
  apply (subst word_plus_and_or_coroll; rule bit_word_eqI)
   apply (auto simp add: bit_simps is_aligned_nth test_bit_eq_bit)
   apply (metis nth_bounded test_bit_eq_bit)
  apply (metis bit_imp_le_length le_add1 less_2p_is_upper_bits_unset test_bit_eq_bit)
  done

lemma neg_mask_add_mask:
  "((x:: 'a :: len word) AND NOT (mask n)) + (2 ^ n - 1) = x OR mask n"
  unfolding mask_2pm1 [symmetric]
  apply (subst word_plus_and_or_coroll; rule bit_word_eqI)
   apply (auto simp add: bit_simps)
  done

lemma and_neg_mask_plus_mask_mono: "(p AND NOT (mask n)) + mask n \<ge> p"
  for p :: \<open>'a::len word\<close>
  apply (rule word_le_minus_cancel[where x = "p AND NOT (mask n)"])
   apply (clarsimp simp: subtract_mask)
   using word_and_le1[where a = "mask n" and y = p]
   apply (clarsimp simp: mask_eq_decr_exp word_le_less_eq)
  apply (rule is_aligned_no_overflow'[folded mask_2pm1])
  apply (clarsimp simp: is_aligned_neg_mask)
  done

lemma word_neg_and_le:
  "ptr \<le> (ptr AND NOT (mask n)) + (2 ^ n - 1)"
  for ptr :: \<open>'a::len word\<close>
  by (simp add: and_neg_mask_plus_mask_mono mask_2pm1[symmetric])

lemma is_aligned_sub_helper:
  "\<lbrakk> is_aligned (p - d) n; d < 2 ^ n \<rbrakk>
     \<Longrightarrow> (p AND mask n = d) \<and> (p AND (NOT (mask n)) = p - d)"
  by (drule(1) is_aligned_add_helper, simp)

lemma is_aligned_after_mask:
  "\<lbrakk>is_aligned k m;m\<le> n\<rbrakk> \<Longrightarrow> is_aligned (k AND mask n) m"
  by (rule is_aligned_andI1)

lemma and_mask_plus:
  "\<lbrakk>is_aligned ptr m; m \<le> n; a < 2 ^ m\<rbrakk>
   \<Longrightarrow> ptr + a AND mask n = (ptr AND mask n) + a"
  apply (rule mask_eqI[where n = m])
   apply (simp add:mask_twice min_def)
    apply (simp add:is_aligned_add_helper)
    apply (subst is_aligned_add_helper[THEN conjunct1])
      apply (erule is_aligned_after_mask)
     apply simp
    apply simp
   apply simp
  apply (subgoal_tac "(ptr + a AND mask n) AND NOT (mask m)
     = (ptr + a AND NOT (mask m) ) AND mask n")
   apply (simp add:is_aligned_add_helper)
   apply (subst is_aligned_add_helper[THEN conjunct2])
     apply (simp add:is_aligned_after_mask)
    apply simp
   apply simp
  apply (simp add:word_bw_comms word_bw_lcs)
  done

lemma le_step_down_word:"\<lbrakk>(i::('a::len) word) \<le> n; i = n \<longrightarrow> P; i \<le> n - 1 \<longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by unat_arith

lemma le_step_down_word_2:
  fixes x :: "'a::len word"
  shows "\<lbrakk>x \<le>  y; x \<noteq> y\<rbrakk> \<Longrightarrow> x \<le> y - 1"
  by (subst (asm) word_le_less_eq,
      clarsimp,
      simp add: word_le_minus_one_leq)

lemma NOT_mask_AND_mask[simp]: "(w AND mask n) AND NOT (mask n) = 0"
  by (clarsimp simp add: mask_eq_decr_exp Parity.bit_eq_iff bit_and_iff bit_not_iff bit_mask_iff)

lemma and_and_not[simp]:"(a AND b) AND NOT b = 0"
  for a b :: \<open>'a::len word\<close>
  apply (subst word_bw_assocs(1))
  apply clarsimp
  done

lemma mask_shift_and_negate[simp]:"(w AND mask n << m) AND NOT (mask n << m) = 0"
  for w :: \<open>'a::len word\<close>
  by (clarsimp simp add: mask_eq_decr_exp Parity.bit_eq_iff bit_and_iff bit_not_iff shiftl_word_eq bit_push_bit_iff)

lemma le_step_down_nat:"\<lbrakk>(i::nat) \<le> n; i = n \<longrightarrow> P; i \<le> n - 1 \<longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by arith

lemma le_step_down_int:"\<lbrakk>(i::int) \<le> n; i = n \<longrightarrow> P; i \<le> n - 1 \<longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by arith

lemma ex_mask_1[simp]: "(\<exists>x. mask x = (1 :: 'a::len word))"
  apply (rule_tac x=1 in exI)
  apply (simp add:mask_eq_decr_exp)
  done

lemma not_switch:"NOT a = x \<Longrightarrow> a = NOT x"
  by auto

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

lemma bit_twiddle_min:
  "(y::'a::len word) XOR (((x::'a::len word) XOR y) AND (if x < y then -1 else 0)) = min x y"
  by (auto simp add: Parity.bit_eq_iff bit_xor_iff min_def)

lemma bit_twiddle_max:
  "(x::'a::len word) XOR (((x::'a::len word) XOR y) AND (if x < y then -1 else 0)) = max x y"
  by (auto simp add: Parity.bit_eq_iff bit_xor_iff max_def)

lemma swap_with_xor:
  "\<lbrakk>(x::'a::len word) = a XOR b; y = b XOR x; z = x XOR y\<rbrakk> \<Longrightarrow> z = b \<and> y = a"
  by (auto simp add: Parity.bit_eq_iff bit_xor_iff max_def)

lemma scast_nop1 [simp]:
  "((scast ((of_int x)::('a::len) word))::'a sword) = of_int x"
  apply (simp only: scast_eq)
  by (metis len_signed sint_sbintrunc' word_sint.Rep_inverse)

lemma scast_nop2 [simp]:
  "((scast ((of_int x)::('a::len) sword))::'a word) = of_int x"
  apply (simp only: scast_eq)
  by (metis len_signed sint_sbintrunc' word_sint.Rep_inverse)

lemmas scast_nop = scast_nop1 scast_nop2 scast_id

lemma le_mask_imp_and_mask:
  "(x::'a::len word) \<le> mask n \<Longrightarrow> x AND mask n = x"
  by (metis and_mask_eq_iff_le_mask)

lemma or_not_mask_nop:
  "((x::'a::len word) OR NOT (mask n)) AND mask n = x AND mask n"
  by (metis word_and_not word_ao_dist2 word_bw_comms(1) word_log_esimps(3))

lemma mask_subsume:
  "\<lbrakk>n \<le> m\<rbrakk> \<Longrightarrow> ((x::'a::len word) OR y AND mask n) AND NOT (mask m) = x AND NOT (mask m)"
  by (auto simp add: Parity.bit_eq_iff bit_not_iff bit_or_iff bit_and_iff bit_mask_iff)

lemma and_mask_0_iff_le_mask:
  fixes w :: "'a::len word"
  shows "(w AND NOT(mask n) = 0) = (w \<le> mask n)"
  by (simp add: mask_eq_0_eq_x le_mask_imp_and_mask and_mask_eq_iff_le_mask)

lemma mask_twice2:
  "n \<le> m \<Longrightarrow> ((x::'a::len word) AND mask m) AND mask n = x AND mask n"
  by (metis mask_twice min_def)

lemma uint_2_id:
  "LENGTH('a) \<ge> 2 \<Longrightarrow> uint (2::('a::len) word) = 2"
  by simp

lemma bintrunc_id:
  "\<lbrakk>m \<le> of_nat n; 0 < m\<rbrakk> \<Longrightarrow> bintrunc n m = m"
  by (simp add: bintrunc_mod2p le_less_trans)

lemma shiftr1_unfold: "shiftr1 x = x >> 1"
  by (metis One_nat_def comp_apply funpow.simps(1) funpow.simps(2) id_apply shiftr_def)

lemma shiftr1_is_div_2: "(x::('a::len) word) >> 1 = x div 2"
  by transfer (simp add: drop_bit_Suc)

lemma shiftl1_is_mult: "(x << 1) = (x :: 'a::len word) * 2"
  by (metis One_nat_def mult_2 mult_2_right one_add_one
        power_0 power_Suc shiftl_t2n)

lemma div_of_0_id[simp]:"(0::('a::len) word) div n = 0"
  by (simp add: word_div_def)

lemma degenerate_word:"LENGTH('a) = 1 \<Longrightarrow> (x::('a::len) word) = 0 \<or> x = 1"
  by (metis One_nat_def less_irrefl_nat sint_1_cases)

lemma div_by_0_word:"(x::('a::len) word) div 0 = 0"
  by (metis div_0 div_by_0 unat_0 word_arith_nat_defs(6) word_div_1)

lemma div_less_dividend_word:"\<lbrakk>x \<noteq> 0; n \<noteq> 1\<rbrakk> \<Longrightarrow> (x::('a::len) word) div n < x"
  apply (cases \<open>n = 0\<close>)
   apply clarsimp
   apply (simp add:word_neq_0_conv)
  apply (subst word_arith_nat_div)
  apply (rule word_of_nat_less)
  apply (rule div_less_dividend)
  using unat_eq_zero word_unat_Rep_inject1 apply force
  apply (simp add:unat_gt_0)
  done

lemma shiftr1_lt:"x \<noteq> 0 \<Longrightarrow> (x::('a::len) word) >> 1 < x"
  apply (subst shiftr1_is_div_2)
  apply (rule div_less_dividend_word)
   apply simp+
  done

lemma word_less_div:
  fixes x :: "('a::len) word"
    and y :: "('a::len) word"
  shows "x div y = 0 \<Longrightarrow> y = 0 \<or> x < y"
  apply (case_tac "y = 0", clarsimp+)
  by (metis One_nat_def Suc_le_mono le0 le_div_geq not_less unat_0 unat_div unat_gt_0 word_less_nat_alt zero_less_one)

lemma not_degenerate_imp_2_neq_0:"LENGTH('a) > 1 \<Longrightarrow> (2::('a::len) word) \<noteq> 0"
  by (metis numerals(1) power_not_zero power_zero_numeral)

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

lemma word_overflow:"(x::('a::len) word) + 1 > x \<or> x + 1 = 0"
  apply clarsimp
  by (metis diff_0 eq_diff_eq less_x_plus_1)

lemma word_overflow_unat:"unat ((x::('a::len) word) + 1) = unat x + 1 \<or> x + 1 = 0"
  by (metis Suc_eq_plus1 add.commute unatSuc)

lemma even_word_imp_odd_next:"even (unat (x::('a::len) word)) \<Longrightarrow> x + 1 = 0 \<or> odd (unat (x + 1))"
  apply (cut_tac x=x in word_overflow_unat)
  apply clarsimp
  done

lemma odd_word_imp_even_next:"odd (unat (x::('a::len) word)) \<Longrightarrow> x + 1 = 0 \<or> even (unat (x + 1))"
  apply (cut_tac x=x in word_overflow_unat)
  apply clarsimp
  done

lemma overflow_imp_lsb:"(x::('a::len) word) + 1 = 0 \<Longrightarrow> x !! 0"
  using even_plus_one_iff [of x] by (simp add: test_bit_word_eq)

lemma odd_iff_lsb:"odd (unat (x::('a::len) word)) = x !! 0"
  by transfer (simp add: even_nat_iff)

lemma of_nat_neq_iff_word:
      "x mod 2 ^ LENGTH('a) \<noteq> y mod 2 ^ LENGTH('a) \<Longrightarrow>
         (((of_nat x)::('a::len) word) \<noteq> of_nat y) = (x \<noteq> y)"
  apply (rule iffI)
   apply (case_tac "x = y")
   apply (subst (asm) of_nat_eq_iff[symmetric])
   apply simp+
  apply (case_tac "((of_nat x)::('a::len) word) = of_nat y")
   apply (subst (asm) word_unat.norm_eq_iff[symmetric])
   apply simp+
  done

lemma shiftr1_irrelevant_lsb:"(x::('a::len) word) !! 0 \<or> x >> 1 = (x + 1) >> 1"
  apply (cases \<open>LENGTH('a)\<close>; transfer)
   apply (simp_all add: take_bit_drop_bit)
  apply (simp add: drop_bit_take_bit drop_bit_Suc)
  done

lemma shiftr1_0_imp_only_lsb:"((x::('a::len) word) + 1) >> 1 = 0 \<Longrightarrow> x = 0 \<or> x + 1 = 0"
  by (metis One_nat_def shiftr1_0_or_1 word_less_1 word_overflow)

lemma shiftr1_irrelevant_lsb':"\<not>((x::('a::len) word) !! 0) \<Longrightarrow> x >> 1 = (x + 1) >> 1"
  by (metis shiftr1_irrelevant_lsb)

lemma lsb_this_or_next:"\<not>(((x::('a::len) word) + 1) !! 0) \<Longrightarrow> x !! 0"
  by (metis (poly_guards_query) even_word_imp_odd_next odd_iff_lsb overflow_imp_lsb)

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

lemma mask_or_not_mask:
  "x AND mask n OR x AND NOT (mask n) = x"
  for x :: \<open>'a::len word\<close>
  apply (subst word_oa_dist, simp)
  apply (subst word_oa_dist2, simp)
  done

lemma is_aligned_add_not_aligned:
  "\<lbrakk>is_aligned (p::'a::len word) n; \<not> is_aligned (q::'a::len word) n\<rbrakk> \<Longrightarrow> \<not> is_aligned (p + q) n"
  by (metis is_aligned_addD1)

lemma word_gr0_conv_Suc: "(m::'a::len word) > 0 \<Longrightarrow> \<exists>n. m = n + 1"
  by (metis add.commute add_minus_cancel)

lemma neg_mask_add_aligned:
  "\<lbrakk> is_aligned p n; q < 2 ^ n \<rbrakk> \<Longrightarrow> (p + q) AND NOT (mask n) = p AND NOT (mask n)"
  by (metis is_aligned_add_helper is_aligned_neg_mask_eq)

lemma word_sless_sint_le:"x <s y \<Longrightarrow> sint x \<le> sint y - 1"
  by (metis word_sless_alt zle_diff1_eq)


lemma upper_trivial:
  fixes x :: "'a::len word"
  shows "x \<noteq> 2 ^ LENGTH('a) - 1 \<Longrightarrow> x < 2 ^ LENGTH('a) - 1"
  by (simp add: less_le)

lemma constraint_expand:
  fixes x :: "'a::len word"
  shows "x \<in> {y. lower \<le> y \<and> y \<le> upper} = (lower \<le> x \<and> x \<le> upper)"
  by (rule mem_Collect_eq)

lemma card_map_elide:
  "card ((of_nat :: nat \<Rightarrow> 'a::len word) ` {0..<n}) = card {0..<n}"
    if "n \<le> CARD('a::len word)"
proof -
  let ?of_nat = "of_nat :: nat \<Rightarrow> 'a word"
  from word_unat.Abs_inj_on
  have "inj_on ?of_nat {i. i < CARD('a word)}"
    by (simp add: unats_def card_word)
  moreover have "{0..<n} \<subseteq> {i. i < CARD('a word)}"
    using that by auto
  ultimately have "inj_on ?of_nat {0..<n}"
    by (rule inj_on_subset)
  then show ?thesis
    by (simp add: card_image)
qed

lemma card_map_elide2:
  "n \<le> CARD('a::len word) \<Longrightarrow> card ((of_nat::nat \<Rightarrow> 'a::len word) ` {0..<n}) = n"
  by (subst card_map_elide) clarsimp+

lemma le_max_word_ucast_id:
  \<open>UCAST('b \<rightarrow> 'a) (UCAST('a \<rightarrow> 'b) x) = x\<close>
    if \<open>x \<le> UCAST('b::len \<rightarrow> 'a) (- 1)\<close>
    for x :: \<open>'a::len word\<close>
proof -
  from that have a1: \<open>x \<le> word_of_int (uint (word_of_int (2 ^ LENGTH('b) - 1) :: 'b word))\<close>
    by simp
  have f2: "((\<exists>i ia. (0::int) \<le> i \<and> \<not> 0 \<le> i + - 1 * ia \<and> i mod ia \<noteq> i) \<or>
            \<not> (0::int) \<le> - 1 + 2 ^ LENGTH('b) \<or> (0::int) \<le> - 1 + 2 ^ LENGTH('b) + - 1 * 2 ^ LENGTH('b) \<or>
            (- (1::int) + 2 ^ LENGTH('b)) mod 2 ^ LENGTH('b) =
              - 1 + 2 ^ LENGTH('b)) = ((\<exists>i ia. (0::int) \<le> i \<and> \<not> 0 \<le> i + - 1 * ia \<and> i mod ia \<noteq> i) \<or>
            \<not> (1::int) \<le> 2 ^ LENGTH('b) \<or>
            2 ^ LENGTH('b) + - (1::int) * ((- 1 + 2 ^ LENGTH('b)) mod 2 ^ LENGTH('b)) = 1)"
    by force
  have f3: "\<forall>i ia. \<not> (0::int) \<le> i \<or> 0 \<le> i + - 1 * ia \<or> i mod ia = i"
    using mod_pos_pos_trivial by force
  have "(1::int) \<le> 2 ^ LENGTH('b)"
    by simp
  then have "2 ^ LENGTH('b) + - (1::int) * ((- 1 + 2 ^ LENGTH('b)) mod 2 ^ len_of TYPE ('b)) = 1"
    using f3 f2 by blast
  then have f4: "- (1::int) + 2 ^ LENGTH('b) = (- 1 + 2 ^ LENGTH('b)) mod 2 ^ LENGTH('b)"
    by linarith
  have f5: "x \<le> word_of_int (uint (word_of_int (- 1 + 2 ^ LENGTH('b))::'b word))"
    using a1 by force
  have f6: "2 ^ LENGTH('b) + - (1::int) = - 1 + 2 ^ LENGTH('b)"
    by force
  have f7: "- (1::int) * 1 = - 1"
    by auto
  have "\<forall>x0 x1. (x1::int) - x0 = x1 + - 1 * x0"
    by force
  then have "x \<le> 2 ^ LENGTH('b) - 1"
    using f7 f6 f5 f4 by (metis uint_word_of_int wi_homs(2) word_arith_wis(8) word_of_int_2p)
  then have \<open>uint x \<le> uint (2 ^ LENGTH('b) - (1 :: 'a word))\<close>
    by (simp add: word_le_def)
  then have \<open>uint x \<le> 2 ^ LENGTH('b) - 1\<close>
    by (simp add: uint_word_ariths)
      (metis \<open>1 \<le> 2 ^ LENGTH('b)\<close> \<open>uint x \<le> uint (2 ^ LENGTH('b) - 1)\<close> linorder_not_less lt2p_lem uint_1 uint_minus_simple_alt uint_power_lower word_le_def zle_diff1_eq)
  then show ?thesis
    apply (simp add: word_ubin.eq_norm bintrunc_mod2p unsigned_ucast_eq)
    apply (metis \<open>x \<le> 2 ^ LENGTH('b) - 1\<close> and_mask_eq_iff_le_mask mask_eq_decr_exp take_bit_eq_mask)
    done
qed

lemma remdups_enum_upto:
  fixes s::"'a::len word"
  shows "remdups [s .e. e] = [s .e. e]"
  by simp

lemma card_enum_upto:
  fixes s::"'a::len word"
  shows "card (set [s .e. e]) = Suc (unat e) - unat s"
  by (subst List.card_set) (simp add: remdups_enum_upto)

lemma complement_nth_w2p:
  shows "n' < LENGTH('a) \<Longrightarrow> (NOT (2 ^ n :: 'a::len word)) !! n' = (n' \<noteq> n)"
  by (fastforce simp: word_ops_nth_size word_size nth_w2p)

lemma word_unat_and_lt:
  "unat x < n \<or> unat y < n \<Longrightarrow> unat (x AND y) < n"
  by (meson le_less_trans word_and_le1 word_and_le2 word_le_nat_alt)

lemma word_unat_mask_lt:
  "m \<le> size w \<Longrightarrow> unat ((w::'a::len word) AND mask m) < 2 ^ m"
  by (rule word_unat_and_lt) (simp add: unat_mask word_size)

lemma unat_shiftr_less_t2n:
  fixes x :: "'a :: len word"
  shows "unat x < 2 ^ (n + m) \<Longrightarrow> unat (x >> n) < 2 ^ m"
  by (simp add: shiftr_div_2n' power_add mult.commute td_gal_lt)

lemma le_or_mask:
  "w \<le> w' \<Longrightarrow> w OR mask x \<le> w' OR mask x"
  for w w' :: \<open>'a::len word\<close>
  by (metis neg_mask_add_mask add.commute le_word_or1 mask_2pm1 neg_mask_mono_le word_plus_mono_left)

lemma le_shiftr1':
  "\<lbrakk> shiftr1 u \<le> shiftr1 v ; shiftr1 u \<noteq> shiftr1 v \<rbrakk> \<Longrightarrow> u \<le> v"
  apply transfer
  apply simp
  done

lemma le_shiftr':
  "\<lbrakk> u >> n \<le> v >> n ; u >> n \<noteq> v >> n \<rbrakk> \<Longrightarrow> (u::'a::len word) \<le> v"
  apply (induct n; simp add: shiftr_def)
  apply (case_tac "(shiftr1 ^^ n) u = (shiftr1 ^^ n) v", simp)
  apply (fastforce dest: le_shiftr1')
  done

lemma word_add_no_overflow:"(x::'a::len word) < max_word \<Longrightarrow> x < x + 1"
  using less_x_plus_1 order_less_le by blast

lemma lt_plus_1_le_word:
  fixes x :: "'a::len word"
  assumes bound:"n < unat (maxBound::'a word)"
  shows "x < 1 + of_nat n = (x \<le> of_nat n)"
  by (metis add.commute bound max_word_max word_Suc_leq word_not_le word_of_nat_less)

lemma unat_ucast_up_simp:
  fixes x :: "'a::len word"
  assumes "LENGTH('a) \<le> LENGTH('b)"
  shows "unat (ucast x :: 'b::len word) = unat x"
  unfolding ucast_eq unat_eq_nat_uint
  apply (subst int_word_uint)
  apply (subst mod_pos_pos_trivial; simp?)
  apply (rule lt2p_lem)
  apply (simp add: assms)
  done

lemma unat_ucast_less_no_overflow:
  "\<lbrakk>n < 2 ^ LENGTH('a); unat f < n\<rbrakk> \<Longrightarrow> (f::('a::len) word) < of_nat n"
  by (erule (1)  order_le_less_trans[OF _ of_nat_mono_maybe,rotated]) simp

lemma unat_ucast_less_no_overflow_simp:
  "n < 2 ^ LENGTH('a) \<Longrightarrow> (unat f < n) = ((f::('a::len) word) < of_nat n)"
  using unat_less_helper unat_ucast_less_no_overflow by blast

lemma unat_ucast_no_overflow_le:
  assumes no_overflow: "unat b < (2 :: nat) ^ LENGTH('a)"
  and upward_cast: "LENGTH('a) < LENGTH('b)"
  shows "(ucast (f::'a::len word) < (b :: 'b :: len word)) = (unat f < unat b)"
proof -
  have LR: "ucast f < b \<Longrightarrow> unat f < unat b"
    apply (rule unat_less_helper)
    apply (simp add:ucast_nat_def)
    apply (rule_tac 'b1 = 'b in  ucast_less_ucast[OF order.strict_implies_order, THEN iffD1])
     apply (rule upward_cast)
    apply (simp add: ucast_ucast_mask less_mask_eq word_less_nat_alt
                     unat_power_lower[OF upward_cast] no_overflow)
    done
  have RL: "unat f < unat b \<Longrightarrow> ucast f < b"
  proof-
    assume ineq: "unat f < unat b"
    have "ucast (f::'a::len word) < ((ucast (ucast b ::'a::len word)) :: 'b :: len word)"
      apply (simp add: ucast_less_ucast[OF order.strict_implies_order] upward_cast)
      apply (simp only: flip: ucast_nat_def)
      apply (rule unat_ucast_less_no_overflow[OF no_overflow ineq])
      done
    then show ?thesis
      apply (rule order_less_le_trans)
      apply (simp add:ucast_ucast_mask word_and_le2)
      done
  qed
  then show ?thesis by (simp add:RL LR iffI)
qed

lemmas ucast_up_mono = ucast_less_ucast[THEN iffD2]

lemma minus_one_word:
  "(-1 :: 'a :: len word) = 2 ^ LENGTH('a) - 1"
  by simp

lemma mask_exceed:
  "n \<ge> LENGTH('a) \<Longrightarrow> (x::'a::len word) AND NOT (mask n) = 0"
  by (simp add: and_not_mask shiftr_eq_0)

lemma word_shift_by_2:
  "x * 4 = (x::'a::len word) << 2"
  by (simp add: shiftl_t2n)

lemma le_2p_upper_bits:
  "\<lbrakk> (p::'a::len word) \<le> 2^n - 1; n < LENGTH('a) \<rbrakk> \<Longrightarrow>
  \<forall>n'\<ge>n. n' < LENGTH('a) \<longrightarrow> \<not> p !! n'"
  by (subst upper_bits_unset_is_l2p; simp)

lemma le2p_bits_unset:
  "p \<le> 2 ^ n - 1 \<Longrightarrow> \<forall>n'\<ge>n. n' < LENGTH('a) \<longrightarrow> \<not> (p::'a::len word) !! n'"
  using upper_bits_unset_is_l2p [where p=p]
  by (cases "n < LENGTH('a)") auto

lemma ucast_less_shiftl_helper:
  "\<lbrakk> LENGTH('b) + 2 < LENGTH('a); 2 ^ (LENGTH('b) + 2) \<le> n\<rbrakk>
    \<Longrightarrow> (ucast (x :: 'b::len word) << 2) < (n :: 'a::len word)"
  apply (erule order_less_le_trans[rotated])
  using ucast_less[where x=x and 'a='a]
  apply (simp only: shiftl_t2n field_simps)
  apply (rule word_less_power_trans2; simp)
  done

lemma word_power_nonzero:
  "\<lbrakk> (x :: 'a::len word) < 2 ^ (LENGTH('a) - n); n < LENGTH('a); x \<noteq> 0 \<rbrakk>
  \<Longrightarrow> x * 2 ^ n \<noteq> 0"
  by (metis and_mask_eq_iff_shiftr_0 less_mask_eq p2_gt_0 semiring_normalization_rules(7)
            shiftl_shiftr_id shiftl_t2n)

lemma less_1_helper:
  "n \<le> m \<Longrightarrow> (n - 1 :: int) < m"
  by arith

lemma div_power_helper:
  "\<lbrakk> x \<le> y; y < LENGTH('a) \<rbrakk> \<Longrightarrow> (2 ^ y - 1) div (2 ^ x :: 'a::len word) = 2 ^ (y - x) - 1"
  apply (rule word_uint.Rep_eqD)
  apply (simp only: uint_word_ariths uint_div uint_power_lower)
  apply (subst mod_pos_pos_trivial, fastforce, fastforce)+
  apply (subst mod_pos_pos_trivial)
    apply (simp add: le_diff_eq uint_2p_alt)
   apply (rule less_1_helper)
   apply (rule power_increasing; simp)
  apply (subst mod_pos_pos_trivial)
    apply (simp add: uint_2p_alt)
   apply (rule less_1_helper)
   apply (rule power_increasing; simp)
  apply (subst int_div_sub_1; simp add: uint_2p_alt)
  apply (subst power_0[symmetric])
  apply (simp add: uint_2p_alt le_imp_power_dvd power_sub_int)
  done


lemma word_add_power_off:
  fixes a :: "'a :: len word"
  assumes ak: "a < k"
  and kw: "k < 2 ^ (LENGTH('a) - m)"
  and mw: "m < LENGTH('a)"
  and off: "off < 2 ^ m"
  shows "(a * 2 ^ m) + off < k * 2 ^ m"
proof (cases "m = 0")
  case True
  then show ?thesis using off ak by simp
next
  case False

  from ak have ak1: "a + 1 \<le> k" by (rule inc_le)
  then have "(a + 1) * 2 ^ m \<noteq> 0"
    apply -
    apply (rule word_power_nonzero)
    apply (erule order_le_less_trans  [OF _ kw])
    apply (rule mw)
    apply (rule less_is_non_zero_p1 [OF ak])
    done
  then have "(a * 2 ^ m) + off < ((a + 1) * 2 ^ m)" using kw mw
    apply -
    apply (simp add: distrib_right)
    apply (rule word_plus_strict_mono_right [OF off])
    apply (rule is_aligned_no_overflow'')
    apply (rule is_aligned_mult_triv2)
    apply assumption
    done
  also have "\<dots> \<le> k * 2 ^ m" using ak1 mw kw False
    apply -
    apply (erule word_mult_le_mono1)
    apply (simp add: p2_gt_0)
    apply (simp add: word_less_nat_alt)
    apply (rule nat_less_power_trans2[simplified])
    apply (simp add: word_less_nat_alt)
    apply simp
    done
  finally show ?thesis .
qed

lemma offset_not_aligned:
  "\<lbrakk> is_aligned (p::'a::len word) n; i > 0; i < 2 ^ n; n < LENGTH('a)\<rbrakk> \<Longrightarrow>
   \<not> is_aligned (p + of_nat i) n"
  apply (erule is_aligned_add_not_aligned)
  apply transfer
  apply (auto simp add: is_aligned_iff_udvd)
  apply (metis bintrunc_bintrunc_ge int_ops(1) nat_int_comparison(1) nat_less_le take_bit_eq_0_iff take_bit_nat_eq_self_iff take_bit_of_nat)
  done

lemma length_upto_enum_one:
  fixes x :: "'a :: len word"
  assumes lt1: "x < y" and lt2: "z < y" and lt3: "x \<le> z"
  shows "[x , y .e. z] = [x]"
  unfolding upto_enum_step_def
proof (subst upto_enum_red, subst if_not_P [OF leD [OF lt3]], clarsimp, rule conjI)
  show "unat ((z - x) div (y - x)) = 0"
  proof (subst unat_div, rule div_less)
    have syx: "unat (y - x) = unat y - unat x"
      by (rule unat_sub [OF order_less_imp_le]) fact
    moreover have "unat (z - x) = unat z - unat x"
      by (rule unat_sub) fact

    ultimately show "unat (z - x) < unat (y - x)"
      using lt2 lt3 unat_mono word_less_minus_mono_left by blast
  qed

  then show "(z - x) div (y - x) * (y - x) = 0"
    by (metis mult_zero_left unat_0 word_unat.Rep_eqD)
qed

lemma max_word_mask:
  "(max_word :: 'a::len word) = mask LENGTH('a)"
  unfolding mask_eq_decr_exp by simp

lemmas mask_len_max = max_word_mask[symmetric]

lemma mask_out_first_mask_some:
  "\<lbrakk> x AND NOT (mask n) = y; n \<le> m \<rbrakk> \<Longrightarrow> x AND NOT (mask m) = y AND NOT (mask m)"
  for x y :: \<open>'a::len word\<close>
  by (rule bit_word_eqI) (auto simp add: bit_simps)

lemma mask_lower_twice:
  "n \<le> m \<Longrightarrow> (x AND NOT (mask n)) AND NOT (mask m) = x AND NOT (mask m)"
  for x :: \<open>'a::len word\<close>
  by (rule bit_word_eqI) (auto simp add: bit_simps)

lemma mask_lower_twice2:
  "(a AND NOT (mask n)) AND NOT (mask m) = a AND NOT (mask (max n m))"
  for a :: \<open>'a::len word\<close>
  by (rule bit_word_eqI) (auto simp add: bit_simps)

lemma ucast_and_neg_mask:
  "ucast (x AND NOT (mask n)) = ucast x AND NOT (mask n)"
  apply (rule bit_word_eqI)
  apply (auto simp add: bit_simps dest: bit_imp_le_length)
  done

lemma ucast_and_mask:
  "ucast (x AND mask n) = ucast x AND mask n"
  apply (rule bit_word_eqI)
  apply (auto simp add: bit_simps dest: bit_imp_le_length)
  done

lemma ucast_mask_drop:
  "LENGTH('a :: len) \<le> n \<Longrightarrow> (ucast (x AND mask n) :: 'a word) = ucast x"
  apply (rule bit_word_eqI)
  apply (auto simp add: bit_simps dest: bit_imp_le_length)
  done

(* negating a mask which has been shifted to the very left *)
lemma NOT_mask_shifted_lenword:
  "NOT (mask len << (LENGTH('a) - len) ::'a::len word) = mask (LENGTH('a) - len)"
  by (rule bit_word_eqI)
    (auto simp add: shiftl_word_eq word_size bit_not_iff bit_push_bit_iff bit_mask_iff)

(* Comparisons between different word sizes. *)

lemma eq_ucast_ucast_eq:
  "LENGTH('b) \<le> LENGTH('a) \<Longrightarrow> x = ucast y \<Longrightarrow> ucast x = y"
  for x :: "'a::len word" and y :: "'b::len word"
  by (simp add: is_down ucast_ucast_a)

lemma le_ucast_ucast_le:
  "x \<le> ucast y \<Longrightarrow> ucast x \<le> y"
  for x :: "'a::len word" and y :: "'b::len word"
  by (smt le_unat_uoi linorder_not_less order_less_imp_le ucast_nat_def unat_arith_simps(1))

lemma less_ucast_ucast_less:
  "LENGTH('b) \<le> LENGTH('a) \<Longrightarrow> x < ucast y \<Longrightarrow> ucast x < y"
  for x :: "'a::len word" and y :: "'b::len word"
  by (metis ucast_nat_def unat_mono unat_ucast_up_simp word_of_nat_less)

lemma ucast_le_ucast:
  "LENGTH('a) \<le> LENGTH('b) \<Longrightarrow> (ucast x \<le> (ucast y::'b::len word)) = (x \<le> y)"
  for x :: "'a::len word"
  by (simp add: unat_arith_simps(1) unat_ucast_up_simp)

lemmas ucast_up_mono_le = ucast_le_ucast[THEN iffD2]

lemma ucast_le_ucast_eq:
  fixes x y :: "'a::len word"
  assumes x: "x < 2 ^ n"
  assumes y: "y < 2 ^ n"
  assumes n: "n = LENGTH('b::len)"
  shows "(UCAST('a \<rightarrow> 'b) x \<le> UCAST('a \<rightarrow> 'b) y) = (x \<le> y)"
  apply (rule iffI)
   apply (cases "LENGTH('b) < LENGTH('a)")
    apply (subst less_mask_eq[OF x, symmetric])
    apply (subst less_mask_eq[OF y, symmetric])
    apply (unfold n)
    apply (subst ucast_ucast_mask[symmetric])+
    apply (simp add: ucast_le_ucast)+
  apply (erule ucast_mono_le[OF _ y[unfolded n]])
  done

lemma ucast_or_distrib:
  fixes x :: "'a::len word"
  fixes y :: "'a::len word"
  shows "(ucast (x OR y) :: ('b::len) word) = ucast x OR ucast y"
  by transfer simp

lemma shiftr_less:
  "(w::'a::len word) < k \<Longrightarrow> w >> n < k"
  by (metis div_le_dividend le_less_trans shiftr_div_2n' unat_arith_simps(2))

lemma word_and_notzeroD:
  "w AND w' \<noteq> 0 \<Longrightarrow> w \<noteq> 0 \<and> w' \<noteq> 0"
  by auto

lemma word_exists_nth:
  "(w::'a::len word) \<noteq> 0 \<Longrightarrow> \<exists>i. w !! i"
  by (simp add: bit_eq_iff test_bit_word_eq)

lemma shiftr_le_0:
  "unat (w::'a::len word) < 2 ^ n \<Longrightarrow> w >> n = (0::'a::len word)"
  by (rule word_unat.Rep_eqD) (simp add: shiftr_div_2n')

lemma of_nat_shiftl:
  "(of_nat x << n) = (of_nat (x * 2 ^ n) :: ('a::len) word)"
proof -
  have "(of_nat x::'a word) << n = of_nat (2 ^ n) * of_nat x"
    using shiftl_t2n by (metis word_unat_power)
  thus ?thesis by simp
qed

lemma shiftl_1_not_0:
  "n < LENGTH('a) \<Longrightarrow> (1::'a::len word) << n \<noteq> 0"
  by (simp add: shiftl_t2n)

lemma max_word_not_0 [simp]:
  "- 1 \<noteq> (0 :: 'a::len word)"
  by simp

lemma ucast_zero_is_aligned:
  "UCAST('a::len \<rightarrow> 'b::len) w = 0 \<Longrightarrow> n \<le> LENGTH('b) \<Longrightarrow> is_aligned w n"
  by (clarsimp simp: is_aligned_mask word_eq_iff word_size nth_ucast)

lemma unat_ucast_eq_unat_and_mask:
  "unat (UCAST('b::len \<rightarrow> 'a::len) w) = unat (w AND mask LENGTH('a))"
  proof -
    have "unat (UCAST('b \<rightarrow> 'a) w) = unat (UCAST('a \<rightarrow> 'b) (UCAST('b \<rightarrow> 'a) w))"
      by (cases "LENGTH('a) < LENGTH('b)"; simp add: is_down ucast_ucast_a unat_ucast_up_simp)
    thus ?thesis using ucast_ucast_mask by simp
  qed

lemma unat_max_word_pos[simp]: "0 < unat (- 1 :: 'a::len word)"
  using unat_gt_0 [of \<open>- 1 :: 'a::len word\<close>] by simp


(* Miscellaneous conditional injectivity rules. *)

lemma mult_pow2_inj:
  assumes ws: "m + n \<le> LENGTH('a)"
  assumes le: "x \<le> mask m" "y \<le> mask m"
  assumes eq: "x * 2 ^ n = y * (2 ^ n::'a::len word)"
  shows "x = y"
proof (rule bit_word_eqI)
  fix q
  assume \<open>q < LENGTH('a)\<close>
  from eq have \<open>push_bit n x = push_bit n y\<close>
    by (simp add: push_bit_eq_mult)
  moreover from le have \<open>take_bit m x = x\<close> \<open>take_bit m y = y\<close>
    by (simp_all add: less_eq_mask_iff_take_bit_eq_self)
  ultimately have \<open>push_bit n (take_bit m x) = push_bit n (take_bit m y)\<close>
    by simp_all
  with \<open>q < LENGTH('a)\<close> ws show \<open>bit x q \<longleftrightarrow> bit y q\<close>
    apply (simp add: push_bit_take_bit)
    unfolding bit_eq_iff
    apply (simp add: bit_simps not_le)
    apply (metis (full_types) \<open>take_bit m x = x\<close> \<open>take_bit m y = y\<close> add.commute add_diff_cancel_right' add_less_cancel_right bit_take_bit_iff le_add2 less_le_trans)
    done
qed

lemma word_of_nat_inj:
  assumes bounded: "x < 2 ^ LENGTH('a)" "y < 2 ^ LENGTH('a)"
  assumes of_nats: "of_nat x = (of_nat y :: 'a::len word)"
  shows "x = y"
  by (rule contrapos_pp[OF of_nats]; cases "x < y"; cases "y < x")
     (auto dest: bounded[THEN of_nat_mono_maybe])

(* Uints *)

lemma uints_mono_iff: "uints l \<subseteq> uints m \<longleftrightarrow> l \<le> m"
  using power_increasing_iff[of "2::int" l m]
  apply (auto simp: uints_num subset_iff simp del: power_increasing_iff)
  by (meson less_irrefl not_less zle2p)

lemmas uints_monoI = uints_mono_iff[THEN iffD2]

lemma Bit_in_uints_Suc: "of_bool c + 2 * w \<in> uints (Suc m)" if "w \<in> uints m"
  using that
  by (auto simp: uints_num)

lemma Bit_in_uintsI: "of_bool c + 2 * w \<in> uints m" if "w \<in> uints (m - 1)" "m > 0"
  using Bit_in_uints_Suc[OF that(1)] that(2)
  by auto

lemma bin_cat_in_uintsI:
  \<open>bin_cat a n b \<in> uints m\<close> if \<open>a \<in> uints l\<close> \<open>m \<ge> l + n\<close>
proof -
  from \<open>m \<ge> l + n\<close> obtain q where \<open>m = l + n + q\<close>
    using le_Suc_ex by blast
  then have \<open>(2::int) ^ m = 2 ^ n * 2 ^ (l + q)\<close>
    by (simp add: ac_simps power_add)
  moreover have \<open>a mod 2 ^ (l + q) = a\<close>
    using \<open>a \<in> uints l\<close>
    by (auto simp add: uints_def take_bit_eq_mod power_add Divides.mod_mult2_eq)
  ultimately have \<open>concat_bit n b a = take_bit m (concat_bit n b a)\<close>
    by (simp add: concat_bit_eq take_bit_eq_mod push_bit_eq_mult Divides.mod_mult2_eq)
  then show ?thesis
    by (simp add: uints_def)
qed

lemma bin_cat_cong: "bin_cat a n b = bin_cat c m d"
  if "n = m" "a = c" "bintrunc m b = bintrunc m d"
  using that(3) unfolding that(1,2) by (simp add: bin_cat_eq_push_bit_add_take_bit)

lemma bin_cat_eqD1: "bin_cat a n b = bin_cat c n d \<Longrightarrow> a = c"
  by (metis drop_bit_bin_cat_eq)

lemma bin_cat_eqD2: "bin_cat a n b = bin_cat c n d \<Longrightarrow> bintrunc n b = bintrunc n d"
  by (metis take_bit_bin_cat_eq)
  
lemma bin_cat_inj: "(bin_cat a n b) = bin_cat c n d \<longleftrightarrow> a = c \<and> bintrunc n b = bintrunc n d"
  by (auto intro: bin_cat_cong bin_cat_eqD1 bin_cat_eqD2)

lemma word_of_int_bin_cat_eq_iff:
  "(word_of_int (bin_cat (uint a) LENGTH('b) (uint b))::'c::len word) =
  word_of_int (bin_cat (uint c) LENGTH('b) (uint d)) \<longleftrightarrow> b = d \<and> a = c"
  if "LENGTH('a) + LENGTH('b) \<le> LENGTH('c)"
  for a::"'a::len word" and b::"'b::len word"
  by (subst word_uint.Abs_inject)
     (auto simp: bin_cat_inj intro!: that bin_cat_in_uintsI)

lemma word_cat_inj: "(word_cat a b::'c::len word) = word_cat c d \<longleftrightarrow> a = c \<and> b = d"
  if "LENGTH('a) + LENGTH('b) \<le> LENGTH('c)"
  for a::"'a::len word" and b::"'b::len word"
  using word_of_int_bin_cat_eq_iff [OF that, of b a d c]
  by transfer auto

lemma p2_eq_1: "2 ^ n = (1::'a::len word) \<longleftrightarrow> n = 0"
proof -
  have "2 ^ n = (1::'a word) \<Longrightarrow> n = 0"
    by (metis One_nat_def not_less one_less_numeral_iff p2_eq_0 p2_gt_0 power_0 power_0
        power_inject_exp semiring_norm(76) unat_power_lower zero_neq_one)
  then show ?thesis by auto
qed

(* usually: x,y = (len_of TYPE ('a)) *)
lemma bitmagic_zeroLast_leq_or1Last:
  "(a::('a::len) word) AND (mask len << x - len) \<le> a OR mask (y - len)"
  by (meson le_word_or2 order_trans word_and_le2)


lemma zero_base_lsb_imp_set_eq_as_bit_operation:
  fixes base ::"'a::len word"
  assumes valid_prefix: "mask (LENGTH('a) - len) AND base = 0"
  shows "(base = NOT (mask (LENGTH('a) - len)) AND a) \<longleftrightarrow>
         (a \<in> {base .. base OR mask (LENGTH('a) - len)})"
proof
  have helper3: "x OR y = x OR y AND NOT x" for x y ::"'a::len word" by (simp add: word_oa_dist2)
  from assms show "base = NOT (mask (LENGTH('a) - len)) AND a \<Longrightarrow>
                    a \<in> {base..base OR mask (LENGTH('a) - len)}"
    apply(simp add: word_and_le1)
    apply(metis helper3 le_word_or2 word_bw_comms(1) word_bw_comms(2))
  done
next
  assume "a \<in> {base..base OR mask (LENGTH('a) - len)}"
  hence a: "base \<le> a \<and> a \<le> base OR mask (LENGTH('a) - len)" by simp
  show "base = NOT (mask (LENGTH('a) - len)) AND a"
  proof -
    have f2: "\<forall>x\<^sub>0. base AND NOT (mask x\<^sub>0) \<le> a AND NOT (mask x\<^sub>0)"
      using a neg_mask_mono_le by blast
    have f3: "\<forall>x\<^sub>0. a AND NOT (mask x\<^sub>0) \<le> (base OR mask (LENGTH('a) - len)) AND NOT (mask x\<^sub>0)"
      using a neg_mask_mono_le by blast
    have f4: "base = base AND NOT (mask (LENGTH('a) - len))"
      using valid_prefix by (metis mask_eq_0_eq_x word_bw_comms(1))
    hence f5: "\<forall>x\<^sub>6. (base OR x\<^sub>6) AND NOT (mask (LENGTH('a) - len)) =
                      base OR x\<^sub>6 AND NOT (mask (LENGTH('a) - len))"
      using word_ao_dist by (metis)
    have f6: "\<forall>x\<^sub>2 x\<^sub>3. a AND NOT (mask x\<^sub>2) \<le> x\<^sub>3 \<or>
                      \<not> (base OR mask (LENGTH('a) - len)) AND NOT (mask x\<^sub>2) \<le> x\<^sub>3"
      using f3 dual_order.trans by auto
    have "base = (base OR mask (LENGTH('a) - len)) AND NOT (mask (LENGTH('a) - len))"
      using f5 by auto
    hence "base = a AND NOT (mask (LENGTH('a) - len))"
      using f2 f4 f6 by (metis eq_iff)
    thus "base = NOT (mask (LENGTH('a) - len)) AND a"
      by (metis word_bw_comms(1))
  qed
qed

lemma of_nat_eq_signed_scast:
  "(of_nat x = (y :: ('a::len) signed word))
   = (of_nat x = (scast y :: 'a word))"
  by (metis scast_of_nat scast_scast_id(2))

lemma word_aligned_add_no_wrap_bounded:
  "\<lbrakk> w + 2^n \<le> x; w + 2^n \<noteq> 0; is_aligned w n \<rbrakk> \<Longrightarrow> (w::'a::len word) < x"
  by (blast dest: is_aligned_no_overflow le_less_trans word_leq_le_minus_one)

lemma mask_Suc:
  "mask (Suc n) = (2 :: 'a::len word) ^ n + mask n"
  by (simp add: mask_eq_decr_exp)

lemma mask_mono:
  "sz' \<le> sz \<Longrightarrow> mask sz' \<le> (mask sz :: 'a::len word)"
  by (simp add: le_mask_iff shiftr_mask_le)

lemma aligned_mask_disjoint:
  "\<lbrakk> is_aligned (a :: 'a :: len word) n; b \<le> mask n \<rbrakk> \<Longrightarrow> a AND b = 0"
  by (metis and_zero_eq is_aligned_mask le_mask_imp_and_mask word_bw_lcs(1))

lemma word_and_or_mask_aligned:
  "\<lbrakk> is_aligned a n; b \<le> mask n \<rbrakk> \<Longrightarrow> a + b = a OR b"
  by (simp add: aligned_mask_disjoint word_plus_and_or_coroll)

lemma word_and_or_mask_aligned2:
  \<open>is_aligned b n \<Longrightarrow> a \<le> mask n \<Longrightarrow> a + b = a OR b\<close>
  using word_and_or_mask_aligned [of b n a] by (simp add: ac_simps)
  
lemma is_aligned_ucastI:
  "is_aligned w n \<Longrightarrow> is_aligned (ucast w) n"
  apply transfer
  apply (auto simp add: min_def)
  apply (metis bintrunc_bintrunc_ge bintrunc_n_0 nat_less_le not_le take_bit_eq_0_iff)
  done

lemma ucast_le_maskI:
  "a \<le> mask n \<Longrightarrow> UCAST('a::len \<rightarrow> 'b::len) a \<le> mask n"
  by (metis and_mask_eq_iff_le_mask ucast_and_mask)

lemma ucast_add_mask_aligned:
  "\<lbrakk> a \<le> mask n; is_aligned b n \<rbrakk> \<Longrightarrow> UCAST ('a::len \<rightarrow> 'b::len) (a + b) = ucast a + ucast b"
  by (metis add.commute is_aligned_ucastI ucast_le_maskI ucast_or_distrib word_and_or_mask_aligned)

lemma ucast_shiftl:
  "LENGTH('b) \<le> LENGTH ('a) \<Longrightarrow> UCAST ('a::len \<rightarrow> 'b::len) x << n = ucast (x << n)"
  by word_eqI_solve

lemma ucast_leq_mask:
  "LENGTH('a) \<le> n \<Longrightarrow> ucast (x::'a::len word) \<le> mask n"
  apply (simp add: less_eq_mask_iff_take_bit_eq_self)
  apply transfer
  apply (simp add: ac_simps)
  done

lemma shiftl_inj:
  "\<lbrakk> x << n = y << n; x \<le> mask (LENGTH('a)-n); y \<le> mask (LENGTH('a)-n) \<rbrakk> \<Longrightarrow>
   x = (y :: 'a :: len word)"
  apply word_eqI
  apply (rename_tac n')
  apply (case_tac "LENGTH('a) - n \<le> n'", simp)
  by (metis add.commute add.right_neutral diff_add_inverse le_diff_conv linorder_not_less zero_order(1))

lemma distinct_word_add_ucast_shift_inj:
  "\<lbrakk> p + (UCAST('a::len \<rightarrow> 'b::len) off << n) = p' + (ucast off' << n);
     is_aligned p n'; is_aligned p' n'; n' = n + LENGTH('a); n' < LENGTH('b) \<rbrakk>
   \<Longrightarrow> p' = p \<and> off' = off"
  apply (simp add: word_and_or_mask_aligned le_mask_shiftl_le_mask[where n="LENGTH('a)"]
                   ucast_leq_mask)
  apply (simp add: is_aligned_nth)
  apply (rule conjI; word_eqI)
   apply (metis add.commute test_bit_conj_lt diff_add_inverse le_diff_conv nat_less_le)
  apply (rename_tac i)
  apply (erule_tac x="i+n" in allE)
  apply simp
  done

lemma word_upto_Nil:
  "y < x \<Longrightarrow> [x .e. y ::'a::len word] = []"
  by (simp add: upto_enum_red not_le word_less_nat_alt)

lemma word_enum_decomp_elem:
  assumes "[x .e. (y ::'a::len word)] = as @ a # bs"
  shows "x \<le> a \<and> a \<le> y"
proof -
  have "set as \<subseteq> set [x .e. y] \<and> a \<in> set [x .e. y]"
    using assms by (auto dest: arg_cong[where f=set])
  then show ?thesis by auto
qed

lemma max_word_not_less[simp]:
   "\<not> max_word < x"
  by (simp add: not_less)

lemma word_enum_prefix:
  "[x .e. (y ::'a::len word)] = as @ a # bs \<Longrightarrow> as = (if x < a then [x .e. a - 1] else [])"
  apply (induct as arbitrary: x; clarsimp)
   apply (case_tac "x < y")
    prefer 2
    apply (case_tac "x = y", simp)
    apply (simp add: not_less)
    apply (drule (1) dual_order.not_eq_order_implies_strict)
    apply (simp add: word_upto_Nil)
   apply (simp add: word_upto_Cons_eq)
  apply (case_tac "x < y")
   prefer 2
   apply (case_tac "x = y", simp)
   apply (simp add: not_less)
   apply (drule (1) dual_order.not_eq_order_implies_strict)
   apply (simp add: word_upto_Nil)
  apply (clarsimp simp: word_upto_Cons_eq)
  apply (frule word_enum_decomp_elem)
  apply clarsimp
  apply (rule conjI)
   prefer 2
   apply (subst word_Suc_le[symmetric]; clarsimp)
  apply (drule meta_spec)
  apply (drule (1) meta_mp)
  apply clarsimp
  apply (rule conjI; clarsimp)
  apply (subst (2) word_upto_Cons_eq)
   apply unat_arith
  apply simp
  done

lemma word_enum_decomp_set:
  "[x .e. (y ::'a::len word)] = as @ a # bs \<Longrightarrow> a \<notin> set as"
  by (metis distinct_append distinct_enum_upto' not_distinct_conv_prefix)

lemma word_enum_decomp:
  assumes "[x .e. (y ::'a::len word)] = as @ a # bs"
  shows "x \<le> a \<and> a \<le> y \<and> a \<notin> set as \<and> (\<forall>z \<in> set as. x \<le> z \<and> z \<le> y)"
proof -
  from assms
  have "set as \<subseteq> set [x .e. y] \<and> a \<in> set [x .e. y]"
    by (auto dest: arg_cong[where f=set])
  with word_enum_decomp_set[OF assms]
  show ?thesis by auto
qed

lemma of_nat_unat_le_mask_ucast:
  "\<lbrakk>of_nat (unat t) = w; t \<le> mask LENGTH('a)\<rbrakk> \<Longrightarrow> t = UCAST('a::len \<rightarrow> 'b::len) w"
  by (clarsimp simp: ucast_nat_def ucast_ucast_mask simp flip: and_mask_eq_iff_le_mask)

lemma less_diff_gt0:
  "a < b \<Longrightarrow> (0 :: 'a :: len word) < b - a"
  by unat_arith

lemma unat_plus_gt:
  "unat ((a :: 'a :: len word) + b) \<le> unat a + unat b"
  by (clarsimp simp: unat_plus_if_size)

lemma const_less:
  "\<lbrakk> (a :: 'a :: len word) - 1 < b; a \<noteq> b \<rbrakk> \<Longrightarrow> a < b"
  by (metis less_1_simp word_le_less_eq)

lemma add_mult_aligned_neg_mask:
  \<open>(x + y * m) AND NOT(mask n) = (x AND NOT(mask n)) + y * m\<close>
  if \<open>m AND (2 ^ n - 1) = 0\<close>
  for x y m :: \<open>'a::len word\<close>
  by (metis (no_types, hide_lams)
    add.assoc add.commute add.right_neutral add_uminus_conv_diff
   mask_eq_decr_exp mask_eqs(2) mask_eqs(6) mult.commute mult_zero_left
   subtract_mask(1) that)

lemma unat_of_nat_minus_1:
  "\<lbrakk> n < 2 ^ LENGTH('a); n \<noteq> 0 \<rbrakk> \<Longrightarrow> unat ((of_nat n:: 'a :: len word) - 1) = n - 1"
  by (simp add: of_nat_diff unat_eq_of_nat)

lemma word_eq_zeroI:
  "a \<le> a - 1 \<Longrightarrow> a = 0" for a :: "'a :: len word"
  by (simp add: word_must_wrap)

lemma word_add_format:
  "(-1 :: 'a :: len  word) + b + c = b + (c - 1)"
  by simp

lemma upto_enum_word_nth:
  "\<lbrakk> i \<le> j; k \<le> unat (j - i) \<rbrakk> \<Longrightarrow> [i .e. j] ! k = i + of_nat k"
  apply (clarsimp simp: upto_enum_def nth_append)
  apply (clarsimp simp: word_le_nat_alt[symmetric])
  apply (rule conjI, clarsimp)
   apply (subst toEnum_of_nat, unat_arith)
   apply unat_arith
  apply (clarsimp simp: not_less unat_sub[symmetric])
  apply unat_arith
  done

lemma upto_enum_step_nth:
  "\<lbrakk> a \<le> c; n \<le> unat ((c - a) div (b - a)) \<rbrakk>
   \<Longrightarrow> [a, b .e. c] ! n = a + of_nat n * (b - a)"
  by (clarsimp simp: upto_enum_step_def not_less[symmetric] upto_enum_word_nth)

lemma upto_enum_inc_1_len:
  "a < - 1 \<Longrightarrow> [(0 :: 'a :: len word) .e. 1 + a] = [0 .e. a] @ [1 + a]"
  apply (simp add: upto_enum_word)
  apply (subgoal_tac "unat (1+a) = 1 + unat a")
   apply simp
  apply (subst unat_plus_simple[THEN iffD1])
   apply (metis add.commute no_plus_overflow_neg olen_add_eqv)
  apply unat_arith
  done

lemma neg_mask_add:
  "y AND mask n = 0 \<Longrightarrow> x + y AND NOT(mask n) = (x AND NOT(mask n)) + y"
  for x y :: \<open>'a::len word\<close>
  by (clarsimp simp: mask_out_sub_mask mask_eqs(7)[symmetric] mask_twice)

lemma shiftr_shiftl_shiftr[simp]:
  "(x :: 'a :: len word)  >> a << a >> a = x >> a"
  by word_eqI_solve

lemma add_right_shift:
  "\<lbrakk> x AND mask n = 0; y AND mask n = 0; x \<le> x + y \<rbrakk>
   \<Longrightarrow> (x + y :: ('a :: len) word) >> n = (x >> n) + (y >> n)"
  apply (simp add: no_olen_add_nat is_aligned_mask[symmetric])
  apply (simp add: unat_arith_simps shiftr_div_2n' split del: if_split)
  apply (subst if_P)
   apply (erule order_le_less_trans[rotated])
   apply (simp add: add_mono)
  apply (simp add: shiftr_div_2n' is_aligned_iff_dvd_nat)
  done

lemma sub_right_shift:
  "\<lbrakk> x AND mask n = 0; y AND mask n = 0; y \<le> x \<rbrakk>
   \<Longrightarrow> (x - y) >> n = (x >> n :: 'a :: len word) - (y >> n)"
  using add_right_shift[where x="x - y" and y=y and n=n]
  by (simp add: aligned_sub_aligned is_aligned_mask[symmetric] word_sub_le)

lemma and_and_mask_simple:
  "y AND mask n = mask n \<Longrightarrow> (x AND y) AND mask n = x AND mask n"
  by (simp add: ac_simps)

lemma and_and_mask_simple_not:
  "y AND mask n = 0 \<Longrightarrow> (x AND y) AND mask n = 0"
  by (simp add: ac_simps)

lemma word_and_le':
  "b \<le> c \<Longrightarrow> (a :: 'a :: len word) AND b \<le> c"
  by (metis word_and_le1 order_trans)

lemma word_and_less':
  "b < c \<Longrightarrow> (a :: 'a :: len word) AND b < c"
  by transfer simp

lemma shiftr_w2p:
  "x < LENGTH('a) \<Longrightarrow> 2 ^ x = (2 ^ (LENGTH('a) - 1) >> (LENGTH('a) - 1 - x) :: 'a :: len word)"
  by word_eqI_solve

lemma t2p_shiftr:
  "\<lbrakk> b \<le> a; a < LENGTH('a) \<rbrakk> \<Longrightarrow> (2 :: 'a :: len word) ^ a >> b = 2 ^ (a - b)"
  by word_eqI_solve

lemma scast_1[simp]:
  "scast (1 :: 'a :: len signed word) = (1 :: 'a word)"
  by simp

lemma ucast_ucast_mask_eq:
  "\<lbrakk> UCAST('a::len \<rightarrow> 'b::len) x = y; x AND mask LENGTH('b) = x \<rbrakk> \<Longrightarrow> x = ucast y"
  by word_eqI_solve

lemma ucast_up_eq:
  "\<lbrakk> ucast x = (ucast y::'b::len word); LENGTH('a) \<le> LENGTH ('b) \<rbrakk>
   \<Longrightarrow> ucast x = (ucast y::'a::len word)"
  by word_eqI_solve

lemma ucast_up_neq:
  "\<lbrakk> ucast x \<noteq> (ucast y::'b::len word); LENGTH('b) \<le> LENGTH ('a) \<rbrakk>
   \<Longrightarrow> ucast x \<noteq> (ucast y::'a::len word)"
  by (fastforce dest: ucast_up_eq)

lemma mask_AND_less_0:
  "\<lbrakk> x AND mask n = 0; m \<le> n \<rbrakk> \<Longrightarrow> x AND mask m = 0"
  for x :: \<open>'a::len word\<close>
  by (metis mask_twice2 word_and_notzeroD)

lemma mask_len_id [simp]:
  "(x :: 'a :: len word) AND mask LENGTH('a) = x"
  using uint_lt2p [of x] by (simp add: mask_eq_iff)

lemma scast_ucast_down_same:
  "LENGTH('b) \<le> LENGTH('a) \<Longrightarrow> SCAST('a \<rightarrow> 'b) = UCAST('a::len \<rightarrow> 'b::len)"
  by (simp add: down_cast_same is_down)

lemma word_aligned_0_sum:
  "\<lbrakk> a + b = 0; is_aligned (a :: 'a :: len word) n; b \<le> mask n; n < LENGTH('a) \<rbrakk>
   \<Longrightarrow> a = 0 \<and> b = 0"
  by (simp add: word_plus_and_or_coroll aligned_mask_disjoint word_or_zero)

lemma mask_eq1_nochoice:
  "\<lbrakk> LENGTH('a) > 1; (x :: 'a :: len word) AND 1 = x \<rbrakk> \<Longrightarrow> x = 0 \<or> x = 1"
  by (metis word_and_1)

lemma shiftr_and_eq_shiftl:
  "(w >> n) AND x = y \<Longrightarrow> w AND (x << n) = (y << n)" for y :: "'a:: len word"
  by (metis (no_types, lifting) and_not_mask bit.conj_ac(1) bit.conj_ac(2) mask_eq_0_eq_x shiftl_mask_is_0 shiftl_over_and_dist)

lemma add_mask_lower_bits':
  "\<lbrakk> len = LENGTH('a); is_aligned (x :: 'a :: len word) n;
     \<forall>n' \<ge> n. n' < len \<longrightarrow> \<not> p !! n' \<rbrakk>
   \<Longrightarrow> x + p AND NOT(mask n) = x"
  using add_mask_lower_bits by auto

lemma leq_mask_shift:
  "(x :: 'a :: len word) \<le> mask (low_bits + high_bits) \<Longrightarrow> (x >> low_bits) \<le> mask high_bits"
  by (simp add: le_mask_iff shiftr_shiftr)

lemma ucast_ucast_eq_mask_shift:
  "(x :: 'a :: len word) \<le> mask (low_bits + LENGTH('b))
   \<Longrightarrow> ucast((ucast (x >> low_bits)) :: 'b :: len word) = x >> low_bits"
  by (meson and_mask_eq_iff_le_mask eq_ucast_ucast_eq not_le_imp_less shiftr_less_t2n'
            ucast_ucast_len)

lemma const_le_unat:
  "\<lbrakk> b < 2 ^ LENGTH('a); of_nat b \<le> a \<rbrakk> \<Longrightarrow> b \<le> unat (a :: 'a :: len word)"
  apply (simp add: word_le_def)
  apply (simp only: uint_nat zle_int)
  apply transfer
  apply (simp add: take_bit_nat_eq_self)
  done

lemma upt_enum_offset_trivial:
  "\<lbrakk> x < 2 ^ LENGTH('a) - 1 ; n \<le> unat x \<rbrakk>
   \<Longrightarrow> ([(0 :: 'a :: len word) .e. x] ! n) = of_nat n"
  apply (induct x arbitrary: n)
    apply simp
  by (simp add: upto_enum_word_nth)

lemma word_le_mask_out_plus_2sz:
  "x \<le> (x AND NOT(mask sz)) + 2 ^ sz - 1"
  for x :: \<open>'a::len word\<close>
  by (metis add_diff_eq word_neg_and_le)

lemma ucast_add:
  "ucast (a + (b :: 'a :: len word)) = ucast a + (ucast b :: ('a signed word))"
  by transfer (simp add: take_bit_add)

lemma ucast_minus:
  "ucast (a - (b :: 'a :: len word)) = ucast a - (ucast b :: ('a signed word))"
  apply (insert ucast_add[where a=a and b="-b"])
  apply (metis (no_types, hide_lams) add_diff_eq diff_add_cancel ucast_add)
  done

lemma scast_ucast_add_one [simp]:
  "scast (ucast (x :: 'a::len word) + (1 :: 'a signed word)) = x + 1"
  apply (subst ucast_1[symmetric])
  apply (subst ucast_add[symmetric])
  apply clarsimp
  done

lemma word_and_le_plus_one:
  "a > 0 \<Longrightarrow> (x :: 'a :: len word) AND (a - 1) < a"
  by (simp add: gt0_iff_gem1 word_and_less')

lemma unat_of_ucast_then_shift_eq_unat_of_shift[simp]:
  "LENGTH('b) \<ge> LENGTH('a)
   \<Longrightarrow> unat ((ucast (x :: 'a :: len word) :: 'b :: len word) >> n) = unat (x >> n)"
  by (simp add: shiftr_div_2n' unat_ucast_up_simp)

lemma unat_of_ucast_then_mask_eq_unat_of_mask[simp]:
  "LENGTH('b) \<ge> LENGTH('a)
   \<Longrightarrow> unat ((ucast (x :: 'a :: len word) :: 'b :: len word) AND mask m) = unat (x AND mask m)"
  by (metis ucast_and_mask unat_ucast_up_simp)

lemma shiftr_less_t2n3:
  "\<lbrakk> (2 :: 'a word) ^ (n + m) = 0; m < LENGTH('a) \<rbrakk>
   \<Longrightarrow> (x :: 'a :: len word) >> n < 2 ^ m"
  by (fastforce intro: shiftr_less_t2n' simp: mask_eq_decr_exp power_overflow)

lemma unat_shiftr_le_bound:
  "\<lbrakk> 2 ^ (LENGTH('a :: len) - n) - 1 \<le> bnd; 0 < n \<rbrakk>
   \<Longrightarrow> unat ((x :: 'a word) >> n) \<le> bnd"
  using less_not_refl3 le_step_down_nat le_trans less_or_eq_imp_le word_shiftr_lt
  by (metis (no_types, lifting))

lemma shiftr_eqD:
  "\<lbrakk> x >> n = y >> n; is_aligned x n; is_aligned y n \<rbrakk>
   \<Longrightarrow> x = y"
  by (metis is_aligned_shiftr_shiftl)

lemma word_shiftr_shiftl_shiftr_eq_shiftr:
  "a \<ge> b \<Longrightarrow> (x :: 'a :: len word) >> a << b >> b = x >> a"
  by (simp add: mask_shift multi_shift_simps(5) shiftr_shiftr)

lemma of_int_uint_ucast:
   "of_int (uint (x :: 'a::len word)) = (ucast x :: 'b::len word)"
  by (fact Word.of_int_uint)

lemma mod_mask_drop:
  "\<lbrakk> m = 2 ^ n; 0 < m; mask n AND msk = mask n \<rbrakk>
   \<Longrightarrow> (x mod m) AND msk = x mod m"
  for x :: \<open>'a::len word\<close>
  by (simp add: word_mod_2p_is_mask word_bw_assocs)

lemma mask_eq_ucast_eq:
  "\<lbrakk> x AND mask LENGTH('a) = (x :: ('c :: len word));
     LENGTH('a) \<le> LENGTH('b)\<rbrakk>
    \<Longrightarrow> ucast (ucast x :: ('a :: len word)) = (ucast x :: ('b :: len word))"
  by (metis ucast_and_mask ucast_id ucast_ucast_mask ucast_up_eq)

lemma of_nat_less_t2n:
  "of_nat i < (2 :: ('a :: len) word) ^ n \<Longrightarrow> n < LENGTH('a) \<and> unat (of_nat i :: 'a word) < 2 ^ n"
  by (metis order_less_trans p2_gt_0 unat_less_power word_neq_0_conv)

lemma two_power_increasing_less_1:
  "\<lbrakk> n \<le> m; m \<le> LENGTH('a) \<rbrakk> \<Longrightarrow> (2 :: 'a :: len word) ^ n - 1 \<le> 2 ^ m - 1"
  by (metis diff_diff_cancel le_m1_iff_lt less_imp_diff_less p2_gt_0 two_power_increasing
            word_1_le_power word_le_minus_mono_left word_less_sub_1)

lemma word_sub_mono4:
  "\<lbrakk> y + x \<le> z + x; y \<le> y + x; z \<le> z + x \<rbrakk> \<Longrightarrow> y \<le> z" for y :: "'a :: len word"
  by (simp add: word_add_le_iff2)

lemma eq_or_less_helperD:
  "\<lbrakk> n = unat (2 ^ m - 1 :: 'a :: len word) \<or> n < unat (2 ^ m - 1 :: 'a word); m < LENGTH('a) \<rbrakk>
   \<Longrightarrow> n < 2 ^ m"
  by (meson le_less_trans nat_less_le unat_less_power word_power_less_1)

lemma mask_sub:
  "n \<le> m \<Longrightarrow> mask m - mask n = mask m AND NOT(mask n :: 'a::len word)"
  by (metis (full_types) and_mask_eq_iff_shiftr_0 mask_out_sub_mask shiftr_mask_le word_bw_comms(1))

lemma neg_mask_diff_bound:
  "sz'\<le> sz \<Longrightarrow> (ptr AND NOT(mask sz')) - (ptr AND NOT(mask sz)) \<le> 2 ^ sz - 2 ^ sz'"
  (is "_ \<Longrightarrow> ?lhs \<le> ?rhs")
  for ptr :: \<open>'a::len word\<close>
proof -
  assume lt: "sz' \<le> sz"
  hence "?lhs = ptr AND (mask sz AND NOT(mask sz'))"
    by (metis add_diff_cancel_left' multiple_mask_trivia)
  also have "\<dots> \<le> ?rhs" using lt
    by (metis (mono_tags) add_diff_eq diff_eq_eq eq_iff mask_2pm1 mask_sub word_and_le')
  finally show ?thesis by simp
qed

lemma mask_out_eq_0:
  "\<lbrakk> idx < 2 ^ sz; sz < LENGTH('a) \<rbrakk> \<Longrightarrow> (of_nat idx :: 'a :: len word) AND NOT(mask sz) = 0"
  by (simp add: Word_Lemmas.of_nat_power less_mask_eq mask_eq_0_eq_x)

lemma is_aligned_neg_mask_eq':
  "is_aligned ptr sz = (ptr AND NOT(mask sz) = ptr)"
  using is_aligned_mask mask_eq_0_eq_x by blast

lemma neg_mask_mask_unat:
  "sz < LENGTH('a)
   \<Longrightarrow> unat ((ptr :: 'a :: len word) AND NOT(mask sz)) + unat (ptr AND mask sz) = unat ptr"
  by (metis AND_NOT_mask_plus_AND_mask_eq unat_plus_simple word_and_le2)

lemma unat_pow_le_intro:
  "LENGTH('a) \<le> n \<Longrightarrow> unat (x :: 'a :: len word) < 2 ^ n"
  by (metis lt2p_lem not_le of_nat_le_iff of_nat_numeral semiring_1_class.of_nat_power uint_nat)

lemma unat_shiftl_less_t2n:
  "\<lbrakk> unat (x :: 'a :: len word) < 2 ^ (m - n); m < LENGTH('a) \<rbrakk> \<Longrightarrow> unat (x << n) < 2 ^ m"
  by (metis (no_types) Word_Lemmas.of_nat_power diff_le_self le_less_trans shiftl_less_t2n
                       unat_less_power word_unat.Rep_inverse)

lemma unat_is_aligned_add:
  "\<lbrakk> is_aligned p n; unat d < 2 ^ n \<rbrakk>
   \<Longrightarrow> unat (p + d AND mask n) = unat d \<and> unat (p + d AND NOT(mask n)) = unat p"
  by (metis add.right_neutral and_mask_eq_iff_le_mask and_not_mask le_mask_iff mask_add_aligned
            mask_out_add_aligned mult_zero_right shiftl_t2n shiftr_le_0)

lemma unat_shiftr_shiftl_mask_zero:
  "\<lbrakk> c + a \<ge> LENGTH('a) + b ; c < LENGTH('a) \<rbrakk>
   \<Longrightarrow> unat (((q :: 'a :: len word) >> a << b) AND NOT(mask c)) = 0"
  by (fastforce intro: unat_is_aligned_add[where p=0 and n=c, simplified, THEN conjunct2]
                       unat_shiftl_less_t2n unat_shiftr_less_t2n unat_pow_le_intro)

lemmas of_nat_ucast = ucast_of_nat[symmetric]

lemma shift_then_mask_eq_shift_low_bits:
  "x \<le> mask (low_bits + high_bits) \<Longrightarrow> (x >> low_bits) AND mask high_bits = x >> low_bits"
  for x :: \<open>'a::len word\<close>
  by (simp add: leq_mask_shift le_mask_imp_and_mask)

lemma leq_low_bits_iff_zero:
  "\<lbrakk> x \<le> mask (low bits + high bits); x >> low_bits = 0 \<rbrakk> \<Longrightarrow> (x AND mask low_bits = 0) = (x = 0)"
  for x :: \<open>'a::len word\<close>
  using and_mask_eq_iff_shiftr_0 by force

lemma unat_less_iff:
  "\<lbrakk> unat (a :: 'a :: len word) = b; c < 2 ^ LENGTH('a) \<rbrakk> \<Longrightarrow> (a < of_nat c) = (b < c)"
  using unat_ucast_less_no_overflow_simp by blast

lemma is_aligned_no_overflow3:
 "\<lbrakk> is_aligned (a :: 'a :: len word) n; n < LENGTH('a); b < 2 ^ n; c \<le> 2 ^ n; b < c \<rbrakk>
  \<Longrightarrow> a + b \<le> a + (c - 1)"
  by (meson is_aligned_no_wrap' le_m1_iff_lt not_le word_less_sub_1 word_plus_mono_right)

lemma mask_add_aligned_right:
  "is_aligned p n \<Longrightarrow> (q + p) AND mask n = q AND mask n"
  by (simp add: mask_add_aligned add.commute)

lemma leq_high_bits_shiftr_low_bits_leq_bits_mask:
  "x \<le> mask high_bits \<Longrightarrow> (x :: 'a :: len word) << low_bits \<le> mask (low_bits + high_bits)"
  by (metis le_mask_shiftl_le_mask)

lemma word_two_power_neg_ineq:
  "2 ^ m \<noteq> (0 :: 'a word) \<Longrightarrow> 2 ^ n \<le> - (2 ^ m :: 'a :: len word)"
  apply (cases "n < LENGTH('a)"; simp add: power_overflow)
  apply (cases "m < LENGTH('a)"; simp add: power_overflow)
  apply (simp add: word_le_nat_alt unat_minus word_size)
  apply (cases "LENGTH('a)"; simp)
  apply (simp add: less_Suc_eq_le)
  apply (drule power_increasing[where a=2 and n=n] power_increasing[where a=2 and n=m], simp)+
  apply (drule(1) add_le_mono)
  apply simp
  done

lemma unat_shiftl_absorb:
  "\<lbrakk> x \<le> 2 ^ p; p + k < LENGTH('a) \<rbrakk> \<Longrightarrow> unat (x :: 'a :: len word) * 2 ^ k = unat (x * 2 ^ k)"
  by (smt add_diff_cancel_right' add_lessD1 le_add2 le_less_trans mult.commute nat_le_power_trans
          unat_lt2p unat_mult_lem unat_power_lower word_le_nat_alt)

lemma word_plus_mono_right_split:
  "\<lbrakk> unat ((x :: 'a :: len word) AND mask sz) + unat z < 2 ^ sz; sz < LENGTH('a) \<rbrakk>
   \<Longrightarrow> x \<le> x + z"
  apply (subgoal_tac "(x AND NOT(mask sz)) + (x AND mask sz) \<le> (x AND NOT(mask sz)) + ((x AND mask sz) + z)")
   apply (simp add:word_plus_and_or_coroll2 field_simps)
  apply (rule word_plus_mono_right)
   apply (simp add: less_le_trans no_olen_add_nat)
  using Word_Lemmas.of_nat_power is_aligned_no_wrap' by force

lemma mul_not_mask_eq_neg_shiftl:
  "NOT(mask n :: 'a::len word) = -1 << n"
  by (simp add: NOT_mask shiftl_t2n)

lemma shiftr_mul_not_mask_eq_and_not_mask:
  "(x >> n) * NOT(mask n) = - (x AND NOT(mask n))"
  for x :: \<open>'a::len word\<close>
  by (metis NOT_mask and_not_mask mult_minus_left semiring_normalization_rules(7) shiftl_t2n)

lemma mask_eq_n1_shiftr:
  "n \<le> LENGTH('a) \<Longrightarrow> (mask n :: 'a :: len word) = -1 >> (LENGTH('a) - n)"
  by (metis diff_diff_cancel eq_refl mask_full shiftr_mask2)

lemma is_aligned_mask_out_add_eq:
  "is_aligned p n \<Longrightarrow> (p + x) AND NOT(mask n) = p + (x AND NOT(mask n))"
  by (simp add: mask_out_sub_mask mask_add_aligned)

lemmas is_aligned_mask_out_add_eq_sub
    = is_aligned_mask_out_add_eq[where x="a - b" for a b, simplified field_simps]

lemma aligned_bump_down:
  "is_aligned x n \<Longrightarrow> (x - 1) AND NOT(mask n) = x - 2 ^ n"
  by (drule is_aligned_mask_out_add_eq[where x="-1"]) (simp add: NOT_mask)

lemma unat_2tp_if:
  "unat (2 ^ n :: ('a :: len) word) = (if n < LENGTH ('a) then 2 ^ n else 0)"
  by (split if_split, simp_all add: power_overflow)

lemma mask_of_mask:
  "mask (n::nat) AND mask (m::nat) = (mask (min m n) :: 'a::len word)"
  by word_eqI_solve

lemma unat_signed_ucast_less_ucast:
  "LENGTH('a) \<le> LENGTH('b) \<Longrightarrow> unat (ucast (x :: 'a :: len word) :: 'b :: len signed word) = unat x"
  by (simp add: unat_ucast_up_simp)

lemma toEnum_of_ucast:
  "LENGTH('b) \<le> LENGTH('a) \<Longrightarrow>
   (toEnum (unat (b::'b :: len word))::'a :: len word) = of_nat (unat b)"
  by (simp add: unat_pow_le_intro)

lemmas unat_ucast_mask = unat_ucast_eq_unat_and_mask[where w=a for a]

lemma t2n_mask_eq_if:
  "2 ^ n AND mask m = (if n < m then 2 ^ n else (0 :: 'a::len word))"
    by (rule word_eqI, auto simp add: word_size nth_w2p split: if_split)

lemma unat_ucast_le:
  "unat (ucast (x :: 'a :: len word) :: 'b :: len word) \<le> unat x"
  by (simp add: ucast_nat_def word_unat_less_le)

lemma ucast_le_up_down_iff:
  "\<lbrakk> LENGTH('a) \<le> LENGTH('b); (x :: 'b :: len word) \<le> ucast (max_word :: 'a :: len word) \<rbrakk>
   \<Longrightarrow> (ucast x \<le> (y :: 'a word)) = (x \<le> ucast y)"
  using le_max_word_ucast_id ucast_le_ucast by metis

lemma ucast_ucast_mask_shift:
  "a \<le> LENGTH('a) + b
   \<Longrightarrow> ucast (ucast (p AND mask a >> b) :: 'a :: len word) = p AND mask a >> b"
  by (metis add.commute le_mask_iff shiftr_mask_le ucast_ucast_eq_mask_shift word_and_le')

lemma unat_ucast_mask_shift:
  "a \<le> LENGTH('a) + b
   \<Longrightarrow> unat (ucast (p AND mask a >> b) :: 'a :: len word) = unat (p AND mask a >> b)"
  by (metis linear ucast_ucast_mask_shift unat_ucast_up_simp)

lemma mask_overlap_zero:
  "a \<le> b \<Longrightarrow> (p AND mask a) AND NOT(mask b) = 0"
  for p :: \<open>'a::len word\<close>
  by (metis NOT_mask_AND_mask mask_lower_twice2 max_def)

lemma mask_shifl_overlap_zero:
  "a + c \<le> b \<Longrightarrow> (p AND mask a << c) AND NOT(mask b) = 0"
  for p :: \<open>'a::len word\<close>
  by (metis and_mask_0_iff_le_mask mask_mono mask_shiftl_decompose order_trans shiftl_over_and_dist word_and_le' word_and_le2)

lemma mask_overlap_zero':
  "a \<ge> b \<Longrightarrow> (p AND NOT(mask a)) AND mask b = 0"
  for p :: \<open>'a::len word\<close>
  using mask_AND_NOT_mask mask_AND_less_0 by blast

lemma mask_rshift_mult_eq_rshift_lshift:
  "((a :: 'a :: len word) >> b) * (1 << c) = (a >> b << c)"
  by (simp add: shiftl_t2n)

lemma shift_alignment:
  "a \<ge> b \<Longrightarrow> is_aligned (p >> a << a) b"
  using is_aligned_shift is_aligned_weaken by blast

lemma mask_split_sum_twice:
  "a \<ge> b \<Longrightarrow> (p AND NOT(mask a)) + ((p AND mask a) AND NOT(mask b)) + (p AND mask b) = p"
  for p :: \<open>'a::len word\<close>
  by (simp add: add.commute multiple_mask_trivia word_bw_comms(1) word_bw_lcs(1) word_plus_and_or_coroll2)

lemma mask_shift_eq_mask_mask:
  "(p AND mask a >> b << b) = (p AND mask a) AND NOT(mask b)"
  for p :: \<open>'a::len word\<close>
  by (simp add: and_not_mask)

lemma mask_shift_sum:
  "\<lbrakk> a \<ge> b; unat n = unat (p AND mask b) \<rbrakk>
   \<Longrightarrow> (p AND NOT(mask a)) + (p AND mask a >> b) * (1 << b) + n = (p :: 'a :: len word)"
  by (metis and_not_mask mask_rshift_mult_eq_rshift_lshift mask_split_sum_twice word_unat.Rep_eqD)

lemma is_up_compose:
  "\<lbrakk> is_up uc; is_up uc' \<rbrakk> \<Longrightarrow> is_up (uc' \<circ> uc)"
  unfolding is_up_def by (simp add: Word.target_size Word.source_size)

lemma of_int_sint_scast:
  "of_int (sint (x :: 'a :: len word)) = (scast x :: 'b :: len word)"
  by (fact Word.of_int_sint) 

lemma scast_of_nat_to_signed [simp]:
  "scast (of_nat x :: 'a :: len word) = (of_nat x :: 'a signed word)"
  by transfer simp

lemma scast_of_nat_signed_to_unsigned_add:
  "scast (of_nat x + of_nat y :: 'a :: len signed word) = (of_nat x + of_nat y :: 'a :: len word)"
  by (metis of_nat_add scast_of_nat)

lemma scast_of_nat_unsigned_to_signed_add:
  "(scast (of_nat x + of_nat y :: 'a :: len word)) = (of_nat x + of_nat y :: 'a :: len signed word)"
  by (metis Abs_fnat_hom_add scast_of_nat_to_signed)

lemma and_mask_cases:
  fixes x :: "'a :: len word"
  assumes len: "n < LENGTH('a)"
  shows "x AND mask n \<in> of_nat ` set [0 ..< 2 ^ n]"
  apply (simp flip: take_bit_eq_mask)
  apply (rule image_eqI [of _ _ \<open>unat (take_bit n x)\<close>])
  using len apply simp_all
  apply transfer
  apply simp
  done

lemma sint_eq_uint_2pl:
  "\<lbrakk> (a :: 'a :: len word) < 2 ^ (LENGTH('a) - 1) \<rbrakk>
   \<Longrightarrow> sint a = uint a"
  by (simp add: not_msb_from_less sint_eq_uint word_2p_lem word_size)

lemma pow_sub_less:
  "\<lbrakk> a + b \<le> LENGTH('a); unat (x :: 'a :: len word) = 2 ^ a \<rbrakk>
   \<Longrightarrow> unat (x * 2 ^ b - 1) < 2 ^ (a + b)"
  by (metis (mono_tags) eq_or_less_helperD not_less of_nat_numeral power_add
                        semiring_1_class.of_nat_power unat_pow_le_intro word_unat.Rep_inverse)

lemma sle_le_2pl:
  "\<lbrakk> (b :: 'a :: len word) < 2 ^ (LENGTH('a) - 1); a \<le> b \<rbrakk> \<Longrightarrow> a <=s b"
  by (simp add: not_msb_from_less word_sle_msb_le)

lemma sless_less_2pl:
  "\<lbrakk> (b :: 'a :: len word) < 2 ^ (LENGTH('a) - 1); a < b \<rbrakk> \<Longrightarrow> a <s b"
  using not_msb_from_less word_sless_msb_less by blast

lemma and_mask2:
  "w << n >> n = w AND mask (size w - n)"
  for w :: \<open>'a::len word\<close>
  by (cases "n \<le> size w"; clarsimp simp: word_and_le2 and_mask shiftl_zero_size)

lemma aligned_sub_aligned_simple:
  "\<lbrakk> is_aligned a n; is_aligned b n \<rbrakk> \<Longrightarrow> is_aligned (a - b) n"
  by (simp add: aligned_sub_aligned)

lemma minus_one_shift:
  "- (1 << n) = (-1 << n :: 'a::len word)"
  by (simp add: mask_eq_decr_exp NOT_eq flip: mul_not_mask_eq_neg_shiftl)

lemma ucast_eq_mask:
  "(UCAST('a::len \<rightarrow> 'b::len) x = UCAST('a \<rightarrow> 'b) y) =
   (x AND mask LENGTH('b) = y AND mask LENGTH('b))"
  by (rule iffI; word_eqI_solve)

context
  fixes w :: "'a::len word"
begin

private lemma sbintrunc_uint_ucast:
  assumes "Suc n = LENGTH('b::len)"
  shows "sbintrunc n (uint (ucast w :: 'b word)) = sbintrunc n (uint w)"
  by (metis assms sbintrunc_bintrunc ucast_eq word_ubin.eq_norm)

private lemma test_bit_sbintrunc:
  assumes "i < LENGTH('a)"
  shows "(word_of_int (sbintrunc n (uint w)) :: 'a word) !! i
           = (if n < i then w !! n else w !! i)"
  using assms by (simp add: nth_sbintr)
                 (simp add: test_bit_bin)

private lemma test_bit_sbintrunc_ucast:
  assumes len_a: "i < LENGTH('a)"
  shows "(word_of_int (sbintrunc (LENGTH('b) - 1) (uint (ucast w :: 'b word))) :: 'a word) !! i
          = (if LENGTH('b::len) \<le> i then w !! (LENGTH('b) - 1) else w !! i)"
  apply (subst sbintrunc_uint_ucast)
   apply simp
  apply (subst test_bit_sbintrunc)
   apply (rule len_a)
  apply (rule if_cong[OF _ refl refl])
  using leD less_linear by fastforce

lemma scast_ucast_high_bits:
  \<open>scast (ucast w :: 'b::len word) = w
     \<longleftrightarrow> (\<forall> i \<in> {LENGTH('b) ..< size w}. w !! i = w !! (LENGTH('b) - 1))\<close>
proof (cases \<open>LENGTH('a) \<le> LENGTH('b)\<close>)
  case True
  moreover define m where \<open>m = LENGTH('b) - LENGTH('a)\<close>
  ultimately have \<open>LENGTH('b) = m + LENGTH('a)\<close>
    by simp
  then show ?thesis
    apply (simp_all add: signed_ucast_eq word_size)
    apply (rule bit_word_eqI)
    apply (simp add: bit_signed_take_bit_iff)
    done
next
  case False
  define q where \<open>q = LENGTH('b) - 1\<close>
  then have \<open>LENGTH('b) = Suc q\<close>
    by simp
  moreover define m where \<open>m = Suc LENGTH('a) - LENGTH('b)\<close>
  with False \<open>LENGTH('b) = Suc q\<close> have \<open>LENGTH('a) = m + q\<close>
    by (simp add: not_le)
  ultimately show ?thesis
    apply (simp_all add: signed_ucast_eq word_size)
    apply (transfer fixing: m q)
    apply (simp add: signed_take_bit_take_bit)
    apply rule
    apply (subst bit_eq_iff)
    apply (simp add: bit_take_bit_iff bit_signed_take_bit_iff min_def)
    apply (auto simp add: Suc_le_eq)
    using less_imp_le_nat apply blast
    using less_imp_le_nat apply blast
    done
qed
  
lemma scast_ucast_mask_compare:
  "scast (ucast w :: 'b::len word) = w
   \<longleftrightarrow> (w \<le> mask (LENGTH('b) - 1) \<or> NOT(mask (LENGTH('b) - 1)) \<le> w)"
  apply (clarsimp simp: le_mask_high_bits neg_mask_le_high_bits scast_ucast_high_bits word_size)
  apply (rule iffI; clarsimp)
   apply (rename_tac i j; case_tac "i = LENGTH('b) - 1"; case_tac "j = LENGTH('b) - 1")
  by auto

lemma ucast_less_shiftl_helper':
  "\<lbrakk> LENGTH('b) + (a::nat) < LENGTH('a); 2 ^ (LENGTH('b) + a) \<le> n\<rbrakk>
   \<Longrightarrow> (ucast (x :: 'b::len word) << a) < (n :: 'a::len word)"
  apply (erule order_less_le_trans[rotated])
  using ucast_less[where x=x and 'a='a]
  apply (simp only: shiftl_t2n field_simps)
  apply (rule word_less_power_trans2; simp)
  done

end

lemma ucast_ucast_mask2:
  "is_down (UCAST ('a \<rightarrow> 'b)) \<Longrightarrow>
   UCAST ('b::len \<rightarrow> 'c::len) (UCAST ('a::len \<rightarrow> 'b::len) x) = UCAST ('a \<rightarrow> 'c) (x AND mask LENGTH('b))"
  by word_eqI_solve

lemma ucast_NOT:
  "ucast (NOT x) = NOT(ucast x) AND mask (LENGTH('a))" for x::"'a::len word"
  by word_eqI

lemma ucast_NOT_down:
  "is_down UCAST('a::len \<rightarrow> 'b::len) \<Longrightarrow> UCAST('a \<rightarrow> 'b) (NOT x) = NOT(UCAST('a \<rightarrow> 'b) x)"
  by word_eqI

lemma upto_enum_step_shift:
  "\<lbrakk> is_aligned p n \<rbrakk> \<Longrightarrow>
  ([p , p + 2 ^ m .e. p + 2 ^ n - 1])
      = map ((+) p) [0, 2 ^ m .e. 2 ^ n - 1]"
  apply (erule is_aligned_get_word_bits)
   prefer 2
   apply (simp add: map_idI)
  apply (clarsimp simp: upto_enum_step_def)
  apply (frule is_aligned_no_overflow)
  apply (simp add: linorder_not_le [symmetric])
  done

lemma upto_enum_step_shift_red:
  "\<lbrakk> is_aligned p sz; sz < LENGTH('a); us \<le> sz \<rbrakk>
     \<Longrightarrow> [p :: 'a :: len word, p + 2 ^ us .e. p + 2 ^ sz - 1]
          = map (\<lambda>x. p + of_nat x * 2 ^ us) [0 ..< 2 ^ (sz - us)]"
  apply (subst upto_enum_step_shift, assumption)
  apply (simp add: upto_enum_step_red)
  done

lemma upto_enum_step_subset:
  "set [x, y .e. z] \<subseteq> {x .. z}"
  apply (clarsimp simp: upto_enum_step_def linorder_not_less)
  apply (drule div_to_mult_word_lt)
  apply (rule conjI)
   apply (erule word_random[rotated])
   apply simp
  apply (rule order_trans)
   apply (erule word_plus_mono_right)
   apply simp
  apply simp
  done

lemma if_and_helper:
  "(If x v v') AND v'' = If x (v AND v'') (v' AND v'')"
  by (rule if_distrib)

end
