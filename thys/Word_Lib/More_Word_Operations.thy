
section \<open>Misc word operations\<close>

theory More_Word_Operations
  imports
    "HOL-Library.Word"
    Reversed_Bit_Lists
    Aligned
    More_Divides
    More_Misc
    "HOL-Library.Sublist"
begin

definition
  ptr_add :: "'a :: len word \<Rightarrow> nat \<Rightarrow> 'a word" where
  "ptr_add ptr n \<equiv> ptr + of_nat n"

definition
  alignUp :: "'a::len word \<Rightarrow> nat \<Rightarrow> 'a word" where
 "alignUp x n \<equiv> x + 2 ^ n - 1 AND NOT (2 ^ n - 1)"

(* standard notation for blocks of 2^n-1 words, usually aligned;
   abbreviation so it simplifies directly *)
abbreviation mask_range :: "'a::len word \<Rightarrow> nat \<Rightarrow> 'a word set" where
  "mask_range p n \<equiv> {p .. p + mask n}"

definition
  w2byte :: "'a :: len word \<Rightarrow> 8 word" where
  "w2byte \<equiv> ucast"

(* Count leading zeros  *)
definition
  word_clz :: "'a::len word \<Rightarrow> nat"
where
  "word_clz w \<equiv> length (takeWhile Not (to_bl w))"

(* Count trailing zeros  *)
definition
  word_ctz :: "'a::len word \<Rightarrow> nat"
where
  "word_ctz w \<equiv> length (takeWhile Not (rev (to_bl w)))"

definition
  word_log2 :: "'a::len word \<Rightarrow> nat"
where
  "word_log2 (w::'a::len word) \<equiv> size w - 1 - word_clz w"

(* Bit population count. Equivalent of __builtin_popcount. *)
definition
  pop_count :: "('a::len) word \<Rightarrow> nat"
where
  "pop_count w \<equiv> length (filter id (to_bl w))"

(* Sign extension from bit n *)
definition
  sign_extend :: "nat \<Rightarrow> 'a::len word \<Rightarrow> 'a word"
where
  "sign_extend n w \<equiv> if w !! n then w OR NOT (mask n) else w AND mask n"

lemma sign_extend_eq_signed_take_bit:
  \<open>sign_extend = signed_take_bit\<close>
proof (rule ext)+
  fix n and w :: \<open>'a::len word\<close>
  show \<open>sign_extend n w = signed_take_bit n w\<close>
  proof (rule bit_word_eqI)
    fix q
    assume \<open>q < LENGTH('a)\<close>
    then show \<open>bit (sign_extend n w) q \<longleftrightarrow> bit (signed_take_bit n w) q\<close>
      by (auto simp add: test_bit_eq_bit bit_signed_take_bit_iff
        sign_extend_def bit_and_iff bit_or_iff bit_not_iff bit_mask_iff not_less
        exp_eq_0_imp_not_bit not_le min_def)
  qed
qed

definition
  sign_extended :: "nat \<Rightarrow> 'a::len word \<Rightarrow> bool"
where
  "sign_extended n w \<equiv> \<forall>i. n < i \<longrightarrow> i < size w \<longrightarrow> w !! i = w !! n"

lemma ptr_add_0 [simp]:
  "ptr_add ref 0 = ref "
  unfolding ptr_add_def by simp

lemma pop_count_0[simp]:
  "pop_count 0 = 0"
  by (clarsimp simp:pop_count_def)

lemma pop_count_1[simp]:
  "pop_count 1 = 1"
  by (clarsimp simp:pop_count_def to_bl_1)

lemma pop_count_0_imp_0:
  "(pop_count w = 0) = (w = 0)"
  apply (rule iffI)
   apply (clarsimp simp:pop_count_def)
   apply (subst (asm) filter_empty_conv)
   apply (clarsimp simp:eq_zero_set_bl)
   apply fast
  apply simp
  done

lemma word_log2_nth_same:
  "w \<noteq> 0 \<Longrightarrow> w !! word_log2 w"
  unfolding word_log2_def
  using nth_length_takeWhile[where P=Not and xs="to_bl w"]
  apply (simp add: word_clz_def word_size to_bl_nth)
  apply (fastforce simp: linorder_not_less eq_zero_set_bl
                   dest: takeWhile_take_has_property)
  done

lemma word_log2_nth_not_set:
  "\<lbrakk> word_log2 w < i ; i < size w \<rbrakk> \<Longrightarrow> \<not> w !! i"
  unfolding word_log2_def word_clz_def
  using takeWhile_take_has_property_nth[where P=Not and xs="to_bl w" and n="size w - Suc i"]
  by (fastforce simp add: to_bl_nth word_size)

lemma word_log2_highest:
  assumes a: "w !! i"
  shows "i \<le> word_log2 w"
proof -
  from a have "i < size w" by - (rule test_bit_size)
  with a show ?thesis
    by - (rule ccontr, simp add: word_log2_nth_not_set)
qed

lemma word_log2_max:
  "word_log2 w < size w"
  unfolding word_log2_def word_clz_def
  by simp

lemma word_clz_0[simp]:
  "word_clz (0::'a::len word) = LENGTH('a)"
  unfolding word_clz_def
  by (simp add: takeWhile_replicate)

lemma word_clz_minus_one[simp]:
  "word_clz (-1::'a::len word) = 0"
  unfolding word_clz_def
  by (simp add: takeWhile_replicate)

lemma is_aligned_alignUp[simp]:
  "is_aligned (alignUp p n) n"
  by (simp add: alignUp_def is_aligned_mask mask_eq_decr_exp word_bw_assocs)

lemma alignUp_le[simp]:
  "alignUp p n \<le> p + 2 ^ n - 1"
  unfolding alignUp_def by (rule word_and_le2)

lemma alignUp_idem:
  fixes a :: "'a::len word"
  assumes "is_aligned a n" "n < LENGTH('a)"
  shows "alignUp a n = a"
  using assms unfolding alignUp_def
  by (metis mask_eq_decr_exp is_aligned_add_helper p_assoc_help power_2_ge_iff)

lemma alignUp_not_aligned_eq:
  fixes a :: "'a :: len word"
  assumes al: "\<not> is_aligned a n"
  and     sz: "n < LENGTH('a)"
  shows   "alignUp a n = (a div 2 ^ n + 1) * 2 ^ n"
proof -
  have anz: "a mod 2 ^ n \<noteq> 0"
    by (rule not_aligned_mod_nz) fact+

  then have um: "unat (a mod 2 ^ n - 1) div 2 ^ n = 0" using sz
    by (meson Euclidean_Division.div_eq_0_iff le_m1_iff_lt measure_unat order_less_trans
              unat_less_power word_less_sub_le word_mod_less_divisor)

  have "a + 2 ^ n - 1 = (a div 2 ^ n) * 2 ^ n + (a mod 2 ^ n) + 2 ^ n - 1"
    by (simp add: word_mod_div_equality)
  also have "\<dots> = (a mod 2 ^ n - 1) + (a div 2 ^ n + 1) * 2 ^ n"
    by (simp add: field_simps)
  finally show "alignUp a n = (a div 2 ^ n + 1) * 2 ^ n" using sz
    unfolding alignUp_def
    apply (subst mask_eq_decr_exp [symmetric])
    apply (erule ssubst)
    apply (subst neg_mask_is_div)
    apply (simp add: word_arith_nat_div)
    apply (subst unat_word_ariths(1) unat_word_ariths(2))+
    apply (subst uno_simps)
    apply (subst unat_1)
    apply (subst mod_add_right_eq)
    apply simp
    apply (subst power_mod_div)
    apply (subst div_mult_self1)
     apply simp
    apply (subst um)
    apply simp
    apply (subst mod_mod_power)
    apply simp
    apply (subst word_unat_power, subst Abs_fnat_hom_mult)
    apply (subst mult_mod_left)
    apply (subst power_add [symmetric])
    apply simp
    apply (subst Abs_fnat_hom_1)
    apply (subst Abs_fnat_hom_add)
    apply (subst word_unat_power, subst Abs_fnat_hom_mult)
    apply (subst word_unat.Rep_inverse[symmetric], subst Abs_fnat_hom_mult)
    apply simp
    done
qed

lemma alignUp_ge:
  fixes a :: "'a :: len word"
  assumes sz: "n < LENGTH('a)"
  and nowrap: "alignUp a n \<noteq> 0"
  shows "a \<le> alignUp a n"
proof (cases "is_aligned a n")
  case True
  then show ?thesis using sz
    by (subst alignUp_idem, simp_all)
next
  case False

  have lt0: "unat a div 2 ^ n < 2 ^ (LENGTH('a) - n)" using sz
    by (metis shiftr_div_2n' word_shiftr_lt)

  have"2 ^ n * (unat a div 2 ^ n + 1) \<le> 2 ^ LENGTH('a)" using sz
    by (metis One_nat_def Suc_leI add.right_neutral add_Suc_right lt0 nat_le_power_trans nat_less_le)
  moreover have "2 ^ n * (unat a div 2 ^ n + 1) \<noteq> 2 ^ LENGTH('a)" using nowrap sz
    apply -
    apply (erule contrapos_nn)
    apply (subst alignUp_not_aligned_eq [OF False sz])
    apply (subst unat_arith_simps)
    apply (subst unat_word_ariths)
    apply (subst unat_word_ariths)
    apply simp
    apply (subst mult_mod_left)
    apply (simp add: unat_div field_simps power_add[symmetric] mod_mod_power min.absorb2)
    done
  ultimately have lt: "2 ^ n * (unat a div 2 ^ n + 1) < 2 ^ LENGTH('a)" by simp

  have "a = a div 2 ^ n * 2 ^ n + a mod 2 ^ n" by (rule word_mod_div_equality [symmetric])
  also have "\<dots> < (a div 2 ^ n + 1) * 2 ^ n" using sz lt
    apply (simp add: field_simps)
    apply (rule word_add_less_mono1)
    apply (rule word_mod_less_divisor)
    apply (simp add: word_less_nat_alt)
    apply (subst unat_word_ariths)
    apply (simp add: unat_div)
    done
  also have "\<dots> =  alignUp a n"
    by (rule alignUp_not_aligned_eq [symmetric]) fact+
  finally show ?thesis by (rule order_less_imp_le)
qed

lemma alignUp_le_greater_al:
  fixes x :: "'a :: len word"
  assumes le: "a \<le> x"
  and     sz: "n < LENGTH('a)"
  and     al: "is_aligned x n"
  shows   "alignUp a n \<le> x"
proof (cases "is_aligned a n")
  case True
  then show ?thesis using sz le by (simp add: alignUp_idem)
next
  case False

  then have anz: "a mod 2 ^ n \<noteq> 0"
    by (rule not_aligned_mod_nz)

  from al obtain k where xk: "x = 2 ^ n * of_nat k" and kv: "k < 2 ^ (LENGTH('a) - n)"
    by (auto elim!: is_alignedE)

  then have kn: "unat (of_nat k :: 'a word) * unat ((2::'a word) ^ n) < 2 ^ LENGTH('a)"
    using sz
    apply (subst unat_of_nat_eq)
     apply (erule order_less_le_trans)
     apply simp
    apply (subst mult.commute)
    apply simp
    apply (rule nat_less_power_trans)
     apply simp
    apply simp
    done

  have au: "alignUp a n = (a div 2 ^ n + 1) * 2 ^ n"
    by (rule alignUp_not_aligned_eq) fact+
  also have "\<dots> \<le> of_nat k * 2 ^ n"
  proof (rule word_mult_le_mono1 [OF inc_le _ kn])
    show "a div 2 ^ n < of_nat k" using kv xk le sz anz
      by (simp add: alignUp_div_helper)

    show "(0:: 'a word) < 2 ^ n" using sz by (simp add: p2_gt_0 sz)
  qed

  finally show ?thesis using xk by (simp add: field_simps)
qed

lemma alignUp_is_aligned_nz:
  fixes a :: "'a :: len word"
  assumes al: "is_aligned x n"
  and     sz: "n < LENGTH('a)"
  and     ax: "a \<le> x"
  and     az: "a \<noteq> 0"
  shows   "alignUp (a::'a :: len word) n \<noteq> 0"
proof (cases "is_aligned a n")
  case True
  then have "alignUp a n = a" using sz by (simp add: alignUp_idem)
  then show ?thesis using az by simp
next
  case False
  then have anz: "a mod 2 ^ n \<noteq> 0"
    by (rule not_aligned_mod_nz)

  {
    assume asm: "alignUp a n = 0"

    have lt0: "unat a div 2 ^ n < 2 ^ (LENGTH('a) - n)" using sz
      by (metis shiftr_div_2n' word_shiftr_lt)

    have leq: "2 ^ n * (unat a div 2 ^ n + 1) \<le> 2 ^ LENGTH('a)" using sz
      by (metis One_nat_def Suc_leI add.right_neutral add_Suc_right lt0 nat_le_power_trans
                order_less_imp_le)

    from al obtain k where  kv: "k < 2 ^ (LENGTH('a) - n)" and xk: "x = 2 ^ n * of_nat k"
      by (auto elim!: is_alignedE)

    then have "a div 2 ^ n < of_nat k" using ax sz anz
      by (rule alignUp_div_helper)

    then have r: "unat a div 2 ^ n < k" using sz
      by (simp flip: drop_bit_eq_div unat_drop_bit_eq) (metis leI le_unat_uoi unat_mono)

    have "alignUp a n = (a div 2 ^ n + 1) * 2 ^ n"
      by (rule alignUp_not_aligned_eq) fact+

    then have "\<dots> = 0" using asm by simp
    then have "2 ^ LENGTH('a) dvd 2 ^ n * (unat a div 2 ^ n + 1)"
      using sz by (simp add: unat_arith_simps ac_simps)
                  (simp add: unat_word_ariths mod_simps mod_eq_0_iff_dvd)
    with leq have "2 ^ n * (unat a div 2 ^ n + 1) = 2 ^ LENGTH('a)"
      by (force elim!: le_SucE)
    then have "unat a div 2 ^ n = 2 ^ LENGTH('a) div 2 ^ n - 1"
      by (metis (no_types, hide_lams) Groups.add_ac(2) add.right_neutral
                add_diff_cancel_left' div_le_dividend div_mult_self4 gr_implies_not0
                le_neq_implies_less power_eq_0_iff zero_neq_numeral)
    then have "unat a div 2 ^ n = 2 ^ (LENGTH('a) - n) - 1"
      using sz by (simp add: power_sub)
    then have "2 ^ (LENGTH('a) - n) - 1 < k" using r
      by simp
    then have False using kv by simp
  } then show ?thesis by clarsimp
qed

lemma alignUp_ar_helper:
  fixes a :: "'a :: len word"
  assumes al: "is_aligned x n"
  and     sz: "n < LENGTH('a)"
  and    sub: "{x..x + 2 ^ n - 1} \<subseteq> {a..b}"
  and    anz: "a \<noteq> 0"
  shows "a \<le> alignUp a n \<and> alignUp a n + 2 ^ n - 1 \<le> b"
proof
  from al have xl: "x \<le> x + 2 ^ n - 1" by (simp add: is_aligned_no_overflow)

  from xl sub have ax: "a \<le> x"
    by (clarsimp elim!: range_subset_lower [where x = x])

  show "a \<le> alignUp a n"
  proof (rule alignUp_ge)
    show "alignUp a n \<noteq> 0" using al sz ax anz
      by (rule alignUp_is_aligned_nz)
  qed fact+

  show "alignUp a n + 2 ^ n - 1 \<le> b"
  proof (rule order_trans)
    from xl show tp: "x + 2 ^ n - 1 \<le> b" using sub
      by (clarsimp elim!: range_subset_upper [where x = x])

    from ax have "alignUp a n \<le> x"
      by (rule alignUp_le_greater_al) fact+
    then have "alignUp a n + (2 ^ n - 1) \<le> x + (2 ^ n - 1)"
      using xl al is_aligned_no_overflow' olen_add_eqv word_plus_mcs_3 by blast
    then show "alignUp a n + 2 ^ n - 1 \<le> x + 2 ^ n - 1"
      by (simp add: field_simps)
  qed
qed

lemma alignUp_def2:
  "alignUp a sz = a + 2 ^ sz - 1 AND NOT (mask sz)"
  by (simp add: alignUp_def flip: mask_eq_decr_exp)

lemma alignUp_def3:
  "alignUp a sz = 2^ sz + (a - 1 AND NOT (mask sz))"
  by (simp add: alignUp_def2 is_aligned_triv field_simps mask_out_add_aligned)

lemma  alignUp_plus:
  "is_aligned w us \<Longrightarrow> alignUp (w + a) us  = w + alignUp a us"
  by (clarsimp simp: alignUp_def2 mask_out_add_aligned field_simps)

lemma alignUp_distance:
  "alignUp (q :: 'a :: len word) sz - q \<le> mask sz"
  by (metis (no_types) add.commute add_diff_cancel_left alignUp_def2 diff_add_cancel
                       mask_2pm1 subtract_mask(2) word_and_le1 word_sub_le_iff)

lemma is_aligned_diff_neg_mask:
  "is_aligned p sz \<Longrightarrow> (p - q AND NOT (mask sz)) = (p - ((alignUp q sz) AND NOT (mask sz)))"
  apply (clarsimp simp only:word_and_le2 diff_conv_add_uminus)
  apply (subst mask_out_add_aligned[symmetric]; simp)
  apply (rule sum_to_zero)
  apply (subst add.commute)
  apply (simp add: alignUp_distance is_aligned_neg_mask_eq mask_out_add_aligned)
  apply (metis add_cancel_right_right alignUp_distance and_mask_eq_iff_le_mask word_plus_and_or_coroll2)
  done

lemma word_clz_max:
  "word_clz w \<le> size (w::'a::len word)"
  unfolding word_clz_def
  by (metis length_takeWhile_le word_size_bl)

lemma word_clz_nonzero_max:
  fixes w :: "'a::len word"
  assumes nz: "w \<noteq> 0"
  shows "word_clz w < size (w::'a::len word)"
proof -
  {
    assume a: "word_clz w = size (w::'a::len word)"
    hence "length (takeWhile Not (to_bl w)) = length (to_bl w)"
      by (simp add: word_clz_def word_size)
    hence allj: "\<forall>j\<in>set(to_bl w). \<not> j"
      by (metis a length_takeWhile_less less_irrefl_nat word_clz_def)
    hence "to_bl w = replicate (length (to_bl w)) False"
      by (fastforce intro!: list_of_false)
    hence "w = 0"
      by (metis to_bl_0 word_bl.Rep_eqD word_bl_Rep')
    with nz have False by simp
  }
  thus ?thesis using word_clz_max
    by (fastforce intro: le_neq_trans)
qed

(* Sign extension from bit n. *)

lemma sign_extend_bitwise_if:
  "i < size w \<Longrightarrow> sign_extend e w !! i \<longleftrightarrow> (if i < e then w !! i else w !! e)"
  by (simp add: sign_extend_def neg_mask_test_bit word_size)

lemma sign_extend_bitwise_if':
  \<open>i < LENGTH('a) \<Longrightarrow> sign_extend e w !! i \<longleftrightarrow> (if i < e then w !! i else w !! e)\<close>
  for w :: \<open>'a::len word\<close>
  using sign_extend_bitwise_if [of i w e] by (simp add: word_size)

lemma sign_extend_bitwise_disj:
  "i < size w \<Longrightarrow> sign_extend e w !! i \<longleftrightarrow> i \<le> e \<and> w !! i \<or> e \<le> i \<and> w !! e"
  by (auto simp: sign_extend_bitwise_if)

lemma sign_extend_bitwise_cases:
  "i < size w \<Longrightarrow> sign_extend e w !! i \<longleftrightarrow> (i \<le> e \<longrightarrow> w !! i) \<and> (e \<le> i \<longrightarrow> w !! e)"
  by (auto simp: sign_extend_bitwise_if)

lemmas sign_extend_bitwise_disj' = sign_extend_bitwise_disj[simplified word_size]
lemmas sign_extend_bitwise_cases' = sign_extend_bitwise_cases[simplified word_size]

(* Often, it is easier to reason about an operation which does not overwrite
   the bit which determines which mask operation to apply. *)
lemma sign_extend_def':
  "sign_extend n w = (if w !! n then w OR NOT (mask (Suc n)) else w AND mask (Suc n))"
  by (rule bit_word_eqI) (auto simp add: bit_simps sign_extend_eq_signed_take_bit min_def test_bit_eq_bit less_Suc_eq_le)

lemma sign_extended_sign_extend:
  "sign_extended n (sign_extend n w)"
  by (clarsimp simp: sign_extended_def word_size sign_extend_bitwise_if)

lemma sign_extended_iff_sign_extend:
  "sign_extended n w \<longleftrightarrow> sign_extend n w = w"
  apply auto
   apply (auto simp add: bit_eq_iff)
    apply (simp_all add: bit_simps sign_extend_eq_signed_take_bit not_le min_def sign_extended_def test_bit_eq_bit word_size split: if_splits)
  using le_imp_less_or_eq apply auto[1]
   apply (metis bit_imp_le_length nat_less_le)
  apply (metis Suc_leI Suc_n_not_le_n le_trans nat_less_le)
  done

lemma sign_extended_weaken:
  "sign_extended n w \<Longrightarrow> n \<le> m \<Longrightarrow> sign_extended m w"
  unfolding sign_extended_def by (cases "n < m") auto

lemma sign_extend_sign_extend_eq:
  "sign_extend m (sign_extend n w) = sign_extend (min m n) w"
  by (rule bit_word_eqI) (simp add: sign_extend_eq_signed_take_bit bit_simps)

lemma sign_extended_high_bits:
  "\<lbrakk> sign_extended e p; j < size p; e \<le> i; i < j \<rbrakk> \<Longrightarrow> p !! i = p !! j"
  by (drule (1) sign_extended_weaken; simp add: sign_extended_def)

lemma sign_extend_eq:
  "w AND mask (Suc n) = v AND mask (Suc n) \<Longrightarrow> sign_extend n w = sign_extend n v"
  by (simp flip: take_bit_eq_mask add: sign_extend_eq_signed_take_bit signed_take_bit_eq_iff_take_bit_eq)

lemma sign_extended_add:
  assumes p: "is_aligned p n"
  assumes f: "f < 2 ^ n"
  assumes e: "n \<le> e"
  assumes "sign_extended e p"
  shows "sign_extended e (p + f)"
proof (cases "e < size p")
  case True
  note and_or = is_aligned_add_or[OF p f]
  have "\<not> f !! e"
    using True e less_2p_is_upper_bits_unset[THEN iffD1, OF f]
    by (fastforce simp: word_size)
  hence i: "(p + f) !! e = p !! e"
    by (simp add: and_or)
  have fm: "f AND mask e = f"
    by (fastforce intro: subst[where P="\<lambda>f. f AND mask e = f", OF less_mask_eq[OF f]]
                  simp: mask_twice e)
  show ?thesis
    using assms
     apply (simp add: sign_extended_iff_sign_extend sign_extend_def i)
     apply (simp add: and_or word_bw_comms[of p f])
     apply (clarsimp simp: word_ao_dist fm word_bw_assocs split: if_splits)
    done
next
  case False thus ?thesis
    by (simp add: sign_extended_def word_size)
qed

lemma sign_extended_neq_mask:
  "\<lbrakk>sign_extended n ptr; m \<le> n\<rbrakk> \<Longrightarrow> sign_extended n (ptr AND NOT (mask m))"
  by (fastforce simp: sign_extended_def word_size neg_mask_test_bit)

definition
  "limited_and (x :: 'a :: len word) y \<longleftrightarrow> (x AND y = x)"

lemma limited_and_eq_0:
  "\<lbrakk> limited_and x z; y AND NOT z = y \<rbrakk> \<Longrightarrow> x AND y = 0"
  unfolding limited_and_def
  apply (subst arg_cong2[where f="(AND)"])
    apply (erule sym)+
  apply (simp(no_asm) add: word_bw_assocs word_bw_comms word_bw_lcs)
  done

lemma limited_and_eq_id:
  "\<lbrakk> limited_and x z; y AND z = z \<rbrakk> \<Longrightarrow> x AND y = x"
  unfolding limited_and_def
  by (erule subst, fastforce simp: word_bw_lcs word_bw_assocs word_bw_comms)

lemma lshift_limited_and:
  "limited_and x z \<Longrightarrow> limited_and (x << n) (z << n)"
  unfolding limited_and_def
  by (simp add: shiftl_over_and_dist[symmetric])

lemma rshift_limited_and:
  "limited_and x z \<Longrightarrow> limited_and (x >> n) (z >> n)"
  unfolding limited_and_def
  by (simp add: shiftr_over_and_dist[symmetric])

lemmas limited_and_simps1 = limited_and_eq_0 limited_and_eq_id

lemmas is_aligned_limited_and
    = is_aligned_neg_mask_eq[unfolded mask_eq_decr_exp, folded limited_and_def]

lemmas limited_and_simps = limited_and_simps1
       limited_and_simps1[OF is_aligned_limited_and]
       limited_and_simps1[OF lshift_limited_and]
       limited_and_simps1[OF rshift_limited_and]
       limited_and_simps1[OF rshift_limited_and, OF is_aligned_limited_and]
       not_one shiftl_shiftr1[unfolded word_size mask_eq_decr_exp]
       shiftl_shiftr2[unfolded word_size mask_eq_decr_exp]

definition
  from_bool :: "bool \<Rightarrow> 'a::len word" where
  "from_bool b \<equiv> case b of True \<Rightarrow> of_nat 1
                         | False \<Rightarrow> of_nat 0"

lemma from_bool_eq:
  \<open>from_bool = of_bool\<close>
  by (simp add: fun_eq_iff from_bool_def)

lemma from_bool_0:
  "(from_bool x = 0) = (\<not> x)"
  by (simp add: from_bool_def split: bool.split)

definition
  to_bool :: "'a::len word \<Rightarrow> bool" where
  "to_bool \<equiv> (\<noteq>) 0"

lemma to_bool_and_1:
  "to_bool (x AND 1) = (x !! 0)"
  by (simp add: test_bit_word_eq to_bool_def and_one_eq mod_2_eq_odd)

lemma to_bool_from_bool [simp]:
  "to_bool (from_bool r) = r"
  unfolding from_bool_def to_bool_def
  by (simp split: bool.splits)

lemma from_bool_neq_0 [simp]:
  "(from_bool b \<noteq> 0) = b"
  by (simp add: from_bool_def split: bool.splits)

lemma from_bool_mask_simp [simp]:
  "(from_bool r :: 'a::len word) AND 1 = from_bool r"
  unfolding from_bool_def
  by (clarsimp split: bool.splits)

lemma from_bool_1 [simp]:
  "(from_bool P = 1) = P"
  by (simp add: from_bool_def split: bool.splits)

lemma ge_0_from_bool [simp]:
  "(0 < from_bool P) = P"
  by (simp add: from_bool_def split: bool.splits)

lemma limited_and_from_bool:
  "limited_and (from_bool b) 1"
  by (simp add: from_bool_def limited_and_def split: bool.split)

lemma to_bool_1 [simp]: "to_bool 1" by (simp add: to_bool_def)
lemma to_bool_0 [simp]: "\<not>to_bool 0" by (simp add: to_bool_def)

lemma from_bool_eq_if:
  "(from_bool Q = (if P then 1 else 0)) = (P = Q)"
  by (cases Q) (simp_all add: from_bool_def)

lemma to_bool_eq_0:
  "(\<not> to_bool x) = (x = 0)"
  by (simp add: to_bool_def)

lemma to_bool_neq_0:
  "(to_bool x) = (x \<noteq> 0)"
  by (simp add: to_bool_def)

lemma from_bool_all_helper:
  "(\<forall>bool. from_bool bool = val \<longrightarrow> P bool)
      = ((\<exists>bool. from_bool bool = val) \<longrightarrow> P (val \<noteq> 0))"
  by (auto simp: from_bool_0)

lemma from_bool_to_bool_iff:
  "w = from_bool b \<longleftrightarrow> to_bool w = b \<and> (w = 0 \<or> w = 1)"
  by (cases b) (auto simp: from_bool_def to_bool_def)

lemma from_bool_eqI:
  "from_bool x = from_bool y \<Longrightarrow> x = y"
  unfolding from_bool_def
  by (auto split: bool.splits)

text \<open>right-padding a word to a certain length\<close>

definition
  "bl_pad_to bl sz \<equiv> bl @ (replicate (sz - length bl) False)"

lemma bl_pad_to_length:
  assumes lbl: "length bl \<le> sz"
  shows   "length (bl_pad_to bl sz) = sz"
  using lbl by (simp add: bl_pad_to_def)

lemma bl_pad_to_prefix:
  "prefix bl (bl_pad_to bl sz)"
  by (simp add: bl_pad_to_def)

end