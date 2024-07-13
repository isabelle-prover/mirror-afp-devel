(*
 * Copyright Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(* Author: Jeremy Dawson and Gerwin Klein, NICTA *)

section \<open>Splitting words into lists\<close>

theory Rsplit
  imports More_Word Bit_Shifts_Infix_Syntax
begin

lemmas th_if_simp1 = if_split [where P = "(=) l", THEN iffD1, THEN conjunct1, THEN mp] for l
lemmas th_if_simp2 = if_split [where P = "(=) l", THEN iffD1, THEN conjunct2, THEN mp] for l


definition bin_split :: \<open>nat \<Rightarrow> int \<Rightarrow> int \<times> int\<close>
  where [simp]: \<open>bin_split n k = (drop_bit n k, take_bit n k)\<close>

lemma [code]:
  "bin_split (Suc n) w = (let (w1, w2) = bin_split n (w div 2) in (w1, of_bool (odd w) + 2 * w2))"
  "bin_split 0 w = (w, 0)"
  by (simp_all add: drop_bit_Suc take_bit_Suc mod_2_eq_odd)

fun bin_rsplit_aux :: "nat \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int list \<Rightarrow> int list"
  where "bin_rsplit_aux n m c bs =
    (if m = 0 \<or> n = 0 then bs
     else
      let (a, b) = bin_split n c
      in bin_rsplit_aux n (m - n) a (b # bs))"

definition bin_rsplit :: "nat \<Rightarrow> nat \<times> int \<Rightarrow> int list"
  where "bin_rsplit n w = bin_rsplit_aux n (fst w) (snd w) []"

fun bin_rsplitl_aux :: "nat \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int list \<Rightarrow> int list"
  where "bin_rsplitl_aux n m c bs =
    (if m = 0 \<or> n = 0 then bs
     else
      let (a, b) = bin_split (min m n) c
      in bin_rsplitl_aux n (m - n) a (b # bs))"

definition bin_rsplitl :: "nat \<Rightarrow> nat \<times> int \<Rightarrow> int list"
  where "bin_rsplitl n w = bin_rsplitl_aux n (fst w) (snd w) []"

declare bin_rsplit_aux.simps [simp del]
declare bin_rsplitl_aux.simps [simp del]

lemma bin_nth_split:
  "bin_split n c = (a, b) \<Longrightarrow>
    (\<forall>k. (bit :: int \<Rightarrow> nat \<Rightarrow> bool) a k = (bit :: int \<Rightarrow> nat \<Rightarrow> bool) c (n + k)) \<and>
    (\<forall>k. (bit :: int \<Rightarrow> nat \<Rightarrow> bool) b k = (k < n \<and> (bit :: int \<Rightarrow> nat \<Rightarrow> bool) c k))"
  apply (drule sym)
  apply (simp add: bit_simps)
  done

lemma split_bintrunc: "bin_split n c = (a, b) \<Longrightarrow> b = (take_bit :: nat \<Rightarrow> int \<Rightarrow> int) n c"
  by simp

lemma bin_cat_split: "bin_split n w = (u, v) \<Longrightarrow> w = (\<lambda>k n l. concat_bit n l k) u n v"
  apply (drule sym)
  using bits_ident [of n w]
  apply (simp add: concat_bit_eq)
  done

lemma bin_split_cat: "bin_split n ((\<lambda>k n l. concat_bit n l k) v n w) = (v, (take_bit :: nat \<Rightarrow> int \<Rightarrow> int) n w)"
  apply (auto intro!: bit_eqI)
     apply (simp_all add: bit_simps)
  apply auto
  done

lemma bin_split_zero [simp]: "bin_split n 0 = (0, 0)"
  by simp

lemma bin_split_minus1 [simp]:
  "bin_split n (- 1) = (- 1, (take_bit :: nat \<Rightarrow> int \<Rightarrow> int) n (- 1))"
  by simp

lemma bin_split_trunc:
  "bin_split (min m n) c = (a, b) \<Longrightarrow>
    bin_split n ((take_bit :: nat \<Rightarrow> int \<Rightarrow> int) m c) = ((take_bit :: nat \<Rightarrow> int \<Rightarrow> int) (m - n) a, b)"
  apply (drule sym)
  apply (simp add: drop_bit_take_bit ac_simps)
  apply (cases \<open>n \<le> m\<close>)
   apply simp_all
  done

lemma bin_split_trunc1:
  "bin_split n c = (a, b) \<Longrightarrow>
    bin_split n ((take_bit :: nat \<Rightarrow> int \<Rightarrow> int) m c) = ((take_bit :: nat \<Rightarrow> int \<Rightarrow> int) (m - n) a, (take_bit :: nat \<Rightarrow> int \<Rightarrow> int) m b)"
  apply (drule sym)
  apply (simp add: drop_bit_take_bit ac_simps)
  done

lemma bin_split_num: "bin_split n b = (b div 2 ^ n, b mod 2 ^ n)"
  by (simp add: drop_bit_eq_div take_bit_eq_mod)

lemmas bin_rsplit_aux_simps = bin_rsplit_aux.simps bin_rsplitl_aux.simps
lemmas rsplit_aux_simps = bin_rsplit_aux_simps

lemmas rsplit_aux_simp1s = rsplit_aux_simps [THEN th_if_simp1]

lemmas rsplit_aux_simp2ls = rsplit_aux_simps [THEN th_if_simp2]
\<comment> \<open>these safe to \<open>[simp add]\<close> as require calculating \<open>m - n\<close>\<close>
lemmas bin_rsplit_aux_simp2s [simp] = rsplit_aux_simp2ls [unfolded Let_def]
lemmas rbscl = bin_rsplit_aux_simp2s (2)

lemmas rsplit_aux_0_simps [simp] =
  rsplit_aux_simp1s [OF disjI1] rsplit_aux_simp1s [OF disjI2]

lemma bin_rsplit_aux_append: "bin_rsplit_aux n m c (bs @ cs) = bin_rsplit_aux n m c bs @ cs"
  apply (induct n m c bs rule: bin_rsplit_aux.induct)
  apply (subst bin_rsplit_aux.simps)
  apply (subst bin_rsplit_aux.simps)
  apply (clarsimp split: prod.split)
  done

lemma bin_rsplitl_aux_append: "bin_rsplitl_aux n m c (bs @ cs) = bin_rsplitl_aux n m c bs @ cs"
  apply (induct n m c bs rule: bin_rsplitl_aux.induct)
  apply (subst bin_rsplitl_aux.simps)
  apply (subst bin_rsplitl_aux.simps)
  apply (clarsimp split: prod.split)
  done

lemmas rsplit_aux_apps [where bs = "[]"] =
  bin_rsplit_aux_append bin_rsplitl_aux_append

lemmas rsplit_def_auxs = bin_rsplit_def bin_rsplitl_def

lemmas rsplit_aux_alts = rsplit_aux_apps
  [unfolded append_Nil rsplit_def_auxs [symmetric]]

lemma bin_split_minus: "0 < n \<Longrightarrow> bin_split (Suc (n - 1)) w = bin_split n w"
  by auto

lemma bin_split_pred_simp [simp]:
  "(0::nat) < numeral bin \<Longrightarrow>
    bin_split (numeral bin) w =
      (let (w1, w2) = bin_split (numeral bin - 1) ((\<lambda>k::int. k div 2) w)
       in (w1, of_bool (odd w) + 2 * w2))"
  by (simp add: take_bit_rec drop_bit_rec mod_2_eq_odd)

lemma bin_rsplit_aux_simp_alt:
  "bin_rsplit_aux n m c bs =
    (if m = 0 \<or> n = 0 then bs
     else let (a, b) = bin_split n c in bin_rsplit n (m - n, a) @ b # bs)"
  apply (simp add: bin_rsplit_aux.simps [of n m c bs])
  apply (subst rsplit_aux_alts)
  apply (simp add: bin_rsplit_def)
  done

lemmas bin_rsplit_simp_alt =
  trans [OF bin_rsplit_def bin_rsplit_aux_simp_alt]

lemmas bthrs = bin_rsplit_simp_alt [THEN [2] trans]

lemma bin_rsplit_size_sign' [rule_format]:
  "n > 0 \<Longrightarrow> rev sw = bin_rsplit n (nw, w) \<Longrightarrow> \<forall>v\<in>set sw. (take_bit :: nat \<Rightarrow> int \<Rightarrow> int) n v = v"
  apply (induct sw arbitrary: nw w)
   apply clarsimp
  apply clarsimp
  apply (drule bthrs)
  apply (simp (no_asm_use) add: Let_def split: prod.split_asm if_split_asm)
  apply clarify
  apply simp
  done

lemmas bin_rsplit_size_sign = bin_rsplit_size_sign' [OF asm_rl
  rev_rev_ident [THEN trans] set_rev [THEN equalityD2 [THEN subsetD]]]

lemma bin_nth_rsplit [rule_format] :
  "n > 0 \<Longrightarrow> m < n \<Longrightarrow>
    \<forall>w k nw.
      rev sw = bin_rsplit n (nw, w) \<longrightarrow>
      k < size sw \<longrightarrow> (bit :: int \<Rightarrow> nat \<Rightarrow> bool) (sw ! k) m = (bit :: int \<Rightarrow> nat \<Rightarrow> bool) w (k * n + m)"
  apply (induct sw)
   apply clarsimp
  apply clarsimp
  apply (drule bthrs)
  apply (simp (no_asm_use) add: Let_def split: prod.split_asm if_split_asm)
  apply (erule allE, erule impE, erule exI)
  apply (case_tac k)
   apply clarsimp
   prefer 2
   apply clarsimp
   apply (erule allE)
   apply (erule (1) impE)
   apply (simp add: bit_drop_bit_eq ac_simps)
  apply (simp add: bit_take_bit_iff ac_simps)
  done

lemma bin_rsplit_all: "0 < nw \<Longrightarrow> nw \<le> n \<Longrightarrow> bin_rsplit n (nw, w) = [(take_bit :: nat \<Rightarrow> int \<Rightarrow> int) n w]"
  by (auto simp: bin_rsplit_def rsplit_aux_simp2ls split: prod.split dest!: split_bintrunc)

lemma bin_rsplit_l [rule_format]:
  "\<forall>bin. bin_rsplitl n (m, bin) = bin_rsplit n (m, (take_bit :: nat \<Rightarrow> int \<Rightarrow> int) m bin)"
  apply (rule_tac a = "m" in wf_less_than [THEN wf_induct])
  apply (simp (no_asm) add: bin_rsplitl_def bin_rsplit_def)
  apply (rule allI)
  apply (subst bin_rsplitl_aux.simps)
  apply (subst bin_rsplit_aux.simps)
  apply (clarsimp simp: Let_def split: prod.split)
  apply (simp add: ac_simps)
  apply (subst rsplit_aux_alts(1))
  apply (subst rsplit_aux_alts(2))
  apply clarsimp
  unfolding bin_rsplit_def bin_rsplitl_def
  apply (simp add: drop_bit_take_bit)
  apply (case_tac \<open>x < n\<close>)
  apply (simp_all add: not_less min_def)
  done

lemma bin_rsplit_aux_len_le [rule_format] :
  "\<forall>ws m. n \<noteq> 0 \<longrightarrow> ws = bin_rsplit_aux n nw w bs \<longrightarrow>
    length ws \<le> m \<longleftrightarrow> nw + length bs * n \<le> m * n"
proof -
  have *: R
    if d: "i \<le> j \<or> m < j'"
    and R1: "i * k \<le> j * k \<Longrightarrow> R"
    and R2: "Suc m * k' \<le> j' * k' \<Longrightarrow> R"
    for i j j' k k' m :: nat and R
    using d
    apply safe
    apply (rule R1, erule mult_le_mono1)
    apply (rule R2, erule Suc_le_eq [THEN iffD2 [THEN mult_le_mono1]])
    done
  have **: "0 < sc \<Longrightarrow> sc - n + (n + lb * n) \<le> m * n \<longleftrightarrow> sc + lb * n \<le> m * n"
    for sc m n lb :: nat
    apply safe
     apply arith
    apply (case_tac "sc \<ge> n")
     apply arith
    apply (insert linorder_le_less_linear [of m lb])
    apply (erule_tac k=n and k'=n in *)
     apply arith
    apply simp
    done
  show ?thesis
    apply (induct n nw w bs rule: bin_rsplit_aux.induct)
    apply (subst bin_rsplit_aux.simps)
    apply (simp add: ** Let_def split: prod.split)
    done
qed

lemma bin_rsplit_len_le: "n \<noteq> 0 \<longrightarrow> ws = bin_rsplit n (nw, w) \<longrightarrow> length ws \<le> m \<longleftrightarrow> nw \<le> m * n"
  by (auto simp: bin_rsplit_def bin_rsplit_aux_len_le)

lemma bin_rsplit_aux_len:
  "n \<noteq> 0 \<Longrightarrow> length (bin_rsplit_aux n nw w cs) = (nw + n - 1) div n + length cs"
  apply (induct n nw w cs rule: bin_rsplit_aux.induct)
  apply (subst bin_rsplit_aux.simps)
  apply (clarsimp simp: Let_def split: prod.split)
  apply (erule thin_rl)
  apply (case_tac m)
   apply simp
  apply (case_tac "m \<le> n")
   apply (auto simp add: div_add_self2)
  done

lemma bin_rsplit_len: "n \<noteq> 0 \<Longrightarrow> length (bin_rsplit n (nw, w)) = (nw + n - 1) div n"
  by (auto simp: bin_rsplit_def bin_rsplit_aux_len)

lemma bin_rsplit_aux_len_indep:
  "n \<noteq> 0 \<Longrightarrow> length bs = length cs \<Longrightarrow>
    length (bin_rsplit_aux n nw v bs) =
    length (bin_rsplit_aux n nw w cs)"
proof (induct n nw w cs arbitrary: v bs rule: bin_rsplit_aux.induct)
  case (1 n m w cs v bs)
  show ?case
  proof (cases "m = 0")
    case True
    with \<open>length bs = length cs\<close> show ?thesis by simp
  next
    case False
    from "1.hyps" [of \<open>bin_split n w\<close> \<open>drop_bit n w\<close> \<open>take_bit n w\<close>] \<open>m \<noteq> 0\<close> \<open>n \<noteq> 0\<close>
    have hyp: "\<And>v bs. length bs = Suc (length cs) \<Longrightarrow>
      length (bin_rsplit_aux n (m - n) v bs) =
      length (bin_rsplit_aux n (m - n) (drop_bit n w) (take_bit n w # cs))"
      using bin_rsplit_aux_len by fastforce
    from \<open>length bs = length cs\<close> \<open>n \<noteq> 0\<close> show ?thesis
      by (auto simp add: bin_rsplit_aux_simp_alt Let_def bin_rsplit_len split: prod.split)
  qed
qed

lemma bin_rsplit_len_indep:
  "n \<noteq> 0 \<Longrightarrow> length (bin_rsplit n (nw, v)) = length (bin_rsplit n (nw, w))"
  apply (unfold bin_rsplit_def)
  apply (simp (no_asm))
  apply (erule bin_rsplit_aux_len_indep)
  apply (rule refl)
  done

lemma split_uint_lem: "bin_split n (uint w) = (a, b) \<Longrightarrow>
    a = take_bit (LENGTH('a) - n) a \<and> b = take_bit (LENGTH('a)) b"
  for w :: "'a::len word"
  by transfer (simp add: drop_bit_take_bit ac_simps)


definition word_rsplit :: "'a::len word \<Rightarrow> 'b::len word list"
  where "word_rsplit w = map word_of_int (bin_rsplit LENGTH('b) (LENGTH('a), uint w))"

lemma word_rsplit_no:
  "(word_rsplit (numeral bin :: 'b::len word) :: 'a word list) =
    map word_of_int (bin_rsplit (LENGTH('a::len))
      (LENGTH('b), take_bit (LENGTH('b)) (numeral bin)))"
  by (simp add: word_rsplit_def of_nat_take_bit)

lemmas word_rsplit_no_cl [simp] = word_rsplit_no
  [unfolded bin_rsplitl_def bin_rsplit_l [symmetric]]

text \<open>
  This odd result arises from the fact that the statement of the
  result implies that the decoded words are of the same type,
  and therefore of the same length, as the original word.\<close>

lemma word_rsplit_same: "word_rsplit w = [w]"
  apply (simp add: word_rsplit_def bin_rsplit_all)
  apply transfer
  apply simp
  done

lemma word_rsplit_empty_iff_size: "word_rsplit w = [] \<longleftrightarrow> size w = 0"
  by (simp add: word_rsplit_def bin_rsplit_def word_size bin_rsplit_aux_simp_alt Let_def
      split: prod.split)

lemma test_bit_rsplit:
  "sw = word_rsplit w \<Longrightarrow> m < size (hd sw) \<Longrightarrow>
    k < length sw \<Longrightarrow> bit (rev sw ! k) m = bit w (k * size (hd sw) + m)"
  for sw :: "'a::len word list"
  apply (unfold word_rsplit_def word_test_bit_def)
  apply (rule trans)
   apply (rule_tac f = "\<lambda>x. bit x m" in arg_cong)
   apply (rule nth_map [symmetric])
   apply simp
  apply (rule bin_nth_rsplit)
     apply simp_all
  apply (simp add : word_size rev_map)
  apply (rule trans)
   defer
   apply (rule map_ident [THEN fun_cong])
  apply (rule refl [THEN map_cong])
  apply (simp add: unsigned_of_int take_bit_int_eq_self_iff)
  using bin_rsplit_size_sign take_bit_int_eq_self_iff by blast

lemma test_bit_rsplit_alt:
  \<open>bit ((word_rsplit w  :: 'b::len word list) ! i) m \<longleftrightarrow>
    bit w ((length (word_rsplit w :: 'b::len word list) - Suc i) * size (hd (word_rsplit w :: 'b::len word list)) + m)\<close>
  if \<open>i < length (word_rsplit w :: 'b::len word list)\<close> \<open>m < size (hd (word_rsplit w :: 'b::len word list))\<close> \<open>0 < length (word_rsplit w :: 'b::len word list)\<close>
  for w :: \<open>'a::len word\<close>
  apply (rule trans)
   apply (rule test_bit_cong)
   apply (rule rev_nth [of _ \<open>rev (word_rsplit w)\<close>, simplified rev_rev_ident])
  apply simp
   apply (rule that(1))
  apply simp
  apply (rule test_bit_rsplit)
    apply (rule refl)
  apply (rule asm_rl)
   apply (rule that(2))
  apply (rule diff_Suc_less)
  apply (rule that(3))
  done

lemma word_rsplit_len_indep [OF refl refl refl refl]:
  "[u,v] = p \<Longrightarrow> [su,sv] = q \<Longrightarrow> word_rsplit u = su \<Longrightarrow>
    word_rsplit v = sv \<Longrightarrow> length su = length sv"
  by (auto simp: word_rsplit_def bin_rsplit_len_indep)

lemma length_word_rsplit_size:
  "n = LENGTH('a::len) \<Longrightarrow>
    length (word_rsplit w :: 'a word list) \<le> m \<longleftrightarrow> size w \<le> m * n"
  by (auto simp: word_rsplit_def word_size bin_rsplit_len_le)

lemmas length_word_rsplit_lt_size =
  length_word_rsplit_size [unfolded Not_eq_iff linorder_not_less [symmetric]]

lemma length_word_rsplit_exp_size:
  "n = LENGTH('a::len) \<Longrightarrow>
    length (word_rsplit w :: 'a word list) = (size w + n - 1) div n"
  by (auto simp: word_rsplit_def word_size bin_rsplit_len)

lemma length_word_rsplit_even_size:
  "n = LENGTH('a::len) \<Longrightarrow> size w = m * n \<Longrightarrow>
    length (word_rsplit w :: 'a word list) = m"
  by (cases \<open>LENGTH('a)\<close>) (simp_all add: length_word_rsplit_exp_size div_nat_eqI)

lemmas length_word_rsplit_exp_size' = refl [THEN length_word_rsplit_exp_size]

\<comment> \<open>alternative proof of \<open>word_rcat_rsplit\<close>\<close>
lemmas tdle = times_div_less_eq_dividend
lemmas dtle = xtrans(4) [OF tdle mult.commute]

lemma word_rcat_rsplit: "word_rcat (word_rsplit w) = w"
  apply (rule word_eqI)
  apply (clarsimp simp: test_bit_rcat word_size)
  apply (subst refl [THEN test_bit_rsplit])
    apply (simp_all add: word_size
      refl [THEN length_word_rsplit_size [simplified not_less [symmetric], simplified]])
   apply safe
   apply (erule xtrans(7), rule dtle)+
  done

lemma size_word_rsplit_rcat_size:
  "word_rcat ws = frcw \<Longrightarrow> size frcw = length ws * LENGTH('a)
    \<Longrightarrow> length (word_rsplit frcw::'a word list) = length ws"
  for ws :: "'a::len word list" and frcw :: "'b::len word"
  by (cases \<open>LENGTH('a)\<close>) (simp_all add: word_size length_word_rsplit_exp_size' div_nat_eqI)

lemma word_rsplit_rcat_size [OF refl]:
  "word_rcat ws = frcw \<Longrightarrow>
    size frcw = length ws * LENGTH('a) \<Longrightarrow> word_rsplit frcw = ws"
  for ws :: "'a::len word list"
  apply (frule size_word_rsplit_rcat_size, assumption)
  apply (clarsimp simp add : word_size)
  apply (rule nth_equalityI, assumption)
  apply clarsimp
  apply (rule word_eqI [rule_format])
  apply (rule trans)
   apply (rule test_bit_rsplit_alt)
     apply (clarsimp simp: word_size)+
  apply (rule trans)
   apply (rule test_bit_rcat [OF refl refl])
  apply (simp add: word_size)
  apply (subst rev_nth)
   apply arith
  apply (simp add: le0 [THEN [2] xtrans(7), THEN diff_Suc_less])
  apply safe
  apply (simp add: diff_mult_distrib)
   apply (cases "size ws")
    apply simp_all
  done

lemma word_rsplit_upt:
  "size x = LENGTH('a :: len) * n \<Longrightarrow> n \<noteq> 0
    \<Longrightarrow> word_rsplit x = map (\<lambda>i. ucast (x >> (i * LENGTH('a))) :: 'a word) (rev [0 ..< n])"
  apply (subgoal_tac "length (word_rsplit x :: 'a word list) = n")
   apply (rule nth_equalityI, simp)
   apply (intro allI word_eqI impI)
   apply (simp add: test_bit_rsplit_alt word_size)
   apply (simp add: nth_ucast bit_simps rev_nth field_simps)
  apply (simp add: length_word_rsplit_exp_size word_size)
  apply (subst diff_add_assoc)
   apply (simp flip: less_eq_Suc_le)
  apply simp
  done

end