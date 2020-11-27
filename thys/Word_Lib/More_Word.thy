
section \<open>Lemmas on words\<close>

theory More_Word
  imports
    "HOL-Library.Word"
    More_Arithmetic
    More_Divides
begin

lemma Suc_0_lt_2p_len_of: "Suc 0 < 2 ^ LENGTH('a :: len)"
  by (metis One_nat_def len_gt_0 lessI numeral_2_eq_2 one_less_power)

lemma unat_power_lower [simp]:
  "unat ((2::'a::len word) ^ n) = 2 ^ n" if "n < LENGTH('a::len)"
  using that by transfer simp

lemma unat_p2: "n < LENGTH('a :: len) \<Longrightarrow> unat (2 ^ n :: 'a word) = 2 ^ n"
  by (fact unat_power_lower)

lemma word_div_lt_eq_0:
  "x < y \<Longrightarrow> x div y = 0" for x :: "'a :: len word"
  by transfer simp

lemma word_div_eq_1_iff: "n div m = 1 \<longleftrightarrow> n \<ge> m \<and> unat n < 2 * unat (m :: 'a :: len word)"
  apply (simp only: word_arith_nat_defs word_le_nat_alt word_of_nat_eq_iff flip: nat_div_eq_Suc_0_iff)
  apply (simp flip: unat_div unsigned_take_bit_eq)
  done

lemma shiftl_power:
  "(shiftl1 ^^ x) (y::'a::len word) = 2 ^ x * y"
  apply (induct x)
   apply simp
  apply (simp add: shiftl1_2t)
  done

lemma AND_twice [simp]:
  "(w AND m) AND m = w AND m"
  by (fact and.right_idem)

lemma word_combine_masks:
  "w AND m = z \<Longrightarrow> w AND m' = z' \<Longrightarrow> w AND (m OR m') = (z OR z')"
  for w m m' z z' :: \<open>'a::len word\<close>
  by (simp add: bit.conj_disj_distrib)

lemma p2_gt_0:
  "(0 < (2 ^ n :: 'a :: len word)) = (n < LENGTH('a))"
  by (simp add : word_gt_0 not_le)

lemma uint_2p_alt:
  \<open>n < LENGTH('a::len) \<Longrightarrow> uint ((2::'a::len word) ^ n) = 2 ^ n\<close>
  using p2_gt_0 [of n, where ?'a = 'a] by (simp add: uint_2p) 

lemma p2_eq_0:
  \<open>(2::'a::len word) ^ n = 0 \<longleftrightarrow> LENGTH('a::len) \<le> n\<close>
  by (fact exp_eq_zero_iff)

lemma p2len:
  \<open>(2 :: 'a word) ^ LENGTH('a::len) = 0\<close>
  by simp

lemma neg_mask_is_div:
  "w AND NOT (mask n) = (w div 2^n) * 2^n"
  for w :: \<open>'a::len word\<close>
  by (rule bit_word_eqI)
    (auto simp add: bit_simps simp flip: push_bit_eq_mult drop_bit_eq_div)

lemma neg_mask_is_div':
  "n < size w \<Longrightarrow> w AND NOT (mask n) = ((w div (2 ^ n)) * (2 ^ n))"
  for w :: \<open>'a::len word\<close>
  by (rule neg_mask_is_div)

lemma and_mask_arith:
  "w AND mask n = (w * 2^(size w - n)) div 2^(size w - n)"
  for w :: \<open>'a::len word\<close>
  by (rule bit_word_eqI)
    (auto simp add: bit_simps word_size simp flip: push_bit_eq_mult drop_bit_eq_div)

lemma and_mask_arith':
  "0 < n \<Longrightarrow> w AND mask n = (w * 2^(size w - n)) div 2^(size w - n)"
  for w :: \<open>'a::len word\<close>
  by (rule and_mask_arith)
  
lemma mask_2pm1: "mask n = 2 ^ n - (1 :: 'a::len word)"
  by (fact mask_eq_decr_exp)

lemma add_mask_fold:
  "x + 2 ^ n - 1 = x + mask n"
  for x :: \<open>'a::len word\<close>
  by (simp add: mask_eq_decr_exp)

lemma word_and_mask_le_2pm1: "w AND mask n \<le> 2 ^ n - 1"
  for w :: \<open>'a::len word\<close>
  by (simp add: mask_2pm1[symmetric] word_and_le1)

lemma is_aligned_AND_less_0:
  "u AND mask n = 0 \<Longrightarrow> v < 2^n \<Longrightarrow> u AND v = 0"
  for u v :: \<open>'a::len word\<close>
  apply (drule less_mask_eq)
  apply (simp flip: take_bit_eq_mask)
  apply (simp add: bit_eq_iff)
  apply (auto simp add: bit_simps)
  done

lemma le_shiftr1:
  \<open>shiftr1 u \<le> shiftr1 v\<close> if \<open>u \<le> v\<close>
using that proof transfer
  fix k l :: int
  assume \<open>take_bit LENGTH('a) k \<le> take_bit LENGTH('a) l\<close>
  then have \<open>take_bit LENGTH('a) (drop_bit 1 (take_bit LENGTH('a) k))
    \<le> take_bit LENGTH('a) (drop_bit 1 (take_bit LENGTH('a) l))\<close>
    apply (simp add: take_bit_drop_bit min_def)
    apply (simp add: drop_bit_eq_div)
    done
  then show \<open>take_bit LENGTH('a) (take_bit LENGTH('a) k div 2)
    \<le> take_bit LENGTH('a) (take_bit LENGTH('a) l div 2)\<close>
    by (simp add: drop_bit_eq_div)
qed

lemma and_mask_eq_iff_le_mask:
  \<open>w AND mask n = w \<longleftrightarrow> w \<le> mask n\<close>
  for w :: \<open>'a::len word\<close>
  apply (simp flip: take_bit_eq_mask)
  apply (cases \<open>n \<ge> LENGTH('a)\<close>; transfer)
   apply (simp_all add: not_le min_def)
   apply (simp_all add: mask_eq_exp_minus_1)
  apply auto
   apply (metis take_bit_int_less_exp)
  apply (metis min_def nat_less_le take_bit_int_eq_self_iff take_bit_take_bit)
  done

lemma less_eq_mask_iff_take_bit_eq_self:
  \<open>w \<le> mask n \<longleftrightarrow> take_bit n w = w\<close>
  for w :: \<open>'a::len word\<close>
  by (simp add: and_mask_eq_iff_le_mask take_bit_eq_mask)

lemma NOT_eq:
  "NOT (x :: 'a :: len word) = - x - 1"
  apply (cut_tac x = "x" in word_add_not)
  apply (drule add.commute [THEN trans])
  apply (drule eq_diff_eq [THEN iffD2])
  by simp

lemma NOT_mask: "NOT (mask n :: 'a::len word) = - (2 ^ n)"
  by (simp add : NOT_eq mask_2pm1)

lemma le_m1_iff_lt: "(x > (0 :: 'a :: len word)) = ((y \<le> x - 1) = (y < x))"
  by uint_arith

lemma gt0_iff_gem1:
  \<open>0 < x \<longleftrightarrow> x - 1 < x\<close>
  for x :: \<open>'a::len word\<close>
  by (metis add.right_neutral diff_add_cancel less_irrefl measure_unat unat_arith_simps(2) word_neq_0_conv word_sub_less_iff)

lemma power_2_ge_iff:
  \<open>2 ^ n - (1 :: 'a::len word) < 2 ^ n \<longleftrightarrow> n < LENGTH('a)\<close>
  using gt0_iff_gem1 p2_gt_0 by blast

lemma le_mask_iff_lt_2n:
  "n < len_of TYPE ('a) = (((w :: 'a :: len word) \<le> mask n) = (w < 2 ^ n))"
  unfolding mask_2pm1 by (rule trans [OF p2_gt_0 [THEN sym] le_m1_iff_lt])

lemma mask_lt_2pn:
  \<open>n < LENGTH('a) \<Longrightarrow> mask n < (2 :: 'a::len word) ^ n\<close>
  by (simp add: mask_eq_exp_minus_1 power_2_ge_iff)

lemma word_unat_power:
  "(2 :: 'a :: len word) ^ n = of_nat (2 ^ n)"
  by simp

lemma of_nat_mono_maybe:
  assumes xlt: "x < 2 ^ len_of TYPE ('a)"
  shows   "y < x \<Longrightarrow> of_nat y < (of_nat x :: 'a :: len word)"
  apply (subst word_less_nat_alt)
  apply (subst unat_of_nat)+
  apply (subst mod_less)
   apply (erule order_less_trans [OF _ xlt])
  apply (subst mod_less [OF xlt])
  apply assumption
  done

lemma word_and_max_word:
  fixes a::"'a::len word"
  shows "x = max_word \<Longrightarrow> a AND x = a"
  by simp

lemma word_and_full_mask_simp:
  \<open>x AND mask LENGTH('a) = x\<close> for x :: \<open>'a::len word\<close>
proof (rule bit_eqI)
  fix n
  assume \<open>2 ^ n \<noteq> (0 :: 'a word)\<close>
  then have \<open>n < LENGTH('a)\<close>
    by simp
  then show \<open>bit (x AND Bit_Operations.mask LENGTH('a)) n \<longleftrightarrow> bit x n\<close>
    by (simp add: bit_and_iff bit_mask_iff)
qed

lemma of_int_uint:
  "of_int (uint x) = x"
  by (fact word_of_int_uint)

corollary word_plus_and_or_coroll:
  "x AND y = 0 \<Longrightarrow> x + y = x OR y"
  for x y :: \<open>'a::len word\<close>
  using word_plus_and_or[where x=x and y=y]
  by simp

corollary word_plus_and_or_coroll2:
  "(x AND w) + (x AND NOT w) = x"
  for x w :: \<open>'a::len word\<close>
  apply (subst disjunctive_add)
   apply (simp add: bit_simps)
  apply (simp flip: bit.conj_disj_distrib)
  done

lemma nat_mask_eq:
  \<open>nat (mask n) = mask n\<close>
  by (simp add: nat_eq_iff of_nat_mask_eq)

lemma unat_mask_eq:
  \<open>unat (mask n :: 'a::len word) = mask (min LENGTH('a) n)\<close>
  by transfer (simp add: nat_mask_eq)

lemma word_plus_mono_left:
  fixes x :: "'a :: len word"
  shows "\<lbrakk>y \<le> z; x \<le> x + z\<rbrakk> \<Longrightarrow> y + x \<le> z + x"
  by unat_arith

lemma less_Suc_unat_less_bound:
  "n < Suc (unat (x :: 'a :: len word)) \<Longrightarrow> n < 2 ^ LENGTH('a)"
  by (auto elim!: order_less_le_trans intro: Suc_leI)

lemma up_ucast_inj:
  "\<lbrakk> ucast x = (ucast y::'b::len word); LENGTH('a) \<le> len_of TYPE ('b) \<rbrakk> \<Longrightarrow> x = (y::'a::len word)"
  by transfer (simp add: min_def split: if_splits)

lemmas ucast_up_inj = up_ucast_inj

lemma up_ucast_inj_eq:
  "LENGTH('a) \<le> len_of TYPE ('b) \<Longrightarrow> (ucast x = (ucast y::'b::len word)) = (x = (y::'a::len word))"
  by (fastforce dest: up_ucast_inj)

lemma no_plus_overflow_neg:
  "(x :: 'a :: len word) < -y \<Longrightarrow> x \<le> x + y"
  by (metis diff_minus_eq_add less_imp_le sub_wrap_lt)

lemma ucast_ucast_eq:
  "\<lbrakk> ucast x = (ucast (ucast y::'a word)::'c::len word); LENGTH('a) \<le> LENGTH('b);
     LENGTH('b) \<le> LENGTH('c) \<rbrakk> \<Longrightarrow>
   x = ucast y" for x :: "'a::len word" and y :: "'b::len word"
  apply transfer
  apply (cases \<open>LENGTH('c) = LENGTH('a)\<close>)
   apply (auto simp add: min_def)
  done

lemma ucast_0_I:
  "x = 0 \<Longrightarrow> ucast x = 0"
  by simp

lemma word_add_offset_less:
  fixes x :: "'a :: len word"
  assumes yv: "y < 2 ^ n"
  and     xv: "x < 2 ^ m"
  and     mnv: "sz < LENGTH('a :: len)"
  and    xv': "x < 2 ^ (LENGTH('a :: len) - n)"
  and     mn: "sz = m + n"
  shows   "x * 2 ^ n + y < 2 ^ sz"
proof (subst mn)
  from mnv mn have nv: "n < LENGTH('a)" and mv: "m < LENGTH('a)"  by auto

  have uy: "unat y < 2 ^ n"
    by (rule order_less_le_trans [OF unat_mono [OF yv] order_eq_refl],
        rule unat_power_lower[OF nv])

  have ux: "unat x < 2 ^ m"
    by (rule order_less_le_trans [OF unat_mono [OF xv] order_eq_refl],
        rule unat_power_lower[OF mv])

  then show "x * 2 ^ n + y < 2 ^ (m + n)" using ux uy nv mnv xv'
    apply (subst word_less_nat_alt)
    apply (subst unat_word_ariths)+
    apply (subst mod_less)
     apply simp
     apply (subst mult.commute)
     apply (rule nat_less_power_trans [OF _ order_less_imp_le [OF nv]])
     apply (rule order_less_le_trans [OF unat_mono [OF xv']])
     apply (cases "n = 0"; simp)
    apply (subst unat_power_lower[OF nv])
    apply (subst mod_less)
     apply (erule order_less_le_trans [OF nat_add_offset_less], assumption)
      apply (rule mn)
     apply simp
    apply (simp add: mn mnv)
    apply (erule nat_add_offset_less; simp)
    done
qed

lemma word_less_power_trans:
  fixes n :: "'a :: len word"
  assumes nv: "n < 2 ^ (m - k)"
  and     kv: "k \<le> m"
  and     mv: "m < len_of TYPE ('a)"
  shows "2 ^ k * n < 2 ^ m"
  using nv kv mv
  apply -
  apply (subst word_less_nat_alt)
  apply (subst unat_word_ariths)
  apply (subst mod_less)
   apply simp
   apply (rule nat_less_power_trans)
    apply (erule order_less_trans [OF unat_mono])
    apply simp
   apply simp
  apply simp
  apply (rule nat_less_power_trans)
   apply (subst unat_power_lower[where 'a = 'a, symmetric])
    apply simp
   apply (erule unat_mono)
  apply simp
  done

lemma  word_less_power_trans2:
  fixes n :: "'a::len word"
  shows "\<lbrakk>n < 2 ^ (m - k); k \<le> m; m < LENGTH('a)\<rbrakk> \<Longrightarrow> n * 2 ^ k < 2 ^ m"
  by (subst field_simps, rule word_less_power_trans)

lemma Suc_unat_diff_1:
  fixes x :: "'a :: len word"
  assumes lt: "1 \<le> x"
  shows "Suc (unat (x - 1)) = unat x"
proof -
  have "0 < unat x"
    by (rule order_less_le_trans [where y = 1], simp, subst unat_1 [symmetric],
        rule iffD1 [OF word_le_nat_alt lt])

  then show ?thesis
    by ((subst unat_sub [OF lt])+, simp only:  unat_1)
qed

lemma word_eq_unatI:
  \<open>v = w\<close> if \<open>unat v = unat w\<close>
  using that by transfer (simp add: nat_eq_iff)

lemma word_div_sub:
  fixes x :: "'a :: len word"
  assumes yx: "y \<le> x"
  and     y0: "0 < y"
  shows "(x - y) div y = x div y - 1"
  apply (rule word_eq_unatI)
  apply (subst unat_div)
  apply (subst unat_sub [OF yx])
  apply (subst unat_sub)
   apply (subst word_le_nat_alt)
   apply (subst unat_div)
   apply (subst le_div_geq)
     apply (rule order_le_less_trans [OF _ unat_mono [OF y0]])
     apply simp
    apply (subst word_le_nat_alt [symmetric], rule yx)
   apply simp
  apply (subst unat_div)
  apply (subst le_div_geq [OF _ iffD1 [OF word_le_nat_alt yx]])
   apply (rule order_le_less_trans [OF _ unat_mono [OF y0]])
   apply simp
  apply simp
  done

lemma word_mult_less_mono1:
  fixes i :: "'a :: len word"
  assumes ij: "i < j"
  and    knz: "0 < k"
  and    ujk: "unat j * unat k < 2 ^ len_of TYPE ('a)"
  shows  "i * k < j * k"
proof -
  from ij ujk knz have jk: "unat i * unat k < 2 ^ len_of TYPE ('a)"
    by (auto intro: order_less_subst2 simp: word_less_nat_alt elim: mult_less_mono1)

  then show ?thesis using ujk knz ij
    by (auto simp: word_less_nat_alt iffD1 [OF unat_mult_lem])
qed

lemma word_mult_less_dest:
  fixes i :: "'a :: len word"
  assumes ij: "i * k < j * k"
  and    uik: "unat i * unat k < 2 ^ len_of TYPE ('a)"
  and    ujk: "unat j * unat k < 2 ^ len_of TYPE ('a)"
  shows  "i < j"
  using uik ujk ij
  by (auto simp: word_less_nat_alt iffD1 [OF unat_mult_lem] elim: mult_less_mono1)

lemma word_mult_less_cancel:
  fixes k :: "'a :: len word"
  assumes knz: "0 < k"
  and    uik: "unat i * unat k < 2 ^ len_of TYPE ('a)"
  and    ujk: "unat j * unat k < 2 ^ len_of TYPE ('a)"
  shows "(i * k < j * k) = (i < j)"
  by (rule iffI [OF word_mult_less_dest [OF _ uik ujk] word_mult_less_mono1 [OF _ knz ujk]])

lemma Suc_div_unat_helper:
  assumes szv: "sz < LENGTH('a :: len)"
  and   usszv: "us \<le> sz"
  shows "2 ^ (sz - us) = Suc (unat (((2::'a :: len word) ^ sz - 1) div 2 ^ us))"
proof -
  note usv = order_le_less_trans [OF usszv szv]

  from usszv obtain q where qv: "sz = us + q" by (auto simp: le_iff_add)

  have "Suc (unat (((2:: 'a word) ^ sz - 1) div 2 ^ us)) =
    (2 ^ us + unat ((2:: 'a word) ^ sz - 1)) div 2 ^ us"
    apply (subst unat_div unat_power_lower[OF usv])+
    apply (subst div_add_self1, simp+)
    done

  also have "\<dots> = ((2 ^ us - 1) + 2 ^ sz) div 2 ^ us" using szv
    by (simp add: unat_minus_one)

  also have "\<dots> = 2 ^ q + ((2 ^ us - 1) div 2 ^ us)"
    apply (subst qv)
    apply (subst power_add)
    apply (subst div_mult_self2; simp)
    done

  also have "\<dots> = 2 ^ (sz - us)" using qv by simp

  finally show ?thesis ..
qed

lemma enum_word_nth_eq:
  \<open>(Enum.enum :: 'a::len word list) ! n = word_of_nat n\<close>
    if \<open>n < 2 ^ LENGTH('a)\<close>
    for n
  using that by (simp add: enum_word_def)

lemma length_enum_word_eq:
  \<open>length (Enum.enum :: 'a::len word list) = 2 ^ LENGTH('a)\<close>
  by (simp add: enum_word_def)

lemma unat_lt2p [iff]:
  \<open>unat x < 2 ^ LENGTH('a)\<close> for x :: \<open>'a::len word\<close>
  by transfer simp

lemma of_nat_unat [simp]:
  "of_nat \<circ> unat = id"
  by (rule ext, simp)

lemma Suc_unat_minus_one [simp]:
  "x \<noteq> 0 \<Longrightarrow> Suc (unat (x - 1)) = unat x"
  by (metis Suc_diff_1 unat_gt_0 unat_minus_one)

lemma word_add_le_dest:
  fixes i :: "'a :: len word"
  assumes le: "i + k \<le> j + k"
  and    uik: "unat i + unat k < 2 ^ len_of TYPE ('a)"
  and    ujk: "unat j + unat k < 2 ^ len_of TYPE ('a)"
  shows  "i \<le> j"
  using uik ujk le
  by (auto simp: word_le_nat_alt iffD1 [OF unat_add_lem] elim: add_le_mono1)

lemma word_add_le_mono1:
  fixes i :: "'a :: len word"
  assumes ij: "i \<le> j"
  and    ujk: "unat j + unat k < 2 ^ len_of TYPE ('a)"
  shows  "i + k \<le> j + k"
proof -
  from ij ujk have jk: "unat i + unat k < 2 ^ len_of TYPE ('a)"
    by (auto elim: order_le_less_subst2 simp: word_le_nat_alt elim: add_le_mono1)

  then show ?thesis using ujk ij
    by (auto simp: word_le_nat_alt iffD1 [OF unat_add_lem])
qed

lemma word_add_le_mono2:
  fixes i :: "'a :: len word"
  shows "\<lbrakk>i \<le> j; unat j + unat k < 2 ^ LENGTH('a)\<rbrakk> \<Longrightarrow> k + i \<le> k + j"
  by (subst field_simps, subst field_simps, erule (1) word_add_le_mono1)

lemma word_add_le_iff:
  fixes i :: "'a :: len word"
  assumes uik: "unat i + unat k < 2 ^ len_of TYPE ('a)"
  and     ujk: "unat j + unat k < 2 ^ len_of TYPE ('a)"
  shows  "(i + k \<le> j + k) = (i \<le> j)"
proof
  assume "i \<le> j"
  show "i + k \<le> j + k" by (rule word_add_le_mono1) fact+
next
  assume "i + k \<le> j + k"
  show "i \<le> j" by (rule word_add_le_dest) fact+
qed

lemma word_add_less_mono1:
  fixes i :: "'a :: len word"
  assumes ij: "i < j"
  and    ujk: "unat j + unat k < 2 ^ len_of TYPE ('a)"
  shows  "i + k < j + k"
proof -
  from ij ujk have jk: "unat i + unat k < 2 ^ len_of TYPE ('a)"
    by (auto elim: order_le_less_subst2 simp: word_less_nat_alt elim: add_less_mono1)

  then show ?thesis using ujk ij
    by (auto simp: word_less_nat_alt iffD1 [OF unat_add_lem])
qed

lemma word_add_less_dest:
  fixes i :: "'a :: len word"
  assumes le: "i + k < j + k"
  and    uik: "unat i + unat k < 2 ^ len_of TYPE ('a)"
  and    ujk: "unat j + unat k < 2 ^ len_of TYPE ('a)"
  shows  "i < j"
  using uik ujk le
  by (auto simp: word_less_nat_alt iffD1 [OF unat_add_lem] elim: add_less_mono1)

lemma word_add_less_iff:
  fixes i :: "'a :: len word"
  assumes uik: "unat i + unat k < 2 ^ len_of TYPE ('a)"
  and     ujk: "unat j + unat k < 2 ^ len_of TYPE ('a)"
  shows  "(i + k < j + k) = (i < j)"
proof
  assume "i < j"
  show "i + k < j + k" by (rule word_add_less_mono1) fact+
next
  assume "i + k < j + k"
  show "i < j" by (rule word_add_less_dest) fact+
qed

lemma word_mult_less_iff:
  fixes i :: "'a :: len word"
  assumes knz: "0 < k"
  and     uik: "unat i * unat k < 2 ^ len_of TYPE ('a)"
  and     ujk: "unat j * unat k < 2 ^ len_of TYPE ('a)"
  shows  "(i * k < j * k) = (i < j)"
  using assms by (rule word_mult_less_cancel)

lemma word_le_imp_diff_le:
  fixes n :: "'a::len word"
  shows "\<lbrakk>k \<le> n; n \<le> m\<rbrakk> \<Longrightarrow> n - k \<le> m"
  by (auto simp: unat_sub word_le_nat_alt)

lemma word_less_imp_diff_less:
  fixes n :: "'a::len word"
  shows "\<lbrakk>k \<le> n; n < m\<rbrakk> \<Longrightarrow> n - k < m"
  by (clarsimp simp: unat_sub word_less_nat_alt
             intro!: less_imp_diff_less)

lemma word_mult_le_mono1:
  fixes i :: "'a :: len word"
  assumes ij: "i \<le> j"
  and    knz: "0 < k"
  and    ujk: "unat j * unat k < 2 ^ len_of TYPE ('a)"
  shows  "i * k \<le> j * k"
proof -
  from ij ujk knz have jk: "unat i * unat k < 2 ^ len_of TYPE ('a)"
    by (auto elim: order_le_less_subst2 simp: word_le_nat_alt elim: mult_le_mono1)

  then show ?thesis using ujk knz ij
    by (auto simp: word_le_nat_alt iffD1 [OF unat_mult_lem])
qed

lemma word_mult_le_iff:
  fixes i :: "'a :: len word"
  assumes knz: "0 < k"
  and     uik: "unat i * unat k < 2 ^ len_of TYPE ('a)"
  and     ujk: "unat j * unat k < 2 ^ len_of TYPE ('a)"
  shows  "(i * k \<le> j * k) = (i \<le> j)"
proof
  assume "i \<le> j"
  show "i * k \<le> j * k" by (rule word_mult_le_mono1) fact+
next
  assume p: "i * k \<le> j * k"

  have "0 < unat k" using knz by (simp add: word_less_nat_alt)
  then show "i \<le> j" using p
    by (clarsimp simp: word_le_nat_alt iffD1 [OF unat_mult_lem uik]
      iffD1 [OF unat_mult_lem ujk])
qed

lemma word_diff_less:
  fixes n :: "'a :: len word"
  shows "\<lbrakk>0 < n; 0 < m; n \<le> m\<rbrakk> \<Longrightarrow> m - n < m"
  apply (subst word_less_nat_alt)
  apply (subst unat_sub)
   apply assumption
  apply (rule diff_less)
   apply (simp_all add: word_less_nat_alt)
  done

lemma word_add_increasing:
  fixes x :: "'a :: len word"
  shows "\<lbrakk> p + w \<le> x; p \<le> p + w \<rbrakk> \<Longrightarrow> p \<le> x"
  by unat_arith

lemma word_random:
  fixes x :: "'a :: len word"
  shows "\<lbrakk> p \<le> p + x'; x \<le> x' \<rbrakk> \<Longrightarrow> p \<le> p + x"
  by unat_arith

lemma word_sub_mono:
  "\<lbrakk> a \<le> c; d \<le> b; a - b \<le> a; c - d \<le> c \<rbrakk>
    \<Longrightarrow> (a - b) \<le> (c - d :: 'a :: len word)"
  by unat_arith

lemma power_not_zero:
  "n < LENGTH('a::len) \<Longrightarrow> (2 :: 'a word) ^ n \<noteq> 0"
  by (metis p2_gt_0 word_neq_0_conv)

lemma word_gt_a_gt_0:
  "a < n \<Longrightarrow> (0 :: 'a::len word) < n"
  apply (case_tac "n = 0")
   apply clarsimp
  apply (clarsimp simp: word_neq_0_conv)
  done

lemma word_power_less_1 [simp]:
  "sz < LENGTH('a::len) \<Longrightarrow> (2::'a word) ^ sz - 1 < 2 ^ sz"
  apply (simp add: word_less_nat_alt)
  apply (subst unat_minus_one)
  apply simp_all
  done

lemma word_sub_1_le:
  "x \<noteq> 0 \<Longrightarrow> x - 1 \<le> (x :: ('a :: len) word)"
  apply (subst no_ulen_sub)
  apply simp
  apply (cases "uint x = 0")
   apply (simp add: uint_0_iff)
  apply (insert uint_ge_0[where x=x])
  apply arith
  done

lemma push_bit_word_eq_nonzero:
  \<open>push_bit n w \<noteq> 0\<close> if \<open>w < 2 ^ m\<close> \<open>m + n < LENGTH('a)\<close> \<open>w \<noteq> 0\<close>
    for w :: \<open>'a::len word\<close>
  using that
  apply (simp only: word_neq_0_conv word_less_nat_alt
                    mod_0 unat_word_ariths
                    unat_power_lower word_le_nat_alt)
  apply (metis add_diff_cancel_right' gr0I gr_implies_not0 less_or_eq_imp_le min_def push_bit_eq_0_iff take_bit_nat_eq_self_iff take_bit_push_bit take_bit_take_bit unsigned_push_bit_eq)
  done

lemma unat_less_power:
  fixes k :: "'a::len word"
  assumes szv: "sz < LENGTH('a)"
  and     kv:  "k < 2 ^ sz"
  shows   "unat k < 2 ^ sz"
  using szv unat_mono [OF kv] by simp

lemma unat_mult_power_lem:
  assumes kv: "k < 2 ^ (LENGTH('a::len) - sz)"
  shows "unat (2 ^ sz * of_nat k :: (('a::len) word)) = 2 ^ sz * k"
proof (cases \<open>sz < LENGTH('a)\<close>)
  case True
  with assms show ?thesis
    by (simp add: unat_word_ariths take_bit_eq_mod mod_simps)
      (simp add: take_bit_nat_eq_self_iff nat_less_power_trans flip: take_bit_eq_mod)
next
  case False
  with assms show ?thesis
    by simp
qed

lemma word_plus_mcs_4:
  "\<lbrakk>v + x \<le> w + x; x \<le> v + x\<rbrakk> \<Longrightarrow> v \<le> (w::'a::len word)"
  by uint_arith

lemma word_plus_mcs_3:
  "\<lbrakk>v \<le> w; x \<le> w + x\<rbrakk> \<Longrightarrow> v + x \<le> w + (x::'a::len word)"
  by unat_arith

lemma word_le_minus_one_leq:
  "x < y \<Longrightarrow> x \<le> y - 1" for x :: "'a :: len word"
  by transfer (metis le_less_trans less_irrefl take_bit_decr_eq take_bit_nonnegative zle_diff1_eq) 

lemma word_less_sub_le[simp]:
  fixes x :: "'a :: len word"
  assumes nv: "n < LENGTH('a)"
  shows "(x \<le> 2 ^ n - 1) = (x < 2 ^ n)"
  using le_less_trans word_le_minus_one_leq nv power_2_ge_iff by blast

lemma unat_of_nat_len:
  "x < 2 ^ LENGTH('a) \<Longrightarrow> unat (of_nat x :: 'a::len word) = x"
  by (simp add: take_bit_nat_eq_self_iff)

lemma unat_of_nat_eq:
  "x < 2 ^ LENGTH('a) \<Longrightarrow> unat (of_nat x ::'a::len word) = x"
  by (rule unat_of_nat_len)

lemma unat_eq_of_nat:
  "n < 2 ^ LENGTH('a) \<Longrightarrow> (unat (x :: 'a::len word) = n) = (x = of_nat n)"
  by transfer
    (auto simp add: take_bit_of_nat nat_eq_iff take_bit_nat_eq_self_iff intro: sym)

lemma alignUp_div_helper:
  fixes a :: "'a::len word"
  assumes kv: "k < 2 ^ (LENGTH('a) - n)"
  and     xk: "x = 2 ^ n * of_nat k"
  and    le: "a \<le> x"
  and    sz: "n < LENGTH('a)"
  and   anz: "a mod 2 ^ n \<noteq> 0"
  shows "a div 2 ^ n < of_nat k"
proof -
  have kn: "unat (of_nat k :: 'a word) * unat ((2::'a word) ^ n) < 2 ^ LENGTH('a)"
    using xk kv sz
    apply (subst unat_of_nat_eq)
     apply (erule order_less_le_trans)
     apply simp
    apply (subst unat_power_lower, simp)
    apply (subst mult.commute)
    apply (rule nat_less_power_trans)
     apply simp
    apply simp
    done

  have "unat a div 2 ^ n * 2 ^ n \<noteq> unat a"
  proof -
    have "unat a = unat a div 2 ^ n * 2 ^ n + unat a mod 2 ^ n"
      by (simp add: div_mult_mod_eq)
    also have "\<dots> \<noteq> unat a div 2 ^ n * 2 ^ n" using sz anz
      by (simp add: unat_arith_simps)
    finally show ?thesis ..
  qed

  then have "a div 2 ^ n * 2 ^ n < a" using sz anz
    apply (subst word_less_nat_alt)
    apply (subst unat_word_ariths)
    apply (subst unat_div)
    apply simp
    apply (rule order_le_less_trans [OF mod_less_eq_dividend])
    apply (erule order_le_neq_trans [OF div_mult_le])
    done

  also from xk le have "\<dots> \<le> of_nat k * 2 ^ n" by (simp add: field_simps)
  finally show ?thesis using sz kv
    apply -
    apply (erule word_mult_less_dest [OF _ _ kn])
    apply (simp add: unat_div)
    apply (rule order_le_less_trans [OF div_mult_le])
    apply (rule unat_lt2p)
    done
qed

lemma mask_out_sub_mask:
  "(x AND NOT (mask n)) = x - (x AND (mask n))"
  for x :: \<open>'a::len word\<close>
  by (simp add: field_simps word_plus_and_or_coroll2)

lemma subtract_mask:
  "p - (p AND mask n) = (p AND NOT (mask n))"
  "p - (p AND NOT (mask n)) = (p AND mask n)"
  for p :: \<open>'a::len word\<close>
  by (simp add: field_simps word_plus_and_or_coroll2)+

lemma take_bit_word_eq_self_iff:
  \<open>take_bit n w = w \<longleftrightarrow> n \<ge> LENGTH('a) \<or> w < 2 ^ n\<close>
  for w :: \<open>'a::len word\<close>
  using take_bit_int_eq_self_iff [of n \<open>take_bit LENGTH('a) (uint w)\<close>]
  by (transfer fixing: n) auto

lemma word_power_increasing:
  assumes x: "2 ^ x < (2 ^ y::'a::len word)" "x < LENGTH('a::len)" "y < LENGTH('a::len)"
  shows "x < y" using x
  using assms by transfer simp

lemma mask_twice:
  "(x AND mask n) AND mask m = x AND mask (min m n)"
  for x :: \<open>'a::len word\<close>
  by (simp flip: take_bit_eq_mask)

lemma plus_one_helper[elim!]:
  "x < n + (1 :: 'a :: len word) \<Longrightarrow> x \<le> n"
  apply (simp add: word_less_nat_alt word_le_nat_alt field_simps)
  apply (case_tac "1 + n = 0")
   apply simp_all
  apply (subst(asm) unatSuc, assumption)
  apply arith
  done

lemma plus_one_helper2:
  "\<lbrakk> x \<le> n; n + 1 \<noteq> 0 \<rbrakk> \<Longrightarrow> x < n + (1 :: 'a :: len word)"
  by (simp add: word_less_nat_alt word_le_nat_alt field_simps
                unatSuc)

lemma less_x_plus_1:
  fixes x :: "'a :: len word" shows
  "x \<noteq> max_word \<Longrightarrow> (y < (x + 1)) = (y < x \<or> y = x)"
  apply (rule iffI)
   apply (rule disjCI)
   apply (drule plus_one_helper)
   apply simp
  apply (subgoal_tac "x < x + 1")
   apply (erule disjE, simp_all)
  apply (rule plus_one_helper2 [OF order_refl])
  apply (rule notI, drule max_word_wrap)
  apply simp
  done

lemma word_Suc_leq:
  fixes k::"'a::len word" shows "k \<noteq> max_word \<Longrightarrow> x < k + 1 \<longleftrightarrow> x \<le> k"
  using less_x_plus_1 word_le_less_eq by auto

lemma word_Suc_le:
   fixes k::"'a::len word" shows "x \<noteq> max_word \<Longrightarrow> x + 1 \<le> k \<longleftrightarrow> x < k"
  by (meson not_less word_Suc_leq)

lemma word_lessThan_Suc_atMost:
  \<open>{..< k + 1} = {..k}\<close> if \<open>k \<noteq> - 1\<close> for k :: \<open>'a::len word\<close>
  using that by (simp add: lessThan_def atMost_def word_Suc_leq)

lemma word_atLeastLessThan_Suc_atLeastAtMost:
  \<open>{l ..< u + 1} = {l..u}\<close> if \<open>u \<noteq> - 1\<close> for l :: \<open>'a::len word\<close>
  using that by (simp add: atLeastAtMost_def atLeastLessThan_def word_lessThan_Suc_atMost)

lemma word_atLeastAtMost_Suc_greaterThanAtMost:
  \<open>{m<..u} = {m + 1..u}\<close> if \<open>m \<noteq> - 1\<close> for m :: \<open>'a::len word\<close>
  using that by (simp add: greaterThanAtMost_def greaterThan_def atLeastAtMost_def atLeast_def word_Suc_le)

lemma word_atLeastLessThan_Suc_atLeastAtMost_union:
  fixes l::"'a::len word"
  assumes "m \<noteq> max_word" and "l \<le> m" and "m \<le> u"
  shows "{l..m} \<union> {m+1..u} = {l..u}"
  proof -
  from ivl_disj_un_two(8)[OF assms(2) assms(3)] have "{l..u} = {l..m} \<union> {m<..u}" by blast
  with assms show ?thesis by(simp add: word_atLeastAtMost_Suc_greaterThanAtMost)
  qed

lemma max_word_less_eq_iff [simp]:
  \<open>- 1 \<le> w \<longleftrightarrow> w = - 1\<close> for w :: \<open>'a::len word\<close>
  by (fact word_order.extremum_unique)

lemma word_or_zero:
  "(a OR b = 0) = (a = 0 \<and> b = 0)"
  for a b :: \<open>'a::len word\<close>
  by (fact or_eq_0_iff)

lemma word_2p_mult_inc:
  assumes x: "2 * 2 ^ n < (2::'a::len word) * 2 ^ m"
  assumes suc_n: "Suc n < LENGTH('a::len)"
  shows "2^n < (2::'a::len word)^m"
  by (smt suc_n le_less_trans lessI nat_less_le nat_mult_less_cancel_disj p2_gt_0
          power_Suc power_Suc unat_power_lower word_less_nat_alt x)

lemma power_overflow:
  "n \<ge> LENGTH('a) \<Longrightarrow> 2 ^ n = (0 :: 'a::len word)"
  by simp

lemmas extra_sle_sless_unfolds [simp] =
    word_sle_eq[where a=0 and b=1]
    word_sle_eq[where a=0 and b="numeral n"]
    word_sle_eq[where a=1 and b=0]
    word_sle_eq[where a=1 and b="numeral n"]
    word_sle_eq[where a="numeral n" and b=0]
    word_sle_eq[where a="numeral n" and b=1]
    word_sless_alt[where a=0 and b=1]
    word_sless_alt[where a=0 and b="numeral n"]
    word_sless_alt[where a=1 and b=0]
    word_sless_alt[where a=1 and b="numeral n"]
    word_sless_alt[where a="numeral n" and b=0]
    word_sless_alt[where a="numeral n" and b=1]
  for n

lemma word_sint_1:
  "sint (1::'a::len word) = (if LENGTH('a) = 1 then -1 else 1)"
  by (fact signed_1)

lemma ucast_of_nat:
  "is_down (ucast :: 'a :: len word \<Rightarrow> 'b :: len word)
    \<Longrightarrow> ucast (of_nat n :: 'a word) = (of_nat n :: 'b word)"
  by transfer simp

lemma scast_1':
  "(scast (1::'a::len word) :: 'b::len word) =
   (word_of_int (signed_take_bit (LENGTH('a::len) - Suc 0) (1::int)))"
  by transfer simp

lemma scast_1:
  "(scast (1::'a::len word) :: 'b::len word) = (if LENGTH('a) = 1 then -1 else 1)"
  by (fact signed_1)

lemma unat_minus_one_word:
  "unat (-1 :: 'a :: len word) = 2 ^ LENGTH('a) - 1"
  apply (simp only: flip: mask_eq_exp_minus_1)
  apply transfer
  apply (simp add: take_bit_minus_one_eq_mask nat_mask_eq)
  done

lemmas word_diff_ls'' = word_diff_ls [where xa=x and x=x for x]
lemmas word_diff_ls' = word_diff_ls'' [simplified]

lemmas word_l_diffs' = word_l_diffs [where xa=x and x=x for x]
lemmas word_l_diffs = word_l_diffs' [simplified]

lemma two_power_increasing:
  "\<lbrakk> n \<le> m; m < LENGTH('a) \<rbrakk> \<Longrightarrow> (2 :: 'a :: len word) ^ n \<le> 2 ^ m"
  by (simp add: word_le_nat_alt)

lemma word_leq_le_minus_one:
  "\<lbrakk> x \<le> y; x \<noteq> 0 \<rbrakk> \<Longrightarrow> x - 1 < (y :: 'a :: len word)"
  apply (simp add: word_less_nat_alt word_le_nat_alt)
  apply (subst unat_minus_one)
   apply assumption
  apply (cases "unat x")
   apply (simp add: unat_eq_zero)
  apply arith
  done

lemma neg_mask_combine:
  "NOT(mask a) AND NOT(mask b) = NOT(mask (max a b) :: 'a::len word)"
  by (rule bit_word_eqI) (auto simp add: bit_simps)

lemma neg_mask_twice:
  "x AND NOT(mask n) AND NOT(mask m) = x AND NOT(mask (max n m))"
  for x :: \<open>'a::len word\<close>
  by (rule bit_word_eqI) (auto simp add: bit_simps)

lemma multiple_mask_trivia:
  "n \<ge> m \<Longrightarrow> (x AND NOT(mask n)) + (x AND mask n AND NOT(mask m)) = x AND NOT(mask m)"
  for x :: \<open>'a::len word\<close>
  apply (rule trans[rotated], rule_tac w="mask n" in word_plus_and_or_coroll2)
  apply (simp add: word_bw_assocs word_bw_comms word_bw_lcs neg_mask_twice
                   max_absorb2)
  done

lemma word_of_nat_less:
  "\<lbrakk> n < unat x \<rbrakk> \<Longrightarrow> of_nat n < x"
  apply (simp add: word_less_nat_alt)
  apply (erule order_le_less_trans[rotated])
  apply (simp add: take_bit_eq_mod)
  done

lemma unat_mask:
  "unat (mask n :: 'a :: len word) = 2 ^ (min n (LENGTH('a))) - 1"
  apply (subst min.commute)
  apply (simp add: mask_eq_decr_exp not_less min_def  split: if_split_asm)
  apply (intro conjI impI)
   apply (simp add: unat_sub_if_size)
   apply (simp add: power_overflow word_size)
  apply (simp add: unat_sub_if_size)
  done

lemma mask_over_length:
  "LENGTH('a) \<le> n \<Longrightarrow> mask n = (-1::'a::len word)"
  by (simp add: mask_eq_decr_exp)

lemma Suc_2p_unat_mask:
  "n < LENGTH('a) \<Longrightarrow> Suc (2 ^ n * k + unat (mask n :: 'a::len word)) = 2 ^ n * (k+1)"
  by (simp add: unat_mask)

lemma sint_of_nat_ge_zero:
  "x < 2 ^ (LENGTH('a) - 1) \<Longrightarrow> sint (of_nat x :: 'a :: len word) \<ge> 0"
  by (simp add: bit_iff_odd)

lemma int_eq_sint:
  "x < 2 ^ (LENGTH('a) - 1) \<Longrightarrow> sint (of_nat x :: 'a :: len word) = int x"
  apply transfer
  apply (rule signed_take_bit_int_eq_self)
   apply simp_all
  apply (metis negative_zle numeral_power_eq_of_nat_cancel_iff)
  done

lemma sint_of_nat_le:
  "\<lbrakk> b < 2 ^ (LENGTH('a) - 1); a \<le> b \<rbrakk>
   \<Longrightarrow> sint (of_nat a :: 'a :: len word) \<le> sint (of_nat b :: 'a :: len word)"
  apply (cases \<open>LENGTH('a)\<close>)
  apply simp_all
  apply transfer
  apply (subst signed_take_bit_eq_if_positive)
   apply (simp add: bit_simps)
  apply (metis bit_take_bit_iff nat_less_le order_less_le_trans take_bit_nat_eq_self_iff)
  apply (subst signed_take_bit_eq_if_positive)
    apply (simp add: bit_simps)
  apply (metis bit_take_bit_iff nat_less_le take_bit_nat_eq_self_iff)
    apply (simp flip: of_nat_take_bit add: take_bit_nat_eq_self)
  done

lemma word_le_not_less:
  "((b::'a::len word) \<le> a) = (\<not>(a < b))"
  by fastforce

lemma less_is_non_zero_p1:
  fixes a :: "'a :: len word"
  shows "a < k \<Longrightarrow> a + 1 \<noteq> 0"
  apply (erule contrapos_pn)
  apply (drule max_word_wrap)
  apply (simp add: not_less)
  done

lemma unat_add_lem':
  "(unat x + unat y < 2 ^ LENGTH('a)) \<Longrightarrow>
    (unat (x + y :: 'a :: len word) = unat x + unat y)"
  by (subst unat_add_lem[symmetric], assumption)

lemma word_less_two_pow_divI:
  "\<lbrakk> (x :: 'a::len word) < 2 ^ (n - m); m \<le> n; n < LENGTH('a) \<rbrakk> \<Longrightarrow> x < 2 ^ n div 2 ^ m"
  apply (simp add: word_less_nat_alt)
  apply (subst unat_word_ariths)
  apply (subst mod_less)
   apply (rule order_le_less_trans [OF div_le_dividend])
   apply (rule unat_lt2p)
  apply (simp add: power_sub)
  done

lemma word_less_two_pow_divD:
  "\<lbrakk> (x :: 'a::len word) < 2 ^ n div 2 ^ m \<rbrakk>
     \<Longrightarrow> n \<ge> m \<and> (x < 2 ^ (n - m))"
  apply (cases "n < LENGTH('a)")
   apply (cases "m < LENGTH('a)")
    apply (simp add: word_less_nat_alt)
    apply (subst(asm) unat_word_ariths)
    apply (subst(asm) mod_less)
     apply (rule order_le_less_trans [OF div_le_dividend])
     apply (rule unat_lt2p)
    apply (clarsimp dest!: less_two_pow_divD)
   apply (simp add: power_overflow)
   apply (simp add: word_div_def)
  apply (simp add: power_overflow word_div_def)
  done

lemma of_nat_less_two_pow_div_set:
  "\<lbrakk> n < LENGTH('a) \<rbrakk> \<Longrightarrow>
   {x. x < (2 ^ n div 2 ^ m :: 'a::len word)}
      = of_nat ` {k. k < 2 ^ n div 2 ^ m}"
  apply (simp add: image_def)
  apply (safe dest!: word_less_two_pow_divD less_two_pow_divD
             intro!: word_less_two_pow_divI)
   apply (rule_tac x="unat x" in exI)
   apply (simp add: power_sub[symmetric])
   apply (subst unat_power_lower[symmetric, where 'a='a])
    apply simp
   apply (erule unat_mono)
  apply (subst word_unat_power)
  apply (rule of_nat_mono_maybe)
   apply (rule power_strict_increasing)
    apply simp
   apply simp
  apply assumption
  done

lemma ucast_less:
  "LENGTH('b) < LENGTH('a) \<Longrightarrow>
   (ucast (x :: 'b :: len word) :: ('a :: len word)) < 2 ^ LENGTH('b)"
  by transfer simp

lemma ucast_range_less:
  "LENGTH('a :: len) < LENGTH('b :: len) \<Longrightarrow>
   range (ucast :: 'a word \<Rightarrow> 'b word) = {x. x < 2 ^ len_of TYPE ('a)}"
  apply safe
   apply (erule ucast_less)
  apply (simp add: image_def)
  apply (rule_tac x="ucast x" in exI)
  apply (rule bit_word_eqI)
  apply (auto simp add: bit_simps)
  apply (metis bit_take_bit_iff less_mask_eq not_less take_bit_eq_mask)
  done

lemma word_power_less_diff:
  "\<lbrakk>2 ^ n * q < (2::'a::len word) ^ m; q < 2 ^ (LENGTH('a) - n)\<rbrakk> \<Longrightarrow> q < 2 ^ (m - n)"
  apply (case_tac "m \<ge> LENGTH('a)")
   apply (simp add: power_overflow)
  apply (case_tac "n \<ge> LENGTH('a)")
   apply (simp add: power_overflow)
  apply (cases "n = 0")
   apply simp
  apply (subst word_less_nat_alt)
  apply (subst unat_power_lower)
   apply simp
  apply (rule nat_power_less_diff)
  apply (simp add: word_less_nat_alt)
  apply (subst (asm) iffD1 [OF unat_mult_lem])
   apply (simp add:nat_less_power_trans)
  apply simp
  done

lemma word_less_sub_1:
  "x < (y :: 'a :: len word) \<Longrightarrow> x \<le> y - 1"
  by (fact word_le_minus_one_leq)

lemma word_sub_mono2:
  "\<lbrakk> a + b \<le> c + d; c \<le> a; b \<le> a + b; d \<le> c + d \<rbrakk>
    \<Longrightarrow> b \<le> (d :: 'a :: len word)"
  apply (drule(1) word_sub_mono)
    apply simp
   apply simp
  apply simp
  done

lemma word_not_le:
  "(\<not> x \<le> (y :: 'a :: len word)) = (y < x)"
  by fastforce

lemma word_subset_less:
  "\<lbrakk> {x .. x + r - 1} \<subseteq> {y .. y + s - 1};
     x \<le> x + r - 1; y \<le> y + (s :: 'a :: len word) - 1;
     s \<noteq> 0 \<rbrakk>
     \<Longrightarrow> r \<le> s"
  apply (frule subsetD[where c=x])
   apply simp
  apply (drule subsetD[where c="x + r - 1"])
   apply simp
  apply (clarsimp simp: add_diff_eq[symmetric])
  apply (drule(1) word_sub_mono2)
    apply (simp_all add: olen_add_eqv[symmetric])
  apply (erule word_le_minus_cancel)
  apply (rule ccontr)
  apply (simp add: word_not_le)
  done

lemma uint_power_lower:
  "n < LENGTH('a) \<Longrightarrow> uint (2 ^ n :: 'a :: len word) = (2 ^ n :: int)"
  by (rule uint_2p_alt)

lemma power_le_mono:
  "\<lbrakk>2 ^ n \<le> (2::'a::len word) ^ m; n < LENGTH('a); m < LENGTH('a)\<rbrakk>
   \<Longrightarrow> n \<le> m"
  apply (clarsimp simp add: le_less)
  apply safe
  apply (simp add: word_less_nat_alt)
  apply (simp only: uint_arith_simps(3))
  apply (drule uint_power_lower)+
  apply simp
  done

lemma two_power_eq:
  "\<lbrakk>n < LENGTH('a); m < LENGTH('a)\<rbrakk>
   \<Longrightarrow> ((2::'a::len word) ^ n = 2 ^ m) = (n = m)"
  apply safe
  apply (rule order_antisym)
   apply (simp add: power_le_mono[where 'a='a])+
  done

lemma unat_less_helper:
  "x < of_nat n \<Longrightarrow> unat x < n"
  apply (simp add: word_less_nat_alt)
  apply (erule order_less_le_trans)
  apply (simp add: take_bit_eq_mod)
  done

lemma nat_uint_less_helper:
  "nat (uint y) = z \<Longrightarrow> x < y \<Longrightarrow> nat (uint x) < z"
  apply (erule subst)
  apply (subst unat_eq_nat_uint [symmetric])
  apply (subst unat_eq_nat_uint [symmetric])
  by (simp add: unat_mono)

lemma of_nat_0:
  "\<lbrakk>of_nat n = (0::'a::len word); n < 2 ^ LENGTH('a)\<rbrakk> \<Longrightarrow> n = 0"
  by transfer (simp add: take_bit_eq_mod)

lemma of_nat_inj:
  "\<lbrakk>x < 2 ^ LENGTH('a); y < 2 ^ LENGTH('a)\<rbrakk> \<Longrightarrow>
   (of_nat x = (of_nat y :: 'a :: len word)) = (x = y)"
  by (metis unat_of_nat_len)

lemma div_to_mult_word_lt:
  "\<lbrakk> (x :: 'a :: len word) \<le> y div z \<rbrakk> \<Longrightarrow> x * z \<le> y"
  apply (cases "z = 0")
   apply simp
  apply (simp add: word_neq_0_conv)
  apply (rule order_trans)
   apply (erule(1) word_mult_le_mono1)
   apply (simp add: unat_div)
   apply (rule order_le_less_trans [OF div_mult_le])
   apply simp
  apply (rule word_div_mult_le)
  done

lemma ucast_ucast_mask:
  "(ucast :: 'a :: len word \<Rightarrow> 'b :: len word) (ucast x) = x AND mask (len_of TYPE ('a))"
  apply (simp flip: take_bit_eq_mask)
  apply transfer
  apply (simp add: ac_simps)
  done

lemma ucast_ucast_len:
  "\<lbrakk> x < 2 ^ LENGTH('b) \<rbrakk> \<Longrightarrow> ucast (ucast x::'b::len word) = (x::'a::len word)"
  apply (subst ucast_ucast_mask)
  apply (erule less_mask_eq)
  done

lemma ucast_ucast_id:
  "LENGTH('a) < LENGTH('b) \<Longrightarrow> ucast (ucast (x::'a::len word)::'b::len word) = x"
  by (auto intro: ucast_up_ucast_id simp: is_up_def source_size_def target_size_def word_size)

lemma unat_ucast:
  "unat (ucast x :: ('a :: len) word) = unat x mod 2 ^ (LENGTH('a))"
proof -
  have \<open>2 ^ LENGTH('a) = nat (2 ^ LENGTH('a))\<close>
    by simp
  moreover have \<open>unat (ucast x :: 'a word) = unat x mod nat (2 ^ LENGTH('a))\<close>
    by transfer (simp flip: nat_mod_distrib take_bit_eq_mod)
  ultimately show ?thesis
    by (simp only:)
qed

lemma ucast_less_ucast:
  "LENGTH('a) \<le> LENGTH('b) \<Longrightarrow>
   (ucast x < ((ucast (y :: 'a::len word)) :: 'b::len word)) = (x < y)"
  apply (simp add: word_less_nat_alt unat_ucast)
  apply (subst mod_less)
   apply(rule less_le_trans[OF unat_lt2p], simp)
  apply (subst mod_less)
   apply(rule less_le_trans[OF unat_lt2p], simp)
  apply simp
  done

\<comment> \<open>This weaker version was previously called @{text ucast_less_ucast}. We retain it to
    support existing proofs.\<close>
lemmas ucast_less_ucast_weak = ucast_less_ucast[OF order.strict_implies_order]

lemma unat_Suc2:
  fixes n :: "'a :: len word"
  shows
  "n \<noteq> -1 \<Longrightarrow> unat (n + 1) = Suc (unat n)"
  apply (subst add.commute, rule unatSuc)
  apply (subst eq_diff_eq[symmetric], simp add: minus_equation_iff)
  done

lemma word_div_1:
  "(n :: 'a :: len word) div 1 = n"
  by (fact bits_div_by_1)

lemma word_minus_one_le:
  "-1 \<le> (x :: 'a :: len word) = (x = -1)"
  by (fact word_order.extremum_unique)

lemma up_scast_inj:
      "\<lbrakk> scast x = (scast y :: 'b :: len word); size x \<le> LENGTH('b) \<rbrakk>
         \<Longrightarrow> x = y"
  apply transfer
  apply (cases \<open>LENGTH('a)\<close>)
  apply simp_all
  apply (metis order_refl take_bit_signed_take_bit take_bit_tightened)
  done

lemma up_scast_inj_eq:
  "LENGTH('a) \<le> len_of TYPE ('b) \<Longrightarrow>
  (scast x = (scast y::'b::len word)) = (x = (y::'a::len word))"
  by (fastforce dest: up_scast_inj simp: word_size)

lemma word_le_add:
  fixes x :: "'a :: len word"
  shows "x \<le> y \<Longrightarrow> \<exists>n. y = x + of_nat n"
  by (rule exI [where x = "unat (y - x)"]) simp

lemma word_plus_mcs_4':
  fixes x :: "'a :: len word"
  shows "\<lbrakk>x + v \<le> x + w; x \<le> x + v\<rbrakk> \<Longrightarrow> v \<le> w"
  apply (rule word_plus_mcs_4)
   apply (simp add: add.commute)
  apply (simp add: add.commute)
  done

end
