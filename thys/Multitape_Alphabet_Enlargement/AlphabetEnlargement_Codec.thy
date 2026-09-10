theory AlphabetEnlargement_Codec
  imports AlphabetEnlargement_Window
begin

subsection \<open>Encoder and decoder structural lemmas\<close>

subsubsection \<open>Decoder structural lemmas and ceiling-div arithmetic\<close>

text \<open>Decoder structural lemmas.  \<open>ae_decode_block_pure\<close>
  resolves to the full enum image (length \<open>c\<close>); the analogous
  fact for padded blocks (length = the padded witness)
  splits the enum list at the witness index and uses the
  takeWhile / append decomposition.\<close>

lemma ae_decode_block_pure:
  fixes f :: "'c :: enum \<Rightarrow> 'a"
  assumes "is_pure_block bl f"
  shows "ae_decode_block bl f
           = map f (enum_class.enum :: 'c list)"
proof -
  have all_neq: "\<forall>a \<in> set (map f (enum_class.enum :: 'c list)). a \<noteq> bl"
    using assms unfolding is_pure_block_def by auto
  show ?thesis
    unfolding ae_decode_block_def
    using all_neq by (simp add: takeWhile_eq_all_conv)
qed

lemma length_ae_decode_block_pure:
  fixes f :: "'c :: enum \<Rightarrow> 'a"
  assumes "is_pure_block bl f"
  shows "length (ae_decode_block bl f) = card (UNIV :: 'c set)"
  using ae_decode_block_pure[OF assms] card_eq_length_enum[symmetric]
  by simp

lemma ae_decode_block_padded:
  fixes f :: "'c :: enum \<Rightarrow> 'a"
  assumes k_lt: "k < length (enum_class.enum :: 'c list)"
      and prefix: "\<forall>x. c_idx x < k \<longrightarrow> f x \<noteq> bl"
      and suffix: "\<forall>x. k \<le> c_idx x \<longrightarrow> f x = bl"
  shows "ae_decode_block bl f
           = map f (take k (enum_class.enum :: 'c list))"
proof -
  let ?xs = "enum_class.enum :: 'c list"
  let ?P = "\<lambda>a. a \<noteq> bl"
  have at_k: "f (?xs ! k) = bl"
  proof -
    have "c_idx (?xs ! k) = k" using k_lt by (rule c_idx_enum_nth)
    thus ?thesis using suffix by simp
  qed
  have prefix_neq: "\<forall>a \<in> set (map f (take k ?xs)). ?P a"
  proof
    fix a assume a_in: "a \<in> set (map f (take k ?xs))"
    then obtain i where i_lt: "i < length (take k ?xs)"
      and a_eq: "a = map f (take k ?xs) ! i"
      by (auto simp: in_set_conv_nth)
    from i_lt have i_lt_k: "i < k" using k_lt by simp
    hence i_lt_n: "i < length ?xs" using k_lt by linarith
    have a_alt: "a = f (?xs ! i)"
      using a_eq i_lt_k k_lt by (simp add: nth_map nth_take)
    have c_idx_at: "c_idx (?xs ! i) = i" using i_lt_n by (rule c_idx_enum_nth)
    show "?P a" using prefix c_idx_at i_lt_k a_alt by simp
  qed
  have xs_split: "?xs = take k ?xs @ ?xs ! k # drop (Suc k) ?xs"
    using k_lt by (rule id_take_nth_drop)
  have map_split: "map f ?xs = map f (take k ?xs) @ f (?xs ! k) # map f (drop (Suc k) ?xs)"
  proof -
    have "map f ?xs = map f (take k ?xs @ ?xs ! k # drop (Suc k) ?xs)"
      using xs_split by simp
    thus ?thesis by simp
  qed
  have step1: "takeWhile ?P (map f ?xs)
                  = map f (take k ?xs)
                      @ takeWhile ?P (f (?xs ! k) # map f (drop (Suc k) ?xs))"
  proof -
    have "takeWhile ?P (map f ?xs)
            = takeWhile ?P (map f (take k ?xs)
                              @ f (?xs ! k) # map f (drop (Suc k) ?xs))"
      using map_split by simp
    also have "\<dots> = map f (take k ?xs)
                      @ takeWhile ?P (f (?xs ! k) # map f (drop (Suc k) ?xs))"
      using prefix_neq by (subst takeWhile_append) auto
    finally show ?thesis .
  qed
  have step2: "takeWhile ?P (f (?xs ! k) # map f (drop (Suc k) ?xs)) = []"
    using at_k by simp
  show ?thesis
    unfolding ae_decode_block_def
    using step1 step2 by simp
qed

text \<open>Decoder structural lemmas (continued).  \<open>ae_decode_input\<close>
  is compositional under list append; the length-of-decode for
  an all-pure prefix is exactly \<open>length \<cdot> c\<close>.\<close>

lemma ae_decode_input_append:
  "ae_decode_input bl (xs @ ys)
     = ae_decode_input bl xs @ ae_decode_input bl ys"
  by (simp add: ae_decode_input_def)

lemma length_ae_decode_input_pure:
  fixes xs :: "('c :: enum \<Rightarrow> 'a) list"
  assumes "\<forall>s < length xs. is_pure_block bl (xs ! s)"
  shows "length (ae_decode_input bl xs) = length xs * card (UNIV :: 'c set)"
  using assms
proof (induction xs)
  case Nil
  show ?case by (simp add: ae_decode_input_def)
next
  case (Cons x xs)
  have x_pure: "is_pure_block bl x"
    using Cons.prems[rule_format, of 0] by simp
  have rest_pure: "\<forall>s < length xs. is_pure_block bl (xs ! s)"
  proof (intro allI impI)
    fix s assume "s < length xs"
    hence "Suc s < length (x # xs)" by simp
    thus "is_pure_block bl (xs ! s)"
      using Cons.prems[rule_format, of "Suc s"] by simp
  qed
  have "length (ae_decode_input bl (x # xs))
          = length (ae_decode_block bl x) + length (ae_decode_input bl xs)"
    by (simp add: ae_decode_input_def)
  also have "\<dots> = card (UNIV :: 'c set) + length xs * card (UNIV :: 'c set)"
    using length_ae_decode_block_pure[OF x_pure] Cons.IH[OF rest_pure]
    by simp
  also have "\<dots> = length (x # xs) * card (UNIV :: 'c set)"
    by simp
  finally show ?case .
qed

text \<open>Ceiling-division arithmetic.  Used by the encoder/decoder
  round-trip lemmas below.\<close>

lemma ceil_div_mult_c:
  fixes m c :: nat
  assumes "0 < c"
  shows "(m * c + c - 1) div c = m"
  using assms
proof (induction m)
  case 0
  show ?case using `0 < c` by simp
next
  case (Suc m)
  have c_ne: "c \<noteq> 0" using `0 < c` by simp
  have eq: "Suc m * c + c - 1 = (m * c + c - 1) + c"
    using `0 < c` by simp
  have step: "((m * c + c - 1) + c) div c = (m * c + c - 1) div c + 1"
    by (rule div_add_self2[OF c_ne])
  have ih: "(m * c + c - 1) div c = m" using Suc.IH[OF `0 < c`] .
  have "(Suc m * c + c - 1) div c = ((m * c + c - 1) + c) div c"
    using eq by (rule arg_cong[where f = "\<lambda>x. x div c"])
  also have "\<dots> = (m * c + c - 1) div c + 1" using step .
  also have "\<dots> = m + 1" using ih by simp
  finally show ?case by simp
qed

lemma ceil_div_2c_minus_1:
  fixes c :: nat
  assumes "0 < c"
  shows "(c + c - 1) div c = 1"
proof -
  have "c + c - 1 = 1 * c + c - 1" by simp
  thus ?thesis using ceil_div_mult_c[OF assms, of 1] by simp
qed

lemma ceil_div_k_plus_c_minus_1:
  fixes k c :: nat
  assumes "0 < c" "0 < k" "k \<le> c"
  shows "(k + c - 1) div c = 1"
proof -
  have lo: "k + c - 1 \<ge> c" using assms by simp
  have hi: "k + c - 1 < c + c"
    using assms by linarith
  have "(k + c - 1) div c = ((k + c - 1) - c) div c + 1"
    using lo assms by (auto simp: le_div_geq)
  also have "(k + c - 1) - c = k - 1" by simp
  also have "(k - 1) div c = 0" using assms by simp
  finally show ?thesis by simp
qed

subsubsection \<open>Encoder list operations and image properties\<close>

text \<open>Encoding an input that is the image of a block function
  under the canonical enumeration yields the singleton list
  containing that block.  Used by the round-trip lemma in the
  forward direction of \<open>ae_validation_canonical_iff_encoder_image\<close>:
  a pure last-block decodes to its full enum image, and that
  image re-encodes back to the original block.\<close>

lemma encode_input_map_enum:
  fixes f :: "'c :: enum \<Rightarrow> 'a"
  shows "encode_input bl (map f (enum_class.enum :: 'c list))
           = ([f] :: ('c \<Rightarrow> 'a) list)"
proof -
  let ?c = "card (UNIV :: 'c set)"
  let ?xs = "enum_class.enum :: 'c list"
  let ?w = "map f ?xs"
  let ?lhs = "encode_input bl ?w :: ('c \<Rightarrow> 'a) list"
  have len_xs: "length ?xs = ?c"
    using card_eq_length_enum[symmetric] .
  have len_w: "length ?w = ?c" using len_xs by simp
  have c_pos: "0 < ?c"
  proof -
    have "(c_first :: 'c) \<in> UNIV" by simp
    thus ?thesis by (simp add: card_gt_0_iff)
  qed
  have len_lhs: "length ?lhs = 1"
  proof -
    have "length ?lhs = (length ?w + ?c - 1) div ?c"
      using length_encode_input[where bl = bl and u = "?w"] .
    also have "\<dots> = (?c + ?c - 1) div ?c" using len_w by simp
    also have "\<dots> = 1" using ceil_div_2c_minus_1[OF c_pos] .
    finally show ?thesis .
  qed
  have zero_lt_lhs: "0 < length ?lhs" using len_lhs by simp
  have nth0_at: "\<And>x :: 'c. (?lhs ! 0) x = f x"
  proof -
    fix x :: 'c
    have idx_lt_xs: "c_idx x < length ?xs"
      using c_idx_in_range(1) .
    have idx_lt_w: "c_idx x < length ?w" using idx_lt_xs by simp
    have nth_step: "(?lhs ! 0) x =
                       (let j = 0 * ?c + c_idx x
                          in if j < length ?w then ?w ! j else bl)"
      by (rule encode_input_nth[OF zero_lt_lhs])
    have w_at: "?w ! c_idx x = f x"
      using idx_lt_xs c_idx_in_range(2)[of x] by (simp add: nth_map)
    show "(?lhs ! 0) x = f x"
      using nth_step idx_lt_w w_at by (simp add: Let_def)
  qed
  have nth0: "?lhs ! 0 = f"
    using nth0_at by (rule ext)
  show ?thesis
  proof (rule nth_equalityI)
    show "length ?lhs = length ([f] :: ('c \<Rightarrow> 'a) list)"
      using len_lhs by simp
  next
    fix i assume i_lt: "i < length ?lhs"
    hence "i = 0" using len_lhs by simp
    thus "?lhs ! i = ([f] :: ('c \<Rightarrow> 'a) list) ! i"
      using nth0 by simp
  qed
qed

text \<open>Generalisation of \<open>encode_input_map_enum\<close>: encoding the
  image of \<open>f\<close> over a length-\<open>m\<close> prefix of the canonical
  enumeration (where \<open>0 < m \<le> c\<close>, and \<open>f x = bl\<close> on the
  out-of-prefix indices) yields the singleton list \<open>[f]\<close>.
  Used by the round-trip in the forward direction of
  \<open>ae_validation_canonical_iff_encoder_image\<close>: a padded last
  block decodes to its enum-prefix, and that prefix
  re-encodes back to the original block.\<close>

lemma encode_input_map_take_enum:
  fixes f :: "'c :: enum \<Rightarrow> 'a"
  assumes m_pos: "0 < m"
      and m_le: "m \<le> length (enum_class.enum :: 'c list)"
      and pad: "\<forall>x. c_idx x \<ge> m \<longrightarrow> f x = bl"
  shows "encode_input bl (map f (take m (enum_class.enum :: 'c list)))
           = ([f] :: ('c \<Rightarrow> 'a) list)"
proof -
  let ?c = "card (UNIV :: 'c set)"
  let ?xs = "enum_class.enum :: 'c list"
  let ?w = "map f (take m ?xs)"
  let ?lhs = "encode_input bl ?w :: ('c \<Rightarrow> 'a) list"
  have len_xs: "length ?xs = ?c" using card_eq_length_enum[symmetric] .
  have c_pos: "0 < ?c"
  proof -
    have "(c_first :: 'c) \<in> UNIV" by simp
    thus ?thesis by (simp add: card_gt_0_iff)
  qed
  have m_le_c: "m \<le> ?c" using m_le len_xs by simp
  have len_take: "length (take m ?xs) = m"
    using m_le by simp
  have len_w: "length ?w = m" using len_take by simp
  have len_lhs: "length ?lhs = 1"
  proof -
    have "length ?lhs = (length ?w + ?c - 1) div ?c"
      using length_encode_input[where bl = bl and u = "?w"] .
    also have "\<dots> = (m + ?c - 1) div ?c" using len_w by simp
    also have "\<dots> = 1"
      using ceil_div_k_plus_c_minus_1[OF c_pos m_pos m_le_c] .
    finally show ?thesis .
  qed
  have zero_lt_lhs: "0 < length ?lhs" using len_lhs by simp
  have nth0_at: "\<And>x :: 'c. (?lhs ! 0) x = f x"
  proof -
    fix x :: 'c
    have idx_lt_xs: "c_idx x < length ?xs" using c_idx_in_range(1) .
    have nth_step: "(?lhs ! 0) x =
                       (let j = 0 * ?c + c_idx x
                          in if j < length ?w then ?w ! j else bl)"
      by (rule encode_input_nth[OF zero_lt_lhs])
    show "(?lhs ! 0) x = f x"
    proof (cases "c_idx x < m")
      case True
      hence j_lt_w: "c_idx x < length ?w" using len_w by simp
      have w_at: "?w ! c_idx x = f x"
      proof -
        have take_at: "(take m ?xs) ! c_idx x = ?xs ! c_idx x"
          using True by simp
        have map_at: "?w ! c_idx x = f ((take m ?xs) ! c_idx x)"
          using True len_take by (simp add: nth_map)
        have "?w ! c_idx x = f (?xs ! c_idx x)"
          using map_at take_at by simp
        also have "?xs ! c_idx x = x" using c_idx_in_range(2)[of x] .
        finally show ?thesis .
      qed
      show ?thesis using nth_step j_lt_w w_at by (simp add: Let_def)
    next
      case False
      hence m_le_idx: "m \<le> c_idx x" by simp
      have f_eq_bl: "f x = bl" using pad m_le_idx by simp
      have body_bl: "(let j = 0 * ?c + c_idx x
                        in if j < length ?w then ?w ! j else bl) = bl"
        using m_le_idx m_le len_w by (auto simp: Let_def)
      have lhs_bl: "(?lhs ! 0) x = bl"
        using nth_step body_bl by simp
      show ?thesis using lhs_bl f_eq_bl by simp
    qed
  qed
  have nth0: "?lhs ! 0 = f" using nth0_at by (rule ext)
  show ?thesis
  proof (rule nth_equalityI)
    show "length ?lhs = length ([f] :: ('c \<Rightarrow> 'a) list)"
      using len_lhs by simp
  next
    fix i assume i_lt: "i < length ?lhs"
    hence "i = 0" using len_lhs by simp
    thus "?lhs ! i = ([f] :: ('c \<Rightarrow> 'a) list) ! i"
      using nth0 by simp
  qed
qed

text \<open>The encoder splits over an append whenever the prefix's
  length is a multiple of \<open>c\<close>: each block of \<open>encode_input
  bl (u1 @ u2)\<close> falls entirely within \<open>u1\<close> or entirely within
  \<open>u2\<close>, so the encoded list is the concatenation of the per-half
  encodings.  Used by the round-trip's \<open>rev_induct\<close>: when peeling
  off the last block of a well-formed \<open>w\<close>, the prefix's
  decode is all-pure (length divisible by \<open>c\<close>), allowing the
  encoder to split.\<close>

lemma encode_input_append_div:
  fixes u1 u2 :: "'a list"
  assumes c_div: "card (UNIV :: 'c :: enum set) dvd length u1"
  shows "(encode_input bl (u1 @ u2) :: ('c \<Rightarrow> 'a) list)
           = encode_input bl u1 @ encode_input bl u2"
proof -
  let ?c = "card (UNIV :: 'c set)"
  let ?lhs = "encode_input bl (u1 @ u2) :: ('c \<Rightarrow> 'a) list"
  let ?rhs1 = "encode_input bl u1 :: ('c \<Rightarrow> 'a) list"
  let ?rhs2 = "encode_input bl u2 :: ('c \<Rightarrow> 'a) list"
  have c_pos: "0 < ?c"
  proof -
    have "(c_first :: 'c) \<in> UNIV" by simp
    thus ?thesis by (simp add: card_gt_0_iff)
  qed
  obtain n where n_eq: "length u1 = n * ?c"
    using c_div by (auto simp: dvd_def mult.commute)
  have len_rhs1: "length ?rhs1 = n"
  proof -
    have "length ?rhs1 = (length u1 + ?c - 1) div ?c"
      using length_encode_input[where bl = bl and u = u1] .
    also have "\<dots> = (n * ?c + ?c - 1) div ?c" using n_eq by simp
    also have "\<dots> = n" using ceil_div_mult_c[OF c_pos] .
    finally show ?thesis .
  qed
  have len_rhs2: "length ?rhs2 = (length u2 + ?c - 1) div ?c"
    using length_encode_input[where bl = bl and u = u2] .
  have len_lhs: "length ?lhs = n + length ?rhs2"
  proof -
    have rearr: "n * ?c + length u2 + ?c - 1
                  = (length u2 + ?c - 1) + n * ?c"
      using c_pos by arith
    have c_ne: "?c \<noteq> 0" using c_pos by simp
    have "length ?lhs = (length u1 + length u2 + ?c - 1) div ?c"
      using length_encode_input[where bl = bl and u = "u1 @ u2"] by simp
    also have "\<dots> = (n * ?c + length u2 + ?c - 1) div ?c"
      using n_eq by simp
    also have "\<dots> = ((length u2 + ?c - 1) + n * ?c) div ?c"
      using rearr by simp
    also have "\<dots> = n + (length u2 + ?c - 1) div ?c"
      using c_ne by (simp add: div_mult_self1)
    also have "\<dots> = n + length ?rhs2" using len_rhs2 by simp
    finally show ?thesis .
  qed
  have len_eq: "length ?lhs = length (?rhs1 @ ?rhs2)"
    using len_rhs1 len_lhs by simp
  show ?thesis
  proof (rule nth_equalityI)
    show "length ?lhs = length (?rhs1 @ ?rhs2)" using len_eq .
  next
    fix i assume i_lt: "i < length ?lhs"
    have lhs_step: "\<And>x :: 'c. (?lhs ! i) x =
                       (let j = i * ?c + c_idx x
                          in if j < length (u1 @ u2)
                                then (u1 @ u2) ! j else bl)"
      using encode_input_nth[OF i_lt] by simp
    show "?lhs ! i = (?rhs1 @ ?rhs2) ! i"
    proof (cases "i < n")
      case True
      have i_lt_rhs1: "i < length ?rhs1" using True len_rhs1 by simp
      have rhs_split: "(?rhs1 @ ?rhs2) ! i = ?rhs1 ! i"
        using i_lt_rhs1 by (simp add: nth_append)
      have rhs1_step: "\<And>x :: 'c. (?rhs1 ! i) x =
                         (let j = i * ?c + c_idx x
                            in if j < length u1 then u1 ! j else bl)"
        using encode_input_nth[OF i_lt_rhs1] by simp
      show ?thesis
      proof (rule ext)
        fix x :: 'c
        have idx_lt_c: "c_idx x < ?c" using c_idx_lt_card .
        have j_lt_u1: "i * ?c + c_idx x < length u1"
        proof -
          have step1: "i + 1 \<le> n" using True by simp
          hence step2: "(i + 1) * ?c \<le> n * ?c" by (rule mult_le_mono1)
          hence step3: "i * ?c + ?c \<le> n * ?c"
            by (simp add: distrib_right)
          have "i * ?c + c_idx x < i * ?c + ?c" using idx_lt_c by simp
          also have "\<dots> \<le> n * ?c" using step3 .
          also have "\<dots> = length u1" using n_eq by simp
          finally show ?thesis .
        qed
        have j_lt_lhs: "i * ?c + c_idx x < length (u1 @ u2)"
          using j_lt_u1 by simp
        have lhs_at: "(?lhs ! i) x = u1 ! (i * ?c + c_idx x)"
        proof -
          have "(?lhs ! i) x = (u1 @ u2) ! (i * ?c + c_idx x)"
            using lhs_step[of x] j_lt_lhs by (simp add: Let_def)
          also have "\<dots> = u1 ! (i * ?c + c_idx x)"
            using j_lt_u1 by (simp add: nth_append)
          finally show ?thesis .
        qed
        have rhs_at: "(?rhs1 ! i) x = u1 ! (i * ?c + c_idx x)"
          using rhs1_step[of x] j_lt_u1 by (simp add: Let_def)
        show "(?lhs ! i) x = ((?rhs1 @ ?rhs2) ! i) x"
          using lhs_at rhs_at rhs_split by simp
      qed
    next
      case False
      hence n_le_i: "n \<le> i" by simp
      define i' where "i' = i - n"
      have i_eq: "i = i' + n" using n_le_i unfolding i'_def by simp
      have i_mul: "i * ?c = i' * ?c + n * ?c"
        using i_eq by (simp add: distrib_right)
      have len_rhs1_le: "length ?rhs1 \<le> i"
        using n_le_i len_rhs1 by simp
      have rhs2_idx: "i - length ?rhs1 = i'"
        using i'_def len_rhs1 by simp
      have i'_lt_rhs2: "i' < length ?rhs2"
        using i_lt len_lhs n_le_i unfolding i'_def by linarith
      have rhs_split: "(?rhs1 @ ?rhs2) ! i = ?rhs2 ! i'"
        using len_rhs1_le rhs2_idx by (simp add: nth_append)
      have rhs2_step: "\<And>x :: 'c. (?rhs2 ! i') x =
                         (let j' = i' * ?c + c_idx x
                            in if j' < length u2 then u2 ! j' else bl)"
        using encode_input_nth[OF i'_lt_rhs2] by simp
      show ?thesis
      proof (rule ext)
        fix x :: 'c
        have idx_lt_c: "c_idx x < ?c" using c_idx_lt_card .
        have j_ge_u1: "length u1 \<le> i * ?c + c_idx x"
          using i_mul n_eq n_le_i by simp
        have j_diff: "i * ?c + c_idx x - length u1 = i' * ?c + c_idx x"
          using i_mul n_eq by simp
        have lhs_lt_iff: "(i * ?c + c_idx x < length (u1 @ u2))
                            \<longleftrightarrow> (i' * ?c + c_idx x < length u2)"
          using i_mul n_eq by simp
        show "(?lhs ! i) x = ((?rhs1 @ ?rhs2) ! i) x"
        proof (cases "i' * ?c + c_idx x < length u2")
          case True
          hence j_lt_lhs: "i * ?c + c_idx x < length (u1 @ u2)"
            using lhs_lt_iff by simp
          have lhs_at: "(?lhs ! i) x = u2 ! (i' * ?c + c_idx x)"
          proof -
            have "(?lhs ! i) x = (u1 @ u2) ! (i * ?c + c_idx x)"
              using lhs_step[of x] j_lt_lhs by (simp add: Let_def)
            also have "\<dots> = u2 ! (i * ?c + c_idx x - length u1)"
              using j_ge_u1 by (simp add: nth_append)
            also have "\<dots> = u2 ! (i' * ?c + c_idx x)" using j_diff by simp
            finally show ?thesis .
          qed
          have rhs2_at: "(?rhs2 ! i') x = u2 ! (i' * ?c + c_idx x)"
            using rhs2_step[of x] True by (simp add: Let_def)
          show ?thesis using lhs_at rhs2_at rhs_split by simp
        next
          case False
          hence j_ge_lhs: "\<not> (i * ?c + c_idx x < length (u1 @ u2))"
            using lhs_lt_iff by simp
          have lhs_at: "(?lhs ! i) x = bl"
            using lhs_step[of x] j_ge_lhs by (simp add: Let_def)
          have rhs2_at: "(?rhs2 ! i') x = bl"
            using rhs2_step[of x] False by (simp add: Let_def)
          show ?thesis using lhs_at rhs2_at rhs_split by simp
        qed
      qed
    qed
  qed
qed

text \<open>Encoding the empty input gives the empty block list.
  Trivial corollary of \<open>length_encode_input\<close>: \<open>(0 + c - 1) div c
  = 0\<close> regardless of \<open>c\<close>'s value (zero in nat division when
  \<open>c = 0\<close>; zero by \<open>div_less\<close> when \<open>c > 0\<close>).\<close>

lemma encode_input_empty:
  "(encode_input bl ([] :: 'a list) :: ('c :: enum \<Rightarrow> 'a) list) = []"
proof -
  have c_pos: "0 < card (UNIV :: 'c set)"
  proof -
    have "(c_first :: 'c) \<in> UNIV" by simp
    thus ?thesis by (simp add: card_gt_0_iff)
  qed
  have div_zero: "(card (UNIV :: 'c set) - Suc 0)
                    div card (UNIV :: 'c set) = 0"
    using c_pos by (simp add: div_less)
  have "length (encode_input bl ([] :: 'a list)
                  :: ('c \<Rightarrow> 'a) list)
          = (0 + card (UNIV :: 'c set) - 1)
              div card (UNIV :: 'c set)"
    using length_encode_input[where bl = bl and u = "[] :: 'a list"]
    by simp
  also have "\<dots> = 0" using div_zero by simp
  finally have "length (encode_input bl ([] :: 'a list)
                          :: ('c \<Rightarrow> 'a) list) = 0" .
  thus ?thesis by simp
qed

text \<open>If a snoc-list is well-formed, every cell of the prefix is
  pure: well-formedness allows the *last* cell to be padded, but
  the prefix's last cell is no longer last after the snoc, so it
  must be pure.  Bridges the \<open>rev_induct\<close> step in
  \<open>encode_decode_round_trip\<close>: the IH applies to the prefix only
  if the prefix is itself well-formed (which follows from
  per-cell purity).\<close>

lemma ae_input_well_formed_init_pure:
  fixes xs :: "('c :: enum \<Rightarrow> 'a) list"
    and y :: "'c \<Rightarrow> 'a"
  assumes "ae_input_well_formed bl (xs @ [y])"
  shows "\<forall>i < length xs. is_pure_block bl (xs ! i)"
proof (intro allI impI)
  fix i assume i_lt_xs: "i < length xs"
  have i_lt: "i < length (xs @ [y])" using i_lt_xs by simp
  have not_last: "i \<noteq> length (xs @ [y]) - 1" using i_lt_xs by simp
  have at_i: "is_pure_block bl ((xs @ [y]) ! i)
                \<or> (i = length (xs @ [y]) - 1
                    \<and> is_padded_block bl ((xs @ [y]) ! i))"
    using assms i_lt unfolding ae_input_well_formed_def by blast
  hence pure: "is_pure_block bl ((xs @ [y]) ! i)" using not_last by blast
  have nth_eq: "(xs @ [y]) ! i = xs ! i"
    using i_lt_xs by (simp add: nth_append)
  show "is_pure_block bl (xs ! i)" using pure nth_eq by simp
qed

text \<open>Encoder image lies inside \<open>gamma_block (\<Sigma>_M \<union> {bl_M})\<close>:
  every cell of every block in \<open>encode_input bl_M u\<close> is
  either an input symbol from \<open>u\<close> (in \<open>\<Sigma>_M\<close>) or the
  blank \<open>bl_M\<close>.\<close>

lemma encode_input_in_gamma_block:
  fixes M :: "('q, 'a) mttm"
    and u :: "'a list"
  assumes u_sub: "set u \<subseteq> Sigma_tm M"
  shows "set (encode_input (bl_tm M) u :: ('c :: enum \<Rightarrow> 'a) list)
           \<subseteq> gamma_block (Sigma_tm M \<union> {bl_tm M})"
proof
  fix f :: "'c \<Rightarrow> 'a"
  assume f_in: "f \<in> set (encode_input (bl_tm M) u :: ('c \<Rightarrow> 'a) list)"
  let ?c = "card (UNIV :: 'c set)"
  from f_in obtain i where
    i_lt: "i < (length u + ?c - 1) div ?c"
    and f_eq: "f = (\<lambda>x. let j = i * ?c + c_idx x in
                          if j < length u then u ! j else bl_tm M)"
    unfolding encode_input_def Let_def by auto
  have "range f \<subseteq> Sigma_tm M \<union> {bl_tm M}"
  proof
    fix v
    assume "v \<in> range f"
    then obtain x :: 'c where v_eq: "v = f x" by auto
    show "v \<in> Sigma_tm M \<union> {bl_tm M}"
    proof (cases "i * ?c + c_idx x < length u")
      case True
      hence fx: "f x = u ! (i * ?c + c_idx x)"
        using f_eq by (simp add: Let_def)
      have "u ! (i * ?c + c_idx x) \<in> set u" using True by simp
      hence "u ! (i * ?c + c_idx x) \<in> Sigma_tm M" using u_sub by auto
      thus ?thesis using v_eq fx by auto
    next
      case False
      hence "f x = bl_tm M" using f_eq by (simp add: Let_def)
      thus ?thesis using v_eq by auto
    qed
  qed
  thus "f \<in> gamma_block (Sigma_tm M \<union> {bl_tm M})"
    unfolding gamma_block_def by simp
qed

text \<open>The all-blank block never appears in \<open>encode_input
  bl_M u\<close>: the cell at the canonical zero offset (\<open>c_idx x = 0\<close>)
  always lies in the input range and so is in \<open>\<Sigma>_M\<close>, not
  \<open>bl_M\<close>.  Discharges the \<open>bl_block bl_M \<notin> set w\<close>
  hypothesis for upstream call sites that feed an encoded word
  into the noncanonical / steps-bound lemmas.\<close>

lemma encode_input_no_bl_block:
  fixes M :: "('q, 'a) mttm"
    and u :: "'a list"
  assumes vM: "valid_mttm M"
      and u_sub: "set u \<subseteq> Sigma_tm M"
  shows "bl_block (bl_tm M)
           \<notin> set (encode_input (bl_tm M) u :: ('c :: enum \<Rightarrow> 'a) list)"
proof
  let ?c = "card (UNIV :: 'c set)"
  let ?N = "(length u + ?c - 1) div ?c"
  let ?xs = "enum_class.enum :: 'c list"
  let ?x0 = "?xs ! 0"
  assume bl_in: "bl_block (bl_tm M)
                   \<in> set (encode_input (bl_tm M) u :: ('c \<Rightarrow> 'a) list)"
  from bl_in obtain i where
    i_lt: "i < ?N"
    and f_eq: "(bl_block (bl_tm M) :: 'c \<Rightarrow> 'a)
                  = (\<lambda>x. let j = i * ?c + c_idx x in
                          if j < length u then u ! j else bl_tm M)"
    unfolding encode_input_def Let_def by auto
  have c_pos: "0 < ?c"
  proof -
    have "(c_first :: 'c) \<in> UNIV" by simp
    thus ?thesis by (simp add: card_gt_0_iff)
  qed
  have N_pos: "0 < ?N" using i_lt by simp
  have u_nonempty: "0 < length u"
  proof (rule ccontr)
    assume "\<not> 0 < length u"
    hence "length u = 0" by simp
    hence "?N = (?c - 1) div ?c" by simp
    also have "\<dots> = 0" using c_pos by simp
    finally have "?N = 0" .
    thus False using N_pos by simp
  qed
  have N_times_c_le: "?N * ?c \<le> length u + ?c - 1"
    using c_pos by (metis div_times_less_eq_dividend)
  have ic_lt: "i * ?c < length u"
  proof -
    have suc_le: "Suc i \<le> ?N" using i_lt by simp
    have "Suc i * ?c \<le> ?N * ?c" by (rule mult_le_mono1[OF suc_le])
    hence "i * ?c + ?c \<le> ?N * ?c" by simp
    also have "\<dots> \<le> length u + ?c - 1" by (rule N_times_c_le)
    finally have "i * ?c + ?c \<le> length u + ?c - 1" .
    thus ?thesis using c_pos u_nonempty by linarith
  qed
  have len_xs_eq: "length ?xs = ?c"
    using card_eq_length_enum[where 'c = 'c] by simp
  have len_xs: "0 < length ?xs" using c_pos len_xs_eq by simp
  have x0_idx: "c_idx ?x0 = 0"
    using c_idx_enum_nth[OF len_xs] .
  have eval_f: "(\<lambda>x. let j = i * ?c + c_idx x in
                       if j < length u then u ! j else bl_tm M) ?x0
                  = u ! (i * ?c)"
    using ic_lt x0_idx by (simp add: Let_def)
  have eval_bl: "(bl_block (bl_tm M) :: 'c \<Rightarrow> 'a) ?x0 = bl_tm M"
    unfolding bl_block_def by simp
  have "u ! (i * ?c) \<in> set u" using ic_lt by simp
  hence "u ! (i * ?c) \<in> Sigma_tm M" using u_sub by auto
  hence "u ! (i * ?c) \<noteq> bl_tm M"
    using bl_tm_notin_Sigma_tm[OF vM] by auto
  thus False using f_eq eval_f eval_bl by metis
qed

text \<open>Encoder output excludes the LE-block.  Mirror of
  \<open>encode_input_no_bl_block\<close>: the first filled position
  \<open>i \<cdot> c\<close> of any block-index \<open>i < \<lceil>|u|/c\<rceil>\<close> is
  strictly less than \<open>|u|\<close>, so the block's value at
  \<open>c_first\<close> equals \<open>u ! (i \<cdot> c) \<in> \<Sigma>_M\<close>; since
  \<open>le_tm M \<notin> \<Sigma>_tm M\<close> (substrate's \<open>valid_mttm_LE_not_Sigma\<close>),
  that value differs from \<open>le_tm M\<close>, so the block is not the
  constant-\<open>le\<close> function.  Used by \<open>alphabet_enlarge_language\<close>
  to show \<open>set (encode_input ...) \<subseteq> Sigma_tm
  (alphabet_enlarge M)\<close>.\<close>

lemma encode_input_no_LE_block:
  fixes M :: "('q, 'a) mttm"
    and u :: "'a list"
  assumes vM: "valid_mttm M"
      and u_sub: "set u \<subseteq> Sigma_tm M"
  shows "LE_block (le_tm M)
           \<notin> set (encode_input (bl_tm M) u :: ('c :: enum \<Rightarrow> 'a) list)"
proof
  let ?c = "card (UNIV :: 'c set)"
  let ?N = "(length u + ?c - 1) div ?c"
  let ?xs = "enum_class.enum :: 'c list"
  let ?x0 = "?xs ! 0"
  assume LE_in: "LE_block (le_tm M)
                   \<in> set (encode_input (bl_tm M) u :: ('c \<Rightarrow> 'a) list)"
  from LE_in obtain i where
    i_lt: "i < ?N"
    and f_eq: "(LE_block (le_tm M) :: 'c \<Rightarrow> 'a)
                  = (\<lambda>x. let j = i * ?c + c_idx x in
                          if j < length u then u ! j else bl_tm M)"
    unfolding encode_input_def Let_def by auto
  have c_pos: "0 < ?c"
  proof -
    have "(c_first :: 'c) \<in> UNIV" by simp
    thus ?thesis by (simp add: card_gt_0_iff)
  qed
  have N_pos: "0 < ?N" using i_lt by simp
  have u_nonempty: "0 < length u"
  proof (rule ccontr)
    assume "\<not> 0 < length u"
    hence "length u = 0" by simp
    hence "?N = (?c - 1) div ?c" by simp
    also have "\<dots> = 0" using c_pos by simp
    finally have "?N = 0" .
    thus False using N_pos by simp
  qed
  have N_times_c_le: "?N * ?c \<le> length u + ?c - 1"
    using c_pos by (metis div_times_less_eq_dividend)
  have ic_lt: "i * ?c < length u"
  proof -
    have suc_le: "Suc i \<le> ?N" using i_lt by simp
    have "Suc i * ?c \<le> ?N * ?c" by (rule mult_le_mono1[OF suc_le])
    hence "i * ?c + ?c \<le> ?N * ?c" by simp
    also have "\<dots> \<le> length u + ?c - 1" by (rule N_times_c_le)
    finally have "i * ?c + ?c \<le> length u + ?c - 1" .
    thus ?thesis using c_pos u_nonempty by linarith
  qed
  have len_xs_eq: "length ?xs = ?c"
    using card_eq_length_enum[where 'c = 'c] by simp
  have len_xs: "0 < length ?xs" using c_pos len_xs_eq by simp
  have x0_idx: "c_idx ?x0 = 0"
    using c_idx_enum_nth[OF len_xs] .
  have eval_f: "(\<lambda>x. let j = i * ?c + c_idx x in
                       if j < length u then u ! j else bl_tm M) ?x0
                  = u ! (i * ?c)"
    using ic_lt x0_idx by (simp add: Let_def)
  have eval_LE: "(LE_block (le_tm M) :: 'c \<Rightarrow> 'a) ?x0 = le_tm M"
    unfolding LE_block_def by simp
  have "u ! (i * ?c) \<in> set u" using ic_lt by simp
  hence "u ! (i * ?c) \<in> Sigma_tm M" using u_sub by auto
  hence "u ! (i * ?c) \<noteq> le_tm M"
    using valid_mttm_LE_not_Sigma[OF vM] by auto
  thus False using f_eq eval_f eval_LE by metis
qed

subsubsection \<open>Encoder well-formedness and round-trip\<close>

text \<open>Encoder output is well-formed: every block except
  possibly the last is pure; the last is either pure (when
  \<open>length u\<close> divides evenly) or trailing-padded (when it
  doesn't).  Discharges the \<open>ae_input_well_formed\<close> precondition
  for upstream call sites that feed an encoded word into the
  steps-bound lemma.

  This is the forward arm of the characterisation biconditional
  \<open>ae_validation_canonical_iff_encoder_image\<close> below: every
  encoder image is well-formed.  The reverse arm of that
  biconditional — every well-formed AE-input is in the encoder
  image — is not consumed by the headline language theorems
  (which are quantified only over explicit encoder-image
  inputs) and is retained there as a structural completeness
  result.\<close>

lemma encode_input_well_formed:
  fixes M :: "('q, 'a) mttm"
    and u :: "'a list"
  assumes vM: "valid_mttm M"
      and u_sub: "set u \<subseteq> Sigma_tm M"
  shows "ae_input_well_formed (bl_tm M)
           (encode_input (bl_tm M) u :: ('c :: enum \<Rightarrow> 'a) list)"
proof -
  let ?c = "card (UNIV :: 'c set)"
  let ?N = "(length u + ?c - 1) div ?c"
  let ?xs = "enum_class.enum :: 'c list"
  let ?w = "encode_input (bl_tm M) u :: ('c \<Rightarrow> 'a) list"
  have len_w: "length ?w = ?N" by (rule length_encode_input)
  have c_pos: "0 < ?c"
  proof -
    have "(c_first :: 'c) \<in> UNIV" by simp
    thus ?thesis by (simp add: card_gt_0_iff)
  qed
  have len_xs: "length ?xs = ?c"
    using card_eq_length_enum[where 'c = 'c] by simp
  have bl_notin_Sigma: "bl_tm M \<notin> Sigma_tm M"
    using bl_tm_notin_Sigma_tm[OF vM] .
  show ?thesis
    unfolding ae_input_well_formed_def
  proof (intro allI impI)
    fix s :: nat
    assume s_lt: "s < length ?w"
    hence s_lt_N: "s < ?N" using len_w by simp
    have at_s: "?w ! s
                  = (\<lambda>x. let j = s * ?c + c_idx x in
                            if j < length u then u ! j else bl_tm M)"
    proof -
      have s_lt_range: "s < length [0 ..< ?N]" using s_lt_N by simp
      have nth_range: "[0 ..< ?N] ! s = s" using s_lt_N by simp
      have map_unfold:
        "?w = map (\<lambda>i. (\<lambda>x. let j = i * ?c + c_idx x in
                                if j < length u then u ! j
                                else bl_tm M))
                  [0 ..< ?N]"
        unfolding encode_input_def Let_def by simp
      show ?thesis
        using nth_map[OF s_lt_range,
                      where f = "\<lambda>i. (\<lambda>x. let j = i * ?c + c_idx x in
                                              if j < length u then u ! j
                                              else bl_tm M)"]
              nth_range map_unfold
        by simp
    qed
    \<comment> \<open>For non-last blocks, every cell maps into the input
        range, hence the block is pure.  For the last
        block, either the input divides evenly (block is
        pure) or there is a trailing-padded prefix.\<close>
    consider (non_last) "Suc s < ?N"
           | (last) "Suc s = ?N"
      using s_lt_N by linarith
    thus "is_pure_block (bl_tm M) (?w ! s)
            \<or> (s = length ?w - 1 \<and> is_padded_block (bl_tm M) (?w ! s))"
    proof cases
      case non_last
      have all_pure: "\<forall>x :: 'c. (?w ! s) x \<noteq> bl_tm M"
      proof
        fix x :: 'c
        have idx_lt_c: "c_idx x < ?c" by (rule c_idx_lt_card)
        \<comment> \<open>For \<open>Suc s < ?N\<close>, \<open>(s + 2) * c \<le> ?N * c \<le> length u + c - 1\<close>,
            so \<open>(s + 1) * c < length u\<close>, hence
            \<open>s * c + c_idx x < (s + 1) * c < length u\<close>.\<close>
        have suc2: "Suc (Suc s) \<le> ?N" using non_last by simp
        have "Suc (Suc s) * ?c \<le> ?N * ?c"
          by (rule mult_le_mono1[OF suc2])
        also have "\<dots> \<le> length u + ?c - 1"
          using c_pos by (metis div_times_less_eq_dividend)
        finally have suc2_bound: "Suc (Suc s) * ?c \<le> length u + ?c - 1" .
        have prod_lt: "s * ?c + c_idx x < length u"
          using suc2_bound idx_lt_c c_pos by simp
        hence "(?w ! s) x = u ! (s * ?c + c_idx x)"
          using at_s by (simp add: Let_def)
        moreover have "u ! (s * ?c + c_idx x) \<in> set u"
          using prod_lt by simp
        ultimately have "(?w ! s) x \<in> Sigma_tm M" using u_sub by auto
        thus "(?w ! s) x \<noteq> bl_tm M" using bl_notin_Sigma by auto
      qed
      hence "is_pure_block (bl_tm M) (?w ! s)"
        unfolding is_pure_block_def by simp
      thus ?thesis ..
    next
      case last
      \<comment> \<open>Last block: split on whether \<open>length u\<close> is a multiple
          of \<open>?c\<close>.  Even \<open>\<longrightarrow>\<close> pure; uneven \<open>\<longrightarrow>\<close> padded with
          witness \<open>k = length u mod ?c\<close>.\<close>
      have s_eq: "s = length ?w - 1"
        using last len_w by simp
      have s_eq_pred: "s = ?N - 1" using last by simp
      have N_pos: "1 \<le> ?N" using last by simp
      have s_times_c: "s * ?c = ?N * ?c - ?c"
      proof -
        have "s * ?c = (?N - 1) * ?c" using s_eq_pred by simp
        also have "\<dots> = ?N * ?c - 1 * ?c"
          by (rule diff_mult_distrib)
        also have "\<dots> = ?N * ?c - ?c" by simp
        finally show ?thesis .
      qed
      show ?thesis
      proof (cases "length u mod ?c = 0")
        case True
        \<comment> \<open>Pure case: \<open>?N * ?c = length u\<close>, so every cell in
            block \<open>s\<close> lands in the input range.\<close>
        have N_eq: "?N * ?c = length u"
        proof -
          let ?q = "length u div ?c"
          have c_neq_0: "?c \<noteq> 0" using c_pos by simp
          have lu_eq: "length u = ?q * ?c"
            using True
            by (metis div_mult_mod_eq add.right_neutral)
          have c_minus_1_lt: "?c - 1 < ?c" using c_pos by simp
          have div_minus: "(?c - 1) div ?c = 0"
            using c_minus_1_lt by simp
          have add_assoc: "length u + ?c - 1 = length u + (?c - 1)"
            using c_pos by simp
          have "?N = (length u + (?c - 1)) div ?c"
            using add_assoc by simp
          also have "\<dots> = (?q * ?c + (?c - 1)) div ?c"
            using lu_eq by simp
          also have "\<dots> = ?q + (?c - 1) div ?c"
            by simp
          also have "\<dots> = ?q" using div_minus by simp
          finally have "?N = ?q" .
          thus ?thesis using lu_eq by simp
        qed
        have all_pure: "\<forall>x :: 'c. (?w ! s) x \<noteq> bl_tm M"
        proof
          fix x :: 'c
          have idx_lt_c: "c_idx x < ?c" by (rule c_idx_lt_card)
          have N_pos_times: "?c \<le> ?N * ?c"
            using N_pos by simp
          have prod_lt_N: "s * ?c + c_idx x < ?N * ?c"
            using s_times_c idx_lt_c c_pos N_pos_times by linarith
          hence prod_lt: "s * ?c + c_idx x < length u" using N_eq by simp
          hence "(?w ! s) x = u ! (s * ?c + c_idx x)"
            using at_s by (simp add: Let_def)
          moreover have "u ! (s * ?c + c_idx x) \<in> set u"
            using prod_lt by simp
          ultimately have "(?w ! s) x \<in> Sigma_tm M" using u_sub by auto
          thus "(?w ! s) x \<noteq> bl_tm M" using bl_notin_Sigma by auto
        qed
        hence "is_pure_block (bl_tm M) (?w ! s)"
          unfolding is_pure_block_def by simp
        thus ?thesis ..
      next
        case False
        \<comment> \<open>Padded case: take the witness \<open>k = length u mod ?c\<close>.
            Decompose \<open>length u = q\<cdot>c + k\<close> with \<open>1 \<le> k < c\<close>;
            then block \<open>s = q\<close> has \<open>s\<cdot>c + j = length u - k + j\<close>,
            which lies in the input range iff \<open>j < k\<close>.\<close>
        let ?k = "length u mod ?c"
        let ?q = "length u div ?c"
        have k_pos: "1 \<le> ?k" using False by simp
        have k_lt_c: "?k < ?c" using c_pos by simp
        have k_lt_xs: "?k < length ?xs" using k_lt_c len_xs by simp
        have lu_eq: "length u = ?q * ?c + ?k"
          by simp
        have N_eq: "?N = ?q + 1"
        proof -
          have plus_eq: "length u + ?c - 1 = ?q * ?c + (?k + ?c - 1)"
            using lu_eq k_pos by linarith
          have N_step: "?N = (?q * ?c + (?k + ?c - 1)) div ?c"
            using plus_eq by simp
          have div_step: "(?q * ?c + (?k + ?c - 1)) div ?c
                            = ?q + (?k + ?c - 1) div ?c"
            by simp
          have k_plus_c_minus_1_lt: "?k + ?c - 1 < 2 * ?c"
            using k_lt_c c_pos by linarith
          have k_plus_c_minus_1_ge: "?c \<le> ?k + ?c - 1"
            using k_pos c_pos by linarith
          have div_kpc_eq_1: "(?k + ?c - 1) div ?c = 1"
          proof -
            have rewrite: "?k + ?c - 1 = (?k - 1) + ?c"
              using k_pos c_pos by linarith
            have small: "(?k - 1) div ?c = 0"
              using k_lt_c by simp
            have c_neq_0: "?c \<noteq> 0" using c_pos by simp
            have "((?k - 1) + ?c) div ?c = (?k - 1) div ?c + 1"
              by (rule div_add_self2[OF c_neq_0])
            also have "\<dots> = 1" using small by simp
            finally show ?thesis using rewrite by simp
          qed
          show ?thesis using N_step div_step div_kpc_eq_1 by simp
        qed
        have s_eq_q: "s = ?q" using last N_eq by simp
        have s_times_c_eq: "s * ?c = length u - ?k"
        proof -
          have q_eq: "length u div ?c * ?c = length u - length u mod ?c"
            by (metis add_diff_cancel_right' div_mod_decomp)
          show ?thesis using s_eq_q q_eq by simp
        qed
        have padded: "is_padded_block (bl_tm M) (?w ! s)"
          unfolding is_padded_block_def
        proof (intro exI[of _ ?k] conjI)
          show "1 \<le> ?k" by (rule k_pos)
          show "?k < length ?xs" by (rule k_lt_xs)
          show "\<forall>x :: 'c. c_idx x < ?k \<longrightarrow> (?w ! s) x \<noteq> bl_tm M"
          proof (intro allI impI)
            fix x :: 'c
            assume idx_lt_k: "c_idx x < ?k"
            have k_le_lu: "?k \<le> length u"
              using lu_eq by linarith
            have prod_lt: "s * ?c + c_idx x < length u"
              using s_times_c_eq idx_lt_k k_le_lu by linarith
            hence "(?w ! s) x = u ! (s * ?c + c_idx x)"
              using at_s by (simp add: Let_def)
            moreover have "u ! (s * ?c + c_idx x) \<in> set u"
              using prod_lt by simp
            ultimately have "(?w ! s) x \<in> Sigma_tm M"
              using u_sub by auto
            thus "(?w ! s) x \<noteq> bl_tm M" using bl_notin_Sigma by auto
          qed
          show "\<forall>x :: 'c. ?k \<le> c_idx x \<longrightarrow> (?w ! s) x = bl_tm M"
          proof (intro allI impI)
            fix x :: 'c
            assume idx_ge_k: "?k \<le> c_idx x"
            have "s * ?c + c_idx x \<ge> length u"
              using s_times_c_eq idx_ge_k by linarith
            hence "\<not> s * ?c + c_idx x < length u" by simp
            thus "(?w ! s) x = bl_tm M"
              using at_s by (simp add: Let_def)
          qed
        qed
        thus ?thesis using s_eq by simp
      qed
    qed
  qed
qed

text \<open>Encoder \<open>\<circ>\<close> decoder is the identity on a single canonical
  block: pure cell \<open>\<rightarrow>\<close> \<open>encode_input bl (map x enum) = [x]\<close>;
  padded cell with witness \<open>k\<close> \<open>\<rightarrow>\<close>
  \<open>encode_input bl (map x (take k enum)) = [x]\<close>.  Per-cell
  identity for the round-trip.\<close>

lemma encode_decode_block:
  fixes x :: "'c :: enum \<Rightarrow> 'a"
  assumes "is_canonical_block bl x"
  shows "encode_input bl (ae_decode_block bl x)
           = ([x] :: ('c \<Rightarrow> 'a) list)"
proof (cases "is_pure_block bl x")
  case True
  have decode: "ae_decode_block bl x
                  = map x (enum_class.enum :: 'c list)"
    by (rule ae_decode_block_pure[OF True])
  show ?thesis using decode encode_input_map_enum by simp
next
  case False
  hence padded: "is_padded_block bl x"
    using assms unfolding is_canonical_block_def by blast
  obtain k where k_pos: "1 \<le> k"
    and k_lt: "k < length (enum_class.enum :: 'c list)"
    and prefix: "\<forall>y. c_idx y < k \<longrightarrow> x y \<noteq> bl"
    and suffix: "\<forall>y. c_idx y \<ge> k \<longrightarrow> x y = bl"
    using padded unfolding is_padded_block_def by blast
  have decode: "ae_decode_block bl x
                  = map x (take k (enum_class.enum :: 'c list))"
    by (rule ae_decode_block_padded[OF k_lt prefix suffix])
  have m_pos: "0 < k" using k_pos by simp
  have m_le: "k \<le> length (enum_class.enum :: 'c list)" using k_lt by simp
  have enc: "encode_input bl (map x (take k (enum_class.enum :: 'c list)))
               = ([x] :: ('c \<Rightarrow> 'a) list)"
    using encode_input_map_take_enum[OF m_pos m_le suffix] .
  show ?thesis using decode enc by simp
qed

text \<open>The round-trip: for any well-formed block list \<open>w\<close>,
  encoding the decoder's output reproduces \<open>w\<close>.  By \<open>rev_induct\<close>:
  the empty case is trivial; the snoc step uses
  \<open>encode_input_append_div\<close> (the prefix decodes to a length
  divisible by \<open>c\<close>, since all of \<open>w\<close>'s prefix cells are pure)
  plus \<open>encode_decode_block\<close> on the last block.\<close>

lemma encode_decode_round_trip:
  fixes w :: "('c :: enum \<Rightarrow> 'a) list"
  assumes wf: "ae_input_well_formed bl w"
  shows "encode_input bl (ae_decode_input bl w) = w"
proof -
  have main: "ae_input_well_formed bl w
                \<longrightarrow> encode_input bl (ae_decode_input bl w) = w"
  proof (induct w rule: rev_induct)
    case Nil
    show ?case
      by (simp add: ae_decode_input_def encode_input_empty)
  next
    case (snoc x xs)
    show ?case
    proof
      assume wf_snoc: "ae_input_well_formed bl (xs @ [x])"
      have all_pure: "\<forall>i < length xs. is_pure_block bl (xs ! i)"
        using wf_snoc by (rule ae_input_well_formed_init_pure)
      have wf_xs: "ae_input_well_formed bl xs"
        unfolding ae_input_well_formed_def using all_pure by blast
      have ih: "encode_input bl (ae_decode_input bl xs) = xs"
        using snoc.hyps wf_xs by blast
      have x_canonical: "is_canonical_block bl x"
      proof -
        let ?n = "length (xs @ [x]) - 1"
        have x_eq: "(xs @ [x]) ! ?n = x" by simp
        have n_lt: "?n < length (xs @ [x])" by simp
        have "is_pure_block bl ((xs @ [x]) ! ?n)
                \<or> (?n = length (xs @ [x]) - 1
                    \<and> is_padded_block bl ((xs @ [x]) ! ?n))"
          using wf_snoc n_lt unfolding ae_input_well_formed_def by blast
        hence "is_pure_block bl x \<or> is_padded_block bl x"
          using x_eq by simp
        thus ?thesis unfolding is_canonical_block_def .
      qed
      have block_eq: "encode_input bl (ae_decode_block bl x) = [x]"
        by (rule encode_decode_block[OF x_canonical])
      have len_xs_decode:
        "card (UNIV :: 'c set) dvd length (ae_decode_input bl xs)"
      proof -
        have "length (ae_decode_input bl xs)
                = length xs * card (UNIV :: 'c set)"
          by (rule length_ae_decode_input_pure[OF all_pure])
        thus ?thesis by simp
      qed
      have decode_split:
        "ae_decode_input bl (xs @ [x])
           = ae_decode_input bl xs @ ae_decode_block bl x"
        by (simp add: ae_decode_input_def)
      have "encode_input bl (ae_decode_input bl (xs @ [x]))
              = encode_input bl
                  (ae_decode_input bl xs @ ae_decode_block bl x)"
        using decode_split by simp
      also have "(encode_input bl
                     (ae_decode_input bl xs @ ae_decode_block bl x)
                       :: ('c \<Rightarrow> 'a) list)
                  = encode_input bl (ae_decode_input bl xs)
                      @ encode_input bl (ae_decode_block bl x)"
        by (rule encode_input_append_div[OF len_xs_decode])
      also have "\<dots> = xs @ encode_input bl (ae_decode_block bl x)"
        using ih by simp
      also have "\<dots> = xs @ [x]" using block_eq by simp
      finally show "encode_input bl (ae_decode_input bl (xs @ [x]))
                      = xs @ [x]" .
    qed
  qed
  show ?thesis using main wf by blast
qed

end
