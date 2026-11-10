theory AlphabetEnlargement_Codec
  imports AlphabetEnlargement_Window
begin

subsection \<open>Encoder and decoder structural lemmas\<close>

subsubsection \<open>Decoder structural lemmas and ceiling-div arithmetic\<close>

text \<open>Decoder structural lemmas.  \<open>ae_decode_block_pure\<close>
  resolves to the image of all of \<open>[0..<m]\<close> (length \<open>m\<close>); the analogous
  fact for padded blocks (length = the padded witness)
  splits \<open>[0..<m]\<close> at the witness index and uses the
  takeWhile / append decomposition.\<close>

lemma ae_decode_block_pure:
  fixes f :: "nat \<Rightarrow> 'a"
  assumes "is_pure_block m bl f"
  shows "ae_decode_block m bl f
           = map f [0..<m]"
proof -
  have all_neq: "\<forall>a \<in> set (map f [0..<m]). a \<noteq> bl"
    using assms unfolding is_pure_block_def by auto
  show ?thesis
    unfolding ae_decode_block_def
    using all_neq by (simp add: takeWhile_eq_all_conv)
qed

lemma length_ae_decode_block_pure:
  fixes f :: "nat \<Rightarrow> 'a"
  assumes "is_pure_block m bl f"
  shows "length (ae_decode_block m bl f) = m"
  using ae_decode_block_pure[OF assms]
  by simp

lemma ae_decode_block_padded:
  fixes f :: "nat \<Rightarrow> 'a"
  assumes k_lt: "k < length [0..<m]"
      and prefix: "\<forall>x<m. x < k \<longrightarrow> f x \<noteq> bl"
      and suffix: "\<forall>x<m. k \<le> x \<longrightarrow> f x = bl"
  shows "ae_decode_block m bl f
           = map f (take k [0..<m])"
proof -
  let ?xs = "[0..<m] :: nat list"
  let ?P = "\<lambda>a. a \<noteq> bl"
  have at_k: "f (?xs ! k) = bl"
  proof -
    have "(?xs ! k) = k" using k_lt by simp
    thus ?thesis using suffix k_lt by simp
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
    have nth_upt_i: "(?xs ! i) = i" using i_lt_n by simp
    show "?P a" using prefix nth_upt_i i_lt_k i_lt_n a_alt by simp
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
  "ae_decode_input m bl (xs @ ys)
     = ae_decode_input m bl xs @ ae_decode_input m bl ys"
  by (simp add: ae_decode_input_def)

lemma length_ae_decode_input_pure:
  fixes xs :: "(nat \<Rightarrow> 'a) list"
  assumes "\<forall>s < length xs. is_pure_block m bl (xs ! s)"
  shows "length (ae_decode_input m bl xs) = length xs * m"
  using assms
proof (induction xs)
  case Nil
  show ?case by (simp add: ae_decode_input_def)
next
  case (Cons x xs)
  have x_pure: "is_pure_block m bl x"
    using Cons.prems[rule_format, of 0] by simp
  have rest_pure: "\<forall>s < length xs. is_pure_block m bl (xs ! s)"
  proof (intro allI impI)
    fix s assume "s < length xs"
    hence "Suc s < length (x # xs)" by simp
    thus "is_pure_block m bl (xs ! s)"
      using Cons.prems[rule_format, of "Suc s"] by simp
  qed
  have "length (ae_decode_input m bl (x # xs))
          = length (ae_decode_block m bl x) + length (ae_decode_input m bl xs)"
    by (simp add: ae_decode_input_def)
  also have "\<dots> = m + length xs * m"
    using length_ae_decode_block_pure[OF x_pure] Cons.IH[OF rest_pure]
    by simp
  also have "\<dots> = length (x # xs) * m"
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
  have "(k + c - 1) div c = ((k + c - 1) - c) div c + 1"
    using lo assms by (auto simp: le_div_geq)
  also have "(k + c - 1) - c = k - 1" by simp
  also have "(k - 1) div c = 0" using assms by simp
  finally show ?thesis by simp
qed

subsubsection \<open>Encoder list operations and image properties\<close>

text \<open>Encoding an input that is the image of a block function
  over \<open>[0..<m]\<close> yields the singleton list
  containing that block.  Used by the round-trip lemma in the
  forward direction of \<open>ae_validation_canonical_iff_encoder_image\<close>:
  a pure last-block decodes to its image over all of \<open>[0..<m]\<close>, and that
  image re-encodes back to the original block.\<close>

lemma encode_input_map_symbols:
  fixes f :: "nat \<Rightarrow> 'a"
  assumes m_pos: "0 < m"
      and f_ext: "\<forall>x. m \<le> x \<longrightarrow> f x = undefined"
  shows "encode_input m bl (map f [0..<m])
           = ([f] :: (nat \<Rightarrow> 'a) list)"
proof -
  let ?c = "m"
  let ?xs = "[0..<m] :: nat list"
  let ?w = "map f ?xs"
  let ?lhs = "encode_input m bl ?w :: (nat \<Rightarrow> 'a) list"
  have len_xs: "length ?xs = ?c"
    by simp
  have len_w: "length ?w = ?c" using len_xs by simp
  have c_pos: "0 < ?c" by (rule m_pos)
  have len_lhs: "length ?lhs = 1"
  proof -
    have "length ?lhs = (length ?w + ?c - 1) div ?c"
      using length_encode_input[where bl = bl and u = "?w"] .
    also have "\<dots> = (?c + ?c - 1) div ?c" using len_w by simp
    also have "\<dots> = 1" using ceil_div_2c_minus_1[OF c_pos] .
    finally show ?thesis .
  qed
  have zero_lt_lhs: "0 < length ?lhs" using len_lhs by simp
  have nth0_at: "\<And>x :: nat. (?lhs ! 0) x = f x"
  proof -
    fix x :: nat
    show "(?lhs ! 0) x = f x"
    proof (cases "x < m")
      case x_lt: True
      have idx_lt_xs: "x < length ?xs"
        using x_lt by simp
      have idx_lt_w: "x < length ?w" using idx_lt_xs by simp
      have nth_step: "(?lhs ! 0) x =
                         (let j = 0 * ?c + x
                            in if j < length ?w then ?w ! j else bl)"
        by (rule encode_input_nth[OF zero_lt_lhs x_lt])
      have w_at: "?w ! x = f x"
        using idx_lt_xs x_lt by (simp add: nth_map)
      show ?thesis
        using nth_step idx_lt_w w_at by (simp add: Let_def)
    next
      case False
      then show ?thesis
        using encode_input_nth_out[OF zero_lt_lhs] f_ext by simp
    qed
  qed
  have nth0: "?lhs ! 0 = f"
    using nth0_at by (rule ext)
  show ?thesis
  proof (rule nth_equalityI)
    show "length ?lhs = length ([f] :: (nat \<Rightarrow> 'a) list)"
      using len_lhs by simp
  next
    fix i assume i_lt: "i < length ?lhs"
    hence "i = 0" using len_lhs by simp
    thus "?lhs ! i = ([f] :: (nat \<Rightarrow> 'a) list) ! i"
      using nth0 by simp
  qed
qed

text \<open>Generalisation of \<open>encode_input_map_symbols\<close>: encoding the
  image of \<open>f\<close> over a length-\<open>p\<close> prefix of
  \<open>[0..<m]\<close> (where \<open>0 < p \<le> m\<close>, and \<open>f x = bl\<close> on the
  out-of-prefix indices) yields the singleton list \<open>[f]\<close>.
  Used by the round-trip in the forward direction of
  \<open>ae_validation_canonical_iff_encoder_image\<close>: a padded last
  block decodes to its image over that prefix, and that prefix
  re-encodes back to the original block.\<close>

lemma encode_input_map_take_symbols:
  fixes f :: "nat \<Rightarrow> 'a"
  assumes m_pos: "0 < p"
      and m_le: "p \<le> length [0..<m]"
      and pad: "\<forall>x<m. x \<ge> p \<longrightarrow> f x = bl"
      and f_ext: "\<forall>x. m \<le> x \<longrightarrow> f x = undefined"
  shows "encode_input m bl (map f (take p [0..<m]))
           = ([f] :: (nat \<Rightarrow> 'a) list)"
proof -
  let ?c = "m"
  let ?xs = "[0..<m] :: nat list"
  let ?w = "map f (take p ?xs)"
  let ?lhs = "encode_input m bl ?w :: (nat \<Rightarrow> 'a) list"
  have len_xs: "length ?xs = ?c" by simp
  have m_le_c: "p \<le> ?c" using m_le len_xs by simp
  have c_pos: "0 < ?c" using m_pos m_le_c by linarith
  have len_take: "length (take p ?xs) = p"
    using m_le by simp
  have len_w: "length ?w = p" using len_take by simp
  have len_lhs: "length ?lhs = 1"
  proof -
    have "length ?lhs = (length ?w + ?c - 1) div ?c"
      using length_encode_input[where bl = bl and u = "?w"] .
    also have "\<dots> = (p + ?c - 1) div ?c" using len_w by simp
    also have "\<dots> = 1"
      using ceil_div_k_plus_c_minus_1[OF c_pos m_pos m_le_c] .
    finally show ?thesis .
  qed
  have zero_lt_lhs: "0 < length ?lhs" using len_lhs by simp
  have nth0_at: "\<And>x :: nat. (?lhs ! 0) x = f x"
  proof -
    fix x :: nat
    show "(?lhs ! 0) x = f x"
    proof (cases "x < m")
      case False
      then show ?thesis
        using encode_input_nth_out[OF zero_lt_lhs] f_ext by simp
    next
      case x_lt: True
    have nth_step: "(?lhs ! 0) x =
                       (let j = 0 * ?c + x
                          in if j < length ?w then ?w ! j else bl)"
      by (rule encode_input_nth[OF zero_lt_lhs x_lt])
    show "(?lhs ! 0) x = f x"
    proof (cases "x < p")
      case True
      hence j_lt_w: "x < length ?w" using len_w by simp
      have w_at: "?w ! x = f x"
      proof -
        have take_at: "(take p ?xs) ! x = ?xs ! x"
          using True by simp
        have map_at: "?w ! x = f ((take p ?xs) ! x)"
          using True len_take by (simp add: nth_map)
        have "?w ! x = f (?xs ! x)"
          using map_at take_at by simp
        also have "?xs ! x = x" using x_lt by simp
        finally show ?thesis .
      qed
      show ?thesis using nth_step j_lt_w w_at by (simp add: Let_def)
    next
      case False
      hence m_le_idx: "p \<le> x" by simp
      have f_eq_bl: "f x = bl" using pad m_le_idx x_lt by simp
      have body_bl: "(let j = 0 * ?c + x
                        in if j < length ?w then ?w ! j else bl) = bl"
        using m_le_idx m_le len_w by (auto simp: Let_def)
      have lhs_bl: "(?lhs ! 0) x = bl"
        using nth_step body_bl by simp
      show ?thesis using lhs_bl f_eq_bl by simp
    qed
    qed
  qed
  have nth0: "?lhs ! 0 = f" using nth0_at by (rule ext)
  show ?thesis
  proof (rule nth_equalityI)
    show "length ?lhs = length ([f] :: (nat \<Rightarrow> 'a) list)"
      using len_lhs by simp
  next
    fix i assume i_lt: "i < length ?lhs"
    hence "i = 0" using len_lhs by simp
    thus "?lhs ! i = ([f] :: (nat \<Rightarrow> 'a) list) ! i"
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
  assumes c_div: "m dvd length u1"
      and m_pos: "0 < m"
  shows "(encode_input m bl (u1 @ u2) :: (nat \<Rightarrow> 'a) list)
           = encode_input m bl u1 @ encode_input m bl u2"
proof -
  let ?c = "m"
  let ?lhs = "encode_input m bl (u1 @ u2) :: (nat \<Rightarrow> 'a) list"
  let ?rhs1 = "encode_input m bl u1 :: (nat \<Rightarrow> 'a) list"
  let ?rhs2 = "encode_input m bl u2 :: (nat \<Rightarrow> 'a) list"
  have c_pos: "0 < ?c" by (rule m_pos)
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
      by (rule div_mult_self1[OF c_ne])
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
    have lhs_step: "\<And>x :: nat. x < m \<Longrightarrow> (?lhs ! i) x =
                       (let j = i * ?c + x
                          in if j < length (u1 @ u2)
                                then (u1 @ u2) ! j else bl)"
      using encode_input_nth[OF i_lt] by simp
    show "?lhs ! i = (?rhs1 @ ?rhs2) ! i"
    proof (cases "i < n")
      case True
      have i_lt_rhs1: "i < length ?rhs1" using True len_rhs1 by simp
      have rhs_split: "(?rhs1 @ ?rhs2) ! i = ?rhs1 ! i"
        using i_lt_rhs1 by (simp add: nth_append)
      have rhs1_step: "\<And>x :: nat. x < m \<Longrightarrow> (?rhs1 ! i) x =
                         (let j = i * ?c + x
                            in if j < length u1 then u1 ! j else bl)"
        using encode_input_nth[OF i_lt_rhs1] by simp
      show ?thesis
      proof (rule ext)
        fix x :: nat
        show "(?lhs ! i) x = ((?rhs1 @ ?rhs2) ! i) x"
        proof (cases "x < m")
          case False
          then show ?thesis
            using encode_input_nth_out[OF i_lt] encode_input_nth_out[OF i_lt_rhs1]
              rhs_split by simp
        next
          case x_lt: True
        have j_lt_u1: "i * ?c + x < length u1"
        proof -
          have step1: "i + 1 \<le> n" using True by simp
          hence step2: "(i + 1) * ?c \<le> n * ?c" by (rule mult_le_mono1)
          hence step3: "i * ?c + ?c \<le> n * ?c"
            by (simp add: distrib_right)
          have "i * ?c + x < i * ?c + ?c" using x_lt by simp
          also have "\<dots> \<le> n * ?c" using step3 .
          also have "\<dots> = length u1" using n_eq by simp
          finally show ?thesis .
        qed
        have j_lt_lhs: "i * ?c + x < length (u1 @ u2)"
          using j_lt_u1 by simp
        have lhs_at: "(?lhs ! i) x = u1 ! (i * ?c + x)"
        proof -
          have "(?lhs ! i) x = (u1 @ u2) ! (i * ?c + x)"
            using lhs_step[OF x_lt] j_lt_lhs by (simp add: Let_def)
          also have "\<dots> = u1 ! (i * ?c + x)"
            using j_lt_u1 by (simp add: nth_append)
          finally show ?thesis .
        qed
        have rhs_at: "(?rhs1 ! i) x = u1 ! (i * ?c + x)"
          using rhs1_step[OF x_lt] j_lt_u1 by (simp add: Let_def)
        show "(?lhs ! i) x = ((?rhs1 @ ?rhs2) ! i) x"
          using lhs_at rhs_at rhs_split by simp
        qed
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
      have rhs2_step: "\<And>x :: nat. x < m \<Longrightarrow> (?rhs2 ! i') x =
                         (let j' = i' * ?c + x
                            in if j' < length u2 then u2 ! j' else bl)"
        using encode_input_nth[OF i'_lt_rhs2] by simp
      show ?thesis
      proof (rule ext)
        fix x :: nat
        show "(?lhs ! i) x = ((?rhs1 @ ?rhs2) ! i) x"
        proof (cases "x < m")
          case False
          then show ?thesis
            using encode_input_nth_out[OF i_lt] encode_input_nth_out[OF i'_lt_rhs2]
              rhs_split by simp
        next
          case x_lt: True
        have j_ge_u1: "length u1 \<le> i * ?c + x"
          using i_mul n_eq n_le_i by simp
        have j_diff: "i * ?c + x - length u1 = i' * ?c + x"
          using i_mul n_eq by simp
        have lhs_lt_iff: "(i * ?c + x < length (u1 @ u2))
                            \<longleftrightarrow> (i' * ?c + x < length u2)"
          using i_mul n_eq by simp
        show "(?lhs ! i) x = ((?rhs1 @ ?rhs2) ! i) x"
        proof (cases "i' * ?c + x < length u2")
          case True
          hence j_lt_lhs: "i * ?c + x < length (u1 @ u2)"
            using lhs_lt_iff by simp
          have lhs_at: "(?lhs ! i) x = u2 ! (i' * ?c + x)"
          proof -
            have "(?lhs ! i) x = (u1 @ u2) ! (i * ?c + x)"
              using lhs_step[OF x_lt] j_lt_lhs by (simp add: Let_def)
            also have "\<dots> = u2 ! (i * ?c + x - length u1)"
              using j_ge_u1 by (simp add: nth_append)
            also have "\<dots> = u2 ! (i' * ?c + x)" using j_diff by simp
            finally show ?thesis .
          qed
          have rhs2_at: "(?rhs2 ! i') x = u2 ! (i' * ?c + x)"
            using rhs2_step[OF x_lt] True by (simp add: Let_def)
          show ?thesis using lhs_at rhs2_at rhs_split by simp
        next
          case False
          hence j_ge_lhs: "\<not> (i * ?c + x < length (u1 @ u2))"
            using lhs_lt_iff by simp
          have lhs_at: "(?lhs ! i) x = bl"
            using lhs_step[OF x_lt] j_ge_lhs by (simp add: Let_def)
          have rhs2_at: "(?rhs2 ! i') x = bl"
            using rhs2_step[OF x_lt] False by (simp add: Let_def)
          show ?thesis using lhs_at rhs2_at rhs_split by simp
        qed
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
  "(encode_input m bl ([] :: 'a list) :: (nat \<Rightarrow> 'a) list) = []"
  by (cases m) (simp_all add: encode_input_def)

text \<open>If a snoc-list is well-formed, every cell of the prefix is
  pure: well-formedness allows the \<^emph>\<open>last\<close> cell to be padded, but
  the prefix's last cell is no longer last after the snoc, so it
  must be pure.  Bridges the \<open>rev_induct\<close> step in
  \<open>encode_decode_round_trip\<close>: the IH applies to the prefix only
  if the prefix is itself well-formed (which follows from
  per-cell purity).\<close>

lemma ae_input_well_formed_init_pure:
  fixes xs :: "(nat \<Rightarrow> 'a) list"
    and y :: "nat \<Rightarrow> 'a"
  assumes "ae_input_well_formed m bl (xs @ [y])"
  shows "\<forall>i < length xs. is_pure_block m bl (xs ! i)"
proof (intro allI impI)
  fix i assume i_lt_xs: "i < length xs"
  have i_lt: "i < length (xs @ [y])" using i_lt_xs by simp
  have not_last: "i \<noteq> length (xs @ [y]) - 1" using i_lt_xs by simp
  have at_i: "is_pure_block m bl ((xs @ [y]) ! i)
                \<or> (i = length (xs @ [y]) - 1
                    \<and> is_padded_block m bl ((xs @ [y]) ! i))"
    using assms i_lt unfolding ae_input_well_formed_def by blast
  hence pure: "is_pure_block m bl ((xs @ [y]) ! i)" using not_last by blast
  have nth_eq: "(xs @ [y]) ! i = xs ! i"
    using i_lt_xs by (simp add: nth_append)
  show "is_pure_block m bl (xs ! i)" using pure nth_eq by simp
qed

text \<open>Encoder image lies inside \<open>gamma_block (\<Sigma>_M \<union> {bl_M})\<close>:
  every cell of every block in \<open>encode_input bl_M u\<close> is
  either an input symbol from \<open>u\<close> (in \<open>\<Sigma>_M\<close>) or the
  blank \<open>bl_M\<close>.\<close>

lemma encode_input_in_gamma_block:
  fixes M :: "('q, 'a) ktm"
    and u :: "'a list"
  assumes u_sub: "set u \<subseteq> Sigma_ktm M"
  shows "set (encode_input m (bl_ktm M) u :: (nat \<Rightarrow> 'a) list)
           \<subseteq> gamma_block m (Sigma_ktm M \<union> {bl_ktm M})"
proof
  fix f :: "nat \<Rightarrow> 'a"
  assume f_in: "f \<in> set (encode_input m (bl_ktm M) u :: (nat \<Rightarrow> 'a) list)"
  from f_in obtain i where
    f_eq: "f = restrict (\<lambda>x. let j = i * m + x in
                          if j < length u then u ! j else bl_ktm M) {..<m}"
    unfolding encode_input_def Let_def by auto
  have cell: "f x \<in> Sigma_ktm M \<union> {bl_ktm M}" if x_lt: "x < m" for x
  proof (cases "i * m + x < length u")
    case True
    then have "f x = u ! (i * m + x)" using f_eq x_lt by (simp add: Let_def)
    moreover have "u ! (i * m + x) \<in> set u" using True by simp
    ultimately show ?thesis using u_sub by auto
  next
    case False
    then have "f x = bl_ktm M" using f_eq x_lt by (simp add: Let_def)
    then show ?thesis by simp
  qed
  have out: "f x = undefined" if "m \<le> x" for x
    using f_eq that by simp
  show "f \<in> gamma_block m (Sigma_ktm M \<union> {bl_ktm M})"
    unfolding gamma_block_def using cell out by blast
qed

text \<open>A constant block whose symbol is not in the input is not among the
  encoded blocks: every block holds an input symbol in its first cell,
  because each block starts inside the input.  The blank and endmarker
  blocks below are its two instances.\<close>

lemma encode_input_no_const_block:
  fixes u :: "'a list"
  assumes z_notin: "z \<notin> set u"
  shows "restrict (\<lambda>_. z) {..<m} \<notin> set (encode_input m b u :: (nat \<Rightarrow> 'a) list)"
proof
  let ?c = "m"
  let ?N = "(length u + ?c - 1) div ?c"
  let ?xs = "[0..<m] :: nat list"
  let ?x0 = "?xs ! 0"
  assume z_in: "restrict (\<lambda>_. z) {..<m} \<in> set (encode_input m b u :: (nat \<Rightarrow> 'a) list)"
  from z_in obtain i where
    i_lt: "i < ?N"
    and f_eq: "(restrict (\<lambda>_. z) {..<m} :: nat \<Rightarrow> 'a)
                  = restrict (\<lambda>x. let j = i * ?c + x in
                          if j < length u then u ! j else b) {..<m}"
    unfolding encode_input_def Let_def by auto
  have c_pos: "0 < ?c" using i_lt by (cases m) auto
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
    by simp
  have len_xs: "0 < length ?xs" using c_pos len_xs_eq by simp
  have x0_idx: "?x0 = 0"
    using len_xs by simp
  have x0_lt: "?x0 < m" using len_xs len_xs_eq by (simp add: c_pos)
  have eval_f: "restrict (\<lambda>x. let j = i * ?c + x in
                       if j < length u then u ! j else b) {..<m} ?x0
                  = u ! (i * ?c)"
    using ic_lt x0_idx x0_lt by (simp add: Let_def)
  have "u ! (i * ?c) \<in> set u" using ic_lt by simp
  hence "u ! (i * ?c) \<noteq> z" using z_notin by auto
  moreover have "restrict (\<lambda>_. z) {..<m} ?x0 = z" using x0_lt by simp
  ultimately show False using f_eq eval_f by metis
qed

lemma encode_input_no_bl_block:
  fixes M :: "('q, 'a) ktm"
    and u :: "'a list"
  assumes vM: "valid_ktm M"
      and u_sub: "set u \<subseteq> Sigma_ktm M"
  shows "bl_block m (bl_ktm M)
           \<notin> set (encode_input m (bl_ktm M) u :: (nat \<Rightarrow> 'a) list)"
  unfolding bl_block_def
  by (rule encode_input_no_const_block)
     (use u_sub valid_ktm_blank_not_Sigma [OF vM] in blast)

lemma encode_input_no_LE_block:
  fixes M :: "('q, 'a) ktm"
    and u :: "'a list"
  assumes vM: "valid_ktm M"
      and u_sub: "set u \<subseteq> Sigma_ktm M"
  shows "LE_block m (le_ktm M)
           \<notin> set (encode_input m (bl_ktm M) u :: (nat \<Rightarrow> 'a) list)"
  unfolding LE_block_def
  by (rule encode_input_no_const_block)
     (use u_sub valid_ktm_LE_not_Sigma [OF vM] in blast)

subsubsection \<open>Encoder well-formedness and round-trip\<close>

text \<open>Encoder output is well-formed: every block except
  possibly the last is pure; the last is either pure (when
  \<open>length u\<close> divides evenly) or trailing-padded (when it
  doesn't).  Discharges the \<open>ae_input_well_formed\<close> precondition
  for upstream call sites that feed an encoded word into the
  steps-bound lemma.

  This is the forward direction of the characterisation biconditional
  \<open>ae_validation_canonical_iff_encoder_image\<close> below: every
  encoder image is well-formed.  The reverse direction of that
  biconditional — every well-formed AE-input is in the encoder
  image — is not consumed by the headline language theorems
  (which are quantified only over explicit encoder-image
  inputs) and is retained there as a structural completeness
  result.\<close>

lemma encode_input_well_formed:
  fixes M :: "('q, 'a) ktm"
    and u :: "'a list"
  assumes vM: "valid_ktm M"
      and u_sub: "set u \<subseteq> Sigma_ktm M"
  shows "ae_input_well_formed m (bl_ktm M)
           (encode_input m (bl_ktm M) u :: (nat \<Rightarrow> 'a) list)"
proof -
  let ?c = "m"
  let ?N = "(length u + ?c - 1) div ?c"
  let ?xs = "[0..<m] :: nat list"
  let ?w = "encode_input m (bl_ktm M) u :: (nat \<Rightarrow> 'a) list"
  have len_w: "length ?w = ?N" by (rule length_encode_input)
  have len_xs: "length ?xs = ?c"
    by simp
  have bl_notin_Sigma: "bl_ktm M \<notin> Sigma_ktm M"
    using valid_ktm_blank_not_Sigma[OF vM] .
  show ?thesis
    unfolding ae_input_well_formed_def
  proof (intro allI impI)
    fix s :: nat
    assume s_lt: "s < length ?w"
    hence s_lt_N: "s < ?N" using len_w by simp
    have c_pos: "0 < ?c" using s_lt_N by (cases m) auto
    have at_s: "?w ! s
                  = restrict (\<lambda>x. let j = s * ?c + x in
                            if j < length u then u ! j else bl_ktm M) {..<m}"
    proof -
      have s_lt_range: "s < length [0 ..< ?N]" using s_lt_N by simp
      have nth_range: "[0 ..< ?N] ! s = s" using s_lt_N by simp
      have map_unfold:
        "?w = map (\<lambda>i. restrict (\<lambda>x. let j = i * ?c + x in
                                if j < length u then u ! j
                                else bl_ktm M) {..<m})
                  [0 ..< ?N]"
        unfolding encode_input_def Let_def by simp
      show ?thesis
        using nth_map[OF s_lt_range,
                      where f = "\<lambda>i. restrict (\<lambda>x. let j = i * ?c + x in
                                              if j < length u then u ! j
                                              else bl_ktm M) {..<m}"]
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
    thus "is_pure_block m (bl_ktm M) (?w ! s)
            \<or> (s = length ?w - 1 \<and> is_padded_block m (bl_ktm M) (?w ! s))"
    proof cases
      case non_last
      have all_pure: "\<forall>x<m. (?w ! s) x \<noteq> bl_ktm M"
      proof (intro allI impI)
        fix x :: nat
        assume x_lt: "x < m"
        \<comment> \<open>For \<open>Suc s < ?N\<close>, \<open>(s + 2) * c \<le> ?N * c \<le> length u + c - 1\<close>,
            so \<open>(s + 1) * c < length u\<close>, hence
            \<open>s * c + x < (s + 1) * c < length u\<close>.\<close>
        have suc2: "Suc (Suc s) \<le> ?N" using non_last by simp
        have "Suc (Suc s) * ?c \<le> ?N * ?c"
          by (rule mult_le_mono1[OF suc2])
        also have "\<dots> \<le> length u + ?c - 1"
          using c_pos by (metis div_times_less_eq_dividend)
        finally have suc2_bound: "Suc (Suc s) * ?c \<le> length u + ?c - 1" .
        have prod_lt: "s * ?c + x < length u"
          using suc2_bound x_lt c_pos by simp
        hence "(?w ! s) x = u ! (s * ?c + x)"
          using at_s x_lt by (simp add: Let_def)
        moreover have "u ! (s * ?c + x) \<in> set u"
          using prod_lt by simp
        ultimately have "(?w ! s) x \<in> Sigma_ktm M" using u_sub by auto
        thus "(?w ! s) x \<noteq> bl_ktm M" using bl_notin_Sigma by auto
      qed
      hence "is_pure_block m (bl_ktm M) (?w ! s)"
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
            by (rule div_mult_self3) (use c_pos in simp)
          also have "\<dots> = ?q" using div_minus by simp
          finally have "?N = ?q" .
          thus ?thesis using lu_eq by simp
        qed
        have all_pure: "\<forall>x<m. (?w ! s) x \<noteq> bl_ktm M"
        proof (intro allI impI)
          fix x :: nat
          assume x_lt: "x < m"
          have N_pos_times: "?c \<le> ?N * ?c"
            using N_pos by simp
          have prod_lt_N: "s * ?c + x < ?N * ?c"
            using s_times_c x_lt c_pos N_pos_times by linarith
          hence prod_lt: "s * ?c + x < length u" using N_eq by simp
          hence "(?w ! s) x = u ! (s * ?c + x)"
            using at_s x_lt by (simp add: Let_def)
          moreover have "u ! (s * ?c + x) \<in> set u"
            using prod_lt by simp
          ultimately have "(?w ! s) x \<in> Sigma_ktm M" using u_sub by auto
          thus "(?w ! s) x \<noteq> bl_ktm M" using bl_notin_Sigma by auto
        qed
        hence "is_pure_block m (bl_ktm M) (?w ! s)"
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
            by (rule div_mult_self3) (use c_pos in simp)
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
        have padded: "is_padded_block m (bl_ktm M) (?w ! s)"
          unfolding is_padded_block_def
        proof (intro exI[of _ ?k] conjI)
          show "1 \<le> ?k" by (rule k_pos)
          show "?k < length ?xs" by (rule k_lt_xs)
          show "\<forall>x<m. x < ?k \<longrightarrow> (?w ! s) x \<noteq> bl_ktm M"
          proof (intro allI impI)
            fix x :: nat
            assume x_lt: "x < m" and idx_lt_k: "x < ?k"
            have k_le_lu: "?k \<le> length u"
              using lu_eq by linarith
            have prod_lt: "s * ?c + x < length u"
              using s_times_c_eq idx_lt_k k_le_lu by linarith
            hence "(?w ! s) x = u ! (s * ?c + x)"
              using at_s x_lt by (simp add: Let_def)
            moreover have "u ! (s * ?c + x) \<in> set u"
              using prod_lt by simp
            ultimately have "(?w ! s) x \<in> Sigma_ktm M"
              using u_sub by auto
            thus "(?w ! s) x \<noteq> bl_ktm M" using bl_notin_Sigma by auto
          qed
          show "\<forall>x<m. ?k \<le> x \<longrightarrow> (?w ! s) x = bl_ktm M"
          proof (intro allI impI)
            fix x :: nat
            assume x_lt: "x < m" and idx_ge_k: "?k \<le> x"
            have "s * ?c + x \<ge> length u"
              using s_times_c_eq idx_ge_k by linarith
            hence "\<not> s * ?c + x < length u" by simp
            thus "(?w ! s) x = bl_ktm M"
              using at_s x_lt by (simp add: Let_def)
          qed
        qed
        thus ?thesis using s_eq by simp
      qed
    qed
  qed
qed

text \<open>Encoder \<open>\<circ>\<close> decoder is the identity on a single canonical
  block: pure cell \<open>\<rightarrow>\<close> \<open>encode_input m bl (map x [0..<m]) = [x]\<close>;
  padded cell with witness \<open>k\<close> \<open>\<rightarrow>\<close>
  \<open>encode_input m bl (map x [0..<k]) = [x]\<close>.  Per-cell
  identity for the round-trip.\<close>

lemma encode_decode_block:
  fixes x :: "nat \<Rightarrow> 'a"
  assumes canon: "is_canonical_block m bl x"
      and m_pos: "0 < m"
      and x_ext: "\<forall>y. m \<le> y \<longrightarrow> x y = undefined"
  shows "encode_input m bl (ae_decode_block m bl x)
           = ([x] :: (nat \<Rightarrow> 'a) list)"
proof (cases "is_pure_block m bl x")
  case True
  have decode: "ae_decode_block m bl x
                  = map x [0..<m]"
    by (rule ae_decode_block_pure[OF True])
  show ?thesis using decode encode_input_map_symbols[OF m_pos x_ext] by simp
next
  case False
  hence padded: "is_padded_block m bl x"
    using canon unfolding is_canonical_block_def by blast
  obtain k where k_pos: "1 \<le> k"
    and k_lt: "k < length [0..<m]"
    and prefix: "\<forall>y<m. y < k \<longrightarrow> x y \<noteq> bl"
    and suffix: "\<forall>y<m. y \<ge> k \<longrightarrow> x y = bl"
    using padded unfolding is_padded_block_def by blast
  have decode: "ae_decode_block m bl x
                  = map x (take k [0..<m])"
    by (rule ae_decode_block_padded[OF k_lt prefix suffix])
  have k_pos': "0 < k" using k_pos by simp
  have k_le: "k \<le> length [0..<m]" using k_lt by simp
  have enc: "encode_input m bl (map x (take k [0..<m]))
               = ([x] :: (nat \<Rightarrow> 'a) list)"
    using encode_input_map_take_symbols[OF k_pos' k_le suffix x_ext] .
  show ?thesis using decode enc by simp
qed

text \<open>The round-trip: for any well-formed block list \<open>w\<close>,
  encoding the decoder's output reproduces \<open>w\<close>.  By \<open>rev_induct\<close>:
  the empty case is trivial; the snoc step uses
  \<open>encode_input_append_div\<close> (the prefix decodes to a length
  divisible by \<open>c\<close>, since all of \<open>w\<close>'s prefix cells are pure)
  plus \<open>encode_decode_block\<close> on the last block.\<close>

lemma encode_decode_round_trip:
  fixes w :: "(nat \<Rightarrow> 'a) list"
  assumes wf: "ae_input_well_formed m bl w"
      and m_pos: "0 < m"
      and w_ext: "\<forall>b\<in>set w. \<forall>y. m \<le> y \<longrightarrow> b y = undefined"
  shows "encode_input m bl (ae_decode_input m bl w) = w"
proof -
  have main: "ae_input_well_formed m bl w
                \<longrightarrow> (\<forall>b\<in>set w. \<forall>y. m \<le> y \<longrightarrow> b y = undefined)
                \<longrightarrow> encode_input m bl (ae_decode_input m bl w) = w"
  proof (induct w rule: rev_induct)
    case Nil
    show ?case
      by (simp add: ae_decode_input_def encode_input_empty)
  next
    case (snoc x xs)
    show ?case
    proof (intro impI)
      assume wf_snoc: "ae_input_well_formed m bl (xs @ [x])"
         and ext_snoc: "\<forall>b\<in>set (xs @ [x]). \<forall>y. m \<le> y \<longrightarrow> b y = undefined"
      have all_pure: "\<forall>i < length xs. is_pure_block m bl (xs ! i)"
        using wf_snoc by (rule ae_input_well_formed_init_pure)
      have wf_xs: "ae_input_well_formed m bl xs"
        unfolding ae_input_well_formed_def using all_pure by blast
      have ext_xs: "\<forall>b\<in>set xs. \<forall>y. m \<le> y \<longrightarrow> b y = undefined"
        using ext_snoc by simp
      have ext_x: "\<forall>y. m \<le> y \<longrightarrow> x y = undefined"
        using ext_snoc by simp
      have ih: "encode_input m bl (ae_decode_input m bl xs) = xs"
        using snoc.hyps wf_xs ext_xs by blast
      have x_canonical: "is_canonical_block m bl x"
      proof -
        let ?n = "length (xs @ [x]) - 1"
        have x_eq: "(xs @ [x]) ! ?n = x" by simp
        have n_lt: "?n < length (xs @ [x])" by simp
        have "is_pure_block m bl ((xs @ [x]) ! ?n)
                \<or> (?n = length (xs @ [x]) - 1
                    \<and> is_padded_block m bl ((xs @ [x]) ! ?n))"
          using wf_snoc n_lt unfolding ae_input_well_formed_def by blast
        hence "is_pure_block m bl x \<or> is_padded_block m bl x"
          using x_eq by simp
        thus ?thesis unfolding is_canonical_block_def .
      qed
      have block_eq: "encode_input m bl (ae_decode_block m bl x) = [x]"
        by (rule encode_decode_block[OF x_canonical m_pos ext_x])
      have len_xs_decode:
        "m dvd length (ae_decode_input m bl xs)"
      proof -
        have "length (ae_decode_input m bl xs)
                = length xs * m"
          by (rule length_ae_decode_input_pure[OF all_pure])
        thus ?thesis by simp
      qed
      have decode_split:
        "ae_decode_input m bl (xs @ [x])
           = ae_decode_input m bl xs @ ae_decode_block m bl x"
        by (simp add: ae_decode_input_def)
      have "encode_input m bl (ae_decode_input m bl (xs @ [x]))
              = encode_input m bl
                  (ae_decode_input m bl xs @ ae_decode_block m bl x)"
        using decode_split by simp
      also have "(encode_input m bl
                     (ae_decode_input m bl xs @ ae_decode_block m bl x)
                       :: (nat \<Rightarrow> 'a) list)
                  = encode_input m bl (ae_decode_input m bl xs)
                      @ encode_input m bl (ae_decode_block m bl x)"
        by (rule encode_input_append_div[OF len_xs_decode m_pos])
      also have "\<dots> = xs @ encode_input m bl (ae_decode_block m bl x)"
        using ih by simp
      also have "\<dots> = xs @ [x]" using block_eq by simp
      finally show "encode_input m bl (ae_decode_input m bl (xs @ [x]))
                      = xs @ [x]" .
    qed
  qed
  show ?thesis using main wf w_ext by blast
qed

end
