theory AlphabetEnlargement_Pack
  imports AlphabetEnlargement_Reverse Wrap_Base
begin

section \<open>AE-wrap glue: \<open>wrap_enc\<close> matches \<open>encode_input\<close>\<close>

text \<open>The bridge between the encoding-wrap combinator's input shape and the
  alphabet enlargement's encoded input: the \<open>ae_pack\<close> packer, a
  ceiling-division identity, and the glue lemma
  \<open>wrap_enc_eq_encode_input\<close> identifying @{const wrap_enc} under
  \<open>ae_pack\<close> with the alphabet enlargement's @{const encode_input}.  This
  bridge is independent of either wrap's tape layout, so it is shared by both
  the shift and the faithful (transpose) classical-speedup headline theories.\<close>

text \<open>Ceiling-division identity for nat: \<open>\<lceil>n/c\<rceil>\<close>
  expressed as @{term "n div c + (if n mod c = 0 then 0 else 1)"}
  equals @{term "(n + c - 1) div c"}.  Used to bridge the
  closed forms of @{thm[source] length_wrap_enc} and @{thm[source] length_encode_input}.\<close>

lemma nat_ceil_div_eq:
  fixes n c :: nat
  assumes c_pos: "0 < c"
  shows "n div c + (if n mod c = 0 then 0 else 1) = (n + c - 1) div c"
proof -
  let ?q = "n div c"
  let ?r = "n mod c"
  have decomp: "n = ?q * c + ?r"
    by (simp add: mult.commute)
  show ?thesis
  proof (cases "?r = 0")
    case True
    have lw_eq: "n = ?q * c" using True decomp by simp
    have step1: "(n + c - 1) div c = (?q * c + (c - 1)) div c"
      using lw_eq c_pos by (simp add: Nat.add_diff_assoc)
    have c_neq: "c \<noteq> 0" using c_pos by simp
    have step2: "(?q * c + (c - 1)) div c = ?q + (c - 1) div c"
      using div_mult_self3[OF c_neq, of ?q "c - 1"] .
    have step3: "?q + (c - 1) div c = ?q"
      using c_pos by simp
    have rhs_eq: "(n + c - 1) div c = ?q"
      using step1 step2 step3 by simp
    show ?thesis using True rhs_eq by simp
  next
    case False
    have r_pos: "0 < ?r" using False by simp
    have r_lt: "?r < c" using c_pos by simp
    have rewrite: "n + c - 1 = (?q + 1) * c + (?r - 1)"
    proof -
      have eq1: "n + c - 1 = ?q * c + ?r + c - 1" using decomp by simp
      have eq2: "?q * c + ?r + c - 1 = ?q * c + c + (?r - 1)"
        using r_pos by simp
      have eq3: "?q * c + c + (?r - 1) = (?q + 1) * c + (?r - 1)"
        by (simp add: distrib_right)
      from eq1 eq2 eq3 show ?thesis by simp
    qed
    have r_m1_lt: "?r - 1 < c" using r_lt by simp
    have c_neq: "c \<noteq> 0" using c_pos by simp
    have step1: "(n + c - 1) div c = ((?q + 1) * c + (?r - 1)) div c"
      using rewrite by simp
    have step2: "((?q + 1) * c + (?r - 1)) div c = (?q + 1) + (?r - 1) div c"
      using div_mult_self3[OF c_neq, of "?q + 1" "?r - 1"] .
    have step3: "(?q + 1) + (?r - 1) div c = ?q + 1"
      using r_m1_lt by simp
    have rhs_eq: "(n + c - 1) div c = ?q + 1"
      using step1 step2 step3 by simp
    show ?thesis using False rhs_eq by simp
  qed
qed

text \<open>The pack function that turns @{const wrap_enc} into AE's
  @{const encode_input}: given a list-shaped block of up to @{term c}
  symbols, build the block function @{typ "'c \<Rightarrow> 'a"} by reading
  off the block's @{term "c_idx x"}-th entry (or the blank
  @{term bl} if the block is shorter than @{term "c_idx x + 1"}).
  This is the per-block packer for the AE-wrap instance of
  @{const wrap_enc}.\<close>

definition ae_pack ::
  "'a \<Rightarrow> 'a list \<Rightarrow> (('c :: enum) \<Rightarrow> 'a)" where
  "ae_pack bl block = (\<lambda>x. if c_idx x < length block
                            then block ! c_idx x
                            else bl)"

text \<open>Glue lemma: when the wrap's grouping factor matches AE's
  @{typ 'c}-cardinality, @{const wrap_enc} with @{const ae_pack}
  produces exactly AE's @{const encode_input}.  This rewrite lets an
  encoding-wrap correctness lemma compose with the alphabet-enlargement
  results @{thm[source] alphabet_enlarge_language} /
  @{thm[source] alphabet_enlarge_time}, identifying the wrap's encoded input
  with the AE-machine's expected input format.\<close>

lemma wrap_enc_eq_encode_input:
  fixes w :: "'a list" and bl :: "'a"
  defines c_def: "c \<equiv> card (UNIV :: ('c :: enum) set)"
  assumes c_pos: "0 < c"
  shows "wrap_enc (ae_pack bl :: 'a list \<Rightarrow> ('c \<Rightarrow> 'a)) c w
          = (encode_input bl w :: ('c \<Rightarrow> 'a) list)"
proof (rule nth_equalityI)
  let ?L = "(length w + c - 1) div c"
  let ?lhs = "wrap_enc (ae_pack bl :: 'a list \<Rightarrow> ('c \<Rightarrow> 'a)) c w"
  let ?rhs = "encode_input bl w :: ('c \<Rightarrow> 'a) list"

  \<comment> \<open>Lengths agree.\<close>
  have ceil_id:
    "length w div c + (if length w mod c = 0 then 0 else 1) = ?L"
    by (rule nat_ceil_div_eq[OF c_pos])
  have len_lhs: "length ?lhs = ?L"
  proof -
    have "length ?lhs
            = length w div c + (if length w mod c = 0 then 0 else 1)"
      by (rule length_wrap_enc[OF c_pos])
    also have "\<dots> = ?L" using ceil_id .
    finally show ?thesis .
  qed
  have len_rhs: "length ?rhs = ?L"
    using length_encode_input[where bl = bl and u = w]
    by (simp add: c_def)
  show "length ?lhs = length ?rhs"
    using len_lhs len_rhs by simp

  \<comment> \<open>Per-index agreement.\<close>
  fix i :: nat
  assume i_lt: "i < length ?lhs"
  with len_lhs have i_L: "i < ?L" by simp

  \<comment> \<open>Bound: \<open>i*c < length w\<close>, from \<open>Suc i \<le> ?L\<close> + the div-multiplication iff.\<close>
  have i_c_lt_lenw: "i * c < length w"
  proof -
    from i_L have Si_le: "Suc i \<le> (length w + c - 1) div c" by simp
    have iff_lemma:
      "(Suc i \<le> (length w + c - 1) div c)
        = (Suc i * c \<le> length w + c - 1)"
      using c_pos by (rule less_eq_div_iff_mult_less_eq)
    from Si_le iff_lemma have step1: "Suc i * c \<le> length w + c - 1" by simp
    have step2: "i * c + c \<le> length w + c - 1" using step1 by simp
    show ?thesis using step2 c_pos by linarith
  qed

  \<comment> \<open>Element equality: the \<open>i\<close>-th block agrees pointwise on \<open>'c\<close>.\<close>
  have nth_lhs:
    "?lhs ! i = ae_pack bl (take c (drop (i * c) w))"
  proof (cases "(Suc i) * c \<le> length w")
    case True  \<comment> \<open>full block\<close>
    show ?thesis
      using wrap_enc_nth[OF c_pos True] .
  next
    case False
    \<comment> \<open>Partial block: \<open>i = length w div c\<close>, \<open>length w mod c \<noteq> 0\<close>.\<close>
    have mod_ne: "length w mod c \<noteq> 0"
    proof
      assume mod_eq: "length w mod c = 0"
      from mod_eq have len_div: "length w = (length w div c) * c"
        using div_mult_mod_eq[of "length w" c] by simp
      have L_eq: "?L = length w div c"
        using nat_ceil_div_eq[OF c_pos, of "length w"] mod_eq by simp
      from i_L L_eq have i_lt: "i < length w div c" by simp
      hence "Suc i \<le> length w div c" by simp
      hence "Suc i * c \<le> (length w div c) * c"
        by (rule mult_le_mono1)
      with len_div have "Suc i * c \<le> length w" by simp
      with False show False ..
    qed
    have i_eq: "i = length w div c"
    proof -
      have L_eq: "?L = length w div c + 1"
        using nat_ceil_div_eq[OF c_pos, of "length w"] mod_ne by simp
      from i_L L_eq have i_le: "i \<le> length w div c" by simp
      from False have "length w < Suc i * c" by simp
      hence "length w div c < Suc i"
        using c_pos by (simp add: div_less_iff_less_mult mult.commute)
      hence "length w div c \<le> i" by simp
      with i_le show ?thesis by simp
    qed
    have nth_partial:
      "?lhs ! (length w div c) = ae_pack bl (drop ((length w div c) * c) w)"
      by (rule wrap_enc_nth_partial[OF c_pos mod_ne])
    have drop_short:
      "length (drop ((length w div c) * c) w) < c"
    proof -
      have len_drop: "length (drop ((length w div c) * c) w)
                       = length w - (length w div c) * c"
        by simp
      have mod_eq: "length w - (length w div c) * c = length w mod c"
        using div_mult_mod_eq[of "length w" c] by linarith
      have mod_lt: "length w mod c < c" using c_pos by simp
      from len_drop mod_eq mod_lt show ?thesis by simp
    qed
    have take_eq:
      "take c (drop ((length w div c) * c) w)
        = drop ((length w div c) * c) w"
      using drop_short by simp
    show ?thesis
      using nth_partial i_eq take_eq by simp
  qed

  show "?lhs ! i = ?rhs ! i"
  proof (rule ext)
    fix x :: "'c"
    have cx_lt: "c_idx x < c"
      unfolding c_def by (rule c_idx_lt_card)

    \<comment> \<open>The right-hand entry, point-x form, via @{thm[source] encode_input_nth}.\<close>
    have rhs_i_lt: "i < length ?rhs" using i_lt len_lhs len_rhs by simp
    have nth_rhs_x:
      "(?rhs ! i) x = (if i * c + c_idx x < length w
                        then w ! (i * c + c_idx x) else bl)"
      using encode_input_nth[OF rhs_i_lt, where x = x]
      by (simp add: c_def Let_def)

    show "(?lhs ! i) x = (?rhs ! i) x"
    proof (cases "(Suc i) * c \<le> length w")
      case True  \<comment> \<open>full block\<close>
      have len_eq: "length (take c (drop (i * c) w)) = c"
        using True by simp
      have j_lt: "i * c + c_idx x < length w"
      proof -
        from True have "i * c + c \<le> length w" by simp
        with cx_lt show ?thesis by linarith
      qed
      have "(?lhs ! i) x = (ae_pack bl (take c (drop (i * c) w))) x"
        using nth_lhs by simp
      also have "\<dots> = (if c_idx x < length (take c (drop (i * c) w))
                        then (take c (drop (i * c) w)) ! c_idx x else bl)"
        unfolding ae_pack_def by simp
      also have "\<dots> = (take c (drop (i * c) w)) ! c_idx x"
        using cx_lt len_eq by simp
      also have "\<dots> = w ! (i * c + c_idx x)"
        using True cx_lt by (simp add: nth_drop)
      also have "\<dots> = (?rhs ! i) x"
        using nth_rhs_x j_lt by simp
      finally show ?thesis .
    next
      case False
      have len_eq: "length (take c (drop (i * c) w)) = length w - i * c"
        using False i_c_lt_lenw by simp
      have cond_iff:
        "(c_idx x < length w - i * c) = (i * c + c_idx x < length w)"
        using i_c_lt_lenw by linarith
      have lhs_x:
        "(?lhs ! i) x = (if c_idx x < length w - i * c
                          then (take c (drop (i * c) w)) ! c_idx x
                          else bl)"
      proof -
        have "(?lhs ! i) x = (ae_pack bl (take c (drop (i * c) w))) x"
          using nth_lhs by simp
        also have "\<dots> = (if c_idx x < length (take c (drop (i * c) w))
                          then (take c (drop (i * c) w)) ! c_idx x else bl)"
          unfolding ae_pack_def by simp
        also have "\<dots> = (if c_idx x < length w - i * c
                          then (take c (drop (i * c) w)) ! c_idx x else bl)"
          using len_eq by simp
        finally show ?thesis .
      qed
      show ?thesis
      proof (cases "c_idx x < length w - i * c")
        case True
        from True cond_iff have j_lt: "i * c + c_idx x < length w" by simp
        have nth_take: "(take c (drop (i * c) w)) ! c_idx x
                          = w ! (i * c + c_idx x)"
          using True cx_lt i_c_lt_lenw by (simp add: nth_drop)
        have lhs_simp: "(?lhs ! i) x = w ! (i * c + c_idx x)"
          using lhs_x True nth_take by simp
        have rhs_simp: "(?rhs ! i) x = w ! (i * c + c_idx x)"
          using nth_rhs_x j_lt by simp
        show ?thesis using lhs_simp rhs_simp by simp
      next
        case False
        from False cond_iff have j_ge: "\<not> i * c + c_idx x < length w" by simp
        have lhs_simp: "(?lhs ! i) x = bl"
          using lhs_x False by simp
        have rhs_simp: "(?rhs ! i) x = bl"
          using nth_rhs_x j_ge by simp
        show ?thesis using lhs_simp rhs_simp by simp
      qed
    qed
  qed
qed

end
