theory Multitape_Binary_Codec
  imports Main
begin

section \<open>Fixed-width binary blocks\<close>

text \<open>Several constructions over the substrate write a natural number onto a
  tape as a block of a fixed number of cells, one binary digit per cell: a
  symbol of a large alphabet as its index, or a field of a record a machine
  keeps on a work tape.  This theory is that codec, once.  It mentions no
  machine.

  The two digit symbols are parameters, \<open>d0\<close> for the bit \<open>0\<close> and \<open>d1\<close> for the
  bit \<open>1\<close>, over an arbitrary symbol type.  A construction whose tape alphabet
  has no spare symbols can then extend it by two fresh ones and use those, and
  one with a fixed alphabet instantiates the parameters once and names the
  instance.

  A block is most-significant digit first.  For \<open>n \<ge> 2 ^ k\<close> the high bits
  of \<open>n\<close> are dropped.\<close>

fun nat_to_syms :: "'x \<Rightarrow> 'x \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'x list" where
  "nat_to_syms d0 d1 0 _ = []"
| "nat_to_syms d0 d1 (Suc k) n =
     nat_to_syms d0 d1 k (n div 2) @ [if n mod 2 = 0 then d0 else d1]"

text \<open>The bit a symbol denotes: \<open>1\<close> for \<open>d1\<close>, \<open>0\<close> for anything else.  The
  decoder is total, so it reads a malformed block as some number; checking
  that every cell is a digit is the caller's business.\<close>

definition bit_of :: "'x \<Rightarrow> 'x \<Rightarrow> nat" where
  "bit_of d1 x = (if x = d1 then 1 else 0)"

lemma bit_of_same [simp]: "bit_of d1 d1 = 1"
  by (simp add: bit_of_def)

lemma bit_of_other [simp]: "x \<noteq> d1 \<Longrightarrow> bit_of d1 x = 0"
  by (simp add: bit_of_def)

fun syms_to_nat :: "'x \<Rightarrow> 'x list \<Rightarrow> nat" where
  "syms_to_nat d1 [] = 0"
| "syms_to_nat d1 (b # bs) = bit_of d1 b * 2 ^ length bs + syms_to_nat d1 bs"

text \<open>A block has the requested width, and every cell is one of the two
  digit symbols.\<close>

lemma length_nat_to_syms [simp]:
  "length (nat_to_syms d0 d1 k n) = k"
  by (induct k arbitrary: n) auto

lemma set_nat_to_syms:
  "set (nat_to_syms d0 d1 k n) \<subseteq> {d0, d1}"
  by (induct k arbitrary: n) auto

text \<open>Appending a low digit shifts the value left and adds the new bit.  This
  matches the shape of @{const nat_to_syms}, which appends its low digit, and
  is the step of the round trip below.\<close>

lemma syms_to_nat_snoc:
  "syms_to_nat d1 (xs @ [b]) = 2 * syms_to_nat d1 xs + bit_of d1 b"
  by (induct xs) auto

lemma bit_of_low_bit:
  assumes "d0 \<noteq> d1"
  shows "bit_of d1 (if n mod 2 = 0 then d0 else d1) = n mod 2"
  using assms mod_less_divisor[of 2 n] by (auto simp: bit_of_def)

text \<open>The round trip: writing \<open>n < 2 ^ k\<close> as a block of \<open>k\<close> cells and reading
  it back gives \<open>n\<close>, provided the two digits differ.\<close>

lemma syms_to_nat_nat_to_syms:
  assumes d: "d0 \<noteq> d1" and "n < 2 ^ k"
  shows "syms_to_nat d1 (nat_to_syms d0 d1 k n) = n"
  using \<open>n < 2 ^ k\<close>
proof (induct k arbitrary: n)
  case 0
  thus ?case by simp
next
  case (Suc k)
  have lt: "n div 2 < 2 ^ k" using \<open>n < 2 ^ Suc k\<close> by simp
  have "syms_to_nat d1 (nat_to_syms d0 d1 (Suc k) n)
          = syms_to_nat d1
              (nat_to_syms d0 d1 k (n div 2)
                 @ [if n mod 2 = 0 then d0 else d1])"
    by simp
  also have "\<dots>
          = 2 * syms_to_nat d1 (nat_to_syms d0 d1 k (n div 2))
              + bit_of d1 (if n mod 2 = 0 then d0 else d1)"
    by (rule syms_to_nat_snoc)
  also have "\<dots> = 2 * (n div 2) + n mod 2"
    using Suc.hyps[OF lt] bit_of_low_bit[OF d, of n] by simp
  also have "\<dots> = n" by presburger
  finally show ?case .
qed

text \<open>Injectivity on the bounded range follows: decoding is a left inverse
  there, so equal blocks have equal values.\<close>

lemma nat_to_syms_inj:
  assumes d: "d0 \<noteq> d1"
      and n1: "n\<^sub>1 < 2 ^ k" and n2: "n\<^sub>2 < 2 ^ k"
      and eq: "nat_to_syms d0 d1 k n\<^sub>1 = nat_to_syms d0 d1 k n\<^sub>2"
  shows "n\<^sub>1 = n\<^sub>2"
proof -
  have "n\<^sub>1 = syms_to_nat d1 (nat_to_syms d0 d1 k n\<^sub>1)"
    by (simp add: syms_to_nat_nat_to_syms[OF d n1])
  also have "\<dots> = syms_to_nat d1 (nat_to_syms d0 d1 k n\<^sub>2)" using eq by simp
  also have "\<dots> = n\<^sub>2" by (simp add: syms_to_nat_nat_to_syms[OF d n2])
  finally show ?thesis .
qed

subsection \<open>The width of a block\<close>

text \<open>The width that indexes a finite set \<open>S\<close>: the fewest binary digits that
  number all of its elements, \<open>\<lceil>log\<^sub>2 (card S)\<rceil>\<close>, and at least one, so that no
  block is empty.  It is defined by \<open>LEAST\<close>, and such an \<open>n\<close> exists because
  \<open>card S < 2 ^ card S\<close>.\<close>

definition block_width :: "'z set \<Rightarrow> nat" where
  "block_width S = max 1 (LEAST n. card S \<le> 2 ^ n)"

lemma block_width_pos: "1 \<le> block_width S"
  unfolding block_width_def by simp

text \<open>Coverage: \<open>card S \<le> 2 ^ block_width S\<close>, so every index below \<open>card S\<close>
  is in the range where @{const nat_to_syms} is injective.\<close>

lemma card_le_two_pow_block_width: "card S \<le> 2 ^ block_width S"
proof -
  have ex: "\<exists>n. card S \<le> 2 ^ n"
    using less_exp[of "card S"] by (intro exI[of _ "card S"]) simp
  let ?m = "LEAST n. card S \<le> 2 ^ n"
  have m_bound: "card S \<le> 2 ^ ?m" using LeastI_ex[OF ex] .
  have "?m \<le> block_width S" unfolding block_width_def by simp
  hence "(2::nat) ^ ?m \<le> 2 ^ block_width S" by (rule power_increasing) simp
  with m_bound show ?thesis by linarith
qed

text \<open>Minimality: once \<open>S\<close> has two elements, one digit fewer does not
  suffice.  With coverage this pins the width to \<open>\<lceil>log\<^sub>2 (card S)\<rceil>\<close>: it is
  constant on each band \<open>2 ^ (b - 1) < card S \<le> 2 ^ b\<close> and rises by one as
  \<open>card S\<close> passes a power of two.\<close>

lemma two_pow_block_width_pred_less_card:
  assumes card2: "2 \<le> card S"
  shows "2 ^ (block_width S - 1) < card S"
proof -
  have ex: "\<exists>n. card S \<le> 2 ^ n"
    using less_exp[of "card S"] by (intro exI[of _ "card S"]) simp
  let ?m = "LEAST n. card S \<le> 2 ^ n"
  have notP0: "\<not> card S \<le> 2 ^ (0::nat)" using card2 by simp
  have m_pos: "0 < ?m"
  proof (rule ccontr)
    assume "\<not> 0 < ?m"
    then have "?m = 0" by simp
    then have "card S \<le> 2 ^ (0::nat)" using LeastI_ex[OF ex] by simp
    with notP0 show False by simp
  qed
  hence bw: "block_width S = ?m" unfolding block_width_def by simp
  have "block_width S - 1 < ?m" using bw m_pos by simp
  hence "\<not> card S \<le> 2 ^ (block_width S - 1)" by (rule not_less_Least)
  thus ?thesis by simp
qed

text \<open>The exact value, for a caller that knows the band \<open>card S\<close> lies in:
  bracketing the cardinality between two consecutive powers pins the
  \<^theory_text>\<open>LEAST\<close>, and the lower bound makes the \<^const>\<open>max\<close> inert.\<close>

lemma block_width_eqI:
  assumes lo: "2 ^ n < card S" and hi: "card S \<le> 2 ^ Suc n"
  shows "block_width S = Suc n"
proof -
  have "(LEAST m. card S \<le> 2 ^ m) = Suc n"
  proof (rule Least_equality)
    show "card S \<le> 2 ^ Suc n" by (rule hi)
  next
    fix m assume m: "card S \<le> 2 ^ m"
    show "Suc n \<le> m"
    proof (rule ccontr)
      assume "\<not> Suc n \<le> m"
      then have "m \<le> n" by simp
      then have "(2::nat) ^ m \<le> 2 ^ n"
        using power_increasing [of m n "2::nat"] by simp
      with lo m show False by simp
    qed
  qed
  then show ?thesis by (simp add: block_width_def)
qed

end
