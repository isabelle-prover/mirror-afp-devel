(*
Author: Claude and Tobias Nipkow, based on Hopcroft and Ullman (1979).
*)

section \<open>Example: \<open>{a\<^sup>ib\<^sup>jc\<^sup>k | i \<noteq> j \<and> j \<noteq> k \<and> i \<noteq> k}\<close> is not context-free\<close>

theory Ogden_Example
imports "Context_Free_Grammar.Ogdens_Lemma" "ABC_Words"
begin

text \<open>
  This is Example 6.3 of Hopcroft and Ullman \cite{HopcroftU79}:
  the language \<open>L\<^sub>4 = {a\<^sup>ib\<^sup>jc\<^sup>k | i \<noteq> j \<and> j \<noteq> k \<and> i \<noteq> k}\<close> is not context-free.
  The proof uses Ogden's lemma in derivation form (@{thm [source] Ogden_Lemma}): we mark the
  \<open>a\<close>-positions of \<open>z = a\<^sup>n b\<^sup>n\<^sup>+\<^sup>n\<^sup>! c\<^sup>n\<^sup>+\<^sup>2\<^sup>n\<^sup>!\<close> and pump.

  Following Hopcroft and Ullman, the marked block \<open>v\<close> and \<open>x\<close> must each be uniform (one letter),
  and since the marks are on \<open>a\<close>s at least one of \<open>v x\<close> consists of \<open>a\<close>s. Hence \<open>v x\<close> omits \<open>b\<close>
  or omits \<open>c\<close>. The factorials in the exponents are chosen so that pumping the \<open>a\<close>s (a block of
  size \<open>p \<le> n\<close>, so \<open>p\<close> divides \<open>n!\<close>) lands the number of \<open>a\<close>s exactly on the number of \<open>b\<close>s
  (\<open>n+n!\<close>) or \<open>c\<close>s (\<open>n+2n!\<close>) -- forcing a forbidden equality.
\<close>

definition L4 :: "letter list set" where
"L4 = {abcword i j k | i j k. i \<noteq> j \<and> j \<noteq> k \<and> i \<noteq> k}"

lemma abcword_in_L4_iff: "abcword i j k \<in> L4 \<longleftrightarrow> i \<noteq> j \<and> j \<noteq> k \<and> i \<noteq> k"
  by (auto simp: L4_def dest: abcword_inj)

text \<open>A word of \<open>L\<^sub>4\<close> has three pairwise-distinct letter counts.\<close>

lemma L4_counts_distinct:
  assumes "w \<in> L4"
  shows "count_list w A \<noteq> count_list w B"
    and "count_list w B \<noteq> count_list w C"
    and "count_list w A \<noteq> count_list w C"
  using assms by (auto simp: L4_def count_abcword)


text \<open>Order the alphabet \<open>A < B < C\<close>, so that an \<open>abcword\<close> is exactly a \<open>sorted\<close> word.\<close>

lemma L4_sorted: "w \<in> L4 \<Longrightarrow> sorted w"
  using abcword_sorted by (auto simp: L4_def)

text \<open>The Ogden marking that distinguishes exactly the \<open>A\<close>-positions of a word.\<close>

abbreviation amark :: "letter list \<Rightarrow> bool list" where
"amark zs \<equiv> map (\<lambda>x. x = A) zs"

lemma dcount_amark: "dcount (amark zs) = count_list zs A"
  by (induction zs) auto

text \<open>Splitting a word splits its marking the same way (matching segment lengths).\<close>

lemma append5_eq:
  assumes "a1 @ a2 @ a3 @ a4 @ a5 = b1 @ b2 @ b3 @ b4 @ b5"
    and "length a1 = length b1" "length a2 = length b2" "length a3 = length b3"
        "length a4 = length b4" "length a5 = length b5"
  shows "a1 = b1 \<and> a2 = b2 \<and> a3 = b3 \<and> a4 = b4 \<and> a5 = b5"
  using assms by (auto)

lemma amark_split:
  assumes z: "z = u @ v @ w @ x @ y"
      and ds: "amark z = du @ dv @ dw @ dx @ dy"
      and l: "length du = length u" "length dv = length v" "length dw = length w"
             "length dx = length x" "length dy = length y"
  shows "dv = amark v" "dw = amark w" "dx = amark x"
proof -
  have eq: "du @ dv @ dw @ dx @ dy = amark u @ amark v @ amark w @ amark x @ amark y"
    using ds z by simp
  have "length du = length (amark u)" "length dv = length (amark v)"
       "length dw = length (amark w)" "length dx = length (amark x)"
       "length dy = length (amark y)"
    using l by simp_all
  from append5_eq[OF eq this]
  show "dv = amark v" "dw = amark w" "dx = amark x" by simp_all
qed


text \<open>Main theorem:\<close>

theorem L4_not_CFL:
  assumes finP: "finite (P :: ('n::fresh0, letter) Prods)"
  shows "Lang P S \<noteq> L4"
proof
  assume eq: "Lang P S = L4"
  from Ogden_Lemma[OF finP, of S] obtain n where ogden: "ogden_property (Lang P S) n" ..

  text \<open>The witness word and its \<open>a\<close>-marking.\<close>
  define z where z_def: "z = abcword n (n + fact n) (n + 2 * fact n)"
  have zL4: "z \<in> L4" using fact_gt_zero by (simp add: z_def abcword_in_L4_iff)
  have zin: "z \<in> Lang P S" using zL4 eq by simp
  have len: "length (amark z) = length z" by simp
  have dcn: "dcount (amark z) = n" by (simp add: dcount_amark z_def count_abcword)

  text \<open>Apply Ogden's lemma with the \<open>a\<close>-marking.\<close>
  have nle: "n \<le> dcount (amark z)" using dcn by simp
  from bspec[OF ogden zin, rule_format, OF conjI[OF len nle]]
  obtain u v w x y du dv dw dx dy where
    O1: "z = u @ v @ w @ x @ y"
    and O2: "amark z = du @ dv @ dw @ dx @ dy"
    and O3: "length du = length u" and O4: "length dv = length v"
    and O5: "length dw = length w" and O6: "length dx = length x"
    and O7: "length dy = length y"
    and O8: "1 \<le> dcount (dv @ dx)"
    and O9: "dcount (dv @ dw @ dx) \<le> n"
    and pumpL4: "\<And>i. u @ v ^^ i @ w @ x ^^ i @ y \<in> L4"
    unfolding eq by blast

  text \<open>The marking restricted to the blocks counts the \<open>a\<close>s of those blocks.\<close>
  note splits = amark_split[OF O1 O2 O3 O4 O5 O6 O7]
  have dvx: "dcount (dv @ dx) = count_list (v @ x) A"
    by (simp add: splits dcount_amark)
  have dvwx: "dcount (dv @ dw @ dx) = count_list (v @ w @ x) A"
    by (simp add: splits dcount_amark)

  text \<open>So the number \<open>p\<close> of marked \<open>a\<close>s in \<open>v x\<close> satisfies \<open>1 \<le> p \<le> n\<close>, hence \<open>p\<close> divides \<open>n!\<close>.\<close>
  have vxA1: "1 \<le> count_list (v @ x) A" using O8 dvx by simp
  have vxAn: "count_list (v @ x) A \<le> n"
    using O9 dvwx by force
  have dvdA: "count_list (v @ x) A dvd fact n" using vxA1 vxAn by (rule dvd_fact)
  have dvd2A: "count_list (v @ x) A dvd 2 * fact n" using vxA1 vxAn by (simp add: dvd_fact)

  text \<open>Pumping with \<open>i = 2\<close> shows \<open>v\<close> and \<open>x\<close> are each uniform (sorted squares).\<close>
  have v2: "v ^^ 2 = v @ v" and x2: "x ^^ 2 = x @ x"
    by (simp_all add: numeral_2_eq_2)
  have srt2: "sorted (u @ v @ v @ w @ x @ x @ y)"
    using L4_sorted[OF pumpL4[of 2]] by (simp add: v2 x2)
  have uniform_v: "\<And>a b. a \<in> set v \<Longrightarrow> b \<in> set v \<Longrightarrow> a = b"
    using sorted_factor_uniform srt2 by blast
  have uniform_x: "\<And>a b. a \<in> set x \<Longrightarrow> b \<in> set x \<Longrightarrow> a = b"
    by (meson sorted_append sorted_factor_uniform srt2)

  text \<open>Since \<open>v x\<close> contains an \<open>a\<close> and \<open>v, x\<close> are uniform, \<open>v x\<close> misses \<open>b\<close> or misses \<open>c\<close>.\<close>
  have AinVX: "A \<in> set (v @ x)"
    using vxA1 by (metis count_list_0_iff not_one_le_zero)
  have disj: "count_list (v @ x) B = 0 \<or> count_list (v @ x) C = 0"
    using uniform_v uniform_x AinVX by (auto simp: count_list_0_iff)

  text \<open>Letter counts of a pumped word, and of \<open>z\<close> itself.\<close>
  have countX: "count_list (u @ v ^^ i @ w @ x ^^ i @ y) c
                  = count_list (u @ w @ y) c + i * (count_list v c + count_list x c)" for i c
    by (simp add: count_list_pow_list algebra_simps)
  have zsplit: "count_list z c = count_list (u @ w @ y) c + (count_list v c + count_list x c)" for c
    using O1 by (simp)
  have zA: "count_list z A = n" by (simp add: z_def count_abcword)
  have zB: "count_list z B = n + fact n" by (simp add: z_def count_abcword)
  have zC: "count_list z C = n + 2 * fact n" by (simp add: z_def count_abcword)

  from disj show False
  proof (elim disjE)
    text \<open>\<open>v x\<close> has no \<open>B\<close>: pump \<open>A\<close>s up to \<open>n+n! = \<close> number of \<open>B\<close>s, contradicting \<open>i \<noteq> j\<close>.\<close>
    assume B0: "count_list (v @ x) B = 0"
    define i0 where "i0 = Suc (fact n div count_list (v @ x) A)"
    let ?word = "u @ v ^^ i0 @ w @ x ^^ i0 @ y"
    have wordA: "count_list ?word A = n + fact n"
      using countX dvdA i0_def zA zsplit by auto
    have wordB: "count_list ?word B = n + fact n"
      by (metis B0 countX count_list_append mult_is_0 zB zsplit) 
    from wordA wordB L4_counts_distinct(1)[OF pumpL4[of i0]] show False by simp
  next
    text \<open>\<open>v x\<close> has no \<open>C\<close>: pump \<open>A\<close>s up to \<open>n+2n! = \<close> number of \<open>C\<close>s, contradicting \<open>i \<noteq> k\<close>.\<close>
    assume C0: "count_list (v @ x) C = 0"
    define i0 where "i0 = Suc (2 * fact n div count_list (v @ x) A)"
    let ?word = "u @ v ^^ i0 @ w @ x ^^ i0 @ y"
    have wordA: "count_list ?word A = n + 2 * fact n"
      using countX dvd2A i0_def zA zsplit by auto
    have wordC: "count_list ?word C = n + 2 * fact n"
      by (metis C0 countX count_list_append mult_is_0 zC zsplit)
    from wordA wordC L4_counts_distinct(3)[OF pumpL4[of i0]] show False by simp
  qed
qed

end
