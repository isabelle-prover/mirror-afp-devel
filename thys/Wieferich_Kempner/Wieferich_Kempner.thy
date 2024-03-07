(*  Author:      Jamie Chen
    License:     LGPL      *)

theory "Wieferich_Kempner"
  imports  
  "HOL-Number_Theory.Cong"
  "HOL.Real"
  "HOL.NthRoot"
  "HOL.Transcendental"
  "HOL-Library.Code_Target_Nat"
  "Three_Squares.Three_Squares"
  Main
begin

fun sumpow :: "nat \<Rightarrow> nat list \<Rightarrow> nat" where [code_computation_unfold, coercion_enabled]:
  "sumpow p l = fold (+) (map (\<lambda>x. x^p) l) 0"
declare sumpow.simps[code]

definition is_sumpow :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool"
  where "is_sumpow p n m \<equiv> \<exists> l. length l = n \<and> m = sumpow p l"

section \<open>Technical Lemmas\<close>
text\<open>We show four lemmas used in the main theorem.\<close>
subsection \<open> Lemma 2.1 in \cite{nathanson1996}\<close>

lemma sum_of_6_cubes:
  fixes A m :: nat
  assumes mLessASq: "m \<le> A\<^sup>2"
  assumes mIsSum3Sq: "is_sumpow 2 3 m"
  shows "is_sumpow 3 6 (6 * A * (A\<^sup>2 + m))"
proof -
  from mIsSum3Sq obtain l where "length l = 3" and " m = sumpow 2 l"
    using is_sumpow_def by blast
  then obtain m\<^sub>1 m\<^sub>2 m\<^sub>3 where "l = [m\<^sub>1, m\<^sub>2, m\<^sub>3]"
    by (smt (verit, best) Suc_length_conv length_0_conv numeral_3_eq_3)

  obtain il where "il = map (int) l" by auto
  obtain iA where "iA = (int A)" by auto
  obtain im where "im = (int m)" by auto

  have "fold (+) (map power2 l) 0 = m\<^sub>1\<^sup>2 + m\<^sub>2\<^sup>2 + m\<^sub>3\<^sup>2"
    using \<open>l = [m\<^sub>1, m\<^sub>2, m\<^sub>3]\<close> by simp
  hence "m = m\<^sub>1\<^sup>2 + m\<^sub>2\<^sup>2 + m\<^sub>3\<^sup>2"
    using \<open>length l = 3\<close> \<open>m = sumpow 2 l\<close> sumpow.simps by presburger
  obtain im\<^sub>1 im\<^sub>2 im\<^sub>3 where "il = [im\<^sub>1, im\<^sub>2, im\<^sub>3]"
    by (simp add: \<open>il = map int l\<close> \<open>l = [m\<^sub>1, m\<^sub>2, m\<^sub>3]\<close>)
  hence "im\<^sub>1 = int m\<^sub>1" and "im\<^sub>2 = int m\<^sub>2" and "im\<^sub>3 = int m\<^sub>3"
    using \<open>il = map int l\<close> \<open>l = [m\<^sub>1, m\<^sub>2, m\<^sub>3]\<close> by auto

  obtain x\<^sub>1 x\<^sub>2 x\<^sub>3 where "[x\<^sub>1,x\<^sub>2,x\<^sub>3] = map (\<lambda>x. A+x) l"
    by (simp add: \<open>l =[m\<^sub>1,m\<^sub>2,m\<^sub>3]\<close>)
  obtain x\<^sub>4 x\<^sub>5 x\<^sub>6 where "[x\<^sub>4,x\<^sub>5,x\<^sub>6] = map (\<lambda>x. A-x) l"
    by (simp add: \<open>l =[m\<^sub>1,m\<^sub>2,m\<^sub>3]\<close>)
  obtain ns where "ns =  [x\<^sub>1, x\<^sub>2, x\<^sub>3, x\<^sub>4, x\<^sub>5, x\<^sub>6]" by auto

  have "\<forall> x \<in> set l. x \<ge> 0"
    by auto
  hence "\<forall> x \<in> set l. x\<^sup>2 \<le> m"
    using\<open>l = [m\<^sub>1, m\<^sub>2, m\<^sub>3]\<close> \<open>m = m\<^sub>1\<^sup>2 + m\<^sub>2\<^sup>2 + m\<^sub>3\<^sup>2\<close> power2_nat_le_imp_le by auto
  have "\<forall> x \<in> set il. x \<ge> 0"
    by (simp add: \<open>il = map int l\<close>)
  hence "\<forall> x \<in> set il. x\<^sup>2 \<le> im"
    using\<open>im = int m\<close> \<open>il = map int l\<close>\<open>l = [m\<^sub>1, m\<^sub>2, m\<^sub>3]\<close> \<open>m = m\<^sub>1\<^sup>2 + m\<^sub>2\<^sup>2 + m\<^sub>3\<^sup>2\<close> power2_nat_le_imp_le 
    by auto

  have "\<forall> x \<in> set il. iA + x \<ge> 0"
    using \<open>iA = int A\<close> \<open>il = map int l\<close> by auto
  have "int (x\<^sub>1) = iA + im\<^sub>1"
    using \<open>[x\<^sub>1, x\<^sub>2, x\<^sub>3] = map ((+) A) l\<close> \<open>iA = int A\<close> \<open>il = [im\<^sub>1, im\<^sub>2, im\<^sub>3]\<close> \<open>il = map int l\<close> by force
  have "int (x\<^sub>2) = iA + im\<^sub>2"
    using \<open>[x\<^sub>1, x\<^sub>2, x\<^sub>3] = map ((+) A) l\<close> \<open>iA = int A\<close> \<open>il = [im\<^sub>1, im\<^sub>2, im\<^sub>3]\<close> \<open>il = map int l\<close> by force
  have "int (x\<^sub>3) = iA + im\<^sub>3"
    using \<open>[x\<^sub>1, x\<^sub>2, x\<^sub>3] = map ((+) A) l\<close> \<open>iA = int A\<close> \<open>il = [im\<^sub>1, im\<^sub>2, im\<^sub>3]\<close> \<open>il = map int l\<close> by force
  have "A \<ge> m\<^sub>1"
    by (metis \<open>m = m\<^sub>1\<^sup>2 + m\<^sub>2\<^sup>2 + m\<^sub>3\<^sup>2\<close> add_leE mLessASq power2_nat_le_eq_le)
  hence "iA - im\<^sub>1 \<ge> 0"
    using \<open>iA = int A\<close> \<open>il = [im\<^sub>1, im\<^sub>2, im\<^sub>3]\<close> \<open>il = map int l\<close> \<open>l = [m\<^sub>1, m\<^sub>2, m\<^sub>3]\<close> by auto
  hence "int x\<^sub>4 = iA - im\<^sub>1"
    using \<open>[x\<^sub>4, x\<^sub>5, x\<^sub>6] = map ((-) A) l\<close> \<open>iA = int A\<close> \<open>im\<^sub>1 = int m\<^sub>1\<close> \<open>l = [m\<^sub>1, m\<^sub>2, m\<^sub>3]\<close> by auto
  have "A \<ge> m\<^sub>2"
    by (metis \<open>m = m\<^sub>1\<^sup>2 + m\<^sub>2\<^sup>2 + m\<^sub>3\<^sup>2\<close> add_leE mLessASq power2_nat_le_eq_le)
  hence "iA - im\<^sub>2 \<ge> 0"
    using \<open>iA = int A\<close> \<open>il = [im\<^sub>1, im\<^sub>2, im\<^sub>3]\<close> \<open>il = map int l\<close> \<open>l = [m\<^sub>1, m\<^sub>2, m\<^sub>3]\<close> by auto
  hence "int x\<^sub>5 = iA - im\<^sub>2"
    using \<open>[x\<^sub>4, x\<^sub>5, x\<^sub>6] = map ((-) A) l\<close> \<open>iA = int A\<close> \<open>im\<^sub>2 = int m\<^sub>2\<close>\<open>l = [m\<^sub>1, m\<^sub>2, m\<^sub>3]\<close> by auto
  have "A \<ge> m\<^sub>3"
    by (metis \<open>m = m\<^sub>1\<^sup>2 + m\<^sub>2\<^sup>2 + m\<^sub>3\<^sup>2\<close> add_leE mLessASq power2_nat_le_eq_le)
  hence "iA - im\<^sub>3 \<ge> 0"
    using \<open>iA = int A\<close> \<open>il = [im\<^sub>1, im\<^sub>2, im\<^sub>3]\<close> \<open>il = map int l\<close> \<open>l = [m\<^sub>1, m\<^sub>2, m\<^sub>3]\<close> by auto
  hence "int x\<^sub>6 = iA - im\<^sub>3"
    using \<open>[x\<^sub>4, x\<^sub>5, x\<^sub>6] = map ((-) A) l\<close> \<open>iA = int A\<close> \<open>im\<^sub>3 = int m\<^sub>3\<close> \<open>l = [m\<^sub>1, m\<^sub>2, m\<^sub>3]\<close> by auto

  have "6*A*(A\<^sup>2+m) = 6*A*(A\<^sup>2 + sumpow 2 l)"
    by (simp add:\<open>m = sumpow 2 l\<close>)
  have distr: "\<dots> = 6*A^3 +6*A*(sumpow 2 l)"
    by (simp add: distrib_left power2_eq_square power3_eq_cube) 
  have "\<dots> = 6*A*(A\<^sup>2 + m\<^sub>1\<^sup>2 + m\<^sub>2\<^sup>2 + m\<^sub>3\<^sup>2)"
    using \<open>m = m\<^sub>1\<^sup>2 + m\<^sub>2\<^sup>2 + m\<^sub>3\<^sup>2\<close> \<open>m = sumpow 2 l\<close> by (metis distr group_cancel.add1)
  hence expanded: "int \<dots> = 6*iA*(iA\<^sup>2 +  im\<^sub>1\<^sup>2 +im\<^sub>2\<^sup>2 + im\<^sub>3\<^sup>2)"
    using \<open>iA = int A\<close> \<open>im\<^sub>1 = int m\<^sub>1\<close> \<open>im\<^sub>2 = int m\<^sub>2\<close> \<open>im\<^sub>3 = int m\<^sub>3\<close> by simp
  have sixcubes: "\<dots> = (iA + im\<^sub>1)^3 + (iA - im\<^sub>1)^3 +
                       (iA + im\<^sub>2)^3 + (iA - im\<^sub>2)^3 +
                       (iA + im\<^sub>3)^3 + (iA - im\<^sub>3)^3"
    by Groebner_Basis.algebra
  have "\<dots> = int x\<^sub>1^3 + int x\<^sub>2^3 + int x\<^sub>3^3 + int x\<^sub>4^3 + int x\<^sub>5^3 + int x\<^sub>6^3"
    using \<open>int x\<^sub>1 = iA + im\<^sub>1\<close> \<open>int x\<^sub>2 = iA + im\<^sub>2\<close> \<open>int x\<^sub>3 = iA + im\<^sub>3\<close> 
          \<open>int x\<^sub>4 = iA - im\<^sub>1\<close> \<open>int x\<^sub>5 = iA - im\<^sub>2\<close> \<open>int x\<^sub>6 = iA - im\<^sub>3\<close> by simp
  hence "6*A*(A\<^sup>2+m) = x\<^sub>1^3 + x\<^sub>2^3 + x\<^sub>3^3 + x\<^sub>4^3 + x\<^sub>5^3 + x\<^sub>6^3"
    using distr \<open>m = sumpow 2 l\<close> \<open>m = m\<^sub>1\<^sup>2 + m\<^sub>2\<^sup>2 + m\<^sub>3\<^sup>2\<close> expanded of_nat_eq_iff sixcubes 
    by (smt (verit) of_nat_add of_nat_power)
  have "map (\<lambda>x. x^3) ns = [x\<^sub>1^3, x\<^sub>2^3, x\<^sub>3^3, x\<^sub>4^3, x\<^sub>5^3, x\<^sub>6^3]"
    by (simp add: \<open>ns = [x\<^sub>1, x\<^sub>2, x\<^sub>3, x\<^sub>4, x\<^sub>5, x\<^sub>6]\<close>)
  hence "sumpow 3 ns = x\<^sub>1^3 + x\<^sub>2^3 + x\<^sub>3^3 + x\<^sub>4^3 + x\<^sub>5^3 + x\<^sub>6^3"
    by (simp add: \<open>ns = [x\<^sub>1, x\<^sub>2, x\<^sub>3, x\<^sub>4, x\<^sub>5, x\<^sub>6]\<close>)
  hence "6*A*(A\<^sup>2+m) = sumpow 3 ns"
    using \<open>6 * A * (A\<^sup>2 + m) = x\<^sub>1 ^ 3 + x\<^sub>2 ^ 3 + x\<^sub>3 ^ 3 + x\<^sub>4 ^ 3 + x\<^sub>5 ^ 3 + x\<^sub>6 ^ 3\<close> by presburger
  hence "length ns = 6 \<and> 6*A*(A\<^sup>2+m) = sumpow 3 ns"
    by (simp add: \<open>ns = [x\<^sub>1, x\<^sub>2, x\<^sub>3, x\<^sub>4, x\<^sub>5, x\<^sub>6]\<close>)
  then show ?thesis
    using is_sumpow_def by blast
qed

subsection \<open> Lemma 2.2 in \cite{nathanson1996}\<close>

lemma if_cube_cong_then_cong:
  fixes t :: nat
  fixes b\<^sub>1 b\<^sub>2 :: int
  assumes odd: "odd b\<^sub>1 \<and> odd b\<^sub>2"
  assumes "b\<^sub>1 > 0 \<and> b\<^sub>2 > 0"
  assumes tGeq1: "t \<ge> 1"
  assumes "[b\<^sub>1^3 = b\<^sub>2^3] (mod 2^t)"
  shows "[b\<^sub>1 \<noteq> b\<^sub>2] (mod 2^t) \<Longrightarrow> [b\<^sub>1^3 \<noteq> b\<^sub>2^3] (mod 2^t)"
proof -
  have "[b\<^sub>2^3 - b\<^sub>1^3 = 0] (mod 2^t)"
    using \<open>[b\<^sub>1 ^ 3 = b\<^sub>2 ^ 3] (mod 2 ^ t)\<close> cong_diff_iff_cong_0 cong_sym_eq by blast
  have "(b\<^sub>2 - b\<^sub>1)*(b\<^sub>2\<^sup>2 + b\<^sub>2*b\<^sub>1 + b\<^sub>1\<^sup>2) = b\<^sub>2^3 - b\<^sub>1^3"
    by Groebner_Basis.algebra
  hence "[(b\<^sub>2-b\<^sub>1)*(b\<^sub>2\<^sup>2 + b\<^sub>2*b\<^sub>1 + b\<^sub>1\<^sup>2) = 0] (mod 2^t)"
    using \<open>[b\<^sub>2 ^ 3 - b\<^sub>1 ^ 3 = 0] (mod 2 ^ t)\<close> by auto
  have "coprime (b\<^sub>2\<^sup>2 + b\<^sub>2*b\<^sub>1 + b\<^sub>1\<^sup>2) (2^t)"
    by (simp add: odd)
  hence "[b\<^sub>2 - b\<^sub>1 = 0] (mod 2^t)"
    by (metis \<open>[(b\<^sub>2 - b\<^sub>1) * (b\<^sub>2\<^sup>2 + b\<^sub>2 * b\<^sub>1 + b\<^sub>1\<^sup>2) = 0] (mod 2 ^ t)\<close> cong_mult_rcancel mult_zero_left)
  hence "[b\<^sub>1 = b\<^sub>2] (mod 2^t)"
    using cong_diff_iff_cong_0 cong_sym_eq by blast
  assume "[b\<^sub>1 \<noteq> b\<^sub>2] (mod 2^t)"
  then show ?thesis
    using \<open>[b\<^sub>1 = b\<^sub>2] (mod 2^t)\<close> by auto
qed

lemma every_odd_nat_cong_cube:
  fixes t w :: nat
  assumes tPositive: "t \<ge> 1"
  assumes wOdd: "odd w"
  shows "\<exists>b. odd b \<and> [w = b^3] (mod 2^t)"
proof (rule ccontr)
  assume "\<not>?thesis"
  hence "\<forall>b. odd b \<longrightarrow> [w \<noteq> b^3] (mod 2^t)"
    by blast
  obtain b::nat where "odd b"
    using odd_numeral by blast
  hence "[w \<noteq> b^3] (mod 2^t)"
    by (simp add: \<open>\<forall>b. odd b \<longrightarrow> [w \<noteq> b ^ 3] (mod 2 ^ t)\<close>)
  obtain bSet::"nat set" where bSet_def: "bSet = {x. odd x \<and> x < 2^t}"
    by auto
  obtain w' where w'_def: "w' = w mod 2^t"
    by auto
  hence "odd w'"
    by (metis dvd_mod_imp_dvd dvd_power order_less_le_trans tPositive wOdd zero_less_one)
  have "w' < 2^t"
    by (simp add: \<open>w' = w mod 2^t\<close>)
  hence "w' \<in> bSet"
    by (simp add: \<open>bSet = {x. odd x \<and> x < 2 ^ t}\<close> \<open>odd w'\<close>)
  define bSetMinusW'::"nat set" where "bSetMinusW' = {x. x \<in> bSet \<and> x \<noteq> w'}"

  have "\<forall>x \<in> bSet. [w \<noteq> x^3] (mod 2^t)"
    using \<open>\<forall>b. odd b \<longrightarrow> [w \<noteq> b ^ 3] (mod 2 ^ t)\<close> \<open>bSet = {x. odd x \<and> x < 2 ^ t}\<close> by blast
  have "\<forall>x \<in> bSet. odd (x^3)"
    using bSet_def by simp
  have "even (2^t)"
    using tPositive by fastforce
  hence "\<forall>x \<in> bSet. odd (x^3 mod 2^t)"
    using \<open>\<forall>x\<in>bSet. odd (x^3)\<close> dvd_mod_iff by blast
  hence "\<forall> x \<in> bSet. (x^3 mod 2^t) \<in> bSet"
    by (simp add: \<open>bSet = {x. odd x \<and> x < 2 ^ t}\<close>)
  hence "\<forall> x \<in> bSet. (x^3 mod 2^t) \<in> bSetMinusW'"
    using \<open>\<forall>x\<in>bSet. [w \<noteq> x ^ 3] (mod 2 ^ t)\<close> bSetMinusW'_def w'_def cong_def
    by (metis (mono_tags, lifting) mem_Collect_eq unique_euclidean_semiring_class.cong_def)
  hence "\<forall> x \<in> bSet. \<exists> y \<in> bSetMinusW'. [y = x^3] (mod 2^t)"
    using cong_mod_right cong_refl by blast
  hence "\<forall> x \<in> bSet. \<exists>! y \<in> bSetMinusW'. [y = x^3] (mod 2^t)"
    by (metis (no_types, lifting) bSet_def bSetMinusW'_def unique_euclidean_semiring_class.cong_def 
        mem_Collect_eq mod_less)
  have "\<forall> x\<^sub>1 \<in> bSet.\<forall> x\<^sub>2 \<in> bSet. odd x\<^sub>1 \<and> odd x\<^sub>2"
    using bSet_def by auto

  hence "\<forall> x\<^sub>1 \<in> bSet. \<forall> x\<^sub>2 \<in> bSet. [x\<^sub>1 \<noteq> x\<^sub>2] (mod 2^t) \<longrightarrow> [x\<^sub>1^3 \<noteq> x\<^sub>2^3] (mod 2^t)"
    by (metis (mono_tags) cong_int_iff even_of_nat if_cube_cong_then_cong odd_pos of_nat_0_less_iff 
        of_nat_numeral of_nat_power tPositive)
  hence "\<forall> x\<^sub>1 \<in> bSet. \<forall> x\<^sub>2 \<in> bSet. x\<^sub>1 \<noteq> x\<^sub>2 \<longrightarrow> [x\<^sub>1^3 \<noteq> x\<^sub>2^3] (mod 2^t)"
    using bSet_def cong_less_modulus_unique_nat by blast
  hence "inj_on (\<lambda> x. x^3 mod 2^t) bSet"
    by (meson inj_onI unique_euclidean_semiring_class.cong_def)

  have "bSetMinusW' \<subset> bSet"
    using bSetMinusW'_def \<open>w' \<in> bSet\<close> by blast 
  moreover hence "card bSetMinusW' < card bSet"
    by (simp add: bSet_def psubset_card_mono)
  moreover have "(\<lambda> x. x^3 mod 2^t) ` bSet \<subseteq> bSetMinusW'"
    using \<open>\<forall>x\<in>bSet. x ^ 3 mod 2 ^ t \<in> bSetMinusW'\<close> by blast
  ultimately have "card ((\<lambda> x. x^3 mod 2^t) ` bSet) < card bSet"
    by (metis card.infinite less_zeroE psubset_card_mono subset_psubset_trans)
  hence "\<not>inj_on (\<lambda> x. x^3 mod 2^t) bSet"
    using pigeonhole by auto
  thus False
    using \<open>inj_on (\<lambda>x. x ^ 3 mod 2 ^ t) bSet\<close> by blast
qed

subsection \<open> Lemma 2.3 in \cite{nathanson1996}\<close>
text\<open>It is this section in which we use the Three Squares Theorem AFP Entry \cite{Three_Squares-AFP}.\<close>

lemma sum_of_3_squares_exceptions:
  fixes m::nat
  assumes notSum3Sq: "\<not>is_sumpow 2 3 m"
  shows "6*m mod 96 \<in> {0,72,42,90}"
proof -
  have "\<not>(\<exists> l. length l = 3 \<and> m = sumpow 2 l)"
    using is_sumpow_def notSum3Sq by blast
  hence "\<not>(\<exists> a b c. m = sumpow 2 [a,b,c])"
    by (metis length_Cons list.size(3) numeral_3_eq_3)
  hence "\<not>(\<exists> a b c. m = fold (+) (map power2 [a,b,c]) 0)"
    by auto
  hence "\<not>(\<exists> a b c. m = fold (+) [a\<^sup>2,b\<^sup>2,c\<^sup>2] 0)"
    by auto
  hence "\<not>(\<exists> a b c. m = a\<^sup>2 + b\<^sup>2 + c\<^sup>2)"
    by (simp add: add.commute)
  then obtain s t where "(m = 4^s*(8*t + 7))"
    using three_squares_iff by auto
  obtain h'::"nat set" where "h' = {0,72,42,90}" 
    by auto
  consider (s0) "s = 0"| (s1) "s = 1" | (s2) "s\<ge>2"
    by arith
  hence "6*4^s*(8*t + 7) mod 96 \<in> h'"
  proof cases
    case s0
    consider (even) "even t" | (odd) "odd t"
      by auto
    thus "6*4^s*(8*t + 7) mod 96 \<in> h'"
    proof cases
      case even
      obtain t' where "t' =  t div 2"
        by simp
      hence "6*4^s*(8*t+7) = 96*t' + 42"
        using s0 even by fastforce
      hence "6*4^s*(8*t+7) mod 96 = 42"
        by (simp add: cong_0_iff cong_add_rcancel_0_nat)
      have "42 \<in> h'"
        by (simp add: \<open>h' = {0, 72, 42, 90}\<close>)
      thus "6*4^s*(8*t + 7) mod 96 \<in> h'"
        by (simp add: \<open>6 * 4 ^ s * (8 * t + 7) mod 96 = 42\<close>)
    next
      case odd
      obtain t' where "t' =  (t-1) div 2"
        by simp
      hence "6*4^s*(8*t+7) = 6*(8*(2*t'+1)+7)"
        by (simp add: s0 odd)
      hence "6*4^s*(8*t+7) mod 96 = 90"
        using cong_le_nat by auto
      have "90 \<in> h'"
        by (simp add: \<open>h' = {0, 72, 42, 90}\<close>)
      thus "6*4^s*(8*t + 7) mod 96 \<in> h'"
        by (simp add: \<open>6 * 4 ^ s * (8 * t + 7) mod 96 = 90\<close>)
    qed
  next
    case s1
    have "6*4^s*(8*t+7) = 96*(2*t + 1) + 72"
      using s1 by auto
    hence "[6*4^s*(8*t+7) = 72] (mod 96)"
    by (metis cong_add_rcancel_0_nat cong_mult_self_left)
  hence "6*4^s*(8*t+7) mod 96 = 72 mod 96"
    using unique_euclidean_semiring_class.cong_def by blast
    hence "6*4^s*(8*t+7) mod 96 = 72"
      by auto
    have "72 \<in> h'"
      by (simp add: \<open>h' = {0, 72, 42, 90}\<close>)
    thus "6*4^s*(8*t + 7) mod 96 \<in> h'"
      by (simp add:\<open>6 * 4 ^ s * (8 * t + 7) mod 96 = 72\<close>)
  next
    case s2
    obtain s' where "s' = s-2"
      by simp
    have "6*4^s*(8*t+7) = 6*4^2*4^s'*(8*t+7)"
      by (metis \<open>s' = s - 2\<close> le_add_diff_inverse mult.assoc power_add s2)
    have "\<dots> = 96*4^s'*(8*t+7)"
      by auto
    hence "[6*4^s*(8*t+7) = 0] (mod 96)"
      by (metis \<open>6*4^s*(8*t + 7) = 6*4\<^sup>2*4^s'*(8*t + 7)\<close> cong_modulus_mult_nat cong_mult_self_left)
    hence "6*4^s*(8*t+7) mod 96 = 0 mod 96"
    using unique_euclidean_semiring_class.cong_def by blast
    hence "6*4^s*(8*t+7) mod 96 = 0"
      by auto
    have "0 \<in> h'"
      by (simp add: \<open>h' = {0, 72, 42, 90}\<close>)
    thus "6*4^s*(8*t + 7) mod 96 \<in> h'"
      by (simp add: \<open>6 * 4 ^ s * (8 * t + 7) mod 96 = 0\<close>)
  qed
  thus ?thesis
     by (metis \<open>h' = {0, 72, 42, 90}\<close> \<open>m = 4 ^ s * (8 * t + 7)\<close> mult.assoc)
qed

lemma values_geq_22_cubed_can_be_normalised:
  fixes r :: nat
  assumes rLarge: " r \<ge> 10648" (*10648 = 22\<^sup>3*)
  obtains d m where "d \<ge> 0" and "d \<le> 22" and "r = d^3 + 6*m" and "is_sumpow 2 3 m"
proof -
  define MultiplesOf6LessThan96::"nat set" where 
    "MultiplesOf6LessThan96 = {0,6,12,18,24,30,36,42,48,54,60,66,72,78,84,90}"
  have "\<forall>m' \<in>  MultiplesOf6LessThan96. m' < 96"
    unfolding MultiplesOf6LessThan96_def by auto
  have "\<forall> m' \<in> MultiplesOf6LessThan96. m' mod 6 = 0"
    unfolding MultiplesOf6LessThan96_def by auto
  hence "\<forall>m \<in> MultiplesOf6LessThan96. \<exists>n. m = 6*n"
     by fastforce
  have "\<forall>m' \<in> MultiplesOf6LessThan96. m' mod 96 = m'"
    by (simp add: \<open>\<forall>m'\<in>MultiplesOf6LessThan96. m' < 96\<close>)

  define H'::"nat set" where "H' = {0,42,72,90}"

  have "\<forall>m'. 6*m' mod 96 \<notin> H' \<longrightarrow> is_sumpow 2 3 m'"
    unfolding H'_def using sum_of_3_squares_exceptions by blast
  hence "\<forall>m'. (6*m' mod 96 \<in> MultiplesOf6LessThan96 - H') \<longrightarrow> is_sumpow 2 3 m'"
    by fastforce

  define H::"nat set" where "H = {6, 12, 18, 24, 30, 36, 48, 54, 60, 66, 78, 84}"
  have "H =  MultiplesOf6LessThan96 - H'"
    unfolding H_def MultiplesOf6LessThan96_def H'_def by auto
  hence "\<forall>m'. 6*m' mod 96 \<in> H \<longrightarrow> is_sumpow 2 3 m'"
    using \<open>\<forall>m'. 6 * m' mod 96 \<in> MultiplesOf6LessThan96 - H' \<longrightarrow> is_sumpow 2 3 m'\<close> by blast

  define D::"nat set" where "D = {0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22}"
  have "\<forall>d \<in> D. d \<ge> 0 \<and> d \<le> 22"
    using D_def by auto
  define residue::"nat set" where "residue = {x. \<exists> h \<in> H. \<exists> d \<in> D. x = (d^3 + h) mod 96}"
(*for some reason Isabelle doesn't like it when you do this in steps larger than 10*)
  have "\<forall>x<10. x \<in> residue"
    unfolding residue_def H_def D_def by auto
  moreover have "\<forall>x\<ge> 10. x < 19 \<longrightarrow> x \<in> residue"
    unfolding residue_def H_def D_def by auto
  moreover have "\<forall>x\<ge> 19. x < 28 \<longrightarrow> x \<in> residue"
    unfolding residue_def H_def D_def by auto
  moreover have "\<forall>x\<ge> 28. x < 37 \<longrightarrow> x \<in> residue"
    unfolding residue_def H_def D_def by auto
  moreover have "\<forall>x\<ge> 37. x < 46 \<longrightarrow> x \<in> residue"
    unfolding residue_def H_def D_def by auto
  moreover have "\<forall>x\<ge> 46. x < 55 \<longrightarrow> x \<in> residue"
    unfolding residue_def H_def D_def by auto
  moreover have "\<forall>x\<ge> 55. x < 64 \<longrightarrow> x \<in> residue"
    unfolding residue_def H_def D_def by auto
  moreover have "\<forall>x\<ge> 64. x < 73 \<longrightarrow> x \<in> residue"
    unfolding residue_def H_def D_def by auto
  moreover have "\<forall>x\<ge> 73. x < 82 \<longrightarrow> x \<in> residue"
    unfolding residue_def H_def D_def by auto
  moreover have "\<forall>x\<ge> 82. x < 91 \<longrightarrow> x \<in> residue"
    unfolding residue_def H_def D_def by auto
  moreover have "\<forall>x\<ge> 91. x < 96 \<longrightarrow> x \<in> residue"
    unfolding residue_def H_def D_def by auto
  ultimately have "\<forall>x < 96. x \<in> residue"
    by (metis leI)

  have "\<forall> r \<in> residue. \<exists> h \<in> H. \<exists> d \<in> D. r = (d^3 + h) mod 96"
    unfolding residue_def by auto
  have "\<forall> h \<in> H. \<forall> d \<in> D. (d^3 + h) mod 96 \<in> residue"
    by (simp add: \<open>\<forall>x<96. x \<in> residue\<close>)
  have "r mod 96 \<in> residue"
    by (simp add: \<open>\<forall>x<96. x \<in> residue\<close>)
  have "\<forall>d \<in> D. r \<ge> d^3"
    unfolding D_def using rLarge by auto
  hence "\<exists> h \<in> H. \<exists> d \<in> D. [d^3 + h = r] (mod 96)"
    using \<open>r mod 96 \<in> residue\<close>
    by (metis \<open>\<forall>r\<in>residue. \<exists>h\<in>H. \<exists>d\<in>D. r = (d ^ 3 + h) mod 96\<close> unique_euclidean_semiring_class.cong_def)
  hence "\<exists> h \<in> H. \<exists> d \<in> D. [r - d^3 = h] (mod 96)"
    by (smt (z3) \<open>\<forall>d\<in>D. d^3 \<le> r\<close> add.commute add_diff_cancel_right' cong_diff_nat cong_refl le_add2)
  then obtain h d where "h \<in> H" and "d \<in> D" and "[r - d^3 = h] (mod 96)"
    by auto
  then obtain h' where "h' mod 96 = h" and "r - d^3 = h'"
    using \<open>H = MultiplesOf6LessThan96 - H'\<close> \<open>\<forall>m'\<in>MultiplesOf6LessThan96. m' mod 96 = m'\<close> 
    by (simp add: unique_euclidean_semiring_class.cong_def)
  have "[h = 0] (mod 6)"
    using \<open>H = MultiplesOf6LessThan96 - H'\<close> \<open>\<forall>m\<in>MultiplesOf6LessThan96. \<exists>n. m = 6*n\<close> \<open>h \<in> H\<close> 
      cong_mult_self_left by fastforce
  hence "[h' = 0] (mod 6)"
    using \<open>[r-d^3 = h] (mod 96)\<close> \<open>r-d^3 = h'\<close> unique_euclidean_semiring_class.cong_def
    by (metis cong_dvd_modulus_nat dvd_triv_right num_double numeral_mult)
  then obtain m where "6*m = h'"
    by (metis cong_0_iff dvd_def)
  moreover hence "is_sumpow 2 3 m"
    using \<open>\<forall>m'. 6 * m' mod 96 \<in> H \<longrightarrow> is_sumpow 2 3 m'\<close> by (simp add:\<open>h \<in> H\<close> \<open>h' mod 96 = h\<close>)
  moreover have "d \<ge> 0" 
    by auto
  moreover have "d \<le> 22"
    by (simp add: \<open>\<forall>d\<in>D. 0 \<le> d \<and> d \<le> 22\<close> \<open>d \<in> D\<close>)
  ultimately show "?thesis"
    by (metis \<open>\<forall>d\<in>D. d ^ 3 \<le> r\<close> \<open>d \<in> D\<close>\<open>r - d ^ 3 = h'\<close> le_add_diff_inverse that)
qed

subsection \<open>Lemma 2.4 in \cite{nathanson1996}\<close>

partial_function(tailrec) list_builder :: "nat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> nat list" 
  where [code_computation_unfold, coercion_enabled]:
    "list_builder m n l = (if n = 0 then l else (list_builder m (n-1) (m#l)))"
declare list_builder.simps[code]

partial_function(tailrec) dec_list :: "nat \<Rightarrow> nat list \<Rightarrow> nat list" 
  where [code_computation_unfold, coercion_enabled]:
    "dec_list depth l = (if (tl l) = [] then list_builder (hd l + 1) (depth+1) [] else 
    if hd l \<le> hd (tl l) + 1 then dec_list (depth+1) ((hd (tl l) + 1)#(tl (tl l))) else
    list_builder (hd (tl l) + 1) (depth + 2) (tl (tl l)))"
declare dec_list.simps[code]

partial_function(tailrec) sumcubepow_finder ::"nat \<Rightarrow> nat list \<Rightarrow> nat list" 
  where [code_computation_unfold, coercion_enabled]:
    "sumcubepow_finder n l = (if (sumpow 3 l < n) then 
    (sumcubepow_finder n ((Suc (hd l))#(tl l)))
    else if (sumpow 3 l) = n then l else sumcubepow_finder n  (dec_list 0 l))"
declare sumcubepow_finder.simps[code]

lemma leq_40000_is_sum_of_9_cubes:
  fixes n :: nat
  assumes "n \<le> 40000"
  shows "is_sumpow 3 9 n" and "n > 8042 \<longrightarrow> is_sumpow 3 6 n"
proof -
  (* split computation into chunks so that computation is done in parallel *)
  let ?A1 = "[8043 ..< 15000]" 
  let ?A2 = "[15000 ..< 23000]" 
  let ?A3 = "[23000 ..< 29000]" 
  let ?A4 = "[29000 ..< 35000]" 
  let ?A5 = "[35000 ..< 40001]" 
  (* let expression to avoid duplicate computation of result *)
  let ?test = "\<lambda> n. let result = sumcubepow_finder n [0,0,0,0,0,0] in
     sumpow 3 result = n \<and> length result = 6" 
  have split: "\<And> n. n \<le> 40000 \<Longrightarrow> n > 8042 \<Longrightarrow> 
    n \<in> set ?A1 \<or> n \<in> set ?A2 \<or> n \<in> set ?A3 \<or> n \<in> set ?A4 \<or> n \<in> set ?A5" 
    unfolding set_upt by simp linarith
  have "\<forall> n \<in> set ?A1. ?test n"
    by eval (*takes a while to compute*)
  moreover have "\<forall>n \<in> set ?A2. ?test n"
    by eval (*takes a while to compute*)
  moreover have "\<forall>n \<in> set ?A3. ?test n"
    by eval (*takes a while to compute*)
  moreover have "\<forall>n \<in> set ?A4. ?test n"
    by eval (*takes a while to compute*)
  moreover have "\<forall>n \<in> set ?A5. ?test n"
    by eval (*takes a while to compute*)
  ultimately have "\<forall>n \<le> 40000. n > 8042 \<longrightarrow> ?test n" using split by blast
  then have "\<forall>n\<le>40000. n > 8042 \<longrightarrow> is_sumpow 3 6 n"
    using is_sumpow_def by metis
  then show "n > 8042 \<longrightarrow> is_sumpow 3 6 n"
    using \<open>n \<le> 40000\<close> by simp
  have "\<forall>n\<le>40000. n > 8042 \<longrightarrow> (\<exists> l. length l = 6 \<and> n = sumpow 3 l)"
    using is_sumpow_def \<open>\<forall>n\<le>40000. n > 8042 \<longrightarrow> is_sumpow 3 6 n\<close> by simp
  then have "\<forall>n\<le>40000. n > 8042 \<longrightarrow> (\<exists> l. length (l@[0,0,0]) = 9 \<and> n = sumpow 3 (l@[0,0,0]))"
    by simp
  then have "\<forall>n\<le>40000. n > 8042 \<longrightarrow> is_sumpow 3 9 n"
    using is_sumpow_def by blast
  have "\<forall>n \<le> 8042. let res = sumcubepow_finder n [0,0,0,0,0,0,0,0,0] in 
      sumpow 3 res = n \<and> length res = 9"
    by eval
  then have "\<forall>n\<le>8042. is_sumpow 3 9 n"
    using is_sumpow_def by metis
  then have "\<forall>n \<le> 40000. is_sumpow 3 9 n"
    using \<open>\<forall>n\<le>40000. n > 8042 \<longrightarrow> is_sumpow 3 9 n\<close> by auto
  then show "is_sumpow 3 9 n"
    using \<open> n \<le> 40000\<close> by simp
qed

section \<open>Wieferich--Kempner Theorem\<close>
text\<open>Theorem 2.1 in \cite{nathanson1996}\<close>

theorem Wieferich_Kempner:
  fixes N :: nat
  shows "is_sumpow 3 9 N"
proof cases
  consider (ge8pow10) "N > 8^10" | (leq8pow10) "N \<le> 8^10"
    by arith
  thus ?thesis
  proof cases
    case ge8pow10
    define n::int where "n = \<lfloor>root 3 N\<rfloor>"
    hence "n \<ge> \<lfloor>root 3 (8^10)\<rfloor>"
      by (meson floor_mono ge8pow10 less_imp_le_nat numeral_power_le_of_nat_cancel_iff 
          real_root_le_iff zero_less_numeral)
    have "(2::nat)^3 = 8"
      by simp
    hence "8^10 = ((2::nat)^10)^3"
      by simp
    have "root 3 ((2::nat)^10)^3 = (2::nat)^10"
      by simp
    hence "n \<ge> \<lfloor>(2::nat)^10\<rfloor>"
      by (metis \<open>8^10 = (2^10)^3\<close> \<open>\<lfloor>root 3 (8^10)\<rfloor> \<le> n\<close> of_nat_numeral of_nat_power power3_eq_cube 
          real_root_mult)
    hence ngeq2pow10: " n \<ge> (2::nat)^10"
      by auto
    obtain k::int where "k = \<lceil>(log 8 (N/8))/3\<rceil>-1"
      by simp
    hence "3*k < (log 8 (N/8))"
      by linarith
    hence "8*(8 powr (3*k)) < N"
      using ge8pow10 less_log_iff by simp
    have "k+1 \<ge> (log 8 (N/8))/3"
      by (simp add: \<open>k = \<lceil>log 8 (real N / 8) / 3\<rceil> - 1\<close>)
    hence "8 powr (3*(k+1)) \<ge> 8 powr (log 8 (N/8))"
      by simp
    hence "8*(8 powr (3*(k+1))) \<ge> N"
      using ge8pow10 by simp
    have "(N/8) > 8^9"
      using ge8pow10 by simp
    hence "(log 8 (N/8)) > 9"
      by (metis less_log_of_power numeral_One numeral_less_iff of_nat_numeral semiring_norm(76))
    hence "(log 8 (N/8))/3 > 3"
      by simp
    hence "k \<ge> 3"
      using \<open>k = \<lceil>(log 8 (N/8))/3\<rceil>-1\<close> by simp

    define i::int where "i = \<lfloor>root 3 (N - (8*(8 powr (3*k))))\<rfloor>"
    hence "i \<le> root 3 (N - (8*(8 powr (3*k))))"
      by fastforce
    have "root 3 (N - (8*(8 powr (3*k)))) \<ge> 0"
      using \<open>8*(8 powr (3 * k)) < N\<close> by force
    hence "i \<ge> 0"
      by (simp add: i_def)
    hence "i^3 \<le> (root 3 (N - (8*(8 powr (3*k)))))^3"
      using \<open>i \<le> root 3 (N - 8 * 8 powr (3*k))\<close> power_mono by fastforce    
    hence "i^3 \<le> N - (8*(8 powr (3*k)))"
      using \<open>8 * 8 powr (3*k) < N\<close> by force
    hence exp01:"8*(8 powr (3*k)) \<le> N - i^3"
      by simp
    have "i+1 > root 3 (N - (8*(8 powr (3*k))))"
      by (simp add: i_def)
    hence "(i+1)^3 > (root 3 (N - (8*(8 powr (3*k)))))^3"
      by (metis \<open>0 \<le> root 3 (N - 8 * 8 powr (3*k))\<close> of_int_power power_strict_mono zero_less_numeral)
    hence "(i+1)^3 > (N - (8*(8 powr (3*k))))"
      using \<open>8 * 8 powr (3*k) < N\<close> by force
    hence exp02:"8*(8 powr (3*k)) > N - (i+1)^3"
      by simp

    have "i \<ge> 1"
    proof (rule ccontr)
      assume "\<not> i\<ge> 1"
      hence "i = 0"
        using \<open>i \<ge> 0\<close> by simp
      hence "8*(8 powr (3*k)) \<le> N"
        using \<open>8*(8 powr (3*k)) \<le> N - i^3\<close> by simp
      moreover have "8*(8 powr (3*k)) + 1 > N"
        using \<open>i = 0\<close> \<open>(N - (i+1)^3) < 8*(8 powr (3*k))\<close> ge8pow10 by auto
      moreover have "\<forall> x. x \<le> N \<and> x + 1 > N \<longrightarrow> x = N"
        by linarith
      have "8*8^(nat(3*k)) = 8*(8 powr (3*k))"
        by (smt (verit, ccfv_SIG) \<open>3 \<le> k\<close> powr_real_of_int)
      ultimately have "8*(8 powr (3*k)) = N"
        by (metis nat_le_real_less nle_le of_nat_le_iff of_nat_numeral of_nat_power power.simps(2))
      thus False
        using \<open>8 * 8 powr (3 * k) < N\<close> by simp
    qed
    
    have "8 powr (3*(k+1)) = (8 powr (k+1))^3"
      by (metis of_int_mult of_int_numeral powr_ge_pzero powr_numeral powr_powr powr_powr_swap) 
    have "\<forall>(x::int)\<ge>1. x^3 - (x-1)^3  = 3*x^2 - 3*x +1"
      by Groebner_Basis.algebra
    hence "\<forall>(x::int)\<ge>1. x^3 - (x-1)^3  < 3*x^2"
      by auto
    have exp03:"\<forall>(x::int)\<ge>1. x \<le> n \<longrightarrow> 3*x^2 \<le> 3*(root 3 N)^2"
      using n_def by (simp add: le_floor_iff)
    have "root 3 N \<le> root 3 (8*(8 powr (3*(k+1))))"
      using \<open>N \<le> 8 * 8 powr (3 * (k + 1))\<close> by force
    moreover have "\<dots> = (root 3 8)*(root 3 ((8 powr ((k+1)))^3))"
      using \<open>8 powr (3*(k+1)) = (8 powr (k+1))^3\<close> real_root_mult by simp
    moreover have "\<dots> = 2*(8 powr ((k+1)))"
      using odd_real_root_power_cancel by simp
    ultimately have exp04:"(root 3 N)^2 \<le> (2*(8 powr (k+1)))^2"
      by (metis of_nat_0_le_iff power_mono real_root_pos_pos_le)
    moreover hence exp05: "\<dots> = (4*(8 powr ((k+1)))^2)"
      using four_x_squared by presburger
    moreover hence exp06:"\<dots> = (4*(8 powr (2*(k+1))))"
      by (smt (verit) of_int_add power2_eq_square powr_add)
    moreover hence "\<dots> = (8*(8 powr (2*k + 2))/2)"
      by simp
    moreover hence exp07:"\<dots> = (8 powr (2*k + 3)/2)"
      by (simp add: add.commute powr_mult_base)
    ultimately have exp08:"3*(root 3 N)^2 \<le> (3*8 powr (2*k + 3))/2"
      by linarith
    have exp09:"\<forall> x \<ge> 1. x \<le> n \<longrightarrow> real_of_int (x^3 - (x-1)^3) < real_of_int (3*x^2)"
      using \<open>\<forall>(x::int)\<ge>1. x^3 - (x-1)^3  < 3*x^2\<close> by presburger 
    hence "\<forall> x \<ge> 1. x \<le> n \<longrightarrow>x^3 - (x-1)^3 < 3*(root 3 N)^2"
      using exp03 less_le_trans 
      by fastforce
    hence exp10:"\<forall> x \<ge> 1. x \<le> n \<longrightarrow>x^3 - (x-1)^3 \<le> (3*8 powr (2*k + 3))/2"
      using exp08 by fastforce

    have "(root 3 N)^3 = N"
      by simp
    have "root 3 N < n+1"
      using n_def by linarith
    hence "(root 3 N)^3 < (n+1)^3"
      by (metis of_int_power of_nat_0_le_iff real_root_pos_pos_le zero_less_numeral power_strict_mono)
   
    text\<open>The following few lines have been slightly modified from the original proof to simplify 
formalisation.  This does not affect the proof in any meaningful way.\<close>
    hence exp11:"N - n^3 < (n+1)^3 - n^3"
      using \<open>(root 3 N)^3 = N\<close> by linarith
    have exp12:"\<dots> = 3*n^2 + 3*n + 1"
      by Groebner_Basis.algebra
    have exp13:"\<dots> \<le> 6*n^2 + 1"
      using \<open>n \<ge> (2::nat)^10\<close> power_strict_mono by (simp add: self_le_power)
    have "\<dots> \<le> 6*(root 3 N)^2 + 1"
      using n_def by auto
    have "\<dots> \<le> (3*8 powr (2*k + 3))+1"
      using \<open>3*(root 3 N)^2 \<le> (3*8 powr (2*k + 3))/2\<close> by auto
    hence exp14:"\<dots> \<le> 4*8 powr (2*k + 3)"
      using \<open>3 \<le> k\<close> ge_one_powr_ge_zero by auto
    hence exp15:"\<dots> \<le> 8*8 powr(3*k)"
      by (smt (verit, best) \<open>3 \<le> k\<close> of_int_le_iff powr_mono)

    have "6*n^2\<le> 3*8 powr (2*k + 3)"
      using \<open>6*(root 3 N)\<^sup>2 + 1 \<le> 3*8 powr (2*k + 3)+1\<close> \<open>(6*n\<^sup>2 + 1) \<le> 6*(root 3 N)\<^sup>2 + 1\<close> by linarith
    hence "i \<le> n-1"
      using exp12 exp14 exp13 exp01 i_def n_def exp11 exp15
      by (smt (verit, ccfv_SIG) floor_mono of_int_less_iff real_root_le_iff zero_less_numeral)
    hence "N - (i+1)^3 \<le> 8*8 powr (3*k)"
      using \<open>(int N - (i + 1) ^ 3) < 8 * 8 powr (3*k)\<close> by linarith
    hence "N \<ge> (i+1)^3"
      using exp04 exp06 exp15 exp07 exp01 exp03 exp09 \<open>i \<le> n - 1\<close> \<open>0 \<le> i\<close> 
      by (smt (verit, ccfv_threshold) divide_cancel_right exp05 of_int_0_le_iff of_int_diff)
    have exp16:"((i+1)^3 - i^3) \<le> 3*8 powr (2*k + 3)"
      using exp10 exp05 exp04 exp06 exp07 exp03 exp09 \<open>i \<le> n-1\<close> \<open>0\<le>i\<close>
      by (smt (verit, ccfv_SIG)  divide_cancel_right powr_non_neg)
    have "(i^3 - (i-1)^3) \<le> 3*8 powr (2*k + 3)"
      using exp10 exp05 exp04 exp06 exp07 exp03 exp09 \<open>i \<le> n-1\<close> \<open>1\<le>i\<close>
      by (smt (verit, ccfv_SIG) divide_cancel_right powr_non_neg)
    have "i^3 > (i-1)^3"
      by (smt (verit, best) power_minus_Bit1 power_mono_iff zero_less_numeral)
    have "N - (i-1)^3 = ((N - (i-1)^3)-(N-i^3)) + ((N-i^3) - (N-(i+1)^3)) + (N-(i+1)^3)"
      by simp
    have "\<dots> = (i^3 - (i-1)^3) + ((i+1)^3 - i^3) + (N-(i+1)^3)"
      by simp
    have exp17: "\<dots> < 3*8 powr (2*k + 3) + 8*8 powr (3*k)"              
      using \<open>N - (i+1)^3 \<le> 8*8 powr (3*k)\<close> \<open>i \<le> n-1\<close> \<open>1\<le>i\<close> \<open>0 \<le> i\<close> exp08 exp10 exp03 exp09
      by (smt (verit) field_sum_of_halves of_int_add of_int_diff power_strict_mono zero_less_numeral)
    have exp18:"\<dots> \<le> 11*(8 powr (3*k))"
      by (simp add: \<open>3 \<le> k\<close>)
    have "(even (i^3) \<and> odd ((i-1)^3)) \<or> (even ((i-1)^3) \<and> odd (i^3))"
      by simp
    hence "(even (N - i^3) \<and> odd (N - (i-1)^3)) \<or> (even (N - (i-1)^3) \<and> odd (N - i^3))"
      by auto
    hence "(even (N-(i-1)^3)) \<longrightarrow> odd (N-i^3)"
      by blast 
    obtain a::nat where a_def: "if odd (N-(i-1)^3) then a = i-1 else a = i"
      by (metis \<open>0 \<le> i\<close> \<open>1 \<le> i\<close> diff_ge_0_iff_ge nonneg_int_cases)
    have "a = int a"
      by simp
    consider (odd) "odd (N - (i-1)^3)" | (even) "even (N - (i-1)^3)"
      by blast
    hence "odd (N - a^3)"
    proof cases
      case odd
      have "int a = i-1"
        using a_def odd by simp
      have "odd (N - (i-1)^3)"
        using odd by simp
      hence "odd (N - (int a)^3)"
        using \<open>a = i-1\<close> by simp
      have "a^3 \<le> N"
        using \<open>N \<ge> (i+1)^3\<close> \<open>int a = i-1\<close> power_mono \<open>i \<ge> 1\<close>
        by (smt (verit, ccfv_SIG) of_nat_le_of_nat_power_cancel_iff)
      hence "N - a^3 = N - (int a)^3"
        by (simp add: of_nat_diff)
      thus ?thesis
        using \<open>odd (N - (int a)^3)\<close> by presburger
    next
      case even
      have "a = i"
        using a_def even by simp
      have "odd (N - i^3)"
        using \<open>(even (N-(i-1)^3)) \<longrightarrow> odd (N-i^3)\<close> even by simp
      hence "odd (N - (int a)^3)"
        using \<open>a = i\<close> by simp
      have "a^3 \<le> N"
        using \<open>N \<ge> (i+1)^3\<close> \<open>int a = i\<close> power_mono \<open>i \<ge> 1\<close>
        by (smt (verit, ccfv_SIG) of_nat_le_of_nat_power_cancel_iff)
      hence "N - a^3 = N - (int a)^3"
        by (simp add: of_nat_diff)
      thus ?thesis 
        using \<open>odd (N - (int a)^3)\<close> by presburger
    qed
    hence "odd (nat (N - a^3))"
      using nat_int by presburger
    moreover have "3*(nat k) \<ge> 1"
      using \<open>3 \<le> k\<close> by auto
    ultimately have "\<exists>b. odd b \<and> [(nat (N - a^3)) = b^3] (mod 2^(3*(nat k)))"
      using every_odd_nat_cong_cube by presburger
    then obtain b'::nat where "odd b'" and "[(nat (N - a^3)) = b'^3] (mod 2^(3*(nat k)))"
      by auto
    define b::nat where "b = b' mod (8^(nat k))"
    have "[nat (N - a^3) \<noteq> 0] (mod 2^(3*(nat k)))"
      by (meson \<open>1 \<le> 3 * nat k\<close> \<open>odd (nat (int (N - a ^ 3)))\<close> cong_0_iff even_power 
          cong_dvd_modulus_nat dvd_refl order_less_le_trans zero_less_one)
    hence "b > 0"
      by (metis \<open>1 \<le> 3 * nat k\<close> \<open>2 ^ 3 = 8\<close> b_def \<open>odd b'\<close> dvd_power gcd_nat.trans 
          mod_greater_zero_iff_not_dvd order_less_le_trans power_mult zero_less_one)
    hence "b^3 > 0"
      by simp

    have "b < 8 powr k"
      by (simp add: b_def powr_int)
    hence "b^3 < (8 powr (k))^3"
      using power_strict_mono by fastforce
    hence "b^3 < 8 powr (3*k)"
      by (metis mult.commute of_int_mult of_int_numeral powr_ge_pzero powr_numeral powr_powr)
    have "N - a^3 \<ge> 8*8 powr (3*k)"
      using \<open>(i - 1)^3 < i^3\<close> \<open>8 * 8 powr (3*k) \<le> N - i^3\<close>
      by (smt (verit, best)  a_def int_ops(6) of_int_less_iff of_int_of_nat_eq of_nat_power)
    
    have exp19:"7*8 powr (3*k) = 8*8 powr (3*k) - 8 powr (3*k)"
      by simp
    have exp20:"\<dots> < (N - a^3) - b^3"
      using \<open>N - a^3 \<ge> 8*8 powr (3*k)\<close> \<open>b^3 < 8 powr (3*k)\<close> by linarith
    hence "\<dots> < N - a^3"
      using \<open>0 < b ^ 3\<close> \<open>(b ^ 3) < 8 powr (3 * k)\<close> by linarith
    have exp21: "\<dots> < 11*8 powr (3*k)"
      using a_def \<open>(i-1)^3 < i^3\<close> exp16 exp01 exp17 exp18 exp02
      by (smt(verit) of_int_less_iff of_int_of_nat_eq of_nat_diff of_nat_le_of_nat_power_cancel_iff 
          of_nat_power)

    have "[N - a^3 - b^3 = 0] (mod (8^(nat k)))"
      by (smt (verit, del_insts) \<open>2^3 = 8\<close> \<open>[nat (N - a^3) = b'^3] (mod 2^(3*nat k))\<close> b_def
          unique_euclidean_semiring_class.cong_def cong_diff_iff_cong_0_nat diff_is_0_eq' nat_int 
          nle_le power_mod power_mult)
    define q::real where "q = (N - a^3 - b^3)/((8 powr k))"
    have "(N - a^3 - b^3)/(8 powr k) \<ge> 1"
      by (smt (verit, ccfv_SIG) \<open>1 \<le> 3 * nat k\<close> exp20 le_divide_eq_1_pos less_numeral_extra(1) 
          nat_0_less_mult_iff of_int_less_iff order_less_le_trans powr_gt_zero powr_less_cancel_iff 
          zero_less_nat_eq)
    hence "q \<noteq> 0"
      using q_def by auto
    moreover have "(N - a^3 - b^3) \<noteq> 0"
      using exp20 by auto

    moreover have "(8 powr k) \<noteq> 0"
      using power_not_zero by auto
    ultimately have exp22: "q*((8 powr k)) = (N - a^3 - b^3)"
      using q_def by auto

    have exp23: "(8::nat)^(nat k) = 8 powr k"
      using \<open>1 \<le> 3 * nat k\<close> powr_int by auto
    hence "q = \<lfloor>q\<rfloor>"
      using \<open>[N - a^3 - b^3 = 0] (mod (8::nat)^(nat k))\<close> q_def
      by (metis cong_0_iff floor_of_nat of_int_of_nat_eq real_of_nat_div)
    have "7*8 powr (3*k) < q*8 powr (k)"
      using exp19 exp20 exp22
      by presburger
    hence "q > 7*8 powr (3*k)/(8 powr k)"
      by (simp add: divide_less_eq)
    hence "\<dots> > 7*(8 powr (3*k - k))"
      using powr_diff by (metis of_int_diff times_divide_eq_right)
    hence "\<dots> > 7 * 8 powr (2*k)"
      by simp

    have "q*8 powr k < 11*8 powr (3*k)"
      using exp22 exp21 by linarith
    hence "q < 11*8 powr (3*k) / 8 powr k"
      by (simp add: pos_less_divide_eq)
    hence "q < 11*8 powr (3*k - k)"
      using powr_diff by (metis of_int_diff times_divide_eq_right) 
    hence "q < 11*8 powr (2*k)"
      by simp
    have exp24:"(8::nat)^(2*(nat k)) = 8 powr (2*k)"
      using \<open>3 \<le> k\<close> powr_int
      by (metis exp23 of_int_mult of_int_numeral of_nat_power power_even_eq powr_ge_pzero 
          powr_numeral powr_powr powr_powr_swap) 
    hence "6*(8::nat)^(2*(nat k)) = 6*8 powr (2*k)"
      by simp
    have "6*(8 powr (2* k)) < 7*(8 powr (2*k))"
      by simp
    hence "\<lfloor>q\<rfloor> - 6*(8 ^ (2*(nat k))) > 0"
      using \<open>7 * 8 powr (2 * k) < q\<close> \<open>q = \<lfloor>q\<rfloor>\<close>
    proof -
      have  "6 * 8 powr (2*k) < 7 * 8 powr (2*k)"
        by simp
      have "7 * 8 powr (2 * k) < q"
        using \<open>7 * 8 powr (2 * k) < q\<close> by fastforce
      hence "6 * 8 powr (2 * k) < q"
        using \<open>6 * 8 powr (2*k) < 7 * 8 powr (2*k)\<close> by linarith
      thus  ?thesis
        by (metis (no_types) \<open>q = \<lfloor>q\<rfloor>\<close> exp24 of_int_0_less_iff of_int_diff of_int_eq_numeral_power_cancel_iff
            of_int_mult of_int_numeral real_of_nat_eq_numeral_power_cancel_iff diff_gt_0_iff_gt)
    qed
    then obtain r::nat where "r = \<lfloor>q\<rfloor> - 6*(8 ^ (2*(nat k)))"
      by (metis zero_less_imp_eq_int)
    hence "r = q - 6*(8 powr (2*k))"
      by (metis \<open>q = \<lfloor>q\<rfloor>\<close> exp24 of_int_diff of_int_mult of_int_numeral of_int_of_nat_eq 
          real_of_nat_eq_numeral_power_cancel_iff)
    have "(22::nat)^3 < 8^6"
      using power_mono by simp
    have "\<dots> \<le> 8^(nat (k*2))"
      by (smt (verit, best) \<open>k \<ge> 3\<close>  nat_mono nat_numeral numeral_Bit0 numeral_Bit1 
          numeral_eq_one_iff numeral_less_iff power_increasing_iff)
    have "\<dots> = 8 powr (2*k)"
      by (smt (verit, best) \<open>3 \<le> k\<close> numeral_Bit0 numeral_One of_nat_1 of_nat_numeral of_nat_power powr_int)
    have "\<dots> < r"
      using \<open>r = q - 6*(8 powr (2*k))\<close> \<open>q > 7*8 powr (2*k)\<close> by auto
    have "\<dots> < 5*(8 powr (2*k))"
      using \<open>q < 11*8 powr (2*k)\<close> \<open>r = q - 6*(8 powr (2*k))\<close> by auto

    have "r > 22^3"
      using \<open>(22::nat)^3 < 8^6\<close> \<open>8^6 \<le> 8^(nat (k*2))\<close> \<open>real (8^(nat (k*2))) = 8 powr (2*k)\<close> \<open>8 powr (2*k) < r\<close> 
      by linarith
    hence " r \<ge> 10648"
      by simp
    then obtain d m where "d \<ge> 0" and "d \<le> 22" and "r = d^3 + 6*m" and "is_sumpow 2 3 m"
      using values_geq_22_cubed_can_be_normalised by auto

    define A::nat where "A = 8^(nat k)"
    have "m \<le> r/6"
      using \<open>r = d^3 + 6*m\<close> \<open>d \<ge> 0\<close> by linarith 
    have "\<dots> < (5*8^(nat (2*k)))/6"
      by (smt (verit, ccfv_SIG) \<open>3 \<le> k\<close> \<open>r < 5*(8 powr (2*k))\<close> divide_strict_right_mono powr_int)
    have "\<dots> < 8^(nat (2*k))"
      by simp
    have "\<dots> = A\<^sup>2"
      by (metis A_def \<open>real (8^(2*nat k)) = 8 powr (2*k)\<close> \<open>real (8 ^ nat(k*2)) = 8 powr (2*k)\<close> 
          mult.commute power_mult real_of_nat_eq_numeral_power_cancel_iff)

    define c::nat where "c = d*2^(nat k)"
    have "N = a^3 + b^3 + (8^(nat k))*q"
      by (smt (verit, del_insts) \<open>1 \<le> 3 * nat k\<close> \<open>N - a^3 - b^3 \<noteq> 0\<close> exp22
          diff_is_0_eq' mult.commute nat_0_iff nat_0_less_mult_iff nat_int nle_le of_nat_add 
          of_nat_diff powr_int zero_less_nat_eq zero_less_one)
    moreover have "\<dots> = a^3 + b^3 + 8^(nat k)*(6*8 powr (2*k) + r)"
      using \<open>r = q - 6*(8 powr (2*k))\<close> by simp
    moreover have "\<dots> = a^3 + b^3 + 8^(nat k)*(6*8^(nat(2*k)) + r)"
    proof -
      have "8 powr (int 2 * k) = (8 ^ nat (k * int 2))"
        using \<open>real (8 ^ nat (k * 2)) = 8 powr (2 * k)\<close> by auto
      thus ?thesis
        by simp
    qed
    moreover have "\<dots> = a^3 + b^3 + (8^(nat k)*d^3) + 8^(nat k)*(6*8^(nat(2*k)) + 6*m)"
      by (simp add: \<open>r = d^3 + 6*m\<close> add_mult_distrib2)
    moreover have "\<dots> = a^3 + b^3 + ((2^(nat k))*d)^3 + 8^(nat k)*(6*8^(nat(2*k)) + 6*m)"
      by (smt (verit) \<open>2 ^ 3 = 8\<close> mult.commute power_mult power_mult_distrib)
    moreover have "\<dots> = a^3 + b^3 + c^3 + 6*A*(A\<^sup>2 + m)"
      by (smt (z3) A_def c_def exp24 \<open>real (8 ^ nat(k*2)) = 8 powr (2*k)\<close> add_mult_distrib2
          mult.assoc mult.commute of_nat_eq_iff power_even_eq)
    ultimately have "N = a^3 + b^3 + c^3 + 6*A*(A\<^sup>2 + m)"
      using of_nat_eq_iff by metis
    have "is_sumpow 3 6 (6*A*(A\<^sup>2 + m))"
    proof -
      have "m \<le> A\<^sup>2"
        using \<open>8 ^ nat (2*k) = real (A\<^sup>2)\<close> \<open>m \<le> r/6\<close> \<open>real r / 6 < 5*8^nat (2 * k)/6\<close> by linarith
      thus ?thesis
        using sum_of_6_cubes \<open>is_sumpow 2 3 m\<close> by simp
    qed
    then obtain l::"nat list" where "length l = 6" and "6*A*(A\<^sup>2 + m) = sumpow 3 l"
      using is_sumpow_def by blast
    have "a^3 + b^3 + c^3 + sumpow 3 l = sumpow 3 (a#b#c#l)"
      by (simp add: fold_plus_sum_list_rev)
    hence "\<dots> = N"
      using \<open>6 * A * (A\<^sup>2 + m) = sumpow 3 l\<close> \<open>N = a^3 + b^3 + c^3 + 6*A*(A\<^sup>2 + m)\<close> by presburger
    have "length (a#b#c#l) = 9"
      using \<open>length l = 6\<close> by simp
    thus ?thesis
      using \<open>sumpow 3 (a#b#c#l) = N\<close> is_sumpow_def by blast
  next
    case leq8pow10
    consider (leq40000) "N \<le> 40000" | (ge40000) "N > 40000"
      by arith
    thus ?thesis
    proof (cases)
      case ge40000
      define a::int where "a = \<lfloor>(N - 10000) powr (1/3)\<rfloor>"

      text\<open>The following inequalities differ from those in \cite{nathanson1996}, which erroneously result in
the false statement a > 31, we have corrected these mistakes.  This does not affect the rest of the proof.\<close>
      have "(N - 10000) > 30000"
        using ge40000 by linarith
      hence "(N - 10000) powr (1/3) \<ge> (30000) powr (1/3)"
        using powr_mono2 by simp
      hence "a \<ge> \<lfloor>(30000::int) powr (1/3)\<rfloor>"
        using a_def floor_mono by simp
      have "(30000::nat) > (31)^3"
        by simp
      hence "(30000::nat) powr (1/3) > (31^3) powr (1/3)"
        by (metis numeral_less_iff numeral_pow of_nat_numeral powr_less_mono2 zero_le_numeral 
            zero_less_divide_1_iff zero_less_numeral)
      hence "\<dots> > 31"
        by auto
      hence "\<lfloor>(30000::nat) powr (1/3)\<rfloor> \<ge> 31"
        by linarith
      hence "a \<ge> 31"
        using \<open>a \<ge> \<lfloor>(30000::int) powr (1/3)\<rfloor>\<close>
        by (metis nle_le of_int_numeral of_nat_numeral order_trans)
      hence "nat a = a"
        by simp
      have "\<forall>(x::int) > 4. x*(x - 3) > 1"
        by (simp add: less_1_mult)
      hence "\<forall>(x::int) > 4. x^2 - 3*x -1 > 0"
        by (simp add: mult.commute power2_eq_square right_diff_distrib')
      define d::int where "d = (a+1)^3 - a^3"
      moreover have "\<dots> =3*a^2 + 3*a + 1"
        by Groebner_Basis.algebra
      moreover hence "a^2 - 3*a -1 > 0"
        using \<open>a \<ge> 31\<close> \<open>\<forall>(x::int) > 4. x^2 - 3*x -1 > 0\<close> by simp
      moreover hence "4*a^2 > 3*a^2 + 3*a + 1"
        by simp
      ultimately have "4*a^2 > d"
        by presburger
      have "a < (N powr (1/3))"
        by (smt (verit, best) a_def diff_less floor_eq_iff ge40000 of_nat_0_le_iff of_nat_less_iff 
            powr_less_mono2 zero_less_divide_1_iff zero_less_numeral)
      hence "a powr 2 < (N powr (1/3))powr 2"
        using \<open>31 \<le> a\<close> order_less_le by fastforce
      hence "4*a^2 < 4*(N powr (2/3))"
        using a_def powr_powr by fastforce
      have "N - (N - 10000) \<le> 10000"
        by simp
      hence "N - ((N - 10000) powr (1/3)) powr 3 \<le> 10000"
        using powr_powr powr_one_gt_zero_iff ge40000 by force
      hence "N - \<lfloor>(N-10000) powr (1/3) + 1\<rfloor> powr 3 < 10000"
        by (smt (verit, best) powr_ge_pzero powr_less_mono2 real_of_int_floor_add_one_gt)
      hence "N - (a+1) powr 3 < 10000"
        using a_def one_add_floor by simp
      have "(a+1) powr 3 = (a+1)^3"
        using a_def by auto
      hence "N - (a+1)^3 < 10000"
        using \<open>N - (a+1) powr 3 < 10000\<close> by linarith
      have "\<dots> \<le> N - (N - 10000)"
        using ge40000 by auto 
      moreover have "\<dots> = N - ((N - 10000) powr (1/3)) powr 3"
        using powr_powr by simp
      moreover have "\<dots> \<le> N - \<lfloor>((N - 10000) powr (1/3))\<rfloor> powr 3"
        by simp
      moreover have "\<dots> = N - a^3"
        using a_def by simp
      ultimately have "10000 \<le> N - a^3"
        by linarith
      have "\<dots> = N - (a+1)^3 + d"
        using d_def by simp
      moreover have "\<dots> < 10000 + 4*(N powr (2/3))"
        using \<open>N - (a+1)^3 < 10000\<close> \<open>4*a^2 > d\<close> \<open>4*a^2 < 4*(N powr (2/3))\<close> le_less_trans by linarith
      ultimately have "N - a^3 < 10000 + 4*(N powr (2/3))"
        by presburger
      hence "int (N - (nat a)^3) < 10000 + 4*(N powr (2/3))"
        using \<open>nat a = a\<close>
        by (smt (verit, best) \<open>10000 \<le> int N - a^3\<close> int_ops(6) of_int_of_nat_eq of_nat_power)

      consider (N_min_a_cube_leq40000) "N-(nat a)^3 \<le> 40000" | (N_min_a_cube_ge40000) "N - (nat a)^3 > 40000"
        by arith
      thus ?thesis
      proof (cases)
        case N_min_a_cube_leq40000
        have "N - (nat a)^3 \<ge> 10000"
          using \<open>10000 \<le> N - a^3\<close> int_nat_eq \<open>a \<ge> 31\<close>
          by (smt (verit) int_ops(6) numeral_Bit0 numeral_Bit1 numeral_One of_nat_1 of_nat_le_iff 
              of_nat_numeral of_nat_power) 
        hence "is_sumpow 3 6 (N-(nat a)^3)"
          using leq_40000_is_sum_of_9_cubes N_min_a_cube_leq40000 by force

        then obtain l::"nat list" where "length l = 6" and "N - (nat a)^3 = sumpow 3 l"
          using is_sumpow_def by blast
        have "0 + 0 + (nat a)^3 + sumpow 3 l = sumpow 3 ((nat a)#0#0#l)"
          by (simp add: fold_plus_sum_list_rev)
        hence "\<dots> = N"
          using \<open>N - (nat a)^3 = sumpow 3 l\<close> \<open>10000 \<le> N - nat a ^ 3\<close> by presburger 
        have "length ((nat a)#0#0#l) = 9"
          using \<open>length l = 6\<close> by simp
        thus ?thesis
          using \<open>sumpow 3 ((nat a)#0#0#l) = N\<close> is_sumpow_def by blast
      next
        case N_min_a_cube_ge40000
        define N'::nat where "N' = N - (nat a)^3"
        hence "N' > 40000"
          using N_min_a_cube_ge40000 by simp

        define b::int where "b = \<lfloor>(N' - 10000) powr (1/3)\<rfloor>"
        text\<open>The same mistake as above crops up, and we have corrected it in the same way.\<close>
        have "\<dots> \<ge> 31"
          by (smt (verit) \<open>31 \<le> \<lfloor>real 30000 powr (1 / 3)\<rfloor>\<close> \<open>40000 < N'\<close> floor_mono floor_of_nat 
              int_ops(2) int_ops(6) less_imp_of_nat_less numeral_Bit0 numeral_Bit1 numeral_One 
              of_nat_numeral powr_mono2 zero_le_divide_1_iff)
        hence "b \<ge> 31"
          using b_def by simp
        hence "nat b = b"
          by simp

        define d'::int where "d' = (b+1)^3 - b^3"
        moreover have "\<dots> =3*b^2 + 3*b + 1"
          by Groebner_Basis.algebra 
        moreover have "b^2 - 3*b -1 > 0"
          using \<open>b \<ge> 31\<close> \<open>\<forall>(x::int) > 4. x^2 - 3*x -1 > 0\<close> by simp
        moreover hence "4*b^2 > 3*b^2 + 3*b + 1"
          by simp
        ultimately have "4*b^2 > d'"        
          by presburger

        have "b < (N' powr (1/3))"
          using b_def
          by (smt (verit, best) N_min_a_cube_ge40000 N'_def diff_less floor_eq_iff of_nat_0_le_iff
              of_nat_less_iff powr_less_mono2 zero_less_divide_1_iff zero_less_numeral)
        hence "b powr 2 < (N' powr (1/3))powr 2"
          using \<open>31 \<le> b\<close> order_less_le by fastforce
        hence "4*b^2 < 4*(N' powr (2/3))"
          using b_def powr_powr by fastforce
        have "N' - (N' - 10000) \<le> 10000"
          by simp
        hence "N' - ((N' - 10000) powr (1/3)) powr 3 \<le> 10000"
          using powr_powr powr_one_gt_zero_iff \<open>N' > 40000\<close> by force
        hence "N' - \<lfloor>(N'-10000) powr (1/3) + 1\<rfloor> powr 3 < 10000"
          by (smt (verit, best) powr_ge_pzero powr_less_mono2 real_of_int_floor_add_one_gt)
        hence "N' - (b+1) powr 3 < 10000"
          using b_def one_add_floor by simp
        have "(b+1) powr 3 = (b+1)^3"
          using b_def by auto
        hence "N' - (b+1)^3 < 10000"
          using  \<open>N' - (b+1) powr 3 < 10000\<close> by linarith
        have "\<dots> \<le> N' - (N' - 10000)"
          using \<open>N' > 40000\<close> by auto
        moreover have "\<dots> = N' - ( (N' - 10000) powr (1/3)) powr 3"
          using powr_powr by simp
        moreover have "\<dots> \<le> N' - \<lfloor>((N' - 10000) powr (1/3))\<rfloor> powr 3"
          by simp
        moreover have "\<dots> = N' - b^3"
          using b_def by simp
        ultimately have "10000 \<le> N' - b^3"
          by linarith
        have "\<dots> = N' - (b+1)^3 + d'"
          using d'_def by simp
        moreover have "\<dots> < 10000 + 4*(N' powr (2/3))"
          using \<open>N' - (b+1)^3 < 10000\<close> \<open>4*b^2 > d'\<close> \<open>4*b^2 < 4*(N' powr (2/3))\<close> le_less_trans 
          by linarith
        ultimately have "N' - b^3 < 10000 + 4*(N' powr (2/3))"
          by presburger
        hence "int (N' - (nat b)^3) < 10000 + 4*(N' powr (2/3))"
          using \<open>nat b = b\<close>
          by (smt (verit, best) \<open>10000 \<le> int N' - b ^ 3\<close> int_ops(6) of_int_of_nat_eq of_nat_power)

        consider (N'_min_b_cube_leq40000) "N'-(nat b)^3 \<le> 40000" | (N'_min_b_cube_ge40000) "N' - (nat b)^3 > 40000"
          by arith
        thus ?thesis
        proof (cases)
          case N'_min_b_cube_leq40000
          have "N' - (nat b)^3 \<ge> 10000"
            using \<open>10000 \<le> N' - b^3\<close> int_nat_eq \<open>b \<ge> 31\<close>
            by (smt (verit) int_ops(6) numeral_Bit0 numeral_Bit1 numeral_One of_nat_1 of_nat_le_iff 
                of_nat_numeral of_nat_power) 
          hence "N - (nat a)^3 - (nat b)^3 \<ge> 10000"
            using N'_def by simp
          hence "is_sumpow 3 6 (N - (nat a)^3 - (nat b)^3)"
            using leq_40000_is_sum_of_9_cubes N'_min_b_cube_leq40000 N'_def by force
          then obtain l::"nat list" where "length l = 6" and "N - (nat a)^3 - (nat b)^3 = sumpow 3 l"
            using is_sumpow_def by blast
          have "0 + (nat b)^3 + (nat a)^3 + sumpow 3 l = sumpow 3 ((nat a)#(nat b)#0#l)"
            by (simp add: fold_plus_sum_list_rev)
          hence "\<dots> = N"
            using \<open>N - (nat a)^3 - (nat b)^3 = sumpow 3 l\<close> \<open>10000 \<le> N - nat a^3 - nat b^3\<close> 
            by presburger 
          have "length ((nat a)#(nat b)#0#l) = 9"
            using \<open>length l = 6\<close> by simp
          thus ?thesis 
            using \<open>sumpow 3 (nat a # nat b # 0 # l) = N\<close> is_sumpow_def by blast
        next
          case N'_min_b_cube_ge40000

          define N''::nat where "N'' = N - (nat a)^3 - (nat b)^3"
          hence "N'' > 40000"
            using N'_min_b_cube_ge40000 N'_def by simp

          define c::int where "c = \<lfloor>(N'' - 10000) powr (1/3)\<rfloor>"
          text\<open>We correct the same mistake as above.\<close>
          have "\<dots> \<ge> 31"
            by (smt (verit) \<open>31 \<le> \<lfloor>real 30000 powr (1 / 3)\<rfloor>\<close> \<open>40000 < N''\<close> floor_mono floor_of_nat 
                int_ops(2) int_ops(6) less_imp_of_nat_less numeral_Bit0 numeral_Bit1 numeral_One 
                of_nat_numeral powr_mono2 zero_le_divide_1_iff)
          hence "c \<ge> 31"
            using c_def by simp
          hence cnotneg: "nat c = c"
            using int_nat_eq by simp 

          define d''::int where "d'' = (c+1)^3 - c^3"
          moreover have "\<dots> =3*c^2 + 3*c + 1"
            by Groebner_Basis.algebra 
          moreover have "c^2 - 3*c -1 > 0"
            using \<open>c \<ge> 31\<close> \<open>\<forall>(x::int) > 4. x^2 - 3*x -1 > 0\<close> by simp
          moreover hence "4*c^2 > 3*c^2 + 3*c + 1"
            by simp
          ultimately have "4*c^2 > d''"        
            by presburger
      
          have "c < (N'' powr (1/3))"
            using c_def N'_min_b_cube_ge40000 N'_def N''_def
            by (smt (verit, ccfv_SIG) diff_less floor_eq_iff of_nat_0_le_iff of_nat_less_iff 
                powr_less_mono2 zero_less_divide_1_iff zero_less_numeral)
          hence "c powr 2 < (N'' powr (1/3))powr 2"
            using \<open>31 \<le> c\<close> order_less_le by fastforce
          hence "4*c^2 < 4*(N'' powr (2/3))"
            using c_def powr_powr by fastforce

          have "N'' - (N'' - 10000) \<le> 10000"
            by simp
          hence "N'' - ((N'' - 10000) powr (1/3)) powr 3 \<le> 10000"
            using powr_powr powr_one_gt_zero_iff \<open>N' > 40000\<close> by force
          hence "N'' - \<lfloor>(N''-10000) powr (1/3) + 1\<rfloor> powr 3 < 10000"
            by (smt (verit, best) powr_ge_pzero powr_less_mono2 real_of_int_floor_add_one_gt)
          hence "N'' - (c+1) powr 3 < 10000"
            using c_def one_add_floor by simp
          have "(c+1) powr 3 = (c+1)^3"
            using c_def by auto
          hence "N'' - (c+1)^3 < 10000"
            using  \<open>N'' - (c+1) powr 3 < 10000\<close> by linarith
          have "\<dots> \<le> N'' - (N'' - 10000)"
            using \<open>N'' > 40000\<close> by auto
          moreover have "\<dots> = N'' - ( (N'' - 10000) powr (1/3)) powr 3"
            using powr_powr by simp
          moreover have "\<dots> \<le> N'' - \<lfloor>((N'' - 10000) powr (1/3))\<rfloor> powr 3"
            by simp
          moreover have "\<dots> = N'' - c^3"
            using c_def by simp
          ultimately have "10000 \<le> N'' - c^3"
            by linarith
          moreover have "\<dots> = N'' - (c+1)^3 + d''"
            using d''_def by simp
          moreover have "\<dots> < 10000 + 4*(N'' powr (2/3))"
            using \<open>N'' - (c+1)^3 < 10000\<close> \<open>4*c^2 > d''\<close> \<open>4*c^2 < 4*(N'' powr (2/3))\<close> le_less_trans 
            by linarith
          ultimately have "N'' - c^3 < 10000 + 4*(N'' powr (2/3))"
            by presburger
          hence "int (N'' - (nat c)^3) < 10000 + 4*(N'' powr (2/3))"
            using cnotneg
            by (smt (verit, best) \<open>10000 \<le> int N'' - c ^ 3\<close> int_ops(6) of_int_of_nat_eq of_nat_power) 
      
          have "N - (nat a)^3 - (nat b)^3 - (c+1)^3 < 10000"
            using \<open>N'' - (c+1)^3 < 10000\<close> N''_def by simp
          have "\<dots> \<le> N'' - (nat c)^3"
            by (smt (verit, del_insts) \<open>10000 \<le> int N'' - c ^ 3\<close> cnotneg int_ops(6) of_nat_power)
          have "\<dots> < 10000 + 4*((N - (nat a)^3 - (nat b)^3) powr (2/3))"
            using N''_def \<open>int (N'' - (nat c)^3) < 10000 + 4*(N'' powr (2/3))\<close> by simp
          moreover have "\<dots> < 10000 + 4*((10000 + 4*((N - (nat a)^3) powr (2/3))) powr (2/3))" 
            using \<open>int (N' - (nat b)^3) < 10000 + 4*(N' powr (2/3))\<close> powr_less_mono2 N'_def by simp
          moreover have "\<dots> < 10000 + 4*((10000 + 4*((10000 + 4*(N powr (2/3))) powr (2/3))) powr (2/3))"
            using \<open>int (N - (nat a)^3) < 10000 + 4*(N powr (2/3))\<close> powr_less_mono2 by simp
          moreover have "\<dots> \<le> 10000 + 4*((10000 + 4*((10000 + 4*((int 8^10) powr (2/3))) powr (2/3))) powr (2/3))"
            using leq8pow10 powr_less_mono2 nle_le
            by (smt (verit, best) numeral_power_le_of_nat_cancel_iff of_int_of_nat_eq of_nat_0_le_iff 
                of_nat_power powr_ge_pzero zero_less_divide_iff)
          moreover have "\<dots> = 10000 + 4*((10000 + 4*((4204304) powr (2/3))) powr (2/3))"
            using powr_powr by simp
          (*4251528 is the next lowest cube number after 4204304*)
          moreover have "\<dots> \<le> 10000 + 4*((10000 + 4*((4251528) powr (2/3))) powr (2/3))" 
            by (smt (verit, best) powr_ge_pzero powr_less_mono2 zero_less_divide_iff)
          moreover have "\<dots> = 10000 + 4*((114976) powr (2/3))"
            by auto
          (*117649 is the next lowest cube number after 114976*)
          moreover have "\<dots> \<le> 10000 + 4*((117649) powr (2/3))" 
            by (smt (verit, best) powr_ge_pzero powr_less_mono2 zero_less_divide_iff)
          moreover have "\<dots> \<le> 20000"
            by auto
          ultimately have "N - (nat a)^3 - (nat b)^3 - (nat c)^3 \<le> 20000"
            by (smt (verit, del_insts) N''_def numeral_Bit0 numeral_Bit1 numerals(1) of_int_of_nat_eq 
                of_nat_1 of_nat_le_iff of_nat_numeral)

          hence "is_sumpow 3 6 (N - (nat a)^3 - (nat b)^3 - (nat c)^3)"
            using leq_40000_is_sum_of_9_cubes \<open>10000 \<le> N'' - c^3\<close> N''_def cnotneg 
            by (smt (verit) \<open>10000 \<le> int (N'' - nat c ^ 3)\<close> int_ops(2) numeral_Bit0 numeral_Bit1 
                numeral_One of_nat_le_iff of_nat_numeral order_less_le) 
          then obtain l::"nat list" where "length l = 6" and 
            "N - (nat a)^3 - (nat b)^3 - (nat c)^3 = sumpow 3 l"
            using is_sumpow_def by blast
          moreover have "(nat c)^3 + (nat b)^3 + (nat a)^3 + sumpow 3 l = sumpow 3 ((nat a)#(nat b)#(nat c)#l)"
            by (simp add: fold_plus_sum_list_rev)
          ultimately have  "\<dots> = N"
            using \<open>10000 \<le> int N'' - c^3\<close> N''_def cnotneg 
            by (smt (verit, del_insts) diff_diff_left of_nat_power of_nat_le_iff le_add_diff_inverse 
                add.commute int_ops(6))
          moreover have "length ((nat a)#(nat b)#(nat c)#l) = 9"
            using \<open>length l = 6\<close> by simp
          ultimately show ?thesis 
            using is_sumpow_def by blast
        qed
      qed
    next
      case leq40000
      thus ?thesis 
        using leq_40000_is_sum_of_9_cubes by blast
    qed
  qed
  thus ?thesis
    by simp
qed
end


