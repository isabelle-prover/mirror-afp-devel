section \<open>Additional results about Bijections and Digit Representations\<close>

theory Finite_Fields_More_Bijections
  imports "HOL-Library.FuncSet" Digit_Expansions.Bits_Digits
begin

lemma nth_digit_0:
  assumes "x < b^k"
  shows "nth_digit x k b = 0"
  using assms unfolding nth_digit_def by auto

lemma nth_digit_bounded':
  assumes "b > 0"
  shows "nth_digit v x b < b"
  using assms by (simp add: nth_digit_def)

lemma digit_gen_sum_repr':
  assumes "n < b^c"
  shows "n = (\<Sum>k<c. nth_digit n k b * b ^ k)"
proof -
  consider (a) "b = 0" "c = 0" | (b) "b = 0" "c > 0" | (c) "b = 1" | (d) "b>1" by linarith
  thus ?thesis
  proof (cases)
    case a thus ?thesis using assms by simp
  next
    case b thus ?thesis using assms by (simp add: zero_power)
  next
    case c thus ?thesis using assms by (simp add:nth_digit_def)
  next
    case d thus ?thesis by (intro digit_gen_sum_repr assms d)
  qed
qed

lemma
  assumes "\<And>x. x \<in> A \<Longrightarrow> f (g x) = x"
  shows "\<And>y. y \<in> g ` A \<Longrightarrow> g (f y) = y"
proof -
  show "g (f y) = y" if 0:"y\<in> g`A" for y
  proof -
    obtain x where x_dom: "x \<in> A" and y_def: "y = g x"  using 0 by auto
    hence "g (f y) = g (f (g x))" by simp
    also have "... = g x" by (intro arg_cong[where f="g"] assms(1) x_dom)
    also have "... = y" unfolding y_def by simp
    finally show ?thesis by simp
  qed
qed

lemma nth_digit_bij:
  "bij_betw (\<lambda>v. (\<lambda>x\<in>{..<n}. nth_digit v x b)) {..<b^n} ({..<n} \<rightarrow>\<^sub>E {..<b})"
  (is "bij_betw ?f ?A ?B")
proof -
  have inj_f: "inj_on ?f ?A"
    using digit_gen_sum_repr' by (intro inj_on_inverseI[where g="(\<lambda>x. (\<Sum>k<n. x k * b^k))"]) auto

  consider (a) "b = 0" "n= 0" | (b) "b = 0" "n>0" | (c) "b > 0" by linarith
  hence "nth_digit x i b \<in> {..<b}" if "i < n" "x < b^n" for i x
  proof (cases)
    case a then show ?thesis using that by auto
  next
    case b thus ?thesis using that by (simp add:zero_power)
  next
    case c thus ?thesis using that by (simp add:nth_digit_def)
  qed
  hence "?f x \<in> ?B" if "x \<in> ?A" for x using that unfolding restrict_PiE_iff by auto
  hence "?f ` ?A = ?B"
    using card_image[OF inj_f] by (intro card_seteq finite_PiE image_subsetI) (auto simp:card_PiE)
  thus ?thesis using inj_f unfolding bij_betw_def by auto
qed

lemma nth_digit_sum:
  assumes "\<And>i. i < l \<Longrightarrow> f i < b"
  shows "\<And>k. k < l \<Longrightarrow> nth_digit (\<Sum>i< l. f i * b^i) k b = f k"
    and "(\<Sum>i<l. f i * b^i) < b^l"
proof -
  define n where "n = (\<Sum>i< l. f i * b^i)"

  have "restrict f {..<l} \<in> {..<l} \<rightarrow>\<^sub>E {..<b}" using assms(1) by auto
  then obtain m where a:"(\<lambda>x\<in>{..<l}. nth_digit m x b) = restrict f {..<l}" and b:"m \<in> {..<b^l}"
    using bij_betw_imp_surj_on[OF nth_digit_bij[where n="l" and b="b"]]
    by (metis (no_types, lifting) image_iff)

  have "m = (\<Sum>i< l. nth_digit m i b * b^i)"
    using b by (intro digit_gen_sum_repr') auto
  also have "... = (\<Sum>i< l. f i * b^i)"
    using a by (intro sum.cong arg_cong2[where f="(*)"] refl) (metis restrict_apply')
  also have "... = n" unfolding n_def by simp
  finally have c:"n = m"  by simp
  show "(\<Sum>i<l. f i * b^i) < b^l" unfolding n_def[symmetric] c using b by auto
  show "nth_digit (\<Sum>i< l. f i * b^i) k b = f k" if "k < l" for k
  proof -
    have "nth_digit (\<Sum>i< l. f i * b^i) k b = nth_digit m k b" unfolding n_def[symmetric] c by simp
    also have "... = f k" using a that by (metis lessThan_iff restrict_apply')
    finally show ?thesis by simp
  qed
qed

lemma bij_betw_reindex:
  assumes "bij_betw f I J"
  shows "bij_betw (\<lambda>x. \<lambda>i\<in>I. x (f i)) (J \<rightarrow>\<^sub>E S) (I \<rightarrow>\<^sub>E S)"
proof (rule bij_betwI[where g="(\<lambda>x. \<lambda>i\<in>J. x (the_inv_into I f i))"])
  have 0:"bij_betw (the_inv_into I f) J I"
    using assms bij_betw_the_inv_into by auto

  show "(\<lambda>x. \<lambda>i\<in>I. x (f i)) \<in> (J \<rightarrow>\<^sub>E S) \<rightarrow> I \<rightarrow>\<^sub>E S"
    using bij_betw_apply[OF assms] by auto
  show "(\<lambda>x. \<lambda>i\<in>J. x (the_inv_into I f i)) \<in> (I \<rightarrow>\<^sub>E S) \<rightarrow> J \<rightarrow>\<^sub>E S"
    using bij_betw_apply[OF 0] by auto
  show "(\<lambda>j\<in>J. (\<lambda>i\<in>I. x (f i)) (the_inv_into I f j)) = x" if "x \<in> J \<rightarrow>\<^sub>E S" for x
  proof -
    have "(\<lambda>i\<in>I. x (f i)) (the_inv_into I f j) = x j" if "j \<in> J" for j
      using 0 assms f_the_inv_into_f_bij_betw bij_betw_apply that by fastforce
    thus ?thesis using PiE_arb[OF that] by auto
  qed
  show " (\<lambda>i\<in>I. (\<lambda>j\<in>J. y (the_inv_into I f j)) (f i)) = y" if "y \<in> I \<rightarrow>\<^sub>E S" for y
  proof -
    have "(\<lambda>j\<in>J. y (the_inv_into I f j)) (f i) = y i" if "i \<in> I" for i
      using assms 0 that the_inv_into_f_f[OF bij_betw_imp_inj_on[OF assms]] bij_betw_apply by force
    thus ?thesis using PiE_arb[OF that] by auto
  qed
qed

lemma lift_bij_betw:
  assumes "bij_betw f S T"
  shows "bij_betw (\<lambda>x. \<lambda>i\<in>I. f (x i)) (I \<rightarrow>\<^sub>E S) (I \<rightarrow>\<^sub>E T)"
proof -
  let ?g = "the_inv_into S f"

  have bij_g: "bij_betw ?g T S" using bij_betw_the_inv_into[OF assms] by simp
  have 0:"?g(f x)=x" if "x \<in> S" for x by (intro the_inv_into_f_f that bij_betw_imp_inj_on[OF assms])
  have 1:"f(?g x)=x" if "x \<in> T" for x by (intro f_the_inv_into_f_bij_betw[OF assms] that)

  have "(\<lambda>i\<in>I. f (x i)) \<in> I \<rightarrow>\<^sub>E T" if "x \<in> (I \<rightarrow>\<^sub>E S)" for x
    using bij_betw_apply[OF assms] that by (auto simp: Pi_def)
  moreover have "(\<lambda>i\<in>I. ?g (x i)) \<in> I \<rightarrow>\<^sub>E S" if "x \<in> (I \<rightarrow>\<^sub>E T)" for x
    using bij_betw_apply[OF bij_g] that by (auto simp: Pi_def)
  moreover have "(\<lambda>i\<in>I. ?g ((\<lambda>i\<in>I. f (x i)) i)) = x" if "x \<in> (I \<rightarrow>\<^sub>E S)" for x
  proof -
    have "(\<lambda>i\<in>I. ?g ((\<lambda>i\<in>I. f (x i)) i)) i = x i" for i
      using PiE_mem[OF that] using PiE_arb[OF that]  by (cases "i \<in> I")  (simp add:0)+
    thus ?thesis by auto
  qed
  moreover have "(\<lambda>i\<in>I. f ((\<lambda>i\<in>I. ?g (x i)) i)) = x" if "x \<in> (I \<rightarrow>\<^sub>E T)" for x
  proof -
    have "(\<lambda>i\<in>I. f ((\<lambda>i\<in>I. ?g (x i)) i)) i = x i" for i
      using PiE_mem[OF that] using PiE_arb[OF that]  by (cases "i \<in> I")  (simp add:1)+
    thus ?thesis by auto
  qed
  ultimately show ?thesis
    by (intro bij_betwI[where g="(\<lambda>x. \<lambda>i\<in>I. ?g (x i))"]) simp_all
qed

lemma lists_bij:
    "bij_betw (\<lambda>x. map x [ 0..<d] ) ({..<d} \<rightarrow>\<^sub>E S) {x. set x \<subseteq> S \<and> length x = d}"
proof (intro bij_betwI[where g="(\<lambda>x. \<lambda>i\<in>{..<d}. x ! i)"] funcsetI CollectI, goal_cases)
  case (1 x)
  hence " x ` {0..<d} \<subseteq> S" by (intro image_subsetI) auto
  thus ?case by simp
next
  case (2 x) thus ?case by auto
next
  case (3 x)
  have "restrict ((!) (map x [ 0..<d] )) {..<d} j = x j" for j
    using PiE_arb[OF 3] by (cases "j \<in> {..<d}") auto
  thus ?case by auto
next
  case (4 y)
  have "map (restrict ((!) y) {..<d}) [ 0..<d ] = map (((!) y)) [ 0..<d]" by (intro map_cong) auto
  also have "... = y" using 4 map_nth by blast
  finally show ?case by auto
qed

lemma bij_betw_prod: "bij_betw (\<lambda>x. (x mod s, x div s)) {..<s * t} ({..<(s::nat)} \<times> {..<t})"
proof -
  have bij_betw_aux: "x + s * y < s * t" if "x < s" "y < t" for x y :: nat
  proof -
    have "x + s * y < s + s * y" using that by simp
    also have "... = s * (y+1)" by simp
    also have "... \<le> s * t" using that by (intro mult_left_mono) auto
    finally show ?thesis by simp
  qed

  show ?thesis
  proof (cases "s > 0 \<and> t > 0")
    case True
    then show ?thesis using less_mult_imp_div_less bij_betw_aux
      by (intro bij_betwI[where g="(\<lambda>x. fst x + s * snd x)"]) (auto simp:mult.commute)
  next
    case False then show ?thesis by (auto simp:bij_betw_def)
  qed
qed

end