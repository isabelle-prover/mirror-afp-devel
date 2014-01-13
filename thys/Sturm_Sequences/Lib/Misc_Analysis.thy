(* Author: Manuel Eberl <eberlm@in.tum.de> *)
theory Misc_Analysis
imports Limits
begin

subsection {* Analysis *}

(* This could fit into Real.thy *)

lemma real_infinite_interval:
  assumes "a < (b::real)"
  shows "\<not>finite {a<..<b}"
proof
  assume "finite {a<..<b}"
  {
    fix S assume fin: "finite (S::real set)" and "\<exists>l u. l < u \<and> S = {l<..<u}"
    from this(2) have "\<not>finite S"
    proof (induction rule: finite_psubset_induct[OF fin])
      case (goal1 S)
        then obtain l u where "l < u" and [simp]: "S = {l<..<u}" by blast
        def S' \<equiv> "{l<..<l + (u-l)/3}"
        have "(l+u)/2 \<in> S" "(l+u)/2 \<notin> S'" unfolding S'_def using `l < u`
            by (simp_all add: field_simps)
        hence "S \<noteq> S'" by blast
        hence "S' \<subset> S" unfolding S'_def by (auto simp: field_simps)
        moreover have "\<exists>l' u'. l' < u' \<and> S' = {l'<..<u'}" using `l < u`
            by (rule_tac exI[of _ l], rule_tac exI[of _ "l+(u-l)/3"], 
                simp add: S'_def)
        ultimately have "\<not>finite S'" by (intro goal1(2), simp_all)
        thus ?case using `S' \<subset> S` using finite_subset by blast
    qed
  }
  from this[OF `finite {a<..<b}`] have "\<not> finite {a<..<b}" using assms by blast
  thus False using `finite {a<..<b}` by contradiction
qed

lemma real_interval_card_eq:
  "card {a<..<b::real} = 0"
  "card {a<..b::real} = 0"
  "card {a..<b::real} = 0"
  "card {a..b::real} = (if a = b then 1 else 0)"
proof-
  show "card {a<..<b} = 0"
      by (cases "a < b", simp_all add: real_infinite_interval)
  have "{a<..<b} \<subseteq> {a<..b}" by auto
  from finite_subset[OF this] show "card {a<..b::real} = 0"
      by (cases "a < b", auto simp: real_infinite_interval card_eq_0_iff) 
  have "{a<..<b} \<subseteq> {a..<b}" by auto
  from finite_subset[OF this] show "card {a..<b::real} = 0"
      by (cases "a < b", auto simp: real_infinite_interval card_eq_0_iff) 
  have "{a<..<b} \<subseteq> {a..b}" by auto
  from finite_subset[OF this] 
      show "card {a..b::real} = (if a = b then 1 else 0)"
      by (cases "a < b", auto simp: real_infinite_interval card_eq_0_iff)
qed



(* This might fit into Limits.thy *)

lemma x_pow_n_limit_at_top[intro]:
  assumes "n \<ge> 1"
  shows "LIM (x::real) at_top. x^n :> at_top"
proof (simp only: filterlim_at_top eventually_at_top_linorder, clarify)
  fix b :: real
  let ?x\<^sub>0 = "max b 1"
  show "\<exists>x\<^sub>0. \<forall>x\<ge>x\<^sub>0. x ^ n \<ge> b"
  proof (rule exI[of _ ?x\<^sub>0], clarify)
    fix x assume "x \<ge> max b 1"
    have "b \<le> ?x\<^sub>0" by simp
    also from power_increasing[OF assms, of ?x\<^sub>0] 
        have "... \<le> ?x\<^sub>0 ^ n" by simp
    also from power_mono[OF `x \<ge> ?x\<^sub>0`] have "... \<le> x ^ n" by simp
    finally show "b \<le> x ^ n" .
  qed
qed

lemma filterlim_pow_at_top:
  assumes "LIM (x::real) F. f x :> at_top" "n \<ge> 1"
  shows "LIM (x::real) F. (f x)^n :: real :> at_top"
proof-
  from assms
      have "filtermap f F \<le> at_top" 
      by (simp add: filterlim_def)
  from filtermap_mono[OF this, of "\<lambda>x. x^n"] 
      have "filtermap (\<lambda>x. (f x)^n) F \<le> filtermap (\<lambda>x. x^n) at_top"
      by (simp add: filtermap_filtermap)
  also from x_pow_n_limit_at_top[OF `n \<ge> 1`]
      have "... \<le> at_top" by (simp add: filterlim_def)
  finally show ?thesis by (simp add: filterlim_def)
qed


lemma x_pow_n_limit_at_bot[intro]: 
  assumes "n \<ge> 1"
  shows "even n \<Longrightarrow> LIM (x::real) at_bot. x^n :> at_top"
    and "odd n \<Longrightarrow> LIM (x::real) at_bot. x^n :> at_bot"
proof-
  assume "even n"
  show "LIM (x::real) at_bot. x^n :> at_top"
  proof (subst filterlim_cong, rule refl, rule refl)
    from `even n` show "eventually (\<lambda>x::real. x^n = (-x)^n) at_bot" 
        by (simp add: neg_power_if)
    show "LIM (x::real) at_bot. (-x)^n :> at_top" using assms
        by (simp add: filterlim_at_bot_mirror x_pow_n_limit_at_top)
  qed
next
  assume "odd n"
  show "LIM (x::real) at_bot. x^n :> at_bot"
  proof (subst filterlim_cong, rule refl, rule refl)
    from `odd n` show "eventually (\<lambda>x::real. x^n = -((-x)^n)) at_bot" 
        by (simp add: neg_power_if)
    show "LIM (x::real) at_bot. -((-x)^n) :> at_bot" using assms
        by (simp add: filterlim_at_bot_mirror filterlim_uminus_at_bot 
                      x_pow_n_limit_at_top)
  qed
qed

lemma filterlim_pow:
  assumes "LIM (x::real) F. f x :> at_top" "n \<ge> 1"
  shows "LIM (x::real) F. (f x)^n :: real :> at_top"
proof-
  from assms
      have "filtermap f F \<le> at_top" 
      by (simp add: filterlim_def)
  from filtermap_mono[OF this, of "\<lambda>x. x^n"] 
      have "filtermap (\<lambda>x. (f x)^n) F \<le> filtermap (\<lambda>x. x^n) at_top"
      by (simp add: filtermap_filtermap)
  also from x_pow_n_limit_at_top[OF `n \<ge> 1`]
      have "... \<le> at_top" by (simp add: filterlim_def)
  finally show ?thesis by (simp add: filterlim_def)
qed


lemma filterlim_pow_at_bot:
  fixes f :: "real \<Rightarrow> real" assumes "n \<ge> 1"
  shows "even n \<Longrightarrow> LIM x F. f x :> at_bot \<Longrightarrow> 
                    LIM x F. (f x)^n :> at_top"
    and "odd n \<Longrightarrow> LIM x F. f x :> at_bot
               \<Longrightarrow> LIM x F. (f x)^n :> at_bot"
proof-
  assume "even n" "LIM x F. f x :> at_bot"
  hence "filtermap f F \<le> at_bot" by (simp add: filterlim_def)
  from filtermap_mono[OF this, of "\<lambda>x. x^n"] 
      have "filtermap (\<lambda>x. (f x)^n) F \<le> filtermap (\<lambda>x. x^n) at_bot"
      by (simp add: filtermap_filtermap)
  also from x_pow_n_limit_at_bot(1)[OF `n \<ge> 1` `even n`]
      have "... \<le> at_top" by (simp add: filterlim_def)
  finally show "LIM x F. (f x)^n :> at_top" by (simp add: filterlim_def)
next
  assume "odd n" "LIM x F. f x :> at_bot"
  hence "filtermap f F \<le> at_bot" by (simp add: filterlim_def)
  from filtermap_mono[OF this, of "\<lambda>x. x^n"] 
      have "filtermap (\<lambda>x. (f x)^n) F \<le> filtermap (\<lambda>x. x^n) at_bot"
      by (simp add: filtermap_filtermap)
  also from x_pow_n_limit_at_bot(2)[OF `n \<ge> 1` `odd n`]
      have "... \<le> at_bot" by (simp add: filterlim_def)
  finally show "LIM x F. (f x)^n :> at_bot" by (simp add: filterlim_def)
qed



(* This may be too specific to be of general interest *)


lemma real_nat_one_half[dest]:
  "(n::nat) = (m::nat) - 1/2 \<Longrightarrow> False"
  "(n::nat) = (m::nat) + 1/2 \<Longrightarrow> False"
proof-
  assume "(n::nat) = (m::nat) - 1/2" 
  hence "2*(n - m) = 1" by linarith 
  thus False by simp
next
  assume "(n::nat) = (m::nat) + 1/2" 
  hence "2*(n - m) = 1" by linarith 
  thus False by simp
qed

lemma natfun_eq_in_ivl:
  assumes "a \<le> b"
  assumes "\<forall>x::real. a \<le> x \<and> x \<le> b \<longrightarrow> eventually (\<lambda>\<xi>. f \<xi> = (f x::nat)) (at x)"
  shows "f a = f b"
proof-
  have cont: "\<forall>x. a \<le> x \<and> x \<le> b \<longrightarrow> isCont f x"
  proof (clarify, simp add: isCont_def, rule tendstoI, simp add: dist_real_def)
    fix \<epsilon> :: real and x :: real assume "\<epsilon> > 0" and  "a \<le> x" "x \<le> b"
    with assms have A: "eventually (\<lambda>\<xi>. f \<xi> = (f x::nat)) (at x)" by simp
    show "eventually (\<lambda>\<xi>. \<bar>real (f \<xi>) - real (f x)\<bar> < \<epsilon>) (at x)"
        by (rule eventually_mono[OF _ A], simp add: `\<epsilon> > 0`)
  qed

  {
    def y \<equiv> "f a + 1/2"
    assume "f a < f b"
    hence "f a \<le> y" "y \<le> f b" by (simp_all add: y_def)
    with IVT[OF this `a \<le> b` cont] have False by (auto simp: y_def)
  }
  moreover
  {
    def y \<equiv> "f a - 1/2"
    assume "f a > f b"
    hence "f b \<le> y" "y \<le> f a" by (simp_all add: y_def)
    with IVT2[OF this `a \<le> b` cont] have False by (auto simp: y_def)
  }
  ultimately show "f a = f b" by force
qed


end
