section \<open>Introduction\<close>

text\<open>Poincar\'e disc is a model of hyperbolic geometry. That fact has been
a mathematical folklore for more than 100 years. However, up to the
best of our knowledge, fully precise, formal proofs of this fact are
lacking. In this paper we present a formalization of the Poincar\'e disc model
in Isabelle/HOL, introduce its basic notions (h-points, h-lines,
h-congruence, h-isometries, h-betweenness) and prove that it models
Tarski's axioms except for Euclid's axiom. We shown that is satisfies
the negation of Euclid's axiom, and, moreover, the existence of
limiting parallels axiom. The model is defined within the extended
complex plane, which has been described quite precisely by
Schwerdfeger~\<^cite>\<open>"schwerdtfeger"\<close> and formalized in the previous work
of the first two authors~\<^cite>\<open>"amai-complexplane"\<close>.\<close> 

paragraph \<open>Related work.\<close>

text\<open>In 1840 Lobachevsky~\<^cite>\<open>"lobachevsky1840geometrische"\<close> published developments
about non-Euclidean geometry. Hyperbolic
geometry is studied through many of its models. The concept of a
projective disc model was introduced by Klein while Poincar\'e
investigated the half-plane model proposed by Liouville and Beltrami
and primarily studied the isometries of the hyperbolic plane that
preserve orientation. In this paper, we focus on the formalization of
the latter.

Regarding non-Euclidean geometry, Makarios showed the
independence of Euclid's axiom~\<^cite>\<open>"makarios"\<close>. He did so by
formalizing that the Klein--Beltrami model is a model of Tarski's
axioms at the exception of Euclid's axiom. Latter Coghetto formalized 
the Klein-Beltrami model within Mizar~\<^cite>\<open>"coghetto2018klein1" and "coghetto2018klein2"\<close>.
\<close>

section \<open>Background theories\<close>

subsection\<open>Hyperbolic Functions\<close>

text \<open>In this section hyperbolic cosine and hyperbolic sine functions are introduced and some of their
properties needed for further development are proved.\<close>

theory Hyperbolic_Functions
  imports Complex_Main Complex_Geometry.More_Complex
begin

lemma arcosh_eq_iff:
  fixes x y::real
  assumes "x \<ge> 1" "y \<ge> 1"
  shows "arcosh x = arcosh y \<longleftrightarrow> x = y"
  by (smt (verit, best) arcosh_less_iff_real arcosh_real_strict_mono assms)


lemma cosh_gt_1 [simp]:
  fixes x ::real
  assumes "x > 0"
  shows "cosh x > 1"
  using assms cosh_real_strict_mono by force


lemma cosh_eq_iff:
  fixes x y::real
  assumes "x \<ge> 0" "y \<ge> 0"
  shows "cosh x = cosh y \<longleftrightarrow> x = y"
  by (simp add: assms)


lemma arcosh_mono:
  fixes x y::real
  assumes "x \<ge> 1" "y \<ge> 1"
  shows "arcosh x \<ge> arcosh y \<longleftrightarrow> x \<ge> y"
  using arcosh_less_iff_real assms linorder_not_le by blast

lemma arcosh_add:
  fixes x y::real
  assumes "x \<ge> 1" "y \<ge> 1"
  shows "arcosh x + arcosh y = arcosh (x*y + sqrt((x\<^sup>2 - 1)*(y\<^sup>2 - 1)))"
proof-
  have "sqrt ((x\<^sup>2 - 1) * (y\<^sup>2 - 1)) \<ge> 0"
    using assms
    by simp
  moreover
  have "x * y \<ge> 1"
    using assms
    by (smt mult_le_cancel_left1)
  ultimately
  have **: "x * y + sqrt ((x\<^sup>2 - 1) * (y\<^sup>2 - 1)) \<ge> 1"
    by linarith
  hence 1: "0 \<le> (x * y + sqrt ((x\<^sup>2 - 1) * (y\<^sup>2 - 1)))\<^sup>2 - 1"
      by simp

  have 2: "x * sqrt (y\<^sup>2 - 1) + y * sqrt (x\<^sup>2 - 1) \<ge> 0"
    using assms
    by simp

  have "(x*sqrt(y\<^sup>2 - 1)+y*sqrt(x\<^sup>2 -1))\<^sup>2 = (sqrt((x*y+sqrt((x\<^sup>2-1)*(y\<^sup>2-1)))\<^sup>2 - 1))\<^sup>2"
    using assms
  proof (subst real_sqrt_pow2)
    show "0 \<le> (x * y + sqrt ((x\<^sup>2 - 1) * (y\<^sup>2 - 1)))\<^sup>2 - 1"
      by fact
  next
    have "(x * sqrt (y\<^sup>2 - 1))\<^sup>2 = x\<^sup>2 * (y\<^sup>2 - 1)"
      by (simp add: \<open>y \<ge> 1\<close> power_mult_distrib)
    moreover
    have "(y * sqrt (x\<^sup>2 - 1))\<^sup>2 = y\<^sup>2 * (x\<^sup>2 - 1)"
      using assms by (simp add: power_mult_distrib)
    ultimately show "(x * sqrt (y\<^sup>2 - 1) + y * sqrt (x\<^sup>2 - 1))\<^sup>2 = (x * y + sqrt ((x\<^sup>2 - 1) * (y\<^sup>2 - 1)))\<^sup>2 - 1"
      using assms
      unfolding power2_sum
      apply (simp add: real_sqrt_mult power_mult_distrib)
      apply (simp add: field_simps)
      done
  qed
  hence "sqrt ((x * y + sqrt ((x\<^sup>2 - 1) * (y\<^sup>2 - 1)))\<^sup>2 - 1) = x * sqrt (y\<^sup>2 - 1) + y * sqrt (x\<^sup>2 - 1)"
    using power2_eq_iff_nonneg[OF 2 real_sqrt_ge_zero[OF 1]]
    by simp
  thus ?thesis
    using assms **
    apply (simp add: arcosh_real_def)
    apply (subst ln_mult_pos[symmetric])
     apply (smt one_le_power real_sqrt_ge_zero)
    apply (smt (verit) one_le_power real_sqrt_ge_zero)
    by (smt (verit) distrib_right mult.commute real_sqrt_mult)
qed

lemma arcosh_double:
  fixes x :: real
  assumes "x \<ge> 1"
  shows "2 * arcosh x = arcosh (2*x\<^sup>2 - 1)"
  by (smt arcosh_add arcosh_mono assms one_power2 power2_eq_square real_sqrt_abs)

end
