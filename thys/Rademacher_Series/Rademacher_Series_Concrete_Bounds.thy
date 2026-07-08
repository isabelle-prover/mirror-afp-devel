(*
  File:     Rademacher_Series_Concrete_Bounds.thy
  Author:   Manuel Eberl, University of Innsbruck
*)
theory Rademacher_Series_Concrete_Bounds
  imports Rademacher_Series "HOL-Decision_Procs.Approximation"
begin

text \<open>
  Concretely, for $\varepsilon = \frac{1}{2}$, $c = 2$ works for all $n\geq 13$, 
  $c = 1$ works for all $n\geq 87$, and $c = \frac{1}{2}$ works for all $n\geq 5682$.

  Of course, in practice, one will presumably want to add a bit more leeway to account for
  rounding errors that occur during the evaluation. However, it is probably a good idea to
  keep this leeway as small as possible, since adding a few more bits of precision during the
  evaluation is cheaper than computing more terms of the series.

  Note again that these bounds are far from tight.
\<close>
corollary rademacher_remainder_bound_concrete_onehalf_onehalf:
  assumes "real N \<ge> sqrt n / 2" "n \<ge> 5682"
  shows   "\<bar>rademacher_remainder n N\<bar> < 1 / 2"
proof (rule rademacher_remainder_bound_concrete_strong')
  show "real N \<ge> (1/2) * sqrt (real n)"
    using assms by simp
next
  define y where "y = 5682 powr (-1/4::real)"
  show "y * (rademacher_bound_const1 * (1/2) powr (-1/2) + 
          rademacher_bound_const3 (1/2) * (1/2) powr (-5/2) * ((1/2) + y\<^sup>2)\<^sup>2) < 1 / 2"
    unfolding rademacher_bound_const1_def rademacher_bound_const3_def y_def
              rademacher_aux5_def sinh_def cosh_def real_scaleR_def
    by (approximation 30)
  show "1 / y ^ 4 \<le> real n"
    using assms by (simp add: powr_power y_def)
qed auto

corollary rademacher_remainder_bound_concrete_onehalf_1:
  assumes "real N \<ge> sqrt n" "n \<ge> 87"
  shows   "\<bar>rademacher_remainder n N\<bar> < 1 / 2"
proof (rule rademacher_remainder_bound_concrete_strong')
  show "real N \<ge> 1 * sqrt (real n)"
    using assms by simp
next
  define y where "y = 87 powr (-1/4::real)"
  show "y * (rademacher_bound_const1 * 1 powr (-1/2) + 
           rademacher_bound_const3 1 * 1 powr (-5/2) * (1 + y\<^sup>2)\<^sup>2) < 1 / 2"
    unfolding rademacher_bound_const1_def rademacher_bound_const3_def y_def
              rademacher_aux5_def sinh_def cosh_def real_scaleR_def
        by (approximation 30)
  show "1 / y ^ 4 \<le> real n"
    using assms by (simp add: powr_power y_def)
qed auto

corollary rademacher_remainder_bound_concrete_onehalf_2:
  assumes "real N \<ge> 2 * sqrt n" "n \<ge> 13"
  shows   "\<bar>rademacher_remainder n N\<bar> < 1 / 2"
proof (rule rademacher_remainder_bound_concrete_strong')
  show "real N \<ge> 2 * sqrt (real n)"
    using assms by simp
next
  define y where "y = 13 powr (-1/4::real)"
  show "y * (rademacher_bound_const1 * 2 powr (-1/2) + 
          rademacher_bound_const3 2 * 2 powr (-5/2) * (2 + y\<^sup>2)\<^sup>2) < 1 / 2"
    unfolding rademacher_bound_const1_def rademacher_bound_const3_def y_def
              rademacher_aux5_def sinh_def cosh_def real_scaleR_def
    by (approximation 30)
  show "1 / y ^ 4 \<le> real n"
    using assms by (simp add: powr_power y_def)
qed auto

end