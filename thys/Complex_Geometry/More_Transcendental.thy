(* ---------------------------------------------------------------------------- *)
section \<open>Introduction\<close>
(* ---------------------------------------------------------------------------- *)

text \<open>The complex plane or some of its parts (e.g., the unit disc or the upper half plane) are often
taken as the domain in which models of various geometries (both Euclidean and non-Euclidean ones)
are formalized. The complex plane gives simpler and more compact formulas than the Cartesian plane.
Within complex plane is easier to describe geometric objects and perform the calculations (usually
shedding some new light on the subject). We give a formalization of the extended complex
plane (given both as a complex projective space and as the Riemann sphere), its objects (points,
circles and lines), and its transformations (Möbius transformations).\<close>

(* ---------------------------------------------------------------------------- *)
section \<open>Related work\<close>
(* ---------------------------------------------------------------------------- *)

text\<open>During the last decade, there have been many results in formalizing
geometry in proof-assistants. Parts of Hilbert's seminal book
,,Foundations of Geometry'' \<^cite>\<open>"hilbert"\<close> have been formalized both
in Coq and Isabelle/Isar.  Formalization of first two groups of axioms
in Coq, in an intuitionistic setting was done by Dehlinger et
al. \<^cite>\<open>"hilbert-coq"\<close>. First formalization in Isabelle/HOL was done
by Fleuriot and Meikele \<^cite>\<open>"hilbert-isabelle"\<close>, and some further
developments were made in master thesis of Scott \<^cite>\<open>"hilbert-scott"\<close>.
Large fragments of Tarski's geometry \<^cite>\<open>"tarski"\<close> have been
formalized in Coq by Narboux et al. \<^cite>\<open>"narboux-tarski"\<close>. Within Coq,
there are also formalizations of von Plato's constructive geometry by
Kahn \<^cite>\<open>"vonPlato" and "von-plato-formalization"\<close>, French high school
geometry by Guilhot \<^cite>\<open>"guilhot"\<close> and ruler and compass geometry by
Duprat \<^cite>\<open>"duprat2008"\<close>, etc.

In our previous work \<^cite>\<open>"petrovic2012formalizing"\<close>, we have already
formally investigated a Cartesian model of Euclidean geometry. 
\<close>

(* ---------------------------------------------------------------------------- *)
section \<open>Background theories\<close> 
(* ---------------------------------------------------------------------------- *)

text \<open>In this section we introduce some basic mathematical notions and prove some lemmas needed in the rest of our
formalization. We describe:

    \<^item> trigonometric functions,

    \<^item> complex numbers, 

    \<^item> systems of two and three linear equations with two unknowns (over arbitrary fields), 

    \<^item> quadratic equations (over real and complex numbers), systems of quadratic and real
      equations, and systems of two quadratic equations,

    \<^item> two-dimensional vectors and matrices over complex numbers.
\<close>

(* -------------------------------------------------------------------------- *)
subsection \<open>Library Additions for Trigonometric Functions\<close>
(* -------------------------------------------------------------------------- *)

theory More_Transcendental
  imports Complex_Main "HOL-Library.Periodic_Fun"
begin

text \<open>Additional properties of @{term sin} and @{term cos} functions that are later used in proving
conjectures for argument of complex number.\<close>

text \<open>Sign of trigonometric functions on some characteristic intervals.\<close>

lemma cos_lt_zero_on_pi2_pi [simp]:
  assumes "x > pi/2" and "x \<le> pi"
  shows "cos x < 0"
  using cos_gt_zero_pi[of "pi - x"] assms
  by simp

text \<open>Value of trigonometric functions in points $k\pi$ and $\frac{\pi}{2} + k\pi$.\<close>

lemma sin_kpi [simp]:
  fixes k::int
  shows "sin (k * pi) = 0"
  by (simp add: sin_zero_iff_int2)

lemma cos_odd_kpi [simp]:
  fixes k::int
  assumes "odd k"
  shows "cos (k * pi) = -1"
  by (simp add: assms mult.commute)

lemma cos_even_kpi [simp]:
  fixes k::int
  assumes "even k"
  shows "cos (k * pi) = 1"
  by (simp add: assms mult.commute)

lemma sin_pi2_plus_odd_kpi [simp]:
  fixes k::int
  assumes "odd k"
  shows "sin (pi / 2 + k * pi) = -1"
  using assms
  by (simp add: sin_add)

lemma sin_pi2_plus_even_kpi [simp]:
  fixes k::int
  assumes "even k"
  shows "sin (pi / 2 + k * pi) = 1"
  using assms
  by (simp add: sin_add)

text \<open>Solving trigonometric equations and systems with special values (0, 1, or -1) of sine and cosine functions\<close>

lemma cos_0_iff_canon:
  assumes "cos \<phi> = 0" and "-pi < \<phi>" and "\<phi> \<le> pi"
  shows "\<phi> = pi/2 \<or> \<phi> = -pi/2"
  by (smt (verit, best) arccos_0 arccos_cos assms cos_minus divide_minus_left)

lemma sin_0_iff_canon:
  assumes "sin \<phi> = 0" and "-pi < \<phi>" and "\<phi> \<le> pi"
  shows "\<phi> = 0 \<or> \<phi> = pi"
  using assms sin_eq_0_pi by force

lemma cos0_sin1:
  assumes "sin \<phi> = 1"
  shows "\<exists> k::int. \<phi> = pi/2 + 2*k*pi"
  by (smt (verit, ccfv_threshold) assms cos_diff cos_one_2pi_int cos_pi_half mult_cancel_right1 sin_pi_half sin_plus_pi)

(* TODO: add lemmas for cos = -1, sin = 0 and cos = 0, sin = -1 *)


text \<open>Sine is injective on $[-\frac{\pi}{2}, \frac{\pi}{2}]$\<close>

lemma sin_inj:
  assumes "-pi/2 \<le> \<alpha> \<and> \<alpha> \<le> pi/2" and "-pi/2 \<le> \<alpha>' \<and> \<alpha>' \<le> pi/2"
  assumes "\<alpha> \<noteq> \<alpha>'"
  shows "sin \<alpha> \<noteq> sin \<alpha>'"
  by (metis assms divide_minus_left sin_inj_pi)

text \<open>Periodicity of trigonometric functions\<close>

text \<open>The following are available in HOL-Decision\_Procs.Approximation\_Bounds, but we want to avoid
that dependency\<close>

lemma sin_periodic_nat [simp]: 
  fixes n :: nat
  shows "sin (x + n * (2 * pi)) = sin x"
  by (metis (no_types, opaque_lifting) add.commute add.left_neutral cos_2npi cos_one_2pi_int mult.assoc mult.commute mult.left_neutral mult_zero_left sin_add sin_int_2pin)

lemma sin_periodic_int [simp]:
  fixes i :: int
  shows "sin (x + i * (2 * pi)) = sin x"
  by (metis add.right_neutral cos_int_2pin mult.commute mult.right_neutral mult_zero_right sin_add sin_int_2pin)

lemma cos_periodic_nat [simp]: 
  fixes n :: nat
  shows "cos (x + n * (2 * pi)) = cos x"
  by (metis add.left_neutral cos_2npi cos_add cos_periodic mult.assoc mult_2 mult_2_right of_nat_numeral sin_periodic sin_periodic_nat)

lemma cos_periodic_int [simp]:
  fixes i :: int
  shows "cos (x + i * (2 * pi)) = cos x"
  by (metis cos_add cos_int_2pin diff_zero mult.commute mult.right_neutral mult_zero_right sin_int_2pin)

text \<open>Values of both sine and cosine are repeated only after multiples of $2\cdot \pi$\<close>

lemma sin_cos_eq:
  fixes a b :: real
  assumes "cos a = cos b" and "sin a = sin b"
  shows "\<exists> k::int. a - b = 2*k*pi"
  by (metis assms cos_diff cos_one_2pi_int mult.commute sin_cos_squared_add3)

text \<open>The following two lemmas are consequences of surjectivity of cosine for the range $[-1, 1]$.\<close>

lemma ex_cos_eq:
  assumes "-pi/2 \<le> \<alpha> \<and> \<alpha> \<le> pi/2"
  assumes "a \<ge> 0" and "a < 1"
  shows "\<exists> \<alpha>'. -pi/2 \<le> \<alpha>' \<and> \<alpha>' \<le> pi/2 \<and> \<alpha>' \<noteq> \<alpha> \<and> cos (\<alpha> - \<alpha>') = a"
proof-
  have "arccos a > 0" "arccos a \<le> pi/2"
    using \<open>a \<ge> 0\<close> \<open>a < 1\<close>
    using arccos_lt_bounded arccos_le_pi2
    by auto

  show ?thesis
  proof (cases "\<alpha> - arccos a \<ge> - pi/2")
    case True
    thus ?thesis
      using assms \<open>arccos a > 0\<close> \<open>arccos a \<le> pi/2\<close>
      by (rule_tac x = "\<alpha> - arccos a" in exI) auto
  next
    case False
    thus ?thesis
      using assms \<open>arccos a > 0\<close> \<open>arccos a \<le> pi/2\<close>
      by (rule_tac x = "\<alpha> + arccos a" in exI) auto
  qed
qed

lemma ex_cos_gt:
  assumes "-pi/2 \<le> \<alpha> \<and> \<alpha> \<le> pi/2"
  assumes "a < 1"
  shows "\<exists> \<alpha>'. -pi/2 \<le> \<alpha>' \<and> \<alpha>' \<le> pi/2 \<and> \<alpha>' \<noteq> \<alpha> \<and> cos (\<alpha> - \<alpha>') > a"
proof-
  obtain a' where "a' \<ge> 0" "a' > a" "a' < 1"
    by (metis assms(2) dense_le_bounded linear not_one_le_zero)
  thus ?thesis
    using ex_cos_eq[of \<alpha> a'] assms
    by auto
qed

text \<open>The function @{term atan2} is a generalization of @{term arctan} that takes a pair of coordinates
of non-zero points returns its angle in the range $[-\pi, \pi)$.\<close>

definition atan2 where
  "atan2 y x =
    (if x > 0 then arctan (y/x)
     else if x < 0 then
          if y > 0 then arctan (y/x) + pi else arctan (y/x) - pi
     else
          if y > 0 then pi/2 else if y < 0 then -pi/2 else 0)"

lemma atan2_bounded: 
  shows "-pi \<le> atan2 y x \<and> atan2 y x < pi"
  using arctan_bounded[of "y/x"] zero_le_arctan_iff[of "y/x"] arctan_le_zero_iff[of "y/x"] zero_less_arctan_iff[of "y/x"] arctan_less_zero_iff[of "y/x"]
  using divide_neg_neg[of y x] divide_neg_pos[of y x] divide_pos_pos[of y x]  divide_pos_neg[of y x]
  unfolding atan2_def
  by (simp (no_asm_simp)) auto

end
