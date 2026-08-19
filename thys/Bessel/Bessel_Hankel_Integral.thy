(*
  File:     Bessel_Hankel_Integral.thy
  Author:   Manuel Eberl, University of Innsbruck
*)
section \<open>A Hankel-style integral formula for the Bessel $I$ function\<close>
theory Bessel_Hankel_Integral
imports 
  "Bessel.Bessel"
  "Path_Automation.Path_Automation"
  "Prime_Number_Theorem.Prime_Number_Theorem_Library"
  "Incomplete_Gamma.More_Beta"
begin

(*<*)
hide_fact (open) Zeta_Library.has_absolute_integral_change_of_variables_1'
(*>*)


subsection \<open>Auxiliary integrals\<close>

text \<open>
  Later on, we will need the integral
  \[
     \int_{-\infty}^\infty (c^2 + t^2)^{-a}\,\text{d}t = 
       \frac{1}{2} c^{1-2a} B(\frac{1}{2}, a-\frac{1}{2})
  \]
  for $c > 0$, $a > \frac{1}{2}$. We first show the $\int_0^\infty$ version. To this end,
  we perform the substitution $x = (t/c)^2$ to get
  \[\frac{1}{2}c^{1-2e} \int_0^\infty x^{-\frac{1}{2}} (1+x)^{-e} \,\text{d}x\ ,\]
  which is one of the various equivalent integral definitions of the Beta function.
\<close>
lemma Bessel_I_aux_integral1:
  fixes c e :: real
  assumes c: "c > 0" and e: "e > 1/2"
  shows "(\<lambda>t. (c\<^sup>2 + t\<^sup>2) powr -e) absolutely_integrable_on {0<..}"
        "integral {0<..} (\<lambda>t. (c\<^sup>2 + t\<^sup>2) powr -e) = c powr (1 - 2 * e) / 2 * Beta (1/2) (e - 1/2)"
proof -
  define C where "C = c powr (1-2*e) / 2"
  define f where "f = (\<lambda>x. C * (x powr (-1/2) / (1 + x) powr e))"
  define g where "g = (\<lambda>x. (x / c) ^ 2)"
  define g' where "g' = (\<lambda>x. 2 * x / c ^ 2)"
  define h where "h = (\<lambda>x. (c\<^sup>2 + x\<^sup>2) powr (-e))"
  define I where "I = c powr (1-2*e) / 2 * Beta (1/2) (e - 1/2)" 

  have bij: "bij_betw g {0<..} {0<..}"
    by (rule bij_betwI[of _ _ _ "\<lambda>y. sqrt y * c"]) (use c in \<open>auto simp: g_def\<close>)

  have eq: "\<bar>g' x\<bar> *\<^sub>R f (g x) = h x" if x: "x > 0" for x
  proof -
    have "\<bar>g' x\<bar> *\<^sub>R f (g x) = c powr (-2 * e) * (c ^ 2) powr e / (c\<^sup>2 + x\<^sup>2) powr e" using x c
      by (auto simp: g'_def f_def g_def field_simps powr_divide powr_minus 
                     powr_half_sqrt power2_eq_square C_def powr_diff)
    also have "(c ^ 2) powr e = c powr (2*e)"
      by (subst powr_powr [symmetric]) (use c in simp_all)
    also have "c powr (-2 * e) * \<dots> = 1"
      by (subst powr_add [symmetric]) (use c in auto)
    finally show ?thesis
      by (simp add: powr_minus field_simps h_def)
  qed

  have "(f has_integral I) {0<..}"
    using has_integral_mult_right[OF has_integral_Beta_0_infinity_real[of "1/2" "e - 1/2"], of C] e
    by (simp add: f_def I_def C_def)
  hence "f absolutely_integrable_on {0<..} \<and> integral {0<..} f = I"
    using c by (simp add: f_def has_integral_iff absolutely_integrable_on_iff_nonneg C_def)
  also have "{0<..} = g ` {0<..}"
    using bij by (simp add: bij_betw_def)
  also have "f absolutely_integrable_on g ` {0<..} \<and> integral (g ` {0<..}) f = I \<longleftrightarrow>
             (\<lambda>x. \<bar>g' x\<bar> * f (g x)) absolutely_integrable_on {0<..} \<and>
             integral {0<..} (\<lambda>x. \<bar>g' x\<bar> * f (g x)) = I"
    by (subst (2) eq_commute, intro has_absolute_integral_change_of_variables_1')
       (use c bij in \<open>auto simp: g_def g'_def power2_eq_square bij_betw_def
                           intro!: derivative_eq_intros\<close>)
  also have "(\<lambda>x. \<bar>g' x\<bar> * f (g x)) absolutely_integrable_on {0<..} \<longleftrightarrow>
             h absolutely_integrable_on {0<..}"
    by (rule set_integrable_cong) (use eq in auto)
  also have "integral {0<..} (\<lambda>x. \<bar>g' x\<bar> * f (g x)) = integral {0<..} h"
    by (rule integral_cong) (use eq in auto)
  finally show "h absolutely_integrable_on {0<..}" "integral {0<..} h = I"
    by (simp_all add: h_def)
qed

text \<open>
  The $\int_{-\infty}^\infty$ version then easily follows by symmetry.
\<close>
lemma Bessel_I_aux_integral2:
  fixes c e :: real
  assumes c: "c > 0" and e: "e > 1/2"
  shows "integrable lebesgue (\<lambda>t. (c\<^sup>2 + t\<^sup>2) powr -e)"
  and   "lebesgue_integral lebesgue (\<lambda>t. (c\<^sup>2 + t\<^sup>2) powr -e) = c powr (1-2*e) * Beta (1/2) (e - 1/2)"
proof -
  define I where "I = c powr (1-2*e) / 2 * Beta (1/2) (e - 1/2)"
  have integrable: "(\<lambda>t. (c\<^sup>2 + t\<^sup>2) powr -e) absolutely_integrable_on {0<..}"
   and integral:   "integral {0<..} (\<lambda>t. (c\<^sup>2 + t\<^sup>2) powr -e) = I"
   using Bessel_I_aux_integral1[of c e] c e by (simp_all add: I_def)

  show integrable': "integrable lebesgue (\<lambda>t. (c\<^sup>2 + t\<^sup>2) powr -e)"
  proof -
    have "(\<lambda>t. (c\<^sup>2 + t\<^sup>2) powr -e) absolutely_integrable_on {..<0}"
      using lebesgue_integrable_real_affine_iff[of "-1" "\<lambda>t. indicator {0<..} t * (c\<^sup>2 + t\<^sup>2) powr -e" 0]
            integrable unfolding set_integrable_def by (simp add: indicator_def)
    hence "(\<lambda>t. (c\<^sup>2 + t\<^sup>2) powr -e) absolutely_integrable_on ({0<..} \<union> {..<0} \<union> {0})"
      by (intro set_integrable_Un integrable) (auto intro: absolutely_integrable_negligible)
    also have "({0<..} \<union> {..<0} \<union> {0}) = (UNIV :: real set)"
      by auto
    finally show ?thesis
      by (simp add: set_integrable_def)
  qed

  show "lebesgue_integral lebesgue (\<lambda>t. (c\<^sup>2 + t\<^sup>2) powr -e) = c powr (1-2*e) * Beta (1/2) (e - 1/2)"
  proof -
    have integrable'': "set_integrable lebesgue UNIV (\<lambda>t. (c\<^sup>2 + t\<^sup>2) powr -e)"
      using integrable' by (simp add: set_integrable_def)
    have "I = integral {0<..} (\<lambda>t. (c\<^sup>2 + t\<^sup>2) powr -e)"
      using integral by simp
    also have "\<dots> = (LINT t:{0<..}|lebesgue. (c\<^sup>2 + t\<^sup>2) powr -e)"
      using integrable by (rule set_lebesgue_integral_eq_integral(2) [symmetric])
    finally have *: "(LINT t:{0<..}|lebesgue. (c\<^sup>2 + t\<^sup>2) powr -e) = I" ..
    have **: "(LINT t:{..<0}|lebesgue. (c\<^sup>2 + t\<^sup>2) powr -e) = I"
      unfolding set_lebesgue_integral_def
      by (subst lebesgue_integral_real_affine[of "-1" _ 0]) 
         (use * in \<open>simp_all add: set_lebesgue_integral_def indicator_def\<close>)

    have "(LINT t|lebesgue. (c\<^sup>2 + t\<^sup>2) powr -e) = (LINT t:-{0}|lebesgue. (c\<^sup>2 + t\<^sup>2) powr -e)"
      unfolding set_lebesgue_integral_def
    proof (rule integral_cong_AE)
      have "AE x in lebesgue. x \<noteq> 0"
        by (metis AE_completion_iff AE_lborel_singleton)
      thus "AE x in lebesgue. (c\<^sup>2 + x\<^sup>2) powr -e = indicator (-{0}) x *\<^sub>R (c\<^sup>2 + x\<^sup>2) powr -e"
        by eventually_elim (auto simp: indicator_def)
    qed (auto intro!: measurable_completion)
    also have "-{0} = {0<..} \<union> {..<0::real}"
      by auto
    also have "(LINT x:({0<..} \<union> {..<0::real})|lebesgue. (c\<^sup>2 + x\<^sup>2) powr -e) =
               (LINT x:{0<..}|lebesgue. (c\<^sup>2 + x\<^sup>2) powr -e) + (LINT x:{..<0}|lebesgue. (c\<^sup>2 + x\<^sup>2) powr -e)"
      by (rule set_integral_Un) (auto intro!: set_integrable_subset[OF integrable''])
    also have "\<dots> = 2 * I"
      using * ** by simp
    finally show ?thesis
      by (simp add: I_def)
  qed
qed


subsection \<open>A Hankel-style representation for $1/\Gamma(s)$\<close>

text \<open>
  The biggest piece of work in this section will be to derive the following Hankel-style contour 
  integral formula for $\Gamma$:
  \[
    \frac{1}{\Gamma(s)} = \frac{1}{2\pi i} \int_{c-i\infty}^{c+i\infty}e^z z^{-s}\,\text{d}z
  \]
  For $\text{Re}(s)>1$, the integral clearly converges absolutely as a Lebesgue integral.
  For $\text{Re}(s)\in (0,1]$ it has to be interpreted as a Cauchy principal value, i.e.\ 
  $\int_{c-i\infty}^{c+i\infty} = \lim_{T\to\infty}\int_{c-iT}^{c+IT}$.

  We first show the existence of the integral as a Lebesgue integral if $\text{Re}(s) > 1$. This 
  is fairly easy to see by a comparison test, since it is $O(|t|^{-\text{Re}(s)})$ uniformly 
  for all $t$.
\<close>
lemma rGamma_hankel_integrable:
  assumes c: "c > 0" and s: "Re s > 1"
  shows   "((\<lambda>z. exp z * z powr (-s)) \<circ> (\<lambda>t. Complex c t)) absolutely_integrable_on UNIV"
proof -
  have *: "((\<lambda>z. exp z * z powr (-s)) \<circ> (\<lambda>t. Complex c (a*t))) absolutely_integrable_on {1..}"
    if [simp]: "\<bar>a\<bar> = 1" for a :: real
  proof (rule set_integrable_bound)
    have "AE t in lebesgue. t \<noteq> 0"
      by (simp add: AE_completion_iff AE_lborel_singleton)
    thus "AE t\<in>{1..} in lebesgue. norm (((\<lambda>z. exp z * z powr (-s)) \<circ> (\<lambda>t. Complex c (a*t))) t) \<le> 
                                   norm (exp c * exp (pi * \<bar>Im s\<bar>) * \<bar>t\<bar> powr -Re s)"
    proof eventually_elim
      case (elim t)
      have "norm (exp (Complex c (a*t)) * Complex c (a*t) powr - s) =
               exp c * norm (Complex c (a*t)) powr -Re s * exp (Im s * Arg (Complex c (a*t)))"
        using c by (simp add: norm_mult norm_exp norm_powr_complex)
      also have "\<dots> \<le> exp c * \<bar>t\<bar> powr -Re s * exp (\<bar>Im s\<bar> * pi)"
      proof (intro mult_mono)
        show "norm (Complex c (a*t)) powr -Re s \<le> \<bar>t\<bar> powr -Re s"
          by (rule powr_mono2')
             (use s elim abs_Im_le_cmod[of "Complex c (a*t)"] in \<open>auto simp: abs_mult\<close>)
      next
        have "Im s * Arg (Complex c (a*t)) \<le> \<bar>Im s * Arg (Complex c (a*t))\<bar>"
          by linarith
        also have "\<dots> \<le> \<bar>Im s\<bar> * pi"
          unfolding abs_mult using Arg_bounded[of "Complex c (a*t)"] by (auto intro!: mult_left_mono)
        finally show "exp (Im s * Arg (Complex c (a*t))) \<le> exp (\<bar>Im s\<bar> * pi)"
          by simp
      qed auto
      finally show ?case
        by (auto simp: mult_ac)
    qed
  next
    have "(\<lambda>x. x powr -Re s) absolutely_integrable_on {1<..}"
      using s set_integrable_powr_at_top[of 1 0 "-Re s"] by simp
    hence "(\<lambda>x. x powr -Re s) integrable_on {1<..}"
      using set_lebesgue_integral_eq_integral(1) by blast
    also have "?this \<longleftrightarrow> (\<lambda>x. x powr -Re s) integrable_on {1..}"
    proof (rule integrable_spike_set_eq)
      have "negligible {1::real}"
        by simp
      also have "\<dots> = sym_diff {1<..} {1..}"
        by auto
      finally show "negligible (sym_diff {1<..} {1..} :: real set)" .
    qed
    finally have "(\<lambda>x. exp c * exp (pi * \<bar>Im s\<bar>) * x powr - Re s) integrable_on {1..}"
      by (rule integrable_on_mult_right)
    also have "?this \<longleftrightarrow> (\<lambda>x. exp c * exp (pi * \<bar>Im s\<bar>) * \<bar>x\<bar> powr - Re s) integrable_on {1..}"
      by (rule integrable_cong) auto
    finally show "(\<lambda>x. exp c * exp (pi * \<bar>Im s\<bar>) * \<bar>x\<bar> powr - Re s) absolutely_integrable_on {1..}"
      by (rule nonnegative_absolutely_integrable_1) auto
  qed (auto simp: set_borel_measurable_def Complex_eq intro!: measurable_completion)

  have "integrable lebesgue (\<lambda>t. indicator {1..} t *\<^sub>R (((\<lambda>z. exp z * z powr (-s)) \<circ> (\<lambda>t. Complex c (-t))) t))"
    using *[of "-1"] by (simp add: set_integrable_def)
  from lebesgue_integrable_real_affine[OF this, of "-1" 0]
    have "((\<lambda>z. exp z * z powr (-s)) \<circ> (\<lambda>t. Complex c t)) absolutely_integrable_on {..-1}"
      unfolding set_integrable_def by (simp add: indicator_def)
  moreover have "((\<lambda>z. exp z * z powr (-s)) \<circ> (\<lambda>t. Complex c t)) absolutely_integrable_on {1..}"
    using *[of 1] by simp
  moreover have "((\<lambda>z. exp z * z powr (-s)) \<circ> (\<lambda>t. Complex c t)) absolutely_integrable_on {-1..1}"
    by (rule absolutely_integrable_continuous_real)
       (use c in \<open>auto intro!: continuous_intros simp: complex_eq_iff\<close>)
  ultimately have "((\<lambda>z. exp z * z powr (-s)) \<circ> (\<lambda>t. Complex c t)) absolutely_integrable_on 
          ({-1..1} \<union> {1..} \<union> {..-1})"
    by (intro set_integrable_Un) auto
  also have "{-1..1} \<union> {1..} \<union> {..-1::real} = UNIV"
    by auto
  finally show ?thesis .
qed

text \<open>
  Next, we show the actual integral formula in the case that $\text{Re}(s) > 0$.
  The proof works is modelled after Lemma~2.3 by Kong and Teo~\<^cite>\<open>kong_teo\<close> and goes roughly 
  like this:

    \<^item> We consider the Hankel-style integration contour sketched in Figure~\ref{fig:contour}.

    \<^item> Since two of the horizontal lines lie directly on the branch cut, this integral is very
      awkward to handle. We instead only consider the part of the contour in the upper half plane,
      adding a horizontal line on the positive real axis to connect the part we cut off,
      and then also move the branch cut out of the way to the negative real axis by using the
      alternative branch of the logarithm $\widehat{\ln} z = \ln (-iz) + \tfrac{1}{2}i\pi$.

    \<^item> We apply the Cauchy integral theorem to this contour and note that the integrand has no
      singularities inside, so its value must be 0.

    \<^item> We do the same for the portion of the contour that is in the lower half of the complex plane
      and add the two values, noting that the horizontal lines we added cancel out.
      To save some work, we note that we can get this result for the lower half plane from that
      for the upper half plane (which we already have) by complex conjugation due to the fact that
      the integrand is symmetric under conjugation.

    \<^item> Denote the vertical integral at $\text{Re}(z) = c$ as $\text{lhs}(T,s)$ and the sum of
      the other ones as $\text{rhs}(r,T,s)$. The above shows that 
      $\text{lhs}(T,s) = \text{rhs}(r,T,s)$ holds for all $s$ with $\text{Re}(s) > 0$.
   
    \<^item> This immediately means that the value of $\text{rhs}(r,T,s)$ is actually independent of $r$.

    \<^item> Note also that $\lim_{T\to\infty} \text{rhs}(r,T,s)$ exists for any $s$ with
      $\text{Re}(s) > 0$, and of course this limit is also independent of $r$.
      Write $\text{RHS}(r,s)$ for this limit. In particular, this already shows that
      $\text{lhs}(T,s)$ also has a limit for $T\to\infty$ and its value is $\text{RHS}(r,s)$.

    \<^item> In fact, $\text{RHS}(r,s)$ can be expressed in terms of the incomplete Gamma function
      $\Gamma(1-s,r)$ and some error terms corresponding to the small circle around the origin.

    \<^item> Thus, if $\text{Re}(s) < 1$, we can let $r\to 0$ and find that the error terms in
      $\text{RHS}(r,s)$ vanish and $\lim_{r\to 0} \Gamma(1-s,r) = \Gamma(1-s)$. Together with the 
      reflection formula for $\Gamma$, we obtain $\text{RHS}(s) = 2\pi/\Gamma(s)$, 
      exactly as we wanted. This establishes the result we wanted in the strip
      $0 < \text{Re}(s) < 1$.

    \<^item> Moreover, both $\Gamma(1-s,r)$ and the error terms and other factors occurring in
      $\text{RHS}(r,s)$ are holomorphic functions in $s$ for $\text{Re}(s) > 0$, so we can use 
      analytic continuation to lift the above equality to all $s$ with $\text{Re}(s) > 0$
      and we are done.

\begin{figure}[t]
\begin{center}
\begin{tikzpicture}[>=Latex, thick]
% ---- colors matching the five contour pieces ----
\definecolor{myblue}{HTML}{378ADD}   % Lv
\definecolor{myteal}{HTML}{1D9E75}   % Cb
\definecolor{mycoral}{HTML}{D85A30}  % Lh
\definecolor{myamber}{HTML}{BA7517}  % Cs
\definecolor{mypink}{HTML}{D4537E}   % Lh'
 
% ---- illustrative values: c, y, r ----
\coordinate (A) at (1.5,0);      % c
\coordinate (B) at (1.5,4.5);    % c+iy
\coordinate (C) at (-4.5,4.5);   % -y+iy
\coordinate (D) at (-4.5,0);     % -y
\coordinate (E) at (-0.6,0);     % -r
\coordinate (F) at (0.6,0);      % r
\coordinate (O) at (0,0);        % origin (excluded)
 
% ---- axes ----
\draw[->, gray, line width=0.4pt] (-5.8,0) -- (3,0);
\draw[->, gray, line width=0.4pt] (0,-0.6) -- (0,5.1);
 
% ---- contour segments, in order ----
\draw[myblue, ->]  (A) -- node [midway, right] {\color{myblue} $L_v$} (B); % Lv
\draw[myteal, ->]  (B) -- (C); % Cb (top)
\draw[myteal, ->]  (C) -- node [midway, right] {\color{myteal} $C_b$} (D); % Cb (left side)
\draw[mycoral, ->] (D) -- node [midway, above] {\color{mycoral} $L_h$} (E); % Lh
\draw[myamber, ->] (E) arc (180:0:0.6) node [midway, above left] {\color{myamber} $C_s$}; % Cs, semicircle over 0
\draw[mypink, ->]  (F) -- node [midway, above] {\color{mypink} $L_h'$} (A); % Lh'
 
% ---- vertices ----
\foreach \p in {A,B,C,D,E,F} \fill (\p) circle (1.6pt);

% ---- point labels ----
\node[below]        at (A) {$\mathstrut c$};
\node[above]        at (B) {$\mathstrut c+iy$};
\node[above]        at (C) {$\mathstrut -y+iy$};
\node[below]        at (D) {$\mathstrut -y$};
\node[below]        at (E) {$\mathstrut -r$};
\node[below]        at (F) {$\mathstrut r$};
\end{tikzpicture}
\end{center}
\caption{The Hankel-style integration contour used in the proof of the 
  $\int_{c-i\infty}^{c+i\infty}$-style integral representation for $1/\Gamma(s)$.}
\label{fig:contour}
\end{figure}
\<close>
theorem rGamma_hankel_strong:
  assumes c: "c > 0" and s: "Re s > 0"
  shows   "((\<lambda>T. integral {-T..T} ((\<lambda>z. exp z * z powr (-s)) \<circ> (\<lambda>t. Complex c t))) 
              \<longlongrightarrow> (2 * of_real pi * rGamma s)) at_top"
proof -
  define A where "A = {z. Re z = 0 \<and> Im z \<le> 0}"
  define Ln' where "Ln' \<equiv> (\<lambda>z. ln (-\<i> * z) + \<i> * pi / 2)"
  have [holomorphic_intros]: "Ln' holomorphic_on X" if "X \<inter> A = {}" for X
    unfolding Ln'_def using that
    by (auto intro!: holomorphic_intros simp: A_def complex_nonpos_Reals_iff)
  have [analytic_intros]: "Ln' analytic_on X" if "X \<inter> A = {}" for X
    unfolding Ln'_def using that 
    by (auto intro!: analytic_intros simp: A_def complex_nonpos_Reals_iff)

  have Ln'_of_real_pos: "Ln' (of_real x) = of_real (ln x)" if "x > 0" for x
  proof -
    have "Ln' (of_real x) = Ln (of_real x * (-\<i>)) + \<i> * pi / 2"
      by (simp add: Ln'_def mult_ac)
    also have "\<dots> = of_real (ln x)" using that
      by (subst Ln_times_of_real) (auto simp: Ln_of_real)
    finally show ?thesis .
  qed

  have Ln'_of_real_neg: "Ln' (of_real x) = of_real (ln (-x)) + \<i> * pi" if "x < 0" for x
  proof -
    have "Ln' (of_real x) = Ln (of_real (-x) * \<i>) + \<i> * pi / 2"
      by (simp add: Ln'_def mult_ac)
    also have "\<dots> = of_real (ln (-x)) + \<i> * pi" using that
      by (subst Ln_times_of_real) (auto simp: Ln_Reals_eq)
    finally show ?thesis .
  qed

  have Ln'_eq_Ln: "Ln' z = Ln z" if z: "z \<noteq> 0" "Im z \<ge> 0" for z
  proof -
    have "0 \<le> Im (Ln z)" "Im (Ln z) \<le> pi"
      using z Im_Ln_pos_le[of z] by auto
    moreover from this have "Im (Ln z) > -pi/2"
      using pi_gt_zero by linarith
    ultimately show ?thesis
    unfolding Ln'_def using z
    by (subst Ln_times_simple) auto
  qed

  define f where "f = (\<lambda>s z. exp z * z powr (-s) :: complex)"
  define fr where "fr = (\<lambda>s z. exp z * complex_of_real z powr (-s))"
  define g where "g = (\<lambda>s z. exp (z - s * Ln' z))"
  define h :: "complex \<Rightarrow> real \<Rightarrow> complex"
    where "h = (\<lambda>s t. exp (of_real t - s * of_real (ln (-t))))"

  define Lv :: "real \<Rightarrow> real \<Rightarrow> complex" where "Lv = (\<lambda>y. linepath (of_real c) (Complex c y))"
  define Lh :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> complex"
    where "Lh = (\<lambda>r y. linepath (-of_real y) (-of_real r))"
  define Lh' :: "real \<Rightarrow> real \<Rightarrow> complex"
    where "Lh' = (\<lambda>r. linepath (of_real r) (of_real c))"
  define Cb :: "real \<Rightarrow> real \<Rightarrow> complex"
    where "Cb = (\<lambda>y. linepath (Complex c y) (Complex (-y) y) +++ linepath (Complex (-y) y) (-of_real y))"
  define Cs :: "real \<Rightarrow> real \<Rightarrow> complex"
    where "Cs = (\<lambda>r. part_circlepath 0 r pi 0)"
  define err1 where "err1 = (\<lambda>s y. contour_integral (Cb y) (g s))"
  define err2 where "err2 = (\<lambda>s r. contour_integral (Cs r) (g s))"

  have "pathstart (Lv y) = of_real c" "pathfinish (Lv y) = Complex c y" for y
    by (auto simp: Lv_def)
  have "pathstart (Cb y) = Complex c y" "pathfinish (Cb y) = of_real (-y)" for y
    by (auto simp: Cb_def complex_eq_iff Im_exp Re_exp)

  have path_image_Cb: "z \<notin> A" if z: "z \<in> path_image (Cb T)" and T: "T > c" for z T
    using that T c by (auto simp: A_def Cb_def path_image_join closed_segment_same_Re closed_segment_same_Im)

  have path_image_Cs: "z \<notin> A" if z: "z \<in> path_image (Cs r)" and r: "r > 0" for z r
  proof
    assume "z \<in> A"
    have "z \<in> path_image (part_circlepath 0 r 0 pi)"
      using z unfolding Cs_def by (metis reversepath_part_circlepath path_image_reversepath)
    then obtain t where t: "z = rcis r t" "t \<in> {0..pi}"
      by (auto simp: path_image_part_circlepath rcis_def cis_conv_exp)
    with \<open>z \<in> A\<close> and r have "cos t = 0"
      by (auto simp: A_def t(1))
    with t(2) have "t = pi / 2"
      by (metis arccos_0 arccos_cos atLeastAtMost_iff)
    with t(2) and \<open>z \<in> A\<close> and r show False
      by (auto simp: t(1) A_def)
  qed

  text \<open>
    The horizontal line integral on the left half of the real axis can be extended to infinity
    for any $s$ due to the exponential decay of the integrand.
  \<close>
  have integrable: "set_integrable lborel {r..} (\<lambda>t. h s (-t))" if r: "r > 0" for r s
    using absolutely_integrable_incomplete_Gamma[of r s] r
    by (simp add: h_def set_integrable_def integrable_completion)


  text \<open>
    We first consider a ``half-Hankel'' contour consisting only of the half of the Hankel 
    contour lying in the upper half plane.
  \<close>
  define \<gamma> where "\<gamma> = (\<lambda>r y. Lv y +++ Cb y +++ Lh r y +++ Cs r +++ Lh' r)"
  have \<gamma>: "valid_path (\<gamma> r y)" "pathfinish (\<gamma> r y) = pathstart (\<gamma> r y)"
    if "y \<ge> c" "r \<ge> 0" for r y using that c
      by (auto simp: \<gamma>_def Lv_def Lh_def Cb_def Cs_def Lh'_def A_def complex_eq_iff Re_exp Im_exp
                     path_image_join closed_segment_same_Re closed_segment_same_Im
                     closed_segment_eq_real_ivl intro!: valid_path_join)
  have path_image_\<gamma>: "path_image (\<gamma> r T) \<subseteq> -A"
    if "T > c" "r > 0" "r < c" for r T
    using path_image_Cs[of _ r] path_image_Cb[of _ T] that
    by (auto simp: \<gamma>_def Cs_def Cb_def Lv_def Lh_def Lh'_def path_image_join 
          closed_segment_same_Re closed_segment_same_Im closed_segment_eq_real_ivl A_def)

  text \<open>
    Applying Cauchy's theorem to this contour, we obtain a term relating the horizontal
    integral on the real axis with the vertical one, modulo some error terms.
  \<close>
  have 1: "\<i> * integral {0..y} (\<lambda>x. f s (Complex c x)) + integral {-y..-r} (fr s) =
             -(integral {r..c} (fr s) + err1 s y + err2 s r)"
     if yr: "y > c" "r > 0" "r < c" for s :: complex and r y :: real
  proof -
    have "(g s has_contour_integral 0) (\<gamma> r y)"
    proof (rule Cauchy_theorem_simply_connected)
      show "open (-A)"
      proof -
        have "closed ({z. Re z = 0} \<inter> {z. Im z \<le> 0})"
          by (intro closed_Int closed_halfspace_Re_eq closed_halfspace_Im_le)
        also have "\<dots> = A"
          by (auto simp: A_def)
        finally show ?thesis
          by auto
      qed
    next
      show "simply_connected (-A)"
      proof (rule simply_connected_retraction_gen)
        show "simply_connected (-complex_of_real ` {..0})"
          by (rule simply_connected_slotted_complex_plane_left)
      next
        show "continuous_on (-A) (\<lambda>z. -\<i> * z)" "continuous_on (-complex_of_real ` {..0}) (\<lambda>z. \<i> * z)"
          by (auto intro!: continuous_intros)
      next
        have "bij_betw (\<lambda>z. \<i> * z) (- complex_of_real ` {..0}) (-A)"
          by (rule bij_betwI[of _ _ _ "\<lambda>z. -\<i> * z"]) (auto simp: A_def complex_eq_iff)
        thus "(*) \<i> ` (- complex_of_real ` {..0}) = - A"
          by (simp add: bij_betw_def)
      qed (auto simp: complex_eq_iff A_def)
    next
      show "g s holomorphic_on -A"
        by (auto simp: g_def intro!: holomorphic_intros)
    qed (use \<gamma>[of y r] path_image_\<gamma>[of y r] yr in simp_all)
    hence "contour_integral (\<gamma> r y) (g s) = 0"
      using contour_integral_unique by blast

    also have "contour_integral (\<gamma> r y) (g s) = 
               contour_integral (Lv y) (g s) + contour_integral (Cb y) (g s) +
               contour_integral (Lh r y) (g s) + contour_integral (Cs r) (g s) +
               contour_integral (Lh' r) (g s)"
      unfolding \<gamma>_def
    proof path
      show "g s analytic_on path_image (Lv y +++ Cb y +++ Lh r y +++ Cs r +++ Lh' r)"
      proof (rule analytic_on_subset)
        show "path_image (Lv y +++ Cb y +++ Lh r y +++ Cs r +++ Lh' r) \<subseteq> -A"
          using path_image_Cb[of _ y] path_image_Cs[of _ r] yr c
          unfolding Lv_def Cb_def Lh_def Cs_def Lh'_def
          by (fastforce simp: path_image_join A_def closed_segment_same_Re closed_segment_same_Im
                              closed_segment_eq_real_ivl)
      qed (auto intro!: analytic_intros simp: g_def)
    qed (auto simp: Cs_def Lh'_def Lh_def Cb_def Lv_def)

    also have "contour_integral (Lh r y) (g s) = integral {-y..-r} (\<lambda>x. g s (of_real x))"
      unfolding Lh_def by (subst contour_integral_linepath_Reals_eq) (use yr c in simp_all)
    also have "\<dots> = integral {-y..-r} (fr s)"
      unfolding g_def fr_def using c yr
      by (intro integral_cong)
         (auto simp: Ln'_of_real_neg powr_def Ln_of_real' field_simps exp_diff exp_minus exp_add)
    also have "contour_integral (Lh' r) (g s) = integral {r..c} (\<lambda>x. g s (of_real x))"
      unfolding Lh'_def by (subst contour_integral_linepath_Reals_eq) (use yr c in simp_all)
    also have "\<dots> = integral {r..c} (fr s)"
      unfolding g_def fr_def using c yr
      by (intro integral_cong)
         (auto simp: Ln'_of_real_pos powr_def Ln_of_real' field_simps exp_diff exp_minus exp_add)
    also have "contour_integral (Lv y) (g s) = \<i> * integral {0..y} (\<lambda>x. g s (Complex c x))"
      unfolding Lv_def by (rule contour_integral_linepath_same_Re) (use yr in auto)
    also have "integral {0..y} (\<lambda>x. g s (Complex c x)) = integral {0..y} (\<lambda>x. f s (Complex c x))"
      unfolding g_def f_def
      by (intro integral_cong, subst Ln'_eq_Ln)
         (use c in \<open>auto simp: g_def powr_def field_simps exp_diff exp_minus exp_add complex_eq_iff\<close>)
    finally show ?thesis
      unfolding err1_def err2_def by (Groebner_Basis.algebra)
  qed

  text \<open>
    We combine this result with a flipped copy of itself to get the full Hankel contour.
    One of the error terms, namely the horizontal line along the positive real axis, cancels.
  \<close>
  have 2: "integral {-y..y} (\<lambda>t. f s (Complex c t)) =
             2 * sin (pi * s) * (CLBINT t=r..y. h s (-t)) -
             \<i> * (cnj (err1 (cnj s) y) + cnj (err2 (cnj s) r) - err2 s r - err1 s y)"
    if yr: "y > c + r" "r > 0" "r < c" for s :: complex and y r :: real
  proof -
    have "\<i> * integral {0..y} (\<lambda>x. f s (Complex c x)) + integral {-y..-r} (fr s) -
          cnj (\<i> * integral {0..y} (\<lambda>x. f (cnj s) (Complex c x)) + integral {-y..-r} (fr (cnj s))) =
          -(integral {r..c} (fr s) + err1 s y + err2 s r) -
          cnj (-(integral {r..c} (fr (cnj s)) + err1 (cnj s) y + err2 (cnj s) r))"
      by (subst (1 2) 1) (use yr in auto)
    also have "cnj (-(integral {r..c} (fr (cnj s)) + err1 (cnj s) y + err2 (cnj s) r)) =
               -integral {r..c} (\<lambda>x. cnj (fr (cnj s) x)) - cnj (err1 (cnj s) y) - cnj (err2 (cnj s) r)"
      by (simp add: integral_cnj)
    also have "integral {r..c} (\<lambda>x. cnj (fr (cnj s) x)) = integral {r..c} (fr s)"
      by (intro integral_cong) (use c yr in \<open>auto simp: exp_cnj fr_def  cnj_powr\<close>)
    also have "-(integral {r..c} (fr s) + err1 s y + err2 s r) -
               (-\<dots> - cnj (err1 (cnj s) y) - cnj (err2 (cnj s) r)) =
               cnj (err1 (cnj s) y) + cnj (err2 (cnj s) r) - err2 s r - err1 s y" 
      by simp

    also have "cnj (\<i> * integral {0..y} (\<lambda>x. f (cnj s) (Complex c x)) + integral {-y..-r} (fr (cnj s))) =
               integral {-y..-r} (\<lambda>x. cnj (fr (cnj s) x)) -
               \<i> * integral {0..y} (\<lambda>x. cnj (f (cnj s) (Complex c x)))"
      by (simp add: integral_cnj)
    also have "\<i> * integral {0..y} (\<lambda>x. f s (Complex c x)) + integral {-y..-r} (fr s) - \<dots> =
               \<i> * (integral {0..y} (\<lambda>x. cnj (f (cnj s) (Complex c x))) + integral {0..y} (\<lambda>x. f s (Complex c x))) +
               (integral {-y..-r} (fr s) - integral {-y..-r} (\<lambda>x. cnj (fr (cnj s) x)))"
      by (Groebner_Basis.algebra)
    also have "integral {-y..-r} (fr s) = 
               integral {-y..-r} (\<lambda>t. exp (t - s * complex_of_real (ln (-t)) - \<i> * s * pi))"
      by (intro integral_cong)
         (use yr in \<open>auto simp: fr_def powr_def exp_cnj Ln_of_real' ring_distribs exp_diff
                                exp_minus exp_add field_simps simp flip: of_real_minus\<close>)
    also have "integral {-y..-r} (\<lambda>x. cnj (fr (cnj s) x)) = 
               integral {-y..-r} (\<lambda>t. exp (t - s * complex_of_real (ln (-t)) + \<i> * s * pi))"
      by (intro integral_cong)
         (use yr in \<open>auto simp: fr_def powr_def exp_cnj Ln_of_real' ring_distribs exp_diff
                                exp_minus exp_add field_simps simp flip: of_real_minus\<close>)
    also have "integral {-y..-r} (\<lambda>t. exp (t - s * complex_of_real (ln (-t)) - \<i> * s * pi)) - \<dots> =
               integral {-y..-r} (\<lambda>t. exp (t - s * complex_of_real (ln (-t)) - \<i> * s * pi) -
                                       exp (t - s * complex_of_real (ln (-t)) + \<i> * s * pi))"
      by (rule integral_diff [symmetric]; rule integrable_continuous_interval)
         (use yr c in \<open>auto intro!: continuous_intros simp: fr_def\<close>)
    also have "(\<lambda>t. exp (t - s * complex_of_real (ln (-t)) - \<i> * s * pi) - 
                    exp (t - s * complex_of_real (ln (-t)) + \<i> * s * pi)) =
               (\<lambda>t. exp (t - s * complex_of_real (ln (-t))) * (exp (-\<i> * s * pi) - exp (\<i> * s * pi)))"
      by (simp add: exp_diff exp_add exp_minus field_simps)
    also have "\<dots> = (\<lambda>t. -2 * \<i> * sin (pi * s) * h s t)"
      by (simp add: h_def sin_exp_eq algebra_simps add_divide_distrib diff_divide_distrib)
    also have "integral {-y..-r} \<dots> = -2 * \<i> * sin (pi * s) * integral {-y..-r} (h s)"
      unfolding h_def by (rule integral_mult_right)
    also have "integral {-y..-r} (h s) = integral {r..y} (\<lambda>t. h s (-t))"
      by (subst Henstock_Kurzweil_Integration.integral_reflect_real [symmetric]) auto
    also have "\<dots> = (CLBINT t=r..y. h s (-t))"
      by (intro interval_integral_eq_integral [symmetric] borel_integrable_atLeastAtMost')
         (use yr in \<open>auto simp: h_def complex_eq_iff intro!: continuous_intros\<close>)

    also have "integral {0..y} (\<lambda>x. cnj (f (cnj s) (Complex c x))) =
               integral {-y..0} (\<lambda>x. cnj (f (cnj s) (Complex c (-x))))"
      by (subst Henstock_Kurzweil_Integration.integral_reflect_real [symmetric]) simp_all
    also have "\<dots> = integral {-y..0} (\<lambda>x. f s (Complex c x))"
      using c yr by (intro integral_cong) (auto simp: f_def exp_cnj cnj_powr complex_cnj)
    also have "integral {-y..0} (\<lambda>x. f s (Complex c x)) + integral {0..y} (\<lambda>x. f s (Complex c x)) =
               integral {-y..y} (\<lambda>x. f s (Complex c x))"
      by (intro Henstock_Kurzweil_Integration.integral_combine integrable_continuous_real)
         (use yr in \<open>auto intro!: continuous_intros simp: f_def complex_eq_iff\<close>)

    finally show ?thesis using power2_i
      by (Groebner_Basis.algebra)
  qed


  text \<open>
    The four error terms vanish under diffrent preconditions: some only for
    $\text{Re}(s) > 0$ and some for $\text{Re}(s) < 1$.
  \<close>
  have lim_err1: "(err1 s \<longlongrightarrow> 0) at_top" if s: "Re s > 0" for s
  proof (rule Lim_null_comparison)
    define C1 where "C1 = exp (c + pi * \<bar>Im s\<bar>)"
    define C2 where "C2 = exp (pi * \<bar>Im s\<bar>)"
    show "eventually (\<lambda>T. norm (err1 s T) \<le> C1 * T powr (-Re s) + C2 * exp (-T) * T powr (-Re s) * T) at_top"
      using eventually_gt_at_top[of c]
    proof eventually_elim
      case (elim T)
      define err1_1 where "err1_1 = contour_integral (linepath (Complex c T) (Complex (-T) T)) (g s)"
      define err1_2 where "err1_2 = contour_integral (linepath (Complex (- T) T) (-of_real T)) (g s)"

      have "err1 s T = err1_1 + err1_2"
        unfolding err1_def err1_1_def err1_2_def Cb_def g_def using path_image_Cb[of _ T] elim
        by (subst contour_integral_join)
           (auto intro!: analytic_imp_contour_integrable analytic_intros
                 simp: A_def Cb_def path_image_join)
      also have "norm \<dots> \<le> norm err1_1 + norm err1_2"
        by norm
      also have "err1_1 = -contour_integral (linepath (Complex (-T) T) (Complex c T)) (g s)"
        unfolding err1_1_def using contour_integral_reversepath by fastforce
      also have "norm \<dots> = norm (integral {-T..c} (\<lambda>x. g s (of_real x + of_real T * \<i>)))"
        using elim c by (subst contour_integral_linepath_same_Im) auto
      also have "\<dots> \<le> T powr (-Re s) * exp (\<bar>Im s\<bar> * pi) * (exp c - exp (-T))"
      proof (rule integral_norm_bound_integral')
        fix t assume t: "t \<in> {-T..c}"
        define z where "z = (of_real t + of_real T * \<i>)"
        have "z \<noteq> 0"
          using c elim by (auto simp: complex_eq_iff z_def)
        hence "g s z = f s z" using t elim
          unfolding f_def g_def powr_def
          by (subst Ln'_eq_Ln) (auto simp: z_def exp_diff exp_minus field_simps)
        also have "norm \<dots> = exp t * (norm z) powr (-Re s) * exp (Im s * Arg z)"
          by (simp add: z_def f_def norm_mult norm_powr_complex)
        also have "\<dots> \<le> exp t * T powr (-Re s) * exp (\<bar>Im s\<bar> * pi)"
        proof (intro mult_mono powr_mono2')
          have "T = Im z"
            by (auto simp: z_def)
          also have "\<dots> \<le> norm z"
            using abs_Im_le_cmod[of z] by simp
          finally show "T \<le> norm z" .
        next
          have "Im s * Arg z \<le> \<bar>Im s * Arg z\<bar>"
            by linarith
          also have "\<dots> \<le> \<bar>Im s\<bar> * pi"
            unfolding abs_mult using Arg_bounded[of z] by (intro mult_left_mono) auto
          finally show "exp (Im s * Arg z) \<le> exp (\<bar>Im s\<bar> * pi)"
            by simp
        qed (use s elim c in auto)
        also have "\<dots> = T powr (-Re s) * exp (\<bar>Im s\<bar> * pi) * exp t"
          by (simp add: C1_def algebra_simps)
        finally show "norm (g s z) \<le> T powr (-Re s) * exp (\<bar>Im s\<bar> * pi) * exp t" .
      next
        have "((\<lambda>x. T powr (-Re s) * exp (\<bar>Im s\<bar> * pi) * exp x) has_integral 
                (T powr (-Re s) * exp (\<bar>Im s\<bar> * pi) * exp c -
                 T powr (-Re s) * exp (\<bar>Im s\<bar> * pi) * exp (-T))) {-T..c}" using elim c
          by (intro fundamental_theorem_of_calculus)
              (auto simp flip: has_real_derivative_iff_has_vector_derivative
                    intro!: derivative_eq_intros)
        thus "((\<lambda>x. T powr (-Re s) * exp (\<bar>Im s\<bar> * pi) * exp x) has_integral 
                (T powr (-Re s) * exp (\<bar>Im s\<bar> * pi) * (exp c - exp (-T)))) {-T..c}"
          by (simp add: algebra_simps)
      qed (auto simp: g_def Ln'_def intro!: measurable_completion borel_measurable_if_D)
      also have "\<dots> \<le> C1 * T powr (-Re s)"
        by (simp add: C1_def algebra_simps exp_add)

      also have "norm err1_2 \<le> C2 * exp (-T) * T powr (-Re s) * norm (-of_real T - Complex (-T) T)"
        unfolding err1_2_def
      proof (rule contour_integral_bound_linepath)
        show "g s contour_integrable_on linepath (Complex (- T) T) (-of_real T)" using c elim
          by (auto intro!: analytic_imp_contour_integrable analytic_intros
                   simp: g_def A_def Cb_def path_image_join closed_segment_same_Re)
      next
        fix z assume "z \<in> closed_segment (Complex (-T) T) (-complex_of_real T)"
        then obtain t where t: "t \<in> {0..T}" "z = Complex (-T) t"
          using c elim by (auto simp: closed_segment_same_Re closed_segment_eq_real_ivl complex_eq_iff)
        have "z \<noteq> 0"
          using c elim by (auto simp: complex_eq_iff t(2))
        hence "g s z = f s z" using t elim
          unfolding f_def g_def powr_def
          by (subst Ln'_eq_Ln) (auto simp: t(2) exp_diff exp_minus field_simps)
        also have "norm (f s z) = exp (-T) * (norm z) powr (-Re s) * exp (Im s * Arg z)"
          by (simp add: f_def norm_mult t(2) norm_powr_complex)
        also have "\<dots> \<le> exp (-T) * T powr (-Re s) * exp (\<bar>Im s\<bar> *pi)"
        proof (intro mult_mono powr_mono2')
          from c elim have "T = \<bar>Re z\<bar>"
            by (auto simp: t)
          also have "\<dots> \<le> norm z"
            using abs_Re_le_cmod[of z] by simp
          finally show "T \<le> norm z" .
        next
          have "Im s * Arg z \<le> \<bar>Im s * Arg z\<bar>"
            by linarith
          also have "\<dots> \<le> \<bar>Im s\<bar> * pi"
            unfolding abs_mult using Arg_bounded[of z] by (intro mult_left_mono) auto
          finally show "exp (Im s * Arg z) \<le> exp (\<bar>Im s\<bar> * pi)"
            by simp
        qed (use c elim s in auto)
        finally show "norm (g s z) \<le> C2 * exp (-T) * T powr (-Re s)"
          by (simp add: C2_def algebra_simps)
      qed (auto simp: C2_def)
      also have "norm (-of_real T - Complex (-T) T) = T"
        using elim c by (simp add: cmod_def)
      finally show ?case
        by simp_all
    qed

    show "((\<lambda>T. C1 * T powr (-Re s) + C2 * exp (-T) * T powr (-Re s) * T) \<longlongrightarrow> 0) at_top"
      using s by real_asymp
  qed

  have lim_err2: "(err2 s \<longlongrightarrow> 0) (at_right 0)" if s: "Re s < 1" for s
  proof (rule Lim_null_comparison)
    define C where "C = pi * exp (c + \<bar>Im s\<bar> * pi)"
    have "eventually (\<lambda>r::real. r > 0) (at_right 0)"
         "eventually (\<lambda>r::real. r < c) (at_right 0)"
      using c by real_asymp+
    thus "eventually (\<lambda>r. norm (err2 s r) \<le> C * r powr (1 - Re s)) (at_right 0)"
    proof eventually_elim
      case (elim r)
      have "norm (err2 s r) \<le> exp c * r powr - Re s * exp (\<bar>Im s\<bar> * pi) * r * \<bar>0 - pi\<bar>"
        unfolding err2_def Cs_def
      proof (rule contour_integral_bound_part_circlepath)
        show "g s contour_integrable_on part_circlepath 0 r pi 0"
          using path_image_Cs[of _ r] elim unfolding g_def Cs_def
          by (auto intro!: analytic_imp_contour_integrable analytic_intros simp: A_def)
      next
        show "norm (g s z) \<le> exp c * r powr - Re s * exp (\<bar>Im s\<bar> * pi)" 
          if z: "z \<in> path_image (part_circlepath 0 r pi 0)" for z
        proof -
          have "z \<in> path_image (part_circlepath 0 r 0 pi)"
            using z by (metis reversepath_part_circlepath path_image_reversepath)
          then obtain t where t: "z = rcis r t" "t \<in> {0..pi}"
            by (auto simp: path_image_part_circlepath rcis_def cis_conv_exp)
          have "g s z = f s z" unfolding g_def f_def using t(2) elim
            by (subst Ln'_eq_Ln)
               (auto simp: t(1) exp_diff powr_def exp_minus field_simps sin_ge_zero)
          also have "norm (f s z) = exp (r * cos t) * r powr -Re s * exp (Im s * Arg z)"
            using elim t by (simp add: t f_def norm_mult norm_powr_complex Arg_rcis)
          also have "\<dots> \<le> exp c * r powr -Re s * exp (\<bar>Im s\<bar> * pi)"
          proof (intro mult_mono)
            have "r * cos t \<le> r * 1"
              by (rule mult_left_mono) (use elim in auto)
            also have "\<dots> \<le> c"
              using elim by simp
            finally show "exp (r * cos t) \<le> exp c"
              by simp
          next
            have "Im s * Arg z \<le> \<bar>Im s * Arg z\<bar>"
              by linarith
            also have "\<dots> \<le> \<bar>Im s\<bar> * pi"
              unfolding abs_mult using Arg_bounded[of z] by (intro mult_left_mono) auto
            finally show "exp (Im s * Arg z) \<le> exp (\<bar>Im s\<bar> * pi)"
              by simp
          qed (use elim in auto)
          finally show "norm (g s z) \<le> exp c * r powr (-Re s) * exp (\<bar>Im s\<bar> * pi)" .
        qed
      qed (use elim in auto)
      also have "exp c * r powr (-Re s) * exp (\<bar>Im s\<bar> * pi) * r * \<bar>0 - pi\<bar> = C * r powr (1-Re s)"
        using elim by (auto simp: C_def powr_diff powr_minus field_simps exp_add)
      finally show "norm (err2 s r) \<le> C * r powr (1 - Re s)" .
    qed

    show "((\<lambda>r. C * r powr (1 - Re s)) \<longlongrightarrow> 0) (at_right 0)"
      using s by real_asymp
  qed


  text \<open>
    We now arbitrarily pick some suitable radius (we will soon see that all the values are
    independent of it anyway).
  \<close>
  define r where "r = c / 2"
  have r: "r > 0" "r < c"
    using c by (auto simp: r_def)


  define lhs where "lhs = (\<lambda>s T. integral {-T..T} (\<lambda>t. f s (Complex c t)))"
  define rhs where "rhs = (\<lambda>s r T. 2 * sin (complex_of_real pi * s) * (CLBINT t=r..T. h s (-t)) -
                                 \<i> * (cnj (err1 (cnj s) T) + cnj (err2 (cnj s) r) - 
                                 err2 s r - err1 s T))"
  define RHS where "RHS = (\<lambda>s r. 2 * sin (complex_of_real pi * s) * (CLBINT t:{r..}. h s (- t)) +
                                     \<i> * (err2 s r - cnj (err2 (cnj s) r)))"


  text \<open>
    For $\text{Re}(s) > 0$, we now let $T\to\infty$ and let two of the error terms vanish.
    What we obtain from this is that the vertical integral we are interested in (\<^term>\<open>lhs\<close>)
    converges to a slightly deformed version of the horizontal integrals we want (\<^term>\<open>RHS\<close>). 
    The deformation is the small circle around the origin to avoid the singularity there.
  \<close>
  have lim_lhs: "(lhs s \<longlongrightarrow> RHS s r) at_top"
    if r: "r > 0" "r < c" and s: "Re s > 0" for s :: complex and r :: real
  proof -  
    have "(rhs s r \<longlongrightarrow> 2 * sin (pi * s) * 
            (CLBINT t:{r..}. h s (-t)) - \<i> * (cnj 0 + cnj (err2 (cnj s) r) - err2 s r - 0)) at_top"
      unfolding rhs_def
    proof (intro tendsto_intros lim_err1 lim_err2)
      have "((\<lambda>x. set_lebesgue_integral lborel {r..x} (\<lambda>t. h s (-t))) \<longlongrightarrow>
               set_lebesgue_integral lborel {r..} (\<lambda>t. h s (-t))) at_top"
      proof (rule tendsto_set_lebesgue_integral_at_top)
        show "set_integrable lborel {r..} (\<lambda>t. h s (- t))"
          by (rule integrable) (use r in auto)
      qed auto
      moreover have "eventually (\<lambda>x. set_lebesgue_integral lborel {r..x} (\<lambda>t. h s (-t)) =
                                     (CLBINT t=ereal r..ereal x. h s (-t))) at_top"
        using eventually_ge_at_top[of r] by eventually_elim (simp_all add: interval_integral_Icc)
      ultimately have *: "((\<lambda>x. (CLBINT t=ereal r..ereal x. h s (-t))) \<longlongrightarrow>
                          set_lebesgue_integral lborel {r..} (\<lambda>t. h s (-t))) at_top"
        by (rule Lim_transform_eventually)
      show "((\<lambda>x. CLBINT t=ereal r..ereal x. h s (- t)) \<longlongrightarrow> 
                    CLBINT t:{r..}. h s (- t)) at_top"
        by (rule filterlim_compose[OF *]) real_asymp
    qed (use s in auto)

    hence "(rhs s r \<longlongrightarrow> 2 * sin (pi * s) * (CLBINT t:{r..}. h s (-t)) +
                            \<i> * (err2 s r - cnj (err2 (cnj s) r))) at_top"
      by (simp add: algebra_simps)
    moreover have "eventually (\<lambda>T. lhs s T = rhs s r T) at_top"
    proof -
      have "eventually (\<lambda>T. c + r < T) at_top"
        by real_asymp
      thus ?thesis
      proof eventually_elim
        case (elim T)
        thus ?case using 2[of r T s] r
          by (simp add: lhs_def rhs_def)
      qed
    qed
    ultimately show "(lhs s \<longlongrightarrow> RHS s r) at_top"
      using filterlim_cong unfolding RHS_def by blast
  qed


  text \<open>
    Next, we show that \<^term>\<open>RHS s r\<close> is equal to $2\pi/\Gamma(s)$ for all $s$ with $\text{Re}(s)<1$,
    independently of the radius $r$.
  \<close>
  have RHS_eq: "RHS s r = 2 * pi * rGamma s" if s: "Re s \<in> {0<..<1}" for s :: complex
  proof -
    have "((\<lambda>r. LBINT t. indicator {r..} t * h s (-t)) \<longlongrightarrow> 
            (LBINT t. indicator {0..} t * h s (-t))) (at_right 0)"
    proof (rule tendsto_at_right_sequentially)
      show "0 < (1::real)"
        by simp
    next
      fix l :: "nat \<Rightarrow> real"
      assume l: "l \<longlonglongrightarrow> 0" "\<And>n. l n > 0"
      show "(\<lambda>x. LBINT t. indicator {l x..} t * h s (-t)) \<longlonglongrightarrow> (LBINT t. indicator {0..} t * h s (-t))"
      proof (rule integral_dominated_convergence)
        have "integrable lebesgue (\<lambda>t. norm (indicator {0<..} t * complex_of_real t powr (-s) / of_real (exp t)))"
          by (intro integrable_norm) 
             (use absolutely_integrable_Gamma_integral'[of "1-s"] s
               in \<open>simp_all add: set_integrable_def scaleR_conv_of_real of_real_indicator\<close>)
        hence "integrable lborel (\<lambda>t. norm (indicator {0<..} t * complex_of_real t powr (-s) / of_real (exp t)))"
          by (subst (asm) integrable_completion) auto
        also have "?this \<longleftrightarrow> integrable lborel (\<lambda>t. indicator {0<..} t * norm (h s (-t)))"
          by (intro Bochner_Integration.integrable_cong)
             (auto simp: norm_mult indicator_def norm_divide h_def powr_def field_simps exp_diff exp_minus)
        finally show "integrable lborel (\<lambda>t. indicator {0<..} t * norm (h s (-t)))" .
      next
        show "AE t in lborel. norm (indicator {l n..} t * h s (- t))
                            \<le> indicat_real {0<..} t * cmod (h s (- t))" for n
          using l(2)[of n] by (intro always_eventually) (auto simp: indicator_def)
      next
        have "AE t in lborel. t \<noteq> 0"
          by (metis AE_lborel_singleton)
        thus "AE t in lborel. (\<lambda>n. indicator {l n..} t * h s (-t)) \<longlonglongrightarrow> indicator {0..} t * h s (-t)"
        proof eventually_elim
          case (elim t)
          show ?case
          proof (cases "t > 0")
            case True
            hence "eventually (\<lambda>n. l n < t) at_top"
              using l(1) order_tendsto_iff by blast
            hence "eventually (\<lambda>n. indicator {l n..} t * h s (-t) = 
                                   indicator {0..} t * h s (-t)) sequentially"
              by eventually_elim (use True in auto)
            thus ?thesis
              by (metis tendsto_eventually)
          next
            case False
            hence "indicator {l n..} t * h s (-t) = indicator {0..} t * h s (-t)" for n
              using l(2)[of n] elim by (auto simp: indicator_def)
            thus ?thesis
              by fastforce
          qed
        qed
      qed (auto simp: h_def)
    qed
    hence lim_integral: "((\<lambda>r. CLBINT t:{r..}. h s (- t)) \<longlongrightarrow> CLBINT t:{0..}. h s (-t)) (at_right 0)"
      by (simp add: set_lebesgue_integral_def scaleR_conv_of_real of_real_indicator)
    
    text \<open>
      For $r\to 0$, the integral in \<^term>\<open>RHS s r\<close> becomes the integral over the entire positive
      real line. This integral is also exactly the one from the definition of $\Gamma$. 
    \<close>
    have "filterlim (\<lambda>r. RHS s r) 
            (nhds (2 * sin (pi * s) * (CLBINT t:{0..}. h s (-t)) + \<i> * (0 - cnj 0))) (at_right 0)"
      unfolding RHS_def by (intro tendsto_intros lim_err2 lim_integral) (use s in auto)
    hence "filterlim (\<lambda>r. RHS s r) (nhds (2 * sin (pi * s) * (CLBINT t:{0..}. h s (-t)))) (at_right 0)"
      by simp

    text \<open>
      Moreover, since \<open>lhs s T\<close> is independent of $r$ but also tends to \<open>RHS s r\<close> for $T\to\infty$ 
      for any $r$, we know that the value of \<open>RHS s r\<close> is actually also independent of $r$ (at least
      for sufficiently small $r$).
    \<close>
    moreover have "eventually (\<lambda>r'::real. r' > 0) (at_right 0)" "eventually (\<lambda>r'. r' < c) (at_right 0)"
      using c by real_asymp+
    hence "eventually (\<lambda>r'. RHS s r' = RHS s r) (at_right 0)"
    proof eventually_elim
      case (elim r')
      have "(lhs s \<longlongrightarrow> RHS s r') at_top"
        by (rule lim_lhs) (use elim s in auto)
      moreover have "(lhs s \<longlongrightarrow> RHS s r) at_top"
        by (rule lim_lhs) (use r s in auto)
      ultimately show "RHS s r' = RHS s r"
        using tendsto_unique trivial_limit_at_top_linorder by blast
    qed
    ultimately have "filterlim (\<lambda>r'. RHS s r) 
                       (nhds (2 * sin (pi * s) * (CLBINT t:{0..}. h s (-t)))) (at_right (0::real))"
      by (rule Lim_transform_eventually)
    hence "RHS s r = 2 * sin (pi * s) * (CLBINT t:{0..}. h s (-t))"
      by (simp add: tendsto_const_iff)

    text \<open>
      All that remains now is some massaging of terms and using the definition of the Gamma function
      as well as the reflection identity.
    \<close>
    also have "(CLBINT t:{0..}. h s (-t)) = (CLBINT t:{0<..}. of_real t powr (-s) / of_real (exp t))"
      unfolding set_lebesgue_integral_def
    proof (intro integral_cong_AE)
      have "AE t in lborel. t \<noteq> (0::real)"
        using AE_lborel_singleton by blast
      thus "AE t in lborel. indicator {0..} t *\<^sub>R h s (-t) = 
                            indicator {0<..} t *\<^sub>R (of_real t powr -s / of_real (exp t))"
        by eventually_elim 
           (auto simp: powr_def h_def exp_add exp_diff exp_minus field_simps 
                       Ln_of_real exp_of_real indicator_def)
    qed (auto simp: h_def)
    also have "\<dots> = integral {0<..} (\<lambda>t. of_real t powr (-s) / of_real (exp t))"
      by (rule set_borel_integral_eq_integral(2))
         (use absolutely_integrable_Gamma_integral'[of "1-s"] s
           in \<open>simp_all add: set_integrable_def integrable_completion\<close>)
    also have "\<dots> = Gamma (1-s)"
      using Gamma_integral_complex'[of "1-s"] s by (simp add: has_integral_iff)
    also have "2 * sin (pi * s) * Gamma (1 - s) = 2 * pi * rGamma s * (Gamma (1 - s) * rGamma (1 - s))"
      using rGamma_reflection_complex[of s] by (simp add: field_simps)
    also have "1 - s \<notin> \<int>\<^sub>\<le>\<^sub>0"
      using s by (auto elim!: nonpos_Ints_cases simp: complex_eq_iff)
    hence "Gamma (1 - s) * rGamma (1 - s) = 1"
      by (simp add: rGamma_inverse_Gamma field_simps Gamma_eq_zero_iff)
    finally show "RHS s r = 2 * pi * rGamma s"
      by simp
  qed


  text \<open>
    Also, for any $r > 0$, the term \<^term>\<open>RHS s r\<close> defines a holomorphic function on the half-plane
    with $\text{Re}(s) > 0$.
  \<close>
  have RHS_holo: "(\<lambda>s. RHS s r) holomorphic_on {s. Re s > 0}"
  proof -
    have "(\<lambda>z. err2 z r) = (\<lambda>z. -contour_integral (part_circlepath 0 r 0 pi) (g z))"
      unfolding err2_def Cs_def by (metis contour_integral_part_circlepath_reverse)
    also have "\<dots> = (\<lambda>z. -integral {0..pi} (\<lambda>t. \<i> * g z (rcis r t) * rcis r t))"
      by (subst contour_integral_part_circlepath_eq) (simp_all add: mult_ac rcis_def)
    finally have err2_eq: "err2 z r = -integral (cbox 0 pi) (\<lambda>t. \<i> * g z (rcis r t) * rcis r t)" for z
      by (auto simp: fun_eq_iff)

    define err2' where 
      "err2' = (\<lambda>a b s. integral {a..b} (\<lambda>t. \<i> * exp (rcis r t - s * Complex (ln r) t) * rcis r t))"

    have err2'_holomorphic: "err2' a b holomorphic_on {s. Re s > 0}" for a b
    proof -
      define l where "l = (\<lambda>s t. \<i> * exp (rcis r t + (1 - s) * Complex (ln r) t))"
      define l' where "l' = (\<lambda>s t. -\<i> * exp (rcis r t + (1 - s) * Complex (ln r) t) * Complex (ln r) t)"
      have "(\<lambda>s. integral (cbox a b) (l s)) holomorphic_on {s. Re s > 0}"
      proof (rule leibniz_rule_holomorphic)
        show "((\<lambda>s. l s t) has_field_derivative l' s t) (at s within {s. Re s > 0})"
          if s: "s \<in> {s. Re s > 0}" and t: "t \<in> cbox a b" for s t
          unfolding l_def l'_def by (auto intro!: derivative_eq_intros)
      next
        show "l s integrable_on cbox a b" if "s \<in> {s. Re s > 0}" for s
          unfolding l_def by (intro integrable_continuous continuous_intros)
      next
        show "continuous_on ({s. 0 < Re s} \<times> cbox a b) (\<lambda>(s, t). l' s t)"
          unfolding l'_def case_prod_unfold by (auto intro!: continuous_intros)
      qed (auto simp: convex_halfspace_Re_gt)
      also have "(\<lambda>s. integral (cbox a b) (l s)) = err2' a b"
        unfolding err2'_def cbox_interval using r
        by (intro ext integral_cong)
           (auto simp: exp_diff l_def exp_add ring_distribs rcis_def cis_conv_exp Complex_eq exp_of_real)
      finally show ?thesis .
    qed

    have "err2 s r = -err2' 0 pi s" for s
    proof -
      have "err2 s r = -integral {0..pi} (\<lambda>x. \<i> * exp (rcis r x - s * Ln' (rcis r x)) * rcis r x)"
        unfolding err2_eq by (simp add: integral_cnj g_def exp_cnj rcis_def cis_cnj)
      also have "integral {0..pi} (\<lambda>t. \<i> * exp (rcis r t - s * Ln' (rcis r t)) * rcis r t) = 
                 integral {0..pi} (\<lambda>t. \<i> * exp (rcis r t - s * Complex (ln r) t) * rcis r t)"
      proof (intro integral_cong)
        fix t assume t: "t \<in> {0..pi}"
        have "Ln' (rcis r t) = Ln (rcis r (t - pi / 2)) + \<i> * pi / 2"
          unfolding Ln'_def by (simp add: rcis_def mult_ac flip: cis_divide)
        also have "\<dots> = Complex (ln r) t"
          by (subst Ln_rcis) (use r t pi_gt_zero in \<open>auto simp del: pi_gt_zero simp: complex_eq_iff\<close>)
        finally show "\<i> * exp (rcis r t - s * Ln' (rcis r t)) * rcis r t =
                      \<i> * exp (rcis r t - s * Complex (ln r) t) * rcis r t" by simp
      qed
      finally show ?thesis
        by (simp add: err2'_def)
    qed
    hence err2_holomorphic1: "(\<lambda>s. err2 s r) holomorphic_on {s. Re s > 0}"
      using holomorphic_on_minus[OF err2'_holomorphic[of 0 pi]] by simp

    have "cnj (err2 (cnj s) r) = err2' (-pi) 0 s" for s
    proof -
      have "cnj (err2 (cnj s) r) =
            integral {0..pi} (\<lambda>x. \<i> * exp (rcis r (-x) - s * cnj (Ln' (rcis r x))) * (rcis r (-x)))"
        unfolding err2_eq by (simp add: integral_cnj g_def exp_cnj rcis_def cis_cnj)
      also have "\<dots> = integral {0..pi} (\<lambda>t. \<i> * exp (rcis r (-t) - s * Complex (ln r) (-t)) * rcis r (-t))"
      proof (intro integral_cong)
        fix t assume t: "t \<in> {0..pi}"
        have "Ln' (rcis r t) = Ln (rcis r (t - pi / 2)) + \<i> * pi / 2"
          unfolding Ln'_def by (simp add: rcis_def mult_ac flip: cis_divide)
        also have "\<dots> = Complex (ln r) t"
          by (subst Ln_rcis) (use r t pi_gt_zero in \<open>auto simp del: pi_gt_zero simp: complex_eq_iff\<close>)
        also have "cnj \<dots> = Complex (ln r) (-t)"
          by (simp add: complex_eq_iff)
        finally show "\<i> * exp (rcis r (-t) - s * cnj (Ln' (rcis r t))) * rcis r (-t) =
                      \<i> * exp (rcis r (-t) - s * Complex (ln r) (-t)) * rcis r (-t)" by simp
      qed
      also have "\<dots> = integral {-pi..0} (\<lambda>t. \<i> * exp (rcis r t - s * Complex (ln r) t) * rcis r t)"
        by (subst Henstock_Kurzweil_Integration.integral_reflect_real [symmetric]) simp_all
      finally show ?thesis
        by (simp add: err2'_def)
    qed
    hence err2_holomorphic2: "(\<lambda>s. cnj (err2 (cnj s) r)) holomorphic_on {s. Re s > 0}"
      using err2'_holomorphic[of "-pi" 0] by simp

    have holo_integral: "(\<lambda>z. CLBINT t:{r..}. h z (-t)) holomorphic_on UNIV"
    proof -
      have "(\<lambda>z. Gamma_incu (1-z) (of_real r)) holomorphic_on UNIV"
        using r by (auto intro!: analytic_imp_holomorphic analytic_intros)
      also have "(\<lambda>z. Gamma_incu (1-z) (of_real r)) = (\<lambda>z. LBINT t:{r..}. h z (-t))"
      proof
        fix z :: complex
        have "Gamma_incu (1-z) (of_real r) = integral {r..} (\<lambda>t. h z (-t))"
          using has_integral_Gamma_incu_complex_of_real'[of r "1-z"] r
          by (simp add: h_def minus_diff_commute has_integral_iff)
        also have "\<dots> = (LBINT t:{r..}. h z (-t))"
          by (intro set_borel_integral_eq_integral(2) [symmetric] integrable r)
        finally show "Gamma_incu (1 - z) (complex_of_real r) = (LBINT t:{r..}. h z (- t))" .
      qed
      finally show ?thesis .
    qed
    show "(\<lambda>s. RHS s r) holomorphic_on {s. Re s > 0}" unfolding RHS_def
      by (intro holomorphic_intros err2_holomorphic1 err2_holomorphic2
                holomorphic_on_subset[OF holo_integral]) auto
  qed

  text \<open>
    Thus, we can extend the validity of our equation to the half-plane $\text{Re}(s)>0$ 
    by analytic continuation.
  \<close>
  have RHS_eq': "RHS s r = 2 * pi * rGamma s"
  proof (rule analytic_continuation_open[where f = "\<lambda>s. RHS s r"])
    have "Re (1/2) \<in> {0<..<1}"
      by simp
    thus "{s. Re s \<in> {0<..<1}} \<noteq> {}"
      by blast
  next
    have "open ({s. Re s > 0} \<inter> {s. Re s < 1})"
      by (intro open_Int open_halfspace_Re_lt open_halfspace_Re_gt)
    also have "\<dots> = {s. Re s \<in> {0<..<1}}"
      by auto
    finally show "open {s. Re s \<in> {0<..<1}}" .
  next
    show "(\<lambda>a. complex_of_real (2 * pi) * rGamma a) holomorphic_on {s. Re s > 0}"
      by (intro holomorphic_intros)
  next
    show "RHS s r = complex_of_real (2 * pi) * rGamma s" if s: "s \<in> {s. Re s \<in> {0<..<1}}" for s
      using RHS_eq[of s] s r by simp
  qed (use s RHS_holo in \<open>auto simp: open_halfspace_Re_gt\<close>)

  show ?thesis
    using lim_lhs[of r s] RHS_eq' r s by (simp add: RHS_def lhs_def f_def o_def)
qed

text \<open>
  If $\text{Re}(s) > 1$, the integral exists not only as an improper/Cauchy principal value
  style integral, but as a Lebesgue integral.
\<close>
corollary rGamma_hankel:
  assumes c: "c > 0" and s: "Re s > 1"
  shows   "(((\<lambda>z. exp z * z powr (-s)) \<circ> (\<lambda>t. Complex c t)) 
             has_integral (2 * of_real pi * rGamma s)) UNIV"
proof -
  have "((\<lambda>T. integral {-T..T} ((\<lambda>z. exp z * z powr - s) \<circ> Complex c)) \<longlongrightarrow>
           2 * of_real pi * rGamma s) at_top"
    by (rule rGamma_hankel_strong) (use assms in auto)
  also have "(\<lambda>T. integral {-T..T} ((\<lambda>z. exp z * z powr - s) \<circ> Complex c)) =
             (\<lambda>T. set_lebesgue_integral lebesgue {-T..T} ((\<lambda>z. exp z * z powr - s) \<circ> Complex c))"
    by (intro ext set_lebesgue_integral_eq_integral(2) [symmetric] 
                 absolutely_integrable_continuous_real)
       (use c s in \<open>auto simp: complex_eq_iff intro!: continuous_intros\<close>)
  finally have "((\<lambda>T. set_lebesgue_integral lebesgue {-T..T} ((\<lambda>z. exp z * z powr - s) \<circ> Complex c)) \<longlongrightarrow>
                   2 * of_real pi * rGamma s) at_top" .
  hence "((\<lambda>T. set_lebesgue_integral lebesgue {-real T..real T} ((\<lambda>z. exp z * z powr - s) \<circ> Complex c)) \<longlongrightarrow>
                 2 * of_real pi * rGamma s) at_top"
    by (rule filterlim_compose) (rule filterlim_real_sequentially)

  moreover have 
    "(\<lambda>T. set_lebesgue_integral lebesgue {-T..T} ((\<lambda>z. exp z * z powr - s) \<circ> Complex c)) \<longlonglongrightarrow>
       lebesgue_integral lebesgue ((\<lambda>z. exp z * z powr - s) \<circ> Complex c)"
    unfolding set_lebesgue_integral_def
  proof (intro integral_dominated_convergence always_eventually allI)
    show "integrable lebesgue (\<lambda>t. norm (exp (Complex c t) * Complex c t powr -s))"
      using rGamma_hankel_integrable[of c s] c s
      by (intro integrable_norm) (simp_all add: set_integrable_def)
  next
    fix t :: real
    have "eventually (\<lambda>T. real T \<ge> \<bar>t\<bar>) at_top"
      by real_asymp
    hence "eventually (\<lambda>T. indicat_real {-real T..real T} t *\<^sub>R ((\<lambda>z. exp z * z powr - s) \<circ> Complex c) t =
                           ((\<lambda>z. exp z * z powr - s) \<circ> Complex c) t) at_top"
      by eventually_elim (auto simp: indicator_def)
    thus "(\<lambda>T. indicat_real {-real T..real T} t *\<^sub>R ((\<lambda>z. exp z * z powr - s) \<circ> Complex c) t)
             \<longlonglongrightarrow> ((\<lambda>z. exp z * z powr - s) \<circ> Complex c) t"
      by (rule tendsto_eventually)
  qed (auto intro!: measurable_completion simp: indicator_def o_def Complex_eq)

  ultimately have "2 * of_real pi * rGamma s = 
                     lebesgue_integral lebesgue ((\<lambda>z. exp z * z powr - s) \<circ> Complex c)"
    using LIMSEQ_unique by blast
  also have "\<dots> = integral UNIV ((\<lambda>z. exp z * z powr - s) \<circ> Complex c)"
    using rGamma_hankel_integrable[OF c s]
    by (intro integral_lebesgue [symmetric]) (simp_all add: set_integrable_def)
  moreover have "((\<lambda>z. exp z * z powr - s) \<circ> Complex c) integrable_on UNIV"
    using rGamma_hankel_integrable[OF c s] absolutely_integrable_on_def by blast
  ultimately show ?thesis
    by (simp add: has_integral_iff)
qed


subsection \<open>The integral for the Bessel function\<close>

text \<open>
  We now show the main result of this section: A Hankel-style contour-integral representation for
  the modified Bessel function of the first kind $I(\nu, s)$, valid for all $s$ and $\nu$ with
  $\text{Re}(\nu) > 0$.

  The integral is of the form $\int_{c-i\infty}^{c+i\infty}$ for any real $c > 0$ and converges
  absolutely. The proof is modelled after Proposition~2.4 by Kong and Teo~\<^cite>\<open>kong_teo\<close> and
  works by taking the similar integral formula for $1/\Gamma(s)$, summing over it, and 
  exchanging the order of summation and integration.

  The proof is fairly quick since the main work was already done in other lemmas. The main bit of
  work that we still have to do here is to justify exchanging summation and integration. 
  This is done by showing that the integrals over the absolute value exist for every summand, 
  and then the sum over these integrals also exists.

  The integrals over the summand can be brought into the form
  \[\int_{-\infty}^\infty (c^2 + t^2)^a\,\text{d}t\]
  for some suitable $a > \frac{1}{2}$, which we showed earlier to have a closed form in terms
  of the Beta function.
\<close>
theorem
  fixes c :: real and s v :: complex
  assumes v: "Re v > 0" and c: "c > 0"
  shows   has_integral_Bessel_I_complex:
            "(((\<lambda>z. 1 / (2*pi) * (s/2) powr v * exp (z + s\<^sup>2/(4*z)) / z powr (v+1)) \<circ> Complex c)
                 has_integral Bessel_I v s) UNIV"
    and   absolutely_integrable_Bessel_I_complex:
            "((\<lambda>z. 1 / (2*pi) * (s/2) powr v * exp (z + s\<^sup>2/(4*z)) / z powr (v+1)) \<circ> Complex c)
               absolutely_integrable_on UNIV"
proof -
  from v have v': "v \<notin> \<int>\<^sub>\<le>\<^sub>0"
    by (auto elim!: nonpos_Ints_cases)
  define LINTL :: "(real \<Rightarrow> complex) \<Rightarrow> complex" ("\<integral>")
    where "LINTL = lebesgue_integral lebesgue"

  have 1: "integrable lebesgue (\<lambda>x. (s/2)^(2*j) / fact j * exp (Complex c x) * 
                                       Complex c x powr - (v + of_nat j + 1))" for j
  proof -
    have "integrable lebesgue (\<lambda>x. (s/2)^(2*j) / fact j *
              (exp (Complex c x) * Complex c x powr - (v + of_nat j + 1)))"
      using rGamma_hankel_integrable[of c "v + of_nat j + 1"] c v
      by (intro integrable_mult_right) (simp add: set_integrable_def)
    thus ?thesis
      by (simp add: algebra_simps)
  qed

  have 2: "summable (\<lambda>j. norm ((s/2)^(2*j) / fact j * exp (Complex c t) * 
                        Complex c t powr -(v + of_nat j + 1)))" for t :: real
  proof -
    define z where "z = Complex c t"
    define C where "C = exp c * exp (Im v * Arg z) * norm z powr (-Re v-1)"
    have "summable (\<lambda>j. C * (inverse (fact j) * (norm s ^ 2 / (4 * norm z)) ^ j))"
      by (intro summable_mult summable_exp)
    also have "\<dots> = (\<lambda>j. norm ((s/2)^(2*j) / fact j * exp (Complex c t) * 
                          Complex c t powr -(v + of_nat j + 1)))"
      by (intro ext) 
         (simp_all add: norm_mult norm_divide norm_power power_mult norm_powr_complex z_def 
                        powr_diff powr_minus divide_simps exp_minus powr_add C_def powr_realpow)
    finally show "summable \<dots>" .
  qed

  have 3: "summable (\<lambda>j. LINT t|lebesgue. norm ((s/2)^(2*j) / fact j * 
                       exp (Complex c t) * Complex c t powr - (v + of_nat j + 1)))"
  proof -
    define C where "C = exp c * (Beta (1 / 2) (Re v / 2) * exp (\<bar>Im v\<bar> * pi)) * c powr (-Re v)"
    show ?thesis
    proof (rule summable_comparison_test')
      fix j :: nat
      assume j: "j \<ge> 0"
      show "norm (LINT t|lebesgue. norm ((s/2)^(2*j) / fact j * 
                      exp (Complex c t) * Complex c t powr - (v + of_nat j + 1))) \<le>
              C * (inverse (fact j) * (norm s ^ 2 / (4 * c)) ^ j)"
      proof -
        define e where "e = (Re v + real j + 1)/2"
        define I where "I = c powr (1-2*e) / 2 * Beta (1/2) (e - 1/2)"
  
        have integrable': "integrable lebesgue (\<lambda>t. (c\<^sup>2 + t\<^sup>2) powr -e)"
         and integral': "lebesgue_integral lebesgue (\<lambda>t. (c\<^sup>2 + t\<^sup>2) powr -e) = 2 * I"
         using Bessel_I_aux_integral2[of c e] assms by (simp_all add: e_def I_def)

       have "norm (LINT t|lebesgue. norm ((s/2)^(2*j) / fact j * exp (Complex c t) * 
                                      Complex c t powr -(v + of_nat j + 1))) =
              (LINT t|lebesgue. norm ((s/2)^(2*j) / fact j * exp (Complex c t) * 
                                  Complex c t powr -(v + of_nat j + 1)))"
          unfolding real_norm_def
          by (intro abs_of_nonneg Bochner_Integration.integral_nonneg) auto
        also have "\<dots> = exp c * (norm s / 2) ^ (2 * j) / fact j * 
                          (LINT t|lebesgue. norm (Complex c t) powr (-Re v - real j - 1) * 
                                            exp (Im v * Arg (Complex c t)))"
          by (simp add: norm_power norm_mult norm_divide norm_powr_complex)
        also have "(LINT t|lebesgue. norm (Complex c t) powr (-Re v - real j - 1) * 
                                       exp (Im v * Arg (Complex c t))) =
                   (LINT t|lebesgue. (c\<^sup>2 + t\<^sup>2) powr (-e) * exp (Im v * Arg (Complex c t)))"
          by (intro Bochner_Integration.integral_cong)
             (auto simp: cmod_def powr_powr e_def add_divide_distrib diff_divide_distrib
                    simp flip: powr_half_sqrt)
        also have "\<dots> \<le> (LINT t|lebesgue. (c\<^sup>2 + t\<^sup>2) powr (-e) * exp (\<bar>Im v\<bar> * pi))"
        proof (rule integral_mono')
          show "integrable lebesgue (\<lambda>x. (c\<^sup>2 + x\<^sup>2) powr -e * exp (\<bar>Im v\<bar> * pi))"
            using integrable' unfolding set_integrable_def by (intro integrable_mult_left)
          show "(c\<^sup>2 + t\<^sup>2) powr -e * exp (Im v * Arg (Complex c t)) \<le> 
                  (c\<^sup>2 + t\<^sup>2) powr -e * exp (\<bar>Im v\<bar> * pi)" for t
          proof -
            have "Im v * Arg (Complex c t) \<le> \<bar>Im v * Arg (Complex c t)\<bar>"
              by linarith
            also have "\<dots> \<le> \<bar>Im v\<bar> * pi"
              unfolding abs_mult using Arg_bounded[of "Complex c t"] by (intro mult_left_mono) auto
            finally show ?thesis
              by (intro mult_mono) auto
          qed
        qed auto
        also have "\<dots> = exp (\<bar>Im v\<bar> * pi) * (LINT t|lebesgue. (c\<^sup>2 + t\<^sup>2) powr (-e))"
          by simp
        also have "\<dots> = 2 * I * exp (\<bar>Im v\<bar> * pi)"
          by (subst integral') simp
        also have "I \<le> Beta (1 / 2) (Re v / 2) / 2 * c powr (1 - 2 * e)"
        proof -
          have "I = Beta (1 / 2) (e - 1 / 2) / 2 * c powr (1 - 2 * e)"
            by (simp add: I_def mult_ac)
          also have "Beta (1 / 2) (e - 1 / 2) \<le> Beta (1 / 2) (Re v / 2)"
            by (rule Beta_real_mono) (use v in \<open>simp_all add: e_def add_divide_distrib\<close>)
          finally show ?thesis
            using c by simp
        qed
        also have "exp c * (cmod s / 2) ^ (2 * j) / fact j * 
                     (2 * (Beta (1 / 2) (Re v / 2) / 2 * c powr (1 - 2 * e)) * exp (\<bar>Im v\<bar> * pi)) =
                   C * (inverse (fact j) * ((cmod s)\<^sup>2 / (4 * c)) ^ j)" using c
          by (simp add: C_def divide_simps e_def powr_diff powr_minus powr_realpow power_mult diff_divide_distrib)
        finally show ?thesis
          by (simp add: mult_left_mono mult_right_mono divide_right_mono)
      qed
    next
      show "summable (\<lambda>j. C * (inverse (fact j) * (norm s ^ 2 / (4 * c)) ^ j))"
        by (intro summable_mult summable_exp)
    qed
  qed

  have sum_eq:
     "(\<lambda>t. \<Sum>j. (s/2)^(2*j) / fact j * exp (Complex c t) * Complex c t powr -(v + of_nat j + 1)) =
      (\<lambda>z. exp (z + s\<^sup>2/(4*z)) * z powr -(v+1)) \<circ> (\<lambda>t. Complex c t)"
    (is "?lhs = ?rhs")
  proof
    fix t :: real
    define z where "z = Complex c t"
    have "(\<lambda>j. exp z * z powr -(v+1) * ((s\<^sup>2/(4 * z))^j /\<^sub>R fact j)) sums
            ((exp z * z powr -(v+1)) * exp (s\<^sup>2/(4 * z)))"
      by (intro sums_mult exp_converges)
    also have "(exp z * z powr -(v+1)) * exp (s\<^sup>2/(4*z)) = exp (z + s\<^sup>2/(4*z)) * z powr -(v+1)"
      by (simp add: exp_add field_simps)
    also have "(\<lambda>j. exp z * z powr -(v+1) * ((s\<^sup>2/(4 * z))^j /\<^sub>R fact j)) = 
               (\<lambda>j. (s/2)^(2*j) / fact j * exp z * z powr -(v + of_nat j + 1))"
      apply (rule ext)
      apply (simp add: powr_diff powr_minus power_divide power_mult powr_nat scaleR_conv_of_real)
      apply (simp add: field_simps)?
      done
    finally show "?lhs t = ?rhs t"
      by (simp add: sums_iff z_def)
  qed


  have "integrable lebesgue
          (\<lambda>t. \<Sum>j. (s/2)^(2*j) / fact j * exp (Complex c t) * Complex c t powr -(v + of_nat j + 1))"
    by (intro integrable_suminf always_eventually allI 1 2 3)
  hence "integrable lebesgue ((\<lambda>z. exp (z + s\<^sup>2 / (4 * z)) * z powr - (v + 1)) \<circ> Complex c)"
    unfolding sum_eq .
  hence "integrable lebesgue ((\<lambda>z. ((s/2) powr v / (2*pi)) *
                                 (exp (z + s\<^sup>2 / (4 * z)) * z powr - (v + 1))) \<circ> Complex c)"
    unfolding o_def by (intro integrable_mult_right)
  thus integrable:
     "((\<lambda>z. 1 / (2*pi) * (s/2) powr v * exp (z + s\<^sup>2 / (4 * z)) / z powr (v + 1))) \<circ> Complex c
        absolutely_integrable_on UNIV"
    by (simp add: o_def set_integrable_def powr_minus powr_diff powr_add field_simps)


  have "(\<lambda>j. \<integral>((\<lambda>z. (s/2)^(2*j) / fact j * exp z * z powr -(v + of_nat j + 1)) \<circ> Complex c)) sums
          \<integral>(\<lambda>t. \<Sum>j. (s/2)^(2*j) / fact j * exp (Complex c t) * Complex c t powr -(v + of_nat j + 1))"
    unfolding LINTL_def o_def by (intro sums_integral always_eventually allI 1 2 3)
  also have "(\<lambda>j. \<integral> ((\<lambda>z. (s/2)^(2*j) / fact j * exp z * z powr -(v + of_nat j + 1)) \<circ> Complex c)) =
             (\<lambda>j. (s/2)^(2*j) / fact j * 2 * pi * rGamma (v + of_nat j + 1))" (is "?lhs = ?rhs")
  proof
    fix j :: nat
    have "\<integral> ((\<lambda>z. (s/2)^(2*j) / fact j * exp z * z powr -(v + of_nat j + 1)) \<circ> Complex c) =
           (s/2)^(2*j) / fact j * \<integral> ((\<lambda>z. exp z * z powr -(v + of_nat j + 1)) \<circ> Complex c)"
      unfolding o_def LINTL_def
      by (subst integral_mult_right_zero [symmetric], rule Bochner_Integration.integral_cong) simp_all
    also have "\<integral> ((\<lambda>z. exp z * z powr -(v + of_nat j + 1)) \<circ> Complex c) =
               integral UNIV ((\<lambda>z. exp z * z powr -(v + of_nat j + 1)) \<circ> Complex c)" unfolding LINTL_def
      by (rule integral_lebesgue [symmetric])
         (use rGamma_hankel_integrable[of c "v + of_nat j + 1"] c v in \<open>simp_all add: set_integrable_def\<close>)
    also have "\<dots> = 2 * pi  * rGamma (v + of_nat j + 1)"
      using rGamma_hankel[of c "v + of_nat j + 1"] c v
      by (simp add: has_integral_iff field_simps)
    finally show "?lhs j = ?rhs j" by (simp add: o_def)
  qed
  also note sum_eq
  finally have "(\<lambda>j. ((s/2) powr v / (2*pi)) * 
                       ((s/2)^(2*j) / fact j * 2 * of_real pi * rGamma (v + of_nat j + 1))) sums
                  (((s/2) powr v / (2*pi)) * (\<integral> ((\<lambda>z. exp (z + s\<^sup>2/(4*z)) * z powr -(v+1)) \<circ> Complex c)))"
    by (intro sums_mult)

  also have "(\<lambda>j. ((s/2) powr v / (2*pi)) * ((s/2)^(2*j) / fact j * 2 * of_real pi * rGamma (v + of_nat j + 1))) =
             (\<lambda>j. (s/2) powr (v + 2 * of_nat j) * rGamma (v + of_nat j + 1) / fact j)"
    by (intro ext; cases "s = 0") (auto simp: powr_add simp flip: powr_nat')
  finally have "(\<lambda>j. (s/2) powr (v + 2 * of_nat j) * rGamma (v + of_nat j + 1) / fact j) sums
                  (((s/2) powr v / (2 * pi)) * (\<integral> ((\<lambda>z. exp (z + s\<^sup>2 / (4 * z)) * z powr - (v + 1)) \<circ> Complex c)))" .
  also have "((s/2) powr v / (2 * pi)) * \<integral> ((\<lambda>z. exp (z + s\<^sup>2 / (4 * z)) * z powr - (v + 1)) \<circ> Complex c) =
             (\<integral> ((\<lambda>z. 1 / (2 * pi) * (s/2) powr v * exp (z + s\<^sup>2 / (4 * z)) / z powr (v+1)) \<circ> Complex c))"
    unfolding LINTL_def
    by (subst integral_mult_right_zero [symmetric], rule Bochner_Integration.integral_cong) 
       (simp_all add: o_def powr_diff powr_add powr_minus field_simps)
  finally have "(\<lambda>j. (s/2) powr (v + 2 * of_nat j) * rGamma (v + of_nat j + 1) / fact j) sums
                  (\<integral> ((\<lambda>z. 1 / (2 * pi) * (s/2) powr v * exp (z + s\<^sup>2/(4*z)) / z powr (v+1)) \<circ> Complex c))" .

  moreover have "(\<lambda>j. (s/2) powr (v + 2 * of_nat j) * rGamma (v + of_nat j + 1) / fact j) sums
                   Bessel_I v s"
  proof -
    have "(\<lambda>j. (s/2) powr' (v + 2 * of_nat j) * rGamma (v + of_nat j + 1) / fact j) sums
                  Bessel_I v s"
      using sums_Bessel_I_complex[of s v] v' by (simp add: rGamma_inverse_Gamma field_simps)
    also have "(\<lambda>j. (s/2) powr' (v + 2 * of_nat j)) = (\<lambda>j. (s/2) powr (v + 2 * of_nat j))"
      (is "?lhs = ?rhs")
    proof
      fix j :: nat
      from v' have "v + 2 * complex_of_nat j \<noteq> 0"
        by (metis v' add.commute left_add_twice plus_of_nat_eq_0_imp plus_of_nat_notin_nonpos_Ints)
      thus "?lhs j = ?rhs j"
        by (cases "s = 0") (auto simp: powr'_complex powr'_0_left_if)
    qed
    finally show ?thesis .
  qed
  ultimately have eq: 
    "Bessel_I v s = 
       (\<integral> ((\<lambda>z. 1 / (2 * pi) * (s/2) powr v * exp (z + s\<^sup>2/(4*z)) / z powr (v+1)) \<circ> Complex c))"
    using sums_unique2 by blast
  also have "\<dots> = integral UNIV ((\<lambda>z. 1 / (2 * pi) * (s/2) powr v * 
                    exp (z + s\<^sup>2/(4*z)) / z powr (v+1)) \<circ> Complex c)"
    unfolding LINTL_def using integrable unfolding set_integrable_def
    by (intro integral_lebesgue [symmetric]) simp
  finally show "(((\<lambda>z. 1 / (2*pi) * (s/2) powr v * exp (z + s\<^sup>2/(4*z)) / z powr (v+1)) \<circ> Complex c)
                  has_integral Bessel_I v s) UNIV"
    using set_lebesgue_integral_eq_integral(1)[OF integrable] assms
    by (simp add: has_integral_iff)
qed

lemma has_integral_Bessel_I_complex':
  fixes x :: complex and c :: real and v :: complex and f :: "complex \<Rightarrow> complex"
  defines "f \<equiv> (\<lambda>t. exp (t + x\<^sup>2 / t) / t powr v)"
  assumes c: "c > 0" and v: "Re v > 1" and x: "x \<noteq> 0"
  shows   "((f \<circ> (\<lambda>t. Complex c t)) has_integral 
             (2 * pi * Bessel_I (v-1) (2*x)) / (x powr (v-1))) UNIV"
proof -
  define a where "a = 2 * pi / (x powr (v - 1))"
  define g where "g = (\<lambda>t. (1 / (2 * pi)) * x powr (v - 1) * exp (t + x\<^sup>2 / t) / t powr v) \<circ> (\<lambda>t. Complex c t)"
  have "(g has_integral Bessel_I (v - 1) (2 * x)) UNIV"
    using has_integral_Bessel_I_complex[of "v-1" c "2*x"] assms unfolding g_def by (simp add: o_def)
  hence "((\<lambda>t. a * g t) has_integral (a * Bessel_I (v - 1) (2 * x))) UNIV"
    by (rule has_integral_mult_right)
  also have "(\<lambda>t. a * g t) = f \<circ> (\<lambda>t. Complex c t)"
    using x by (auto simp: a_def g_def f_def fun_eq_iff)
  finally show "((f \<circ> (\<lambda>t. Complex c t)) has_integral 
                  (2 * pi * Bessel_I (v - 1) (2 * x)) / (x powr (v - 1))) UNIV" 
    by (simp add: a_def o_def)
qed

lemma absolutely_integrable_Bessel_I_complex':
  fixes c :: real and s v :: complex
  assumes v: "Re v > 1" and c: "c > 0"
  shows   "((\<lambda>z. exp (z + s/z) / z powr v) \<circ> Complex c) absolutely_integrable_on UNIV"
proof (cases "s = 0")
  case [simp]: False
  define x where "x = csqrt s"
  define C where "C = 1 / (2*pi) * (2 * csqrt s / 2) powr (v-1)"
  have [simp]: "C \<noteq> 0"
    by (simp add: C_def)
  have "(\<lambda>z. inverse C * ((\<lambda>z. C * exp (z + (2 * csqrt s)\<^sup>2/(4*z)) / z powr (v-1+1)) \<circ> Complex c) z)
          absolutely_integrable_on UNIV" unfolding C_def 
    by (intro set_integrable_mult_right absolutely_integrable_Bessel_I_complex) (use v c in auto)
  also have "(\<lambda>z. inverse C * ((\<lambda>z. C * exp (z + (2 * csqrt s)\<^sup>2/(4*z)) / z powr (v-1+1)) \<circ> Complex c) z) =
             (\<lambda>z.  exp (z + s / z) / z powr v) \<circ> Complex c"
    by (simp add: fun_eq_iff)
  finally show ?thesis .
next
  case [simp]: True
  show ?thesis using rGamma_hankel_integrable[of c v] c v
    by (simp add: powr_minus field_simps)
qed

end
