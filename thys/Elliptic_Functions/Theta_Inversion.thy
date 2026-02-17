section \<open>Related facts about Jacobi theta functions\<close>
theory Theta_Inversion
imports 
  "Theta_Functions.Jacobi_Triple_Product"
  "Theta_Functions.Theta_Nullwert"
  Complex_Lattices
begin

(* TODO Move *)
lemmas [simp del] = div_mult_self1 div_mult_self2 div_mult_self3 div_mult_self4

text \<open>
  In this section we will re-use some of the lemmas we proved to study elliptic functions in order
  to show two non-trivial facts about the Jacobi theta functions. The first one is a uniqueness
  result:

  We know that $\vartheta_{00}(z,t)$, viewed as a function of $z$ for fixed $t$, is entire,
  periodic with period $1$, and quasi-periodic with period $t$ and factor $e^{-2z-t}$.
  We will show that for any fixed $t$ in the upper half plane, $\vartheta_{00}(\cdot, t)$ is 
  actually uniquely defined by these relations, up to a constant factor.
\<close>

subsection \<open>Uniqueness of quasi-periodic entire functions\<close>

text \<open>
  We first show a fairly obvious fact: in any complete real normed field, the separable ordinary 
  differential equation $f'(x) = g(x) f(x)$ has at most one solution up to a constant factor in
  any complex domain.

  If a non-vanishing function $G$ satisfies $G'(x) = g(x) G(X)$, then $G$ is that solution.
  This allows us to ``certify'' a solution easily.
\<close>
lemma separable_ODE_simple_unique:
  fixes f :: "'a :: {banach, real_normed_field} \<Rightarrow> 'a"
  assumes eq: "\<And>x. x \<in> A \<Longrightarrow> f' x = g x * f x"
  assumes deriv_f: "\<And>x. x \<in> A \<Longrightarrow> (f has_field_derivative f' x) (at x within A)"
  assumes deriv_g: "\<And>x. x \<in> A \<Longrightarrow> (G has_field_derivative (g x * G x)) (at x within A)"
  assumes nonzero [simp]: "\<And>x. x \<in> A \<Longrightarrow> G x \<noteq> 0"
  assumes "convex A"
  shows "\<exists>c. \<forall>x\<in>A. f x = c * G x"
proof - 
  have "\<exists>c. \<forall>x\<in>A. f x / G x = c"
  proof (rule has_field_derivative_zero_constant)
    show "((\<lambda>x. f x / G x) has_field_derivative 0) (at x within A)" if x: "x \<in> A" for x
      using x by (auto intro!: derivative_eq_intros deriv_f deriv_g simp: eq)
  qed fact
  then obtain c where c: "\<And>x. x \<in> A \<Longrightarrow> f x / G x = c"
    by blast
  thus ?thesis
    by (auto simp: field_simps)
qed

text \<open>
  The following locale captures the notion of an entire function in the complex plane
  that satisfies the same (quasi-)periodicity as the Jacobi theta function $\vartheta_{00}$,
  namely $f(z+1) = f(z)$ and $f(z + t) = e^{-2z-t}f(z)$ for some fixed $t$ with $\text{Im}(t)>0$.

  We will show that any such function is equal to $\vartheta_{00}$ up to a constant factor.
\<close>
locale thetalike_function =
  fixes f :: "complex \<Rightarrow> complex" and t :: complex
  assumes entire: "f holomorphic_on UNIV"
  assumes Im_t: "Im t > 0"
  assumes f_plus_1: "f (z + 1) = f z"
  assumes f_plus_quasiperiod: "f (z + t) = f z / to_nome (2*z+t)"
begin

lemma holomorphic:
  assumes "g holomorphic_on A"
  shows   "(\<lambda>x. f (g x)) holomorphic_on A"
proof -
  have "(f \<circ> g) holomorphic_on A"
    using assms entire by (rule holomorphic_on_compose_gen) auto
  thus ?thesis
    by (simp add: o_def)
qed

lemma analytic:
  assumes "g analytic_on A"
  shows   "(\<lambda>x. f (g x)) analytic_on A"
proof -
  have *: "f analytic_on UNIV"
    by (subst analytic_on_open) (auto intro!: holomorphic)
  have "(f \<circ> g) analytic_on A"
    using assms * by (rule analytic_on_compose_gen) auto
  thus ?thesis
    by (simp add: o_def)
qed


text \<open>
  We first show some straightforward facts about the behaviour of $f$ on the lattice generated
  by $1$ and $t$.
\<close>
sublocale lattice: std_complex_lattice t
  by standard (use Im_t in \<open>auto elim!: Reals_cases\<close>)

lemma f_plus_of_nat: "f (z + of_nat n) = f z"
proof (induction n)
  case (Suc n)
  thus ?case
    using f_plus_1[of "z + of_nat n"] by (simp add: algebra_simps)
qed auto

lemma f_plus_of_int: "f (z + of_int n) = f z"
  using f_plus_of_nat[of z "nat n"] f_plus_of_nat[of "z + of_int n" "nat (-n)"]
  by (cases "n \<ge> 0") (auto simp: algebra_simps)

lemma f_plus_of_nat_quasiperiod:
  "f (z + of_nat n * t) = f z / to_nome (2 * of_nat n * z + of_nat (n\<^sup>2) * t)"
proof (induction n)
  case (Suc n)
  thus ?case
    using f_plus_quasiperiod[of "z + of_nat n * t"] 
    by (simp add: algebra_simps power2_eq_square flip: to_nome_add)
qed auto

lemma f_plus_of_int_quasiperiod:
  "f (z + of_int n * t) = f z / to_nome (2 * of_int n * z + of_int (n\<^sup>2) * t)"
proof (cases "n \<ge> 0")
  case True
  thus ?thesis
    using f_plus_of_nat_quasiperiod[of z "nat n"] by (auto simp: sgn_if)
next
  case False
  thus ?thesis
    using f_plus_of_nat_quasiperiod[of "z + of_int n * t" "nat (-n)"]
    by (simp add: field_simps to_nome_add to_nome_diff power2_eq_square to_nome_minus)
qed

lemma relE:
  assumes "lattice.rel z z'"
  obtains m n :: int where "z = z' + of_int m + of_int n * t"
  using assms unfolding lattice.rel_def
  by (elim lattice.latticeE) (auto simp: lattice.of_\<omega>12_coords_def algebra_simps)

lemma f_zero_cong_lattice:
  assumes "lattice.rel z z'"
  shows   "f z = 0 \<longleftrightarrow> f z' = 0"
proof -
  interpret lattice: complex_lattice_periodic 1 t "\<lambda>z. f z = 0"
    by standard (auto simp: f_plus_1 f_plus_quasiperiod)
  show ?thesis
    using lattice.lattice_cong[OF assms] .
qed

lemma zorder_f_cong_lattice:
  assumes "lattice.rel z z'"
  shows   "zorder f z = zorder f z'"
proof -
  from assms obtain m n where mn: "z = z' + of_int m + of_int n * t"
    by (elim relE)
  define h where "h = (\<lambda>z. z + of_int m + of_int n * t)"
  define g where "g = (\<lambda>z. to_nome (-(2 * of_int n * (z + of_int m) + (of_int n)\<^sup>2 * t)))"
  have "zorder f (h z') = zorder (f \<circ> h) z'"
    by (simp add: zorder_shift' h_def algebra_simps)
  also have "\<dots> = zorder f z'"
  proof (cases "\<forall>z. f z = 0")
    case True
    hence [simp]: "f = (\<lambda>_. 0)"
      by auto
    show ?thesis
      by simp
  next
    case False
    have ev_nz: "eventually (\<lambda>z. f z \<noteq> 0) (cosparse UNIV)"
    proof -
      have "(\<forall>x\<in>UNIV. f x = 0) \<or> (\<forall>\<^sub>\<approx>x\<in>UNIV. f x \<noteq> 0)"
        by (intro nicely_meromorphic_imp_constant_or_avoid 
                  analytic_on_imp_nicely_meromorphic_on analytic) auto
      moreover have "\<not>(\<forall>x\<in>UNIV. f x = 0)"
        using False by auto
      ultimately show ?thesis
        by blast
    qed
    hence ev: "eventually (\<lambda>w. f w \<noteq> 0) (at z')"
      by (rule eventually_cosparse_imp_eventually_at) auto
    have "f \<circ> h = (\<lambda>z. f z * g z)"
      unfolding to_nome_minus g_def
      by (auto simp: h_def fun_eq_iff f_plus_of_int_quasiperiod f_plus_of_int divide_inverse)
    hence "zorder (f \<circ> h) z' = zorder (\<lambda>z. f z * g z) z'"
      by (rule arg_cong)
    also have "zorder (\<lambda>z. f z * g z) z' = zorder f z' + zorder g z'"
      by (rule zorder_times_analytic)
         (use ev in \<open>auto intro!: analytic_intros analytic simp: g_def\<close>)
    also have "zorder g z' = 0"
      by (rule zorder_eq_0I) (auto simp: g_def intro!: analytic_intros)
    finally show ?thesis
      by (simp add: o_def)
  qed
  finally show ?thesis
    by (simp add: h_def mn o_def)
qed

lemma deriv_f_plus_1: "deriv f (z + 1) = deriv f z"
proof -
  have "deriv f (z + 1) = deriv (\<lambda>z. f (z + 1)) z"
    by (simp add: deriv_shift_0' o_def add_ac)
  also have "(\<lambda>z. f (z + 1)) = f"
    by (subst f_plus_1) auto
  finally show ?thesis .
qed

lemma deriv_f_plus_quasiperiod:
  "deriv f (z + t) = (deriv f z - 2 * pi * \<i> * f z) / to_nome (2 * z + t)"
proof -
  have "deriv f (z + t) = deriv (\<lambda>z. f (z + t)) z"
    by (simp add: deriv_shift_0' o_def add_ac)
  also have "(\<lambda>z. f (z + t)) = (\<lambda>z. f z * to_nome (-2 * z - t))"
    by (subst f_plus_quasiperiod) (auto simp: to_nome_diff to_nome_minus field_simps to_nome_add)
  also have "deriv \<dots> z = f z * deriv (\<lambda>z. to_nome (- (2 * z) - t)) z + deriv f z * to_nome (- (2 * z) - t)"
    by (subst complex_derivative_mult_at) (auto intro!: analytic_intros analytic)
  also have "deriv (\<lambda>z. to_nome (- (2 * z) - t)) z = -2 * pi * \<i> * to_nome (-(2*z)-t)"
    by (rule DERIV_imp_deriv) (auto intro!: derivative_eq_intros)
  finally show "deriv f (z + t) = (deriv f z - 2 * pi * \<i> * f z) / to_nome (2 * z + t)"
    by (auto simp: field_simps to_nome_minus to_nome_diff to_nome_add)
qed


text \<open>
  Next, we will simplify the integral
  \[\int_{\gamma} \frac{h(z) f'(z)}{f(z)}\,\text{d}z\]
  for an arbitrary function $h(z)$ using the shift relations for $f$.
  Here, $\gamma$ is a counter-clockwise contour along the border of a period parallelogram with
  lower left corner $b$ and no zeros of $f$ on it.

  We find that:
  \[\int_{\gamma} \frac{h(z) f'(z)}{f(z)}\,\text{d}z =
     \int_b^{b+1} (h(z) - h(z+t))\frac{f'(z)}{f(z)} + 2\pi i h(z+t)\,\text{d}z -
     \int_b^{b+t} (h(z) - h(z+1))\frac{f'(z)}{f(z)}\,\text{d}z\]
\<close>
lemma argument_principle_f_gen:
  fixes orig :: complex
  defines "\<gamma> \<equiv> parallelogram_path orig 1 t"
  assumes h: "h holomorphic_on UNIV"
  assumes nz: "\<And>z. z \<in> path_image \<gamma> \<Longrightarrow> f z \<noteq> 0"
  shows "contour_integral \<gamma> (\<lambda>x. h x * deriv f x / f x) =
           contour_integral (linepath orig (orig + 1)) 
             (\<lambda>z. (h z - h (z + t)) * deriv f z / f z + 2 * pi * \<i> * h (z + t)) -
           contour_integral (linepath orig (orig + t))
             (\<lambda>z. (h z - h (z + 1)) * deriv f z / f z)"
proof -
  define h' where "h' = (\<lambda>x. h (x + orig) * deriv f (x + orig) / f (x + orig))"
  have [analytic_intros]: "h analytic_on A" for A
    using h analytic_on_holomorphic by blast

  have "contour_integral \<gamma> (\<lambda>x. h x * deriv f x / f x) = 
          contour_integral (linepath 0 1) (\<lambda>x. h' x - h' (x + t)) -
          contour_integral (linepath 0 t) (\<lambda>x. h' x - h' (x + 1))" (is "_ = ?rhs")
    unfolding \<gamma>_def
  proof (subst contour_integral_parallelogram_path'; (fold \<gamma>_def)?)
    show "continuous_on (path_image \<gamma>) (\<lambda>x. h x * deriv f x / f x)" using nz
      by (intro continuous_intros holomorphic_on_imp_continuous_on analytic_imp_holomorphic)
         (auto intro!: analytic_intros analytic)
  next
    have 1: "linepath orig (orig + 1) = (+) orig \<circ> linepath 0 1"
     and 2: "linepath orig (orig + t) = (+) orig \<circ> linepath 0 t"
      by (auto simp: linepath_translate add_ac)
    show "contour_integral (linepath orig (orig + 1))
            (\<lambda>x. h x * deriv f x / f x - h (x + t) * deriv f (x + t) / f (x + t)) -
          contour_integral (linepath orig (orig + t)) 
            (\<lambda>x. h x * deriv f x / f x - h (x + 1) * deriv f (x + 1) / f (x + 1)) = ?rhs"
      unfolding 1 2 contour_integral_translate h'_def by (simp add: algebra_simps)
  qed

  also have "(\<lambda>z. h' z - h' (z + 1)) = 
             (\<lambda>z. (h (z + orig) - h (z + orig + 1)) * deriv f (z + orig) / f (z + orig))" 
    (is "?lhs = ?rhs")
  proof
    fix z :: complex
    have "h' z - h' (z + 1) = 
            h (z + orig) * deriv f (z + orig) / f (z + orig) -
            h (z + orig + 1) * deriv f (z + orig + 1) / f (z + orig + 1)"
      by (simp add: h'_def add_ac)
    also have "\<dots> = (h (z + orig) - h (z + orig + 1)) * deriv f (z + orig) / f (z + orig)"
      unfolding f_plus_1 deriv_f_plus_1 by (simp add: diff_divide_distrib ring_distribs)
    finally show "?lhs z = ?rhs z" .
  qed
  also have "contour_integral (linepath 0 t) \<dots> =
             contour_integral ((+) orig \<circ> linepath 0 t) (\<lambda>z. (h z - h (z + 1)) * deriv f z / f z)"
    by (rule contour_integral_translate [symmetric])
  also have "(+) orig \<circ> linepath 0 t = linepath orig (orig + t)"
    by (subst linepath_translate) (simp_all add: add_ac)

  also have "contour_integral (linepath 0 1) (\<lambda>z. h' z - h' (z + t)) =
             contour_integral (linepath 0 1) 
               (\<lambda>z. (h (z + orig) - h (z + orig + t)) * deriv f (z + orig) / f (z + orig) + 
                    2 * pi * \<i> * h (z + orig + t))"
    (is "contour_integral _ ?lhs = contour_integral _ ?rhs")
  proof (rule contour_integral_cong)
    fix z :: complex
    assume z: "z \<in> path_image (linepath 0 1)"
    hence "orig + z \<in> path_image ((+) orig \<circ> linepath 0 1)"
      by (subst path_image_compose) auto
    also have "(+) orig \<circ> linepath 0 1 = linepath orig (orig + 1)"
      by (subst linepath_translate) (auto simp: add_ac)
    finally have "orig + z \<in> path_image \<gamma>"
      unfolding \<gamma>_def parallelogram_path_def by (auto simp: path_image_join)
    hence nz': "f (orig + z) \<noteq> 0"
      using nz by blast

    have "h' z - h' (z + t) = 
            h (z + orig) * deriv f (z + orig) / f (z + orig) -
            h (z + orig + t) * (deriv f (z + orig + t) / f (z + orig + t))"
      by (simp add: h'_def add_ac)
    also have "deriv f (z + orig + t) / f (z + orig + t) = 
               deriv f (z + orig) / f (z + orig) - 2 * pi * \<i>"
      unfolding f_plus_quasiperiod deriv_f_plus_quasiperiod using nz'
      by (auto simp: divide_simps add_ac)
    also have "h (z + orig) * deriv f (z + orig) / f (z + orig) - h (z + orig + t) * \<dots> = ?rhs z"
      by (simp add: ring_distribs diff_divide_distrib)
    finally show "?lhs z = ?rhs z" .
  qed auto
  also have "\<dots> = contour_integral ((+) orig \<circ> linepath 0 1) 
                    (\<lambda>z. (h z - h (z + t)) * deriv f z / f z + 2 * pi * \<i> * h (z + t))"
    unfolding contour_integral_translate by (simp add: add_ac)
  also have "(+) orig \<circ> linepath 0 1 = linepath orig (orig + 1)"
    by (subst linepath_translate) (simp_all add: add_ac)

  finally show ?thesis .
qed

text \<open>
  We now instantiate the above fact with $h(z) = 1$ and see that the corresponding
  integral divided by $2\pi i$ evaluates to 1. This will later tell us that every period
  parallelogram contains exactly one root of $f$, and that it is a simple root.
\<close>
lemma argument_principle_f_1:
  fixes orig :: complex
  defines "\<gamma> \<equiv> parallelogram_path orig 1 t"
  assumes nz: "\<And>z. z \<in> path_image \<gamma> \<Longrightarrow> f z \<noteq> 0"
  shows "contour_integral \<gamma> (\<lambda>z. deriv f z / f z) = 2 * pi * \<i>"
  using argument_principle_f_gen[OF _ nz, of "\<lambda>_. 1"] by (simp add: \<gamma>_def)

text \<open>
  Next, we instantiate the lemma with $h(z) = z$ and see that the integral divided by
  $2\pi i$ evaluates to some value of the form $\frac{t+1}{2} + m + nt$ for integers $m,n$.
  In other words: it evaluates to some value equivalent to $\frac{t+1}{2}$ modulo our lattice.

  This will later tell us that the roots of $f$ in any period parallelogram sum to something
  equivalent to $\frac{t+1}{2}$. Since we know there is only one root and it is simple, 
  this means that the only root in each period parallelogram is the copy of $\frac{t+1}{2}$
  contained in it.
\<close>
lemma argument_principle_f_z:
  fixes orig :: complex
  defines "\<gamma> \<equiv> parallelogram_path orig 1 t"
  assumes nz: "\<And>z. z \<in> path_image \<gamma> \<Longrightarrow> f z \<noteq> 0"
  shows "lattice.rel (contour_integral \<gamma> (\<lambda>z. z * deriv f z / f z) / (2*pi*\<i>)) ((t+1)/2)"
proof -
  note [holomorphic_intros del] = holomorphic_deriv
  note [holomorphic_intros] = holomorphic holomorphic_on_subset[OF holomorphic_deriv[of _ UNIV]]
  define \<gamma>1 where "\<gamma>1 = linepath orig (orig + 1)"
  define \<gamma>2 where "\<gamma>2 = linepath orig (orig + t)"
  define \<gamma>2' where "\<gamma>2' = f \<circ> \<gamma>2"
  define \<gamma>3 where "\<gamma>3 = (\<lambda>z. f orig * to_nome z) \<circ> linepath 0 (-2 * orig - t)"

  have "pathstart \<gamma> \<in> path_image \<gamma>"
    by blast
  from nz[OF this] have [simp]: "f orig \<noteq> 0"
    by (simp add: \<gamma>_def)

  have [simp, intro]: "valid_path \<gamma>1" "valid_path \<gamma>2"
    by (simp_all add: \<gamma>1_def \<gamma>2_def)
  have [simp, intro]: "valid_path \<gamma>2'"
    unfolding \<gamma>2'_def by (intro valid_path_compose_analytic[of _ _ UNIV] analytic) auto
  have [simp, intro]: "valid_path \<gamma>3"
    unfolding \<gamma>3_def by (intro valid_path_compose_analytic[of _ _ UNIV] analytic_intros) auto

  have [simp]: "pathstart \<gamma>2' = f orig" "pathfinish \<gamma>2' = f (orig + t)"
    by (simp_all add: \<gamma>2'_def \<gamma>2_def pathstart_compose pathfinish_compose)
  have [simp]: "pathstart \<gamma>3 = f orig" "pathfinish \<gamma>3 = f (orig + t)"
    by (simp_all add: \<gamma>3_def pathstart_compose pathfinish_compose f_plus_quasiperiod
                      to_nome_diff to_nome_minus to_nome_add field_simps)

  have nz': "f z \<noteq> 0" if "z \<in> path_image \<gamma>1 \<union> path_image \<gamma>2" for z
  proof -
    note \<open>z \<in> path_image \<gamma>1 \<union> path_image \<gamma>2\<close>
    also have "path_image \<gamma>1 \<union> path_image \<gamma>2 \<subseteq> path_image \<gamma>"
      by (auto simp: \<gamma>1_def \<gamma>2_def \<gamma>_def path_image_compose path_image_join 
                     parallelogram_path_def image_Un closed_segment_commute
               simp flip: closed_segment_translation)
    finally show ?thesis
      using nz[of z] by blast
  qed

  have [simp]: "0 \<notin> path_image \<gamma>3"
    by (auto simp: \<gamma>3_def path_image_compose)
  have [simp]: "0 \<notin> path_image \<gamma>2'"
    using nz' unfolding \<gamma>2'_def by (auto simp: \<gamma>2'_def path_image_compose)


  text \<open>The actual proof starts here.\<close>
  define I1 where "I1 = contour_integral \<gamma>1"
  define I2 where "I2 = contour_integral \<gamma>2"

  have "winding_number (f \<circ> \<gamma>1) 0 \<in> \<int>"
  proof (rule integer_winding_number)
    have "valid_path (f \<circ> \<gamma>1)"
      by (intro valid_path_compose_analytic[of _ _ UNIV] analytic) auto
    thus "path (f \<circ> \<gamma>1)"
      by (rule valid_path_imp_path)
  qed (auto simp: path_image_compose nz' pathfinish_def pathstart_def \<gamma>1_def linepath_def f_plus_1)
  then obtain m where m: "winding_number (f \<circ> \<gamma>1) 0 = of_int m"
    by (elim Ints_cases)

  have "winding_number \<gamma>2' 0 + orig + t / 2 \<in> \<int>"
  proof -
    define r where "r = unwinding (\<i> * pi * (- (2 * orig) - t))"
    have "winding_number (\<gamma>2' +++ reversepath \<gamma>3) 0 \<in> \<int>"
    proof (rule integer_winding_number)
      have "valid_path (\<gamma>2' +++ reversepath \<gamma>3)"
        by (intro valid_path_join valid_path_compose_analytic[of _ _ UNIV] analytic)
           (auto simp: pathfinish_compose f_plus_quasiperiod)
      thus "path (\<gamma>2' +++ reversepath \<gamma>3)"
        by (rule valid_path_imp_path)
    next
      show "pathfinish (\<gamma>2' +++ reversepath \<gamma>3) =
            pathstart (\<gamma>2' +++ reversepath \<gamma>3)"
        by (auto simp: pathfinish_compose pathstart_compose \<gamma>2_def)
    next
      have "0 \<notin> path_image \<gamma>2' \<union> path_image \<gamma>3"
        by auto
      also have "path_image \<gamma>2' \<union> path_image \<gamma>3 = path_image (\<gamma>2' +++ reversepath \<gamma>3)"
        by (subst path_image_join) 
           (simp_all add: f_plus_quasiperiod)
      finally show "0 \<notin> path_image (\<gamma>2' +++ reversepath \<gamma>3)" .
    qed

    also have "winding_number (\<gamma>2' +++ reversepath \<gamma>3) 0 =
               winding_number \<gamma>2' 0 + winding_number (reversepath \<gamma>3) 0"
      by (rule winding_number_join) (auto simp: valid_path_imp_path)
    also have "winding_number (reversepath \<gamma>3) 0 = -winding_number \<gamma>3 0"
      by (subst winding_number_reversepath) (auto simp: valid_path_imp_path)
    also have "winding_number \<gamma>3 0 = contour_integral \<gamma>3 (\<lambda>w. 1 / w) / (2 * pi * \<i>)"
      by (subst winding_number_valid_path) auto
    also have "contour_integral \<gamma>3 (\<lambda>w. 1 / w) = 
                 contour_integral (linepath 0 (-2 * orig - t))
                   (\<lambda>w. deriv (\<lambda>z. f orig * to_nome z) w / (f orig * to_nome w))" unfolding \<gamma>3_def 
      by (subst contour_integral_comp_analyticW[of _ UNIV]) (auto intro!: analytic_intros)
    also have "(\<lambda>w. deriv (\<lambda>z. f orig * to_nome z) w / (f orig * to_nome w)) = (\<lambda>w. pi * \<i>)"
    proof
      fix w :: complex
      have "deriv (\<lambda>z. f orig * to_nome z) w = pi * \<i> * to_nome w * f orig"
        by (rule DERIV_imp_deriv) (auto intro!: derivative_eq_intros)
      thus "deriv (\<lambda>z. f orig * to_nome z) w / (f orig * to_nome w) = pi * \<i>"
        by simp
    qed
    also have "contour_integral (linepath 0 (-2 * orig - t)) (\<lambda>w. pi*\<i>) / (2*pi*\<i>) = -orig - t / 2"
      by simp
    finally show ?thesis
      by (simp add: algebra_simps o_def)
  qed
  then obtain n where n: "winding_number \<gamma>2' 0 + orig + t / 2 = of_int n"
    by (elim Ints_cases)

  have "contour_integral \<gamma> (\<lambda>z. z * deriv f z / f z) / (2*pi*\<i>) =
          I1 (\<lambda>z. -t * deriv f z / f z + 2 * pi * \<i> * (z + t)) / (2*pi*\<i>) -
          I2 (\<lambda>z. -(deriv f z / f z)) / (2*pi*\<i>)"
    using nz unfolding \<gamma>_def I1_def I2_def \<gamma>1_def \<gamma>2_def
    by (subst argument_principle_f_gen) (auto simp: diff_divide_distrib)
  also have "I1 (\<lambda>z. -t * deriv f z / f z + 2 * pi * \<i> * (z + t)) =
             I1 (\<lambda>z. (-t) * (deriv f z / f z)) + I1 (\<lambda>z. 2 * pi * \<i> * (z + t))"
    using nz' unfolding I1_def \<gamma>1_def
    by (subst contour_integral_add)
       (auto intro!: contour_integrable_continuous_linepath holomorphic_on_imp_continuous_on
                     holomorphic_intros)
  also have "\<dots> / (2*pi*\<i>) = I1 (\<lambda>z. (-t) * (deriv f z / f z)) / (2*pi*\<i>) +
                            I1 (\<lambda>z. 2 * pi * \<i> * (z + t)) / (2*pi*\<i>)"
    by (simp add: add_divide_distrib)
  also have "I1 (\<lambda>z. 2 * pi * \<i> * (z + t)) = 2 * pi * \<i> * (orig + t + 1 / 2)"
    unfolding I1_def
  proof (rule contour_integral_unique)
    define F where "F = (\<lambda>z. pi * \<i> * z ^ 2 + 2 * pi * \<i> * t * z)"
    have "((\<lambda>z. 2 * pi * \<i> * (z + t)) has_contour_integral (F (pathfinish \<gamma>1) - F (pathstart \<gamma>1))) \<gamma>1"
      by (rule contour_integral_primitive[of UNIV])
         (auto simp: \<gamma>1_def F_def field_simps intro!: derivative_eq_intros)
    also have "F (pathfinish \<gamma>1) - F (pathstart \<gamma>1) = 2 * pi * \<i> * (orig + t + 1 / 2)"
      by (simp add: F_def \<gamma>1_def power2_eq_square field_simps)
    finally show "((\<lambda>z. 2 * pi * \<i> * (z + t)) has_contour_integral
                    (2 * pi * \<i> * (orig + t + 1 / 2))) \<gamma>1" .
  qed
  also have "\<dots> / (2*pi*\<i>) = (orig + t + 1/2)"
    by (simp add: divide_simps)
  also have "I1 (\<lambda>z. (-t) * (deriv f z / f z)) = (-t) * I1 (\<lambda>z. deriv f z / f z)"
    using nz' unfolding I1_def \<gamma>1_def
    by (subst contour_integral_lmul)
       (auto intro!: contour_integrable_continuous_linepath holomorphic_on_imp_continuous_on
                     holomorphic_intros)

  also have "I1 (\<lambda>z. deriv f z / f z) = contour_integral (f \<circ> \<gamma>1) (\<lambda>z. 1 / z)"
    unfolding I1_def \<gamma>1_def by (subst contour_integral_comp_analyticW[OF analytic[of _ UNIV]]) auto
  also have "-t * \<dots> / (2 * pi * \<i>) = -t * winding_number (f \<circ> \<gamma>1) 0"
    by (subst winding_number_valid_path)
       (auto simp: path_image_compose nz' intro!: valid_path_compose_analytic analytic)
  also have "winding_number (f \<circ> \<gamma>1) 0 = of_int m"
    by (rule m)

  also have "I2 (\<lambda>z. -(deriv f z / f z)) = -I2 (\<lambda>z. deriv f z / f z)"
    unfolding I2_def by (subst contour_integral_neg) auto
  also have "I2 (\<lambda>z. deriv f z / f z) = contour_integral \<gamma>2' (\<lambda>z. 1 / z)"
    unfolding I2_def \<gamma>2'_def \<gamma>2_def
    by (subst contour_integral_comp_analyticW[OF analytic[of _ UNIV]]) auto
  also have "(-\<dots>) / (2 * pi * \<i>) = -winding_number \<gamma>2' 0"
    by (subst winding_number_valid_path) auto
  also have "-t * of_int m + (orig + t + 1 / 2) - - winding_number \<gamma>2' 0 =
             (t + 1) / 2 + of_int n + of_int (-m) * t"
    unfolding n [symmetric] by (simp add: field_simps)
  finally have "contour_integral \<gamma> (\<lambda>z. z * deriv f z / f z) / (2*pi*\<i>) - (t+1)/2 =
                  complex_of_int n + complex_of_int (- m) * t"
    by simp
  also have "\<dots> = lattice.of_\<omega>12_coords (of_int n, of_int (-m))"
    by (simp add: lattice.of_\<omega>12_coords_def)
  also have "\<dots> \<in> lattice.lattice"
    by (rule lattice.of_\<omega>12_coords_in_lattice) auto
  finally show ?thesis 
    unfolding lattice.rel_def by blast
qed

text \<open>
  We now tie everything together and prove the fact mentioned above: the zeros of $f$ are
  precisely the shifted copies of $\frac{t+1}{2}$, and they are all simple. Unless of course
  $f(z)$ is identically zero.
\<close>
lemma zero_iff:
  assumes "\<not>(\<forall>z. f z = 0)"
  shows   "f z = 0 \<longleftrightarrow> lattice.rel z  ((t + 1) / 2)"
    and   "lattice.rel z ((t + 1) / 2) \<Longrightarrow> zorder f z = 1"
proof -
  note [holomorphic_intros] = holomorphic
  define avoid where "avoid = {z. f z = 0}"
  define parallelogram where "parallelogram = (\<lambda>z. closure (lattice.period_parallelogram z))"
  define parallelogram' where "parallelogram' = (\<lambda>z. interior (lattice.period_parallelogram z))"

  have ev_nz: "eventually (\<lambda>z. f z \<noteq> 0) (cosparse UNIV)"
  proof -
    have "(\<forall>x\<in>UNIV. f x = 0) \<or> (\<forall>\<^sub>\<approx>x\<in>UNIV. f x \<noteq> 0)"
      by (intro nicely_meromorphic_imp_constant_or_avoid 
                analytic_on_imp_nicely_meromorphic_on analytic) auto
    moreover have "\<not>(\<forall>x\<in>UNIV. f x = 0)"
      using assms by auto
    ultimately show ?thesis
      by blast
  qed

  have sparse_avoid: "\<not>z islimpt avoid" for z
  proof -
    from ev_nz have "eventually (\<lambda>z. f z \<noteq> 0) (at z)"
      by (rule eventually_cosparse_imp_eventually_at) auto
    thus ?thesis
      unfolding avoid_def by (auto simp: islimpt_iff_eventually)
  qed

  have countable: "countable avoid"
    using sparse_avoid no_limpt_imp_countable by blast
  obtain orig where avoid: "path_image (parallelogram_path orig 1 t) \<inter> avoid = {}"
   using lattice.shifted_period_parallelogram_avoid[OF countable] by blast

  have "compact (parallelogram orig)"
    unfolding parallelogram_def by (rule lattice.compact_closure_period_parallelogram)
  then obtain R where R: "parallelogram orig \<subseteq> ball 0 R"
    by (meson bounded_subset_ballD compact_imp_bounded)

  define \<gamma> where "\<gamma> = parallelogram_path orig 1 t"
  have \<gamma>_subset: "path_image \<gamma> \<subseteq> parallelogram orig"
   and \<gamma>_disjoint: "path_image \<gamma> \<inter> interior (lattice.period_parallelogram orig) = {}"
    using lattice.path_image_parallelogram_subset_closure[of orig]
          lattice.path_image_parallelogram_disjoint_interior[of orig]
    unfolding parallelogram_def \<gamma>_def by blast+
  have path_image_\<gamma>_eq: "path_image \<gamma> = parallelogram orig - parallelogram' orig"
    unfolding \<gamma>_def parallelogram_def parallelogram'_def
              lattice.path_image_parallelogram_path frontier_def ..
  have "parallelogram' orig \<subseteq> parallelogram orig"
    unfolding parallelogram_def parallelogram'_def
    by (meson closure_subset dual_order.trans interior_subset)
  hence parallelogram_conv_union: "parallelogram orig = parallelogram' orig \<union> path_image \<gamma>"
    using \<gamma>_subset path_image_\<gamma>_eq by blast    

  have \<gamma>: "valid_path \<gamma>" "path \<gamma>" "pathfinish \<gamma> = pathstart \<gamma>"
          "path_image \<gamma> \<subseteq> ball 0 R - {w \<in> ball 0 R. f w = 0}"
    using avoid R \<gamma>_subset by (auto simp: \<gamma>_def avoid_def intro!: valid_path_imp_path)

  have inside: "winding_number \<gamma> w = 1" if w: "w \<in> parallelogram orig" "f w = 0" for w
    using Im_t w avoid \<gamma>_disjoint parallelogram_conv_union unfolding \<gamma>_def
    by (subst lattice.winding_number_parallelogram_inside)
       (auto simp: avoid_def parallelogram'_def parallelogram_def)

  have outside: "winding_number \<gamma> w = 0" 
    if w: "w \<in> {w \<in> ball 0 R. f w = 0} - parallelogram orig" for w
  proof (rule winding_number_zero_outside)
    show "convex (parallelogram orig)"
      unfolding parallelogram_def by auto
    show "w \<notin> parallelogram orig" using w avoid
      by auto
    show "path_image \<gamma> \<subseteq> parallelogram orig"
      using path_image_\<gamma>_eq by blast
  qed (use \<gamma> in auto)

  have outside': "\<forall>z. z \<notin> ball 0 R \<longrightarrow> winding_number \<gamma> z = 0"
  proof safe
    fix z :: complex assume z: "z \<notin> ball 0 R"
    show "winding_number \<gamma> z = 0"
      by (rule winding_number_zero_outside[of _ "ball 0 R"])
         (use z \<gamma> in \<open>auto simp: \<gamma>_def\<close>)
  qed

  have "finite (cball 0 R \<inter> {w. f w = 0})"
    by (rule sparse_in_compact_finite)
       (use ev_nz in \<open>auto simp: eventually_cosparse intro: sparse_in_subset\<close>)
  hence fin: "finite {w\<in>ball 0 R. f w = 0}"
    by (rule finite_subset [rotated]) auto

  have "contour_integral \<gamma> (\<lambda>x. deriv f x / f x) / (2 * pi * \<i>) = 1"
    unfolding \<gamma>_def by (subst argument_principle_f_1) (use avoid in \<open>auto simp: avoid_def\<close>)
  also have "contour_integral \<gamma> (\<lambda>x. deriv f x / f x) =
             contour_integral \<gamma> (\<lambda>x. deriv f x * 1 / f x)"
    by simp
  also have "\<dots> / (2 * pi * \<i>) = 
               (\<Sum>p\<in>{w\<in>ball 0 R. f w = 0}. winding_number \<gamma> p * 1 * of_int (zorder f p))"
    by (subst argument_principle[of "ball 0 R"]) 
       (use \<gamma> fin outside' in \<open>auto intro!: holomorphic\<close>)
  also have "(\<Sum>p\<in>{w \<in> ball 0 R. f w = 0}. winding_number \<gamma> p * 1 * of_int (zorder f p)) =
             (\<Sum>p\<in>{w \<in> parallelogram orig. f w = 0}. of_int (zorder f p))"
  proof (intro sum.mono_neutral_cong_right ballI)
    show "{w \<in> parallelogram orig. f w = 0} \<subseteq> {w \<in> ball 0 R. f w = 0}"
      using R by (auto simp: parallelogram_def path_image_\<gamma>_eq)
  qed (use fin in \<open>auto simp: outside inside\<close>)
  finally have "of_int (\<Sum>p\<in>{w \<in> parallelogram orig. f w = 0}. zorder f p) = complex_of_int 1"
    unfolding of_int_sum by simp
  hence sum_zorder_eq: "(\<Sum>p\<in>{w \<in> parallelogram orig. f w = 0}. zorder f p) = 1"
    by (simp only: of_int_eq_iff)

  obtain root where root: "{w \<in> parallelogram orig. f w = 0} = {root}" 
                          "f root = 0" "zorder f root = 1"
  proof -
    have "int (card {w \<in> parallelogram orig. f w = 0}) = (\<Sum>p\<in>{w \<in> parallelogram orig. f w = 0}. 1)"
      by simp
    also have "\<dots> \<le> (\<Sum>p\<in>{w \<in> parallelogram orig. f w = 0}. zorder f p)"
    proof (rule sum_mono)
      fix w assume w: "w \<in> {w \<in> parallelogram orig. f w = 0}"
      have "\<exists>\<^sub>F z in at w. f z \<noteq> 0" using ev_nz 
        by (intro eventually_frequently eventually_cosparse_imp_eventually_at[OF ev_nz]) auto
      hence "zorder f w > 0"
        by (subst zorder_pos_iff') (use w in \<open>auto intro!: analytic\<close>)
      thus "zorder f w \<ge> 1"
        by simp
    qed
    also have "\<dots> = 1"
      by (fact sum_zorder_eq)
    finally have "card {w \<in> parallelogram orig. f w = 0} \<le> 1"
      by simp
    moreover have "card {w \<in> parallelogram orig. f w = 0} > 0"
    proof (subst card_gt_0_iff, safe)
      assume *: "{w \<in> parallelogram orig. f w = 0} = {}"
      show False
        using sum_zorder_eq unfolding * by simp
    next
      show "finite {w \<in> parallelogram orig. f w = 0}"
        by (rule finite_subset[OF _ fin]) (use R in \<open>auto simp: parallelogram_def path_image_\<gamma>_eq\<close>)
    qed
    ultimately have "card {w \<in> parallelogram orig. f w = 0} = 1" 
      by linarith
    then obtain w where w: "{w \<in> parallelogram orig. f w = 0} = {w}"
      by (auto simp: card_1_singleton_iff)
    moreover have "zorder f w = 1"
      using sum_zorder_eq unfolding w by simp
    ultimately show ?thesis
      using that by blast
  qed

  have "lattice.rel (contour_integral \<gamma> (\<lambda>x. x * deriv f x / f x) / (2 * pi * \<i>)) ((t + 1) / 2)"
    unfolding \<gamma>_def by (rule argument_principle_f_z) (use avoid in \<open>auto simp: avoid_def\<close>)
  also have "contour_integral \<gamma> (\<lambda>x. x * deriv f x / f x) =
             contour_integral \<gamma> (\<lambda>x. deriv f x * x / f x)"
    by (simp add: mult_ac)
  also have "\<dots> / (2 * pi * \<i>) = 
               (\<Sum>p\<in>{w\<in>ball 0 R. f w = 0}. winding_number \<gamma> p * p * of_int (zorder f p))"
    by (subst argument_principle[of "ball 0 R"]) 
       (use \<gamma> fin outside' in \<open>auto intro!: holomorphic\<close>)
  also have "(\<Sum>p\<in>{w \<in> ball 0 R. f w = 0}. winding_number \<gamma> p * p * of_int (zorder f p)) =
             (\<Sum>p\<in>{w \<in> parallelogram orig. f w = 0}. p * of_int (zorder f p))"
  proof (intro sum.mono_neutral_cong_right ballI)
    show "{w \<in> parallelogram orig. f w = 0} \<subseteq> {w \<in> ball 0 R. f w = 0}"
      using R by (auto simp: parallelogram_def path_image_\<gamma>_eq)
  qed (use fin in \<open>auto simp: outside inside\<close>)
  also have "\<dots> = root"
    unfolding root(1) using root(3) by simp
  finally have root': "lattice.rel root ((t + 1) / 2)" .

  show "f z = 0 \<longleftrightarrow> lattice.rel z ((t + 1) / 2)"
  proof
    assume "lattice.rel z ((t + 1) / 2)"
    also have "lattice.rel ((t + 1) / 2) root"
      using root' by (simp add: lattice.rel_sym)
    finally show "f z = 0"
      using f_zero_cong_lattice[of z root] using root by simp
  next
    assume "f z = 0"
    obtain h where h: "bij_betw h (lattice.period_parallelogram z)
                                  (lattice.period_parallelogram orig)"
                      "\<And>w. lattice.rel (h w) w"
      using lattice.bij_betw_period_parallelograms[of z orig] by blast
    have "z \<in> lattice.period_parallelogram z"
      by auto
    hence "h z \<in> {z\<in>parallelogram orig. f z = 0}"
      using h(1) f_zero_cong_lattice[OF h(2)[of z]] \<open>f z = 0\<close>
      using bij_betw_apply closure_subset parallelogram_def by fastforce
    hence "h z = root"
      unfolding root(1) by simp
    hence "lattice.rel (h z) ((t+1) / 2)"
      using root' by simp
    thus "lattice.rel z ((t+1)/2)"
      using h(2) pre_complex_lattice.rel_symI pre_complex_lattice.rel_trans by blast
  qed

  show "zorder f z = 1" if *: "lattice.rel z ((t+1)/2)"
  proof -
    have "zorder f z = zorder f ((t+1)/2)"
      by (rule zorder_f_cong_lattice) fact
    also have "\<dots> = zorder f root"
      by (rule sym, rule zorder_f_cong_lattice) fact
    also have "\<dots> = 1"
      by fact
    finally show ?thesis .
  qed
qed

text \<open>
  Finally, we conclude that our quasi-periodic function is in fact a multiple of $\vartheta_{00}$.
\<close>
theorem multiple_jacobi_theta_00: "\<exists>c. \<forall>z. f z = c * jacobi_theta_00 z t"
proof -
  define g where "g = (\<lambda>z. jacobi_theta_00 0 t * f z - f 0 * jacobi_theta_00 z t)"
  interpret g: thetalike_function g t
  proof
    show "g holomorphic_on UNIV"
      unfolding g_def using Im_t by (auto intro!: holomorphic_intros holomorphic)
    show "Im t > 0"
      by (fact Im_t)
    show "g (z + 1) = g z" for z
      unfolding g_def
      by (simp add: f_plus_1 jacobi_theta_00_left.plus_1)
    show "g (z + t) = g z / to_nome (2 * z + t)" for z
      unfolding g_def using f_plus_quasiperiod[of z] jacobi_theta_00_plus_quasiperiod[of z t]
      by (simp add: diff_divide_distrib add_ac)
  qed

  show ?thesis
  proof (rule exI[of _ "f 0 / jacobi_theta_00 0 t"], rule allI)
    fix z :: complex
    have "g z = 0"
    proof (rule ccontr)
      assume "g z \<noteq> 0"
      hence *: "\<not>(\<forall>z. g z = 0)"
        by auto
      have "g 0 = 0"
        by (simp add: g_def)
      also have "?this \<longleftrightarrow> lattice.rel 0 ((t + 1) / 2)"
        by (rule g.zero_iff[OF *])
      also have "\<dots> \<longleftrightarrow> (0 - ((t + 1) / 2)) \<in> lattice.lattice"
        by (simp add: lattice.rel_def)
      also have "0 - ((t + 1) / 2) = lattice.of_\<omega>12_coords (-1/2, -1/2)"
        by (simp add: lattice.of_\<omega>12_coords_def field_simps)
      finally show False
        by (subst (asm) lattice.of_\<omega>12_coords_in_lattice_iff) auto
    qed
    thus "f z = f 0 / jacobi_theta_00 0 t * jacobi_theta_00 z t"
      using Im_t by (auto simp: field_simps jacobi_theta_00_0_left_nonzero g_def)
  qed
qed

end


text \<open>
  As a side effect, we also now know that the zeros of $\vartheta_{00}$ are all simple zeros.
\<close>
lemma jacobi_theta_00_simple_zero:
  assumes "Im t > 0" "jacobi_theta_00 z t = 0"
  shows   "zorder (\<lambda>z. jacobi_theta_00 z t) z = 1"
proof -
  interpret thetalike_function "\<lambda>z. jacobi_theta_00 z t"
    by unfold_locales
       (use assms(1) 
        in \<open>auto simp: jacobi_theta_00_plus_quasiperiod jacobi_theta_00_left.plus_1 add_ac
                 intro!: holomorphic_intros\<close>)
  have "\<not>(\<forall>z. jacobi_theta_00 z t = 0)"
    using jacobi_theta_00_0_left_nonzero assms(1) by blast
  with assms(2) and zero_iff show ?thesis
    by blast
qed

(* TODO: other jacobi_theta_xy *)



subsection \<open>Theta inversion\<close>

text \<open>
  Using the fact that any quasiperiodic function (in the sense used above) is a multiple
  of $\vartheta_{00}$ and the heat equation for $\vartheta_{00}$, we can now relatively easily
  prove the theta inversion identity, which describes how $\vartheta_{00}$ transforms under the
  modular transformation $t \mapsto -\frac{1}{t}$:
  \[\vartheta_{00}(z, -1/t) = \sqrt{-it} e^{i\pi tz^2} \vartheta_{00}(tz, t)\]
  In particular, this means that $\vartheta_{00}(0, t)$ is a modular form of weight $\frac{1}{2}$.
\<close>
theorem jacobi_theta_00_minus_one_over:
  fixes z t :: complex
  assumes t: "Im t > 0"
  shows "jacobi_theta_00 z (-(1/t)) = csqrt (-(\<i>*t)) * to_nome (t*z\<^sup>2) * jacobi_theta_00 (t*z) t"
proof -
  text \<open>
    First of all, we look at the quotient
      \[\frac{e^{i\pi tz^2}\vartheta_{00}(tz,t)}{\vartheta_{00}(z,-1/t)}\]
    and show that it does not depend on $z$.

    The proof works by nothing that, for fixed $t$ with $\text{Im}(t)>0$, the numerator is a 
    theta-like function in $z$ and must therefore be a constant multiple of the denominator.
  \<close>
  define f where "f = (\<lambda>z t. to_nome (t * z^2) * jacobi_theta_00 (t*z) t)"
  define g where "g = (\<lambda>z t. f z t / jacobi_theta_00 z (-1/t))"
  define c where "c = (\<lambda>t. g 0 t)"
  have [analytic_intros]: "c analytic_on A" if "A \<subseteq> {t. Im t > 0}" for A 
    unfolding c_def g_def f_def using that
    by (auto intro!: analytic_intros simp: Im_complex_div_lt_0 jacobi_theta_00_0_left_nonzero)

  have f_eq: "f z t = c t * jacobi_theta_00 z (-1/t)" if t: "Im t > 0" for z t
  proof -
    from t have [simp]: "t \<noteq> 0"
      by auto
    interpret f: thetalike_function "\<lambda>z. f z t" "-1/t"
    proof
      show "(\<lambda>z. f z t) holomorphic_on UNIV"
        using t unfolding f_def by (auto intro!: holomorphic_intros)
    next
      show "Im (-1/t) > 0"
        using t by (simp add: Im_complex_div_lt_0)
    next
      show "f (z + 1) t = f z t" for z
        using jacobi_theta_00_plus_quasiperiod[of "t*z" t]
        by (simp add: f_def ring_distribs power2_eq_square field_simps to_nome_add)
    next
      show "f (z + (-1/t)) t = f z t / to_nome (2 * z + (-1/t))" for z
      proof -
        have "f (z + (-1/t)) t = to_nome (t * (z - 1 / t)\<^sup>2) * jacobi_theta_00 (t * z - 1) t"
          by (simp add: f_def ring_distribs)
        also have "jacobi_theta_00 (t * z - 1) t = jacobi_theta_00 (t * z) t"
          by (rule jacobi_theta_00_left.minus_1)
        also have "t * (z - 1 / t) ^ 2 = t * z ^ 2 - 2 * z + 1 / t"
          by (simp add: field_simps power2_eq_square)
        also have "to_nome \<dots> * jacobi_theta_00 (t * z) t = f z t / to_nome (2*z + (-1/t))"
          by (simp add: f_def to_nome_add to_nome_diff)
        finally show ?thesis .
      qed
    qed

    obtain c' where "f z t = c' * jacobi_theta_00 z (-1/t)" for z
      using f.multiple_jacobi_theta_00 by blast
    from this[of 0] and this[of z] show ?thesis
      using jacobi_theta_00_0_left_nonzero[of "-1/t"] t
      by (auto simp: g_def divide_simps Im_complex_div_lt_0 c_def)
  qed

  text \<open>
    Next, we take the equation
    \[e^{i\pi tz^2}\vartheta_{00}(tz,t) = c(t) \vartheta_{00}(z,-1/t)\]
    and take the derivatives $\frac{\partial^2}{\partial z}$ of both sides and then,
    separately, $\frac{\partial}{\partial t}$ of both sides. We then use the heat equation
    for $\vartheta_{00}$ and combine both equations, which gives us the following ordinary
    differential equation:
    \[c'(t) = -\frac{c(t)}{2t} \]
  \<close>
  have c_ODE: "deriv c t = (-1 / (2*t)) * c t" if t: "Im t > 0" for t
  proof -
    have [simp]: "t \<noteq> 0"
      using t by auto

    have "(deriv ^^ 2) (\<lambda>z. f z t) 0 = (deriv ^^ 2) (\<lambda>z. c t * jacobi_theta_00 z (-1/t)) 0"
      using t by (subst f_eq) auto
    also have "\<dots> = c t * (deriv ^^ 2) (\<lambda>z. jacobi_theta_00 z (- 1 / t)) 0"
      by (rule higher_deriv_cmult')
         (use t in \<open>auto intro!: analytic_intros simp: Im_complex_div_lt_0\<close>)
    also have "(deriv ^^ 2) (\<lambda>z. jacobi_theta_00 z (- 1 / t)) 0 = 
                 4 * pi * \<i> * deriv (jacobi_theta_00 0) (-(1/t))"
      by (subst jacobi_theta_00_heat_equation) (use t in \<open>auto simp: Im_complex_div_lt_0\<close>)
    also have "(deriv ^^ 2) (\<lambda>z. f z t) 0 = 
                 deriv (deriv (\<lambda>z. jacobi_theta_00 (t * z) t)) 0 +
                 2 * deriv (\<lambda>z. to_nome (t*z\<^sup>2)) 0 * deriv (\<lambda>z. jacobi_theta_00 (t * z) t) 0 +
                 deriv (deriv (\<lambda>z. to_nome (t*z\<^sup>2))) 0 * jacobi_theta_00 0 t"
      unfolding f_def using t
      by (subst higher_deriv_mult[of _ UNIV]) (auto intro!: holomorphic_intros simp: eval_nat_numeral)
    also have "deriv (\<lambda>z. to_nome (t*z\<^sup>2)) = (\<lambda>z. 2 * pi * \<i> * t * z * to_nome (t*z\<^sup>2))"
      by (intro ext DERIV_imp_deriv) (auto intro!: derivative_eq_intros)
    also have "deriv \<dots> = (\<lambda>z. 2 * pi * \<i> * t * to_nome (t*z\<^sup>2) - 4 * pi\<^sup>2 * t\<^sup>2 * z\<^sup>2 * to_nome (t*z\<^sup>2))"
      by (intro ext DERIV_imp_deriv)
         (auto intro!: derivative_eq_intros simp: algebra_simps power2_eq_square)
    also have "deriv (\<lambda>z. jacobi_theta_00 (t * z) t) = (\<lambda>z. t * deriv (\<lambda>z. jacobi_theta_00 z t) (t*z))"
    proof (rule ext, rule DERIV_imp_deriv)
      fix z :: complex
      have "((\<lambda>z. jacobi_theta_00 z t) \<circ> (\<lambda>z. t * z) has_field_derivative 
              deriv (\<lambda>z. jacobi_theta_00 z t) (t*z) * t) (at z)"
        by (rule DERIV_chain) (use t in \<open>auto intro!: analytic_derivI analytic_intros\<close>)
      thus "((\<lambda>z. jacobi_theta_00 (t*z) t) has_field_derivative 
              t * deriv (\<lambda>z. jacobi_theta_00 z t) (t*z)) (at z)"
        by (simp add: algebra_simps o_def)
    qed
    also have "deriv \<dots> 0 = t * deriv (\<lambda>z. deriv (\<lambda>z. jacobi_theta_00 z t) (t*z)) 0"
      by (subst deriv_cmult') (use t in \<open>auto intro!: analytic_intros simp: eval_nat_numeral\<close>)
    also have "deriv (\<lambda>z. deriv (\<lambda>z. jacobi_theta_00 z t) (t*z)) 0 =
               t * (deriv ^^ 2) (\<lambda>z. jacobi_theta_00 z t) 0"
    proof (rule DERIV_imp_deriv)
      have "(deriv (\<lambda>z. jacobi_theta_00 z t) \<circ> (\<lambda>z. t * z) has_field_derivative 
              deriv (deriv (\<lambda>z. jacobi_theta_00 z t)) 0 * t) (at 0)"
        by (rule DERIV_chain) (use t in \<open>auto intro!: analytic_derivI analytic_intros\<close>)
      thus "((\<lambda>z. deriv (\<lambda>z. jacobi_theta_00 z t) (t * z)) has_field_derivative
               t * (deriv ^^ 2) (\<lambda>z. jacobi_theta_00 z t) 0) (at 0)"
        by (simp add: algebra_simps o_def eval_nat_numeral)
    qed
    also have "(deriv ^^ 2) (\<lambda>z. jacobi_theta_00 z t) 0 = 4 * pi * \<i> * deriv (jacobi_theta_00 0) t"
      using t by (subst jacobi_theta_00_heat_equation) simp_all
    finally have "4 * pi * \<i> * (t\<^sup>2 * deriv (jacobi_theta_00 0) t +
                                t * jacobi_theta_00 0 t / 2) =
                  4 * pi * \<i> * (c t * deriv (jacobi_theta_00 0) (- (1 / t)))"
      unfolding ring_distribs by (simp add: field_simps power2_eq_square)
    hence *: "c t * deriv (jacobi_theta_00 0) (-(1/t)) = 
                t\<^sup>2 * deriv (jacobi_theta_00 0) t + t * jacobi_theta_00 0 t / 2"
      by (subst (asm) mult_cancel_left) auto

    have "deriv (f 0) t = deriv (\<lambda>t. c t * jacobi_theta_00 0 (-1/t)) t"
    proof (rule deriv_cong_ev)
      have "eventually (\<lambda>t. t \<in> {t. Im t > 0}) (nhds t)"
        by (rule eventually_nhds_in_open) (use t in \<open>auto simp: open_halfspace_Im_gt\<close>)
      thus "\<forall>\<^sub>F x in nhds t. f 0 x = c x * jacobi_theta_00 0 (- 1 / x)"
        by eventually_elim (auto simp: f_eq)
    qed auto
    also have "\<dots> = c t * deriv (\<lambda>t. jacobi_theta_00 0 (- (1 / t))) t +
                    deriv c t * jacobi_theta_00 0 (- (1 / t))"
      by (subst complex_derivative_mult_at)
         (use t in \<open>auto intro!: analytic_intros simp: Im_complex_div_lt_0\<close>)
    also have "deriv (\<lambda>t. jacobi_theta_00 0 (- (1 / t))) t = 
                 deriv (jacobi_theta_00 0) (-(1/t)) * deriv (\<lambda>t. -(1/t)) t"
      by (rule deriv_compose_analytic)
         (use t in \<open>auto intro!: analytic_intros simp: Im_complex_div_lt_0\<close>)
    also have "deriv (\<lambda>t. -(1/t)) t = 1 / t ^ 2"
      using t by (auto intro!: DERIV_imp_deriv derivative_eq_intros simp: power2_eq_square)
    also have "deriv (f 0) t = deriv (jacobi_theta_00 0) t"
      unfolding f_def by simp
    finally have "deriv (jacobi_theta_00 0) t = 
                     c t * deriv (jacobi_theta_00 0) (-(1/t)) / t ^ 2 + 
                     deriv c t * jacobi_theta_00 0 (-(1/t))"
      by simp
    also note *
    finally have "jacobi_theta_00 0 t / (2*t) + deriv c t * jacobi_theta_00 0 (-(1/t)) = 0"
      by (simp add: add_divide_distrib power2_eq_square)

    also have "jacobi_theta_00 0 t = c t * jacobi_theta_00 0 (- (1 / t))"
      using f_eq[of t 0] t by (simp add: f_def)
    also have "c t * jacobi_theta_00 0 (-(1/t)) / (2 * t) + deriv c t * jacobi_theta_00 0 (-(1/t)) =
               jacobi_theta_00 0 (-1/t) * (c t / (2*t) + deriv c t)"
      by (simp add: algebra_simps)
    finally have "c t / (2*t) + deriv c t = 0"
      unfolding mult_eq_0_iff using jacobi_theta_00_0_left_nonzero[of "-1/t"] t
      by (simp_all add: Im_complex_div_lt_0)
    thus "deriv c t = (-1 / (2*t)) * c t"
      using t by (simp add: field_simps add_eq_0_iff)
  qed

  text \<open>
    This is a particularly simple separable ODE, which has the unique general solution
    $c(t) = C / \sqrt{t}$ for some constant $C$.
  \<close>
  have "\<exists>C. \<forall>t\<in>{t. Im t > 0}. c t = C * (1 / csqrt t)"
    using c_ODE
  proof (rule separable_ODE_simple_unique)
    show "(c has_field_derivative deriv c t) (at t within {t. 0 < Im t})"
      if "t \<in> {t. Im t > 0}" for t
      by (intro analytic_derivI analytic_intros) (use that in auto)
  next
    show "((\<lambda>x. 1 / csqrt x) has_field_derivative - 1 / (2 * t) * (1 / csqrt t)) 
             (at t within {t. 0 < Im t})" if "t \<in> {t. Im t > 0}" for t using that
      by (auto intro!: derivative_eq_intros simp: complex_nonpos_Reals_iff 
               simp flip: power2_eq_square)
  qed (auto simp: convex_halfspace_Im_gt)
  then obtain C where C: "\<And>t. Im t > 0 \<Longrightarrow> c t = C / csqrt t"
    by auto

  text \<open>
    Noting that $c(i) = 1$, we find that $C = \sqrt{i}$ and therefore
    $c(t) = 1 / \sqrt{-it}$ as desired.
  \<close>
  have "c \<i> = C / csqrt \<i>"
    by (rule C) auto
  also have "c \<i> = 1"
    by (simp add: c_def g_def f_def jacobi_theta_00_0_left_nonzero)
  finally have C_eq: "C = csqrt \<i>"
    by (simp add: field_simps)

  have c_eq: "c t = 1 / csqrt (- \<i> * t)" if t: "Im t > 0" for t
  proof -
    have [simp]: "t \<noteq> 0"
      using t by auto
    have "csqrt (\<i> * (-\<i> * t)) = csqrt \<i> * csqrt (-\<i> * t)"
    proof (rule csqrt_mult)
      have "Arg (-\<i> * t) = Arg (-\<i>) + Arg t"
        by (subst Arg_times) (use Arg_lt_pi[of t] t in auto)
      thus "Arg \<i> + Arg (- \<i> * t) \<in> {- pi<..pi}"
        using Arg_lt_pi[of t] t by auto
    qed
    hence "csqrt \<i> / csqrt t = 1 / csqrt (-\<i> * t)"
      by (simp add: field_simps del: csqrt_ii)
    also have "csqrt \<i> / csqrt t = c t"
      by (subst C) (use t in \<open>auto simp: C_eq\<close>)
    finally show ?thesis .
  qed

  have "to_nome (t * z\<^sup>2) * jacobi_theta_00 (t * z) t = c t * jacobi_theta_00 z (- 1 / t)"
    using f_eq[of t z] t by (simp add: f_def)
  also have "c t = 1 / csqrt (-\<i> * t)"
    using t by (rule c_eq)
  finally show ?thesis
    using t by (auto simp add: field_simps)
qed

text \<open>
  Equivalent identities for the other $\vartheta_{xx}$ follow:
\<close>
lemma jacobi_theta_01_minus_one_over:
  fixes z t :: complex
  assumes "Im t > 0"
  shows "jacobi_theta_01 z (-(1/t)) = csqrt (-(\<i>*t)) * to_nome (t*z\<^sup>2) * jacobi_theta_10 (t*z) t"
  by (simp add: jacobi_theta_01_def jacobi_theta_10_def jacobi_theta_00_minus_one_over
                ring_distribs power2_eq_square to_nome_add add_divide_distrib assms)

lemma jacobi_theta_10_minus_one_over:
  fixes z t :: complex
  assumes "Im t > 0"
  shows "jacobi_theta_10 z (-(1/t)) = csqrt (-(\<i>*t)) * to_nome (t*z\<^sup>2) * jacobi_theta_01 (t*z) t"
proof -
  have [simp]: "t \<noteq> 0"
    using assms by auto
  have "jacobi_theta_10 z (-1/t) = csqrt (-\<i>*t) * 
          (to_nome (z - 1 / (t * 4)) * to_nome (t * (z - 1 / (t * 2))\<^sup>2)) *
          jacobi_theta_00 (t * z - 1 / 2) t" using assms 
    by (simp add: jacobi_theta_10_def jacobi_theta_00_minus_one_over
                  power2_eq_square ring_distribs mult_ac)
  also have "to_nome (z - 1 / (t * 4)) * to_nome (t * (z - 1 / (t * 2))\<^sup>2) =
             to_nome (z - 1 / (t * 4) + t * (z - 1 / (t * 2))\<^sup>2)"
    by (rule to_nome_add [symmetric])
  also have "z - 1 / (t * 4) + t * (z - 1 / (t * 2))\<^sup>2 = t * z\<^sup>2"
    by (auto simp: field_simps power2_eq_square)
  also have "jacobi_theta_00 (t * z - 1 / 2) t = jacobi_theta_01 (t * z - 1) t"
    by (simp add: jacobi_theta_01_def)
  also have "jacobi_theta_01 (t * z - 1) t = jacobi_theta_01 (t * z) t"
    by (rule jacobi_theta_01_left.minus_1)
  finally show ?thesis by simp
qed

lemma jacobi_theta_11_minus_one_over:
  fixes z t :: complex
  assumes t: "Im t > 0"
  shows "jacobi_theta_11 z (-(1/t)) = -\<i> * csqrt (-(\<i>*t)) * to_nome (t*z\<^sup>2) * jacobi_theta_11 (t*z) t"
proof -
  have [simp]: "t \<noteq> 0"
    using assms by auto
  have "jacobi_theta_11 z (-1/t) = \<i> * csqrt (-(\<i>*t)) * to_nome (t * z\<^sup>2) *
          (to_nome (t*z + t/4 - 1/2) * jacobi_theta_00 (t * z - 1 / 2 + t / 2) t)" using assms 
    by (simp add: jacobi_theta_11_def jacobi_theta_00_minus_one_over add_ac
                  power2_eq_square ring_distribs mult_ac to_nome_add to_nome_diff)
  also have "to_nome (t * z + t / 4 - 1 / 2) * jacobi_theta_00 (t * z - 1 / 2 + t / 2) t = 
             jacobi_theta_11 (t*z - 1) t"
    by (simp add: jacobi_theta_11_def algebra_simps)
  also have "\<dots> = -jacobi_theta_11 (t*z) t"
    by (rule jacobi_theta_11_minus1_left)
  finally show ?thesis
    by simp
qed


subsection \<open>Theta nullwert inversions in the reals\<close>

text \<open>
  We can thus translate the above theta inversion identities into the $q$-disc. For simplicity,
  we only do this for real $q$ with $0 < q < 1$, and we will focus mostly on the theta nullwert
  functions, where the identities are particularly nice (and stay within the reals).

  We introduce the ``$q$ inversion'' function
  \[f : [0,1] \to [0,1],\ f(q) = \exp(\pi^2/\log q)\]
  with the border values $f(0) = 1$ and $f(1) = 0$.
  This function is a strictly decreasing involution on the real interval $[0,1]$. It corresponds
  to translating $q$ from the $q$-disc to the $z$-plane, doing the transformation $z \mapsto -1/z$,
  and then translating the result back into the $q$-disc.

  This is useful for computing $\vartheta_i(q)$, since we can apply the inversion to bring any $q$ 
  in the unit disc very close to $0$, where the power series of $\vartheta_i$ converges extremely
  quickly.
\<close>

definition q_inversion :: "real \<Rightarrow> real" where
  "q_inversion q = (if q = 0 then 1 else if q = 1 then 0 else exp (pi\<^sup>2 / ln q))"

lemma q_inversion_0 [simp]: "q_inversion 0 = 1"
  and q_inversion_1 [simp]: "q_inversion 1 = 0"
  by (simp_all add: q_inversion_def)

lemma q_inversion_nonneg: "q \<in> {0..1} \<Longrightarrow> q_inversion q \<ge> 0"
  and q_inversion_le_1: "q \<in> {0..1} \<Longrightarrow> q_inversion q \<le> 1"
  and q_inversion_pos: "q \<in> {0..<1} \<Longrightarrow> q_inversion q > 0"
  and q_inversion_less_1: "q \<in> {0<..1} \<Longrightarrow> q_inversion q < 1"
  by (auto simp: q_inversion_def field_simps)

lemma q_inversion_strict_antimono: "strict_antimono_on {0..1} q_inversion"
  unfolding monotone_on_def by (auto simp: q_inversion_def field_simps)

lemma q_inversion_less_iff:
  assumes "q \<in> {0..1}" "q' \<in> {0..1}"
  shows   "q_inversion q < q_inversion q' \<longleftrightarrow> q > q'"
  using assms by (auto simp: q_inversion_def field_simps)

lemma q_inversion_le_iff:
  assumes "q \<in> {0..1}" "q' \<in> {0..1}"
  shows   "q_inversion q \<le> q_inversion q' \<longleftrightarrow> q \<ge> q'"
  using assms by (auto simp: q_inversion_def field_simps)

lemma q_inversion_eq_iff:
  assumes "q \<in> {0..1}" "q' \<in> {0..1}"
  shows   "q_inversion q = q_inversion q' \<longleftrightarrow> q = q'"
  using assms by (auto simp: q_inversion_def field_simps)

lemma q_inversion_involution:
  assumes "q \<in> {0..1}"
  shows   "q_inversion (q_inversion q) = q"
  using assms by (auto simp: q_inversion_def)

lemma continuous_q_inversion [continuous_intros]:
  assumes q: "q \<in> {0..1}"
  shows   "continuous (at q within {0..1}) q_inversion"
proof -
  define f where "f = (\<lambda>q. exp (pi ^ 2 / ln q))"

consider "q = 0" | "q = 1" | "q \<in> {0<..<1}"
    using q by force
  hence "(f \<longlongrightarrow> q_inversion q) (at q within {0..1})"
  proof cases
    assume q: "q = 0"
    have "(f \<longlongrightarrow> 1) (at_right 0)"
      unfolding f_def by real_asymp
    thus ?thesis
      by (simp add: q f_def at_within_Icc_at_right)
  next
    assume q: "q = 1"
    have "(f \<longlongrightarrow> 0) (at_left 1)"
      unfolding f_def by real_asymp
    thus ?thesis
      by (simp add: q f_def at_within_Icc_at_left)
  next
    assume q: "q \<in> {0<..<1}"
    have "isCont f q"
      using q unfolding f_def by (auto intro!: continuous_intros)
    hence "(f \<longlongrightarrow> f q) (at q within {0..1})"
      by (meson Lim_at_imp_Lim_at_within continuous_within)
    thus ?thesis
      using q by (simp add: q_inversion_def f_def)
  qed
  moreover have "eventually (\<lambda>q. f q = q_inversion q) (at q within {0..1})"
    using eventually_neq_at_within[of 0] eventually_neq_at_within[of 1]
    by eventually_elim (auto simp: q_inversion_def f_def)
  ultimately have "(q_inversion \<longlongrightarrow> q_inversion q) (at q within {0..1})"
    by (rule Lim_transform_eventually)
  thus ?thesis
    using continuous_within by blast
qed

lemma continuous_on_q_inversion [continuous_intros]: "continuous_on {0..1} q_inversion"
  using continuous_q_inversion continuous_on_eq_continuous_within by blast

lemma continuous_on_q_inversion' [continuous_intros]:
  assumes "continuous_on A f" "\<And>x. x \<in> A \<Longrightarrow> f x \<in> {0..1}"
  shows   "continuous_on A (\<lambda>x. q_inversion (f x))"
  by (rule continuous_on_compose2[OF continuous_on_q_inversion assms(1)]) (use assms(2) in auto)


definition q_inversion_fixedpoint :: real where
  "q_inversion_fixedpoint = exp (-pi)"

lemma q_inversion_fixedpoint:
  defines "q0 \<equiv> q_inversion_fixedpoint"
  shows   "q0 \<in> {0..1}" "q_inversion q0 = q0"
proof -
  show "q0 \<in> {0..1}"
    by (auto simp: q0_def q_inversion_fixedpoint_def)
  show "q_inversion q0 = q0"
    by (auto simp: q_inversion_def q0_def q_inversion_fixedpoint_def field_simps power2_eq_square)
qed

lemma q_inversion_less_self_iff: 
  assumes "q \<in> {0..1}"
  shows   "q_inversion q < q \<longleftrightarrow> q > q_inversion_fixedpoint"
  using q_inversion_less_iff[OF assms q_inversion_fixedpoint(1)] q_inversion_fixedpoint(2)
  by auto

lemma q_inversion_greater_self_iff: 
  assumes "q \<in> {0..1}"
  shows   "q_inversion q > q \<longleftrightarrow> q < q_inversion_fixedpoint"
  using q_inversion_less_iff[OF q_inversion_fixedpoint(1) assms] q_inversion_fixedpoint(2)
  by auto


text \<open>
  From the theta inversion identities, we get three identities of the form
  $\vartheta_i(f(q)) = \sqrt{-\ln q/\pi} \vartheta_j(q)$.
  This can be harnessed to evaluate the theta nullwert functions very rapidly: their power series
  converge extremely quickly for small $q$, and since  $f(q)$ has a unique fixed point 
  $q_0 = e^{-\pi} \approx 0.0432$, we can reduce the computation of theta nullwert functions to 
  computing them for $q$ with $q \leq q_0$ via the inversion formulas.
\<close>

lemma jacobi_theta_nome_inversion_real:
  fixes w q :: real
  assumes q: "q \<in> {0<..<1}" and w: "w > 0"
  shows "jacobi_theta_nome (of_real w) (of_real q) =
           complex_of_real (sqrt (- pi / ln q) * exp (- (ln w)\<^sup>2 / (4 * ln q))) *
           jacobi_theta_nome (cis (-pi * ln w / ln q)) (of_real (exp (pi\<^sup>2 / ln q)))"
proof -
  define x where "x = ln (of_real w) / (2 * pi * \<i>)"
  define y where "y = of_real (ln q) / (pi * \<i>)"
  have w_eq: "w = to_nome x ^ 2"
    using w by (simp add: x_def to_nome_def exp_of_real flip: exp_of_nat_mult)
  have q_eq: "q = to_nome y"
    using q by (simp add: y_def to_nome_def exp_of_real)
  have y: "y \<noteq> 0" "Im y > 0"
    using q by (auto simp: y_def Im_complex_div_gt_0 mult_neg_pos)

  have "jacobi_theta_nome (of_real w) (of_real q) = jacobi_theta_00 x y"
    by (simp add: w_eq q_eq jacobi_theta_00_def flip: jacobi_theta_nome_of_real)
  also have "\<dots> = jacobi_theta_00 x (-(1/(-1/y)))"
    using \<open>y \<noteq> 0\<close> by auto
  also have "\<dots> = csqrt (\<i> / y) * to_nome (- (x\<^sup>2 / y)) * jacobi_theta_00 (-(x/y)) (-(1/y))"
    by (subst jacobi_theta_00_minus_one_over) (use y in \<open>auto simp: Im_complex_div_lt_0\<close>)
  also have "\<i> / y = -of_real (pi / ln q)"
    by (auto simp: y_def field_simps)
  also have "jacobi_theta_00 (-(x/y)) (-(1/y)) =
             jacobi_theta_nome (inverse (to_nome (x / y)) ^ 2) (inverse (to_nome (1 / y)))"
    by (simp add: jacobi_theta_00_def to_nome_power to_nome_minus)
  also have "inverse (to_nome (1 / y)) = exp (of_real (pi ^ 2 / ln q))"
    using q by (simp add: to_nome_def y_def field_simps exp_minus power2_eq_square)
  also have "\<dots> = of_real (exp (pi ^ 2 / ln q))"
    by (rule exp_of_real)
  also have "inverse (to_nome (x / y)) ^ 2 = 
               exp (-\<i> * (complex_of_real pi * Ln (complex_of_real w)) / complex_of_real (ln q))"
    by (simp add: to_nome_def x_def y_def exp_minus field_simps flip: exp_of_nat_mult)
  also have "-\<i> * (complex_of_real pi * Ln (complex_of_real w)) / complex_of_real (ln q) =
             -\<i> * complex_of_real (pi * ln w / ln q)"
    using q w by (subst Ln_of_real') (auto simp: field_simps power2_eq_square)
  also have "exp \<dots> = cis (-pi * ln w / ln q)"
    by (auto simp: exp_diff exp_add cis_conv_exp exp_minus field_simps)
  also have "csqrt (- complex_of_real (pi / ln q)) = csqrt (of_real (-pi / ln q))"
    by simp
  also have "\<dots> = of_real (sqrt (-pi / ln q))"
    by (subst of_real_sqrt) (use q in \<open>auto simp: field_simps\<close>)
  also have "to_nome (- (x\<^sup>2 / y)) = exp (-(ln (of_real w) ^ 2 / of_real (4 * ln q)))"
    unfolding x_def y_def by (simp add: field_simps to_nome_def power2_eq_square)
  also have "-(ln (complex_of_real w) ^ 2 / of_real (4 * ln q)) =
                of_real (-(ln w ^ 2) / (4 * ln q))"
    by (subst Ln_of_real') (use w q in \<open>auto simp: field_simps power2_eq_square\<close>)
  also have "exp \<dots> = complex_of_real (exp (-(ln w ^ 2) / (4 * ln q)))"
    by (rule exp_of_real)
  finally show ?thesis by simp
qed

lemma jacobi_theta_nome_1_left_inversion_real:
  assumes q: "q \<in> {0..<1}"
  shows "jacobi_theta_nome 1 (q_inversion q) = sqrt (-ln q / pi) * jacobi_theta_nome 1 q"
proof (cases "q = 0")
  case False
  with assms have q: "q \<in> {0<..<1}"
    by auto
  have "complex_of_real (jacobi_theta_nome 1 q) = jacobi_theta_nome (of_real 1) (of_real q)"
    by (simp flip: jacobi_theta_nome_of_real)
  also have "\<dots> = of_real (sqrt (-pi / ln q) * jacobi_theta_nome 1 (exp (pi\<^sup>2 / ln q)))"
    by (subst jacobi_theta_nome_inversion_real) (use q in \<open>auto simp flip: jacobi_theta_nome_of_real\<close>)
  finally have "jacobi_theta_nome 1 q = sqrt (-pi / ln q) * jacobi_theta_nome 1 (q_inversion q)"
    unfolding of_real_eq_iff q_inversion_def using q by simp
  thus ?thesis
    using q by (simp add: real_sqrt_divide field_simps real_sqrt_minus)
qed auto

lemma jacobi_theta_nw_00_inversion_real:
  assumes q: "q \<in> {0..<1::real}"
  shows   "jacobi_theta_nw_00 (q_inversion q) = sqrt (-ln q / pi) * jacobi_theta_nw_00 q"
  unfolding jacobi_theta_nome_00_def power_one
  by (subst jacobi_theta_nome_1_left_inversion_real [OF q]) auto

lemma jacobi_theta_nw_01_inversion_real:
  assumes q: "q \<in> {0..<1::real}"
  shows   "jacobi_theta_nw_01 (q_inversion q) = sqrt (-ln q / pi) * jacobi_theta_nw_10 q"
proof (cases "q = 0")
  case False
  with assms have q: "q \<in> {0<..<1}"
    by auto
  have "complex_of_real (jacobi_theta_nw_10 q) = 
          of_real (q powr (1/4)) * jacobi_theta_nome (of_real q) (of_real q)"
    by (simp add: jacobi_theta_nome_10_def jacobi_theta_nome_of_real)
  also have "\<dots> = of_real (sqrt (-(pi/ln q))) *
                   jacobi_theta_nome (-1) (complex_of_real (exp (pi\<^sup>2 / ln q)))"
    by (subst jacobi_theta_nome_inversion_real) 
       (use q in \<open>auto simp flip: cis_inverse simp: power2_eq_square powr_def exp_minus\<close>)
  also have "\<dots> = complex_of_real (sqrt (-pi/ln q) * jacobi_theta_nw_01 (exp (pi\<^sup>2 / ln q)))"
    by (simp flip: jacobi_theta_nome_of_real add: jacobi_theta_nome_01_def)
  finally have "jacobi_theta_nw_10 q = sqrt (-pi / ln q) * jacobi_theta_nw_01 (q_inversion q)"
    unfolding of_real_eq_iff q_inversion_def using q by simp
  thus ?thesis
    using q by (simp add: real_sqrt_divide field_simps real_sqrt_minus)
qed auto
  
lemma jacobi_theta_nw_10_inversion_real:
  assumes q: "q \<in> {0<..1::real}"
  shows   "jacobi_theta_nw_10 (q_inversion q) = sqrt (-ln q / pi) * jacobi_theta_nw_01 q"
proof -
  have "jacobi_theta_nw_01 q = jacobi_theta_nw_01 (q_inversion (q_inversion q))"
    using q by (simp add: q_inversion_involution)
  also have "\<dots> = sqrt (-ln (q_inversion q) / pi) * jacobi_theta_nw_10 (q_inversion q)"
    by (subst jacobi_theta_nw_01_inversion_real) 
       (use q in \<open>auto simp: q_inversion_less_1 q_inversion_nonneg\<close>)
  also have "-ln (q_inversion q) / pi = -pi / ln q"
    using q by (simp add: q_inversion_def power2_eq_square)
  finally show ?thesis
    using q by (simp add: real_sqrt_divide field_simps real_sqrt_minus)
qed  

end
