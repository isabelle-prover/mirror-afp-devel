subsection \<open>Exact Division of Multivariate Polynomials\<close>

theory MPoly_Divide
  imports
    Hermite_Lindemann.More_Multivariate_Polynomial_HLW
    Polynomials.MPoly_Type_Class
    Poly_Connection
begin

lemma poly_lead_coeff_dvd_lead_coeff:
  assumes "p dvd (q :: 'a :: idom poly)"
  shows   "Polynomial.lead_coeff p dvd Polynomial.lead_coeff q"
  using assms by (elim dvdE) (auto simp: Polynomial.lead_coeff_mult)


text \<open>
  Since there is no particularly sensible algorithm for division with a remainder on
  multivariate polynomials, we define the following division operator that performs an
  exact division if possible and returns 0 otherwise.
\<close>

instantiation mpoly :: ("comm_semiring_1") divide
begin

definition divide_mpoly :: "'a mpoly \<Rightarrow> 'a mpoly \<Rightarrow> 'a mpoly" where
  "divide_mpoly x y = (if y \<noteq> 0 \<and> y dvd x then THE z. x = y * z else 0)"

instance ..

end

instance mpoly :: (idom) idom_divide
  by standard (auto simp: divide_mpoly_def)



lemma (in transfer_mpoly_to_mpoly_poly) transfer_div [transfer_rule]:
  assumes [transfer_rule]: "R p' p" "R q' q"
  assumes "q dvd p"
  shows   "R (p' div q') (p div q)"
  using assms
  by (smt (z3) div_by_0 dvd_imp_mult_div_cancel_left mpoly_to_mpoly_poly_0 mpoly_to_mpoly_poly_eq_iff
        mpoly_to_mpoly_poly_mult nonzero_mult_div_cancel_left transfer_mpoly_to_mpoly_poly.R_def)


instantiation mpoly :: ("{normalization_semidom, idom}") normalization_semidom
begin

definition unit_factor_mpoly :: "'a mpoly \<Rightarrow> 'a mpoly" where
  "unit_factor_mpoly p = Const (unit_factor (lead_coeff p))"

definition normalize_mpoly :: "'a mpoly \<Rightarrow> 'a mpoly" where
  "normalize_mpoly p = Rings.divide p (unit_factor p)"

lemma unit_factor_mpoly_Const [simp]:
  "unit_factor (Const c) = Const (unit_factor c)"
  unfolding unit_factor_mpoly_def by simp

lemma normalize_mpoly_Const [simp]:
  "normalize (Const c) = Const (normalize c)"
proof (cases "c = 0")
  case False
  have "normalize (Const c) = Const c div Const (unit_factor c)"
    by (simp add: normalize_mpoly_def)
  also have "\<dots> = Const (unit_factor c * normalize c) div Const (unit_factor c)"
    by simp
  also have "\<dots> = Const (unit_factor c) * Const (normalize c) div Const (unit_factor c)"
    by (subst mpoly_Const_mult) auto
  also have "\<dots> = Const (normalize c)"
    using \<open>c \<noteq> 0\<close>
    by (subst nonzero_mult_div_cancel_left) auto
  finally show ?thesis .
qed (auto simp: normalize_mpoly_def)

instance proof
  show "unit_factor (0 :: 'a mpoly) = 0"
    by (simp add: unit_factor_mpoly_def)
next
  show "unit_factor x = x" if "x dvd 1" for x :: "'a mpoly"
    using that by (auto elim!: mpoly_is_unitE simp: is_unit_unit_factor)
next
  fix x :: "'a mpoly"
  assume "x \<noteq> 0"
  thus "unit_factor x dvd 1"
    by (auto simp: unit_factor_mpoly_def)
next
  fix x y :: "'a mpoly"
  assume "x dvd 1"
  hence "x \<noteq> 0"
    by auto
  show "unit_factor (x * y) = x * unit_factor y"
  proof (cases "y = 0")
    case False
    have "Const (unit_factor (lead_coeff x * lead_coeff y)) =
            x * Const (unit_factor (lead_coeff y))" using \<open>x dvd 1\<close>
      by (subst unit_factor_mult_unit_left)
         (auto elim!: mpoly_is_unitE simp: mpoly_Const_mult)
    thus ?thesis using \<open>x \<noteq> 0\<close> False
      by (simp add: unit_factor_mpoly_def lead_coeff_mult)
  qed (auto simp: unit_factor_mpoly_def)
next
  fix p :: "'a mpoly"
  let ?c = "Const (unit_factor (lead_coeff p))"
  show "unit_factor p * normalize p = p"
  proof (cases "p = 0")
    case False
    hence "?c dvd 1"
      by (intro is_unit_ConstI) auto
    also have "1 dvd p"
      by simp
    finally have "?c * (p div ?c) = p"
      by (rule dvd_imp_mult_div_cancel_left)
    thus ?thesis
      by (auto simp: unit_factor_mpoly_def normalize_mpoly_def)
  qed (auto simp: normalize_mpoly_def)
next
  show "normalize (0 :: 'a mpoly) = 0"
    by (simp add: normalize_mpoly_def)
qed

end



text \<open>
  The following is an exact division operator that can fail, i.e.\ if the divisor does not
  divide the dividend, it returns \<^const>\<open>None\<close>.
\<close>

definition divide_option :: "'a :: idom_divide \<Rightarrow> 'a \<Rightarrow> 'a option"  (infixl "div?" 70) where
  "divide_option p q = (if q dvd p then Some (p div q) else None)"

text \<open>
  We now show that exact division on the ring $R[X_1,\ldots, X_n]$ can be reduced to
  exact division on the ring $R[X_1,\ldots,X_n][X]$, i.e.\ we can go from \<^typ>\<open>'a mpoly\<close> to
  a \<^typ>\<open>'a mpoly poly\<close> where the coefficients have one variable less than the original
  multivariate polynomial. We basically simply use the isomorphism between these two rings.
\<close>

lemma divide_option_mpoly:
  fixes p q :: "'a :: idom_divide mpoly"
  shows "p div? q = (let V = vars p \<union> vars q in
           (if V = {} then
              let a = MPoly_Type.coeff p 0; b = MPoly_Type.coeff q 0; c = a div b
              in  if b * c = a then Some (Const c) else None
            else
              let x = Max V;
                  p' = mpoly_to_mpoly_poly x p; q' = mpoly_to_mpoly_poly x q
              in  case p' div? q' of
                    None \<Rightarrow> None
                  | Some r \<Rightarrow> Some (poly r (Var x))))" (is "_ = ?rhs")
proof -
  define x where "x = Max (vars p \<union> vars q)"
  define p' where "p' = mpoly_to_mpoly_poly x p"
  define q' where "q' = mpoly_to_mpoly_poly x q"
  interpret transfer_mpoly_to_mpoly_poly x .
  have [transfer_rule]: "R p' p" "R q' q"
    by (auto simp: p'_def q'_def R_def)

  show ?thesis
  proof (cases "vars p \<union> vars q = {}")
    case True
    define a where "a = MPoly_Type.coeff p 0"
    define b where "b = MPoly_Type.coeff q 0"
    have [simp]: "p = Const a" "q = Const b"
      using True by (auto elim!: vars_emptyE simp: a_def b_def mpoly_coeff_Const)
    show ?thesis
      apply (cases "b = 0")
       apply (auto simp: Let_def mpoly_coeff_Const mpoly_Const_mult divide_option_def elim!: dvdE)
      by (metis dvd_triv_left)
  next
    case False
    have "?rhs =
            (case p' div? q' of None \<Rightarrow> None
              | Some r \<Rightarrow> Some (poly r (Var x)))"
      using False
      unfolding Let_def
      apply (simp only: )
      apply (subst if_False)
      apply (simp flip: x_def p'_def q'_def cong: option.case_cong)
      done
    also have "\<dots> = (if q' dvd p' then Some (poly (p' div q') (Var x)) else None)"
      using False by (auto simp: divide_option_def)
    also have "\<dots> = p div? q"
      unfolding divide_option_def
    proof (intro if_cong refl arg_cong[where f = Some])
      show "(q' dvd p') = (q dvd p)"
        by transfer_prover
    next
      assume [transfer_rule]: "q dvd p"
      have "R (p' div q') (p div q)"
        by transfer_prover
      thus "poly (p' div q') (Var x) = p div q"
        by (simp add: R_def poly_mpoly_to_mpoly_poly)
    qed
    finally show ?thesis ..
  qed
qed

text \<open>
  Next, we show that exact division on the ring $R[X_1,\ldots,X_n][Y]$ can be reduced to
  exact division on the ring $R[X_1,\ldots,X_n]$. This is essentially just polynomial division.
\<close>
lemma divide_option_mpoly_poly:
  fixes p q :: "'a :: idom_divide mpoly poly"
  shows "p div? q =
            (if p = 0 then Some 0
            else if q = 0 then None
            else let dp = Polynomial.degree p; dq = Polynomial.degree q
                 in  if dp < dq then None
                     else case Polynomial.lead_coeff p div? Polynomial.lead_coeff q of
                            None \<Rightarrow> None
                          | Some c \<Rightarrow> (
                              case (p - Polynomial.monom c (dp - dq) * q) div? q of
                                None \<Rightarrow> None
                              | Some r \<Rightarrow> Some (Polynomial.monom c (dp - dq) + r)))"
  (is "_ = ?rhs")
proof (cases "p = 0"; cases "q = 0")
  assume [simp]: "p \<noteq> 0" "q \<noteq> 0"
  define dp where "dp = Polynomial.degree p"
  define dq where "dq = Polynomial.degree q"
  define cp where "cp = Polynomial.lead_coeff p"
  define cq where "cq = Polynomial.lead_coeff q"
  define mon where "mon = Polynomial.monom (cp div cq) (dp - dq)"
  show ?thesis
  proof (cases "dp < dq")
    case True
    hence "\<not>q dvd p"
      unfolding dp_def dq_def
      by (meson \<open>p \<noteq> 0\<close> divides_degree leD)
    thus ?thesis
      using True by (simp add: divide_option_def dp_def dq_def)
  next
    case deg: False
    show ?thesis
    proof (cases "cq dvd cp")
      case False
      hence "\<not>q dvd p"
        unfolding cq_def cp_def using poly_lead_coeff_dvd_lead_coeff by blast
      thus ?thesis
        using deg False by (simp add: dp_def dq_def Let_def divide_option_def cp_def cq_def)
    next
      case dvd1: True
      show ?thesis
      proof (cases "q dvd (p - mon * q)")
        case False
        hence "\<not>q dvd p"
          by (meson dvd_diff dvd_triv_right)
        thus ?thesis
          using deg dvd1 False
          by (simp add: dp_def dq_def Let_def divide_option_def cp_def cq_def mon_def)
      next
        case dvd2: True
        hence "q dvd p"
          by (metis diff_eq_eq dvd_add dvd_triv_right)
        have "?rhs = Some (mon + (p - mon * q) div q)"
          using deg dvd1 dvd2
          by (simp add: dp_def dq_def Let_def divide_option_def cp_def cq_def mon_def)
        also have "mon + (p - mon * q) div q = p div q"
          using dvd2 by (elim dvdE) (auto simp: algebra_simps)
        also have "Some \<dots> = p div? q"
          using \<open>q dvd p\<close> by (simp add: divide_option_def)
        finally show ?thesis ..
      qed
    qed
  qed
qed (auto simp: divide_option_def)

text \<open>
  These two equations now serve as two mutually recursive code equations that allow us to
  reduce exact division of multivariate polynomials to exact division of their coefficients.
  Termination of these code equations is not shown explicitly, but is obvious since one variable
  is eliminated in every step.
\<close>

definition divide_option_mpoly :: "'a :: idom_divide mpoly \<Rightarrow> _"
  where "divide_option_mpoly = divide_option"

definition divide_option_mpoly_poly :: "'a :: idom_divide mpoly poly \<Rightarrow> _"
  where "divide_option_mpoly_poly = divide_option"

lemmas divide_option_mpoly_code [code] =
  divide_option_mpoly [folded divide_option_mpoly_def divide_option_mpoly_poly_def]

lemmas divide_option_mpoly_poly_code [code] =
  divide_option_mpoly_poly [folded divide_option_mpoly_def divide_option_mpoly_poly_def]

lemma divide_mpoly_code [code]:
  fixes p q :: "'a :: idom_divide mpoly"
  shows "p div q = (case divide_option_mpoly p q of None \<Rightarrow> 0 | Some r \<Rightarrow> r)"
  by (auto simp: divide_option_mpoly_def divide_option_def divide_mpoly_def)

end
