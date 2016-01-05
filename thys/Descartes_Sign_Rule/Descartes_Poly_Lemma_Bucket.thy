(*
  File:    Descartes_Poly_Lemma_Bucket.thy
  Author:  Manuel Eberl <eberlm@in.tum.de>

  Auxiliary facts about polynomials.
*)
section \<open>Auxiliary lemmas\<close>

theory Descartes_Poly_Lemma_Bucket
imports 
  Main 
  "~~/src/HOL/Library/Polynomial" 
  "../Sturm_Tarski/PolyMisc"
begin

subsection \<open>Miscellaneous facts\<close>

lemma order_0I: "poly p a \<noteq> 0 \<Longrightarrow> order a p = 0"
  by (subst (asm) order_root) auto

lemma length_coeffs: "p \<noteq> 0 \<Longrightarrow> length (coeffs p) = degree p + 1"
  by (simp add: coeffs_def)
  
lemma Poly_snoc: "Poly (xs @ [x]) = Poly xs + monom x (length xs)"
  by (induction xs) (simp_all add: monom_0 monom_Suc)

lemma coeffs_nth:
  assumes "p \<noteq> 0" "n \<le> degree p"
  shows   "coeffs p ! n = coeff p n"
  using assms unfolding coeffs_def by (auto simp del: upt_Suc)

lemma degree_Poly: "degree (Poly xs) \<le> length xs"
  by (induction xs) simp_all

lemma of_nat_poly: "of_nat n = [:of_nat n :: 'a :: comm_semiring_1:]"
proof (induction n)
  case (Suc n)
  hence "of_nat (Suc n) = 1 + (of_nat n :: 'a poly)" 
    by simp
  also have "(of_nat n :: 'a poly) = [: of_nat n :]" 
    by (subst Suc) (rule refl)
  also have "1 = [:1:]" by (simp add: one_poly_def)
  finally show ?case by (subst (asm) add_pCons) simp
qed simp

lemma degree_of_nat [simp]: "degree (of_nat n) = 0"
  by (simp add: of_nat_poly)

lemma degree_numeral [simp]: "degree (numeral n) = 0"
  by (subst of_nat_numeral [symmetric], subst of_nat_poly) simp

lemma numeral_poly: "numeral n = [:numeral n:]"
  unfolding lead_coeff_def
  by (subst of_nat_numeral [symmetric], subst of_nat_poly) simp


subsection \<open>The leading coefficient\<close>

lemma lead_coeff_smult: 
  "lead_coeff (smult c p :: 'a :: idom poly) = c * lead_coeff p"
proof -
  have "smult c p = [:c:] * p" by simp
  also have "lead_coeff \<dots> = c * lead_coeff p" 
    by (subst lead_coeff_mult) simp_all
  finally show ?thesis .
qed

lemma lead_coeff_1 [simp]: "lead_coeff 1 = 1"
  by (simp add: lead_coeff_def)

lemma lead_coeff_of_nat [simp]:
  "lead_coeff (of_nat n) = (of_nat n :: 'a :: {comm_semiring_1,semiring_char_0})"
  by (induction n) (simp_all add: lead_coeff_def of_nat_poly)

lemma lead_coeff_numeral [simp]: 
  "lead_coeff (numeral n) = numeral n"
  unfolding lead_coeff_def
  by (subst of_nat_numeral [symmetric], subst of_nat_poly) simp

lemma lead_coeff_power: 
  "lead_coeff (p ^ n :: 'a :: idom poly) = lead_coeff p ^ n"
  by (induction n) (simp_all add: lead_coeff_mult)

lemma lead_coeff_nonzero: "p \<noteq> 0 \<Longrightarrow> lead_coeff p \<noteq> 0"
  by (simp add: lead_coeff_def)


subsection \<open>Existence of positive real roots\<close> 

text\<open>
  A real polynomial whose leading and constant coefficients have opposite
  non-zero signs must have a positive root.
\<close>
lemma pos_root_exI:
  assumes "poly p 0 * lead_coeff p < (0 :: real)"
  obtains x where "x > 0" "poly p x = 0"
proof -
  {
    fix p :: "real poly" assume p: "poly p 0 < 0"
    assume "lead_coeff p > 0"
    also from poly_pinfty_gt_lc[OF \<open>lead_coeff p > 0\<close>] obtain x0 
      where "\<And>x. x \<ge> x0 \<Longrightarrow> poly p x \<ge> lead_coeff p" by auto
    hence "poly p (max x0 1) \<ge> lead_coeff p" by auto
    finally have "poly p (max x0 1) > 0" .
    with p have "\<exists>x. x > 0 \<and> x < max x0 1 \<and> poly p x = 0"
      by (intro poly_IVT mult_neg_pos) auto
    hence "\<exists>x>0. poly p x = 0"  by auto
  } note P = this

  show ?thesis
  proof (cases "lead_coeff p > 0")
    case True
    with assms have "poly p 0 < 0" 
      by (auto simp: mult_less_0_iff)
    from P[OF this True] that show ?thesis 
      by blast
  next
    case False
    from False assms have "poly (-p) 0 < 0" 
      by (auto simp: mult_less_0_iff)
    moreover from assms have "p \<noteq> 0"
      by auto
    with False have "lead_coeff (-p) > 0" 
      by (cases rule: linorder_cases[of "lead_coeff p" 0]) 
         (simp_all add: lead_coeff_def)
    ultimately show ?thesis using that P[of "-p"] by auto
  qed
qed


text \<open>
  An induction rule for induction over the roots of a polynomial with a certain property. 
  (e.g. all positive roots)
\<close>
lemma poly_root_induct [case_names 0 no_roots root]:
  fixes p :: "'a :: idom poly"
  assumes "Q 0"
  assumes "\<And>p. (\<And>a. P a \<Longrightarrow> poly p a \<noteq> 0) \<Longrightarrow> Q p"
  assumes "\<And>a p. P a \<Longrightarrow> Q p \<Longrightarrow> Q ([:a, -1:] * p)"
  shows   "Q p"
proof (induction "degree p" arbitrary: p rule: less_induct)
  case (less p)
  show ?case
  proof (cases "p = 0")
    assume nz: "p \<noteq> 0"
    show ?case
    proof (cases "\<exists>a. P a \<and> poly p a = 0")
      case False
      thus ?thesis by (intro assms(2)) blast
    next
      case True
      then obtain a where a: "P a" "poly p a = 0" 
        by blast
      hence "-[:-a, 1:] dvd p" 
        by (subst minus_dvd_iff) (simp add: poly_eq_0_iff_dvd)
      then obtain q where q: "p = [:a, -1:] * q" by (elim dvdE) simp
      with nz have q_nz: "q \<noteq> 0" by auto
      have "degree p = Suc (degree q)"
        by (subst q, subst degree_mult_eq) (simp_all add: q_nz)
      hence "Q q" by (intro less) simp
      from a(1) and this have "Q ([:a, -1:] * q)" 
        by (rule assms(3))
      with q show ?thesis by simp
    qed
  qed (simp add: assms(1))
qed


lemma dropWhile_replicate_append: 
  "dropWhile (op= a) (replicate n a @ ys) = dropWhile (op= a) ys"
  by (induction n) simp_all

lemma Poly_append_replicate_0: "Poly (xs @ replicate n 0) = Poly xs"
  by (subst coeffs_eq_iff) (simp_all add: strip_while_def dropWhile_replicate_append)

text \<open>
  An induction rule for simultaneous induction over two polynomials, 
  prepending one coefficient in each step.
\<close>
lemma poly_induct2 [case_names 0 pCons]:
  assumes "P 0 0" "\<And>a p b q. P p q \<Longrightarrow> P (pCons a p) (pCons b q)"
  shows   "P p q"
proof -
  def n \<equiv> "max (length (coeffs p)) (length (coeffs q))"
  def xs \<equiv> "coeffs p @ (replicate (n - length (coeffs p)) 0)"
  def ys \<equiv> "coeffs q @ (replicate (n - length (coeffs q)) 0)"
  have "length xs = length ys" 
    by (simp add: xs_def ys_def n_def)
  hence "P (Poly xs) (Poly ys)" 
    by (induction rule: list_induct2) (simp_all add: assms)
  also have "Poly xs = p" 
    by (simp add: xs_def Poly_append_replicate_0)
  also have "Poly ys = q" 
    by (simp add: ys_def Poly_append_replicate_0)
  finally show ?thesis .
qed

lemma pcompose_add:
  fixes p q r :: "'a :: {comm_semiring_0, ab_semigroup_add} poly"
  shows "pcompose (p + q) r = pcompose p r + pcompose q r"
proof (induction p q rule: poly_induct2)
  case (pCons a p b q)
  have "pcompose (pCons a p + pCons b q) r = 
          [:a + b:] + r * pcompose p r + r * pcompose q r"
    by (simp_all add: pcompose_pCons pCons.IH algebra_simps)
  also have "[:a + b:] = [:a:] + [:b:]" by simp
  also have "\<dots> + r * pcompose p r + r * pcompose q r = 
                 pcompose (pCons a p) r + pcompose (pCons b q) r"
    by (simp only: pcompose_pCons add_ac)
  finally show ?case .
qed simp


subsection \<open>Polynomial composition\<close>

lemma pcompose_minus:
  fixes p r :: "'a :: comm_ring poly"
  shows "pcompose (-p) r = -pcompose p r"
  by (induction p) (simp_all add: pcompose_pCons)

lemma pcompose_diff:
  fixes p q r :: "'a :: comm_ring poly"
  shows "pcompose (p - q) r = pcompose p r - pcompose q r"
  using pcompose_add[of p "-q"] by (simp add: pcompose_minus)

lemma pcompose_smult:
  fixes p r :: "'a :: comm_semiring_0 poly"
  shows "pcompose (smult a p) r = smult a (pcompose p r)"
  by (induction p) 
     (simp_all add: pcompose_pCons pcompose_add smult_add_right)

lemma pcompose_mult:
  fixes p q r :: "'a :: comm_semiring_0 poly"
  shows "pcompose (p * q) r = pcompose p r * pcompose q r"
  by (induction p arbitrary: q)
     (simp_all add: pcompose_add pcompose_smult pcompose_pCons algebra_simps)

lemma pcompose_assoc: 
  "pcompose p (pcompose q r :: 'a :: comm_semiring_0 poly ) =
     pcompose (pcompose p q) r"
  by (induction p arbitrary: q) 
     (simp_all add: pcompose_pCons pcompose_add pcompose_mult)


text \<open>
  Substitute $X$ with $aX$ in a polynomial $p(X)$. This turns all the $X - a$ factors in $p$
  into factors of the form $X - 1$.
\<close>
definition reduce_root where
  "reduce_root a p = pcompose p [:0, a:]"

lemma reduce_root_pCons: 
  "reduce_root a (pCons c p) = pCons c (smult a (reduce_root a p))"
  by (simp add: reduce_root_def pcompose_pCons)

lemma reduce_root_nonzero [simp]: 
  "a \<noteq> 0 \<Longrightarrow> p \<noteq> 0 \<Longrightarrow> reduce_root a p \<noteq> (0 :: 'a :: idom poly)"
  unfolding reduce_root_def using pcompose_eq_0[of p "[:0, a:]"] 
  by auto
  
end