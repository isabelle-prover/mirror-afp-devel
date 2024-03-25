(*
  File:     Continued_Fractions/Continued_Fraction_Approximation.thy
  Author:   Manuel Eberl, University of Innsbruck
*)
section \<open>Computing continued fraction expansions through interval arithmetic\<close>
theory Continued_Fraction_Approximation
imports
  Complex_Main
  "HOL-Decision_Procs.Approximation"
  "Coinductive.Coinductive_List"
  "HOL-Library.Code_Lazy"
  "HOL-Library.Code_Target_Numeral"
  Continued_Fractions
keywords "approximate_cfrac" :: diag
begin

text \<open>
  The approximation package allows us to compute an enclosing interval for a given
  real constant. From this, we are able to compute an initial fragment of the continued
  fraction expansion of the number.

  The algorithm essentially works by computing the continued fraction expansion of the lower
  and upper bound simultaneously and stopping when the results start to diverge.

  This algorithm terminates because the lower and upper bounds, being rational numbers, have
  a finite continued fraction expansion.
\<close>

definition float_to_rat :: "float \<Rightarrow> int \<times> int" where
  "float_to_rat f = (if exponent f \<ge> 0 then
     (mantissa f * 2 ^ nat (exponent f), 1) else (mantissa f, 2 ^ nat (-exponent f)))"

lemma float_to_rat: "fst (float_to_rat f) / snd (float_to_rat f) = real_of_float f"
  by (auto simp: float_to_rat_def mantissa_exponent powr_int)

lemma snd_float_to_rat_pos [simp]: "snd (float_to_rat f) > 0"
  by (simp add: float_to_rat_def)


function cfrac_from_approx :: "int \<times> int \<Rightarrow> int \<times> int \<Rightarrow> int list" where
  "cfrac_from_approx (nl, dl) (nu, du) =
     (if nl = 0 \<or> nu = 0 \<or> dl = 0 \<or> du = 0 then []
      else let l = nl div dl; u = nu div du
           in  if l \<noteq> u then []
               else l # (let m = nl mod dl in if m = 0 then [] else
                           cfrac_from_approx (du, nu mod du) (dl, m)))"
  by auto
termination proof (relation "measure (\<lambda>((nl, dl), (nu, du)). nat (abs dl + abs du))", goal_cases)
  case (2 nl dl nu du)
  hence "\<bar>nl mod dl\<bar> + \<bar>nu mod du\<bar> < \<bar>dl\<bar> + \<bar>du\<bar>"
    by (intro add_strict_mono) (auto simp: abs_mod_less)
  thus ?case using 2 by simp
qed auto

lemmas [simp del] = cfrac_from_approx.simps

lemma cfrac_from_approx_correct:
  assumes "x \<in> {fst l / snd l..fst u / snd u}" and "snd l > 0" and "snd u > 0"
  assumes "i < length (cfrac_from_approx l u)"
  shows   "cfrac_nth (cfrac_of_real x) i = cfrac_from_approx l u ! i"
  using assms
proof (induction l u arbitrary: i x rule: cfrac_from_approx.induct)
  case (1 nl dl nu du i x)
  from "1.prems" have *: "nl div dl = nu div du" "nl \<noteq> 0" "nu \<noteq> 0" "dl > 0" "du > 0"
    by (auto simp: cfrac_from_approx.simps Let_def split: if_splits)
  have "\<lfloor>nl / dl\<rfloor> \<le> \<lfloor>x\<rfloor>" "\<lfloor>x\<rfloor> \<le> \<lfloor>nu / du\<rfloor>"
    using "1.prems"(1) by (intro floor_mono; simp)+
  hence "nl div dl \<le> \<lfloor>x\<rfloor>" "\<lfloor>x\<rfloor> \<le> nu div du"
    by (simp_all add: floor_divide_of_int_eq)
  with * have "\<lfloor>x\<rfloor> = nu div du"
    by linarith

  show ?case
  proof (cases i)
    case 0
    with 0 and \<open>\<lfloor>x\<rfloor> = _\<close> show ?thesis using "1.prems"
      by (auto simp: Let_def cfrac_from_approx.simps)
  next
    case [simp]: (Suc i')
    from "1.prems" * have "nl mod dl \<noteq> 0"
      by (subst (asm) cfrac_from_approx.simps) (auto split: if_splits)
    have frac_eq: "frac x = x - nu div du"
      using \<open>\<lfloor>x\<rfloor> = _\<close> by (simp add: frac_def)

    have "frac x \<ge> nl / dl - nl div dl"
      using * "1.prems" by (simp add: frac_eq)
    also have "nl / dl - nl div dl = (nl - dl * (nl div dl)) / dl"
      using * by (simp add: field_simps)
    also have "nl - dl * (nl div dl) = nl mod dl"
      by (subst minus_div_mult_eq_mod [symmetric]) auto
    finally have "frac x \<ge> (nl mod dl) / dl" .

    have "nl mod dl \<ge> 0"
      using * by (intro pos_mod_sign) auto
    with \<open>nl mod dl \<noteq> 0\<close> have "nl mod dl > 0"
      by linarith
    hence "0 < (nl mod dl) / dl"
      using * by (intro divide_pos_pos) auto
    also have "\<dots> \<le> frac x"
      by fact
    finally have "frac x > 0" .

    have "frac x \<le> nu / du - nu div du"
      using * "1.prems" by (simp add: frac_eq)
    also have "\<dots> = (nu - du * (nu div du)) / du"
      using * by (simp add: field_simps)
    also have "nu - du * (nu div du) = nu mod du"
      by (subst minus_div_mult_eq_mod [symmetric]) auto
    finally have "frac x \<le> real_of_int (nu mod du) / real_of_int du" .

    have "0 < frac x"
      by fact
    also have "\<dots> \<le> (nu mod du) / du"
      by fact
    finally have "nu mod du > 0"
      using * by (auto simp: field_simps)

    have "cfrac_nth (cfrac_of_real x) i = cfrac_nth (cfrac_tl (cfrac_of_real x)) i'"
      by simp
    also have "cfrac_tl (cfrac_of_real x) = cfrac_of_real (1 / frac x)"
      using \<open>frac x > 0\<close> by (intro cfrac_tl_of_real) auto
    also have "cfrac_nth (cfrac_of_real (1 / frac x)) i' =
               cfrac_from_approx (du, nu mod du) (dl, nl mod dl) ! i'"
    proof (rule "1.IH"[OF _ refl refl _ refl])
      show "\<not> (nl = 0 \<or> nu = 0 \<or> dl = 0 \<or> du = 0)" "\<not> nl div dl \<noteq> nu div du"
        using "1.prems" by (auto split: if_splits simp: Let_def cfrac_from_approx.simps)
    next
      show "i' < length (cfrac_from_approx (du, nu mod du) (dl, nl mod dl))" using "1.prems"
        by (subst (asm) cfrac_from_approx.simps) (auto split: if_splits simp: Let_def)
    next
      have "1 / frac x \<le> dl / (nl mod dl)"
        using \<open>frac x > 0\<close> and \<open>nl mod dl > 0\<close> and \<open>frac x \<ge> (nl mod dl) / dl\<close> and *
        by (auto simp: field_simps)
      moreover have "1 / frac x \<ge> du / (nu mod du)"
        using \<open>frac x > 0\<close> and \<open>nu mod du > 0\<close> and \<open>frac x \<le> (nu mod du) / du\<close> and *
        by (auto simp: field_simps)
      ultimately show
         "1 / frac x \<in> {real_of_int (fst (du, nu mod du)) / real_of_int (snd (du, nu mod du))..
                         real_of_int (fst (dl, nl mod dl)) / real_of_int (snd (dl, nl mod dl))}"
        by simp
      show "snd (du, nu mod du) > 0" "snd (dl, nl mod dl) > 0" and "nl mod dl \<noteq> 0"
        using \<open>nu mod du > 0\<close> and \<open>nl mod dl > 0\<close> by simp_all
    qed
    also have "cfrac_from_approx (du, nu mod du) (dl, nl mod dl) ! i' =
               cfrac_from_approx (nl, dl) (nu, du) ! i"
      using "1.prems" *  \<open>nl mod dl \<noteq> 0\<close> by (subst (2) cfrac_from_approx.simps) auto
    finally show ?thesis .
  qed
qed

definition cfrac_from_approx' :: "float \<Rightarrow> float \<Rightarrow> int list" where
  "cfrac_from_approx' l u = cfrac_from_approx (float_to_rat l) (float_to_rat u)"

lemma cfrac_from_approx'_correct:
  assumes "x \<in> {real_of_float l..real_of_float u}"
  assumes "i < length (cfrac_from_approx' l u)"
  shows   "cfrac_nth (cfrac_of_real x) i = cfrac_from_approx' l u ! i"
  using assms unfolding cfrac_from_approx'_def
  by (intro cfrac_from_approx_correct) (auto simp: float_to_rat cfrac_from_approx'_def)

definition approx_cfrac :: "nat \<Rightarrow> floatarith \<Rightarrow> int list" where
  "approx_cfrac prec e =
     (case approx' prec e [] of
        None \<Rightarrow> []
      | Some ivl \<Rightarrow> cfrac_from_approx' (lower ivl) (upper ivl))"

ML_file \<open>approximation_cfrac.ML\<close>


text \<open>Now let us do some experiments:\<close>

value "let prec = 34; c = cfrac_from_approx' (lb_pi prec) (ub_pi prec) in c"
value "let prec = 34; c = cfrac_from_approx' (lb_pi prec) (ub_pi prec)
       in  map (\<lambda>n. (conv_num_fun ((!) c) n, conv_denom_fun ((!) c) n)) [0..<length c]"

approximate_cfrac prec: 200 "pi"
approximate_cfrac "ln 2"
approximate_cfrac "exp 1"
approximate_cfrac "sqrt 129"
approximate_cfrac "(sqrt 13 + 3) / 4"
approximate_cfrac "arctan 1"

(*
  Due to imprecision in the computation, approximate_cfrac is usually unable to determine
  the last digit in a finite continued fraction:
*)
approximate_cfrac "123 / 97"
value "cfrac_list_of_rat (123, 97)"

end