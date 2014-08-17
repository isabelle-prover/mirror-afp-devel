
(* Author: Florian Haftmann, TU Muenchen *)

header {* A barebone conversion for discrete summation *}

theory Summation_Conversion
imports Factorials Summation
begin

named_theorems summation "rules for solving summation problems"

declare
  \<Sigma>_const [summation] \<Sigma>_add [summation]
  \<Sigma>_factor [summation] monomial_ffact [summation]

lemma intervall_simps [summation]:
  "(\<Sum>k\<Colon>nat = 0..0. f k) = f 0"
  "(\<Sum>k\<Colon>nat = 0..Suc n. f k) = f (Suc n) + (\<Sum>k\<Colon>nat = 0..n. f k)"
  by (simp_all add: add.commute)

lemma \<Delta>_ffact:
  "\<Delta> (ffact (Suc n)) k = of_nat (Suc n) * ffact n (of_int k)"
proof (induct n)
  case 0 then show ?case by (simp add: \<Delta>_def)
next
  case (Suc n)
  obtain m where "m = Suc n" by blast
  have "\<Delta> (ffact (Suc m)) k =
    ffact (Suc m) (of_int (k + 1)) - ffact (Suc m) (of_int k)" 
    by (simp add: \<Delta>_def)
  also have "\<dots> = of_int (k + 1) * ffact m (of_int k)
    - (ffact m (of_int k) * (of_int k - of_nat m))"
    using ffact_Suc [of m "of_int k :: 'b"] by (simp add: mult.commute)
  also have "\<dots> = (of_int k + 1 - of_int k + of_nat m) * ffact m (of_int k)"
    by (simp add: algebra_simps)
  also have "\<dots> = of_nat (Suc m) * ffact m (of_int k)" by simp
  also have "\<dots> = of_nat (Suc m) * ffact (Suc m - 1) (of_int k)" by simp
  finally show ?case by (simp only: `m = Suc n` diff_Suc_1)
qed

lemma \<Sigma>_ffact_div [summation]:
  "\<Sigma> (ffact n) j l =
    (ffact (Suc n) (of_int l :: 'a :: {ring_div, semiring_char_0}) - ffact (Suc n) (of_int j)) div of_nat (Suc n)"
proof -
  have "ffact (Suc n) (of_int l :: 'a) - ffact (Suc n) (of_int j) =
    \<Sigma> (\<lambda>k. \<Delta> (ffact (Suc n)) k) j l"
    by (simp add: \<Sigma>_\<Delta>)
  also have "\<dots> = \<Sigma> (\<lambda>k. of_nat (Suc n) * ffact n (of_int k)) j l"
    by (simp add: \<Delta>_ffact)
  also have "\<dots> = of_nat (Suc n) * \<Sigma> (ffact n \<circ> of_int) j l"
    by (simp add: \<Sigma>_factor comp_def)
  finally show ?thesis by (simp only: \<Sigma>_comp_of_int div_mult_self1_is_id of_nat_eq_0_iff)
qed

lemma \<Sigma>_ffact_divide [summation]:
  "\<Sigma> (ffact n) j l =
    (ffact (Suc n) (of_int l :: 'a :: field_char_0) - ffact (Suc n) (of_int j)) / of_nat (Suc n)"
proof -
  have "ffact (Suc n) (of_int l :: 'a) - ffact (Suc n) (of_int j) =
    \<Sigma> (\<lambda>k. \<Delta> (ffact (Suc n)) k) j l"
    by (simp add: \<Sigma>_\<Delta>)
  also have "\<dots> = \<Sigma> (\<lambda>k. of_nat (Suc n) * ffact n (of_int k)) j l"
    by (simp add: \<Delta>_ffact)
  also have "\<dots> = of_nat (Suc n) * \<Sigma> (ffact n \<circ> of_int) j l"
    by (simp add: \<Sigma>_factor comp_def)
  finally show ?thesis by (simp only: \<Sigma>_comp_of_int nonzero_mult_divide_cancel_left of_nat_eq_0_iff)
qed

lemma of_int_coeff:
  "(of_int l :: 'a::comm_ring_1) * numeral k = of_int (l * numeral k)"
  by simp

lemmas nat_simps =
  add_0_left add_0_right add_Suc add_Suc_right
  mult_Suc mult_Suc_right mult_zero_left mult_zero_right
  One_nat_def of_nat_simps

lemmas of_int_pull_out =
   of_int_add [symmetric] of_int_diff [symmetric] of_int_mult [symmetric]
   of_int_coeff

lemmas of_int_pull_in =
  of_int_pull_out [symmetric] add_divide_distrib diff_divide_distrib of_int_power
  of_int_numeral of_int_neg_numeral times_divide_eq_left [symmetric]

ML {*
signature SUMMATION =
sig
  val conv: Proof.context -> conv
end

structure Summation : SUMMATION =
struct

val simps2 = @{thms Stirling.simps ffact.simps nat_simps};
val simpset3 =
  @{context}
  |> fold Simplifier.add_simp @{thms field_simps}
  |> Simplifier.simpset_of;
val simps4 = @{thms of_int_pull_out};
val simps6 = @{thms of_int_pull_in};

fun conv ctxt =
  let
    val ctxt1 =
      ctxt
      |> put_simpset HOL_basic_ss
      |> fold Simplifier.add_simp (Named_Theorems.get ctxt @{named_theorems summation})
    val ctxt2 =
      ctxt
      |> put_simpset HOL_basic_ss
      |> fold Simplifier.add_simp simps2
    val ctxt3 =
      ctxt
      |> put_simpset simpset3
    val ctxt4 =
      ctxt
      |> put_simpset HOL_basic_ss
      |> fold Simplifier.add_simp simps4
    val semiring_conv = Conv.arg1_conv (Conv.arg_conv
       (Semiring_Normalizer.semiring_normalize_conv ctxt))
       (* an approximation: we assume @{term "of_int _ / _"} here *)
    val ctxt6 =
      ctxt
      |> put_simpset HOL_basic_ss
      |> fold Simplifier.add_simp simps6
  in
     Simplifier.rewrite ctxt1
     then_conv Simplifier.rewrite ctxt2
     then_conv Simplifier.rewrite ctxt3
     then_conv Simplifier.rewrite ctxt4
     then_conv semiring_conv
     then_conv Simplifier.rewrite ctxt6
  end

end
*}

hide_fact (open) nat_simps of_int_pull_out of_int_pull_in

end

