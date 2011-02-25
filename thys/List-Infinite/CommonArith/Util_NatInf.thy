(*  Title:      Util_NatInf.thy
    Date:       Oct 2006
    Author:     David Trachtenherz
*)

header {* Results for natural arithmetics with infinity *}

theory Util_NatInf
imports "$ISABELLE_HOME/src/HOL/Library/Nat_Infinity"
begin



subsection {* Arithmetic operations with @{typ inat} *} 

subsubsection {* Additional definitions *}


thm one_inat_def
thm plus_inat_def
thm times_inat_def

instantiation inat :: "{minus, Divides.div}"
begin

definition
  diff_inat_def [code del]: "
  a - b \<equiv> (case a of 
    (Fin x) \<Rightarrow> (case b of (Fin y) \<Rightarrow> Fin (x - y) | \<infinity> \<Rightarrow> 0) | 
    \<infinity> \<Rightarrow> \<infinity>)"

definition
  div_inat_def [code del]: "
  a div b \<equiv> (case a of 
    (Fin x) \<Rightarrow> (case b of (Fin y) \<Rightarrow> Fin (x div y) | \<infinity> \<Rightarrow> 0) | 
    \<infinity> \<Rightarrow> (case b of (Fin y) \<Rightarrow> ((case y of 0 \<Rightarrow> 0 | Suc n \<Rightarrow> \<infinity>)) | \<infinity> \<Rightarrow> \<infinity> ))"
definition
  mod_inat_def [code del]: "
  a mod b \<equiv> (case a of 
    (Fin x) \<Rightarrow> (case b of (Fin y) \<Rightarrow> Fin (x mod y) | \<infinity> \<Rightarrow> a) | 
    \<infinity> \<Rightarrow> \<infinity>)"

instance ..

end

(*instance inat :: "{ord, zero, one, plus, minus, times, Divides.div}" ..*)





lemmas inat_arith_defs = 
  zero_inat_def one_inat_def
  plus_inat_def diff_inat_def times_inat_def div_inat_def mod_inat_def
declare zero_inat_def[simp]

primrec the_Fin :: "inat \<Rightarrow> nat" where
  "the_Fin (Fin n) = n"

lemma Fin_the_Fin: "n \<noteq> \<infinity> \<Longrightarrow> Fin (the_Fin n) = n" by fastsimp

subsubsection {* Results for comparison operators *}

lemma Fin_ile_mono: "(Fin m \<le> Fin n) = (m \<le> n)" by simp
lemma Fin_iless_mono: "(Fin m < Fin n) = (m < n)" by simp
lemma Infty_ub: "n \<le> \<infinity>" by simp

thm less_not_sym
lemma iless_not_sym: "(x::inat) < y \<Longrightarrow> \<not> y < x" by simp
thm less_not_refl
lemma iless_not_refl: "\<not> (n::inat) < n" by simp
thm le_refl
lemma ile_refl: "(n::inat) \<le> n" by simp
lemma eq_imp_ile: "(m::inat) = n \<Longrightarrow> m \<le> n" by simp

lemma not_Infty_iless: "\<not> \<infinity> < n" by simp
lemma Fin_iless_Infty: "Fin n < \<infinity>" by simp
lemma not_Infty_ile_Fin: "\<not> \<infinity> \<le> Fin n" by simp
(*lemma Fin_ile_Infty: "Fin n \<le> \<infinity>"*)
lemmas Fin_ile_Infty = Infty_ub


(*lemma neq_Infty_Fin_conv: "(n \<noteq> \<infinity>) = (\<exists>k. n = Fin k)" *)
lemmas neq_Infty_Fin_conv = not_Infty_eq

lemma Infty_le_eq: "(\<infinity> \<le> n) = (n = \<infinity>)" by simp

lemma ile_trans: "\<lbrakk> (i::inat) \<le> j; j \<le> k \<rbrakk> \<Longrightarrow> i \<le> k" by simp
lemma ile_anti_sym: "\<lbrakk> (m::inat) \<le> n; n \<le> m \<rbrakk> \<Longrightarrow> m = n" by simp
lemma iless_ile: "((m::inat) < n) = (m \<le> n \<and> m \<noteq> n)" by (safe, simp_all)
lemma ile_linear: "(m::inat) \<le> n \<or> n \<le> m" by (safe, simp_all)

(*
instance inat :: order ..
instance inat :: linorder ..
instance inat :: wellorder ..
*)




thm neq0_conv
lemma ineq0_conv: "(n \<noteq> (0::inat)) = (0 < n)"
by (case_tac n, simp_all)
lemmas ineq0_conv_Fin[simp] = ineq0_conv[unfolded zero_inat_def]

(*lemma not_iless0: "\<not> n < (0::inat)"*)
lemmas not_iless0 = not_ilessi0
lemma iless_iSuc0: "(n < iSuc 0) = (n = 0)"
by (case_tac n, simp_all)
lemmas iless_iSuc0_Fin[simp] = iless_iSuc0[unfolded zero_inat_def]

(*lemma ile_0_eq: "(n \<le> (0::inat)) = (n = 0)"*)
lemmas ile_0_eq = i0_neq

lemma neq_Infty_imp_ex_Fin: "n \<noteq> \<infinity> \<Longrightarrow> \<exists>nat. n = Fin nat"
by (case_tac n, simp_all)
corollary less_Infty_imp_ex_Fin: "n < \<infinity> \<Longrightarrow> \<exists>nat. n = Fin nat"
thm neq_Infty_imp_ex_Fin[OF less_imp_neq]
by (rule neq_Infty_imp_ex_Fin[OF less_imp_neq])





subsubsection {* Addition and difference *}


lemma iadd_Fin_Fin: "Fin a + Fin b = Fin (a + b)" by simp
lemma iadd_Infty: "\<infinity> + n = \<infinity>" by simp
lemma iadd_Infty_right: "n + \<infinity> = \<infinity>" by simp

lemma idiff_Fin_Fin[simp,code]: "Fin a - Fin b = Fin (a - b)"
unfolding diff_inat_def by simp
lemma idiff_Infty[simp,code]: "\<infinity> - n = \<infinity>"
unfolding diff_inat_def by simp
lemma idiff_Infty_right[simp,code]: "Fin a - \<infinity> = 0"
unfolding diff_inat_def by simp

lemma idiff_0: "(n::inat) - 0 = n"
by (case_tac n, simp_all)
lemmas idiff_0_Fin[simp,code] = idiff_0[unfolded zero_inat_def]
lemma idiff_0_eq_0: "(0::inat) - n = 0"
by (case_tac n, simp_all)
lemmas idiff_0_eq_0_Fin[simp,code] = idiff_0_eq_0[unfolded zero_inat_def]

lemma diff_eq_conv_nat: "(x - y = (z::nat)) = (if y < x then x = y + z else z = 0)"
by auto
lemma idiff_eq_conv: "
  (x - y = (z::inat)) = 
  (if y < x then x = y + z else if x \<noteq> \<infinity> then z = 0 else z = \<infinity>)"
by (case_tac x, case_tac y, case_tac z, auto, case_tac z, auto)
lemmas idiff_eq_conv_Fin = idiff_eq_conv[unfolded zero_inat_def]

lemma idiff_self_eq_0: "n \<noteq> \<infinity> \<Longrightarrow> (n::inat) - n = 0" 
by fastsimp
lemmas idiff_self_eq_0_Fin = idiff_self_eq_0[unfolded zero_inat_def]

lemma less_eq_idiff_eq_sum: "y \<le> (x::inat) \<Longrightarrow> (z \<le> x - y) = (z + y \<le> x)"
by (case_tac x, case_tac y, case_tac z, fastsimp+)


lemma iSuc_pred: "0 < n \<Longrightarrow> iSuc (n - iSuc 0) = n"
apply (case_tac n)
apply (simp add: iSuc_Fin)+
done
lemmas iSuc_pred_Fin = iSuc_pred[unfolded zero_inat_def]
lemma iadd_0: "(0::inat) + n = n" 
by (rule monoid_add_class.add_0_left)
lemmas iadd_0_Fin[simp, code] = iadd_0[unfolded zero_inat_def]
lemma iadd_0_right: "n + (0::inat) = n" 
by (rule monoid_add_class.add_0_right)
lemmas iadd_0_right_Fin[simp, code] = iadd_0_right[unfolded zero_inat_def]

lemma iadd_commute: "(a::inat) + b = b + a" 
by (rule ab_semigroup_add_class.add_commute)
thm add_assoc
lemma iadd_assoc: "(a::inat) + b + c = a + (b + c)"
by (rule semigroup_add_class.add.assoc)


thm add_Suc
lemma iadd_Suc: "iSuc m + n = iSuc (m + n)"
apply (case_tac m, case_tac n)
apply (simp add: iSuc_Fin)+
done

thm add_Suc_right
lemma iadd_Suc_right: "m + iSuc n = iSuc (m + n)"
by (simp only: iadd_commute[of m] iadd_Suc)

lemma mono_iSuc: "mono iSuc"
unfolding mono_def by simp

thm add_is_0[no_vars]
lemma iadd_is_0: "(m + n = (0::inat)) = (m = 0 \<and> n = 0)"
by (case_tac m, case_tac n, simp_all)
lemmas iadd_is_0_Fin = iadd_is_0[unfolded zero_inat_def]

lemma ile_add1: "(n::inat) \<le> n + m"
by (case_tac m, case_tac n, simp_all)
lemma ile_add2: "(n::inat) \<le> m + n"
by (simp only: iadd_commute[of m] ile_add1)

lemma iadd_ile_mono: "\<lbrakk> (i::inat) \<le> j; k \<le> l \<rbrakk> \<Longrightarrow> i + k \<le> j + l"
by (rule add_mono)
lemma iadd_ile_mono1: "(i::inat) \<le> j \<Longrightarrow> i + k \<le> j + k"
by (rule add_right_mono)
lemma iadd_ile_mono2: "(i::inat) \<le> j \<Longrightarrow> k + i \<le> k + j"
by (rule add_left_mono)

lemma iadd_iless_mono: "\<lbrakk> (i::inat) < j; k < l \<rbrakk> \<Longrightarrow> i + k < j + l"
by (case_tac i, case_tac k, case_tac j, case_tac l, simp_all)

lemma trans_ile_iadd1: "i \<le> (j::inat) \<Longrightarrow> i \<le> j + m" 
by (rule order_trans[OF _ ile_add1])
lemma trans_ile_iadd2: "i \<le> (j::inat) \<Longrightarrow> i \<le> m + j"
by (rule order_trans[OF _ ile_add2])

lemma trans_iless_iadd1: "i < (j::inat) \<Longrightarrow> i < j + m"
by (rule order_less_le_trans[OF _ ile_add1])
lemma trans_iless_iadd2: "i < (j::inat) \<Longrightarrow> i < m + j"
by (rule order_less_le_trans[OF _ ile_add2])

thm add_leD1[no_vars]
lemma iadd_ileD1: "m + k \<le> (n::inat) \<Longrightarrow> m \<le> n"
by (case_tac m, case_tac n, case_tac k, simp_all)
lemma iadd_ileD2: "m + k \<le> (n::inat) \<Longrightarrow> k \<le> n"
by (rule iadd_ileD1, simp only: iadd_commute[of m])



thm diff_le_mono
lemma idiff_ile_mono: "m \<le> (n::inat) \<Longrightarrow> m - l \<le> n - l"
by (case_tac m, case_tac n, case_tac l, simp_all)
thm diff_le_mono2
lemma idiff_ile_mono2: "m \<le> (n::inat) \<Longrightarrow> l - n \<le> l - m"
by (case_tac m, case_tac n, case_tac l, simp_all, case_tac l, simp_all)

thm diff_less_mono
lemma idiff_iless_mono: "\<lbrakk> m < (n::inat); l \<le> m \<rbrakk> \<Longrightarrow> m - l < n - l"
by (case_tac m, case_tac n, case_tac l, simp_all, case_tac l, simp_all)
thm diff_less_mono2
lemma idiff_iless_mono2: "\<lbrakk> m < (n::inat); m < l \<rbrakk> \<Longrightarrow> l - n \<le> l - m"
by (case_tac m, case_tac n, case_tac l, simp_all, case_tac l, simp_all)



subsubsection {* Multiplication and division *}

lemma imult_Fin_Fin: "Fin a * Fin b = Fin (a * b)" by simp
lemma imult_Infty: "(0::inat) < n \<Longrightarrow> \<infinity> * n = \<infinity>" 
by (case_tac n, simp_all)
lemmas imult_Infty_Fin[simp] = imult_Infty[unfolded zero_inat_def]
lemma imult_Infty_right: "(0::inat) < n \<Longrightarrow> n * \<infinity> = \<infinity>"
by (case_tac n, simp_all)
lemmas imult_Infty_right_Fin[simp] = imult_Infty_right[unfolded zero_inat_def]

lemma idiv_Fin_Fin[simp, code]: "Fin a div Fin b = Fin (a div b)"
unfolding div_inat_def by simp
lemma idiv_Infty: "0 < n \<Longrightarrow> \<infinity> div n = \<infinity>"
unfolding div_inat_def
apply (case_tac n, simp_all)
apply (rename_tac n1, case_tac n1, simp_all)
done
lemmas idiv_Infty_Fin[simp] = idiv_Infty[unfolded zero_inat_def]

lemma idiv_Infty_right[simp]: "n \<noteq> \<infinity> \<Longrightarrow> n div \<infinity> = 0"
unfolding div_inat_def by (case_tac n, simp_all)

lemma idiv_Infty_if: "n div \<infinity> = (if n = \<infinity> then \<infinity> else 0)"
unfolding div_inat_def
by (case_tac n, simp_all)

lemmas idiv_Infty_if_Fin = idiv_Infty_if[unfolded zero_inat_def]

lemma imult_0: "0 * (m::inat) = 0" 
by (case_tac m, simp_all)
lemmas imult_0_Fin[simp, code] = imult_0[unfolded zero_inat_def]
lemma imult_0_right: "(m::inat) * 0 = 0"
by (case_tac m, simp_all)
lemmas imult_0_right_Fin[simp, code] = imult_0_right[unfolded zero_inat_def]

lemma imult_is_0: "((m::inat) * n = 0) = (m = 0 \<or> n = 0)"
apply (case_tac m, case_tac n, simp_all)
apply (case_tac n, simp_all)
done
lemma inat_0_less_mult_iff: "(0 < (m::inat) * n) = (0 < m \<and> 0 < n)"
by (simp only: ineq0_conv[symmetric] imult_is_0, simp)
lemmas imult_is_0_Fin = imult_is_0[unfolded zero_inat_def]
lemmas inat_0_less_mult_iff_Fin = inat_0_less_mult_iff[unfolded zero_inat_def]

lemma imult_commute: "(a::inat) * b = b * a"
by (rule ab_semigroup_mult_class.mult_commute)


lemma imult_Infty_if: "\<infinity> * n = (if n = 0 then 0 else \<infinity>)"
by (case_tac n, simp_all)
lemma imult_Infty_right_if: "n * \<infinity> = (if n = 0 then 0 else \<infinity>)"
by (case_tac n, simp_all)
lemmas imult_Infty_if_Fin = imult_Infty_if[unfolded zero_inat_def]
lemmas imult_Infty_right_if_Fin = imult_Infty_right_if[unfolded zero_inat_def]

lemma imult_is_Infty: "((a::inat) * b = \<infinity>) = (a = \<infinity> \<and> b \<noteq> 0 \<or> b = \<infinity> \<and> a \<noteq> 0)"
apply (case_tac a, case_tac b, simp_all)
apply (case_tac b, simp_all)
done
lemmas imult_is_Infty_Fin = imult_is_Infty[unfolded zero_inat_def]

lemma imult_assoc: "(a::inat) * b * c = a * (b * c)"
by (rule semigroup_mult_class.mult.assoc)

lemma idiv_by_0: "(a::inat) div 0 = 0"
unfolding div_inat_def by (case_tac a, simp_all)
lemmas idiv_by_0_Fin[simp, code] = idiv_by_0[unfolded zero_inat_def]

lemma idiv_0: "0 div (a::inat) = 0"
unfolding div_inat_def by (case_tac a, simp_all)
lemmas idiv_0_Fin[simp, code] = idiv_0[unfolded zero_inat_def]

thm mod_by_0
lemma imod_by_0: "(a::inat) mod 0 = a"
unfolding mod_inat_def by (case_tac a, simp_all)
lemmas imod_by_0_Fin[simp, code] = imod_by_0[unfolded zero_inat_def]

lemma imod_0: "0 mod (a::inat) = 0"
unfolding mod_inat_def by (case_tac a, simp_all)
lemmas imod_0_Fin[simp, code] = imod_0[unfolded zero_inat_def]

lemma imod_Fin_Fin[simp, code]: "Fin a mod Fin b = Fin (a mod b)"
unfolding mod_inat_def by simp
lemma imod_Infty[simp, code]: "\<infinity> mod n = \<infinity>"
unfolding mod_inat_def by simp
lemma imod_Infty_right[simp, code]: "n mod \<infinity> = n"
unfolding mod_inat_def by (case_tac n) simp_all

(*<*)
thm mult_Suc
(*lemma imult_Suc: "iSuc m * n = n + m * n"*)
(*lemmas imult_Suc = mult_iSuc*)

thm mult_Suc_right
(*lemma imult_Suc_right: "m * iSuc n = m + m * n"*)
(*lemmas imult_Suc_right mult_iSuc_right*)
(*>*)

lemma idiv_self: "\<lbrakk> 0 < (n::inat); n \<noteq> \<infinity> \<rbrakk> \<Longrightarrow> n div n = 1"
by (case_tac n, simp_all add: one_inat_def)
lemma imod_self: "n \<noteq> \<infinity> \<Longrightarrow> (n::inat) mod n = 0"
by (case_tac n, simp_all)

lemma idiv_iless: "m < (n::inat) \<Longrightarrow> m div n = 0"
by (case_tac m, simp_all) (case_tac n, simp_all)
lemma imod_iless: "m < (n::inat) \<Longrightarrow> m mod n = m"
by (case_tac m, simp_all) (case_tac n, simp_all)

lemma imod_iless_divisor: "\<lbrakk> 0 < (n::inat); m \<noteq> \<infinity> \<rbrakk>  \<Longrightarrow> m mod n < n"
by (case_tac m, simp_all) (case_tac n, simp_all)
lemma imod_ile_dividend: "(m::inat) mod n \<le> m"
by (case_tac m, simp_all) (case_tac n, simp_all)
lemma idiv_ile_dividend: "(m::inat) div n \<le> m"
by (case_tac m, simp_all) (case_tac n, simp_all)

thm div_mult2_eq
lemma idiv_imult2_eq: "(a::inat) div (b * c) = a div b div c"
apply (case_tac a, case_tac b, case_tac c, simp add: div_mult2_eq)
apply (simp add: imult_Infty_right_if idiv_Infty_right)
apply (simp add: imult_Infty_if idiv_Infty_right idiv_0[unfolded zero_inat_def])
apply (case_tac "b = 0", simp)
apply (case_tac "c = 0", simp)
thm idiv_Infty
thm idiv_Infty[OF inat_0_less_mult_iff[THEN iffD2]]
apply (simp add: idiv_Infty[OF inat_0_less_mult_iff[THEN iffD2]])
done


thm add_mult_distrib
lemma iadd_imult_distrib: "((m::inat) + n) * k = m * k + n * k"
by (rule left_distrib)

thm add_mult_distrib2
lemma iadd_imult_distrib2: "k * ((m::inat) + n) = k * m + k * n"
by (simp only: imult_commute[of k] iadd_imult_distrib)



thm mult_le_mono
lemma imult_ile_mono: "\<lbrakk> (i::inat) \<le> j; k \<le> l \<rbrakk> \<Longrightarrow> i * k \<le> j * l"
apply (case_tac i, case_tac j, case_tac k, case_tac l, simp_all add: mult_le_mono)
apply (case_tac k, case_tac l, simp_all)
apply (case_tac k, case_tac l, simp_all)
done

lemma imult_ile_mono1: "(i::inat) \<le> j \<Longrightarrow> i * k \<le> j * k"
by (rule imult_ile_mono[OF _ ile_refl])
thm mult_le_mono2
lemma imult_ile_mono2: "(i::inat) \<le> j \<Longrightarrow> k * i \<le> k * j"
by (rule imult_ile_mono[OF ile_refl])

lemma imult_iless_mono1: "\<lbrakk> (i::inat) < j; 0 < k; k \<noteq> \<infinity> \<rbrakk> \<Longrightarrow> i * k \<le> j * k"
by (case_tac i, case_tac j, case_tac k, simp_all)
lemma imult_iless_mono2: "\<lbrakk> (i::inat) < j; 0 < k; k \<noteq> \<infinity> \<rbrakk> \<Longrightarrow> k * i \<le> k * j"
by (simp only: imult_commute[of k], rule imult_iless_mono1)

lemma imod_1: "(Fin m) mod iSuc 0 = 0"
by (simp add: iSuc_Fin)
lemmas imod_1_Fin[simp, code] = imod_1[unfolded zero_inat_def]

lemma imod_iadd_self2: "(m + Fin n) mod (Fin n) = m mod (Fin n)"
by (case_tac m, simp_all)

lemma imod_iadd_self1: "(Fin n + m) mod (Fin n) = m mod (Fin n)"
by (simp only: iadd_commute[of _ m] imod_iadd_self2)

lemma idiv_imod_equality: "(m::inat) div n * n + m mod n + k = m + k"
by (case_tac m, simp_all) (case_tac n, simp_all)
lemma imod_idiv_equality: "(m::inat) div n * n + m mod n = m"
by (insert idiv_imod_equality[of m n 0], simp)

lemma idiv_ile_mono: "m \<le> (n::inat) \<Longrightarrow> m div k \<le> n div k"
apply (case_tac "k = 0", simp)
apply (case_tac m, case_tac k, simp_all)
apply (case_tac n)
 apply (simp add: div_le_mono)
apply (simp add: idiv_Infty)
apply (simp add: i0_lb[unfolded zero_inat_def])
done
lemma idiv_ile_mono2: "\<lbrakk> 0 < m; m \<le> (n::inat) \<rbrakk> \<Longrightarrow> k div n \<le> k div m"
apply (case_tac "n = 0", simp)
apply (case_tac m, case_tac k, simp_all)
apply (case_tac n)
 apply (simp add: div_le_mono2)
apply simp
done



end