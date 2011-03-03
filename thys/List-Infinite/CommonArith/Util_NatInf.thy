(*  Title:      Util_NatInf.thy
    Date:       Oct 2006
    Author:     David Trachtenherz
*)

header {* Results for natural arithmetics with infinity *}

theory Util_NatInf
imports "~~/src/HOL/Library/Nat_Infinity"
begin



subsection {* Arithmetic operations with @{typ inat} *} 

subsubsection {* Additional definitions *}

instantiation inat :: "{Divides.div}"
begin

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


lemmas inat_arith_defs = 
  zero_inat_def one_inat_def
  plus_inat_def diff_inat_def times_inat_def div_inat_def mod_inat_def
declare zero_inat_def[simp]


lemmas ineq0_conv_Fin[simp] = i0_less[symmetric, unfolded zero_inat_def]

lemmas iless_iSuc0_Fin[simp] = iless_iSuc0[unfolded zero_inat_def]


subsubsection {* Addition, difference, order *}

lemma diff_eq_conv_nat: "(x - y = (z::nat)) = (if y < x then x = y + z else z = 0)"
by auto
lemma idiff_eq_conv: "
  (x - y = (z::inat)) = 
  (if y < x then x = y + z else if x \<noteq> \<infinity> then z = 0 else z = \<infinity>)"
by (case_tac x, case_tac y, case_tac z, auto, case_tac z, auto)
lemmas idiff_eq_conv_Fin = idiff_eq_conv[unfolded zero_inat_def]

lemma less_eq_idiff_eq_sum: "y \<le> (x::inat) \<Longrightarrow> (z \<le> x - y) = (z + y \<le> x)"
by (case_tac x, case_tac y, case_tac z, fastsimp+)


lemma iSuc_pred: "0 < n \<Longrightarrow> iSuc (n - iSuc 0) = n"
apply (case_tac n)
apply (simp add: iSuc_Fin)+
done
lemmas iSuc_pred_Fin = iSuc_pred[unfolded zero_inat_def]
lemmas iadd_0_Fin[simp] = add_0_left[where 'a = inat, unfolded zero_inat_def]
lemmas iadd_0_right_Fin[simp] = add_0_right[where 'a=inat, unfolded zero_inat_def]

lemma ile_add1: "(n::inat) \<le> n + m"
by (case_tac m, case_tac n, simp_all)
lemma ile_add2: "(n::inat) \<le> m + n"
by (simp only: add_commute[of m] ile_add1)

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
by (rule iadd_ileD1, simp only: add_commute[of m])


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

lemmas imult_Infty_Fin[simp] = imult_Infty[unfolded zero_inat_def]
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

lemmas imult_0_Fin[simp] = mult_zero_left[where 'a=inat,unfolded zero_inat_def]
lemmas imult_0_right_Fin[simp] = mult_zero_right[where 'a=inat,unfolded zero_inat_def]

lemmas imult_is_0_Fin = imult_is_0[unfolded zero_inat_def]
lemmas inat_0_less_mult_iff_Fin = inat_0_less_mult_iff[unfolded zero_inat_def]

lemma imult_Infty_if: "\<infinity> * n = (if n = 0 then 0 else \<infinity>)"
by (case_tac n, simp_all)
lemma imult_Infty_right_if: "n * \<infinity> = (if n = 0 then 0 else \<infinity>)"
by (case_tac n, simp_all)
lemmas imult_Infty_if_Fin = imult_Infty_if[unfolded zero_inat_def]
lemmas imult_Infty_right_if_Fin = imult_Infty_right_if[unfolded zero_inat_def]

lemmas imult_is_Infty_Fin = imult_is_Infty[unfolded zero_inat_def]

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


thm mult_le_mono
lemma imult_ile_mono: "\<lbrakk> (i::inat) \<le> j; k \<le> l \<rbrakk> \<Longrightarrow> i * k \<le> j * l"
apply (case_tac i, case_tac j, case_tac k, case_tac l, simp_all add: mult_le_mono)
apply (case_tac k, case_tac l, simp_all)
apply (case_tac k, case_tac l, simp_all)
done

lemma imult_ile_mono1: "(i::inat) \<le> j \<Longrightarrow> i * k \<le> j * k"
by (rule imult_ile_mono[OF _ order_refl])
thm mult_le_mono2
lemma imult_ile_mono2: "(i::inat) \<le> j \<Longrightarrow> k * i \<le> k * j"
by (rule imult_ile_mono[OF order_refl])

lemma imult_iless_mono1: "\<lbrakk> (i::inat) < j; 0 < k; k \<noteq> \<infinity> \<rbrakk> \<Longrightarrow> i * k \<le> j * k"
by (case_tac i, case_tac j, case_tac k, simp_all)
lemma imult_iless_mono2: "\<lbrakk> (i::inat) < j; 0 < k; k \<noteq> \<infinity> \<rbrakk> \<Longrightarrow> k * i \<le> k * j"
by (simp only: mult_commute[of k], rule imult_iless_mono1)

lemma imod_1: "(Fin m) mod iSuc 0 = 0"
by (simp add: iSuc_Fin)
lemmas imod_1_Fin[simp, code] = imod_1[unfolded zero_inat_def]

lemma imod_iadd_self2: "(m + Fin n) mod (Fin n) = m mod (Fin n)"
by (case_tac m, simp_all)

lemma imod_iadd_self1: "(Fin n + m) mod (Fin n) = m mod (Fin n)"
by (simp only: add_commute[of _ m] imod_iadd_self2)

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