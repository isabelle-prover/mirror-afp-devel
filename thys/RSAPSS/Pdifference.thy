(*  Title:      RSAPSS/Pdifference.thy

    Author:     Christina Lindenberg, Kai Wirt, Technische Universität Darmstadt
    Copyright:  2005 - Technische Universität Darmstadt 
*)
header "Positive differences"

theory Pdifference
imports "~~/src/HOL/Old_Number_Theory/Primes" Mod
begin

definition
  pdifference :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  [simp]: "pdifference a b = (if a < b then (b-a) else (a-b))"

lemma timesdistributesoverpdifference:
    "m*(pdifference a b) = pdifference (m*(a::nat)) (m* (b::nat))"
  by (auto simp add: nat_distrib)

lemma addconst: "a = (b::nat) \<Longrightarrow> c+a = c+b"
  by auto

lemma invers: "a \<le> x \<Longrightarrow> (x::nat) = x - a + a"
  by auto

lemma invers2: "\<lbrakk>a \<le> b; (b-a) = p*q\<rbrakk> \<Longrightarrow> (b::nat) = a+p*q"
  apply (subst addconst [symmetric])
  apply (assumption)
  apply (subst add_commute, rule invers, simp)
  done

lemma modadd: "\<lbrakk>b = a+p*q\<rbrakk> \<Longrightarrow> (a::nat) mod p = b mod p"
  by auto

lemma equalmodstrick1: "pdifference a b mod p = 0 \<Longrightarrow> a mod p = b mod p"
  apply (cases "a < b")
  apply auto
  apply (rule modadd, rule invers2, auto)
  apply (rule sym)
  apply (rule modadd, rule invers2, auto)
  done

lemma diff_add_assoc: "b \<le> c \<Longrightarrow> c - (c - b) = c - c + (b::nat)"
  by auto

lemma diff_add_assoc2: "a \<le> c \<Longrightarrow> c - (c - a + b) = (c - c + (a::nat) - b)"
  apply (subst diff_diff_left [symmetric])
  apply (subst diff_add_assoc)
  apply auto
  done

lemma diff_add_diff: "x \<le> b \<Longrightarrow> (b::nat) - x + y - b = y - x"
  by (induct b) auto

lemma equalmodstrick2: "a mod p = b mod p \<Longrightarrow> pdifference a b mod p = 0"
  apply auto
   apply (drule mod_eqD [simplified], auto)
   apply (subst mod_div_equality' [of b])
   apply (subst diff_add_assoc2)
    apply (subst mult_commute, subst mult_div_cancel)
    apply simp+
   apply (subst diff_mult_distrib [symmetric])
   apply simp
  apply (drule mod_eqD [simplified], auto)
  apply (subst mod_div_equality' [of b])
  apply (subst diff_add_diff)
   apply (subst mult_commute, subst mult_div_cancel, auto)
  apply (subst diff_mult_distrib [symmetric])
  apply simp
  done

lemma primekeyrewrite: "\<lbrakk>prime p; p dvd (a*b);~(p dvd a)\<rbrakk> \<Longrightarrow> p dvd b"
  apply (drule prime_dvd_mult)
  apply auto
  done

lemma multzero: "\<lbrakk>0 < m mod p; m*a = 0\<rbrakk> \<Longrightarrow> (a::nat) = 0"
  by auto

lemma primekeytrick: "\<lbrakk>(M*A) mod P = (M*B) mod P;M mod P \<noteq> 0; prime P\<rbrakk>
    \<Longrightarrow> A mod P = (B::nat) mod P"
  apply (drule equalmodstrick2)
  apply (rule equalmodstrick1)
  apply (rule multzero, simp)
  apply (subst mod_mult_distrib2)
  apply (subst timesdistributesoverpdifference)
  apply simp
  apply (rule conjI, rule impI, simp)
   apply (subst diff_mult_distrib2 [symmetric])
   apply (simp add: dvd_eq_mod_eq_0 [symmetric])
   apply (rule primekeyrewrite, simp)
    apply (subst diff_mult_distrib2)
    apply (simp add: dvd_eq_mod_eq_0)+
  apply (rule impI, simp)
  apply (subst diff_mult_distrib2 [symmetric])
  apply (simp add: dvd_eq_mod_eq_0 [symmetric])
  apply (rule disjI2)
  apply (rule primekeyrewrite)
    apply (simp add: dvd_eq_mod_eq_0 diff_mult_distrib2)+
  done

end
