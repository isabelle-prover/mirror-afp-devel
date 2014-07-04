(* Title:      Regular Algebras
   Author:     Simon Foster, Georg Struth
   Maintainer: Simon Foster <s.foster at york.ac.uk>
               Georg Struth <g.struth at sheffield.ac.uk>               
*)

header {* Dioids, Powers and Finite Sums *}

theory Dioid_Power_Sum
  imports "../Kleene_Algebra/Dioid" "../Kleene_Algebra/Finite_Suprema"
begin

text {* We add a few facts about powers and finite
 sums---in fact, finite suprema---to an existing theory field for dioids. *}

context dioid_one_zero
begin

lemma add_iso_r:
  "y \<le> z \<Longrightarrow> x + y \<le> x + z"
   by (metis add_iso_var le_less)

notation power ("_\<^bsup>_\<^esup>" [101,50] 100) 

lemma power_subdist: "x\<^bsup>n\<^esup> \<le> (x + y)\<^bsup>n\<^esup>"
  by (induct n, metis eq_refl power.simps(1), metis add_ub1 mult_isol_var power.simps(2))
  
lemma power_inductl_var: "x \<cdot> y \<le> y \<Longrightarrow> x\<^bsup>n\<^esup> \<cdot> y \<le> y"
  by (induct n, metis eq_refl mult_onel power.simps(1), metis mult.assoc mult_isol mult_isol_equiv_subdistl order_trans power.simps(2))

lemma power_inductr_var: "y \<cdot> x \<le> y \<Longrightarrow> y \<cdot> x\<^bsup>n\<^esup> \<le> y"
  by (induct n, metis eq_refl mult_oner power.simps(1), metis mult.assoc mult_isor order_refl order_trans power.simps(2) power_commutes)

definition powsum :: "'a \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a"  ("_\<^bsub>_\<^esub>\<^bsup>_\<^esup>" [101,50,50] 100) where
  "powsum x m n = setsum (op ^ x) {m..n + m}"

lemmas powsum_simps = powsum_def atLeastAtMostSuc_conv numerals

lemma powsum1: "x\<^bsub>n\<^esub>\<^bsup>0\<^esup> = x\<^bsup>n\<^esup>"
  by (simp add:powsum_simps)
  
lemma powsum2: "x\<^bsub>n\<^esub>\<^bsup>Suc m\<^esup> = x\<^bsub>n\<^esub>\<^bsup>m \<^esup>+ x\<^bsup>n+Suc m\<^esup>"
  by (simp add:powsum_simps ab_semigroup_add_class.add.commute)

lemma powsum_00: "x\<^bsub>0\<^esub>\<^bsup>0 \<^esup>= 1"
  by (simp add:powsum_def)

lemma powsum_01: "x\<^bsub>0\<^esub>\<^bsup>1\<^esup> = 1 + x" 
  by (simp add:powsum_simps) 

lemma powsum_10: "x\<^bsub>1\<^esub>\<^bsup>0\<^esup> = x"  
  by (simp add: powsum_simps) 

lemma powsum_split: "x\<^bsub>m\<^esub>\<^bsup>i+Suc n\<^esup> = x\<^bsub>m\<^esub>\<^bsup>i\<^esup> + x\<^bsub>m+Suc i\<^esub>\<^bsup>n\<^esup>"
  by (induct n, simp_all add:powsum_simps ac_simps)

lemma powsum_split_var1: "x\<^bsub>0\<^esub>\<^bsup>n+1\<^esup> = 1 + x\<^bsub>1\<^esub>\<^bsup>n\<^esup>" 
proof -
  have "x\<^bsub>0\<^esub>\<^bsup>n + 1\<^esup> = x\<^bsub>0\<^esub>\<^bsup>0 + Suc n\<^esup>"
    by simp
  also have "... = x\<^bsub>0\<^esub>\<^bsup>0\<^esup> + x\<^bsub>0 + Suc 0\<^esub>\<^bsup>n\<^esup>"
    by (subst powsum_split, rule refl)
  also have "... = 1 + x\<^bsub>0 + Suc 0\<^esub>\<^bsup>n\<^esup>"
    by (metis powsum_00)
  finally show ?thesis 
    by simp
qed

lemma powsum_split_var2: "x\<^bsup>m\<^esup> + x\<^bsub>0\<^esub>\<^bsup>m\<^esup> = x\<^bsub>0\<^esub>\<^bsup>m\<^esup>"
proof (induct m)
  case 0 show ?case 
    by (metis add_idem' power_0 powsum_00)
  case (Suc n) show ?case
    by (auto simp add: powsum2, metis add_assoc' add_idem')
qed

lemma powsum_split_var3: "x\<^bsub>0\<^esub>\<^bsup>m+Suc n\<^esup> = x\<^bsub>0\<^esub>\<^bsup>m \<^esup>+ x\<^bsub>0+Suc m\<^esub>\<^bsup>n\<^esup>" 
  by (subst powsum_split, simp)

lemma powsum_split_var4: "x\<^bsub>0\<^esub>\<^bsup>m+n\<^esup> + x\<^bsub>m\<^esub>\<^bsup>n\<^esup> = x\<^bsub>0\<^esub>\<^bsup>m+n\<^esup>"
proof (induct n)
  case 0 show ?case
    by (metis add_0_iff add_comm powsum1 powsum_split_var2)
next
  case (Suc n) note hyp = this
  show ?case
  proof -
    have  "x\<^bsub>0\<^esub>\<^bsup>m + Suc n\<^esup> + x\<^bsub>m\<^esub>\<^bsup>Suc n\<^esup> = x\<^bsub>0\<^esub>\<^bsup>m + n\<^esup> + x\<^bsup>Suc (m + n)\<^esup> + (x\<^bsub>m\<^esub>\<^bsup>n\<^esup> + x\<^bsup>m + Suc n\<^esup>)"
      by (auto simp add: powsum2)  
    also have "... = (x\<^bsub>0\<^esub>\<^bsup>m + n \<^esup>+ x\<^bsub>m\<^esub>\<^bsup>n\<^esup>) + x\<^bsup>Suc (m + n)\<^esup> + x\<^bsup>m + Suc n\<^esup>"
      by (metis add.assoc add.left_commute)
    also have "... =  x\<^bsup>Suc (m+n)\<^esup> + x\<^bsub>0\<^esub>\<^bsup>m+n\<^esup>"
      by (metis add_Suc_right add.assoc add.commute add_idem' hyp)
    also have "... = x\<^bsub>0\<^esub>\<^bsup>m + Suc n\<^esup>"
      by (auto simp add: powsum2)
    finally show ?thesis .
  qed
qed

lemma powsum_split_var6: "x\<^bsub>0\<^esub>\<^bsup>(Suc k)+Suc n\<^esup> = x\<^bsub>0\<^esub>\<^bsup>Suc k \<^esup>+ x\<^bsub>0+Suc (Suc k)\<^esub>\<^bsup>n\<^esup>"     
  by (metis powsum_split_var3) 

lemma powsum_ext: "x \<le> x\<^bsub>0\<^esub>\<^bsup>Suc n\<^esup>" 
proof (induct n)
  case 0 show ?case
    by (metis (full_types) One_nat_def add_lub order_refl powsum_01)
next
  case (Suc n) thus ?case
    by (auto simp add:less_eq_def powsum_simps, metis (lifting, no_types) add.left_commute)
qed

lemma powsum_one: "1 \<le> x\<^bsub>0\<^esub>\<^bsup>Suc n\<^esup>"  
  by (induct n, metis One_nat_def add_ub1 powsum_01, metis (full_types) Suc_eq_plus1 add_ub1 powsum_split_var1)

lemma powsum_shift1: "x \<cdot> x\<^bsub>m\<^esub>\<^bsup>n\<^esup> = x\<^bsub>m+1\<^esub>\<^bsup>n\<^esup>" 
  by (induct n, simp_all add:powsum_simps, metis distrib_left)

lemma powsum_shift: "x\<^bsup>k \<^esup>\<cdot> x\<^bsub>m\<^esub>\<^bsup>n\<^esup> = x\<^bsub>k+m\<^esub>\<^bsup>n\<^esup>" 
  by (induct k, simp_all, metis Suc_eq_plus1 mult.assoc powsum_shift1)

lemma powsum_prod_suc: "x\<^bsub>0\<^esub>\<^bsup>m \<^esup>\<cdot> x\<^bsub>0\<^esub>\<^bsup>Suc n\<^esup> = x\<^bsub>0\<^esub>\<^bsup>Suc (m+n)\<^esup>"
proof (induct m)
  case 0 show ?case
    by (simp add: mult_onel plus_nat.add_0 powsum_00)
  case (Suc m) 
  note hyp = this
  show ?case
  proof -
    have "x\<^bsub>0\<^esub>\<^bsup>Suc m \<^esup>\<cdot> x\<^bsub>0\<^esub>\<^bsup>Suc n\<^esup> =  x\<^bsub>0\<^esub>\<^bsup>m\<^esup> \<cdot> x\<^bsub>0\<^esub>\<^bsup>Suc n\<^esup> + x\<^bsup>Suc m \<^esup>\<cdot> x\<^bsub>0\<^esub>\<^bsup>Suc n\<^esup>"
      by (simp add:powsum2 distrib_right')
    also have "... = x\<^bsub>0\<^esub>\<^bsup>Suc (m + n)\<^esup> + x\<^bsup>Suc m \<^esup>\<cdot> x\<^bsub>0\<^esub>\<^bsup>Suc n\<^esup>"
      by (simp add:hyp)
    also have "... = x\<^bsub>0\<^esub>\<^bsup>Suc (m + n)\<^esup> + x\<^bsub>Suc m\<^esub>\<^bsup>Suc n\<^esup>"
      by (subst powsum_shift, simp)
    also have "... = x\<^bsub>0\<^esub>\<^bsup>Suc (m + n)\<^esup> + (x\<^bsub>Suc m\<^esub>\<^bsup>n\<^esup> + x\<^bsup>Suc m + Suc n\<^esup>)"
      by (simp add:powsum2)
    also have "... = x\<^bsub>0\<^esub>\<^bsup>Suc (m + n)\<^esup> + x\<^bsub>Suc m\<^esub>\<^bsup>n\<^esup> + x\<^bsup>Suc (Suc (m + n))\<^esup>"
      by (metis add_Suc_right add_Suc_shift add.assoc add.left_commute)
    also have "... = x\<^bsub>0\<^esub>\<^bsup>Suc (m + n)\<^esup> + x\<^bsup>Suc (Suc (m + n))\<^esup>"
      by (simp only: add_Suc_right[THEN sym] add_Suc_shift[THEN sym] powsum_split_var4)
    also have "... = x\<^bsub>0\<^esub>\<^bsup>Suc (Suc m + n)\<^esup>"
      by (simp add: powsum2)
    finally show ?thesis .
  qed
qed

lemma powsum_prod: "x\<^bsub>0\<^esub>\<^bsup>m \<^esup>\<cdot> x\<^bsub>0\<^esub>\<^bsup>n\<^esup> = x\<^bsub>0\<^esub>\<^bsup>m+n\<^esup>"
  by (cases n, metis (full_types) Nat.add_0_right mult_oner powsum_00, metis add_Suc_right powsum_prod_suc)

end

text {* The following 5 finite suprema laws should be integrated into the Kleene Algebra library *}

lemma setsum_image:
  fixes f :: "'a \<Rightarrow> 'b::join_semilattice_zero"
  assumes "finite X"
  shows "setsum f X = \<Sum>(f ` X)"
using assms 
proof (induct rule: finite_induct)
  case empty thus ?case by simp
next
  case insert thus ?case
    by (metis setsum.insert setsum_fun_insert)
qed

lemma setsum_interval_cong:
  "\<lbrakk> \<And> i. \<lbrakk> m \<le> i; i \<le> n \<rbrakk> \<Longrightarrow> P(i) = Q(i) \<rbrakk> \<Longrightarrow> (\<Sum>i=m..n. P(i)) = (\<Sum>i=m..n. Q(i))"
  by (auto intro: setsum.cong)

lemma setsum_interval_distl:
  fixes f :: "nat \<Rightarrow> 'a::dioid_one_zero"
  assumes "m \<le> n"
  shows "x \<cdot> (\<Sum>i=m..n. f(i)) = (\<Sum>i=m..n. (x \<cdot> f(i)))"
proof -
  have "x \<cdot> (\<Sum>i=m..n. f(i)) = x \<cdot> \<Sum>(f ` {m..n})"
    by (metis finite_atLeastAtMost setsum_image)
  also have "... = \<Sum>{x \<cdot> y |y. y \<in> f ` {m..n}}"
    by (metis finite_atLeastAtMost fset_to_im image_image setsum_fun_distl)
  also have "... = \<Sum>((\<lambda>i. x \<cdot> f i) ` {m..n})"
    by (metis fset_to_im image_image)
  also have "... = (\<Sum>i=m..n. (x \<cdot> f(i)))"
    by (metis finite_atLeastAtMost setsum_image)
  finally show ?thesis .
qed

lemma setsum_interval_distr:
  fixes f :: "nat \<Rightarrow> 'a::dioid_one_zero"
  assumes "m \<le> n"
  shows "(\<Sum>i=m..n. f(i)) \<cdot> y = (\<Sum>i=m..n. (f(i) \<cdot> y))"
  proof -
  have "(\<Sum>i=m..n. f(i)) \<cdot> y = \<Sum>(f ` {m..n}) \<cdot> y"
    by (metis finite_atLeastAtMost setsum_image)
  also have "... = \<Sum>{x \<cdot> y |x. x \<in> f ` {m..n}}"
    by (metis calculation finite_atLeastAtMost finite_imageI fset_to_im setsum_distr)
  also have "... = \<Sum>((\<lambda>i. f(i) \<cdot> y) ` {m..n})"
    by (auto intro: setsum.cong)
  also have "... = (\<Sum>i=m..n. (f(i) \<cdot> y))"
    by (metis finite_atLeastAtMost setsum_image)
  finally show ?thesis .
qed

end