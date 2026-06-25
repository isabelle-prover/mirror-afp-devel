(*  Title:  FallFactorial.thy
    Author: Jacques D. Fleuriot, University of Edinburgh, 2026
*)

section\<open>Generalized falling factorial\<close>

theory FallFactorial
imports "HOL.Binomial" "HOL.Rat"
begin

definition 
  "fallfactpow  (a::'a::comm_ring_1) n = (if n = 0 then 1 else prod (\<lambda>n. a - of_nat n) {0 .. n - 1})"
 
lemma fallfactpow_0[simp]: "fallfactpow a 0 = 1" 
  by (simp add: fallfactpow_def)

lemma fallfactpow_1[simp]: "fallfactpow a 1 = a" by (simp add: fallfactpow_def)
lemma fallfactpow_Suc0[simp]: "fallfactpow a (Suc 0) = a" by (simp add: fallfactpow_def)

lemma fallfactpow_Suc_setprod: "fallfactpow a (Suc n) = prod (\<lambda>n. a - of_nat n) {0 .. n}"
  by (simp add: fallfactpow_def)

subsection\<open>Falling factorial expressed recursively\<close>

lemma fallfactpow_Suc: "fallfactpow a (Suc n) = fallfactpow a n * (a - of_nat n)"
proof-
  {assume "n=0" then have ?thesis by simp}
  moreover
  {fix m assume m: "n = Suc m"
    have ?thesis  unfolding m fallfactpow_Suc_setprod prod.atLeast0_atMost_Suc by blast }
  ultimately show ?thesis by (cases n, auto)
qed 


lemma fallfactpow_rec: "fallfactpow a (Suc n) = a * fallfactpow (a - 1) n"
proof-
  {assume "n=0" 
    then have ?thesis 
      by (simp add: fallfactpow_Suc_setprod)}
  moreover
  {assume n0: "n \<noteq> 0"
    have th0: "finite {1 .. n}" "0 \<notin> {1 .. n}" by auto
    have eq: "insert 0 {1 .. n} = {0..n}" by auto
    have th1: "(\<Prod>n\<in>{1::nat..n}. a - of_nat n) =
      (\<Prod>n\<in>{0::nat..n - 1}. a - (1 + of_nat n))"
      apply (rule prod.reindex_cong [where l = Suc])
      using n0 by (auto simp add: fun_eq_iff field_simps)
    have ?thesis 
      apply (simp add: fallfactpow_def)
    unfolding prod.insert[OF th0, unfolded eq]
    using th1 by (simp add: field_simps)}
  ultimately show ?thesis 
    by blast
qed

lemma fallfactpow_base_zero[simp]: "fallfactpow 0 (Suc n) = 0"
by (simp add: fallfactpow_rec)

lemma fallfactpow_fact: "of_nat(fact n) =  fallfactpow (of_nat n) n"
proof (induct n)
  case 0
  then show ?case
    by simp 
next
  case (Suc n)
  then show ?case
    by (metis add_diff_cancel_left' fact_Suc fallfactpow_rec id_apply 
        of_nat_Suc of_nat_eq_id of_nat_mult) 
qed

lemma fallfactpow_altdef:
  "fallfactpow a k = (\<Prod>i<k. a - of_nat i)"
proof (induct k)
  case 0
  then show ?case by simp
next
  case (Suc k)
  then show ?case
    by (simp add: fallfactpow_Suc) 
qed

text\<open>The falling factorial and Pochammer functions\<close>

lemma pochhammer_fallfactpow_eq:
  "pochhammer a n = fallfactpow (a + of_nat n - 1) n"
proof (induct n)
  case 0
  then show ?case     
    by simp 
next
  case (Suc n)
  then show ?case
    by (simp add: fallfactpow_rec pochhammer_rec')
qed

lemma fallfactpow_of_nat_eq_0_lemma [simp]:
  assumes kn: "k > n" 
  shows "fallfactpow (of_nat n :: 'a:: idom) k = 0"
  by (metis cancel_comm_monoid_add_class.diff_cancel fallfactpow_altdef 
      finite_lessThan kn lessThan_iff prod_zero_iff)

lemma setprod_zero_of_nat_diff_lemma:
  "a < k \<Longrightarrow> (\<Prod>i<k. of_nat (a - i)) = (0::'a::comm_semiring_1)"
by (force intro: prod_zero)

lemma fallfactpow_of_nat_altdef:
  "fallfactpow (of_nat a :: 'a :: idom) k = ((\<Prod>i<k. of_nat (a - i)) :: 'a :: idom)"
proof (cases "k > a")
  case True
  then show ?thesis
    by (simp add:  setprod_zero_of_nat_diff_lemma) 
next
  case False
  then show ?thesis 
    by (auto intro!: prod.cong simp add: fallfactpow_altdef)
qed

lemma fallfactpow_ge_zero: 
  "of_nat k < j \<Longrightarrow> 0 \<le> fallfactpow (j::'a::{linordered_idom}) k"
proof (induct k)
  case 0
  then show ?case
    by simp 
next
  case (Suc k)
  then show ?case
    by (simp add: fallfactpow_Suc) 
qed

lemma fallfactpow_le_power_self [simp]:
  "fallfactpow (of_nat k ::'a::{linordered_idom}) k \<le> of_nat k ^ k"
proof(induct k)
  case 0
  then show ?case
    by simp 
next
  case (Suc k)
  then show ?case
  proof (auto simp add: fallfactpow_rec mult_le_cancel_left)
    assume "(0::'a::linordered_idom) < 1 + of_nat k"
       have "of_nat k ^ k \<le> ((1::'a::linordered_idom) + of_nat k) ^ k"
         by (simp add: power_mono)        
       then show "fallfactpow (of_nat k) k \<le> ((1::'a::linordered_idom) + of_nat k) ^ k"
         using Suc by linarith
    next
      assume "1 + of_nat k < (0::'a::linordered_idom)"
      then show "(1 + of_nat k) ^ k \<le> fallfactpow (of_nat k) k" 
        by (metis of_nat_1 of_nat_add of_nat_less_0_iff)
  qed
qed


lemma fallfactpow_le_power:
  assumes "of_nat k \<le> j" 
  shows "fallfactpow (j::'a::{linordered_idom}) k \<le> j ^ k"
proof cases 
  assume "of_nat k = j"
  then show ?thesis
    using fallfactpow_le_power_self by blast 
next
  assume "of_nat k \<noteq> j"
  then have "of_nat k < j"
    by (simp add: assms order.not_eq_order_implies_strict)
  then show ?thesis
  proof(induct k)
    case 0
    then show ?case
      by simp 
  next
    case (Suc k)
    then have "fallfactpow j k \<le> j ^ k"
      by simp
    moreover have "of_nat k + 1 < j"
      using Suc.prems by auto
    ultimately have "(j - of_nat k) * fallfactpow j k \<le> j * j ^ k"
      by (auto intro!: mult_mono' fallfactpow_ge_zero)
    then show ?case
      by (simp add: fallfactpow_Suc mult.commute) 
  qed
qed

lemma fallfactpow_ge_zero' [simp]:
  "fallfactpow (of_nat n) k \<ge> (0::'a::linordered_idom)"
  by (metis eq_iff fallfactpow_fact fallfactpow_ge_zero fallfactpow_of_nat_eq_0_lemma 
      less_imp_of_nat_less less_linear of_nat_0_le_iff)

subsection\<open>Falling factorial and binomial coefficients\<close>
lemma binomial_fallfactpow_altdef_of_nat: 
  "of_nat (n choose k) =
          (fallfactpow (of_nat n) k :: 'a :: {field_char_0})/fact k"
  by (simp add: binomial_gbinomial gbinomial_pochhammer' pochhammer_fallfactpow_eq)

lemma binomial_fallfactpow_ring:
  "fallfactpow (a + b :: 'a::{comm_ring_1}) n =
  (\<Sum>k=0..n. of_nat(n choose k) * fallfactpow a (n - k) * fallfactpow b k)"
proof(induction n)
  case 0 show ?case by simp
next
  case (Suc n)
  have "(\<Sum>k = 0..Suc n.
               of_nat (Suc n choose k) * fallfactpow a (Suc n - k) * fallfactpow b k) =
         fallfactpow a (Suc n) + 
         (\<Sum>k = 1..Suc n.
               of_nat (Suc n choose k) * fallfactpow a (Suc n - k) * fallfactpow b k)"
           by (simp add: sum.atLeast_Suc_atMost)
  moreover have "\<dots> = fallfactpow a (Suc n) + 
                  (\<Sum>k = 1..Suc n. (of_nat(n choose (k - 1)) + of_nat(n choose k)) * fallfactpow a (Suc n - k) * fallfactpow b k)"
           by (simp add: sum.shift_bounds_cl_Suc_ivl del: sum.cl_ivl_Suc)
  moreover have "\<dots> = fallfactpow a (Suc n) + 
                  (\<Sum>k = 1..Suc n. of_nat(n choose (k - 1)) * fallfactpow a (Suc n - k) * fallfactpow b k) + 
                  (\<Sum>k = 1..Suc n. of_nat(n choose k) * fallfactpow a (Suc n - k) * fallfactpow b k)"
           by (simp add: sum.distrib [symmetric] distrib_right del: sum.cl_ivl_Suc)
  moreover have "\<dots> = fallfactpow a (Suc n) + 
                  (\<Sum>k = 0..n. of_nat(n choose k) * fallfactpow a (n - k) * fallfactpow b (k + 1)) + 
                  (\<Sum>k = 1..Suc n. of_nat(n choose k) * fallfactpow a (Suc n - k) * fallfactpow b k)"
           by (simp add: sum.shift_bounds_cl_Suc_ivl  del: sum.cl_ivl_Suc)
  moreover have "\<dots> = fallfactpow a (Suc n) + 
                  (\<Sum>k = 0..n. of_nat(n choose k) * fallfactpow a (n - k) * fallfactpow b (k + 1)) + 
                  (\<Sum>k = 1..Suc n. of_nat(n choose k) * fallfactpow a (Suc n - k) * fallfactpow b k)"
           by (simp add: sum.shift_bounds_cl_Suc_ivl  del: sum.cl_ivl_Suc)
  moreover have "\<dots> = (\<Sum>k = 0..n. of_nat(n choose k) * fallfactpow a (n - k) * fallfactpow b (k + 1)) + 
                  (\<Sum>k = 0..Suc n. of_nat(n choose k) * fallfactpow a (Suc n - k) * fallfactpow b k)"
           by (simp add: sum.atLeast_Suc_atMost)
  moreover have "\<dots> = (\<Sum>k = 0..n. of_nat(n choose k) * fallfactpow a (n - k) * fallfactpow b (k + 1)) + 
                      (\<Sum>k = 0..n. of_nat(n choose k) * fallfactpow a (Suc (n - k)) * fallfactpow b k)"
           by (simp add:  binomial_eq_0 Suc_diff_le)
  moreover have "\<dots> = (\<Sum>k = 0..n. of_nat(n choose k) * fallfactpow a (n - k) * fallfactpow b k * (b - of_nat k)) + 
                      (\<Sum>k = 0..n. of_nat(n choose k) * fallfactpow a (n - k) * fallfactpow b k * (a - of_nat (n - k)))"
           by (simp add:  fallfactpow_Suc algebra_simps)
  moreover have "\<dots> = (\<Sum>k = 0..n. of_nat(n choose k) * fallfactpow a (n - k) * fallfactpow b k *
                        ((a - of_nat n + of_nat k) + (b - of_nat k)))"
           by (simp add: sum.distrib [symmetric] algebra_simps)
  moreover have "\<dots> = (\<Sum>k = 0..n. of_nat(n choose k) * fallfactpow a (n - k) * fallfactpow b k *
                        (a + b - of_nat n))"
           by (simp add: algebra_simps)
  moreover have "\<dots> = (\<Sum>k = 0..n. of_nat(n choose k) * fallfactpow a (n - k) * fallfactpow b k) * (a + b - of_nat n)"
           by (simp add: sum_distrib_right)
  moreover have "\<dots> = fallfactpow (a + b) n * (a + b - of_nat n)" using Suc  by metis
  ultimately show ?case by (metis fallfactpow_Suc)  
qed

(*  Not proven before *)
lemma binomial_vandermonde:
  "(r + s)^ k/fact k = 
   (\<Sum>i = 0..k. (r::'a :: field_char_0) ^ i / fact i *  s ^ (k - i) / fact (k - i))"
proof - 
   have "(r + s)^ k  =  (\<Sum>i = 0..k. of_nat (k choose i) * r ^ i * s ^ (k - i))"
     using binomial_ring atLeast0AtMost by auto 
   then have  "(r + s)^ k = (\<Sum>i = 0..k.  fact k / (fact i * fact (k - i)) * r ^ i * s ^ (k - i))"
     using binomial_fact sum.cong atLeastAtMost_iff by (metis (no_types, lifting)) 
   then show ?thesis by (simp add: field_simps sum_distrib_left)
qed

lemma natsum_reverse_index:
  fixes m::nat
  shows "(\<And>k. m \<le> k \<Longrightarrow> k \<le> n \<Longrightarrow> g k = f (m + n - k)) \<Longrightarrow> (\<Sum>k=m..n. f k) = (\<Sum>k=m..n. g k)"
  by (metis add.commute atLeastAtMost_iff sum.atLeastAtMost_rev sum.cong)

lemma binomial_fallfactpow_vandermonde:
  "fallfactpow (r + s) k/fact k = 
   (\<Sum>i = 0..k. fallfactpow (r::'a :: field_char_0) i / fact i *  fallfactpow s (k - i) / fact (k - i))"
proof -
   have "fallfactpow (r + s) k  =  (\<Sum>i = 0..k. of_nat (k choose i) * fallfactpow r i * fallfactpow s (k - i))"
     using binomial_fallfactpow_ring 
      by (metis (no_types, lifting) add.left_neutral binomial_symmetric diff_diff_cancel 
         natsum_reverse_index) 
   then have "fallfactpow (r + s) k = 
              (\<Sum>i = 0..k.  fact k / (fact i * fact (k - i)) * fallfactpow r i * fallfactpow s (k - i))"
      using binomial_fact sum.cong atLeastAtMost_iff  by (metis (no_types, lifting)) 
   then show ?thesis by (simp add: field_simps sum_distrib_left)
qed

lemma gbinomial_fallfactpow: "a gchoose n = fallfactpow a n / fact n"
  by (simp add: gbinomial_pochhammer' pochhammer_fallfactpow_eq)

lemma binomial_fallfactpow_vandermonde_alt:
  "fallfactpow (r + s) k/fact k = 
   (\<Sum>i = 0..k.  ((r::'a :: field_char_0) gchoose i) *   (s gchoose (k - i)))"
by (simp add: binomial_fallfactpow_vandermonde gbinomial_fallfactpow)

end
