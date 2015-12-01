(*  Title:      RSAPSS/Productdivides.thy
    Author:     Christina Lindenberg, Kai Wirt, Technische Universität Darmstadt
    Copyright:  2005 - Technische Universität Darmstadt 
*)

section "Lemmata for modular arithmetic with primes"

theory Productdivides
imports Pdifference
begin

lemma productdivides_lemma: "\<lbrakk>x mod z = (0::nat)\<rbrakk> \<Longrightarrow> ((y*x) mod (y*z) = 0)"
  apply (subst mod_eq_0_iff [of "y*x" "y*z"])
  apply auto
  done

lemma productdivides: "\<lbrakk>x mod a = (0::nat); x mod b = 0; prime a; prime b; a \<noteq> b\<rbrakk> \<Longrightarrow> x mod (a*b) = 0"
  apply (simp add: mod_eq_0_iff [of x a])
  apply (erule exE)
  apply (simp)
  apply (rule disjI2)
  apply (simp add: dvd_eq_mod_eq_0 [symmetric])
  apply (drule prime_dvd_mult_nat [of b])
  apply (erule disjE)
  apply auto
  apply (simp add: prime_def)
  apply auto
  done

lemma specializedtoprimes1: 
  fixes p::nat 
  shows "\<lbrakk>prime p; prime q; p \<noteq> q; a mod p = b mod p ; a mod q = b mod q\<rbrakk>
         \<Longrightarrow> a mod (p*q) = b mod (p*q)"
by (metis equalmodstrick1 equalmodstrick2 productdivides) 

lemma specializedtoprimes1a:
 fixes p::nat 
 shows "\<lbrakk>prime p; prime q; p \<noteq> q; a mod p = b mod p; a mod q = b mod q; b < p*q \<rbrakk>
    \<Longrightarrow> a mod (p*q) = b"
by (metis Divides.mod_less specializedtoprimes1)

end
