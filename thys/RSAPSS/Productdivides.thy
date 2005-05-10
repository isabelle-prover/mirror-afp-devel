(*  Title:      RSAPSS/Productdivides.thy
    ID:         $Id: Productdivides.thy,v 1.1 2005-05-10 16:13:46 nipkow Exp $
    Author:     Christina Lindenberg, Kai Wirt, Technische Universität Darmstadt
    Copyright:  2005 - Technische Universität Darmstadt 
*)

header "Lemmata for modular arithmetic with primes"

theory Productdivides
imports Pdifference
begin

lemma productdivides_lemma: "\<lbrakk>x mod z = (0::nat)\<rbrakk> \<Longrightarrow> ((y*x) mod (y*z) = 0)"
  apply (subst mod_eq_0_iff [of "y*x" "y*z"])
by (auto)

lemma productdivides:"\<lbrakk>x mod a = (0::nat); x mod b = 0; a \<in> prime; b \<in> prime; a \<noteq> b\<rbrakk> \<Longrightarrow> x mod (a*b) = 0"
  apply (simp add: mod_eq_0_iff [of "x" "a"])
  apply (erule exE)
  apply (simp);
  apply (rule productdivides_lemma)
  apply (simp add: dvd_eq_mod_eq_0 [THEN sym])
  apply (drule prime_dvd_mult [of "b"])
  apply (assumption)
  apply (erule disjE)
  apply (auto)
  apply (simp add:prime_def)
  by (auto)

lemma specializedtoprimes1: "\<lbrakk>p \<in> prime; q \<in> prime; p \<noteq> q; a mod p = b mod p ; a mod q = b mod q\<rbrakk> \<Longrightarrow> a mod (p*q) = b mod (p*q)" 
  apply (drule equalmodstrick2)+
  apply (rule equalmodstrick1)
  apply (rule productdivides)
  by (auto)

lemma specializedtoprimes1a: "\<lbrakk>p \<in> prime; q \<in> prime; p \<noteq> q; a mod p = b mod p; a mod q = b mod q; b < p*q \<rbrakk> \<Longrightarrow> a mod (p*q) = b"
  apply (subst specializedtoprimes1)
  by (auto)

end
