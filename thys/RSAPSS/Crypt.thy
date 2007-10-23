(*  Title:      RSAPSS/Crypt.thy
    ID:         $Id: Crypt.thy,v 1.3 2007-10-23 20:52:24 nipkow Exp $ 
    Author:     Christina Lindenberg, Kai Wirt, Technische Universität Darmstadt
    Copyright:  2005 - Technische Universität Darmstadt 
*)

header "Definition of rsacrypt"

theory Crypt
imports Mod
begin

text {* 
  This theory defines the rsacrypt function which implements RSA using fast
  exponentiation. An proof, that this function calculates RSA is also given
*}

constdefs even :: "nat \<Rightarrow> bool"
  "even n == 2 dvd n"

consts
  rsa_crypt :: "nat \<times> nat \<times> nat => nat"

recdef rsa_crypt "measure(\<lambda>(M,e,n).e)"
  "rsa_crypt (M,0,n) = 1"
  "rsa_crypt (M,Suc e,n) = (if even (Suc e) then ((rsa_crypt (M, (Suc e) div 2,n))^2 mod n) else ((M * ((rsa_crypt (M, Suc e div 2,n))^2 mod n)) mod n))"

lemma div_2_times_2: "(if (even m) then  (m div 2 * 2 = m) else (m div 2 * 2 = m - 1))"
  by (simp add: even_def dvd_eq_mod_eq_0 mult_commute mult_div_cancel)

theorem cryptcorrect[rule_format]: "((n \<noteq> 0) & (n \<noteq> 1)) \<longrightarrow> (rsa_crypt(M,e,n) = M^e mod n)"
  apply (induct_tac M e n rule: rsa_crypt.induct) 
  by (auto simp add: power_mult [THEN sym] div_2_times_2 remainderexp timesmod1)

end
