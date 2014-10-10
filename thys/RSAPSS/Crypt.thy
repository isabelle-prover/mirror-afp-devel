(*  Title:      RSAPSS/Crypt.thy
 
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

definition
  even :: "nat \<Rightarrow> bool" where
  "even n \<longleftrightarrow> 2 dvd n"

fun rsa_crypt :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"
where
  "rsa_crypt M 0 n = 1"
| "rsa_crypt M (Suc e) n = (if even (Suc e)
       then (rsa_crypt M (Suc e div 2) n) ^ 2 mod n
       else (M * ((rsa_crypt M (Suc e div 2) n) ^ 2 mod n)) mod n)"

lemma div_2_times_2: "(if (even m) then  (m div 2 * 2 = m) else (m div 2 * 2 = m - 1))"
  by (simp add: even_iff_mod_2_eq_zero dvd_eq_mod_eq_0 mult.commute mult_div_cancel)

theorem cryptcorrect: "n \<noteq> 0 \<Longrightarrow> n \<noteq> 1 \<Longrightarrow> rsa_crypt M e n = M^e mod n"
  by (induct M e n rule: rsa_crypt.induct) 
    (auto simp add: power_mult [symmetric] div_2_times_2 remainderexp timesmod1)

end
