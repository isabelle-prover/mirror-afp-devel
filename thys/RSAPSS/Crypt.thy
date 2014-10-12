(*  Title:      RSAPSS/Crypt.thy
 
    Author:     Christina Lindenberg, Kai Wirt, Technische Universität Darmstadt
    Copyright:  2005 - Technische Universität Darmstadt 
*)

header "Definition of rsacrypt"

theory Crypt
imports Mod "~~/src/HOL/Parity"
begin

text {* 
  This theory defines the rsacrypt function which implements RSA using fast
  exponentiation. An proof, that this function calculates RSA is also given
*}

fun rsa_crypt :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"
where
  "rsa_crypt M 0 n = 1"
| "rsa_crypt M (Suc e) n = (if 2 dvd Suc e
       then (rsa_crypt M (Suc e div 2) n) ^ 2 mod n
       else (M * ((rsa_crypt M (Suc e div 2) n) ^ 2 mod n)) mod n)"

theorem cryptcorrect: "n \<noteq> 0 \<Longrightarrow> n \<noteq> 1 \<Longrightarrow> rsa_crypt M e n = M ^ e mod n"
  by (induct M e n rule: rsa_crypt.induct)
    (auto simp add: dvd_eq_mod_eq_0 div_mod_equality' power_mult [symmetric] remainderexp timesmod1)

end

