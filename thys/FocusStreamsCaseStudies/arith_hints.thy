(*<*)
(*
   Title:  Theory arith_hints.thy 
   Author: Maria Spichkova <maria.spichkova at rmit.edu.au>, 2013
*)
(*>*)

header {* Auxiliary arithmetic lemmas *}

theory arith_hints
imports Main
begin


lemma arith_mod_neq:
  assumes h1:"a mod n \<noteq> b mod n"
  shows "a \<noteq> b"
using assms by auto 


lemma arith_mod_nzero: 
  fixes i::nat
  assumes h1: "i < n" 
      and h2:"0 < i"
  shows "0 < (n * t + i) mod n"
proof -
  from h1 and h2 have  sg1:"(i + n * t) mod n = i"
    by (simp add: mod_mult_self2)
  also have sg2:"n * t + i = i + n * t"  by simp
  from this and h1 and h2 show ?thesis
    by (simp (no_asm_simp))
qed


lemma arith_mult_neq_nzero1:
  fixes i::nat
  assumes h1:"i < n"
      and h2:"0 < i"
  shows "i + n * t \<noteq> n * q"
proof -
  from h1 and h2 have sg1:"(i + n * t) mod n = i"
    by (simp add: mod_mult_self2)
  also have sg2:"(n * q) mod n = 0"  by simp
  from this and h1 and h2 have "(i + n * t) mod n \<noteq> (n * q) mod n"
    by simp
  from this show ?thesis  by (rule arith_mod_neq)
qed


lemma arith_mult_neq_nzero2:
  fixes i::nat
  assumes h1:"i < n"
      and h2:"0 < i"
  shows "n * t + i \<noteq> n * q"
proof - 
  from h1 and h2 have "i + n * t \<noteq> n * q" 
    by (rule arith_mult_neq_nzero1)
  from this show ?thesis by simp
qed


lemma arith_mult_neq_nzero3:
  fixes i::nat
  assumes h1:"i < n"
      and h2:"0 < i"
  shows "n + n * t + i \<noteq> n * qc"
proof -
   from h1 and h2 have sg1: "n *(Suc t) + i  \<noteq> n * qc"
     by (rule arith_mult_neq_nzero2)
   have sg2: "n + n * t + i = n *(Suc t) + i" by simp
   from sg1 and sg2  show ?thesis  by arith
qed


lemma arith_modZero1:
  "(t + n * t) mod Suc n = 0"
proof - 
  have "((Suc n) * t) mod Suc n = 0" by (rule mod_mult_self1_is_0)
  from this show ?thesis by simp
qed


lemma arith_modZero2:
  "Suc (n + (t + n * t)) mod Suc n = 0"
proof -
  have "((Suc n) * (Suc t)) mod Suc n = 0" by (rule mod_mult_self1_is_0)
  from this show ?thesis by simp
qed


lemma arith1:
  assumes h1:"Suc n * t = Suc n * q"
  shows "t = q"
proof -
  have "Suc n * t = Suc n * q = (t = q | (Suc n) = (0::nat))"
    by (rule mult_cancel1)
  from this and h1 show ?thesis by simp
qed


lemma arith2:
  fixes t n q :: "nat"
  assumes h1:"t + n * t = q + n * q"
  shows "t = q"
proof -
  have sg1:"t + n * t = (Suc n) * t" by auto
  have sg2:"q + n * q = (Suc n) * q" by auto
  from h1 and sg1 and sg2 have "Suc n * t = Suc n * q" by arith
  from this show ?thesis by (rule arith1)
qed

end