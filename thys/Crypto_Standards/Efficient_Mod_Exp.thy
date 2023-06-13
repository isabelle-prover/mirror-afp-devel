theory Efficient_Mod_Exp
  imports PKCS1v2_2
          "HOL-Library.Power_By_Squaring"

begin

text \<open>The problem is that codegen can't compute RSAEP (which is simply modular exponentiation) 
in a straightforward manner.  We need to tell codegen how to efficiently compute x^e mod n.  We 
use HOL-Library.Power_by_Squaring for this.  We show that RSAEP can be expressed in terms
of Power_by_Squaring.efficient_funpow and use its existing code equations.\<close>

definition mod_mult :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "mod_mult n a b = (a*b) mod n" 

lemma mod_mult_exp_not1: 
  assumes "1 \<noteq> n"
  shows   "((mod_mult n) x ^^ e) 1 = (x^e) mod n"
proof (induction e)
  case 0
  then show ?case using assms by fastforce
next
  case (Suc n)
  then show ?case by (metis funpow.simps(2) mod_mult_def mod_mult_right_eq o_apply power.simps(2))
qed

lemma mod_mult_by_squaring_not1: 
  assumes "1 \<noteq> n"
  shows   "efficient_funpow (mod_mult n) 1 x e = (x^e) mod n"
  by (metis assms efficient_funpow_correct mod_mult_def mod_mult_exp_not1 mod_mult_left_eq
            mod_mult_right_eq mult.assoc)

lemma RSAEP_efficient [code]:
  "PKCS1_RSAEP n e m = 
  ( if (n \<noteq> 1) then efficient_funpow (mod_mult n) 1 m e 
               else 0)"
  using PKCS1_RSAEP_def mod_mult_by_squaring_not1 by presburger

end