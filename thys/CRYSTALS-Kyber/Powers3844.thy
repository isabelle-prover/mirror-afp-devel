theory Powers3844

imports Main Kyber_Values

begin
section \<open>Checking Powers of Root of Unity\<close>
text \<open>In order to check, that $3844$ is indeed a root of unity, we need to calculate all powers 
and show that they are not equal to one.\<close>
fun fast_exp_7681 ::" int \<Rightarrow> nat \<Rightarrow> int" where
"fast_exp_7681 x 0 = 1" |
"fast_exp_7681 x (Suc e) = (x * (fast_exp_7681 x e)) mod 7681"

lemma list_all_fast_exp_7681: 
"list_all (\<lambda>l. fast_exp_7681 (3844::int) l \<noteq> 1) [1..<256]"
by (subst upt_conv_Cons, simp, subst list_all_simps(1), intro conjI, eval)+ 
   force

lemma fast_exp_7681_to_mod_ring: 
"fast_exp_7681 x e = to_int_mod_ring ((of_int_mod_ring x :: fin7681 mod_ring)^e)"
proof (induct e arbitrary: x rule: fast_exp_7681.induct)
  case (2 x e)
  then show ?case
  by (metis (no_types, lifting) Suc_inject fast_exp_7681.elims kyber7681.module_spec_axioms 
    module_spec.CARD_a nat.simps(3) of_int_mod_ring.rep_eq of_int_mod_ring_mult 
    of_int_mod_ring_to_int_mod_ring power_Suc to_int_mod_ring.rep_eq)
qed auto

lemma fast_exp_7681_less256:
assumes "0<l" "l<256"
shows "fast_exp_7681 3844 l \<noteq> 1"
using list_all_fast_exp_7681 assms 
by (smt (verit, ccfv_threshold) Ball_set One_nat_def atLeastLessThan_iff 
  bot_nat_0.not_eq_extremum fast_exp_7681.elims less_Suc_numeral less_nat_zero_code 
  not_less numeral_One numeral_less_iff set_upt)

lemma powr_less256:
assumes "0<l" "l<256"
shows "(3844::fin7681 mod_ring)^l \<noteq> 1"
using fast_exp_7681_less256[OF assms] unfolding fast_exp_7681_to_mod_ring
by (metis of_int_numeral of_int_of_int_mod_ring to_int_mod_ring_hom.hom_one)


end