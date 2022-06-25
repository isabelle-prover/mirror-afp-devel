subsection \<open>Simulation of a Register Machine\<close>

theory RegisterMachineSimulation
  imports RegisterMachineProperties "Digit_Expansions.Binary_Operations"
begin

definition B :: "nat \<Rightarrow> nat" where
  "(B c) = 2^(Suc c)"

definition "RLe c p b q l = (\<Sum>t = 0..q. b^t * R c p l t)"
definition "SKe c p b q k = (\<Sum>t = 0..q. b^t * S c p k t)"
definition "ZLe c p b q l = (\<Sum>t = 0..q. b^t * Z c p l t)"

fun sum_radd :: "program \<Rightarrow> register \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat"
  where "sum_radd p l f = (\<Sum>k = 0..length p-1. if isadd (p!k) \<and> l = modifies (p!k) then f k else 0)"

abbreviation sum_radd_abbrev ("\<Sum>R+ _ _ _" [999, 999, 999] 1000)
  where "(\<Sum>R+ p l f) \<equiv> (sum_radd p l f)"

fun sum_rsub :: "program \<Rightarrow> register \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat"
  where "sum_rsub p l f = (\<Sum>k = 0..length p-1. if issub (p!k) \<and> l = modifies (p!k) then f k else 0)"

abbreviation sum_rsub_abbrev ("\<Sum>R- _ _ _ " [999, 999, 999] 1000)
  where "(\<Sum>R- p l f) \<equiv> (sum_rsub p l f)"

(* Note: different naming convention for sums compared to original paper *)
fun sum_sadd :: "program \<Rightarrow> state \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat"
  where "sum_sadd p d f = (\<Sum>k = 0..length p-1. if isadd (p!k) \<and> d = goes_to (p!k) then f k else 0)"

abbreviation sum_sadd_abbrev ("\<Sum>S+ _ _ _ " [999, 999, 999] 1000)
  where "(\<Sum>S+ p d f) \<equiv> (sum_sadd p d f)"

(* careful: f needs be passed the program so that z l t can be properly called with l = modifies (p!k) *)
fun sum_ssub_nzero :: "program \<Rightarrow> state \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat"
  where "sum_ssub_nzero p d f = (\<Sum>k = 0..length p-1. if issub (p!k) \<and> d = goes_to (p!k) then f k else 0)"

abbreviation sum_ssub_nzero_abbrev ("\<Sum>S- _ _ _ " [999, 999, 999] 1000)
  where "(\<Sum>S- p d f) \<equiv> (sum_ssub_nzero p d f)"

fun sum_ssub_zero :: "program \<Rightarrow> state \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat"
  where "sum_ssub_zero p d f = (\<Sum>k = 0..length p-1. if issub (p!k) \<and> d = goes_to_alt (p!k) then f k else 0)"

abbreviation sum_ssub_zero_abbrev ("\<Sum>S0 _ _ _ " [999, 999, 999] 1000)
  where "(\<Sum>S0 p d f) \<equiv> (sum_ssub_zero p d f)"

declare sum_radd.simps[simp del]
declare sum_rsub.simps[simp del]
declare sum_sadd.simps[simp del]
declare sum_ssub_nzero.simps[simp del]
declare sum_ssub_zero.simps[simp del]

text \<open>Special sum cong lemmas\<close>

lemma sum_sadd_cong:
  assumes "\<forall>k. k \<le> length p-1 \<and> isadd (p!k) \<and> l = goes_to (p!k) \<longrightarrow> f k = g k"
  shows "\<Sum>S+ p l f = \<Sum>S+ p l g"
  unfolding sum_sadd.simps
  by (rule sum.cong, simp) (rule if_cong, simp_all add: assms)

lemma sum_ssub_nzero_cong:
  assumes "\<forall>k. k \<le> length p - 1 \<and> issub (p!k) \<and> l = goes_to (p!k) \<longrightarrow> f k = g k"
  shows "\<Sum>S- p l f = \<Sum>S- p l g"
  unfolding sum_ssub_nzero.simps
  by (rule sum.cong, simp) (rule if_cong, simp_all add: assms)

lemma sum_ssub_zero_cong:
  assumes "\<forall>k. k \<le> length p - 1 \<and> issub (p!k) \<and> l = goes_to_alt (p!k) \<longrightarrow> f k = g k"
  shows "\<Sum>S0 p l f = \<Sum>S0 p l g"
  unfolding sum_ssub_zero.simps
  by (rule sum.cong, simp) (rule if_cong, simp_all add: assms)

lemma sum_radd_cong:
  assumes "\<forall>k. k \<le> length p - 1 \<and> isadd (p!k) \<and> l = modifies (p!k) \<longrightarrow> f k = g k"
  shows "\<Sum>R+ p l f = \<Sum>R+ p l g"
  unfolding sum_radd.simps
  by (rule sum.cong, simp) (rule if_cong, simp_all add: assms)

lemma sum_rsub_cong:
  assumes "\<forall>k. k \<le> length p - 1 \<and> issub (p!k) \<and> l = modifies (p!k) \<longrightarrow> f k = g k"
  shows "\<Sum>R- p l f = \<Sum>R- p l g"
  unfolding sum_rsub.simps
  by (rule sum.cong, simp) (rule if_cong, simp_all add: assms)



text \<open>Properties and simple lemmas\<close>
lemma RLe_equivalent: "RL c p b q l = RLe c p b q l"
  by (induction q arbitrary: c) (auto simp add: RLe_def R_def RL.simps(1) RL_simp)

lemma SKe_equivalent: "SK c p b q k = SKe c p b q k"
  by (induction q arbitrary: c) (auto simp add: SKe_def S_def SK.simps(1) S2_def SK_simp)

lemma ZLe_equivalent: "ZL c p b q l = ZLe c p b q l"
  by (induction q arbitrary: c) (auto simp add: ZLe_def ZL.simps(1) R_def Z2_def Z_def ZL_simp)


lemma sum_radd_distrib: "a * (\<Sum>R+ p l f) = (\<Sum>R+ p l (\<lambda>k. a * f k))"
  by (auto simp add: sum_radd.simps sum_distrib_left; smt mult_is_0 sum.cong)

lemma sum_rsub_distrib: "a * (\<Sum>R- p l f) = (\<Sum>R- p l (\<lambda>k. a * f k))"
  by (auto simp add: sum_rsub.simps sum_distrib_left; smt mult_is_0 sum.cong)

lemma sum_sadd_distrib: "a * (\<Sum>S+ p d f) = (\<Sum>S+ p d (\<lambda>k. a * f k))" for a
  by (auto simp add: sum_sadd.simps sum_distrib_left; smt mult_is_0 sum.cong)

lemma sum_ssub_nzero_distrib: "a * (\<Sum>S- p d f) = (\<Sum>S- p d (\<lambda>k. a * f k))" for a
  by (auto simp add: sum_ssub_nzero.simps sum_distrib_left; smt mult_is_0 sum.cong)

lemma sum_ssub_zero_distrib: "a * (\<Sum>S0 p d f) = (\<Sum>S0 p d (\<lambda>k. a * f k))" for a
  by (auto simp add: sum_ssub_zero.simps sum_distrib_left; smt mult_is_0 sum.cong)

lemma sum_distrib:
  fixes SX :: "program \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat"
    and p :: program

assumes SX_simps: "\<And>h. SX p x h = (\<Sum>k = 0..length p-1. if g x k then h k else 0)"

shows "SX p x h1 + SX p x h2 = SX p x (\<lambda>k. h1 k + h2 k)"
  by (subst SX_simps)+ (auto simp: sum.distrib[symmetric] intro: sum.cong)

lemma sum_commutative:
  fixes SX :: "program \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat"
    and p :: program

assumes SX_simps: "\<And>h. SX p x h = (\<Sum>k = 0..length p-1. if g x k then h k else 0)"

  shows "(\<Sum>t=0..q::nat. SX p x (\<lambda>k. f k t))
       = (SX p x (\<lambda>k. \<Sum>t=0..q. f k t))"
proof (induction q)
  case 0
  then show ?case by (auto)
next
  case (Suc q)
  have SX_add: "SX p x h1 + SX p x h2 = SX p x (\<lambda>k. h1 k + h2 k)" for h1 h2
    by (subst sum_distrib[where ?h1.0 = "h1"]) (auto simp: SX_simps) +

  have h1: "(\<Sum>t\<le>(Suc q). SX p x (\<lambda>k. f k t)) = SX p x (\<lambda>k. f k (Suc q)) + sum (\<lambda>t. SX p x (\<lambda>k. f k t)) {0..q}"
    by (auto simp add: sum.atLeast0_atMost_Suc add.commute atMost_atLeast0)
  also have h2: "... = SX p x (\<lambda>k. f k (Suc q)) + SX p x (\<lambda>k. sum (f k){0..q})"
    using Suc.IH Suc.prems by auto
  also have h3: "... = SX p x (\<lambda>k. sum (f k) {0..(Suc q)})"
    by (subst SX_add) (auto simp: atLeast0_atMost_Suc)
  finally show ?case using Suc.IH by (simp add: atMost_atLeast0)
qed

lemma sum_radd_commutative: "(\<Sum>t=0..(q::nat). \<Sum>R+ p l (\<lambda>k. f k t)) = (\<Sum>R+ p l (\<lambda>k. \<Sum>t=0..q. f k t))"
  by (rule sum_commutative sum_radd.simps) +
lemma sum_rsub_commutative: "(\<Sum>t=0..(q::nat). \<Sum>R- p l (\<lambda>k. f k t)) = (\<Sum>R- p l (\<lambda>k. \<Sum>t=0..q. f k t))"
  by (rule sum_commutative sum_rsub.simps) +
lemma sum_sadd_commutative: "(\<Sum>t=0..(q::nat). \<Sum>S+ p l (\<lambda>k. f k t)) = (\<Sum>S+ p l (\<lambda>k. \<Sum>t=0..q. f k t))"
  by (rule sum_commutative sum_sadd.simps) +
lemma sum_ssub_nzero_commutative: "(\<Sum>t=0..(q::nat). \<Sum>S- p l (\<lambda>k. f k t)) = (\<Sum>S- p l (\<lambda>k. \<Sum>t=0..q. f k t))"
  by (rule sum_commutative sum_ssub_nzero.simps) +
lemma sum_ssub_zero_commutative: "(\<Sum>t=0..(q::nat). \<Sum>S0 p l (\<lambda>k. f k t)) = (\<Sum>S0 p l (\<lambda>k. \<Sum>t=0..q. f k t))"
  by (rule sum_commutative sum_ssub_zero.simps) +

lemma sum_int: "c \<le> a + b \<Longrightarrow> int(a + b - c) = int(a) + int(b) - int(c)"
  by (simp add: SMT.int_plus)

lemma ZLe_bounded: "b > 2 \<Longrightarrow> ZLe c p b q l < b ^ (Suc q)"
  using Z_bounded ZLe_def
proof (induction q)
  case 0
  then show ?case by (simp add: Z_bounded ZLe_def Z_def)
next
  case (Suc q)
  have "ZLe c p b (Suc q) l = b ^ (Suc q) * Z c p l (Suc q) + ZLe c p b q l"
    by (auto simp: ZLe_def)
  also have "ZLe c p b q l < b ^ (Suc q)" using Suc.IH
    by (auto simp: ZLe_def Z_def Suc.prems(1))
  also have "b ^ (Suc q) * Z c p l (Suc q) \<le> b ^ (Suc q)" using Suc.prems(1)
    by (auto simp: Z_def)
  finally have "ZLe c p b (Suc q) l < 2 * b ^ (Suc q)"
    by auto
  also have "... < b ^ Suc (Suc q)"
    using Suc.prems(1) by auto
  finally show ?case by simp
qed

lemma SKe_bounded: "b > 2 \<Longrightarrow> SKe c p b q k < b ^ (Suc q)"
  proof (induction q)
  case 0
  then show ?case by (auto simp add: SKe_def S_bounded S_def)
next
  case (Suc q)
  have "SKe c p b (Suc q) k = b ^ (Suc q) * S c p k (Suc q) + SKe c p b q k"
    by (auto simp: SKe_def)
  also have "SKe c p b q k < b ^ (Suc q)" using Suc.IH
    by (auto simp: Suc.prems(1))
  also have "b ^ (Suc q) * S c p k (Suc q) \<le> b ^ (Suc q)" using Suc.prems(1)
    by (auto simp: S_def)
  finally have "SKe c p b (Suc q) k < 2 * b ^ (Suc q)"
    by auto
  also have "... < b ^ Suc (Suc q)"
    using Suc.prems(1) by auto
  finally show ?case by simp
qed

lemma mult_to_bitAND:
  assumes cells_bounded: "cells_bounded ic p c"
and "c > 1"
and "b = B c"

shows "(\<Sum>t=0..q. b^t * (Z ic p l t * S ic p k t))
       = ZLe ic p b q l && SKe ic p b q k"
proof (induction q arbitrary: ic p c l k)
  case 0
  then show ?case using S_bounded Z_bounded
    by (auto simp add: SKe_def ZLe_def bitAND_single_bit_mult_equiv)
next
  case (Suc q)

  have b4: "b > 2" using assms(2-3) apply (auto simp add: B_def)
    by (metis One_nat_def Suc_less_eq2 lessI numeral_2_eq_2 power_gt1)

  have ske: "SKe ic p b q k < b ^ (Suc q)" using SKe_bounded b4 by auto
  have zle: "ZLe ic p b q l < b ^ (Suc q)" using ZLe_bounded b4 by auto

  have ih: "(\<Sum>t = 0..q. b ^ t * (Z ic p l t * S ic p k t)) = ZLe ic p b q l && SKe ic p b q k"
    using Suc.IH by auto

  have "(\<Sum>t = 0..Suc q. b ^ t * (Z ic p l t * S ic p k t))
        = b ^(Suc q) * (Z ic p l (Suc q) * S ic p k (Suc q)) + (\<Sum>t = 0..q. b ^ t * (Z ic p l t * S ic p k t))"
    by (auto simp: sum.atLeast0_atMost_Suc add.commute)

  also have "... = b ^ (Suc q) * (Z ic p l (Suc q) * S ic p k (Suc q)) + (ZLe ic p b q l && SKe ic p b q k)"
    by (auto simp add: ih)

  also have "... = b ^ (Suc q) * (Z ic p l (Suc q) && S ic p k (Suc q)) + (ZLe ic p b q l && SKe ic p b q k)"
    using bitAND_single_bit_mult_equiv S_bounded Z_bounded by (auto)

  also have "... = (b ^(Suc q) * Z ic p l (Suc q) + ZLe ic p b q l) && (b ^ (Suc q) * S ic p k (Suc q) + SKe ic p b q k)"
    using bitAND_linear ske zle
    by (auto) (smt B_def assms(3) bitAND_linear mult.commute power_Suc power_mult)

  also have "... = (ZLe ic p b (Suc q) l && SKe ic p b (Suc q) k)"
    by (auto simp: ZLe_def SKe_def add.commute)

  finally show ?case by simp
qed

lemma sum_bt:
  fixes b q :: nat
  assumes "b > 2"
  shows "(\<Sum>t = 0..q. b^t) < b ^ (Suc q)"
    using assms
proof (induction q, auto)
  fix qb :: nat
  assume "sum ((^) b) {0..qb} < b * b ^ qb"
then have f1: "sum ((^) b) {0..qb} < b ^ Suc qb"
  by fastforce
have "b ^ Suc qb * 2 < b ^ Suc (Suc qb)"
  using assms by force
then have "2 * b ^ Suc qb < b ^ Suc (Suc qb)"
  by simp
then have "b ^ Suc qb + sum ((^) b) {0..qb} < b ^ Suc (Suc qb)"
  using f1 by linarith
then show "sum ((^) b) {0..qb} + b * b ^ qb < b * (b * b ^ qb)"
  by simp
qed

lemma mult_to_bitAND_state:
  assumes cells_bounded: "cells_bounded ic p c"
and c: "c > 1"
and b: "b = B c"

shows "(\<Sum>t=0..q. b^t * ((1 - Z ic p l t) * S ic p k t))
       = ((\<Sum>t = 0..q. b^t) - ZLe ic p b q l) && SKe ic p b q k"
proof (induction q arbitrary: ic p c l k)
  case 0
  show ?case using Z_def S_def ZLe_def SKe_def by auto
next
  case (Suc q)
  
  have b4: "b > 2" using assms(2-3) apply (auto simp add: B_def)
    by (metis One_nat_def Suc_less_eq2 lessI numeral_2_eq_2 power_gt1)

  have ske: "SKe ic p b q k < b ^ (Suc q)" using SKe_bounded b4 by auto
  have zle: "ZLe ic p b q l < b ^ (Suc q)" using ZLe_bounded b4 by auto
  define cst where "cst \<equiv> Suc q"
  define e where "e \<equiv> \<Sum>t = 0..Suc q. b^t"

  have "(\<Sum>t = 0..q. b^t) < b ^ (Suc q)"
    using sum_bt b4 by auto
  hence zle2: "(\<Sum>t = 0..q. b^t) - ZLe ic p b q l < b ^ (Suc q)"
    using less_imp_diff_less by blast

  have "(\<Sum>t = 0..x. b^t) - ZLe ic p b x l = (\<Sum>t=0..x. b^t - b^t * Z ic p l t)" for x
    unfolding ZLe_def
    using Z_bounded sum_subtractf_nat[where ?f = "(^) b" and ?g = "\<lambda>t. b ^ t * Z ic p l t"]
    by auto
  hence aux_sum: "(\<Sum>t = 0..x. b^t) - ZLe ic p b x l = (\<Sum>t=0..x. b^t * (1 - Z ic p l t))" for x
    using diff_Suc_1 diff_mult_distrib2 by auto

  have aux1: "b ^(Suc q) * (1 - Z ic p l (Suc q)) + (\<Sum>t=0..q. b^t * (1 - Z ic p l t))
                    = (\<Sum>t = 0..cst. b ^ t * (1 - Z ic p l t))"
    by (auto simp: sum.atLeast0_atMost_Suc cst_def)
  also have aux2: "... = (\<Sum>t = 0..cst. b ^ t) - ZLe ic p b cst l"
    unfolding e_def ZLe_def using aux_sum[of "cst"]
    by (auto simp: ZLe_def)
  finally have aux_add_sub:
      "(b ^(Suc q) * (1 - Z ic p l (Suc q)) + ((\<Sum>t = 0..q. b^t) - ZLe ic p b q l))
        = (e - ZLe ic p b (Suc q) l)"
    by (auto simp: cst_def e_def aux_sum)

  hence ih: "(\<Sum>t = 0..q. b ^ t * ((1 - Z ic p l t) * S ic p k t)) 
            = (\<Sum>t = 0..q. b^t) - ZLe ic p b q l && SKe ic p b q k" 
    using Suc[of "ic" "p" "l" "k"] by auto
  
  have "(\<Sum>t = 0..Suc q. b ^ t * ((1 - Z ic p l t) * S ic p k t))
      = (\<Sum>t = 0..    q. b ^ t * ((1 - Z ic p l t) * S ic p k t)) 
      + b^(Suc q) * ((1 - Z ic p l (Suc q)) * S ic p k (Suc q))"
    by (auto cong: sum.cong)
  
  also have "... = ((\<Sum>t = 0..q. b^t) - ZLe ic p b q l && SKe ic p b q k)
      + b^(Suc q) * ((1 - Z ic p l (Suc q)) * S ic p k (Suc q))" 
    using ih by auto

  also have "... = ((\<Sum>t = 0..q. b^t) - ZLe ic p b q l && SKe ic p b q k)
      +  b^(Suc q) * ((1 - Z ic p l (Suc q)) && S ic p k (Suc q))"
    using bitAND_single_bit_mult_equiv by (simp add: S_def)

  also have "... = (b ^(Suc q) * (1 - Z ic p l (Suc q)) + ((\<Sum>t = 0..q. b^t) - ZLe ic p b q l))
                   && (b ^ (Suc q) * S ic p k (Suc q) + SKe ic p b q k)"
    using bitAND_linear ske zle2 B_def b
    by (smt add_ac(2) mult_ac(2) bitAND_linear power.simps(2) power_mult power_mult_distrib)
  also have "... = (e - ZLe ic p b (Suc q) l && SKe ic p b (Suc q) k)"
    using SKe_def aux_add_sub by (auto simp: add.commute)

  finally show ?case by (auto simp: e_def)
qed

end
