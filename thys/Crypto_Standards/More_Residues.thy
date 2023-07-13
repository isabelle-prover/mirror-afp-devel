theory More_Residues 

imports 
  "HOL-Decision_Procs.Algebra_Aux"
  "HOL-Number_Theory.Residues"

begin

section \<open>Inverses mod p\<close>

text \<open>In SEC 1, we need to find the inverse of an integer modulo a prime modulus.  Using
Fermat's Little Theorem, it is easy to compute that inverse when it exists.  For a prime 
modulus p, we know that x has a multiplicative inverse exactly when p does not divide x.
Note that if we are ever going to run test vectors, we need a function that computes the
inverse, not just a statement that such an inverse exists.\<close>
definition inv_mod :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "inv_mod p x = (x^(p-2)) mod p"

lemma inv_mod_r: 
  assumes "\<not> p dvd x"  "prime p" 
  shows   "(x * inv_mod p x) mod p = 1"
proof -
  have 1: "1 mod p = 1"
    using assms(2) mod_less prime_gt_1_nat by blast 
  have 2: "(x * inv_mod p x) mod p = (x*(x^(p-2))) mod p"
    by (simp add: inv_mod_def mod_mult_right_eq)
  have 3: "x*(x^(p-2)) = x^(p-1)"
    by (metis assms(2) Suc_pred diff_diff_left numeral_2_eq_2 plus_1_eq_Suc power_add 
              power_one_right prime_gt_1_nat zero_less_diff) 
  have 4: "(x * inv_mod p x) mod p = x^(p-1) mod p"  using 2 3 by argo
  show ?thesis  by (metis 1 4 assms fermat_theorem cong_def)  
qed

lemma inv_mod_l:
  assumes "\<not> p dvd x"  "prime p" 
  shows   "(inv_mod p x)*x mod p = 1"
  by (metis inv_mod_r mult.commute assms)

lemma (in residues_prime) inv_mod_p_inv_in_ring:
  assumes "x \<in> carrier R"  "x \<noteq> 0" 
  shows   "inv\<^bsub>R\<^esub> x = inv_mod p x"
proof - 
  have 1: "x < p"                        using assms(1) res_carrier_eq by auto 
  have 2: "\<not> p dvd x"                    by (meson 1 assms(2) nat_dvd_not_less neq0_conv) 
  have 3: "(x * inv_mod p x) mod p = 1"  using 2 inv_mod_r by blast
  show ?thesis 
    by (metis (no_types, opaque_lifting) 3 assms(1) one_cong comm_inv_char inv_mod_def res_mult_eq
          mod_in_carrier mod_mod_trivial of_nat_1 of_nat_mod semiring_1_class.of_nat_mult)
qed

lemma (in residues) mod_in_carrier_nat: "(x::nat) mod m \<in> carrier R"
  using mod_in_carrier of_nat_mod by fast

lemma inv_mod_0: 
  assumes "prime p"  "2 < p" 
  shows   "(inv_mod p x = 0) = (x mod p = 0)"
  by (metis (no_types, opaque_lifting) One_nat_def assms(1,2) dvd_imp_mod_0 inv_mod_def inv_mod_r
        less_nat_zero_code mod_0 mod_mult_left_eq mult_0_right mult_zero_left nat.distinct(1)
        not0_implies_Suc power_Suc zero_less_diff)

lemma inv_mod_0': 
  assumes "prime p"  "2 < p"  "x < p"  
  shows   "(inv_mod p x = 0) = (x = 0)"
  using assms inv_mod_0 mod_less by algebra

lemma inv_mod_mod: "inv_mod p x = inv_mod p (x mod p)"
  by (metis Euclidean_Rings.euclidean_semiring_cancel_class.power_mod inv_mod_def)

lemma inv_mod_mult: "inv_mod p (x*y) = (inv_mod p x)*(inv_mod p y) mod p"
  by (metis inv_mod_def power_mult_distrib mod_mult_eq)

lemma (in residues_prime) div_eq_inv_mod:
  assumes "2 < p" 
  shows   "(x * (inv_mod p y)) mod p = (x mod p) \<oslash>\<^bsub>R\<^esub> (y mod p)" 
apply (cases "y mod p = 0")
apply (metis assms int_ops(1) inv_mod_0 m_div_def mod_mod_trivial mult_0_right p_prime zero_cong)
by (metis (no_types, lifting) inv_mod_mod inv_mod_p_inv_in_ring m_div_def mod_in_carrier_nat
      mod_mult_left_eq of_nat_eq_0_iff res_mult_eq semiring_1_class.of_nat_mult zero_cong zmod_int)

lemma (in residues_prime) div_eq_inv_mod':
  assumes "2 < p"  "x < p"  "y < p" 
  shows   "(x * (inv_mod p y)) mod p = x \<oslash>\<^bsub>R\<^esub> y"
  using assms div_eq_inv_mod mod_less by presburger 

section \<open>SOME Square Root\<close>

text \<open>In SEC 1, there are times when we need to find a square root of a quadratic residue modulo
a prime p.  It is not easy to write down such a square root for a general p.  There are cases
where it is easy (see below), but we cannot guarantee that the prime modulus p is in one of 
those easy cases.  So we need to use HOL's choice operator SOME.  There are some issues with
how QuadRes is defined in Residues.thy and how it relates to the types defined in 
Elliptic_Test.thy.  So here we define QuadRes' so that the types are better aligned.  We also
define two forms of the "get a square root" function, some_root_int and some_root_nat.  Then
we prove many lemmas about these definitions, with the various types.  We might be able to cut
out some of this later.\<close>

lemma int_nat_mod:
  fixes a :: int
  and   p :: nat 
  assumes "0 \<le> a" 
  shows "nat (a mod int p) = (nat a) mod p"
  by (simp add: assms nat_mod_distrib)

definition QuadRes' :: "nat \<Rightarrow> int \<Rightarrow> bool"
  where "QuadRes' p a = ( \<exists>(y::nat). (y < p) \<and> ([(int y)^2 = a] (mod p)) )"

lemma QuadRes'implQuadRes:
  assumes "QuadRes'      p  a"
  shows   "QuadRes  (int p) a"
  using QuadRes'_def QuadRes_def assms by blast

lemma QuadResImplQuadRes'1:
  assumes "QuadRes  (int p) a"  "1 < p" 
  shows   "QuadRes'      p  a"
proof - 
  obtain y where 1: "[y\<^sup>2 = a] (mod (int p))"  using assms(1) QuadRes_def by blast
  let ?y = "y mod p"
  have 2: "?y < p \<and> 0 \<le> ?y"                  using assms(2) by force
  have 3: "[?y\<^sup>2 = a] (mod (int p))"           by (metis 1 cong_def power_mod)
  let ?y' = "nat ?y"
  have 4: "int ?y' = ?y"                      using 2 by auto 
  show ?thesis   by (metis QuadRes'_def 3 4 2 nat_less_iff) 
qed

lemma QuadResImplQuadRes'2:
  assumes "QuadRes  (int p) a"  "prime p" 
  shows   "QuadRes'      p  a"
  using QuadResImplQuadRes'1 assms(1,2) prime_gt_1_nat by blast 

text \<open>When a is a quadratic reside mod p, then (by definition) it has a square root.  We can
use the choice operator SOME in order to get one of those roots.  If a is not 0 mod p, there
will be exactly two roots mod p: some b and p-b.\<close>

definition some_root_int :: "nat \<Rightarrow> int \<Rightarrow> int" where
  "some_root_int p a = (SOME (b::int). [b^2 = a] (mod int p))" 

definition some_root_nat :: "nat \<Rightarrow> int \<Rightarrow> nat" where
  "some_root_nat p a = (SOME (b::nat). (b < p) \<and> [b^2 = a] (mod int p))"

lemma QuadResHasIntRoot:
  assumes "QuadRes (int p) a"  "b = some_root_int p a"
  shows   "[b^2 = a] (mod p)"
  by (metis (lifting) QuadRes_def assms(1,2) someI_ex some_root_int_def)

lemma QuadResHasNatRoot:
  assumes "QuadRes (int p) a"  "b = some_root_nat p a"  "prime p"
  shows   "(b < p) \<and> [b^2 = a] (mod p)"
proof - 
  have "QuadRes' p a"  using assms(1,3) QuadResImplQuadRes'2 by meson
  then show ?thesis
    by (metis (no_types, lifting) QuadRes'_def assms(2) of_nat_power someI_ex some_root_nat_def) 
qed

lemma QuadRes'HasNatRoot: 
  assumes "QuadRes' p a"  "b = some_root_nat p a" 
  shows   "(b < p) \<and> [b^2 = a] (mod p)"
  by (metis (no_types, lifting) QuadRes'_def assms(1,2) someI_ex some_root_nat_def of_nat_power)

lemma QuadRes'HasIntRoot: 
  assumes "QuadRes' p a"  "b = some_root_int p a" 
  shows   "[b^2 = a] (mod p)"
  by (simp add: QuadRes'implQuadRes QuadResHasIntRoot assms(1,2))

lemma ZeroIsQuadRes: 
  assumes "1 < p"
  shows   "QuadRes' p 0"
  by (metis QuadRes'_def assms cong_def int_ops(1) less_trans power_zero_numeral zero_less_one)

lemma ZeroIsQuadRes': 
  assumes "prime p"
  shows   "QuadRes' p 0"
  using ZeroIsQuadRes assms prime_gt_1_nat by presburger

lemma ZeroHasOneRoot:
  assumes "prime (p::nat)"  "b < p"  "[b^2 = 0] (mod p)"
  shows   "b = 0"
  by (metis Groups.add_ac(2) One_nat_def add_diff_cancel_left' assms(1,2,3) diff_diff_left
          dvd_imp_mod_0  mod_0 mod_0_imp_dvd mod_less numerals(2) plus_1_eq_Suc power.simps(1)
          power_add power_one_right prime_dvd_mult_nat cong_def)

lemma ZeroSqrtMod:
  assumes "(y::int)^2 mod (p::nat) = 0"  "prime (p::int)"  "0 \<le> y"  "y < p"
  shows   "y = 0"
  by (metis assms(1,2,3,4) dvd_eq_mod_eq_0 mod_pos_pos_trivial prime_dvd_power_int)

lemma ZeroSqrtMod':
  assumes "b = some_root_nat p 0"  "prime (p::int)" 
  shows   "b = 0"
  by (metis QuadRes'HasNatRoot ZeroHasOneRoot ZeroIsQuadRes' assms(1,2) cong_int_iff 
            int_ops(1) prime_nat_int_transfer)

lemma QuadResNot0HasRootNot0: 
  assumes "QuadRes p a"  "b = some_root_nat p a"  "0 < a"  "a < p"  "1 < p"
  shows   "0 < b"
  by (smt (verit) QuadRes'HasNatRoot QuadResImplQuadRes'1 int_ops(1) neq0_conv Eps_cong 
      Euclidean_Rings.pos_mod_sign add.commute arith_special(3) assms(1,2,3,4,5) cong_def
      mod_mod_trivial mod_pos_pos_trivial mod_self plus_1_eq_Suc power_mod power_zero_numeral)

lemma QuadRes'Not0HasRootNot0: 
  assumes "QuadRes' p a"  "b = some_root_nat p a"  "0 < a"  "a < p"  "1 < p"
  shows   "0 < b"
  using QuadRes'implQuadRes QuadResNot0HasRootNot0 assms(1,2,3,4,5) by blast

lemma QuadResHasTwoIntRoots:
  assumes "QuadRes' p a"  "b = some_root_int p a"
  shows "[(p - b)^2 = a] (mod p)"
  by (metis (mono_tags, opaque_lifting) QuadRes'HasIntRoot assms(1,2) cong_def cong_pow 
            minus_mod_self2 power2_commute)

lemma QuadRes'HasTwoNatRoots:
  assumes "QuadRes' p a"  "b = some_root_nat p a"
  shows "[(p - b)^2 = a] (mod p)"
proof - 
  have 1: "[b^2 = a] (mod p)"     using QuadRes'HasNatRoot assms(1,2) by blast 
  have 2: "b < p"                 using QuadRes'HasNatRoot assms(1,2) by blast 
  let ?b = "int b"
  have 3: "nat ?b = b"            by simp
  have 4: "?b^2 mod p = a mod p"  using 1 cong_def by auto
  have 5: "(p-?b)^2 mod p = ?b^2 mod p"
    by (metis (no_types) minus_mod_self2 power2_commute power_mod) 
  show ?thesis 
    by (smt (verit, best) 1 2 5 cong_def int_ops(6) less_imp_of_nat_less of_nat_power) 
qed

lemma QuadResHasTwoRoots':
  assumes "QuadRes' p a"  "b = some_root_nat p a"  "0 < a"  "a < p"  "1 < p"
          "S = {x. 0 \<le> x \<and> x < p \<and> [x^2 = a] (mod p)}"
    shows "{b, (p-b)} \<subseteq> S" 
proof - 
  have 1: "b \<in> S"                   using QuadRes'HasNatRoot assms(1,2,6) by blast 
  have 2: "0 < b"                   using QuadRes'Not0HasRootNot0 assms(1,2,3,4,5) by blast
  have 3: "p - b < p"               using 2 assms(5) by simp
  have 4: "b < p"                   using 1 assms(6) by fast
  have 5: "0 \<le> p-b"                 using 4 by fast
  have 6: "[(p - b)^2 = a] (mod p)" using QuadRes'HasTwoNatRoots assms(1,2) by blast
  have 7: "p - b \<in> S"               using 3 5 6 assms(6) by blast
  show ?thesis                      using 1 7 by blast
qed

lemma roots_mod_prime_bound':
  fixes a :: int
  and   p n :: nat 
  assumes "prime p" "n > 0" "0 \<le> a" 
  defines "A \<equiv> {x\<in>{..<p}. [x ^ n = a] (mod p)}"
  shows   "card A \<le> n"
proof - 
  let ?a = "nat a"
  let ?A = "{x\<in>{..<p}. [x ^ n = ?a] (mod p)}"
  have 1: "finite ?A"    by simp
  have 2: "card ?A \<le> n"  using roots_mod_prime_bound assms(1,2) by blast
  have 3: "card ?A = card A"
    by (smt (verit) A_def Collect_cong assms(3) cong_int_iff int_nat_eq of_nat_power) 
  show ?thesis           using 2 3 by argo
qed

lemma QuadResHasExactlyTwoRoots:
  assumes "QuadRes' p a"  "b = some_root_nat p a"  "0 < a"  "a < p"  "prime p"
          "S = {x\<in>{..<p}. [x^2 = a] (mod p)}" "2 < p" 
    shows "{b, (p-b)} = S" 
proof - 
  have 0: "0 \<le> a"           using assms(3) by simp
  have 1: "0 < (2::nat)"    by simp
  have 2: "card S \<le> 2"      using 0 1 assms(5,6) roots_mod_prime_bound' by simp
  have 3: "1 < p"           using assms(7) by auto
  have 4: "{b, (p-b)} \<subseteq> S"  using QuadResHasTwoRoots' assms(1,2,3,4,6) 3 by blast
  have 5: "odd p"           using assms(5,7) prime_odd_nat by auto
  have 6: "b \<noteq> (p-b)" proof (cases "even b")
    case True
    then have "odd (p-b)"
      by (metis "5" QuadRes'HasNatRoot assms(1) assms(2) dvd_diffD less_imp_le_nat)
    then show ?thesis       using True by metis
  next
    case False
    then have "even (p-b)"             by (simp add: 5)
    then show ?thesis                  using False by metis
  qed
  have 7: "card {b, (p-b)} = 2"        using 6 by simp
  have 8: "S \<subseteq> {x. 0 \<le> x \<and> x < p}"    using assms(6) by fast
  have 9: "finite {x. 0 \<le> x \<and> x < p}" by fast
  have 10: "finite S"                  using 8 9 finite_subset by blast
  show ?thesis                         by (metis 2 4 7 10 card_seteq) 
qed

lemma QuadResHasExactlyTwoRoots1:
  assumes "QuadRes' p a"  "b = some_root_nat p a"  "0 < a"  "a < p"  "prime p"  "2 < p"
          "y^2 mod p = a" "0 \<le> y" "y < p"
    shows "y = b \<or> y = p - b" 
proof - 
  have 1: "a mod p = a"       using assms(3,4) by force
  let ?S = "{x\<in>{..<p}. [x^2 = a] (mod p)}"
  have 2: "[y^2 = a] (mod p)" by (metis assms(7) 1 cong_def of_nat_mod) 
  have 3: "y \<in> ?S"            using 2 assms(8,9) by simp
  have 4: "{b, (p-b)} = ?S"   using QuadResHasExactlyTwoRoots assms(1,2,3,4,5,6) by auto
  show ?thesis                using 3 4 by blast
qed

lemma QuadResHasExactlyTwoRoots2:
    fixes y :: int 
  assumes "QuadRes' p a"  "b = some_root_nat p a"  "0 < a"  "a < p"  "prime p"  "2 < p" 
          "y^2 mod p = a" "0 \<le> y" "y < p"
        shows "y = b \<or> y = p - b" 
proof - 
  let ?y = "nat y"
  have "?y = b \<or> ?y = p - b"
    by (smt (verit) QuadResHasExactlyTwoRoots1 assms int_nat_eq nat_int of_nat_mod of_nat_power
            zero_le zless_nat_conj) 
  then show ?thesis by (metis assms(8) int_nat_eq) 
qed

section \<open>Compute Square Root\<close>

text \<open>We want to compute the square root of a modulo an odd prime p, when a is a quadratic
residue.  We need to have some concrete formula if we have any hope of running test vectors
for SEC 1 when point compression is used to store EC points.  This is not complete.  For the
general case, we need to have a quadratic non-residue in order to write down the square root.\<close>

definition EulersCriterion :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  "EulersCriterion p a = 
   ( let n = (p-1) div 2;
         x = (a ^ n) mod p 
     in
         if x = 1 then True
                  else False
   )" 

lemma QuadResImpliesEulersCrit:
  assumes "prime p"  "odd p"  "a < p"  "0 < a"  "QuadRes' p a"
  shows   "EulersCriterion p a" 
proof - 
  obtain r where r: "(r < p) \<and> [r^2 = a] (mod p)" 
    by (meson QuadRes'HasNatRoot assms(5) cong_int_iff) 
  have 0: "0 < r" 
    by (metis assms(3,4) r cong_less_modulus_unique_nat gr0I zero_power2) 
  have 1: "2 dvd (p-1)"                using assms(2) by simp
  let ?k = "(p-1) div 2"
  have 2: "[a^?k = (r^2)^?k] (mod p)"  using cong_pow cong_sym r by blast
  have 3: "[a^?k = r^(2*?k)] (mod p)"  using 2 by (simp add: power_mult) 
  have 4: "[a^?k = r^(p-1)] (mod p)"   using 3 1 by force
  have 5: "[a^?k = 1] (mod p)"  
    by (metis assms(1) 4 0 r fermat_theorem nat_dvd_not_less cong_def) 
  show ?thesis  by (metis EulersCriterion_def 5 assms(1) cong_def mod_less prime_gt_1_nat) 
qed

definition computeRoot3mod4 :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "computeRoot3mod4 p a = ( let k = p div 4 in a^(k+1) mod p )" 

definition computeRoot5mod8 :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "computeRoot5mod8 p a = 
   ( let k = p div 8; 
         t = a^(2*k + 1) mod p;
         b = a^(  k + 1) mod p;
         c = 2^(2*k + 1) mod p
     in
         if t = 1 then b 
                  else b*c mod p
   )" 

definition computeRoot :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "computeRoot p a =
   ( let a' = a mod p in
     ( if p mod 2 = 0 then a' else
       if p mod 4 = 3 then (computeRoot3mod4 p a') else
       if p mod 8 = 5 then (computeRoot5mod8 p a') else
       if p mod 8 = 1 then (0)
       else 0
     )
   )"



end

