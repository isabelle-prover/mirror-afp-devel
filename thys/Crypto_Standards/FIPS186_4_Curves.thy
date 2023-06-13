theory FIPS186_4_Curves
  imports "Efficient_SEC1"

begin

text \<open>In FIPS 186-4, NIST defines several recommended curves for government use.  In this theory,
we define the NIST recommended curves over prime fields, that is, all the curves that are labelled
with "P-"  Note that all these curves have cofactor h=1 and coefficient a = p-3.

https://csrc.nist.gov/Projects/Elliptic-Curve-Cryptography
https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.186-4.pdf

Below you will find the parameters given by NIST for the "P-" curves.  Then we prove that these 
parameters meet the definition of a valid elliptic curve.  Of course, to be a valid elliptic
curve with h=1, we must know that p and n are prime and also that the number of (integer) points
on the curve is n (=n*h).  These three things we do not attempt to prove; instead, we take them
as given as axioms.  All other facts about valid elliptic curves can be and are checked below.

Note that FIPS 186-4 is being replaced by FIPS 186-5.  The curve parameters listed here appear
unchanged in the new version of the standard.\<close>

section \<open>P-192\<close>

subsection \<open>Parameters\<close>

definition P192_p :: nat where 
  "P192_p = 6277101735386680763835789423207666416083908700390324961279"

definition P192_n :: nat where 
  "P192_n = 6277101735386680763835789423176059013767194773182842284081"

definition P192_SEED :: nat where 
  "P192_SEED = 0x3045ae6fc8422f64ed579528d38120eae12196d5"

definition P192_c :: nat where 
  "P192_c = 0x3099d2bbbfcb2538542dcd5fb078b6ef5f3d6fe2c745de65"

definition P192_a :: nat where 
  "P192_a = P192_p - 3"

definition P192_b :: nat where 
  "P192_b = 0x64210519e59c80e70fa7e9ab72243049feb8deecc146b9b1"

definition P192_Gx :: nat where 
  "P192_Gx = 0x188da80eb03090f67cbf20eb43a18800f4ff0afd82ff1012"

definition P192_Gy :: nat where 
  "P192_Gy = 0x07192b95ffc8da78631011ed6b24cdd573f977a11e794811"

definition P192_G :: "int point" where
  "P192_G = Point (int P192_Gx) (int P192_Gy)"

definition P192_prG :: "int ppoint" where
  "P192_prG = (int P192_Gx, int P192_Gy, 1)"

definition P192_h :: nat where
  "P192_h = 1"

definition P192_t :: nat where
  "P192_t = 80"

subsection \<open>Parameter Checks\<close>

text\<open>We can't easily check that n and p are prime, but there are many conditions on the parameters
of an elliptic curve to be considered a valid curve.  We verify now the things that we can check.\<close>

text\<open>We are just going to assume that p is prime.\<close>
axiomatization where P192_p_prime: "prime P192_p"

text\<open>But we can easily see that p is an odd prime.\<close>
lemma P192_p_gr2: "2 < P192_p" by eval

text\<open>We are just going to assume that n is prime.\<close>
axiomatization where P192_n_prime: "prime P192_n"

text \<open>Check (\<forall>B\<in>{1..99}. (p^B mod n \<noteq> 1)).\<close>
lemma P192_checkPmodN: "\<forall>i\<in>{1..99}. (P192_p^i mod P192_n \<noteq> 1)"
proof - 
  have 1: "list_all (%i. P192_p^i mod P192_n \<noteq> 1) [1..<100]" by eval
  have 2: "\<forall>i \<in> set [1..<100]. (P192_p^i mod P192_n \<noteq> 1)" 
    by (metis (mono_tags, lifting) 1 Ball_set)
  have 3: "set [1..<100] = {1::nat..99}" by fastforce
  show ?thesis using 2 3 by blast
qed

text\<open>Check (a \<in> carrier R) \<and> (b \<in> carrier R) \<and> (nonsingular a b)\<close>
lemma P192_checkA: "P192_a < P192_p" by eval

lemma P192_checkB: "P192_b < P192_p" by eval

lemma P192_checkNonsingular: "(4*P192_a^3 + 27*P192_b^2) mod P192_p \<noteq> 0"
  by eval

text \<open>Check (on_curve a b G)  \<and> (G \<noteq> Infinity)  \<and> (point_mult a n G = Infinity)\<close>
lemma P192_checkGnotInf: "P192_G \<noteq> Infinity" 
  by eval

lemma P192_checkGoncurve: "mon_curve P192_p P192_a P192_b P192_G" 
  by eval

lemma P192_checkGord:
  "mmake_affine P192_p (fast_ppoint_mult P192_p P192_a P192_n P192_prG) = Infinity"
  by eval

text \<open>Check the cofactor h and the security level t.\<close>
lemma P192_checkT: "P192_t \<in> {80, 112, 128, 192, 256}"
  by eval

lemma P192_checkHT: "P192_h \<le> 2^(P192_t div 8)"
  by eval

lemma P192_checkNHnotP: "P192_n * P192_h \<noteq> P192_p" 
  by eval

lemma P192_checkHnot0: "0 < P192_h" 
  by eval

text \<open>Check \<open>h = \<lfloor>((sqrt p + 1)^2) div n\<rfloor>\<close>.  This is slightly more involved than the above checks.\<close>
lemma P192_checkH1: "(P192_h*P192_n - P192_p - 1)^2 \<le> 4*P192_p"     by eval

lemma P192_checkH2: "4*P192_p < ((P192_h+1)*P192_n - P192_p - 1)^2"  by eval

lemma P192_checkH: "P192_h = \<lfloor>((sqrt P192_p + 1)^2) div P192_n\<rfloor>"
proof - 
  have p1: "((sqrt P192_p) + 1)^2 = P192_p + 2*(sqrt P192_p) + 1"
    by (simp add: power2_sum)
  have n1: "0 < P192_n" by eval
  have l1: "P192_h*P192_n - P192_p - 1 \<le> 2*(sqrt P192_p)"
    by (metis (mono_tags, opaque_lifting) P192_checkH1 real_le_rsqrt of_nat_le_iff of_nat_mult
        of_nat_numeral of_nat_power real_sqrt_four real_sqrt_mult) 
  have l2: "P192_h*P192_n \<le> P192_p + 2*(sqrt P192_p) + 1"
    using l1 by linarith
  have l3: "P192_h*P192_n \<le> ((sqrt P192_p) + 1)^2"
    using l2 p1 by presburger
  have l4: "P192_h \<le> (((sqrt P192_p) + 1)^2) div P192_n"
    using l3 pos_le_divide_eq n1 by force 
  have g1: "2*(sqrt P192_p) < (P192_h+1)*P192_n - P192_p - 1"
    by (metis (mono_tags, opaque_lifting) P192_checkH2 real_less_lsqrt of_nat_mult of_nat_less_iff
        of_nat_numeral of_nat_power real_sqrt_four real_sqrt_mult of_nat_0_le_iff) 
  have g2: "P192_p + 2*(sqrt P192_p) + 1 < (P192_h+1)*P192_n"
    by (smt (verit, ccfv_SIG) g1 P192_p_gr2 add_diff_inverse_nat cring_class.of_nat_add of_nat_1
        less_diff_conv less_imp_of_nat_less nat_1_add_1 of_nat_less_imp_less real_sqrt_ge_one)
  have g3: "((sqrt P192_p) + 1)^2 < (P192_h+1)*P192_n"
    using g2 p1 by presburger
  have g4: "(((sqrt P192_p) + 1)^2) div P192_n < (P192_h+1)"
    by (metis g3 n1 pos_divide_less_eq of_nat_0_less_iff of_nat_mult) 
  show ?thesis using l4 g4 by linarith
qed

subsection \<open>Interpretations\<close>

text \<open>Because p is (assumed to be) prime and greater than 2, we can interpret the 
residues_prime_gr2 locale.\<close>

lemma P192_residues_prime_gt2: "residues_prime_gt2 P192_p"
  using P192_p_prime P192_p_gr2 residues_prime_gt2_def residues_prime.intro 
        residues_prime_gt2_axioms.intro by blast

definition P192_R :: "int ring" where
  "P192_R = residue_ring (int P192_p)"

global_interpretation PG2_P192: residues_prime_gt2 P192_p P192_R
  defines P192_nonsingular = "PG2_P192.nonsingular"
  and     P192_on_curve    = "PG2_P192.on_curve"
  and     P192_add         = "PG2_P192.add"
  and     P192_opp         = "PG2_P192.opp"
  and     P192_is_tangent  = "PG2_P192.is_tangent"
  and     P192_is_generic  = "PG2_P192.is_generic"
  and     P192_point_mult  = "PG2_P192.point_mult"
  and     P192_pdouble     = "PG2_P192.pdouble"
  and     P192_padd        = "PG2_P192.padd"
  and     P192_make_affine = "PG2_P192.make_affine"
  and     P192_in_carrierp = "PG2_P192.in_carrierp"
  and     P192_on_curvep   = "PG2_P192.on_curvep"
  and     P192_ppoint_mult = "PG2_P192.ppoint_mult"
  and     P192_proj_eq     = "PG2_P192.proj_eq"
  and     P192_point_madd  = "PG2_P192.point_madd"
  and     P192_point_mmult = "PG2_P192.point_mmult"
  and     P192_point_to_octets_nocomp = "PG2_P192.point_to_octets_nocomp"
  and     P192_point_to_octets_comp   = "PG2_P192.point_to_octets_comp"
  and     P192_point_to_octets        = "PG2_P192.point_to_octets"
  and     P192_FlipY                  = "PG2_P192.FlipY"
  and     P192_FlipYhd                = "PG2_P192.FlipYhd"
  and     P192_octets_to_point_nocomp_validInput = "PG2_P192.octets_to_point_nocomp_validInput"
  and     P192_octets_to_point_nocomp            = "PG2_P192.octets_to_point_nocomp"
  and     P192_octets_to_point_comp_validInput   = "PG2_P192.octets_to_point_comp_validInput"
  and     P192_octets_to_point_comp              = "PG2_P192.octets_to_point_comp"
  and     P192_octets_to_point_validInput        = "PG2_P192.octets_to_point_validInput"
  and     P192_octets_to_point                   = "PG2_P192.octets_to_point"
  and     P192_twiceSecurityLevel                = "PG2_P192.twiceSecurityLevel"
  and     P192_ECdomainParametersValid           = "PG2_P192.ECdomainParametersValid"
  and     P192_ECdomainParametersValid'          = "PG2_P192.ECdomainParametersValid'"
  and     P192_twiceSecurityLevelInv             = "PG2_P192.twiceSecurityLevelInv"
  using P192_residues_prime_gt2 apply fast
  by (simp add: P192_R_def) 

text \<open>With a definition above, we can show one more thing about the curve parameters, namely\<close>
lemma P192_checkTP: "P192_twiceSecurityLevel P192_t = (bit_length P192_p)"
  by eval

lemma P192_checkTP': "P192_twiceSecurityLevel P192_t = \<lceil>log 2 P192_p\<rceil>"
  using P192_checkTP P192_p_prime P192_p_gr2 bitLenLog2Prime by presburger 

text \<open>We can restate some facts from above using PG2_P192 definitions\<close>
lemma P192_checkAB: 
  "(P192_a \<in> carrier P192_R) \<and> (P192_b \<in> carrier P192_R) \<and> (P192_nonsingular P192_a P192_b)"
proof - 
  have 1: "P192_a \<in> carrier P192_R" by (simp add: P192_checkA PG2_P192.inCarrier) 
  have 2: "P192_b \<in> carrier P192_R" by (simp add: P192_checkB PG2_P192.inCarrier) 
  have 3: "P192_nonsingular P192_a P192_b" 
    by (metis 1 2 P192_checkNonsingular P192_R_def P192_nonsingular_def P192_residues_prime_gt2 
        ell_prime_field.nonsingular_in_bf ell_prime_field_axioms.intro ell_prime_field_def) 
  show ?thesis using 1 2 3 by satx
qed

lemma P192_checkGoncurve': "P192_on_curve P192_a P192_b P192_G" 
  by eval

lemma P192_checkGord'h: 
  "efficient_funpow (P192_point_madd P192_a) Infinity P192_G P192_n = Infinity" 
  by eval

lemma P192_checkGord': "P192_point_mult P192_a P192_n P192_G = Infinity"
  using P192_checkAB P192_checkGoncurve' P192_checkGord'h PG2_P192.point_add_eq
        PG2_P192.point_mult_efficient[of P192_a P192_b P192_G P192_n]
  by presburger

text \<open>The last thing we are going to assume is that n*h is the number of points on the curve.\<close>
axiomatization where P192_numCurvePoints: "card {P. P192_on_curve P192_a P192_b P} = P192_n*P192_h"

text\<open>Then with the 3 things we assumed and all the things we checked, we know that these 
parameters describe a valid elliptic curve.  Then we can interpret the SEC1 locale with P192.\<close>

lemma P192valid: "P192_ECdomainParametersValid P192_a P192_b P192_G P192_n P192_h P192_t"
  using PG2_P192.ECdomainParametersValid_def P192_checkNHnotP P192_checkHnot0 P192_checkH
        P192_checkAB P192_n_prime P192_checkTP' P192_checkPmodN P192_checkT P192_checkHT 
        P192_checkGoncurve' P192_checkGord' P192_checkGnotInf P192_numCurvePoints by presburger

global_interpretation SEC1_P192: SEC1 P192_p P192_R P192_a P192_b P192_n P192_h P192_t P192_G
  defines SEC1_P192_Rn                      = "SEC1_P192.Rn"
  and     SEC1_P192_ECkeyGen                = "SEC1_P192.ECkeyGen"
  and     SEC1_P192_ECkeyPairValid          = "SEC1_P192.ECkeyPairValid"
  and     SEC1_P192_ECprivateKeyValid       = "SEC1_P192.ECprivateKeyValid"
  and     SEC1_P192_ECpublicKeyValid        = "SEC1_P192.ECpublicKeyValid"
  and     SEC1_P192_ECpublicKeyPartialValid = "SEC1_P192.ECpublicKeyPartialValid"
  and     SEC1_P192_ECDHprim                = "SEC1_P192.ECDHprim"
  and     SEC1_P192_MQVcomputeQbar          = "SEC1_P192.MQVcomputeQbar"
  and     SEC1_P192_MQVcompute_s            = "SEC1_P192.MQVcompute_s"
  and     SEC1_P192_MQVcomputeP             = "SEC1_P192.MQVcomputeP"
  and     SEC1_P192_ECMQVprim_validInput    = "SEC1_P192.ECMQVprim_validInput"
  and     SEC1_P192_ECMQVprim               = "SEC1_P192.ECMQVprim"
  and     SEC1_P192_ECDSA_compute_e         = "SEC1_P192.ECDSA_compute_e"
  and     SEC1_P192_ECDSA_Sign_e            = "SEC1_P192.ECDSA_Sign_e"
  and     SEC1_P192_ECDSA_Verify_e          = "SEC1_P192.ECDSA_Verify_e"
  and     SEC1_P192_ECDSA_Verify_e_Alt      = "SEC1_P192.ECDSA_Verify_e_Alt"
  and     SEC1_P192_ECDSA_Verify_Alt        = "SEC1_P192.ECDSA_Verify_Alt"
  using P192valid SEC1.intro SEC1_axioms_def P192_residues_prime_gt2 
        P192_ECdomainParametersValid_def apply simp 
  using P192_R_def by simp 

abbreviation "SEC1_P192_on_curve'        \<equiv> P192_on_curve P192_a P192_b"
abbreviation "SEC1_P192_mon_curve'       \<equiv> mon_curve P192_p P192_a P192_b"
abbreviation "SEC1_P192_point_mult'      \<equiv> P192_point_mult P192_a"
abbreviation "SEC1_P192_point_mmult'     \<equiv> P192_point_mmult P192_a"
abbreviation "SEC1_P192_add'             \<equiv> P192_add P192_a"
abbreviation "SEC1_P192_madd'            \<equiv> P192_point_madd P192_a"
abbreviation "SEC1_P192_octets_to_point' \<equiv> P192_octets_to_point P192_a P192_b"
abbreviation "SEC1_P192_inv_mod_n        \<equiv> inv_mod P192_n"
abbreviation "SEC1_P192_ECDSA_Sign Hash d\<^sub>U M k P \<equiv> 
                SEC1_P192_ECDSA_Sign_e d\<^sub>U (SEC1_P192_ECDSA_compute_e Hash M) k P"
abbreviation "SEC1_P192_ECDSA_Sign_e' d\<^sub>U e k     \<equiv> 
                SEC1_P192_ECDSA_Sign_e d\<^sub>U e k (SEC1_P192_ECkeyGen k)"
abbreviation "SEC1_P192_ECDSA_Sign' Hash d\<^sub>U M k  \<equiv> 
                SEC1_P192_ECDSA_Sign Hash d\<^sub>U M k (SEC1_P192_ECkeyGen k)"
abbreviation "SEC1_P192_ECDSA_Verify Hash Q\<^sub>U M S \<equiv> 
                SEC1_P192_ECDSA_Verify_e Q\<^sub>U (SEC1_P192_ECDSA_compute_e Hash M) S"

section \<open>P-224\<close>

subsection \<open>Parameters\<close>

definition P224_p :: nat where 
  "P224_p = 26959946667150639794667015087019630673557916260026308143510066298881"

definition P224_n :: nat where 
  "P224_n = 26959946667150639794667015087019625940457807714424391721682722368061"

definition P224_SEED :: nat where 
  "P224_SEED = 0xbd71344799d5c7fcdc45b59fa3b9ab8f6a948bc5"

definition P224_c :: nat where 
  "P224_c = 0x5b056c7e11dd68f40469ee7f3c7a7d74f7d121116506d031218291fb"

definition P224_a :: nat where 
  "P224_a = P224_p - 3"

definition P224_b :: nat where 
  "P224_b = 0xb4050a850c04b3abf54132565044b0b7d7bfd8ba270b39432355ffb4"

definition P224_Gx :: nat where 
  "P224_Gx = 0xb70e0cbd6bb4bf7f321390b94a03c1d356c21122343280d6115c1d21"

definition P224_Gy :: nat where 
  "P224_Gy = 0xbd376388b5f723fb4c22dfe6cd4375a05a07476444d5819985007e34"

definition P224_G :: "int point" where
  "P224_G = Point (int P224_Gx) (int P224_Gy)"

definition P224_prG :: "int ppoint" where
  "P224_prG = (int P224_Gx, int P224_Gy, 1)"

definition P224_h :: nat where
  "P224_h = 1"

definition P224_t :: nat where
  "P224_t = 112"


subsection \<open>Parameter Checks\<close>

text\<open>We can't easily check that n and p are prime, but there are many conditions on the parameters
of an elliptic curve to be considered a valid curve.  We check now the things that we can check.\<close>

text\<open>We are just going to assume that p is prime.\<close>
axiomatization where P224_p_prime: "prime P224_p"

text\<open>But we can easily see that p is an odd prime.\<close>
lemma P224_p_gr2: "2 < P224_p" by eval

text\<open>We are just going to assume that n is prime.\<close>
axiomatization where P224_n_prime: "prime P224_n"

text \<open>Check (\<forall>B\<in>{1..99}. (p^B mod n \<noteq> 1)).\<close>
lemma P224_checkPmodN: "\<forall>i\<in>{1..99}. (P224_p^i mod P224_n \<noteq> 1)"
proof - 
  have 1: "list_all (%i. P224_p^i mod P224_n \<noteq> 1) [1..<100]" by eval
  have 2: "\<forall>i \<in> set [1..<100]. (P224_p^i mod P224_n \<noteq> 1)" 
    by (metis (mono_tags, lifting) 1 Ball_set)
  have 3: "set [1..<100] = {1::nat..99}" by fastforce
  show ?thesis using 2 3 by blast
qed

text\<open>Check (a \<in> carrier R) \<and> (b \<in> carrier R) \<and> (nonsingular a b)\<close>
lemma P224_checkA: "P224_a < P224_p" by eval

lemma P224_checkB: "P224_b < P224_p" by eval

lemma P224_checkNonsingular: "(4*P224_a^3 + 27*P224_b^2) mod P224_p \<noteq> 0"
  by eval

text \<open>Check (on_curve a b G)  \<and> (G \<noteq> Infinity)  \<and> (point_mult a n G = Infinity)\<close>
lemma P224_checkGnotInf: "P224_G \<noteq> Infinity" 
  by eval

lemma P224_checkGoncurve: "mon_curve P224_p P224_a P224_b P224_G" 
  by eval

lemma P224_checkGord:
  "mmake_affine P224_p (fast_ppoint_mult P224_p P224_a P224_n P224_prG) = Infinity"
  by eval

text \<open>Check the cofactor h and the security level t.\<close>
lemma P224_checkT: "P224_t \<in> {80, 112, 128, 192, 256}"
  by eval

lemma P224_checkHT: "P224_h \<le> 2^(P224_t div 8)"
  by eval

lemma P224_checkNHnotP: "P224_n * P224_h \<noteq> P224_p" 
  by eval

lemma P224_checkHnot0: "0 < P224_h" 
  by eval

text \<open>Check \<open>h = \<lfloor>((sqrt p + 1)^2) div n\<rfloor>\<close>.  This is slightly more involved than the above checks.\<close>
lemma P224_checkH1: "(P224_h*P224_n - P224_p - 1)^2 \<le> 4*P224_p"     by eval

lemma P224_checkH2: "4*P224_p < ((P224_h+1)*P224_n - P224_p - 1)^2"  by eval

lemma P224_checkH: "P224_h = \<lfloor>((sqrt P224_p + 1)^2) div P224_n\<rfloor>"
proof - 
  have p1: "((sqrt P224_p) + 1)^2 = P224_p + 2*(sqrt P224_p) + 1"
    by (simp add: power2_sum)
  have n1: "0 < P224_n" by eval
  have l1: "P224_h*P224_n - P224_p - 1 \<le> 2*(sqrt P224_p)"
    by (metis (mono_tags, opaque_lifting) P224_checkH1 real_le_rsqrt of_nat_le_iff of_nat_mult 
        of_nat_numeral of_nat_power real_sqrt_four real_sqrt_mult) 
  have l2: "P224_h*P224_n \<le> P224_p + 2*(sqrt P224_p) + 1"
    using l1 by linarith
  have l3: "P224_h*P224_n \<le> ((sqrt P224_p) + 1)^2"
    using l2 p1 by presburger
  have l4: "P224_h \<le> (((sqrt P224_p) + 1)^2) div P224_n"
    using l3 pos_le_divide_eq n1 by force 
  have g1: "2*(sqrt P224_p) < (P224_h+1)*P224_n - P224_p - 1"
    by (metis (mono_tags, opaque_lifting) P224_checkH2 real_less_lsqrt of_nat_mult of_nat_less_iff
        of_nat_numeral of_nat_power real_sqrt_four real_sqrt_mult of_nat_0_le_iff) 
  have g2: "P224_p + 2*(sqrt P224_p) + 1 < (P224_h+1)*P224_n"
    by (smt (verit, ccfv_SIG) g1 P224_p_gr2 add_diff_inverse_nat cring_class.of_nat_add of_nat_1
        less_diff_conv less_imp_of_nat_less nat_1_add_1 of_nat_less_imp_less real_sqrt_ge_one)
  have g3: "((sqrt P224_p) + 1)^2 < (P224_h+1)*P224_n"
    using g2 p1 by presburger
  have g4: "(((sqrt P224_p) + 1)^2) div P224_n < (P224_h+1)"
    by (metis g3 n1 pos_divide_less_eq of_nat_0_less_iff of_nat_mult) 
  show ?thesis using l4 g4 by linarith
qed

subsection \<open>Interpretations\<close>

text \<open>Because p is (assumed to be) prime and greater than 2, we can interpret the 
residues_prime_gr2 locale.\<close>

lemma P224_residues_prime_gt2: "residues_prime_gt2 P224_p"
  using P224_p_prime P224_p_gr2 residues_prime_gt2_def residues_prime.intro 
        residues_prime_gt2_axioms.intro by blast

definition P224_R :: "int ring" where
  "P224_R = residue_ring (int P224_p)"

global_interpretation PG2_P224: residues_prime_gt2 P224_p P224_R
  defines P224_nonsingular = "PG2_P224.nonsingular"
  and     P224_on_curve    = "PG2_P224.on_curve"
  and     P224_add         = "PG2_P224.add"
  and     P224_opp         = "PG2_P224.opp"
  and     P224_is_tangent  = "PG2_P224.is_tangent"
  and     P224_is_generic  = "PG2_P224.is_generic"
  and     P224_point_mult  = "PG2_P224.point_mult"
  and     P224_pdouble     = "PG2_P224.pdouble"
  and     P224_padd        = "PG2_P224.padd"
  and     P224_make_affine = "PG2_P224.make_affine"
  and     P224_in_carrierp = "PG2_P224.in_carrierp"
  and     P224_on_curvep   = "PG2_P224.on_curvep"
  and     P224_ppoint_mult = "PG2_P224.ppoint_mult"
  and     P224_proj_eq     = "PG2_P224.proj_eq"
  and     P224_point_madd  = "PG2_P224.point_madd"
  and     P224_point_mmult = "PG2_P224.point_mmult"
  and     P224_point_to_octets_nocomp = "PG2_P224.point_to_octets_nocomp"
  and     P224_point_to_octets_comp   = "PG2_P224.point_to_octets_comp"
  and     P224_point_to_octets        = "PG2_P224.point_to_octets"
  and     P224_FlipY                  = "PG2_P224.FlipY"
  and     P224_FlipYhd                = "PG2_P224.FlipYhd"
  and     P224_octets_to_point_nocomp_validInput = "PG2_P224.octets_to_point_nocomp_validInput"
  and     P224_octets_to_point_nocomp            = "PG2_P224.octets_to_point_nocomp"
  and     P224_octets_to_point_comp_validInput   = "PG2_P224.octets_to_point_comp_validInput"
  and     P224_octets_to_point_comp              = "PG2_P224.octets_to_point_comp"
  and     P224_octets_to_point_validInput        = "PG2_P224.octets_to_point_validInput"
  and     P224_octets_to_point                   = "PG2_P224.octets_to_point"
  and     P224_twiceSecurityLevel                = "PG2_P224.twiceSecurityLevel"
  and     P224_ECdomainParametersValid           = "PG2_P224.ECdomainParametersValid"
  and     P224_ECdomainParametersValid'          = "PG2_P224.ECdomainParametersValid'"
  and     P224_twiceSecurityLevelInv             = "PG2_P224.twiceSecurityLevelInv"
  using P224_residues_prime_gt2 apply fast
  by (simp add: P224_R_def) 

text \<open>With a definition above, we can show one more thing about the curve parameters, namely\<close>
lemma P224_checkTP: "P224_twiceSecurityLevel P224_t = (bit_length P224_p)"
  by eval

lemma P224_checkTP': "P224_twiceSecurityLevel P224_t = \<lceil>log 2 P224_p\<rceil>"
  using P224_checkTP P224_p_prime P224_p_gr2 bitLenLog2Prime by presburger 

text \<open>We can restate some facts from above using PG2_P224 definitions\<close>
lemma P224_checkAB: 
  "(P224_a \<in> carrier P224_R) \<and> (P224_b \<in> carrier P224_R) \<and> (P224_nonsingular P224_a P224_b)"
proof - 
  have 1: "P224_a \<in> carrier P224_R" by (simp add: P224_checkA PG2_P224.inCarrier) 
  have 2: "P224_b \<in> carrier P224_R" by (simp add: P224_checkB PG2_P224.inCarrier) 
  have 3: "P224_nonsingular P224_a P224_b" 
    by (metis 1 2 P224_checkNonsingular P224_R_def P224_nonsingular_def P224_residues_prime_gt2 
        ell_prime_field.nonsingular_in_bf ell_prime_field_axioms.intro ell_prime_field_def) 
  show ?thesis using 1 2 3 by satx
qed

lemma P224_checkGoncurve': "P224_on_curve P224_a P224_b P224_G" 
  by eval

lemma P224_checkGord'h: 
  "efficient_funpow (P224_point_madd P224_a) Infinity P224_G P224_n = Infinity" 
  by eval

lemma P224_checkGord': "P224_point_mult P224_a P224_n P224_G = Infinity"
  using P224_checkAB P224_checkGoncurve' P224_checkGord'h PG2_P224.point_add_eq
        PG2_P224.point_mult_efficient[of P224_a P224_b P224_G P224_n]
  by presburger

text \<open>The last thing we are going to assume is that n*h is the number of points on the curve.\<close>
axiomatization where P224_numCurvePoints: "card {P. P224_on_curve P224_a P224_b P} = P224_n*P224_h"

text\<open>Then with the 3 things we assumed and all the things we checked, we know that these 
parameters describe a valid elliptic curve.  Then we can interpret the SEC1 locale with P224.\<close>

lemma P224valid: "P224_ECdomainParametersValid P224_a P224_b P224_G P224_n P224_h P224_t"
  using PG2_P224.ECdomainParametersValid_def P224_checkNHnotP P224_checkHnot0 P224_checkH
        P224_checkAB P224_n_prime P224_checkTP' P224_checkPmodN P224_checkT P224_checkHT 
        P224_checkGoncurve' P224_checkGord' P224_checkGnotInf P224_numCurvePoints by presburger

global_interpretation SEC1_P224: SEC1 P224_p P224_R P224_a P224_b P224_n P224_h P224_t P224_G
  defines SEC1_P224_Rn                      = "SEC1_P224.Rn"
  and     SEC1_P224_ECkeyGen                = "SEC1_P224.ECkeyGen"
  and     SEC1_P224_ECkeyPairValid          = "SEC1_P224.ECkeyPairValid"
  and     SEC1_P224_ECprivateKeyValid       = "SEC1_P224.ECprivateKeyValid"
  and     SEC1_P224_ECpublicKeyValid        = "SEC1_P224.ECpublicKeyValid"
  and     SEC1_P224_ECpublicKeyPartialValid = "SEC1_P224.ECpublicKeyPartialValid"
  and     SEC1_P224_ECDHprim                = "SEC1_P224.ECDHprim"
  and     SEC1_P224_MQVcomputeQbar          = "SEC1_P224.MQVcomputeQbar"
  and     SEC1_P224_MQVcompute_s            = "SEC1_P224.MQVcompute_s"
  and     SEC1_P224_MQVcomputeP             = "SEC1_P224.MQVcomputeP"
  and     SEC1_P224_ECMQVprim_validInput    = "SEC1_P224.ECMQVprim_validInput"
  and     SEC1_P224_ECMQVprim               = "SEC1_P224.ECMQVprim"
  and     SEC1_P224_ECDSA_compute_e         = "SEC1_P224.ECDSA_compute_e"
  and     SEC1_P224_ECDSA_Sign_e            = "SEC1_P224.ECDSA_Sign_e"
  and     SEC1_P224_ECDSA_Verify_e          = "SEC1_P224.ECDSA_Verify_e"
  and     SEC1_P224_ECDSA_Verify_e_Alt      = "SEC1_P224.ECDSA_Verify_e_Alt"
  and     SEC1_P224_ECDSA_Verify_Alt        = "SEC1_P224.ECDSA_Verify_Alt"
  using P224valid SEC1.intro SEC1_axioms_def P224_residues_prime_gt2 
        P224_ECdomainParametersValid_def apply simp 
  using P224_R_def by simp 

abbreviation "SEC1_P224_on_curve'        \<equiv> P224_on_curve P224_a P224_b"
abbreviation "SEC1_P224_mon_curve'       \<equiv> mon_curve P224_p P224_a P224_b"
abbreviation "SEC1_P224_point_mult'      \<equiv> P224_point_mult P224_a"
abbreviation "SEC1_P224_point_mmult'     \<equiv> P224_point_mmult P224_a"
abbreviation "SEC1_P224_add'             \<equiv> P224_add P224_a"
abbreviation "SEC1_P224_madd'            \<equiv> P224_point_madd P224_a"
abbreviation "SEC1_P224_octets_to_point' \<equiv> P224_octets_to_point P224_a P224_b"
abbreviation "SEC1_P224_inv_mod_n        \<equiv> inv_mod P224_n"
abbreviation "SEC1_P224_ECDSA_Sign Hash d\<^sub>U M k P \<equiv> 
                SEC1_P224_ECDSA_Sign_e d\<^sub>U (SEC1_P224_ECDSA_compute_e Hash M) k P"
abbreviation "SEC1_P224_ECDSA_Sign_e' d\<^sub>U e k     \<equiv> 
                SEC1_P224_ECDSA_Sign_e d\<^sub>U e k (SEC1_P224_ECkeyGen k)"
abbreviation "SEC1_P224_ECDSA_Sign' Hash d\<^sub>U M k  \<equiv> 
                SEC1_P224_ECDSA_Sign Hash d\<^sub>U M k (SEC1_P224_ECkeyGen k)"
abbreviation "SEC1_P224_ECDSA_Verify Hash Q\<^sub>U M S \<equiv> 
                SEC1_P224_ECDSA_Verify_e Q\<^sub>U (SEC1_P224_ECDSA_compute_e Hash M) S"

section \<open>P-256\<close>

subsection \<open>Parameters\<close>

definition P256_p :: nat where 
  "P256_p = 115792089210356248762697446949407573530086143415290314195533631308867097853951"

definition P256_n :: nat where 
  "P256_n = 115792089210356248762697446949407573529996955224135760342422259061068512044369"

definition P256_SEED :: nat where 
  "P256_SEED = 0xc49d360886e704936a6678e1139d26b7819f7e90"

definition P256_c :: nat where 
  "P256_c = 0x7efba1662985be9403cb055c75d4f7e0ce8d84a9c5114abcaf3177680104fa0d"

definition P256_a :: nat where 
  "P256_a = P256_p - 3"

definition P256_b :: nat where 
  "P256_b = 0x5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604b"

definition P256_Gx :: nat where 
  "P256_Gx = 0x6b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c296"

definition P256_Gy :: nat where 
  "P256_Gy = 0x4fe342e2fe1a7f9b8ee7eb4a7c0f9e162bce33576b315ececbb6406837bf51f5"

definition P256_G :: "int point" where
  "P256_G = Point (int P256_Gx) (int P256_Gy)"

definition P256_prG :: "int ppoint" where
  "P256_prG = (int P256_Gx, int P256_Gy, 1)"

definition P256_h :: nat where
  "P256_h = 1"

definition P256_t :: nat where
  "P256_t = 128"

subsection \<open>Parameter Checks\<close>

text\<open>We can't easily check that n and p are prime, but there are many conditions on the parameters
of an elliptic curve to be considered a valid curve.  We check now the things that we can check.\<close>

text\<open>We are just going to assume that p is prime.\<close>
axiomatization where P256_p_prime: "prime P256_p"

text\<open>But we can easily see that p is an odd prime.\<close>
lemma P256_p_gr2: "2 < P256_p" by eval

text\<open>We are just going to assume that n is prime.\<close>
axiomatization where P256_n_prime: "prime P256_n"

text \<open>Check (\<forall>B\<in>{1..99}. (p^B mod n \<noteq> 1)).\<close>
lemma P256_checkPmodN: "\<forall>i\<in>{1..99}. (P256_p^i mod P256_n \<noteq> 1)"
proof - 
  have 1: "list_all (%i. P256_p^i mod P256_n \<noteq> 1) [1..<100]" by eval
  have 2: "\<forall>i \<in> set [1..<100]. (P256_p^i mod P256_n \<noteq> 1)" 
    by (metis (mono_tags, lifting) 1 Ball_set)
  have 3: "set [1..<100] = {1::nat..99}" by fastforce
  show ?thesis using 2 3 by blast
qed

text\<open>Check (a \<in> carrier R) \<and> (b \<in> carrier R) \<and> (nonsingular a b)\<close>
lemma P256_checkA: "P256_a < P256_p" by eval

lemma P256_checkB: "P256_b < P256_p" by eval

lemma P256_checkNonsingular: "(4*P256_a^3 + 27*P256_b^2) mod P256_p \<noteq> 0"
  by eval

text \<open>Check (on_curve a b G)  \<and> (G \<noteq> Infinity)  \<and> (point_mult a n G = Infinity)\<close>
lemma P256_checkGnotInf: "P256_G \<noteq> Infinity" 
  by eval

lemma P256_checkGoncurve: "mon_curve P256_p P256_a P256_b P256_G" 
  by eval

lemma P256_checkGord:
  "mmake_affine P256_p (fast_ppoint_mult P256_p P256_a P256_n P256_prG) = Infinity"
  by eval

text \<open>Check the cofactor h and the security level t.\<close>
lemma P256_checkT: "P256_t \<in> {80, 112, 128, 192, 256}"
  by eval

lemma P256_checkHT: "P256_h \<le> 2^(P256_t div 8)"
  by eval

lemma P256_checkNHnotP: "P256_n * P256_h \<noteq> P256_p" 
  by eval

lemma P256_checkHnot0: "0 < P256_h" 
  by eval

text \<open>Check \<open>h = \<lfloor>((sqrt p + 1)^2) div n\<rfloor>\<close>.  This is slightly more involved than the above checks.\<close>
lemma P256_checkH1: "(P256_h*P256_n - P256_p - 1)^2 \<le> 4*P256_p"     by eval

lemma P256_checkH2: "4*P256_p < ((P256_h+1)*P256_n - P256_p - 1)^2"  by eval

lemma P256_checkH: "P256_h = \<lfloor>((sqrt P256_p + 1)^2) div P256_n\<rfloor>"
proof - 
  have p1: "((sqrt P256_p) + 1)^2 = P256_p + 2*(sqrt P256_p) + 1"
    by (simp add: power2_sum)
  have n1: "0 < P256_n" by eval
  have l1: "P256_h*P256_n - P256_p - 1 \<le> 2*(sqrt P256_p)"
    by (metis (mono_tags, opaque_lifting) P256_checkH1 real_le_rsqrt of_nat_le_iff of_nat_mult 
        of_nat_numeral of_nat_power real_sqrt_four real_sqrt_mult) 
  have l2: "P256_h*P256_n \<le> P256_p + 2*(sqrt P256_p) + 1"
    using l1 by linarith
  have l3: "P256_h*P256_n \<le> ((sqrt P256_p) + 1)^2"
    using l2 p1 by presburger
  have l4: "P256_h \<le> (((sqrt P256_p) + 1)^2) div P256_n"
    using l3 pos_le_divide_eq n1 by force 
  have g1: "2*(sqrt P256_p) < (P256_h+1)*P256_n - P256_p - 1"
    by (metis (mono_tags, opaque_lifting) P256_checkH2 real_less_lsqrt of_nat_mult of_nat_less_iff
        of_nat_numeral of_nat_power real_sqrt_four real_sqrt_mult of_nat_0_le_iff) 
  have g2: "P256_p + 2*(sqrt P256_p) + 1 < (P256_h+1)*P256_n"
    by (smt (verit, ccfv_SIG) g1 P256_p_gr2 add_diff_inverse_nat cring_class.of_nat_add of_nat_1
        less_diff_conv less_imp_of_nat_less nat_1_add_1 of_nat_less_imp_less real_sqrt_ge_one)
  have g3: "((sqrt P256_p) + 1)^2 < (P256_h+1)*P256_n"
    using g2 p1 by presburger
  have g4: "(((sqrt P256_p) + 1)^2) div P256_n < (P256_h+1)"
    by (metis g3 n1 pos_divide_less_eq of_nat_0_less_iff of_nat_mult) 
  show ?thesis using l4 g4 by linarith
qed

subsection \<open>Interpretations\<close>

text \<open>Because p is (assumed to be) prime and greater than 2, we can interpret the 
residues_prime_gr2 locale.\<close>

lemma P256_residues_prime_gt2: "residues_prime_gt2 P256_p"
  using P256_p_prime P256_p_gr2 residues_prime_gt2_def residues_prime.intro 
        residues_prime_gt2_axioms.intro by blast

definition P256_R :: "int ring" where
  "P256_R = residue_ring (int P256_p)"

global_interpretation PG2_P256: residues_prime_gt2 P256_p P256_R
  defines P256_nonsingular = "PG2_P256.nonsingular"
  and     P256_on_curve    = "PG2_P256.on_curve"
  and     P256_add         = "PG2_P256.add"
  and     P256_opp         = "PG2_P256.opp"
  and     P256_is_tangent  = "PG2_P256.is_tangent"
  and     P256_is_generic  = "PG2_P256.is_generic"
  and     P256_point_mult  = "PG2_P256.point_mult"
  and     P256_pdouble     = "PG2_P256.pdouble"
  and     P256_padd        = "PG2_P256.padd"
  and     P256_make_affine = "PG2_P256.make_affine"
  and     P256_in_carrierp = "PG2_P256.in_carrierp"
  and     P256_on_curvep   = "PG2_P256.on_curvep"
  and     P256_ppoint_mult = "PG2_P256.ppoint_mult"
  and     P256_proj_eq     = "PG2_P256.proj_eq"
  and     P256_point_madd  = "PG2_P256.point_madd"
  and     P256_point_mmult = "PG2_P256.point_mmult"
  and     P256_point_to_octets_nocomp = "PG2_P256.point_to_octets_nocomp"
  and     P256_point_to_octets_comp   = "PG2_P256.point_to_octets_comp"
  and     P256_point_to_octets        = "PG2_P256.point_to_octets"
  and     P256_FlipY                  = "PG2_P256.FlipY"
  and     P256_FlipYhd                = "PG2_P256.FlipYhd"
  and     P256_octets_to_point_nocomp_validInput = "PG2_P256.octets_to_point_nocomp_validInput"
  and     P256_octets_to_point_nocomp            = "PG2_P256.octets_to_point_nocomp"
  and     P256_octets_to_point_comp_validInput   = "PG2_P256.octets_to_point_comp_validInput"
  and     P256_octets_to_point_comp              = "PG2_P256.octets_to_point_comp"
  and     P256_octets_to_point_validInput        = "PG2_P256.octets_to_point_validInput"
  and     P256_octets_to_point                   = "PG2_P256.octets_to_point"
  and     P256_twiceSecurityLevel                = "PG2_P256.twiceSecurityLevel"
  and     P256_ECdomainParametersValid           = "PG2_P256.ECdomainParametersValid"
  and     P256_ECdomainParametersValid'          = "PG2_P256.ECdomainParametersValid'"
  and     P256_twiceSecurityLevelInv             = "PG2_P256.twiceSecurityLevelInv"
  using P256_residues_prime_gt2 apply fast
  by (simp add: P256_R_def) 

text \<open>With a definition above, we can show one more thing about the curve parameters, namely\<close>
lemma P256_checkTP: "P256_twiceSecurityLevel P256_t = (bit_length P256_p)"
  by eval

lemma P256_checkTP': "P256_twiceSecurityLevel P256_t = \<lceil>log 2 P256_p\<rceil>"
  using P256_checkTP P256_p_prime P256_p_gr2 bitLenLog2Prime by presburger 

text \<open>We can restate some facts from above using PG2_P256 definitions\<close>
lemma P256_checkAB: 
  "(P256_a \<in> carrier P256_R) \<and> (P256_b \<in> carrier P256_R) \<and> (P256_nonsingular P256_a P256_b)"
proof - 
  have 1: "P256_a \<in> carrier P256_R" by (simp add: P256_checkA PG2_P256.inCarrier) 
  have 2: "P256_b \<in> carrier P256_R" by (simp add: P256_checkB PG2_P256.inCarrier) 
  have 3: "P256_nonsingular P256_a P256_b" 
    by (metis 1 2 P256_checkNonsingular P256_R_def P256_nonsingular_def P256_residues_prime_gt2 
        ell_prime_field.nonsingular_in_bf ell_prime_field_axioms.intro ell_prime_field_def) 
  show ?thesis using 1 2 3 by satx
qed

lemma P256_checkGoncurve': "P256_on_curve P256_a P256_b P256_G" 
  by eval

lemma P256_checkGord'h: 
  "efficient_funpow (P256_point_madd P256_a) Infinity P256_G P256_n = Infinity" 
  by eval

lemma P256_checkGord': "P256_point_mult P256_a P256_n P256_G = Infinity"
  using P256_checkAB P256_checkGoncurve' P256_checkGord'h PG2_P256.point_add_eq
        PG2_P256.point_mult_efficient[of P256_a P256_b P256_G P256_n]
  by presburger

text \<open>The last thing we are going to assume is that n*h is the number of points on the curve.\<close>
axiomatization where P256_numCurvePoints: "card {P. P256_on_curve P256_a P256_b P} = P256_n*P256_h"

text\<open>Then with the 3 things we assumed and all the things we checked, we know that these 
parameters describe a valid elliptic curve.  Then we can interpret the SEC1 locale with P256.\<close>

lemma P256valid: "P256_ECdomainParametersValid P256_a P256_b P256_G P256_n P256_h P256_t"
  using PG2_P256.ECdomainParametersValid_def P256_checkNHnotP P256_checkHnot0 P256_checkH
        P256_checkAB P256_n_prime P256_checkTP' P256_checkPmodN P256_checkT P256_checkHT 
        P256_checkGoncurve' P256_checkGord' P256_checkGnotInf P256_numCurvePoints by presburger

global_interpretation SEC1_P256: SEC1 P256_p P256_R P256_a P256_b P256_n P256_h P256_t P256_G
  defines SEC1_P256_Rn                      = "SEC1_P256.Rn"
  and     SEC1_P256_ECkeyGen                = "SEC1_P256.ECkeyGen"
  and     SEC1_P256_ECkeyPairValid          = "SEC1_P256.ECkeyPairValid"
  and     SEC1_P256_ECprivateKeyValid       = "SEC1_P256.ECprivateKeyValid"
  and     SEC1_P256_ECpublicKeyValid        = "SEC1_P256.ECpublicKeyValid"
  and     SEC1_P256_ECpublicKeyPartialValid = "SEC1_P256.ECpublicKeyPartialValid"
  and     SEC1_P256_ECDHprim                = "SEC1_P256.ECDHprim"
  and     SEC1_P256_MQVcomputeQbar          = "SEC1_P256.MQVcomputeQbar"
  and     SEC1_P256_MQVcompute_s            = "SEC1_P256.MQVcompute_s"
  and     SEC1_P256_MQVcomputeP             = "SEC1_P256.MQVcomputeP"
  and     SEC1_P256_ECMQVprim_validInput    = "SEC1_P256.ECMQVprim_validInput"
  and     SEC1_P256_ECMQVprim               = "SEC1_P256.ECMQVprim"
  and     SEC1_P256_ECDSA_compute_e         = "SEC1_P256.ECDSA_compute_e"
  and     SEC1_P256_ECDSA_Sign_e            = "SEC1_P256.ECDSA_Sign_e"
  and     SEC1_P256_ECDSA_Verify_e          = "SEC1_P256.ECDSA_Verify_e"
  and     SEC1_P256_ECDSA_Verify_e_Alt      = "SEC1_P256.ECDSA_Verify_e_Alt"
  and     SEC1_P256_ECDSA_Verify_Alt        = "SEC1_P256.ECDSA_Verify_Alt"
  using P256valid SEC1.intro SEC1_axioms_def P256_residues_prime_gt2 
        P256_ECdomainParametersValid_def apply simp 
  using P256_R_def by simp 

abbreviation "SEC1_P256_on_curve'        \<equiv> P256_on_curve P256_a P256_b"
abbreviation "SEC1_P256_mon_curve'       \<equiv> mon_curve P256_p P256_a P256_b"
abbreviation "SEC1_P256_point_mult'      \<equiv> P256_point_mult P256_a"
abbreviation "SEC1_P256_point_mmult'     \<equiv> P256_point_mmult P256_a"
abbreviation "SEC1_P256_add'             \<equiv> P256_add P256_a"
abbreviation "SEC1_P256_madd'            \<equiv> P256_point_madd P256_a"
abbreviation "SEC1_P256_octets_to_point' \<equiv> P256_octets_to_point P256_a P256_b"
abbreviation "SEC1_P256_inv_mod_n        \<equiv> inv_mod P256_n"
abbreviation "SEC1_P256_ECDSA_Sign Hash d\<^sub>U M k P \<equiv> 
                SEC1_P256_ECDSA_Sign_e d\<^sub>U (SEC1_P256_ECDSA_compute_e Hash M) k P"
abbreviation "SEC1_P256_ECDSA_Sign_e' d\<^sub>U e k     \<equiv> 
                SEC1_P256_ECDSA_Sign_e d\<^sub>U e k (SEC1_P256_ECkeyGen k)"
abbreviation "SEC1_P256_ECDSA_Sign' Hash d\<^sub>U M k  \<equiv> 
                SEC1_P256_ECDSA_Sign Hash d\<^sub>U M k (SEC1_P256_ECkeyGen k)"
abbreviation "SEC1_P256_ECDSA_Verify Hash Q\<^sub>U M S \<equiv> 
                SEC1_P256_ECDSA_Verify_e Q\<^sub>U (SEC1_P256_ECDSA_compute_e Hash M) S"

section \<open>P-384\<close>

subsection \<open>Parameters\<close>

definition P384_p :: nat where 
  "P384_p = 39402006196394479212279040100143613805079739270465446667948293404245721771496870329047266088258938001861606973112319"

definition P384_n :: nat where 
  "P384_n = 39402006196394479212279040100143613805079739270465446667946905279627659399113263569398956308152294913554433653942643"

definition P384_SEED :: nat where 
  "P384_SEED = 0xa335926aa319a27a1d00896a6773a4827acdac73"

definition P384_c :: nat where 
  "P384_c = 0x79d1e655f868f02fff48dcdee14151ddb80643c1406d0ca10dfe6fc52009540a495e8042ea5f744f6e184667cc722483"

definition P384_a :: nat where 
  "P384_a = P384_p - 3"

definition P384_b :: nat where 
  "P384_b = 0xb3312fa7e23ee7e4988e056be3f82d19181d9c6efe8141120314088f5013875ac656398d8a2ed19d2a85c8edd3ec2aef"

definition P384_Gx :: nat where 
  "P384_Gx = 0xaa87ca22be8b05378eb1c71ef320ad746e1d3b628ba79b9859f741e082542a385502f25dbf55296c3a545e3872760ab7"

definition P384_Gy :: nat where 
  "P384_Gy = 0x3617de4a96262c6f5d9e98bf9292dc29f8f41dbd289a147ce9da3113b5f0b8c00a60b1ce1d7e819d7a431d7c90ea0e5f"

definition P384_G :: "int point" where
  "P384_G = Point (int P384_Gx) (int P384_Gy)"

definition P384_prG :: "int ppoint" where
  "P384_prG = (int P384_Gx, int P384_Gy, 1)"

definition P384_h :: nat where
  "P384_h = 1"

definition P384_t :: nat where
  "P384_t = 192"


subsection \<open>Parameter Checks\<close>

text\<open>We can't easily check that n and p are prime, but there are many conditions on the parameters
of an elliptic curve to be considered a valid curve.  We check now the things that we can check.\<close>

text\<open>We are just going to assume that p is prime.\<close>
axiomatization where P384_p_prime: "prime P384_p"

text\<open>But we can easily see that p is an odd prime.\<close>
lemma P384_p_gr2: "2 < P384_p" by eval

text\<open>We are just going to assume that n is prime.\<close>
axiomatization where P384_n_prime: "prime P384_n"

text \<open>Check (\<forall>B\<in>{1..99}. (p^B mod n \<noteq> 1)).\<close>
lemma P384_checkPmodN: "\<forall>i\<in>{1..99}. (P384_p^i mod P384_n \<noteq> 1)"
proof - 
  have 1: "list_all (%i. P384_p^i mod P384_n \<noteq> 1) [1..<100]" by eval
  have 2: "\<forall>i \<in> set [1..<100]. (P384_p^i mod P384_n \<noteq> 1)" 
    by (metis (mono_tags, lifting) 1 Ball_set)
  have 3: "set [1..<100] = {1::nat..99}" by fastforce
  show ?thesis using 2 3 by blast
qed

text\<open>Check (a \<in> carrier R) \<and> (b \<in> carrier R) \<and> (nonsingular a b)\<close>
lemma P384_checkA: "P384_a < P384_p" by eval

lemma P384_checkB: "P384_b < P384_p" by eval

lemma P384_checkNonsingular: "(4*P384_a^3 + 27*P384_b^2) mod P384_p \<noteq> 0"
  by eval

text \<open>Check (on_curve a b G)  \<and> (G \<noteq> Infinity)  \<and> (point_mult a n G = Infinity)\<close>
lemma P384_checkGnotInf: "P384_G \<noteq> Infinity" 
  by eval

lemma P384_checkGoncurve: "mon_curve P384_p P384_a P384_b P384_G" 
  by eval

lemma P384_checkGord:
  "mmake_affine P384_p (fast_ppoint_mult P384_p P384_a P384_n P384_prG) = Infinity"
  by eval

text \<open>Check the cofactor h and the security level t.\<close>
lemma P384_checkT: "P384_t \<in> {80, 112, 128, 192, 256}"
  by eval

lemma P384_checkHT: "P384_h \<le> 2^(P384_t div 8)"
  by eval

lemma P384_checkNHnotP: "P384_n * P384_h \<noteq> P384_p" 
  by eval

lemma P384_checkHnot0: "0 < P384_h" 
  by eval

text \<open>Check \<open>h = \<lfloor>((sqrt p + 1)^2) div n\<rfloor>\<close>.  This is slightly more involved than the above checks.\<close>
lemma P384_checkH1: "(P384_h*P384_n - P384_p - 1)^2 \<le> 4*P384_p"     by eval

lemma P384_checkH2: "4*P384_p < ((P384_h+1)*P384_n - P384_p - 1)^2"  by eval

lemma P384_checkH: "P384_h = \<lfloor>((sqrt P384_p + 1)^2) div P384_n\<rfloor>"
proof - 
  have p1: "((sqrt P384_p) + 1)^2 = P384_p + 2*(sqrt P384_p) + 1"
    by (simp add: power2_sum)
  have n1: "0 < P384_n" by eval
  have l1: "P384_h*P384_n - P384_p - 1 \<le> 2*(sqrt P384_p)"
    by (metis (mono_tags, opaque_lifting) P384_checkH1 real_le_rsqrt of_nat_le_iff of_nat_mult 
        of_nat_numeral of_nat_power real_sqrt_four real_sqrt_mult) 
  have l2: "P384_h*P384_n \<le> P384_p + 2*(sqrt P384_p) + 1"
    using l1 by linarith
  have l3: "P384_h*P384_n \<le> ((sqrt P384_p) + 1)^2"
    using l2 p1 by presburger
  have l4: "P384_h \<le> (((sqrt P384_p) + 1)^2) div P384_n"
    using l3 pos_le_divide_eq n1 by force 
  have g1: "2*(sqrt P384_p) < (P384_h+1)*P384_n - P384_p - 1"
    by (metis (mono_tags, opaque_lifting) P384_checkH2 real_less_lsqrt of_nat_mult of_nat_less_iff
        of_nat_numeral of_nat_power real_sqrt_four real_sqrt_mult of_nat_0_le_iff) 
  have g2: "P384_p + 2*(sqrt P384_p) + 1 < (P384_h+1)*P384_n"
    by (smt (verit, ccfv_SIG) g1 P384_p_gr2 add_diff_inverse_nat cring_class.of_nat_add of_nat_1
        less_diff_conv less_imp_of_nat_less nat_1_add_1 of_nat_less_imp_less real_sqrt_ge_one)
  have g3: "((sqrt P384_p) + 1)^2 < (P384_h+1)*P384_n"
    using g2 p1 by presburger
  have g4: "(((sqrt P384_p) + 1)^2) div P384_n < (P384_h+1)"
    by (metis g3 n1 pos_divide_less_eq of_nat_0_less_iff of_nat_mult) 
  show ?thesis using l4 g4 by linarith
qed

subsection \<open>Interpretations\<close>

text \<open>Because p is (assumed to be) prime and greater than 2, we can interpret the 
residues_prime_gr2 locale.\<close>

lemma P384_residues_prime_gt2: "residues_prime_gt2 P384_p"
  using P384_p_prime P384_p_gr2 residues_prime_gt2_def residues_prime.intro 
        residues_prime_gt2_axioms.intro by blast

definition P384_R :: "int ring" where
  "P384_R = residue_ring (int P384_p)"

global_interpretation PG2_P384: residues_prime_gt2 P384_p P384_R
  defines P384_nonsingular = "PG2_P384.nonsingular"
  and     P384_on_curve    = "PG2_P384.on_curve"
  and     P384_add         = "PG2_P384.add"
  and     P384_opp         = "PG2_P384.opp"
  and     P384_is_tangent  = "PG2_P384.is_tangent"
  and     P384_is_generic  = "PG2_P384.is_generic"
  and     P384_point_mult  = "PG2_P384.point_mult"
  and     P384_pdouble     = "PG2_P384.pdouble"
  and     P384_padd        = "PG2_P384.padd"
  and     P384_make_affine = "PG2_P384.make_affine"
  and     P384_in_carrierp = "PG2_P384.in_carrierp"
  and     P384_on_curvep   = "PG2_P384.on_curvep"
  and     P384_ppoint_mult = "PG2_P384.ppoint_mult"
  and     P384_proj_eq     = "PG2_P384.proj_eq"
  and     P384_point_madd  = "PG2_P384.point_madd"
  and     P384_point_mmult = "PG2_P384.point_mmult"
  and     P384_point_to_octets_nocomp = "PG2_P384.point_to_octets_nocomp"
  and     P384_point_to_octets_comp   = "PG2_P384.point_to_octets_comp"
  and     P384_point_to_octets        = "PG2_P384.point_to_octets"
  and     P384_FlipY                  = "PG2_P384.FlipY"
  and     P384_FlipYhd                = "PG2_P384.FlipYhd"
  and     P384_octets_to_point_nocomp_validInput = "PG2_P384.octets_to_point_nocomp_validInput"
  and     P384_octets_to_point_nocomp            = "PG2_P384.octets_to_point_nocomp"
  and     P384_octets_to_point_comp_validInput   = "PG2_P384.octets_to_point_comp_validInput"
  and     P384_octets_to_point_comp              = "PG2_P384.octets_to_point_comp"
  and     P384_octets_to_point_validInput        = "PG2_P384.octets_to_point_validInput"
  and     P384_octets_to_point                   = "PG2_P384.octets_to_point"
  and     P384_twiceSecurityLevel                = "PG2_P384.twiceSecurityLevel"
  and     P384_ECdomainParametersValid           = "PG2_P384.ECdomainParametersValid"
  and     P384_ECdomainParametersValid'          = "PG2_P384.ECdomainParametersValid'"
  and     P384_twiceSecurityLevelInv             = "PG2_P384.twiceSecurityLevelInv"
  using P384_residues_prime_gt2 apply fast
  by (simp add: P384_R_def) 

text \<open>With a definition above, we can show one more thing about the curve parameters, namely\<close>
lemma P384_checkTP: "P384_twiceSecurityLevel P384_t = (bit_length P384_p)"
  by eval

lemma P384_checkTP': "P384_twiceSecurityLevel P384_t = \<lceil>log 2 P384_p\<rceil>"
  using P384_checkTP P384_p_prime P384_p_gr2 bitLenLog2Prime by presburger 

text \<open>We can restate some facts from above using PG2_P384 definitions\<close>
lemma P384_checkAB: 
  "(P384_a \<in> carrier P384_R) \<and> (P384_b \<in> carrier P384_R) \<and> (P384_nonsingular P384_a P384_b)"
proof - 
  have 1: "P384_a \<in> carrier P384_R" by (simp add: P384_checkA PG2_P384.inCarrier) 
  have 2: "P384_b \<in> carrier P384_R" by (simp add: P384_checkB PG2_P384.inCarrier) 
  have 3: "P384_nonsingular P384_a P384_b" 
    by (metis 1 2 P384_checkNonsingular P384_R_def P384_nonsingular_def P384_residues_prime_gt2 
        ell_prime_field.nonsingular_in_bf ell_prime_field_axioms.intro ell_prime_field_def) 
  show ?thesis using 1 2 3 by satx
qed

lemma P384_checkGoncurve': "P384_on_curve P384_a P384_b P384_G" 
  by eval

lemma P384_checkGord'h: 
  "efficient_funpow (P384_point_madd P384_a) Infinity P384_G P384_n = Infinity" 
  by eval

lemma P384_checkGord': "P384_point_mult P384_a P384_n P384_G = Infinity"
  using P384_checkAB P384_checkGoncurve' P384_checkGord'h PG2_P384.point_add_eq
        PG2_P384.point_mult_efficient[of P384_a P384_b P384_G P384_n]
  by presburger

text \<open>The last thing we are going to assume is that n*h is the number of points on the curve.\<close>
axiomatization where P384_numCurvePoints: "card {P. P384_on_curve P384_a P384_b P} = P384_n*P384_h"

text\<open>Then with the 3 things we assumed and all the things we checked, we know that these 
parameters describe a valid elliptic curve.  Then we can interpret the SEC1 locale with P384.\<close>

lemma P384valid: "P384_ECdomainParametersValid P384_a P384_b P384_G P384_n P384_h P384_t"
  using PG2_P384.ECdomainParametersValid_def P384_checkNHnotP P384_checkHnot0 P384_checkH
        P384_checkAB P384_n_prime P384_checkTP' P384_checkPmodN P384_checkT P384_checkHT 
        P384_checkGoncurve' P384_checkGord' P384_checkGnotInf P384_numCurvePoints by presburger

global_interpretation SEC1_P384: SEC1 P384_p P384_R P384_a P384_b P384_n P384_h P384_t P384_G
  defines SEC1_P384_Rn                      = "SEC1_P384.Rn"
  and     SEC1_P384_ECkeyGen                = "SEC1_P384.ECkeyGen"
  and     SEC1_P384_ECkeyPairValid          = "SEC1_P384.ECkeyPairValid"
  and     SEC1_P384_ECprivateKeyValid       = "SEC1_P384.ECprivateKeyValid"
  and     SEC1_P384_ECpublicKeyValid        = "SEC1_P384.ECpublicKeyValid"
  and     SEC1_P384_ECpublicKeyPartialValid = "SEC1_P384.ECpublicKeyPartialValid"
  and     SEC1_P384_ECDHprim                = "SEC1_P384.ECDHprim"
  and     SEC1_P384_MQVcomputeQbar          = "SEC1_P384.MQVcomputeQbar"
  and     SEC1_P384_MQVcompute_s            = "SEC1_P384.MQVcompute_s"
  and     SEC1_P384_MQVcomputeP             = "SEC1_P384.MQVcomputeP"
  and     SEC1_P384_ECMQVprim_validInput    = "SEC1_P384.ECMQVprim_validInput"
  and     SEC1_P384_ECMQVprim               = "SEC1_P384.ECMQVprim"
  and     SEC1_P384_ECDSA_compute_e         = "SEC1_P384.ECDSA_compute_e"
  and     SEC1_P384_ECDSA_Sign_e            = "SEC1_P384.ECDSA_Sign_e"
  and     SEC1_P384_ECDSA_Verify_e          = "SEC1_P384.ECDSA_Verify_e"
  and     SEC1_P384_ECDSA_Verify_e_Alt      = "SEC1_P384.ECDSA_Verify_e_Alt"
  and     SEC1_P384_ECDSA_Verify_Alt        = "SEC1_P384.ECDSA_Verify_Alt"
  using P384valid SEC1.intro SEC1_axioms_def P384_residues_prime_gt2 
        P384_ECdomainParametersValid_def apply simp 
  using P384_R_def by simp 

abbreviation "SEC1_P384_on_curve'        \<equiv> P384_on_curve P384_a P384_b"
abbreviation "SEC1_P384_mon_curve'       \<equiv> mon_curve P384_p P384_a P384_b"
abbreviation "SEC1_P384_point_mult'      \<equiv> P384_point_mult P384_a"
abbreviation "SEC1_P384_point_mmult'     \<equiv> P384_point_mmult P384_a"
abbreviation "SEC1_P384_add'             \<equiv> P384_add P384_a"
abbreviation "SEC1_P384_madd'            \<equiv> P384_point_madd P384_a"
abbreviation "SEC1_P384_octets_to_point' \<equiv> P384_octets_to_point P384_a P384_b"
abbreviation "SEC1_P384_inv_mod_n        \<equiv> inv_mod P384_n"
abbreviation "SEC1_P384_ECDSA_Sign Hash d\<^sub>U M k P \<equiv> 
                SEC1_P384_ECDSA_Sign_e d\<^sub>U (SEC1_P384_ECDSA_compute_e Hash M) k P"
abbreviation "SEC1_P384_ECDSA_Sign_e' d\<^sub>U e k     \<equiv> 
                SEC1_P384_ECDSA_Sign_e d\<^sub>U e k (SEC1_P384_ECkeyGen k)"
abbreviation "SEC1_P384_ECDSA_Sign' Hash d\<^sub>U M k  \<equiv> 
                SEC1_P384_ECDSA_Sign Hash d\<^sub>U M k (SEC1_P384_ECkeyGen k)"
abbreviation "SEC1_P384_ECDSA_Verify Hash Q\<^sub>U M S \<equiv> 
                SEC1_P384_ECDSA_Verify_e Q\<^sub>U (SEC1_P384_ECDSA_compute_e Hash M) S"

section \<open>P-521\<close>

subsection \<open>Parameters\<close>

definition P521_p :: nat where 
  "P521_p = 6864797660130609714981900799081393217269435300143305409394463459185543183397656052122559640661454554977296311391480858037121987999716643812574028291115057151"

definition P521_n :: nat where 
  "P521_n = 6864797660130609714981900799081393217269435300143305409394463459185543183397655394245057746333217197532963996371363321113864768612440380340372808892707005449"

definition P521_SEED :: nat where 
  "P521_SEED = 0xd09e8800291cb85396cc6717393284aaa0da64ba"

definition P521_c :: nat where 
  "P521_c = 0x0b48bfa5f420a34949539d2bdfc264eeeeb077688e44fbf0ad8f6d0edb37bd6b533281000518e19f1b9ffbe0fe9ed8a3c2200b8f875e523868c70c1e5bf55bad637"

definition P521_a :: nat where 
  "P521_a = P521_p - 3"

definition P521_b :: nat where 
  "P521_b = 0x051953eb9618e1c9a1f929a21a0b68540eea2da725b99b315f3b8b489918ef109e156193951ec7e937b1652c0bd3bb1bf073573df883d2c34f1ef451fd46b503f00"

definition P521_Gx :: nat where 
  "P521_Gx = 0xc6858e06b70404e9cd9e3ecb662395b4429c648139053fb521f828af606b4d3dbaa14b5e77efe75928fe1dc127a2ffa8de3348b3c1856a429bf97e7e31c2e5bd66"

definition P521_Gy :: nat where 
  "P521_Gy = 0x11839296a789a3bc0045c8a5fb42c7d1bd998f54449579b446817afbd17273e662c97ee72995ef42640c550b9013fad0761353c7086a272c24088be94769fd16650"

definition P521_G :: "int point" where
  "P521_G = Point (int P521_Gx) (int P521_Gy)"

definition P521_prG :: "int ppoint" where
  "P521_prG = (int P521_Gx, int P521_Gy, 1)"

definition P521_h :: nat where
  "P521_h = 1"

definition P521_t :: nat where
  "P521_t = 256"


subsection \<open>Parameter Checks\<close>

text\<open>We can't easily check that n and p are prime, but there are many conditions on the parameters
of an elliptic curve to be considered a valid curve.  We check now the things that we can check.\<close>

text\<open>We are just going to assume that p is prime.\<close>
axiomatization where P521_p_prime: "prime P521_p"

text\<open>But we can easily see that p is an odd prime.\<close>
lemma P521_p_gr2: "2 < P521_p" by eval

text\<open>We are just going to assume that n is prime.\<close>
axiomatization where P521_n_prime: "prime P521_n"

text \<open>Check (\<forall>B\<in>{1..99}. (p^B mod n \<noteq> 1)).\<close>
lemma P521_checkPmodN: "\<forall>i\<in>{1..99}. (P521_p^i mod P521_n \<noteq> 1)"
proof - 
  have 1: "list_all (%i. P521_p^i mod P521_n \<noteq> 1) [1..<100]" by eval
  have 2: "\<forall>i \<in> set [1..<100]. (P521_p^i mod P521_n \<noteq> 1)" 
    by (metis (mono_tags, lifting) 1 Ball_set)
  have 3: "set [1..<100] = {1::nat..99}" by fastforce
  show ?thesis using 2 3 by blast
qed

text\<open>Check (a \<in> carrier R) \<and> (b \<in> carrier R) \<and> (nonsingular a b)\<close>
lemma P521_checkA: "P521_a < P521_p" by eval

lemma P521_checkB: "P521_b < P521_p" by eval

lemma P521_checkNonsingular: "(4*P521_a^3 + 27*P521_b^2) mod P521_p \<noteq> 0"
  by eval

text \<open>Check (on_curve a b G)  \<and> (G \<noteq> Infinity)  \<and> (point_mult a n G = Infinity)\<close>
lemma P521_checkGnotInf: "P521_G \<noteq> Infinity" 
  by eval

lemma P521_checkGoncurve: "mon_curve P521_p P521_a P521_b P521_G" 
  by eval

lemma P521_checkGord:
  "mmake_affine P521_p (fast_ppoint_mult P521_p P521_a P521_n P521_prG) = Infinity"
  by eval

text \<open>Check the cofactor h and the security level t.\<close>
lemma P521_checkT: "P521_t \<in> {80, 112, 128, 192, 256}"
  by eval

lemma P521_checkHT: "P521_h \<le> 2^(P521_t div 8)"
  by eval

lemma P521_checkNHnotP: "P521_n * P521_h \<noteq> P521_p" 
  by eval

lemma P521_checkHnot0: "0 < P521_h" 
  by eval

text \<open>Check \<open>h = \<lfloor>((sqrt p + 1)^2) div n\<rfloor>\<close>.  This is slightly more involved than the above checks.\<close>
lemma P521_checkH1: "(P521_h*P521_n - P521_p - 1)^2 \<le> 4*P521_p"     by eval

lemma P521_checkH2: "4*P521_p < ((P521_h+1)*P521_n - P521_p - 1)^2"  by eval

lemma P521_checkH: "P521_h = \<lfloor>((sqrt P521_p + 1)^2) div P521_n\<rfloor>"
proof - 
  have p1: "((sqrt P521_p) + 1)^2 = P521_p + 2*(sqrt P521_p) + 1"
    by (simp add: power2_sum)
  have n1: "0 < P521_n" by eval
  have l1: "P521_h*P521_n - P521_p - 1 \<le> 2*(sqrt P521_p)"
    by (metis (mono_tags, opaque_lifting) P521_checkH1 real_le_rsqrt of_nat_le_iff of_nat_mult 
        of_nat_numeral of_nat_power real_sqrt_four real_sqrt_mult) 
  have l2: "P521_h*P521_n \<le> P521_p + 2*(sqrt P521_p) + 1"
    using l1 by linarith
  have l3: "P521_h*P521_n \<le> ((sqrt P521_p) + 1)^2"
    using l2 p1 by presburger
  have l4: "P521_h \<le> (((sqrt P521_p) + 1)^2) div P521_n"
    using l3 pos_le_divide_eq n1 by force 
  have g1: "2*(sqrt P521_p) < (P521_h+1)*P521_n - P521_p - 1"
    by (metis (mono_tags, opaque_lifting) P521_checkH2 real_less_lsqrt of_nat_mult of_nat_less_iff
        of_nat_numeral of_nat_power real_sqrt_four real_sqrt_mult of_nat_0_le_iff) 
  have g2: "P521_p + 2*(sqrt P521_p) + 1 < (P521_h+1)*P521_n"
    by (smt (verit, ccfv_SIG) g1 P521_p_gr2 add_diff_inverse_nat cring_class.of_nat_add of_nat_1
        less_diff_conv less_imp_of_nat_less nat_1_add_1 of_nat_less_imp_less real_sqrt_ge_one)
  have g3: "((sqrt P521_p) + 1)^2 < (P521_h+1)*P521_n"
    using g2 p1 by presburger
  have g4: "(((sqrt P521_p) + 1)^2) div P521_n < (P521_h+1)"
    by (metis g3 n1 pos_divide_less_eq of_nat_0_less_iff of_nat_mult) 
  show ?thesis using l4 g4 by linarith
qed

subsection \<open>Interpretations\<close>

text \<open>Because p is (assumed to be) prime and greater than 2, we can interpret the 
residues_prime_gr2 locale.\<close>

lemma P521_residues_prime_gt2: "residues_prime_gt2 P521_p"
  using P521_p_prime P521_p_gr2 residues_prime_gt2_def residues_prime.intro 
        residues_prime_gt2_axioms.intro by blast

definition P521_R :: "int ring" where
  "P521_R = residue_ring (int P521_p)"

global_interpretation PG2_P521: residues_prime_gt2 P521_p P521_R
  defines P521_nonsingular = "PG2_P521.nonsingular"
  and     P521_on_curve    = "PG2_P521.on_curve"
  and     P521_add         = "PG2_P521.add"
  and     P521_opp         = "PG2_P521.opp"
  and     P521_is_tangent  = "PG2_P521.is_tangent"
  and     P521_is_generic  = "PG2_P521.is_generic"
  and     P521_point_mult  = "PG2_P521.point_mult"
  and     P521_pdouble     = "PG2_P521.pdouble"
  and     P521_padd        = "PG2_P521.padd"
  and     P521_make_affine = "PG2_P521.make_affine"
  and     P521_in_carrierp = "PG2_P521.in_carrierp"
  and     P521_on_curvep   = "PG2_P521.on_curvep"
  and     P521_ppoint_mult = "PG2_P521.ppoint_mult"
  and     P521_proj_eq     = "PG2_P521.proj_eq"
  and     P521_point_madd  = "PG2_P521.point_madd"
  and     P521_point_mmult = "PG2_P521.point_mmult"
  and     P521_point_to_octets_nocomp = "PG2_P521.point_to_octets_nocomp"
  and     P521_point_to_octets_comp   = "PG2_P521.point_to_octets_comp"
  and     P521_point_to_octets        = "PG2_P521.point_to_octets"
  and     P521_FlipY                  = "PG2_P521.FlipY"
  and     P521_FlipYhd                = "PG2_P521.FlipYhd"
  and     P521_octets_to_point_nocomp_validInput = "PG2_P521.octets_to_point_nocomp_validInput"
  and     P521_octets_to_point_nocomp            = "PG2_P521.octets_to_point_nocomp"
  and     P521_octets_to_point_comp_validInput   = "PG2_P521.octets_to_point_comp_validInput"
  and     P521_octets_to_point_comp              = "PG2_P521.octets_to_point_comp"
  and     P521_octets_to_point_validInput        = "PG2_P521.octets_to_point_validInput"
  and     P521_octets_to_point                   = "PG2_P521.octets_to_point"
  and     P521_twiceSecurityLevel                = "PG2_P521.twiceSecurityLevel"
  and     P521_ECdomainParametersValid           = "PG2_P521.ECdomainParametersValid"
  and     P521_ECdomainParametersValid'          = "PG2_P521.ECdomainParametersValid'"
  and     P521_twiceSecurityLevelInv             = "PG2_P521.twiceSecurityLevelInv"
  using P521_residues_prime_gt2 apply fast
  by (simp add: P521_R_def) 

text \<open>With a definition above, we can show one more thing about the curve parameters, namely\<close>
lemma P521_checkTP: "P521_twiceSecurityLevel P521_t = (bit_length P521_p)"
  by eval

lemma P521_checkTP': "P521_twiceSecurityLevel P521_t = \<lceil>log 2 P521_p\<rceil>"
  using P521_checkTP P521_p_prime P521_p_gr2 bitLenLog2Prime by presburger 

text \<open>We can restate some facts from above using PG2_P521 definitions\<close>
lemma P521_checkAB: 
  "(P521_a \<in> carrier P521_R) \<and> (P521_b \<in> carrier P521_R) \<and> (P521_nonsingular P521_a P521_b)"
proof - 
  have 1: "P521_a \<in> carrier P521_R" by (simp add: P521_checkA PG2_P521.inCarrier) 
  have 2: "P521_b \<in> carrier P521_R" by (simp add: P521_checkB PG2_P521.inCarrier) 
  have 3: "P521_nonsingular P521_a P521_b" 
    by (metis 1 2 P521_checkNonsingular P521_R_def P521_nonsingular_def P521_residues_prime_gt2 
        ell_prime_field.nonsingular_in_bf ell_prime_field_axioms.intro ell_prime_field_def) 
  show ?thesis using 1 2 3 by satx
qed

lemma P521_checkGoncurve': "P521_on_curve P521_a P521_b P521_G" 
  by eval

lemma P521_checkGord'h: 
  "efficient_funpow (P521_point_madd P521_a) Infinity P521_G P521_n = Infinity" 
  by eval

lemma P521_checkGord': "P521_point_mult P521_a P521_n P521_G = Infinity"
  using P521_checkAB P521_checkGoncurve' P521_checkGord'h PG2_P521.point_add_eq
        PG2_P521.point_mult_efficient[of P521_a P521_b P521_G P521_n]
  by presburger

text \<open>The last thing we are going to assume is that n*h is the number of points on the curve.\<close>
axiomatization where P521_numCurvePoints: "card {P. P521_on_curve P521_a P521_b P} = P521_n*P521_h"

text\<open>Then with the 3 things we assumed and all the things we checked, we know that these 
parameters describe a valid elliptic curve.  Then we can interpret the SEC1 locale with P521.\<close>

lemma P521valid: "P521_ECdomainParametersValid P521_a P521_b P521_G P521_n P521_h P521_t"
  using PG2_P521.ECdomainParametersValid_def P521_checkNHnotP P521_checkHnot0 P521_checkH
        P521_checkAB P521_n_prime P521_checkTP' P521_checkPmodN P521_checkT P521_checkHT 
        P521_checkGoncurve' P521_checkGord' P521_checkGnotInf P521_numCurvePoints by presburger

global_interpretation SEC1_P521: SEC1 P521_p P521_R P521_a P521_b P521_n P521_h P521_t P521_G
  defines SEC1_P521_Rn                      = "SEC1_P521.Rn"
  and     SEC1_P521_ECkeyGen                = "SEC1_P521.ECkeyGen"
  and     SEC1_P521_ECkeyPairValid          = "SEC1_P521.ECkeyPairValid"
  and     SEC1_P521_ECprivateKeyValid       = "SEC1_P521.ECprivateKeyValid"
  and     SEC1_P521_ECpublicKeyValid        = "SEC1_P521.ECpublicKeyValid"
  and     SEC1_P521_ECpublicKeyPartialValid = "SEC1_P521.ECpublicKeyPartialValid"
  and     SEC1_P521_ECDHprim                = "SEC1_P521.ECDHprim"
  and     SEC1_P521_MQVcomputeQbar          = "SEC1_P521.MQVcomputeQbar"
  and     SEC1_P521_MQVcompute_s            = "SEC1_P521.MQVcompute_s"
  and     SEC1_P521_MQVcomputeP             = "SEC1_P521.MQVcomputeP"
  and     SEC1_P521_ECMQVprim_validInput    = "SEC1_P521.ECMQVprim_validInput"
  and     SEC1_P521_ECMQVprim               = "SEC1_P521.ECMQVprim"
  and     SEC1_P521_ECDSA_compute_e         = "SEC1_P521.ECDSA_compute_e"
  and     SEC1_P521_ECDSA_Sign_e            = "SEC1_P521.ECDSA_Sign_e"
  and     SEC1_P521_ECDSA_Verify_e          = "SEC1_P521.ECDSA_Verify_e"
  and     SEC1_P521_ECDSA_Verify_e_Alt      = "SEC1_P521.ECDSA_Verify_e_Alt"
  and     SEC1_P521_ECDSA_Verify_Alt        = "SEC1_P521.ECDSA_Verify_Alt"
  using P521valid SEC1.intro SEC1_axioms_def P521_residues_prime_gt2 
        P521_ECdomainParametersValid_def apply simp 
  using P521_R_def by simp 

abbreviation "SEC1_P521_on_curve'        \<equiv> P521_on_curve P521_a P521_b"
abbreviation "SEC1_P521_mon_curve'       \<equiv> mon_curve P521_p P521_a P521_b"
abbreviation "SEC1_P521_point_mult'      \<equiv> P521_point_mult P521_a"
abbreviation "SEC1_P521_point_mmult'     \<equiv> P521_point_mmult P521_a"
abbreviation "SEC1_P521_add'             \<equiv> P521_add P521_a"
abbreviation "SEC1_P521_madd'            \<equiv> P521_point_madd P521_a"
abbreviation "SEC1_P521_octets_to_point' \<equiv> P521_octets_to_point P521_a P521_b"
abbreviation "SEC1_P521_inv_mod_n        \<equiv> inv_mod P521_n"
abbreviation "SEC1_P521_ECDSA_Sign Hash d\<^sub>U M k P \<equiv> 
                SEC1_P521_ECDSA_Sign_e d\<^sub>U (SEC1_P521_ECDSA_compute_e Hash M) k P"
abbreviation "SEC1_P521_ECDSA_Sign_e' d\<^sub>U e k     \<equiv> 
                SEC1_P521_ECDSA_Sign_e d\<^sub>U e k (SEC1_P521_ECkeyGen k)"
abbreviation "SEC1_P521_ECDSA_Sign' Hash d\<^sub>U M k  \<equiv> 
                SEC1_P521_ECDSA_Sign Hash d\<^sub>U M k (SEC1_P521_ECkeyGen k)"
abbreviation "SEC1_P521_ECDSA_Verify Hash Q\<^sub>U M S \<equiv> 
                SEC1_P521_ECDSA_Verify_e Q\<^sub>U (SEC1_P521_ECDSA_compute_e Hash M) S"

end