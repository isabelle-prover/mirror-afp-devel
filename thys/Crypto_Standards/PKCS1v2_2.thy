theory PKCS1v2_2
  imports  
    Words
          
begin

text \<open>The PKCS #1 standard defines primitives and schemes related to the RSA cryptosystem.  It is
currently in version 2.2.

https://www.rfc-editor.org/rfc/rfc8017
http://mpqs.free.fr/h11300-pkcs-1v2-2-rsa-cryptography-standard-wp_EMC_Corporation_Public-Key_Cryptography_Standards_(PKCS).pdf

In this theory, we translate the functions defined in PKCS #1 v2.2 to Isabelle. We adhere as
closely to the written standard as possible, including function and variable names.  It should
be painfully obvious, even to non-Isabelle users, that the definitions here match exactly
those in the standard.

Notes:
- We will only consider the case of n = p*q, and ignore the "multi-prime" RSA (see section 3 of
  PKCS #1).  That is, in the notation of the standard, we only consider u = 2.
- The abbreviation CRT will refer to the Chinese Remainder Theorem.
- The standard includes some error checking on input.  We aim to keep the definitions of the 
  cryptographic primitives to mathematical functions.  In the case that the standard specifies
  an error case, we define a "foo_inputValid" Isabelle function to capture that requirement 
  separate from the foo function definition.
- PKCS #1 defines an octet as an 8-bit byte.  We use the same terminology, and use "octets" to
  mean a string (list) of octets.  Words.thy implements the conversions from non-negative
  integers to octet strings and back again, as defined in PCKS #1 v 2.2.

The structure of this theory mimics exactly the structure of the standard.  Definitions found
in Section 3 (for example) of the standard are found in the section titled Section 3 in this 
theory.  In addition to those definitions, each section contains a subsection that proves all the
lemmas that one might care to know about them.  For example, you may find there lemmas about
converting between private keys for use in the CRT decryption method and the corresponding key
for use without the CRT method.  There are also many less lofty but practical lemmas.  Note that
Section 9 must precede Section 8 because of dependencies among their definitions.
\<close>


text \<open>Some of the schemes describe in PKCS #1 assume the existence of a hash function or a mask
generating function (mgf).  For this translation, we only need to know the type of such functions.
For certain lemmas we may need to assume things, such as the output of a hash function is always of
a given length.  Those assumptions will be made as they are needed.
\<close>

type_synonym mgf_type  = "octets \<Rightarrow> nat \<Rightarrow> octets"
type_synonym hash_type = "octets \<Rightarrow> octets" 

section \<open>Section 3: RSA Key Types\<close>

named_theorems ValidKeyDefs

subsection \<open>Section 3.1: RSA Public Key\<close>
text \<open>The current standard uses Carmichael's totient, l = lcm((p-1),(q-1)).  This is more efficient
than using Euler's totient, (p-1)*(q-1).\<close>

definition PKCS1_validRSApublicKey :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  [ValidKeyDefs]:"PKCS1_validRSApublicKey n e p q \<equiv> 
  ( let l = (lcm (p-1) (q-1)) in
    (prime p) \<and> (2 < p) \<and> (prime q) \<and> (2 < q) \<and> (p\<noteq>q) \<and> (n = p*q) \<and> 
    (2 < e)   \<and> (e < n) \<and> (gcd e l = 1) )"

definition PKCS1_validRSApublicKeyPair :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  "PKCS1_validRSApublicKeyPair n e \<equiv> (\<exists>p q. PKCS1_validRSApublicKey n e p q)"

subsection \<open>Section 3.2: RSA Private Key\<close>

definition PKCS1_validRSAprivateKey :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  [ValidKeyDefs]:"PKCS1_validRSAprivateKey n d p q e \<equiv> 
  ( let l = (lcm (p-1) (q-1)) in
    (PKCS1_validRSApublicKey n e p q) \<and> (0 < d) \<and> (d < n) \<and> (e*d mod l = 1) )"

definition PKCS1_validRSAprivateKey_CRT :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  [ValidKeyDefs]: "PKCS1_validRSAprivateKey_CRT p q dP dQ qInv e \<equiv> 
    (PKCS1_validRSApublicKey (p*q) e p q) \<and> (0 < dP) \<and> (dP < p) \<and> (e*dP mod (p-1) = 1) \<and> 
    (0 < dQ) \<and> (dQ < q) \<and> (e*dQ mod (q-1) = 1) \<and> (q*qInv mod p = 1)"

subsection \<open>Valid Key Lemmas\<close>

named_theorems ValidKeyThms

lemma validPublicKey_pq_symm:
  assumes "PKCS1_validRSApublicKey n e p q"
  shows   "PKCS1_validRSApublicKey n e q p"
  by (metis assms PKCS1_validRSApublicKey_def lcm.commute mult.commute) 

lemma validPrivateKey_pq_symm:
  assumes "PKCS1_validRSAprivateKey n d p q e"
  shows   "PKCS1_validRSAprivateKey n d q p e"
  by (metis assms ValidKeyDefs(1,2) lcm.commute mult.commute) 

lemma validPrivateKey_ed_symm:
  assumes "PKCS1_validRSAprivateKey n d p q e" "2 < d"
  shows   "PKCS1_validRSAprivateKey n e p q d"
proof -
  let ?l = "lcm (p-1) (q-1)"
  have n: "(prime p) \<and> (2 < p) \<and> (prime q) \<and> (2 < q) \<and> (p\<noteq>q) \<and> (n = p*q)"
    using assms(1) ValidKeyDefs(1,2) by algebra
  have e1: "(2 < e) \<and> (e < n) \<and> (gcd e ?l = 1)"   using assms(1) ValidKeyDefs(1,2) by metis
  have e0: "0 < e"                                using e1 by fastforce 
  have d1: "(2 < d) \<and> (d < n) \<and> (e*d mod ?l = 1)" using assms ValidKeyDefs(2) by algebra
  have d2: "gcd d ?l = 1"
  by (metis d1 gcd.bottom_right_bottom gcd.left_commute gcd_0_nat gcd_red_nat mod_mult_self2_is_0)
  show ?thesis by (metis n e1 e0 d1 d2 ValidKeyDefs(1,2) mult.commute) 
qed

lemma n_prime_factorization:
  assumes "prime (p::nat)"  "prime q"  "n = p*q"  "p \<noteq> q"
  shows   "prime_factors n = {p, q} \<and> multiplicity p n = 1 \<and> multiplicity q n = 1"
proof - 
  have 2: "0 < p \<and> 0 < q"  using assms prime_gt_0_nat by presburger 
  have 3: "multiplicity p n = 1 \<and> multiplicity q n = 1" 
    by (metis assms 2 One_nat_def multiplicity_times_same neq0_conv not_prime_unit 
              prime_multiplicity_other mult.commute) 
  have 4: "(count (prime_factorization n) p = 1) \<and> (count (prime_factorization n) q = 1)" 
    by (metis assms(1,2) 3 prime_factorization.rep_eq) 
  have 5: "(p \<in> prime_factors n) \<and> (q \<in> prime_factors n)" 
    by (metis 4 count_greater_zero_iff less_one)  
  have 6: "prime_factors n \<subseteq> {p,q}" 
    by (metis assms in_prime_factors_iff insert_iff prime_dvd_mult_nat primes_dvd_imp_eq subsetI) 
  have    "prime_factors n = {p,q}"  using 5 6 by blast
  then show ?thesis  using 3 by blast
qed

lemma n_positive:
  assumes "prime (p::nat)"  "prime q"  "n = p*q" 
  shows   "0 < n" 
  using assms prime_gt_0_nat by simp

lemma n_positive2:
  assumes "PKCS1_validRSApublicKey n e p q"
  shows   "0 < n"
  using assms PKCS1_validRSApublicKey_def n_positive by algebra

lemma p_minus_1_gr_1:
  assumes "PKCS1_validRSApublicKey n e p q"
  shows   "1 < p - 1"
  using assms PKCS1_validRSApublicKey_def by force

lemma q_minus_1_gr_1:
  assumes "PKCS1_validRSApublicKey n e p q"
  shows   "1 < q - 1"
  using assms PKCS1_validRSApublicKey_def by force

lemma n_totient:
  assumes "prime (p::nat)"  "prime q"  "n = p*q"  "p \<noteq> q"
  shows   "totient n = (p-1)*(q-1)" 
  by (metis assms nat_less_le prime_imp_coprime prime_nat_iff residues_prime.intro 
            residues_prime.prime_totient_eq totient_mult_coprime)

lemma n_odd:
  assumes "PKCS1_validRSApublicKey n e p q"
  shows   "n mod 2 = 1"
  by (metis PKCS1_validRSApublicKey_def assms even_mult_iff parity_cases prime_odd_nat)

lemma n_odd2:
  assumes "PKCS1_validRSApublicKeyPair n e"
  shows   "n mod 2 = 1"
  using PKCS1_validRSApublicKeyPair_def assms n_odd by blast

lemma l_dvd_totient_n:
  assumes "prime (p::nat)"  "prime q"  "n = p*q"  "p \<noteq> q"  "l = lcm (p-1) (q-1)"
  shows   "l dvd totient n"
  using assms n_totient by force

lemma l_less_n:
  assumes "prime (p::nat)"  "prime q"  "n = p*q"  "p \<noteq> q"  "l = lcm (p-1) (q-1)"
  shows   "l < n"
  by (metis assms dual_order.strict_trans l_dvd_totient_n less_1_mult linorder_neqE_nat 
            n_positive nat_dvd_not_less prime_gt_1_nat totient_gt_0_iff totient_less)

lemma dP_from_d: 
  assumes "PKCS1_validRSAprivateKey n d p q e"  "dP = d mod (p-1)" 
  shows   "e*dP mod (p-1) = 1 \<and> 0 < dP \<and> dP < p"
proof - 
  have "2 < p"              using assms(1) ValidKeyDefs(1,2) by algebra
  then have p1: "1 < p - 1" by linarith
  let ?l = "lcm (p-1) (q-1)"
  have "e*d mod ?l = 1"     using assms(1) PKCS1_validRSAprivateKey_def by algebra 
  then have a: "e*dP mod (p-1) = 1"
    by (metis assms(2) dvd_lcm1 mod_if mod_mod_cancel mod_mult_right_eq p1)
  have b: "dP < p" 
    by (metis assms(2) p1 add_diff_inverse_nat bot_nat_0.not_eq_extremum le_simps(1) 
              mod_less_divisor nat_diff_split not_one_le_zero trans_less_add2) 
  have c: "0 < dP"          by (metis a bits_mod_0 mult_eq_0_iff neq0_conv zero_neq_one) 
  show ?thesis              using a b c by blast
qed

lemma dQ_from_d:
  assumes "PKCS1_validRSAprivateKey n d p q e"  "dQ = d mod (q-1)" 
  shows   "(e*dQ mod (q-1) = 1) \<and> 0 < dQ \<and> dQ < q"
  using assms dP_from_d validPrivateKey_pq_symm by meson 

text\<open>If you start with a valid private RSA key and you know the inverse of q (mod p), then it's
easy to write down a valid private RSA key for decrypting with the Chinese Remainder Theorem.\<close>
lemma validPrivateKey_to_validPrivateCRTkey [ValidKeyThms]:
  assumes "PKCS1_validRSAprivateKey n d p q e"  "(q*qInv mod p = 1)" 
          "dP = d mod (p-1)"  "dQ = d mod (q-1)" 
  shows   "PKCS1_validRSAprivateKey_CRT p q dP dQ qInv e"
  by (metis assms dP_from_d dQ_from_d ValidKeyDefs)

text\<open>It is possible to go from a CRT private key to a "plain" private key, but the computation is
more involved.  The "bezw" function here is for "Bezout's theorem witness", meaning bezw(a,b) will
return two integers (x,y) so that a*x + b*y = gcd a b.\<close>
definition d_from_dP_dQ :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where [ValidKeyDefs]:
  "d_from_dP_dQ dP dQ p q = 
  ( let pm1 = p-1;
        qm1 = q-1;
        g   = gcd pm1 qm1;
        l   = lcm pm1 qm1;
        u   = fst (bezw pm1 qm1);
        v   = snd (bezw pm1 qm1) 
    in
        nat ( ((dP*v*qm1 + dQ*u*pm1) div g) mod l) )" 

lemma d_from_dP_dQ_h1:
  fixes    pm1 qm1 :: nat
  and      u v     :: int 
  assumes "g = gcd pm1 qm1" 
  shows   "g dvd (dP*v*qm1 + dQ*u*pm1)"
  by (simp add: assms)

lemma d_from_dP_dQ_h2:
  assumes "d = d_from_dP_dQ dP dQ p q"  "n = p*q"  "PKCS1_validRSAprivateKey_CRT p q dP dQ qInv e"
  shows   "d < n"
  by (smt (z3) pos_mod_bound ValidKeyDefs(1,3) assms d_from_dP_dQ_def int_nat_eq l_less_n 
       lcm_int_int_eq lcm_pos_nat less_asym of_nat_0_less_iff of_nat_less_imp_less prime_gt_1_nat
       zero_less_diff) 

lemma d_from_dP_dQ_h3:
  assumes "PKCS1_validRSAprivateKey_CRT p q dP dQ qInv e"  "d = d_from_dP_dQ dP dQ p q" 
          "l = lcm (p-1) (q-1)"
  shows   "e*d mod l = 1"
proof -
  let ?pm1 = "p-1"
  let ?qm1 = "q-1" 
  let ?g   = "gcd ?pm1 ?qm1" 
  let ?u   = "fst (bezw ?pm1 ?qm1)"
  let ?v   = "snd (bezw ?pm1 ?qm1)"
  have gl: "?pm1*?qm1 = ?g*l"       using assms(3) prod_gcd_lcm_nat by presburger       
  have g:  "?u*?pm1 + ?v*?qm1 = ?g" using bezw_aux by presburger
  have e:  "e*dP mod ?pm1 = 1"      using assms(1) ValidKeyDefs(3) by algebra
  then obtain x where x: "e*dP = 1 + x*?pm1"  by (metis add.commute div_mod_decomp) 
  have "e*dQ mod ?qm1 = 1"          using assms(1) ValidKeyDefs(3) by algebra
  then obtain y where y: "e*dQ = 1 + y*?qm1"  by (metis add.commute div_mod_decomp) 
  have m1: "1 < ?pm1 \<and> 1 < ?qm1"    using assms(1) ValidKeyDefs(1,3) by auto
  have m2: "0 < ?pm1*?qm1"          using m1 by force
  have m3: "0 < l"                  using assms(3) lcm_pos_nat m2 nat_0_less_mult_iff by algebra
  let ?dint = "( (dP *?v * ?qm1 + dQ * ?u * ?pm1) div ?g) mod l" 
  have a0: "0 \<le> ?dint"       using m3 Euclidean_Rings.pos_mod_sign by simp
  have a1: "d = nat ?dint"   by (metis assms(2,3) d_from_dP_dQ_def gcd_int_int_eq lcm_int_int_eq)
  let ?eint = "int e" 
  let ?eiml = "?eint mod l" 
  have a2: "?eiml*?dint mod l = ?eint*((dP *?v * ?qm1 + dQ * ?u * ?pm1) div ?g) mod l"
    by (meson mod_mult_eq)
  have a3: "?eiml*?dint mod l = (?eint*(dP *?v * ?qm1 + dQ * ?u * ?pm1) div ?g) mod l"
    by (smt (verit, ccfv_threshold) a2 d_from_dP_dQ_h1 div_0 div_mult1_eq div_mult_mod_eq 
          dvd_div_mult_self of_nat_0 right_diff_distrib) 
  have a4: "?eiml*?dint mod l = ((?eint*dP *?v * ?qm1 + ?eint*dQ * ?u * ?pm1) div ?g) mod l"
    by (metis (no_types, opaque_lifting) a3 distrib_left mult.assoc) 
  have a5: "?eiml*?dint mod l = (((1 + x*?pm1)*?v * ?qm1 + (1 + y*?qm1) * ?u * ?pm1) div ?g) mod l"
    by (metis (no_types, lifting) a4 x y of_nat_mult) 
  have a6: "((1 + x*?pm1)*?v * ?qm1 + (1 + y*?qm1) * ?u * ?pm1) div ?g = 
             (?v*?qm1 + x*?pm1*?v*?qm1 + ?u*?pm1 + y*?qm1*?u*?pm1) div ?g"
    by (simp add: comm_semiring_class.distrib)
  have a7: "((1 + x*?pm1)*?v * ?qm1 + (1 + y*?qm1) * ?u * ?pm1) div ?g = 
             ((?v*?qm1 + ?u*?pm1) + (x*?pm1*?v*?qm1 + y*?qm1*?u*?pm1)) div ?g"
    using a6 by presburger
  have a8: "((1 + x*?pm1)*?v * ?qm1 + (1 + y*?qm1) * ?u * ?pm1) div ?g = 
             ((?g) + (x*?pm1*?v*?qm1 + y*?qm1*?u*?pm1)) div ?g"
    by (metis a7 g add.commute)
  have a9: "((1 + x*?pm1)*?v * ?qm1 + (1 + y*?qm1) * ?u * ?pm1) div ?g = 
             (?g + (x*?v*?pm1*?qm1 + y*?u*?pm1*?qm1)) div ?g"
    by (smt (verit, ccfv_threshold) a8 mult.left_commute mult_of_nat_commute of_nat_mult) 
  have a10: "((1 + x*?pm1)*?v * ?qm1 + (1 + y*?qm1) * ?u * ?pm1) div ?g = 
             (?g + (x*?v + y*?u)*?pm1*?qm1) div ?g"
    by (smt (verit) a9 distrib_left mult.assoc mult.commute of_nat_mult x y) 
  have a11: "((1 + x*?pm1)*?v * ?qm1 + (1 + y*?qm1) * ?u * ?pm1) div ?g = 
             (?g + (x*?v + y*?u)*?g*l) div ?g"
    by (metis (no_types, opaque_lifting) a10 gl mult.assoc of_nat_mult) 
  have a12: "((1 + x*?pm1)*?v * ?qm1 + (1 + y*?qm1) * ?u * ?pm1) div ?g = 
             (1*?g + (x*?v + y*?u)*l*?g) div ?g"
    using a11 mult.commute mult.left_commute by auto 
  have a13: "(1*?g + (x*?v + y*?u)*l*?g) = (1 + (x*?v + y*?u)*l)*?g" 
    by (smt (verit) semiring_normalization_rules(1) mult_cancel_right1 nat_mult_1)
  have a14: "(1*?g + (x*?v + y*?u)*l*?g) div ?g = 1 + (x*?v + y*?u)*l"
    by (metis a13 gl m2 mult.commute mult_zero_left nat_neq_iff nonzero_mult_div_cancel_left 
          of_nat_eq_0_iff) 
  have a15: "?eiml*?dint mod l = (1 + (x*?v + y*?u)*l) mod l"
    using a12 a14 a5 by presburger
  have a16: "?eiml*?dint mod l = 1 mod l"
    by (metis a15 mod_mult_self2 mult.commute of_nat_1 of_nat_mod) 
  have a17: "1 mod l = 1"
    by (metis m1 assms(3) dvd_eq_mod_eq_0 dvd_lcm1 lcm_0_iff_nat less_one linorder_neqE_nat 
          mod_less) 
  show ?thesis
    by (smt (verit) a0 a1 a16 a17 int_nat_eq mod_mult_left_eq of_nat_eq_iff of_nat_mod of_nat_mult)
qed

lemma d_from_dP_dQ_h4:
  assumes "d = d_from_dP_dQ dP dQ p q"  "PKCS1_validRSAprivateKey_CRT p q dP dQ qInv e"
  shows   "0 < d"
  by (metis assms d_from_dP_dQ_h3 bits_mod_0 mult_0_right neq0_conv zero_neq_one) 

text\<open>As said above, we can convert a valid RSA private key for CRT decryption into a valid RSA
private key for "plain" decryption.\<close>
lemma validPrivateCRTKey_to_validPrivateKey [ValidKeyThms]:
  assumes "PKCS1_validRSAprivateKey_CRT p q dP dQ qInv e"  "d = d_from_dP_dQ dP dQ p q"  "n=p*q"
  shows   "PKCS1_validRSAprivateKey n d p q e"
  by (metis ValidKeyDefs(2,3) assms d_from_dP_dQ_h2 d_from_dP_dQ_h3 d_from_dP_dQ_h4)

text\<open>The standard only insists that the decryption exponent d is < n.  But it's only d's value
modulo l that matters.  If the standard insisted that d < l, then there would be a unique 
decryption exponent d for a fixed RSA public key (n,e,p,q). \<close>
lemma d_unique_mod_l: 
  assumes "PKCS1_validRSAprivateKey n d1 p q e"  "PKCS1_validRSAprivateKey n d2 p q e" 
          "l = (lcm (p-1) (q-1))"
  shows   "[d1 = d2] (mod l)" 
proof - 
  have d1: "[e*d1 = 1] (mod l)" by (metis assms(1,3) ValidKeyDefs(2) cong_def mod_mod_trivial) 
  have d2: "[e*d2 = 1] (mod l)" by (metis assms(2,3) ValidKeyDefs(2) cong_def mod_mod_trivial) 
  show ?thesis
    by (metis (mono_tags, opaque_lifting) d1 d2 cong_def mod_mult_right_eq mult.left_commute
               mult.right_neutral)
qed

lemma d_mod_l_valid:
  assumes "PKCS1_validRSAprivateKey n d1 p q e"  "0 < d2"  "d2 < n"  "[d1=d2] (mod l)" 
          "l = (lcm (p-1) (q-1))"
  shows   "PKCS1_validRSAprivateKey n d2 p q e"
  by (metis (mono_tags, lifting) ValidKeyDefs(2) assms cong_def mod_mult_right_eq)

text\<open>In contrast, the standard requires that dP < p and dQ < q.  Given that, we know that their
values are unique for a fixed RSA public key (n,e,p,q)\<close>
lemma dP_dQ_unique:
  assumes "PKCS1_validRSAprivateKey_CRT p q dP1 dQ1 qInv e"
          "PKCS1_validRSAprivateKey_CRT p q dP2 dQ2 qInv e"
  shows   "dP1 = dP2 \<and> dQ1 = dQ2"
proof - 
  let ?l = "lcm (p-1) (q-1)"
  have e1:  "gcd e ?l = 1"    using assms(1) ValidKeyDefs(1,3) by algebra
  have ep1: "gcd e (p-1) = 1" by (metis e1 dvd_lcm1 gcd_lcm_distrib is_unit_gcd_iff) 
  have ep2: "coprime e (p-1)" using ep1 by blast
  have eq1: "gcd e (q-1) = 1" by (metis e1 dvd_lcm1 gcd_lcm_distrib is_unit_gcd_iff lcm.commute)
  have eq2: "coprime e (q-1)" using eq1 by blast
  have p0:  "0 < p-1"         using assms(1) ValidKeyDefs(1,3) by force
  have p1:  "e*dP1 mod (p-1) = 1" using assms(1) ValidKeyDefs(3) by blast
  have p2:  "e*dP2 mod (p-1) = 1" using assms(2) ValidKeyDefs(3) by blast
  have p3:  "e*dP1 mod (p-1) = e*dP2 mod (p-1)" using p1 p2 by presburger
  have p4:  "dP1 mod (p-1) = dP2 mod (p-1)"     by (meson p3 ep2 cong_mult_lcancel_nat cong_def)
  have p5:  "dP1 < p \<and> dP2 < p"   using assms(1,2) ValidKeyDefs(3) by blast
  have p6:  "dP1 < p-1 \<and> dP2 < p-1" 
    by (metis p1 p2 p5 Suc_leI diff_Suc_1 less_imp_Suc_add linorder_neqE_nat mod_mult_self2_is_0 
           not_le zero_neq_one) 
  have p7: "dP1 mod (p-1) = dP1 \<and> dP2 mod (p-1) = dP2" using p0 p6 by force
  have p:  "dP1 = dP2"            using p4 p7 by argo
  have q0: "0 < q-1"              using assms(1) ValidKeyDefs(1,3) by force
  have q1: "e*dQ1 mod (q-1) = 1"  using assms(1) ValidKeyDefs(3) by blast
  have q2: "e*dQ2 mod (q-1) = 1"  using assms(2) ValidKeyDefs(3) by blast
  have q3: "e*dQ1 mod (q-1) = e*dQ2 mod (q-1)" using q1 q2 by presburger
  have q4: "dQ1 mod (q-1) = dQ2 mod (q-1)"     by (meson q3 eq2 cong_mult_lcancel_nat cong_def)
  have q5: "dQ1 < q \<and> dQ2 < q"                 using assms(1,2) ValidKeyDefs(3) by blast
  have q6: "dQ1 < q-1 \<and> dQ2 < q-1" 
    by (metis q1 q2 q5 Suc_leI diff_Suc_1 less_imp_Suc_add linorder_neqE_nat mod_mult_self2_is_0 
          not_le zero_neq_one) 
  have q7: "dQ1 mod (q-1) = dQ1 \<and> dQ2 mod (q-1) = dQ2"  using q0 q6 by force
  have q:  "dQ1 = dQ2"                                  using q4 q7 by argo
  show ?thesis using p q by blast
qed

text \<open>Finally, if you have a valid public key, there is a decryption exponent d that completes
a valid private key.  Of course in order to compute d, one must know the factorization of n = p*q.\<close>
lemma ValidPublicKey_to_ValidPrivateKey:
  assumes "PKCS1_validRSApublicKey n e p q"
  shows   "\<exists>d. PKCS1_validRSAprivateKey n d p q e"
proof -
  let ?l = "lcm (p-1) (q-1)"
  have 1: "gcd e ?l = 1"  using assms(1) ValidKeyDefs(1) by algebra
  let ?ei = "int  e"
  let ?li = "int ?l"
  obtain x y where 2: "x*?ei + y*?li = 1"  by (metis 1 bezw_aux of_nat_1)
  have 3: "x*?ei mod ?li = 1" 
    by (smt (verit, ccfv_SIG) 2 assms int_ops(2) lcm_0_iff_nat lcm_eq_1_iff less_one q_minus_1_gr_1
          linorder_neqE_nat mod_less mod_mult_self3 nat_dvd_not_less of_nat_mod p_minus_1_gr_1)
  let ?d = "nat (x mod ?li)" 
  have 4: "?d * e mod ?l = 1" 
    by (smt (z3) 1 2 3 Euclidean_Rings.pos_mod_sign gcd_0_nat int_nat_eq mod_mult_left_eq
          mult_cancel_right1 mult_eq_0_iff nat_int nat_one_as_int nat_times_as_int of_nat_le_0_iff
          of_nat_mod) 
  have 5: "0 < ?d" 
    by (metis 4 mod_0 mult_is_0 not_gr_zero one_neq_zero) 
  have 6: "?d < n" 
    by (smt (verit, ccfv_threshold) 4 5 Euclidean_Rings.pos_mod_bound ValidKeyDefs(1)
          assms gcd_0_nat l_less_n less_imp_of_nat_less mod_by_0 mult.right_neutral nat_less_iff
          of_nat_le_0_iff split_nat)
  show ?thesis  by (metis 4 5 6 assms ValidKeyDefs(2) mult.commute)
qed

lemma ValidPublicKeyPair_to_ValidPrivateKey:
  assumes "PKCS1_validRSApublicKeyPair n e"
  shows   "\<exists>p q d. PKCS1_validRSAprivateKey n d p q e"
  using ValidPublicKey_to_ValidPrivateKey assms PKCS1_validRSApublicKeyPair_def by fast


section \<open>Section 4: Data Conversion Primitives\<close>
text \<open>"Two data conversion primitives are employed in the schemes defined in this document:
  •I2OSP – Integer-to-Octet-String primitive
  •OS2IP – Octet-String-to-Integer primitive
For the purposes of this document, and consistent with ASN.1 syntax, an octet string is an ordered
sequence of octets (eight-bit bytes).  The sequence is indexed from first (conventionally,  
leftmost) to last (rightmost).  For purposes of conversion to and from integers, the first octet
is considered the most significant in the following conversion primitives.

Write the integer x in its unique xLen-digit representation in base 256:
  x = x_{xLen–1} 256^{xLen–1} + x_{xLen–2} 256^{xLen–2} + ... + x_1 256 + x_0,  
where 0 \<le> xi < 256 (note that one or more leading digits will be zero if x is less than 
256^{xLen–1}). 

Let the octet X_i have the integer value x{xLen–i} for 1 \<le> i \<le>xLen.  Output the octet string 
  X = X_1 X_2 ... X_{xLen}."

Octets.thy is a separate theory that contains all the foundational lemmas related to these data
conversion primitives. Update: Octets.thy has been generalized to Words.thy, to handle conversions
from natural numbers to a list of w-bit values and back again.
\<close>

subsection \<open>Section 4.1: Integer to Octet String\<close>

definition PKCS1_I2OSP_inputValid :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  "PKCS1_I2OSP_inputValid x xLen = (x < 256^xLen)"

definition PKCS1_I2OSP :: "nat \<Rightarrow> nat \<Rightarrow> octets" where
  "PKCS1_I2OSP x xLen = nat_to_octets_len x xLen" 

subsection \<open>Section 4.2: Octet String to Integer\<close>

definition PKCS1_OS2IP :: "octets \<Rightarrow> nat" where
  "PKCS1_OS2IP X = octets_to_nat X" 

subsection \<open>Data Conversion Lemmas\<close>

lemma octet_len_I2OSP_inputValid1: 
  assumes "(octet_length x \<le> xLen)" 
  shows   "(PKCS1_I2OSP_inputValid x xLen)"
  by (metis PKCS1_I2OSP_inputValid_def assms leD leI nat_lowbnd_word_len2 Twoto8 zero_less_numeral)

lemma octet_len_I2OSP_inputValid2: 
  assumes "(PKCS1_I2OSP_inputValid x xLen)" 
  shows   "(octet_length x \<le> xLen)"
  using PKCS1_I2OSP_inputValid_def assms nat_bnd_word_len2 Twoto8 zero_less_numeral by presburger

lemma I2OSP_valid_len:
  assumes "PKCS1_I2OSP_inputValid x xLen"
  shows   "length (PKCS1_I2OSP x xLen) = xLen" 
  using assms PKCS1_I2OSP_inputValid_def PKCS1_I2OSP_def nat_to_words_len_upbnd Twoto8 
        zero_less_numeral by algebra

lemma I2OSP_OS2IP: "PKCS1_OS2IP (PKCS1_I2OSP x xLen) = x"
  using PKCS1_I2OSP_inputValid_def PKCS1_I2OSP_def PKCS1_OS2IP_def nat_to_words_len_to_nat
        zero_less_numeral by force

lemma I2OSP_octets_valid: "octets_valid (PKCS1_I2OSP x xLen)"
  using words_valid_def PKCS1_I2OSP_def nat_to_words_len_valid by presburger

lemma OS2IP_I2OSP: 
  assumes "octets_valid os" 
  shows   "PKCS1_I2OSP (PKCS1_OS2IP os) (length os) = os"
  by (metis assms PKCS1_I2OSP_def PKCS1_OS2IP_def words_valid_def words_to_nat_to_words_len) 


section \<open>Section 5: Cryptographic Primitives\<close>

subsection \<open>Section 5.1: Encryption and Decryption Primitives\<close>

named_theorems RSAprims

subsubsection \<open>Section 5.1.1: Encryption Primitives\<close>

definition PKCS1_RSAEP_messageValid :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  [RSAprims]: "PKCS1_RSAEP_messageValid n m = (m < n)" 

definition PKCS1_RSAEP :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  [RSAprims]: "PKCS1_RSAEP n e m = (m ^ e) mod n"

subsubsection \<open>Section 5.1.2: Decryption Primitives\<close>

abbreviation PKCS1_RSADP_ciphertextValid :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  "PKCS1_RSADP_ciphertextValid n c \<equiv> PKCS1_RSAEP_messageValid n c"

abbreviation PKCS1_RSADP :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "PKCS1_RSADP n d c \<equiv> PKCS1_RSAEP n d c"

abbreviation PKCS1_RSADP_CRT_ciphertextValid :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "PKCS1_RSADP_CRT_ciphertextValid p q c \<equiv> PKCS1_RSADP_ciphertextValid (p*q) c"

definition PKCS1_RSADP_CRT :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  [RSAprims]: "PKCS1_RSADP_CRT p q dP dQ qInv c = 
   (let m1 = int ((c ^ dP) mod p);
        m2 = int ((c ^ dQ) mod q);
        h  = (m1 - m2)*qInv mod p 
    in
        nat ( m2 + (q*h) )
   )" 

subsubsection \<open>RSA Encryption/Decryption Lemmas\<close>

named_theorems RSAprimsThms

lemma encryptValidCiphertext: 
  assumes "0 < n"
  shows   "PKCS1_RSADP_ciphertextValid n (PKCS1_RSAEP n e m)"
  using assms RSAprims(1,2) by auto 

lemma encryptValidCiphertext2: 
  assumes "PKCS1_validRSApublicKey n e p q"
  shows   "PKCS1_RSADP_ciphertextValid n (PKCS1_RSAEP n e m)"
  using assms RSAprims(1,2) n_positive2 by auto

lemma encryptValidI2OSP:
  assumes "k = octet_length n"  "c = PKCS1_RSAEP n e m"  "0 < n"
  shows   "PKCS1_I2OSP_inputValid c k"
  using PKCS1_RSAEP_messageValid_def assms encryptValidCiphertext less_imp_le_nat 
        octet_len_I2OSP_inputValid1 word_len_mono by presburger

lemma encryptValidI2OSP2:
  assumes "k = octet_length n"  "c = PKCS1_RSAEP n e m"  "PKCS1_validRSApublicKey n e p q"
  shows   "PKCS1_I2OSP_inputValid c k"
  using assms RSAprims(1,2) n_positive2 encryptValidI2OSP by auto

lemma decryptCRTmessageValid_h:
  fixes   n p q     :: nat
  and     m1 m2 h m :: int
  assumes "0 < n"  "n = p*q"  "m1 = int ((c ^ dP) mod p)"  "m2 = int ((c ^ dQ) mod q)"
          "h  = (m1 - m2)*qInv mod p"  "m  = m2 + (q*h)" 
  shows   "m < n \<and> 0 \<le> m"
proof - 
  have p0: "0 < p"     using assms(1,2) by simp
  have q0: "0 < q"     using assms(1,2) by simp
  have 1: "m2 \<le> q-1"   by (simp add: assms(4) q0 pos_mod_bound Suc_leI of_nat_diff) 
  have 2: "h < p"      by (metis assms(5) p0 pos_mod_bound of_nat_0_less_iff) 
  have 20: "h \<le> p-1"   using 2 by auto
  have 3: "m \<le> (q-1) + q*h"         using 1 assms(6) by linarith
  have 4: "q*h \<le> q*(p-1)"           using q0 20 by auto
  have 5: "m \<le> (q-1) + q*(p-1)"     using 3 4 by linarith
  have 6: "q*(p-1) = q*p - q"       by (simp add: diff_mult_distrib2) 
  have 7: "m \<le> (q - 1) + (q*p - q)" using 5 6 by argo
  have 8: "m \<le> (q - q) + (q*p - 1)" using 7
    by (metis (no_types, opaque_lifting) Nat.add_diff_assoc2 One_nat_def Suc_leI add.commute 
           assms(1,2) mult.right_neutral mult_le_mono2 nat_0_less_mult_iff) 
  have 9: "m \<le> 0 + q*p - 1"        using 8 by fastforce
  have    "m \<le> n - 1"              using assms(2) 9 by (metis mult.commute plus_nat.add_0) 
  then have a1: "m < n"            using assms(1) by linarith      
  have      a2: "0 \<le> m"            using p0 assms(4,5,6) by simp
  show ?thesis  using a1 a2 by simp
qed

lemma decryptCRTmessageValid:
  assumes "0 < n" "n = p*q"
  shows   "PKCS1_RSAEP_messageValid n (PKCS1_RSADP_CRT p q dP dQ qInv c)"
proof - 
  let ?m1 = "int ((c ^ dP) mod p)"
  let ?m2 = "int ((c ^ dQ) mod q)" 
  let ?h  = "(?m1 - ?m2)*qInv mod p"
  let ?m  = "?m2 + (q*?h)" 
  have a1: "?m < n \<and> 0 \<le> ?m"  using assms decryptCRTmessageValid_h by blast
  have a2: "(nat ?m) < n"     using a1 assms(1) by linarith
  have a3: "nat ?m = PKCS1_RSADP_CRT p q dP dQ qInv c"  using PKCS1_RSADP_CRT_def by metis
  show ?thesis using a2 a3 PKCS1_RSAEP_messageValid_def by algebra
qed

lemma decryptCRTmessageValid2:
  assumes "PKCS1_validRSAprivateKey_CRT p q dP dQ qInv e"  "n = p*q"
  shows   "PKCS1_RSAEP_messageValid n (PKCS1_RSADP_CRT p q dP dQ qInv c)"
  by (metis assms decryptCRTmessageValid ValidKeyDefs(1,3) bot_nat_0.not_eq_extremum 
            less_nat_zero_code) 

lemma RSAEP_RSADP_onePrime_p:
  assumes "PKCS1_validRSAprivateKey n d p q e"
  shows   "[m^(e*d) = m] (mod p)"
proof - 
  let ?l = "lcm (p-1) (q-1)"
  obtain lp where lp: "lp*(p-1) = ?l" using dvd_div_mult_self by blast 
  obtain lq where lq: "lq*(q-1) = ?l" using dvd_div_mult_self by blast 
  have 1: "e*d mod ?l = 1"            using assms PKCS1_validRSAprivateKey_def by algebra
  obtain c where c0: "e*d = 1 + c*?l" 
    by (metis 1 Nat.add_0_right Suc_eq_plus1_left add_Suc_right div_mod_decomp) 
  let ?cp = "c*lp"
  let ?cq = "c*lq"
  have c1: "?cp*(p-1) = c*?l"    using lp by force
  have c2: "?cq*(q-1) = c*?l"    using lq by force 
  have p1: "e*d = 1 + ?cp*(p-1)" using c0 c1 by presburger
  show ?thesis  
  proof (cases)
    assume "m mod p = 0" 
    then show ?thesis 
    by (metis cong_def add_gr_0 c0 dvd_imp_mod_0 dvd_power dvd_trans mod_0_imp_dvd zero_less_one)
  next
    assume "m mod p \<noteq> 0"
    then have p201: "coprime m p" 
      by (meson assms ValidKeyDefs(1,2) coprime_commute dvd_imp_mod_0 prime_imp_coprime) 
    have p202: "totient p = (p-1)"  using ValidKeyDefs(1,2) assms totient_prime by algebra
    have p203: "[m^(p-1) = 1] (mod p)"          by (metis p201 p202 euler_theorem) 
    have      "m^(e*d) = m^(1 + ?cp*(p-1))"     using p1 by presburger
    then have "m^(e*d) = m * m ^(?cp*(p-1))"    by force
    then have "m^(e*d) = m * (m^(p-1))^?cp"     by (metis mult.commute power_mult) 
    then have "[m^(e*d) = m * (1)^?cp] (mod p)" by (metis p203 cong_pow cong_scalar_left) 
    then show ?thesis by force
  qed
qed

lemma RSAEP_RSADP_onePrime_q:
  assumes "PKCS1_validRSAprivateKey n d p q e"
  shows   "[m^(e*d) = m] (mod q)"
  using assms validPrivateKey_pq_symm RSAEP_RSADP_onePrime_p by fast

lemma simple_CRT:
  assumes "prime (p::nat)"  "prime q"  "p \<noteq> q"  "[a = b] (mod p)"  "[a = b] (mod q)"
  shows   "[a = b] (mod p*q)"
  by (simp add: assms coprime_cong_mult_nat primes_coprime)

lemma simple_CRT_int:
  assumes "prime (p::nat)"  "prime q"  "p \<noteq> q"  "[(a::int) = (b::nat)] (mod p)"  
          "[a = b] (mod q)"  "0 \<le> a"
  shows   "[a = b] (mod p*q)"
  by (metis assms cong_int_iff simple_CRT zero_le_imp_eq_int)

text\<open>The first of 4 "inverse" theorems.  Here, if you start with a valid message and a valid key,
if you encrypt the message and ("plainly") decrypt the resulting ciphertext, you will get back
the original message.\<close>
lemma RSAEP_RSADP [RSAprimsThms]:
  assumes "PKCS1_RSAEP_messageValid n m"  "PKCS1_validRSAprivateKey n d p q e"
  shows   "PKCS1_RSADP n d (PKCS1_RSAEP n e m) = m" 
proof - 
  have p: "[m^(e*d) = m] (mod p)" using assms(2) RSAEP_RSADP_onePrime_p by auto
  have q: "[m^(e*d) = m] (mod q)" using assms(2) RSAEP_RSADP_onePrime_q by auto
  have n: "[m^(e*d) = m] (mod n)" by (metis p q assms(2) ValidKeyDefs(1,2) simple_CRT)
  show ?thesis  by (metis n assms(1) RSAprims(1,2) cong_def mod_less power_mod power_mult) 
qed

text\<open>This is the second of the 4 inverse theorems.  Here we start with a valid ciphertext and
a valid key.  If we decrypt the ciphertext and encrypt the resulting plaintext, we will get back
the original ciphertext.  This is a direct result of the 1st inverse theorem because for RSA, the
plain decryption function is equal to the encryption function.\<close>
lemma RSADP_RSAEP [RSAprimsThms]:
  assumes "PKCS1_RSADP_ciphertextValid n c" "PKCS1_validRSAprivateKey n d p q e"
  shows   "PKCS1_RSAEP n e (PKCS1_RSADP n d c) = c" 
  by (metis assms RSAEP_RSADP PKCS1_RSAEP_def mult.commute power_mod power_mult) 

text\<open>As noted above, the value of the decryption exponent d is only unqiue modulo l.  In the case
that we have two valid RSA keys where only the ds are different, using either key will result in
the same values when decrypting.\<close>
lemma RSADP_equiv_d [RSAprimsThms]:
  assumes "PKCS1_validRSAprivateKey n d1 p q e" "PKCS1_validRSAprivateKey n d2 p q e"
  shows   "PKCS1_RSADP n d1 c = PKCS1_RSADP n d2 c"
  by (smt (verit, ccfv_SIG) assms RSAprims(1,2) ValidKeyDefs(2) RSADP_RSAEP RSAEP_RSADP 
       le_eq_less_or_eq less_le_trans mod_less_divisor power_mod) 

lemma fermat2: 
  assumes "prime p"  "\<not> p dvd a"
  shows "a^b mod p = a^(b mod (p-1)) mod p"
proof - 
  let ?pm1 = "p-1" 
  let ?x = "(b div ?pm1)"
  let ?y = "(b mod ?pm1)" 
  have 1: "b = ?x*?pm1 + ?y" by presburger
  have 2: "a^?pm1 mod p = 1" by (metis assms fermat_theorem cong_def mod_less prime_nat_iff)
  have 3: "a^b = ((a^?pm1)^?x)*a^?y"             by (metis 1 mult.commute power_add power_mult)
  have 4: "a^b mod p = ((a^?pm1)^?x)*a^?y mod p" using 3 by presburger
  have 5: "a^b mod p = ((1)^?x)*a^?y mod p"      by (metis 2 4 mod_mult_cong power_mod)
  have 6: "a^b mod p = (1)*a^?y mod p"           using 5 by force
  then show ?thesis                              by fastforce
qed

text\<open>In section 3 we saw how to convert a valid RSA key for "plain" decryption into a valid RSA
key for CRT decryption.  Here we show that those keys are equivalent (result in the same plaintext)
when using the appropriate decryption primitive.\<close>
lemma RSADP_CRT_equiv1 [RSAprimsThms]:
  assumes "PKCS1_validRSAprivateKey n d p q e"  "(q*qInv mod p = 1)" 
          "dP = d mod (p-1)"  "dQ = d mod (q-1)" 
  shows   "PKCS1_RSADP n d c = PKCS1_RSADP_CRT p q dP dQ qInv c" 
proof - 
  let ?m1 = "int ((c ^ dP) mod p)" 
  let ?m2 = "int ((c ^ dQ) mod q)"
  let ?h  = "((?m1 - ?m2)*qInv) mod p" 
  let ?m  = "?m2 + (q*?h)"
  have n0: "0 < n"   using n_positive2 assms(1) ValidKeyDefs(1,2) by meson
  have n1: "n = p*q" using assms(1) ValidKeyDefs(1,2) by algebra
  have r0: "nat ?m = PKCS1_RSADP_CRT p q dP dQ qInv c" using PKCS1_RSADP_CRT_def by metis
  have r1: "0 \<le> ?m"  using decryptCRTmessageValid_h n0 n1 by blast
  have r2: "?m < n"  using decryptCRTmessageValid_h n0 n1 by blast
  have r3: "(nat ?m) < n"            using r1 r2 by linarith 
  have r4: "(nat ?m) mod n = nat ?m" using r1 r3 by force 
  let ?a = "c^d mod n"
  have a0: "PKCS1_RSADP n d c = ?a"  using PKCS1_RSAEP_def by meson
  have q1: "[?m = ?m2] (mod q)"      using cong_def mod_mult_self2 by blast 
  have q2: "[?m2 = ?a] (mod q)"
  proof - 
    have 1: "q dvd n"                using assms(1) ValidKeyDefs(1,2) by simp
    have 2: "?a mod q = c^d mod q"   using 1 mod_mod_cancel by blast 
    have 3: "prime q"                using assms(1) ValidKeyDefs(1,2) by algebra
    have 4: "c^d mod q = c^(d mod (q-1)) mod q"
      by (metis 3 PKCS1_validRSAprivateKey_def assms(1) dQ_from_d dvd_imp_mod_0 dvd_power 
           dvd_trans fermat2)
    have 5: "c^d mod q = c^dQ mod q" using 4 assms(4) by blast
    then show ?thesis by (metis (no_types, lifting) 2 5 cong_def cong_mod_left of_nat_mod) 
  qed
  have q3: "[?m = ?a] (mod q)"       using q1 q2 cong_trans by blast 
  have p1: "[?m = ?m1] (mod p)" 
  proof - 
   have "[?m = ?m2 + q*((?m1 - ?m2)*qInv)] (mod p)"
     by (meson cong_add_lcancel cong_def mod_mult_right_eq) 
   then have "[?m = ?m2 + (?m1-?m2)*q*qInv] (mod p)"
     by (simp add: mult.assoc mult.left_commute)
   then have 1: "[?m = ?m2 + (?m1-?m2)*(q*qInv)] (mod p)"
     by (simp add: mult.assoc)
   have "[(?m1-?m2)*(q*qInv) = (?m1-?m2)*1] (mod p)" 
     by (metis assms(2) cong_mod_right cong_refl cong_scalar_right mult.commute of_nat_1 of_nat_mod)
   then have "[(?m1-?m2)*(q*qInv) = ?m1-?m2] (mod p)" by fastforce 
   then have "[?m = ?m2 + ?m1 - ?m2] (mod p)" 
     by (smt (verit) 1 cong_add_lcancel cong_def mod_mult_right_eq of_nat_1 of_nat_mod 
           add_diff_cancel_left' diff_add_cancel) 
   then show ?thesis by simp
  qed
  have p2: "[?m1 = ?a] (mod p)"
    by (smt (verit) ValidKeyDefs(1,2) assms(1,3) cong_def dP_from_d dvd_imp_mod_0 dvd_power 
    dvd_trans dvd_triv_right fermat2 mod_mod_cancel mod_mod_trivial mult.commute of_nat_mod)
  have p3: "[?m = ?a] (mod p)" using p1 p2 cong_trans by blast
  have a2: "[?m = ?a] (mod n)" using r1 q3 p3 assms(1) ValidKeyDefs(1,2) simple_CRT_int by algebra
  have a3: "?a < n"
    by (metis ValidKeyDefs(2) assms(1) gr_implies_not_zero mod_less_divisor neq0_conv) 
  have a4: "?a mod n = ?a"     using a3 by auto
  have a5: "?a mod n = (nat ?m) mod n" 
    by (metis r1 a2 cong_def nat_int nat_mod_distrib of_nat_0_le_iff r1)
  have a6: "?a = nat ?m"       using a4 a5 r4 by argo
  show ?thesis                 using a6 r0 a0 by argo
qed

text\<open>In section 3 we saw how to convert a valid RSA key for CRT decryption into a valid RSA
key for "plain" decryption.  Here we show that those keys are equivalent (result in the same 
plaintext) when using the appropriate decryption primitive.\<close>
lemma RSADP_CRT_equiv2 [RSAprimsThms]:
  assumes "PKCS1_validRSAprivateKey_CRT p q dP dQ qInv e"  "d = d_from_dP_dQ dP dQ p q"  "n=p*q"
  shows   "PKCS1_RSADP n d c = PKCS1_RSADP_CRT p q dP dQ qInv c"
  by (metis (no_types, opaque_lifting) PKCS1_validRSAprivateKey_CRT_def RSADP_CRT_equiv1 assms 
     dP_dQ_unique validPrivateCRTKey_to_validPrivateKey validPrivateKey_to_validPrivateCRTkey)

text\<open>We end this section with the final 2 of the 4 inverse theorems.  These show that the RSA
decryption operation using the Chinese Remainder Theorem is an inverse function of the RSA
encryption (in either order.)\<close>
lemma RSAEP_RSADP_CRT [RSAprimsThms]:
  assumes "PKCS1_RSAEP_messageValid n m"  "PKCS1_validRSAprivateKey_CRT p q dP dQ qInv e"  "n=p*q"
  shows   "PKCS1_RSADP_CRT p q dP dQ qInv (PKCS1_RSAEP n e m) = m"
  by (metis RSADP_CRT_equiv2 RSAEP_RSADP assms validPrivateCRTKey_to_validPrivateKey) 

lemma RSADP_CRT_RSAEP [RSAprimsThms]:
  assumes "PKCS1_RSADP_ciphertextValid n c"  "PKCS1_validRSAprivateKey_CRT p q dP dQ qInv e"
          "n=p*q"
  shows   "PKCS1_RSAEP n e (PKCS1_RSADP_CRT p q dP dQ qInv c) = c"
  by (metis RSADP_CRT_equiv2 RSADP_RSAEP assms validPrivateCRTKey_to_validPrivateKey) 
  

subsection \<open>Section 5.2: RSA Signature/Verification Primitives\<close>

text \<open>"The main mathematical operation in each primitive is exponentiation, as in the encryption
and decryption primitives of Section 5.1. RSASP1 and RSAVP1 are the same as RSADP and RSAEP except
for the names of their input and output arguments; they are distinguished as they are intended
for different purposes." 

Because the signature primitives are simply aliases of the encryption primitives, there are no
lemmas in this subsection.\<close>

subsubsection \<open>Section 5.2.1: Signature Primitives\<close>

abbreviation PKCS1_RSASP1 :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "PKCS1_RSASP1 n d m \<equiv> PKCS1_RSADP n d m"

abbreviation PKCS1_RSASP1_CRT :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "PKCS1_RSASP1_CRT p q dP dQ qInv m \<equiv> PKCS1_RSADP_CRT p q dP dQ qInv m"

subsubsection \<open>Section 5.2.2: Verification Primitive\<close>

abbreviation PKCS1_RSAVP1 :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "PKCS1_RSAVP1 n e s \<equiv> PKCS1_RSAEP n e s" 


section \<open>Section 7: Encryption Schemes\<close>

text \<open>"For the purposes of this document, an encryption scheme consists of an encryption operation
and a decryption operation, where the encryption operation produces a ciphertext from a message 
with a recipient's RSA public key, and the decryption operation recovers the message from the 
ciphertext with the recipient's corresponding RSA private key.

An encryption scheme can be employed in a variety of applications.  A typical application is a key
establishment protocol, where the message contains key material to be delivered confidentially from
one party to another.  For instance, PKCS #7 employs such a protocol to deliver a content-
encryption key from a sender to a recipient; the encryption schemes defined here would be suitable
key-encryption algorithms in that context. 

Two encryption schemes are specified in this document: RSAES-OAEP and RSAES-PKCS1-v1_5.  RSAES-OAEP
is required to be supported for new applications; RSAES-PKCS1-v1_5 is included only for
compatibility with existing applications. 

The encryption schemes given here follow a general model similar to that employed in IEEE 1363-2000
combining encryption and decryption primitives with an encoding method for encryption. The 
encryption operations apply a message encoding operation to a message to produce an encoded message
which is then converted to an integer message representative.  An encryption primitive is applied
to the message representative to produce the ciphertext. Reversing this, the decryption operations
apply a decryption primitive to the ciphertext to recover a message representative, which is then 
converted to an octet string encoded message. A message decoding operation is applied to the 
encoded message to recover the message and verify the correctness of the decryption." \<close>

subsection \<open>Section 7.1.1: RSAES-OAEP\<close>

text \<open>In this locale, we fix a mask generating function MGF.  We also fix a hash function, with 
with output length hLen.  The only place that the hash function is used is to hash the (optional) 
label L to get lHash.  When a label is not provided, a default lHash value is used.  These default
lHash values may be found below.

Moreover, we abstract away the underlying RSA primitives for encryption and decryption.  We do this
to elide over the two options for decryption.  We only need to know that the output of either
encryption or decryption is less than the modulus n and that in either order, these two functions
are inverses of each other.  We have proven these facts above for both "plain" RSA decryption and
decryption using the Chinese Remainder Theorem. 
\<close>

locale OAEP = 
  fixes MGF   :: mgf_type
    and Hash  :: hash_type
    and hLen  :: nat
    and RSAENCRYPT RSADECRYPT :: "nat \<Rightarrow> nat"
    and n     :: nat
assumes mgf_valid:   "\<forall>x y. octets_valid (MGF x y)"
    and mgf_len:     "\<forall>x y. length (MGF x y) = y"
    and hash_valid:  "\<forall>x. octets_valid (Hash x)"
    and hash_len :   "\<forall>x. length (Hash x) = hLen" 
    and RSA_npos:    "0 < n"
    and RSA_bnd:     "\<forall>m. (RSAENCRYPT m) < n" 
                     "\<forall>c. (RSADECRYPT c) < n"
    and RSA_inv:     "\<forall>m. (m < n) \<longrightarrow> RSADECRYPT (RSAENCRYPT m) = m" 
                     "\<forall>c. (c < n) \<longrightarrow> RSAENCRYPT (RSADECRYPT c) = c"
begin

named_theorems OAEPdefs
named_theorems OAEPthms

definition k where "k = octet_length n" 

subsubsection \<open>Section 7.1.1: Encryption Operation\<close>
text\<open>
RSAES-OAEP-ENCRYPT ((n, e), M, L) 
"Options: Hash   hash function (hLen denotes the length in octets of the hash function output)
          MGF    mask generation function 
 Input:  (n, e)  recipient's RSA public key (k denotes the length in octets of the RSA modulus n)
          M      message to be encrypted, an octet string of length mLen,  
                 where  mLen\<le>k – 2hLen – 2
          L      optional label to be associated with the message; the default value for L, if L is
                 not provided, is the empty string
 Output:  C      ciphertext, an octet string of length k"
Notes:
 - The only place that Hash is used in RSAES_OAEP_Encrypt is to hash the label L to get lHash.
   When no label L is given there are default values for lHash.
 - Not listed as an input in the standard, the RSA-OAEP-ENCRYPT operation requires a random nonce
   called seed. From step d of the operations, the standard requires you to: "Generate a random 
   octet string seed of length hLen."  The seed could be the output of Hash, but the standard does
   not insist on that.  In any case, we include seed in the list of inputs to RSAES-OAEP-ENCRYPT.
\<close>

definition PKCS1_OAEP_PS :: "nat \<Rightarrow> octets" where
  "PKCS1_OAEP_PS mLen = replicate (k - mLen - (2*hLen) - 2) 0"

definition PKCS1_OAEP_DB :: "octets \<Rightarrow> octets \<Rightarrow> octets \<Rightarrow> octets" where
  "PKCS1_OAEP_DB lHash PS M = lHash @ PS @ [1] @ M"

definition PKCS1_OAEP_dbMask :: "octets \<Rightarrow> octets" where 
  "PKCS1_OAEP_dbMask seed = MGF seed (k - hLen - 1)"

definition PKCS1_OAEP_maskedDB :: "octets \<Rightarrow> octets \<Rightarrow> octets" where
  "PKCS1_OAEP_maskedDB DB dbMask = xor_octets DB dbMask"

definition PKCS1_OAEP_seedMask :: "octets \<Rightarrow> octets" where 
  "PKCS1_OAEP_seedMask maskedDB = MGF maskedDB hLen"

definition PKCS1_OAEP_maskedSeed :: "octets \<Rightarrow> octets \<Rightarrow> octets" where
  "PKCS1_OAEP_maskedSeed seed seedMask = xor_octets seed seedMask"

definition PKCS1_OAEP_EM :: "octets \<Rightarrow> octets \<Rightarrow> octets" where
  "PKCS1_OAEP_EM maskedSeed maskedDB  = [0] @ maskedSeed @ maskedDB"

definition PKCS1_RSAES_OAEP_Encrypt_lengthValid :: "nat \<Rightarrow> bool" where
  [OAEPdefs]: "PKCS1_RSAES_OAEP_Encrypt_lengthValid mLen \<equiv> (mLen + 2*hLen + 2 \<le> k)" 

definition PKCS1_RSAES_OAEP_Encrypt :: "octets \<Rightarrow> octets \<Rightarrow> octets \<Rightarrow> octets" where
  [OAEPdefs]: "PKCS1_RSAES_OAEP_Encrypt M L seed =
  ( let mLen       = length M; 
        lHash      = Hash L;
        PS         = PKCS1_OAEP_PS mLen;
        DB         = PKCS1_OAEP_DB lHash PS M;
        dbMask     = PKCS1_OAEP_dbMask seed;
        maskedDB   = PKCS1_OAEP_maskedDB DB dbMask;
        seedMask   = PKCS1_OAEP_seedMask maskedDB;
        maskedSeed = PKCS1_OAEP_maskedSeed seed seedMask;
        EM         = PKCS1_OAEP_EM maskedSeed maskedDB;
        m          = PKCS1_OS2IP EM;
        c          = RSAENCRYPT m 
    in  PKCS1_I2OSP c k )"

text \<open>We write down simple lemmas for each of the intermediate values in the OAEP encoding.\<close>

lemma OAEP_PS_len: "length (PKCS1_OAEP_PS mLen) = k - mLen - 2*hLen - 2"
  using PKCS1_OAEP_PS_def by force

lemma OAEP_PS_octetsValid: "octets_valid (PKCS1_OAEP_PS mLen)"
  using words_valid_def PKCS1_OAEP_PS_def by force

lemma OAEP_DB_len:
  assumes "PKCS1_RSAES_OAEP_Encrypt_lengthValid mLen" 
          "DB = PKCS1_OAEP_DB lHash PS M"
          "length lHash = hLen" 
          "length PS    = k - mLen - 2*hLen - 2" 
          "length M     = mLen"
  shows   "length DB    = k - hLen - 1" 
proof - 
  have 1: "mLen + 2*hLen + 2 \<le> k" 
    using assms(1) OAEPdefs(1) by fast
  have 2: "length DB = hLen + (k - mLen - 2*hLen - 2) + 1 + mLen" 
    using PKCS1_OAEP_DB_def assms(2,3,4,5) by simp 
  show ?thesis using 1 2 by force
qed

lemma OAEP_DB_octetsValid:
  assumes "DB = PKCS1_OAEP_DB lHash PS M" 
          "octets_valid lHash" 
          "octets_valid PS"
          "octets_valid M"
  shows   "octets_valid DB" 
  using assms PKCS1_OAEP_DB_def words_valid_concat words_valid_cons by fastforce

lemma OAEP_dbMask_len: "length (PKCS1_OAEP_dbMask seed) = k - hLen - 1"  
  using PKCS1_OAEP_dbMask_def mgf_len by simp

lemma OAEP_dbMask_octetsValid: "octets_valid (PKCS1_OAEP_dbMask seed)"
  using PKCS1_OAEP_dbMask_def mgf_valid by presburger

lemma OAEP_maskedDB_len:
  assumes "maskedDB = PKCS1_OAEP_maskedDB DB dbMask"
          "length DB       = x" 
          "length dbMask   = x" 
  shows   "length maskedDB = x"
  by (simp add: PKCS1_OAEP_maskedDB_def assms xor_words_length) 

lemma OAEP_maskedDB_octetsValid:
  assumes "maskedDB = PKCS1_OAEP_maskedDB DB dbMask"
          "octets_valid DB" 
          "octets_valid dbMask" 
  shows   "octets_valid maskedDB"
  by (simp add: assms xor_valid_words PKCS1_OAEP_maskedDB_def)

lemma OAEP_seedMask_len:
  assumes "seedMask = PKCS1_OAEP_seedMask maskedDB"
  shows   "length seedMask = hLen"
  using assms PKCS1_OAEP_seedMask_def mgf_len by auto

lemma OAEP_seedMask_octetsValid:
  assumes "seedMask = PKCS1_OAEP_seedMask maskedDB"
  shows   "octets_valid seedMask" 
  using assms PKCS1_OAEP_seedMask_def mgf_valid by presburger

lemma OAEP_maskedSeed_len:
  assumes "maskedSeed = PKCS1_OAEP_maskedSeed seed seedMask"
          "length seedMask   = hLen"  "length seed = hLen" 
  shows   "length maskedSeed = hLen" 
  by (simp add: PKCS1_OAEP_maskedSeed_def assms xor_words_length)

lemma OAEP_maskedSeed_octetsValid:
  assumes "maskedSeed = PKCS1_OAEP_maskedSeed seed seedMask"
          "octets_valid seedMask"  "octets_valid seed"
  shows   "octets_valid maskedSeed" 
  using assms PKCS1_OAEP_maskedSeed_def xor_valid_words by presburger

lemma OAEP_EM_octetsValid:
  assumes "EM = PKCS1_OAEP_EM maskedSeed maskedDB" 
          "octets_valid maskedSeed"  "octets_valid maskedDB" 
  shows   "octets_valid EM"
  using PKCS1_OAEP_EM_def assms words_valid_def by fastforce

lemma OAEP_EM_len:
  assumes "PKCS1_RSAES_OAEP_Encrypt_lengthValid mLen"  "EM = PKCS1_OAEP_EM maskedSeed maskedDB"
          "length maskedSeed = hLen"  "length maskedDB   = k - hLen - 1" 
  shows   "length EM = k"
proof - 
  have "mLen + 2*hLen + 2 \<le> k" using assms(1) OAEPdefs(1) by auto
  then have "hLen + 1 \<le> k"     by linarith
  then show ?thesis            using assms(2,3,4) PKCS1_OAEP_EM_def by force
qed

lemma OAEP_EM_strip0_len:
  assumes "EM = PKCS1_OAEP_EM maskedSeed maskedDB"  "length EM = k"
  shows   "length (words_strip_zero EM) \<le> k - 1"
  by (metis PKCS1_OAEP_EM_def append.simps(2) assms length_tl list.sel(1) 
            words_strip_zero.simps(2) strip_zero_length)

lemma OAEP_m_less_n:
  assumes "length (words_strip_zero EM) \<le> k - 1"  "octets_valid EM"  "m = PKCS1_OS2IP EM"
  shows   "m < n"
proof - 
  have 1: "256^(k-1) \<le> n" 
    by (metis RSA_npos k_def word_length_eq3 Twoto8 zero_less_numeral) 
  have 2: "octets_to_nat EM < 256^(k-1)" 
    by (metis assms(1,2) words_strip0_to_nat_len_bnd2 words_valid_def Twoto8)
  show ?thesis 
    using 1 2 PKCS1_OS2IP_def assms(3) by force
qed


subsubsection \<open>Section 7.1.2: Decryption Operation\<close>
text\<open> "RSAES-OAEP-DECRYPT (K, C, L)
 Options: Hash  hash function (hLen denotes the length in octets of the hash function output)
          MGF   mask generation function
 Input:   K     recipient's RSA private key (k denotes the length in octets of the RSA modulus n)
          C     ciphertext to be decrypted, an octet string of length k, where  k\<ge> 2hLen + 2
          L     optional label whose association with the message is to be verified;
                the default value for L, if L is not provided, is the empty string
Output:   M     message, an octet string of length mLen, where mLen\<le>k – 2hLen – 2"
\<close>

definition PKCS1_OAEP_decode_Y :: "octets \<Rightarrow> nat" where
  "PKCS1_OAEP_decode_Y EM = hd EM"

definition PKCS1_OAEP_decode_maskedSeed :: "octets \<Rightarrow> octets" where
  "PKCS1_OAEP_decode_maskedSeed EM = take hLen (drop 1 EM)"

definition PKCS1_OAEP_decode_maskedDB :: "octets \<Rightarrow> octets" where
  "PKCS1_OAEP_decode_maskedDB EM = drop (1 + hLen) EM" 

definition PKCS1_OAEP_decode_seedMask :: "octets \<Rightarrow> octets" where
  "PKCS1_OAEP_decode_seedMask maskedDB = MGF maskedDB hLen"

definition PKCS1_OAEP_decode_seed :: "octets \<Rightarrow> octets \<Rightarrow> octets" where 
  "PKCS1_OAEP_decode_seed maskedSeed seedMask = xor_octets maskedSeed seedMask"

definition PKCS1_OAEP_decode_dbMask :: "octets \<Rightarrow> octets" where 
  "PKCS1_OAEP_decode_dbMask seed = MGF seed (k - hLen - 1)"

definition PKCS1_OAEP_decode_DB :: "octets \<Rightarrow> octets \<Rightarrow> octets" where 
  "PKCS1_OAEP_decode_DB maskedDB dbMask = xor_octets maskedDB dbMask"

text \<open>"Separate DB into an octet string lHash' of length hLen, a (possibly empty) padding string
PS consisting of octets with hexadecimal value 0x00, and a message M as 
      DB = lHash' || PS || 0x01 || M .
If there is no octet with hexadecimal value 0x01 to separate PS from M, if lHash does not equal
lHash', or if Y is nonzero, output ``decryption error'' and stop."\<close>

definition PKCS1_OAEP_decode_lHash :: "octets \<Rightarrow> octets" where
  "PKCS1_OAEP_decode_lHash DB = take hLen DB"

definition PKCS1_OAEP_decode_validPS :: "octets \<Rightarrow> bool" where
  "PKCS1_OAEP_decode_validPS DB \<equiv>
  (let PS_0x01_M = drop hLen DB;
          Ox01_M = words_strip_zero PS_0x01_M
   in
      (Ox01_M \<noteq> []) \<and> (Ox01_M ! 0 = 1)
  )"

definition PKCS1_OAEP_decode_PSlen :: "octets \<Rightarrow> nat" where
  "PKCS1_OAEP_decode_PSlen DB =
  (let PS_0x01_M = drop hLen DB;
          Ox01_M = words_strip_zero PS_0x01_M;
       tl        = length PS_0x01_M;
       sl        = length    Ox01_M
   in
      tl - sl
  )"

definition PKCS1_OAEP_decode_M :: "octets \<Rightarrow> octets" where
  "PKCS1_OAEP_decode_M DB =  drop 1 (words_strip_zero (drop hLen DB))"

definition PKCS1_RSAES_OAEP_Decrypt_validInput :: "octets \<Rightarrow> octets \<Rightarrow> bool" where
  [OAEPdefs]: "PKCS1_RSAES_OAEP_Decrypt_validInput C lHash \<equiv> 
  ( let c          = PKCS1_OS2IP C;
        m          = RSADECRYPT c;
        EM         = PKCS1_I2OSP m k;
        Y          = PKCS1_OAEP_decode_Y EM;
        maskedSeed = PKCS1_OAEP_decode_maskedSeed EM;
        maskedDB   = PKCS1_OAEP_decode_maskedDB EM;
        seedMask   = PKCS1_OAEP_decode_seedMask maskedDB;
        seed       = PKCS1_OAEP_decode_seed maskedSeed seedMask;
        dbMask     = PKCS1_OAEP_decode_dbMask seed;
        DB         = PKCS1_OAEP_decode_DB maskedDB dbMask;
        lHash'     = PKCS1_OAEP_decode_lHash DB
    in (length C = k)   \<and> (2*hLen + 2 \<le> k)  \<and>  (c < n)  \<and>  (Y = 0) \<and> 
       (lHash' = lHash) \<and> (PKCS1_OAEP_decode_validPS DB)
  )"  

definition PKCS1_RSAES_OAEP_Decrypt :: "octets \<Rightarrow> octets" where
  [OAEPdefs]: "PKCS1_RSAES_OAEP_Decrypt C = 
  ( let c          = PKCS1_OS2IP C;
        m          = RSADECRYPT c;
        EM         = PKCS1_I2OSP m k;
        maskedSeed = PKCS1_OAEP_decode_maskedSeed EM;
        maskedDB   = PKCS1_OAEP_decode_maskedDB EM;
        seedMask   = PKCS1_OAEP_decode_seedMask maskedDB;
        seed       = PKCS1_OAEP_decode_seed maskedSeed seedMask;
        dbMask     = PKCS1_OAEP_decode_dbMask seed;
        DB         = PKCS1_OAEP_decode_DB maskedDB dbMask
    in
        PKCS1_OAEP_decode_M DB
  )"

text \<open>At times it is convenient to have direct access to the seed and lHash decoded from a 
ciphertext.  Also it is convenient to have direct access to the routine to check the padding 
string.\<close>
definition PKCS1_RSAES_OAEP_Decrypt_seed :: "octets \<Rightarrow> octets" where
  [OAEPdefs]: "PKCS1_RSAES_OAEP_Decrypt_seed C = 
  ( let c          = PKCS1_OS2IP C;
        m          = RSADECRYPT c;
        EM         = PKCS1_I2OSP m k;
        maskedSeed = PKCS1_OAEP_decode_maskedSeed EM;
        maskedDB   = PKCS1_OAEP_decode_maskedDB EM;
        seedMask   = PKCS1_OAEP_decode_seedMask maskedDB
  in
        PKCS1_OAEP_decode_seed maskedSeed seedMask
  )"

definition PKCS1_RSAES_OAEP_Decrypt_lHash :: "octets \<Rightarrow> octets" where
  [OAEPdefs]: "PKCS1_RSAES_OAEP_Decrypt_lHash C = 
  ( let c          = PKCS1_OS2IP C;
        m          = RSADECRYPT c;
        EM         = PKCS1_I2OSP m k;
        Y          = PKCS1_OAEP_decode_Y EM;
        maskedSeed = PKCS1_OAEP_decode_maskedSeed EM;
        maskedDB   = PKCS1_OAEP_decode_maskedDB EM;
        seedMask   = PKCS1_OAEP_decode_seedMask maskedDB;
        seed       = PKCS1_OAEP_decode_seed maskedSeed seedMask;
        dbMask     = PKCS1_OAEP_decode_dbMask seed;
        DB         = PKCS1_OAEP_decode_DB maskedDB dbMask
    in
        PKCS1_OAEP_decode_lHash DB
  )"

definition PKCS1_RSAES_OAEP_Decrypt_validPS :: "octets \<Rightarrow> bool" where
  [OAEPdefs]: "PKCS1_RSAES_OAEP_Decrypt_validPS C \<equiv> 
  ( let c          = PKCS1_OS2IP C;
        m          = RSADECRYPT c;
        EM         = PKCS1_I2OSP m k;
        maskedSeed = PKCS1_OAEP_decode_maskedSeed EM;
        maskedDB   = PKCS1_OAEP_decode_maskedDB EM;
        seedMask   = PKCS1_OAEP_decode_seedMask maskedDB;
        seed       = PKCS1_OAEP_decode_seed maskedSeed seedMask;
        dbMask     = PKCS1_OAEP_decode_dbMask seed;
        DB         = PKCS1_OAEP_decode_DB maskedDB dbMask
    in (PKCS1_OAEP_decode_validPS DB)
  )"  

text \<open>We write down simple lemmas for each of the intermediate values in the OAEP decoding.\<close>
  
lemma OAEP_decode_EM_octetsValid:
  assumes "EM = PKCS1_I2OSP m k"
  shows   "octets_valid EM"
  by (simp add: I2OSP_octets_valid assms)

lemma OAEP_decode_EM_len:
  assumes "EM = PKCS1_I2OSP m k"  "m < n" 
  shows   "length EM = k"
  by (metis I2OSP_valid_len PKCS1_I2OSP_inputValid_def k_def assms less_trans word_length_eq2 
            Twoto8 zero_less_numeral)
  
lemma OAEP_decode_Y_valid:
  assumes "octets_valid EM"  "Y = PKCS1_OAEP_decode_Y EM"  "0 < length EM"
  shows   "Y < 256"
  using assms words_valid_def PKCS1_OAEP_decode_Y_def by simp

lemma OAEP_decode_maskedSeed_octetsValid:
  assumes "octets_valid EM"  "maskedSeed = PKCS1_OAEP_decode_maskedSeed EM"
  shows   "octets_valid maskedSeed"
  by (metis assms PKCS1_OAEP_decode_maskedSeed_def words_valid_drop words_valid_take)

lemma OAEP_decode_maskedSeed_len:
  assumes "hLen + 1 \<le> length EM"  "maskedSeed = PKCS1_OAEP_decode_maskedSeed EM"
  shows   "length maskedSeed = hLen"
  using assms PKCS1_OAEP_decode_maskedSeed_def by auto

lemma OAEP_decode_maskedDB_octetsValid:
  assumes "octets_valid EM"  "maskedDB = PKCS1_OAEP_decode_maskedDB EM"
  shows   "octets_valid maskedDB"
  by (metis assms PKCS1_OAEP_decode_maskedDB_def words_valid_drop)

lemma OAEP_decode_maskedDB_len:
  assumes "maskedDB = PKCS1_OAEP_decode_maskedDB EM"
  shows   "length maskedDB = (length EM) - 1 - hLen"
  using assms PKCS1_OAEP_decode_maskedDB_def by force

lemma OAEP_decode_seedMask_octetsValid:
  assumes "seedMask = PKCS1_OAEP_decode_seedMask maskedDB"
  shows   "octets_valid seedMask"
  using assms PKCS1_OAEP_decode_seedMask_def mgf_valid by simp

lemma OAEP_decode_seedMask_len:
  assumes "seedMask = PKCS1_OAEP_decode_seedMask maskedDB"
  shows   "length seedMask = hLen"
  using assms PKCS1_OAEP_decode_seedMask_def mgf_len by presburger

lemma OAEP_decode_seed_octetsValid:
  assumes "seed = PKCS1_OAEP_decode_seed maskedSeed seedMask" 
          "octets_valid maskedSeed" "octets_valid seedMask"
  shows   "octets_valid seed"
  using assms PKCS1_OAEP_decode_seed_def xor_valid_words by simp

lemma OAEP_decode_seed_len:
  assumes "seed = PKCS1_OAEP_decode_seed maskedSeed seedMask" 
          "length maskedSeed = hLen" "length seedMask = hLen"
  shows   "length seed = hLen"
  using assms PKCS1_OAEP_decode_seed_def xor_words_length by simp

lemma OAEP_decode_dbMask_octetsValid:
  assumes "dbMask = PKCS1_OAEP_decode_dbMask seed" 
  shows   "octets_valid dbMask" 
  using assms PKCS1_OAEP_decode_dbMask_def mgf_valid by presburger

lemma OAEP_decode_dbMask_len:
  assumes "dbMask = PKCS1_OAEP_decode_dbMask seed" 
  shows   "length dbMask = k - hLen - 1" 
  using assms PKCS1_OAEP_decode_dbMask_def mgf_len by presburger

lemma OAEP_decode_DB_octetsValid:
  assumes "DB = PKCS1_OAEP_decode_DB maskedDB dbMask" "octets_valid maskedDB" "octets_valid dbMask"
  shows   "octets_valid DB"
  using assms PKCS1_OAEP_decode_DB_def xor_valid_words by auto

lemma OAEP_decode_DB_len:
  assumes "DB = PKCS1_OAEP_decode_DB maskedDB dbMask"  "length maskedDB = x"  "length dbMask = x"
  shows   "length DB = x"
  using assms PKCS1_OAEP_decode_DB_def xor_words_length by auto

lemma OAEP_decode_lHash_octetsValid:
  assumes "lHash' = PKCS1_OAEP_decode_lHash DB"  "octets_valid DB"
  shows   "octets_valid lHash'"
  by (metis assms PKCS1_OAEP_decode_lHash_def in_set_takeD words_valid_def) 

lemma OAEP_decode_lHash_len:
  assumes "lHash' = PKCS1_OAEP_decode_lHash DB"  "hLen \<le> length DB"
  shows   "length lHash' = hLen"
  using assms PKCS1_OAEP_decode_lHash_def by auto

lemma OAEP_decode_PSlen_pos:
  assumes "PSlen = PKCS1_OAEP_decode_PSlen DB"
  shows   "0 \<le> PSlen"
  using assms PKCS1_OAEP_decode_PSlen_def by blast

lemma OAEP_decode_validPS_DBlen:
  assumes "PKCS1_OAEP_decode_validPS DB"  "PSlen = PKCS1_OAEP_decode_PSlen DB"
  shows   "hLen + PSlen + 1  \<le> length DB"
  by (metis assms PKCS1_OAEP_decode_PSlen_def PKCS1_OAEP_decode_validPS_def Suc_eq_plus1 Suc_leI 
        add.commute diff_is_0_eq' drop_drop length_0_conv length_drop linorder_not_less 
        strip_zero_drop)

lemma OAEP_decode_validPS_DB_PS:
  assumes "PKCS1_OAEP_decode_validPS DB"  "PSlen = PKCS1_OAEP_decode_PSlen DB"
  shows   "take PSlen (drop hLen DB) = replicate PSlen 0"
  by (metis PKCS1_OAEP_decode_PSlen_def append_eq_conv_conj assms(2) length_replicate 
        strip_zero_concat)

lemma OAEP_decode_inputValid_DB:
  assumes "PKCS1_RSAES_OAEP_Decrypt_validInput C lHash"
          "c          = PKCS1_OS2IP C"
          "m          = RSADECRYPT c"
          "EM         = PKCS1_I2OSP m k"
          "maskedSeed = PKCS1_OAEP_decode_maskedSeed EM"
          "maskedDB   = PKCS1_OAEP_decode_maskedDB EM"
          "seedMask   = PKCS1_OAEP_decode_seedMask maskedDB"
          "seed       = PKCS1_OAEP_decode_seed maskedSeed seedMask"
          "dbMask     = PKCS1_OAEP_decode_dbMask seed"
          "DB         = PKCS1_OAEP_decode_DB maskedDB dbMask"
          "lHash'     = PKCS1_OAEP_decode_lHash DB"
          "M          = PKCS1_OAEP_decode_M DB"
          "PSlen      = PKCS1_OAEP_decode_PSlen DB"
          "PS         = replicate PSlen 0"
  shows   "DB = lHash @ PS @ [1] @ M"
proof - 
  have 0: "lHash = lHash'"
    by (metis OAEPdefs(3) assms(1,2,3,4,5,6,7,8,9,10,11))
  have 1: "take hLen DB = lHash"
    using 0 PKCS1_OAEP_decode_lHash_def assms(11) by presburger 
  have 2: "(drop (hLen+PSlen) DB) ! 0 = 1"
    by (metis assms(1,2,3,4,5,6,7,8,9,10,13) drop_drop strip_zero_drop PKCS1_OAEP_decode_PSlen_def
          PKCS1_OAEP_decode_validPS_def OAEPdefs(3) add.commute) 
  have 3: "drop (hLen+PSlen+1) DB = M"
    by (metis PKCS1_OAEP_decode_M_def PKCS1_OAEP_decode_PSlen_def add.commute assms(12,13)
          drop_drop strip_zero_drop)
  have 4: "take PSlen (drop hLen DB) = PS"
    by (metis PKCS1_OAEP_decode_PSlen_def append_eq_conv_conj assms(13,14) length_replicate
          strip_zero_concat)
  show ?thesis 
    by (metis Cons_nth_drop_Suc One_nat_def PKCS1_OAEP_decode_PSlen_def append_Cons append_Nil
          PKCS1_OAEP_decode_validPS_def OAEPdefs(3) add.commute assms(1,2,3,4,5,6,7,8,9,10,13)
          append_take_drop_id drop0 drop_drop length_greater_0_conv strip_zero_drop 1 2 3 4)
          
qed

lemma OAEP_decode_M_octetsValid:
  assumes "M = PKCS1_OAEP_decode_M DB"  "octets_valid DB"
  shows   "octets_valid M"
  by (metis assms PKCS1_OAEP_decode_M_def words_valid_def in_set_dropD
        words_to_nat_to_strip_words words_upper_bound) 

lemma OAEP_decode_M_len:
  assumes "M = PKCS1_OAEP_decode_M DB"  "PSlen = PKCS1_OAEP_decode_PSlen DB"
  shows   "length M = (length DB) - hLen - PSlen - 1"
  by (metis assms PKCS1_OAEP_decode_M_def PKCS1_OAEP_decode_PSlen_def length_drop strip_zero_drop) 

lemma OAEP_decode_M_drop:
  assumes "M = PKCS1_OAEP_decode_M DB"  "PSlen = PKCS1_OAEP_decode_PSlen DB"
  shows   "M = drop (hLen + PSlen + 1) DB"
  by (metis (no_types) PKCS1_OAEP_decode_M_def PKCS1_OAEP_decode_PSlen_def add.commute assms(1,2) 
        drop_drop strip_zero_drop) 


subsubsection \<open>RSAES-OAEP Lemmas\<close>

text \<open>In the following lemma, we put together all the facts that we know about the intermediate
values when encrypting a message M with RSA-OAEP.\<close>
lemma OAEP_Encrypt_IntVals:
  assumes "PKCS1_RSAES_OAEP_Encrypt_lengthValid mLen"
          "lHash      = Hash L"
          "PS         = PKCS1_OAEP_PS mLen" 
          "DB         = PKCS1_OAEP_DB lHash PS M" 
          "dbMask     = PKCS1_OAEP_dbMask seed"  
          "maskedDB   = PKCS1_OAEP_maskedDB DB dbMask"
          "seedMask   = PKCS1_OAEP_seedMask maskedDB"
          "maskedSeed = PKCS1_OAEP_maskedSeed seed seedMask"
          "EM         = PKCS1_OAEP_EM maskedSeed maskedDB"
          "m          = PKCS1_OS2IP EM" 
          "c          = RSAENCRYPT m"
          "C          = PKCS1_I2OSP c k" 
          "length M    = mLen"  "octets_valid M" 
          "length seed = hLen"  "octets_valid seed"
  shows   "length lHash      = hLen                  \<and> octets_valid lHash \<and>
           length PS         = k - mLen - 2*hLen - 2 \<and> octets_valid PS \<and>
           length DB         = k - hLen - 1          \<and> octets_valid DB \<and>
           length dbMask     = k - hLen - 1          \<and> octets_valid dbMask \<and> 
           length maskedDB   = k - hLen - 1          \<and> octets_valid maskedDB \<and>
           length seedMask   = hLen                  \<and> octets_valid seedMask \<and>
           length maskedSeed = hLen                  \<and> octets_valid maskedSeed \<and> 
           length EM         = k                     \<and> octets_valid EM \<and> 
           m < n                                     \<and> c < n \<and>
           length C          = k                     \<and> octets_valid C \<and>
           C = PKCS1_RSAES_OAEP_Encrypt M L seed     \<and>
           PKCS1_OAEP_decode_Y EM = 0                \<and> PKCS1_OAEP_decode_M DB = M \<and>
           lHash = PKCS1_OAEP_decode_lHash DB        \<and> PKCS1_OAEP_decode_validPS DB"
proof - 
  have lH1: "length lHash = hLen"               using assms(2) hash_len by blast
  have lH2: "octets_valid lHash"                using assms(2) hash_valid by fast
  have ps1: "length PS = k - mLen - 2*hLen - 2" using assms(3) OAEP_PS_len by blast
  have ps2: "octets_valid PS"           using assms(3) OAEP_PS_octetsValid by fast
  have db1: "length DB = k - hLen - 1"  using assms(1,4,13) lH1 ps1 OAEP_DB_len by algebra
  have db2: "octets_valid DB"           by (simp add: OAEP_DB_octetsValid assms(4,14) lH2 ps2)
  have db3: "lHash = PKCS1_OAEP_decode_lHash DB"
    by (simp add: PKCS1_OAEP_DB_def PKCS1_OAEP_decode_lHash_def assms(4) lH1)
  have db40: "drop hLen DB = PS@[1::nat]@M" 
    by (simp add: PKCS1_OAEP_DB_def assms(4) lH1)
  have db41: "words_strip_zero (drop hLen DB) = [1]@M" 
    by (simp add: assms(3) db40 PKCS1_OAEP_PS_def strip_prepend_zeros) 
  have db4: "PKCS1_OAEP_decode_validPS DB"    using db41 PKCS1_OAEP_decode_validPS_def by force
  have db5: "PKCS1_OAEP_decode_M DB = M"      by (simp add: PKCS1_OAEP_decode_M_def db41)
  have dbm1: "length dbMask = k - hLen - 1"   using assms(5) OAEP_dbMask_len by fast
  have dbm2: "octets_valid dbMask"            using assms(5) OAEP_dbMask_octetsValid by simp
  have mdb1: "length maskedDB = k - hLen - 1" using assms(6) OAEP_maskedDB_len db1 dbm1 by blast
  have mdb2: "octets_valid maskedDB"   using assms(6) OAEP_maskedDB_octetsValid db2 dbm2 by blast
  have sm1: "length seedMask = hLen"   using assms(7) OAEP_seedMask_len by blast
  have sm2: "octets_valid seedMask"    using assms(7) OAEP_seedMask_octetsValid by blast
  have ms1: "length maskedSeed = hLen" using assms(8,15) sm1 OAEP_maskedSeed_len by blast
  have ms2: "octets_valid maskedSeed"  using assms(8,16) sm2 OAEP_maskedSeed_octetsValid by blast
  have em1: "length EM = k"    using assms(1,9) ms1 mdb1 OAEP_EM_len by blast
  have em2: "octets_valid EM"  using assms(9) ms2 mdb2 OAEP_EM_octetsValid by simp
  have em3: "length (words_strip_zero EM) \<le> k - 1" using assms(9) em1 OAEP_EM_strip0_len by fast
  have em4: "PKCS1_OAEP_decode_Y EM = 0" 
    by (simp add: assms(9) PKCS1_OAEP_EM_def PKCS1_OAEP_decode_Y_def)
  have m1: "m < n"
    using em3 em2 assms(10,14,15) OAEP_m_less_n PKCS1_RSAEP_messageValid_def by algebra
  have c1: "c < n"          using RSA_bnd(1) assms(11) by simp 
  have C1: "length C = k"   using OAEP_decode_EM_len k_def assms(12) c1 by blast
  have C2: "octets_valid C" by (simp add: I2OSP_octets_valid assms(12)) 
  have C3: "C = PKCS1_RSAES_OAEP_Encrypt M L seed"
    using OAEPdefs(2) assms(2,3,4,5,6,7,8,9,10,11,12,13,14) by metis
  show ?thesis 
    using lH1 lH2 ps1 ps2 db1 db2 db3 db4 db5 dbm1 dbm2 mdb1 mdb2 sm1 sm2 ms1 ms2 em1 em2 em3 em4
       m1 c1 C1 C2 C3 by blast
qed

text \<open>Assuming you have valid inputs, this lemma shows that the intermediate values computed while
encrypting a message with RSA-OAEP match the corresponding intermediate values computed while
decrypting that ciphertext.\<close>
lemma OAEP_EncryptDecrypt_IntValsMatch:
  assumes "PKCS1_RSAES_OAEP_Encrypt_lengthValid mLen" 
          "octets_valid M"   "length seed = hLen"   "octets_valid seed" 
          "mLen        = length M" 
          "lHash       = Hash L"
          "PS          = PKCS1_OAEP_PS mLen"
          "DB          = PKCS1_OAEP_DB lHash PS M"
          "dbMask      = PKCS1_OAEP_dbMask seed"
          "maskedDB    = PKCS1_OAEP_maskedDB DB dbMask"
          "seedMask    = PKCS1_OAEP_seedMask maskedDB"
          "maskedSeed  = PKCS1_OAEP_maskedSeed seed seedMask"
          "EM          = PKCS1_OAEP_EM maskedSeed maskedDB"
          "m           = PKCS1_OS2IP EM"
          "c           = RSAENCRYPT m"
          "C           = PKCS1_I2OSP c k"
          "c'          = PKCS1_OS2IP C" 
          "m'          = RSADECRYPT c'" 
          "EM'         = PKCS1_I2OSP m' k" 
          "Y'          = PKCS1_OAEP_decode_Y EM'" 
          "maskedSeed' = PKCS1_OAEP_decode_maskedSeed EM'"
          "maskedDB'   = PKCS1_OAEP_decode_maskedDB EM'"
          "seedMask'   = PKCS1_OAEP_decode_seedMask maskedDB'"
          "seed'       = PKCS1_OAEP_decode_seed maskedSeed' seedMask'"
          "dbMask'     = PKCS1_OAEP_decode_dbMask seed'"
          "DB'         = PKCS1_OAEP_decode_DB maskedDB' dbMask'"
          "M'          = PKCS1_OAEP_decode_M DB'" 
          "lHash'      = PKCS1_OAEP_decode_lHash DB'"
    shows "DB = DB' \<and> dbMask = dbMask' \<and> maskedDB = maskedDB' \<and> seedMask = seedMask' \<and> Y' = 0 \<and>
           maskedSeed = maskedSeed' \<and> EM = EM' \<and> m = m' \<and> c = c' \<and> seed = seed' \<and> M = M' \<and>
           lHash' = lHash \<and> C = PKCS1_RSAES_OAEP_Encrypt M L seed \<and> length C = k \<and>
           M' = PKCS1_RSAES_OAEP_Decrypt C \<and> PKCS1_OAEP_decode_validPS DB"
proof - 
  have c: "c = c'" 
    by (metis I2OSP_OS2IP assms(16,17)) 
  have m1: "m < n"
    using OAEP_Encrypt_IntVals assms(1,2,3,4,5,6,7,8,9,10,11,12,13,14,15) by blast
  have m: "m = m'"
    using RSA_inv(1) c m1 assms(15,18) by metis 
  have EM1: "length EM = k"
    using OAEP_Encrypt_IntVals assms(1,2,3,4,5,6,7,8,9,10,11,12,13) by blast
  have EM2: "octets_valid EM" 
    using OAEP_Encrypt_IntVals assms(1,2,3,4,5,6,7,8,9,10,11,12,13) by blast
  have EM: "EM = EM'" 
    using m EM1 EM2 OS2IP_I2OSP assms(14,19) by force
  have Y: "Y' = 0"
    using EM OAEP_Encrypt_IntVals assms(1,2,3,4,5,6,7,8,9,10,11,12,13,20) by force
  have mS1: "length maskedSeed = hLen"
    using OAEP_maskedSeed_len PKCS1_OAEP_seedMask_def assms(3,11,12) mgf_len by presburger
  have mS: "maskedSeed = maskedSeed'" 
    by (metis EM One_nat_def PKCS1_OAEP_EM_def PKCS1_OAEP_decode_maskedSeed_def Suc_eq_plus1 
          append_eq_conv_conj assms(13,21) list.size(3) list.size(4) mS1) 
  have mDB: "maskedDB = maskedDB'" 
    by (metis assms(13,22) EM PKCS1_OAEP_decode_maskedDB_def PKCS1_OAEP_EM_def Suc_eq_plus1 
          add.commute append.simps(1) append.simps(2) cancel_comm_monoid_add_class.diff_cancel 
          drop0 drop_Suc_Cons drop_all drop_append mS1 order_refl)
  have sM: "seedMask = seedMask'"
    using assms(11,23) mDB PKCS1_OAEP_decode_seedMask_def PKCS1_OAEP_seedMask_def by presburger 
  have S: "seed = seed'"
    by (metis assms(3,11,12,24) mS sM PKCS1_OAEP_decode_seed_def PKCS1_OAEP_maskedSeed_def 
          PKCS1_OAEP_seedMask_def words_xor_inv xor_words_symm mgf_len)
  have dbM: "dbMask = dbMask'"
    using assms(9,15,25) S PKCS1_OAEP_dbMask_def PKCS1_OAEP_decode_dbMask_def by presburger
  have DB1: "DB = DB'"
    by (metis assms(1,2,3,4,5,6,7,8,9,10,26) dbM mDB mgf_len PKCS1_OAEP_maskedDB_def
        words_xor_inv2 PKCS1_OAEP_dbMask_def PKCS1_OAEP_decode_DB_def OAEP_Encrypt_IntVals)
  have DB2: "PKCS1_OAEP_decode_validPS DB" by (metis OAEP_Encrypt_IntVals assms(1,2,3,4,5,6,7,8))
  have M: "M = M'"
    by (metis DB1 OAEP_Encrypt_IntVals assms(1,2,3,4,5,6,7,8,27))
  have lH: "lHash' = lHash"
    using DB1 PKCS1_OAEP_DB_def PKCS1_OAEP_decode_lHash_def assms(6,8,28) hash_len by force
  have C1: "C = PKCS1_RSAES_OAEP_Encrypt M L seed"
    by (metis OAEPdefs(2) assms(5,6,7,8,9,10,11,12,13,14,15,16))
  have C2: "length C = k" by (simp add: OAEP_decode_EM_len RSA_bnd(1) assms(15,16))
  have "M' = PKCS1_RSAES_OAEP_Decrypt C"
    by (metis OAEPdefs(4) assms(17,18,19,21,22,23,24,25,26,27))
  then show ?thesis using c m EM Y mS mDB sM S dbM DB1 DB2 M lH C1 C2 by blast
qed

lemma OAEP_Encrypt_validCipher_h1:
  assumes "C = PKCS1_RSAES_OAEP_Encrypt M L seed" 
  shows   "length C = k" 
  by (metis OAEPdefs(2) assms OAEP_decode_EM_len RSA_bnd(1)) 

lemma OAEP_Encrypt_validCipher_h2:
  assumes "PKCS1_RSAES_OAEP_Encrypt_lengthValid mLen" 
  shows   "2*hLen + 2 \<le> k"
  by (meson Nat.le_diff_conv2 OAEPdefs(1) add_leD2 assms)

lemma OAEP_Encrypt_validCipher_h3:
  assumes "C = PKCS1_RSAES_OAEP_Encrypt M L seed" 
          "c          = PKCS1_OS2IP C" 
          "m          = RSADECRYPT c" 
          "EM         = PKCS1_I2OSP m k" 
          "Y          = PKCS1_OAEP_decode_Y EM" 
          "maskedSeed = PKCS1_OAEP_decode_maskedSeed EM"
          "maskedDB   = PKCS1_OAEP_decode_maskedDB EM"
          "seedMask   = PKCS1_OAEP_decode_seedMask maskedDB"
          "seed'      = PKCS1_OAEP_decode_seed maskedSeed seedMask"
          "dbMask     = PKCS1_OAEP_decode_dbMask seed'"
          "DB         = PKCS1_OAEP_decode_DB maskedDB dbMask"
          "lHash'     = PKCS1_OAEP_decode_lHash DB"
          "mLen = length M"   "octets_valid M"
          "PKCS1_RSAES_OAEP_Encrypt_lengthValid mLen"   
          "length seed = hLen"   "octets_valid seed"
          "lHash = Hash L"
  shows   "Y = 0 \<and> (lHash' = lHash) \<and> (PKCS1_OAEP_decode_validPS DB)"
proof - 
  let ?PS          = "PKCS1_OAEP_PS mLen"
  let ?DB          = "PKCS1_OAEP_DB lHash ?PS M"
  let ?dbMask      = "PKCS1_OAEP_dbMask seed"
  let ?maskedDB    = "PKCS1_OAEP_maskedDB ?DB ?dbMask" 
  let ?seedMask    = "PKCS1_OAEP_seedMask ?maskedDB"
  let ?maskedSeed  = "PKCS1_OAEP_maskedSeed seed ?seedMask" 
  let ?EM          = "PKCS1_OAEP_EM ?maskedSeed ?maskedDB" 
  let ?m           = "PKCS1_OS2IP ?EM" 
  let ?c           = "RSAENCRYPT ?m" 
  have "?DB = DB \<and> Y = 0 \<and> lHash' = lHash"
    using assms OAEPdefs(2) 
      OAEP_EncryptDecrypt_IntValsMatch[of mLen M seed lHash L ?PS ?DB ?dbMask ?maskedDB ?seedMask
        ?maskedSeed ?EM ?m ?c C c m EM Y maskedSeed maskedDB seedMask seed' dbMask DB _ lHash']
    by metis
  then show ?thesis using assms OAEP_Encrypt_IntVals by metis 
qed


text\<open>If you start with a valid message, when you encode and encrypt it with RSA-OAEP, the resulting
ciphertext is a valid input for the RSA-OAEP decryption scheme.\<close>
lemma OAEP_Encrypt_validCipher [OAEPthms]:
  assumes "PKCS1_RSAES_OAEP_Encrypt_lengthValid (length M)" 
          "C = PKCS1_RSAES_OAEP_Encrypt M L seed" 
          "octets_valid M"  "octets_valid seed"  "length seed = hLen"
  shows   "PKCS1_RSAES_OAEP_Decrypt_validInput C (Hash L)" 
proof - 
  let ?lHash      = "Hash L"
  let ?c          = "PKCS1_OS2IP C"
  let ?m          = "RSADECRYPT ?c"
  let ?EM         = "PKCS1_I2OSP ?m k"
  let ?Y          = "PKCS1_OAEP_decode_Y ?EM"
  let ?maskedSeed = "PKCS1_OAEP_decode_maskedSeed ?EM"
  let ?maskedDB   = "PKCS1_OAEP_decode_maskedDB ?EM"
  let ?seedMask   = "PKCS1_OAEP_decode_seedMask ?maskedDB"
  let ?seed       = "PKCS1_OAEP_decode_seed ?maskedSeed ?seedMask"
  let ?dbMask     = "PKCS1_OAEP_decode_dbMask ?seed" 
  let ?DB         = "PKCS1_OAEP_decode_DB ?maskedDB ?dbMask"
  let ?lHash'     = "PKCS1_OAEP_decode_lHash ?DB"
  have a1: "length C = k"    using assms(2) OAEP_Encrypt_validCipher_h1 by blast  
  have a2: "2*hLen + 2 \<le> k"  using assms(1) OAEP_Encrypt_validCipher_h2 by blast
  have a3: "?c < n"          by (metis assms(2) I2OSP_OS2IP OAEPdefs(2) RSA_bnd(1))
  have a4: "(?Y = 0) \<and> (?lHash' = ?lHash) \<and> (PKCS1_OAEP_decode_validPS ?DB)"
                             using assms OAEP_Encrypt_validCipher_h3 by force
  show ?thesis               using a1 a2 a3 a4 OAEPdefs(3) by presburger
qed

text\<open>Start with a valid message and seed.  Encrypt the message with RSA-OAEP.  Decrypt the 
resulting ciphertext with RSA-OAEP.  The result will be the original message.\<close>
lemma OAEP_Encrypt_Decrypt [OAEPthms]:
  assumes "PKCS1_RSAES_OAEP_Encrypt_lengthValid (length M)" 
          "C = PKCS1_RSAES_OAEP_Encrypt M L seed"
          "octets_valid M"  "octets_valid seed" "length seed = hLen"
  shows   "PKCS1_RSAES_OAEP_Decrypt C = M"
proof - 
  let ?c'          = "PKCS1_OS2IP C"
  let ?m'          = "RSADECRYPT ?c'"
  let ?EM'         = "PKCS1_I2OSP ?m' k"
  let ?maskedSeed' = "PKCS1_OAEP_decode_maskedSeed ?EM'"
  let ?maskedDB'   = "PKCS1_OAEP_decode_maskedDB ?EM'"
  let ?seedMask'   = "PKCS1_OAEP_decode_seedMask ?maskedDB'"
  let ?seed'       = "PKCS1_OAEP_decode_seed ?maskedSeed' ?seedMask'"
  let ?dbMask'     = "PKCS1_OAEP_decode_dbMask ?seed'" 
  let ?DB'         = "PKCS1_OAEP_decode_DB ?maskedDB' ?dbMask'"
  let ?M'          = "PKCS1_OAEP_decode_M ?DB'" 
  have 1: "M = ?M'"  by (metis assms OAEPdefs(2) OAEP_EncryptDecrypt_IntValsMatch)
  have 2: "PKCS1_RSAES_OAEP_Decrypt C = ?M'"   by (meson OAEPdefs(4))
  show ?thesis       using 1 2 by presburger 
qed

text \<open>In the following lemma, we put together all the facts that we know about the intermediate
values when decrypting ciphertext C with RSA-OAEP.\<close>
lemma OAEP_Decrypt_IntVals: 
  assumes "PKCS1_RSAES_OAEP_Decrypt_validInput C lHash" 
          "c           = PKCS1_OS2IP C" 
          "m           = RSADECRYPT c" 
          "EM          = PKCS1_I2OSP m k" 
          "Y           = PKCS1_OAEP_decode_Y EM" 
          "maskedSeed  = PKCS1_OAEP_decode_maskedSeed EM"
          "maskedDB    = PKCS1_OAEP_decode_maskedDB EM"
          "seedMask    = PKCS1_OAEP_decode_seedMask maskedDB"
          "seed        = PKCS1_OAEP_decode_seed maskedSeed seedMask"
          "dbMask      = PKCS1_OAEP_decode_dbMask seed"
          "DB          = PKCS1_OAEP_decode_DB maskedDB dbMask"
          "M           = PKCS1_OAEP_decode_M DB" 
          "lHash'      = PKCS1_OAEP_decode_lHash DB"
          "PSlen       = PKCS1_OAEP_decode_PSlen DB"
          "PS          = replicate PSlen 0" 
  shows   "m  < n                  \<and> Y = 0          \<and> lHash = lHash' \<and>
          octets_valid EM          \<and> length EM  = k \<and> 
          octets_valid maskedSeed  \<and> length maskedSeed = hLen \<and>
          octets_valid maskedDB    \<and> length maskedDB   = k - 1 - hLen \<and>
          octets_valid seedMask    \<and> length seedMask   = hLen \<and>
          octets_valid seed        \<and> length seed       = hLen \<and>
          octets_valid dbMask      \<and> length dbMask     = k - hLen - 1 \<and>
          octets_valid DB          \<and> length DB         = k - hLen - 1 \<and>
          octets_valid lHash'      \<and> length lHash'     = hLen \<and>
          octets_valid M           \<and> length M          = k - 2*hLen - PSlen - 2 \<and>
          M = PKCS1_RSAES_OAEP_Decrypt C       \<and> PSlen \<le> k - 2*hLen - 2   \<and> 
          DB = lHash @ PS @ [1] @ M            \<and>  EM = [0] @ maskedSeed @ maskedDB"
proof - 
  have l1: "2*hLen + 2 \<le> k"          using assms(1,2,3) OAEPdefs(3) by meson
  have l2:   "hLen + 1 \<le> k"          using l1 by linarith
  have l3: "hLen + 1 \<le> k - hLen - 1" using l1 by auto
  have m: "m < n"              using assms(1,2,3) RSA_bnd(2) by blast
  have EM1: "octets_valid EM"  using assms(4) OAEP_decode_EM_octetsValid by fast
  have EM2: "length EM = k"    using assms(4) m OAEP_decode_EM_len by auto
  have Y: "Y = 0"              using OAEPdefs(3) assms(1,2,3,4,5) by meson
  have mS1: "octets_valid maskedSeed" 
    using assms(6) EM1 OAEP_decode_maskedSeed_octetsValid by force
  have mS2: "length maskedSeed = hLen" 
    using assms(6) l2 EM2 OAEP_decode_maskedSeed_len by presburger
  have mDB1: "octets_valid maskedDB" 
    using assms(7) EM1 OAEP_decode_maskedDB_octetsValid by blast
  have mDB2: "length maskedDB = k - 1 - hLen" 
    using assms(7) EM2 OAEP_decode_maskedDB_len by presburger
  have sM1: "octets_valid seedMask" 
    using assms(8) mgf_valid OAEP_decode_seedMask_octetsValid by blast
  have sM2: "length seedMask = hLen" using assms(8) mgf_len OAEP_decode_seedMask_len by blast
  have s1: "octets_valid seed"       using assms(9) mS1 sM1 OAEP_decode_seed_octetsValid by blast
  have s2: "length seed = hLen"      using assms(9) mS2 sM2 OAEP_decode_seed_len by blast
  have dbM1: "octets_valid dbMask"   using assms(10) OAEP_decode_dbMask_octetsValid by blast
  have dbM2: "length dbMask = k - hLen - 1"  using assms(10) OAEP_decode_dbMask_len by blast
  have DB1: "octets_valid DB"        using assms(11) mDB1 dbM1 OAEP_decode_DB_octetsValid by blast
  have DB2: "length DB = k - hLen - 1" using assms(11) mDB2 dbM2 OAEP_decode_DB_len by force
  have lH1: "octets_valid lHash'"      using assms(13) DB1 OAEP_decode_lHash_octetsValid by fast
  have lH2: "length lHash' = hLen"     using assms(13) l3 DB2 OAEP_decode_lHash_len by auto
  have lH3: "lHash = lHash'"
    by (metis OAEPdefs(3) assms(1,2,3,4,6,7,8,9,10,11,13)) 
  have M1: "octets_valid M"            using assms(12) DB1 OAEP_decode_M_octetsValid by fast
  have M2: "length M = k - 2*hLen - PSlen - 2" 
    by (metis assms(12,14) DB2 OAEP_decode_M_len Suc_eq_plus1 add.left_neutral add_2_eq_Suc' 
        diff_diff_left mult.commute mult.right_neutral mult_Suc_right) 
  have M3: "M = PKCS1_RSAES_OAEP_Decrypt C"
    by (metis OAEPdefs(4) assms(2,3,4,6,7,8,9,10,11,12) )
  have PSl1: "hLen + PSlen + 1  \<le> length DB" 
    using assms OAEP_decode_validPS_DBlen OAEPdefs(3) by metis
  have PSl: "PSlen \<le> k - 2*hLen - 2"    using PSl1 DB2 by linarith
  have DB3: "DB = lHash @ PS @ [1] @ M" using OAEP_decode_inputValid_DB assms by meson
  have EM3: "EM = [0] @ maskedSeed @ maskedDB" 
  proof - 
    have 1: "hd EM = 0" 
      using Y PKCS1_OAEP_decode_Y_def assms(5) by presburger 
    have 2: "take hLen (drop 1 EM) = maskedSeed"
      using PKCS1_OAEP_decode_maskedSeed_def assms(6) by presburger
    have 3: "drop (hLen + 1) EM = maskedDB"
      by (simp add: PKCS1_OAEP_decode_maskedDB_def assms(7))
    show ?thesis 
      by (metis 1 2 3 EM2 One_nat_def add_leD2 append_Cons append_Nil append_take_drop_id drop0
            drop_Suc drop_drop hd_Cons_tl l2 list.size(3) not_one_le_zero)
  qed
  show ?thesis using m EM1 EM2 Y mS1 mS2 mDB1 mDB2 sM1 sM2 s1 s2 dbM1 dbM2 DB1 DB2 lH1 lH2 lH3
    M1 M2 M3 PSl DB3 EM3 by blast
qed

text\<open>If you start with a valid ciphertext, when you decode and decrypt it with RSA-OAEP, the 
resulting plaintexttext is a valid input for the RSA-OAEP encryption scheme.\<close>
lemma OAEP_Decrypt_lengthValid [OAEPthms]: 
  assumes "M = PKCS1_RSAES_OAEP_Decrypt C"
          "PKCS1_RSAES_OAEP_Decrypt_validInput C lHash" 
          "mLen = length M" 
  shows   "PKCS1_RSAES_OAEP_Encrypt_lengthValid mLen" 
proof - 
  let ?c          = "PKCS1_OS2IP C"
  let ?m          = "RSADECRYPT ?c"
  let ?EM         = "PKCS1_I2OSP ?m k"
  let ?Y          = "PKCS1_OAEP_decode_Y ?EM"
  let ?maskedSeed = "PKCS1_OAEP_decode_maskedSeed ?EM"
  let ?maskedDB   = "PKCS1_OAEP_decode_maskedDB ?EM"
  let ?seedMask   = "PKCS1_OAEP_decode_seedMask ?maskedDB"
  let ?seed       = "PKCS1_OAEP_decode_seed ?maskedSeed ?seedMask"
  let ?dbMask     = "PKCS1_OAEP_decode_dbMask ?seed" 
  let ?DB         = "PKCS1_OAEP_decode_DB ?maskedDB ?dbMask"
  let ?PSlen      = "PKCS1_OAEP_decode_PSlen ?DB"
  let ?M          = "PKCS1_OAEP_decode_M ?DB"
  have 1: "M = ?M"            by (metis (no_types) OAEPdefs(4) assms(1))
  have 2: "mLen = length ?M"  using 1 assms(3) by fast
  have 3: "mLen = k - 2*hLen - ?PSlen - 2" 
    using RSA_npos 2 assms(2,3) OAEP_Decrypt_IntVals by blast
  have 4: "2*hLen + 2 \<le> k"    using assms(2) OAEPdefs(3) by meson
  show ?thesis                using 3 4 OAEPdefs(1) by fastforce
qed

text \<open>Assuming you have valid inputs, this lemma shows that the intermediate values computed while
decrypting a ciphertext with RSA-OAEP match the corresponding intermediate values computed while
encrypting the resulting plaintext.\<close>
lemma OAEP_DecryptEncrypt_IntValsMatch:
  assumes "PKCS1_RSAES_OAEP_Decrypt_validInput C lHash"   "octets_valid C"      
          "c'          = PKCS1_OS2IP C" 
          "m'          = RSADECRYPT c'" 
          "EM'         = PKCS1_I2OSP m' k" 
          "Y'          = PKCS1_OAEP_decode_Y EM'" 
          "maskedSeed' = PKCS1_OAEP_decode_maskedSeed EM'"
          "maskedDB'   = PKCS1_OAEP_decode_maskedDB EM'"
          "seedMask'   = PKCS1_OAEP_decode_seedMask maskedDB'"
          "seed'       = PKCS1_OAEP_decode_seed maskedSeed' seedMask'"
          "dbMask'     = PKCS1_OAEP_decode_dbMask seed'"
          "DB'         = PKCS1_OAEP_decode_DB maskedDB' dbMask'"
          "M'          = PKCS1_OAEP_decode_M DB'" 
          "lHash'      = PKCS1_OAEP_decode_lHash DB'"
          "PSlen'      = PKCS1_OAEP_decode_PSlen DB'"
          "mLen        = length M'"
          "PS          = PKCS1_OAEP_PS mLen"
          "DB          = PKCS1_OAEP_DB lHash PS M'"
          "dbMask      = PKCS1_OAEP_dbMask seed'"
          "maskedDB    = PKCS1_OAEP_maskedDB DB dbMask"
          "seedMask    = PKCS1_OAEP_seedMask maskedDB"
          "maskedSeed  = PKCS1_OAEP_maskedSeed seed' seedMask"
          "EM          = PKCS1_OAEP_EM maskedSeed maskedDB"
          "m           = PKCS1_OS2IP EM"
          "c           = RSAENCRYPT m"
          "C'          = PKCS1_I2OSP c k"
          "Hash L      = lHash" 
    shows "DB = DB' \<and> dbMask = dbMask' \<and> maskedDB = maskedDB' \<and> seedMask = seedMask' \<and> Y' = 0 \<and>
           maskedSeed = maskedSeed' \<and> EM = EM' \<and> m = m' \<and> c = c' \<and> C = C' \<and> lHash' = lHash \<and> 
           C' = PKCS1_RSAES_OAEP_Encrypt M' L seed' \<and> 
           M' = PKCS1_RSAES_OAEP_Decrypt C \<and> (length PS = PSlen')"
proof - 
  have l1: "2*hLen + 2 \<le> k"         by (meson OAEPdefs(3) assms(1)) 
  have l2: "0 \<le> k - 2*hLen - 2"     using l1 by blast
  let ?x = "k - 2*hLen - 2"
  have lH: "lHash' = lHash"         by (metis assms(1,3,4,5,7,8,9,10,11,12,14) OAEPdefs(3))
  have lH1: "hLen = length lHash'"  using assms(27) hash_len lH by fastforce 
  have Y: "Y' = 0"                  by (metis assms(1,3,4,5,6) OAEPdefs(3)) 
  have M: "M' = PKCS1_RSAES_OAEP_Decrypt C"  by (metis OAEPdefs(4) assms(3,4,5,7,8,9,10,11,12,13))
  have M1: "mLen = k - 2*hLen - PSlen' - 2"  using assms OAEP_Decrypt_IntVals by meson
  have M2: "mLen = ?x - PSlen'"              using M1 by auto
  have M3: "mLen \<le> ?x"                       using M2 by linarith
  have PS1: "PSlen' \<le> k - 2*hLen - 2"
    using OAEP_Decrypt_IntVals assms(1,3,4,5,6,7,8,9,10,11,12,15) by blast
  have PS: "length PS = PSlen'"              using M2 OAEP_PS_len PS1 assms(17) by auto 
  have DB1: "DB = lHash @ PS @ [1] @ M'"     using PKCS1_OAEP_DB_def assms(18) by presburger 
  have DB2: "DB' = lHash' @ PS @ [1] @ M'"
    using assms(1,3,4,5,7,8,9,10,11,12,13,15,17) PS lH OAEP_decode_inputValid_DB PKCS1_OAEP_PS_def
    by auto
  have DB: "DB = DB'"                        using DB1 DB2 lH by fast
  have dbM: "dbMask = dbMask'" 
    using DB PKCS1_OAEP_dbMask_def PKCS1_OAEP_decode_dbMask_def assms(11,19) by presburger 
  have mDB: "maskedDB = maskedDB'"
    using DB OAEP.OAEP_Decrypt_IntVals OAEP.OAEP_dbMask_len OAEP_axioms PKCS1_OAEP_decode_DB_def 
      PKCS1_OAEP_maskedDB_def assms(1,3,4,5,8,12,19,20) dbM words_xor_inv2 by auto 
  have sM: "seedMask = seedMask'"
    by (simp add: assms(9,21) mDB PKCS1_OAEP_decode_seedMask_def PKCS1_OAEP_seedMask_def) 
  have mS: "maskedSeed = maskedSeed'"
    by(metis sM assms(1,3,4,5,7,10,21,22) OAEP_Decrypt_IntVals OAEP_seedMask_len 
         PKCS1_OAEP_decode_seed_def PKCS1_OAEP_maskedSeed_def words_xor_inv xor_words_symm)
  have EM: "EM = EM'"
    by (metis mDB mS assms(1,3,4,5,7,8,23) OAEP_Decrypt_IntVals PKCS1_OAEP_EM_def)
  have m: "m = m'"  by (simp add: EM I2OSP_OS2IP assms(5,24)) 
  have c: "c = c'"  by (metis OAEPdefs(3) RSA_inv(2) assms(1,3,4,25) m)
  have C: "C = C'"  by (metis OS2IP_I2OSP OAEPdefs(3) assms(1,2,3,26) c) 
  have C2: "C' = PKCS1_RSAES_OAEP_Encrypt M' L seed'"
    by (metis OAEPdefs(2) assms(16,17,18,19,20,21,22,23,24,25,26,27))
  show ?thesis using lH Y M PS DB dbM mDB sM mS EM m c C C2 by argo
qed

text\<open>Start with a valid ciphertext.  Remember that the ciphertext is only valid if the decoded
lHash matches that hash of the known label L.  Decrypt the ciphertext with RSA-OAEP.  Remember the
seed that you computed during that decryption.  Then encrypt the plaintext that you got using that
seed and label L.  The result will be the original ciphertext.\<close>
lemma OAEP_Decrypt_Encrypt [OAEPthms]:
  assumes "PKCS1_RSAES_OAEP_Decrypt_validInput C (Hash L)"
          "M    = PKCS1_RSAES_OAEP_Decrypt      C"
          "seed = PKCS1_RSAES_OAEP_Decrypt_seed C"
          "octets_valid C" 
  shows   "PKCS1_RSAES_OAEP_Encrypt M L seed = C"
proof - 
  let ?lHash       = "Hash L" 
  let ?mLen        = "length M"
  let ?c'          = "PKCS1_OS2IP C"
  let ?m'          = "RSADECRYPT ?c'"
  let ?EM'         = "PKCS1_I2OSP ?m' k"
  let ?Y'          = "PKCS1_OAEP_decode_Y ?EM'"
  let ?maskedSeed' = "PKCS1_OAEP_decode_maskedSeed ?EM'"
  let ?maskedDB'   = "PKCS1_OAEP_decode_maskedDB ?EM'"
  let ?seedMask'   = "PKCS1_OAEP_decode_seedMask ?maskedDB'"
  let ?seed'       = "PKCS1_OAEP_decode_seed ?maskedSeed' ?seedMask'"
  let ?dbMask'     = "PKCS1_OAEP_decode_dbMask ?seed'" 
  let ?DB'         = "PKCS1_OAEP_decode_DB ?maskedDB' ?dbMask'"
  let ?M'          = "PKCS1_OAEP_decode_M ?DB'" 
  let ?lHash'      = "PKCS1_OAEP_decode_lHash ?DB'"
  let ?PSlen'      = "PKCS1_OAEP_decode_PSlen ?DB'"
  let ?mLen'       = "length ?M'"
  let ?PS          = "PKCS1_OAEP_PS ?mLen"
  let ?DB          = "PKCS1_OAEP_DB ?lHash ?PS M"
  let ?dbMask      = "PKCS1_OAEP_dbMask ?seed'"
  let ?maskedDB    = "PKCS1_OAEP_maskedDB ?DB ?dbMask" 
  let ?seedMask    = "PKCS1_OAEP_seedMask ?maskedDB"
  let ?maskedSeed  = "PKCS1_OAEP_maskedSeed ?seed' ?seedMask" 
  let ?EM          = "PKCS1_OAEP_EM ?maskedSeed ?maskedDB" 
  let ?m           = "PKCS1_OS2IP ?EM" 
  let ?c           = "RSAENCRYPT ?m" 
  let ?C           = "PKCS1_I2OSP ?c k"
  have 1: "seed = ?seed'"  by (metis OAEPdefs(5) assms(3)) 
  have 2: "C = ?C \<and> ?M' = PKCS1_RSAES_OAEP_Decrypt C \<and> ?C = PKCS1_RSAES_OAEP_Encrypt ?M' L seed" 
    using 1 assms OAEPdefs(4)
      OAEP_DecryptEncrypt_IntValsMatch[of C ?lHash ?c' ?m' ?EM' ?Y' ?maskedSeed' ?maskedDB' 
      ?seedMask' ?seed' ?dbMask' ?DB' ?M' ?lHash' ?PSlen' ?mLen' ?PS ?DB ?dbMask 
      ?maskedDB ?seedMask ?maskedSeed ?EM ?m ?c ?C L] by metis
  show ?thesis  using 2 assms(2) by argo
qed

end (*end of OAEP locale*)

subsubsection \<open>OAEP Interpretations\<close>
text \<open>To see an example of interpretation the OAEP locale, we define a very bad mask generating 
function, MFG0, and a very bad hash function, Hash0.  These should never ever be used in a real
application.  We also need to have a valid RSA key.\<close>
definition MGF0 :: mgf_type where
  "MGF0 os n = replicate n 0" 

lemma MGF0_len: "\<forall>x y. length (MGF0 x y) = y"
  using MGF0_def by simp

lemma MGF0_valid: "\<forall>x y. octets_valid (MGF0 x y)"
  by (simp add: MGF0_def words_valid_def)

definition Hash0 :: hash_type where
  "Hash0 os = [0]" 

lemma Hash0_len: "\<forall>x. length (Hash0 x) = 1"
  by (metis (no_types) Hash0_def One_nat_def Suc_eq_plus1 list.size(3) list.size(4))

lemma Hash0_valid: "\<forall>x. octets_valid (Hash0 x)"
  by (simp add: Hash0_def words_valid_def)

locale OAEP_Basic_Example = 
  fixes n d p q e :: nat
  assumes RSAkey: "PKCS1_validRSAprivateKey n d p q e"
begin

interpretation OAEP MGF0 Hash0 1 "PKCS1_RSAEP n e" "PKCS1_RSADP n d" n 
proof - 
  have 1: "\<forall>x y. octets_valid (MGF0 x y)" using MGF0_valid  by fast
  have 2: "\<forall>x y. length (MGF0 x y) = y"   using MGF0_len    by meson
  have 3: "\<forall>x. octets_valid (Hash0 x)"    using Hash0_valid by blast
  have 4: "\<forall>x. length (Hash0 x) = 1"      using Hash0_len   by blast
  have 5: "0 < n" using n_positive2 RSAkey ValidKeyDefs(2)  by meson
  have 6: "\<forall>m. PKCS1_RSAEP n e m < n"
    using 5 PKCS1_RSAEP_messageValid_def encryptValidCiphertext by presburger
  have 7: "\<forall>c. PKCS1_RSADP n d c < n" 
    using 5 PKCS1_RSAEP_messageValid_def encryptValidCiphertext by presburger 
  have 8: "\<forall>m<n. PKCS1_RSADP n d (PKCS1_RSAEP n e m) = m"
    using PKCS1_RSAEP_messageValid_def RSAEP_RSADP RSAkey by presburger
  have 9: "\<forall>c<n. PKCS1_RSAEP n e (PKCS1_RSADP n d c) = c"
    by (meson PKCS1_RSAEP_messageValid_def RSADP_RSAEP RSAkey)
  show "OAEP MGF0 Hash0 1 (PKCS1_RSAEP n e) (PKCS1_RSADP n d) n" 
    using 1 2 3 4 5 6 7 8 9 by (simp add: OAEP.intro) 
qed

end (* of locale OAEP_Basic_Example *)

locale OAEP_CRT_Example = 
  fixes n p q dP dQ qInv e :: nat
  assumes RSAkey: "PKCS1_validRSAprivateKey_CRT p q dP dQ qInv e" "n = p*q"
begin

interpretation OAEP MGF0 Hash0 1 "PKCS1_RSAEP n e" "PKCS1_RSADP_CRT p q dP dQ qInv" n 
proof - 
  have 1: "\<forall>x y. octets_valid (MGF0 x y)" using MGF0_valid  by fast
  have 2: "\<forall>x y. length (MGF0 x y) = y"   using MGF0_len    by meson
  have 3: "\<forall>x. octets_valid (Hash0 x)"    using Hash0_valid by blast
  have 4: "\<forall>x. length (Hash0 x) = 1"      using Hash0_len   by blast
  have 5: "0 < n" by (metis RSAkey ValidKeyDefs(3) n_positive2)
  have 6: "\<forall>m. PKCS1_RSAEP n e m < n"
    using 5 PKCS1_RSAEP_messageValid_def encryptValidCiphertext by presburger
  have 7: "\<forall>c. PKCS1_RSADP_CRT p q dP dQ qInv c < n"
    using PKCS1_RSAEP_messageValid_def RSAkey decryptCRTmessageValid2 by auto 
  have 8: "\<forall>m<n. PKCS1_RSADP_CRT p q dP dQ qInv (PKCS1_RSAEP n e m) = m"
    using PKCS1_RSAEP_messageValid_def RSAEP_RSADP_CRT RSAkey by presburger
  have 9: "\<forall>c<n. PKCS1_RSAEP n e (PKCS1_RSADP_CRT p q dP dQ qInv c) = c"
    using PKCS1_RSAEP_messageValid_def RSADP_CRT_RSAEP RSAkey by auto
  show "OAEP MGF0 Hash0 1 (PKCS1_RSAEP n e) (PKCS1_RSADP_CRT p q dP dQ qInv) n" 
    using 1 2 3 4 5 6 7 8 9 by (simp add: OAEP.intro) 
qed

end (* of locale OAEP_CRT_Example *)


subsection \<open>Section 7.2: RSAES-PKCS1-v1.5\<close>
text \<open>"RSAES-PKCS1-v1_5  combines the RSAEP and RSADP primitives (Sections  5.1.1  and 5.1.2) with
the EME-PKCS1-v1_5 encoding method (step 1 in Section 7.2.1 and step 3 in Section 7.2.2). It is
mathematically equivalent to the encryption scheme in PKCS #1 v1.5. RSAES-PKCS1-v1_5 can operate on
messages of length up to k – 11 octets (k is the octet length of the RSA modulus), although care
should be taken to avoid certain attacks on low-exponent RSA due to Coppersmith, Franklin, Patarin,
and Reiter when long messages are encrypted (see the third bullet in the notes below and [10]; [14]
contains an improved attack).  As a general rule, the use of this scheme for encrypting an
arbitrary message, as opposed to a randomly generated key, is not recommended.

The padding string PS in step 2 in Section 7.2.1 is at least eight octets long, which is a security
condition for public-key operations that makes it difficult for an attacker to recover data by 
trying all possible encryption blocks."

Here the padding string PS is randomly generated and assumed to be all non-zero.  Just as with the
seed in OAEP above, we include PS here with the list of inputs of this encryption scheme.\<close>

locale RSAES_PKCS1_v1_5 = 
  fixes RSAENCRYPT RSADECRYPT :: "nat \<Rightarrow> nat"
    and n                     :: nat
assumes RSA_mod:  "0 < n"   "11 < octet_length n"
    and RSA_bnd:  "\<forall>m. (RSAENCRYPT m) < n" 
                  "\<forall>c. (RSADECRYPT c) < n"
    and RSA_inv:  "\<forall>m. (m < n) \<longrightarrow> RSADECRYPT (RSAENCRYPT m) = m" 
                  "\<forall>c. (c < n) \<longrightarrow> RSAENCRYPT (RSADECRYPT c) = c"

begin

named_theorems v1_5defs
named_theorems v1_5thms
definition k where "k = octet_length n" 

lemma k_bnd: "11 < k" 
  using k_def RSA_mod(2) by fastforce

subsubsection \<open>Section 7.2.1: Encryption Operation\<close>

definition RSAES_PKCS1_v1_5_Encrypt_EM :: "octets \<Rightarrow> octets \<Rightarrow> octets" where
  [v1_5defs]: "RSAES_PKCS1_v1_5_Encrypt_EM PS M = [0,2] @ PS @ [0] @ M"

definition RSAES_PKCS1_v1_5_Encrypt_inputValid :: "octets \<Rightarrow> octets \<Rightarrow> bool" where
  [v1_5defs]: "RSAES_PKCS1_v1_5_Encrypt_inputValid M PS = 
  (let mLen  = length M;
       psLen = length PS
   in  (mLen + 11 \<le> k) \<and> (psLen + mLen + 3 = k) \<and> (8 \<le> psLen) \<and> (\<forall>p \<in> set PS. 0 < p) \<and>
       (octets_valid M) \<and> (octets_valid PS) )" 

definition RSAES_PKCS1_v1_5_Encrypt :: "octets \<Rightarrow> octets \<Rightarrow> octets" where
  [v1_5defs]: "RSAES_PKCS1_v1_5_Encrypt M PS = 
  (let EM = RSAES_PKCS1_v1_5_Encrypt_EM PS M;
       m  = PKCS1_OS2IP EM;
       c  = RSAENCRYPT m
   in  PKCS1_I2OSP c k )" 

lemma RSAES_v1_5_Encrypt_EM_valid:
  assumes "octets_valid M" "octets_valid PS" "EM = RSAES_PKCS1_v1_5_Encrypt_EM PS M"
  shows   "octets_valid EM"
  using assms v1_5defs(1) words_valid_def by auto

lemma RSAES_v1_5_Encrypt_EM_valid2:
  assumes "RSAES_PKCS1_v1_5_Encrypt_inputValid M PS" "EM = RSAES_PKCS1_v1_5_Encrypt_EM PS M"
  shows   "octets_valid EM"
  using assms v1_5defs(2) RSAES_v1_5_Encrypt_EM_valid by meson

lemma RSAES_v1_5_Encrypt_EM_len:
  "length (RSAES_PKCS1_v1_5_Encrypt_EM PS M) = (length PS) + (length M) + 3"
  by (metis One_nat_def v1_5defs(1) Suc_eq_plus1 add.assoc length_append list.size(3,4)
        numeral_3_eq_3 plus_1_eq_Suc)

lemma RSAES_v1_5_Encrypt_EM_stripZero:
  assumes "EM = RSAES_PKCS1_v1_5_Encrypt_EM PS M"
  shows   "words_strip_zero EM = [2] @ PS @ [0] @ M"
  by (simp add: v1_5defs(1) assms)

lemma RSAES_v1_5_Encrypt_EM_stripLen:
  assumes "EM = RSAES_PKCS1_v1_5_Encrypt_EM PS M"
  shows   "length (words_strip_zero EM) = (length PS) + (length M) + 2"
  by (metis assms RSAES_v1_5_Encrypt_EM_stripZero One_nat_def Suc_eq_plus1 add_Suc_right 
        length_append list.size(3,4) numerals(2) plus_1_eq_Suc)

lemma RSAES_v1_5_Encrypt_m_bnd:
  assumes "RSAES_PKCS1_v1_5_Encrypt_inputValid M PS" 
          "EM = RSAES_PKCS1_v1_5_Encrypt_EM PS M" 
          "m  = PKCS1_OS2IP EM"
  shows   "m < n"
proof - 
  let ?mLen  = "length M"
  let ?psLen = "length PS"
  have 1: "(?psLen + ?mLen + 3 = k)" 
    using assms(1) v1_5defs(2) by meson
  have 2: "length (words_strip_zero EM) = k - 1" 
    using 1 RSAES_v1_5_Encrypt_EM_stripLen assms(2) by auto 
  have 3: "octets_valid EM" 
    using assms(1,2) RSAES_v1_5_Encrypt_EM_valid2 by simp
  show ?thesis 
    by (metis 2 3 assms(3) k_def words_valid_def PKCS1_OS2IP_def RSA_mod(1) less_le_trans 
          word_length_eq3 words_strip0_to_nat_len_bnd Twoto8 zero_less_numeral) 
qed

lemma RSAES_v1_5_Encrypt_len:
  assumes "C = RSAES_PKCS1_v1_5_Encrypt M PS"
  shows   "length C = k"
  by (metis I2OSP_valid_len PKCS1_RSAEP_def v1_5defs(3) RSA_bnd(1) assms 
        encryptValidI2OSP k_def less_nat_zero_code mod_less nat_neq_iff power_one_right)

subsubsection \<open>Section 7.2.2: Decryption Operation\<close>

definition RSAES_PKCS1_v1_5_Decode_M :: "octets \<Rightarrow> octets" where 
  [v1_5defs]: "RSAES_PKCS1_v1_5_Decode_M EM = drop 1 (words_strip_nonzero (drop 2 EM))"

definition RSAES_PKCS1_v1_5_Decode_PS :: "octets \<Rightarrow> octets" where
  [v1_5defs]: "RSAES_PKCS1_v1_5_Decode_PS EM = 
  ( let emLen   = length EM;
        M       = RSAES_PKCS1_v1_5_Decode_M EM;
        mLen    = length M;
        psLen   = emLen - mLen - 3
    in  take psLen (drop 2 EM) )"

definition RSAES_PKCS1_v1_5_Decode_validEM :: "octets \<Rightarrow> bool" where 
  [v1_5defs]: "RSAES_PKCS1_v1_5_Decode_validEM EM = 
  ( let emLen   = length EM;
        ZeroTwo = take 2 EM;
        Zero_M  = words_strip_nonzero (drop 2 EM);
        M       = RSAES_PKCS1_v1_5_Decode_M EM;
        mLen    = length M;
        psLen   = emLen - mLen - 3
    in
     (ZeroTwo = [0,2]) \<and> (Zero_M \<noteq> []) \<and> (8 \<le> psLen) )"

definition RSAES_PKCS1_v1_5_Decrypt_inputValid :: "octets \<Rightarrow> bool" where
  [v1_5defs]: "RSAES_PKCS1_v1_5_Decrypt_inputValid C = 
  ( let c  = PKCS1_OS2IP C;
        m  = RSADECRYPT c;
        EM = PKCS1_I2OSP m k
  in (length C = k) \<and> (octets_valid C) \<and> (c < n) \<and> (RSAES_PKCS1_v1_5_Decode_validEM EM) )"

definition RSAES_PKCS1_v1_5_Decrypt :: "octets \<Rightarrow> octets" where
  [v1_5defs]: "RSAES_PKCS1_v1_5_Decrypt C = 
  ( let c  = PKCS1_OS2IP C;
        m  = RSADECRYPT c;
        EM = PKCS1_I2OSP m k
  in RSAES_PKCS1_v1_5_Decode_M EM )"

text \<open>It is convenient to have the following function to recover the padding string from the
ciphertext.  Or just the enocoded message.\<close>
definition RSAES_PKCS1_v1_5_Decrypt_PS :: "octets \<Rightarrow> octets" where
  "RSAES_PKCS1_v1_5_Decrypt_PS C = 
  ( let c  = PKCS1_OS2IP C;
        m  = RSADECRYPT c;
        EM = PKCS1_I2OSP m k
  in RSAES_PKCS1_v1_5_Decode_PS EM )"

definition RSAES_PKCS1_v1_5_Decrypt_EM :: "octets \<Rightarrow> octets" where
  "RSAES_PKCS1_v1_5_Decrypt_EM C = 
  ( let c  = PKCS1_OS2IP C;
        m  = RSADECRYPT c
    in PKCS1_I2OSP m k )"


lemma RSAES_v1_5_Decode_EM:
  assumes "M = RSAES_PKCS1_v1_5_Decode_M EM" 
          "PS = RSAES_PKCS1_v1_5_Decode_PS EM"
          "RSAES_PKCS1_v1_5_Decode_validEM EM"
  shows   "EM = [0,2] @ PS @ [0] @ M"
proof - 
  let ?emLen   = "length EM"
  let ?ZeroTwo = "take 2 EM"
  let ?Zero_M  = "words_strip_nonzero (drop 2 EM)"
  let ?mLen    = "length M"
  let ?psLen   = "?emLen - ?mLen - 3"
  have 1: "?ZeroTwo = [0,2]"     using assms(3) v1_5defs(6) by algebra
  have 2: "M = drop 1 ?Zero_M"   using assms(1) v1_5defs(4) by blast
  have 3: "?Zero_M \<noteq> []"         using assms(3) v1_5defs(6) by algebra
  have 4: "take 1 ?Zero_M = [0]" 
    by (metis 3 strip_non0_head Cons_nth_drop_Suc cancel_comm_monoid_add_class.diff_cancel
          drop0 take0 length_greater_0_conv numerals(1) take_Cons_numeral)
  have 5: "PS = take ?psLen (drop 2 EM)"  using assms(1,2) v1_5defs(5) by presburger
  have 6: "8 \<le> ?psLen"                    using assms(1,3) v1_5defs(6) by algebra
  show ?thesis
    by (metis (mono_tags, lifting) 1 2 4 5 One_nat_def Suc_eq_plus1 append_take_drop_id
          diff_diff_add length_Cons length_append length_drop list.size(3) numeral_2_eq_2
          add.commute numeral_3_eq_3 strip_non0_drop)
qed

lemma RSAES_v1_5_Decode_EM_len:
  assumes "m  = RSADECRYPT c" "EM = PKCS1_I2OSP m k"
  shows   "length EM = k"
  by (metis I2OSP_valid_len PKCS1_I2OSP_inputValid_def RSA_bnd(2) assms k_def less_trans 
        word_length_eq2 Twoto8 zero_less_numeral)

lemma RSAES_v1_5_Decode_EM_valid:
  assumes "EM = PKCS1_I2OSP m k"
  shows   "octets_valid EM"
  by (simp add: I2OSP_octets_valid assms)

lemma RSAES_v1_5_Decode_M_valid:
  assumes "octets_valid EM" "M = RSAES_PKCS1_v1_5_Decode_M EM"
  shows   "octets_valid M"
  by (metis v1_5defs(4) assms in_set_dropD words_valid_def strip_non0_drop)

lemma RSAES_v1_5_Decode_PS_valid:
  assumes "octets_valid EM" "PS = RSAES_PKCS1_v1_5_Decode_PS EM"
  shows   "octets_valid PS"
  by (metis v1_5defs(5) assms in_set_dropD in_set_takeD words_valid_def)

lemma RSAES_v1_5_Decode_PS_nonzero:
  assumes "PS = RSAES_PKCS1_v1_5_Decode_PS EM" "RSAES_PKCS1_v1_5_Decode_validEM EM"
  shows   "\<forall>p \<in> set PS. 0 < p" 
proof - 
  let ?emLen   = "length EM"
  let ?M       = "drop 1 (words_strip_nonzero (drop 2 EM))"
  let ?mLen    = "length ?M"
  let ?psLen   = "?emLen - ?mLen - 3"
  have 1: "PS = take ?psLen (drop 2 EM)"  using assms(1) v1_5defs(4,5) by presburger 
  let ?X = "drop 2 EM"
  let ?Y = "words_strip_nonzero ?X" 
  have 2: "length ?X = ?emLen - 2"        using length_drop by blast 
  have 3: "length ?Y = ?mLen + 1"
    by (metis One_nat_def v1_5defs(6) Suc_eq_plus1 Suc_pred assms(2) length_drop 
          length_greater_0_conv) 
  have 4: "\<forall>i < ((length ?X) - (length ?Y)). 0 < ?X ! i" using strip_non0_leading_pos by blast
  have 5: "(length ?X) - (length ?Y) = ?psLen"           using 2 3 by fastforce
  have 6: "PS = take ?psLen ?X"                          using 1 by fast
  have 7: "\<forall>i < ?psLen. 0 < ?X ! i"                      using 4 5 by presburger
  have 8: "\<forall>i < ?psLen. ?X ! i = PS ! i"                 by (metis 6 nth_take) 
  have 9: "\<forall>i < ?psLen. 0 < PS ! i"                      using 7 8 by algebra
  have 10: "length PS = ?psLen"
    by (metis 5 6 add_diff_cancel_right' append_take_drop_id length_append strip_non0_drop) 
  show ?thesis                                           by (metis 9 10 in_set_conv_nth)
qed

subsubsection \<open>RSAES_PKCS1_v1_5 Lemmas\<close>

lemma RSAES_PKCS1_v1_5_EncryptDecrypt_IntValsMatch [v1_5thms]:
  assumes "RSAES_PKCS1_v1_5_Encrypt_inputValid M PS" 
          "EM  = RSAES_PKCS1_v1_5_Encrypt_EM PS M"
          "m   = PKCS1_OS2IP EM"
          "c   = RSAENCRYPT m"
          "C   = PKCS1_I2OSP c k"
          "c'  = PKCS1_OS2IP C"
          "m'  = RSADECRYPT c'"
          "EM' = PKCS1_I2OSP m' k"
          "M'  = RSAES_PKCS1_v1_5_Decode_M EM'"
  shows   "M = M'  \<and>  EM = EM'  \<and>  m = m'  \<and>  c = c'  \<and>  EM = [0,2] @ PS @ [0] @ M  \<and>
           C = RSAES_PKCS1_v1_5_Encrypt M PS  \<and>  M' = RSAES_PKCS1_v1_5_Decrypt C  \<and>
           M = RSAES_PKCS1_v1_5_Decode_M EM" 
proof - 
  have c:   "c = c'"     by (simp add: I2OSP_OS2IP assms(5,6)) 
  have m:   "m = m'"     using RSA_inv(1) assms(1,2,3,4,7) c RSAES_v1_5_Encrypt_m_bnd by force 
  have EM1: "octets_valid EM"           using assms(1,2) RSAES_v1_5_Encrypt_EM_valid2 by blast
  have EM2: "length EM = k"
    by (metis (no_types) v1_5defs(2) assms(1,2) 
        RSAES_v1_5_Encrypt_EM_len)
  have EM:  "EM = EM'"                  using m EM1 EM2 OS2IP_I2OSP assms(3,8) by fastforce
  have EM3: "EM = [0,2] @ PS @ [0] @ M" using assms(2) v1_5defs(1) by fast
  have M1:  "drop 2 EM = PS @ [0] @ M"  using EM3 by auto
  have M2:  "\<forall>p \<in> set PS. 0 < p"        using assms(1) v1_5defs(2) by meson
  have M3:  "words_strip_nonzero (PS @ [0] @ M) = [0] @ M" 
    using strip_non0_concat M2 by blast
  have M4:  "M = RSAES_PKCS1_v1_5_Decode_M EM" using M1 M3 v1_5defs(4) by simp
  have M:   "M = M'"               using EM M1 M3 assms(9) v1_5defs(4) by simp
  have C1:  "C = RSAES_PKCS1_v1_5_Encrypt M PS" 
    using assms(2,3,4,5) v1_5defs(3) by presburger
  have C2:  "M' = RSAES_PKCS1_v1_5_Decrypt C" 
    using assms(6,7,8,9) v1_5defs(8) by presburger
  show ?thesis using c m EM EM3 M M4 C1 C2 by blast
qed

lemma RSAES_PKCS1_v1_5_Encrypt_validCipher [v1_5thms]:
  assumes "RSAES_PKCS1_v1_5_Encrypt_inputValid M PS"  "C = RSAES_PKCS1_v1_5_Encrypt M PS"
  shows   "RSAES_PKCS1_v1_5_Decrypt_inputValid C"
proof - 
  let ?EM  = "RSAES_PKCS1_v1_5_Encrypt_EM PS M"
  let ?m   = "PKCS1_OS2IP ?EM"
  let ?c   = "RSAENCRYPT ?m"
  let ?C'  = "PKCS1_I2OSP ?c k"
  let ?c'  = "PKCS1_OS2IP ?C'"
  let ?m'  = "RSADECRYPT ?c'"
  let ?EM' = "PKCS1_I2OSP ?m' k"
  let ?M'  = "RSAES_PKCS1_v1_5_Decode_M ?EM'"
  have C1: "C = ?C'"         using assms(2) v1_5defs(3) by presburger
  have C2: "length C = k"    by (simp add: assms(2) RSAES_v1_5_Encrypt_len) 
  have C3: "octets_valid C"  by (simp add: C1 I2OSP_octets_valid) 
  have c:  "?c < n"          using RSA_bnd(1) by blast 
  have EM: "?EM = ?EM'"      using v1_5thms(1) assms(1) by blast
  have EM1: "?EM = [0,2] @ PS @ [0] @ M"  using v1_5defs(1) by blast
  let ?emLen   = "length ?EM"
  let ?ZeroTwo = "take 2 ?EM"
  let ?Zero_M  = "words_strip_nonzero (drop 2 ?EM)"
  let ?mLen    = "length ?M'"
  let ?psLen   = "?emLen - ?mLen - 3"
  have vEM1: "?ZeroTwo = [0,2]"           using EM1 by simp
  have vEM2: "?Zero_M = [0] @ M"
    by (metis EM1 assms(1) One_nat_def v1_5defs(2) Suc_eq_plus1
          append_eq_conv_conj list.size(3,4) numerals(2) strip_non0_concat) 
  have vEM3: "?Zero_M \<noteq> []"               using vEM2 by simp
  have vEM4: "8 \<le> ?psLen" 
    by (metis assms(1) v1_5defs(2) RSAES_v1_5_Encrypt_EM_len v1_5thms(1) add_diff_cancel_right'
          diff_commute) 
  show ?thesis  
    using C1 C2 C3 c EM vEM1 vEM3 vEM4 v1_5defs(6,7) I2OSP_OS2IP by metis
qed

lemma RSAES_PKCS1_v1_5_Encrypt_Decrypt [v1_5thms]:
  assumes "RSAES_PKCS1_v1_5_Encrypt_inputValid M PS"  "C = RSAES_PKCS1_v1_5_Encrypt M PS"
  shows   "RSAES_PKCS1_v1_5_Decrypt C = M"
  by (metis (no_types) assms v1_5thms(1)) 

lemma RSAES_PKCS1_v1_5_DecryptEncrypt_IntValsMatch [v1_5thms]:
  assumes "RSAES_PKCS1_v1_5_Decrypt_inputValid C" 
          "c'  = PKCS1_OS2IP C"
          "m'  = RSADECRYPT c'"
          "EM' = PKCS1_I2OSP m' k"
          "M'  = RSAES_PKCS1_v1_5_Decode_M EM'"
          "PS' = RSAES_PKCS1_v1_5_Decode_PS EM'" 
          "EM  = RSAES_PKCS1_v1_5_Encrypt_EM PS' M'"
          "m   = PKCS1_OS2IP EM"
          "c   = RSAENCRYPT m"
          "C'  = PKCS1_I2OSP c k"
  shows   "C = C' \<and> EM = EM' \<and> m = m' \<and> c = c' \<and> EM = [0,2] @ PS' @ [0] @ M' \<and>
           C' = RSAES_PKCS1_v1_5_Encrypt M' PS' \<and> M' = RSAES_PKCS1_v1_5_Decrypt C" 
proof -
  have EM1: "RSAES_PKCS1_v1_5_Decode_validEM EM'" 
    using assms(1,2,3,4) v1_5defs(7) by meson
  have EM2: "EM = [0,2] @ PS' @ [0] @ M'" using assms(7) v1_5defs(1) by fast
  have EM3: "EM = EM'" using EM1 EM2 RSAES_v1_5_Decode_EM assms(5,6) by presburger 
  have m: "m = m'"     using EM3 I2OSP_OS2IP assms(4,8) by presburger 
  have c: "c = c'"     by (metis m v1_5defs(7) RSA_inv(2) assms(1,2,3,9)) 
  have C: "C = C'"     by (metis (no_types) OS2IP_I2OSP v1_5defs(7) assms(1,2,10) c) 
  have M1: "C' = RSAES_PKCS1_v1_5_Encrypt M' PS'" 
    using assms(7,8,9,10) v1_5defs(3) by presburger
  have M2: "M' = RSAES_PKCS1_v1_5_Decrypt C" 
    using assms(2,3,4,5) v1_5defs(8) by presburger
  show ?thesis         using EM2 EM3 m c C M1 M2 by blast
qed

lemma RSAES_PKCS1_v1_5_Decrypt_validInput [v1_5thms]:
  assumes "M  = RSAES_PKCS1_v1_5_Decrypt C"  "RSAES_PKCS1_v1_5_Decrypt_inputValid C"
          "c  = PKCS1_OS2IP C"  "m = RSADECRYPT c"  "EM = PKCS1_I2OSP m k" 
          "PS = RSAES_PKCS1_v1_5_Decode_PS EM" 
  shows   "RSAES_PKCS1_v1_5_Encrypt_inputValid M PS" 
proof - 
  have Mval: "octets_valid M"
    using I2OSP_octets_valid v1_5defs(8) assms(1) RSAES_v1_5_Decode_M_valid by presburger 
  have PSval: "octets_valid PS"
    using I2OSP_octets_valid assms(5) assms(6) RSAES_v1_5_Decode_PS_valid by force
  have EMval: "RSAES_PKCS1_v1_5_Decode_validEM EM" 
    using assms(2,3,4,5) v1_5defs(7) by meson
  have PSpos: "(\<forall>p \<in> set PS. 0 < p)" using RSAES_v1_5_Decode_PS_nonzero EMval assms(6) by blast
  let ?mLen  = "length M"  
  let ?psLen = "length PS"
  let ?emLen = "length EM"
  have l1: "?emLen = k"              by (simp add: assms(4,5) RSAES_v1_5_Decode_EM_len) 
  have l2: "?psLen = ?emLen - ?mLen - 3" 
    by (metis assms v1_5thms(4) add_diff_cancel_right' diff_commute RSAES_v1_5_Encrypt_EM_len)
  have l3: "8 \<le> ?psLen"              by (metis EMval v1_5defs(6,8) assms(1,3,4,5) l2)
  have l4: "?psLen + ?mLen + 3 = k"  by (metis l1 v1_5thms(4) assms RSAES_v1_5_Encrypt_EM_len) 
  have l5: "?mLen + 11 \<le> k"          using l3 l4 by simp
  show ?thesis                       using Mval PSval PSpos l3 l4 l5 v1_5defs(2) by presburger
qed

lemma RSAES_PKCS1_v1_5_Decrypt_Encrypt [v1_5thms]:
  assumes "RSAES_PKCS1_v1_5_Decrypt_inputValid C"  "RSAES_PKCS1_v1_5_Decrypt C = M"
          "c  = PKCS1_OS2IP C"  "m = RSADECRYPT c"  "EM = PKCS1_I2OSP m k" 
          "PS = RSAES_PKCS1_v1_5_Decode_PS EM" 
  shows   "C = RSAES_PKCS1_v1_5_Encrypt M PS"
  using v1_5thms(4) assms by force

end (*v1_5 locale*)

subsubsection \<open>PSAES_PKCS1_v1_5 Interpretations\<close>
text\<open>We interpret the v1_5 locale for both the basic RSA decryption primitive and the decryption
primitive that uses the Chinese Remainder Theorem.\<close>

locale RSAES_PKCS1_v1_5_Basic = 
  fixes n d p q e :: nat
  assumes RSAkey: "PKCS1_validRSAprivateKey n d p q e" "11 < octet_length n"

begin

interpretation RSAES_PKCS1_v1_5 "PKCS1_RSAEP n e" "PKCS1_RSADP n d" n 
proof - 
 have 1: "0 < n"                using n_positive2 RSAkey(1) ValidKeyDefs(2) by meson
 have 2: "11 < octet_length n"  using RSAkey(2) by blast
 have 3: "\<forall>m. PKCS1_RSAEP n e m < n"
    using 1 PKCS1_RSAEP_messageValid_def encryptValidCiphertext by presburger
 have 4: "\<forall>c. PKCS1_RSADP n d c < n" 
    using 1 PKCS1_RSAEP_messageValid_def encryptValidCiphertext by presburger 
 have 5: "\<forall>m<n. PKCS1_RSADP n d (PKCS1_RSAEP n e m) = m"
    using PKCS1_RSAEP_messageValid_def RSAEP_RSADP RSAkey by presburger
 have 6: "\<forall>c<n. PKCS1_RSAEP n e (PKCS1_RSADP n d c) = c"
    by (meson PKCS1_RSAEP_messageValid_def RSADP_RSAEP RSAkey)
 show "RSAES_PKCS1_v1_5 (PKCS1_RSAVP1 n e) (PKCS1_RSAVP1 n d) n"
   by (simp add: 1 2 3 4 5 6 RSAES_PKCS1_v1_5.intro)
qed

end

locale RSAES_PKCS1_v1_5_CRT = 
  fixes   n p q dP dQ qInv e :: nat
  assumes RSAkey: "PKCS1_validRSAprivateKey_CRT p q dP dQ qInv e" "n = p*q" "11 < octet_length n"

begin

interpretation RSAES_PKCS1_v1_5 "PKCS1_RSAEP n e" "PKCS1_RSADP_CRT p q dP dQ qInv" n 
proof - 
 have 1: "0 < n" by (metis RSAkey(1,2) ValidKeyDefs(3) n_positive2)
 have 2: "11 < octet_length n" using RSAkey(3) by blast
 have 3: "\<forall>m. PKCS1_RSAEP n e m < n"
    using 1 PKCS1_RSAEP_messageValid_def encryptValidCiphertext by presburger
 have 4: "\<forall>c. PKCS1_RSADP_CRT p q dP dQ qInv c < n"
    using PKCS1_RSAEP_messageValid_def RSAkey decryptCRTmessageValid2 by auto 
 have 5: "\<forall>m<n. PKCS1_RSADP_CRT p q dP dQ qInv (PKCS1_RSAEP n e m) = m"
    using PKCS1_RSAEP_messageValid_def RSAEP_RSADP_CRT RSAkey by presburger
 have 6: "\<forall>c<n. PKCS1_RSAEP n e (PKCS1_RSADP_CRT p q dP dQ qInv c) = c"
    using PKCS1_RSAEP_messageValid_def RSADP_CRT_RSAEP RSAkey by auto
 show "RSAES_PKCS1_v1_5 (PKCS1_RSAVP1 n e) (PKCS1_RSADP_CRT p q dP dQ qInv) n"
   using 1 2 3 4 5 6 by (simp add: RSAES_PKCS1_v1_5.intro)
qed

end


section \<open>Section 9: Encoding Methods for Signatures\<close>
text \<open>Definitions in Section 8 depend on definitions in Section 9.  So we include Section 9 first.

"Encoding methods consist of operations that map between octet string messages and octet string 
encoded messages, which are converted to and from integer message representatives in the schemes.
The integer message representatives are processed via the primitives.  The encoding methods thus 
provide the connection between the schemes, which process messages, and the primitives." \<close>


subsection \<open>Section 9.1: EMSA-PSS\<close>

locale EMSA_PSS = 
  fixes MGF  :: mgf_type
    and Hash :: hash_type
    and hLen :: nat
assumes mgf_valid:   "\<forall>x y. octets_valid (MGF x y)"
    and mgf_len:     "\<forall>x y. length (MGF x y) = y"
    and hash_valid:  "\<forall>x. octets_valid (Hash x)"
    and hash_len:    "\<forall>x. length (Hash x) = hLen" 

begin 

subsubsection \<open>Section 9.1.1: Encoding Operation\<close>

definition PKCS1_EMSA_PSS_Encode_inputValid :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  "PKCS1_EMSA_PSS_Encode_inputValid sLen emLen = (hLen + sLen + 2 \<le> emLen)"

definition PKCS1_EMSA_PSS_Encode_M' :
  "PKCS1_EMSA_PSS_Encode_M' mHash salt = (replicate 8 0) @ mHash @ salt"

definition PKCS1_EMSA_PSS_Encode_H :
  "PKCS1_EMSA_PSS_Encode_H M' = Hash M'" 

definition PKCS1_EMSA_PSS_Encode_PS :
  "PKCS1_EMSA_PSS_Encode_PS emLen sLen = replicate (emLen - sLen - hLen - 2) 0"

definition PKCS1_EMSA_PSS_Encode_DB :
  "PKCS1_EMSA_PSS_Encode_DB PS salt = PS @ [1] @ salt"

definition PKCS1_EMSA_PSS_Encode_dbMask :
  "PKCS1_EMSA_PSS_Encode_dbMask H emLen = MGF H (emLen - hLen - 1)" 

definition PKCS1_EMSA_PSS_Encode_maskedDB :
  "PKCS1_EMSA_PSS_Encode_maskedDB DB dbMask = xor_octets DB dbMask"

definition PKCS1_EMSA_PSS_Encode_EM :: "octets \<Rightarrow> octets \<Rightarrow> octets" where 
  "PKCS1_EMSA_PSS_Encode_EM maskedDB_sethi H = maskedDB_sethi @ H @ [0xbc]"

definition PKCS1_EMSA_PSS_Encode ::  "octets \<Rightarrow> octets \<Rightarrow> nat \<Rightarrow> octets" where
  "PKCS1_EMSA_PSS_Encode M salt emBits = 
( let emLen     = numBits_to_numOctets emBits;
      mHash     = Hash M; 
      sLen      = length salt;
      M'        = PKCS1_EMSA_PSS_Encode_M' mHash salt; 
      H         = PKCS1_EMSA_PSS_Encode_H  M'; 
      PS        = PKCS1_EMSA_PSS_Encode_PS emLen sLen;
      DB        = PKCS1_EMSA_PSS_Encode_DB PS salt;
      dbMask    = PKCS1_EMSA_PSS_Encode_dbMask H emLen;
      maskedDB  = PKCS1_EMSA_PSS_Encode_maskedDB DB dbMask;
      maskedDB' = SetLeftmostBits emLen emBits maskedDB 
  in
      PKCS1_EMSA_PSS_Encode_EM maskedDB' H )"

subsubsection \<open>Section 9.1.2: Verification Operation\<close>

definition PKCS1_EMSA_PSS_Verify_maskedDB :
  "PKCS1_EMSA_PSS_Verify_maskedDB emLen EM = take (emLen - hLen - 1) EM"

definition PKCS1_EMSA_PSS_Verify_H :
  "PKCS1_EMSA_PSS_Verify_H emLen EM = take hLen (drop (emLen - hLen - 1) EM)"

definition PKCS1_EMSA_PSS_Verify_dbMask : 
  "PKCS1_EMSA_PSS_Verify_dbMask H emLen = MGF H (emLen - hLen - 1)"

definition PKCS1_EMSA_PSS_Verify_DB : 
  "PKCS1_EMSA_PSS_Verify_DB maskedDB dbMask = xor_octets maskedDB dbMask"

definition PKCS1_EMSA_PSS_Verify_PS_0x01 : 
  "PKCS1_EMSA_PSS_Verify_PS_0x01 emLen sLen DB_sethi = 
     PKCS1_OS2IP (take (emLen - hLen - sLen -1) DB_sethi)"

definition PKCS1_EMSA_PSS_Verify_salt : 
  "PKCS1_EMSA_PSS_Verify_salt emLen sLen DB_sethi = drop (emLen - hLen - sLen - 1) DB_sethi" 

definition PKCS1_EMSA_PSS_Verify_M' : 
  "PKCS1_EMSA_PSS_Verify_M' mHash salt = (replicate 8 0) @ mHash @ salt"

definition PKCS1_EMSA_PSS_Verify_H' : 
  "PKCS1_EMSA_PSS_Verify_H' M' = Hash M'"

definition PKCS1_EMSA_PSS_Verify :: "nat \<Rightarrow> octets \<Rightarrow> octets \<Rightarrow> nat \<Rightarrow> bool" where
  "PKCS1_EMSA_PSS_Verify sLen M EM emBits = 
( let emLen    = numBits_to_numOctets emBits;
      mHash    = Hash M;
      maskedDB = PKCS1_EMSA_PSS_Verify_maskedDB emLen EM;
      H        = PKCS1_EMSA_PSS_Verify_H        emLen EM;
      dbMask   = PKCS1_EMSA_PSS_Verify_dbMask   H emLen;
      DB       = PKCS1_EMSA_PSS_Verify_DB       maskedDB dbMask;
      DB'      = SetLeftmostBits                emLen emBits DB;
      PS_0x01  = PKCS1_EMSA_PSS_Verify_PS_0x01  emLen sLen DB';
      salt     = PKCS1_EMSA_PSS_Verify_salt     emLen sLen DB';
      M'       = PKCS1_EMSA_PSS_Encode_M'       mHash salt;
      H'       = PKCS1_EMSA_PSS_Encode_H        M'
  in
    (length EM = emLen) \<and> (hLen + sLen + 2 \<le> emLen) \<and> (last EM = 0xbc) \<and> PS_0x01 = 1 \<and> (H = H') \<and>
    (TestLeftmostBits emLen emBits maskedDB)  )" 


subsubsection \<open>EMSA-PSS Lemmas\<close>

lemma EMSA_PSS_Encode_M'_valid:
  assumes "octets_valid mHash"  "octets_valid salt"  "M' = PKCS1_EMSA_PSS_Encode_M' mHash salt"
  shows   "octets_valid M'"
  by (metis assms PKCS1_EMSA_PSS_Encode_M' words_valid_concat words_valid_zeros)

lemma EMSA_PSS_Encode_M'_len:
  assumes "length mHash = hLen"  "length salt = sLen"  "M' = PKCS1_EMSA_PSS_Encode_M' mHash salt"
  shows   "length M' = 8 + hLen + sLen"
  by (simp add: assms PKCS1_EMSA_PSS_Encode_M')  

lemma EMSA_PSS_Encode_H_valid:
  assumes "H = PKCS1_EMSA_PSS_Encode_H M'"
  shows   "octets_valid H"
  using assms PKCS1_EMSA_PSS_Encode_H hash_valid by presburger

lemma EMSA_PSS_Encode_H_len:
  assumes "H = PKCS1_EMSA_PSS_Encode_H M'"
  shows   "length H = hLen"
  using assms PKCS1_EMSA_PSS_Encode_H hash_len by presburger

lemma EMSA_PSS_Encode_PS_valid:
  assumes "PS = PKCS1_EMSA_PSS_Encode_PS emLen sLen"
  shows   "octets_valid PS" 
  using assms words_valid_zeros PKCS1_EMSA_PSS_Encode_PS by metis

lemma EMSA_PSS_Encode_PS_len:
  assumes "PS = PKCS1_EMSA_PSS_Encode_PS emLen sLen"
  shows   "length PS = emLen - sLen - hLen - 2" 
  by (simp add: assms PKCS1_EMSA_PSS_Encode_PS) 

lemma EMSA_PSS_Encode_DB_valid:
  assumes "octets_valid PS"  "octets_valid salt"  "DB = PKCS1_EMSA_PSS_Encode_DB PS salt"
  shows   "octets_valid DB"
  by (metis assms PKCS1_EMSA_PSS_Encode_DB words_valid_concat words_valid_cons 
            words_valid_nil one_less_numeral_iff semiring_norm(76) Twoto8) 

lemma EMSA_PSS_Encode_DB_len:
  assumes "length PS = emLen - sLen - hLen - 2"  "length salt = sLen" 
          "DB = PKCS1_EMSA_PSS_Encode_DB PS salt" "PKCS1_EMSA_PSS_Encode_inputValid sLen emLen"
  shows   "length DB = emLen - hLen - 1" 
proof - 
  have 1: "hLen + sLen + 2 \<le> emLen" using assms(4) PKCS1_EMSA_PSS_Encode_inputValid_def by blast
  have 2: "length DB = (length PS) + 1 + (length salt)" 
    by (simp add: assms(3) PKCS1_EMSA_PSS_Encode_DB) 
  show ?thesis  using 1 2 assms(1,2) by simp
qed

lemma EMSA_PSS_Encode_DB_hibits:
  assumes "emLen = numBits_to_numOctets emBits"  "PS = PKCS1_EMSA_PSS_Encode_PS emLen sLen"
          "DB = PKCS1_EMSA_PSS_Encode_DB PS salt"
  shows   "TestLeftmostBits emLen emBits DB"
proof - 
  have 1: "DB = PS @ [1] @ salt" using assms(3) PKCS1_EMSA_PSS_Encode_DB by blast
  let ?x = "8*emLen - emBits" 
  have 2: "?x < 8 \<and> 0 \<le> ?x"      using emLen_emBits assms(1) by blast
  let ?y = "8 - ?x"
  have 3: "1 \<le> ?y \<and> ?y \<le> 8"      using 2 by force
  have 4: "2^1 \<le> (2::nat)^?y"    using 3 one_le_numeral power_increasing by blast 
  have 5: "(2::nat) \<le> 2^?y"      using 4 by force
  have 6: "(1::nat) < 2^?y"      using 5 by fastforce
  let ?h = "hd DB"  
  show ?thesis
  proof (cases "PS = []")
    case True
    then have "?h = 1"  using 1 by simp 
    then show ?thesis   using 6 TestLeftmostBits_def by algebra
  next
    case False
    then have "?h = 0"
      by (metis 1 assms(2) PKCS1_EMSA_PSS_Encode_PS EMSA_PSS_Encode_PS_len hd_append 
            hd_replicate length_0_conv) 
  then show ?thesis     using 6 TestLeftmostBits_def by presburger
  qed
qed

lemma EMSA_PSS_Encode_dbMask_valid:
  assumes "dbMask = PKCS1_EMSA_PSS_Encode_dbMask H emLen"
  shows   "octets_valid dbMask"
  using assms PKCS1_EMSA_PSS_Encode_dbMask mgf_valid by presburger

lemma EMSA_PSS_Encode_dbMask_len:
  assumes "dbMask = PKCS1_EMSA_PSS_Encode_dbMask H emLen"
  shows   "length dbMask = emLen - hLen - 1"
  using assms PKCS1_EMSA_PSS_Encode_dbMask mgf_len by presburger

lemma EMSA_PSS_Encode_maskedDB_valid:
  assumes "maskedDB = PKCS1_EMSA_PSS_Encode_maskedDB DB dbMask"
          "octets_valid DB" "octets_valid dbMask"
  shows   "octets_valid maskedDB"
  by (simp add: PKCS1_EMSA_PSS_Encode_maskedDB assms xor_valid_words)

lemma EMSA_PSS_Encode_maskedDB_len:
  assumes "maskedDB = PKCS1_EMSA_PSS_Encode_maskedDB DB dbMask"
          "length DB = x" "length dbMask = x"
  shows   "length maskedDB = x"
  by (simp add: PKCS1_EMSA_PSS_Encode_maskedDB assms xor_words_length)

lemma EMSA_PSS_Encode_maskedDB_sethi_valid:
  assumes "octets_valid maskedDB"
  shows   "octets_valid (SetLeftmostBits emLen emBits maskedDB)"
  by (simp add: SetLeftmostBits_valid assms)

lemma EMSA_PSS_Encode_maskedDB_sethi_len:
  "length (SetLeftmostBits emLen emBits maskedDB) = length maskedDB"
  by (simp add: SetLeftmostBits_len)

lemma EMSA_PSS_Encode_maskedDB_sethi_hd:
  assumes "maskedDB_sethi = SetLeftmostBits emLen emBits maskedDB" 
          "maskedDB \<noteq> []"
  shows   "hd maskedDB_sethi < 2^(8- (8*emLen - emBits))"
  using SetLeftmostBits_hd assms by presburger

lemma EMSA_PSS_Encode_EM_valid:
  assumes "octets_valid maskedDB"  "octets_valid H"  "EM = PKCS1_EMSA_PSS_Encode_EM maskedDB H"
  shows   "octets_valid EM"
proof - 
  have "(0xbc::nat) < 256" by auto
  then show ?thesis 
    using words_valid_concat PKCS1_EMSA_PSS_Encode_EM_def assms words_valid_cons words_valid_nil
          Twoto8 by presburger 
qed

lemma EMSA_PSS_Encode_EM_len:
  assumes "length maskedDB = emLen - hLen - 1"  "length H = hLen" 
          "EM = PKCS1_EMSA_PSS_Encode_EM maskedDB H"  "PKCS1_EMSA_PSS_Encode_inputValid sLen emLen"
  shows   "length EM = emLen"
proof -
  have 1: "hLen + sLen + 2 \<le> emLen" using assms(4) PKCS1_EMSA_PSS_Encode_inputValid_def by blast
  have 2: "hLen + 1 < emLen"        using 1 by auto
  have 3: "length EM = (length maskedDB) + (length H) + 1"
    using assms(3) PKCS1_EMSA_PSS_Encode_EM_def by simp
  show ?thesis  using 2 3 assms(1,2) by fastforce
qed

text \<open>In the following, we collect up all the facts we know about the intermediate values
computed in the EMAS_PSS_Encode operation.\<close>
lemma EMSA_PSS_Encode_IntVals:
  assumes "PKCS1_EMSA_PSS_Encode_inputValid sLen emLen"  "octets_valid salt"
          "emLen     = numBits_to_numOctets emBits"
          "mHash     = Hash M" 
          "sLen      = length salt"
          "M'        = PKCS1_EMSA_PSS_Encode_M' mHash salt"
          "H         = PKCS1_EMSA_PSS_Encode_H M'" 
          "PS        = PKCS1_EMSA_PSS_Encode_PS emLen sLen"
          "DB        = PKCS1_EMSA_PSS_Encode_DB PS salt" 
          "dbMask    = PKCS1_EMSA_PSS_Encode_dbMask H emLen" 
          "maskedDB  = PKCS1_EMSA_PSS_Encode_maskedDB DB dbMask" 
          "maskedDB' = SetLeftmostBits emLen emBits maskedDB"
          "DB'       = SetLeftmostBits emLen emBits DB"
          "dbMask'   = SetLeftmostBits emLen emBits dbMask"
          "EM        = PKCS1_EMSA_PSS_Encode_EM maskedDB' H"
   shows  "octets_valid mHash       \<and> length mHash     = hLen \<and> 
           octets_valid M'          \<and> length M'        = 8 + hLen + sLen \<and>
           octets_valid H           \<and> length H         = hLen \<and>
           octets_valid PS          \<and> length PS        = emLen - sLen - hLen - 2 \<and>
           octets_valid DB          \<and> length DB        = emLen - hLen - 1 \<and> 
           octets_valid dbMask      \<and> length dbMask    = emLen - hLen - 1 \<and>
           octets_valid maskedDB    \<and> length maskedDB  = emLen - hLen - 1 \<and>
           octets_valid maskedDB'   \<and> length maskedDB' = emLen - hLen - 1 \<and>
           octets_valid EM          \<and> length EM        = emLen \<and>
           EM = PKCS1_EMSA_PSS_Encode M salt emBits \<and> last EM = 0xbc \<and> 
           bit_length (PKCS1_OS2IP EM) \<le> emBits"
proof -
  have mH1: "octets_valid mHash"  by (simp add: assms(4) hash_valid) 
  have mH2: "length mHash = hLen" by (simp add: assms(4) hash_len) 
  have M1:  "octets_valid M'"     using EMSA_PSS_Encode_M'_valid assms(2,6) mH1 by presburger 
  have M2:  "length M' = 8 + hLen + sLen"  using EMSA_PSS_Encode_M'_len assms(5,6) mH2 by blast 
  have H1:  "octets_valid H"      by (simp add: EMSA_PSS_Encode_H_valid assms(7)) 
  have H2:  "length H = hLen"     by (simp add: EMSA_PSS_Encode_H_len assms(7)) 
  have PS1: "octets_valid PS"     by (simp add: EMSA_PSS_Encode_PS_valid assms(8))         
  have PS2: "length PS = emLen - sLen - hLen - 2"  by (simp add: EMSA_PSS_Encode_PS_len assms(8))
  have PS3: "octets_to_nat PS = 0" 
    by (metis assms(8) PKCS1_EMSA_PSS_Encode_PS words_to_nat_prepend_zeros append_Nil2 
             words_to_nat_empty) 
  have DB1: "octets_valid DB"     using EMSA_PSS_Encode_DB_valid PS1 assms(2,9) by blast         
  have DB2: "length DB = emLen - hLen - 1"  using EMSA_PSS_Encode_DB_len PS2 assms(1,5,9) by blast
  have DB3: "DB \<noteq> []" 
    by (metis Nil_is_append_conv PKCS1_EMSA_PSS_Encode_DB assms(9) list.distinct(1)) 
  have DB4: "hd DB' < 2^(8 - (8*emLen - emBits))"
    using DB3 SetLeftmostBits_hd assms(13) by presburger
  have DB5: "DB = PS @ [1] @ salt"
    by (simp add: PKCS1_EMSA_PSS_Encode_DB assms(9))
  have DB6: "take (emLen - hLen - sLen -1) DB = PS @ [1]"
    using DB5 PS2 DB2 assms(5) by auto
  have DB7: "PKCS1_OS2IP (PS @ [1]) = 1" 
    using words_to_nat_prepend_zeros assms(8) PKCS1_OS2IP_def one_word_to_nat
    by (simp add: PKCS1_EMSA_PSS_Encode_PS) 
  have DB8: "PKCS1_EMSA_PSS_Verify_PS_0x01 emLen sLen DB = 1"
    using DB6 DB7 PKCS1_EMSA_PSS_Verify_PS_0x01 by presburger
  have DB9: "TestLeftmostBits emLen emBits DB"
    using EMSA_PSS_Encode_DB_hibits assms(3,8,9) by blast
  have DB10: "DB = DB'"             using DB9 SetTestLeftmostBits assms(13) by simp
  have dbM1: "octets_valid dbMask"  by (simp add: EMSA_PSS_Encode_dbMask_valid assms(10)) 
  have dbM2: "length dbMask = emLen - hLen - 1" 
    using EMSA_PSS_Encode_dbMask_len assms(10) by presburger 
  have dbM3: "dbMask \<noteq> []"          using DB2 DB3 dbM2 by force 
  have dbM4: "hd dbMask' < 2^(8 - (8*emLen - emBits))"
    using dbM3 SetLeftmostBits_hd assms(14) by presburger
  have mDB1: "octets_valid maskedDB" 
    using assms(11) EMSA_PSS_Encode_maskedDB_valid DB1 dbM1 by blast
  have mDB2: "length maskedDB = emLen - hLen - 1" 
    using assms(11) EMSA_PSS_Encode_maskedDB_len DB2 dbM2 by blast
  have mDB3: "maskedDB \<noteq> []"        using DB2 DB3 mDB2 by fastforce
  have mDBsh1: "octets_valid maskedDB'"
    by (simp add: EMSA_PSS_Encode_maskedDB_sethi_valid assms(12) mDB1)
  have mDBsh2: "length maskedDB' = emLen - hLen - 1"
    using EMSA_PSS_Encode_maskedDB_sethi_len assms(12) mDB2 by presburger
  have mDBsh3: "hd maskedDB' < 2^(8 - (8*emLen - emBits))" 
    using assms(12) mDB3 EMSA_PSS_Encode_maskedDB_sethi_hd by blast
  have mDBsh4: "maskedDB = xor_octets DB dbMask"
    by (simp add: PKCS1_EMSA_PSS_Encode_maskedDB assms(11))
  have mDBsh5: "length DB = length dbMask"  using DB2 dbM2 by argo
  have mDBsh6: "maskedDB' = xor_octets DB' dbMask'"
    using assms(12,13,14) mDBsh4 mDBsh5 SetLeftmostBits_xor[of DB dbMask emLen emBits] by fast
  have mDBsh7: "maskedDB' = xor_octets DB dbMask'"
    using mDBsh6 DB10 by blast
  have mDBsh8: "TestLeftmostBits emLen emBits maskedDB'"
    using TestLeftmostBits_def mDBsh3 by presburger 
  have EM1:  "octets_valid EM"    using EMSA_PSS_Encode_EM_valid H1 assms(15) mDBsh1 by blast  
  have EM2: "length EM = emLen"   using EMSA_PSS_Encode_EM_len H2 assms(1,15) mDBsh2 by blast 
  have EM3: "EM = PKCS1_EMSA_PSS_Encode M salt emBits" 
    by (metis assms(3,4,5,6,7,8,9,10,11,12,15) PKCS1_EMSA_PSS_Encode_def)
  have EM4: "last EM = 0xbc"      by (simp add: PKCS1_EMSA_PSS_Encode_EM_def assms(15))
  have EM5: "EM \<noteq> []"             using DB2 DB3 EM2 by force
  have EM6: "hd EM = hd maskedDB'"
    by (metis DB2 DB3 PKCS1_EMSA_PSS_Encode_EM_def assms(15) hd_append2 length_0_conv mDBsh2) 
  have EM7: "TestLeftmostBits emLen emBits EM" using EM6 TestLeftmostBits_def mDBsh3 by presburger
  let ?n = "octets_to_nat EM"
  have n: "?n = PKCS1_OS2IP EM"                using PKCS1_OS2IP_def by presburger
  have EM8: "bit_length (?n) \<le> emBits" 
    using setleftmost_bit_len3[of emLen emBits EM ?n] assms(3) EM1 EM2 EM5 EM7 by presburger
  have EM9: "bit_length (PKCS1_OS2IP EM) \<le> emBits"  using n EM8 by presburger
  show ?thesis 
    using mH1 mH2 M1 M2 H1 H2 PS1 PS2 DB1 DB2 DB4 DB8 DB9 DB10 dbM1 dbM2 dbM4 mDB1 
    mDB2 mDB3 mDBsh1 mDBsh2 mDBsh3 mDBsh6 mDBsh7 mDBsh8 EM1 EM2 EM3 EM4 EM7 EM9 by blast
qed

lemma EMSA_PSS_Encode_Verify_IntValsMatch:
  assumes "PKCS1_EMSA_PSS_Encode_inputValid sLen emLen"  "octets_valid salt"
          "emLen      = numBits_to_numOctets emBits"
          "mHash      = Hash M" 
          "sLen       = length salt"
          "M'         = PKCS1_EMSA_PSS_Encode_M' mHash salt"
          "H          = PKCS1_EMSA_PSS_Encode_H M'" 
          "PS         = PKCS1_EMSA_PSS_Encode_PS emLen sLen"
          "DB         = PKCS1_EMSA_PSS_Encode_DB  PS salt" 
          "DB'        = SetLeftmostBits emLen emBits DB" 
          "dbMask     = PKCS1_EMSA_PSS_Encode_dbMask H emLen" 
          "dbMask'    = SetLeftmostBits emLen emBits dbMask" 
          "maskedDB   = PKCS1_EMSA_PSS_Encode_maskedDB DB dbMask" 
          "maskedDB'  = SetLeftmostBits emLen emBits maskedDB" 
          "EM         = PKCS1_EMSA_PSS_Encode_EM maskedDB' H"
          "vmaskedDB  = PKCS1_EMSA_PSS_Verify_maskedDB emLen EM"
          "vmaskedDB' = SetLeftmostBits emLen emBits vmaskedDB" 
          "vH         = PKCS1_EMSA_PSS_Verify_H emLen EM"
          "vdbMask    = PKCS1_EMSA_PSS_Verify_dbMask vH emLen"
          "vdbMask'   = SetLeftmostBits emLen emBits vdbMask" 
          "vDB        = PKCS1_EMSA_PSS_Verify_DB vmaskedDB vdbMask"
          "vDB'       = SetLeftmostBits emLen emBits vDB"
          "PS_0x01    = PKCS1_EMSA_PSS_Verify_PS_0x01 emLen sLen vDB'"
          "vsalt      = PKCS1_EMSA_PSS_Verify_salt emLen sLen vDB'"
          "vM'        = PKCS1_EMSA_PSS_Encode_M' mHash vsalt"
          "vH'        = PKCS1_EMSA_PSS_Encode_H vM'"
    shows "maskedDB' = vmaskedDB \<and> H = vH \<and> dbMask = vdbMask \<and> DB = vDB' \<and> PS_0x01 = 1 \<and> 
           salt = vsalt \<and> M' = vM' \<and> vH' = H"
proof - 
  have EM1: "EM = maskedDB' @ H @ [0xbc]" 
    using PKCS1_EMSA_PSS_Encode_EM_def assms(15) by presburger
  have mDB1: "length maskedDB = emLen - hLen - 1"
    using EMSA_PSS_Encode_IntVals assms(1,2,3,4,5,6,7,8,9,11,13) by blast 
  have mDB2: "maskedDB' = vmaskedDB"
    by (simp add: EM1 PKCS1_EMSA_PSS_Verify_maskedDB SetLeftmostBits_len assms(14,16) mDB1) 
  have mDB3: "vmaskedDB = vmaskedDB'" 
    using mDB2 SetLeftmostBits_idem assms(14,17) by auto 
  have H1: "H = vH"
    by (simp add: EM1 PKCS1_EMSA_PSS_Encode_H PKCS1_EMSA_PSS_Verify_H SetLeftmostBits_len 
                  assms(7,14,18) hash_len mDB1) 
  have dbM1: "dbMask = vdbMask"
    using H1 PKCS1_EMSA_PSS_Encode_dbMask PKCS1_EMSA_PSS_Verify_dbMask assms(11,19) by presburger 
  have dbM2: "dbMask' = vdbMask'" using dbM1 assms(12,20) by blast
  have DB0: "DB = DB'"
    by (simp add: EMSA_PSS_Encode_DB_hibits SetTestLeftmostBits assms(3,8,9,10)) 
  have DB1: "maskedDB = xor_octets DB dbMask"
    by (simp add: PKCS1_EMSA_PSS_Encode_maskedDB assms(13))
  have DB2: "length DB = length dbMask"
    using EMSA_PSS_Encode_IntVals EMSA_PSS_Encode_dbMask_len assms(1,2,3,5,8,9,11) 
    by presburger 
  have DB3: "DB = xor_octets maskedDB dbMask"
    using DB1 DB2 words_xor_inv xor_words_symm by presburger
  have DB4: "DB' = xor_octets maskedDB' dbMask'"
    by (simp add: EMSA_PSS_Encode_dbMask_len SetLeftmostBits_xor assms(10,11,12,14) mDB1 DB3) 
  have DB5: "DB' = xor_octets vmaskedDB' vdbMask'" using DB4 mDB2 mDB3 dbM1 dbM2 by argo
  have DB6: "vDB = xor_octets vmaskedDB vdbMask"
    by (simp add: PKCS1_EMSA_PSS_Verify_DB assms(21))
  have DB7: "vDB' = xor_octets vmaskedDB' vdbMask'" 
    using DB6 SetLeftmostBits_xor DB2 EMSA_PSS_Encode_maskedDB_len SetLeftmostBits_len 
          assms(13,14,17,20,22) dbM1 mDB2 by auto 
  have DB8: "DB' = vDB'" using DB5 DB7 by fast
  have DB9: "DB = vDB'" using DB0 DB8 by fast
  have DB10: "DB = PS @ [1] @ salt" by (simp add: PKCS1_EMSA_PSS_Encode_DB assms(9))
  have s: "salt = vsalt" 
    by (metis (no_types, lifting) EMSA_PSS_Encode_maskedDB_len PKCS1_EMSA_PSS_Verify_salt 
        add.commute add_diff_cancel_right' append.assoc append_eq_conv_conj diff_diff_left 
        length_append assms(5,13,24) DB2 mDB1 DB9 DB10) 
  have M: "M' = vM'" using s assms(6,25) by metis
  have H1: "vH' = H" using M assms(7,26) by argo
  have H2: "H = vH"
    by (simp add: EM1 PKCS1_EMSA_PSS_Encode_H PKCS1_EMSA_PSS_Verify_H SetLeftmostBits_len 
        assms(7,14,18) hash_len mDB1) 
  have PS1: "PS_0x01 = PKCS1_OS2IP(PS @ [1])"
    by (smt (verit, del_insts) DB10 DB2 DB9 mDB1 assms(5,13,23) EMSA_PSS_Encode_maskedDB_len 
    PKCS1_EMSA_PSS_Verify_PS_0x01 add_diff_cancel_right' append.assoc append_eq_conv_conj 
    cancel_ab_semigroup_add_class.diff_right_commute length_append )
  have PS2: "PS_0x01 = 1" using PS1
    by (simp add: PKCS1_EMSA_PSS_Encode_PS PKCS1_OS2IP_def assms(8) words_to_nat_prepend_zeros) 
  show ?thesis using H1 H2 M s mDB2 dbM1 DB9 PS2 by blast
qed

lemma PKCS1_EMSA_PSS_Encode_Verify:
  assumes "EM = PKCS1_EMSA_PSS_Encode M salt emBits"  "sLen = length salt"  "octets_valid salt"
          "PKCS1_EMSA_PSS_Encode_inputValid sLen emLen"  "emLen = numBits_to_numOctets emBits"
  shows   "PKCS1_EMSA_PSS_Verify sLen M EM emBits"
proof - 
  have EM1: "length EM = emLen"     using assms EMSA_PSS_Encode_IntVals by force
  have l: "hLen + sLen + 2 \<le> emLen" using assms(4) PKCS1_EMSA_PSS_Encode_inputValid_def by blast
  have EM2: "last EM = 0xbc"        using EMSA_PSS_Encode_IntVals assms by force
  let ?mHash    = "Hash M"
  let ?maskedDB = "PKCS1_EMSA_PSS_Verify_maskedDB emLen EM"
  let ?H        = "PKCS1_EMSA_PSS_Verify_H        emLen EM"
  let ?dbMask   = "PKCS1_EMSA_PSS_Verify_dbMask   ?H emLen"
  let ?DB       = "PKCS1_EMSA_PSS_Verify_DB       ?maskedDB ?dbMask"
  let ?DB'      = "SetLeftmostBits emLen emBits ?DB"
  let ?PS_0x01  = "PKCS1_EMSA_PSS_Verify_PS_0x01  emLen sLen ?DB'"
  let ?salt     = "PKCS1_EMSA_PSS_Verify_salt     emLen sLen ?DB'"
  let ?M'       = "PKCS1_EMSA_PSS_Encode_M'       ?mHash salt"
  let ?H'       = "PKCS1_EMSA_PSS_Encode_H        ?M'"
  have PS: "?PS_0x01 = 1"
    by (metis EMSA_PSS_Encode_Verify_IntValsMatch PKCS1_EMSA_PSS_Encode_def assms) 
  have H: "?H = ?H'"
    by (metis (no_types) EMSA_PSS_Encode_Verify_IntValsMatch PKCS1_EMSA_PSS_Encode_def assms)
  have mDB: "TestLeftmostBits emLen emBits ?maskedDB"
    by (metis assms TestLeftmostBits_def EMSA_PSS_Encode_Verify_IntValsMatch 
              PKCS1_EMSA_PSS_Encode_def SetLeftmostBits_hd SetTestLeftmostBits)
  show ?thesis using EM1 EM2 l PS H mDB PKCS1_EMSA_PSS_Verify_def[of sLen M EM emBits] 
    by (metis EMSA_PSS_Encode_Verify_IntValsMatch PKCS1_EMSA_PSS_Encode_def assms)
qed
    

end (* of locale EMSA *)

subsection \<open>Section 9.2: EMSA-PKCS1-v1_5\<close>
text \<open>"This encoding method is deterministic and only has an encoding operation."

The algorithmID for the nine hash functions mentioned in Appendix B.1 are given on page 40 of the
standard.  We include them in section B.1 of this theory.
\<close>

locale EMSA_v1_5 = 
  fixes Hash        :: hash_type
    and hLen        :: nat
    and algorithmID :: octets
assumes hash_valid:  "\<forall>x. octets_valid (Hash x)"
    and hash_len:    "\<forall>x. length (Hash x) = hLen" 
    and IDvalid:     "octets_valid algorithmID"
begin

definition PKCS1_EMSA_v1_5_Encode_inputValid :: "octets \<Rightarrow> nat \<Rightarrow> bool" where
  "PKCS1_EMSA_v1_5_Encode_inputValid M emLen = 
(  let H    = Hash M;
       T    = algorithmID @ H;
       tLen = length T;
       PS   = replicate (emLen - tLen - 3) (0xff::nat)
    in (tLen + 11 \<le> emLen) \<and> (8 \<le> length PS) )" 

definition PKCS1_EMSA_v1_5_Encode :: "octets \<Rightarrow> nat \<Rightarrow> octets" where
  "PKCS1_EMSA_v1_5_Encode M emLen = 
(  let H    = Hash M;
       T    = algorithmID @ H;
       tLen = length T;
       PS   = replicate (emLen - tLen - 3) (0xff::nat)
    in [0, 1] @ PS @ [0] @ T )" 

text \<open>Only having an encoding method means that there's not a whole lot that we might prove about
it.  The one thing we can show is that given valid input, the length of the result of decoding
is known. We also know that the encoded message has valid octets.\<close>
lemma PKCS1_EMSA_v1_5_Encode_valid_len:
  assumes "PKCS1_EMSA_v1_5_Encode_inputValid M emLen"  "EM = PKCS1_EMSA_v1_5_Encode M emLen"
  shows   "length EM = emLen"
proof - 
  let ?H     = "Hash M" 
  let ?T     = "algorithmID @ ?H"
  let ?tLen  = "length ?T"
  let ?PS    = "replicate (emLen - ?tLen - 3) (0xff::nat)"
  let ?psLen = "length ?PS" 
  have 1: "(?tLen + 11 \<le> emLen) \<and> (8 \<le> ?psLen)" 
    using assms(1) PKCS1_EMSA_v1_5_Encode_inputValid_def by meson
  have 2: "EM = [0, 1] @ ?PS @ [0] @ ?T"    using assms(2) PKCS1_EMSA_v1_5_Encode_def by meson
  have 3: "length EM = 3 + ?psLen + ?tLen"  using 2 by auto
  have 4: "?psLen = emLen - ?tLen - 3"      by simp
  show ?thesis                              using 1 3 4 by presburger
qed

lemma PKCS1_EMSA_v1_5_Encode_octetsValid:
  assumes "EM = PKCS1_EMSA_v1_5_Encode M emLen"
  shows   "octets_valid EM"
proof -
  let ?H    = "Hash M"
  let ?T    = "algorithmID @ ?H"
  let ?tLen = "length ?T"
  let ?PS   = "replicate (emLen - ?tLen - 3) (0xff::nat)"
  have 1: "EM = [0, 1] @ ?PS @ [0] @ ?T"  by (metis (no_types) PKCS1_EMSA_v1_5_Encode_def assms)
  have 2: "octets_valid ?PS"              by (simp add: words_valid_def)
  have 3: "octets_valid [0,1] \<and> octets_valid [0]"  by (simp add: words_valid_def)
  have 4: "octets_valid ?T"               by (simp add: IDvalid hash_valid words_valid_concat) 
  show ?thesis                            using 1 2 3 4 words_valid_concat by presburger 
qed
  

text \<open>Well, I suppose we could unwrap the encoding.  It's obvious so maybe that's why the standard
did not bother to write it down.  We provide two different forms.\<close>
lemma PKCS1_EMSA_v1_5_Decode:
  assumes "EM = PKCS1_EMSA_v1_5_Encode M emLen" 
  shows   "Hash M = drop (1+(length algorithmID)) (words_strip_nonzero (drop 2 EM))"
proof - 
  let ?H    = "Hash M" 
  let ?T    = "algorithmID @ ?H"
  let ?tLen = "length ?T"
  let ?PS   = "replicate (emLen - ?tLen - 3) (0xff::nat)"
  have 0: "EM = [0, 1] @ ?PS @ [0] @ ?T"  using assms PKCS1_EMSA_v1_5_Encode_def by meson
  have 1: "\<forall>p \<in> set ?PS. 0 < p"           by fastforce
  have 2: "drop 2 EM = ?PS @ [0] @ ?T"    using 0 by auto
  have 3: "words_strip_nonzero (drop 2 EM) = [0] @ ?T"  using 2 strip_non0_concat by force
  show ?thesis                            using 3 by simp
qed

lemma PKCS1_EMSA_v1_5_Decode2:
  assumes "EM = PKCS1_EMSA_v1_5_Encode M emLen"  "PKCS1_EMSA_v1_5_Encode_inputValid M emLen"
          "H = Hash M"  "hLen = length H" 
  shows   "H = drop (emLen - hLen) EM"
proof - 
  let ?aLen = "length algorithmID"
  let ?T    = "algorithmID @ H"
  let ?tLen = "length ?T"
  have T: "?tLen = ?aLen + hLen"                    using assms(4) by simp
  let ?PS   = "replicate (emLen - ?tLen - 3) (0xff::nat)"
  have EM1: "EM = [0, 1] @ ?PS @ [0] @ algorithmID @ H" 
    using assms(1,3) PKCS1_EMSA_v1_5_Encode_def by meson
  have EM2: "?tLen + 11 \<le> emLen" using assms(2,3) PKCS1_EMSA_v1_5_Encode_inputValid_def by meson
  have EM3: "?aLen + hLen + 11 \<le> emLen"             using T EM2 by presburger
  have EM4: "?aLen + hLen + 3 < emLen"              using EM3 by auto
  have PS: "length ?PS = emLen - ?aLen - hLen - 3"  using T length_replicate by force
  have 1: "length ([0, 1] @ ?PS @ [0] @ algorithmID) = 2 + (emLen - ?aLen - hLen - 3) + 1 + ?aLen"
    by (metis PS assms(4) One_nat_def Suc_eq_plus1 ab_semigroup_add_class.add_ac(1) length_append
              list.size(3,4) numeral_2_eq_2) 
  have 2: "length ([0, 1] @ ?PS @ [0] @ algorithmID) = emLen - hLen"  using 1 EM4 by simp
  show ?thesis using 2 EM1 
    by (smt (verit, ccfv_threshold) append.assoc cancel_comm_monoid_add_class.diff_cancel drop0 
            drop_append eq_Nil_appendI length_0_conv length_drop) 
qed

end (* of locale EMSA_v1_5 *)

section \<open>Section 8: Signature Schemes\<close>

text\<open>"For the purposes of this document, a signature scheme with appendix consists of a
signature generation operation and a signature verification operation, where the
signature generation operation produces a signature from a message with a signer's RSA
private key, and the signature verification operation verifies the signature on the message
with the signer's corresponding RSA public key.  To verify a signature constructed with
this type of scheme it is necessary to have the message itself.  In this way, signature
schemes with appendix are distinguished from signature schemes with message recovery, 
which are not supported in this document.

Two signature schemes with appendix are specified in this document: RSASSA-PSS and
RSASSA-PKCS1-v1_5. Although no attacks are known against RSASSA-PKCS1-v1_5,
in the interest of increased robustness, RSASSA-PSS is required in new applications.
RSASSA-PKCS1-v1_5 is included only for compatibility with existing applications."\<close>

subsection \<open>Section 8.1: RSASSA-PSS\<close>

text\<open>"RSASSA-PSS combines the RSASP1 and RSAVP1 primitives with the EMSA-PSS encoding method.  It
is compatible with the IFSSA scheme as amended in the IEEE 1363a-2004, where the signature and
verification primitives are IFSP-RSA1 and IFVP-RSA1 as defined in IEEE 1363-2000 and the message
encoding method is EMSA4. EMSA4 is slightly more general than EMSA-PSS as it acts on bit strings
rather than on octet strings.  EMSA-PSS is equivalent to EMSA4 restricted to the case that the
operands as well as the hash and salt values are octet strings."\<close>


locale RSASSA_PSS = EMSA_PSS +
  fixes RSAENCRYPT RSADECRYPT :: "nat \<Rightarrow> nat"
    and n                     :: nat
assumes RSA_mod:     "0 < n"
    and RSA_bnd:     "\<forall>m. (RSAENCRYPT m) < n" 
                     "\<forall>c. (RSADECRYPT c) < n"
    and RSA_inv:     "\<forall>m. (m < n) \<longrightarrow> RSADECRYPT (RSAENCRYPT m) = m" 
                     "\<forall>c. (c < n) \<longrightarrow> RSAENCRYPT (RSADECRYPT c) = c"

begin

definition k :       "k       = octet_length n" 
definition modBits : "modBits = bit_length   n"

subsubsection \<open>Section 8.1.1: Signature Generation Operation\<close>

definition PKCS1_RSASSA_PSS_Sign_inputValid:
  "PKCS1_RSASSA_PSS_Sign_inputValid salt = 
  ( let sLen  = length salt;
        emLen = numBits_to_numOctets (modBits-1)
    in
     (PKCS1_EMSA_PSS_Encode_inputValid sLen emLen) \<and> (octets_valid salt))"

definition PKCS1_RSASSA_PSS_Sign:
  "PKCS1_RSASSA_PSS_Sign M salt = 
  ( let EM = PKCS1_EMSA_PSS_Encode M salt (modBits-1);
        m  = PKCS1_OS2IP EM;
        s  = RSADECRYPT m
    in
        PKCS1_I2OSP s k)" 

subsubsection \<open>Section 8.1.2: Signature Verification Operation\<close>

definition PKCS1_RSASSA_PSS_Verify :
  "PKCS1_RSASSA_PSS_Verify M S sLen = 
  ( let s       = PKCS1_OS2IP S;
        m       = RSAENCRYPT s;
        emLen   = numBits_to_numOctets (modBits - 1);
        EM      = PKCS1_I2OSP m emLen
    in
    (length S = k) \<and> (s < n) \<and> (PKCS1_I2OSP_inputValid m emLen) \<and>
    (PKCS1_EMSA_PSS_Verify sLen M EM (modBits - 1)) )"


subsubsection \<open>RSASSA_PSS Lemmas\<close>

lemma RSASSA_PSS_IntVals:
  assumes "PKCS1_RSASSA_PSS_Sign_inputValid salt"   "sLen  = length salt"
          "emLen = numBits_to_numOctets (modBits-1)"
          "EM    = PKCS1_EMSA_PSS_Encode M salt (modBits-1)"
          "m     = PKCS1_OS2IP EM"
          "s     = RSADECRYPT m"
          "S     = PKCS1_I2OSP s k"
          "s'    = PKCS1_OS2IP S"
          "m'    = RSAENCRYPT s'"
          "EM'   = PKCS1_I2OSP m' emLen"
   shows  "s = s' \<and> s < n \<and> m = m' \<and> m < n \<and> EM = EM' \<and> length EM = emLen \<and> octets_valid EM \<and>
          length S = k \<and>  S = PKCS1_RSASSA_PSS_Sign M salt"
proof - 
  have s1: "s = s'"  by (simp add: I2OSP_OS2IP assms(7,8))
  have s2: "s < n"   by (simp add: RSA_bnd(2) assms(6))
  have m1: "bit_length m \<le> (modBits -1)" 
    by (metis assms(1,4,5) EMSA_PSS_Encode_IntVals PKCS1_RSASSA_PSS_Sign_inputValid)
  have m2: "bit_length m < bit_length n" 
    by (metis m1 RSA_bnd(1) bit_len_zero_eq diff_less leD less_imp_diff_less less_nat_zero_code 
              modBits nat_neq_iff zero_less_one) 
  have m3: "m < n"   using m2 word_len_comp by blast
  have m4: "m = m'"  using RSA_inv(2) assms(6,9) m3 s1 by auto 
  have EM1: "length EM = emLen"
    by (metis EMSA_PSS_Encode_IntVals PKCS1_RSASSA_PSS_Sign_inputValid assms(1,3,4))
  have EM2: "EM = EM'"
    by (metis EM1 EMSA_PSS_Encode_DB_valid EMSA_PSS_Encode_EM_valid EMSA_PSS_Encode_H_valid 
        EMSA_PSS_Encode_PS_valid EMSA_PSS_Encode_dbMask_valid EMSA_PSS_Encode_maskedDB_sethi_valid 
        EMSA_PSS_Encode_maskedDB_valid OS2IP_I2OSP PKCS1_EMSA_PSS_Encode_def 
        PKCS1_RSASSA_PSS_Sign_inputValid assms(1,4,5,10) m4)
  have EM3: "octets_valid EM" by (simp add: EM2 I2OSP_octets_valid assms(10))
  have S1:  "length S = k"
    by (metis I2OSP_valid_len PKCS1_I2OSP_inputValid_def RSA_bnd(2) assms(6,7) k less_trans 
              word_length_eq2 Twoto8 zero_less_numeral) 
  have S2:  "S = PKCS1_RSASSA_PSS_Sign M salt" by (simp add: PKCS1_RSASSA_PSS_Sign assms(4,5,6,7))
  show ?thesis using s1 s2 m3 m4 EM1 EM2 EM3 S1 S2 by blast
qed
  

lemma RSASSA_PSS_SigVerifies:
  assumes "PKCS1_RSASSA_PSS_Sign_inputValid salt"  "S = PKCS1_RSASSA_PSS_Sign M salt"
          "sLen = length salt"
  shows   "PKCS1_RSASSA_PSS_Verify M S sLen"
  by (metis assms EMSA_PSS.PKCS1_EMSA_PSS_Encode_Verify EMSA_PSS_axioms PKCS1_I2OSP_inputValid_def
       PKCS1_OS2IP_def PKCS1_RSASSA_PSS_Verify RSASSA_PSS.PKCS1_RSASSA_PSS_Sign_inputValid Twoto8
       RSASSA_PSS_IntVals RSASSA_PSS_axioms words_to_nat_len_bnd words_valid_def zero_less_numeral)

end (* of locale RSASSA_PSS *)



subsection \<open>Section 8.2: RSASSA-PKCS1-v1_5\<close>

locale RSASSA_v1_5 = EMSA_v1_5 + 
  fixes RSAENCRYPT RSADECRYPT :: "nat \<Rightarrow> nat"
    and n           :: nat
assumes RSA_mod:     "0 < n"
    and RSA_bnd:     "\<forall>m. (RSAENCRYPT m) < n" 
                     "\<forall>c. (RSADECRYPT c) < n"
    and RSA_inv:     "\<forall>m. (m < n) \<longrightarrow> RSADECRYPT (RSAENCRYPT m) = m" 
                     "\<forall>c. (c < n) \<longrightarrow> RSAENCRYPT (RSADECRYPT c) = c"

begin

definition k :  "k = octet_length n" 

subsubsection \<open>Section 8.2.1: Signature Generation Operation\<close>

definition PKCS1_RSASSA_v1_5_Sign :
  "PKCS1_RSASSA_v1_5_Sign M = 
  (let EM = PKCS1_EMSA_v1_5_Encode M k;
       m  = PKCS1_OS2IP EM;
       s  = RSADECRYPT m
   in
       PKCS1_I2OSP s k )"

subsubsection \<open>Section 8.2.2: Signature Verification Operation\<close>

definition PKCS1_RSASSA_v1_5_Verify :
  "PKCS1_RSASSA_v1_5_Verify M S =
  (let s   = PKCS1_OS2IP S;
       m   = RSAENCRYPT s;
       EM  = PKCS1_I2OSP m k;
       EM' = PKCS1_EMSA_v1_5_Encode M k
   in 
  (length S = k) \<and> (s < n) \<and> (PKCS1_I2OSP_inputValid m k) \<and> (EM = EM') \<and> 
  (PKCS1_EMSA_v1_5_Encode_inputValid M k) )"

subsubsection \<open>RSASSA_v1_5 Lemmas\<close>

lemma RSASSA_v1_5_IntVals:
  assumes "PKCS1_EMSA_v1_5_Encode_inputValid M k" 
          "EM   = PKCS1_EMSA_v1_5_Encode M k"
          "m    = PKCS1_OS2IP EM"
          "s    = RSADECRYPT m"
          "S    = PKCS1_I2OSP s k"
          "s'   = PKCS1_OS2IP S"
          "m'   = RSAENCRYPT s'"
          "EM'  = PKCS1_I2OSP m' k"
  shows   "s = s' \<and> m = m' \<and> EM = EM' \<and> length S = k \<and> m < n \<and> s < n \<and> length EM = k"
proof -
  have s1: "s = s'"  by (simp add: I2OSP_OS2IP assms(5,6)) 
  have s2: "s < n"   by (simp add: RSA_bnd(2) assms(4)) 
  have s3: "s' < n"  using s1 s2 by fast
  have S: "length S = k"
    by (metis I2OSP_valid_len PKCS1_I2OSP_inputValid_def assms(5) k less_trans word_length_eq2 s2
              Twoto8 zero_less_numeral) 
  have EM1: "length EM = k"    using assms(1,2) PKCS1_EMSA_v1_5_Encode_valid_len by blast
  have EM2: "octets_valid EM"  by (simp add: PKCS1_EMSA_v1_5_Encode_octetsValid assms(2)) 
  let ?H     = "Hash M" 
  let ?T     = "algorithmID @ ?H"
  let ?tLen  = "length ?T"
  let ?PS    = "replicate (k - ?tLen - 3) (0xff::nat)"
  let ?psLen = "length ?PS"
  have EM3: "EM = [0, 1] @ ?PS @ [0] @ ?T"
    by (metis (no_types) PKCS1_EMSA_v1_5_Encode_def assms(2)) 
  have EM4: "words_strip_zero EM = [1] @ ?PS @ [0] @ ?T"  using EM3 by simp
  have EM5: "length (words_strip_zero EM) = k-1"
    by (metis EM1 EM3 EM4 append_Cons length_tl list.sel(3))  
  have m1: "m < 256^(k-1)"
    by (metis EM2 EM5 PKCS1_OS2IP_def assms(3) words_strip0_to_nat_len_bnd words_valid_def Twoto8) 
  have m2: "m < n" 
    by (metis (no_types, lifting) RSA_mod k less_le_trans m1 word_length_eq3 Twoto8 
        zero_less_numeral) 
  have m3: "m = m'"     using RSA_inv(2) m2 assms(4,7) s1 by auto
  have EM4: "EM = EM'"  using EM1 EM2 OS2IP_I2OSP assms(3,8) m3 by fastforce
  show ?thesis          using s1 s2 S m2 m3 EM1 EM4 by blast
qed

lemma RSASSA_v1_5_SigVerifies:
  assumes "PKCS1_EMSA_v1_5_Encode_inputValid M k" "S = PKCS1_RSASSA_v1_5_Sign M"
  shows   "PKCS1_RSASSA_v1_5_Verify M S"
  by (metis PKCS1_I2OSP_inputValid_def PKCS1_RSASSA_v1_5_Sign PKCS1_RSASSA_v1_5_Verify 
            RSASSA_v1_5_IntVals assms k less_trans word_length_eq2 Twoto8 zero_less_numeral)

end (* of locale RSASSA_v1_5 *)

section \<open>Appendix B: Supporting Techniques\<close>

subsection \<open>Appendix B.1: Hash Functions\<close>

text \<open>"Nine hash functions are given as examples for the encoding methods in this document: MD2,
MD5, SHA-1, SHA-224, SHA-256, SHA-384, SHA-512, SHA-512/224, and SHA-512/256.  For the RSAES-OAEP
encryption scheme and EMSA-PSS encoding method, only SHA-1, SHA-224, SHA-256, SHA-384, SHA-512,
SHA-512/224, and SHA-512/256 are recommended.  For the EMSA-PKCS1-v1_5 encoding method, SHA-224,
SHA-256, SHA-384, SHA-512, SHA-512/224, and SHA-512/256 are recommended for new applications.  
MD2, MD5 and SHA-1 are recommended only for compatibility with existing applications based on 
PKCS #1 v1.5."\<close>

datatype HashAlg = tMD2 | tMD5 | tSHA1 | tSHA224 | tSHA256 | tSHA384 | tSHA512 | tSHA512_224 | 
                   tSHA512_256

text \<open>This is the DER encoding of the algorithm IDs for the 9 has algorithms given in the appendix
of PKCS #1.\<close>
fun PKCS1_AlgorithmID :: "HashAlg \<Rightarrow> octets" where
  "PKCS1_AlgorithmID tMD2        = [0x30, 0x20, 0x30, 0x0c, 0x06, 0x08, 0x2a, 0x86, 
                                    0x48, 0x86, 0xf7, 0x0d, 0x02, 0x02, 0x05, 0x00, 
                                    0x04, 0x10]"
| "PKCS1_AlgorithmID tMD5        = [0x30, 0x20, 0x30, 0x0c, 0x06, 0x08, 0x2a, 0x86, 
                                    0x48, 0x86, 0xf7, 0x0d, 0x02, 0x05, 0x05, 0x00, 
                                    0x04, 0x10]"
| "PKCS1_AlgorithmID tSHA1       = [0x30, 0x21, 0x30, 0x09, 0x06, 0x05, 0x2b, 0x0e, 
                                    0x03, 0x02, 0x1a, 0x05, 0x00, 0x04, 0x14]"
| "PKCS1_AlgorithmID tSHA224     = [0x30, 0x2d, 0x30, 0x0d, 0x06, 0x09, 0x60, 0x86, 
                                    0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x04, 0x05, 
                                    0x00, 0x04, 0x1c]"
| "PKCS1_AlgorithmID tSHA256     = [0x30, 0x31, 0x30, 0x0d, 0x06, 0x09, 0x60, 0x86, 
                                    0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x01, 0x05, 
                                    0x00, 0x04, 0x20]"
| "PKCS1_AlgorithmID tSHA384     = [0x30, 0x41, 0x30, 0x0d, 0x06, 0x09, 0x60, 0x86, 
                                    0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x02, 0x05, 
                                    0x00, 0x04, 0x30]"
| "PKCS1_AlgorithmID tSHA512     = [0x30, 0x51, 0x30, 0x0d, 0x06, 0x09, 0x60, 0x86, 
                                    0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x03, 0x05, 
                                    0x00, 0x04, 0x40]"
| "PKCS1_AlgorithmID tSHA512_224 = [0x30, 0x2d, 0x30, 0x0d, 0x06, 0x09, 0x60, 0x86, 
                                    0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x05, 0x05, 
                                    0x00, 0x04, 0x1c]"
| "PKCS1_AlgorithmID tSHA512_256 = [0x30, 0x31, 0x30, 0x0d, 0x06, 0x09, 0x60, 0x86, 
                                    0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x06, 0x05, 
                                    0x00, 0x04, 0x20]"

lemma PKCS1_AlgorithmID_Valid: "octets_valid (PKCS1_AlgorithmID X)"
  apply (cases X)
  by (simp_all add: words_valid_def)


text\<open>This gives the default values for the hash of the label L when no L is given.
Because MD2 and MD5 are not recommended for RSA-OAEP or EMSAPSS, there is no lHash given 
for those hash algorithms.\<close>

fun PKCS1_emptyL_lHash :: "HashAlg \<Rightarrow> octets" where
  "PKCS1_emptyL_lHash tMD2        = []"
| "PKCS1_emptyL_lHash tMD5        = []"
| "PKCS1_emptyL_lHash tSHA1       = [0xda, 0x39, 0xa3, 0xee, 0x5e, 0x6b, 0x4b, 0x0d, 
                                     0x32, 0x55, 0xbf, 0xef, 0x95, 0x60, 0x18, 0x90, 
                                     0xaf, 0xd8, 0x07, 0x09]"
| "PKCS1_emptyL_lHash tSHA224     = [0xd1, 0x4a, 0x02, 0x8c, 0x2a, 0x3a, 0x2b, 0xc9, 
                                     0x47, 0x61, 0x02, 0xbb, 0x28, 0x82, 0x34, 0xc4, 
                                     0x15, 0xa2, 0xb0, 0x1f, 0x82, 0x8e, 0xa6, 0x2a, 
                                     0xc5, 0xb3, 0xe4, 0x2f]"
| "PKCS1_emptyL_lHash tSHA256     = [0xe3, 0xb0, 0xc4, 0x42, 0x98, 0xfc, 0x1c, 0x14, 
                                     0x9a, 0xfb, 0xf4, 0xc8, 0x99, 0x6f, 0xb9, 0x24, 
                                     0x27, 0xae, 0x41, 0xe4, 0x64, 0x9b, 0x93, 0x4c, 
                                     0xa4, 0x95, 0x99, 0x1b, 0x78, 0x52, 0xb8, 0x55]"
| "PKCS1_emptyL_lHash tSHA384     = [0x38, 0xb0, 0x60, 0xa7, 0x51, 0xac, 0x96, 0x38, 
                                     0x4c, 0xd9, 0x32, 0x7e, 0xb1, 0xb1, 0xe3, 0x6a, 
                                     0x21, 0xfd, 0xb7, 0x11, 0x14, 0xbe, 0x07, 0x43, 
                                     0x4c, 0x0c, 0xc7, 0xbf, 0x63, 0xf6, 0xe1, 0xda, 
                                     0x27, 0x4e, 0xde, 0xbf, 0xe7, 0x6f, 0x65, 0xfb, 
                                     0xd5, 0x1a, 0xd2, 0xf1, 0x48, 0x98, 0xb9, 0x5b]"
| "PKCS1_emptyL_lHash tSHA512     = [0xcf, 0x83, 0xe1, 0x35, 0x7e, 0xef, 0xb8, 0xbd, 
                                     0xf1, 0x54, 0x28, 0x50, 0xd6, 0x6d, 0x80, 0x07, 
                                     0xd6, 0x20, 0xe4, 0x05, 0x0b, 0x57, 0x15, 0xdc, 
                                     0x83, 0xf4, 0xa9, 0x21, 0xd3, 0x6c, 0xe9, 0xce, 
                                     0x47, 0xd0, 0xd1, 0x3c, 0x5d, 0x85, 0xf2, 0xb0, 
                                     0xff, 0x83, 0x18, 0xd2, 0x87, 0x7e, 0xec, 0x2f, 
                                     0x63, 0xb9, 0x31, 0xbd, 0x47, 0x41, 0x7a, 0x81, 
                                     0xa5, 0x38, 0x32, 0x7a, 0xf9, 0x27, 0xda, 0x3e]"
| "PKCS1_emptyL_lHash tSHA512_224 = [0x6e, 0xd0, 0xdd, 0x02, 0x80, 0x6f, 0xa8, 0x9e, 
                                     0x25, 0xde, 0x06, 0x0c, 0x19, 0xd3, 0xac, 0x86, 
                                     0xca, 0xbb, 0x87, 0xd6, 0xa0, 0xdd, 0xd0, 0x5c, 
                                     0x33, 0x3b, 0x84, 0xf4]"
| "PKCS1_emptyL_lHash tSHA512_256 = [0xc6, 0x72, 0xb8, 0xd1, 0xef, 0x56, 0xed, 0x28, 
                                     0xab, 0x87, 0xc3, 0x62, 0x2c, 0x51, 0x14, 0x06, 
                                     0x9b, 0xdd, 0x3a, 0xd7, 0xb8, 0xf9, 0x73, 0x74, 
                                     0x98, 0xd0, 0xc0, 0x1e, 0xce, 0xf0, 0x96, 0x7a]"

lemma PKCS1_emptyL_lHash_Valid: "octets_valid (PKCS1_emptyL_lHash X)"
  apply (cases X)
  by (simp_all add: words_valid_def)

subsection \<open>Appendix B.2: Mask Generation Functions\<close>

subsubsection \<open>Appendix B.2.1: MGF1\<close>
text\<open>
"Options: Hash     hash function (hLen denotes the length in octets of the hash function output)
 Input:   mgfSeed  seed from which mask is generated, an octet string*
          maskLen  intended length in octets of the mask, at most (2^32)*hLen"\<close>

named_theorems MGF1thms

definition PKCS1_MGF1_maskLenValid :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  "PKCS1_MGF1_maskLenValid maskLen hLen = (maskLen \<le> (2^32)*hLen)"

fun PKCS1_MGF1_rec :: "hash_type \<Rightarrow> octets \<Rightarrow> nat \<Rightarrow> octets" where
  "PKCS1_MGF1_rec Hash mgfSeed      0  = Hash ( mgfSeed @ (PKCS1_I2OSP 0 4) )" 
| "PKCS1_MGF1_rec Hash mgfSeed (Suc n) = (PKCS1_MGF1_rec Hash mgfSeed n) @ 
                                         (Hash (mgfSeed @ (PKCS1_I2OSP (Suc n) 4)))"

definition PKCS1_MGF1_MaxCounter :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "PKCS1_MGF1_MaxCounter maskLen hLen = 
  ( if (maskLen mod hLen = 0) then (maskLen div hLen) - 1 else (maskLen div hLen) )"

definition PKCS1_MGF1 :: "hash_type \<Rightarrow> nat \<Rightarrow> octets \<Rightarrow> nat \<Rightarrow> octets" where
  "PKCS1_MGF1 Hash hLen mgfSeed maskLen = 
     take maskLen ( PKCS1_MGF1_rec Hash mgfSeed (PKCS1_MGF1_MaxCounter maskLen hLen) )"

text \<open>What we want to know about any mask generating function is that it produces valid octets
(meaning the value of every octet is < 256) and that the length of the mask produced is given by
the input maskLen.  These facts are true for MGF1 assuming that the underlying Hash produces
valid octets, and the hash of any input has length hLen where 0 < hLen.\<close>

lemma MGF1_rec_valid:
  assumes "\<forall>x. octets_valid (Hash x)"
  shows   "octets_valid (PKCS1_MGF1_rec Hash mgfSeed n)"
using assms proof (induction n)
  case 0
  then show ?case by simp 
next
  case (Suc n)
  then show ?case by (simp add: words_valid_concat) 
qed

text \<open>Here is the first of the two things we want to know about MGF1.  It produces valid octets,
assuming that the underlying hash produces valid octets.\<close>
lemma MGF1_valid [MGF1thms]:
  assumes "\<forall>x. octets_valid (Hash x)"
  shows   "octets_valid (PKCS1_MGF1 Hash hLen mgfSeed maskLen)"
  using MGF1_rec_valid PKCS1_MGF1_def assms words_valid_take by presburger

lemma MGF1_rec_len:
  assumes "\<forall>x. length (Hash x) = hLen"
  shows   "length (PKCS1_MGF1_rec Hash mgfSeed n) = (n+1)*hLen"
using assms proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then show ?case
    by (metis PKCS1_MGF1_rec.simps(2) Suc_eq_plus1 comm_monoid_mult_class.mult_1 
              comm_semiring_class.distrib length_append) 
qed

lemma MaxCounter_zero:
  assumes "m < h"
  shows   "PKCS1_MGF1_MaxCounter m h = 0"
  by (simp add: PKCS1_MGF1_MaxCounter_def assms)

lemma MaxCounter_zero2: "PKCS1_MGF1_MaxCounter h h = 0"
  by (metis PKCS1_MGF1_MaxCounter_def Suc_diff_1 div_0 lessI less_one mod_mult_self2_is_0 
        mult.commute nat_mult_1 nonzero_mult_div_cancel_left zero_diff)

lemma MGF1_len_h: 
  assumes "\<forall>x. length (Hash x) = hLen"  "0 < hLen" 
  shows   "maskLen \<le> length (PKCS1_MGF1_rec Hash mgfSeed (PKCS1_MGF1_MaxCounter maskLen hLen))"
proof (cases)
  assume 10: "maskLen \<le> hLen" 
  have 11: "PKCS1_MGF1_MaxCounter maskLen hLen = 0" 
    by (metis 10 MaxCounter_zero MaxCounter_zero2 le_eq_less_or_eq) 
  have 12: "length (PKCS1_MGF1_rec Hash mgfSeed (PKCS1_MGF1_MaxCounter maskLen hLen)) = hLen"
    using 11 MGF1_rec_len assms(1) by presburger
  show ?thesis using 10 12 by argo
next
  assume "\<not> maskLen \<le> hLen"
  then have 20: "hLen < maskLen" by auto
  have 21: "1 \<le> maskLen div hLen" 
    by (metis One_nat_def Suc_leI assms(2) 20 div_greater_zero_iff less_imp_le_nat) 
  let ?n = "PKCS1_MGF1_MaxCounter maskLen hLen" 
  show ?thesis proof (cases "maskLen mod hLen = 0")
    case True
    then have "?n + 1 = maskLen div hLen"
      by (metis 21 One_nat_def PKCS1_MGF1_MaxCounter_def Suc_diff_1 add.right_neutral 
                add_Suc_right less_le_trans zero_less_one)
    then have "length (PKCS1_MGF1_rec Hash mgfSeed ?n) = maskLen" 
      by (simp add: MGF1_rec_len True assms(1) mod_0_imp_dvd) 
    then show ?thesis by simp
  next
    case 30: False
    let ?x = "maskLen div hLen"
    let ?y = "maskLen mod hLen" 
    have 31: "maskLen = ?x * hLen + ?y"        by presburger
    have 32: "?n + 1 = ?x + 1"                 using 30 PKCS1_MGF1_MaxCounter_def by presburger
    have 33: "(?n + 1) * hLen = ?x*hLen + hLen"
      by (metis 32 Suc_eq_plus1 add.commute mult.commute mult_Suc_right)  
    have 34: "?y < hLen"                       using assms(2) mod_less_divisor by blast
    have 35: "?x * hLen + ?y < ?x*hLen + hLen" using 34 by linarith
    have 36: "maskLen < (?n + 1) * hLen"       using 33 35 by presburger
    then show ?thesis by (metis MGF1_rec_len assms(1) less_imp_le) 
  qed
qed 

text \<open>Here is the second of the two things we want to know about MGF1.  It produces an octet
string of length maskLen (the final input value), as long as the two conditions are true of the
underlying Hash.\<close>
lemma MGF1_len [MGF1thms]: 
  assumes "\<forall>x. length (Hash x) = hLen"  "0 < hLen" 
  shows   "length (PKCS1_MGF1 Hash hLen mgfSeed maskLen) = maskLen"
proof - 
  have "maskLen \<le> length (PKCS1_MGF1_rec Hash mgfSeed (PKCS1_MGF1_MaxCounter maskLen hLen))"
    using assms MGF1_len_h by blast
  then show ?thesis using PKCS1_MGF1_def by simp
qed

end

