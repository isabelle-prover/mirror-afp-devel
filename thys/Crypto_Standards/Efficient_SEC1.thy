theory Efficient_SEC1
  imports "Efficient_Mod_Exp"
          "SEC1v2_0"

begin

text \<open>If we are to run test vectors, we need an efficient ways to compute functions used in SEC1.
Here we prove the necessary code equations.\<close>

section\<open>inv_mod\<close>

text\<open>We need to be able to efficiently calculate the inverse of a number modulo some modulus.
The work for this was done in EfficientModExp.\<close>

lemma inv_mod_efficient [code]: "inv_mod m x = 
  (if m = 0 then 1 else ( if m = 1 then 0 else efficient_funpow (mod_mult m) 1 x (m-2) ) )"
  by (metis diff_0_eq_0 efficient_funpow.simps(1) inv_mod_def mod_by_1 mod_mult_by_squaring_not1)

lemma (in SEC1) inv_mod_n_efficient: "inv_mod_n x = efficient_funpow (mod_mult n) 1 x (n-2)"
  by (metis inv_mod_efficient n_not_2 ECparamsValid not_less_zero not_numeral_less_one) 

section\<open>point_mult\<close>

text\<open>We need to be able to efficiently compute the scalar multiple of a point.  Note that this
efficient form only works for points that are on the elliptic curve.  So many of the following
code equation lemmas are of the form "if this is a point on the curve, then use the efficient 
form, otherwise I got nothing."  This is fine since we will only ever be computing scalar 
multiples of points on the curve.\<close>

lemma (in residues_prime_gt2) point_mult_efficient_h1: 
  assumes "on_curve a b P"  "on_curve a b Q"  "a \<in> carrier R"  "b \<in> carrier R"  "nonsingular a b"
  shows   "add a (add a P Q) (point_mult a x P) = add a Q (point_mult a (x + 1) P)"
  using assms add_comm' point_mult_add ell_prime_field.AB_in_carrier(1,2) point_mult_closed
        ell_prime_field.nonsingular_in_bf Suc_eq_plus1 add_assoc point_mult.simps(2)
  by presburger 

lemma (in residues_prime_gt2) point_mult_efficient_h2:
  assumes "on_curve a b P"  "on_curve a b Q"  "a \<in> carrier R"  "b \<in> carrier R"  "nonsingular a b"
  shows   "add a Q (point_mult a k P) = efficient_funpow (add a) Q P k"
  using assms proof (induction k arbitrary: P Q rule: less_induct)
  case L: (less x)
  then show ?case proof (cases "even x")
    case E: True
    then show ?thesis proof (cases "x = 0")
      case True
      then show ?thesis by (simp add: add_0_r) 
    next
      case EG: False
      have EG0: "x div 2 < x" using EG by simp 
      have EG1: "efficient_funpow (add a) Q P x 
                   = efficient_funpow (add a) Q (add a P P) (x div 2)"
        by (metis efficient_funpow.simps(3) E EG)
      have EG2: "on_curve a b (add a P P)"
        using L.prems add_closed by auto 
      have EG3: "efficient_funpow (add a) Q P x = add a Q (point_mult a (x div 2) (add a P P))"
        using EG0 EG1 EG2 L(1,3) assms(3,4,5) by presburger
      have EG4: "2 * (x div 2) = x" using E by simp
      show ?thesis by (metis EG3 EG4 assms(3,4,5) L(2) point_mult2_eq_double point_mult_mult) 
    qed
  next
    case O: False
    then show ?thesis proof (cases "x = 1")
      case True
      then show ?thesis
        by (metis (no_types, lifting) assms(3,4,5) L(2,3) point_mult.simps  on_curve_infinity
            One_nat_def add_0_r add_comm' efficient_funpow.simps(2)) 
    next
      case OG: False
      have OG1: "x div 2 < x"          using O by presburger
      have OG2: "x = 2*(x div 2) + 1"  using O by auto
      have OG3: "efficient_funpow (add a) Q P x 
                   = efficient_funpow (add a) (add a P Q) (add a P P) (x div 2)"
        by (meson O OG efficient_funpow.simps(4))
      have OG4: "efficient_funpow (add a) Q P x 
                   = add a (add a P Q) (point_mult a (x div 2) (add a P P))"
        using assms(3,4) L OG1 OG3 add_closed by presburger
      have OG5: "add a (add a P Q) (point_mult a    (x div 2) (add a P P)) = 
                 add a (add a P Q) (point_mult a (2*(x div 2)) P)"
        using assms(3,4,5) L(2) point_mult2_eq_double point_mult_mult by presburger 
      have OG6: "add a (add a P Q) (point_mult a (2*(x div 2)) P) 
               = add a Q (point_mult a (2*(x div 2) + 1) P)"
        using L(2,3) assms(3,4,5) point_mult_efficient_h1 by blast
      show ?thesis using OG2 OG4 OG5 OG6 by argo
    qed
  qed
qed

lemma (in residues_prime_gt2) point_mult_efficient:
  assumes "on_curve a b P"  "a \<in> carrier R"  "b \<in> carrier R"  "nonsingular a b"
  shows   "point_mult a k P = efficient_funpow (add a) Infinity P k"
  by (metis assms point_mult_efficient_h2 add_0_l on_curve_infinity)

lemma (in residues_prime_gt2) point_mult_efficient_code:
  assumes "mon_curve p a b P"  "a \<in> carrier R"  "b \<in> carrier R"  "nonsingular a b"
  shows   "point_mult a k P = efficient_funpow (point_madd a) Infinity P k"
  using assms point_add_eq[of a] point_mult_efficient[of a b P k] on_curve_residues_eq 
  by presburger

lemma (in SEC1) point_mult_efficient_SEC1 [code]:
  "point_mult' k P = (if (mon_curve p a b P) then (efficient_funpow (point_madd a) Infinity P k)
                      else (point_mult' k P))"
  using point_mult_efficient_code EPF.AB_in_carrier EPF.nonsingular_in_bf by presburger 

section\<open>Et Cetera\<close>

text\<open>Using the above efficient methods for inv_mod and point_mult, we can write code equations
for more involved definitions from SEC1.\<close>

lemma (in SEC1) ECkeyGen_efficient [code]: 
  "ECkeyGen d = efficient_funpow (point_madd a) Infinity G d"
  by (metis point_mult_efficient_SEC1 on_curve_residues_eq ECkeyGen_def EPF.in_carrier_curve 
            GonEPFcurve) 

lemma (in SEC1) ECDSA_Sign_e_efficient [code]:
  "ECDSA_Sign_e d\<^sub>U e k P = 
  ( case P of 
      Infinity    \<Rightarrow> None
    | Point x\<^sub>P y\<^sub>P \<Rightarrow> 
      ( let r    = nat (x\<^sub>P mod n);
            kinv = efficient_funpow (mod_mult n) 1 k (n-2);
            s    = (kinv*(e + r*d\<^sub>U)) mod n
       in
        if r = 0 then None else (
        if s = 0 then None else Some (r,s)
        )
      )
  )"
  using ECDSA_Sign_e_def inv_mod_n_efficient by presburger

lemma (in SEC1) ECDSA_Verify_e_efficient [code]:
  "ECDSA_Verify_e Q\<^sub>U e S = ( if (mon_curve p a b Q\<^sub>U) then
  ( let r    = fst S; 
        s    = snd S; 
        sinv = efficient_funpow (mod_mult n) 1 s (n-2);
        u1   = (e*sinv) mod n;
        u2   = (r*sinv) mod n;
        P    = point_madd a (efficient_funpow (point_madd a) Infinity G u1) 
                            (efficient_funpow (point_madd a) Infinity Q\<^sub>U u2)
    in
       (case P of 
          Infinity  \<Rightarrow> False
        | Point x y \<Rightarrow> (
             (0 < r) \<and> (r < n) \<and> (0 < s) \<and> (s < n) \<and> (nat (x mod n) = r) )
       )
  ) else (ECDSA_Verify_e Q\<^sub>U e S) )"
  using ECDSA_Verify_e_def ECkeyGen_def ECkeyGen_efficient inv_mod_n_efficient point_add_eq 
        point_mult_efficient_SEC1 by presburger 

lemma (in SEC1) ECDHprim_efficient [code]:
  "ECDHprim d Q = (if (mon_curve p a b Q) then
   ( let P = efficient_funpow (point_madd a) Infinity Q d in
     ( case P of
         Infinity    \<Rightarrow> None
       | Point x\<^sub>P y\<^sub>P \<Rightarrow> Some x\<^sub>P )
   )
     else (ECDHprim d Q)
  )"
  using ECDHprim_def point_mult_efficient_SEC1 by presburger

lemma (in SEC1) MQVcomputeQbar_efficient [code]:
  "MQVcomputeQbar Q = 
  (case Q of
     Infinity  \<Rightarrow> None
   | Point x y \<Rightarrow> (
     let z    = (2::nat)^(word_length 2 n);
         xBar = nat (x mod z)
     in Some (xBar + z)
  ))"
proof - 
  have 1: "prime n"                         using N.p_prime by presburger
  have 2: "2 < n"                           using ECparamsValid n_not_2 by auto 
  have 3: "0 < (2::nat)"                    using zero_less_numeral by fast
  have 4: "word_length 2 n = \<lceil>(log 2 n)/2\<rceil>"  using wordLenLog2Prime 1 2 3 by force
  show ?thesis                              by (metis 4 MQVcomputeQbar_def nat_int)  
qed

lemma (in SEC1) MQVcomputeP_efficient [code]:
  "MQVcomputeP s Q2V Q2Vbar Q1V = (if (mon_curve p a b Q1V \<and> mon_curve p a b Q2V) then
  ( case s of
     None    \<Rightarrow> None
   | Some s' \<Rightarrow>
     (case Q2Vbar of
       None         \<Rightarrow> None
     | Some Q2Vbar' \<Rightarrow> Some ( (efficient_funpow (point_madd a) Infinity 
                              (point_madd a Q2V 
                              (efficient_funpow (point_madd a) Infinity Q1V Q2Vbar') )
                              (h*s'))
                            )
     )
  )
  else MQVcomputeP s Q2V Q2Vbar Q1V)"
proof (cases s)
  case None
  then show ?thesis using MQVcomputeP_def by force
next
  case s: (Some s')
  then show ?thesis proof (cases Q2Vbar)
    case None
    then show ?thesis using MQVcomputeP_def s by simp
  next
    case Q2Vbar: (Some Q2Vbar')
    then show ?thesis proof (cases "(mon_curve p a b Q1V \<and> mon_curve p a b Q2V)")
      case True 
      let ?P1 = "point_mult' Q2Vbar' Q1V"
      have 2: "on_curve' ?P1"
        using True on_curve_residues_eq point_mult_closed by auto
      have 3: "add' Q2V ?P1 = point_madd a Q2V ?P1"
        using point_add_eq by blast
      let ?P2 = "add' Q2V ?P1"
      have 4: "on_curve' ?P2" using True on_curve_residues_eq add_closed
        using 2 True on_curve_residues_eq add_closed EPF.AB_in_carrier(1,2) by presburger 
      show ?thesis 
        by (metis (no_types, lifting) s Q2Vbar 3 4 point_mult_efficient_SEC1 MQVcomputeP_def
            on_curve_residues_eq option.simps(5))
    next
      case False
      then show ?thesis by argo
    qed
  qed
qed


end 
