theory MobiusGyroGroup
  imports Complex_Main HOL.Real_Vector_Spaces HOL.Transcendental MoreComplex
          GyroGroup PoincareDisc
begin

definition ozero_m' :: "complex" where
  "ozero_m' = 0"                                     

lift_definition ozero_m :: PoincareDisc  ("0\<^sub>m") is ozero_m'
  unfolding ozero_m'_def
  by simp

lemma to_complex_0 [simp]:
  shows "to_complex 0\<^sub>m = 0"
  by transfer (simp add: ozero_m'_def)

lemma to_complex_0_iff [iff]:
  shows "to_complex x = 0 \<longleftrightarrow> x = 0\<^sub>m"
  by transfer (simp add: ozero_m'_def)

definition oplus_m' :: "complex \<Rightarrow> complex \<Rightarrow> complex"  where
  "oplus_m' a z = (a + z) / (1 + (cnj a) * z)"

lemma oplus_m'_in_disc:
  assumes "cmod c1 < 1" "cmod c2 < 1"
  shows "cmod (oplus_m' c1 c2) < 1"
proof-
  have "Im ((c1 + c2) * (cnj c1 + cnj c2)) = 0"
    by (metis complex_In_mult_cnj_zero complex_cnj_add)
  moreover
  have "Im ((1 + cnj c1 * c2) * (1 + c1 * cnj c2)) = 0"
    by (cases c1, cases c2, simp add: field_simps)
  ultimately
  have 1: "Re (oplus_m' c1 c2 * cnj (oplus_m' c1 c2)) = 
        Re (((c1 + c2) * (cnj c1 + cnj c2))) /
        Re (((1 + cnj c1 * c2) * (1 + c1 * cnj c2)))"
    unfolding oplus_m'_def
    by (simp add: complex_is_Real_iff)

  have "Re (((c1 + c2) * (cnj c1 + cnj c2))) = 
       (cmod c1)\<^sup>2 + (cmod c2)\<^sup>2 + Re (cnj c1 * c2 + c1 * cnj c2)"
    by (smt Re_complex_of_real complex_norm_square plus_complex.simps(1) semiring_normalization_rules(34) semiring_normalization_rules(7))
  moreover
  have "Re (((1 + cnj c1 * c2) * (1 + c1 * cnj c2))) =
        Re (1 + cnj c1 * c2 + cnj c2 * c1 + c1 * cnj c1 * c2 * cnj c2)"
    by (simp add: field_simps)
  hence *: "Re (((1 + cnj c1 * c2) * (1 + c1 * cnj c2))) =
        1 + Re (cnj c1 * c2 + c1 * cnj c2) + (cmod c1)\<^sup>2 * (cmod c2)\<^sup>2"
    by (smt Re_complex_of_real ab_semigroup_mult_class.mult_ac(1) complex_In_mult_cnj_zero complex_cnj_one complex_norm_square one_complex.simps(1) one_power2 plus_complex.simps(1) power2_eq_square semiring_normalization_rules(7) times_complex.simps(1))
  moreover
  have "(cmod c1)\<^sup>2 + (cmod c2)\<^sup>2 < 1 + (cmod c1)\<^sup>2 * (cmod c2)\<^sup>2"
  proof-
    have "(cmod c1)\<^sup>2 < 1" "(cmod c2)\<^sup>2 < 1"
      using assms
      by (simp_all add: cmod_def)
    hence "(1 - (cmod c1)\<^sup>2) * (1 - (cmod c2)\<^sup>2) > 0"
      by simp
    thus ?thesis
      by (simp add: field_simps)
  qed
  ultimately
  have "Re (((c1 + c2) * (cnj c1 + cnj c2))) < Re (((1 + cnj c1 * c2) * (1 + c1 * cnj c2)))"
    by simp
  moreover
  have "Re (((1 + cnj c1 * c2) * (1 + c1 * cnj c2))) > 0"
    by (smt "*" Re_complex_div_lt_0 calculation complex_cnj_add divide_self mult_zero_left one_complex.simps(1) zero_complex.simps(1))
  ultimately
  have 2: "Re (((c1 + c2) * (cnj c1 + cnj c2))) / Re (((1 + cnj c1 * c2) * (1 + c1 * cnj c2))) < 1"
    by (simp add: divide_less_eq)
  
  have "Re (oplus_m' c1 c2 * cnj (oplus_m' c1 c2)) < 1"
    using 1 2
    by simp
    
  thus ?thesis
    by (simp add: complex_mod_sqrt_Re_mult_cnj)
qed

lift_definition oplus_m :: "PoincareDisc \<Rightarrow> PoincareDisc \<Rightarrow> PoincareDisc" (infixl "\<oplus>\<^sub>m" 100) is oplus_m'
proof-
  fix c1 c2
  assume "cmod c1 < 1" "cmod c2 < 1"
  thus "cmod (oplus_m' c1 c2) < 1"
    by (simp add: oplus_m'_in_disc)
qed

definition ominus_m' :: "complex \<Rightarrow> complex" where
  "ominus_m' z = - z"                                      

lemma ominus_m'_in_disc:
  assumes "cmod z < 1"
  shows "cmod (ominus_m' z) < 1"
  using assms
  unfolding ominus_m'_def
  by simp

lift_definition ominus_m :: "PoincareDisc \<Rightarrow> PoincareDisc" ("\<ominus>\<^sub>m") is ominus_m'
proof-
  fix c
  assume "cmod c < 1"
  thus "cmod (ominus_m' c) < 1" 
    by (simp add: ominus_m'_def)
qed

lemma m_left_id:
  shows "0\<^sub>m \<oplus>\<^sub>m a = a"
  by (transfer, simp add: oplus_m'_def ozero_m'_def)

lemma m_left_inv:
  shows "\<ominus>\<^sub>m a \<oplus>\<^sub>m a = 0\<^sub>m"
  by (transfer, simp add: oplus_m'_def ominus_m'_def ozero_m'_def)

definition gyr_m' :: "complex \<Rightarrow> complex \<Rightarrow> complex \<Rightarrow> complex" where
  "gyr_m' a b z = ((1 + a * cnj b) / (1 + cnj a * b)) * z"

lift_definition gyr\<^sub>m :: "PoincareDisc \<Rightarrow> PoincareDisc \<Rightarrow> PoincareDisc \<Rightarrow> PoincareDisc" is gyr_m'
proof-
  fix a b z
  assume "cmod a < 1" "cmod b < 1" "cmod z < 1"
  have "cmod (1 + a * cnj b) = cmod (1 + cnj a * b)"
    by (metis complex_cnj_add complex_cnj_cnj complex_cnj_mult complex_cnj_one complex_mod_cnj)
  hence "cmod ((1 + a * cnj b) / (1 + cnj a * b)) = 1"
    by (simp add: \<open>cmod a < 1\<close> \<open>cmod b < 1\<close> den_not_zero norm_divide)
  thus "cmod (gyr_m' a b z) < 1"
    using \<open>cmod z < 1\<close>
    unfolding gyr_m'_def
    by (metis mult_cancel_right1 norm_mult)
qed

lemma gyr_m_commute:
  "a \<oplus>\<^sub>m b = gyr\<^sub>m a b (b \<oplus>\<^sub>m a)"
  by transfer (metis (no_types, opaque_lifting) oplus_m'_def gyr_m'_def add.commute den_not_zero mult.commute nonzero_mult_divide_mult_cancel_right2 times_divide_times_eq)

lemma gyr_m_left_assoc:
  "a \<oplus>\<^sub>m (b \<oplus>\<^sub>m z) = (a \<oplus>\<^sub>m b) \<oplus>\<^sub>m gyr\<^sub>m a b z"
proof transfer
  fix a b z
  assume *: "cmod a < 1" "cmod b < 1" "cmod z < 1"
  have 1: "oplus_m' a (oplus_m' b z) =
          (a + b + (1 + a * cnj b) * z) / 
          ((cnj a + cnj b) * z + (1 + cnj a * b))"
      unfolding gyr_m'_def oplus_m'_def
      by (smt "*"(2) "*"(3) ab_semigroup_mult_class.mult_ac(1) add.left_commute add_divide_eq_iff combine_common_factor den_not_zero divide_divide_eq_right mult.commute mult_cancel_right2 nonzero_mult_div_cancel_left semiring_normalization_rules(1) semiring_normalization_rules(23) semiring_normalization_rules(34) times_divide_eq_right)
  have 2: "oplus_m' (oplus_m' a b) (gyr_m' a b z) = 
          ((a + b) + (1 + a * cnj b) * z) / 
          ((cnj a + cnj b) * z + (1 + cnj a * b))"
  proof-
    have x: "((a + b) / (1 + cnj a * b) +
           (1 + a * cnj b) / (1 + cnj a * b) * z) = 
          ((a + b) + (1 + a * cnj b) * z) / (1 + cnj a * b)"
      by (metis add_divide_distrib times_divide_eq_left)
    moreover
    have "1 + cnj ((a + b) / (1 + cnj a * b)) *
               ((1 + a * cnj b) / (1 + cnj a * b) * z) = 
          1 + (cnj a + cnj b) / (1 + cnj a * b) * z"
      using divide_divide_times_eq divide_eq_0_iff mult_eq_0_iff nonzero_mult_div_cancel_left
      by force
    hence y: "1 + cnj ((a + b) / (1 + cnj a * b)) *
               ((1 + a * cnj b) / (1 + cnj a * b) * z) =
          ((cnj a + cnj b) * z + (1 + cnj a * b)) / (1 + cnj a * b)"
      by (metis "*"(1) "*"(2) add.commute add_divide_distrib den_not_zero divide_self times_divide_eq_left)
    ultimately
    show ?thesis
      unfolding gyr_m'_def oplus_m'_def  
      by (subst x, subst y, simp add: "*"(1) "*"(2) den_not_zero)
  qed
  show "oplus_m' a (oplus_m' b z) =
        oplus_m' (oplus_m' a b) (gyr_m' a b z)"
      by (subst 1, subst 2, simp)
qed

lemma gyr_m_inv:
  "gyr\<^sub>m a b (gyr\<^sub>m b a z) = z"
  by transfer (simp add: gyr_m'_def, metis den_not_zero nonzero_mult_div_cancel_left nonzero_mult_divide_mult_cancel_right semiring_normalization_rules(7))

lemma gyr_m_bij:
  shows "bij (gyr\<^sub>m a b)"
  by (metis bij_betw_def inj_def gyr_m_inv surj_def)

lemma gyr_m_not_degenerate:
  shows "\<exists> z1 z2. gyr\<^sub>m a b z1 \<noteq> gyr\<^sub>m a b z2"
proof-
  obtain z1 z2 :: PoincareDisc where "z1 \<noteq> z2"
    using poincare_disc_two_elems
    by blast
  hence "gyr\<^sub>m a b z1 \<noteq> gyr\<^sub>m a b z2"
    by (metis gyr_m_inv)
  thus ?thesis
    by blast
qed

lemma gyr_m_left_loop:
  shows "gyr\<^sub>m a b = gyr\<^sub>m (a \<oplus>\<^sub>m b) b"
proof-
  have "\<exists> z. gyr\<^sub>m (a \<oplus>\<^sub>m b) b z \<noteq> 0\<^sub>m"
    using gyr_m_not_degenerate
    by metis
  hence "\<And> z. gyr\<^sub>m a b z = gyr\<^sub>m (a \<oplus>\<^sub>m b) b z"
  proof transfer
    fix a b z
    assume "\<exists>z\<in>{z. cmod z < 1}. gyr_m' (oplus_m' a b) b z \<noteq> ozero_m'"
    then obtain z' where
      "cmod z' < 1" "gyr_m' (oplus_m' a b) b z' \<noteq> ozero_m'"
      by auto
    hence *: "1 + (a + b) / (1 + cnj a * b) * cnj b \<noteq> 0"
      by (simp add: gyr_m'_def oplus_m'_def ozero_m'_def)
    assume "cmod a < 1" "cmod b < 1" "cmod z < 1"    
    have 1: "1 + (a + b) / (1 + cnj a * b) * cnj b = 
          (1 + cnj a * b + a * cnj b + b * cnj b) / (1 + cnj a * b)"
      using \<open>cmod a < 1\<close> \<open>cmod b < 1\<close> add_divide_distrib den_not_zero divide_self times_divide_eq_left
      by (metis (no_types, lifting) ab_semigroup_add_class.add_ac(1) distrib_right)
    have 2: "1 + cnj ((a + b) / (1 + cnj a * b)) * b = 
             (1 + cnj a * b + a * cnj b + b * cnj b) / (1 + a * cnj b)"
      by (smt "1" complex_cnj_add complex_cnj_cnj complex_cnj_divide complex_cnj_mult complex_cnj_one semiring_normalization_rules(23) semiring_normalization_rules(7))
    have "1 + cnj a * b + a * cnj b + b * cnj b \<noteq> 0"
      using * 1
      by auto
    then show "gyr_m' a b z = gyr_m' (oplus_m' a b) b z"
      unfolding gyr_m'_def oplus_m'_def
      by (subst 1, subst 2, simp)
  qed
  thus ?thesis
    by auto
qed

lemma gyr_m_distrib:
  shows "gyr\<^sub>m a b (a' \<oplus>\<^sub>m b') = gyr\<^sub>m a b a' \<oplus>\<^sub>m gyr\<^sub>m a b b'"
  apply transfer
  apply (simp add: gyr_m'_def oplus_m'_def)
  apply (simp add: add_divide_distrib distrib_left)
  done

interpretation Mobius_gyrogroup: gyrogroup ozero_m oplus_m ominus_m gyr\<^sub>m
proof
  fix a
  show "0\<^sub>m \<oplus>\<^sub>m a = a"
    by (simp add: m_left_id)
next
  fix a
  show "\<ominus>\<^sub>m a \<oplus>\<^sub>m a = 0\<^sub>m"
    by (simp add: m_left_inv)
next
  fix a b z
  show "a \<oplus>\<^sub>m (b \<oplus>\<^sub>m z) = a \<oplus>\<^sub>m b \<oplus>\<^sub>m gyr\<^sub>m a b z"
    by (simp add: gyr_m_left_assoc)
next
  fix a b
  show "gyr\<^sub>m a b = gyr\<^sub>m (a \<oplus>\<^sub>m b) b"
    using gyr_m_left_loop by auto
next
  fix a b
  show "gyrogroupoid.gyroaut (\<oplus>\<^sub>m) (gyr\<^sub>m a b)"
    unfolding gyrogroupoid.gyroaut_def
  proof safe
    fix a' b'
    show "gyr\<^sub>m a b (a' \<oplus>\<^sub>m b') = gyr\<^sub>m a b a' \<oplus>\<^sub>m gyr\<^sub>m a b b'"
      by (simp add: gyr_m_distrib)
  next
    show "bij (gyr\<^sub>m a b)"
      by (simp add: gyr_m_bij)
  qed
qed

interpretation Mobius_gyrocommutative_gyrogroup: gyrocommutative_gyrogroup ozero_m oplus_m ominus_m gyr\<^sub>m
proof
  fix a b
  show "a \<oplus>\<^sub>m b = gyr\<^sub>m a b (b \<oplus>\<^sub>m a)"
    using gyr_m_commute by blast
qed

instantiation PoincareDisc :: gyrogroupoid
begin
definition gyrozero_PoincareDisc where
 "gyrozero_PoincareDisc = ozero_m"
definition gyroplus_PoincareDisc where
 "gyroplus_PoincareDisc = oplus_m"
instance ..
end

instantiation PoincareDisc :: gyrogroup
begin
definition gyroinv_PoincareDisc where
 "gyroinv_PoincareDisc = ominus_m"
definition gyr_PoincareDisc where
 "gyr_PoincareDisc = gyr\<^sub>m"
instance proof
  fix a :: PoincareDisc
  show "0\<^sub>g \<oplus> a = a"
    by (simp add: gyroplus_PoincareDisc_def gyrozero_PoincareDisc_def)
next
  fix a :: PoincareDisc
  show "\<ominus> a \<oplus> a = 0\<^sub>g"
    by (simp add: gyroinv_PoincareDisc_def gyroplus_PoincareDisc_def gyrozero_PoincareDisc_def)
next
  fix a b :: PoincareDisc
  show "gyroaut (gyr a b)"
    by (simp add: gyr_PoincareDisc_def gyroaut_def gyroplus_PoincareDisc_def gyr_m_bij)
next
  fix a b z :: PoincareDisc
  show "a \<oplus> (b \<oplus> z) = a \<oplus> b \<oplus> gyr a b z"
    by (simp add: gyr_PoincareDisc_def gyroplus_PoincareDisc_def gyr_m_left_assoc)
next
  fix a b :: PoincareDisc
  show  "gyr a b = gyr (a \<oplus> b) b"
    using gyr_PoincareDisc_def gyroplus_PoincareDisc_def gyr_m_left_loop by auto
qed
end

instantiation PoincareDisc :: gyrocommutative_gyrogroup
begin
instance proof
  fix a b :: PoincareDisc
  show "a \<oplus> b = gyr a b (b \<oplus> a)"
    using gyr_PoincareDisc_def gyroplus_PoincareDisc_def gyr_m_commute by auto
qed
end

(* ------------------------------------------------------------------- *)

lemma oplusM_reals:
  assumes "Im (to_complex x) = 0" "Im (to_complex y) = 0"
  shows "Im (to_complex (x \<oplus>\<^sub>m y)) = 0"
  using assms
  by (transfer, auto simp add: oplus_m'_def complex_is_Real_iff) 

lemma oplusM_pos_reals:
  assumes "Im (to_complex x) = 0" "Im (to_complex y) = 0"
  assumes "Re (to_complex x) \<ge> 0" "Re (to_complex y) \<ge> 0"
  shows "Re (to_complex (x \<oplus>\<^sub>m y)) \<ge> 0"
  using assms
  by (transfer, auto simp add: oplus_m'_def complex_is_Real_iff) 

definition gyr\<^sub>m_alternative :: "PoincareDisc \<Rightarrow> PoincareDisc \<Rightarrow> PoincareDisc \<Rightarrow> PoincareDisc" where
  "gyr\<^sub>m_alternative u v w = \<ominus>\<^sub>m (u \<oplus>\<^sub>m v) \<oplus>\<^sub>m (u \<oplus>\<^sub>m (v \<oplus>\<^sub>m w))"

lemma gyr_m_alternative_gyr_m:
  shows "gyr\<^sub>m_alternative u v w = gyr\<^sub>m u v w"
  by (metis gyr\<^sub>m_alternative_def gyr_m_inv gyr_m_left_assoc gyr_m_left_loop m_left_id m_left_inv)

definition oplus_m'_alternative :: "complex \<Rightarrow> complex \<Rightarrow> complex" where 
  "oplus_m'_alternative u v =
      ((1 + 2*inner u v + (norm v)^2) *\<^sub>R u + (1 - (norm u)^2) *\<^sub>R v) /
       (1 + 2*inner u v + (norm u)^2 * (norm v)^2)"

lemma oplus_m'_alternative:
  assumes "cmod u < 1" "cmod v < 1"
  shows "oplus_m'_alternative u v = oplus_m' u v"
proof-
  have *: "2 * inner u v = cnj u * v + cnj v * u"
    using two_inner_cnj
    by auto
  
  have "(1 + 2*inner u v + (norm v)^2) * u =
        (1 + cnj u *v + cnj v * u + (norm v)^2) * u"
    using *
    by auto

  moreover

  have "1 + 2*inner u v + (norm u)^2 * (norm v)^2 = 
        1 + cnj u * v + cnj v * u + (norm u)^2 * (norm v)^2"
    using *
    by auto

  moreover

  have "(1 + cnj u * v + cnj v * u + (norm v)^2) * u + (1 - (norm u)^2) * v =
        (1 + cnj v * u) * (u + v)"
  proof-
    have *: "(1 + cnj u * v + cnj v * u + (norm v)^2) * u = 
             u + (norm u)^2 * v + cnj v * u^2 + (norm v)^2 * u"
      by (smt (verit, del_insts) ab_semigroup_mult_class.mult_ac(1) comm_semiring_class.distrib complex_norm_square mult.commute mult_cancel_right1 power2_eq_square)
    have **: "(1 + cnj v * u) * (u + v) = u + cnj v * u * u + v + cnj v * u * v"
      by (simp add: distrib_left ring_class.ring_distribs(2))
    have "u + cnj u * v *u + v + cnj u* v * v = u + cnj u * v^2 + (norm u)^2 * v + v"
      by (simp add: cnj_cmod mult.commute power2_eq_square)
    have ***: "(1 - (norm u)^2) * v = v - (norm u)^2 * v"
      by (simp add: mult.commute right_diff_distrib')
    have "(1 + cnj u * v + cnj v * u + (norm v)^2) * u + (1 - (norm u)^2) * v =
          u + (norm u)^2 * v + (cnj v) * u^2 + (norm v)^2 * u + v - (norm u)^2 * v"
      using * ***
      by force
    have ****: "(1 + cnj u * v + cnj v * u + (norm v)^2) * u + (1-(norm u)^2) * v =
                u + cnj v *u^2 + (norm v)^2 * u + v"
      using * *** 
      by auto

    have "(1 + cnj v * u) * (u+v) = u + (norm v)^2 *u + v + cnj v * u^2"
      using **
      by (simp add: cnj_cmod mult.commute power2_eq_square)

    then show ?thesis
      using ****
      by auto
  qed

  moreover have "1 + cnj u * v + cnj v *u + (norm u)^2 * (norm v)^2  =
                (1 + cnj u * v) * (1 + cnj v * u)"
    by (smt (verit, del_insts) cnj_cmod comm_semiring_class.distrib complex_cnj_cnj complex_cnj_mult complex_mod_cnj is_num_normalize(1) mult.commute mult_numeral_1 norm_mult numeral_One power_mult_distrib)
  
  ultimately
  show ?thesis 
    using assms
    unfolding oplus_m'_alternative_def oplus_m'_def
    by (metis (no_types, lifting) den_not_zero divide_divide_eq_left' nonzero_mult_div_cancel_left scaleR_conv_of_real)
qed

lift_definition oplus_m_alternative :: "PoincareDisc \<Rightarrow> PoincareDisc \<Rightarrow> PoincareDisc" is oplus_m'_alternative
  by (simp add: oplus_m'_alternative oplus_m'_in_disc)

end
