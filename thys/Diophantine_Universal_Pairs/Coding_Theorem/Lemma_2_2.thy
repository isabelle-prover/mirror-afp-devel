theory Lemma_2_2                                 
  imports "HOL-Number_Theory.Number_Theory" "../Coding/Utils"
begin

subsection \<open>Increasing the base b appropriately\<close>

lemma exp_grows: 
  fixes a b k :: int
  assumes H: "a \<ge> 2 \<and> k \<ge> 0 "
  shows "\<exists> (s::nat). a^s \<ge> b \<and> s \<ge> k"
proof -
  let ?c = "nat(abs(b)) + nat(abs(k))" 
  have "nat(a)^?c \<ge> b" 
    by (smt (verit, best) assms nat_le_iff nat_plus_as_int of_nat_1 one_add_one self_le_ge2_pow 
        zless_nat_conj zless_nat_eq_int_zless) 
 thus ?thesis     
    using assms by force 
qed

lemma little_fermat:
  fixes a m :: int
  assumes gcd: "coprime a m" and posit: "a \<ge> 1 \<and> m \<ge> 2"
  shows "\<exists> k l. a^k-1 = m*l \<and> k \<ge> 1"
proof -
  have "residues m" 
    using posit residues_def by auto 
  hence "a^totient(nat m) mod m = 1"
    using  Residues.residues.euler_theorem[of "m" "a"] gcd 
    by (metis abs_le_zero_iff abs_one mod_pos_pos_trivial
        residues.m_gt_one residues.res_eq_to_cong verit_la_generic)
  hence 0: "(a^totient(nat m) - 1) mod m = 0 "
    by (metis diff_self mod_0 mod_diff_right_eq)

  have "totient(nat m) \<ge> 1" 
    using `residues m` not_le_imp_less residues.m_gt_one by fastforce
  thus ?thesis 
    using 0 by blast
qed
  

lemma lemma_2_2:
  fixes a Z :: int
  assumes posit:"Z > 0 \<and> a \<ge> 0"
  shows "\<exists> f r. f \<ge> Z \<and> 1 + 3*(2*a+1)*f = 4^r"
proof -
  let ?c = "3*(2*a+1)" and ?d = "1 + 3*(2*a+1)*Z"
  have d: "?d \<ge>1 \<and> ?d \<ge> 0" using posit by auto
  have c: "?c \<ge> 2 \<and> (4::int) \<ge> 1 " using posit by auto
  have c_odd: "\<exists> h. ?c = 2*h +1" by presburger
  then obtain h where h_def: "?c = 2*h +1" by auto

  have gcd: "coprime (4::int) ?c" 
    using h_def
    by (metis coprime_add_one_right coprime_mult_left_iff
        mult_2 mult_2_right numeral_Bit0 one_add_one)
  hence 10:"\<exists> k l. (4::int)^k-1 = ?c*l \<and> k \<ge> 1" 
    using little_fermat[of 4 ?c] c by auto
  then obtain k l where 11: "4^k-1 = ?c*l \<and> k \<ge> 1"  
    by auto
  obtain s where s_def: "s \<ge> 4 \<and> 4^s \<ge> 1 + 3*(2*a+1)*Z"
    using d exp_grows[of 4 4 ?d] by force
 
  have "(4::nat)^(s*k) \<ge> (4::nat)^s"
    using 11 by simp
  hence 20: "((4::nat)^(s*k)) \<ge> 1 + 3*(2*a+1)*Z"
    using s_def by (meson dual_order.trans numeral_power_le_of_nat_cancel_iff)   
  
  have 21: "(\<exists>q. 4 ^ k - 1 =  3 * (2 * a + 1) * q)" 
    using 11 by auto
  hence "(4^k -1) mod ?c = 0 " 
    using zmod_eq_0_iff[of "4^k-1" ?c] by auto
  hence "4^k mod ?c = 1 mod ?c" 
    by (smt (verit, ccfv_SIG) "11" mod_mult_self2)
  hence "(4^k)^s mod ?c = 1 mod ?c"
    by (metis power_mod power_one)
  hence "((4^k)^s -1) mod ?c = 0" 
    by (smt (z3) mod_eqE zmod_eq_0_iff)
  then obtain f where f_def: "(4^k)^s - 1 = f*?c" 
    using zmod_eq_0_iff by force
  hence 40: "4^(s*k) = 1 + ?c*f"   
    by (simp add: mult.commute power_mult)
  hence "1 + f*?c \<ge> 1 + Z*?c" 
    using 20 by (metis int_ops(3) mult.commute of_nat_power_eq_of_nat_cancel_iff)
  hence 50: "f \<ge> Z" 
    using c by auto
  hence "Z \<le> f \<and> 1 + 3*(2*a+1)*f = 4^(s*k)" 
    using 40 by auto
  thus ?thesis 
    by auto
qed

(* The version which will be used in the proof of 9 Unknowns over N and Z *)
(* For every minimal value of b, there is an f such that b as defined is large enough. *)
lemma lemma_2_2_useful: 
  fixes a min_b :: int
  assumes "min_b \<ge> 0 \<and> a \<ge> 0"
  defines "b \<equiv> \<lambda>f. 1 + 3 * (2*a + 1) * f"
  shows "\<exists>f. f > 0 \<and> is_square (b f) \<and> is_power2 (b f) \<and> b f > min_b"
proof -
  have 0: "f > 0 \<Longrightarrow> b f > f" for f
    unfolding b_def using assms(1)
    by (simp add: add_strict_increasing)

  from lemma_2_2[of "min_b + 1" a] obtain f r
    where fr_def: "min_b + 1 \<le> f \<and> 1 + 3 * (2 * a + 1) * f = 4 ^ r"
    by (auto simp: assms(1))

  show ?thesis
  proof (rule exI[of _ f], intro conjI)
    show "f > 0"
      using fr_def assms by auto
    show "is_square (b f)"
      unfolding is_square_def b_def conjunct2[OF fr_def] power2_eq_square
      by (metis num_double numeral_times_numeral power_mult_distrib)
    show "is_power2 (b f)"
      unfolding b_def conjunct2[OF fr_def] by simp
    show "min_b < b f"
      using assms(1) conjunct1[OF fr_def]
      by (smt (verit) "0")
  qed
qed

end
