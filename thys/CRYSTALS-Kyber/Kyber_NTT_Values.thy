theory Kyber_NTT_Values

imports Kyber_Values
  NTT_Scheme
  Powers3844

begin
section \<open>Specification of Kyber with NTT\<close>
text \<open>Calculations for NTT specifications\<close>

lemma "3844 * 6584 = (1 :: fin7681 mod_ring)"
  by simp 

lemma "62 * 1115 = (1 :: fin7681 mod_ring)"
  by simp

lemma "256 * 7651 = (1:: fin7681 mod_ring)"
  by simp

lemma "7681 = 30 * 256 + (1::int)" by simp 


lemma powr256:  "3844 ^ 256 = (1::fin7681 mod_ring)" 
proof -
  have calc1: "3844^16 = (7154::fin7681 mod_ring)" by simp
  have calc2: "7154^16 = (1::fin7681 mod_ring)" by simp
  have "(3844::fin7681 mod_ring)^256 = (3844^16)^16"
    by (metis (mono_tags, opaque_lifting) num_double numeral_times_numeral power_mult)
  also have "\<dots> = 1" unfolding calc1 calc2 by auto
  finally show ?thesis by blast
qed



lemma powr256':
  "62 ^ 256 = (- 1::fin7681 mod_ring)" 
proof -
  have calc1: "62^16 = (1366::fin7681 mod_ring)" by simp
  have calc2: "1366^16 = (-1::fin7681 mod_ring)" by simp
  have "(62::fin7681 mod_ring)^256 = (62^16)^16"
    by (metis (mono_tags, opaque_lifting) num_double numeral_times_numeral power_mult)
  also have "\<dots> = -1" unfolding calc1 calc2 by auto
  finally show ?thesis by blast
qed

(*
powrs 3844^l for l=1..<256 in Powrs_3844 file"
*)


interpretation kyber7681_ntt: kyber_ntt 256 7681 3 8 
  "TYPE(fin7681)" "TYPE(3)" 3844 6584 62 1115 7651 30
proof (unfold_locales, goal_cases)
  case 4
  then show ?case using kyber7681.q_prime by fastforce
next
  case 6
  then show ?case using kyber7681.CARD_k by blast
next
  case 7
  then show ?case by (simp add: qr_poly'_fin7681_def)
next
  case 9
  then show ?case using powr256 by blast
next
  case 11
  then show ?case proof (safe, goal_cases)
    case (1 m)
    then show ?case using powr_less256[OF 1(2)]
      using linorder_not_less by blast
  qed
next
  case 15
  then show ?case using powr256' by blast
next
  case 17
  have mult: "256 * 7651 = (1::fin7681 mod_ring)" by simp
  have of_int: "of_int_mod_ring (int 256) = 256"
    by (metis o_def of_nat_numeral of_nat_of_int_mod_ring)
  show ?case unfolding of_int mult by simp
qed (auto)

end