subsection \<open>From multiple to single step relations\<close> 

theory MultipleToSingleSteps
  imports MachineEquations CommutationRelations "../Diophantine/Binary_And"
begin

text \<open>This file contains lemmas that are needed to prove the <-- direction of conclusion4.5 in the
file MachineEquationEquivalence. In particular, it is shown that single step equations follow 
from the multiple step relations. The key idea of Matiyasevich's proof is to code all register
and state values over the time into one large number. A further central statement in this file 
shows that the decoding of these numbers back to the single cell contents is indeed correct.\<close>

context 
    fixes a :: nat 
      and ic:: configuration
      and p :: program
      and q :: nat
      and r z :: "register \<Rightarrow> nat"
      and s :: "state \<Rightarrow> nat"
      and b c d e f :: nat
      and m n :: nat
      and Req Seq Zeq (* These variables are to store the single cell entries obtained from the
                         rows r s and z in the protocol *)
  
  assumes m_def: "m \<equiv> length p - 1"
      and n_def: "n \<equiv> length (snd ic)"
  
  assumes is_val: "is_valid_initial ic p a"

  (* rm_equations *)
  assumes m_eq: "mask_equations n r z c d e f"
      and r_eq: "reg_equations p r z s b a n q"
      and s_eq: "state_equations p s z b e q m"
      and c_eq: "rm_constants q c b d e f a"
  
  assumes Seq_def: "Seq = (\<lambda>k t. nth_digit (s k) t b)"
      and Req_def: "Req = (\<lambda>l t. nth_digit (r l) t b)"
      and Zeq_def: "Zeq = (\<lambda>l t. nth_digit (z l) t b)"

begin

text \<open>Basic properties\<close>
lemma n_gt0: "n>0"
  using n_def is_val is_valid_initial_def[of "ic" "p" "a"] is_valid_def
  by auto

lemma f_def: "f = (\<Sum>t = 0..q. 2^c * b^t)"
  using c_eq by (simp add: rm_constants_def F_def)
lemma e_def: "e = (\<Sum>t = 0..q. b^t)"
  using c_eq by (simp add: rm_constants_def E_def)
lemma d_def: "d = (\<Sum>t = 0..q. (2^c - 1) * b^t)"
  using c_eq by (simp add: D_def rm_constants_def)
lemma b_def: "b = 2^(Suc c)"
  using c_eq by (simp add: B_def rm_constants_def)

lemma b_gt1: "b > 1" using c_eq B_def rm_constants_def by auto

lemma c_gt0: "c > 0" using rm_constants_def c_eq by auto
lemma h0: "1 < (2::nat)^c"
  using c_gt0 one_less_numeral_iff one_less_power semiring_norm(76) by blast
(* this even implies b > 2, in fact b \<ge> 4 *)

lemma rl_fst_digit_zero:
  assumes "l < n"
  shows "nth_digit (r l) t b \<exclamdown> c = 0"
proof -
  have "2 ^ c - (Suc 0) < 2 ^ Suc c" using c_gt0 by (simp add: less_imp_diff_less)
  hence "\<forall>t. nth_digit d t b = (if t\<le>q then 2^c - 1 else 0)"
    using nth_digit_gen_power_series[of "\<lambda>x. 2^c - 1" "c"] d_def c_gt0 b_def
    by (simp add: d_def)
  then have d_lead_digit_zero: "\<forall>t. (nth_digit d t b) \<exclamdown> c = 0"
    by (auto simp: nth_bit_def)

  from m_eq have "(r l) \<preceq> d" 
    by (simp add: mask_equations_def assms)
  then have "\<forall>k. (r l) \<exclamdown> k \<le> d \<exclamdown> k"
    by (auto simp: masks_leq_equiv)
  then have "\<forall>t. (nth_digit (r l) t b \<exclamdown> c) \<le> (nth_digit d t b \<exclamdown> c)"
    using digit_gen_pow2_reduct[where ?c = "Suc c"] by (auto simp: b_def)
  thus ?thesis
    by (auto simp: d_lead_digit_zero)
qed

lemma e_mask_bound:
  assumes "x \<preceq> e"
  shows "nth_digit x t b \<le> 1"
proof -
   have x_bounded: "nth_digit x t' b \<le> nth_digit e t' b" for t' 
   proof -
     have "\<forall>t'. x \<exclamdown> t' \<le> e \<exclamdown> t'" using assms masks_leq_equiv by auto
     then have k_lt_c: "\<forall>t'. \<forall>k'<Suc c. nth_digit x t' b \<exclamdown> k'
                                          \<le> nth_digit e t' b \<exclamdown> k'"
       using digit_gen_pow2_reduct by (auto simp: b_def) (metis power_Suc)
     
     have "k\<ge>Suc c \<Longrightarrow> x mod (2 ^ Suc c) div 2 ^ k = 0" for k x::nat
       by (simp only: drop_bit_take_bit flip: take_bit_eq_mod drop_bit_eq_div) simp
     then have "\<forall>k\<ge>Suc c. nth_digit x y b \<exclamdown> k = 0" for x y
       using b_def nth_bit_def nth_digit_def by auto
     then have k_gt_c: "\<forall>t'. \<forall>k'\<ge>Suc c. nth_digit x t' b \<exclamdown> k' 
                                     \<le> nth_digit e t' b \<exclamdown> k'"
       by auto
      
     from k_lt_c k_gt_c have "nth_digit x t' b \<le> nth_digit e t' b" for t'
       using bitwise_leq by (meson not_le)
    thus ?thesis by auto
  qed

  have "\<forall>k. Suc 0 < 2^c" using c_gt0 h0 by auto
  hence e_aux: "nth_digit e tt b \<le> 1" for tt
    using e_def b_def c_gt0 nth_digit_gen_power_series[of "\<lambda>k. Suc 0" "c" "q"] by auto

  show ?thesis using e_aux[of "t"] x_bounded[of "t"] using le_trans by blast
qed

(* --- individual bounds --- *)
lemma sk_bound:
  shows "\<forall>t k. k\<le>length p - 1 \<longrightarrow> nth_digit (s k) t b \<le> 1"
proof -
  have "\<forall>k\<le>length p - 1. s k \<preceq> e" using s_eq state_equations_def m_def by auto
  thus ?thesis using e_mask_bound by auto
qed

lemma sk_bitAND_bound:
  shows "\<forall>t k. k\<le>length p - 1 \<longrightarrow> nth_digit (s k && x k) t b \<le> 1"
  using bitAND_nth_digit_commute sk_bound bitAND_lt masks_leq
  by (auto simp: b_def) (meson dual_order.trans)

lemma s_bound:
  shows "\<forall>j<m. s j < b ^ q"
  using s_eq state_equations_def by auto

lemma sk_sum_masked:
  shows "\<forall>M\<le>m. (\<Sum>k\<le>M. s k) \<preceq> e"
  using s_eq state_equations_def by auto

lemma sk_sum_bound:
  shows "\<forall>t M. M\<le>length p - 1 \<longrightarrow> nth_digit (\<Sum>k\<le>M. s k) t b \<le> 1"
  using sk_sum_masked e_mask_bound m_def by auto

lemma sum_sk_bound:
  shows "(\<Sum>k\<le>length p - 1. nth_digit (s k) t b) \<le> 1"
proof -
  have "\<forall>t m. m \<le> length p - 1 \<longrightarrow> nth_digit (sum s {0..m}) t b < 2 ^ c"
    using sk_sum_bound b_def c_gt0 h0
    by (metis atLeast0AtMost le_less_trans)
  moreover have "\<forall>t k. k \<le> length p - 1 \<longrightarrow> nth_digit (s k) t b < 2 ^ c"
    using sk_bound b_def c_gt0 h0
    by (metis le_less_trans)
  
  ultimately have "nth_digit (\<Sum>k\<le>length p - 1. s k) t b
                                  = (\<Sum>k\<le>length p - 1. nth_digit (s k) t b)"
    using b_def c_gt0
    using finite_sum_nth_digit_commute2[where ?M = "length p - 1"]
    by (simp add: atMost_atLeast0)

  thus ?thesis using sk_sum_bound by (metis order_refl)
qed

lemma bitAND_sum_lt: "(\<Sum>k\<le>length p - 1. nth_digit (s k && x k) t b)
                      \<le> (\<Sum>k\<le>length p - 1. Seq k t)"
proof -
  have "(\<Sum>k\<le>length p - 1. nth_digit (s k && x k) t b)
        = (\<Sum>k\<le>length p - 1. nth_digit (s k) t b && nth_digit (x k) t b)"
    using bitAND_nth_digit_commute b_def by auto
  also have "... \<le> (\<Sum>k\<le>length p - 1. nth_digit (s k) t b)"
    using bitAND_lt by (simp add: sum_mono)
  finally show ?thesis using Seq_def by auto
qed


lemma states_unique_RAW:
  "\<forall>k\<le>m. Seq k t = 1 \<longrightarrow> (\<forall>j\<le>m. j \<noteq> k \<longrightarrow> Seq j t = 0)"
proof -
  {
    fix k
    assume "k\<le>m"
    assume skt_1: "Seq k t = 1"

    have "\<forall>j\<le>m. j \<noteq> k \<longrightarrow> Seq j t = 0"
    proof -
      {
        fix j
        assume "j\<le>m"
        assume "j \<noteq> k"
        let ?fct = "(\<lambda>k. Seq k t)"

        have "Seq j t = 0"
        proof (rule ccontr)
          assume "Seq j t \<noteq> 0"
          then have "Seq j t + Seq k t > 1"
            using skt_1 by auto
          moreover have "sum ?fct {0..m} \<ge> sum ?fct {j, k}"
            using `j\<le>m` `k\<le>m` sum_mono2
            by (metis atLeastAtMost_iff empty_subsetI finite_atLeastAtMost insert_subset le0)
          ultimately have "(\<Sum>k\<le>m. Seq k t) > 1"
            by (simp add: \<open>j \<noteq> k\<close> atLeast0AtMost)
          thus "False"
            using sum_sk_bound[where ?t = t]
            by (auto simp: Seq_def m_def)
        qed
      }
      thus ?thesis by auto
    qed
  }
  thus ?thesis by auto
qed

lemma block_sum_radd_bound:
  shows "\<forall>t. (\<Sum>R+ p l (\<lambda>k. nth_digit (s k) t b)) \<le> 1"
proof -
  {
    fix t
    have "(\<Sum>R+ p l (\<lambda>k. Seq k t)) \<le> (\<Sum>k\<le>length p - 1. Seq k t)"
      unfolding sum_radd.simps
      by (simp add: atMost_atLeast0 sum_mono)
    hence "(\<Sum>R+ p l (\<lambda>k. Seq k t)) \<le> 1"
      using sum_sk_bound[of t] Seq_def
      using dual_order.trans by blast
  }
  thus ?thesis using Seq_def by auto
qed

lemma block_sum_rsub_bound:
  shows "\<forall>t. (\<Sum>R- p l (\<lambda>k. nth_digit (s k && z l) t b)) \<le> 1"
proof -
  {
    fix t
    have "(\<Sum>R- p l (\<lambda>k. nth_digit (s k && z l) t b))
          \<le> (\<Sum>k\<le>length p - 1. nth_digit (s k && z l) t b)"
      unfolding sum_rsub.simps
      by (simp add: atMost_atLeast0 sum_mono)
    also have "... \<le> (\<Sum>k\<le>length p - 1. Seq k t)"
      using bitAND_sum_lt[where ?x = "\<lambda>k. z l"] by blast
    finally have "(\<Sum>R- p l (\<lambda>k. nth_digit (s k && z l) t b)) \<le> 1"
      using sum_sk_bound[of t] Seq_def
      using dual_order.trans by blast
  }
  thus ?thesis using Seq_def by auto
qed

lemma block_sum_rsub_special_bound:
  shows "\<forall>t. (\<Sum>R- p l (\<lambda>k. nth_digit (s k) t b)) \<le> 1"
proof -
  {
    fix t
    have "(\<Sum>R- p l (\<lambda>k. nth_digit (s k) t b))
          \<le> (\<Sum>k\<le>length p - 1. nth_digit (s k) t b)"
      unfolding sum_rsub.simps
      by (simp add: atMost_atLeast0 sum_mono)
    then have "(\<Sum>R- p l (\<lambda>k. nth_digit (s k) t b)) \<le> 1"
      using sum_sk_bound[of t]
      using dual_order.trans by blast
  }
  thus ?thesis using Seq_def by auto
qed

lemma block_sum_sadd_bound:
  shows "\<forall>t. (\<Sum>S+ p j (\<lambda>k. nth_digit (s k) t b)) \<le> 1"
proof -
  {
    fix t
    have "(\<Sum>S+ p j (\<lambda>k. Seq k t)) \<le> (\<Sum>k\<le>length p - 1. Seq k t)"
      unfolding sum_sadd.simps
      by (simp add: atMost_atLeast0 sum_mono)
    hence "(\<Sum>S+ p j (\<lambda>k. Seq k t)) \<le> 1"
      using sum_sk_bound[of t] Seq_def
      using dual_order.trans by blast
  }
  thus ?thesis using Seq_def by auto
qed

lemma block_sum_ssub_bound:
  shows "\<forall>t. (\<Sum>S- p j (\<lambda>k. nth_digit (s k && z (l k)) t b)) \<le> 1"
proof -
  {
    fix t
    have "(\<Sum>S- p j (\<lambda>k. nth_digit (s k && z (l k)) t b))
          \<le> (\<Sum>k\<le>length p - 1. nth_digit (s k && z (l k)) t b)"
      unfolding sum_ssub_nzero.simps
      by (simp add: atMost_atLeast0 sum_mono)
    also have "... \<le> (\<Sum>k\<le>length p - 1. Seq k t)"
      using bitAND_sum_lt[where ?x = "\<lambda>k. z (l k)"] by blast
    finally have "(\<Sum>S- p j (\<lambda>k. nth_digit (s k && z (l k)) t b)) \<le> 1"
      using sum_sk_bound[of t] Seq_def
      using dual_order.trans by blast
  }
  thus ?thesis using Seq_def by auto
qed

lemma block_sum_szero_bound:
  shows "\<forall>t. (\<Sum>S0 p j (\<lambda>k. nth_digit (s k && (e - z (l k))) t b)) \<le> 1"
proof -
  {
    fix t
    have "(\<Sum>S0 p j (\<lambda>k. nth_digit (s k && e - z (l k)) t b))
          \<le> (\<Sum>k\<le>length p - 1. nth_digit (s k && e - z (l k)) t b)"
      unfolding sum_ssub_zero.simps
      by (simp add: atMost_atLeast0 sum_mono)
    also have "... \<le> (\<Sum>k\<le>length p - 1. Seq k t)"
      using bitAND_sum_lt[where ?x = "\<lambda>k. e - z (l k)"] by blast
    finally have "(\<Sum>S0 p j (\<lambda>k. nth_digit (s k && e - z (l k)) t b)) \<le> 1"
      using sum_sk_bound[of t] Seq_def
      using dual_order.trans by blast
  }
  thus ?thesis using Seq_def by auto
qed

lemma sum_radd_nth_digit_commute:
  shows "nth_digit (\<Sum>R+ p l (\<lambda>k. s k)) t b = \<Sum>R+ p l (\<lambda>k. nth_digit (s k) t b)"
proof -
  have a1: "\<forall>t. \<forall>k\<le>length p - 1. nth_digit (s k) t b < 2^c"
    using sk_bound h0 by (meson le_less_trans)

  have a2: "\<forall>t. (\<Sum>R+ p l (\<lambda>k. nth_digit (s k) t b)) < 2^c"
    using block_sum_radd_bound h0 by (meson le_less_trans)

  show ?thesis
    using a1 a2 c_gt0 b_def unfolding sum_radd.simps
    using sum_nth_digit_commute[where ?g = "\<lambda>l k. isadd (p ! k) \<and> l = modifies (p ! k)"]
    by blast
qed

lemma sum_rsub_nth_digit_commute:
  shows "nth_digit (\<Sum>R- p l (\<lambda>k. s k && z l)) t b
         = \<Sum>R- p l (\<lambda>k. nth_digit (s k && z l) t b)"
proof -
  have a1: "\<forall>t. \<forall>k\<le>length p - 1. nth_digit (s k && z l) t b < 2^c"
    using sk_bitAND_bound[where ?x = "\<lambda>k. z l"] h0 le_less_trans by blast

  have a2: "\<forall>t. (\<Sum>R- p l (\<lambda>k. nth_digit (s k && z l) t b)) < 2^c"
    using block_sum_rsub_bound h0 by (meson le_less_trans)

  show ?thesis
    using a1 a2 c_gt0 b_def unfolding sum_rsub.simps
    using sum_nth_digit_commute
            [where ?g = "\<lambda>l k. issub (p ! k) \<and> l = modifies (p ! k)" and ?fct = "\<lambda>k. s k && z l"]
    by blast
qed

lemma sum_sadd_nth_digit_commute:
  shows "nth_digit (\<Sum>S+ p j (\<lambda>k. s k)) t b = \<Sum>S+ p j (\<lambda>k. nth_digit (s k) t b)"
proof -
  have a1: "\<forall>t. \<forall>k\<le>length p - 1. nth_digit (s k) t b < 2^c"
    using sk_bound h0 by (meson le_less_trans)

  have a2: "\<forall>t. (\<Sum>S+ p j (\<lambda>k. nth_digit (s k) t b)) < 2^c"
    using block_sum_sadd_bound h0 by (meson le_less_trans)

  show ?thesis
    using a1 a2 b_def c_gt0 unfolding sum_sadd.simps
    using sum_nth_digit_commute[where ?g = "\<lambda>j k. isadd (p ! k) \<and> j = goes_to (p ! k)"]
    by blast
qed

lemma sum_ssub_nth_digit_commute:
  shows "nth_digit (\<Sum>S- p j (\<lambda>k. s k && z (l k))) t b
         = \<Sum>S- p j (\<lambda>k. nth_digit (s k && z (l k)) t b)"
proof -
  have a1: "\<forall>t. \<forall>k\<le>length p - 1. nth_digit (s k && z (l k)) t b < 2^c"
    using sk_bitAND_bound[where ?x = "\<lambda>k. z (l k)"] h0 le_less_trans by blast

  have a2: "\<forall>t. (\<Sum>S- p j (\<lambda>k. nth_digit (s k && z (l k)) t b)) < 2^c"
    using block_sum_ssub_bound h0 by (meson le_less_trans)

  show ?thesis
    using a1 a2 b_def c_gt0 unfolding sum_ssub_nzero.simps
    using sum_nth_digit_commute
            [where ?g = "\<lambda>j k. issub (p ! k) \<and> j = goes_to (p ! k)" and ?fct = "\<lambda>k. s k && z (l k)"]
    by blast
qed

lemma sum_szero_nth_digit_commute:
  shows "nth_digit (\<Sum>S0 p j (\<lambda>k. s k && (e - z (l k)))) t b
         = \<Sum>S0 p j (\<lambda>k. nth_digit (s k && (e - z (l k))) t b)"
proof -
  have a1: "\<forall>t. \<forall>k\<le>length p - 1. nth_digit (s k && (e - z (l k))) t b < 2^c"
    using sk_bitAND_bound[where ?x = "\<lambda>k. e - z (l k)"] h0 le_less_trans by blast

  have a2: "\<forall>t. (\<Sum>S0 p j (\<lambda>k. nth_digit (s k && (e - z (l k))) t b)) < 2^c"
    using block_sum_szero_bound h0 by (meson le_less_trans)

  show ?thesis
    using a1 a2 b_def c_gt0 unfolding sum_ssub_zero.simps
    using sum_nth_digit_commute
            [where ?g = "\<lambda>j k. issub (p ! k) \<and> j = goes_to_alt (p ! k)" and ?fct = "\<lambda>k. s k && e - z (l k)"]
    by blast
qed

lemma block_bound_impl_fst_digit_zero:
  assumes "nth_digit x t b \<le> 1"
  shows "(nth_digit x t b) \<exclamdown> c = 0"
  using assms apply (auto simp: nth_bit_def)
  by (metis (no_types, opaque_lifting) c_gt0 div_le_dividend le_0_eq le_Suc_eq mod_0 mod_Suc
            mod_div_trivial numeral_2_eq_2 power_eq_0_iff power_mod)

lemma sum_radd_block_bound:
  shows "nth_digit (\<Sum>R+ p l (\<lambda>k. s k)) t b \<le> 1"
  using block_sum_radd_bound sum_radd_nth_digit_commute by auto
lemma sum_radd_fst_digit_zero:
  shows "(nth_digit (\<Sum>R+ p l s) t b) \<exclamdown> c = 0"
  using sum_radd_block_bound block_bound_impl_fst_digit_zero by auto

lemma sum_sadd_block_bound:
  shows "nth_digit (\<Sum>S+ p j (\<lambda>k. s k)) t b \<le> 1"
  using block_sum_sadd_bound sum_sadd_nth_digit_commute by auto
lemma sum_sadd_fst_digit_zero:
  shows "(nth_digit (\<Sum>S+ p j s) t b) \<exclamdown> c = 0"
  using sum_sadd_block_bound block_bound_impl_fst_digit_zero by auto

lemma sum_ssub_block_bound:
  shows "nth_digit (\<Sum>S- p j (\<lambda>k. s k && z (l k))) t b \<le> 1"
  using block_sum_ssub_bound sum_ssub_nth_digit_commute by auto
lemma sum_ssub_fst_digit_zero:
  shows "(nth_digit (\<Sum>S- p j (\<lambda>k. s k && z (l k))) t b) \<exclamdown> c = 0"
  using sum_ssub_block_bound block_bound_impl_fst_digit_zero by auto

lemma sum_szero_block_bound:
  shows "nth_digit (\<Sum>S0 p j (\<lambda>k. s k && (e - z (l k)))) t b \<le> 1"
  using block_sum_szero_bound sum_szero_nth_digit_commute by auto
lemma sum_szero_fst_digit_zero:
  shows "(nth_digit (\<Sum>S0 p j (\<lambda>k. s k && (e - z (l k)))) t b) \<exclamdown> c = 0"
  using sum_szero_block_bound block_bound_impl_fst_digit_zero by auto

lemma sum_rsub_special_block_bound:
  shows "nth_digit (\<Sum>R- p l (\<lambda>k. s k)) t b \<le> 1"
proof -
  have a1: "\<forall>t k. k \<le> length p - 1 \<longrightarrow> nth_digit (s k) t b < 2^c"
    using sk_bound h0 le_less_trans by blast
  have a2: "\<forall>t. \<Sum>R- p l (\<lambda>k. nth_digit (s k) t b) < 2^c"
    using block_sum_rsub_special_bound h0 le_less_trans by blast

  have "nth_digit (\<Sum>R- p l (\<lambda>k. s k)) t b = \<Sum>R- p l (\<lambda>k. nth_digit (s k) t b)"
    using a1 a2 b_def c_gt0 unfolding sum_rsub.simps
    using sum_nth_digit_commute[where ?g = "\<lambda>l k. issub (p ! k) \<and> l = modifies (p ! k)"]
    by blast

  thus ?thesis
    using block_sum_rsub_special_bound by auto
qed

lemma sum_state_special_block_bound:
  shows "nth_digit (\<Sum>S+ p j (\<lambda>k. s k)
          + \<Sum>S0 p j (\<lambda>k. s k && (e - z (l k)))) t b \<le> 1"
proof -
  have aux_sum_zero:
    "\<Sum>S0 p j (\<lambda>k. nth_digit (s k) t b && nth_digit (e - z (l k)) t b)
      \<le> \<Sum>S0 p j (\<lambda>k. nth_digit (s k) t b)"
    unfolding sum_ssub_zero.simps
    by (auto simp: bitAND_lt sum_mono)

  have aux_addsub_excl: "(if isadd (p ! k) then Seq k t else 0)
                            + (if issub (p ! k) then Seq k t else 0)
                       = (if isadd (p ! k) \<or> issub (p ! k) then Seq k t else 0)" for k
    by auto

  have aux_sum_add_lt:
    "\<Sum>S+ p j (\<lambda>k. Seq k t) \<le> (\<Sum>k = 0..length p - 1. if isadd (p ! k) then Seq k t else 0)"
    unfolding sum_sadd.simps by (simp add: sum_mono)
  have aux_sum_sub_lt:
    "\<Sum>S0 p j (\<lambda>k. Seq k t) \<le> (\<Sum>k = 0..length p - 1. if issub (p ! k) then Seq k t else 0)"
    unfolding sum_ssub_zero.simps by (simp add: sum_mono)

  have "nth_digit (\<Sum>S+ p j (\<lambda>k. s k)
                            + \<Sum>S0 p j (\<lambda>k. s k && e - z (l k))) t b
        = nth_digit (\<Sum>S+ p j (\<lambda>k. s k)) t b
            + nth_digit (\<Sum>S0 p j (\<lambda>k. s k && e - z (l k))) t b"
    using sum_sadd_fst_digit_zero sum_szero_fst_digit_zero block_additivity
    by (auto simp: c_gt0 b_def)
  also have "... = \<Sum>S+ p j (\<lambda>k. nth_digit (s k) t b)       
                  + \<Sum>S0 p j (\<lambda>k. nth_digit (s k && e - z (l k)) t b)"
    by (simp add: sum_sadd_nth_digit_commute sum_szero_nth_digit_commute)
  also have "... \<le> \<Sum>S+ p j (\<lambda>k. Seq k t) + \<Sum>S0 p j (\<lambda>k. Seq k t)"
    using bitAND_nth_digit_commute aux_sum_zero
    unfolding Seq_def by (simp add: b_def)
  also have "... \<le> (\<Sum>k = 0..length p - 1. if isadd (p ! k) then Seq k t else 0) +
                      (\<Sum>k = 0..length p - 1. if issub (p ! k) then Seq k t else 0)"
    using aux_sum_add_lt aux_sum_sub_lt by auto
  also have "... = (\<Sum>k\<le>length p - 1. if (isadd (p ! k) \<or> issub (p ! k))
                                       then Seq k t else 0)"
    using aux_addsub_excl
    using sum.distrib[where ?g = "\<lambda>k. if isadd (p ! k) then Seq k t else 0"
                        and ?h = "\<lambda>k. if issub (p ! k) then Seq k t else 0"]
    by (auto simp: aux_addsub_excl atMost_atLeast0)
  also have "... \<le> (\<Sum>k\<le>length p - 1. Seq k t)"
      by (smt eq_iff le0 sum_mono)

  finally show ?thesis using sum_sk_bound[of t] Seq_def by auto
qed
lemma sum_state_special_fst_digit_zero:
  shows "(nth_digit (\<Sum>S+ p j (\<lambda>k. s k)
                            + \<Sum>S0 p j (\<lambda>k. s k && (e - z (modifies (p!k))))) t b) \<exclamdown> c = 0"
  using sum_state_special_block_bound block_bound_impl_fst_digit_zero by auto

text \<open>Main three redution lemmas: Zero Indicators, Registers, States\<close>

lemma Z:
  assumes "l<n"
  shows "Zeq l t = (if Req l t > 0 then Suc 0 else 0)"
proof -
  have cond: "2^c * (z l) = (r l + d) && f" using m_eq mask_equations_def assms by auto
  have d_block: "\<forall>t\<le>q. nth_digit d t b = 2^c - 1" using d_def b_def 
      less_imp_diff_less nth_digit_gen_power_series[of "\<lambda>_. 2^c-1" "c"] c_gt0 by auto
  have rl_bound: "t\<le>q \<longrightarrow> nth_digit (r l) t b \<exclamdown> c= 0" for t by (simp add: assms rl_fst_digit_zero)
  have f_block: "\<forall>t\<le>q. nth_digit f t b = 2^c"
    using f_def b_def less_imp_diff_less nth_digit_gen_power_series[of "\<lambda>_. 2^c" c] c_gt0 by auto
  then have "\<forall>t\<le>q.\<forall>k<c. nth_digit f t b \<exclamdown> k = 0"  by (simp add: aux_powertwo_digits)

  moreover have AND_gen: "\<forall>t\<le>q.\<forall>k\<le>c. nth_digit ((r l + d) && f) t b \<exclamdown> k = (nth_digit (r l + d) t b \<exclamdown> k) * nth_digit f t b \<exclamdown> k"
    using b_def digit_gen_pow2_reduct bitAND_digit_mult digit_gen_pow2_reduct le_imp_less_Suc by presburger
  ultimately have "\<forall>t\<le>q.\<forall>k<c. nth_digit ((r l + d) && f) t b \<exclamdown> k = 0" using f_def by auto
  moreover have "(r l + d) && f < b ^ Suc q" using lm0245[of "r l + d" f] masks_leq[of "(r l + d) && f" f] f_def
  proof-
    have "2 < b" using b_def c_gt0 gr0_conv_Suc not_less_iff_gr_or_eq by fastforce
    then have "b^u + b^u < b* b^ u" for u using zero_less_power[of b u] mult_less_mono1[of 2 b "b^u"] by linarith
    then have "(\<Sum>t\<in>{..<q}. b ^ t) <  b ^ q" apply(induct q, auto) subgoal for q 
        using add_strict_right_mono[of " sum ((^) b) {..<q}" "b^q" "b^q"] less_trans by blast done
    then have "(\<Sum>t\<in>{..<q}.2^c* b ^ t) < 2^c * b^ q" using sum_distrib_left[of "2^c" "\<lambda>q. b^q" "{..<q}"]
     zero_less_power[of 2 c] mult_less_mono1[of "sum ((^) b) {..<q}" "b ^ q" "2^c"] by (simp add: mult.commute)
    moreover have "2 ^ c * b ^ q = b ^ Suc q div 2" using b_def by auto
    moreover have "f= (\<Sum>t\<in>{..<q}.2^c* b ^ t) + 2^c*b^q" 
        using f_def atLeastLessThanSuc_atLeastAtMost c_eq rm_constants_def gr0_conv_Suc lessThan_atLeast0 by auto
    ultimately have "f < b ^ Suc q" by linarith
    moreover have "(r l + d) && f \<le> f" using lm0245[of "r l + d" f] masks_leq[of "(r l + d) && f" f] by auto
    ultimately show ?thesis by auto
  qed
  then have rldf0: "t>q \<longrightarrow> nth_digit ((r l + d) && f) t b = 0" for t using nth_digit_def[of "r l + d && f" t b]
    div_less[of "r l + d && f" "b^t"] b_def power_increasing[of "Suc q" t b] by auto
  moreover have "\<forall>t>q.\<forall>k<c. nth_digit ((r l + d) && f) t b \<exclamdown> k = 0" using aux_lt_implies_mask rldf0 by fastforce
  ultimately have AND_zero: "\<forall>t.\<forall>k<c. nth_digit ((r l + d) && f) t b \<exclamdown> k = 0" using leI by blast

  have "0<k \<Longrightarrow> k< Suc c \<Longrightarrow> nth_digit (z l) t b \<exclamdown> k = nth_digit ((r l + d) && f) (Suc t) b \<exclamdown> (k - 1)" 
    for k using b_def nth_digit_bound digit_gen_pow2_reduct[of k "Suc c" "z l" t] aux_digit_shift[of "z l" c "t + c * t + k"]
    digit_gen_pow2_reduct[of "k-1" "Suc c" "z l * 2^c" "Suc t"] cond by (simp add: add.commute add.left_commute mult.commute)
  then have aux: "0<k \<Longrightarrow> k< Suc c \<Longrightarrow> nth_digit (z l) t b \<exclamdown> k = 0" for k using AND_zero by auto 
  have zl_formula: "nth_digit (z l) t b =  nth_digit (z l) t b \<exclamdown> 0 "
    using b_def digit_sum_repr[of "nth_digit (z l) t b" "Suc c"]
  proof -
    have "nth_digit (z l) t b < 2 ^ Suc c
          \<Longrightarrow> nth_digit (z l) t b = (\<Sum>k\<in>{0..<Suc c}. nth_digit (z l) t b \<exclamdown> k * 2 ^ k)"
      using b_def digit_sum_repr[of "nth_digit (z l) t b" "Suc c"]
      by (simp add: atLeast0LessThan)
    hence "nth_digit (z l) t b < 2 ^ Suc c
          \<Longrightarrow> nth_digit (z l) t b = nth_digit (z l) t b \<exclamdown> 0
                                            + (\<Sum>k\<in>{0<..<Suc c}. nth_digit (z l) t b \<exclamdown> k * 2 ^ k)"
      by (metis One_nat_def atLeastSucLessThan_greaterThanLessThan mult_numeral_1_right
                numeral_1_eq_Suc_0 power_0 sum.atLeast_Suc_lessThan zero_less_Suc)
    thus ?thesis using aux nth_digit_bound b_def by auto
  qed

  consider (tleq) "t\<le>q" |(tgq) "t>q" by linarith
  then show ?thesis
  proof cases
    case tleq
    then have t_bound: "t \<le> q" by auto
    have "nth_digit ((r l + d) && f) t b \<exclamdown> c =  (nth_digit (r l + d) t b \<exclamdown> c)" 
      using f_block bitAND_single_digit AND_gen t_bound by auto
    moreover have "nth_digit (r l + d && f) t b < 2 ^ Suc c" using nth_digit_def b_def by simp
    ultimately have AND_all:"nth_digit ((r l + d) && f) t b = (nth_digit (r l + d) t b \<exclamdown> c) * 2^c" using AND_gen AND_zero
      using digit_sum_repr[of "nth_digit ((r l + d) && f) t b" "Suc c"] by auto
  
    then have "\<forall>k<c. nth_digit (2^c * (z l)) t b \<exclamdown> k =  0" using cond AND_zero by metis
    moreover have "nth_digit (2^c * (z l)) t b \<exclamdown> c =  nth_digit (z l) t b \<exclamdown> 0"
      using digit_gen_pow2_reduct[of c "Suc c" " (2^c * (z l))" t]
            digit_gen_pow2_reduct[of 0 "Suc c" "z l" t] b_def by (simp add: aux_digit_shift mult.commute)
    ultimately have zl0: "nth_digit (2^c * (z l)) t b = 2^c * nth_digit (z l) t b \<exclamdown> 0"
      using digit_sum_repr[of "nth_digit (2^c * (z l)) t b" "Suc c"] nth_digit_bound b_def by auto
  
    have "nth_digit (2^c * (z l)) t b = 2^c * nth_digit (z l) t b" using zl0 zl_formula by auto
    then have zl_block: "nth_digit (z l) t b = nth_digit (r l + d) t b \<exclamdown> c" using AND_all cond by auto
  
    consider (g0) "Req l t > 0" | (e0) "Req l t = 0 " by auto
    then show ?thesis
    proof cases
      case e0
      show ?thesis using e0 apply(auto simp add: Req_def Zeq_def) subgoal
      proof-
        assume asm: "nth_digit (r l) t b = 0"
        have add:"((nth_digit d t b) + (nth_digit (r l) t b)) \<exclamdown> c = 0" by (simp add: asm d_block nth_bit_def t_bound)
        from d_block t_bound have "nth_digit d (t-1) b \<exclamdown> c = 0"
          using add asm by auto
        then have "(nth_digit (r l + d) t b) \<exclamdown> c = 0" 
          using add digit_wise_block_additivity[of "r l" "t" "c" "d" "c"] rl_bound[of "t-1"] b_def asm t_bound c_gt0 by auto
        then show ?thesis using zl_block by simp
      qed done
    next
      case g0
      show ?thesis using g0 apply(auto simp add: Req_def Zeq_def) subgoal
      proof -
        assume "0 < nth_digit (r l) t b"
        then obtain k0 where k0_def: "nth_digit (r l) t b \<exclamdown> k0 = 1" using aux0_digit_wise_equiv by auto
        then have "k0\<le>c" using nth_digit_bound[of "r l" t c] b_def aux_lt_implies_mask by (metis Suc_leI leI zero_neq_one)
        then have k0bound: "k0<c" using rl_fst_digit_zero using k0_def le_less rl_bound t_bound by fastforce
        moreover have d_dig: "\<forall>k<c. nth_digit d t b \<exclamdown> k = 1" using d_block t_bound nth_bit_def[of "nth_digit d t b"]
          by (metis One_nat_def Suc_1 Suc_diff_Suc Suc_pred dmask_aux even_add even_power odd_iff_mod_2_eq_one 
              one_mod_two_eq_one plus_1_eq_Suc zero_less_Suc zero_less_power)
        ultimately have "nth_digit d t b \<exclamdown> k0 = 1" by simp
        then have "bin_carry (nth_digit d t b) (nth_digit (r l) t b) (Suc k0) = 1" using  
             k0_def sum_carry_formula carry_bounded less_eq_Suc_le by simp
        moreover have "\<And>n. Suc k0 \<le> n \<Longrightarrow> n < c \<Longrightarrow> bin_carry (nth_digit d t b) (nth_digit (r l) t b) n =
             Suc 0 \<Longrightarrow> bin_carry (nth_digit d t b) (nth_digit (r l) t b) (Suc n) = Suc 0" subgoal for n
        proof-
          assume "n<c" "bin_carry (nth_digit d t b) (nth_digit (r l) t b) n =  Suc 0"
          then show ?thesis using d_dig sum_carry_formula
              carry_bounded[of "(nth_digit d t b)" "(nth_digit (r l) t b)"  "Suc n" ] by auto
        qed done
        ultimately have "bin_carry (nth_digit d t b) (nth_digit (r l) t b) c = 1" (is "?P c") 
          using dec_induct[of "Suc k0" c ?P] by (simp add: Suc_le_eq k0bound)
  
        then have add:"((nth_digit d t b) + (nth_digit (r l) t b)) \<exclamdown> c = 1"
          using sum_digit_formula[of "nth_digit d t b" "nth_digit (r l) t b" c]
            d_block nth_bit_def t_bound assms rl_fst_digit_zero by auto

        from d_block t_bound have "nth_digit d (t-1) b \<exclamdown> c = 0"
          by (smt aux_lt_implies_mask diff_le_self diff_less le_eq_less_or_eq le_trans
                  zero_less_numeral zero_less_one zero_less_power)
        then have "(nth_digit (r l + d) t b) \<exclamdown> c = 1" using add b_def t_bound 
            block_additivity assms rl_fst_digit_zero c_gt0 d_block by (simp add: add.commute)
        then show ?thesis using zl_block by simp
      qed done
    qed
  next
    case tgq
    then have t_bound: "q<t" by auto
    (* (r l) is 0 for all blocks *)
    have "r l < b ^ q" using reg_equations_def assms r_eq by auto
    then have rl0: "nth_digit (r l) t b = 0" using t_bound nth_digit_def[of "r l" t b] b_gt1 
        power_strict_increasing[of q t b] by fastforce
    then have "\<forall>k<c. nth_digit (2^c * (z l)) t b \<exclamdown> k = 0" using cond AND_zero by simp
    (* the next two statements are already proven above but here they rely on rl0 *)
    moreover have "nth_digit (2^c * (z l)) t b \<exclamdown> c = nth_digit (z l) t b \<exclamdown> 0"
      using digit_gen_pow2_reduct[of c "Suc c" " (2^c * (z l))" t]
            digit_gen_pow2_reduct[of 0 "Suc c" "z l" t] b_def by (simp add: aux_digit_shift mult.commute)
    ultimately have zl0: "nth_digit (2^c * (z l)) t b = 2^c * nth_digit (z l) t b \<exclamdown> 0"
      using digit_sum_repr[of "nth_digit (2^c * (z l)) t b" "Suc c"] nth_digit_bound b_def by auto
    have "0<k \<Longrightarrow> k< Suc c \<Longrightarrow> nth_digit (z l) t b \<exclamdown> k = nth_digit ((r l + d) && f) (Suc t) b \<exclamdown> (k - 1)" 
      for k using b_def nth_digit_bound digit_gen_pow2_reduct[of k "Suc c" "z l" t] aux_digit_shift[of "z l" c "t + c * t + k"]
      digit_gen_pow2_reduct[of "k-1" "Suc c" "z l * 2^c" "Suc t"] cond by (simp add: add.commute add.left_commute mult.commute)
    (* Using some simplification lemmas, the result follows *)
    then show ?thesis using Zeq_def Req_def cond rl0 zl0 rldf0 zl_formula t_bound by auto 
  qed 
qed

lemma zl_le_rl: "l<n \<Longrightarrow> z l \<le> r l" for l
proof -
  assume l: "l < n"
  have "Zeq l t \<le> Req l t" for t using Z l by auto
  hence "nth_digit (z l) t b \<le> nth_digit (r l) t b" for t
    using Zeq_def Req_def by auto
  thus ?thesis using digitwise_leq b_gt1 by auto
qed


lemma modifies_valid: "\<forall>k\<le>m. modifies (p!k) < n"
proof -
  have reg_check: "program_register_check p n"
    using is_val by (cases ic, auto simp: is_valid_initial_def n_def is_valid_def)
  {
    fix k
    assume "k \<le> m"
    then have "p ! k \<in> set p"
      by (metis \<open>k \<le> m\<close> add_eq_if diff_le_self is_val le_antisym le_trans m_def
                n_not_Suc_n not_less not_less0 nth_mem p_contains)
    then have "instruction_register_check n (p ! k)"
      using reg_check by (auto simp: list_all_def)
    then have "modifies (p!k) < n"  by (cases "p ! k", auto simp: n_gt0)
  }
  thus ?thesis by auto
qed

lemma seq_bound: "k \<le> length p - 1 \<Longrightarrow> Seq k t \<le> 1"
  using sk_bound Seq_def by blast

lemma skzl_bitAND_to_mult:
  assumes "k \<le> length p - 1"
  assumes "l < n"
  shows "nth_digit (z l) t b && nth_digit (s k) t b = (Zeq l t) * Seq k t"
proof -
  have "nth_digit (z l) t b && nth_digit (s k) t b = (Zeq l t) && Seq k t"
    using Zeq_def Seq_def by simp
  also have "... = (Zeq l t) * Seq k t"
    using bitAND_single_bit_mult_equiv[of "(Zeq l t)" "Seq k t"] seq_bound Z assms by auto
  finally show ?thesis by auto
qed

lemma skzl_bitAND_to_mult2:
  assumes "k \<le> length p - 1"
  assumes "\<forall>k \<le> length p - 1. l k < n"
  shows "(1 - nth_digit (z (l k)) t b) && nth_digit (s k) t b
       = (1 - Zeq (l k) t) * Seq k t"
proof -
  have "(1 - nth_digit (z (l k)) t b) && nth_digit (s k) t b
       = (1 - Zeq (l k) t) && Seq k t"
    using Zeq_def Seq_def by simp
  also have "... = (1 - Zeq (l k) t) * Seq k t"
    using bitAND_single_bit_mult_equiv[of "(1 - Zeq (l k) t)" "Seq k t"] seq_bound Z assms by auto
  finally show ?thesis by auto
qed

lemma state_equations_digit_commute: 
 assumes "t < q" and "j \<le> m"
 defines "l \<equiv> \<lambda>k. modifies (p!k)"
 shows "nth_digit (s j) (Suc t) b =
            (\<Sum>S+ p j (\<lambda>k. Seq k t))
          + (\<Sum>S- p j (\<lambda>k. Zeq (l k) t * Seq k t))
          + (\<Sum>S0 p j (\<lambda>k. (1 - Zeq (l k) t) * Seq k t))"
proof - 
  define o' :: nat where "o' \<equiv> if j = 0 then 1 else 0"
  have o'_div: "o' div b = 0" using b_gt1 by (auto simp: o'_def)

  have l: "\<forall>k\<le>length p - 1. (l k) < n"
    using l_def by (auto simp: m_def modifies_valid)

  have "\<forall>k. Suc 0 < 2^c" using c_gt0 h0 by auto
  hence e_aux: "\<forall>tt. nth_digit e tt b = (if tt\<le>q then Suc 0 else 0)"
    using e_def b_def c_gt0 nth_digit_gen_power_series[of "\<lambda>k. Suc 0" "c" "q"] by auto
  have zl_bounded: "k\<le>m \<Longrightarrow> \<forall>t'. nth_digit (z (l k)) t' b \<le> nth_digit e t' b" for k
  proof -
    assume "k\<le>m"
    from m_eq have "\<forall>l<n. z l \<preceq> e" using mask_equations_def by auto
    then have "\<forall>l<n. \<forall>t'. (z l) \<exclamdown> t' \<le> e \<exclamdown> t'" using masks_leq_equiv by auto
    then have k_lt_c: "\<forall>l<n. \<forall>t'. \<forall>k'<Suc c. nth_digit (z l) t' b \<exclamdown> k' 
                                   \<le> nth_digit e t' b \<exclamdown> k'"
      using digit_gen_pow2_reduct by (auto simp: b_def) (metis power_Suc)

    have "k\<ge>Suc c \<Longrightarrow> x mod (2 ^ Suc c) div 2 ^ k = 0" for k x::nat
      by (simp only: drop_bit_take_bit flip: take_bit_eq_mod drop_bit_eq_div) simp
    then have "\<forall>k\<ge>Suc c. nth_digit x y b \<exclamdown> k = 0" for x y
      using b_def nth_bit_def nth_digit_def by auto
    then have k_gt_c: "\<forall>l<n. \<forall>t'. \<forall>k'\<ge>Suc c. nth_digit (z l) t' b \<exclamdown> k' 
                                           \<le> nth_digit e t' b \<exclamdown> k'"
      by auto
    from k_lt_c k_gt_c have "\<forall>l<n. \<forall>t'. nth_digit (z l) t' b \<le> nth_digit e t' b"
      using bitwise_leq by (meson not_le)
    thus ?thesis by (auto simp: modifies_valid l_def `k\<le>m`)
  qed

  have "\<forall>t k. k\<le>m \<longrightarrow> nth_digit (e - z (l k)) t b =
                   nth_digit e t b - nth_digit (z (l k)) t b"
    using zl_bounded block_subtractivity by (auto simp: c_gt0 b_def l_def)
  then have sum_szero_aux:
    "\<forall>t k. t<q \<longrightarrow> k\<le>m \<longrightarrow> nth_digit (e - z (l k)) t b = 1-nth_digit (z (l k)) t b"
    using e_aux by auto

  have skzl_bound2: "\<forall>k\<le>length p - 1. (l k) < n \<Longrightarrow>
                      \<forall>t. \<forall>k\<le>length p - 1. nth_digit (s k && (e - z (l k))) t b < 2^c"
  proof - 
    assume l: "\<forall>k\<le>length p - 1. (l k) < n"
    have "\<forall>t. \<forall>k\<le>length p - 1. nth_digit (s k && (e - z (l k))) t b
          = nth_digit (s k) t b && nth_digit (e - z (l k)) t b"
      using bitAND_nth_digit_commute Zeq_def b_def by auto
  
    moreover have "\<forall>t<q. \<forall>k\<le>length p - 1. 
                    nth_digit (s k) t b && nth_digit (e - z (l k)) t b
                  = nth_digit (s k) t b && (1 - nth_digit (z (l k)) t b)"
      using sum_szero_aux by (simp add: m_def)

    moreover have "\<forall>t. \<forall>k\<le>length p - 1. 
                     nth_digit (s k) t b && (1 - nth_digit (z (l k)) t b)
                   \<le> nth_digit (s k) t b"
      using Z l using lm0245 masks_leq by (simp add: lm0244)
  
    moreover have "\<forall>t. \<forall>k\<le>length p - 1. nth_digit (s k) t b < 2^c"
      using sk_bound h0 by (meson le_less_trans)
  
    ultimately show ?thesis
      using le_less_trans by (metis lm0244 masks_leq)
  qed

    (* START *)
    have "s j = o' + b*\<Sum>S+ p j (\<lambda>k. s k) + b*\<Sum>S- p j (\<lambda>k. s k && z (modifies (p!k)))
                   + b*\<Sum>S0 p j (\<lambda>k. s k && (e - z (modifies (p!k))))"
      using s_eq state_equations_def \<open>j\<le>m\<close> by (auto simp: o'_def)
    then have "s j div b^Suc t mod b =
                 ( o' + b*\<Sum>S+ p j (\<lambda>k. s k)
                      + b*\<Sum>S- p j (\<lambda>k. s k && z (modifies (p!k)))
                      + b*\<Sum>S0 p j (\<lambda>k. s k && (e - z (modifies (p!k)))) ) div b div b^t mod b"
      by (auto simp: algebra_simps div_mult2_eq)
    also have "... =   (\<Sum>S+ p j (\<lambda>k. s k)
                      + \<Sum>S- p j (\<lambda>k. s k && z (modifies (p!k)))
                      + \<Sum>S0 p j (\<lambda>k. s k && (e - z (modifies (p!k)))) ) div b^t mod b"
      using o'_div
      by (auto simp: algebra_simps div_mult2_eq)
         (smt Nat.add_0_right add_mult_distrib2 b_gt1 div_mult_self2 gr_implies_not0)
    (* Interchanged order in the following with add.commute to ease next step *)
    also have "... = nth_digit (\<Sum>S- p j (\<lambda>k. s k && z (l k))
                      + \<Sum>S+ p j (\<lambda>k. s k)
                      + \<Sum>S0 p j (\<lambda>k. s k && (e - z (l k)))) t b"
      by (auto simp: nth_digit_def l_def add.commute)

    (* STEP 2: Commute nth_digit to the inside of all expressions. *)
    also have "... = nth_digit (\<Sum>S- p j (\<lambda>k. s k && z (l k))) t b
                      + nth_digit (\<Sum>S+ p j (\<lambda>k. s k)
                                         + \<Sum>S0 p j (\<lambda>k. s k && (e - z (l k)))) t b"
      using block_additivity sum_ssub_fst_digit_zero sum_state_special_fst_digit_zero
      by (auto simp: l_def c_gt0 b_def add.assoc) 
    also have "... = nth_digit (\<Sum>S+ p j (\<lambda>k. s k)) t b
                      + nth_digit (\<Sum>S- p j (\<lambda>k. s k && z (l k))) t b
                      + nth_digit (\<Sum>S0 p j (\<lambda>k. s k && (e - z (l k)))) t b"
      using block_additivity sum_sadd_fst_digit_zero sum_szero_fst_digit_zero
      by (auto simp: l_def c_gt0 b_def)
    also have "... = nth_digit (\<Sum>S+ p j (\<lambda>k. s k)) t b
                      + (\<Sum>S- p j (\<lambda>k. nth_digit (s k && z (l k)) t b))
                      + nth_digit (\<Sum>S0 p j (\<lambda>k. s k && (e - z (l k)))) t b"
      using sum_ssub_nth_digit_commute by auto
    also have "... = nth_digit (\<Sum>S+ p j (\<lambda>k. s k)) t b
                      + \<Sum>S- p j (\<lambda>k. nth_digit (s k && z (l k)) t b)
                      + \<Sum>S0 p j (\<lambda>k. nth_digit (s k && (e - z (l k))) t b)"
      using l_def l skzl_bound2 sum_szero_nth_digit_commute by (auto)
    also have "... = \<Sum>S+ p j (\<lambda>k. nth_digit (s k) t b)
                      + \<Sum>S- p j (\<lambda>k. nth_digit (s k && z (l k)) t b)
                      + \<Sum>S0 p j (\<lambda>k. nth_digit (s k && (e - z (l k))) t b)"
      using sum_sadd_nth_digit_commute by auto
    also have "... = \<Sum>S+ p j (\<lambda>k. nth_digit (s k) t b)
                      + \<Sum>S- p j (\<lambda>k. nth_digit (z (l k)) t b && nth_digit (s k) t b)
                      + \<Sum>S0 p j (\<lambda>k. (nth_digit (e - z (l k)) t b) && nth_digit (s k) t b)"
      using bitAND_nth_digit_commute b_def by (auto simp: bitAND_commutes)
    also have "... = (\<Sum>S+ p j (\<lambda>k. nth_digit (s k) t b))
          + (\<Sum>S- p j (\<lambda>k. nth_digit (z (l k)) t b && nth_digit (s k) t b))
          + (\<Sum>S0 p j (\<lambda>k. (1 - nth_digit (z (l k)) t b) && nth_digit (s k) t b))"
      using sum_szero_aux assms sum_ssub_zero.simps m_def \<open>t<q\<close>
      apply (auto) using sum.cong atLeastAtMost_iff by smt 
      (* this ATP proof ensures that the \<Sum>S0 only uses the sum_szero_aux lemma with k \<le> m
         because the summation of sum_ssub_zero ranges from k = 0 .. (length p - 1) *)
    ultimately have "s j div (b ^ Suc t) mod b =
            (\<Sum>S+ p j (\<lambda>k. nth_digit (s k) t b))
          + (\<Sum>S- p j (\<lambda>k. nth_digit (z (l k)) t b && nth_digit (s k) t b))
          + (\<Sum>S0 p j (\<lambda>k. (1 - nth_digit (z (l k)) t b) && nth_digit (s k) t b))"
      by auto

    moreover have "(\<Sum>S- p j (\<lambda>k. nth_digit (z (l k)) t b && nth_digit (s k) t b))
                   = (\<Sum>S- p j (\<lambda>k. Zeq (l k) t * Seq k t))"
      using skzl_bitAND_to_mult sum_ssub_nzero.simps l
      by (smt atLeastAtMost_iff sum.cong)

    moreover have "(\<Sum>S0 p j (\<lambda>k. (1 - nth_digit (z (l k)) t b) && nth_digit (s k) t b))
                   = (\<Sum>S0 p j (\<lambda>k. (1 - Zeq (l k) t) * Seq k t))"
      using skzl_bitAND_to_mult2 sum_ssub_zero.simps l
      by (auto) (smt atLeastAtMost_iff sum.cong)

    ultimately have "nth_digit (s j) (Suc t) b =
            (\<Sum>S+ p j (\<lambda>k. Seq k t))
          + (\<Sum>S- p j (\<lambda>k. Zeq (l k) t * Seq k t))
          + (\<Sum>S0 p j (\<lambda>k. (1 - Zeq (l k) t) * Seq k t))"
      using Seq_def nth_digit_def by auto
  
    thus ?thesis by auto
qed

lemma aux_nocarry_sk: 
  assumes "t\<le>q"
  shows "i \<noteq> j \<longrightarrow> i\<le>m \<longrightarrow> j\<le>m \<longrightarrow> nth_digit (s i) t b * nth_digit (s j) t b = 0"
proof (cases "t=q")
  case True
  have "j < m \<longrightarrow> Seq j q = 0" for j using s_bound Seq_def nth_digit_def by auto
  then show ?thesis using True Seq_def apply auto by (metis le_less less_nat_zero_code)
next
  case False
  hence "k\<le>m \<and> nth_digit (s k) t b = 1 \<longrightarrow>
                          (\<forall>j\<le>m. j \<noteq> k \<longrightarrow> nth_digit (s j) t b = 0)" for k
    using states_unique_RAW[of "t"] Seq_def assms by auto
  thus ?thesis
    by (auto) (metis One_nat_def le_neq_implies_less m_def not_less_eq sk_bound)
qed

lemma nocarry_sk: 
  assumes "i \<noteq> j" and "i\<le>m" and "j\<le>m"
  shows "(s i) \<exclamdown> k * (s j) \<exclamdown> k = 0" 
proof -
  have reduct: "(s i) \<exclamdown> k = nth_digit (s i) (k div Suc c) b \<exclamdown> (k mod Suc c)" for i
    using digit_gen_pow2_reduct[of "k mod Suc c" "Suc c" "s i" "k div Suc c"] b_def
    using mod_less_divisor zero_less_Suc by presburger
  have "k div Suc c \<le> q \<longrightarrow> 
        nth_digit (s i) (k div Suc c) b * nth_digit (s j) (k div Suc c) b = 0" 
    using aux_nocarry_sk assms by auto
  moreover have "k div Suc c > q \<longrightarrow> 
        nth_digit (s i) (k div Suc c) b * nth_digit (s j) (k div Suc c) b = 0" 
    using nth_digit_def s_bound apply auto 
    using b_gt1 div_greater_zero_iff leD le_less less_trans mod_less neq0_conv power_increasing_iff
    by (smt assms) 
  ultimately have "nth_digit (s i) (k div Suc c) b \<exclamdown> (k mod Suc c) 
      * nth_digit (s j) (k div Suc c) b \<exclamdown> (k mod Suc c) = 0" 
    using nth_bit_def by auto
  thus ?thesis using reduct[of "i"] reduct[of "j"] by auto
qed


lemma commute_sum_rsub_bitAND: "\<Sum>R- p l (\<lambda>k. s k && z l) = \<Sum>R- p l (\<lambda>k. s k) && z l"
proof -
  show ?thesis apply (auto simp: sum_rsub.simps)
    using m_def nocarry_sk aux_commute_bitAND_sum_if[of "m" 
        "s" "\<lambda>k. issub (p ! k) \<and> l = modifies (p ! k)" "z l"] 
    by (auto simp add: atMost_atLeast0)
qed

lemma sum_rsub_bound: "l<n \<Longrightarrow> \<Sum>R- p l (\<lambda>k. s k && z l) \<le> r l + \<Sum>R+ p l s"
proof -
  assume "l<n"
  have "\<Sum>R- p l (\<lambda>k. s k) && z l \<le> z l" by (auto simp: lm0245 masks_leq)
  also have "... \<le> r l" using zl_le_rl `l<n` by auto
  ultimately show ?thesis
    using commute_sum_rsub_bitAND by (simp add: trans_le_add1)
qed


text \<open>Obtaining single step register relations from multiple step register relations \<close>
lemma mult_to_single_reg: 
  "c>0 \<Longrightarrow> l<n \<Longrightarrow> Req l (Suc t) = Req l t + (\<Sum>R+ p l (\<lambda>k. Seq k t)) 
                         - (\<Sum>R- p l (\<lambda>k. (Zeq l t) * Seq k t))" for l t
proof -
  assume l: "l<n"
  assume c: "c > 0"

  have a_div: "a div b = 0" using c_eq rm_constants_def B_def by auto

  have subtract_bound: "\<forall>t'. nth_digit (\<Sum>R- p l (\<lambda>k. s k && z l)) t' b
                                   \<le> nth_digit (r l + \<Sum>R+ p l (\<lambda>k. s k)) t' b"
  proof -
    {
      fix t'
      have "nth_digit (z l) t' b \<le> nth_digit (r l) t' b"
        using Zeq_def Req_def Z l by auto
      then have "nth_digit (\<Sum>R- p l (\<lambda>k. s k)) t' b && nth_digit (z l) t' b
                 \<le> nth_digit (r l) t' b"
        using sum_rsub_special_block_bound
        by (meson dual_order.trans lm0245 masks_leq)
      then have "nth_digit (\<Sum>R- p l (\<lambda>k. s k && z l)) t' b
                 \<le> nth_digit (r l) t' b"
        using commute_sum_rsub_bitAND bitAND_nth_digit_commute b_def by auto
      then have "nth_digit (\<Sum>R- p l (\<lambda>k. s k && z l)) t' b
                 \<le> nth_digit (r l) t' b + nth_digit (\<Sum>R+ p l (\<lambda>k. s k)) t' b"
        by auto
      then have "nth_digit (\<Sum>R- p l (\<lambda>k. s k && z l)) t' b
                 \<le> nth_digit (r l + \<Sum>R+ p l (\<lambda>k. s k)) t' b"
        using block_additivity rl_fst_digit_zero sum_radd_fst_digit_zero
        by (auto simp: b_def c l)
    }
    then show ?thesis by auto
  qed

  define a' where "a' \<equiv> (if l = 0 then a else 0)"
  have a'_div: "a' div b = 0" using a_div a'_def by auto

  (* START PROOF CHAIN *)
  (* STEP 1: Remove a' using divisibility properties. *)
  have "r l div (b * b ^ t) mod b =
         (a' + b*r l + b*\<Sum>R+ p l (\<lambda>k. s k) - b*\<Sum>R- p l (\<lambda>k. s k && z l)) div (b * b ^ t) mod b"
    using r_eq reg_equations_def by (auto simp: a'_def l)
  also have "... =
         (a' + b * (r l + \<Sum>R+ p l (\<lambda>k. s k) - \<Sum>R- p l (\<lambda>k. s k && z l))) div b div b^t mod b"
    by (auto simp: algebra_simps div_mult2_eq)
       (metis Nat.add_diff_assoc add_mult_distrib2 mult_le_mono2 sum_rsub_bound l)
  also have "... =
         ((r l + \<Sum>R+ p l (\<lambda>k. s k) - \<Sum>R- p l (\<lambda>k. s k && z l)) + a' div b) div b ^ t mod b"
    using b_gt1 by auto
  also have "... = (r l + \<Sum>R+ p l (\<lambda>k. s k) - \<Sum>R- p l (\<lambda>k. s k && z l)) div b ^ t mod b"
    using a'_div by auto
  also have "... = nth_digit (r l + \<Sum>R+ p l (\<lambda>k. s k) - \<Sum>R- p l (\<lambda>k. s k && z l)) t b"
    using nth_digit_def by auto
  
  (* STEP 2: Commute nth_digit to the inside of all expressions. *)
  also have "... = nth_digit (r l + \<Sum>R+ p l (\<lambda>k. s k)) t b
                   - nth_digit (\<Sum>R- p l (\<lambda>k. s k && z l)) t b"
    using block_subtractivity subtract_bound
    by (auto simp: c b_def)
  also have "... = nth_digit (r l) t b 
                   + nth_digit (\<Sum>R+ p l (\<lambda>k. s k)) t b
                   - nth_digit (\<Sum>R- p l (\<lambda>k. s k && z l)) t b"
    using block_additivity rl_fst_digit_zero sum_radd_fst_digit_zero
    by (auto simp: l b_def c)
  also have "... = nth_digit (r l) t b
                   + \<Sum>R+ p l (\<lambda>k. nth_digit (s k) t b)
                   - \<Sum>R- p l (\<lambda>k. nth_digit (s k && z l) t b)"
    using sum_radd_nth_digit_commute
    using sum_rsub_nth_digit_commute
    by auto
  ultimately have "r l div (b * b ^ t) mod b =
                     (nth_digit (r l) t b)
                     + \<Sum>R+ p l (\<lambda>k. nth_digit (s k) t b)
                     - \<Sum>R- p l (\<lambda>k. nth_digit (z l) t b && nth_digit (s k) t b)"
    using bitAND_nth_digit_commute b_def by (simp add: bitAND_commutes)

  then show ?thesis using Req_def Seq_def nth_digit_def skzl_bitAND_to_mult l
    by (auto simp: sum_rsub.simps) (smt atLeastAtMost_iff sum.cong)
qed

text \<open>Obtaining single step state relations from multiple step state relations\<close>
lemma mult_to_single_state:
  fixes t j :: nat
  defines "l \<equiv> \<lambda>k. modifies (p!k)"
  shows "j\<le>m \<Longrightarrow> t<q \<Longrightarrow> Seq j (Suc t) = (\<Sum>S+ p j (\<lambda>k. Seq k t))
       + (\<Sum>S- p j (\<lambda>k. Zeq (l k) t * Seq k t))
       + (\<Sum>S0 p j (\<lambda>k. (1 - Zeq (l k) t) * Seq k t))"
proof -
  assume "j \<le> m"
  assume "t < q"

  have "nth_digit (s j) (Suc t) b =
            (\<Sum>S+ p j (\<lambda>k. Seq k t))
          + (\<Sum>S- p j (\<lambda>k. Zeq (l k) t * Seq k t))
          + (\<Sum>S0 p j (\<lambda>k. (1 - Zeq (l k) t) * Seq k t))" 
    using state_equations_digit_commute \<open>j\<le>m\<close> \<open>t<q\<close> l_def by auto

  then show ?thesis using nth_digit_def l_def Seq_def by auto
qed

text \<open>Conclusion: 
   The central equivalence showing that the cell entries obtained from r s z indeed coincide with
   the correct cell values when executing the register machine. This statement is proven by 
   induction using the single step relations for Req and Seq as well as the statement for Zeq. \<close>

lemma rzs_eq:
  "l<n \<Longrightarrow> j\<le>m \<Longrightarrow> t\<le>q \<Longrightarrow> R ic p l t = Req l t \<and> Z ic p l t = Zeq l t \<and> S ic p j t = Seq j t"
proof (induction t arbitrary: j l)
  have "m>0" using m_def is_val is_valid_initial_def[of "ic" "p"] is_valid_def[of "ic" "p"] by auto

  case 0
  (* STATES *)
  have mod_aux0: "Suc (b * k) mod b = 1" for k 
    using euclidean_semiring_cancel_class.mod_mult_self2[of "1" "b" "k"] b_gt1 by auto
  have step_state0: "s 0 = 1 + b*\<Sum>S+ p 0 (\<lambda>k. s k) + b*\<Sum>S- p 0 (\<lambda>k. s k && z (modifies (p!k)))
           + b*\<Sum>S0 p 0 (\<lambda>k. s k && (e - z (modifies (p!k))))" 
    using s_eq state_equations_def by auto
  hence "Seq 0 0 = 1" using Seq_def by (auto simp: nth_digit_def mod_aux0)
  hence S00: "Seq 0 0 = S ic p 0 0" using S_def is_val is_valid_initial_def[of "ic"] by auto

  have "s m = b^q" using s_eq state_equations_def by auto
  hence "Seq m 0 = 0" using Seq_def nth_digit_def c_eq rm_constants_def by auto
  hence Sm0: "S ic p m 0 = Seq m 0"
    using is_val is_valid_initial_def[of "ic" "p" "a"] S_def `m>0` by auto

  have step_states: "\<forall>d>0. d<m \<longrightarrow> s d = b*\<Sum>S+ p d (\<lambda>k. s k) 
                                       + b*\<Sum>S- p d (\<lambda>k. s k && z (modifies (p!k)))
                                       + b*\<Sum>S0 p d (\<lambda>k. s k && (e - z (modifies (p!k))))" 
    using s_eq state_equations_def by auto
  hence "\<forall>k>0. k<m \<longrightarrow> Seq k 0 = 0" using Seq_def by (auto simp: nth_digit_def)
  hence "k>0 \<longrightarrow> k<m \<longrightarrow> Seq k 0 = S ic p k 0" for k 
    using S_def is_val is_valid_initial_def[of "ic"] by auto

  with S00 Sm0 have Sid: "k\<le>m \<longrightarrow> Seq k 0 = S ic p k 0" for k 
    by (cases "k=0"; cases "k=m"; auto)

  (* REGISTERS *)
  have "b * (r 0 + \<Sum>R+ p 0 s - \<Sum>R- p 0 (\<lambda>k. s k && z 0)) 
        = b * (r 0 + \<Sum>R+ p 0 s) - b * \<Sum>R- p 0 (\<lambda>k. s k && z 0)"
    using Nat.diff_mult_distrib2[of "b" "r 0 + \<Sum>R+ p 0 s" "\<Sum>R- p 0 (\<lambda>k. s k && z 0)"] by auto
  also have "... = b * r 0 + b* \<Sum>R+ p 0 s - b * \<Sum>R- p 0 (\<lambda>k. s k && z 0)"
    using Nat.add_mult_distrib2[of "b" "r 0" "\<Sum>R+ p 0 s"] by auto
  ultimately have distrib: "a + b * (r 0 + \<Sum>R+ p 0 s - \<Sum>R- p 0 (\<lambda>k. s k && z 0))
                       = a + b * r 0 + b * \<Sum>R+ p 0 s - b * \<Sum>R- p 0 (\<lambda>k. s k && z 0)"
    by (auto simp: algebra_simps)
       (metis Nat.add_diff_assoc add_mult_distrib2 mult_le_mono2 n_gt0 sum_rsub_bound)

  hence "Req 0 0 = (a + b * r 0 + b * \<Sum>R+ p 0 s - b * \<Sum>R- p 0 (\<lambda>k. s k && z 0)) mod b"
    using Req_def nth_digit_def r_eq reg_equations_def by auto
  also have "... = (a + b * (r 0 + \<Sum>R+ p 0 s - \<Sum>R- p 0 (\<lambda>k. s k && z 0))) mod b"
    using distrib by auto
  finally have "Req 0 0 = a" using c_eq rm_constants_def B_def by auto
  hence R00: "R ic p 0 0 = Req 0 0" 
    using R_def is_val is_valid_initial_def[of "ic" "p" "a"] by auto

  have rl_transform: "l>0 \<longrightarrow> r l = b * r l + b * \<Sum>R+ p l s - b * \<Sum>R- p l (\<lambda>k. s k && z l)" 
    using reg_equations_def r_eq `l<n` by auto

  have "l>0 \<longrightarrow> (b * r l + b * \<Sum>R+ p l s - b * \<Sum>R- p l (\<lambda>k. s k && z l)) mod b = 0"
    using Req_def nth_digit_def reg_equations_def r_eq by auto
  hence "l>0 \<longrightarrow> Req l 0 = 0" 
    using Req_def rl_transform nth_digit_def by auto
  hence "l>0 \<Longrightarrow> Req l 0 = R ic p l 0" using is_val is_valid_initial_def[of "ic"] R_def by auto
  hence Rid: "R ic p l 0 = Req l 0" using R00 by (cases "l=0"; auto)

  (* ZERO INDICATORS *)
  hence Zid: "Z ic p l 0 = Zeq l 0" using Z Z_def 0 by auto

  show ?case using Sid Rid Zid `l<n` `j\<le>m` by auto
next
  case (Suc t)

  (* INDUCTIVE HYPOTHESIS *)
  have "Suc t\<le>q" using Suc by auto
  then have "t<q" by auto

  have S_IH: "k\<le>m \<Longrightarrow> S ic p k t = Seq k t" for k using Suc m_def by auto
  have Z_IH: "\<forall>l::nat. l<n \<longrightarrow> Z ic p l t = Zeq l t" using Suc by auto
  
  (* REGISTERS *)
  from S_IH have S1: "k\<le>m \<Longrightarrow>
          (if isadd (p ! k) \<and> l = modifies (p ! k) then Seq k t else 0)
        = (if isadd (p ! k) \<and> l = modifies (p ! k) then S ic p k t else 0)" for k
    by auto
  have S2: "k \<in> {0..length p-1} \<Longrightarrow>
        (if issub (p ! k) \<and> l = modifies (p ! k) then Zeq l t * Seq k t else 0)
      = (if issub (p ! k) \<and> l = modifies (p ! k) then Zeq l t * S ic p k t else 0)" for k 
    using Suc m_def by auto

  have "Req l (Suc t) = Req l t + (\<Sum>R+ p l (\<lambda>k. Seq k t)) - (\<Sum>R- p l (\<lambda>k. (Zeq l t) * Seq k t))" 
    using mult_to_single_reg[of "l"] `l<n` by (auto simp: c_gt0)
  also have "... = R ic p l t + (\<Sum>R+ p l (\<lambda>k. S ic p k t))
                             - (\<Sum>R- p l (\<lambda>k. (Z ic p l t) * S ic p k t))"
    using Suc sum_radd.simps sum_rsub.simps S1 S2 m_def by auto
  finally have R: "Req l (Suc t) = R ic p l (Suc t)"
    using is_val `l<n` n_def lm04_06_one_step_relation_register[of "ic" "p" "a" "l"] by auto
  
  (* ZERO INDICATRORS *)
  hence Z_suct: "Zeq l (Suc t) = Z ic p l (Suc t)" using Z Z_def `l<n` by auto

  have plength: "length p \<le> Suc m" by (simp add: m_def)

  (* STATES *)
  have "s m = b ^ q" using s_eq state_equations_def by auto
  hence "Seq m t = 0" using Seq_def \<open>t<q\<close> nth_digit_def apply auto
    using b_gt1 bx_aux by auto
  hence "S ic p m t = 0" using Suc by auto
  hence "fst (steps ic p t) \<noteq> m" using S_def by auto
  hence "fst (steps ic p t) < m" using is_val m_def 
    by (metis less_Suc_eq less_le_trans p_contains plength) 
  hence nohalt: "\<not> ishalt (p ! fst (steps ic p t))" using is_valid_def[of "ic" "p"]
      is_valid_initial_def[of "ic" "p" "a"] m_def is_val by auto

  have "j<length p" using `j\<le>m` m_def
    by (metis (full_types) diff_less is_val length_greater_0_conv less_imp_diff_less less_one 
        list.size(3) nat_less_le not_less not_less_zero p_contains)
  have "Seq j (Suc t) = (\<Sum>S+ p j (\<lambda>k. Seq k t))
                 + (\<Sum>S- p j (\<lambda>k. Zeq (modifies (p!k)) t * Seq k t))
                 + (\<Sum>S0 p j (\<lambda>k. (1 - Zeq (modifies (p!k)) t) * Seq k t))" 
    using mult_to_single_state `j\<le>m` `t<q` c_gt0 by auto
  also have "... = (\<Sum>S+ p j (\<lambda>k. Seq k t))
                 + (\<Sum>S- p j (\<lambda>k. Z ic p (modifies (p!k)) t * Seq k t))
                 + (\<Sum>S0 p j (\<lambda>k. (1 - Z ic p (modifies (p!k)) t) * Seq k t))" 
    using Z_IH modifies_valid sum_ssub_zero.simps sum_ssub_nzero.simps
    by (auto simp: m_def, smt atLeastAtMost_iff sum.cong)
  also have "... = (\<Sum>S+ p j (\<lambda>k. S ic p k t))
                 + (\<Sum>S- p j (\<lambda>k. Z ic p (modifies (p!k)) t * S ic p k t))
                 + (\<Sum>S0 p j (\<lambda>k. (1 - Z ic p (modifies (p!k)) t) * S ic p k t))"
    using S_IH sum_ssub_zero.simps sum_ssub_nzero.simps sum_sadd.simps
    by (auto simp: m_def, smt atLeastAtMost_iff sum.cong)
  finally have S: "Seq j (Suc t) = S ic p j (Suc t)"
    using is_val lm04_07_one_step_relation_state[of "ic" "p" "a" "j"] `j<length p` nohalt by auto

  show ?case using R S Z_suct by auto
qed

end 

end