theory Mod_Plus_Minus

imports Kyber_spec

begin
section \<open>Re-centered Modulo Operation\<close>
text \<open>To define the compress and decompress functions, 
  we need some special form of modulo. It returns the 
  representation of the equivalence class in \<open>(-q div 2, q div 2]\<close>.
  Using these representatives, we ensure that the norm of the 
  representative is as small as possible.\<close>

definition mod_plus_minus :: "int \<Rightarrow> int \<Rightarrow> int" 
  (infixl "mod+-" 70) where
"m mod+- b = 
  (if m mod b > \<lfloor>b/2\<rfloor> then m mod b - b else m mod b)"

text \<open>Range of the (re-centered) modulo operation\<close>
 
lemma mod_range: "b>0 \<Longrightarrow> (a::int) mod (b::int) \<in> {0..b-1}"
using range_mod by auto

lemma mod_rangeE: 
  assumes "(a::int)\<in>{0..<b}"
  shows "a = a mod b"
using assms by auto


lemma half_mod_odd:
assumes "b>0" "odd b" "\<lfloor>real_of_int b / 2\<rfloor> < y mod b" 
shows "- \<lfloor>real_of_int b / 2\<rfloor> \<le> y mod b - b" "y mod b - b \<le> \<lfloor>real_of_int b / 2\<rfloor>"
proof -
  have "\<lfloor>real_of_int b / 2\<rfloor> = (b-1) div 2" using \<open>odd b\<close>
    by (metis add.commute diff_add_cancel even_add even_succ_div_2 floor_divide_of_int_eq 
    odd_one of_int_numeral)
  then show "- \<lfloor>real_of_int b / 2\<rfloor> \<le> y mod b - b" using assms by linarith
  have "y mod b \<le> b + \<lfloor>real_of_int b / 2\<rfloor>" using mod_range[OF assms(1)] 
  by (smt (verit, ccfv_SIG) \<open>\<lfloor>real_of_int b / 2\<rfloor> = (b - 1) div 2\<close> atLeastAtMost_iff 
    pos_imp_zdiv_neg_iff)
  then show "y mod b - b \<le> \<lfloor>real_of_int b / 2\<rfloor>" by auto
qed

lemma half_mod:
assumes "b>0"
shows "- \<lfloor>real_of_int b / 2\<rfloor> \<le> y mod b"
using assms
by (smt (verit, best) floor_less_zero half_gt_zero mod_int_pos_iff of_int_pos)

lemma mod_plus_minus_range_odd: 
  assumes "b>0" "odd b"
  shows "y mod+- b \<in> {-\<lfloor>b/2\<rfloor>..\<lfloor>b/2\<rfloor>}"
unfolding mod_plus_minus_def by (auto simp add: half_mod_odd[OF assms] half_mod[OF assms(1)])

lemma odd_smaller_b:
  assumes "odd b" 
  shows "\<lfloor> real_of_int b / 2 \<rfloor> + \<lfloor> real_of_int b / 2 \<rfloor> < b"
using assms 
by (smt (z3) floor_divide_of_int_eq odd_two_times_div_two_succ 
  of_int_hom.hom_add of_int_hom.hom_one)
 

lemma mod_plus_minus_rangeE_neg:
  assumes "y \<in> {-\<lfloor>real_of_int b/2\<rfloor>..\<lfloor>real_of_int b/2\<rfloor>}"
          "odd b" "b > 0"
           "\<lfloor>real_of_int b / 2\<rfloor> < y mod b"
  shows "y = y mod b - b"
proof -
  have "y \<in> {-\<lfloor>real_of_int b/2\<rfloor>..<0}" using assms
  by (meson atLeastAtMost_iff atLeastLessThan_iff linorder_not_le order_trans zmod_le_nonneg_dividend)
  then have "y \<in> {-b..<0}" using assms(2-3)
  by (metis atLeastLessThan_iff floor_divide_of_int_eq int_div_less_self linorder_linear 
    linorder_not_le neg_le_iff_le numeral_code(1) numeral_le_iff of_int_numeral order_trans 
    semiring_norm(69))
  then have "y mod b = y + b" 
  by (smt (verit) atLeastLessThan_iff mod_add_self2 mod_pos_pos_trivial)
  then show ?thesis by auto
qed

lemma mod_plus_minus_rangeE_pos:
  assumes "y \<in> {-\<lfloor>real_of_int b/2\<rfloor>..\<lfloor>real_of_int b/2\<rfloor>}"
          "odd b" "b > 0"
          "\<lfloor>real_of_int b / 2\<rfloor> \<ge> y mod b"
  shows "y = y mod b"
proof -
  have "y \<in> {0..\<lfloor>real_of_int b/2\<rfloor>}" 
  proof (rule ccontr)
    assume "y \<notin> {0..\<lfloor>real_of_int b / 2\<rfloor>} "
    then have "y \<in> {-\<lfloor>real_of_int b/2\<rfloor>..<0}" using assms(1) by auto
    then have "y \<in> {-b..<0}" using assms(2-3)
    by (metis atLeastLessThan_iff floor_divide_of_int_eq int_div_less_self linorder_linear 
      linorder_not_le neg_le_iff_le numeral_code(1) numeral_le_iff of_int_numeral order_trans 
      semiring_norm(69))
    then have "y mod b = y + b" 
      by (smt (verit) atLeastLessThan_iff mod_add_self2 mod_pos_pos_trivial)
    then have "y mod b \<ge> b - \<lfloor>real_of_int b/2\<rfloor>" using assms(1) by auto
    then have "y mod b > \<lfloor>real_of_int b/2\<rfloor>"
      using assms(2) odd_smaller_b by fastforce
    then show False using assms(4) by auto
  qed
  then have "y \<in> {0..<b}" using assms(2-3)
  by (metis atLeastAtMost_iff atLeastLessThan_empty atLeastLessThan_iff floor_divide_of_int_eq 
    int_div_less_self linorder_not_le numeral_One numeral_less_iff of_int_numeral semiring_norm(76))
  then show ?thesis by auto
qed

lemma mod_plus_minus_rangeE:
  assumes "y \<in> {-\<lfloor>real_of_int b/2\<rfloor>..\<lfloor>real_of_int b/2\<rfloor>}"
          "odd b" "b > 0"
  shows "y = y mod+- b"
unfolding mod_plus_minus_def 
using mod_plus_minus_rangeE_pos[OF assms] mod_plus_minus_rangeE_neg[OF assms]
by auto

text \<open>Image of $0$.\<close>

lemma mod_plus_minus_zero:
  assumes "x mod+- b = 0"
  shows "x mod b = 0"
using assms unfolding mod_plus_minus_def 
by (metis eq_iff_diff_eq_0 mod_mod_trivial mod_self)

lemma mod_plus_minus_zero':
  assumes "b>0" "odd b"
  shows "0 mod+- b = (0::int)" 
using assms(1) mod_plus_minus_def by force

text \<open>\<open>mod+-\<close> with negative values.\<close>

lemma neg_mod_plus_minus:
  assumes "odd b"
          "b>0"
  shows "(- x) mod+- b = - (x mod+- b)"
proof -
  obtain k :: int where k_def: "(-x) mod+- b = (-x)+ k* b" 
  using mod_plus_minus_def
  proof -
    assume a1: "\<And>k. - x mod+- b = - x + k * b \<Longrightarrow> thesis"
    have "\<exists>i. i mod b + - (x + i) = - x mod+- b" 
    by (smt (verit, del_insts) mod_add_self1 mod_plus_minus_def)
    then show ?thesis
      using a1 by (metis (no_types) diff_add_cancel diff_diff_add 
      diff_minus_eq_add minus_diff_eq minus_mult_div_eq_mod 
      mult.commute mult_minus_left)
  qed
  then have "(-x) mod+- b = -(x - k*b)" using k_def by auto
  also have "\<dots> = - ((x-k*b) mod+- b)"
  proof -
    have range_xkb:"x - k * b \<in> 
      {- \<lfloor>real_of_int b / 2\<rfloor>..\<lfloor>real_of_int b / 2\<rfloor>}"
      using k_def mod_plus_minus_range_odd[OF assms(2) assms(1)]
      by (smt (verit, ccfv_SIG) atLeastAtMost_iff)
    have "x - k*b = (x - k*b) mod+- b" 
      using mod_plus_minus_rangeE[OF range_xkb assms] by auto
    then show ?thesis by auto
  qed
  also have "-((x - k*b) mod+- b) = -(x mod+- b)" 
    unfolding mod_plus_minus_def 
    by (smt (verit, best) mod_mult_self1)
  finally show ?thesis by auto
qed

text \<open>Representative with \<open>mod+-\<close>\<close>

lemma mod_plus_minus_rep_ex:
"\<exists>k. x = k*b + x mod+- b"
unfolding mod_plus_minus_def 
by (split if_splits)(metis add.right_neutral add_diff_eq div_mod_decomp_int 
  eq_iff_diff_eq_0 mod_add_self2)


lemma mod_plus_minus_rep: 
  obtains k where "x = k*b + x mod+- b"
using mod_plus_minus_rep_ex by auto

text \<open>Multiplication in \<open>mod+-\<close>\<close>

lemma mod_plus_minus_mult: 
  "s*x mod+- q = (s mod+- q) * (x mod+- q) mod+- q"
unfolding mod_plus_minus_def 
by (smt (verit, ccfv_threshold) minus_mod_self2 mod_mult_left_eq mod_mult_right_eq)
end