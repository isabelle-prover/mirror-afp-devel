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
  ((m + \<lfloor> real_of_int b / 2 \<rfloor>) mod b) - \<lfloor> real_of_int b / 2 \<rfloor>"
 
lemma mod_range: "b>0 \<Longrightarrow> (a::int) mod (b::int) \<in> {0..b-1}"
using range_mod by auto

lemma mod_rangeE: 
  assumes "(a::int)\<in>{0..<b}"
  shows "a = a mod b"
using assms by auto

lemma mod_plus_minus_range: 
  assumes "b>0"
  shows "y mod+- b \<in> {-\<lfloor>b/2\<rfloor>..\<lfloor>b/2\<rfloor>}"
unfolding mod_plus_minus_def 
using mod_range[OF assms, of "(y + \<lfloor>real_of_int b / 2\<rfloor>)"]
by (auto)(linarith)

lemma odd_smaller_b:
  assumes "odd b" 
  shows "\<lfloor> real_of_int b / 2 \<rfloor> + \<lfloor> real_of_int b / 2 \<rfloor> < b"
using assms 
by (smt (z3) floor_divide_of_int_eq odd_two_times_div_two_succ 
  of_int_hom.hom_add of_int_hom.hom_one)

lemma mod_plus_minus_rangeE:
  assumes "y \<in> {-\<lfloor>real_of_int b/2\<rfloor>..<\<lfloor>real_of_int b/2\<rfloor>}"
          "odd b"
  shows "y = y mod+- b"
proof -
  have "(y + \<lfloor> real_of_int b / 2 \<rfloor>) \<in> {0..<b}" 
    using assms(1) odd_smaller_b[OF assms(2)] by auto
  then have "(y + \<lfloor> real_of_int b / 2 \<rfloor>) mod b = 
    (y + \<lfloor> real_of_int b / 2 \<rfloor>)" 
    using mod_rangeE by auto
  then show ?thesis unfolding mod_plus_minus_def by auto
qed

lemma mod_plus_minus_rangeE':
  assumes "y \<in> {-\<lfloor>real_of_int b/2\<rfloor>..\<lfloor>real_of_int b/2\<rfloor>}"
          "odd b"
  shows "y = y mod+- b"
proof -
  have "(y + \<lfloor> real_of_int b / 2 \<rfloor>) \<in> {0..<b}" 
    using assms(1) odd_smaller_b[OF assms(2)] by auto
  then have "(y + \<lfloor> real_of_int b / 2 \<rfloor>) mod b = 
    (y + \<lfloor> real_of_int b / 2 \<rfloor>)" 
    using mod_rangeE by auto
  then show ?thesis unfolding mod_plus_minus_def by auto
qed

lemma mod_plus_minus_zero:
  assumes "x mod+- b = 0"
  shows "x mod b = 0"
using assms unfolding mod_plus_minus_def
by (metis add.commute add.right_neutral bits_mod_0 
  diff_add_cancel group_cancel.add1 mod_add_left_eq)

lemma mod_plus_minus_zero':
  assumes "b>0" "odd b"
  shows "0 mod+- b = (0::int)"
using mod_plus_minus_rangeE[of 0] 
by (smt (verit, best) assms(1) assms(2) atLeastAtMost_iff 
  atLeastLessThan_iff mod_plus_minus_range)


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
      by (metis (no_types) add.commute diff_add_cancel diff_minus_eq_add 
        floor_divide_of_int_eq mod_plus_minus_def of_int_numeral)
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
      using k_def mod_plus_minus_range[OF assms(2)]
      by (smt (verit, ccfv_SIG) atLeastAtMost_iff)
    have "x - k*b = (x - k*b) mod+- b" 
      using mod_plus_minus_rangeE'[OF range_xkb assms(1)] by auto
    then show ?thesis by auto
  qed
  also have "-((x - k*b) mod+- b) = -(x mod+- b)" 
    unfolding mod_plus_minus_def 
    by (smt (verit, best) mod_mult_self1)
  finally show ?thesis by auto
qed


lemma mod_plus_minus_rep: 
  obtains k where "x = k*b + x mod+- b"
unfolding mod_plus_minus_def 
by (metis add.commute add_diff_eq diff_eq_eq 
  minus_mult_div_eq_mod mult.commute)

end