section \<open>State Model with Fractional Permissions\<close>

text \<open>In this section, we define a concrete state model based on fractional permissions \<^cite>\<open>"Boyland03"\<close>.
A state is a pair of a permission mask and a partial heap.
A permission mask is a total map from heap locations to a rational between 0 and 1 (included),
while a partial heap is a partial map from heap locations to values.
We also define a partial addition on these states, and show that this state model corresponds to a separation algebra.\<close>

subsection \<open>Non-negative rationals (permission amounts)\<close>

theory PosRat
  imports Main HOL.Rat
begin



subsubsection Definitions

typedef prat = "{ r :: rat |r. r \<ge> 0}" by fastforce

setup_lifting type_definition_prat

lift_definition pwrite :: "prat" is "1" by simp
lift_definition pnone :: "prat" is "0" by simp
lift_definition half :: "prat" is "1 / 2" by fastforce

lift_definition pgte :: "prat \<Rightarrow> prat \<Rightarrow> bool" is "(\<ge>)" done
lift_definition pgt :: "prat \<Rightarrow> prat \<Rightarrow> bool" is "(>)" done
(* lift_definition lte :: "prat \<Rightarrow> prat \<Rightarrow> bool" is "(\<le>)" done *)
lift_definition lt :: "prat \<Rightarrow> prat \<Rightarrow> bool" is "(<)" done
lift_definition ppos :: "prat \<Rightarrow> bool" is "\<lambda>p. p > 0" done

lift_definition pmult :: "prat \<Rightarrow> prat \<Rightarrow> prat" is "(*)" by simp
lift_definition padd :: "prat \<Rightarrow> prat \<Rightarrow> prat" is "(+)" by simp

lift_definition pdiv :: "prat \<Rightarrow> prat \<Rightarrow> prat" is "(/)" by simp

lift_definition pmin :: "prat \<Rightarrow> prat \<Rightarrow> prat" is "(min)" by simp
lift_definition pmax :: "prat \<Rightarrow> prat \<Rightarrow> prat" is "(max)" by simp

subsubsection Lemmas

lemma pmin_comm:
  "pmin a b = pmin b a"
  by (metis Rep_prat_inverse min.commute pmin.rep_eq)

lemma pmin_greater:
  "pgte a (pmin a b)"
  by (simp add: pgte.rep_eq pmin.rep_eq)

lemma pmin_is:
  assumes "pgte a b"
  shows "pmin a b = b"
  by (metis Rep_prat_inject assms min_absorb2 pgte.rep_eq pmin.rep_eq)

lemma pmax_comm:
  "pmax a b = pmax b a"
  by (metis Rep_prat_inverse max.commute pmax.rep_eq)

lemma pmax_smaller:
  "pgte (pmax a b) a"
  by (simp add: pgte.rep_eq pmax.rep_eq)

lemma pmax_is:
  assumes "pgte a b"
  shows "pmax a b = a"
  by (metis Rep_prat_inject assms max.absorb_iff1 pgte.rep_eq pmax.rep_eq)


lemma pmax_is_smaller:
  assumes "pgte x a"
      and "pgte x b"
    shows "pgte x (pmax a b)"
proof (cases "pgte a b")
  case True
  then show ?thesis
    by (simp add: assms(1) pmax_is)
next
  case False
  then show ?thesis
    using assms(2) pgte.rep_eq pmax.rep_eq by auto
qed


lemma half_between_0_1:
  "ppos half \<and> pgt pwrite half"
  by (simp add: half.rep_eq pgt.rep_eq ppos.rep_eq pwrite.rep_eq)

lemma pgt_implies_pgte:
  assumes "pgt a b"
  shows "pgte a b"
  by (meson assms less_imp_le pgt.rep_eq pgte.rep_eq)

lemma half_plus_half:
  "padd half half = pwrite"
  by (metis Rep_prat_inject divide_less_eq_numeral1(1) dual_order.irrefl half.rep_eq less_divide_eq_numeral1(1) linorder_neqE_linordered_idom mult.right_neutral one_add_one padd.rep_eq pwrite.rep_eq ring_class.ring_distribs(1))

lemma padd_comm:
  "padd a b = padd b a"
  by (metis Rep_prat_inject add.commute padd.rep_eq)

lemma padd_asso:
  "padd (padd a b) c = padd a (padd b c)"
  by (metis Rep_prat_inverse group_cancel.add1 padd.rep_eq)


lemma p_greater_exists:
  "pgte a b \<longleftrightarrow> (\<exists>r. a = padd b r)"
proof (rule iffI)
  show "pgte a b \<Longrightarrow> \<exists>r. a = padd b r"
  proof -
    assume asm: "pgte a b"
    obtain aa bb where "aa = Rep_prat a" "bb = Rep_prat b"
      by simp
    then have "aa \<ge> bb" using asm
      using pgte.rep_eq by fastforce
    then obtain rr where "rr = aa - bb"
      by simp
    then have "a = padd b (Abs_prat rr)"
      by (metis Abs_prat_inverse Rep_prat_inject \<open>aa = Rep_prat a\<close> \<open>bb = Rep_prat b\<close> \<open>bb \<le> aa\<close> add.commute diff_add_cancel diff_ge_0_iff_ge mem_Collect_eq padd.rep_eq)
    then show "\<exists>r. a = padd b r" by blast
  qed
  show "\<exists>r. a = padd b r \<Longrightarrow> pgte a b"
    using Rep_prat padd.rep_eq pgte.rep_eq by force
qed


lemma pgte_antisym:
  assumes "pgte a b"
      and "pgte b a"
    shows "a = b"
  by (metis Rep_prat_inverse assms(1) assms(2) leD le_less pgte.rep_eq)

lemma greater_sum_both:
  assumes "pgte a (padd b c)"
  shows "\<exists>a1 a2. a = padd a1 a2 \<and> pgte a1 b \<and> pgte a2 c"
proof -
  obtain aa bb cc where "aa = Rep_prat a" "bb = Rep_prat b" "cc = Rep_prat c"
    by simp
  then have "aa \<ge> bb + cc"
    using assms padd.rep_eq pgte.rep_eq by auto
  then obtain x where "aa = bb + x" "x \<ge> cc"
    by (metis add.commute add_le_cancel_left diff_add_cancel)
  then show ?thesis
    by (metis assms order_refl p_greater_exists padd_asso pgte.rep_eq)
qed


lemma padd_cancellative:
  assumes "a = padd x b"
      and "a = padd y b"
    shows "x = y"
  by (metis Rep_prat_inject add_le_cancel_right assms(1) assms(2) leD less_eq_rat_def padd.rep_eq)


lemma not_pgte_charact:
  "\<not> pgte a b \<longleftrightarrow> pgt b a"
  by (meson not_less pgt.rep_eq pgte.rep_eq)

lemma pgte_pgt:
  assumes "pgt a b"
      and "pgte c d"
    shows "pgt (padd a c) (padd b d)"
  using assms(1) assms(2) padd.rep_eq pgt.rep_eq pgte.rep_eq by auto

lemma pmult_distr:
  "pmult a (padd b c) = padd (pmult a b) (pmult a c)"
  by (metis Rep_prat_inject distrib_left padd.rep_eq pmult.rep_eq)

lemma pmult_comm:
  "pmult a b = pmult b a"
  by (metis Rep_prat_inject mult.commute pmult.rep_eq)

lemma pmult_special:
  "pmult pwrite x = x"
  "pmult pnone x = pnone"
  apply (metis Rep_prat_inverse comm_monoid_mult_class.mult_1 pmult.rep_eq pwrite.rep_eq)
  by (metis Rep_prat_inverse mult_zero_left pmult.rep_eq pnone.rep_eq)



definition pinv where
  "pinv p = pdiv pwrite p"

lemma pinv_double_half:
  assumes "ppos p"
  shows "pmult half (pinv p) = pinv (padd p p)"
proof -
  have "(Fract 1 2) * ((Fract 1 1) / (Rep_prat p)) = (Fract 1 1) / (Rep_prat p + Rep_prat p)"
    by (metis (no_types, lifting) One_rat_def comm_monoid_mult_class.mult_1 divide_rat mult_2 mult_rat rat_number_expand(3) times_divide_times_eq)
  then show ?thesis
    by (metis Rep_prat_inject half.rep_eq mult_2 mult_numeral_1_right numeral_One padd.rep_eq pdiv.rep_eq pinv_def pmult.rep_eq pwrite.rep_eq times_divide_times_eq)
qed

lemma ppos_mult:
  assumes "ppos a"
      and "ppos b"
    shows "ppos (pmult a b)"
  using assms(1) assms(2) pmult.rep_eq ppos.rep_eq by auto

lemma padd_zero:
  "pnone = padd a b \<longleftrightarrow> a = pnone \<and> b = pnone"
  by (metis Rep_prat Rep_prat_inject add.right_neutral leD le_add_same_cancel2 less_eq_rat_def mem_Collect_eq padd.rep_eq pnone.rep_eq)

lemma ppos_add:
  assumes "ppos a"
  shows "ppos (padd a b)"
  by (metis Rep_prat Rep_prat_inject assms dual_order.strict_iff_order mem_Collect_eq padd_zero pnone.rep_eq ppos.rep_eq)



lemma pinv_inverts:
  assumes "pgte a b"
      and "ppos b"
    shows "pgte (pinv b) (pinv a)"
proof -
  have "Rep_prat a \<ge> Rep_prat b"
    using assms(1) pgte.rep_eq by auto
  then have "(Fract 1 1) / Rep_prat b \<ge> (Fract 1 1) / Rep_prat a"
    by (metis One_rat_def assms(2) frac_le le_numeral_extra(4) ppos.rep_eq zero_le_one)
  then show ?thesis
    by (simp add: One_rat_def pdiv.rep_eq pgte.rep_eq pinv_def pwrite.rep_eq)
qed



lemma pinv_pmult_ok:
  assumes "ppos p"
  shows "pmult p (pinv p) = pwrite"
proof -
  obtain r where "r = Rep_prat p" by simp
  then have "r * ((Fract 1 1) / r) = Fract 1 1"
    using assms ppos.rep_eq by force
  then show ?thesis
    by (metis One_rat_def Rep_prat_inject \<open>r = Rep_prat p\<close> pdiv.rep_eq pinv_def pmult.rep_eq pwrite.rep_eq)
qed


lemma pinv_pwrite:
  "pinv pwrite = pwrite"
  by (metis Rep_prat_inverse div_by_1 pdiv.rep_eq pinv_def pwrite.rep_eq)

lemma pmult_ppos:
  assumes "ppos a"
      and "ppos b"
    shows "ppos (pmult a b)"
  using assms(1) assms(2) pmult.rep_eq ppos.rep_eq by auto


lemma ppos_inv:
  assumes "ppos p"
  shows "ppos (pinv p)"
by (metis Rep_prat Rep_prat_inverse assms less_eq_rat_def mem_Collect_eq not_one_le_zero pinv_pmult_ok pmult_comm pmult_special(2) pnone.rep_eq ppos.rep_eq pwrite.rep_eq)


lemma pmin_pmax:
  assumes "pgte x (pmin a b)"
  shows "x = pmin (pmax x a) (pmax x b)"
proof (cases "pgte x a")
  case True
  then show ?thesis
    by (metis pmax_is pmax_smaller pmin_comm pmin_is)
next
  case False
  then show ?thesis
    by (metis assms not_pgte_charact pgt_implies_pgte pmax_is pmax_smaller pmin_comm pmin_is)
qed

definition comp_one where
  "comp_one p = (SOME r. padd p r = pwrite)"

lemma padd_comp_one:
  assumes "pgte pwrite x"
  shows "padd x (comp_one x) = pwrite"
  by (metis (mono_tags, lifting) assms comp_one_def p_greater_exists someI_ex)

lemma ppos_eq_pnone:
  "ppos p \<longleftrightarrow> p \<noteq> pnone"
  by (metis Rep_prat Rep_prat_inject dual_order.strict_iff_order mem_Collect_eq pnone.rep_eq ppos.rep_eq)



lemma pmult_order:
  assumes "pgte a b"
  shows "pgte (pmult p a) (pmult b p)"
  using assms p_greater_exists pmult_comm pmult_distr by force

lemma multiply_smaller_pwrite:
  assumes "pgte pwrite a"
      and "pgte pwrite b"
    shows "pgte pwrite (pmult a b)"
  by (metis assms(1) assms(2) p_greater_exists padd_asso pmult_order pmult_special(1))


lemma pmult_pdiv_cancel:
  assumes "ppos a"
  shows "pmult a (pdiv x a) = x"
  by (metis Rep_prat_inject assms divide_cancel_right dual_order.strict_iff_order nonzero_mult_div_cancel_left pdiv.rep_eq pmult.rep_eq ppos.rep_eq)

lemma pmult_padd:
  "pmult a (padd (pmult b x) (pmult c y)) = padd (pmult (pmult a b) x) (pmult (pmult a c) y)"
  by (metis Rep_prat_inject mult.assoc pmult.rep_eq pmult_distr)


lemma pdiv_smaller:
  assumes "pgte a b"
      and "ppos a"
  shows "pgte pwrite (pdiv b a)"
proof -
  let ?a = "Rep_prat a"
  let ?b = "Rep_prat b"
  have "?b / ?a \<le> 1"
    by (meson assms(1) assms(2) divide_le_eq_1_pos pgte.rep_eq ppos.rep_eq)
  then show ?thesis
    by (simp add: pdiv.rep_eq pgte.rep_eq pwrite.rep_eq)
qed


lemma sum_coeff:
  assumes "ppos a"
      and "ppos b"
    shows "padd (pdiv a (padd a b)) (pdiv b (padd a b)) = pwrite"
proof -
  let ?a = "Rep_prat a"
  let ?b = "Rep_prat b"
  have "(?a / (?a + ?b)) + (?b / (?a + ?b)) = 1"
    by (metis add_divide_distrib add_pos_pos assms(1) assms(2) less_irrefl ppos.rep_eq right_inverse_eq)
  then show ?thesis
    by (metis Rep_prat_inject padd.rep_eq pdiv.rep_eq pwrite.rep_eq)
qed

lemma padd_one_ineq_sum:
  assumes "padd a b = pwrite"
      and "pgte x aa"
      and "pgte x bb"
    shows "pgte x (padd (pmult a aa) (pmult b bb))"
  by (metis (mono_tags, lifting) Rep_prat assms(1) assms(2) assms(3) convex_bound_le mem_Collect_eq padd.rep_eq pgte.rep_eq pmult.rep_eq pwrite.rep_eq)


end
