subsection \<open>Fractional Permissions\<close>

theory PosRat
  imports Main HOL.Rat
begin

typedef prat = "{ r :: rat |r. r > 0}" by fastforce

setup_lifting type_definition_prat

lift_definition pwrite :: "prat" is "1" by simp
lift_definition half :: "prat" is "1 / 2" by fastforce

lift_definition pgte :: "prat \<Rightarrow> prat \<Rightarrow> bool" is "(\<ge>)" done
lift_definition pgt :: "prat \<Rightarrow> prat \<Rightarrow> bool" is "(>)" done
lift_definition lt :: "prat \<Rightarrow> prat \<Rightarrow> bool" is "(<)" done

lift_definition pmult :: "prat \<Rightarrow> prat \<Rightarrow> prat" is "(*)" by simp
lift_definition padd :: "prat \<Rightarrow> prat \<Rightarrow> prat" is "(+)" by simp

lift_definition pdiv :: "prat \<Rightarrow> prat \<Rightarrow> prat" is "(/)" by simp

lift_definition pmin :: "prat \<Rightarrow> prat \<Rightarrow> prat" is "(min)" by simp
lift_definition pmax :: "prat \<Rightarrow> prat \<Rightarrow> prat" is "(max)" by simp

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
  "pgt pwrite half"
  by (simp add: half.rep_eq pgt.rep_eq pwrite.rep_eq)

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

lemma pgte_antisym:
  assumes "pgte a b"
      and "pgte b a"
    shows "a = b"
  by (metis Rep_prat_inverse assms(1) assms(2) leD le_less pgte.rep_eq)

lemma sum_larger:
  "pgt (padd a b) a"
  using Rep_prat padd.rep_eq pgt.rep_eq by auto

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
    by (metis (no_types, lifting) Abs_prat_inverse Rep_prat Rep_prat_inverse \<open>aa = Rep_prat a\<close> \<open>bb = Rep_prat b\<close> \<open>cc = Rep_prat c\<close> dual_order.trans eq_onp_same_args le_less mem_Collect_eq min_absorb2 min_def order_refl padd.abs_eq pgte.rep_eq)
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
  by (metis Rep_prat_inverse comm_monoid_mult_class.mult_1 pmult.rep_eq pwrite.rep_eq)

definition pinv where
  "pinv p = pdiv pwrite p"

lemma pinv_double_half:
  "pmult half (pinv p) = pinv (padd p p)"
proof -
  have "(Fract 1 2) * ((Fract 1 1) / (Rep_prat p)) = (Fract 1 1) / (Rep_prat p + Rep_prat p)"
    by (metis (no_types, lifting) One_rat_def comm_monoid_mult_class.mult_1 divide_rat mult_2 mult_rat rat_number_expand(3) times_divide_times_eq)
  then show ?thesis
    by (metis Rep_prat_inject half.rep_eq mult_2 mult_numeral_1_right numeral_One padd.rep_eq pdiv.rep_eq pinv_def pmult.rep_eq pwrite.rep_eq times_divide_times_eq)
qed



lemma pinv_inverts:
  assumes "pgte a b"
    shows "pgte (pinv b) (pinv a)"
proof -
  have "Rep_prat a \<ge> Rep_prat b"
    using assms(1) pgte.rep_eq by auto
  then have "(Fract 1 1) / Rep_prat b \<ge> (Fract 1 1) / Rep_prat a"
    by (metis One_rat_def Rep_prat frac_le le_numeral_extra(4) mem_Collect_eq zero_le_one)
  then show ?thesis
    by (simp add: One_rat_def pdiv.rep_eq pgte.rep_eq pinv_def pwrite.rep_eq)
qed



lemma pinv_pmult_ok:
  "pmult p (pinv p) = pwrite"
proof -
  obtain r where "r = Rep_prat p" by simp
  then have "r * ((Fract 1 1) / r) = Fract 1 1"
    by (metis Rep_prat less_numeral_extra(3) mem_Collect_eq nonzero_mult_div_cancel_left times_divide_eq_right)
  then show ?thesis
    by (metis One_rat_def Rep_prat_inject \<open>r = Rep_prat p\<close> pdiv.rep_eq pinv_def pmult.rep_eq pwrite.rep_eq)
qed


lemma pinv_pwrite:
  "pinv pwrite = pwrite"
  by (metis Rep_prat_inverse div_by_1 pdiv.rep_eq pinv_def pwrite.rep_eq)

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

lemma pmin_sum:
  "padd (pmin a b) c = pmin (padd a c) (padd b c)"
  by (metis not_pgte_charact pgt_implies_pgte pgte_pgt pmin_comm pmin_is)

lemma pmin_sum_larger:
  "pgte (pmin (padd a1 b1) (padd a2 b2)) (padd (pmin a1 a2) (pmin b1 b2))"
proof (cases "pgte (padd a1 b1) (padd a2 b2)")
  case True
  then have "pmin (padd a1 b1) (padd a2 b2) = padd a2 b2"
    by (simp add: pmin_is)
  moreover have "pgte a2 (pmin a1 a2) \<and> pgte b2 (pmin b1 b2)"
    by (metis pmin_comm pmin_greater)
  ultimately show ?thesis
    by (simp add: padd.rep_eq pgte.rep_eq)
next
  case False
  then have "pmin (padd a1 b1) (padd a2 b2) = padd a1 b1"
    by (metis not_pgte_charact pgt_implies_pgte pmin_comm pmin_is)
  moreover have "pgte a1 (pmin a1 a2) \<and> pgte b1 (pmin b1 b2)"
    by (metis pmin_greater)
  ultimately show ?thesis
    by (simp add: padd.rep_eq pgte.rep_eq)
qed

end
