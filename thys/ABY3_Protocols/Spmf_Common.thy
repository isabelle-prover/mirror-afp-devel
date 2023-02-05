theory Spmf_Common
  imports CryptHOL.CryptHOL
begin

no_adhoc_overloading Monad_Syntax.bind bind_pmf

lemma mk_lossless_back_eq:
  "scale_spmf (weight_spmf s) (mk_lossless s) = s"
  unfolding mk_lossless_def
  unfolding scale_scale_spmf
  by (auto simp: field_simps weight_spmf_eq_0)


lemma cond_spmf_enforce:
  "cond_spmf sx (Collect A) = mk_lossless (enforce_spmf A sx)"
  unfolding enforce_spmf_def
  unfolding cond_spmf_alt
  unfolding restrict_spmf_def
  unfolding enforce_option_alt_def
  apply (rule arg_cong[where f="mk_lossless"])
  apply (rule arg_cong[where f="\<lambda>x. map_pmf x sx"])
  apply (intro ext)
  apply (rule arg_cong[where f="Option.bind _"])
  apply auto
  done


definition "rel_scale_spmf s t \<longleftrightarrow> (mk_lossless s = mk_lossless t)"

lemma rel_scale_spmf_refl:
  "rel_scale_spmf s s"
  unfolding rel_scale_spmf_def ..

lemma rel_scale_spmf_sym:
  "rel_scale_spmf s t \<Longrightarrow> rel_scale_spmf t s"
  unfolding rel_scale_spmf_def by simp

lemma rel_scale_spmf_trans:
  "rel_scale_spmf s t \<Longrightarrow> rel_scale_spmf t u \<Longrightarrow> rel_scale_spmf s u"
  unfolding rel_scale_spmf_def by simp

lemma rel_scale_spmf_equiv:
  "equivp rel_scale_spmf"
  using rel_scale_spmf_refl rel_scale_spmf_sym
  by (auto intro!: equivpI reflpI sympI transpI dest: rel_scale_spmf_trans)


lemma spmf_eq_iff: "p = q \<longleftrightarrow> (\<forall>i. spmf p i = spmf q i)"
  using spmf_eqI by auto

lemma spmf_eq_iff_set:
  "set_spmf a = set_spmf b \<Longrightarrow> (\<And>x. x \<in> set_spmf b \<Longrightarrow> spmf a x = spmf b x) \<Longrightarrow> a = b"
  using in_set_spmf_iff_spmf spmf_eq_iff
  by (metis)

lemma rel_scale_spmf_None:
  "rel_scale_spmf s t \<Longrightarrow> s = return_pmf None \<longleftrightarrow> t = return_pmf None"
  unfolding rel_scale_spmf_def by auto

lemma rel_scale_spmf_def_alt:
  "rel_scale_spmf s t \<longleftrightarrow> (\<exists>k>0. s = scale_spmf k t)"
proof
  assume rel: "rel_scale_spmf s t"
  then consider (isNone) "s = return_pmf None \<and> t = return_pmf None" | (notNone) "weight_spmf s > 0 \<and> weight_spmf t > 0"
    using rel_scale_spmf_None weight_spmf_eq_0 zero_less_measure_iff by blast
  then show "\<exists>k>0. s = scale_spmf k t"
  proof cases
    case isNone
    show ?thesis
      apply (rule exI[of _ 1])
      using isNone by simp
  next
    case notNone
    have "scale_spmf (weight_spmf s) (mk_lossless s) = scale_spmf (weight_spmf s / weight_spmf t) t"
      unfolding rel[unfolded rel_scale_spmf_def]
      unfolding mk_lossless_def
      unfolding scale_scale_spmf
      by (auto simp: field_simps)
    then show "\<exists>k>0. s = scale_spmf k t"
      apply (unfold mk_lossless_back_eq)
      using notNone divide_pos_pos by blast
  qed
next
  assume "\<exists>k>0. s = scale_spmf k t"
  then obtain k where kpos: "k>0" and st: "s = scale_spmf k t" by blast
  then consider (isNone) "weight_spmf s = 0 \<and> weight_spmf t = 0" | (notNone) "weight_spmf s > 0 \<and> weight_spmf t > 0"
    using zero_less_measure_iff mult_pos_pos zero_less_measure_iff by (fastforce simp: weight_scale_spmf)
  then show "rel_scale_spmf s t"
  proof cases
    case isNone
    then show ?thesis
      unfolding rel_scale_spmf_def weight_spmf_eq_0 by simp
  next
    case notNone
    then show ?thesis
      unfolding rel_scale_spmf_def
      unfolding mk_lossless_def
      unfolding st
      by (cases "k < inverse (weight_spmf t)")
        (auto simp: weight_scale_spmf scale_scale_spmf field_simps)
  qed
qed

lemma rel_scale_spmf_def_alt2:
  "rel_scale_spmf s t \<longleftrightarrow>
    (s = return_pmf None \<and> t = return_pmf None)
  | (weight_spmf s > 0 \<and> weight_spmf t > 0 \<and> s = scale_spmf (weight_spmf s / weight_spmf t) t)"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume rel: ?lhs
  then consider (isNone) "s = return_pmf None \<and> t = return_pmf None" | (notNone) "weight_spmf s > 0 \<and> weight_spmf t > 0"
    using rel_scale_spmf_None weight_spmf_eq_0 zero_less_measure_iff by blast
  thus ?rhs
  proof cases
    case notNone
    have "scale_spmf (weight_spmf s) (mk_lossless s) = scale_spmf (weight_spmf s / weight_spmf t) t"
      unfolding rel[unfolded rel_scale_spmf_def]
      unfolding mk_lossless_def
      unfolding scale_scale_spmf
      by (auto simp: field_simps)
    thus ?thesis
      apply (unfold mk_lossless_back_eq)
      using notNone by simp
  qed simp
next
  assume ?rhs
  then show ?lhs
  proof cases
    case right
    then have gt0: "weight_spmf s > 0" "weight_spmf t > 0" and st: "s = scale_spmf (weight_spmf s / weight_spmf t) t"
      by auto
    then have "(1 / weight_spmf t) \<ge> (weight_spmf s / weight_spmf t)"
      using weight_spmf_le_1 divide_le_cancel by fastforce
    then show ?thesis
      unfolding rel_scale_spmf_def mk_lossless_def
      apply (subst (3) st)
      using gt0 by (auto simp: scale_scale_spmf field_simps)
  qed (simp add: rel_scale_spmf_refl)
qed

lemma rel_scale_spmf_scale:
  "r > 0 \<Longrightarrow> rel_scale_spmf s t \<Longrightarrow> rel_scale_spmf s (scale_spmf r t)"
  apply (unfold rel_scale_spmf_def_alt)
  by (metis rel_scale_spmf_def rel_scale_spmf_def_alt)

lemma rel_scale_spmf_mk_lossless:
  "rel_scale_spmf s t \<Longrightarrow> rel_scale_spmf s (mk_lossless t)"
  unfolding rel_scale_spmf_def_alt
  unfolding mk_lossless_def
  apply (cases "weight_spmf t = 0")
  subgoal by(simp add: weight_spmf_eq_0)
  subgoal
    apply (auto simp: weight_spmf_eq_0 field_simps scale_scale_spmf)
    using rel_scale_spmf_def_alt rel_scale_spmf_def_alt2 by blast
  done

lemma rel_scale_spmf_eq_iff:
  "rel_scale_spmf s t \<Longrightarrow> weight_spmf s = weight_spmf t \<Longrightarrow> s = t"
  unfolding rel_scale_spmf_def_alt2 by auto

lemma rel_scale_spmf_set_restrict:
  "finite A \<Longrightarrow> rel_scale_spmf (restrict_spmf (spmf_of_set A) B) (spmf_of_set (A \<inter> B))"
  apply (unfold rel_scale_spmf_def)
  apply (fold cond_spmf_alt)
  apply (subst cond_spmf_spmf_of_set)
  subgoal .
  apply (unfold mk_lossless_spmf_of_set)
  ..

lemma spmf_of_set_restrict_empty:
  "A \<inter> B = {} \<Longrightarrow> restrict_spmf (spmf_of_set A) B = return_pmf None"
  unfolding spmf_of_set_def
  by simp

lemma spmf_of_set_restrict_scale:
  "finite A \<Longrightarrow> restrict_spmf (spmf_of_set A) B = scale_spmf (card (A\<inter>B) / card A) (spmf_of_set (A\<inter>B))"
  apply (rule rel_scale_spmf_eq_iff)
  subgoal
    apply (cases "A\<inter>B = {}")
    subgoal
      by (auto simp: spmf_of_set_restrict_empty intro: rel_scale_spmf_refl)
    subgoal
      apply (rule rel_scale_spmf_scale)
      subgoal
        by (metis card_gt_0_iff divide_pos_pos finite_Int inf_bot_left of_nat_0_less_iff)
      subgoal by (rule rel_scale_spmf_set_restrict)
      done
    done
  subgoal
    apply (auto simp add: weight_scale_spmf measure_spmf_of_set)
    by (smt (verit, best) card_gt_0_iff card_mono disjoint_notin1 divide_le_eq_1_pos finite_Int inf_le1 of_nat_0_less_iff of_nat_le_iff)
  done

lemma min_em2:
  "min a b = c \<Longrightarrow> a\<noteq>c \<Longrightarrow> b=c"
  unfolding min_def by auto

lemma weight_0_spmf:
  "weight_spmf s = 0 \<Longrightarrow> spmf s i = 0"
  using order_trans[OF spmf_le_weight, of s 0 i] by simp

lemma mk_lossless_scale_absorb:
  "r > 0 \<Longrightarrow> mk_lossless (scale_spmf r s) = mk_lossless s"
  apply (rule rel_scale_spmf_eq_iff)
  subgoal
    apply (rule rel_scale_spmf_trans[where t=s])
    subgoal
      apply (rule rel_scale_spmf_sym)
      apply (rule rel_scale_spmf_mk_lossless)
      apply (rule rel_scale_spmf_scale)
      subgoal .
      subgoal by (rule rel_scale_spmf_refl)
      done
    subgoal
      apply (rule rel_scale_spmf_mk_lossless)
      apply (rule rel_scale_spmf_refl)
      done
    done
  subgoal
    unfolding weight_mk_lossless
    by (auto simp flip: weight_spmf_eq_0 simp: weight_scale_spmf dest: min_em2)
  done

lemma scale_spmf_None_iff:
  "scale_spmf k s = return_pmf None \<longleftrightarrow> k\<le>0 \<or> s=return_pmf None"
  apply (auto simp: spmf_eq_iff spmf_scale_spmf)
  using
    inverse_nonpositive_iff_nonpositive
    weight_0_spmf
    weight_spmf_le_0
  by smt

lemma spmf_of_pmf_the:
  "lossless_spmf s \<Longrightarrow> spmf_of_pmf (map_pmf the s) = s"
  unfolding lossless_spmf_conv_spmf_of_pmf by auto

lemma lossless_mk_lossless:
  "s \<noteq> return_pmf None \<Longrightarrow> lossless_spmf (mk_lossless s)"
  unfolding lossless_spmf_def
  unfolding weight_mk_lossless
  by simp

definition pmf_of_spmf where
  "pmf_of_spmf p = map_pmf the (mk_lossless p)"

lemma scale_weight_spmf_of_pmf:
  "p = scale_spmf (weight_spmf p) (spmf_of_pmf (pmf_of_spmf p))"
  unfolding pmf_of_spmf_def
  apply (cases "p = return_pmf None")
  subgoal by simp
  subgoal
    apply (subst mk_lossless_back_eq[of p, symmetric])
    apply (rule arg_cong[where f="scale_spmf _ "])
    apply (rule spmf_of_pmf_the[symmetric])
    by (fact lossless_mk_lossless)
  done

lemma pmf_spmf:
  "pmf_of_spmf (spmf_of_pmf p) = p"
  unfolding pmf_of_spmf_def
  unfolding lossless_spmf_spmf_of_spmf[THEN mk_lossless_lossless]
  unfolding map_the_spmf_of_pmf
  ..

lemma spmf_pmf:
  "lossless_spmf p \<Longrightarrow> spmf_of_pmf (pmf_of_spmf p) = p"
  unfolding pmf_of_spmf_def
  by (simp add: spmf_of_pmf_the)

lemma pmf_of_spmf_scale_spmf:
  "r > 0 \<Longrightarrow> pmf_of_spmf (scale_spmf r p) = pmf_of_spmf p"
  unfolding pmf_of_spmf_def
  by (simp add: mk_lossless_scale_absorb)

lemma nonempty_spmf_weight:
  "p \<noteq> return_pmf None \<longleftrightarrow> weight_spmf p > 0"
  apply (fold weight_spmf_eq_0)
  using dual_order.not_eq_order_implies_strict[OF _ weight_spmf_nonneg[of p]]
  by auto

lemma pmf_of_spmf_mk_lossless:
  "pmf_of_spmf (mk_lossless p) = pmf_of_spmf p"
  apply (cases "p = return_pmf None")
  subgoal by auto
  apply (unfold mk_lossless_def)
  apply (subst pmf_of_spmf_scale_spmf)
  subgoal by (simp add: nonempty_spmf_weight)
  ..

lemma spmf_pmf':
  "p \<noteq> return_pmf None \<Longrightarrow> spmf_of_pmf (pmf_of_spmf p) = mk_lossless p"
  apply (subst spmf_pmf[of "mk_lossless p", symmetric])
   apply (unfold pmf_of_spmf_mk_lossless)
  subgoal using lossless_mk_lossless .
  subgoal ..
  done

lemma rel_scale_spmf_cond_UNIV:
  "rel_scale_spmf s (cond_spmf s UNIV)"
  unfolding cond_spmf_UNIV
  by (rule rel_scale_spmf_mk_lossless) (rule rel_scale_spmf_refl)

lemma "set_pmf p \<inter> g \<noteq> {} \<Longrightarrow> pmf_prob p (f \<inter> g) = pmf_prob (cond_pmf p g) f * pmf_prob p g"
  using measure_cond_pmf
  unfolding pmf_prob_def
  by (metis Int_commute divide_eq_eq measure_measure_pmf_not_zero)

lemma bayes:
  "set_pmf p \<inter> A \<noteq> {} \<Longrightarrow> set_pmf p \<inter> B \<noteq> {} \<Longrightarrow>
   measure_pmf.prob (cond_pmf p A) B
 = measure_pmf.prob (cond_pmf p B) A * measure_pmf.prob p B / measure_pmf.prob p A"
  unfolding measure_cond_pmf
  by (subst inf_commute) (simp add: measure_pmf_zero_iff)

definition spmf_prob :: "'a spmf \<Rightarrow> 'a set \<Rightarrow> real" where
  "spmf_prob p = Sigma_Algebra.measure (measure_spmf p)"

lemma "spmf_prob = measure_measure_spmf"
  unfolding spmf_prob_def measure_measure_spmf_def ..

lemma spmf_prob_pmf:
  "spmf_prob p A = pmf_prob p (Some ` A)"
  unfolding spmf_prob_def pmf_prob_def
  unfolding measure_measure_spmf_conv_measure_pmf
  ..

lemma bayes_spmf:
  "spmf_prob (cond_spmf p A) B
 = spmf_prob (cond_spmf p B) A * spmf_prob p B / spmf_prob p A"
  unfolding spmf_prob_def
  unfolding measure_cond_spmf
  by (subst inf_commute) (auto simp: measure_spmf_zero_iff)

lemma spmf_prob_pmf_of_spmf:
  "spmf_prob p A = weight_spmf p * pmf_prob (pmf_of_spmf p) A"
  apply (subst scale_weight_spmf_of_pmf)
  apply (unfold spmf_prob_def)
  apply (subst measure_spmf_scale_spmf')
  subgoal using weight_spmf_le_1 .
  by (simp add: pmf_prob_def)

lemma cond_spmf_Int:
  "cond_spmf (cond_spmf p A) B = cond_spmf p (A \<inter> B)"
  apply (rule spmf_eqI)
  apply (unfold spmf_cond_spmf)
  apply(auto simp add: measure_cond_spmf split: if_split_asm)
  using Int_lower1[THEN measure_spmf.finite_measure_mono[simplified]]  measure_le_0_iff
  by metis

lemma cond_spmf_prob:
  "spmf_prob p (A \<inter> B) = spmf_prob (cond_spmf p A) B * spmf_prob p A"
  unfolding spmf_prob_def measure_cond_spmf
  using Int_lower1[THEN measure_spmf.finite_measure_mono[simplified]]  measure_le_0_iff
  by (metis mult_eq_0_iff nonzero_eq_divide_eq)

definition "empty_spmf = return_pmf None"

lemma spmf_prob_empty:
  "spmf_prob empty_spmf A = 0"
  unfolding spmf_prob_def empty_spmf_def
  by simp

definition le_spmf :: "'a spmf \<Rightarrow> 'a spmf \<Rightarrow> bool" where
  "le_spmf p q \<longleftrightarrow> (\<exists>k\<le>1. p = scale_spmf k q)"

definition lt_spmf :: "'a spmf \<Rightarrow> 'a spmf \<Rightarrow> bool" where
  "lt_spmf p q \<longleftrightarrow> (\<exists>k<1. p = scale_spmf k q)"

lemma "class.order_bot empty_spmf le_spmf lt_spmf"
  oops

lemma spmf_prob_cond_Int:
  "spmf_prob (cond_spmf p C) (A \<inter> B)
   = spmf_prob (cond_spmf p (B \<inter> C)) A * spmf_prob (cond_spmf p C) B"
  apply (subst Int_commute[of B C])
  apply (subst Int_commute[of A B])
  apply (fold cond_spmf_Int)
  using cond_spmf_prob .

lemma cond_spmf_mk_lossless:
  "cond_spmf (mk_lossless p) A = cond_spmf p A"
  apply (fold cond_spmf_UNIV)
  apply (unfold cond_spmf_Int)
  by simp

primrec sequence_spmf :: "'a spmf list \<Rightarrow> 'a list spmf" where
  "sequence_spmf [] = return_spmf []"
| "sequence_spmf (x#xs) = map_spmf (case_prod Cons) (pair_spmf x (sequence_spmf xs))"

lemma set_sequence_spmf:
  "set_spmf (sequence_spmf xs) = {l. list_all2 (\<lambda>x s. x \<in> set_spmf s) l xs}"
  by (induction xs) (auto simp: list_all2_Cons2)

lemma map_spmf_map_sequence:
  "map_spmf (map f) (sequence_spmf xs) = sequence_spmf (map (map_spmf f) xs)"
  apply (induction xs)
  subgoal by simp
  subgoal premises IH
    unfolding list.map
    unfolding sequence_spmf.simps
    apply (fold IH)
    apply (unfold pair_map_spmf)
    apply (unfold spmf.map_comp)
    by (simp add: comp_def case_prod_map_prod prod.case_distrib)
  done

lemma sequence_map_return_spmf:
  "sequence_spmf (map return_spmf xs) = return_spmf xs"
  by (induction xs) auto

lemma sequence_bind_cong:
  "\<lbrakk>xs=ys; \<And>y. length y = length ys \<Longrightarrow> f y = g y\<rbrakk> \<Longrightarrow> bind_spmf (sequence_spmf xs) f = bind_spmf (sequence_spmf ys) g"
  apply (rule bind_spmf_cong)
  subgoal by simp
  subgoal unfolding set_sequence_spmf list_all2_iff by simp
  done

lemma bind_spmf_sequence_replicate_cong:
  "(\<And>l. length l = n \<Longrightarrow> f l = g l)
    \<Longrightarrow> bind_spmf (sequence_spmf (replicate n x)) f = bind_spmf (sequence_spmf (replicate n x)) g"
  by (rule bind_spmf_cong[OF refl]) (simp add: set_spmf_of_set finite_permutations set_sequence_spmf[unfolded list_all2_iff])

lemma bind_spmf_sequence_map_cong:
  "(\<And>l. length l = length x \<Longrightarrow> f l = g l)
    \<Longrightarrow> bind_spmf (sequence_spmf (map m x)) f = bind_spmf (sequence_spmf (map m x)) g"
  by (rule bind_spmf_cong[OF refl]) (simp add: set_spmf_of_set finite_permutations set_sequence_spmf[unfolded list_all2_iff])

lemma lossless_pair_spmf_iff:
  "lossless_spmf (pair_spmf a b) \<longleftrightarrow> lossless_spmf a \<and> lossless_spmf b"
  unfolding pair_spmf_alt_def
  by (auto simp: set_spmf_eq_empty)

lemma lossless_sequence_spmf:
  "(\<And>x. x\<in>set xs \<Longrightarrow> lossless_spmf x) \<Longrightarrow> lossless_spmf (sequence_spmf xs)"
  by (induction xs) (auto simp: lossless_pair_spmf_iff)

end