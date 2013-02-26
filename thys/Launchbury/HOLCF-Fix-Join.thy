theory "HOLCF-Fix-Join"
  imports "HOLCF-Set" "HOLCF-Join"
begin

subsubsection {* A carrier set for fixed points of binary joins *}

text {* @{term fix_join_compat} is a set in which the join operation is always defined, and can
serve as carrier sets for the various HOLCF-Set operations. *}

definition fix_join_compat where 
  "fix_join_compat (\<rho>::'a::{Bounded_Nonempty_Meet_cpo,subpcpo_partition})  F = {\<rho>'. \<rho>' \<sqsubseteq> fix_on' (to_bot \<rho>) (\<lambda> \<rho>'. \<rho> \<squnion> F \<rho>')}"

lemma fjc_iff[iff]:
  "\<rho>' \<in> fix_join_compat \<rho> F \<longleftrightarrow> \<rho>' \<sqsubseteq> fix_on' (to_bot \<rho>) (\<lambda> \<rho>'. \<rho> \<squnion> F \<rho>')"
  unfolding fix_join_compat_def by auto

lemma subcpo_fjc: "subcpo (fix_join_compat \<rho> F)"
  unfolding fix_join_compat_def by (rule subcpo_cone_below)

lemma subpcpo_fjc: "subpcpo (fix_join_compat \<rho> F)"
  unfolding fix_join_compat_def by (rule subpcpo_cone_below)

lemma subpcpo_bot_fjc: "subpcpo_bot (fix_join_compat \<rho> F) (to_bot \<rho>)"
  apply (rule subpcpo_botI)
  apply (metis subcpo.cpo subcpo_fjc)
  apply (auto)
  by (metis to_bot_fix_on to_bot_minimal unrelated)

lemma bottom_of_fjc: "bottom_of (fix_join_compat \<rho> F) = to_bot \<rho>"
  by (rule bottom_of_subpcpo_bot[OF subpcpo_bot_fjc])

lemma down_closed_fjc: "\<And>x y. x \<in> fix_join_compat \<rho> F \<Longrightarrow> y \<sqsubseteq> x \<Longrightarrow> y \<in> fix_join_compat \<rho> F"
  by (auto dest:below_trans)

lemma compat_fjc: "x \<in> fix_join_compat \<rho> F \<Longrightarrow> y \<in> fix_join_compat \<rho> F \<Longrightarrow> compatible x y"
  by (auto elim:ub_implies_compatible)

lemma join_fjc: "x \<in> fix_join_compat \<rho> F \<Longrightarrow> y \<in> fix_join_compat \<rho> F \<Longrightarrow> x \<squnion> y \<in> fix_join_compat \<rho> F"
  by (rule, metis join_below[OF compat_fjc] fjc_iff)

lemma closed_on_join_fjc: "closed_on (fix_join_compat \<rho> F) G \<Longrightarrow> closed_on (fix_join_compat \<rho> F) H \<Longrightarrow> closed_on (fix_join_compat \<rho> F) (\<lambda> x. G x \<squnion> H x)"
  apply (rule closed_onI)
  apply (rule join_fjc)
  apply (erule (1) closed_onE)+
  done

lemma cont_on_join_fjc:
  assumes "closed_on (fix_join_compat \<rho> F) G"
  assumes "closed_on (fix_join_compat \<rho> F) H"
  assumes "cont_on  (fix_join_compat \<rho> F) G"
  assumes "cont_on  (fix_join_compat \<rho> F) H"
  shows "cont_on (fix_join_compat \<rho> F) (\<lambda> x. G x \<squnion> H x)"
  proof(rule subpcpo.cont_onI2[OF subpcpo_fjc])
  case goal1
  show ?case
    proof(rule monofun_onI)
    case (goal1 x y)
      hence "compatible (G x) (H x)" and "compatible (G y) (H y)"
        by -(rule compat_fjc[OF closed_onE[OF assms(1)] closed_onE[OF assms(2)]], assumption+)+
      moreover
      from goal1
      have "G x \<sqsubseteq> G y"
        by (rule monofun_onE[OF cont_on2mono_on[OF assms(3)]])
      moreover
      from goal1
      have "H x \<sqsubseteq> H y"
        by (rule monofun_onE[OF cont_on2mono_on[OF assms(4)]])
      ultimately
      show ?case
        by (rule join_mono)
    qed
  next
  case (goal2 Y)
    have "G (\<Squnion> i. Y i) \<squnion> H (\<Squnion> i. Y i) = (\<Squnion> i. G (Y i)) \<squnion> (\<Squnion> i. H (Y i))"
      by (simp add: cont_on2contlubE[OF assms(3) goal2(1)]  cont_on2contlubE[OF assms(4) goal2(1)])
    also
    have "... = (\<Squnion> i. G (Y i) \<squnion> H (Y i))"
      apply (rule join_cont12)
      apply (rule chain_on_is_chain[OF ch2ch_cont_on'[OF assms(3) goal2(1) assms(1)]])
      apply (rule chain_on_is_chain[OF ch2ch_cont_on'[OF assms(4) goal2(1) assms(2)]])
      apply (rule compat_fjc[OF closed_onE[OF assms(1) chain_on_is_on[OF goal2(1)]] closed_onE[OF assms(2) chain_on_is_on[OF goal2(1)]]])
      done
   finally show ?case by (rule eq_imp_below)
qed

subsubsection {* Conditions for the existence of the fixed point of binary joins *}

inductive fix_join_cond
  where fix_join_condI:
  "cont F \<Longrightarrow>
   (\<And> i. compatible \<rho> (F (((\<lambda>\<rho>'. \<rho> \<squnion> F \<rho>')^^i) (to_bot \<rho>)))) \<Longrightarrow> fix_join_cond \<rho> F "


context
  fixes \<rho> :: "'a::{Bounded_Nonempty_Meet_cpo,subpcpo_partition}" and S and F
  assumes "fix_join_cond \<rho> F"
begin
  lemma cont_F_fjc: "cont F"
    by (rule fix_join_cond.induct[OF `fix_join_cond _ _`]) 

  lemma chain_compat_fjc: "compatible \<rho> (F (((\<lambda>\<rho>'. \<rho> \<squnion> F \<rho>')^^i) (to_bot \<rho>)))"
    by (rule fix_join_cond.induct[OF `fix_join_cond _ _`]) 

  lemma chain_fjc: "chain (\<lambda>i. ((\<lambda>\<rho>'. \<rho> \<squnion> F \<rho>')^^i) (to_bot \<rho>))"
  proof(rule chainI, induct_tac i, simp_all)
    have "to_bot \<rho> \<sqsubseteq> \<rho>"
      by (rule to_bot_minimal)
    also have "\<rho> \<sqsubseteq> \<rho> \<squnion> F (to_bot \<rho>)"
      by (rule join_above1[OF chain_compat_fjc[of 0, simplified]])
    finally
    show "to_bot \<rho> \<sqsubseteq> \<rho> \<squnion> F (to_bot \<rho>)".
   
    fix n
    assume "((\<lambda>\<rho>'. \<rho> \<squnion> F \<rho>') ^^ n) (to_bot \<rho>) \<sqsubseteq> \<rho> \<squnion> F (((\<lambda>\<rho>'. \<rho> \<squnion> F \<rho>') ^^ n) (to_bot \<rho>))"
    thus "\<rho> \<squnion> F (((\<lambda>\<rho>'. \<rho> \<squnion> F \<rho>') ^^ n) (to_bot \<rho>)) \<sqsubseteq> \<rho> \<squnion> F (\<rho> \<squnion> F (((\<lambda>\<rho>'. \<rho> \<squnion> F \<rho>') ^^ n) (to_bot \<rho>)))"
      by (rule join_mono[OF chain_compat_fjc chain_compat_fjc[of "Suc n", simplified] below_refl cont2monofunE[OF `cont F`]])
  qed 
  
  lemma rho_fjc: "\<rho> \<in> fix_join_compat \<rho> F"
    apply auto
    apply (subst fix_on_def, subst if_P[OF chain_fjc])
    apply (rule below_trans[OF _ is_ub_thelub[of _ 1, OF chain_fjc]])
    apply (simp del: funpow.simps(1))
    apply (rule join_above1)
    apply (rule fix_join_cond.induct[OF `fix_join_cond _ _`])
    apply assumption
    done

  lemma F_pres_compat'': "x \<in> fix_join_compat \<rho> F \<Longrightarrow> F x \<in> fix_join_compat \<rho> F" 
    apply auto
    apply (drule cont2monofunE[OF cont_F_fjc])
    apply (erule below_trans)
    apply (subst (1 2) fix_on_def, subst (1 2) if_P[OF chain_fjc])
    apply (subst cont2contlubE[OF cont_F_fjc chain_fjc])
    apply (subst lub_range_shift[symmetric, OF chain_fjc, of 1])
    apply (rule lub_mono[OF ch2ch_cont[OF cont_F_fjc chain_fjc] chain_shift[OF chain_fjc]])
    apply simp
    apply (rule join_above2[OF chain_compat_fjc])
    done

  lemma rho_F_compat_fjc: "x \<in> fix_join_compat \<rho> F \<Longrightarrow> compatible \<rho> (F x)"
    by (rule compat_fjc[OF rho_fjc F_pres_compat''])

  lemma F_closed_on_fjc: "closed_on (fix_join_compat \<rho> F) F"
    by (rule, rule F_pres_compat'')

  lemma closed_fjc: "x \<in> fix_join_compat \<rho> F \<Longrightarrow> \<rho> \<squnion> F x \<in> fix_join_compat \<rho> F"
    by (metis F_pres_compat'' rho_fjc join_fjc)

  lemma closed_on_fjc: "closed_on (fix_join_compat \<rho> F) (\<lambda> x. \<rho> \<squnion> F x)"
    by (rule closed_onI, rule closed_fjc)

  lemma cont_on_fjc: "cont_on (fix_join_compat \<rho> F) (\<lambda> x. \<rho> \<squnion> F x)"
    by (rule cont_on_join_fjc[OF const_closed_on[OF rho_fjc] F_closed_on_fjc cont_is_cont_on[OF cont_const] cont_is_cont_on[OF `cont F`]]) 

  lemma fix_on_cond_fjc:
    "fix_on_cond (fix_join_compat \<rho> F) (bottom_of (fix_join_compat \<rho> F)) (\<lambda>x. \<rho> \<squnion> F x)"
    apply (subst bottom_of_fjc)
    by (rule fix_on_condI[OF subpcpo_fjc bottom_of_fjc closed_on_fjc cont_on_fjc])

  lemma fix_on_fjc_ind:
    assumes "adm_on (fix_join_compat \<rho> F) P"
    assumes "P (bottom_of (fix_join_compat \<rho> F))"
    assumes "\<And> y. y \<in> fix_join_compat \<rho> F \<Longrightarrow> P y \<Longrightarrow> P (\<rho> \<squnion> F y)"
    shows "P (fix_on (fix_join_compat \<rho> F) (\<lambda> x. \<rho> \<squnion> F x))"
      by (rule fix_on_ind[OF fix_on_cond_fjc assms])

  lemma fix_on_fjc_eq:
    shows "fix_on (fix_join_compat \<rho> F) (\<lambda> x. \<rho> \<squnion> F x) = \<rho> \<squnion> F (fix_on (fix_join_compat \<rho> F) (\<lambda> x. \<rho> \<squnion> F x))"
    by (rule fix_on_eq[OF fix_on_cond_fjc])
end

subsubsection {* Continutiy of the fixed point of joins *}

lemma fix_on_join_cont_general:
  fixes F :: "'a::Bounded_Nonempty_Meet_cpo \<Rightarrow> 'a"
  assumes "subpcpo S'"
  assumes pcpo_i: "\<And> i. subpcpo (S i)"
  assumes down_closed: "\<And>x y. x \<in> S' \<Longrightarrow> y \<sqsubseteq> x \<Longrightarrow> y \<in> S'"
  assumes same_bottoms: "\<And> i j. bottom_of (S i) = bottom_of (S j)"
  assumes same_bottoms'[simp]: "\<And> i. bottom_of (S i) = bottom_of S'"
  assumes "chain Y"
  assumes "cont F"
  assumes compat: "\<And> i x. x \<in> S i \<Longrightarrow> compatible (Y i) (F x)"
  assumes compat': "\<And> x. x \<in> S' \<Longrightarrow> compatible (\<Squnion> i. Y i) (F x)"
  assumes cl: "\<And> i. closed_on (S i) (\<lambda>x. Y i \<squnion> F x)"
  assumes cl': "\<And> i. closed_on S' (\<lambda>x. (\<Squnion>i. Y i) \<squnion> F x)"

  shows "fix_on S' (\<lambda> x. (\<Squnion>i. Y i) \<squnion> F x) = (\<Squnion> i. (fix_on (S i) (\<lambda> x. Y i \<squnion> F x)))"
    (is "fix_on _ _ = Lub ?F")
proof-
  interpret subpcpo S' by fact

  have coF: "cont_on S' F" by (rule cont_is_cont_on[OF `cont F`])

  have co: "\<And> i. cont_on (S i) (\<lambda>x. Y i \<squnion> F x)"
  proof(rule subpcpo.cont_onI2[OF pcpo_i])
  case goal1 show ?case
    by (rule monofun_onI, erule (2) join_mono[OF compat compat below_refl cont2monofunE[OF `cont F`]])
  next
  case (goal2 i Y)
    hence "chain Y" by (metis chain_on_is_chain)
    show ?case
      apply (rule subst[OF cont2contlubE[OF `cont F` `chain Y`, symmetric]])
      apply (subst join_cont2[OF ch2ch_cont[OF `cont F` `chain Y`] compat[OF chain_on_is_on[OF goal2(1)]]])
      apply (rule below_refl)
    done
  qed

  have co': "cont_on S' (\<lambda>x. (\<Squnion> i. Y i) \<squnion> F x)"
  proof(rule cont_onI2)
  case goal1 show ?case
    by (rule monofun_onI, rule join_mono[OF compat' compat' below_refl cont2monofunE[OF `cont F`]])
  next
  case (goal2 Y)
    hence "chain Y" by (metis chain_on_is_chain)
    show ?case
      apply (rule subst[OF cont2contlubE[OF `cont F` `chain Y`, symmetric]])
      apply (subst join_cont2[OF ch2ch_cont[OF `cont F` `chain Y`] compat'[OF chain_on_is_on[OF goal2(1)]]])
      apply (rule below_refl)
    done
  qed

  have foc': "fix_on_cond S' (bottom_of S') (\<lambda>x. (\<Squnion>i. Y i) \<squnion> F x)"
    by (rule fix_on_condI[OF subpcpo_axioms refl cl' co'])
  have foc: "\<And> i. fix_on_cond (S i) (bottom_of (S i)) (\<lambda>x. Y i \<squnion> F x)"
    by (rule fix_on_condI[OF pcpo_i refl cl co])

  { fix i j
    have  "compatible (Y j) (F (?F i))"
    proof(cases "i \<le> j")
    case True show ?thesis
      apply (rule compatible_down_closed2)
      apply (rule compat[OF fix_on_there[OF foc]])
      apply (rule cont2monofunE[OF `cont F`])
      apply (rule fix_on_mono2[OF foc foc eq_imp_below[OF same_bottoms]])
      apply (erule (2) join_mono[OF compat compat chain_mono[OF `chain Y` True] cont2monofunE[OF `cont F`] ])
      done
   next
   case False
     hence "j \<le> i" by (metis nat_le_linear)
     thus ?thesis
       by (rule compatible_down_closed[OF compat[OF fix_on_there[OF foc]] chain_mono[OF `chain Y`]])
   qed
  } note compat'' = this

  have  "fix_on S' (\<lambda>x. (Lub Y) \<squnion> F x) \<in> S'"
    by (rule fix_on_there[OF foc'])
  moreover
  have "\<And> i. fix_on (S i) (\<lambda>x. Y i \<squnion> F x) \<sqsubseteq> fix_on S' (\<lambda>x. (Lub Y) \<squnion> F x)"
    apply (rule fix_on_mono2[OF foc foc'])
    apply simp      
    apply (erule (2) join_mono[OF
        compat
        compat'
        is_ub_thelub[OF `chain Y`]
        cont2monofunE[OF `cont F`]])
    done
  ultimately
  have F_in_S: "\<And> i. fix_on (S i) (\<lambda>x. Y i \<squnion> F x) \<in> S'"
    by (rule down_closed)

  have chF: "chain ?F"
    apply (rule chainI)
    apply (rule fix_on_mono2[OF foc foc])
    apply simp
    by (rule join_mono[OF compat compat chainE[OF `chain Y`] cont2monofunE[OF `cont F`]])
  have cho: "chain_on S' ?F"
    apply (rule chain_onI[OF _ F_in_S])
    apply (rule chainE[OF chF])
    done

  have c1: "\<And> j. chain (\<lambda>i. Y i \<squnion> F (?F j))"
    by (rule chainI, rule join_mono[OF compat'' compat'' chainE[OF `chain Y`] below_refl])
  have c2: "\<And> i. chain (\<lambda>j. Y i \<squnion> F (?F j))"
    by (rule chainI, rule join_mono[OF compat'' compat'' below_refl cont2monofunE[OF `cont F` chainE[OF chF]]])
  have c3: "chain (\<lambda>i. F (?F i))"
    by (rule ch2ch_cont[OF `cont F` chF])

  have "(\<Squnion> i. ?F i) \<in> S'"
    by (rule chain_on_lub_on[OF cho])
  moreover
  {
  have "(\<Squnion> i. Y i) \<squnion> F (\<Squnion> i. fix_on (S i) (\<lambda>x. Y i \<squnion> F x))
    = (\<Squnion> i. Y i) \<squnion> (\<Squnion> i. F (fix_on (S i) (\<lambda>x. Y i \<squnion> F x)))"
    by (subst cont_on2contlubE[OF coF cho], rule)
  also have " ... = (\<Squnion> i. Y i \<squnion> (\<Squnion> i. F (fix_on (S i) (\<lambda>x. Y i \<squnion> F x))))"
    by (rule join_cont1[OF `chain Y` admD[OF compatible_adm2 c3 compat'']])
  also have " ... = (\<Squnion> i j. Y i \<squnion> F (fix_on (S j) (\<lambda>x. Y j \<squnion> F x)))"
    by (subst join_cont2[OF c3 compat''], rule)
  also have " ... = (\<Squnion> i. Y i \<squnion> F (fix_on (S i) (\<lambda>x. Y i \<squnion> F x)))"
    by (rule diag_lub[OF c1 c2])
  also have " ... = (\<Squnion> i. fix_on (S i) (\<lambda>x. Y i \<squnion> F x))"
    by (subst fix_on_eq[symmetric, OF foc], rule)
  also note calculation
  }
  hence "(\<Squnion> i. Y i) \<squnion> F (\<Squnion> i. fix_on (S i) (\<lambda>x. Y i \<squnion> F x)) \<sqsubseteq> (\<Squnion> i. fix_on (S i) (\<lambda>x. Y i \<squnion> F x))"
    by (rule eq_imp_below)
  ultimately
  have "fix_on S' (\<lambda> x. (\<Squnion>i. Y i) \<squnion> F x) \<sqsubseteq> (\<Squnion> i. (fix_on (S i) (\<lambda> x. Y i \<squnion> F x)))"
    by (rule fix_on_least_below[OF foc'])
  moreover
  have  "(\<Squnion> i. (fix_on (S i) (\<lambda> x. Y i \<squnion> F x))) \<sqsubseteq> fix_on S' (\<lambda> x. (\<Squnion>i. Y i) \<squnion> F x)"
  proof (rule lub_below[OF chF])
    fix i
    show "(fix_on (S i) (\<lambda> x. Y i \<squnion> F x)) \<sqsubseteq> fix_on S' (\<lambda> x. (\<Squnion>i. Y i) \<squnion> F x)"
      apply (rule fix_on_mono2[OF foc foc' eq_imp_below[OF same_bottoms']])
      by (rule join_mono[OF compat compat' is_ub_thelub[OF `chain Y`] cont2monofunE[OF `cont F`]])
  qed
  finally
  show ?thesis.
qed

lemma fix_on_join_cont:
  fixes Y :: "nat \<Rightarrow> 'a::{Bounded_Nonempty_Meet_cpo, subpcpo_partition}"
  assumes "chain Y"
  assumes focj: "\<And>i. fix_join_cond (Y i) F"
  assumes focj': "fix_join_cond (\<Squnion> i. Y i) F"

  shows "fix_on (fix_join_compat (\<Squnion> i. Y i) F) (\<lambda> x. (\<Squnion>i. Y i) \<squnion> F x) = (\<Squnion> i. (fix_on (fix_join_compat (Y i) F) (\<lambda> x. Y i \<squnion> F x)))"
proof(rule fix_on_join_cont_general)
  fix i
  show "\<And> j. bottom_of (fix_join_compat (Y i) F) = bottom_of (fix_join_compat (Y j) F)"
    apply (simp add: bottom_of_fjc)
    by (metis linorder_linear unrelated[OF chain_mono[OF `chain Y`]])
  next
  fix i
  show "bottom_of (fix_join_compat (Y i) F) = bottom_of (fix_join_compat (\<Squnion> i. Y i) F)"
    apply (simp add: bottom_of_fjc)
    by (rule unrelated[OF is_ub_thelub[OF `chain Y`]])
  next
  show "cont F"
    by (rule cont_F_fjc[OF focj])
  next
  fix i x
  assume "x \<in> fix_join_compat (Y i) F"
  thus "compatible (Y i) (F x)"
    by (rule rho_F_compat_fjc[OF focj])
  next
  fix x
  assume "x \<in> fix_join_compat (\<Squnion> i. Y i) F"
  thus "compatible (\<Squnion> i. Y i) (F x)"
    by (rule rho_F_compat_fjc[OF focj'])
  next
  fix i
  show "closed_on (fix_join_compat (Y i) F) (\<lambda>x. Y i \<squnion> F x)"
    by (rule closed_on_fjc[OF focj])
  next
  fix i
  show "closed_on (fix_join_compat (\<Squnion> i. Y i) F) (\<lambda>x. (\<Squnion> i. Y i) \<squnion> F x)"
    by (rule closed_on_fjc[OF focj'])
  next
  fix x y
  assume "x \<in> fix_join_compat (\<Squnion> i. Y i) F" and "y \<sqsubseteq> x"
  thus "y \<in> fix_join_compat (\<Squnion> i. Y i) F"
    by (rule down_closed_fjc)
qed (intro subpcpo_fjc  rho_F_compat_fjc closed_on_fjc assms)+

end
