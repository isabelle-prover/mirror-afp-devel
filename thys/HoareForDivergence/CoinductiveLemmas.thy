theory CoinductiveLemmas imports Coinductive.Coinductive_List begin

lemma lSup_lappend:
  "\<lbrakk>Complete_Partial_Order.chain lprefix A; A \<noteq> {}\<rbrakk>
    \<Longrightarrow> lSup (lappend xs ` A) = lappend xs (lSup A)"
  apply (induct xs; clarsimp)
   defer
   apply (subst image_image[symmetric, where f="\<lambda>x. LCons _ x"])
   apply (clarsimp simp: lSup_LCons)
  apply (clarsimp simp: ccpo.admissible_def)
  apply (rename_tac B)
  apply (case_tac "lfinite (lSup B)")
   defer
   apply (rule lprefix_antisym)
    apply (rule chain_lSup_lprefix)
     apply (rule chainI)
     apply (fastforce simp: lappend_inf)
    apply clarsimp
   apply (rule chain_lprefix_lSup)
    apply (rule chainI)
    apply (fastforce simp: lappend_inf)
   apply (fastforce simp: lappend_inf)
  apply (erule lfinite_rev_induct)
   apply clarsimp
  by (metis mcont_contD mcont_lappend2)

lemma lSup_lmap:
  "\<lbrakk>Complete_Partial_Order.chain lprefix A; A \<noteq> {}\<rbrakk>
    \<Longrightarrow> lSup ((lmap f) ` A) = lmap f (lSup A)"
  by (metis mcont_contD mcont_lmap)

lemma lSup_lconcat:
  "\<lbrakk>Complete_Partial_Order.chain lprefix A; A \<noteq> {}\<rbrakk>
    \<Longrightarrow> lSup (lconcat ` A) = lconcat (lSup A)"
  by (metis mcont_contD mcont_lconcat)

lemma cpo_llist_of_upt:
  "Complete_Partial_Order.chain lprefix {x. \<exists>i. x = llist_of [0..<i]}"
  apply (rule chainI)
  apply clarsimp
  apply (rename_tac i i')
  apply (case_tac "i \<le> i'")
   apply (simp (no_asm) add: prefix_def)
   apply (rule_tac x="[i..<i']" in exI)
  using le_Suc_ex upt_add_eq_append apply blast
  apply (simp add: not_le)
  apply (erule notE)
  apply (drule less_imp_le)
  apply (simp (no_asm) add: prefix_def)
  apply (rule_tac x="[i'..<i]" in exI)
  using le_Suc_ex upt_add_eq_append by blast

lemma iterates_Suc_is_lSup_upt:
  "iterates Suc 0 = lSup {x. \<exists>i. x = llist_of [0..<i]}"
proof (coinduct rule : llist.coinduct
      [where R="\<lambda>x y. ltl x = lmap Suc x \<and> ltl y = lmap Suc y \<and> lnull x = lnull y
                      \<and> lhd x = lhd y"])
  case Eq_llist
  then show ?case
   apply (rule conjI)
    apply (simp add: lmap_iterates)
   apply (subst lSup_lmap[symmetric, OF cpo_llist_of_upt])
    apply fastforce
   apply clarsimp
   apply (rule conjI)
    apply (rule arg_cong[where f=lSup])
    apply (rule equalityI; clarsimp simp: subset_iff image_def)
      apply (metis Suc_pred lmap_llist_of map_Suc_upt)
    apply (rename_tac i)
    apply (rule_tac x="llist_of [0..<Suc i]" in bexI)
     apply (metis ltl_llist_of map_Suc_upt tl_upt)
     apply fastforce
   apply (rule conjI)
    apply fastforce
   apply (simp add: lSup.code)
   apply (rule conjI; clarsimp)
     apply (metis lnull_llist_of neq0_conv not_less upt_eq_Nil_conv)
    apply (rename_tac i)
   apply (rule the_equality; clarsimp simp: image_def)
   apply (rule_tac x="llist_of [0..<i]" in bexI, clarsimp)
   apply fastforce
  done
qed simp

abbreviation (input) flat :: "'a list llist \<Rightarrow> 'a llist" where
  "flat xs \<equiv> lconcat (lmap llist_of xs)"

lemma flat_inf_llist_lSup:
  "flat (inf_llist f) = lSup {x. \<exists>i. x = llist_of (concat (map f [0..<i]))}"
  apply (clarsimp simp: Coinductive_List.inf_llist_def)
  apply (subst iterates_Suc_is_lSup_upt)
  apply clarsimp
  apply (subst lSup_lmap[symmetric, OF cpo_llist_of_upt])
   apply fastforce
  apply (clarsimp simp: image_def)
  apply (subst lSup_lmap[symmetric])
    apply (rule chainI)
    apply clarsimp
    apply (metis (mono_tags, lifting) chain_def cpo_llist_of_upt lprefix_llist_of map_mono_prefix
                                      mem_Collect_eq)
   apply fastforce
  apply (clarsimp simp add: lconcat_llist_of[symmetric])
  apply (subst lmap_llist_of[symmetric])
  apply (subst llist.map_comp[symmetric])
  apply (subst lSup_lconcat[symmetric])
    apply (rule chainI)
    apply clarsimp
    using cpo_llist_of_upt
    apply (metis (no_types, opaque_lifting) le_Suc_ex less_imp_add_positive map_mono_prefix
                                            not_less prefix_def upt_add_eq_append zero_le)
   apply fastforce
  apply (rule arg_cong[of _ _ lSup])
  apply (fastforce simp: image_def)
  done

lemma upper_subset_lSup_eq:
  "\<lbrakk>Complete_Partial_Order.chain lprefix B; A \<subseteq> B;
    \<forall>x\<in>B. \<exists>y\<in>A. lprefix x y\<rbrakk> \<Longrightarrow> lSup B = lSup A"
  apply (rule lprefix_antisym)
   apply (rule chain_lSup_lprefix, simp)
   apply (rename_tac xs)
   apply (drule_tac x=xs in bspec, simp)
   apply (meson chain_subset less_imp_le llist.lub_upper lprefix_trans)
  apply (rule chain_lSup_lprefix)
  using chain_subset apply blast
  using llist.lub_upper by blast

lemma lmap_iterates_id:
  "lmap (\<lambda>z. x) (iterates Suc 0) = iterates id x"
  apply coinduction
  apply (simp add: lmap_iterates[symmetric] llist.map_comp)
  done

end
