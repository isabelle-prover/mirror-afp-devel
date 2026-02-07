section \<open>Impossibility results\<close>
subsection \<open>Infrastructure for SAT import and export\<close>
theory SWF_Impossibility_Automation          
  imports SWF_Lowering SWF_Anonymous PAPP_Impossibility.SAT_Replay
begin

subsection \<open>Automation for computing topological sortings\<close>

definition topo_sorts_aux_step :: "('a \<times> 'a set) list \<Rightarrow> ('a \<times> 'b set) list \<Rightarrow> 'a list list" where
  "topo_sorts_aux_step rel rel' = 
     List.bind (map fst (filter (\<lambda>(_,ys). ys = {}) rel'))
     (\<lambda>x. map ((#) x) (topo_sorts_aux (map (\<lambda>(y,ys). (y, Set.filter (\<lambda>z. z \<noteq> x) ys))
     (filter (\<lambda>(y,_). y \<noteq> x) rel))))"

lemma topo_sorts_aux_step_simps:
  "topo_sorts_aux_step rel [] = []"
  "topo_sorts_aux_step rel ((x, insert y ys) # rel') = topo_sorts_aux_step rel rel'"
  "topo_sorts_aux_step rel ((x, {}) # rel') = 
     map ((#) x) (topo_sorts_aux (map (\<lambda>(y,ys). (y, Set.filter (\<lambda>z. z \<noteq> x) ys)) (filter (\<lambda>(y,_). y \<noteq> x) rel))) @
     topo_sorts_aux_step rel rel'"
  by (simp_all add: topo_sorts_aux_step_def)

lemma topo_sorts_aux_Cons':
  fixes x xs defines "rel \<equiv> x # xs"
  shows "topo_sorts_aux rel = topo_sorts_aux_step rel rel"
  unfolding topo_sorts_aux_step_def assms
  by (subst topo_sorts_aux_Cons; unfold map_prod_def id_def) (rule refl)

context
begin

qualified fun dom_set :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a set"  where
  "dom_set x [] = {}"
| "dom_set x (y # ys) = (if x = y then {} else insert y (dom_set x ys))"

qualified lemma dom_set_altdef:
  assumes "distinct r" "x \<in> set r"
  shows   "dom_set x r = {y. y \<succ>[of_ranking r] x}"
  using assms
  by (induction r)
     (force simp: strongly_preferred_def of_ranking_Cons of_ranking_imp_in_set)+

qualified definition unanimity :: "'a list \<Rightarrow> 'a list multiset \<Rightarrow> ('a \<times> 'a set) list" where
  "unanimity xs R = map (\<lambda>x. (x, \<Inter>r\<in>set_mset R. SWF_Impossibility_Automation.dom_set x r)) xs"

end



locale anonymous_unanimous_kemenysp_swf = 
  anonymous_swf agents alts swf +
  unanimous_swf agents alts swf +
  kemeny_strategyproof_swf agents alts swf
  for agents :: "'agent set" and alts :: "'alt set" and swf
begin

sublocale anonymous_unanimous_swf agents alts swf ..

sublocale anonymous_kemeny_strategyproof_swf agents alts swf ..

end


locale anonymous_unanimous_kemenysp_swf_explicit = anonymous_unanimous_kemenysp_swf agents alts swf
  for agents :: "'agent set" and alts :: "'alt set" and swf +
  fixes agent_card :: nat and alts_list :: "'alt list"
  assumes card_agents: "card agents = agent_card"
  assumes alts_list: "mset alts_list = mset_set alts"
begin

lemma distinct_alts_list: "distinct alts_list"
  using alts_list by (metis finite_alts mset_eq_mset_set_imp_distinct)

lemma alts_conv_alts_list: "alts = set alts_list"
  using alts_list by (metis finite_alts finite_set_mset_mset_set set_mset_mset)

lemma card_alts [simp]: "card alts = length alts_list"
  using alts_list by (metis size_mset size_mset_set)

fun (in -) expand_ranking :: "'a list \<Rightarrow> ('a \<times> 'a) list" where
  "expand_ranking [] = []"
| "expand_ranking (x # xs) = map (\<lambda>y. (y, x)) xs @ expand_ranking xs"

lemma (in -) set_expand_ranking:
  "distinct xs \<Longrightarrow> set (expand_ranking xs) = {(x,y). x \<noteq> y \<and> of_ranking xs x y}"
  by (induction xs) (auto simp: of_ranking_Cons)


definition allowed_results :: "'alt list multiset \<Rightarrow> 'alt list set" where
  "allowed_results Rs = set (topo_sorts_aux (SWF_Impossibility_Automation.unanimity alts_list Rs))"

lemmas eval_allowed_results =
  allowed_results_def topo_sorts_aux_Cons' Set_filter_insert_if SWF_Impossibility_Automation.dom_set.simps
  SWF_Impossibility_Automation.unanimity_def disj_ac topo_sorts_aux_Nil topo_sorts_aux_step_simps

lemma aswf'_in_all_rankings:
  assumes "is_apref_profile' R"
  defines "A \<equiv> set (topo_sorts_aux (map (\<lambda>x. (x, {})) alts_list))"
  shows   "aswf' R \<in> A"
proof -
  have "set (topo_sorts_aux (map (\<lambda>x. (x, {})) alts_list)) = topo_sorts alts (\<lambda>x y. False)"
  proof (subst set_topo_sorts_aux, goal_cases)
    case 3
    show ?case
      by (rule arg_cong2[of _ _ _ _ topo_sorts]) (auto simp: alts_conv_alts_list)
  qed (use distinct_alts_list in \<open>auto simp: o_def\<close>)
  also have "\<dots> = permutations_of_set alts"
    by (subst topo_sorts_correct) (auto simp: le_fun_def)
  finally have "A = permutations_of_set alts"
    unfolding A_def .
  with aswf'_wf[OF assms(1)] show ?thesis
    by simp
qed 

lemma aswf'_in_allowed_results:
  assumes "is_apref_profile' Rs"
  shows   "aswf' Rs \<in> allowed_results Rs"
proof -
  have "Rs \<noteq> {#}"
    using assms unfolding is_apref_profile'_def by force
  then obtain R where R: "R \<in># Rs"
    by auto
  then interpret R: linorder_on alts "of_ranking R"
    using assms by (auto intro!: linorder_of_ranking simp: is_apref_profile'_def permutations_of_set_def)

  note wf = is_apref_profile'_imp_is_apref_profile[OF assms]
  have "aswf' Rs \<in> ranking ` of_ranking ` topo_sorts alts (\<lambda>x y. \<forall>R\<in>#image_mset of_ranking Rs. R x y)"
    using unanimous_topo_sorts_Pareto_aswf[OF wf] unfolding aswf'_def by blast
  also have "\<dots> = (\<lambda>xs. xs) ` topo_sorts alts (\<lambda>x y. \<forall>R\<in>#image_mset of_ranking Rs. R x y)"
    unfolding image_image
  proof (intro image_cong refl)
    fix xs assume "xs \<in> topo_sorts alts (\<lambda>x y. \<forall>R\<in>#image_mset of_ranking Rs. R x y)"
    also have "\<dots> = {xs \<in> permutations_of_set alts. (\<lambda>x y. \<forall>R\<in>#image_mset of_ranking Rs. R x y) \<le> of_ranking xs}"
      by (subst topo_sorts_correct) (use is_apref_profile_unanimous_not_outside[OF wf] in auto)
    finally show "ranking (of_ranking xs) = xs"
      by (intro ranking_of_ranking) (auto simp: permutations_of_set_def)
  qed
  also have "topo_sorts alts (\<lambda>x y. \<forall>R\<in>#image_mset of_ranking Rs. R x y) =
             topo_sorts alts (\<lambda>x y. \<forall>R\<in>#image_mset of_ranking Rs. x \<noteq> y \<and> R x y)"
    by (rule topo_sorts_cong) auto
  also have "\<dots> = topo_sorts (set alts_list) (\<lambda>x y. \<forall>R\<in>#image_mset of_ranking Rs. x \<noteq> y \<and> R x y)"
    by (subst alts_conv_alts_list) simp_all
  also have "\<dots> = set (topo_sorts_aux (SWF_Impossibility_Automation.unanimity alts_list Rs))"
  proof (subst set_topo_sorts_aux, goal_cases)
    case 1
    thus ?case using distinct_alts_list
      by (simp add: SWF_Impossibility_Automation.unanimity_def o_def)
  next
    case (2 x ys)
    thus ?case using assms R.not_outside R.antisymmetric R unfolding is_apref_profile'_def
      by (fastforce simp: SWF_Impossibility_Automation.unanimity_def SWF_Impossibility_Automation.dom_set_altdef
            permutations_of_set_def alts_conv_alts_list strongly_preferred_def)
  next
    case 3
    show ?case
    proof (intro arg_cong2[of _ _ _ _ topo_sorts] ext, goal_cases)
      case (2 x y)
      have "(\<forall>R\<in>#image_mset of_ranking Rs. x \<noteq> y \<and> R x y) \<longleftrightarrow>
            (\<forall>R\<in>#Rs. x \<in> alts \<and> y \<in> SWF_Impossibility_Automation.dom_set x R)"
        unfolding set_image_mset ball_simps
      proof (intro ball_cong refl)
        fix S assume S: "S \<in># Rs"
        interpret S: linorder_on alts "of_ranking S" using assms S 
          by (auto simp: is_apref_profile'_def permutations_of_set_def intro!: linorder_of_ranking)
        have "distinct S" "set S = alts"
          using S assms by (auto simp: is_apref_profile'_def permutations_of_set_def)
        thus "(x \<noteq> y \<and> of_ranking S x y) = (x \<in> alts \<and> y \<in> SWF_Impossibility_Automation.dom_set x S)"
          using S.not_outside[of x y] S.antisymmetric[of x y]
          by (auto simp: SWF_Impossibility_Automation.dom_set_altdef strongly_preferred_def)
      qed
      also have "\<dots> \<longleftrightarrow> (\<exists>ys. (x, ys) \<in> set (SWF_Impossibility_Automation.unanimity alts_list Rs) \<and> y \<in> ys)"
        unfolding SWF_Impossibility_Automation.unanimity_def using R
        by (auto simp: image_iff simp flip: alts_conv_alts_list)
      finally show ?case .
    qed (auto simp: SWF_Impossibility_Automation.unanimity_def)
  qed
  also have "\<dots> = allowed_results Rs"
    unfolding allowed_results_def ..
  finally show ?thesis by simp
qed

lemma is_apref_profile'_iff:
  "is_apref_profile' Rs \<longleftrightarrow> (size Rs = agent_card \<and> (\<forall>R\<in>#Rs. mset R = mset alts_list))"
  unfolding is_apref_profile'_def card_agents alts_list
  by (subst mset_eq_mset_set_iff) simp_all

end



subsection \<open>Automation for strategyproofness\<close>

lemma (in anonymous_unanimous_kemenysp_swf_explicit) kemeny_strategyproof_aswf'_aux:
  assumes "is_apref_profile' R1" "is_apref_profile' R2"
  assumes "inversion_number S1' = d1" "inversion_number S2' = d2"
  assumes "map (index T) S1 = S1'" "map (index T) S2 = S2'"
  assumes R12: "add_mset T' R1 \<equiv> add_mset T R2"
  assumes "d2 < d1"
  shows   "aswf' R1 \<noteq> S1 \<or> aswf' R2 \<noteq> S2"
proof (rule ccontr)
  assume *: "\<not>(aswf' R1 \<noteq> S1 \<or> aswf' R2 \<noteq> S2)"
  hence S12: "S1 \<in> permutations_of_set alts" "S2 \<in> permutations_of_set alts"
    using assms(1,2) aswf'_wf by blast+
  have "T \<noteq> T'"
    using assms * by fastforce
  hence "T \<in># R1" using R12
    by (metis insert_noteq_member)
  have "T' \<in># R2"
    using R12 by (metis \<open>T \<noteq> T'\<close> insert_noteq_member)
  have "R1 - R2 = {#T#}"
    using R12 \<open>T \<in># R1\<close> \<open>T \<noteq> T'\<close> \<open>T' \<in># R2\<close>
          add_diff_cancel_left add_mset_remove_trivial[of T R2]
          add_mset_remove_trivial[of T' "R1 - {#T#}"]
          diff_union_swap insert_DiffM2[of T R1] insert_DiffM2[of T' R2] zero_diff
    by metis

  have T: "T \<in> permutations_of_set alts"
    using assms(1) \<open>T \<in># R1\<close> by (auto simp: is_apref_profile'_def)
  have "swap_dist T S1 = d1" "swap_dist T S2 = d2"
    by (subst swap_dist_conv_inversion_number;
        use S12 T assms in \<open>simp add: permutations_of_set_def\<close>; fail)+
  with assms * show False
    using kemeny_strategyproof_aswf'[of R1 R2 S2 S1] \<open>R1 - R2 = {#T#}\<close> by simp
qed

lemma (in anonymous_unanimous_kemenysp_swf_explicit) kemeny_strategyproof_aswf'_no_obtain_optimal:
  assumes "is_apref_profile' R" "is_apref_profile' R'" "add_mset S R' \<equiv> add_mset S' R"
  shows   "aswf' R = S \<or> aswf' R' \<noteq> S"
  using kemeny_strategyproof_aswf'_no_obtain_optimal[of R R' S S'] assms by simp


subsection \<open>Automation for majority consistency\<close>

fun majority_rel_mset_aux :: "'a list multiset \<Rightarrow> 'a list \<Rightarrow> bool" where
  "majority_rel_mset_aux Rs [] \<longleftrightarrow> True"
| "majority_rel_mset_aux Rs (x # xs) \<longleftrightarrow>
     (\<forall>y\<in>set xs. 2 * size (filter_mset (\<lambda>R. of_ranking R y x) Rs) > size Rs) \<and>
     majority_rel_mset_aux Rs xs"

fun majority_rel_list_aux :: "'a list list \<Rightarrow> 'a list \<Rightarrow> bool" where
  "majority_rel_list_aux Rs [] \<longleftrightarrow> True"
| "majority_rel_list_aux Rs (x # xs) \<longleftrightarrow>
     list_all (\<lambda>y. 2 * length (filter (\<lambda>R. of_ranking R y x) Rs) > length Rs) xs \<and>
     majority_rel_list_aux Rs xs"

lemma majority_rel_mset_aux_mset:
  "majority_rel_mset_aux (mset Rs) ys \<longleftrightarrow> majority_rel_list_aux Rs ys"
  by (induction ys) (simp_all add: list.pred_set flip: mset_filter)

lemma majority_rel_mset_aux_correct:
  assumes "\<And>R. R \<in># Rs \<Longrightarrow> distinct R \<and> set R = A" "Rs \<noteq> {#}" "distinct zs" "set zs \<subseteq> A"
  defines "Rs' \<equiv> image_mset of_ranking Rs"
  defines "M \<equiv> majority_mset Rs'"
  shows   "majority_rel_mset_aux Rs zs \<longleftrightarrow> 
             (\<forall>x\<in>set zs. \<forall>y\<in>set zs. x \<prec>[M] y \<longleftrightarrow> x \<prec>[of_ranking zs] y)"
  (is "_ \<longleftrightarrow> ?rhs zs")
  using assms(3,4)
proof (induction zs)
  case (Cons z zs)
  define P where "P = (\<lambda>zs x y. x \<prec>[M] y \<longleftrightarrow> x \<prec>[of_ranking zs] y)"
  have R: "linorder_on A R" if "R \<in># Rs'" for R
    using assms(1) that linorder_of_ranking unfolding Rs'_def by fastforce
  have R': "preorder_on A R" if "R \<in># Rs'" for R
    using R[OF that] linorder_on_def order_on_def by blast
  have *: "P (z # zs) z z"
    using Cons.prems majority_mset_refl[of Rs' A z] R' assms(2)
    unfolding P_def strongly_preferred_def M_def by (auto simp: of_ranking_Cons)
  have less_iff: "x \<prec>[M] y \<longleftrightarrow> size Rs' < 2 * size {#R \<in># Rs'. R x y#}"
    if "x \<in> A" "y \<in> A" "x \<noteq> y" for x y
    using strongly_preferred_majority_mset_iff_gt[of Rs' A, OF R] that assms(2)
    by (simp add: Rs'_def M_def strongly_preferred_def filter_mset_image_mset not_le)
    
  have "majority_rel_mset_aux Rs (z # zs) \<longleftrightarrow>
         (\<forall>y\<in>set zs. size Rs' < 2 * size {#R \<in># Rs'. R y z#}) \<and>
          majority_rel_mset_aux Rs zs"
    by (simp add: Rs'_def filter_mset_image_mset)
  also have "(\<forall>y\<in>set zs. size Rs' < 2 * size {#R \<in># Rs'. R y z#}) \<longleftrightarrow>
             (\<forall>y\<in>set zs. P (z # zs) y z)"
    by (intro ball_cong refl)
       (use less_iff Cons.prems in \<open>auto simp: P_def of_ranking_strongly_preferred_Cons_iff\<close>)
  also have "majority_rel_mset_aux Rs zs \<longleftrightarrow>
               (\<forall>x\<in>set zs. \<forall>y\<in>set zs. x \<prec>[M] y = x \<prec>[of_ranking zs] y)"
    by (rule Cons.IH) (use Cons.prems in auto)
  also have "\<dots> \<longleftrightarrow> (\<forall>x\<in>set zs. \<forall>y\<in>set zs. P zs x y)"
    unfolding P_def ..
  also have "\<dots> \<longleftrightarrow> (\<forall>x\<in>set zs. \<forall>y\<in>set zs. P (z # zs) x y)"
    using Cons.prems 
    by (intro ball_cong refl) (auto simp: P_def of_ranking_strongly_preferred_Cons_iff)
  also have "(\<forall>y\<in>set zs. P (z # zs) y z) \<longleftrightarrow> (\<forall>x\<in>set zs. P (z # zs) x z) \<and> (\<forall>x\<in>set zs. P (z # zs) z x)"
  proof (intro iffI conjI)
    assume *: "\<forall>y\<in>set zs. P (z # zs) y z"
    show "\<forall>y\<in>set zs. P (z # zs) z y"
    proof
      fix y assume y: "y \<in> set zs"
      have [simp]: "y \<noteq> z" "z \<noteq> y"
        using Cons.prems y by auto
      have "P (z # zs) y z"
        using y * by blast
      moreover have "y \<prec>[of_ranking (z # zs)] z"
        using Cons.prems y of_ranking_imp_in_set[of zs z y]
        by (auto simp: strongly_preferred_def of_ranking_Cons)
      ultimately have "y \<prec>[M] z"
        by (auto simp: P_def)
      hence "\<not>z \<prec>[M] y"
        by (auto simp: strongly_preferred_def)
      moreover have "\<not>z \<prec>[of_ranking (z # zs)] y"
        using Cons.prems y of_ranking_imp_in_set[of zs z y]
        by (auto simp: strongly_preferred_def of_ranking_Cons)
      ultimately show "P (z # zs) z y"
        by (auto simp: P_def)
    qed
  qed blast+
  also have "\<dots> \<and> (\<forall>x\<in>set zs. \<forall>y\<in>set zs. P (z # zs) x y) \<longleftrightarrow>
             (\<forall>x\<in>set (z#zs). \<forall>y\<in>set (z#zs). P (z # zs) x y)"
    unfolding list.set using * by blast
  finally show ?case unfolding P_def .
qed simp_all

lemma majority_rel_mset_aux_correct':
  assumes "\<And>R. R \<in># Rs \<Longrightarrow> distinct R \<and> set R = A" "Rs \<noteq> {#}"
  assumes "set S = A" "distinct S"
  assumes "majority_rel_mset_aux Rs S"
  shows   "majority_rel_mset Rs S"
proof -
  define Rs' where "Rs' = image_mset of_ranking Rs"
  define M where "M = majority_mset Rs'"
  have Rs': "linorder_on A R" if "R \<in># Rs'" for R
    using that assms unfolding Rs'_def by (auto intro: linorder_of_ranking)
  have Rs'': "preorder_on A R" if "R \<in># Rs'" for R
    using Rs'[OF that] linorder_on_def order_on_def by blast
  have "x \<in> A \<and> y \<in> A" if "M x y" for x y
    using majority_mset_not_outside[of Rs' x y A] that Rs'' unfolding M_def by blast
  moreover have "x \<in> A \<and> y \<in> A" if "of_ranking S x y" for x y
    using of_ranking_imp_in_set[OF that] assms by auto
  moreover have "\<forall>x\<in>A. \<forall>y\<in>A. x \<prec>[M] y \<longleftrightarrow> x \<prec>[of_ranking S] y"
    using majority_rel_mset_aux_correct[OF assms(1,2,4)] assms(3,5) unfolding M_def Rs'_def
    by blast
  hence "\<forall>x\<in>A. \<forall>y\<in>A. x \<preceq>[M] y \<longleftrightarrow> x \<preceq>[of_ranking S] y"
    unfolding strongly_preferred_def 
    by (metis M_def Rs'' Rs'_def assms(2,3,4) image_mset_is_empty_iff majority_mset_refl nle_le
              nth_index of_ranking_altdef)
  ultimately have "M = of_ranking S"
    by blast
  thus ?thesis
    unfolding majority_rel_mset_def using \<open>distinct S\<close> by (simp add: M_def Rs'_def)
qed


context social_welfare_function_explicit
begin 

lemma majority_rel_list_aux_imp_majority_rel_mset:
  assumes "prefs_from_rankings_wf R" "majority_rel_list_aux R ys" "mset ys = mset alts_list"
  shows   "majority_rel_mset (mset R) ys"
proof -
  have "distinct ys"
    using \<open>mset ys = _\<close> by (metis alts_list finite_alts mset_eq_mset_set_imp_distinct)
  have "set ys = alts"
    using \<open>mset ys = _\<close> by (metis alts_list finite_alts finite_set_mset_mset_set set_mset_mset)
  note ys = \<open>distinct ys\<close> \<open>set ys = alts\<close>
  show ?thesis
  proof (rule majority_rel_mset_aux_correct'[where A = alts])
    
    show "mset R \<noteq> {#}"
      using assms(1) agents_conv_agents_list unfolding prefs_from_rankings_wf_def by force
    show "distinct S \<and> set S = alts" if "S \<in># mset R" for S
      using that assms(1) by (auto simp: prefs_from_rankings_wf_def list.pred_set mset_eq_alts_list_iff)
  qed (use ys assms in \<open>simp_all add: majority_rel_mset_aux_mset\<close>)
qed

lemma majority_prefs_from_rankings_eq_of_ranking_aux:
  assumes "prefs_from_rankings_wf R" "majority_rel_list_aux R ys" "mset ys = mset alts_list"
  shows   "majority (prefs_from_rankings R) = of_ranking ys"
  using majority_rel_list_aux_imp_majority_rel_mset majority_prefs_from_rankings_eq_of_ranking assms
  by metis

end


lemma (in majcons_kstratproof_swf_explicit) majority_consistent_swf'_aux:
  assumes "prefs_from_rankings_wf xss" "mset ys = mset alts_list"
  assumes "majority_rel_list_aux xss ys"
  shows   "swf' xss = ys"
proof (rule majority_consistent_swf')
  show "majority_rel_mset (mset xss) ys"
  proof (rule majority_rel_mset_aux_correct')
    show "distinct R \<and> set R = alts" if "R \<in># mset xss" for R
      using assms(1) that
      by (auto simp: prefs_from_rankings_wf_def mset_eq_alts_list_iff list.pred_set)
  next
    show "majority_rel_mset_aux (mset xss) ys"
      using assms(3) by (subst majority_rel_mset_aux_mset)
  next
    show "mset xss \<noteq> {#}"
      using assms(1) unfolding prefs_from_rankings_wf_def by auto
  next
    show "set ys = alts"
      using assms(2) alts_conv_alts_list mset_eq_setD by blast
  next
    show "distinct ys"
      using assms(2) distinct_alts_list mset_eq_imp_distinct_iff by blast
  qed
qed fact+

lemma (in majcons_weak_kstratproof_swf_explicit) majority_consistent_kemeny_strategyproof_swf'_aux:
  assumes "prefs_from_rankings_wf R1" "i < card agents"
  assumes "mset zs = mset alts_list" "mset ys = mset alts_list"
  assumes "xs = R1 ! i" "majority_rel_list_aux (R1[i := zs]) ys"
  shows   "swap_dist xs (swf' R1) \<le> swap_dist xs ys"
  using majority_consistent_kemeny_strategyproof_swf' assms
  using majority_rel_list_aux_imp_majority_rel_mset prefs_from_rankings_wf_update by presburger


lemma permutations_of_set_aux_list_Nil: "permutations_of_set_aux_list acc [] = [acc]"
  by (subst permutations_of_set_aux_list.simps) simp_all

lemma permutations_of_set_aux_list_Cons:
  "permutations_of_set_aux_list acc (x#xs) = 
     permutations_of_set_aux_list (x # acc) xs @ List.bind xs
     (\<lambda>xa. permutations_of_set_aux_list (xa # acc) (if xa = x then xs else x # remove1 xa xs)) "
  by (subst permutations_of_set_aux_list.simps) simp_all


ML_file \<open>sat_problem.ML\<close>
ML_file \<open>swf_util.ML\<close>
ML_file \<open>anon_unan_stratproof_impossibility.ML\<close>
ML_file \<open>majcons_stratproof_impossibility.ML\<close>

end
