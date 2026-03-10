theory Majcons_Stratproof_Impossibility
  imports SWF_Impossibility_Automation
begin

text \<open>
  A somewhat technical lemma: If the swap distance of two rankings restricted to some subset $A$ is
  the same as the swap distance of the full rankings and additionally the elements of $A$ are
  all ranked above the elements not in $A$ in one of the rankings, then the second ranking
  must also have all elements not in $A$ ranked below those in $A$ and in the same order.
\<close>
lemma swap_dist_append_eq_swap_dist_filter_imp_eq:
  fixes xs ys zs
  defines "zs' \<equiv> (filter (\<lambda>x. x \<in> set xs) zs)"
  assumes "swap_dist (xs @ ys) zs \<le> swap_dist xs zs'"
  assumes wf: "distinct (xs @ ys)" "distinct zs" "set (xs @ ys) = set zs"
  shows   "zs = zs' @ ys"
proof -
  have "linorder_on (set zs) (of_ranking (xs @ ys))"
    by (rule linorder_of_ranking) (use assms in auto)
  moreover have "linorder_on (set zs) (of_ranking zs)"
    by (rule linorder_of_ranking) (use assms in auto)
  ultimately have *: "of_ranking (xs @ ys) a b = of_ranking zs a b" 
    if "a \<notin> set xs \<or> b \<notin> set xs" for a b
  proof (rule swap_dist_relation_restrict_eq_imp_eq)
    note \<open>swap_dist (xs @ ys) zs \<le> swap_dist xs zs'\<close>
    also have "swap_dist (xs @ ys) zs = swap_dist_relation (of_ranking (xs @ ys)) (of_ranking zs)"
      unfolding swap_dist_def using assms by auto
    also have "swap_dist xs zs' = swap_dist_relation (of_ranking xs) (of_ranking zs')"
      unfolding swap_dist_def using assms by auto
    also have "filter (\<lambda>x. x \<in> set xs) ys = []"
      unfolding filter_empty_conv using assms by auto
    hence "of_ranking xs = of_ranking (filter (\<lambda>x. x \<in> set xs) (xs @ ys))"
      by simp
    finally show "swap_dist_relation (restrict_relation (set xs) (of_ranking (xs @ ys))) 
                    (restrict_relation (set xs) (of_ranking zs)) \<ge>
                  swap_dist_relation (of_ranking (xs @ ys)) (of_ranking zs)"
      unfolding zs'_def of_ranking_filter by simp
  qed (use that in auto)

  have "of_ranking zs a b = of_ranking (zs' @ ys) a b" for a b
  proof (cases "a \<in> set xs \<and> b \<in> set xs")
    case True
    hence "of_ranking zs a b \<longleftrightarrow> of_ranking zs' a b"
      by (auto simp: zs'_def of_ranking_filter restrict_relation_def)
    also have "\<dots> \<longleftrightarrow> of_ranking (zs' @ ys) a b"
      using wf of_ranking_imp_in_set[of ys a b] True
      by (auto simp: of_ranking_append zs'_def)
    finally show ?thesis .
  next
    case False
    hence "of_ranking zs a b \<longleftrightarrow> of_ranking (xs @ ys) a b"
      by (intro * [symmetric]) auto
    also have "\<dots> \<longleftrightarrow> of_ranking (zs' @ ys) a b"
      using wf False of_ranking_imp_in_set[of xs a b] of_ranking_imp_in_set[of zs' a b]
      by (auto simp: of_ranking_append zs'_def)
    finally show ?thesis .
  qed
  hence "of_ranking zs = of_ranking (zs' @ ys)"
    by blast
  hence "ranking (of_ranking zs) = ranking (of_ranking (zs' @ ys))"
    by (rule arg_cong)
  also have "ranking (of_ranking zs) = zs"
    by (rule ranking_of_ranking) (use wf in auto)
  also have "ranking (of_ranking (zs' @ ys)) = zs' @ ys"
    by (rule ranking_of_ranking) (use wf in \<open>auto simp: zs'_def\<close>)
  finally show ?thesis .
qed


text \<open>
  We now turn to a setting where we have exactly 9 agents and 4 alternatives and an SWF that
  is majority consistent and satisfies our weak form of Kemeny strategyproofness where the 
  only manipulated profiles that have a linear majority relation are considered. We will, in
  particular, consider two specific profiles and show that there is only one admissible result
  ranking for them.

  When strengthening the strategyproofness assumption to full strategyproofness, these two results
  also turn out to be incompatible, yielding a contradiction.
\<close>
locale majcons_weak_kstratproof_swf_explicit_4_9 =
  majcons_weak_kstratproof_swf_explicit agents alts swf agents_list "[a,b,c,d]"
  for agents :: "'agent set" and alts :: "'alt set" and swf 
  and agents_list and a b c d +
  assumes card_agents_9 [simp]: "card agents = 9"
begin

lemma distinct_abcd [simp]:
  "a \<noteq> b" "a \<noteq> c" "a \<noteq> d" "b \<noteq> a" "b \<noteq> c" "b \<noteq> d" 
  "c \<noteq> a" "c \<noteq> b" "c \<noteq> d" "d \<noteq> a" "d \<noteq> b" "d \<noteq> c"
  using distinct_alts_list by auto

text \<open>
  We consider the following profile $R$. This profile does not have a linear majority relation,
  but many manipulations of it do.
\<close>
definition R :: "'alt list list" where
  "R = [[c,d,b,a],[b,a,d,c],[d,b,a,c],[c,b,a,d],
        [a,d,c,b],[c,a,d,b],[d,c,b,a],[d,a,b,c],[a,b,c,d]]"

lemma R_wf [simp]: "prefs_from_rankings_wf R"
  by (simp add: prefs_from_rankings_wf_def R_def)

text \<open>
  We perform five independent manipulations of $R$, all of which result in profiles with a
  transitive majority relation. This gives us five upper bounds about the swap distance between
  $f(R)$ and one other ranking each. It turns out that there is only one ranking that satisfies
  all of these constraints, and that ranking is $adcb$.

  Note also that the first four inequalities are all sharp.
\<close>
lemma swf'_R: "swf' R = [a,d,c,b]"
proof -
  note SP = majority_consistent_kemeny_strategyproof_swf'_aux

  have "swap_dist [c,d,b,a] (swf' R) \<le> swap_dist [c,d,b,a] [a,d,c,b]"
    by (rule SP[where i = 0 and zs = "[c,d,a,b]"])
       (simp_all add: R_def prefs_from_rankings_wf_def of_ranking_Cons)
  hence 1: "swap_dist [c,d,b,a] (swf' R) \<le> 4"
    by (simp add: swap_dist_conv_inversion_number insert_commute inversion_number_Cons)

  have "swap_dist [b,a,d,c] (swf' R) \<le> swap_dist [b,a,d,c] [a,d,c,b]"
    by (rule SP[where i = 1 and zs = "[a,b,d,c]"])
       (simp_all add: R_def prefs_from_rankings_wf_def of_ranking_Cons)
  hence 2: "swap_dist [b,a,d,c] (swf' R) \<le> 3"
    by (simp add: swap_dist_conv_inversion_number insert_commute inversion_number_Cons)

  have "swap_dist [d,b,a,c] (swf' R) \<le> swap_dist [d,b,a,c] [a,d,c,b]"
    by (rule SP[where i = 2 and zs = "[d,a,b,c]"])
       (simp_all add: R_def prefs_from_rankings_wf_def of_ranking_Cons)
  hence 3: "swap_dist [d,b,a,c] (swf' R) \<le> 3"
    by (simp add: swap_dist_conv_inversion_number insert_commute inversion_number_Cons)

  have "swap_dist [c,b,a,d] (swf' R) \<le> swap_dist [c,b,a,d] [a,d,c,b]"
    by (rule SP[where i = 3 and zs = "[c,a,b,d]"])
       (simp_all add: R_def prefs_from_rankings_wf_def of_ranking_Cons)
  hence 4: "swap_dist [c,b,a,d] (swf' R) \<le> 4"
    by (simp add: swap_dist_conv_inversion_number insert_commute inversion_number_Cons)

  have "swap_dist [a,d,c,b] (swf' R) \<le> swap_dist [a,d,c,b] [d,b,a,c]"
    by (rule SP[where i = 4 and zs = "[d,a,b,c]"])
       (simp_all add: R_def prefs_from_rankings_wf_def of_ranking_Cons)
  hence 5: "swap_dist [a,d,c,b] (swf' R) \<le> 3"
    by (simp add: swap_dist_conv_inversion_number insert_commute inversion_number_Cons)

  define constraints :: "('alt list \<times> nat) list" where
    "constraints = [([c,d,b,a],4), ([b,a,d,c],3), ([d,b,a,c],3), ([c,b,a,d],4), ([a,d,c,b],3)]"
  define P where "P = (\<lambda>ys. list_all (\<lambda>(xs,d). swap_dist xs ys \<le> d) constraints)"

  have "swf' R \<in> permutations_of_set alts"
    using swf'_wf[of R] mset_eq_alts_list_iff[of "swf' R"] alts_conv_alts_list
    by (simp add: permutations_of_set_def)
  moreover have "P (swf' R)"
    unfolding P_def using 1 2 3 4 5 by (simp add: constraints_def)
  ultimately have "swf' R \<in> Set.filter P (permutations_of_set alts)"
    by simp
  also have "permutations_of_set alts = set (permutations_of_set_list [a,b,c,d])"
    unfolding alts_conv_alts_list by (subst permutations_of_list) simp_all
  also have "Set.filter P \<dots> = {[a,d,c,b]}"
    by (simp add: P_def constraints_def permutations_of_set_list_def insert_commute
                  permutations_of_set_aux_list_Nil permutations_of_set_aux_list_Cons
                  Set_filter_insert swap_dist_conv_inversion_number inversion_number_Cons
             del: Set.filter_eq)
  finally show ?thesis
    by simp
qed


text \<open>
  We now consider a second profile, which differs from $R$ only by a manipulation of the
  third agent.
\<close>
definition S :: "'alt list list" where
  "S =  [[c,d,b,a],[b,a,d,c],[d,b,c,a],[c,b,a,d],[a,d,c,b],
         [c,a,d,b],[d,c,b,a],[d,a,b,c],[a,b,c,d]]"

lemma S_wf [simp]: "prefs_from_rankings_wf S"
  by (simp add: prefs_from_rankings_wf_def S_def)

text \<open>
  We similarly show that $f(S) = dcba$.
\<close>
lemma swf'_S: "swf' S = [d,c,b,a]"
proof -
  note SP = majority_consistent_kemeny_strategyproof_swf'_aux

  have "swap_dist [c,b,a,d] (swf' S) \<le> swap_dist [c,b,a,d] [d,c,b,a]"
    by (rule SP[where i = 3 and zs = "[c,b,d,a]"])
       (simp_all add: S_def prefs_from_rankings_wf_def of_ranking_Cons)
  hence 1: "swap_dist [c,b,a,d] (swf' S) \<le> 3"
    by (simp add: swap_dist_conv_inversion_number insert_commute inversion_number_Cons)

  have "swap_dist [a,d,c,b] (swf' S) \<le> swap_dist [a,d,c,b] [d,c,b,a]"
    by (rule SP[where i = 4 and zs = "[d,a,c,b]"])
       (simp_all add: S_def prefs_from_rankings_wf_def of_ranking_Cons)
  hence 2: "swap_dist [a,d,c,b] (swf' S) \<le> 3"
    by (simp add: swap_dist_conv_inversion_number insert_commute inversion_number_Cons)

  have "swap_dist [c,a,d,b] (swf' S) \<le> swap_dist [c,a,d,b] [d,c,b,a]"
    by (rule SP[where i = 5 and zs = "[c,d,a,b]"])
       (simp_all add: S_def prefs_from_rankings_wf_def of_ranking_Cons)
  hence 3: "swap_dist [c,a,d,b] (swf' S) \<le> 3"
    by (simp add: swap_dist_conv_inversion_number insert_commute inversion_number_Cons)

  have "swap_dist [b,a,d,c] (swf' S) \<le> swap_dist [b,a,d,c] [d,c,b,a]"
    by (rule SP[where i = 1 and zs = "[b,d,a,c]"])
       (simp_all add: S_def prefs_from_rankings_wf_def of_ranking_Cons)
  hence 4: "swap_dist [b,a,d,c] (swf' S) \<le> 4"
    by (simp add: swap_dist_conv_inversion_number insert_commute inversion_number_Cons)

  have "swap_dist [d,c,b,a] (swf' S) \<le> swap_dist [d,c,b,a] [c,a,d,b]"
    by (rule SP[where i = 6 and zs = "[c,d,a,b]"])
       (simp_all add: S_def prefs_from_rankings_wf_def of_ranking_Cons)
  hence 5: "swap_dist [d,c,b,a] (swf' S) \<le> 3"
    by (simp add: swap_dist_conv_inversion_number insert_commute inversion_number_Cons)

  define constraints :: "('alt list \<times> nat) list" where
    "constraints = [([c,b,a,d],3), ([a,d,c,b],3), ([c,a,d,b],3), ([b,a,d,c],4), ([d,c,b,a],3)]"
  define P where "P = (\<lambda>ys. list_all (\<lambda>(xs,d). swap_dist xs ys \<le> d) constraints)"

  have "swf' S \<in> permutations_of_set alts"
    using swf'_wf[of S] mset_eq_alts_list_iff[of "swf' S"] alts_conv_alts_list
    by (simp add: permutations_of_set_def)
  moreover have "P (swf' S)"
    unfolding P_def using 1 2 3 4 5 by (simp add: constraints_def)
  ultimately have "swf' S \<in> Set.filter P (permutations_of_set alts)"
    by simp
  also have "permutations_of_set alts = set (permutations_of_set_list [a,b,c,d])"
    unfolding alts_conv_alts_list by (subst permutations_of_list) simp_all
  also have "Set.filter P \<dots> = {[d,c,b,a]}"
    by (simp add: P_def constraints_def permutations_of_set_list_def insert_commute
                  permutations_of_set_aux_list_Nil permutations_of_set_aux_list_Cons
                  Set_filter_insert swap_dist_conv_inversion_number inversion_number_Cons
             del: Set.filter_eq)
  finally show ?thesis
    by simp
qed

end


text \<open>
  We use the argument outlined in the paper to derive the impossibility for 9 agents
  and ${\geq}\,4$ alternatives. We call the first four alternatives $a,b,c,d$ and treat the
  remaining ones as ``dummy alternatives'' in some fixed order. Agents will always list them as
  their least preferred alternatives in exactly that fixed order.

  The complication is that, since we do not have unanimity, the ranking returned by the SWF does 
  not have to respect this order or put them as less preferred than the `real' alternatives. 
  However, we can show that for the profiles we consider, the SWF indeed has to respect the order.
\<close>
context majcons_kstratproof_swf_explicit
begin

sublocale majcons_weak_kstratproof_swf_explicit agents alts swf agents_list alts_list ..

lemma contradiction_eq9_ge4_aux:
  assumes "card agents = 9" "card alts \<ge> 4"
  shows   False
proof -
  define a b c d where 
    "a = alts_list ! 0" and "b = alts_list ! 1" and "c = alts_list ! 2" and "d = alts_list ! 3"
  define dummy_alts where "dummy_alts = drop 4 alts_list"

  have alts_list_expand: "alts_list = a # b # c # d # dummy_alts"
    by (rule nth_equalityI)
       (use \<open>card alts \<ge> 4\<close>
        in  \<open>auto simp: a_def b_def c_def d_def dummy_alts_def nth_Cons eval_nat_numeral 
                  split: nat.splits\<close>)
  have mset_alts_list [simp]: "mset alts_list = {#a,b,c,d#} + mset dummy_alts"
    by (simp add: alts_list_expand)
  have distinct_abcd: "distinct [a,b,c,d]" 
   and abcd_not_in_dummy_alts: "{a,b,c,d} \<inter> set dummy_alts = {}"
   and "distinct dummy_alts"
    using distinct_alts_list unfolding alts_list_expand by auto

  interpret majority_consistent_weak_kstratproof_swf_restrict_alts
      agents alts swf dummy_alts "{a,b,c,d}"
    by unfold_locales
       (use distinct_abcd in \<open>simp_all add: alts_conv_alts_list mset_set_set distinct_alts_list\<close>)
  interpret swf_restrict_alts_explicit agents alts swf dummy_alts "{a,b,c,d}" 
              agents_list alts_list "[a,b,c,d]"
    by standard (simp_all add: alts_list_expand)
  interpret new: majcons_weak_kstratproof_swf_explicit_4_9 
      agents "{a,b,c,d}" swf_low agents_list a b c d
    by standard (use distinct_abcd \<open>card agents = 9\<close> in \<open>simp_all add: agents_list\<close>)

  define R S where "R = map extend new.R" and "S = map extend new.S"
  have R_wf: "prefs_from_rankings_wf R" and S_wf: "prefs_from_rankings_wf S"
    by (simp_all add: prefs_from_rankings_wf_def R_def new.R_def S_def new.S_def extend_def)

  text \<open>
    The swap distance inequalities we derived throughs strategyproofness before still hold after 
    adding the dummy alternatives. We only need one of them for each of $R$ and $S$.
  \<close>
  have swap_dist_swf'_R: "swap_dist (extend [c,d,b,a]) (swf' R) \<le> 4"
  proof -
    have "swap_dist (extend [c,d,b,a]) (swf' R) \<le> swap_dist (extend [c,d,b,a]) (extend [a,d,c,b])"
    proof (rule majority_consistent_kemeny_strategyproof_swf'
                  [OF R_wf, where i = 0 and zs = "extend [c,d,a,b]"])
      have "majority_rel_mset (mset (new.R[0 := [c,d,a,b]])) [a,d,c,b]"
        by (rule new.majority_rel_list_aux_imp_majority_rel_mset)
           (use distinct_abcd in \<open>simp_all add: new.R_def new.prefs_from_rankings_wf_def 
                                                add_mset_commute of_ranking_Cons\<close>)
      hence "majority_rel_mset (mset (map extend (new.R[0 := [c,d,a,b]]))) (extend [a,d,c,b])"
        by (subst majority_rel_mset_extend) (simp_all add: new.R_def new.prefs_from_rankings_wf_def)
      also have "map extend (new.R[0 := [c,d,a,b]]) = R[0 := extend [c,d,a,b]]"
        by (simp add: R_def new.R_def)
      finally show "majority_rel_mset (mset (R[0 := extend [c,d,a,b]])) (extend [a,d,c,b])" .
    qed (simp_all add: R_def new.R_def extend_def)
    also have "\<dots> = swap_dist [c,d,b,a] [a,d,c,b]"
      by (subst swap_dist_extend) auto
    also have "\<dots> = 4"
      using distinct_abcd
      by (simp add: swap_dist_conv_inversion_number insert_commute inversion_number_Cons)
    finally show ?thesis .
  qed

  have swap_dist_swf'_S: "swap_dist (extend [c,b,a,d]) (swf' S) \<le> 3"
  proof -
    have "swap_dist (extend [c,b,a,d]) (swf' S) \<le> swap_dist (extend [c,b,a,d]) (extend [d,c,b,a])"
    proof (rule majority_consistent_kemeny_strategyproof_swf'
                  [OF S_wf, where i = 3 and zs = "extend [c,b,d,a]"])
      have "majority_rel_mset (mset (new.S[3 := [c,b,d,a]])) [d,c,b,a]"
        by (rule new.majority_rel_list_aux_imp_majority_rel_mset)
           (use distinct_abcd in \<open>simp_all add: new.S_def new.prefs_from_rankings_wf_def 
                                                add_mset_commute of_ranking_Cons\<close>)
      hence "majority_rel_mset (mset (map extend (new.S[3 := [c,b,d,a]]))) (extend [d,c,b,a])"
        by (subst majority_rel_mset_extend) (simp_all add: new.S_def new.prefs_from_rankings_wf_def)
      also have "map extend (new.S[3 := [c,b,d,a]]) = S[3 := extend [c, b, d, a]]"
        by (simp add: S_def new.S_def)
      finally show "majority_rel_mset (mset (S[3 := extend [c, b, d, a]])) (extend [d, c, b, a])" .
    qed (simp_all add: S_def new.S_def extend_def)
    also have "\<dots> = swap_dist [c,b,a,d] [d,c,b,a]"
      by (subst swap_dist_extend) auto
    also have "\<dots> = 3"
      using distinct_abcd
      by (simp add: swap_dist_conv_inversion_number insert_commute inversion_number_Cons)
    finally show ?thesis .
  qed

  text \<open>
    Since we know that $R$ returns the ranking $adcb$ when restricted to four alternatives and this
    already has a swap distance of 3 to $cbad$, that means that all the dummy alternatives in the
    ranking returnd for $R$ must be in the desired position since they would only introduce
    additinal swap distance, i.e.\ $f(R) = \uparrow adcb$.
  \<close>
  have swf'_R: "swf' R = extend [a, d, c, b]"
  proof -
    have "new.swf' new.R = [a, d, c, b]"
      by (rule new.swf'_R)
    also have "new.swf' new.R = filter (\<lambda>x. x \<in> {a,b,c,d}) (swf' R)"
      using new_swf'_eq[OF new.R_wf] by (simp add: R_def)
    finally have restrict_swf'_R: "filter (\<lambda>x. x \<in> {a, b, c, d}) (swf' R) = [a, d, c, b]" .
  
    have "swf' R = filter (\<lambda>x. x \<in> set [c,d,b,a]) (swf' R) @ dummy_alts"
    proof (rule swap_dist_append_eq_swap_dist_filter_imp_eq)
      have "mset ([c,d,b,a] @ dummy_alts) = mset alts_list"
        by simp
      with distinct_alts_list show "distinct ([c,d,b,a] @ dummy_alts)"
        using mset_eq_imp_distinct_iff by blast
    next
      have *: "mset (swf' R) = mset_set alts"
        by (rule swf'_wf) (fact R_wf)
      from * show "distinct (swf' R)"
        by (metis alts_list mset_eq_alts_list_iff)
      have "mset ([c,d,b,a] @ dummy_alts) = mset alts_list"
        by simp
      with * show "set ([c,d,b,a] @ dummy_alts) = set (swf' R)"
        by (metis alts_list mset_eq_setD)
    next
      have "filter (\<lambda>x. x \<in> set [c,d,b,a]) (swf' R) = [a,d,c,b]"
        using restrict_swf'_R by (simp add: disj_ac)
      hence "swap_dist [c,d,b,a] (filter (\<lambda>x. x \<in> set [c,d,b,a]) (swf' R)) = 
             swap_dist [c,d,b,a] [a,d,c,b]"
        by (rule arg_cong)
      also have "\<dots> = 4"
        using distinct_abcd
        by (simp add: swap_dist_conv_inversion_number insert_commute eq_commute inversion_number_Cons)
      also have "4 \<ge> swap_dist ([c,d,b,a] @ dummy_alts) (swf' R)"
        using swap_dist_swf'_R by (simp add: extend_def)
      finally show "swap_dist ([c,d,b,a] @ dummy_alts) (swf' R) \<le>
                    swap_dist [c,d,b,a] (filter (\<lambda>x. x \<in> set [c,d,b,a]) (swf' R))" .
    qed
    also have "filter (\<lambda>x. x \<in> set [c,d,b,a]) (swf' R) = [a,d,c,b]"
      using restrict_swf'_R by (simp add: disj_ac)
    finally show "swf' R = extend [a, d, c, b]" by (simp add: extend_def)
  qed

  text \<open>
    And similarly for $S$.
  \<close>
  have swf'_S: "swf' S = extend [d, c, b, a]"
  proof -
    have "new.swf' new.S = [d, c, b, a]"
      by (rule new.swf'_S)
    also have "new.swf' new.S = filter (\<lambda>x. x \<in> {a,b,c,d}) (swf' S)"
      using new_swf'_eq[OF new.S_wf] by (simp add: S_def)
    finally have restrict_swf'_S: "filter (\<lambda>x. x \<in> {a, b, c, d}) (swf' S) = [d, c, b, a]" .
  
    have "swf' S = filter (\<lambda>x. x \<in> set [c,b,a,d]) (swf' S) @ dummy_alts"
    proof (rule swap_dist_append_eq_swap_dist_filter_imp_eq)
      have "mset ([c,b,a,d] @ dummy_alts) = mset alts_list"
        by simp
      with distinct_alts_list show "distinct ([c,b,a,d] @ dummy_alts)"
        using mset_eq_imp_distinct_iff by blast
    next
      have *: "mset (swf' S) = mset_set alts"
        by (rule swf'_wf) (fact S_wf)
      from * show "distinct (swf' S)"
        by (metis alts_list mset_eq_alts_list_iff)
      have "mset ([c,b,a,d] @ dummy_alts) = mset alts_list"
        by simp
      with * show "set ([c,b,a,d] @ dummy_alts) = set (swf' S)"
        by (metis alts_list mset_eq_setD)
    next
      have "filter (\<lambda>x. x \<in> set [c,b,a,d]) (swf' S) = [d,c,b,a]"
        using restrict_swf'_S by (simp add: disj_ac)
      hence "swap_dist [c,b,a,d] (filter (\<lambda>x. x \<in> set [c,b,a,d]) (swf' S)) = 
             swap_dist [c,b,a,d] [d,c,b,a]"
        by (rule arg_cong)
      also have "\<dots> = 3"
        using distinct_abcd
        by (simp add: swap_dist_conv_inversion_number insert_commute eq_commute inversion_number_Cons)
      also have "3 \<ge> swap_dist ([c,b,a,d] @ dummy_alts) (swf' S)"
        using swap_dist_swf'_S by (simp add: extend_def)
      finally show "swap_dist ([c,b,a,d] @ dummy_alts) (swf' S) \<le>
                    swap_dist [c,b,a,d] (filter (\<lambda>x. x \<in> set [c,b,a,d]) (swf' S))" .
    qed
    also have "filter (\<lambda>x. x \<in> set [c,b,a,d]) (swf' S) = [d,c,b,a]"
      using restrict_swf'_S by (simp add: disj_ac)
    finally show "swf' S = extend [d, c, b, a]"
      by (simp add: extend_def)
  qed

  text \<open>
    Finally, strategyproofness tells us that
    $\Delta(f(R), \uparrow dbac) \leq \Delta(f(S), \uparrow dbac)$.
    However, we also know that $f(R) = \uparrow adcb$ and $f(S) = \uparrow dcba$, leading to
    $3 = \Delta(f(R),\uparrow dbac) \leq 2 = \Delta(f(S),\uparrow dbac)$.
  \<close>
  have "swap_dist (extend [d,b,a,c]) (swf' R) \<le> swap_dist (extend [d,b,a,c]) (swf' S)"
    by (rule kemeny_strategyproof_swf'[where i = 2 and zs = "extend [d,b,c,a]"])
       (use R_wf in \<open>simp_all add: R_def S_def new.R_def new.S_def extend_def\<close>)
  also have "swf' R = extend [a,d,c,b]"
    by fact
  also have "swap_dist (extend [d,b,a,c]) (extend [a,d,c,b]) = swap_dist [d,b,a,c] [a,d,c,b]"
    by (rule swap_dist_extend) simp_all
  also have "\<dots> = 3"
    using distinct_abcd
    by (simp add: swap_dist_conv_inversion_number insert_commute inversion_number_Cons)
  also have "swf' S = extend [d,c,b,a]"
    by fact
  also have "swap_dist (extend [d,b,a,c]) (extend [d,c,b,a]) = swap_dist [d,b,a,c] [d,c,b,a]"
    by (rule swap_dist_extend) simp_all
  also have "\<dots> = 2"
    using distinct_abcd
    by (simp add: swap_dist_conv_inversion_number insert_commute inversion_number_Cons)
  finally show False
    by simp
qed

text \<open>
  Using agent cloning, we can lift the impossibility to any multiple of 9 agents. In particular,
  we can derive it for 18 agents.
\<close>
lemma contradiction_eq18_ge4_aux:
  assumes "card agents = 18" "card alts \<ge> 4"
  shows   False
proof -
  have "card agents \<ge> 9"
    using assms by simp
  then obtain agents' where agents': "agents' \<subseteq> agents" "card agents' = 9"
    using obtain_subset_with_card_n by metis
  obtain unclone where "cloning agents' agents unclone"
    using cloning_exists[of agents' agents] agents' assms by force
  interpret unclone: cloning agents' agents unclone by fact
  interpret swf_split_agents agents alts swf agents' unclone ..

  interpret new: majority_consistent_swf agents' alts swf_low
    by (rule majority_consistent_clone) unfold_locales
  interpret new: kemeny_strategyproof_swf agents' alts swf_low
    by (rule kemeny_strategyproof_clone) unfold_locales
  have "finite agents'"
    by (rule finite_subset[OF _ finite_agents]) (use agents' in auto)
  then obtain agents_list'
    where agents_list': "mset agents_list' = mset_set agents'"
    using ex_mset by blast
  interpret new: majcons_kstratproof_swf_explicit agents' alts swf_low agents_list' alts_list
    by unfold_locales (use agents_list' alts_list in auto)

  show False
    by (rule new.contradiction_eq9_ge4_aux) (use \<open>card agents' = 9\<close> assms in auto)
qed

text \<open>
  By adding $k$ agents together with $k$ `anti-clones' of these agents, we can lift the
  impossibility to $9 + 2k$ or $18 + 2k$ agents. This covers every $n\geq 9$ except for
  $n \in\{10,12,14,16\}$.
\<close>
lemma contradiction_geq9_ge4_aux:
  assumes "card agents \<in> {9, 11, 13, 15} \<union> {17..}" "card alts \<ge> 4"
  shows   False
proof -
  define k where "k = (card agents - (if even (card agents) then 18 else 9)) div 2"
  from assms have "card agents \<ge> (if even (card agents) then 18 else 9)"
    by auto
  hence k: "card agents = (if even (card agents) then 18 else 9) + 2 * k"
    unfolding k_def by auto

  have "k \<le> card agents"
    using k by auto
  then obtain agents1 where agents1: "agents1 \<subseteq> agents" "card agents1 = k"
    using k obtain_subset_with_card_n by metis
  have "k \<le> card (agents - agents1)"
    by (subst card_Diff_subset) (use agents1 finite_subset[OF agents1(1)] k in auto)
  then obtain agents2 where agents2: "agents2 \<subseteq> agents - agents1" "card agents2 = k"
    using k obtain_subset_with_card_n by metis
  have [simp]: "finite agents1" "finite agents2"
    by (rule finite_subset[of _ agents]; use agents1 agents2 in force)+
  interpret dummy_ord: linorder_on alts "of_ranking alts_list"
    by (rule linorder_of_ranking) (use alts_conv_alts_list distinct_alts_list in auto)

  interpret swf_reduce_agents_even agents alts swf agents1 agents2 "of_ranking alts_list"
  proof
    have "card (agents1 \<union> agents2) < card agents"
      by (subst card_Un_disjoint) (use agents1 agents2 k in \<open>auto split: if_splits\<close>)
    moreover have "agents1 \<union> agents2 \<subseteq> agents"
      using agents1 agents2 by blast
    ultimately show "agents1 \<union> agents2 \<subset> agents"
      by blast
  qed (use agents1 agents2 in auto)

  interpret new: majority_consistent_swf "agents - agents1 - agents2" alts swf_low
    by (rule majority_consistent_reduce) unfold_locales
  interpret new: kemeny_strategyproof_swf "agents - agents1 - agents2" alts swf_low
    by (rule kemeny_strategyproof_reduce) unfold_locales
  have "finite (agents - agents1 - agents2)"
    by (rule finite_subset[OF _ finite_agents]) auto
  then obtain agents_list'
    where agents_list': "mset agents_list' = mset_set (agents - agents1 - agents2)"
    using ex_mset by blast
  interpret new: majcons_kstratproof_swf_explicit 
      "agents - agents1 - agents2" alts swf_low agents_list' alts_list
    by unfold_locales (use agents_list' alts_list in auto)

  have "card (agents - agents1 - agents2) \<in> {9, 18}"
    using agents1 agents2 k by (simp add: card_Diff_subset split: if_splits)
  thus False
    using new.contradiction_eq9_ge4_aux new.contradiction_eq18_ge4_aux assms by auto
qed

end


text \<open>
  We get rid of the explicit lists of agents and alternatives.
\<close>
context majcons_kstratproof_swf
begin

lemma contradiction_geq9_ge4:
  assumes "card agents \<in> {9, 11, 13, 15} \<union> {17..}" "card alts \<ge> 4"
  shows   False
proof -
  obtain agents_list where "mset agents_list = mset_set agents"
    using ex_mset by blast
  obtain alts_list where "mset alts_list = mset_set alts"
    using ex_mset by blast
  interpret majcons_kstratproof_swf_explicit agents alts swf agents_list alts_list
    by standard fact+
  show ?thesis
    using contradiction_geq9_ge4_aux assms by simp
qed

end



text \<open>
  We use an imported SAT proof to show the case of $m = 4$, $n = 3$.
\<close>

external_file "sat_data/maj_profiles_4_3.xz"
external_file "sat_data/maj_4_3.grat.xz"
external_file "sat_data/maj_sp_4_4.xz"
external_file "sat_data/maj_4_4.grat.xz"

locale majcons_kstratproof_swf_explicit_4_3 =
  majcons_kstratproof_swf_explicit agents alts swf "[A1,A2,A3]" "[a,b,c,d]"
  for agents :: "'agent set" and alts :: "'alt set" and swf and A1 A2 A3 and a b c d
begin

local_setup \<open>fn lthy =>
  let 
    val params = {
      name = "maj_4_3",
      locale_thm = @{thm majcons_kstratproof_swf_explicit_axioms},
      profile_file = SOME \<^path>\<open>sat_data/maj_profiles_4_3.xz\<close>,
      sp_file = NONE,
      grat_file = \<^path>\<open>sat_data/maj_4_3.grat.xz\<close>
    }
    val thm =
      Goal.prove_future lthy [] [] \<^prop>\<open>False\<close>
        (fn {context, ...} => 
          HEADGOAL (resolve_tac context [Majcons_Stratproof_Impossibility.derive_false context params]))
  in
    Local_Theory.note ((\<^binding>\<open>contradiction\<close>, []), [thm]) lthy |> snd
  end
\<close>

end


locale majcons_kstratproof_swf_explicit_4_4 =
  majcons_kstratproof_swf_explicit agents alts swf "[A1,A2,A3,A4]" "[a,b,c,d]"
  for agents :: "'agent set" and alts :: "'alt set" and swf and A1 A2 A3 A4 and a b c d
begin

local_setup \<open>fn lthy =>
  let 
    val params = {
      name = "maj_4_4",
      locale_thm = @{thm majcons_kstratproof_swf_explicit_axioms},
      profile_file = NONE,
      sp_file = SOME \<^path>\<open>sat_data/maj_sp_4_4.xz\<close>,
      grat_file = \<^path>\<open>sat_data/maj_4_4.grat.xz\<close>
    }
    val thm =
      Goal.prove_future lthy [] [] \<^prop>\<open>False\<close>
        (fn {context, ...} =>
          HEADGOAL (resolve_tac context [Majcons_Stratproof_Impossibility.derive_false context params]))
  in
    Local_Theory.note ((\<^binding>\<open>contradiction\<close>, []), [thm]) lthy |> snd
  end
\<close>

end


context majcons_kstratproof_swf_explicit
begin

lemma contradiction_ge3_eq4:
  assumes "card agents \<ge> 3" "card alts = 4"
  shows   False
proof -
  from assms have "length alts_list = 4"
    by simp
  then obtain a b c d where alts_list_eq: "alts_list = [a, b, c, d]"
    by (auto simp: eval_nat_numeral length_Suc_conv)

  define k where "k = (card agents - (if even (card agents) then 4 else 3)) div 2"
  from assms have "card agents \<ge> (if even (card agents) then 4 else 3)"
    by auto
  hence k: "card agents = (if even (card agents) then 4 else 3) + 2 * k"
    unfolding k_def by auto

  have "k \<le> card agents"
    using k by auto
  then obtain agents1 where agents1: "agents1 \<subseteq> agents" "card agents1 = k"
    using k obtain_subset_with_card_n by metis
  have "k \<le> card (agents - agents1)"
    by (subst card_Diff_subset) (use agents1 finite_subset[OF agents1(1)] k in auto)
  then obtain agents2 where agents2: "agents2 \<subseteq> agents - agents1" "card agents2 = k"
    using k obtain_subset_with_card_n by metis
  have [simp]: "finite agents1" "finite agents2"
    by (rule finite_subset[of _ agents]; use agents1 agents2 in force)+
  interpret dummy_ord: linorder_on alts "of_ranking alts_list"
    by (rule linorder_of_ranking) (use alts_conv_alts_list distinct_alts_list in auto)

  interpret swf_reduce_agents_even agents alts swf agents1 agents2 "of_ranking alts_list"
  proof
    have "card (agents1 \<union> agents2) < card agents"
      by (subst card_Un_disjoint) (use agents1 agents2 k in \<open>auto split: if_splits\<close>)
    moreover have "agents1 \<union> agents2 \<subseteq> agents"
      using agents1 agents2 by blast
    ultimately show "agents1 \<union> agents2 \<subset> agents"
      by blast
  qed (use agents1 agents2 in auto)

  interpret new: majority_consistent_swf "agents - agents1 - agents2" alts swf_low
    by (rule majority_consistent_reduce) unfold_locales
  interpret new: kemeny_strategyproof_swf "agents - agents1 - agents2" alts swf_low
    by (rule kemeny_strategyproof_reduce) unfold_locales
  have "finite (agents - agents1 - agents2)"
    by (rule finite_subset[OF _ finite_agents]) auto
  define agents' where "agents' = agents - agents1 - agents2"
  then obtain agents_list'
    where agents_list': "mset agents_list' = mset_set agents'"
    using ex_mset by blast
  interpret new: majcons_kstratproof_swf_explicit 
      "agents - agents1 - agents2" alts swf_low agents_list' alts_list
    by unfold_locales (use agents_list' alts_list in \<open>auto simp: agents'_def\<close>)

  have "card agents' = 3 \<or> card agents' = 4"
    using agents1 agents2 k by (simp add: card_Diff_subset agents'_def split: if_splits)
  hence "length agents_list' = 3 \<or> length agents_list' = 4"
    using agents_list' by (metis size_mset size_mset_set)
  thus False
  proof
    assume "length agents_list' = 3"
    then obtain A1 A2 A3 where agents_list_eq: "agents_list' = [A1, A2, A3]"
      by (auto simp: eval_nat_numeral length_Suc_conv)
    interpret new2: majcons_kstratproof_swf_explicit_4_3 "agents - agents1 - agents2" 
                      alts swf_low A1 A2 A3 a b c d
    proof
      show "mset [A1, A2, A3] = mset_set (agents - agents1 - agents2)"
        using agents_list_eq new.agents_list by force
    qed (simp_all flip: agents_list alts_list add: agents_list_eq alts_list_eq)
    show False
      using new2.contradiction assms(1,2) by simp
  next
    assume "length agents_list' = 4"
    then obtain A1 A2 A3 A4 where agents_list_eq: "agents_list' = [A1, A2, A3, A4]"
      by (auto simp: eval_nat_numeral length_Suc_conv)
    interpret new2: majcons_kstratproof_swf_explicit_4_4 "agents - agents1 - agents2" 
                      alts swf_low A1 A2 A3 A4 a b c d
    proof
      show "mset [A1, A2, A3, A4] = mset_set (agents - agents1 - agents2)"
        using agents_list_eq new.agents_list by force
    qed (simp_all flip: agents_list alts_list add: agents_list_eq alts_list_eq)
    show False
      using new2.contradiction assms(1,2) by simp
  qed
qed

end


text \<open>
  We now have everything to put together the final impossibility theorem.
\<close>
theorem majcons_kstratproof_impossibility:
  assumes "(card alts = 4 \<and> card agents \<ge> 3) \<or>
           (card alts \<ge> 4 \<and> card agents \<in> {9, 11, 13, 15} \<union> {17..})"
  assumes "majority_consistent_swf agents alts swf"
  assumes "kemeny_strategyproof_swf agents alts swf"
  shows   False
  using assms(1)
proof 
  assume *: "card alts \<ge> 4 \<and> card agents \<in> {9, 11, 13, 15} \<union> {17..}"
  interpret majority_consistent_swf agents alts swf by fact
  interpret kemeny_strategyproof_swf agents alts swf by fact
  interpret majcons_kstratproof_swf agents alts swf ..
  show False
    using contradiction_geq9_ge4 * by simp
next
  assume *: "card alts = 4 \<and> card agents \<ge> 3"
  interpret majority_consistent_swf agents alts swf by fact
  interpret kemeny_strategyproof_swf agents alts swf by fact
  interpret majcons_kstratproof_swf agents alts swf ..

  obtain alts_list where alts_list: "mset alts_list = mset_set alts"
    using ex_mset by blast
  obtain agents_list where agents_list: "mset agents_list = mset_set agents"
    using ex_mset by blast
  interpret majcons_kstratproof_swf_explicit agents alts swf agents_list alts_list
    by unfold_locales (simp_all add: agents_list alts_list)
  show False
    using * contradiction_ge3_eq4 by auto
qed

end