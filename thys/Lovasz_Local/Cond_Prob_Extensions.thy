(* Theory: Cond_Prob_Extensions
   Author: Chelsea Edmonds *)

section \<open>Conditional Probability Library Extensions \<close>

theory Cond_Prob_Extensions 
  imports 
    Prob_Events_Extras  
    Design_Theory.Multisets_Extras
begin

subsection \<open>Miscellaneous Set and List Lemmas \<close>

lemma nth_image_tl: 
  assumes "xs \<noteq> []"
  shows "nth xs ` {1..<length xs} = set(tl xs)"
proof -
  have "set (tl xs) = {(tl xs)!i | i. i < length (tl xs)}"
    using set_conv_nth by metis 
  then have "set (tl xs) = {xs! (Suc i) | i. i  < length xs - 1}"
    using nth_tl by fastforce 
  then have "set (tl xs) = {xs ! j | j. j > 0 \<and> j < length xs}"
    by (smt (verit, best) Collect_cong Suc_diff_1 Suc_less_eq assms length_greater_0_conv zero_less_Suc)
  thus ?thesis by auto
qed

lemma exists_list_card: 
  assumes "finite S"
  obtains xs where "set xs = S" and "length xs = card S"
  by (metis assms distinct_card finite_distinct_list)

lemma bij_betw_inter_empty: (* this is the only lemma needing the Multisets_Extras theory *)
  assumes "bij_betw f A B"
  assumes "A' \<subseteq> A"
  assumes "A'' \<subseteq> A"
  assumes "A' \<inter> A'' = {}"
  shows "f ` A' \<inter> f ` A'' = {}"
  by (metis assms(1) assms(2) assms(3) assms(4) bij_betw_inter_subsets image_empty)


lemma bij_betw_image_comp_eq: 
  assumes "bij_betw g T S"
  shows "(F \<circ> g) ` T = F ` S"
  using assms bij_betw_imp_surj_on by (metis image_comp) 

lemma prod_card_image_set_eq: 
  assumes "bij_betw f {0..<card S} S"
  assumes "finite S"
  shows "(\<Prod>i \<in> {n..<(card S)} . g (f i)) = (\<Prod>i \<in> f ` {n..<card S} . g i)"
proof (cases "n \<ge> card S")
  case True
  then show ?thesis by simp
next
  case False
  then show ?thesis using assms 
  proof (induct "card S" arbitrary: S)
    case 0
    then show ?case by auto
  next
    case (Suc x)
    then have nlt: "n < Suc x" by simp
    then have split: "{n..<Suc x} = {n..<x} \<union> {x}" by auto
    then have "f ` {n..<Suc x} = f ` ({n..< x} \<union> {x})" by simp
    then have fsplit: "f ` {n..<Suc x} = f ` {n..< x} \<union> {f x}"
      by simp 
    have "{n..<x} \<subseteq> {0..<card S}"
      using Suc(2)  by auto 
    moreover have "{x} \<subseteq> {0..<card S}" using Suc(2) by auto
    moreover have "{n..< x} \<inter> {x} = {}" by auto
    ultimately have finter: "f ` {n..< x} \<inter> {f x} = {}" using Suc.prems(2) Suc.prems(1) 
       bij_betw_inter_empty[of f "{0..<card S}" S "{n..< x}" "{x}"] by auto
    have "(\<Prod>i = n..<Suc x. g (f i)) = (\<Prod>i = n..<x. g (f i)) * g (f( x))" using nlt by simp
    moreover have "(\<Prod>x\<in>f ` {n..<Suc x}. g x) = (\<Prod>i\<in>f ` {n..< x}. g i) * g (f x)" using finter fsplit
      by (simp add: Groups.mult_ac(2))
    moreover have "(\<Prod>i\<in>f ` {n..< x}. g i) = (\<Prod>i = n..<x. g (f i))"
    proof -
      let ?S' = "f ` {0..<x}"
      have "{0..<x} \<subseteq> {0..<card S}" using Suc(2) by auto
      then have bij: "bij_betw f {0..<x} ?S'" using Suc.prems(2)
        using bij_betw_subset by blast 
      moreover have "card ?S' = x" using bij_betw_same_card[of f "{0..<x}" ?S'] bij by auto
      moreover have "finite ?S'" using finite_subset by auto 
      ultimately show ?thesis
        by (metis bij_betw_subset ivl_subset less_eq_nat.simps(1) order_refl prod.reindex_bij_betw)  
    qed 
    ultimately show ?case using Suc(2) by auto
  qed
qed

lemma set_take_distinct_elem_not: 
  assumes "distinct xs"
  assumes "i < length xs"
  shows "xs ! i \<notin> set (take i xs)"
  by (metis assms(1) assms(2) distinct_take id_take_nth_drop not_distinct_conv_prefix)

subsection \<open> Conditional Probability Basics \<close>
context prob_space
begin

text \<open>Abbreviation to mirror mathematical notations \<close>

abbreviation cond_prob_ev :: "'a set \<Rightarrow> 'a set \<Rightarrow> real" ("\<P>'(_ | _')")  where 
"\<P>(B | A) \<equiv>  \<P>(x in M. (x \<in> B) \<bar> (x \<in> A))"

lemma cond_prob_inter: "\<P>(B | A) = \<P>(\<omega> in M. (\<omega> \<in> B \<inter> A)) / \<P>(\<omega> in M. (\<omega> \<in> A))"
  using cond_prob_def by auto

lemma cond_prob_ev_def: 
  assumes "A \<in> events" "B \<in> events"
  shows "\<P>(B | A) = prob (A \<inter> B) / prob A"
proof -
  have a: "\<P>(B | A) = \<P>(\<omega> in M. (\<omega> \<in> B \<inter> A)) / \<P>(\<omega> in M. (\<omega> \<in> A))"
    using cond_prob_inter by auto
  also have "... = prob {w \<in> space M . w \<in> B \<inter> A} / prob {w \<in> space M . w \<in> A}"
    by auto
  finally show ?thesis using assms
    by (simp add: Collect_conj_eq a inf_commute)
qed

lemma measurable_in_ev:
  assumes "A \<in> events"
  shows "Measurable.pred M (\<lambda> x . x \<in> A)"
  using assms by auto

lemma measure_uniform_measure_eq_cond_prob_ev:
  assumes "A \<in> events" "B \<in> events"
  shows "\<P>(A | B) =\<P>(x in uniform_measure M {x\<in>space M. x \<in> B}. x \<in> A)"
  using assms measurable_in_ev measure_uniform_measure_eq_cond_prob by auto

lemma measure_uniform_measure_eq_cond_prob_ev2:
  assumes "A \<in> events" "B \<in> events"
  shows "\<P>(A | B) = measure (uniform_measure M {x\<in>space M. x \<in> B}) A"
  using measure_uniform_measure_eq_cond_prob_ev assms
  by (metis Int_def sets.Int_space_eq1 space_uniform_measure) 

lemma measure_uniform_measure_eq_cond_prob_ev3:
  assumes "A \<in> events" "B \<in> events"
  shows "\<P>(A | B) = measure (uniform_measure M B) A"
  using measure_uniform_measure_eq_cond_prob_ev assms  Int_def sets.Int_space_eq1 space_uniform_measure
  by metis (* Slow *)

lemma prob_space_cond_prob_uniform:
  assumes "prob ({x\<in>space M. Q x}) > 0"
  shows "prob_space (uniform_measure M {x\<in>space M. Q x})"
  using assms by (intro prob_space_uniform_measure) (simp_all add: emeasure_eq_measure)

lemma prob_space_cond_prob_event:
  assumes "prob B > 0"
  shows "prob_space (uniform_measure M B)"
  using assms by (intro prob_space_uniform_measure) (simp_all add: emeasure_eq_measure)

text\<open>Note this case shouldn't be used. Conditional probability should have > 0 assumption\<close>
lemma cond_prob_empty: "\<P>(B | {}) = 0" 
  using cond_prob_inter[of B "{}"] by auto

lemma cond_prob_space:  "\<P>(A | space M) = \<P>(w in M . w \<in> A)"
proof -
  have p1: "prob {\<omega> \<in> space M. \<omega> \<in> space M} = 1"
    by (simp add: prob_space) 
  have "\<And> w. w \<in> space M \<Longrightarrow> w \<in> A \<inter> (space M) \<longleftrightarrow> w \<in> A" by auto
  then have "prob {\<omega> \<in> space M. \<omega> \<in> A \<inter> space M} = \<P>(w in M . w \<in> A)"
    by meson 
  then show ?thesis using cond_prob_inter[of  A "space M"] p1 by auto
qed

lemma cond_prob_space_ev: assumes "A \<in> events" shows "\<P>(A | space M) = prob A"
  using cond_prob_space assms
  by (metis Int_commute Int_def measure_space_inter sets.top) 

lemma cond_prob_UNIV: "\<P>(A | UNIV) = \<P>(w in M . w \<in> A)"
proof -
  have p1: "prob {\<omega> \<in> space M. \<omega> \<in> UNIV} = 1"
    by (simp add: prob_space) 
  have "\<And> w. w \<in> space M \<Longrightarrow> w \<in> A \<inter> UNIV \<longleftrightarrow> w \<in> A" by auto
  then have "prob {\<omega> \<in> space M. \<omega> \<in> A \<inter> UNIV} = \<P>(w in M . w \<in> A)"
    by meson 
  then show ?thesis using cond_prob_inter[of A UNIV] p1 by auto
qed

lemma cond_prob_UNIV_ev: "A \<in> events \<Longrightarrow> \<P>(A | UNIV) = prob A"
  using cond_prob_UNIV 
  by (metis Int_commute Int_def measure_space_inter sets.top)

lemma cond_prob_neg: 
  assumes "A \<in> events" "B \<in> events"
  assumes "prob A >0"
  shows "\<P>((space M - B) | A) = 1 - \<P>(B | A)"
proof -
  have negB: "space M - B \<in> events" using assms by auto 
  have "prob ((space M - B) \<inter> A) = prob A - prob (B \<inter> A)"
    by (simp add: Diff_Int_distrib2 assms(1) assms(2) finite_measure_Diff sets.Int)
  then have "\<P>((space M - B) | A) = (prob A - prob (B \<inter> A))/prob A" 
    using cond_prob_ev_def[of A "space M - B"] assms negB by (simp add: Int_commute) 
  also have "... = ((prob A)/prob A) - ((prob (B \<inter> A))/prob A)" by (simp add: field_simps)
  also have "... = 1 - ((prob (B \<inter> A))/prob A)" using assms(3) by (simp add: field_simps)
  finally show "\<P>((space M - B) | A) = 1 - \<P>(B | A)" using cond_prob_ev_def[of A B] assms
    by (simp add: inf_commute) 
qed

subsection \<open>Bayes Theorem \<close>


lemma prob_intersect_A: 
  assumes "A \<in> events" "B \<in> events"
  shows "prob (A \<inter> B) = prob A * \<P>(B | A)"
  using cond_prob_ev_def assms apply simp
  by (metis Int_lower1 finite_measure_mono measure_le_0_iff)

lemma prob_intersect_B: 
  assumes "A \<in> events" "B \<in> events"
  shows "prob (A \<inter> B) = prob B * \<P>(A | B)"
  using cond_prob_ev_def assms 
  by (simp_all add: inf_commute)(metis Int_lower2 finite_measure_mono measure_le_0_iff)

theorem Bayes_theorem: 
  assumes "A \<in> events" "B \<in> events"
  shows "prob B * \<P>(A | B) = prob A * \<P>(B |A)" 
  using prob_intersect_A prob_intersect_B assms by simp

corollary Bayes_theorem_div: 
  assumes "A \<in> events" "B \<in> events"
  shows "\<P>(A | B) = (prob A * \<P>(B |A))/(prob B)"
  using assms Bayes_theorem
  by (metis cond_prob_ev_def prob_intersect_A) 

lemma cond_prob_dual_intersect: 
  assumes "A \<in> events" "B \<in> events" "C \<in> events"
  assumes "prob C \<noteq> 0"
  shows "\<P>(A | (B \<inter> C)) = \<P>(A \<inter> B | C)/ \<P>(B | C)" (is "?LHS = ?RHS")
proof - 
  have "B \<inter> C \<in> events" using assms by auto
  then have lhs: "?LHS = prob (A \<inter> B \<inter> C)/prob (B \<inter> C)" 
    using assms cond_prob_ev_def[of "B \<inter> C" "A"] inf_commute inf_left_commute  by (metis)
  have "A \<inter> B \<in> events" using assms by auto
  then have "\<P>(A \<inter> B | C) = prob (A \<inter> B \<inter> C) / prob C" 
    using assms cond_prob_ev_def[of "C" "A \<inter> B"] inf_commute by (metis)
  moreover have "\<P>(B | C) = prob (B \<inter> C)/prob C" using cond_prob_ev_def[of "C" "B"] assms inf_commute by metis
  ultimately have "?RHS = (prob (A \<inter> B \<inter> C) / prob C)/( prob (B \<inter> C)/prob C)"
    by simp
  also have "... = (prob (A \<inter> B \<inter> C) / prob C)*( prob (C)/prob (B \<inter> C))" by simp
  also have "... = prob (A \<inter> B \<inter> C)/prob (B\<inter> C)" using assms(4) by simp
  finally show ?thesis using lhs by simp
qed


lemma cond_prob_ev_double: 
  assumes "A \<in> events" "B \<in> events" "C \<in> events"
  assumes "prob C > 0"
  shows "\<P>(x in (uniform_measure M C). (x \<in> A) \<bar> (x \<in> B)) =  \<P>(A | (B \<inter> C))"
proof - 
  let ?M = "uniform_measure M C"
  interpret cps: prob_space "?M" using assms(4) prob_space_cond_prob_event by auto
  have probne: "prob C \<noteq> 0" using assms(4) by auto
  have ev: "cps.events = events" using sets_uniform_measure by auto
  have iev: "A \<inter> B \<in> events" using assms(1) assms(2) by simp
  have 0: "\<P>(x in (uniform_measure M C). (x \<in> A) \<bar> (x \<in> B)) = cps.cond_prob_ev A B" by simp
  also have 1: "... = (measure ?M (A \<inter> B))/(measure ?M B)" using cond_prob_ev_def assms(1) assms(2) ev
    by (metis Int_commute cps.cond_prob_ev_def)
  also have 2: "... = \<P>((A \<inter> B) | C)/(measure ?M B)" 
    using measure_uniform_measure_eq_cond_prob_ev3[of "A \<inter> B" "C"] assms(3) iev by auto
  also have 3: "... = \<P>((A \<inter> B) | C)/ \<P>(B | C)" using measure_uniform_measure_eq_cond_prob_ev3[of "B" "C"] assms(3) assms(2) by auto
  also have 4: "... = \<P>(A | (B \<inter> C))" 
    using cond_prob_dual_intersect[of "A" "B" "C"] assms(1) assms(2) assms(3) probne by presburger 
  finally show ?thesis using 1 2 3 4 by presburger
qed

lemma cond_prob_inter_set_lt: 
  assumes "A \<in> events" "B \<in> events" "AS \<subseteq> events"
  assumes "finite AS"
  shows "\<P>((A \<inter> (\<Inter>AS)) | B) \<le> \<P>(A|B)" (is "?LHS \<le> ?RHS")
using measure_uniform_measure_eq_cond_prob_ev finite_measure_mono 
proof (cases "AS = {}")
  case True
  then have "(A \<inter> (\<Inter>AS)) = A" by simp
  then show ?thesis by simp
next
  case False
  then have "(\<Inter>AS) \<in> events" using assms(3) assms(4) Inter_event_ss by simp
  then have "(A \<inter> (\<Inter>AS)) \<in> events" using assms by simp
  then have "?LHS = prob (A \<inter> (\<Inter>AS) \<inter> B)/prob B" 
    using assms cond_prob_ev_def[of "B" "(A \<inter> (\<Inter>AS))"] inf_commute by metis
  moreover have "prob (A \<inter> (\<Inter>AS) \<inter> B) \<le> prob (A \<inter> B)" using finite_measure_mono
    assms(1) inf_commute inf_left_commute by (metis assms(2) inf_sup_ord(1) sets.Int) 
  ultimately show ?thesis using cond_prob_ev_def[of "B" "A"]
    by (simp add: assms(1) assms(2) divide_right_mono inf_commute) 
qed

subsection \<open>Conditional Probability Multiplication Rule \<close>
text \<open>Many list and indexed variations of this lemma \<close>

lemma prob_cond_Inter_List:  
  assumes "xs \<noteq> []"
  assumes "\<And> A. A \<in> set xs \<Longrightarrow> A \<in> events"
  shows "prob (\<Inter>(set xs)) = prob (hd xs) * (\<Prod>i = 1..<(length xs) . 
    \<P>((xs ! i) | (\<Inter>(set (take i xs )))))"
  using assms(1) assms(2) 
proof (induct xs rule: rev_nonempty_induct)
  case (single x)
  then show ?case by auto
next
  case (snoc x xs)
  have "xs \<noteq> []"
    by (simp add: snoc.hyps(1)) 
  then have inev: "(\<Inter>(set xs)) \<in> events" using events_inter
    by (simp add: snoc.prems) 
  have len: "(length (xs @ [x])) = length xs + 1" by auto
  have last_p: "\<P>(x | (\<Inter>(set xs))) = 
    \<P>((xs @ [x]) ! length xs | \<Inter> (set (take (length xs) (xs @ [x]))))"
    by auto
  have "prob (\<Inter> (set (xs @ [x]))) = prob (x \<inter> (\<Inter>(set xs)))"
    by auto
  also have "... = prob (\<Inter>(set xs)) * \<P>(x | (\<Inter>(set xs)))" 
    using prob_intersect_B snoc.prems inev by simp 
  also have "... = prob (hd xs) * (\<Prod>i = 1..<length xs. \<P>(xs ! i | \<Inter> (set (take i xs)))) * 
      \<P>(x | (\<Inter>(set xs)))"
    using snoc.hyps snoc.prems by auto
  finally have "prob (\<Inter> (set (xs @ [x]))) = prob (hd (xs @[x])) * 
      (\<Prod>i = 1..<length xs. \<P>((xs @ [x]) ! i | \<Inter> (set (take i (xs @ [x]))))) *  \<P>(x | (\<Inter>(set xs)))" 
    using nth_append[of xs "[x]"] nth_take by (simp add: snoc.hyps(1)) 
  then show ?case using last_p by auto
qed

lemma prob_cond_Inter_index:  
  fixes n :: nat
  assumes "n > 0"
  assumes "F ` {0..<n} \<subseteq> events"
  shows "prob (\<Inter> (F `{0..<n} )) = prob (F 0) * (\<Prod>i \<in> {1..<n} . 
    \<P>(F i | (\<Inter> (F`{0..<i}))))"
proof -
  define xs where "xs \<equiv> map F [0..<n]"
  have "prob (\<Inter>(set xs)) = prob (hd xs) * (\<Prod>i = 1..<(length xs) . 
    \<P>((xs ! i) | (\<Inter>(set (take i xs )))))" using xs_def assms prob_cond_Inter_List[of xs] by auto
  then have "prob (\<Inter>(set xs)) = prob (hd xs) * (\<Prod>i \<in> {1..<n} . \<P>((xs ! i) | (\<Inter>(set (take i xs )))))" 
    using xs_def by auto
  moreover have "hd xs = F 0" 
    unfolding xs_def by (simp add: assms(1) hd_map) 
  moreover have "\<And> i. i \<in> {1..<n} \<Longrightarrow> F ` {0..<i} = set (take i xs )"
    by (metis atLeastLessThan_iff atLeastLessThan_upt image_set less_or_eq_imp_le plus_nat.add_0 
        take_map take_upt xs_def)
  ultimately show ?thesis using xs_def by auto
qed

lemma prob_cond_Inter_index_compl: 
  fixes n :: nat
  assumes "n > 0"
  assumes "F ` {0..<n} \<subseteq> events"
  shows "prob (\<Inter> x \<in> {0..<n} . space M - F x) = prob (space M - F 0) * (\<Prod>i \<in> {1..<n} . 
    \<P>(space M - F i | (\<Inter> j\<in> {0..<i}. space M - F j)))"
proof -
  define G where "G \<equiv> \<lambda> i. space M - F i"
  then have "G ` {0..<n} \<subseteq> events" using assms(2) by auto
  then show ?thesis using prob_cond_Inter_index[of n G] G_def
    using assms(1) by blast  
qed


lemma prob_cond_Inter_take_cond:
  assumes "xs \<noteq> []"
  assumes "set xs \<subseteq> events"
  assumes "S \<subseteq> events"
  assumes "S \<noteq> {}"
  assumes "finite S"
  assumes "prob (\<Inter>S) > 0"
  shows "\<P>((\<Inter>(set xs)) | (\<Inter> S)) = (\<Prod>i = 0..<(length xs) .  \<P>((xs ! i) | (\<Inter>(set (take i xs ) \<union> S))))"
proof -
  define M' where "M' = uniform_measure M (\<Inter>S)"
  interpret cps: prob_space M' using prob_space_cond_prob_event M'_def assms(6) by auto
  have len: "length xs > 0" using assms(1) by simp
  have cps_ev: "cps.events = events" using sets_uniform_measure M'_def by auto
  have sevents: "\<Inter>S \<in> events" using assms(3) assms(4) Inter_event_ss assms(5) by auto
  have fin: "finite (set xs)" by auto
  then have xevents: "\<Inter>(set xs) \<in> events" using assms(1) assms(2) Inter_event_ss by blast
  then have peq: "\<P>((\<Inter>(set xs)) | (\<Inter> S)) = cps.prob (\<Inter> (set xs))" 
    using measure_uniform_measure_eq_cond_prob_ev3[of "\<Inter>(set xs)" "\<Inter>S"] sevents M'_def
    by blast
  then have "cps.prob (\<Inter> (set xs)) = cps.prob (hd xs) * (\<Prod>i = 1..<(length xs) . 
    cps.cond_prob_ev (xs ! i) (\<Inter>(set (take i xs ))))" using assms cps.prob_cond_Inter_List cps_ev 
    by blast
  moreover have "cps.prob (hd xs) = \<P>((xs ! 0) | (\<Inter>(set (take 0 xs ) \<union> S)))"
  proof -
    have ev: "hd xs \<in> events" using assms(2) len by auto
    then have "cps.prob (hd xs) = \<P>(hd xs | \<Inter>S)" 
      using ev sevents measure_uniform_measure_eq_cond_prob_ev3[of "hd xs" "\<Inter>S"] M'_def by presburger
    then show ?thesis using len by (simp add: hd_conv_nth)
  qed
  moreover have "\<And>i. i > 0 \<Longrightarrow> i < length xs \<Longrightarrow> 
    cps.cond_prob_ev (xs ! i) (\<Inter>(set (take i xs ))) = \<P>((xs ! i) | (\<Inter>(set (take i xs ) \<union> S)))"
  proof -
    fix i assume igt: "i > 0" and ilt: "i <length xs"
    then have "set (take i xs) \<subseteq> events" using assms(2)
      by (meson set_take_subset subset_trans) 
    moreover have "set (take i xs) \<noteq> {}" using len igt ilt by auto
    ultimately have "(\<Inter>(set (take i xs ))) \<in> events"
      using Inter_event_ss fin by auto
    moreover have "xs ! i \<in> events" using assms(2)
      using nth_mem subset_iff igt ilt by blast
    moreover have "(\<Inter>(set (take i xs ) \<union> S)) = (\<Inter>(set (take i xs ))) \<inter> (\<Inter>S)"
      by (simp add: Inf_union_distrib) 
    ultimately show "cps.cond_prob_ev (xs ! i) (\<Inter>(set (take i xs ))) = \<P>((xs ! i) | (\<Inter>(set (take i xs ) \<union> S)))"
      using sevents cond_prob_ev_double[of "xs ! i" "(\<Inter>(set (take i xs )))" "\<Inter>S"] assms(6) M'_def by presburger 
  qed
  ultimately have eq: "cps.prob (\<Inter> (set xs)) = \<P>((xs ! 0) | (\<Inter>(set (take 0 xs ) \<union> S))) * (\<Prod>i \<in> {1..<(length xs)} . 
    \<P>((xs ! i) | (\<Inter>(set (take i xs ) \<union> S))))" by simp
  moreover have "{1..<length xs} = {0..<length xs} - {0}"
    by (simp add: atLeast1_lessThan_eq_remove0 lessThan_atLeast0)
  moreover have "finite {0..<length xs}" by auto
  moreover have "0 \<in> {0..<length xs}"by (simp add: assms(1)) 
  ultimately have "\<P>((xs ! 0) | (\<Inter>(set (take 0 xs ) \<union> S))) * (\<Prod>i \<in> {1..<(length xs)} . 
    \<P>((xs ! i) | (\<Inter>(set (take i xs ) \<union> S)))) = (\<Prod>i \<in> {0..<(length xs)} . 
    \<P>((xs ! i) | (\<Inter>(set (take i xs ) \<union> S))))" using prod.remove[of "{0..<length xs}" "0" "\<lambda> i. \<P>((xs ! i) | (\<Inter>(set (take i xs ) \<union> S)))"]
    by presburger
  then have "cps.prob (\<Inter> (set xs)) = (\<Prod>i \<in> {0..<(length xs)} . 
    \<P>((xs ! i) | (\<Inter>(set (take i xs ) \<union> S))))" using eq by simp
  then show ?thesis using peq by auto
qed

lemma prob_cond_Inter_index_cond_set:
  fixes n :: nat
  assumes "n > 0"
  assumes "finite E"
  assumes "E \<noteq> {}"
  assumes "E \<subseteq> events"
  assumes "F ` {0..<n} \<subseteq> events"
  assumes "prob (\<Inter>E) > 0"
  shows "\<P>((\<Inter>(F ` {0..<n})) | (\<Inter>E)) = (\<Prod>i \<in> {0..<n}.  \<P>(F i | (\<Inter>((F ` {0..<i}) \<union> E))))"
proof -
  define M' where "M' = uniform_measure M (\<Inter>E)"
  interpret cps: prob_space M' using prob_space_cond_prob_event M'_def assms(6) by auto
  have cps_ev: "cps.events = events" using sets_uniform_measure M'_def by auto
  have sevents: "(\<Inter>(E)) \<in> events" using assms(6) assms(2) assms(3) assms(4) Inter_event_ss by auto
  have fin: "finite (F ` {0..<n})" by auto
  then have xevents: "\<Inter>(F ` {0..<n}) \<in> events" using assms Inter_event_ss by auto
  then have peq: "\<P>((\<Inter>(F ` {0..<n})) | (\<Inter> E)) = cps.prob (\<Inter> (F ` {0..<n}))" 
    using measure_uniform_measure_eq_cond_prob_ev3[of "\<Inter>(F ` {0..<n})" "\<Inter>E"] sevents M'_def
    by blast
  moreover have "F `{0..<n} \<subseteq> cps.events" using cps_ev assms(5) by force 
  ultimately have "cps.prob (\<Inter> (F ` {0..<n})) = cps.prob (F 0) * (\<Prod>i = 1..<n . 
    cps.cond_prob_ev (F i) (\<Inter>(F ` {0..<i})))" 
    using assms(1) cps.prob_cond_Inter_index[of n F] by blast
  moreover have "cps.prob (F 0) = \<P>((F 0) | (\<Inter>E))"
  proof -
    have ev: "F 0 \<in> events" using assms(1) assms(5) by auto
    then show ?thesis 
      using ev sevents measure_uniform_measure_eq_cond_prob_ev3[of "F 0" "\<Inter>E"] M'_def by presburger
  qed
  moreover have "\<And>i. i > 0 \<Longrightarrow> i < n \<Longrightarrow> 
    cps.cond_prob_ev (F i) (\<Inter>(F ` {0..<i})) = \<P>((F i) | (\<Inter>((F ` {0..<i}) \<union> E)))"
  proof -
    fix i assume igt: "i > 0" and ilt: "i <n"
    then have "(\<Inter>(F ` {0..<i})) \<in> events"
      using assms subset_trans igt Inter_event_ss fin by auto
    moreover have "F i \<in> events" using assms 
      using subset_iff igt ilt by simp
    moreover have "(\<Inter>((F ` {0..<i}) \<union> (E))) = (\<Inter>((F ` {0..<i}))) \<inter> (\<Inter>(E))"
      by (simp add: Inf_union_distrib) 
    ultimately show "cps.cond_prob_ev (F i) (\<Inter>(F ` {0..<i})) = \<P>((F i) | (\<Inter>((F ` {0..<i}) \<union> E)))"
      using sevents cond_prob_ev_double[of "F i" "(\<Inter>((F ` {0..<i})))" "\<Inter>E"] assms M'_def by presburger 
  qed
  ultimately have eq: "cps.prob (\<Inter> (F ` {0..<n})) = \<P>((F 0) | (\<Inter>E)) * (\<Prod>i \<in> {1..<n} . 
    \<P>((F i) | (\<Inter>((F ` {0..<i}) \<union> E))))" by simp
  moreover have "{1..<n} = {0..<n} - {0}"
    by (simp add: atLeast1_lessThan_eq_remove0 lessThan_atLeast0)
  ultimately have "\<P>((F 0) | (\<Inter>E)) * (\<Prod>i \<in> {1..<n} .  \<P>((F i) | (\<Inter>((F ` {0..<i}) \<union> E)))) = 
      (\<Prod>i \<in> {0..<n} . \<P>((F i) | (\<Inter>((F ` {0..<i}) \<union> E))))" using assms(1) 
    prod.remove[of "{0..<n}" "0" "\<lambda> i. \<P>((F i) | (\<Inter>((F `{0..<i}) \<union> E)))"] by fastforce
  then show ?thesis using peq eq by auto
qed

lemma prob_cond_Inter_index_cond_compl_set:
  fixes n :: nat
  assumes "n > 0"
  assumes "finite E"
  assumes "E \<noteq> {}"
  assumes "E \<subseteq> events"
  assumes "F ` {0..<n} \<subseteq> events"
  assumes "prob (\<Inter>E) > 0"
  shows "\<P>((\<Inter>((-) (space M) ` F ` {0..<n})) | (\<Inter>E)) = 
    (\<Prod>i = 0..<n .  \<P>((space M - F i) | (\<Inter>((-) (space M) ` F ` {0..<i} \<union> E))))"
proof -
  define G where "G \<equiv> \<lambda> i. (space M - F i)"
  then have "G ` {0..<n} \<subseteq> events" using assms(5) by auto
  then have "\<P>((\<Inter>(G ` {0..<n})) | (\<Inter>E)) = (\<Prod>i \<in> {0..<n}.  \<P>(G i | (\<Inter>((G ` {0..<i}) \<union> E))))"
    using prob_cond_Inter_index_cond_set[of n E G] assms by blast
  moreover have "((-) (space M) ` F ` {0..<n}) = (G ` {0..<n})"  unfolding G_def by auto
  moreover have "\<And> i. i \<in> {0..<n} \<Longrightarrow> \<P>((space M - F i) | (\<Inter>((-) (space M) ` F ` {0..<i} \<union> E))) = 
    \<P>(G i | (\<Inter>((G ` {0..<i}) \<union> E)))" 
  proof -
    fix i assume iin: "i \<in> {0..<n}"
    have "(-) (space M) ` F ` {0..<i} =  G ` {0..<i}" unfolding G_def using iin by auto
    then show "\<P>((space M - F i) | (\<Inter>((-) (space M) ` F ` {0..<i} \<union> E))) = 
    \<P>(G i | (\<Inter>((G ` {0..<i}) \<union> E)))" unfolding G_def by auto
  qed
  ultimately show ?thesis  by auto
qed

lemma prob_cond_Inter_index_cond:
  fixes n :: nat
  assumes "n > 0"
  assumes "n < m"
  assumes "F ` {0..<m} \<subseteq> events"
  assumes "prob (\<Inter>j \<in> {n..<m}. F j) > 0"
  shows "\<P>((\<Inter>(F ` {0..<n})) | (\<Inter>j \<in>{n..<m} . F j)) = (\<Prod>i \<in> {0..<n}.  \<P>(F i | (\<Inter>((F ` {0..<i}) \<union> (F ` {n..<m})))))"
proof -
  let ?E = "F ` {n..<m}"
  have "F ` {0..<n} \<subseteq> events" using assms(2) assms(3) by auto
  moreover have "?E \<subseteq> events" using assms(2) assms(3) by auto
  moreover have "prob(\<Inter>?E) > 0" using assms(4) by simp
  moreover have "?E \<noteq> {}" using assms(2) by simp
  ultimately show ?thesis using prob_cond_Inter_index_cond_set[of n "?E" F] assms(1) by blast
qed


lemma prob_cond_Inter_index_cond_compl:
  fixes n :: nat
  assumes "n > 0"
  assumes "n < m"
  assumes "F ` {0..<m} \<subseteq> events"
  assumes "prob (\<Inter>j \<in> {n..<m}. F j) > 0"
  shows "\<P>((\<Inter>((-) (space M) ` F ` {0..<n})) | (\<Inter>( F ` {n..<m}))) = 
    (\<Prod>i = 0..<n .  \<P>((space M - F i) | (\<Inter>((-) (space M) ` F ` {0..<i} \<union> (F ` {n..<m})))))"
proof -
  define G where "G \<equiv> \<lambda> i. if (i < n) then (space M - F i) else F i"
  then have "G ` {0..<m} \<subseteq> events" using assms(3) by auto
  moreover have "prob (\<Inter>j \<in> {n..<m}. G j) > 0" using G_def assms(4) by simp
  ultimately have "\<P>((\<Inter>(G ` {0..<n})) | (\<Inter>( G ` {n..<m}))) = (\<Prod>i \<in> {0..<n}.  \<P>(G i | (\<Inter>((G ` {0..<i}) \<union> (G ` {n..<m})))))"
    using prob_cond_Inter_index_cond[of n m G] assms(1) assms(2) by blast
  moreover have "((-) (space M) ` F ` {0..<n}) = (G ` {0..<n})"  unfolding G_def by auto
  moreover have meq: "( F ` {n..<m}) = ( G ` {n..<m})" unfolding G_def by auto
  moreover have "\<And> i. i \<in> {0..<n} \<Longrightarrow> \<P>((space M - F i) | (\<Inter>((-) (space M) ` F ` {0..<i} \<union> (F ` {n..<m})))) = 
    \<P>(G i | (\<Inter>((G ` {0..<i}) \<union> (G ` {n..<m}))))" 
  proof -
    fix i assume iin: "i \<in> {0..<n}"
    then have "(space M - F i) = G i" unfolding G_def by auto
    moreover have "(-) (space M) ` F ` {0..<i} =  G ` {0..<i}" unfolding G_def using iin by auto
    ultimately show "\<P>((space M - F i) | (\<Inter>((-) (space M) ` F ` {0..<i} \<union> (F ` {n..<m})))) = 
    \<P>(G i | (\<Inter>((G ` {0..<i}) \<union> (G ` {n..<m}))))" using meq by auto
  qed
  ultimately show ?thesis  by auto
qed

lemma prob_cond_Inter_take_cond_neg:
  assumes "xs \<noteq> []"
  assumes "set xs \<subseteq> events"
  assumes "S \<subseteq> events"
  assumes "S \<noteq> {}"
  assumes "finite S"
  assumes "prob (\<Inter>S) > 0"
  shows "\<P>((\<Inter>((-) (space M) ` (set xs))) | (\<Inter> S)) = 
    (\<Prod>i = 0..<(length xs) .  \<P>((space M - xs ! i) | (\<Inter>((-) (space M) ` (set (take i xs )) \<union> S))))"
proof -
  define ys where "ys = map ((-) (space M)) xs"
  have set: "((-) (space M) ` (set xs)) = set (ys)"
    using ys_def by simp
  then have "set ys \<subseteq> events"
    by (metis assms(2) image_subset_iff sets.compl_sets subsetD)
  moreover have "ys \<noteq> []" using ys_def assms(1) by simp
  ultimately have "\<P>(\<Inter>(set ys) | (\<Inter>S)) = 
      (\<Prod>i = 0..<(length ys) .  \<P>((ys ! i) | (\<Inter>(set (take i ys ) \<union> S))))"
    using prob_cond_Inter_take_cond assms by auto
  moreover have len: "length ys = length xs" using ys_def by auto
  moreover have "\<And>i. i < length xs \<Longrightarrow> ys ! i = space M - xs ! i" using ys_def nth_map len by auto
  moreover have "\<And>i. i < length xs \<Longrightarrow> set (take i ys) = (-) (space M) ` set (take i xs)" 
    using ys_def take_map len by (metis set_map) 
  ultimately show ?thesis using set by auto
qed

lemma prob_cond_Inter_List_Index:  
  assumes "xs \<noteq> []"
  assumes "set xs \<subseteq> events"
  shows "prob (\<Inter>(set xs)) = prob (hd xs) * (\<Prod>i = 1..<(length xs) . 
    \<P>((xs ! i) | (\<Inter> j \<in> {0..<i} . xs ! j)))"
proof -
  have "\<And> i. i < length xs \<Longrightarrow> set (take i xs) = ((!) xs ` {0..<i})"
    by (metis nat_less_le nth_image)
  thus ?thesis using prob_cond_Inter_List[of xs] assms by auto
qed

lemma obtains_prob_cond_Inter_index: (* added obtains *)
  assumes " S \<noteq> {}"
  assumes "S \<subseteq> events"
  assumes "finite S"
  obtains xs where "set xs = S" and "length xs = card S" and 
    "prob (\<Inter>S) = prob (hd xs) * (\<Prod>i = 1..<(length xs) . \<P>((xs ! i) | (\<Inter> j \<in> {0..<i} . xs ! j)))"
  using assms prob_cond_Inter_List_Index exists_list_card 
  by (metis (no_types, lifting) set_empty2) 

lemma obtain_list_index: 
  assumes "bij_betw g {0..<card S} S"
  assumes "finite S"
  obtains xs where "set xs = S" and "\<And> i . i \<in> {0..<card S} \<Longrightarrow> g i = xs ! i" and "distinct xs"
proof -
  let ?xs = "map g [0..<card S]" 
  have seq: "g ` {0..<card S} = S" using assms(1)
    by (simp add: bij_betw_imp_surj_on) 
  then have set_eq: "set ?xs = S"
    by simp 
  moreover have "\<And> i . i \<in> {0..<card S} \<Longrightarrow> g i = ?xs ! i" 
    by auto
  moreover have leneq: "length ?xs = card S" using seq by auto
  moreover have "distinct ?xs" using set_eq leneq
    by (simp add: card_distinct) 
  ultimately show ?thesis
    using that by blast 
qed

lemma prob_cond_inter_fn:  
  assumes "bij_betw g {0..<card S} S"
  assumes "finite S"
  assumes "S \<noteq> {}"
  assumes "S \<subseteq> events"
  shows "prob (\<Inter>S) = prob (g 0) * (\<Prod>i \<in> {1..<(card S)} . \<P>(g i | (\<Inter>(g ` {0..<i}))))"
proof -
  obtain xs where seq: "set xs = S" and geq: "\<And> i . i \<in> {0..<card S} \<Longrightarrow> g i = xs ! i" and "distinct xs"
    using obtain_list_index assms by auto
  then have len:  "length xs = card S" by (metis distinct_card) 
  then have "prob (\<Inter>S) = prob (hd xs) * (\<Prod>i \<in> {1..<(length xs)} . \<P>((xs ! i) | (\<Inter> j \<in> {0..<i} . xs ! j)))"
    using prob_cond_Inter_List_Index[of xs] assms(3) assms(4) seq by auto
  then have "prob (\<Inter>S) = prob (hd xs) * (\<Prod>i \<in> {1..<card S} . \<P>(g i | (\<Inter> j \<in> {0..<i} . g j)))"
    using geq len by auto
  moreover have "hd xs = g 0" 
  proof -
    have "length xs > 0" using seq assms(3) by auto 
    then have "hd xs = xs ! 0"
      by (simp add: hd_conv_nth) 
    then show ?thesis using geq len
      using \<open>0 < length xs\<close> by auto 
  qed
  ultimately show ?thesis by simp
qed

lemma prob_cond_inter_obtain_fn: 
  assumes " S \<noteq> {}"
  assumes "S \<subseteq> events"
  assumes "finite S"
  obtains f where "bij_betw f {0..<card S} S"  and 
    "prob (\<Inter>S) = prob (f 0) * (\<Prod>i \<in> {1..<(card S)} . \<P>(f i | (\<Inter>(f ` {0..<i}))))"
proof -
  obtain f where "bij_betw f {0..<card S} S"
    using assms(3) ex_bij_betw_nat_finite by blast 
  then show ?thesis using that prob_cond_inter_fn assms by auto
qed 


lemma prob_cond_inter_obtain_fn_compl: 
  assumes " S \<noteq> {}"
  assumes "S \<subseteq> events"
  assumes "finite S"
  obtains f where "bij_betw f {0..<card S} S" and "prob (\<Inter>((-) (space M) ` S)) = 
     prob (space M - f 0) * (\<Prod>i \<in> {1..<(card S)} . \<P>(space M - f i | (\<Inter>((-) (space M) ` f ` {0..<i}))))"
proof -
  let ?c = "(-) (space M)"
  obtain f where bb: "bij_betw f {0..<card S} S"
    using assms(3) ex_bij_betw_nat_finite by blast 
  moreover have bij: "bij_betw ?c S ((-) (space M) ` S)"
    using bij_betw_compl_sets_rev assms(2) by auto
  ultimately have "bij_betw (?c \<circ> f) {0..<card S} (?c ` S)"
    using bij_betw_comp_iff by blast 
  moreover have "?c ` S \<noteq> {}" using assms(1) by auto
  moreover have "finite (?c ` S )" using assms(3) by auto
  moreover have "?c ` S \<subseteq> events" using assms(2) by auto
  moreover have "card S = card (?c ` S)" using bij
    by (simp add: bij_betw_same_card)  
  ultimately have "prob (\<Inter>(?c ` S)) = prob ((?c \<circ> f) 0) * 
    (\<Prod>i \<in> {1..<(card S)} . \<P>((?c \<circ> f) i | (\<Inter>((?c \<circ> f) ` {0..<i}))))"
    using prob_cond_inter_fn[of "(?c \<circ> f)" "(?c ` S)"] by auto
  then have "prob (\<Inter>(?c ` S)) = prob (space M - (f 0)) * 
    (\<Prod>i \<in> {1..<(card S)} . \<P>(space M -  (f i) | (\<Inter>((?c \<circ> f) ` {0..<i}))))" by simp
  then show ?thesis using that bb by simp
qed 

lemma prob_cond_Inter_index_cond_fn:
  assumes "I \<noteq> {}"
  assumes "finite I"
  assumes "finite E"
  assumes "E \<noteq> {}"
  assumes "E \<subseteq> events"
  assumes "F ` I \<subseteq> events"
  assumes "prob (\<Inter>E) > 0"
  assumes bb: "bij_betw g {0..<card I} I"
  shows "\<P>((\<Inter>(F ` g ` {0..<card I})) | (\<Inter>E)) = 
    (\<Prod>i \<in> {0..<card I}.  \<P>(F (g i) | (\<Inter>((F ` g` {0..<i}) \<union> E))))"
proof -
  let ?n = "card I"
  have eq: "F ` I = (F \<circ> g) ` {0..<card I}" using bij_betw_image_comp_eq bb  by metis
  moreover have "0 < ?n" using assms(1) assms(2) by auto
  ultimately have "\<P>(\<Inter> ((F \<circ> g) ` {0..<card I}) | \<Inter> E) = 
      (\<Prod>i = 0..<?n. \<P>(F (g i) | \<Inter> ((F \<circ> g) ` {0..<i} \<union> E)))"
    using prob_cond_Inter_index_cond_set[of ?n E "(F \<circ> g)"] assms(3) assms(4) assms(5) assms(6) 
      assms(7) by auto
  moreover have "\<And> i. i \<in> {0..<?n} \<Longrightarrow> (F \<circ> g) ` {0..<i} = F ` g ` {0..<i}" using image_comp by auto
  ultimately have "\<P>(\<Inter> (F ` g ` {0..<card I}) | \<Inter> E) = (\<Prod>i = 0..<?n. \<P>(F (g i) | \<Inter> (F ` g ` {0..<i} \<union> E)))" 
    using image_comp[of F g "{0..<card I}"] by auto
  then show ?thesis using eq bb assms by blast
qed

lemma prob_cond_Inter_index_cond_obtains:
  assumes "I \<noteq> {}"
  assumes "finite I"
  assumes "finite E"
  assumes "E \<noteq> {}"
  assumes "E \<subseteq> events"
  assumes "F ` I \<subseteq> events"
  assumes "prob (\<Inter>E) > 0"
  obtains g where "bij_betw g {0..<card I} I" and  "\<P>((\<Inter>(F ` g ` {0..<card I})) | (\<Inter>E)) = 
    (\<Prod>i \<in> {0..<card I}.  \<P>(F (g i) | (\<Inter>((F ` g` {0..<i}) \<union> E))))"
proof -
  obtain g where bb: "bij_betw g {0..<card I} I" using assms(2) ex_bij_betw_nat_finite by auto
  then show thesis using assms prob_cond_Inter_index_cond_fn[of I E F g] that by blast
qed

lemma prob_cond_Inter_index_cond_compl_fn:
  assumes "I \<noteq> {}"
  assumes "finite I"
  assumes "finite E"
  assumes "E \<noteq> {}"
  assumes "E \<subseteq> events"
  assumes "F ` I \<subseteq> events"
  assumes "prob (\<Inter>E) > 0"
  assumes bb: "bij_betw g {0..<card I} I"
  shows "\<P>((\<Inter>Aj \<in> I . space M - F Aj) | (\<Inter>E)) = 
    (\<Prod>i \<in> {0..<card I}.  \<P>(space M - F (g i) | (\<Inter>(((\<lambda>Aj. space M - F Aj) ` g ` {0..<i}) \<union> E))))"
proof -
  let ?n = "card I"
  let ?G = "\<lambda> i. space M - F i"
  have eq: "?G ` I = (?G \<circ> g) ` {0..<card I}" using bij_betw_image_comp_eq bb by metis
  then have "(?G \<circ> g) ` {0..<card I}  \<subseteq> events" using assms(5)
    by (metis assms(6) compl_subset_in_events image_image) 
  moreover have "0 < ?n" using assms(1) assms(2) by auto
  ultimately have "\<P>(\<Inter> ((?G \<circ> g) ` {0..<card I}) | \<Inter> E) = (\<Prod>i = 0..<?n. \<P>(?G (g i) | \<Inter> ((?G \<circ> g) ` {0..<i} \<union> E)))"
    using prob_cond_Inter_index_cond_set[of ?n E "(?G \<circ> g)"] assms(3) assms(4) assms(5) assms(6) 
      assms(7) by auto
  moreover have "\<And> i. i \<in> {0..<?n} \<Longrightarrow> (?G \<circ> g) ` {0..<i} = ?G ` g ` {0..<i}" using image_comp by auto
  ultimately have "\<P>(\<Inter> (?G ` I) | \<Inter> E) = (\<Prod>i = 0..<?n. \<P>(?G (g i) | \<Inter> (?G ` g ` {0..<i} \<union> E)))" 
    using image_comp[of ?G g "{0..<card I}"] eq by auto
  then show ?thesis using bb by blast
qed

lemma prob_cond_Inter_index_cond_compl_obtains:
  assumes "I \<noteq> {}"
  assumes "finite I"
  assumes "finite E"
  assumes "E \<noteq> {}"
  assumes "E \<subseteq> events"
  assumes "F ` I \<subseteq> events"
  assumes "prob (\<Inter>E) > 0"
  obtains g where "bij_betw g {0..<card I} I" and "\<P>((\<Inter>Aj \<in> I . space M - F Aj) | (\<Inter>E)) = 
    (\<Prod>i \<in> {0..<card I}.  \<P>(space M - F (g i) | (\<Inter>(((\<lambda>Aj. space M - F Aj) ` g ` {0..<i}) \<union> E))))"
proof -
  let ?n = "card I"
  let ?G = "\<lambda> i. space M - F i"
  obtain g where bb: "bij_betw g {0..<?n} I" using assms(2) ex_bij_betw_nat_finite by auto
  then show ?thesis using assms prob_cond_Inter_index_cond_compl_fn[of I E F g] that by blast
qed

lemma prob_cond_inter_index_fn2: 
  assumes "F ` S \<subseteq> events"
  assumes "finite S"
  assumes "card S > 0"
  assumes "bij_betw g {0..<card S} S"
  shows "prob (\<Inter>(F `S)) = prob (F (g 0)) * (\<Prod>i \<in> {1..<(card S)} . \<P>(F (g i) | (\<Inter>(F ` g ` {0..<i}))))"
proof -
  have 1: "F ` S = (F \<circ> g) ` {0..<card S}" using assms(4) bij_betw_image_comp_eq  by metis
  moreover have "prob (\<Inter>((F \<circ> g) ` {0..<card S})) = 
      prob (F (g 0)) * (\<Prod>i \<in> {1..<(card S)} . \<P>(F (g i) | (\<Inter>(F ` g ` {0..<i}))))"
    using 1 prob_cond_Inter_index[of "card S" "F \<circ> g"] assms(3) assms(1) by auto
  ultimately show ?thesis using assms(4)
    by metis
qed 

lemma prob_cond_inter_index_fn: 
  assumes "F ` S \<subseteq> events"
  assumes "finite S"
  assumes "S \<noteq> {}"
  assumes "bij_betw g {0..<card S} S"
  shows "prob (\<Inter>(F `S)) = prob (F (g 0)) * (\<Prod>i \<in> {1..<(card S)} . \<P>(F (g i) | (\<Inter>(F ` g ` {0..<i}))))"
proof -
  have "card S > 0" using assms(3) assms(2)
    by (simp add: card_gt_0_iff) 
  moreover have "(F \<circ> g) ` {0..<card S} \<subseteq> events" using assms(1) assms(4)
    using  bij_betw_imp_surj_on by (metis image_comp) 
  ultimately have "prob (\<Inter>((F \<circ> g) ` {0..<card S})) = 
      prob (F (g 0)) * (\<Prod>i \<in> {1..<(card S)} . \<P>(F (g i) | (\<Inter>(F ` g ` {0..<i}))))"
    using prob_cond_Inter_index[of "card S" "F \<circ> g"] by auto
  moreover have "F ` S = (F \<circ> g) ` {0..<card S}" using assms(4) 
    using bij_betw_imp_surj_on image_comp by (metis) 
  ultimately show ?thesis using assms(4) by presburger 
qed 

lemma prob_cond_inter_index_obtain_fn: 
  assumes "F ` S \<subseteq> events"
  assumes "finite S"
  assumes "S \<noteq> {}"
  obtains g where "bij_betw g {0..<card S} S"  and 
    "prob (\<Inter>(F `S)) = prob (F (g 0)) * (\<Prod>i \<in> {1..<(card S)} . \<P>(F (g i) | (\<Inter>(F ` g ` {0..<i}))))"
proof -
  obtain f where bb: "bij_betw f {0..<card S} S"
    using assms(2) ex_bij_betw_nat_finite by blast 
  then show ?thesis using prob_cond_inter_index_fn that assms by blast 
qed 

lemma prob_cond_inter_index_fn_compl: 
  assumes " S \<noteq> {}"
  assumes "F ` S \<subseteq> events"
  assumes "finite S"
  assumes "bij_betw f {0..<card S} S"
  shows "prob (\<Inter>((-) (space M) ` F ` S)) = prob (space M - F (f 0)) * 
    (\<Prod>i \<in> {1..<(card S)} . \<P>(space M - F (f i) | (\<Inter>((-) (space M) ` F ` f ` {0..<i}))))"
proof -
  define G where "G \<equiv> \<lambda> i. space M - F i"
  then have "G ` S \<subseteq> events" using G_def assms(2) by auto
  then have "prob (\<Inter> (G ` S)) = prob (G (f 0)) * (\<Prod>i = 1..<card S. \<P>(G (f i) | \<Inter> (G ` f ` {0..<i})))"
    using prob_cond_inter_index_fn[of G S] assms by auto
  moreover have "(\<Inter>((-) (space M) ` F ` S)) = (\<Inter>i\<in>S. space M - F i)" by auto
  ultimately show ?thesis unfolding G_def by auto
qed


lemma prob_cond_inter_index_obtain_fn_compl: 
  assumes " S \<noteq> {}"
  assumes "F ` S \<subseteq> events"
  assumes "finite S"
  obtains f where "bij_betw f {0..<card S} S"  and 
    "prob (\<Inter>((-) (space M) ` F ` S)) = prob (space M - F (f 0)) * 
      (\<Prod>i \<in> {1..<(card S)} . \<P>(space M - F (f i) | (\<Inter>((-) (space M) ` F ` f ` {0..<i}))))"
proof -
  obtain f where bb: "bij_betw f {0..<card S} S"
    using assms(3) ex_bij_betw_nat_finite by blast 
  then show ?thesis using prob_cond_inter_index_fn_compl[of S F f] assms that by blast
qed

lemma prob_cond_Inter_take: 
  assumes " S \<noteq> {}"
  assumes "S \<subseteq> events"
  assumes "finite S"
  obtains xs where "set xs = S" and "length xs = card S" and 
    "prob (\<Inter>S) = prob (hd xs) * (\<Prod>i = 1..<(length xs) . \<P>((xs ! i) | (\<Inter>(set (take i xs )))))"
  using assms prob_cond_Inter_List exists_list_card 
  by (metis (no_types, lifting) set_empty2 subset_code(1)) 


lemma prob_cond_Inter_set_bound: 
  assumes " A \<noteq> {}"
  assumes "A \<subseteq> events"
  assumes "finite A"
  assumes "\<And> Ai . f Ai \<ge> 0 \<and> f Ai \<le> 1"
  assumes "\<And>Ai S. Ai \<in> A \<Longrightarrow> S \<subseteq> A - {Ai} \<Longrightarrow> S \<noteq> {} \<Longrightarrow> \<P>(Ai | (\<Inter>S)) \<ge> f Ai"
  assumes "\<And> Ai. Ai \<in> A \<Longrightarrow> prob Ai \<ge> f Ai"
  shows "prob (\<Inter>A) \<ge> (\<Prod>a' \<in> A .  f a')"
proof - 
  obtain xs where eq: "set xs = A" and seq: "length xs = card A" and
    pA: "prob (\<Inter>A) = prob (hd xs) * (\<Prod>i = 1..<(length xs) . \<P>((xs ! i) | (\<Inter> j \<in> {0..<i} . xs ! j)))"
    using assms obtains_prob_cond_Inter_index[of A] by blast
  then have dis: "distinct xs" using card_distinct
    by metis 
  then have "hd xs \<in> A" using eq hd_in_set assms(1) by auto
  then have "prob (hd xs) \<ge> (f (hd xs))" using assms(6) by blast
  have "\<And> i. i \<in> {1..<(length xs)} \<Longrightarrow> \<P>((xs ! i) | (\<Inter> j \<in> {0..<i} . xs ! j)) \<ge> f (xs ! i)"
  proof -
    fix i assume "i \<in> {1..<length xs}"
    then have ilb: "i \<ge> 1" and iub: "i < length xs" by auto
    then have xsin: "xs ! i \<in> A" using eq by auto
    define S where "S = (\<lambda> j. xs ! j) ` {0..<i}"
    then have "S = set (take i xs)"
      by (simp add: iub less_or_eq_imp_le nth_image)
    then have "xs ! i \<notin> S" using dis set_take_distinct_elem_not iub by simp
    then have "S \<subseteq> A - {(xs ! i)}"
      using \<open>S = set (take i xs)\<close> eq set_take_subset by fastforce 
    moreover have "S \<noteq> {}" using S_def ilb by (simp) 
    moreover have "\<P>((xs ! i) | (\<Inter> j \<in> {0..<i} . xs ! j)) = \<P>((xs ! i) | (\<Inter> Aj \<in> S . Aj))" 
      using S_def by auto
    ultimately show "\<P>((xs ! i) | (\<Inter> j \<in> {0..<i} . xs ! j)) \<ge> f (xs ! i)"
      using assms(5) xsin by auto
  qed
  then have "(\<Prod>i = 1..<(length xs) . \<P>((xs ! i) | (\<Inter> j \<in> {0..<i} . xs ! j))) \<ge> 
    (\<Prod>i = 1..<(length xs) . f (xs ! i))"
    by (meson assms(4) prod_mono)
  moreover have "(\<Prod>i = 1..<(length xs) . f (xs ! i)) = (\<Prod>a \<in> A - {hd xs} . f a)"
  proof -
    have ne: "xs \<noteq> []" using assms(1) eq by auto
    have "A = (\<lambda> j. xs ! j) ` {0..<length xs}" using eq
      by (simp add: nth_image) 
    have "A - {hd xs} = set (tl xs) " using dis
      by (metis Diff_insert_absorb distinct.simps(2) eq list.exhaust_sel list.set(2) ne)
    also have "... = (\<lambda> j. xs ! j) ` {1..<length xs}" using nth_image_tl ne by auto
    finally have Ahdeq: "A - {hd xs} = (\<lambda> j. xs ! j) ` {1..<length xs}" by simp
    have io: "inj_on (nth xs) {1..<length xs}" using inj_on_nth dis
      by (metis atLeastLessThan_iff) 
    have "(\<Prod>i = 1..<(length xs) . f (xs ! i)) = (\<Prod>i \<in> {1..<(length xs)} . f (xs ! i))" by simp
    also have "... = (\<Prod>i \<in> (\<lambda> j. xs ! j) ` {1..<length xs} . f i)" 
      using io by (simp add: prod.reindex_cong) 
    finally show ?thesis using Ahdeq
      using \<open>(\<Prod>i = 1..<length xs. f (xs ! i)) = prod f ((!) xs ` {1..<length xs})\<close> by presburger 
  qed
  ultimately have "prob (\<Inter>A) \<ge> f (hd xs) * (\<Prod>a \<in> A - {hd xs} . f a)"
    using pA \<open>f (hd xs) \<le> prob (hd xs)\<close> assms(4) ordered_comm_semiring_class.comm_mult_left_mono
    by (simp add: mult_mono' prod_nonneg)  
  then show ?thesis
    by (metis \<open>hd xs \<in> A\<close> assms(3) prod.remove) 
qed
end

end