(* Author: Alexander Bentkamp, Universität des Saarlandes
*)
section \<open>Missing Lemmas of Sublist\<close>

theory DL_Missing_Sublist
imports Main
begin

lemma sublist_only_one:
assumes "{i. i < length xs \<and> i\<in>I} = {j}"
shows "sublist xs I = [xs!j]"
proof -
  have "set (sublist xs I) = {xs!j}" 
    unfolding set_sublist using subset_antisym assms by fastforce 
  moreover have "length (sublist xs I) = 1"
    unfolding length_sublist assms by auto
  ultimately show ?thesis 
    by (metis One_nat_def length_0_conv length_Suc_conv the_elem_eq the_elem_set)
qed

lemma sublist_replicate:
"sublist (replicate n x) A = (replicate (card {i. i < n \<and> i \<in> A}) x)"
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then show ?case
  proof (cases "n\<in>A")
    case True
    then have 0:"(if 0 \<in> {j. j + length (replicate n x) \<in> A} then [x] else []) = [x]" by simp
    have "{i. i < Suc n \<and> i \<in> A} = insert n {i. i < n \<and> i \<in> A}" using True by auto
    have "Suc (card {i. i < n \<and> i \<in> A}) = card {i. i < Suc n \<and> i \<in> A}"
      unfolding \<open>{i. i < Suc n \<and> i \<in> A} = insert n {i. i < n \<and> i \<in> A}\<close>
      using finite_Collect_conjI[THEN card_insert_if] finite_Collect_less_nat 
       less_irrefl_nat mem_Collect_eq by simp
    then show ?thesis unfolding replicate_Suc replicate_append_same[symmetric] sublist_append Suc sublist_singleton 0
      unfolding replicate_append_same replicate_Suc[symmetric] by simp
  next
    case False
    then have 0:"(if 0 \<in> {j. j + length (replicate n x) \<in> A} then [x] else []) = []" by simp
    have "{i. i < Suc n \<and> i \<in> A} = {i. i < n \<and> i \<in> A}" using False using le_less less_Suc_eq_le by auto
    then show ?thesis unfolding replicate_Suc replicate_append_same[symmetric] sublist_append Suc sublist_singleton 0
      by simp
  qed
qed 

lemma length_sublist_even:
assumes "even (length xs)"
shows "length (sublist xs (Collect even)) = length (sublist xs (Collect odd))"
using assms proof (induction "length xs div 2" arbitrary:xs)
  case 0
  then have "length xs = 0"
    using div_eq_0_iff length_0_conv length_greater_0_conv nat_dvd_not_less zero_not_eq_two by auto
  then show ?case by simp
next
  case (Suc l xs)
  then have length_drop2: "length (sublist (drop 2 xs) (Collect even)) = length (sublist (drop 2 xs) {a. odd a})" by simp

  have "length (take 2 xs) = 2" using Suc.hyps(2) by auto
  then have plus_odd: "{j. j + length (take 2 xs) \<in> Collect odd} = Collect odd" and
            plus_even: "{j. j + length (take 2 xs) \<in> Collect even} = Collect even" by simp_all
  have sublist_take2: "sublist (take 2 xs) (Collect even) = [take 2 xs ! 0]" "sublist (take 2 xs) (Collect odd) = [take 2 xs ! 1]" 
    using `length (take 2 xs) = 2` less_2_cases sublist_only_one[of "take 2 xs" "Collect even" 0]
    sublist_only_one[of "take 2 xs" "Collect odd" 1]  
    by fastforce+
  then have "length (sublist (take 2 xs @ drop 2 xs) (Collect even))
           = length (sublist (take 2 xs @ drop 2 xs) {a. odd a})" 
    unfolding sublist_append length_append plus_odd plus_even sublist_take2 length_drop2
    by auto
  then show ?case using append_take_drop_id[of 2 xs] by simp
qed

lemma sublist_map:
"sublist (map f xs) A = map f (sublist xs A)"
proof (induction xs arbitrary:A)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  then show ?case
  by (simp add: sublist_Cons)
qed


section "Pick"

fun pick :: "nat set \<Rightarrow> nat \<Rightarrow> nat" where
"pick S 0 = (LEAST a. a\<in>S)" |
"pick S (Suc n) = (LEAST a. a\<in>S \<and> a > pick S n)"

lemma pick_in_set_inf:
assumes "infinite S"
shows "pick S n \<in> S"
proof (cases n)
  show "n = 0 \<Longrightarrow> pick S n \<in> S" 
    unfolding pick.simps using `infinite S` LeastI pick.simps(1) by (metis Collect_mem_eq not_finite_existsD)
next
  fix n' assume "n = Suc n'"
  obtain a where "a\<in>S \<and> a > pick S n'" using assms by (metis bounded_nat_set_is_finite less_Suc_eq nat_neq_iff)
  show "pick S n \<in> S" unfolding `n = Suc n'` pick.simps(2) 
    using LeastI[of "\<lambda>a. a \<in> S \<and> pick S n' < a" a, OF `a\<in>S \<and> a > pick S n'`] by blast
qed

lemma pick_mono_inf:
assumes "infinite S"
shows "m < n \<Longrightarrow> pick S m < pick S n"
using assms proof (induction n)
  case 0
  then show ?case by auto
next
  case (Suc n)
  then obtain a where "a \<in> S \<and> pick S n < a" by (metis bounded_nat_set_is_finite less_Suc_eq nat_neq_iff)
  then have "pick S n < pick S (Suc n)" unfolding pick.simps 
    using LeastI[of "\<lambda>a. a \<in> S \<and> pick S n < a" a, OF `a\<in>S \<and> a > pick S n`] by simp
  then show ?case using Suc.IH Suc.prems(1) assms dual_order.strict_trans less_Suc_eq by auto
qed

lemma pick_eq_iff_inf:
assumes "infinite S"
shows "x = y \<longleftrightarrow> pick S x = pick S y"
  by (metis assms nat_neq_iff pick_mono_inf)

lemma card_le_pick_inf:
assumes "infinite S"
and "pick S n \<ge> i"
shows "card {a\<in>S. a < i} \<le> n"
using assms proof (induction n arbitrary:i)
  case 0
  then show ?case unfolding pick.simps using not_less_Least 
    by (metis (no_types, lifting) Collect_empty_eq card_0_eq card_ge_0_finite dual_order.strict_trans1 leI le_0_eq)
next
  case (Suc n)
  then show ?case
  proof - 
    have "card {a \<in> S. a < pick S n} \<le> n" using Suc by blast
    have "{a \<in> S. a < i} \<subseteq> {a \<in> S. a < pick S (Suc n)}" using Suc.prems(2) by auto
    have "{a \<in> S. a < pick S (Suc n)} = {a \<in> S. a < pick S n} \<union> {pick S n}" 
      apply (rule subset_antisym; rule subsetI) 
      using not_less_Least UnCI mem_Collect_eq nat_neq_iff singleton_conv
       pick_mono_inf[OF Suc.prems(1), of n "Suc n"] pick_in_set_inf[OF Suc.prems(1), of n] by fastforce+
    then have "card {a \<in> S. a < i} \<le> card {a \<in> S. a < pick S n} + card {pick S n}"  
      using card_Un_disjoint  card_mono[OF _ `{a \<in> S. a < i} \<subseteq> {a \<in> S. a < pick S (Suc n)}`] by simp
    then show ?thesis using \<open>card {a \<in> S. a < pick S n} \<le> n\<close>  by auto
  qed
qed
  
lemma card_pick_inf:
assumes "infinite S"
shows "card {a\<in>S. a < pick S n} = n"
using assms proof (induction n)
  case 0
  then show ?case unfolding pick.simps using not_less_Least by auto
next
  case (Suc n)
  then show "card {a\<in>S. a < pick S (Suc n)} = Suc n" 
  proof - 
    have "{a \<in> S. a < pick S (Suc n)} = {a \<in> S. a < pick S n} \<union> {pick S n}" 
      apply (rule subset_antisym; rule subsetI) 
      using not_less_Least UnCI mem_Collect_eq nat_neq_iff singleton_conv
       pick_mono_inf[OF Suc.prems, of n "Suc n"] pick_in_set_inf[OF Suc.prems, of n] by fastforce+
    then have "card {a \<in> S. a < pick S (Suc n)} = card {a \<in> S. a < pick S n} + card {pick S n}"  using card_Un_disjoint by auto
    then show ?thesis by (metis One_nat_def Suc_eq_plus1 Suc card_empty card_insert_if empty_iff finite.emptyI)
  qed
qed

lemma
assumes "n < card S"
shows 
  pick_in_set_le:"pick S n \<in> S" and 
  card_pick_le: "card {a\<in>S. a < pick S n} = n" and
  pick_mono_le: "m < n \<Longrightarrow> pick S m < pick S n"
using assms proof (induction n)
  assume "0 < card S"
  then obtain x where "x\<in>S" by fastforce
  then show "pick S 0 \<in> S" unfolding pick.simps by (meson LeastI)
  then show "card {a \<in> S. a < pick S 0} = 0" using not_less_Least by auto
  show "m < 0 \<Longrightarrow>  pick S m < pick S 0" by auto
next
  fix n 
  assume "n < card S \<Longrightarrow> pick S n \<in> S" 
    and "n < card S \<Longrightarrow> card {a \<in> S. a < pick S n} = n"
    and "Suc n < card S"
    and "m < n \<Longrightarrow> n < card S \<Longrightarrow> pick S m < pick S n"
  then have "card {a \<in> S. a < pick S n} = n" "pick S n \<in> S" by linarith+
  have "card {a \<in> S. a > pick S n} > 0"
  proof -
    have "S = {a \<in> S. a < pick S n} \<union> {a \<in> S. a \<ge> pick S n}" by fastforce
    then have "card {a \<in> S. a \<ge> pick S n} > 1" 
      using `Suc n < card S` `card {a \<in> S. a < pick S n} = n` 
      card_Un_le[of "{a \<in> S. a < pick S n}" "{a \<in> S. pick S n \<le> a}"] by force 
    then have 0:"{a \<in> S. a \<ge> pick S n} \<subseteq> {pick S n} \<union> {a \<in> S. a > pick S n}" by auto 
    have 1:"finite ({pick S n} \<union> {a \<in> S. pick S n < a})" 
      unfolding finite_Un using Collect_mem_eq assms card_infinite conjI by force
    have "1 < card {pick S n} + card {a \<in> S. pick S n < a}" 
      using card_mono[OF 1 0] card_Un_le[of "{pick S n}" "{a \<in> S. a > pick S n}"]  `card {a \<in> S. a \<ge> pick S n} > 1` 
      by linarith
    then show ?thesis by simp
  qed
  then show "pick S (Suc n) \<in> S" unfolding pick.simps 
    by (metis (no_types, lifting) Collect_empty_eq LeastI card_0_eq card_infinite less_numeral_extra(3))
  have "pick S (Suc n) > pick S n" 
    by (metis (no_types, lifting) pick.simps(2) `card {a \<in> S. a > pick S n} > 0` Collect_empty_eq LeastI card_0_eq card_infinite less_numeral_extra(3))
  then show "m < Suc n \<Longrightarrow> pick S m < pick S (Suc n)" 
    using `m < n \<Longrightarrow> n < card S \<Longrightarrow> pick S m < pick S n` 
    using \<open>Suc n < card S\<close> dual_order.strict_trans less_Suc_eq by auto
  then show "card {a\<in>S. a < pick S (Suc n)} = Suc n" 
  proof - 
    have "{a \<in> S. a < pick S (Suc n)} = {a \<in> S. a < pick S n} \<union> {pick S n}" 
      apply (rule subset_antisym; rule subsetI) 
      using pick.simps not_less_Least `pick S (Suc n) > pick S n` `pick S n \<in> S` by fastforce+
    then have "card {a \<in> S. a < pick S (Suc n)} = card {a \<in> S. a < pick S n} + card {pick S n}"  using card_Un_disjoint by auto
    then show ?thesis by (metis One_nat_def Suc_eq_plus1 \<open>card {a \<in> S. a < pick S n} = n\<close> card_empty card_insert_if empty_iff finite.emptyI)
  qed
qed

lemma card_le_pick_le:
assumes "n < card S"
and "pick S n \<ge> i"
shows "card {a\<in>S. a < i} \<le> n"
using assms proof (induction n arbitrary:i)
  case 0
  then show ?case unfolding pick.simps using not_less_Least 
    by (metis (no_types, lifting) Collect_empty_eq card_0_eq card_ge_0_finite dual_order.strict_trans1 leI le_0_eq)
next
  case (Suc n)
  have "card {a \<in> S. a < pick S n} \<le> n" using Suc by (simp add: less_eq_Suc_le nat_less_le)
  have "{a \<in> S. a < i} \<subseteq> {a \<in> S. a < pick S (Suc n)}" using Suc.prems(2) by auto
  have "{a \<in> S. a < pick S (Suc n)} = {a \<in> S. a < pick S n} \<union> {pick S n}" 
    apply (rule subset_antisym; rule subsetI) 
    using pick.simps not_less_Least  pick_mono_le[OF Suc.prems(1), of n, OF lessI] pick_in_set_le[of n S] Suc by fastforce+
  then have "card {a \<in> S. a < i} \<le> card {a \<in> S. a < pick S n} + card {pick S n}"  
    using card_Un_disjoint  card_mono[OF _ `{a \<in> S. a < i} \<subseteq> {a \<in> S. a < pick S (Suc n)}`] by simp
  then show ?case using \<open>card {a \<in> S. a < pick S n} \<le> n\<close>  by auto
qed

lemma
assumes "n < card S \<or> infinite S"
shows 
  pick_in_set:"pick S n \<in> S" and 
  card_le_pick: "i \<le> pick S n ==> card {a\<in>S. a < i} \<le> n" and
  card_pick: "card {a\<in>S. a < pick S n} = n" and
  pick_mono: "m < n \<Longrightarrow> pick S m < pick S n"
    using assms pick_in_set_inf pick_in_set_le card_pick_inf card_pick_le card_le_pick_le card_le_pick_inf
    pick_mono_inf pick_mono_le by auto

lemma pick_card:
"pick I (card {a\<in>I. a < i}) = (LEAST a. a\<in>I \<and> a \<ge> i)" 
proof (induction i)
  case 0
  then show ?case by (simp add: pick_in_set_le)
next
  case (Suc i)
  then show ?case 
  proof (cases "i\<in>I") 
    case True
    then have 1:"pick I (card {a\<in>I. a < i}) = i" by (metis (mono_tags, lifting) Least_equality Suc.IH order_refl)
    have "{a \<in> I. a < Suc i} = {a \<in> I. a < i} \<union> {i}" using True by auto
    then have 2:"card {a \<in> I. a < Suc i} = Suc (card {a \<in> I. a < i})" by auto
    then show ?thesis unfolding 2 pick.simps 1 using Suc_le_eq by auto
  next
    case False
    then have 1:"{a \<in> I. a < Suc i} = {a \<in> I. a < i}" using Collect_cong less_Suc_eq by auto
    have 2:"\<And>a. (a \<in> I \<and> Suc i \<le> a) = (a \<in> I \<and> i \<le> a)" using False Suc_leD le_less_Suc_eq not_le by blast
    then show ?thesis unfolding 1 2 using Suc.IH by blast
  qed
qed

lemma pick_card_in_set: "i\<in>I \<Longrightarrow> pick I (card {a\<in>I. a < i}) = i" 
  unfolding pick_card using Least_equality order_refl by (metis (no_types, lifting))

section "Sublist"

lemma nth_sublist_card:
assumes "j<length xs"
and "j\<in>J"
shows "sublist xs J ! card {j0. j0 < j \<and> j0 \<in> J} = xs!j"
using assms proof (induction xs rule:rev_induct)
  case Nil
  then show ?case using gr_implies_not0 list.size(3) by auto
next
  case (snoc x xs)
  then show ?case 
  proof (cases "j < length xs")
    case True
    have "{j0. j0 < j \<and> j0 \<in> J} \<subset> {i. i < length xs \<and> i \<in> J}" 
      using True snoc.prems(2) by auto
    then have "card {j0. j0 < j \<and> j0 \<in> J} < length (sublist xs J)" unfolding length_sublist 
      using psubset_card_mono[of "{i. i < length xs \<and> i \<in> J}"] by simp
    then show ?thesis unfolding sublist_append nth_append by (simp add: True snoc.IH snoc.prems(2))
  next
    case False
    then have "length xs = j" 
      using length_append_singleton less_antisym snoc.prems(1) by auto
    then show ?thesis unfolding sublist_append nth_append length_sublist `length xs = j` 
      by (simp add: snoc.prems(2))
  qed
qed

lemma pick_reduce_set:
assumes "i<card {a. a<m \<and> a\<in>I}"
shows "pick I i = pick {a. a < m \<and> a \<in> I} i"
using assms proof (induction i)
  let ?L = "LEAST a. a \<in> {a. a < m \<and> a \<in> I}"
  case 0
  then have "{a. a < m \<and> a \<in> I} \<noteq> {}" using card_empty less_numeral_extra(3) by fastforce
  then have "?L \<in> I" "?L < m" by (metis (mono_tags, lifting) Collect_empty_eq LeastI mem_Collect_eq)+
  have "\<And>x. x \<in> {a. a < m \<and> a \<in> I} \<Longrightarrow> ?L \<le> x" by (simp add: Least_le)
  have "\<And>x. x \<in> I \<Longrightarrow> ?L \<le> x" 
    by (metis (mono_tags) \<open>?L < m\<close> \<open>\<And>x. x \<in> {a. a < m \<and> a \<in> I} \<Longrightarrow> ?L \<le> x\<close> dual_order.strict_trans2 le_cases mem_Collect_eq)
  then show ?case unfolding pick.simps using Least_equality[of "\<lambda>x. x\<in>I", OF `?L \<in> I`] by blast
next
  case (Suc i)
  let ?L = "LEAST x. x \<in> {a. a < m \<and> a \<in> I} \<and> pick I i < x"
  have 0:"pick {a. a < m \<and> a \<in> I} i = pick I i" using Suc_lessD Suc by linarith
  then have "?L \<in> {a. a < m \<and> a \<in> I}" "pick I i < ?L" 
    using LeastI[of "\<lambda>a. a \<in> {a. a < m \<and> a \<in> I} \<and> pick I i < a"] using Suc.prems pick_in_set_le pick_mono_le by fastforce+
  then have "?L \<in> I" by blast
  show ?case unfolding pick.simps 0 using Least_equality[of "\<lambda>a. a \<in> I \<and> pick I i < a" ?L]  
    by (metis (no_types, lifting) Least_le \<open>?L \<in> {a. a < m \<and> a \<in> I}\<close> \<open>pick I i < ?L\<close> mem_Collect_eq not_le not_less_iff_gr_or_eq order.trans)
qed

lemma nth_sublist: 
assumes "i<card {i. i<length xs \<and> i\<in>I}"
shows "sublist xs I ! i = xs ! pick I i" 
proof -
  have "{a \<in> {i. i < length xs \<and> i \<in> I}. a < pick {i. i < length xs \<and> i \<in> I} i}
        = {a.  a < pick {i. i < length xs \<and> i \<in> I} i \<and> a \<in> I}" 
    using assms pick_in_set by fastforce
  then have "card {a. a < pick {i. i < length xs \<and> i \<in> I} i \<and> a \<in> I} = i" 
    using card_pick_le[OF assms] by simp
  then have "sublist xs I ! i = xs ! pick {i. i < length xs \<and> i \<in> I} i"
    using nth_sublist_card[where j = "pick {i. i < length xs \<and> i \<in> I} i", of xs I] 
    assms pick_in_set pick_in_set by auto
  then show ?thesis using pick_reduce_set using assms by auto
qed

lemma pick_UNIV: "pick UNIV j = j" 
by (induction j, simp, metis (no_types, lifting) LeastI pick.simps(2)  Suc_mono UNIV_I less_Suc_eq not_less_Least)

lemma pick_le:
assumes "n < card {a. a < i \<and> a \<in> S}"
shows "pick S n < i"
proof -
  have 0:"{a \<in> {a. a < i \<and> a \<in> S}. a < i} = {a. a < i \<and> a \<in> S}" by blast
  show ?thesis apply (rule ccontr) 
    using card_le_pick_le[OF assms, unfolded pick_reduce_set[OF assms, symmetric], of i, unfolded 0]
    assms not_less not_le by blast
qed

lemma prod_list_complementary_sublists:
fixes f ::"'a \<Rightarrow> 'b::comm_monoid_mult"
shows "prod_list (map f xs) = prod_list (map f (sublist xs A)) *  prod_list (map f (sublist xs (-A)))"
proof (induction xs rule:rev_induct)
  case Nil
  then show ?case by simp
next
  case (snoc x xs)
  show ?case unfolding map_append "prod_list.append" sublist_append sublist_singleton snoc 
    by (cases "(length xs)\<in>A"; simp;metis mult.assoc mult.commute)
qed

lemma sublist_zip: "sublist (zip xs ys) I = zip (sublist xs I) (sublist ys I)" 
proof (rule nth_equalityI)
  show "length (sublist (zip xs ys) I) = length (zip (sublist xs I) (sublist ys I))" 
  proof (cases "length xs \<le> length ys")
    case True
    then have "{i. i < length xs \<and> i \<in> I} \<subseteq> {i. i < length ys \<and> i \<in> I}" by (simp add: Collect_mono less_le_trans)
    then have "card {i. i < length xs \<and> i \<in> I} \<le> card {i. i < length ys \<and> i \<in> I}" 
      by (metis (mono_tags, lifting) card_mono finite_nat_set_iff_bounded mem_Collect_eq)
    then show ?thesis unfolding length_sublist length_zip using True using min_def by linarith
  next
    case False
    then have "{i. i < length ys \<and> i \<in> I} \<subseteq> {i. i < length xs \<and> i \<in> I}" by (simp add: Collect_mono less_le_trans)
    then have "card {i. i < length ys \<and> i \<in> I} \<le> card {i. i < length xs \<and> i \<in> I}" 
      by (metis (mono_tags, lifting) card_mono finite_nat_set_iff_bounded mem_Collect_eq)
    then show ?thesis unfolding length_sublist length_zip using False using min_def by linarith
  qed
  show "\<forall>i<length (sublist (zip xs ys) I). sublist (zip xs ys) I ! i = zip (sublist xs I) (sublist ys I) ! i"
  proof (rule allI; rule impI)
   fix i assume "i < length (sublist (zip xs ys) I)"
   then have "i < length (sublist xs I)" "i < length (sublist ys I)" 
     by (simp_all add: \<open>length (sublist (zip xs ys) I) = length (zip (sublist xs I) (sublist ys I))\<close>)
   show "sublist (zip xs ys) I ! i = zip (sublist xs I) (sublist ys I) ! i"
     unfolding nth_sublist[OF `i < length (sublist (zip xs ys) I)`[unfolded length_sublist]] 
     unfolding nth_zip[OF `i < length (sublist xs I)` `i < length (sublist ys I)`]
     unfolding nth_zip[OF pick_le[OF `i < length (sublist xs I)`[unfolded length_sublist]] 
                          pick_le[OF `i < length (sublist ys I)`[unfolded length_sublist]]]
     by (metis (full_types) \<open>i < length (sublist xs I)\<close> \<open>i < length (sublist ys I)\<close> length_sublist nth_sublist)
  qed
qed


end
