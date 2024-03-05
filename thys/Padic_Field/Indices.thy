theory Indices
imports Main
begin

(**************************************************************************************************)
(**************************************************************************************************)
section\<open>Basic Lemmas for Manipulating Indices and Lists\<close>
(**************************************************************************************************)
(**************************************************************************************************)
fun index_list where
"index_list 0 = []"|
"index_list (Suc n) = index_list n @ [n]"

lemma index_list_length:
"length (index_list n) = n"
  by(induction n, simp, auto ) 

lemma index_list_indices:
"k < n \<Longrightarrow> (index_list n)!k = k"
  apply(induction n)
  apply (simp; fail)
  by (simp add: index_list_length nth_append)

lemma index_list_set:
"set (index_list n) = {..<n}"
  apply(induction n)
  apply force
  by (metis Zero_not_Suc atLeastLessThan_empty atLeastLessThan_singleton atLeastLessThan_upt 
      diff_Suc_1 index_list.elims ivl_disj_un_singleton(2) lessI lessThan_Suc_atMost less_Suc_eq_le 
      set_append sorted_list_of_set_empty sorted_list_of_set_range upt_rec)

fun flat_map :: "('a => 'b list) => 'a list => 'b list" where
  "flat_map f [] = []"
 |"flat_map f (h#t) = (f h)@(flat_map f t)"

abbreviation(input) project_at_indices ("\<pi>\<^bsub>_\<^esub>") where
"project_at_indices S as \<equiv> nths as S"

fun insert_at_index :: " 'a list \<Rightarrow>'a \<Rightarrow> nat \<Rightarrow> 'a list" where
"insert_at_index as a n= (take n as) @ (a#(drop n as))"

lemma insert_at_index_length:
  shows "length (insert_at_index as a n) = length as + 1"
  by(induction n, auto) 

lemma insert_at_index_eq[simp]:
  assumes "n \<le> length as"
  shows "(insert_at_index as a n)!n = a"
  by (metis assms insert_at_index.elims length_take min.absorb2 nth_append_length)

lemma insert_at_index_eq'[simp]:
  assumes "n \<le> length as"
  assumes "k < n"
  shows "(insert_at_index as a n)!k = as ! k"
  using assms 
  by (simp add: nth_append)

lemma insert_at_index_eq''[simp]:
  assumes "n < length as"
  assumes "k \<le> n"
  shows "(insert_at_index as a k)!(Suc n) = as ! n"  
  using assms insert_at_index.simps[of as a k] 
  by (smt Suc_diff_Suc append_take_drop_id diff_Suc_Suc dual_order.order_iff_strict 
      le_imp_less_Suc length_take less_trans min.absorb2 not_le nth_Cons_Suc nth_append)

text\<open>Correctness of project\_at\_indices\<close>

definition indices_of :: "'a list \<Rightarrow> nat set" where
"indices_of as = {..<(length as)}"

lemma proj_at_index_list_length[simp]:
  assumes "S \<subseteq> indices_of as"
  shows "length (project_at_indices S as) = card S"
proof-
  have "S = {i. i < length as \<and> i \<in> S}"
    using assms unfolding indices_of_def 
    by blast
  thus ?thesis 
  using length_nths[of as S] by auto   
qed

text\<open>A function which enumerates finite sets\<close>

abbreviation(input) set_to_list :: "nat set \<Rightarrow>  nat list" where
"set_to_list S \<equiv> sorted_list_of_set S"

lemma set_to_list_set:
  assumes "finite S"
  shows "set (set_to_list S) = S"
  by (simp add: assms)

lemma set_to_list_length:
  assumes "finite S"
  shows "length (set_to_list S) = card S"
  by (metis assms length_remdups_card_conv length_sort set_sorted_list_of_set sorted_list_of_set_sort_remdups)

lemma set_to_list_empty:
  assumes "card S = 0"
  shows "set_to_list S = []"
  by (metis assms length_0_conv length_sorted_list_of_set)

lemma set_to_list_first:
  assumes "card S > 0"
  shows "Min S = set_to_list S ! 0 "
proof-
  have 0: "set (set_to_list S) = S"
    using assms card_ge_0_finite set_sorted_list_of_set by blast
  have 1: "sorted (set_to_list S)"
    by simp
  show ?thesis apply(rule Min_eqI)
    using assms card_ge_0_finite apply blast
     apply (metis "0" "1" in_set_conv_nth less_Suc0 less_or_eq_imp_le not_less_eq sorted_iff_nth_mono_less)
      by (metis "0" Max_in assms card_0_eq card_ge_0_finite gr_zeroI in_set_conv_nth not_less0)
qed
  
lemma set_to_list_last:
  assumes "card S > 0"
  shows "Max S = last (set_to_list S)"
proof-
  have 0: "set (set_to_list S) = S"
    using assms card_ge_0_finite set_sorted_list_of_set by blast
  have 1: "sorted (set_to_list S)"
    by simp
  show ?thesis apply(rule Max_eqI)
    using assms card_ge_0_finite apply blast
     apply (smt "0" "1" Suc_diff_1 in_set_conv_nth last_conv_nth le_simps(2) length_greater_0_conv 
        less_or_eq_imp_le nat_neq_iff neq0_conv not_less_eq sorted_iff_nth_mono_less)
      by (metis "0" assms card.empty empty_set last_in_set less_numeral_extra(3))
qed

lemma set_to_list_insert_Max:
  assumes "finite S"
  assumes "\<And>s. s \<in> S \<Longrightarrow> a > s"
  shows "set_to_list (insert a S) = set_to_list S @[a]"
  by (metis assms(1) assms(2) card_0_eq card_insert_if finite.insertI infinite_growing 
      insert_not_empty less_imp_le_nat sorted_insort_is_snoc sorted_list_of_set(1) sorted_list_of_set(2) 
      sorted_list_of_set_insert)

lemma set_to_list_insert_Min:
  assumes "finite S"
  assumes "\<And>s. s \<in> S \<Longrightarrow> a < s"
  shows "set_to_list (insert a S) = a#set_to_list S"
  by (metis assms(1) assms(2) insort_is_Cons nat_less_le sorted_list_of_set(1) sorted_list_of_set_insert)

fun nth_elem where
"nth_elem S n = set_to_list S ! n"

lemma nth_elem_closed:
  assumes "i < card S"
  shows "nth_elem S i \<in> S"
  by (metis assms card.infinite not_less0 nth_elem.elims nth_mem set_to_list_length sorted_list_of_set(1))

lemma nth_elem_Min:
  assumes "card S > 0"
  shows "nth_elem S 0 = Min S"
  by (simp add: assms  set_to_list_first)

lemma nth_elem_Max:
  assumes "card S > 0"
  shows "nth_elem S (card S - 1) = Max S"
proof-
  have "last (set_to_list S) = set_to_list S ! (card S - 1)"
    by (metis assms card_0_eq card_ge_0_finite last_conv_nth neq0_conv set_to_list_length sorted_list_of_set_eq_Nil_iff)
  thus ?thesis 
    using assms set_to_list_last set_to_list_length 
    by simp
qed

lemma nth_elem_Suc:
  assumes "card S > Suc n"
  shows "nth_elem S (Suc n) > nth_elem S n"
  using assms sorted_sorted_list_of_set[of S] set_to_list_length[of S]
  by (metis Suc_lessD card.infinite distinct_sorted_list_of_set lessI nat_less_le not_less0 nth_elem.elims nth_eq_iff_index_eq sorted_iff_nth_mono_less)

lemma nth_elem_insert_Min:
  assumes "card S > 0"
  assumes "a < Min S"
  shows "nth_elem (insert a S) (Suc i) = nth_elem S i"
  using assms  
  by (metis Min_gr_iff card_0_eq card_ge_0_finite neq0_conv nth_Cons_Suc nth_elem.elims set_to_list_insert_Min)
  
lemma set_to_list_Suc_map:
  assumes "finite S"
  shows "set_to_list (Suc ` S) = map Suc (set_to_list S)"
proof-
  obtain n where n_def: "n = card S"
    by blast 
  have "\<And>S. card S = n \<Longrightarrow> set_to_list (Suc ` S) = map Suc (set_to_list S)"
  proof(induction n)
    case 0
    then show ?case 
      by (metis card_eq_0_iff finite_imageD image_is_empty inj_Suc list.simps(8) set_to_list_empty)
  next
    case (Suc n)
    have 0: "S = insert (Min S) (S - {Min S})"
      by (metis Min_in Suc.prems card_gt_0_iff insert_Diff zero_less_Suc)
    have 1: "sorted_list_of_set (Suc ` (S - {Min S})) = map Suc (sorted_list_of_set (S - {Min S}))"
      by (metis "0" Suc.IH Suc.prems card_Diff_singleton card.infinite diff_Suc_1 insertI1 nat.simps(3))
    have 2: "set_to_list S = (Min S)#(set_to_list (S - {Min S}))"
      by (metis "0" DiffD1 Min_le Suc.prems card_Diff_singleton card.infinite card_insert_if  
          diff_Suc_1 finite_Diff n_not_Suc_n nat.simps(3) nat_less_le set_to_list_insert_Min)
    have 3: "sorted_list_of_set (Suc ` S) = (Min (Suc ` S))#(set_to_list ((Suc ` S) - {Min (Suc ` S)}))"
      by (metis DiffD1 Diff_idemp Min_in Min_le Suc.prems card_Diff1_less card_eq_0_iff finite_Diff 
          finite_imageI image_is_empty insert_Diff nat.simps(3) nat_less_le set_to_list_insert_Min)
    have 4: "(Min (Suc ` S)) = Suc (Min S)"
      by (metis Min.hom_commute Suc.prems Suc_le_mono card_eq_0_iff min_def nat.simps(3))
    have 5: "sorted_list_of_set (Suc ` S) = Suc (Min S)#(set_to_list ((Suc ` S) - {Suc (Min S)}))"
      using 3 4 by auto 
    have 6: "sorted_list_of_set (Suc ` S) = Suc (Min S)#(set_to_list (Suc ` (S - {Min S})))"
      by (metis (no_types, lifting) "0" "5" Diff_insert_absorb image_insert inj_Suc inj_on_insert)
    show ?case 
      using 6 
      by (simp add: "1" "2")
  qed  
  thus ?thesis 
    using n_def by blast
qed

lemma nth_elem_Suc_im:
  assumes "i < card S"
  shows "nth_elem (Suc ` S) i = Suc (nth_elem S i) "
  using set_to_list_Suc_map 
  by (metis assms card_ge_0_finite dual_order.strict_trans not_gr0 nth_elem.elims nth_map set_to_list_length)

lemma set_to_list_upto:
"set_to_list {..<n} = [0..<n]"
  by (simp add: lessThan_atLeast0)

lemma nth_elem_upto:
  assumes "i < n"
  shows "nth_elem {..<n} i = i"
  using set_to_list_upto 
  by (simp add: assms)

text\<open>Characterizing the entries of project\_at\_indices \<close>

lemma project_at_indices_append:
"project_at_indices S (as@bs) = project_at_indices S as @ project_at_indices {j. j + length as \<in> S} bs"
  using nths_append[of as bs S] by auto 

lemma project_at_indices_nth:
  assumes "S \<subseteq> indices_of as"
  assumes "card S > i"
  shows "project_at_indices S as ! i = as ! (nth_elem S i)"
proof-
  have "\<And> S i. S \<subseteq> indices_of as \<and> card S > i \<Longrightarrow> project_at_indices S as ! i = as ! (nth_elem S i)"
  proof(induction as)
    case Nil
    then show ?case 
      by (metis list.size(3) not_less0 nths_nil proj_at_index_list_length)   
  next
    case (Cons a as)
    assume A: "S \<subseteq> indices_of (a # as) \<and> i < card S"
    have 0: "nths (a # as) S = (if 0 \<in> S then [a] else []) @ nths as {j. Suc j \<in> S}"
      using nths_Cons[of a as S] by simp 
    show "nths (a # as) S ! i = (a # as) ! nth_elem S i"
    proof(cases "0 \<in> S")
      case True
      show ?thesis 
      proof(cases "S = {0}")
        case True
        then show ?thesis 
          using "0" Cons.prems  by auto        
      next
        case False
        have T0: "nths (a # as) S = a#nths as {j. Suc j \<in> S}"
          using 0 
          by (simp add: True)
        have T1: "{j. Suc j \<in> S} \<subseteq> indices_of as"
        proof fix x assume A: "x \<in> {j. Suc j \<in> S}"
          then have "Suc x < length (a#as)" 
          using Cons.prems indices_of_def by blast
         then show "x \<in> indices_of as"
          by (simp add: indices_of_def)
        qed
        have T2: "\<And>i.  i < card {j. Suc j \<in> S} \<Longrightarrow> nths as {j. Suc j \<in> S} ! i = as ! nth_elem {j. Suc j \<in> S} i"
          using Cons.IH T1 by blast
        have T3: "\<And>i.  i < card {j. Suc j \<in> S} \<Longrightarrow> nth_elem {j. j > 0 \<and> j\<in> S} i = nth_elem S (Suc i)"
        proof-
          have 0: " 0 < card {j. Suc j \<in> S}" 
            by (smt Cons.prems Diff_iff Diff_subset False T0 T1 True add_diff_cancel_left' 
                card.insert card_0_eq card.infinite finite_subset gr_zeroI insert_Diff 
                length_Cons n_not_Suc_n plus_1_eq_Suc proj_at_index_list_length singletonI)
          have 1: "(insert 0 {j. 0 < j \<and> j \<in> S}) = S"
            apply(rule set_eqI) using True  gr0I by blast
          have 2: "0 < Min {j. 0 < j \<and> j \<in> S}" using False 
            by (metis (mono_tags, lifting) "1" Cons.prems Min_in finite_insert finite_lessThan
                finite_subset indices_of_def less_Suc_eq less_Suc_eq_0_disj mem_Collect_eq singleton_conv)    
          show "\<And>i. i < card {j. Suc j \<in> S} \<Longrightarrow> nth_elem {j. 0 < j \<and> j \<in> S} i = nth_elem S (Suc i)"
            using 0 1 2 nth_elem_insert_Min[of "{j. 0 < j \<and> j \<in> S}" 0] True False 
            by (metis (no_types, lifting) Cons.prems T0 T1 card_gt_0_iff finite_insert length_Cons less_SucI proj_at_index_list_length)
        qed      
        show "nths (a # as) S ! i = (a # as) ! nth_elem S i"
          apply(cases "i = 0")
           apply (metis Cons.prems Min_le T0 True card_ge_0_finite le_zero_eq nth_Cons' nth_elem_Min)           
        proof-
          assume "i \<noteq> 0"
          then have "i = Suc (i - 1)"
            using Suc_pred' by blast
          hence "nths (a # as) S ! i = nths as {j. Suc j \<in> S} ! (i-1)"
            using A by (simp add: T0)
          thus "nths (a # as) S ! i = (a # as) ! nth_elem S i"
          proof-
            have "i - 1 < card {j. Suc j \<in> S}"
              by (metis Cons.prems Suc_less_SucD T0 T1 \<open>i = Suc (i - 1)\<close> length_Cons proj_at_index_list_length)
            hence 0: "nth_elem {j. 0 < j \<and> j \<in> S} (i - 1) = nth_elem S i" 
              using T3[of "i-1"] \<open>i = Suc (i - 1)\<close> by auto   

            have 1: "nths as {j. Suc j \<in> S} ! (i-1) = as ! nth_elem {j. Suc j \<in> S} (i-1)"
              using T2 \<open>i - 1 < card {j. Suc j \<in> S}\<close> by blast
            have 2: "(a # as) ! nth_elem S i = as! ((nth_elem S i) - 1)"
              by (metis Cons.prems \<open>i = Suc (i - 1)\<close> not_less0 nth_Cons' nth_elem_Suc)
            have 3: "(nth_elem S i) - 1 = nth_elem {j. Suc j \<in> S} (i-1)"
            proof-
              have "Suc ` {j. Suc j \<in> S} = {j. 0 < j \<and> j \<in> S}"
              proof
                show "Suc ` {j. Suc j \<in> S} \<subseteq> {j. 0 < j \<and> j \<in> S}"
                  by blast
                show "{j. 0 < j \<and> j \<in> S} \<subseteq> Suc ` {j. Suc j \<in> S}"
                  using Suc_pred gr0_conv_Suc by auto
              qed
              thus ?thesis 
                using "0" \<open>i - 1 < card {j. Suc j \<in> S}\<close> nth_elem_Suc_im by fastforce
            qed
            show "nths (a # as) S ! i = (a # as) ! nth_elem S i"
              using "1" "2" "3" \<open>nths (a # as) S ! i = nths as {j. Suc j \<in> S} ! (i - 1)\<close> by auto
          qed
        qed
      qed
    next
      case False
      have F0: "nths (a # as) S = nths as {j. Suc j \<in> S}"
        by (simp add: "0" False)
      have F1: "Suc `{j. Suc j \<in> S} = S"
      proof show "Suc ` {j. Suc j \<in> S} \<subseteq> S" by auto 
            show "S \<subseteq> Suc ` {j. Suc j \<in> S}"  using False Suc_pred  
                by (smt image_iff mem_Collect_eq neq0_conv subsetI)
      qed
      have F2: "{j. Suc j \<in> S} \<subseteq> indices_of as \<and> i < card {j. Suc j \<in> S}"
        using F1 
        by (metis (mono_tags, lifting) A F0 Suc_less_SucD indices_of_def length_Cons lessThan_iff
            mem_Collect_eq proj_at_index_list_length subset_iff)        
      have F3: "project_at_indices {j. Suc j \<in> S} as ! i = as ! (nth_elem {j. Suc j \<in> S} i)"
        using F2 Cons(1)[of "{j. Suc j \<in> S}"] Cons(2)
        by blast
      then show ?thesis 
        using F0 F1 F2 nth_elem_Suc_im by fastforce
    qed
  qed
  then show ?thesis 
    using assms(1) assms(2) by blast
qed

text\<open>An inverse for nth\_elem\<close>

definition set_rank where
"set_rank S x = (THE i. i < card S \<and> x = nth_elem S i)"

lemma set_rank_exist:
  assumes "finite S"
  assumes "x \<in> S"
  shows "\<exists>i. i < card S \<and> x = nth_elem S i"
  using assms nth_elem.simps[of S]
  by (metis in_set_conv_nth set_to_list_length sorted_list_of_set(1))  

lemma set_rank_unique:
  assumes "finite S"
  assumes "x \<in> S"
  assumes "i < card S \<and> x = nth_elem S i"
  assumes "j < card S \<and> x = nth_elem S j"
  shows "i = j"
  using assms nth_elem.simps[of S]
  by (simp add: \<open>i < card S \<and> x = nth_elem S i\<close> \<open>j < card S \<and> x = nth_elem S j\<close>
      nth_eq_iff_index_eq set_to_list_length)

lemma nth_elem_set_rank_inv:
  assumes "finite S"
  assumes "x \<in> S"
  shows "nth_elem S (set_rank S x) = x"
  using the_equality  set_rank_unique set_rank_exist assms 
  unfolding set_rank_def 
  by smt

lemma set_rank_nth_elem_inv:
  assumes "finite S"
  assumes "i < card S"
  shows "set_rank S (nth_elem S i) = i"
  using the_equality  set_rank_unique set_rank_exist assms 
  unfolding set_rank_def 
proof -
  show "(THE n. n < card S \<and> nth_elem S i = nth_elem S n) = i"
    using assms(1) assms(2) nth_elem_closed set_rank_unique by blast
qed
 
lemma set_rank_range:
  assumes "finite S"
  assumes "x \<in> S"
  shows "set_rank S x < card S"
  using assms(1) assms(2) set_rank_exist set_rank_nth_elem_inv by fastforce

lemma project_at_indices_nth':
  assumes "S \<subseteq> indices_of as"
  assumes "i \<in> S"
  shows "as ! i = project_at_indices S as ! (set_rank S i) "
  by (metis assms(1) assms(2) finite_lessThan finite_subset indices_of_def nth_elem_set_rank_inv 
      project_at_indices_nth set_rank_range)

fun proj_away_from_index :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list" ("\<pi>\<^bsub>\<noteq>_\<^esub>")where
"proj_away_from_index n as = (take n as)@(drop (Suc n) as)"

text\<open>proj\_away\_from\_index is an inverse to insert\_at\_index\<close>

lemma insert_at_index_project_away[simp]:
  assumes "k < length as"
  assumes "bs = (insert_at_index as a k)"
  shows "\<pi>\<^bsub>\<noteq> k\<^esub> bs = as"
  using assms insert_at_index.simps[of as a k] proj_away_from_index.simps[of k bs]
  by (simp add: \<open>k < length as\<close> less_imp_le_nat min.absorb2)

definition fibred_cell :: "'a list set \<Rightarrow> ('a list \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list set" where 
"fibred_cell C P = {as . \<exists>x t. as = (t#x) \<and> x \<in> C \<and> (P x t)}"

definition fibred_cell_at_ind :: "nat \<Rightarrow> 'a list set \<Rightarrow> ('a list \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list set" where
"fibred_cell_at_ind n C P = {as . \<exists>x t. as = (insert_at_index x t n) \<and> x \<in> C \<and> (P x t)}"

lemma fibred_cell_lengths:
  assumes "\<And>k. k \<in> C \<Longrightarrow> length k = n"
  shows "k \<in> (fibred_cell C P) \<Longrightarrow> length k = Suc n"
proof-
  assume "k \<in> (fibred_cell C P)"
  obtain x t where "k = (t#x) \<and> x \<in> C \<and> P x t"
  proof -
    assume a1: "\<And>t x. k = t # x \<and> x \<in> C \<and> P x t \<Longrightarrow> thesis"
    have "\<exists>as a. k = a # as \<and> as \<in> C \<and> P as a"
      using \<open>k \<in> fibred_cell C P\<close> fibred_cell_def by blast
    then show ?thesis
      using a1 by blast
  qed
  then show ?thesis 
    by (simp add: assms)
qed

lemma fibred_cell_at_ind_lengths:
  assumes "\<And>k. k \<in> C \<Longrightarrow> length k = n"
  assumes "k \<le> n"
  shows "c \<in> (fibred_cell_at_ind k C P) \<Longrightarrow> length c = Suc n"
proof-
  assume "c \<in> (fibred_cell_at_ind k C P)"
  then obtain x t where "c = (insert_at_index x t k) \<and> x \<in> C \<and> (P x t)"
    using assms
    unfolding fibred_cell_at_ind_def 
    by blast
  then show ?thesis 
    by (simp add: assms(1))   
qed

lemma project_fibred_cell:
  assumes "\<And>k. k \<in> C \<Longrightarrow> length k = n"
  assumes "k < n"
  assumes "\<forall>x \<in> C. \<exists>t. P x t"
  shows "\<pi>\<^bsub>\<noteq> k\<^esub> ` (fibred_cell_at_ind k C P) = C"
proof
  show "\<pi>\<^bsub>\<noteq>k\<^esub> ` fibred_cell_at_ind k C P \<subseteq> C"
  proof
    fix x
    assume x_def: "x \<in> \<pi>\<^bsub>\<noteq>k\<^esub> ` fibred_cell_at_ind k C P"
    then obtain c where c_def: "x = \<pi>\<^bsub>\<noteq>k\<^esub> c \<and> c \<in>  fibred_cell_at_ind k C P"
      by blast
    then obtain y t where yt_def: "c = (insert_at_index y t k) \<and> y \<in> C \<and> (P y t)"
      using assms
      unfolding fibred_cell_at_ind_def 
      by blast
    have 0: "x =\<pi>\<^bsub>\<noteq>k\<^esub> c"
      by (simp add: c_def)
    have 1: "y =\<pi>\<^bsub>\<noteq>k\<^esub> c"
      using yt_def  assms(1) assms(2)
      by (metis insert_at_index_project_away)      
    have 2: "x = y" using 0 1 by auto 
    then show "x \<in> C"
      by (simp add: yt_def)
  qed
  show "C \<subseteq> \<pi>\<^bsub>\<noteq>k\<^esub> ` fibred_cell_at_ind k C P"
  proof fix x
    assume A: "x \<in> C"
    obtain t where t_def: "P x t"
      using assms A by auto 
    then show "x \<in> \<pi>\<^bsub>\<noteq>k\<^esub> ` fibred_cell_at_ind k C P"
    proof -
      have f1: "\<forall>a n A as. take n as @ (a::'a) # drop n as \<notin> A \<or> as \<in> \<pi>\<^bsub>\<noteq>n\<^esub> ` A \<or> \<not> n < length as"
        by (metis insert_at_index.simps insert_at_index_project_away rev_image_eqI)        
      have "\<forall>n. \<exists>as a. take n x @ t # drop n x = insert_at_index as a n \<and> as \<in> C \<and> P as a"
        using A t_def by auto 
      then have "\<forall>n. take n x @ t # drop n x \<in> {insert_at_index as a n |as a. as \<in> C \<and> P as a}"
        by blast
      then have "x \<in> \<pi>\<^bsub>\<noteq>k\<^esub> ` {insert_at_index as a k |as a. as \<in> C \<and> P as a}"
        using f1 by (metis (lifting) A assms(1) assms(2))
      then show ?thesis
        by (simp add: fibred_cell_at_ind_def)
    qed
  qed
qed

definition list_segment where
"list_segment i j as = map (nth as)  [i..<j]"

lemma list_segment_length:
  assumes "i \<le> j"
  assumes "j \<le>  length as"
  shows "length (list_segment i j as) = j - i"
  using  assms 
  unfolding list_segment_def   
  by (metis length_map length_upt)

lemma list_segment_drop:
  assumes "i < length as"
  shows "(list_segment i (length as) as) = drop i  as"
  by (metis One_nat_def Suc_diff_Suc add_diff_inverse_nat drop0  drop_map drop_upt
      less_Suc_eq list_segment_def map_nth neq0_conv not_less0 plus_1_eq_Suc)
  
lemma list_segment_concat:
  assumes "j \<le> k"
  assumes "i \<le> j"
  shows "(list_segment i j as) @ (list_segment j k as) = (list_segment i k as)"
  using assms   unfolding list_segment_def 
  using le_Suc_ex upt_add_eq_append 
  by fastforce

lemma list_segment_subset:
  assumes "j \<le> k"
  shows "set (list_segment i j as) \<subseteq> set (list_segment i k as)"
  apply(cases "i > j")
  unfolding list_segment_def 
  apply (metis in_set_conv_nth length_map list.size(3) order.asym subsetI upt_rec zero_order(3))
proof-
  assume "\<not> j < i"
  then have "i \<le>j"
    using not_le 
    by blast
  then have "list_segment i j as @ list_segment j k as = list_segment i k as"
    using assms list_segment_concat[of j k i as] by auto 
  then show "set (map ((!) as) [i..<j]) \<subseteq> set (map ((!) as) [i..<k])" 
    using set_append  unfolding list_segment_def 
    by (metis Un_upper1)
qed

lemma list_segment_subset_list_set:
  assumes "j \<le> length as"
  shows "set (list_segment i j as) \<subseteq> set as"
  apply(cases "i \<ge> j")
  apply (simp add: list_segment_def)
proof-
  assume A: "\<not> j \<le> i"
  then have B: "i < j"
    by auto 
  have 0: "list_segment i (length as) as = drop i as"
    using B assms list_segment_drop[of i as] less_le_trans 
    by blast
  have 1: "set (list_segment i j as) \<subseteq> set (list_segment i (length as) as)"
    using B assms list_segment_subset[of j "length as" i as] 
    by blast
  then show ?thesis 
  using assms 0 dual_order.trans  set_drop_subset[of i as]
    by metis
qed

definition fun_inv where 
"fun_inv = inv"



end
