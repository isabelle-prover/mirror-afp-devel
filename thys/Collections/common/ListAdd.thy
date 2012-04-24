theory ListAdd
imports Main
begin 

(* Additional Lemmas for Lists *)

(* TODO: Misc *)
lemma (in linorder) sorted_hd_min: "\<lbrakk>xs \<noteq> []; sorted xs\<rbrakk> \<Longrightarrow> \<forall>x \<in> set xs. hd xs \<le> x"
  by(induct xs, auto simp add: sorted_Cons)

lemma map_hd: "\<lbrakk>xs \<noteq> []\<rbrakk> \<Longrightarrow> f (hd xs) = hd (map f xs)"
 apply(induct xs)
 apply(auto)
done

lemma map_tl: "map f (tl xs) = tl (map f xs)"
  apply(induct xs)
  apply(auto)
done

lemma drop_1_tl: "drop 1 xs = tl xs"
  apply(induct xs)
  apply(auto)
done

lemma remove1_tl: "xs \<noteq> [] \<Longrightarrow> remove1 (hd xs) xs = tl xs"
  apply(induct xs, simp)
  apply(auto)
done

lemma sorted_append_bigger: 
  "\<lbrakk>sorted xs; \<forall>x \<in> set xs. x \<le> y\<rbrakk> \<Longrightarrow> sorted (xs @ [y])"
  apply (induct xs)
  apply simp
proof -
  case goal1
  from goal1 have s: "sorted xs" by (cases xs) simp_all
  from goal1 have a: "\<forall>x\<in>set xs. x \<le> y" by simp
  from goal1(1)[OF s a] goal1(2-) show ?case by (cases xs) simp_all
qed









fun remove_rev where
   "remove_rev a x [] = a"
 | "remove_rev a x (y # xs) =
    remove_rev (if x = y then a else (y # a)) x xs"

lemma remove_rev_alt_def :
  "remove_rev a x xs = (filter (\<lambda>y. y \<noteq> x) (rev xs)) @ a"
by (induct xs arbitrary: a) auto

subsection {* Implementation of Mergesort *}

fun merge :: "'a::{linorder} list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
   "merge [] l2 = l2"
 | "merge l1 [] = l1"
 | "merge (x1 # l1) (x2 # l2) =
    (if (x1 < x2) then x1 # (merge l1 (x2 # l2)) else 
     (if (x1 = x2) then x1 # (merge l1 l2) else x2 # (merge (x1 # l1) l2)))"

lemma merge_correct :
assumes l1_OK: "distinct l1 \<and> sorted l1"
assumes l2_OK: "distinct l2 \<and> sorted l2"
shows "distinct (merge l1 l2) \<and> sorted (merge l1 l2) \<and> set (merge l1 l2) = set l1 \<union> set l2"
using assms
proof (induct l1 arbitrary: l2) 
  case Nil thus ?case by simp
next
  case (Cons x1 l1 l2) 
  note x1_l1_props = Cons(2)
  note l2_props = Cons(3)

  from x1_l1_props have l1_props: "distinct l1 \<and> sorted l1"
                    and x1_nin_l1: "x1 \<notin> set l1"
                    and x1_le: "\<And>x. x \<in> set l1 \<Longrightarrow> x1 \<le> x"
    by (simp_all add: sorted_Cons Ball_def)

  note ind_hyp_l1 = Cons(1)[OF l1_props]

  show ?case
  using l2_props 
  proof (induct l2)
    case Nil with x1_l1_props show ?case by simp
  next
    case (Cons x2 l2)
    note x2_l2_props = Cons(2)
    from x2_l2_props have l2_props: "distinct l2 \<and> sorted l2"
                    and x2_nin_l2: "x2 \<notin> set l2"
                    and x2_le: "\<And>x. x \<in> set l2 \<Longrightarrow> x2 \<le> x"
    by (simp_all add: sorted_Cons Ball_def)

    note ind_hyp_l2 = Cons(1)[OF l2_props]
    show ?case
    proof (cases "x1 < x2")
      case True note x1_less_x2 = this

      from ind_hyp_l1[OF x2_l2_props] x1_less_x2 x1_nin_l1 x1_le x2_le
      show ?thesis
        apply (auto simp add: sorted_Cons Ball_def)
        apply (metis linorder_not_le)
        apply (metis linorder_not_less xt1(6) xt1(9))
      done
    next
      case False note x2_le_x1 = this
      
      show ?thesis
      proof (cases "x1 = x2")
        case True note x1_eq_x2 = this

        from ind_hyp_l1[OF l2_props] x1_le x2_le x2_nin_l2 x1_eq_x2 x1_nin_l1
        show ?thesis by (simp add: x1_eq_x2 sorted_Cons Ball_def)
      next
        case False note x1_neq_x2 = this
        with x2_le_x1 have x2_less_x1 : "x2 < x1" by auto

        from ind_hyp_l2 x2_le_x1 x1_neq_x2 x2_le x2_nin_l2 x1_le
        show ?thesis 
          apply (simp add: x2_less_x1 sorted_Cons Ball_def)
          apply (metis linorder_not_le x2_less_x1 xt1(7))
        done
      qed
    qed
  qed
qed

function merge_list :: "'a::{linorder} list list \<Rightarrow> 'a list list \<Rightarrow> 'a list" where
   "merge_list [] [] = []"
 | "merge_list [] [l] = l"
 | "merge_list (la # acc2) [] = merge_list [] (la # acc2)"
 | "merge_list (la # acc2) [l] = merge_list [] (l # la # acc2)"
 | "merge_list acc2 (l1 # l2 # ls) = 
    merge_list ((merge l1 l2) # acc2) ls"
by pat_completeness simp_all
termination
by (relation "measure (\<lambda>(acc, ls). 3 * length acc + 2 * length ls)") (simp_all)

lemma merge_list_correct :
assumes ls_OK: "\<And>l. l \<in> set ls \<Longrightarrow> distinct l \<and> sorted l"
assumes as_OK: "\<And>l. l \<in> set as \<Longrightarrow> distinct l \<and> sorted l"
shows "distinct (merge_list as ls) \<and> sorted (merge_list as ls) \<and> 
       set (merge_list as ls) = set (concat (as @ ls))"
using assms
proof (induct as ls rule: merge_list.induct)
  case 1 thus ?case by simp
next
  case 2 thus ?case by simp
next
  case 3 thus ?case by simp
next
  case 4 thus ?case by auto
next
  case (5 acc l1 l2 ls) 
  note ind_hyp = 5(1) 
  note l12_l_OK = 5(2)
  note acc_OK = 5(3)

  from l12_l_OK acc_OK merge_correct[of l1 l2]
    have set_merge_eq: "set (merge l1 l2) = set l1 \<union> set l2" by auto

  from l12_l_OK acc_OK merge_correct[of l1 l2]
  have "distinct (merge_list (merge l1 l2 # acc) ls) \<and>
        sorted (merge_list (merge l1 l2 # acc) ls) \<and>
        set (merge_list (merge l1 l2 # acc) ls) =
        set (concat ((merge l1 l2 # acc) @ ls))"
    by (rule_tac ind_hyp) auto
  with set_merge_eq show ?case by auto
qed


definition mergesort where
  "mergesort xs = merge_list [] (map (\<lambda>x. [x]) xs)"

lemma mergesort_correct :
  "distinct (mergesort l) \<and> sorted (mergesort l) \<and> (set (mergesort l) = set l)"
proof -
  let ?l' = "map (\<lambda>x. [x]) l"

  { fix xs
    assume "xs \<in> set ?l'"
    then obtain x where xs_eq: "xs = [x]" by auto 
    hence "distinct xs \<and> sorted xs" by simp
  } note l'_OK = this

  from merge_list_correct[of "?l'" "[]", OF l'_OK]
  show ?thesis unfolding mergesort_def by simp
qed


subsection {* Operations on sorted Lists *}

fun inter_sorted :: "'a::{linorder} list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
   "inter_sorted [] l2 = []"
 | "inter_sorted l1 [] = []"
 | "inter_sorted (x1 # l1) (x2 # l2) =
    (if (x1 < x2) then (inter_sorted l1 (x2 # l2)) else 
     (if (x1 = x2) then x1 # (inter_sorted l1 l2) else inter_sorted (x1 # l1) l2))"

lemma inter_sorted_correct :
assumes l1_OK: "distinct l1 \<and> sorted l1"
assumes l2_OK: "distinct l2 \<and> sorted l2"
shows "distinct (inter_sorted l1 l2) \<and> sorted (inter_sorted l1 l2) \<and> 
       set (inter_sorted l1 l2) = set l1 \<inter> set l2"
using assms
proof (induct l1 arbitrary: l2) 
  case Nil thus ?case by simp
next
  case (Cons x1 l1 l2) 
  note x1_l1_props = Cons(2)
  note l2_props = Cons(3)

  from x1_l1_props have l1_props: "distinct l1 \<and> sorted l1"
                    and x1_nin_l1: "x1 \<notin> set l1"
                    and x1_le: "\<And>x. x \<in> set l1 \<Longrightarrow> x1 \<le> x"
    by (simp_all add: sorted_Cons Ball_def)

  note ind_hyp_l1 = Cons(1)[OF l1_props]

  show ?case
  using l2_props 
  proof (induct l2)
    case Nil with x1_l1_props show ?case by simp
  next
    case (Cons x2 l2)
    note x2_l2_props = Cons(2)
    from x2_l2_props have l2_props: "distinct l2 \<and> sorted l2"
                    and x2_nin_l2: "x2 \<notin> set l2"
                    and x2_le: "\<And>x. x \<in> set l2 \<Longrightarrow> x2 \<le> x"
    by (simp_all add: sorted_Cons Ball_def)

    note ind_hyp_l2 = Cons(1)[OF l2_props]
    show ?case
    proof (cases "x1 < x2")
      case True note x1_less_x2 = this

      from ind_hyp_l1[OF x2_l2_props] x1_less_x2 x1_nin_l1 x1_le x2_le
      show ?thesis
        apply (auto simp add: sorted_Cons Ball_def)
        apply (metis linorder_not_le)
      done
    next
      case False note x2_le_x1 = this
      
      show ?thesis
      proof (cases "x1 = x2")
        case True note x1_eq_x2 = this

        from ind_hyp_l1[OF l2_props] x1_le x2_le x2_nin_l2 x1_eq_x2 x1_nin_l1
        show ?thesis by (simp add: x1_eq_x2 sorted_Cons Ball_def)
      next
        case False note x1_neq_x2 = this
        with x2_le_x1 have x2_less_x1 : "x2 < x1" by auto

        from ind_hyp_l2 x2_le_x1 x1_neq_x2 x2_le x2_nin_l2 x1_le
        show ?thesis 
          apply (auto simp add: x2_less_x1 sorted_Cons Ball_def)
          apply (metis linorder_not_le x2_less_x1)
        done
      qed
    qed
  qed
qed

fun diff_sorted :: "'a::{linorder} list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
   "diff_sorted [] l2 = []"
 | "diff_sorted l1 [] = l1"
 | "diff_sorted (x1 # l1) (x2 # l2) =
    (if (x1 < x2) then x1 # (diff_sorted l1 (x2 # l2)) else 
     (if (x1 = x2) then (diff_sorted l1 l2) else diff_sorted (x1 # l1) l2))"

lemma diff_sorted_correct :
assumes l1_OK: "distinct l1 \<and> sorted l1"
assumes l2_OK: "distinct l2 \<and> sorted l2"
shows "distinct (diff_sorted l1 l2) \<and> sorted (diff_sorted l1 l2) \<and> 
       set (diff_sorted l1 l2) = set l1 - set l2"
using assms
proof (induct l1 arbitrary: l2) 
  case Nil thus ?case by simp
next
  case (Cons x1 l1 l2) 
  note x1_l1_props = Cons(2)
  note l2_props = Cons(3)

  from x1_l1_props have l1_props: "distinct l1 \<and> sorted l1"
                    and x1_nin_l1: "x1 \<notin> set l1"
                    and x1_le: "\<And>x. x \<in> set l1 \<Longrightarrow> x1 \<le> x"
    by (simp_all add: sorted_Cons Ball_def)

  note ind_hyp_l1 = Cons(1)[OF l1_props]

  show ?case
  using l2_props 
  proof (induct l2)
    case Nil with x1_l1_props show ?case by simp
  next
    case (Cons x2 l2)
    note x2_l2_props = Cons(2)
    from x2_l2_props have l2_props: "distinct l2 \<and> sorted l2"
                    and x2_nin_l2: "x2 \<notin> set l2"
                    and x2_le: "\<And>x. x \<in> set l2 \<Longrightarrow> x2 \<le> x"
    by (simp_all add: sorted_Cons Ball_def)

    note ind_hyp_l2 = Cons(1)[OF l2_props]
    show ?case
    proof (cases "x1 < x2")
      case True note x1_less_x2 = this

      from ind_hyp_l1[OF x2_l2_props] x1_less_x2 x1_nin_l1 x1_le x2_le
      show ?thesis
        apply simp
        apply (simp add: sorted_Cons Ball_def set_eq_iff)
        apply (metis linorder_not_le order_less_imp_not_eq2)
      done
    next
      case False note x2_le_x1 = this
      
      show ?thesis
      proof (cases "x1 = x2")
        case True note x1_eq_x2 = this

        from ind_hyp_l1[OF l2_props] x1_le x2_le x2_nin_l2 x1_eq_x2 x1_nin_l1
        show ?thesis by (simp add: x1_eq_x2 sorted_Cons Ball_def)
      next
        case False note x1_neq_x2 = this
        with x2_le_x1 have x2_less_x1 : "x2 < x1" by auto

        from x2_less_x1 x1_le have x2_nin_l1: "x2 \<notin> set l1"
           by (metis linorder_not_less)

        from ind_hyp_l2 x1_le x2_nin_l1
        show ?thesis 
          apply (simp add: x2_less_x1 x1_neq_x2 x2_le_x1 x1_nin_l1 sorted_Cons Ball_def set_eq_iff)
          apply (metis x1_neq_x2)
        done
      qed
    qed
  qed
qed

fun subset_sorted :: "'a::{linorder} list \<Rightarrow> 'a list \<Rightarrow> bool" where
   "subset_sorted [] l2 = True"
 | "subset_sorted (x1 # l1) [] = False"
 | "subset_sorted (x1 # l1) (x2 # l2) =
    (if (x1 < x2) then False else 
     (if (x1 = x2) then (subset_sorted l1 l2) else subset_sorted (x1 # l1) l2))"

lemma subset_sorted_correct :
assumes l1_OK: "distinct l1 \<and> sorted l1"
assumes l2_OK: "distinct l2 \<and> sorted l2"
shows "subset_sorted l1 l2 \<longleftrightarrow> set l1 \<subseteq> set l2"
using assms
proof (induct l1 arbitrary: l2) 
  case Nil thus ?case by simp
next
  case (Cons x1 l1 l2) 
  note x1_l1_props = Cons(2)
  note l2_props = Cons(3)

  from x1_l1_props have l1_props: "distinct l1 \<and> sorted l1"
                    and x1_nin_l1: "x1 \<notin> set l1"
                    and x1_le: "\<And>x. x \<in> set l1 \<Longrightarrow> x1 \<le> x"
    by (simp_all add: sorted_Cons Ball_def)

  note ind_hyp_l1 = Cons(1)[OF l1_props]

  show ?case
  using l2_props 
  proof (induct l2)
    case Nil with x1_l1_props show ?case by simp
  next
    case (Cons x2 l2)
    note x2_l2_props = Cons(2)
    from x2_l2_props have l2_props: "distinct l2 \<and> sorted l2"
                    and x2_nin_l2: "x2 \<notin> set l2"
                    and x2_le: "\<And>x. x \<in> set l2 \<Longrightarrow> x2 \<le> x"
    by (simp_all add: sorted_Cons Ball_def)

    note ind_hyp_l2 = Cons(1)[OF l2_props]
    show ?case
    proof (cases "x1 < x2")
      case True note x1_less_x2 = this

      from ind_hyp_l1[OF x2_l2_props] x1_less_x2 x1_nin_l1 x1_le x2_le
      show ?thesis
        apply (auto simp add: sorted_Cons Ball_def)
        apply (metis linorder_not_le)
      done
    next
      case False note x2_le_x1 = this
      
      show ?thesis
      proof (cases "x1 = x2")
        case True note x1_eq_x2 = this

        from ind_hyp_l1[OF l2_props] x1_le x2_le x2_nin_l2 x1_eq_x2 x1_nin_l1
        show ?thesis 
          apply (simp add: subset_iff x1_eq_x2 sorted_Cons Ball_def)
          apply metis
        done
      next
        case False note x1_neq_x2 = this
        with x2_le_x1 have x2_less_x1 : "x2 < x1" by auto

        from ind_hyp_l2 x2_le_x1 x1_neq_x2 x2_le x2_nin_l2 x1_le
        show ?thesis 
          apply (simp add: subset_iff x2_less_x1 sorted_Cons Ball_def)
          apply (metis linorder_not_le x2_less_x1)
        done
      qed
    qed
  qed
qed

lemma set_eq_sorted_correct :
  assumes l1_OK: "distinct l1 \<and> sorted l1"
  assumes l2_OK: "distinct l2 \<and> sorted l2"
  shows "l1 = l2 \<longleftrightarrow> set l1 = set l2"
  using assms
proof -
  have l12_eq: "l1 = l2 \<longleftrightarrow> subset_sorted l1 l2 \<and> subset_sorted l2 l1"
  proof (induct l1 arbitrary: l2)
    case Nil thus ?case by (cases l2) auto
  next
    case (Cons x1 l1')
    note ind_hyp = Cons(1)

    show ?case
    proof (cases l2)
      case Nil thus ?thesis by simp
    next
      case (Cons x2 l2')
      thus ?thesis by (simp add: ind_hyp)
    qed
  qed
  also have "\<dots> \<longleftrightarrow> ((set l1 \<subseteq> set l2) \<and> (set l2 \<subseteq> set l1))"
    using subset_sorted_correct[OF l1_OK l2_OK] subset_sorted_correct[OF l2_OK l1_OK]
    by simp
  also have "\<dots> \<longleftrightarrow> set l1 = set l2" by auto
  finally show ?thesis .
qed

fun memb_sorted where
   "memb_sorted [] x = False"
 | "memb_sorted (y # xs) x =
    (if (y < x) then memb_sorted xs x else (x = y))"

lemma memb_sorted_correct :
  "sorted xs \<Longrightarrow> memb_sorted xs x \<longleftrightarrow> x \<in> set xs"
by (induct xs) (auto simp add: sorted_Cons Ball_def)


fun insertion_sort where
   "insertion_sort x [] = [x]"
 | "insertion_sort x (y # xs) =
    (if (y < x) then y # insertion_sort x xs else 
     (if (x = y) then y # xs else x # y # xs))"

lemma insertion_sort_correct :
  "sorted xs \<Longrightarrow> distinct xs \<Longrightarrow>
   distinct (insertion_sort x xs) \<and> 
   sorted (insertion_sort x xs) \<and>
   set (insertion_sort x xs) = set (x # xs)"
by (induct xs) (auto simp add: sorted_Cons Ball_def)

fun delete_sorted where
   "delete_sorted x [] = []"
 | "delete_sorted x (y # xs) =
    (if (y < x) then y # delete_sorted x xs else 
     (if (x = y) then xs else y # xs))"

lemma delete_sorted_correct :
  "sorted xs \<Longrightarrow> distinct xs \<Longrightarrow>
   distinct (delete_sorted x xs) \<and> 
   sorted (delete_sorted x xs) \<and>
   set (delete_sorted x xs) = set xs - {x}"
apply (induct xs) 
apply simp
apply (simp add: sorted_Cons Ball_def set_eq_iff)
apply (metis order_less_le)
done

(* TODO: Misc *)
lemma sorted_filter :
  "sorted l \<Longrightarrow> sorted (filter P l)"
by (induct l) (simp_all add: sorted_Cons)

end
