theory Basic_Utils
  imports Term_Context
begin

primrec is_Inl where
  "is_Inl (Inl q) \<longleftrightarrow> True"
| "is_Inl (Inr q) \<longleftrightarrow> False"

primrec is_Inr where
  "is_Inr (Inr q) \<longleftrightarrow> True"
| "is_Inr (Inl q) \<longleftrightarrow> False"

fun remove_sum where
  "remove_sum (Inl q) = q"
| "remove_sum (Inr q) = q"


text \<open>List operations\<close>

definition filter_rev_nth where
  "filter_rev_nth P xs i = length (filter P (take (Suc i) xs)) - 1"

lemma filter_rev_nth_butlast:
  "\<not> P (last xs) \<Longrightarrow> filter_rev_nth P xs i = filter_rev_nth P (butlast xs) i"
  unfolding filter_rev_nth_def
  by (induct xs arbitrary: i rule: rev_induct) (auto simp add: take_Cons')

lemma filter_rev_nth_idx:
  assumes "i < length xs" "P (xs ! i)" "ys = filter P xs"
  shows "xs ! i = ys ! (filter_rev_nth P xs i) \<and> filter_rev_nth P xs i < length ys"
  using assms unfolding filter_rev_nth_def
proof (induct xs arbitrary: ys i)
  case (Cons x xs) show ?case
  proof (cases "P x")
    case True
    then obtain ys' where *:"ys = x # ys'" using Cons(4) by auto
    show ?thesis using True Cons(1)[of "i - 1" ys'] Cons(2-)
      unfolding *
      by (cases i) (auto simp: nth_Cons' take_Suc_conv_app_nth)
  next
    case False
    then show ?thesis using Cons(1)[of "i - 1" ys] Cons(2-)
      by (auto simp: nth_Cons')
  qed
qed auto


(*replace list_of_permutation_n with n_lists *)

primrec add_elem_list_lists :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list list" where
  "add_elem_list_lists x [] = [[x]]"
| "add_elem_list_lists x (y # ys) = (x # y # ys) # (map ((#) y) (add_elem_list_lists x ys))"

lemma length_add_elem_list_lists:
  "ys \<in> set (add_elem_list_lists x xs) \<Longrightarrow> length ys = Suc (length xs)"
  by (induct xs arbitrary: ys) auto

lemma add_elem_list_listsE:
  assumes "ys \<in> set (add_elem_list_lists x xs)"
  shows "\<exists> n \<le> length xs. ys = take n xs @ x # drop n xs" using assms
proof(induct xs arbitrary: ys)
  case (Cons a xs)
  then show ?case
    by auto fastforce
qed auto

lemma add_elem_list_listsI:
  assumes "n \<le> length xs" "ys = take n xs @ x # drop n xs"
  shows "ys \<in> set (add_elem_list_lists x xs)" using assms
proof  (induct xs arbitrary: ys n)
  case (Cons a xs)
  then show ?case
    by (cases n) (auto simp: image_iff) 
qed auto

lemma add_elem_list_lists_def':
  "set (add_elem_list_lists x xs) = {ys | ys n. n \<le> length xs \<and> ys = take n xs @ x # drop n xs}"
  using add_elem_list_listsI add_elem_list_listsE
  by fastforce

fun list_of_permutation_element_n :: "'a \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> 'a list list" where
  "list_of_permutation_element_n x 0 L = [[]]"
|  "list_of_permutation_element_n x (Suc n) L = concat (map (add_elem_list_lists x) (List.n_lists n L))"

lemma list_of_permutation_element_n_conv:
  assumes "n \<noteq> 0"
  shows "set (list_of_permutation_element_n x n L) =
    {xs | xs i. i < length xs \<and> (\<forall> j < length xs. j \<noteq> i \<longrightarrow> xs ! j \<in> set L) \<and> length xs = n \<and> xs ! i = x}" (is "?Ls = ?Rs")
proof (intro equalityI)
  from assms obtain j where [simp]: "n = Suc j" using assms by (cases n) auto
  {fix ys assume "ys \<in> ?Ls"
    then obtain xs i where wit: "xs \<in> set (List.n_lists j L)" "i \<le> length xs"
      "ys = take i xs @ x # drop i xs"
      by (auto dest: add_elem_list_listsE)
    then have "i < length ys" "length ys = Suc (length xs)" "ys ! i = x"
      by (auto simp: nth_append)
    moreover have "\<forall> j < length ys. j \<noteq> i \<longrightarrow> ys ! j \<in> set L" using wit(1, 2)
      by (auto simp: wit(3) min_def nth_append set_n_lists)
    ultimately have "ys \<in> ?Rs" using wit(1) unfolding set_n_lists
      by auto}
  then show "?Ls \<subseteq> ?Rs" by blast
next
  {fix xs assume "xs \<in> ?Rs"
    then obtain i where wit: "i < length xs" "\<forall> j < length xs. j \<noteq> i \<longrightarrow> xs ! j \<in> set L"
      "length xs = n" "xs ! i = x"
      by blast
    then have *: "xs \<in> set (add_elem_list_lists (xs ! i) (take i xs @ drop (Suc i) xs))"
      unfolding add_elem_list_lists_def'
      by (auto simp: min_def intro!: nth_equalityI)
         (metis Cons_nth_drop_Suc Suc_pred append_Nil append_take_drop_id assms diff_le_self diff_self_eq_0 drop_take less_Suc_eq_le nat_less_le take0)
    have [simp]: "x \<in> set (take i xs) \<Longrightarrow> x \<in> set L" 
      "x \<in> set (drop (Suc i) xs) \<Longrightarrow> x \<in> set L" for x using wit(2)
      by (auto simp: set_conv_nth)
    have "xs \<in> ?Ls" using wit
      by (cases "length xs")
         (auto simp: set_n_lists nth_append * min_def
               intro!: exI[of _ "take i xs @ drop (Suc i) xs"])}
  then show "?Rs \<subseteq> ?Ls" by blast
qed

lemma list_of_permutation_element_n_iff:
  "set (list_of_permutation_element_n x n L) =
    (if n = 0 then {[]} else {xs | xs i. i < length xs \<and> (\<forall> j < length xs. j \<noteq> i \<longrightarrow> xs ! j \<in> set L) \<and> length xs = n \<and> xs ! i = x})"
proof (cases n)
  case (Suc nat)
  then have [simp]: "Suc nat \<noteq> 0" by auto
  then show ?thesis
    by (auto simp: list_of_permutation_element_n_conv)
qed auto

lemma list_of_permutation_element_n_conv':
  assumes "x \<in> set L" "0 < n"
  shows "set (list_of_permutation_element_n x n L) =
      {xs. set xs \<subseteq> insert x (set L) \<and> length xs = n \<and> x \<in> set xs}"
proof -
  from assms(2) have *: "n \<noteq> 0" by simp
  show ?thesis using assms
    unfolding list_of_permutation_element_n_conv[OF *]
    by (auto simp: in_set_conv_nth) 
       (metis in_set_conv_nth insert_absorb subsetD)+
qed

text \<open>Misc\<close>

lemma in_set_idx:
  "x \<in> set xs \<Longrightarrow> \<exists> i < length xs. xs ! i = x"
  by (induct xs) force+

lemma set_list_subset_eq_nth_conv:
  "set xs \<subseteq> A \<longleftrightarrow> (\<forall> i < length xs. xs ! i \<in> A)"
  by (metis in_set_conv_nth subset_code(1))

lemma map_eq_nth_conv:
  "map f xs = map g ys \<longleftrightarrow> length xs = length ys \<and> (\<forall> i < length ys. f (xs ! i) = g (ys ! i))"
  using map_eq_imp_length_eq[of f xs g ys]
  by (auto intro: nth_equalityI) (metis nth_map)

lemma nth_append_Cons: "(xs @ y # zs) ! i =
  (if i < length xs then xs ! i else if i = length xs then y else zs ! (i - Suc (length xs)))"
  by (cases i "length xs" rule: linorder_cases, auto simp: nth_append)

lemma map_prod_times:
  "f ` A \<times> g ` B = map_prod f g ` (A \<times> B)"
  by auto

lemma trancl_full_on: "(X \<times> X)\<^sup>+ = X \<times> X"
  using trancl_unfold_left[of "X \<times> X"] trancl_unfold_right[of "X \<times> X"] by auto

lemma trancl_map:
  assumes simu: "\<And>x y. (x, y) \<in> r \<Longrightarrow> (f x, f y) \<in> s"
    and steps: "(x, y) \<in> r\<^sup>+"
  shows "(f x, f y) \<in> s\<^sup>+" using steps
proof (induct)
  case (step y z) show ?case using step(3) simu[OF step(2)] 
    by auto
qed (auto simp: simu)

lemma trancl_map_prod_mono:
  "map_both f ` R\<^sup>+ \<subseteq> (map_both f ` R)\<^sup>+"
proof -
  have "(f x, f y) \<in> (map_both f ` R)\<^sup>+" if "(x, y) \<in> R\<^sup>+" for x y using that
    by (induct) (auto intro: trancl_into_trancl)
  then show ?thesis by auto
qed

lemma trancl_map_both_Restr:
  assumes "inj_on f X"
  shows "(map_both f ` Restr R X)\<^sup>+ = map_both f ` (Restr R X)\<^sup>+"
proof -
  have [simp]:
    "map_prod (inv_into X f \<circ> f) (inv_into X f \<circ> f) ` Restr R X = Restr R X"
    using inv_into_f_f[OF assms]
    by (intro equalityI subrelI)
       (force simp: comp_def map_prod_def image_def split: prod.splits)+
  have [simp]:
    "map_prod (f \<circ> inv_into X f) (f \<circ> inv_into X f) ` (map_both f ` Restr R X)\<^sup>+ = (map_both f ` Restr R X)\<^sup>+"
    using f_inv_into_f[of _ f X] subsetD[OF trancl_mono_set[OF image_mono[of "Restr R X" "X \<times> X" "map_both f"]]]
    by (intro equalityI subrelI) (auto simp: map_prod_surj_on trancl_full_on comp_def rev_image_eqI)
  show ?thesis using assms trancl_map_prod_mono[of f "Restr R X"]
      image_mono[OF trancl_map_prod_mono[of "inv_into X f" "map_both f ` Restr R X"], of "map_both f"]
    by (intro equalityI) (simp_all add: image_comp map_prod.comp)
qed

lemma inj_on_trancl_map_both:
  assumes "inj_on f (fst ` R \<union> snd ` R)"
  shows "(map_both f ` R)\<^sup>+ = map_both f ` R\<^sup>+"
proof -
  have [simp]: "Restr R (fst ` R \<union> snd ` R) = R"
    by (force simp: image_def)
  then show ?thesis using assms
    using trancl_map_both_Restr[of f "fst ` R \<union> snd ` R" R]
    by simp
qed


lemma kleene_induct:
  "A \<subseteq> X \<Longrightarrow> B O X \<subseteq> X \<Longrightarrow> X O C \<subseteq> X \<Longrightarrow> B\<^sup>* O A O C\<^sup>* \<subseteq> X"
  using relcomp_mono[OF compat_tr_compat[of B X] subset_refl, of "C\<^sup>*"] compat_tr_compat[of "C\<inverse>" "X\<inverse>"]
    relcomp_mono[OF relcomp_mono, OF subset_refl _ subset_refl, of A X "B\<^sup>*" "C\<^sup>*"]
  unfolding rtrancl_converse converse_relcomp[symmetric] converse_mono by blast

lemma kleene_trancl_induct:
  "A \<subseteq> X \<Longrightarrow> B O X \<subseteq> X \<Longrightarrow> X O C \<subseteq> X \<Longrightarrow> B\<^sup>+ O A O C\<^sup>+ \<subseteq> X"
  using kleene_induct[of A X B C]
  by (auto simp: rtrancl_eq_or_trancl)
     (meson relcomp.relcompI subsetD trancl_into_rtrancl)

lemma rtrancl_Un2_separatorE:
  "B O A = {} \<Longrightarrow> (A \<union> B)\<^sup>* = A\<^sup>* \<union> A\<^sup>* O B\<^sup>*"
  by (metis R_O_Id empty_subsetI relcomp_distrib rtrancl_U_push rtrancl_reflcl_absorb sup_commute)

lemma trancl_Un2_separatorE:
  assumes "B O A = {}"
  shows "(A \<union> B)\<^sup>+ = A\<^sup>+ \<union> A\<^sup>+ O B\<^sup>+ \<union> B\<^sup>+" (is "?Ls = ?Rs")
proof -
  {fix x y assume "(x, y) \<in> ?Ls"
    then have "(x, y) \<in> ?Rs" using assms
    proof (induct)
      case (step y z)
      then show ?case
        by (auto simp add: trancl_into_trancl relcomp_unfold dest: tranclD2)
    qed auto}
  then show ?thesis
    by (auto simp add: trancl_mono)
       (meson sup_ge1 sup_ge2 trancl_mono trancl_trans)
qed

text \<open>Sum types where both components have the same type (to create copies)\<close>

lemma is_InrE:
  assumes "is_Inr q"
  obtains p where "q = Inr p"
  using assms by (cases q) auto

lemma is_InlE:
  assumes "is_Inl q"
  obtains p where "q = Inl p"
  using assms by (cases q) auto

lemma not_is_Inr_is_Inl [simp]:
  "\<not> is_Inl t \<longleftrightarrow> is_Inr t"
  "\<not> is_Inr t \<longleftrightarrow> is_Inl t"
  by (cases t, auto)+

lemma [simp]: "remove_sum \<circ> Inl = id" by auto

abbreviation CInl :: "'q \<Rightarrow> 'q + 'q" where "CInl \<equiv> Inl"
abbreviation CInr :: "'q \<Rightarrow> 'q + 'q" where "CInr \<equiv> Inr"

lemma inj_CInl: "inj CInl" "inj CInr" using inj_Inl inj_Inr by blast+

lemma map_prod_simp': "map_prod f g G = (f (fst G), g (snd G))"
  by (auto simp add: map_prod_def split!: prod.splits)

end