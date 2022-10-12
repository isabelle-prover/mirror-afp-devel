(* Author: Bernhard Stöckl *)

theory CostFunctions
  imports Complex_Main JoinTree Selectivities
begin

section \<open>Cost Functions\<close>

subsection \<open>General Cost Functions\<close>

fun c_out :: "'a card \<Rightarrow> 'a selectivity \<Rightarrow> 'a joinTree \<Rightarrow> real" where
  "c_out _ _ (Relation _) = 0"
| "c_out cf f (Join l r) = card cf f (Join l r) + c_out cf f l + c_out cf f r"

fun c_nlj :: "'a card \<Rightarrow> 'a selectivity \<Rightarrow> 'a joinTree \<Rightarrow> real" where
  "c_nlj _ _ (Relation _) = 0"
| "c_nlj cf f (Join l r) = card cf f l * card cf f r + c_nlj cf f l + c_nlj cf f r"

fun c_hj :: "'a card \<Rightarrow> 'a selectivity \<Rightarrow> 'a joinTree \<Rightarrow> real" where
  "c_hj _ _ (Relation _) = 0"
| "c_hj cf f (Join l r) = 1.2 * card cf f l + c_hj cf f l + c_hj cf f r"

fun c_smj :: "'a card \<Rightarrow> 'a selectivity \<Rightarrow> 'a joinTree \<Rightarrow> real" where
  "c_smj _ _ (Relation _) = 0"
| "c_smj cf f (Join l r) = card cf f l * log 2 (card cf f l) + card cf f r * log 2 (card cf f r)
    + c_smj cf f l + c_smj cf f r"

subsection \<open>Cost functions that are considered by IKKBZ.\<close>

fun c_IKKBZ :: "('a \<Rightarrow> real \<Rightarrow> real) \<Rightarrow> 'a card \<Rightarrow> 'a selectivity \<Rightarrow> 'a joinTree \<Rightarrow> real" where
  "c_IKKBZ _ _ _ (Relation _) = 0"
| "c_IKKBZ h cf f (Join l (Relation rel)) = card cf f l * (h rel (cf rel)) + c_IKKBZ h cf f l"
| "c_IKKBZ _ _ _ (Join l r) = undefined"

text \<open>
  A list of relations defines a unique left-deep tree. This functions computes a cost function
  given by such a list representation of a tree according to the formula
  @{text "\<Sum>\<^sub>i\<^sub>=\<^sub>2\<^sup>n n\<^sub>{\<^sub>1\<^sub>,\<^sub>2\<^sub>,\<^sub>\<dots>\<^sub>i\<^sub>-\<^sub>1\<^sub>} h\<^sub>i(n\<^sub>i)"}
  where @{text "n\<^sub>{\<^sub>1\<^sub>,\<^sub>2\<^sub>,\<^sub>\<dots>\<^sub>i\<^sub>-\<^sub>1\<^sub>}"} = @{term "card subtree"} = @{term "ldeep_n f cf"} (list subtree)
  The input list is expected to be in reversed order for easier recursive processing
  i.e. the first element in xs is the rightmost element of the left-deep tree
\<close>

fun c_list' :: "'a selectivity \<Rightarrow> 'a card \<Rightarrow> ('a list \<Rightarrow> 'a \<Rightarrow> real) \<Rightarrow> 'a list \<Rightarrow> real" where
  "c_list' _ _ _ [] = 0"
| "c_list' _ _ _ [x] = 0"
| "c_list' f cf h (x#xs) = ldeep_n f cf xs * h xs x + c_list' f cf h xs"

text \<open>
  Equivalent definition which allows splitting the list at any point.
\<close>
fun c_list :: "('a \<Rightarrow> real) \<Rightarrow> 'a card \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> real" where
  "c_list _ _ _ _ [] = 0"
| "c_list _ _ h r [x] = (if x=r then 0 else h x)"
| "c_list sf cf h r (x#xs) = c_list sf cf h r xs + ldeep_T sf cf xs * c_list sf cf h r [x]"

text \<open>
  Maps the h function to a static version that doesn't require an input list.
\<close>
fun create_h_list :: "('a list \<Rightarrow> 'a \<Rightarrow> real) \<Rightarrow> 'a list \<Rightarrow> 'a \<Rightarrow> real" where
  "create_h_list _ [] = (\<lambda>_. 1)"
| "create_h_list h (x#xs) = (\<lambda>a. if a=x then h xs x else create_h_list h xs a)"

subsection \<open>Properties of Cost Functions\<close>

definition symmetric :: "('a joinTree \<Rightarrow> real) \<Rightarrow> bool" where
  "symmetric f = (\<forall>x y. f (Join x y) = f (Join y x))"

definition symmetric' :: "('a card \<Rightarrow> 'a selectivity \<Rightarrow> 'a joinTree \<Rightarrow> real) \<Rightarrow> bool" where
  "symmetric' f = (\<forall>x y cf sf. sel_symm sf \<longrightarrow> (f cf sf (Join x y) = f cf sf (Join y x)))"

text \<open>
  Uses reversed lists since the last joined relation should only appear once. Therefore, it should
  be the head of the list and by inductive reasoning the list should be reversed.
  Furthermore, the root must be the first relation in the sequence (last in the reverse) or it must
  not be contained at all.
\<close>
definition asi' :: "'a \<Rightarrow> ('a list \<Rightarrow> real) \<Rightarrow> bool" where
  "asi' r c = (\<exists>rank :: ('a list \<Rightarrow> real).
    (\<forall>A U V B. distinct (A@U@V@B) \<and> U \<noteq> [] \<and> V \<noteq> []
      \<and> (r \<notin> set (A@U@V@B) \<or> (take 1 (A@U@V@B) = [r] \<and> take 1 (A@V@U@B) = [r]))
      \<longrightarrow> (c (rev (A@U@V@B)) \<le> c (rev (A@V@U@B)) \<longleftrightarrow> rank (rev U) \<le> rank (rev V))))"

definition asi :: "('a list \<Rightarrow> real) \<Rightarrow> 'a \<Rightarrow> ('a list \<Rightarrow> real) \<Rightarrow> bool" where
  "asi rank r c = (\<forall>A U V B. distinct (A@U@V@B) \<and> U \<noteq> [] \<and> V \<noteq> []
      \<and> (r \<notin> set (A@U@V@B) \<or> (take 1 (A@U@V@B) = [r] \<and> take 1 (A@V@U@B) = [r]))
      \<longrightarrow> (c (rev (A@U@V@B)) \<le> c (rev (A@V@U@B)) \<longleftrightarrow> rank (rev U) \<le> rank (rev V)))"

(* alternative asi definition with slightly changed preconditions related for r *)
definition asi'' :: "('a list \<Rightarrow> real) \<Rightarrow> 'a \<Rightarrow> ('a list \<Rightarrow> real) \<Rightarrow> bool" where
  "asi'' rank r c = ((\<forall>A U V B. distinct (A@U@V@B) \<and> U \<noteq> [] \<and> V \<noteq> [] \<and> U \<noteq> [r] \<and> V \<noteq> [r]
    \<longrightarrow> (c (rev (A@U@V@B)) \<le> c (rev (A@V@U@B)) \<longleftrightarrow> rank (rev U) \<le> rank (rev V))))"


subsection \<open>Proofs\<close>
(** proofs that certain cost functions satisfy properties **)

lemma c_out_symm: "sel_symm f \<Longrightarrow> symmetric (c_out cf f)"
  by (simp add: symmetric_def list_sel_symm)

lemma c_nlj_symm: "symmetric (c_nlj cf f)"
  by (simp add: symmetric_def)

lemma c_smj_symm: "symmetric (c_smj cf f)"
  by (simp add: symmetric_def)

subsubsection \<open>Equivalence Proofs\<close>

theorem c_nlj_IKKBZ: "left_deep t \<Longrightarrow> c_nlj cf f t = c_IKKBZ (\<lambda>_. id) cf f t"
proof(induction t)
  case (Join l r)
  then show ?case by(cases r) auto
qed(simp)

theorem c_hj_IKKBZ: "left_deep t \<Longrightarrow> c_hj cf f t = c_IKKBZ (\<lambda>_ _. 1.2) cf f t"
proof(induction t)
  case ind: (Join l r)
  then show ?case by(cases r) auto
qed(simp)

lemma change_fun_order: "y\<noteq>rel
  \<Longrightarrow> (\<lambda>a b. if a=rel then g a b else (\<lambda>c d. if c=y then h c d else f c d) a b)
    = (\<lambda>a b. if a=y then h a b else (\<lambda>c d. if c=rel then g c d else f c d) a b)"
  by fastforce

lemma c_IKKBZ_fun_notelem:
  assumes "left_deep t"
      and "distinct_relations t"
      and "y \<notin> relations t"
      and "f' = (\<lambda>a b. if a=y then z b else f a b)"
    shows "c_IKKBZ f' cf sf t = c_IKKBZ f cf sf t"
using assms proof(induction t arbitrary: f' f z rule: left_deep.induct)
  case (2 l rel)
  then have 0: "rel \<noteq> y" by auto
  have "c_IKKBZ f' cf sf (Join l (Relation rel))
      = card cf sf l * (f' rel (cf rel)) + c_IKKBZ f' cf sf l" by simp
  also have "\<dots> = card cf sf l * (f' rel (cf rel)) + c_IKKBZ f cf sf l"
    using ldeep_trans distinct_trans_l 2 by fastforce
  also have "\<dots> = card cf sf l * (f rel (cf rel)) + c_IKKBZ f cf sf l"
    using "2.prems"(3,4) by fastforce
  also have "\<dots> = c_IKKBZ f cf sf (Join l (Relation rel))" using "2.prems"(1) by simp
  finally show ?case .
qed (auto)

lemma distinct_c_IKKBZ_ldeep_s_prepend:
  "\<lbrakk>distinct(ys@revorder t); left_deep t\<rbrakk>
    \<Longrightarrow> c_IKKBZ (\<lambda>a b. ldeep_s f (ys@revorder t) a * b) cf f t
      = c_IKKBZ (\<lambda>a b. ldeep_s f (revorder t) a * b) cf f t"
proof(induction t arbitrary: ys rule: left_deep.induct)
  case (2 l rr)
  let ?ylr = "ys @ revorder (Join l (Relation rr))"
  let ?lr = "revorder (Join l (Relation rr))"
  let ?h = "(\<lambda>a. (*) (ldeep_s f ?ylr a))"
  let ?h' = "(\<lambda>a. (*) (ldeep_s f ?lr a))"
  let ?h'' = "(\<lambda>a. (*) (ldeep_s f (revorder l) a))"
  have "?lr = [rr]@revorder l" by simp
  have 0: "distinct ?lr" using "2.prems"(1) by simp
  have "c_IKKBZ ?h cf f (Join l (Relation rr))
      = card cf f l * ((ldeep_s f ?ylr rr) * (cf rr)) + c_IKKBZ ?h cf f l"
    by simp
  also have "\<dots> = card cf f l * ((list_sel_aux' f (revorder l) rr) * (cf rr))
              + c_IKKBZ ?h cf f l"
    using "2.prems"(1) by (fastforce simp: distinct_ldeep_s_eq_aux)
  also have "\<dots> = card cf f l * (?h' rr (cf rr)) + c_IKKBZ ?h cf f l" by simp
  also have "\<dots> = card cf f l * (?h' rr (cf rr)) + c_IKKBZ ?h'' cf f l"
    using "2.IH"[of "ys@[rr]"] "2.prems" by simp
  also have "\<dots> = card cf f l * (?h' rr (cf rr)) + c_IKKBZ ?h' cf f l"
    using "2.IH"[of "[rr]"] "2.prems"(2) 0 by simp
  finally show ?case by simp
qed (auto)

lemma distinct_c_IKKBZ_ldeep_s_subtree:
  assumes "distinct_relations (Join l (Relation rel))"
      and "left_deep (Join l (Relation rel))"
    shows "c_IKKBZ (\<lambda>a b. ldeep_s f (revorder (Join l (Relation rel))) a * b) cf f l
          = c_IKKBZ (\<lambda>a b. ldeep_s f (revorder l) a * b) cf f l"
proof -
  have "distinct (revorder (Join l (Relation rel)))"
    using assms(1) by (simp add: distinct_rels_alt inorder_eq_mset)
  then have "distinct ([rel]@revorder l)" by simp
  then show ?thesis using distinct_c_IKKBZ_ldeep_s_prepend[of "[rel]" l] assms(2) by simp
qed

theorem c_out_IKKBZ:
  "\<lbrakk>distinct_relations t; reasonable_cards cf f t; left_deep t\<rbrakk>
    \<Longrightarrow> c_IKKBZ (\<lambda>a b. ldeep_s f (revorder t) a * b) cf f t = c_out cf f t"
proof(induction t)
  case ind: (Join l r)
  then show ?case
  proof(cases r)
    case (Relation rel)
    let ?s = "(\<lambda>a b. ldeep_s f (revorder (Join l r)) a * b)"
    let ?s' = "(\<lambda>a b. ldeep_s f (revorder l) a * b)"
    have "c_IKKBZ ?s cf f l = c_IKKBZ ?s' cf f l"
      using ind.prems distinct_c_IKKBZ_ldeep_s_subtree Relation by fast
    then have 0: "c_IKKBZ ?s cf f l = c_out cf f l"
      using ind ldeep_trans distinct_trans_l reasonable_trans by metis
    have "c_IKKBZ ?s cf f (Join l r) = card cf f l * (?s rel (cf rel)) + c_IKKBZ ?s cf f l"
      using Relation by simp
    also have "\<dots> = card cf f l * ((list_sel_aux' f (revorder l) rel) * (cf rel))
                + c_IKKBZ ?s cf f l"
      using Relation by simp
    also have "\<dots> = card cf f l * ((list_sel f (revorder l) [rel]) * (cf rel))
                + c_IKKBZ ?s cf f l"
      by (simp add: list_sel_sing_aux')
    also have "\<dots> = card cf f l * ((list_sel f (inorder l) [rel]) * (cf rel))
                + c_IKKBZ ?s cf f l"
      using mset_x_eq_list_sel_eq[of "revorder l"] by (simp add: revorder_eq_rev_inorder)
    also have "\<dots> = card cf f (Join l r) + c_IKKBZ ?s' cf f l"
      using distinct_c_IKKBZ_ldeep_s_subtree ind.prems Relation by fastforce
    also have "\<dots> = card cf f (Join l r) + c_out cf f l"
      using ind reasonable_trans distinct_trans_l ldeep_trans by metis
    finally show ?thesis using Relation by simp
  next
    case (Join lr rr)
    then show ?thesis using ind by simp
  qed
qed(simp)

theorem c_out_eq_c_list':
  "\<lbrakk>distinct_relations t; reasonable_cards cf f t; left_deep t\<rbrakk>
    \<Longrightarrow> c_list' f cf (\<lambda>xs x. (list_sel_aux' f xs x) * cf x) (revorder t) = c_out cf f t"
proof(induction t rule: left_deep.induct)
  case (2 l rr)
  let ?h = "\<lambda>xs x. list_sel_aux' f xs x * cf x"
  let ?ll = "revorder l"
  have 1: "distinct_relations l" using "2.prems" distinct_trans_l by simp
  have 2: "reasonable_cards cf f l" using "2.prems" reasonable_trans by blast
  have 3: "left_deep l" using "2.prems" by simp
  have "revorder (Join l (Relation rr)) = rr # ?ll" by simp
  then have "c_list' f cf ?h (revorder (Join l (Relation rr)))
        = ldeep_n f cf ?ll * ?h ?ll rr + c_list' f cf ?h ?ll"
    using joinTree_cases_ldeep[OF 3] by auto
  also have "\<dots> = card cf f l * ?h ?ll rr + c_list' f cf ?h ?ll"
    using ldeep_n_eq_card_subtree "2.prems" by auto
  also have "\<dots> = card cf f l * (list_sel_aux' f ?ll rr) * cf rr + c_list' f cf ?h ?ll"
    using mset_x_eq_list_sel_aux'_eq mset_rev by fastforce
  also have "\<dots> = card cf f (Join l (Relation rr)) + c_list' f cf ?h ?ll"
    unfolding card_join_alt by (simp add: list_sel_sing_aux')
  also have "\<dots> = card cf f (Join l (Relation rr)) + c_out cf f l" using "2.IH" 1 2 3 by simp
  finally show ?case by simp
qed (auto)

lemma rev_first_last_elem: "(rev (x#x'#xs')) = (r#rs) \<Longrightarrow> x \<in># mset rs"
  using  in_multiset_in_set last_in_set last_snoc rev_singleton_conv
  by (metis List.last.simps List.list.discI List.list.inject List.rev.simps(2))

lemma distinct_first_uneq_last: "distinct (x#x'#xs') \<Longrightarrow> rev (x#x'#xs') = r#rs \<Longrightarrow> r \<noteq> x"
  using rev_first_last_elem mset_rev set_mset_mset
  by (metis List.distinct.simps(2) count_eq_zero_iff distinct_count_atmost_1)

lemma distinct_create_eq_app:
  "\<lbrakk>distinct (ys@xs); x \<in># mset xs\<rbrakk> \<Longrightarrow> create_h_list h xs x = create_h_list h (ys@xs) x"
  by(induction ys) auto

lemma c_list_single_h_list_not_elem_prepend:
  "x \<notin> set ys
  \<Longrightarrow> c_list f cf (create_h_list h (ys@x#xs)) r [x] = c_list f cf (create_h_list h (x#xs)) r [x]"
  by(induction ys) auto

lemma c_list_single_f_list_not_elem_prepend:
  "x \<notin> set ys
  \<Longrightarrow> c_list (ldeep_s f (ys@x#xs)) cf h r [x] = c_list (ldeep_s f (x#xs)) cf h r [x]"
  by(induction ys) auto

lemma c_list_prepend_h_disjunct:
  assumes "distinct (ys@xs)"
  shows "c_list f cf (create_h_list h (ys@xs)) r xs = c_list f cf (create_h_list h xs) r xs"
using assms proof(induction xs arbitrary: ys)
  case (Cons x xs)
  then have 0: "distinct (ys @ [x] @ xs)" by simp
  then have 1: "distinct ([x] @ xs)" by simp
  let ?h = "create_h_list h (ys @ x # xs)"
  let ?h' = "create_h_list h xs"
  let ?h'' = "create_h_list h (x#xs)"
  have 2: "x \<notin> set ys" using Cons.prems by simp
  show ?case
  proof(cases "xs=[]")
    case True
    then show ?thesis
      using Cons distinct_create_eq_app in_multiset_in_set
      by (metis CostFunctions.c_list.simps(2) List.list.set_intros(1))
  next
    case False
    then obtain x' xs' where x'_def[simp]: "xs = x'#xs'" using List.list.exhaust_sel by auto
    then have "c_list f cf ?h r (x # xs)
        = c_list f cf ?h r xs + ldeep_T f cf xs * c_list f cf ?h r [x]" by simp
    also have "\<dots> = c_list f cf ?h' r xs + ldeep_T f cf xs * c_list f cf ?h r [x]"
      using Cons.IH[of "ys@[x]"] 0 by simp
    also have "\<dots> = c_list f cf ?h'' r xs + ldeep_T f cf xs * c_list f cf ?h r [x]"
      using Cons.IH[of "[x]"] 1 by simp
    also have "\<dots> = c_list f cf ?h'' r xs + ldeep_T f cf xs * c_list f cf ?h'' r [x]"
      using c_list_single_h_list_not_elem_prepend 2 by metis
    finally show ?thesis by simp
  qed
qed(simp)

lemma c_list_prepend_f_disjunct:
  assumes "distinct (ys@xs)"
  shows "c_list (ldeep_s f (ys@xs)) cf h r xs = c_list (ldeep_s f xs) cf h r xs"
using assms proof(induction xs arbitrary: ys)
  case (Cons x xs)
  then have 0: "distinct(ys @ [x] @ xs)" by simp
  then have 1: "distinct ([x] @ xs)" by simp
  let ?f = "ldeep_s f (ys @ x # xs)"
  let ?f' = "ldeep_s f xs"
  let ?f'' = "ldeep_s f (x#xs)"
  have 2: "x \<notin> set ys" using Cons.prems by simp
  show ?case
  proof(cases "xs=[]")
    case False
    then obtain x' xs' where x'_def[simp]: "xs = x'#xs'" using List.list.exhaust_sel by auto
    have "ldeep_T ?f cf xs = ldeep_T ?f' cf xs"
      using distinct_ldeep_T_prepend[of "ys@[x]" "xs" f cf] Cons.prems by simp
    then have 3: "ldeep_T ?f cf xs = ldeep_T ?f'' cf xs"
      using distinct_ldeep_T_prepend[of "[x]" "xs" f cf] Cons.prems 1 by simp
    have "c_list ?f cf h r (x # xs)
          = c_list ?f cf h r xs + ldeep_T ?f cf xs * c_list ?f cf h r [x]"
      by simp
    also have "\<dots> = c_list ?f' cf h r xs + ldeep_T ?f'' cf xs * c_list ?f cf h r [x]"
      using Cons.IH[of "ys@[x]"] 0 3 by simp
    also have "\<dots> = c_list ?f'' cf h r xs + ldeep_T ?f'' cf xs * c_list ?f cf h r [x]"
      using Cons.IH[of "[x]"] 1 by simp
    also have "\<dots> = c_list ?f'' cf h r xs + ldeep_T ?f'' cf xs * c_list ?f'' cf h r [x]"
      using c_list_single_f_list_not_elem_prepend 2 by metis
    finally show ?thesis by simp
  qed(simp)
qed(simp)

lemma c_list'_eq_c_list:
  assumes "distinct xs"
      and "rev xs = r # rs"
    shows "c_list (ldeep_s f xs) cf (create_h_list h xs) r xs = c_list' f cf h xs"
using assms proof(induction xs arbitrary: rs)
  case (Cons x xs)
  then show ?case
  proof(cases "xs=[]")
    case False
    then obtain x' xs' where x'_def[simp]: "xs = x'#xs'" using List.list.exhaust_sel by auto
    then have 0: "x \<noteq> r" using distinct_first_uneq_last Cons by fast
    have 1: "distinct xs" using Cons.prems(1) by simp
    have "\<exists>rs'. rev xs = r # rs'"
      using Cons.prems Nil_is_append_conv butlast_append
      by (metis List.append.right_neutral List.butlast.simps(2) List.list.distinct(1)
          List.rev.simps(2) \<open>\<And>thesis. (\<And>x' xs'. xs = x' # xs' \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close>)
    then obtain rs' where 2: "rev xs = r # rs'" by blast
    let ?h = "create_h_list h (x # x' # xs')"
    let ?h' = "create_h_list h (x' # xs')"
    let ?f = "ldeep_s f (x'#xs')"
    let ?f' = "ldeep_s f (x#x'#xs')"
    have "c_list (ldeep_s f (x#xs)) cf (create_h_list h (x # xs)) r (x # xs)
        = c_list ?f' cf ?h r (x # x' # xs')"
      by simp
    also have "\<dots> = c_list ?f' cf ?h r (x' # xs')
            + ldeep_T ?f' cf (x' # xs') * c_list ?f' cf ?h r [x]"
      by simp
    also have "\<dots> = c_list ?f' cf ?h r (x' # xs') + ldeep_T ?f' cf (x' # xs') * h (x' # xs') x"
      using 0 by simp
    also have "\<dots> = c_list ?f' cf ?h r (x' # xs') + ldeep_T ?f cf (x' # xs') * h (x' # xs') x"
      using distinct_ldeep_T_prepend[of "[x]" "x'#xs'"] Cons.prems(1) by simp
    also have "\<dots> = c_list ?f' cf ?h r (x' # xs') + ldeep_n f cf (x' # xs') * h (x' # xs') x"
      using ldeep_T_eq_ldeep_n 1 by fastforce
    also have "\<dots> = c_list ?f cf ?h r (x' # xs') + ldeep_n f cf (x' # xs') * h (x' # xs') x"
      using c_list_prepend_f_disjunct[of "[x]" "x'#xs'"] Cons.prems(1) by simp
    also have "\<dots> = c_list ?f cf ?h' r (x' # xs') + ldeep_n f cf (x' # xs') * h (x' # xs') x"
      using c_list_prepend_h_disjunct[of "[x]" "x'#xs'"] Cons.prems by simp
    also have "\<dots> = c_list' f cf h (x' # xs') + ldeep_n f cf (x' # xs') * h (x' # xs') x"
      using Cons.IH 1 2 by simp
    also have "\<dots> = c_list' f cf h (x#x' # xs')"
      using Cons.prems x'_def 1 2 by simp
    finally show ?thesis by simp
  qed(simp)
qed(simp)

lemma clist_eq_if_cf_eq:
  "\<forall>x. set x \<subseteq> set xs \<longrightarrow> ldeep_T sf cf' x = ldeep_T sf cf x
    \<Longrightarrow> c_list sf cf' h r xs = c_list sf cf h r xs"
  by (induction sf cf' h r xs rule: c_list.induct) (auto simp: subset_insertI2)

lemma ldeep_s_h_eq_list_sel_aux'_h:
  "\<lbrakk>distinct xs; ys@x#zs = xs\<rbrakk>
    \<Longrightarrow> (\<lambda>a. ldeep_s f xs a * cf a) x  = (\<lambda>xs x. (list_sel_aux' f xs x) * cf x) zs x"
  by (fastforce simp: distinct_ldeep_s_eq_aux)

corollary ldeep_s_h_eq_list_sel_aux'_h':
  "\<lbrakk>distinct_relations t; ys@x#zs = revorder t\<rbrakk>
    \<Longrightarrow> (\<lambda>a. ldeep_s f (revorder t) a * cf a) x = (\<lambda>xs x. (list_sel_aux' f xs x) * cf x) zs x"
  by (fastforce simp: distinct_rels_alt ldeep_s_h_eq_list_sel_aux'_h)

lemma create_h_list_distinct_simp: "\<lbrakk>distinct xs; ys@x#zs = xs\<rbrakk> \<Longrightarrow> create_h_list h xs x = h zs x"
  by (induction xs arbitrary: ys) (force simp: append_eq_Cons_conv)+

lemma ldeep_s_h_eq_create_h_list:
  "\<lbrakk>distinct xs; ys@x#zs = xs\<rbrakk>
    \<Longrightarrow> (\<lambda>a. ldeep_s f xs a * cf a) x = create_h_list (\<lambda>xs x. (list_sel_aux' f xs x) * cf x) xs x"
  by (simp add: distinct_relations_def create_h_list_distinct_simp ldeep_s_h_eq_list_sel_aux'_h)

lemma ldeep_s_h_eq_create_h_list':
  "\<lbrakk>distinct_relations t; ys@x#zs = revorder t\<rbrakk>
    \<Longrightarrow> (\<lambda>a. ldeep_s f (revorder t) a * cf a) x
      = create_h_list (\<lambda>xs x. (list_sel_aux' f xs x) * cf x) (revorder t) x"
  by (simp add: distinct_rels_alt ldeep_s_h_eq_create_h_list)

corollary ldeep_s_h_eq_create_h_list'':
  "distinct_relations t \<Longrightarrow> \<forall>ys x zs. ys@x#zs = revorder t
    \<longrightarrow> (\<lambda>a. ldeep_s f (revorder t) a * cf a) x
      = create_h_list (\<lambda>xs x. (list_sel_aux' f xs x) * cf x) (revorder t) x"
  using ldeep_s_h_eq_create_h_list' by fast

lemma ldeep_s_h_eq_create_h_list''':
  "\<lbrakk>distinct_relations t; x \<in> relations t\<rbrakk>
    \<Longrightarrow> (\<lambda>a. ldeep_s f (revorder t) a * cf a) x
      = create_h_list (\<lambda>xs x. (list_sel_aux' f xs x) * cf x) (revorder t) x"
  using ldeep_s_eq_list_sel_aux'_split revorder_eq_set
  by (fastforce simp add: distinct_rels_alt ldeep_s_h_eq_create_h_list)

lemma cons2_if_2elems: "\<lbrakk>x \<in> set xs; y \<in> set xs; x \<noteq> y\<rbrakk> \<Longrightarrow> \<exists>y z zs. xs = y # z # zs"
  using last.simps list.set_cases neq_Nil_conv by metis

theorem c_IKKBZ_eq_c_list:
  fixes t
  defines "xs \<equiv> revorder t"
  assumes "distinct_relations t"
      and "reasonable_cards cf f t"
      and "left_deep t"
      and "\<forall>x \<in> relations t. h1 x (cf x) = h2 x"
  shows "c_IKKBZ h1 cf f t = c_list (ldeep_s f xs) cf h2 (first_node t) xs"
using assms proof(induction t arbitrary: xs rule: left_deep.induct)
  case (2 l r)
  let ?r = "first_node (Join l (Relation r))"
  let ?xs = "revorder (Join l (Relation r))"
  let ?ys = "revorder l"
  let ?sf = "ldeep_s f ?xs"
  have h1_h2_l: "\<forall>x \<in> relations l. h1 x (cf x) = h2 x" using "2.prems"(4) by simp
  have "c_IKKBZ h1 cf f (Join l (Relation r)) = card cf f l * (h1 r (cf r)) + c_IKKBZ h1 cf f l"
    by simp
  then have "c_IKKBZ h1 cf f (Join l (Relation r))
          = card cf f l * (h1 r (cf r)) + c_list (ldeep_s f ?ys) cf h2 ?r ?ys"
    using "2.hyps" "2.prems"(2-3) distinct_trans_l[OF "2.prems"(1)] h1_h2_l by force
  then have ind: "c_IKKBZ h1 cf f (Join l (Relation r))
          = card cf f l * (h1 r (cf r)) + c_list ?sf cf h2 ?r ?ys"
    using c_list_prepend_f_disjunct "2.prems"(1) unfolding distinct_rels_alt
    by (metis revorder.simps(2))
  have 0: "?r \<in> set ?xs" using first_node_last_revorder[of l] by force
  moreover have 1: "r \<in> set ?xs" by simp
  moreover have "distinct ?xs" using "2.prems"(1) distinct_rels_alt by force
  ultimately have "?r \<noteq> r" using first_node_last_revorder[of l] by auto
  then obtain z zs where z_def: "?xs = r # z # zs" using cons2_if_2elems[OF 0 1] by auto
  then have "c_list ?sf cf h2 ?r ?xs
          = c_list ?sf cf h2 ?r ?ys + ldeep_T ?sf cf ?ys * c_list ?sf cf h2 ?r [r]"
    by simp
  also have "\<dots> = c_list ?sf cf h2 ?r ?ys + ldeep_T ?sf cf ?ys * (h1 r (cf r))"
    using \<open>?r \<noteq> r\<close> "2.prems"(4) by fastforce
  also have "\<dots> = c_list ?sf cf h2 ?r ?ys + card cf f l * (h1 r (cf r))"
    using "2.prems"(1,3) ldeep_T_eq_card distinct_rels_alt distinct_ldeep_T_prepend
    by (metis revorder.simps(2) ldeep_trans distinct_trans_l)
  finally show ?case using ind by simp
qed(auto)

lemma c_IKKBZ_eq_c_list_cout:
  fixes f cf t
  defines "xs \<equiv> revorder t"
  defines "h \<equiv> (\<lambda>a. ldeep_s f xs a * cf a)"
  assumes "distinct_relations t"
      and "reasonable_cards cf f t"
      and "left_deep t"
  shows "c_IKKBZ (\<lambda>a b. ldeep_s f xs a * b) cf f t = c_list (ldeep_s f xs) cf h (first_node t) xs"
  using assms c_IKKBZ_eq_c_list by fast

lemma c_IKKBZ_eq_c_list_cout_hlist:
  fixes f cf t
  defines "h \<equiv> (\<lambda>xs x. (list_sel_aux' f xs x) * cf x)"
  defines "xs \<equiv> revorder t"
  assumes "distinct_relations t"
      and "reasonable_cards cf f t"
      and "left_deep t"
  shows "c_IKKBZ (\<lambda>a b. ldeep_s f xs a * b) cf f t
        = c_list (ldeep_s f xs) cf (create_h_list h xs) (first_node t) xs"
  using assms c_IKKBZ_eq_c_list ldeep_s_h_eq_create_h_list'''[OF assms(3)] by fastforce

theorem c_out_eq_c_list:
  fixes f cf t
  defines "xs \<equiv> revorder t"
  defines "h \<equiv> (\<lambda>a. ldeep_s f xs a * cf a)"
  assumes "distinct_relations t"
      and "reasonable_cards cf f t"
      and "left_deep t"
  shows "c_list (ldeep_s f xs) cf h (first_node t) xs = c_out cf f t"
  using c_IKKBZ_eq_c_list_cout c_out_IKKBZ assms by fastforce

theorem c_out_eq_c_list_hlist:
  fixes f cf t
  defines "h \<equiv> (\<lambda>xs x. (list_sel_aux' f xs x) * cf x)"
  defines "xs \<equiv> revorder t"
  assumes "distinct_relations t"
      and "reasonable_cards cf f t"
      and "left_deep t"
    shows "c_list (ldeep_s f xs) cf (create_h_list h xs) (first_node t) xs = c_out cf f t"
  using c_IKKBZ_eq_c_list_cout_hlist c_out_IKKBZ assms by fastforce

(* alternative proof using c_list' *)
lemma c_out_eq_c_list_altproof:
  fixes f cf t
  defines "h \<equiv> (\<lambda>xs x. (list_sel_aux' f xs x) * cf x)"
  defines "xs \<equiv> revorder t"
  assumes "distinct_relations t"
      and "reasonable_cards cf f t"
      and "left_deep t"
    shows "c_list (ldeep_s f xs) cf (create_h_list h xs) (first_node t) xs = c_out cf f t"
proof -
  obtain rs where rs_def[simp]: "rev (revorder t) = (first_node t) # rs"
    unfolding revorder_eq_rev_inorder using first_node_first_inorder by auto
  have 0: "distinct (revorder t)" using assms(3) distinct_rels_alt by auto
  then have "c_list (ldeep_s f xs) cf (create_h_list h xs) (first_node t) xs
          = c_list' f cf h (revorder t)"
    using rs_def c_list'_eq_c_list xs_def by fast
  then show ?thesis using assms c_out_eq_c_list' by auto
qed

text \<open>
  Similarly, we can derive the equivalence for other cost functions like @{term c_nlj} and
  @{term c_hj} by using the equivalence of @{term c_IKKBZ} and @{term c_list}.
\<close>

lemma c_IKKBZ_eq_c_list_hj:
  fixes f cf t
  defines "xs \<equiv> revorder t"
  assumes "distinct_relations t"
      and "reasonable_cards cf f t"
      and "left_deep t"
    shows "c_IKKBZ (\<lambda>_ _. 1.2) cf f t = c_list (ldeep_s f xs) cf (\<lambda>_. 1.2) (first_node t) xs"
  using c_IKKBZ_eq_c_list assms by fast

corollary c_hj_eq_c_list:
  fixes f cf t
  defines "xs \<equiv> revorder t"
  assumes "distinct_relations t"
      and "reasonable_cards cf f t"
      and "left_deep t"
    shows "c_list (ldeep_s f xs) cf (\<lambda>_. 1.2) (first_node t) xs = c_hj cf f t"
  using c_IKKBZ_eq_c_list_hj c_hj_IKKBZ assms by fastforce

lemma c_IKKBZ_eq_c_list_nlj:
  fixes f cf t
  defines "xs \<equiv> revorder t"
  assumes "distinct_relations t"
      and "reasonable_cards cf f t"
      and "left_deep t"
    shows "c_IKKBZ (\<lambda>_. id) cf f t = c_list (ldeep_s f xs) cf cf (first_node t) xs"
  using c_IKKBZ_eq_c_list assms by fastforce

corollary c_nlj_eq_c_list:
  fixes f cf t
  defines "xs \<equiv> revorder t"
  assumes "distinct_relations t"
      and "reasonable_cards cf f t"
      and "left_deep t"
    shows "c_list (ldeep_s f xs) cf cf (first_node t) xs = c_nlj cf f t"
  using c_IKKBZ_eq_c_list_nlj c_nlj_IKKBZ assms by fastforce

lemma c_list_app:
  "c_list f cf h r (ys@xs) = c_list f cf h r xs + ldeep_T f cf xs * c_list f cf h r ys"
proof(induction ys)
  case (Cons y ys)
  then show ?case
  proof(cases "xs=[]")
    case True
    then show ?thesis using ldeep_T_empty by auto
  next
    case False
    then obtain x' xs' where x'_def[simp]: "xs = x'#xs'" using List.list.exhaust_sel by blast
    then have "c_list f cf h r (y#ys @ xs)
            = c_list f cf h r (ys@xs) + ldeep_T f cf (ys@xs) * c_list f cf h r [y]"
      by (metis CostFunctions.c_list.simps(3) Nil_is_append_conv neq_Nil_conv)
    also have "\<dots> = c_list f cf h r xs + ldeep_T f cf xs * c_list f cf h r ys
            + ldeep_T f cf (ys@xs) * c_list f cf h r [y]"
      using Cons.IH by simp
    also have "\<dots> = c_list f cf h r xs + ldeep_T f cf xs * c_list f cf h r ys
            + ldeep_T f cf ys * ldeep_T f cf xs * c_list f cf h r [y]"
      using ldeep_T_app by auto
    also have "\<dots> = c_list f cf h r xs + ldeep_T f cf xs * (c_list f cf h r ys
            + ldeep_T f cf ys * c_list f cf h r [y])"
      by argo
    also have "\<dots> = c_list f cf h r xs + ldeep_T f cf xs * (c_list f cf h r (y # ys))"
      using False neq_Nil_conv List.append.left_neutral
      by (metis CostFunctions.c_list.simps(3) calculation)
    finally show ?thesis by simp
  qed
qed(simp)

lemma create_h_list_pos:
  "\<lbrakk>sel_reasonable sf; \<forall>x \<in> set xs. cf x > 0\<rbrakk>
    \<Longrightarrow> (create_h_list (\<lambda>xs x. (list_sel_aux' sf xs x) * cf x) xs) x > 0"
  by (induction xs) (auto simp: list_sel_aux'_reasonable)

lemma c_list_not_neg:
  assumes "sel_reasonable sf"
      and "\<forall>x \<in> set ys. cf x > 0"
      and "h = (\<lambda>a. ldeep_s sf xs a * cf a)"
    shows "c_list (ldeep_s sf xs) cf h r ys \<ge> 0"
using assms proof(induction ys arbitrary: xs)
  case ind: (Cons y ys)
  let ?sf = "ldeep_s sf xs"
  show ?case
  proof(cases ys)
    case Nil
    then show ?thesis using ind.prems by (simp add: ldeep_s_pos order_less_imp_le)
  next
    case (Cons y' ys')
    show ?thesis
    proof(cases "y=r")
      case True
      then show ?thesis using Cons ind by simp
    next
      case False
      have "c_list ?sf cf h r (y # ys) = c_list ?sf cf h r ys + ldeep_T ?sf cf ys * h y"
        using Cons False by simp
      then have "c_list ?sf cf h r (y # ys) \<ge> ldeep_T ?sf cf ys * h y"
        using ind by simp
      moreover have "ldeep_T ?sf cf ys * h y > 0"
        using ind.prems by (simp add: ldeep_T_pos ldeep_s_pos)
      ultimately show ?thesis by simp
    qed
  qed
qed(simp)

lemma c_list_not_neg_hlist:
  assumes "sel_reasonable sf"
      and "\<forall>x \<in> set xs. cf x > 0"
      and "\<forall>x \<in> set ys. cf x > 0"
      and "h = create_h_list (\<lambda>xs x. (list_sel_aux' sf xs x) * cf x) xs"
    shows "c_list (ldeep_s sf xs) cf h r ys \<ge> 0"
using assms proof(induction ys arbitrary: xs)
  case ind: (Cons y ys)
  let ?sf = "ldeep_s sf xs"
  show ?case
  proof(cases ys)
    case Nil
    then show ?thesis
      using ind.prems by(cases "y=r")(auto simp: create_h_list_pos less_eq_real_def)
  next
    case (Cons y' ys')
    show ?thesis
    proof(cases "y=r")
      case True
      then show ?thesis using Cons ind by simp
    next
      case False
      have "c_list ?sf cf h r (y # ys) = c_list ?sf cf h r ys + ldeep_T ?sf cf ys * h y"
        using Cons False by simp
      then have "c_list ?sf cf h r (y # ys) \<ge> ldeep_T ?sf cf ys * h y"
        using ind by simp
      moreover have "ldeep_T ?sf cf ys * h y > 0"
        using create_h_list_pos[of sf xs cf y] ind.prems by (simp add: ldeep_T_pos)
      ultimately show ?thesis by simp
    qed
  qed
qed(simp)

lemma c_list_pos_if_h_pos:
  "\<lbrakk>sel_reasonable sf; \<forall>x \<in> set xs. cf x > 0; \<forall>x \<in> set xs. h x > 0; r \<notin> set xs; xs \<noteq> []\<rbrakk>
    \<Longrightarrow> c_list (ldeep_s sf ys) cf h r xs > 0"
proof(induction "ldeep_s sf ys" cf h r xs rule: c_list.induct)
  case (3 cf h r y x xs)
  have "ldeep_T (ldeep_s sf ys) cf (x#xs) > 0" using ldeep_T_pos[of "x#xs"] "3.prems"(1,2) by simp
  then have "ldeep_T (ldeep_s sf ys) cf (x#xs) * c_list (ldeep_s sf ys) cf h r [y] > 0"
    using 3 by auto
  moreover have "c_list (ldeep_s sf ys) cf h r (x#xs) > 0" using 3 by auto
  ultimately show ?case by simp
qed(auto)

lemma c_list_pos_r_not_elem:
  assumes "sel_reasonable sf"
      and "\<forall>x \<in> set ys. cf x > 0"
      and "ys \<noteq> []"
      and "r \<notin> set ys"
      and "h = (\<lambda>a. ldeep_s sf xs a * cf a)"
    shows "c_list (ldeep_s sf xs) cf h r ys > 0"
  using c_list_pos_if_h_pos ldeep_s_pos assms by fastforce

lemma c_list_pos_r_not_elem_hlist:
  assumes "sel_reasonable sf"
      and "\<forall>x \<in> set xs. cf x > 0"
      and "\<forall>x \<in> set ys. cf x > 0"
      and "ys \<noteq> []"
      and "r \<notin> set ys"
      and "h = create_h_list (\<lambda>xs x. (list_sel_aux' sf xs x) * cf x) xs"
    shows "c_list (ldeep_s sf xs) cf h r ys > 0"
  using c_list_pos_if_h_pos create_h_list_pos[OF assms(1)] assms by fastforce

lemma c_list_pos_not_root:
  assumes "sel_reasonable sf"
      and "\<forall>x \<in> set ys. cf x > 0"
      and "ys \<noteq> []"
      and "ys \<noteq> [r]"
      and "distinct ys"
      and "h = (\<lambda>a. ldeep_s sf xs a * cf a)"
    shows "c_list (ldeep_s sf xs) cf h r ys > 0"
using assms proof(induction ys arbitrary: xs)
  case ind: (Cons y ys)
  let ?sf = "ldeep_s sf xs"
  show ?case
  proof(cases ys)
    case Nil
    then have "c_list ?sf cf h r (y # ys) = h y" using ind.prems(4) by simp
    then show ?thesis using ind.prems(1,2,6) by (simp add: ldeep_s_pos)
  next
    case (Cons y' ys')
    show ?thesis
    proof(cases "y=r")
      case True
      then have 0: "r \<notin> set ys" using ind.prems(5) by simp
      have "c_list ?sf cf h r (y # ys) = c_list ?sf cf h r ys"
        using Cons True by simp
      then show ?thesis using ind.prems(1,2,4,6) 0 True by (fastforce intro: c_list_pos_r_not_elem)
    next
      case False
      have "c_list ?sf cf h r (y # ys) = c_list ?sf cf h r ys + ldeep_T ?sf cf ys * h y"
        using Cons False by simp
      then have "c_list ?sf cf h r (y # ys) \<ge> ldeep_T ?sf cf ys * h y"
        using c_list_not_neg ind.prems(1,2,3,6) by fastforce
      moreover have "ldeep_T ?sf cf ys * h y > 0"
        using ind.prems(1,2,6) by (simp add: ldeep_T_pos ldeep_s_pos)
      ultimately show ?thesis by simp
    qed
  qed
qed(simp)

lemma c_list_pos_not_root_hlist:
  assumes "sel_reasonable sf"
      and "\<forall>x \<in> set xs. cf x > 0"
      and "\<forall>x \<in> set ys. cf x > 0"
      and "ys \<noteq> []"
      and "ys \<noteq> [r]"
      and "distinct ys"
      and "h = create_h_list (\<lambda>xs x. (list_sel_aux' sf xs x) * cf x) xs"
    shows "c_list (ldeep_s sf xs) cf h r ys > 0"
using assms proof(induction ys arbitrary: xs)
  case ind: (Cons y ys)
  let ?sf = "ldeep_s sf xs"
  show ?case
  proof(cases ys)
    case Nil
    then have "c_list ?sf cf h r (y # ys) = h y" using ind.prems(5) by simp
    then show ?thesis using create_h_list_pos ind.prems(1,2,7) by fastforce
  next
    case (Cons y' ys')
    show ?thesis
    proof(cases "y=r")
      case True
      then have 0: "r \<notin> set ys" using ind.prems(6) by simp
      have "c_list ?sf cf h r (y # ys) = c_list ?sf cf h r ys"
        using Cons True by simp
      then show ?thesis
        using c_list_pos_r_not_elem_hlist[of sf xs cf ys r h] 0 ind.prems(1,2,3,7) Cons by auto
    next
      case False
      have "c_list ?sf cf h r (y # ys) = c_list ?sf cf h r ys + ldeep_T ?sf cf ys * h y"
        using Cons False by simp
      then have "c_list ?sf cf h r (y # ys) \<ge> ldeep_T ?sf cf ys * h y"
        using c_list_not_neg_hlist ind.prems(1,2,3,7) by fastforce
      moreover have "ldeep_T ?sf cf ys * h y > 0"
        using ind.prems(1,2,3,7) by (simp add: ldeep_T_pos create_h_list_pos)
      ultimately show ?thesis by simp
    qed
  qed
qed(simp)

lemma c_list_split_four:
  assumes "T = ldeep_T f cf"
      and "C = c_list f cf h r"
    shows "C (rev (A @ U @ V @ B)) = C (rev A) + T (rev A) * C (rev U)
            + T (rev A) * T (rev U) * C (rev V)
            + T (rev A) * T (rev U) * T (rev V) * C (rev B)"
proof -
  let ?T = "ldeep_T f cf"
  let ?C = "c_list f cf h r"
  have "?C (rev (A @ U @ V @ B))
      = ?C (rev A) + ?T (rev A) * ?C (rev (U @ V @ B))"
    using c_list_app[where ys="rev (U@V@B)"] by simp
  also have "\<dots> = ?C (rev A) + ?T (rev A) * (?C (rev U)
        + ?T (rev U) * ?C (rev (V@B)))"
    using c_list_app[where ys="rev (V@B)"] by simp
  also have "\<dots> = ?C (rev A) + ?T (rev A) * ?C (rev U)
        + ?T (rev A) * ?T (rev U) * ?C (rev (V@B))"
    by argo
  also have "\<dots> = ?C (rev A) + ?T (rev A) * ?C (rev U)
        + ?T (rev A) * ?T (rev U) * (?C (rev V)
        + ?T (rev V) * ?C (rev B))"
    using c_list_app by force
  finally have 0: "?C (rev (A @ U @ V @ B))
      = ?C (rev A) + ?T (rev A) * ?C (rev U)
        + ?T (rev A) * ?T (rev U) * ?C (rev V)
        + ?T (rev A) * ?T (rev U) * ?T (rev V) * ?C (rev B)"
    by argo
  then show ?thesis using assms by simp
qed

lemma c_list_A_pos_asi:
  assumes "c_list f cf h r (rev U) > 0"
      and "c_list f cf h r (rev V) > 0"
      and "ldeep_T f cf (rev A) > 0"
    shows "c_list f cf h r (rev (A @ U @ V @ B)) \<le> c_list f cf h r (rev (A @ V @ U @ B))
       \<longleftrightarrow> ((ldeep_T f cf (rev U) - 1) / c_list f cf h r (rev U)
          \<le> (ldeep_T f cf (rev V) - 1) / c_list f cf h r (rev V))"
proof -
  let ?T = "ldeep_T f cf"
  let ?C = "c_list f cf h r"
  let ?rank = "(\<lambda>l. (?T l - 1) / ?C l)"
  have 0: "?C (rev (A @ U @ V @ B))
      = ?C (rev A) + ?T (rev A) * ?C (rev U)
        + ?T (rev A) * ?T (rev U) * ?C (rev V)
        + ?T (rev A) * ?T (rev U) * ?T (rev V) * ?C (rev B)"
    using c_list_split_four by fastforce
  have "?C (rev (A @ V @ U @ B))
      = ?C (rev A) + ?T (rev A) * ?C (rev V)
        + ?T (rev A) * ?T (rev V) * ?C (rev U)
        + ?T (rev A) * ?T (rev V) * ?T (rev U) * ?C (rev B)"
    using c_list_split_four by fastforce
  then have "?C (rev (A@U@V@B)) - ?C (rev (A@V@U@B))
          = ?T (rev A) * (?C (rev V) * (?T (rev U) - 1) - ?C (rev U) * (?T (rev V) - 1))"
    using 0 by argo
  also have "\<dots> = ?T (rev A) *
              (?C (rev V) * (?T (rev U) - 1) * (?C (rev U) / ?C (rev U))
                - ?C (rev U) * (?T (rev V) - 1) * (?C (rev V) / ?C (rev V)))"
    using assms
    by (metis Groups.monoid_mult_class.mult.right_neutral divide_self_if less_numeral_extra(3))
  also have "\<dots> = ?T (rev A) * ?C (rev U) * ?C (rev V) * (?rank (rev U) - ?rank (rev V))"
    by argo
  finally have 1: "?C (rev (A@U@V@B)) - ?C (rev (A@V@U@B))
              = ?T (rev A) * ?C (rev U) * ?C (rev V) * (?rank (rev U) - ?rank (rev V))".
  then show ?thesis
  proof(cases "?C (rev (A@U@V@B)) \<le> ?C (rev (A@V@U@B))")
    case True
    then show ?thesis by (smt (verit) assms 1 mult_pos_pos)
  next
    case False
    then show ?thesis by (smt (z3) 1 assms mult_pos_pos zero_less_mult_pos)
  qed
qed

lemma c_list_asi_aux:
  assumes "sel_reasonable sf"
      and "\<forall>x. cf x > 0"
      and "c = c_list f cf h r"
      and "f = (ldeep_s sf xs)"
      and "\<forall>ys. (ys \<noteq> [] \<and> r \<notin> set ys) \<longrightarrow> c ys > 0"
      and "distinct (A@U@V@B)"
      and "U \<noteq> []"
      and "V \<noteq> []"
      and "rank = (\<lambda>l. (ldeep_T f cf l - 1) / c l)"
      and "r \<notin> set (A@U@V@B) \<or> (take 1 (A@U@V@B) = [r] \<and> take 1 (A@V@U@B) = [r])"
    shows "(c (rev (A@U@V@B)) \<le> c (rev (A@V@U@B)) \<longleftrightarrow> rank (rev U) \<le> rank (rev V))"
proof (cases "r \<notin> set (A@U@V@B)")
  case True
  have 0: "ldeep_T f cf (rev A) > 0" using assms(1,2,4) ldeep_T_pos by fast
  have "r \<notin> set (rev U)" using True by simp
  then have 1: "c_list f cf h r (rev U) > 0"
    using c_list_pos_r_not_elem assms(1-5,7) by fastforce
  have "r \<notin> set (rev V)" using True by simp
  then have "c_list f cf h r (rev V) > 0"
    using c_list_pos_r_not_elem assms(1-5,8) by fastforce
  then show ?thesis using c_list_A_pos_asi 0 1 assms(3,9) by fast
next
  case False
  have 0: "ldeep_T f cf (rev A) > 0" using assms(1,2,4) ldeep_T_pos by fast
  have r_first: "take 1 (A@U@V@B) = [r] \<and> take 1 (A@V@U@B) = [r]"
    using assms(10) False by blast
  then have "take 1 A = [r]" using assms(6-8) distinct_change_order_first_elem by metis
  then have "r \<in> set A" by (metis List.list.set_intros(1) in_set_takeD)
  then have 1: "r \<notin> set (U@V@B)" using assms(6) by auto
  then have "r \<notin> set (rev U)" by simp
  then have 2: "c_list f cf h r (rev U) > 0"
    using c_list_pos_r_not_elem assms(1-5,7) by fastforce
  have "r \<notin> set (rev V)" using 1 by simp
  then have "c_list f cf h r (rev V) > 0"
    using c_list_pos_r_not_elem assms(1-5,8) by fastforce
  then show ?thesis using c_list_A_pos_asi 0 2 assms(3,9) by fast
qed

lemma c_list_pos_asi:
  fixes sf cf h r xs
  defines "f \<equiv> ldeep_s sf xs"
  defines "rank \<equiv> (\<lambda>l. (ldeep_T f cf l - 1) / c_list f cf h r l)"
  assumes "sel_reasonable sf"
      and "\<forall>x. cf x > 0"
      and "\<forall>ys. (ys \<noteq> [] \<and> r \<notin> set ys) \<longrightarrow> c_list f cf h r ys > 0"
  shows "asi rank r (c_list f cf h r)"
  unfolding asi_def using c_list_asi_aux[OF assms(3,4)] assms(1,2,5) by simp

theorem c_list_asi:
  fixes sf cf h r xs
  defines "f \<equiv> ldeep_s sf xs"
  defines "rank \<equiv> (\<lambda>l. (ldeep_T f cf l - 1) / c_list f cf h r l)"
  assumes "sel_reasonable sf"
      and "\<forall>x. cf x > 0"
      and "\<forall>x. h x > 0"
  shows "asi rank r (c_list f cf h r)"
  using c_list_pos_asi assms c_list_pos_if_h_pos[OF assms(3)] by fastforce

corollary c_out_asi:
  fixes sf cf r xs
  defines "f \<equiv> ldeep_s sf xs"
  defines "h \<equiv> (\<lambda>a. ldeep_s sf xs a * cf a)"
  defines "rank \<equiv> (\<lambda>l. (ldeep_T f cf l - 1) / c_list f cf h r l)"
  assumes "sel_reasonable sf"
      and "\<forall>x. cf x > 0"
  shows "asi rank r (c_list f cf h r)"
  using c_list_asi ldeep_s_pos assms by fastforce

(* old alternative proof that proofs asi property directly for this specific h *)
lemma c_out_asi_aux:
  assumes "sel_reasonable sf"
      and "\<forall>x. cf x > 0"
      and "c = c_list f cf h r"
      and "f = (ldeep_s sf xs)"
      and "h = (\<lambda>a. ldeep_s sf xs a * cf a)"
      and "distinct (A@U@V@B)"
      and "U \<noteq> []"
      and "V \<noteq> []"
      and "rank = (\<lambda>l. (ldeep_T f cf l - 1) / c l)"
      and "r \<notin> set (A@U@V@B) \<or> (take 1 (A@U@V@B) = [r] \<and> take 1 (A@V@U@B) = [r])"
    shows "(c (rev (A@U@V@B)) \<le> c (rev (A@V@U@B)) \<longleftrightarrow> rank (rev U) \<le> rank (rev V))"
proof (cases "r \<notin> set (A@U@V@B)")
  case True
  have 0: "ldeep_T f cf (rev A) > 0" using assms(1,2,4) ldeep_T_pos by fast
  have "r \<notin> set (rev U)" using True by simp
  then have 1: "c_list f cf h r (rev U) > 0"
    using c_list_pos_r_not_elem assms(1,2,4,5,7) by fastforce
  have "r \<notin> set (rev V)" using True by simp
  then have "c_list f cf h r (rev V) > 0"
    using c_list_pos_r_not_elem assms(1,2,4,5,8) by fastforce
  then show ?thesis using c_list_A_pos_asi 0 1 assms(3,9) by fast
next
  case False
  have 0: "ldeep_T f cf (rev A) > 0" using assms(1,2,4) ldeep_T_pos by fast
  have r_first: "take 1 (A@U@V@B) = [r] \<and> take 1 (A@V@U@B) = [r]"
    using assms(10) False by blast
  then have "take 1 A = [r]" using assms(6-8) distinct_change_order_first_elem by metis
  then have "r \<in> set A" by (metis List.list.set_intros(1) in_set_takeD)
  then have 1: "r \<notin> set (U@V@B)" using assms(6) by auto
  then have "r \<notin> set (rev U)" by simp
  then have 2: "c_list f cf h r (rev U) > 0"
    using c_list_pos_r_not_elem assms(1,2,4,5,7) by fastforce
  have "r \<notin> set (rev V)" using 1 by simp
  then have "c_list f cf h r (rev V) > 0"
    using c_list_pos_r_not_elem assms(1,2,4,5,8) by fastforce
  then show ?thesis using c_list_A_pos_asi 0 2 assms(3,9) by fast
qed

lemma c_out_asi_aux_hlist:
  assumes "sel_reasonable sf"
      and "\<forall>x. cf x > 0"
      and "c = c_list f cf h r"
      and "f = (ldeep_s sf xs)"
      and "h = create_h_list (\<lambda>xs x. (list_sel_aux' sf xs x) * cf x) xs"
      and "distinct (A@U@V@B)"
      and "U \<noteq> []"
      and "V \<noteq> []"
      and "rank = (\<lambda>l. (ldeep_T f cf l - 1) / c l)"
      and "r \<notin> set (A@U@V@B) \<or> (take 1 (A@U@V@B) = [r] \<and> take 1 (A@V@U@B) = [r])"
    shows "(c (rev (A@U@V@B)) \<le> c (rev (A@V@U@B)) \<longleftrightarrow> rank (rev U) \<le> rank (rev V))"
proof (cases "r \<notin> set (A@U@V@B)")
  case True
  have 0: "ldeep_T f cf (rev A) > 0" using assms(1,2,4) ldeep_T_pos by fast
  have "r \<notin> set (rev U)" using True by simp
  then have 1: "c_list f cf h r (rev U) > 0"
    using c_list_pos_r_not_elem_hlist assms(1,2,4,5,7) by fastforce
  have "r \<notin> set (rev V)" using True by simp
  then have "c_list f cf h r (rev V) > 0"
    using c_list_pos_r_not_elem_hlist assms(1,2,4,5,8) by fastforce
  then show ?thesis using c_list_A_pos_asi 0 1 assms(3,9) by fast
next
  case False
  have 0: "ldeep_T f cf (rev A) > 0" using assms(1,2,4) ldeep_T_pos by fast
  have r_first: "take 1 (A@U@V@B) = [r] \<and> take 1 (A@V@U@B) = [r]"
    using assms(10) False by blast
  then have "take 1 A = [r]" using assms(6-8) distinct_change_order_first_elem by metis
  then have "r \<in> set A" by (metis List.list.set_intros(1) in_set_takeD)
  then have 1: "r \<notin> set (U@V@B)" using assms(6) by auto
  then have "r \<notin> set (rev U)" by simp
  then have 2: "c_list f cf h r (rev U) > 0"
    using c_list_pos_r_not_elem_hlist assms(1,2,4,5,7) by fastforce
  have "r \<notin> set (rev V)" using 1 by simp
  then have "c_list f cf h r (rev V) > 0"
    using c_list_pos_r_not_elem_hlist assms(1,2,4,5,8) by fastforce
  then show ?thesis using c_list_A_pos_asi 0 2 assms(3,9) by fast
qed

theorem c_out_asi_altproof:
  assumes "sel_reasonable sf"
      and "\<forall>x. cf x > 0"
      and "c = c_list f cf h r"
      and "f = (ldeep_s sf xs)"
      and "h = (\<lambda>a. ldeep_s sf xs a * cf a)"
    shows "asi (\<lambda>l. (ldeep_T f cf l - 1) / c l) r (c_list f cf h r)"
  unfolding asi_def using c_out_asi_aux[OF assms] assms(3) by blast

theorem c_out_asi_hlist:
  assumes "sel_reasonable sf"
      and "\<forall>x. cf x > 0"
      and "c = c_list f cf h r"
      and "f = (ldeep_s sf xs)"
      and "h = create_h_list (\<lambda>xs x. (list_sel_aux' sf xs x) * cf x) xs"
    shows "asi (\<lambda>l. (ldeep_T f cf l - 1) / c l) r (c_list f cf h r)"
  unfolding asi_def using c_out_asi_aux_hlist[OF assms] assms(3) by blast

lemma asi_if_asi': "asi rank r c \<Longrightarrow> asi' r c"
  unfolding asi'_def asi_def by auto

corollary c_out_asi':
  assumes "sel_reasonable sf"
      and "\<forall>x. cf x > 0"
      and "f = (ldeep_s sf xs)"
      and "h = (\<lambda>a. ldeep_s sf xs a * cf a)"
    shows "asi' r (c_list f cf h r)"
  using asi_if_asi' c_out_asi[OF assms(1,2)] assms(3,4) by fast

corollary c_out_asi'_hlist:
  assumes "sel_reasonable sf"
      and "\<forall>x. cf x > 0"
      and "f = (ldeep_s sf xs)"
      and "h = create_h_list (\<lambda>xs x. (list_sel_aux' sf xs x) * cf x) xs"
    shows "asi' r (c_list f cf h r)"
  using asi_if_asi' c_out_asi_hlist[OF assms(1,2)] assms(3,4) by fast

lemma c_out_asi''_aux:
  assumes "sel_reasonable sf"
      and "\<forall>x. cf x > 0"
      and "c = c_list f cf h r"
      and "f = (ldeep_s sf xs)"
      and "h = create_h_list (\<lambda>xs x. (list_sel_aux' sf xs x) * cf x) xs"
      and "distinct (A@U@V@B)"
      and "U \<noteq> []"
      and "V \<noteq> []"
      and "rank = (\<lambda>l. (ldeep_T f cf l - 1) / c l)"
      and "U \<noteq> [r]"
      and "V \<noteq> [r]"
    shows "(c (rev (A@U@V@B)) \<le> c (rev (A@V@U@B)) \<longleftrightarrow> rank (rev U) \<le> rank (rev V))"
proof (cases "r \<notin> set (A@U@V@B)")
  case True
  have 0: "ldeep_T f cf (rev A) > 0" using assms(1,2,4) ldeep_T_pos by fast
  have "r \<notin> set (rev U)" using True by simp
  then have 1: "c_list f cf h r (rev U) > 0"
    using c_list_pos_r_not_elem_hlist assms(1,2,4,5,7) by fastforce
  have "r \<notin> set (rev V)" using True by simp
  then have "c_list f cf h r (rev V) > 0"
    using c_list_pos_r_not_elem_hlist assms(1,2,4,5,8) by fastforce
  then show ?thesis using c_list_A_pos_asi 0 1 assms(3,9) by fast
next
  case False
  have 0: "ldeep_T f cf (rev A) > 0" using assms(1,2,4) ldeep_T_pos by fast
  have 2: "c_list f cf h r (rev U) > 0"
    using c_list_pos_not_root_hlist assms(1,2,4-7,10) by fastforce
  have "c_list f cf h r (rev V) > 0"
    using c_list_pos_not_root_hlist assms(1,2,4-6,8,11) by fastforce
  then show ?thesis using c_list_A_pos_asi 0 2 assms(3,9) by fast
qed

theorem c_out_asi'':
  assumes "sel_reasonable sf"
      and "\<forall>x. cf x > 0"
      and "c = c_list f cf h r"
      and "f = (ldeep_s sf xs)"
      and "h = create_h_list (\<lambda>xs x. (list_sel_aux' sf xs x) * cf x) xs"
    shows "asi'' (\<lambda>l. (ldeep_T f cf l - 1) / c l) r (c_list f cf h r)"
  unfolding asi''_def using c_out_asi''_aux[OF assms] assms(3) by blast

subsubsection \<open>Additional ASI Proofs\<close>

lemma asi_le_iff_notr:
  "\<lbrakk>asi rank r cost; U \<noteq> []; V \<noteq> []; r \<notin> set (A @ U @ V @ B); distinct (A @ U @ V @ B)\<rbrakk>
    \<Longrightarrow> rank (rev U) \<le> rank (rev V) \<longleftrightarrow> cost (rev (A@U@V@B)) \<le> cost (rev (A@V@U@B))"
  unfolding asi_def by blast

lemma asi_le_iff_rfst:
  "\<lbrakk>asi rank r cost; U \<noteq> []; V \<noteq> [];
    take 1 (A @ U @ V @ B) = [r]; take 1 (A @ V @ U @ B) = [r]; distinct (A @ U @ V @ B)\<rbrakk>
    \<Longrightarrow> rank (rev U) \<le> rank (rev V) \<longleftrightarrow> cost (rev (A@U@V@B)) \<le> cost (rev (A@V@U@B))"
  unfolding asi_def by blast

lemma asi_le_notr:
  "\<lbrakk>asi rank r cost; rank (rev U) \<le> rank (rev V); U\<noteq>[]; V\<noteq>[];
    distinct (A@U@V@B); r \<notin> set (A@U@V@B)\<rbrakk>
    \<Longrightarrow> cost (rev (A@U@V@B)) \<le> cost (rev (A@V@U@B))"
  unfolding asi_def by blast

lemma asi_le_rfst:
  "\<lbrakk>asi rank r cost; rank (rev U) \<le> rank (rev V); U\<noteq>[]; V\<noteq>[]; distinct (A@U@V@B);
    take 1 (A @ U @ V @ B) = [r]; take 1 (A @ V @ U @ B) = [r]\<rbrakk>
    \<Longrightarrow> cost (rev (A@U@V@B)) \<le> cost (rev (A@V@U@B))"
  unfolding asi_def by blast

lemma asi_eq_notr:
  assumes "asi rank r cost"
      and "rank (rev U) = rank (rev V)"
      and "U \<noteq> []"
      and "V \<noteq> []"
      and "r \<notin> set (A@U@V@B)"
      and "distinct (A @ U @ V @ B)"
    shows "cost (rev (A@U@V@B)) = cost (rev (A@V@U@B))"
proof -
  have 0: "distinct (A@V@U@B)" using assms(6) by auto
  have 1: "r \<notin> set (A@V@U@B)" using assms(5) by auto
  then show ?thesis
    using asi_le_iff_notr[OF assms(1,3-6)] asi_le_iff_notr[OF assms(1,4,3) 1 0] assms(2) by simp
qed

lemma asi_eq_notr':
  assumes "asi rank r cost"
      and "cost (rev (A@U@V@B)) = cost (rev (A@V@U@B))"
      and "U \<noteq> []"
      and "V \<noteq> []"
      and "r \<notin> set (A@U@V@B)"
      and "distinct (A @ U @ V @ B)"
    shows "rank (rev U) = rank (rev V)"
proof -
  have 0: "distinct (A@V@U@B)" using assms(6) by auto
  have 1: "r \<notin> set (A@V@U@B)" using assms(5) by auto
  show ?thesis
    using asi_le_iff_notr[OF assms(1,3-6)] asi_le_iff_notr[OF assms(1,4,3) 1 0] assms(2) by simp
qed

lemma asi_eq_iff_notr:
  "\<lbrakk>asi rank r cost; U \<noteq> []; V \<noteq> []; r \<notin> set (A@U@V@B); distinct (A@U@V@B)\<rbrakk>
    \<Longrightarrow> rank (rev U) = rank (rev V) \<longleftrightarrow> cost (rev (A@U@V@B)) = cost (rev (A@V@U@B))"
  using asi_eq_notr[of rank r cost] asi_eq_notr'[of rank r cost] by blast

lemma asi_eq_rfst:
  assumes "asi rank r cost"
      and "rank (rev U) = rank (rev V)"
      and "U \<noteq> []"
      and "V \<noteq> []"
      and "take 1 (A @ U @ V @ B) = [r]"
      and "take 1 (A @ V @ U @ B) = [r]"
      and "distinct (A @ U @ V @ B)"
    shows "cost (rev (A@U@V@B)) = cost (rev (A@V@U@B))"
proof -
  have 0: "distinct (A@V@U@B)" using assms(7) by auto
  show ?thesis
    using asi_le_iff_rfst[OF assms(1,3-7)] asi_le_iff_rfst[OF assms(1,4,3,6,5) 0] assms(2) by simp
qed

lemma asi_eq_rfst':
  assumes "asi rank r cost"
      and "cost (rev (A@U@V@B)) = cost (rev (A@V@U@B))"
      and "U \<noteq> []"
      and "V \<noteq> []"
      and "take 1 (A @ U @ V @ B) = [r]"
      and "take 1 (A @ V @ U @ B) = [r]"
      and "distinct (A @ U @ V @ B)"
    shows "rank (rev U) = rank (rev V)"
proof -
  have 0: "distinct (A@V@U@B)" using assms(7) by auto
  show ?thesis
    using asi_le_iff_rfst[OF assms(1,3-7)] asi_le_iff_rfst[OF assms(1,4,3,6,5) 0] assms(2) by simp
qed

lemma asi_eq_iff_rfst:
  "\<lbrakk>asi rank r cost; U \<noteq> []; V \<noteq> [];
    take 1 (A @ U @ V @ B) = [r]; take 1 (A @ V @ U @ B) = [r]; distinct (A @ U @ V @ B)\<rbrakk>
    \<Longrightarrow> rank (rev U) = rank (rev V) \<longleftrightarrow> cost (rev (A@U@V@B)) = cost (rev (A@V@U@B))"
  using asi_eq_rfst[of rank r cost] asi_eq_rfst'[of rank r cost] by blast

lemma asi_lt_iff_notr:
  assumes "asi rank r cost"
      and "U \<noteq> []" and "V \<noteq> []"
      and "r \<notin> set (A @ U @ V @ B)"
      and "distinct (A @ U @ V @ B)"
    shows "rank (rev U) < rank (rev V) \<longleftrightarrow> cost (rev (A@U@V@B)) < cost (rev (A@V@U@B))"
  using asi_le_iff_notr[OF assms] asi_eq_iff_notr[OF assms] by auto

lemma asi_lt_iff_rfst:
  assumes "asi rank r cost"
      and "U \<noteq> []" and "V \<noteq> []"
      and "take 1 (A @ U @ V @ B) = [r]"
      and "take 1 (A @ V @ U @ B) = [r]"
      and "distinct (A @ U @ V @ B)"
    shows "rank (rev U) < rank (rev V) \<longleftrightarrow> cost (rev (A@U@V@B)) < cost (rev (A@V@U@B))"
  using asi_le_iff_rfst[OF assms] asi_eq_iff_rfst[OF assms] by auto

lemma asi_lt_notr:
  "\<lbrakk>asi rank r cost; rank (rev U) < rank (rev V); U\<noteq>[]; V\<noteq>[];
    distinct (A@U@V@B); r \<notin> set (A@U@V@B)\<rbrakk>
    \<Longrightarrow> cost (rev (A@U@V@B)) < cost (rev (A@V@U@B))"
  using asi_lt_iff_notr by fastforce

lemma asi_lt_rfst:
  "\<lbrakk>asi rank r cost; rank (rev U) < rank (rev V); U\<noteq>[]; V\<noteq>[]; distinct (A@U@V@B);
    take 1 (A @ U @ V @ B) = [r]; take 1 (A @ V @ U @ B) = [r]\<rbrakk>
    \<Longrightarrow> cost (rev (A@U@V@B)) < cost (rev (A@V@U@B))"
  using asi_lt_iff_rfst by fastforce

lemma asi''_simp_iff:
  "\<lbrakk>asi'' rank r cost; U \<noteq> []; V \<noteq> []; U \<noteq> [r]; V \<noteq> [r]; distinct (A @ U @ V @ B)\<rbrakk>
    \<Longrightarrow> rank (rev U) \<le> rank (rev V) \<longleftrightarrow> cost (rev (A@U@V@B)) \<le> cost (rev (A@V@U@B))"
  unfolding asi''_def by blast

lemma asi''_simp:
  "\<lbrakk>asi'' rank r cost; rank (rev U) \<le> rank (rev V); U\<noteq>[]; V\<noteq>[]; distinct (A@U@V@B); U\<noteq>[r]; V\<noteq>[r]\<rbrakk>
    \<Longrightarrow> cost (rev (A@U@V@B)) \<le> cost (rev (A@V@U@B))"
  unfolding asi''_def by blast

end