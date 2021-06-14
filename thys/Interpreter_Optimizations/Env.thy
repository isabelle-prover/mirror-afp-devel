theory Env
  imports Main "HOL-Library.Library"
begin

section \<open>Generic lemmas\<close>

lemma map_of_list_allI:
  assumes "\<And>k v. f k = Some v \<Longrightarrow> P (k, v)" and
    "\<And>k v. map_of kvs k = Some v \<Longrightarrow> f k = Some v" and
    "distinct (map fst kvs)"
  shows "list_all P kvs"
  using assms(2-)
proof (induction kvs)
  case Nil
  then show ?case by simp
next
  case (Cons kv kvs)
  from Cons.prems(1) have "f (fst kv) = Some (snd kv)"
    by simp
  hence"P kv"
    using assms(1)
    by (cases kv; simp)
  moreover have "list_all P kvs"
    using Cons.IH Cons.prems
    by (metis Some_eq_map_of_iff distinct.simps(2) list.set_intros(2) list.simps(9))
  ultimately show ?case by simp
qed

section \<open>Environment\<close>

locale env =
  fixes
    empty :: 'env and
    get :: "'env \<Rightarrow> 'key \<Rightarrow> 'val option" and
    add :: "'env \<Rightarrow> 'key \<Rightarrow> 'val \<Rightarrow> 'env" and
    to_list :: "'env \<Rightarrow> ('key \<times> 'val) list"
  assumes
    get_empty: "get empty x = None" and
    get_add_eq: "get (add e x v) x = Some v" and
    get_add_neq: "x \<noteq> y \<Longrightarrow> get (add e x v) y = get e y" and
    to_list_correct: "map_of (to_list e) = get e" and
    to_list_distinct: "distinct (map fst (to_list e))"

begin

declare get_empty[simp]
declare get_add_eq[simp]
declare get_add_neq[simp]

definition singleton where
  "singleton \<equiv> add empty"

fun add_list :: "'env \<Rightarrow> ('key \<times> 'val) list \<Rightarrow> 'env" where
  "add_list e [] = e" |
  "add_list e (x # xs) = add (add_list e xs) (fst x) (snd x)"

definition from_list :: "('key \<times> 'val) list \<Rightarrow> 'env" where
  "from_list \<equiv> add_list empty"

lemma from_list_correct: "get (from_list xs) = map_of xs"
proof (induction xs)
  case Nil
  then show ?case
    using get_empty by (simp add: from_list_def)
next
  case (Cons x xs)
  show ?case
    using get_add_eq get_add_neq Cons.IH by (auto simp: from_list_def)
qed

lemma from_list_Nil[simp]: "from_list [] = empty"
  by (simp add: from_list_def)

lemma get_from_list_to_list: "get (from_list (to_list e)) = get e"
proof
  fix x
  show "get (from_list (to_list e)) x = get e x"
    unfolding from_list_correct
    unfolding to_list_correct
    by (rule refl)
qed

lemma to_list_list_allI:
  assumes "\<And>k v. get e k = Some v \<Longrightarrow> P (k, v)"
  shows "list_all P (to_list e)"
proof (rule map_of_list_allI[of "get e"])
  fix k v
  show "get e k = Some v \<Longrightarrow> P (k, v)"
    using assms by simp
next
  fix k v
  show "map_of (to_list e) k = Some v \<Longrightarrow> get e k = Some v"
    unfolding to_list_correct by assumption
next
  show "distinct (map fst (to_list e))"
    by (rule to_list_distinct)
qed

definition map_entry where
  "map_entry e k f \<equiv> case get e k of None \<Rightarrow> e | Some v \<Rightarrow> add e k (f v)"

lemma get_map_entry_eq[simp]: "get (map_entry e k f) k = map_option f (get e k)"
  unfolding map_entry_def
  by (cases "get e k") simp_all

lemma get_map_entry_neq[simp]: "x \<noteq> y \<Longrightarrow> get (map_entry e x f) y = get e y"
  unfolding map_entry_def
  by (cases "get e x") simp_all

lemma dom_map_entry[simp]: "dom (get (map_entry e k f)) = dom (get e)"
  unfolding dom_def
  apply (rule Collect_cong)
  by (metis None_eq_map_option_iff get_map_entry_eq get_map_entry_neq)

lemma get_map_entry_conv:
  "get (map_entry e x f) y = map_option (\<lambda>v. if x = y then f v else  v) (get e y)"
  unfolding map_entry_def
  by (cases "get e x"; cases "x = y"; simp add: option.map_ident)

lemma map_option_comp_map_entry:
  assumes "\<forall>x \<in> ran (get e). f (g x) = f x"
  shows "map_option f \<circ> get (map_entry e k g) = map_option f \<circ> get e"
proof (intro ext)
  fix x
  show "(map_option f \<circ> get (map_entry e k g)) x = (map_option f \<circ> get e) x"
  proof (cases "k = x")
    case True
    thus ?thesis
      using assms(1)
      by (auto simp: get_map_entry_eq option.map_comp intro!: map_option_cong ranI)
  next
    case False
    then show ?thesis
      by (simp add: get_map_entry_neq)
  qed
qed

lemma map_option_comp_get_add:
  assumes "k \<in> dom (get e)" and "\<forall>x \<in> ran (get e). f v = f x"
  shows "map_option f \<circ> get (add e k v) = map_option f \<circ> get e"
proof (intro ext)
  fix x
  show "(map_option f \<circ> get (add e k v)) x = (map_option f \<circ> get e) x"
  proof (cases "x = k")
    case True
    show ?thesis
    proof (cases "get e x")
      case None
      thus ?thesis
        using True assms(1) by auto
    next
      case (Some v')
      thus ?thesis
        using True assms(2) by (auto intro: ranI)
    qed
  next
    case False
    thus ?thesis by simp
  qed
qed

end

end