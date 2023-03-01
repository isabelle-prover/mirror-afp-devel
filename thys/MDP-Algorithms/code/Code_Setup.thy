theory Code_Setup
  imports 
    "HOL-Library.IArray"
    "HOL-Data_Structures.Array_Braun"
    "HOL-Data_Structures.RBT_Map"

    "../MDP_fin" 
    "../Value_Iteration" 
    
    "./lib/DiffArray_ST"

begin

context MDP_nat_disc begin
lemma L_zero:
  assumes "\<And>s. s \<ge> states \<Longrightarrow> apply_bfun v s = 0" "s \<ge> states"
  shows "L d v s = 0"
  using assms
  proof (induction s rule: less_induct)
    case (less x)
    moreover have "r (x, a) = 0" if "a \<in> A x" for a
      by (simp add: less.prems reward_zero_outside)
    moreover have "measure_pmf.expectation (K (x, a)) v = 0" for a
      using K_closed_compl assms less 
      by (blast intro: integral_eq_zero_AE AE_pmfI)
    ultimately show ?case
      by (auto simp: A_ne A_fin L_eq_L\<^sub>a reward_zero_outside)
    qed

lemma \<L>\<^sub>b_zero:
  assumes "\<And>s. s \<ge> states \<Longrightarrow> apply_bfun v s = 0" "s \<ge> states"
  shows "\<L>\<^sub>b v s = 0"
  using assms
  proof (induction s rule: less_induct)
    case (less x)
    have "r (x, a) = 0" if "a \<in> A x" for a
      by (simp add: less.prems reward_zero_outside)
    moreover have "measure_pmf.expectation (K (x, a)) v = 0" for a
      using K_closed_compl assms less 
      by (blast intro: integral_eq_zero_AE AE_pmfI)
      ultimately show ?case
        by (auto simp: A_ne A_fin \<L>\<^sub>b_eq_L\<^sub>a_max')
    qed
end

lemma max_geI: "finite A \<Longrightarrow> A \<noteq> {} \<Longrightarrow> (\<exists>a\<in>A. x \<le> a) \<Longrightarrow> (x \<le> Max A)" for x A
  by (simp add: Max_ge_iff)

section \<open>Least argmax\<close>

fun "least_arg_max_max_ne" where
  "least_arg_max_max_ne f (x#xs) = 
  (fold (\<lambda>y (am, m). let fy = f y in 
   if m < fy then (y, fy) else (am, m)) xs (x, f x))" |
  "least_arg_max_max_ne a [] = undefined"

fun "least_arg_max_ne" where
"least_arg_max_ne f (x#xs) = fst (least_arg_max_max_ne f (x#xs))" |
"least_arg_max_ne a [] = undefined"

lemmas 
  least_arg_max_ne.simps[simp del]
  least_arg_max_max_ne.simps[simp del]

lemma least_arg_max_max_ne_Cons: "least_arg_max_max_ne f (x#y#xs) = 
  (if f x < f y then least_arg_max_max_ne f (y#xs) else least_arg_max_max_ne f (x#xs))"
  by (auto simp: least_arg_max_max_ne.simps)

lemma least_arg_max_max_ne_Cons1: "f x < f y \<Longrightarrow> least_arg_max_max_ne f (x#y#xs) = least_arg_max_max_ne f (y#xs)"
  by (auto simp: least_arg_max_max_ne.simps)

lemma least_arg_max_max_ne_Cons2: "\<not> f x < f y \<Longrightarrow> least_arg_max_max_ne f (x#y#xs) = least_arg_max_max_ne f (x#xs)"
  by (auto simp: least_arg_max_max_ne.simps)

lemma Max_insert_absorb: "finite X \<Longrightarrow> (\<exists>y \<in> X. x \<le> y) \<Longrightarrow> Max (Set.insert x X) = (if X = {} then x else Max X)"
  by (simp add: Max_ge_iff)

lemma Max_insert_absorb': "finite X \<Longrightarrow> y\<in>X \<Longrightarrow> x \<le> y \<Longrightarrow> Max (Set.insert x X) = (if X = {} then x else Max X)"
  using Max_insert_absorb
  by blast

lemma fold_max_eq_arg_max:
  assumes "sorted (x#xs)"
  shows "least_arg_max_max_ne f (x#xs) = (least_arg_max f (List.member (x#xs)), Max (f ` set (x#xs)))"
  using assms
proof (induction xs arbitrary: x)
  case Nil
  then show ?case
    by (auto simp:  List.member_def least_arg_max_def least_arg_max_max_ne.simps is_arg_max_def intro!: Least_equality[symmetric])
next
  case (Cons a xs)
  then show ?case
  proof (cases "is_arg_max f (List.member (x#a#xs)) x")
    case True
    have 1: "least_arg_max f (List.member (x#a#xs)) = x" 
      using True Cons
      unfolding least_arg_max_def 
      by (fastforce intro!: Least_equality simp: in_set_member[symmetric])
    have 2: "Max (f ` set (x#a#xs)) = f x"
      using True unfolding is_arg_max_def 
      by (subst Max_eq_iff) (auto simp add: not_less in_set_member member_rec(1))
    show ?thesis
      unfolding 1 2
      using True
      by (induction xs) (auto simp: least_arg_max_max_ne.simps simp: is_arg_max_linorder member_rec)+
  next
    case False
    have "is_arg_max f (List.member (x#a#xs)) = is_arg_max f (List.member (a#xs))"
      using False by (fastforce simp: least_arg_max_max_ne.simps is_arg_max_linorder member_rec)
    hence 1: "least_arg_max f (List.member (x#a#xs)) = least_arg_max f (List.member (a#xs))"
      using Cons False unfolding least_arg_max_def by auto
    have "f a \<le> f x \<Longrightarrow> is_arg_max f (List.member (x#xs)) = is_arg_max f (List.member xs)"
      using False by (fastforce simp: is_arg_max_linorder member_rec)   
    hence 4: "f a \<le> f x \<Longrightarrow> least_arg_max f (List.member (x#xs)) = least_arg_max f (List.member xs)"
      using Cons False unfolding least_arg_max_def by auto
    have "f a \<le> f x \<Longrightarrow> is_arg_max f (List.member (a#xs)) = is_arg_max f (List.member xs)"
      using False by (fastforce simp: is_arg_max_linorder  member_rec(1))
    hence 3: "f a \<le> f x \<Longrightarrow> least_arg_max f (List.member (a#xs)) = least_arg_max f (List.member xs)"
      using Cons False unfolding least_arg_max_def by auto
    have 2: "Max (f`set (x#a#xs)) = Max (f`set (a#xs))"
      using False 
      by (fastforce simp: nle_le in_set_member is_arg_max_linorder Max_ge_iff simp: member_rec intro!:  max_absorb2 )  
    have 5: "Max (f`set (a#xs)) = Max (f`set (xs)) \<and> Max (f`set (x#xs)) = Max (f`set (xs))" if "f a \<le> f x"
      using False that
      by (cases "xs = []") (auto simp: nle_le is_arg_max_linorder in_set_member[symmetric] intro: order.trans intro!:max_absorb2)
    show ?thesis
      unfolding least_arg_max_max_ne_Cons 1 2 using Cons 5 3 4 by auto
    qed
  qed

lemma least_arg_max_ne_correct:
  assumes "sorted (x#xs)"
  shows "least_arg_max_ne (f :: _ \<Rightarrow> 'b ::linorder) (x#xs) = least_arg_max f (List.member (x#xs))"
  using assms
  by (auto simp: fold_max_eq_arg_max least_arg_max_ne.simps)

lemma least_arg_max_ne_cong: 
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> g x = f x"
  shows "least_arg_max_max_ne f xs = least_arg_max_max_ne g xs"
proof (cases xs)
  case Nil
  then show ?thesis 
    by (metis least_arg_max_max_ne.elims list.discI)
next
  case (Cons a list)
  then show ?thesis 
  using assms
  by (auto simp: least_arg_max_max_ne.simps intro!: List.fold_cong)
qed

lemma least_arg_max_max_ne_app:
  assumes "\<And>y. y \<in> set (x#xs) \<Longrightarrow> f' (g y) = (f y)"
  shows "(case (least_arg_max_max_ne f (x#xs)) of (a, m) \<Rightarrow> (g a, m)) = least_arg_max_max_ne f' (map g (x#xs))"
  using assms
proof (induction xs arbitrary: x)
  case Nil
  then show ?case
    by (auto simp: least_arg_max_max_ne.simps)
next
  case (Cons a xs)
    thus ?case
      by (cases "f x <  f a") (auto simp: least_arg_max_max_ne_Cons1 least_arg_max_max_ne_Cons2)
  qed

lemma least_arg_max_max_ne_app':
  assumes "\<And>y. y \<in> set xs \<Longrightarrow> f' (g y) = (f y)" "xs \<noteq> []"
  shows "(case (least_arg_max_max_ne f xs) of (a, m) \<Rightarrow> (g a, m)) = least_arg_max_max_ne f' (map g xs)"
  using assms
  by (cases xs) (auto intro!: least_arg_max_max_ne_app[simplified])

lemma fold_max_eq_arg_max': "xs \<noteq> [] \<Longrightarrow> sorted xs \<Longrightarrow> least_arg_max_max_ne f xs = (least_arg_max f (List.member xs), Max (f ` set xs))"
  using fold_max_eq_arg_max by (metis list.exhaust)

lemma least_arg_max_cong: "(\<And>x. P x \<Longrightarrow> f x = g x) \<Longrightarrow> least_arg_max f P = least_arg_max g P"
  unfolding least_arg_max_def using is_arg_max_cong' by metis

lemma least_arg_max_cong': "P = Q \<Longrightarrow>  (\<And>x. P x \<Longrightarrow> f x = g x) \<Longrightarrow> least_arg_max f P = least_arg_max g Q"
  unfolding least_arg_max_def using is_arg_max_cong' by metis

section \<open>Congruence rule for fold\<close>

lemma fold_cong':
  assumes "(\<And>x acc. P acc \<Longrightarrow> x \<in> set xs \<Longrightarrow> f x acc = g x acc \<and> P (f x acc))" "P a"
  shows "fold f xs a = fold g xs a"
  using assms
proof (induction xs arbitrary: a)
  case (Cons a xs y)
  show ?case
    using Cons(2)[OF Cons(3), of a] 
    by (auto intro!: Cons(2) intro: Cons.IH)
qed auto


section \<open>MDP type\<close>

datatype MDP = MDP (disc: real) (states: nat) 
  (transitions: "(((nat \<times> (real \<times> ((nat \<times> real) list))) RBT.rbt)) iarray")

abbreviation "is_MDP_states mdp \<equiv> 
  IArray.length (transitions mdp) = states mdp"

abbreviation "is_MDP_actions mdp \<equiv> IArray.all (\<lambda>t. 
  rbt t \<and> 
  sorted1 (Tree2.inorder t) \<and> 
  t \<noteq> empty \<and> 
  (\<forall>(_, _, probs) \<in> set (inorder t). sum_list (map snd probs) = 1
    \<and> (list_all (\<lambda>(s, p). p \<ge> 0 \<and> s<states mdp) probs))) (transitions mdp)"

abbreviation "is_MDP_disc mdp \<equiv> (0 \<le> disc mdp \<and> disc mdp < 1)"

definition is_MDP :: "MDP \<Rightarrow> bool"
  where "is_MDP mdp \<longleftrightarrow> is_MDP_states mdp \<and> is_MDP_disc mdp \<and> is_MDP_actions mdp"

definition "trivial_MDP = MDP 0 0 (IArray [])"

lemma trivial_MDP: "is_MDP trivial_MDP"
  unfolding trivial_MDP_def is_MDP_def by auto

typedef Valid_MDP = "{mdp. is_MDP mdp}"
  using trivial_MDP by auto

setup_lifting type_definition_Valid_MDP

definition "error_mdp = trivial_MDP"

declare [[code abort: error_mdp]]

lift_definition to_valid_MDP :: "MDP \<Rightarrow> Valid_MDP" is 
  "\<lambda>mdp. if is_MDP mdp then mdp else Code.abort (STR ''not an MDP'') (\<lambda>_. trivial_MDP)" 
  by (simp add: trivial_MDP_def is_MDP_def)

context Map_by_Ordered begin
lemmas map_specs(5)[intro]

lemma map_of_Some_in_set: "AList_Upd_Del.map_of xs k = Some v \<Longrightarrow> (k, v) \<in> set xs"
  by (induction xs) (auto split: if_splits)

lemma map_of_None_notin_set: "AList_Upd_Del.map_of xs k = None \<Longrightarrow> k \<notin> fst ` set xs"
  by (induction xs) (fastforce split: if_splits)+

definition "entries m = set (inorder m)"
definition "keys m = fst ` set (inorder m)"

lemma lookup_some_set_a_inorder: 
  assumes "invar m" "lookup m x = Some y" 
  shows "(x, y) \<in> entries m"
  using inorder_lookup assms map_of_Some_in_set invar_def entries_def by metis

lemma lookup_None_set_inorder: 
  assumes "invar m" "lookup m x = None" 
  shows "x \<notin> keys m"
  using assms inorder_lookup map_of_None_notin_set keys_def invar_def by metis

lemma entries_imp_keys[intro]: "(x,y) \<in> entries m \<Longrightarrow> x \<in> keys m"
  unfolding keys_def entries_def by force

lemma lookup_some_set_key: "invar m \<Longrightarrow> lookup m x = Some y \<Longrightarrow> x \<in> keys m"
  using lookup_some_set_a_inorder by force

lemma lookup_in_keys: "invar m \<Longrightarrow> x \<in> keys m \<Longrightarrow> \<exists>y. lookup m x = Some y"
  using lookup_None_set_inorder by auto

lemma lookup_notin_keys: "invar m \<Longrightarrow> x \<notin> keys m \<Longrightarrow> lookup m x = None"
  by (meson lookup_some_set_key not_Some_eq)

lemma inorder_delete: "invar m \<Longrightarrow> inorder m = kv#xs \<Longrightarrow> inorder ((delete (fst kv) m)) = xs"
  unfolding invar_def
  using AList_Upd_Del.del_list.simps(2)[of _ "fst kv" "snd kv"]
  by (simp add: local.inorder_delete)

lemma inorder_lookup_Some: "invar m \<Longrightarrow> (k, v) \<in> entries m \<Longrightarrow> lookup m k = Some v"
  unfolding entries_def
proof (induction "inorder m" arbitrary: m)
  case Nil thus ?case by auto 
next
  case (Cons a x)
  show ?case
  proof (cases "a = (k,v)")
    case True
    then show ?thesis 
    using inorder_lookup Cons AList_Upd_Del.map_of.simps(2) invar_def by metis
  next
    case False
    have "lookup (delete (fst a) m) k = Some v"
      using False Cons(2)[symmetric] Cons(3-4)
      by (fastforce simp: inorder_delete map_specs intro!: Cons(1))
    then show ?thesis
      by (metis map_delete fun_upd_other fun_upd_same Cons(3) option.distinct(1))
  qed
qed

lemma keys_eq_lookup_Some: "invar m \<Longrightarrow> keys m = {k. \<exists>v. lookup m k = Some v}"
  using lookup_some_set_key lookup_in_keys by auto

lemma keys_eq_fst_entries: "invar m \<Longrightarrow> keys m = fst ` entries m"
  unfolding entries_def keys_def by auto

lemma keys_update[simp]: "invar m \<Longrightarrow> keys (update k v m) = Set.insert k (keys m)"
  by (subst keys_eq_lookup_Some) (auto simp add: lookup_notin_keys lookup_in_keys map_specs split: if_splits)

definition "is_empty t \<longleftrightarrow> inorder t = []"

lemma is_empty_iff_entries_empty: "is_empty t \<longleftrightarrow> entries t = {}"
  by (simp add: entries_def is_empty_def)

lemma is_empty_iff_keys_empty: "is_empty t \<longleftrightarrow> keys t = {}"
  by (simp add: keys_def is_empty_def)

lemma finite_keys: "finite (keys t)"
  by (simp add: keys_def)

lemma finite_entries: "finite (entries t)"
  by (simp add: entries_def)

lemma keys_empty[simp]: "keys empty = {}"
  by (auto simp: keys_def inorder_empty)

definition "lookup' m k = the (lookup m k)"

section \<open>Converting Lists to Maps\<close>

definition "from_list' f xs = foldl (\<lambda>acc s. update s (f s) acc) empty xs"
definition "from_list xs = foldl (\<lambda>acc (k,v). update k v acc) empty xs"

                                                                
lemmas invar_empty[simp, intro]

lemma from_list_invar[simp]: "invar (from_list' f xs)"
proof -
  have "invar t \<Longrightarrow> invar (foldl (\<lambda>acc s. update s (f s) acc) t xs)" for t
    by (induction xs arbitrary: t) auto
  thus ?thesis
    unfolding from_list'_def by auto
qed

lemma from_list_snoc[simp]: "(from_list' f (xs @[y])) = update y (f y) (from_list' f xs)"
  by (auto simp: from_list'_def)

lemma from_list_empty[simp]: "from_list' f [] = empty"
  unfolding from_list'_def by simp

lemma from_list_keys[simp]: "keys (from_list' f xs) = set xs"
  by (induction xs rule: List.rev_induct) (auto simp: map_update)

lemma from_list_lookup[simp]: "x \<in> set xs \<Longrightarrow> lookup (from_list' f xs)  x = Some (f x)"
  by (induction xs rule: List.rev_induct) (auto simp: map_update)

lemma from_list_lookup'[simp]: "x \<in> set xs \<Longrightarrow> lookup' (from_list' f xs)  x = f x"
  unfolding lookup'_def
  using from_list_lookup
  by auto

lemma from_list_snoc'[simp]: "(from_list (xs @[(k,v)])) = update k v (from_list xs)"
  by (auto simp: from_list_def)

lemma from_list_invar'[simp]: "invar (from_list xs)"
proof -
  have "invar t \<Longrightarrow> invar (foldl (\<lambda>acc (k,v). update k v acc) t xs)" for t
    by (induction xs arbitrary: t) auto
  thus ?thesis
    unfolding from_list_def by auto
qed

lemma lookup_from_list_distinct: "(x,y) \<in> set xs \<Longrightarrow> distinct (map fst xs) \<Longrightarrow> lookup (from_list xs) x = Some y"
  by (induction xs  arbitrary: x y rule: List.rev_induct) (auto simp: rev_image_eqI map_update)

lemma lookup'_from_list_distinct: "(x,y) \<in> set xs \<Longrightarrow> distinct (map fst xs) \<Longrightarrow> lookup' (from_list xs) x = y"
  using lookup_from_list_distinct unfolding lookup'_def
  by auto

lemma distinct_inorder: "invar m \<Longrightarrow> distinct (map fst (inorder m))"
  using invar_def strict_sorted_iff by blast

lemmas map_empty[simp]

lemma from_list_lookup_notin[simp]: "x \<notin> set xs \<Longrightarrow> lookup (from_list' f xs)  x = None"
  by (induction xs rule: List.rev_induct) (auto simp: map_update)
end

locale Map_by_Ordered_nat_zero = Map_by_Ordered empty update delete lookup inorder inv' for empty and update :: "nat \<Rightarrow> ('a::zero) \<Rightarrow> 't \<Rightarrow> 't" and delete lookup inorder inv'
begin

definition map_to_fun :: "'t \<Rightarrow> nat \<Rightarrow> 'a" where 
  "map_to_fun m n = (if invar m then case lookup m n of None \<Rightarrow> 0 | Some r \<Rightarrow> r else 0)"

lemma map_to_fun_update: "invar m \<Longrightarrow> (map_to_fun (update k v m)) = (map_to_fun m)(k := v)"
  by (fastforce simp: map_to_fun_def map_update)
end

locale Map_by_Ordered_nat_real = Map_by_Ordered empty update delete lookup inorder inv' for empty and update :: "nat \<Rightarrow> real \<Rightarrow> 't \<Rightarrow> 't" and delete lookup inorder inv'
begin

lift_definition map_to_bfun :: "'t \<Rightarrow> nat \<Rightarrow>\<^sub>b real" is 
  "\<lambda>m n. if invar m then case lookup m n of None \<Rightarrow> 0 | Some r \<Rightarrow> r else 0"
proof -
  fix t
  show "(\<lambda>n. if invar t then case lookup t n of None \<Rightarrow> 0 | Some r \<Rightarrow> r else 0) \<in> bfun"
  proof (cases "is_empty t \<or> \<not> invar t")
    case True
    then show ?thesis 
      by (auto simp add: is_empty_iff_keys_empty lookup_notin_keys)
  next
    case False
    have "norm (case lookup t x of None \<Rightarrow> 0 | Some r \<Rightarrow> r) \<le> (MAX a \<in> entries t. abs (snd a))" for x
       using False is_empty_iff_entries_empty lookup_some_set_a_inorder[of t x]
       by (fastforce simp: Max_ge_iff finite_entries split: option.splits)
     thus ?thesis
       using False by (intro bfun_normI) auto
   qed
 qed

lemma map_to_bfun_update: "invar m \<Longrightarrow> apply_bfun (map_to_bfun (update k v m)) = (map_to_bfun m)(k := v)"
  by (fastforce simp: map_to_bfun.rep_eq map_update)
  
end

locale Array' = Array +
  assumes lookup_array: "i < length xs \<Longrightarrow> lookup (array xs) i = xs ! i"

locale Array_real = Array' lookup update len array list invar for lookup :: "'t \<Rightarrow> nat \<Rightarrow> real" and update len array list invar
begin

lift_definition map_to_bfun :: "'t \<Rightarrow> nat \<Rightarrow>\<^sub>b real" is 
  "\<lambda>m n. if invar m \<and> n < len m then lookup m n else 0"
  using bounded_const by fastforce

lemma map_to_bfun_update: 
  assumes "invar m" "k < len m"
  shows "apply_bfun (map_to_bfun (update k v m)) = (map_to_bfun m)(k := v)"
  using assms
  by (auto simp: invar_update map_to_bfun.rep_eq len_array lookup update)
end

locale Array_zero = Array' lookup update len array list invar for lookup :: "'t \<Rightarrow> nat \<Rightarrow> 'a::zero" and update len array list invar
begin

definition map_to_fun :: "'t \<Rightarrow> nat \<Rightarrow> 'a" where 
  "map_to_fun m n = (if invar m \<and> n < len m then lookup m n else 0)"

lemma map_to_fun_update: "invar m \<Longrightarrow> k < len m \<Longrightarrow> (map_to_fun (update k v m)) = (map_to_fun m)(k := v)"
  by (auto simp: invar_update map_to_fun_def len_array lookup update)

end

context Array' begin
lemma lookup_in_list: "invar m \<Longrightarrow> x < len m \<Longrightarrow> lookup m x \<in> set (list m)"
  using lookup len_array
  by auto

definition "arr_tabulate f n = array (map f [0..<n])"

lemma invar_tabulate[simp]: "invar (arr_tabulate f n)"
  by (auto simp: arr_tabulate_def invar_array)


lemma len_tabulate[simp]: "len (arr_tabulate f n) = n"
  using arr_tabulate_def array invar_tabulate len_array by auto

lemma lookup_tabulate[simp]: "i < n \<Longrightarrow> lookup (arr_tabulate f n) i = f i"
  by (simp add: arr_tabulate_def lookup_array)

lemmas invar_update[intro]
end

lemma foldr_Cons[simp]: "foldr (#) xs ys = xs@ys"
  by (induction xs) auto

interpretation starray_Array: 
  Array' starray_get "\<lambda>i x arr. starray_set arr i x" starray_length starray_of_list 
    "\<lambda>arr. starray_foldr (\<lambda>x xs. x # xs) arr []" "\<lambda>_. True"
  by standard auto

definition "starray_to_list a = tabulate (starray_length a) (starray_get a)"


lemma set_pmf_of_list:
  assumes "pmf_of_list_wf ps" 
  shows "set_pmf (pmf_of_list ps) = {a | a b. (a,b) \<in> set ps \<and> b \<noteq> 0}"
proof safe
  fix x 
  assume "x \<in> set_pmf (pmf_of_list ps)"
  hence "sum_list (map snd (filter (\<lambda>z. fst z = x) ps)) \<noteq> 0"
    using assms
    by (auto simp: set_pmf_eq pmf_pmf_of_list)
  hence "\<exists>y \<in> set (map snd (filter (\<lambda>z. fst z = x) ps)). y \<noteq> 0"
    by (metis map_idI sum_list_0)
  then obtain sp where "snd sp \<noteq> 0" "fst sp = x" "sp \<in> set ps"
    by auto
  thus "\<exists>a b. x = a \<and> (a, b) \<in> set ps \<and> b \<noteq> 0"
    by force
next
  fix x a b
  assume h: "(a, b) \<in> set ps" "b \<noteq> 0"
  have "\<Sum>(Set.insert a X) = a + \<Sum> (X-{a})" if "finite X" for X and a :: real
    using that 
    by (meson sum.insert_remove)
  hence *: "\<forall>b \<in> set ps. b \<ge> 0 \<Longrightarrow> b \<in> set ps \<Longrightarrow>  b \<le> sum_list ps" for ps
    by (induction ps ) (auto intro!: sum_list_nonneg)
  have "pmf (pmf_of_list ps) a \<ge> b"
    using assms  \<open>(a, b) \<in> set ps\<close> 
    by (fastforce simp add: image_iff pmf_pmf_of_list pmf_of_list_wf_def intro!: * )
  thus "a \<in> set_pmf (pmf_of_list ps)"
    unfolding set_pmf_iff
    using h assms pmf_of_list_wf_def by fastforce
qed

lemma set_pmf_of_list':
  assumes "pmf_of_list_wf ps" 
  shows "set_pmf (pmf_of_list ps) = {a | a b. (a,b) \<in> set ps \<and> b > 0}"
  unfolding set_pmf_of_list[OF assms]
  using assms unfolding pmf_of_list_wf_def
  by fastforce

locale MDP_Code_raw =
  S_Map : Array' "s_lookup :: 'ts \<Rightarrow> nat \<Rightarrow> 'ta"  s_update s_len s_array s_list s_invar +
  A_Map : Map_by_Ordered a_empty "a_update :: nat \<Rightarrow> (real \<times> ((nat \<times> real) list)) \<Rightarrow> 'ta \<Rightarrow> 'ta" a_delete a_lookup a_inorder a_inv
  for s_lookup s_update s_len s_array s_list s_invar
  and a_empty a_update a_delete a_lookup a_inorder a_inv +
fixes
  mdp :: 'ts and
  states :: nat
assumes
  s_invar: "s_invar mdp" and
  s_len: "s_len mdp = states" and
  A_inv_locale: "\<forall>am \<in> set (s_list mdp). A_Map.invar am" and
  A_ne_locale: "\<forall>am \<in> set (s_list mdp). \<not> A_Map.is_empty am" and
  K_closed_locale: 
  "\<forall>am \<in> set (s_list mdp). \<forall>(_, _, p) \<in> A_Map.entries am. 
    list_all (\<lambda>(s', p). s' <states) p" and
  lists_are_pmfs: "\<forall>am \<in> set (s_list mdp). \<forall>(_, _, p) \<in> A_Map.entries am. pmf_of_list_wf p"
begin

definition "a_lookup' m x = (
  case (a_lookup m x) of 
   Some v \<Rightarrow> v
  | None \<Rightarrow> Code.abort (STR ''MDP is missing action information'') (\<lambda>_. undefined))" 

definition "MDP_A s = (if s < states then A_Map.keys (s_lookup mdp s) else {0})"

definition "MDP_r sa = (if fst sa \<ge> states then 0 else
  let a_map = s_lookup mdp (fst sa) in 
  (case a_lookup a_map (snd sa) of Some (r, _) \<Rightarrow> r | None \<Rightarrow> 0)
)"

definition "MDP_K sa = (
  if fst sa \<ge> states then 
    return_pmf (fst sa) 
  else 
    let a_map = s_lookup mdp (fst sa) in (
      case a_lookup a_map (snd sa) of 
        Some (_, p) \<Rightarrow> pmf_of_list p 
      | None \<Rightarrow> return_pmf (fst sa))
)"

lemma MDP_r_zero_notin_states: "s \<ge> states  \<Longrightarrow> MDP_r (s, a) = 0" for s a
  unfolding MDP_r_def
  by auto


lemma a_lookup_some_in_A: "s < states \<Longrightarrow> a_lookup (s_lookup mdp s) a = Some (aa, b) \<Longrightarrow> a \<in> MDP_A s"
  using A_Map.lookup_some_set_key A_inv_locale S_Map.lookup_in_list s_len s_invar
  by (simp add: A_Map.keys_def MDP_A_def)

lemma a_lookup_None_notin_A: "s < states \<Longrightarrow> a_lookup (s_lookup mdp s) a = None \<Longrightarrow> a \<notin> MDP_A s"
  unfolding MDP_A_def
  using A_Map.lookup_None_set_inorder A_inv_locale S_Map.lookup_in_list s_invar s_len
  by auto

lemma MDP_r_zero_notin_A: "s < states \<Longrightarrow> a \<notin> MDP_A s  \<Longrightarrow> MDP_r (s, a) = 0" for s a
  using a_lookup_some_in_A
  by (auto split: option.splits simp: MDP_r_def)

lemma MDP_r_in_A_eq: "s < states \<Longrightarrow> a \<in> MDP_A s \<Longrightarrow> MDP_r (s, a) = fst ((a_lookup' (s_lookup mdp s) a))"
  using a_lookup_None_notin_A by (auto split: option.splits simp: a_lookup'_def MDP_r_def)

lemma range_MDP_r_subs: "range (MDP_r) \<subseteq> {0} \<union> {fst ((a_lookup' (s_lookup mdp s) a)) | s a. s < states \<and> a \<in> MDP_A s}"
  using MDP_r_in_A_eq MDP_r_zero_notin_A MDP_r_zero_notin_states 
  by (auto) (metis not_le)

lemma finite_MDP_A[simp]: "finite (MDP_A s)"
  unfolding MDP_A_def
  by (simp add: A_Map.finite_keys)

lemma finite_sa: "finite {(s,a). s < states \<and> a \<in> MDP_A s}"
proof -
  have "{(s,a). s < states \<and> a \<in> MDP_A s} \<subseteq> {(s,a). s < states \<and> a \<in> (\<Union>s < states. MDP_A s)}"
    by auto
  moreover have "finite {(s,a). s < states \<and> a \<in> (\<Union>s < states. MDP_A s)}"
    by auto
  ultimately show ?thesis
    using finite_subset by blast
qed

lemma finite_r_lookup: "finite {fst ((a_lookup' (s_lookup mdp s) a)) | s a. s < states \<and> a \<in> MDP_A s}"
proof -
  have aux: "{fst ((a_lookup' (s_lookup mdp s) a)) | s a. s < states \<and> a \<in> MDP_A s} = {fst ((a_lookup' (s_lookup mdp (fst sa)) (snd sa))) | sa. fst sa < states \<and> snd sa \<in> MDP_A (fst sa)}"
    by auto
  show ?thesis
    unfolding aux
    using finite_sa
    by (fastforce intro!: finite_image_set simp: case_prod_unfold)
qed

lemma bounded_MDP_r: "bounded (range MDP_r)"
  using finite_r_lookup range_MDP_r_subs
  by (simp add: finite_imp_bounded finite_subset)

lemma MDP_A_ne[simp]: "(MDP_A s) \<noteq> {}"
  using A_ne_locale s_invar s_len
  by (auto simp: MDP_A_def A_Map.is_empty_iff_keys_empty S_Map.lookup_in_list)

lemma K_closed_locale': 
  "am \<in> set (s_list mdp) \<Longrightarrow> (x, y, p) \<in> A_Map.entries am \<Longrightarrow> (s', prob) \<in> set p \<Longrightarrow> s' <states"
  using K_closed_locale
  by (fastforce simp: list.pred_set case_prod_beta)
  
lemma MDP_K_closed: 
  assumes "s<states" 
  shows "set_pmf (MDP_K (s, a)) \<subseteq> {0..<states}"
proof 
  fix s'
  assume h: "s' \<in> set_pmf (MDP_K (s, a))"
  show "s' \<in> {0..<states}"
  proof (cases "a \<in> MDP_A s")
    case False
    thus ?thesis
    using assms h
    using a_lookup_some_in_A 
    by (auto simp: MDP_K_def split: option.splits)
  next
    case True
    from h obtain r ps where "a_lookup (s_lookup mdp s) a = Some (r, ps)" and **:"s' \<in> set_pmf (pmf_of_list ps)"
      unfolding MDP_K_def using assms True a_lookup_None_notin_A
      by (auto split: option.splits)
    have "pmf_of_list_wf ps"
      using lists_are_pmfs
      by (metis A_Map.Map_by_Ordered_axioms A_inv_locale Map_by_Ordered.lookup_some_set_a_inorder S_Map.lookup_in_list \<open>a_lookup (s_lookup mdp s) a = Some (r, ps)\<close> assms case_prod_conv s_invar s_len)
    have ***:"(s'', p) \<in> set ps \<Longrightarrow> p > 0 \<Longrightarrow> s'' < states" for s'' p
      by (metis A_Map.Map_by_Ordered_axioms A_inv_locale K_closed_locale' Map_by_Ordered.lookup_some_set_a_inorder S_Map.lookup_in_list \<open>a_lookup (s_lookup mdp s) a = Some (r, ps)\<close> assms s_invar s_len)
    have "s' < states"
      using *** ** set_pmf_of_list'[OF \<open>pmf_of_list_wf ps\<close>]
      by blast
    then show ?thesis by auto
  qed
qed

lemma MDP_K_comp_closed: "s \<ge> states \<Longrightarrow> set_pmf (MDP_K (s, a)) \<subseteq> {states..}"
  unfolding MDP_K_def
  by auto

lemma MDP_A_outside: "states \<le> s \<Longrightarrow> MDP_A s = {0}"
  unfolding MDP_A_def
  by auto


lemma invar_s_lookup: "s < states \<Longrightarrow> A_Map.invar (s_lookup mdp s)"
  by (simp add: A_inv_locale S_Map.lookup_in_list s_invar s_len)

lemma ne_s_lookup: "s < states \<Longrightarrow> \<not> A_Map.is_empty (s_lookup mdp s)"
  using A_ne_locale S_Map.lookup_in_list s_invar s_len by blast

lemma sa_lookup_eq:
  assumes "s < states" "a \<in> MDP_A s" "(a_lookup (s_lookup mdp s) a) = Some (r, ps)"
  shows "r = MDP_r (s,a)" "pmf_of_list ps = MDP_K (s, a)"
  unfolding MDP_K_def 
  using assms a_lookup_None_notin_A
  by (auto split: option.splits simp: MDP_r_in_A_eq a_lookup'_def)

lemma fst_sa_lookup'_eq:
  assumes "s < states" "a \<in> MDP_A s"
  shows "fst (a_lookup' (s_lookup mdp s) a) = MDP_r (s, a)"
  by (simp add: MDP_r_in_A_eq assms)


lemma snd_sa_lookup'_eq:
  assumes "s < states" "a \<in> MDP_A s"
  shows "pmf_of_list (snd (a_lookup' (s_lookup mdp s) a)) = MDP_K (s, a)"
  using assms a_lookup'_def sa_lookup_eq a_lookup_None_notin_A
  by (auto split: option.splits)

lemma entries_A_eq_r: "s < states \<Longrightarrow> (a, r, succs) \<in> A_Map.entries (s_lookup mdp s) \<Longrightarrow> r = MDP_r (s, a)"
  using sa_lookup_eq[OF _ a_lookup_some_in_A] A_Map.inorder_lookup_Some[OF invar_s_lookup]  
  by simp

lemma entries_A_eq_K: "s < states \<Longrightarrow> (a, r, succs) \<in> A_Map.entries (s_lookup mdp s) \<Longrightarrow> pmf_of_list succs = MDP_K (s, a)"
  using sa_lookup_eq[OF _ a_lookup_some_in_A] A_Map.inorder_lookup_Some[OF invar_s_lookup]  
  by simp

lemma a_inorderD:
  assumes "s < states" "(a, r, succs) \<in> A_Map.entries (s_lookup mdp s)"
  shows "a \<in> MDP_A s" "r = MDP_r (s, a)" "pmf_of_list succs = MDP_K (s, a)"
  using assms A_Map.inorder_lookup_Some a_lookup_some_in_A invar_s_lookup entries_A_eq_r entries_A_eq_K 
  by auto


lemma a_map_entries_lookup: "s < states \<Longrightarrow> a \<in> MDP_A s \<Longrightarrow> (a, a_lookup' (s_lookup mdp s) a) \<in> A_Map.entries (s_lookup mdp s)"
  by (metis A_Map.lookup_in_keys A_Map.lookup_some_set_a_inorder MDP_A_def a_lookup'_def invar_s_lookup option.simps(5))

lemma lists_are_pmfs': "am\<in>set (s_list mdp) \<Longrightarrow>  (a,r,p)\<in>A_Map.entries am \<Longrightarrow> pmf_of_list_wf p"
  using lists_are_pmfs by fastforce

lemma lists_are_pmfs'': "am\<in>set (s_list mdp) \<Longrightarrow>  (a,rp)\<in>A_Map.entries am \<Longrightarrow> pmf_of_list_wf (snd rp)"
  using lists_are_pmfs by fastforce

lemma lists_are_pmfs''': "s < states \<Longrightarrow>  (a,rp)\<in>A_Map.entries (s_lookup mdp s) \<Longrightarrow> pmf_of_list_wf (snd rp)"
  using S_Map.lookup_in_list lists_are_pmfs'' s_invar s_len by blast

lemma pmf_of_list_wf_mdp:
  assumes "s < states" "a \<in> MDP_A s"
  shows "pmf_of_list_wf (snd (a_lookup' (s_lookup mdp s) a))"
  using assms a_map_entries_lookup
  by (auto intro: lists_are_pmfs'''[of s a])


lemma  set_list_pmf_in_states:
   assumes "s < states" "a \<in> MDP_A s" "(aa, b) \<in> set (snd (a_lookup' (s_lookup mdp s) a)) "
shows 
  "aa < states"
proof -
  have"(s_lookup mdp s) \<in> set( s_list mdp)"
    using S_Map.lookup_in_list assms(1) s_invar s_len by blast
  moreover have  "(a, (a_lookup' (s_lookup mdp s) a)) \<in> A_Map.entries (s_lookup mdp s)"
    by (metis A_Map.lookup_in_keys A_Map.lookup_some_set_a_inorder MDP_A_def a_lookup'_def assms(1) assms(2) invar_s_lookup option.case(2))
  ultimately show ?thesis
  using K_closed_locale assms
  by (fastforce simp: case_prod_beta list_all_def)
qed
end


lemma sum_list_partition_fst: "(\<Sum>sp\<leftarrow>ps. f sp) = (\<Sum>a\<in>fst ` set ps. \<Sum>sp\<leftarrow>filter (\<lambda>z. fst z = a) ps. f sp)"
proof (induction ps)
  case Nil
  then show ?case by auto
next
    have *:"(if b then x else y) + z =  (if b then x+z else y+z)" for b x y z
      by auto
  case (Cons a ps)
  show ?case
  proof (cases "fst a \<in> fst ` set ps")
    case True
      have "sum_list (map f (a # ps)) = f a + (\<Sum>a\<in>fst ` set ps. sum_list (map f (filter (\<lambda>z. fst z = a) ps)))"      
      by (auto dest: simp: Cons if_distrib  sum.insert_remove cong: sum.cong if_cong)
    also have "\<dots> = (\<Sum>aa\<in>fst ` set ps. (if fst a =  aa then f a else 0)) + (\<Sum>aa\<in>fst ` set ps. sum_list (map f (filter (\<lambda>z. fst z = aa) ps)))"  
      using True by auto
    also have "\<dots> = (\<Sum>aa\<in>fst ` set ps. (if fst a =  aa then f a else 0) +  sum_list (map f (filter (\<lambda>z. fst z = aa) ps)))" 
      by (auto simp:  sum.distrib)
    also have "\<dots> = (\<Sum>aa\<in>fst ` set (a # ps). sum_list (map f (filter (\<lambda>z. fst z = aa) (a # ps))))"
      by (auto simp: * True if_distrib[of "map _"] if_distrib[of "sum_list"] insert_absorb cong: if_cong)
    finally show ?thesis.
  next
      case False     
      have "sum_list (map f (a # ps)) = f a + (\<Sum>a\<in>fst ` set ps. sum_list (map f (filter (\<lambda>z. fst z = a) ps)))"      
      by (auto dest: simp: Cons if_distrib  sum.insert_remove cong: sum.cong if_cong)
    also have "\<dots> = (\<Sum>aa\<in>fst ` set (a#ps). (if fst a =  aa then f a else 0)) + (\<Sum>aa\<in>fst ` set ps. sum_list (map f (filter (\<lambda>z. fst z = aa) ps)))"  
      using False
      by (auto simp: )
    also have "\<dots> = (\<Sum>aa\<in>fst ` set (a#ps). (if fst a =  aa then f a else 0)) + (\<Sum>aa\<in>fst ` set (a#ps). sum_list (map f (filter (\<lambda>z. fst z = aa) ps)))"  
    proof -
      have *: "(\<And>x. x \<in> set xs \<Longrightarrow> x = 0) \<Longrightarrow> sum_list xs = 0" for xs
        by (induction xs) auto
      have "(sum_list (map f (filter (\<lambda>z. fst z = fst a) ps))) = 0"
        using False
        by (intro *) (auto intro: fst_eqD)
      thus ?thesis
        by (auto simp: False)
    qed
    also have "\<dots> = (\<Sum>aa\<in>fst ` set (a#ps). (if fst a =  aa then f a else 0) +  sum_list (map f (filter (\<lambda>z. fst z = aa) ps)))" 
      by (auto simp:  sum.distrib)
    also have "\<dots> = (\<Sum>aa\<in>fst ` set (a # ps). sum_list (map f (filter (\<lambda>z. fst z = aa) (a # ps))))"
      by (auto simp: * False if_distrib[of "map _"] if_distrib[of "sum_list"] insert_absorb cong: if_cong)
    finally show ?thesis.
  qed
qed

lemma pmf_of_list_expectation:
  assumes "pmf_of_list_wf ps"
  shows "measure_pmf.expectation (pmf_of_list ps) f = (\<Sum>(s', p)\<leftarrow> ps. p * f s')"
proof -
  have sumlist_cong: "sum_list (map f xs) = sum_list (map g xs)" if "\<And>x. x \<in> set xs \<Longrightarrow> f x = g x" for f g xs
    using that
    by (induction xs) auto
  have "(\<Sum>(s', p)\<leftarrow> ps. p * f s') = sum_list (map (\<lambda>sp. snd sp * f (fst sp)) ps)"
    by (metis case_prod_conv fst_def old.prod.exhaust snd_def)
  also have "\<dots> = (\<Sum>a \<in> fst ` (set ps). sum_list (map (\<lambda>sp. snd sp * f (fst sp)) (filter (\<lambda>z. fst z = a) ps)))"
    using sum_list_partition_fst
    by auto
    also have "\<dots> = (\<Sum>a \<in> fst ` (set ps). sum_list (map snd (filter (\<lambda>z. fst z = a) ps)) * f a)"
      by (auto simp: add.commute set_filter map_eq_conv sum_list_mult_const[symmetric] intro!: sumlist_cong  sum.cong)
    also have "\<dots> = (\<Sum>a \<in> {u. \<exists>b. (u, b) \<in> set ps \<and> b \<noteq> 0} \<union> {u. \<exists>b. (u,b) \<in> set ps \<and> (\<forall>b. (u,b) \<in> set ps \<longrightarrow> b = 0)}. sum_list (map snd (filter (\<lambda>z. fst z = a) ps)) * f a)"
    proof -
      have "fst ` (set ps) = {u. \<exists>b. (u, b) \<in> set ps}" 
        by force
      also have "\<dots> = {u. \<exists>b. (u, b) \<in> set ps \<and> b \<noteq> 0} \<union> {u. \<exists>b. (u,b) \<in> set ps \<and> (\<forall>b. (u,b) \<in> set ps \<longrightarrow> b = 0)}"
        by auto
      finally show ?thesis by auto
    qed
          also have "\<dots> = (\<Sum>a \<in> {u. \<exists>b. (u, b) \<in> set ps \<and> b \<noteq> 0} . sum_list (map snd (filter (\<lambda>z. fst z = a) ps)) * f a) + (\<Sum>a \<in> {u. \<exists>b. (u,b) \<in> set ps \<and> (\<forall>b. (u,b) \<in> set ps \<longrightarrow> b = 0)}. sum_list (map snd (filter (\<lambda>z. fst z = a) ps)) * f a)"
          proof -
            have "{u. (\<exists>b. (u, b) \<in> set ps) \<and> (\<forall>b. (u, b) \<in> set ps \<longrightarrow> b = 0)} \<subseteq> fst ` set ps" 
              by force
            hence "finite {u. (\<exists>b. (u, b) \<in> set ps) \<and> (\<forall>b. (u, b) \<in> set ps \<longrightarrow> b = 0)}"
              using finite_surj by blast
            thus ?thesis
              using assms finite_set_pmf_of_list set_pmf_of_list 
              by (subst sum.union_disjoint) fastforce+
          qed
        also have "\<dots> = (\<Sum>a \<in> {u. \<exists>b. (u, b) \<in> set ps \<and> b \<noteq> 0} . sum_list (map snd (filter (\<lambda>z. fst z = a) ps)) * f a)"
          by (fastforce intro!: sum.neutral iffD2[OF sum_list_nonneg_eq_0_iff])
    also have "\<dots> = (\<Sum>a\<in>{u. \<exists>b. (u, b) \<in> set ps \<and> b \<noteq> 0}. sum_list (map snd (filter (\<lambda>z. fst z = a) ps)) * f a)" by blast
  finally have "measure_pmf.expectation (pmf_of_list ps) f = (\<Sum>a\<in>{u. \<exists>b. (u, b) \<in> set ps \<and> b \<noteq> 0}. sum_list (map snd (filter (\<lambda>z. fst z = a) ps)) * f a)"   
    using finite_set_pmf_of_list[OF assms]
    by (subst integral_measure_pmf) (fastforce simp add:  pmf_pmf_of_list set_pmf_of_list assms)+
  thus ?thesis
    using \<open>(\<Sum>(s', p)\<leftarrow>ps. p * f s') = (\<Sum>sp\<leftarrow>ps. snd sp * f (fst sp))\<close> \<open>(\<Sum>a\<in>fst ` set ps. \<Sum>sp\<leftarrow>filter (\<lambda>z. fst z = a) ps. snd sp * f (fst sp)) = (\<Sum>a\<in>fst ` set ps. sum_list (map snd (filter (\<lambda>z. fst z = a) ps)) * f a)\<close> \<open>(\<Sum>a\<in>fst ` set ps. sum_list (map snd (filter (\<lambda>z. fst z = a) ps)) * f a) = (\<Sum>a\<in>{u. \<exists>b. (u, b) \<in> set ps \<and> b \<noteq> 0} \<union> {u. \<exists>b. (u, b) \<in> set ps \<and> (\<forall>b. (u, b) \<in> set ps \<longrightarrow> b = 0)}. sum_list (map snd (filter (\<lambda>z. fst z = a) ps)) * f a)\<close> \<open>(\<Sum>a\<in>{u. \<exists>b. (u, b) \<in> set ps \<and> b \<noteq> 0} \<union> {u. \<exists>b. (u, b) \<in> set ps \<and> (\<forall>b. (u, b) \<in> set ps \<longrightarrow> b = 0)}. sum_list (map snd (filter (\<lambda>z. fst z = a) ps)) * f a) = (\<Sum>a\<in>{u. \<exists>b. (u, b) \<in> set ps \<and> b \<noteq> 0}. sum_list (map snd (filter (\<lambda>z. fst z = a) ps)) * f a) + (\<Sum>a\<in>{u. \<exists>b. (u, b) \<in> set ps \<and> (\<forall>b. (u, b) \<in> set ps \<longrightarrow> b = 0)}. sum_list (map snd (filter (\<lambda>z. fst z = a) ps)) * f a)\<close> \<open>(\<Sum>a\<in>{u. \<exists>b. (u, b) \<in> set ps \<and> b \<noteq> 0}. sum_list (map snd (filter (\<lambda>z. fst z = a) ps)) * f a) + (\<Sum>a\<in>{u. \<exists>b. (u, b) \<in> set ps \<and> (\<forall>b. (u, b) \<in> set ps \<longrightarrow> b = 0)}. sum_list (map snd (filter (\<lambda>z. fst z = a) ps)) * f a) = (\<Sum>a\<in>{u. \<exists>b. (u, b) \<in> set ps \<and> b \<noteq> 0}. sum_list (map snd (filter (\<lambda>z. fst z = a) ps)) * f a)\<close> \<open>(\<Sum>sp\<leftarrow>ps. snd sp * f (fst sp)) = (\<Sum>a\<in>fst ` set ps. \<Sum>sp\<leftarrow>filter (\<lambda>z. fst z = a) ps. snd sp * f (fst sp))\<close> by presburger
qed


locale MDP_Code = MDP_Code_raw +
  V_Map : Array' "v_lookup :: 'tv \<Rightarrow> nat \<Rightarrow> real" v_update v_len v_array v_list v_invar +
  D_Map : Map_by_Ordered d_empty "d_update :: nat \<Rightarrow> nat \<Rightarrow> 'td \<Rightarrow> 'td" d_delete d_lookup d_inorder d_inv
  for v_lookup v_update v_len v_array v_list v_invar
  and d_empty d_update d_delete d_lookup d_inorder d_inv +
fixes
  l :: real
assumes
  zero_le_disc_locale: "0 \<le> l" and
  disc_lt_one_locale: "l < 1"
begin

sublocale V_Map: Array_real v_lookup v_update v_len v_array v_list v_invar
  by unfold_locales

sublocale V_Map: Array_zero v_lookup v_update v_len v_array v_list v_invar
  by unfold_locales
   
sublocale D_Map: Map_by_Ordered_nat_zero d_empty d_update d_delete d_lookup d_inorder d_inv
  by unfold_locales

definition "d_lookup' m x = the (d_lookup m x)"

lemma map_to_fun_lookup: "D_Map.invar f \<Longrightarrow> s \<in> D_Map.keys f \<Longrightarrow> D_Map.map_to_fun f s = d_lookup' f s"
  unfolding D_Map.map_to_fun_def d_lookup'_def
 using D_Map.lookup_None_set_inorder
  by (auto split: option.splits)

sublocale MDP: MDP_reward "(MDP_A)" "(MDP_K)"  "(MDP_r)" l 
  using MDP_A_ne bounded_MDP_r zero_le_disc_locale disc_lt_one_locale
  by unfold_locales auto

sublocale MDP: MDP_nat_disc "(MDP_A)" "(MDP_K)" "(MDP_r)" l "\<lambda>X. LEAST y. y \<in> X"  states
proof -
  have [simp]: "MDP_reward_disc.max_L_ex MDP_A MDP_K MDP_r l s v" for s v
    by (simp add: MDP.MDP_reward_axioms MDP_reward_disc.intro MDP_reward_disc.max_L_ex_def MDP_reward_disc_axioms.intro disc_lt_one_locale finite_is_arg_max has_arg_max_def)
  have "X \<noteq> {} \<Longrightarrow> (LEAST (y::nat). y \<in> X) \<in> X" for X
    using Inf_nat_def Inf_nat_def1 by presburger
  thus "MDP_nat_disc MDP_A MDP_K MDP_r l (\<lambda>X. LEAST y. y \<in> X) states"
  using MDP_K_closed MDP_K_comp_closed MDP_r_zero_notin_states MDP_A_outside disc_lt_one_locale
  by unfold_locales auto
qed

section \<open>Code for @{const MDP.L\<^sub>a}\<close>

definition "L\<^sub>a_code rp v = ( 
    let (r, ps) = rp in r + l * (foldl (\<lambda> acc (s', p). p * v_lookup v s' + acc)) 0 ps)"

lemma L\<^sub>a_code_correct:
  assumes "s < states" "v_len v = states" "v_invar v"  "pmf_of_list (snd rps) = MDP_K (s, a)" 
    "pmf_of_list_wf (snd rps)" "fst ` set (snd rps) \<subseteq> {0..<states}" "fst rps = MDP_r (s, a)"
  shows "L\<^sub>a_code rps v = MDP.L\<^sub>a a (V_Map.map_to_bfun v) s"
proof -
  have "measure_pmf.expectation (MDP_K (s, a)) (v_lookup v) = measure_pmf.expectation (MDP_K (s, a)) (V_Map.map_to_bfun v)"
    using assms MDP.K_closed
    by (force simp: V_Map.map_to_bfun.rep_eq split: option.splits 
        intro!: Bochner_Integration.integral_cong_AE AE_pmfI)
  have "foldl (\<lambda>acc x. f x + acc) x xs = (\<Sum>x\<leftarrow>xs. f x) + x" for f xs and x :: real
    by (induction xs arbitrary: x) (auto simp: algebra_simps)
  hence *: "(\<Sum>x\<leftarrow>xs. f x) = foldl (\<lambda>acc x. f x + acc) (0::real) xs" for f xs
    by (metis add.right_neutral)
  have "foldl (\<lambda>acc (s', p). p * v_lookup v s' + acc) 0 (snd rps) = measure_pmf.expectation (MDP_K (s, a)) (apply_bfun (V_Map.map_to_bfun v))"
    unfolding assms(4)[symmetric] 
    using assms(5,6,7)
    by (auto intro!: foldl_cong simp: pmf_of_list_expectation * V_Map.map_to_bfun.rep_eq assms(2,3))
  thus ?thesis
    unfolding L\<^sub>a_code_def
    using assms
    by (simp add: case_prod_unfold)
qed

lemma L_GS_code_correct':
  assumes "s < states" "v_len v = states" "v_invar v" "a \<in> MDP_A s"
  shows "L\<^sub>a_code (a_lookup' (s_lookup mdp s) a) v = MDP.L\<^sub>a a (V_Map.map_to_bfun v) s"
  using pmf_of_list_wf_mdp assms set_list_pmf_in_states
  by(intro L\<^sub>a_code_correct) 
    (auto simp: fst_sa_lookup'_eq[symmetric] snd_sa_lookup'_eq)

lemma v_lookup_map_to_bfun: "v_invar m \<Longrightarrow> k < v_len m \<Longrightarrow> v_lookup m k = V_Map.map_to_bfun m k"
  unfolding V_Map.map_to_bfun.rep_eq 
  by (force split: option.splits)

lemma map_to_bfun_eq_fun: "v_invar m \<Longrightarrow> apply_bfun (V_Map.map_to_bfun v) = V_Map.map_to_fun v" 
  by (auto simp: V_Map.map_to_bfun.rep_eq V_Map.map_to_fun_def)

lemma map_to_fun_notin: "D_Map.invar d \<Longrightarrow> k \<notin> D_Map.keys d \<Longrightarrow> D_Map.map_to_fun d k = 0"
  by (auto simp: D_Map.map_to_fun_def D_Map.lookup_notin_keys split: option.splits)

section \<open>Folding lists to maps\<close>
(* TODO: convert to function from_list *)

lemma v_lookup_update: "v_invar m \<Longrightarrow> k < v_len m \<Longrightarrow> j < v_len m \<Longrightarrow> v_lookup (v_update j x m) k  = (if j = k then x else v_lookup m k)" 
  by (auto simp add: V_Map.invar_update V_Map.len_array V_Map.lookup V_Map.update)

lemma V_invar_fold: "v_invar m \<Longrightarrow> set xs \<subseteq> {0..<v_len m} \<Longrightarrow> v_invar (fold (\<lambda>s v. v_update s (f s v) v) xs m)"
  by (induction xs arbitrary: m) (auto simp add: V_Map.invar_update V_Map.len_array V_Map.update)


lemma V_len_fold: "v_invar m \<Longrightarrow> set xs \<subseteq> {0..<v_len m} \<Longrightarrow> v_len (fold (\<lambda>s v. v_update s (f s v) v) xs m) = v_len m"
  by (induction xs arbitrary: m) (auto simp add: V_Map.invar_update V_Map.len_array V_Map.update)

lemma v_len_update: "v_invar m \<Longrightarrow> j < v_len m \<Longrightarrow> v_len (v_update j x m) = v_len m"
  by (simp add: V_Map.invar_update V_Map.len_array V_Map.update)

lemma v_lookup_fold: "v_invar m \<Longrightarrow> n \<le> v_len m \<Longrightarrow> k < n \<Longrightarrow> v_lookup (fold (\<lambda>s v. v_update s (f s) v) [0..<n] m) k = (f k)"
  using V_invar_fold
  by (induction n arbitrary: m k) (auto intro!: V_invar_fold simp: v_lookup_update V_len_fold)

lemma keys_fold_map: "D_Map.invar m \<Longrightarrow> D_Map.keys (fold (\<lambda>s. d_update s (f s)) xs m) = D_Map.keys m \<union> set xs"
  using D_Map.map_specs
  by (induction xs arbitrary: m) auto
                
lemma invar_fold_update: "D_Map.invar m \<Longrightarrow> D_Map.invar (fold (\<lambda>s. d_update s (f s)) xs m)"
    using D_Map.map_specs by (induction xs arbitrary: m) auto

lemma d_lookup_fold: "k < n \<Longrightarrow> D_Map.invar m \<Longrightarrow> d_lookup (fold (\<lambda>s v. d_update s (f s) v) [0..<n] m) k = Some (f k)"
  using D_Map.map_update invar_fold_update by (induction n) auto

section \<open>Code for @{const MDP.\<L>\<^sub>b}\<close>

definition "\<L>_GS_code acts v = 
  (MAX (a, rs) \<in> A_Map.entries acts. L\<^sub>a_code rs v)"


lemma \<L>_GS_code_correct:
  assumes "s < states"  "v_invar v" "v_len v = states"
  shows "\<L>_GS_code (s_lookup mdp s) v = (\<Squnion>a \<in> MDP_A s. MDP.L\<^sub>a a (V_Map.map_to_bfun v) s)"
  unfolding \<L>_GS_code_def
proof (subst cSup_eq_Max[symmetric])
  show "finite ((\<lambda>(a, rs). L\<^sub>a_code rs v) ` A_Map.entries (s_lookup mdp s))"
    using A_Map.finite_entries by blast
  show "(\<lambda>(a, rs). L\<^sub>a_code rs v) ` A_Map.entries (s_lookup mdp s) \<noteq> {}"
    using ne_s_lookup assms A_Map.is_empty_iff_entries_empty by blast
  
  
  have "L\<^sub>a_code (r,s') v = MDP.L\<^sub>a a (V_Map.map_to_bfun v) s" if "(a, r,s') \<in> A_Map.entries (s_lookup mdp s)" for a r s'
  proof -
    have "r = MDP_r (s, a)"
      by (metis assms(1) entries_A_eq_r that)
    moreover have "fst ` set s' \<subseteq> MDP.state_space"
      using K_closed_locale' S_Map.lookup_in_list assms(1) s_invar s_len that by fastforce
    moreover have "s' = (snd (a_lookup' (s_lookup mdp s) a))"
      using A_Map.inorder_lookup_Some a_lookup'_def assms(1) invar_s_lookup that by auto
    ultimately show ?thesis 
        using assms that a_inorderD pmf_of_list_wf_mdp
        by (intro L\<^sub>a_code_correct) auto
qed
  thus "(\<Squnion>(a, rs)\<in>A_Map.entries (s_lookup mdp s). L\<^sub>a_code rs v) = (\<Squnion>a\<in>MDP_A s. MDP.L\<^sub>a a (V_Map.map_to_bfun v) s)"
    using invar_s_lookup
    by (auto simp: MDP_A_def assms SUP_image A_Map.keys_eq_fst_entries intro!: SUP_cong)
qed


definition "\<L>_code v = 
  V_Map.arr_tabulate (\<lambda>s. \<L>_GS_code (s_lookup mdp s) v) states"


lemma \<L>_code_lookup:
  assumes "s < states" "v_len v = states" "v_invar v"
  shows "v_lookup (\<L>_code v) s = (\<L>_GS_code (s_lookup mdp s) v)"
  using assms unfolding \<L>_code_def by auto

lemma keys_\<L>_code[simp]: "v_invar v \<Longrightarrow> v_len v = states \<Longrightarrow> v_len (\<L>_code v) = v_len v"
  unfolding \<L>_code_def by auto


lemma \<L>_code_correct:
  assumes "s < states" "v_len v = states" "v_invar v"
  shows "v_lookup (\<L>_code v) s = MDP.\<L>\<^sub>b (V_Map.map_to_bfun v) s"
  unfolding \<L>_code_lookup[OF assms] MDP.\<L>\<^sub>b_eq_L\<^sub>a_max'
  by (auto intro: cSup_eq_Max simp: assms \<L>_GS_code_correct)

lemma invar_\<L>_code: "v_invar v \<Longrightarrow> v_invar (\<L>_code v)"
  using V_invar_fold unfolding \<L>_code_def
  using V_Map.arr_tabulate_def V_Map.invar_array by presburger


lemma \<L>_code_correct':
  assumes "v_len v = states" "v_invar v"
  shows "V_Map.map_to_bfun (\<L>_code v) = MDP.\<L>\<^sub>b (V_Map.map_to_bfun v)"
  using MDP.\<L>\<^sub>b_zero  assms
proof (intro bfun_eqI)
  fix x
  show "apply_bfun (V_Map.map_to_bfun (\<L>_code v)) x = apply_bfun (MDP.\<L>\<^sub>b (V_Map.map_to_bfun v)) x"
  proof (cases "x < states")
    case True
    then show ?thesis
      using assms keys_\<L>_code \<L>_code_correct invar_\<L>_code v_lookup_map_to_bfun by force
  next
    case False
    then show ?thesis
      using assms keys_\<L>_code MDP.\<L>\<^sub>b_zero
      by (fastforce simp: V_Map.map_to_bfun.rep_eq  dest: split: option.splits)+
  qed
qed

section \<open>Code to check condition\<close>

definition "check_dist v v' eps = (
  let m = eps * (1 - l) / (2 * l) in
    (\<forall>s < states. abs (v_lookup v s - v_lookup v' s) < m))"

lemma check_dist_correct:
  assumes "v_invar v" "v_invar v'" "v_len v = states" "v_len v' = states" "eps > 0" "l \<noteq> 0"
  shows "check_dist v v' eps \<longleftrightarrow> dist (V_Map.map_to_bfun v) (V_Map.map_to_bfun v') < eps * (1 - l) / (2 * l)"
proof -
  have dist_zero_ge: "dist (apply_bfun (V_Map.map_to_bfun v) x) (apply_bfun (V_Map.map_to_bfun v') x) = 0" if "x \<ge> states" for x
    using assms that 
    by (auto simp: V_Map.map_to_bfun.rep_eq split: option.splits)
 have univ: "UNIV = {0..<states} \<union> {states..}" by auto
 have fin: "finite (range (\<lambda>x. dist (apply_bfun (V_Map.map_to_bfun v) x) (apply_bfun (V_Map.map_to_bfun v') x)))"
    by (auto simp: dist_zero_ge univ Set.image_Un Set.image_constant[of states])
  have zero_less_eps: "0 < eps * (1 - l) / (2 * l)"
    using MDP.zero_le_disc assms MDP.disc_lt_one
    by (auto intro!: mult_imp_less_div_pos simp: less_le)
  show ?thesis
  proof
    assume h: "check_dist v v' eps" 
    show "dist (V_Map.map_to_bfun v) (V_Map.map_to_bfun v') < eps * (1 - l) / (2 * l)"
      unfolding dist_bfun.rep_eq
    proof (rule finite_imp_Sup_less[OF fin])
      show "0 \<in> range (\<lambda>x. dist (apply_bfun (V_Map.map_to_bfun v) x) (apply_bfun (V_Map.map_to_bfun v') x))"
        using dist_zero_ge by fastforce
      have "dist (apply_bfun (V_Map.map_to_bfun v) x) (apply_bfun (V_Map.map_to_bfun v') x) < eps * (1 - l) / (2 * l)" if "x < states" for x
        using assms h that
        unfolding check_dist_def V_Map.map_to_bfun.rep_eq  dist_real_def
        by (auto  split: option.splits)
      thus "x \<in> range (\<lambda>x. dist (apply_bfun (V_Map.map_to_bfun v) x) (apply_bfun (V_Map.map_to_bfun v') x)) \<Longrightarrow> x < eps * (1 - l) / (2 * l)" for x
        using zero_less_eps dist_zero_ge imageE not_less 
        by (metis (no_types, lifting))
    qed
  next
  show "dist (V_Map.map_to_bfun v) (V_Map.map_to_bfun v') < eps * (1 - l) / (2 * l) \<Longrightarrow> check_dist v v' eps"
    using assms fin
    by (auto simp: check_dist_def dist_bfun.rep_eq finite_Sup_less_iff dist_real_def v_lookup_map_to_bfun)
qed
qed


section \<open>Find policy\<close>
definition "find_policy_state_code_aux v s = 
  (least_arg_max_max_ne (\<lambda>(_, rsuccs). 
    L\<^sub>a_code rsuccs v) ((a_inorder (s_lookup mdp s))))"

definition "find_policy_state_code_aux' v s = (
  case find_policy_state_code_aux v s of ((a, _, _), v) \<Rightarrow> (a, v))"


lemma find_policy_state_code_aux_eq:
  assumes "s < states"
  shows "find_policy_state_code_aux' v s = (least_arg_max_max_ne (\<lambda>a.
   L\<^sub>a_code (a_lookup' (s_lookup mdp s) a) v) ((map fst (a_inorder (s_lookup mdp s)))))"
  unfolding find_policy_state_code_aux'_def  find_policy_state_code_aux_def
  using assms ne_s_lookup invar_s_lookup A_Map.inorder_lookup_Some
  by (subst least_arg_max_max_ne_app'[symmetric]) 
    (auto simp: A_Map.entries_def a_lookup'_def case_prod_unfold A_Map.is_empty_def)

lemma find_policy_state_code_aux'_eq':
  assumes "s < states" "v_len v = states" "v_invar v"
  shows "find_policy_state_code_aux' v s = 
  (least_arg_max (\<lambda>a. MDP.L\<^sub>a a (V_Map.map_to_bfun v) s) (\<lambda>a. a \<in> MDP_A s), Max ((\<lambda>a. MDP.L\<^sub>a a (V_Map.map_to_bfun v) s) ` (MDP_A s)))"
proof -
  have "find_policy_state_code_aux' v s = least_arg_max_max_ne (\<lambda>a. L\<^sub>a_code (a_lookup' (s_lookup mdp s) a) v) (map fst (a_inorder (s_lookup mdp s)))"
    using find_policy_state_code_aux_eq assms by auto
  also have \<open>\<dots> = (least_arg_max (\<lambda>a. L\<^sub>a_code (a_lookup' (s_lookup mdp s) a) v) (List.member (map fst (a_inorder (s_lookup mdp s)))),
     MAX a\<in>set (map fst (a_inorder (s_lookup mdp s))). L\<^sub>a_code (a_lookup' (s_lookup mdp s) a) v)\<close>
    using A_Map.is_empty_def assms(1) ne_s_lookup A_Map.invar_def A_inv_locale S_Map.lookup_in_list s_invar s_len 
    by (auto simp: fold_max_eq_arg_max')
  also have \<open>\<dots> = (least_arg_max (\<lambda>a. MDP.L\<^sub>a a (V_Map.map_to_bfun v) s) (List.member (map fst (a_inorder (s_lookup mdp s)))),
     MAX a\<in>set (map fst (a_inorder (s_lookup mdp s))). MDP.L\<^sub>a a (V_Map.map_to_bfun v) s)\<close>
    using assms a_inorderD(1) A_Map.keys_def  MDP_A_def 
    by (auto intro!: least_arg_max_cong simp: L_GS_code_correct' in_set_member[symmetric])
  also have \<open>\<dots> = (least_arg_max (\<lambda>a. MDP.L\<^sub>a a (V_Map.map_to_bfun v) s) (\<lambda>a. a \<in> MDP_A s),
     MAX a\<in>MDP_A s. MDP.L\<^sub>a a (V_Map.map_to_bfun v) s)\<close>
  proof -
    have *: "a \<in> fst ` set (a_inorder (s_lookup mdp s))  \<longleftrightarrow> List.member (map fst ((a_inorder (s_lookup mdp s)))) a" for a
      by (auto simp: List.member_def)
    show ?thesis
    using assms L\<^sub>a_code_correct  A_Map.keys_def 
    by (auto intro!: least_arg_max_cong  simp: * MDP_A_def)
qed
  finally show ?thesis.
qed

definition "vi_find_policy_code (v::'tv) = D_Map.from_list' (\<lambda>s. fst (find_policy_state_code_aux' v s)) [0..<states]"

lemma d_invar_vi_find_policy_code: "D_Map.invar (vi_find_policy_code v)"
  using D_Map.from_list_invar vi_find_policy_code_def by simp

lemma d_keys_vi_find_policy_code: "D_Map.keys (vi_find_policy_code v) = {0..<states}"
  using D_Map.from_list_keys vi_find_policy_code_def by simp

lemma vi_find_policy_code_notin: 
  assumes "s \<ge> states" shows "d_lookup (vi_find_policy_code v) s = None"
  using D_Map.lookup_notin_keys assms d_invar_vi_find_policy_code d_keys_vi_find_policy_code by force

lemma vi_find_policy_code_in: 
  assumes "s < states" shows "\<exists>x. d_lookup (vi_find_policy_code v) s = Some x"
  by (simp add: D_Map.lookup_in_keys assms d_invar_vi_find_policy_code d_keys_vi_find_policy_code)
 
lemma vi_find_policy_code_ge: "s \<ge> states \<Longrightarrow> D_Map.map_to_fun (vi_find_policy_code v) s = 0"
  using vi_find_policy_code_notin vi_find_policy_code_def 
  by (auto simp: D_Map.map_to_fun_def)


lemma vi_find_policy_code_correct:
  assumes "v_len v = states" "v_invar v" "s < states"
  shows "D_Map.map_to_fun ((vi_find_policy_code v)) s = least_arg_max (\<lambda>a. MDP.L\<^sub>a a (V_Map.map_to_bfun v) s) (\<lambda>a. a \<in> MDP_A s)"
  using assms
  by (simp add: find_policy_state_code_aux'_eq'  vi_find_policy_code_def D_Map.map_to_fun_def)


lemma vi_find_policy_correct: 
  assumes "v_len v = states" "v_invar v"
  shows "D_Map.map_to_fun (vi_find_policy_code v) = (MDP.find_policy' (V_Map.map_to_bfun v))"
proof -
  have "D_Map.map_to_fun (vi_find_policy_code v) s = (MDP.find_policy' (V_Map.map_to_bfun v)) s" if "s \<ge> states" for s
    using vi_find_policy_code_ge that
    by (auto simp:  MDP.find_policy'_def MDP_A_def  MDP.is_opt_act_def intro!: Least_equality)
  moreover have "D_Map.map_to_fun (vi_find_policy_code v) s = (MDP.find_policy' (V_Map.map_to_bfun v)) s" if "s < states" for s
    using that assms
    by (auto simp: MDP.find_policy'_def vi_find_policy_code_correct least_arg_max_def MDP.is_opt_act_def)
  ultimately show ?thesis
    using not_le by blast
qed

definition "v0 = V_Map.arr_tabulate (\<lambda>_. 0) states"

lemma v0_correct: "v_invar v0" "v_len v0 = states"
  unfolding v0_def by auto
 
definition "v_map_from_list xs = v_array xs" 

end

text \<open>
hack:
@{const pmf_of_list_wf} is polymorphic, so equality to @{term "1"} is checked for the sum of all probabilities.
This fails for floats, so we reimplement the check monomorphically and change equality on floats to
@{term "a = b \<longleftrightarrow> dist a b < 1.0/10^8"}.
\<close>
lemmas pmf_of_list_wf_code[code del]

definition
  "pmf_of_list_wf' xs \<longleftrightarrow> list_all (\<lambda>z. snd z \<ge> 0) xs \<and> sum_list (map snd xs) = (1 :: real)"

lemma pmf_of_list_code [code abstract]:
  "mapping_of_pmf (pmf_of_list xs) = (
     if pmf_of_list_wf' xs then
       let xs' = filter (\<lambda>z. snd z*(10^8) \<noteq> 0) xs
       in  Mapping.tabulate (remdups (map fst xs')) 
             (\<lambda>x. sum_list (map snd (filter (\<lambda>z. fst z = x) xs')))
     else
       Code.abort (STR ''Invalid list for pmf_of_list'') (\<lambda>_. mapping_of_pmf (pmf_of_list xs)))"
  using mapping_of_pmf_pmf_of_list'[of xs] pmf_of_list_wfI
  by (auto simp add: pmf_of_list_wf'_def list_all_def)


code_printing
 constant IArray.tabulate \<rightharpoonup> (SML) "case _ of (n, f) => Vector.tabulate (IntInf.toInt n, fn i => f ((IntInf.fromInt i)))"
| constant IArray.sub' \<rightharpoonup> (SML) "case _ of (arr, i) => Vector.sub (arr, IntInf.toInt i)"
| constant IArray.length' \<rightharpoonup> (SML) "IntInf.fromInt (Vector.length _)"

definition "nat_map_from_list (xs :: (nat \<times> _) list) = foldr (\<lambda>(k,v) m. RBT_Map.update k v m) xs RBT_Set.empty "
definition "nat_pmf_of_list (xs :: (nat \<times> _) list) = pmf_of_list xs"

definition "assoc_list_to_MDP d xs = 
    to_valid_MDP (MDP d (length xs) (IArray (map (\<lambda>as. foldr (\<lambda>(a,(r,p)) m. RBT_Map.update a (r, p) m) as RBT_Set.empty) xs)))"

lemma starray_of_list_tabulate [code_unfold]: "starray_of_list (map f [0..<n]) = starray_tabulate n f"
  by (simp add: starray_eq_iff tabulate_def)

end
