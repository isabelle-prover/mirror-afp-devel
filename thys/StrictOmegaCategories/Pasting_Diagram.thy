theory Pasting_Diagram
imports Strict_Omega_Category

begin

section \<open>The category of pasting diagrams\<close>

text \<open>We define the strict $\omega$-category of pasting diagrams, 'pd'. We encode its cells as rooted
 trees. First we develop some basic theory of trees.\<close>

subsection \<open>Rooted trees\<close>

datatype tree = Node (subtrees: "tree list") \<comment> \<open>\cite[p. 268]{Leinster2004}\<close>

abbreviation Leaf :: tree where
"Leaf \<equiv> Node []"

fun subtree :: "tree \<Rightarrow> nat list \<Rightarrow> tree" ("_ !t _" [59,60]59) where
"t !t [] = t" |
"t !t (i#xs) = subtrees (t !t xs) ! i"

value "Leaf !t []" (* Leaf *)
value "Node [Node [Leaf, Leaf, Leaf], Leaf, Node [Leaf]] !t [0]"    (* Node [Leaf, Leaf, Leaf] *)
value "Node [Node [Leaf, Leaf, Leaf], Leaf, Node [Leaf]] !t [2,0]"  (* Leaf *)
value "Node [Node [Leaf, Leaf, Leaf], Leaf, Node [Leaf]] !t [1]"    (* Leaf *)
value "Node [Node [Leaf, Leaf, Leaf], Leaf, Node [Leaf]] !t [0,2]"  (* Leaf *)

lemma subtrees_Leaf: "(t = Leaf) = (subtrees t = [])"
  by (metis tree.collapse tree.sel)

fun is_subtree_index :: "tree \<Rightarrow> nat list \<Rightarrow>  bool" where
"is_subtree_index t [] = True" |
"is_subtree_index t (i#xs) = (is_subtree_index t xs \<and> i < length (subtrees (t !t xs)))"

lemma subtree_append: "ts ! i !t xs = Node ts !t xs @ [i]"
  by (induction xs, auto)

lemma is_subtree_index_append [iff]: "is_subtree_index (Node ts) (xs @ [i]) =
  (i < length ts \<and> is_subtree_index (ts!i) xs)"
proof
  show "is_subtree_index (Node ts) (xs @ [i]) \<Longrightarrow> i < length ts \<and> is_subtree_index (ts ! i) xs"
  by (induction xs, auto simp: subtree_append)
next
  show "i < length ts \<and> is_subtree_index (ts ! i) xs \<Longrightarrow> is_subtree_index (Node ts) (xs @ [i])"
  by (induction xs, auto simp: subtree_append)
qed

lemma is_subtree_index_append' [iff]: "is_subtree_index t (xs @ [i]) =
  (is_subtree_index t [i] \<and> is_subtree_index (t !t [i]) xs)"
  by (metis is_subtree_index_append is_subtree_index.simps subtree.simps tree.collapse)

lemma max_set_upt [simp]: "Max {0..<Suc n} = n"
  by (simp add: Max_eq_iff)

lemma length_subtrees_eq_Max: assumes "is_subtree_index t xs" "subtrees (t !t xs) \<noteq> []"
  shows "length (subtrees (t !t xs)) = Suc (Max {i. is_subtree_index t (i # xs)})"
proof -
  have "\<And>i. is_subtree_index t (i # xs) = (i < length (subtrees (t !t xs)))" using assms(1) by simp
  hence "{i. is_subtree_index t (i # xs)} = {0..<length (subtrees (t !t xs))}" by fastforce
  moreover have "length (subtrees (t !t xs)) > 0" using assms(2) by simp
  ultimately show "length (subtrees (t !t xs)) = Suc (Max {i. is_subtree_index t (i # xs)})"
    by (metis max_set_upt gr0_implies_Suc)
qed

lemma tree_eq_iff_subtree_eq: "(t = u) = (length (subtrees t) = length (subtrees u) \<and>
  (\<forall>i < length (subtrees t). t !t [i] = u !t [i]))"
  by (cases t, cases u, auto simp add: list_eq_iff_nth_eq)

text \<open>We define the height of a rooted tree. A tree with only one node has height 0. The trees of 
height at most n encode the n-cells in 'pd'.\<close>
fun height :: "tree \<Rightarrow> nat" where
"height Leaf = 0" |
"height (Node ts) = Suc (fold (max \<circ> height) ts 0)"

value "height Leaf"                              (* 0 *)
value "height (Node [Leaf, Leaf])"               (* 1 *)
value "height (Node [Node [Leaf, Leaf], Leaf])"  (* 2 *)
value "height (Node [Node [Leaf, Node [Leaf]]])" (* 3 *)

lemma height_Node [simp]: "ts \<noteq> [] \<Longrightarrow> height (Node ts) = Suc (fold (max \<circ> height) ts 0)"
  by (metis height.simps(2) neq_Nil_conv)

lemma fold_eq_Max [simp]: "ts \<noteq> [] \<Longrightarrow> fold (max \<circ> height) ts 0 = Max (set (map height ts))"
  using Max.set_eq_fold fold_map list.exhaust
  by (metis (no_types, lifting) fold_simps(2) map_is_Nil_conv max_nat.right_neutral)

lemma height_Node_Max: "ts \<noteq> [] \<Longrightarrow> height (Node ts) = Suc (Max (set (map height ts)))"
  by simp

lemma height_Node_pos : "ts \<noteq> [] \<Longrightarrow> 0 < height (Node ts)"
proof (induction "Node ts" rule: height.induct)
  case 1
  then show ?case by blast
next
  case (2 t ts')
  then show ?case by fastforce
qed

lemma height_exists:
  assumes "height (Node ts) = Suc n"
  shows "\<exists>t. t \<in> set ts \<and> height t = n"
proof (cases "ts = []")
  case True
  then show ?thesis using assms by simp
next
  case False
  hence "n = Max (set (map height ts))" using assms height_Node_Max by force
  hence "n \<in> set (map height ts)" using Max_in `ts \<noteq> []` by auto
  then show ?thesis by auto
qed

lemma height_lt: assumes "t \<in> set ts" shows "height t < height (Node ts)"
proof -
  from assms have nemp: "ts \<noteq> []" by fastforce
  have "height t \<le> Max (set (map height ts))" using assms by fastforce
  also have "\<dots> = fold (max \<circ> height) ts 0" using nemp fold_eq_Max by simp
  finally show ?thesis using nemp by simp
qed

lemma height_le_imp_le_Suc:
  assumes "\<forall>t \<in> set ts. height t \<le> n"
  shows "height (Node ts) \<le> Suc n"
proof (cases "ts = []")
  case True
  then show ?thesis by simp
next
  case False
  hence "height (Node ts) = Suc (Max (set (map height ts)))" using height_Node_Max by blast
  also have "\<dots> \<le> Suc (Max (height ` set ts))" using set_map by fastforce
  finally show ?thesis using `ts \<noteq> []` assms by simp
qed

lemma height_zero [simp]: "height t = 0 \<Longrightarrow> t = Leaf"
  by (metis height.cases height_Node_pos less_nat_zero_code)

lemma is_subtree_index_length_le: "is_subtree_index t xs \<Longrightarrow> length xs \<le> height t"
proof (induction xs arbitrary: t rule: rev_induct)
  case Nil
  then show ?case by force
next
  case (snoc i xs)
  hence hi: "i < length (subtrees t)" by (metis is_subtree_index_append tree.exhaust_sel)
  hence "length xs \<le> height (subtrees t ! i)"
    by (metis snoc is_subtree_index_append tree.exhaust_sel)
  moreover have "subtrees t ! i \<in> set (subtrees t)" using hi by simp
  ultimately show ?case using height_lt by fastforce
qed

lemma height_subtree: "is_subtree_index t xs \<Longrightarrow> height (t !t xs) \<le> height t - length xs"
proof (induction xs arbitrary: t rule: rev_induct)
  case Nil
  then show ?case by simp
next
  case (snoc i xs)
  hence "is_subtree_index (t !t [i]) xs" using is_subtree_index_append' by fastforce
  hence "height (t !t [i] !t xs) \<le> height (t !t [i]) - length xs" using snoc.IH by blast
  moreover have "height (t !t [i]) < height t"  
    by (metis height_lt is_subtree_index.simps(2) is_subtree_index_append' nth_mem snoc.prems
        subtree.simps tree.collapse)
  moreover have "t !t [i] !t xs = t !t xs @ [i]" using subtree_append by simp
  ultimately show ?case by auto
qed

lemma height_induct: "(\<And>t. \<forall>u. height u < height t \<longrightarrow> P u \<Longrightarrow> P t) \<Longrightarrow> P t"
  by (metis Nat.measure_induct)

lemma subtree_index_induct [case_names Index Step]:
  assumes 
    "is_subtree_index t xs"
    "\<And>xs. \<lbrakk>is_subtree_index t xs; \<forall>i < length (subtrees (t !t xs)). P (i#xs)\<rbrakk> \<Longrightarrow> P xs"
  shows "P xs"
proof -
  have hl: "length xs \<le> height t" by (simp add: assms(1) is_subtree_index_length_le)
  then show "P xs" using assms
  proof (induction "height t - length xs" arbitrary: xs)
    case 0
    hence "height (t !t xs) = 0" using height_subtree by fastforce
    hence "\<forall>i < length (subtrees (t !t xs)). P (i # xs)"
      by (metis height_zero length_0_conv less_nat_zero_code tree.sel)
    then show ?case using "0.prems" by blast
  next
    case (Suc n)
    have "\<forall>i < length (subtrees (t !t xs)). P (i # xs)"
    proof (safe)
      fix i assume "i < length (subtrees (t !t xs))"
      hence "is_subtree_index t (i # xs)" using Suc(4) by simp
      moreover hence "length (i # xs) \<le> height t" using is_subtree_index_length_le by blast
      moreover have "n = height t - length (i # xs)" using Suc(2) by simp
      ultimately show "P (i # xs)" using Suc(1) Suc(5) by blast
    qed
    then show ?case using Suc.prems by blast
  qed
qed

text \<open>The function \<open>trim\<close> keeps the first n layers of a tree and removes the remaining ones.\<close>
fun trim :: "nat \<Rightarrow> tree \<Rightarrow> tree" where
"trim 0 t = Leaf" |
"trim (Suc n) (Node ts) = Node (map (trim n) ts)" 

lemma trim_Leaf [simp]: "trim n Leaf = Leaf"
  by (metis list.simps(8) trim.elims trim.simps(2))

lemma height_trim_le: "height (trim n t) \<le> n"
proof (induction n t rule: trim.induct)
  case (1 t)
  then show ?case by auto
next
  case (2 n ts)
  hence "\<forall>t' \<in> set (map (trim n) ts). height t' \<le> n" by auto
  then show ?case using height_le_imp_le_Suc trim.simps(2) by presburger
qed

lemma trim_const: "height t \<le> n \<Longrightarrow> trim n t = t"
proof (induction n t rule: trim.induct)
  case (1 t)
  then show ?case using height_zero trim_Leaf by blast
next
  case (2 n ts)
  hence "\<And>t. t \<in> set ts \<Longrightarrow> trim n t = t" using height_lt by fastforce
  hence "map (trim n) ts = ts" using map_idI by blast
  then show ?case by fastforce
qed

lemma height_trim_le': "n \<le> height t \<Longrightarrow> height (trim n t) = n"
proof (induction n t rule: trim.induct)
  case (1 t)
  then show ?case by fastforce
next
  case (2 n ts)
  hence "\<exists>m. height (Node ts) = Suc m" by presburger
  then obtain m where hm: "height (Node ts) = Suc m" by presburger
  then obtain t where ht: "t \<in> set ts \<and> height t = m" using height_exists by meson
  have "n \<le> m" using 2 hm by fastforce
  hence hn: "height (trim n t) = n" using 2 ht by blast
  have "trim n t \<in> set (subtrees (trim (Suc n) (Node ts)))" using ht by simp
  then show ?case using hn height_lt by (metis height_trim_le leD le_SucE tree.collapse)
qed

lemma height_trim: "height (trim n t) = (if n \<le> height t then n else height t)"
  using height_trim_le' trim_const by auto

value "trim 1 Leaf"
value "trim 1 (Node [Leaf, Leaf])"
value "trim 2 (Node [Node [Leaf, Leaf], Leaf])"
value "trim 1 (Node [Node [Leaf, Node [Leaf]], Node [Leaf]])"

lemma trim_trim' [simp]: "trim n \<circ> trim n = trim n"
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then show ?case apply (simp add: fun_eq_iff) proof
    fix t
    show "trim (Suc n) (trim (Suc n) t) = trim (Suc n) t"
      using Suc by (metis list.map_comp tree.exhaust trim.simps(2))
  qed
qed

lemma trim_trim_Suc [simp]: "trim n \<circ> trim (Suc n) = trim n"
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then show ?case apply (simp add: fun_eq_iff) proof
    fix t
    show "trim (Suc n) (trim (Suc (Suc n)) t) = trim (Suc n) t"
      using Suc by (metis list.map_comp tree.exhaust trim.simps(2))
  qed
qed

lemma trim_trim [simp]: "n \<le> m \<Longrightarrow> trim n \<circ> trim m = trim n"
proof (induction m arbitrary: n)
  case 0
  then show ?case by force
next
  case (Suc m)
  then show ?case proof (cases "n = Suc m")
    case True
    then show ?thesis by auto
  next
    case False
    hence "n \<le> m" using Suc.prems by auto
    hence ih: "trim n = trim n \<circ> trim m" using Suc by presburger
    hence "trim n \<circ> trim (Suc m) = (trim n \<circ> trim m) \<circ> trim (Suc m)" by simp
    also have "\<dots> = trim n \<circ> trim m" by (metis fun.map_comp trim_trim_Suc)
    finally show ?thesis using ih by auto
  qed
qed

lemma trim_eq_imp_trim_eq [simp]: "\<lbrakk>n \<le> m; trim m t = trim m u\<rbrakk> \<Longrightarrow> trim n t = trim n u"
  by (metis trim_trim comp_apply)

lemma trim_1_eq: assumes "trim 1 (Node ts) = trim 1 (Node us)" shows "length ts = length us"
proof -
  have "\<And>vs. trim 1 (Node vs) = Node (map (\<lambda>x. Leaf) vs)" by force
  then show ?thesis using assms map_eq_imp_length_eq by auto
qed

lemma length_subtrees_trim_Suc: "length (subtrees (trim (Suc n) t)) = length (subtrees t)"
  by (induction t, simp)

lemma trim_eq_Leaf: "trim n t = Leaf \<Longrightarrow> n = 0 \<or> t = Leaf"
  by (induction n t rule: trim.induct, simp_all)

lemma map_eq_imp_pairs_eq: "map f xs = map g ys \<Longrightarrow> (\<And>x y. (x, y) \<in> set (zip xs ys) \<Longrightarrow> f x = g y)"
  by (metis fst_eqD in_set_zip nth_map snd_eqD)

lemma trim_eq_subtree_eq:
  assumes "trim (Suc n) (Node ts) = trim (Suc n) (Node us)"
  shows "\<And>t u. (t, u) \<in> set (zip ts us) \<Longrightarrow> trim n t = trim n u"
proof -
  fix t u assume "(t, u) \<in> set (zip ts us)"
  moreover from assms have "map (trim n) ts = map (trim n) us" by fastforce
  ultimately show "trim n t = trim n u" using map_eq_imp_pairs_eq by fast
qed

lemma pairs_eq_imp_map_eq:
  assumes "length xs = length ys" "\<forall>(x, y) \<in> set (zip xs ys). f x = g y"
  shows "map f xs = map g ys"
proof -
  have "\<And>x y. (x, y) \<in> set (zip (map f xs) (map g ys)) \<Longrightarrow> x = y" proof -
    fix x y assume h: "(x, y) \<in> set (zip (map f xs) (map g ys))"
    hence "\<exists>n. (map f xs)!n = x \<and> (map g ys)!n = y \<and> n < length xs \<and> n < length ys"
      by (metis in_set_zip fst_conv length_map snd_conv)
    then obtain n where hn: "(map f xs)!n = x" "(map g ys)!n = y" "n < length xs" "n < length ys"
      by blast
    hence "(xs!n, ys!n) \<in> set (zip xs ys)" using in_set_zip by fastforce
    with hn assms(2) show "x = y" by auto
  qed
  hence "\<forall>(x, y) \<in> set (zip (map f xs) (map g ys)). x = y" by force
  with assms(1) list_eq_iff_zip_eq show "map f xs = map g ys" by fastforce
qed

lemma map_eq_iff_pairs_eq: "(map f xs = map g ys) = 
  (length xs = length ys \<and> (\<forall>(x, y) \<in> set (zip xs ys). f x = g y))"
proof -
  have "map f xs = map g ys \<Longrightarrow> \<forall>(x, y) \<in> set (zip xs ys). f x = g y" using map_eq_imp_pairs_eq
    by fast
  thus ?thesis by (metis pairs_eq_imp_map_eq length_map)
qed

lemma subtree_eq_trim_eq:
  assumes "length ts = length us" "\<forall>(t, u) \<in> set (zip ts us). trim n t = trim n u"
  shows "trim (Suc n) (Node ts) = trim (Suc n) (Node us)"
  by (auto simp add: assms map_eq_iff_pairs_eq)

lemma subtree_trim_1: "is_subtree_index t [i] \<Longrightarrow> trim (Suc n) t !t [i] = trim n (t !t [i])"
  by (smt (verit) Suc_inject is_subtree_index.simps(2) list.distinct(1) nat.distinct(1) nth_map
      subtree.elims subtree.simps(2) tree.sel trim.elims)

lemma is_subtree_index_trim:
  "is_subtree_index (trim n t) xs = (is_subtree_index t xs \<and> length xs \<le> n)"
proof (induction n t arbitrary: xs rule: trim.induct)
  case (1 t)
  then show ?case using is_subtree_index_length_le by fastforce
next
  case (2 n ts)
  then show ?case proof (induction xs rule: rev_induct)
    case Nil
    then show ?case by auto
  next
    case (snoc x xs)
    then show ?case by fastforce
  qed
qed

lemma subtree_trim: "\<lbrakk>is_subtree_index t xs; length xs \<le> n\<rbrakk> \<Longrightarrow>
  trim n t !t xs = trim (n - length xs) (t !t xs)"
proof (induction n t arbitrary: xs rule: trim.induct)
  case (1 t)
  then show ?case by simp
next
  case (2 n ts)
  then show ?case proof (cases "length xs = Suc n")
    case True
    hence "is_subtree_index (trim (Suc n) (Node ts)) xs" using is_subtree_index_trim 2 by blast
    hence "height (trim (Suc n) (Node ts) !t xs) \<le> 0"
      by (metis height_subtree height_trim_le True diff_is_0_eq')
    then show ?thesis using True height_zero by fastforce
  next
    case False
    then show ?thesis proof (cases xs rule: rev_cases)
      case Nil
      then show ?thesis by simp
    next
      case (snoc ys i)
      have hi: "ts ! i \<in> set ts" "is_subtree_index (ts ! i) ys" using snoc 2(2) by simp_all
      have hl: "length ys \<le> n" using snoc 2(3) by simp
      have "Node (map (trim n) ts) !t ys @ [i] = trim n (ts ! i) !t ys"
        by (metis "2.prems"(1) is_subtree_index_append nth_map snoc subtree_append)
      also have "\<dots> = trim (n - length ys) (ts ! i !t ys)" using 2(1) hi hl by blast
      finally show "trim (Suc n) (Node ts) !t xs = trim (Suc n - length xs) (Node ts !t xs)" 
        by (simp add: snoc subtree_append)
    qed
  qed
qed

lemma length_subtrees_trim: "\<lbrakk>is_subtree_index t xs; length xs < n\<rbrakk> \<Longrightarrow>
  length (subtrees (trim n t !t xs)) = length (subtrees (t !t xs))"
  by (metis subtree_trim length_subtrees_trim_Suc Suc_diff_Suc less_imp_le_nat)

lemma subtree_trim_Leaf: assumes "is_subtree_index (trim n t) xs" "t !t xs = Leaf"
  shows "trim n t !t xs = Leaf"
proof (cases "length xs < n")
  case True
  then show ?thesis
    using length_subtrees_trim assms is_subtree_index_trim subtrees_Leaf by fastforce
next
  case False
  hence "length xs = n" using assms(1) by (simp add: is_subtree_index_trim)
  then show ?thesis using assms(1) is_subtree_index_trim subtree_trim by auto
qed

subsection \<open>The strict $\omega$-category of pasting diagrams\<close>

text \<open>The function \<open>\<delta>\<close> acts as both the source and target map in the globular set of pasting
diagrams. It is denoted $\partial$ in Leinster \cite[p. 264]{Leinster2004}.\<close>
abbreviation \<delta> where
"\<delta> \<equiv> trim"

value "\<delta> 1 (Node [Node [Leaf, Leaf, Leaf], Leaf, Node [Leaf]])"  (* Leinster2004: (8.1), p. 264 *)
value "\<delta> 2 (Node [Node [Node [Leaf, Leaf]], Node [Leaf, Leaf]])" (* Leinster2004: (8.3), p. 265 *)

abbreviation PD :: "nat \<Rightarrow> tree set" where
"PD n \<equiv> {t. height t \<le> n}"

interpretation pd: globular_set PD \<delta> \<delta>
  by (unfold_locales, auto simp add: height_trim_le)

text \<open>The generalised source and target maps have simple interpretations in terms of \<open>trim\<close>.\<close>

lemma s'_eq_trim: assumes "n \<le> m" "height t \<le> m" shows "pd.s' m n t = trim n t"
  using assms
proof (induction m arbitrary: t)
  case 0
  moreover hence "n = 0" by force
  ultimately show ?case using pd.s'_n_n trim_const by simp
next
  case (Suc m)
  then show ?case proof (cases "n = Suc m")
    case True
    then show ?thesis using pd.s'_n_n Suc(3) trim_const by simp
  next
    case False
    with Suc(2) have "n \<le> m" by simp
    hence "pd.s' (Suc m) n t = pd.s' m n (\<delta> m t)" using Suc(3) by force
    also have "\<dots> = \<delta> n (\<delta> m t)" using Suc.IH height_trim_le \<open>n \<le> m\<close> by blast
    finally show ?thesis by (metis trim_trim \<open>n \<le> m\<close> comp_apply)
  qed
qed

lemma s'_eq_t': "pd.s' = pd.t'"
proof (clarsimp simp add: fun_eq_iff)
  fix m n t
  show "pd.s' m n t = pd.t' m n t" proof (induction m arbitrary: n t)
    case 0
    then show ?case
      using pd.s'_n_n pd.t'_n_n pd.s'.simps(2) pd.t'.simps(2) by (cases n, presburger+)
  next
    case (Suc m)
    then show ?case by (cases "Suc m" rule: linorder_cases, simp_all)
  qed
qed

lemma t'_eq_trim: assumes "n \<le> m" "height t \<le> m" shows "pd.t' m n t = trim n t"
  by (metis (mono_tags, lifting) assms s'_eq_trim s'_eq_t')

text \<open>Next we define identities and composition \cite[p. 266]{Leinster2004}. The identity of a tree with height at most \<open>n\<close> is
  the same tree seen as a tree of height at most \<open>n + 1\<close>.\<close>

fun tree_comp :: "nat \<Rightarrow> tree \<Rightarrow> tree \<Rightarrow> tree" where
"tree_comp 0 (Node ts) (Node us) = Node (ts @ us)" |
"tree_comp (Suc n) (Node ts) (Node us) = Node (map2 (tree_comp n) ts us)"

value "tree_comp 1
  (Node [Node [Leaf, Leaf], Leaf, Node [Leaf]])
  (Node [Leaf, Leaf, Node [Leaf, Leaf]])"
  (* Node [Node [Leaf, Leaf], Leaf, Node [Leaf, Leaf, Leaf]] *)
  (* Leinster2001: p. 39 *)

value "tree_comp 0
  (Node [Node [Node [Leaf, Leaf]]])
  (Node [Node [Leaf, Leaf]])"
  (* Node [Node [Node [Leaf, Leaf]], Node [Leaf, Leaf]] *)
  (* Leinster2001: p. 39 *)

value "tree_comp 0
  (tree_comp 0
    (tree_comp 1
      (Node [Leaf, Leaf])
      (Node [Node [Leaf], Node [Leaf, Leaf, Leaf]]))
    (Node [Leaf, Node [Leaf, Leaf]]))
  (Node [Leaf, Leaf, Leaf])"
  (* Node [
      Node [Leaf], 
      Node [Leaf, Leaf, Leaf], 
      Leaf, 
      Node [Leaf, Leaf], 
      Leaf, 
      Leaf, 
      Leaf]*)
  (* Leinster2001: p. 40 *)

lemma tree_comp_0_Leaf1 [simp]: "tree_comp 0 Leaf t = t"
  by (metis eq_Nil_appendI tree.exhaust tree_comp.simps(1))

lemma tree_comp_0_Leaf2 [simp]: "tree_comp 0 t Leaf = t"
  by (metis append_Nil2 tree.exhaust tree_comp.simps(1))

lemma tree_comp_Suc_Leaf1 [simp]: "tree_comp (Suc n) Leaf t = Leaf"
  by (cases t, simp)

lemma tree_comp_Suc_Leaf2 [simp]: "tree_comp (Suc n) t Leaf = Leaf"
  by (cases t, simp)

lemma height_tree_comp_0 [simp]: "height (tree_comp 0 t u) = max (height t) (height u)"
proof (cases "t = Leaf \<or> u = Leaf")
  case True
  then show ?thesis by auto
next
  case False
  hence nempt: "subtrees t \<noteq> [] \<and> subtrees u \<noteq> []" by (metis tree.exhaust_sel)
  have "height (tree_comp 0 t u) = height (Node (subtrees t @ subtrees u))"
    by (metis tree.collapse tree_comp.simps(1))
  also have "\<dots> = Suc (Max (set (map height (subtrees t @ subtrees u))))"
    using nempt height_Node_Max by blast
  also have "\<dots> = Suc (Max (set (map height (subtrees t)) \<union> set (map height (subtrees u))))"
    by simp
  also have "\<dots> = Suc (max (Max (set (map height (subtrees t))))
                          (Max (set (map height (subtrees u)))))"
    using nempt Max_Un by (metis List.finite_set map_is_Nil_conv set_empty2)
  also have "\<dots> = max (Suc (Max (set (map height (subtrees t))))) 
                         (Suc (Max (set (map height (subtrees u)))))"
    by linarith
  finally show "height (tree_comp 0 t u) = max (height t) (height u)"
    using nempt height_Node_Max by (metis tree.collapse)
qed

text \<open>An alternative description of being composable for trees. Defined so that 
\<open>tree_comp n t u\<close> is defined if and only if \<open>composable_tree n t u\<close>.\<close>
fun composable_tree :: "nat \<Rightarrow> tree \<Rightarrow> tree \<Rightarrow> bool" where
"composable_tree 0 (Node ts) (Node us) = True" |
"composable_tree (Suc n) (Node ts) (Node us) = (length ts = length us \<and>
  (\<forall>i < length ts. composable_tree n (ts!i) (us!i)))"

lemma sym_composable_tree: "composable_tree n t u = composable_tree n u t"
  by (induction n t u rule: composable_tree.induct, simp, fastforce)

lemma is_composable_pair_imp_composable_tree: "pd.is_composable_pair m n t u \<Longrightarrow>
  composable_tree n t u"
proof (induction n t u rule: composable_tree.induct)
  case (1 ts us)
  then show ?case by fastforce
next
  case (2 n ts us)
  with pd.is_composable_pair_def have h: "Suc n < m" "height (Node ts) \<le> m" "height (Node us) \<le> m"
    "pd.t' m (Suc n) (Node us) = pd.s' m (Suc n) (Node ts)" by blast+
  moreover hence "Suc n \<le> m" by linarith
  ultimately have htrim: "trim (Suc n) (Node ts) = trim (Suc n) (Node us)"
    by (metis (mono_tags, lifting) s'_eq_trim t'_eq_trim)
  hence "trim 1 (Node ts) = trim 1 (Node us)" 
    by (metis One_nat_def Suc_le_mono le0 trim_eq_imp_trim_eq)
  with trim_1_eq have hl: "length ts = length us" by blast
  moreover have "\<forall>i < length ts. composable_tree n (ts!i) (us!i)" proof (safe)
    fix i assume hi: "i < length ts"
    hence "height (ts!i) \<le> m" using h(2) height_lt nth_mem by fastforce
    moreover have "height (us!i) \<le> m" using hi h(3) height_lt nth_mem hl by fastforce
    moreover have "n < m" using h(1) by simp
    moreover have "trim n (ts!i) = trim n (us!i)" proof -
      have "map (trim n) ts = map (trim n) us" using htrim by auto
      thus "trim n (ts!i) = trim n (us!i)" using nth_map hi hl by metis
    qed
    ultimately have "pd.t' m n (us!i) = pd.s' m n (ts!i)"
      using s'_eq_trim t'_eq_trim order_less_imp_le[of n m] by presburger
    hence "pd.is_composable_pair m n (ts!i) (us!i)" 
      using pd.is_composable_pair_def \<open>n < m\<close> \<open>height (ts!i) \<le> m\<close> \<open>height (us!i) \<le> m\<close> by blast
    with 2(1) hi show "composable_tree n (ts!i) (us!i)" by fast
  qed
  ultimately show ?case by fastforce
qed

lemma composable_tree_imp_trim_eq: "composable_tree n t u \<Longrightarrow> trim n t = trim n u"
proof (induction n t u rule: composable_tree.induct)
  case (1 ts us)
  then show ?case by simp
next
  case (2 n ts us)
  then show ?case
    by (metis (mono_tags, lifting) nth_map trim.simps(2) length_map nth_equalityI 
        composable_tree.simps(2))
qed

lemma composable_tree_imp_is_composable_pair:
  assumes "n < m" "height t \<le> m" "height u \<le> m" "composable_tree n t u"
  shows "pd.is_composable_pair m n t u"
  using assms
proof (induction m arbitrary: n t u)
  case 0
  then show ?case by blast
next
  case (Suc m)
  hence "trim n u = trim n t" using composable_tree_imp_trim_eq by presburger
  hence "pd.t' (Suc m) n u = pd.s' (Suc m) n t"
    using Suc(2-4) s'_eq_trim t'_eq_trim less_imp_le_nat by presburger
  with Suc(2-4) pd.is_composable_pair_def show ?case by blast
qed
                            
lemma is_composable_pair_iff_composable_tree: "pd.is_composable_pair m n t u =
  (n < m \<and> height t \<le> m \<and> height u \<le> m \<and> composable_tree n t u)"
  by (metis (mono_tags, lifting) composable_tree_imp_is_composable_pair
      is_composable_pair_imp_composable_tree mem_Collect_eq pd.is_composable_pair_def)

lemma composable_tree_imp_composable_tree_subtrees:
  "composable_tree (Suc n) (Node ts) (Node us) \<Longrightarrow> \<forall>(t, u) \<in> set (zip ts us). composable_tree n t u"
  by (metis in_set_zip case_prod_beta composable_tree.simps(2))

lemma composable_tree_nth_subtrees:
  "\<lbrakk>composable_tree (Suc n) (Node ts) (Node us); i < length ts\<rbrakk> \<Longrightarrow> composable_tree n (ts!i) (us!i)"
  by fastforce

lemma is_composable_pair_imp_is_composable_pair_subtrees:
  assumes "pd.is_composable_pair (Suc m) (Suc n) (Node ts) (Node us)"
  shows "\<forall>(t, u) \<in> set (zip ts us). pd.is_composable_pair m n t u"
proof
  have "pd.is_composable_pair m n (fst p) (snd p)" if hp: "p \<in> set (zip ts us)" for p proof -
    have "composable_tree (Suc n) (Node ts) (Node us)" 
      using is_composable_pair_iff_composable_tree assms by blast
    hence h: "composable_tree n (fst p) (snd p)" 
      using hp composable_tree_imp_composable_tree_subtrees by fastforce
    have "fst p \<in> set ts" "snd p \<in> set us" by (metis hp in_set_zipE prod.exhaust_sel)+
    hence "height (fst p) \<le> m" "height (snd p) \<le> m"
      by (meson hp height_lt assms less_Suc_eq_le order_less_le_trans
          is_composable_pair_iff_composable_tree)+
    with h is_composable_pair_iff_composable_tree assms
    show "pd.is_composable_pair m n (fst p) (snd p)" by force
  qed
  then show "\<And>x. x \<in> set (zip ts us) \<Longrightarrow> case x of (t, u) \<Rightarrow> pd.is_composable_pair m n t u"
    by force
qed

lemma in_set_map2: "(z \<in> set (map2 f xs ys)) = (\<exists>(x, y) \<in> set (zip xs ys). z = f x y)"
  by auto

lemma height_tree_comp_le: "\<lbrakk>height t \<le> m; height u \<le> m\<rbrakk> \<Longrightarrow> height (tree_comp n t u) \<le> m"
proof (induction n t u arbitrary: m rule: tree_comp.induct)
  case (1 ts us)
  then show ?case using height_tree_comp_0 by presburger
next
  case (2 n ts us)
  show ?case proof (cases "ts \<noteq> [] \<and> us \<noteq> []")
    case True
    hence "\<exists>m'. m = Suc m'" using height_zero "2.prems"(1) not0_implies_Suc by auto
    then obtain m' where "m = Suc m'" by blast
    hence "\<forall>t \<in> set ts. height t \<le> m'" "\<forall>u \<in> set us. height u \<le> m'"
      using True "2.prems" by simp+
    hence "\<forall>(t, u) \<in> set (zip ts us). height (tree_comp n t u) \<le> m'"
      by (metis (no_types, lifting) "2.IH" case_prodI2 set_zip_leftD set_zip_rightD)
    then show ?thesis using True \<open>m = Suc m'\<close> by auto
  next
    case False
    then show ?thesis by force
  qed
qed

lemma nth_map2 [simp]: "\<lbrakk>n < length xs; n < length ys\<rbrakk> \<Longrightarrow> map2 f xs ys ! n = f (xs ! n) (ys ! n)"
  by fastforce

lemma trim_tree_comp1: "composable_tree n t u \<Longrightarrow> trim n (tree_comp n t u) = trim n t"
proof (induction n t u rule: composable_tree.induct)
  case (1 ts us)
  then show ?case by fastforce
next
  case (2 n ts us)
  then show ?case by (simp add: list_eq_iff_nth_eq)
qed

lemma trim_tree_comp2: "composable_tree n t u \<Longrightarrow> trim n (tree_comp n t u) = trim n u"
  using trim_tree_comp1 composable_tree_imp_trim_eq by presburger

lemma map2_map_map': "map2 f (map g xs) (map h ys) = map (\<lambda>(x, y). f (g x) (h y)) (zip xs ys)"
proof (induction xs arbitrary: ys)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case proof (induction ys)
    case Nil
    then show ?case by simp
  next
    case (Cons a ys)
    then show ?case by auto
  qed
qed

lemma trim_tree_comp_commute: "trim m (tree_comp n t u) = tree_comp n (trim m t) (trim m u)"
proof (induction m arbitrary: n t u)
  case 0
  then show ?case by (cases n, simp_all)
next
  case (Suc m)
  then show ?case
    by (induction n t u rule: composable_tree.induct, simp_all add: list_eq_iff_nth_eq)
qed

interpretation pd_pre_cat: pre_strict_omega_category PD \<delta> \<delta> "\<lambda> m. tree_comp" "\<lambda> n. id"
proof (unfold_locales)
  fix m n x' x assume "pd.is_composable_pair m n x' x"
  then show "tree_comp n x' x \<in> PD m"
    using is_composable_pair_iff_composable_tree height_tree_comp_le by auto
next
  fix n show "id \<in> PD n \<rightarrow> PD (Suc n)" by simp
next
  fix m x' x assume "pd.is_composable_pair (Suc m) m x' x"
  then show "\<delta> m (tree_comp m x' x) = \<delta> m x"
    by (simp add: is_composable_pair_iff_composable_tree trim_tree_comp2 height_tree_comp_le)
next
  fix m x' x assume "pd.is_composable_pair (Suc m) m x' x"
  then show "\<delta> m (tree_comp m x' x) = \<delta> m x'"
    by (simp add: is_composable_pair_iff_composable_tree trim_tree_comp1 height_tree_comp_le)
next
  fix m n x' x assume "pd.is_composable_pair (Suc m) n x' x" "n < m"
  then show "\<delta> m (tree_comp n x' x) = tree_comp n (\<delta> m x') (\<delta> m x)"
    by (simp add: is_composable_pair_iff_composable_tree trim_tree_comp_commute height_tree_comp_le)
next 
  fix x n assume "x \<in> PD n"
  then show "\<delta> n (id x) = x" using trim_const by auto
qed

lemma tree_comp_assoc: "tree_comp n (tree_comp n t u) v = tree_comp n t (tree_comp n u v)"
proof (induction n t u arbitrary: v rule: composable_tree.induct)
  case (1 ts us)
  then show ?case by (metis append_assoc tree_comp.simps(1) tree.exhaust)
next
  case (2 n ts us)
  define vs where "vs = subtrees v" hence hv: "v = Node vs" by force
  let ?k = "min (length ts) (min (length us) (length vs))"
  have "\<forall>i < ?k. tree_comp n (tree_comp n (ts!i) (us!i)) (vs!i) =
    tree_comp n (ts!i) (tree_comp n (us!i) (vs!i))" using "2.IH" by auto
  hence "map2 (tree_comp n) (map2 (tree_comp n) ts us) vs =
    map2 (tree_comp n) ts (map2 (tree_comp n) us vs)" by (simp add: list_eq_iff_nth_eq)
  then show ?case using hv by auto
qed

lemma i'_eq_id: "n \<le> m \<Longrightarrow> pd_pre_cat.i' m n = id"
proof (induction m)
  case 0
  then show ?case using pd_pre_cat.i'.simps(1) by blast
next
  case (Suc m)
  then show ?case by (metis pd_pre_cat.i'_Suc id_comp le_Suc_eq pd_pre_cat.i'_n_n)
qed

lemma composable_tree_trim1: "n \<le> m \<Longrightarrow> composable_tree n (trim m t) t"
proof (induction n t arbitrary: m rule: trim.induct)
  case (1 t)
  then show ?case by (metis composable_tree.simps(1) tree.exhaust)
next
  case (2 n ts)
  hence "\<exists>m'. m = Suc m'" by presburger
  then obtain m' where hm: "m = Suc m'" "n \<le> m'" using 2(2) by blast
  moreover hence "\<forall>i < length ts. composable_tree n (\<delta> m' (ts!i)) (ts!i)" using 2(1) by simp
  ultimately show ?case by force
qed

lemma composable_tree_trim2: "n \<le> m \<Longrightarrow> composable_tree n t (trim m t)"
  using sym_composable_tree composable_tree_trim1 by presburger

lemma tree_comp_trim1: "tree_comp n (trim n t) t = t"
  by (induction n t rule: trim.induct, simp add: tree.exhaust, simp add: list_eq_iff_nth_eq)

lemma tree_comp_trim2: "tree_comp n t (trim n t) = t"
  by (induction n t rule: trim.induct, simp add: tree.exhaust, simp add: list_eq_iff_nth_eq)

lemma tree_comp_exchange: 
  "\<lbrakk>q < p; composable_tree p y' y; composable_tree p x' x;
  composable_tree q y' x'; composable_tree q y x\<rbrakk> \<Longrightarrow>
  tree_comp q (tree_comp p y' y) (tree_comp p x' x) =
  tree_comp p (tree_comp q y' x') (tree_comp q y x)"
proof (induction p y' y arbitrary: q x' x rule: composable_tree.induct)
  case (1 ys' ys)
  then show ?case proof (induction q x' x rule: composable_tree.induct)
    case (1 xs' xs)
    then show ?case by blast
  next
    case (2 q xs' xs)
    then show ?case by force
  qed
next
  case (2 p ys' ys)
  then show ?case proof (induction q x' x rule: composable_tree.induct)
    case (1 ts us)
    then show ?case by force
  next
    case (2 n ts us)
    then show ?case by (simp add: list_eq_iff_nth_eq)
  qed
qed

interpretation pd_cat': strict_omega_category PD \<delta> \<delta> "\<lambda> m. tree_comp" "\<lambda> n. id"
proof (unfold_locales)
  fix m n x' x x'' assume "pd.is_composable_pair m n x' x" "pd.is_composable_pair m n x'' x'"
  then show "tree_comp n (tree_comp n x'' x') x = tree_comp n x'' (tree_comp n x' x)"
    using tree_comp_assoc is_composable_pair_iff_composable_tree by force
next
  fix n m x assume "n < m" "x \<in> PD m"
  moreover hence "height x \<le> m" by simp
  ultimately show "tree_comp n (pd_pre_cat.i' m n (pd.t' m n x)) x = x"
    by (metis (no_types, lifting) i'_eq_id t'_eq_trim tree_comp_trim1 id_apply nat_less_le)
next
  fix n m x assume "n < m" "x \<in> PD m"
  moreover hence "height x \<le> m" by simp
  ultimately show "tree_comp n x (pd_pre_cat.i' m n (pd.s' m n x)) = x"
    by (metis (no_types, lifting) i'_eq_id s'_eq_trim tree_comp_trim2 id_apply nat_less_le)
next
  fix q p m y' y x' x assume "q < p" "p < m"
    "pd.is_composable_pair m p y' y" "pd.is_composable_pair m p x' x"
    "pd.is_composable_pair m q y' x'" "pd.is_composable_pair m q y x"
  then show "tree_comp q (tree_comp p y' y) (tree_comp p x' x) =
    tree_comp p (tree_comp q y' x') (tree_comp q y x)"
    using is_composable_pair_iff_composable_tree tree_comp_exchange by meson
qed (simp)

end