theory Undirected_Graph_Walks imports Undirected_Graph_Basics
begin

section \<open>Walks, Paths and Cycles \<close>
text \<open> The definition of walks, paths, cycles, and related concepts are foundations of graph theory,
yet there can be some differences in literature between definitions. This formalisation draws inspiration 
from Noschinski's Graph Library \<^cite>\<open>"noschinski_2015"\<close>, however focuses on an undirected graph context
compared to a directed graph context, and extends on some definitions, as required to formalise
Balog Szemeredi Gowers theorem. \<close>

context ulgraph
begin

subsection \<open> Walks\<close>

text\<open>This definition is taken from the directed graph library, however edges are undirected\<close> 
fun walk_edges :: "'a list \<Rightarrow> 'a edge list" where
    "walk_edges [] = []"
  | "walk_edges [x] = []"
  | "walk_edges (x # y # ys) = {x,y} # walk_edges (y # ys)"

lemma walk_edges_app: "walk_edges (xs @ [y, x]) = walk_edges (xs @ [y]) @ [{y, x}]"
  by (induct xs rule: walk_edges.induct, simp_all)

lemma walk_edges_tl_ss: "set (walk_edges (tl xs)) \<subseteq> set (walk_edges xs)"
  by (induct xs rule: walk_edges.induct)  auto

lemma walk_edges_rev: "rev (walk_edges xs) = walk_edges (rev xs)"
proof (induct xs rule: walk_edges.induct, simp_all)
  fix x y ys assume assm: "rev (walk_edges (y # ys)) = walk_edges (rev ys @ [y])"
  then show "walk_edges (rev ys @ [y]) @ [{x, y}] = walk_edges (rev ys @ [y, x])"
    using walk_edges_app by fastforce 
qed

lemma walk_edges_append_ss1: "set (walk_edges (ys)) \<subseteq> set (walk_edges (xs@ys))"
proof (induct xs rule: walk_edges.induct)
  case 1
  then show ?case by simp
next
  case (2 x)
  then show ?case
    using walk_edges_tl_ss by fastforce 
next
  case (3 x y ys)
  then show ?case by (simp add: subset_iff) 
qed 
 

lemma walk_edges_append_ss2: "set (walk_edges (xs)) \<subseteq> set (walk_edges (xs@ys))"
  by (induct xs rule: walk_edges.induct) auto

lemma walk_edges_singleton_app: "ys \<noteq> [] \<Longrightarrow> walk_edges ([x]@ys) = {x, hd ys} # walk_edges ys"
  using list.exhaust_sel walk_edges.simps(3) by (metis Cons_eq_appendI eq_Nil_appendI) 

lemma walk_edges_append_union: "xs \<noteq> [] \<Longrightarrow> ys \<noteq> [] \<Longrightarrow> 
    set (walk_edges (xs@ys)) = set (walk_edges (xs)) \<union> set (walk_edges ys) \<union> {{last xs, hd ys}}"
  using walk_edges_singleton_app  by (induct xs rule: walk_edges.induct) auto

lemma walk_edges_decomp_ss: "set (walk_edges (xs@[y]@zs)) \<subseteq> set (walk_edges (xs@[y]@ys@[y]@zs))"
proof -
  have half_ss: "set (walk_edges (xs@[y])) \<subseteq> set (walk_edges (xs@[y]@ys@[y]))" 
    using walk_edges_append_ss2 by fastforce
  thus ?thesis proof (cases "zs = []")
    case True
    then show ?thesis using half_ss by auto
  next
    case False
    then have decomp1: "set (walk_edges (xs@[y]@zs)) = set (walk_edges (xs@[y])) \<union> set (walk_edges (zs)) \<union> {{y, hd zs}}" 
      using walk_edges_append_union
      by (metis append_assoc append_is_Nil_conv last_snoc neq_Nil_conv) 
    have "set (walk_edges (xs@[y]@ys@[y]@zs)) =  set (walk_edges (xs@[y]@ys@[y])) \<union> set (walk_edges (zs)) \<union> {{y, hd zs}}"
      using walk_edges_append_union False
      by (metis append_assoc append_is_Nil_conv empty_iff empty_set last_snoc list.set_intros(1)) 
    then show ?thesis using decomp1 half_ss by auto
  qed
qed

definition walk_length :: "'a list \<Rightarrow> nat" where
  "walk_length p \<equiv> length (walk_edges p)"

lemma walk_length_conv: "walk_length p = length p - 1"
  by (induct p rule: walk_edges.induct) (auto simp: walk_length_def)

lemma walk_length_rev: "walk_length p = walk_length (rev p)"
  using walk_edges_rev walk_length_def
  by (metis length_rev) 

lemma walk_length_app: "xs \<noteq> [] \<Longrightarrow> ys \<noteq> [] \<Longrightarrow> walk_length (xs @ ys) = walk_length xs + walk_length ys + 1"
  apply (induct xs rule: walk_edges.induct) 
    apply (simp_all add: walk_length_def)
  using walk_edges_singleton_app by force

lemma walk_length_app_ineq: "walk_length (xs @ ys) \<ge> walk_length xs + walk_length ys \<and> 
  walk_length (xs @ ys) \<le> walk_length xs + walk_length ys + 1"
proof (cases "xs = [] \<or> ys = []")
  case True
  then show ?thesis using walk_length_def by auto 
next
  case False
  then show ?thesis
    by (simp add: walk_length_app) 
qed

text \<open> Note that while the trivial walk is allowed, the empty walk is not \<close>
definition is_walk :: "'a list \<Rightarrow> bool" where
"is_walk xs \<equiv> set xs \<subseteq> V \<and> set (walk_edges xs) \<subseteq> E \<and> xs \<noteq> []"

lemma is_walkI: "set xs \<subseteq> V \<Longrightarrow> set (walk_edges xs) \<subseteq> E \<Longrightarrow> xs \<noteq> [] \<Longrightarrow> is_walk xs"
  using is_walk_def by simp 

lemma is_walk_wf: "is_walk xs \<Longrightarrow> set xs \<subseteq> V"
  by (simp add: is_walk_def)

lemma is_walk_wf_hd: "is_walk xs \<Longrightarrow> hd xs \<in> V"
  using is_walk_wf hd_in_set is_walk_def by blast 

lemma is_walk_wf_last: "is_walk xs \<Longrightarrow> last xs \<in> V"
  using is_walk_wf last_in_set is_walk_def by blast

lemma is_walk_singleton: "u \<in> V \<Longrightarrow> is_walk [u]"
  unfolding is_walk_def using walk_edges.simps by simp

lemma is_walk_not_empty: "is_walk xs \<Longrightarrow> xs \<noteq> []" 
  unfolding is_walk_def by simp

lemma is_walk_not_empty2: "is_walk [] = False" 
  unfolding is_walk_def by simp

text \<open>Reasoning on transformations of a walk \<close>
lemma is_walk_rev: "is_walk xs \<longleftrightarrow> is_walk (rev xs)"
  unfolding is_walk_def using walk_edges_rev
  by (metis rev_is_Nil_conv set_rev)

lemma is_walk_tl: "length xs \<ge> 2 \<Longrightarrow> is_walk xs \<Longrightarrow> is_walk (tl xs)"
  using walk_edges_tl_ss is_walk_def in_mono list.set_sel(2) tl_Nil by fastforce
 
lemma is_walk_append: 
  assumes "is_walk xs"
  assumes "is_walk ys"
  assumes "last xs = hd ys"
  shows "is_walk (xs @ (tl ys))"
proof (intro is_walkI subsetI)
  show "xs @ tl ys \<noteq> []" using is_walk_def assms by auto
  show "\<And>x. x \<in> set (xs @ tl ys) \<Longrightarrow> x \<in> V" using assms is_walk_def is_walk_wf
    by (metis Un_iff in_mono list_set_tl set_append)
next
  fix x assume xin: "x \<in> set (walk_edges (xs @ tl ys))"
  show "x \<in> E" proof (cases "tl ys = []")
    case True
    then show ?thesis using assms(1) is_walk_def xin by auto
  next
    case False
    then have xin2: "x \<in> (set (walk_edges xs) \<union> set (walk_edges (tl ys)) \<union> {{last xs, hd (tl ys)}})" 
      using walk_edges_append_union is_walk_not_empty assms xin by auto
    have 1: "set (walk_edges xs) \<subseteq> E" using assms(1) is_walk_def
      by simp 
    have 2: "set (walk_edges (tl ys)) \<subseteq> E" using assms(2) is_walk_def
      by (meson dual_order.trans walk_edges_tl_ss)
    have "{last xs, hd (tl ys)} \<in> E" using is_walk_def assms(2) assms(3)
      by (metis False hd_Cons_tl insert_subset list.simps(15) walk_edges.simps(3)) 
    then show ?thesis using 1 2 xin2 by auto
  qed
qed

lemma is_walk_decomp: 
  assumes "is_walk (xs@[y]@ys@[y]@zs)" (is "is_walk ?w")
  shows "is_walk (xs@[y]@zs)"
proof (intro is_walkI) 
  show "set (xs @ [y] @ zs) \<subseteq> V"  using assms is_walk_def by simp
  show "xs @ [y] @ zs \<noteq> []" by simp
  show "set (walk_edges (xs @ [y] @ zs)) \<subseteq> E" 
    using walk_edges_decomp_ss assms(1) is_walk_def by blast 
qed

lemma is_walk_hd_tl: 
  assumes "is_walk (y # ys)"
  assumes "{x, y} \<in> E"
  shows "is_walk (x # y # ys)"
proof (intro is_walkI)
  show "set (x # y # ys) \<subseteq> V"
    using assms by (simp add: is_walk_def wellformed_alt_fst) 
  show "set (walk_edges (x # y # ys)) \<subseteq> E"
    using walk_edges.simps assms is_walk_def by simp
  show "x # y # ys \<noteq> []" by simp
qed

lemma is_walk_drop_hd: 
  assumes "ys \<noteq> []"
  assumes "is_walk (y # ys)"
  shows "is_walk ys"
proof (intro is_walkI)
  show "set ys \<subseteq> V" 
    using assms is_walk_wf by fastforce
  show "set (walk_edges ys) \<subseteq> E"
    using assms is_walk_def walk_edges_tl_ss by force 
  show "ys \<noteq> []" using assms by simp
qed

lemma walk_edges_index: 
  assumes "i \<ge> 0" "i < walk_length w"
  assumes "is_walk w"
  shows "(walk_edges w) ! i \<in> E"
  using assms 
proof (induct w arbitrary: i rule: walk_edges.induct, simp add: is_walk_not_empty2, 
    simp add: walk_length_def)
  case (3 x y ys)
  then show ?case proof (cases "i = 0")
    case True
    then show ?thesis
      using "3.prems"(3) is_walk_def by fastforce 
  next
    case False
    have gt: "0 \<le> i -1" using False by simp
    have lt: "i - 1 < walk_length (y # ys)"
      using "3.prems"(2) False walk_length_conv by auto 
    have "is_walk (y # ys)"
      using "3.prems"(3) is_walk_def by fastforce 
    then show ?thesis using "3.hyps"[of "i -1"]
      by (metis "3.prems"(1) False gt lt le_neq_implies_less nth_Cons_pos walk_edges.simps(3)) 
  qed
qed

lemma is_walk_index: 
  assumes "i \<ge> 0" "Suc i < (length w)"
  assumes "is_walk w"
  shows "{w ! i, w ! (i + 1)} \<in> E" 
  using assms proof (induct w arbitrary: i rule: walk_edges.induct, simp, simp)
  fix x y ys i
  assume IH: "\<And>j. 0 \<le> j \<Longrightarrow> Suc j < length (y # ys) \<Longrightarrow> is_walk (y # ys) \<Longrightarrow> {(y # ys) ! j, (y # ys) ! (j + 1)} \<in> E"
  assume 1: " 0 \<le> i" and 2: "Suc i < length (x # y # ys)" and 3: "is_walk (x # y # ys)"
  show "{(x # y # ys) ! i, (x # y # ys) ! (i + 1)} \<in> E"
  proof (cases "i = 0")
    case True
    then show ?thesis using 3 is_walk_def
      by simp 
  next
    case False
    have "is_walk (y # ys)" using is_walk_def 3 by fastforce
    then show ?thesis using 2 IH[of "i - 1"]
      by (simp add: False nat_less_le)
  qed
qed

lemma is_walk_take: 
  assumes "is_walk w"
  assumes "n > 0"
  assumes "n \<le> length w"
  shows "is_walk (take n w)"
  using assms proof (induct w arbitrary: n rule: walk_edges.induct)
  case 1
  then show ?case by simp 
next
  case (2 x)
  then have "n = 1" using 2 by auto
  then show ?case by (simp add: "2.prems"(1)) 
next
  case (3 x y ys)
  then show ?case proof (cases "n = 1")
    case True
    then have "take n (x # y # ys) = [x]"
      by simp 
    then show ?thesis using is_walk_def "3.prems"(1) by simp
  next
    case False
    then have ngt: "n \<ge> 2" using "3.prems"(2) by auto
    then have tk_split1: "take n (x # y # ys) = x # take (n - 1) (y # ys)" using 3
      by (simp add: take_Cons') 
    then have tk_split: "take n (x # y # ys) = x # y # (take (n - 2) ys)" 
      using 3 ngt take_Cons'[of "n -1" "y" "ys"]
      by (metis False diff_diff_left less_one nat_neq_iff one_add_one zero_less_diff)  
    have w: "is_walk (y # ys)" using is_walk_tl
      using "3.prems"(1) is_walk_def by force 
    have "n - 1 \<le> length (y # ys)" using "3.prems"(3) by simp
    then have w_tl: "is_walk (take (n - 1) (y # ys))" using "3.hyps"[of "n - 1"] w "3.prems" ngt
      by linarith 
    have "{x, y} \<in> E" using is_walk_def walk_edges.simps "3.prems"(1) by auto 
    then show ?thesis using is_walk_hd_tl[of y "(take (n - 2) ys)" x] tk_split
      using tk_split1 w_tl by force 
  qed
qed

lemma is_walk_drop: 
  assumes "is_walk w"
  assumes "n < length w"
  shows "is_walk (drop n w)"
  using assms proof (induct w arbitrary: n rule: walk_edges.induct)
  case 1
  then show ?case by simp 
next
  case (2 x)
  then have "n = 0" using 2 by auto
  then show ?case by (simp add: "2.prems"(1)) 
next
  case (3 x y ys)
  then show ?case proof (cases "n \<ge> 2")
    case True
    then have ngt: "n \<ge> 2" using "3.prems"(2) by auto
    then have tk_split1: "drop n (x # y # ys) = drop (n - 1) (y # ys)" using 3
      by (simp add: drop_Cons') 
    then have tk_split: "drop n (x # y # ys) = (drop (n - 2) ys)" 
      using 3 ngt drop_Cons'[of "n -1" "y" "ys"] True
      by (metis Suc_1 Suc_le_eq diff_diff_left less_not_refl nat_1_add_1 zero_less_diff) 
    have w: "is_walk (y # ys)" using is_walk_tl
      using "3.prems"(1) is_walk_def by force 
    have "n - 1 < length (y # ys)" using "3.prems"(2) by simp
    then have w_tl: "is_walk (drop (n - 1) (y # ys))" using "3.hyps"[of "n - 1"] w "3.prems" ngt
      by linarith 
    have "{x, y} \<in> E" using is_walk_def walk_edges.simps "3.prems"(1) by auto 
    then show ?thesis using is_walk_hd_tl[of y "(take (n - 2) ys)" x] tk_split
      using tk_split1 w_tl by force 
  next 
    case False
    then have or: "n = 0 \<or> n = 1"
      by auto
    have walk: "is_walk (y # ys)" using is_walk_drop_hd 3 by blast 
    have n0: "n = 0 \<Longrightarrow> (drop n (x # y # ys)) = (x # y # ys)" by simp
    have "n = 1 \<Longrightarrow> (drop n (x # y # ys)) = y # ys" by simp
    then show ?thesis using n0 3 walk or by auto
  qed
qed

definition walks :: "'a list set" where
  "walks \<equiv> {p. is_walk p}"

definition is_open_walk :: "'a list \<Rightarrow> bool" where
"is_open_walk xs \<equiv> is_walk xs \<and> hd xs \<noteq> last xs"

lemma is_open_walk_rev: "is_open_walk xs \<longleftrightarrow> is_open_walk (rev xs)"
  unfolding is_open_walk_def using is_walk_rev
  by (metis hd_rev last_rev) 

definition is_closed_walk :: "'a list \<Rightarrow> bool" where
"is_closed_walk xs \<equiv> is_walk xs \<and> hd xs = last xs"

lemma is_closed_walk_rev: "is_closed_walk xs \<longleftrightarrow> is_closed_walk (rev xs)"
  unfolding is_closed_walk_def using is_walk_rev
  by (metis hd_rev last_rev)

definition is_trail :: "'a list \<Rightarrow> bool" where
"is_trail xs \<equiv> is_walk xs \<and> distinct (walk_edges xs)"

lemma is_trail_rev: "is_trail xs \<longleftrightarrow> is_trail (rev xs)"
  unfolding is_trail_def using is_walk_rev
  by (metis distinct_rev walk_edges_rev) 

subsection \<open>Paths\<close>

text \<open>There are two common definitions of a path. The first, given below, excludes the case
where a path is a cycle. Note this also excludes the trivial path $[x]$\<close>
definition is_path :: "'a list \<Rightarrow> bool" where
"is_path xs \<equiv> (is_open_walk xs \<and> distinct (xs))"

lemma is_path_rev: "is_path xs \<longleftrightarrow> is_path (rev xs)"
  unfolding is_path_def using is_open_walk_rev 
  by (metis distinct_rev)

lemma is_path_walk: "is_path xs \<Longrightarrow> is_walk xs"
  unfolding is_path_def is_open_walk_def by auto

definition paths :: "'a list set" where 
"paths \<equiv> {p . is_path p}"

lemma paths_ss_walk: "paths \<subseteq> walks"
  unfolding paths_def walks_def is_path_def is_open_walk_def by auto

text \<open> A more generic definition of a path - used when a cycle is considered a path, and 
therefore includes the trivial path $[x]$ \<close>
definition is_gen_path:: "'a list \<Rightarrow> bool" where
"is_gen_path p \<equiv> is_walk p \<and> ((distinct (tl p) \<and> hd p = last p) \<or> distinct p)"

lemma is_path_gen_path: "is_path p \<Longrightarrow> is_gen_path p"
  unfolding is_path_def is_gen_path_def is_open_walk_def by (auto simp add: distinct_tl)

lemma is_gen_path_rev: "is_gen_path p \<longleftrightarrow> is_gen_path (rev p)"
  unfolding is_gen_path_def using is_walk_rev distinct_tl_rev
  by (metis distinct_rev hd_rev last_rev)

lemma is_gen_path_distinct: "is_gen_path p \<Longrightarrow> hd p \<noteq> last p \<Longrightarrow> distinct p"
  unfolding is_gen_path_def by auto

lemma is_gen_path_distinct_tl: 
  assumes "is_gen_path p" and "hd p = last p" 
  shows "distinct (tl p)"
proof (cases "length p > 1")
  case True
  then show ?thesis
    using assms(1) distinct_tl is_gen_path_def by auto 
next
  case False
  then show ?thesis
    using assms(1) distinct_tl is_gen_path_def by auto 
qed

lemma is_gen_path_trivial: "x \<in> V \<Longrightarrow> is_gen_path [x]"
  unfolding is_gen_path_def is_walk_def by simp 

definition gen_paths :: "'a list set" where
"gen_paths \<equiv> {p . is_gen_path p}"

lemma gen_paths_ss_walks: "gen_paths \<subseteq> walks"
  unfolding gen_paths_def walks_def is_gen_path_def by auto

subsection \<open> Cycles \<close>
text \<open>Note, a cycle must be non trivial (i.e. have an edge), but as we let a loop by a cycle
we broaden the definition in comparison to Noschinski \<^cite>\<open>"noschinski_2015"\<close> for a cycle to be of 
length greater than 1 rather than 3 \<close>
definition is_cycle :: "'a list \<Rightarrow> bool" where
"is_cycle xs \<equiv> is_closed_walk xs \<and> walk_length xs \<ge> 1 \<and> distinct (tl xs)"

lemma is_gen_path_cycle: "is_cycle p \<Longrightarrow> is_gen_path p"
  unfolding is_cycle_def is_gen_path_def is_closed_walk_def by auto

lemma is_cycle_alt_gen_path: "is_cycle xs \<longleftrightarrow> is_gen_path xs \<and> walk_length xs \<ge> 1 \<and> hd xs = last xs"
proof (intro iffI)
  show "is_cycle xs \<Longrightarrow> is_gen_path xs \<and> 1 \<le> walk_length xs \<and> hd xs = last xs"
    using is_gen_path_cycle is_cycle_def is_closed_walk_def
    by auto 
  show "is_gen_path xs \<and> 1 \<le> walk_length xs \<and> hd xs = last xs \<Longrightarrow> is_cycle xs"
    using distinct_tl is_closed_walk_def is_cycle_def is_gen_path_def by blast
qed

lemma is_cycle_alt: "is_cycle xs \<longleftrightarrow> is_walk xs \<and> distinct (tl xs) \<and> walk_length xs \<ge> 1 \<and> hd xs = last xs"
proof (intro iffI)
  show "is_cycle xs \<Longrightarrow> is_walk xs \<and> distinct (tl xs) \<and> 1 \<le> walk_length xs \<and> hd xs = last xs"
    using is_cycle_alt_gen_path is_cycle_def is_gen_path_def by blast 
  show "is_walk xs \<and> distinct (tl xs) \<and> 1 \<le> walk_length xs \<and> hd xs = last xs \<Longrightarrow> is_cycle xs"
    by (simp add: is_cycle_alt_gen_path is_gen_path_def)
qed

lemma is_cycle_rev: "is_cycle xs \<longleftrightarrow> is_cycle (rev xs)"
proof -
  have len: "1 \<le> walk_length xs \<longleftrightarrow> 1 \<le> walk_length (rev xs)"
    by (metis length_rev walk_edges_rev walk_length_def)
  have "hd xs = last xs \<Longrightarrow> distinct (tl xs) \<longleftrightarrow> distinct (tl (rev xs))"
    using distinct_tl_rev by blast 
  then show ?thesis using len is_cycle_def
    using is_closed_walk_def is_closed_walk_rev by auto 
qed

lemma cycle_tl_is_path: "is_cycle xs \<and> walk_length xs \<ge> 3 \<Longrightarrow> is_path (tl xs)"
proof (simp add: is_cycle_def is_path_def is_open_walk_def is_closed_walk_def walk_length_conv, 
    elim conjE, intro conjI, simp add: is_walk_tl)
  assume w: "is_walk xs" and eq: "hd xs = last xs" and  "3 \<le> length xs - Suc 0" and 
    dis: "distinct (tl xs)"
  then have len: "4 \<le> length xs"
    by linarith 
  then have lentl: "3 \<le> length (tl xs)" by simp
  then have lentltl: "2 \<le> length (tl (tl xs))" by simp
  have "last (tl (tl xs)) = last (tl xs)"
    by (metis One_nat_def Suc_1 \<open>3 \<le> length xs - Suc 0\<close> diff_is_0_eq' is_walk_def is_walk_tl last_tl 
        lentl not_less_eq_eq numeral_le_one_iff one_le_numeral order.trans semiring_norm(70) w) 
  then have "last (tl xs) \<in> set (tl (tl xs))"
    using  last_in_list_tl_set lentltl by (metis last_in_set list.sel(2))  
  moreover have "hd (tl xs) \<notin> set (tl (tl xs))" using dis lentltl
    by (metis distinct.simps(2) hd_Cons_tl list.sel(2) list.size(3) not_numeral_le_zero) 
  ultimately show "hd (tl xs) \<noteq> last (tl xs)" by fastforce 
qed

lemma is_gen_path_path: 
  assumes "is_gen_path p" and "walk_length p > 0" and "(\<not> is_cycle p)"
  shows "is_path p"
proof (simp add: is_gen_path_def is_path_def is_open_walk_def, intro conjI)
  show "is_walk p" using is_gen_path_def assms(1) by simp
  show ne: "hd p \<noteq> last p"
    using assms(1) assms(2) assms(3) is_cycle_alt_gen_path by auto 
  have "((distinct (tl p) \<and> hd p = last p) \<or> distinct p)" using is_gen_path_def assms(1) by auto
  thus "distinct p" using ne by auto
qed

lemma is_gen_path_options: "is_gen_path p \<longleftrightarrow> is_cycle p \<or> is_path p \<or> (\<exists> v \<in> V. p = [v])"
proof (intro iffI)
  assume a: "is_gen_path p"
  then have "p \<noteq> []" unfolding is_gen_path_def is_walk_def by auto
  then have "(\<forall> v \<in> V . p \<noteq> [v]) \<Longrightarrow> walk_length p > 0" using walk_length_def
    by (metis a is_gen_path_def is_walk_wf_hd length_greater_0_conv list.collapse list.distinct(1) walk_edges.simps(3)) 
  then show "is_cycle p \<or> is_path p \<or> (\<exists> v \<in> V. p = [v])"
    using a is_gen_path_path by auto
next
  show "is_cycle p \<or> is_path p \<or> (\<exists> v \<in> V. p = [v]) \<Longrightarrow> is_gen_path p " 
    using is_gen_path_cycle is_path_gen_path is_gen_path_trivial by auto
qed

definition cycles :: "'a list set" where
  "cycles \<equiv> {p. is_cycle p}"

lemma cycles_ss_gen_paths: "cycles \<subseteq> gen_paths"
  unfolding cycles_def gen_paths_def using is_gen_path_cycle by auto

lemma gen_paths_ss: "gen_paths \<subseteq> cycles \<union> paths \<union> {[v] | v. v \<in> V}"
  unfolding gen_paths_def cycles_def paths_def using is_gen_path_options by auto

text \<open>Walk edges are distinct in a path and cycle \<close>
lemma distinct_edgesI:
  assumes "distinct p" shows "distinct (walk_edges p)"
proof -
  from assms have "?thesis" "\<And>u. u \<notin> set p \<Longrightarrow> (\<And>v. u \<noteq> v \<Longrightarrow> {u,v} \<notin> set (walk_edges p))"
    by (induct p rule: walk_edges.induct) auto
  then show ?thesis by simp
qed

lemma scycles_distinct_edges:
  assumes "c \<in> cycles" "3 \<le> walk_length c" shows "distinct (walk_edges c)"
proof -
  from assms  have c_props: "distinct (tl c)" "4 \<le> length c" "hd c = last c"
    by (auto simp add: cycles_def is_cycle_def is_closed_walk_def walk_length_conv)
  then have "{hd c, hd (tl c)} \<notin> set (walk_edges (tl c))"
  proof (induct c rule: walk_edges.induct)
    case (3 x y ys)
    then have "hd ys \<noteq> last ys" by (cases ys) auto
    moreover
    from 3 have "walk_edges (y # ys) = {y, hd ys} # walk_edges ys"
      by (cases ys) auto
    moreover
    { fix xs have "set (walk_edges xs) \<subseteq> Pow (set xs)"
        by (induct xs rule: walk_edges.induct) auto }
    ultimately
    show ?case using 3 by auto
  qed simp_all
  moreover
  from assms have "distinct (walk_edges (tl c))"
    by (intro distinct_edgesI) (simp add: cycles_def is_cycle_def)
  ultimately
  show ?thesis by(cases c, simp_all) 
      (metis distinct.simps(1) distinct.simps(2) list.sel(1) list.sel(3) walk_edges.elims)
qed

end

context fin_ulgraph
begin

lemma finite_paths: "finite paths"
proof -
  have ss: "paths \<subseteq> {xs. set xs \<subseteq> V \<and> length xs \<le> (card (V))}"
  proof (rule, simp, intro conjI)
    show 1: "\<And>x. x \<in> paths \<Longrightarrow> set x \<subseteq> V"
      unfolding paths_def is_path_def is_open_walk_def is_walk_def by simp
    fix x assume a: "x \<in> paths"
    then have "distinct x" 
      using paths_def is_path_def by simp_all
    then have eq: "length x = card (set x)"
      by (simp add: distinct_card)
    then show "length x \<le> gorder" using a 1
      by (simp add: card_mono finV) 
  qed
  have "finite {xs. set xs \<subseteq> V \<and> length xs \<le> (card (V))}"
    using finV by (simp add: finite_lists_length_le) 
  thus ?thesis using ss finite_subset by auto
qed

lemma finite_cycles: "finite (cycles)"
proof -
  have "cycles \<subseteq> {xs. set xs \<subseteq> V \<and> length xs \<le> Suc (card (V))}"
  proof (rule, simp)
    fix p assume "p \<in> cycles"
    then have "distinct (tl p)" and "set p \<subseteq> V"
      unfolding cycles_def walks_def is_cycle_def is_closed_walk_def is_walk_def
      by (simp_all) 
    then have "set (tl p) \<subseteq> V"
      by (cases p) auto
    with finV have "card (set (tl p)) \<le> card (V)"
      by (rule card_mono)
    then have "length (p) \<le> 1 + card (V)"
      using distinct_card[OF \<open>distinct (tl p)\<close>] by auto
    then show "set p \<subseteq> V \<and> length p \<le> Suc (card (V))"
      by (simp add: \<open>set p \<subseteq> V\<close>) 
  qed
  moreover
  have "finite {xs. set xs \<subseteq> V \<and> length xs \<le> Suc (card (V))}"
    using finV by (rule finite_lists_length_le)
  ultimately
  show ?thesis by (rule finite_subset)
qed

lemma finite_gen_paths: "finite (gen_paths)"
proof -
  have "finite ({[v] | v . v \<in> V})" using finV by auto
  thus ?thesis  using gen_paths_ss finite_cycles finite_paths finite_subset by auto
qed

end

end