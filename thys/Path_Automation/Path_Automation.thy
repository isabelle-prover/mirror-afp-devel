(*
  File: Path_Automation.thy
  Author: Manuel Eberl, University of Innsbruck

  Notions of equivalence of paths and loops and the subpath relation.
*)
section \<open>Automation for paths\<close>
theory Path_Automation
  imports "HOL-Library.Sublist" Path_Equivalence
begin

text \<open>
  In this section, we provide some machinery to make certain common arguments about paths easier.
  In particular:

    \<^item> Proving the equivalence of some combination of lines and circular arcs modulo
      associativity

    \<^item> Proving the equivalence of loops modulo associativity and ``rotation''

    \<^item> Proving subpath relationships

    \<^item> Decomposing a contour integral over a composite path into the contour integrals of its
      constituent paths

  Equivalence arguments that involve splitting, e.g.\ 
  \<^prop>\<open>linepath 0 1 +++ linepath 1 2 \<equiv>\<^sub>p linepath 0 2\<close> are not supported.
\<close>

subsection \<open>Joining a list of paths together\<close>

text \<open>
  The following operation takes a non-empty list of paths and joines them together
  left-to-right, i.e. it is an \<open>n\<close>-ary version of \<^const>\<open>joinpaths\<close>. Associativity is to the right.

  A list of paths is considered well-formed if it is non-empty, each path is indeed a well-formed
  path, and each successive pair of paths has compatible ends.
\<close>

fun joinpaths_list :: "(real \<Rightarrow> 'a :: real_normed_vector) list \<Rightarrow> real \<Rightarrow> 'a" where
  "joinpaths_list [] = linepath 0 0"
| "joinpaths_list [p] = p"
| "joinpaths_list (p # ps) = p +++ joinpaths_list ps"

lemma joinpaths_list_Cons [simp]: "ps \<noteq> [] \<Longrightarrow> joinpaths_list (p # ps) = p +++ joinpaths_list ps"
  by (cases ps) auto

fun wf_pathlist :: "(real \<Rightarrow> 'a :: real_normed_vector) list \<Rightarrow> bool" where
  "wf_pathlist [] \<longleftrightarrow> False"
| "wf_pathlist [p] \<longleftrightarrow> path p"
| "wf_pathlist (p # q # ps) \<longleftrightarrow> path p \<and> path q \<and> pathfinish p = pathstart q \<and> wf_pathlist (q # ps)"

fun weak_wf_pathlist :: "(real \<Rightarrow> 'a :: real_normed_vector) list \<Rightarrow> bool" where
  "weak_wf_pathlist [] \<longleftrightarrow> False"
| "weak_wf_pathlist [p] \<longleftrightarrow> True"
| "weak_wf_pathlist (p # q # ps) \<longleftrightarrow> pathfinish p = pathstart q \<and> weak_wf_pathlist (q # ps)"

fun arc_joinpaths_list_aux :: "(real \<Rightarrow> 'a :: real_normed_vector) list \<Rightarrow> bool" where
  "arc_joinpaths_list_aux [] \<longleftrightarrow> False"
| "arc_joinpaths_list_aux [p] \<longleftrightarrow> True"
| "arc_joinpaths_list_aux (p # q # ps) \<longleftrightarrow>
     path_image p \<inter> path_image q \<subseteq> {pathfinish p} \<and>
     (\<forall>r\<in>set ps. path_image p \<inter> path_image r = {}) \<and>
     arc_joinpaths_list_aux (q # ps)"

definition arc_joinpaths_list :: "(real \<Rightarrow> 'a :: real_normed_vector) list \<Rightarrow> bool" where
  "arc_joinpaths_list ps \<longleftrightarrow> arc_joinpaths_list_aux ps \<and> (\<forall>p\<in>set ps. arc p)"

fun simple_joinpaths_list :: "(real \<Rightarrow> 'a :: real_normed_vector) list \<Rightarrow> bool" where
  "simple_joinpaths_list [] \<longleftrightarrow> False"
| "simple_joinpaths_list [p] \<longleftrightarrow> simple_path p"
| "simple_joinpaths_list [p, q] \<longleftrightarrow>
     path_image p \<inter> path_image q \<subseteq> {pathfinish p} \<union> ({pathstart p} \<inter> {pathfinish q}) \<and> arc p \<and> arc q"
| "simple_joinpaths_list (p # q # ps) \<longleftrightarrow>
     path_image p \<inter> path_image q \<subseteq> {pathfinish p} \<and>
     (\<forall>r\<in>set (butlast ps). path_image p \<inter> path_image r = {}) \<and>
     path_image p \<inter> path_image (last ps) \<subseteq> {pathstart p} \<inter> {pathfinish (last ps)} \<and>
     arc_joinpaths_list_aux (q # ps) \<and> arc p \<and> (\<forall>r\<in>set (q#ps). arc r)"

lemma simple_joinpaths_list_Cons [simp]:
  assumes "ps \<noteq> []"
  shows "simple_joinpaths_list (p # q # ps) \<longleftrightarrow>
           path_image p \<inter> path_image q \<subseteq> {pathfinish p} \<and>
     (\<forall>r\<in>set (butlast ps). path_image p \<inter> path_image r = {}) \<and>
     path_image p \<inter> path_image (last ps) \<subseteq> {pathstart p} \<inter> {pathfinish (last ps)} \<and>
     arc_joinpaths_list_aux (q # ps) \<and> arc p \<and> (\<forall>q\<in>set (q#ps). arc q)"
  using assms by (cases ps rule: simple_joinpaths_list.cases) simp_all


lemma wf_pathlist_Cons:
  "wf_pathlist (p # ps) \<longleftrightarrow> path p \<and> (ps = [] \<or> pathfinish p = pathstart (hd ps) \<and> wf_pathlist ps)"
  by (induction ps arbitrary: p) auto

lemma weak_wf_pathlist_Cons:
  "weak_wf_pathlist (p # ps) \<longleftrightarrow> (ps = [] \<or> pathfinish p = pathstart (hd ps) \<and> weak_wf_pathlist ps)"
  by (induction ps arbitrary: p) auto

fun valid_path_pathlist where
  "valid_path_pathlist [] \<longleftrightarrow> False"
| "valid_path_pathlist [p] \<longleftrightarrow> valid_path p"
| "valid_path_pathlist (p # ps) \<longleftrightarrow> valid_path p \<and> valid_path_pathlist ps"

lemma valid_path_pathlist_Cons:
  "valid_path_pathlist (p # ps) \<longleftrightarrow> valid_path p \<and> (ps = [] \<or> valid_path_pathlist ps)"
  by (cases ps) auto

lemma valid_path_pathlist_altdef: "valid_path_pathlist xs \<longleftrightarrow> xs \<noteq> [] \<and> list_all valid_path xs"
  by (induction xs) (auto simp: valid_path_pathlist_Cons)

lemma valid_path_weak_wf_pathlist_imp_wf:
  "valid_path_pathlist ps \<Longrightarrow> weak_wf_pathlist ps \<Longrightarrow> wf_pathlist ps"
  by (induction ps)
     (auto dest: valid_path_imp_path simp: valid_path_pathlist_Cons
                 weak_wf_pathlist_Cons wf_pathlist_Cons)

lemma wf_pathlist_append:
  assumes "ps \<noteq> []" "qs \<noteq> []"
  shows   "wf_pathlist (ps @ qs) \<longleftrightarrow>
             wf_pathlist ps \<and> wf_pathlist qs \<and> pathfinish (last ps) = pathstart (hd qs)"
  using assms
  by (induction ps arbitrary: qs rule: wf_pathlist.induct) (auto simp: wf_pathlist_Cons)

lemma wf_pathlist_append':
  "wf_pathlist (ps @ qs) \<longleftrightarrow> (ps = [] \<and> wf_pathlist qs) \<or> (qs = [] \<and> wf_pathlist ps) \<or> 
     (wf_pathlist ps \<and> wf_pathlist qs \<and> pathfinish (last ps) = pathstart (hd qs))"
  using wf_pathlist_append[of ps qs] by (cases "ps = []"; cases "qs = []") auto

lemma weak_wf_pathlist_append:
  assumes "ps \<noteq> []" "qs \<noteq> []"
  shows   "weak_wf_pathlist (ps @ qs) \<longleftrightarrow>
             weak_wf_pathlist ps \<and> weak_wf_pathlist qs \<and> pathfinish (last ps) = pathstart (hd qs)"
  using assms
  by (induction ps arbitrary: qs rule: weak_wf_pathlist.induct) (auto simp: weak_wf_pathlist_Cons)

lemma weak_wf_pathlist_append':
  "weak_wf_pathlist (ps @ qs) \<longleftrightarrow> (ps = [] \<and> weak_wf_pathlist qs) \<or> (qs = [] \<and> weak_wf_pathlist ps) \<or> 
     (weak_wf_pathlist ps \<and> weak_wf_pathlist qs \<and> pathfinish (last ps) = pathstart (hd qs))"
  using weak_wf_pathlist_append[of ps qs] by (cases "ps = []"; cases "qs = []") auto

lemma pathstart_joinpaths_list [simp]:
  "xs \<noteq> [] \<Longrightarrow> pathstart (joinpaths_list xs) = pathstart (hd xs)"
  by (induction xs rule: joinpaths_list.induct) auto

lemma pathfinish_joinpaths_list [simp]:
  "xs \<noteq> [] \<Longrightarrow> pathfinish (joinpaths_list xs) = pathfinish (last xs)"
  by (induction xs rule: joinpaths_list.induct) auto

lemma path_joinpaths_list [simp, intro]: "wf_pathlist xs \<Longrightarrow> path (joinpaths_list xs)"
  by (induction xs rule: joinpaths_list.induct) auto

lemma valid_path_joinpaths_list [intro]:
  "valid_path_pathlist xs \<Longrightarrow> weak_wf_pathlist xs \<Longrightarrow> valid_path (joinpaths_list xs)"
  by (induction xs rule: joinpaths_list.induct) (auto intro!: valid_path_join)

lemma path_image_joinpaths_list:
  assumes "wf_pathlist ps"
  shows   "path_image (joinpaths_list ps) = (\<Union>p\<in>set ps. path_image p)"
  using assms by (induction ps rule: wf_pathlist.induct) (auto simp: path_image_join)

lemma joinpaths_list_append:
  assumes "wf_pathlist xs" "wf_pathlist ys" "pathfinish (last xs) = pathstart (hd ys)"
  shows   "joinpaths_list (xs @ ys) \<equiv>\<^sub>p joinpaths_list xs +++ joinpaths_list ys"
proof -
  from assms(1) have "xs \<noteq> []"
    by auto
  from assms show ?thesis
  proof (induction xs arbitrary: ys rule: joinpaths_list.induct)
    case (2 p ys)
    have "ys \<noteq> []"
      using 2 by auto
    then obtain y ys' where [simp]: "ys = y # ys'"
      by (cases ys) auto
    show ?case using 2 by auto
  next
    case (3 p1 p2 ps qs)
    obtain q qs' where [simp]: "qs = q # qs'"
      using 3 by (cases qs) auto
    have "joinpaths_list ((p1 # p2 # ps) @ qs) =
          p1 +++ joinpaths_list ((p2 # ps) @ qs)"
      by simp
    also have "\<dots> \<equiv>\<^sub>p p1 +++ joinpaths_list (p2 # ps) +++ joinpaths_list qs"
      using 3 by (intro eq_paths_join eq_paths_refl 3) auto
    also have "\<dots> \<equiv>\<^sub>p (p1 +++ joinpaths_list (p2 # ps)) +++ joinpaths_list qs"
      by (intro eq_paths_join_assoc2) (use 3 in auto)
    finally show ?case
      by simp
  qed auto
qed

lemma arc_joinpaths_list_weak_wf_imp_wf:
  assumes "weak_wf_pathlist xs" "arc_joinpaths_list xs"
  shows   "wf_pathlist xs"
  using assms
  by (induction xs rule: wf_pathlist.induct) (auto intro: arc_imp_path simp: arc_joinpaths_list_def)

lemma arc_joinpaths_aux:
  assumes "wf_pathlist xs" "arc_joinpaths_list_aux xs" "\<forall>x\<in>set xs. arc x"
  shows   "arc (joinpaths_list xs)"
  using assms
proof (induction xs rule: wf_pathlist.induct)
  case (3 p q ps)
  thus ?case 
    by (fastforce intro!: arc_join simp: path_image_joinpaths_list)
qed auto

lemma arc_joinpaths_list [intro?]:
  assumes "weak_wf_pathlist xs" "arc_joinpaths_list xs"
  shows   "arc (joinpaths_list xs)"
  using assms arc_joinpaths_aux[of xs] arc_joinpaths_list_weak_wf_imp_wf[of xs]
  by (auto simp: arc_joinpaths_list_def)

lemma simple_joinpaths_list_weak_wf_imp_wf:
  assumes "weak_wf_pathlist xs" "simple_joinpaths_list xs"
  shows   "wf_pathlist xs"
  using arc_joinpaths_list_weak_wf_imp_wf[of "tl xs"] assms
  by (cases xs rule: simple_joinpaths_list.cases)
     (auto dest: simple_path_imp_path arc_imp_path simp: arc_joinpaths_list_def)

lemma simple_path_joinpaths_list [intro?]:
  assumes "weak_wf_pathlist xs" "simple_joinpaths_list xs"
  shows   "simple_path (joinpaths_list xs)"
proof (cases xs rule: simple_joinpaths_list.cases)
  case (3 p q)
  thus ?thesis using assms
    by (force split: if_splits intro!: simple_path_joinI)
next
  case (4 p q r rs)
  define rs' where "rs' = r # rs"
  have [simp]: "rs' \<noteq> []"
    by (auto simp: rs'_def)
  have [simp]: "xs = p # q # rs'"
    by (simp add: 4 rs'_def)
  note [simp] = wf_pathlist_Cons

  have "simple_path (p +++ joinpaths_list (q # rs'))"
  proof (rule simple_path_joinI)
    show "arc p" 
      using assms by auto
  next
    show "arc (joinpaths_list (q # rs'))" using assms
      by (intro arc_joinpaths_list) (auto split: if_splits simp: arc_joinpaths_list_def)
  next
    have *: "set rs' = insert (last rs') (set (butlast rs'))"
      by (subst append_butlast_last_id [symmetric]) (auto simp del: append_butlast_last_id)
    have "wf_pathlist (q # rs')"
      using assms arc_joinpaths_list_weak_wf_imp_wf[of "q # rs'"]
      by (auto simp: arc_joinpaths_list_def)
    thus "path_image p \<inter> path_image (joinpaths_list (q # rs'))
            \<subseteq> insert (pathstart (joinpaths_list (q # rs')))
           (if pathstart p = pathfinish (joinpaths_list (q # rs')) then {pathstart p} else {})"
      using assms by (subst path_image_joinpaths_list) (auto simp: *)
  qed (use assms in auto)
  thus ?thesis
    by (simp add: rs'_def)
qed (use assms in auto)

lemma wf_pathlist_sublist:
  assumes "wf_pathlist ys" "sublist xs ys" "xs \<noteq> []"
  shows   "wf_pathlist xs"
proof -
  from assms(2) obtain as bs where *: "ys = as @ xs @ bs"
    by (auto simp: sublist_def)
  have **: "wf_pathlist xs" if "wf_pathlist (xs @ bs)"
    using that \<open>xs \<noteq> []\<close> by (induction xs rule: wf_pathlist.induct) (auto simp: wf_pathlist_Cons)
  show ?thesis
    using assms(1) \<open>xs \<noteq> []\<close> unfolding *
    by (induction as) (auto simp: ** wf_pathlist_Cons)
qed


lemma is_subpath_joinpaths_list_append_right:
  assumes "wf_pathlist (xs @ ys)" "xs \<noteq> []"
  shows   "is_subpath (joinpaths_list xs) (joinpaths_list (xs @ ys))"
proof (cases "ys = []")
  case False
  hence "is_subpath (joinpaths_list xs) (joinpaths_list xs +++ joinpaths_list ys)"
    using assms by (intro is_subpath_joinI1 path_joinpaths_list) (auto simp: wf_pathlist_append)
  also have "eq_paths \<dots> (joinpaths_list (xs @ ys))"
    using False assms by (intro eq_paths_sym[OF joinpaths_list_append])
                         (auto simp: wf_pathlist_append)
  finally show ?thesis .
qed (use assms in auto)

lemma is_subpath_joinpaths_list_append_left:
  assumes "wf_pathlist (xs @ ys)" "ys \<noteq> []"
  shows   "is_subpath (joinpaths_list ys) (joinpaths_list (xs @ ys))"
proof (cases "xs = []")
  case False
  hence "is_subpath (joinpaths_list ys) (joinpaths_list xs +++ joinpaths_list ys)"
    using assms by (intro is_subpath_joinI2 path_joinpaths_list) (auto simp: wf_pathlist_append)
  also have "eq_paths \<dots> (joinpaths_list (xs @ ys))"
    using False assms by (intro eq_paths_sym[OF joinpaths_list_append])
                         (auto simp: wf_pathlist_append)
  finally show ?thesis .
qed (use assms in auto)

lemma is_subpath_joinpaths_list:
  assumes "wf_pathlist ys" "sublist xs ys" "xs \<noteq> []"
  shows   "is_subpath (joinpaths_list xs) (joinpaths_list ys)"
proof -
  from assms(2) obtain as bs where *: "ys = as @ xs @ bs"
    by (auto simp: sublist_def)
  have "is_subpath (joinpaths_list xs) (joinpaths_list (xs @ bs))"
    using assms by (intro is_subpath_joinpaths_list_append_right)
                   (auto simp: wf_pathlist_append' *)
  also have "is_subpath \<dots> (joinpaths_list (as @ xs @ bs))"
    using assms by (intro is_subpath_joinpaths_list_append_left)
                   (auto simp: wf_pathlist_append' *)    
  finally show ?thesis
    by (simp add: *)
qed

lemma eq_loops_joinpaths_list_append:
  assumes "wf_pathlist (xs @ ys)" "pathfinish (last (xs @ ys)) = pathstart (hd (xs @ ys))"
  shows   "eq_loops (joinpaths_list (xs @ ys)) (joinpaths_list (ys @ xs))"
proof (cases "xs = [] \<or> ys = []")
  case True
  have "xs \<noteq> [] \<or> ys \<noteq> []"
    using assms by auto
  with True show ?thesis
    using assms by auto
next
  case False
  have "eq_paths (joinpaths_list (xs @ ys)) (joinpaths_list xs +++ joinpaths_list ys)"
    using assms False by (intro joinpaths_list_append) (auto simp: wf_pathlist_append)
  also have "eq_loops \<dots> (joinpaths_list ys +++ joinpaths_list xs)"
    using assms False by (intro eq_loops_joinpaths_commute) (auto simp: wf_pathlist_append)
  also have "eq_paths \<dots> (joinpaths_list (ys @ xs))"
    using assms False
    by (intro eq_paths_sym[OF joinpaths_list_append]) (auto simp: wf_pathlist_append)
  finally show ?thesis .
qed

lemma eq_loops_rotate:
  assumes "wf_pathlist xs" "pathfinish (last xs) = pathstart (hd xs)"
  shows   "eq_loops (joinpaths_list xs) (joinpaths_list (rotate n xs))"
proof -
  define m where "m = n mod length xs"
  have "eq_loops (joinpaths_list (take m xs @ drop m xs))
                 (joinpaths_list (drop m xs @ take m xs))"
    using assms by (intro eq_loops_joinpaths_list_append) auto
  thus ?thesis
    by (simp add: m_def rotate_drop_take)
qed

lemma winding_number_joinpaths_list:
  assumes "wf_pathlist ps" "\<And>p. p \<in> set ps \<Longrightarrow> x \<notin> path_image p"
  shows   "winding_number (joinpaths_list ps) x = (\<Sum>p\<leftarrow>ps. winding_number p x)"
  using assms
proof (induction ps rule: wf_pathlist.induct)
  case (3 p q ps)
  have "winding_number (joinpaths_list (p # q # ps)) x =
        winding_number (p +++ joinpaths_list (q # ps)) x"
    by simp
  also have "\<dots> = winding_number p x + winding_number (joinpaths_list (q # ps)) x"
    using "3.prems" by (intro winding_number_join) (auto simp: path_image_joinpaths_list)
  also have "winding_number (joinpaths_list (q # ps)) x = (\<Sum>r\<leftarrow>q#ps. winding_number r x)"
    by (intro "3.IH") (use "3.prems" in auto)
  finally show ?case
    by simp
qed auto

lemma contour_integral_joinpaths_list:
  assumes "weak_wf_pathlist ps" "valid_path_pathlist ps"
          "f contour_integrable_on (joinpaths_list ps)"
  shows   "contour_integral (joinpaths_list ps) f = (\<Sum>p\<leftarrow>ps. contour_integral p f)"
  using assms
proof (induction ps rule: wf_pathlist.induct)
  case (3 p q ps)
  have wf: "wf_pathlist (p # q # ps)"
    using "3.prems" valid_path_weak_wf_pathlist_imp_wf by blast
  have int: "f contour_integrable_on (p +++ joinpaths_list (q # ps))"
    using "3.prems" by simp
  have int1: "f contour_integrable_on p"
    using contour_integrable_joinD1[OF int] "3.prems" by auto 
  have int2: "f contour_integrable_on joinpaths_list (q # ps)"
    using contour_integrable_joinD2[OF int] "3.prems" by auto

  have "contour_integral (joinpaths_list (p # q # ps)) f =
        contour_integral (p +++ joinpaths_list (q # ps)) f"
    by simp
  also have "\<dots> = contour_integral p f + contour_integral (joinpaths_list (q # ps)) f"
    using "3.prems" int1 int2 by (intro contour_integral_join) auto
  also have "contour_integral (joinpaths_list (q # ps)) f = (\<Sum>r\<leftarrow>q#ps. contour_integral r f)"
    by (intro "3.IH") (use "3.prems" int2 in auto)
  finally show ?case
    by simp
qed auto


subsection \<open>Representing a sequence of path joins as a tree\<close>

text \<open>
  To deal with the problem that path joining is not associative, we define an expression tree
  to represent all the possible different bracketings of joining \<open>n\<close> paths together.

  There is also a ``flattening'' operation to convert the tree to a list of paths, since our
  eventual goal is to show that the order does not matter (up to path equivalence).

  Well-formedness is again defined similarly to the list case.
\<close>

datatype 'a joinpaths_tree =
  Path "real \<Rightarrow> 'a" | Reverse "'a joinpaths_tree" | Join "'a joinpaths_tree" "'a joinpaths_tree"

primrec paths_joinpaths_tree :: "'a joinpaths_tree \<Rightarrow> (real \<Rightarrow> 'a) set" where
  "paths_joinpaths_tree (Path p) = {p}"
| "paths_joinpaths_tree (Reverse p) = paths_joinpaths_tree p"
| "paths_joinpaths_tree (Join l r) = paths_joinpaths_tree l \<union> paths_joinpaths_tree r"

fun start_joinpaths_tree :: "'a :: real_normed_vector joinpaths_tree \<Rightarrow> 'a"
and finish_joinpaths_tree :: "'a :: real_normed_vector joinpaths_tree \<Rightarrow> 'a" where
  "start_joinpaths_tree (Path p) = pathstart p"
| "start_joinpaths_tree (Reverse p) = finish_joinpaths_tree p"
| "start_joinpaths_tree (Join l r) = start_joinpaths_tree l"
| "finish_joinpaths_tree (Path p) = pathfinish p"
| "finish_joinpaths_tree (Reverse p) = start_joinpaths_tree p"
| "finish_joinpaths_tree (Join l r) = finish_joinpaths_tree r"

primrec eval_joinpaths_tree :: "'a :: real_normed_vector joinpaths_tree \<Rightarrow> real \<Rightarrow> 'a" where
  "eval_joinpaths_tree (Path p) = p"
| "eval_joinpaths_tree (Reverse t) = reversepath (eval_joinpaths_tree t)"
| "eval_joinpaths_tree (Join l r) = eval_joinpaths_tree l +++ eval_joinpaths_tree r"

primrec flatten_joinpaths_tree :: "'a :: real_normed_vector joinpaths_tree \<Rightarrow> (real \<Rightarrow> 'a) list" where
  "flatten_joinpaths_tree (Path p) = [p]"
| "flatten_joinpaths_tree (Reverse t) = rev (map reversepath (flatten_joinpaths_tree t))"
| "flatten_joinpaths_tree (Join l r) = flatten_joinpaths_tree l @ flatten_joinpaths_tree r"

primrec wf_joinpaths_tree :: "'a :: real_normed_vector joinpaths_tree \<Rightarrow> bool" where
  "wf_joinpaths_tree (Path p) \<longleftrightarrow> path p"
| "wf_joinpaths_tree (Reverse t) \<longleftrightarrow> wf_joinpaths_tree t"
| "wf_joinpaths_tree (Join l r) \<longleftrightarrow>
     wf_joinpaths_tree l \<and> wf_joinpaths_tree r \<and> finish_joinpaths_tree l = start_joinpaths_tree r"

primrec weak_wf_joinpaths_tree :: "'a :: real_normed_vector joinpaths_tree \<Rightarrow> bool" where
  "weak_wf_joinpaths_tree (Path p) \<longleftrightarrow> True"
| "weak_wf_joinpaths_tree (Reverse t) \<longleftrightarrow> weak_wf_joinpaths_tree t"
| "weak_wf_joinpaths_tree (Join l r) \<longleftrightarrow>
     weak_wf_joinpaths_tree l \<and> weak_wf_joinpaths_tree r \<and> finish_joinpaths_tree l = start_joinpaths_tree r"

primrec valid_path_joinpaths_tree :: "'a :: real_normed_vector joinpaths_tree \<Rightarrow> bool" where
  "valid_path_joinpaths_tree (Path p) \<longleftrightarrow> valid_path p"
| "valid_path_joinpaths_tree (Reverse p) \<longleftrightarrow> valid_path_joinpaths_tree p"
| "valid_path_joinpaths_tree (Join l r) \<longleftrightarrow>
     valid_path_joinpaths_tree l \<and> valid_path_joinpaths_tree r \<and> finish_joinpaths_tree l = start_joinpaths_tree r"

primrec arc_joinpaths_tree :: "'a :: real_normed_vector joinpaths_tree \<Rightarrow> bool" where
  "arc_joinpaths_tree (Path p) \<longleftrightarrow> arc p"
| "arc_joinpaths_tree (Reverse p) \<longleftrightarrow> arc_joinpaths_tree p"
| "arc_joinpaths_tree (Join l r) \<longleftrightarrow>
     (\<forall>l'\<in>paths_joinpaths_tree l. \<forall>r'\<in>paths_joinpaths_tree r.
          path_image l' \<inter> path_image r' \<subseteq> {finish_joinpaths_tree l}) \<and>
     arc_joinpaths_tree l \<and> arc_joinpaths_tree r"

primrec simple_joinpaths_tree :: "'a :: real_normed_vector joinpaths_tree \<Rightarrow> bool" where
  "simple_joinpaths_tree (Path p) \<longleftrightarrow> simple_path p"
| "simple_joinpaths_tree (Reverse t) \<longleftrightarrow> simple_joinpaths_tree t"
| "simple_joinpaths_tree (Join l r) \<longleftrightarrow> 
     (\<forall>l'\<in>paths_joinpaths_tree l. \<forall>r'\<in>paths_joinpaths_tree r.
        path_image l' \<inter> path_image r' \<subseteq>
           {finish_joinpaths_tree l} \<union> ({start_joinpaths_tree l} \<inter> {finish_joinpaths_tree r})) \<and>
     arc_joinpaths_tree l \<and> arc_joinpaths_tree r"

lemma flatten_joinpaths_tree_nonempty [simp]: "flatten_joinpaths_tree t \<noteq> []"
  by (induction t) auto



lemma pathstart_eval_joinpaths_tree [simp]: "pathstart (eval_joinpaths_tree t) = start_joinpaths_tree t"
  and pathfinish_eval_joinpaths_tree [simp]: "pathfinish (eval_joinpaths_tree t) = finish_joinpaths_tree t"
  by (induction t) auto

lemma pathstart_last_flatten_joinpaths_tree [simp]:
        "pathstart (hd (flatten_joinpaths_tree t)) = start_joinpaths_tree t" (is ?th1)
  and pathfinish_last_flatten_joinpaths_tree [simp]:
        "pathfinish (last (flatten_joinpaths_tree t)) = finish_joinpaths_tree t" (is ?th2)
  by (induction t and t rule: start_joinpaths_tree_finish_joinpaths_tree.induct)
     (auto simp: hd_rev last_rev hd_map last_map)

lemma wf_pathlist_map_rev [simp]: "wf_pathlist (map reversepath xs) \<longleftrightarrow> wf_pathlist (rev xs)"
  by (induction xs) (auto simp: wf_pathlist_Cons hd_map wf_pathlist_append' last_rev)

lemma weak_wf_pathlist_map_rev' [simp]: "weak_wf_pathlist (map reversepath xs) \<longleftrightarrow> weak_wf_pathlist (rev xs)"
  by (induction xs) (auto simp: weak_wf_pathlist_Cons weak_wf_pathlist_append' last_rev rev_map hd_map)

lemma weak_wf_pathlist_map_rev [simp]: "weak_wf_pathlist (rev (map reversepath xs)) \<longleftrightarrow> weak_wf_pathlist xs"
  by (induction xs) (auto simp: weak_wf_pathlist_Cons weak_wf_pathlist_append' last_rev rev_map hd_map last_map)

lemma wf_pathlist_map_rev' [simp]: "wf_pathlist (rev (map reversepath xs)) \<longleftrightarrow> wf_pathlist xs"
  by (induction xs) (auto simp: wf_pathlist_Cons hd_map wf_pathlist_append' last_rev)

lemma wf_pathlist_flatten_pathree [simp]: "wf_pathlist (flatten_joinpaths_tree t) \<longleftrightarrow> wf_joinpaths_tree t"
  by (induction t) (auto simp: wf_pathlist_append rev_map)

lemma weak_wf_pathlist_flatten_pathree [simp]:
  "weak_wf_pathlist (flatten_joinpaths_tree t) \<longleftrightarrow> weak_wf_joinpaths_tree t"
  by (induction t) (auto simp: weak_wf_pathlist_append)

lemma reversepath_joinpaths_list:
  assumes "wf_pathlist xs"
  shows   "reversepath (joinpaths_list xs) \<equiv>\<^sub>p joinpaths_list (rev (map reversepath xs))"
  using assms
proof (induction xs rule: wf_pathlist.induct)
  case (3 p q ps)
  have "reversepath (joinpaths_list (p # q # ps)) =
        reversepath (joinpaths_list (q # ps)) +++ reversepath p"
    using 3 by (simp_all add: reversepath_joinpaths)
  also have "\<dots> \<equiv>\<^sub>p joinpaths_list (rev (map reversepath (q # ps))) +++ reversepath p"
    using 3 by (intro eq_paths_join) auto
  also have "\<dots> = joinpaths_list (rev (map reversepath (q # ps))) +++ joinpaths_list [reversepath p]"
    by simp
  also have "\<dots> \<equiv>\<^sub>p joinpaths_list (rev (map reversepath (q # ps)) @ [reversepath p])"
    using 3 by (intro eq_paths_sym[OF joinpaths_list_append])
               (auto simp: wf_pathlist_append' last_rev hd_map wf_pathlist_Cons)
  finally show ?case
    by simp
qed auto

lemma joinpaths_flatten_joinpaths_tree:
  assumes "wf_joinpaths_tree t"
  shows   "eval_joinpaths_tree t \<equiv>\<^sub>p joinpaths_list (flatten_joinpaths_tree t)"
  using assms
proof (induction t)
  case (Path p)
  thus ?case by simp
next
  case (Reverse t)
  have "eval_joinpaths_tree (Reverse t) \<equiv>\<^sub>p
        reversepath (joinpaths_list (flatten_joinpaths_tree t))"
    unfolding eval_joinpaths_tree.simps using Reverse.prems
    by (intro eq_paths_reverse Reverse.IH) auto 
  also have "\<dots> \<equiv>\<^sub>p joinpaths_list (rev (map reversepath (flatten_joinpaths_tree t)))"
    by (intro reversepath_joinpaths_list) (use Reverse in auto)
  finally show ?case
    by simp
next
  case (Join l r)
  have "eval_joinpaths_tree l +++ eval_joinpaths_tree r \<equiv>\<^sub>p
          joinpaths_list (flatten_joinpaths_tree l) +++ joinpaths_list (flatten_joinpaths_tree r)"
    using Join by (intro eq_paths_join) auto
  also have "\<dots> \<equiv>\<^sub>p joinpaths_list (flatten_joinpaths_tree l @ flatten_joinpaths_tree r)"
    by (rule eq_paths_sym[OF joinpaths_list_append]) (use Join in auto)
  finally show ?case
    by simp
qed

lemma valid_path_joinpaths_tree:
  fixes t :: "'a :: real_normed_field joinpaths_tree"
  shows "valid_path_joinpaths_tree t \<Longrightarrow> valid_path (eval_joinpaths_tree t)"
  by (induction t) auto

lemma path_image_eval_joinpaths_tree:
  "wf_joinpaths_tree t \<Longrightarrow>
     path_image (eval_joinpaths_tree t) = (\<Union>p\<in>paths_joinpaths_tree t. path_image p)"
  by (induction t) (auto simp: path_image_join)

lemma arc_joinpaths_tree [intro?]:
  "wf_joinpaths_tree t \<Longrightarrow> arc_joinpaths_tree t \<Longrightarrow> arc (eval_joinpaths_tree t)"
  by (induction t) (auto simp: arc_join_eq path_image_eval_joinpaths_tree intro!: arc_reversepath)

lemma simple_joinpaths_tree [intro?]:
  "wf_joinpaths_tree t \<Longrightarrow> simple_joinpaths_tree t \<Longrightarrow> simple_path (eval_joinpaths_tree t)"
  by (induction t)
    (fastforce intro!: simple_path_joinI arc_joinpaths_tree split: if_splits
               simp: path_image_eval_joinpaths_tree simple_path_reversepath_iff)+


subsection \<open>Equivalence of two join trees\<close>

text \<open>
  Two trees are considered equivalent if they flatten to the same list of paths.
  Equivalence implies that one tree is well-formed if and only if the other one is as well,
  and in that case that their evaluations are equivalent paths.
\<close>

definition equiv_joinpaths_tree ::
  "('a :: real_normed_vector joinpaths_tree) \<Rightarrow> 'a joinpaths_tree \<Rightarrow> bool" where
  "equiv_joinpaths_tree t1 t2 \<longleftrightarrow> flatten_joinpaths_tree t1 = flatten_joinpaths_tree t2"

lemma equiv_joinpaths_tree_imp_wf_iff:
  "equiv_joinpaths_tree t1 t2 \<Longrightarrow> wf_joinpaths_tree t1 \<longleftrightarrow> wf_joinpaths_tree t2"
  by (metis equiv_joinpaths_tree_def wf_pathlist_flatten_pathree)

lemma equiv_joinpaths_tree_imp_eval_eq:
  "equiv_joinpaths_tree t1 t2 \<Longrightarrow> wf_joinpaths_tree t1 \<Longrightarrow>
     eval_joinpaths_tree t1 \<equiv>\<^sub>p eval_joinpaths_tree t2"
  by (metis eq_paths_sym eq_paths_trans equiv_joinpaths_tree_def
            equiv_joinpaths_tree_imp_wf_iff joinpaths_flatten_joinpaths_tree)



subsection \<open>Implementation\<close>

named_theorems path_automation_simps
named_theorems path_automation_intros


text \<open>
  The following allows us to reify an expression containing join operations into a tree.
  One might be able to incorporate path reversal as well.
\<close>

definition REIFY_JOINPATHS_TAG where "REIFY_JOINPATHS_TAG x = x"

lemma REIFY_JOINPATHS_TAG:
  "REIFY_JOINPATHS_TAG (x :: real \<Rightarrow> 'a :: real_normed_vector) = y \<Longrightarrow> x = y"
  by (simp add: REIFY_JOINPATHS_TAG_def)

named_theorems reify_joinpath_tree

lemma reify_joinpaths_tree [reify_joinpath_tree]:
  "REIFY_JOINPATHS_TAG (reversepath p) = reversepath (REIFY_JOINPATHS_TAG p)"
  "REIFY_JOINPATHS_TAG (p +++ q) = REIFY_JOINPATHS_TAG p +++ REIFY_JOINPATHS_TAG q"
  "REIFY_JOINPATHS_TAG p = eval_joinpaths_tree (Path p)"
  "eval_joinpaths_tree l +++ eval_joinpaths_tree r = eval_joinpaths_tree (Join l r)"
  "reversepath (eval_joinpaths_tree t) = eval_joinpaths_tree (Reverse t)"
  by (simp_all add: REIFY_JOINPATHS_TAG_def)


lemma path_via_joinpaths_tree [path_automation_intros]:
  assumes "REIFY_JOINPATHS_TAG p = eval_joinpaths_tree t"
  assumes "wf_joinpaths_tree t"
  shows   "path p"
  using assms joinpaths_flatten_joinpaths_tree[of t] by (auto simp: REIFY_JOINPATHS_TAG_def)

lemma valid_path_via_joinpaths_tree [path_automation_intros]:
  fixes p :: "real \<Rightarrow> 'a :: real_normed_field"
  assumes "REIFY_JOINPATHS_TAG p = eval_joinpaths_tree t"
  assumes "valid_path_joinpaths_tree t"
  shows   "valid_path p"
  using assms valid_path_joinpaths_tree[of t] by (auto simp: REIFY_JOINPATHS_TAG_def)

lemma arc_via_joinpaths_tree [path_automation_intros]:
  assumes "REIFY_JOINPATHS_TAG p = eval_joinpaths_tree t"
  assumes "arc_joinpaths_list (flatten_joinpaths_tree t) \<and> weak_wf_joinpaths_tree t"
  shows   "arc p"
proof -
  have wf: "wf_joinpaths_tree t"
    using arc_joinpaths_list_weak_wf_imp_wf[of "flatten_joinpaths_tree t"] assms
    by auto
  have "arc (joinpaths_list (flatten_joinpaths_tree t))"
    using assms by (intro arc_joinpaths_list) auto
  moreover have "eval_joinpaths_tree t \<equiv>\<^sub>p joinpaths_list (flatten_joinpaths_tree t)"
    using wf by (intro joinpaths_flatten_joinpaths_tree) auto
  ultimately show ?thesis
    using assms eq_paths_imp_arc_iff unfolding REIFY_JOINPATHS_TAG_def by metis
qed

lemma simple_path_via_joinpaths_tree [path_automation_intros]:
  assumes "REIFY_JOINPATHS_TAG p = eval_joinpaths_tree t"
  assumes "simple_joinpaths_list (flatten_joinpaths_tree t) \<and> weak_wf_joinpaths_tree t"
  shows   "simple_path p"
proof -
  have wf: "wf_joinpaths_tree t"
    using simple_joinpaths_list_weak_wf_imp_wf[of "flatten_joinpaths_tree t"] assms
    by auto
  have "simple_path (joinpaths_list (flatten_joinpaths_tree t))"
    using assms by (intro simple_path_joinpaths_list) auto
  moreover have "eval_joinpaths_tree t \<equiv>\<^sub>p joinpaths_list (flatten_joinpaths_tree t)"
    using wf by (intro joinpaths_flatten_joinpaths_tree) auto
  ultimately show ?thesis
    using assms eq_paths_imp_simple_path_iff unfolding REIFY_JOINPATHS_TAG_def by metis
qed

lemma eq_paths_via_reify_joinpaths [path_automation_intros]:
  assumes "REIFY_JOINPATHS_TAG p = eval_joinpaths_tree t1"
  assumes "REIFY_JOINPATHS_TAG q = eval_joinpaths_tree t2"
  assumes "wf_joinpaths_tree t1 \<and> wf_joinpaths_tree t2 \<and> 
           flatten_joinpaths_tree t1 = flatten_joinpaths_tree t2"
  shows   "eq_paths p q"
  using assms unfolding REIFY_JOINPATHS_TAG_def
  by (simp add: equiv_joinpaths_tree_def equiv_joinpaths_tree_imp_eval_eq)

definition is_rotation_of :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
  "is_rotation_of xs ys \<longleftrightarrow> (\<exists>n. xs = rotate n ys)"

fun is_rotation_of_aux :: "'a list \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> bool" where
  "is_rotation_of_aux xs ys 0 \<longleftrightarrow> False"
| "is_rotation_of_aux xs [] _ \<longleftrightarrow> xs = []"
| "is_rotation_of_aux xs (y # ys) (Suc n) \<longleftrightarrow>
    xs = y # ys \<or> is_rotation_of_aux xs (ys @ [y]) n"

lemma is_rotation_of_aux_correct: "is_rotation_of_aux xs ys n \<longleftrightarrow> (\<exists>k<n. xs = rotate k ys)"
proof (induction xs ys n rule: is_rotation_of_aux.induct)
  case (3 xs y ys n)
  show ?case
  proof
    assume "is_rotation_of_aux xs (y # ys) (Suc n)"
    hence "xs = y # ys \<or> is_rotation_of_aux xs (ys @ [y]) n"
      by auto
    thus "\<exists>k<Suc n. xs = rotate k (y # ys)"
    proof
      assume "xs = y # ys"
      thus ?thesis
        by (intro exI[of _ 0]) auto
    next
      assume "is_rotation_of_aux xs (ys @ [y]) n"
      with 3 obtain k where "k < n" "xs = rotate k (ys @ [y])"
        by blast
      thus "\<exists>k<Suc n. xs = rotate k (y # ys)"
        by (intro exI[of _ "Suc k"]) (auto simp: rotate1_rotate_swap)
    qed
  next
    assume "\<exists>k<Suc n. xs = rotate k (y # ys)"
    then obtain k where k: "k < Suc n" "xs = rotate k (y # ys)"
      by blast
    show "is_rotation_of_aux xs (y # ys) (Suc n)"
    proof (cases k)
      case 0
      with k show ?thesis by simp
    next
      case (Suc k')
      with k have "k' < n" "xs = rotate k' (ys @ [y])"
        by (simp_all add: rotate1_rotate_swap)
      with 3 have "is_rotation_of_aux xs (ys @ [y]) n"
        by blast
      thus ?thesis by simp
    qed
  qed
qed auto

lemma is_rotation_of_code [code]:
  "is_rotation_of xs ys \<longleftrightarrow> length xs = length ys \<and> (xs = [] \<or> is_rotation_of_aux xs ys (length xs))"
proof (intro iffI conjI)
  assume "is_rotation_of xs ys"
  then obtain n where n: "xs = rotate n ys"
    by (auto simp: is_rotation_of_def)
  also have "rotate n ys = rotate (n mod length ys) ys"
    by (simp add: rotate_drop_take)
  also have "length ys = length xs"
    by (simp add: n)
  finally have "xs = rotate (n mod length xs) ys"
    by simp
  moreover have "n mod length xs < length xs" if "xs \<noteq> []"
    using that by auto
  ultimately show "xs = [] \<or> is_rotation_of_aux xs ys (length xs)"
    unfolding is_rotation_of_aux_correct by blast
qed (auto simp: is_rotation_of_def is_rotation_of_aux_correct)

lemma eq_loops_via_reify_joinpaths [path_automation_intros]:
  assumes "REIFY_JOINPATHS_TAG p = eval_joinpaths_tree t1"
  assumes "REIFY_JOINPATHS_TAG q = eval_joinpaths_tree t2"
  assumes "wf_joinpaths_tree t1 \<and> wf_joinpaths_tree t2 \<and> 
           finish_joinpaths_tree t2 = start_joinpaths_tree t2 \<and>
           is_rotation_of (flatten_joinpaths_tree t1) (flatten_joinpaths_tree t2)"
  shows   "eq_loops p q"
proof -
  from assms obtain n where n: "flatten_joinpaths_tree t1 = rotate n (flatten_joinpaths_tree t2)"
    unfolding is_rotation_of_def by blast
  have "eq_paths (eval_joinpaths_tree t2) (joinpaths_list (flatten_joinpaths_tree t2))"
    using assms eq_paths_sym_iff joinpaths_flatten_joinpaths_tree by blast
  also have "eq_loops \<dots> (joinpaths_list (flatten_joinpaths_tree t1))"
    unfolding n by (intro eq_loops_rotate) (use assms in auto)
  also have "eq_paths \<dots> (eval_joinpaths_tree t1)"
    using assms eq_paths_sym_iff joinpaths_flatten_joinpaths_tree by blast
  finally show ?thesis
    using assms by (simp add: eq_loops_sym_iff REIFY_JOINPATHS_TAG_def)
qed

lemma is_subpath_via_reify_joinpaths [path_automation_intros]:
  assumes "REIFY_JOINPATHS_TAG p = eval_joinpaths_tree t1"
  assumes "REIFY_JOINPATHS_TAG q = eval_joinpaths_tree t2"
  assumes "wf_joinpaths_tree t1 \<and> wf_joinpaths_tree t2 \<and>
           sublist (flatten_joinpaths_tree t1) (flatten_joinpaths_tree t2)"
  shows   "is_subpath p q"
  using assms unfolding REIFY_JOINPATHS_TAG_def
  by (meson eq_paths_sym flatten_joinpaths_tree_nonempty is_subpath_eq_paths_trans
       is_subpath_joinpaths_list joinpaths_flatten_joinpaths_tree wf_pathlist_flatten_pathree)

lemma sum_list_singleton: "sum_list [x] = x"
  by simp

lemma sum_list_Cons_rev: "sum_list (x # y # xs) = sum_list (y # xs) + (x :: 'a :: comm_monoid_add)"
  by (simp add: add_ac)

lemma winding_number_via_joinpaths [path_automation_intros]:
  assumes "REIFY_JOINPATHS_TAG p = eval_joinpaths_tree t"
  assumes "(\<Sum>q\<leftarrow>rev (flatten_joinpaths_tree t). winding_number q x) = T \<and> 
           (\<forall>p\<in>set (flatten_joinpaths_tree t). x \<notin> path_image p) \<and>
           weak_wf_joinpaths_tree t \<and> valid_path_pathlist (flatten_joinpaths_tree t)"
  shows   "winding_number p x = T"
proof -
  have wf: "wf_joinpaths_tree t"
    using assms valid_path_weak_wf_pathlist_imp_wf weak_wf_pathlist_flatten_pathree
          wf_pathlist_flatten_pathree by blast
  have "p \<equiv>\<^sub>p joinpaths_list (flatten_joinpaths_tree t)"
    using assms wf unfolding REIFY_JOINPATHS_TAG_def
    by (metis joinpaths_flatten_joinpaths_tree)
  hence "winding_number p x = winding_number (joinpaths_list (flatten_joinpaths_tree t)) x"
    using assms wf by (intro eq_paths_imp_winding_number_eq) (auto simp: path_image_joinpaths_list)
  also have "\<dots> = (\<Sum>p\<leftarrow>flatten_joinpaths_tree t. winding_number p x)"
    using wf assms by (subst winding_number_joinpaths_list) auto
  finally show ?thesis using assms by (simp flip: rev_map)
qed

lemma valid_path_pathlist_flatten_imp_valid_path_eval_joinpaths_tree:
  assumes "weak_wf_pathlist (flatten_joinpaths_tree t)"
  assumes "valid_path_pathlist (flatten_joinpaths_tree t)"
  shows   "valid_path (eval_joinpaths_tree t)"
  using assms
  by (induction t)
     (auto intro!: valid_path_join simp: valid_path_pathlist_altdef
                   weak_wf_pathlist_append list.pred_map o_def)

lemma path_image_eval_joinpaths_tree':
  assumes "wf_joinpaths_tree t"
  shows   "path_image (eval_joinpaths_tree t) = (\<Union>p\<in>set (flatten_joinpaths_tree t). path_image p)"
  using assms by (induction t) (simp_all add: path_image_join) 


lemma contour_integral_via_joinpaths [path_automation_intros]:
  assumes "REIFY_JOINPATHS_TAG p = eval_joinpaths_tree t"
  assumes "(\<Sum>q\<leftarrow>rev (flatten_joinpaths_tree t). contour_integral q f) = T \<and>
           f analytic_on (path_image p) \<and>
           weak_wf_joinpaths_tree t \<and> valid_path_pathlist (flatten_joinpaths_tree t)"
  shows   "contour_integral p f = T"
proof -
  have valid: "valid_path (eval_joinpaths_tree t)"
    by (intro valid_path_pathlist_flatten_imp_valid_path_eval_joinpaths_tree) (use assms in auto)
  have wf: "wf_joinpaths_tree t"
    using assms valid_path_weak_wf_pathlist_imp_wf weak_wf_pathlist_flatten_pathree
          wf_pathlist_flatten_pathree by blast
  have int: "f contour_integrable_on joinpaths_list (flatten_joinpaths_tree t)"
    using assms wf path_image_eval_joinpaths_tree'[OF wf]
    by (intro analytic_imp_contour_integrable valid_path_joinpaths_list)
       (auto simp: path_image_joinpaths_list REIFY_JOINPATHS_TAG_def)
  have eq: "p \<equiv>\<^sub>p joinpaths_list (flatten_joinpaths_tree t)"
    using assms wf unfolding REIFY_JOINPATHS_TAG_def
    by (metis joinpaths_flatten_joinpaths_tree)
  moreover have "f analytic_on path_image (eval_joinpaths_tree t) \<inter> \<Union> (path_image ` set (flatten_joinpaths_tree t))"
  proof (rule analytic_on_subset[of f "path_image p"])
    have "path_image (eval_joinpaths_tree t) = path_image p"
      using assms by (simp add: path_image_joinpaths_list REIFY_JOINPATHS_TAG_def)
    thus "path_image (eval_joinpaths_tree t) \<inter> \<Union> (path_image ` set (flatten_joinpaths_tree t))
            \<subseteq> path_image p" by simp
  qed (use assms in auto)
  ultimately have "contour_integral p f = contour_integral (joinpaths_list (flatten_joinpaths_tree t)) f"
    using assms wf valid
    by (intro eq_paths_imp_contour_integral_eq)
       (auto simp: path_image_joinpaths_list REIFY_JOINPATHS_TAG_def)
  also have "\<dots> = (\<Sum>p\<leftarrow>flatten_joinpaths_tree t. contour_integral p f)"
    using wf assms int by (subst contour_integral_joinpaths_list) auto
  finally show ?thesis 
    using assms by (simp flip: rev_map)
qed

text \<open>
  The following is an alternative way to split contour integrals that uses holomorphicity
  w.r.t.\ a user-defined region rather than analyticity on the path. This may sometimes be
  more convenient.
\<close>
lemma contour_integral_via_joinpaths_holo:
  assumes "REIFY_JOINPATHS_TAG p = eval_joinpaths_tree t"
  assumes "(\<Sum>q\<leftarrow>rev (flatten_joinpaths_tree t). contour_integral q f) = T \<and>
           f holomorphic_on A \<and> open A \<and> path_image p \<subseteq> A \<and>
           weak_wf_joinpaths_tree t \<and> valid_path_pathlist (flatten_joinpaths_tree t)"
  shows   "contour_integral p f = T"
proof (rule contour_integral_via_joinpaths[of _ t], goal_cases)
  case 2
  from assms have "f holomorphic_on A" "open A" "path_image p \<subseteq> A"
    by blast+
  hence "f analytic_on path_image p"
    using analytic_on_holomorphic by blast
  with assms show ?case
    by blast
qed fact+


fun unions_list :: "('a \<Rightarrow> 'b set) \<Rightarrow> 'a list \<Rightarrow> 'b set" where
  "unions_list f [] = {}"
| "unions_list f [x] = f x"
| "unions_list f (x # xs) = f x \<union> unions_list f xs"

lemma unions_list_eq: "unions_list f xs = (\<Union>x\<in>set xs. f x)"
  by (induction f xs rule: unions_list.induct) auto

lemma path_image_via_joinpaths [path_automation_intros]:
  assumes "REIFY_JOINPATHS_TAG p = eval_joinpaths_tree t"
  assumes "wf_joinpaths_tree t \<and> unions_list path_image (flatten_joinpaths_tree t) = T"
  shows   "path_image p = T"
proof -
  have "path_image p = path_image (eval_joinpaths_tree t)"
    using assms by (simp add: REIFY_JOINPATHS_TAG_def)
  also have "\<dots> = path_image (joinpaths_list (flatten_joinpaths_tree t))"
    by (intro eq_paths_imp_path_image_eq joinpaths_flatten_joinpaths_tree) (use assms in auto)
  also have "\<dots> = (\<Union>x\<in>set (flatten_joinpaths_tree t). path_image x)"
    by (subst path_image_joinpaths_list) (use assms in auto)
  also have "\<dots> = unions_list path_image (flatten_joinpaths_tree t)"
    by (rule unions_list_eq [symmetric])
  finally show ?thesis
    using assms by auto
qed

lemma path_image_subset_via_joinpaths [path_automation_intros]:
  assumes "REIFY_JOINPATHS_TAG p = eval_joinpaths_tree t"
  assumes "wf_joinpaths_tree t \<and> list_all (\<lambda>p. path_image p \<subseteq> T) (flatten_joinpaths_tree t)"
  shows   "path_image p \<subseteq> T"
proof -
  have "path_image p = path_image (eval_joinpaths_tree t)"
    using assms by (simp add: REIFY_JOINPATHS_TAG_def)
  also have "\<dots> = path_image (joinpaths_list (flatten_joinpaths_tree t))"
    by (intro eq_paths_imp_path_image_eq joinpaths_flatten_joinpaths_tree) (use assms in auto)
  also have "\<dots> = (\<Union>x\<in>set (flatten_joinpaths_tree t). path_image x)"
    by (subst path_image_joinpaths_list) (use assms in auto)
  finally show ?thesis
    using assms by (auto simp: list.pred_set)
qed

lemma not_in_path_image_via_joinpaths [path_automation_intros]:
  assumes "REIFY_JOINPATHS_TAG p = eval_joinpaths_tree t"
  assumes "wf_joinpaths_tree t \<and> list_all (\<lambda>p. x \<notin> path_image p) (flatten_joinpaths_tree t)"
  shows   "x \<notin> path_image p"
  using path_image_subset_via_joinpaths[of p t "-{x}"] assms by auto

lemma list_all_singleton_iff: "list_all P [x] \<longleftrightarrow> P x"
  by auto
  
lemmas [path_automation_simps] =
  flatten_joinpaths_tree.simps simple_joinpaths_list.simps weak_wf_joinpaths_tree.simps
  append.simps list.sel last.simps butlast.simps list.simps if_False if_True refl
  arc_joinpaths_list_aux.simps arc_joinpaths_list_def ball_simps HOL.simp_thms
  start_joinpaths_tree.simps finish_joinpaths_tree.simps wf_joinpaths_tree.simps
  valid_path_joinpaths_tree.simps sublist_code prefix_code is_rotation_of_code
  is_rotation_of_aux.simps list.size add_Suc_right plus_nat.add_Suc add_0_right add_0_left
  pathstart_linepath pathfinish_linepath pathstart_part_circlepath' pathfinish_part_circlepath'
  pathstart_circlepath pathfinish_circlepath pathstart_rectpath pathfinish_rectpath
  path_linepath path_part_circlepath path_circlepath path_rectpath
  valid_path_linepath valid_path_part_circlepath valid_path_circlepath valid_path_rectpath
  simple_path_part_circlepath simple_path_circlepath sum_list_Cons_rev sum_list_singleton list.map
  valid_path_pathlist.simps rev.simps reversepath_linepath reversepath_part_circlepath
  reversepath_circlepath unions_list.simps path_image_linepath path_image_circlepath
  list.pred_inject(1) list_all_singleton_iff list.pred_inject(2)[of P x "y # xs" for P x y xs]

lemma arc_linepath_iff [path_automation_simps]: "arc (linepath a b) \<longleftrightarrow> a \<noteq> b"
proof
  assume "arc (linepath a b)"
  thus "a \<noteq> b"
    by (smt (verit, best) arcD atLeastAtMost_iff linepath_0' linepath_1')
qed auto

lemma simple_path_linepath_iff [path_automation_simps]: "simple_path (linepath a b) \<longleftrightarrow> a \<noteq> b"
proof
  assume "simple_path (linepath a b)"
  thus "a \<noteq> b"
    by (metis linepath_1' simple_path_subpath_eq subpath_refl)
qed auto

lemma arc_part_circlepath_iff [path_automation_simps]:
  "arc (part_circlepath x r a b) \<longleftrightarrow> r \<noteq> 0 \<and> a \<noteq> b \<and> \<bar>a - b\<bar> < 2 * pi"
proof (intro iffI conjI)
  assume *: "arc (part_circlepath x r a b)"
  show "r \<noteq> 0"
    using * by (auto simp: arc_linepath_iff)
  show "a \<noteq> b"
    using * by (auto simp: part_circlepath_empty arc_linepath_iff)
  show "\<bar>a - b\<bar> < 2 * pi"
  proof (rule ccontr)
    assume **: "\<not>\<bar>a - b\<bar> < 2 * pi"
    hence "a \<noteq> b"
      by auto
    have "part_circlepath x r a b (2 * pi / \<bar>a - b\<bar>) = 
            x + rcis r ((1 - 2 * pi / \<bar>a - b\<bar>) * a + 2 * pi * b / \<bar>a - b\<bar>)"
      by (simp add: part_circlepath_altdef linepath_def)
    also have "(1 - 2 * pi / \<bar>a - b\<bar>) * a + 2 * pi * b / \<bar>a - b\<bar> = a + sgn (b - a) * 2 * pi"
      using ** \<open>a \<noteq> b\<close> by (auto simp: divide_simps) (auto simp: field_simps abs_if split: if_splits)?
    also have "x + rcis r (a + sgn (b - a) * 2 * pi) = part_circlepath x r a b 0"
      by (simp add: part_circlepath_altdef linepath_def rcis_def sgn_if flip: cis_mult cis_cnj)
    finally have "part_circlepath x r a b (2 * pi / \<bar>a - b\<bar>) = part_circlepath x r a b 0" .
    moreover have "0 \<in> {0..(1::real)}" 
      by simp
    moreover have "2 * pi / \<bar>a - b\<bar> \<in> {0..1}"
      using ** \<open>a \<noteq> b\<close> by (auto simp: field_simps)
    ultimately show False
      using arcD[OF *, of 0 "2 * pi / \<bar>a - b\<bar>"] \<open>a \<noteq> b\<close> by fastforce
  qed
qed (auto intro!: arc_part_circlepath)

lemma arc_circlepath_iff [path_automation_simps]: "arc (circlepath x r) \<longleftrightarrow> False"
  unfolding circlepath_def arc_part_circlepath_iff by auto



named_theorems path_automation_unfolds

ML \<open>
signature PATH_REIFY = sig
  val do_path_reify_tac : Proof.context -> int -> tactic
  val path_reify_tac : Proof.context -> int -> tactic
  val tac : Proof.context -> int -> tactic
end


structure Path_Reify : PATH_REIFY = struct

val intros = \<^named_theorems>\<open>path_automation_intros\<close>
val simps = \<^named_theorems>\<open>path_automation_simps\<close>
val reifies = \<^named_theorems>\<open>reify_joinpath_tree\<close>
val unfolds = \<^named_theorems>\<open>path_automation_unfolds\<close>

fun do_path_reify_tac ctxt i =
  let 
    val thms = Named_Theorems.get ctxt reifies
  in
    REPEAT (EqSubst.eqsubst_tac ctxt [0] thms i) THEN resolve_tac ctxt @{thms HOL.refl} i
  end

local

fun tac {context = ctxt, concl, ...} =
    case Thm.term_of concl of
      \<^const>\<open>Trueprop\<close> $ (Const (\<^const_name>\<open>HOL.eq\<close>, _) $ 
         (Const (\<^const_name>\<open>REIFY_JOINPATHS_TAG\<close>, _) $ _) $ _) =>
        HEADGOAL (do_path_reify_tac ctxt)
    | _ => all_tac

in

val path_reify_tac = Subgoal.FOCUS_PARAMS tac

end


local

fun tac' {context = ctxt, ...} = 
  let
    val intros = Named_Theorems.get ctxt intros
    val simps = Named_Theorems.get ctxt simps
    val unfolds = Named_Theorems.get ctxt unfolds
    val ctxt' = put_simpset HOL_basic_ss ctxt addsimps simps
  in
    Local_Defs.unfold_tac ctxt unfolds
    THEN HEADGOAL (
      resolve_tac ctxt intros
      THEN_ALL_NEW DETERM o path_reify_tac ctxt
      THEN_ALL_NEW DETERM o Simplifier.simp_tac ctxt'
      THEN_ALL_NEW (TRY o REPEAT_ALL_NEW (DETERM o resolve_tac ctxt @{thms conjI}))
    )
    THEN distinct_subgoals_tac
    THEN Local_Defs.fold_tac ctxt unfolds
  end

val sections =
  Method.sections
    [
     Args.add -- Args.colon >> K (Method.modifier (Named_Theorems.add intros) \<^here>),
     Args.del -- Args.colon >> K (Method.modifier (Named_Theorems.del intros) \<^here>),
     Args.$$$ "simp" -- Args.add -- Args.colon >> K (Method.modifier (Named_Theorems.add simps) \<^here>),
     Args.$$$ "simp" -- Args.colon >> K (Method.modifier (Named_Theorems.add simps) \<^here>),
     Args.$$$ "simp" -- Args.del -- Args.colon >> K (Method.modifier (Named_Theorems.del simps) \<^here>),
     Args.$$$ "defs" -- Args.add -- Args.colon >> K (Method.modifier (Named_Theorems.add unfolds) \<^here>),
     Args.$$$ "defs" -- Args.colon >> K (Method.modifier (Named_Theorems.add unfolds) \<^here>),
     Args.$$$ "defs" -- Args.del -- Args.colon >> K (Method.modifier (Named_Theorems.del unfolds) \<^here>)
    ]

in

val tac = Subgoal.FOCUS_PARAMS tac'
val method = sections >> K (SIMPLE_METHOD' o tac)

val _ =
  Theory.setup
   (Method.setup \<^binding>\<open>path_reify\<close> method "reification of composite paths into a path tree" #>
    Method.setup \<^binding>\<open>path\<close> method
      "automation for various common path problems, e.g. path equivalence, splitting integrals");

end

end
\<close>



subsection  \<open>Examples\<close>

text \<open>
  We now look at some concrete examples of how the method can be used.
\<close>

experiment
begin


text \<open>Showing well-formedness:\<close>
lemma "path (linepath 0 1 +++ linepath 1 (1 + \<i>) +++ linepath (1 + \<i>) 0)"
  by path

lemma "valid_path (linepath 0 1 +++ linepath 1 (1 + \<i>) +++ linepath (1 + \<i>) 0)"
  by path


text \<open>Showing that a path is simple:\<close>
lemma "arc (linepath 0 1 +++ linepath 1 (1 + \<i>) +++ linepath (1 + \<i>) \<i>)"
  apply path
         apply (auto simp: closed_segment_def complex_eq_iff)
  done

lemma "simple_path (linepath 0 1 +++ linepath 1 (1 + \<i>) +++ linepath (1 + \<i>) 0)"
  apply path
         apply (auto simp: closed_segment_def complex_eq_iff)
  done


text \<open>
  Computing the image of a composite path:
\<close>
lemma "path_image (linepath 0 (1::complex) +++ linepath 1 \<i>) = 
         closed_segment 0 1 \<union> closed_segment 1 \<i>"
  by path


text \<open>
  Showing equivalence of paths modulo associativity and reversal:
\<close>
lemma "((linepath 0 1 +++ linepath 1 2) +++ linepath 2 3) +++ linepath 3 4 \<equiv>\<^sub>p
       linepath 0 1 +++ (linepath 1 2 +++ (linepath 2 3 +++ linepath 3 4))"
  by path

lemma "linepath 0 1 +++ reversepath (linepath 3 2 +++ linepath 2 1) +++ linepath 3 4 \<equiv>\<^sub>p
       linepath 0 1 +++ (linepath 1 2 +++ (linepath 2 3 +++ linepath 3 4))"
  by path


text \<open>
  Subpath relationships can also be shown in the same fashion.
\<close>
lemma "linepath 1 2 +++ linepath 2 3 \<le>\<^sub>p
       linepath 0 1 +++ linepath 1 2 +++ linepath 2 3 +++ linepath 3 4"
  by path

lemma "linepath 0 1 +++ reversepath (linepath 3 2 +++ linepath 2 1) \<le>\<^sub>p
       linepath 0 1 +++ (linepath 1 2 +++ (linepath 2 3 +++ linepath 3 4))"
  by path


(*
  TODO: One could be a bit more clever here and solve the "sublist" thing in ML in a more
  controlled way. Similarly for eq_paths, and possibly that would also make eq_loops easier.
*)


text \<open>
  For loops, one can, in addition to reversal and associativity, also show equivalence modulo
  ``rotation''. Consider e.g.\ a counter-clockwise rectangular path and consider
  paths to be equal modular associativity. Then there are four different ways to write that path,
  corresponding to which corner we start in.

  The automation can prove automatically that all of these four paths are equivalent to one
  another (basically by brute-forcing all 4 possibilities).
\<close>
lemma "linepath 0 1 +++ linepath 1 (1 + \<i>) +++ linepath (1 + \<i>) \<i> +++ linepath \<i> 0 \<equiv>\<^sub>\<circle>
       linepath 1 (1 + \<i>) +++ linepath (1 + \<i>) \<i> +++ linepath \<i> 0 +++ linepath 0 1"
  by path



(* TODO: support reversal *)

text \<open>
  For the next few examples, we define a path consisting of three perpendicular lines.
\<close>
definition g where "g = (linepath 0 1 +++ linepath 1 (1 + \<i>) +++ linepath (1 + \<i>) \<i>)"

text \<open>
  Contour integrals on such composite paths can be split into integrals on the constituent paths.
  Since the path is often a large, unwieldy expression that is hidden behind a definition,
  one can give that definition theorem to the \emph{path} method with the \emph{defs} keyword.
  Its definition is then unfolded automatically and re-folded in any of the arising proof 
  obligations that contain the full path again, such as the analyticity condition here.
\<close>
lemma "contour_integral g (\<lambda>x. x) = -1/2"
proof (path defs: g_def)
  show "contour_integral (linepath 0 1) (\<lambda>x. x) +
        contour_integral (linepath 1 (1 + \<i>)) (\<lambda>x. x) +
        contour_integral (linepath (1 + \<i>) \<i>) (\<lambda>x. x) = - 1 / 2"
    by (simp add: field_simps)
next
  show "(\<lambda>x. x) analytic_on path_image g"
    by auto
qed


text \<open>
  Alternatively, one can also show holomorphicity on some open superset of the path's image
  instead of analyticity on exactly the path's image.
\<close>
lemma "contour_integral g (\<lambda>x. x) = -1/2"
proof (path defs: g_def del: contour_integral_via_joinpaths add: contour_integral_via_joinpaths_holo)
  show "contour_integral (linepath 0 1) (\<lambda>x. x) +
        contour_integral (linepath 1 (1 + \<i>)) (\<lambda>x. x) +
        contour_integral (linepath (1 + \<i>) \<i>) (\<lambda>x. x) = - 1 / 2"
    by (simp add: field_simps)
next
  show "(\<lambda>x. x) holomorphic_on UNIV"
    by auto
next
  show "open (UNIV :: complex set)"
    by simp
next
  text \<open>
    Conditions such as a path being a subset of some other set can also be simplified using
    the \<^emph>\<open>path\<close> method:
  \<close>
  show "path_image g \<subseteq> UNIV"
    apply (path defs: g_def)
      apply auto
    done
qed


text \<open>
  Winding numbers can be split into the winding numbers of the constituent paths in the same way
  as integrals. However, for concrete paths it is probably better to use Wenda Li's automation
  rather than this.
\<close>
lemma "winding_number g (1 / 3 + 1 / 3 * \<i>) = undefined"
  apply (path defs: g_def)
     apply (simp_all add: closed_segment_same_Re closed_segment_same_Im)
  oops

end

end