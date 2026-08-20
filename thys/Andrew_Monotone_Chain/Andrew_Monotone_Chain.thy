(*  Title:      Andrew_Monotone_Chain.thy
    Author:     Arthur Freitas Ramos
    Author:     David Barros Hulak
    Author:     Ruy J. G. B. de Queiroz
*)

section \<open>Andrew's Monotone Chain Convex Hull Algorithm\<close>

theory Andrew_Monotone_Chain
  imports
    "HOL-Analysis.Convex"
    "HOL-Analysis.Convex_Euclidean_Space"
    "HOL-Library.Product_Lexorder"
    "HOL-Library.Sublist"
begin

text \<open>
  This theory formalizes the executable core of Andrew's monotone chain
  convex hull algorithm.  Points are sorted lexicographically, duplicate
  points are removed, and two stack scans compute the lower and upper chains.
  The final hull is the usual concatenation of the two chains with their
  repeated endpoints removed.

  The scan is stored internally with the top of the stack at the head of the
  list.  Reversing the stack gives the geometric left-to-right order of a
  lower scan, or the right-to-left order of an upper scan.

  The main correctness theorem combines executable invariants with a
  real-coordinate support-function argument.  Since the algorithm only returns
  input points, convex-hull equality follows once every input point is shown to
  lie in the convex hull of the computed output.

  The executable definitions are deliberately polymorphic over ordered
  integral domains: the scan only needs lexicographic ordering and signs of
  orientation determinants.  The geometric specification below is stated for
  real coordinates, because Isabelle's convex-hull and separating-hyperplane
  theorems live in real vector spaces.
\<close>

type_synonym 'a point = "'a \<times> 'a"

definition cross ::
  "('a::linordered_idom) point \<Rightarrow> 'a point \<Rightarrow> 'a point \<Rightarrow> 'a"
where
  "cross p q r =
    (fst q - fst p) * (snd r - snd p) -
    (snd q - snd p) * (fst r - fst p)"

definition left_turn ::
  "('a::linordered_idom) point \<Rightarrow> 'a point \<Rightarrow> 'a point \<Rightarrow> bool"
where
  "left_turn p q r \<longleftrightarrow> cross p q r > 0"

definition collinear ::
  "('a::linordered_idom) point \<Rightarrow> 'a point \<Rightarrow> 'a point \<Rightarrow> bool"
where
  "collinear p q r \<longleftrightarrow> cross p q r = 0"

lemma cross_same_left [simp]: "cross p p q = 0"
  by (simp add: cross_def)

lemma cross_same_right [simp]: "cross p q q = 0"
  by (simp add: cross_def)

lemma cross_same_outer [simp]: "cross p q p = 0"
  by (simp add: cross_def)

lemma cross_swap_outer:
  "cross p q r = - cross r q p"
  by (simp add: cross_def algebra_simps)

lemma cross_swap_last:
  "cross p r q = - cross p q r"
  by (simp add: cross_def algebra_simps)

lemma cross_cycle:
  "cross p q r = cross q r p"
  by (simp add: cross_def algebra_simps)

lemma two_cross_zero_imp_eq_middle:
  fixes a p c q :: "real point"
  assumes "cross a p q = 0"
    and "cross p c q = 0"
    and "cross a p c \<noteq> 0"
  shows "q = p"
proof (cases a; cases p; cases c; cases q)
  fix ax ay px py cx cy qx qy :: real
  assume pts: "a = (ax, ay)" "p = (px, py)" "c = (cx, cy)" "q = (qx, qy)"
  define A where "A = ax - px"
  define B where "B = ay - py"
  define C where "C = cx - px"
  define D where "D = cy - py"
  define X where "X = qx - px"
  define Y where "Y = qy - py"
  have e1: "A * Y - B * X = 0"
    using assms(1) pts
    by (simp add: cross_def A_def B_def X_def Y_def algebra_simps)
  have e2: "C * Y - D * X = 0"
    using assms(2) pts
    by (simp add: cross_def C_def D_def X_def Y_def algebra_simps)
  have det_ne: "A * D - B * C \<noteq> 0"
    using assms(3) pts
    by (simp add: cross_def A_def B_def C_def D_def algebra_simps)
  have "(A * D - B * C) * X = C * (A * Y - B * X) - A * (C * Y - D * X)"
    by (simp add: algebra_simps)
  then have X_zero: "X = 0"
    using e1 e2 det_ne by auto
  have "(A * D - B * C) * Y = D * (A * Y - B * X) - B * (C * Y - D * X)"
    by (simp add: algebra_simps)
  then have Y_zero: "Y = 0"
    using e1 e2 det_ne by auto
  show "q = p"
    using pts X_zero Y_zero by (simp add: X_def Y_def)
qed

lemma cross_pos_trans_coords:
  fixes ax ay bx b_y cx cy dx d_y :: real
  assumes "(ax, ay) < (bx, b_y)"
    and "(bx, b_y) < (cx, cy)"
    and "(cx, cy) < (dx, d_y)"
    and "0 < cross (ax, ay) (bx, b_y) (cx, cy)"
    and "0 < cross (bx, b_y) (cx, cy) (dx, d_y)"
  shows "0 < cross (ax, ay) (bx, b_y) (dx, d_y)"
    and "0 < cross (ax, ay) (cx, cy) (dx, d_y)"
proof -
  define ux where "ux = bx - ax"
  define uy where "uy = b_y - ay"
  define vx where "vx = cx - bx"
  define vy where "vy = cy - b_y"
  define wx where "wx = dx - cx"
  define wy where "wy = d_y - cy"
  have ux_nonneg: "0 \<le> ux"
    using assms(1) by (auto simp: ux_def less_prod_def')
  have vx_nonneg: "0 \<le> vx"
    using assms(2) by (auto simp: vx_def less_prod_def')
  have wx_nonneg: "0 \<le> wx"
    using assms(3) by (auto simp: wx_def less_prod_def')
  have cross_uv: "0 < ux * vy - uy * vx"
    using assms(4) by (simp add: cross_def ux_def uy_def vx_def vy_def algebra_simps)
  have cross_vw: "0 < vx * wy - vy * wx"
    using assms(5) by (simp add: cross_def vx_def vy_def wx_def wy_def algebra_simps)
  have ux_pos: "0 < ux"
  proof (rule ccontr)
    assume "\<not> 0 < ux"
    then have ux_zero: "ux = 0"
      using ux_nonneg by simp
    have uy_pos: "0 < uy"
      using assms(1) ux_zero by (auto simp: ux_def uy_def less_prod_def')
    have "ux * vy - uy * vx \<le> 0"
      using ux_zero uy_pos vx_nonneg by (simp add: mult_nonneg_nonneg)
    then show False
      using cross_uv by linarith
  qed
  have vx_pos: "0 < vx"
  proof (rule ccontr)
    assume "\<not> 0 < vx"
    then have vx_zero: "vx = 0"
      using vx_nonneg by simp
    have vy_pos: "0 < vy"
      using assms(2) vx_zero by (auto simp: vx_def vy_def less_prod_def')
    have "vx * wy - vy * wx \<le> 0"
      using vx_zero vy_pos wx_nonneg by (simp add: mult_nonneg_nonneg)
    then show False
      using cross_vw by linarith
  qed
  have identity:
    "vx * (ux * wy - uy * wx) =
      wx * (ux * vy - uy * vx) + ux * (vx * wy - vy * wx)"
    by (simp add: algebra_simps)
  have "0 \<le> wx * (ux * vy - uy * vx)"
    using wx_nonneg cross_uv by (intro mult_nonneg_nonneg) linarith+
  moreover have "0 < ux * (vx * wy - vy * wx)"
    using ux_pos cross_vw by (intro mult_pos_pos)
  ultimately have "0 < vx * (ux * wy - uy * wx)"
    using identity by linarith
  then have cross_uw: "0 < ux * wy - uy * wx"
    using vx_pos by (simp add: zero_less_mult_iff)
  show "0 < cross (ax, ay) (bx, b_y) (dx, d_y)"
    using cross_uv cross_uw
    by (simp add: cross_def ux_def uy_def vx_def vy_def wx_def wy_def algebra_simps)
  show "0 < cross (ax, ay) (cx, cy) (dx, d_y)"
    using cross_uw cross_vw
    by (simp add: cross_def ux_def uy_def vx_def vy_def wx_def wy_def algebra_simps)
qed

lemma cross_pos_trans_left_coords:
  fixes ax ay bx b_y cx cy dx d_y :: real
  assumes "(ax, ay) < (bx, b_y)"
    and "(bx, b_y) < (cx, cy)"
    and "(cx, cy) < (dx, d_y)"
    and "0 < cross (ax, ay) (bx, b_y) (cx, cy)"
    and "0 < cross (bx, b_y) (cx, cy) (dx, d_y)"
  shows "0 < cross (ax, ay) (bx, b_y) (dx, d_y)"
  using assms by (rule cross_pos_trans_coords(1))

lemma cross_pos_trans_left:
  fixes a b c d :: "real point"
  assumes "a < b" and "b < c" and "c < d"
    and "0 < cross a b c" and "0 < cross b c d"
  shows "0 < cross a b d"
  using assms
  by (cases a; cases b; cases c; cases d; auto intro: cross_pos_trans_left_coords)

lemma cross_pos_trans_right_coords:
  fixes ax ay bx b_y cx cy dx d_y :: real
  assumes "(ax, ay) < (bx, b_y)"
    and "(bx, b_y) < (cx, cy)"
    and "(cx, cy) < (dx, d_y)"
    and "0 < cross (ax, ay) (bx, b_y) (cx, cy)"
    and "0 < cross (bx, b_y) (cx, cy) (dx, d_y)"
  shows "0 < cross (ax, ay) (cx, cy) (dx, d_y)"
  using assms by (rule cross_pos_trans_coords(2))

lemma cross_pos_trans_right:
  fixes a b c d :: "real point"
  assumes "a < b" and "b < c" and "c < d"
    and "0 < cross a b c" and "0 < cross b c d"
  shows "0 < cross a c d"
  using assms
  by (cases a; cases b; cases c; cases d; auto intro: cross_pos_trans_right_coords)

fun stack_turns :: "('a::linordered_idom) point list \<Rightarrow> bool"
where
  "stack_turns [] = True"
| "stack_turns [p] = True"
| "stack_turns [p, q] = True"
| "stack_turns (p # q # r # ps) =
    (left_turn r q p \<and> stack_turns (q # r # ps))"

definition chain_turns :: "('a::linordered_idom) point list \<Rightarrow> bool"
where
  "chain_turns ps \<longleftrightarrow> stack_turns (rev ps)"

fun scan_push ::
  "('a::linordered_idom) point list \<Rightarrow> 'a point \<Rightarrow> 'a point list"
where
  "scan_push [] p = [p]"
| "scan_push [q] p = [p, q]"
| "scan_push (q # r # st) p =
    (if cross r q p \<le> 0 then scan_push (r # st) p else p # q # r # st)"

definition scan_stack ::
  "('a::linordered_idom) point list \<Rightarrow> 'a point list"
where
  "scan_stack ps = foldl scan_push [] ps"

definition scan_chain ::
  "('a::linordered_idom) point list \<Rightarrow> 'a point list"
where
  "scan_chain ps = rev (scan_stack ps)"

definition sorted_unique ::
  "('a::linorder) list \<Rightarrow> 'a list"
where
  "sorted_unique xs = sorted_list_of_set (set xs)"

definition lower_hull ::
  "('a::{linorder,linordered_idom}) point list \<Rightarrow> 'a point list"
where
  "lower_hull ps = scan_chain (sorted_unique ps)"

definition upper_hull ::
  "('a::{linorder,linordered_idom}) point list \<Rightarrow> 'a point list"
where
  "upper_hull ps = scan_chain (rev (sorted_unique ps))"

definition andrew_hull ::
  "('a::{linorder,linordered_idom}) point list \<Rightarrow> 'a point list"
where
  "andrew_hull ps =
    (case sorted_unique ps of
      [] \<Rightarrow> []
    | [p] \<Rightarrow> [p]
    | _ \<Rightarrow> butlast (lower_hull ps) @ butlast (upper_hull ps))"

lemma sorted_unique_set [simp]:
  "set (sorted_unique xs) = set xs"
  by (simp add: sorted_unique_def)

lemma sorted_unique_distinct [simp]:
  "distinct (sorted_unique xs)"
  by (simp add: sorted_unique_def)

lemma sorted_unique_sorted [simp]:
  "sorted (sorted_unique xs)"
  by (simp add: sorted_unique_def)

lemma sorted_unique_Nil_iff [simp]:
  "sorted_unique xs = [] \<longleftrightarrow> xs = []"
  by (metis set_empty sorted_unique_set)

lemma sorted_unique_singleton_iff:
  "sorted_unique xs = [p] \<longleftrightarrow> set xs = {p}"
proof
  assume "sorted_unique xs = [p]"
  then have "set (sorted_unique xs) = {p}"
    by simp
  then show "set xs = {p}"
    by simp
next
  assume set_xs: "set xs = {p}"
  have set_su: "set (sorted_unique xs) = {p}"
    using set_xs by simp
  have dist: "distinct (sorted_unique xs)"
    by simp
  show "sorted_unique xs = [p]"
  proof (cases "sorted_unique xs")
    case Nil
    then show ?thesis using set_su by simp
  next
    case (Cons y ys)
    then have y: "y = p"
      using set_su by auto
    have "ys = []"
    proof (rule ccontr)
      assume "ys \<noteq> []"
      then obtain z zs where ys: "ys = z # zs"
        by (cases ys) auto
      with Cons set_su have "z = p"
        by auto
      with Cons ys y dist show False
        by auto
    qed
    with Cons y show ?thesis by simp
  qed
qed

lemma set_scan_push_subset:
  "set (scan_push st p) \<subseteq> insert p (set st)"
  by (induction st p rule: scan_push.induct) auto

lemma set_scan_stack_subset:
  "set (scan_stack ps) \<subseteq> set ps"
  unfolding scan_stack_def
proof (induction ps arbitrary: rule: rev_induct)
  case Nil
  then show ?case by simp
next
  case (snoc p ps)
  have "set (foldl scan_push [] (ps @ [p])) \<subseteq> insert p (set (foldl scan_push [] ps))"
    using set_scan_push_subset by simp
  also have "\<dots> \<subseteq> set (ps @ [p])"
    using snoc.IH by auto
  finally show ?case .
qed

lemma set_scan_chain_subset:
  "set (scan_chain ps) \<subseteq> set ps"
  using set_scan_stack_subset by (simp add: scan_chain_def)

lemma lower_hull_subset:
  "set (lower_hull ps) \<subseteq> set ps"
  using set_scan_chain_subset[of "sorted_unique ps"]
  by (auto simp: lower_hull_def)

lemma upper_hull_subset:
  "set (upper_hull ps) \<subseteq> set ps"
  using set_scan_chain_subset[of "rev (sorted_unique ps)"]
  by (auto simp: upper_hull_def)

theorem andrew_hull_subset:
  "set (andrew_hull ps) \<subseteq> set ps"
proof (cases "sorted_unique ps")
  case Nil
  then have "ps = []"
    by simp
  then show ?thesis
    by (simp add: andrew_hull_def sorted_unique_def)
next
  case (Cons p qs)
  then show ?thesis
  proof (cases qs)
    case Nil
    with Cons have su: "sorted_unique ps = [p]"
      by simp
    then have "set ps = {p}"
      using sorted_unique_singleton_iff by blast
    moreover have "andrew_hull ps = [p]"
      using su by (simp add: andrew_hull_def)
    ultimately show ?thesis
      by simp
  next
    case (Cons q rs)
    have "set (butlast (lower_hull ps)) \<subseteq> set ps"
      using lower_hull_subset[of ps] by (auto dest: in_set_butlastD)
    moreover have "set (butlast (upper_hull ps)) \<subseteq> set ps"
      using upper_hull_subset[of ps] by (auto dest: in_set_butlastD)
    ultimately show ?thesis
      using Cons \<open>sorted_unique ps = p # qs\<close>
      by (simp add: andrew_hull_def)
  qed
qed

subsection \<open>Convex-Hull Correctness Interface\<close>

text \<open>
  The executable algorithm is generic over ordered integral domains.  The
  geometric convex-hull specification is stated here for real coordinates,
  where Isabelle's convexity library supplies the ambient real vector-space
  structure on products.

  The predicate is the envelope specification proved for the algorithm.  The
  first conjunct says that every returned vertex is an input point.  The second
  conjunct is equality of convex hulls, which includes both coverage of the
  input by the returned envelope and the absence of any hull area outside the
  input hull.  Thus the predicate is stronger than one-sided soundness.
\<close>

definition convex_hull_correct ::
  "real point list \<Rightarrow> real point list \<Rightarrow> bool"
where
  "convex_hull_correct ps hs \<longleftrightarrow>
    set hs \<subseteq> set ps \<and> convex hull set hs = convex hull set ps"

definition convex_hull_irredundant :: "real point list \<Rightarrow> bool"
where
  "convex_hull_irredundant hs \<longleftrightarrow>
    (\<forall>p\<in>set hs. convex hull (set hs - {p}) \<noteq> convex hull set hs)"

lemma strict_support_notin_convex_hull:
  fixes p v :: "real point"
  assumes strict: "\<And>q. q \<in> S \<Longrightarrow> inner v q < inner v p"
  shows "p \<notin> convex hull S"
proof
  assume p_hull: "p \<in> convex hull S"
  have "convex hull S \<subseteq> {q. inner v q < inner v p}"
    by (rule hull_minimal) (use strict in \<open>auto simp: convex_halfspace_lt\<close>)
  then show False
    using p_hull by auto
qed

lemma strict_support_hull_delete_ne:
  fixes p v :: "real point"
  assumes p: "p \<in> S"
    and strict: "\<And>q. q \<in> S - {p} \<Longrightarrow> inner v q < inner v p"
  shows "convex hull (S - {p}) \<noteq> convex hull S"
proof
  assume eq: "convex hull (S - {p}) = convex hull S"
  have "p \<notin> convex hull (S - {p})"
    by (rule strict_support_notin_convex_hull[OF strict])
  moreover have "p \<in> convex hull (S - {p})"
    using p eq by (simp add: hull_inc)
  ultimately show False
    by contradiction
qed

theorem andrew_hull_convex_hull_subset:
  fixes ps :: "real point list"
  shows "convex hull set (andrew_hull ps) \<subseteq> convex hull set ps"
  by (rule hull_mono) (rule andrew_hull_subset)

lemma convex_hull_eq_from_mutual_inclusion:
  fixes xs ys :: "('a::real_vector) list"
  assumes "set xs \<subseteq> convex hull set ys"
    and "set ys \<subseteq> convex hull set xs"
  shows "convex hull set xs = convex hull set ys"
proof (rule subset_antisym)
  show "convex hull set xs \<subseteq> convex hull set ys"
    by (rule hull_minimal) (use assms in \<open>auto simp: convex_convex_hull\<close>)
  show "convex hull set ys \<subseteq> convex hull set xs"
    by (rule hull_minimal) (use assms in \<open>auto simp: convex_convex_hull\<close>)
qed

theorem andrew_hull_convex_hull_eqI:
  fixes ps :: "real point list"
  assumes "set ps \<subseteq> convex hull set (andrew_hull ps)"
  shows "convex hull set (andrew_hull ps) = convex hull set ps"
proof (rule convex_hull_eq_from_mutual_inclusion)
  show "set (andrew_hull ps) \<subseteq> convex hull set ps"
  proof
    fix p
    assume "p \<in> set (andrew_hull ps)"
    then have "p \<in> set ps"
      using andrew_hull_subset[of ps] by blast
    then show "p \<in> convex hull set ps"
      by (rule hull_inc)
  qed
  show "set ps \<subseteq> convex hull set (andrew_hull ps)"
    by (rule assms)
qed

theorem andrew_hull_convex_hull_eq_iff:
  fixes ps :: "real point list"
  shows "convex hull set (andrew_hull ps) = convex hull set ps \<longleftrightarrow>
    set ps \<subseteq> convex hull set (andrew_hull ps)"
proof
  assume eq: "convex hull set (andrew_hull ps) = convex hull set ps"
  show "set ps \<subseteq> convex hull set (andrew_hull ps)"
    using eq by (auto intro: hull_inc)
next
  assume "set ps \<subseteq> convex hull set (andrew_hull ps)"
  then show "convex hull set (andrew_hull ps) = convex hull set ps"
    by (rule andrew_hull_convex_hull_eqI)
qed

theorem andrew_hull_correctI:
  fixes ps :: "real point list"
  assumes "set ps \<subseteq> convex hull set (andrew_hull ps)"
  shows "convex_hull_correct ps (andrew_hull ps)"
  using assms andrew_hull_subset[of ps] andrew_hull_convex_hull_eqI[of ps]
  by (simp add: convex_hull_correct_def)

theorem andrew_hull_correct_iff:
  fixes ps :: "real point list"
  shows "convex_hull_correct ps (andrew_hull ps) \<longleftrightarrow>
    set ps \<subseteq> convex hull set (andrew_hull ps)"
proof
  assume "convex_hull_correct ps (andrew_hull ps)"
  then have "convex hull set (andrew_hull ps) = convex hull set ps"
    by (simp add: convex_hull_correct_def)
  then show "set ps \<subseteq> convex hull set (andrew_hull ps)"
    by (auto intro: hull_inc)
next
  assume "set ps \<subseteq> convex hull set (andrew_hull ps)"
  then show "convex_hull_correct ps (andrew_hull ps)"
    by (rule andrew_hull_correctI)
qed

lemma distinct_scan_push:
  assumes "distinct st" and "p \<notin> set st"
  shows "distinct (scan_push st p)"
  using assms by (induction st p rule: scan_push.induct) auto

lemma distinct_scan_stack:
  assumes "distinct ps"
  shows "distinct (scan_stack ps)"
  using assms unfolding scan_stack_def
proof (induction ps arbitrary: rule: rev_induct)
  case Nil
  then show ?case by simp
next
  case (snoc p ps)
  have dps: "distinct ps" and p_notin: "p \<notin> set ps"
    using snoc.prems by auto
  have "distinct (foldl scan_push [] ps)"
    using snoc.IH dps by blast
  moreover have "p \<notin> set (foldl scan_push [] ps)"
    using p_notin set_scan_stack_subset[of ps] by (auto simp: scan_stack_def)
  ultimately show ?case
    by (simp add: distinct_scan_push)
qed

lemma distinct_scan_chain:
  assumes "distinct ps"
  shows "distinct (scan_chain ps)"
  using assms distinct_scan_stack by (simp add: scan_chain_def)

lemma distinct_lower_hull:
  "distinct (lower_hull ps)"
  by (simp add: lower_hull_def distinct_scan_chain)

lemma distinct_upper_hull:
  "distinct (upper_hull ps)"
  by (simp add: upper_hull_def distinct_scan_chain)

lemma stack_turns_scan_push:
  assumes "stack_turns st"
  shows "stack_turns (scan_push st p)"
  using assms
proof (induction st p rule: scan_push.induct)
  case (3 q r st p)
  then show ?case
    by (cases st) (auto simp: left_turn_def)
qed auto

lemma stack_turns_scan_stack:
  "stack_turns (scan_stack ps)"
  unfolding scan_stack_def
proof (induction ps arbitrary: rule: rev_induct)
  case Nil
  then show ?case by simp
next
  case (snoc p ps)
  then show ?case
    by (simp add: stack_turns_scan_push)
qed

theorem chain_turns_scan_chain:
  "chain_turns (scan_chain ps)"
  using stack_turns_scan_stack[of ps] by (simp add: chain_turns_def scan_chain_def)

theorem lower_hull_turns:
  "chain_turns (lower_hull ps)"
  by (simp add: lower_hull_def chain_turns_scan_chain)

theorem upper_hull_turns:
  "chain_turns (upper_hull ps)"
  by (simp add: upper_hull_def chain_turns_scan_chain)

lemma stack_turns_tl:
  assumes "stack_turns xs"
  shows "stack_turns (tl xs)"
  using assms
  by (cases xs; cases "tl xs"; cases "tl (tl xs)") auto

lemma stack_turns_butlast:
  assumes "stack_turns xs"
  shows "stack_turns (butlast xs)"
  using assms
  by (induction xs rule: stack_turns.induct) (auto split: list.splits)

lemma stack_turns_append_last3:
  assumes "stack_turns (xs @ [z, y, x])"
  shows "left_turn x y z"
  using assms
proof (induction xs)
  case Nil
  then show ?case
    by simp
next
  case (Cons a xs)
  have "stack_turns (tl ((a # xs) @ [z, y, x]))"
    by (rule stack_turns_tl[OF Cons.prems])
  then have "stack_turns (xs @ [z, y, x])"
    by simp
  then show ?case
    by (rule Cons.IH)
qed

lemma chain_turns_tl:
  assumes "chain_turns xs"
  shows "chain_turns (tl xs)"
proof (cases xs)
  case Nil
  then show ?thesis
    by (simp add: chain_turns_def)
next
  case (Cons x xs')
  have "stack_turns (butlast (rev xs' @ [x]))"
    using assms Cons by (intro stack_turns_butlast) (simp add: chain_turns_def)
  then show ?thesis
    using Cons by (simp add: chain_turns_def)
qed

lemma chain_turns_first:
  assumes "chain_turns (x # y # z # xs)"
  shows "left_turn x y z"
  using assms stack_turns_append_last3[of "rev xs" z y x]
  by (simp add: chain_turns_def)

lemma sorted_chain_cross_first_two:
  fixes x y z :: "real point"
  assumes sorted: "sorted_wrt (<) (x # y # zs)"
    and turns: "chain_turns (x # y # zs)"
    and z: "z \<in> set zs"
  shows "0 < cross x y z"
  using sorted turns z
proof (induction zs arbitrary: x y z)
  case Nil
  then show ?case
    by simp
next
  case (Cons w ws)
  show ?case
  proof (cases "z = w")
    case True
    have "left_turn x y w"
      using chain_turns_first[OF Cons.prems(2)] .
    then show ?thesis
      using True by (simp add: left_turn_def)
  next
    case False
    then have z_ws: "z \<in> set ws"
      using Cons.prems(3) by simp
    have sorted_tail: "sorted_wrt (<) (y # w # ws)"
      using Cons.prems(1) by simp
    have turns_tail: "chain_turns (y # w # ws)"
      using chain_turns_tl[OF Cons.prems(2)] by simp
    have y_w_z: "0 < cross y w z"
      using Cons.IH[OF sorted_tail turns_tail z_ws] .
    have x_y_w: "0 < cross x y w"
      using chain_turns_first[OF Cons.prems(2)]
      by (simp add: left_turn_def)
    have "x < y" and "y < w" and "w < z"
      using Cons.prems(1) z_ws by auto
    then show ?thesis
      using cross_pos_trans_left[OF _ _ _ x_y_w y_w_z] by blast
  qed
qed

lemma sorted_chain_cross_nth_increasing:
  fixes xs :: "real point list"
  assumes sorted: "sorted_wrt (<) xs"
    and turns: "chain_turns xs"
    and ij: "i < j"
    and jk: "j < k"
    and k_len: "k < length xs"
  shows "0 < cross (xs ! i) (xs ! j) (xs ! k)"
  using sorted turns ij jk k_len
proof (induction xs arbitrary: i j k)
  case Nil
  then show ?case
    by simp
next
  case (Cons x xs)
  show ?case
  proof (cases i)
    case (Suc i')
    then obtain j' k' where j: "j = Suc j'" and k: "k = Suc k'"
      using Cons.prems(3,4) by (cases j; cases k) auto
    have "0 < cross (xs ! i') (xs ! j') (xs ! k')"
    proof (rule Cons.IH)
      show "sorted_wrt (<) xs"
        using Cons.prems(1) by simp
      show "chain_turns xs"
        using chain_turns_tl[OF Cons.prems(2)] by simp
      show "i' < j'"
        using Cons.prems(3) Suc j by simp
      show "j' < k'"
        using Cons.prems(4) j k by simp
      show "k' < length xs"
        using Cons.prems(5) k by simp
    qed
    then show ?thesis
      using Suc j k by simp
  next
    case 0
    note i_zero = 0
    then have j_pos: "0 < j"
      using Cons.prems(3) by simp
    obtain y ys where xs: "xs = y # ys"
      using j_pos Cons.prems(4,5) by (cases xs) auto
    obtain j' where j: "j = Suc j'"
      using j_pos by (cases j) auto
    obtain k' where k: "k = Suc k'"
      using Cons.prems(4) j by (cases k) auto
    have sorted_tail: "sorted_wrt (<) xs"
      using Cons.prems(1) by simp
    have turns_tail: "chain_turns xs"
      using chain_turns_tl[OF Cons.prems(2)] by simp
    show ?thesis
    proof (cases j')
      case 0
      then have k'_pos: "0 < k'"
        using Cons.prems(4) j k by simp
      then obtain kk where kk: "k' = Suc kk"
        by (cases k') auto
      have kk_len: "kk < length ys"
        using Cons.prems(5) k kk xs by simp
      have "0 < cross x y (ys ! kk)"
        using sorted_chain_cross_first_two[of x y ys "ys ! kk"] Cons.prems(1,2) xs kk_len
        by simp
      then show ?thesis
        using i_zero 0 j k kk xs by simp
    next
      case (Suc jj)
      have j'_lt_k': "j' < k'"
        using Cons.prems(4) j k by simp
      have k'_len: "k' < length xs"
        using Cons.prems(5) k by simp
      have y_b_c: "0 < cross (xs ! 0) (xs ! j') (xs ! k')"
      proof (rule Cons.IH)
        show "sorted_wrt (<) xs"
          using sorted_tail .
        show "chain_turns xs"
          using turns_tail .
        show "0 < j'"
          using Suc by simp
        show "j' < k'"
          using j'_lt_k' .
        show "k' < length xs"
          using k'_len .
      qed
      have y_b_c': "0 < cross y (xs ! j') (xs ! k')"
        using y_b_c xs by simp
      have jj_len: "jj < length ys"
        using Suc k'_len j'_lt_k' xs by simp
      have x_y_b: "0 < cross x y (ys ! jj)"
        using sorted_chain_cross_first_two[of x y ys "ys ! jj"] Cons.prems(1,2) xs jj_len
        by simp
      have x_y_b': "0 < cross x y (xs ! j')"
        using x_y_b Suc xs by simp
      have x_lt_y: "x < y"
        using Cons.prems(1) xs by simp
      have j'_len: "j' < length xs"
        using j'_lt_k' k'_len by simp
      have y_lt_b: "y < xs ! j'"
        using sorted_wrt_nth_less[OF sorted_tail, of 0 j'] Suc j'_len xs by simp
      have b_lt_c: "xs ! j' < xs ! k'"
        using sorted_wrt_nth_less[OF sorted_tail, of j' k'] j'_lt_k' k'_len .
      have "0 < cross x (xs ! j') (xs ! k')"
        by (rule cross_pos_trans_right[OF x_lt_y y_lt_b b_lt_c x_y_b' y_b_c'])
      then show ?thesis
      using i_zero j k by simp
    qed
  qed
qed

lemma uminus_less_point_iff [simp]:
  fixes p q :: "real point"
  shows "- p < - q \<longleftrightarrow> q < p"
  by (cases p; cases q) (auto simp: less_prod_def')

lemma cross_uminus [simp]:
  fixes p q r :: "real point"
  shows "cross (- p) (- q) (- r) = cross p q r"
  by (cases p; cases q; cases r) (simp add: cross_def algebra_simps)

lemma left_turn_uminus [simp]:
  fixes p q r :: "real point"
  shows "left_turn (- p) (- q) (- r) \<longleftrightarrow> left_turn p q r"
  by (simp add: left_turn_def)

lemma stack_turns_map_uminus [simp]:
  fixes xs :: "real point list"
  shows "stack_turns (map (\<lambda>p. - p) xs) \<longleftrightarrow> stack_turns xs"
  by (induction xs rule: stack_turns.induct) auto

lemma chain_turns_map_uminus [simp]:
  fixes xs :: "real point list"
  shows "chain_turns (map (\<lambda>p. - p) xs) \<longleftrightarrow> chain_turns xs"
  by (simp add: chain_turns_def rev_map)

lemma sorted_wrt_less_map_uminus:
  fixes xs :: "real point list"
  assumes "sorted_wrt (>) xs"
  shows "sorted_wrt (<) (map (\<lambda>p. - p) xs)"
  using assms by (induction xs) auto

lemma sorted_chain_cross_nth_decreasing:
  fixes xs :: "real point list"
  assumes sorted: "sorted_wrt (>) xs"
    and turns: "chain_turns xs"
    and ij: "i < j"
    and jk: "j < k"
    and k_len: "k < length xs"
  shows "0 < cross (xs ! i) (xs ! j) (xs ! k)"
proof -
  let ?xs = "map (\<lambda>p. - p) xs"
  have "0 < cross (?xs ! i) (?xs ! j) (?xs ! k)"
  proof (rule sorted_chain_cross_nth_increasing)
    show "sorted_wrt (<) ?xs"
      by (rule sorted_wrt_less_map_uminus[OF sorted])
    show "chain_turns ?xs"
      using turns by simp
    show "i < j"
      using ij .
    show "j < k"
      using jk .
    show "k < length ?xs"
      using k_len by simp
  qed
  then show ?thesis
    using ij jk k_len by simp
qed

lemma sorted_chain_edge_cross_nonneg_increasing:
  fixes xs :: "real point list"
  assumes sorted: "sorted_wrt (<) xs"
    and turns: "chain_turns xs"
    and edge: "Suc i < length xs"
    and q: "q \<in> set xs"
  shows "0 \<le> cross (xs ! i) (xs ! Suc i) q"
proof -
  obtain k where k_len: "k < length xs" and q_eq: "q = xs ! k"
    using q by (auto simp: in_set_conv_nth)
  show ?thesis
  proof (cases "k = i \<or> k = Suc i")
    case True
    then show ?thesis
      using q_eq by auto
  next
    case False
    note not_endpoint = False
    show ?thesis
    proof (cases "k < i")
      case True
      have "0 < cross (xs ! k) (xs ! i) (xs ! Suc i)"
        by (rule sorted_chain_cross_nth_increasing[OF sorted turns True _ edge]) simp
      then show ?thesis
        using q_eq cross_cycle[of "xs ! k" "xs ! i" "xs ! Suc i"] by simp
    next
      case False
      then have "Suc i < k"
        using not_endpoint by linarith
      have "0 < cross (xs ! i) (xs ! Suc i) (xs ! k)"
        by (rule sorted_chain_cross_nth_increasing[OF sorted turns _ \<open>Suc i < k\<close> k_len]) simp
      then show ?thesis
        using q_eq by simp
    qed
  qed
qed

lemma sorted_chain_edge_cross_nonneg_decreasing:
  fixes xs :: "real point list"
  assumes sorted: "sorted_wrt (>) xs"
    and turns: "chain_turns xs"
    and edge: "Suc i < length xs"
    and q: "q \<in> set xs"
  shows "0 \<le> cross (xs ! i) (xs ! Suc i) q"
proof -
  obtain k where k_len: "k < length xs" and q_eq: "q = xs ! k"
    using q by (auto simp: in_set_conv_nth)
  show ?thesis
  proof (cases "k = i \<or> k = Suc i")
    case True
    then show ?thesis
      using q_eq by auto
  next
    case False
    note not_endpoint = False
    show ?thesis
    proof (cases "k < i")
      case True
      have "0 < cross (xs ! k) (xs ! i) (xs ! Suc i)"
        by (rule sorted_chain_cross_nth_decreasing[OF sorted turns True _ edge]) simp
      then show ?thesis
        using q_eq cross_cycle[of "xs ! k" "xs ! i" "xs ! Suc i"] by simp
    next
      case False
      then have "Suc i < k"
        using not_endpoint by linarith
      have "0 < cross (xs ! i) (xs ! Suc i) (xs ! k)"
        by (rule sorted_chain_cross_nth_decreasing[OF sorted turns _ \<open>Suc i < k\<close> k_len]) simp
      then show ?thesis
        using q_eq by simp
    qed
  qed
qed

lemma scan_push_nonempty [simp]:
  "scan_push st p \<noteq> []"
  by (induction st p rule: scan_push.induct) auto

lemma scan_stack_nonempty:
  "ps \<noteq> [] \<Longrightarrow> scan_stack ps \<noteq> []"
  by (cases ps rule: rev_cases) (simp_all add: scan_stack_def)

lemma scan_chain_nonempty:
  "ps \<noteq> [] \<Longrightarrow> scan_chain ps \<noteq> []"
  by (simp add: scan_chain_def scan_stack_nonempty)

lemma lower_hull_nonempty:
  "ps \<noteq> [] \<Longrightarrow> lower_hull ps \<noteq> []"
  by (simp add: lower_hull_def scan_chain_nonempty)

lemma upper_hull_nonempty:
  "ps \<noteq> [] \<Longrightarrow> upper_hull ps \<noteq> []"
  by (simp add: upper_hull_def scan_chain_nonempty)

subsection \<open>Endpoints of the Scans\<close>

lemma hd_scan_push [simp]:
  "hd (scan_push st p) = p"
  by (induction st p rule: scan_push.induct) simp_all

lemma last_scan_push:
  assumes "st \<noteq> []"
  shows "last (scan_push st p) = last st"
  using assms by (induction st p rule: scan_push.induct) simp_all

lemma hd_scan_stack:
  assumes "ps \<noteq> []"
  shows "hd (scan_stack ps) = last ps"
  using assms
proof (induction ps rule: rev_induct)
  case Nil
  then show ?case by simp
next
  case (snoc p ps)
  show ?case
    by (simp add: scan_stack_def)
qed

lemma last_scan_stack:
  assumes "ps \<noteq> []"
  shows "last (scan_stack ps) = hd ps"
  using assms
proof (induction ps rule: rev_induct)
  case Nil
  then show ?case by simp
next
  case (snoc p ps)
  show ?case
  proof (cases ps)
    case Nil
    then show ?thesis
      by (simp add: scan_stack_def)
  next
    case (Cons q qs)
    let ?st = "foldl scan_push [] ps"
    have "?st \<noteq> []"
      using Cons scan_stack_nonempty[of ps] by (simp add: scan_stack_def)
    moreover have "last ?st = hd ps"
    proof -
      have "last (scan_stack ps) = hd ps"
        using snoc.IH Cons by simp
      then show ?thesis
        by (simp add: scan_stack_def)
    qed
    ultimately show ?thesis
      using Cons by (simp add: scan_stack_def last_scan_push)
  qed
qed

lemma hd_scan_chain:
  assumes "ps \<noteq> []"
  shows "hd (scan_chain ps) = hd ps"
proof -
  have "scan_stack ps \<noteq> []"
    using assms scan_stack_nonempty by blast
  then show ?thesis
    using assms last_scan_stack[of ps] by (simp add: scan_chain_def hd_rev)
qed

lemma last_scan_chain:
  assumes "ps \<noteq> []"
  shows "last (scan_chain ps) = last ps"
proof -
  have "scan_stack ps \<noteq> []"
    using assms scan_stack_nonempty by blast
  then show ?thesis
    using assms hd_scan_stack[of ps] by (simp add: scan_chain_def last_rev)
qed

lemma hd_lower_hull:
  assumes "ps \<noteq> []"
  shows "hd (lower_hull ps) = hd (sorted_unique ps)"
  using assms by (simp add: lower_hull_def hd_scan_chain)

lemma last_lower_hull:
  assumes "ps \<noteq> []"
  shows "last (lower_hull ps) = last (sorted_unique ps)"
  using assms by (simp add: lower_hull_def last_scan_chain)

lemma hd_upper_hull:
  assumes "ps \<noteq> []"
  shows "hd (upper_hull ps) = last (sorted_unique ps)"
proof -
  have su_nonempty: "sorted_unique ps \<noteq> []"
    using assms by simp
  then show ?thesis
    using assms by (simp add: upper_hull_def hd_scan_chain hd_rev)
qed

lemma last_upper_hull:
  assumes "ps \<noteq> []"
  shows "last (upper_hull ps) = hd (sorted_unique ps)"
proof -
  have su_nonempty: "sorted_unique ps \<noteq> []"
    using assms by simp
  then show ?thesis
    using assms by (simp add: upper_hull_def last_scan_chain last_rev)
qed

lemma length_scan_chain_ge2:
  assumes "xs \<noteq> []" and "hd xs \<noteq> last xs"
  shows "2 \<le> length (scan_chain xs)"
proof -
  have ch_nonempty: "scan_chain xs \<noteq> []"
    using assms(1) scan_chain_nonempty by blast
  have endpoints: "hd (scan_chain xs) \<noteq> last (scan_chain xs)"
    using assms hd_scan_chain[of xs] last_scan_chain[of xs] by simp
  obtain y ys where ch: "scan_chain xs = y # ys"
    using ch_nonempty by (cases "scan_chain xs") auto
  then show ?thesis
  proof (cases ys)
    case Nil
    then show ?thesis
      using ch endpoints by simp
  next
    case (Cons z zs)
    then show ?thesis
      using ch by simp
  qed
qed

lemma hd_ne_last_sorted_unique_if_card_ge2:
  assumes "2 \<le> card (set ps)"
  shows "hd (sorted_unique ps) \<noteq> last (sorted_unique ps)"
proof -
  have len: "length (sorted_unique ps) = card (set ps)"
    by (simp add: sorted_unique_def length_sorted_list_of_set)
  then have len_ge2: "2 \<le> length (sorted_unique ps)"
    using assms by simp
  obtain x xs where su_Cons: "sorted_unique ps = x # xs"
    using len_ge2 by (cases "sorted_unique ps") auto
  then obtain y ys where xs_Cons: "xs = y # ys"
    using len_ge2 by (cases xs) auto
  have "last (sorted_unique ps) \<in> set xs"
    by (simp add: su_Cons xs_Cons)
  then show ?thesis
    using sorted_unique_distinct[of ps] by (auto simp: su_Cons)
qed

lemma length_lower_hull_ge2:
  assumes "2 \<le> card (set ps)"
  shows "2 \<le> length (lower_hull ps)"
proof -
  have ps_nonempty: "ps \<noteq> []"
    using assms by auto
  have su_ne: "hd (sorted_unique ps) \<noteq> last (sorted_unique ps)"
    using hd_ne_last_sorted_unique_if_card_ge2[OF assms] .
  show ?thesis
    using length_scan_chain_ge2[of "sorted_unique ps"] ps_nonempty su_ne
    by (simp add: lower_hull_def)
qed

lemma length_upper_hull_ge2:
  assumes "2 \<le> card (set ps)"
  shows "2 \<le> length (upper_hull ps)"
proof -
  have ps_nonempty: "ps \<noteq> []"
    using assms by auto
  have su_nonempty: "sorted_unique ps \<noteq> []"
    using ps_nonempty by simp
  have rev_ne: "hd (rev (sorted_unique ps)) \<noteq> last (rev (sorted_unique ps))"
    using hd_ne_last_sorted_unique_if_card_ge2[OF assms] su_nonempty
    by (simp add: hd_rev last_rev)
  show ?thesis
    using length_scan_chain_ge2[of "rev (sorted_unique ps)"] su_nonempty rev_ne
    by (simp add: upper_hull_def)
qed

lemma set_butlast_last:
  assumes "xs \<noteq> []"
  shows "set xs = set (butlast xs) \<union> {last xs}"
proof -
  have "xs = butlast xs @ [last xs]"
    using assms by simp
  then have "set xs = set (butlast xs @ [last xs])"
    by auto
  also have "\<dots> = set (butlast xs) \<union> {last xs}"
    by simp
  finally show ?thesis .
qed

lemma hd_mem_set_butlast:
  assumes "2 \<le> length xs"
  shows "hd xs \<in> set (butlast xs)"
proof (cases xs)
  case Nil
  then show ?thesis
    using assms by simp
next
  case (Cons x xs')
  then show ?thesis
  proof (cases xs')
    case Nil
    then show ?thesis
      using assms Cons by simp
  next
    case (Cons y ys)
    then show ?thesis
      using \<open>xs = x # xs'\<close> by simp
  qed
qed

theorem set_andrew_hull:
  "set (andrew_hull ps) = set (lower_hull ps) \<union> set (upper_hull ps)"
proof (cases "sorted_unique ps")
  case Nil
  then have "ps = []"
    by simp
  then show ?thesis
    by (simp add: andrew_hull_def lower_hull_def upper_hull_def
        scan_chain_def scan_stack_def sorted_unique_def)
next
  case (Cons p qs)
  then show ?thesis
  proof (cases qs)
    case Nil
    then show ?thesis
      using Cons
      by (simp add: andrew_hull_def lower_hull_def upper_hull_def
          scan_chain_def scan_stack_def sorted_unique_def)
  next
    case (Cons q rs)
    let ?L = "lower_hull ps"
    let ?U = "upper_hull ps"
    have ps_nonempty: "ps \<noteq> []"
      using \<open>sorted_unique ps = p # qs\<close> sorted_unique_Nil_iff[of ps] by force
    have len_su: "length (sorted_unique ps) = card (set ps)"
      by (simp add: sorted_unique_def length_sorted_list_of_set)
    have "2 \<le> length (sorted_unique ps)"
      using \<open>sorted_unique ps = p # qs\<close> Cons by simp
    then have card_ge2: "2 \<le> card (set ps)"
      using len_su by simp
    have andrew: "andrew_hull ps = butlast ?L @ butlast ?U"
      using \<open>sorted_unique ps = p # qs\<close> Cons by (simp add: andrew_hull_def)
    have L_nonempty: "?L \<noteq> []"
      using ps_nonempty lower_hull_nonempty by blast
    have U_nonempty: "?U \<noteq> []"
      using ps_nonempty upper_hull_nonempty by blast
    have last_L: "last ?L = hd ?U"
      using ps_nonempty last_lower_hull[of ps] hd_upper_hull[of ps] by simp
    have last_U: "last ?U = hd ?L"
      using ps_nonempty last_upper_hull[of ps] hd_lower_hull[of ps] by simp
    have last_L_in_U: "last ?L \<in> set (butlast ?U)"
      using last_L hd_mem_set_butlast[OF length_upper_hull_ge2[OF card_ge2]] by simp
    have last_U_in_L: "last ?U \<in> set (butlast ?L)"
      using last_U hd_mem_set_butlast[OF length_lower_hull_ge2[OF card_ge2]] by simp
    show ?thesis
      using andrew set_butlast_last[OF L_nonempty] set_butlast_last[OF U_nonempty]
        last_L_in_U last_U_in_L
      by auto
  qed
qed

subsection \<open>Support-Function Invariants\<close>

definition support_value :: "real point \<Rightarrow> real point \<Rightarrow> real"
where
  "support_value v p = fst v * fst p + snd v * snd p"

lemma support_value_eq_inner:
  "support_value v p = inner v p"
  by (cases v; cases p; simp add: support_value_def)

lemma support_value_edge_normal:
  fixes a b x :: "real point"
  shows "support_value (snd b - snd a, fst a - fst b) x =
    support_value (snd b - snd a, fst a - fst b) a - cross a b x"
  by (cases a; cases b; cases x) (simp add: support_value_def cross_def algebra_simps)

lemma support_middle_le_max_increasing:
  fixes r q p v :: "real point"
  assumes rq: "r < q" and qp: "q < p"
    and turn: "cross r q p \<le> 0"
    and neg: "snd v < 0"
  shows "support_value v q \<le> max (support_value v r) (support_value v p)"
proof (cases "fst r = fst p")
  case True
  have frq: "fst r = fst q" and fqp: "fst q = fst p"
    using rq qp True by (auto simp: less_prod_def')
  have yrq: "snd r \<le> snd q"
    using rq frq by (auto simp: less_prod_def')
  have "snd v * snd q \<le> snd v * snd r"
    using yrq neg by (intro mult_left_mono_neg) auto
  then have "support_value v q \<le> support_value v r"
    using frq fqp by (simp add: support_value_def)
  then show ?thesis
    by simp
next
  case False
  define A where "A = fst q - fst r"
  define B where "B = fst p - fst q"
  define D where "D = fst p - fst r"
  have xrq: "fst r \<le> fst q"
    using rq by (auto simp: less_prod_def')
  have xqp: "fst q \<le> fst p"
    using qp by (auto simp: less_prod_def')
  have A_nonneg: "0 \<le> A"
    using xrq by (simp add: A_def)
  have B_nonneg: "0 \<le> B"
    using xqp by (simp add: B_def)
  have D_pos: "0 < D"
    using xrq xqp False unfolding D_def by linarith
  have D_eq: "D = A + B"
    by (simp add: A_def B_def D_def)
  have x_combo: "D * fst q = B * fst r + A * fst p"
    by (simp add: A_def B_def D_def algebra_simps)
  have y_combo: "B * snd r + A * snd p \<le> D * snd q"
  proof -
    have "A * (snd p - snd r) \<le> (snd q - snd r) * D"
      using turn by (simp add: cross_def A_def D_def)
    then show ?thesis
      using D_eq by (simp add: algebra_simps)
  qed
  have y_scaled:
    "snd v * (D * snd q) \<le> snd v * (B * snd r + A * snd p)"
    using y_combo neg by (intro mult_left_mono_neg) auto
  have x_part:
    "D * (fst v * fst q) = B * (fst v * fst r) + A * (fst v * fst p)"
  proof -
    have "D * (fst v * fst q) = fst v * (D * fst q)"
      by (simp add: algebra_simps)
    also have "\<dots> = fst v * (B * fst r + A * fst p)"
      using x_combo by simp
    also have "\<dots> = B * (fst v * fst r) + A * (fst v * fst p)"
      by (simp add: algebra_simps)
    finally show ?thesis .
  qed
  have y_part:
    "D * (snd v * snd q) \<le> B * (snd v * snd r) + A * (snd v * snd p)"
  proof -
    have "D * (snd v * snd q) = snd v * (D * snd q)"
      by (simp add: algebra_simps)
    also have "\<dots> \<le> snd v * (B * snd r + A * snd p)"
      using y_scaled .
    also have "\<dots> = B * (snd v * snd r) + A * (snd v * snd p)"
      by (simp add: algebra_simps)
    finally show ?thesis .
  qed
  have scaled_le:
    "D * support_value v q \<le>
      B * support_value v r + A * support_value v p"
  proof -
    have "D * support_value v q =
        D * (fst v * fst q) + D * (snd v * snd q)"
      by (simp add: support_value_def algebra_simps)
    also have "\<dots> \<le>
        (B * (fst v * fst r) + A * (fst v * fst p)) +
        (B * (snd v * snd r) + A * (snd v * snd p))"
    proof (rule add_mono)
      show "D * (fst v * fst q) \<le>
          B * (fst v * fst r) + A * (fst v * fst p)"
        using x_part by simp
      show "D * (snd v * snd q) \<le>
          B * (snd v * snd r) + A * (snd v * snd p)"
        using y_part .
    qed
    also have "\<dots> = B * support_value v r + A * support_value v p"
      by (simp add: support_value_def algebra_simps)
    finally show ?thesis .
  qed
  have r_le: "B * support_value v r \<le>
      B * max (support_value v r) (support_value v p)"
    using B_nonneg by (intro mult_left_mono) simp_all
  have p_le: "A * support_value v p \<le>
      A * max (support_value v r) (support_value v p)"
    using A_nonneg by (intro mult_left_mono) simp_all
  have "D * support_value v q \<le>
      D * max (support_value v r) (support_value v p)"
    using scaled_le r_le p_le D_eq by (simp add: algebra_simps)
  then show ?thesis
    using D_pos by simp
qed

lemma support_middle_le_max_decreasing:
  fixes r q p v :: "real point"
  assumes pq: "p < q" and qr: "q < r"
    and turn: "cross r q p \<le> 0"
    and pos: "0 < snd v"
  shows "support_value v q \<le> max (support_value v r) (support_value v p)"
proof (cases "fst p = fst r")
  case True
  have fpq: "fst p = fst q" and fqr: "fst q = fst r"
    using pq qr True by (auto simp: less_prod_def')
  have yqr: "snd q \<le> snd r"
    using qr fqr by (auto simp: less_prod_def')
  have "snd v * snd q \<le> snd v * snd r"
    using yqr pos by (intro mult_left_mono) auto
  then have "support_value v q \<le> support_value v r"
    using fpq fqr by (simp add: support_value_def)
  then show ?thesis
    by simp
next
  case False
  define A where "A = fst q - fst p"
  define B where "B = fst r - fst q"
  define D where "D = fst r - fst p"
  have xpq: "fst p \<le> fst q"
    using pq by (auto simp: less_prod_def')
  have xqr: "fst q \<le> fst r"
    using qr by (auto simp: less_prod_def')
  have A_nonneg: "0 \<le> A"
    using xpq by (simp add: A_def)
  have B_nonneg: "0 \<le> B"
    using xqr by (simp add: B_def)
  have D_pos: "0 < D"
    using xpq xqr False unfolding D_def by linarith
  have D_eq: "D = A + B"
    by (simp add: A_def B_def D_def)
  have x_combo: "D * fst q = B * fst p + A * fst r"
    by (simp add: A_def B_def D_def algebra_simps)
  have y_combo: "D * snd q \<le> B * snd p + A * snd r"
  proof -
    have "(snd q - snd p) * D \<le> A * (snd r - snd p)"
      using turn by (simp add: cross_def A_def D_def algebra_simps)
    then show ?thesis
      using D_eq by (simp add: algebra_simps)
  qed
  have y_scaled:
    "snd v * (D * snd q) \<le> snd v * (B * snd p + A * snd r)"
    using y_combo pos by (intro mult_left_mono) auto
  have x_part:
    "D * (fst v * fst q) = B * (fst v * fst p) + A * (fst v * fst r)"
  proof -
    have "D * (fst v * fst q) = fst v * (D * fst q)"
      by (simp add: algebra_simps)
    also have "\<dots> = fst v * (B * fst p + A * fst r)"
      using x_combo by simp
    also have "\<dots> = B * (fst v * fst p) + A * (fst v * fst r)"
      by (simp add: algebra_simps)
    finally show ?thesis .
  qed
  have y_part:
    "D * (snd v * snd q) \<le> B * (snd v * snd p) + A * (snd v * snd r)"
  proof -
    have "D * (snd v * snd q) = snd v * (D * snd q)"
      by (simp add: algebra_simps)
    also have "\<dots> \<le> snd v * (B * snd p + A * snd r)"
      using y_scaled .
    also have "\<dots> = B * (snd v * snd p) + A * (snd v * snd r)"
      by (simp add: algebra_simps)
    finally show ?thesis .
  qed
  have scaled_le:
    "D * support_value v q \<le>
      B * support_value v p + A * support_value v r"
  proof -
    have "D * support_value v q =
        D * (fst v * fst q) + D * (snd v * snd q)"
      by (simp add: support_value_def algebra_simps)
    also have "\<dots> \<le>
        (B * (fst v * fst p) + A * (fst v * fst r)) +
        (B * (snd v * snd p) + A * (snd v * snd r))"
    proof (rule add_mono)
      show "D * (fst v * fst q) \<le>
          B * (fst v * fst p) + A * (fst v * fst r)"
        using x_part by simp
      show "D * (snd v * snd q) \<le>
          B * (snd v * snd p) + A * (snd v * snd r)"
        using y_part .
    qed
    also have "\<dots> = B * support_value v p + A * support_value v r"
      by (simp add: support_value_def algebra_simps)
    finally show ?thesis .
  qed
  have p_le: "B * support_value v p \<le>
      B * max (support_value v r) (support_value v p)"
    using B_nonneg by (intro mult_left_mono) simp_all
  have r_le: "A * support_value v r \<le>
      A * max (support_value v r) (support_value v p)"
    using A_nonneg by (intro mult_left_mono) simp_all
  have "D * support_value v q \<le>
      D * max (support_value v r) (support_value v p)"
    using scaled_le p_le r_le D_eq by (simp add: algebra_simps)
  then show ?thesis
    using D_pos by simp
qed

lemma scan_push_strict_sorted_increasing:
  fixes st :: "real point list"
  assumes sorted: "sorted_wrt (<) (rev st)"
    and below: "\<And>q. q \<in> set st \<Longrightarrow> q < p"
  shows "sorted_wrt (<) (rev (scan_push st p))"
  using sorted below
  by (induction st p rule: scan_push.induct) (auto simp: sorted_wrt_append)

lemma scan_stack_strict_sorted_increasing:
  fixes xs :: "real point list"
  assumes "sorted_wrt (<) xs"
  shows "sorted_wrt (<) (rev (scan_stack xs))"
  using assms unfolding scan_stack_def
proof (induction xs rule: rev_induct)
  case Nil
  then show ?case by simp
next
  case (snoc p xs)
  have sorted_xs: "sorted_wrt (<) xs"
    using snoc.prems by (simp add: sorted_wrt_append)
  have below: "\<And>q. q \<in> set (foldl scan_push [] xs) \<Longrightarrow> q < p"
  proof -
    fix q
    assume "q \<in> set (foldl scan_push [] xs)"
    then have "q \<in> set xs"
      using set_scan_stack_subset[of xs] by (auto simp: scan_stack_def)
    then show "q < p"
      using snoc.prems by (simp add: sorted_wrt_append)
  qed
  show ?case
    using scan_push_strict_sorted_increasing[OF snoc.IH[OF sorted_xs] below] by simp
qed

lemma scan_push_support_dominates_increasing_step:
  fixes q r p x :: "real point" and st :: "real point list"
  assumes tail_dom:
    "cross r q p \<le> 0 \<Longrightarrow>
      (\<And>x. x \<in> insert p (set (r # st)) \<Longrightarrow>
        \<exists>y\<in>set (scan_push (r # st) p). support_value v x \<le> support_value v y)"
    and sorted: "sorted_wrt (<) (rev (q # r # st))"
    and below: "\<And>z. z \<in> set (q # r # st) \<Longrightarrow> z < p"
    and neg: "snd v < 0"
    and x_in: "x \<in> insert p (set (q # r # st))"
  shows "\<exists>y\<in>set (scan_push (q # r # st) p). support_value v x \<le> support_value v y"
proof (cases "cross r q p \<le> 0")
  case False
  have "x \<in> set (scan_push (q # r # st) p)"
    using False x_in by simp
  then show ?thesis
    by (intro bexI[where x = x]) simp_all
next
  case True
  show ?thesis
  proof (cases "x = q")
    case False
    then have x_tail: "x \<in> insert p (set (r # st))"
      using x_in by auto
    obtain y where y_set: "y \<in> set (scan_push (r # st) p)"
      and y_ge: "support_value v x \<le> support_value v y"
      using tail_dom[OF True x_tail] by auto
    have "scan_push (q # r # st) p = scan_push (r # st) p"
      using True by simp
    then show ?thesis
      using y_set y_ge by auto
  next
    case True_x: True
    have rq: "r < q"
      using sorted by (simp add: sorted_wrt_append)
    have qp: "q < p"
      using below by simp
    have q_le: "support_value v q \<le> max (support_value v r) (support_value v p)"
      using support_middle_le_max_increasing[OF rq qp True neg] .
    obtain yr where yr_set: "yr \<in> set (scan_push (r # st) p)"
      and yr_ge: "support_value v r \<le> support_value v yr"
      using tail_dom[OF True, of r] by auto
    obtain yp where yp_set: "yp \<in> set (scan_push (r # st) p)"
      and yp_ge: "support_value v p \<le> support_value v yp"
      using tail_dom[OF True, of p] by auto
    have "support_value v q \<le> support_value v r \<or>
        support_value v q \<le> support_value v p"
      using q_le by (simp add: max_def split: if_splits)
    then show ?thesis
    proof
      assume "support_value v q \<le> support_value v r"
      then have "support_value v q \<le> support_value v yr"
        using yr_ge by (rule order_trans)
      then have "support_value v x \<le> support_value v yr"
        using True_x by simp
      then show ?thesis
        using True yr_set by (intro bexI[where x = yr]) simp_all
    next
      assume "support_value v q \<le> support_value v p"
      then have "support_value v q \<le> support_value v yp"
        using yp_ge by (rule order_trans)
      then have "support_value v x \<le> support_value v yp"
        using True_x by simp
      then show ?thesis
        using True yp_set by (intro bexI[where x = yp]) simp_all
    qed
  qed
qed

lemma scan_push_support_dominates_increasing:
  fixes st :: "real point list"
  shows "sorted_wrt (<) (rev st) \<Longrightarrow>
    (\<And>q. q \<in> set st \<Longrightarrow> q < p) \<Longrightarrow>
    snd v < 0 \<Longrightarrow>
    x \<in> insert p (set st) \<Longrightarrow>
    \<exists>y\<in>set (scan_push st p). support_value v x \<le> support_value v y"
proof (induction st p arbitrary: x rule: scan_push.induct)
  case (1 p)
  then show ?case by auto
next
  case (2 q p)
  then show ?case by auto
next
  case (3 q r st p)
  have sorted_tail: "sorted_wrt (<) (rev (r # st))"
    using "3.prems"(1) by (simp add: sorted_wrt_append)
  have below_tail: "\<And>w. w \<in> set (r # st) \<Longrightarrow> w < p"
    using "3.prems"(2) by simp
  have neg: "snd v < 0"
    using "3.prems"(3) .
  have tail_dom:
    "cross r q p \<le> 0 \<Longrightarrow>
      (\<And>z. z \<in> insert p (set (r # st)) \<Longrightarrow>
        \<exists>y\<in>set (scan_push (r # st) p). support_value v z \<le> support_value v y)"
    using "3.IH"[OF _ sorted_tail below_tail neg] by blast
  have sorted: "sorted_wrt (<) (rev (q # r # st))"
    using "3.prems"(1) .
  have below: "\<And>z. z \<in> set (q # r # st) \<Longrightarrow> z < p"
    using "3.prems"(2) .
  have x_in: "x \<in> insert p (set (q # r # st))"
    using "3.prems"(4) .
  show ?case
    by (rule scan_push_support_dominates_increasing_step[
        OF tail_dom sorted below neg x_in])
qed

lemma scan_stack_support_dominates_increasing:
  fixes xs :: "real point list"
  assumes sorted: "sorted_wrt (<) xs"
    and neg: "snd v < 0"
    and x: "x \<in> set xs"
  shows "\<exists>y\<in>set (scan_stack xs). support_value v x \<le> support_value v y"
  using sorted x
proof (induction xs arbitrary: x rule: rev_induct)
  case Nil
  then show ?case by simp
next
  case (snoc p xs)
  have sorted_xs: "sorted_wrt (<) xs"
    using snoc.prems(1) by (simp add: sorted_wrt_append)
  have stack_sorted: "sorted_wrt (<) (rev (scan_stack xs))"
    using scan_stack_strict_sorted_increasing[OF sorted_xs] .
  have below: "\<And>q. q \<in> set (scan_stack xs) \<Longrightarrow> q < p"
  proof -
    fix q
    assume "q \<in> set (scan_stack xs)"
    then have "q \<in> set xs"
      using set_scan_stack_subset[of xs] by blast
    then show "q < p"
      using snoc.prems(1) by (simp add: sorted_wrt_append)
  qed
  have push_dom:
    "\<And>z. z \<in> insert p (set (scan_stack xs)) \<Longrightarrow>
      \<exists>y\<in>set (scan_push (scan_stack xs) p). support_value v z \<le> support_value v y"
    using scan_push_support_dominates_increasing[OF stack_sorted below neg] by blast
  show ?case
  proof (cases "x = p")
    case True
    then show ?thesis
      using push_dom[of p] by (simp add: scan_stack_def)
  next
    case False
    then have x_in_xs: "x \<in> set xs"
      using snoc.prems(2) by auto
    obtain z where z_set: "z \<in> set (scan_stack xs)"
      and z_ge: "support_value v x \<le> support_value v z"
      using snoc.IH[OF sorted_xs x_in_xs] by blast
    obtain y where y_set: "y \<in> set (scan_push (scan_stack xs) p)"
      and y_ge: "support_value v z \<le> support_value v y"
      using push_dom[of z] z_set by auto
    have xy_ge: "support_value v x \<le> support_value v y"
      by (rule order_trans[OF z_ge y_ge])
    show ?thesis
      using y_set xy_ge by (auto simp: scan_stack_def)
  qed
qed

lemma scan_chain_support_dominates_increasing:
  fixes xs :: "real point list"
  assumes "sorted_wrt (<) xs" and "snd v < 0" and "x \<in> set xs"
  shows "\<exists>y\<in>set (scan_chain xs). support_value v x \<le> support_value v y"
  using scan_stack_support_dominates_increasing[OF assms]
  by (simp add: scan_chain_def)

lemma sorted_wrt_less_sorted_unique [simp]:
  "sorted_wrt (<) (sorted_unique (xs :: 'a::linorder list))"
  by (simp add: strict_sorted_iff)

lemma lower_hull_supports_negative:
  assumes "snd v < 0" and "x \<in> set ps"
  shows "\<exists>y\<in>set (lower_hull ps). support_value v x \<le> support_value v y"
  using scan_chain_support_dominates_increasing[of "sorted_unique ps" v x] assms
  by (simp add: lower_hull_def)

lemma scan_push_strict_sorted_decreasing:
  fixes st :: "real point list"
  assumes sorted: "sorted_wrt (>) (rev st)"
    and above: "\<And>q. q \<in> set st \<Longrightarrow> p < q"
  shows "sorted_wrt (>) (rev (scan_push st p))"
  using sorted above
  by (induction st p rule: scan_push.induct) (auto simp: sorted_wrt_append)

lemma scan_stack_strict_sorted_decreasing:
  fixes xs :: "real point list"
  assumes "sorted_wrt (>) xs"
  shows "sorted_wrt (>) (rev (scan_stack xs))"
  using assms unfolding scan_stack_def
proof (induction xs rule: rev_induct)
  case Nil
  then show ?case by simp
next
  case (snoc p xs)
  have sorted_xs: "sorted_wrt (>) xs"
    using snoc.prems by (simp add: sorted_wrt_append)
  have above: "\<And>q. q \<in> set (foldl scan_push [] xs) \<Longrightarrow> p < q"
  proof -
    fix q
    assume "q \<in> set (foldl scan_push [] xs)"
    then have "q \<in> set xs"
      using set_scan_stack_subset[of xs] by (auto simp: scan_stack_def)
    then show "p < q"
      using snoc.prems by (simp add: sorted_wrt_append)
  qed
  show ?case
    using scan_push_strict_sorted_decreasing[OF snoc.IH[OF sorted_xs] above] by simp
qed

lemma scan_push_support_dominates_decreasing_step:
  fixes q r p x :: "real point" and st :: "real point list"
  assumes tail_dom:
    "cross r q p \<le> 0 \<Longrightarrow>
      (\<And>x. x \<in> insert p (set (r # st)) \<Longrightarrow>
        \<exists>y\<in>set (scan_push (r # st) p). support_value v x \<le> support_value v y)"
    and sorted: "sorted_wrt (>) (rev (q # r # st))"
    and above: "\<And>z. z \<in> set (q # r # st) \<Longrightarrow> p < z"
    and pos: "0 < snd v"
    and x_in: "x \<in> insert p (set (q # r # st))"
  shows "\<exists>y\<in>set (scan_push (q # r # st) p). support_value v x \<le> support_value v y"
proof (cases "cross r q p \<le> 0")
  case False
  have "x \<in> set (scan_push (q # r # st) p)"
    using False x_in by simp
  then show ?thesis
    by (intro bexI[where x = x]) simp_all
next
  case True
  show ?thesis
  proof (cases "x = q")
    case False
    then have x_tail: "x \<in> insert p (set (r # st))"
      using x_in by auto
    obtain y where y_set: "y \<in> set (scan_push (r # st) p)"
      and y_ge: "support_value v x \<le> support_value v y"
      using tail_dom[OF True x_tail] by auto
    have "scan_push (q # r # st) p = scan_push (r # st) p"
      using True by simp
    then show ?thesis
      using y_set y_ge by auto
  next
    case True_x: True
    have pq: "p < q"
      using above by simp
    have qr: "q < r"
      using sorted by (simp add: sorted_wrt_append)
    have q_le: "support_value v q \<le> max (support_value v r) (support_value v p)"
      using support_middle_le_max_decreasing[OF pq qr True pos] .
    obtain yr where yr_set: "yr \<in> set (scan_push (r # st) p)"
      and yr_ge: "support_value v r \<le> support_value v yr"
      using tail_dom[OF True, of r] by auto
    obtain yp where yp_set: "yp \<in> set (scan_push (r # st) p)"
      and yp_ge: "support_value v p \<le> support_value v yp"
      using tail_dom[OF True, of p] by auto
    have "support_value v q \<le> support_value v r \<or>
        support_value v q \<le> support_value v p"
      using q_le by (simp add: max_def split: if_splits)
    then show ?thesis
    proof
      assume "support_value v q \<le> support_value v r"
      then have "support_value v q \<le> support_value v yr"
        using yr_ge by (rule order_trans)
      then have "support_value v x \<le> support_value v yr"
        using True_x by simp
      then show ?thesis
        using True yr_set by (intro bexI[where x = yr]) simp_all
    next
      assume "support_value v q \<le> support_value v p"
      then have "support_value v q \<le> support_value v yp"
        using yp_ge by (rule order_trans)
      then have "support_value v x \<le> support_value v yp"
        using True_x by simp
      then show ?thesis
        using True yp_set by (intro bexI[where x = yp]) simp_all
    qed
  qed
qed

lemma scan_push_support_dominates_decreasing:
  fixes st :: "real point list"
  shows "sorted_wrt (>) (rev st) \<Longrightarrow>
    (\<And>q. q \<in> set st \<Longrightarrow> p < q) \<Longrightarrow>
    0 < snd v \<Longrightarrow>
    x \<in> insert p (set st) \<Longrightarrow>
    \<exists>y\<in>set (scan_push st p). support_value v x \<le> support_value v y"
proof (induction st p arbitrary: x rule: scan_push.induct)
  case (1 p)
  then show ?case by auto
next
  case (2 q p)
  then show ?case by auto
next
  case (3 q r st p)
  have sorted_tail: "sorted_wrt (>) (rev (r # st))"
    using "3.prems"(1) by (simp add: sorted_wrt_append)
  have above_tail: "\<And>w. w \<in> set (r # st) \<Longrightarrow> p < w"
    using "3.prems"(2) by simp
  have pos: "0 < snd v"
    using "3.prems"(3) .
  have tail_dom:
    "cross r q p \<le> 0 \<Longrightarrow>
      (\<And>z. z \<in> insert p (set (r # st)) \<Longrightarrow>
        \<exists>y\<in>set (scan_push (r # st) p). support_value v z \<le> support_value v y)"
    using "3.IH"[OF _ sorted_tail above_tail pos] by blast
  have sorted: "sorted_wrt (>) (rev (q # r # st))"
    using "3.prems"(1) .
  have above: "\<And>z. z \<in> set (q # r # st) \<Longrightarrow> p < z"
    using "3.prems"(2) .
  have x_in: "x \<in> insert p (set (q # r # st))"
    using "3.prems"(4) .
  show ?case
    by (rule scan_push_support_dominates_decreasing_step[
        OF tail_dom sorted above pos x_in])
qed

lemma scan_stack_support_dominates_decreasing:
  fixes xs :: "real point list"
  assumes sorted: "sorted_wrt (>) xs"
    and pos: "0 < snd v"
    and x: "x \<in> set xs"
  shows "\<exists>y\<in>set (scan_stack xs). support_value v x \<le> support_value v y"
  using sorted x
proof (induction xs arbitrary: x rule: rev_induct)
  case Nil
  then show ?case by simp
next
  case (snoc p xs)
  have sorted_xs: "sorted_wrt (>) xs"
    using snoc.prems(1) by (simp add: sorted_wrt_append)
  have stack_sorted: "sorted_wrt (>) (rev (scan_stack xs))"
    using scan_stack_strict_sorted_decreasing[OF sorted_xs] .
  have above: "\<And>q. q \<in> set (scan_stack xs) \<Longrightarrow> p < q"
  proof -
    fix q
    assume "q \<in> set (scan_stack xs)"
    then have "q \<in> set xs"
      using set_scan_stack_subset[of xs] by blast
    then show "p < q"
      using snoc.prems(1) by (simp add: sorted_wrt_append)
  qed
  have push_dom:
    "\<And>z. z \<in> insert p (set (scan_stack xs)) \<Longrightarrow>
      \<exists>y\<in>set (scan_push (scan_stack xs) p). support_value v z \<le> support_value v y"
    using scan_push_support_dominates_decreasing[OF stack_sorted above pos] by blast
  show ?case
  proof (cases "x = p")
    case True
    then show ?thesis
      using push_dom[of p] by (simp add: scan_stack_def)
  next
    case False
    then have x_in_xs: "x \<in> set xs"
      using snoc.prems(2) by auto
    obtain z where z_set: "z \<in> set (scan_stack xs)"
      and z_ge: "support_value v x \<le> support_value v z"
      using snoc.IH[OF sorted_xs x_in_xs] by blast
    obtain y where y_set: "y \<in> set (scan_push (scan_stack xs) p)"
      and y_ge: "support_value v z \<le> support_value v y"
      using push_dom[of z] z_set by auto
    have xy_ge: "support_value v x \<le> support_value v y"
      by (rule order_trans[OF z_ge y_ge])
    show ?thesis
      using y_set xy_ge by (auto simp: scan_stack_def)
  qed
qed

lemma scan_chain_support_dominates_decreasing:
  fixes xs :: "real point list"
  assumes "sorted_wrt (>) xs" and "0 < snd v" and "x \<in> set xs"
  shows "\<exists>y\<in>set (scan_chain xs). support_value v x \<le> support_value v y"
  using scan_stack_support_dominates_decreasing[OF assms]
  by (simp add: scan_chain_def)

lemma sorted_wrt_greater_rev_sorted_unique [simp]:
  "sorted_wrt (>) (rev (sorted_unique (xs :: 'a::linorder list)))"
  by (simp add: sorted_wrt_rev strict_sorted_iff)

lemma upper_hull_supports_positive:
  assumes "0 < snd v" and "x \<in> set ps"
  shows "\<exists>y\<in>set (upper_hull ps). support_value v x \<le> support_value v y"
  using scan_chain_support_dominates_decreasing[of "rev (sorted_unique ps)" v x] assms
  by (simp add: upper_hull_def)

theorem lower_hull_sorted:
  fixes ps :: "real point list"
  shows "sorted_wrt (<) (lower_hull ps)"
  using scan_stack_strict_sorted_increasing[of "sorted_unique ps"]
  by (simp add: lower_hull_def scan_chain_def)

theorem upper_hull_sorted:
  fixes ps :: "real point list"
  shows "sorted_wrt (>) (upper_hull ps)"
  using scan_stack_strict_sorted_decreasing[of "rev (sorted_unique ps)"]
  by (simp add: upper_hull_def scan_chain_def)

lemma fst_hd_sorted_unique_le:
  fixes x :: "real point"
  assumes "x \<in> set ps"
  shows "fst (hd (sorted_unique ps)) \<le> fst x"
proof -
  let ?xs = "sorted_unique ps"
  have xs_ne: "?xs \<noteq> []"
    using assms by auto
  obtain h t where xs: "?xs = h # t"
    using xs_ne by (cases ?xs) auto
  have sorted_xs: "sorted ?xs"
    by simp
  have x_set: "x \<in> set ?xs"
    using assms by simp
  have "h \<le> x"
  proof (cases "x = h")
    case True
    then show ?thesis by simp
  next
    case False
    then have "x \<in> set t"
      using x_set xs by auto
    then show ?thesis
      using sorted_xs xs by (simp add: sorted_simps)
  qed
  then show ?thesis
    by (auto simp: xs less_eq_prod_def)
qed

lemma fst_le_last_sorted_unique:
  fixes x :: "real point"
  assumes "x \<in> set ps"
  shows "fst x \<le> fst (last (sorted_unique ps))"
proof -
  let ?xs = "sorted_unique ps"
  have xs_ne: "?xs \<noteq> []"
    using assms by auto
  have xs_decomp: "?xs = butlast ?xs @ [last ?xs]"
    using xs_ne by simp
  have x_set: "x \<in> set ?xs"
    using assms by simp
  have sorted_decomp: "sorted (butlast ?xs @ [last ?xs])"
    using xs_decomp by simp
  have "x \<le> last ?xs"
  proof (cases "x = last ?xs")
    case True
    then show ?thesis by simp
  next
    case False
    have "x \<in> set (butlast ?xs @ [last ?xs])"
      using x_set xs_decomp by metis
    then have "x \<in> set (butlast ?xs)"
      using False by simp
    then show ?thesis
      using sorted_decomp by (simp add: sorted_append)
  qed
  then show ?thesis
    by (auto simp: less_eq_prod_def)
qed

lemma hd_sorted_unique_less:
  fixes x :: "real point"
  assumes x: "x \<in> set ps"
    and ne: "x \<noteq> hd (sorted_unique ps)"
  shows "hd (sorted_unique ps) < x"
proof -
  let ?xs = "sorted_unique ps"
  have xs_ne: "?xs \<noteq> []"
    using x by auto
  obtain h t where xs: "?xs = h # t"
    using xs_ne by (cases ?xs) auto
  have sorted_xs: "sorted ?xs"
    by simp
  have x_set: "x \<in> set ?xs"
    using x by simp
  have "h \<le> x"
  proof (cases "x = h")
    case True
    then show ?thesis by simp
  next
    case False
    then have "x \<in> set t"
      using x_set xs by auto
    then show ?thesis
      using sorted_xs xs by (simp add: sorted_simps)
  qed
  moreover have "h \<noteq> x"
    using ne xs by simp
  ultimately show ?thesis
    using xs by simp
qed

lemma less_last_sorted_unique:
  fixes x :: "real point"
  assumes x: "x \<in> set ps"
    and ne: "x \<noteq> last (sorted_unique ps)"
  shows "x < last (sorted_unique ps)"
proof -
  let ?xs = "sorted_unique ps"
  have xs_ne: "?xs \<noteq> []"
    using x by auto
  have xs_decomp: "?xs = butlast ?xs @ [last ?xs]"
    using xs_ne by simp
  have x_set: "x \<in> set ?xs"
    using x by simp
  have sorted_decomp: "sorted (butlast ?xs @ [last ?xs])"
    using xs_decomp by simp
  have "x \<le> last ?xs"
  proof (cases "x = last ?xs")
    case True
    then show ?thesis by simp
  next
    case False
    have "x \<in> set (butlast ?xs @ [last ?xs])"
      using x_set xs_decomp by metis
    then have "x \<in> set (butlast ?xs)"
      using False by simp
    then show ?thesis
      using sorted_decomp by (simp add: sorted_append)
  qed
  then show ?thesis
    using ne by simp
qed

lemma lex_min_strict_support:
  fixes p :: "real point"
  assumes fin: "finite S"
    and lex: "\<And>q. q \<in> S - {p} \<Longrightarrow> p < q"
  shows "\<exists>v. \<forall>q\<in>S - {p}. inner v q < inner v p"
proof -
  let ?T = "{q \<in> S - {p}. snd q < snd p}"
  let ?R = "(\<lambda>q. (fst q - fst p) / (snd p - snd q)) ` ?T"
  let ?M = "insert 1 ?R"
  define e :: real where "e = Min ?M / 2"
  have finite_T: "finite ?T"
    using fin by auto
  have finite_M: "finite ?M"
    using finite_T by auto
  have ratio_pos: "0 < (fst q - fst p) / (snd p - snd q)" if q: "q \<in> ?T" for q
  proof -
    have p_lt_q: "p < q"
      using lex q by auto
    have fst_lt: "fst p < fst q"
      using p_lt_q q
      by (cases p; cases q) (auto simp: less_prod_def')
    have snd_pos: "0 < snd p - snd q"
      using q by simp
    show ?thesis
      using fst_lt snd_pos by simp
  qed
  have M_pos: "\<forall>r\<in>?M. 0 < r"
    using ratio_pos by auto
  have min_pos: "0 < Min ?M"
    using finite_M M_pos by (simp add: Min_gr_iff)
  have e_pos: "0 < e"
    using min_pos by (simp add: e_def)
  have e_lt_ratio: "e < (fst q - fst p) / (snd p - snd q)" if q_T: "q \<in> ?T" for q
  proof -
    have q_R: "(fst q - fst p) / (snd p - snd q) \<in> ?M"
      using finite_T q_T by auto
    have min_le: "Min ?M \<le> (fst q - fst p) / (snd p - snd q)"
      using Min_le[OF finite_M q_R] .
    have half_lt_min: "Min ?M / 2 < Min ?M"
      using min_pos by linarith
    have e_eq: "e = Min ?M / 2"
      by (simp add: e_def)
    show ?thesis
      using min_le half_lt_min e_eq by linarith
  qed
  have strict: "inner (-1, - e) q < inner (-1, - e) p" if q: "q \<in> S - {p}" for q
  proof -
    have p_lt_q: "p < q"
      using lex[OF q] .
    have key: "e * (snd p - snd q) < fst q - fst p"
    proof (cases "snd q < snd p")
      case True
      then have q_T: "q \<in> ?T"
        using q by simp
      have snd_pos: "0 < snd p - snd q"
        using True by simp
      show ?thesis
        using e_lt_ratio[OF q_T] snd_pos by (simp add: pos_less_divide_eq)
    next
      case False
      show ?thesis
      proof (cases "fst p < fst q")
        case True
        have lhs_nonpos: "e * (snd p - snd q) \<le> 0"
          using e_pos False by (intro mult_nonneg_nonpos) linarith+
        then show ?thesis
          using True by linarith
      next
        case False
        have fst_eq: "fst p = fst q"
          using p_lt_q False
          by (cases p; cases q) (auto simp: less_prod_def')
        have snd_lt: "snd p < snd q"
          using p_lt_q fst_eq
          by (cases p; cases q) (auto simp: less_prod_def')
        have lhs_neg: "e * (snd p - snd q) < 0"
          using e_pos snd_lt by (intro mult_pos_neg) linarith+
        then show ?thesis
          using fst_eq by linarith
      qed
    qed
    note key = this
    have key': "e * snd p - e * snd q < fst q - fst p"
    proof -
      have "e * (snd p - snd q) = e * snd p - e * snd q"
        by (simp add: algebra_simps)
      then show ?thesis
        using key by linarith
    qed
    have q_sv: "support_value (-1, - e) q = - fst q - e * snd q"
      by (simp add: support_value_def)
    have p_sv: "support_value (-1, - e) p = - fst p - e * snd p"
      by (simp add: support_value_def)
    have "support_value (-1, - e) q < support_value (-1, - e) p"
      using key' q_sv p_sv by linarith
    then show ?thesis
      by (simp add: support_value_eq_inner)
  qed
  show ?thesis
    using strict by blast
qed

lemma lex_max_strict_support:
  fixes p :: "real point"
  assumes fin: "finite S"
    and lex: "\<And>q. q \<in> S - {p} \<Longrightarrow> q < p"
  shows "\<exists>v. \<forall>q\<in>S - {p}. inner v q < inner v p"
proof -
  have neg_lex: "- p < r" if r: "r \<in> (\<lambda>x. - x) ` S - {- p}" for r
  proof -
    obtain q where q: "q \<in> S" and r_eq: "r = - q"
      using r by auto
    have q_ne: "q \<noteq> p"
      using r r_eq by auto
    have "q < p"
      using lex[of q] q q_ne by auto
    then show ?thesis
      using r_eq by simp
  qed
  obtain v where v: "\<forall>r\<in>(\<lambda>x. - x) ` S - {- p}. inner v r < inner v (- p)"
    using lex_min_strict_support[of "(\<lambda>x. - x) ` S" "- p"] fin neg_lex by auto
  have "\<forall>q\<in>S - {p}. inner (- v) q < inner (- v) p"
  proof
    fix q
    assume q: "q \<in> S - {p}"
    then have "- q \<in> (\<lambda>x. - x) ` S - {- p}"
      by auto
    then have "inner v (- q) < inner v (- p)"
      using v by blast
    then show "inner (- v) q < inner (- v) p"
      by (cases v; cases p; cases q) simp
  qed
  then show ?thesis
    by blast
qed

lemma lower_hull_edge_cross_nonneg_input_if_fst_less:
  fixes ps :: "real point list"
  defines "L \<equiv> lower_hull ps"
  assumes edge: "Suc i < length L"
    and fst_less: "fst (L ! i) < fst (L ! Suc i)"
    and x: "x \<in> set ps"
  shows "0 \<le> cross (L ! i) (L ! Suc i) x"
proof -
  let ?a = "L ! i"
  let ?b = "L ! Suc i"
  let ?v = "(snd ?b - snd ?a, fst ?a - fst ?b)"
  have snd_v: "snd ?v < 0"
    using fst_less by simp
  obtain y where y: "y \<in> set L"
    and x_le_y: "support_value ?v x \<le> support_value ?v y"
    using lower_hull_supports_negative[OF snd_v x] L_def by blast
  have edge_lower: "Suc i < length (lower_hull ps)"
    using edge L_def by simp
  have y_lower: "y \<in> set (lower_hull ps)"
    using y L_def by simp
  have y_side: "0 \<le> cross ?a ?b y"
    using sorted_chain_edge_cross_nonneg_increasing[
        OF lower_hull_sorted lower_hull_turns edge_lower y_lower] L_def
    by simp
  have y_eq: "support_value ?v y = support_value ?v ?a - cross ?a ?b y"
    by (rule support_value_edge_normal)
  have "support_value ?v y \<le> support_value ?v ?a"
    using y_side y_eq by linarith
  then have x_le_a: "support_value ?v x \<le> support_value ?v ?a"
    using x_le_y by linarith
  have x_eq: "support_value ?v x = support_value ?v ?a - cross ?a ?b x"
    by (rule support_value_edge_normal)
  show ?thesis
    using x_le_a x_eq by linarith
qed

lemma upper_hull_edge_cross_nonneg_input_if_fst_greater:
  fixes ps :: "real point list"
  defines "U \<equiv> upper_hull ps"
  assumes edge: "Suc i < length U"
    and fst_greater: "fst (U ! Suc i) < fst (U ! i)"
    and x: "x \<in> set ps"
  shows "0 \<le> cross (U ! i) (U ! Suc i) x"
proof -
  let ?a = "U ! i"
  let ?b = "U ! Suc i"
  let ?v = "(snd ?b - snd ?a, fst ?a - fst ?b)"
  have snd_v: "0 < snd ?v"
    using fst_greater by simp
  obtain y where y: "y \<in> set U"
    and x_le_y: "support_value ?v x \<le> support_value ?v y"
    using upper_hull_supports_positive[OF snd_v x] U_def by blast
  have edge_upper: "Suc i < length (upper_hull ps)"
    using edge U_def by simp
  have y_upper: "y \<in> set (upper_hull ps)"
    using y U_def by simp
  have y_side: "0 \<le> cross ?a ?b y"
    using sorted_chain_edge_cross_nonneg_decreasing[
        OF upper_hull_sorted upper_hull_turns edge_upper y_upper] U_def
    by simp
  have y_eq: "support_value ?v y = support_value ?v ?a - cross ?a ?b y"
    by (rule support_value_edge_normal)
  have "support_value ?v y \<le> support_value ?v ?a"
    using y_side y_eq by linarith
  then have x_le_a: "support_value ?v x \<le> support_value ?v ?a"
    using x_le_y by linarith
  have x_eq: "support_value ?v x = support_value ?v ?a - cross ?a ?b x"
    by (rule support_value_edge_normal)
  show ?thesis
    using x_le_a x_eq by linarith
qed

lemma lower_hull_vertical_edge_last:
  fixes ps :: "real point list"
  defines "L \<equiv> lower_hull ps"
  assumes edge: "Suc i < length L"
    and same_x: "fst (L ! i) = fst (L ! Suc i)"
  shows "Suc i = length L - 1"
proof (rule ccontr)
  assume not_last: "Suc i \<noteq> length L - 1"
  have next_len: "Suc (Suc i) < length L"
    using edge not_last by linarith
  have sorted_L: "sorted_wrt (<) L"
    using lower_hull_sorted L_def by simp
  have turns_L: "chain_turns L"
    using lower_hull_turns L_def by simp
  have a_lt_b: "L ! i < L ! Suc i"
    using sorted_wrt_nth_less[OF sorted_L, of i "Suc i"] edge by simp
  have b_lt_c: "L ! Suc i < L ! Suc (Suc i)"
    using sorted_wrt_nth_less[OF sorted_L, of "Suc i" "Suc (Suc i)"] next_len by simp
  have snd_lt: "snd (L ! i) < snd (L ! Suc i)"
    using a_lt_b same_x
    by (cases "L ! i"; cases "L ! Suc i") (auto simp: less_prod_def')
  have fst_le: "fst (L ! Suc i) \<le> fst (L ! Suc (Suc i))"
    using b_lt_c
    by (cases "L ! Suc i"; cases "L ! Suc (Suc i)")
      (auto simp: less_prod_def' less_eq_prod_def)
  have prod_nonneg:
    "0 \<le> (snd (L ! Suc i) - snd (L ! i)) *
        (fst (L ! Suc (Suc i)) - fst (L ! i))"
    using snd_lt fst_le same_x by (intro mult_nonneg_nonneg) linarith+
  have cross_nonpos: "cross (L ! i) (L ! Suc i) (L ! Suc (Suc i)) \<le> 0"
    using same_x prod_nonneg
    by (cases "L ! i"; cases "L ! Suc i"; cases "L ! Suc (Suc i)")
      (simp add: cross_def algebra_simps)
  have "0 < cross (L ! i) (L ! Suc i) (L ! Suc (Suc i))"
    by (rule sorted_chain_cross_nth_increasing[OF sorted_L turns_L _ _ next_len]) simp_all
  then show False
    using cross_nonpos by linarith
qed

lemma upper_hull_vertical_edge_last:
  fixes ps :: "real point list"
  defines "U \<equiv> upper_hull ps"
  assumes edge: "Suc i < length U"
    and same_x: "fst (U ! i) = fst (U ! Suc i)"
  shows "Suc i = length U - 1"
proof (rule ccontr)
  assume not_last: "Suc i \<noteq> length U - 1"
  have next_len: "Suc (Suc i) < length U"
    using edge not_last by linarith
  have sorted_U: "sorted_wrt (>) U"
    using upper_hull_sorted U_def by simp
  have turns_U: "chain_turns U"
    using upper_hull_turns U_def by simp
  have b_lt_a: "U ! Suc i < U ! i"
    using sorted_wrt_nth_less[OF sorted_U, of i "Suc i"] edge by simp
  have c_lt_b: "U ! Suc (Suc i) < U ! Suc i"
    using sorted_wrt_nth_less[OF sorted_U, of "Suc i" "Suc (Suc i)"] next_len by simp
  have snd_lt: "snd (U ! Suc i) < snd (U ! i)"
    using b_lt_a same_x
    by (cases "U ! i"; cases "U ! Suc i") (auto simp: less_prod_def')
  have fst_le: "fst (U ! Suc (Suc i)) \<le> fst (U ! Suc i)"
    using c_lt_b
    by (cases "U ! Suc (Suc i)"; cases "U ! Suc i")
      (auto simp: less_prod_def' less_eq_prod_def)
  have prod_nonneg:
    "0 \<le> (snd (U ! Suc i) - snd (U ! i)) *
        (fst (U ! Suc (Suc i)) - fst (U ! i))"
    using snd_lt fst_le same_x by (intro mult_nonpos_nonpos) linarith+
  have cross_nonpos: "cross (U ! i) (U ! Suc i) (U ! Suc (Suc i)) \<le> 0"
    using same_x prod_nonneg
    by (cases "U ! i"; cases "U ! Suc i"; cases "U ! Suc (Suc i)")
      (simp add: cross_def algebra_simps)
  have "0 < cross (U ! i) (U ! Suc i) (U ! Suc (Suc i))"
    by (rule sorted_chain_cross_nth_decreasing[OF sorted_U turns_U _ _ next_len]) simp_all
  then show False
    using cross_nonpos by linarith
qed

lemma lower_hull_edge_cross_nonneg_input:
  fixes ps :: "real point list"
  defines "L \<equiv> lower_hull ps"
  assumes edge: "Suc i < length L"
    and x: "x \<in> set ps"
  shows "0 \<le> cross (L ! i) (L ! Suc i) x"
proof (cases "fst (L ! i) < fst (L ! Suc i)")
  case True
  then show ?thesis
    using lower_hull_edge_cross_nonneg_input_if_fst_less[where ps=ps and i=i and x=x]
      edge x L_def
    by simp
next
  case False
  have sorted_L: "sorted_wrt (<) L"
    using lower_hull_sorted L_def by simp
  have a_lt_b: "L ! i < L ! Suc i"
    using sorted_wrt_nth_less[OF sorted_L, of i "Suc i"] edge by simp
  have same_x: "fst (L ! i) = fst (L ! Suc i)"
    using a_lt_b False
    by (cases "L ! i"; cases "L ! Suc i") (auto simp: less_prod_def')
  have snd_lt: "snd (L ! i) < snd (L ! Suc i)"
    using a_lt_b same_x
    by (cases "L ! i"; cases "L ! Suc i") (auto simp: less_prod_def')
  have last_edge: "Suc i = length L - 1"
    using lower_hull_vertical_edge_last[where ps=ps and i=i] edge same_x L_def by simp
  have ps_ne: "ps \<noteq> []"
    using x by auto
  have b_last: "L ! Suc i = last L"
  proof -
    have L_ne: "L \<noteq> []"
      using edge by auto
    have "last L = L ! (length L - 1)"
      using L_ne by (rule last_conv_nth)
    then show ?thesis
      using last_edge by simp
  qed
  have b_su: "L ! Suc i = last (sorted_unique ps)"
    using b_last last_lower_hull[OF ps_ne] L_def by simp
  have fst_x_le: "fst x \<le> fst (L ! Suc i)"
    using fst_le_last_sorted_unique[OF x] b_su by simp
  have prod_nonpos:
    "(snd (L ! Suc i) - snd (L ! i)) * (fst x - fst (L ! i)) \<le> 0"
    using snd_lt fst_x_le same_x by (intro mult_nonneg_nonpos) linarith+
  show ?thesis
    using same_x prod_nonpos
    by (cases "L ! i"; cases "L ! Suc i"; cases x)
      (simp add: cross_def algebra_simps)
qed

lemma upper_hull_edge_cross_nonneg_input:
  fixes ps :: "real point list"
  defines "U \<equiv> upper_hull ps"
  assumes edge: "Suc i < length U"
    and x: "x \<in> set ps"
  shows "0 \<le> cross (U ! i) (U ! Suc i) x"
proof (cases "fst (U ! Suc i) < fst (U ! i)")
  case True
  then show ?thesis
    using upper_hull_edge_cross_nonneg_input_if_fst_greater[where ps=ps and i=i and x=x]
      edge x U_def
    by simp
next
  case False
  have sorted_U: "sorted_wrt (>) U"
    using upper_hull_sorted U_def by simp
  have b_lt_a: "U ! Suc i < U ! i"
    using sorted_wrt_nth_less[OF sorted_U, of i "Suc i"] edge by simp
  have same_x: "fst (U ! i) = fst (U ! Suc i)"
    using b_lt_a False
    by (cases "U ! i"; cases "U ! Suc i") (auto simp: less_prod_def')
  have snd_lt: "snd (U ! Suc i) < snd (U ! i)"
    using b_lt_a same_x
    by (cases "U ! i"; cases "U ! Suc i") (auto simp: less_prod_def')
  have last_edge: "Suc i = length U - 1"
    using upper_hull_vertical_edge_last[where ps=ps and i=i] edge same_x U_def by simp
  have ps_ne: "ps \<noteq> []"
    using x by auto
  have b_last: "U ! Suc i = last U"
  proof -
    have U_ne: "U \<noteq> []"
      using edge by auto
    have "last U = U ! (length U - 1)"
      using U_ne by (rule last_conv_nth)
    then show ?thesis
      using last_edge by simp
  qed
  have b_su: "U ! Suc i = hd (sorted_unique ps)"
    using b_last last_upper_hull[OF ps_ne] U_def by simp
  have fst_le_x: "fst (U ! Suc i) \<le> fst x"
    using fst_hd_sorted_unique_le[OF x] b_su by simp
  have prod_nonpos:
    "(snd (U ! Suc i) - snd (U ! i)) * (fst x - fst (U ! i)) \<le> 0"
    using snd_lt fst_le_x same_x by (intro mult_nonpos_nonneg) linarith+
  show ?thesis
    using same_x prod_nonpos
    by (cases "U ! i"; cases "U ! Suc i"; cases x)
      (simp add: cross_def algebra_simps)
qed

lemma strict_support_from_two_edges:
  fixes a p c :: "real point"
  assumes left: "\<And>q. q \<in> S \<Longrightarrow> 0 \<le> cross a p q"
    and right: "\<And>q. q \<in> S \<Longrightarrow> 0 \<le> cross p c q"
    and noncol: "cross a p c \<noteq> 0"
  shows "\<exists>v. \<forall>q\<in>S - {p}. inner v q < inner v p"
proof -
  let ?v1 = "(snd p - snd a, fst a - fst p)"
  let ?v2 = "(snd c - snd p, fst p - fst c)"
  let ?v = "?v1 + ?v2"
  have strict: "inner ?v q < inner ?v p" if q: "q \<in> S - {p}" for q
  proof -
    have q_S: "q \<in> S" and q_ne: "q \<noteq> p"
      using q by auto
    have c1_nonneg: "0 \<le> cross a p q"
      by (rule left[OF q_S])
    have c2_nonneg: "0 \<le> cross p c q"
      by (rule right[OF q_S])
    have not_both_zero: "cross a p q \<noteq> 0 \<or> cross p c q \<noteq> 0"
    proof (rule ccontr)
      assume "\<not> (cross a p q \<noteq> 0 \<or> cross p c q \<noteq> 0)"
      then have z1: "cross a p q = 0" and z2: "cross p c q = 0"
        by auto
      have "q = p"
        by (rule two_cross_zero_imp_eq_middle[OF z1 z2 noncol])
      then show False
        using q_ne by simp
    qed
    have sum_pos: "0 < cross a p q + cross p c q"
      using c1_nonneg c2_nonneg not_both_zero by linarith
    have q1: "support_value ?v1 q = support_value ?v1 a - cross a p q"
      by (rule support_value_edge_normal)
    have p1_eq: "support_value ?v1 p = support_value ?v1 a - cross a p p"
      by (rule support_value_edge_normal)
    have p1: "support_value ?v1 p = support_value ?v1 a"
      using p1_eq by simp
    have v1_diff: "support_value ?v1 q = support_value ?v1 p - cross a p q"
      using q1 p1 by simp
    have v2_diff: "support_value ?v2 q = support_value ?v2 p - cross p c q"
      by (rule support_value_edge_normal)
    have sum_q: "support_value ?v q = support_value ?v1 q + support_value ?v2 q"
      by (cases ?v1; cases ?v2; cases q) (simp add: support_value_def algebra_simps)
    have sum_p: "support_value ?v p = support_value ?v1 p + support_value ?v2 p"
      by (cases ?v1; cases ?v2; cases p) (simp add: support_value_def algebra_simps)
    show ?thesis
      using v1_diff v2_diff sum_q sum_p sum_pos by (simp add: support_value_eq_inner)
  qed
  show ?thesis
    using strict by blast
qed

lemma lower_hull_interior_strict_support:
  fixes ps :: "real point list"
  defines "L \<equiv> lower_hull ps"
  assumes i_pos: "0 < i"
    and i_len: "Suc i < length L"
  shows "\<exists>v. \<forall>q\<in>set ps - {L ! i}. inner v q < inner v (L ! i)"
proof -
  let ?a = "L ! (i - 1)"
  let ?p = "L ! i"
  let ?c = "L ! Suc i"
  have edge_left: "Suc (i - 1) < length L"
    using i_pos i_len by simp
  have Suc_pred_i: "Suc (i - 1) = i"
    using i_pos by simp
  have turn: "0 < cross ?a ?p ?c"
    using sorted_chain_cross_nth_increasing[
        OF lower_hull_sorted lower_hull_turns, of "i - 1" i "Suc i"] i_pos i_len L_def
    by simp
  show ?thesis
  proof (rule strict_support_from_two_edges[where S="set ps" and a="?a" and p="?p" and c="?c"])
    fix q
    assume q: "q \<in> set ps"
    show "0 \<le> cross ?a ?p q"
      using lower_hull_edge_cross_nonneg_input[where ps=ps and i="i - 1" and x=q]
        edge_left q L_def Suc_pred_i
      by simp
    show "0 \<le> cross ?p ?c q"
      using lower_hull_edge_cross_nonneg_input[where ps=ps and i=i and x=q] i_len q L_def
      by simp
  next
    show "cross ?a ?p ?c \<noteq> 0"
      using turn by linarith
  qed
qed

lemma upper_hull_interior_strict_support:
  fixes ps :: "real point list"
  defines "U \<equiv> upper_hull ps"
  assumes i_pos: "0 < i"
    and i_len: "Suc i < length U"
  shows "\<exists>v. \<forall>q\<in>set ps - {U ! i}. inner v q < inner v (U ! i)"
proof -
  let ?a = "U ! (i - 1)"
  let ?p = "U ! i"
  let ?c = "U ! Suc i"
  have edge_left: "Suc (i - 1) < length U"
    using i_pos i_len by simp
  have Suc_pred_i: "Suc (i - 1) = i"
    using i_pos by simp
  have turn: "0 < cross ?a ?p ?c"
    using sorted_chain_cross_nth_decreasing[
        OF upper_hull_sorted upper_hull_turns, of "i - 1" i "Suc i"] i_pos i_len U_def
    by simp
  show ?thesis
  proof (rule strict_support_from_two_edges[where S="set ps" and a="?a" and p="?p" and c="?c"])
    fix q
    assume q: "q \<in> set ps"
    show "0 \<le> cross ?a ?p q"
      using upper_hull_edge_cross_nonneg_input[where ps=ps and i="i - 1" and x=q]
        edge_left q U_def Suc_pred_i
      by simp
    show "0 \<le> cross ?p ?c q"
      using upper_hull_edge_cross_nonneg_input[where ps=ps and i=i and x=q] i_len q U_def
      by simp
  next
    show "cross ?a ?p ?c \<noteq> 0"
      using turn by linarith
  qed
qed

lemma lower_hull_interior_strict_support_if_fst_less:
  fixes ps :: "real point list"
  defines "L \<equiv> lower_hull ps"
  assumes i_pos: "0 < i"
    and i_len: "Suc i < length L"
    and fst_left: "fst (L ! (i - 1)) < fst (L ! i)"
    and fst_right: "fst (L ! i) < fst (L ! Suc i)"
  shows "\<exists>v. \<forall>q\<in>set ps - {L ! i}. inner v q < inner v (L ! i)"
proof -
  let ?a = "L ! (i - 1)"
  let ?p = "L ! i"
  let ?c = "L ! Suc i"
  let ?v1 = "(snd ?p - snd ?a, fst ?a - fst ?p)"
  let ?v2 = "(snd ?c - snd ?p, fst ?p - fst ?c)"
  let ?v = "?v1 + ?v2"
  have edge_left: "Suc (i - 1) < length L"
    using i_pos i_len by simp
  have Suc_pred_i: "Suc (i - 1) = i"
    using i_pos by simp
  have turn: "0 < cross ?a ?p ?c"
    using sorted_chain_cross_nth_increasing[
        OF lower_hull_sorted lower_hull_turns, of "i - 1" i "Suc i"] i_pos i_len L_def
    by simp
  have strict: "inner ?v q < inner ?v ?p" if q: "q \<in> set ps - {?p}" for q
  proof -
    have q_ps: "q \<in> set ps" and q_ne: "q \<noteq> ?p"
      using q by auto
    have c1_nonneg: "0 \<le> cross ?a ?p q"
      using lower_hull_edge_cross_nonneg_input_if_fst_less[
          where ps=ps and i="i - 1" and x=q] edge_left fst_left q_ps L_def
      using Suc_pred_i by simp
    have c2_nonneg: "0 \<le> cross ?p ?c q"
      using lower_hull_edge_cross_nonneg_input_if_fst_less[
          where ps=ps and i=i and x=q] i_len fst_right q_ps L_def
      by simp
    have not_both_zero: "cross ?a ?p q \<noteq> 0 \<or> cross ?p ?c q \<noteq> 0"
    proof (rule ccontr)
      assume "\<not> (cross ?a ?p q \<noteq> 0 \<or> cross ?p ?c q \<noteq> 0)"
      then have z1: "cross ?a ?p q = 0" and z2: "cross ?p ?c q = 0"
        by auto
      have nz: "cross ?a ?p ?c \<noteq> 0"
        using turn by linarith
      have "q = ?p"
        by (rule two_cross_zero_imp_eq_middle[OF z1 z2 nz])
      then show False
        using q_ne by simp
    qed
    have sum_pos: "0 < cross ?a ?p q + cross ?p ?c q"
      using c1_nonneg c2_nonneg not_both_zero by linarith
    have q1: "support_value ?v1 q = support_value ?v1 ?a - cross ?a ?p q"
      by (rule support_value_edge_normal)
    have p1_eq: "support_value ?v1 ?p = support_value ?v1 ?a - cross ?a ?p ?p"
      by (rule support_value_edge_normal)
    have p1: "support_value ?v1 ?p = support_value ?v1 ?a"
      using p1_eq by simp
    have v1_diff: "support_value ?v1 q = support_value ?v1 ?p - cross ?a ?p q"
      using q1 p1 by simp
    have v2_diff: "support_value ?v2 q = support_value ?v2 ?p - cross ?p ?c q"
      by (rule support_value_edge_normal)
    have sum_q: "support_value ?v q = support_value ?v1 q + support_value ?v2 q"
      by (cases ?v1; cases ?v2; cases q) (simp add: support_value_def algebra_simps)
    have sum_p: "support_value ?v ?p = support_value ?v1 ?p + support_value ?v2 ?p"
      by (cases ?v1; cases ?v2; cases ?p) (simp add: support_value_def algebra_simps)
    show ?thesis
      using v1_diff v2_diff sum_q sum_p sum_pos by (simp add: support_value_eq_inner)
  qed
  show ?thesis
    using strict by blast
qed

lemma hd_sorted_unique_mem_andrew_hull:
  assumes "ps \<noteq> []"
  shows "hd (sorted_unique ps) \<in> set (andrew_hull ps)"
proof -
  have lower_ne: "lower_hull ps \<noteq> []"
    using assms lower_hull_nonempty by blast
  then have "hd (lower_hull ps) \<in> set (lower_hull ps)"
    by (cases "lower_hull ps") auto
  then show ?thesis
    using hd_lower_hull[OF assms] set_andrew_hull[of ps] by auto
qed

lemma last_sorted_unique_mem_andrew_hull:
  assumes "ps \<noteq> []"
  shows "last (sorted_unique ps) \<in> set (andrew_hull ps)"
proof -
  have lower_ne: "lower_hull ps \<noteq> []"
    using assms lower_hull_nonempty by blast
  then have "last (lower_hull ps) \<in> set (lower_hull ps)"
    by (cases "lower_hull ps") auto
  then show ?thesis
    using last_lower_hull[OF assms] set_andrew_hull[of ps] by auto
qed

lemma andrew_hull_supports_horizontal:
  assumes x: "x \<in> set ps" and horizontal: "snd v = 0"
  shows "\<exists>y\<in>set (andrew_hull ps). support_value v x \<le> support_value v y"
proof (cases "0 \<le> fst v")
  case True
  let ?y = "last (sorted_unique ps)"
  have ps_ne: "ps \<noteq> []"
    using x by auto
  have y_set: "?y \<in> set (andrew_hull ps)"
    using last_sorted_unique_mem_andrew_hull[OF ps_ne] .
  have fst_le: "fst x \<le> fst ?y"
    using fst_le_last_sorted_unique[OF x] .
  have "support_value v x \<le> support_value v ?y"
    using True fst_le horizontal
    by (simp add: support_value_def mult_left_mono)
  then show ?thesis
    using y_set by blast
next
  case False
  let ?y = "hd (sorted_unique ps)"
  have ps_ne: "ps \<noteq> []"
    using x by auto
  have y_set: "?y \<in> set (andrew_hull ps)"
    using hd_sorted_unique_mem_andrew_hull[OF ps_ne] .
  have fst_le: "fst ?y \<le> fst x"
    using fst_hd_sorted_unique_le[OF x] .
  have fst_neg: "fst v < 0"
    using False by simp
  have "support_value v x \<le> support_value v ?y"
    using fst_le fst_neg horizontal
    by (simp add: support_value_def mult_left_mono_neg)
  then show ?thesis
    using y_set by blast
qed

lemma andrew_hull_supports:
  assumes x: "x \<in> set ps"
  shows "\<exists>y\<in>set (andrew_hull ps). support_value v x \<le> support_value v y"
proof (cases "snd v < 0")
  case True
  obtain y where "y \<in> set (lower_hull ps)"
    and "support_value v x \<le> support_value v y"
    using lower_hull_supports_negative[OF True x] by blast
  then show ?thesis
    using set_andrew_hull[of ps] by auto
next
  case False
  then show ?thesis
  proof (cases "0 < snd v")
    case True
    obtain y where "y \<in> set (upper_hull ps)"
      and "support_value v x \<le> support_value v y"
      using upper_hull_supports_positive[OF True x] by blast
    then show ?thesis
      using set_andrew_hull[of ps] by auto
  next
    case False
    then have "snd v = 0"
      using \<open>\<not> snd v < 0\<close> by simp
    then show ?thesis
      using andrew_hull_supports_horizontal[OF x] by blast
  qed
qed

declare support_value_eq_inner [simp]

theorem andrew_hull_covers_input:
  fixes ps :: "real point list"
  shows "set ps \<subseteq> convex hull set (andrew_hull ps)"
proof
  fix x
  assume x: "x \<in> set ps"
  let ?S = "convex hull set (andrew_hull ps)"
  show "x \<in> ?S"
  proof (rule ccontr)
    assume x_not: "x \<notin> ?S"
    have closed_S: "closed ?S"
      using finite_imp_compact_convex_hull[of "set (andrew_hull ps)"]
      by (simp add: compact_imp_closed)
    obtain a b where ax_lt: "inner a x < b"
      and S_gt: "\<And>y. y \<in> ?S \<Longrightarrow> b < inner a y"
      using separating_hyperplane_closed_point[OF convex_convex_hull closed_S x_not]
      by auto
    obtain y where y_set: "y \<in> set (andrew_hull ps)"
      and support: "support_value (- a) x \<le> support_value (- a) y"
      using andrew_hull_supports[OF x, of "- a"] by auto
    have y_in_S: "y \<in> ?S"
      using y_set by (simp add: hull_inc)
    have "inner a y \<le> inner a x"
      using support by simp
    then show False
      using ax_lt S_gt[OF y_in_S] by linarith
  qed
qed

theorem andrew_hull_correct:
  fixes ps :: "real point list"
  shows "convex_hull_correct ps (andrew_hull ps)"
  using andrew_hull_covers_input[of ps]
  by (rule andrew_hull_correctI)

lemma andrew_hull_point_strict_support:
  fixes ps :: "real point list"
  assumes p: "p \<in> set (andrew_hull ps)"
  shows "\<exists>v. \<forall>q\<in>set (andrew_hull ps) - {p}. inner v q < inner v p"
proof -
  let ?S = "set (andrew_hull ps)"
  let ?lo = "hd (sorted_unique ps)"
  let ?hi = "last (sorted_unique ps)"
  have p_ps: "p \<in> set ps"
    using p andrew_hull_subset[of ps] by auto
  then have ps_ne: "ps \<noteq> []"
    by auto
  show ?thesis
  proof (cases "p = ?lo")
    case True
    have "\<exists>v. \<forall>q\<in>?S - {?lo}. inner v q < inner v ?lo"
    proof (rule lex_min_strict_support)
      show "finite ?S"
        by simp
      fix q
      assume q: "q \<in> ?S - {?lo}"
      then have q_ps: "q \<in> set ps"
        using andrew_hull_subset[of ps] by auto
      have q_ne: "q \<noteq> ?lo"
        using q by auto
      show "?lo < q"
        by (rule hd_sorted_unique_less[OF q_ps q_ne])
    qed
    then show ?thesis
      using True by simp
  next
    case p_ne_lo: False
    show ?thesis
    proof (cases "p = ?hi")
      case True
      have "\<exists>v. \<forall>q\<in>?S - {?hi}. inner v q < inner v ?hi"
      proof (rule lex_max_strict_support)
        show "finite ?S"
          by simp
        fix q
        assume q: "q \<in> ?S - {?hi}"
        then have q_ps: "q \<in> set ps"
          using andrew_hull_subset[of ps] by auto
        have q_ne: "q \<noteq> ?hi"
          using q by auto
        show "q < ?hi"
          by (rule less_last_sorted_unique[OF q_ps q_ne])
      qed
      then show ?thesis
        using True by simp
    next
      case p_ne_hi: False
      have p_union: "p \<in> set (lower_hull ps) \<or> p \<in> set (upper_hull ps)"
        using p set_andrew_hull[of ps] by auto
      show ?thesis
      proof (cases "p \<in> set (lower_hull ps)")
        case True
        let ?L = "lower_hull ps"
        obtain i where i_len: "i < length ?L" and p_i: "p = ?L ! i"
          using True by (auto simp: in_set_conv_nth)
        have i_pos: "0 < i"
        proof (rule ccontr)
          assume "\<not> 0 < i"
          then have i0: "i = 0"
            by simp
          have "p = hd ?L"
            using p_i i_len i0 by (cases ?L) auto
          also have "\<dots> = ?lo"
            using hd_lower_hull[OF ps_ne] .
          finally show False
            using p_ne_lo by simp
        qed
        have i_suc: "Suc i < length ?L"
        proof (rule ccontr)
          assume not_suc: "\<not> Suc i < length ?L"
          have i_last: "i = length ?L - 1"
            using i_len not_suc by linarith
          have L_ne: "?L \<noteq> []"
            using i_len by auto
          have "last ?L = ?L ! (length ?L - 1)"
            using L_ne by (rule last_conv_nth)
          then have "p = last ?L"
            using p_i i_last by simp
          also have "\<dots> = ?hi"
            using last_lower_hull[OF ps_ne] .
          finally show False
            using p_ne_hi by simp
        qed
        obtain v where strict_ps: "\<forall>q\<in>set ps - {p}. inner v q < inner v p"
          using lower_hull_interior_strict_support[where ps=ps and i=i] i_pos i_suc p_i
          by auto
        have "\<forall>q\<in>?S - {p}. inner v q < inner v p"
          using strict_ps andrew_hull_subset[of ps] by auto
        then show ?thesis
          by blast
      next
        case False
        then have p_upper: "p \<in> set (upper_hull ps)"
          using p_union by auto
        let ?U = "upper_hull ps"
        obtain i where i_len: "i < length ?U" and p_i: "p = ?U ! i"
          using p_upper by (auto simp: in_set_conv_nth)
        have i_pos: "0 < i"
        proof (rule ccontr)
          assume "\<not> 0 < i"
          then have i0: "i = 0"
            by simp
          have "p = hd ?U"
            using p_i i_len i0 by (cases ?U) auto
          also have "\<dots> = ?hi"
            using hd_upper_hull[OF ps_ne] .
          finally show False
            using p_ne_hi by simp
        qed
        have i_suc: "Suc i < length ?U"
        proof (rule ccontr)
          assume not_suc: "\<not> Suc i < length ?U"
          have i_last: "i = length ?U - 1"
            using i_len not_suc by linarith
          have U_ne: "?U \<noteq> []"
            using i_len by auto
          have "last ?U = ?U ! (length ?U - 1)"
            using U_ne by (rule last_conv_nth)
          then have "p = last ?U"
            using p_i i_last by simp
          also have "\<dots> = ?lo"
            using last_upper_hull[OF ps_ne] .
          finally show False
            using p_ne_lo by simp
        qed
        obtain v where strict_ps: "\<forall>q\<in>set ps - {p}. inner v q < inner v p"
          using upper_hull_interior_strict_support[where ps=ps and i=i] i_pos i_suc p_i
          by auto
        have "\<forall>q\<in>?S - {p}. inner v q < inner v p"
          using strict_ps andrew_hull_subset[of ps] by auto
        then show ?thesis
          by blast
      qed
    qed
  qed
qed

theorem andrew_hull_delete_changes_convex_hull:
  fixes ps :: "real point list"
  assumes p: "p \<in> set (andrew_hull ps)"
  shows "convex hull (set (andrew_hull ps) - {p}) \<noteq> convex hull set (andrew_hull ps)"
proof -
  obtain v where strict: "\<forall>q\<in>set (andrew_hull ps) - {p}. inner v q < inner v p"
    using andrew_hull_point_strict_support[OF p] by blast
  show ?thesis
    by (rule strict_support_hull_delete_ne[where p=p and S="set (andrew_hull ps)" and v=v])
      (use p strict in auto)
qed

theorem andrew_hull_irredundant:
  fixes ps :: "real point list"
  shows "convex_hull_irredundant (andrew_hull ps)"
  unfolding convex_hull_irredundant_def
  using andrew_hull_delete_changes_convex_hull[of _ ps] by blast

lemma length_scan_push_le:
  "length (scan_push st p) \<le> Suc (length st)"
  by (induction st p rule: scan_push.induct) auto

lemma length_scan_stack_le:
  "length (scan_stack ps) \<le> length ps"
  unfolding scan_stack_def
proof (induction ps arbitrary: rule: rev_induct)
  case Nil
  then show ?case by simp
next
  case (snoc p ps)
  have "length (foldl scan_push [] (ps @ [p])) \<le> Suc (length (foldl scan_push [] ps))"
    using length_scan_push_le by simp
  also have "\<dots> \<le> Suc (length ps)"
    using snoc.IH by simp
  finally show ?case by simp
qed

lemma length_scan_chain_le:
  "length (scan_chain ps) \<le> length ps"
  by (simp add: scan_chain_def length_scan_stack_le)

lemma length_lower_hull_le:
  "length (lower_hull ps) \<le> card (set ps)"
proof -
  have "length (lower_hull ps) \<le> length (sorted_unique ps)"
    using length_scan_chain_le[of "sorted_unique ps"]
    by (simp add: lower_hull_def)
  also have "\<dots> = card (set ps)"
    by (simp add: sorted_unique_def length_sorted_list_of_set)
  finally show ?thesis .
qed

lemma length_upper_hull_le:
  "length (upper_hull ps) \<le> card (set ps)"
proof -
  have "length (upper_hull ps) \<le> length (rev (sorted_unique ps))"
    using length_scan_chain_le[of "rev (sorted_unique ps)"]
    by (simp add: upper_hull_def)
  also have "\<dots> = card (set ps)"
    by (simp add: sorted_unique_def length_sorted_list_of_set)
  finally show ?thesis .
qed

theorem length_andrew_hull_le_twice_card:
  "length (andrew_hull ps) \<le> 2 * card (set ps)"
proof (cases "sorted_unique ps")
  case Nil
  then have "ps = []"
    by simp
  then show ?thesis
    by (simp add: andrew_hull_def sorted_unique_def)
next
  case (Cons p qs)
  then show ?thesis
  proof (cases qs)
    case Nil
    with Cons have su: "sorted_unique ps = [p]"
      by simp
    then have "set ps = {p}"
      using sorted_unique_singleton_iff by blast
    moreover have "andrew_hull ps = [p]"
      using su by (simp add: andrew_hull_def)
    ultimately show ?thesis
      by simp
  next
    case (Cons q rs)
    have "length (andrew_hull ps) \<le> length (lower_hull ps) + length (upper_hull ps)"
      using Cons \<open>sorted_unique ps = p # qs\<close>
      by (simp add: andrew_hull_def)
    also have "\<dots> \<le> card (set ps) + card (set ps)"
      using length_lower_hull_le[of ps] length_upper_hull_le[of ps] by simp
    finally show ?thesis by simp
  qed
qed

text \<open>
  For inputs with at least two distinct points, the implementation returns
  exactly the standard Andrew concatenation of lower and upper scans.  This
  theorem is often the most convenient way to unfold the top-level algorithm
  without exposing the special empty and singleton cases.
\<close>

theorem andrew_hull_ge2:
  assumes "card (set ps) \<ge> 2"
  shows "andrew_hull ps = butlast (lower_hull ps) @ butlast (upper_hull ps)"
proof -
  have "sorted_unique ps \<noteq> []" and "\<And>p. sorted_unique ps \<noteq> [p]"
    using assms by (auto simp: sorted_unique_singleton_iff card_Suc_eq)
  then show ?thesis
    by (cases "sorted_unique ps") (auto simp: andrew_hull_def split: list.splits)
qed

theorem andrew_hull_ordered_chains:
  fixes ps :: "real point list"
  assumes "2 \<le> card (set ps)"
  shows "andrew_hull ps = butlast (lower_hull ps) @ butlast (upper_hull ps)"
    and "sorted_wrt (<) (lower_hull ps)"
    and "sorted_wrt (>) (upper_hull ps)"
    and "chain_turns (lower_hull ps)"
    and "chain_turns (upper_hull ps)"
proof -
  show "andrew_hull ps = butlast (lower_hull ps) @ butlast (upper_hull ps)"
    using andrew_hull_ge2[OF assms] .
  show "sorted_wrt (<) (lower_hull ps)"
    by (rule lower_hull_sorted)
  show "sorted_wrt (>) (upper_hull ps)"
    by (rule upper_hull_sorted)
  show "chain_turns (lower_hull ps)"
    by (rule lower_hull_turns)
  show "chain_turns (upper_hull ps)"
    by (rule upper_hull_turns)
qed

theorem distinct_andrew_hull_iff:
  fixes ps :: "real point list"
  shows "distinct (andrew_hull ps) \<longleftrightarrow>
    card (set ps) < 2 \<or>
    set (butlast (lower_hull ps)) \<inter> set (butlast (upper_hull ps)) = {}"
proof (cases "card (set ps) < 2")
  case True
  have "distinct (andrew_hull ps)"
  proof (cases "sorted_unique ps")
    case Nil
    then have "ps = []"
      by simp
    then show ?thesis
      by (simp add: andrew_hull_def sorted_unique_def)
  next
    case (Cons p qs)
    then show ?thesis
    proof (cases qs)
      case Nil
      then show ?thesis
        using Cons by (simp add: andrew_hull_def)
    next
      case (Cons q rs)
      have len_su: "length (sorted_unique ps) = card (set ps)"
        by (simp add: sorted_unique_def length_sorted_list_of_set)
      have "2 \<le> card (set ps)"
        using len_su \<open>sorted_unique ps = p # qs\<close> Cons by simp
      then show ?thesis
        using True by simp
    qed
  qed
  then show ?thesis
    using True by simp
next
  case False
  then have ge2: "2 \<le> card (set ps)"
    by simp
  have dL: "distinct (butlast (lower_hull ps))"
    by (rule distinct_butlast[OF distinct_lower_hull])
  have dU: "distinct (butlast (upper_hull ps))"
    by (rule distinct_butlast[OF distinct_upper_hull])
  have "distinct (andrew_hull ps) \<longleftrightarrow>
      set (butlast (lower_hull ps)) \<inter> set (butlast (upper_hull ps)) = {}"
    using andrew_hull_ge2[OF ge2] dL dU
    by (simp add: distinct_append)
  then show ?thesis
    using False by simp
qed

theorem distinct_andrew_hull_if_trimmed_chains_disjoint:
  fixes ps :: "real point list"
  assumes "set (butlast (lower_hull ps)) \<inter> set (butlast (upper_hull ps)) = {}"
  shows "distinct (andrew_hull ps)"
  using assms distinct_andrew_hull_iff[of ps] by auto

subsection \<open>Top-Level Correctness Statement\<close>

text \<open>
  The final theorem collects the specification in one place.  For real-coordinate
  inputs, the returned list consists only of input points, covers every input
  point by its convex hull, has exactly the same convex hull as the input, and
  is irredundant: deleting any returned point changes the convex hull of the
  returned set.  The preceding sortedness and left-turn theorems describe the
  order and shape of the lower and upper scans; they are supporting invariants,
  not a substitute for this envelope and irredundancy specification.

  The irredundancy conjunct is the semantic minimality property for the returned
  vertex set.  It does not merely follow from convex-hull equality; it is proved
  separately by exposing every returned point with a strict supporting
  direction.
\<close>

theorem andrew_hull_correctness:
  fixes ps :: "real point list"
  shows "set (andrew_hull ps) \<subseteq> set ps"
    and "set ps \<subseteq> convex hull set (andrew_hull ps)"
    and "convex hull set (andrew_hull ps) = convex hull set ps"
    and "convex_hull_correct ps (andrew_hull ps)"
    and "convex_hull_irredundant (andrew_hull ps)"
proof -
  show "set (andrew_hull ps) \<subseteq> set ps"
    by (rule andrew_hull_subset)
  show covers: "set ps \<subseteq> convex hull set (andrew_hull ps)"
    by (rule andrew_hull_covers_input)
  show "convex hull set (andrew_hull ps) = convex hull set ps"
    using covers by (rule andrew_hull_convex_hull_eqI)
  show "convex_hull_correct ps (andrew_hull ps)"
    by (rule andrew_hull_correct)
  show "convex_hull_irredundant (andrew_hull ps)"
    by (rule andrew_hull_irredundant)
qed

end
