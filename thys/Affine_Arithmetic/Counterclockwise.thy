section {* Counterclockwise *}
theory Counterclockwise
imports "~~/src/HOL/Multivariate_Analysis/Multivariate_Analysis"
begin
text {*\label{sec:counterclockwise}*}

subsection {* Auxiliary Lemmas *}

lemma convex3_alt:
  fixes x y z::"'a::real_vector"
  assumes "0 \<le> a" "0 \<le> b" "0 \<le> c" "a + b + c = 1"
  obtains u v  where "a *\<^sub>R x + b *\<^sub>R y + c *\<^sub>R z = x + u *\<^sub>R (y - x) + v *\<^sub>R (z - x)"
    and "0 \<le> u" "0 \<le> v" "u + v \<le> 1"
proof -
  from convex_hull_3[of x y z] have "a *\<^sub>R x + b *\<^sub>R y + c *\<^sub>R z \<in> convex hull {x, y, z}"
    using assms by auto
  also note convex_hull_3_alt
  finally obtain u v where "a *\<^sub>R x + b *\<^sub>R y + c *\<^sub>R z = x + u *\<^sub>R (y - x) + v *\<^sub>R (z - x)"
    and uv: "0 \<le> u" "0 \<le> v" "u + v \<le> 1"
    by auto
  thus ?thesis ..
qed

lemma (in ordered_ab_group_add) add_nonpos_eq_0_iff:
  assumes x: "0 \<ge> x" and y: "0 \<ge> y"
  shows "x + y = 0 \<longleftrightarrow> x = 0 \<and> y = 0"
proof -
  from add_nonneg_eq_0_iff[of "-x" "-y"] assms
  have "- (x + y) = 0 \<longleftrightarrow> - x = 0 \<and> - y = 0"
    by simp
  also have "(- (x + y) = 0) = (x + y = 0)" unfolding neg_equal_0_iff_equal ..
  finally show ?thesis by simp
qed

lemma setsum_nonpos_eq_0_iff:
  fixes f :: "'a \<Rightarrow> 'b::ordered_ab_group_add"
  shows "\<lbrakk>finite A; \<forall>x\<in>A. f x \<le> 0\<rbrakk> \<Longrightarrow> setsum f A = 0 \<longleftrightarrow> (\<forall>x\<in>A. f x = 0)"
  by (induct set: finite) (simp_all add: add_nonpos_eq_0_iff setsum_nonpos)

lemma fold_if_in_set:
  "fold (\<lambda>x m. if P x m then x else m) xs x \<in> set (x#xs)"
  by (induct xs arbitrary: x) auto

subsection {* Sort Elements of a List *}

locale linorder_list0 = fixes LE::"'a \<Rightarrow> 'a \<Rightarrow> bool"
begin

definition "MIN a b = (if LE a b then a else b)"

lemma MIN_in[simp]: "x \<in> S \<Longrightarrow> y \<in> S \<Longrightarrow> MIN x y \<in> S"
  by (auto simp: MIN_def)

lemma fold_min_eqI1: "fold MIN ys y \<notin> set ys \<Longrightarrow> fold MIN ys y = y"
  using fold_if_in_set[of _ ys y]
  by (auto simp: MIN_def[abs_def])

function selsort where
  "selsort [] = []"
| "selsort (y#ys) = (let
      xm = fold MIN ys y;
      xs' = List.remove1 xm (y#ys)
    in (xm#selsort xs'))"
  by pat_completeness auto
termination
  by (relation "measure length")
    (auto simp: length_remove1 intro!: fold_min_eqI1 dest!: length_pos_if_in_set)

lemma in_set_selsort_eq: "x \<in> set (selsort xs) \<longleftrightarrow> x \<in> (set xs)"
  by (induct rule: selsort.induct) (auto simp: Let_def intro!: fold_min_eqI1)

lemma set_selsort[simp]: "set (selsort xs) = set xs"
  using in_set_selsort_eq by blast

lemma length_selsort[simp]: "length (selsort xs) = length xs"
proof (induct xs rule: selsort.induct)
  case (2 x xs)
  from 2[OF refl refl]
  show ?case
    unfolding selsort.simps
    by (auto simp: Let_def length_remove1
      simp del: selsort.simps split: split_if_asm
      intro!: Suc_pred
      dest!: fold_min_eqI1)
qed simp

lemma distinct_selsort[simp]: "distinct (selsort xs) = distinct xs"
  by (auto intro!: card_distinct dest!: distinct_card)

lemma selsort_eq_empty_iff[simp]: "selsort xs = [] \<longleftrightarrow> xs = []"
  by (cases xs) (auto simp: Let_def)


inductive sortedP :: "'a list \<Rightarrow> bool" where
  Nil: "sortedP []"
| Cons: "\<forall>y\<in>set ys. LE x y \<Longrightarrow> sortedP ys \<Longrightarrow> sortedP (x # ys)"

inductive_cases
  sortedP_Nil: "sortedP []" and
  sortedP_Cons: "sortedP (x#xs)"
inductive_simps
  sortedP_Nil_iff: "sortedP Nil" and
  sortedP_Cons_iff: "sortedP (Cons x xs)"

lemma sortedP_append_iff:
  "sortedP (xs @ ys) = (sortedP xs & sortedP ys & (\<forall>x \<in> set xs. \<forall>y \<in> set ys. LE x y))"
  by (induct xs) (auto intro!: Nil Cons elim!: sortedP_Cons)

lemma sortedP_appendI:
  "sortedP xs \<Longrightarrow> sortedP ys \<Longrightarrow> (\<And>x y. x \<in> set xs \<Longrightarrow> y \<in> set ys \<Longrightarrow> LE x y) \<Longrightarrow> sortedP (xs @ ys)"
  by (induct xs) (auto intro!: Nil Cons elim!: sortedP_Cons)

lemma sorted_nth_less: "sortedP xs \<Longrightarrow> i < j \<Longrightarrow> j < length xs \<Longrightarrow> LE (xs ! i) (xs ! j)"
  by (induct xs arbitrary: i j) (auto simp: nth_Cons split: nat.split elim!: sortedP_Cons)

lemma sorted_butlastI[intro, simp]: "sortedP xs \<Longrightarrow> sortedP (butlast xs)"
  by (induct xs) (auto simp: elim!: sortedP_Cons intro!: sortedP.Cons dest!: in_set_butlastD)

lemma sortedP_right_of_append1:
  assumes "sortedP (zs@[z])"
  assumes "y \<in> set zs"
  shows "LE y z"
  using assms
  by (induct zs arbitrary: y z) (auto elim!: sortedP_Cons)

lemma sortedP_right_of_last:
  assumes "sortedP zs"
  assumes "y \<in> set zs" "y \<noteq> last zs"
  shows "LE y (last zs)"
  using assms
  apply (intro sortedP_right_of_append1[of "butlast zs" "last zs" y])
  apply (metis append_is_Nil_conv list.distinct(1) snoc_eq_iff_butlast split_list)
  apply (metis List.insert_def append_butlast_last_id insert_Nil list.distinct(1) rotate1.simps(2)
    set_ConsD set_rotate1)
  done

lemma selsort_singleton_iff: "selsort xs = [x] \<longleftrightarrow> xs = [x]"
  by (induct xs) (auto simp: Let_def)

lemma hd_last_sorted:
  assumes "sortedP xs" "length xs > 1"
  shows "LE (hd xs) (last xs)"
proof (cases xs)
  case (Cons y ys)
  note ys = this
  thus ?thesis
    using ys assms
    by (auto elim!: sortedP_Cons)
qed (insert assms, simp)

end

lemma (in comm_monoid_add) listsum_distinct_selsort:
  assumes "distinct xs"
  shows "listsum (linorder_list0.selsort LE xs) = listsum xs"
  using assms
  apply (simp add: distinct_listsum_conv_Setsum linorder_list0.distinct_selsort)
  apply (rule setsum.cong)
  apply (simp add: linorder_list0.set_selsort)
  apply simp
  done

declare linorder_list0.sortedP_Nil_iff[code]
  linorder_list0.sortedP_Cons_iff[code]
  linorder_list0.selsort.simps[code]
  linorder_list0.MIN_def[code]

locale linorder_list = linorder_list0 LE for LE::"'a::ab_group_add \<Rightarrow> _" +
  fixes S
  assumes order_refl: "a \<in> S \<Longrightarrow> LE a a"
  assumes trans': "a \<in> S \<Longrightarrow> b \<in> S \<Longrightarrow> c \<in> S \<Longrightarrow> a \<noteq> b \<Longrightarrow> b \<noteq> c \<Longrightarrow> a \<noteq> c \<Longrightarrow>
    LE a b \<Longrightarrow> LE b c \<Longrightarrow> LE a c"
  assumes antisym: "a \<in> S \<Longrightarrow> b \<in> S \<Longrightarrow> LE a b \<Longrightarrow> LE b a \<Longrightarrow> a = b"
  assumes linear': "a \<in> S \<Longrightarrow> b \<in> S \<Longrightarrow> a \<noteq> b \<Longrightarrow> LE a b \<or> LE b a"
begin

lemma trans: "a \<in> S \<Longrightarrow> b \<in> S \<Longrightarrow> c \<in> S \<Longrightarrow> LE a b \<Longrightarrow> LE b c \<Longrightarrow> LE a c"
  by (cases "a = b" "b = c" "a = c"
    rule: bool.exhaust[case_product bool.exhaust[case_product bool.exhaust]])
    (auto simp: order_refl intro: trans')

lemma linear: "a \<in> S \<Longrightarrow> b \<in> S \<Longrightarrow> LE a b \<or> LE b a"
  by (cases "a = b") (auto simp: linear' order_refl)

lemma MIN_le1: "w \<in> S \<Longrightarrow> y \<in> S \<Longrightarrow> LE (MIN w y) y"
  and MIN_le2: "w \<in> S \<Longrightarrow> y \<in> S \<Longrightarrow> LE (MIN w y) w"
  using linear
  by (auto simp: MIN_def refl)

lemma fold_min:
  assumes "set xs \<subseteq> S"
  shows "list_all (\<lambda>y. LE (fold MIN (tl xs) (hd xs)) y) xs"
proof (cases xs)
  case (Cons y ys)
  hence subset: "set (y#ys) \<subseteq> S" using assms
    by auto
  show ?thesis
    unfolding Cons list.sel
    using subset
  proof (induct ys arbitrary: y)
    case (Cons z zs)
    hence IH: "\<And>y. y \<in> S \<Longrightarrow> list_all (LE (fold MIN zs y)) (y # zs)"
      by simp
    let ?f = "fold MIN zs (MIN z y)"
    have "?f \<in> set ((MIN z y)#zs)"
      unfolding MIN_def[abs_def]
      by (rule fold_if_in_set)
    also have "\<dots> \<subseteq> S" using Cons.prems by auto
    finally have "?f \<in> S" .

    have "LE ?f (MIN z y)"
      using IH[of "MIN z y"] Cons.prems
      by auto
    moreover have "LE (MIN z y) y" "LE (MIN z y) z" using Cons.prems
      by (auto intro!: MIN_le1 MIN_le2)
    ultimately have "LE ?f y" "LE ?f z" using Cons.prems `?f \<in> S`
      by (auto intro!: trans[of ?f "MIN z y"])
    thus ?case
      using IH[of "MIN z y"]
      using Cons.prems
      by auto
  qed (simp add: order_refl)
qed simp

lemma
  sortedP_selsort:
  assumes "set xs \<subseteq> S"
  shows "sortedP (selsort xs)"
  using assms
proof (induction xs rule: selsort.induct)
  case (2 z zs)
  from this fold_min[of "z#zs"]
  show ?case
    by (cases "fold MIN zs z = z")
      (fastforce simp: list_all_iff Let_def
        simp del: remove1.simps
        intro: Cons intro!: 2(1)[OF refl refl]
        dest!: set_rev_mp[OF _ set_remove1_subset])+
qed (auto intro!: Nil)

end


subsection {* Abstract CCW Systems *}

locale ccw_system0 =
  fixes ccw::"'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
    and S::"'a set"
begin

abbreviation "indelta t p q r \<equiv> ccw t q r \<and> ccw p t r \<and> ccw p q t"
abbreviation "insquare p q r s \<equiv> ccw p q r \<and> ccw q r s \<and> ccw r s p \<and> ccw s p q"

end

abbreviation "distinct3 p q r \<equiv> \<not>(p = q \<or> p = r \<or> q = r)"
abbreviation "distinct4 p q r s \<equiv> \<not>(p = q \<or> p = r \<or> p = s \<or> \<not> distinct3 q r s)"
abbreviation "distinct5 p q r s t \<equiv> \<not>(p = q \<or> p = r \<or> p = s \<or> p = t \<or> \<not> distinct4 q r s t)"

abbreviation "in3 S p q r \<equiv> p \<in> S \<and> q \<in> S \<and> r \<in> S"
abbreviation "in4 S p q r s \<equiv> in3 S p q r \<and> s \<in> S"
abbreviation "in5 S p q r s t \<equiv> in4 S p q r s \<and> t \<in> S"

locale ccw_system12 = ccw_system0 +
  assumes cyclic: "ccw p q r \<Longrightarrow> ccw q r p"
  assumes ccw_antisym: "distinct3 p q r \<Longrightarrow> in3 S p q r \<Longrightarrow> ccw p q r \<Longrightarrow> \<not> ccw p r q"

locale ccw_system123 = ccw_system12 +
  assumes nondegenerate: "distinct3 p q r \<Longrightarrow> in3 S p q r \<Longrightarrow> ccw p q r \<or> ccw p r q"
begin

lemma not_ccw_eq: "distinct3 p q r \<Longrightarrow> in3 S p q r \<Longrightarrow> \<not> ccw p q r \<longleftrightarrow> ccw p r q"
  using ccw_antisym nondegenerate by blast

end

locale ccw_system4 = ccw_system123 +
  assumes interior:
    "distinct4 p q r t \<Longrightarrow> in4 S p q r t \<Longrightarrow> ccw t q r \<Longrightarrow> ccw p t r \<Longrightarrow> ccw p q t \<Longrightarrow> ccw p q r"
begin

lemma interior':
  "distinct4 p q r t \<Longrightarrow> in4 S p q r t \<Longrightarrow> ccw p q t \<Longrightarrow> ccw q r t \<Longrightarrow> ccw r p t \<Longrightarrow> ccw p q r"
  by (metis ccw_antisym cyclic interior nondegenerate)

end

locale ccw_system1235' = ccw_system123 +
  assumes dual_transitive:
    "distinct5 p q r s t \<Longrightarrow> in5 S p q r s t \<Longrightarrow>
      ccw s t p \<Longrightarrow> ccw s t q \<Longrightarrow> ccw s t r \<Longrightarrow> ccw t p q \<Longrightarrow> ccw t q r \<Longrightarrow> ccw t p r"

locale ccw_system1235 = ccw_system123 +
  assumes transitive: "distinct5 p q r s t \<Longrightarrow> in5 S p q r s t \<Longrightarrow>
    ccw t s p \<Longrightarrow> ccw t s q \<Longrightarrow> ccw t s r \<Longrightarrow> ccw t p q \<Longrightarrow> ccw t q r \<Longrightarrow> ccw t p r"
begin

lemmas ccw_axioms = cyclic nondegenerate ccw_antisym transitive

sublocale ccw_system1235'
proof (unfold_locales, rule ccontr, goal_cases)
  case prems: (1 p q r s t)
  hence "ccw s p q \<Longrightarrow> ccw s r p"
    by (metis ccw_axioms prems)
  moreover
  have "ccw s r p \<Longrightarrow> ccw s q r"
    by (metis ccw_axioms prems)
  moreover
  have "ccw s q r \<Longrightarrow> ccw s p q"
    by (metis ccw_axioms prems)
  ultimately
  have "ccw s p q \<and> ccw s r p \<and> ccw s q r \<or> ccw s q p \<and> ccw s p r \<and> ccw s r q"
    by (metis ccw_axioms prems)
  thus False
    by (metis ccw_axioms prems)
qed

end

locale ccw_system = ccw_system1235 + ccw_system4

end
