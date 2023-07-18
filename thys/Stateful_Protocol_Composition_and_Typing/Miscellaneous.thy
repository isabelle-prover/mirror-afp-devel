(*  Title:      Miscellaneous.thy
    Author:     Andreas Viktor Hess, DTU
    SPDX-License-Identifier: BSD-3-Clause
*)

section \<open>Miscellaneous Lemmata\<close>
theory Miscellaneous
  imports Main "HOL-Library.Sublist" "HOL-Library.Infinite_Set" "HOL-Library.While_Combinator"
begin

subsection \<open>List: zip, filter, map\<close>
lemma zip_arg_subterm_split:
  assumes "(x,y) \<in> set (zip xs ys)"
  obtains xs' xs'' ys' ys'' where "xs = xs'@x#xs''" "ys = ys'@y#ys''" "length xs' = length ys'"
proof -
  from assms have "\<exists>zs zs' vs vs'. xs = zs@x#zs' \<and> ys = vs@y#vs' \<and> length zs = length vs"
  proof (induction ys arbitrary: xs)
    case (Cons y' ys' xs)
    then obtain x' xs' where x': "xs = x'#xs'"
      by (metis empty_iff list.exhaust list.set(1) set_zip_leftD)
    show ?case
      by (cases "(x, y) \<in> set (zip xs' ys')",
          metis \<open>xs = x'#xs'\<close> Cons.IH[of xs'] Cons_eq_appendI list.size(4),
          use Cons.prems x' in fastforce)
  qed simp
  thus ?thesis using that by blast
qed

lemma zip_arg_index:
  assumes "(x,y) \<in> set (zip xs ys)"
  obtains i where "xs ! i = x" "ys ! i = y" "i < length xs" "i < length ys"
proof -
  obtain xs1 xs2 ys1 ys2 where "xs = xs1@x#xs2" "ys = ys1@y#ys2" "length xs1 = length ys1"
    using zip_arg_subterm_split[OF assms] by moura
  thus ?thesis using nth_append_length[of xs1 x xs2] nth_append_length[of ys1 y ys2] that by simp
qed

lemma in_set_zip_swap: "(x,y) \<in> set (zip xs ys) \<longleftrightarrow> (y,x) \<in> set (zip ys xs)"
unfolding in_set_zip by auto

lemma filter_nth: "i < length (filter P xs) \<Longrightarrow> P (filter P xs ! i)"
using nth_mem by force

lemma list_all_filter_eq: "list_all P xs \<Longrightarrow> filter P xs = xs"
by (metis list_all_iff filter_True)

lemma list_all_filter_nil:
  assumes "list_all P xs"
    and "\<And>x. P x \<Longrightarrow> \<not>Q x"
  shows "filter Q xs = []"
using assms by (induct xs) simp_all

lemma list_all_concat: "list_all (list_all f) P \<longleftrightarrow> list_all f (concat P)"
by (induct P) auto

lemma list_all2_in_set_ex:
  assumes P: "list_all2 P xs ys"
    and x: "x \<in> set xs"
  shows "\<exists>y \<in> set ys. P x y"
proof -
  obtain i where i: "i < length xs" "xs ! i = x" by (meson x in_set_conv_nth)
  have "i < length ys" "P (xs ! i) (ys ! i)"
    using P i(1) by (simp_all add: list_all2_iff list_all2_nthD)
  thus ?thesis using i(2) by auto
qed

lemma list_all2_in_set_ex':
  assumes P: "list_all2 P xs ys"
    and y: "y \<in> set ys"
  shows "\<exists>x \<in> set xs. P x y"
proof -
  obtain i where i: "i < length ys" "ys ! i = y" by (meson y in_set_conv_nth)
  have "i < length xs" "P (xs ! i) (ys ! i)"
    using P i(1) by (simp_all add: list_all2_iff list_all2_nthD)
  thus ?thesis using i(2) by auto
qed

lemma list_all2_sym:
  assumes "\<And>x y. P x y \<Longrightarrow> P y x"
    and "list_all2 P xs ys"
  shows "list_all2 P ys xs"
using assms(2) by (induct rule: list_all2_induct) (simp_all add: assms(1))

lemma map_upt_index_eq:
  assumes "j < length xs"
  shows "(map (\<lambda>i. xs ! is i) [0..<length xs]) ! j = xs ! is j"
using assms by (simp add: map_nth)

lemma map_snd_list_insert_distrib:
  assumes "\<forall>(i,p) \<in> insert x (set xs). \<forall>(i',p') \<in> insert x (set xs). p = p' \<longrightarrow> i = i'"
  shows "map snd (List.insert x xs) = List.insert (snd x) (map snd xs)"
using assms
proof (induction xs rule: List.rev_induct)
  case (snoc y xs)
  hence IH: "map snd (List.insert x xs) = List.insert (snd x) (map snd xs)" by fastforce

  obtain iy py where y: "y = (iy,py)" by (metis surj_pair)
  obtain ix px where x: "x = (ix,px)" by (metis surj_pair)

  have "(ix,px) \<in> insert x (set (y#xs))" "(iy,py) \<in> insert x (set (y#xs))" using y x by auto
  hence *: "iy = ix" when "py = px" using that snoc.prems by auto

  show ?case
  proof (cases "px = py")
    case True
    hence "y = x" using * y x by auto
    thus ?thesis using IH by simp
  next
    case False
    hence "y \<noteq> x" using y x by simp
    have "List.insert x (xs@[y]) = (List.insert x xs)@[y]"
    proof -
      have 1: "insert y (set xs) = set (xs@[y])" by simp
      have 2: "x \<notin> insert y (set xs) \<or> x \<in> set xs" using \<open>y \<noteq> x\<close> by blast
      show ?thesis using 1 2 by (metis (no_types) List.insert_def append_Cons insertCI)
    qed
    thus ?thesis using IH y x False by (auto simp add: List.insert_def)
  qed
qed simp

lemma map_append_inv: "map f xs = ys@zs \<Longrightarrow> \<exists>vs ws. xs = vs@ws \<and> map f vs = ys \<and> map f ws = zs"
proof (induction xs arbitrary: ys zs)
  case (Cons x xs')
  note prems = Cons.prems
  note IH = Cons.IH

  show ?case
  proof (cases ys)
    case (Cons y ys') 
    then obtain vs' ws where *: "xs' = vs'@ws" "map f vs' = ys'" "map f ws = zs"
      using prems IH[of ys' zs] by auto
    hence "x#xs' = (x#vs')@ws" "map f (x#vs') = y#ys'" using Cons prems by force+
    thus ?thesis by (metis Cons *(3))
  qed (use prems in simp)
qed simp

lemma map2_those_Some_case:
  assumes "those (map2 f xs ys) = Some zs"
    and "(x,y) \<in> set (zip xs ys)"
  shows "\<exists>z. f x y = Some z"
  using assms 
proof (induction xs arbitrary: ys zs)
  case (Cons x' xs')
  obtain y' ys' where ys: "ys = y'#ys'" using Cons.prems(2) by (cases ys) simp_all
  obtain z where z: "f x' y' = Some z" using Cons.prems(1) ys by fastforce
  obtain zs' where zs: "those (map2 f xs' ys') = Some zs'" using z Cons.prems(1) ys by auto

  show ?case
  proof (cases "(x,y) = (x',y')")
    case False
    hence "(x,y) \<in> set (zip xs' ys')" using Cons.prems(2) unfolding ys by force
    thus ?thesis using Cons.IH[OF zs] by blast
  qed (use ys z in fast)
qed simp

lemma those_Some_Cons_ex:
  assumes "those (x#xs) = Some ys"
  shows "\<exists>y ys'. ys = y#ys' \<and> those xs = Some ys' \<and> x = Some y"
using assms by (cases x) auto

lemma those_Some_iff:
  "those xs = Some ys \<longleftrightarrow> ((\<forall>x' \<in> set xs. \<exists>x. x' = Some x) \<and> ys = map the xs)"
  (is "?A xs ys \<longleftrightarrow> ?B xs ys")
proof
  show "?A xs ys \<Longrightarrow> ?B xs ys"
  proof (induction xs arbitrary: ys)
    case (Cons x' xs')
    obtain y' ys' where ys: "ys = y'#ys'" "those xs' = Some ys'" and x: "x' = Some y'"
      using Cons.prems those_Some_Cons_ex by blast
    show ?case using Cons.IH[OF ys(2)] unfolding x ys by simp
  qed simp

  show "?B xs ys \<Longrightarrow> ?A xs ys"
    by (induct xs arbitrary: ys) (simp, fastforce)
qed

lemma those_map2_SomeD:
  assumes "those (map2 f ts ss) = Some \<theta>"
    and "\<sigma> \<in> set \<theta>"
  shows "\<exists>(t,s) \<in> set (zip ts ss). f t s = Some \<sigma>"
using those_Some_iff[of "map2 f ts ss" \<theta>] assms by fastforce

lemma those_map2_SomeI:
  assumes "\<And>i. i < length xs \<Longrightarrow> f (xs ! i) (ys ! i) = Some (g i)"
    and "length xs = length ys"
  shows "those (map2 f xs ys) = Some (map g [0..<length xs])"
proof -
  have "\<forall>z \<in> set (map2 f xs ys). \<exists>z'. z = Some z'"
  proof
    fix z assume z: "z \<in> set (map2 f xs ys)"
    then obtain i where i: "i < length xs" "i < length ys" "z = f (xs ! i) (ys ! i)"
      using in_set_conv_nth[of z "map2 f xs ys"] by auto
    thus "\<exists>z'. z = Some z'"
      using assms(1) by blast
  qed
  moreover have "map Some (map g [0..<length xs]) = map (\<lambda>i. f (xs ! i) (ys ! i)) [0..<length xs]"
    using assms by auto
  hence "map Some (map g [0..<length xs]) = map2 f xs ys"
    using assms by (smt map2_map_map map_eq_conv map_nth)
  hence "map (the \<circ> Some) (map g [0..<length xs]) = map the (map2 f xs ys)"
    by (metis map_map)
  hence "map g [0..<length xs] = map the (map2 f xs ys)"
    by simp
  ultimately show ?thesis using those_Some_iff by blast
qed


subsection \<open>List: subsequences\<close>
lemma subseqs_set_subset:
  assumes "ys \<in> set (subseqs xs)"
  shows "set ys \<subseteq> set xs"
using assms subseqs_powset[of xs] by auto

lemma subset_sublist_exists:
  "ys \<subseteq> set xs \<Longrightarrow> \<exists>zs. set zs = ys \<and> zs \<in> set (subseqs xs)"
proof (induction xs arbitrary: ys)
  case Cons thus ?case by (metis (no_types, lifting) Pow_iff imageE subseqs_powset) 
qed simp

lemma map_subseqs: "map (map f) (subseqs xs) = subseqs (map f xs)"
proof (induct xs)
  case (Cons x xs)
  have "map (Cons (f x)) (map (map f) (subseqs xs)) = map (map f) (map (Cons x) (subseqs xs))"
    by (induct "subseqs xs") auto
  thus ?case by (simp add: Let_def Cons)
qed simp

lemma subseqs_Cons:
  assumes "ys \<in> set (subseqs xs)"
  shows "ys \<in> set (subseqs (x#xs))"
by (metis assms Un_iff set_append subseqs.simps(2))

lemma subseqs_subset:
  assumes "ys \<in> set (subseqs xs)"
  shows "set ys \<subseteq> set xs"
using assms by (metis Pow_iff image_eqI subseqs_powset)


subsection \<open>List: prefixes, suffixes\<close>
lemma suffix_Cons': "suffix [x] (y#ys) \<Longrightarrow> suffix [x] ys \<or> (y = x \<and> ys = [])"
using suffix_Cons[of "[x]"] by auto

lemma prefix_Cons': "prefix (x#xs) (x#ys) \<Longrightarrow> prefix xs ys"
by simp

lemma prefix_map: "prefix xs (map f ys) \<Longrightarrow> \<exists>zs. prefix zs ys \<and> map f zs = xs"
using map_append_inv unfolding prefix_def by fast

lemma concat_mono_prefix: "prefix xs ys \<Longrightarrow> prefix (concat xs) (concat ys)"
unfolding prefix_def by fastforce

lemma concat_map_mono_prefix: "prefix xs ys \<Longrightarrow> prefix (concat (map f xs)) (concat (map f ys))"
by (rule map_mono_prefix[THEN concat_mono_prefix])

lemma length_prefix_ex:
  assumes "n \<le> length xs"
  shows "\<exists>ys zs. xs = ys@zs \<and> length ys = n"
  using assms
proof (induction n)
  case (Suc n)
  then obtain ys zs where IH: "xs = ys@zs" "length ys = n" by moura
  hence "length zs > 0" using Suc.prems(1) by auto
  then obtain v vs where v: "zs = v#vs" by (metis Suc_length_conv gr0_conv_Suc)
  hence "length (ys@[v]) = Suc n" using IH(2) by simp
  thus ?case using IH(1) v by (metis append.assoc append_Cons append_Nil)
qed simp

lemma length_prefix_ex':
  assumes "n < length xs"
  shows "\<exists>ys zs. xs = ys@xs ! n#zs \<and> length ys = n"
proof -
  obtain ys zs where xs: "xs = ys@zs" "length ys = n" using assms length_prefix_ex[of n xs] by moura
  hence "length zs > 0" using assms by auto
  then obtain v vs where v: "zs = v#vs" by (metis Suc_length_conv gr0_conv_Suc)
  hence "(ys@zs) ! n = v" using xs by auto
  thus ?thesis using v xs by auto
qed

lemma length_prefix_ex2:
  assumes "i < length xs" "j < length xs" "i < j"
  shows "\<exists>ys zs vs. xs = ys@xs ! i#zs@xs ! j#vs \<and> length ys = i \<and> length zs = j - i - 1"
proof -
  obtain xs0 vs where xs0: "xs = xs0@xs ! j#vs" "length xs0 = j"
    using length_prefix_ex'[OF assms(2)] by blast
  then obtain ys zs where "xs0 = ys@xs ! i#zs" "length ys = i"
    by (metis assms(3) length_prefix_ex' nth_append[of _ _ i])
  thus ?thesis using xs0 by force
qed

lemma prefix_prefix_inv:
  assumes xs: "prefix xs (ys@zs)"
    and x: "suffix [x] xs"
  shows "prefix xs ys \<or> x \<in> set zs"
proof -
  have "prefix xs ys" when "x \<notin> set zs" using that xs
  proof (induction zs rule: rev_induct)
    case (snoc z zs) show ?case
    proof (rule snoc.IH)
      have "x \<noteq> z" using snoc.prems(1) by simp
      thus "prefix xs (ys@zs)"
        using snoc.prems(2) x by (metis append1_eq_conv append_assoc prefix_snoc suffixE) 
    qed (use snoc.prems(1) in simp)
  qed simp
  thus ?thesis by blast
qed

lemma prefix_snoc_obtain:
  assumes xs: "prefix (xs@[x]) (ys@zs)"
    and ys: "\<not>prefix (xs@[x]) ys"
  obtains vs where "xs@[x] = ys@vs@[x]" "prefix (vs@[x]) zs"
proof -
  have "\<exists>vs. xs@[x] = ys@vs@[x] \<and> prefix (vs@[x]) zs" using xs
  proof (induction zs rule: List.rev_induct)
    case (snoc z zs)
    show ?case
    proof (cases "xs@[x] = ys@zs@[z]")
      case False
      hence "prefix (xs@[x]) (ys@zs)" using snoc.prems by (metis append_assoc prefix_snoc)
      thus ?thesis using snoc.IH by auto
    qed simp
  qed (simp add: ys)
  thus ?thesis using that by blast
qed

lemma prefix_snoc_in_iff: "x \<in> set xs \<longleftrightarrow> (\<exists>B. prefix (B@[x]) xs)"
by (induct xs rule: List.rev_induct) auto


subsection \<open>List: products\<close>
lemma product_lists_Cons:
  "x#xs \<in> set (product_lists (y#ys)) \<longleftrightarrow> (xs \<in> set (product_lists ys) \<and> x \<in> set y)"
by auto

lemma product_lists_in_set_nth:
  assumes "xs \<in> set (product_lists ys)"
  shows "\<forall>i<length ys. xs ! i \<in> set (ys ! i)"
proof -
  have 0: "length ys = length xs" using assms(1) by (simp add: in_set_product_lists_length)
  thus ?thesis using assms
  proof (induction ys arbitrary: xs)
    case (Cons y ys)
    obtain x xs' where xs: "xs = x#xs'" using Cons.prems(1) by (metis length_Suc_conv)
    hence "xs' \<in> set (product_lists ys) \<Longrightarrow> \<forall>i<length ys. xs' ! i \<in> set (ys ! i)"
          "length ys = length xs'" "x#xs' \<in> set (product_lists (y#ys))"
      using Cons by simp_all
    thus ?case using xs product_lists_Cons[of x xs' y ys] by (simp add: nth_Cons')
  qed simp
qed

lemma product_lists_in_set_nth':
  assumes "\<forall>i<length xs. ys ! i \<in> set (xs ! i)"
    and "length xs = length ys"
  shows "ys \<in> set (product_lists xs)"
using assms
proof (induction xs arbitrary: ys)
  case (Cons x xs)
  obtain y ys' where ys: "ys = y#ys'" using Cons.prems(2) by (metis length_Suc_conv)
  hence "ys' \<in> set (product_lists xs)" "y \<in> set x" "length xs = length ys'"
    using Cons by fastforce+
  thus ?case using ys product_lists_Cons[of y ys' x xs] by (simp add: nth_Cons')
qed simp


subsection \<open>Other Lemmata\<close>
lemma finite_ballI:
  "\<forall>l \<in> {}. P l" "P x \<Longrightarrow> \<forall>l \<in> xs. P l \<Longrightarrow> \<forall>l \<in> insert x xs. P l"
by (blast, blast)

lemma list_set_ballI:
  "\<forall>l \<in> set []. P l" "P x \<Longrightarrow> \<forall>l \<in> set xs. P l \<Longrightarrow> \<forall>l \<in> set (x#xs). P l"
by (simp, simp)

lemma inv_set_fset: "finite M \<Longrightarrow> set (inv set M) = M"
unfolding inv_def by (metis (mono_tags) finite_list someI_ex)

lemma lfp_eqI':
  assumes "mono f"
    and "f C = C"
    and "\<forall>X \<in> Pow C. f X = X \<longrightarrow> X = C"
  shows "lfp f = C"
by (metis PowI assms lfp_lowerbound lfp_unfold subset_refl)

lemma lfp_while':
  fixes f::"'a set \<Rightarrow> 'a set" and M::"'a set"
  defines "N \<equiv> while (\<lambda>A. f A \<noteq> A) f {}"
  assumes f_mono: "mono f"
    and N_finite: "finite N"
    and N_supset: "f N \<subseteq> N"
  shows "lfp f = N"
proof -
  have *: "f X \<subseteq> N" when "X \<subseteq> N" for X using N_supset monoD[OF f_mono that] by blast
  show ?thesis
    using lfp_while[OF f_mono * N_finite]
    by (simp add: N_def)
qed

lemma lfp_while'':
  fixes f::"'a set \<Rightarrow> 'a set" and M::"'a set"
  defines "N \<equiv> while (\<lambda>A. f A \<noteq> A) f {}"
  assumes f_mono: "mono f"
    and lfp_finite: "finite (lfp f)"
  shows "lfp f = N"
proof -
  have *: "f X \<subseteq> lfp f" when "X \<subseteq> lfp f" for X
    using lfp_fixpoint[OF f_mono] monoD[OF f_mono that]
    by blast
  show ?thesis
    using lfp_while[OF f_mono * lfp_finite]
    by (simp add: N_def)
qed

lemma preordered_finite_set_has_maxima:
  assumes "finite A" "A \<noteq> {}"
  shows "\<exists>a::'a::{preorder} \<in> A. \<forall>b \<in> A. \<not>(a < b)"
using assms 
proof (induction A rule: finite_induct)
  case (insert a A) thus ?case
    by (cases "A = {}", simp, metis insert_iff order_trans less_le_not_le)
qed simp

lemma partition_index_bij:
  fixes n::nat
  obtains I k where
    "bij_betw I {0..<n} {0..<n}" "k \<le> n"
    "\<forall>i. i < k \<longrightarrow> P (I i)"
    "\<forall>i. k \<le> i \<and> i < n \<longrightarrow> \<not>(P (I i))"
proof -
  define A where "A = filter P [0..<n]"
  define B where "B = filter (\<lambda>i. \<not>P i) [0..<n]"
  define k where "k = length A"
  define I where "I = (\<lambda>n. (A@B) ! n)"

  note defs = A_def B_def k_def I_def
  
  have k1: "k \<le> n" by (metis defs(1,3) diff_le_self dual_order.trans length_filter_le length_upt)

  have "i < k \<Longrightarrow> P (A ! i)" for i by (metis defs(1,3) filter_nth)
  hence k2: "i < k \<Longrightarrow> P ((A@B) ! i)" for i by (simp add: defs nth_append) 

  have "i < length B \<Longrightarrow> \<not>(P (B ! i))" for i by (metis defs(2) filter_nth)
  hence "i < length B \<Longrightarrow> \<not>(P ((A@B) ! (k + i)))" for i using k_def by simp 
  hence "k \<le> i \<and> i < k + length B \<Longrightarrow> \<not>(P ((A@B) ! i))" for i
    by (metis add.commute add_less_imp_less_right le_add_diff_inverse2)
  hence k3: "k \<le> i \<and> i < n \<Longrightarrow> \<not>(P ((A@B) ! i))" for i by (simp add: defs sum_length_filter_compl)

  have *: "length (A@B) = n" "set (A@B) = {0..<n}" "distinct (A@B)"
    by (metis defs(1,2) diff_zero length_append length_upt sum_length_filter_compl)
       (auto simp add: defs)

  have I: "bij_betw I {0..<n} {0..<n}"
  proof (intro bij_betwI')
    fix x y show "x \<in> {0..<n} \<Longrightarrow> y \<in> {0..<n} \<Longrightarrow> (I x = I y) = (x = y)"
      by (metis *(1,3) defs(4) nth_eq_iff_index_eq atLeastLessThan_iff)
  next
    fix x show "x \<in> {0..<n} \<Longrightarrow> I x \<in> {0..<n}"
      by (metis *(1,2) defs(4) atLeastLessThan_iff nth_mem)
  next
    fix y show "y \<in> {0..<n} \<Longrightarrow> \<exists>x \<in> {0..<n}. y = I x"
      by (metis * defs(4) atLeast0LessThan distinct_Ex1 lessThan_iff)
  qed

  show ?thesis using k1 k2 k3 I that by (simp add: defs)
qed

lemma finite_lists_length_eq':
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> finite {y. P x y}"
  shows "finite {ys. length xs = length ys \<and> (\<forall>y \<in> set ys. \<exists>x \<in> set xs. P x y)}"
proof -
  define Q where "Q \<equiv> \<lambda>ys. \<forall>y \<in> set ys. \<exists>x \<in> set xs. P x y"
  define M where "M \<equiv> {y. \<exists>x \<in> set xs. P x y}"

  have 0: "finite M" using assms unfolding M_def by fastforce

  have "Q ys \<longleftrightarrow> set ys \<subseteq> M"
       "(Q ys \<and> length ys = length xs) \<longleftrightarrow> (length xs = length ys \<and> Q ys)"
    for ys
    unfolding Q_def M_def by auto
  thus ?thesis
    using finite_lists_length_eq[OF 0, of "length xs"]
    unfolding Q_def by presburger
qed

lemma trancl_eqI:
  assumes "\<forall>(a,b) \<in> A. \<forall>(c,d) \<in> A. b = c \<longrightarrow> (a,d) \<in> A"
  shows "A = A\<^sup>+"
proof
  show "A\<^sup>+ \<subseteq> A"
  proof
    fix x assume x: "x \<in> A\<^sup>+"
    then obtain a b where ab: "x = (a,b)" by (metis surj_pair)
    hence "(a,b) \<in> A\<^sup>+" using x by metis
    hence "(a,b) \<in> A" using assms by (induct rule: trancl_induct) auto
    thus "x \<in> A" using ab by metis
  qed
qed auto

lemma trancl_eqI':
  assumes "\<forall>(a,b) \<in> A. \<forall>(c,d) \<in> A. b = c \<and> a \<noteq> d \<longrightarrow> (a,d) \<in> A"
    and "\<forall>(a,b) \<in> A. a \<noteq> b"
  shows "A = {(a,b) \<in> A\<^sup>+. a \<noteq> b}"
proof
  show "{(a,b) \<in> A\<^sup>+. a \<noteq> b} \<subseteq> A"
  proof
    fix x assume x: "x \<in> {(a,b) \<in> A\<^sup>+. a \<noteq> b}"
    then obtain a b where ab: "x = (a,b)" by (metis surj_pair)
    hence "(a,b) \<in> A\<^sup>+" "a \<noteq> b" using x by blast+
    hence "(a,b) \<in> A"
    proof (induction rule: trancl_induct)
      case base thus ?case by blast
    next
      case step thus ?case using assms(1) by force
    qed
    thus "x \<in> A" using ab by metis
  qed
qed (use assms(2) in auto)

lemma distinct_concat_idx_disjoint:
  assumes xs: "distinct (concat xs)"
    and ij: "i < length xs" "j < length xs" "i < j"
  shows "set (xs ! i) \<inter> set (xs ! j) = {}"
proof -
  obtain ys zs vs where ys: "xs = ys@xs ! i#zs@xs ! j#vs" "length ys = i" "length zs = j - i - 1"
    using length_prefix_ex2[OF ij] by moura
  thus ?thesis
    using xs concat_append[of "ys@xs ! i#zs" "xs ! j#vs"]
          distinct_append[of "concat (ys@xs ! i#zs)" "concat (xs ! j#vs)"]
    by auto
qed

lemma remdups_ex2:
  "length (remdups xs) > 1 \<Longrightarrow> \<exists>a \<in> set xs. \<exists>b \<in> set xs. a \<noteq> b"
by (metis distinct_Ex1 distinct_remdups less_trans nth_mem set_remdups zero_less_one zero_neq_one)

lemma trancl_minus_refl_idem:
  defines "cl \<equiv> \<lambda>ts. {(a,b) \<in> ts\<^sup>+. a \<noteq> b}"
  shows "cl (cl ts) = cl ts"
proof -
  have 0: "(ts\<^sup>+)\<^sup>+ = ts\<^sup>+" "cl ts \<subseteq> ts\<^sup>+" "(cl ts)\<^sup>+ \<subseteq> (ts\<^sup>+)\<^sup>+"
  proof -
    show "(ts\<^sup>+)\<^sup>+ = ts\<^sup>+" "cl ts \<subseteq> ts\<^sup>+" unfolding cl_def by auto
    thus "(cl ts)\<^sup>+ \<subseteq> (ts\<^sup>+)\<^sup>+" using trancl_mono[of _ "cl ts" "ts\<^sup>+"] by blast
  qed

  have 1: "t \<in> cl (cl ts)" when t: "t \<in> cl ts" for t
    using t 0 unfolding cl_def by fast

  have 2: "t \<in> cl ts" when t: "t \<in> cl (cl ts)" for t
  proof -
    obtain a b where ab: "t = (a,b)" by (metis surj_pair)
    have "t \<in> (cl ts)\<^sup>+" and a_neq_b: "a \<noteq> b" using t unfolding cl_def ab by force+
    hence "t \<in> ts\<^sup>+" using 0 by blast
    thus ?thesis using a_neq_b unfolding cl_def ab by blast
  qed

  show ?thesis using 1 2 by blast
qed

lemma ex_list_obtain:
  assumes ts: "\<And>t. t \<in> set ts \<Longrightarrow> \<exists>s. P t s"
  obtains ss where "length ss = length ts" "\<forall>i < length ss. P (ts ! i) (ss ! i)"
proof -
  have "\<exists>ss. length ss = length ts \<and> (\<forall>i < length ss. P (ts ! i) (ss ! i))" using ts
  proof (induction ts rule: List.rev_induct)
    case (snoc t ts)
    obtain s ss where s: "length ss = length ts" "\<forall>i < length ss. P (ts ! i) (ss ! i)" "P t s"
      using snoc.IH snoc.prems by force
    have *: "length (ss@[s]) = length (ts@[t])" using s(1) by simp
    hence "P ((ts@[t]) ! i) ((ss@[s]) ! i)" when i: "i < length (ss@[s])" for i
      using s(2,3) i nth_append[of ts "[t]"] nth_append[of ss "[s]"] by force
    thus ?case using * by blast
  qed simp
  thus thesis using that by blast
qed

lemma length_1_conv[iff]:
  "(length ts = 1) = (\<exists>a. ts = [a])"
by (cases ts) simp_all

lemma length_2_conv[iff]:
  "(length ts = 2) = (\<exists>a b. ts = [a,b])"
proof (cases ts)
  case (Cons a ts') thus ?thesis by (cases ts') simp_all
qed simp

lemma length_3_conv[iff]:
  "(length ts = 3) \<longleftrightarrow> (\<exists>a b c. ts = [a,b,c])"
proof (cases ts)
  case (Cons a ts')
  note * = this
  thus ?thesis
  proof (cases ts')
    case (Cons b ts'') thus ?thesis using * by (cases ts'') simp_all
  qed simp
qed simp

lemma Max_nat_finite_le:
  assumes "finite M"
    and "\<And>m. m \<in> M \<Longrightarrow> f m \<le> (n::nat)"
  shows "Max (insert 0 (f ` M)) \<le> n"
proof -
  have 0: "finite (insert 0 (f ` M))" using assms(1) by blast
  have 1: "insert 0 (f ` M) \<noteq> {}" by force
  have 2: "m \<le> n" when "m \<in> insert 0 (f ` M)" for m using assms(2) that by fastforce
  show ?thesis using Max.boundedI[OF 0 1 2] by blast
qed

lemma Max_nat_finite_lt:
  assumes "finite M"
    and "M \<noteq> {}"
    and "\<And>m. m \<in> M \<Longrightarrow> f m < (n::nat)"
  shows "Max (f ` M) < n"
proof -
  define g where "g \<equiv> \<lambda>m. Suc (f m)"
  have 0: "finite (f ` M)" "finite (g ` M)" using assms(1) by (blast, blast)
  have 1: "f ` M \<noteq> {}" "g ` M \<noteq> {}" using assms(2) by (force, force)
  have 2: "m \<le> n" when "m \<in> g ` M" for m using assms(3) that unfolding g_def by fastforce
  have 3: "Max (g ` M) \<le> n" using Max.boundedI[OF 0(2) 1(2) 2] by blast
  have 4: "Max (f ` M) < Max (g ` M)"
    using Max_in[OF 0(1) 1(1)] Max_gr_iff[OF 0(2) 1(2), of "Max (f ` M)"]
    unfolding g_def by blast
  show ?thesis using 3 4 by linarith
qed

lemma ex_finite_disj_nat_inj:
  fixes N N'::"nat set"
  assumes N: "finite N"
    and N': "finite N'"
  shows "\<exists>M::nat set. \<exists>\<delta>::nat \<Rightarrow> nat. inj \<delta> \<and> \<delta> ` N = M \<and> M \<inter> N' = {}"
using N 
proof (induction N rule: finite_induct)
  case empty thus ?case using injI[of "\<lambda>x::nat. x"] by blast
next
  case (insert n N)
  then obtain M \<delta> where M: "inj \<delta>" "\<delta> ` N = M" "M \<inter> N' = {}" by blast

  obtain m where m: "m \<notin> M" "m \<notin> insert n N" "m \<notin> N'"
    using M(2) finite_imageI[OF insert.hyps(1), of \<delta>] insert.hyps(1) N'
    by (metis finite_UnI finite_insert UnCI infinite_nat_iff_unbounded_le
              finite_nat_set_iff_bounded_le)

  define \<sigma> where "\<sigma> \<equiv> \<lambda>k. if k \<in> insert n N then (\<delta>(n := m)) k else Suc (Max (insert m M)) + k"

  have "insert m M \<inter> N' = {}" using m M(3) unfolding \<sigma>_def by auto
  moreover have "\<sigma> ` insert n N = insert m M" using insert.hyps(2) M(2) unfolding \<sigma>_def by auto
  moreover have "inj \<sigma>"
  proof (intro injI)
    fix i j assume ij: "\<sigma> i = \<sigma> j"

    have 0: "finite (insert m (\<delta> ` N))"
      using insert.hyps(1) by simp

    have 1: "Suc (Max (insert m (\<delta> ` N))) > k" when k: "k \<in> insert m (\<delta> ` N)" for k
      using Max_ge[OF 0 k] by linarith
    
    have 2: "(\<delta>(n := m)) k \<in> insert m (\<delta> ` N)" when k: "k \<in> insert n N" for k
      using k by auto
    
    have 3: "(\<delta>(n := m)) k \<noteq> Suc (Max (insert m (\<delta> ` N))) + k'" when k: "k \<in> insert n N" for k k'
      using 1[OF 2[OF k]] by linarith

    have 4: "i \<in> insert n N \<longleftrightarrow> j \<in> insert n N"
      using ij 3 M(2) unfolding \<sigma>_def by metis

    show "i = j"
    proof (cases "i \<in> insert n N")
      case True
      hence *: "\<sigma> i = (\<delta>(n := m)) i" "\<sigma> j = (\<delta>(n := m)) j"
               "i \<in> insert n N" "j \<in> insert n N"
        using ij iffD1[OF 4] unfolding \<sigma>_def by (argo, argo, argo, argo)

      show ?thesis
      proof (cases "i = n \<or> j = n")
        case True
        moreover have ?thesis when "i = n" "j = n" using that by simp
        moreover have False when "(i = n \<and> j \<noteq> n) \<or> (i \<noteq> n \<and> j = n)"
          by (metis M(2) that ij * m(1) fun_upd_other fun_upd_same image_eqI insertE)
        ultimately show ?thesis by argo
      next
        case False thus ?thesis using ij injD[OF M(1), of i j] unfolding *(1,2) by simp
      qed
    next
      case False thus ?thesis using ij 4 unfolding \<sigma>_def by force
    qed
  qed
  ultimately show ?case by blast
qed


subsection \<open>Infinite Paths in Relations as Mappings from Naturals to States\<close>
context
begin

private fun rel_chain_fun::"nat \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> ('a \<times> 'a) set \<Rightarrow> 'a" where
  "rel_chain_fun 0 x _ _ = x"
| "rel_chain_fun (Suc i) x y r = (if i = 0 then y else SOME z. (rel_chain_fun i x y r, z) \<in> r)"

lemma infinite_chain_intro:
  fixes r::"('a \<times> 'a) set"
  assumes "\<forall>(a,b) \<in> r. \<exists>c. (b,c) \<in> r" "r \<noteq> {}"
  shows "\<exists>f. \<forall>i::nat. (f i, f (Suc i)) \<in> r"
proof -
  from assms(2) obtain a b where "(a,b) \<in> r" by auto

  let ?P = "\<lambda>i. (rel_chain_fun i a b r, rel_chain_fun (Suc i) a b r) \<in> r"
  let ?Q = "\<lambda>i. \<exists>z. (rel_chain_fun i a b r, z) \<in> r"

  have base: "?P 0" using \<open>(a,b) \<in> r\<close> by auto

  have step: "?P (Suc i)" when i: "?P i" for i
  proof -
    have "?Q (Suc i)" using assms(1) i by auto
    thus ?thesis using someI_ex[OF \<open>?Q (Suc i)\<close>] by auto
  qed

  have "\<forall>i::nat. (rel_chain_fun i a b r, rel_chain_fun (Suc i) a b r) \<in> r"
    using base step nat_induct[of ?P] by simp
  thus ?thesis by fastforce
qed

end

lemma infinite_chain_intro':
  fixes r::"('a \<times> 'a) set"
  assumes base: "\<exists>b. (x,b) \<in> r" and step: "\<forall>b. (x,b) \<in> r\<^sup>+ \<longrightarrow> (\<exists>c. (b,c) \<in> r)" 
  shows "\<exists>f. \<forall>i::nat. (f i, f (Suc i)) \<in> r"
proof -
  let ?s = "{(a,b) \<in> r. a = x \<or> (x,a) \<in> r\<^sup>+}"

  have "?s \<noteq> {}" using base by auto

  have "\<exists>c. (b,c) \<in> ?s" when ab: "(a,b) \<in> ?s" for a b
  proof (cases "a = x")
    case False
    hence "(x,a) \<in> r\<^sup>+" using ab by auto
    hence "(x,b) \<in> r\<^sup>+" using \<open>(a,b) \<in> ?s\<close> by auto
    thus ?thesis using step by auto
  qed (use ab step in auto)
  hence "\<exists>f. \<forall>i. (f i, f (Suc i)) \<in> ?s" using infinite_chain_intro[of ?s] \<open>?s \<noteq> {}\<close> by blast
  thus ?thesis by auto
qed

lemma infinite_chain_mono:
  assumes "S \<subseteq> T" "\<exists>f. \<forall>i::nat. (f i, f (Suc i)) \<in> S"
  shows "\<exists>f. \<forall>i::nat. (f i, f (Suc i)) \<in> T"
using assms by auto

end
