
section \<open>Miscellaneous lemmas\<close>

theory More_Misc
imports Main
begin

lemma cart_singleton_empty:
  "(S \<times> {e} = {}) = (S = {})"
  by blast

lemma MinI:
  assumes fa: "finite A"
  and     ne: "A \<noteq> {}"
  and     xv: "m \<in> A"
  and    min: "\<forall>y \<in> A. m \<le> y"
  shows "Min A = m" using fa ne xv min
proof (induct A arbitrary: m rule: finite_ne_induct)
  case singleton then show ?case by simp
next
  case (insert y F)

  from insert.prems have yx: "m \<le> y" and fx: "\<forall>y \<in> F. m \<le> y" by auto
  have "m \<in> insert y F" by fact
  then show ?case
  proof
    assume mv: "m = y"

    have mlt: "m \<le> Min F"
      by (rule iffD2 [OF Min_ge_iff [OF insert.hyps(1) insert.hyps(2)] fx])

    show ?case
      apply (subst Min_insert [OF insert.hyps(1) insert.hyps(2)])
      apply (subst mv [symmetric])
      apply (auto simp: min_def mlt)
      done
  next
    assume "m \<in> F"
    then have mf: "Min F = m"
      by (rule insert.hyps(4) [OF _ fx])

    show ?case
      apply (subst Min_insert [OF insert.hyps(1) insert.hyps(2)])
      apply (subst mf)
      apply (rule iffD2 [OF _ yx])
      apply (auto simp: min_def)
      done
  qed
qed

lemma power_numeral: "a ^ numeral k = a * a ^ (pred_numeral k)"
  by (simp add: numeral_eq_Suc)

lemma funpow_numeral [simp]: "f ^^ numeral k = f \<circ> f ^^ (pred_numeral k)"
  by (simp add: numeral_eq_Suc)

lemma funpow_minus_simp: "0 < n \<Longrightarrow> f ^^ n = f \<circ> f ^^ (n - 1)"
  by (auto dest: gr0_implies_Suc)

lemma rco_alt: "(f \<circ> g) ^^ n \<circ> f = f \<circ> (g \<circ> f) ^^ n"
  apply (rule ext)
  apply (induct n)
   apply (simp_all add: o_def)
  done

lemma union_sub:
  "\<lbrakk>B \<subseteq> A; C \<subseteq> B\<rbrakk> \<Longrightarrow> (A - B) \<union> (B - C) = (A - C)"
  by fastforce

lemma insert_sub:
  "x \<in> xs \<Longrightarrow> (insert x (xs - ys)) = (xs - (ys - {x}))"
  by blast

lemma ran_upd:
  "\<lbrakk> inj_on f (dom f); f y = Some z \<rbrakk> \<Longrightarrow> ran (\<lambda>x. if x = y then None else f x) = ran f - {z}"
  unfolding ran_def
  apply (rule set_eqI)
  apply simp
  by (metis domI inj_on_eq_iff option.sel)

lemma if_apply_def2:
  "(if P then F else G) = (\<lambda>x. (P \<longrightarrow> F x) \<and> (\<not> P \<longrightarrow> G x))"
  by simp

lemma case_bool_If:
  "case_bool P Q b = (if b then P else Q)"
  by simp

lemma if_f:
  "(if a then f b else f c) = f (if a then b else c)"
  by simp

lemmas ls_splits = prod.split prod.split_asm if_split_asm

lemma size_if: "size (if p then xs else ys) = (if p then size xs else size ys)"
  by (fact if_distrib)

lemma if_Not_x: "(if p then \<not> x else x) = (p = (\<not> x))"
  by auto

lemma if_x_Not: "(if p then x else \<not> x) = (p = x)"
  by auto

lemma if_same_and: "(If p x y \<and> If p u v) = (if p then x \<and> u else y \<and> v)"
  by auto

lemma if_same_eq: "(If p x y  = (If p u v)) = (if p then x = u else y = v)"
  by auto

lemma if_same_eq_not: "(If p x y = (\<not> If p u v)) = (if p then x = (\<not> u) else y = (\<not> v))"
  by auto

lemma the_elemI: "y = {x} \<Longrightarrow> the_elem y = x"
  by simp

lemma nonemptyE: "S \<noteq> {} \<Longrightarrow> (\<And>x. x \<in> S \<Longrightarrow> R) \<Longrightarrow> R"
  by auto

lemmas xtr1 = xtrans(1)
lemmas xtr2 = xtrans(2)
lemmas xtr3 = xtrans(3)
lemmas xtr4 = xtrans(4)
lemmas xtr5 = xtrans(5)
lemmas xtr6 = xtrans(6)
lemmas xtr7 = xtrans(7)
lemmas xtr8 = xtrans(8)

lemmas if_fun_split = if_apply_def2

lemma not_empty_eq:
  "(S \<noteq> {}) = (\<exists>x. x \<in> S)"
  by auto

lemma range_subset_lower:
  fixes c :: "'a ::linorder"
  shows "\<lbrakk> {a..b} \<subseteq> {c..d}; x \<in> {a..b} \<rbrakk> \<Longrightarrow> c \<le> a"
  apply (frule (1) subsetD)
  apply (rule classical)
  apply clarsimp
  done

lemma range_subset_upper:
  fixes c :: "'a ::linorder"
  shows "\<lbrakk> {a..b} \<subseteq> {c..d}; x \<in> {a..b} \<rbrakk> \<Longrightarrow> b \<le> d"
  apply (frule (1) subsetD)
  apply (rule classical)
  apply clarsimp
  done

lemma range_subset_eq:
  fixes a::"'a::linorder"
  assumes non_empty: "a \<le> b"
  shows "({a..b} \<subseteq> {c..d}) = (c \<le> a \<and> b \<le> d)"
  apply (insert non_empty)
  apply (rule iffI)
   apply (frule range_subset_lower [where x=a], simp)
   apply (drule range_subset_upper [where x=a], simp)
   apply simp
  apply auto
  done

lemma range_eq:
  fixes a::"'a::linorder"
  assumes non_empty: "a \<le> b"
  shows "({a..b} = {c..d}) = (a = c \<and> b = d)"
  by (metis atLeastatMost_subset_iff eq_iff non_empty)

lemma range_strict_subset_eq:
  fixes a::"'a::linorder"
  assumes non_empty: "a \<le> b"
  shows "({a..b} \<subset> {c..d}) = (c \<le> a \<and> b \<le> d \<and> (a = c \<longrightarrow> b \<noteq> d))"
  apply (insert non_empty)
  apply (subst psubset_eq)
  apply (subst range_subset_eq, assumption+)
  apply (subst range_eq, assumption+)
  apply simp
  done

lemma range_subsetI:
  fixes x :: "'a :: order"
  assumes xX: "X \<le> x"
  and     yY: "y \<le> Y"
  shows   "{x .. y} \<subseteq> {X .. Y}"
  using xX yY by auto

lemma set_False [simp]:
  "(set bs \<subseteq> {False}) = (True \<notin> set bs)" by auto

lemma int_not_emptyD:
  "A \<inter> B \<noteq> {} \<Longrightarrow> \<exists>x. x \<in> A \<and> x \<in> B"
  by (erule contrapos_np, clarsimp simp: disjoint_iff_not_equal)

definition
  sum_map :: "('a \<Rightarrow> 'b) \<Rightarrow> ('c \<Rightarrow> 'd) \<Rightarrow> 'a + 'c \<Rightarrow> 'b + 'd" where
 "sum_map f g x \<equiv> case x of Inl v \<Rightarrow> Inl (f v) | Inr v' \<Rightarrow> Inr (g v')"

lemma sum_map_simps[simp]:
  "sum_map f g (Inl v) = Inl (f v)"
  "sum_map f g (Inr w) = Inr (g w)"
  by (simp add: sum_map_def)+

lemma if_Some_None_eq_None:
  "((if P then Some v else None) = None) = (\<not> P)"
  by simp

lemma CollectPairFalse [iff]:
  "{(a,b). False} = {}"
  by (simp add: split_def)

lemma if_conj_dist:
  "((if b then w else x) \<and> (if b then y else z) \<and> X) =
  ((if b then w \<and> y else x \<and> z) \<and> X)"
  by simp

lemma if_P_True1:
  "Q \<Longrightarrow> (if P then True else Q)"
  by simp

lemma if_P_True2:
  "Q \<Longrightarrow> (if P then Q else True)"
  by simp

end
