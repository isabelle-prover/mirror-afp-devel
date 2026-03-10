(* Author: Tobias Nipkow *)

section \<open>Parse Trees\<close>

theory Parse_Tree
imports Context_Free_Grammar
begin

datatype ('n,'t) ptree = Sym "('n,'t) sym"  | Prod 'n "('n,'t) ptree list"
datatype_compat ptree

fun size_pt :: "('n,'t)ptree \<Rightarrow> nat" where
"size_pt (Sym _) = 0" |
"size_pt (Prod _ ts) = sum_list (map size_pt ts) + 1"

lemma size_pt_0_iff:  "size_pt t = 0 \<longleftrightarrow> (\<exists>s. t = Sym s)"
by (metis not_add_less2 size_pt.elims size_pt.simps(1) zero_less_one)

abbreviation "size_pts ts \<equiv> sum_list (map size_pt ts)"

fun root :: "('n,'t) ptree \<Rightarrow> ('n,'t) sym" where
"root(Sym s) = s" |
"root(Prod A _) = Nt A"

fun fringe :: "('n,'t) ptree \<Rightarrow> ('n,'t) syms" where
"fringe(Sym s) = [s]" |
"fringe(Prod _ ts) = concat(map fringe ts)"

abbreviation "fringes ts \<equiv> concat(map fringe ts)"

fun parse_tree :: "('n,'t)Prods \<Rightarrow> ('n,'t) ptree \<Rightarrow> bool" where
"parse_tree P (Sym s) = True" |
"parse_tree P (Prod A ts) = ((\<forall>t \<in> set ts. parse_tree P t) \<and> (A,map root ts) \<in> P)"

lemma fringe_deriven_if_parse_tree: "parse_tree P t \<Longrightarrow> P \<turnstile> [root t] \<Rightarrow>(size_pt t) fringe t"
proof(induction t)
  case (Sym s)
  then show ?case by (auto)
next
  case (Prod A ts)
  have "P \<turnstile> [Nt A] \<Rightarrow> map root ts"
    using Prod.prems by (simp add: derive_singleton)
  with Prod show ?case
    using deriven_concat1[of ts size_pt P root fringe] by (simp add: relpowp_Suc_I2)
qed

lemma derives_fringe_if_parse_tree: "parse_tree P t \<Longrightarrow> P \<turnstile> [root t] \<Rightarrow>* fringe t"
by (meson fringe_deriven_if_parse_tree rtranclp_power)

fun subst_pt and subst_pts where
"subst_pt t' 0 (Sym _) = t'" |
"subst_pt t' m (Prod A ts) = Prod A (subst_pts t' m ts)" |
"subst_pts t' m (t#ts) =
  (let n = length(fringe t) in if m < n then subst_pt t' m t # ts
   else t # subst_pts t' (m-n) ts)"

lemma fringe_subst_pt: "i < length(fringe t) \<Longrightarrow>
  fringe(subst_pt t' i t) = take i (fringe t) @ fringe t' @ drop (Suc i) (fringe t)" and
fringe_subst_pts: "i < length(fringes ts) \<Longrightarrow>
  fringes (subst_pts t' i ts) =
    take i (fringes ts) @ fringe t' @ drop (Suc i) (fringes ts)"
proof(induction t' i t and t' i ts rule: subst_pt_subst_pts.induct)
  case (3 t' m t ts)
  let ?n = "length (fringe t)"
  show ?case
  proof (cases "m < ?n")
    case True
    thus ?thesis using "3.IH"(1)[OF refl] by (simp add: Let_def)
  next
    case False
    thus ?thesis using "3.IH"(2)[OF refl] "3.prems" by (simp add: Suc_diff_le)
  qed
qed auto

lemma root_subst_pt: "\<lbrakk> i < length(fringe t); fringe t ! i = Nt A; root t' = Nt A \<rbrakk>
 \<Longrightarrow> root (subst_pt t' i t) = root t" and
map_root_subst_pts: "\<lbrakk> i < length(fringes ts); fringes ts ! i = Nt A; root t' = Nt A \<rbrakk>
 \<Longrightarrow> map root (subst_pts t' i ts) = map root ts"
proof(induction t' i t and t' i ts rule: subst_pt_subst_pts.induct)
  case (3 t' m t ts)
  then show ?case by (auto simp add: nth_append Let_def)
qed auto

lemma size_subst_pt: "\<lbrakk> i < length(fringe t) \<rbrakk>
 \<Longrightarrow> size_pt (subst_pt t' i t) = size_pt t + size_pt t'" and
size_subst_pts: "\<lbrakk> i < length(fringes ts) \<rbrakk>
 \<Longrightarrow> size_pts (subst_pts t' i ts) = size_pts ts + size_pt t'"
proof(induction t' i t and t' i ts rule: subst_pt_subst_pts.induct)
  case (3 t' m t ts)
  then show ?case by (auto simp add: nth_append Let_def)
qed auto

lemma parse_tree_subst_pt:
  "\<lbrakk> parse_tree P t; i < length(fringe t); fringe t ! i = Nt A; parse_tree P t'; root t'= Nt A \<rbrakk>
  \<Longrightarrow> parse_tree P (subst_pt t' i t)"
and parse_tree_subst_pts:
  "\<lbrakk> \<forall>t \<in> set ts. parse_tree P t; i < length(fringes ts); fringes ts ! i = Nt A; parse_tree P t'; root t'= Nt A \<rbrakk>
  \<Longrightarrow> \<forall>t' \<in> set(subst_pts t' i ts). parse_tree P t'"
proof(induction t' i t and t' i ts rule: subst_pt_subst_pts.induct)
  case (2 m A ts)
  then show ?case
    using map_root_subst_pts by fastforce
next
  case (3 m t ts)
  then show ?case by(auto simp add: nth_append Let_def)
qed auto

lemma parse_tree_if_deriven: "P \<turnstile> [Nt A] \<Rightarrow>(n) w \<Longrightarrow>
  \<exists>t. parse_tree P t \<and> size_pt t = n \<and> fringe t = w \<and> root t = Nt A"
proof(induction rule: deriven_induct)
  case 0
  then show ?case
    using parse_tree.simps(1) by fastforce
next
  case (Suc n u A' v w)
  then obtain t where 1: "parse_tree P t" and 2: "fringe t = u @ [Nt A'] @ v" and 3: \<open>root t = Nt A\<close>
and 4: "size_pt t = n"
    by blast
  let ?t' = "Prod A' (map Sym w)"
  let ?t = "subst_pt ?t' (length u) t"
  have "fringe ?t = u @ w @ v"
    using 2 fringe_subst_pt[of "length u" t ?t'] by(simp add: o_def)
  moreover have "parse_tree P ?t"
    using parse_tree_subst_pt[OF 1, of "length u"] Suc.hyps(2) 2 by(simp add: o_def)
  moreover have \<open>root ?t = Nt A\<close> by (simp add: 2 3 root_subst_pt)
  ultimately show ?case using size_subst_pt[of "length u" t ?t'] 2 4
    by (auto simp add: o_def)
qed

lemma parse_tree_if_derives: "P \<turnstile> [Nt A] \<Rightarrow>* w \<Longrightarrow> \<exists>t. parse_tree P t \<and> fringe t = w \<and> root t = Nt A"
by (meson parse_tree_if_deriven rtranclp_power)


subsection \<open>Parse Trees up to some height\<close>

text \<open>Derived from the corresponding derivability thms:\<close>

lemma parse_tree_bound_if_Unit_Eps_free:
assumes "Unit_free P" "Eps_free P"
shows "parse_tree P t \<Longrightarrow>
  size_pt t \<le> length (fringe t) - 1 + length(filter isTm (fringe t))"
using  deriven_bound_if_Unit_Eps_free[OF assms] fringe_deriven_if_parse_tree
  by fastforce

lemma parse_tree_bound_if_Unit_Eps_free_NtTm:
assumes "Unit_free P" "Eps_free P"
shows "parse_tree P t \<Longrightarrow> fringe t = map Tm w \<Longrightarrow> size_pt t \<le> 2*length w - 1"
using parse_tree_bound_if_Unit_Eps_free[OF assms]
  by fastforce

text \<open>There are only finitely many parse ptrees up to some height.
A complication \<open>Sym s\<close> is a valid parse ptree for any symbol s. This is in correspondence with
the fact that \<open>P \<turnstile> [s] \<Rightarrow>* [s]\<close> also holds for any \<open>s\<close>. Thus we need to restrict the parse ptrees
to those containing only symbols from \<open>P\<close>.\<close>


lemma finite_pptrees_height_le1:
  assumes "finite P"
  shows "finite {t. parse_tree P t \<and> 0 < size_pt t \<and> size_pt t \<le> n}" (is "finite (?T n)")
proof (induction n)
  case 0
  then show ?case using not_finite_existsD by fastforce
next
  case (Suc n)
  let ?max = "Max (length ` snd ` P)"
  have 1: "(A,w) \<in> P \<Longrightarrow> length w \<le> ?max" for A w
    by (metis Max_ge assms finite_imageI imageI snd_eqD)
  have 2: "(A, map root ts) \<in> P \<Longrightarrow> Sym s \<in> set ts \<Longrightarrow> s \<in> Syms P" for A ts s
    by (metis Syms_simps(2) UnCI in_set_conv_nth insert_Diff length_map nth_map root.simps(1))
  let ?Ts = "{ts. set ts \<subseteq> Sym ` Syms P \<union> ?T n \<and> length ts \<le> ?max}"
  have "t \<in> (\<lambda>(A,ts). Prod A ts) ` (Nts P \<times> ?Ts)" if t: "t \<in> ?T(Suc n)" for t
  proof (cases t)
    case (Prod A ts)
    with t have "A \<in> Nts P" by (auto simp: Nts_Lhss_Rhs_Nts Lhss_def)
    from Prod t Suc have "\<forall>t \<in> set ts. parse_tree P t \<and> size_pt t \<le> n" 
      using member_le_sum_list[of _ "map size_pt ts"] by fastforce
    then have ts: "set ts \<subseteq> Sym ` Syms P \<union> ?T n"
      using size_pt_0_iff 2 t Prod by (fastforce simp: image_iff elim: size_pt.elims)
    have "length ts \<le> ?max" using 1 Prod t by fastforce
    with \<open>A \<in> Nts P\<close> ts Prod show ?thesis
      by blast
  qed (use t in simp)
  hence 4: "?T (Suc n) \<subseteq> (\<lambda>(A,ts). Prod A ts) ` (Nts P \<times> ?Ts)" by blast
  show ?case using finite_subset[OF 4] Suc.IH
    by (simp add: assms finite_Nts finite_Syms finite_lists_length_le)
qed

corollary finite_pptrees_height_le:
  assumes "finite P"
  shows "finite {t. parse_tree P t \<and> size_pt t \<le> n \<and> (\<forall>s. t = Sym s \<longrightarrow> s \<in> Syms P)}"
proof -
  have "{t. parse_tree P t \<and> size_pt t \<le> n \<and> (\<forall>s. t = Sym s \<longrightarrow> s \<in> Syms P)} =
    Sym ` Syms P \<union> {t. parse_tree P t \<and> 0 < size_pt t \<and> size_pt t \<le> n}"
    using size_pt_0_iff by(auto simp: image_iff)
  then show ?thesis
    using finite_pptrees_height_le1[OF assms, of n]
  by (simp add: assms finite_Syms)
qed

end