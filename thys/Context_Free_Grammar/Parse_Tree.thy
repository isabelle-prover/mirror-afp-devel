(* Author: Tobias Nipkow *)

section \<open>Parse Trees\<close>

theory Parse_Tree
imports Context_Free_Grammar
begin

datatype ('n,'t) tree = Sym "('n,'t) sym"  | Rule 'n "('n,'t) tree list"
datatype_compat tree

fun root :: "('n,'t) tree \<Rightarrow> ('n,'t) sym" where
"root(Sym s) = s" |
"root(Rule A _) = Nt A"

fun fringe :: "('n,'t) tree \<Rightarrow> ('n,'t) syms" where
"fringe(Sym s) = [s]" |
"fringe(Rule _ ts) = concat(map fringe ts)"

abbreviation "fringes ts \<equiv> concat(map fringe ts)"

fun parse_tree :: "('n,'t)Prods \<Rightarrow> ('n,'t) tree \<Rightarrow> bool" where
"parse_tree P (Sym s) = True" |
"parse_tree P (Rule A ts) = ((\<forall>t \<in> set ts. parse_tree P t) \<and> (A,map root ts) \<in> P)"

lemma fringe_steps_if_parse_tree: "parse_tree P t \<Longrightarrow> P \<turnstile> [root t] \<Rightarrow>* fringe t"
proof(induction t)
  case (Sym s)
  then show ?case by (auto)
next
  case (Rule A ts)
  have "P \<turnstile> [Nt A] \<Rightarrow> map root ts"
    using Rule.prems by (simp add: derive_singleton)
  with Rule show ?case apply(simp)
    using derives_concat1 by (metis converse_rtranclp_into_rtranclp)
qed

fun subst_pt and subst_pts where
"subst_pt t' 0 (Sym _) = t'" |
"subst_pt t' m (Rule A ts) = Rule A (subst_pts t' m ts)" |
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

lemma parse_tree_if_derives: "P \<turnstile> [Nt A] \<Rightarrow>* w \<Longrightarrow> \<exists>t. parse_tree P t \<and> fringe t = w \<and> root t = Nt A"
proof(induction rule: derives_induct)
  case base
  then show ?case
    using fringe.simps(1) parse_tree.simps(1) root.simps(1) by blast
next
  case (step u A' v w)
  then obtain t where 1: "parse_tree P t" and 2: "fringe t = u @ [Nt A'] @ v" and 3: \<open>root t = Nt A\<close>
    by blast
  let ?t' = "Rule A' (map Sym w)"
  let ?t = "subst_pt ?t' (length u) t"
  have "fringe ?t = u @ w @ v"
    using 2 fringe_subst_pt[of "length u" t ?t'] by(simp add: o_def)
  moreover have "parse_tree P ?t"
    using parse_tree_subst_pt[OF 1, of "length u"] step.hyps(2) 2 by(simp add: o_def)
  moreover have \<open>root ?t = Nt A\<close> by (simp add: 2 3 root_subst_pt)
  ultimately show ?case by blast
qed

end