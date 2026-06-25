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

definition parse_tree_syms :: "('n, 't) Prods \<Rightarrow> ('n,'t) ptree \<Rightarrow> 'n \<Rightarrow> ('n, 't) syms \<Rightarrow> bool" where
"parse_tree_syms P t A \<alpha> = (parse_tree P t \<and> root t = Nt A \<and> fringe t = \<alpha>)"

abbreviation parse_tree_tms :: "('n,'t)Prods \<Rightarrow> ('n,'t)ptree \<Rightarrow> 'n \<Rightarrow> 't list \<Rightarrow> bool" where
"parse_tree_tms P t A w \<equiv> parse_tree_syms P t A (map Tm w)"

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

fun subst_sym_pt and subst_sym_pts where
"subst_sym_pt t' 0 (Sym _) = t'" |
"subst_sym_pt t' m (Prod A ts) = Prod A (subst_sym_pts t' m ts)" |
"subst_sym_pts t' m (t#ts) =
  (let n = length(fringe t) in if m < n then subst_sym_pt t' m t # ts
   else t # subst_sym_pts t' (m-n) ts)"

lemma fringe_subst_sym_pt: "i < length(fringe t) \<Longrightarrow>
  fringe(subst_sym_pt t' i t) = take i (fringe t) @ fringe t' @ drop (Suc i) (fringe t)" and
fringe_subst_sym_pts: "i < length(fringes ts) \<Longrightarrow>
  fringes (subst_sym_pts t' i ts) =
    take i (fringes ts) @ fringe t' @ drop (Suc i) (fringes ts)"
proof(induction t' i t and t' i ts rule: subst_sym_pt_subst_sym_pts.induct)
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

lemma root_subst_sym_pt: "\<lbrakk> i < length(fringe t); fringe t ! i = Nt A; root t' = Nt A \<rbrakk>
 \<Longrightarrow> root (subst_sym_pt t' i t) = root t" and
map_root_subst_sym_pts: "\<lbrakk> i < length(fringes ts); fringes ts ! i = Nt A; root t' = Nt A \<rbrakk>
 \<Longrightarrow> map root (subst_sym_pts t' i ts) = map root ts"
proof(induction t' i t and t' i ts rule: subst_sym_pt_subst_sym_pts.induct)
  case (3 t' m t ts)
  then show ?case by (auto simp add: nth_append Let_def)
qed auto

lemma size_subst_sym_pt: "\<lbrakk> i < length(fringe t) \<rbrakk>
 \<Longrightarrow> size_pt (subst_sym_pt t' i t) = size_pt t + size_pt t'" and
size_subst_sym_pts: "\<lbrakk> i < length(fringes ts) \<rbrakk>
 \<Longrightarrow> size_pts (subst_sym_pts t' i ts) = size_pts ts + size_pt t'"
proof(induction t' i t and t' i ts rule: subst_sym_pt_subst_sym_pts.induct)
  case (3 t' m t ts)
  then show ?case by (auto simp add: nth_append Let_def)
qed auto

lemma parse_tree_subst_sym_pt:
  "\<lbrakk> parse_tree P t; i < length(fringe t); fringe t ! i = Nt A; parse_tree P t'; root t'= Nt A \<rbrakk>
  \<Longrightarrow> parse_tree P (subst_sym_pt t' i t)"
and parse_tree_subst_sym_pts:
  "\<lbrakk> \<forall>t \<in> set ts. parse_tree P t; i < length(fringes ts); fringes ts ! i = Nt A; parse_tree P t'; root t'= Nt A \<rbrakk>
  \<Longrightarrow> \<forall>t' \<in> set(subst_sym_pts t' i ts). parse_tree P t'"
proof(induction t' i t and t' i ts rule: subst_sym_pt_subst_sym_pts.induct)
  case (2 m A ts)
  then show ?case
    using map_root_subst_sym_pts by fastforce
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
  let ?t = "subst_sym_pt ?t' (length u) t"
  have "fringe ?t = u @ w @ v"
    using 2 fringe_subst_sym_pt[of "length u" t ?t'] by(simp add: o_def)
  moreover have "parse_tree P ?t"
    using parse_tree_subst_sym_pt[OF 1, of "length u"] Suc.hyps(2) 2 by(simp add: o_def)
  moreover have \<open>root ?t = Nt A\<close> by (simp add: 2 3 root_subst_sym_pt)
  ultimately show ?case using size_subst_sym_pt[of "length u" t ?t'] 2 4
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
the fact that \<open>P \<turnstile> [s] \<Rightarrow>* [s]\<close> also holds for any \<open>s\<close>. Thus we need to restrict the parse trees
to those containing only symbols from \<open>P\<close>.\<close>

lemma finite_ptrees_height_le1:
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

corollary finite_ptrees_height_le:
  assumes "finite P"
  shows "finite {t. parse_tree P t \<and> size_pt t \<le> n \<and> (\<forall>s. t = Sym s \<longrightarrow> s \<in> Syms P)}"
proof -
  have "{t. parse_tree P t \<and> size_pt t \<le> n \<and> (\<forall>s. t = Sym s \<longrightarrow> s \<in> Syms P)} =
    Sym ` Syms P \<union> {t. parse_tree P t \<and> 0 < size_pt t \<and> size_pt t \<le> n}"
    using size_pt_0_iff by(auto simp: image_iff)
  then show ?thesis
    using finite_ptrees_height_le1[OF assms, of n]
  by (simp add: assms finite_Syms)
qed


subsection \<open>Positions and Subtrees\<close>

text \<open>A \<^emph>\<open>position\<close> (or \<^emph>\<open>address\<close>) is a list of child indices.
  \<open>Pos_pt t\<close> is the set of positions in \<open>t\<close>.
  \<open>sub_pt t p\<close> is the subtree at \<open>p\<close>.\<close>

fun Pos_pt :: "('n,'t) ptree \<Rightarrow> nat list set" where
"Pos_pt (Sym s) = {[]}" |
"Pos_pt (Prod A ts) = {[]} \<union> {i # p | i p. i < length ts \<and> p \<in> map Pos_pt ts ! i}"

fun sub_pt :: "('n,'t) ptree \<Rightarrow> nat list \<Rightarrow> ('n,'t) ptree" where
"sub_pt t [] = t" |
"sub_pt (Prod A ts) (i # p) = sub_pt (ts ! i) p" |
"sub_pt (Sym s) (i # p) = Sym s"

lemma Nil_in_Pos_pt[simp]: "[] \<in> Pos_pt t"
  by (cases t) auto

lemma sub_pt_Sym: "sub_pt (Sym s) q = Sym s"
  by (cases q) auto

lemma sub_pt_append: "sub_pt t (p @ q) = sub_pt (sub_pt t p) q"
proof (induction t p arbitrary: q rule: sub_pt.induct)
  case (1 t) show ?case by simp
next
  case (2 A ts i p) thus ?case by simp
next
  case (3 s i p) thus ?case by (simp add: sub_pt_Sym)
qed

lemma Pos_pt_append: "\<lbrakk> p \<in> Pos_pt t; q \<in> Pos_pt (sub_pt t p) \<rbrakk> \<Longrightarrow> p @ q \<in> Pos_pt t"
proof (induction t p rule: sub_pt.induct)
  case (1 t) thus ?case by simp
next
  case (2 A ts i p)
  from "2.prems"(1) have iv: "i < length ts" and vp: "p \<in> Pos_pt (ts ! i)" by auto
  have "q \<in> Pos_pt (sub_pt (ts ! i) p)" using "2.prems"(2) by simp
  hence "p @ q \<in> Pos_pt (ts ! i)" using "2.IH"[OF vp] by simp
  thus ?case using iv by simp
next
  case (3 s i p) thus ?case by simp
qed

lemma Pos_pt_decomp: "p @ q \<in> Pos_pt t \<Longrightarrow> q \<in> Pos_pt (sub_pt t p)"
proof (induction t p rule: sub_pt.induct)
  case (1 t) thus ?case by simp
next
  case (2 A ts i p)
  from "2.prems" have "p @ q \<in> Pos_pt (ts ! i)" by auto
  thus ?case using "2.IH" by simp
next
  case (3 s i p) thus ?case by simp
qed

lemma parse_tree_sub_pt: "\<lbrakk> parse_tree P t; p \<in> Pos_pt t \<rbrakk> \<Longrightarrow> parse_tree P (sub_pt t p)"
proof (induction t p rule: sub_pt.induct)
  case (2 A ts i p)
  from "2.prems"(2) have iv: "i < length ts" and vp: "p \<in> Pos_pt (ts ! i)" by auto
  from "2.prems"(1) have "parse_tree P (ts ! i)" using nth_mem[OF iv] by auto
  thus ?case using "2.IH"[OF _ vp] by simp
qed auto


subsection \<open>Subtree replacement\<close>

text \<open>\<open>subst_pt t p t'\<close> replaces the subtree of \<open>t\<close> at position \<open>p\<close> by \<open>t'\<close>.\<close>

fun subst_pt :: "('n,'t) ptree \<Rightarrow> nat list \<Rightarrow> ('n,'t) ptree \<Rightarrow> ('n,'t) ptree" where
"subst_pt t [] t' = t'" |
"subst_pt (Prod A ts) (i # p) t' = Prod A (ts[i := subst_pt (ts ! i) p t'])" |
"subst_pt (Sym s) (i # p) t' = Sym s"

lemma root_subst_pt: "\<lbrakk> p \<in> Pos_pt t; p \<noteq> [] \<rbrakk> \<Longrightarrow> root (subst_pt t p t') = root t"
  by (cases p; cases t) auto

lemma root_subst_pt': "\<lbrakk> p \<in> Pos_pt t; root t' = root (sub_pt t p) \<rbrakk> \<Longrightarrow> root (subst_pt t p t') = root t"
  by (cases p) (auto simp: root_subst_pt)

lemma Pos_pt_subst_pt: "p \<in> Pos_pt t \<Longrightarrow> p \<in> Pos_pt (subst_pt t p t')"
proof (induction t p rule: sub_pt.induct)
  case (2 A ts i p)
  from "2.prems" have iv: "i < length ts" and vp: "p \<in> Pos_pt (ts ! i)" by auto
  show ?case using iv "2.IH"[OF vp] by simp
qed auto

lemma sub_pt_subst_pt: "p \<in> Pos_pt t \<Longrightarrow> sub_pt (subst_pt t p t') p = t'"
proof (induction t p rule: sub_pt.induct)
  case (2 A ts i p)
  from "2.prems" have iv: "i < length ts" and vp: "p \<in> Pos_pt (ts ! i)" by auto
  show ?case using iv "2.IH"[OF vp] by simp
qed auto

lemma parse_tree_subst_pt:
  "\<lbrakk> p \<in> Pos_pt t; parse_tree P t; parse_tree P t'; root t' = root (sub_pt t p) \<rbrakk>
   \<Longrightarrow> parse_tree P (subst_pt t p t')"
proof (induction t p t' rule: subst_pt.induct)
  case (2 A ts i p t')
  from "2.prems"(1) have iv: "i < length ts" and vp: "p \<in> Pos_pt (ts ! i)" by auto
  from "2.prems"(2) have pts: "\<forall>x\<in>set ts. parse_tree P x" and inP: "(A, map root ts) \<in> P" by auto
  have ptsi: "parse_tree P (ts ! i)" using nth_mem[OF iv] pts by blast
  have rt: "root t' = root (sub_pt (ts ! i) p)" using "2.prems"(4) by simp
  have ptr: "parse_tree P (subst_pt (ts ! i) p t')" by (rule "2.IH"[OF vp ptsi "2.prems"(3) rt])
  have rr: "root (subst_pt (ts ! i) p t') = root (ts ! i)"
  proof (cases p)
    case Nil thus ?thesis using rt by simp
  next
    case Cons thus ?thesis using root_subst_pt[OF vp] by simp
  qed
  have mr: "map root (ts[i := subst_pt (ts ! i) p t']) = map root ts"
    using iv by (simp add: rr map_update list_update_same_conv)
  have "\<forall>x\<in>set (ts[i := subst_pt (ts ! i) p t']). parse_tree P x"
    using ptr pts set_update_subset_insert by fastforce
  thus ?case using inP mr by auto
qed simp_all


subsection \<open>Fringe spans\<close>

text \<open>A *\<open>fringe span\<close> is the set of indices of the fringe of a subtree of \<open>t\<close> within \<open>fringe t\<close>.\<close>

text \<open>\<open>fringe_beg t p\<close> is the beginning of \<open>fringe (sub_pt t pos)\<close> within \<open>fringe t\<close>\<close>
fun fringe_beg :: "('n,'t) ptree \<Rightarrow> nat list \<Rightarrow> nat" where
"fringe_beg t [] = 0" |
"fringe_beg (Prod A ts) (i # p) = length (fringes (take i ts)) + fringe_beg (ts ! i) p" |
"fringe_beg (Sym s) (i # p) = 0"

text \<open>\<open>fringe_end t p\<close> is the (exclusive) right end of the fringe slice occupied by the subtree at \<open>p\<close>,
  and \<open>fringe_span t p\<close> the set of fringe positions it covers.\<close>

abbreviation fringe_end :: "('n,'t) ptree \<Rightarrow> nat list \<Rightarrow> nat" where
"fringe_end t p \<equiv> fringe_beg t p + length (fringe (sub_pt t p))"

definition fringe_span :: "('n,'t) ptree \<Rightarrow> nat list \<Rightarrow> nat set" where
"fringe_span t p = {fringe_beg t p ..< fringe_end t p}"

lemma len_fringes_take_Suc:
  "i < length ts \<Longrightarrow>
   length (fringes (take (Suc i) ts)) = length (fringes (take i ts)) + length (fringe (ts ! i))"
  by (simp add: take_Suc_conv_app_nth)

lemma len_fringes_take_le: "length (fringes (take i ts)) \<le> length (fringes ts)"
proof -
  have "fringes ts = fringes (take i ts) @ fringes (drop i ts)"
    by (metis append_take_drop_id concat_append map_append)
  thus ?thesis by simp
qed

lemma len_fringes_take_mono:
  assumes "i \<le> j" shows "length (fringes (take i ts)) \<le> length (fringes (take j ts))"
by (metis (no_types, lifting) assms len_fringes_take_le min.absorb1 take_take)

lemma fringe_end_bound: "p \<in> Pos_pt t \<Longrightarrow> fringe_end t p \<le> length (fringe t)"
proof (induction t arbitrary: p)
  case (Sym s)
  show ?case using Sym.prems by (cases p) auto
next
  case (Prod A ts)
  show ?case
  proof (cases p)
    case Nil thus ?thesis by simp
  next
    case (Cons i p')
    with Prod.prems have i: "i < length ts" and v: "p' \<in> Pos_pt (ts ! i)" by auto
    have "fringe_end (Prod A ts) p = length (fringes (take i ts)) + fringe_end (ts ! i) p'"
      using Cons by simp
    also have "\<dots> \<le> length (fringes (take i ts)) + length (fringe (ts ! i))"
      using Prod.IH[OF nth_mem[OF i] v] by simp
    also have "\<dots> = length (fringes (take (Suc i) ts))"
      using len_fringes_take_Suc[OF i] by simp
    also have "\<dots> \<le> length (fringes ts)" using len_fringes_take_le by blast
    also have "\<dots> = length (fringe (Prod A ts))" by simp
    finally show ?thesis .
  qed
qed

text \<open>The replacement decomposes the fringe; the prefix has length exactly \<open>fringe_beg t p\<close>.\<close>

lemma fringe_subst_pt:
  "p \<in> Pos_pt t \<Longrightarrow> \<exists>pre post.
     (\<forall>t'. fringe (subst_pt t p t') = pre @ fringe t' @ post) \<and>
     fringe t = pre @ fringe (sub_pt t p) @ post \<and>
     length pre = fringe_beg t p"
proof (induction t p rule: sub_pt.induct)
  case (1 t)
  show ?case by (rule exI[of _ "[]"], rule exI[of _ "[]"]) simp
next
  case (2 A ts i p)
  from "2.prems" have iv: "i < length ts" and vp: "p \<in> Pos_pt (ts ! i)" by auto
  from "2.IH"[OF vp] obtain pre' post' where
    IH1: "\<And>t'. fringe (subst_pt (ts ! i) p t') = pre' @ fringe t' @ post'" and
    IH2: "fringe (ts ! i) = pre' @ fringe (sub_pt (ts ! i) p) @ post'" and
    IH3: "length pre' = fringe_beg (ts ! i) p" by blast
  let ?pre0 = "concat (take i (map fringe ts))"
  let ?post0 = "concat (drop (Suc i) (map fringe ts))"
  have e: "fringe (Prod A ts) = ?pre0 @ fringe (ts ! i) @ ?post0"
  proof -
    have "map fringe ts = take i (map fringe ts) @ (map fringe ts) ! i # drop (Suc i) (map fringe ts)"
      using iv id_take_nth_drop[of i "map fringe ts"] by simp
    hence "concat (map fringe ts)
         = concat (take i (map fringe ts)) @ (map fringe ts) ! i @ concat (drop (Suc i) (map fringe ts))"
      by (metis concat.simps(2) concat_append)
    thus ?thesis using iv by simp
  qed
  have r: "fringe (subst_pt (Prod A ts) (i # p) t') = ?pre0 @ (pre' @ fringe t' @ post') @ ?post0" for t'
  proof -
    have "fringe (subst_pt (Prod A ts) (i # p) t')
        = concat ((map fringe ts)[i := fringe (subst_pt (ts ! i) p t')])"
      by (simp add: map_update)
    also have "\<dots> = ?pre0 @ fringe (subst_pt (ts ! i) p t') @ ?post0"
      using iv by (simp add: upd_conv_take_nth_drop)
    also have "\<dots> = ?pre0 @ (pre' @ fringe t' @ post') @ ?post0" using IH1 by simp
    finally show ?thesis .
  qed
  have lenpre: "length (?pre0 @ pre') = fringe_beg (Prod A ts) (i # p)"
    using IH3 by (simp add: take_map)
  have "\<forall>t'. fringe (subst_pt (Prod A ts) (i # p) t') = (?pre0 @ pre') @ fringe t' @ (post' @ ?post0)"
    using r by simp
  moreover have "fringe (Prod A ts)
       = (?pre0 @ pre') @ fringe (sub_pt (Prod A ts) (i # p)) @ (post' @ ?post0)"
    using e IH2 by simp
  ultimately show ?case using lenpre by blast
qed simp

lemma fringe_beg_subst_pt: "p \<in> Pos_pt t \<Longrightarrow> fringe_beg (subst_pt t p t') p = fringe_beg t p"
proof (induction t p rule: sub_pt.induct)
  case (1 t) show ?case by simp
next
  case (2 A ts i p)
  from "2.prems" have iv: "i < length ts" and vp: "p \<in> Pos_pt (ts ! i)" by auto
  have "fringe_beg (subst_pt (Prod A ts) (i # p) t') (i # p)
      = length (fringes (take i ts)) + fringe_beg (subst_pt (ts ! i) p t') p"
    using iv by simp
  also have "\<dots> = length (fringes (take i ts)) + fringe_beg (ts ! i) p" using "2.IH"[OF vp] by simp
  also have "\<dots> = fringe_beg (Prod A ts) (i # p)" by simp
  finally show ?case .
next
  case (3 s i p) show ?case by simp
qed

text \<open>
  The following lemmas are the structural core of the classical inherent-ambiguity arguments of
  Parikh (1961) and Ogden (1968): the step "two derivations of the same word that pump
  \<^emph>\<open>overlapping but incomparable\<close> regions cannot be the same parse tree".

Terminology: Two sets are called *\<open>laminar\<close>
  if they are either nested (= one is contained in the other) or disjoint.

  The key fact is \<^emph>\<open>laminarity\<close> of fringe spans: the fringe of the subterm at one
  node and the fringe of the subterm at another node are always either nested or disjoint
  — never overlapping-but-incomparable. From this, two parse trees that exhibit non-laminar
  node-slices must be distinct, so the grammar is ambiguous.
\<close>

lemma fringe_spans_laminar_aux:
  "\<lbrakk> p \<in> Pos_pt t; q \<in> Pos_pt t \<rbrakk> \<Longrightarrow>
   fringe_end t p \<le> fringe_beg t q \<or> fringe_end t q \<le> fringe_beg t p
   \<or> (fringe_beg t p \<le> fringe_beg t q \<and> fringe_end t q \<le> fringe_end t p)
   \<or> (fringe_beg t q \<le> fringe_beg t p \<and> fringe_end t p \<le> fringe_end t q)"
proof (induction t arbitrary: p q)
  case (Sym s)
  show ?case using Sym.prems by (cases p; cases q) auto
next
  case (Prod A ts)
  show ?case
  proof (cases p)
    case Nil
    have "fringe_end (Prod A ts) q \<le> length (fringe (Prod A ts))" using fringe_end_bound[OF Prod.prems(2)] .
    thus ?thesis using Nil by auto
  next
    case (Cons i p')
    from Prod.prems(1) Cons have iL: "i < length ts" and vi: "p' \<in> Pos_pt (ts ! i)" by auto
    show ?thesis
    proof (cases q)
      case Nil
      have "fringe_end (Prod A ts) p \<le> length (fringe (Prod A ts))" using fringe_end_bound[OF Prod.prems(1)] .
      thus ?thesis using Nil by auto
    next
      case (Cons j q')
      from Prod.prems(2) Cons have jL: "j < length ts" and vj: "q' \<in> Pos_pt (ts ! j)" by auto
      show ?thesis
      proof (cases "i = j")
        case True
        have viq: "q' \<in> Pos_pt (ts ! i)" using vj True by simp
        let ?c = "length (fringes (take i ts))"
        have rp: "fringe_beg (Prod A ts) p = ?c + fringe_beg (ts ! i) p'"
                 "sub_pt (Prod A ts) p = sub_pt (ts ! i) p'"
          using \<open>p = i # p'\<close> by simp_all
        have rq: "fringe_beg (Prod A ts) q = ?c + fringe_beg (ts ! i) q'"
                 "sub_pt (Prod A ts) q = sub_pt (ts ! i) q'"
          using \<open>q = j # q'\<close> True by simp_all
        from Prod.IH[OF nth_mem[OF iL] vi viq]
        show ?thesis by (simp add: rp rq)
      next
        case neq: False
        from neq consider "i < j" | "j < i" by (meson nat_neq_iff)
        then show ?thesis
        proof cases
          case 1
          have "fringe_end (Prod A ts) p \<le> fringe_beg (Prod A ts) q"
          proof -
            have "fringe_end (Prod A ts) p = length (fringes (take i ts)) + fringe_end (ts ! i) p'"
              using \<open>p = i # p'\<close> by simp
            also have "\<dots> \<le> length (fringes (take i ts)) + length (fringe (ts ! i))"
              using fringe_end_bound[OF vi] by simp
            also have "\<dots> = length (fringes (take (Suc i) ts))"
              using len_fringes_take_Suc[OF iL] by simp
            also have "\<dots> \<le> length (fringes (take j ts))"
              using len_fringes_take_mono[of "Suc i" j ts] \<open>i < j\<close> by simp
            also have "\<dots> \<le> fringe_beg (Prod A ts) q" using \<open>q = j # q'\<close> by simp
            finally show ?thesis .
          qed
          thus ?thesis by blast
        next
          case 2
          have "fringe_end (Prod A ts) q \<le> fringe_beg (Prod A ts) p"
          proof -
            have "fringe_end (Prod A ts) q = length (fringes (take j ts)) + fringe_end (ts ! j) q'"
              using \<open>q = j # q'\<close> by simp
            also have "\<dots> \<le> length (fringes (take j ts)) + length (fringe (ts ! j))"
              using fringe_end_bound[OF vj] by simp
            also have "\<dots> = length (fringes (take (Suc j) ts))"
              using len_fringes_take_Suc[OF jL] by simp
            also have "\<dots> \<le> length (fringes (take i ts))"
              using len_fringes_take_mono[of "Suc j" i ts] \<open>j < i\<close> by simp
            also have "\<dots> \<le> fringe_beg (Prod A ts) p" using \<open>p = i # p'\<close> by simp
            finally show ?thesis .
          qed
          thus ?thesis by blast
        qed
      qed
    qed
  qed
qed

text \<open>The fringe spans of subtrees are laminar:\<close>

theorem fringe_spans_laminar:
  assumes "p \<in> Pos_pt t" "q \<in> Pos_pt t"
  shows "fringe_span t p \<subseteq> fringe_span t q \<or> fringe_span t q \<subseteq> fringe_span t p
    \<or> fringe_span t p \<inter> fringe_span t q = {}"
using fringe_spans_laminar_aux[OF assms] by (auto simp: fringe_span_def)


subsection \<open>Ambiguity\<close>

definition ambiguous :: "('n, 't) Prods \<Rightarrow> 'n \<Rightarrow> bool" where
"ambiguous P S = (\<exists>w \<in> Lang P S.
   \<exists>t1 t2. (parse_tree_tms P t1 S w \<and> parse_tree_tms P t2 S w) \<and> t1 \<noteq> t2)"

abbreviation unambiguous :: "('n, 't) Prods \<Rightarrow> 'n \<Rightarrow> bool" where
"unambiguous P S \<equiv> \<not> ambiguous P S"

text \<open>A trivial consequence of @{thm fringe_spans_laminar}:
if two parse trees with the same fringe have positions whose fringe spans are not laminar,
the parse trees must be different and hence the grammar is ambiguous.\<close>

corollary ambiguous_if_not_laminar:
  assumes "parse_tree_tms P t1 S w" "parse_tree_tms P t2 S w"
    and "w \<in> Lang P S"
    and "p \<in> Pos_pt t1" "q \<in> Pos_pt t2"
    and "fringe_span t1 p \<inter> fringe_span t2 q \<noteq> {}"
    and "\<not> fringe_span t1 p \<subseteq> fringe_span t2 q" "\<not> fringe_span t2 q \<subseteq> fringe_span t1 p"
  shows "ambiguous P S"
proof -
  have "t1 \<noteq> t2" using assms(4-8) fringe_spans_laminar by blast
  with assms(1-3) have "ambiguous P S" unfolding ambiguous_def by blast
  thus ?thesis by simp
qed

end