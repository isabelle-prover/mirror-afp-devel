(* Author: Bernhard Stöckl *)

theory List_Dtree
  imports Complex_Main "Graph_Additions" "Dtree"
begin

section \<open>Dtrees of Lists\<close>

subsection \<open>Functions\<close>

abbreviation remove_child :: "'a \<Rightarrow> (('a,'b) dtree \<times> 'b) fset \<Rightarrow> (('a,'b) dtree \<times> 'b) fset" where
  "remove_child x xs \<equiv> ffilter (\<lambda>(t,e). root t \<noteq> x) xs"

abbreviation child2 ::
  "'a \<Rightarrow> (('a,'b) dtree \<times> 'b) fset \<Rightarrow> (('a,'b) dtree \<times> 'b) fset \<Rightarrow> (('a,'b) dtree \<times> 'b) fset" where
  "child2 x zs xs \<equiv> ffold (\<lambda>(t,_) b. case t of Node r ys \<Rightarrow> if r = x then ys |\<union>| b else b) zs xs"

text \<open>Combine children sets to a single set and append element to list.\<close>

fun combine :: "'a list \<Rightarrow> 'a list \<Rightarrow> ('a list,'b) dtree \<Rightarrow> ('a list,'b) dtree" where
  "combine x y (Node r xs) = (if x=r \<and> (\<exists>t. t \<in> fst ` fset xs \<and> root t = y)
    then Node (r@y) (child2 y (remove_child y xs) xs)
    else Node r ((\<lambda>(t,e). (combine x y t,e)) |`| xs))"

text \<open>Basic @{term wf_dverts} property is not strong enough to be preserved in combine operation.\<close>

fun dlverts :: "('a list,'b) dtree \<Rightarrow> 'a set" where
  "dlverts (Node r xs) = set r \<union> (\<Union>x\<in>fset xs. dlverts (fst x))"

abbreviation disjoint_dlverts :: "(('a list, 'b) dtree \<times> 'b) fset \<Rightarrow> bool" where
  "disjoint_dlverts xs \<equiv>
    (\<forall>(x,e1) \<in> fset xs. \<forall>(y,e2) \<in> fset xs. dlverts x \<inter> dlverts y = {} \<or> (x,e1)=(y,e2))"

fun wf_dlverts :: "('a list,'b) dtree \<Rightarrow> bool" where
  "wf_dlverts (Node r xs) =
    (r \<noteq> [] \<and> (\<forall>(x,e1) \<in> fset xs. set r \<inter> dlverts x = {} \<and> wf_dlverts x) \<and> disjoint_dlverts xs)"

definition wf_dlverts' :: "('a list,'b) dtree \<Rightarrow> bool" where
  "wf_dlverts' t \<longleftrightarrow>
     wf_dverts t \<and> [] \<notin> dverts t \<and> (\<forall>v1\<in>dverts t. \<forall>v2\<in>dverts t. set v1 \<inter> set v2 = {} \<or> v1=v2)"

fun wf_list_lverts :: "('a list\<times>'b) list \<Rightarrow> bool" where
  "wf_list_lverts [] = True"
| "wf_list_lverts ((v,e)#xs) =
    (v \<noteq> [] \<and> (\<forall>v2 \<in> fst ` set xs. set v \<inter> set v2 = {}) \<and> wf_list_lverts xs)"

subsection \<open>List Dtrees as Well-Formed Dtrees\<close>

lemma list_in_verts_if_lverts: "x \<in> dlverts t \<Longrightarrow> (\<exists>v \<in> dverts t. x \<in> set v)"
  by(induction t) fastforce

lemma list_in_verts_iff_lverts: "x \<in> dlverts t \<longleftrightarrow> (\<exists>v \<in> dverts t. x \<in> set v)"
  by(induction t) fastforce

lemma lverts_if_in_verts: "\<lbrakk>v \<in> dverts t; x \<in> set v\<rbrakk> \<Longrightarrow> x \<in> dlverts t"
  by(induction t) fastforce

lemma nempty_inter_notin_dverts: "\<lbrakk>v \<noteq> []; set v \<inter> dlverts t = {}\<rbrakk> \<Longrightarrow> v \<notin> dverts t"
  using lverts_if_in_verts disjoint_iff_not_equal equals0I set_empty by metis

lemma empty_notin_wf_dlverts: "wf_dlverts t \<Longrightarrow> [] \<notin> dverts t"
  by(induction t) auto

lemma wf_dlverts'_rec: "\<lbrakk>wf_dlverts' (Node r xs); t1 \<in> fst ` fset xs\<rbrakk> \<Longrightarrow> wf_dlverts' t1"
  unfolding wf_dlverts'_def using wf_dverts_rec[of r xs t1] dverts_child_subseteq[of t1 xs] by blast

lemma wf_dlverts'_suc: "\<lbrakk>wf_dlverts' t; t1 \<in> fst ` fset (sucs t)\<rbrakk> \<Longrightarrow> wf_dlverts' t1"
  using wf_dlverts'_rec[of "root t" "sucs t"] by simp

lemma wf_dlverts_suc: "\<lbrakk>wf_dlverts t; t1 \<in> fst ` fset (sucs t)\<rbrakk> \<Longrightarrow> wf_dlverts t1"
  using wf_dlverts.simps[of "root t" "sucs t"] by auto

lemma wf_dlverts_subtree: "\<lbrakk>wf_dlverts t; is_subtree t1 t\<rbrakk> \<Longrightarrow> wf_dlverts t1"
  by (induction t) auto

lemma dlverts_eq_dverts_union: "dlverts t = \<Union> (set ` dverts t)"
  by (induction t) fastforce

lemma dlverts_eq_dverts_union': "dlverts t = (\<Union>x\<in> dverts t. set x)"
  using dlverts_eq_dverts_union by simp

lemma dverts_nempty: "dverts t \<noteq> {}"
  using dtree.set(1)[of "root t" "sucs t"] by simp

lemma dlverts_nempty_aux: "[] \<notin> dverts t \<Longrightarrow> dlverts t \<noteq> {}"
  using dverts_nempty dlverts_eq_dverts_union[of t] by fastforce

lemma dlverts_nempty_if_wf: "wf_dlverts t \<Longrightarrow> dlverts t \<noteq> {}"
  using dlverts_nempty_aux empty_notin_wf_dlverts by blast

lemma nempty_root_in_lverts: "root t \<noteq> [] \<Longrightarrow> hd (root t) \<in> dlverts t"
  using dtree.set_sel(1) list_in_verts_iff_lverts by fastforce

lemma roothd_in_lverts_if_wf: "wf_dlverts t \<Longrightarrow> hd (root t) \<in> dlverts t"
  using wf_dlverts.simps[of "root t" "sucs t"] nempty_root_in_lverts by auto

lemma hd_in_lverts_if_wf: "\<lbrakk>wf_dlverts t; v \<in> dverts t\<rbrakk> \<Longrightarrow> hd v \<in> dlverts t"
  using empty_notin_wf_dlverts hd_in_set[of v] lverts_if_in_verts by fast

lemma dlverts_notin_root_sucs:
  "\<lbrakk>wf_dlverts t; t1 \<in> fst ` fset (sucs t); x \<in> dlverts t1\<rbrakk> \<Longrightarrow> x \<notin> set (root t)"
  using wf_dlverts.simps[of "root t" "sucs t"] by fastforce

lemma dverts_inter_empty_if_verts_inter:
  assumes "dlverts x \<inter> dlverts y = {}" and "wf_dlverts x"
  shows "dverts x \<inter> dverts y = {}"
proof (rule ccontr)
  assume asm: "dverts x \<inter> dverts y \<noteq> {}"
  then obtain r where r_def: "r \<in> dverts x" "r \<in> dverts y" by blast
  then have "r \<noteq> []" using assms(2) by(auto simp: empty_notin_wf_dlverts)
  then obtain v where v_def: "v \<in> set r" by fastforce
  then show False using r_def assms(1) lverts_if_in_verts by (metis IntI all_not_in_conv)
qed

lemma disjoint_dlverts_if_wf: "wf_dlverts t \<Longrightarrow> disjoint_dlverts (sucs t)"
  using wf_dlverts.simps[of "root t" "sucs t"] by simp

lemma disjoint_dlverts_subset:
  assumes "xs |\<subseteq>| ys" and "disjoint_dlverts ys"
  shows "disjoint_dlverts xs"
proof (rule ccontr)
  assume "\<not> disjoint_dlverts xs"
  then obtain x e1 y e2 where x_def: "(x,e1) \<in> fset xs" "(y,e2) \<in> fset xs"
      "dlverts x \<inter> dlverts y \<noteq> {} \<and> (x,e1)\<noteq>(y,e2)"
    by blast
  have "(x,e1) \<in> fset ys" "(y,e2) \<in> fset ys" using x_def(1,2) assms(1) less_eq_fset.rep_eq by fast+
  then show False using assms(2) x_def(3) by fast
qed

lemma root_empty_inter_subset:
  assumes "xs |\<subseteq>| ys" and "\<forall>(x,e1) \<in> fset ys. set r \<inter> dlverts x = {}"
  shows "\<forall>(x,e1) \<in> fset xs. set r \<inter> dlverts x = {}"
  using assms less_eq_fset.rep_eq by force

lemma wf_dlverts_sub:
  assumes "xs |\<subseteq>| ys" and "wf_dlverts (Node r ys)"
  shows "wf_dlverts (Node r xs)"
proof (rule ccontr)
  assume asm: "\<not>wf_dlverts (Node r xs)"
  have "disjoint_dlverts xs" using assms(2) disjoint_dlverts_subset[OF assms(1)] by simp
  moreover have "r \<noteq> []" using assms(2) by simp
  moreover have "(\<forall>(x,e1) \<in> fset xs. set r \<inter> dlverts x = {})"
    using assms(2) root_empty_inter_subset[OF assms(1)] by fastforce
  ultimately obtain x e where x_def: "(x,e) \<in> fset xs" "\<not>wf_dlverts x" using asm by auto
  then have "(x,e) \<in> fset ys" using assms(1) fin_mono by metis
  then show False using assms(2) x_def(2) by fastforce
qed

lemma wf_dlverts_sucs: "\<lbrakk>wf_dlverts t; x \<in> fset (sucs t)\<rbrakk> \<Longrightarrow> wf_dlverts (Node (root t) {|x|})"
  using wf_dlverts_sub[of "{|x|}" "sucs t" "root t"] by (simp add: less_eq_fset.rep_eq)

lemma wf_dverts_if_wf_dlverts: "wf_dlverts t \<Longrightarrow> wf_dverts t"
proof(induction t)
  case (Node r xs)
  then have "\<forall>(x,e) \<in> fset xs. wf_dverts x" by auto
  moreover have "\<forall>(x,e) \<in> fset xs. r \<notin> dverts x"
    using nempty_inter_notin_dverts Node.prems by fastforce
  ultimately show ?case
    using Node.prems dverts_inter_empty_if_verts_inter wf_dverts_iff_dverts'
    by (smt (verit, del_insts) wf_dlverts.simps wf_dverts'.simps case_prodD case_prodI2)
qed

lemma notin_dlverts_child_if_wf_in_root:
  "\<lbrakk>wf_dlverts (Node r xs); x \<in> set r; t \<in> fst ` fset xs\<rbrakk> \<Longrightarrow> x \<notin> dlverts t"
  by fastforce

lemma notin_dlverts_suc_if_wf_in_root:
  "\<lbrakk>wf_dlverts t1; x \<in> set (root t1); t2 \<in> fst ` fset (sucs t1)\<rbrakk> \<Longrightarrow> x \<notin> dlverts t2"
  using notin_dlverts_child_if_wf_in_root[of "root t1" "sucs t1"] by simp

lemma root_if_same_lvert_wf:
  "\<lbrakk>wf_dlverts (Node r xs); x \<in> set r; v \<in> dverts (Node r xs); x \<in> set v\<rbrakk> \<Longrightarrow> v = r"
  by (fastforce simp: lverts_if_in_verts dverts_child_if_not_root notin_dlverts_child_if_wf_in_root)

lemma dverts_same_if_set_wf:
  "\<lbrakk>wf_dlverts t; v1 \<in> dverts t; v2 \<in> dverts t; x \<in> set v1; x \<in> set v2\<rbrakk> \<Longrightarrow> v1 = v2"
proof(induction t)
  case (Node r xs)
  then show ?case
  proof(cases "x \<in> set r")
    case True
    then show ?thesis using Node.prems(2,3,4,5) root_if_same_lvert_wf[OF Node.prems(1)] by blast
  next
    case False
    then obtain t2 e2 where t2_def: "(t2,e2) \<in> fset xs" "x \<in> dlverts t2"
      using Node.prems(2,4) lverts_if_in_verts by fastforce
    then have "\<forall>(t3,e3)\<in>fset xs. (t3,e3) = (t2,e2) \<or> x \<notin> dlverts t3"
      using Node.prems(1) by fastforce
    then have "v1 \<in> dverts t2 \<and> v2 \<in> dverts t2"
      using Node.prems(2-5) lverts_if_in_verts False by force
    then show ?thesis using Node.IH t2_def(1) Node.prems(1,4,5) by auto
  qed
qed

lemma dtree_from_list_empty_inter_iff:
  "(\<forall>v \<in> fst ` set ((v, e) # xs). set r \<inter> set v = {})
    \<longleftrightarrow> (\<forall>(x,e1) \<in> fset {|(dtree_from_list v xs,e)|}. set r \<inter> dlverts x = {})" (is "?P \<longleftrightarrow> ?Q")
proof
  assume asm: "?P"
  have "dverts (dtree_from_list v xs) = fst ` set ((v,e)#xs)"
    by(simp add: dtree_from_list_eq_dverts)
  then show ?Q using list_in_verts_if_lverts asm by fastforce
next
  assume asm: "?Q"
  have "dverts (dtree_from_list v xs) = fst ` set ((v,e)#xs)"
    by(simp add: dtree_from_list_eq_dverts)
  moreover have "(dtree_from_list v xs,e) \<in> fset {|(dtree_from_list v xs, e)|}" by simp
  ultimately show "?P" using asm lverts_if_in_verts by fast
qed

lemma wf_dlverts_iff_wf_list_lverts:
  "(\<forall>v \<in> fst ` set xs. set r \<inter> set v = {}) \<and> r \<noteq> [] \<and> wf_list_lverts xs
    \<longleftrightarrow> wf_dlverts (dtree_from_list r xs)"
proof(induction xs arbitrary: r rule: wf_list_lverts.induct)
  case (2 v e xs)
  then show ?case using dtree_from_list_empty_inter_iff[of v e] by auto
qed (simp)

lemma vert_disjoint_if_not_root:
  assumes "wf_dlverts t"
      and "v \<in> dverts t - {root t}"
    shows "set (root t) \<inter> set v = {}"
proof -
  obtain t1 e1 where t1_def: "(t1,e1) \<in> fset (sucs t)" "v \<in> dverts t1"
    using assms(2) dtree.set_cases(1) by force
  then show ?thesis using assms(1) wf_dlverts.simps[of "root t"] lverts_if_in_verts by fastforce
qed

lemma vert_disjoint_if_to_list:
  "\<lbrakk>wf_dlverts (Node r {|(t1,e1)|}); v \<in> fst ` set (dtree_to_list t1)\<rbrakk>
    \<Longrightarrow> set (root t1) \<inter> set v = {}"
  using vert_disjoint_if_not_root dtree_to_list_sub_dverts wf_dverts_if_wf_dlverts by fastforce

lemma wf_list_lverts_if_wf_dlverts: "wf_dlverts t \<Longrightarrow> wf_list_lverts (dtree_to_list t)"
proof(induction t)
  case (Node r xs)
  then show ?case
  proof(cases "\<forall>x. xs \<noteq> {|x|}")
    case True
    then show ?thesis using dtree_to_list.simps(2) by simp
  next
    case False
    then obtain t1 e1 where t1_def: "xs = {|(t1,e1)|}" by auto
    then have "wf_dlverts t1" using Node.prems by simp
    then have "root t1 \<noteq> []" using wf_dlverts.simps[of "root t1" "sucs t1"] by simp
    then show ?thesis using Node vert_disjoint_if_to_list t1_def by fastforce
  qed
qed

lemma child_in_dlverts: "(t1,e) \<in> fset xs \<Longrightarrow> dlverts t1 \<subseteq> dlverts (Node r xs)"
  by force

lemma suc_in_dlverts: "(t1,e) \<in> fset (sucs t2) \<Longrightarrow> dlverts t1 \<subseteq> dlverts t2"
  using child_in_dlverts[of t1 e "sucs t2" "root t2"] by auto

lemma suc_in_dlverts': "t1 \<in> fst ` fset (sucs t2) \<Longrightarrow> dlverts t1 \<subseteq> dlverts t2"
  using suc_in_dlverts by fastforce

lemma subtree_in_dlverts: "is_subtree t1 t2 \<Longrightarrow> dlverts t1 \<subseteq> dlverts t2"
  by(induction t2) fastforce

lemma subtree_root_if_dlverts: "x \<in> dlverts t \<Longrightarrow> \<exists>r xs. is_subtree (Node r xs) t \<and> x \<in> set r"
  using subtree_root_if_dverts list_in_verts_if_lverts by fast

lemma x_not_root_strict_subtree:
  assumes "x \<in> dlverts t" and "x \<notin> set (root t)"
  shows "\<exists>r xs t1. is_subtree (Node r xs) t \<and> t1 \<in> fst ` fset xs \<and> x \<in> set (root t1)"
proof -
  obtain r xs where r_def: "is_subtree (Node r xs) t" "x \<in> set r"
    using subtree_root_if_dlverts[OF assms(1)] by fast
  then have sub: "strict_subtree (Node r xs) t" using assms(2) strict_subtree_def by fastforce
  then show ?thesis using assms(2) subtree_child_if_strict_subtree[OF sub] r_def(2) by force
qed

lemma dverts_disj_if_wf_dlverts:
  "\<lbrakk>wf_dlverts t; v1 \<in> dverts t; v2 \<in> dverts t; v1 \<noteq> v2\<rbrakk> \<Longrightarrow> set v1 \<inter> set v2 = {}"
  using dverts_same_if_set_wf by fast

thm empty_notin_wf_dlverts

lemma wf_dlverts'_if_dlverts: "wf_dlverts t \<Longrightarrow> wf_dlverts' t"
  using wf_dlverts'_def empty_notin_wf_dlverts dverts_disj_if_wf_dlverts wf_dverts_if_wf_dlverts
  by blast

lemma disjoint_dlverts_if_wf'_aux:
  assumes "wf_dlverts' (Node r xs)"
      and "(t1,e1) \<in> fset xs"
      and "(t2,e2) \<in> fset xs"
      and "(t1,e1) \<noteq> (t2,e2)"
    shows "dlverts t1 \<inter> dlverts t2 = {}"
proof(rule ccontr)
  assume "dlverts t1 \<inter> dlverts t2 \<noteq> {}"
  then obtain x y where x_def: "x \<in> dverts t1" "y \<in> dverts t2" "set x \<inter> set y \<noteq> {}"
    using dlverts_eq_dverts_union[of t1] dlverts_eq_dverts_union[of t2] by auto
  then have "x \<in> dverts (Node r xs)" "y \<in> dverts (Node r xs)"
    using dverts_child_subseteq assms(2,3) by auto
  moreover have "x \<noteq> y"
    using assms(1) disjoint_dverts_if_wf_aux[rotated, OF assms(2-4)] x_def(1,2)
    unfolding wf_dlverts'_def by blast
  ultimately show False using assms(1) x_def(3) unfolding wf_dlverts'_def by blast
qed

lemma disjoint_dlverts_if_wf': "wf_dlverts' (Node r xs) \<Longrightarrow> disjoint_dlverts xs"
  using disjoint_dlverts_if_wf'_aux by fast

lemma root_nempty_if_wf': "wf_dlverts' (Node r xs) \<Longrightarrow> r \<noteq> []"
  unfolding wf_dlverts'_def by fastforce

lemma disjoint_root_if_wf'_aux:
  assumes "wf_dlverts' (Node r xs)"
      and "(t1,e1) \<in> fset xs"
    shows "set r \<inter> dlverts t1 = {}"
proof(rule ccontr)
  assume "set r \<inter> dlverts t1 \<noteq> {}"
  then obtain x where x_def: "x \<in> dverts t1" "set x \<inter> set r \<noteq> {}"
    using dlverts_eq_dverts_union by fast
  then have "x \<in> dverts (Node r xs)" using dverts_child_subseteq assms(2) by auto
  moreover have "r \<in> dverts (Node r xs)" by simp
  moreover have "x \<noteq> r"
    using assms x_def(1) root_not_child_if_wf_dverts unfolding wf_dlverts'_def by fast
  ultimately show False using assms(1) x_def(2) unfolding wf_dlverts'_def by blast
qed

lemma disjoint_root_if_wf':
  "wf_dlverts' (Node r xs) \<Longrightarrow> \<forall>(t1,e1) \<in> fset xs. set r \<inter> dlverts t1 = {}"
  using disjoint_root_if_wf'_aux by fast

lemma wf_dlverts_if_dlverts': "wf_dlverts' t \<Longrightarrow> wf_dlverts t"
proof(induction t)
  case (Node r xs)
  then have "\<forall>(t1,e1) \<in> fset xs. set r \<inter> dlverts t1 = {}"
    using disjoint_root_if_wf' by blast
  moreover have "r \<noteq> [] \<and> disjoint_dlverts xs"
    using disjoint_dlverts_if_wf' Node.prems root_nempty_if_wf' by fast
  moreover have "\<forall>(t1,e1) \<in> fset xs. wf_dlverts t1"
    using Node wf_dlverts'_rec by fastforce
  ultimately show ?case by auto
qed

lemma wf_dlverts_iff_dlverts': "wf_dlverts t \<longleftrightarrow> wf_dlverts' t"
  using wf_dlverts_if_dlverts' wf_dlverts'_if_dlverts by blast

locale list_dtree =
  fixes t :: "('a list,'b) dtree"
  assumes wf_arcs: "wf_darcs t"
      and wf_lverts: "wf_dlverts t"

sublocale list_dtree \<subseteq> wf_dtree
  using wf_arcs wf_lverts wf_dverts_if_wf_dlverts by(unfold_locales) auto

theorem list_dtree_iff_wf_list:
  "wf_list_arcs xs \<and> (\<forall>v \<in> fst ` set xs. set r \<inter> set v = {}) \<and> r \<noteq> [] \<and> wf_list_lverts xs
    \<longleftrightarrow> list_dtree (dtree_from_list r xs)"
  using wf_darcs_iff_wf_list_arcs wf_dlverts_iff_wf_list_lverts list_dtree_def by metis

lemma list_dtree_subset:
  assumes "xs |\<subseteq>| ys" and "list_dtree (Node r ys)"
  shows "list_dtree (Node r xs)"
  using wf_dlverts_sub[OF assms(1)] wf_darcs_sub[OF assms(1)] assms(2)
  by (unfold_locales) (fast dest: list_dtree.wf_lverts list_dtree.wf_arcs)+

context fin_list_directed_tree
begin

lemma dlverts_disjoint:
  assumes "r \<in> verts T" and "(Node r xs) = to_dtree_aux r"
      and "(x,e1) \<in> fset xs" and "(y,e2) \<in> fset xs" and "(x,e1)\<noteq>(y,e2)"
    shows "dlverts x \<inter> dlverts y = {}"
proof (rule ccontr)
  assume "dlverts x \<inter> dlverts y \<noteq> {}"
  then obtain v where v_def[simp]: "v \<in> dlverts x" "v \<in> dlverts y" by blast
  obtain x1 where x1_def: "v \<in> set x1" "x1 \<in> dverts x" using list_in_verts_if_lverts by force
  obtain y1 where y1_def: "v \<in> set y1" "y1 \<in> dverts y" using list_in_verts_if_lverts by force
  have 0: "y = to_dtree_aux (Dtree.root y)" using to_dtree_aux_self assms(2,4) by blast
  have "r \<rightarrow>\<^bsub>T\<^esub> Dtree.root y"
    using assms(2,4) dominated_if_child by (metis (no_types, opaque_lifting) fst_conv image_iff)
  then have 1: "Dtree.root y \<in> verts T" using adj_in_verts(2) by simp
  have "r \<rightarrow>\<^bsub>T\<^esub> Dtree.root x"
    using assms(2,3) dominated_if_child by (metis (no_types, opaque_lifting) fst_conv image_iff)
  then have "Dtree.root x \<in> verts T" using adj_in_verts(2) by simp
  moreover have "x = to_dtree_aux (Dtree.root x)" using to_dtree_aux_self assms(2,3) by blast
  ultimately have "Dtree.root x \<rightarrow>\<^sup>*\<^bsub>T\<^esub> x1" using to_dtree_aux_dverts_reachable x1_def(2) by blast
  moreover have "Dtree.root y \<rightarrow>\<^sup>*\<^bsub>T\<^esub> y1" using 0 1 to_dtree_aux_dverts_reachable y1_def(2) by blast
  ultimately have "x1 = y1" using disjoint_verts reachable_in_verts(2) x1_def(1) y1_def(1) by auto
  then show False using dverts_disjoint[OF assms(2-5)] x1_def(2) y1_def(2) by blast
qed

lemma wf_dlverts_to_dtree_aux: "\<lbrakk>r \<in> verts T; t = to_dtree_aux r\<rbrakk> \<Longrightarrow> wf_dlverts t"
proof(induction t arbitrary: r rule: darcs_mset.induct)
  case (1 r' xs)
  then have "r = r'" by simp
  have "\<forall>(x,e) \<in> fset xs. wf_dlverts x \<and> set r \<inter> dlverts x = {}"
  proof (standard, standard, standard)
    fix xp x e
    assume asm: "xp \<in> fset xs" "xp = (x,e)"
    then have 0: "x = to_dtree_aux (Dtree.root x)" using to_dtree_aux_self "1.prems"(2) by simp
    have 2: "r \<rightarrow>\<^bsub>T\<^esub> Dtree.root x" using asm "1.prems" \<open>r = r'\<close>
      by (metis (no_types, opaque_lifting) dominated_if_child fst_conv image_iff)
    then have 3: "Dtree.root x \<in> verts T" using adj_in_verts(2) by simp
    then show "wf_dlverts x" using "1.IH" asm 0 by blast
    have "r \<notin> dverts x"
    proof
      assume "r \<in> dverts x"
      then have "Dtree.root x \<rightarrow>\<^sup>*\<^bsub>T\<^esub> r" using 0 3 to_dtree_aux_dverts_reachable by blast
      then have "r \<rightarrow>\<^sup>+\<^bsub>T\<^esub> r" using 2 by auto
      then show False using reachable1_not_reverse by blast
    qed
    then show "set r \<inter> dlverts x = {}"
      using 0 "1.prems"(1) 3 disjoint_iff_not_equal disjoint_verts list_in_verts_if_lverts
      by (metis reachable_in_verts(2) to_dtree_aux_dverts_reachable)
  qed
  moreover have "disjoint_dlverts xs" using dlverts_disjoint "1.prems" by fastforce
  ultimately show ?case using \<open>r = r'\<close> by (auto simp add: "1.prems"(1) nempty_verts)
qed

lemma wf_dlverts_to_dtree: "wf_dlverts to_dtree"
  using to_dtree_def wf_dlverts_to_dtree_aux root_in_T by blast

theorem list_dtree_to_dtree: "list_dtree to_dtree"
  using list_dtree_def wf_dlverts_to_dtree wf_darcs_to_dtree by blast

end

context list_dtree
begin

lemma list_dtree_rec: "\<lbrakk>Node r xs = t; (x,e) \<in> fset xs\<rbrakk> \<Longrightarrow> list_dtree x"
  using wf_arcs wf_lverts by(unfold_locales) auto

lemma list_dtree_rec_suc: "(x,e) \<in> fset (sucs t) \<Longrightarrow> list_dtree x"
  using list_dtree_rec[of "root t"] by force

lemma list_dtree_sub: "is_subtree x t \<Longrightarrow> list_dtree x"
using list_dtree_axioms proof(induction t rule: darcs_mset.induct)
  case (1 r xs)
  then interpret list_dtree "Node r xs" by blast
  show ?case
  proof(cases "x = Node r xs")
    case True
    then show ?thesis by (simp add: "1.prems")
  next
    case False
    then show ?thesis using "1.IH" list_dtree_rec "1.prems"(1) by auto
  qed
qed

theorem from_dtree_fin_list_dir: "fin_list_directed_tree (root t) (from_dtree dt dh t)"
  unfolding fin_list_directed_tree_def fin_list_directed_tree_axioms_def
  by (auto simp: from_dtree_fin_directed empty_notin_wf_dlverts[OF wf_lverts]
      intro: wf_lverts dverts_same_if_set_wf)

subsection \<open>Combining Preserves Well-Formedness\<close>

lemma remove_child_sub: "remove_child x xs |\<subseteq>| xs"
  by auto

lemma child2_commute_aux:
  assumes "f = (\<lambda>(t,_) b. case t of Node r ys \<Rightarrow> if r = a then ys |\<union>| b else b)"
  shows "(f y \<circ> f x) z = (f x \<circ> f y) z"
proof -
  obtain r1 ys1 e1 where y_def: "y = (Node r1 ys1, e1)" by (metis dtree.exhaust eq_snd_iff)
  obtain r2 ys2 e2 where "x = (Node r2 ys2, e2)" by (metis dtree.exhaust eq_snd_iff)
  then show ?thesis by (simp add: assms funion_left_commute y_def)
qed

lemma child2_commute:
  "comp_fun_commute (\<lambda>(t,_) b. case t of Node r ys \<Rightarrow> if r = x then ys |\<union>| b else b)"
  using comp_fun_commute_def child2_commute_aux by fastforce

interpretation Comm:
  comp_fun_commute "\<lambda>(t,_) b. case t of Node r ys \<Rightarrow> if r = x then ys |\<union>| b else b"
  by (rule child2_commute)

lemma input_in_child2:
  "zs |\<subseteq>| child2 x zs ys"
proof(induction ys)
  case empty
  then show ?case using Comm.ffold_empty by simp
next
  case (insert y ys)
  then obtain r xs e where r_def: "(Node r xs,e) = y" by (metis dtree.exhaust surj_pair)
  let ?f = "(\<lambda>(t,_) b. case t of Node r ys \<Rightarrow> if r = x then ys |\<union>| b else b)"
  show ?case
  proof(cases "r=x")
    case True
    then have "ffold ?f zs (finsert y ys) = xs |\<union>| (ffold ?f zs ys)"
      using r_def insert.hyps by force
    then show ?thesis using insert.IH by blast
  next
    case False
    then have "ffold ?f zs (finsert y ys) = (ffold ?f zs ys)" using r_def insert.hyps by force
    then show ?thesis using insert.IH by blast
  qed
qed

lemma child2_subset_if_input1:
  "zs' |\<subseteq>| zs \<Longrightarrow> child2 x zs' ys |\<subseteq>| child2 x zs ys"
proof(induction ys)
  case (insert y ys)
  obtain r xs e where r_def: "(Node r xs, e) = y" by (metis dtree.exhaust surj_pair)
  let ?f = "(\<lambda>(t,_) b. case t of Node r ys \<Rightarrow> if r = x then ys |\<union>| b else b)"
  show ?case
  proof(cases "r=x")
    case True
    then have "ffold ?f zs (finsert y ys) = xs |\<union>| (ffold ?f zs ys)"
      using r_def insert.hyps by force
    moreover have "ffold ?f zs' (finsert y ys) = xs |\<union>| (ffold ?f zs' ys)"
      using r_def insert.hyps True by force
    ultimately show ?thesis using insert by blast
  next
    case False
    then have "ffold ?f zs (finsert y ys) = (ffold ?f zs ys)" using r_def insert.hyps by force
    moreover have "ffold ?f zs' (finsert y ys) = (ffold ?f zs' ys)"
      using r_def insert.hyps False by force
    ultimately show ?thesis using insert by blast
  qed
qed (simp)

lemma child2_subset_if_input2:
  "ys' |\<subseteq>| ys \<Longrightarrow> child2 x xs ys' |\<subseteq>| child2 x xs ys"
proof(induction "fcard ys" arbitrary: ys)
  case (Suc n)
  show ?case
  proof(cases "ys' = ys")
    case False
    then obtain z where z_def: "z |\<in>| ys \<and> z |\<notin>| ys'" using Suc.prems by blast
    then obtain zs where zs_def: "finsert z zs = ys \<and> z |\<notin>| zs" by blast
    then have "ys' |\<subseteq>| zs \<and> fcard zs = n"
      using Suc.prems(1) Suc.hyps(2) z_def fcard_finsert_disjoint by fastforce
    then have 0: "child2 x xs ys' |\<subseteq>| child2 x xs zs" using Suc.hyps(1) by blast
    obtain r rs e where r_def: "(Node r rs, e) = z" by (metis dtree.exhaust surj_pair)
    then show ?thesis using 0 zs_def by force
  qed (simp)
qed (simp)

lemma darcs_split: "darcs (Node r (xs|\<union>|ys)) = darcs (Node r xs) \<union> darcs (Node r ys)"
  by simp

lemma darcs_sub_if_children_sub: "xs |\<subseteq>| ys \<Longrightarrow> darcs (Node r xs) \<subseteq> darcs (Node v ys)"
proof(induction "fcard ys" arbitrary: ys)
  case (Suc n)
  then show ?case
  proof(cases "ys = xs")
    case False
    then obtain z where z_def: "z |\<in>| ys \<and> z |\<notin>| xs" using Suc.prems by blast
    then obtain zs where zs_def: "finsert z zs = ys \<and> z |\<notin>| zs" by blast
    then have "xs |\<subseteq>| zs \<and> fcard zs = n"
      using Suc.prems(1) Suc.hyps(2) z_def fcard_finsert_disjoint by fastforce
    then have "darcs (Node r xs) \<subseteq> darcs (Node v zs)" using Suc.hyps(1) by blast
    then show ?thesis using zs_def darcs_split[of v "{|z|}" zs] by auto
  qed (simp)
qed (simp)

lemma darc_in_child2_snd_if_nin_fst:
  "e \<in> darcs (Node x (child2 a xs ys)) \<Longrightarrow> e \<notin> darcs (Node v ys) \<Longrightarrow> e \<in> darcs (Node r xs)"
proof(induction "ys")
  case (insert y ys)
  obtain r rs e1 where r_def: "(Node r rs, e1) = y" by (metis dtree.exhaust surj_pair)
  then have e_not_rs: "e \<notin> darcs (Node x rs)" using insert.prems(2) by fastforce
  show ?case
  proof(cases "r = a")
    case True
    then have "darcs (Node x (child2 a xs (finsert y ys)))
              = darcs (Node x (rs |\<union>| (child2 a xs ys)))"
      using r_def insert.hyps(1) by force
    moreover have "\<dots> = darcs (Node x rs) \<union> darcs (Node x (child2 a xs ys))" by simp
    ultimately have "e \<in> darcs (Node x (child2 a xs ys))" using insert.prems(1) e_not_rs by blast
    then show ?thesis using insert.IH insert.prems(2) by simp
  next
    case False
    then have "darcs (Node x (child2 a xs (finsert y ys))) = darcs (Node x (child2 a xs ys))"
      using r_def insert.hyps(1) by force
    then show ?thesis using insert.IH insert.prems by simp
  qed
qed (simp)

lemma darc_in_child2_fst_if_nin_snd:
  "e \<in> darcs (Node x (child2 a xs ys)) \<Longrightarrow> e \<notin> darcs (Node v xs) \<Longrightarrow> e \<in> darcs (Node r ys)"
  using darc_in_child2_snd_if_nin_fst by fast

lemma darcs_child2_sub: "darcs (Node x (child2 y xs ys)) \<subseteq> darcs (Node r xs) \<union> darcs (Node r' ys)"
  using darc_in_child2_snd_if_nin_fst by fast

lemma darcs_combine_sub_orig: "darcs (combine x y t1) \<subseteq> darcs t1"
proof(induction t1)
  case ind: (Node r xs)
  show ?case
  proof(cases "x=r \<and> (\<exists>t. t \<in> fst ` fset xs \<and> root t = y)")
    case True
    then have "darcs (combine x y (Node r xs))
            = darcs (Node (x@y) (child2 y (remove_child y xs) xs))" by simp
    also have "\<dots> \<subseteq> darcs (Node x (child2 y xs xs))"
      using darcs_sub_if_children_sub[of "child2 y (remove_child y xs) xs" "child2 y xs xs"]
          child2_subset_if_input1[of "remove_child y xs" xs] remove_child_sub by fast
    finally show ?thesis using darcs_child2_sub by fast
  next
    case False
    then have "darcs (combine x y (Node r xs))
              = darcs (Node r ((\<lambda>(t,e). (combine x y t,e)) |`| xs))"
      by auto
    also have "\<dots> \<subseteq> (\<Union>(t,e)\<in>fset xs. \<Union> (darcs ` {t}) \<union> {e})"
      using ind.IH wf_dtree_rec by fastforce
    finally show ?thesis by force
  qed
qed

lemma child2_in_child:
  "\<lbrakk>b \<in> fset (child2 a ys xs); b |\<notin>| ys\<rbrakk> \<Longrightarrow> \<exists>rs e. (Node a rs, e) \<in> fset xs \<and> b |\<in>| rs"
proof(induction xs)
  case (insert x xs)
  obtain r rs e1 where r_def: "(Node r rs, e1) = x" by (metis dtree.exhaust surj_pair)
  show ?case
  proof(cases "r = a")
    case ra: True
    then have 0: "child2 a ys (finsert x xs) = rs |\<union>| (child2 a ys xs)"
      using r_def insert.hyps(1) by force
    show ?thesis
    proof(cases "b |\<in>| rs")
      case True
      then show ?thesis using r_def ra by auto
    next
      case False
      then have "b \<in> fset (child2 a ys xs)" using insert.prems(1) 0 by force
      then show ?thesis using insert.IH insert.prems(2) by auto
    qed
  next
    case False
    then show ?thesis using insert r_def by force
  qed
qed simp

lemma child_in_darcs: "(y,e2) \<in> fset xs \<Longrightarrow> darcs y \<union> {e2} \<subseteq> darcs (Node r xs)"
  by force

lemma disjoint_darcs_child2:
  assumes "wf_darcs (Node r xs)"
  shows "disjoint_darcs (child2 a (remove_child a xs) xs)" (is "disjoint_darcs ?P")
proof (rule ccontr)
  assume "\<not> disjoint_darcs ?P"
  then obtain x e1 y e2 where asm: "(x,e1) \<in> fset ?P" "(y,e2) \<in> fset ?P" "(e1 \<in> darcs x \<or>
      ((darcs x \<union> {e1}) \<inter> (darcs y \<union> {e2}) \<noteq> {} \<and> (x,e1)\<noteq>(y,e2)))" by blast
  note wf_darcs_iff_darcs'[simp]
  consider "(x,e1) \<in> fset (remove_child a xs)" "e1 \<in> darcs x"
    | "(x,e1) \<in> fset (remove_child a xs)" "e1 \<notin> darcs x" "(y,e2) \<in> fset (remove_child a xs)"
    | "(x,e1) \<in> fset (remove_child a xs)" "e1 \<notin> darcs x" "(y,e2) |\<notin>| (remove_child a xs)"
    | "(x,e1) |\<notin>| (remove_child a xs)" "e1 \<in> darcs x"
    | "(x,e1) |\<notin>| (remove_child a xs)" "e1 \<notin> darcs x" "(y,e2) \<in> fset (remove_child a xs)"
    | "(x,e1) |\<notin>| (remove_child a xs)" "e1 \<notin> darcs x" "(y,e2) |\<notin>| (remove_child a xs)"
    by auto
  then show False
  proof(cases)
    case 1
    then show ?thesis using assms by auto
  next
    case 2
    then show ?thesis using assms asm(3) by fastforce
  next
    case 3
    then have x_xs: "(x,e1) \<in> fset xs" by simp
    obtain rs2 re2 where r2_def: "(Node a rs2, re2) \<in> fset xs" "(y,e2) |\<in>| rs2"
      using child2_in_child asm(2) 3(3) by fast
    then have "darcs y \<union> {e2} \<subseteq> darcs (Node a rs2)" using child_in_darcs by fast
    then have "(darcs x \<union> {e1}) \<inter> (darcs (Node a rs2) \<union> {re2}) \<noteq> {}" using 3(2) asm(3) by blast
    moreover have "(x,e1)\<noteq>(Node a rs2, re2)" using 3(1) by force
    ultimately have "\<not> disjoint_darcs xs" using r2_def(1) x_xs by fast
    then show ?thesis using assms by simp
  next
    case 4
    then obtain rs1 re1 where r1_def: "(Node a rs1, re1) \<in> fset xs" "(x,e1) |\<in>| rs1"
      using child2_in_child asm(1) by fast
    then have "\<not>disjoint_darcs rs1" using 4(2) by fast
    then show ?thesis using assms r1_def(1) by fastforce
  next
    case 5
    then obtain rs1 re1 where r1_def: "(Node a rs1, re1) \<in> fset xs" "(x,e1) |\<in>| rs1"
      using child2_in_child asm(1) by fast
    have 1: "(darcs (Node a rs1) \<union> {re1}) \<inter> (darcs y \<union> {e2}) \<noteq> {}"
      using r1_def(2) asm(3) 5(2) child_in_darcs by fast
    have y_xs: "(y,e2) \<in> fset xs" using 5(3) by simp
    then have "(Node a rs1, re1)\<noteq>(y,e2)" using 5(3) by force
    then have "\<not> disjoint_darcs xs" using r1_def(1) y_xs 1 by fast
    then show ?thesis using assms by simp
  next
    case 6
    then obtain rs1 re1 where r1_def: "(Node a rs1, re1) \<in> fset xs" "(x,e1) |\<in>| rs1"
      using child2_in_child asm(1) by fast
    then have 1: "(darcs (Node a rs1) \<union> {re1}) \<inter> (darcs y \<union> {e2}) \<noteq> {}"
      using asm(3) 6(2) child_in_darcs by fast
    obtain rs2 re2 where r2_def: "(Node a rs2, re2) \<in> fset xs" "(y,e2) |\<in>| rs2"
      using child2_in_child asm(2) 6(3) by fast
    then have "darcs y \<union> {e2} \<subseteq> darcs (Node a rs2)" using child_in_darcs by fast
    then have 1: "(darcs (Node a rs1) \<union> {re1}) \<inter> (darcs (Node a rs2) \<union> {re2}) \<noteq> {}"
      using 1 asm(3) 6(2) child_in_darcs by blast
    then show ?thesis
    proof(cases "(Node a rs1, re1) = (Node a rs2, re2)")
      case True
      then have "(x,e1) \<in> fset rs1 \<and> (y,e2) \<in> fset rs1"
        using r1_def(2) r2_def(2) by fast
      then show ?thesis using assms r1_def asm(3) 6(2) by fastforce
    next
      case False
      then have "\<not> disjoint_darcs xs" using r1_def(1) r2_def(1) 1 by fast
      then show ?thesis using assms by simp
    qed
  qed
qed

lemma wf_darcs_child2:
  assumes "wf_darcs (Node r xs)" and "(x,e) \<in> fset (child2 a (remove_child a xs) xs)"
  shows "wf_darcs x"
proof(cases "(x,e) |\<in>| remove_child a xs")
  case True
  then show ?thesis using assms(1) by (fastforce simp: wf_darcs_iff_darcs')
next
  case False
  then obtain r rs e1  where "(Node r rs, e1) \<in> fset xs \<and> (x,e) |\<in>| rs \<and> r = a"
    using child2_in_child assms(2) by fast
  then show ?thesis using assms by (fastforce simp: wf_darcs_iff_darcs')
qed

lemma disjoint_darcs_combine:
  assumes "Node r xs = t"
  shows "disjoint_darcs ((\<lambda>(t,e). (combine x y t,e)) |`| xs)"
proof -
  have "disjoint_darcs xs" using wf_arcs assms by (fastforce simp: wf_darcs_iff_darcs')
  then show ?thesis
    using disjoint_darcs_img[of xs "combine x y"] by (simp add: darcs_combine_sub_orig)
qed

lemma wf_darcs_combine: "wf_darcs (combine x y t)"
using list_dtree_axioms proof(induction t)
  case ind: (Node r xs)
  then interpret list_dtree "Node r xs" using ind.prems by blast
  show ?case
  proof(cases "x=r \<and> (\<exists>t. t \<in> fst ` fset xs \<and> root t = y)")
    case True
    have "disjoint_darcs (child2 y (remove_child y xs) xs)"
      using disjoint_darcs_child2[OF wf_arcs] by simp
    moreover have "\<forall>(x,e) \<in> fset (child2 y (remove_child y xs) xs). wf_darcs x"
      using wf_darcs_child2 wf_arcs by fast
    ultimately show ?thesis using True by (simp add: wf_darcs_iff_darcs')
  next
    case False
    have "disjoint_darcs ((\<lambda>(t,e). (combine x y t, e)) |`| xs)"
      using disjoint_darcs_combine ind.prems by simp
    moreover have "\<forall>(x,e) \<in> fset xs. list_dtree x" using list_dtree_rec by blast
    ultimately show ?thesis using False ind.IH ind.prems by (auto simp: wf_darcs_iff_darcs')
  qed
qed

lemma v_in_dlverts_if_in_comb: "v \<in> dlverts (combine x y t) \<Longrightarrow> v \<in> dlverts t"
using list_dtree_axioms proof(induction t)
  case ind: (Node r xs)
  then interpret list_dtree "Node r xs" using ind.prems by blast
  show ?case
  proof(cases "x=r \<and> (\<exists>t. t \<in> fst ` fset xs \<and> root t = y)")
    case x_and_y: True
    show ?thesis
    proof(cases "v \<in> set x \<union> set y")
      case True
      then show ?thesis using x_and_y dtree.set_sel(1) lverts_if_in_verts by fastforce
    next
      case False
      then obtain t e where t_def: "(t,e) \<in> fset (child2 y (remove_child y xs) xs)" "v \<in> dlverts t"
        using x_and_y ind.prems by auto
      then show ?thesis
      proof(cases "(t,e) |\<in>| (remove_child y xs)")
        case True
        then have "(t,e) \<in> fset (remove_child y xs)" by fast
        then show ?thesis using t_def(2) by force
      next
        case False
        then obtain r1 rs1 re1 where r1_def: "(Node r1 rs1, re1) \<in> fset xs" "(t,e) |\<in>| rs1"
          using child2_in_child t_def(1) by fast
        have "is_subtree t (Node r1 rs1)" using subtree_if_child r1_def(2)
          by (metis image_iff prod.sel(1))
        moreover have "is_subtree (Node r1 rs1) (Node r xs)"
          using subtree_if_child r1_def(1) by fastforce
        ultimately have "is_subtree t (Node r xs)" using subtree_trans by blast
        then show ?thesis using t_def(2) subtree_in_dlverts by blast
      qed
    qed
  next
    case rec: False
    then show ?thesis
    proof(cases "v \<in> set r")
      case False
      then have "\<exists>(t,e) \<in> fset xs. v \<in> dlverts (combine x y t)"
        using ind.prems list_dtree_rec rec by force
      then show ?thesis using ind.IH list_dtree_rec by fastforce
    qed (simp)
  qed
qed

lemma ex_subtree_if_in_lverts: "v \<in> dlverts t1 \<Longrightarrow> \<exists>t2. is_subtree t2 t1 \<and> v \<in> set (root t2)"
  apply(induction t1)
  apply(cases)
   apply simp
  by fastforce

lemma child'_in_child2:
  assumes "(Node y rs1,e1) \<in> fset xs" and "(t2,e2) \<in> fset rs1"
  shows "(t2,e2) \<in> fset (child2 y ys xs)"
using assms proof(induction xs)
  case (insert x xs)
  obtain r rs re where r_def: "(Node r rs, re) = x" by (metis dtree.exhaust surj_pair)
  show ?case
  proof(cases "r = y")
    case ry: True
    then have 0: "child2 y ys (finsert x xs) = rs |\<union>| (child2 y ys xs)"
      using r_def insert.hyps(1) by force
    then show ?thesis using insert by fastforce
  next
    case False
    then show ?thesis using insert r_def by force
  qed
qed (simp)

lemma v_in_comb_if_in_dlverts: "v \<in> dlverts t \<Longrightarrow> v \<in> dlverts (combine x y t)"
using list_dtree_axioms proof(induction t)
  case ind: (Node r xs)
  then interpret list_dtree "Node r xs" using ind.prems by blast
  show ?case
  proof(cases "x=r \<and> (\<exists>t. t \<in> fst ` fset xs \<and> root t = y)")
    case x_and_y: True
    then have 0: "combine x y (Node r xs) = Node (x@y) (child2 y (remove_child y xs) xs)" by simp
    show ?thesis
    proof(cases "v \<in> set x \<union> set y")
      case True
      then show ?thesis using x_and_y dtree.set_sel(1) lverts_if_in_verts by fastforce
    next
      case False
      obtain t where t_def: "is_subtree t (Node r xs)" "v \<in> set (root t)"
        using ex_subtree_if_in_lverts ind.prems by fast
      then have "Node r xs \<noteq> t" using False x_and_y by fastforce
      then obtain t1 e1 where t1_def: "is_subtree t t1" "(t1,e1) \<in> fset xs"
        using t_def(1) by force
      then show ?thesis
      proof(cases "root t1 = y")
        case True
        then have "t1 \<noteq> t" using False t_def(2) by blast
        then obtain rs1 where rs1_def: "t1 = Node y rs1" using True dtree.exhaust_sel by blast
        then obtain t2 e2 where t2_def: "is_subtree t t2" "(t2,e2) \<in> fset rs1"
          using \<open>t1\<noteq>t\<close> t1_def(1) by auto
        have "(t2,e2) \<in> fset (child2 y (remove_child y xs) xs)"
          using t2_def(2) rs1_def t1_def(2) child'_in_child2 by fast
        then have "is_subtree t2 (combine x y (Node r xs))" using subtree_if_child 0
          using self_subtree by fastforce
        then have "is_subtree t (combine x y (Node r xs))" using subtree_trans t2_def(1) by blast
        then show ?thesis
          using t_def(2) t2_def(1) subtree_in_dlverts dtree.set_sel(1) lverts_if_in_verts by fast
      next
        case False
        then have "(t1,e1) \<in> fset (remove_child y xs)" using t1_def(2) by simp
        then have "(t1,e1) \<in> fset (child2 y (remove_child y xs) xs)"
          using less_eq_fset.rep_eq input_in_child2 by fast
        then have "is_subtree t (combine x y (Node r xs))"
          using 0 subtree_if_child subtree_trans t1_def(1) by auto
        then show ?thesis
          using t_def(2) subtree_in_dlverts dtree.set_sel(1) lverts_if_in_verts by fast
      qed
    qed
  next
    case rec: False
    then show ?thesis
    proof(cases "v \<in> set r")
      case False
      then obtain t e where t_def: "(t,e) \<in> fset xs" "v \<in> dlverts t" using ind.prems by auto
      then have "v \<in> dlverts (combine x y t)" using ind.IH list_dtree_rec by auto
      then show ?thesis using rec t_def(1) by force
    qed (simp)
  qed
qed

lemma dlverts_comb_id[simp]: "dlverts (combine x y t) = dlverts t"
  using v_in_comb_if_in_dlverts v_in_dlverts_if_in_comb by blast

lemma wf_dlverts_comb_aux:
  assumes "\<forall>(t,e) \<in> fset xs. dlverts (combine x y t) = dlverts t"
      and "\<forall>(t1,e1) \<in> fset xs. \<forall>(t2,e2) \<in> fset xs. dlverts t1 \<inter> dlverts t2 = {} \<or> (t1,e1)=(t2,e2)"
      and "(t1,e1) \<in> fset ((\<lambda>(t,e). (combine x y t, e)) |`| xs)"
      and "(t2,e2) \<in> fset ((\<lambda>(t,e). (combine x y t, e)) |`| xs)"
    shows "dlverts t1 \<inter> dlverts t2 = {} \<or> (t1,e1)=(t2,e2)"
proof -
  obtain t1' where t1_def: "combine x y t1' = t1" "(t1',e1) \<in> fset xs" using assms(3) by auto
  obtain t2' where t2_def: "combine x y t2' = t2" "(t2',e2) \<in> fset xs" using assms(4) by auto
  show ?thesis
  proof(cases "dlverts t1' \<inter> dlverts t2' = {}")
    case True
    then show ?thesis using assms(1) t1_def t2_def by blast
  next
    case False
    then show ?thesis using assms(2) t1_def t2_def by fast
  qed
qed

lemma wf_dlverts_child2:
  assumes "(t1,e) \<in> fset (child2 y (remove_child y xs) xs)"
      and "\<forall>(t,e) \<in> fset xs. wf_dlverts t"
    shows "wf_dlverts t1"
proof(cases "(t1,e) |\<in>| (remove_child y xs)")
  case True
  then show ?thesis using assms(2) by fastforce
next
  case False
  then obtain rs re where r_def: "(Node y rs, re) \<in> fset xs" "(t1,e)|\<in>| rs"
    using child2_in_child assms(1) by fast
  then show ?thesis using assms(2) by fastforce
qed

lemma wf_dlverts_child2_aux1:
  assumes "(t1,e1) \<in> fset (child2 y (remove_child y xs) xs)"
      and "\<exists>t. t \<in> fst ` fset xs \<and> root t = y"
      and "wf_dlverts (Node r xs)"
    shows "set (r@y) \<inter> dlverts t1 = {}"
proof(cases "(t1,e1) |\<in>| (remove_child y xs)")
  case True
  then have t1_def: "root t1 \<noteq> y" "(t1,e1) \<in> fset xs" by fastforce+
  obtain t et where t_def: "(t,et) \<in> fset xs" "root t = y" using assms(2) by force
  have "\<forall>y'\<in> set y. y' \<notin> dlverts t1"
  proof
    fix y'
    assume "y' \<in> set y"
    then have asm: "y' \<in> dlverts t" using t_def(2) dtree.set_sel(1) lverts_if_in_verts by fastforce
    have "dlverts t1 \<inter> dlverts t = {}" using assms(3) t1_def t_def by fastforce
    then show "y' \<notin> dlverts t1" using asm by blast
  qed
  then show ?thesis using assms(3) t1_def(2) by auto
next
  case False
  then obtain rs1 re1 where r_def: "(Node y rs1, re1) \<in> fset xs" "(t1,e1)|\<in>| rs1"
    using child2_in_child assms(1) by fast
  have "\<forall>y'\<in> set y. y' \<notin> dlverts t1" using assms(3) r_def by fastforce
  then show ?thesis using assms(3) r_def by fastforce
qed

lemma wf_dlverts_child2_aux2:
  assumes "\<forall>(t1,e1) \<in> fset xs. \<forall>(t2,e2) \<in> fset xs. dlverts t1 \<inter> dlverts t2 = {} \<or> (t1,e1)=(t2,e2)"
      and "\<forall>(t,e) \<in> fset xs. wf_dlverts t"
      and "(t1,e1) \<in> fset (child2 y (remove_child y xs) xs)"
      and "(t2,e2) \<in> fset (child2 y (remove_child y xs) xs)"
      and "(t1,e1)\<noteq>(t2,e2)"
    shows "dlverts t1 \<inter> dlverts t2 = {}"
proof(cases "(t1,e1) |\<in>| (remove_child y xs)")
  case t1_r: True
  then show ?thesis
  proof(cases "(t2,e2) |\<in>| (remove_child y xs)")
    case True
    then show ?thesis
      by (smt (verit, ccfv_threshold) t1_r assms(1,5) Int_iff case_prodD filter_fset)
  next
    case False
    then obtain rs2 re2 where r_def: "(Node y rs2, re2) \<in> fset xs" "(t2,e2)|\<in>| rs2"
      using child2_in_child assms(4) by fast
    then show ?thesis
      using t1_r assms(1) ffmember_filter inf_assoc inf_bot_right inf_commute
      by (smt (verit) dtree.sel(1) semilattice_inf_class.inf.absorb_iff2 case_prodD child_in_dlverts)
  qed
next
  case False
  then obtain rs1 re1 where r1_def: "(Node y rs1, re1) \<in> fset xs" "(t1,e1)|\<in>| rs1"
    using child2_in_child assms(3) by fast
  show ?thesis
  proof(cases "(t2,e2) |\<in>| (remove_child y xs)")
    case True
    then show ?thesis
      using r1_def assms(1) ffmember_filter inf_assoc inf_bot_right inf_commute
      by (smt (verit) dtree.sel(1) semilattice_inf_class.inf.absorb_iff2 case_prodD child_in_dlverts)
  next
    case False
    then obtain rs2 re2 where r2_def: "(Node y rs2, re2) \<in> fset xs" "(t2,e2) |\<in>| rs2"
      using child2_in_child assms(4) by fast
    then show ?thesis
    proof(cases "rs1=rs2")
      case True
      have "\<forall>(t1,e1) \<in> fset rs1. \<forall>(t2,e2) \<in> fset rs1.
                dlverts t1 \<inter> dlverts t2 = {} \<or> (t1,e1)=(t2,e2)"
        using r1_def(1) assms(2) by fastforce
      then show ?thesis
        using r1_def(2) r2_def(2) assms(5) True
        by (metis (mono_tags, lifting) case_prodD)
    next
      case False
      then have "dlverts (Node y rs1) \<inter> dlverts (Node y rs2) = {}"
        using assms(1) r1_def(1) r2_def(1) by fast
      then show ?thesis
        using r1_def(2) r2_def(2) child_in_dlverts
        by (metis order_bot_class.bot.extremum_uniqueI inf_mono)
    qed
  qed
qed

lemma wf_dlverts_combine: "wf_dlverts (combine x y t)"
using list_dtree_axioms proof(induction t)
  case ind: (Node r xs)
  then interpret list_dtree "Node r xs" using ind.prems by blast
  show ?case
  proof(cases "x=r \<and> (\<exists>t. t \<in> fst ` fset xs \<and> root t = y)")
    case True
    let ?xs = "child2 y (remove_child y xs) xs"
    have "\<forall>(t1,e1) \<in> fset xs. \<forall>(t2,e2) \<in> fset xs.
        dlverts t1 \<inter> dlverts t2 = {} \<or> (t1,e1)=(t2,e2)" using wf_lverts by fastforce
    moreover have "\<forall>(t1,e1) \<in> fset xs. wf_dlverts t1" using wf_lverts by fastforce
    ultimately have "\<forall>(t1,e1) \<in> fset ?xs. \<forall>(t2,e2) \<in> fset ?xs.
        dlverts t1 \<inter> dlverts t2 = {} \<or> (t1,e1)=(t2,e2)"
      using wf_dlverts_child2_aux2[of xs] by blast
    moreover have "\<forall>(x,e) \<in> fset ?xs. wf_dlverts x" using wf_dlverts_child2 wf_lverts by fastforce
    moreover have "(x@y) \<noteq> []" using True wf_lverts by simp
    moreover have "\<forall>(t1,e1) \<in> fset ?xs. set (x@y) \<inter> dlverts t1 = {}"
      using wf_dlverts_child2_aux1 wf_lverts True by fast
    ultimately have "wf_dlverts (Node (x@y) ?xs)" by fastforce
    moreover have "combine x y (Node r xs) = Node (x@y) ?xs" using True by simp
    ultimately show ?thesis by argo
  next
    case False
    let ?xs = "(\<lambda>(t,e). (combine x y t, e)) |`| xs"
    have 0: "\<forall>(t,e) \<in> fset xs. dlverts (combine x y t) = dlverts t"
      using list_dtree.dlverts_comb_id list_dtree_rec by fast
    have 1: "\<forall>(t,e) \<in> fset ?xs. wf_dlverts t" using ind.IH list_dtree_rec by auto
    have 2: "\<forall>(t,e) \<in> fset ?xs. set r \<inter> dlverts t = {}" using 0 wf_lverts by fastforce
    have "\<forall>(t1,e1) \<in> fset xs. \<forall>(t2,e2) \<in> fset xs.
        dlverts t1 \<inter> dlverts t2 = {} \<or> (t1,e1)=(t2,e2)" using wf_lverts by fastforce
    then have 3: "\<forall>(t1,e1) \<in> fset ?xs. \<forall>(t2,e2) \<in> fset ?xs.
        dlverts t1 \<inter> dlverts t2 = {} \<or> (t1,e1)=(t2,e2)"
      using 0 wf_dlverts_comb_aux[of xs] by blast
    have 4: "combine x y (Node r xs) = Node r ?xs" using False by auto
    have "r \<noteq> []" using wf_lverts by simp
    then show ?thesis using 1 2 3 4 by fastforce
  qed
qed

theorem list_dtree_comb: "list_dtree (combine x y t)"
  by(unfold_locales) (auto simp: wf_darcs_combine wf_dlverts_combine)

end

end