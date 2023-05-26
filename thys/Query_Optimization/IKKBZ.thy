(* Author: Bernhard Stöckl *)

theory IKKBZ
  imports Complex_Main "CostFunctions" "QueryGraph" "List_Dtree" "HOL-Library.Sorting_Algorithms"
begin

section \<open>IKKBZ\<close>

subsection \<open>Additional Proofs for Merging Lists\<close>

lemma merge_comm_if_not_equiv: "\<forall>x \<in> set xs. \<forall>y \<in> set ys. compare cmp x y \<noteq> Equiv \<Longrightarrow>
  Sorting_Algorithms.merge cmp xs ys = Sorting_Algorithms.merge cmp ys xs"
  apply(induction xs ys rule: Sorting_Algorithms.merge.induct)
  by(auto intro: compare.quasisym_not_greater simp: compare.asym_greater)

lemma set_merge: "set xs \<union> set ys = set (Sorting_Algorithms.merge cmp xs ys)"
  using mset_merge set_mset_mset set_mset_union by metis

lemma input_empty_if_merge_empty: "Sorting_Algorithms.merge cmp xs ys = [] \<Longrightarrow> xs = [] \<and> ys = []"
  using Un_empty set_empty2 set_merge by metis

lemma merge_assoc:
  "Sorting_Algorithms.merge cmp xs (Sorting_Algorithms.merge cmp ys zs)
  = Sorting_Algorithms.merge cmp (Sorting_Algorithms.merge cmp xs ys) zs"
  (is "?merge _ xs (?merge cmp _ zs) = _")
proof(induction xs "?merge cmp ys zs" arbitrary: ys zs taking: cmp rule: Sorting_Algorithms.merge.induct)
  case (2 cmp v vs)
  show ?case using input_empty_if_merge_empty[OF 2[symmetric]] by simp
next
  case ind: (3 x xs r rs)
  then show ?case
  proof(induction ys zs taking: cmp rule: Sorting_Algorithms.merge.induct)
    case (3 y ys z zs)
    then show ?case
      using ind compare.asym_greater
      by (smt (verit, best) compare.trans_not_greater list.inject merge.simps(3))
  qed (auto)
qed (simp)

lemma merge_comp_commute:
  assumes "\<forall>x \<in> set xs. \<forall>y \<in> set ys. compare cmp x y \<noteq> Equiv"
  shows "Sorting_Algorithms.merge cmp xs (Sorting_Algorithms.merge cmp ys zs)
        = Sorting_Algorithms.merge cmp ys (Sorting_Algorithms.merge cmp xs zs)"
  using assms merge_assoc merge_comm_if_not_equiv by metis

lemma wf_list_arcs_merge:
  "\<lbrakk>wf_list_arcs xs; wf_list_arcs ys; snd ` set xs \<inter> snd ` set ys = {}\<rbrakk>
    \<Longrightarrow> wf_list_arcs (Sorting_Algorithms.merge cmp xs ys)"
proof(induction xs ys taking: cmp rule: Sorting_Algorithms.merge.induct)
  case (3 x xs y ys)
  obtain v1 e1 where v1_def[simp]: "x = (v1,e1)" by force
  obtain v2 e2 where v2_def[simp]: "y = (v2,e2)" by force
  show ?case
  proof(cases "compare cmp x y = Greater")
    case True
    have "e2 \<notin> snd ` set (x#xs)" using "3.prems"(3) by auto
    moreover have "e2 \<notin> snd ` set ys" using "3.prems"(2) by simp
    ultimately have "e2 \<notin> snd ` set (Sorting_Algorithms.merge cmp (x#xs) ys)"
      using set_merge by fast
    then show ?thesis using True 3 by force
  next
    case False
    have "e1 \<notin> snd `set (y#ys)" using "3.prems"(3) by auto
    moreover have "e1 \<notin> snd ` set xs" using "3.prems"(1) by simp
    ultimately have "e1 \<notin> snd `set (Sorting_Algorithms.merge cmp xs (y#ys))"
      using set_merge by fast
    then show ?thesis using False 3 by force
  qed
qed (auto)

lemma wf_list_lverts_merge:
  "\<lbrakk>wf_list_lverts xs; wf_list_lverts ys;
    \<forall>v1 \<in> fst ` set xs. \<forall>v2 \<in> fst ` set ys. set v1 \<inter> set v2 = {}\<rbrakk>
    \<Longrightarrow> wf_list_lverts (Sorting_Algorithms.merge cmp xs ys)"
proof(induction xs ys taking: cmp rule: Sorting_Algorithms.merge.induct)
  case (3 x xs y ys)
  obtain v1 e1 where v1_def[simp]: "x = (v1,e1)" by force
  obtain v2 e2 where v2_def[simp]: "y = (v2,e2)" by force
  show ?case
  proof(cases "compare cmp x y = Greater")
    case True
    have "\<forall>v \<in> fst ` set (x#xs). set v2 \<inter> set v = {}" using "3.prems"(3) by auto
    moreover have "\<forall>v \<in> fst ` set ys. set v2 \<inter> set v = {}" using "3.prems"(2) by simp
    ultimately have "\<forall>v \<in> fst ` set (Sorting_Algorithms.merge cmp (x#xs) ys). set v2 \<inter> set v = {}"
      using set_merge[of "x#xs"] by blast
    then show ?thesis using True 3 by force
  next
    case False
    have "\<forall>v \<in> fst ` set (y#ys). set v1 \<inter> set v = {}" using "3.prems"(3) by auto
    moreover have "\<forall>v \<in> fst ` set xs. set v1 \<inter> set v = {}" using "3.prems"(1) by simp
    ultimately have "\<forall>v \<in> fst ` set (Sorting_Algorithms.merge cmp xs (y#ys)). set v1 \<inter> set v = {}"
      using set_merge[of xs] by auto
    then show ?thesis using False 3 by force
  qed
qed (auto)

lemma merge_hd_exists_preserv:
  "\<lbrakk>\<exists>(t1,e1) \<in> fset xs. hd as = (root t1,e1); \<exists>(t1,e1) \<in> fset xs. hd bs = (root t1,e1)\<rbrakk>
    \<Longrightarrow> \<exists>(t1,e1) \<in> fset xs. hd (Sorting_Algorithms.merge cmp as bs) = (root t1,e1)"
  by(induction as bs rule: Sorting_Algorithms.merge.induct) auto

lemma merge_split_supset:
  assumes "as@r#bs = (Sorting_Algorithms.merge cmp xs ys)"
    shows "\<exists>bs' as'. set bs' \<subseteq> set bs \<and> (as'@r#bs' = xs \<or> as'@r#bs' = ys)"
using assms proof(induction xs ys arbitrary: as taking: cmp rule: Sorting_Algorithms.merge.induct)
  case (3 x xs y ys)
  let ?merge = "Sorting_Algorithms.merge cmp"
  show ?case
  proof(cases "compare cmp x y = Greater")
    case True
    then show ?thesis
    proof(cases as)
      case Nil
      have "set ys \<subseteq> set (?merge (x#xs) ys)" using set_merge by fast
      then show ?thesis using Nil True "3.prems" by auto
    next
      case (Cons c cs)
      then have "cs@r#bs = ?merge (x#xs) ys" using True "3.prems" by simp
      then obtain as' bs' where as_def: "set bs' \<subseteq> set bs" "as'@r#bs' = x#xs \<or> as'@r#bs' = ys"
        using "3.IH"(1)[OF True] by blast
      have "as'@r#bs' = x#xs \<or> (y#as')@r#bs' = y#ys" using as_def(2) by simp
      then show ?thesis using as_def(1) by blast
    qed
  next
    case False
    then show ?thesis
    proof(cases as)
      case Nil
      have "set xs \<subseteq> set (?merge xs (y#ys))" using set_merge by fast
      then show ?thesis using Nil False "3.prems" by auto
    next
      case (Cons c cs)
      then have "cs@r#bs = ?merge xs (y#ys)" using False "3.prems" by simp
      then obtain as' bs' where as_def: "set bs' \<subseteq> set bs" "as'@r#bs' = xs \<or> as'@r#bs' = y#ys"
        using "3.IH"(2)[OF False] by blast
      have "(x#as')@r#bs' = x#xs \<or> as'@r#bs' = y#ys" using as_def(2) by simp
      then show ?thesis using as_def(1) by blast
    qed
  qed
qed(auto)

lemma merge_split_supset_fst:
  assumes "as@(r,e)#bs = (Sorting_Algorithms.merge cmp xs ys)"
  shows "\<exists>as' bs'. set bs' \<subseteq> set bs \<and> (as'@(r,e)#bs' = xs \<or> as'@(r,e)#bs' = ys)"
  using merge_split_supset[OF assms] by blast

lemma merge_split_supset':
  assumes "r \<in> set (Sorting_Algorithms.merge cmp xs ys)"
  shows "\<exists>as bs as' bs'. as@r#bs = (Sorting_Algorithms.merge cmp xs ys)
          \<and> set bs' \<subseteq> set bs \<and> (as'@r#bs' = xs \<or> as'@r#bs' = ys)"
  using merge_split_supset split_list[OF assms] by metis

lemma merge_split_supset_fst':
  assumes "r \<in> fst ` set (Sorting_Algorithms.merge cmp xs ys)"
  shows "\<exists>as e bs as' bs'. as@(r,e)#bs = (Sorting_Algorithms.merge cmp xs ys)
        \<and> set bs' \<subseteq> set bs \<and> (as'@(r,e)#bs' = xs \<or> as'@(r,e)#bs' = ys)"
proof -
  obtain e where "(r,e) \<in> set (Sorting_Algorithms.merge cmp xs ys)" using assms by auto
  then show ?thesis using merge_split_supset'[of "(r,e)"] by blast
qed

lemma merge_split_supset_subtree:
  assumes "\<forall>as bs. as@(r,e)#bs = xs \<longrightarrow>
            (\<exists>zs. is_subtree (Node r zs) t \<and> dverts (Node r zs) \<subseteq> fst ` set ((r,e)#bs))"
      and "\<forall>as bs. as@(r,e)#bs = ys \<longrightarrow>
            (\<exists>zs. is_subtree (Node r zs) t \<and> dverts (Node r zs) \<subseteq> fst ` set ((r,e)#bs))"
      and "as@(r,e)#bs = (Sorting_Algorithms.merge cmp xs ys)"
    shows "\<exists>zs. is_subtree (Node r zs) t \<and> dverts (Node r zs) \<subseteq> (fst ` set ((r,e)#bs))"
proof -
  obtain as' bs' where bs'_def: "set bs' \<subseteq> set bs" "as'@(r,e)#bs' = xs \<or> as'@(r,e)#bs' = ys"
    using merge_split_supset[OF assms(3)] by blast
  obtain zs where zs_def: "is_subtree (Node r zs) t" "dverts (Node r zs) \<subseteq> fst ` set ((r,e)#bs')"
    using assms(1,2) bs'_def(2) by blast
  then have "dverts (Node r zs) \<subseteq> fst ` set ((r,e)#bs)" using bs'_def(1) by auto
  then show ?thesis using zs_def(1) by blast
qed

lemma merge_split_supset_strict_subtree:
  assumes "\<forall>as bs. as@(r,e)#bs = xs \<longrightarrow> (\<exists>zs. strict_subtree (Node r zs) t
            \<and> dverts (Node r zs) \<subseteq> fst ` set ((r,e)#bs))"
      and "\<forall>as bs. as@(r,e)#bs = ys \<longrightarrow> (\<exists>zs. strict_subtree (Node r zs) t
            \<and> dverts (Node r zs) \<subseteq> fst ` set ((r,e)#bs))"
      and "as@(r,e)#bs = (Sorting_Algorithms.merge cmp xs ys)"
    shows "\<exists>zs. strict_subtree (Node r zs) t
            \<and> dverts (Node r zs) \<subseteq> (fst ` set ((r,e)#bs))"
proof -
  obtain as' bs' where bs'_def: "set bs' \<subseteq> set bs" "as'@(r,e)#bs' = xs \<or> as'@(r,e)#bs' = ys"
    using merge_split_supset[OF assms(3)] by blast
  obtain zs where zs_def:
      "strict_subtree (Node r zs) t" "dverts (Node r zs) \<subseteq> fst ` set ((r,e)#bs')"
    using assms(1,2) bs'_def(2) by blast
  then have "dverts (Node r zs) \<subseteq> fst ` set ((r,e)#bs)" using bs'_def(1) by auto
  then show ?thesis using zs_def(1,2) by blast
qed

lemma sorted_app_l: "sorted cmp (xs@ys) \<Longrightarrow> sorted cmp xs"
  by(induction xs rule: sorted.induct) auto

lemma sorted_app_r: "sorted cmp (xs@ys) \<Longrightarrow> sorted cmp ys"
  by(induction xs) (auto simp: sorted_Cons_imp_sorted)

subsection \<open>Merging Subtrees of Ranked Dtrees\<close>

locale ranked_dtree = list_dtree t for t :: "('a list,'b) dtree" +
  fixes rank :: "'a list \<Rightarrow> real"
  fixes cmp :: "('a list\<times>'b) comparator"
  assumes cmp_antisym:
    "\<lbrakk>v1 \<noteq> []; v2 \<noteq> []; compare cmp (v1,e1) (v2,e2) = Equiv\<rbrakk> \<Longrightarrow> set v1 \<inter> set v2 \<noteq> {} \<or> e1=e2"
begin

lemma ranked_dtree_rec: "\<lbrakk>Node r xs = t; (x,e) \<in> fset xs\<rbrakk> \<Longrightarrow> ranked_dtree x cmp"
  using wf_arcs wf_lverts by(unfold_locales) (auto dest: cmp_antisym)

lemma ranked_dtree_rec_suc: "(x,e) \<in> fset (sucs t) \<Longrightarrow> ranked_dtree x cmp"
  using ranked_dtree_rec[of "root t"] by force

lemma ranked_dtree_subtree: "is_subtree x t \<Longrightarrow> ranked_dtree x cmp"
using ranked_dtree_axioms proof(induction t)
  case (Node r xs)
  then interpret ranked_dtree "Node r xs" by blast
  show ?case using Node ranked_dtree_rec by (cases "x = Node r xs") auto
qed

subsubsection \<open>Definitions\<close>

lift_definition cmp' :: "('a list\<times>'b) comparator" is
  "(\<lambda>x y. if rank (rev (fst x)) < rank (rev (fst y)) then Less
    else if rank (rev (fst x)) > rank (rev (fst y)) then Greater
    else compare cmp x y)"
  by (smt (z3) comp.distinct(3) compare.less_iff_sym_greater compare.refl compare.trans_equiv
      compare.trans_less comparator_def)

abbreviation disjoint_sets :: "(('a list, 'b) dtree \<times> 'b) fset \<Rightarrow> bool" where
  "disjoint_sets xs \<equiv> disjoint_darcs xs \<and> disjoint_dlverts xs \<and> (\<forall>(t,e) \<in> fset xs. [] \<notin> dverts t)"

abbreviation merge_f :: "'a list \<Rightarrow> (('a list, 'b) dtree \<times> 'b) fset
        \<Rightarrow> ('a list, 'b) dtree \<times> 'b \<Rightarrow> ('a list \<times> 'b) list \<Rightarrow> ('a list \<times> 'b) list" where
  "merge_f r xs \<equiv> \<lambda>(t,e) b. if (t,e) \<in> fset xs \<and> list_dtree (Node r xs)
        \<and> (\<forall>(v,e') \<in> set b. set v \<inter> dlverts t = {} \<and> v \<noteq> [] \<and> e' \<notin> darcs t \<union> {e})
      then Sorting_Algorithms.merge cmp' (dtree_to_list (Node r {|(t,e)|})) b else b"

definition merge :: "('a list,'b) dtree \<Rightarrow> ('a list,'b) dtree" where
  "merge t1 \<equiv> dtree_from_list (root t1) (ffold (merge_f (root t1) (sucs t1)) [] (sucs t1))"

subsubsection \<open>Commutativity Proofs\<close>

lemma cmp_sets_not_dsjnt_if_equiv:
  "\<lbrakk>v1 \<noteq> []; v2 \<noteq> []\<rbrakk> \<Longrightarrow> compare cmp' (v1,e1) (v2,e2) = Equiv \<Longrightarrow> set v1 \<inter> set v2 \<noteq> {} \<or> e1=e2"
  by(auto simp: cmp'.rep_eq dest: cmp_antisym split: if_splits)

lemma dtree_to_list_x_in_dverts:
  "x \<in> fst ` set (dtree_to_list (Node r {|(t1,e1)|})) \<Longrightarrow> x \<in> dverts t1"
  using dtree_to_list_sub_dverts_ins by auto

lemma dtree_to_list_x_in_dlverts:
  "x \<in> fst ` set (dtree_to_list (Node r {|(t1,e1)|})) \<Longrightarrow> set x \<subseteq> dlverts t1"
  using dtree_to_list_x_in_dverts lverts_if_in_verts by fast

lemma dtree_to_list_x1_disjoint:
  "dlverts t1 \<inter> dlverts t2 = {}
    \<Longrightarrow> \<forall>x1 \<in> fst ` set (dtree_to_list (Node r {|(t1,e1)|})). set x1 \<inter> dlverts t2 = {}"
  using dtree_to_list_x_in_dlverts by fast

lemma dtree_to_list_xs_disjoint:
  "dlverts t1 \<inter> dlverts t2 = {}
    \<Longrightarrow> \<forall>x1 \<in> fst ` set (dtree_to_list (Node r {|(t1,e1)|})).
          \<forall>x2 \<in> fst ` set (dtree_to_list (Node r' {|(t2,e2)|})). set x1 \<inter> set x2 = {}"
  using dtree_to_list_x_in_dlverts by (metis inf_mono subset_empty)

lemma dtree_to_list_e_in_darcs:
  "e \<in> snd ` set (dtree_to_list (Node r {|(t1,e1)|})) \<Longrightarrow> e \<in> darcs t1 \<union> {e1}"
  using dtree_to_list_sub_darcs by fastforce

lemma dtree_to_list_e_disjoint:
  "(darcs t1 \<union> {e1}) \<inter> (darcs t2 \<union> {e2}) = {}
    \<Longrightarrow> \<forall>e \<in> snd ` set (dtree_to_list (Node r {|(t1,e1)|})). e \<notin> darcs t2 \<union> {e2}"
  using dtree_to_list_e_in_darcs by fast

lemma dtree_to_list_es_disjoint:
  "(darcs t1 \<union> {e1}) \<inter> (darcs t2 \<union> {e2}) = {}
    \<Longrightarrow> \<forall>e3 \<in> snd ` set (dtree_to_list (Node r {|(t1,e1)|})).
          \<forall>e4 \<in> snd ` set (dtree_to_list (Node r' {|(t2,e2)|})). e3 \<noteq> e4"
  using dtree_to_list_e_disjoint dtree_to_list_e_in_darcs by fast

lemma dtree_to_list_xs_not_equiv:
  assumes "dlverts t1 \<inter> dlverts t2 = {}"
      and "(darcs t1 \<union> {e3}) \<inter> (darcs t2 \<union> {e4}) = {}"
      and "(x1,e1) \<in> set (dtree_to_list (Node r {|(t1,e3)|}))" and "x1 \<noteq> []"
      and "(x2,e2) \<in> set (dtree_to_list (Node r' {|(t2,e4)|}))" and "x2 \<noteq> []"
    shows "compare cmp' (x1,e1) (x2,e2) \<noteq> Equiv"
  using dtree_to_list_xs_disjoint[OF assms(1)] cmp_sets_not_dsjnt_if_equiv[of x1 x2 e1 e2]
    dtree_to_list_es_disjoint[OF assms(2)] assms(3-6) by fastforce

lemma merge_dtree1_not_equiv:
  assumes "dlverts t1 \<inter> dlverts t2 = {}"
      and "(darcs t1 \<union> {e1}) \<inter> (darcs t2 \<union> {e2}) = {}"
      and "[] \<notin> dverts t1"
      and "[] \<notin> dverts t2"
      and "xs = dtree_to_list (Node r {|(t1,e1)|})"
      and "ys = dtree_to_list (Node r' {|(t2,e2)|})"
    shows "\<forall>(x1,e1)\<in>set xs. \<forall>(x2,e2)\<in>set ys. compare cmp' (x1,e1) (x2,e2) \<noteq> Equiv"
proof -
  have "\<forall>(x1,e1)\<in>set xs. x1 \<noteq> []"
    using assms(3,5) dtree_to_list_x_in_dverts
    by (smt (verit) case_prod_conv case_prod_eta fst_conv pair_imageI surj_pair)
  moreover have "\<forall>(x1,e1)\<in>set ys. x1 \<noteq> []"
    using assms(4,6) dtree_to_list_x_in_dverts
    by (smt (verit) case_prod_conv case_prod_eta fst_conv pair_imageI surj_pair)
  ultimately show ?thesis using dtree_to_list_xs_not_equiv[of t1 t2] assms(1,2,5,6) by fast
qed

lemma merge_commute_aux1:
  assumes "dlverts t1 \<inter> dlverts t2 = {}"
      and "(darcs t1 \<union> {e1}) \<inter> (darcs t2 \<union> {e2}) = {}"
      and "[] \<notin> dverts t1"
      and "[] \<notin> dverts t2"
      and "xs = dtree_to_list (Node r {|(t1,e1)|})"
      and "ys = dtree_to_list (Node r' {|(t2,e2)|})"
    shows "Sorting_Algorithms.merge cmp' xs ys = Sorting_Algorithms.merge cmp' ys xs"
  using merge_dtree1_not_equiv merge_comm_if_not_equiv assms by fast

lemma dtree_to_list_x1_list_disjoint:
  "set x2 \<inter> dlverts t1 = {}
    \<Longrightarrow> \<forall>x1 \<in> fst ` set (dtree_to_list (Node r {|(t1,e1)|})). set x1 \<inter> set x2 = {}"
  using dtree_to_list_x_in_dlverts by fast

lemma dtree_to_list_e1_list_disjoint':
  "set x2 \<inter> darcs t1 \<union> {e1} = {}
    \<Longrightarrow> \<forall>x1 \<in> snd ` set (dtree_to_list (Node r {|(t1,e1)|})). x1 \<notin> set x2"
  using dtree_to_list_e_in_darcs by blast

lemma dtree_to_list_e1_list_disjoint:
  "e2 \<notin> darcs t1 \<union> {e1}
    \<Longrightarrow> \<forall>x1 \<in> snd ` set (dtree_to_list (Node r {|(t1,e1)|})). x1 \<noteq> e2"
  using dtree_to_list_e_in_darcs by fast

lemma dtree_to_list_xs_list_not_equiv:
  assumes "(x1,e1) \<in> set (dtree_to_list (Node r {|(t1,e3)|}))"
      and "x1 \<noteq> []"
      and "\<forall>(v,e) \<in> set ys. set v \<inter> dlverts t1 = {} \<and> v \<noteq> [] \<and> e \<notin> darcs t1 \<union> {e3}"
      and "(x2,e2) \<in> set ys"
    shows "compare cmp' (x1,e1) (x2,e2) \<noteq> Equiv"
proof -
  have "set x1 \<inter> set x2 = {}" using dtree_to_list_x1_list_disjoint assms(1,3,4) by fastforce
  moreover have "e1 \<noteq> e2" using dtree_to_list_e1_list_disjoint assms(1,3,4) by fastforce
  ultimately show ?thesis using cmp_sets_not_dsjnt_if_equiv assms(2-4) by auto
qed

lemma merge_commute_aux2:
  assumes "[] \<notin> dverts t1"
      and "xs = dtree_to_list (Node r {|(t1,e1)|})"
      and "\<forall>(v,e) \<in> set ys. set v \<inter> dlverts t1 = {} \<and> v\<noteq>[] \<and> e \<notin> darcs t1 \<union> {e1}"
    shows "Sorting_Algorithms.merge cmp' xs ys = Sorting_Algorithms.merge cmp' ys xs"
proof -
  have "\<forall>(x1,e1)\<in>set xs. x1 \<noteq> []"
    using assms(1,2) dtree_to_list_x_in_dverts
    by (smt (verit) case_prod_conv case_prod_eta fst_conv pair_imageI surj_pair)
  then have "\<forall>(x1,e1)\<in>set xs. \<forall>(x2,e2)\<in>set ys. compare cmp' (x1,e1) (x2,e2) \<noteq> Equiv"
    using assms(2,3) dtree_to_list_xs_list_not_equiv by force
  then show ?thesis using merge_comm_if_not_equiv by fast
qed

lemma merge_inter_preserv':
  assumes "f = (merge_f r xs)"
      and "\<not>(\<forall>(v,_) \<in> set z. set v \<inter> dlverts t1 = {})"
    shows "\<not>(\<forall>(v,_) \<in> set (f (t2,e2) z). set v \<inter> dlverts t1 = {})"
proof(cases "f (t2,e2) z = z")
  case False
  then have "f (t2,e2) z = Sorting_Algorithms.merge cmp' (dtree_to_list (Node r {|(t2,e2)|})) z"
    by(simp add: assms(1)) meson
  then show ?thesis using assms(2) set_merge by force
qed (simp add: assms(2))

lemma merge_inter_preserv:
  assumes "f = (merge_f r xs)"
      and "\<not>(\<forall>(v,e) \<in> set z. set v \<inter> dlverts t1 = {} \<and> e \<notin> darcs t1 \<union> {e1})"
    shows "\<not>(\<forall>(v,e) \<in> set (f (t2,e2) z). set v \<inter> dlverts t1 = {} \<and> e \<notin> darcs t1 \<union> {e1})"
proof(cases "f (t2,e2) z = z")
  case True
  then show ?thesis using assms(2) by simp
next
  case False
  then have "f (t2,e2) z = Sorting_Algorithms.merge cmp' (dtree_to_list (Node r {|(t2,e2)|})) z"
    by(simp add: assms(1)) meson
  then show ?thesis
    using assms(2) set_merge[of "dtree_to_list (Node r {|(t2,e2)|})"] by simp blast
qed

lemma merge_f_eq_z_if_inter':
  "\<not>(\<forall>(v,_) \<in> set z. set v \<inter> dlverts t1 = {}) \<Longrightarrow> (merge_f r xs) (t1,e1) z = z"
  by auto

lemma merge_f_eq_z_if_inter:
  "\<not>(\<forall>(v,e) \<in> set z. set v \<inter> dlverts t1 = {} \<and> e \<notin> darcs t1 \<union> {e1})
    \<Longrightarrow> (merge_f r xs) (t1,e1) z = z"
  by auto

lemma merge_empty_inter_preserv_aux:
  assumes "f = (merge_f r xs)"
      and "(t2,e2) \<in> fset xs"
      and "\<forall>(v,e) \<in> set z. set v \<inter> dlverts t2 = {} \<and> v\<noteq>[] \<and> e \<notin> darcs t2 \<union> {e2}"
      and "list_dtree (Node r xs)"
      and "(t1,e1) \<in> fset xs"
      and "(t1,e1) \<noteq> (t2,e2)"
      and "\<forall>(v,e) \<in> set z. set v \<inter> dlverts t1 = {} \<and> v\<noteq>[] \<and> e \<notin> darcs t1 \<union> {e1}"
    shows "\<forall>(v,e) \<in> set (f (t2,e2) z). set v \<inter> dlverts t1 = {} \<and> v\<noteq>[] \<and> e \<notin> darcs t1 \<union> {e1}"
proof -
  have 0: "f (t2,e2) z = Sorting_Algorithms.merge cmp' (dtree_to_list (Node r {|(t2,e2)|})) z"
    using assms(1-6) by simp
  let ?ys = "dtree_to_list (Node r {|(t2,e2)|})"
  interpret list_dtree "Node r xs" using assms(4) .
  have "disjoint_dlverts xs" using wf_lverts by simp
  then have "\<forall>v\<in>fst ` set ?ys. set v \<inter> dlverts t1 = {}"
    using dtree_to_list_x1_disjoint assms(2,5,6) by fast
  then have 1: "\<forall>v\<in>fst ` set (Sorting_Algorithms.merge cmp' ?ys z). set v \<inter> dlverts t1 = {}"
    using assms(7) set_merge[of ?ys] by fastforce
  have "disjoint_darcs xs" using disjoint_darcs_if_wf_xs[OF wf_arcs] .
  then have 2: "(darcs t2 \<union> {e2}) \<inter> (darcs t1 \<union> {e1}) = {}" using assms(2,5,6) by fast
  have "\<forall>e\<in>snd ` set ?ys. e \<notin> darcs t1 \<union> {e1}" using dtree_to_list_e_disjoint[OF 2] by blast
  then have 2: "\<forall>e\<in>snd ` set (Sorting_Algorithms.merge cmp' ?ys z). e \<notin> darcs t1 \<union> {e1}"
    using assms(7) set_merge[of ?ys] by fastforce
  have "[] \<notin> dverts t2" using assms(2) empty_notin_wf_dlverts wf_lverts by fastforce
  then have "\<forall>v\<in>fst ` set ?ys. v \<noteq> []" by (metis dtree_to_list_x_in_dverts)
  then have "\<forall>v\<in>fst ` set (Sorting_Algorithms.merge cmp' ?ys z). v \<noteq> []"
    using assms(7) set_merge[of ?ys] by fastforce
  then show ?thesis using 0 1 2 by fastforce
qed

lemma merge_empty_inter_preserv:
  assumes "f = (merge_f r xs)"
      and "\<forall>(v,e) \<in> set z. set v \<inter> dlverts t1 = {} \<and> v\<noteq>[] \<and> e \<notin> darcs t1 \<union> {e1}"
      and "(t1,e1) \<in> fset xs"
      and "(t1,e1) \<noteq> (t2,e2)"
    shows "\<forall>(v,e) \<in> set (f (t2,e2) z). set v \<inter> dlverts t1 = {} \<and> v\<noteq>[] \<and> e \<notin> darcs t1 \<union> {e1}"
proof(cases "f (t2,e2) z = z")
  case True
  then show ?thesis using assms(2) by simp
next
  case False
  have "(t2,e2) \<in> fset xs" using False assms(1) by simp argo
  moreover have "list_dtree (Node r xs)" using False assms(1) by simp argo
  moreover have "\<forall>(v,e) \<in> set z. set v \<inter> dlverts t2 = {} \<and> v\<noteq>[] \<and> e \<notin> darcs t2 \<union> {e2}"
    using False assms(1) by simp argo
  ultimately show ?thesis using merge_empty_inter_preserv_aux assms by presburger
qed

lemma merge_commute_aux3:
  assumes "f = (merge_f r xs)"
      and "list_dtree (Node r xs)"
      and "(t1,e1) \<noteq> (t2,e2)"
      and "(\<forall>(v,e) \<in> set z. set v \<inter> dlverts t1 = {} \<and> v \<noteq> [] \<and> e \<notin> darcs t1 \<union> {e1})"
      and "(\<forall>(v,e) \<in> set z. set v \<inter> dlverts t2 = {} \<and> v \<noteq> [] \<and> e \<notin> darcs t2 \<union> {e2})"
      and "(t1,e1) \<in> fset xs"
      and "(t2,e2) \<in> fset xs"
    shows "(f (t2, e2) \<circ> f (t1, e1)) z = (f (t1, e1) \<circ> f (t2, e2)) z"
proof -
  let ?merge = "Sorting_Algorithms.merge"
  let ?xs = "dtree_to_list (Node r {|(t1, e1)|})"
  let ?ys = "dtree_to_list (Node r {|(t2, e2)|})"
  interpret list_dtree "Node r xs" using assms(2) .
  have disj: "dlverts t1 \<inter> dlverts t2 = {}" "[] \<notin> dverts t1" "[] \<notin> dverts t2"
    using assms(3,6,7) disjoint_dlverts_if_wf[OF wf_lverts] empty_notin_wf_dlverts[OF wf_lverts]
    by fastforce+
  have disj2: "(darcs t1 \<union> {e1}) \<inter> (darcs t2 \<union> {e2}) = {}"
    using assms(2,3,6,7) disjoint_darcs_if_wf_aux5[OF wf_arcs] by blast
  have "f (t2, e2) z = Sorting_Algorithms.merge cmp' ?ys z" using assms(1,2,5,7) by simp
  moreover have "\<forall>(v,e)\<in>set (f (t2,e2) z). set v \<inter> dlverts t1 = {} \<and> v \<noteq> [] \<and> e \<notin> darcs t1 \<union> {e1}"
    using merge_empty_inter_preserv[OF assms(1)] assms(3,4,6) by simp
  ultimately have 2: "(f (t1, e1) \<circ> f (t2, e2)) z = ?merge cmp' ?xs (?merge cmp' ?ys z)"
    using assms(1-2,6) by auto
  have "f (t1, e1) z = Sorting_Algorithms.merge cmp' ?xs z" using assms(1-2,4,6) by simp
  moreover have "\<forall>(v,e)\<in>set (f (t1, e1) z). set v \<inter> dlverts t2 = {} \<and> v\<noteq>[] \<and> e \<notin> darcs t2 \<union> {e2}"
    using merge_empty_inter_preserv[OF assms(1)] assms(3,5,7) by presburger
  ultimately have 3: "(f (t2, e2) \<circ> f (t1,e1)) z = ?merge cmp' ?ys (?merge cmp' ?xs z)"
    using assms(1-2,7) by simp
  have "\<forall>x\<in>set ?xs. \<forall>y\<in>set ?ys. compare cmp' x y \<noteq> Equiv"
    using merge_dtree1_not_equiv[OF disj(1) disj2] disj(2,3) by fast
  then have "?merge cmp' ?xs (?merge cmp' ?ys z) = ?merge cmp' ?ys (?merge cmp' ?xs z)"
    using merge_comp_commute by blast
  then show ?thesis using 2 3 by simp
qed

lemma merge_commute_aux:
  assumes "f = (merge_f r xs)"
  shows "(f y \<circ> f x) z = (f x \<circ> f y) z"
proof -
  obtain t1 e1 where y_def[simp]: "x = (t1, e1)" by fastforce
  obtain t2 e2 where x_def[simp]: "y = (t2, e2)" by fastforce
  show ?thesis
  proof(cases "(t1,e1) \<in> fset xs \<and> (t2,e2) \<in> fset xs")
    case True
    then consider "list_dtree (Node r xs)" "(t1,e1) \<noteq> (t2,e2)"
        "(\<forall>(v,e) \<in> set z. set v \<inter> dlverts t1 = {} \<and> v \<noteq> [] \<and> e \<notin> darcs t1 \<union> {e1})"
        "(\<forall>(v,e) \<in> set z. set v \<inter> dlverts t2 = {} \<and> v \<noteq> [] \<and> e \<notin> darcs t2 \<union> {e2})"
      | "(t1,e1) = (t2,e2)"
      | "\<not>list_dtree (Node r xs)"
      | "\<not>(\<forall>(v,e) \<in> set z. set v \<inter> dlverts t1 = {} \<and> e \<notin> darcs t1 \<union> {e1})"
      | "\<not>(\<forall>(v,e) \<in> set z. set v \<inter> dlverts t2 = {} \<and> e \<notin> darcs t2 \<union> {e2})"
      | "\<not>(\<forall>(v,_) \<in> set z. v \<noteq> [])"
      by fast
    then show ?thesis
    proof(cases)
      case 1
      then show ?thesis using merge_commute_aux3[OF assms] True by simp
    next
      case 4
      then have "f x z = z" by(auto simp: assms)
      then have 0: "(f y \<circ> f x) z = f y z" by simp
      have "\<not>(\<forall>(v,e) \<in> set (f y z). set v \<inter> dlverts t1 = {} \<and> e \<notin> darcs t1 \<union> {e1})"
        using merge_inter_preserv[OF assms 4] by simp
      then have "(f x \<circ> f y) z = f y z" using assms merge_f_eq_z_if_inter by auto
      then show ?thesis using 0 by simp
    next
      case 5
      then have "f y z = z" by(auto simp: assms)
      then have 0: "(f x \<circ> f y) z = f x z" by simp
      have "\<not>(\<forall>(v,e) \<in> set (f x z). set v \<inter> dlverts t2 = {} \<and> e \<notin> darcs t2 \<union> {e2})"
        using merge_inter_preserv[OF assms 5] by simp
      then have "(f y \<circ> f x) z = f x z" using assms merge_f_eq_z_if_inter by simp
      then show ?thesis using 0 by simp
    next
      case 6
      then have "(f x \<circ> f y) z = z" by(auto simp: assms)
      also have "z = (f y \<circ> f x) z" using 6 by(auto simp: assms)
      finally show ?thesis by simp
    qed(auto simp: assms)
  next
    case False
    then have "(\<forall>z. f x z = z) \<or> (\<forall>z. f y z = z)" by(auto simp: assms)
    then show ?thesis by force
  qed
qed

lemma merge_commute: "comp_fun_commute (merge_f r xs)"
  using comp_fun_commute_def merge_commute_aux by blast

interpretation Comm: comp_fun_commute "merge_f r xs" by (rule merge_commute)

subsubsection \<open>Merging Preserves Arcs and Verts\<close>

lemma empty_list_valid_merge:
  "(\<forall>(v,e) \<in> set []. set v \<inter> dlverts t1 = {} \<and> v \<noteq> [] \<and> e \<notin> darcs t1 \<union> {e1})"
  by simp

lemma disjoint_sets_sucs: "disjoint_sets (sucs t)"
  using empty_notin_wf_dlverts list_dtree.wf_lverts list_dtree_rec dtree.collapse
    disjoint_dlverts_if_wf[OF wf_lverts] disjoint_darcs_if_wf[OF wf_arcs] by blast

lemma empty_not_elem_subset:
  "\<lbrakk>xs |\<subseteq>| ys; \<forall>(t,e) \<in> fset ys. [] \<notin> dverts t\<rbrakk> \<Longrightarrow> \<forall>(t,e) \<in> fset xs. [] \<notin> dverts t"
  by (meson less_eq_fset.rep_eq subset_iff)

lemma disjoint_sets_subset:
  assumes "xs |\<subseteq>| ys" and "disjoint_sets ys"
  shows " disjoint_sets xs"
  using disjoint_darcs_subset[OF assms(1)] disjoint_dlverts_subset[OF assms(1)]
    empty_not_elem_subset[OF assms(1)] assms by fast

lemma merge_mdeg_le_1: "max_deg (merge t1) \<le> 1"
  unfolding merge_def by (rule dtree_from_list_deg_le_1)

lemma merge_mdeg_le1_sub: "is_subtree t1 (merge t2) \<Longrightarrow> max_deg t1 \<le> 1"
  using merge_mdeg_le_1 le_trans mdeg_ge_sub by fast

lemma merge_fcard_le1: "fcard (sucs (merge t1)) \<le> 1"
  unfolding merge_def by (rule dtree_from_list_fcard_le1)

lemma merge_fcard_le1_sub: "is_subtree t1 (merge t2) \<Longrightarrow> fcard (sucs t1) \<le> 1"
  using merge_mdeg_le1_sub mdeg_ge_fcard[of "sucs t1" "root t1"] by force

lemma merge_f_alt:
  assumes "P = (\<lambda>xs. list_dtree (Node r xs))"
      and "Q = (\<lambda>(t,e) b. (\<forall>(v,e') \<in> set b. set v \<inter> dlverts t = {} \<and> v\<noteq>[] \<and> e' \<notin> darcs t \<union> {e}))"
      and "R = (\<lambda>(t,e) b. Sorting_Algorithms.merge cmp' (dtree_to_list (Node r {|(t,e)|})) b)"
    shows "merge_f r xs = (\<lambda>a b. if a \<notin> fset xs \<or> \<not> Q a b \<or> \<not> P xs then b else R a b)"
  using assms by force

lemma merge_f_alt_commute:
  assumes "P = (\<lambda>xs. list_dtree (Node r xs))"
      and "Q = (\<lambda>(t,e) b. (\<forall>(v,e') \<in> set b. set v \<inter> dlverts t = {} \<and> v \<noteq> [] \<and> e' \<notin> darcs t \<union> {e}))"
      and "R = (\<lambda>(t,e) b. Sorting_Algorithms.merge cmp' (dtree_to_list (Node r {|(t,e)|})) b)"
    shows "comp_fun_commute (\<lambda>a b. if a \<notin> fset xs \<or> \<not> Q a b \<or> \<not> P xs then b else R a b)"
proof -
  have "comp_fun_commute (merge_f r xs)" using merge_commute by fast
  then show ?thesis using merge_f_alt[OF assms] by simp
qed

lemma merge_ffold_supset:
  assumes "xs |\<subseteq>| ys" and "list_dtree (Node r ys)"
  shows "ffold (merge_f r ys) acc xs = ffold (merge_f r xs) acc xs"
proof -
  let ?P = "\<lambda>xs. list_dtree (Node r xs)"
  let ?Q = "\<lambda>(t,e) b. (\<forall>(v,e') \<in> set b. set v \<inter> dlverts t = {} \<and> v \<noteq> [] \<and> e' \<notin> darcs t \<union> {e})"
  let ?R = "\<lambda>(t,e) b. Sorting_Algorithms.merge cmp' (dtree_to_list (Node r {|(t,e)|})) b"
  have 0: "\<And>xs. comp_fun_commute (\<lambda>a b. if a \<notin> fset xs \<or> \<not> ?Q a b \<or> \<not> ?P xs then b else ?R a b)"
    using merge_f_alt_commute by blast
  have "ffold (\<lambda>a b. if a \<notin> fset ys \<or> \<not> ?Q a b \<or> \<not> ?P ys then b else ?R a b) acc xs
      = ffold (\<lambda>a b. if a \<notin> fset xs \<or> \<not> ?Q a b \<or> \<not> ?P xs then b else ?R a b) acc xs"
    using ffold_commute_supset[OF assms(1), of ?P ?Q ?R, OF assms(2) list_dtree_subset 0] by auto
  then show ?thesis using merge_f_alt by presburger
qed

lemma merge_f_merge_if_not_snd:
  "merge_f r xs (t1,e1) z \<noteq> z \<Longrightarrow>
  merge_f r xs (t1,e1) z = Sorting_Algorithms.merge cmp' (dtree_to_list (Node r {|(t1,e1)|})) z"
  by(simp) meson

lemma merge_f_merge_if_conds:
  "\<lbrakk>list_dtree (Node r xs); \<forall>(v,e) \<in> set z. set v \<inter> dlverts t1 = {} \<and> v\<noteq>[] \<and> e \<notin> darcs t1 \<union> {e1};
     (t1,e1) \<in> fset xs\<rbrakk>
  \<Longrightarrow> merge_f r xs (t1,e1) z = Sorting_Algorithms.merge cmp' (dtree_to_list (Node r {|(t1,e1)|})) z"
  by force

lemma merge_f_merge_if_conds_empty:
  "\<lbrakk>list_dtree (Node r xs); (t1,e1) \<in> fset xs\<rbrakk>
  \<Longrightarrow> merge_f r xs (t1,e1) []
      = Sorting_Algorithms.merge cmp' (dtree_to_list (Node r {|(t1,e1)|})) []"
  using merge_f_merge_if_conds by simp

lemma merge_ffold_empty_inter_preserv:
  "\<lbrakk>list_dtree (Node r ys); xs |\<subseteq>| ys;
    \<forall>(v,e) \<in> set z. set v \<inter> dlverts t1 = {} \<and> v\<noteq>[] \<and> e \<notin> darcs t1 \<union> {e1};
    (t1,e1) \<in> fset ys; (t1,e1) \<notin> fset xs; (v,e) \<in> set (ffold (merge_f r xs) z xs)\<rbrakk>
      \<Longrightarrow> set v \<inter> dlverts t1 = {} \<and> v \<noteq> [] \<and> e \<notin> darcs t1 \<union> {e1}"
proof(induction xs)
  case (insert x xs)
  let ?f = "merge_f r (finsert x xs)"
  let ?f' = "merge_f r xs"
  let ?merge = "Sorting_Algorithms.merge"
  interpret list_dtree "Node r ys" using insert.prems(1) .
  have 0: "list_dtree (Node r (finsert x xs))" using list_dtree_subset insert.prems(1,2) by blast
  show ?case
  proof(cases "ffold ?f z (finsert x xs) = ffold ?f' z xs")
    case True
    then have "(v,e) \<in> set (ffold ?f' z xs)" using insert.prems(6) by argo
    then show ?thesis using insert.IH insert.prems by force
  next
    case not_right: False
    obtain t2 e2 where t2_def[simp]: "x = (t2,e2)" by fastforce
    show ?thesis
    proof(cases "(v,e) \<in> set (dtree_to_list (Node r {|(t2,e2)|}))")
      case True
      have uneq: "(t2,e2) \<noteq> (t1,e1)" using insert.prems(5) t2_def by fastforce
      moreover have 1: "(t2,e2) \<in> fset ys" using insert.prems(2) by fastforce
      ultimately have "dlverts t1 \<inter> dlverts t2 = {}" using insert.prems(4) wf_lverts by fastforce
      then have 2: "\<forall>x1\<in>fst ` set (dtree_to_list (Node r {|(t2, e2)|})). set x1 \<inter> dlverts t1 = {}"
        using dtree_to_list_x1_disjoint by fast
      have "(darcs t1 \<union> {e1}) \<inter> (darcs t2 \<union> {e2}) = {}"
        using insert.prems(4) uneq 1 disjoint_darcs_if_wf_aux5 wf_arcs by fast
      then have 3: "\<forall>e\<in>snd ` set (dtree_to_list (Node r {|(t2, e2)|})). e \<notin> darcs t1 \<union> {e1}"
        using dtree_to_list_e_disjoint by fast
      have "[] \<notin> dverts t2" using 1 wf_lverts empty_notin_wf_dlverts by auto
      then have "\<forall>x1\<in>fst ` set (dtree_to_list (Node r {|(t2, e2)|})). x1 \<noteq> []"
        using 1 dtree_to_list_x_in_dverts by metis
      then show ?thesis using True 2 3 by fastforce
    next
      case False
      have "xs |\<subseteq>| finsert x xs" by blast
      then have f_xs: "ffold ?f z xs = ffold ?f' z xs"
        using merge_ffold_supset 0 by presburger
      have "ffold ?f z (finsert x xs) = ?f x (ffold ?f z xs)"
        using Comm.ffold_finsert[OF insert.hyps] by blast
      then have 0: "ffold ?f z (finsert x xs) = ?f x (ffold ?f' z xs)" using f_xs by argo
      then have "?f x (ffold ?f' z xs) \<noteq> ffold ?f' z xs" using not_right by argo
      then have "?f (t2,e2) (ffold ?f' z xs)
                = ?merge cmp' (dtree_to_list (Node r {|(t2,e2)|})) (ffold ?f' z xs)"
        using merge_f_merge_if_not_snd t2_def by blast
      then have "ffold ?f z (finsert x xs)
                = ?merge cmp' (dtree_to_list (Node r {|(t2,e2)|})) (ffold ?f' z xs)"
        using 0 t2_def by argo
      then have "(v,e) \<in> set (?merge cmp' (dtree_to_list (Node r {|(t2,e2)|})) (ffold ?f' z xs))"
        using insert.prems(6) by argo
      then have "(v,e) \<in> set (ffold ?f' z xs)" using set_merge False by fast
      then show ?thesis using insert.IH insert.prems by force
    qed
  qed
qed (auto simp: ffold.rep_eq)

lemma merge_ffold_empty_inter_preserv':
  "\<lbrakk>list_dtree (Node r (finsert x xs));
    \<forall>(v,e) \<in> set z. set v \<inter> dlverts t1 = {} \<and> v\<noteq>[] \<and> e \<notin> darcs t1 \<union> {e1};
    (t1,e1) \<in> fset (finsert x xs); (t1,e1) \<notin> fset xs; (v,e) \<in> set (ffold (merge_f r xs) z xs)\<rbrakk>
    \<Longrightarrow> set v \<inter> dlverts t1 = {} \<and> v \<noteq> [] \<and> e \<notin> darcs t1 \<union> {e1}"
  using merge_ffold_empty_inter_preserv[of r "finsert x xs" xs z t1 e1 v e] by fast

lemma merge_ffold_set_sub_union:
  "list_dtree (Node r xs)
    \<Longrightarrow> set (ffold (merge_f r xs) [] xs) \<subseteq> (\<Union>x\<in>fset xs. set (dtree_to_list (Node r {|x|})))"
proof(induction xs)
  case (insert x xs)
  obtain t1 e1 where t1_def[simp]: "x = (t1,e1)" by fastforce
  let ?f = "merge_f r (finsert x xs)"
  let ?f' = "merge_f r xs"
  have "(t1, e1) \<in> fset (finsert x xs)" by simp
  moreover have "(t1, e1) \<notin> fset xs" using insert.hyps by fastforce
  ultimately have xs_val:
    "(\<forall>(v,e) \<in> set (ffold ?f' [] xs). set v \<inter> dlverts t1 = {} \<and> v \<noteq> [] \<and> e \<notin> darcs t1 \<union> {e1})"
    using merge_ffold_empty_inter_preserv'[OF insert.prems empty_list_valid_merge] by blast
  have 0: "list_dtree (Node r xs)" using list_dtree_subset insert.prems by blast
  have "ffold ?f [] (finsert x xs) = ?f x (ffold ?f [] xs)"
    using Comm.ffold_finsert[OF insert.hyps] by blast
  also have "\<dots> = ?f x (ffold ?f' [] xs)"
    using merge_ffold_supset[of xs "finsert x xs" r "[]"] insert.prems by fastforce
  finally have "ffold ?f [] (finsert x xs)
              = Sorting_Algorithms.merge cmp' (dtree_to_list (Node r {|x|})) (ffold ?f' [] xs)"
    using merge_f_merge_if_conds[OF insert.prems xs_val] by simp
  then have "set (ffold ?f [] (finsert x xs))
        = set (Sorting_Algorithms.merge cmp' (dtree_to_list (Node r {|x|})) (ffold ?f' [] xs))"
    by argo
  then have "set (ffold ?f [] (finsert x xs))
        = (set (dtree_to_list (Node r {|x|})) \<union> set (ffold ?f' [] xs))" using set_merge by fast
  then show ?case using 0 insert.IH insert.prems by auto
qed (simp add: ffold.rep_eq)

lemma merge_ffold_nempty:
  "\<lbrakk>list_dtree (Node r xs); xs \<noteq> {||}\<rbrakk> \<Longrightarrow> ffold (merge_f r xs) [] xs \<noteq> []"
proof(induction xs)
  case (insert x xs)
  define f where "f = merge_f r (finsert x xs)"
  define f' where "f' = merge_f r xs"
  let ?merge = "Sorting_Algorithms.merge cmp'"
  have 0: "list_dtree (Node r xs)" using list_dtree_subset insert.prems(1) by blast
  obtain t2 e2 where t2_def[simp]: "x = (t2,e2)" by fastforce
  have "(t2, e2) \<in> fset (finsert x xs)" by simp
  moreover have "(t2, e2) \<notin> fset xs" using insert.hyps by fastforce
  ultimately have xs_val:
    "(\<forall>(v,e) \<in> set (ffold f' [] xs). set v \<inter> dlverts t2 = {} \<and> v \<noteq> [] \<and> e \<notin> darcs t2 \<union> {e2})"
    using merge_ffold_empty_inter_preserv'[OF insert.prems(1) empty_list_valid_merge] f'_def
    by blast
  have "ffold f [] (finsert x xs) = f x (ffold f [] xs)"
    using Comm.ffold_finsert[OF insert.hyps] f_def by blast
  also have "\<dots> = f x (ffold f' [] xs)"
    using merge_ffold_supset[of xs "finsert x xs" r "[]"] insert.prems(1) f_def f'_def by fastforce
  finally have "ffold f [] (finsert x xs) = ?merge (dtree_to_list (Node r {|x|})) (ffold f' [] xs)"
    using xs_val insert.prems f_def by simp
  then have merge: "ffold f [] (finsert x xs)
              = ?merge (dtree_to_list (Node r {|(t2,e2)|})) (ffold f'[] xs)"
    using t2_def by blast
  then show ?case
    using input_empty_if_merge_empty[of cmp' "dtree_to_list (Node r {|(t2,e2)|})"] f_def by auto
qed(simp)

lemma merge_f_ndisjoint_sets_aux:
  "\<not>disjoint_sets xs
    \<Longrightarrow> \<not>((t,e) \<in> fset xs \<and> disjoint_sets xs \<and> (\<forall>(v,_) \<in> set b. set v \<inter> dlverts t = {} \<and> v \<noteq> []))"
  by blast

lemma merge_f_not_list_dtree: "\<not>list_dtree (Node r xs) \<Longrightarrow> (merge_f r xs) a b = b"
  using merge_f_alt by simp

lemma merge_ffold_empty_if_nwf: "\<not>list_dtree (Node r ys) \<Longrightarrow> ffold (merge_f r ys) [] xs = []"
proof(induction xs)
  case (insert x xs)
  define f where "f = merge_f r ys"
  let ?f = "merge_f r ys"
  let ?merge = "Sorting_Algorithms.merge cmp'"
  obtain t2 e2 where t2_def[simp]: "x = (t2,e2)" by fastforce
  have "ffold f [] (finsert x xs) = ?f x (ffold f [] xs)"
    using Comm.ffold_finsert[OF insert.hyps] f_def by blast
  then have "ffold f [] (finsert x xs) = ffold f [] xs"
    using insert.prems merge_f_not_list_dtree by force
  then show ?case using insert f_def by argo
qed (simp add: ffold.rep_eq)

lemma merge_empty_if_nwf: "\<not>list_dtree (Node r xs) \<Longrightarrow> merge (Node r xs) = Node r {||}"
  unfolding merge_def using merge_ffold_empty_if_nwf by simp

lemma merge_empty_if_nwf_sucs: "\<not>list_dtree t1 \<Longrightarrow> merge t1 = Node (root t1) {||}"
  using merge_empty_if_nwf[of "root t1" "sucs t1"] by simp

lemma merge_empty: "merge (Node r {||}) = Node r {||}"
proof -
  have "comp_fun_commute (\<lambda>(t, e) b. b)"
    by (simp add: comp_fun_commute_const cond_case_prod_eta)
  hence "dtree_from_list r (ffold (\<lambda>(t, e) b. b) [] {||}) = Node r {||}"
    using comp_fun_commute.ffold_empty
    by (smt (verit, best) dtree_from_list.simps(1))
  thus ?thesis
    unfolding merge_def by simp
qed

lemma merge_empty_sucs:
  assumes "sucs t1 = {||}"
  shows "merge t1 = Node (root t1) {||}"
proof -
  have "dtree_from_list (dtree.root t1) (ffold (\<lambda>(t, e) b. b) [] {||}) = Node (dtree.root t1) {||}"
    by (simp add: ffold.rep_eq)
  with assms show ?thesis
    unfolding merge_def by simp
qed

lemma merge_singleton_sucs:
  assumes "list_dtree (Node (root t1) (sucs t1))" and "sucs t1 \<noteq> {||}"
  shows "\<exists>t e. merge t1 = Node (root t1) {|(t,e)|}"
  unfolding merge_def using merge_ffold_nempty[OF assms] dtree_from_list_singleton by fast

lemma merge_singleton:
  assumes "list_dtree (Node r xs)" and "xs \<noteq> {||}"
  shows "\<exists>t e. merge (Node r xs) = Node r {|(t,e)|}"
  unfolding merge_def dtree.sel(1) using merge_ffold_nempty[OF assms] dtree_from_list_singleton
  by fastforce

lemma merge_cases: "\<exists>t e. merge (Node r xs) = Node r {|(t,e)|} \<or> merge (Node r xs) = Node r {||}"
  using merge_singleton merge_empty_if_nwf merge_empty by blast

lemma merge_cases_sucs:
  "\<exists>t e. merge t1 = Node (root t1) {|(t,e)|} \<or> merge t1 = Node (root t1) {||}"
  using merge_singleton_sucs[of t1] merge_empty_if_nwf_sucs merge_empty_sucs by auto

lemma merge_single_root:
  "(t2,e2) \<in> fset (sucs (merge (Node r xs))) \<Longrightarrow> merge (Node r xs) = Node r {|(t2,e2)|}"
  using merge_cases[of r xs] by fastforce

lemma merge_single_root_sucs:
  "(t2,e2) \<in> fset (sucs (merge t1)) \<Longrightarrow> merge t1 = Node (root t1) {|(t2,e2)|}"
  using merge_cases_sucs[of t1] by auto

lemma merge_single_root1:
  "t2 \<in> fst ` fset (sucs (merge (Node r xs))) \<Longrightarrow> \<exists>e2. merge (Node r xs) = Node r {|(t2,e2)|}"
  using merge_single_root by fastforce

lemma merge_single_root1_sucs:
  "t2 \<in> fst ` fset (sucs (merge t1)) \<Longrightarrow> \<exists>e2. merge t1 = Node (root t1) {|(t2,e2)|}"
  using merge_single_root_sucs by fastforce

lemma merge_nempty_sucs: "\<lbrakk>list_dtree t1; sucs t1 \<noteq> {||}\<rbrakk> \<Longrightarrow> sucs (merge t1) \<noteq> {||}"
  using merge_singleton_sucs by fastforce

lemma merge_nempty: "\<lbrakk>list_dtree (Node r xs); xs \<noteq> {||}\<rbrakk> \<Longrightarrow> sucs (merge (Node r xs)) \<noteq> {||}"
  using merge_singleton by fastforce

lemma merge_xs: "merge (Node r xs) = dtree_from_list r (ffold (merge_f r xs) [] xs)"
  unfolding merge_def dtree.sel(1) dtree.sel(2) by blast

lemma merge_root_eq[simp]: "root (merge t1) = root  t1"
  unfolding merge_def by simp

lemma merge_ffold_fsts_in_childverts:
  "\<lbrakk>list_dtree (Node r xs); y \<in> fst ` set (ffold (merge_f r xs) [] xs)\<rbrakk>
    \<Longrightarrow> \<exists>t1 \<in> fst `  fset xs. y \<in> dverts t1"
proof(induction xs)
  case (insert x xs)
  obtain t1 e1 where t1_def[simp]: "x = (t1,e1)" by fastforce
  let ?f = "merge_f r (finsert x xs)"
  let ?f' = "merge_f r xs"
  have "(t1, e1) \<in> fset (finsert x xs)" by simp
  moreover have "(t1, e1) \<notin> fset xs" using insert.hyps by fastforce
  ultimately have xs_val:
    "(\<forall>(v,e) \<in> set (ffold ?f' [] xs). set v \<inter> dlverts t1 = {} \<and> v \<noteq> [] \<and> e \<notin> darcs t1 \<union> {e1})"
    using merge_ffold_empty_inter_preserv'[OF insert.prems(1) empty_list_valid_merge] by blast
  have 0: "list_dtree (Node r xs)" using list_dtree_subset insert.prems(1) by blast
  then show ?case
  proof(cases "y \<in> fst ` set (ffold (merge_f r xs) [] xs)")
    case True
    then show ?thesis using insert.IH[OF 0] by simp
  next
    case False
    have "ffold ?f [] (finsert x xs) = ?f x (ffold ?f [] xs)"
      using Comm.ffold_finsert[OF insert.hyps] by blast
    also have "\<dots> = ?f x (ffold ?f' [] xs)"
      using merge_ffold_supset[of xs "finsert x xs" r "[]"] insert.prems(1) by fastforce
    finally have "ffold ?f [] (finsert x xs)
                = Sorting_Algorithms.merge cmp' (dtree_to_list (Node r {|x|})) (ffold ?f' [] xs)"
      using xs_val insert.prems by simp
    then have "set (ffold ?f [] (finsert x xs))
          = set (Sorting_Algorithms.merge cmp' (dtree_to_list (Node r {|x|})) (ffold ?f' [] xs))"
      by argo
    then have "set (ffold ?f [] (finsert x xs))
          = (set (dtree_to_list (Node r {|x|})) \<union> set (ffold ?f' [] xs))"
      using set_merge by fast
    then have "y \<in> fst ` set (dtree_to_list (Node r {|x|}))" using False insert.prems by fast
    then show ?thesis by (simp add: dtree_to_list_x_in_dverts)
  qed
qed (simp add: ffold.rep_eq)

lemma verts_child_if_merge_child:
  assumes "t1 \<in> fst ` fset (sucs (merge t0))" and "x \<in> dverts t1"
  shows "\<exists>t2 \<in> fst ` fset (sucs t0). x \<in> dverts t2"
proof -
  have 0: "list_dtree t0" using assms(1) merge_empty_if_nwf_sucs by fastforce
  have "merge t0 \<noteq> Node (root t0) {||}" using assms(1) by force
  then obtain e1 where e1_def: "merge t0 = Node (root t0) {|(t1,e1)|}"
    using assms(1) merge_single_root1_sucs by blast
  then obtain ys where ys_def:
      "(root t1, e1) # ys = ffold (merge_f (root t0) (sucs t0)) [] (sucs t0)"
    unfolding merge_def by (metis (no_types, lifting) dtree_to_list.simps(1) dtree_to_from_list_id)
  then have "merge t0 = dtree_from_list (root t0) ((root t1, e1) # ys)" unfolding merge_def by simp
  then have "t1 = dtree_from_list (root t1) ys" using e1_def by simp
  then have "dverts t1 = (fst ` set ((root t1, e1) # ys))"
    using dtree_from_list_eq_dverts[of "root t1" ys] by simp
  then have "x \<in> fst ` set (ffold (merge_f (root t0) (sucs t0)) [] (sucs t0))"
    using assms(2) ys_def by simp
  then show ?thesis using merge_ffold_fsts_in_childverts[of "root t0"] 0 by simp
qed

lemma sucs_dverts_eq_dtree_list:
  assumes "(t1,e1) \<in> fset (sucs t)" and "max_deg t1 \<le> 1"
  shows "dverts (Node (root t) {|(t1,e1)|}) - {root t}
        = fst ` set (dtree_to_list (Node (root t) {|(t1,e1)|}))"
proof -
  have "{|(t1,e1)|} |\<subseteq>| sucs t" using assms(1) by fast
  then have wf: "wf_dverts (Node (root t) {|(t1,e1)|})"
    using wf_verts wf_dverts_sub by (metis dtree.exhaust_sel)
  have "\<forall>(t1,e1) \<in> fset (sucs t) . fcard {|(t1,e1)|} = 1" using fcard_single_1 by fast
  moreover have "max_deg (Node (root t) {|(t1,e1)|}) = max (max_deg t1) (fcard {|(t1,e1)|})"
    using mdeg_singleton by fast
  ultimately have "max_deg (Node (root t) {|(t1,e1)|}) \<le> 1"
    using assms by fastforce
  then show ?thesis using dtree_to_list_eq_dverts[OF wf] by simp
qed

lemma merge_ffold_set_eq_union:
  "list_dtree (Node r xs)
    \<Longrightarrow> set (ffold (merge_f r xs) [] xs) = (\<Union>x\<in>fset xs. set (dtree_to_list (Node r {|x|})))"
proof(induction xs)
  case (insert x xs)
  obtain t1 e1 where t1_def[simp]: "x = (t1,e1)" by fastforce
  let ?f = "merge_f r (finsert x xs)"
  let ?f' = "merge_f r xs"
  have "(t1, e1) \<in> fset (finsert x xs)" by simp
  moreover have "(t1, e1) \<notin> fset xs" using insert.hyps by fastforce
  ultimately have xs_val:
    "(\<forall>(v,e) \<in> set (ffold ?f' [] xs). set v \<inter> dlverts t1 = {} \<and> v \<noteq> [] \<and> e \<notin> darcs t1 \<union> {e1})"
    using merge_ffold_empty_inter_preserv'[OF insert.prems(1) empty_list_valid_merge] by blast
  have 1: "list_dtree (Node r xs)" using list_dtree_subset insert.prems(1) by blast
  have "ffold ?f [] (finsert x xs) = ?f x (ffold ?f [] xs)"
    using Comm.ffold_finsert[OF insert.hyps] by blast
  also have "\<dots> = ?f x (ffold ?f' [] xs)"
    using merge_ffold_supset[of xs "finsert x xs" r "[]"] insert.prems(1) by fastforce
  finally have "ffold ?f [] (finsert x xs)
              = Sorting_Algorithms.merge cmp' (dtree_to_list (Node r {|x|})) (ffold ?f' [] xs)"
    using xs_val insert.prems by simp
  then have "set (ffold ?f [] (finsert x xs))
        = set (Sorting_Algorithms.merge cmp' (dtree_to_list (Node r {|x|})) (ffold ?f' [] xs))"
    by argo
  then have "set (ffold ?f [] (finsert x xs))
        = (set (dtree_to_list (Node r {|x|})) \<union> set (ffold ?f' [] xs))" using set_merge by fast
  then show ?case using 1 insert.IH by simp
qed (simp add: ffold.rep_eq)

lemma sucs_dverts_no_root:
  "(t1,e1) \<in> fset (sucs t) \<Longrightarrow> dverts (Node (root t) {|(t1,e1)|}) - {root t} = dverts t1"
  using wf_verts wf_dverts'.simps unfolding wf_dverts_iff_dverts' by fastforce

lemma dverts_merge_sub:
  assumes "\<forall>t \<in> fst ` fset (sucs t0). max_deg t \<le> 1"
  shows "dverts (merge t0) \<subseteq> dverts t0"
proof
  fix x
  assume asm: "x \<in> dverts (merge t0)"
  show "x \<in> dverts t0"
  proof(cases "x = root (merge t0)")
    case True
    then show ?thesis by (simp add: dtree.set_sel(1))
  next
    case False
    then obtain t1 e1 where t1_def: "merge t0 = Node (root t0) ({|(t1,e1)|})"
      using merge_cases_sucs asm by fastforce
    then have 0: "list_dtree (Node (root t0) (sucs t0))"
      using merge_empty_if_nwf_sucs by fastforce
    have "x \<in> fst ` set (ffold (merge_f (root t0) (sucs t0)) [] (sucs t0))"
      using t1_def unfolding merge_def using False asm t1_def
        dtree_from_list_eq_dverts[of "root t0" "ffold (merge_f (root t0) (sucs t0)) [] (sucs t0)"]
      by auto
    then obtain t2 e2 where t2_def:
        "(t2,e2) \<in> fset (sucs t0)" "x \<in> fst ` set (dtree_to_list (Node (root t0) {|(t2,e2)|}))"
      using merge_ffold_set_sub_union[OF 0] by fast
    then have "x \<in> dverts t2" by (simp add: dtree_to_list_x_in_dverts)
    then show ?thesis using t2_def(1) dtree.set_sel(2) by fastforce
  qed
qed

lemma dverts_merge_eq[simp]:
  assumes "\<forall>t \<in> fst ` fset (sucs t). max_deg t \<le> 1"
  shows "dverts (merge t) = dverts t"
proof -
  have "\<forall>(t1,e1) \<in> fset (sucs t). dverts (Node (root t) {|(t1,e1)|}) - {root t}
        = fst ` set (dtree_to_list (Node (root t) {|(t1,e1)|}))"
    using sucs_dverts_eq_dtree_list assms
    by (smt (verit, ccfv_threshold) case_prodI2 fst_conv image_iff)
  then have "\<forall>(t1,e1) \<in> fset (sucs t). dverts t1
              = fst ` set (dtree_to_list (Node (root t) {|(t1,e1)|}))"
    by (metis (mono_tags, lifting) sucs_dverts_no_root case_prodD case_prodI2)
  then have "(\<Union>x\<in>fset (sucs t). \<Union> (dverts ` Basic_BNFs.fsts x))
          = (\<Union>x\<in>fset (sucs t). fst ` set (dtree_to_list (Node (root t) {|x|})))"
    by force
  then have "dverts t
          = insert (root t) (\<Union>x\<in>fset (sucs t). fst ` set (dtree_to_list (Node (root t) {|x|})))"
    using dtree.simps(6)[of "root t" "sucs t"] by auto
  also have "\<dots> = insert (root t) (fst ` set (ffold (merge_f (root t) (sucs t)) [] (sucs t)))"
    using merge_ffold_set_eq_union[of "root t" "sucs t"] list_dtree_axioms by auto
  also have "\<dots> = dverts (dtree_from_list (root t) (ffold (merge_f (root t) (sucs t)) [] (sucs t)))"
    using dtree_from_list_eq_dverts[of "root t"] by blast
  finally show ?thesis unfolding merge_def by blast
qed

lemma dlverts_merge_eq[simp]:
  assumes "\<forall>t \<in> fst ` fset (sucs t). max_deg t \<le> 1"
  shows "dlverts (merge t) = dlverts t"
  using dverts_merge_eq[OF assms] by (simp add: dlverts_eq_dverts_union)

lemma sucs_darcs_eq_dtree_list:
  assumes "(t1,e1) \<in> fset (sucs t)" and "max_deg t1 \<le> 1"
  shows "darcs (Node (root t) {|(t1,e1)|}) = snd ` set (dtree_to_list (Node (root t) {|(t1,e1)|}))"
proof -
  have "\<forall>(t1,e1) \<in> fset (sucs t) . fcard {|(t1,e1)|} = 1" using fcard_single_1 by fast
  moreover have "max_deg (Node (root t) {|(t1,e1)|}) = max (max_deg t1) (fcard {|(t1,e1)|})"
    using mdeg_singleton by fast
  ultimately have "max_deg (Node (root t) {|(t1,e1)|}) \<le> 1"
    using assms by fastforce
  then show ?thesis using dtree_to_list_eq_darcs by blast
qed

lemma darcs_merge_eq[simp]:
  assumes "\<forall>t \<in> fst ` fset (sucs t). max_deg t \<le> 1"
  shows "darcs (merge t) = darcs t"
proof -
  have 0: "list_dtree (Node (root t) (sucs t))" using list_dtree_axioms by simp
  have "\<forall>(t1,e1) \<in> fset (sucs t). darcs (Node (root t) {|(t1,e1)|})
        = snd ` set (dtree_to_list (Node (root t) {|(t1,e1)|}))"
    using sucs_darcs_eq_dtree_list assms
    by (smt (verit, ccfv_threshold) case_prodI2 fst_conv image_iff)
  then have "\<forall>(t1,e1) \<in> fset (sucs t). darcs t1 \<union> {e1}
              = snd ` set (dtree_to_list (Node (root t) {|(t1,e1)|}))"
    by simp
  moreover have "darcs t = (\<Union>(t1,e1)\<in>fset (sucs t). darcs t1 \<union> {e1})"
    using dtree.simps(7)[of "root t" "sucs t"] by force
  ultimately have "darcs t
            = (\<Union>(t1,e1)\<in>fset (sucs t). snd ` set (dtree_to_list (Node (root t) {|(t1,e1)|})))"
    by (smt (verit, best) Sup.SUP_cong case_prodE case_prod_conv)
  also have "\<dots> = (snd ` set (ffold (merge_f (root t) (sucs t)) [] (sucs t)))"
    using merge_ffold_set_eq_union[OF 0] by blast
  also have "\<dots> = darcs (dtree_from_list (root t) (ffold (merge_f (root t) (sucs t)) [] (sucs t)))"
    using dtree_from_list_eq_darcs[of "root t"] by fast
  finally show ?thesis unfolding merge_def by blast
qed

subsubsection \<open>Merging Preserves Well-Formedness\<close>

lemma dtree_to_list_x_in_darcs:
  "x \<in> snd ` set (dtree_to_list (Node r {|(t1,e1)|})) \<Longrightarrow> x \<in> (darcs t1 \<union> {e1})"
  using dtree_to_list_sub_darcs by fastforce

lemma dtree_to_list_snds_disjoint:
  "(darcs t1 \<union> {e1}) \<inter> (darcs t2 \<union> {e2}) = {}
    \<Longrightarrow> snd ` set (dtree_to_list (Node r {|(t1,e1)|})) \<inter> (darcs t2 \<union> {e2}) = {}"
  using dtree_to_list_x_in_darcs by fast

lemma dtree_to_list_snds_disjoint2:
  "(darcs t1 \<union> {e1}) \<inter> (darcs t2 \<union> {e2}) = {}
    \<Longrightarrow> snd ` set (dtree_to_list (Node r {|(t1,e1)|}))
      \<inter> snd ` set (dtree_to_list (Node r {|(t2,e2)|})) = {}"
  using disjoint_iff dtree_to_list_x_in_darcs by metis

lemma merge_ffold_arc_inter_preserv:
  "\<lbrakk>list_dtree (Node r ys); xs |\<subseteq>| ys; (darcs t1 \<union> {e1}) \<inter> (snd ` set z) = {};
    (t1,e1) \<in> fset ys; (t1,e1) \<notin> fset xs\<rbrakk>
    \<Longrightarrow> (darcs t1 \<union> {e1}) \<inter> (snd ` set (ffold (merge_f r xs) z xs)) = {}"
proof(induction xs)
  case (insert x xs)
  let ?f = "merge_f r (finsert x xs)"
  let ?f' = "merge_f r xs"
  let ?merge = "Sorting_Algorithms.merge"
  show ?case
  proof(cases "ffold ?f z (finsert x xs) = ffold ?f' z xs")
    case True
    then show ?thesis using insert.IH insert.prems by auto
  next
    case False
    obtain t2 e2 where t2_def[simp]: "x = (t2,e2)" by fastforce
    have 0: "list_dtree (Node r (finsert x xs))" using list_dtree_subset insert.prems(1,2) by blast
    have "(t2,e2) \<noteq> (t1,e1)" using insert.prems(5) t2_def by fastforce
    moreover have "(t2,e2) \<in> fset ys" using insert.prems(2) by fastforce
    moreover have "disjoint_darcs ys"
      using disjoint_darcs_if_wf[OF list_dtree.wf_arcs [OF insert.prems(1)]] by simp
    ultimately have "(darcs t1 \<union> {e1}) \<inter> (darcs t2 \<union> {e2}) = {}"
      using insert.prems(4) by fast
    then have 1: "(darcs t1 \<union> {e1}) \<inter> snd ` set (dtree_to_list (Node r {|(t2, e2)|})) = {}"
      using dtree_to_list_snds_disjoint by fast
    have 2: "(darcs t1 \<union> {e1}) \<inter> snd ` set (ffold ?f' z xs) = {}"
      using insert.IH insert.prems by simp
    have "xs |\<subseteq>| finsert x xs" by blast
    then have f_xs: "ffold ?f z xs = ffold ?f' z xs"
      using merge_ffold_supset 0 by presburger
    have "ffold ?f z (finsert x xs) = ?f x (ffold ?f z xs)"
      using Comm.ffold_finsert[OF insert.hyps] by blast
    then have 0: "ffold ?f z (finsert x xs) = ?f x (ffold ?f' z xs)" using f_xs by argo
    then have "?f x (ffold ?f' z xs) \<noteq> ffold ?f' z xs" using False by argo
    then have "?f (t2,e2) (ffold ?f' z xs)
              = ?merge cmp' (dtree_to_list (Node r {|(t2,e2)|})) (ffold ?f' z xs)"
      using merge_f_merge_if_not_snd t2_def by blast
    then have "ffold ?f z (finsert x xs)
              = ?merge cmp' (dtree_to_list (Node r {|(t2,e2)|})) (ffold ?f' z xs)"
      using 0 t2_def by argo
    then have "set (ffold ?f z (finsert x xs))
        = set (dtree_to_list (Node r {|(t2,e2)|})) \<union> set (ffold ?f' z xs)"
      using set_merge[of "dtree_to_list (Node r {|(t2,e2)|})"] by presburger
    then show ?thesis using 1 2 by fast
  qed
qed (auto simp: ffold.rep_eq)

lemma merge_ffold_wf_list_arcs:
  "\<lbrakk>\<And>x. x \<in> fset xs \<Longrightarrow> wf_darcs (Node r {|x|}); list_dtree (Node r xs)\<rbrakk>
    \<Longrightarrow> wf_list_arcs (ffold (merge_f r xs) [] xs)"
proof(induction xs)
  case (insert x xs)
  obtain t1 e1 where t1_def[simp]: "x = (t1,e1)" by fastforce
  let ?f = "merge_f r (finsert x xs)"
  let ?f' = "merge_f r xs"
  have 0: "(t1, e1) \<in> fset (finsert x xs)" by simp
  moreover have t1_not_xs: "(t1, e1) \<notin> fset xs" using insert.hyps by fastforce
  ultimately have xs_val:
    "(\<forall>(v,e) \<in> set (ffold ?f' [] xs). set v \<inter> dlverts t1 = {} \<and> v \<noteq> [] \<and> e \<notin> darcs t1 \<union> {e1})"
    using merge_ffold_empty_inter_preserv'[OF insert.prems(2) empty_list_valid_merge] by blast
  have 1: "wf_list_arcs (dtree_to_list (Node r {|x|}))"
    using insert.prems(1) 0 t1_def wf_list_arcs_if_wf_darcs by fast
  have "list_dtree (Node r xs)" using list_dtree_subset insert.prems(2) by blast
  then have 2: "wf_list_arcs (ffold ?f' [] xs)" using insert.IH insert.prems by auto
  have "darcs (Node r {|x|}) \<inter> snd ` set (ffold ?f' [] xs) = {}"
    using merge_ffold_arc_inter_preserv[OF insert.prems(2), of xs t1 e1 "[]"] t1_not_xs by auto
  then have 3: "snd ` set (dtree_to_list (Node r {|x|})) \<inter> snd ` set (ffold ?f' [] xs) = {}"
    using dtree_to_list_sub_darcs by fast
  have "ffold ?f [] (finsert x xs) = ?f x (ffold ?f [] xs)"
    using Comm.ffold_finsert[OF insert.hyps] by blast
  also have "\<dots> = ?f x (ffold ?f' [] xs)"
    using merge_ffold_supset[of xs "finsert x xs" r "[]"] insert.prems(2) by fastforce
  finally have "ffold ?f [] (finsert x xs)
              = Sorting_Algorithms.merge cmp' (dtree_to_list (Node r {|x|})) (ffold ?f' [] xs)"
    using xs_val insert.prems by simp
  then show ?case using wf_list_arcs_merge[OF 1 2 3] by presburger
qed (simp add: ffold.rep_eq)

lemma merge_wf_darcs: "wf_darcs (merge t)"
proof -
  have "wf_list_arcs (ffold (merge_f (root t) (sucs t)) [] (sucs t))"
    using merge_ffold_wf_list_arcs[OF wf_darcs_sucs[OF wf_arcs]] list_dtree_axioms by simp
  then show ?thesis using wf_darcs_iff_wf_list_arcs merge_def by fastforce
qed

lemma merge_ffold_wf_list_lverts:
  "\<lbrakk>\<And>x. x \<in> fset xs \<Longrightarrow> wf_dlverts (Node r {|x|}); list_dtree (Node r xs)\<rbrakk>
    \<Longrightarrow> wf_list_lverts (ffold (merge_f r xs) [] xs)"
proof(induction xs)
  case (insert x xs)
  obtain t1 e1 where t1_def[simp]: "x = (t1,e1)" by fastforce
  let ?f = "merge_f r (finsert x xs)"
  let ?f' = "merge_f r xs"
  have 0: "(t1, e1) \<in> fset (finsert x xs)" by simp
  moreover have "(t1, e1) \<notin> fset xs" using insert.hyps by fastforce
  ultimately have xs_val:
    "(\<forall>(v,e) \<in> set (ffold ?f' [] xs). set v \<inter> dlverts t1 = {} \<and> v \<noteq> [] \<and> e \<notin> darcs t1 \<union> {e1})"
    using merge_ffold_empty_inter_preserv'[OF insert.prems(2) empty_list_valid_merge] by blast
  have 1: "wf_list_lverts (dtree_to_list (Node r {|x|}))"
    using insert.prems(1) 0 t1_def wf_list_lverts_if_wf_dlverts by fast
  have "list_dtree (Node r xs)" using list_dtree_subset insert.prems(2) by blast
  then have 2: "wf_list_lverts (ffold ?f' [] xs)" using insert.IH insert.prems by auto
  have "\<forall>v2\<in>fst ` set (ffold ?f' [] xs). set v2 \<inter> dlverts t1 = {}"
    using xs_val by fastforce
  then have 3: "\<forall>v1\<in>fst ` set (dtree_to_list (Node r {|x|})). \<forall>v2\<in>fst ` set (ffold ?f' [] xs).
                  set v1 \<inter> set v2 = {}"
    using dtree_to_list_x1_list_disjoint t1_def by fast
  have "ffold ?f [] (finsert x xs) = ?f x (ffold ?f [] xs)"
    using Comm.ffold_finsert[OF insert.hyps] by blast
  also have "\<dots> = ?f x (ffold ?f' [] xs)"
    using merge_ffold_supset[of xs "finsert x xs" r "[]"] insert.prems(2) by fastforce
  finally have "ffold ?f [] (finsert x xs)
              = Sorting_Algorithms.merge cmp' (dtree_to_list (Node r {|x|})) (ffold ?f' [] xs)"
    using xs_val insert.prems by simp
  then show ?case using wf_list_lverts_merge[OF 1 2 3] by presburger
qed (simp add: ffold.rep_eq)

lemma merge_ffold_root_inter_preserv:
  "\<lbrakk>list_dtree (Node r xs); \<forall>t1 \<in> fst ` fset xs. set r' \<inter> dlverts t1 = {};
    \<forall>v1 \<in> fst ` set z. set r' \<inter> set v1 = {}; (v,e) \<in> set (ffold (merge_f r xs) z xs)\<rbrakk>
    \<Longrightarrow> set r' \<inter> set v = {}"
proof(induction xs)
  case (insert x xs)
  let ?f = "merge_f r (finsert x xs)"
  let ?f' = "merge_f r xs"
  let ?merge = "Sorting_Algorithms.merge"
  have 0: "list_dtree (Node r xs)" using insert.prems(1) list_dtree_subset by blast
  show ?case
  proof(cases "ffold ?f z (finsert x xs) = ffold ?f' z xs")
    case True
    then show ?thesis using insert.IH[OF 0] insert.prems(2-4) by simp
  next
    case not_right: False
    obtain t2 e2 where t2_def[simp]: "x = (t2,e2)" by fastforce
    show ?thesis
    proof(cases "(v,e) \<in> set (dtree_to_list (Node r {|(t2,e2)|}))")
      case True
      then show ?thesis using dtree_to_list_x1_list_disjoint insert.prems(2) by fastforce
    next
      case False
      have "xs |\<subseteq>| finsert x xs" by blast
      then have f_xs: "ffold ?f z xs = ffold ?f' z xs"
        using merge_ffold_supset[of xs "finsert x xs"] insert.prems(1) by blast
      have "ffold ?f z (finsert x xs) = ?f x (ffold ?f z xs)"
        using Comm.ffold_finsert[OF insert.hyps] by blast
      then have 1: "ffold ?f z (finsert x xs) = ?f x (ffold ?f' z xs)" using f_xs by argo
      then have "?f x (ffold ?f' z xs) \<noteq> ffold ?f' z xs" using not_right by argo
      then have "?f (t2,e2) (ffold ?f' z xs)
                = ?merge cmp' (dtree_to_list (Node r {|(t2,e2)|})) (ffold ?f' z xs)"
        using merge_f_merge_if_not_snd t2_def by blast
      then have "ffold ?f z (finsert x xs)
                = ?merge cmp' (dtree_to_list (Node r {|(t2,e2)|})) (ffold ?f' z xs)"
        using 1 t2_def by argo
      then have "(v,e) \<in> set (?merge cmp' (dtree_to_list (Node r {|(t2,e2)|})) (ffold ?f' z xs))"
        using insert.prems(4) by argo
      then have "(v,e) \<in> set (ffold ?f' z xs)" using set_merge False by fast
      then show ?thesis using insert.IH insert.prems(2-3) 0 by auto
    qed
  qed
qed (fastforce simp: ffold.rep_eq)

lemma merge_wf_dlverts: "wf_dlverts (merge t)"
proof -
  have 0: "list_dtree (Node (root t) (sucs t))" using list_dtree_axioms by simp
  have 1: "\<forall>t1\<in>fst ` fset (sucs t). set (root t) \<inter> dlverts t1 = {}"
    using wf_lverts wf_dlverts.simps[of "root t"] by fastforce
  have "\<forall>v\<in>fst ` set (ffold (merge_f (root t) (sucs t)) [] (sucs t)). set (root t) \<inter> set v = {}"
    using wf_lverts merge_ffold_root_inter_preserv[OF 0 1] by force
  moreover have "wf_list_lverts (ffold (merge_f (root t) (sucs t)) [] (sucs t))"
    using merge_ffold_wf_list_lverts[OF wf_dlverts_sucs[OF wf_lverts] 0] by simp
  moreover have "root t \<noteq> []" using wf_lverts wf_dlverts.elims(2) by fastforce
  ultimately show ?thesis unfolding merge_def using wf_dlverts_iff_wf_list_lverts by blast
qed

theorem merge_list_dtree: "list_dtree (merge t)"
  using merge_wf_dlverts merge_wf_darcs list_dtree_def by blast

corollary merge_ranked_dtree: "ranked_dtree (merge t) cmp"
  using merge_list_dtree ranked_dtree_def ranked_dtree_axioms by auto

subsubsection \<open>Additional Merging Properties\<close>

lemma merge_ffold_distinct:
  "\<lbrakk>list_dtree (Node r xs); \<forall>t1 \<in> fst ` fset xs. \<forall>v\<in>dverts t1. distinct v;
    \<forall>v1 \<in> fst ` set z. distinct v1; v \<in> fst ` set (ffold (merge_f r xs) z xs)\<rbrakk>
    \<Longrightarrow> distinct v"
proof(induction xs)
  case (insert x xs)
  let ?f = "merge_f r (finsert x xs)"
  let ?f' = "merge_f r xs"
  let ?merge = "Sorting_Algorithms.merge"
  have 0: "list_dtree (Node r xs)" using insert.prems(1) list_dtree_subset by blast
  show ?case
  proof(cases "ffold ?f z (finsert x xs) = ffold ?f' z xs")
    case True
    then show ?thesis using insert.IH[OF 0] insert.prems(2-4) by simp
  next
    case not_right: False
    obtain t2 e2 where t2_def[simp]: "x = (t2,e2)" by fastforce
    show ?thesis
    proof(cases "v \<in> fst ` set (dtree_to_list (Node r {|(t2,e2)|}))")
      case True
      have "\<forall>v\<in>dverts t2. distinct v" using insert.prems(2) by simp
      then have 2: "\<forall>v\<in>fst ` set (dtree_to_list (Node r {|(t2,e2)|})). distinct v"
        by (simp add: dtree_to_list_x_in_dverts)
      then show ?thesis using True by auto
    next
      case False
      have "xs |\<subseteq>| finsert x xs" by blast
      then have f_xs: "ffold ?f z xs = ffold ?f' z xs"
        using merge_ffold_supset insert.prems(1) by presburger
      have "ffold ?f z (finsert x xs) = ?f x (ffold ?f z xs)"
        using Comm.ffold_finsert[OF insert.hyps] by blast
      then have 1: "ffold ?f z (finsert x xs) = ?f x (ffold ?f' z xs)" using f_xs by argo
      then have "?f x (ffold ?f' z xs) \<noteq> ffold ?f' z xs" using not_right by argo
      then have "?f (t2,e2) (ffold ?f' z xs)
                = ?merge cmp' (dtree_to_list (Node r {|(t2,e2)|})) (ffold ?f' z xs)"
        using merge_f_merge_if_not_snd t2_def by blast
      then have "ffold ?f z (finsert x xs)
                = ?merge cmp' (dtree_to_list (Node r {|(t2,e2)|})) (ffold ?f' z xs)"
        using 1 t2_def by argo
      then have "v \<in> fst ` set (?merge cmp' (dtree_to_list (Node r {|(t2,e2)|})) (ffold ?f' z xs))"
        using insert.prems(4) by argo
      then have "v \<in> fst ` set (ffold ?f' z xs)" using set_merge False by fast
      then show ?thesis using insert.IH[OF 0] insert.prems(2-3) by simp
    qed
  qed
qed (fastforce simp: ffold.rep_eq)

lemma distinct_merge:
  assumes "\<forall>v\<in>dverts t. distinct v" and "v\<in>dverts (merge t)"
  shows "distinct v"
proof(cases "v = root t")
  case True
  then show ?thesis by (simp add: dtree.set_sel(1) assms(1))
next
  case False
  then have 0: "v \<in> fst ` set (ffold (merge_f (root t) (sucs t)) [] (sucs t))"
    using merge_def assms(2) dtree_from_list_eq_dverts[of "root t"] by auto
  moreover have "\<forall>t1\<in>fst ` fset (sucs t). \<forall>v\<in>dverts t1. distinct v"
    using assms(1) dverts_child_subset[of "root t" "sucs t"] by auto
  moreover have "\<forall>v1\<in>fst ` set []. distinct v1" by simp
  moreover have 0: "list_dtree (Node (root t) (sucs t))" using list_dtree_axioms by simp
  ultimately show ?thesis using merge_ffold_distinct by fast
qed

lemma merge_hd_root_eq[simp]: "hd (root (merge t1)) = hd (root t1)"
  unfolding merge_def by auto

lemma merge_ffold_hd_is_child:
  "\<lbrakk>list_dtree (Node r xs); xs \<noteq> {||}\<rbrakk>
    \<Longrightarrow> \<exists>(t1,e1) \<in> fset xs. hd (ffold (merge_f r xs) [] xs) = (root t1,e1)"
proof(induction xs)
  case (insert x xs)
  interpret Comm: comp_fun_commute "merge_f r (finsert x xs)" by (rule merge_commute)
  define f where "f = merge_f r (finsert x xs)"
  define f' where "f' = merge_f r xs"
  let ?merge = "Sorting_Algorithms.merge cmp'"
  have 0: "list_dtree (Node r xs)" using list_dtree_subset insert.prems(1) by blast
  obtain t2 e2 where t2_def[simp]: "x = (t2,e2)" by fastforce
  have i1: "\<exists>(t1, e1)\<in>fset (finsert x xs). hd (dtree_to_list (Node r {|(t2,e2)|})) = (root t1, e1)"
    by simp
  have "(t2, e2) \<in> fset (finsert x xs)" by simp
  moreover have "(t2, e2) \<notin> fset xs" using insert.hyps by fastforce
  ultimately have xs_val:
    "(\<forall>(v,e) \<in> set (ffold f' [] xs). set v \<inter> dlverts t2 = {} \<and> v \<noteq> [] \<and> e \<notin> darcs t2 \<union> {e2})"
    using merge_ffold_empty_inter_preserv'[OF insert.prems(1) empty_list_valid_merge] f'_def
    by blast
  have "ffold f [] (finsert x xs) = f x (ffold f [] xs)"
    using Comm.ffold_finsert[OF insert.hyps] f_def by blast
  also have "\<dots> = f x (ffold f' [] xs)"
    using merge_ffold_supset[of xs "finsert x xs" r "[]"] insert.prems(1) f_def f'_def by fastforce
  finally have "ffold f [] (finsert x xs) = ?merge (dtree_to_list (Node r {|x|})) (ffold f' [] xs)"
    using xs_val insert.prems f_def by simp
  then have merge: "ffold f [] (finsert x xs)
              = ?merge (dtree_to_list (Node r {|(t2,e2)|})) (ffold f'[] xs)"
    using t2_def by blast
  show ?case
  proof(cases "xs = {||}")
    case True
    then show ?thesis using merge i1 f_def by (auto simp: ffold.rep_eq)
  next
    case False
    then have i2: "\<exists>(t1,e1) \<in> fset (finsert x xs). hd (ffold f' [] xs) = (root t1,e1)"
      using insert.IH[OF 0] f'_def by simp
    show ?thesis using merge_hd_exists_preserv[OF i1 i2] merge f_def by simp
  qed
qed(simp)

lemma merge_ffold_nempty_if_child:
  assumes "(t1,e1) \<in> fset (sucs (merge t0))"
  shows "ffold (merge_f (root t0) (sucs t0)) [] (sucs t0) \<noteq> []"
  using assms unfolding merge_def by auto

lemma merge_ffold_hd_eq_child:
  assumes "(t1,e1) \<in> fset (sucs (merge t0))"
  shows "hd (ffold (merge_f (root t0) (sucs t0)) [] (sucs t0)) = (root t1,e1)"
proof -
  have "merge t0 = (dtree_from_list (root t0) (ffold (merge_f (root t0) (sucs t0)) [] (sucs t0)))"
    unfolding merge_def by blast
  have "merge t0 = (Node (root t0) {|(t1,e1)|})" using merge_cases_sucs[of t0] assms by auto
  have 0: "(Node (root t0) {|(t1,e1)|})
      = (dtree_from_list (root t0) (ffold (merge_f (root t0) (sucs t0)) [] (sucs t0)))"
    using merge_cases_sucs[of t0] assms unfolding merge_def by fastforce
  then obtain ys where "(root t1, e1) # ys = ffold (merge_f (root t0) (sucs t0)) [] (sucs t0)"
    using dtree_from_list_eq_singleton[OF 0] by blast
  then show ?thesis using list.sel(1)[of "(root t1, e1)" ys] by simp
qed

lemma merge_child_in_orig:
  assumes "(t1,e1) \<in> fset (sucs (merge t0))"
  shows "\<exists>(t2,e2) \<in> fset (sucs t0). (root t2,e2) = (root t1,e1)"
proof -
  have 0: "list_dtree (Node (root t0) (sucs t0))" using assms merge_empty_if_nwf_sucs by fastforce
  have "sucs t0 \<noteq> {||}" using assms merge_empty_sucs by fastforce
  then obtain t2 e2 where t2_def: "(t2,e2) \<in> fset (sucs t0)"
    "hd (ffold (merge_f (root t0) (sucs t0)) [] (sucs t0)) = (root t2,e2)"
    using merge_ffold_hd_is_child[OF 0] by blast
  then show ?thesis using merge_ffold_hd_eq_child[OF assms] by auto
qed

lemma ffold_singleton: "comp_fun_commute f \<Longrightarrow> ffold f z {|x|} = f x z"
  using comp_fun_commute.ffold_finsert
  by (metis comp_fun_commute.ffold_empty finsert_absorb finsert_not_fempty)

lemma ffold_singleton1:
  "\<lbrakk>comp_fun_commute (\<lambda>a b. if P a b then Q a b else R a b); P x z\<rbrakk>
    \<Longrightarrow> ffold (\<lambda>a b. if P a b then Q a b else R a b) z {|x|} = Q x z"
  using ffold_singleton by fastforce

lemma ffold_singleton2:
  "\<lbrakk>comp_fun_commute (\<lambda>a b. if P a b then Q a b else R a b); \<not>P x z\<rbrakk>
    \<Longrightarrow> ffold (\<lambda>a b. if P a b then Q a b else R a b) z {|x|} = R x z"
  using ffold_singleton by fastforce

lemma merge_ffold_singleton_if_wf:
  assumes "list_dtree (Node r {|(t1,e1)|})"
  shows "ffold (merge_f r {|(t1,e1)|}) [] {|(t1,e1)|} = dtree_to_list (Node r {|(t1,e1)|})"
proof -
  interpret Comm: comp_fun_commute "merge_f r {|(t1,e1)|}" by (rule merge_commute)
  define f where "f = merge_f r {|(t1,e1)|}"
  have "ffold f [] {|(t1,e1)|} = f (t1,e1) (ffold f [] {||})"
    using Comm.ffold_finsert f_def by blast
  then show ?thesis using f_def assms by (simp add: ffold.rep_eq)
qed

lemma merge_singleton_if_wf:
  assumes "list_dtree (Node r {|(t1,e1)|})"
  shows "merge (Node r {|(t1,e1)|}) = dtree_from_list r (dtree_to_list (Node r {|(t1,e1)|}))"
  using merge_ffold_singleton_if_wf[OF assms] merge_xs by simp

lemma merge_disjoint_if_child:
  "merge (Node r {|(t1,e1)|}) = Node r {|(t2,e2)|} \<Longrightarrow> list_dtree (Node r {|(t1,e1)|})"
  using merge_empty_if_nwf by fastforce

lemma merge_root_child_eq:
  "merge (Node r {|(t1,e1)|}) = Node r {|(t2,e2)|} \<Longrightarrow> root t1 = root t2"
  using merge_singleton_if_wf[OF merge_disjoint_if_child] by fastforce

lemma merge_ffold_split_subtree:
  "\<lbrakk>\<forall>t \<in> fst ` fset xs. max_deg t \<le> 1; list_dtree (Node r xs);
    as@(v,e)#bs = ffold (merge_f r xs) [] xs\<rbrakk>
    \<Longrightarrow> \<exists>ys. strict_subtree (Node v ys) (Node r xs) \<and> dverts (Node v ys) \<subseteq> (fst ` set ((v,e)#bs))"
proof(induction xs arbitrary: as bs)
  case (insert x xs)
  obtain t1 e1 where t1_def[simp]: "x = (t1,e1)" by fastforce
  define f' where "f' = merge_f r xs"
  let ?f = "merge_f r (finsert x xs)"
  let ?f' = "merge_f r xs"
  have "(t1, e1) \<in> fset (finsert x xs)" by simp
  moreover have "(t1, e1) \<notin> fset xs" using insert.hyps by fastforce
  ultimately have xs_val:
    "(\<forall>(v,e) \<in> set (ffold ?f' [] xs). set v \<inter> dlverts t1 = {} \<and> v \<noteq> [] \<and> e \<notin> darcs t1 \<union> {e1})"
    using merge_ffold_empty_inter_preserv'[OF insert.prems(2) empty_list_valid_merge] by blast
  have 0: "\<forall>t \<in> fst ` fset xs. max_deg t \<le> 1" using insert.prems(1) by simp
  have 1: "list_dtree (Node r xs)" using list_dtree_subset insert.prems(2) by blast
  have "ffold ?f [] (finsert x xs) = ?f x (ffold ?f [] xs)"
    using Comm.ffold_finsert[OF insert.hyps] by blast
  also have "\<dots> = ?f x (ffold ?f' [] xs)"
    using merge_ffold_supset[of xs "finsert x xs" r "[]"] insert.prems(2) by fastforce
  finally have ind: "ffold ?f [] (finsert x xs)
              = Sorting_Algorithms.merge cmp' (dtree_to_list (Node r {|x|})) (ffold f' [] xs)"
    using insert.prems(2) xs_val f'_def by simp
  have "max_deg (fst x) \<le> 1" using insert.prems(1) by simp
  then have "max_deg (Node r {|x|}) \<le> 1"
    using mdeg_child_sucs_eq_if_gt1[of r "fst x" "snd x" "root (fst x)"] by fastforce
  then have "\<forall>as bs. as@(v,e)#bs = dtree_to_list (Node r {|x|}) \<longrightarrow>
        (\<exists>zs. strict_subtree (Node v zs) (Node r {|x|})
          \<and> dverts (Node v zs) \<subseteq> fst ` set ((v,e)#bs))"
    using dtree_to_list_split_subtree_dverts_eq_fsts' by fast
  then have left: "\<forall>as bs. as@(v,e)#bs = dtree_to_list (Node r {|x|}) \<longrightarrow>
        (\<exists>zs. strict_subtree (Node v zs) (Node r (finsert x xs))
          \<and> dverts (Node v zs) \<subseteq> fst ` set ((v,e)#bs))"
    using strict_subtree_singleton[where xs="finsert x xs"] by blast
  have "\<forall>as bs. as@(v,e)#bs = ffold f' [] xs \<longrightarrow>
        (\<exists>zs. strict_subtree (Node v zs) (Node r xs)
          \<and> dverts (Node v zs) \<subseteq> fst ` set ((v,e)#bs))"
    using insert.IH[OF 0 1] f'_def by blast
  then have right: "\<forall>as bs. as@(v,e)#bs = ffold f' [] xs \<longrightarrow>
        (\<exists>zs. strict_subtree (Node v zs) (Node r (finsert x xs))
          \<and> dverts (Node v zs) \<subseteq> fst ` set ((v,e)#bs))"
    using strict_subtree_subset[where r=r and xs=xs and ys="finsert x xs"] by fast
  then show ?case using merge_split_supset_strict_subtree[OF left right] ind insert.prems(3) by simp
qed (simp add: ffold.rep_eq)

lemma merge_strict_subtree_dverts_sup:
  assumes "\<forall>t \<in> fst ` fset (sucs t). max_deg t \<le> 1"
      and "strict_subtree (Node r xs) (merge t)"
    shows "\<exists>ys. is_subtree (Node r ys) t \<and> dverts (Node r ys) \<subseteq> dverts (Node r xs)"
proof -
  have 0: "list_dtree (Node (root t) (sucs t))" using list_dtree_axioms by simp
  have "\<forall>as r e bs. as@(r,e)#bs = ffold (merge_f (root t) (sucs t)) [] (sucs t)
    \<longrightarrow> (\<exists>ys. strict_subtree (Node r ys) (Node (root t) (sucs t))
         \<and> dverts (Node r ys) \<subseteq> fst ` set ((r,e)#bs))"
    using merge_ffold_split_subtree[OF assms(1) 0] by blast
  then have "\<forall>as r e bs. as@(r,e)#bs = ffold (merge_f (root t) (sucs t)) [] (sucs t) \<longrightarrow>
    (\<exists>ys. strict_subtree (Node r ys) t \<and> dverts (Node r ys) \<subseteq> fst ` set ((r,e)#bs))"
    by simp
  obtain as e bs where bs_def: "as@(r,e)#bs = ffold (merge_f (root t) (sucs t)) [] (sucs t)"
    using assms(2) dtree_from_list_uneq_sequence_xs[of r] unfolding merge_def by blast
  have "wf_dverts (merge t)" by (simp add: merge_wf_dlverts wf_dverts_if_wf_dlverts)
  then have wf: "wf_dverts (dtree_from_list (root t) (as@(r,e)#bs))"
    unfolding merge_def bs_def .
  moreover obtain ys where
      "strict_subtree (Node r ys) t" "dverts (Node r ys) \<subseteq> fst ` set ((r,e)#bs)"
    using merge_ffold_split_subtree[OF assms(1) 0 bs_def] by auto
  moreover have "strict_subtree (Node r xs) (dtree_from_list (root t) (as@(r,e)#bs))"
    using assms(2) unfolding bs_def merge_def .
  ultimately show ?thesis
    using dtree_from_list_dverts_subset_wfdverts1 unfolding strict_subtree_def by fast
qed

lemma merge_subtree_dverts_supset:
  assumes "\<forall>t\<in>fst ` fset (sucs t). max_deg t \<le> 1" and "is_subtree (Node r xs) (merge t)"
  shows "\<exists>ys. is_subtree (Node r ys) t \<and> dverts (Node r ys) \<subseteq> dverts (Node r xs)"
proof(cases "Node r xs = merge t")
  case True
  then obtain ys where "t = Node r ys" using merge_root_eq dtree.exhaust_sel dtree.sel(1) by metis
  then show ?thesis using dverts_merge_eq[OF assms(1)] True by auto
next
  case False
  then show ?thesis using merge_strict_subtree_dverts_sup assms strict_subtree_def by blast
qed

lemma merge_subtree_dlverts_supset:
  assumes "\<forall>t\<in>fst ` fset (sucs t). max_deg t \<le> 1" and "is_subtree (Node r xs) (merge t)"
  shows "\<exists>ys. is_subtree (Node r ys) t \<and> dlverts (Node r ys) \<subseteq> dlverts (Node r xs)"
proof -
  obtain ys where "is_subtree (Node r ys) t" "dverts (Node r ys) \<subseteq> dverts (Node r xs)"
    using merge_subtree_dverts_supset[OF assms] by blast
  then show ?thesis using dlverts_eq_dverts_union[of "Node r ys"] dlverts_eq_dverts_union by fast
qed

end

subsection \<open>Normalizing Dtrees\<close>

context ranked_dtree
begin

subsubsection \<open>Definitions\<close>

function normalize1 :: "('a list,'b) dtree \<Rightarrow> ('a list,'b) dtree" where
  "normalize1 (Node r {|(t1,e)|}) =
    (if rank (rev (root t1)) < rank (rev r) then Node (r@root t1) (sucs t1)
    else Node r {|(normalize1 t1,e)|})"
| "\<forall>x. xs \<noteq> {|x|} \<Longrightarrow> normalize1 (Node r xs) = Node r ((\<lambda>(t,e). (normalize1 t,e)) |`| xs)"
  by (metis darcs_mset.cases old.prod.exhaust) fast+
termination by lexicographic_order

lemma normalize1_size_decr[termination_simp]:
  "normalize1 t1 \<noteq> t1 \<Longrightarrow> size (normalize1 t1) < size t1"
proof(induction t1 rule: normalize1.induct)
  case (1 r t e)
  then show ?case
  proof(cases "rank (rev (root t)) < rank (rev r)")
    case True
    then show ?thesis using dtree_size_eq_root[of "root t" "sucs t"] by simp
  next
    case False
    then show ?thesis using dtree_size_img_le 1 by auto
  qed
next
  case (2 xs r)
  then have 0: "\<forall>t \<in> fst ` fset xs. size (normalize1 t) \<le> size t" by fastforce
  moreover have "\<exists>t \<in> fst ` fset xs. size (normalize1 t) < size t"
    using elem_neq_if_fset_neq[of normalize1 xs] 2 by fastforce
  ultimately show ?case using dtree_size_img_lt "2.hyps" by auto
qed

lemma normalize1_size_le: "size (normalize1 t1) \<le> size t1"
  by(cases "normalize1 t1=t1") (auto dest: normalize1_size_decr)

fun normalize :: "('a list,'b) dtree \<Rightarrow> ('a list,'b) dtree" where
  "normalize t1 = (let t2 = normalize1 t1 in if t1 = t2 then t2 else normalize t2)"

subsubsection \<open>Basic Proofs\<close>

lemma root_normalize1_eq1:
  "\<not>rank (rev (root t1)) < rank (rev r) \<Longrightarrow> root (normalize1 (Node r {|(t1,e1)|})) = r"
  by simp

lemma root_normalize1_eq1':
  "\<not>rank (rev (root t1)) \<le> rank (rev r) \<Longrightarrow> root (normalize1 (Node r {|(t1,e1)|})) = r"
  by simp

lemma root_normalize1_eq2: "\<forall>x. xs \<noteq> {|x|} \<Longrightarrow> root (normalize1 (Node r xs)) = r"
  by simp

lemma fset_img_eq: "\<forall>x \<in> fset xs. f x = x \<Longrightarrow> f |`| xs = xs"
  using fset_inject[of xs "f |`| xs"] by simp

lemma fset_img_uneq: "f |`| xs \<noteq> xs \<Longrightarrow> \<exists>x \<in> fset xs. f x \<noteq> x"
  using fset_img_eq by fastforce

lemma fset_img_uneq_prod: "(\<lambda>(t,e). (f t, e)) |`| xs \<noteq> xs \<Longrightarrow> \<exists>(t,e) \<in> fset xs. f t \<noteq> t"
  using fset_img_uneq[of "\<lambda>(t,e). (f t, e)" xs] by auto

lemma contr_if_normalize1_uneq:
  "normalize1 t1 \<noteq> t1
    \<Longrightarrow> \<exists>v t2 e2. is_subtree (Node v {|(t2,e2)|}) t1 \<and> rank (rev (root t2)) < rank (rev v)"
proof(induction t1 rule: normalize1.induct)
  case (2 xs r)
  then show ?case using fset_img_uneq_prod[of normalize1 xs] by fastforce
qed(fastforce)

lemma contr_before_normalize1:
  "\<lbrakk>is_subtree (Node v {|(t1,e1)|}) (normalize1 t3); rank (rev (root t1)) < rank (rev v)\<rbrakk>
    \<Longrightarrow> \<exists>v' t2 e2. is_subtree (Node v' {|(t2,e2)|}) t3 \<and> rank (rev (root t2)) < rank (rev v')"
  using contr_if_normalize1_uneq by force

subsubsection \<open>Normalizing Preserves Well-Formedness\<close>

lemma normalize1_darcs_sub: "darcs (normalize1 t1) \<subseteq> darcs t1"
proof(induction t1 rule: normalize1.induct)
  case (1 r t e)
  then show ?case
  proof(cases "rank (rev (root t)) < rank (rev r)")
    case True
    then have "darcs (normalize1 (Node r {|(t,e)|})) = darcs (Node (r@root t) (sucs t))" by simp
    also have "\<dots> = darcs (Node (root t) (sucs t))" using darcs_sub_if_children_sub by fast
    finally show ?thesis by auto
  next
    case False
    then show ?thesis using 1 by auto
  qed
qed (fastforce)

lemma disjoint_darcs_normalize1:
  "wf_darcs t1 \<Longrightarrow> disjoint_darcs ((\<lambda>(t,e). (normalize1 t,e)) |`| (sucs t1))"
  using disjoint_darcs_img[OF disjoint_darcs_if_wf, of t1 normalize1]
  by (simp add: normalize1_darcs_sub)

lemma wf_darcs_normalize1: "wf_darcs t1 \<Longrightarrow> wf_darcs (normalize1 t1)"
proof(induction t1 rule: normalize1.induct)
  case (1 r t e)
  show ?case
  proof(cases "rank (rev (root t)) < rank (rev r)")
    case True
    then show ?thesis
      using "1.prems" dtree.collapse singletonI finsert.rep_eq case_prodD
      unfolding wf_darcs_iff_darcs'
      by (metis (no_types, lifting) wf_darcs'.simps bot_fset.rep_eq normalize1.simps(1))
  next
    case False
    have "disjoint_darcs {|(normalize1 t,e)|}"
      using normalize1_darcs_sub disjoint_darcs_if_wf_xs[OF "1.prems"] by auto
    then show ?thesis using 1 False unfolding wf_darcs_iff_darcs' by force
  qed
next
  case (2 xs r)
  then show ?case
    using disjoint_darcs_normalize1[OF "2.prems"]
    by (fastforce simp: wf_darcs_iff_darcs')
qed

lemma normalize1_dlverts_eq[simp]: "dlverts (normalize1 t1) = dlverts t1"
proof(induction t1 rule: normalize1.induct)
  case (1 r t e)
  then show ?case
  proof(cases "rank (rev (root t)) < rank (rev r)")
    case True
    then show ?thesis using dlverts.simps[of "root t" "sucs t"] by force
  next
    case False
    then show ?thesis using 1 by auto
  qed
qed (fastforce)

lemma normalize1_dverts_contr_subtree:
  "\<lbrakk>v \<in> dverts (normalize1 t1); v \<notin> dverts t1\<rbrakk>
    \<Longrightarrow> \<exists>v2 t2 e2. is_subtree (Node v2 {|(t2,e2)|}) t1
        \<and> v2 @ root t2 = v \<and> rank (rev (root t2)) < rank (rev v2)"
proof(induction t1 rule: normalize1.induct)
  case (1 r t e)
  show ?case
  proof(cases "rank (rev (root t)) < rank (rev r)")
    case True
    then show ?thesis using "1.prems" dverts_suc_subseteq by fastforce
  next
    case False
    then show ?thesis using 1 by auto
  qed
qed(fastforce)

lemma normalize1_dverts_app_contr:
  "\<lbrakk>v \<in> dverts (normalize1 t1); v \<notin> dverts t1\<rbrakk>
    \<Longrightarrow> \<exists>v1\<in>dverts t1. \<exists>v2\<in>dverts t1. v1 @ v2 = v \<and> rank (rev v2) < rank (rev v1)"
  using normalize1_dverts_contr_subtree
  by (fastforce simp: single_subtree_root_dverts single_subtree_child_root_dverts)

lemma disjoint_dlverts_img:
  assumes "disjoint_dlverts xs" and "\<forall>(t,e) \<in> fset xs. dlverts (f t) \<subseteq> dlverts t"
  shows "disjoint_dlverts ((\<lambda>(t,e). (f t,e)) |`| xs)" (is "disjoint_dlverts ?xs")
proof (rule ccontr)
  assume "\<not> disjoint_dlverts ?xs"
  then obtain x1 e1 y1 e2 where asm: "(x1,e1) \<in> fset ?xs" "(y1,e2) \<in> fset ?xs"
      "dlverts x1 \<inter> dlverts y1 \<noteq> {} \<and> (x1,e1)\<noteq>(y1,e2)" by blast
  then obtain x2 where x2_def: "f x2 = x1" "(x2,e1) \<in> fset xs" by auto
  obtain y2 where y2_def: "f y2 = y1" "(y2,e2) \<in> fset xs" using asm(2) by auto
  have "dlverts x1 \<subseteq> dlverts x2" using assms(2) x2_def by fast
  moreover have "dlverts y1 \<subseteq> dlverts y2" using assms(2) y2_def by fast
  ultimately have "\<not> disjoint_dlverts xs" using asm(3) x2_def y2_def by blast
  then show False using assms(1) by blast
qed

lemma disjoint_dlverts_normalize1:
  "disjoint_dlverts xs \<Longrightarrow> disjoint_dlverts ((\<lambda>(t,e). (normalize1 t,e)) |`| xs)"
  using disjoint_dlverts_img[of xs] by simp

lemma disjoint_dlverts_normalize1_sucs:
  "disjoint_dlverts (sucs t1) \<Longrightarrow> disjoint_dlverts ((\<lambda>(t,e). (normalize1 t,e)) |`| (sucs t1))"
  using disjoint_dlverts_img[of "sucs t1"] by simp

lemma disjoint_dlverts_normalize1_wf:
  "wf_dlverts t1 \<Longrightarrow> disjoint_dlverts ((\<lambda>(t,e). (normalize1 t,e)) |`| (sucs t1))"
  using disjoint_dlverts_img[OF disjoint_dlverts_if_wf, of t1] by simp

lemma disjoint_dlverts_normalize1_wf':
  "wf_dlverts (Node r xs) \<Longrightarrow> disjoint_dlverts ((\<lambda>(t,e). (normalize1 t,e)) |`| xs)"
  using disjoint_dlverts_img[OF disjoint_dlverts_if_wf, of "Node r xs"] by simp

lemma root_empty_inter_dlverts_normalize1:
  assumes "wf_dlverts t1" and "(x1,e1) \<in> fset  ((\<lambda>(t,e). (normalize1 t,e)) |`| (sucs t1))"
  shows "set (root t1) \<inter> dlverts x1 = {}"
proof (rule ccontr)
  assume asm: "set (root t1) \<inter> dlverts x1 \<noteq> {}"
  obtain x2 where x2_def: "normalize1 x2 = x1" "(x2,e1) \<in> fset (sucs t1)" using assms(2) by auto
  have "set (root t1) \<inter> dlverts x2 \<noteq> {}" using x2_def(1) asm by force
  then show False using x2_def(2) assms(1) wf_dlverts.simps[of "root t1" "sucs t1"] by auto
qed

lemma wf_dlverts_normalize1: "wf_dlverts t1 \<Longrightarrow> wf_dlverts (normalize1 t1)"
proof(induction t1 rule: normalize1.induct)
  case (1 r t e)
  show ?case
  proof(cases "rank (rev (root t)) < rank (rev r)")
    case True
    have 0: "\<forall>(t1,e1) \<in> fset (sucs t). wf_dlverts t1"
      using "1.prems" wf_dlverts.simps[of "root t" "sucs t"] by auto
    have "\<forall>(t1,e1) \<in> fset (sucs t). set (root t) \<inter> dlverts t1 = {}"
      using "1.prems" wf_dlverts.simps[of "root t"] by fastforce
    then have "\<forall>(t1,e1) \<in> fset (sucs t). set (r@root t) \<inter> dlverts t1 = {}"
      using suc_in_dlverts "1.prems" by fastforce
    then show ?thesis using True 0 disjoint_dlverts_if_wf[of t] "1.prems" by auto
  next
    case False
    then show ?thesis
      using root_empty_inter_dlverts_normalize1[OF "1.prems"] disjoint_dlverts_normalize1 1 by auto
  qed
next
  case (2 xs r)
  have "\<forall>(t1,e1) \<in> fset ((\<lambda>(t, e). (normalize1 t, e)) |`| xs). set r \<inter> dlverts t1 = {}"
    using root_empty_inter_dlverts_normalize1[OF "2.prems"] by force
  then show ?case using disjoint_dlverts_normalize1 2 by auto
qed

corollary list_dtree_normalize1: "list_dtree (normalize1 t)"
  using wf_dlverts_normalize1[OF wf_lverts] wf_darcs_normalize1[OF wf_arcs] list_dtree_def by blast

corollary ranked_dtree_normalize1: "ranked_dtree (normalize1 t) cmp"
  using list_dtree_normalize1 ranked_dtree_def ranked_dtree_axioms by blast

lemma normalize_darcs_sub: "darcs (normalize t1) \<subseteq> darcs t1"
  apply(induction t1 rule: normalize.induct)
  by (smt (verit) normalize1_darcs_sub normalize.simps subset_trans)

lemma normalize_dlverts_eq: "dlverts (normalize t1) = dlverts t1"
  by(induction t1 rule: normalize.induct) (metis (full_types) normalize.elims normalize1_dlverts_eq)

theorem ranked_dtree_normalize: "ranked_dtree (normalize t) cmp"
  using ranked_dtree_axioms apply(induction t rule: normalize.induct)
  by (smt (verit) ranked_dtree.normalize.elims ranked_dtree.ranked_dtree_normalize1)

subsubsection \<open>Distinctness and hd preserved\<close>

lemma distinct_normalize1: "\<lbrakk>\<forall>v\<in>dverts t. distinct v; v\<in>dverts (normalize1 t)\<rbrakk> \<Longrightarrow> distinct v"
using ranked_dtree_axioms proof(induction t rule: normalize1.induct)
  case (1 r t e)
  then interpret R: ranked_dtree "Node r {|(t, e)|}" rank by blast
  show ?case
  proof(cases "rank (rev (root t)) < rank (rev r)")
    case True
    interpret T: ranked_dtree t rank using R.ranked_dtree_rec by auto
    have "set r \<inter> set (root t) = {}"
      using R.wf_lverts dlverts.simps[of "root t" "sucs t"] by auto
    then have "distinct (r@root t)" by (auto simp: dtree.set_sel(1) "1.prems"(1))
    moreover have "\<forall>v \<in> (\<Union>(t, e)\<in>fset (sucs t). dverts t). distinct v"
      using "1.prems"(1) dtree.set(1)[of "root t" "sucs t"] by fastforce
    ultimately show ?thesis using dverts_root_or_child "1.prems"(2) True by auto
  next
    case False
    then show ?thesis using R.ranked_dtree_rec 1 by auto
  qed
next
  case (2 xs r)
  then interpret R: ranked_dtree "Node r xs" rank by blast
  show ?case using R.ranked_dtree_rec 2 by fastforce
qed

lemma distinct_normalize: "\<forall>v\<in>dverts t. distinct v \<Longrightarrow> \<forall>v\<in>dverts (normalize t). distinct v"
using ranked_dtree_axioms proof(induction t rule: normalize.induct)
  case (1 t)
  then interpret T1: ranked_dtree "t" rank by blast
  interpret T2: ranked_dtree "normalize1 t" rank by (simp add: T1.ranked_dtree_normalize1)
  show ?case
    by (smt (verit, del_insts) 1 T1.distinct_normalize1 T2.ranked_dtree_axioms normalize.simps)
qed

lemma normalize1_hd_root_eq[simp]:
  assumes "root t1 \<noteq> []"
  shows "hd (root (normalize1 t1)) = hd (root t1)"
proof(cases "\<forall>x. sucs t1 \<noteq> {|x|}")
  case True
  then show ?thesis using normalize1.simps(2)[of "sucs t1" "root t1"] by simp
next
  case False
  then obtain t e where "{|(t, e)|} = sucs t1" by auto
  then show ?thesis using normalize1.simps(1)[of "root t1" t e] assms by simp
qed

corollary normalize1_hd_root_eq':
  "wf_dlverts t1 \<Longrightarrow> hd (root (normalize1 t1)) = hd (root t1)"
  using normalize1_hd_root_eq[of t1] wf_dlverts.simps[of "root t1" "sucs t1"] by simp

lemma normalize1_root_nempty:
  assumes "root t1 \<noteq> []"
  shows "root (normalize1 t1) \<noteq> []"
proof(cases "\<forall>x. sucs t1 \<noteq> {|x|}")
  case True
  then show ?thesis using normalize1.simps(2)[of "sucs t1" "root t1"] assms by simp
next
  case False
  then obtain t e where "{|(t, e)|} = sucs t1" by auto
  then show ?thesis using normalize1.simps(1)[of "root t1" t e] assms by simp
qed

lemma normalize_hd_root_eq[simp]: "root t1 \<noteq> [] \<Longrightarrow> hd (root (normalize t1)) = hd (root t1)"
using ranked_dtree_axioms proof(induction t1 rule: normalize.induct)
  case (1 t)
  then show ?case
  proof(cases "t = normalize1 t")
    case False
    then have "normalize t = normalize (normalize1 t)" by (simp add: Let_def)
    then show ?thesis using 1 normalize1_root_nempty by force
  qed(simp)
qed

corollary normalize_hd_root_eq'[simp]: "wf_dlverts t1 \<Longrightarrow> hd (root (normalize t1)) = hd (root t1)"
  using normalize_hd_root_eq wf_dlverts.simps[of "root t1" "sucs t1"] by simp

subsubsection \<open>Normalize and Sorting\<close>

lemma normalize1_uneq_if_contr:
  "\<lbrakk>is_subtree (Node r1 {|(t1,e1)|}) t2; rank (rev (root t1)) < rank (rev r1); wf_darcs t2\<rbrakk>
    \<Longrightarrow> t2 \<noteq> normalize1 t2"
proof(induction t2 rule: normalize1.induct)
  case (1 r t e)
  then show ?case
  proof(cases "rank (rev (root t)) < rank (rev r)")
    case True
    then show ?thesis using combine_uneq by fastforce
  next
    case False
    then show ?thesis using 1 by auto
  qed
next
  case (2 xs r)
  then obtain t e where t_def: "(t,e) \<in> fset xs" "is_subtree (Node r1 {|(t1,e1)|}) t" by auto
  then have "t \<noteq> normalize1 t" using 2 by fastforce
  then have "(normalize1 t, e) \<notin> fset xs"
    using "2.prems"(3) t_def(1) by (auto simp: wf_darcs_iff_darcs')
  moreover have "(normalize1 t, e) \<in> fset ((\<lambda>(t,e). (normalize1 t,e)) |`| xs)"
    using t_def(1) by auto
  ultimately have "(\<lambda>(t,e). (normalize1 t,e)) |`| xs \<noteq> xs" using t_def(1) by fastforce
  then show ?case using "2.hyps" by simp
qed

lemma sorted_ranks_if_normalize1_eq:
  "\<lbrakk>wf_darcs t2; is_subtree (Node r1 {|(t1,e1)|}) t2; t2 = normalize1 t2\<rbrakk>
    \<Longrightarrow> rank (rev r1) \<le> rank (rev (root t1))"
  using normalize1_uneq_if_contr by fastforce

lemma normalize_sorted_ranks:
  "\<lbrakk>is_subtree (Node r {|(t1,e1)|}) (normalize t)\<rbrakk> \<Longrightarrow> rank (rev r) \<le> rank (rev (root t1))"
using ranked_dtree_axioms proof(induction t rule: normalize.induct)
  case (1 t)
  then interpret T: ranked_dtree t by blast
  show ?case
    using 1 sorted_ranks_if_normalize1_eq[OF T.wf_arcs]
    by (smt (verit, ccfv_SIG) T.ranked_dtree_normalize1 normalize.simps)
qed

lift_definition cmp'' :: "('a list\<times>'b) comparator" is
  "(\<lambda>x y. if rank (rev (fst x)) < rank (rev (fst y)) then Less
    else if rank (rev (fst x)) > rank (rev (fst y)) then Greater
    else Equiv)"
  by (simp add: comparator_def)

lemma dtree_to_list_sorted_if_no_contr:
  "\<lbrakk>\<And>r1 t1 e1. is_subtree (Node r1 {|(t1,e1)|}) t2 \<Longrightarrow> rank (rev r1) \<le> rank (rev (root t1))\<rbrakk>
    \<Longrightarrow> sorted cmp'' (dtree_to_list (Node r {|(t2,e2)|}))"
proof(induction cmp'' "dtree_to_list (Node r {|(t2,e2)|})" arbitrary: r t2 e2 rule: sorted.induct)
  case (2 x)
  then show ?case using sorted_single[of cmp'' x] by simp
next
  case (3 y x xs)
  then obtain r1 t1 e1 where r1_def: "t2 = Node r1 {|(t1,e1)|}"
    using dtree_to_list.elims[of t2] by fastforce
  have "y = (root t2,e2)" using "3.hyps"(2) r1_def by simp
  moreover have "x = (root t1,e1)" using "3.hyps"(2) r1_def by simp
  moreover have "rank (rev (root t2)) \<le> rank (rev (root t1))" using "3.prems" r1_def by auto
  ultimately have "compare cmp'' y x \<noteq> Greater" using cmp''.rep_eq by simp
  moreover have "sorted cmp'' (dtree_to_list t2)" using 3 r1_def by auto
  ultimately show ?case using 3 r1_def by simp
qed(simp)

lemma dtree_to_list_sorted_if_no_contr':
  "\<lbrakk>\<And>r1 t1 e1. is_subtree (Node r1 {|(t1,e1)|}) t2 \<Longrightarrow> rank (rev r1) \<le> rank (rev (root t1))\<rbrakk>
    \<Longrightarrow> sorted cmp'' (dtree_to_list t2)"
  using dtree_to_list_sorted_if_no_contr[of t2] sorted_Cons_imp_sorted by fastforce

lemma dtree_to_list_sorted_if_subtree:
  "\<lbrakk>is_subtree t1 t2;
    \<And>r1 t1 e1. is_subtree (Node r1 {|(t1,e1)|}) t2 \<Longrightarrow> rank (rev r1) \<le> rank (rev (root t1))\<rbrakk>
    \<Longrightarrow> sorted cmp'' (dtree_to_list (Node r {|(t1,e1)|}))"
  using dtree_to_list_sorted_if_no_contr subtree_trans by blast

lemma dtree_to_list_sorted_if_subtree':
  "\<lbrakk>is_subtree t1 t2;
    \<And>r1 t1 e1. is_subtree (Node r1 {|(t1,e1)|}) t2 \<Longrightarrow> rank (rev r1) \<le> rank (rev (root t1))\<rbrakk>
    \<Longrightarrow> sorted cmp'' (dtree_to_list t1)"
  using dtree_to_list_sorted_if_no_contr' subtree_trans by blast

lemma normalize_dtree_to_list_sorted:
  "is_subtree t1 (normalize t) \<Longrightarrow> sorted cmp'' (dtree_to_list (Node r {|(t1,e1)|}))"
  using dtree_to_list_sorted_if_subtree normalize_sorted_ranks by blast

lemma normalize_dtree_to_list_sorted':
  "is_subtree t1 (normalize t) \<Longrightarrow> sorted cmp'' (dtree_to_list t1)"
  using dtree_to_list_sorted_if_subtree' normalize_sorted_ranks by blast

lemma gt_if_rank_contr: "rank (rev r0) < rank (rev r) \<Longrightarrow> compare cmp'' (r, e) (r0, e0) = Greater"
  by (auto simp: cmp''.rep_eq)

lemma rank_le_if_ngt: "compare cmp'' (r, e) (r0, e0) \<noteq> Greater \<Longrightarrow> rank (rev r) \<le> rank (rev r0)"
  using gt_if_rank_contr by force

lemma rank_le_if_sorted_from_list:
  assumes "sorted cmp'' ((v1,e1)#ys)" and "is_subtree (Node r0 {|(t0,e0)|}) (dtree_from_list v1 ys)"
  shows "rank (rev r0) \<le> rank (rev (root t0))"
proof -
  obtain e as bs where e_def: "as @ (r0, e) # (root t0, e0) # bs = ((v1,e1)#ys)"
    using dtree_from_list_sequence[OF assms(2)] by blast
  then have "sorted cmp'' (as @ (r0, e) # (root t0, e0) # bs)" using assms(1) by simp
  then have "sorted cmp'' ((r0, e) # (root t0, e0) # bs)" using sorted_app_r by blast
  then show ?thesis using rank_le_if_ngt by auto
qed

lemma cmp'_gt_if_cmp''_gt: "compare cmp'' x y = Greater \<Longrightarrow> compare cmp' x y = Greater"
  by (auto simp: cmp'.rep_eq cmp''.rep_eq split: if_splits)

lemma cmp'_lt_if_cmp''_lt: "compare cmp'' x y = Less \<Longrightarrow> compare cmp' x y = Less"
  by (auto simp: cmp'.rep_eq cmp''.rep_eq)

lemma cmp''_ge_if_cmp'_gt:
  "compare cmp' x y = Greater \<Longrightarrow> compare cmp'' x y = Greater \<or> compare cmp'' x y = Equiv"
  by (auto simp: cmp'.rep_eq cmp''.rep_eq split: if_splits)

lemma cmp''_nlt_if_cmp'_gt: "compare cmp' x y = Greater \<Longrightarrow> compare cmp'' y x \<noteq> Greater"
  by (auto simp: cmp'.rep_eq cmp''.rep_eq)

interpretation Comm: comp_fun_commute "merge_f r xs" by (rule merge_commute)

lemma sorted_cmp''_merge:
  "\<lbrakk>sorted cmp'' xs; sorted cmp'' ys\<rbrakk> \<Longrightarrow> sorted cmp'' (Sorting_Algorithms.merge cmp' xs ys)"
proof(induction xs ys taking: cmp' rule: Sorting_Algorithms.merge.induct)
  case (3 x xs y ys)
  let ?merge = "Sorting_Algorithms.merge cmp'"
  show ?case
  proof(cases "compare cmp' x y = Greater")
    case True
    have "?merge (x # xs) (y#ys) = y # (?merge (x # xs) ys)" using True by simp
    moreover have "sorted cmp'' (?merge (x # xs) ys)" using 3 True sorted_Cons_imp_sorted by fast
    ultimately show ?thesis
      using cmp''_nlt_if_cmp'_gt[OF True] "3.prems" sorted_rec[of cmp'' y]
        merge.elims[of cmp' "x#xs" ys "?merge (x # xs) ys"]
      by metis
  next
    case False
    have "?merge (x#xs) (y#ys) = x # (?merge xs (y#ys))" using False by simp
    moreover have "sorted cmp'' (?merge xs (y#ys))" using 3 False sorted_Cons_imp_sorted by fast
    ultimately show ?thesis
      using cmp'_gt_if_cmp''_gt False "3.prems" sorted_rec[of cmp'' x]
        merge.elims[of cmp' xs "y#ys" "?merge xs (y#ys)"]
      by metis
  qed
qed(auto)

lemma merge_ffold_sorted:
  "\<lbrakk>list_dtree (Node r xs); \<And>t2 r1 t1 e1. \<lbrakk>t2 \<in> fst ` fset xs; is_subtree (Node r1 {|(t1,e1)|}) t2\<rbrakk>
    \<Longrightarrow> rank (rev r1) \<le> rank (rev (root t1))\<rbrakk>
    \<Longrightarrow> sorted cmp'' (ffold (merge_f r xs) [] xs)"
proof(induction xs)
  case (insert x xs)
  interpret Comm: comp_fun_commute "merge_f r (finsert x xs)" by (rule merge_commute)
  define f where "f = merge_f r (finsert x xs)"
  define f' where "f' = merge_f r xs"
  let ?merge = "Sorting_Algorithms.merge cmp'"
  have 0: "list_dtree (Node r xs)" using list_dtree_subset insert.prems(1) by blast
  obtain t2 e2 where t2_def[simp]: "x = (t2,e2)" by fastforce
  have ind1: "sorted cmp'' (dtree_to_list (Node r {|(t2,e2)|}))"
    using dtree_to_list_sorted_if_no_contr insert.prems(2) by fastforce
  have "\<And>t2 r1 t1 e1. \<lbrakk>t2 \<in> fst ` fset xs; is_subtree (Node r1 {|(t1, e1)|}) t2\<rbrakk>
        \<Longrightarrow> rank (rev r1) \<le> rank (rev (root t1))"
    using insert.prems(2) by fastforce
  then have ind2: "sorted cmp'' (ffold f' [] xs)" using insert.IH[OF 0] f'_def by blast
  have "(t2, e2) \<in> fset (finsert x xs)" by simp
  moreover have "(t2, e2) \<notin> fset xs" using insert.hyps by fastforce
  ultimately have xs_val:
    "(\<forall>(v,e) \<in> set (ffold f' [] xs). set v \<inter> dlverts t2 = {} \<and> v \<noteq> [] \<and> e \<notin> darcs t2 \<union> {e2})"
    using merge_ffold_empty_inter_preserv'[OF insert.prems(1) empty_list_valid_merge] f'_def
    by blast
  have "ffold f [] (finsert x xs) = f x (ffold f [] xs)"
    using Comm.ffold_finsert[OF insert.hyps] f_def by blast
  also have "\<dots> = f x (ffold f' [] xs)"
    using merge_ffold_supset[of xs "finsert x xs" r "[]"] insert.prems(1) f_def f'_def by fastforce
  finally have "ffold f [] (finsert x xs) = ?merge (dtree_to_list (Node r {|x|})) (ffold f' [] xs)"
    using xs_val insert.prems f_def by simp
  then have merge: "ffold f [] (finsert x xs)
              = ?merge (dtree_to_list (Node r {|(t2,e2)|})) (ffold f'[] xs)"
    using t2_def by blast
  then show ?case using sorted_cmp''_merge[OF ind1 ind2] f_def by auto
qed (simp add: ffold.rep_eq)

lemma not_single_subtree_if_nwf:
  "\<not>list_dtree (Node r xs) \<Longrightarrow> \<not>is_subtree (Node r1 {|(t1,e1)|}) (merge (Node r xs))"
  using merge_empty_if_nwf by simp

lemma not_single_subtree_if_nwf_sucs:
  "\<not>list_dtree t2 \<Longrightarrow> \<not>is_subtree (Node r1 {|(t1,e1)|}) (merge t2)"
  using merge_empty_if_nwf_sucs by simp

lemma merge_strict_subtree_nocontr:
  assumes "\<And>t2 r1 t1 e1. \<lbrakk>t2 \<in> fst ` fset xs; is_subtree (Node r1 {|(t1,e1)|}) t2\<rbrakk>
            \<Longrightarrow> rank (rev r1) \<le> rank (rev (root t1))"
      and "strict_subtree (Node r1 {|(t1,e1)|}) (merge (Node r xs))"
    shows "rank (rev r1) \<le> rank (rev (root t1))"
proof(cases "list_dtree (Node r xs)")
  case True
  obtain e as bs where e_def: "as @ (r1, e) # (root t1, e1) # bs = ffold (merge_f r xs) [] xs"
    using dtree_from_list_uneq_sequence assms(2) unfolding merge_def dtree.sel strict_subtree_def
    by fast
  have "sorted cmp'' (ffold (merge_f r xs) [] xs)"
    using merge_ffold_sorted[OF True assms(1)] by simp
  then have "sorted cmp'' ((r1, e) # (root t1, e1) # bs)"
    using e_def sorted_app_r[of cmp'' as "(r1, e) # (root t1, e1) # bs"] by simp
  then show ?thesis using rank_le_if_sorted_from_list by fastforce
next
  case False
  then show ?thesis using not_single_subtree_if_nwf assms(2) by (simp add: strict_subtree_def)
qed

lemma merge_strict_subtree_nocontr2:
  assumes "\<And>r1 t1 e1. is_subtree (Node r1 {|(t1,e1)|}) (Node r xs)
            \<Longrightarrow> rank (rev r1) \<le> rank (rev (root t1))"
      and "strict_subtree (Node r1 {|(t1,e1)|}) (merge (Node r xs))"
    shows "rank (rev r1) \<le> rank (rev (root t1))"
  using merge_strict_subtree_nocontr[OF assms] by fastforce

lemma merge_strict_subtree_nocontr_sucs:
  assumes "\<And>t2 r1 t1 e1. \<lbrakk>t2 \<in> fst ` fset (sucs t0); is_subtree (Node r1 {|(t1,e1)|}) t2\<rbrakk>
            \<Longrightarrow> rank (rev r1) \<le> rank (rev (root t1))"
      and "strict_subtree (Node r1 {|(t1,e1)|}) (merge t0)"
    shows "rank (rev r1) \<le> rank (rev (root t1))"
  using merge_strict_subtree_nocontr[of "sucs t0" r1 t1 e1 "root t0"] assms by simp

lemma merge_strict_subtree_nocontr_sucs2:
  assumes "\<And>r1 t1 e1. is_subtree (Node r1 {|(t1,e1)|}) t2 \<Longrightarrow> rank (rev r1) \<le> rank (rev (root t1))"
      and "strict_subtree (Node r1 {|(t1,e1)|}) (merge t2)"
    shows "rank (rev r1) \<le> rank (rev (root t1))"
  using merge_strict_subtree_nocontr2[of "root t2" "sucs t2"] assms by auto

lemma no_contr_imp_parent:
  "\<lbrakk>is_subtree (Node r1 {|(t1,e1)|}) (Node r xs) \<Longrightarrow> rank (rev r1) \<le> rank (rev (root t1));
    t2 \<in> fst ` fset xs; is_subtree (Node r1 {|(t1,e1)|}) t2\<rbrakk>
      \<Longrightarrow> rank (rev r1) \<le> rank (rev (root t1))"
  using subtree_if_child subtree_trans by fast

lemma no_contr_imp_subtree:
  "\<lbrakk>\<And>t2 r1 t1 e1. \<lbrakk>t2 \<in> fst ` fset xs; is_subtree (Node r1 {|(t1,e1)|}) t2\<rbrakk>
      \<Longrightarrow> rank (rev r1) \<le> rank (rev (root t1));
    is_subtree (Node r1 {|(t1,e1)|}) (Node r xs); \<forall>x. xs \<noteq> {|x|}\<rbrakk>
    \<Longrightarrow> rank (rev r1) \<le> rank (rev (root t1))"
  by fastforce

lemma no_contr_imp_subtree_fcard:
  "\<lbrakk>\<And>t2 r1 t1 e1. \<lbrakk>t2 \<in> fst ` fset xs; is_subtree (Node r1 {|(t1,e1)|}) t2\<rbrakk>
      \<Longrightarrow> rank (rev r1) \<le> rank (rev (root t1));
    is_subtree (Node r1 {|(t1,e1)|}) (Node r xs); fcard xs \<noteq> 1\<rbrakk>
    \<Longrightarrow> rank (rev r1) \<le> rank (rev (root t1))"
  using fcard_single_1_iff[of xs] by fastforce

end

subsection \<open>Removing Wedges\<close>

context ranked_dtree
begin

fun merge1 :: "('a list,'b) dtree \<Rightarrow> ('a list,'b) dtree" where
  "merge1 (Node r xs) = (
    if fcard xs > 1 \<and> (\<forall>t \<in> fst ` fset xs. max_deg t \<le> 1) then merge (Node r xs)
    else Node r ((\<lambda>(t,e). (merge1 t,e)) |`| xs))"

lemma merge1_dverts_eq[simp]: "dverts (merge1 t) = dverts t"
using ranked_dtree_axioms proof(induction t)
  case (Node r xs)
  then interpret R: ranked_dtree "Node r xs" rank by blast
  show ?case
  proof(cases "fcard xs > 1 \<and> (\<forall>t \<in> fst ` fset xs. max_deg t \<le> 1)")
    case True
    then show ?thesis by simp
  next
    case False
    then show ?thesis using Node.IH R.ranked_dtree_rec by auto
  qed
qed

lemma merge1_dlverts_eq[simp]: "dlverts (merge1 t) = dlverts t"
using ranked_dtree_axioms proof(induction t)
  case (Node r xs)
  then interpret R: ranked_dtree "Node r xs" rank by blast
  show ?case
  proof(cases "fcard xs > 1 \<and> (\<forall>t \<in> fst ` fset xs. max_deg t \<le> 1)")
    case True
    then show ?thesis by simp
  next
    case False
    then show ?thesis using Node.IH R.ranked_dtree_rec by auto
  qed
qed

lemma dverts_merge1_img_sub:
  "\<forall>(t2,e2) \<in> fset xs. dverts (merge1 t2) \<subseteq> dverts t2
    \<Longrightarrow> dverts (Node r ((\<lambda>(t,e). (merge1 t,e)) |`| xs)) \<subseteq> dverts (Node r xs)"
  by fastforce

lemma merge1_dverts_sub: "dverts (merge1 t1) \<subseteq> dverts t1"
proof(induction t1)
  case (Node r xs)
  show ?case
  proof(cases "fcard xs > 1 \<and> (\<forall>t \<in> fst ` fset xs. max_deg t \<le> 1)")
    case True
    then show ?thesis using dverts_merge_sub by force
  next
    case False
    then have "\<forall>(t2,e2) \<in> fset xs. dverts (merge1 t2) \<subseteq> dverts t2" using Node by fastforce
    then show ?thesis using False dverts_merge1_img_sub by auto
  qed
qed

lemma disjoint_dlverts_merge1: "disjoint_dlverts ((\<lambda>(t,e). (merge1 t,e)) |`| (sucs t))"
proof -
  have "\<forall>(t, e)\<in>fset (sucs t). dlverts (merge1 t) \<subseteq> dlverts t"
    using ranked_dtree.merge1_dlverts_eq ranked_dtree_rec[of "root t"] by force
  then show ?thesis using disjoint_dlverts_img[OF disjoint_dlverts_if_wf[OF wf_lverts]] by simp
qed

lemma root_empty_inter_dlverts_merge1:
  assumes "(x1,e1) \<in> fset  ((\<lambda>(t,e). (merge1 t,e)) |`| (sucs t))"
  shows "set (root t) \<inter> dlverts x1 = {}"
proof (rule ccontr)
  assume asm: "set (root t) \<inter> dlverts x1 \<noteq> {}"
  obtain x2 where x2_def: "merge1 x2 = x1" "(x2,e1) \<in> fset (sucs t)" using assms by auto
  then interpret X: ranked_dtree x2 using ranked_dtree_rec dtree.collapse by blast
  have "set (root t) \<inter> dlverts x2 \<noteq> {}" using X.merge1_dlverts_eq x2_def(1) asm by argo
  then show False using x2_def(2) wf_lverts wf_dlverts.simps[of "root t" "sucs t"] by auto
qed

lemma wf_dlverts_merge1: "wf_dlverts (merge1 t)"
using ranked_dtree_axioms proof(induction t)
  case (Node r xs)
  then interpret R: ranked_dtree "Node r xs" rank by blast
  show ?case
  proof(cases "fcard xs > 1 \<and> (\<forall>t \<in> fst ` fset xs. max_deg t \<le> 1)")
    case True
    then show ?thesis using R.merge_wf_dlverts by simp
  next
    case False
    have "(\<forall>(t,e) \<in> fset ((\<lambda>(t,e). (merge1 t,e)) |`| xs). set r \<inter> dlverts t = {} \<and> wf_dlverts t)"
      using R.ranked_dtree_rec Node.IH R.root_empty_inter_dlverts_merge1 by fastforce
    then show ?thesis using R.disjoint_dlverts_merge1 R.wf_lverts False by auto
  qed
qed

lemma merge1_darcs_eq[simp]: "darcs (merge1 t) = darcs t"
using ranked_dtree_axioms proof(induction t)
  case (Node r xs)
  then interpret R: ranked_dtree "Node r xs" rank by blast
  show ?case using Node.IH R.ranked_dtree_rec by auto
qed

lemma disjoint_darcs_merge1: "disjoint_darcs ((\<lambda>(t,e). (merge1 t,e)) |`| (sucs t))"
proof -
  have "\<forall>(t, e)\<in>fset (sucs t). darcs (merge1 t) \<subseteq> darcs t"
    using ranked_dtree.merge1_darcs_eq ranked_dtree_rec[of "root t"] by force
  then show ?thesis using disjoint_darcs_img[OF disjoint_darcs_if_wf[OF wf_arcs]] by simp
qed

lemma wf_darcs_merge1: "wf_darcs (merge1 t)"
using ranked_dtree_axioms proof(induction t)
  case (Node r xs)
  then interpret R: ranked_dtree "Node r xs" rank by blast
  show ?case
  proof(cases "fcard xs > 1 \<and> (\<forall>t \<in> fst ` fset xs. max_deg t \<le> 1)")
    case True
    then show ?thesis using R.merge_wf_darcs by simp
  next
    case False
    then show ?thesis
      using R.disjoint_darcs_merge1 R.ranked_dtree_rec Node.IH
      by (auto simp: wf_darcs_iff_darcs')
  qed
qed

theorem ranked_dtree_merge1: "ranked_dtree (merge1 t) cmp"
  by(unfold_locales) (auto simp: wf_darcs_merge1 wf_dlverts_merge1 dest: cmp_antisym)

lemma distinct_merge1:
  "\<lbrakk>\<forall>v\<in>dverts t. distinct v; v\<in>dverts (merge1 t)\<rbrakk> \<Longrightarrow> distinct v"
using ranked_dtree_axioms proof(induction t arbitrary: v rule: merge1.induct)
  case (1 r xs)
  then interpret R: ranked_dtree "Node r xs" rank by blast
  show ?case
  proof(cases "fcard xs > 1 \<and> (\<forall>t \<in> fst ` fset xs. max_deg t \<le> 1)")
    case True
    then show ?thesis using R.distinct_merge[OF "1.prems"(1)] "1.prems"(2) by simp
  next
    case ind: False
    then show ?thesis
    proof(cases "v = r")
      case False
      have "v\<in>dverts (merge1 (Node r xs)) \<longleftrightarrow> v \<in> dverts (Node r ((\<lambda>(t,e). (merge1 t,e)) |`| xs))"
        using ind by auto
      then obtain t e where t_def: "(t,e) \<in> fset xs" "v \<in> dverts (merge1 t)"
        using False "1.prems"(2) by auto
      then have "\<forall>v\<in>dverts t. distinct v" using "1.prems"(1) by force
      then show ?thesis using "1.IH"[OF ind] t_def R.ranked_dtree_rec by fast
    qed(simp add: "1.prems"(1))
  qed
qed

lemma merge1_root_eq[simp]: "root (merge1 t1) = root t1"
  by(induction t1) simp

lemma merge1_hd_root_eq[simp]: "hd (root (merge1 t1)) = hd (root t1)"
  by simp

lemma merge1_mdeg_le: "max_deg (merge1 t1) \<le> max_deg t1"
proof(induction t1)
  case (Node r xs)
  then show ?case
  proof(cases "fcard xs > 1 \<and> (\<forall>t \<in> fst ` fset xs. max_deg t \<le> 1)")
    case True
    then have "max_deg (merge1 (Node r xs)) \<le> 1" using merge_mdeg_le_1 by simp
    then show ?thesis using mdeg_ge_fcard[of xs] True by simp
  next
    case False
    have 0: "\<forall>(t,e) \<in> fset xs. max_deg (merge1 t) \<le> max_deg t" using Node by force
    have "merge1 (Node r xs) = (Node r ((\<lambda>(t, e). (merge1 t, e)) |`| xs))"
      using False by auto
    then show ?thesis using mdeg_img_le'[OF 0] by simp
  qed
qed

lemma merge1_childdeg_gt1_if_fcard_gt1:
  "fcard (sucs (merge1 t1)) > 1 \<Longrightarrow> \<exists>t \<in> fst ` fset (sucs t1). max_deg t > 1"
proof(induction t1)
  case (Node r xs)
  have 0: "\<not>(fcard xs > 1 \<and> (\<forall>t \<in> fst ` fset xs. max_deg t \<le> 1))"
      using merge_fcard_le1[of "Node r xs"] Node.prems(1) by fastforce
  then have "fcard (sucs (merge1 (Node r xs))) \<le> fcard xs" using fcard_image_le by auto
  then show ?case using 0 Node.prems(1) by fastforce
qed

lemma merge1_fcard_le: "fcard (sucs (merge1 (Node r xs))) \<le> fcard xs"
  using fcard_image_le merge_fcard_le1[of "Node r xs"] by auto

lemma merge1_subtree_if_fcard_gt1:
  "\<lbrakk>is_subtree (Node r xs) (merge1 t1); fcard xs > 1\<rbrakk>
    \<Longrightarrow> \<exists>ys. merge1 (Node r ys) = Node r xs \<and> is_subtree (Node r ys) t1 \<and> fcard xs \<le> fcard ys"
proof(induction t1)
  case (Node r1 xs1)
  have 0: "\<not>(fcard xs1 > 1 \<and> (\<forall>t \<in> fst ` fset xs1. max_deg t \<le> 1))"
    using merge_fcard_le1_sub Node.prems by fastforce
  then have eq: "merge1 (Node r1 xs1) = Node r1 ((\<lambda>(t,e). (merge1 t,e)) |`| xs1)" by auto
  show ?case
  proof(cases "Node r xs = merge1 (Node r1 xs1)")
    case True
    moreover have "r = r1" using True eq by auto
    moreover have "fcard xs \<le> fcard xs1" using merge1_fcard_le True dtree.sel(2)[of r xs] by auto
    ultimately show ?thesis using self_subtree Node.prems(2) by auto
  next
    case False
    then obtain t2 e2 where "(t2,e2) \<in> fset xs1" "is_subtree (Node r xs) (merge1 t2)"
      using eq Node.prems(1) by auto
    then show ?thesis using Node.IH[of "(t2,e2)" t2] Node.prems(2) by fastforce
  qed
qed

lemma merge1_childdeg_gt1_if_fcard_gt1_sub:
  "\<lbrakk>is_subtree (Node r xs) (merge1 t1); fcard xs > 1\<rbrakk>
    \<Longrightarrow> \<exists>ys. merge1 (Node r ys) = Node r xs \<and> is_subtree (Node r ys) t1
          \<and> (\<exists>t \<in> fst ` fset ys. max_deg t > 1)"
  using merge1_subtree_if_fcard_gt1 merge1_childdeg_gt1_if_fcard_gt1 dtree.sel(2) by metis

lemma merge1_img_eq: "\<forall>(t2,e2) \<in> fset xs. merge1 t2 = t2 \<Longrightarrow> ((\<lambda>(t,e). (merge1 t,e)) |`| xs) = xs"
  using fset_img_eq[of xs "\<lambda>(t,e). (merge1 t,e)"] by force

lemma merge1_wedge_if_uneq:
  "merge1 t1 \<noteq> t1
    \<Longrightarrow> \<exists>r xs. is_subtree (Node r xs) t1 \<and> fcard xs > 1 \<and> (\<forall>t \<in> fst ` fset xs. max_deg t \<le> 1)"
proof(induction t1)
  case (Node r xs)
  show ?case
  proof(cases "fcard xs > 1 \<and> (\<forall>t \<in> fst ` fset xs. max_deg t \<le> 1)")
    case True
    then show ?thesis by auto
  next
    case False
    then have "merge1 (Node r xs) = Node r ((\<lambda>(t,e). (merge1 t,e)) |`| xs)" by auto
    then obtain t2 e2 where "(t2,e2) \<in> fset xs" "merge1 t2 \<noteq> t2"
      using Node.prems merge1_img_eq[of xs] by auto
    then show ?thesis using Node.IH[of "(t2,e2)"] by auto
  qed
qed

lemma merge1_mdeg_gt1_if_uneq:
  assumes "merge1 t1 \<noteq> t1"
  shows "max_deg t1 > 1"
proof -
  obtain r xs where r_def: "is_subtree (Node r xs) t1" "1 < fcard xs"
    using merge1_wedge_if_uneq[OF assms] by fast
  then show ?thesis using mdeg_ge_fcard[of xs] mdeg_ge_sub by force
qed

corollary merge1_eq_if_mdeg_le1: "max_deg t1 \<le> 1 \<Longrightarrow> merge1 t1 = t1"
  using merge1_mdeg_gt1_if_uneq by fastforce

lemma merge1_not_merge_if_fcard_gt1:
  "\<lbrakk>merge1 (Node r ys) = Node r xs; fcard xs > 1\<rbrakk> \<Longrightarrow> merge (Node r ys) \<noteq> Node r xs"
  using merge_fcard_le1[of "Node r ys"] by auto

lemma merge1_img_if_not_merge:
  "merge1 (Node r xs) \<noteq> merge (Node r xs)
    \<Longrightarrow> merge1 (Node r xs) = Node r ((\<lambda>(t,e). (merge1 t,e)) |`| xs)"
  by auto

lemma merge1_img_if_fcard_gt1:
  "\<lbrakk>merge1 (Node r ys) = Node r xs; fcard xs > 1\<rbrakk>
    \<Longrightarrow> merge1 (Node r ys) = Node r ((\<lambda>(t,e). (merge1 t,e)) |`| ys)"
  using merge1_img_if_not_merge merge1_not_merge_if_fcard_gt1[of r ys] by simp

lemma merge1_elem_in_img_if_fcard_gt1:
  "\<lbrakk>merge1 (Node r ys) = Node r xs; fcard xs > 1; (t2,e2) \<in> fset xs\<rbrakk>
    \<Longrightarrow> \<exists>t1. (t1,e2) \<in> fset ys \<and> merge1 t1 = t2"
  using merge1_img_if_fcard_gt1 by fastforce

lemma child_mdeg_gt1_if_sub_fcard_gt1:
  "\<lbrakk>is_subtree (Node r xs) (Node v ys); Node r xs \<noteq> Node v ys; fcard xs > 1\<rbrakk>
    \<Longrightarrow> \<exists>t1 e2. (t1,e2) \<in> fset ys \<and> max_deg t1 > 1"
  using mdeg_ge_fcard[of xs] mdeg_ge_sub by force

lemma merge1_subtree_if_mdeg_gt1:
  "\<lbrakk>is_subtree (Node r xs) (merge1 t1); max_deg (Node r xs) > 1\<rbrakk>
    \<Longrightarrow> \<exists>ys. merge1 (Node r ys) = Node r xs \<and> is_subtree (Node r ys) t1"
proof(induction t1)
  case (Node r1 xs1)
  then have 0: "\<not>(fcard xs1 > 1 \<and> (\<forall>t \<in> fst ` fset xs1. max_deg t \<le> 1))"
    using merge_mdeg_le1_sub by fastforce
  then have eq: "merge1 (Node r1 xs1) = Node r1 ((\<lambda>(t,e). (merge1 t,e)) |`| xs1)" by auto
  show ?case
  proof(cases "Node r xs = merge1 (Node r1 xs1)")
    case True
    moreover have "r = r1" using True eq by auto
    moreover have "fcard xs \<le> fcard xs1" using merge1_fcard_le True dtree.sel(2)[of r xs] by auto
    ultimately show ?thesis using self_subtree Node.prems(2) by auto
  next
    case False
    then obtain t2 e2 where "(t2,e2) \<in> fset xs1" "is_subtree (Node r xs) (merge1 t2)"
      using eq Node.prems(1) by auto
    then show ?thesis using Node.IH[of "(t2,e2)" t2] Node.prems(2) by fastforce
  qed
qed

lemma merge1_child_in_orig:
  assumes "merge1 (Node r ys) = Node r xs" and "(t1,e1) \<in> fset xs"
  shows "\<exists>t2. (t2,e1) \<in> fset ys \<and> root t2 = root t1"
proof(cases "fcard ys > 1 \<and> (\<forall>t \<in> fst ` fset ys. max_deg t \<le> 1)")
  case True
  then show ?thesis using merge_child_in_orig[of t1 e1 "Node r ys"] assms by auto
next
  case False
  then have "merge1 (Node r ys) = Node r ((\<lambda>(t,e). (merge1 t,e)) |`| ys)" by auto
  then show ?thesis using assms by fastforce
qed

lemma dverts_if_subtree_merge1:
  "is_subtree (Node r xs) (merge1 t1) \<Longrightarrow> r \<in> dverts t1"
  using merge1_dverts_sub dverts_subtree_subset by fastforce

lemma subtree_merge1_orig:
  "is_subtree (Node r xs) (merge1 t1) \<Longrightarrow> \<exists>ys. is_subtree (Node r ys) t1"
  using dverts_if_subtree_merge1 subtree_root_if_dverts by fast

lemma merge1_subtree_dlverts_supset:
  "is_subtree (Node r xs) (merge1 t)
    \<Longrightarrow> \<exists>ys. is_subtree (Node r ys) t \<and> dlverts (Node r ys) \<subseteq> dlverts (Node r xs)"
using ranked_dtree_axioms proof(induction t)
  case (Node r1 xs1)
  then interpret R: ranked_dtree "Node r1 xs1" by simp
  show ?case
  proof(cases "Node r xs = merge1 (Node r1 xs1)")
    case True
    then have "dlverts (Node r1 xs1) \<subseteq> dlverts (Node r xs)" using R.merge1_dlverts_eq by simp
    moreover have "r = r1" using True dtree.sel(1)[of r xs] by auto
    ultimately show ?thesis by auto
  next
    case uneq: False
    show ?thesis
    proof(cases "fcard xs1 > 1 \<and> (\<forall>t \<in> fst ` fset xs1. max_deg t \<le> 1)")
      case True
      then show ?thesis using R.merge_subtree_dlverts_supset Node.prems by simp
    next
      case False
      then have eq: "merge1 (Node r1 xs1) = Node r1 ((\<lambda>(t,e). (merge1 t,e)) |`| xs1)" by auto
      then obtain t2 e2 where "(t2,e2) \<in> fset xs1" "is_subtree (Node r xs) (merge1 t2)"
        using Node.prems(1) uneq by auto
      then show ?thesis using Node.IH[of "(t2,e2)"] R.ranked_dtree_rec by auto
    qed
  qed
qed

end

subsection \<open>IKKBZ-Sub\<close>

function denormalize :: "('a list, 'b) dtree \<Rightarrow> 'a list" where
  "denormalize (Node r {|(t,e)|}) = r @ denormalize t"
| "\<forall>x. xs \<noteq> {|x|} \<Longrightarrow> denormalize (Node r xs) = r"
  using dtree_to_list.cases by blast+
termination by lexicographic_order

lemma denormalize_set_eq_dlverts: "max_deg t1 \<le> 1 \<Longrightarrow> set (denormalize t1) = dlverts t1"
proof(induction t1 rule: denormalize.induct)
  case (1 r t e)
  then show ?case using mdeg_ge_child[of t e "{|(t, e)|}"] by force
next
  case (2 xs r)
  then have "max_deg (Node r xs) = 0" using mdeg_1_singleton[of r xs] by fastforce
  then have "xs = {||}" by (auto intro!: empty_if_mdeg_0)
  then show ?case using 2 by auto
qed

lemma denormalize_set_sub_dlverts: "set (denormalize t1) \<subseteq> dlverts t1"
  by(induction t1 rule: denormalize.induct) auto

lemma denormalize_distinct:
  "\<lbrakk>\<forall>v \<in> dverts t1. distinct v; wf_dlverts t1\<rbrakk> \<Longrightarrow> distinct (denormalize t1)"
proof(induction t1 rule: denormalize.induct)
  case (1 r t e)
  then have "set r \<inter> set (denormalize t) = {}" using denormalize_set_sub_dlverts by fastforce
  then show ?case using 1 by auto
next
  case (2 xs r)
  then show ?case by simp
qed

lemma denormalize_hd_root:
  assumes "root t \<noteq> []"
  shows "hd (denormalize t) = hd (root t)"
proof(cases "\<forall>x. sucs t \<noteq> {|x|}")
  case True
  then show ?thesis using denormalize.simps(2)[of "sucs t" "root t"] by simp
next
  case False
  then obtain t1 e where "{|(t1, e)|} = sucs t" by auto
  then show ?thesis using denormalize.simps(1)[of "root t" t1 e] assms by simp
qed

lemma denormalize_hd_root_wf: "wf_dlverts t \<Longrightarrow> hd (denormalize t) = hd (root t)"
  using denormalize_hd_root empty_notin_wf_dlverts dtree.set_sel(1)[of t] by force

lemma denormalize_nempty_if_wf: "wf_dlverts t \<Longrightarrow> denormalize t \<noteq> []"
  by (induction t rule: denormalize.induct) auto

context ranked_dtree
begin

lemma fcard_normalize_img_if_disjoint:
  "disjoint_darcs xs \<Longrightarrow> fcard ((\<lambda>(t,e). (normalize1 t,e)) |`| xs) = fcard xs"
  using snds_neq_img_card_eq[of xs] by fast

lemma fcard_merge1_img_if_disjoint:
  "disjoint_darcs xs \<Longrightarrow> fcard ((\<lambda>(t,e). (merge1 t,e)) |`| xs) = fcard xs"
  using snds_neq_img_card_eq[of xs] by fast

lemma fsts_uneq_if_disjoint_lverts_nempty:
  "\<lbrakk>disjoint_dlverts xs; \<forall>(t, e)\<in>fset xs. dlverts t \<noteq> {}\<rbrakk>
    \<Longrightarrow> \<forall>(t, e)\<in>fset xs. \<forall>(t2, e2)\<in>fset xs. t \<noteq> t2 \<or> (t, e) = (t2, e2)"
  by fast

lemma normalize1_dlverts_nempty:
  "\<forall>(t, e)\<in>fset xs. dlverts t \<noteq> {}
    \<Longrightarrow> \<forall>(t, e)\<in>fset ((\<lambda>(t, e). (normalize1 t, e)) |`| xs). dlverts t \<noteq> {}"
  by auto

lemma normalize1_fsts_uneq:
  assumes "disjoint_dlverts xs" and "\<forall>(t, e)\<in>fset xs. dlverts t \<noteq> {}"
  shows "\<forall>(t, e)\<in>fset xs. \<forall>(t2, e2)\<in>fset xs. normalize1 t \<noteq> normalize1 t2 \<or> (t,e) = (t2,e2)"
  by (smt (verit) assms Int_absorb case_prodD case_prodI2 normalize1_dlverts_eq)

lemma fcard_normalize_img_if_disjoint_lverts:
  "\<lbrakk>disjoint_dlverts xs; \<forall>(t, e)\<in>fset xs. dlverts t \<noteq> {}\<rbrakk>
    \<Longrightarrow> fcard ((\<lambda>(t,e). (normalize1 t,e)) |`| xs) = fcard xs"
  using fst_neq_img_card_eq[of xs normalize1] normalize1_fsts_uneq by auto

lemma fcard_normalize_img_if_wf_dlverts:
  "wf_dlverts (Node r xs) \<Longrightarrow> fcard ((\<lambda>(t,e). (normalize1 t,e)) |`| xs) = fcard xs"
  using dlverts_nempty_if_wf fcard_normalize_img_if_disjoint_lverts[of xs] by force

lemma fcard_normalize_img_if_wf_dlverts_sucs:
  "wf_dlverts t1 \<Longrightarrow> fcard ((\<lambda>(t,e). (normalize1 t,e)) |`| (sucs t1)) = fcard (sucs t1)"
  using fcard_normalize_img_if_wf_dlverts[of "root t1" "sucs t1"] by simp

lemma singleton_normalize1:
  assumes "disjoint_darcs xs" and "\<forall>x. xs \<noteq> {|x|}"
  shows "\<forall>x. (\<lambda>(t,e). (normalize1 t,e)) |`| xs \<noteq> {|x|}"
proof (rule ccontr)
  assume "\<not>(\<forall>x. (\<lambda>(t,e). (normalize1 t,e)) |`| xs \<noteq> {|x|})"
  then obtain x where "(\<lambda>(t,e). (normalize1 t,e)) |`| xs = {|x|}" by blast
  then have "fcard ((\<lambda>(t,e). (normalize1 t,e)) |`| xs) = 1" using fcard_single_1 by force
  then have "fcard xs = 1" using fcard_normalize_img_if_disjoint[OF assms(1)] by simp
  then have "\<exists>x. xs = {|x|}" using fcard_single_1_iff by fast
  then show False using assms(2) by simp
qed

lemma num_leaves_normalize1_eq[simp]: "wf_darcs t1 \<Longrightarrow> num_leaves (normalize1 t1) = num_leaves t1"
proof(induction t1)
  case (Node r xs)
  then show ?case
  proof(cases "\<forall>x. xs \<noteq> {|x|}")
    case True
    have "fcard ((\<lambda>(t,e). (normalize1 t,e)) |`| xs) = fcard xs"
      using fcard_normalize_img_if_disjoint Node.prems
      by (auto simp: wf_darcs_iff_darcs')
    moreover have "\<forall>t\<in>fst ` fset xs. num_leaves (normalize1 t) = num_leaves t"
      using Node by fastforce
    ultimately show ?thesis using Node sum_img_eq[of xs] True by force
  next
    case False
    then obtain t e where t_def: "xs = {|(t,e)|}" by auto
    show ?thesis
    proof(cases "rank (rev (root t)) < rank (rev r)")
      case True
      then show ?thesis
        using t_def num_leaves_singleton num_leaves_root[of "root t" "sucs t"] by simp
    next
      case False
      then show ?thesis
        using num_leaves_singleton t_def Node by (simp add: wf_darcs_iff_darcs')
    qed
  qed
qed

lemma num_leaves_normalize_eq[simp]: "wf_darcs t1 \<Longrightarrow> num_leaves (normalize t1) = num_leaves t1"
proof(induction t1 rule: normalize.induct)
  case (1 t)
  then have "num_leaves (normalize1 t) = num_leaves t" using num_leaves_normalize1_eq by blast
  then show ?case using 1 wf_darcs_normalize1 by (smt (verit, best) normalize.simps)
qed

lemma num_leaves_normalize1_le: "num_leaves (normalize1 t1) \<le> num_leaves t1"
proof(induction t1)
  case (Node r xs)
  then show ?case
  proof(cases "\<forall>x. xs \<noteq> {|x|}")
    case True
    have fcard_le: "fcard ((\<lambda>(t,e). (normalize1 t,e)) |`| xs) \<le> fcard xs"
      by (simp add: fcard_image_le)
    moreover have xs_le: "\<forall>t\<in>fst ` fset xs. num_leaves (normalize1 t) \<le> num_leaves t"
      using Node by fastforce
    ultimately show ?thesis using Node sum_img_le[of xs] xs_le \<open>\<forall>x. xs \<noteq> {|x|}\<close> by simp
  next
    case False
    then obtain t e where t_def: "xs = {|(t,e)|}" by auto
    show ?thesis
    proof(cases "rank (rev (root t)) < rank (rev r)")
      case True
      then show ?thesis
        using t_def num_leaves_singleton num_leaves_root[of "root t" "sucs t"] by simp
    next
      case False
      then show ?thesis using num_leaves_singleton t_def Node by simp
    qed
  qed
qed

lemma num_leaves_normalize_le: "num_leaves (normalize t1) \<le> num_leaves t1"
proof(induction t1 rule: normalize.induct)
  case (1 t)
  then have "num_leaves (normalize1 t) \<le> num_leaves t" using num_leaves_normalize1_le by blast
  then show ?case using 1 by (smt (verit) le_trans normalize.simps)
qed

lemma num_leaves_merge1_le: "num_leaves (merge1 t1) \<le> num_leaves t1"
proof(induction t1)
  case (Node r xs)
  then show ?case
  proof(cases "fcard xs > 1 \<and> (\<forall>t \<in> fst ` fset xs. max_deg t \<le> 1)")
    case True
    then have "merge1 (Node r xs) = merge (Node r xs)" by simp
    then have "num_leaves (merge1 (Node r xs)) = 1"
      unfolding merge_def using dtree_from_list_1_leaf by fastforce
    also have "\<dots> < fcard xs" using True by blast
    also have "\<dots> \<le> num_leaves (Node r xs)" using num_leaves_ge_card by fast
    finally show ?thesis by simp
  next
    case False
    have "\<forall>t \<in> fst ` fset xs. num_leaves (merge1 t) \<le> num_leaves t" using Node by force
    then show ?thesis using sum_img_le False by auto
  qed
qed

lemma num_leaves_merge1_lt: "max_deg t1 > 1 \<Longrightarrow> num_leaves (merge1 t1) < num_leaves t1"
proof(induction t1)
  case (Node r xs)
  show ?case
  proof(cases "fcard xs > 1 \<and> (\<forall>t \<in> fst ` fset xs. max_deg t \<le> 1)")
    case True
    then have "merge1 (Node r xs) = merge (Node r xs)" by simp
    then have "num_leaves (merge1 (Node r xs)) = 1"
      unfolding merge_def using dtree_from_list_1_leaf by fastforce
    also have "\<dots> < fcard xs" using True by blast
    finally show ?thesis using num_leaves_ge_card less_le_trans by fast
  next
    case False
    have 0: "xs \<noteq> {||}" using Node.prems by (metis nempty_if_mdeg_n0 not_one_less_zero)
    have 1: "\<forall>t \<in> fst ` fset xs. num_leaves (merge1 t) \<le> num_leaves t"
      using num_leaves_merge1_le by blast
    have "\<exists>t \<in> fst ` fset xs. max_deg t > 1" using Node.prems False mdeg_child_if_wedge by auto
    then have 2: "\<exists>t \<in> fst ` fset xs. num_leaves (merge1 t) < num_leaves t" using Node.IH by force
    have 3: "\<forall>t\<in>fst ` fset xs. 0 < num_leaves t"
      using num_leaves_ge1 by (metis neq0_conv not_one_le_zero)
    from False have "merge1 (Node r xs) = Node r ((\<lambda>(t,e). (merge1 t,e)) |`| xs)" by auto
    then have "num_leaves (merge1 (Node r xs))
            = (\<Sum>(t,e)\<in> fset ((\<lambda>(t,e). (merge1 t,e)) |`| xs). num_leaves t)" using 0 by auto
    then show ?thesis using 0 sum_img_lt[OF 1 2 3] by simp
  qed
qed

lemma ikkbz_num_leaves_decr:
  "max_deg t1 > 1 \<Longrightarrow> num_leaves (merge1 (normalize t1)) < num_leaves t1"
  using num_leaves_merge1_lt num_leaves_normalize_le num_leaves_1_if_mdeg_1 num_leaves_ge1
  by (metis antisym_conv2 dual_order.antisym dual_order.trans not_le_imp_less num_leaves_merge1_le)

function ikkbz_sub :: "('a list,'b) dtree \<Rightarrow> ('a list,'b) dtree" where
  "ikkbz_sub t1 = (if max_deg t1 \<le> 1 then t1 else ikkbz_sub (merge1 (normalize t1)))"
  by auto
termination using ikkbz_num_leaves_decr by(relation "measure (\<lambda>t. num_leaves t)") auto

lemma ikkbz_sub_darcs_sub: "darcs (ikkbz_sub t) \<subseteq> darcs t"
using ranked_dtree_axioms proof(induction t rule: ikkbz_sub.induct)
  case (1 t)
  show ?case
  proof(cases "max_deg t \<le> 1")
    case False
    have "darcs (merge1 (normalize t)) = darcs (normalize t)"
      using ranked_dtree.merge1_darcs_eq ranked_dtree.ranked_dtree_normalize "1.prems" by blast
    moreover have "ranked_dtree (merge1 (normalize t)) cmp"
      using ranked_dtree.ranked_dtree_normalize "1.prems" ranked_dtree.ranked_dtree_merge1 by blast
    moreover have "\<not> (max_deg t \<le> 1 \<or> \<not> list_dtree t)" using False ranked_dtree_def "1.prems" by blast
    ultimately show ?thesis using "1.IH" normalize_darcs_sub by force
  qed(simp)
qed

lemma ikkbz_sub_dlverts_eq[simp]: "dlverts (ikkbz_sub t) = dlverts t"
using ranked_dtree_axioms proof(induction t rule: ikkbz_sub.induct)
  case (1 t)
  show ?case
  proof(cases "max_deg t \<le> 1")
    case True
    then show ?thesis by simp
  next
    case False
    then show ?thesis
      using 1 ranked_dtree.merge1_dlverts_eq[of "normalize t"] normalize_dlverts_eq
      ranked_dtree.ranked_dtree_normalize ranked_dtree.ranked_dtree_merge1 ikkbz_sub.elims by metis
  qed
qed

lemma ikkbz_sub_wf_darcs: "wf_darcs (ikkbz_sub t)"
using ranked_dtree_axioms proof(induction t rule: ikkbz_sub.induct)
  case (1 t)
  then show ?case
  proof(cases "max_deg t \<le> 1")
    case True
    then show ?thesis using "1.prems" list_dtree_def ranked_dtree_def by auto
  next
    case False
    then show ?thesis
      using 1 ranked_dtree.ranked_dtree_normalize ranked_dtree.ranked_dtree_merge1
      by (metis ikkbz_sub.simps)
  qed
qed

lemma ikkbz_sub_wf_dlverts: "wf_dlverts (ikkbz_sub t)"
using ranked_dtree_axioms proof(induction t rule: ikkbz_sub.induct)
  case (1 t)
  then show ?case
  proof(cases "max_deg t \<le> 1")
    case True
    then show ?thesis using "1.prems" list_dtree_def ranked_dtree_def by auto
  next
    case False
    then show ?thesis
      using 1 ranked_dtree.ranked_dtree_normalize ranked_dtree.ranked_dtree_merge1
      by (metis ikkbz_sub.simps)
  qed
qed

theorem ikkbz_sub_list_dtree: "list_dtree (ikkbz_sub t)"
  using ikkbz_sub_wf_darcs ikkbz_sub_wf_dlverts list_dtree_def by blast

corollary ikkbz_sub_ranked_dtree: "ranked_dtree (ikkbz_sub t) cmp"
  using ikkbz_sub_list_dtree ranked_dtree_def ranked_dtree_axioms by blast

lemma ikkbz_sub_mdeg_le1: "max_deg (ikkbz_sub t1) \<le> 1"
  by (induction t1 rule: ikkbz_sub.induct) simp

corollary denormalize_ikkbz_eq_dlverts: "set (denormalize (ikkbz_sub t)) = dlverts t"
  using denormalize_set_eq_dlverts ikkbz_sub_mdeg_le1 ikkbz_sub_dlverts_eq by blast

lemma distinct_ikkbz_sub: "\<lbrakk>\<forall>v\<in>dverts t. distinct v; v\<in>dverts (ikkbz_sub t)\<rbrakk> \<Longrightarrow> distinct v"
using list_dtree_axioms proof(induction t arbitrary: v rule: ikkbz_sub.induct)
  case (1 t)
  then interpret T1: ranked_dtree t rank cmp
    using ranked_dtree_axioms by (simp add: ranked_dtree_def)
  show ?case
    using 1 T1.ranked_dtree_normalize T1.distinct_normalize ranked_dtree.merge1_dverts_eq
      ranked_dtree.wf_dlverts_merge1 ranked_dtree.wf_darcs_merge1
    by (metis ikkbz_sub.elims list_dtree_def)
qed

corollary distinct_denormalize_ikkbz_sub:
  "\<forall>v\<in>dverts t. distinct v \<Longrightarrow> distinct (denormalize (ikkbz_sub t))"
  using distinct_ikkbz_sub ikkbz_sub_wf_dlverts denormalize_distinct by blast

lemma ikkbz_sub_hd_root[simp]: "hd (root (ikkbz_sub t)) = hd (root t)"
using list_dtree_axioms proof(induction t rule: ikkbz_sub.induct)
  case (1 t)
  then interpret T1: ranked_dtree t rank cmp
    using ranked_dtree_axioms by (simp add: ranked_dtree_def)
  show ?case
    using 1 merge1_hd_root_eq ranked_dtree.axioms(1) ranked_dtree.ranked_dtree_merge1
    by (metis T1.ranked_dtree_normalize T1.wf_lverts ikkbz_sub.simps normalize_hd_root_eq')
qed

corollary denormalize_ikkbz_sub_hd_root[simp]: "hd (denormalize (ikkbz_sub t)) = hd (root t)"
  using ikkbz_sub_hd_root denormalize_hd_root
  by (metis dtree.set_sel(1) empty_notin_wf_dlverts ikkbz_sub_wf_dlverts)

end

locale precedence_graph = finite_directed_tree +
  fixes rank :: "'a list \<Rightarrow> real"
  fixes cost :: "'a list \<Rightarrow> real"
  fixes cmp :: "('a list\<times>'b) comparator"
  assumes asi_rank: "asi rank root cost"
      and cmp_antisym:
    "\<lbrakk>v1 \<noteq> []; v2 \<noteq> []; compare cmp (v1,e1) (v2,e2) = Equiv\<rbrakk> \<Longrightarrow> set v1 \<inter> set v2 \<noteq> {} \<or> e1=e2"
begin

definition to_list_dtree :: "('a list, 'b) dtree" where
  "to_list_dtree = finite_directed_tree.to_dtree to_list_tree [root]"

lemma to_list_dtree_single: "v \<in> dverts to_list_dtree \<Longrightarrow> \<exists>x. v = [x] \<and> x \<in> verts T"
  unfolding to_list_dtree_def using to_list_tree_single
  by (simp add: finite_directed_tree.dverts_eq_verts to_list_tree_finite_directed_tree)

lemma to_list_dtree_wf_dverts: "wf_dverts to_list_dtree"
  using finite_directed_tree.wf_dverts_to_dtree[OF to_list_tree_finite_directed_tree]
  by(simp add: to_list_dtree_def)

lemma to_list_dtree_wf_dlverts: "wf_dlverts to_list_dtree"
  unfolding to_list_dtree_def
  by (simp add: to_list_tree_fin_list_directed_tree fin_list_directed_tree.wf_dlverts_to_dtree)

lemma to_list_dtree_wf_darcs: "wf_darcs to_list_dtree"
  using finite_directed_tree.wf_darcs_to_dtree[OF to_list_tree_finite_directed_tree]
  by(simp add: to_list_dtree_def)

lemma to_list_dtree_list_dtree: "list_dtree to_list_dtree"
  by(simp add: list_dtree_def to_list_dtree_wf_dlverts to_list_dtree_wf_darcs)

lemma to_list_dtree_ranked_dtree: "ranked_dtree to_list_dtree cmp"
  by(auto simp: ranked_dtree_def to_list_dtree_list_dtree ranked_dtree_axioms_def dest: cmp_antisym)

interpretation t: ranked_dtree to_list_dtree by (rule to_list_dtree_ranked_dtree)

definition ikkbz_sub :: "'a list" where
  "ikkbz_sub = denormalize (t.ikkbz_sub to_list_dtree)"

lemma dverts_eq_verts_to_list_tree: "dverts to_list_dtree = pre_digraph.verts to_list_tree"
  unfolding to_list_dtree_def
  by (simp add: finite_directed_tree.dverts_eq_verts to_list_tree_finite_directed_tree)

lemma dverts_eq_verts_img: "dverts to_list_dtree = (\<lambda>x. [x]) ` verts T"
  by (simp add: dverts_eq_verts_to_list_tree to_list_tree_def)

lemma dlverts_eq_verts: "dlverts to_list_dtree = verts T"
  by (simp add: dverts_eq_verts_img dlverts_eq_dverts_union)

theorem ikkbz_set_eq_verts: "set ikkbz_sub = verts T"
  using dlverts_eq_verts ikkbz_sub_def t.denormalize_ikkbz_eq_dlverts by simp

lemma distinct_to_list_tree: "\<forall>v\<in>verts to_list_tree. distinct v"
  unfolding to_list_tree_def by simp

lemma distinct_to_list_dtree: "\<forall>v\<in>dverts to_list_dtree. distinct v"
  using distinct_to_list_tree dverts_eq_verts_to_list_tree by blast

theorem distinct_ikkbz_sub: "distinct ikkbz_sub"
  unfolding ikkbz_sub_def
  using distinct_to_list_dtree t.distinct_denormalize_ikkbz_sub by blast

lemma to_list_dtree_root_eq_root: "Dtree.root (to_list_dtree) = [root]"
  unfolding to_list_dtree_def
  by (simp add: finite_directed_tree.to_dtree_root_eq_root to_list_tree_finite_directed_tree)

lemma to_list_dtree_hd_root_eq_root[simp]: "hd (Dtree.root to_list_dtree) = root"
  by (simp add: to_list_dtree_root_eq_root)

theorem ikkbz_sub_hd_eq_root[simp]: "hd ikkbz_sub = root"
  unfolding ikkbz_sub_def using t.denormalize_ikkbz_sub_hd_root to_list_dtree_root_eq_root by simp

end

subsection \<open>Full IKKBZ\<close>

locale tree_query_graph = undir_tree_todir G + query_graph G for G

locale cmp_tree_query_graph = tree_query_graph +
  fixes cmp :: "('a list\<times>'b) comparator"
  assumes cmp_antisym:
    "\<lbrakk>v1 \<noteq> []; v2 \<noteq> []; compare cmp (v1,e1) (v2,e2) = Equiv\<rbrakk> \<Longrightarrow> set v1 \<inter> set v2 \<noteq> {} \<or> e1=e2"

locale ikkbz_query_graph = cmp_tree_query_graph +
  fixes cost :: "'a joinTree \<Rightarrow> real"
  fixes cost_r :: "'a \<Rightarrow> ('a list \<Rightarrow> real)"
  fixes rank_r :: "'a \<Rightarrow> ('a list \<Rightarrow> real)"
  assumes asi_rank: "r \<in> verts G \<Longrightarrow> asi (rank_r r) r (cost_r r)"
      and cost_correct:
        "\<lbrakk>valid_tree t; no_cross_products t; left_deep t\<rbrakk>
          \<Longrightarrow> cost_r (first_node t) (revorder t) = cost t"
begin

abbreviation ikkbz_sub :: "'a \<Rightarrow> 'a list" where
  "ikkbz_sub r \<equiv> precedence_graph.ikkbz_sub (dir_tree_r r) r (rank_r r) cmp"

abbreviation cost_l :: "'a list \<Rightarrow> real" where
  "cost_l xs \<equiv> cost (create_ldeep xs)"

lemma precedence_graph_r:
  "r \<in> verts G \<Longrightarrow> precedence_graph (dir_tree_r r) r (rank_r r) (cost_r r) cmp"
  using fin_directed_tree_r cmp_antisym
  by (simp add: precedence_graph_def precedence_graph_axioms_def asi_rank)

lemma nempty_if_set_eq_verts: "set xs = verts G \<Longrightarrow> xs \<noteq> []"
  using verts_nempty by force

lemma revorder_if_set_eq_verts: "set xs = verts G \<Longrightarrow> revorder (create_ldeep xs) = rev xs"
  using nempty_if_set_eq_verts create_ldeep_order unfolding revorder_eq_rev_inorder by blast

lemma cost_correct':
  "\<lbrakk>set xs = verts G; distinct xs; no_cross_products (create_ldeep xs)\<rbrakk>
    \<Longrightarrow> cost_r (hd xs) (rev xs) = cost_l xs"
  using cost_correct[of "create_ldeep xs"] revorder_if_set_eq_verts create_ldeep_ldeep[of xs]
  unfolding valid_tree_def distinct_relations_def
  by (simp add: create_ldeep_order create_ldeep_relations first_node_eq_hd nempty_if_set_eq_verts)

lemma ikkbz_sub_verts_eq: "r \<in> verts G \<Longrightarrow> set (ikkbz_sub r) = verts G"
  using precedence_graph.ikkbz_set_eq_verts precedence_graph_r verts_dir_tree_r_eq by fast

lemma ikkbz_sub_distinct: "r \<in> verts G \<Longrightarrow> distinct (ikkbz_sub r)"
  using precedence_graph.distinct_ikkbz_sub precedence_graph_r by fast

lemma ikkbz_sub_hd_eq_root: "r \<in> verts G \<Longrightarrow> hd (ikkbz_sub r) = r"
  using precedence_graph.ikkbz_sub_hd_eq_root precedence_graph_r by fast

definition ikkbz :: "'a list" where
  "ikkbz \<equiv> arg_min_on cost_l {ikkbz_sub r|r. r \<in> verts G}"

lemma ikkbz_sub_set_fin: "finite {ikkbz_sub r|r. r \<in> verts G}"
  by simp

lemma ikkbz_sub_set_nempty: "{ikkbz_sub r|r. r \<in> verts G} \<noteq> {}"
  by (simp add: verts_nempty)

lemma ikkbz_in_ikkbz_sub_set: "ikkbz \<in> {ikkbz_sub r|r. r \<in> verts G}"
  unfolding ikkbz_def using ikkbz_sub_set_fin ikkbz_sub_set_nempty arg_min_if_finite by blast

lemma ikkbz_eq_ikkbz_sub: "\<exists>r \<in> verts G. ikkbz = ikkbz_sub r"
  using ikkbz_in_ikkbz_sub_set by blast

lemma ikkbz_min_ikkbz_sub: "r \<in> verts G \<Longrightarrow> cost_l ikkbz \<le> cost_l (ikkbz_sub r)"
  unfolding ikkbz_def using ikkbz_sub_set_fin arg_min_least by fast

lemma ikkbz_distinct: "distinct ikkbz"
  using ikkbz_eq_ikkbz_sub ikkbz_sub_distinct by fastforce

lemma ikkbz_set_eq_verts: "set ikkbz = verts G"
  using ikkbz_eq_ikkbz_sub ikkbz_sub_verts_eq by force

lemma ikkbz_nempty: "ikkbz \<noteq> []"
  using ikkbz_set_eq_verts verts_nempty by fastforce

lemma ikkbz_hd_in_verts: "hd ikkbz \<in> verts G"
  using ikkbz_nempty ikkbz_set_eq_verts by fastforce

lemma inorder_ikkbz: "inorder (create_ldeep ikkbz) = ikkbz"
  using create_ldeep_order ikkbz_nempty by blast

lemma inorder_ikkbz_distinct: "distinct (inorder (create_ldeep ikkbz))"
  using ikkbz_distinct inorder_ikkbz by simp

lemma inorder_relations_eq_verts: "relations (create_ldeep ikkbz) = verts G"
  using ikkbz_set_eq_verts create_ldeep_relations ikkbz_nempty by blast

theorem ikkbz_valid_tree: "valid_tree (create_ldeep ikkbz)"
  unfolding valid_tree_def distinct_relations_def
  using inorder_ikkbz_distinct inorder_relations_eq_verts by blast

end

(* non commutative merging based on inserting (INCOMPLETE) *)

locale old = list_dtree t for t :: "('a list,'b) dtree" +
  fixes rank :: "'a list \<Rightarrow> real"
begin

function find_pos_aux :: "'a list \<Rightarrow> 'a list \<Rightarrow> ('a list,'b) dtree \<Rightarrow> ('a list \<times> 'a list)" where
  "find_pos_aux v p (Node r {|(t1,_)|}) =
    (if rank (rev v) \<le> rank (rev r) then (p,r) else find_pos_aux v r t1)"
| "\<forall>x. xs \<noteq> {|x|} \<Longrightarrow> find_pos_aux v p (Node r xs) =
    (if rank (rev v) \<le> rank (rev r) then (p,r) else (r,r))"
  by (metis combine.cases old.prod.exhaust) auto
termination by lexicographic_order

function find_pos :: "'a list \<Rightarrow> ('a list,'b) dtree \<Rightarrow> ('a list \<times> 'a list)" where
  "find_pos v (Node r {|(t1,_)|}) = find_pos_aux v r t1"
| "\<forall>x. xs \<noteq> {|x|} \<Longrightarrow> find_pos v (Node r xs) = (r,r)"
  by (metis dtree.exhaust surj_pair) auto
termination by lexicographic_order

abbreviation insert_chain :: "('a list\<times>'b) list \<Rightarrow> ('a list,'b) dtree \<Rightarrow> ('a list,'b) dtree" where
  "insert_chain xs t1 \<equiv>
    foldr (\<lambda>(v,e) t2. case find_pos v t2 of (x,y) \<Rightarrow> insert_between v e x y t2) xs t1"

fun merge :: "('a list,'b) dtree \<Rightarrow> ('a list,'b) dtree" where
  "merge (Node r xs) = ffold (\<lambda>(t,e) b. case b of Node r xs \<Rightarrow>
      if xs = {||} then Node r {|(t,e)|} else insert_chain (dtree_to_list t) b)
    (Node r {||}) xs"

lemma ffold_if_False_eq_acc:
  "\<lbrakk>\<forall>a. \<not>P a; comp_fun_commute (\<lambda>a b. if \<not>P a then b else Q a b)\<rbrakk>
    \<Longrightarrow> ffold (\<lambda>a b. if \<not>P a then b else Q a b) acc xs = acc"
proof(induction xs)
  case (insert x xs)
  let ?f = "\<lambda>a b. if \<not>P a then b else Q a b"
  have "ffold ?f acc (finsert x xs) = ?f x (ffold ?f acc xs)"
    using insert.hyps by (simp add: comp_fun_commute.ffold_finsert insert.prems(2))
  then have "ffold ?f acc (finsert x xs) = ffold ?f acc xs" using insert.prems by simp
  then show ?case using insert.IH insert.prems by simp
qed(simp add: comp_fun_commute.ffold_empty)

lemma find_pos_rank_less: "rank (rev v) \<le> rank (rev r) \<Longrightarrow> find_pos_aux v p (Node r xs) = (p,r)"
  by(cases "\<exists>x. xs = {|x|}") auto

lemma find_pos_y_in_dverts: "(x,y) = find_pos_aux v p t1 \<Longrightarrow> y \<in> dverts t1"
proof(induction t1 arbitrary: p)
  case (Node r xs)
  then show ?case
  proof(cases "rank (rev v) \<le> rank (rev r)")
    case True
    then show ?thesis using Node.prems by(cases "\<exists>x. xs = {|x|}") auto
  next
    case False
    then show ?thesis using Node by(cases "\<exists>x. xs = {|x|}") fastforce+
  qed
qed

lemma find_pos_x_in_dverts: "(x,y) = find_pos_aux v p t1 \<Longrightarrow> x \<in> dverts t1 \<or> p=x"
proof(induction t1 arbitrary: p)
  case (Node r xs)
  then show ?case
  proof(cases "rank (rev v) \<le> rank (rev r)")
    case True
    then show ?thesis using Node.prems by(cases "\<exists>x. xs = {|x|}") auto
  next
    case False
    then show ?thesis using Node by(cases "\<exists>x. xs = {|x|}") fastforce+
  qed
qed

end

end