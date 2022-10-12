(* Author: Bernhard Stöckl *)

theory IKKBZ_Examples
  imports IKKBZ_Optimality
begin

section \<open>Examples of Applying IKKBZ\<close>

subsection \<open>Computing Contributing Selectivity without Lists\<close>

context directed_tree
begin

definition contr_sel :: "'a selectivity \<Rightarrow> 'a \<Rightarrow> real" where
  "contr_sel sel y = (if \<exists>x. x \<rightarrow>\<^bsub>T\<^esub> y then sel (THE x. x \<rightarrow>\<^bsub>T\<^esub> y) y else 1)"

definition tree_sel :: "'a selectivity \<Rightarrow> bool" where
  "tree_sel sel = (\<forall>x y. \<not>(x \<rightarrow>\<^bsub>T\<^esub> y \<or> y \<rightarrow>\<^bsub>T\<^esub> x) \<longrightarrow> sel x y = 1)"

lemma contr_sel_gt0: "sel_reasonable sf \<Longrightarrow> contr_sel sf x > 0"
  unfolding contr_sel_def sel_reasonable_def by simp

lemma contr_sel_le1: "sel_reasonable sf \<Longrightarrow> contr_sel sf x \<le> 1"
  unfolding contr_sel_def sel_reasonable_def by simp

lemma nempty_if_not_fwd_conc: "\<not>forward_arcs (y#xs) \<Longrightarrow> xs \<noteq> []"
  by auto

lemma len_gt1_if_not_fwd_conc: "\<not>forward_arcs (y#xs) \<Longrightarrow> length (y#xs) > 1"
  by auto

lemma two_elems_if_not_fwd_conc: "\<not>forward_arcs (y#xs) \<Longrightarrow> \<exists>a b cs. a # b # cs = y#xs"
  by (metis forward_arcs.cases forward_arcs.simps(2))

lemma hd_reach_all_if_nfwd_app_fwd:
  "\<lbrakk>\<not>forward_arcs (y#xs); forward_arcs (y#ys@xs); x \<in> set (y#ys@xs)\<rbrakk>
    \<Longrightarrow> hd (rev (y#ys@xs)) \<rightarrow>\<^sup>*\<^bsub>T\<^esub> x"
  using hd_reach_all_forward'[of "rev (y#ys@xs)"] len_gt1_if_not_fwd_conc forward_arcs_alt by auto

lemma hd_not_y_if_if_nfwd_app_fwd:
  assumes "\<not>forward_arcs (y#xs)" and "forward_arcs (y#ys@xs)"
  shows "hd (rev (y#ys@xs)) \<noteq> y"
proof -
  obtain a where a_def: "a \<in> set (ys@xs)" "a \<rightarrow>\<^bsub>T\<^esub> y"
    by (metis assms Nil_is_append_conv forward_arcs.simps(3) neq_Nil_conv)
  then have "hd (rev (y#ys@xs)) \<rightarrow>\<^sup>*\<^bsub>T\<^esub> a" using hd_reach_all_if_nfwd_app_fwd[OF assms] by simp
  then show ?thesis
    using a_def(2) reachable1_not_reverse
    by (metis loopfree.adj_not_same reachable_adjI reachable_neq_reachable1)
qed

lemma hd_reach1_y_if_nfwd_app_fwd:
  "\<lbrakk>\<not>forward_arcs (y#xs); forward_arcs (y#ys@xs)\<rbrakk> \<Longrightarrow> hd (rev (y#ys@xs)) \<rightarrow>\<^sup>+\<^bsub>T\<^esub> y"
  using hd_not_y_if_if_nfwd_app_fwd hd_reach_all_if_nfwd_app_fwd by auto

lemma not_fwd_if_skip1:
  "\<lbrakk>\<not> forward_arcs (y#x#x'#xs); forward_arcs (x#x'#xs)\<rbrakk> \<Longrightarrow> \<not> forward_arcs (y#x'#xs)"
  by auto

lemma fwd_arcs_conc_nlast_elem:
  assumes "forward_arcs xs" and "y \<in> set xs" and "y \<noteq> last xs"
  shows "forward_arcs (y#xs)"
proof -
  obtain as bs where as_def: "as @ y # bs = xs" "bs \<noteq> []"
    using split_list_not_last[OF assms(2,3)] by blast
  then have "forward_arcs (y#bs)" using assms(1) forward_arcs_split by blast
  then obtain x where x_def: "x \<in> set bs" "x \<rightarrow>\<^bsub>T\<^esub> y"
    using as_def(2) by (force intro: list.exhaust)
  then have "x \<in> set xs" using as_def(1) by auto
  then show ?thesis using assms(1) x_def(2) forward_arcs.elims(3) by blast
qed

lemma fwd_app_nhead_elem: "\<lbrakk>forward xs; y \<in> set xs; y \<noteq> hd xs\<rbrakk> \<Longrightarrow> forward (xs@[y])"
  using fwd_arcs_conc_nlast_elem forward_arcs_alt by (simp add: last_rev)

lemma hd_last_not_fwd_arcs: "\<not>forward_arcs (x#xs@[x])"
proof
  assume asm: "forward_arcs (x#xs@[x])"
  then obtain y where y_def: "y \<in> set (xs@[x])" "y \<rightarrow>\<^bsub>T\<^esub> x"
    by (metis append_is_Nil_conv forward_arcs.simps(3) no_back_arcs.cases)
  then have hd_in_verts: "hd (rev (xs @ [x])) \<in> verts T" by auto
  have "forward_arcs (xs@[x])" using asm forward_arcs_split[of "[x]" "xs@[x]"] by simp
  then have "x \<rightarrow>\<^sup>*\<^bsub>T\<^esub> y" using hd_reach_all_forward[OF hd_in_verts] y_def forward_arcs_alt by simp
  then show False using y_def(2) reachable1_not_reverse by auto
qed

lemma hd_not_fwd_arcs: "\<not>forward_arcs (ys@x#xs@[x])"
  using hd_last_not_fwd_arcs forward_arcs_split by blast

lemma hd_last_not_fwd: "\<not>forward (x#xs@[x])"
  using hd_last_not_fwd_arcs forward_arcs_alt by simp

lemma hd_not_fwd: "\<not>forward (x#xs@[x]@ys)"
  using hd_not_fwd_arcs forward_arcs_alt by simp

lemma y_not_dom_if_nfwd_app_fwd:
  "\<lbrakk>\<not>forward_arcs (y#xs); forward_arcs (y#ys@xs); x \<in> set xs\<rbrakk> \<Longrightarrow> \<not> x \<rightarrow>\<^bsub>T\<^esub> y"
  using forward_arcs_split[of "y#ys" xs] two_elems_if_not_fwd_conc by force

lemma not_y_dom_if_nfwd_app_fwd:
  "\<lbrakk>\<not>forward_arcs (y#xs); forward_arcs (y#ys@xs); x \<in> set xs\<rbrakk> \<Longrightarrow> \<not> y \<rightarrow>\<^bsub>T\<^esub> x"
  by (smt (verit, ccfv_threshold) append_is_Nil_conv forward_arcs_alt' forward_arcs_split
      forward_cons fwd_app_nhead_elem hd_append hd_reach1_y_if_nfwd_app_fwd
      hd_reachable1_from_outside' list.distinct(1) reachable1_not_reverse reachable_adjI
      reachable_neq_reachable1 rev.simps(2) rev_append set_rev split_list)

lemma list_sel_aux'1_if_tree_sel_nfwd:
  "\<lbrakk>tree_sel sel; \<not>forward_arcs (y#xs); forward_arcs (y#ys@xs)\<rbrakk>
    \<Longrightarrow> list_sel_aux' sel xs y = 1"
proof(induction xs arbitrary: ys rule: forward_arcs.induct)
  case (2 x)
  then show ?case using not_y_dom_if_nfwd_app_fwd[OF 2(2,3)] by (auto simp: tree_sel_def)
next
  case (3 x x' xs)
  then have "forward_arcs (x # x' # xs)"
    using forward_arcs_split[of "y#ys" "x#x'#xs"] by simp
  then have "\<not> forward_arcs (y # x' # xs)" using not_fwd_if_skip1 "3.prems"(2) by blast
  moreover have "forward_arcs (y # (ys@[x]) @ x' # xs)" using 3 by simp
  ultimately have "list_sel_aux' sel (x' # xs) y = 1" using "3.IH"[OF "3.prems"(1)] by blast
  then show ?case
    using "3.prems"(1) y_not_dom_if_nfwd_app_fwd[OF "3.prems"(2,3)]
      not_y_dom_if_nfwd_app_fwd[OF "3.prems"(2,3)]
    by (simp add: tree_sel_def)
qed(simp)

lemma contr_sel_eq_list_sel_aux'_if_tree_sel:
  "\<lbrakk>tree_sel sel; distinct (y#xs); forward_arcs (y#xs); xs \<noteq> []\<rbrakk>
    \<Longrightarrow> contr_sel sel y = list_sel_aux' sel xs y"
proof(induction xs rule: forward_arcs.induct)
  case (2 x)
  then have "x \<rightarrow>\<^bsub>T\<^esub> y" by simp
  then have "(THE x. x \<rightarrow>\<^bsub>T\<^esub> y) = x" using two_in_arcs_contr by blast
  then show ?case using \<open>x \<rightarrow>\<^bsub>T\<^esub> y\<close> unfolding contr_sel_def by auto
next
  case (3 x x' xs)
  then show ?case
  proof(cases "x \<rightarrow>\<^bsub>T\<^esub> y")
    case True
    then have "(THE x. x \<rightarrow>\<^bsub>T\<^esub> y) = x" using two_in_arcs_contr by blast
    then have contr_sel: "contr_sel sel y = sel x y" using True unfolding contr_sel_def by auto
    have "\<not>forward_arcs (y#x'#xs)" using True "3.prems"(2) two_in_arcs_contr by auto
    then have "list_sel_aux' sel (x'#xs) y = 1"
      using list_sel_aux'1_if_tree_sel_nfwd[of sel y "x'#xs" "[x]"] "3.prems"(1,3) by auto
    then show ?thesis using contr_sel by simp
  next
    case False
    have "\<not>y \<rightarrow>\<^bsub>T\<^esub> x"
      using "3.prems"(2,3) forward_arcs_alt' no_back_arc_if_fwd_dstct
      by (metis distinct_rev list.set_intros(1) rev.simps(2) set_rev)
    then have "sel x y = 1" using "3.prems"(1) False unfolding tree_sel_def by blast
    then show ?thesis using 3 False by simp
  qed
qed(simp)

corollary contr_sel_eq_list_sel_aux'_if_tree_sel':
  "\<lbrakk>tree_sel sel; distinct (xs@[y]); forward (xs@[y]); xs \<noteq> []\<rbrakk>
    \<Longrightarrow> contr_sel sel y = list_sel_aux' sel (rev xs) y"
  by (simp add: contr_sel_eq_list_sel_aux'_if_tree_sel forward_arcs_alt)

corollary contr_sel_eq_list_sel_aux'_if_tree_sel'':
  "\<lbrakk>tree_sel sel; distinct (xs@[y]); forward (xs@[y]); xs \<noteq> []\<rbrakk>
    \<Longrightarrow> contr_sel sel y = list_sel_aux' sel xs y"
  by (simp add: contr_sel_eq_list_sel_aux'_if_tree_sel' mset_x_eq_list_sel_aux'_eq[of "rev xs"])

lemma contr_sel_root[simp]: "contr_sel sel root = 1"
  by (auto simp: contr_sel_def dest: dominated_not_root)

lemma contr_sel_notvert[simp]: "v \<notin> verts T \<Longrightarrow> contr_sel sel v = 1"
  by (auto simp: contr_sel_def)

lemma hd_reach_all_forward_verts:
  "\<lbrakk>forward xs; set xs = verts T; v \<in> verts T\<rbrakk> \<Longrightarrow> hd xs \<rightarrow>\<^sup>*\<^bsub>T\<^esub> v"
  using hd_reach_all_forward list.set_sel(1)[of xs] by force

lemma hd_eq_root_if_forward_verts: "\<lbrakk>forward xs; set xs = verts T\<rbrakk> \<Longrightarrow> hd xs = root"
  using hd_reach_all_forward_verts root_if_all_reach by simp

lemma contr_sel_eq_ldeep_s_if_tree_dst_fwd_verts:
  assumes "tree_sel sel" and "distinct xs" and "forward xs" and "set xs = verts T"
  shows "contr_sel sel y = ldeep_s sel (rev xs) y"
proof -
  have hd_root: "hd xs = root" using hd_eq_root_if_forward_verts assms(3,4) by blast
  consider "y \<in> set xs" "y = root" | "y \<in> set xs" "y \<noteq> root" | "y \<notin> set xs" by blast
  then show ?thesis
  proof(cases)
    case 1
    then show ?thesis using hd_root ldeep_s_revhd1_if_distinct assms(2) by auto
  next
    case 2
    then obtain as bs where as_def: "as @ y # bs = xs" using split_list[of y] by fastforce
    then have "forward (as@[y])" using assms(3) forward_split[of "as@[y]"] by auto
    moreover have "distinct (as@[y])" using assms(2) as_def by auto
    moreover have "as \<noteq> []" using 2 hd_root as_def by fastforce
    ultimately have "contr_sel sel y = list_sel_aux' sel (rev as) y"
      using contr_sel_eq_list_sel_aux'_if_tree_sel'[OF assms(1)] by blast
    then show ?thesis using as_def distinct_ldeep_s_eq_aux'[of "rev xs"] assms(2) by auto
  next
    case 3
    then have "contr_sel sel y = 1" using assms(4) by simp
    then show ?thesis using 3 ldeep_s_1_if_nelem set_rev by fastforce
  qed
qed

corollary contr_sel_eq_ldeep_s_if_tree_dst_fwd_verts':
  "\<lbrakk>tree_sel sel; distinct xs; forward xs; set xs = verts T\<rbrakk>
    \<Longrightarrow> contr_sel sel = ldeep_s sel (rev xs)"
  using contr_sel_eq_ldeep_s_if_tree_dst_fwd_verts by blast

lemma add_leaf_forward_arcs_preserv:
  "\<lbrakk>a \<notin> arcs T; u \<in> verts T; v \<notin> verts T; forward_arcs xs\<rbrakk>
    \<Longrightarrow> directed_tree.forward_arcs \<lparr>verts = verts T \<union> {v}, arcs = arcs T \<union> {a},
              tail = (tail T)(a := u), head = (head T)(a := v)\<rparr> xs"
proof(induction xs rule: forward_arcs.induct)
  case 1
  then show ?case using directed_tree.forward_arcs.simps(1) add_leaf_dir_tree by fast
next
  case (2 x)
  then show ?case using directed_tree.forward_arcs.simps(2) add_leaf_dir_tree by fast
next
  case (3 x y xs)
  let ?T = "\<lparr>verts = verts T \<union> {v}, arcs = arcs T \<union> {a},
            tail = (tail T)(a := u), head = (head T)(a := v)\<rparr>"
  interpret T: directed_tree ?T root using add_leaf_dir_tree[OF "3.prems"(1-3)] by blast
  have "T.forward_arcs (y # xs)" using 3 by fastforce
  then show ?case
    using T.forward_arcs.simps(3)[of x y xs] add_leaf_dom_preserv "3.prems"(1,4) by fastforce
qed

end

subsection \<open>Contributing Selectivity Satisfies ASI Property\<close>

context finite_directed_tree
begin

lemma dst_fwd_arcs_all_verts_ex: "\<exists>xs. forward_arcs xs \<and> distinct xs \<and> set xs = verts T"
using finite_verts proof(induction rule: finite_directed_tree_induct)
  case (single_vert t h root)
  then show ?case using directed_tree.forward_arcs.simps(2)[OF dir_tree_single] by fastforce
next
  case (add_leaf T' V A t h u root a v)
  define T where "T \<equiv> \<lparr>verts = V \<union> {v}, arcs = A \<union> {a}, tail = t(a := u), head = h(a := v)\<rparr>"
  interpret T': directed_tree T' root using add_leaf.hyps(3) by blast
  interpret T: directed_tree T root using add_leaf.hyps(1,4-6) T'.add_leaf_dir_tree T_def by simp
  obtain xs where xs_def: "T'.forward_arcs xs" "distinct xs" "set xs = verts T'"
    using add_leaf.IH by blast
  then have "T.forward_arcs xs"
    using T'.add_leaf_forward_arcs_preserv add_leaf.hyps(1,4,5,6) T_def by simp
  moreover have "\<exists>y\<in>set xs. y \<rightarrow>\<^bsub>T\<^esub> v"
    using add_leaf.hyps(1,4) T_def xs_def(3) unfolding arcs_ends_def arc_to_ends_def by force
  ultimately have "T.forward_arcs (v#xs)" using T.forward_arcs.elims(3) by blast
  then show ?case using xs_def(2,3) add_leaf.hyps(1,5) T_def by auto
qed

lemma dst_fwd_all_verts_ex: "\<exists>xs. forward xs \<and> distinct xs \<and> set xs = verts T"
  using dst_fwd_arcs_all_verts_ex forward_arcs_alt'[symmetric] by auto

lemma c_list_asi_if_tree_sel:
  fixes sf cf h r
  defines "rank \<equiv> (\<lambda>l. (ldeep_T (contr_sel sf) cf l - 1) / c_list (contr_sel sf) cf h r l)"
  assumes "tree_sel sf"
      and "sel_reasonable sf"
      and "\<forall>x. cf x > 0"
      and "\<forall>x. h x > 0"
    shows "asi rank r (c_list (contr_sel sf) cf h r)"
  using c_list_asi assms contr_sel_eq_ldeep_s_if_tree_dst_fwd_verts' dst_fwd_all_verts_ex
  by fastforce

end

context tree_query_graph
begin

abbreviation sel_r :: "'a \<Rightarrow> 'a \<Rightarrow> real" where
  "sel_r r \<equiv> directed_tree.contr_sel (dir_tree_r r) match_sel"

text \<open>
  Since cf is only required to be positive for verts of G, we map all others to 1.
\<close>

definition cf' :: "'a \<Rightarrow> real" where
  "cf' x = (if x \<in> verts G then cf x else 1)"

definition c_list_r  :: "('a \<Rightarrow> real) \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> real" where
  "c_list_r h r = c_list (sel_r r) cf' h r"

definition rank_r  :: "('a \<Rightarrow> real) \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> real" where
  "rank_r h r xs = (ldeep_T (sel_r r) cf' xs - 1) / c_list_r h r xs"

lemma dom_in_dir_tree_r:
  assumes "r \<in> verts G" and "x \<rightarrow>\<^bsub>G\<^esub> y"
  shows "x \<rightarrow>\<^bsub>dir_tree_r r\<^esub> y \<or> y \<rightarrow>\<^bsub>dir_tree_r r\<^esub> x"
proof -
  obtain e1 where e1_def: "e1 \<in> arcs G" "tail G e1 = x" "head G e1 = y"
    using assms(2) unfolding arcs_ends_def arc_to_ends_def by blast
  then show ?thesis
  proof(cases "e1 \<in> arcs (dir_tree_r r)")
    case True
    moreover have "tail (dir_tree_r r) e1 = x"
      using e1_def(2) tail_dir_tree_r_eq[OF assms(1)] by blast
    moreover have "head (dir_tree_r r) e1 = y"
      using e1_def(3) head_dir_tree_r_eq[OF assms(1)] by blast
    ultimately show ?thesis using e1_def(1) unfolding arcs_ends_def arc_to_ends_def by blast
  next
    case False
    then obtain e2 where e2_def: "e2 \<in> arcs (dir_tree_r r)" "tail G e2 = y" "head G e2 = x"
      using arcs_compl_un_eq_arcs[OF assms(1)] e1_def by force
    have "tail (dir_tree_r r) e2 = y"
      using e2_def(2) tail_dir_tree_r_eq[OF assms(1)] by blast
    moreover have "head (dir_tree_r r) e2 = x"
      using e2_def(3) head_dir_tree_r_eq[OF assms(1)] by blast
    ultimately show ?thesis using e2_def(1) unfolding arcs_ends_def arc_to_ends_def by blast
  qed
qed

lemma dom_in_dir_tree_r_iff_aux:
  "r \<in> verts G \<Longrightarrow> (x \<rightarrow>\<^bsub>dir_tree_r r\<^esub> y \<or> y \<rightarrow>\<^bsub>dir_tree_r r\<^esub> x) \<longleftrightarrow> (x \<rightarrow>\<^bsub>G\<^esub> y \<or> y \<rightarrow>\<^bsub>G\<^esub> x)"
  using dir_tree_r_dom_in_G dom_in_dir_tree_r by blast

lemma dom_in_dir_tree_r_iff:
  "r \<in> verts G \<Longrightarrow> (x \<rightarrow>\<^bsub>dir_tree_r r\<^esub> y \<or> y \<rightarrow>\<^bsub>dir_tree_r r\<^esub> x) \<longleftrightarrow> x \<rightarrow>\<^bsub>G\<^esub> y"
  using dom_in_dir_tree_r_iff_aux dominates_sym by blast

lemma dir_tree_sel[intro]: "r \<in> verts G \<Longrightarrow> directed_tree.tree_sel (dir_tree_r r) match_sel"
  unfolding directed_tree.tree_sel_def[OF directed_tree_r]
  using match_sel1_if_no_arc dom_in_dir_tree_r_iff by blast

lemma pos_cards'[intro!]: "\<forall>x. cf' x > 0"
  unfolding cf'_def using pos_cards by simp

theorem c_list_asi: "\<lbrakk>r \<in> verts G; \<forall>x. h x > 0\<rbrakk> \<Longrightarrow> asi (rank_r h r) r (c_list_r h r)"
  using finite_directed_tree.c_list_asi_if_tree_sel[OF fin_directed_tree_r]
  unfolding c_list_r_def rank_r_def by blast

subsection \<open>Applying IKKBZ\<close>

lemma cf'_simp: "x \<in> verts G \<Longrightarrow> cf' x = cf x"
  unfolding cf'_def by simp

lemma ldeep_T_cf'_eq: "set xs \<subseteq> verts G \<Longrightarrow> ldeep_T sf cf' xs = ldeep_T sf cf xs"
  using ldeep_T_eq_if_cf_eq[of xs] cf'_simp by blast

lemma clist_cf'_eq: "set xs \<subseteq> verts G \<Longrightarrow> c_list sf cf' h r xs = c_list sf cf h r xs"
  by (simp add: clist_eq_if_cf_eq ldeep_T_cf'_eq)

lemma card_cf'_eq: "matching_rels t \<Longrightarrow> card cf' f t = card cf f t"
  by (induction cf' f t rule: card.induct) (auto simp: matching_rels_def cf'_simp)

lemma c_IKKBZ_cf'_eq: "matching_rels t \<Longrightarrow> c_IKKBZ h cf' sf t = c_IKKBZ h cf sf t"
  by (induction h cf' sf t rule: c_IKKBZ.induct) (auto simp: card_cf'_eq cf'_simp matching_rels_def)

lemma c_IKKBZ_cf'_eq': "valid_tree t \<Longrightarrow> c_IKKBZ h cf' sf t = c_IKKBZ h cf sf t"
  by (simp add: c_IKKBZ_cf'_eq matching_rels_def valid_tree_def)

lemma c_out_cf'_eq: "matching_rels t \<Longrightarrow> c_out cf' sf t = c_out cf sf t"
  by (induction cf' sf t rule: c_out.induct) (auto simp: card_cf'_eq cf'_simp matching_rels_def)

lemma c_out_cf'_eq': "valid_tree t \<Longrightarrow> c_out cf' sf t = c_out cf sf t"
  by (simp add: c_out_cf'_eq matching_rels_def valid_tree_def)

lemma joinTree_card'_pos[intro]: "pos_rel_cards cf' t"
  by (induction t) (auto simp: pos_cards' pos_rel_cards_def)

lemma match_reasonable_cards'[intro]: "reasonable_cards cf' match_sel t"
  using pos_sel_reason_impl_reason by blast

lemma sel_r_gt0: "r \<in> verts G \<Longrightarrow> sel_r r x > 0"
  using directed_tree.contr_sel_gt0[OF directed_tree_r] by blast

lemma sel_r_le1: "r \<in> verts G \<Longrightarrow> sel_r r x \<le> 1"
  using directed_tree.contr_sel_le1[OF directed_tree_r] by blast

lemma sel_r_eq_ldeep_s_if_dst_fwd_verts:
  "\<lbrakk>r \<in> verts G; distinct xs; directed_tree.forward (dir_tree_r r) xs; set xs = verts G\<rbrakk>
    \<Longrightarrow> sel_r r = ldeep_s match_sel (rev xs)"
  using directed_tree.contr_sel_eq_ldeep_s_if_tree_dst_fwd_verts'[OF directed_tree_r]
    verts_dir_tree_r_eq
  by blast

lemma sel_r_eq_ldeep_s_if_valid_fwd:
  "\<lbrakk>r \<in> verts G; valid_tree t; directed_tree.forward (dir_tree_r r) (inorder t)\<rbrakk>
    \<Longrightarrow> sel_r r = ldeep_s match_sel (revorder t)"
  unfolding valid_tree_def distinct_relations_def inorder_eq_set[symmetric] revorder_eq_rev_inorder
  using sel_r_eq_ldeep_s_if_dst_fwd_verts by blast

lemma sel_r_eq_ldeep_s_if_valid_no_cross:
  "\<lbrakk>valid_tree t; no_cross_products t; left_deep t\<rbrakk>
    \<Longrightarrow> sel_r (first_node t) = ldeep_s match_sel (revorder t)"
  using sel_r_eq_ldeep_s_if_valid_fwd forward_if_ldeep_no_cross'
    valid_tree_def first_node_in_verts_if_valid
  by blast

lemma c_list_ldeep_s_eq_c_list_r_if_valid_no_cross:
  "\<lbrakk>valid_tree t; no_cross_products t; left_deep t\<rbrakk>
    \<Longrightarrow> c_list (ldeep_s match_sel (revorder t)) cf' h (first_node t) xs
      = c_list_r h (first_node t) xs"
  using sel_r_eq_ldeep_s_if_valid_no_cross c_list_r_def by simp

lemma c_IKKBZ_list_correct_if_simple_h:
  assumes "valid_tree t" and "no_cross_products t" and "left_deep t"
  shows "c_list_r (\<lambda>x. h x (cf' x)) (first_node t) (revorder t) = c_IKKBZ h cf match_sel t"
proof -
  have "(\<lambda>t. c_IKKBZ h cf' match_sel t) t
      = c_list (ldeep_s match_sel (revorder t)) cf' (\<lambda>x. h x (cf' x)) (first_node t) (revorder t)"
    using c_IKKBZ_eq_c_list assms(1,3) valid_tree_def by fast
  then show ?thesis
    using c_list_ldeep_s_eq_c_list_r_if_valid_no_cross assms by (simp add: c_IKKBZ_cf'_eq')
qed

end

subsubsection \<open>Applying IKKBZ on Simple Cost Functions\<close>

text \<open>
  For simple cost functions like @{term c_nlj} and @{term c_hj} that do not depend on the
  contributing selectivies as @{term c_out} does, the h function does not change. Therefore, we can
  apply it directly using @{term c_IKKBZ} and @{term c_list}.
\<close>

context cmp_tree_query_graph
begin

context
  fixes h :: "'a \<Rightarrow> real \<Rightarrow> real"
  assumes h_pos: "\<forall>x. h x (cf' x) > 0"
begin

theorem ikkbz_query_graph_if_simple_h:
  defines "cost \<equiv> c_IKKBZ h cf match_sel"
  defines "h' \<equiv> (\<lambda>x. h x (cf' x))"
  shows "ikkbz_query_graph bfs sel cf G cmp cost (c_list_r h') (rank_r h')"
  unfolding ikkbz_query_graph_def ikkbz_query_graph_axioms_def assms
  by (auto simp: cmp_tree_query_graph_axioms c_list_asi c_IKKBZ_list_correct_if_simple_h h_pos)

interpretation ikkbz_query_graph bfs sel cf G cmp
    "c_IKKBZ h cf match_sel" "c_list_r (\<lambda>x. h x (cf' x))" "rank_r (\<lambda>x. h x (cf' x))"
  by (fact ikkbz_query_graph_if_simple_h)

corollary ikkbz_simple_h_nempty: "ikkbz \<noteq> []"
  by (rule ikkbz_nempty)

corollary ikkbz_simple_h_valid_tree: "valid_tree (create_ldeep ikkbz)"
  by (rule ikkbz_valid_tree)

corollary ikkbz_simple_h_no_cross:
  "no_cross_products (create_ldeep ikkbz)"
  by (rule ikkbz_no_cross)

theorem ikkbz_simple_h_optimal:
  "\<lbrakk>valid_tree t; no_cross_products t; left_deep t\<rbrakk>
    \<Longrightarrow> c_IKKBZ h cf match_sel (create_ldeep ikkbz) \<le> c_IKKBZ h cf match_sel t"
  by (rule ikkbz_optimal_tree)

abbreviation ikkbz_simple_h :: "'a list" where
  "ikkbz_simple_h \<equiv> ikkbz"
end

text \<open>
  We can now apply these results directly to valid cost functions like @{term c_nlj} and
  @{term c_hj}.
\<close>

lemma id_cf'_gt0: "\<forall>x. id (cf' x) > 0"
  by auto

corollary ikkbz_nempty_nlj: "ikkbz_simple_h (\<lambda>_. id) \<noteq> []"
  using ikkbz_simple_h_nempty[of "\<lambda>_. id", OF id_cf'_gt0] by blast

corollary ikkbz_valid_tree_nlj: "valid_tree (create_ldeep (ikkbz_simple_h (\<lambda>_. id)))"
  using ikkbz_simple_h_valid_tree[of "\<lambda>_. id", OF id_cf'_gt0] by blast

corollary ikkbz_no_cross_nlj: "no_cross_products (create_ldeep (ikkbz_simple_h (\<lambda>_. id)))"
  using ikkbz_simple_h_no_cross[of "\<lambda>_. id", OF id_cf'_gt0] by blast

corollary ikkbz_optimal_nlj:
  "\<lbrakk>valid_tree t; no_cross_products t; left_deep t\<rbrakk>
    \<Longrightarrow> c_nlj cf match_sel (create_ldeep (ikkbz_simple_h (\<lambda>_. id))) \<le> c_nlj cf match_sel t"
  using ikkbz_simple_h_optimal[of "\<lambda>_. id", OF id_cf'_gt0] ikkbz_nempty_nlj
  by (fastforce simp: c_nlj_IKKBZ create_ldeep_ldeep)

corollary ikkbz_nempty_hj: "ikkbz_simple_h (\<lambda>_ _. 1.2) \<noteq> []"
  using ikkbz_simple_h_nempty by force

corollary ikkbz_valid_tree_hj: "valid_tree (create_ldeep (ikkbz_simple_h (\<lambda>_ _. 1.2)))"
  using ikkbz_simple_h_valid_tree by force

corollary ikkbz_no_cross_hj: "no_cross_products (create_ldeep (ikkbz_simple_h (\<lambda>_ _. 1.2)))"
  using ikkbz_simple_h_no_cross by force

corollary ikkbz_optimal_hj:
  "\<lbrakk>valid_tree t; no_cross_products t; left_deep t\<rbrakk>
    \<Longrightarrow> c_hj cf match_sel (create_ldeep (ikkbz_simple_h (\<lambda>_ _. 1.2))) \<le> c_hj cf match_sel t"
  using ikkbz_simple_h_optimal[of "\<lambda>_ _. 1.2"] ikkbz_nempty_hj
  by (fastforce simp: c_hj_IKKBZ create_ldeep_ldeep)

end

subsubsection \<open>Applying IKKBZ on C\_out\<close>

text \<open>
  Since @{term c_out} uses the contributing selectivity as part of its h, we can not use the general
  approach we used for the "simple" cost functions. Instead, we show the applicability directly.
\<close>

context tree_query_graph
begin

definition c_out_list_r  :: "'a \<Rightarrow> 'a list \<Rightarrow> real" where
  "c_out_list_r r = c_list_r (\<lambda>a. sel_r r a * cf' a) r"

definition c_out_rank_r  :: "'a \<Rightarrow> 'a list \<Rightarrow> real" where
  "c_out_rank_r r = rank_r (\<lambda>a. sel_r r a * cf' a) r"

lemma c_out_eq_c_list_cf':
  fixes t
  defines "xs \<equiv> revorder t"
  defines "h \<equiv> (\<lambda>a. ldeep_s match_sel xs a * cf' a)"
  assumes "distinct_relations t" and "left_deep t"
  shows "c_list (ldeep_s match_sel xs) cf' h (first_node t) xs = c_out cf' match_sel t"
  using c_out_eq_c_list assms by blast

lemma c_out_list_correct_cf':
  fixes t
  defines "h \<equiv> (\<lambda>a. sel_r (first_node t) a * cf' a)"
  assumes "valid_tree t" and "no_cross_products t" and "left_deep t"
  shows "c_list_r h (first_node t) (revorder t) = c_out cf' match_sel t"
  using c_out_eq_c_list_cf' assms sel_r_eq_ldeep_s_if_valid_no_cross
  by (fastforce simp: valid_tree_def c_list_ldeep_s_eq_c_list_r_if_valid_no_cross)

lemma c_out_list_correct_cf:
  fixes t
  defines "h \<equiv> (\<lambda>a. sel_r (first_node t) a * cf' a)"
  assumes "valid_tree t" and "no_cross_products t" and "left_deep t"
  shows "c_list_r h (first_node t) (revorder t) = c_out cf match_sel t"
  using c_out_list_correct_cf' c_out_cf'_eq' assms by simp

lemma c_out_list_correct:
  "\<lbrakk>valid_tree t; no_cross_products t; left_deep t\<rbrakk>
    \<Longrightarrow> c_out_list_r (first_node t) (revorder t) = c_out cf match_sel t"
  using c_out_list_correct_cf c_out_list_r_def by simp

lemma c_out_h_gt0: "r \<in> verts G \<Longrightarrow> (\<lambda>a. sel_r r a * cf' a) x > 0"
  using sel_r_gt0 by (simp add: pos_cards')

lemma c_out_r_asi: "r \<in> verts G \<Longrightarrow> asi (c_out_rank_r r) r (c_out_list_r r)"
  using c_out_h_gt0 by (simp add: c_list_asi c_out_list_r_def c_out_rank_r_def)

end

context cmp_tree_query_graph
begin

theorem ikkbz_query_graph_c_out:
  "ikkbz_query_graph bfs sel cf G cmp (c_out cf match_sel) c_out_list_r c_out_rank_r"
  unfolding ikkbz_query_graph_def ikkbz_query_graph_axioms_def
  by (auto simp: cmp_tree_query_graph_axioms c_out_r_asi c_out_list_correct)

interpretation QG\<^sub>o\<^sub>u\<^sub>t:
  ikkbz_query_graph bfs sel cf G cmp "c_out cf match_sel" c_out_list_r c_out_rank_r
  by (rule ikkbz_query_graph_c_out)

corollary ikkbz_nempty_cout: "QG\<^sub>o\<^sub>u\<^sub>t.ikkbz \<noteq> []"
  using QG\<^sub>o\<^sub>u\<^sub>t.ikkbz_nempty .

corollary ikkbz_valid_tree_cout: "valid_tree (create_ldeep QG\<^sub>o\<^sub>u\<^sub>t.ikkbz)"
  using QG\<^sub>o\<^sub>u\<^sub>t.ikkbz_valid_tree .

corollary ikkbz_no_cross_cout: "no_cross_products (create_ldeep QG\<^sub>o\<^sub>u\<^sub>t.ikkbz)"
  using QG\<^sub>o\<^sub>u\<^sub>t.ikkbz_no_cross .

corollary ikkbz_optimal_cout:
  "\<lbrakk>valid_tree t; no_cross_products t; left_deep t\<rbrakk>
    \<Longrightarrow> c_out cf match_sel (create_ldeep QG\<^sub>o\<^sub>u\<^sub>t.ikkbz) \<le> c_out cf match_sel t"
  using QG\<^sub>o\<^sub>u\<^sub>t.ikkbz_optimal_tree .

end

subsection \<open>Instantiating Comparators with Linorders\<close>

(* possible cmp definition based on 'a::linorder *)
locale alin_tree_query_graph = tree_query_graph bfs sel cf G
  for bfs sel and cf :: "'a :: linorder \<Rightarrow> real" and G
begin

lift_definition cmp :: "('a list\<times>'b) comparator" is
  "(\<lambda>x y. if hd (fst x) < hd (fst y) then Less
    else if hd (fst x) > hd (fst y) then Greater else Equiv)"
  by(unfold_locales) (auto split: if_splits)

lemma cmp_hd_eq_if_equiv: "compare cmp (v1,e1) (v2,e2) = Equiv \<Longrightarrow> hd v1 = hd v2"
  by(auto simp: cmp.rep_eq split: if_splits)

lemma cmp_sets_not_dsjnt_if_equiv:
  "\<lbrakk>v1 \<noteq> []; v2 \<noteq> []; compare cmp (v1,e1) (v2,e2) = Equiv\<rbrakk> \<Longrightarrow> set v1 \<inter> set v2 \<noteq> {}"
  using cmp_hd_eq_if_equiv disjoint_iff_not_equal hd_in_set[of v1] by auto

lemma cmp_tree_qg: "cmp_tree_query_graph bfs sel cf G cmp"
  by standard (simp add: cmp_sets_not_dsjnt_if_equiv)

interpretation cmp_tree_query_graph bfs sel cf G cmp
  by (rule cmp_tree_qg)

(* The results are now useable: *)
thm ikkbz_optimal_hj ikkbz_optimal_cout

end

(* possible cmp definition based on 'b::linorder *)
locale blin_tree_query_graph = tree_query_graph bfs sel cf G
  for bfs and sel :: "'b :: linorder \<Rightarrow> real" and cf G
begin

lift_definition cmp :: "('a list\<times>'b) comparator" is
  "(\<lambda>x y. if snd x < snd y then Less
    else if snd x > snd y then Greater else Equiv)"
  by(unfold_locales) (auto split: if_splits)

lemma cmp_arcs_eq_if_equiv: "compare cmp (v1,e1) (v2,e2) = Equiv \<Longrightarrow> e1 = e2"
  by(auto simp: cmp.rep_eq split: if_splits)

lemma cmp_tree_qg: "cmp_tree_query_graph bfs sel cf G cmp"
  by standard (simp add: cmp_arcs_eq_if_equiv)

interpretation cmp_tree_query_graph bfs sel cf G cmp
  by (rule cmp_tree_qg)

(* The results are now useable: *)
thm ikkbz_optimal_hj ikkbz_optimal_cout

end

end