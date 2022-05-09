(* Title: Design Extras.thy
   Author: Chelsea Edmonds
*)

section \<open> Micellaneous Design Extras \<close>

text \<open>Extension's to the author's previous entry on Design Theory \<close>

theory Design_Extras imports Set_Multiset_Extras Design_Theory.BIBD
begin

subsection \<open>Extensions to existing Locales and Properties \<close>

text \<open>Extend lemmas on intersection number\<close>
lemma inter_num_max_bound: 
  assumes "finite b1" "finite b2"
  shows "b1 |\<inter>| b2 \<le> card b1" "b1 |\<inter>| b2 \<le> card b2"
  by(simp_all add: assms intersection_number_def card_mono)

lemma inter_eq_blocks_eq_card: "card b1 = card b2 \<Longrightarrow> finite b1 \<Longrightarrow> finite b2 \<Longrightarrow> b1 |\<inter>| b2 = card b1 
    \<Longrightarrow> b1 = b2"
  using equal_card_inter_fin_eq_sets intersection_number_def by (metis) 

lemma inter_num_of_eq_blocks: "b1 = b2 \<Longrightarrow> b1 |\<inter>| b2 = card b1"
  by (simp add: intersection_number_def)

lemma intersect_num_same_eq_size[simp]: "bl |\<inter>| bl = card bl"
  by (simp add: intersection_number_def)

lemma index_lt_rep_general: "x \<in> ps \<Longrightarrow> B index ps \<le> B rep x"
  by (simp add: points_index_def point_replication_number_def) 
    (metis filter_filter_mset_cond_simp size_filter_mset_lesseq subset_iff)

context incidence_system 
begin

lemma block_size_alt:
  assumes "bl \<in># \<B>"
  shows "card bl = card {x \<in> \<V> . x \<in> bl}" 
proof -
  have "\<And> x. x \<in> bl \<Longrightarrow> x \<in> \<V>" using wellformed assms by auto
  thus ?thesis
    by (metis (no_types, lifting) Collect_cong Collect_mem_eq) 
qed

lemma complement_image: "\<B>\<^sup>C = image_mset block_complement \<B>"
  by (simp add: complement_blocks_def)

lemma point_in_block_rep_min_iff:
  assumes "x \<in> \<V>" 
  shows "\<exists> bl . bl \<in># \<B> \<and> x \<in> bl \<longleftrightarrow> (\<B> rep x > 0)"
  using rep_number_g0_exists
  by (metis block_complement_elem_iff block_complement_inv wellformed)

lemma points_inter_num_rep: 
  assumes "b1 \<in># \<B>" and "b2 \<in># \<B> - {#b1#}"
  shows "card {v \<in> \<V> . v \<in> b1 \<and> v \<in> b2} = b1 |\<inter>| b2"
proof -
  have "\<And> x. x \<in> b1 \<inter> b2 \<Longrightarrow> x \<in> \<V>" using wellformed assms by auto
  then have "{v \<in> \<V> . v \<in> (b1 \<inter> b2)} = (b1 \<inter> b2)"
    by blast 
  then have "card {v \<in> \<V> . v \<in> b1 \<and> v \<in> b2} = card (b1 \<inter> b2)"
    by simp 
  thus ?thesis using assms intersection_number_def by metis 
qed

text \<open>Extensions on design operation lemmas \<close>
lemma del_block_b: 
  "bl \<in># \<B> \<Longrightarrow> size (del_block bl) = \<b> - 1"
  "bl \<notin># \<B> \<Longrightarrow> size (del_block bl) = \<b>"
  by (simp_all add: del_block_def size_Diff_singleton)

lemma del_block_points_index: 
  assumes "ps \<subseteq> \<V>"
  assumes "card ps = 2"
  assumes "bl \<in># \<B>"
  shows "ps \<subseteq> bl \<Longrightarrow> points_index (del_block bl) ps = points_index \<B> ps - 1"
        "\<not> (ps \<subseteq> bl) \<Longrightarrow> points_index (del_block bl) ps = points_index \<B> ps"
proof -
  assume "ps \<subseteq> bl"
  then show "points_index (del_block bl) ps = points_index \<B> ps - 1"
    using point_index_diff del_block_def
    by (metis assms(3) insert_DiffM2 points_index_singleton) 
next
  assume "\<not> ps \<subseteq> bl"
  then show "del_block bl index ps = \<B> index ps"
    using point_index_diff del_block_def
    by (metis add_block_def add_block_index_not_in assms(3) insert_DiffM2) 
qed

end

text \<open>Extensions to properties of design sub types \<close>

context finite_incidence_system
begin

lemma complete_block_size_eq_points: "bl \<in># \<B> \<Longrightarrow> card bl = \<v> \<Longrightarrow> bl = \<V>"
  using wellformed by (simp add:  card_subset_eq finite_sets) 

lemma complete_block_all_subsets: "bl \<in># \<B> \<Longrightarrow> card bl = \<v> \<Longrightarrow> ps \<subseteq> \<V> \<Longrightarrow> ps \<subseteq> bl"
  using complete_block_size_eq_points by auto

lemma del_block_complete_points_index: "ps \<subseteq> \<V> \<Longrightarrow> card ps = 2 \<Longrightarrow> bl \<in># \<B> \<Longrightarrow> card bl = \<v> \<Longrightarrow> 
  points_index (del_block bl) ps = points_index \<B> ps - 1"
  using complete_block_size_eq_points del_block_points_index(1) by blast

end

context design
begin

lemma block_num_rep_bound: "\<b> \<le> (\<Sum> x \<in> \<V>. \<B> rep x)"
proof -
  have exists: "\<And> bl. bl \<in># \<B> \<Longrightarrow> (\<exists> x \<in> \<V> . bl \<in># {#b \<in># \<B>. x \<in> b#})" using wellformed
    using blocks_nempty by fastforce 
  then have bss: "\<B> \<subseteq># \<Sum>\<^sub># (image_mset (\<lambda> v. {#b \<in># \<B>. v \<in> b#}) (mset_set \<V>))"
  proof (intro  mset_subset_eqI)
    fix bl
    show "count \<B> bl \<le> count (\<Sum>v\<in>#mset_set \<V>. filter_mset ((\<in>) v) \<B>) bl"
    proof (cases "bl \<in># \<B>")
      case True
      then obtain x where xin: "x \<in> \<V>" and blin: "bl \<in># filter_mset ((\<in>) x) \<B>" using exists by auto
      then have eq: "count \<B> bl = count (filter_mset ((\<in>) x) \<B>) bl" by simp 
      have "(\<Sum>v\<in>#mset_set \<V>. filter_mset ((\<in>) v) \<B>) = (filter_mset ((\<in>) x) \<B>) + 
        (\<Sum>v\<in>#(mset_set \<V>) - {#x#}. filter_mset ((\<in>) v) \<B>)"
        using xin by (simp add: finite_sets mset_set.remove) 
      then have "count (\<Sum>v\<in>#mset_set \<V>. filter_mset ((\<in>) v) \<B>) bl = count (filter_mset ((\<in>) x) \<B>) bl 
        +  count (\<Sum>v\<in>#(mset_set \<V>) - {#x#}. filter_mset ((\<in>) v) \<B>) bl"
        by simp
      then show ?thesis using eq by linarith 
    next
      case False
      then show ?thesis by (metis count_eq_zero_iff le0)
    qed
  qed
  have "(\<Sum> x \<in> \<V>. \<B> rep x) = (\<Sum> x \<in> \<V>. size ({#b \<in># \<B>. x \<in> b#}))" 
    by (simp add: point_replication_number_def)
  also have "... = (\<Sum> x \<in># (mset_set \<V>). size ({#b \<in># \<B>. x \<in> b#}))"
    by (simp add: sum_unfold_sum_mset) 
  also have "... = (\<Sum> x \<in># (image_mset (\<lambda> v. {#b \<in># \<B>. v \<in> b#}) (mset_set \<V>)) . size x)"
    by auto  
  finally have "(\<Sum> x \<in> \<V>. \<B> rep x) = size (\<Sum>\<^sub># (image_mset (\<lambda> v. {#b \<in># \<B>. v \<in> b#}) (mset_set \<V>)))" 
    using size_big_union_sum by metis 
  then show ?thesis using bss
    by (simp add: size_mset_mono)
qed

end

context proper_design
begin

lemma del_block_proper: 
  assumes "\<b> > 1"
  shows "proper_design \<V> (del_block bl)"
proof -
  interpret d: design \<V> "(del_block bl)"
    using delete_block_design by simp
  have "d.\<b> > 0" using del_block_b assms
    by (metis b_positive zero_less_diff) 
  then show ?thesis by(unfold_locales) (auto)
qed

end

context simple_design 
begin

lemma inter_num_lt_block_size_strict: 
  assumes "bl1 \<in># \<B>"
  assumes "bl2 \<in># \<B>"
  assumes "bl1 \<noteq> bl2"
  assumes "card bl1 = card bl2"
  shows "bl1 |\<inter>| bl2 < card bl1" "bl1 |\<inter>| bl2 < card bl2"
proof -
  have lt: "bl1 |\<inter>| bl2 \<le> card bl1" using finite_blocks
    by (simp add: \<open>bl1 \<in># \<B>\<close> \<open>bl2 \<in># \<B>\<close> inter_num_max_bound(1)) 
  have ne: "bl1 |\<inter>| bl2 \<noteq> card bl1" 
  proof (rule ccontr, simp)
    assume "bl1 |\<inter>| bl2 = card bl1"
    then have "bl1 = bl2" using assms(4) inter_eq_blocks_eq_card assms(1) assms(2) finite_blocks 
      by blast 
    then show False using assms(3) by simp
  qed
  then show "bl1 |\<inter>| bl2 < card bl1" using lt by simp
  have "bl1 |\<inter>| bl2 \<noteq> card bl2" using ne by (simp add: assms(4)) 
  then show "bl1 |\<inter>| bl2 < card bl2" using lt assms(4) by simp
qed

lemma block_mset_distinct: "distinct_mset \<B>" using simple
  by (simp add: distinct_mset_def) 

end

context constant_rep_design 
begin

lemma index_lt_const_rep: 
  assumes "ps \<subseteq> \<V>"
  assumes "ps \<noteq> {}"
  shows "\<B> index ps \<le> \<r>"
proof -
  obtain x where xin: "x \<in> ps" using assms by auto
  then have "\<B> rep x = \<r>"
    by (meson assms(1) in_mono rep_number_alt_def_all) 
  thus ?thesis using index_lt_rep_general xin by auto
qed

end

context t_wise_balance
begin

lemma  obtain_t_subset_with_point: 
  assumes "x \<in> \<V>"
  obtains ps where "ps \<subseteq> \<V>" and "card ps = \<t>" and "x \<in> ps"
proof (cases "\<t> = 1")
  case True
  have "{x} \<subseteq> \<V>" "card {x} = 1" "x \<in> {x}"
    using assms by simp_all
  then show ?thesis
    using True that by blast 
next
  case False
  have "\<t> - 1 \<le> card (\<V> - {x})"
    by (simp add: assms diff_le_mono finite_sets t_lt_order) 
  then obtain ps' where psss: "ps' \<subseteq> (\<V> - {x})" and psc: "card ps' = \<t> - 1" 
    by (meson obtain_subset_with_card_n)
  then have xs: "(insert x ps') \<subseteq> \<V>"
    using assms by blast 
  have xnotin: "x \<notin> ps'" using psss
    by blast 
  then have "card (insert x ps') = Suc (card ps')"
    by (meson \<open>insert x ps' \<subseteq> \<V>\<close> finite_insert card_insert_disjoint finite_sets finite_subset) 
  then have "card (insert x ps') = card ps' + 1"
    by presburger 
  then have xc: "card (insert x ps') = \<t>" using psc
    using add.commute add_diff_inverse t_non_zero by linarith 
  have "x \<in> (insert x ps')" by simp
  then show ?thesis using xs xc that by blast 
qed

lemma const_index_lt_rep: 
  assumes "x \<in> \<V>"
  shows "\<Lambda>\<^sub>t \<le> \<B> rep x"
proof -
  obtain ps where psin: "ps \<subseteq> \<V>" and "card ps = \<t>" and xin: "x \<in> ps" 
    using assms t_lt_order obtain_t_subset_with_point by auto
  then have "\<B> index ps = \<Lambda>\<^sub>t " using balanced by simp
  thus ?thesis using index_lt_rep_general xin 
    by (meson) 
qed

end

context pairwise_balance
begin

lemma index_zero_iff: "\<Lambda> = 0 \<longleftrightarrow> (\<forall> bl \<in># \<B> . card bl = 1)"
proof (auto)
  fix bl assume l0: "\<Lambda> = 0" assume blin: "bl \<in># \<B>"
  have "card bl = 1"
  proof (rule ccontr)
    assume "card bl \<noteq> 1"
    then have "card bl \<ge> 2" using block_size_gt_0
      by (metis Suc_1 Suc_leI blin less_one nat_neq_iff) 
    then obtain ps where psss: "ps \<subseteq> bl" and pscard: "card ps = 2"
      by (meson obtain_subset_with_card_n)
    then have psin: "\<B> index ps \<ge> 1"
      using blin points_index_count_min by auto
    have "ps \<subseteq> \<V>" using wellformed psss blin by auto
    then show False using balanced l0 psin pscard by auto
  qed
  thus "card bl = (Suc 0)" by simp
next
  assume a: "\<forall>bl\<in>#\<B>. card bl = Suc 0"
  obtain ps where psss: "ps \<subseteq> \<V>" and ps2: "card ps = 2"
    by (meson obtain_t_subset_points) 
  then have "\<And> bl. bl \<in># \<B> \<Longrightarrow> (card ps > card bl)" using a
    by simp 
  then have cond: "\<And> bl. bl \<in># \<B> \<Longrightarrow> \<not>( ps \<subseteq>  bl)"
    by (metis card_mono finite_blocks le_antisym less_imp_le_nat less_not_refl3) 
  have "\<B> index ps = size {# bl \<in># \<B> . ps \<subseteq> bl #}" by (simp add:points_index_def)
  then have "\<B> index ps = size {#}" using cond
    by (metis points_index_0_iff size_empty) 
  thus "\<Lambda> = 0" using psss ps2 balanced by simp
qed

lemma count_complete_lt_balance: "count \<B> \<V> \<le> \<Lambda>"
proof (rule ccontr)
  assume a: "\<not> count \<B> \<V> \<le> \<Lambda>"
  then have assm: "count \<B> \<V> > \<Lambda>"
    by simp
  then have gt: "size {# bl \<in># \<B> . bl = \<V>#} > \<Lambda>"
    by (simp add: count_size_set_repr) 
  obtain ps where psss: "ps \<subseteq> \<V>" and pscard: "card ps = 2" using t_lt_order
    by (meson obtain_t_subset_points) 
  then have "{# bl \<in># \<B> . bl = \<V>#} \<subseteq># {# bl \<in># \<B> . ps \<subseteq> bl #}"
    by (metis a balanced le_refl points_index_count_min) 
  then have "size {# bl \<in># \<B> . bl = \<V>#} \<le> \<B> index ps " 
    using points_index_def[of \<B> ps] size_mset_mono by simp
  thus False using pscard psss balanced gt by auto
qed

lemma eq_index_rep_imp_complete: 
  assumes "\<Lambda> = \<B> rep x"
  assumes "x \<in> \<V>"
  assumes "bl \<in># \<B>"
  assumes "x \<in> bl"
  shows "card bl = \<v>"
proof -
  have "\<And> y. y \<in> \<V> \<Longrightarrow> y \<noteq> x \<Longrightarrow> card {x, y} = 2 \<and> {x, y} \<subseteq> \<V>" using assms by simp
  then have size_eq: "\<And> y. y \<in> \<V> \<Longrightarrow> y \<noteq> x \<Longrightarrow> size {# b \<in># \<B> . {x, y} \<subseteq> b#} = size {# b \<in># \<B> . x \<in> b#}"
    using point_replication_number_def balanced points_index_def assms by metis 
  have "\<And> y b. y \<in> \<V> \<Longrightarrow> y \<noteq> x \<Longrightarrow> b \<in># \<B> \<Longrightarrow> {x, y} \<subseteq> b \<longrightarrow> x \<in> b" by simp
  then have "\<And> y. y \<in> \<V> \<Longrightarrow> y \<noteq> x \<Longrightarrow> {# b \<in># \<B> . {x, y} \<subseteq> b#} \<subseteq># {# b \<in># \<B> . x \<in> b#}" 
    using multiset_filter_mono2 assms by auto
  then have eq_sets: "\<And> y. y \<in> \<V> \<Longrightarrow> y \<noteq> x \<Longrightarrow> {# b \<in># \<B> . {x, y} \<subseteq> b#} = {# b \<in># \<B> . x \<in> b#}" 
    using size_eq by (smt (z3) Diff_eq_empty_iff_mset cancel_comm_monoid_add_class.diff_cancel 
        size_Diff_submset size_empty size_eq_0_iff_empty subset_mset.antisym) 
  have "bl \<in># {# b \<in># \<B> . x \<in> b#}" using assms by simp
  then have "\<And> y. y \<in> \<V> \<Longrightarrow> y \<noteq> x \<Longrightarrow> {x, y} \<subseteq> bl" using eq_sets
    by (metis (no_types, lifting) Multiset.set_mset_filter mem_Collect_eq) 
  then have "\<And> y. y \<in> \<V> \<Longrightarrow> y \<in> bl" using assms by blast 
  then have "bl = \<V>" using wellformed assms(3) by blast 
  thus ?thesis by simp
qed

lemma incomplete_index_strict_lt_rep:
  assumes "\<And> bl. bl \<in># \<B> \<Longrightarrow> incomplete_block bl" 
  assumes "x \<in> \<V>"
  assumes "\<Lambda> > 0"
  shows "\<Lambda> < \<B> rep x"
proof (rule ccontr)
  assume "\<not> (\<Lambda> < \<B> rep x)"
  then have a: "\<Lambda> \<ge> \<B> rep x"
    by simp
  then have "\<Lambda> = \<B> rep x" using const_index_lt_rep
    using assms(2) le_antisym by blast 
  then obtain bl where xin: "x \<in> bl" and blin: "bl \<in># \<B>"
    by (metis assms(3) rep_number_g0_exists) 
  thus False using assms eq_index_rep_imp_complete incomplete_alt_size
    using \<open>\<Lambda> = \<B> rep x\<close> nat_less_le by blast  
qed

text \<open>Construct new PBD's from existing PBD's \<close>

lemma remove_complete_block_pbd: 
  assumes "\<b> \<ge> 2"
  assumes "bl \<in># \<B>"
  assumes "card bl = \<v>"
  shows "pairwise_balance \<V> (del_block bl) (\<Lambda> - 1)"
proof -
  interpret pd: proper_design \<V> "(del_block bl)" using assms(1) del_block_proper by simp
  show ?thesis using t_lt_order assms del_block_complete_points_index 
    by (unfold_locales) (simp_all)
qed

lemma remove_complete_block_pbd_alt: 
  assumes "\<b> \<ge> 2"
  assumes "bl \<in># \<B>"
  assumes "bl = \<V>"
  shows "pairwise_balance \<V> (del_block bl) (\<Lambda> - 1)"
  using remove_complete_block_pbd assms by blast 

lemma b_gt_index:"\<b> \<ge> \<Lambda>"
proof (rule ccontr)
  assume blt: "\<not> \<b> \<ge> \<Lambda>"
  obtain ps where "card ps = 2" and "ps \<subseteq> \<V>" using t_lt_order
    by (meson obtain_t_subset_points) 
  then have "size {#bl \<in># \<B>. ps \<subseteq> bl#} = \<Lambda>" using balanced by (simp add: points_index_def)
  thus False using blt by auto 
qed

lemma remove_complete_blocks_set_pbd:
  assumes "x < \<Lambda>"
  assumes "size A = x"
  assumes "A \<subset># \<B>"
  assumes "\<And> a. a \<in># A \<Longrightarrow> a = \<V>"
  shows "pairwise_balance \<V> (\<B> - A) (\<Lambda> - x)"
using assms proof (induct "x" arbitrary: A)
  case 0
  then have beq: "\<B> - A = \<B>" by simp
  have "pairwise_balance \<V> \<B> \<Lambda>" by (unfold_locales)
  then show ?case using beq by simp
next
  case (Suc x)
  then have "size A > 0" by simp
  let ?A' = "A - {#\<V>#}"
  have ss: "?A' \<subset># \<B>"
    using Suc.prems(3) by (metis diff_subset_eq_self subset_mset.le_less_trans)
  have sx: "size ?A' = x"
    by (metis Suc.prems(2) Suc.prems(4) Suc_inject size_Suc_Diff1 size_eq_Suc_imp_elem)
  have xlt: "x < \<Lambda>"
    by (simp add: Suc.prems(1) Suc_lessD) 
  have av: "\<And> a. a \<in># ?A' \<Longrightarrow> a = \<V>" using Suc.prems(4)
    by (meson in_remove1_mset_neq)
  then interpret pbd: pairwise_balance \<V> "(\<B> - ?A')" "(\<Lambda> - x)" using Suc.hyps sx ss xlt by simp
  have "Suc x < \<b>" using Suc.prems(3)
    by (metis Suc.prems(2) mset_subset_size) 
  then have "\<b> - x \<ge> 2"
    by linarith 
  then have bgt: "size (\<B> - ?A') \<ge> 2" using ss size_Diff_submset
    by (metis subset_msetE sx)
  have ar: "add_mset \<V> (remove1_mset \<V> A) = A" using Suc.prems(2) Suc.prems(4)
    by (metis insert_DiffM size_eq_Suc_imp_elem) 
  then have db: "pbd.del_block \<V> = \<B> - A" by(simp add: pbd.del_block_def)
  then have "\<B> - ?A' = \<B> - A + {#\<V>#}" using Suc.prems(2) Suc.prems(4)
    by (metis (no_types, lifting) Suc.prems(3) ar add_diff_cancel_left' add_mset_add_single add_right_cancel 
        pbd.del_block_def remove_1_mset_id_iff_notin ss subset_mset.lessE trivial_add_mset_remove_iff) 
  then have "\<V> \<in># (\<B> - ?A')" by simp 
  then have "pairwise_balance \<V> (\<B> - A) (\<Lambda> - (Suc x))" using db bgt diff_Suc_eq_diff_pred 
      diff_commute pbd.remove_complete_block_pbd_alt by presburger
  then show ?case by simp
qed

lemma remove_all_complete_blocks_pbd:
  assumes "count \<B> \<V> < \<Lambda>"
  shows "pairwise_balance \<V> (removeAll_mset \<V> \<B>) (\<Lambda> - (count \<B> \<V>))" (is "pairwise_balance \<V> ?B ?\<Lambda>")
proof -
  let ?A = "replicate_mset (count \<B> \<V>) \<V>"
  let ?x = "size ?A"
  have blt: "count \<B> \<V> \<noteq> \<b>" using b_gt_index assms
    by linarith 
  have xeq: "?x = count \<B> \<V>" by simp
  have av: "\<And> a. a \<in># ?A \<Longrightarrow> a = \<V>"
    by (metis in_replicate_mset)
  have "?A \<subseteq># \<B>"
    by (meson count_le_replicate_mset_subset_eq le_eq_less_or_eq)
  then have "?A \<subset># \<B>" using blt
    by (metis subset_mset.nless_le xeq) 
  thus ?thesis using assms av xeq remove_complete_blocks_set_pbd
    by presburger 
qed

end

context bibd
begin
lemma symmetric_bibdIII: "\<r> = \<k> \<Longrightarrow> symmetric_bibd \<V> \<B> \<k> \<Lambda>"
  using necessary_condition_one symmetric_condition_1 by (unfold_locales) (simp)
end

subsection \<open> New Design Locales \<close>
text \<open> We establish a number of new locales and link them to the existing locale hierarchy
in order to reason in contexts requiring specific combinations of contexts \<close>

text \<open>Regular t-wise balance \<close>
locale regular_t_wise_balance = t_wise_balance + constant_rep_design
begin

lemma reg_index_lt_rep: 
  shows "\<Lambda>\<^sub>t \<le> \<r>"
proof -
  obtain ps where psin: "ps \<subseteq> \<V>" and pst: "card ps = \<t>"
    by (metis obtain_t_subset_points) 
  then have ne: "ps \<noteq> {}" using t_non_zero by auto
  then have "\<B> index ps = \<Lambda>\<^sub>t" using balanced pst psin by simp
  thus ?thesis using index_lt_const_rep
    using ne psin by auto 
qed

end

locale regular_pairwise_balance = regular_t_wise_balance \<V> \<B> 2 \<Lambda> \<r> + pairwise_balance \<V> \<B> \<Lambda>
  for \<V> and \<B> and \<Lambda> and \<r>

text \<open> Const Intersect Design \<close>
text \<open> This is the dual of a balanced design, and used extensively in the remaining formalisation \<close>

locale const_intersect_design = proper_design + 
  fixes \<m> :: nat
  assumes const_intersect: "b1 \<in># \<B> \<Longrightarrow> b2 \<in># (\<B> - {#b1#}) \<Longrightarrow> b1 |\<inter>| b2 = \<m>"

sublocale symmetric_bibd \<subseteq> const_intersect_design \<V> \<B> \<Lambda>
  by (unfold_locales) (simp)

context const_intersect_design
begin

lemma inter_num_le_block_size: 
  assumes "bl \<in># \<B>"
  assumes "\<b> \<ge> 2"
  shows "\<m> \<le> card bl"
proof (rule ccontr)
  assume a: "\<not> (\<m> \<le> card bl)"
  obtain bl' where blin: "bl' \<in># \<B> - {#bl#}"
    using assms by (metis add_mset_add_single diff_add_inverse2 diff_is_0_eq' multiset_nonemptyE 
        nat_1_add_1 remove1_mset_eqE size_single zero_neq_one)
  then have const: "bl |\<inter>| bl' = \<m>" using const_intersect assms by auto
  thus False using inter_num_max_bound(1) finite_blocks 
    by (metis a blin assms(1) finite_blocks in_diffD) 
qed

lemma const_inter_multiplicity_one: 
  assumes "bl \<in># \<B>"
  assumes "\<m> < card bl"
  shows "multiplicity bl = 1"
proof (rule ccontr)
  assume "multiplicity bl \<noteq> 1"
  then have "multiplicity bl > 1" using assms
    by (simp add: le_neq_implies_less)
  then obtain bl2 where "bl = bl2" and "bl2 \<in># \<B> - {#bl#}"
    by (metis count_single in_diff_count)
  then have "bl |\<inter>| bl2 = card bl"
    using inter_num_of_eq_blocks by blast  
  thus False using assms const_intersect
    by (simp add: \<open>bl2 \<in># remove1_mset bl \<B>\<close>) 
qed

lemma mult_blocks_const_inter: 
  assumes "bl \<in># \<B>"
  assumes "multiplicity bl > 1"
  assumes "\<b> \<ge> 2"
  shows "\<m> = card bl"
proof (rule ccontr)
  assume "\<m> \<noteq> card bl"
  then have "\<m> < card bl" using inter_num_le_block_size assms
    using nat_less_le by blast 
  then have "multiplicity bl = 1" using const_inter_multiplicity_one assms by simp
  thus False using assms(2) by simp
qed

lemma simple_const_inter_block_size: "(\<And> bl. bl \<in># \<B> \<Longrightarrow> \<m> < card bl) \<Longrightarrow> simple_design \<V> \<B>"
  using const_inter_multiplicity_one by (unfold_locales) (simp)

lemma simple_const_inter_iff: 
  assumes "\<b> \<ge> 2"
  shows "size {#bl \<in># \<B> . card bl = \<m>  #} \<le> 1 \<longleftrightarrow> simple_design \<V> \<B>"
proof (intro iffI)
  assume a: "size {#bl \<in># \<B>. card bl = \<m>#} \<le> 1"
  show "simple_design \<V> \<B>" 
  proof (unfold_locales)
    fix bl assume blin: "bl \<in># \<B>"
    show "multiplicity bl = 1"
    proof (cases "card bl = \<m>")
      case True
      then have m: "multiplicity bl = size {#b \<in># \<B> . b = bl#}"
        by (simp add: count_size_set_repr)
      then have "{#b \<in># \<B> . b = bl#} \<subseteq># {#bl \<in># \<B>. card bl = \<m>#}" using True
        by (simp add: mset_subset_eqI)
      then have "size {#b \<in># \<B> . b = bl#} \<le> size {#bl \<in># \<B>. card bl = \<m>#}"
        by (simp add: size_mset_mono) 
      then show ?thesis using a blin
        by (metis count_eq_zero_iff le_neq_implies_less le_trans less_one m) 
    next
      case False
      then have "\<m> < card bl" using assms
        by (simp add: blin inter_num_le_block_size le_neq_implies_less) 
      then show ?thesis using const_inter_multiplicity_one
        by (simp add: blin) 
    qed
  qed
next
  assume simp: "simple_design \<V> \<B>"
  then have mult: "\<And> bl. bl \<in># \<B> \<Longrightarrow> multiplicity bl = 1"
    using simple_design.axioms(2) simple_incidence_system.simple_alt_def_all by blast 
  show "size {#bl \<in># \<B> . card bl = \<m> #} \<le> 1"
  proof (rule ccontr)
    assume "\<not> size {#bl \<in># \<B>. card bl = \<m>#} \<le> 1"
    then have "size {#bl \<in># \<B> . card bl = \<m> #} > 1" by simp
    then obtain bl1 bl2 where blin: "bl1 \<in># \<B>" and bl2in: "bl2 \<in># \<B> - {#bl1#}" and 
        card1: "card bl1 = \<m>" and card2: "card bl2 = \<m>"
      using obtain_two_items_mset_filter by blast 
    then have "bl1 |\<inter>| bl2 = \<m>" using const_intersect by simp
    then have "bl1 = bl2"
      by (metis blin bl2in card1 card2 finite_blocks in_diffD inter_eq_blocks_eq_card)
    then have "multiplicity bl1 > 1"
      using \<open>bl2 \<in># remove1_mset bl1 \<B>\<close> count_eq_zero_iff by force 
    thus False using mult blin by simp
  qed
qed

lemma empty_inter_implies_rep_one: 
  assumes "\<m> = 0"
  assumes "x \<in> \<V>"
  shows "\<B> rep x \<le> 1"
proof (rule ccontr)
  assume a: "\<not> \<B> rep x \<le> 1"
  then have gt1: "\<B> rep x > 1" by simp
  then obtain bl1 where blin1: "bl1 \<in># \<B>" and xin1: "x \<in> bl1"
    by (metis gr_implies_not0 linorder_neqE_nat rep_number_g0_exists) 
  then have "(\<B> - {#bl1#}) rep x > 0" using gt1 point_rep_number_split point_rep_singleton_val
    by (metis a add_0 eq_imp_le neq0_conv remove1_mset_eqE) 
  then obtain bl2 where blin2: "bl2 \<in># (\<B> - {#bl1#})" and xin2: "x \<in> bl2" 
    by (metis rep_number_g0_exists) 
  then have "x \<in> (bl1 \<inter> bl2)" using xin1 by simp
  then have "bl1 |\<inter>| bl2 \<noteq> 0"
    by (metis blin1 empty_iff finite_blocks intersection_number_empty_iff) 
  thus False using const_intersect assms blin1 blin2 by simp
qed

lemma empty_inter_implies_b_lt_v: 
  assumes "\<m> = 0"
  shows "\<b> \<le> \<v>"
proof -
  have le1: "\<And> x. x \<in> \<V> \<Longrightarrow> \<B> rep x \<le> 1" using empty_inter_implies_rep_one assms by simp
  have disj: "{v \<in> \<V> . \<B> rep v = 0} \<inter> {v \<in> \<V> . \<not> (\<B> rep v = 0)} = {}" by auto
  have eqv: "\<V> = ({v \<in> \<V> . \<B> rep v = 0} \<union> {v \<in> \<V> . \<not> (\<B> rep v = 0)})" by auto
  have "\<b> \<le> (\<Sum> x \<in> \<V> . \<B> rep x)" using block_num_rep_bound by simp
  also have 1: "... \<le> (\<Sum> x \<in> ({v \<in> \<V> . \<B> rep v = 0} \<union> {v \<in> \<V> . \<not> (\<B> rep v = 0)}) . \<B> rep x)" 
    using eqv by simp
  also have "... \<le> (\<Sum> x \<in> ({v \<in> \<V> . \<B> rep v = 0}) . \<B> rep x) + (\<Sum> x \<in> ({v \<in> \<V> . \<not> (\<B> rep v = 0)}) . \<B> rep x)"
    using sum.union_disjoint finite_sets eqv disj
    by (metis (no_types, lifting) 1 finite_Un) 
  also have "... \<le> (\<Sum> x \<in> ({v \<in> \<V> . \<not> (\<B> rep v = 0)}) . \<B> rep x)" by simp
  also have "... \<le> (\<Sum> x \<in> ({v \<in> \<V> . \<not> (\<B> rep v = 0)}) . 1)" using le1
    by (metis (mono_tags, lifting) mem_Collect_eq sum_mono)
  also have "... \<le> card {v \<in> \<V> . \<not> (\<B> rep v = 0)}" by simp
  also have "... \<le> card \<V>" using finite_sets
    using card_mono eqv by blast 
  finally show ?thesis by simp
qed

end

locale simple_const_intersect_design = const_intersect_design + simple_design

end