header {*\isaheader{Automatic Refinement: Collection Bindings}*}
theory Autoref_Collection_Bindings
imports Refine_Autoref Collection_Bindings "../Collections/Collections"
begin
  text {* This theory provides an (incomplete) automatic refinement setup for
    the Isabelle Collection Framework.

    Note that the quality of the generated refinement depends on the order
    in which the lemmas are set up here: Lemmas for special operations must
    be set up after lemmas for general operations, e.g., the singleton set
    should come after insert and empty set. Otherwise, the specialized 
    operation will never be tried, because the general operation yields a
    suitable translation, too.
    *}

  (* TODO: Hack to port from older version. Inline this! *)
  abbreviation (input) DETREFe where "DETREFe c r a \<equiv> (c,a)\<in>r"


  subsection "Set"
  
lemma (in set_empty) set_empty_et[autoref_ex]:
  "(empty (),{})\<in>(build_rel (\<alpha>::'s \<Rightarrow> 'x set) invar)"
  by (auto simp: empty_correct)

lemma (in set_memb) set_memb_et[autoref_ex]:
  assumes "DETREFe x Id x'"
  assumes "DETREFe s (build_rel \<alpha> invar) s'" 
  shows "DETREFe (memb x s) Id (x'\<in>s')"
  using assms by (auto simp: memb_correct)
  
lemma (in set_ball) set_ball_et[autoref_ex]:
  "DETREFe s (build_rel \<alpha> invar) s' \<Longrightarrow> DETREFe P Id P'
    \<Longrightarrow> DETREFe (ball s P) Id (\<forall>x\<in>s'. P' x)"
  by (auto simp: ball_correct)
  
lemma (in set_bexists) set_bexists_et[autoref_ex]:
  "DETREFe s (build_rel \<alpha> invar) s' \<Longrightarrow> DETREFe P Id P'
    \<Longrightarrow> DETREFe (bexists s P) Id (\<exists>x\<in>s'. P' x)"
  by (auto simp: bexists_correct)

lemma (in set_size) set_size_et[autoref_ex]:
  "DETREFe s (build_rel \<alpha> invar) s'
    \<Longrightarrow> DETREFe (size s) Id (card s')"
  by (auto simp: size_correct)

lemma (in set_size_abort) set_size_abort_et[autoref_ex]:
  "DETREFe m Id m' \<Longrightarrow> DETREFe s (build_rel \<alpha> invar) s'
    \<Longrightarrow> DETREFe (size_abort m s) Id (min m' (card s'))"
  by (auto simp: size_abort_correct)

lemma (in set_union) set_union_et[autoref_ex]:
  assumes "DETREFe s1 (build_rel \<alpha>1 invar1) s1'"
  assumes "DETREFe s2 (build_rel \<alpha>2 invar2) s2'"
  shows "DETREFe (union s1 s2) (build_rel \<alpha>3 invar3) (s1' \<union> s2')"
  using assms by (simp add: union_correct)

lemma (in set_union_dj) set_union_dj_et[autoref_ex]:
  assumes "s1'\<inter>s2'={}"
  assumes "DETREFe s1 (build_rel \<alpha>1 invar1) s1'"
  assumes "DETREFe s2 (build_rel \<alpha>2 invar2) s2'"
  shows "DETREFe (union_dj s1 s2) (build_rel \<alpha>3 invar3) (s1' \<union> s2')"
  using assms by (simp add: union_dj_correct)

lemma (in set_diff) set_diff_et[autoref_ex]:
  assumes "DETREFe s1 (build_rel \<alpha>1 invar1) s1'"
  assumes "DETREFe s2 (build_rel \<alpha>2 invar2) s2'"
  shows "DETREFe (diff s1 s2) (build_rel \<alpha>1 invar1) (s1'-s2')"
  using assms by (simp add: diff_correct)

lemma (in set_filter) set_filter_et[autoref_ex]:
  assumes "DETREFe P Id P'"
  assumes "DETREFe s (build_rel \<alpha>1 invar1) s'"
  shows "DETREFe (filter P s) (build_rel \<alpha>2 invar2) ({e\<in>s'. P' e})"
  using assms by (simp add: filter_correct)

lemma (in set_inter) set_inter_et[autoref_ex]:
  assumes "DETREFe s1 (build_rel \<alpha>1 invar1) s1'"
  assumes "DETREFe s2 (build_rel \<alpha>2 invar2) s2'"
  shows "DETREFe (inter s1 s2) (build_rel \<alpha>3 invar3) (s1'\<inter>s2')"
  using assms by (simp add: inter_correct)

lemma (in set_ins) set_ins_et[autoref_ex]:
  "DETREFe x Id x' \<Longrightarrow> DETREFe s (build_rel \<alpha> invar) s'
    \<Longrightarrow> DETREFe (ins x s) (build_rel \<alpha> invar) (insert x' s')"
  by (auto simp: ins_correct)

lemma (in set_ins_dj) set_ins_dj_et[autoref_ex]:
  "x'\<notin>s' \<Longrightarrow> 
    DETREFe x Id x' \<Longrightarrow> DETREFe s (build_rel \<alpha> invar) s'
    \<Longrightarrow> DETREFe (ins_dj x s) (build_rel \<alpha> invar) (insert x' s')"
  by (auto simp: ins_dj_correct)

lemma (in set_sng) set_sng_et[autoref_ex]:
  "DETREFe x Id x'
    \<Longrightarrow> DETREFe (sng x) (build_rel \<alpha> invar) ({x'})"
  by (auto simp: sng_correct)

lemma (in set_delete) set_delete_et[autoref_ex]:
  "DETREFe x Id x' \<Longrightarrow> DETREFe s (build_rel \<alpha> invar) s'
    \<Longrightarrow> DETREFe (delete x s) (build_rel \<alpha> invar) (s'-{x'})"
  by (auto simp: delete_correct)

lemma (in set_subset) set_subset_et[autoref_ex]:
  assumes "DETREFe s1 (build_rel \<alpha>1 invar1) s1'"
  assumes "DETREFe s2 (build_rel \<alpha>2 invar2) s2'"
  shows "DETREFe (subset s1 s2) Id (s1'\<subseteq>s2')"
  using assms by (simp add: subset_correct)

lemma (in set_equal) set_equal_et[autoref_ex]:
  assumes "DETREFe s1 (build_rel \<alpha>1 invar1) s1'"
  assumes "DETREFe s2 (build_rel \<alpha>2 invar2) s2'"
  shows "DETREFe (equal s1 s2) Id (s1'=s2')"
  using assms by (simp add: equal_correct)

lemma (in set_isEmpty) set_isEmpty_et[autoref_ex]:
  "DETREFe s (build_rel \<alpha> invar) s' \<Longrightarrow> DETREFe (isEmpty s) Id (s'={})"
  by (auto simp: isEmpty_correct)

lemma (in set_isSng) set_isSng_et[autoref_ex]:
  "DETREFe s (build_rel \<alpha> invar) s' \<Longrightarrow> DETREFe (isSng s) Id (\<exists>e. s'={e})"
  by (auto simp: isSng_correct)

lemma (in set_disjoint) set_disjoint_et[autoref_ex]:
  assumes "DETREFe s1 (build_rel \<alpha>1 invar1) s1'"
  assumes "DETREFe s2 (build_rel \<alpha>2 invar2) s2'"
  shows "DETREFe (disjoint s1 s2) Id (s1'\<inter>s2'={})"
  using assms by (simp add: disjoint_correct)

thm set_disjoint_witness.disjoint_witness_correct
lemma (in set_disjoint_witness) set_disjoint_witness_et[autoref_ex]:
  assumes "DETREFe s1 (build_rel \<alpha>1 invar1) s1'"
  assumes "DETREFe s2 (build_rel \<alpha>2 invar2) s2'"
  shows "RETURN (disjoint_witness s1 s2) \<le> \<Down>Id (SPEC 
    (\<lambda>r. if (s1'\<inter>s2'={}) then r=None else (\<exists>e\<in>s1'\<inter>s2'. r=Some e)))"
  using assms
  apply -
  apply (simp, intro impI conjI)
  apply (simp add: disjoint_witness_None)
  apply (elim conjE)
  apply (cases "disjoint_witness s1 s2")
  apply (drule (2) disjoint_witness_correct) apply blast
  apply (drule (2) disjoint_witness_correct) apply blast
  done

lemma (in set_sel') set_sel'_et[autoref_ex]:
  assumes "DETREFe P Id P'"
  assumes "DETREFe s (build_rel \<alpha> invar) s'"
  shows "RETURN (sel' s P) \<le>\<Down>Id 
    (SPEC (\<lambda>r. if (\<forall>x\<in>s'. \<not> P' x) then r=None else (\<exists>x\<in>s'. P' x \<and> r=Some x)))"
  using assms apply -
  apply (cases "sel' s P")
  apply (auto dest: sel'_someD sel'_noneD)
  done

lemma (in set_to_list) set_to_list_et[autoref_ex]:
  assumes "DETREFe s (build_rel \<alpha> invar) s'"
  shows "RETURN (to_list s) \<le>\<Down>Id (SPEC (\<lambda>l. set l = s' \<and> distinct l))"
  using assms to_list_correct by auto

lemma (in list_to_set) list_to_set_et[autoref_ex]:
  assumes "DETREFe l Id l'"
  shows "DETREFe (to_set l) (build_rel \<alpha> invar) (set l')"
  using assms by (auto simp: to_set_correct)

lemma (in set_sel') pick_et[autoref_ex]:
  assumes "s'\<noteq>{}"
  assumes "DETREFe s (build_rel \<alpha> invar) s'"
  shows "RETURN (the (sel' s (\<lambda>_. True))) \<le>\<Down>Id (SPEC (\<lambda>x. x\<in>s'))"
  using assms by (auto elim!: sel'E)

subsection "Map"
text {* TODO: Still incomplete *}
lemma (in map_empty) map_empty_t[autoref_ex]:
  "DETREFe (empty ()) (build_rel \<alpha> invar) Map.empty"
  by (auto simp: empty_correct)

(* TODO: This may cause a mess with higher-order unification!
    Do not enable by default, but only add for required types,
    as specifically instantiated as possible!
 *)
lemma (in map_lookup) map_lookup_t:
  assumes "DETREFe k Id k'"
  assumes "DETREFe m (build_rel \<alpha> invar) m'"
  shows "DETREFe (lookup k m) Id (m' k')"
  using assms by (auto simp: lookup_correct)

lemma (in map_update) map_update_t[autoref_ex]:
  assumes "DETREFe k Id k'"
  assumes "DETREFe v Id v'"
  assumes "DETREFe m (build_rel \<alpha> invar) m'"
  shows "DETREFe (update k v m) (build_rel \<alpha> invar) (m'(k'\<mapsto>v'))"
  using assms by (auto simp: update_correct)

lemma (in map_sng) map_sng_t[autoref_ex]:
  assumes "DETREFe k Id k'"
  assumes "DETREFe v Id v'"
  shows "DETREFe (sng k v) (build_rel \<alpha> invar) [k'\<mapsto>v']"
  using assms by (auto simp: sng_correct)


subsection "Unique Priority Queue"
text {* TODO: Still incomplete *}

lemma (in uprio_empty) uprio_empty_t[autoref_ex]:
  "DETREFe (empty ()) (build_rel \<alpha> invar) Map.empty"
  by (auto simp: empty_correct)

lemma (in uprio_isEmpty) uprio_isEmpty_t[autoref_ex]:
  assumes "DETREFe s (build_rel \<alpha> invar) s'"
  shows 
    "DETREFe (isEmpty s) Id (s'=Map.empty)"
    "DETREFe (isEmpty s) Id (dom s'={})"
  using assms by (auto simp: isEmpty_correct)

lemma (in uprio_insert) uprio_insert_t[autoref_ex]:
  assumes "DETREFe s (build_rel \<alpha> invar) s'"
  assumes "DETREFe e Id e'"
  assumes "DETREFe a Id a'"
  shows "DETREFe (insert s e a) (build_rel \<alpha> invar) (s'(e' \<mapsto> a'))"
  using assms by (simp add: insert_correct)

lemma (in uprio_pop) uprio_pop_t[autoref_ex]:
  assumes "dom q'\<noteq>{}"
  assumes "DETREFe q (build_rel \<alpha> invar) q'"
  shows "RETURN (pop q) \<le> \<Down>(rprod Id (rprod Id (build_rel \<alpha> invar)))
           (SPEC (\<lambda>(e, w, rq').
            rq' = q'(e := None) \<and>
            q' e = Some w \<and> (\<forall>e' w'. q' e' = Some w' \<longrightarrow> w \<le> w')))"
  apply (rule SPEC_refine_sv)
  apply (intro rprod_sv single_valued_Id br_single_valued)
  using assms
  apply auto
  apply (erule (1) popE)
  apply (auto simp: ran_def)
  done

  hide_const (open) DETREFe
end
