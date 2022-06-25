theory Mapping_Code
  imports "Containers.Mapping_Impl"
begin

lift_definition set_of_idx :: "('a, 'b set) mapping \<Rightarrow> 'b set" is
  "\<lambda>m. \<Union>(ran m)" .

lemma set_of_idx_code[code]:
  fixes t :: "('a :: ccompare, 'b set) mapping_rbt"
  shows "set_of_idx (RBT_Mapping t) =
    (case ID CCOMPARE('a) of None \<Rightarrow> Code.abort (STR ''set_of_idx RBT_Mapping: ccompare = None'') (\<lambda>_. set_of_idx (RBT_Mapping t))
    | Some _ \<Rightarrow> \<Union>(snd ` set (RBT_Mapping2.entries t)))"
  unfolding RBT_Mapping_def
  by transfer (auto simp: ran_def rbt_comp_lookup[OF ID_ccompare'] ord.is_rbt_def linorder.rbt_lookup_in_tree[OF comparator.linorder[OF ID_ccompare']] split: option.splits)+

lemma mapping_combine[code]:
  fixes t :: "('a :: ccompare, 'b) mapping_rbt"
  shows "Mapping.combine f (RBT_Mapping t) (RBT_Mapping u) =
    (case ID CCOMPARE('a) of None \<Rightarrow> Code.abort (STR ''combine RBT_Mapping: ccompare = None'') (\<lambda>_. Mapping.combine f (RBT_Mapping t) (RBT_Mapping u))
    | Some _ \<Rightarrow> RBT_Mapping (RBT_Mapping2.join (\<lambda>_. f) t u))"
  by (auto simp add: Mapping.combine.abs_eq Mapping_inject lookup_join split: option.split)

lift_definition mapping_join :: "('b \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> ('a, 'b) mapping \<Rightarrow> ('a, 'b) mapping \<Rightarrow> ('a, 'b) mapping" is
  "\<lambda>f m m' x. case m x of None \<Rightarrow> None | Some y \<Rightarrow> (case m' x of None \<Rightarrow> None | Some y' \<Rightarrow> Some (f y y'))" .

lemma mapping_join_code[code]:
  fixes t :: "('a :: ccompare, 'b) mapping_rbt"
  shows "mapping_join f (RBT_Mapping t) (RBT_Mapping u) =
    (case ID CCOMPARE('a) of None \<Rightarrow> Code.abort (STR ''mapping_join RBT_Mapping: ccompare = None'') (\<lambda>_. mapping_join f (RBT_Mapping t) (RBT_Mapping u))
    | Some _ \<Rightarrow> RBT_Mapping (RBT_Mapping2.meet (\<lambda>_. f) t u))"
  by (auto simp add: mapping_join.abs_eq Mapping_inject lookup_meet split: option.split)

context fixes dummy :: "'a :: ccompare" begin

lift_definition diff ::
  "('a, 'b) mapping_rbt \<Rightarrow> ('a, 'b) mapping_rbt \<Rightarrow> ('a, 'b) mapping_rbt" is "rbt_comp_minus ccomp"
  by (auto 4 3 intro: linorder.rbt_minus_is_rbt ID_ccompare ord.is_rbt_rbt_sorted simp: rbt_comp_minus[OF ID_ccompare'])

end

context assumes ID_ccompare_neq_None: "ID CCOMPARE('a :: ccompare) \<noteq> None"
begin

lemma lookup_diff:
  "RBT_Mapping2.lookup (diff (t1 :: ('a, 'b) mapping_rbt) t2) =
  (\<lambda>k. case RBT_Mapping2.lookup t1 k of None \<Rightarrow> None | Some v1 \<Rightarrow> (case RBT_Mapping2.lookup t2 k of None \<Rightarrow> Some v1 | Some v2 \<Rightarrow> None))"
  by transfer (auto simp add: fun_eq_iff linorder.rbt_lookup_rbt_minus[OF mapping_linorder] ID_ccompare_neq_None restrict_map_def split: option.splits)

end

lift_definition mapping_antijoin :: "('a, 'b) mapping \<Rightarrow> ('a, 'b) mapping \<Rightarrow> ('a, 'b) mapping" is
  "\<lambda>m m' x. case m x of None \<Rightarrow> None | Some y \<Rightarrow> (case m' x of None \<Rightarrow> Some y | Some y' \<Rightarrow> None)" .

lemma mapping_antijoin_code[code]:
  fixes t :: "('a :: ccompare, 'b) mapping_rbt"
  shows "mapping_antijoin (RBT_Mapping t) (RBT_Mapping u) =
    (case ID CCOMPARE('a) of None \<Rightarrow> Code.abort (STR ''mapping_antijoin RBT_Mapping: ccompare = None'') (\<lambda>_. mapping_antijoin (RBT_Mapping t) (RBT_Mapping u))
    | Some _ \<Rightarrow> RBT_Mapping (diff t u))"
  by (auto simp add: mapping_antijoin.abs_eq Mapping_inject lookup_diff split: option.split)

end