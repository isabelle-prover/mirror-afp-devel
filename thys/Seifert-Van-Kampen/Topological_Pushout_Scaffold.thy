theory Topological_Pushout_Scaffold
  imports Binary_Sum_Topology Pushout_Scaffold
begin

section \<open>Topological pushouts\<close>

text \<open>
  The quotient-level pushout relation from \<open>Pushout_Scaffold\<close> becomes a
  genuine topological pushout here. The theory defines the quotient topology on
  the glued disjoint sum and proves the universal maps from the two summands
  into that topological pushout.
\<close>

definition pushout_topspace ::
  "'a topology => 'b topology => ('c => 'a) => ('c => 'b) => ('a + 'b) set set"
where
  "pushout_topspace X Y f g = pushout_class f g ` topspace (binary_sum_topology X Y)"

definition pushout_topology ::
  "'a topology => 'b topology => ('c => 'a) => ('c => 'b) => (('a + 'b) set) topology"
where
  "pushout_topology X Y f g =
     topology (\<lambda>U.
       U \<subseteq> pushout_topspace X Y f g \<and>
       openin (binary_sum_topology X Y)
         {z \<in> topspace (binary_sum_topology X Y). pushout_class f g z \<in> U})"

lemma pushout_topspace_alt:
  "pushout_topspace X Y f g = pushout_inl f g ` topspace X \<union> pushout_inr f g ` topspace Y"
  unfolding pushout_topspace_def pushout_inl_def pushout_inr_def topspace_binary_sum_topology
  by auto

lemma pushout_topspace_subset_pushout_space:
  "pushout_topspace X Y f g \<subseteq> pushout_space f g"
  unfolding pushout_topspace_def pushout_space_def pushout_class_def quotient_space_def
  by blast

lemma is_pushout_topology:
  "istopology (\<lambda>U.
      U \<subseteq> pushout_topspace X Y f g \<and>
      openin (binary_sum_topology X Y)
        {z \<in> topspace (binary_sum_topology X Y). pushout_class f g z \<in> U})"
proof -
  have Int_eq:
    "{z \<in> topspace (binary_sum_topology X Y). pushout_class f g z \<in> S \<inter> T} =
      {z \<in> topspace (binary_sum_topology X Y). pushout_class f g z \<in> S} \<inter>
      {z \<in> topspace (binary_sum_topology X Y). pushout_class f g z \<in> T}" for S T
    by auto
  have Union_eq:
    "{z \<in> topspace (binary_sum_topology X Y). pushout_class f g z \<in> \<Union>\<K>} =
      (\<Union>U\<in>\<K>. {z \<in> topspace (binary_sum_topology X Y). pushout_class f g z \<in> U})" for \<K>
    by auto
  show ?thesis
    unfolding istopology_def pushout_topspace_def Int_eq Union_eq
    by blast
qed

lemma openin_pushout_topology:
  "openin (pushout_topology X Y f g) U \<longleftrightarrow>
    U \<subseteq> pushout_topspace X Y f g \<and>
    openin (binary_sum_topology X Y)
      {z \<in> topspace (binary_sum_topology X Y). pushout_class f g z \<in> U}"
proof -
  have "openin (pushout_topology X Y f g) U =
      (U \<subseteq> pushout_topspace X Y f g \<and>
       openin (binary_sum_topology X Y)
         {z \<in> topspace (binary_sum_topology X Y). pushout_class f g z \<in> U})"
    unfolding pushout_topology_def
    by (subst topology_inverse'[OF is_pushout_topology]) simp
  then show ?thesis
    by simp
qed

lemma topspace_pushout_topology [simp]:
  "topspace (pushout_topology X Y f g) = pushout_topspace X Y f g"
proof
  have top_open: "openin (pushout_topology X Y f g) (topspace (pushout_topology X Y f g))"
    by simp
  show "topspace (pushout_topology X Y f g) \<subseteq> pushout_topspace X Y f g"
    using top_open unfolding openin_pushout_topology by blast
  have preimage_space:
    "{z \<in> topspace (binary_sum_topology X Y). pushout_class f g z \<in> pushout_topspace X Y f g} =
      topspace (binary_sum_topology X Y)"
    unfolding pushout_topspace_def by auto
  have open_top: "openin (binary_sum_topology X Y) (topspace (binary_sum_topology X Y))"
    by (rule openin_topspace)
  have "openin (pushout_topology X Y f g) (pushout_topspace X Y f g)"
    unfolding openin_pushout_topology preimage_space
    using open_top by simp
  then show "pushout_topspace X Y f g \<subseteq> topspace (pushout_topology X Y f g)"
    by (rule openin_subset)
qed

lemma quotient_map_pushout_class:
  "quotient_map (binary_sum_topology X Y) (pushout_topology X Y f g) (pushout_class f g)"
proof (unfold quotient_map_def, intro conjI allI impI)
  show "pushout_class f g ` topspace (binary_sum_topology X Y) = topspace (pushout_topology X Y f g)"
    by (auto simp: pushout_topspace_alt pushout_inl_def pushout_inr_def image_Un)
next
  fix U
  assume U: "U \<subseteq> topspace (pushout_topology X Y f g)"
  then have U': "U \<subseteq> pushout_topspace X Y f g"
    by simp
  show "openin (binary_sum_topology X Y)
          {x \<in> topspace (binary_sum_topology X Y). pushout_class f g x \<in> U} =
        openin (pushout_topology X Y f g) U"
    using U' by (simp add: openin_pushout_topology)
qed

lemma continuous_map_pushout_class:
  "continuous_map (binary_sum_topology X Y) (pushout_topology X Y f g) (pushout_class f g)"
  using quotient_map_pushout_class by (rule quotient_imp_continuous_map)

lemma pushout_inl_in_topspace:
  assumes "a \<in> topspace X"
  shows "pushout_inl f g a \<in> pushout_topspace X Y f g"
  using assms
  unfolding pushout_topspace_def pushout_inl_def topspace_binary_sum_topology
  by auto

lemma pushout_inr_in_topspace:
  assumes "b \<in> topspace Y"
  shows "pushout_inr f g b \<in> pushout_topspace X Y f g"
  using assms
  unfolding pushout_topspace_def pushout_inr_def topspace_binary_sum_topology
  by auto

lemma continuous_map_pushout_inl [continuous_intros]:
  "continuous_map X (pushout_topology X Y f g) (pushout_inl f g)"
proof -
  have "continuous_map X (pushout_topology X Y f g)
          (pushout_class f g \<circ> (Inl :: 'a \<Rightarrow> 'a + 'b))"
    using continuous_map_binary_sum_inl continuous_map_pushout_class
    by (rule continuous_map_compose)
  then show ?thesis
    unfolding pushout_inl_def o_def
    by (rule continuous_map_eq) auto
qed

lemma continuous_map_pushout_inr [continuous_intros]:
  "continuous_map Y (pushout_topology X Y f g) (pushout_inr f g)"
proof -
  have inr_cont: "continuous_map Y (binary_sum_topology X Y) (\<lambda>b. Inr b)"
    using continuous_map_binary_sum_inr
    by (rule continuous_map_eq) auto
  have "continuous_map Y (pushout_topology X Y f g)
          (pushout_class f g \<circ> (\<lambda>b. Inr b))"
    using inr_cont continuous_map_pushout_class
    by (rule continuous_map_compose)
  then show ?thesis
    unfolding pushout_inr_def o_def
    by (rule continuous_map_eq) auto
qed

lemma pushout_rec_pushout_class:
  assumes compat: "pushout_case_compatible f g left right"
    and x_in: "x \<in> topspace (binary_sum_topology X Y)"
  shows "pushout_rec f g left right (pushout_class f g x) = case_sum left right x"
proof -
  from x_in have "(\<exists>a\<in>topspace X. x = Inl a) \<or> (\<exists>b\<in>topspace Y. x = Inr b)"
    by (auto simp: topspace_binary_sum_topology)
  then show ?thesis
  proof
    assume "\<exists>a\<in>topspace X. x = Inl a"
    then obtain a where "a \<in> topspace X" "x = Inl a"
      by blast
    then show ?thesis
      using pushout_rec_inl[OF compat, of a]
      unfolding pushout_inl_def by simp
  next
    assume "\<exists>b\<in>topspace Y. x = Inr b"
    then obtain b where "b \<in> topspace Y" "x = Inr b"
      by blast
    then show ?thesis
      using pushout_rec_inr[OF compat, of b]
      unfolding pushout_inr_def by simp
  qed
qed

lemma continuous_map_pushout_rec:
  assumes compat: "pushout_case_compatible f g left right"
    and left_cont: "continuous_map X Z left"
    and right_cont: "continuous_map Y Z right"
  shows "continuous_map (pushout_topology X Y f g) Z (pushout_rec f g left right)"
proof -
  have sum_cont: "continuous_map (binary_sum_topology X Y) Z (case_sum left right)"
    using left_cont right_cont by (rule continuous_map_from_binary_sum_topology)
  have comp_eq:
    "((pushout_rec f g left right) \<circ> pushout_class f g) x = case_sum left right x"
    if "x \<in> topspace (binary_sum_topology X Y)" for x
    using pushout_rec_pushout_class[OF compat that] by (simp add: o_def)
  have comp_eq':
    "case_sum left right x = ((pushout_rec f g left right) \<circ> pushout_class f g) x"
    if "x \<in> topspace (binary_sum_topology X Y)" for x
    using comp_eq[OF that] by simp
  have comp_cont:
    "continuous_map (binary_sum_topology X Y) Z ((pushout_rec f g left right) \<circ> pushout_class f g)"
    using sum_cont comp_eq' by (rule continuous_map_eq)
  show ?thesis
    using quotient_map_pushout_class comp_cont by (rule continuous_compose_quotient_map)
qed

lemma pushout_rec_universal:
  assumes compat: "pushout_case_compatible f g left right"
    and left_cont: "continuous_map X Z left"
    and right_cont: "continuous_map Y Z right"
  shows "continuous_map (pushout_topology X Y f g) Z (pushout_rec f g left right)"
    and "\<And>a. pushout_rec f g left right (pushout_inl f g a) = left a"
    and "\<And>b. pushout_rec f g left right (pushout_inr f g b) = right b"
  using assms
  by (auto intro: continuous_map_pushout_rec simp: pushout_rec_inl pushout_rec_inr)

end
