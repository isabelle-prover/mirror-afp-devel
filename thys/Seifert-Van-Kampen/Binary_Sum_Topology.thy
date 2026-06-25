theory Binary_Sum_Topology
  imports "HOL-Analysis.Abstract_Topology"
begin

section \<open>Binary coproduct topology\<close>

text \<open>
  Topological pushouts are constructed by first equipping the disjoint sum with
  its coproduct topology and only then quotienting by the glue relation. This
  short theory records that coproduct topology together with the basic
  continuity lemmas used by the later pushout arguments.
\<close>

definition binary_sum_topology :: "'a topology => 'b topology => ('a + 'b) topology"
where
  "binary_sum_topology X Y =
     topology (\<lambda>U.
       U \<subseteq> Inl ` topspace X \<union> Inr ` topspace Y \<and>
       openin X {x. Inl x \<in> U} \<and>
       openin Y {y. Inr y \<in> U})"

lemma is_binary_sum_topology:
  "istopology (\<lambda>U.
      U \<subseteq> Inl ` topspace X \<union> Inr ` topspace Y \<and>
      openin X {x. Inl x \<in> U} \<and>
      openin Y {y. Inr y \<in> U})"
proof -
  have inl_Int: "{x. Inl x \<in> S \<inter> T} = {x. Inl x \<in> S} \<inter> {x. Inl x \<in> T}" for S T
    by auto
  have inr_Int: "{y. Inr y \<in> S \<inter> T} = {y. Inr y \<in> S} \<inter> {y. Inr y \<in> T}" for S T
    by auto
  have inl_Union: "{x. Inl x \<in> \<Union>\<K>} = (\<Union>U\<in>\<K>. {x. Inl x \<in> U})" for \<K>
    by auto
  have inr_Union: "{y. Inr y \<in> \<Union>\<K>} = (\<Union>U\<in>\<K>. {y. Inr y \<in> U})" for \<K>
    by auto
  show ?thesis
    unfolding istopology_def inl_Int inr_Int inl_Union inr_Union
    by blast
qed

lemma openin_binary_sum_topology:
  "openin (binary_sum_topology X Y) U \<longleftrightarrow>
    U \<subseteq> Inl ` topspace X \<union> Inr ` topspace Y \<and>
    openin X {x. Inl x \<in> U} \<and>
    openin Y {y. Inr y \<in> U}"
  by (auto simp: binary_sum_topology_def is_binary_sum_topology)

lemma topspace_binary_sum_topology [simp]:
  "topspace (binary_sum_topology X Y) = Inl ` topspace X \<union> Inr ` topspace Y"
proof
  have top_open: "openin (binary_sum_topology X Y) (topspace (binary_sum_topology X Y))"
    by simp
  show "topspace (binary_sum_topology X Y) \<subseteq> Inl ` topspace X \<union> Inr ` topspace Y"
    using top_open unfolding openin_binary_sum_topology by blast
  have eqX: "{x. Inl x \<in> Inl ` topspace X \<union> Inr ` topspace Y} = topspace X"
    by auto
  have eqY: "{y. Inr y \<in> Inl ` topspace X \<union> Inr ` topspace Y} = topspace Y"
    by auto
  have "openin (binary_sum_topology X Y) (Inl ` topspace X \<union> Inr ` topspace Y)"
    unfolding openin_binary_sum_topology eqX eqY by simp
  then show "Inl ` topspace X \<union> Inr ` topspace Y \<subseteq> topspace (binary_sum_topology X Y)"
    by (rule openin_subset)
qed

lemma subset_topspace_binary_sum_inl:
  "(Inl :: 'a \<Rightarrow> 'a + 'b) ` topspace X \<subseteq> topspace (binary_sum_topology X Y)"
  by simp

lemma subset_topspace_binary_sum_inr:
  "(Inr :: 'b \<Rightarrow> 'a + 'b) ` topspace Y \<subseteq> topspace (binary_sum_topology X Y)"
  by simp

lemma continuous_map_binary_sum_inl:
  "continuous_map X (binary_sum_topology X Y) (Inl :: 'a \<Rightarrow> 'a + 'b)"
proof -
  have image: "(Inl :: 'a \<Rightarrow> 'a + 'b) ` topspace X \<subseteq> topspace (binary_sum_topology X Y)"
    by simp
  have preimage:
    "\<forall>U. openin (binary_sum_topology X Y) U \<longrightarrow> openin X {x \<in> topspace X. Inl x \<in> U}"
  proof (intro allI impI)
    fix U
    assume U: "openin (binary_sum_topology X Y) U"
    have openU: "openin X {x. Inl x \<in> U}"
      using U by (simp add: openin_binary_sum_topology)
    have subsetX: "{x. Inl x \<in> U} \<subseteq> topspace X"
      using openU by (rule openin_subset)
    have eq: "{x \<in> topspace X. Inl x \<in> U} = {x. Inl x \<in> U}"
      using subsetX by auto
    have "openin X {x \<in> topspace X. Inl x \<in> U}"
      unfolding eq using openU by simp
    then show "openin X {x \<in> topspace X. Inl x \<in> U}" .
  qed
  from image preimage show ?thesis
    by (simp add: continuous_map)
qed

lemma continuous_map_binary_sum_inr:
  "continuous_map Y (binary_sum_topology X Y) (Inr :: 'b \<Rightarrow> 'a + 'b)"
proof -
  have image: "(Inr :: 'b \<Rightarrow> 'a + 'b) ` topspace Y \<subseteq> topspace (binary_sum_topology X Y)"
    by simp
  have preimage:
    "\<forall>U. openin (binary_sum_topology X Y) U \<longrightarrow> openin Y {y \<in> topspace Y. Inr y \<in> U}"
  proof (intro allI impI)
    fix U
    assume U: "openin (binary_sum_topology X Y) U"
    have openU: "openin Y {y. Inr y \<in> U}"
      using U by (simp add: openin_binary_sum_topology)
    have subsetY: "{y. Inr y \<in> U} \<subseteq> topspace Y"
      using openU by (rule openin_subset)
    have eq: "{y \<in> topspace Y. Inr y \<in> U} = {y. Inr y \<in> U}"
      using subsetY by auto
    have "openin Y {y \<in> topspace Y. Inr y \<in> U}"
      unfolding eq using openU by simp
    then show "openin Y {y \<in> topspace Y. Inr y \<in> U}" .
  qed
  from image preimage show ?thesis
    by (simp add: continuous_map)
qed

lemma open_map_binary_sum_inl:
  "open_map X (binary_sum_topology X Y) (Inl :: 'a \<Rightarrow> 'a + 'b)"
  unfolding open_map_def openin_binary_sum_topology
  using openin_subset openin_subopen by (force simp: image_iff)

lemma open_map_binary_sum_inr:
  "open_map Y (binary_sum_topology X Y) (Inr :: 'b \<Rightarrow> 'a + 'b)"
  unfolding open_map_def openin_binary_sum_topology
  using openin_subset openin_subopen by (force simp: image_iff)

lemma continuous_map_from_binary_sum_topology:
  assumes f: "continuous_map X Z f"
    and g: "continuous_map Y Z g"
  shows "continuous_map (binary_sum_topology X Y) Z (case_sum f g)"
proof -
  from f have f_image: "f ` topspace X \<subseteq> topspace Z"
    by (simp add: continuous_map)
  from g have g_image: "g ` topspace Y \<subseteq> topspace Z"
    by (simp add: continuous_map)
  have case_image:
    "case_sum f g ` topspace (binary_sum_topology X Y) = f ` topspace X \<union> g ` topspace Y"
  proof
    show "case_sum f g ` topspace (binary_sum_topology X Y) \<subseteq> f ` topspace X \<union> g ` topspace Y"
      by (auto simp: topspace_binary_sum_topology)
    show "f ` topspace X \<union> g ` topspace Y \<subseteq> case_sum f g ` topspace (binary_sum_topology X Y)"
    proof
      fix z
      assume "z \<in> f ` topspace X \<union> g ` topspace Y"
      then consider
        (left) x where "x \<in> topspace X" "z = f x"
      | (right) y where "y \<in> topspace Y" "z = g y"
        by auto
      then show "z \<in> case_sum f g ` topspace (binary_sum_topology X Y)"
      proof cases
        case (left x)
        have "Inl x \<in> topspace (binary_sum_topology X Y)"
          using left by (auto simp: topspace_binary_sum_topology)
        then have "case_sum f g (Inl x) \<in> case_sum f g ` topspace (binary_sum_topology X Y)"
          by (rule imageI)
        then show ?thesis
          using left by simp
      next
        case (right y)
        have "Inr y \<in> topspace (binary_sum_topology X Y)"
          using right by (auto simp: topspace_binary_sum_topology)
        then have "case_sum f g (Inr y) \<in> case_sum f g ` topspace (binary_sum_topology X Y)"
          by (rule imageI)
        then show ?thesis
          using right by simp
      qed
    qed
  qed
  have image: "case_sum f g ` topspace (binary_sum_topology X Y) \<subseteq> topspace Z"
  proof -
    have case_subset: "f ` topspace X \<union> g ` topspace Y \<subseteq> topspace Z"
      using f_image g_image by blast
    from case_image case_subset show ?thesis
      by blast
  qed
  have preimage:
    "\<forall>U. openin Z U \<longrightarrow>
      openin (binary_sum_topology X Y) {z \<in> topspace (binary_sum_topology X Y). case_sum f g z \<in> U}"
  proof (intro allI impI)
    fix U
    assume U: "openin Z U"
    from f U have openX: "openin X {x \<in> topspace X. f x \<in> U}"
      by (simp add: continuous_map)
    from g U have openY: "openin Y {y \<in> topspace Y. g y \<in> U}"
      by (simp add: continuous_map)
    let ?W = "{z \<in> topspace (binary_sum_topology X Y). case_sum f g z \<in> U}"
    have subsetW: "?W \<subseteq> topspace (binary_sum_topology X Y)"
      by auto
    have eqX: "{x. Inl x \<in> ?W} = {x \<in> topspace X. f x \<in> U}"
      by auto
    have eqY: "{y. Inr y \<in> ?W} = {y \<in> topspace Y. g y \<in> U}"
      by auto
    show "openin (binary_sum_topology X Y) ?W"
      unfolding openin_binary_sum_topology eqX eqY
      using subsetW openX openY by simp
  qed
  from image preimage show ?thesis
    by (simp add: continuous_map)
qed

end
