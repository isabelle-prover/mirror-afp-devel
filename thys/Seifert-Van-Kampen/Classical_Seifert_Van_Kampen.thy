theory Classical_Seifert_Van_Kampen
  imports
    Carrier_Amalgamated_Free_Product_Eval
    Explicit_Fundamental_Group_Scaffold
    Seifert_Van_Kampen_Scaffold
begin

section \<open>Classical Seifert--van Kampen for open unions\<close>

text \<open>
  This theory specializes the general encode/decode interface to the classical
  open-cover hypotheses. Its long middle portion constructs encodings of loops
  by subdividing them into pieces that lie in \<open>U\<close> or \<open>V\<close>, proves invariance
  under refinement and homotopy, and then packages the resulting quotient as the
  carrier-based amalgamated free product of the three relevant fundamental
  groups.
\<close>

lemma path_top_of_setI:
  assumes "path p"
    and "path_image p \<subseteq> S"
  shows "pathin (top_of_set S) p"
  using assms
  by (auto simp: pathin_canon_iff path_image_def image_subset_iff_funcset)

locale classical_svk_setup =
  fixes U :: "'a::topological_space set"
    and V :: "'a set"
    and x0 :: "'a"
  assumes U_open: "open U"
    and V_open: "open V"
    and x0_in: "x0 \<in> U \<inter> V"
    and UV_path_connected: "path_connected (U \<inter> V)"
begin

abbreviation W where "W \<equiv> U \<union> V"

abbreviation G1 where "G1 \<equiv> fundamental_group_space U x0"
abbreviation G2 where "G2 \<equiv> fundamental_group_space V x0"
abbreviation H where "H \<equiv> fundamental_group_space (U \<inter> V) x0"

abbreviation mult1 where "mult1 \<equiv> fundamental_group_mult U x0"
abbreviation one1 where "one1 \<equiv> fundamental_group_one U x0"
abbreviation mult2 where "mult2 \<equiv> fundamental_group_mult V x0"
abbreviation one2 where "one2 \<equiv> fundamental_group_one V x0"
abbreviation multW where "multW \<equiv> fundamental_group_mult W x0"
abbreviation oneW where "oneW \<equiv> fundamental_group_one W x0"

abbreviation i1 where "i1 \<equiv> fundamental_group_map (U \<inter> V) x0 U x0 id"
abbreviation i2 where "i2 \<equiv> fundamental_group_map (U \<inter> V) x0 V x0 id"
abbreviation j1 where "j1 \<equiv> fundamental_group_map U x0 W x0 id"
abbreviation j2 where "j2 \<equiv> fundamental_group_map V x0 W x0 id"

subsection \<open>Carrier-side setup\<close>

text \<open>
  The first part of the theory fixes the inclusion-induced maps between the
  three fundamental groups and packages them into the carrier-side evaluation
  locale used by the later decode map. This isolates the algebraic compatibility
  conditions that are immediate from the open-union inclusions.
\<close>

lemma x0_in_U [simp]: "x0 \<in> U"
  using x0_in by blast

lemma x0_in_V [simp]: "x0 \<in> V"
  using x0_in by blast

lemma x0_in_W [simp]: "x0 \<in> W"
  using x0_in by blast

lemma x0_in_UV [simp]: "x0 \<in> U \<inter> V"
  using x0_in by blast

lemma i1_in_G1:
  assumes "h \<in> H"
  shows "i1 h \<in> G1"
  by (rule fundamental_group_map_in_space[OF assms]) auto

lemma i2_in_G2:
  assumes "h \<in> H"
  shows "i2 h \<in> G2"
  by (rule fundamental_group_map_in_space[OF assms]) auto

lemma union_fundamental_group_maps_agree:
  assumes h_in: "h \<in> H"
  shows "j1 (i1 h) = j2 (i2 h)"
proof -
  have left_comp:
    "fundamental_group_map U x0 W x0 id
      (fundamental_group_map (U \<inter> V) x0 U x0 id h) =
      fundamental_group_map (U \<inter> V) x0 W x0 (id \<circ> id) h"
    by (rule fundamental_group_map_compose[OF h_in]) auto
  have right_comp:
    "fundamental_group_map V x0 W x0 id
      (fundamental_group_map (U \<inter> V) x0 V x0 id h) =
      fundamental_group_map (U \<inter> V) x0 W x0 (id \<circ> id) h"
    by (rule fundamental_group_map_compose[OF h_in]) auto
  show ?thesis
    using left_comp right_comp by simp
qed

lemma decode_locale:
  "carrier_full_amalg_word_eval
    G1 mult1 one1 (fundamental_group_inv U x0)
    G2 mult2 one2 (fundamental_group_inv V x0)
    H i1 i2
    (fundamental_group_space W x0) multW oneW (fundamental_group_inv W x0)
    j1 j2"
proof (rule carrier_full_amalg_word_eval.intro)
  show "carrier_group
      (fundamental_group_space U x0)
      (fundamental_group_mult U x0)
      (fundamental_group_one U x0)
      (fundamental_group_inv U x0)"
    by (rule fundamental_group_carrier_group[OF x0_in_U])
  show "carrier_group
      (fundamental_group_space V x0)
      (fundamental_group_mult V x0)
      (fundamental_group_one V x0)
      (fundamental_group_inv V x0)"
    by (rule fundamental_group_carrier_group[OF x0_in_V])
  show "carrier_group
      (fundamental_group_space W x0)
      (fundamental_group_mult W x0)
      (fundamental_group_one W x0)
      (fundamental_group_inv W x0)"
    by (rule fundamental_group_carrier_group[OF x0_in_W])
  show "carrier_group_hom
      (fundamental_group_space U x0)
      (fundamental_group_mult U x0)
      (fundamental_group_one U x0)
      (fundamental_group_inv U x0)
      (fundamental_group_space W x0)
      (fundamental_group_mult W x0)
      (fundamental_group_one W x0)
      (fundamental_group_inv W x0)
      (fundamental_group_map U x0 W x0 id)"
    by (rule fundamental_group_map_carrier_group_hom[OF x0_in_U]) auto
  show "carrier_group_hom
      (fundamental_group_space V x0)
      (fundamental_group_mult V x0)
      (fundamental_group_one V x0)
      (fundamental_group_inv V x0)
      (fundamental_group_space W x0)
      (fundamental_group_mult W x0)
      (fundamental_group_one W x0)
      (fundamental_group_inv W x0)
      (fundamental_group_map V x0 W x0 id)"
    by (rule fundamental_group_map_carrier_group_hom[OF x0_in_V]) auto
  show "carrier_full_amalg_word_eval_axioms G1 G2 H i1 i2 j1 j2"
  proof (rule carrier_full_amalg_word_eval_axioms.intro)
    show "h \<in> H \<Longrightarrow> i1 h \<in> G1" for h
      by (rule i1_in_G1)
    show "h \<in> H \<Longrightarrow> i2 h \<in> G2" for h
      by (rule i2_in_G2)
    show "h \<in> H \<Longrightarrow> j1 (i1 h) = j2 (i2 h)" for h
      by (rule union_fundamental_group_maps_agree)
  qed
qed

interpretation decode:
  carrier_full_amalg_word_eval
    G1 mult1 one1 "fundamental_group_inv U x0"
    G2 mult2 one2 "fundamental_group_inv V x0"
    H i1 i2
    "fundamental_group_space W x0" multW oneW "fundamental_group_inv W x0"
    j1 j2
  by (rule decode_locale)

abbreviation svk_word_eval where "svk_word_eval \<equiv> decode.carrier_full_amalg_eval"
abbreviation svk_decode where "svk_decode \<equiv> decode.carrier_full_amalg_decode"

lemma svk_decode_in_space:
  "svk_decode w \<in> fundamental_group_space W x0"
  by (rule decode.carrier_full_amalg_decode_in_carrier)

lemma svk_decode_respects:
  assumes "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2 u v"
  shows "svk_decode u = svk_decode v"
  using assms by (rule decode.carrier_full_amalg_decode_respects)

lemma svk_decode_eq_eval:
  assumes "fpw_in_space G1 G2 w"
  shows "svk_decode w = svk_word_eval w"
  using assms by (rule decode.carrier_full_amalg_decode_eq_eval)

lemma carrier_full_amalg_equiv_left_context:
  assumes rel: "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2 u v"
    and a_in: "a \<in> G1"
  shows "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2
    (WordLeft a u) (WordLeft a v)"
  using rel a_in
proof (induction rule: carrier_full_amalg_equiv.induct)
  case (refl w)
  then show ?case by simp
next
  case (sym u v)
  then show ?case
    by (meson carrier_full_amalg_equiv.sym)
next
  case (trans u v w)
  then show ?case
    by (meson carrier_full_amalg_equiv.trans)
next
  case (of_amalg u v)
  then show ?case
    by (meson carrier_amalgam_equiv.left_context carrier_full_amalg_equiv.of_amalg)
next
  case (of_reduction u v)
  then show ?case
    by (meson carrier_fpw_reduction_left_context carrier_full_amalg_equiv.of_reduction)
qed

lemma carrier_full_amalg_equiv_right_context:
  assumes rel: "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2 u v"
    and b_in: "b \<in> G2"
  shows "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2
    (WordRight b u) (WordRight b v)"
  using rel b_in
proof (induction rule: carrier_full_amalg_equiv.induct)
  case (refl w)
  then show ?case by simp
next
  case (sym u v)
  then show ?case
    by (meson carrier_full_amalg_equiv.sym)
next
  case (trans u v w)
  then show ?case
    by (meson carrier_full_amalg_equiv.trans)
next
  case (of_amalg u v)
  then show ?case
    by (meson carrier_amalgam_equiv.right_context carrier_full_amalg_equiv.of_amalg)
next
  case (of_reduction u v)
  then show ?case
    by (meson carrier_fpw_reduction_right_context carrier_full_amalg_equiv.of_reduction)
qed

lemma carrier_full_amalg_equiv_left_pair_eq:
  assumes a_in: "a \<in> G1"
    and b_in: "b \<in> G1"
    and ab_in: "mult1 a b \<in> G1"
    and c_in: "c \<in> G1"
    and d_in: "d \<in> G1"
    and cd_in: "mult1 c d \<in> G1"
    and rest_in: "fpw_in_space G1 G2 rest"
    and eq: "mult1 a b = mult1 c d"
  shows "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2
    (WordLeft a (WordLeft b rest))
    (WordLeft c (WordLeft d rest))"
proof -
  have step_left:
    "carrier_fpw_reduction_step G1 G2 mult1 one1 mult2 one2
      (WordLeft a (WordLeft b rest))
      (WordLeft (mult1 a b) rest)"
  proof (rule carrier_fpw_reduction_step.combine_left)
    show "a \<in> G1" by (rule a_in)
    show "b \<in> G1" by (rule b_in)
    show "mult1 a b \<in> G1" by (rule ab_in)
    show "fpw_in_space G1 G2 rest" by (rule rest_in)
  qed
  have red_left:
    "carrier_fpw_reduction G1 G2 mult1 one1 mult2 one2
      (WordLeft a (WordLeft b rest))
      (WordLeft (mult1 a b) rest)"
    by (rule carrier_fpw_reduction.step[OF step_left])
  have step_right:
    "carrier_fpw_reduction_step G1 G2 mult1 one1 mult2 one2
      (WordLeft c (WordLeft d rest))
      (WordLeft (mult1 c d) rest)"
  proof (rule carrier_fpw_reduction_step.combine_left)
    show "c \<in> G1" by (rule c_in)
    show "d \<in> G1" by (rule d_in)
    show "mult1 c d \<in> G1" by (rule cd_in)
    show "fpw_in_space G1 G2 rest" by (rule rest_in)
  qed
  have red_right:
    "carrier_fpw_reduction G1 G2 mult1 one1 mult2 one2
      (WordLeft c (WordLeft d rest))
      (WordLeft (mult1 c d) rest)"
    by (rule carrier_fpw_reduction.step[OF step_right])
  have rel_left:
    "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2
      (WordLeft a (WordLeft b rest))
      (WordLeft (mult1 a b) rest)"
    by (rule carrier_full_amalg_equiv.of_reduction[OF red_left])
  have rel_right:
    "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2
      (WordLeft c (WordLeft d rest))
      (WordLeft (mult1 a b) rest)"
    using eq by (simp add: carrier_full_amalg_equiv.of_reduction[OF red_right])
  show ?thesis
    by (rule carrier_full_amalg_equiv.trans[OF rel_left])
       (rule carrier_full_amalg_equiv.sym[OF rel_right])
qed

lemma carrier_full_amalg_equiv_right_pair_eq:
  assumes a_in: "a \<in> G2"
    and b_in: "b \<in> G2"
    and ab_in: "mult2 a b \<in> G2"
    and c_in: "c \<in> G2"
    and d_in: "d \<in> G2"
    and cd_in: "mult2 c d \<in> G2"
    and rest_in: "fpw_in_space G1 G2 rest"
    and eq: "mult2 a b = mult2 c d"
  shows "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2
    (WordRight a (WordRight b rest))
    (WordRight c (WordRight d rest))"
proof -
  have step_left:
    "carrier_fpw_reduction_step G1 G2 mult1 one1 mult2 one2
      (WordRight a (WordRight b rest))
      (WordRight (mult2 a b) rest)"
  proof (rule carrier_fpw_reduction_step.combine_right)
    show "a \<in> G2" by (rule a_in)
    show "b \<in> G2" by (rule b_in)
    show "mult2 a b \<in> G2" by (rule ab_in)
    show "fpw_in_space G1 G2 rest" by (rule rest_in)
  qed
  have red_left:
    "carrier_fpw_reduction G1 G2 mult1 one1 mult2 one2
      (WordRight a (WordRight b rest))
      (WordRight (mult2 a b) rest)"
    by (rule carrier_fpw_reduction.step[OF step_left])
  have step_right:
    "carrier_fpw_reduction_step G1 G2 mult1 one1 mult2 one2
      (WordRight c (WordRight d rest))
      (WordRight (mult2 c d) rest)"
  proof (rule carrier_fpw_reduction_step.combine_right)
    show "c \<in> G2" by (rule c_in)
    show "d \<in> G2" by (rule d_in)
    show "mult2 c d \<in> G2" by (rule cd_in)
    show "fpw_in_space G1 G2 rest" by (rule rest_in)
  qed
  have red_right:
    "carrier_fpw_reduction G1 G2 mult1 one1 mult2 one2
      (WordRight c (WordRight d rest))
      (WordRight (mult2 c d) rest)"
    by (rule carrier_fpw_reduction.step[OF step_right])
  have rel_left:
    "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2
      (WordRight a (WordRight b rest))
      (WordRight (mult2 a b) rest)"
    by (rule carrier_full_amalg_equiv.of_reduction[OF red_left])
  have rel_right:
    "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2
      (WordRight c (WordRight d rest))
      (WordRight (mult2 a b) rest)"
    using eq by (simp add: carrier_full_amalg_equiv.of_reduction[OF red_right])
  show ?thesis
    by (rule carrier_full_amalg_equiv.trans[OF rel_left])
       (rule carrier_full_amalg_equiv.sym[OF rel_right])
qed

lemma loop_subdivision_by_cover:
  assumes p_loop: "p \<in> loop_space W x0"
  shows "\<exists>n::nat. 0 < n \<and>
      (\<forall>i<n.
        subpathin (real i / real n) (real (Suc i) / real n) p ` {0..1} \<subseteq> U \<or>
        subpathin (real i / real n) (real (Suc i) / real n) p ` {0..1} \<subseteq> V)"
proof -
  have p_path: "path p"
    using p_loop unfolding loop_space_def by auto
  have p_img: "path_image p \<subseteq> W"
    using p_loop unfolding loop_space_def by auto
  have p_pathin: "pathin (top_of_set W) p"
    by (rule path_top_of_setI[OF p_path p_img])
  have cover: "p ` {0..1} \<subseteq> \<Union>{U, V}"
    using p_img by (auto simp: path_image_def)
  have open_cover: "openin (top_of_set W) S" if "S \<in> {U, V}" for S
    using that U_open V_open by (auto simp: openin_open)
  from pathin_subdivision_open_cover[OF p_pathin cover open_cover]
  obtain n :: nat where n_pos: "0 < n"
    and n_cover:
      "\<forall>i<n. \<exists>S\<in>{U, V}.
        subpathin (real i / real n) (real (Suc i) / real n) p ` {0..1} \<subseteq> S"
    by blast
  show ?thesis
    using n_pos n_cover by auto
qed

definition connector :: "'a \<Rightarrow> real \<Rightarrow> 'a" where
  "connector a =
    (if a = x0 then (\<lambda>_. x0)
     else (SOME p. path p \<and> path_image p \<subseteq> U \<inter> V \<and> pathstart p = x0 \<and> pathfinish p = a))"

lemma connector_x0 [simp]:
  "connector x0 = (\<lambda>_. x0)"
  unfolding connector_def by simp

lemma connector_witness:
  assumes a_in: "a \<in> U \<inter> V"
  shows "\<exists>p. path p \<and> path_image p \<subseteq> U \<inter> V \<and> pathstart p = x0 \<and> pathfinish p = a"
proof (cases "a = x0")
  case True
  have "path (\<lambda>_. x0) \<and>
      path_image (\<lambda>_. x0) \<subseteq> U \<inter> V \<and>
      pathstart (\<lambda>_. x0) = x0 \<and>
      pathfinish (\<lambda>_. x0) = a"
    using a_in True by (auto simp: path_def path_image_def pathstart_def pathfinish_def)
  then show ?thesis by blast
next
  case False
  then show ?thesis
    using UV_path_connected x0_in_UV a_in unfolding path_connected_def by blast
qed

lemma connector_path:
  assumes a_in: "a \<in> U \<inter> V"
  shows "path (connector a)"
proof (cases "a = x0")
  case True
  then show ?thesis
    by (simp add: connector_def path_def)
next
  case False
  have some:
    "path (SOME p. path p \<and> path_image p \<subseteq> U \<inter> V \<and> pathstart p = x0 \<and> pathfinish p = a) \<and>
      path_image (SOME p. path p \<and> path_image p \<subseteq> U \<inter> V \<and> pathstart p = x0 \<and> pathfinish p = a) \<subseteq> U \<inter> V \<and>
      pathstart (SOME p. path p \<and> path_image p \<subseteq> U \<inter> V \<and> pathstart p = x0 \<and> pathfinish p = a) = x0 \<and>
      pathfinish (SOME p. path p \<and> path_image p \<subseteq> U \<inter> V \<and> pathstart p = x0 \<and> pathfinish p = a) = a"
    by (rule someI_ex[OF connector_witness[OF a_in]])
  then show ?thesis
    using False by (simp add: connector_def)
qed

lemma connector_image_subset:
  assumes a_in: "a \<in> U \<inter> V"
  shows "path_image (connector a) \<subseteq> U \<inter> V"
proof (cases "a = x0")
  case True
  then show ?thesis
    using a_in by (auto simp: connector_def path_image_def)
next
  case False
  have some:
    "path (SOME p. path p \<and> path_image p \<subseteq> U \<inter> V \<and> pathstart p = x0 \<and> pathfinish p = a) \<and>
      path_image (SOME p. path p \<and> path_image p \<subseteq> U \<inter> V \<and> pathstart p = x0 \<and> pathfinish p = a) \<subseteq> U \<inter> V \<and>
      pathstart (SOME p. path p \<and> path_image p \<subseteq> U \<inter> V \<and> pathstart p = x0 \<and> pathfinish p = a) = x0 \<and>
      pathfinish (SOME p. path p \<and> path_image p \<subseteq> U \<inter> V \<and> pathstart p = x0 \<and> pathfinish p = a) = a"
    by (rule someI_ex[OF connector_witness[OF a_in]])
  then show ?thesis
    using False by (simp add: connector_def)
qed

lemma connector_start:
  assumes a_in: "a \<in> U \<inter> V"
  shows "pathstart (connector a) = x0"
proof (cases "a = x0")
  case True
  then show ?thesis
    by (simp add: connector_def pathstart_def)
next
  case False
  have some:
    "path (SOME p. path p \<and> path_image p \<subseteq> U \<inter> V \<and> pathstart p = x0 \<and> pathfinish p = a) \<and>
      path_image (SOME p. path p \<and> path_image p \<subseteq> U \<inter> V \<and> pathstart p = x0 \<and> pathfinish p = a) \<subseteq> U \<inter> V \<and>
      pathstart (SOME p. path p \<and> path_image p \<subseteq> U \<inter> V \<and> pathstart p = x0 \<and> pathfinish p = a) = x0 \<and>
      pathfinish (SOME p. path p \<and> path_image p \<subseteq> U \<inter> V \<and> pathstart p = x0 \<and> pathfinish p = a) = a"
    by (rule someI_ex[OF connector_witness[OF a_in]])
  then show ?thesis
    using False by (simp add: connector_def)
qed

lemma connector_finish:
  assumes a_in: "a \<in> U \<inter> V"
  shows "pathfinish (connector a) = a"
proof (cases "a = x0")
  case True
  then show ?thesis
    by (simp add: connector_def pathfinish_def)
next
  case False
  have some:
    "path (SOME p. path p \<and> path_image p \<subseteq> U \<inter> V \<and> pathstart p = x0 \<and> pathfinish p = a) \<and>
      path_image (SOME p. path p \<and> path_image p \<subseteq> U \<inter> V \<and> pathstart p = x0 \<and> pathfinish p = a) \<subseteq> U \<inter> V \<and>
      pathstart (SOME p. path p \<and> path_image p \<subseteq> U \<inter> V \<and> pathstart p = x0 \<and> pathfinish p = a) = x0 \<and>
      pathfinish (SOME p. path p \<and> path_image p \<subseteq> U \<inter> V \<and> pathstart p = x0 \<and> pathfinish p = a) = a"
    by (rule someI_ex[OF connector_witness[OF a_in]])
  then show ?thesis
    using False by (simp add: connector_def)
qed

lemmas connector_spec = connector_path connector_image_subset connector_start connector_finish

definition segment_loop :: "(real \<Rightarrow> 'a) \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> 'a" where
  "segment_loop p u v =
    (connector (p u) +++ subpathin u v p) +++ reversepath (connector (p v))"

lemma segment_loop_in_set:
  assumes p_path: "path p"
    and p_image: "path_image p \<subseteq> W"
    and uv01: "u \<in> {0..1}" "v \<in> {0..1}"
    and puv_in: "p u \<in> U \<inter> V" "p v \<in> U \<inter> V"
    and conn_u: "path_image (connector (p u)) \<subseteq> S"
    and conn_v: "path_image (connector (p v)) \<subseteq> S"
    and seg_in: "subpathin u v p ` {0..1} \<subseteq> S"
    and x0S: "x0 \<in> S"
  shows "segment_loop p u v \<in> loop_space S x0"
proof -
  have cu_path: "path (connector (p u))"
    using puv_in connector_spec(1)[of "p u"] by blast
  have cv_path: "path (connector (p v))"
    using puv_in connector_spec(1)[of "p v"] by blast
  have cu_start: "pathstart (connector (p u)) = x0"
    using puv_in connector_spec(3)[of "p u"] by blast
  have cu_finish: "pathfinish (connector (p u)) = p u"
    using puv_in connector_spec(4)[of "p u"] by blast
  have cv_start: "pathstart (connector (p v)) = x0"
    using puv_in connector_spec(3)[of "p v"] by blast
  have cv_finish: "pathfinish (connector (p v)) = p v"
    using puv_in connector_spec(4)[of "p v"] by blast
  have p_pathin: "pathin (top_of_set W) p"
    by (rule path_top_of_setI[OF p_path p_image])
  have subpath_pathin: "pathin (top_of_set W) (subpathin u v p)"
    by (rule pathin_subpathin[OF p_pathin uv01])
  have subpath_path: "path (subpathin u v p)"
    using subpath_pathin by (simp add: pathin_canon_iff)
  have subpath_start: "pathstart (subpathin u v p) = p u"
    by (simp add: pathstart_def subpathin_def)
  have subpath_finish: "pathfinish (subpathin u v p) = p v"
    by (simp add: pathfinish_def subpathin_def)
  have first_join: "path (connector (p u) +++ subpathin u v p)"
    using cu_path subpath_path cu_finish subpath_start by simp
  have first_finish: "pathfinish (connector (p u) +++ subpathin u v p) = p v"
    using first_join subpath_finish by simp
  have rev_cv_path: "path (reversepath (connector (p v)))"
    using cv_path by simp
  have rev_cv_start: "pathstart (reversepath (connector (p v))) = p v"
    using cv_finish by simp
  have second_join:
    "path ((connector (p u) +++ subpathin u v p) +++ reversepath (connector (p v)))"
    using first_join rev_cv_path first_finish rev_cv_start by simp
  show ?thesis
  proof (rule loop_spaceI)
    show "path (segment_loop p u v)"
      using second_join unfolding segment_loop_def by simp
    show "path_image (segment_loop p u v) \<subseteq> S"
    proof -
      have seg_img: "path_image (subpathin u v p) \<subseteq> S"
        using seg_in by (simp add: path_image_def)
      have left_img: "path_image (connector (p u) +++ subpathin u v p) \<subseteq> S"
        by (rule subset_path_image_join[OF conn_u seg_img])
      have right_img: "path_image (reversepath (connector (p v))) \<subseteq> S"
        using conn_v by simp
      show ?thesis
        unfolding segment_loop_def by (rule subset_path_image_join[OF left_img right_img])
    qed
    show "pathstart (segment_loop p u v) = x0"
      unfolding segment_loop_def using cu_start by simp
    show "pathfinish (segment_loop p u v) = x0"
      unfolding segment_loop_def using cv_start by simp
  qed
qed

lemma segment_loop_in_U:
  assumes p_path: "path p"
    and p_image: "path_image p \<subseteq> W"
    and uv01: "u \<in> {0..1}" "v \<in> {0..1}"
    and puv_in: "p u \<in> U \<inter> V" "p v \<in> U \<inter> V"
    and seg_in: "subpathin u v p ` {0..1} \<subseteq> U"
  shows "segment_loop p u v \<in> loop_space U x0"
proof (rule segment_loop_in_set[where S = U])
  show "path p"
    by (rule p_path)
  show "path_image p \<subseteq> W"
    by (rule p_image)
  show "u \<in> {0..1}" "v \<in> {0..1}"
    by (rule uv01)+
  show "p u \<in> U \<inter> V" "p v \<in> U \<inter> V"
    by (rule puv_in)+
  show "path_image (connector (p u)) \<subseteq> U"
    using connector_spec(2)[OF puv_in(1)] by blast
  show "path_image (connector (p v)) \<subseteq> U"
    using connector_spec(2)[OF puv_in(2)] by blast
  show "subpathin u v p ` {0..1} \<subseteq> U"
    by (rule seg_in)
  show "x0 \<in> U"
    by simp
qed

lemma segment_loop_in_V:
  assumes p_path: "path p"
    and p_image: "path_image p \<subseteq> W"
    and uv01: "u \<in> {0..1}" "v \<in> {0..1}"
    and puv_in: "p u \<in> U \<inter> V" "p v \<in> U \<inter> V"
    and seg_in: "subpathin u v p ` {0..1} \<subseteq> V"
  shows "segment_loop p u v \<in> loop_space V x0"
proof (rule segment_loop_in_set[where S = V])
  show "path p"
    by (rule p_path)
  show "path_image p \<subseteq> W"
    by (rule p_image)
  show "u \<in> {0..1}" "v \<in> {0..1}"
    by (rule uv01)+
  show "p u \<in> U \<inter> V" "p v \<in> U \<inter> V"
    by (rule puv_in)+
  show "path_image (connector (p u)) \<subseteq> V"
    using connector_spec(2)[OF puv_in(1)] by blast
  show "path_image (connector (p v)) \<subseteq> V"
    using connector_spec(2)[OF puv_in(2)] by blast
  show "subpathin u v p ` {0..1} \<subseteq> V"
    by (rule seg_in)
  show "x0 \<in> V"
    by simp
qed

lemma segment_loop_in_W:
  assumes p_path: "path p"
    and p_image: "path_image p \<subseteq> W"
    and uv01: "u \<in> {0..1}" "v \<in> {0..1}"
    and puv_in: "p u \<in> U \<inter> V" "p v \<in> U \<inter> V"
    and seg_in: "subpathin u v p ` {0..1} \<subseteq> W"
  shows "segment_loop p u v \<in> loop_space W x0"
proof (rule segment_loop_in_set[where S = W])
  show "path p"
    by (rule p_path)
  show "path_image p \<subseteq> W"
    by (rule p_image)
  show "u \<in> {0..1}" "v \<in> {0..1}"
    by (rule uv01)+
  show "p u \<in> U \<inter> V" "p v \<in> U \<inter> V"
    by (rule puv_in)+
  show "path_image (connector (p u)) \<subseteq> W"
    using connector_spec(2)[OF puv_in(1)] by blast
  show "path_image (connector (p v)) \<subseteq> W"
    using connector_spec(2)[OF puv_in(2)] by blast
  show "subpathin u v p ` {0..1} \<subseteq> W"
    by (rule seg_in)
  show "x0 \<in> W"
    by simp
qed

lemma path_subpathin:
  assumes "path p"
    and "u \<in> {0..1}"
    and "v \<in> {0..1}"
  shows "path (subpathin u v p)"
proof -
  have "pathin (top_of_set (path_image p)) p"
    by (rule path_top_of_setI[OF assms(1)]) auto
  then have "pathin (top_of_set (path_image p)) (subpathin u v p)"
    by (rule pathin_subpathin[OF _ assms(2,3)])
  then show ?thesis
    by (simp add: pathin_canon_iff)
qed

lemma path_image_subpathin_subset:
  assumes "u \<in> {0..1}"
    and "v \<in> {0..1}"
  shows "path_image (subpathin u v p) \<subseteq> path_image p"
proof -
  have "closed_segment u v \<subseteq> {0..1}"
    using assms by (auto simp: closed_segment_eq_real_ivl)
  then show ?thesis
    by (simp add: path_image_def subpathin_image image_mono)
qed

lemma reversepath_subpathin [simp]:
  "reversepath (subpathin u v p) = subpathin v u p"
  unfolding reversepath_def subpathin_def by (rule ext) (simp add: algebra_simps)

lemma subpathin_refl [simp]:
  "subpathin u u p = (\<lambda>_. p u)"
  unfolding subpathin_def by (rule ext) simp

fun svk_partition :: "(real \<Rightarrow> 'a) \<Rightarrow> real list \<Rightarrow> bool list \<Rightarrow> bool" where
  "svk_partition p [] bs = False"
| "svk_partition p [t] [] = (t = 1 \<and> p t \<in> U \<inter> V)"
| "svk_partition p [t] (b # bs) = False"
| "svk_partition p (t # u # ts) [] = False"
| "svk_partition p (t # u # ts) (b # bs) =
    (t \<in> {0..1} \<and> p t \<in> U \<inter> V \<and> u \<in> {0..1} \<and> t < u \<and>
      (if b then subpathin t u p ` {0..1} \<subseteq> U else subpathin t u p ` {0..1} \<subseteq> V) \<and>
      svk_partition p (u # ts) bs)"

subsection \<open>Partitions and encoded loop words\<close>

text \<open>
  A loop is encoded by subdividing the unit interval into pieces whose images lie
  entirely in \<open>U\<close> or entirely in \<open>V\<close>. The resulting bitstring records which
  side each segment uses, and the partition word records the corresponding loop
  classes in the two factors of the amalgamated free product.
\<close>

definition valid_partition :: "(real \<Rightarrow> 'a) \<Rightarrow> real list \<Rightarrow> bool list \<Rightarrow> bool" where
  "valid_partition p ts bs \<longleftrightarrow> ts \<noteq> [] \<and> hd ts = 0 \<and> svk_partition p ts bs"

fun cover_partition :: "(real \<Rightarrow> 'a) \<Rightarrow> real list \<Rightarrow> bool list \<Rightarrow> bool" where
  "cover_partition p [t] [] = (t = 1)"
| "cover_partition p (t # u # ts) (b # bs) =
    (t \<in> {0..1} \<and> u \<in> {0..1} \<and> t < u \<and>
      (if b then subpathin t u p ` {0..1} \<subseteq> U else subpathin t u p ` {0..1} \<subseteq> V) \<and>
      cover_partition p (u # ts) bs)"
| "cover_partition p ts bs = False"

fun rectangle_partition ::
  "((real \<times> real) \<Rightarrow> 'a) \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real list \<Rightarrow> bool list \<Rightarrow> bool"
where
  "rectangle_partition h c d [t] [] = (t = 1)"
| "rectangle_partition h c d (t # u # ts) (b # bs) =
    (t \<in> {0..1} \<and> u \<in> {0..1} \<and> t < u \<and>
      (if b then h ` ({t..u} \<times> {c..d}) \<subseteq> U else h ` ({t..u} \<times> {c..d}) \<subseteq> V) \<and>
      rectangle_partition h c d (u # ts) bs)"
| "rectangle_partition h c d ts bs = False"

fun alternating_bits :: "bool list \<Rightarrow> bool" where
  "alternating_bits [] = True"
| "alternating_bits [b] = True"
| "alternating_bits (b # c # bs) = (b \<noteq> c \<and> alternating_bits (c # bs))"

fun partition_word ::
  "(real \<Rightarrow> 'a) \<Rightarrow> real list \<Rightarrow> bool list \<Rightarrow>
    ((real \<Rightarrow> 'a) set, (real \<Rightarrow> 'a) set) free_product_word"
where
  "partition_word p (t # u # ts) (b # bs) =
    (if b then WordLeft (loop_class U x0 (segment_loop p t u))
     else WordRight (loop_class V x0 (segment_loop p t u)))
      (partition_word p (u # ts) bs)"
| "partition_word p ts bs = WordNil"

fun partition_word_with_tail ::
  "(real \<Rightarrow> 'a) \<Rightarrow> real list \<Rightarrow> bool list \<Rightarrow>
    ((real \<Rightarrow> 'a) set, (real \<Rightarrow> 'a) set) free_product_word \<Rightarrow>
    ((real \<Rightarrow> 'a) set, (real \<Rightarrow> 'a) set) free_product_word"
where
  "partition_word_with_tail p (t # u # ts) (b # bs) tail =
    (if b then WordLeft (loop_class U x0 (segment_loop p t u))
     else WordRight (loop_class V x0 (segment_loop p t u)))
      (partition_word_with_tail p (u # ts) bs tail)"
| "partition_word_with_tail p ts bs tail = tail"

fun bridge_word ::
  "bool \<Rightarrow> (real \<Rightarrow> 'a) set \<Rightarrow>
    ((real \<Rightarrow> 'a) set, (real \<Rightarrow> 'a) set) free_product_word \<Rightarrow>
    ((real \<Rightarrow> 'a) set, (real \<Rightarrow> 'a) set) free_product_word"
where
  "bridge_word True h rest = WordLeft (i1 h) rest"
| "bridge_word False h rest = WordRight (i2 h) rest"

fun partition_loop :: "(real \<Rightarrow> 'a) \<Rightarrow> real list \<Rightarrow> real \<Rightarrow> 'a" where
  "partition_loop p (t # u # ts) = segment_loop p t u +++ partition_loop p (u # ts)"
| "partition_loop p ts = (\<lambda>_. x0)"

lemma partition_word_with_tail_nil [simp]:
  "partition_word_with_tail p ts bs WordNil = partition_word p ts bs"
  by (induction p ts bs
      "WordNil :: ((real \<Rightarrow> 'a) set, (real \<Rightarrow> 'a) set) free_product_word"
      rule: partition_word_with_tail.induct) simp_all

lemma subpathin_joinpaths_left_half [simp]:
  "subpathin 0 (1 / 2) (p +++ q) ` {0..1} = p ` {0..1}"
proof
  show "subpathin 0 (1 / 2) (p +++ q) ` {0..1} \<subseteq> p ` {0..1}"
    by (auto simp: subpathin_def joinpaths_def)
next
  show "p ` {0..1} \<subseteq> subpathin 0 (1 / 2) (p +++ q) ` {0..1}"
  proof
    fix x
    assume "x \<in> p ` {0..1}"
    then obtain t where t01: "t \<in> {0..1}" and x_eq: "x = p t"
      by blast
    have x_eq': "x = subpathin 0 (1 / 2) (p +++ q) t"
      using x_eq t01 by (simp add: subpathin_def joinpaths_def)
    show "x \<in> subpathin 0 (1 / 2) (p +++ q) ` {0..1}"
      using t01 x_eq' by blast
  qed
qed

lemma affine_unit_interval:
  fixes u v t :: real
  assumes u01: "u \<in> {0..1}"
    and v01: "v \<in> {0..1}"
    and t01: "t \<in> {0..1}"
  shows "(v - u) * t + u \<in> {0..1}"
proof -
  have t_bounds: "0 \<le> t" "t \<le> 1"
    using t01 by auto
  have u_bounds: "0 \<le> u" "u \<le> 1"
    using u01 by auto
  have v_bounds: "0 \<le> v" "v \<le> 1"
    using v01 by auto
  have one_minus_t_nonneg: "0 \<le> 1 - t"
    using t_bounds by linarith
  have lower1: "0 \<le> (1 - t) * u"
    using one_minus_t_nonneg u_bounds by (intro mult_nonneg_nonneg) auto
  have lower2: "0 \<le> t * v"
    using t_bounds v_bounds by (intro mult_nonneg_nonneg) auto
  have lower: "0 \<le> (1 - t) * u + t * v"
    using lower1 lower2 by simp
  have upper1: "(1 - t) * u \<le> (1 - t) * 1"
    using one_minus_t_nonneg u_bounds by (intro mult_left_mono) auto
  have upper2: "t * v \<le> t * 1"
    using t_bounds v_bounds by (intro mult_left_mono) auto
  have upper: "(1 - t) * u + t * v \<le> 1"
    using upper1 upper2 by simp
  have "(v - u) * t + u = (1 - t) * u + t * v"
    by (simp add: algebra_simps)
  then show ?thesis
    using lower upper by auto
qed

lemma subpathin_joinpaths_tail_scaled_pointwise:
  assumes q0: "pathstart q = pathfinish p"
    and u01: "u \<in> {0..1}"
    and v01: "v \<in> {0..1}"
    and t01: "t \<in> {0..1}"
  shows "subpathin ((1 + u) / 2) ((1 + v) / 2) (p +++ q) t = subpathin u v q t"
proof -
  let ?s = "(v - u) * t + u"
  have s01: "?s \<in> {0..1}"
    by (rule affine_unit_interval[OF u01 v01 t01])
  have param_eq:
    "((1 + v) / 2 - (1 + u) / 2) * t + (1 + u) / 2 = (1 + ?s) / 2"
    by (simp add: field_simps algebra_simps)
  show ?thesis
  proof (cases "?s = 0")
    case True
    then show ?thesis
      using q0 by (simp add: subpathin_def joinpaths_def pathstart_def pathfinish_def param_eq)
  next
    case False
    then have s_pos: "0 < ?s"
      using s01 by auto
    then have param_gt:
      "1 / 2 < ((1 + v) / 2 - (1 + u) / 2) * t + (1 + u) / 2"
      by (simp add: param_eq)
    have param_not_le:
      "\<not> (((1 + v) / 2 - (1 + u) / 2) * t + (1 + u) / 2 \<le> 1 / 2)"
      using param_gt by simp
    then show ?thesis
    proof -
      have "subpathin ((1 + u) / 2) ((1 + v) / 2) (p +++ q) t =
          q (2 * (((1 + v) / 2 - (1 + u) / 2) * t + (1 + u) / 2) - 1)"
        using param_not_le by (simp add: subpathin_def joinpaths_def)
      also have "... = q ?s"
      proof -
        have "2 * (((1 + v) / 2 - (1 + u) / 2) * t + (1 + u) / 2) - 1 = ?s"
          by (simp add: field_simps algebra_simps)
        then show ?thesis
          by simp
      qed
      also have "... = subpathin u v q t"
        by (simp add: subpathin_def)
      finally show ?thesis .
    qed
  qed
qed

lemma subpathin_joinpaths_tail_scaled [simp]:
  assumes q0: "pathstart q = pathfinish p"
    and u01: "u \<in> {0..1}"
    and v01: "v \<in> {0..1}"
  shows "subpathin ((1 + u) / 2) ((1 + v) / 2) (p +++ q) ` {0..1} = subpathin u v q ` {0..1}"
proof
  show "subpathin ((1 + u) / 2) ((1 + v) / 2) (p +++ q) ` {0..1} \<subseteq> subpathin u v q ` {0..1}"
  proof
    fix x
    assume x_in: "x \<in> subpathin ((1 + u) / 2) ((1 + v) / 2) (p +++ q) ` {0..1}"
    then obtain t where t01: "t \<in> {0..1}"
      and x_eq: "x = subpathin ((1 + u) / 2) ((1 + v) / 2) (p +++ q) t"
      by blast
    have x_eq': "x = subpathin u v q t"
      using x_eq subpathin_joinpaths_tail_scaled_pointwise[OF q0 u01 v01 t01] by simp
    show "x \<in> subpathin u v q ` {0..1}"
      using t01 x_eq' by blast
  qed
next
  show "subpathin u v q ` {0..1} \<subseteq> subpathin ((1 + u) / 2) ((1 + v) / 2) (p +++ q) ` {0..1}"
  proof
    fix x
    assume x_in: "x \<in> subpathin u v q ` {0..1}"
    then obtain t where t01: "t \<in> {0..1}" and x_eq: "x = subpathin u v q t"
      by blast
    have x_eq': "x = subpathin ((1 + u) / 2) ((1 + v) / 2) (p +++ q) t"
      using x_eq subpathin_joinpaths_tail_scaled_pointwise[OF q0 u01 v01 t01] by simp
    show "x \<in> subpathin ((1 + u) / 2) ((1 + v) / 2) (p +++ q) ` {0..1}"
      using t01 x_eq' by blast
  qed
qed

lemma homotopic_paths_join_left:
  assumes qr: "homotopic_paths S q r"
    and p_path: "path p"
    and p_img: "path_image p \<subseteq> S"
    and pq: "pathfinish p = pathstart q"
  shows "homotopic_paths S (p +++ q) (p +++ r)"
proof (rule homotopic_paths_join)
  show "homotopic_paths S p p"
    using p_path p_img by simp
  show "homotopic_paths S q r"
    by (rule qr)
  show "pathfinish p = pathstart q"
    by (rule pq)
qed

lemma homotopic_paths_join_right:
  assumes pq: "homotopic_paths S p q"
    and r_path: "path r"
    and r_img: "path_image r \<subseteq> S"
    and qr: "pathfinish p = pathstart r"
  shows "homotopic_paths S (p +++ r) (q +++ r)"
proof (rule homotopic_paths_join)
  show "homotopic_paths S p q"
    by (rule pq)
  show "homotopic_paths S r r"
    using r_path r_img by simp
  show "pathfinish p = pathstart r"
    by (rule qr)
qed

lemma homotopic_paths_cancel_middle_local:
  assumes r_path: "path r"
    and r_img: "path_image r \<subseteq> S"
    and c_path: "path c"
    and c_img: "path_image c \<subseteq> S"
    and s_path: "path s"
    and s_img: "path_image s \<subseteq> S"
    and rc: "pathfinish r = pathfinish c"
    and cs: "pathstart s = pathfinish c"
  shows "homotopic_paths S ((((r +++ reversepath c) +++ c) +++ s)) (r +++ s)"
proof -
  have revc_path: "path (reversepath c)"
    using c_path by simp
  have revc_img: "path_image (reversepath c) \<subseteq> S"
    using c_img by simp
  have mid_path: "path (reversepath c +++ c)"
    using revc_path c_path by simp
  have mid_img: "path_image (reversepath c +++ c) \<subseteq> S"
    by (rule subset_path_image_join[OF revc_img c_img])
  have hom_cancel0: "homotopic_paths S (reversepath c +++ c) (\<lambda>_. pathfinish c)"
    by (rule homotopic_paths_linv_const[OF c_path c_img])
  have hom_cancel1:
    "homotopic_paths S (((reversepath c +++ c) +++ s)) (((\<lambda>_. pathfinish c) +++ s))"
  proof (rule homotopic_paths_join_right[OF hom_cancel0 s_path s_img])
    show "pathfinish (reversepath c +++ c) = pathstart s"
      using cs by (simp add: pathstart_def pathfinish_def joinpaths_def reversepath_def)
  qed
  have hom_cancel2: "homotopic_paths S (((\<lambda>_. pathfinish c) +++ s)) s"
    using homotopic_paths_lid_const[OF s_path s_img] cs by (simp add: pathstart_def)
  have hom_cancel: "homotopic_paths S (((reversepath c +++ c) +++ s)) s"
    by (rule homotopic_paths_trans[OF hom_cancel1 hom_cancel2])
  have hom_left:
    "homotopic_paths S (r +++ ((reversepath c +++ c) +++ s)) (r +++ s)"
  proof (rule homotopic_paths_join_left[OF hom_cancel r_path r_img])
    show "pathfinish r = pathstart ((reversepath c +++ c) +++ s)"
      using rc by (simp add: pathstart_def pathfinish_def joinpaths_def reversepath_def)
  qed
  have assoc1:
    "homotopic_paths S (((r +++ reversepath c) +++ c)) (r +++ (reversepath c +++ c))"
  proof -
    have "homotopic_paths S (r +++ (reversepath c +++ c)) (((r +++ reversepath c) +++ c))"
      by (rule homotopic_paths_assoc[OF r_path r_img revc_path revc_img c_path c_img]) (use rc in simp_all)
    then show ?thesis
      by (rule homotopic_paths_sym)
  qed
  have assoc1_join:
    "homotopic_paths S ((((r +++ reversepath c) +++ c) +++ s)) (((r +++ (reversepath c +++ c)) +++ s))"
  proof (rule homotopic_paths_join_right[OF assoc1 s_path s_img])
    show "pathfinish ((r +++ reversepath c) +++ c) = pathstart s"
      using rc cs by (simp add: pathstart_def pathfinish_def joinpaths_def reversepath_def)
  qed
  have assoc2:
    "homotopic_paths S (((r +++ (reversepath c +++ c)) +++ s)) (r +++ ((reversepath c +++ c) +++ s))"
  proof -
    have "homotopic_paths S (r +++ ((reversepath c +++ c) +++ s)) (((r +++ (reversepath c +++ c)) +++ s))"
      by (rule homotopic_paths_assoc[OF r_path r_img mid_path mid_img s_path s_img]) (use rc cs in simp_all)
    then show ?thesis
      by (rule homotopic_paths_sym)
  qed
  have "homotopic_paths S ((((r +++ reversepath c) +++ c) +++ s)) (r +++ ((reversepath c +++ c) +++ s))"
    by (rule homotopic_paths_trans[OF assoc1_join assoc2])
  then show ?thesis
    by (rule homotopic_paths_trans[OF _ hom_left])
qed

lemma segment_loop_base_full_in_set:
  assumes p_loop: "p \<in> loop_space S x0"
  shows "homotopic_paths S (segment_loop p 0 1) p"
proof -
  have p_path: "path p"
    and p_img: "path_image p \<subseteq> S"
    and p0: "p 0 = x0"
    and p1: "p 1 = x0"
    using p_loop unfolding loop_space_def pathstart_def pathfinish_def by auto
  have x0_in_S: "x0 \<in> S"
    using p_img p0 by (auto simp: path_image_def)
  have const_path: "path (\<lambda>_. x0)"
    by (simp add: path_def)
  have const_img: "path_image (\<lambda>_. x0) \<subseteq> S"
    using x0_in_S by (auto simp: path_image_def)
  have hom_lid: "homotopic_paths S ((\<lambda>_. x0) +++ p) p"
    using homotopic_paths_lid_const[OF p_path p_img] p0 by (simp add: pathstart_def)
  have hom_join:
    "homotopic_paths S ((((\<lambda>_. x0) +++ p) +++ (\<lambda>_. x0))) (p +++ (\<lambda>_. x0))"
  proof (rule homotopic_paths_join_right[OF hom_lid const_path const_img])
    show "pathfinish ((\<lambda>_. x0) +++ p) = pathstart (\<lambda>_. x0)"
      using p0 p1 by (simp add: pathstart_def pathfinish_def joinpaths_def)
  qed
  have hom_rid: "homotopic_paths S (p +++ (\<lambda>_. x0)) p"
    using homotopic_paths_rid_const[OF p_path p_img] p1 by (simp add: pathfinish_def)
  have conn0: "connector (p 0) = (\<lambda>_. x0)"
    using p0 by (simp add: connector_def fun_eq_iff)
  have conn1: "reversepath (connector (p 1)) = (\<lambda>_. x0)"
    using p1 by (simp add: connector_def reversepath_def fun_eq_iff)
  have seg_eq: "segment_loop p 0 1 = (((\<lambda>_. x0) +++ p) +++ (\<lambda>_. x0))"
    unfolding segment_loop_def using conn0 conn1 by simp
  have "homotopic_paths S (segment_loop p 0 1) (p +++ (\<lambda>_. x0))"
    unfolding seg_eq by (rule hom_join)
  then show ?thesis
    by (rule homotopic_paths_trans[OF _ hom_rid])
qed

lemma segment_loop_joinpaths_head [simp]:
  assumes p_loop: "p \<in> loop_space S x0"
    and q_loop: "q \<in> loop_space W x0"
  shows "segment_loop (p +++ q) 0 (1 / 2) = segment_loop p 0 1"
proof -
  have p0: "p 0 = x0" and p1: "p 1 = x0"
    using p_loop unfolding loop_space_def pathstart_def pathfinish_def by auto
  show ?thesis
  proof
    fix t
    show "segment_loop (p +++ q) 0 (1 / 2) t = segment_loop p 0 1 t"
    proof (cases "t \<le> 1 / 4")
      case True
      then show ?thesis
        unfolding segment_loop_def
        using p0 p1
        by (simp add: connector_def joinpaths_def subpathin_def reversepath_def field_simps algebra_simps)
    next
      case False
      show ?thesis
      proof (cases "t \<le> 1 / 2")
        case True
        have mid_gt: "\<not> (2 * t \<le> 1 / 2)"
          using False by linarith
        have sub_le: "(4 * t - 1) / 2 \<le> 1 / 2"
        proof -
          have "4 * t - 1 \<le> 1"
            using True by linarith
          then show ?thesis
            by (simp add: divide_right_mono)
        qed
        have start_eq: "(p +++ q) 0 = x0"
          using p0 by (simp add: joinpaths_def)
        have mid_eq: "(p +++ q) (1 / 2) = x0"
          using p1 by (simp add: joinpaths_def)
        have conn_start: "connector ((p +++ q) 0) = (\<lambda>_. x0)"
          using start_eq by (simp add: connector_def fun_eq_iff)
        have conn_mid: "reversepath (connector ((p +++ q) (1 / 2))) = (\<lambda>_. x0)"
          using mid_eq by (simp add: connector_def reversepath_def fun_eq_iff)
        have arg_eq: "((8 * t - 2) / 2 :: real) = 4 * t - 1"
        proof -
          have "((8 * t - 2) / 2 :: real) = (8 * t) / 2 - (2 :: real) / 2"
            by (simp add: diff_divide_distrib)
          also have "... = 4 * t - 1"
            by simp
          finally show ?thesis .
        qed
        have lhs_eq: "segment_loop (p +++ q) 0 (1 / 2) t = p (4 * t - 1)"
        proof -
          have "segment_loop (p +++ q) 0 (1 / 2) t =
              (((\<lambda>_. x0) +++ subpathin 0 (1 / 2) (p +++ q)) +++ (\<lambda>_. x0)) t"
            unfolding segment_loop_def
            using conn_start conn_mid by simp
          also have "... = subpathin 0 (1 / 2) (p +++ q) (4 * t - 1)"
            using False True mid_gt
            by (simp add: joinpaths_def field_simps algebra_simps)
          also have "... = (p +++ q) ((4 * t - 1) / 2)"
            by (simp add: subpathin_def)
          also have "... = p ((8 * t - 2) / 2)"
            using sub_le by (simp add: joinpaths_def field_simps algebra_simps)
          also have "... = p (4 * t - 1)"
            by (subst arg_eq) simp
          finally show ?thesis .
        qed
        have rhs_eq: "segment_loop p 0 1 t = p (4 * t - 1)"
          unfolding segment_loop_def
          using p0 p1 False True mid_gt
          by (simp add: connector_def joinpaths_def subpathin_def reversepath_def field_simps algebra_simps)
        show ?thesis
          using lhs_eq rhs_eq by simp
      next
        case False
        then show ?thesis
          unfolding segment_loop_def
          using p0 p1
          by (simp add: connector_def joinpaths_def subpathin_def reversepath_def field_simps algebra_simps)
      qed
    qed
  qed
qed

lemma segment_loop_joinpaths_tail_scaled [simp]:
  assumes p_loop: "p \<in> loop_space W x0"
    and q_loop: "q \<in> loop_space W x0"
    and u01: "u \<in> {0..1}"
    and v01: "v \<in> {0..1}"
  shows "segment_loop (p +++ q) ((1 + u) / 2) ((1 + v) / 2) = segment_loop q u v"
proof -
  have p1: "p 1 = x0" and q0: "q 0 = x0"
    using p_loop q_loop unfolding loop_space_def pathfinish_def pathstart_def by auto
  have pq: "pathstart q = pathfinish p"
    using p_loop q_loop unfolding loop_space_def by auto
  have start_eq: "(p +++ q) ((1 + u) / 2) = q u"
  proof (cases "u = 0")
    case True
    then show ?thesis
      using p1 q0 by (simp add: joinpaths_def)
  next
    case False
    then have "(1 / 2 :: real) < (1 + u) / 2"
      using u01 by auto
    then show ?thesis
      by (simp add: joinpaths_def field_simps algebra_simps)
  qed
  have finish_eq: "(p +++ q) ((1 + v) / 2) = q v"
  proof (cases "v = 0")
    case True
    then show ?thesis
      using p1 q0 by (simp add: joinpaths_def)
  next
    case False
    then have "(1 / 2 :: real) < (1 + v) / 2"
      using v01 by auto
    then show ?thesis
      by (simp add: joinpaths_def field_simps algebra_simps)
  qed
  show ?thesis
  proof
    fix t :: real
    show "segment_loop (p +++ q) ((1 + u) / 2) ((1 + v) / 2) t = segment_loop q u v t"
    proof (cases "t \<le> 1 / 4")
      case True
      then show ?thesis
        unfolding segment_loop_def
        using start_eq finish_eq
        by (simp add: joinpaths_def field_simps algebra_simps)
    next
      case False
      show ?thesis
      proof (cases "t \<le> 1 / 2")
        case True
        have s01: "4 * t - 1 \<in> {0..1}"
          using False True by auto
        have sub_eq:
          "subpathin ((1 + u) / 2) ((1 + v) / 2) (p +++ q) (4 * t - 1) =
            subpathin u v q (4 * t - 1)"
          by (rule subpathin_joinpaths_tail_scaled_pointwise[OF pq u01 v01 s01])
        show ?thesis
          unfolding segment_loop_def
          using False True start_eq finish_eq sub_eq
          by (simp add: joinpaths_def field_simps algebra_simps)
      next
        case False
        then show ?thesis
          unfolding segment_loop_def
          using finish_eq
          by (simp add: joinpaths_def field_simps algebra_simps)
      qed
    qed
  qed
qed

fun word_loop ::
  "((real \<Rightarrow> 'a) set, (real \<Rightarrow> 'a) set) free_product_word \<Rightarrow> real \<Rightarrow> 'a"
where
  "word_loop WordNil = (\<lambda>_. x0)"
| "word_loop (WordLeft a rest) =
    (if rest = WordNil then some_loop U x0 a else some_loop U x0 a +++ word_loop rest)"
| "word_loop (WordRight b rest) =
    (if rest = WordNil then some_loop V x0 b else some_loop V x0 b +++ word_loop rest)"

fun word_partition_times ::
  "((real \<Rightarrow> 'a) set, (real \<Rightarrow> 'a) set) free_product_word \<Rightarrow> real list"
where
  "word_partition_times WordNil = [0, 1]"
| "word_partition_times (WordLeft a rest) =
    (if rest = WordNil
     then [0, 1]
     else 0 # map (\<lambda>t. (1 + t) / 2) (word_partition_times rest))"
| "word_partition_times (WordRight b rest) =
    (if rest = WordNil
     then [0, 1]
     else 0 # map (\<lambda>t. (1 + t) / 2) (word_partition_times rest))"

fun word_partition_bits ::
  "((real \<Rightarrow> 'a) set, (real \<Rightarrow> 'a) set) free_product_word \<Rightarrow> bool list"
where
  "word_partition_bits WordNil = [True]"
| "word_partition_bits (WordLeft a rest) =
    (if rest = WordNil then [True] else True # word_partition_bits rest)"
| "word_partition_bits (WordRight b rest) =
    (if rest = WordNil then [False] else False # word_partition_bits rest)"

lemma joinpaths_tail_scaled_point [simp]:
  assumes p_loop: "p \<in> loop_space W x0"
    and q_loop: "q \<in> loop_space W x0"
    and t01: "t \<in> {0..1}"
  shows "(p +++ q) ((1 + t) / 2) = q t"
proof (cases "t = 0")
  case True
  then show ?thesis
    using p_loop q_loop
    unfolding loop_space_def pathstart_def pathfinish_def joinpaths_def
    by simp
next
  case False
  have t_pos: "0 < t"
    using False t01 by auto
  then have param_gt: "(1 + t) / 2 > 1 / 2"
    by (simp add: field_simps)
  have param_not_le: "\<not> ((1 + t) / 2 \<le> 1 / 2)"
    using param_gt by simp
  have arg_eq: "2 * ((1 + t) / 2) - 1 = (t :: real)"
    by (simp add: field_simps algebra_simps)
  have "(p +++ q) ((1 + t) / 2) = q (2 * ((1 + t) / 2) - 1)"
    using param_not_le by (simp add: joinpaths_def algebra_simps)
  also have "... = q t"
    by (subst arg_eq) simp
  finally show ?thesis .
qed

lemma word_loop_in_W:
  assumes w_in: "fpw_in_space G1 G2 w"
  shows "word_loop w \<in> loop_space W x0"
  using w_in
proof (induction w)
  case WordNil
  then show ?case
    by (simp add: constant_loop_in_space[OF x0_in_W])
next
  case (WordLeft a rest)
  then have a_in: "a \<in> G1" and rest_in: "fpw_in_space G1 G2 rest"
    by auto
  have a_loopU: "some_loop U x0 a \<in> loop_space U x0"
    using some_loop_spec[OF a_in] by auto
  have a_loopW: "some_loop U x0 a \<in> loop_space W x0"
    using a_loopU unfolding loop_space_def by auto
  show ?case
  proof (cases "rest = WordNil")
    case True
    then show ?thesis
      using a_loopW by simp
  next
    case False
    have tail_loop: "word_loop rest \<in> loop_space W x0"
      by (rule WordLeft.IH[OF rest_in])
    have a_path: "path (some_loop U x0 a)"
      and a_img: "path_image (some_loop U x0 a) \<subseteq> W"
      and a_start: "pathstart (some_loop U x0 a) = x0"
      and a_finish: "pathfinish (some_loop U x0 a) = x0"
      using a_loopW unfolding loop_space_def by auto
    have tail_path: "path (word_loop rest)"
      and tail_img: "path_image (word_loop rest) \<subseteq> W"
      and tail_start: "pathstart (word_loop rest) = x0"
      and tail_finish: "pathfinish (word_loop rest) = x0"
      using tail_loop unfolding loop_space_def by auto
    have join_loop: "some_loop U x0 a +++ word_loop rest \<in> loop_space W x0"
    proof -
      have join_path: "path (some_loop U x0 a +++ word_loop rest)"
        using a_path tail_path a_finish tail_start by simp
      have join_img: "path_image (some_loop U x0 a +++ word_loop rest) \<subseteq> W"
        by (rule subset_path_image_join[OF a_img tail_img])
      show ?thesis
        unfolding loop_space_def
        using join_path join_img a_start tail_finish by simp
    qed
    then show ?thesis
      using False by simp
  qed
next
  case (WordRight b rest)
  then have b_in: "b \<in> G2" and rest_in: "fpw_in_space G1 G2 rest"
    by auto
  have b_loopV: "some_loop V x0 b \<in> loop_space V x0"
    using some_loop_spec[OF b_in] by auto
  have b_loopW: "some_loop V x0 b \<in> loop_space W x0"
    using b_loopV unfolding loop_space_def by auto
  show ?case
  proof (cases "rest = WordNil")
    case True
    then show ?thesis
      using b_loopW by simp
  next
    case False
    have tail_loop: "word_loop rest \<in> loop_space W x0"
      by (rule WordRight.IH[OF rest_in])
    have b_path: "path (some_loop V x0 b)"
      and b_img: "path_image (some_loop V x0 b) \<subseteq> W"
      and b_start: "pathstart (some_loop V x0 b) = x0"
      and b_finish: "pathfinish (some_loop V x0 b) = x0"
      using b_loopW unfolding loop_space_def by auto
    have tail_path: "path (word_loop rest)"
      and tail_img: "path_image (word_loop rest) \<subseteq> W"
      and tail_start: "pathstart (word_loop rest) = x0"
      and tail_finish: "pathfinish (word_loop rest) = x0"
      using tail_loop unfolding loop_space_def by auto
    have join_loop: "some_loop V x0 b +++ word_loop rest \<in> loop_space W x0"
    proof -
      have join_path: "path (some_loop V x0 b +++ word_loop rest)"
        using b_path tail_path b_finish tail_start by simp
      have join_img: "path_image (some_loop V x0 b +++ word_loop rest) \<subseteq> W"
        by (rule subset_path_image_join[OF b_img tail_img])
      show ?thesis
        unfolding loop_space_def
        using join_path join_img b_start tail_finish by simp
    qed
    then show ?thesis
      using False by simp
  qed
qed

lemma svk_partition_joinpaths_tail_scaled:
  assumes p_loop: "p \<in> loop_space W x0"
    and q_loop: "q \<in> loop_space W x0"
    and q_part: "svk_partition q ts bs"
  shows "svk_partition (p +++ q) (map (\<lambda>t. (1 + t) / 2) ts) bs"
  using q_part
proof (induction ts arbitrary: bs)
  case Nil
  then show ?case by simp
next
  case (Cons t ts)
  show ?case
  proof (cases ts)
    case Nil
    have bs_nil: "bs = []"
      using Cons.prems Nil by (cases bs) simp_all
    have t1: "t = 1"
      using Cons.prems Nil bs_nil by simp
    have qt1UV: "q 1 \<in> U \<inter> V"
      using Cons.prems Nil bs_nil t1 by simp
    have qtUV: "q t \<in> U \<inter> V"
      using t1 qt1UV by simp
    have t01: "t \<in> {0..1}"
      using t1 by simp
    have joined_tUV: "(p +++ q) ((1 + t) / 2) \<in> U \<inter> V"
      using qtUV joinpaths_tail_scaled_point[OF p_loop q_loop t01] by simp
    show ?thesis
      using Nil bs_nil t1 joined_tUV by simp
  next
    case (Cons u us)
    then obtain b bs' where bs: "bs = b # bs'"
      using Cons.prems by (cases bs) auto
    have t01: "t \<in> {0..1}" and qtUV: "q t \<in> U \<inter> V"
      and u01: "u \<in> {0..1}" and tu: "t < u"
      and seg_side: "(if b then subpathin t u q ` {0..1} \<subseteq> U else subpathin t u q ` {0..1} \<subseteq> V)"
      and q_tail: "svk_partition q (u # us) bs'"
      using Cons.prems bs Cons by simp_all
    have pq: "pathstart q = pathfinish p"
      using p_loop q_loop unfolding loop_space_def by auto
    have scaled_seg_side:
      "(if b
        then subpathin ((1 + t) / 2) ((1 + u) / 2) (p +++ q) ` {0..1} \<subseteq> U
        else subpathin ((1 + t) / 2) ((1 + u) / 2) (p +++ q) ` {0..1} \<subseteq> V)"
      using seg_side by (simp add: subpathin_joinpaths_tail_scaled[OF pq t01 u01])
    have q_tail_ts: "svk_partition q ts bs'"
      using q_tail Cons by simp
    have tail_scaled_ts:
      "svk_partition (p +++ q) (map (\<lambda>t. (1 + t) / 2) ts) bs'"
      by (rule Cons.IH[OF q_tail_ts])
    have tail_scaled:
      "svk_partition (p +++ q) (map (\<lambda>t. (1 + t) / 2) (u # us)) bs'"
      using tail_scaled_ts Cons by simp
    have joined_tUV: "(p +++ q) ((1 + t) / 2) \<in> U \<inter> V"
      using qtUV joinpaths_tail_scaled_point[OF p_loop q_loop t01] by simp
    show ?thesis
      using bs Cons t01 joined_tUV u01 tu scaled_seg_side tail_scaled
      by simp
  qed
qed

lemma word_loop_valid_partition:
  assumes w_in: "fpw_in_space G1 G2 w"
  shows "valid_partition (word_loop w) (word_partition_times w) (word_partition_bits w)"
  using w_in
proof (induction w)
  case WordNil
  have const_subU: "(\<lambda>_. x0) ` {0..1} \<subseteq> U"
    using x0_in_UV by auto
  then show ?case
    unfolding valid_partition_def
    using x0_in_UV const_subU
    by (auto simp: path_image_def subpathin_def)
next
  case (WordLeft a rest)
  then have a_in: "a \<in> G1" and rest_in: "fpw_in_space G1 G2 rest"
    by auto
  have a_loopU: "some_loop U x0 a \<in> loop_space U x0"
    using some_loop_spec[OF a_in] by auto
  have a_loopW: "some_loop U x0 a \<in> loop_space W x0"
    using a_loopU unfolding loop_space_def by auto
  show ?case
  proof (cases "rest = WordNil")
    case True
    then show ?thesis
      using a_loopU x0_in_UV
      unfolding valid_partition_def loop_space_def
      by (auto simp: pathstart_def pathfinish_def path_image_def)
  next
    case False
    have rest_valid:
      "valid_partition (word_loop rest) (word_partition_times rest) (word_partition_bits rest)"
      by (rule WordLeft.IH[OF rest_in])
    have rest_svk:
      "svk_partition (word_loop rest) (word_partition_times rest) (word_partition_bits rest)"
      using rest_valid unfolding valid_partition_def by auto
    have tail_scaled:
      "svk_partition (some_loop U x0 a +++ word_loop rest)
        (map (\<lambda>t. (1 + t) / 2) (word_partition_times rest))
        (word_partition_bits rest)"
      by (rule svk_partition_joinpaths_tail_scaled[OF a_loopW word_loop_in_W[OF rest_in] rest_svk])
    have headU:
      "subpathin 0 (1 / 2) (some_loop U x0 a +++ word_loop rest) ` {0..1} \<subseteq> U"
      using a_loopU by (simp add: loop_space_def path_image_def)
    have startUV: "(some_loop U x0 a +++ word_loop rest) 0 \<in> U \<inter> V"
      using a_loopU x0_in_UV unfolding loop_space_def pathstart_def joinpaths_def by simp
    have midUV: "(some_loop U x0 a +++ word_loop rest) (1 / 2) \<in> U \<inter> V"
      using a_loopU x0_in_UV unfolding loop_space_def pathfinish_def joinpaths_def by simp
    have rest_times_nonempty: "word_partition_times rest \<noteq> []"
      using rest_valid unfolding valid_partition_def by auto
    have rest_times_hd: "hd (word_partition_times rest) = 0"
      using rest_valid unfolding valid_partition_def by auto
    have rest_times: "word_partition_times rest = 0 # tl (word_partition_times rest)"
    proof (cases "word_partition_times rest")
      case Nil
      with rest_times_nonempty show ?thesis
        by simp
    next
      case (Cons s ss)
      have "s = 0"
        using rest_times_hd Cons by simp
      then show ?thesis
        using Cons by simp
    qed
    have scaled_times:
      "map (\<lambda>t. (1 + t) / 2) (word_partition_times rest) =
        1 / 2 # map (\<lambda>t. (1 + t) / 2) (tl (word_partition_times rest))"
    proof -
      have "map (\<lambda>t. (1 + t) / 2) (word_partition_times rest) =
          map (\<lambda>t. (1 + t) / 2) (0 # tl (word_partition_times rest))"
        using rest_times by simp
      also have "\<dots> = 1 / 2 # map (\<lambda>t. (1 + t) / 2) (tl (word_partition_times rest))"
        by simp
      finally show ?thesis .
    qed
    have tail_scaled':
      "svk_partition (some_loop U x0 a +++ word_loop rest)
        (1 / 2 # map (\<lambda>t. (1 + t) / 2) (tl (word_partition_times rest)))
        (word_partition_bits rest)"
      using tail_scaled scaled_times by simp
    have step_svk:
      "svk_partition (some_loop U x0 a +++ word_loop rest)
        (0 # 1 / 2 # map (\<lambda>t. (1 + t) / 2) (tl (word_partition_times rest)))
        (True # word_partition_bits rest)"
      using False tail_scaled' headU startUV midUV
      by simp
    have step_svk':
      "svk_partition (some_loop U x0 a +++ word_loop rest)
        (0 # map (\<lambda>t. (1 + t) / 2) (word_partition_times rest))
        (True # word_partition_bits rest)"
      using step_svk scaled_times by simp
    show ?thesis
      unfolding valid_partition_def
      using False step_svk'
      by simp
  qed
next
  case (WordRight b rest)
  then have b_in: "b \<in> G2" and rest_in: "fpw_in_space G1 G2 rest"
    by auto
  have b_loopV: "some_loop V x0 b \<in> loop_space V x0"
    using some_loop_spec[OF b_in] by auto
  have b_loopW: "some_loop V x0 b \<in> loop_space W x0"
    using b_loopV unfolding loop_space_def by auto
  show ?case
  proof (cases "rest = WordNil")
    case True
    then show ?thesis
      using b_loopV x0_in_UV
      unfolding valid_partition_def loop_space_def
      by (auto simp: pathstart_def pathfinish_def path_image_def)
  next
    case False
    have rest_valid:
      "valid_partition (word_loop rest) (word_partition_times rest) (word_partition_bits rest)"
      by (rule WordRight.IH[OF rest_in])
    have rest_svk:
      "svk_partition (word_loop rest) (word_partition_times rest) (word_partition_bits rest)"
      using rest_valid unfolding valid_partition_def by auto
    have tail_scaled:
      "svk_partition (some_loop V x0 b +++ word_loop rest)
        (map (\<lambda>t. (1 + t) / 2) (word_partition_times rest))
        (word_partition_bits rest)"
      by (rule svk_partition_joinpaths_tail_scaled[OF b_loopW word_loop_in_W[OF rest_in] rest_svk])
    have headV:
      "subpathin 0 (1 / 2) (some_loop V x0 b +++ word_loop rest) ` {0..1} \<subseteq> V"
      using b_loopV by (simp add: loop_space_def path_image_def)
    have startUV: "(some_loop V x0 b +++ word_loop rest) 0 \<in> U \<inter> V"
      using b_loopV x0_in_UV unfolding loop_space_def pathstart_def joinpaths_def by simp
    have midUV: "(some_loop V x0 b +++ word_loop rest) (1 / 2) \<in> U \<inter> V"
      using b_loopV x0_in_UV unfolding loop_space_def pathfinish_def joinpaths_def by simp
    have rest_times_nonempty: "word_partition_times rest \<noteq> []"
      using rest_valid unfolding valid_partition_def by auto
    have rest_times_hd: "hd (word_partition_times rest) = 0"
      using rest_valid unfolding valid_partition_def by auto
    have rest_times: "word_partition_times rest = 0 # tl (word_partition_times rest)"
    proof (cases "word_partition_times rest")
      case Nil
      with rest_times_nonempty show ?thesis
        by simp
    next
      case (Cons s ss)
      have "s = 0"
        using rest_times_hd Cons by simp
      then show ?thesis
        using Cons by simp
    qed
    have scaled_times:
      "map (\<lambda>t. (1 + t) / 2) (word_partition_times rest) =
        1 / 2 # map (\<lambda>t. (1 + t) / 2) (tl (word_partition_times rest))"
    proof -
      have "map (\<lambda>t. (1 + t) / 2) (word_partition_times rest) =
          map (\<lambda>t. (1 + t) / 2) (0 # tl (word_partition_times rest))"
        using rest_times by simp
      also have "\<dots> = 1 / 2 # map (\<lambda>t. (1 + t) / 2) (tl (word_partition_times rest))"
        by simp
      finally show ?thesis .
    qed
    have tail_scaled':
      "svk_partition (some_loop V x0 b +++ word_loop rest)
        (1 / 2 # map (\<lambda>t. (1 + t) / 2) (tl (word_partition_times rest)))
        (word_partition_bits rest)"
      using tail_scaled scaled_times by simp
    have step_svk:
      "svk_partition (some_loop V x0 b +++ word_loop rest)
        (0 # 1 / 2 # map (\<lambda>t. (1 + t) / 2) (tl (word_partition_times rest)))
        (False # word_partition_bits rest)"
      using False tail_scaled' headV startUV midUV
      by simp
    have step_svk':
      "svk_partition (some_loop V x0 b +++ word_loop rest)
        (0 # map (\<lambda>t. (1 + t) / 2) (word_partition_times rest))
        (False # word_partition_bits rest)"
      using step_svk scaled_times by simp
    show ?thesis
      unfolding valid_partition_def
      using False step_svk'
      by simp
  qed
qed

lemma partition_word_joinpaths_tail_scaled:
  assumes p_loop: "p \<in> loop_space W x0"
    and q_loop: "q \<in> loop_space W x0"
    and q_part: "svk_partition q ts bs"
  shows "partition_word (p +++ q) (map (\<lambda>t. (1 + t) / 2) ts) bs = partition_word q ts bs"
  using q_part
proof (induction ts arbitrary: bs)
  case Nil
  then show ?case
    by simp
next
  case (Cons t ts)
  show ?case
  proof (cases ts)
    case Nil
    then show ?thesis
      using Cons.prems by (cases bs) simp_all
  next
    case (Cons u us)
    then obtain b bs' where bs: "bs = b # bs'"
      using Cons.prems by (cases bs) auto
    have tail: "svk_partition q (u # us) bs'"
      using Cons.prems Cons bs by simp
    have t01: "t \<in> {0..1}" and u01: "u \<in> {0..1}"
      using Cons.prems Cons bs by simp_all
    have tail_ts: "svk_partition q ts bs'"
      using tail Cons by simp
    have ih0:
      "partition_word (p +++ q) (map (\<lambda>t. (1 + t) / 2) ts) bs' =
        partition_word q ts bs'"
      by (rule Cons.IH[of bs', OF tail_ts])
    have ih:
      "partition_word (p +++ q) (map (\<lambda>t. (1 + t) / 2) (u # us)) bs' =
        partition_word q (u # us) bs'"
      using ih0 Cons by simp
    have seg_eq:
      "segment_loop (p +++ q) ((1 + t) / 2) ((1 + u) / 2) = segment_loop q t u"
      by (rule segment_loop_joinpaths_tail_scaled[OF p_loop q_loop t01 u01])
    show ?thesis
      using Cons bs ih seg_eq
      by simp
  qed
qed

lemma segment_loop_some_loop_left_class:
  assumes a_in: "a \<in> G1"
  shows "loop_class U x0 (segment_loop (some_loop U x0 a) 0 1) = a"
proof -
  have p_loop: "some_loop U x0 a \<in> loop_space U x0"
    and a_eq: "a = loop_class U x0 (some_loop U x0 a)"
    using some_loop_spec[OF a_in] by auto
  have p_path: "path (some_loop U x0 a)"
    and p_imgU: "path_image (some_loop U x0 a) \<subseteq> U"
    and p0: "some_loop U x0 a 0 = x0"
    and p1: "some_loop U x0 a 1 = x0"
    using p_loop unfolding loop_space_def pathstart_def pathfinish_def by auto
  have segU: "segment_loop (some_loop U x0 a) 0 1 \<in> loop_space U x0"
  proof (rule segment_loop_in_U[OF p_path])
    show "path_image (some_loop U x0 a) \<subseteq> W"
      using p_imgU by auto
    show "(0::real) \<in> {0..1}"
      by simp
    show "(1::real) \<in> {0..1}"
      by simp
    show "some_loop U x0 a 0 \<in> U \<inter> V" "some_loop U x0 a 1 \<in> U \<inter> V"
      using p0 p1 x0_in_UV by simp_all
    show "subpathin 0 1 (some_loop U x0 a) ` {0..1} \<subseteq> U"
      using p_imgU by (simp add: path_image_def)
  qed
  have seg_eq:
    "loop_class U x0 (segment_loop (some_loop U x0 a) 0 1) =
      loop_class U x0 (some_loop U x0 a)"
    by (rule loop_class_eqI[OF segU p_loop segment_loop_base_full_in_set[OF p_loop]])
  show ?thesis
    using seg_eq a_eq by simp
qed

lemma segment_loop_some_loop_right_class:
  assumes b_in: "b \<in> G2"
  shows "loop_class V x0 (segment_loop (some_loop V x0 b) 0 1) = b"
proof -
  have p_loop: "some_loop V x0 b \<in> loop_space V x0"
    and b_eq: "b = loop_class V x0 (some_loop V x0 b)"
    using some_loop_spec[OF b_in] by auto
  have p_path: "path (some_loop V x0 b)"
    and p_imgV: "path_image (some_loop V x0 b) \<subseteq> V"
    and p0: "some_loop V x0 b 0 = x0"
    and p1: "some_loop V x0 b 1 = x0"
    using p_loop unfolding loop_space_def pathstart_def pathfinish_def by auto
  have segV: "segment_loop (some_loop V x0 b) 0 1 \<in> loop_space V x0"
  proof (rule segment_loop_in_V[OF p_path])
    show "path_image (some_loop V x0 b) \<subseteq> W"
      using p_imgV by auto
    show "(0::real) \<in> {0..1}"
      by simp
    show "(1::real) \<in> {0..1}"
      by simp
    show "some_loop V x0 b 0 \<in> U \<inter> V" "some_loop V x0 b 1 \<in> U \<inter> V"
      using p0 p1 x0_in_UV by simp_all
    show "subpathin 0 1 (some_loop V x0 b) ` {0..1} \<subseteq> V"
      using p_imgV by (simp add: path_image_def)
  qed
  have seg_eq:
    "loop_class V x0 (segment_loop (some_loop V x0 b) 0 1) =
      loop_class V x0 (some_loop V x0 b)"
    by (rule loop_class_eqI[OF segV p_loop segment_loop_base_full_in_set[OF p_loop]])
  show ?thesis
    using seg_eq b_eq by simp
qed

lemma partition_word_word_loop_equiv:
  assumes w_in: "fpw_in_space G1 G2 w"
  shows "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2
    (partition_word (word_loop w) (word_partition_times w) (word_partition_bits w)) w"
  using w_in
proof (induction w)
  case WordNil
  have nil_loopU: "word_loop WordNil \<in> loop_space U x0"
    by (simp add: constant_loop_in_space[OF x0_in_U])
  have nil_segU: "segment_loop (word_loop WordNil) 0 1 \<in> loop_space U x0"
  proof (rule segment_loop_in_U)
    show "path (word_loop WordNil)"
      using nil_loopU unfolding loop_space_def by simp
    show "path_image (word_loop WordNil) \<subseteq> W"
      using nil_loopU unfolding loop_space_def by simp
    show "(0::real) \<in> {0..1}"
      by simp
    show "(1::real) \<in> {0..1}"
      by simp
    show "word_loop WordNil 0 \<in> U \<inter> V" "word_loop WordNil 1 \<in> U \<inter> V"
      using x0_in_UV by simp_all
    show "subpathin 0 1 (word_loop WordNil) ` {0..1} \<subseteq> U"
    proof
      fix y
      assume "y \<in> subpathin 0 1 (word_loop WordNil) ` {0..1}"
      then obtain t where "t \<in> {0..1}" and y_eq: "y = subpathin 0 1 (word_loop WordNil) t"
        by blast
      have "y = x0"
        using y_eq by (simp add: word_loop.simps subpathin_def)
      then show "y \<in> U"
        using x0_in_U by simp
    qed
  qed
  have nil_hom:
    "homotopic_paths U (segment_loop (word_loop WordNil) 0 1) (word_loop WordNil)"
    by (rule segment_loop_base_full_in_set[OF nil_loopU])
  have nil_class:
    "loop_class U x0 (segment_loop (word_loop WordNil) 0 1) = one1"
  proof -
    have "loop_class U x0 (segment_loop (word_loop WordNil) 0 1) =
        loop_class U x0 (word_loop WordNil)"
      by (rule loop_class_eqI[OF nil_segU nil_loopU nil_hom])
    then show ?thesis
      unfolding word_loop.simps fundamental_group_one_def by simp
  qed
  have one1_in: "one1 \<in> G1"
    by (rule fundamental_group_one_in_space[OF x0_in_U])
  have red:
    "carrier_fpw_reduction G1 G2 mult1 one1 mult2 one2
      (WordLeft one1 WordNil) WordNil"
    by (rule carrier_fpw_reduction.step,
        rule carrier_fpw_reduction_step.remove_left_one[OF one1_in], simp)
  show ?case
    using nil_class red
    by (simp add: carrier_full_amalg_equiv.of_reduction)
next
  case (WordLeft a rest)
  then have a_in: "a \<in> G1" and rest_in: "fpw_in_space G1 G2 rest"
    by auto
  have a_loopU: "some_loop U x0 a \<in> loop_space U x0"
    using some_loop_spec[OF a_in] by auto
  have a_loopW: "some_loop U x0 a \<in> loop_space W x0"
    using a_loopU unfolding loop_space_def by auto
  show ?case
  proof (cases "rest = WordNil")
    case True
    then show ?thesis
      using segment_loop_some_loop_left_class[OF a_in]
      by simp
  next
    case False
    have rest_loopW: "word_loop rest \<in> loop_space W x0"
      by (rule word_loop_in_W[OF rest_in])
    have rest_valid:
      "valid_partition (word_loop rest) (word_partition_times rest) (word_partition_bits rest)"
      by (rule word_loop_valid_partition[OF rest_in])
    have rest_svk:
      "svk_partition (word_loop rest) (word_partition_times rest) (word_partition_bits rest)"
      using rest_valid unfolding valid_partition_def by auto
    have rest_times_nonempty: "word_partition_times rest \<noteq> []"
      using rest_valid unfolding valid_partition_def by auto
    have rest_times_hd: "hd (word_partition_times rest) = 0"
      using rest_valid unfolding valid_partition_def by auto
    have rest_times: "word_partition_times rest = 0 # tl (word_partition_times rest)"
    proof (cases "word_partition_times rest")
      case Nil
      with rest_times_nonempty show ?thesis
        by simp
    next
      case (Cons s ss)
      have "s = 0"
        using rest_times_hd Cons by simp
      then show ?thesis
        using Cons by simp
    qed
    have scaled_times:
      "map (\<lambda>t. (1 + t) / 2) (word_partition_times rest) =
        1 / 2 # map (\<lambda>t. (1 + t) / 2) (tl (word_partition_times rest))"
    proof -
      have "map (\<lambda>t. (1 + t) / 2) (word_partition_times rest) =
          map (\<lambda>t. (1 + t) / 2) (0 # tl (word_partition_times rest))"
        using rest_times by simp
      also have "\<dots> = 1 / 2 # map (\<lambda>t. (1 + t) / 2) (tl (word_partition_times rest))"
        by simp
      finally show ?thesis .
    qed
    have tail_eq:
      "partition_word (some_loop U x0 a +++ word_loop rest)
          (map (\<lambda>t. (1 + t) / 2) (word_partition_times rest))
          (word_partition_bits rest) =
        partition_word (word_loop rest) (word_partition_times rest) (word_partition_bits rest)"
      by (rule partition_word_joinpaths_tail_scaled[OF a_loopW rest_loopW rest_svk])
    have head_eq:
      "loop_class U x0
          (segment_loop (some_loop U x0 a +++ word_loop rest) 0 (1 / 2)) = a"
      using segment_loop_some_loop_left_class[OF a_in]
      by (simp add: segment_loop_joinpaths_head[OF a_loopU rest_loopW])
    have tail_eq':
      "partition_word (some_loop U x0 a +++ word_loop rest)
          (1 / 2 # map (\<lambda>t. (1 + t) / 2) (tl (word_partition_times rest)))
          (word_partition_bits rest) =
        partition_word (word_loop rest) (word_partition_times rest) (word_partition_bits rest)"
      using tail_eq scaled_times by simp
    have step_eq:
      "partition_word (word_loop (WordLeft a rest))
          (word_partition_times (WordLeft a rest))
          (word_partition_bits (WordLeft a rest)) =
        WordLeft a
          (partition_word (word_loop rest) (word_partition_times rest) (word_partition_bits rest))"
    proof -
      have "partition_word (word_loop (WordLeft a rest))
          (word_partition_times (WordLeft a rest))
          (word_partition_bits (WordLeft a rest)) =
        WordLeft (loop_class U x0
            (segment_loop (some_loop U x0 a +++ word_loop rest) 0 (1 / 2)))
          (partition_word (some_loop U x0 a +++ word_loop rest)
            (1 / 2 # map (\<lambda>t. (1 + t) / 2) (tl (word_partition_times rest)))
            (word_partition_bits rest))"
        using False scaled_times by simp
      also have "\<dots> =
        WordLeft a
          (partition_word (word_loop rest) (word_partition_times rest) (word_partition_bits rest))"
        using head_eq tail_eq' by simp
      finally show ?thesis .
    qed
    have tail_rel:
      "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2
        (partition_word (word_loop rest) (word_partition_times rest) (word_partition_bits rest))
        rest"
      by (rule WordLeft.IH[OF rest_in])
    have
      "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2
        (WordLeft a
          (partition_word (word_loop rest) (word_partition_times rest) (word_partition_bits rest)))
        (WordLeft a rest)"
      by (rule carrier_full_amalg_equiv_left_context[OF tail_rel a_in])
    then show ?thesis
      by (subst step_eq) simp
  qed
next
  case (WordRight b rest)
  then have b_in: "b \<in> G2" and rest_in: "fpw_in_space G1 G2 rest"
    by auto
  have b_loopV: "some_loop V x0 b \<in> loop_space V x0"
    using some_loop_spec[OF b_in] by auto
  have b_loopW: "some_loop V x0 b \<in> loop_space W x0"
    using b_loopV unfolding loop_space_def by auto
  show ?case
  proof (cases "rest = WordNil")
    case True
    then show ?thesis
      using segment_loop_some_loop_right_class[OF b_in]
      by simp
  next
    case False
    have rest_loopW: "word_loop rest \<in> loop_space W x0"
      by (rule word_loop_in_W[OF rest_in])
    have rest_valid:
      "valid_partition (word_loop rest) (word_partition_times rest) (word_partition_bits rest)"
      by (rule word_loop_valid_partition[OF rest_in])
    have rest_svk:
      "svk_partition (word_loop rest) (word_partition_times rest) (word_partition_bits rest)"
      using rest_valid unfolding valid_partition_def by auto
    have rest_times_nonempty: "word_partition_times rest \<noteq> []"
      using rest_valid unfolding valid_partition_def by auto
    have rest_times_hd: "hd (word_partition_times rest) = 0"
      using rest_valid unfolding valid_partition_def by auto
    have rest_times: "word_partition_times rest = 0 # tl (word_partition_times rest)"
    proof (cases "word_partition_times rest")
      case Nil
      with rest_times_nonempty show ?thesis
        by simp
    next
      case (Cons s ss)
      have "s = 0"
        using rest_times_hd Cons by simp
      then show ?thesis
        using Cons by simp
    qed
    have scaled_times:
      "map (\<lambda>t. (1 + t) / 2) (word_partition_times rest) =
        1 / 2 # map (\<lambda>t. (1 + t) / 2) (tl (word_partition_times rest))"
    proof -
      have "map (\<lambda>t. (1 + t) / 2) (word_partition_times rest) =
          map (\<lambda>t. (1 + t) / 2) (0 # tl (word_partition_times rest))"
        using rest_times by simp
      also have "\<dots> = 1 / 2 # map (\<lambda>t. (1 + t) / 2) (tl (word_partition_times rest))"
        by simp
      finally show ?thesis .
    qed
    have tail_eq:
      "partition_word (some_loop V x0 b +++ word_loop rest)
          (map (\<lambda>t. (1 + t) / 2) (word_partition_times rest))
          (word_partition_bits rest) =
        partition_word (word_loop rest) (word_partition_times rest) (word_partition_bits rest)"
      by (rule partition_word_joinpaths_tail_scaled[OF b_loopW rest_loopW rest_svk])
    have head_eq:
      "loop_class V x0
          (segment_loop (some_loop V x0 b +++ word_loop rest) 0 (1 / 2)) = b"
      using segment_loop_some_loop_right_class[OF b_in]
      by (simp add: segment_loop_joinpaths_head[OF b_loopV rest_loopW])
    have tail_eq':
      "partition_word (some_loop V x0 b +++ word_loop rest)
          (1 / 2 # map (\<lambda>t. (1 + t) / 2) (tl (word_partition_times rest)))
          (word_partition_bits rest) =
        partition_word (word_loop rest) (word_partition_times rest) (word_partition_bits rest)"
      using tail_eq scaled_times by simp
    have step_eq:
      "partition_word (word_loop (WordRight b rest))
          (word_partition_times (WordRight b rest))
          (word_partition_bits (WordRight b rest)) =
        WordRight b
          (partition_word (word_loop rest) (word_partition_times rest) (word_partition_bits rest))"
    proof -
      have "partition_word (word_loop (WordRight b rest))
          (word_partition_times (WordRight b rest))
          (word_partition_bits (WordRight b rest)) =
        WordRight (loop_class V x0
            (segment_loop (some_loop V x0 b +++ word_loop rest) 0 (1 / 2)))
          (partition_word (some_loop V x0 b +++ word_loop rest)
            (1 / 2 # map (\<lambda>t. (1 + t) / 2) (tl (word_partition_times rest)))
            (word_partition_bits rest))"
        using False scaled_times by simp
      also have "\<dots> =
        WordRight b
          (partition_word (word_loop rest) (word_partition_times rest) (word_partition_bits rest))"
        using head_eq tail_eq' by simp
      finally show ?thesis .
    qed
    have tail_rel:
      "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2
        (partition_word (word_loop rest) (word_partition_times rest) (word_partition_bits rest))
        rest"
      by (rule WordRight.IH[OF rest_in])
    have
      "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2
        (WordRight b
          (partition_word (word_loop rest) (word_partition_times rest) (word_partition_bits rest)))
        (WordRight b rest)"
      by (rule carrier_full_amalg_equiv_right_context[OF tail_rel b_in])
    then show ?thesis
      by (subst step_eq) simp
  qed
qed

lemma valid_partition_hd:
  assumes "valid_partition p ts bs"
  shows "ts \<noteq> []" "hd ts = 0"
  using assms unfolding valid_partition_def by auto

lemma valid_partition_cases:
  assumes "valid_partition p (t # ts) bs"
  shows "t = 0" and "svk_partition p (t # ts) bs"
  using assms unfolding valid_partition_def by auto

lemma svk_partition_head_props:
  assumes "svk_partition p (t # ts) bs"
  shows "t \<in> {0..1}" and "p t \<in> U \<inter> V"
proof -
  show "t \<in> {0..1}"
  proof (cases ts)
    case Nil
    then show ?thesis
      using assms by (cases bs) auto
  next
    case (Cons u us)
    then show ?thesis
      using assms by (cases bs) auto
  qed
next
  show "p t \<in> U \<inter> V"
  proof (cases ts)
    case Nil
    then show ?thesis
      using assms by (cases bs) auto
  next
    case (Cons u us)
    then show ?thesis
      using assms by (cases bs) auto
  qed
qed

lemma svk_partition_tail:
  assumes "svk_partition p (t # u # ts) (b # bs)"
  shows "svk_partition p (u # ts) bs"
  using assms by simp

lemma svk_partition_step_props:
  assumes "svk_partition p (t # u # ts) (b # bs)"
  shows "t \<in> {0..1}"
    and "p t \<in> U \<inter> V"
    and "u \<in> {0..1}"
    and "t < u"
    and "(if b then subpathin t u p ` {0..1} \<subseteq> U else subpathin t u p ` {0..1} \<subseteq> V)"
  using assms by simp_all

lemma svk_partition_next_in_intersection:
  assumes "svk_partition p (t # u # ts) (b # bs)"
  shows "p u \<in> U \<inter> V"
proof -
  have "svk_partition p (u # ts) bs"
    using assms by simp
  then show ?thesis
    by (rule svk_partition_head_props(2))
qed

lemma svk_partition_nonempty:
  assumes "svk_partition p ts bs"
  shows "ts \<noteq> []"
  using assms by (cases ts) simp_all

lemma svk_partition_last_eq_one:
  assumes part: "svk_partition p ts bs"
  shows "last ts = 1"
  using part
proof (induction ts arbitrary: bs)
  case Nil
  then show ?case
    by simp
next
  case (Cons t ts)
  show ?case
  proof (cases ts)
    case Nil
    then show ?thesis
      using Cons.prems by (cases bs) auto
  next
    case (Cons u us)
    then obtain b bs' where bs: "bs = b # bs'"
      using Cons.prems by (cases bs) auto
    have tail: "svk_partition p (u # us) bs'"
      using Cons.prems Cons bs by simp
    from Cons.IH[of bs'] Cons tail show ?thesis
      by simp
  qed
qed

lemma svk_partition_last_in_intersection:
  assumes part: "svk_partition p ts bs"
  shows "p (last ts) \<in> U \<inter> V"
  using part
proof (induction ts arbitrary: bs)
  case Nil
  then show ?case
    by simp
next
  case (Cons t ts)
  show ?case
  proof (cases ts)
    case Nil
    then show ?thesis
      using Cons.prems by (cases bs) auto
  next
    case (Cons u us)
    then obtain b bs' where bs: "bs = b # bs'"
      using Cons.prems by (cases bs) auto
    have tail: "svk_partition p (u # us) bs'"
      using Cons.prems Cons bs by simp
    from Cons.IH[of bs'] Cons tail show ?thesis
      by simp
  qed
qed

lemma svk_partition_last_props:
  assumes part: "svk_partition p ts bs"
  shows "ts \<noteq> []" and "last ts = 1" and "p (last ts) \<in> U \<inter> V"
  using svk_partition_nonempty[OF part]
    svk_partition_last_eq_one[OF part]
    svk_partition_last_in_intersection[OF part]
  by auto

lemma valid_partition_last_props:
  assumes "valid_partition p ts bs"
  shows "ts \<noteq> []" and "last ts = 1" and "p (last ts) \<in> U \<inter> V"
proof -
  have ts_ne: "ts \<noteq> []"
    using assms unfolding valid_partition_def by auto
  have part: "svk_partition p ts bs"
    using assms unfolding valid_partition_def by auto
  show "ts \<noteq> []"
    by (rule ts_ne)
  from svk_partition_last_props[OF part] ts_ne
  show "last ts = 1" and "p (last ts) \<in> U \<inter> V"
    by auto
qed

lemma subpathin_endpoints_in_set:
  assumes seg_in: "subpathin u v p ` {0..1} \<subseteq> S"
  shows "p u \<in> S" and "p v \<in> S"
proof -
  have u_in: "subpathin u v p 0 \<in> S"
    using seg_in by auto
  then show "p u \<in> S"
    by (simp add: subpathin_def)
  have v_in: "subpathin u v p 1 \<in> S"
    using seg_in by auto
  then show "p v \<in> S"
    by (simp add: subpathin_def)
qed

lemma subpathin_image_subset_union:
  assumes tu: "t \<le> u"
    and uv: "u \<le> v"
  shows "subpathin t v p ` {0..1} \<subseteq> subpathin t u p ` {0..1} \<union> subpathin u v p ` {0..1}"
proof -
  have seg_subset: "closed_segment t v \<subseteq> closed_segment t u \<union> closed_segment u v"
    using tu uv by (auto simp: closed_segment_eq_real_ivl)
  show ?thesis
    using seg_subset by (auto simp: subpathin_image)
qed

lemma subpathin_image_subset_trans:
  assumes tu: "t \<le> u"
    and uv: "u \<le> v"
    and left: "subpathin t u p ` {0..1} \<subseteq> S"
    and right: "subpathin u v p ` {0..1} \<subseteq> S"
  shows "subpathin t v p ` {0..1} \<subseteq> S"
  using subpathin_image_subset_union[OF tu uv, of p] left right by blast

lemma cover_partition_step_props:
  assumes "cover_partition p (t # u # ts) (b # bs)"
  shows "t \<in> {0..1}"
    and "u \<in> {0..1}"
    and "t < u"
    and "(if b then subpathin t u p ` {0..1} \<subseteq> U else subpathin t u p ` {0..1} \<subseteq> V)"
    and "cover_partition p (u # ts) bs"
  using assms by simp_all

lemma cover_partition_consI:
  assumes "t \<in> {0..1}"
    and "u \<in> {0..1}"
    and "t < u"
    and "(if b then subpathin t u p ` {0..1} \<subseteq> U else subpathin t u p ` {0..1} \<subseteq> V)"
    and "cover_partition p (u # ts) bs"
  shows "cover_partition p (t # u # ts) (b # bs)"
  using assms by simp

lemma cover_partition_switch_point:
  assumes cp: "cover_partition p (t # u # v # ts) (b # c # bs)"
    and diff: "b \<noteq> c"
  shows "p u \<in> U \<inter> V"
proof (cases b)
  case True
  then have leftU: "subpathin t u p ` {0..1} \<subseteq> U"
    using cp by simp
  from diff True have c_false: "\<not> c"
    by simp
  then have rightV: "subpathin u v p ` {0..1} \<subseteq> V"
    using cp by simp
  show ?thesis
    using subpathin_endpoints_in_set(2)[OF leftU] subpathin_endpoints_in_set(1)[OF rightV]
    by blast
next
  case False
  then have leftV: "subpathin t u p ` {0..1} \<subseteq> V"
    using cp by simp
  from diff False have c_true: "c"
    by simp
  then have rightU: "subpathin u v p ` {0..1} \<subseteq> U"
    using cp by simp
  show ?thesis
    using subpathin_endpoints_in_set(1)[OF rightU] subpathin_endpoints_in_set(2)[OF leftV]
    by blast
qed

lemma cover_partition_pair_svk_partition:
  assumes cp: "cover_partition p [t, u] [b]"
    and ptUV: "p t \<in> U \<inter> V"
    and puUV: "p u \<in> U \<inter> V"
  shows "svk_partition p [t, u] [b]"
proof -
  have t01: "t \<in> {0..1}"
    using cp by simp
  have u01: "u \<in> {0..1}"
    using cp by simp
  have tu: "t < u"
    using cp by simp
  have u1: "u = 1"
    using cp by simp
  have seg: "(if b then subpathin t u p ` {0..1} \<subseteq> U else subpathin t u p ` {0..1} \<subseteq> V)"
  proof (cases b)
    case True
    then show ?thesis
      using cp u1 by simp
  next
    case False
    then show ?thesis
      using cp u1 by simp
  qed
  have tail: "svk_partition p [u] []"
    using u1 puUV by simp
  show ?thesis
  proof (cases b)
    case True
    then show ?thesis
      using t01 ptUV u01 tu seg u1 puUV by simp
  next
    case False
    then show ?thesis
      using t01 ptUV u01 tu seg u1 puUV by simp
  qed
qed

lemma cover_partition_compress_svk_partition:
  assumes cp: "cover_partition p (t # ts) bs"
    and ptUV: "p t \<in> U \<inter> V"
    and plastUV: "p (last (t # ts)) \<in> U \<inter> V"
  shows "\<exists>ts' bs'. svk_partition p (t # ts') bs'"
  using assms
proof (induction "length bs" arbitrary: bs t ts rule: less_induct)
  case less
  show ?case
  proof (cases bs)
    case Nil
    show ?thesis
    proof (cases ts)
      case Nil_ts: Nil
      then have t1: "t = 1"
        using less.prems(1) Nil by simp
      have "svk_partition p [t] []"
        using t1 less.prems(2) by simp
      show ?thesis
      proof
        show "\<exists>bs'. svk_partition p (t # []) bs'"
        proof
          show "svk_partition p (t # []) []"
            using t1 less.prems(2) by simp
        qed
      qed
    next
      case (Cons u us)
      then have False
        using less.prems(1) Nil by simp
      then show ?thesis
        by simp
    qed
  next
    case (Cons b bs0)
    note bs_cons = Cons
    show ?thesis
    proof (cases bs0)
      case Nil
      then obtain u where ts: "ts = [u]"
      proof (cases ts)
        case Nil
        then have False
          using less.prems(1) bs_cons Nil by simp
        then show thesis
          by simp
      next
        case (Cons u ts0)
        note ts_cons = Cons
        then show thesis
        proof (cases ts0)
          case Nil
          have ts_single: "ts = [u]"
            using ts_cons Nil by simp
          from ts_single show thesis
            by (rule that[of u])
        next
          case (Cons v us)
          then have False
            using less.prems(1) bs_cons Nil ts_cons by simp
          then show thesis
            by simp
        qed
      qed
      have puUV: "p u \<in> U \<inter> V"
        using less.prems(3) unfolding ts by simp
      have t01: "t \<in> {0..1}"
        using less.prems(1) bs_cons Nil ts by simp
      have u01: "u \<in> {0..1}"
        using less.prems(1) bs_cons Nil ts by simp
      have tu: "t < u"
        using less.prems(1) bs_cons Nil ts by simp
      have u1: "u = 1"
        using less.prems(1) bs_cons Nil ts by simp
      have seg_tu: "(if b then subpathin t u p ` {0..1} \<subseteq> U else subpathin t u p ` {0..1} \<subseteq> V)"
      proof (cases b)
        case True
        then show ?thesis
          using less.prems(1) bs_cons Nil ts u1 by simp
      next
        case False
        then show ?thesis
          using less.prems(1) bs_cons Nil ts u1 by simp
      qed
      have part_tu: "svk_partition p [t, u] [b]"
      proof (cases b)
        case True
        then show ?thesis
          using t01 less.prems(2) u01 tu seg_tu u1 puUV by simp
      next
        case False
        then show ?thesis
          using t01 less.prems(2) u01 tu seg_tu u1 puUV by simp
      qed
      show ?thesis
      proof
        show "\<exists>bs'. svk_partition p (t # [u]) bs'"
        proof
          show "svk_partition p (t # [u]) [b]"
            by (rule part_tu)
        qed
      qed
    next
      case (Cons c bs')
      note bs0_cons = Cons
      have bs_eq: "bs = b # c # bs'"
        using bs_cons bs0_cons by simp
      then obtain u v us where ts: "ts = u # v # us"
      proof (cases ts)
        case Nil
        then have False
          using less.prems(1) bs_cons bs0_cons by simp
        then show thesis
          by simp
      next
        case (Cons u ts0)
        note ts_cons = Cons
        then show thesis
        proof (cases ts0)
          case Nil
          then have False
            using less.prems(1) bs_cons bs0_cons ts_cons by simp
          then show thesis
            by simp
        next
          case (Cons v us)
          have ts_long: "ts = u # v # us"
            using ts_cons Cons by simp
          from ts_long show thesis
            by (rule that[of u v us])
        qed
      qed
      have cp_step: "cover_partition p (t # u # v # us) (b # c # bs')"
        using less.prems(1) bs_cons bs0_cons ts by simp
      have t01: "t \<in> {0..1}" and u01: "u \<in> {0..1}" and tu: "t < u"
        and seg_tu: "(if b then subpathin t u p ` {0..1} \<subseteq> U else subpathin t u p ` {0..1} \<subseteq> V)"
        and cp_tail: "cover_partition p (u # v # us) (c # bs')"
        using cp_step by (rule cover_partition_step_props)+
      show ?thesis
      proof (cases "b = c")
        case True
        note bits_eq = True
        have uv: "u < v"
          using cp_tail by simp
        have tu_le: "t \<le> u"
          using tu by simp
        have uv_le: "u \<le> v"
          using uv by simp
        have seg_tv: "(if b then subpathin t v p ` {0..1} \<subseteq> U else subpathin t v p ` {0..1} \<subseteq> V)"
        proof (cases b)
          case True
          then have leftU: "subpathin t u p ` {0..1} \<subseteq> U"
            using seg_tu by simp
          have rightU: "subpathin u v p ` {0..1} \<subseteq> U"
            using cp_tail bits_eq True by simp
          have seg_U: "subpathin t v p ` {0..1} \<subseteq> U"
            by (rule subpathin_image_subset_trans[OF tu_le uv_le leftU rightU])
          then show ?thesis
            using True by simp
        next
          case False
          then have leftV: "subpathin t u p ` {0..1} \<subseteq> V"
            using seg_tu by simp
          have rightV: "subpathin u v p ` {0..1} \<subseteq> V"
            using cp_tail bits_eq False by simp
          have seg_V: "subpathin t v p ` {0..1} \<subseteq> V"
            by (rule subpathin_image_subset_trans[OF tu_le uv_le leftV rightV])
          then show ?thesis
            using False by simp
        qed
        have cp_merged: "cover_partition p (t # v # us) (b # bs')"
          using cp_tail t01 seg_tv tu u01 by simp
        have shorter: "length (b # bs') < length bs"
          using bs_eq by simp
        have plast_merged: "p (last (t # v # us)) \<in> U \<inter> V"
          using less.prems(3) unfolding ts by simp
        have merged_part: "\<exists>ts' bs''. svk_partition p (t # ts') bs''"
          by (rule less.hyps[of "b # bs'" t "v # us"]) (use shorter cp_merged less.prems(2) plast_merged in simp_all)
        from merged_part obtain ts' bs'' where "svk_partition p (t # ts') bs''"
          by blast
        then show ?thesis
          by blast
      next
        case False
        have puUV: "p u \<in> U \<inter> V"
          by (rule cover_partition_switch_point[OF cp_step False])
        have shorter: "length (c # bs') < length bs"
          using bs_eq by simp
        have plast_tail: "p (last (u # v # us)) \<in> U \<inter> V"
          using less.prems(3) unfolding ts by simp
        have tail_exists: "\<exists>us' bs''. svk_partition p (u # us') bs''"
          by (rule less.hyps[of "c # bs'" u "v # us"]) (use shorter cp_tail puUV plast_tail in simp_all)
        from tail_exists obtain us' bs'' where tail_part: "svk_partition p (u # us') bs''"
          by blast
        have "svk_partition p (t # u # us') (b # bs'')"
          using t01 u01 tu seg_tu less.prems(2) puUV tail_part by simp
        then show ?thesis
          by blast
      qed
    qed
  qed
qed

lemma cover_partition_last_eq_one:
  assumes cp: "cover_partition p ts bs"
    and ts_ne: "ts \<noteq> []"
  shows "last ts = 1"
  using cp ts_ne
proof (induction ts arbitrary: bs)
  case Nil
  then show ?case
    by simp
next
  case (Cons t ts)
  show ?case
  proof (cases ts)
    case Nil
    then show ?thesis
      using Cons.prems by (cases bs) simp_all
  next
    case (Cons u us)
    then obtain b bs' where bs: "bs = b # bs'"
      using Cons.prems by (cases bs) auto
    have tail: "cover_partition p (u # us) bs'"
      using Cons.prems Cons bs by simp
    have ts_ne_tail: "ts \<noteq> []"
      using Cons by simp
    have last_ts: "last ts = 1"
      by (rule Cons.IH[of bs']) (use tail ts_ne_tail Cons in simp_all)
    have last_tail: "last (u # us) = 1"
      using last_ts Cons by simp
    then show ?thesis
      using Cons by simp
  qed
qed

lemma nat_real_div_in_unit_interval:
  assumes n_pos: "0 < n"
    and i_le: "i \<le> n"
  shows "real i / real n \<in> {0..1}"
proof -
  have n_real_pos: "0 < real n"
  proof -
    have "real 0 < real n"
      using n_pos by (rule less_imp_of_nat_less)
    then show ?thesis
      by simp
  qed
  have lower: "0 \<le> real i / real n"
    using n_real_pos by (simp add: zero_le_divide_iff)
  have i_real_le: "real i \<le> real n"
    using i_le by simp
  have upper: "real i / real n \<le> 1"
  proof -
    have "real i / real n \<le> real n / real n"
      using i_real_le n_real_pos by (intro divide_right_mono) simp_all
    then show ?thesis
      using n_real_pos by simp
  qed
  show ?thesis
    using lower upper by auto
qed

lemma nat_real_div_strict_mono:
  assumes n_pos: "0 < n"
    and i_lt: "i < n"
  shows "real i / real n < real (Suc i) / real n"
proof -
  have "real i < real (Suc i)"
    by simp
  then show ?thesis
    using n_pos by (simp add: divide_strict_right_mono)
qed

fun subdivision_times :: "nat \<Rightarrow> nat \<Rightarrow> real list" where
  "subdivision_times n 0 = [1]"
| "subdivision_times n (Suc k) = real (n - Suc k) / real n # subdivision_times n k"

fun subdivision_bits :: "(nat \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool list" where
  "subdivision_bits side n 0 = []"
| "subdivision_bits side n (Suc k) = side (n - Suc k) # subdivision_bits side n k"

lemma cover_partition_subdivision_from:
  assumes n_pos: "0 < n"
    and k_le: "k \<le> n"
    and cover: "\<And>i. n - k \<le> i \<Longrightarrow> i < n \<Longrightarrow>
      (if side i
       then subpathin (real i / real n) (real (Suc i) / real n) p ` {0..1} \<subseteq> U
       else subpathin (real i / real n) (real (Suc i) / real n) p ` {0..1} \<subseteq> V)"
  shows "cover_partition p (subdivision_times n k) (subdivision_bits side n k)"
  using k_le cover
proof (induction k)
  case 0
  then show ?case
    by simp
next
  case (Suc k)
  have k_le_n: "k \<le> n"
    using Suc.prems by simp
  have i0_lt_n: "n - Suc k < n"
    using Suc.prems n_pos by arith
  have i0_le_n: "n - Suc k \<le> n"
    by arith
  have i1_le_n: "n - k \<le> n"
    by arith
  have nk: "n - k = Suc (n - Suc k)"
    using Suc.prems by arith
  have t01: "real (n - Suc k) / real n \<in> {0..1}"
    by (rule nat_real_div_in_unit_interval[OF n_pos i0_le_n])
  have u01: "real (n - k) / real n \<in> {0..1}"
    by (rule nat_real_div_in_unit_interval[OF n_pos i1_le_n])
  have tu: "real (n - Suc k) / real n < real (n - k) / real n"
    unfolding nk by (rule nat_real_div_strict_mono[OF n_pos i0_lt_n])
  have seg_side_suc:
    "(if side (n - Suc k)
      then subpathin (real (n - Suc k) / real n) (real (Suc (n - Suc k)) / real n) p ` {0..1} \<subseteq> U
      else subpathin (real (n - Suc k) / real n) (real (Suc (n - Suc k)) / real n) p ` {0..1} \<subseteq> V)"
    by (rule Suc.prems(2)[of "n - Suc k"]) (use i0_lt_n in simp_all)
  have seg_side:
    "(if side (n - Suc k)
      then subpathin (real (n - Suc k) / real n) (real (n - k) / real n) p ` {0..1} \<subseteq> U
      else subpathin (real (n - Suc k) / real n) (real (n - k) / real n) p ` {0..1} \<subseteq> V)"
  proof (cases "side (n - Suc k)")
    case True
    then show ?thesis
      using seg_side_suc nk by simp
  next
    case False
    then show ?thesis
      using seg_side_suc nk by simp
  qed
  have tail_cover:
    "\<And>i. n - k \<le> i \<Longrightarrow> i < n \<Longrightarrow>
      (if side i
       then subpathin (real i / real n) (real (Suc i) / real n) p ` {0..1} \<subseteq> U
       else subpathin (real i / real n) (real (Suc i) / real n) p ` {0..1} \<subseteq> V)"
  proof -
    fix i
    assume i_lb: "n - k \<le> i"
      and i_lt: "i < n"
    have i_lb': "n - Suc k \<le> i"
      using i_lb by arith
    show "(if side i
      then subpathin (real i / real n) (real (Suc i) / real n) p ` {0..1} \<subseteq> U
      else subpathin (real i / real n) (real (Suc i) / real n) p ` {0..1} \<subseteq> V)"
      by (rule Suc.prems(2)[OF i_lb' i_lt])
  qed
  have tail_cp: "cover_partition p (subdivision_times n k) (subdivision_bits side n k)"
    by (rule Suc.IH[OF k_le_n tail_cover])
  show ?case
  proof (cases k)
    case 0
    have t0_nonneg: "0 \<le> real (n - Suc 0) / real n"
      and t0_le1: "real (n - Suc 0) / real n \<le> 1"
      using t01 0 by auto
    have tu0: "real (n - Suc 0) / real n < 1"
      using tu 0 n_pos by simp
    have seg0_raw:
      "(if side (n - Suc 0)
        then subpathin (real (n - Suc 0) / real n) (real (n - 0) / real n) p ` {0..1} \<subseteq> U
        else subpathin (real (n - Suc 0) / real n) (real (n - 0) / real n) p ` {0..1} \<subseteq> V)"
      using seg_side
      unfolding 0
      by simp
    have end_eq: "real (n - 0) / real n = 1"
      using n_pos by simp
    have seg0:
      "(if side (n - Suc 0)
        then subpathin (real (n - Suc 0) / real n) 1 p ` {0..1} \<subseteq> U
        else subpathin (real (n - Suc 0) / real n) 1 p ` {0..1} \<subseteq> V)"
      using seg0_raw end_eq by (cases "side (n - Suc 0)") simp_all
    have tail0: "cover_partition p [1] []"
      using tail_cp 0 by simp
    then show ?thesis
      unfolding 0 subdivision_times.simps subdivision_bits.simps
      using t0_nonneg t0_le1 tu0 seg0 tail0
      by simp
  next
    case (Suc j)
    have t01_suc: "real (n - Suc (Suc j)) / real n \<in> {0..1}"
      using t01 by (simp only: Suc)
    have u01_suc: "real (n - Suc j) / real n \<in> {0..1}"
      using u01 by (simp only: Suc)
    have tu_suc: "real (n - Suc (Suc j)) / real n < real (n - Suc j) / real n"
      using tu by (simp only: Suc)
    have seg_suc:
      "(if side (n - Suc (Suc j))
        then subpathin (real (n - Suc (Suc j)) / real n) (real (n - Suc j) / real n) p ` {0..1} \<subseteq> U
        else subpathin (real (n - Suc (Suc j)) / real n) (real (n - Suc j) / real n) p ` {0..1} \<subseteq> V)"
      using seg_side by (simp only: Suc)
    have tail_suc:
      "cover_partition p
        (real (n - Suc j) / real n # subdivision_times n j)
        (side (n - Suc j) # subdivision_bits side n j)"
      using tail_cp by (simp only: Suc subdivision_times.simps subdivision_bits.simps)
    have times_suc:
      "subdivision_times n (Suc (Suc j)) =
        real (n - Suc (Suc j)) / real n # real (n - Suc j) / real n # subdivision_times n j"
      by simp
    have bits_suc:
      "subdivision_bits side n (Suc (Suc j)) =
        side (n - Suc (Suc j)) # side (n - Suc j) # subdivision_bits side n j"
      by simp
    show ?thesis
      unfolding Suc times_suc bits_suc
      by (rule cover_partition_consI[OF t01_suc u01_suc tu_suc seg_suc tail_suc])
  qed
qed

lemma subdivision_times_start:
  assumes n_pos: "0 < n"
  shows "subdivision_times n n = 0 # subdivision_times n (n - 1)"
  using n_pos by (cases n) simp_all

lemma loop_has_valid_partition:
  assumes p_loop: "p \<in> loop_space W x0"
  shows "\<exists>ts bs. valid_partition p ts bs"
proof -
  obtain n :: nat where n_pos: "0 < n"
    and n_cover:
      "\<forall>i<n.
        subpathin (real i / real n) (real (Suc i) / real n) p ` {0..1} \<subseteq> U \<or>
        subpathin (real i / real n) (real (Suc i) / real n) p ` {0..1} \<subseteq> V"
    using loop_subdivision_by_cover[OF p_loop] by blast
  let ?side = "\<lambda>i. subpathin (real i / real n) (real (Suc i) / real n) p ` {0..1} \<subseteq> U"
  have raw: "cover_partition p (subdivision_times n n) (subdivision_bits ?side n n)"
  proof (rule cover_partition_subdivision_from[OF n_pos le_refl])
    fix i
    assume "n - n \<le> i" and i_lt: "i < n"
    from n_cover[rule_format, OF i_lt]
    show "(if ?side i
      then subpathin (real i / real n) (real (Suc i) / real n) p ` {0..1} \<subseteq> U
      else subpathin (real i / real n) (real (Suc i) / real n) p ` {0..1} \<subseteq> V)"
      by auto
  qed
  have times0: "subdivision_times n n = 0 # subdivision_times n (n - 1)"
    by (rule subdivision_times_start[OF n_pos])
  have times_ne: "subdivision_times n n \<noteq> []"
    using times0 by simp
  have last1: "last (subdivision_times n n) = 1"
    by (rule cover_partition_last_eq_one[OF raw times_ne])
  have p0UV: "p 0 \<in> U \<inter> V" and p1UV: "p 1 \<in> U \<inter> V"
    using p_loop x0_in_UV unfolding loop_space_def pathstart_def pathfinish_def by auto
  have raw0: "cover_partition p (0 # subdivision_times n (n - 1)) (subdivision_bits ?side n n)"
    using raw times0 by simp
  have plastUV: "p (last (0 # subdivision_times n (n - 1))) \<in> U \<inter> V"
    using p1UV last1 times0 by simp
  from cover_partition_compress_svk_partition[OF raw0 p0UV plastUV]
  obtain ts' bs' where part: "svk_partition p (0 # ts') bs'"
    by blast
  have "valid_partition p (0 # ts') bs'"
    unfolding valid_partition_def using part by simp
  then show ?thesis
    by blast
qed

lemma svk_partition_partition_word_in_space:
  assumes p_loop: "p \<in> loop_space W x0"
    and part: "svk_partition p ts bs"
  shows "fpw_in_space G1 G2 (partition_word p ts bs)"
  using part
proof (induction ts arbitrary: bs)
  case Nil
  then show ?case
    by simp
next
  case (Cons t ts)
  from p_loop have p_path: "path p" and p_image: "path_image p \<subseteq> W"
    unfolding loop_space_def by auto
  show ?case
  proof (cases ts)
    case Nil
    then show ?thesis
      using Cons.prems by (cases bs) simp_all
  next
    case (Cons u us)
    then obtain b bs' where bs: "bs = b # bs'"
      using Cons.prems by (cases bs) auto
    have tail: "svk_partition p (u # us) bs'"
      using Cons.prems Cons bs by simp
    have tail_in: "fpw_in_space G1 G2 (partition_word p (u # us) bs')"
      using p_loop Cons.IH[of bs'] Cons tail by simp
    have t01: "t \<in> {0..1}" and ptUV: "p t \<in> U \<inter> V"
      using Cons.prems Cons bs by simp_all
    have u01: "u \<in> {0..1}" and seg_side:
      "(if b then subpathin t u p ` {0..1} \<subseteq> U else subpathin t u p ` {0..1} \<subseteq> V)"
      using Cons.prems Cons bs by simp_all
    have puUV: "p u \<in> U \<inter> V"
      using svk_partition_next_in_intersection[of p t u us b bs'] Cons.prems Cons bs by simp
    show ?thesis
    proof (cases b)
      case True
      have segU: "segment_loop p t u \<in> loop_space U x0"
        by (rule segment_loop_in_U[OF p_path p_image t01 u01 ptUV puUV]) (use seg_side True in simp)
      have "loop_class U x0 (segment_loop p t u) \<in> G1"
        by (rule loop_class_in_space[OF segU])
      then show ?thesis
        using tail_in True bs Cons by simp
    next
      case False
      have segV: "segment_loop p t u \<in> loop_space V x0"
        by (rule segment_loop_in_V[OF p_path p_image t01 u01 ptUV puUV]) (use seg_side False in simp)
      have "loop_class V x0 (segment_loop p t u) \<in> G2"
        by (rule loop_class_in_space[OF segV])
      then show ?thesis
        using tail_in False bs Cons by simp
    qed
  qed
qed

lemma valid_partition_partition_word_in_space:
  assumes p_loop: "p \<in> loop_space W x0"
    and part: "valid_partition p ts bs"
  shows "fpw_in_space G1 G2 (partition_word p ts bs)"
  using assms unfolding valid_partition_def
  by (auto intro: svk_partition_partition_word_in_space)

lemma svk_partition_partition_loop_in_W:
  assumes p_loop: "p \<in> loop_space W x0"
    and part: "svk_partition p ts bs"
  shows "partition_loop p ts \<in> loop_space W x0"
  using part
proof (induction ts arbitrary: bs)
  case Nil
  then show ?case
    by (simp add: constant_loop_in_space[OF x0_in_W])
next
  case (Cons t ts)
  from p_loop have p_path: "path p" and p_image: "path_image p \<subseteq> W"
    unfolding loop_space_def by auto
  show ?case
  proof (cases ts)
    case Nil
    then show ?thesis
      by (simp add: constant_loop_in_space[OF x0_in_W])
  next
    case (Cons u us)
    then obtain b bs' where bs: "bs = b # bs'"
      using Cons.prems by (cases bs) auto
    have tail: "svk_partition p (u # us) bs'"
      using Cons.prems Cons bs by simp
    have tail_loop: "partition_loop p (u # us) \<in> loop_space W x0"
      using p_loop Cons.IH[of bs'] Cons tail by simp
    have t01: "t \<in> {0..1}" and ptUV: "p t \<in> U \<inter> V"
      using Cons.prems Cons bs by simp_all
    have u01: "u \<in> {0..1}" and puUV: "p u \<in> U \<inter> V"
      using Cons.prems Cons bs svk_partition_next_in_intersection[of p t u us b bs'] by simp_all
    have segW:
      "segment_loop p t u \<in> loop_space W x0"
    proof (rule segment_loop_in_W[OF p_path p_image t01 u01 ptUV puUV])
      have sub_imgW: "path_image (subpathin t u p) \<subseteq> W"
        using p_image path_image_subpathin_subset[OF t01 u01, of p] by blast
      show "subpathin t u p ` {0..1} \<subseteq> W"
        using sub_imgW by (simp add: path_image_def)
    qed
    have joined_loop:
      "segment_loop p t u +++ partition_loop p (u # us) \<in> loop_space W x0"
      by (rule loop_space_join[OF segW tail_loop])
    show ?thesis
      using joined_loop Cons by simp
  qed
qed

lemma valid_partition_partition_loop_in_W:
  assumes p_loop: "p \<in> loop_space W x0"
    and part: "valid_partition p ts bs"
  shows "partition_loop p ts \<in> loop_space W x0"
  using assms unfolding valid_partition_def
  by (auto intro: svk_partition_partition_loop_in_W)

lemma i1_loop_class_eq:
  assumes p_loop: "p \<in> loop_space (U \<inter> V) x0"
  shows "i1 (loop_class (U \<inter> V) x0 p) = loop_class U x0 p"
proof -
  have A_in: "loop_class (U \<inter> V) x0 p \<in> fundamental_group_space (U \<inter> V) x0"
    by (rule loop_class_in_space[OF p_loop])
  have "i1 (loop_class (U \<inter> V) x0 p) = loop_class U x0 (loop_image id p)"
  proof (rule fundamental_group_map_eqI)
    show "loop_class (U \<inter> V) x0 p \<in> fundamental_group_space (U \<inter> V) x0"
      by (rule A_in)
    show "p \<in> loop_space (U \<inter> V) x0"
      by (rule p_loop)
    show "loop_class (U \<inter> V) x0 p = loop_class (U \<inter> V) x0 p"
      by simp
    show "continuous_on (U \<inter> V) id"
      by simp
    show "id \<in> (U \<inter> V) \<rightarrow> U"
      by auto
    show "id x0 = x0"
      by simp
  qed
  then show ?thesis
    by (simp add: loop_image_def)
qed

lemma i2_loop_class_eq:
  assumes p_loop: "p \<in> loop_space (U \<inter> V) x0"
  shows "i2 (loop_class (U \<inter> V) x0 p) = loop_class V x0 p"
proof -
  have A_in: "loop_class (U \<inter> V) x0 p \<in> fundamental_group_space (U \<inter> V) x0"
    by (rule loop_class_in_space[OF p_loop])
  have "i2 (loop_class (U \<inter> V) x0 p) = loop_class V x0 (loop_image id p)"
  proof (rule fundamental_group_map_eqI)
    show "loop_class (U \<inter> V) x0 p \<in> fundamental_group_space (U \<inter> V) x0"
      by (rule A_in)
    show "p \<in> loop_space (U \<inter> V) x0"
      by (rule p_loop)
    show "loop_class (U \<inter> V) x0 p = loop_class (U \<inter> V) x0 p"
      by simp
    show "continuous_on (U \<inter> V) id"
      by simp
    show "id \<in> (U \<inter> V) \<rightarrow> V"
      by auto
    show "id x0 = x0"
      by simp
  qed
  then show ?thesis
    by (simp add: loop_image_def)
qed

lemma j1_segment_loop_eq:
  assumes segU: "segment_loop p t u \<in> loop_space U x0"
  shows "j1 (loop_class U x0 (segment_loop p t u)) =
    loop_class W x0 (segment_loop p t u)"
proof -
  have A_in: "loop_class U x0 (segment_loop p t u) \<in> fundamental_group_space U x0"
    by (rule loop_class_in_space[OF segU])
  have "j1 (loop_class U x0 (segment_loop p t u)) =
      loop_class W x0 (loop_image id (segment_loop p t u))"
  proof (rule fundamental_group_map_eqI)
    show "loop_class U x0 (segment_loop p t u) \<in> fundamental_group_space U x0"
      by (rule A_in)
    show "segment_loop p t u \<in> loop_space U x0"
      by (rule segU)
    show "loop_class U x0 (segment_loop p t u) =
        loop_class U x0 (segment_loop p t u)"
      by simp
    show "continuous_on U id"
      by simp
    show "id \<in> U \<rightarrow> W"
      by auto
    show "id x0 = x0"
      by simp
  qed
  then show ?thesis
    by (simp add: loop_image_def)
qed

lemma j2_segment_loop_eq:
  assumes segV: "segment_loop p t u \<in> loop_space V x0"
  shows "j2 (loop_class V x0 (segment_loop p t u)) =
    loop_class W x0 (segment_loop p t u)"
proof -
  have A_in: "loop_class V x0 (segment_loop p t u) \<in> fundamental_group_space V x0"
    by (rule loop_class_in_space[OF segV])
  have "j2 (loop_class V x0 (segment_loop p t u)) =
      loop_class W x0 (loop_image id (segment_loop p t u))"
  proof (rule fundamental_group_map_eqI)
    show "loop_class V x0 (segment_loop p t u) \<in> fundamental_group_space V x0"
      by (rule A_in)
    show "segment_loop p t u \<in> loop_space V x0"
      by (rule segV)
    show "loop_class V x0 (segment_loop p t u) =
        loop_class V x0 (segment_loop p t u)"
      by simp
    show "continuous_on V id"
      by simp
    show "id \<in> V \<rightarrow> W"
      by auto
    show "id x0 = x0"
      by simp
  qed
  then show ?thesis
    by (simp add: loop_image_def)
qed

lemma svk_partition_eval_partition_word:
  assumes p_loop: "p \<in> loop_space W x0"
    and part: "svk_partition p ts bs"
  shows "svk_word_eval (partition_word p ts bs) =
    loop_class W x0 (partition_loop p ts)"
  using part
proof (induction ts arbitrary: bs)
  case Nil
  then show ?case
    by (simp add: fundamental_group_one_def)
next
  case (Cons t ts)
  from p_loop have p_path: "path p" and p_image: "path_image p \<subseteq> W"
    unfolding loop_space_def by auto
  show ?case
  proof (cases ts)
    case ts_nil: Nil
    then show ?thesis
    proof (cases bs)
      case bs_nil: Nil
      have pw: "partition_word p (t # ts) bs = WordNil"
        using ts_nil bs_nil by simp
      have pl: "partition_loop p (t # ts) = (\<lambda>_. x0)"
        using ts_nil by simp
      have eval_nil0: "svk_word_eval WordNil = oneW"
        by (rule decode.carrier_full_amalg_eval.simps(1))
      have eval_nil: "svk_word_eval WordNil = loop_class W x0 (\<lambda>_. x0)"
        using eval_nil0 by (simp add: fundamental_group_one_def)
      have "svk_word_eval (partition_word p (t # ts) bs) = svk_word_eval WordNil"
        using pw by simp
      also have "... = loop_class W x0 (\<lambda>_. x0)"
        by (rule eval_nil)
      also have "... = loop_class W x0 (partition_loop p (t # ts))"
        using pl by simp
      finally show ?thesis
        .
    next
      case bs_cons: (Cons b bs')
      then show ?thesis
        using Cons.prems ts_nil by simp
    qed
  next
    case (Cons u us)
    then obtain b bs' where bs: "bs = b # bs'"
      using Cons.prems by (cases bs) auto
    have tail: "svk_partition p (u # us) bs'"
      using Cons.prems Cons bs by simp
    have tail_ts: "svk_partition p ts bs'"
      using Cons tail by simp
    have tail_eval_ts:
      "svk_word_eval (partition_word p ts bs') =
        loop_class W x0 (partition_loop p ts)"
      by (rule Cons.IH[OF tail_ts])
    have tail_eval:
      "svk_word_eval (partition_word p (u # us) bs') =
        loop_class W x0 (partition_loop p (u # us))"
      using Cons tail_eval_ts by simp
    have tail_loop: "partition_loop p (u # us) \<in> loop_space W x0"
      by (rule svk_partition_partition_loop_in_W[OF p_loop tail])
    have t01: "t \<in> {0..1}" and ptUV: "p t \<in> U \<inter> V"
      using Cons.prems Cons bs by simp_all
    have u01: "u \<in> {0..1}" and puUV: "p u \<in> U \<inter> V"
      using Cons.prems Cons bs svk_partition_next_in_intersection[of p t u us b bs'] by simp_all
    have seg_side:
      "(if b then subpathin t u p ` {0..1} \<subseteq> U else subpathin t u p ` {0..1} \<subseteq> V)"
      using Cons.prems Cons bs by simp
    have segW:
      "segment_loop p t u \<in> loop_space W x0"
    proof (rule segment_loop_in_W[OF p_path p_image t01 u01 ptUV puUV])
      have sub_imgW: "path_image (subpathin t u p) \<subseteq> W"
        using p_image path_image_subpathin_subset[OF t01 u01, of p] by blast
      show "subpathin t u p ` {0..1} \<subseteq> W"
        using sub_imgW by (simp add: path_image_def)
    qed
    have segW_in: "loop_class W x0 (segment_loop p t u) \<in> fundamental_group_space W x0"
      by (rule loop_class_in_space[OF segW])
    have tail_in: "loop_class W x0 (partition_loop p (u # us)) \<in> fundamental_group_space W x0"
      by (rule loop_class_in_space[OF tail_loop])
    have mult_eq:
      "multW (loop_class W x0 (segment_loop p t u))
          (loop_class W x0 (partition_loop p (u # us))) =
        loop_class W x0 (segment_loop p t u +++ partition_loop p (u # us))"
      by (rule fundamental_group_mult_eqI[OF segW_in tail_in segW tail_loop]) simp_all
    show ?thesis
    proof (cases b)
      case True
      have segU: "segment_loop p t u \<in> loop_space U x0"
        by (rule segment_loop_in_U[OF p_path p_image t01 u01 ptUV puUV]) (use seg_side True in simp)
      have j1_eq:
        "j1 (loop_class U x0 (segment_loop p t u)) =
          loop_class W x0 (segment_loop p t u)"
        by (rule j1_segment_loop_eq[OF segU])
      show ?thesis
      proof -
        have "svk_word_eval (partition_word p (t # ts) (True # bs')) =
            multW (j1 (loop_class U x0 (segment_loop p t u)))
              (svk_word_eval (partition_word p (u # us) bs'))"
          using Cons by simp
        also have "... =
            multW (loop_class W x0 (segment_loop p t u))
              (loop_class W x0 (partition_loop p (u # us)))"
          using j1_eq tail_eval by simp
        also have "... =
            loop_class W x0 (segment_loop p t u +++ partition_loop p (u # us))"
          by (rule mult_eq)
        also have "... = loop_class W x0 (partition_loop p (t # ts))"
          using Cons by simp
        finally have branch_true:
          "svk_word_eval (partition_word p (t # ts) (True # bs')) =
            loop_class W x0 (partition_loop p (t # ts))" .
        have bs_true: "bs = True # bs'"
          using bs True by simp
        show ?thesis
          unfolding bs_true using branch_true .
      qed
    next
      case False
      have segV: "segment_loop p t u \<in> loop_space V x0"
        by (rule segment_loop_in_V[OF p_path p_image t01 u01 ptUV puUV]) (use seg_side False in simp)
      have j2_eq:
        "j2 (loop_class V x0 (segment_loop p t u)) =
          loop_class W x0 (segment_loop p t u)"
        by (rule j2_segment_loop_eq[OF segV])
      show ?thesis
      proof -
        have "svk_word_eval (partition_word p (t # ts) (False # bs')) =
            multW (j2 (loop_class V x0 (segment_loop p t u)))
              (svk_word_eval (partition_word p (u # us) bs'))"
          using Cons by simp
        also have "... =
            multW (loop_class W x0 (segment_loop p t u))
              (loop_class W x0 (partition_loop p (u # us)))"
          using j2_eq tail_eval by simp
        also have "... =
            loop_class W x0 (segment_loop p t u +++ partition_loop p (u # us))"
          by (rule mult_eq)
        also have "... = loop_class W x0 (partition_loop p (t # ts))"
          using Cons by simp
        finally have branch_false:
          "svk_word_eval (partition_word p (t # ts) (False # bs')) =
            loop_class W x0 (partition_loop p (t # ts))" .
        have bs_false: "bs = False # bs'"
          using bs False by simp
        show ?thesis
          unfolding bs_false using branch_false .
      qed
    qed
  qed
qed

lemma valid_partition_eval_partition_word:
  assumes p_loop: "p \<in> loop_space W x0"
    and part: "valid_partition p ts bs"
  shows "svk_word_eval (partition_word p ts bs) =
    loop_class W x0 (partition_loop p ts)"
proof -
  have svk_part: "svk_partition p ts bs"
    using part unfolding valid_partition_def by auto
  show ?thesis
    by (rule svk_partition_eval_partition_word[OF p_loop svk_part])
qed

lemma valid_partition_decode_partition_word:
  assumes p_loop: "p \<in> loop_space W x0"
    and part: "valid_partition p ts bs"
  shows "svk_decode (partition_word p ts bs) =
    loop_class W x0 (partition_loop p ts)"
proof -
  have in_space: "fpw_in_space G1 G2 (partition_word p ts bs)"
    by (rule valid_partition_partition_word_in_space[OF p_loop part])
  show ?thesis
    using valid_partition_eval_partition_word[OF p_loop part]
    by (simp add: svk_decode_eq_eval[OF in_space])
qed

lemma pair_interval_member:
  fixes x y :: "real \<times> real" and x1 x2 y1 y2 u v :: real
  assumes x: "x = (x1, x2)"
    and y: "y = (y1, y2)"
    and mix1: "u *\<^sub>R x1 + v *\<^sub>R y1 \<in> {0..1}"
    and mix2: "u *\<^sub>R x2 + v *\<^sub>R y2 \<in> {0..1}"
  shows "u *\<^sub>R x + v *\<^sub>R y \<in> {0..1} \<times> {0..1}"
proof -
  have pair_form:
    "u *\<^sub>R x + v *\<^sub>R y =
      (u *\<^sub>R x1 + v *\<^sub>R y1, u *\<^sub>R x2 + v *\<^sub>R y2)"
    using x y by simp
  have pair_in_Q:
    "(u *\<^sub>R x1 + v *\<^sub>R y1, u *\<^sub>R x2 + v *\<^sub>R y2) \<in> {0..1} \<times> {0..1}"
    using mix1 mix2 by auto
  from pair_in_Q show ?thesis
    by (subst pair_form) simp
qed

lemma affine_closed_segment_member:
  fixes a b u :: real
  assumes u01: "u \<in> {0..1}"
  shows "(b - a) * u + a \<in> closed_segment a b"
proof -
  have "(b - a) * u + a = linepath a b u"
    by (simp add: linepath_def algebra_simps)
  moreover have "linepath a b u \<in> closed_segment a b"
    using u01 by (rule linepath_in_path)
  ultimately show ?thesis
    by simp
qed

lemma affine_subinterval_member:
  fixes a b u :: real
  assumes ab: "a \<le> b"
    and u01: "u \<in> {0..1}"
  shows "(b - a) * u + a \<in> {a..b}"
proof -
  have "(b - a) * u + a \<in> closed_segment a b"
    by (rule affine_closed_segment_member[OF u01])
  also have "closed_segment a b = {a..b}"
    by (rule closed_segment_eq_real_ivl1[OF ab])
  finally show ?thesis .
qed

lemma affine_unit_interval_member:
  fixes a b u :: real
  assumes a01: "a \<in> {0..1}"
    and b01: "b \<in> {0..1}"
    and ab: "a \<le> b"
    and u01: "u \<in> {0..1}"
  shows "(b - a) * u + a \<in> {0..1}"
proof -
  have "(b - a) * u + a \<in> {a..b}"
    by (rule affine_subinterval_member[OF ab u01])
  moreover have "{a..b} \<subseteq> {0..1}"
    using a01 b01 ab by auto
  ultimately show ?thesis
    by blast
qed

lemma square_edge_homotopic:
  fixes h :: "(real \<times> real) \<Rightarrow> 'a"
  assumes h_cont: "continuous_map (top_of_set ({0..1} \<times> {0..1})) (top_of_set S) h"
  shows "homotopic_paths S
    ((\<lambda>t. h (t, 0)) +++ (\<lambda>t. h (1, t)))
    ((\<lambda>t. h (0, t)) +++ (\<lambda>t. h (t, 1)))"
proof -
  let ?g = "linepath (0::real, 0::real) (1, 0) +++ linepath (1, 0) (1, 1)"
  let ?k = "linepath (0::real, 0::real) (0, 1) +++ linepath (0, 1) (1, 1)"
  have hk:
    "homotopic_paths ({0..1} \<times> {0..1}) ?g ?k"
  proof (rule homotopic_paths_linear)
    show "path ?g" "path ?k"
      by simp_all
    show "pathstart ?k = pathstart ?g" "pathfinish ?k = pathfinish ?g"
      by simp_all
    show "closed_segment (?g t) (?k t) \<subseteq> {0..1} \<times> {0..1}" if "t \<in> {0..1}" for t
    proof (rule closed_segment_subset)
      show "?g t \<in> {0..1} \<times> {0..1}" "?k t \<in> {0..1} \<times> {0..1}"
        using that by (auto simp: joinpaths_def linepath_def)
      show "convex (({0::real..1}) \<times> ({0::real..1}))"
        by (intro convex_Times) auto
    qed
  qed
  from h_cont have h_on: "continuous_on ({0..1} \<times> {0..1}) h"
    and h_into: "h \<in> ({0..1} \<times> {0..1}) \<rightarrow> S"
    by simp_all
  have img:
    "homotopic_paths S (h \<circ> ?g) (h \<circ> ?k)"
    by (rule homotopic_paths_continuous_image[OF hk h_on h_into])
  have g_eq: "h \<circ> ?g = ((\<lambda>t. h (t, 0)) +++ (\<lambda>t. h (1, t)))"
    by (rule ext) (simp add: joinpaths_def linepath_def)
  have k_eq: "h \<circ> ?k = ((\<lambda>t. h (0, t)) +++ (\<lambda>t. h (t, 1)))"
    by (rule ext) (simp add: joinpaths_def linepath_def)
  show ?thesis
    using img unfolding g_eq k_eq .
qed

lemma rectangle_edge_homotopic:
  fixes h :: "(real \<times> real) \<Rightarrow> 'a"
  assumes h_cont: "continuous_map (top_of_set ({0..1} \<times> {0..1})) (top_of_set S) h"
    and a01: "a \<in> {0..1}" and b01: "b \<in> {0..1}"
    and c01: "c \<in> {0..1}" and d01: "d \<in> {0..1}"
    and ab: "a \<le> b" and cd: "c \<le> d"
  shows "homotopic_paths S
    (subpathin a b (\<lambda>t. h (t, c)) +++ (\<lambda>t. h (b, (d - c) * t + c)))
    ((\<lambda>t. h (a, (d - c) * t + c)) +++ subpathin a b (\<lambda>t. h (t, d)))"
proof -
  let ?Q = "{0..1} \<times> {0..1}"
  let ?r = "\<lambda>z::real \<times> real. ((b - a) * fst z + a, (d - c) * snd z + c)"
  have r_on: "continuous_on ?Q ?r"
    by (intro continuous_intros)
  have r_into: "?r \<in> ?Q \<rightarrow> ?Q"
  proof
    fix z :: "real \<times> real"
    assume z_in: "z \<in> ?Q"
    then have z1: "fst z \<in> {0..1}" and z2: "snd z \<in> {0..1}"
      by auto
    have x_in: "(b - a) * fst z + a \<in> {0..1}"
      by (rule affine_unit_interval_member[OF a01 b01 ab z1])
    have y_in: "(d - c) * snd z + c \<in> {0..1}"
      by (rule affine_unit_interval_member[OF c01 d01 cd z2])
    show "?r z \<in> ?Q"
      using x_in y_in by simp
  qed
  from h_cont have h_on: "continuous_on ?Q h" and h_into: "h \<in> ?Q \<rightarrow> S"
    by simp_all
  have hr_on: "continuous_on ?Q (h \<circ> ?r)"
  proof -
    have "continuous_on ?Q (\<lambda>x. h (?r x))"
    proof (rule continuous_on_compose2[OF h_on])
      show "continuous_on ?Q ?r"
        by (rule r_on)
      show "?r ` ?Q \<subseteq> ?Q"
        using r_into by auto
    qed
    then show ?thesis
      by (simp add: comp_def)
  qed
  have hr_into: "(h \<circ> ?r) \<in> ?Q \<rightarrow> S"
  proof
    fix z :: "real \<times> real"
    assume z_in: "z \<in> ?Q"
    obtain x y where z: "z = (x, y)"
      by (cases z)
    have x01: "x \<in> {0..1}" and y01: "y \<in> {0..1}"
      using z_in z by auto
    have rx_in: "(b - a) * x + a \<in> {0..1}"
      by (rule affine_unit_interval_member[OF a01 b01 ab x01])
    have ry_in: "(d - c) * y + c \<in> {0..1}"
      by (rule affine_unit_interval_member[OF c01 d01 cd y01])
    have rz_in: "?r z \<in> ?Q"
      using z rx_in ry_in by simp
    have hz_in: "h (?r z) \<in> S"
      using h_into rz_in by auto
    show "(h \<circ> ?r) z \<in> S"
      using hz_in by (simp add: comp_def)
  qed
  have hr_cont: "continuous_map (top_of_set ?Q) (top_of_set S) (h \<circ> ?r)"
    using hr_on hr_into by simp
  have base:
    "homotopic_paths S
      ((\<lambda>t. (h \<circ> ?r) (t, 0)) +++ (\<lambda>t. (h \<circ> ?r) (1, t)))
      ((\<lambda>t. (h \<circ> ?r) (0, t)) +++ (\<lambda>t. (h \<circ> ?r) (t, 1)))"
    by (rule square_edge_homotopic[OF hr_cont])
  have left_eq:
    "((\<lambda>t. (h \<circ> ?r) (t, 0)) +++ (\<lambda>t. (h \<circ> ?r) (1, t))) =
      (subpathin a b (\<lambda>t. h (t, c)) +++ (\<lambda>t. h (b, (d - c) * t + c)))"
    by (rule ext) (simp add: subpathin_def joinpaths_def)
  have right_eq:
    "((\<lambda>t. (h \<circ> ?r) (0, t)) +++ (\<lambda>t. (h \<circ> ?r) (t, 1))) =
      ((\<lambda>t. h (a, (d - c) * t + c)) +++ subpathin a b (\<lambda>t. h (t, d)))"
    by (rule ext) (simp add: subpathin_def joinpaths_def)
  show ?thesis
  proof (subst left_eq[symmetric], subst right_eq[symmetric])
    show "homotopic_paths S
        (((\<lambda>t. (h \<circ> ?r) (t, 0)) +++ (\<lambda>t. (h \<circ> ?r) (1, t))))
        (((\<lambda>t. (h \<circ> ?r) (0, t)) +++ (\<lambda>t. (h \<circ> ?r) (t, 1))))"
      by (rule base)
  qed
qed

lemma rectangle_edge_homotopic_in_set:
  fixes h :: "(real \<times> real) \<Rightarrow> 'a"
  assumes h_cont: "continuous_map (top_of_set ({0..1} \<times> {0..1})) (top_of_set W) h"
    and a01: "a \<in> {0..1}" and b01: "b \<in> {0..1}"
    and c01: "c \<in> {0..1}" and d01: "d \<in> {0..1}"
    and ab: "a \<le> b" and cd: "c \<le> d"
    and rectS: "h ` ({a..b} \<times> {c..d}) \<subseteq> S"
  shows "homotopic_paths S
    (subpathin a b (\<lambda>t. h (t, c)) +++ (\<lambda>t. h (b, (d - c) * t + c)))
    ((\<lambda>t. h (a, (d - c) * t + c)) +++ subpathin a b (\<lambda>t. h (t, d)))"
proof -
  let ?Q = "{0..1} \<times> {0..1}"
  let ?R = "{a..b} \<times> {c..d}"
  let ?r = "\<lambda>z::real \<times> real. ((b - a) * fst z + a, (d - c) * snd z + c)"
  have r_on: "continuous_on ?Q ?r"
    by (intro continuous_intros)
  have r_into: "?r \<in> ?Q \<rightarrow> ?Q"
  proof
    fix z :: "real \<times> real"
    assume z_in: "z \<in> ?Q"
    then have z1: "fst z \<in> {0..1}" and z2: "snd z \<in> {0..1}"
      by auto
    have x_in: "(b - a) * fst z + a \<in> {0..1}"
      by (rule affine_unit_interval_member[OF a01 b01 ab z1])
    have y_in: "(d - c) * snd z + c \<in> {0..1}"
      by (rule affine_unit_interval_member[OF c01 d01 cd z2])
    show "?r z \<in> ?Q"
      using x_in y_in by simp
  qed
  have r_rect: "?r ` ?Q \<subseteq> ?R"
  proof
    fix x
    assume "x \<in> ?r ` ?Q"
    then obtain z where z_in: "z \<in> ?Q" and x_eq: "x = ?r z"
      by blast
    have x1: "(b - a) * fst z + a \<in> {a..b}"
      by (rule affine_subinterval_member[OF ab]) (use z_in in auto)
    have x2: "(d - c) * snd z + c \<in> {c..d}"
      by (rule affine_subinterval_member[OF cd]) (use z_in in auto)
    show "x \<in> ?R"
      using x1 x2 x_eq by simp
  qed
  from h_cont have h_on: "continuous_on ?Q h"
    and h_intoW: "h \<in> ?Q \<rightarrow> W"
    by simp_all
  have hr_on: "continuous_on ?Q (h \<circ> ?r)"
  proof -
    have "continuous_on ?Q (\<lambda>x. h (?r x))"
    proof (rule continuous_on_compose2[OF h_on])
      show "continuous_on ?Q ?r"
        by (rule r_on)
      show "?r ` ?Q \<subseteq> ?Q"
        using r_into by auto
    qed
    then show ?thesis
      by (simp add: comp_def)
  qed
  have hr_into: "(h \<circ> ?r) \<in> ?Q \<rightarrow> S"
  proof
    fix z :: "real \<times> real"
    assume z_in: "z \<in> ?Q"
    then have rz_in: "?r z \<in> ?R"
    proof -
      have "?r z \<in> ?r ` ?Q"
        using z_in by blast
      then show ?thesis
        using r_rect by blast
    qed
    show "(h \<circ> ?r) z \<in> S"
      using rectS rz_in by auto
  qed
  have hr_cont: "continuous_map (top_of_set ?Q) (top_of_set S) (h \<circ> ?r)"
    using hr_on hr_into by simp
  have base:
    "homotopic_paths S
      ((\<lambda>t. (h \<circ> ?r) (t, 0)) +++ (\<lambda>t. (h \<circ> ?r) (1, t)))
      ((\<lambda>t. (h \<circ> ?r) (0, t)) +++ (\<lambda>t. (h \<circ> ?r) (t, 1)))"
    by (rule square_edge_homotopic[OF hr_cont])
  have left_eq:
    "((\<lambda>t. (h \<circ> ?r) (t, 0)) +++ (\<lambda>t. (h \<circ> ?r) (1, t))) =
      (subpathin a b (\<lambda>t. h (t, c)) +++ (\<lambda>t. h (b, (d - c) * t + c)))"
    by (rule ext) (simp add: subpathin_def joinpaths_def)
  have right_eq:
    "((\<lambda>t. (h \<circ> ?r) (0, t)) +++ (\<lambda>t. (h \<circ> ?r) (t, 1))) =
      ((\<lambda>t. h (a, (d - c) * t + c)) +++ subpathin a b (\<lambda>t. h (t, d)))"
    by (rule ext) (simp add: subpathin_def joinpaths_def)
  show ?thesis
    using base unfolding left_eq right_eq .
qed

definition vertical_strip_path ::
  "((real \<times> real) \<Rightarrow> 'a) \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> 'a"
where
  "vertical_strip_path h t c d = (\<lambda>u. h (t, (d - c) * u + c))"

definition bridge_loop ::
  "((real \<times> real) \<Rightarrow> 'a) \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> 'a"
where
  "bridge_loop h t c d =
    (connector (h (t, c)) +++ vertical_strip_path h t c d) +++
      reversepath (connector (h (t, d)))"

lemma bridge_loop_eq_segment_loop [simp]:
  "bridge_loop h t c d = segment_loop (vertical_strip_path h t c d) 0 1"
  unfolding bridge_loop_def vertical_strip_path_def segment_loop_def subpathin_def
  by (rule ext) simp

lemma vertical_strip_path_image_subset:
  assumes cd: "c \<le> d"
  shows "vertical_strip_path h t c d ` {0..1} \<subseteq> h ` ({t} \<times> {c..d})"
proof
  fix x
  assume x_in: "x \<in> vertical_strip_path h t c d ` {0..1}"
  then obtain u where u01: "u \<in> {0..1}" and x_eq: "x = vertical_strip_path h t c d u"
    by blast
  have yc: "(d - c) * u + c \<in> {c..d}"
    by (rule affine_subinterval_member[OF cd u01])
  show "x \<in> h ` ({t} \<times> {c..d})"
    using yc x_eq unfolding vertical_strip_path_def by auto
qed

lemma rectangle_segment_loop_bridge_homotopic:
  fixes h :: "(real \<times> real) \<Rightarrow> 'a"
  assumes h_cont: "continuous_map (top_of_set ({0..1} \<times> {0..1})) (top_of_set W) h"
    and a01: "a \<in> {0..1}" and b01: "b \<in> {0..1}"
    and c01: "c \<in> {0..1}" and d01: "d \<in> {0..1}"
    and ab: "a \<le> b" and cd: "c \<le> d"
    and rectS: "h ` ({a..b} \<times> {c..d}) \<subseteq> S"
    and leftUV: "h ` ({a} \<times> {c..d}) \<subseteq> U \<inter> V"
    and rightUV: "h ` ({b} \<times> {c..d}) \<subseteq> U \<inter> V"
    and UVS: "U \<inter> V \<subseteq> S"
  shows "homotopic_paths S
    (segment_loop (\<lambda>t. h (t, c)) a b +++ bridge_loop h b c d)
    (bridge_loop h a c d +++ segment_loop (\<lambda>t. h (t, d)) a b)"
proof -
  let ?pc = "\<lambda>t. h (t, c)"
  let ?pd = "\<lambda>t. h (t, d)"
  let ?la = "vertical_strip_path h a c d"
  let ?lb = "vertical_strip_path h b c d"
  let ?ac = "connector (h (a, c))"
  let ?ad = "connector (h (a, d))"
  let ?bc = "connector (h (b, c))"
  let ?bd = "connector (h (b, d))"
  let ?bot = "subpathin a b ?pc"
  let ?top = "subpathin a b ?pd"
  have h_on: "continuous_on ({0..1} \<times> {0..1}) h"
    and h_intoW: "h \<in> ({0..1} \<times> {0..1}) \<rightarrow> W"
    using h_cont by simp_all
  have x0S: "x0 \<in> S"
    using x0_in_UV UVS by blast

  have acUV: "h (a, c) \<in> U \<inter> V"
    using leftUV cd by auto
  have adUV: "h (a, d) \<in> U \<inter> V"
    using leftUV cd by auto
  have bcUV: "h (b, c) \<in> U \<inter> V"
    using rightUV cd by auto
  have bdUV: "h (b, d) \<in> U \<inter> V"
    using rightUV cd by auto

  have pc_path: "path ?pc"
  proof -
    have "continuous_on {0..1} ?pc"
    proof (rule continuous_on_compose2[OF h_on])
      show "continuous_on {0..1} (\<lambda>t. (t, c))"
        by (intro continuous_intros)
      show "(\<lambda>t. (t, c)) ` {0..1} \<subseteq> {0..1} \<times> {0..1}"
        using c01 by auto
    qed
    then show ?thesis
      by (simp add: path_def)
  qed
  have pd_path: "path ?pd"
  proof -
    have "continuous_on {0..1} ?pd"
    proof (rule continuous_on_compose2[OF h_on])
      show "continuous_on {0..1} (\<lambda>t. (t, d))"
        by (intro continuous_intros)
      show "(\<lambda>t. (t, d)) ` {0..1} \<subseteq> {0..1} \<times> {0..1}"
        using d01 by auto
    qed
    then show ?thesis
      by (simp add: path_def)
  qed
  have la_path: "path ?la"
  proof -
    have "continuous_on {0..1} ?la"
    proof -
      have "continuous_on {0..1} (\<lambda>u. h (a, (d - c) * u + c))"
      proof (rule continuous_on_compose2[OF h_on])
        show "continuous_on {0..1} (\<lambda>u. (a, (d - c) * u + c))"
          by (intro continuous_intros)
        show "(\<lambda>u. (a, (d - c) * u + c)) ` {0..1} \<subseteq> {0..1} \<times> {0..1}"
        proof
          fix x
          assume "x \<in> (\<lambda>u. (a, (d - c) * u + c)) ` {0..1}"
          then obtain u where u01: "u \<in> {0..1}" and x_eq: "x = (a, (d - c) * u + c)"
            by blast
          have y_in: "(d - c) * u + c \<in> {0..1}"
            by (rule affine_unit_interval_member[OF c01 d01 cd u01])
          show "x \<in> {0..1} \<times> {0..1}"
            using a01 y_in x_eq by auto
        qed
      qed
      then show ?thesis
        by (simp add: vertical_strip_path_def)
    qed
    then show ?thesis
      by (simp add: vertical_strip_path_def path_def)
  qed
  have lb_path: "path ?lb"
  proof -
    have "continuous_on {0..1} ?lb"
    proof -
      have "continuous_on {0..1} (\<lambda>u. h (b, (d - c) * u + c))"
      proof (rule continuous_on_compose2[OF h_on])
        show "continuous_on {0..1} (\<lambda>u. (b, (d - c) * u + c))"
          by (intro continuous_intros)
        show "(\<lambda>u. (b, (d - c) * u + c)) ` {0..1} \<subseteq> {0..1} \<times> {0..1}"
        proof
          fix x
          assume "x \<in> (\<lambda>u. (b, (d - c) * u + c)) ` {0..1}"
          then obtain u where u01: "u \<in> {0..1}" and x_eq: "x = (b, (d - c) * u + c)"
            by blast
          have y_in: "(d - c) * u + c \<in> {0..1}"
            by (rule affine_unit_interval_member[OF c01 d01 cd u01])
          show "x \<in> {0..1} \<times> {0..1}"
            using b01 y_in x_eq by auto
        qed
      qed
      then show ?thesis
        by (simp add: vertical_strip_path_def)
    qed
    then show ?thesis
      by (simp add: vertical_strip_path_def path_def)
  qed

  have pc_imgW: "path_image ?pc \<subseteq> W"
    using h_intoW c01 by (auto simp: path_image_def)
  have pd_imgW: "path_image ?pd \<subseteq> W"
    using h_intoW d01 by (auto simp: path_image_def)
  have bot_imgS: "?bot ` {0..1} \<subseteq> S"
    using rectS ab cd by (auto simp: subpathin_image_eq)
  have top_imgS: "?top ` {0..1} \<subseteq> S"
    using rectS ab cd by (auto simp: subpathin_image_eq)
  have la_imgS: "path_image ?la \<subseteq> S"
  proof -
    have vs_subset: "vertical_strip_path h a c d ` {0..1} \<subseteq> h ` ({a} \<times> {c..d})"
      by (rule vertical_strip_path_image_subset[OF cd])
    have "path_image ?la \<subseteq> U \<inter> V"
      using vs_subset leftUV by (auto simp: path_image_def)
    then show ?thesis
      using UVS by blast
  qed
  have lb_imgS: "path_image ?lb \<subseteq> S"
  proof -
    have vs_subset: "vertical_strip_path h b c d ` {0..1} \<subseteq> h ` ({b} \<times> {c..d})"
      by (rule vertical_strip_path_image_subset[OF cd])
    have "path_image ?lb \<subseteq> U \<inter> V"
      using vs_subset rightUV by (auto simp: path_image_def)
    then show ?thesis
      using UVS by blast
  qed
  have la_imgUV: "path_image ?la \<subseteq> U \<inter> V"
  proof -
    have vs_subset: "vertical_strip_path h a c d ` {0..1} \<subseteq> h ` ({a} \<times> {c..d})"
      by (rule vertical_strip_path_image_subset[OF cd])
    show ?thesis
      using vs_subset leftUV by (auto simp: path_image_def)
  qed
  have lb_imgUV: "path_image ?lb \<subseteq> U \<inter> V"
  proof -
    have vs_subset: "vertical_strip_path h b c d ` {0..1} \<subseteq> h ` ({b} \<times> {c..d})"
      by (rule vertical_strip_path_image_subset[OF cd])
    show ?thesis
      using vs_subset rightUV by (auto simp: path_image_def)
  qed

  have ac_path: "path ?ac" and ac_imgS: "path_image ?ac \<subseteq> S"
    using connector_path[OF acUV] connector_image_subset[OF acUV] UVS by blast+
  have ad_path: "path ?ad" and ad_imgS: "path_image ?ad \<subseteq> S"
    using connector_path[OF adUV] connector_image_subset[OF adUV] UVS by blast+
  have bc_path: "path ?bc" and bc_imgS: "path_image ?bc \<subseteq> S"
    using connector_path[OF bcUV] connector_image_subset[OF bcUV] UVS by blast+
  have bd_path: "path ?bd" and bd_imgS: "path_image ?bd \<subseteq> S"
    using connector_path[OF bdUV] connector_image_subset[OF bdUV] UVS by blast+

  have segc_loop: "segment_loop ?pc a b \<in> loop_space S x0"
  proof (rule segment_loop_in_set[where S = S])
    show "path ?pc"
      by (rule pc_path)
    show "path_image ?pc \<subseteq> W"
      by (rule pc_imgW)
    show "a \<in> {0..1}" "b \<in> {0..1}"
      by (rule a01, rule b01)
    show "?pc a \<in> U \<inter> V" "?pc b \<in> U \<inter> V"
      using acUV bcUV by simp_all
    show "path_image (connector (?pc a)) \<subseteq> S"
      using connector_image_subset[OF acUV] UVS by blast
    show "path_image (connector (?pc b)) \<subseteq> S"
      using connector_image_subset[OF bcUV] UVS by blast
    show "?bot ` {0..1} \<subseteq> S"
      by (rule bot_imgS)
    show "x0 \<in> S"
      by (rule x0S)
  qed
  have segd_loop: "segment_loop ?pd a b \<in> loop_space S x0"
  proof (rule segment_loop_in_set[where S = S])
    show "path ?pd"
      by (rule pd_path)
    show "path_image ?pd \<subseteq> W"
      by (rule pd_imgW)
    show "a \<in> {0..1}" "b \<in> {0..1}"
      by (rule a01, rule b01)
    show "?pd a \<in> U \<inter> V" "?pd b \<in> U \<inter> V"
      using adUV bdUV by simp_all
    show "path_image (connector (?pd a)) \<subseteq> S"
      using connector_image_subset[OF adUV] UVS by blast
    show "path_image (connector (?pd b)) \<subseteq> S"
      using connector_image_subset[OF bdUV] UVS by blast
    show "?top ` {0..1} \<subseteq> S"
      by (rule top_imgS)
    show "x0 \<in> S"
      by (rule x0S)
  qed
  have bridge_a_loop: "bridge_loop h a c d \<in> loop_space S x0"
  unfolding bridge_loop_eq_segment_loop
  proof (rule segment_loop_in_set[where S = S])
    show "path ?la"
      by (rule la_path)
    show "path_image ?la \<subseteq> W"
      using la_imgUV by blast
    show "(0::real) \<in> {0..1}"
      by simp
    show "(1::real) \<in> {0..1}"
      by simp
    show "?la 0 \<in> U \<inter> V" "?la 1 \<in> U \<inter> V"
      using acUV adUV by (simp_all add: vertical_strip_path_def)
    show "path_image (connector (?la 0)) \<subseteq> S"
      using connector_image_subset[OF acUV] UVS by (simp add: vertical_strip_path_def; blast)
    show "path_image (connector (?la 1)) \<subseteq> S"
      using connector_image_subset[OF adUV] UVS by (simp add: vertical_strip_path_def; blast)
    have edge_S: "h ` ({a} \<times> {c..d}) \<subseteq> S"
      by (rule order_trans[OF leftUV UVS])
    have la_imgS': "vertical_strip_path h a c d ` {0..1} \<subseteq> S"
      by (rule order_trans[OF vertical_strip_path_image_subset[OF cd] edge_S])
    have la_eq: "?la = vertical_strip_path h a c d"
      by simp
    show "subpathin 0 1 ?la ` {0..1} \<subseteq> S"
      using la_imgS' by simp
    show "x0 \<in> S"
      by (rule x0S)
  qed
  have bridge_b_loop: "bridge_loop h b c d \<in> loop_space S x0"
  unfolding bridge_loop_eq_segment_loop
  proof (rule segment_loop_in_set[where S = S])
    show "path ?lb"
      by (rule lb_path)
    show "path_image ?lb \<subseteq> W"
      using lb_imgUV by blast
    show "(0::real) \<in> {0..1}"
      by simp
    show "(1::real) \<in> {0..1}"
      by simp
    show "?lb 0 \<in> U \<inter> V" "?lb 1 \<in> U \<inter> V"
      using bcUV bdUV by (simp_all add: vertical_strip_path_def)
    show "path_image (connector (?lb 0)) \<subseteq> S"
      using connector_image_subset[OF bcUV] UVS by (simp add: vertical_strip_path_def; blast)
    show "path_image (connector (?lb 1)) \<subseteq> S"
      using connector_image_subset[OF bdUV] UVS by (simp add: vertical_strip_path_def; blast)
    have edge_S: "h ` ({b} \<times> {c..d}) \<subseteq> S"
      by (rule order_trans[OF rightUV UVS])
    have lb_imgS': "vertical_strip_path h b c d ` {0..1} \<subseteq> S"
      by (rule order_trans[OF vertical_strip_path_image_subset[OF cd] edge_S])
    have lb_eq: "?lb = vertical_strip_path h b c d"
      by simp
    show "subpathin 0 1 ?lb ` {0..1} \<subseteq> S"
      using lb_imgS' by simp
    show "x0 \<in> S"
      by (rule x0S)
  qed

  have segc_path: "path (segment_loop ?pc a b)" and segc_imgS: "path_image (segment_loop ?pc a b) \<subseteq> S"
    using segc_loop unfolding loop_space_def by auto
  have segd_path: "path (segment_loop ?pd a b)" and segd_imgS: "path_image (segment_loop ?pd a b) \<subseteq> S"
    using segd_loop unfolding loop_space_def by auto
  have bridge_a_path: "path (bridge_loop h a c d)" and bridge_a_imgS: "path_image (bridge_loop h a c d) \<subseteq> S"
    using bridge_a_loop unfolding loop_space_def by auto
  have bridge_b_path: "path (bridge_loop h b c d)" and bridge_b_imgS: "path_image (bridge_loop h b c d) \<subseteq> S"
    using bridge_b_loop unfolding loop_space_def by auto
  have segc_finish: "pathfinish (segment_loop ?pc a b) = x0"
    using segc_loop unfolding loop_space_def by auto
  have bridge_b_start: "pathstart (bridge_loop h b c d) = x0"
    using bridge_b_loop unfolding loop_space_def by auto
  have bc_start: "pathstart ?bc = x0"
    using connector_start[OF bcUV] by simp
  have bc_finish: "pathfinish ?bc = h (b, c)"
    using connector_finish[OF bcUV] by simp

  have edge_hom:
    "homotopic_paths S (?bot +++ ?lb) (?la +++ ?top)"
    unfolding vertical_strip_path_def
    by (rule rectangle_edge_homotopic_in_set[OF h_cont a01 b01 c01 d01 ab cd rectS])

  have lb_finish: "pathfinish ?lb = h (b, d)"
    using cd by (simp add: vertical_strip_path_def pathfinish_def)
  have lb_start: "pathstart ?lb = h (b, c)"
    by (simp add: vertical_strip_path_def pathstart_def)
  have rev_bd_path: "path (reversepath ?bd)"
    using bd_path by simp
  have rev_bd_imgS: "path_image (reversepath ?bd) \<subseteq> S"
    using bd_imgS by simp
  have rev_bd_start: "pathstart (reversepath ?bd) = h (b, d)"
    using connector_finish[OF bdUV] by simp
  have s_b_path: "path (?lb +++ reversepath ?bd)"
    using lb_path bd_path lb_finish rev_bd_start by simp
  have s_b_imgS: "path_image (?lb +++ reversepath ?bd) \<subseteq> S"
    by (rule subset_path_image_join[OF lb_imgS]) (use bd_imgS in simp)
  have ac_finish: "pathfinish ?ac = h (a, c)"
    using connector_finish[OF acUV] by simp
  have bot_start: "pathstart ?bot = h (a, c)"
    by (simp add: pathstart_def subpathin_def)
  have pc_pathin: "pathin (top_of_set W) ?pc"
    by (rule path_top_of_setI[OF pc_path pc_imgW])
  have bot_path: "path ?bot"
  proof -
    have "pathin (top_of_set W) ?bot"
      by (rule pathin_subpathin[OF pc_pathin]) (use a01 b01 in auto)
    then show ?thesis
      by (simp add: pathin_canon_iff)
  qed
  have r_b_path: "path (?ac +++ ?bot)"
    using ac_path bot_path ac_finish bot_start by simp
  have bot_finish: "pathfinish ?bot = h (b, c)"
    by (simp add: pathfinish_def subpathin_def)
  have r_b_finish: "pathfinish (?ac +++ ?bot) = h (b, c)"
    using r_b_path bot_finish by simp
  have bot_path_imgS: "path_image ?bot \<subseteq> S"
    using bot_imgS by (simp add: path_image_def)
  have pd_pathin: "pathin (top_of_set W) ?pd"
    by (rule path_top_of_setI[OF pd_path pd_imgW])
  have r_b_imgS: "path_image (?ac +++ ?bot) \<subseteq> S"
  proof (rule subset_path_image_join[OF ac_imgS])
    show "path_image ?bot \<subseteq> S"
      using bot_imgS by (simp add: path_image_def)
  qed
  have assoc_bridge_b:
    "homotopic_paths S (bridge_loop h b c d) (?bc +++ (?lb +++ reversepath ?bd))"
  proof -
    have bc_lb: "pathfinish ?bc = pathstart ?lb"
      using bc_finish lb_start by simp
    have lb_bd: "pathfinish ?lb = pathstart (reversepath ?bd)"
      using lb_finish rev_bd_start by simp
    have rev_bd_path: "path (reversepath ?bd)"
      using bd_path by simp
    have rev_bd_imgS: "path_image (reversepath ?bd) \<subseteq> S"
      using bd_imgS by simp
    have "homotopic_paths S (?bc +++ (?lb +++ reversepath ?bd)) (((?bc +++ ?lb) +++ reversepath ?bd))"
      by (rule homotopic_paths_assoc[OF bc_path bc_imgS lb_path lb_imgS rev_bd_path rev_bd_imgS bc_lb lb_bd])
    then show ?thesis
      unfolding bridge_loop_def by (rule homotopic_paths_sym)
  qed
  have s_b_start: "pathstart (?lb +++ reversepath ?bd) = h (b, c)"
    using lb_start by simp
  have lhs_step1:
    "homotopic_paths S
      (segment_loop ?pc a b +++ bridge_loop h b c d)
      (segment_loop ?pc a b +++ (?bc +++ (?lb +++ reversepath ?bd)))"
    by (rule homotopic_paths_join_left[OF assoc_bridge_b segc_path segc_imgS]) (use segc_finish bridge_b_start in simp)
  have lhs_step2:
    "homotopic_paths S
      (segment_loop ?pc a b +++ (?bc +++ (?lb +++ reversepath ?bd)))
      (((segment_loop ?pc a b +++ ?bc) +++ (?lb +++ reversepath ?bd)))"
    by (rule homotopic_paths_assoc[OF segc_path segc_imgS bc_path bc_imgS s_b_path s_b_imgS])
       (use segc_finish bc_start bc_finish s_b_start in simp_all)
  have segc_bc_path: "path (segment_loop ?pc a b +++ ?bc)"
    using segc_path bc_path segc_finish bc_start by simp
  have segc_bc_imgS: "path_image (segment_loop ?pc a b +++ ?bc) \<subseteq> S"
    by (rule subset_path_image_join[OF segc_imgS]) (use bc_imgS in simp)
  have lhs_step3:
    "homotopic_paths S
      (((segment_loop ?pc a b +++ ?bc) +++ (?lb +++ reversepath ?bd)))
      ((((?ac +++ ?bot) +++ reversepath ?bc) +++ ?bc) +++ (?lb +++ reversepath ?bd))"
  proof (rule homotopic_paths_eq[OF _ _])
    show "path (((segment_loop ?pc a b +++ ?bc) +++ (?lb +++ reversepath ?bd)))"
      using segc_bc_path s_b_path bc_finish s_b_start by simp
    show "path_image (((segment_loop ?pc a b +++ ?bc) +++ (?lb +++ reversepath ?bd))) \<subseteq> S"
      by (rule subset_path_image_join[OF segc_bc_imgS]) (use s_b_imgS in simp)
    show "((segment_loop ?pc a b +++ ?bc) +++ (?lb +++ reversepath ?bd)) t =
          ((((?ac +++ ?bot) +++ reversepath ?bc) +++ ?bc) +++ (?lb +++ reversepath ?bd)) t"
      if "t \<in> {0..1}" for t
      using that by (simp add: segment_loop_def)
  qed
  have lhs_step4:
    "homotopic_paths S
      ((((?ac +++ ?bot) +++ reversepath ?bc) +++ ?bc) +++ (?lb +++ reversepath ?bd))
      ((?ac +++ ?bot) +++ (?lb +++ reversepath ?bd))"
    by (rule homotopic_paths_cancel_middle_local[OF r_b_path r_b_imgS bc_path bc_imgS s_b_path s_b_imgS])
       (use r_b_finish bc_finish s_b_start in simp_all)
  have assoc_ac_bot_lb:
    "homotopic_paths S (((?ac +++ ?bot) +++ ?lb)) (?ac +++ (?bot +++ ?lb))"
  proof -
    have "homotopic_paths S (?ac +++ (?bot +++ ?lb)) (((?ac +++ ?bot) +++ ?lb))"
      by (rule homotopic_paths_assoc[OF ac_path ac_imgS bot_path bot_path_imgS lb_path lb_imgS])
         (use ac_finish bot_start bot_finish lb_start in simp_all)
    then show ?thesis
      by (rule homotopic_paths_sym)
  qed
  have assoc_r_b_lb:
    "homotopic_paths S
      ((?ac +++ ?bot) +++ (?lb +++ reversepath ?bd))
      ((((?ac +++ ?bot) +++ ?lb) +++ reversepath ?bd))"
    by (rule homotopic_paths_assoc[OF r_b_path r_b_imgS lb_path lb_imgS rev_bd_path rev_bd_imgS])
       (use r_b_finish lb_start lb_finish rev_bd_start in simp_all)
  have assoc_ac_bot_lb_join:
    "homotopic_paths S
      ((((?ac +++ ?bot) +++ ?lb) +++ reversepath ?bd))
      ((?ac +++ (?bot +++ ?lb)) +++ reversepath ?bd)"
    by (rule homotopic_paths_join_right[OF assoc_ac_bot_lb rev_bd_path rev_bd_imgS])
       (use lb_finish rev_bd_start in simp_all)
  have lhs_step5:
    "homotopic_paths S
      ((?ac +++ ?bot) +++ (?lb +++ reversepath ?bd))
      ((?ac +++ (?bot +++ ?lb)) +++ reversepath ?bd)"
    by (rule homotopic_paths_trans[OF assoc_r_b_lb assoc_ac_bot_lb_join])
  have lhs_to_boundary:
    "homotopic_paths S
      (segment_loop ?pc a b +++ bridge_loop h b c d)
      ((?ac +++ (?bot +++ ?lb)) +++ reversepath ?bd)"
    by (rule homotopic_paths_trans[OF lhs_step1])
       (rule homotopic_paths_trans[OF lhs_step2],
        rule homotopic_paths_trans[OF lhs_step3],
        rule homotopic_paths_trans[OF lhs_step4 lhs_step5])

  have top_path: "path ?top"
  proof -
    have "pathin (top_of_set W) ?top"
      by (rule pathin_subpathin[OF pd_pathin]) (use a01 b01 in auto)
    then show ?thesis
      by (simp add: pathin_canon_iff)
  qed
  have top_start: "pathstart ?top = h (a, d)"
    by (simp add: pathstart_def subpathin_def)
  have top_finish: "pathfinish ?top = h (b, d)"
    by (simp add: pathfinish_def subpathin_def)
  have top_path_imgS: "path_image ?top \<subseteq> S"
    using top_imgS by (simp add: path_image_def)
  have s_a_path: "path (?top +++ reversepath ?bd)"
    using top_path bd_path top_finish rev_bd_start by simp
  have s_a_imgS: "path_image (?top +++ reversepath ?bd) \<subseteq> S"
    by (rule subset_path_image_join[OF top_path_imgS rev_bd_imgS])
  have la_start: "pathstart ?la = h (a, c)"
    by (simp add: vertical_strip_path_def pathstart_def)
  have la_finish: "pathfinish ?la = h (a, d)"
    by (simp add: vertical_strip_path_def pathfinish_def)
  have ad_start: "pathstart ?ad = x0"
    using connector_start[OF adUV] by simp
  have ad_finish: "pathfinish ?ad = h (a, d)"
    using connector_finish[OF adUV] by simp
  have rev_ad_path: "path (reversepath ?ad)"
    using ad_path by simp
  have rev_ad_imgS: "path_image (reversepath ?ad) \<subseteq> S"
    using ad_imgS by simp
  have rev_ad_start: "pathstart (reversepath ?ad) = h (a, d)"
    using connector_finish[OF adUV] by simp
  have rev_ad_finish: "pathfinish (reversepath ?ad) = x0"
    using ad_start by simp
  have r_a_path: "path (?ac +++ ?la)"
    using ac_path la_path ac_finish la_start by simp
  have r_a_imgS: "path_image (?ac +++ ?la) \<subseteq> S"
    by (rule subset_path_image_join[OF ac_imgS la_imgS])
  have r_a_rev_path: "path ((?ac +++ ?la) +++ reversepath ?ad)"
    using r_a_path rev_ad_path la_finish rev_ad_start by simp
  have r_a_rev_imgS: "path_image ((?ac +++ ?la) +++ reversepath ?ad) \<subseteq> S"
    by (rule subset_path_image_join[OF r_a_imgS rev_ad_imgS])
  have assoc_bridge_a:
    "homotopic_paths S (bridge_loop h a c d) (?ac +++ (?la +++ reversepath ?ad))"
  proof -
    have "homotopic_paths S (?ac +++ (?la +++ reversepath ?ad)) (((?ac +++ ?la) +++ reversepath ?ad))"
      by (rule homotopic_paths_assoc[OF ac_path ac_imgS la_path la_imgS rev_ad_path rev_ad_imgS])
         (use ac_finish la_start la_finish rev_ad_start in simp_all)
    then show ?thesis
      unfolding bridge_loop_def by (rule homotopic_paths_sym)
  qed
  have bridge_a_finish: "pathfinish (bridge_loop h a c d) = x0"
    using bridge_a_loop unfolding loop_space_def by auto
  have segd_start: "pathstart (segment_loop ?pd a b) = x0"
    using segd_loop unfolding loop_space_def by auto
  have rhs_step1:
    "homotopic_paths S
      (bridge_loop h a c d +++ segment_loop ?pd a b)
      ((?ac +++ (?la +++ reversepath ?ad)) +++ segment_loop ?pd a b)"
    by (rule homotopic_paths_join_right[OF assoc_bridge_a segd_path segd_imgS])
       (use bridge_a_finish segd_start in simp_all)
  have rhs_step2:
    "homotopic_paths S
      ((?ac +++ (?la +++ reversepath ?ad)) +++ segment_loop ?pd a b)
      (((?ac +++ ?la) +++ reversepath ?ad) +++ segment_loop ?pd a b)"
    by (rule homotopic_paths_join_right[
          OF homotopic_paths_assoc[OF ac_path ac_imgS la_path la_imgS rev_ad_path rev_ad_imgS] segd_path segd_imgS])
       (use ac_finish la_start la_finish rev_ad_start ad_start bridge_a_finish segd_start in simp_all)
  have rhs_step3:
    "homotopic_paths S
      (((?ac +++ ?la) +++ reversepath ?ad) +++ segment_loop ?pd a b)
      ((((?ac +++ ?la) +++ reversepath ?ad) +++ ?ad) +++ (?top +++ reversepath ?bd))"
  proof -
    have segd_assoc:
      "homotopic_paths S (segment_loop ?pd a b) (?ad +++ (?top +++ reversepath ?bd))"
    proof -
      have "homotopic_paths S (?ad +++ (?top +++ reversepath ?bd)) (segment_loop ?pd a b)"
        unfolding segment_loop_def
        by (rule homotopic_paths_assoc[OF ad_path ad_imgS top_path top_path_imgS rev_bd_path rev_bd_imgS])
           (use ad_finish top_start top_finish rev_bd_start in simp_all)
      then show ?thesis
        by (rule homotopic_paths_sym)
    qed
    have step1:
      "homotopic_paths S
        (((?ac +++ ?la) +++ reversepath ?ad) +++ segment_loop ?pd a b)
        (((?ac +++ ?la) +++ reversepath ?ad) +++ (?ad +++ (?top +++ reversepath ?bd)))"
      by (rule homotopic_paths_join_left[OF segd_assoc r_a_rev_path r_a_rev_imgS])
         (use segd_start ad_start rev_ad_finish in simp_all)
    have step2:
      "homotopic_paths S
        (((?ac +++ ?la) +++ reversepath ?ad) +++ (?ad +++ (?top +++ reversepath ?bd)))
        ((((?ac +++ ?la) +++ reversepath ?ad) +++ ?ad) +++ (?top +++ reversepath ?bd))"
      by (rule homotopic_paths_assoc[OF r_a_rev_path r_a_rev_imgS ad_path ad_imgS s_a_path s_a_imgS])
         (use rev_ad_finish ad_start ad_finish top_start in simp_all)
    show ?thesis
      by (rule homotopic_paths_trans[OF step1 step2])
  qed
  have rhs_step4:
    "homotopic_paths S
      ((((?ac +++ ?la) +++ reversepath ?ad) +++ ?ad) +++ (?top +++ reversepath ?bd))
      ((?ac +++ ?la) +++ (?top +++ reversepath ?bd))"
    by (rule homotopic_paths_cancel_middle_local[OF r_a_path r_a_imgS ad_path ad_imgS s_a_path s_a_imgS])
       (use la_finish ad_finish top_start in simp_all)
  have rhs_step5:
    "homotopic_paths S
      ((?ac +++ ?la) +++ (?top +++ reversepath ?bd))
      ((?ac +++ (?la +++ ?top)) +++ reversepath ?bd)"
  proof -
    have step5a:
      "homotopic_paths S
        ((?ac +++ ?la) +++ (?top +++ reversepath ?bd))
        (((?ac +++ ?la) +++ ?top) +++ reversepath ?bd)"
      by (rule homotopic_paths_assoc[OF r_a_path r_a_imgS top_path top_path_imgS rev_bd_path rev_bd_imgS])
         (use la_finish top_start top_finish rev_bd_start in simp_all)
    have inner:
      "homotopic_paths S
        (((?ac +++ ?la) +++ ?top))
        (?ac +++ (?la +++ ?top))"
    proof -
      have "homotopic_paths S
          (?ac +++ (?la +++ ?top))
          (((?ac +++ ?la) +++ ?top))"
        by (rule homotopic_paths_assoc[OF ac_path ac_imgS la_path la_imgS top_path top_path_imgS])
           (use ac_finish la_start la_finish top_start in simp_all)
      then show ?thesis
        by (rule homotopic_paths_sym)
    qed
    have step5b:
      "homotopic_paths S
        (((?ac +++ ?la) +++ ?top) +++ reversepath ?bd)
        ((?ac +++ (?la +++ ?top)) +++ reversepath ?bd)"
      by (rule homotopic_paths_join_right[OF inner rev_bd_path rev_bd_imgS])
         (use top_finish rev_bd_start in simp_all)
    show ?thesis
      by (rule homotopic_paths_trans[OF step5a step5b])
  qed
  have boundary_to_rhs:
    "homotopic_paths S
      ((?ac +++ (?la +++ ?top)) +++ reversepath ?bd)
      (bridge_loop h a c d +++ segment_loop ?pd a b)"
  proof -
    have "homotopic_paths S (bridge_loop h a c d +++ segment_loop ?pd a b)
      ((?ac +++ (?la +++ ?top)) +++ reversepath ?bd)"
      by (rule homotopic_paths_trans[OF rhs_step1])
         (rule homotopic_paths_trans[OF rhs_step2],
          rule homotopic_paths_trans[OF rhs_step3],
          rule homotopic_paths_trans[OF rhs_step4 rhs_step5])
    then show ?thesis
      by (rule homotopic_paths_sym)
  qed

  have edge_boundary:
    "homotopic_paths S
      ((?ac +++ (?bot +++ ?lb)) +++ reversepath ?bd)
      ((?ac +++ (?la +++ ?top)) +++ reversepath ?bd)"
  proof -
    have pre:
      "homotopic_paths S (?ac +++ (?bot +++ ?lb)) (?ac +++ (?la +++ ?top))"
      by (rule homotopic_paths_join_left[OF edge_hom ac_path ac_imgS]) (use ac_finish bot_start la_start in simp_all)
    show ?thesis
    proof (rule homotopic_paths_join_right[OF pre rev_bd_path rev_bd_imgS])
      show "pathfinish (?ac +++ (?bot +++ ?lb)) = pathstart (reversepath ?bd)"
        using lb_finish rev_bd_start by simp
    qed
  qed

  show ?thesis
    by (rule homotopic_paths_trans[OF lhs_to_boundary])
       (rule homotopic_paths_trans[OF edge_boundary boundary_to_rhs])
qed

lemma horizontal_rectangle_segment_loop_in_set:
  fixes h :: "(real \<times> real) \<Rightarrow> 'a"
  assumes h_cont: "continuous_map (top_of_set ({0..1} \<times> {0..1})) (top_of_set W) h"
    and a01: "a \<in> {0..1}" and b01: "b \<in> {0..1}" and c01: "c \<in> {0..1}"
    and ab: "a \<le> b"
    and segS: "h ` ({a..b} \<times> {c}) \<subseteq> S"
    and acUV: "h (a, c) \<in> U \<inter> V"
    and bcUV: "h (b, c) \<in> U \<inter> V"
    and UVS: "U \<inter> V \<subseteq> S"
  shows "segment_loop (\<lambda>t. h (t, c)) a b \<in> loop_space S x0"
proof -
  have h_on: "continuous_on ({0..1} \<times> {0..1}) h"
    and h_intoW: "h \<in> ({0..1} \<times> {0..1}) \<rightarrow> W"
    using h_cont by simp_all
  have pc_path: "path (\<lambda>t. h (t, c))"
  proof -
    have "continuous_on {0..1} (\<lambda>t. h (t, c))"
    proof (rule continuous_on_compose2[OF h_on])
      show "continuous_on {0..1} (\<lambda>t. (t, c))"
        by (intro continuous_intros)
      show "(\<lambda>t. (t, c)) ` {0..1} \<subseteq> {0..1} \<times> {0..1}"
        using c01 by auto
    qed
    then show ?thesis
      by (simp add: path_def)
  qed
  have pc_imgW: "path_image (\<lambda>t. h (t, c)) \<subseteq> W"
    using h_intoW c01 by (auto simp: path_image_def)
  have seg_imgS: "subpathin a b (\<lambda>t. h (t, c)) ` {0..1} \<subseteq> S"
    using segS ab by (auto simp: subpathin_image_eq)
  have x0S: "x0 \<in> S"
    using x0_in_UV UVS by blast
  show ?thesis
  proof (rule segment_loop_in_set[where S = S])
    show "path (\<lambda>t. h (t, c))"
      by (rule pc_path)
    show "path_image (\<lambda>t. h (t, c)) \<subseteq> W"
      by (rule pc_imgW)
    show "a \<in> {0..1}" "b \<in> {0..1}"
      by (rule a01, rule b01)
    show "(\<lambda>t. h (t, c)) a \<in> U \<inter> V" "(\<lambda>t. h (t, c)) b \<in> U \<inter> V"
      using acUV bcUV by simp_all
    show "path_image (connector ((\<lambda>t. h (t, c)) a)) \<subseteq> S"
      using connector_image_subset[OF acUV] UVS by blast
    show "path_image (connector ((\<lambda>t. h (t, c)) b)) \<subseteq> S"
      using connector_image_subset[OF bcUV] UVS by blast
    show "subpathin a b (\<lambda>t. h (t, c)) ` {0..1} \<subseteq> S"
      by (rule seg_imgS)
    show "x0 \<in> S"
      by (rule x0S)
  qed
qed

lemma vertical_bridge_loop_in_set:
  fixes h :: "(real \<times> real) \<Rightarrow> 'a"
  assumes h_cont: "continuous_map (top_of_set ({0..1} \<times> {0..1})) (top_of_set W) h"
    and t01: "t \<in> {0..1}" and c01: "c \<in> {0..1}" and d01: "d \<in> {0..1}"
    and cd: "c \<le> d"
    and edgeUV: "h ` ({t} \<times> {c..d}) \<subseteq> U \<inter> V"
    and UVS: "U \<inter> V \<subseteq> S"
  shows "bridge_loop h t c d \<in> loop_space S x0"
proof -
  have h_on: "continuous_on ({0..1} \<times> {0..1}) h"
    and h_intoW: "h \<in> ({0..1} \<times> {0..1}) \<rightarrow> W"
    using h_cont by simp_all
  have vt_path: "path (vertical_strip_path h t c d)"
  proof -
    have "continuous_on {0..1} (vertical_strip_path h t c d)"
    proof -
      have "continuous_on {0..1} (\<lambda>u. h (t, (d - c) * u + c))"
      proof (rule continuous_on_compose2[OF h_on])
        show "continuous_on {0..1} (\<lambda>u. (t, (d - c) * u + c))"
          by (intro continuous_intros)
        show "(\<lambda>u. (t, (d - c) * u + c)) ` {0..1} \<subseteq> {0..1} \<times> {0..1}"
        proof
          fix x
          assume "x \<in> (\<lambda>u. (t, (d - c) * u + c)) ` {0..1}"
          then obtain u where u01: "u \<in> {0..1}" and x_eq: "x = (t, (d - c) * u + c)"
            by blast
          have y_in: "(d - c) * u + c \<in> {0..1}"
            by (rule affine_unit_interval_member[OF c01 d01 cd u01])
          show "x \<in> {0..1} \<times> {0..1}"
            using t01 y_in x_eq by auto
        qed
      qed
      then show ?thesis
        by (simp add: vertical_strip_path_def)
    qed
    then show ?thesis
      by (simp add: vertical_strip_path_def path_def)
  qed
  have vt_imgW: "path_image (vertical_strip_path h t c d) \<subseteq> W"
  proof
    fix x
    assume x_in: "x \<in> path_image (vertical_strip_path h t c d)"
    then obtain u where u01: "u \<in> {0..1}" and x_eq: "x = vertical_strip_path h t c d u"
      unfolding path_image_def by blast
    have yu01: "(d - c) * u + c \<in> {0..1}"
      by (rule affine_unit_interval_member[OF c01 d01 cd u01])
    have point_in: "(t, (d - c) * u + c) \<in> {0..1} \<times> {0..1}"
      using t01 yu01 by auto
    show "x \<in> W"
      using h_intoW point_in x_eq by (auto simp: vertical_strip_path_def)
  qed
  have vt_imgS: "vertical_strip_path h t c d ` {0..1} \<subseteq> S"
  proof -
    have vs_subset: "vertical_strip_path h t c d ` {0..1} \<subseteq> h ` ({t} \<times> {c..d})"
      by (rule vertical_strip_path_image_subset[OF cd])
    show ?thesis
      using vs_subset edgeUV UVS by blast
  qed
  have tcUV: "h (t, c) \<in> U \<inter> V" and tdUV: "h (t, d) \<in> U \<inter> V"
    using edgeUV cd by auto
  have x0S: "x0 \<in> S"
    using x0_in_UV UVS by blast
  have "segment_loop (vertical_strip_path h t c d) 0 1 \<in> loop_space S x0"
  proof (rule segment_loop_in_set[where S = S])
    show "path (vertical_strip_path h t c d)"
      by (rule vt_path)
    show "path_image (vertical_strip_path h t c d) \<subseteq> W"
      by (rule vt_imgW)
    show "0 \<in> {0::real..1}"
      by auto
    show "1 \<in> {0::real..1}"
      by auto
    show "vertical_strip_path h t c d 0 \<in> U \<inter> V"
      using tcUV by (simp add: vertical_strip_path_def)
    show "vertical_strip_path h t c d 1 \<in> U \<inter> V"
      using tdUV by (simp add: vertical_strip_path_def)
    show "path_image (connector (vertical_strip_path h t c d 0)) \<subseteq> S"
      using connector_image_subset[OF tcUV] UVS by (simp add: vertical_strip_path_def; blast)
    show "path_image (connector (vertical_strip_path h t c d 1)) \<subseteq> S"
      using connector_image_subset[OF tdUV] UVS by (simp add: vertical_strip_path_def; blast)
    show "subpathin 0 1 (vertical_strip_path h t c d) ` {0..1} \<subseteq> S"
      using vt_imgS by (simp add: subpathin_def)
    show "x0 \<in> S"
      by (rule x0S)
  qed
  then show ?thesis
    by simp
qed

lemma rectangle_segment_loop_bridge_class_eq:
  fixes h :: "(real \<times> real) \<Rightarrow> 'a"
  assumes h_cont: "continuous_map (top_of_set ({0..1} \<times> {0..1})) (top_of_set W) h"
    and a01: "a \<in> {0..1}" and b01: "b \<in> {0..1}"
    and c01: "c \<in> {0..1}" and d01: "d \<in> {0..1}"
    and ab: "a \<le> b" and cd: "c \<le> d"
    and rectS: "h ` ({a..b} \<times> {c..d}) \<subseteq> S"
    and leftUV: "h ` ({a} \<times> {c..d}) \<subseteq> U \<inter> V"
    and rightUV: "h ` ({b} \<times> {c..d}) \<subseteq> U \<inter> V"
    and UVS: "U \<inter> V \<subseteq> S"
  shows "fundamental_group_mult S x0
      (loop_class S x0 (segment_loop (\<lambda>t. h (t, c)) a b))
      (loop_class S x0 (bridge_loop h b c d)) =
    fundamental_group_mult S x0
      (loop_class S x0 (bridge_loop h a c d))
      (loop_class S x0 (segment_loop (\<lambda>t. h (t, d)) a b))"
proof -
  have acUV: "h (a, c) \<in> U \<inter> V"
    using leftUV cd by auto
  have bcUV: "h (b, c) \<in> U \<inter> V"
    using rightUV cd by auto
  have adUV: "h (a, d) \<in> U \<inter> V"
    using leftUV cd by auto
  have bdUV: "h (b, d) \<in> U \<inter> V"
    using rightUV cd by auto

  have segc_in_S: "h ` ({a..b} \<times> {c}) \<subseteq> S"
  proof
    fix x
    assume x_in: "x \<in> h ` ({a..b} \<times> {c})"
    then obtain aa where aa_in: "aa \<in> {a..b}" and x_eq: "x = h (aa, c)"
      by auto
    have "(aa, c) \<in> {a..b} \<times> {c..d}"
      using aa_in cd by auto
    then show "x \<in> S"
      using rectS x_eq by blast
  qed
  have segd_in_S: "h ` ({a..b} \<times> {d}) \<subseteq> S"
  proof
    fix x
    assume x_in: "x \<in> h ` ({a..b} \<times> {d})"
    then obtain aa where aa_in: "aa \<in> {a..b}" and x_eq: "x = h (aa, d)"
      by auto
    have "(aa, d) \<in> {a..b} \<times> {c..d}"
      using aa_in cd by auto
    then show "x \<in> S"
      using rectS x_eq by blast
  qed
  have segc_loop: "segment_loop (\<lambda>t. h (t, c)) a b \<in> loop_space S x0"
    by (rule horizontal_rectangle_segment_loop_in_set[OF h_cont a01 b01 c01 ab]) (use segc_in_S acUV bcUV UVS in auto)
  have segd_loop: "segment_loop (\<lambda>t. h (t, d)) a b \<in> loop_space S x0"
    by (rule horizontal_rectangle_segment_loop_in_set[OF h_cont a01 b01 d01 ab]) (use segd_in_S adUV bdUV UVS in auto)
  have bridge_b_loop: "bridge_loop h b c d \<in> loop_space S x0"
    by (rule vertical_bridge_loop_in_set[OF h_cont b01 c01 d01 cd]) (use rightUV UVS in auto)
  have bridge_a_loop: "bridge_loop h a c d \<in> loop_space S x0"
    by (rule vertical_bridge_loop_in_set[OF h_cont a01 c01 d01 cd]) (use leftUV UVS in auto)

  have left_join_loop:
    "segment_loop (\<lambda>t. h (t, c)) a b +++ bridge_loop h b c d \<in> loop_space S x0"
    by (rule loop_space_join[OF segc_loop bridge_b_loop])
  have right_join_loop:
    "bridge_loop h a c d +++ segment_loop (\<lambda>t. h (t, d)) a b \<in> loop_space S x0"
    by (rule loop_space_join[OF bridge_a_loop segd_loop])

  have segc_in: "loop_class S x0 (segment_loop (\<lambda>t. h (t, c)) a b) \<in> fundamental_group_space S x0"
    by (rule loop_class_in_space[OF segc_loop])
  have segd_in: "loop_class S x0 (segment_loop (\<lambda>t. h (t, d)) a b) \<in> fundamental_group_space S x0"
    by (rule loop_class_in_space[OF segd_loop])
  have bridge_a_in: "loop_class S x0 (bridge_loop h a c d) \<in> fundamental_group_space S x0"
    by (rule loop_class_in_space[OF bridge_a_loop])
  have bridge_b_in: "loop_class S x0 (bridge_loop h b c d) \<in> fundamental_group_space S x0"
    by (rule loop_class_in_space[OF bridge_b_loop])

  have left_mult:
    "fundamental_group_mult S x0
      (loop_class S x0 (segment_loop (\<lambda>t. h (t, c)) a b))
      (loop_class S x0 (bridge_loop h b c d)) =
      loop_class S x0 (segment_loop (\<lambda>t. h (t, c)) a b +++ bridge_loop h b c d)"
    by (rule fundamental_group_mult_eqI[OF segc_in bridge_b_in segc_loop bridge_b_loop]) simp_all
  have right_mult:
    "fundamental_group_mult S x0
      (loop_class S x0 (bridge_loop h a c d))
      (loop_class S x0 (segment_loop (\<lambda>t. h (t, d)) a b)) =
      loop_class S x0 (bridge_loop h a c d +++ segment_loop (\<lambda>t. h (t, d)) a b)"
    by (rule fundamental_group_mult_eqI[OF bridge_a_in segd_in bridge_a_loop segd_loop]) simp_all

  have joined_hom:
    "homotopic_paths S
      (segment_loop (\<lambda>t. h (t, c)) a b +++ bridge_loop h b c d)
      (bridge_loop h a c d +++ segment_loop (\<lambda>t. h (t, d)) a b)"
    by (rule rectangle_segment_loop_bridge_homotopic[OF h_cont a01 b01 c01 d01 ab cd rectS leftUV rightUV UVS])
  have joined_eq:
    "loop_class S x0 (segment_loop (\<lambda>t. h (t, c)) a b +++ bridge_loop h b c d) =
      loop_class S x0 (bridge_loop h a c d +++ segment_loop (\<lambda>t. h (t, d)) a b)"
    by (rule loop_class_eqI[OF left_join_loop right_join_loop joined_hom])

  show ?thesis
    using left_mult right_mult joined_eq by simp
qed

lemma bridge_word_identify:
  assumes h_in: "h \<in> H"
  shows "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2
      (bridge_word True h rest) (bridge_word False h rest)"
    and "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2
      (bridge_word False h rest) (bridge_word True h rest)"
proof -
  have step:
    "carrier_amalgam_equiv H i1 i2 (bridge_word True h rest) (bridge_word False h rest)"
    using h_in
    by (auto simp: bridge_word.simps intro: carrier_amalgam_equiv.step carrier_amalgam_step.identify)
  show "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2
      (bridge_word True h rest) (bridge_word False h rest)"
    by (rule carrier_full_amalg_equiv.of_amalg[OF step])
  then show "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2
      (bridge_word False h rest) (bridge_word True h rest)"
    by (rule carrier_full_amalg_equiv.sym)
qed

lemma rectangle_partition_step_props:
  assumes "rectangle_partition h c d (t # u # ts) (b # bs)"
  shows "t \<in> {0..1}"
    and "u \<in> {0..1}"
    and "t < u"
    and "(if b then h ` ({t..u} \<times> {c..d}) \<subseteq> U else h ` ({t..u} \<times> {c..d}) \<subseteq> V)"
    and "rectangle_partition h c d (u # ts) bs"
  using assms by simp_all

lemma rectangle_partition_switch_edge:
  assumes rp: "rectangle_partition h c d (t # u # v # ts) (b # e # bs)"
    and diff: "b \<noteq> e"
  shows "h ` ({u} \<times> {c..d}) \<subseteq> U \<inter> V"
proof (cases b)
  case True
  have step: "rectangle_partition h c d (u # v # ts) (e # bs)"
    by (rule rectangle_partition_step_props(5)[OF rp])
  have tu: "t < u" and uv: "u < v"
    using rp step by simp_all
  have leftU: "h ` ({t..u} \<times> {c..d}) \<subseteq> U"
    using rectangle_partition_step_props(4)[OF rp] True by simp
  from diff True have e_false: "\<not> e"
    by simp
  then have rightV: "h ` ({u..v} \<times> {c..d}) \<subseteq> V"
    using rectangle_partition_step_props(4)[OF step] by simp
  show ?thesis
  proof
    fix x
    assume x_in: "x \<in> h ` ({u} \<times> {c..d})"
    then obtain y where y_cd: "y \<in> {c..d}" and x_eq: "x = h (u, y)"
      by auto
    have u_tu: "u \<in> {t..u}" and u_uv: "u \<in> {u..v}"
      using tu uv by auto
    have xU: "x \<in> U"
      using leftU x_eq u_tu y_cd by auto
    have xV: "x \<in> V"
      using rightV x_eq u_uv y_cd by auto
    show "x \<in> U \<inter> V"
      using xU xV by blast
  qed
next
  case False
  have step: "rectangle_partition h c d (u # v # ts) (e # bs)"
    by (rule rectangle_partition_step_props(5)[OF rp])
  have tu: "t < u" and uv: "u < v"
    using rp step by simp_all
  have leftV: "h ` ({t..u} \<times> {c..d}) \<subseteq> V"
    using rectangle_partition_step_props(4)[OF rp] False by simp
  from diff False have e_true: "e"
    by simp
  then have rightU: "h ` ({u..v} \<times> {c..d}) \<subseteq> U"
    using rectangle_partition_step_props(4)[OF step] by simp
  show ?thesis
  proof
    fix x
    assume x_in: "x \<in> h ` ({u} \<times> {c..d})"
    then obtain y where y_cd: "y \<in> {c..d}" and x_eq: "x = h (u, y)"
      by auto
    have u_tu: "u \<in> {t..u}" and u_uv: "u \<in> {u..v}"
      using tu uv by auto
    have xU: "x \<in> U"
      using rightU x_eq u_uv y_cd by auto
    have xV: "x \<in> V"
      using leftV x_eq u_tu y_cd by auto
    show "x \<in> U \<inter> V"
      using xU xV by blast
  qed
qed

lemma carrier_full_amalg_equiv_side_context:
  assumes rel: "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2 u v"
    and a_in: "(if b then a \<in> G1 else a \<in> G2)"
  shows "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2
      (if b then WordLeft a u else WordRight a u)
      (if b then WordLeft a v else WordRight a v)"
  using rel a_in
  by (cases b) (auto intro: carrier_full_amalg_equiv_left_context carrier_full_amalg_equiv_right_context)

lemma bridge_word_switch:
  assumes h_in: "h \<in> H"
    and bc: "b \<noteq> c"
  shows "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2
      (bridge_word b h rest) (bridge_word c h rest)"
  using h_in bc bridge_word_identify
  by (cases b; cases c) auto

lemma rectangle_segment_bridge_left_equiv:
  fixes h :: "(real \<times> real) \<Rightarrow> 'a"
  assumes h_cont: "continuous_map (top_of_set ({0..1} \<times> {0..1})) (top_of_set W) h"
    and a01: "a \<in> {0..1}" and b01: "b \<in> {0..1}"
    and c01: "c \<in> {0..1}" and d01: "d \<in> {0..1}"
    and ab: "a \<le> b" and cd: "c \<le> d"
    and rectU: "h ` ({a..b} \<times> {c..d}) \<subseteq> U"
    and leftUV: "h ` ({a} \<times> {c..d}) \<subseteq> U \<inter> V"
    and rightUV: "h ` ({b} \<times> {c..d}) \<subseteq> U \<inter> V"
    and rest_in: "fpw_in_space G1 G2 rest"
  shows "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2
      (WordLeft (loop_class U x0 (segment_loop (\<lambda>t. h (t, c)) a b))
        (bridge_word True (loop_class (U \<inter> V) x0 (bridge_loop h b c d)) rest))
      (bridge_word True (loop_class (U \<inter> V) x0 (bridge_loop h a c d))
        (WordLeft (loop_class U x0 (segment_loop (\<lambda>t. h (t, d)) a b)) rest))"
proof -
  define bottom where
    "bottom = loop_class U x0 (segment_loop (\<lambda>t. h (t, c)) a b)"
  define top where
    "top = loop_class U x0 (segment_loop (\<lambda>t. h (t, d)) a b)"
  define ga where
    "ga = loop_class (U \<inter> V) x0 (bridge_loop h a c d)"
  define gb where
    "gb = loop_class (U \<inter> V) x0 (bridge_loop h b c d)"

  have acUV: "h (a, c) \<in> U \<inter> V"
    using leftUV cd by auto
  have bcUV: "h (b, c) \<in> U \<inter> V"
    using rightUV cd by auto
  have adUV: "h (a, d) \<in> U \<inter> V"
    using leftUV cd by auto
  have bdUV: "h (b, d) \<in> U \<inter> V"
    using rightUV cd by auto

  have segc_in_U: "h ` ({a..b} \<times> {c}) \<subseteq> U"
  proof
    fix x
    assume x_in: "x \<in> h ` ({a..b} \<times> {c})"
    then obtain aa where aa_in: "aa \<in> {a..b}" and x_eq: "x = h (aa, c)"
      by auto
    have "(aa, c) \<in> {a..b} \<times> {c..d}"
      using aa_in cd by auto
    then show "x \<in> U"
      using rectU x_eq by blast
  qed
  have segd_in_U: "h ` ({a..b} \<times> {d}) \<subseteq> U"
  proof
    fix x
    assume x_in: "x \<in> h ` ({a..b} \<times> {d})"
    then obtain aa where aa_in: "aa \<in> {a..b}" and x_eq: "x = h (aa, d)"
      by auto
    have "(aa, d) \<in> {a..b} \<times> {c..d}"
      using aa_in cd by auto
    then show "x \<in> U"
      using rectU x_eq by blast
  qed
  have segc_loop: "segment_loop (\<lambda>t. h (t, c)) a b \<in> loop_space U x0"
    by (rule horizontal_rectangle_segment_loop_in_set[OF h_cont a01 b01 c01 ab])
      (use segc_in_U acUV bcUV in auto)
  have segd_loop: "segment_loop (\<lambda>t. h (t, d)) a b \<in> loop_space U x0"
    by (rule horizontal_rectangle_segment_loop_in_set[OF h_cont a01 b01 d01 ab])
      (use segd_in_U adUV bdUV in auto)
  have bridge_a_loop: "bridge_loop h a c d \<in> loop_space (U \<inter> V) x0"
    by (rule vertical_bridge_loop_in_set[OF h_cont a01 c01 d01 cd leftUV]) simp
  have bridge_b_loop: "bridge_loop h b c d \<in> loop_space (U \<inter> V) x0"
    by (rule vertical_bridge_loop_in_set[OF h_cont b01 c01 d01 cd rightUV]) simp

  have bottom_in: "bottom \<in> G1"
    unfolding bottom_def by (rule loop_class_in_space[OF segc_loop])
  have top_in: "top \<in> G1"
    unfolding top_def by (rule loop_class_in_space[OF segd_loop])
  have ga_in_H: "ga \<in> H"
    unfolding ga_def by (rule loop_class_in_space[OF bridge_a_loop])
  have gb_in_H: "gb \<in> H"
    unfolding gb_def by (rule loop_class_in_space[OF bridge_b_loop])
  have ga_in: "i1 ga \<in> G1"
    by (rule i1_in_G1[OF ga_in_H])
  have gb_in: "i1 gb \<in> G1"
    by (rule i1_in_G1[OF gb_in_H])
  have ab_in: "mult1 bottom (i1 gb) \<in> G1"
    by (rule fundamental_group_mult_in_space[OF bottom_in gb_in])
  have cd_in: "mult1 (i1 ga) top \<in> G1"
    by (rule fundamental_group_mult_in_space[OF ga_in top_in])

  have ga_eq: "i1 ga = loop_class U x0 (bridge_loop h a c d)"
    unfolding ga_def
    by (subst i1_loop_class_eq[OF bridge_a_loop]) simp
  have gb_eq: "i1 gb = loop_class U x0 (bridge_loop h b c d)"
    unfolding gb_def
    by (subst i1_loop_class_eq[OF bridge_b_loop]) simp
  have mult_eq: "mult1 bottom (i1 gb) = mult1 (i1 ga) top"
    unfolding bottom_def top_def ga_eq gb_eq
    by (rule rectangle_segment_loop_bridge_class_eq[OF h_cont a01 b01 c01 d01 ab cd rectU leftUV rightUV])
       auto
  have pair_eq:
    "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2
      (WordLeft bottom (WordLeft (i1 gb) rest))
      (WordLeft (i1 ga) (WordLeft top rest))"
    by (rule carrier_full_amalg_equiv_left_pair_eq[OF bottom_in gb_in ab_in ga_in top_in cd_in rest_in mult_eq])

  show ?thesis
    using pair_eq
    by (simp only: bottom_def top_def bridge_word.simps ga_def gb_def)
qed

lemma rectangle_segment_bridge_right_equiv:
  fixes h :: "(real \<times> real) \<Rightarrow> 'a"
  assumes h_cont: "continuous_map (top_of_set ({0..1} \<times> {0..1})) (top_of_set W) h"
    and a01: "a \<in> {0..1}" and b01: "b \<in> {0..1}"
    and c01: "c \<in> {0..1}" and d01: "d \<in> {0..1}"
    and ab: "a \<le> b" and cd: "c \<le> d"
    and rectV: "h ` ({a..b} \<times> {c..d}) \<subseteq> V"
    and leftUV: "h ` ({a} \<times> {c..d}) \<subseteq> U \<inter> V"
    and rightUV: "h ` ({b} \<times> {c..d}) \<subseteq> U \<inter> V"
    and rest_in: "fpw_in_space G1 G2 rest"
  shows "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2
      (WordRight (loop_class V x0 (segment_loop (\<lambda>t. h (t, c)) a b))
        (bridge_word False (loop_class (U \<inter> V) x0 (bridge_loop h b c d)) rest))
      (bridge_word False (loop_class (U \<inter> V) x0 (bridge_loop h a c d))
        (WordRight (loop_class V x0 (segment_loop (\<lambda>t. h (t, d)) a b)) rest))"
proof -
  define bottom where
    "bottom = loop_class V x0 (segment_loop (\<lambda>t. h (t, c)) a b)"
  define top where
    "top = loop_class V x0 (segment_loop (\<lambda>t. h (t, d)) a b)"
  define ga where
    "ga = loop_class (U \<inter> V) x0 (bridge_loop h a c d)"
  define gb where
    "gb = loop_class (U \<inter> V) x0 (bridge_loop h b c d)"

  have acUV: "h (a, c) \<in> U \<inter> V"
    using leftUV cd by auto
  have bcUV: "h (b, c) \<in> U \<inter> V"
    using rightUV cd by auto
  have adUV: "h (a, d) \<in> U \<inter> V"
    using leftUV cd by auto
  have bdUV: "h (b, d) \<in> U \<inter> V"
    using rightUV cd by auto

  have segc_in_V: "h ` ({a..b} \<times> {c}) \<subseteq> V"
  proof
    fix x
    assume x_in: "x \<in> h ` ({a..b} \<times> {c})"
    then obtain aa where aa_in: "aa \<in> {a..b}" and x_eq: "x = h (aa, c)"
      by auto
    have "(aa, c) \<in> {a..b} \<times> {c..d}"
      using aa_in cd by auto
    then show "x \<in> V"
      using rectV x_eq by blast
  qed
  have segd_in_V: "h ` ({a..b} \<times> {d}) \<subseteq> V"
  proof
    fix x
    assume x_in: "x \<in> h ` ({a..b} \<times> {d})"
    then obtain aa where aa_in: "aa \<in> {a..b}" and x_eq: "x = h (aa, d)"
      by auto
    have "(aa, d) \<in> {a..b} \<times> {c..d}"
      using aa_in cd by auto
    then show "x \<in> V"
      using rectV x_eq by blast
  qed
  have segc_loop: "segment_loop (\<lambda>t. h (t, c)) a b \<in> loop_space V x0"
    by (rule horizontal_rectangle_segment_loop_in_set[OF h_cont a01 b01 c01 ab])
      (use segc_in_V acUV bcUV in auto)
  have segd_loop: "segment_loop (\<lambda>t. h (t, d)) a b \<in> loop_space V x0"
  proof -
    have UVV: "U \<inter> V \<subseteq> V"
      by blast
    show ?thesis
      by (rule horizontal_rectangle_segment_loop_in_set[OF h_cont a01 b01 d01 ab segd_in_V adUV bdUV UVV])
  qed
  have bridge_a_loop: "bridge_loop h a c d \<in> loop_space (U \<inter> V) x0"
    by (rule vertical_bridge_loop_in_set[OF h_cont a01 c01 d01 cd leftUV]) simp
  have bridge_b_loop: "bridge_loop h b c d \<in> loop_space (U \<inter> V) x0"
    by (rule vertical_bridge_loop_in_set[OF h_cont b01 c01 d01 cd rightUV]) simp

  have bottom_in: "bottom \<in> G2"
    unfolding bottom_def by (rule loop_class_in_space[OF segc_loop])
  have top_in: "top \<in> G2"
    unfolding top_def by (rule loop_class_in_space[OF segd_loop])
  have ga_in_H: "ga \<in> H"
    unfolding ga_def by (rule loop_class_in_space[OF bridge_a_loop])
  have gb_in_H: "gb \<in> H"
    unfolding gb_def by (rule loop_class_in_space[OF bridge_b_loop])
  have ga_in: "i2 ga \<in> G2"
    by (rule i2_in_G2[OF ga_in_H])
  have gb_in: "i2 gb \<in> G2"
    by (rule i2_in_G2[OF gb_in_H])
  have ab_in: "mult2 bottom (i2 gb) \<in> G2"
    by (rule fundamental_group_mult_in_space[OF bottom_in gb_in])
  have cd_in: "mult2 (i2 ga) top \<in> G2"
    by (rule fundamental_group_mult_in_space[OF ga_in top_in])

  have ga_eq: "i2 ga = loop_class V x0 (bridge_loop h a c d)"
    unfolding ga_def
    by (subst i2_loop_class_eq[OF bridge_a_loop]) simp
  have gb_eq: "i2 gb = loop_class V x0 (bridge_loop h b c d)"
    unfolding gb_def
    by (subst i2_loop_class_eq[OF bridge_b_loop]) simp
  have mult_eq: "mult2 bottom (i2 gb) = mult2 (i2 ga) top"
    unfolding bottom_def top_def ga_eq gb_eq
    by (rule rectangle_segment_loop_bridge_class_eq[OF h_cont a01 b01 c01 d01 ab cd rectV leftUV rightUV])
       auto
  have pair_eq:
    "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2
      (WordRight bottom (WordRight (i2 gb) rest))
      (WordRight (i2 ga) (WordRight top rest))"
    by (rule carrier_full_amalg_equiv_right_pair_eq[OF bottom_in gb_in ab_in ga_in top_in cd_in rest_in mult_eq])

  show ?thesis
    using pair_eq
    by (simp only: bottom_def top_def bridge_word.simps ga_def gb_def)
qed

lemma rectangle_partition_partition_word_with_tail_in_space:
  fixes h :: "(real \<times> real) \<Rightarrow> 'a"
  assumes h_cont: "continuous_map (top_of_set ({0..1} \<times> {0..1})) (top_of_set W) h"
    and c01: "c \<in> {0..1}" and d01: "d \<in> {0..1}" and cd: "c \<le> d"
    and y_in: "y \<in> {c, d}"
    and part: "rectangle_partition h c d ts bs"
    and edgeUV: "\<And>t. t \<in> set ts \<Longrightarrow> h ` ({t} \<times> {c..d}) \<subseteq> U \<inter> V"
    and tail_in: "fpw_in_space G1 G2 rest"
  shows "fpw_in_space G1 G2 (partition_word_with_tail (\<lambda>t. h (t, y)) ts bs rest)"
  using part edgeUV
proof (induction ts arbitrary: bs)
  case Nil
  then show ?case
    by (cases bs) (simp_all add: tail_in)
next
  case (Cons t ts)
  show ?case
  proof (cases ts)
    case Nil
    then show ?thesis
      using Cons.prems tail_in by (cases bs) simp_all
  next
    case (Cons u us)
    obtain b bs' where bs: "bs = b # bs'"
      using Cons.prems Cons by (cases bs) auto
    have tail_part: "rectangle_partition h c d (u # us) bs'"
      using Cons.prems Cons bs by simp
    have tail_edgeUV:
      "\<And>x. x \<in> set (u # us) \<Longrightarrow> h ` ({x} \<times> {c..d}) \<subseteq> U \<inter> V"
      using Cons.prems Cons by auto
    have tail_in':
      "fpw_in_space G1 G2 (partition_word_with_tail (\<lambda>t. h (t, y)) (u # us) bs' rest)"
      using h_cont c01 d01 cd y_in Cons.IH[of bs'] Cons tail_part tail_edgeUV tail_in bs
      by simp

    have t01: "t \<in> {0..1}" and u01: "u \<in> {0..1}" and tu: "t < u"
      and rect_side:
        "(if b then h ` ({t..u} \<times> {c..d}) \<subseteq> U else h ` ({t..u} \<times> {c..d}) \<subseteq> V)"
      using Cons.prems Cons bs by simp_all
    have y01: "y \<in> {0..1}"
      using y_in c01 d01 by auto
    have y_cd: "y \<in> {c..d}"
      using y_in cd by auto
    have tu_le: "t \<le> u"
      using tu by simp
    have tyUV: "h (t, y) \<in> U \<inter> V"
    proof -
      have t_edge: "h ` ({t} \<times> {c..d}) \<subseteq> U \<inter> V"
        using Cons.prems(2)[of t] Cons by simp
      moreover have "(t, y) \<in> {t} \<times> {c..d}"
        using y_cd by auto
      ultimately show ?thesis
        using t_edge
        by blast
    qed
    have uyUV: "h (u, y) \<in> U \<inter> V"
    proof -      
      have u_edge: "h ` ({u} \<times> {c..d}) \<subseteq> U \<inter> V"
        using Cons.prems(2)[of u] Cons by simp
      moreover have "(u, y) \<in> {u} \<times> {c..d}"
        using y_cd by auto
      ultimately show ?thesis
        using u_edge
        by blast
    qed

    show ?thesis
    proof (cases b)
      case True
      have segyU: "h ` ({t..u} \<times> {y}) \<subseteq> U"
      proof
        fix z
        assume z_in: "z \<in> h ` ({t..u} \<times> {y})"
        then obtain a where a_in: "a \<in> {t..u}" and z_eq: "z = h (a, y)"
          by auto
        have "(a, y) \<in> {t..u} \<times> {c..d}"
          using a_in y_cd by auto
        then have z_strip: "z \<in> h ` ({t..u} \<times> {c..d})"
          using z_eq by blast
        have stripU: "h ` ({t..u} \<times> {c..d}) \<subseteq> U"
          using rect_side True by simp
        then show "z \<in> U"
          using z_strip by blast
      qed
      have segU: "segment_loop (\<lambda>t. h (t, y)) t u \<in> loop_space U x0"
        by (rule horizontal_rectangle_segment_loop_in_set[OF h_cont t01 u01 y01 tu_le])
          (use segyU tyUV uyUV in auto)
      have seg_in: "loop_class U x0 (segment_loop (\<lambda>t. h (t, y)) t u) \<in> G1"
        by (rule loop_class_in_space[OF segU])
      show ?thesis
        using True seg_in tail_in' bs Cons by simp
    next
      case False
      have segyV: "h ` ({t..u} \<times> {y}) \<subseteq> V"
      proof
        fix z
        assume z_in: "z \<in> h ` ({t..u} \<times> {y})"
        then obtain a where a_in: "a \<in> {t..u}" and z_eq: "z = h (a, y)"
          by auto
        have "(a, y) \<in> {t..u} \<times> {c..d}"
          using a_in y_cd by auto
        then have z_strip: "z \<in> h ` ({t..u} \<times> {c..d})"
          using z_eq by blast
        have stripV: "h ` ({t..u} \<times> {c..d}) \<subseteq> V"
          using rect_side False by simp
        then show "z \<in> V"
          using z_strip by blast
      qed
      have segV: "segment_loop (\<lambda>t. h (t, y)) t u \<in> loop_space V x0"
        by (rule horizontal_rectangle_segment_loop_in_set[OF h_cont t01 u01 y01 tu_le])
          (use segyV tyUV uyUV in auto)
      have seg_in: "loop_class V x0 (segment_loop (\<lambda>t. h (t, y)) t u) \<in> G2"
        by (rule loop_class_in_space[OF segV])
      show ?thesis
        using False seg_in tail_in' bs Cons by simp
    qed
  qed
qed

lemma rectangle_partition_partition_word_with_tail_equiv:
  fixes h :: "(real \<times> real) \<Rightarrow> 'a"
  assumes h_cont: "continuous_map (top_of_set ({0..1} \<times> {0..1})) (top_of_set W) h"
    and c01: "c \<in> {0..1}" and d01: "d \<in> {0..1}" and cd: "c \<le> d"
    and part: "rectangle_partition h c d (t # u # ts) (b # bs)"
    and edgeUV: "\<And>x. x \<in> set (t # u # ts) \<Longrightarrow> h ` ({x} \<times> {c..d}) \<subseteq> U \<inter> V"
    and rest_in: "fpw_in_space G1 G2 rest"
  shows "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2
      (partition_word_with_tail (\<lambda>x. h (x, c)) (t # u # ts) (b # bs)
        (bridge_word (last (b # bs))
          (loop_class (U \<inter> V) x0 (bridge_loop h (last (t # u # ts)) c d)) rest))
      (bridge_word b (loop_class (U \<inter> V) x0 (bridge_loop h t c d))
        (partition_word_with_tail (\<lambda>x. h (x, d)) (t # u # ts) (b # bs) rest))"
  using part rest_in edgeUV
proof (induction bs arbitrary: t u ts b rest)
  case Nil
  have ts_nil: "ts = []"
  proof (cases ts)
    case Nil
    then show ?thesis .
  next
    case (Cons v vs)
    with Nil.prems(1) show ?thesis
      by simp
  qed
  have u1: "u = 1"
    using Nil.prems(1) ts_nil by simp
  have t01: "t \<in> {0..1}" and u01: "u \<in> {0..1}" and tu: "t < u"
    using Nil.prems(1) ts_nil by simp_all
  have tu_le: "t \<le> u"
    using tu by simp
  have rect_side: "(if b then h ` ({t..u} \<times> {c..d}) \<subseteq> U else h ` ({t..u} \<times> {c..d}) \<subseteq> V)"
    using Nil.prems(1) ts_nil u1 by simp
  have t_in: "t \<in> set (t # u # ts)"
    by simp
  have u_in: "u \<in> set (t # u # ts)"
    by simp
  have leftUV: "h ` ({t} \<times> {c..d}) \<subseteq> U \<inter> V"
    by (rule Nil.prems(3)[OF t_in])
  have rightUV: "h ` ({u} \<times> {c..d}) \<subseteq> U \<inter> V"
    by (rule Nil.prems(3)[OF u_in])
  show ?case
  proof (cases b)
    case True
    have rectU: "h ` ({t..u} \<times> {c..d}) \<subseteq> U"
      using rect_side True by simp
    have rel:
      "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2
        (WordLeft (loop_class U x0 (segment_loop (\<lambda>x. h (x, c)) t u))
          (bridge_word True (loop_class (U \<inter> V) x0 (bridge_loop h u c d)) rest))
        (bridge_word True (loop_class (U \<inter> V) x0 (bridge_loop h t c d))
          (WordLeft (loop_class U x0 (segment_loop (\<lambda>x. h (x, d)) t u)) rest))"
      by (rule rectangle_segment_bridge_left_equiv[
            where h = h and a = t and b = u and c = c and d = d and rest = rest,
            OF h_cont t01 u01 c01 d01 tu_le cd rectU leftUV rightUV Nil.prems(2)])
    have lhs_eq:
      "partition_word_with_tail (\<lambda>x. h (x, c)) (t # u # ts) [b]
         (bridge_word (last [b])
           (loop_class (U \<inter> V) x0 (bridge_loop h (last (t # u # ts)) c d)) rest) =
       WordLeft (loop_class U x0 (segment_loop (\<lambda>x. h (x, c)) t u))
         (bridge_word True (loop_class (U \<inter> V) x0 (bridge_loop h u c d)) rest)"
      using True ts_nil by simp
    have rhs_eq:
      "bridge_word b (loop_class (U \<inter> V) x0 (bridge_loop h t c d))
         (partition_word_with_tail (\<lambda>x. h (x, d)) (t # u # ts) [b] rest) =
       bridge_word True (loop_class (U \<inter> V) x0 (bridge_loop h t c d))
         (WordLeft (loop_class U x0 (segment_loop (\<lambda>x. h (x, d)) t u)) rest)"
      using True ts_nil by simp
    show ?thesis
      unfolding lhs_eq rhs_eq by (rule rel)
  next
    case False
    have rectV: "h ` ({t..u} \<times> {c..d}) \<subseteq> V"
      using rect_side False by simp
    have rel:
      "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2
        (WordRight (loop_class V x0 (segment_loop (\<lambda>x. h (x, c)) t u))
          (bridge_word False (loop_class (U \<inter> V) x0 (bridge_loop h u c d)) rest))
        (bridge_word False (loop_class (U \<inter> V) x0 (bridge_loop h t c d))
          (WordRight (loop_class V x0 (segment_loop (\<lambda>x. h (x, d)) t u)) rest))"
      by (rule rectangle_segment_bridge_right_equiv[
            where h = h and a = t and b = u and c = c and d = d and rest = rest,
            OF h_cont t01 u01 c01 d01 tu_le cd rectV leftUV rightUV Nil.prems(2)])
    have lhs_eq:
      "partition_word_with_tail (\<lambda>x. h (x, c)) (t # u # ts) [b]
         (bridge_word (last [b])
           (loop_class (U \<inter> V) x0 (bridge_loop h (last (t # u # ts)) c d)) rest) =
       WordRight (loop_class V x0 (segment_loop (\<lambda>x. h (x, c)) t u))
         (bridge_word False (loop_class (U \<inter> V) x0 (bridge_loop h u c d)) rest)"
      using False ts_nil by simp
    have rhs_eq:
      "bridge_word b (loop_class (U \<inter> V) x0 (bridge_loop h t c d))
         (partition_word_with_tail (\<lambda>x. h (x, d)) (t # u # ts) [b] rest) =
       bridge_word False (loop_class (U \<inter> V) x0 (bridge_loop h t c d))
         (WordRight (loop_class V x0 (segment_loop (\<lambda>x. h (x, d)) t u)) rest)"
      using False ts_nil by simp
    show ?thesis
      unfolding lhs_eq rhs_eq by (rule rel)
  qed
next
  case (Cons cflag bs')
  obtain v us where ts: "ts = v # us"
    using Cons.prems(1) by (cases ts) simp_all
  have t01: "t \<in> {0..1}" and u01: "u \<in> {0..1}" and tu: "t < u"
    and rect_side: "(if b then h ` ({t..u} \<times> {c..d}) \<subseteq> U else h ` ({t..u} \<times> {c..d}) \<subseteq> V)"
    and tail_part: "rectangle_partition h c d (u # v # us) (cflag # bs')"
    using Cons.prems(1) ts by simp_all
  have tu_le: "t \<le> u"
    using tu by simp
  have t_in: "t \<in> set (t # u # ts)"
    by simp
  have u_in: "u \<in> set (t # u # ts)"
    by simp
  have leftUV: "h ` ({t} \<times> {c..d}) \<subseteq> U \<inter> V"
    by (rule Cons.prems(3)[OF t_in])
  have midUV: "h ` ({u} \<times> {c..d}) \<subseteq> U \<inter> V"
    by (rule Cons.prems(3)[OF u_in])
  have top_tail_in:
    "fpw_in_space G1 G2
      (partition_word_with_tail (\<lambda>x. h (x, d)) (u # v # us) (cflag # bs') rest)"
    by (rule rectangle_partition_partition_word_with_tail_in_space[OF h_cont c01 d01 cd])
       (use tail_part Cons.prems(3) Cons.prems(2) ts in auto)
  have gu_loop: "bridge_loop h u c d \<in> loop_space (U \<inter> V) x0"
    by (rule vertical_bridge_loop_in_set[OF h_cont u01 c01 d01 cd]) (use midUV in auto)
  have gu_in_H: "loop_class (U \<inter> V) x0 (bridge_loop h u c d) \<in> H"
    by (rule loop_class_in_space[OF gu_loop])
  have tail_rel:
    "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2
      (partition_word_with_tail (\<lambda>x. h (x, c)) (u # v # us) (cflag # bs')
        (bridge_word (last (cflag # bs'))
          (loop_class (U \<inter> V) x0 (bridge_loop h (last (u # v # us)) c d)) rest))
      (bridge_word cflag (loop_class (U \<inter> V) x0 (bridge_loop h u c d))
        (partition_word_with_tail (\<lambda>x. h (x, d)) (u # v # us) (cflag # bs') rest))"
    by (rule Cons.IH[OF tail_part])
       (use h_cont c01 d01 cd Cons.prems(3) Cons.prems(2) ts in auto)
  have tail_switched:
    "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2
      (partition_word_with_tail (\<lambda>x. h (x, c)) (u # v # us) (cflag # bs')
        (bridge_word (last (cflag # bs'))
          (loop_class (U \<inter> V) x0 (bridge_loop h (last (u # v # us)) c d)) rest))
      (bridge_word b (loop_class (U \<inter> V) x0 (bridge_loop h u c d))
        (partition_word_with_tail (\<lambda>x. h (x, d)) (u # v # us) (cflag # bs') rest))"
  proof (cases "b = cflag")
    case True
    then show ?thesis
      using tail_rel by simp
  next
    case False
    have switch:
      "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2
        (bridge_word cflag (loop_class (U \<inter> V) x0 (bridge_loop h u c d))
          (partition_word_with_tail (\<lambda>x. h (x, d)) (u # v # us) (cflag # bs') rest))
        (bridge_word b (loop_class (U \<inter> V) x0 (bridge_loop h u c d))
          (partition_word_with_tail (\<lambda>x. h (x, d)) (u # v # us) (cflag # bs') rest))"
      by (rule carrier_full_amalg_equiv.sym[OF bridge_word_switch[OF gu_in_H False]])
    show ?thesis
      by (rule carrier_full_amalg_equiv.trans[OF tail_rel switch])
  qed
  show ?case
  proof (cases b)
    case True
    have seg_in: "loop_class U x0 (segment_loop (\<lambda>x. h (x, c)) t u) \<in> G1"
    proof -
      have line_subset: "{t..u} \<times> {c} \<subseteq> {t..u} \<times> {c..d}"
        using c01 cd by auto
      have rectU: "h ` ({t..u} \<times> {c..d}) \<subseteq> U"
        using rect_side True by simp
      have segU_line: "h ` ({t..u} \<times> {c}) \<subseteq> U"
        by (rule order_trans[OF image_mono[OF line_subset] rectU])
      have tcUV: "h (t, c) \<in> U \<inter> V"
        by (rule subsetD[OF leftUV]) (use cd in auto)
      have ucUV: "h (u, c) \<in> U \<inter> V"
        by (rule subsetD[OF midUV]) (use cd in auto)
      have seg_loop: "segment_loop (\<lambda>x. h (x, c)) t u \<in> loop_space U x0"
        by (rule horizontal_rectangle_segment_loop_in_set[OF h_cont t01 u01 c01 tu_le segU_line tcUV ucUV]) auto
      show ?thesis
        by (rule loop_class_in_space[OF seg_loop])
    qed
    have pref_rel:
      "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2
        (WordLeft (loop_class U x0 (segment_loop (\<lambda>x. h (x, c)) t u))
          (partition_word_with_tail (\<lambda>x. h (x, c)) (u # v # us) (cflag # bs')
            (bridge_word (last (cflag # bs'))
              (loop_class (U \<inter> V) x0 (bridge_loop h (last (u # v # us)) c d)) rest)))
        (WordLeft (loop_class U x0 (segment_loop (\<lambda>x. h (x, c)) t u))
          (bridge_word True (loop_class (U \<inter> V) x0 (bridge_loop h u c d))
            (partition_word_with_tail (\<lambda>x. h (x, d)) (u # v # us) (cflag # bs') rest)))"
    proof -
      have tail_true:
        "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2
          (partition_word_with_tail (\<lambda>x. h (x, c)) (u # v # us) (cflag # bs')
            (bridge_word (last (cflag # bs'))
              (loop_class (U \<inter> V) x0 (bridge_loop h (last (u # v # us)) c d)) rest))
          (bridge_word True (loop_class (U \<inter> V) x0 (bridge_loop h u c d))
            (partition_word_with_tail (\<lambda>x. h (x, d)) (u # v # us) (cflag # bs') rest))"
        using tail_switched True by simp
      show ?thesis
        by (rule carrier_full_amalg_equiv_left_context[OF tail_true seg_in])
    qed
    have cell_rel:
      "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2
        (WordLeft (loop_class U x0 (segment_loop (\<lambda>x. h (x, c)) t u))
          (bridge_word True (loop_class (U \<inter> V) x0 (bridge_loop h u c d))
            (partition_word_with_tail (\<lambda>x. h (x, d)) (u # v # us) (cflag # bs') rest)))
        (bridge_word True (loop_class (U \<inter> V) x0 (bridge_loop h t c d))
          (WordLeft (loop_class U x0 (segment_loop (\<lambda>x. h (x, d)) t u))
            (partition_word_with_tail (\<lambda>x. h (x, d)) (u # v # us) (cflag # bs') rest)))"
      by (rule rectangle_segment_bridge_left_equiv[OF h_cont t01 u01 c01 d01 tu_le cd])
         (use rect_side True leftUV midUV top_tail_in in auto)
    have lhs_eq:
      "partition_word_with_tail (\<lambda>x. h (x, c)) (t # u # ts) (b # cflag # bs')
         (bridge_word (last (b # cflag # bs'))
           (loop_class (U \<inter> V) x0 (bridge_loop h (last (t # u # ts)) c d)) rest) =
       WordLeft (loop_class U x0 (segment_loop (\<lambda>x. h (x, c)) t u))
         (partition_word_with_tail (\<lambda>x. h (x, c)) (u # v # us) (cflag # bs')
           (bridge_word (last (cflag # bs'))
             (loop_class (U \<inter> V) x0 (bridge_loop h (last (u # v # us)) c d)) rest))"
      using True ts by simp
    have rhs_eq:
      "bridge_word b (loop_class (U \<inter> V) x0 (bridge_loop h t c d))
         (partition_word_with_tail (\<lambda>x. h (x, d)) (t # u # ts) (b # cflag # bs') rest) =
       bridge_word True (loop_class (U \<inter> V) x0 (bridge_loop h t c d))
         (WordLeft (loop_class U x0 (segment_loop (\<lambda>x. h (x, d)) t u))
           (partition_word_with_tail (\<lambda>x. h (x, d)) (u # v # us) (cflag # bs') rest))"
      using True ts by simp
    show ?thesis
      unfolding lhs_eq rhs_eq by (rule carrier_full_amalg_equiv.trans[OF pref_rel cell_rel])
  next
    case False
    have seg_in: "loop_class V x0 (segment_loop (\<lambda>x. h (x, c)) t u) \<in> G2"
    proof -
      have line_subset: "{t..u} \<times> {c} \<subseteq> {t..u} \<times> {c..d}"
        using c01 cd by auto
      have rectV: "h ` ({t..u} \<times> {c..d}) \<subseteq> V"
        using rect_side False by simp
      have segV_line: "h ` ({t..u} \<times> {c}) \<subseteq> V"
        by (rule order_trans[OF image_mono[OF line_subset] rectV])
      have tcUV: "h (t, c) \<in> U \<inter> V"
        by (rule subsetD[OF leftUV]) (use cd in auto)
      have ucUV: "h (u, c) \<in> U \<inter> V"
        by (rule subsetD[OF midUV]) (use cd in auto)
      have seg_loop: "segment_loop (\<lambda>x. h (x, c)) t u \<in> loop_space V x0"
        by (rule horizontal_rectangle_segment_loop_in_set[OF h_cont t01 u01 c01 tu_le segV_line tcUV ucUV]) auto
      show ?thesis
        by (rule loop_class_in_space[OF seg_loop])
    qed
    have pref_rel:
      "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2
        (WordRight (loop_class V x0 (segment_loop (\<lambda>x. h (x, c)) t u))
          (partition_word_with_tail (\<lambda>x. h (x, c)) (u # v # us) (cflag # bs')
            (bridge_word (last (cflag # bs'))
              (loop_class (U \<inter> V) x0 (bridge_loop h (last (u # v # us)) c d)) rest)))
        (WordRight (loop_class V x0 (segment_loop (\<lambda>x. h (x, c)) t u))
          (bridge_word False (loop_class (U \<inter> V) x0 (bridge_loop h u c d))
            (partition_word_with_tail (\<lambda>x. h (x, d)) (u # v # us) (cflag # bs') rest)))"
    proof -
      have tail_false:
        "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2
          (partition_word_with_tail (\<lambda>x. h (x, c)) (u # v # us) (cflag # bs')
            (bridge_word (last (cflag # bs'))
              (loop_class (U \<inter> V) x0 (bridge_loop h (last (u # v # us)) c d)) rest))
          (bridge_word False (loop_class (U \<inter> V) x0 (bridge_loop h u c d))
            (partition_word_with_tail (\<lambda>x. h (x, d)) (u # v # us) (cflag # bs') rest))"
        using tail_switched False by simp
      show ?thesis
        by (rule carrier_full_amalg_equiv_right_context[OF tail_false seg_in])
    qed
    have cell_rel:
      "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2
        (WordRight (loop_class V x0 (segment_loop (\<lambda>x. h (x, c)) t u))
          (bridge_word False (loop_class (U \<inter> V) x0 (bridge_loop h u c d))
            (partition_word_with_tail (\<lambda>x. h (x, d)) (u # v # us) (cflag # bs') rest)))
        (bridge_word False (loop_class (U \<inter> V) x0 (bridge_loop h t c d))
          (WordRight (loop_class V x0 (segment_loop (\<lambda>x. h (x, d)) t u))
            (partition_word_with_tail (\<lambda>x. h (x, d)) (u # v # us) (cflag # bs') rest)))"
      by (rule rectangle_segment_bridge_right_equiv[OF h_cont t01 u01 c01 d01 tu_le cd])
         (use rect_side False leftUV midUV top_tail_in in auto)
    have lhs_eq:
      "partition_word_with_tail (\<lambda>x. h (x, c)) (t # u # ts) (b # cflag # bs')
         (bridge_word (last (b # cflag # bs'))
           (loop_class (U \<inter> V) x0 (bridge_loop h (last (t # u # ts)) c d)) rest) =
       WordRight (loop_class V x0 (segment_loop (\<lambda>x. h (x, c)) t u))
         (partition_word_with_tail (\<lambda>x. h (x, c)) (u # v # us) (cflag # bs')
           (bridge_word (last (cflag # bs'))
             (loop_class (U \<inter> V) x0 (bridge_loop h (last (u # v # us)) c d)) rest))"
      using False ts by simp
    have rhs_eq:
      "bridge_word b (loop_class (U \<inter> V) x0 (bridge_loop h t c d))
         (partition_word_with_tail (\<lambda>x. h (x, d)) (t # u # ts) (b # cflag # bs') rest) =
       bridge_word False (loop_class (U \<inter> V) x0 (bridge_loop h t c d))
         (WordRight (loop_class V x0 (segment_loop (\<lambda>x. h (x, d)) t u))
           (partition_word_with_tail (\<lambda>x. h (x, d)) (u # v # us) (cflag # bs') rest))"
      using False ts by simp
    show ?thesis
      unfolding lhs_eq rhs_eq by (rule carrier_full_amalg_equiv.trans[OF pref_rel cell_rel])
  qed
qed

lemma homotopic_paths_join_subpathin:
  assumes p_path: "path p"
    and p_img: "path_image p \<subseteq> S"
    and u01: "u \<in> {0..1}"
    and v01: "v \<in> {0..1}"
    and w01: "w \<in> {0..1}"
    and uv: "u \<le> v"
    and vw: "v \<le> w"
  shows "homotopic_paths S (subpathin u v p +++ subpathin v w p) (subpathin u w p)"
proof (cases "w = u")
  case True
  then have uvw: "u = v" "v = w"
    using uv vw by linarith+
  have pu_in: "p u \<in> S"
    using p_img u01 by (auto simp: path_image_def)
  have const_join: "subpathin u v p +++ subpathin v w p = (\<lambda>_. p u)"
    using uvw by (simp add: fun_eq_iff joinpaths_def subpathin_def)
  have const_subpath: "subpathin u w p = (\<lambda>_. p u)"
    using uvw by (simp add: fun_eq_iff subpathin_def)
  show ?thesis
    unfolding const_join const_subpath
    using pu_in by (simp add: path_def)
next
  case False
  define a where "a = (v - u) / (w - u)"
  have wu_pos: "0 < w - u"
    using False uv vw by linarith
  have a_nonneg: "0 \<le> a"
    unfolding a_def using uv wu_pos by (simp add: field_simps)
  have a_le1: "a \<le> 1"
    unfolding a_def using uv vw wu_pos by (simp add: field_simps)
  have a01: "a \<in> {0..1}"
    using a_nonneg a_le1 by auto
  let ?f = "\<lambda>t::real. if t \<le> 1 / 2 then 2 * a * t else a + (1 - a) * (2 * t - 1)"
  have f_eq: "?f = subpathin 0 a id +++ subpathin a 1 id"
    by (rule ext) (simp add: joinpaths_def subpathin_def)
  have contf: "continuous_on {0..1} ?f"
  proof -
    have id_path: "path id"
      by (simp add: path_def)
    have left_path: "path (subpathin 0 a id)"
      by (rule path_subpathin[OF id_path]) (use a01 in auto)
    have right_path: "path (subpathin a 1 id)"
      by (rule path_subpathin[OF id_path]) (use a01 in auto)
    have join_path: "path (subpathin 0 a id +++ subpathin a 1 id)"
      using left_path right_path a01
      by (simp add: pathstart_def pathfinish_def subpathin_def)
    show ?thesis
      unfolding f_eq
      using join_path by (simp add: path_def)
  qed
  have f01: "?f \<in> {0..1} \<rightarrow> {0..1}"
  proof
    fix t :: real
    assume t01: "t \<in> {0..1}"
    show "?f t \<in> {0..1}"
    proof (cases "t \<le> 1 / 2")
      case True
      have t_nonneg: "0 \<le> t"
        using t01 by auto
      have two_t_le1: "2 * t \<le> 1"
        using t01 True by linarith
      have lower: "0 \<le> 2 * a * t"
        using a_nonneg t_nonneg by (intro mult_nonneg_nonneg) auto
      have upper1: "a * (2 * t) \<le> a * 1"
        using a_nonneg two_t_le1 by (intro mult_left_mono) auto
      have upper: "2 * a * t \<le> 1"
        using upper1 a_le1 by (simp add: algebra_simps)
      show ?thesis
        using True lower upper by auto
    next
      case False
      have two_t_minus1_nonneg: "0 \<le> 2 * t - 1"
        using t01 False by linarith
      have two_t_minus1_le1: "2 * t - 1 \<le> 1"
      proof -
        have t_le1: "t \<le> 1"
          using t01 by auto
        then show ?thesis
          by linarith
      qed
      have one_minus_a_nonneg: "0 \<le> 1 - a"
        using a_le1 by linarith
      have lower: "0 \<le> a + (1 - a) * (2 * t - 1)"
        using a_nonneg one_minus_a_nonneg two_t_minus1_nonneg
        by (intro add_nonneg_nonneg mult_nonneg_nonneg)
      have upper1: "(1 - a) * (2 * t - 1) \<le> (1 - a) * 1"
        using one_minus_a_nonneg two_t_minus1_le1 by (intro mult_left_mono) auto
      have upper: "a + (1 - a) * (2 * t - 1) \<le> 1"
      proof -
        have "a + (1 - a) * (2 * t - 1) \<le> a + (1 - a) * 1"
          using upper1 by linarith
        also have "... = 1"
          by simp
        finally show ?thesis .
      qed
      show ?thesis
        using False lower upper by auto
    qed
  qed
  have sub_uw_path: "path (subpathin u w p)"
    by (rule path_subpathin[OF p_path u01 w01])
  have sub_uw_img: "path_image (subpathin u w p) \<subseteq> S"
    using p_img path_image_subpathin_subset[OF u01 w01, of p] by blast
  show ?thesis
  proof (rule homotopic_paths_sym[OF homotopic_paths_reparametrize[where p = "subpathin u w p" and f = ?f]])
    show "path (subpathin u w p)"
      by (rule sub_uw_path)
    show "path_image (subpathin u w p) \<subseteq> S"
      by (rule sub_uw_img)
    show "continuous_on {0..1} ?f"
      by (rule contf)
    show "?f \<in> {0..1} \<rightarrow> {0..1}"
      by (rule f01)
    show "?f 0 = 0"
      by simp
    show "?f 1 = 1"
      using a_nonneg a_le1 by simp
    show "(subpathin u v p +++ subpathin v w p) t = subpathin u w p (?f t)"
      if t01: "t \<in> {0..1}" for t
    proof (cases "t \<le> 1 / 2")
      case True
      have "(subpathin u v p +++ subpathin v w p) t = p (u + (v - u) * (2 * t))"
        using True by (simp add: joinpaths_def subpathin_def algebra_simps)
      also have "\<dots> = p (u + (w - u) * (2 * a * t))"
      proof -
        have wa_eq: "(w - u) * a = v - u"
          unfolding a_def using wu_pos by (simp add: field_simps algebra_simps)
        have scale_eq: "(w - u) * (2 * a * t) = (v - u) * (2 * t)"
        proof -
          have "(w - u) * (2 * a * t) = ((w - u) * a) * (2 * t)"
            by (simp add: algebra_simps)
          also have "\<dots> = (v - u) * (2 * t)"
            using wa_eq by simp
          finally show ?thesis .
        qed
        have arg_eq: "u + (v - u) * (2 * t) = u + (w - u) * (2 * a * t)"
          using scale_eq by linarith
        show ?thesis
          by (subst arg_eq) simp
      qed
      also have "\<dots> = subpathin u w p (?f t)"
        using True by (simp add: subpathin_def algebra_simps)
      finally show ?thesis .
    next
      case False
      have "(subpathin u v p +++ subpathin v w p) t = p (v + (w - v) * (2 * t - 1))"
        using t01 False by (simp add: joinpaths_def subpathin_def algebra_simps)
      also have "\<dots> = p (u + (w - u) * (a + (1 - a) * (2 * t - 1)))"
      proof -
        have one_minus_a: "1 - a = (w - v) / (w - u)"
          unfolding a_def using wu_pos by (simp add: field_simps)
        have ua_eq: "u + (w - u) * a = v"
          unfolding a_def using wu_pos by (simp add: field_simps)
        have tail_eq: "(w - u) * (1 - a) = w - v"
          using one_minus_a wu_pos by (simp add: field_simps)
        have arg_eq: "u + (w - u) * (a + (1 - a) * (2 * t - 1)) = v + (w - v) * (2 * t - 1)"
        proof -
          have "u + (w - u) * (a + (1 - a) * (2 * t - 1)) =
              (u + (w - u) * a) + ((w - u) * (1 - a)) * (2 * t - 1)"
            by (simp add: algebra_simps)
          also have "\<dots> = v + (w - v) * (2 * t - 1)"
            using ua_eq tail_eq by simp
          finally show ?thesis .
        qed
        show ?thesis
          using arg_eq by simp
      qed
      also have "\<dots> = subpathin u w p (?f t)"
        using False by (simp add: subpathin_def algebra_simps)
      finally show ?thesis .
    qed
  qed
qed

lemma subpathin_full [simp]:
  "subpathin 0 1 p = p"
  unfolding subpathin_def by (rule ext) simp

lemma segment_loop_refl:
  assumes puUV: "p u \<in> U \<inter> V"
  shows "homotopic_paths W (segment_loop p u u) (\<lambda>_. x0)"
proof -
  let ?c = "connector (p u)"
  have c_path: "path ?c"
    by (rule connector_path[OF puUV])
  have c_img: "path_image ?c \<subseteq> W"
    using connector_image_subset[OF puUV] by blast
  have rev_c_path: "path (reversepath ?c)"
    using c_path by simp
  have rev_c_img: "path_image (reversepath ?c) \<subseteq> W"
    using c_img by simp
  have hom_rid: "homotopic_paths W (?c +++ (\<lambda>_. p u)) ?c"
    using homotopic_paths_rid_const[OF c_path c_img] connector_finish[OF puUV]
    by (simp add: pathfinish_def)
  have hom_join:
    "homotopic_paths W (((?c +++ (\<lambda>_. p u)) +++ reversepath ?c)) (?c +++ reversepath ?c)"
  proof (rule homotopic_paths_join_right[OF hom_rid rev_c_path rev_c_img])
    show "pathfinish (?c +++ (\<lambda>_. p u)) = pathstart (reversepath ?c)"
      using connector_finish[OF puUV]
      by (simp add: pathstart_def pathfinish_def joinpaths_def reversepath_def)
  qed
  have hom_inv: "homotopic_paths W (?c +++ reversepath ?c) (\<lambda>_. x0)"
    using homotopic_paths_rinv_const[OF c_path c_img] connector_start[OF puUV]
    by simp
  have "homotopic_paths W (segment_loop p u u) (?c +++ reversepath ?c)"
    unfolding segment_loop_def by (simp add: hom_join)
  then show ?thesis
    by (rule homotopic_paths_trans[OF _ hom_inv])
qed

lemma segment_loop_full:
  assumes p_loop: "p \<in> loop_space W x0"
  shows "homotopic_paths W (segment_loop p 0 1) p"
  by (rule segment_loop_base_full_in_set[OF p_loop])

lemma homotopic_paths_cancel_middle:
  assumes r_path: "path r"
    and r_img: "path_image r \<subseteq> S"
    and c_path: "path c"
    and c_img: "path_image c \<subseteq> S"
    and s_path: "path s"
    and s_img: "path_image s \<subseteq> S"
    and rc: "pathfinish r = pathfinish c"
    and cs: "pathstart s = pathfinish c"
  shows "homotopic_paths S ((((r +++ reversepath c) +++ c) +++ s)) (r +++ s)"
proof -
  have revc_path: "path (reversepath c)"
    using c_path by simp
  have revc_img: "path_image (reversepath c) \<subseteq> S"
    using c_img by simp
  have mid_path: "path (reversepath c +++ c)"
    using revc_path c_path by simp
  have mid_img: "path_image (reversepath c +++ c) \<subseteq> S"
    by (rule subset_path_image_join[OF revc_img c_img])
  have hom_cancel0: "homotopic_paths S (reversepath c +++ c) (\<lambda>_. pathfinish c)"
    by (rule homotopic_paths_linv_const[OF c_path c_img])
  have hom_cancel1:
    "homotopic_paths S (((reversepath c +++ c) +++ s)) (((\<lambda>_. pathfinish c) +++ s))"
  proof (rule homotopic_paths_join_right[OF hom_cancel0 s_path s_img])
    show "pathfinish (reversepath c +++ c) = pathstart s"
      using cs by (simp add: pathstart_def pathfinish_def joinpaths_def reversepath_def)
  qed
  have hom_cancel2: "homotopic_paths S (((\<lambda>_. pathfinish c) +++ s)) s"
    using homotopic_paths_lid_const[OF s_path s_img] cs by (simp add: pathstart_def)
  have hom_cancel: "homotopic_paths S (((reversepath c +++ c) +++ s)) s"
    by (rule homotopic_paths_trans[OF hom_cancel1 hom_cancel2])
  have hom_left:
    "homotopic_paths S (r +++ ((reversepath c +++ c) +++ s)) (r +++ s)"
  proof (rule homotopic_paths_join_left[OF hom_cancel r_path r_img])
    show "pathfinish r = pathstart ((reversepath c +++ c) +++ s)"
      using rc by (simp add: pathstart_def pathfinish_def joinpaths_def reversepath_def)
  qed
  have assoc1:
    "homotopic_paths S (((r +++ reversepath c) +++ c)) (r +++ (reversepath c +++ c))"
  proof -
    have "homotopic_paths S (r +++ (reversepath c +++ c)) (((r +++ reversepath c) +++ c))"
      by (rule homotopic_paths_assoc[OF r_path r_img revc_path revc_img c_path c_img]) (use rc in simp_all)
    then show ?thesis
      by (rule homotopic_paths_sym)
  qed
  have assoc1_join:
    "homotopic_paths S ((((r +++ reversepath c) +++ c) +++ s)) (((r +++ (reversepath c +++ c)) +++ s))"
  proof (rule homotopic_paths_join_right[OF assoc1 s_path s_img])
    show "pathfinish ((r +++ reversepath c) +++ c) = pathstart s"
      using rc cs by (simp add: pathstart_def pathfinish_def joinpaths_def reversepath_def)
  qed
  have assoc2:
    "homotopic_paths S (((r +++ (reversepath c +++ c)) +++ s)) (r +++ ((reversepath c +++ c) +++ s))"
  proof -
    have "homotopic_paths S (r +++ ((reversepath c +++ c) +++ s)) (((r +++ (reversepath c +++ c)) +++ s))"
      by (rule homotopic_paths_assoc[OF r_path r_img mid_path mid_img s_path s_img]) (use rc cs in simp_all)
    then show ?thesis
      by (rule homotopic_paths_sym)
  qed
  have "homotopic_paths S ((((r +++ reversepath c) +++ c) +++ s)) (r +++ ((reversepath c +++ c) +++ s))"
    by (rule homotopic_paths_trans[OF assoc1_join assoc2])
  then show ?thesis
    by (rule homotopic_paths_trans[OF _ hom_left])
qed

lemma segment_loop_join:
  assumes p_path: "path p"
    and p_img: "path_image p \<subseteq> W"
    and u01: "u \<in> {0..1}"
    and v01: "v \<in> {0..1}"
    and w01: "w \<in> {0..1}"
    and uv: "u \<le> v"
    and vw: "v \<le> w"
    and puUV: "p u \<in> U \<inter> V"
    and pvUV: "p v \<in> U \<inter> V"
    and pwUV: "p w \<in> U \<inter> V"
  shows "homotopic_paths W (segment_loop p u v +++ segment_loop p v w) (segment_loop p u w)"
proof -
  let ?cu = "connector (p u)"
  let ?cv = "connector (p v)"
  let ?cw = "connector (p w)"
  let ?suv = "subpathin u v p"
  let ?svw = "subpathin v w p"
  let ?suw = "subpathin u w p"
  let ?head = "?cu +++ ?suv"
  let ?tail = "?svw +++ reversepath ?cw"

  have cu_path: "path ?cu"
    by (rule connector_path[OF puUV])
  have cv_path: "path ?cv"
    by (rule connector_path[OF pvUV])
  have cw_path: "path ?cw"
    by (rule connector_path[OF pwUV])
  have cu_img: "path_image ?cu \<subseteq> W"
    using connector_image_subset[OF puUV] by blast
  have cv_img: "path_image ?cv \<subseteq> W"
    using connector_image_subset[OF pvUV] by blast
  have cw_img: "path_image ?cw \<subseteq> W"
    using connector_image_subset[OF pwUV] by blast

  have suv_path: "path ?suv"
    by (rule path_subpathin[OF p_path u01 v01])
  have svw_path: "path ?svw"
    by (rule path_subpathin[OF p_path v01 w01])
  have suw_path: "path ?suw"
    by (rule path_subpathin[OF p_path u01 w01])
  have suv_img: "path_image ?suv \<subseteq> W"
    using p_img path_image_subpathin_subset[OF u01 v01, of p] by blast
  have svw_img: "path_image ?svw \<subseteq> W"
    using p_img path_image_subpathin_subset[OF v01 w01, of p] by blast
  have suw_img: "path_image ?suw \<subseteq> W"
    using p_img path_image_subpathin_subset[OF u01 w01, of p] by blast
  have suv_start: "pathstart ?suv = p u"
    by (simp add: pathstart_def subpathin_def)
  have svw_start: "pathstart ?svw = p v"
    by (simp add: pathstart_def subpathin_def)
  have svw_finish: "pathfinish ?svw = p w"
    by (simp add: pathfinish_def subpathin_def)
  have rev_cw_path: "path (reversepath ?cw)"
    using cw_path by simp
  have rev_cw_img: "path_image (reversepath ?cw) \<subseteq> W"
    using cw_img by simp
  have rev_cw_start: "pathstart (reversepath ?cw) = p w"
    using connector_finish[OF pwUV] by simp

  have head_path: "path ?head"
    using cu_path suv_path connector_finish[OF puUV] suv_start by simp
  have head_img: "path_image ?head \<subseteq> W"
    by (rule subset_path_image_join[OF cu_img suv_img])
  have tail_path: "path ?tail"
    using svw_path rev_cw_path svw_finish rev_cw_start by simp
  have tail_img: "path_image ?tail \<subseteq> W"
    by (rule subset_path_image_join[OF svw_img rev_cw_img])

  have seg_uv_loop: "segment_loop p u v \<in> loop_space W x0"
  proof (rule segment_loop_in_W[OF p_path p_img u01 v01 puUV pvUV])
    show "subpathin u v p ` {0..1} \<subseteq> W"
      using suv_img by (simp add: path_image_def)
  qed
  then have seg_uv_path: "path (segment_loop p u v)" and seg_uv_img: "path_image (segment_loop p u v) \<subseteq> W"
    unfolding loop_space_def by auto

  have seg_vw_assoc:
    "homotopic_paths W (segment_loop p v w) (?cv +++ ?tail)"
  proof -
    have "homotopic_paths W (?cv +++ (?svw +++ reversepath ?cw)) ((?cv +++ ?svw) +++ reversepath ?cw)"
      by (rule homotopic_paths_assoc[OF cv_path cv_img svw_path svw_img rev_cw_path rev_cw_img])
         (use connector_finish[OF pvUV] svw_start svw_finish rev_cw_start in simp_all)
    then show ?thesis
      unfolding segment_loop_def by (rule homotopic_paths_sym)
  qed

  have seg_join_start: "pathfinish (segment_loop p u v) = pathstart (segment_loop p v w)"
    using pvUV by (simp add: segment_loop_def connector_start connector_finish)
  have step1:
    "homotopic_paths W (segment_loop p u v +++ segment_loop p v w) (segment_loop p u v +++ (?cv +++ ?tail))"
    by (rule homotopic_paths_join_left[OF seg_vw_assoc seg_uv_path seg_uv_img seg_join_start])

  have seg_cv_start: "pathfinish (segment_loop p u v) = pathstart ?cv"
    using pvUV by (simp add: segment_loop_def connector_start connector_finish)
  have cv_tail_start: "pathfinish ?cv = pathstart ?tail"
    using connector_finish[OF pvUV] svw_start by simp
  have step2:
    "homotopic_paths W (segment_loop p u v +++ (?cv +++ ?tail)) ((segment_loop p u v +++ ?cv) +++ ?tail)"
    by (rule homotopic_paths_assoc[OF seg_uv_path seg_uv_img cv_path cv_img tail_path tail_img seg_cv_start cv_tail_start])

  have subpath_uv_finish: "pathfinish (subpathin u v p) = p v"
    by (simp add: subpathin_def pathfinish_def)
  have head_finish_pv: "pathfinish ?head = p v"
    using connector_finish[OF puUV] subpath_uv_finish
    by (simp add: segment_loop_def connector_start connector_finish)
  have head_cv_finish: "pathfinish ?head = pathfinish ?cv"
    using head_finish_pv connector_finish[OF pvUV] by simp
  have tail_cv_start: "pathstart ?tail = pathfinish ?cv"
    using connector_finish[OF pvUV] svw_start by simp
  have step3_raw:
    "homotopic_paths W ((((?head +++ reversepath ?cv) +++ ?cv) +++ ?tail)) (?head +++ ?tail)"
    by (rule homotopic_paths_cancel_middle[OF head_path head_img cv_path cv_img tail_path tail_img head_cv_finish tail_cv_start])
  have step3:
    "homotopic_paths W ((segment_loop p u v +++ ?cv) +++ ?tail) (?head +++ ?tail)"
    unfolding segment_loop_def using step3_raw by simp

  have suv_finish: "pathfinish ?suv = p v"
    by (simp add: subpathin_def pathfinish_def)
  have svw_start_eq: "pathstart ?svw = p v"
    by (simp add: subpathin_def pathstart_def)
  have svw_finish: "pathfinish ?svw = p w"
    by (simp add: subpathin_def pathfinish_def)
  have head_svw_start: "pathfinish ?head = pathstart ?svw"
    using connector_finish[OF puUV] suv_finish svw_start_eq
    by (simp add: connector_start connector_finish)
  have svw_revcw_start: "pathfinish ?svw = pathstart (reversepath ?cw)"
    using connector_finish[OF pwUV] svw_finish by simp
  have step4a:
    "homotopic_paths W (?head +++ ?tail) (((?cu +++ ?suv) +++ ?svw) +++ reversepath ?cw)"
    by (rule homotopic_paths_assoc[OF head_path head_img svw_path svw_img rev_cw_path rev_cw_img head_svw_start svw_revcw_start])
  have step4b_inner:
    "homotopic_paths W (((?cu +++ ?suv) +++ ?svw)) (?cu +++ (?suv +++ ?svw))"
  proof -
    have cu_suv_start: "pathfinish ?cu = pathstart ?suv"
      using connector_finish[OF puUV] by (simp add: subpathin_def pathstart_def)
    have suv_svw_start: "pathfinish ?suv = pathstart ?svw"
      by (simp add: subpathin_def pathstart_def pathfinish_def)
    have "homotopic_paths W (?cu +++ (?suv +++ ?svw)) (((?cu +++ ?suv) +++ ?svw))"
      by (rule homotopic_paths_assoc[OF cu_path cu_img suv_path suv_img svw_path svw_img cu_suv_start suv_svw_start])
    then show ?thesis
      by (rule homotopic_paths_sym)
  qed
  have step4b:
    "homotopic_paths W ((((?cu +++ ?suv) +++ ?svw) +++ reversepath ?cw))
      (((?cu +++ (?suv +++ ?svw)) +++ reversepath ?cw))"
  proof -
    have cusuv_svw_finish: "pathfinish (((?cu +++ ?suv) +++ ?svw)) = p w"
      using connector_finish[OF puUV] suv_finish svw_finish
      by (simp add: connector_start connector_finish)
    have cusuv_svw_revcw_start: "pathfinish (((?cu +++ ?suv) +++ ?svw)) = pathstart (reversepath ?cw)"
      using cusuv_svw_finish connector_finish[OF pwUV] by simp
    show ?thesis
      by (rule homotopic_paths_join_right[OF step4b_inner rev_cw_path rev_cw_img cusuv_svw_revcw_start])
  qed
  have step4:
    "homotopic_paths W (?head +++ ?tail) (((?cu +++ (?suv +++ ?svw)) +++ reversepath ?cw))"
    by (rule homotopic_paths_trans[OF step4a step4b])

  have step5_inner0: "homotopic_paths W (?suv +++ ?svw) ?suw"
    by (rule homotopic_paths_join_subpathin[OF p_path p_img u01 v01 w01 uv vw])
  have step5_inner1:
    "homotopic_paths W (?cu +++ (?suv +++ ?svw)) (?cu +++ ?suw)"
  proof -
    have cu_suvsvw_start: "pathfinish ?cu = pathstart (?suv +++ ?svw)"
    proof -
      have cu_finish: "pathfinish ?cu = p u"
        using connector_finish[OF puUV] by simp
      have suvsvw_start: "pathstart (?suv +++ ?svw) = p u"
        by (simp add: joinpaths_def subpathin_def pathstart_def)
      show ?thesis
        using cu_finish suvsvw_start by simp
    qed
    show ?thesis
      by (rule homotopic_paths_join_left[OF step5_inner0 cu_path cu_img cu_suvsvw_start])
  qed
  have step5:
    "homotopic_paths W (((?cu +++ (?suv +++ ?svw)) +++ reversepath ?cw)) (segment_loop p u w)"
  proof -
    have cu_suvw_finish: "pathfinish (?cu +++ (?suv +++ ?svw)) = p w"
      using connector_finish[OF puUV] suv_finish svw_finish
      by (simp add: connector_start connector_finish)
    have cu_suvw_revcw_start: "pathfinish (?cu +++ (?suv +++ ?svw)) = pathstart (reversepath ?cw)"
      using cu_suvw_finish connector_finish[OF pwUV] by simp
    have step5_raw:
      "homotopic_paths W (((?cu +++ (?suv +++ ?svw)) +++ reversepath ?cw))
        (((?cu +++ ?suw) +++ reversepath ?cw))"
    proof (rule homotopic_paths_join_right[OF step5_inner1 rev_cw_path rev_cw_img])
      show "pathfinish (?cu +++ (?suv +++ ?svw)) = pathstart (reversepath ?cw)"
        by (rule cu_suvw_revcw_start)
    qed
    have step5_assoc:
      "homotopic_paths W (((?cu +++ ?suw) +++ reversepath ?cw))
        (?cu +++ (?suw +++ reversepath ?cw))"
    proof -
      have cu_suw_start: "pathfinish ?cu = pathstart ?suw"
        using connector_finish[OF puUV] by (simp add: subpathin_def pathstart_def)
      have suw_revcw_start: "pathfinish ?suw = pathstart (reversepath ?cw)"
        using connector_finish[OF pwUV] by (simp add: subpathin_def pathfinish_def)
      have "homotopic_paths W (?cu +++ (?suw +++ reversepath ?cw))
          (((?cu +++ ?suw) +++ reversepath ?cw))"
        by (rule homotopic_paths_assoc[OF cu_path cu_img suw_path suw_img rev_cw_path rev_cw_img cu_suw_start suw_revcw_start])
      then show ?thesis
        by (rule homotopic_paths_sym)
    qed
    have step5_assoc':
      "homotopic_paths W (((?cu +++ ?suw) +++ reversepath ?cw))
        (connector (p u) +++ (subpathin u w p +++ reversepath (connector (p w))))"
      using step5_assoc by simp
    have step5_final:
      "homotopic_paths W (((?cu +++ (?suv +++ ?svw)) +++ reversepath ?cw))
        (connector (p u) +++ (subpathin u w p +++ reversepath (connector (p w))))"
      by (rule homotopic_paths_trans[OF step5_raw step5_assoc'])
    show ?thesis
      unfolding segment_loop_def
      by (rule step5_raw)
  qed

  have "homotopic_paths W (segment_loop p u v +++ segment_loop p v w) ((segment_loop p u v +++ ?cv) +++ ?tail)"
    by (rule homotopic_paths_trans[OF step1 step2])
  then have "homotopic_paths W (segment_loop p u v +++ segment_loop p v w) (?head +++ ?tail)"
    by (rule homotopic_paths_trans[OF _ step3])
  then have "homotopic_paths W (segment_loop p u v +++ segment_loop p v w)
      (((?cu +++ (?suv +++ ?svw)) +++ reversepath ?cw))"
    by (rule homotopic_paths_trans[OF _ step4])
  then show ?thesis
    by (rule homotopic_paths_trans[OF _ step5])
qed

lemma segment_loop_join_in_set:
  assumes p_path: "path p"
    and p_imgS: "path_image p \<subseteq> S"
    and SW: "S \<subseteq> W"
    and UVS: "U \<inter> V \<subseteq> S"
    and u01: "u \<in> {0..1}"
    and v01: "v \<in> {0..1}"
    and w01: "w \<in> {0..1}"
    and uv: "u \<le> v"
    and vw: "v \<le> w"
    and puUV: "p u \<in> U \<inter> V"
    and pvUV: "p v \<in> U \<inter> V"
    and pwUV: "p w \<in> U \<inter> V"
  shows "homotopic_paths S (segment_loop p u v +++ segment_loop p v w) (segment_loop p u w)"
proof -
  let ?cu = "connector (p u)"
  let ?cv = "connector (p v)"
  let ?cw = "connector (p w)"
  let ?suv = "subpathin u v p"
  let ?svw = "subpathin v w p"
  let ?suw = "subpathin u w p"
  let ?head = "?cu +++ ?suv"
  let ?tail = "?svw +++ reversepath ?cw"

  have p_imgW: "path_image p \<subseteq> W"
    using p_imgS SW by blast

  have cu_path: "path ?cu"
    by (rule connector_path[OF puUV])
  have cv_path: "path ?cv"
    by (rule connector_path[OF pvUV])
  have cw_path: "path ?cw"
    by (rule connector_path[OF pwUV])
  have cu_img: "path_image ?cu \<subseteq> S"
    using connector_image_subset[OF puUV] UVS by blast
  have cv_img: "path_image ?cv \<subseteq> S"
    using connector_image_subset[OF pvUV] UVS by blast
  have cw_img: "path_image ?cw \<subseteq> S"
    using connector_image_subset[OF pwUV] UVS by blast

  have suv_path: "path ?suv"
    by (rule path_subpathin[OF p_path u01 v01])
  have svw_path: "path ?svw"
    by (rule path_subpathin[OF p_path v01 w01])
  have suw_path: "path ?suw"
    by (rule path_subpathin[OF p_path u01 w01])
  have suv_img: "path_image ?suv \<subseteq> S"
    using p_imgS path_image_subpathin_subset[OF u01 v01, of p] by blast
  have svw_img: "path_image ?svw \<subseteq> S"
    using p_imgS path_image_subpathin_subset[OF v01 w01, of p] by blast
  have suw_img: "path_image ?suw \<subseteq> S"
    using p_imgS path_image_subpathin_subset[OF u01 w01, of p] by blast
  have suv_start: "pathstart ?suv = p u"
    by (simp add: pathstart_def subpathin_def)
  have svw_start: "pathstart ?svw = p v"
    by (simp add: pathstart_def subpathin_def)
  have svw_finish: "pathfinish ?svw = p w"
    by (simp add: pathfinish_def subpathin_def)
  have rev_cw_path: "path (reversepath ?cw)"
    using cw_path by simp
  have rev_cw_img: "path_image (reversepath ?cw) \<subseteq> S"
    using cw_img by simp
  have rev_cw_start: "pathstart (reversepath ?cw) = p w"
    using connector_finish[OF pwUV] by simp

  have head_path: "path ?head"
    using cu_path suv_path connector_finish[OF puUV] suv_start by simp
  have head_img: "path_image ?head \<subseteq> S"
    by (rule subset_path_image_join[OF cu_img suv_img])
  have tail_path: "path ?tail"
    using svw_path rev_cw_path svw_finish rev_cw_start by simp
  have tail_img: "path_image ?tail \<subseteq> S"
    by (rule subset_path_image_join[OF svw_img rev_cw_img])

  have seg_uv_loop: "segment_loop p u v \<in> loop_space S x0"
  proof (rule segment_loop_in_set[where S = S])
    show "path p"
      by (rule p_path)
    show "path_image p \<subseteq> W"
      by (rule p_imgW)
    show "u \<in> {0..1}" "v \<in> {0..1}"
      by (rule u01, rule v01)+
    show "p u \<in> U \<inter> V" "p v \<in> U \<inter> V"
      by (rule puUV, rule pvUV)+
    show "path_image (connector (p u)) \<subseteq> S"
      by (rule cu_img)
    show "path_image (connector (p v)) \<subseteq> S"
      by (rule cv_img)
    show "subpathin u v p ` {0..1} \<subseteq> S"
      using suv_img by (simp add: path_image_def)
    show "x0 \<in> S"
      using x0_in_UV UVS by blast
  qed
  then have seg_uv_path: "path (segment_loop p u v)"
    and seg_uv_img: "path_image (segment_loop p u v) \<subseteq> S"
    unfolding loop_space_def by auto

  have seg_vw_assoc:
    "homotopic_paths S (segment_loop p v w) (?cv +++ ?tail)"
  proof -
    have "homotopic_paths S (?cv +++ (?svw +++ reversepath ?cw)) ((?cv +++ ?svw) +++ reversepath ?cw)"
      by (rule homotopic_paths_assoc[OF cv_path cv_img svw_path svw_img rev_cw_path rev_cw_img])
         (use connector_finish[OF pvUV] svw_start svw_finish rev_cw_start in simp_all)
    then show ?thesis
      unfolding segment_loop_def by (rule homotopic_paths_sym)
  qed

  have seg_join_start: "pathfinish (segment_loop p u v) = pathstart (segment_loop p v w)"
    using pvUV by (simp add: segment_loop_def connector_start connector_finish)
  have step1:
    "homotopic_paths S (segment_loop p u v +++ segment_loop p v w) (segment_loop p u v +++ (?cv +++ ?tail))"
    by (rule homotopic_paths_join_left[OF seg_vw_assoc seg_uv_path seg_uv_img seg_join_start])

  have seg_cv_start: "pathfinish (segment_loop p u v) = pathstart ?cv"
    using pvUV by (simp add: segment_loop_def connector_start connector_finish)
  have cv_tail_start: "pathfinish ?cv = pathstart ?tail"
    using connector_finish[OF pvUV] svw_start by simp
  have step2:
    "homotopic_paths S (segment_loop p u v +++ (?cv +++ ?tail)) ((segment_loop p u v +++ ?cv) +++ ?tail)"
    by (rule homotopic_paths_assoc[OF seg_uv_path seg_uv_img cv_path cv_img tail_path tail_img seg_cv_start cv_tail_start])

  have subpath_uv_finish: "pathfinish (subpathin u v p) = p v"
    by (simp add: subpathin_def pathfinish_def)
  have head_finish_pv: "pathfinish ?head = p v"
    using connector_finish[OF puUV] subpath_uv_finish
    by (simp add: segment_loop_def connector_start connector_finish)
  have head_cv_finish: "pathfinish ?head = pathfinish ?cv"
    using head_finish_pv connector_finish[OF pvUV] by simp
  have tail_cv_start: "pathstart ?tail = pathfinish ?cv"
    using connector_finish[OF pvUV] svw_start by simp
  have step3_raw:
    "homotopic_paths S ((((?head +++ reversepath ?cv) +++ ?cv) +++ ?tail)) (?head +++ ?tail)"
    by (rule homotopic_paths_cancel_middle[OF head_path head_img cv_path cv_img tail_path tail_img head_cv_finish tail_cv_start])
  have step3:
    "homotopic_paths S ((segment_loop p u v +++ ?cv) +++ ?tail) (?head +++ ?tail)"
    unfolding segment_loop_def using step3_raw by simp

  have suv_finish: "pathfinish ?suv = p v"
    by (simp add: subpathin_def pathfinish_def)
  have svw_start_eq: "pathstart ?svw = p v"
    by (simp add: subpathin_def pathstart_def)
  have svw_finish: "pathfinish ?svw = p w"
    by (simp add: subpathin_def pathfinish_def)
  have head_svw_start: "pathfinish ?head = pathstart ?svw"
    using connector_finish[OF puUV] suv_finish svw_start_eq
    by (simp add: connector_start connector_finish)
  have svw_revcw_start: "pathfinish ?svw = pathstart (reversepath ?cw)"
    using connector_finish[OF pwUV] svw_finish by simp
  have step4a:
    "homotopic_paths S (?head +++ ?tail) (((?cu +++ ?suv) +++ ?svw) +++ reversepath ?cw)"
    by (rule homotopic_paths_assoc[OF head_path head_img svw_path svw_img rev_cw_path rev_cw_img head_svw_start svw_revcw_start])
  have step4b_inner:
    "homotopic_paths S (((?cu +++ ?suv) +++ ?svw)) (?cu +++ (?suv +++ ?svw))"
  proof -
    have cu_suv_start: "pathfinish ?cu = pathstart ?suv"
      using connector_finish[OF puUV] by (simp add: subpathin_def pathstart_def)
    have suv_svw_start: "pathfinish ?suv = pathstart ?svw"
      by (simp add: subpathin_def pathstart_def pathfinish_def)
    have "homotopic_paths S (?cu +++ (?suv +++ ?svw)) (((?cu +++ ?suv) +++ ?svw))"
      by (rule homotopic_paths_assoc[OF cu_path cu_img suv_path suv_img svw_path svw_img cu_suv_start suv_svw_start])
    then show ?thesis
      by (rule homotopic_paths_sym)
  qed
  have step4b:
    "homotopic_paths S ((((?cu +++ ?suv) +++ ?svw) +++ reversepath ?cw))
      (((?cu +++ (?suv +++ ?svw)) +++ reversepath ?cw))"
  proof -
    have cusuv_svw_finish: "pathfinish (((?cu +++ ?suv) +++ ?svw)) = p w"
      using connector_finish[OF puUV] suv_finish svw_finish
      by (simp add: connector_start connector_finish)
    have cusuv_svw_revcw_start: "pathfinish (((?cu +++ ?suv) +++ ?svw)) = pathstart (reversepath ?cw)"
      using cusuv_svw_finish connector_finish[OF pwUV] by simp
    show ?thesis
      by (rule homotopic_paths_join_right[OF step4b_inner rev_cw_path rev_cw_img cusuv_svw_revcw_start])
  qed
  have step4:
    "homotopic_paths S (?head +++ ?tail) (((?cu +++ (?suv +++ ?svw)) +++ reversepath ?cw))"
    by (rule homotopic_paths_trans[OF step4a step4b])

  have step5_inner0: "homotopic_paths S (?suv +++ ?svw) ?suw"
    by (rule homotopic_paths_join_subpathin[OF p_path p_imgS u01 v01 w01 uv vw])
  have step5_inner1:
    "homotopic_paths S (?cu +++ (?suv +++ ?svw)) (?cu +++ ?suw)"
  proof -
    have cu_suvsvw_start: "pathfinish ?cu = pathstart (?suv +++ ?svw)"
    proof -
      have cu_finish: "pathfinish ?cu = p u"
        using connector_finish[OF puUV] by simp
      have suvsvw_start: "pathstart (?suv +++ ?svw) = p u"
        by (simp add: joinpaths_def subpathin_def pathstart_def)
      show ?thesis
        using cu_finish suvsvw_start by simp
    qed
    show ?thesis
      by (rule homotopic_paths_join_left[OF step5_inner0 cu_path cu_img cu_suvsvw_start])
  qed
  have step5:
    "homotopic_paths S (((?cu +++ (?suv +++ ?svw)) +++ reversepath ?cw)) (segment_loop p u w)"
  proof -
    have cu_suvw_finish: "pathfinish (?cu +++ (?suv +++ ?svw)) = p w"
      using connector_finish[OF puUV] suv_finish svw_finish
      by (simp add: connector_start connector_finish)
    have cu_suvw_revcw_start: "pathfinish (?cu +++ (?suv +++ ?svw)) = pathstart (reversepath ?cw)"
      using cu_suvw_finish connector_finish[OF pwUV] by simp
    have step5_raw:
      "homotopic_paths S (((?cu +++ (?suv +++ ?svw)) +++ reversepath ?cw))
        (((?cu +++ ?suw) +++ reversepath ?cw))"
    proof (rule homotopic_paths_join_right[OF step5_inner1 rev_cw_path rev_cw_img])
      show "pathfinish (?cu +++ (?suv +++ ?svw)) = pathstart (reversepath ?cw)"
        by (rule cu_suvw_revcw_start)
    qed
    have step5_assoc:
      "homotopic_paths S (((?cu +++ ?suw) +++ reversepath ?cw))
        (?cu +++ (?suw +++ reversepath ?cw))"
    proof -
      have cu_suw_start: "pathfinish ?cu = pathstart ?suw"
        using connector_finish[OF puUV] by (simp add: subpathin_def pathstart_def)
      have suw_revcw_start: "pathfinish ?suw = pathstart (reversepath ?cw)"
        using connector_finish[OF pwUV] by (simp add: subpathin_def pathfinish_def)
      have "homotopic_paths S (?cu +++ (?suw +++ reversepath ?cw))
          (((?cu +++ ?suw) +++ reversepath ?cw))"
        by (rule homotopic_paths_assoc[OF cu_path cu_img suw_path suw_img rev_cw_path rev_cw_img cu_suw_start suw_revcw_start])
      then show ?thesis
        by (rule homotopic_paths_sym)
    qed
    have step5_assoc':
      "homotopic_paths S (((?cu +++ ?suw) +++ reversepath ?cw))
        (connector (p u) +++ (subpathin u w p +++ reversepath (connector (p w))))"
      using step5_assoc by simp
    have step5_final:
      "homotopic_paths S (((?cu +++ (?suv +++ ?svw)) +++ reversepath ?cw))
        (connector (p u) +++ (subpathin u w p +++ reversepath (connector (p w))))"
      by (rule homotopic_paths_trans[OF step5_raw step5_assoc'])
    show ?thesis
      unfolding segment_loop_def
      by (rule step5_raw)
  qed

  have "homotopic_paths S (segment_loop p u v +++ segment_loop p v w) ((segment_loop p u v +++ ?cv) +++ ?tail)"
    by (rule homotopic_paths_trans[OF step1 step2])
  then have "homotopic_paths S (segment_loop p u v +++ segment_loop p v w) (?head +++ ?tail)"
    by (rule homotopic_paths_trans[OF _ step3])
  then have "homotopic_paths S (segment_loop p u v +++ segment_loop p v w)
      (((?cu +++ (?suv +++ ?svw)) +++ reversepath ?cw))"
    by (rule homotopic_paths_trans[OF _ step4])
  then show ?thesis
    by (rule homotopic_paths_trans[OF _ step5])
qed

lemma partition_loop_nil [simp]:
  "partition_loop p [] = (\<lambda>_. x0)"
  by simp

lemma partition_loop_singleton [simp]:
  "partition_loop p [t] = (\<lambda>_. x0)"
  by simp

lemma svk_partition_partition_loop_homotopic_segment_loop:
  assumes p_loop: "p \<in> loop_space W x0"
    and part: "svk_partition p (t # ts) bs"
  shows "homotopic_paths W (partition_loop p (t # ts)) (segment_loop p t 1)"
  using part
proof (induction ts arbitrary: t bs)
  case Nil
  have t1: "t = 1"
    using svk_partition_last_eq_one[OF Nil.prems] by simp
  have ptUV: "p t \<in> U \<inter> V"
    by (rule svk_partition_head_props(2)[OF Nil.prems])
  have "homotopic_paths W (segment_loop p t 1) (\<lambda>_. x0)"
    using t1 ptUV by (simp add: segment_loop_refl)
  then show ?case
    by (simp add: homotopic_paths_sym)
next
  case (Cons u us)
  from p_loop have p_path: "path p" and p_img: "path_image p \<subseteq> W"
    unfolding loop_space_def by auto
  obtain b bs' where bs: "bs = b # bs'"
    using Cons.prems by (cases bs) auto
  have tail: "svk_partition p (u # us) bs'"
    using Cons.prems bs by simp
  have tail_hom:
    "homotopic_paths W (partition_loop p (u # us)) (segment_loop p u 1)"
    by (rule Cons.IH[OF tail])
  have t01: "t \<in> {0..1}" and ptUV: "p t \<in> U \<inter> V"
    using Cons.prems bs by simp_all
  have u01: "u \<in> {0..1}" and tu: "t < u"
    using Cons.prems bs by simp_all
  have puUV: "p u \<in> U \<inter> V"
    using Cons.prems bs svk_partition_next_in_intersection[of p t u us b bs'] by simp
  have seg_in:
    "subpathin t u p ` {0..1} \<subseteq> W"
    by (cases b) (use Cons.prems bs in auto)
  have oneUV: "p 1 \<in> U \<inter> V"
    using svk_partition_last_in_intersection[OF tail] svk_partition_last_eq_one[OF tail] by simp
  have seg_tu_loop: "segment_loop p t u \<in> loop_space W x0"
    by (rule segment_loop_in_W[OF p_path p_img t01 u01 ptUV puUV seg_in])
  then have seg_tu_path: "path (segment_loop p t u)"
    and seg_tu_img: "path_image (segment_loop p t u) \<subseteq> W"
    unfolding loop_space_def by auto
  have tail_loop: "partition_loop p (u # us) \<in> loop_space W x0"
    by (rule svk_partition_partition_loop_in_W[OF p_loop tail])
  have join_hom:
    "homotopic_paths W (segment_loop p t u +++ partition_loop p (u # us))
      (segment_loop p t u +++ segment_loop p u 1)"
  proof (rule homotopic_paths_join_left[OF tail_hom seg_tu_path seg_tu_img])
    show "pathfinish (segment_loop p t u) = pathstart (partition_loop p (u # us))"
      using seg_tu_loop tail_loop unfolding loop_space_def by simp
  qed
  have step1:
    "homotopic_paths W (partition_loop p (t # u # us)) (segment_loop p t u +++ segment_loop p u 1)"
    using join_hom by simp
  have step2:
    "homotopic_paths W (segment_loop p t u +++ segment_loop p u 1) (segment_loop p t 1)"
    by (rule segment_loop_join[OF p_path p_img t01 u01]) (use u01 tu oneUV ptUV puUV in auto)
  show ?case
    by (rule homotopic_paths_trans[OF step1 step2])
qed

lemma valid_partition_partition_loop_homotopic_segment_loop:
  assumes p_loop: "p \<in> loop_space W x0"
    and part: "valid_partition p ts bs"
  shows "homotopic_paths W (partition_loop p ts) (segment_loop p 0 1)"
proof -
  obtain t ts' where ts: "ts = t # ts'"
    using valid_partition_hd(1)[OF part] by (cases ts) auto
  have valid_ts: "valid_partition p (t # ts') bs"
    using part unfolding ts by simp
  have t0: "t = 0"
    by (rule valid_partition_cases(1)[OF valid_ts])
  have svk: "svk_partition p (t # ts') bs"
    by (rule valid_partition_cases(2)[OF valid_ts])
  have "homotopic_paths W (partition_loop p (t # ts')) (segment_loop p t 1)"
    by (rule svk_partition_partition_loop_homotopic_segment_loop[OF p_loop svk])
  then show ?thesis
    using ts t0 by simp
qed

lemma valid_partition_partition_loop_homotopic:
  assumes p_loop: "p \<in> loop_space W x0"
    and part: "valid_partition p ts bs"
  shows "homotopic_paths W (partition_loop p ts) p"
proof -
  have step1: "homotopic_paths W (partition_loop p ts) (segment_loop p 0 1)"
    by (rule valid_partition_partition_loop_homotopic_segment_loop[OF p_loop part])
  have step2: "homotopic_paths W (segment_loop p 0 1) p"
    by (rule segment_loop_full[OF p_loop])
  show ?thesis
    by (rule homotopic_paths_trans[OF step1 step2])
qed

lemma valid_partition_partition_loop_eq:
  assumes p_loop: "p \<in> loop_space W x0"
    and part: "valid_partition p ts bs"
  shows "loop_class W x0 (partition_loop p ts) = loop_class W x0 p"
proof -
  have part_loop: "partition_loop p ts \<in> loop_space W x0"
    by (rule valid_partition_partition_loop_in_W[OF p_loop part])
  have hom: "homotopic_paths W (partition_loop p ts) p"
    by (rule valid_partition_partition_loop_homotopic[OF p_loop part])
  show ?thesis
    by (rule loop_class_eqI[OF part_loop p_loop hom])
qed

lemma valid_partition_decode_partition_word_eq_loop_class:
  assumes p_loop: "p \<in> loop_space W x0"
    and part: "valid_partition p ts bs"
  shows "svk_decode (partition_word p ts bs) = loop_class W x0 p"
  using valid_partition_decode_partition_word[OF p_loop part]
    valid_partition_partition_loop_eq[OF p_loop part]
  by simp

lemma subpathin_image_subset_left:
  assumes t01: "t \<in> {0..1}"
    and u01: "u \<in> {0..1}"
    and v01: "v \<in> {0..1}"
    and tu: "t \<le> u"
    and uv: "u \<le> v"
  shows "subpathin t u p ` {0..1} \<subseteq> subpathin t v p ` {0..1}"
proof -
  have "closed_segment t u \<subseteq> closed_segment t v"
    using t01 u01 v01 tu uv by (auto simp: closed_segment_eq_real_ivl)
  then show ?thesis
    by (auto simp: subpathin_image)
qed

lemma subpathin_image_subset_right:
  assumes t01: "t \<in> {0..1}"
    and u01: "u \<in> {0..1}"
    and v01: "v \<in> {0..1}"
    and tu: "t \<le> u"
    and uv: "u \<le> v"
  shows "subpathin u v p ` {0..1} \<subseteq> subpathin t v p ` {0..1}"
proof -
  have "closed_segment u v \<subseteq> closed_segment t v"
    using t01 u01 v01 tu uv by (auto simp: closed_segment_eq_real_ivl)
  then show ?thesis
    by (auto simp: subpathin_image)
qed

lemma subpathin_subpathin:
  "subpathin a b (subpathin u v p) =
    subpathin (((v - u) * a) + u) (((v - u) * b) + u) p"
  unfolding subpathin_def by (rule ext) (simp add: algebra_simps)

lemma segment_loop_subpathin:
  "segment_loop (subpathin u v p) a b =
    segment_loop p (((v - u) * a) + u) (((v - u) * b) + u)"
  unfolding segment_loop_def subpathin_subpathin subpathin_def
  by (rule ext) (simp add: algebra_simps)

lemma segment_loop_mult_eq_left:
  assumes p_path: "path p"
    and p_imgW: "path_image p \<subseteq> W"
    and t01: "t \<in> {0..1}"
    and u01: "u \<in> {0..1}"
    and v01: "v \<in> {0..1}"
    and tu: "t < u"
    and uv: "u < v"
    and ptUV: "p t \<in> U \<inter> V"
    and puUV: "p u \<in> U \<inter> V"
    and pvUV: "p v \<in> U \<inter> V"
    and seg_tvU: "subpathin t v p ` {0..1} \<subseteq> U"
  shows "mult1 (loop_class U x0 (segment_loop p t u))
      (loop_class U x0 (segment_loop p u v)) =
    loop_class U x0 (segment_loop p t v)"
proof -
  define q where "q = subpathin t v p"
  define a where "a = (u - t) / (v - t)"

  have tv: "t < v"
    using tu uv by linarith
  have a01: "a \<in> {0..1}"
    unfolding a_def using tu uv tv by (auto simp: field_simps)
  have q_path: "path q"
    unfolding q_def by (rule path_subpathin[OF p_path t01 v01])
  have q_imgU: "path_image q \<subseteq> U"
    unfolding q_def using seg_tvU by (simp add: path_image_def)
  have q0UV: "q 0 \<in> U \<inter> V"
    unfolding q_def using ptUV by (simp add: subpathin_def)
  have qaUV: "q a \<in> U \<inter> V"
  proof -
    have qa_eq: "q a = p u"
    proof -
      have ta_eq: "t + (v - t) * a = u"
        unfolding a_def using tv by (simp add: field_simps)
      show ?thesis
        unfolding q_def subpathin_def using ta_eq by (simp add: algebra_simps)
    qed
    then show ?thesis
      using puUV by simp
  qed
  have q1UV: "q 1 \<in> U \<inter> V"
    unfolding q_def using pvUV by (simp add: subpathin_def)
  have join_hom_q:
    "homotopic_paths U (segment_loop q 0 a +++ segment_loop q a 1) (segment_loop q 0 1)"
    by (rule segment_loop_join_in_set[OF q_path q_imgU]) (use a01 q0UV qaUV q1UV in auto)

  have seg_tu_eq: "segment_loop q 0 a = segment_loop p t u"
  proof -
    have ta_eq: "((v - t) * a) + t = u"
      unfolding a_def using tv by (simp add: field_simps algebra_simps)
    show ?thesis
      unfolding q_def using ta_eq by (simp add: segment_loop_subpathin)
  qed
  have seg_uv_eq: "segment_loop q a 1 = segment_loop p u v"
  proof -
    have ta_eq: "((v - t) * a) + t = u"
      unfolding a_def using tv by (simp add: field_simps algebra_simps)
    show ?thesis
      unfolding q_def using ta_eq by (simp add: segment_loop_subpathin)
  qed
  have seg_tv_eq: "segment_loop q 0 1 = segment_loop p t v"
    unfolding q_def by (simp add: segment_loop_subpathin)

  have seg_tuU: "subpathin t u p ` {0..1} \<subseteq> U"
    by (rule order_trans[OF subpathin_image_subset_left[OF t01 u01 v01]]) (use tu uv seg_tvU in auto)
  have seg_uvU: "subpathin u v p ` {0..1} \<subseteq> U"
    by (rule order_trans[OF subpathin_image_subset_right[OF t01 u01 v01]]) (use tu uv seg_tvU in auto)

  have loop_tu: "segment_loop p t u \<in> loop_space U x0"
    by (rule segment_loop_in_U[OF p_path p_imgW t01 u01 ptUV puUV seg_tuU])
  have loop_uv: "segment_loop p u v \<in> loop_space U x0"
    by (rule segment_loop_in_U[OF p_path p_imgW u01 v01 puUV pvUV seg_uvU])
  have loop_tv: "segment_loop p t v \<in> loop_space U x0"
    by (rule segment_loop_in_U[OF p_path p_imgW t01 v01 ptUV pvUV seg_tvU])

  have class_tu_in: "loop_class U x0 (segment_loop p t u) \<in> G1"
    by (rule loop_class_in_space[OF loop_tu])
  have class_uv_in: "loop_class U x0 (segment_loop p u v) \<in> G1"
    by (rule loop_class_in_space[OF loop_uv])
  have join_loop: "segment_loop p t u +++ segment_loop p u v \<in> loop_space U x0"
    by (rule loop_space_join[OF loop_tu loop_uv])

  have mult_eq_join:
    "mult1 (loop_class U x0 (segment_loop p t u))
      (loop_class U x0 (segment_loop p u v)) =
      loop_class U x0 (segment_loop p t u +++ segment_loop p u v)"
    by (rule fundamental_group_mult_eqI[OF class_tu_in class_uv_in loop_tu loop_uv]) simp_all
  have join_eq:
    "loop_class U x0 (segment_loop p t u +++ segment_loop p u v) =
      loop_class U x0 (segment_loop p t v)"
  proof -
    have join_eq_q:
      "loop_class U x0 (segment_loop q 0 a +++ segment_loop q a 1) =
        loop_class U x0 (segment_loop q 0 1)"
    proof (rule loop_class_eqI)
      show "segment_loop q 0 a +++ segment_loop q a 1 \<in> loop_space U x0"
        unfolding seg_tu_eq seg_uv_eq by (rule join_loop)
      show "segment_loop q 0 1 \<in> loop_space U x0"
        using seg_tv_eq loop_tv by simp
      show "homotopic_paths U (segment_loop q 0 a +++ segment_loop q a 1) (segment_loop q 0 1)"
        by (rule join_hom_q)
    qed
    show ?thesis
      using join_eq_q by (simp only: seg_tu_eq seg_uv_eq seg_tv_eq)
  qed
  show ?thesis
    using mult_eq_join join_eq by simp
qed

lemma segment_loop_mult_eq_right:
  assumes p_path: "path p"
    and p_imgW: "path_image p \<subseteq> W"
    and t01: "t \<in> {0..1}"
    and u01: "u \<in> {0..1}"
    and v01: "v \<in> {0..1}"
    and tu: "t < u"
    and uv: "u < v"
    and ptUV: "p t \<in> U \<inter> V"
    and puUV: "p u \<in> U \<inter> V"
    and pvUV: "p v \<in> U \<inter> V"
    and seg_tvV: "subpathin t v p ` {0..1} \<subseteq> V"
  shows "mult2 (loop_class V x0 (segment_loop p t u))
      (loop_class V x0 (segment_loop p u v)) =
    loop_class V x0 (segment_loop p t v)"
proof -
  define q where "q = subpathin t v p"
  define a where "a = (u - t) / (v - t)"

  have tv: "t < v"
    using tu uv by linarith
  have a01: "a \<in> {0..1}"
    unfolding a_def using tu uv tv by (auto simp: field_simps)
  have q_path: "path q"
    unfolding q_def by (rule path_subpathin[OF p_path t01 v01])
  have q_imgV: "path_image q \<subseteq> V"
    unfolding q_def using seg_tvV by (simp add: path_image_def)
  have q0UV: "q 0 \<in> U \<inter> V"
    unfolding q_def using ptUV by (simp add: subpathin_def)
  have qaUV: "q a \<in> U \<inter> V"
  proof -
    have qa_eq: "q a = p u"
    proof -
      have ta_eq: "t + (v - t) * a = u"
        unfolding a_def using tv by (simp add: field_simps)
      show ?thesis
        unfolding q_def subpathin_def using ta_eq by (simp add: algebra_simps)
    qed
    then show ?thesis
      using puUV by simp
  qed
  have q1UV: "q 1 \<in> U \<inter> V"
    unfolding q_def using pvUV by (simp add: subpathin_def)
  have join_hom_q:
    "homotopic_paths V (segment_loop q 0 a +++ segment_loop q a 1) (segment_loop q 0 1)"
    by (rule segment_loop_join_in_set[OF q_path q_imgV]) (use a01 q0UV qaUV q1UV in auto)

  have seg_tu_eq: "segment_loop q 0 a = segment_loop p t u"
  proof -
    have ta_eq: "((v - t) * a) + t = u"
      unfolding a_def using tv by (simp add: field_simps algebra_simps)
    show ?thesis
      unfolding q_def using ta_eq by (simp add: segment_loop_subpathin)
  qed
  have seg_uv_eq: "segment_loop q a 1 = segment_loop p u v"
  proof -
    have ta_eq: "((v - t) * a) + t = u"
      unfolding a_def using tv by (simp add: field_simps algebra_simps)
    show ?thesis
      unfolding q_def using ta_eq by (simp add: segment_loop_subpathin)
  qed
  have seg_tv_eq: "segment_loop q 0 1 = segment_loop p t v"
    unfolding q_def by (simp add: segment_loop_subpathin)

  have seg_tuV: "subpathin t u p ` {0..1} \<subseteq> V"
    by (rule order_trans[OF subpathin_image_subset_left[OF t01 u01 v01]]) (use tu uv seg_tvV in auto)
  have seg_uvV: "subpathin u v p ` {0..1} \<subseteq> V"
    by (rule order_trans[OF subpathin_image_subset_right[OF t01 u01 v01]]) (use tu uv seg_tvV in auto)

  have loop_tu: "segment_loop p t u \<in> loop_space V x0"
    by (rule segment_loop_in_V[OF p_path p_imgW t01 u01 ptUV puUV seg_tuV])
  have loop_uv: "segment_loop p u v \<in> loop_space V x0"
    by (rule segment_loop_in_V[OF p_path p_imgW u01 v01 puUV pvUV seg_uvV])
  have loop_tv: "segment_loop p t v \<in> loop_space V x0"
    by (rule segment_loop_in_V[OF p_path p_imgW t01 v01 ptUV pvUV seg_tvV])

  have class_tu_in: "loop_class V x0 (segment_loop p t u) \<in> G2"
    by (rule loop_class_in_space[OF loop_tu])
  have class_uv_in: "loop_class V x0 (segment_loop p u v) \<in> G2"
    by (rule loop_class_in_space[OF loop_uv])
  have join_loop: "segment_loop p t u +++ segment_loop p u v \<in> loop_space V x0"
    by (rule loop_space_join[OF loop_tu loop_uv])

  have mult_eq_join:
    "mult2 (loop_class V x0 (segment_loop p t u))
      (loop_class V x0 (segment_loop p u v)) =
      loop_class V x0 (segment_loop p t u +++ segment_loop p u v)"
    by (rule fundamental_group_mult_eqI[OF class_tu_in class_uv_in loop_tu loop_uv]) simp_all
  have join_eq:
    "loop_class V x0 (segment_loop p t u +++ segment_loop p u v) =
      loop_class V x0 (segment_loop p t v)"
  proof -
    have join_eq_q:
      "loop_class V x0 (segment_loop q 0 a +++ segment_loop q a 1) =
        loop_class V x0 (segment_loop q 0 1)"
    proof (rule loop_class_eqI)
      show "segment_loop q 0 a +++ segment_loop q a 1 \<in> loop_space V x0"
        unfolding seg_tu_eq seg_uv_eq by (rule join_loop)
      show "segment_loop q 0 1 \<in> loop_space V x0"
        using seg_tv_eq loop_tv by simp
      show "homotopic_paths V (segment_loop q 0 a +++ segment_loop q a 1) (segment_loop q 0 1)"
        by (rule join_hom_q)
    qed
    show ?thesis
      using join_eq_q by (simp only: seg_tu_eq seg_uv_eq seg_tv_eq)
  qed
  show ?thesis
    using mult_eq_join join_eq by simp
qed

lemma segment_word_split_left_equiv:
  assumes p_loop: "p \<in> loop_space W x0"
    and t01: "t \<in> {0..1}"
    and u01: "u \<in> {0..1}"
    and v01: "v \<in> {0..1}"
    and tu: "t < u"
    and uv: "u < v"
    and ptUV: "p t \<in> U \<inter> V"
    and puUV: "p u \<in> U \<inter> V"
    and pvUV: "p v \<in> U \<inter> V"
    and seg_tvU: "subpathin t v p ` {0..1} \<subseteq> U"
    and rest_in: "fpw_in_space G1 G2 rest"
  shows "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2
      (WordLeft (loop_class U x0 (segment_loop p t u))
        (WordLeft (loop_class U x0 (segment_loop p u v)) rest))
      (WordLeft (loop_class U x0 (segment_loop p t v)) rest)"
proof -
  from p_loop have p_path: "path p" and p_imgW: "path_image p \<subseteq> W"
    unfolding loop_space_def by auto
  have seg_tuU: "subpathin t u p ` {0..1} \<subseteq> U"
    by (rule order_trans[OF subpathin_image_subset_left[OF t01 u01 v01]]) (use tu uv seg_tvU in auto)
  have seg_uvU: "subpathin u v p ` {0..1} \<subseteq> U"
    by (rule order_trans[OF subpathin_image_subset_right[OF t01 u01 v01]]) (use tu uv seg_tvU in auto)
  have loop_tu: "segment_loop p t u \<in> loop_space U x0"
    by (rule segment_loop_in_U[OF p_path p_imgW t01 u01 ptUV puUV seg_tuU])
  have loop_uv: "segment_loop p u v \<in> loop_space U x0"
    by (rule segment_loop_in_U[OF p_path p_imgW u01 v01 puUV pvUV seg_uvU])
  have class_tu_in: "loop_class U x0 (segment_loop p t u) \<in> G1"
    by (rule loop_class_in_space[OF loop_tu])
  have class_uv_in: "loop_class U x0 (segment_loop p u v) \<in> G1"
    by (rule loop_class_in_space[OF loop_uv])
  have mult_in:
    "mult1 (loop_class U x0 (segment_loop p t u))
      (loop_class U x0 (segment_loop p u v)) \<in> G1"
    by (rule fundamental_group_mult_in_space[OF class_tu_in class_uv_in])
  have mult_eq:
    "mult1 (loop_class U x0 (segment_loop p t u))
      (loop_class U x0 (segment_loop p u v)) =
      loop_class U x0 (segment_loop p t v)"
    by (rule segment_loop_mult_eq_left[OF p_path p_imgW t01 u01 v01 tu uv ptUV puUV pvUV seg_tvU])
  have step:
    "carrier_fpw_reduction_step G1 G2 mult1 one1 mult2 one2
      (WordLeft (loop_class U x0 (segment_loop p t u))
        (WordLeft (loop_class U x0 (segment_loop p u v)) rest))
      (WordLeft (mult1 (loop_class U x0 (segment_loop p t u))
        (loop_class U x0 (segment_loop p u v))) rest)"
  proof (rule carrier_fpw_reduction_step.combine_left)
    show "loop_class U x0 (segment_loop p t u) \<in> G1"
      by (rule class_tu_in)
    show "loop_class U x0 (segment_loop p u v) \<in> G1"
      by (rule class_uv_in)
    show "mult1 (loop_class U x0 (segment_loop p t u)) (loop_class U x0 (segment_loop p u v)) \<in> G1"
      by (rule mult_in)
    show "fpw_in_space G1 G2 rest"
      by (rule rest_in)
  qed
  have red:
    "carrier_fpw_reduction G1 G2 mult1 one1 mult2 one2
      (WordLeft (loop_class U x0 (segment_loop p t u))
        (WordLeft (loop_class U x0 (segment_loop p u v)) rest))
      (WordLeft (mult1 (loop_class U x0 (segment_loop p t u))
        (loop_class U x0 (segment_loop p u v))) rest)"
    by (rule carrier_fpw_reduction.step[OF step])
  have rel:
    "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2
      (WordLeft (loop_class U x0 (segment_loop p t u))
        (WordLeft (loop_class U x0 (segment_loop p u v)) rest))
      (WordLeft (mult1 (loop_class U x0 (segment_loop p t u))
        (loop_class U x0 (segment_loop p u v))) rest)"
    by (rule carrier_full_amalg_equiv.of_reduction[OF red])
  show ?thesis
    using rel mult_eq by simp
qed

lemma segment_word_split_right_equiv:
  assumes p_loop: "p \<in> loop_space W x0"
    and t01: "t \<in> {0..1}"
    and u01: "u \<in> {0..1}"
    and v01: "v \<in> {0..1}"
    and tu: "t < u"
    and uv: "u < v"
    and ptUV: "p t \<in> U \<inter> V"
    and puUV: "p u \<in> U \<inter> V"
    and pvUV: "p v \<in> U \<inter> V"
    and seg_tvV: "subpathin t v p ` {0..1} \<subseteq> V"
    and rest_in: "fpw_in_space G1 G2 rest"
  shows "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2
      (WordRight (loop_class V x0 (segment_loop p t u))
        (WordRight (loop_class V x0 (segment_loop p u v)) rest))
      (WordRight (loop_class V x0 (segment_loop p t v)) rest)"
proof -
  from p_loop have p_path: "path p" and p_imgW: "path_image p \<subseteq> W"
    unfolding loop_space_def by auto
  have seg_tuV: "subpathin t u p ` {0..1} \<subseteq> V"
    by (rule order_trans[OF subpathin_image_subset_left[OF t01 u01 v01]]) (use tu uv seg_tvV in auto)
  have seg_uvV: "subpathin u v p ` {0..1} \<subseteq> V"
    by (rule order_trans[OF subpathin_image_subset_right[OF t01 u01 v01]]) (use tu uv seg_tvV in auto)
  have loop_tu: "segment_loop p t u \<in> loop_space V x0"
    by (rule segment_loop_in_V[OF p_path p_imgW t01 u01 ptUV puUV seg_tuV])
  have loop_uv: "segment_loop p u v \<in> loop_space V x0"
    by (rule segment_loop_in_V[OF p_path p_imgW u01 v01 puUV pvUV seg_uvV])
  have class_tu_in: "loop_class V x0 (segment_loop p t u) \<in> G2"
    by (rule loop_class_in_space[OF loop_tu])
  have class_uv_in: "loop_class V x0 (segment_loop p u v) \<in> G2"
    by (rule loop_class_in_space[OF loop_uv])
  have mult_in:
    "mult2 (loop_class V x0 (segment_loop p t u))
      (loop_class V x0 (segment_loop p u v)) \<in> G2"
    by (rule fundamental_group_mult_in_space[OF class_tu_in class_uv_in])
  have mult_eq:
    "mult2 (loop_class V x0 (segment_loop p t u))
      (loop_class V x0 (segment_loop p u v)) =
      loop_class V x0 (segment_loop p t v)"
    by (rule segment_loop_mult_eq_right[OF p_path p_imgW t01 u01 v01 tu uv ptUV puUV pvUV seg_tvV])
  have step:
    "carrier_fpw_reduction_step G1 G2 mult1 one1 mult2 one2
      (WordRight (loop_class V x0 (segment_loop p t u))
        (WordRight (loop_class V x0 (segment_loop p u v)) rest))
      (WordRight (mult2 (loop_class V x0 (segment_loop p t u))
        (loop_class V x0 (segment_loop p u v))) rest)"
  proof (rule carrier_fpw_reduction_step.combine_right)
    show "loop_class V x0 (segment_loop p t u) \<in> G2"
      by (rule class_tu_in)
    show "loop_class V x0 (segment_loop p u v) \<in> G2"
      by (rule class_uv_in)
    show "mult2 (loop_class V x0 (segment_loop p t u)) (loop_class V x0 (segment_loop p u v)) \<in> G2"
      by (rule mult_in)
    show "fpw_in_space G1 G2 rest"
      by (rule rest_in)
  qed
  have red:
    "carrier_fpw_reduction G1 G2 mult1 one1 mult2 one2
      (WordRight (loop_class V x0 (segment_loop p t u))
        (WordRight (loop_class V x0 (segment_loop p u v)) rest))
      (WordRight (mult2 (loop_class V x0 (segment_loop p t u))
        (loop_class V x0 (segment_loop p u v))) rest)"
    by (rule carrier_fpw_reduction.step[OF step])
  have rel:
    "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2
      (WordRight (loop_class V x0 (segment_loop p t u))
        (WordRight (loop_class V x0 (segment_loop p u v)) rest))
      (WordRight (mult2 (loop_class V x0 (segment_loop p t u))
        (loop_class V x0 (segment_loop p u v))) rest)"
    by (rule carrier_full_amalg_equiv.of_reduction[OF red])
  show ?thesis
    using rel mult_eq by simp
qed

lemma segment_word_switch:
  assumes p_path: "path p"
    and p_imgW: "path_image p \<subseteq> W"
    and t01: "t \<in> {0..1}"
    and u01: "u \<in> {0..1}"
    and tu: "t < u"
    and ptUV: "p t \<in> U \<inter> V"
    and puUV: "p u \<in> U \<inter> V"
    and segUV: "subpathin t u p ` {0..1} \<subseteq> U \<inter> V"
    and rest_in: "fpw_in_space G1 G2 rest"
    and bc: "b \<noteq> c"
  shows "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2
      (if b then WordLeft (loop_class U x0 (segment_loop p t u)) rest
       else WordRight (loop_class V x0 (segment_loop p t u)) rest)
      (if c then WordLeft (loop_class U x0 (segment_loop p t u)) rest
       else WordRight (loop_class V x0 (segment_loop p t u)) rest)"
proof -
  have conn_t_img: "path_image (connector (p t)) \<subseteq> U \<inter> V"
    using connector_image_subset[OF ptUV] by blast
  have conn_u_img: "path_image (connector (p u)) \<subseteq> U \<inter> V"
    using connector_image_subset[OF puUV] by blast
  have segH: "segment_loop p t u \<in> loop_space (U \<inter> V) x0"
    by (rule segment_loop_in_set[where S = "U \<inter> V"])
       (use p_path p_imgW t01 u01 ptUV puUV segUV x0_in_UV conn_t_img conn_u_img in auto)
  have h_in: "loop_class (U \<inter> V) x0 (segment_loop p t u) \<in> H"
    by (rule loop_class_in_space[OF segH])
  have base:
    "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2
      (bridge_word b (loop_class (U \<inter> V) x0 (segment_loop p t u)) rest)
      (bridge_word c (loop_class (U \<inter> V) x0 (segment_loop p t u)) rest)"
    by (rule bridge_word_switch[OF h_in bc])
  show ?thesis
    using base
    by (cases b; cases c) (simp_all add: i1_loop_class_eq[OF segH] i2_loop_class_eq[OF segH])
qed

lemma svk_partition_split_head:
  assumes part: "svk_partition p (t # v # us) (b # bs)"
    and tu: "t < u"
    and uv: "u < v"
    and puUV: "p u \<in> U \<inter> V"
  shows "svk_partition p (t # u # v # us) (b # b # bs)"
proof -
  have t01: "t \<in> {0..1}" and v01: "v \<in> {0..1}"
    and seg_tv:
      "(if b then subpathin t v p ` {0..1} \<subseteq> U else subpathin t v p ` {0..1} \<subseteq> V)"
    and tail: "svk_partition p (v # us) bs"
    using part by simp_all
  have ptUV: "p t \<in> U \<inter> V"
    using part by simp
  have pvUV: "p v \<in> U \<inter> V"
    using tail by (cases us; cases bs) simp_all
  have u01: "u \<in> {0..1}"
    using t01 v01 tu uv by auto
  have seg_tu:
    "(if b then subpathin t u p ` {0..1} \<subseteq> U else subpathin t u p ` {0..1} \<subseteq> V)"
  proof (cases b)
    case True
    have "subpathin t u p ` {0..1} \<subseteq> subpathin t v p ` {0..1}"
      by (rule subpathin_image_subset_left[OF t01 u01 v01]) (use tu uv in auto)
    then show ?thesis
      using seg_tv True by auto
  next
    case False
    have "subpathin t u p ` {0..1} \<subseteq> subpathin t v p ` {0..1}"
      by (rule subpathin_image_subset_left[OF t01 u01 v01]) (use tu uv in auto)
    then show ?thesis
      using seg_tv False by auto
  qed
  have seg_uv:
    "(if b then subpathin u v p ` {0..1} \<subseteq> U else subpathin u v p ` {0..1} \<subseteq> V)"
  proof (cases b)
    case True
    have "subpathin u v p ` {0..1} \<subseteq> subpathin t v p ` {0..1}"
      by (rule subpathin_image_subset_right[OF t01 u01 v01]) (use tu uv in auto)
    then show ?thesis
      using seg_tv True by auto
  next
    case False
    have "subpathin u v p ` {0..1} \<subseteq> subpathin t v p ` {0..1}"
      by (rule subpathin_image_subset_right[OF t01 u01 v01]) (use tu uv in auto)
    then show ?thesis
      using seg_tv False by auto
  qed
  show ?thesis
    using t01 ptUV u01 tu seg_tu puUV v01 pvUV uv seg_uv tail by simp
qed

lemma svk_partition_same_start_equiv:
  assumes p_loop: "p \<in> loop_space W x0"
    and part1: "svk_partition p (t # ts) bs"
    and part2: "svk_partition p (t # us) cs"
  shows "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2
      (partition_word p (t # ts) bs)
      (partition_word p (t # us) cs)"
  using assms
proof (induction "length bs + length cs" arbitrary: t ts bs us cs rule: less_induct)
  case less
  note p_loop = less.prems(1)
  note part1 = less.prems(2)
  note part2 = less.prems(3)

  from p_loop have p_path: "path p" and p_imgW: "path_image p \<subseteq> W"
    unfolding loop_space_def by auto

  show ?case
  proof (cases bs)
    case Nil
    have ts_nil: "ts = []"
      using part1 Nil by (cases ts) simp_all
    have t1: "t = 1"
      using svk_partition_last_eq_one[OF part1] ts_nil by simp
    show ?thesis
    proof (cases cs)
      case Nil
      then show ?thesis
        using ts_nil by simp
    next
      case (Cons c cs')
      obtain v us' where us: "us = v # us'"
        using part2 Cons by (cases us) auto
      have v01: "v \<in> {0..1}"
        using part2 Cons us by simp
      have "t < v"
        using part2 Cons us by simp
      then have False
        using t1 v01 by auto
      then show ?thesis
        by simp
    qed
  next
    case (Cons b bs')
    note bs_cons = Cons
    obtain u ts' where ts: "ts = u # ts'"
      using part1 Cons by (cases ts) auto
    have t01: "t \<in> {0..1}" and ptUV: "p t \<in> U \<inter> V"
      and u01: "u \<in> {0..1}" and tu: "t < u"
      and seg_tu:
        "(if b then subpathin t u p ` {0..1} \<subseteq> U else subpathin t u p ` {0..1} \<subseteq> V)"
      and tail1: "svk_partition p (u # ts') bs'"
      using part1 Cons ts by simp_all
    have puUV: "p u \<in> U \<inter> V"
      by (rule svk_partition_next_in_intersection[OF part1[unfolded ts Cons]])
    have first_in1:
      "(if b then loop_class U x0 (segment_loop p t u) \<in> G1
       else loop_class V x0 (segment_loop p t u) \<in> G2)"
    proof (cases b)
      case True
      have seg_loop: "segment_loop p t u \<in> loop_space U x0"
        by (rule segment_loop_in_U[OF p_path p_imgW t01 u01 ptUV puUV]) (use seg_tu True in auto)
      show ?thesis
        using True by (auto intro: loop_class_in_space[OF seg_loop])
    next
      case False
      have seg_loop: "segment_loop p t u \<in> loop_space V x0"
        by (rule segment_loop_in_V[OF p_path p_imgW t01 u01 ptUV puUV]) (use seg_tu False in auto)
      show ?thesis
        using False by (auto intro: loop_class_in_space[OF seg_loop])
    qed

    show ?thesis
    proof (cases cs)
      case Nil
      have us_nil: "us = []"
        using part2 Nil by (cases us) simp_all
      have t1: "t = 1"
        using svk_partition_last_eq_one[OF part2] us_nil by simp
      have contradiction: False
        using tu t1 u01 by auto
      from contradiction show ?thesis
        by simp
    next
      case (Cons c cs')
      obtain v us' where us: "us = v # us'"
        using part2 Cons by (cases us) auto
      have v01: "v \<in> {0..1}" and tv: "t < v"
        and seg_tv:
          "(if c then subpathin t v p ` {0..1} \<subseteq> U else subpathin t v p ` {0..1} \<subseteq> V)"
        and tail2: "svk_partition p (v # us') cs'"
        using part2 Cons us by simp_all
      have pvUV: "p v \<in> U \<inter> V"
        using tail2 by (cases us'; cases cs') simp_all
      have tail2_in:
        "fpw_in_space G1 G2 (partition_word p (v # us') cs')"
        by (rule svk_partition_partition_word_in_space[OF p_loop tail2])

      show ?thesis
      proof (cases "u = v")
        case True
        note uv_eq = True
        have smaller: "length bs' + length cs' < length (b # bs') + length (c # cs')"
          by simp
        have tail_rel:
          "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2
            (partition_word p (u # ts') bs')
            (partition_word p (u # us') cs')"
        proof -
          have tail2': "svk_partition p (u # us') cs'"
            using tail2 True by simp
          have smaller': "length bs' + length cs' < length (b # bs') + length cs"
            using smaller Cons by simp
          have bs_eq: "bs = b # bs'"
            by (rule bs_cons)
          have smaller'': "length bs' + length cs' < length bs + length cs"
            using smaller' bs_eq by simp
          have ih:
            "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2
              (partition_word p (u # ts') bs')
              (partition_word p (u # us') cs')"
            by (rule less.hyps[OF smaller'' p_loop tail1 tail2'])
          show ?thesis
            by (rule ih)
        qed
        have pref_rel:
          "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2
            (partition_word p (t # u # ts') (b # bs'))
            (if b then WordLeft (loop_class U x0 (segment_loop p t u))
              (partition_word p (u # us') cs')
             else WordRight (loop_class V x0 (segment_loop p t u))
              (partition_word p (u # us') cs'))"
        proof (cases b)
          case True
          have class_in: "loop_class U x0 (segment_loop p t u) \<in> G1"
            using first_in1 True by simp
          have rel':
            "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2
              (WordLeft (loop_class U x0 (segment_loop p t u))
                (partition_word p (u # ts') bs'))
              (WordLeft (loop_class U x0 (segment_loop p t u))
                (partition_word p (u # us') cs'))"
            by (rule carrier_full_amalg_equiv_left_context[OF tail_rel class_in])
          then show ?thesis
            using rel' ts True by simp
        next
          case False
          have class_in: "loop_class V x0 (segment_loop p t u) \<in> G2"
            using first_in1 False by simp
          have rel':
            "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2
              (WordRight (loop_class V x0 (segment_loop p t u))
                (partition_word p (u # ts') bs'))
              (WordRight (loop_class V x0 (segment_loop p t u))
                (partition_word p (u # us') cs'))"
            by (rule carrier_full_amalg_equiv_right_context[OF tail_rel class_in])
          then show ?thesis
            using rel' ts False by simp
        qed
        show ?thesis
        proof (cases "b = c")
          case True
          note bc_eq = True
          show ?thesis
          proof (cases b)
            case True
            then show ?thesis
              using pref_rel bc_eq True ts us uv_eq bs_cons Cons by simp
          next
            case False
            then show ?thesis
              using pref_rel bc_eq False ts us uv_eq bs_cons Cons by simp
          qed
        next
          case False
          have segUV: "subpathin t u p ` {0..1} \<subseteq> U \<inter> V"
            using seg_tu seg_tv True False by (cases b; cases c) auto
          have tail2': "svk_partition p (u # us') cs'"
            using tail2 uv_eq by simp
          have rest_in:
            "fpw_in_space G1 G2 (partition_word p (u # us') cs')"
            by (rule svk_partition_partition_word_in_space[OF p_loop tail2'])
          have bc_ne: "b \<noteq> c"
            by (rule False)
          have switch_raw:
            "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2
              (if b then WordLeft (loop_class U x0 (segment_loop p t u))
                (partition_word p (u # us') cs')
               else WordRight (loop_class V x0 (segment_loop p t u))
                (partition_word p (u # us') cs'))
              (if c then WordLeft (loop_class U x0 (segment_loop p t u))
                (partition_word p (u # us') cs')
               else WordRight (loop_class V x0 (segment_loop p t u))
                (partition_word p (u # us') cs'))"
            by (rule segment_word_switch[where rest = "partition_word p (u # us') cs'",
                  OF p_path p_imgW t01 u01 tu ptUV puUV segUV rest_in bc_ne])
          have switch:
            "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2
              (if b then WordLeft (loop_class U x0 (segment_loop p t u))
                (partition_word p (u # us') cs')
               else WordRight (loop_class V x0 (segment_loop p t u))
                (partition_word p (u # us') cs'))
              (partition_word p (t # u # us') (c # cs'))"
            using switch_raw by (cases c) simp_all
          have step:
            "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2
              (partition_word p (t # u # ts') (b # bs'))
              (partition_word p (t # u # us') (c # cs'))"
            by (rule carrier_full_amalg_equiv.trans[OF pref_rel switch])
          show ?thesis
            using step True ts us uv_eq bs_cons Cons by simp
        qed
      next
        case False
        show ?thesis
        proof (cases "u < v")
          case True
          note uv_lt = True
          have part2_tv: "svk_partition p (t # v # us') (c # cs')"
            using part2 Cons us by simp
          have split2: "svk_partition p (t # u # v # us') (c # c # cs')"
            by (rule svk_partition_split_head[OF part2_tv tu True puUV])
          have split_tail2: "svk_partition p (u # v # us') (c # cs')"
            using split2 by simp
          have split_tail2_in:
            "fpw_in_space G1 G2 (partition_word p (u # v # us') (c # cs'))"
            by (rule svk_partition_partition_word_in_space[OF p_loop split_tail2])
          have tail2_in:
            "fpw_in_space G1 G2 (partition_word p (v # us') cs')"
            by (rule svk_partition_partition_word_in_space[OF p_loop tail2])
          have split2_rel:
            "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2
              (partition_word p (t # u # v # us') (c # c # cs'))
              (partition_word p (t # v # us') (c # cs'))"
          proof (cases c)
            case True
            have seg_tvU: "subpathin t v p ` {0..1} \<subseteq> U"
              using seg_tv True by auto
            have raw:
              "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2
                (WordLeft (loop_class U x0 (segment_loop p t u))
                  (WordLeft (loop_class U x0 (segment_loop p u v))
                    (partition_word p (v # us') cs')))
                (WordLeft (loop_class U x0 (segment_loop p t v))
                  (partition_word p (v # us') cs'))"
              by (rule segment_word_split_left_equiv[OF p_loop t01 u01 v01 tu uv_lt ptUV puUV pvUV seg_tvU tail2_in])
            then show ?thesis
              using True by simp
          next
            case False
            have seg_tvV: "subpathin t v p ` {0..1} \<subseteq> V"
              using seg_tv False by auto
            have raw:
              "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2
                (WordRight (loop_class V x0 (segment_loop p t u))
                  (WordRight (loop_class V x0 (segment_loop p u v))
                    (partition_word p (v # us') cs')))
                (WordRight (loop_class V x0 (segment_loop p t v))
                  (partition_word p (v # us') cs'))"
              by (rule segment_word_split_right_equiv[OF p_loop t01 u01 v01 tu uv_lt ptUV puUV pvUV seg_tvV tail2_in])
            then show ?thesis
              using False by simp
          qed
          have smaller: "length bs' + length (c # cs') < length (b # bs') + length (c # cs')"
            by simp
          have tail_rel:
            "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2
              (partition_word p (u # ts') bs')
              (partition_word p (u # v # us') (c # cs'))"
          proof -
            have smaller': "length bs' + length (c # cs') < length (b # bs') + length cs"
              using smaller Cons by simp
            have bs_eq: "bs = b # bs'"
              by (rule bs_cons)
            have smaller'': "length bs' + length (c # cs') < length bs + length cs"
              using smaller' bs_eq by simp
            have ih:
              "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2
                (partition_word p (u # ts') bs')
                (partition_word p (u # v # us') (c # cs'))"
              by (rule less.hyps[OF smaller'' p_loop tail1 split_tail2])
            show ?thesis
              by (rule ih)
          qed
          have pref_rel:
            "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2
              (partition_word p (t # u # ts') (b # bs'))
              (if b then WordLeft (loop_class U x0 (segment_loop p t u))
                (partition_word p (u # v # us') (c # cs'))
               else WordRight (loop_class V x0 (segment_loop p t u))
                (partition_word p (u # v # us') (c # cs')))"
          proof (cases b)
            case True
            have class_in: "loop_class U x0 (segment_loop p t u) \<in> G1"
              using first_in1 True by simp
            have rel':
              "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2
                (WordLeft (loop_class U x0 (segment_loop p t u))
                  (partition_word p (u # ts') bs'))
                (WordLeft (loop_class U x0 (segment_loop p t u))
                  (partition_word p (u # v # us') (c # cs')))"
              by (rule carrier_full_amalg_equiv_left_context[OF tail_rel class_in])
            from rel' show ?thesis
              using True ts by simp
          next
            case False
            have class_in: "loop_class V x0 (segment_loop p t u) \<in> G2"
              using first_in1 False by simp
            have rel':
              "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2
                (WordRight (loop_class V x0 (segment_loop p t u))
                  (partition_word p (u # ts') bs'))
                (WordRight (loop_class V x0 (segment_loop p t u))
                  (partition_word p (u # v # us') (c # cs')))"
              by (rule carrier_full_amalg_equiv_right_context[OF tail_rel class_in])
            then show ?thesis
              using False ts by simp
          qed
          show ?thesis
          proof (cases "b = c")
            case True
            have pref_to_split:
              "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2
                (if b then WordLeft (loop_class U x0 (segment_loop p t u))
                  (partition_word p (u # v # us') (c # cs'))
                 else WordRight (loop_class V x0 (segment_loop p t u))
                  (partition_word p (u # v # us') (c # cs')))
                (partition_word p (t # u # v # us') (c # c # cs'))"
              using True by simp
            have step:
              "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2
                (partition_word p (t # u # ts') (b # bs'))
                (partition_word p (t # u # v # us') (c # c # cs'))"
              by (rule carrier_full_amalg_equiv.trans[OF pref_rel pref_to_split])
            have final:
              "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2
                (partition_word p (t # u # ts') (b # bs'))
                (partition_word p (t # v # us') (c # cs'))"
              by (rule carrier_full_amalg_equiv.trans[OF step split2_rel])
            show ?thesis
              using final ts us bs_cons Cons by simp
          next
            case False
            have segUV: "subpathin t u p ` {0..1} \<subseteq> U \<inter> V"
              using seg_tu split2 False by (cases b; cases c) auto
            have switch_raw:
              "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2
                (if b then WordLeft (loop_class U x0 (segment_loop p t u))
                  (partition_word p (u # v # us') (c # cs'))
                 else WordRight (loop_class V x0 (segment_loop p t u))
                  (partition_word p (u # v # us') (c # cs')))
                (if c then WordLeft (loop_class U x0 (segment_loop p t u))
                  (partition_word p (u # v # us') (c # cs'))
                 else WordRight (loop_class V x0 (segment_loop p t u))
                  (partition_word p (u # v # us') (c # cs')))"
              by (rule segment_word_switch[where rest = "partition_word p (u # v # us') (c # cs')",
                    OF p_path p_imgW t01 u01 tu ptUV puUV segUV split_tail2_in False])
            have switch:
              "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2
                (if b then WordLeft (loop_class U x0 (segment_loop p t u))
                  (partition_word p (u # v # us') (c # cs'))
                 else WordRight (loop_class V x0 (segment_loop p t u))
                  (partition_word p (u # v # us') (c # cs')))
                (partition_word p (t # u # v # us') (c # c # cs'))"
              using switch_raw by (cases c) simp_all
            have step:
              "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2
                (partition_word p (t # u # ts') (b # bs'))
                (partition_word p (t # u # v # us') (c # c # cs'))"
              by (rule carrier_full_amalg_equiv.trans[OF pref_rel switch])
            have final:
              "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2
                (partition_word p (t # u # ts') (b # bs'))
                (partition_word p (t # v # us') (c # cs'))"
              by (rule carrier_full_amalg_equiv.trans[OF step split2_rel])
            show ?thesis
              using final ts us bs_cons Cons by simp
          qed
        next
          case False_lt: False
          have vu: "v < u"
            using False False_lt by linarith
          have part1_tu: "svk_partition p (t # u # ts') (b # bs')"
            using part1 bs_cons ts by simp
          have split1: "svk_partition p (t # v # u # ts') (b # b # bs')"
            by (rule svk_partition_split_head[OF part1_tu tv vu pvUV])
          have split_tail1: "svk_partition p (v # u # ts') (b # bs')"
            using split1 by simp
          have split1_rel:
            "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2
              (partition_word p (t # v # u # ts') (b # b # bs'))
              (partition_word p (t # u # ts') (b # bs'))"
          proof (cases b)
            case True
            have seg_tuU: "subpathin t u p ` {0..1} \<subseteq> U"
              using seg_tu True by simp
            have raw:
              "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2
                (WordLeft (loop_class U x0 (segment_loop p t v))
                  (WordLeft (loop_class U x0 (segment_loop p v u))
                    (partition_word p (u # ts') bs')))
                (WordLeft (loop_class U x0 (segment_loop p t u))
                  (partition_word p (u # ts') bs'))"
              by (rule segment_word_split_left_equiv[where rest = "partition_word p (u # ts') bs'",
                    OF p_loop t01 v01 u01 tv vu ptUV pvUV puUV seg_tuU
                       svk_partition_partition_word_in_space[OF p_loop tail1]])
            then show ?thesis
              using True by simp
          next
            case False
            have seg_tuV: "subpathin t u p ` {0..1} \<subseteq> V"
              using seg_tu False by simp
            have raw:
              "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2
                (WordRight (loop_class V x0 (segment_loop p t v))
                  (WordRight (loop_class V x0 (segment_loop p v u))
                    (partition_word p (u # ts') bs')))
                (WordRight (loop_class V x0 (segment_loop p t u))
                  (partition_word p (u # ts') bs'))"
              by (rule segment_word_split_right_equiv[where rest = "partition_word p (u # ts') bs'",
                    OF p_loop t01 v01 u01 tv vu ptUV pvUV puUV seg_tuV
                       svk_partition_partition_word_in_space[OF p_loop tail1]])
            then show ?thesis
              using False by simp
          qed
          have smaller: "length (b # bs') + length cs' < length (b # bs') + length (c # cs')"
            by simp
          have tail_rel:
            "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2
              (partition_word p (v # u # ts') (b # bs'))
              (partition_word p (v # us') cs')"
          proof -
            have smaller': "length (b # bs') + length cs' < length bs + length (c # cs')"
              using smaller bs_cons by simp
            have cs_eq: "cs = c # cs'"
              by (rule Cons)
            have smaller'': "length (b # bs') + length cs' < length bs + length cs"
              using smaller' cs_eq by simp
            have ih:
              "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2
                (partition_word p (v # u # ts') (b # bs'))
                (partition_word p (v # us') cs')"
              by (rule less.hyps[OF smaller'' p_loop split_tail1 tail2])
            show ?thesis
              by (rule ih)
          qed
          have first_in2:
            "(if c then loop_class U x0 (segment_loop p t v) \<in> G1
             else loop_class V x0 (segment_loop p t v) \<in> G2)"
          proof (cases c)
            case True
            have seg_loop: "segment_loop p t v \<in> loop_space U x0"
              by (rule segment_loop_in_U[OF p_path p_imgW t01 v01 ptUV pvUV]) (use seg_tv True in auto)
            show ?thesis
              using True by (auto intro: loop_class_in_space[OF seg_loop])
          next
            case False
            have seg_loop: "segment_loop p t v \<in> loop_space V x0"
              by (rule segment_loop_in_V[OF p_path p_imgW t01 v01 ptUV pvUV]) (use seg_tv False in auto)
            show ?thesis
              using False by (auto intro: loop_class_in_space[OF seg_loop])
          qed
          show ?thesis
          proof (cases "b = c")
            case True
            from True have bc: "b = c" .
            have pref_rel:
              "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2
                (partition_word p (t # v # u # ts') (b # b # bs'))
                (partition_word p (t # v # us') (c # cs'))"
            proof (cases b)
              case True
              have class_in: "loop_class U x0 (segment_loop p t v) \<in> G1"
                using first_in2 bc True by simp
              from bc True have c_true: "c"
                by simp
              have tail_rel':
                "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2
                  (partition_word p (v # u # ts') (True # bs'))
                  (partition_word p (v # us') cs')"
                using tail_rel True c_true by simp
              have ctx_rel:
                "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2
                  (WordLeft (loop_class U x0 (segment_loop p t v))
                    (partition_word p (v # u # ts') (True # bs')))
                  (WordLeft (loop_class U x0 (segment_loop p t v))
                    (partition_word p (v # us') cs'))"
                by (rule carrier_full_amalg_equiv_left_context[OF tail_rel' class_in])
              show ?thesis
                using bc True ctx_rel by simp
            next
              case False
              have class_in: "loop_class V x0 (segment_loop p t v) \<in> G2"
                using first_in2 bc False by simp
              from bc False have c_false: "\<not> c"
                by simp
              have tail_rel':
                "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2
                  (partition_word p (v # u # ts') (False # bs'))
                  (partition_word p (v # us') cs')"
                using tail_rel False c_false by simp
              have ctx_rel:
                "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2
                  (WordRight (loop_class V x0 (segment_loop p t v))
                    (partition_word p (v # u # ts') (False # bs')))
                  (WordRight (loop_class V x0 (segment_loop p t v))
                    (partition_word p (v # us') cs'))"
                by (rule carrier_full_amalg_equiv_right_context[OF tail_rel' class_in])
              show ?thesis
                using bc False ctx_rel by simp
            qed
            have from_orig:
              "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2
                (partition_word p (t # u # ts') (b # bs'))
                (partition_word p (t # v # u # ts') (b # b # bs'))"
              by (rule carrier_full_amalg_equiv.sym[OF split1_rel])
            have step:
              "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2
                (partition_word p (t # u # ts') (b # bs'))
                (partition_word p (t # v # us') (c # cs'))"
              by (rule carrier_full_amalg_equiv.trans[OF from_orig pref_rel])
            show ?thesis
              using step us ts bs_cons Cons by simp
          next
            case False
            have pref_rel:
              "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2
                (partition_word p (t # v # u # ts') (b # b # bs'))
                (if b then WordLeft (loop_class U x0 (segment_loop p t v))
                  (partition_word p (v # us') cs')
                 else WordRight (loop_class V x0 (segment_loop p t v))
                  (partition_word p (v # us') cs'))"
            proof -
              have first_in_split:
                "(if b then loop_class U x0 (segment_loop p t v) \<in> G1
                 else loop_class V x0 (segment_loop p t v) \<in> G2)"
                using split1 by (cases b) (auto intro: loop_class_in_space
                  segment_loop_in_U[OF p_path p_imgW t01 v01 ptUV pvUV]
                  segment_loop_in_V[OF p_path p_imgW t01 v01 ptUV pvUV])
              show ?thesis
              proof (cases b)
                case True
                have class_in: "loop_class U x0 (segment_loop p t v) \<in> G1"
                  using first_in_split True by simp
                have tail_rel':
                  "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2
                    (partition_word p (v # u # ts') (True # bs'))
                    (partition_word p (v # us') cs')"
                  using tail_rel True by simp
                have ctx_rel:
                  "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2
                    (WordLeft (loop_class U x0 (segment_loop p t v))
                      (partition_word p (v # u # ts') (True # bs')))
                    (WordLeft (loop_class U x0 (segment_loop p t v))
                      (partition_word p (v # us') cs'))"
                  by (rule carrier_full_amalg_equiv_left_context[OF tail_rel' class_in])
                show ?thesis
                  using True ctx_rel by simp
              next
                case False
                have class_in: "loop_class V x0 (segment_loop p t v) \<in> G2"
                  using first_in_split False by simp
                have tail_rel':
                  "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2
                    (partition_word p (v # u # ts') (False # bs'))
                    (partition_word p (v # us') cs')"
                  using tail_rel False by simp
                have ctx_rel:
                  "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2
                    (WordRight (loop_class V x0 (segment_loop p t v))
                      (partition_word p (v # u # ts') (False # bs')))
                    (WordRight (loop_class V x0 (segment_loop p t v))
                      (partition_word p (v # us') cs'))"
                  by (rule carrier_full_amalg_equiv_right_context[OF tail_rel' class_in])
                show ?thesis
                  using False ctx_rel by simp
              qed
            qed
            have segUV: "subpathin t v p ` {0..1} \<subseteq> U \<inter> V"
              using split1 seg_tv False by (cases b; cases c) auto
            have switch_raw:
              "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2
                (if b then WordLeft (loop_class U x0 (segment_loop p t v))
                  (partition_word p (v # us') cs')
                 else WordRight (loop_class V x0 (segment_loop p t v))
                  (partition_word p (v # us') cs'))
                (if c then WordLeft (loop_class U x0 (segment_loop p t v))
                  (partition_word p (v # us') cs')
                 else WordRight (loop_class V x0 (segment_loop p t v))
                  (partition_word p (v # us') cs'))"
              by (rule segment_word_switch[where rest = "partition_word p (v # us') cs'",
                    OF p_path p_imgW t01 v01 tv ptUV pvUV segUV tail2_in False])
            have switch:
              "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2
                (if b then WordLeft (loop_class U x0 (segment_loop p t v))
                  (partition_word p (v # us') cs')
                 else WordRight (loop_class V x0 (segment_loop p t v))
                  (partition_word p (v # us') cs'))
                (partition_word p (t # v # us') (c # cs'))"
              using switch_raw by (cases c) simp_all
            have from_orig:
              "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2
                (partition_word p (t # u # ts') (b # bs'))
                (partition_word p (t # v # u # ts') (b # b # bs'))"
              by (rule carrier_full_amalg_equiv.sym[OF split1_rel])
            have step1:
              "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2
                (partition_word p (t # u # ts') (b # bs'))
                (if b then WordLeft (loop_class U x0 (segment_loop p t v))
                  (partition_word p (v # us') cs')
                 else WordRight (loop_class V x0 (segment_loop p t v))
                  (partition_word p (v # us') cs'))"
              by (rule carrier_full_amalg_equiv.trans[OF from_orig pref_rel])
            have final:
              "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2
                (partition_word p (t # u # ts') (b # bs'))
                (partition_word p (t # v # us') (c # cs'))"
              by (rule carrier_full_amalg_equiv.trans[OF step1 switch])
            show ?thesis
              using final ts us bs_cons Cons by simp
          qed
        qed
      qed
    qed
  qed
qed

lemma valid_partition_same_loop_partition_word_equiv:
  assumes p_loop: "p \<in> loop_space W x0"
    and part1: "valid_partition p ts bs"
    and part2: "valid_partition p us cs"
  shows "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2
      (partition_word p ts bs) (partition_word p us cs)"
proof -
  obtain t ts' where ts: "ts = t # ts'"
    using valid_partition_hd(1)[OF part1] by (cases ts) auto
  obtain u us' where us: "us = u # us'"
    using valid_partition_hd(1)[OF part2] by (cases us) auto
  have valid_ts: "valid_partition p (t # ts') bs"
    using part1 unfolding ts by simp
  have t0: "t = 0"
    by (rule valid_partition_cases(1)[OF valid_ts])
  have part1': "svk_partition p (t # ts') bs"
    by (rule valid_partition_cases(2)[OF valid_ts])
  have valid_us: "valid_partition p (u # us') cs"
    using part2 unfolding us by simp
  have u0: "u = 0"
    by (rule valid_partition_cases(1)[OF valid_us])
  have part2': "svk_partition p (u # us') cs"
    by (rule valid_partition_cases(2)[OF valid_us])
  have rel:
    "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2
      (partition_word p (t # ts') bs)
      (partition_word p (u # us') cs)"
  proof -
    have part1_0: "svk_partition p (0 # ts') bs"
      using part1' t0 by simp
    have part2_0: "svk_partition p (0 # us') cs"
      using part2' u0 by simp
    show ?thesis
      by (subst t0, subst u0, rule svk_partition_same_start_equiv[OF p_loop part1_0 part2_0])
  qed
then show ?thesis
    using ts us t0 u0 by simp
qed

lemma strip_neighbourhood:
  fixes h :: "(real \<times> real) \<Rightarrow> 'a"
  assumes h_cont: "continuous_map (top_of_set ({0..1} \<times> {0..1})) (top_of_set W) h"
    and a01: "a \<in> {0..1}"
    and b01: "b \<in> {0..1}"
    and y0_01: "y0 \<in> {0..1}"
    and ab: "a \<le> b"
    and rowS: "h ` ({a..b} \<times> {y0}) \<subseteq> S"
    and openS: "open S"
  shows "\<exists>N. openin (top_of_set {0..1}) N \<and> y0 \<in> N \<and> h ` ({a..b} \<times> N) \<subseteq> S"
proof -
  have h_on: "continuous_on ({0..1} \<times> {0..1}) h"
    using h_cont by simp
  have strip_subset: "{a..b} \<times> {0..1} \<subseteq> {0..1} \<times> {0..1}"
    using a01 b01 ab by auto
  have strip_cont: "continuous_on ({a..b} \<times> {0..1}) h"
    by (rule continuous_on_subset[OF h_on strip_subset])
  have strip_open:
    "openin (top_of_set ({a..b} \<times> {0..1}))
      (({a..b} \<times> {0..1}) \<inter> h -` S)"
    by (rule continuous_openin_preimage_gen[OF strip_cont openS])
  have line_in:
    "(\<lambda>x. (x, y0)) ` {a..b} \<subseteq> (({a..b} \<times> {0..1}) \<inter> h -` S)"
    using rowS y0_01 by auto
  obtain N where N_open: "openin (top_of_set {0..1}) N"
    and y0N: "y0 \<in> N"
    and stripN: "{a..b} \<times> N \<subseteq> (({a..b} \<times> {0..1}) \<inter> h -` S)"
  proof -
    have strip_open_prod:
      "openin (prod_topology (top_of_set {a..b}) (top_of_set {0..1}))
        (({a..b} \<times> {0..1}) \<inter> h -` S)"
      using strip_open by simp
    have line_in_prod:
      "{a..b} \<times> {y0} \<subseteq> (({a..b} \<times> {0..1}) \<inter> h -` S)"
      using line_in by auto
    have compact_ab: "compactin (top_of_set {a..b}) {a..b}"
      using compact_Icc by simp
    obtain M N where M_open: "openin (top_of_set {a..b}) M"
      and N_open: "openin (top_of_set {0..1}) N"
      and M_cover: "{a..b} \<subseteq> M"
      and y0N: "y0 \<in> N"
      and MN_strip: "M \<times> N \<subseteq> (({a..b} \<times> {0..1}) \<inter> h -` S)"
    proof -
      have local_boxes:
        "\<exists>M N. openin (top_of_set {a..b}) M \<and> openin (top_of_set {0..1}) N \<and>
          x \<in> M \<and> y0 \<in> N \<and> M \<times> N \<subseteq> (({a..b} \<times> {0..1}) \<inter> h -` S)"
        if x_in: "x \<in> {a..b}" for x
      proof -
        have xy_pair: "(x, y0) \<in> {a..b} \<times> {y0}"
          using x_in by auto
        have xy_in: "(x, y0) \<in> (({a..b} \<times> {0..1}) \<inter> h -` S)"
          by (rule subsetD[OF line_in_prod xy_pair])
        show ?thesis
          using strip_open_prod xy_in by (metis openin_prod_topology_alt)
      qed
      then obtain U V where UV:
        "\<And>x. x \<in> {a..b} \<Longrightarrow>
          openin (top_of_set {a..b}) (U x) \<and>
          openin (top_of_set {0..1}) (V x) \<and>
          x \<in> U x \<and> y0 \<in> V x \<and>
          U x \<times> V x \<subseteq> (({a..b} \<times> {0..1}) \<inter> h -` S)"
        by metis
      then obtain D where D: "finite D" "D \<subseteq> {a..b}" "{a..b} \<subseteq> \<Union> (U ` D)"
        using compactinD[OF compact_ab, of "U ` {a..b}"]
        by (smt (verit) UN_I finite_subset_image imageE subsetI)
      show ?thesis
      proof (intro that[of "\<Union> (U ` D)" "\<Inter> (V ` D)"])
        show "openin (top_of_set {a..b}) (\<Union> (U ` D))"
          using D UV by blast
        show "openin (top_of_set {0..1}) (\<Inter> (V ` D))"
        proof (rule openin_Inter)
          show "finite (V ` D)"
            using D by simp
          show "V ` D \<noteq> {}"
          proof
            assume "V ` D = {}"
            then have "D = {}"
              by auto
            with D(3) ab show False
              by simp
          qed
          show "openin (top_of_set {0..1}) T" if "T \<in> V ` D" for T
          proof -
            from that obtain x where xD: "x \<in> D" and T_def: "T = V x"
              by auto
            show ?thesis
              using D(2) UV xD T_def by blast
          qed
        qed
        show "{a..b} \<subseteq> \<Union> (U ` D)"
          using D by blast
        show "y0 \<in> \<Inter> (V ` D)"
          using D UV by force
        show "(\<Union> (U ` D)) \<times> (\<Inter> (V ` D)) \<subseteq> (({a..b} \<times> {0..1}) \<inter> h -` S)"
        proof
          fix xy
          assume xy_in: "xy \<in> (\<Union> (U ` D)) \<times> (\<Inter> (V ` D))"
          then obtain x y where xy_eq: "xy = (x, y)"
            and x_in: "x \<in> \<Union> (U ` D)"
            and y_in: "y \<in> \<Inter> (V ` D)"
            by blast
          obtain d where dD: "d \<in> D" and xUd: "x \<in> U d"
            using x_in by auto
          have yVd: "y \<in> V d"
            using y_in dD by auto
          have UdVd_strip: "U d \<times> V d \<subseteq> (({a..b} \<times> {0..1}) \<inter> h -` S)"
            using D(2) UV dD by blast
          have "(x, y) \<in> U d \<times> V d"
            using xUd yVd by auto
          then have "(x, y) \<in> (({a..b} \<times> {0..1}) \<inter> h -` S)"
            using UdVd_strip by blast
          then show "xy \<in> (({a..b} \<times> {0..1}) \<inter> h -` S)"
            using xy_eq by simp
        qed
      qed
    qed
    have stripN0: "{a..b} \<times> N \<subseteq> (({a..b} \<times> {0..1}) \<inter> h -` S)"
      using M_cover MN_strip by blast
    show thesis
      by (rule that[of N], rule N_open, rule y0N, use stripN0 in auto)
  qed
  show ?thesis
  proof (intro exI conjI)
    show "openin (top_of_set {0..1}) N"
      by (rule N_open)
    show "y0 \<in> N"
      by (rule y0N)
    show "h ` ({a..b} \<times> N) \<subseteq> S"
      using stripN by auto
  qed
qed

lemma svk_partition_local_neighbourhood:
  fixes h :: "(real \<times> real) \<Rightarrow> 'a"
  assumes h_cont: "continuous_map (top_of_set ({0..1} \<times> {0..1})) (top_of_set W) h"
    and y0_01: "y0 \<in> {0..1}"
    and part: "svk_partition (\<lambda>x. h (x, y0)) ts bs"
  shows "\<exists>N. openin (top_of_set {0..1}) N \<and> y0 \<in> N \<and>
    (\<forall>x\<in>set ts. h ` ({x} \<times> N) \<subseteq> U \<inter> V) \<and>
    (\<forall>y z. y \<le> z \<longrightarrow> {y..z} \<subseteq> N \<longrightarrow> rectangle_partition h y z ts bs)"
  using part
proof (induction ts arbitrary: bs)
  case Nil
  then show ?case
    by simp
next
  case (Cons t ts)
  show ?case
  proof (cases ts)
    case Nil
    have bs_nil: "bs = []"
      using Cons.prems Nil by (cases bs) simp_all
    have t1: "t = 1"
      using Cons.prems Nil bs_nil by simp
    have t01: "t \<in> {0..1}"
      using t1 by simp
    have tt: "t \<le> t"
      by simp
    have point_row: "h ` ({t..t} \<times> {y0}) \<subseteq> U \<inter> V"
      using Cons.prems Nil bs_nil y0_01 by auto
    have UV_open: "open (U \<inter> V)"
      using U_open V_open by auto
    have point_neigh:
      "\<exists>N. openin (top_of_set {0..1}) N \<and> y0 \<in> N \<and> h ` ({t..t} \<times> N) \<subseteq> U \<inter> V"
      by (rule strip_neighbourhood[where a = t and b = t and S = "U \<inter> V", OF h_cont t01 t01 y0_01 tt point_row UV_open])
    then obtain N where N_open: "openin (top_of_set {0..1}) N"
      and y0N: "y0 \<in> N"
      and pointN: "h ` ({t..t} \<times> N) \<subseteq> U \<inter> V"
      by blast
    show ?thesis
    proof (intro exI conjI ballI allI impI)
      show "openin (top_of_set {0..1}) N"
        by (rule N_open)
      show "y0 \<in> N"
        by (rule y0N)
      show "h ` ({x} \<times> N) \<subseteq> U \<inter> V" if "x \<in> set (t # ts)" for x
        using that Nil pointN by auto
      show "rectangle_partition h y z (t # ts) bs" if "y \<le> z" "{y..z} \<subseteq> N" for y z
        using t1 Nil bs_nil by simp
    qed
  next
    case (Cons u us)
    obtain b bs' where bs: "bs = b # bs'"
      using Cons.prems Cons by (cases bs) auto
    have t01: "t \<in> {0..1}" and u01: "u \<in> {0..1}" and tu: "t < u"
      and seg_side:
        "(if b
          then subpathin t u (\<lambda>x. h (x, y0)) ` {0..1} \<subseteq> U
          else subpathin t u (\<lambda>x. h (x, y0)) ` {0..1} \<subseteq> V)"
      and tail: "svk_partition (\<lambda>x. h (x, y0)) (u # us) bs'"
      and ptUV: "h (t, y0) \<in> U \<inter> V"
      using Cons.prems Cons bs by simp_all
    have seg_row: "h ` ({t..u} \<times> {y0}) \<subseteq> (if b then U else V)"
    proof -
      have seg_image: "(\<lambda>x. h (x, y0)) ` {t..u} \<subseteq> (if b then U else V)"
        using seg_side tu by (cases b) (auto simp: subpathin_image_eq)
      show ?thesis
      proof
        fix z
        assume z_in: "z \<in> h ` ({t..u} \<times> {y0})"
        then obtain x where x_in: "x \<in> {t..u}" and z_eq: "z = h (x, y0)"
          by auto
        have "h (x, y0) \<in> (if b then U else V)"
        proof (cases b)
          case True
          then show ?thesis
            using seg_image x_in by auto
        next
          case False
          then show ?thesis
            using seg_image x_in by auto
        qed
        then show "z \<in> (if b then U else V)"
          using z_eq by simp
      qed
    qed
    have point_row: "h ` ({t..t} \<times> {y0}) \<subseteq> U \<inter> V"
      using ptUV by auto
    obtain Nseg where Nseg_open: "openin (top_of_set {0..1}) Nseg"
      and y0Nseg: "y0 \<in> Nseg"
      and segN: "h ` ({t..u} \<times> Nseg) \<subseteq> (if b then U else V)"
    proof (cases b)
      case True
      have seg_rowU: "h ` ({t..u} \<times> {y0}) \<subseteq> U"
        using seg_row True by simp
      obtain Nseg where Nseg_open0: "openin (top_of_set {0..1}) Nseg"
        and y0Nseg0: "y0 \<in> Nseg"
        and segN0: "h ` ({t..u} \<times> Nseg) \<subseteq> U"
        using strip_neighbourhood[OF h_cont t01 u01 y0_01 less_imp_le[OF tu] seg_rowU U_open] by blast
      show thesis
      proof (rule that[of Nseg])
        show "openin (top_of_set {0..1}) Nseg"
          by (rule Nseg_open0)
        show "y0 \<in> Nseg"
          by (rule y0Nseg0)
        show "h ` ({t..u} \<times> Nseg) \<subseteq> (if b then U else V)"
          using True segN0 by simp
      qed
    next
      case False
      have seg_rowV: "h ` ({t..u} \<times> {y0}) \<subseteq> V"
        using seg_row False by simp
      obtain Nseg where Nseg_open0: "openin (top_of_set {0..1}) Nseg"
        and y0Nseg0: "y0 \<in> Nseg"
        and segN0: "h ` ({t..u} \<times> Nseg) \<subseteq> V"
        using strip_neighbourhood[OF h_cont t01 u01 y0_01 less_imp_le[OF tu] seg_rowV V_open] by blast
      show thesis
      proof (rule that[of Nseg])
        show "openin (top_of_set {0..1}) Nseg"
          by (rule Nseg_open0)
        show "y0 \<in> Nseg"
          by (rule y0Nseg0)
        show "h ` ({t..u} \<times> Nseg) \<subseteq> (if b then U else V)"
          using False segN0 by simp
      qed
    qed
    obtain Nt where Nt_open: "openin (top_of_set {0..1}) Nt"
      and y0Nt: "y0 \<in> Nt"
      and pointN: "h ` ({t..t} \<times> Nt) \<subseteq> U \<inter> V"
      using strip_neighbourhood[OF h_cont t01 t01 y0_01 order_refl point_row] U_open V_open by blast
    obtain Ntail where Ntail_open: "openin (top_of_set {0..1}) Ntail"
      and y0Ntail: "y0 \<in> Ntail"
      and tail_points_raw: "\<forall>x\<in>set ts. h ` ({x} \<times> Ntail) \<subseteq> U \<inter> V"
      and tail_rect_raw:
        "\<forall>y z. y \<le> z \<longrightarrow> {y..z} \<subseteq> Ntail \<longrightarrow> rectangle_partition h y z ts bs'"
    proof -
      have tail_ts: "svk_partition (\<lambda>x. h (x, y0)) ts bs'"
        using tail Cons by simp
      obtain N where N_open: "openin (top_of_set {0..1}) N"
        and y0N: "y0 \<in> N"
        and pointsN: "\<forall>x\<in>set ts. h ` ({x} \<times> N) \<subseteq> U \<inter> V"
        and rectN:
          "\<forall>y z. y \<le> z \<longrightarrow> {y..z} \<subseteq> N \<longrightarrow> rectangle_partition h y z ts bs'"
        using Cons.IH[OF tail_ts] by blast
      show thesis
      proof (rule that[of N])
        show "openin (top_of_set {0..1}) N"
          by (rule N_open)
        show "y0 \<in> N"
          by (rule y0N)
        show "\<forall>x\<in>set ts. h ` ({x} \<times> N) \<subseteq> U \<inter> V"
          by (rule pointsN)
        show "\<forall>y z. y \<le> z \<longrightarrow> {y..z} \<subseteq> N \<longrightarrow> rectangle_partition h y z ts bs'"
          by (rule rectN)
      qed
    qed
    have tail_points: "\<forall>x\<in>set (u # us). h ` ({x} \<times> Ntail) \<subseteq> U \<inter> V"
      using tail_points_raw Cons by simp
    have tail_rect:
      "\<forall>y z. y \<le> z \<longrightarrow> {y..z} \<subseteq> Ntail \<longrightarrow> rectangle_partition h y z (u # us) bs'"
      using tail_rect_raw Cons by simp
    let ?N = "Nseg \<inter> Nt \<inter> Ntail"
    have N_open: "openin (top_of_set {0..1}) ?N"
      by (intro openin_Int Nseg_open Nt_open Ntail_open)
    have y0N: "y0 \<in> ?N"
      using y0Nseg y0Nt y0Ntail by auto
    have points:
      "h ` ({x} \<times> ?N) \<subseteq> U \<inter> V" if x_in: "x \<in> set (t # u # us)" for x
    proof (cases "x = t")
      case True
      have point_t: "h ` ({t..t} \<times> Nt) \<subseteq> U \<inter> V"
        by (rule pointN)
      have subset_t: "{x} \<times> ?N \<subseteq> {t..t} \<times> Nt"
        using True by auto
      have img_subset_t: "h ` ({x} \<times> ?N) \<subseteq> h ` ({t..t} \<times> Nt)"
        by (rule image_mono[OF subset_t])
      show ?thesis
        using img_subset_t point_t by blast
    next
      case False
      then have "x \<in> set (u # us)"
        using x_in by auto
      then have point_x: "h ` ({x} \<times> Ntail) \<subseteq> U \<inter> V"
        using tail_points by blast
      have subset_x: "{x} \<times> ?N \<subseteq> {x} \<times> Ntail"
        by auto
      have img_subset_x: "h ` ({x} \<times> ?N) \<subseteq> h ` ({x} \<times> Ntail)"
        by (rule image_mono[OF subset_x])
      show ?thesis
        using img_subset_x point_x by blast
    qed
    have rect:
      "rectangle_partition h y z (t # u # us) (b # bs')"
      if yz: "y \<le> z" and yzN: "{y..z} \<subseteq> ?N" for y z
    proof -
      have yzNseg: "{y..z} \<subseteq> Nseg"
        using yzN by auto
      have seg_rect: "h ` ({t..u} \<times> {y..z}) \<subseteq> (if b then U else V)"
      proof (cases b)
        case True
        have prod_subset: "{t..u} \<times> {y..z} \<subseteq> {t..u} \<times> Nseg"
          using yzNseg by auto
        have "h ` ({t..u} \<times> {y..z}) \<subseteq> h ` ({t..u} \<times> Nseg)"
          by (rule image_mono[OF prod_subset])
        also have "... \<subseteq> U"
          using segN True by simp
        finally show ?thesis
          using True by simp
      next
        case False
        have prod_subset: "{t..u} \<times> {y..z} \<subseteq> {t..u} \<times> Nseg"
          using yzNseg by auto
        have "h ` ({t..u} \<times> {y..z}) \<subseteq> h ` ({t..u} \<times> Nseg)"
          by (rule image_mono[OF prod_subset])
        also have "... \<subseteq> V"
          using segN False by simp
        finally show ?thesis
          using False by simp
      qed
      have tail_rect': "rectangle_partition h y z (u # us) bs'"
        by (rule tail_rect[rule_format, OF yz]) (use yzN in auto)
      show ?thesis
        using t01 u01 tu seg_rect tail_rect' by (cases b) simp_all
    qed
    show ?thesis
    proof (intro exI conjI ballI allI impI)
      show "openin (top_of_set {0..1}) ?N"
        by (rule N_open)
      show "y0 \<in> ?N"
        by (rule y0N)
      show "h ` ({x} \<times> ?N) \<subseteq> U \<inter> V" if "x \<in> set (t # ts)" for x
        using that Cons points by simp
      show "rectangle_partition h y z (t # ts) bs" if "y \<le> z" "{y..z} \<subseteq> ?N" for y z
        using rect[OF that] Cons bs by simp
    qed
  qed
qed

lemma rectangle_partition_svk_partition_row:
  fixes h :: "(real \<times> real) \<Rightarrow> 'a"
  assumes part: "rectangle_partition h c d ts bs"
    and edgeUV: "\<And>x. x \<in> set ts \<Longrightarrow> h ` ({x} \<times> {c..d}) \<subseteq> U \<inter> V"
    and y_in: "y \<in> {c..d}"
  shows "svk_partition (\<lambda>x. h (x, y)) ts bs"
  using part edgeUV
proof (induction ts arbitrary: bs)
  case Nil
  then show ?case
    by simp
next
  case (Cons t ts)
  show ?case
  proof (cases ts)
    case Nil
    have bs_nil: "bs = []"
      using Cons.prems Nil by (cases bs) simp_all
    have t1: "t = 1"
      using Cons.prems Nil bs_nil by simp
    have ptUV: "h (t, y) \<in> U \<inter> V"
    proof -
      have t_edge: "h ` ({t} \<times> {c..d}) \<subseteq> U \<inter> V"
        using Cons.prems(2)[of t] Nil by simp
      have "(t, y) \<in> {t} \<times> {c..d}"
        using y_in by auto
      then show ?thesis
        using t_edge by auto
    qed
    then show ?thesis
      using Nil bs_nil t1 by simp
  next
    case (Cons u us)
    obtain b bs' where bs: "bs = b # bs'"
      using Cons.prems Cons by (cases bs) auto
    have t01: "t \<in> {0..1}" and u01: "u \<in> {0..1}" and tu: "t < u"
      and rect_side: "(if b then h ` ({t..u} \<times> {c..d}) \<subseteq> U else h ` ({t..u} \<times> {c..d}) \<subseteq> V)"
      and tail: "rectangle_partition h c d (u # us) bs'"
      using Cons.prems Cons bs by simp_all
    have edge_t: "h ` ({t} \<times> {c..d}) \<subseteq> U \<inter> V"
      using Cons.prems(2)[of t] Cons by simp
    have ptUV: "h (t, y) \<in> U \<inter> V"
    proof -
      have "(t, y) \<in> {t} \<times> {c..d}"
        using y_in by auto
      then show ?thesis
        using edge_t by auto
    qed
    have seg_side:
      "(if b
        then subpathin t u (\<lambda>x. h (x, y)) ` {0..1} \<subseteq> U
        else subpathin t u (\<lambda>x. h (x, y)) ` {0..1} \<subseteq> V)"
    proof -
      have row_subset: "{t..u} \<times> {y} \<subseteq> {t..u} \<times> {c..d}"
        using y_in by auto
      have row_rect: "h ` ({t..u} \<times> {y}) \<subseteq> (if b then U else V)"
      proof (cases b)
        case True
        have "h ` ({t..u} \<times> {y}) \<subseteq> h ` ({t..u} \<times> {c..d})"
          by (rule image_mono[OF row_subset])
        also have "... \<subseteq> U"
          using rect_side True by simp
        finally show ?thesis
          using True by simp
      next
        case False
        have "h ` ({t..u} \<times> {y}) \<subseteq> h ` ({t..u} \<times> {c..d})"
          by (rule image_mono[OF row_subset])
        also have "... \<subseteq> V"
          using rect_side False by simp
        finally show ?thesis
          using False by simp
      qed
      then show ?thesis
        using tu by (cases b) (auto simp: subpathin_image_eq)
    qed
    have tail_svk_ts: "svk_partition (\<lambda>x. h (x, y)) ts bs'"
    proof (rule Cons.IH[where bs = bs'])
      show "rectangle_partition h c d ts bs'"
        using tail Cons by simp
      show "\<And>x. x \<in> set ts \<Longrightarrow> h ` ({x} \<times> {c..d}) \<subseteq> U \<inter> V"
      proof -
        fix x
        assume x_in: "x \<in> set ts"
        have "x \<in> set (t # ts)"
          using x_in by simp
        then show "h ` ({x} \<times> {c..d}) \<subseteq> U \<inter> V"
          using Cons.prems(2) by blast
      qed
    qed
    have tail_svk: "svk_partition (\<lambda>x. h (x, y)) (u # us) bs'"
      using tail_svk_ts Cons by simp
    have step_svk: "svk_partition (\<lambda>x. h (x, y)) (t # u # us) (b # bs')"
      using t01 u01 tu seg_side ptUV tail_svk by simp
    show ?thesis
      using step_svk Cons bs by simp
  qed
qed

lemma rectangle_partition_valid_partition_row:
  fixes h :: "(real \<times> real) \<Rightarrow> 'a"
  assumes part: "rectangle_partition h c d ts bs"
    and edgeUV: "\<And>x. x \<in> set ts \<Longrightarrow> h ` ({x} \<times> {c..d}) \<subseteq> U \<inter> V"
    and y_in: "y \<in> {c..d}"
    and ts_ne: "ts \<noteq> []"
    and hd0: "hd ts = 0"
  shows "valid_partition (\<lambda>x. h (x, y)) ts bs"
  unfolding valid_partition_def
  using rectangle_partition_svk_partition_row[OF part edgeUV y_in] ts_ne hd0 by simp

lemma homotopy_row_in_loop_space:
  fixes h :: "(real \<times> real) \<Rightarrow> 'a"
  assumes h_cont: "continuous_map (top_of_set ({0..1} \<times> {0..1})) (top_of_set W) h"
    and y01: "y \<in> {0..1}"
    and start: "h (0, y) = x0"
    and finish: "h (1, y) = x0"
  shows "(\<lambda>x. h (x, y)) \<in> loop_space W x0"
proof -
  have h_on: "continuous_on ({0..1} \<times> {0..1}) h"
    and h_into: "h \<in> ({0..1} \<times> {0..1}) \<rightarrow> W"
    using h_cont by simp_all
  have row_cont: "continuous_on {0..1} (\<lambda>x. h (x, y))"
  proof (rule continuous_on_compose2[OF h_on])
    show "continuous_on {0..1} (\<lambda>x. (x, y))"
      by (intro continuous_intros)
    show "(\<lambda>x. (x, y)) ` {0..1} \<subseteq> {0..1} \<times> {0..1}"
      using y01 by auto
  qed
  have row_path: "path (\<lambda>x. h (x, y))"
    using row_cont by (simp add: path_def)
  have row_img: "path_image (\<lambda>x. h (x, y)) \<subseteq> W"
    using h_into y01 by (auto simp: path_image_def)
  show ?thesis
    unfolding loop_space_def pathstart_def pathfinish_def
    using row_path row_img start finish by simp
qed

lemma bridge_word_one_equiv:
  assumes rest_in: "fpw_in_space G1 G2 rest"
  shows "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2
      (bridge_word b (fundamental_group_one (U \<inter> V) x0) rest) rest"
proof (cases b)
  case True
  have i1_one: "i1 (fundamental_group_one (U \<inter> V) x0) = one1"
    by (rule fundamental_group_map_one[OF x0_in_UV]) auto
  have one1_in: "one1 \<in> G1"
    by (rule fundamental_group_one_in_space[OF x0_in_U])
  have red:
    "carrier_fpw_reduction G1 G2 mult1 one1 mult2 one2
      (WordLeft one1 rest) rest"
    by (rule carrier_fpw_reduction.step,
        rule carrier_fpw_reduction_step.remove_left_one[OF one1_in], rule rest_in)
  show ?thesis
    using True i1_one by (simp add: carrier_full_amalg_equiv.of_reduction[OF red])
next
  case False
  have i2_one: "i2 (fundamental_group_one (U \<inter> V) x0) = one2"
    by (rule fundamental_group_map_one[OF x0_in_UV]) auto
  have one2_in: "one2 \<in> G2"
    by (rule fundamental_group_one_in_space[OF x0_in_V])
  have red:
    "carrier_fpw_reduction G1 G2 mult1 one1 mult2 one2
      (WordRight one2 rest) rest"
    by (rule carrier_fpw_reduction.step,
        rule carrier_fpw_reduction_step.remove_right_one[OF one2_in], rule rest_in)
  show ?thesis
    using False i2_one by (simp add: carrier_full_amalg_equiv.of_reduction[OF red])
qed

lemma partition_word_with_tail_respects:
  assumes p_loop: "p \<in> loop_space W x0"
    and part: "svk_partition p ts bs"
    and rel: "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2 r s"
  shows "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2
      (partition_word_with_tail p ts bs r)
      (partition_word_with_tail p ts bs s)"
  using part rel
proof (induction ts arbitrary: bs r s)
  case Nil
  then show ?case
    by simp
next
  case (Cons t ts)
  from p_loop have p_path: "path p" and p_img: "path_image p \<subseteq> W"
    unfolding loop_space_def by auto
  show ?case
  proof (cases ts)
    case Nil
    have bs_nil: "bs = []"
      using Cons.prems Nil by (cases bs) simp_all
    have pw_r: "partition_word_with_tail p (t # ts) bs r = r"
      using Nil bs_nil by simp
    have pw_s: "partition_word_with_tail p (t # ts) bs s = s"
      using Nil bs_nil by simp
    show ?thesis
      unfolding pw_r pw_s
      by (rule Cons.prems(2))
  next
    case (Cons u us)
    obtain b bs' where bs: "bs = b # bs'"
      using Cons.prems(1) Cons by (cases bs) auto
    have tail: "svk_partition p (u # us) bs'"
      using Cons.prems(1) Cons bs by simp
    have ts_eq: "ts = u # us"
      using Cons by simp
    have tail_rel_ts:
      "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2
        (partition_word_with_tail p ts bs' r)
        (partition_word_with_tail p ts bs' s)"
      by (rule Cons.IH) (use tail Cons.prems(2) ts_eq in simp_all)
    have tail_rel:
      "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2
        (partition_word_with_tail p (u # us) bs' r)
        (partition_word_with_tail p (u # us) bs' s)"
      using tail_rel_ts ts_eq by simp
    have i1_back: "fundamental_group_map (U \<inter> V) x0 U x0 id = i1"
      by simp
    have i2_back: "fundamental_group_map (U \<inter> V) x0 V x0 id = i2"
      by simp
    have t01: "t \<in> {0..1}" and ptUV: "p t \<in> U \<inter> V"
      using Cons.prems(1) Cons bs by simp_all
    have u01: "u \<in> {0..1}" and seg_side:
      "(if b then subpathin t u p ` {0..1} \<subseteq> U else subpathin t u p ` {0..1} \<subseteq> V)"
      using Cons.prems(1) Cons bs by simp_all
    have puUV: "p u \<in> U \<inter> V"
      using Cons.prems(1) Cons bs svk_partition_next_in_intersection[of p t u us b bs'] by simp
    show ?thesis
    proof (cases b)
      case True
      have segU: "segment_loop p t u \<in> loop_space U x0"
        by (rule segment_loop_in_U[OF p_path p_img t01 u01 ptUV puUV]) (use seg_side True in auto)
      have class_in: "loop_class U x0 (segment_loop p t u) \<in> G1"
        by (rule loop_class_in_space[OF segU])
      have ctx_rel:
        "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2
          (WordLeft (loop_class U x0 (segment_loop p t u))
            (partition_word_with_tail p (u # us) bs' r))
          (WordLeft (loop_class U x0 (segment_loop p t u))
            (partition_word_with_tail p (u # us) bs' s))"
        by (rule carrier_full_amalg_equiv_left_context[OF tail_rel class_in])
      show ?thesis
        using True ts_eq ctx_rel
        by (subst i1_back, subst i2_back, simp add: bs)
    next
      case False
      have segV: "segment_loop p t u \<in> loop_space V x0"
        by (rule segment_loop_in_V[OF p_path p_img t01 u01 ptUV puUV]) (use seg_side False in auto)
      have class_in: "loop_class V x0 (segment_loop p t u) \<in> G2"
        by (rule loop_class_in_space[OF segV])
      have ctx_rel:
        "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2
          (WordRight (loop_class V x0 (segment_loop p t u))
            (partition_word_with_tail p (u # us) bs' r))
          (WordRight (loop_class V x0 (segment_loop p t u))
            (partition_word_with_tail p (u # us) bs' s))"
        by (rule carrier_full_amalg_equiv_right_context[OF tail_rel class_in])
      show ?thesis
        using False ts_eq ctx_rel
        by (subst i1_back, subst i2_back, simp add: bs)
    qed
  qed
qed

lemma valid_partition_tail_bridge_one_equiv:
  assumes p_loop: "p \<in> loop_space W x0"
    and part: "valid_partition p (t # u # ts) (b # bs)"
  shows "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2
      (partition_word_with_tail p (t # u # ts) (b # bs)
        (bridge_word (last (b # bs)) (fundamental_group_one (U \<inter> V) x0) WordNil))
      (partition_word p (t # u # ts) (b # bs))"
proof -
  have svk: "svk_partition p (t # u # ts) (b # bs)"
    using part by (rule valid_partition_cases(2))
  have tail_rel:
    "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2
      (partition_word_with_tail p (t # u # ts) (b # bs)
        (bridge_word (last (b # bs)) (fundamental_group_one (U \<inter> V) x0) WordNil))
      (partition_word_with_tail p (t # u # ts) (b # bs) WordNil)"
    by (rule partition_word_with_tail_respects[OF p_loop svk bridge_word_one_equiv]) simp
  then show ?thesis
    by simp
qed

lemma bridge_loop_constant_one:
  fixes h :: "(real \<times> real) \<Rightarrow> 'a"
  assumes h_cont: "continuous_map (top_of_set ({0..1} \<times> {0..1})) (top_of_set W) h"
    and t01: "t \<in> {0..1}"
    and c01: "c \<in> {0..1}"
    and d01: "d \<in> {0..1}"
    and cd: "c \<le> d"
    and const: "\<forall>y\<in>{c..d}. h (t, y) = x0"
  shows "loop_class (U \<inter> V) x0 (bridge_loop h t c d) = fundamental_group_one (U \<inter> V) x0"
proof -
  have edgeUV: "h ` ({t} \<times> {c..d}) \<subseteq> U \<inter> V"
    using const x0_in_UV by auto
  have bridge_loop_in: "bridge_loop h t c d \<in> loop_space (U \<inter> V) x0"
    by (rule vertical_bridge_loop_in_set[OF h_cont t01 c01 d01 cd edgeUV]) simp
  have hc: "h (t, c) = x0" and hd: "h (t, d) = x0"
    using const cd by auto
  have conn_c_img: "path_image (connector (h (t, c))) \<subseteq> {x0}"
    using hc by (auto simp: path_image_def connector_def)
  have conn_d_img: "path_image (reversepath (connector (h (t, d)))) \<subseteq> {x0}"
    using hd by (auto simp: path_image_def connector_def reversepath_def)
  have vert_img: "path_image (vertical_strip_path h t c d) \<subseteq> {x0}"
  proof -
    have vert_img_raw: "vertical_strip_path h t c d ` {0..1} \<subseteq> {x0}"
    proof
      fix x
      assume "x \<in> vertical_strip_path h t c d ` {0..1}"
      then obtain u where u01: "u \<in> {0..1}" and x_eq: "x = vertical_strip_path h t c d u"
        by blast
      have "(d - c) * u + c \<in> {c..d}"
        by (rule affine_subinterval_member[OF cd u01])
      then show "x \<in> {x0}"
        using const x_eq by (auto simp: vertical_strip_path_def)
    qed
    from vert_img_raw show ?thesis
      by (simp add: path_image_def)
  qed
  have join_img:
    "path_image (connector (h (t, c)) +++ vertical_strip_path h t c d) \<subseteq> {x0}"
    by (rule subset_path_image_join[OF conn_c_img vert_img])
  have bridge_img_single: "path_image (bridge_loop h t c d) \<subseteq> {x0}"
    unfolding bridge_loop_def by (rule subset_path_image_join[OF join_img conn_d_img])
  have bridge_path: "path (bridge_loop h t c d)"
    and bridge_img: "path_image (bridge_loop h t c d) \<subseteq> U \<inter> V"
    using bridge_loop_in unfolding loop_space_def by auto
  have bridge_const:
    "homotopic_paths (U \<inter> V) (bridge_loop h t c d) (\<lambda>_. x0)"
  proof (rule homotopic_paths_eq[OF bridge_path bridge_img])
    fix u :: real
    assume u01: "u \<in> {0..1}"
    then have "bridge_loop h t c d u \<in> path_image (bridge_loop h t c d)"
      by (auto simp: path_image_def)
    then show "bridge_loop h t c d u = x0"
      using bridge_img_single by auto
  qed
  show ?thesis
    unfolding fundamental_group_one_def
    by (rule loop_class_eqI[OF bridge_loop_in constant_loop_in_space[OF x0_in_UV] bridge_const])
qed

lemma rectangle_partition_partition_word_equiv:
  fixes h :: "(real \<times> real) \<Rightarrow> 'a"
  assumes h_cont: "continuous_map (top_of_set ({0..1} \<times> {0..1})) (top_of_set W) h"
    and c01: "c \<in> {0..1}"
    and d01: "d \<in> {0..1}"
    and cd: "c \<le> d"
    and part: "rectangle_partition h c d ts bs"
    and ts_ne: "ts \<noteq> []"
    and hd0: "hd ts = 0"
    and edgeUV: "\<And>x. x \<in> set ts \<Longrightarrow> h ` ({x} \<times> {c..d}) \<subseteq> U \<inter> V"
    and end0: "\<forall>y\<in>{c..d}. h (0, y) = x0"
    and end1: "\<forall>y\<in>{c..d}. h (1, y) = x0"
  shows "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2
      (partition_word (\<lambda>x. h (x, c)) ts bs)
      (partition_word (\<lambda>x. h (x, d)) ts bs)"
proof -
  have rowc_loop: "(\<lambda>x. h (x, c)) \<in> loop_space W x0"
    by (rule homotopy_row_in_loop_space[OF h_cont c01]) (use end0 end1 cd in auto)
  have rowd_loop: "(\<lambda>x. h (x, d)) \<in> loop_space W x0"
    by (rule homotopy_row_in_loop_space[OF h_cont d01]) (use end0 end1 cd in auto)
  have valid_c: "valid_partition (\<lambda>x. h (x, c)) ts bs"
    by (rule rectangle_partition_valid_partition_row[OF part edgeUV _ ts_ne hd0]) (use c01 cd in auto)
  have valid_d: "valid_partition (\<lambda>x. h (x, d)) ts bs"
    by (rule rectangle_partition_valid_partition_row[OF part edgeUV _ ts_ne hd0]) (use d01 cd in auto)
  obtain t ts' where ts: "ts = t # ts'"
    using ts_ne by (cases ts) auto
  have valid_c_ts: "valid_partition (\<lambda>x. h (x, c)) ts bs"
    using valid_c by simp
  have t0: "t = 0"
    using valid_c_ts unfolding ts by (rule valid_partition_cases(1))
  have svk_c: "svk_partition (\<lambda>x. h (x, c)) (t # ts') bs"
    using valid_c_ts unfolding ts by (rule valid_partition_cases(2))
  have ts'_ne: "ts' \<noteq> []"
  proof
    assume "ts' = []"
    with svk_c t0 show False
      by (cases bs) auto
  qed
  obtain u us where ts': "ts' = u # us"
    using ts'_ne by (cases ts') auto
  obtain b bs' where bs: "bs = b # bs'"
    using svk_c ts' by (cases bs) auto
  have part_shape: "rectangle_partition h c d (t # u # us) (b # bs')"
    using part unfolding ts ts' bs by simp
  have last1: "last (t # u # us) = 1"
    using valid_partition_last_props[OF valid_c] unfolding ts ts' by simp
  have rowd_in:
    "fpw_in_space G1 G2 (partition_word (\<lambda>x. h (x, d)) (t # u # us) (b # bs'))"
    by (rule valid_partition_partition_word_in_space[OF rowd_loop]) (use valid_d ts ts' bs in simp)
  have edgeUV_shape:
    "\<And>x. x \<in> set (t # u # us) \<Longrightarrow> h ` ({x} \<times> {c..d}) \<subseteq> U \<inter> V"
    using edgeUV unfolding ts ts' by simp
  have wordnil_in: "fpw_in_space G1 G2 WordNil"
    by simp
  have rect_rel_raw:
    "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2
      (partition_word_with_tail (\<lambda>x. h (x, c)) (t # u # us) (b # bs')
        (bridge_word (last (b # bs'))
          (loop_class (U \<inter> V) x0 (bridge_loop h (last (t # u # us)) c d)) WordNil))
      (bridge_word b (loop_class (U \<inter> V) x0 (bridge_loop h t c d))
        (partition_word_with_tail (\<lambda>x. h (x, d)) (t # u # us) (b # bs') WordNil))"
    by (rule rectangle_partition_partition_word_with_tail_equiv[OF h_cont c01 d01 cd part_shape edgeUV_shape wordnil_in])
  have rect_rel:
    "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2
      (partition_word_with_tail (\<lambda>x. h (x, c)) (t # u # us) (b # bs')
        (bridge_word (last (b # bs'))
          (loop_class (U \<inter> V) x0 (bridge_loop h (last (t # u # us)) c d)) WordNil))
      (bridge_word b (loop_class (U \<inter> V) x0 (bridge_loop h t c d))
        (partition_word (\<lambda>x. h (x, d)) (t # u # us) (b # bs')))"
    using rect_rel_raw by simp
  have start_one:
    "loop_class (U \<inter> V) x0 (bridge_loop h t c d) = fundamental_group_one (U \<inter> V) x0"
    by (subst t0, rule bridge_loop_constant_one[OF h_cont]) (use c01 d01 cd end0 in auto)
  have end_one:
    "loop_class (U \<inter> V) x0 (bridge_loop h (last (t # u # us)) c d) =
      fundamental_group_one (U \<inter> V) x0"
    by (subst last1, rule bridge_loop_constant_one[OF h_cont]) (use c01 d01 cd end1 in auto)
  have rect_rel':
    "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2
      (partition_word_with_tail (\<lambda>x. h (x, c)) (t # u # us) (b # bs')
        (bridge_word (last (b # bs')) (fundamental_group_one (U \<inter> V) x0) WordNil))
      (bridge_word b (fundamental_group_one (U \<inter> V) x0)
        (partition_word (\<lambda>x. h (x, d)) (t # u # us) (b # bs')))"
  proof (cases b)
    case True
    then show ?thesis
      using rect_rel start_one end_one by simp
  next
    case False
    then show ?thesis
      using rect_rel start_one end_one by simp
  qed
  have tail_rel:
    "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2
      (partition_word_with_tail (\<lambda>x. h (x, c)) (t # u # us) (b # bs')
        (bridge_word (last (b # bs')) (fundamental_group_one (U \<inter> V) x0) WordNil))
      (partition_word (\<lambda>x. h (x, c)) (t # u # us) (b # bs'))"
    by (rule valid_partition_tail_bridge_one_equiv[OF rowc_loop]) (use valid_c ts ts' bs in simp)
  have prefix_rel:
    "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2
      (bridge_word b (fundamental_group_one (U \<inter> V) x0)
        (partition_word (\<lambda>x. h (x, d)) (t # u # us) (b # bs')))
      (partition_word (\<lambda>x. h (x, d)) (t # u # us) (b # bs'))"
    by (rule bridge_word_one_equiv[OF rowd_in])
  have step1:
    "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2
      (partition_word (\<lambda>x. h (x, c)) (t # u # us) (b # bs'))
      (partition_word_with_tail (\<lambda>x. h (x, c)) (t # u # us) (b # bs')
        (bridge_word (last (b # bs')) (fundamental_group_one (U \<inter> V) x0) WordNil))"
    by (rule carrier_full_amalg_equiv.sym[OF tail_rel])
  have step2:
    "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2
      (partition_word (\<lambda>x. h (x, c)) (t # u # us) (b # bs'))
      (bridge_word b (fundamental_group_one (U \<inter> V) x0)
        (partition_word (\<lambda>x. h (x, d)) (t # u # us) (b # bs')))"
    by (rule carrier_full_amalg_equiv.trans[OF step1 rect_rel'])
  have step3:
    "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2
      (partition_word (\<lambda>x. h (x, c)) (t # u # us) (b # bs'))
      (partition_word (\<lambda>x. h (x, d)) (t # u # us) (b # bs'))"
    by (rule carrier_full_amalg_equiv.trans[OF step2 prefix_rel])
  then show ?thesis
    using ts ts' bs by simp
qed

lemma valid_partition_nearby_partition_word_equiv:
  fixes h :: "(real \<times> real) \<Rightarrow> 'a"
  assumes h_cont: "continuous_map (top_of_set ({0..1} \<times> {0..1})) (top_of_set W) h"
    and end0: "\<forall>y\<in>{0..1}. h (0, y) = x0"
    and end1: "\<forall>y\<in>{0..1}. h (1, y) = x0"
    and y0_01: "y0 \<in> {0..1}"
    and part0: "valid_partition (\<lambda>x. h (x, y0)) ts bs"
  shows "\<exists>e>0. \<forall>z\<in>{0..1}. dist z y0 < e \<longrightarrow>
    valid_partition (\<lambda>x. h (x, z)) ts bs \<and>
    carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2
      (partition_word (\<lambda>x. h (x, y0)) ts bs)
      (partition_word (\<lambda>x. h (x, z)) ts bs)"
proof -
  obtain t ts' where ts: "ts = t # ts'"
    using valid_partition_hd(1)[OF part0] by (cases ts) auto
  have hd_ts0: "hd ts = 0"
    by (rule valid_partition_hd(2)[OF part0])
  have valid_ts: "valid_partition (\<lambda>x. h (x, y0)) ts bs"
    using part0 by simp
  have t0: "t = 0"
    using valid_ts unfolding ts by (rule valid_partition_cases(1))
  have svk0: "svk_partition (\<lambda>x. h (x, y0)) (t # ts') bs"
    using valid_ts unfolding ts by (rule valid_partition_cases(2))
  have local_neigh:
    "\<exists>N. openin (top_of_set {0..1}) N \<and> y0 \<in> N \<and>
      (\<forall>x\<in>set (t # ts'). h ` ({x} \<times> N) \<subseteq> U \<inter> V) \<and>
      (\<forall>y z. y \<le> z \<longrightarrow> {y..z} \<subseteq> N \<longrightarrow> rectangle_partition h y z (t # ts') bs)"
    by (rule svk_partition_local_neighbourhood[OF h_cont y0_01 svk0])
  obtain N where N_open: "openin (top_of_set {0..1}) N"
    and y0N: "y0 \<in> N"
    and pointN: "\<forall>x\<in>set ts. h ` ({x} \<times> N) \<subseteq> U \<inter> V"
    and rectN: "\<forall>y z. y \<le> z \<longrightarrow> {y..z} \<subseteq> N \<longrightarrow> rectangle_partition h y z ts bs"
    using local_neigh unfolding ts by blast
  from openin_euclidean_subtopology_iff[THEN iffD1, OF N_open] y0N
  obtain e where e_pos: "e > 0"
    and e_ball: "\<forall>z\<in>{0..1}. dist z y0 < e \<longrightarrow> z \<in> N"
    by blast
  show ?thesis
  proof (intro exI conjI ballI impI)
    show "e > 0"
      by (rule e_pos)
    fix z
    assume z01: "z \<in> {0..1}"
      and dz: "dist z y0 < e"
    have zN: "z \<in> N"
      by (rule e_ball[rule_format, OF z01 dz])
    have dyz: "dist y0 z < e"
      using dz by (simp add: dist_commute)
    have seg_ball: "closed_segment y0 z \<subseteq> ball y0 e"
      by (rule closed_segment_subset) (use y0_01 z01 e_pos dyz in auto)
    have seg_unit: "closed_segment y0 z \<subseteq> {0..1}"
      by (rule closed_segment_subset) (use y0_01 z01 in auto)
    have segN: "closed_segment y0 z \<subseteq> N"
    proof
      fix w
      assume wseg: "w \<in> closed_segment y0 z"
      have w01: "w \<in> {0..1}"
        using seg_unit wseg by auto
      have w_ball: "w \<in> ball y0 e"
        using seg_ball wseg by auto
      have "dist w y0 < e"
        using w_ball unfolding ball_def by (simp add: dist_commute)
      then show "w \<in> N"
        by (rule e_ball[rule_format, OF w01])
    qed
    have intervalN: "{min y0 z..max y0 z} \<subseteq> N"
    proof
      fix y
      assume y_in: "y \<in> {min y0 z..max y0 z}"
      have "y \<in> closed_segment y0 z"
      proof (cases "y0 \<le> z")
        case True
        with y_in show ?thesis
          by (simp add: closed_segment_eq_real_ivl)
      next
        case False
        with y_in show ?thesis
          by (simp add: closed_segment_eq_real_ivl)
      qed
      then show "y \<in> N"
        using segN by blast
    qed
    have edgeUV_interval:
      "h ` ({x} \<times> {min y0 z..max y0 z}) \<subseteq> U \<inter> V" if x_in: "x \<in> set ts" for x
    proof -
      have edgeN: "h ` ({x} \<times> N) \<subseteq> U \<inter> V"
        using pointN x_in by auto
      have subset_x: "{x} \<times> {min y0 z..max y0 z} \<subseteq> {x} \<times> N"
        using intervalN by auto
      show ?thesis
        by (rule order_trans[OF image_mono[OF subset_x] edgeN])
    qed
    have rect:
      "rectangle_partition h (min y0 z) (max y0 z) ts bs"
      by (rule rectN[rule_format]) (use intervalN in auto)
    have valid_z: "valid_partition (\<lambda>x. h (x, z)) ts bs"
      by (rule rectangle_partition_valid_partition_row[OF rect edgeUV_interval _ valid_partition_hd(1)[OF part0] hd_ts0])
         auto
    have min01: "min y0 z \<in> {0..1}"
      using y0_01 z01 by auto
    have max01: "max y0 z \<in> {0..1}"
      using y0_01 z01 by auto
    have interval01: "{min y0 z..max y0 z} \<subseteq> {0..1}"
      using y0_01 z01 by auto
    have end0_interval: "\<forall>y\<in>{min y0 z..max y0 z}. h (0, y) = x0"
    proof
      fix y
      assume y_in: "y \<in> {min y0 z..max y0 z}"
      then have y01: "y \<in> {0..1}"
        using interval01 by blast
      show "h (0, y) = x0"
        using end0 y01 by blast
    qed
    have end1_interval: "\<forall>y\<in>{min y0 z..max y0 z}. h (1, y) = x0"
    proof
      fix y
      assume y_in: "y \<in> {min y0 z..max y0 z}"
      then have y01: "y \<in> {0..1}"
        using interval01 by blast
      show "h (1, y) = x0"
        using end1 y01 by blast
    qed
    have part_rel_raw:
      "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2
        (partition_word (\<lambda>x. h (x, min y0 z)) ts bs)
        (partition_word (\<lambda>x. h (x, max y0 z)) ts bs)"
      by (rule rectangle_partition_partition_word_equiv[
            OF h_cont min01 max01 _ rect valid_partition_hd(1)[OF part0] hd_ts0
               edgeUV_interval end0_interval end1_interval])
         simp
    have part_rel:
      "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2
        (partition_word (\<lambda>x. h (x, y0)) ts bs)
        (partition_word (\<lambda>x. h (x, z)) ts bs)"
    proof (cases "y0 \<le> z")
      case True
      then show ?thesis
        using part_rel_raw by simp
    next
      case False
      then have "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2
          (partition_word (\<lambda>x. h (x, z)) ts bs)
          (partition_word (\<lambda>x. h (x, y0)) ts bs)"
        using part_rel_raw by simp
      then show ?thesis
        by (rule carrier_full_amalg_equiv.sym)
    qed
    show "valid_partition (\<lambda>x. h (x, z)) ts bs"
      using valid_z by simp
    show "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2
        (partition_word (\<lambda>x. h (x, y0)) ts bs)
        (partition_word (\<lambda>x. h (x, z)) ts bs)"
      using part_rel by simp
  qed
qed

definition some_valid_partition :: "(real \<Rightarrow> 'a) \<Rightarrow> real list \<times> bool list" where
  "some_valid_partition p =
    (SOME tb. case tb of (ts, bs) \<Rightarrow> valid_partition p ts bs)"

lemma some_valid_partition_spec:
  assumes p_loop: "p \<in> loop_space W x0"
  shows "valid_partition p
    (fst (some_valid_partition p))
    (snd (some_valid_partition p))"
proof -
  have ex: "\<exists>tb. case tb of (ts, bs) \<Rightarrow> valid_partition p ts bs"
    using loop_has_valid_partition[OF p_loop] by force
  have "case some_valid_partition p of (ts, bs) \<Rightarrow> valid_partition p ts bs"
    unfolding some_valid_partition_def by (rule someI_ex[OF ex])
  then show ?thesis
    by (cases "some_valid_partition p") auto
qed

subsection \<open>Homotopy invariance of the partition encoding\<close>

text \<open>
  The central technical step is that different valid partitions of homotopic
  loops produce equivalent words in the carrier-side amalgamated free product.
  The proof uses a rectangular decomposition of a homotopy and keeps the word
  encoding stable while moving from one boundary loop to the other.
\<close>

lemma valid_partition_homotopic_partition_word_equiv:
  assumes p_loop: "p \<in> loop_space W x0"
    and q_loop: "q \<in> loop_space W x0"
    and pq: "homotopic_paths W p q"
    and p_part: "valid_partition p ts bs"
    and q_part: "valid_partition q us cs"
  shows "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2
      (partition_word p ts bs) (partition_word q us cs)"
proof -
  obtain h0 :: "real \<times> real \<Rightarrow> 'a" where h0_cont: "continuous_on ({0..1} \<times> {0..1}) h0"
    and h0_into: "h0 \<in> ({0..1} \<times> {0..1}) \<rightarrow> W"
    and h0_p: "\<And>x. h0 (0, x) = p x"
    and h0_q: "\<And>x. h0 (1, x) = q x"
    and h0_left: "\<And>y. y \<in> {0..1} \<Longrightarrow> h0 (y, 0) = p 0"
    and h0_right: "\<And>y. y \<in> {0..1} \<Longrightarrow> h0 (y, 1) = p 1"
    using pq
    by (auto simp: homotopic_paths_def homotopic_with_def
                   pathstart_def pathfinish_def image_subset_iff_funcset)
  define h where "h = (\<lambda>xy. h0 (snd xy, fst xy))"
  let ?row = "\<lambda>y. \<lambda>x. h (x, y)"
  let ?enc = "\<lambda>y. case some_valid_partition (?row y) of (vs, ds) \<Rightarrow> partition_word (?row y) vs ds"
  let ?P =
    "{y \<in> {0..1}. carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2 (?enc 0) (?enc y)}"
  have p_start: "pathstart p = x0" and p_finish: "pathfinish p = x0"
    using p_loop unfolding loop_space_def by auto
  have h_cont: "continuous_map (top_of_set ({0..1} \<times> {0..1})) (top_of_set W) h"
  proof -
    have swap_cont:
      "continuous_on ({0..1} \<times> {0..1}) (\<lambda>xy. (snd xy, fst xy))"
      by (intro continuous_intros)
    have swap_in:
      "(\<lambda>xy. (snd xy, fst xy)) ` ({0..1} \<times> {0..1}) \<subseteq> ({0..1} \<times> {0..1})"
      by auto
    have h_on: "continuous_on ({0..1} \<times> {0..1}) h"
    proof -
      have "continuous_on ({0..1} \<times> {0..1}) (\<lambda>xy. h0 (snd xy, fst xy))"
        by (rule continuous_on_compose2[OF h0_cont]) (use swap_cont swap_in in auto)
      then show ?thesis
        unfolding h_def .
    qed
    have h_into: "h \<in> ({0..1} \<times> {0..1}) \<rightarrow> W"
      using h0_into unfolding h_def by auto
    show ?thesis
      using h_on h_into by simp
  qed
  have end0: "\<forall>y\<in>{0..1}. h (0, y) = x0"
  proof
    fix y :: real
    assume y01: "y \<in> {0..1}"
    have "h0 (y, 0::real) = p 0"
      by (rule h0_left[OF y01])
    then show "h (0, y) = x0"
      using p_start unfolding h_def pathstart_def by simp
  qed
  have end1: "\<forall>y\<in>{0..1}. h (1, y) = x0"
  proof
    fix y :: real
    assume y01: "y \<in> {0..1}"
    have "h0 (y, 1::real) = p 1"
      by (rule h0_right[OF y01])
    then show "h (1, y) = x0"
      using p_finish unfolding h_def pathfinish_def by simp
  qed
  have row_loop: "?row y \<in> loop_space W x0" if y01: "y \<in> {0..1}" for y
    by (rule homotopy_row_in_loop_space[OF h_cont y01]) (use end0 end1 y01 in auto)
  have openP_local: "\<forall>y0\<in>?P. \<exists>e>0. \<forall>z\<in>{0..1}. dist z y0 < e \<longrightarrow> z \<in> ?P"
  proof
    fix y0
    assume y0P: "y0 \<in> ?P"
    then have y0_01: "y0 \<in> {0..1}"
      by simp
    obtain vs ds where tb0: "some_valid_partition (?row y0) = (vs, ds)"
      by (cases "some_valid_partition (?row y0)") auto
    have part0: "valid_partition (?row y0) vs ds"
      using some_valid_partition_spec[OF row_loop[OF y0_01]] unfolding tb0 by simp
    obtain e where e_pos: "e > 0"
      and near:
        "\<forall>z\<in>{0..1}. dist z y0 < e \<longrightarrow>
          valid_partition (?row z) vs ds \<and>
          carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2
            (partition_word (?row y0) vs ds)
            (partition_word (?row z) vs ds)"
      using valid_partition_nearby_partition_word_equiv[OF h_cont end0 end1 y0_01 part0]
      by blast
    have nearP: "\<forall>z\<in>{0..1}. dist z y0 < e \<longrightarrow> z \<in> ?P"
    proof
      fix z :: real
      assume z01: "z \<in> {0..1}"
      show "dist z y0 < e \<longrightarrow> z \<in> ?P"
      proof
        assume dz: "dist z y0 < e"
        have z_part: "valid_partition (?row z) vs ds"
          and fixed_rel:
            "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2
              (partition_word (?row y0) vs ds)
              (partition_word (?row z) vs ds)"
          using near[rule_format, OF z01 dz] by blast+
        obtain us' cs' where tbz: "some_valid_partition (?row z) = (us', cs')"
          by (cases "some_valid_partition (?row z)") auto
        have chosen_z: "valid_partition (?row z) us' cs'"
          using some_valid_partition_spec[OF row_loop[OF z01]] unfolding tbz by simp
        have z_rel:
          "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2
            (partition_word (?row z) vs ds) (?enc z)"
          using valid_partition_same_loop_partition_word_equiv[OF row_loop[OF z01] z_part chosen_z]
          unfolding tbz by simp
        have y0_eq: "?enc y0 = partition_word (?row y0) vs ds"
          unfolding tb0 by simp
        have base_rel0:
          "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2
            (?enc 0) (?enc y0)"
          using y0P by simp
        have base_rel:
          "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2
            (?enc 0) (partition_word (?row y0) vs ds)"
          using base_rel0 unfolding y0_eq by simp
        have "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2
            (?enc 0) (?enc z)"
          by (rule carrier_full_amalg_equiv.trans[OF base_rel])
             (rule carrier_full_amalg_equiv.trans[OF fixed_rel z_rel])
        then show "z \<in> ?P"
          using z01 by simp
      qed
    qed
    have witness: "e > 0 \<and> (\<forall>z\<in>{0..1}. dist z y0 < e \<longrightarrow> z \<in> ?P)"
    proof
      show "e > 0"
        by (rule e_pos)
      show "\<forall>z\<in>{0..1}. dist z y0 < e \<longrightarrow> z \<in> ?P"
        by (rule nearP)
    qed
    have ex_witness: "\<exists>eps. eps > 0 \<and> (\<forall>z\<in>{0..1}. dist z y0 < eps \<longrightarrow> z \<in> ?P)"
    proof (rule exI[where x = e], rule conjI)
      show "e > 0"
        using witness by simp
      show "\<forall>z\<in>{0..1}. dist z y0 < e \<longrightarrow> z \<in> ?P"
        using witness by simp
    qed
    have ex_witness_set: "\<exists>eps. eps \<in> {0<..} \<and> (\<forall>z\<in>{0..1}. dist z y0 < eps \<longrightarrow> z \<in> ?P)"
    proof -
      from ex_witness obtain eps where
        eps_pos: "eps > 0" and eps_near: "\<forall>z\<in>{0..1}. dist z y0 < eps \<longrightarrow> z \<in> ?P"
        by auto
      show ?thesis
      proof (rule exI[where x = eps], rule conjI)
        show "eps \<in> {0<..}"
          using eps_pos by simp
        show "\<forall>z\<in>{0..1}. dist z y0 < eps \<longrightarrow> z \<in> ?P"
          by (rule eps_near)
      qed
    qed
    show "\<exists>e>0. \<forall>z\<in>{0..1}. dist z y0 < e \<longrightarrow> z \<in> ?P"
    proof -
      from ex_witness
      show ?thesis
        unfolding Bex_def greaterThan_def
        by blast
    qed
  qed
  have P_subset: "?P \<subseteq> {0..1}"
    by auto
  have openP: "openin (top_of_set {0..1}) ?P"
    using openP_local P_subset by (auto simp: openin_euclidean_subtopology_iff)
  have open_notP_local:
    "\<forall>y0\<in>{0..1} - ?P. \<exists>e>0. \<forall>z\<in>{0..1}. dist z y0 < e \<longrightarrow> z \<in> {0..1} - ?P"
  proof
    fix y0
    assume y0_notP: "y0 \<in> {0..1} - ?P"
    then have y0_01: "y0 \<in> {0..1}" and y0_not: "y0 \<notin> ?P"
      by auto
    obtain vs ds where tb0: "some_valid_partition (?row y0) = (vs, ds)"
      by (cases "some_valid_partition (?row y0)") auto
    have part0: "valid_partition (?row y0) vs ds"
      using some_valid_partition_spec[OF row_loop[OF y0_01]] unfolding tb0 by simp
    obtain e where e_pos: "e > 0"
      and near:
        "\<forall>z\<in>{0..1}. dist z y0 < e \<longrightarrow>
          valid_partition (?row z) vs ds \<and>
          carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2
            (partition_word (?row y0) vs ds)
            (partition_word (?row z) vs ds)"
      using valid_partition_nearby_partition_word_equiv[OF h_cont end0 end1 y0_01 part0]
      by blast
    have near_notP: "\<forall>z\<in>{0..1}. dist z y0 < e \<longrightarrow> z \<in> {0..1} - ?P"
    proof
      fix z :: real
      assume z01: "z \<in> {0..1}"
      show "dist z y0 < e \<longrightarrow> z \<in> {0..1} - ?P"
      proof
        assume dz: "dist z y0 < e"
        have z_part: "valid_partition (?row z) vs ds"
          and fixed_rel:
            "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2
              (partition_word (?row y0) vs ds)
              (partition_word (?row z) vs ds)"
          using near[rule_format, OF z01 dz] by blast+
        obtain us' cs' where tbz: "some_valid_partition (?row z) = (us', cs')"
          by (cases "some_valid_partition (?row z)") auto
        have chosen_z: "valid_partition (?row z) us' cs'"
          using some_valid_partition_spec[OF row_loop[OF z01]] unfolding tbz by simp
        have z_rel:
          "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2
            (partition_word (?row z) vs ds) (?enc z)"
          using valid_partition_same_loop_partition_word_equiv[OF row_loop[OF z01] z_part chosen_z]
          unfolding tbz by simp
        have y0_eq: "?enc y0 = partition_word (?row y0) vs ds"
          unfolding tb0 by simp
        show "z \<in> {0..1} - ?P"
        proof
          show "z \<in> {0..1}"
            by (rule z01)
          show "z \<notin> ?P"
          proof
            assume zP: "z \<in> ?P"
            have base_to_z:
              "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2 (?enc 0) (?enc z)"
              using zP by simp
            have z_to_y0:
              "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2 (?enc z) (?enc y0)"
            proof -
              have step1:
                "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2
                  (?enc z) (partition_word (?row z) vs ds)"
                by (rule carrier_full_amalg_equiv.sym[OF z_rel])
              show ?thesis
                unfolding y0_eq
                by (rule carrier_full_amalg_equiv.trans[OF step1])
                   (rule carrier_full_amalg_equiv.sym[OF fixed_rel])
            qed
            have "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2 (?enc 0) (?enc y0)"
              by (rule carrier_full_amalg_equiv.trans[OF base_to_z z_to_y0])
            then show False
              using y0_not y0_01 by simp
          qed
        qed
      qed
    qed
    have witness: "e > 0 \<and> (\<forall>z\<in>{0..1}. dist z y0 < e \<longrightarrow> z \<in> {0..1} - ?P)"
    proof
      show "e > 0"
        by (rule e_pos)
      show "\<forall>z\<in>{0..1}. dist z y0 < e \<longrightarrow> z \<in> {0..1} - ?P"
        by (rule near_notP)
    qed
    have ex_witness: "\<exists>eps. eps > 0 \<and> (\<forall>z\<in>{0..1}. dist z y0 < eps \<longrightarrow> z \<in> {0..1} - ?P)"
    proof (rule exI[where x = e], rule conjI)
      show "e > 0"
        using witness by simp
      show "\<forall>z\<in>{0..1}. dist z y0 < e \<longrightarrow> z \<in> {0..1} - ?P"
        using witness by simp
    qed
    have ex_witness_set: "\<exists>eps. eps \<in> {0<..} \<and> (\<forall>z\<in>{0..1}. dist z y0 < eps \<longrightarrow> z \<in> {0..1} - ?P)"
    proof -
      from ex_witness obtain eps where
        eps_pos: "eps > 0" and eps_near: "\<forall>z\<in>{0..1}. dist z y0 < eps \<longrightarrow> z \<in> {0..1} - ?P"
        by auto
      show ?thesis
      proof (rule exI[where x = eps], rule conjI)
        show "eps \<in> {0<..}"
          using eps_pos by simp
        show "\<forall>z\<in>{0..1}. dist z y0 < eps \<longrightarrow> z \<in> {0..1} - ?P"
          by (rule eps_near)
      qed
    qed
    show "\<exists>e>0. \<forall>z\<in>{0..1}. dist z y0 < e \<longrightarrow> z \<in> {0..1} - ?P"
    proof -
      from ex_witness
      show ?thesis
        unfolding Bex_def greaterThan_def
        by blast
    qed
  qed
  have open_notP: "openin (top_of_set {0..1}) ({0..1} - ?P)"
    using open_notP_local by (auto simp: openin_euclidean_subtopology_iff)
  have closedP: "closedin (top_of_set {0..1}) ?P"
  proof -
    have "{0..1} - ({0..1} - ?P) = ?P"
      using P_subset by auto
    with open_notP show ?thesis
      by (auto simp: openin_closedin_eq)
  qed
  have P_all: "?P = {0..1}"
  proof -
    have "connected ({0..1} :: real set)"
      by simp
    then have P_cases: "?P = {} \<or> ?P = {0..1}"
      using openP closedP unfolding connected_clopen by blast
    have "(0::real) \<in> ?P"
      by (auto intro: carrier_full_amalg_equiv.refl)
    then have P_nonempty: "?P \<noteq> {}"
      by blast
    from P_cases P_nonempty show ?thesis
      by blast
  qed
  have row0_eq: "?row 0 = p"
  proof
    fix x :: real
    show "?row 0 x = p x"
      using h0_p[of x] unfolding h_def by simp
  qed
  have row1_eq: "?row 1 = q"
  proof
    fix x :: real
    show "?row 1 x = q x"
      using h0_q[of x] unfolding h_def by simp
  qed
  have row0_hom: "homotopic_paths W (?row 0) p"
  proof -
    have row0_path: "path (?row 0)" and row0_img: "path_image (?row 0) \<subseteq> W"
      using row_loop[of 0] unfolding loop_space_def by auto
    show ?thesis
    proof (rule homotopic_paths_eq[OF row0_path row0_img])
      fix t :: real
      assume t01: "t \<in> {0..1}"
      show "?row 0 t = p t"
      proof -
        from row0_eq have "?row 0 t = p t"
          by (rule fun_cong)
        then show ?thesis .
      qed
    qed
  qed
  have row1_hom: "homotopic_paths W (?row 1) q"
  proof -
    have row1_path: "path (?row 1)" and row1_img: "path_image (?row 1) \<subseteq> W"
      using row_loop[of 1] unfolding loop_space_def by auto
    show ?thesis
    proof (rule homotopic_paths_eq[OF row1_path row1_img])
      fix t :: real
      assume t01: "t \<in> {0..1}"
      show "?row 1 t = q t"
      proof -
        from row1_eq have "?row 1 t = q t"
          by (rule fun_cong)
        then show ?thesis .
      qed
    qed
  qed
  obtain vs0 ds0 where tb0: "some_valid_partition (?row 0) = (vs0, ds0)"
    by (cases "some_valid_partition (?row 0)") auto
  obtain vs1 ds1 where tb1: "some_valid_partition (?row 1) = (vs1, ds1)"
    by (cases "some_valid_partition (?row 1)") auto
  have tb0_p: "some_valid_partition p = (vs0, ds0)"
    using tb0 row0_eq by simp
  have tb1_q: "some_valid_partition q = (vs1, ds1)"
    using tb1 row1_eq by simp
  have enc0_eq: "?enc 0 = partition_word p vs0 ds0"
    using tb0 row0_eq by simp
  have enc1_eq: "?enc 1 = partition_word q vs1 ds1"
    using tb1 row1_eq by simp
  have part_row0: "valid_partition p vs0 ds0"
    using some_valid_partition_spec[OF p_loop] unfolding tb0_p by simp
  have part_row1: "valid_partition q vs1 ds1"
    using some_valid_partition_spec[OF q_loop] unfolding tb1_q by simp
  have p_to_row0:
    "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2
      (partition_word p ts bs) (?enc 0)"
    using valid_partition_same_loop_partition_word_equiv[OF p_loop p_part part_row0]
    using enc0_eq by simp
  have row1_to_q:
    "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2
      (?enc 1) (partition_word q us cs)"
    using valid_partition_same_loop_partition_word_equiv[OF q_loop part_row1 q_part]
    using enc1_eq by simp
  have row0_to_row1:
    "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2 (?enc 0) (?enc 1)"
  proof -
    have "(1::real) \<in> ?P"
      using P_all by simp
    then show ?thesis
      by simp
  qed
  show ?thesis
    by (rule carrier_full_amalg_equiv.trans[OF p_to_row0])
       (rule carrier_full_amalg_equiv.trans[OF row0_to_row1 row1_to_q])
qed

lemma valid_partition_loop_class_partition_word_equiv:
  assumes p_loop: "p \<in> loop_space W x0"
    and q_loop: "q \<in> loop_space W x0"
    and eq: "loop_class W x0 p = loop_class W x0 q"
    and p_part: "valid_partition p ts bs"
    and q_part: "valid_partition q us cs"
  shows "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2
      (partition_word p ts bs) (partition_word q us cs)"
proof -
  have hom: "homotopic_paths W p q"
    using p_loop q_loop eq by (simp add: loop_class_eq_iff)
  show ?thesis
    by (rule valid_partition_homotopic_partition_word_equiv[OF p_loop q_loop hom p_part q_part])
qed

lemma svk_decode_word_loop:
  assumes w_in: "fpw_in_space G1 G2 w"
  shows "svk_decode w = loop_class W x0 (word_loop w)"
proof -
  have w_loop: "word_loop w \<in> loop_space W x0"
    by (rule word_loop_in_W[OF w_in])
  have w_part:
    "valid_partition (word_loop w) (word_partition_times w) (word_partition_bits w)"
    by (rule word_loop_valid_partition[OF w_in])
  have decode_part:
    "svk_decode (partition_word (word_loop w) (word_partition_times w) (word_partition_bits w)) =
      loop_class W x0 (word_loop w)"
    by (rule valid_partition_decode_partition_word_eq_loop_class[OF w_loop w_part])
  have rel:
    "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2
      (partition_word (word_loop w) (word_partition_times w) (word_partition_bits w)) w"
    by (rule partition_word_word_loop_equiv[OF w_in])
  have "svk_decode (partition_word (word_loop w) (word_partition_times w) (word_partition_bits w)) =
      svk_decode w"
    by (rule svk_decode_respects[OF rel])
  then show ?thesis
    using decode_part by simp
qed

subsection \<open>Encoding, decoding, and the final bijection\<close>

text \<open>
  With existence, refinement invariance, and homotopy invariance in place, the
  encode/decode pair can now be defined directly on loop classes. The remaining
  lemmas verify the round-trip laws required by the abstract interface and turn
  them into the classical Seifert--van Kampen bijection.
\<close>

definition svk_encode ::
  "(real \<Rightarrow> 'a) set \<Rightarrow> ((real \<Rightarrow> 'a) set, (real \<Rightarrow> 'a) set) free_product_word"
where
  "svk_encode A =
    (let p = some_loop W x0 A;
         tb = some_valid_partition p
     in case tb of (ts, bs) \<Rightarrow> partition_word p ts bs)"

lemma svk_encode_in_space:
  assumes A_in: "A \<in> fundamental_group_space W x0"
  shows "fpw_in_space G1 G2 (svk_encode A)"
proof -
  have p_loop: "some_loop W x0 A \<in> loop_space W x0"
    and A_eq: "A = loop_class W x0 (some_loop W x0 A)"
    using some_loop_spec[OF A_in] by auto
  have part: "valid_partition (some_loop W x0 A)
      (fst (some_valid_partition (some_loop W x0 A)))
      (snd (some_valid_partition (some_loop W x0 A)))"
    by (rule some_valid_partition_spec[OF p_loop])
  show ?thesis
    unfolding svk_encode_def Let_def
    using valid_partition_partition_word_in_space[OF p_loop part]
    by (cases "some_valid_partition (some_loop W x0 A)") simp_all
qed

lemma svk_decode_encode:
  assumes A_in: "A \<in> fundamental_group_space W x0"
  shows "svk_decode (svk_encode A) = A"
proof -
  have p_loop: "some_loop W x0 A \<in> loop_space W x0"
    and A_eq: "A = loop_class W x0 (some_loop W x0 A)"
    using some_loop_spec[OF A_in] by auto
  have part: "valid_partition (some_loop W x0 A)
      (fst (some_valid_partition (some_loop W x0 A)))
      (snd (some_valid_partition (some_loop W x0 A)))"
    by (rule some_valid_partition_spec[OF p_loop])
  show ?thesis
    unfolding svk_encode_def Let_def
    using valid_partition_decode_partition_word_eq_loop_class[OF p_loop part] A_eq
    by (cases "some_valid_partition (some_loop W x0 A)") simp_all
qed

lemma svk_encode_decode:
  assumes w_in: "fpw_in_space G1 G2 w"
  shows "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2
      (svk_encode (svk_decode w)) w"
proof -
  let ?p = "some_loop W x0 (svk_decode w)"
  let ?tb = "some_valid_partition ?p"
  obtain ts bs where tb: "?tb = (ts, bs)"
    by (cases ?tb) auto
  have p_loop: "?p \<in> loop_space W x0"
    and p_class: "svk_decode w = loop_class W x0 ?p"
    using some_loop_spec[OF svk_decode_in_space] by auto
  have p_part: "valid_partition ?p ts bs"
    using some_valid_partition_spec[OF p_loop] unfolding tb by simp
  have w_loop: "word_loop w \<in> loop_space W x0"
    by (rule word_loop_in_W[OF w_in])
  have w_part:
    "valid_partition (word_loop w) (word_partition_times w) (word_partition_bits w)"
    by (rule word_loop_valid_partition[OF w_in])
  have same_class: "loop_class W x0 ?p = loop_class W x0 (word_loop w)"
    using p_class svk_decode_word_loop[OF w_in] by simp
  have part_rel:
    "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2
      (partition_word ?p ts bs)
      (partition_word (word_loop w) (word_partition_times w) (word_partition_bits w))"
    by (rule valid_partition_loop_class_partition_word_equiv[OF p_loop w_loop same_class p_part w_part])
  have word_rel:
    "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2
      (partition_word (word_loop w) (word_partition_times w) (word_partition_bits w)) w"
    by (rule partition_word_word_loop_equiv[OF w_in])
  have encode_word: "svk_encode (svk_decode w) = partition_word ?p ts bs"
    unfolding svk_encode_def Let_def tb by simp
  show ?thesis
    unfolding encode_word
    by (rule carrier_full_amalg_equiv.trans[OF part_rel word_rel])
qed

lemma svk_decode_surjective:
  assumes A_in: "A \<in> fundamental_group_space W x0"
  shows "\<exists>w. fpw_in_space G1 G2 w \<and> svk_decode w = A"
  using svk_encode_in_space[OF A_in] svk_decode_encode[OF A_in] by blast

theorem svk_decode_image:
  "svk_decode ` {w. fpw_in_space G1 G2 w} = fundamental_group_space W x0"
proof
  show "svk_decode ` {w. fpw_in_space G1 G2 w} \<subseteq> fundamental_group_space W x0"
    using svk_decode_in_space by blast
next
  show "fundamental_group_space W x0 \<subseteq> svk_decode ` {w. fpw_in_space G1 G2 w}"
    using svk_decode_surjective by blast
qed

definition classical_svk_quotient_map ::
  "(real \<Rightarrow> 'a) set \<Rightarrow>
    (((real \<Rightarrow> 'a) set, (real \<Rightarrow> 'a) set) free_product_word) set"
where
  "classical_svk_quotient_map A =
    carrier_full_amalg_class G1 G2 H i1 i2 mult1 one1 mult2 one2 (svk_encode A)"

lemma classical_svk_quotient_map_in_space:
  assumes A_in: "A \<in> fundamental_group_space W x0"
  shows "classical_svk_quotient_map A \<in>
    carrier_full_amalgamated_free_product_space G1 G2 H i1 i2 mult1 one1 mult2 one2"
  unfolding classical_svk_quotient_map_def
  by (rule carrier_full_amalg_class_in_space[OF svk_encode_in_space[OF A_in]])

lemma classical_svk_quotient_map_injective:
  assumes AB: "classical_svk_quotient_map A = classical_svk_quotient_map B"
    and A_in: "A \<in> fundamental_group_space W x0"
    and B_in: "B \<in> fundamental_group_space W x0"
  shows "A = B"
proof -
  have "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2
      (svk_encode A) (svk_encode B)"
    using AB unfolding classical_svk_quotient_map_def
    by (simp add: carrier_full_amalg_class_eq_iff)
  then have "svk_decode (svk_encode A) = svk_decode (svk_encode B)"
    by (rule svk_decode_respects)
  then show ?thesis
    using A_in B_in by (simp add: svk_decode_encode)
qed

lemma classical_svk_quotient_map_surjective:
  assumes Q_in:
    "Q \<in> carrier_full_amalgamated_free_product_space G1 G2 H i1 i2 mult1 one1 mult2 one2"
  shows "\<exists>A \<in> fundamental_group_space W x0. classical_svk_quotient_map A = Q"
proof -
  from Q_in obtain w where w_in: "fpw_in_space G1 G2 w"
    and Q_rep: "Q = carrier_full_amalg_class G1 G2 H i1 i2 mult1 one1 mult2 one2 w"
    unfolding carrier_full_amalgamated_free_product_space_def by auto
  have A_in: "svk_decode w \<in> fundamental_group_space W x0"
    by (rule svk_decode_in_space)
  have "classical_svk_quotient_map (svk_decode w) = Q"
    unfolding classical_svk_quotient_map_def Q_rep
    by (simp add: carrier_full_amalg_class_eq_iff svk_encode_decode[OF w_in])
  then show ?thesis
    using A_in by blast
qed

text \<open>
  At this point the encoding and decoding maps satisfy the abstract round-trip
  laws from the interface theory. The final theorem therefore presents the
  classical Seifert--van Kampen statement as a bijection between the fundamental
  group of \<open>U \<union> V\<close> at \<open>x0\<close> and the carrier-based amalgamated free product
  assembled from \<open>U\<close>, \<open>V\<close>, and \<open>U \<inter> V\<close>.
\<close>

theorem classical_seifert_van_kampen_bij_betw:
  "bij_betw classical_svk_quotient_map (fundamental_group_space W x0)
    (carrier_full_amalgamated_free_product_space G1 G2 H i1 i2 mult1 one1 mult2 one2)"
  unfolding bij_betw_def
proof
  show "inj_on classical_svk_quotient_map (fundamental_group_space W x0)"
    unfolding inj_on_def
    using classical_svk_quotient_map_injective by blast
next
  show "classical_svk_quotient_map ` fundamental_group_space W x0 =
      carrier_full_amalgamated_free_product_space G1 G2 H i1 i2 mult1 one1 mult2 one2"
  proof
    show "classical_svk_quotient_map ` fundamental_group_space W x0 \<subseteq>
        carrier_full_amalgamated_free_product_space G1 G2 H i1 i2 mult1 one1 mult2 one2"
      using classical_svk_quotient_map_in_space by blast
  next
    show "carrier_full_amalgamated_free_product_space G1 G2 H i1 i2 mult1 one1 mult2 one2
        \<subseteq> classical_svk_quotient_map ` fundamental_group_space W x0"
      using classical_svk_quotient_map_surjective by blast
  qed
qed

end

end
