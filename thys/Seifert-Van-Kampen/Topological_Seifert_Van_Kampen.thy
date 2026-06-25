theory Topological_Seifert_Van_Kampen
  imports
    Carrier_Amalgamated_Free_Product_Eval
    Explicit_Fundamental_Group_Scaffold
    Topological_Pushout_Scaffold
    Seifert_Van_Kampen_Scaffold
begin

section \<open>Concrete decode data for topological pushouts\<close>

text \<open>
  Once the pushout topology and the carrier-side amalgamation evaluator are
  available, the remaining task is to package a concrete decoding map back into
  the fundamental group of the pushout. This theory shows how such decode data
  yields the abstract carrier-level Seifert--van Kampen bijection in the
  topological pushout setting.
\<close>

lemma loopin_image_compose [simp]:
  "loopin_image g (loopin_image f p) = loopin_image (g \<circ> f) p"
  unfolding loopin_image_def by (rule ext) simp

lemma fundamental_groupin_map_eq:
  assumes A_in: "A \<in> fundamental_groupin_space X x"
    and f_cont: "continuous_map X Y f"
    and g_cont: "continuous_map X Y g"
    and fx: "f x = y"
    and gx: "g x = y"
    and fg: "\<And>u. f u = g u"
  shows "fundamental_groupin_map X x Y y f A = fundamental_groupin_map X x Y y g A"
proof -
  have repA: "some_loopin X x A \<in> loopin_space X x" "A = loopin_class X x (some_loopin X x A)"
    using some_loopin_spec[OF A_in] by auto
  have left_eq:
    "fundamental_groupin_map X x Y y f A =
      loopin_class Y y (loopin_image f (some_loopin X x A))"
    by (rule fundamental_groupin_map_rep[OF A_in repA(1) repA(2) f_cont fx])
  have right_eq:
    "fundamental_groupin_map X x Y y g A =
      loopin_class Y y (loopin_image g (some_loopin X x A))"
    by (rule fundamental_groupin_map_rep[OF A_in repA(1) repA(2) g_cont gx])
  have "loopin_image f (some_loopin X x A) = loopin_image g (some_loopin X x A)"
    using fg by (simp add: loopin_image_def fun_eq_iff)
  then show ?thesis
    using left_eq right_eq by simp
qed

lemma fundamental_groupin_map_compose:
  assumes A_in: "A \<in> fundamental_groupin_space X x"
    and f_cont: "continuous_map X Y f"
    and g_cont: "continuous_map Y Z g"
    and fx: "f x = y"
    and gy: "g y = z"
  shows "fundamental_groupin_map Y y Z z g (fundamental_groupin_map X x Y y f A) =
    fundamental_groupin_map X x Z z (g \<circ> f) A"
proof -
  have repA: "some_loopin X x A \<in> loopin_space X x" "A = loopin_class X x (some_loopin X x A)"
    using some_loopin_spec[OF A_in] by auto
  have mapA_in: "fundamental_groupin_map X x Y y f A \<in> fundamental_groupin_space Y y"
    by (rule fundamental_groupin_map_in_space[OF A_in f_cont fx])
  have mapA_eq:
    "fundamental_groupin_map X x Y y f A =
      loopin_class Y y (loopin_image f (some_loopin X x A))"
    by (rule fundamental_groupin_map_rep[OF A_in repA(1) repA(2) f_cont fx])
  have map_loop_in: "loopin_image f (some_loopin X x A) \<in> loopin_space Y y"
    by (rule loopin_image_in_space[OF repA(1) f_cont fx])
  have left_eq:
    "fundamental_groupin_map Y y Z z g (fundamental_groupin_map X x Y y f A) =
      loopin_class Z z (loopin_image g (loopin_image f (some_loopin X x A)))"
    by (rule fundamental_groupin_map_rep[OF mapA_in map_loop_in mapA_eq g_cont gy])
  have comp_cont: "continuous_map X Z (g \<circ> f)"
    using f_cont g_cont by (rule continuous_map_compose)
  have right_eq:
    "fundamental_groupin_map X x Z z (g \<circ> f) A =
      loopin_class Z z (loopin_image (g \<circ> f) (some_loopin X x A))"
    by (rule fundamental_groupin_map_rep[OF A_in repA(1) repA(2) comp_cont]) (simp add: fx gy)
  show ?thesis
    using left_eq right_eq by simp
qed

locale topological_svk_setup =
  fixes X :: "'a topology"
    and Y :: "'b topology"
    and Z :: "'c topology"
    and f :: "'c \<Rightarrow> 'a"
    and g :: "'c \<Rightarrow> 'b"
    and z0 :: "'c"
  assumes z0_in: "z0 \<in> topspace Z"
    and f_cont: "continuous_map Z X f"
    and g_cont: "continuous_map Z Y g"
begin

abbreviation x0 where "x0 \<equiv> f z0"
abbreviation y0 where "y0 \<equiv> g z0"
abbreviation P where "P \<equiv> pushout_topology X Y f g"
abbreviation p0 where "p0 \<equiv> pushout_inl f g x0"

abbreviation G1 where "G1 \<equiv> fundamental_groupin_space X x0"
abbreviation G2 where "G2 \<equiv> fundamental_groupin_space Y y0"
abbreviation H where "H \<equiv> fundamental_groupin_space Z z0"
abbreviation mult1 where "mult1 \<equiv> fundamental_groupin_mult X x0"
abbreviation one1 where "one1 \<equiv> fundamental_groupin_one X x0"
abbreviation mult2 where "mult2 \<equiv> fundamental_groupin_mult Y y0"
abbreviation one2 where "one2 \<equiv> fundamental_groupin_one Y y0"
abbreviation multP where "multP \<equiv> fundamental_groupin_mult P p0"
abbreviation oneP where "oneP \<equiv> fundamental_groupin_one P p0"

abbreviation i1 where "i1 \<equiv> fundamental_groupin_map Z z0 X x0 f"
abbreviation i2 where "i2 \<equiv> fundamental_groupin_map Z z0 Y y0 g"
abbreviation j1 where "j1 \<equiv> fundamental_groupin_map X x0 P p0 (pushout_inl f g)"
abbreviation j2 where "j2 \<equiv> fundamental_groupin_map Y y0 P p0 (pushout_inr f g)"

lemma x0_in [simp]: "x0 \<in> topspace X"
  using z0_in f_cont unfolding continuous_map_def by blast

lemma y0_in [simp]: "y0 \<in> topspace Y"
  using z0_in g_cont unfolding continuous_map_def by blast

lemma pushout_basepoint_eq [simp]:
  "pushout_inr f g y0 = p0"
  by (simp add: pushout_glue)

lemma pushout_basepoint_in [simp]:
  "p0 \<in> topspace P"
  by (simp add: pushout_inl_in_topspace[OF x0_in])

lemma pushout_fundamental_group_maps_agree:
  assumes h_in: "h \<in> H"
  shows "j1 (i1 h) = j2 (i2 h)"
proof -
  have left_comp:
    "j1 (i1 h) = fundamental_groupin_map Z z0 P p0 ((pushout_inl f g) \<circ> f) h"
    by (simp add: fundamental_groupin_map_compose[OF h_in f_cont continuous_map_pushout_inl])
  have right_comp:
    "j2 (i2 h) = fundamental_groupin_map Z z0 P p0 ((pushout_inr f g) \<circ> g) h"
    by (simp add: fundamental_groupin_map_compose[OF h_in g_cont continuous_map_pushout_inr])
  have left_cont: "continuous_map Z P ((pushout_inl f g) \<circ> f)"
    by (rule continuous_map_compose[OF f_cont continuous_map_pushout_inl])
  have right_cont: "continuous_map Z P ((pushout_inr f g) \<circ> g)"
    by (rule continuous_map_compose[OF g_cont continuous_map_pushout_inr])
  have left_z0: "((pushout_inl f g) \<circ> f) z0 = p0"
    by simp
  have right_z0: "((pushout_inr f g) \<circ> g) z0 = p0"
    by simp
  have comp_fun_eq: "((pushout_inl f g) \<circ> f) u = ((pushout_inr f g) \<circ> g) u" for u
    by (simp add: pushout_glue)
  have comp_eq:
    "fundamental_groupin_map Z z0 P p0 ((pushout_inl f g) \<circ> f) h =
      fundamental_groupin_map Z z0 P p0 ((pushout_inr f g) \<circ> g) h"
    by (rule fundamental_groupin_map_eq[OF h_in left_cont right_cont left_z0 right_z0 comp_fun_eq])
  show ?thesis
    using left_comp right_comp comp_eq by simp
qed

lemma i1_in_G1:
  assumes "h \<in> H"
  shows "i1 h \<in> G1"
  by (rule fundamental_groupin_map_in_space[OF assms f_cont]) simp

lemma i2_in_G2:
  assumes "h \<in> H"
  shows "i2 h \<in> G2"
  by (rule fundamental_groupin_map_in_space[OF assms g_cont]) simp

lemma decode_locale:
  "carrier_full_amalg_word_eval
    G1 mult1 one1 (fundamental_groupin_inv X x0)
    G2 mult2 one2 (fundamental_groupin_inv Y y0)
    H i1 i2
    (fundamental_groupin_space P p0) multP oneP (fundamental_groupin_inv P p0)
    j1 j2"
proof (rule carrier_full_amalg_word_eval.intro)
  show "carrier_group
      (fundamental_groupin_space X x0)
      (fundamental_groupin_mult X x0)
      (fundamental_groupin_one X x0)
      (fundamental_groupin_inv X x0)"
    by (rule fundamental_groupin_carrier_group[OF x0_in])
  show "carrier_group
      (fundamental_groupin_space Y y0)
      (fundamental_groupin_mult Y y0)
      (fundamental_groupin_one Y y0)
      (fundamental_groupin_inv Y y0)"
    by (rule fundamental_groupin_carrier_group[OF y0_in])
  show "carrier_group
      (fundamental_groupin_space P p0) multP oneP (fundamental_groupin_inv P p0)"
    by (rule fundamental_groupin_carrier_group[OF pushout_basepoint_in])
  show "carrier_group_hom
      (fundamental_groupin_space X x0)
      (fundamental_groupin_mult X x0)
      (fundamental_groupin_one X x0)
      (fundamental_groupin_inv X x0)
      (fundamental_groupin_space P p0) multP oneP (fundamental_groupin_inv P p0)
      (fundamental_groupin_map X x0 P p0 (pushout_inl f g))"
    by (rule fundamental_groupin_map_carrier_group_hom[OF x0_in continuous_map_pushout_inl]) simp
  show "carrier_group_hom
      (fundamental_groupin_space Y y0)
      (fundamental_groupin_mult Y y0)
      (fundamental_groupin_one Y y0)
      (fundamental_groupin_inv Y y0)
      (fundamental_groupin_space P p0) multP oneP (fundamental_groupin_inv P p0)
      (fundamental_groupin_map Y y0 P p0 (pushout_inr f g))"
    by (rule fundamental_groupin_map_carrier_group_hom[OF y0_in continuous_map_pushout_inr]) simp
  show "carrier_full_amalg_word_eval_axioms G1 G2 H i1 i2 j1 j2"
  proof (rule carrier_full_amalg_word_eval_axioms.intro)
    show "h \<in> H \<Longrightarrow> i1 h \<in> G1" for h
      by (rule i1_in_G1)
    show "h \<in> H \<Longrightarrow> i2 h \<in> G2" for h
      by (rule i2_in_G2)
    show "h \<in> H \<Longrightarrow> j1 (i1 h) = j2 (i2 h)" for h
      by (rule pushout_fundamental_group_maps_agree)
  qed
qed

interpretation decode:
  carrier_full_amalg_word_eval
    G1 mult1 one1 "fundamental_groupin_inv X x0"
    G2 mult2 one2 "fundamental_groupin_inv Y y0"
    H i1 i2
    "fundamental_groupin_space P p0" multP oneP "fundamental_groupin_inv P p0"
    j1 j2
  by (rule decode_locale)

abbreviation svk_word_eval where "svk_word_eval \<equiv> decode.carrier_full_amalg_eval"
abbreviation svk_decode where "svk_decode \<equiv> decode.carrier_full_amalg_decode"

lemma svk_decode_in_space:
  "svk_decode w \<in> fundamental_groupin_space P p0"
  by (rule decode.carrier_full_amalg_decode_in_carrier)

lemma svk_decode_respects:
  assumes "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2 u v"
  shows "svk_decode u = svk_decode v"
  using assms by (rule decode.carrier_full_amalg_decode_respects)

lemma svk_decode_eq_eval:
  assumes "fpw_in_space G1 G2 w"
  shows "svk_decode w = svk_word_eval w"
  using assms by (rule decode.carrier_full_amalg_decode_eq_eval)

end

locale topological_svk_open_cover =
  topological_svk_setup X Y Z f g z0
  for X :: "'a topology"
    and Y :: "'b topology"
    and Z :: "'c topology"
    and f :: "'c \<Rightarrow> 'a"
    and g :: "'c \<Rightarrow> 'b"
    and z0 :: "'c" +
  assumes left_open: "openin P (pushout_inl f g ` topspace X)"
    and right_open: "openin P (pushout_inr f g ` topspace Y)"
begin

lemma loopin_subdivision_by_summands:
  assumes p_loop: "p \<in> loopin_space P p0"
  shows "\<exists>n::nat. 0 < n \<and>
      (\<forall>i<n.
        subpathin (real i / real n) (real (Suc i) / real n) p ` {0..1}
          \<subseteq> pushout_inl f g ` topspace X \<or>
        subpathin (real i / real n) (real (Suc i) / real n) p ` {0..1}
          \<subseteq> pushout_inr f g ` topspace Y)"
proof -
  let ?L = "pushout_inl f g ` topspace X"
  let ?R = "pushout_inr f g ` topspace Y"
  from p_loop obtain p_path where p_path: "pathin P p"
    by (rule loopin_spaceE)
  have p_img: "p ` {0..1} \<subseteq> topspace P"
    by (rule pathin_image_subset_topspace[OF p_path])
  have cover: "p ` {0..1} \<subseteq> ?L \<union> ?R"
    using p_img by (auto simp: pushout_topspace_alt)
  have cover': "p ` {0..1} \<subseteq> \<Union>{?L, ?R}"
    using cover by auto
  have open_cover: "openin P U" if "U \<in> {?L, ?R}" for U
    using that left_open right_open by auto
  have subdiv:
    "\<exists>n::nat. 0 < n \<and>
      (\<forall>i<n. \<exists>U\<in>{?L, ?R}.
        subpathin (real i / real n) (real (Suc i) / real n) p ` {0..1} \<subseteq> U)"
    by (rule pathin_subdivision_open_cover[OF p_path cover' open_cover])
  then obtain n :: nat where n_pos: "0 < n"
    and n_cover:
      "\<forall>i<n. \<exists>U\<in>{?L, ?R}.
        subpathin (real i / real n) (real (Suc i) / real n) p ` {0..1} \<subseteq> U"
    by blast
  show ?thesis
    using n_pos n_cover by auto
qed

end

locale topological_svk =
  topological_svk_setup X Y Z f g z0
  for X :: "'a topology"
    and Y :: "'b topology"
    and Z :: "'c topology"
    and f :: "'c \<Rightarrow> 'a"
    and g :: "'c \<Rightarrow> 'b"
    and z0 :: "'c" +
  fixes encode
  assumes encode_in_space: "fpw_in_space G1 G2 (encode A)"
    and decode_encode: "svk_decode (encode A) = A"
    and encode_decode:
      "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2 (encode (svk_decode w)) w"
begin

lemma svk_locale:
  "carrier_svk_encode_decode_interface
    G1 G2 H i1 i2 mult1 one1 mult2 one2 encode svk_decode"
proof (rule carrier_svk_encode_decode_interface.intro)
  show "fpw_in_space G1 G2 (encode x)" for x
    by (fact encode_in_space)
  show "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2 u v \<Longrightarrow> svk_decode u = svk_decode v" for u v
    by (rule svk_decode_respects)
  show "svk_decode (encode x) = x" for x
    by (fact decode_encode)
  show "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2 (encode (svk_decode w)) w" for w
    by (fact encode_decode)
qed

interpretation svk: carrier_svk_encode_decode_interface
  G1 G2 H i1 i2 mult1 one1 mult2 one2 encode svk_decode
  by (rule svk_locale)

text \<open>
  The theorem below isolates the topological conclusion once an encoding map has
  been supplied and the usual round-trip laws have been verified. The classical
  open-union theorem later instantiates this interface by constructing that
  encoding from loop partitions subordinate to \<open>U\<close> and \<open>V\<close>.
\<close>

theorem topological_seifert_van_kampen_bij_betw:
  "bij_betw svk.carrier_svk_quotient_map UNIV
    (carrier_full_amalgamated_free_product_space G1 G2 H i1 i2 mult1 one1 mult2 one2)"
  by (rule svk.carrier_seifert_van_kampen_bij_betw)

end

end
