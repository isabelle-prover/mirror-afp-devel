theory Polygon_Splitting
imports
  "HOL-Analysis.Complete_Measure"
  Polygon_Jordan_Curve
  Polygon_Convex_Lemmas
begin

section "Polygon Splitting"

lemma split_up_a_list_into_3_parts:
  fixes i j:: "nat"
  assumes "i < length vts \<and> j < length vts \<and> i < j"
  shows  
  "vts = (take i vts) @ ((vts ! i) # ((take (j - i - 1) (drop (Suc i) vts)) @ (vts ! j) # drop (j - i) (drop (Suc i) vts)))"
proof - 
  let ?x = "vts ! i"
  let ?y =  "vts ! j"
  let ?vts1 = "(take i vts)"
  let ?drop_list = "drop (Suc i) vts"
  have vts_is: "vts = ?vts1 @ vts!i # drop (Suc i) vts"
    using split_list assms 
    by (meson id_take_nth_drop)
  then have len_vts1: "length ?vts1 = i"
    using length_take[of i vts] assms 
    by auto 
  have gt_eq: "j - i - 1 \<ge> 0"
    using assms by auto
  let ?ind = "j - i - 1"
  have drop_is: "drop (Suc i) vts ! (j - i - 1) = ?y"
    using assms by auto
  then have drop_list_is: "?drop_list = take ?ind ?drop_list @ ?y # (drop (j - i) ?drop_list)"
    by (metis Suc_diff_Suc Suc_leI assms diff_Suc_1 diff_less_mono id_take_nth_drop length_drop)
  have "length (drop (Suc ?ind) ?drop_list) = length vts - j - 1"
    using length_drop[of "Suc (j - i - 1)" "(drop (Suc i) vts)"] length_take assms 
    by auto
  then show ?thesis
    using vts_is drop_list_is len_vts1 
    by presburger
qed 

(* is_polygon_cut is a definition that is essentially from the (formalized) theta curve theorem;
  see split_inside_simple_closed_curve_real2 *)
definition is_polygon_cut :: "(real^2) list \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> bool" where
  "is_polygon_cut vts x y =
      (x \<noteq> y \<and>
      polygon (make_polygonal_path vts) \<and>
      {x, y} \<subseteq> set vts \<and>
      path_image (linepath x y) \<inter> path_image (make_polygonal_path vts) = {x, y} \<and>
      path_image (linepath x y) \<inter> path_inside (make_polygonal_path vts) \<noteq> {})"

definition is_polygon_cut_path :: "(real^2) list \<Rightarrow> R_to_R2 \<Rightarrow> bool" where
  "is_polygon_cut_path vts cutpath =
    (let x = pathstart cutpath ; y = pathfinish cutpath in
      (x \<noteq> y \<and>
      polygon (make_polygonal_path vts) \<and>
      {x, y} \<subseteq> set vts \<and>
      simple_path cutpath \<and> 
      path_image cutpath \<inter> path_image (make_polygonal_path vts) = {x, y} \<and>
      path_image cutpath \<inter> path_inside (make_polygonal_path vts) \<noteq> {}))"

(* This definition is basically the same as is_polygon_cut, but it contains a lot
  of useful properties / information explicitly, which is intended to make it easier
  to prove pick_union.  
  I.e. it splits a polygon into two polygons instead of just having two curves (from
  is_polygon_cut)
  See lemma polygon_cut_to_split_vtx0 for a connection between this definition and
  polygon_cut_to_split_vtx0 *)
definition is_polygon_split ::
  "(real^2) list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "is_polygon_split vts i j = 
  (i < length vts \<and> j < length vts \<and> i < j \<and>
  (let vts1 = (take i vts) in 
  let vts2 = (take (j - i - 1) (drop (Suc i) vts)) in
  let vts3 = drop (j - i) (drop (Suc i) vts) in
  let x = vts ! i in
  let y = vts ! j in
  let p = make_polygonal_path (vts@[vts!0]) in
  let p1 = make_polygonal_path (x#(vts2@[y, x])) in
  let p2 = make_polygonal_path (vts1 @ [x, y] @ vts3 @ [vts ! 0]) in
  let c1 = make_polygonal_path (x#(vts2@[y])) in
  let c2 = make_polygonal_path (vts1 @ [x, y] @ vts3) in
    (is_polygon_cut (vts@[vts!0]) x y \<and>
    polygon p \<and> polygon p1 \<and> polygon p2 \<and>
    path_inside p1 \<inter> path_inside p2 = {} \<and>
    path_inside p1 \<union> path_inside p2 \<union> (path_image (linepath x y) - {x, y}) = path_inside p 
    \<and> ((path_image p1) - (path_image (linepath x y))) \<inter> ((path_image p2) - (path_image (linepath x y)))
      = {}
    \<and> path_image p
      = ((path_image p1) - (path_image (linepath x y))) \<union> ((path_image p2) - (path_image (linepath x y))) \<union> {x, y}
  )))"

definition is_polygon_split_path :: "(real^2) list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (real^2) list \<Rightarrow> bool" where
  "is_polygon_split_path vts i j cutvts = 
  (i < length vts \<and> j < length vts \<and> i < j \<and>
  (let vts1 = (take i vts) in 
  let vts2 = (take (j - i - 1) (drop (Suc i) vts)) in
  let vts3 = drop (j - i) (drop (Suc i) vts) in
  let x = vts!i in
  let y = vts!j in
  let cutpath = make_polygonal_path (x # cutvts @ [y]) in
  let p = make_polygonal_path (vts@[vts!0]) in
  let p1 = make_polygonal_path (x#(vts2 @ [y] @ (rev cutvts) @ [x])) in
  let p2 = make_polygonal_path (vts1 @ ([x] @ cutvts @ [y]) @ vts3 @ [vts ! 0]) in
  let c1 = make_polygonal_path (x#(vts2@[y])) in
  let c2 = make_polygonal_path (vts1 @ ([x] @ cutvts @ [y]) @ vts3) in
    (is_polygon_cut_path (vts@[vts!0]) cutpath \<and>
    polygon p \<and> polygon p1 \<and> polygon p2 \<and>
    path_inside p1 \<inter> path_inside p2 = {} \<and>
    path_inside p1 \<union> path_inside p2 \<union> (path_image cutpath - {x, y}) = path_inside p 
    \<and> ((path_image p1) - (path_image cutpath)) \<inter> ((path_image p2) - (path_image cutpath)) = {}
    \<and> path_image p
      = ((path_image p1) - (path_image cutpath)) \<union> ((path_image p2) - (path_image cutpath)) \<union> {x, y}
  )))"

lemma polygon_split_add_measure:
  fixes p p1 p2 :: "R_to_R2"
  assumes "is_polygon_split vts i j"
  assumes "vts1 = (take i vts)" 
          "vts2 = (take (j - i - 1) (drop (Suc i) vts)) "
          "vts3 = drop (j - i) (drop (Suc i) vts) "
          "x = vts ! i "
          "y = vts ! j "
          "p = make_polygonal_path (vts@[vts!0]) "
          "p1 = make_polygonal_path (x#(vts2@[y, x])) "
          "p2 = make_polygonal_path (vts1 @ [x, y] @ vts3 @ [vts ! 0])"
  defines "M1 \<equiv> measure lebesgue (path_inside p1)" and
          "M2 \<equiv> measure lebesgue (path_inside p2)" and
          "M \<equiv> measure lebesgue (path_inside p)"
  shows "M1 + M2 = M"
proof-
  let ?cut = "linepath x y"
  let ?cut_open_image = "(path_image ?cut) - {x, y}"
  let ?P = "path_inside p"
  let ?P1 = "path_inside p1"
  let ?P2 = "path_inside p2"
  let ?M = "space lebesgue"
  let ?A = "sets lebesgue"
  let ?\<mu> = "emeasure lebesgue"

  have "open ?P1"
    by (metis assms(1) assms(3) assms(5) assms(6) assms(8) closed_path_image is_polygon_split_def open_inside path_inside_def polygon_def simple_path_def)
  then have P1_measurable: "?P1 \<in> ?A" by simp

  have "open ?P2"
    by (metis assms(1) assms(2) assms(4) assms(5) assms(6) assms(9) closed_path_image is_polygon_split_def open_inside path_inside_def polygon_def simple_path_def)
  then have P2_measurable: "?P2 \<in> ?A" by simp  

  have "?P1 \<inter> ?P2 = {}"
    by (metis assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) assms(8) assms(9) is_polygon_split_def)
  then have sum_union_finite: "?\<mu> ?P1 + ?\<mu> ?P2 = ?\<mu> (?P1 \<union> ?P2)"
    using plus_emeasure P1_measurable P2_measurable by blast
  
  have "measure lebesgue ?P1 = ?\<mu> ?P1"
    by (metis assms(1) assms(3) assms(5) assms(6) assms(8) bounded_inside bounded_set_imp_lmeasurable bounded_simple_path_image emeasure_eq_ennreal_measure emeasure_notin_sets ennreal_0 fmeasurableD2 is_polygon_split_def measure_zero_top path_inside_def polygon_def)
  moreover have "measure lebesgue ?P2 = ?\<mu> ?P2"
    by (metis Sigma_Algebra.measure_def assms(1) assms(2) assms(4) assms(5) assms(6) assms(9) bounded_inside bounded_path_image bounded_set_imp_lmeasurable emeasure_eq_ennreal_measure emeasure_notin_sets enn2real_top ennreal_0 fmeasurableD2 is_polygon_split_def path_inside_def polygon_def simple_path_def)
  ultimately have "?\<mu> (?P1 \<union> ?P2) = M1 + M2"
    using assms(10) assms(11) sum_union_finite by auto
  moreover have "?\<mu> (?P1 \<union> ?P2) = ?\<mu> ?P"
  proof-
    have "?\<mu> (path_image ?cut) = 0" using linepath_has_emeasure_0 by blast
    then have "(path_image ?cut) \<in> null_sets lebesgue" by auto
    moreover have "{x, y} \<in> null_sets lebesgue" by simp
    ultimately have "?cut_open_image \<in> null_sets lebesgue" using measure_Diff_null_set by auto
    moreover have "?P = ?P1 \<union> ?P2 \<union> ?cut_open_image"
      by (metis assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) assms(7) assms(8) assms(9) is_polygon_split_def)
    ultimately show ?thesis
      by (simp add: P1_measurable P2_measurable emeasure_Un_null_set sets.Un)
  qed
  ultimately show ?thesis
    by (smt (verit, best) M1_def M2_def M_def emeasure_eq_ennreal_measure enn2real_ennreal ennreal_neq_top measure_nonneg)
qed

lemma polygonal_paths_measurable:
  shows "path_image (make_polygonal_path vts) \<in> sets lebesgue"
proof (induct vts rule: make_polygonal_path_induct)
  case (Empty ell)
  then show ?case by auto
next
  case (Single ell)
  then obtain a where "ell = [a]"
    by (metis Cons_nth_drop_Suc One_nat_def drop0 drop_eq_Nil le_numeral_extra(4) zero_less_one)
  then show ?case using make_polygonal_path.simps(2)[of a] by simp
next
  case (Two ell)
  then obtain a b where "ell = [a, b]" 
    by (metis Cons_nth_drop_Suc One_nat_def Suc_1 append_Nil drop_eq_Nil2 dual_order.refl id_take_nth_drop lessI pos2 take0)
  then show ?case using make_polygonal_path.simps(3)[of a b] by simp
next
  case (Multiple ell)
  then have "ell = (ell ! 0) # (ell ! 1) # (ell ! 2) # (drop 3 ell)"
    by (metis Cons_nth_drop_Suc One_nat_def Suc_1 drop0 le_Suc_eq linorder_not_less numeral_3_eq_3)
  then have "make_polygonal_path ell =
    linepath (ell ! 0) (ell ! 1) +++ make_polygonal_path (ell ! 1 # ell ! 2 # (drop 3 ell))"
    by (metis make_polygonal_path.simps(4))
  (* TODO: could simplify here *)
  then have "path_image (make_polygonal_path ell) = path_image (linepath (ell ! 0) (ell ! 1)) \<union> path_image (make_polygonal_path (ell ! 1 # ell ! 2 # (drop 2 ell)))"
    using Cons_nth_drop_Suc Multiple.hyps(1) One_nat_def Suc_1 Un_assoc \<open>ell = ell ! 0 # ell ! 1 # ell ! 2 # drop 3 ell\<close> list.discI make_polygonal_path.simps(2) make_polygonal_path.simps(3) nth_Cons_0 numeral_3_eq_3 path_image_cons_union
  proof-
    have f1: "ell = ell ! 0 # ell ! 1 # ell ! Suc 1 # drop 3 ell"
      using Suc_1 \<open>ell = ell ! 0 # ell ! 1 # ell ! 2 # drop 3 ell\<close> by presburger
    have "Suc 1 < length ell"
      by (smt (z3) Suc_1 \<open>2 < length ell\<close>)
    then have f2: "drop (Suc 1) ell = ell ! Suc 1 # drop (Suc (Suc 1)) ell"
      by (smt (z3) Cons_nth_drop_Suc)
    have f3: "\<forall>v va vs. path_image (make_polygonal_path (v # va # vs)) = path_image (linepath v va) \<union> path_image (make_polygonal_path (va # vs))"
      by (metis (no_types) list.discI nth_Cons_0 path_image_cons_union)
    have f4: "\<forall>V v va. path_image (linepath (v::(real, 2) vec) va) \<union> (path_image (linepath va va) \<union> V) = path_image (linepath v va) \<union> V"
      by auto
    have "path_image (make_polygonal_path ell) = path_image (make_polygonal_path (ell ! 0 # ell ! 1 # drop (Suc 1) ell))"
      using f2 f1 by (simp add: numeral_3_eq_3)
    then have "path_image (make_polygonal_path ell) = path_image (linepath (ell ! 0) (ell ! 1)) \<union> path_image (make_polygonal_path (ell ! 1 # ell ! Suc 1 # drop (Suc 1) ell))"
      using f4 f3 f2 by presburger
    then show ?thesis
      using Suc_1 by presburger
  qed
    then show ?case using Multiple(3)
      by (metis (no_types, lifting) Cons_nth_drop_Suc Multiple.hyps(1) Multiple.hyps(2) One_nat_def Suc_1 \<open>ell = ell ! 0 # ell ! 1 # ell ! 2 # drop 3 ell\<close> list.discI make_polygonal_path.simps(3) nth_Cons_0 numeral_3_eq_3 path_image_cons_union sets.Un) 
  qed

lemma polygonal_path_has_emeasure_0:
  shows "emeasure lebesgue (path_image (make_polygonal_path vts)) = 0"
proof (induct vts)
  case Nil
  then show ?case by auto
next
  case (Cons a vts)
  then show ?case
    by (metis linepath_is_negligible make_polygonal_path.simps(2) negligible_Un negligible_iff_emeasure0 path_image_cons_union polygonal_paths_measurable)
qed

lemma polygon_split_path_add_measure:
  fixes p p1 p2 :: "R_to_R2"
  assumes "is_polygon_split_path vts i j cutvts"
  assumes "vts1 = (take i vts)" 
          "vts2 = (take (j - i - 1) (drop (Suc i) vts)) "
          "vts3 = drop (j - i) (drop (Suc i) vts) "
          "x = vts ! i "
          "y = vts ! j "
          "p = make_polygonal_path (vts@[vts!0])"
          "p1 = make_polygonal_path (x#(vts2 @ [y] @ (rev cutvts) @ [x]))"
          "p2 = make_polygonal_path (vts1 @ ([x] @ cutvts @ [y]) @ vts3 @ [vts ! 0])"
  defines "M1 \<equiv> measure lebesgue (path_inside p1)" and
          "M2 \<equiv> measure lebesgue (path_inside p2)" and
          "M \<equiv> measure lebesgue (path_inside p)"
  shows "M1 + M2 = M"
proof-
  let ?cut = "make_polygonal_path (x # cutvts @ [y])"
  let ?cut_open_image = "(path_image ?cut) - {x, y}"
  let ?P = "path_inside p"
  let ?P1 = "path_inside p1"
  let ?P2 = "path_inside p2"
  let ?M = "space lebesgue"
  let ?A = "sets lebesgue"
  let ?\<mu> = "emeasure lebesgue"

  have "open ?P1"
    by (metis assms(1) assms(3) assms(5) assms(6) assms(8) closed_path_image is_polygon_split_path_def open_inside path_inside_def polygon_def simple_path_def)
  then have P1_measurable: "?P1 \<in> ?A" by simp

  have "open ?P2"
    by (metis assms(1) assms(2) assms(4) assms(5) assms(6) assms(9) closed_path_image is_polygon_split_path_def open_inside path_inside_def polygon_def simple_path_def)
  then have P2_measurable: "?P2 \<in> ?A" by simp  

  have "?P1 \<inter> ?P2 = {}"
    by (metis assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) assms(8) assms(9) is_polygon_split_path_def)
  then have sum_union_finite: "?\<mu> ?P1 + ?\<mu> ?P2 = ?\<mu> (?P1 \<union> ?P2)"
    using plus_emeasure P1_measurable P2_measurable by blast

  have "?\<mu> (path_image q) = 0 \<Longrightarrow> (path_image q) \<in> null_sets lebesgue" if *: "path_image q \<in> sets lebesgue" for q::"real \<Rightarrow> (real, 2) vec"
    using null_sets_def * by blast
  
  have "measure lebesgue ?P1 = ?\<mu> ?P1"
    by (metis assms(1) assms(3) assms(5) assms(6) assms(8) bounded_inside bounded_set_imp_lmeasurable bounded_simple_path_image emeasure_eq_ennreal_measure emeasure_notin_sets ennreal_0 fmeasurableD2 is_polygon_split_path_def measure_zero_top path_inside_def polygon_def)
  moreover have "measure lebesgue ?P2 = ?\<mu> ?P2"
    by (metis Sigma_Algebra.measure_def assms(1) assms(2) assms(4) assms(5) assms(6) assms(9) bounded_inside bounded_path_image bounded_set_imp_lmeasurable emeasure_eq_ennreal_measure emeasure_notin_sets enn2real_top ennreal_0 fmeasurableD2 is_polygon_split_path_def path_inside_def polygon_def simple_path_def)
  ultimately have "?\<mu> (?P1 \<union> ?P2) = M1 + M2"
    using assms(10) assms(11) sum_union_finite by auto
  moreover have "?\<mu> (?P1 \<union> ?P2) = ?\<mu> ?P"
  proof-
    have "?\<mu> (path_image ?cut) = 0" using polygonal_path_has_emeasure_0 
      by presburger
    then have "(path_image ?cut) \<in> null_sets lebesgue" using polygonal_paths_measurable
      by blast
    moreover have "{x, y} \<in> null_sets lebesgue" by simp
    ultimately have "?cut_open_image \<in> null_sets lebesgue" using measure_Diff_null_set by auto
    moreover have "?P = ?P1 \<union> ?P2 \<union> ?cut_open_image"
      by (metis assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) assms(7) assms(8) assms(9) is_polygon_split_path_def)
    ultimately show ?thesis
      by (simp add: P1_measurable P2_measurable emeasure_Un_null_set sets.Un)
  qed
  ultimately show ?thesis
    by (smt (verit, best) M1_def M2_def M_def emeasure_eq_ennreal_measure enn2real_ennreal ennreal_neq_top measure_nonneg)
qed

lemma polygon_cut_path_to_split_path_vtx0:
  fixes p :: "R_to_R2"
  assumes polygon_p: "polygon p" and
          i_gt: "i > 0" and
          i_lt: "i < length vts" and
          p_is: "p = make_polygonal_path (vts @ [vts ! 0])" and
          cutpath: "cutpath = make_polygonal_path ([vts!0] @ cutvts @ [vts!i])" and
          have_cut: "is_polygon_cut_path (vts @ [vts!0]) cutpath"
  shows "is_polygon_split_path vts 0 i cutvts"
proof - 
  let ?vts2 = "take (i - 1) (drop 1 vts)"
  let ?vts3 = "drop i (drop 1 vts)"
  let ?x = "vts ! 0"
  let ?y = "vts ! i"

  let ?c3_vts = "[?x] @ cutvts @ [?y]"
  let ?c3 = "cutpath"
  let ?c3_rev_vts = "rev ?c3_vts"
  let ?c3_rev = "make_polygonal_path ?c3_rev_vts"
  let ?c3' = "reversepath ?c3"

  let ?p = "make_polygonal_path (vts @ [vts ! 0])"
  let ?p1_vts = "?x # ?vts2 @ ?c3_rev_vts"
  let ?p1 = "make_polygonal_path ?p1_vts"
  let ?p1_rot_vts = "?c3_rev_vts @ ?vts2 @ [?y]"
  let ?p1_rot = "make_polygonal_path ?p1_rot_vts"
  let ?p2_vts = "?c3_vts @ ?vts3 @ [?x]"
  let ?p2 = "make_polygonal_path ?p2_vts"
  let ?c1_vts = "?x # ?vts2 @ [?y]"
  let ?c1 = "make_polygonal_path ?c1_vts"
  let ?c2_vts = "[?y] @ ?vts3 @ [?x]"
  let ?c2 = "reversepath (make_polygonal_path ?c2_vts)"
  let ?c2'_vts = "[?y] @ ?vts3 @ [?x]"
  let ?c2' = "(make_polygonal_path (?c2'_vts))"

  have distinct_vts: "distinct vts"
    using polygon_p p_is 
    using polygon_def simple_polygonal_path_vts_distinct by force
  have len_vts_gteq3: "length vts \<ge> 3"
    using polygon_p p_is  polygon_vertices_length_at_least_4 by fastforce

  then have "?x # ?vts2 @ [?y] = take (i+1) (vts@ [vts ! 0])"
    by (smt (verit, ccfv_threshold) i_gt Cons_nth_drop_Suc Suc_eq_plus1 Suc_pred' add_less_cancel_left butlast_snoc drop0 drop_drop hd_drop_conv_nth i_lt length_append_singleton length_greater_0_conv less_imp_le_nat linorder_not_less list.size(3) plus_1_eq_Suc take_Suc_Cons take_all_iff take_butlast take_hd_drop)
  have "[?y] @ ?vts3 @ [?x] = drop (i) (vts @ [vts ! 0])"
    using i_gt 
    by (metis (no_types, lifting) Cons_eq_appendI Cons_nth_drop_Suc Suc_eq_plus1 append_Nil diff_is_0_eq' drop_0 drop_append drop_drop i_lt less_imp_le_nat)

  have card_gteq: "card (set vts) \<ge> 3"
    using polygon_at_least_3_vertices_wraparound polygon_p p_is
    by (metis butlast_conv_take butlast_snoc)
  then have "vts \<noteq> []"
    by auto
  then have vts_is: "vts = ?x # ?vts2 @ ?y # ?vts3"
    using split_up_a_list_into_3_parts[of 0 vts i] i_gt i_lt
    by auto

  (* First, show some relationships among the path images *)
  have elem_prop1: "last ?c1_vts = ?y"
    by (metis (no_types, lifting) last.simps snoc_eq_iff_butlast)
  have elem_prop2: "(vts ! 0 # (rev ?vts3) @ [vts ! i]) !
        (length (vts ! 0 # drop i (drop 1 vts) @ [vts ! i]) - 1) = vts ! i"
    by (metis diff_Suc_1 length_Cons length_append_singleton length_rev nth_Cons_Suc nth_append_length)
  have "path_image cutpath = path_image ?c3'" by simp
  then have "path_image ?p1 = path_image (?c1 +++ ?c3_rev)"
    using elem_prop1 assms make_polygonal_path_image_append_alt[of ?p1 ?p1_vts ?c1 ?c1_vts ?c3_rev ?c3_rev_vts]
    by simp
  also have "... = path_image ?c1 \<union> path_image ?c3_rev"
    by (metis (no_types, opaque_lifting) append_Cons append_Nil elem_prop1 hd_conv_nth last_conv_nth list.discI list.sel(1) path_image_join polygon_pathfinish polygon_pathstart rev.simps(2) rev_rev_ident)
  finally have image_prop: "path_image ?p1 = path_image ?c1 \<union> path_image cutpath"
    using rev_vts_path_image cutpath by presburger
  have "path_image ?c3' = path_image ?c3"
    using cutpath rev_vts_path_image by force
  then have path_image_p1: "path_image ?c1 \<union> path_image ?c3 = path_image ?p1"
    using image_prop by presburger

  have "?p2_vts = ?c3_vts @ (tl ?c2_vts)" by simp
  then have "path_image ?p2 = path_image (?c3 +++ ?c2')"
    using make_polygonal_path_image_append_alt[of ?p2 ?p2_vts ?c3 ?c3_vts ?c2' ?c2_vts]
    unfolding assms by auto
  then have path_image_p2: "path_image ?c2 \<union> path_image ?c3 = path_image ?p2"
    by (metis (no_types, opaque_lifting) Un_commute append_Cons append_Nil cutpath last_conv_nth nth_Cons_0 path_image_join path_image_reversepath polygon_pathfinish polygon_pathstart snoc_eq_iff_butlast)

  have "drop 1 vts = take (i - 1) (drop 1 vts) @ [vts ! i] @ drop i (drop 1 vts)"
    by (metis (no_types, lifting) Cons_eq_appendI Cons_nth_drop_Suc Suc_eq_plus1 Suc_pred' append.simps(1) append_take_drop_id drop_drop i_gt i_lt)
  then have vts_is: "vts @ [vts ! 0] = vts ! 0 # take (i - 1) (drop 1 vts) @ [vts ! i] @ drop i (drop 1 vts) @ [vts ! 0]"
    by (metis (no_types, opaque_lifting) Cons_nth_drop_Suc One_nat_def append.assoc append_Cons drop0 i_lt length_pos_if_in_set nth_mem)
  let ?vts1' = "take (i - 1) (drop 1 vts)"
  let ?vts2' = "drop i (drop 1 vts)"
  have path_im_p: "path_image
     (make_polygonal_path
       ((vts ! 0 # ?vts1') @ [vts ! i] @ [vts ! i] @ ?vts2' @ [vts ! 0])) =
    path_image
     (make_polygonal_path
       ((vts ! 0 # ?vts1') @ [vts ! i] @ ?vts2' @ [vts ! 0]))"
    using make_polygonal_path_image_append_helper[of " vts ! 0 # ?vts1'" "?vts2' @ [vts ! 0]"] by auto
  have "path_image
     (make_polygonal_path
       ((vts ! 0 # ?vts1') @ [vts ! i] @ [vts ! i] @ ?vts2' @ [vts ! 0])) = path_image (make_polygonal_path ((vts ! 0 # ?vts1') @ [vts ! i]) +++ (linepath (vts ! i) (vts ! i)) +++ make_polygonal_path ([vts ! i] @ ?vts2' @ [vts ! 0]))"
    using make_polygonal_path_image_append[of "(vts ! 0 # ?vts1') @ [vts ! i]" "[vts ! i] @ ?vts2' @ [vts ! 0]"] 
      (* SMT call may take a few seconds to load *)
    by (smt (verit) add_2_eq_Suc' append.assoc append_Cons diff_Suc_1 le_add2 length_Cons length_append_singleton nth_Cons_0 nth_append_length)
  then have "path_image p = path_image (make_polygonal_path ((vts ! 0 # ?vts1') @ [vts ! i]) +++ (linepath (vts ! i) (vts ! i)) +++ make_polygonal_path ([vts ! i] @ ?vts2' @ [vts ! 0]))"
    using path_im_p p_is vts_is 
    by simp
  then have "path_image p = path_image ?c1 \<union> path_image (linepath (vts ! i) (vts ! i)) \<union> path_image (make_polygonal_path ([vts ! i] @ ?vts2' @ [vts ! 0]))" 
    by (metis (no_types, lifting) Un_assoc append_Cons elem_prop1 list.discI nth_Cons_0 path_image_join pathfinish_linepath pathstart_join pathstart_linepath polygon_pathfinish polygon_pathstart last_conv_nth)
  moreover have "... = path_image ?c1 \<union> {vts ! i} \<union> path_image (make_polygonal_path ([vts ! i] @ ?vts2' @ [vts ! 0]))"
    by auto
  moreover have "... = path_image ?c1 \<union> path_image (make_polygonal_path ([vts ! i] @ ?vts2' @ [vts ! 0]))"
    using vertices_on_path_image by fastforce
  ultimately have path_image_p: "path_image p = path_image ?c1 \<union> path_image ?c2"
    using path_image_reversepath by blast

  (* Next, show that ?c1, ?c2 are loopfree, ?p1, ?p2 are polygons *)
  have simple_path_polygon: "simple_path (make_polygonal_path (?x # ?vts2 @ ?y # ?vts3 @ [?x]))"
    using polygon_p p_is vts_is 
    using Cons_eq_appendI append_self_conv2 polygon_def by auto
  then have loop_free_polygon: "loop_free (make_polygonal_path (?x # ?vts2 @ ?y # ?vts3 @ [?x]))"
    unfolding simple_path_def by auto

  have loop_free_p: "loop_free p"
    using polygon_p p_is unfolding polygon_def simple_path_def by auto

  have sublist_c1: "sublist (?x # ?vts2 @ [?y]) vts"
    using \<open>vts ! 0 # take (i - 1) (drop 1 vts) @ [vts ! i] = take (i + 1) (vts @ [vts ! 0])\<close> i_lt by auto
  then have sublist_c1: "sublist (?x # ?vts2 @ [?y]) (vts@[vts !0])"
    by (metis \<open>vts ! 0 # take (i - 1) (drop 1 vts) @ [vts ! i] = take (i + 1) (vts @ [vts ! 0])\<close> sublist_take)
  then have "loop_free ?c1"
    using sublist_is_loop_free p_is loop_free_p sublist_c1
    by (metis One_nat_def Suc_1 Suc_eq_plus1 Suc_leI Suc_le_mono \<open>vts ! 0 # take (i - 1) (drop 1 vts) @ [vts ! i] = take (i + 1) (vts @ [vts ! 0])\<close> i_gt i_lt length_append_singleton less_imp_le_nat take_i_is_loop_free)
  then have simple_c1: "simple_path ?c1"
    unfolding simple_path_def 
    using make_polygonal_path_gives_path by blast
  have start_c1: "pathstart ?c1 = ?x"
    using polygon_pathstart  
    by (metis Cons_eq_appendI list.discI nth_Cons_0 )
  have finish_c1: "pathfinish ?c1 = ?y"
    using polygon_pathfinish
    by (metis Cons_eq_appendI diff_Suc_1 length_append_singleton list.discI nth_append_length)

  have sublist_c2: "sublist ([?y] @ ?vts3 @ [?x]) (vts@[vts !0])"
    by (metis \<open>[vts ! i] @ drop i (drop 1 vts) @ [vts ! 0] = drop i (vts @ [vts ! 0])\<close> sublist_drop)
  have "i \<le> length (tl vts)" using i_lt by fastforce
  then have "loop_free ?c2"
    by (metis (no_types) Suc_1 \<open>[vts ! i] @ drop i (drop 1 vts) @ [vts ! 0] = drop i (vts @ [vts ! 0])\<close> \<open>vts \<noteq> []\<close> butlast_snoc drop_Suc drop_i_is_loop_free length_butlast length_drop loop_free_p loop_free_reversepath p_is tl_append2)
  then have simple_c2: "simple_path ?c2"
    unfolding simple_path_def 
    using make_polygonal_path_gives_path 
    using path_imp_reversepath by blast
  have start_c2: "pathstart ?c2 = ?x"
    using polygon_pathfinish 
    by (metis (no_types, lifting) Nil_is_append_conv last_appendR last_conv_nth pathstart_reversepath polygon_pathfinish snoc_eq_iff_butlast)  
  have finish_c2: "pathfinish ?c2 = ?y"
    using polygon_pathstart by auto 

  have path_image_int: "path_image ?c1 \<subseteq> path_image ?p"
    unfolding path_image_def 
    by (metis Un_upper1 p_is path_image_def path_image_p)
  moreover have "path_image ?p \<inter> path_image ?c3 \<subseteq> {vts ! 0, vts ! i}"
    using have_cut unfolding is_polygon_cut_path_def
    by (metis (no_types, lifting) Int_commute append_Cons append_is_Nil_conv cutpath last_appendR last_conv_nth last_snoc not_Cons_self2 nth_Cons_0 polygon_pathfinish polygon_pathstart set_eq_subset)
  ultimately have vts_subset_c1c3: "path_image ?c1 \<inter> path_image ?c3 \<subseteq> {?x, ?y}"
    by blast
  have other_subset1: "{vts ! 0, vts ! i} \<subseteq> path_image ?c1"
    using vertices_on_path_image by fastforce
  have other_subset2: "{vts ! 0, vts ! i} \<subseteq> path_image ?c3"
    unfolding assms using vertices_on_path_image by force
  then have c1_inter_c3: "path_image ?c1 \<inter>  path_image ?c3 = {vts ! 0, vts ! i}"
    using vts_subset_c1c3 other_subset1 other_subset2 by blast
  then have "path_image ?c1 \<inter>  path_image ?c3_rev = {pathstart ?c1, pathstart ?c3_rev}"
    by (metis rev_vts_path_image append_Cons append_Nil cutpath hd_conv_nth list.discI list.sel(1) polygon_pathstart rev.simps(2) rev_rev_ident)
  
  (* prove loop_free p1 *)
  then have c1_inter_c3': "path_image (make_polygonal_path (vts ! 0 # take (i - 1) (drop 1 vts) @ [vts ! i])) \<inter>
    path_image (make_polygonal_path (rev ([vts ! 0] @ cutvts @ [vts ! i])))
    \<subseteq> {pathstart (make_polygonal_path (vts ! 0 # take (i - 1) (drop 1 vts) @ [vts ! i])),
        pathstart (make_polygonal_path (rev ([vts ! 0] @ cutvts @ [vts ! i])))}"
    by blast
  have last_is_head: "last ?c3_rev_vts = hd ?c1_vts" by auto
  have vts_append: "vts ! 0 # take (i - 1) (drop 1 vts) @ rev ([vts ! 0] @ cutvts @ [vts ! i]) =
    (vts ! 0 # take (i - 1) (drop 1 vts) @ [vts ! i]) @
    tl (rev ([vts ! 0] @ cutvts @ [vts ! i]))"
    by simp
  have loop_free: "loop_free (make_polygonal_path (vts ! 0 # take (i - 1) (drop 1 vts) @ [vts ! i])) \<and>
    loop_free (make_polygonal_path (rev ([vts ! 0] @ cutvts @ [vts ! i])))"
    by (metis Suc_eq_plus1 Suc_le_mono Zero_neq_Suc \<open>vts ! 0 # take (i - 1) (drop 1 vts) @ [vts ! i] = take (i + 1) (vts @ [vts ! 0])\<close> cutpath diff_Suc_1 have_cut i_gt i_lt is_polygon_cut_path_def length_append_singleton less_2_cases less_imp_le_nat less_nat_zero_code linorder_le_less_linear loop_free_p p_is rev_vts_is_loop_free simple_path_def take_i_is_loop_free)
  have last_is_head2: 
    "last (vts ! 0 # take (i - 1) (drop 1 vts) @ [vts ! i]) =
    hd (rev ([vts ! 0] @ cutvts @ [vts ! i]))" by simp
  have arcs: "arc (make_polygonal_path (vts ! 0 # take (i - 1) (drop 1 vts) @ [vts ! i])) \<and>
      arc (make_polygonal_path (rev ([vts ! 0] @ cutvts @ [vts ! i])))"
    using Nil_is_append_conv append_Cons constant_linepath_is_not_loop_free cutpath finish_c1 have_cut hd_conv_nth is_polygon_cut_path_def last_appendR last_conv_nth last_is_head last_is_head2 last_snoc list.sel(1) loop_free make_polygonal_path.simps(1) make_polygonal_path_gives_path polygon_pathfinish polygon_pathstart simple_path_def simple_path_imp_arc loop_free
    by (smt (verit, ccfv_SIG))
  then have "loop_free ?p1"
    using loop_free_append[of ?p1 ?p1_vts ?c1 ?c1_vts ?c3_rev ?c3_rev_vts,
        OF _ _ _ vts_append loop_free c1_inter_c3' _ last_is_head2 arcs] using last_is_head by blast

  (* Prove polygon ?p1*)
  then have "simple_path ?p1"
    unfolding simple_path_def
    using make_polygonal_path_gives_path by blast
  moreover have "closed_path ?p1"
    using polygon_pathstart polygon_pathfinish
    unfolding closed_path_def
    using elem_prop1 make_polygonal_path_gives_path
    by (smt (verit, best) append_is_Nil_conv last_ConsR last_appendR last_conv_nth last_snoc list.discI nth_Cons_0 rev_append singleton_rev_conv)
  ultimately have polygon_p1: "polygon ?p1" unfolding polygon_def polygonal_path_def by fastforce


  have path_image_int: "path_image ?c2 \<subseteq> path_image (make_polygonal_path (vts @ [vts ! 0]))"
    unfolding path_image_def using path_image_p
    by (simp add: p_is path_image_def)
  then have vts_subset_c2c3: "path_image ?c2 \<inter>  path_image ?c3 \<subseteq> {?x, ?y}"
    using have_cut unfolding is_polygon_cut_path_def using \<open>path_image (make_polygonal_path (vts @ [vts ! 0])) \<inter> path_image cutpath \<subseteq> {vts ! 0, vts ! i}\<close> by auto
  have other_subset3: "{vts ! 0, vts ! i} \<subseteq> path_image ?c2"
     using vertices_on_path_image by fastforce
   have other_subset4: "{vts ! 0, vts ! i} \<subseteq> path_image ?c3"
     unfolding assms using vertices_on_path_image by fastforce
  have c2_inter_c3: "path_image ?c2 \<inter>  path_image ?c3 = {vts ! 0, vts ! i}"
    using vts_subset_c2c3 other_subset3 other_subset4 by blast
 have path_p2: "path ?p2"
   using make_polygonal_path_gives_path by blast
  have "pathfinish ?p2 = vts ! 0"
    using polygon_pathfinish 
    by (metis Nil_is_append_conv last_appendR last_conv_nth last_snoc list.discI)
  then have closed_p2: "closed_path ?p2"
    unfolding closed_path_def using polygon_pathstart 
    using path_p2 by auto

  (* Prove loop_free ?p2*)
  have "([vts ! 0] @ cutvts @ [vts ! i]) @ drop i (drop 1 vts) @ [vts ! 0] =
      ([vts ! 0] @ cutvts @ [vts ! i]) @ tl ([vts ! i] @ drop i (drop 1 vts) @ [vts ! 0])" by force
  moreover have "loop_free cutpath \<and>
      loop_free (make_polygonal_path ([vts ! i] @ drop i (drop 1 vts) @ [vts ! 0]))"
    by (metis \<open>loop_free (reversepath (make_polygonal_path ([vts ! i] @ drop i (drop 1 vts) @ [vts ! 0])))\<close> cutpath loop_free loop_free_reversepath rev_rev_ident rev_vts_is_loop_free reversepath_reversepath)
  moreover have "path_image cutpath \<inter> path_image (make_polygonal_path ([vts ! i] @ drop i (drop 1 vts) @ [vts ! 0]))
      \<subseteq> {pathstart cutpath,
      pathstart (make_polygonal_path ([vts ! i] @ drop i (drop 1 vts) @ [vts ! 0]))}"
    using c2_inter_c3 cutpath polygon_pathstart by auto
  moreover have "last ([vts ! i] @ drop i (drop 1 vts) @ [vts ! 0]) \<noteq> hd ([vts ! 0] @ cutvts @ [vts ! i]) \<longrightarrow>
      path_image cutpath \<inter> path_image (make_polygonal_path ([vts ! i] @ drop i (drop 1 vts) @ [vts ! 0]))
      \<subseteq> {pathstart (make_polygonal_path ([vts ! i] @ drop i (drop 1 vts) @ [vts ! 0]))}"
    by simp
  moreover have "last ([vts ! 0] @ cutvts @ [vts ! i]) = hd ([vts ! i] @ drop i (drop 1 vts) @ [vts ! 0])"
    by simp
  moreover have "arc cutpath \<and> arc (make_polygonal_path ([vts ! i] @ drop i (drop 1 vts) @ [vts ! 0]))"
    by (metis (no_types, lifting) arc_simple_path arcs calculation(2) finish_c1 finish_c2 have_cut is_polygon_cut_path_def make_polygonal_path_gives_path pathfinish_reversepath pathstart_reversepath simple_path_def start_c1 start_c2)
  ultimately have "loop_free ?p2" 
    using loop_free_append[of ?p2 ?p2_vts ?c3 ?c3_vts ?c2' ?c2'_vts,
            OF _ _ _] using cutpath by blast
  then have polygon_p2: "polygon ?p2"
    using path_p2 closed_p2  unfolding polygon_def simple_path_def polygonal_path_def 
    by blast

  (* Next, show some properties of the intersections *)
  have simple_c3: "simple_path ?c3"
    using have_cut unfolding is_polygon_cut_path_def by meson
  have start_c3: "pathstart ?c3 = ?x" unfolding assms using polygon_pathstart by simp 
  have finish_c3: "pathfinish ?c3 = ?y" unfolding assms using polygon_pathfinish by simp
  have "pathstart cutpath = ?x" using assms polygon_pathstart by force
  moreover have "pathfinish cutpath = ?y" using assms polygon_pathfinish by simp
  ultimately have vts_neq: "vts ! 0 \<noteq> vts ! i"
    using have_cut unfolding is_polygon_cut_path_def by force
  have c1_inter_c2: "path_image ?c1 \<inter> path_image ?c2 = {vts ! 0, vts ! i}"
  proof-
    obtain i where i1: "(?x # ?vts2 @ [?y] = take i (vts @ [vts!0]))" and
        i2: "([?y] @ ?vts3 @ [?x] = drop (i-1) (vts @ [vts!0]))"
      by (metis \<open>[vts ! i] @ drop i (drop 1 vts) @ [vts ! 0] = drop i (vts @ [vts ! 0])\<close> \<open>vts ! 0 # take (i - 1) (drop 1 vts) @ [vts ! i] = take (i + 1) (vts @ [vts ! 0])\<close> add.commute add_diff_cancel_left')
    moreover have 1: "i \<ge> 1 \<and> i < length (vts @ [vts!0])"
      by (metis (no_types, lifting) bot_nat_0.extremum less_one Nil_is_append_conv append_Cons calculation diff_is_0_eq drop_Cons' linorder_not_less list.inject not_Cons_self2 same_append_eq take_all vts_is vts_neq) 
    moreover have 2: "?p = make_polygonal_path (vts @ [vts!0]) \<and> loop_free ?p"
      unfolding polygon_of_def using p_is polygon_p unfolding polygon_def simple_path_def by blast
    ultimately have "path_image ?c1 \<inter> path_image (make_polygonal_path ([?y] @ ?vts3 @ [?x])) \<subseteq> {pathstart ?c1, pathstart (make_polygonal_path ([?y] @ ?vts3 @ [?x]))}"
      using loop_free_split_int[of ?p "vts @ [vts!0]" "?x # ?vts2 @ [?y]" i "[?y] @ ?vts3 @ [?x]" ?c1 "make_polygonal_path ([?y] @ ?vts3 @ [?x])" "length (vts @ [vts!0])",
                                OF 2 i1 i2 _ _ _ 1]
      by presburger
    moreover have "path_image ?c2 = path_image (make_polygonal_path ([?y] @ ?vts3 @ [?x]))" using path_image_reversepath by fast
    moreover have "pathstart (make_polygonal_path ([?y] @ ?vts3 @ [?x])) = ?y" using polygon_pathstart by auto
    moreover have "pathstart ?c1 = ?x" using polygon_pathstart by auto
    ultimately show ?thesis 
      using other_subset1 other_subset3 subset_antisym by force
  qed

  have non_empty_inter: "path_image ?c3 \<inter> inside(path_image ?c1 \<union> path_image ?c2) \<noteq> {}"
    using have_cut path_image_p p_is
    unfolding is_polygon_cut_path_def path_inside_def
    by fastforce

  have p1_minus: "((path_image ?p1) - (path_image ?c3)) = path_image ?c1 - {?x, ?y}"
    using c1_inter_c3 path_image_p1 by blast
  have p2_minus: "((path_image ?p2) - (path_image ?c3)) = path_image ?c2 - {?x, ?y}"
    using c2_inter_c3 path_image_p2 by auto
    
  then have path_im_intersect_minus: "((path_image ?p1) - (path_image ?c3)) \<inter> ((path_image ?p2) - (path_image (linepath ?x ?y))) = {}"
    using c1_inter_c2 p1_minus p2_minus 
    by blast
  have "((path_image ?p1) - (path_image ?c3)) \<union> ((path_image ?p2) - (path_image ?c3)) \<union> {?x, ?y} = ((path_image ?p1) - (path_image ?c3) \<union> {?x, ?y}) \<union> ((path_image ?p2) - (path_image ?c3) \<union> {?x, ?y})"
    by auto
  then have "((path_image ?p1) - (path_image (?c3))) \<union> ((path_image ?p2) - (path_image (?c3))) \<union> {?x, ?y} = ((path_image ?c1) - {?x, ?y} \<union> {?x, ?y}) \<union> ((path_image ?c2) - {?x, ?y} \<union> {?x, ?y})"
    using p1_minus p2_minus by simp
  then have "((path_image ?p1) - (path_image (?c3))) \<union> ((path_image ?p2) - (path_image (?c3))) \<union> {?x, ?y} = path_image ?c1 \<union> path_image ?c2"
    using other_subset1 other_subset3 by auto
  then have path_im_intersect_union: "path_image ?p = ((path_image ?p1) - (path_image (?c3))) \<union> ((path_image ?p2) - (path_image (?c3))) \<union> {?x, ?y}"
    using path_image_p  p_is by auto

  (* Finally, use split_inside_simple_closed_curve_real2 and put everything together *)
  have "inside(path_image ?c1 \<union> path_image ?c3) \<inter> inside(path_image ?c2 \<union> path_image ?c3) = {}"
 using split_inside_simple_closed_curve_real2[OF simple_c1 start_c1 finish_c1 simple_c2 start_c2 finish_c2
          simple_c3 start_c3 finish_c3 vts_neq c1_inter_c2 c1_inter_c3 c2_inter_c3 non_empty_inter] 
  by fast 
  then have empty_inter: "path_inside ?p1 \<inter> path_inside ?p2 = {}"
    using path_image_p1 path_image_p2 unfolding path_inside_def 
    by force
  have  "inside(path_image ?c1 \<union> path_image ?c3) \<union> inside(path_image ?c2 \<union> path_image ?c3) \<union>
           (path_image ?c3 - {vts ! 0, vts ! i}) = inside(path_image ?c1 \<union> path_image ?c2)"
    using split_inside_simple_closed_curve_real2[OF simple_c1 start_c1 finish_c1 simple_c2 start_c2 finish_c2
          simple_c3 start_c3 finish_c3 vts_neq c1_inter_c2 c1_inter_c3 c2_inter_c3 non_empty_inter] 
  by fast
  then have inside: "path_inside ?p1 \<union> path_inside ?p2 \<union> (path_image ?c3 - {?x, ?y}) = path_inside p"
    using path_image_p1 path_image_p1 path_image_p unfolding path_inside_def
    by (smt (z3) Diff_cancel Int_Un_distrib2 c1_inter_c2 c1_inter_c3 finish_c1 inf_commute inf_sup_absorb nonempty_simple_path_endless path_image_p2 simple_c1 start_c1) 
  have first_part: "0 < length vts \<and>
    i < length vts \<and>
    0 < i"
    using assms
    by auto
  have second_part_helper: "is_polygon_cut_path (vts @ [vts ! 0]) cutpath \<and>
        polygon ?p \<and>
        polygon ?p1 \<and>
        polygon ?p2 \<and>
        path_inside ?p1 \<inter> path_inside ?p2 = {} \<and>
        path_inside ?p1 \<union> path_inside ?p2 \<union> (path_image (?c3) - {?x, ?y}) = path_inside p
        \<and> ((path_image ?p1) - (path_image (?c3))) \<inter> ((path_image ?p2) - (path_image (?c3))) = {}
    \<and> path_image ?p = ((path_image ?p1) - (path_image (?c3))) \<union> ((path_image ?p2) - (path_image (?c3))) \<union> {?x, ?y}"
    using polygon_p p_is polygon_p1 polygon_p2 empty_inter inside have_cut path_im_intersect_minus path_im_intersect_union
  proof-
    have "{} = path_image cutpath \<union> path_image (make_polygonal_path (vts ! 0 # take (i - 1) (drop 1 vts) @ [vts ! i])) \<inter> path_image (reversepath (make_polygonal_path ([vts ! i] @ drop i (drop 1 vts) @ [vts ! 0]))) - path_image cutpath"
      using c1_inter_c2 c2_inter_c3 by fastforce
    then have "{} = (path_image cutpath \<union> path_image (make_polygonal_path (vts ! 0 # take (i - 1) (drop 1 vts) @ [vts ! i]))) \<inter> (path_image cutpath \<union> path_image (reversepath (make_polygonal_path ([vts ! i] @ drop i (drop 1 vts) @ [vts ! 0])))) - path_image cutpath"
      by blast
    then show ?thesis
      using empty_inter have_cut inside polygon_p1 polygon_p2 Int_Diff image_prop p_is path_im_intersect_union path_image_p2 polygon_p
      by auto
  qed
  have vts_relation: "(let vts1 = take 0 vts; vts2 = take (i - 0 - 1) (drop (Suc 0) vts);
         vts3 = drop (i - 0) (drop (Suc 0) vts); x = vts ! 0; y = vts ! i;
         p = make_polygonal_path (vts @ [vts ! 0]); p1 = make_polygonal_path (x # vts2 @ ?c3_rev_vts);
         p2 = make_polygonal_path (?c3_vts @ vts3 @ [x]) in 
         vts1 = [] \<and> vts2 = ?vts2 \<and> vts3 = ?vts3 \<and> p = ?p \<and> p1 = ?p1 \<and> p2 = ?p2)"
    by simp
  have second_part: "(let vts1 = take 0 vts; vts2 = take (i - 0 - 1) (drop (Suc 0) vts);
         vts3 = drop (i - 0) (drop (Suc 0) vts); x = vts ! 0; y = vts ! i;
         p = make_polygonal_path (vts @ [vts ! 0]); p1 = make_polygonal_path (x # vts2 @ ?c3_rev_vts);
         p2 = make_polygonal_path (vts1 @ ?c3_vts @ vts3 @ [vts ! 0])
     in is_polygon_cut_path (vts @ [vts ! 0]) cutpath \<and>
        polygon p \<and>
        polygon p1 \<and>
        polygon p2 \<and>
        path_inside p1 \<inter> path_inside p2 = {} \<and>
        path_inside p1 \<union> path_inside p2 \<union> (path_image cutpath - {x, y}) = path_inside p
      \<and> ((path_image p1) - (path_image (cutpath))) \<inter> ((path_image p2) - (path_image (cutpath))) = {} \<and>
        path_image p = ((path_image p1) - (path_image (cutpath))) \<union> ((path_image p2) - (path_image (cutpath))) \<union> {x, y})"
    using second_part_helper vts_relation p_is
    by (metis self_append_conv2) (* May take a couple seconds to load *)
  show ?thesis
    unfolding is_polygon_split_path_def[of vts 0 i cutvts]
    using first_part second_part 
    by (smt (verit, ccfv_threshold) append_Cons append_Nil cutpath rev.simps(2) rev_append rev_is_Nil_conv)
qed

lemma polygon_cut_path_to_split_path:
  fixes p :: "R_to_R2"
  assumes "polygon p" 
          "p = make_polygonal_path (vts @ [vts ! 0])" 
          "is_polygon_cut_path (vts @ [vts!0]) cutpath"
          "vts1 \<equiv> (take i vts)" 
          "vts2 \<equiv> (take (j - i - 1) (drop (Suc i) vts))" 
          "vts3 \<equiv> drop (j - i) (drop (Suc i) vts)"
          "x \<equiv> vts ! i" 
          "y \<equiv> vts ! j"
          "cutpath = make_polygonal_path ([x] @ cutvts @ [y])"
          "i < length vts \<and> j < length vts \<and> i < j"
          "p1 \<equiv> make_polygonal_path (x#(vts2@([y] @ (rev cutvts) @ [x])))" and
          "p2 \<equiv> make_polygonal_path (vts1 @ ([x] @ cutvts @ [y]) @ vts3 @ [(vts1 @ [x]) ! 0])"
        shows "is_polygon_split_path vts i j cutvts"
proof-
  let ?poly_vts_rot = "rotate_polygon_vertices (vts @ [vts ! 0]) i"
  let ?vts_rot = "butlast ?poly_vts_rot"
  let ?p_rot = "make_polygonal_path ?poly_vts_rot"
  let ?i_rot = "j - i"
  have rot_poly: "polygon ?p_rot" using assms(1) assms(2) rotation_is_polygon by blast
  have i_rot: "?i_rot > 0 \<and> ?i_rot < length ?poly_vts_rot - 1"
    using assms(10) rotate_polygon_vertices_same_length by fastforce
  have vtsi: "vts ! i = ?poly_vts_rot ! 0"
    using rotated_polygon_vertices[of ?poly_vts_rot "vts @ [vts!0]" i i]
    by (metis (no_types, lifting) One_nat_def Suc_1 assms(10) diff_self_eq_0 hd_conv_nth last_snoc length_append_singleton less_imp_le_nat linorder_not_le not_less_eq_eq nth_append take_all_iff take_eq_Nil)
  have vtsj: "vts ! j = ?poly_vts_rot ! ?i_rot"
    using rotated_polygon_vertices[of ?poly_vts_rot "vts @ [vts!0]" i j]
    by (smt (verit, ccfv_SIG) One_nat_def Suc_1 assms(10) butlast_snoc hd_append2 hd_conv_nth last_snoc leD length_append_singleton less_Suc_eq_le less_imp_le_nat not_less_eq_eq nth_butlast take_all_iff take_eq_Nil)
  have "is_polygon_cut_path ?poly_vts_rot cutpath"
  proof-
    have "?poly_vts_rot ! 0 \<noteq> ?poly_vts_rot ! ?i_rot"
      using assms(3) unfolding is_polygon_cut_path_def using vtsi vtsj
      using append_Cons append_is_Nil_conv assms(7) assms(8) assms(9) last_appendR last_conv_nth polygon_pathfinish polygon_pathstart
      by force
    moreover have "{?poly_vts_rot ! 0, ?poly_vts_rot ! ?i_rot} \<subseteq> set (?poly_vts_rot @ [?poly_vts_rot ! 0])"
      using assms(3) unfolding is_polygon_cut_path_def using i_rot vtsi vtsj by fastforce
    moreover have "path_image cutpath \<inter> path_image ?p_rot = {?poly_vts_rot ! 0, ?poly_vts_rot ! ?i_rot}"
      using polygon_vts_arb_rotation vtsi vtsj assms(3) is_polygon_cut_path_def
      by (metis (no_types, lifting) append.assoc append_Cons assms(7) assms(8) assms(9) last_conv_nth nth_Cons_0 polygon_pathfinish polygon_pathstart snoc_eq_iff_butlast)
    moreover have "path_image cutpath \<inter> path_inside (?p_rot) \<noteq> {}"
      using vtsi vtsj assms(3) polygon_vts_arb_rotation
      unfolding is_polygon_cut_path_def path_inside_def by metis
    ultimately show ?thesis
      unfolding is_polygon_cut_path_def
      using rot_poly assms(3) is_polygon_cut_path_def rotate_polygon_vertices_same_set vtsi vtsj
      by (metis polygon_vts_arb_rotation)
  qed
  then have rot_cut: "is_polygon_cut_path (?vts_rot @ [?vts_rot!0]) cutpath"
    by (metis butlast_snoc rotate_polygon_vertices_def)
  have rot_cut_butlast: "make_polygonal_path ?poly_vts_rot = make_polygonal_path (?vts_rot @ [?vts_rot!0])"
    by (metis butlast_snoc rotate_polygon_vertices_def)
  have split_rot: "is_polygon_split_path ?vts_rot 0 ?i_rot cutvts"
    using rot_cut rot_cut_butlast
    by (smt (verit, ccfv_SIG) assms(7) assms(8) assms(9) dual_order.strict_trans i_rot is_polygon_cut_path_def length_butlast nth_butlast polygon_cut_path_to_split_path_vtx0 vtsi vtsj)

  let ?vts1_rot = "take 0 ?vts_rot"
  let ?vts2_rot = "take (j - i - 0 - 1) (drop (Suc 0) ?vts_rot)"
  let ?vts3_rot = "drop (j - i - 0) (drop (Suc 0) ?vts_rot)"
  let ?x_rot = "?vts_rot ! 0"
  let ?y_rot = "?vts_rot ! (j - i)"
  let ?p1_rot_vts = "?x_rot # ?vts2_rot @ [?y_rot] @ (rev cutvts) @ [?x_rot]"
  let ?p1_rot = "make_polygonal_path ?p1_rot_vts"
  let ?p2_rot_vts = "?vts1_rot @ [?x_rot] @ cutvts @ [?y_rot] @ ?vts3_rot @ [?vts_rot ! 0]"
  let ?p2_rot = "make_polygonal_path ?p2_rot_vts"

  let ?p1_vts = "x # vts2 @ [y] @ (rev cutvts) @ [x]"
  let ?p2_vts = "vts1 @ [x] @ cutvts @ [y] @ vts3 @ [(vts1 @ [x]) ! 0]"

  have p2_firstlast: "hd ?p2_vts = last ?p2_vts"
    by (metis (no_types, lifting) append_is_Nil_conv append_self_conv2 hd_append2 hd_conv_nth last_appendR last_snoc list.discI list.sel(1))

  have "length (drop (Suc i) vts) = length vts - i - 1"
    by simp
  then have len_prop: "length (drop (Suc i) vts) \<ge> j - i - 1"
    using assms(9) assms(10) diff_le_mono less_or_eq_imp_le by presburger
  have drop_take: "rotate i vts = drop i vts @ take i vts"
    using rotate_drop_take[of i vts] assms(10) mod_less by presburger
  then have drop_take_suc: "drop (Suc 0) (rotate i vts) = drop (Suc i) vts @ take i vts"
    using assms(10) by simp
  then have "take (j - Suc i) (drop (Suc 0) (rotate i vts)) = take (j - Suc i) (drop (Suc i) vts)"
    using len_prop by force
  then have vts2: "take (j - i - 0 - 1) (drop (Suc 0) (butlast (rotate_polygon_vertices (vts @ [vts ! 0]) i))) = vts2"
    using assms(5) unfolding rotate_polygon_vertices_def 
    by (metis Suc_eq_plus1 butlast_snoc diff_diff_left diff_zero)

  have xy: "?x_rot = x \<and> ?y_rot = y"
    using vtsi vtsj assms by (metis is_polygon_split_path_def nth_butlast split_rot)

  moreover have "path_image p = path_image ?p_rot"
    using assms(1) assms(2) polygon_vts_arb_rotation by auto
  moreover then have "path_inside p = path_inside ?p_rot" unfolding path_inside_def by simp

  moreover have "?p1_rot_vts = ?p1_vts" using xy vts2 by presburger
  moreover then have "path_image p1 = path_image ?p1_rot" using assms by argo
  moreover then have "path_inside p1 = path_inside ?p1_rot" unfolding path_inside_def by argo
  moreover have "polygon p1"
    using calculation split_rot assms(11) unfolding is_polygon_split_path_def
    by (smt (verit, ccfv_SIG) vts2)

  moreover have "?p2_rot_vts = rotate_polygon_vertices ?p2_vts i"
  proof-
    have "butlast (vts1 @ [x] @ cutvts @ [y] @ vts3 @ [(vts1 @ [x]) ! 0])
        = vts1 @ [x] @ cutvts @ [y] @ vts3"
      by (simp add: butlast_append)
    also have "rotate i ... = [x] @ cutvts @ [y] @ vts3 @ vts1"
      using assms(4)
      by (metis (no_types, lifting) drop_take add_diff_cancel_right' append.assoc assms(10) diff_diff_cancel length_append length_drop length_rotate less_imp_le_nat rotate_append)
    finally have "rotate_polygon_vertices ?p2_vts i = [x] @ cutvts @ [y] @ vts3 @ vts1 @ [x]"
      unfolding rotate_polygon_vertices_def by simp
    moreover have "?vts3_rot = vts3 @ vts1"
      using assms(4,6) unfolding rotate_polygon_vertices_def
      by (smt (verit, del_insts) One_nat_def Suc_diff_Suc Suc_leI drop_take_suc assms(10) butlast_snoc diff_is_0_eq diff_zero drop0 drop_append i_rot le_add_diff_inverse len_prop length_drop nat_less_le)
    ultimately show ?thesis by (simp add: xy)
  qed
  moreover then have "polygon p2"
    using unrotation_is_polygon[of ?p2_vts i p2] split_rot assms(12) p2_firstlast
    unfolding is_polygon_split_path_def
    by (smt (verit) append.assoc)
  moreover then have "path_image p2 = path_image (?p2_rot)"
    using assms(12) polygon_vts_arb_rotation calculation by auto
  moreover then have "path_inside p2 = path_inside ?p2_rot" unfolding path_inside_def by presburger

  ultimately show "is_polygon_split_path vts i j cutvts"
    using split_rot unfolding is_polygon_split_path_def
    using One_nat_def assms bot_nat_0.not_eq_extremum butlast_snoc hd_append2 hd_conv_nth hd_take le_add2 length_0_conv length_Cons length_append length_butlast nth_append_length rot_cut_butlast rotate_polygon_vertices_same_length take_eq_Nil
    by (smt (verit) append.assoc butlast_conv_take have_wraparound_vertex is_polygon_cut_path_def rotate_polygon_vertices_same_set)
qed

lemma good_polygonal_path_implies_polygon_split_path:
  assumes "polygon p"
  assumes "p = make_polygonal_path (vts @ [vts!0])"
  assumes "good_polygonal_path v1 cutvts v2 (vts @ [vts!0])"
  assumes "i < length vts \<and> j < length vts"
  assumes "vts ! i = v1"
  assumes "vts ! j = v2"
  assumes "i < j"
  shows "is_polygon_split_path vts i j cutvts"
proof-
  let ?cutpath = "make_polygonal_path ([v1] @ cutvts @ [v2])"
  let ?p_path = "make_polygonal_path (vts @ [vts!0])"
  have linepath_subset: "path_image ?cutpath \<subseteq> path_inside ?p_path \<union> {v1, v2}"
    using assms(3) unfolding good_polygonal_path_def by meson
  have linepath_ends: "pathstart ?cutpath = v1 \<and> pathfinish ?cutpath = v2"
    using polygon_pathfinish polygon_pathstart by force
  then have vs_subset1: "{v1, v2} \<subseteq> path_image ?cutpath" 
    using vertices_on_path_image by fastforce
  have vs_subset2: "{v1, v2} \<subseteq> path_image (make_polygonal_path (vts @ [vts ! 0]))"
    using assms(4-6) vertices_on_path_image[of vts]
    using vertices_on_path_image by fastforce
  have "path_inside ?p_path \<inter> path_image ?p_path = {}"
    using inside_outside_polygon[OF assms(1)] assms(2) unfolding inside_outside_def
    by blast
  then have linepath_path: "path_image ?cutpath \<inter> path_image (make_polygonal_path (vts @ [vts ! 0])) = {v1, v2}"
    using linepath_subset vs_subset1 vs_subset2
    by blast
  have "?cutpath (5 / 10) \<in> path_image ?cutpath"
    unfolding path_image_def by auto
  have v1_neq_v2: "v1 \<noteq> v2"
    using assms(3) unfolding good_polygonal_path_def 
    by fastforce
  have not_v1: "?cutpath (0.5::real) = v1 \<Longrightarrow> False"
  proof - 
    assume *: "?cutpath (0.5::real) = v1"
    then have "?cutpath (0.5::real) = ?cutpath 0"
      using linepath_ends unfolding pathstart_def by simp
    moreover have "loop_free ?cutpath" using assms unfolding good_polygonal_path_def by metis
    ultimately show "False" unfolding loop_free_def by fastforce
  qed 
  have not_v2: "?cutpath (0.5::real) = v2 \<Longrightarrow> False"
  proof- 
    assume *: "?cutpath (0.5::real) = v2"
    then have "?cutpath (0.5::real) = ?cutpath 1"
      using linepath_ends unfolding pathfinish_def by simp
    moreover have "loop_free ?cutpath" using assms unfolding good_polygonal_path_def by metis
    ultimately show "False" unfolding loop_free_def by fastforce
  qed 
  then have "?cutpath (0.5::real) \<noteq> v1 \<and> ?cutpath (0.5::real) \<noteq> v2"
    using not_v1 not_v2 by auto
  then have linepath_inside: "path_image ?cutpath \<inter> path_inside (make_polygonal_path (vts @ [vts ! 0])) \<noteq> {}"
    using linepath_subset 
    using \<open>?cutpath (5 / 10) \<in> path_image ?cutpath\<close> by blast
  have "is_polygon_cut_path (vts @ [vts!0]) ?cutpath"
    using assms(3) assms(1-2) unfolding good_polygonal_path_def is_polygon_cut_path_def
    using linepath_path linepath_inside
    by (metis linepath_ends make_polygonal_path_gives_path simple_path_def)
  then show ?thesis using polygon_cut_path_to_split_path assms by blast
qed

(* a linepath split is a special case of a polygonal path split *)

lemma good_path_iff:
  "good_linepath a b vts \<longleftrightarrow> good_polygonal_path a [] b vts"
  unfolding good_linepath_def good_polygonal_path_def
  using linepath_loop_free by auto

lemma polygon_cut_iff: "is_polygon_cut (vts @ [vts!0]) (vts!i) (vts!j)
    \<longleftrightarrow> is_polygon_cut_path (vts @ [vts!0]) (linepath (vts!i) (vts!j))"
  unfolding is_polygon_cut_def is_polygon_cut_path_def
  by (metis pathfinish_linepath pathstart_linepath simple_path_linepath)

lemma polygon_split_iff: "is_polygon_split vts i j \<longleftrightarrow> is_polygon_split_path vts i j []"
  unfolding is_polygon_split_def is_polygon_split_path_def
  by (smt (verit, ccfv_threshold) append_Cons append_Nil make_polygonal_path.simps(3) polygon_cut_iff rev.simps(1))

lemma polygon_cut_to_split_vtx0:
  fixes p :: "R_to_R2"
  assumes polygon_p: "polygon p" and
          i_gt: "i > 0" and
          i_lt: "i < length vts" and
          p_is: "p = make_polygonal_path (vts @ [vts ! 0])" and
          have_cut: "is_polygon_cut (vts @ [vts!0]) (vts!0) (vts!i)"
  shows "is_polygon_split vts 0 i"
  using have_cut i_gt i_lt p_is polygon_cut_path_to_split_path_vtx0 polygon_cut_iff polygon_p polygon_split_iff
  by force

lemma polygon_cut_to_split:
  fixes p :: "R_to_R2"
  assumes "is_polygon_cut (vts @ [vts!0]) (vts!i) (vts!j)"
          "i < length vts \<and> j < length vts \<and> i < j"
  shows "is_polygon_split vts i j"
  by (metis append_Cons append_Nil assms is_polygon_cut_def make_polygonal_path.simps(3) polygon_cut_path_to_split_path polygon_cut_iff polygon_split_iff)

lemma good_linepath_implies_polygon_split:
  assumes "polygon p"
  assumes "p = make_polygonal_path (vts @ [vts!0])"
  assumes "good_linepath v1 v2 (vts @ [vts!0])"
  assumes "i < length vts \<and> j < length vts"
  assumes "vts ! i = v1"
  assumes "vts ! j = v2"
  assumes "i < j"
  shows "is_polygon_split vts i j"
  using assms good_path_iff good_polygonal_path_implies_polygon_split_path polygon_split_iff
  by auto

end