theory Polygon_Jordan_Curve
imports
  "HOL-Analysis.Cartesian_Space"
  "HOL-Analysis.Path_Connected"
  "Poincare_Bendixson.Poincare_Bendixson"
  Integral_Matrix

begin

section "Polygon Definitions"
type_synonym R_to_R2 = "(real \<Rightarrow> real^2)"

definition closed_path :: "R_to_R2 \<Rightarrow> bool" where  
  "closed_path g \<longleftrightarrow> path g \<and> pathstart g = pathfinish g"

definition path_inside :: "R_to_R2 \<Rightarrow> (real^2) set" where
  "path_inside g = inside (path_image g)"

definition path_outside :: "R_to_R2 \<Rightarrow> (real^2) set" where
  "path_outside g = outside (path_image g)"

fun make_polygonal_path :: "(real^2) list \<Rightarrow> R_to_R2" where
  "make_polygonal_path [] = linepath 0 0"
| "make_polygonal_path [a] = linepath a a"
| "make_polygonal_path [a,b] = linepath a b"
| "make_polygonal_path (a # b # xs) = (linepath a b) +++ make_polygonal_path (b # xs)"

definition polygonal_path :: "R_to_R2 \<Rightarrow> bool" where
  "polygonal_path g \<longleftrightarrow> g \<in> make_polygonal_path`{xs :: (real^2) list. True}"

definition all_integral :: "(real^2) list \<Rightarrow> bool" where
  "all_integral l = (\<forall>x \<in> set l. integral_vec x)"

definition polygon :: "R_to_R2 \<Rightarrow> bool" where
  "polygon g \<longleftrightarrow> polygonal_path g \<and> simple_path g \<and> closed_path g"

definition integral_polygon :: "R_to_R2 \<Rightarrow> bool" where
  "integral_polygon g \<longleftrightarrow>
    (polygon g \<and> (\<exists>vts. g = make_polygonal_path vts \<and> all_integral vts))"

definition make_triangle :: "real^2 \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> R_to_R2" where
  "make_triangle a b c = make_polygonal_path [a, b, c, a]"

definition polygon_of :: "R_to_R2 \<Rightarrow> (real^2) list \<Rightarrow> bool" where
  "polygon_of p vts \<longleftrightarrow> polygon p \<and> p = make_polygonal_path vts" 

definition good_linepath :: "real^2 \<Rightarrow> real^2 \<Rightarrow> (real^2) list \<Rightarrow> bool" where
  "good_linepath a b vts \<longleftrightarrow> (let p = make_polygonal_path vts in
    a \<noteq> b \<and> {a, b} \<subseteq> set vts \<and> path_image (linepath a b) \<subseteq> path_inside p \<union> {a, b})"

definition good_polygonal_path :: "real^2 \<Rightarrow> (real^2) list \<Rightarrow> real^2 \<Rightarrow> (real^2) list \<Rightarrow> bool" where
  "good_polygonal_path a cutvts b vts \<longleftrightarrow> (
    let p = make_polygonal_path vts in
    let p_cut = make_polygonal_path ([a] @ cutvts @ [b]) in
      (a \<noteq> b \<and> {a, b} \<subseteq> set vts \<and> path_image (p_cut) \<subseteq> path_inside p \<union> {a, b} \<and> loop_free p_cut))"

section "Jordan Curve Theorem for Polygons"

definition inside_outside :: "R_to_R2 \<Rightarrow> (real^2) set \<Rightarrow> (real^2) set \<Rightarrow> bool" where
  "inside_outside p ins outs \<longleftrightarrow>
    (ins \<noteq> {} \<and> open ins \<and> connected ins \<and>
    outs \<noteq> {} \<and> open outs \<and> connected outs \<and>
    bounded ins \<and> \<not> bounded outs \<and>
    ins \<inter> outs = {} \<and> ins \<union> outs = - path_image p \<and>
    frontier ins = path_image p \<and> frontier outs = path_image p)"

(* For our purposes, it helps to have the same result as Jordan_inside_outside_R2
   outside of the locale (and specialized to paths of our type) *)
lemma Jordan_inside_outside_real2:
  fixes p :: "real \<Rightarrow> real^2"
  assumes "simple_path p" "pathfinish p = pathstart p"
  shows "inside(path_image p) \<noteq> {} \<and>
          open(inside(path_image p)) \<and>
          connected(inside(path_image p)) \<and>
          outside(path_image p) \<noteq> {} \<and>
          open(outside(path_image p)) \<and>
          connected(outside(path_image p)) \<and>
          bounded(inside(path_image p)) \<and>
          \<not> bounded(outside(path_image p)) \<and>
          inside(path_image p) \<inter> outside(path_image p) = {} \<and>
          inside(path_image p) \<union> outside(path_image p) =
          - path_image p \<and>
          frontier(inside(path_image p)) = path_image p \<and>
          frontier(outside(path_image p)) = path_image p"
proof -
have good_type: "c1_on_open_R2_axioms TYPE((real, 2) vec)"
    unfolding c1_on_open_R2_axioms_def by auto
   have "inside(path_image p) \<noteq> {} \<and>
          open(inside(path_image p)) \<and>
          connected(inside(path_image p)) \<and>
          outside(path_image p) \<noteq> {} \<and>
          open(outside(path_image p)) \<and>
          connected(outside(path_image p)) \<and>
          bounded(inside(path_image p)) \<and>
          \<not> bounded(outside(path_image p)) \<and>
          inside(path_image p) \<inter> outside(path_image p) = {} \<and>
          inside(path_image p) \<union> outside(path_image p) =
          - path_image p \<and>
          frontier(inside(path_image p)) = path_image p \<and>
          frontier(outside(path_image p)) = path_image p"
    using assms c1_on_open_R2.Jordan_inside_outside_R2[of _  _ _ p]
    unfolding c1_on_open_R2_def c1_on_open_euclidean_def c1_on_open_def using good_type
    by (metis continuous_on_empty equals0D open_empty)
  then show ?thesis unfolding inside_outside_def
    using path_inside_def path_outside_def by auto
qed

lemma inside_outside_polygon:
  fixes p :: "R_to_R2"
  assumes polygon: "polygon p"
  shows "inside_outside p (path_inside p) (path_outside p)"
proof-
  have good_type: "c1_on_open_R2_axioms TYPE((real, 2) vec)"
    unfolding c1_on_open_R2_axioms_def by auto
  have "simple_path p" "pathfinish p = pathstart p" using assms polygon_def closed_path_def by auto
  then show ?thesis using Jordan_inside_outside_real2 unfolding inside_outside_def
    using path_inside_def path_outside_def by auto
qed

(* Heavily relies on Jordan_inside_outside_R2 from the existing libraries *)
lemma inside_outside_unique:
  fixes p :: "R_to_R2"
  assumes "polygon p"
  assumes io1: "inside_outside p inside1 outside1"
  assumes io2: "inside_outside p inside2 outside2"
  shows "inside1 = inside2 \<and> outside1 = outside2"
proof -
   have inner1: "inside(path_image p) = inside1"
    using dual_order.antisym inside_subset interior_eq interior_inside_frontier
    using io1 unfolding inside_outside_def
    by metis
  have inner2: "inside(path_image p) = inside2"
    using dual_order.antisym inside_subset interior_eq interior_inside_frontier
    using io2 unfolding inside_outside_def
    by metis
  have eq1: "inside1 = inside2"
    using inner1 inner2
    by auto 
  have h1: "inside1 \<union> outside1 = - path_image p"
    using io1 unfolding inside_outside_def by auto 
  have h2: "inside1 \<inter> outside1 = {}"
    using io1 unfolding inside_outside_def by auto 
  have outer1: "outside(path_image p) = outside1"
    using io1 inner1 unfolding inside_outside_def
    using h1 h2 outside_inside by auto
  have h3: "inside2 \<union> outside2 = - path_image p"
    using io2 unfolding inside_outside_def by auto 
  have h4: "inside2 \<inter> outside2 = {}"
    using io2 unfolding inside_outside_def by auto 
  have outer2: "outside(path_image p) = outside2"
    using io2 inner2 unfolding inside_outside_def
    using h3 h4 outside_inside by auto
  then have eq2: "outside1 = outside2"
    using outer1 outer2 by auto 
  then show ?thesis using eq1 eq2 by auto
qed

lemma polygon_jordan_curve:
  fixes p :: "R_to_R2"
  assumes "polygon p"
  obtains inside outside where
    "inside_outside p inside outside"
proof-
  have good_type: "c1_on_open_R2_axioms TYPE((real, 2) vec)"
    unfolding c1_on_open_R2_axioms_def by auto
  have "simple_path p" "pathfinish p = pathstart p" using assms polygon_def closed_path_def by auto
  then obtain inside outside where
    "inside \<noteq> {}" "open inside" "connected inside"
    "outside \<noteq> {}" "open outside" "connected outside"
    "bounded inside" "\<not> bounded outside" "inside \<inter> outside = {}"
    "inside \<union> outside = - path_image p"
    "frontier inside = path_image p"
    "frontier outside = path_image p"
    using c1_on_open_R2.Jordan_curve_R2[of _  _ _ p]
    unfolding c1_on_open_R2_def c1_on_open_euclidean_def c1_on_open_def using good_type
    by (metis continuous_on_empty equals0D open_empty)
  then show ?thesis
    using inside_outside_def that by auto 
qed

lemma connected_component_image:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "linear f" "bij f"
  shows " f ` (connected_component_set S x) = connected_component_set (f ` S) (f x)"
proof - 
  have conn: "\<And>S. connected S \<Longrightarrow> connected (f ` S)"
    by (simp add: assms(1) connected_linear_image)
  then have h1: "\<And>T. T \<in> {T. connected T \<and> x \<in> T \<and> T \<subseteq> S} \<Longrightarrow> f ` T \<in> {T. connected T \<and> (f x) \<in> T \<and> T \<subseteq> (f ` S)}"
    by auto
  then have subset1: "f ` connected_component_set S x \<subseteq> connected_component_set (f ` S) (f x)"
    using connected_component_Union   
    by (smt (verit, ccfv_threshold) assms(2) bij_is_inj connected_component_eq_empty connected_component_maximal connected_component_refl_eq connected_component_subset connected_connected_component image_is_empty inj_image_mem_iff mem_Collect_eq) have "\<And>S. connected (f ` S) \<Longrightarrow> connected S"
    using assms  connected_continuous_image assms linear_continuous_on linear_conv_bounded_linear
   bij_is_inj homeomorphism_def linear_homeomorphism_image
    by (smt (verit, del_insts))
  then have h2: "\<And>T. f ` T \<in> {T. connected T \<and> (f x) \<in> T \<and> T \<subseteq> (f ` S)} \<Longrightarrow> T \<in> {T. connected T \<and> x \<in> T \<and> T \<subseteq> S}"
    by (simp add: assms(2) bij_is_inj image_subset_iff inj_image_mem_iff subsetI)
    then have subset2: "connected_component_set (f ` S) (f x) \<subseteq> f ` connected_component_set S x"
    using connected_component_Union[of S x] connected_component_Union[of "f`S" "f x"]
    by (smt (verit, del_insts) assms(2) bij_is_inj connected_component_eq_empty connected_component_maximal connected_component_refl_eq connected_component_subset connected_connected_component image_mono inj_image_mem_iff mem_Collect_eq subset_imageE)
  show "f ` (connected_component_set S x) = connected_component_set (f ` S) (f x)"
    using subset1 subset2 by auto
qed

lemma bounded_map:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "linear f" "bij f"
  shows "bounded (f ` S) = bounded S"
proof - 
  have h1: "bounded S \<Longrightarrow> bounded (f ` S)"
    using assms 
    using bounded_linear_image linear_conv_bounded_linear by blast
  have "bounded_linear f"
    using linear_conv_bounded_linear assms by auto 
  then have "bounded_linear (inv f)"
    using assms unfolding bij_def 
    by (smt (verit, ccfv_threshold) bij_betw_def bij_betw_subset dim_image_eq inv_equality linear_conv_bounded_linear linear_surjective_isomorphism subset_UNIV)
  then have h2: "bounded (f ` S) \<Longrightarrow> bounded S"
    using assms 
    by (metis bij_is_inj bounded_linear_image image_inv_f_f)
  then show ?thesis
    using assms h1 h2 by auto
qed

lemma inside_bijective_linear_image:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  fixes c :: "real \<Rightarrow> 'a"
  assumes c_simple:"path c"
  assumes "linear f" "bij f"
  shows "inside (f ` (path_image c)) = f ` (inside(path_image c))" 
proof - 
  have set1: "{x. x \<notin> f ` path_image c} =  f ` {x. x \<notin> path_image c}"
    using assms path_image_compose unfolding bij_def 
    by (smt (verit, best) UNIV_I imageE inj_image_mem_iff mem_Collect_eq subsetI subset_antisym)
  have linear_inv: "linear (inv f)"
    using assms 
    by (metis bij_imp_bij_inv bij_is_inj inv_o_cancel linear_injective_left_inverse o_inv_o_cancel)
  have bij_inv: "bij (inv f)"
    using assms 
    using bij_imp_bij_inv by blast
  have inset1: "\<And>x. x \<in> {x. bounded (connected_component_set (- f ` path_image c) x)} \<Longrightarrow> x \<in> f ` {x. bounded (connected_component_set (- path_image c) x)}"
  proof -
    fix x
    assume *: "x \<in> {x. bounded (connected_component_set (- f ` path_image c) x)}"
    have "inj f"
        using assms(3) bij_betw_imp_inj_on by blast
    then show "x \<in> f ` {x. bounded (connected_component_set (- path_image c) x)}"
      using * connected_component_image[OF linear_inv bij_inv]
        by (smt (z3) \<open>\<And>x S. inv f ` connected_component_set S x = connected_component_set (inv f ` S) (inv f x)\<close> \<open>bij (inv f)\<close> \<open>linear (inv f)\<close> \<open>x \<in> {x. bounded (connected_component_set (- f ` path_image c) x)}\<close> bij_image_Compl_eq bounded_map connected_component_eq_empty image_empty image_inv_f_f mem_Collect_eq)
  qed
  have inset2: "\<And>x. x \<in> f ` {x. bounded (connected_component_set (- path_image c) x)} \<Longrightarrow> x \<in> {x. bounded (connected_component_set (- f ` path_image c) x)}"
  proof - 
    fix x
    assume "x \<in> f ` {x. bounded (connected_component_set (- path_image c) x)}"
    then obtain x1 where "x = f x1" "x1 \<in> {x. bounded (connected_component_set (- path_image c) x)}"
      by auto
    then show "x \<in> {x. bounded (connected_component_set (- f ` path_image c) x)}" 
      using bounded_map[OF assms(2) assms(3)] connected_component_image[OF assms(2) assms(3)]
      by (metis assms(3) bij_image_Compl_eq mem_Collect_eq)
  qed
  have set2: "f ` {x. bounded (connected_component_set (- path_image c) x)} = {x. bounded (connected_component_set (- f ` path_image c) x)}"
    using inset1 inset2 by auto
  have inset1: "\<And>x. x \<in> f ` {x. x \<notin> path_image c \<and> bounded (connected_component_set (- path_image c) x)} \<Longrightarrow> 
    x\<in> {x. x \<notin> f ` path_image c \<and> bounded (connected_component_set (- f ` path_image c) x)}"
  proof - 
    fix x
    assume "x \<in> f ` {x. x \<notin> path_image c \<and> bounded (connected_component_set (- path_image c) x)}" 
    then show "x\<in> {x. x \<notin> f ` path_image c \<and> bounded (connected_component_set (- f ` path_image c) x)}"
      by (metis (no_types, lifting) image_iff mem_Collect_eq set1 set2)
  qed
  have inset2: "\<And>x. x\<in> {x. x \<notin> f ` path_image c \<and> bounded (connected_component_set (- f ` path_image c) x)} \<Longrightarrow>
    x \<in> f ` {x. x \<notin> path_image c \<and> bounded (connected_component_set (- path_image c) x)}"
  proof - 
    fix x
    assume " x\<in> {x. x \<notin> f ` path_image c \<and> bounded (connected_component_set (- f ` path_image c) x)}"
    then show "x \<in> f ` {x. x \<notin> path_image c \<and> bounded (connected_component_set (- path_image c) x)}"
      by (smt (verit, best) image_iff mem_Collect_eq set2)
  qed
  have same_set: "{x. x \<notin> f ` path_image c \<and> bounded (connected_component_set (- f ` path_image c) x)} =
    f ` {x. x \<notin> path_image c \<and> bounded (connected_component_set (- path_image c) x)}"
    using inset1 inset2 
    by blast
  have ins1: "\<And>x. x \<in> inside (f ` path_image c) \<Longrightarrow> x \<in> f ` inside (path_image c)"
  proof - 
    fix x
    assume *: "x \<in> inside (f ` path_image c)"
    show "x \<in> f ` inside (path_image c)"
      by (metis (no_types) * same_set inside_def)
  qed
  then have "inside (f ` (path_image c)) \<subseteq> f ` (inside(path_image c))"
    by auto
  have ins2: "\<And>xa. xa \<in> inside (path_image c) \<Longrightarrow> f xa \<in> inside (f ` path_image c)"
  proof - 
    fix xa
    assume *: "xa \<in> inside (path_image c)"
    show "f xa \<in> inside (f ` path_image c)"
      by (metis (no_types, lifting) * same_set assms(3) bij_def inj_image_mem_iff inside_def mem_Collect_eq)
  qed
  then have "f ` (inside(path_image c)) \<subseteq> inside (f ` (path_image c)) "
    by auto
  show ?thesis
  using ins1 ins2 by auto 
qed

lemma bij_image_intersection:
  assumes "path_image c1 \<inter> path_image c2 = S"
  assumes "bij f"
  assumes "c \<in> path_image (f \<circ> c1) \<inter> path_image (f \<circ> c2)"
  shows "c \<in> f ` S"
  proof - 
    have "c \<in> f ` path_image c1 \<inter> f ` path_image c2"
      using assms path_image_compose[of f  c1] path_image_compose[of f c2]
      by auto
    then obtain w where c_is: "w \<in> path_image c1 \<and> w \<in> path_image c2 \<and> c = f w"
      using assms unfolding bij_def inj_def surj_def 
      by auto
    then have "w \<in> S"
      using assms by auto
    then show "c \<in> f ` S"
    using c_is by auto 
qed

(* inspired by a proof in Poincare_Bendixson, but still requires some work *)
theorem (in c1_on_open_R2) split_inside_simple_closed_curve_locale:
  fixes c :: "real \<Rightarrow> 'a"
  assumes c1_simple:"simple_path c1" and c1_start: "pathstart c1 = a" and c1_end: "pathfinish c1 = b"
  assumes c2_simple: "simple_path c2" and c2_start: "pathstart c2 = a" and c2_end: "pathfinish c2 = b"
  assumes c_simple: "simple_path c" and c_start: "pathstart c = a" and c_end: "pathfinish c = b"
  assumes a_neq_b: "a \<noteq> b"
      and c1c2: "path_image c1 \<inter> path_image c2 = {a,b}"
      and c1c: "path_image c1 \<inter> path_image c = {a,b}"
      and c2c: "path_image c2 \<inter> path_image c = {a,b}"
      and ne_12: "path_image c \<inter> inside(path_image c1 \<union> path_image c2) \<noteq> {}"
  obtains "inside(path_image c1 \<union> path_image c) \<inter> inside(path_image c2 \<union> path_image c) = {}"
          "inside(path_image c1 \<union> path_image c) \<union> inside(path_image c2 \<union> path_image c) \<union>
           (path_image c - {a,b}) = inside(path_image c1 \<union> path_image c2)"
proof - 
  let ?cc1 = "(complex_of \<circ> c1)"
  let ?cc2 = "(complex_of \<circ> c2)"
  let ?cc = "(complex_of \<circ> c)"
  have cc1_simple:"simple_path ?cc1"
    using bij_betw_imp_inj_on c1_simple complex_of_bij
    using simple_path_linear_image_eq[OF complex_of_linear]
    by blast
  have cc1_start:"pathstart ?cc1 = (complex_of a)"
    using c1_start by (simp add:pathstart_compose)
  have cc1_end:"pathfinish ?cc1 = (complex_of b)"
    using c1_end by (simp add: pathfinish_compose)
  have cc2_simple:"simple_path ?cc2"
    using c2_simple complex_of_bij bij_betw_imp_inj_on
    using simple_path_linear_image_eq[OF complex_of_linear]
    by blast
  have cc2_start:"pathstart ?cc2 = (complex_of a)"
    using c2_start by (simp add:pathstart_compose)
  have cc2_end:"pathfinish ?cc2 = (complex_of b)"
    using c2_end by (simp add: pathfinish_compose)
  have cc_simple:"simple_path ?cc" using c_simple complex_of_bij
    using bij_betw_imp_inj_on
    using simple_path_linear_image_eq[OF complex_of_linear]
    by blast
  have cc_start:"pathstart ?cc = (complex_of a)"
    using c_start by (simp add:pathstart_compose)
  have cc_end:"pathfinish ?cc = (complex_of b)"
    using c_end by (simp add: pathfinish_compose)
  have ca_neq_cb: "complex_of a \<noteq> complex_of b"
    using a_neq_b 
    by (meson bij_betw_imp_inj_on complex_of_bij inj_eq)
  have image_set_eq1: "{complex_of a, complex_of b} \<subseteq> path_image ?cc1 \<inter> path_image ?cc2"
    using c1c2 path_image_compose[of complex_of  c1] path_image_compose[of complex_of c2]
    by auto
  have image_set_eq2: "\<And>c. c \<in> path_image ?cc1 \<inter> path_image ?cc2 \<Longrightarrow> c \<in>{complex_of a, complex_of b}"
   using bij_image_intersection[of c1 c2 "{a, b}" "complex_of"] 
    using c1c2 complex_of_bij by auto
  have cc1c2: "path_image ?cc1 \<inter> path_image ?cc2 = {(complex_of a),(complex_of b)}"
    using image_set_eq1 image_set_eq2 by auto
  have image_set_eq1: "{complex_of a, complex_of b} \<subseteq> path_image ?cc1 \<inter> path_image ?cc"
    using c1c path_image_compose[of complex_of c1] path_image_compose[of complex_of c]
    by auto
  have image_set_eq2: "\<And>c. c \<in> path_image ?cc1 \<inter> path_image ?cc \<Longrightarrow> c \<in>{complex_of a, complex_of b}"
   using bij_image_intersection[of c1 c "{a, b}" "complex_of"] 
    using c1c complex_of_bij by auto
  have cc1c: "path_image ?cc1 \<inter> path_image ?cc = {(complex_of a),(complex_of b)}" 
    using image_set_eq1 image_set_eq2 by auto
  have image_set_eq1: "{complex_of a, complex_of b} \<subseteq> path_image ?cc2 \<inter> path_image ?cc"
    using c2c path_image_compose[of complex_of c2] path_image_compose[of complex_of c]
    by auto
  have image_set_eq2: "\<And>c. c \<in> path_image ?cc2 \<inter> path_image ?cc \<Longrightarrow> c \<in>{complex_of a, complex_of b}"
   using bij_image_intersection[of c2 c "{a, b}" "complex_of"] 
    using c2c complex_of_bij by auto
  have cc2c: "path_image ?cc2 \<inter> path_image ?cc = {(complex_of a),(complex_of b)}"
    using image_set_eq1 image_set_eq2 by auto

  (* show there exists a path where the union of the two path images is that path*)
  let ?j = "c1 +++ (reversepath c)"
  let ?cj = "?cc1 +++ (reversepath ?cc)"
  have cj_and_j: "path_image ?cj = complex_of ` (path_image ?j)"
    by (metis path_compose_join path_compose_reversepath path_image_compose)
  have "pathstart (reversepath c) = b"
    using c_end
    by auto 
  then have j_path: "path (c1 +++ (reversepath c))"
    using c1_end c1_simple c_simple unfolding simple_path_def path_def
    by (metis continuous_on_joinpaths path_def path_reversepath)
  then have "path ?j \<and> path_image ?j = path_image c1 \<union> path_image c" 
    using \<open>pathstart (reversepath c) = b\<close> c1_end path_image_join path_image_reversepath by blast
  then have "inside(path_image c1 \<union> path_image c) = inside(path_image ?j)"
    by auto
  have "pathstart (reversepath ?cc) = complex_of b"
    using cc_end
    by auto 
  then have cj_path: "path ?cj"
    using cc1_end cc1_simple cc_simple unfolding simple_path_def path_def
    by (metis continuous_on_joinpaths path_def path_reversepath)
  then have "path ?cj \<and> path_image ?cj = path_image ?cc1 \<union> path_image ?cc" 
    by (metis \<open>pathstart (reversepath (complex_of \<circ> c)) = complex_of b\<close> cc1_end path_image_join path_image_reversepath)
  then have ins_cj: "inside(path_image ?cc1 \<union> path_image ?cc) = inside (path_image ?cj)"
    by auto
  have "inside(path_image ?cj) = complex_of ` (inside(path_image ?j))"
    using inside_bijective_linear_image[of ?j "complex_of"] j_path
    using cj_and_j complex_of_bij complex_of_linear by presburger
  then have i1: "inside(path_image ?cc1 \<union> path_image ?cc) = complex_of ` (inside(path_image c1 \<union> path_image c))" using complex_of_real_of unfolding image_comp
    using cj_and_j 
    by (simp add: ins_cj \<open>inside (path_image c1 \<union> path_image c) = inside (path_image (c1 +++ reversepath c))\<close>) 
 
  (* Very similar to the proof of i1 *)
  let ?j2 = "c2 +++ (reversepath c)"
  let ?cj2 = "?cc2 +++ (reversepath ?cc)"
  have cj2_and_j2: "path_image ?cj2 = complex_of ` (path_image ?j2)"
    by (metis path_compose_join path_compose_reversepath path_image_compose)
  have "pathstart (reversepath c) = b"
    using c_end by auto 
  then have j2_path: "path (c2 +++ (reversepath c))"
    using c2_end c2_simple c_simple unfolding simple_path_def path_def
    by (metis continuous_on_joinpaths path_def path_reversepath)
  then have "path ?j2 \<and> path_image ?j2 = path_image c2 \<union> path_image c"
    using \<open>pathstart (reversepath c) = b\<close> c2_end path_image_join path_image_reversepath by blast 
  then have "inside(path_image c2 \<union> path_image c) = inside(path_image ?j2)"
    by auto
  have "pathstart (reversepath ?cc) = complex_of b"
    using cc_end by auto 
  then have cj2_path: "path ?cj2"
    using cc2_end cc2_simple cc_simple unfolding simple_path_def path_def
    by (metis continuous_on_joinpaths path_def path_reversepath)
  then have "path ?cj2 \<and> path_image ?cj2 = path_image ?cc2 \<union> path_image ?cc" 
    by (metis \<open>pathstart (reversepath (complex_of \<circ> c)) = complex_of b\<close> cc2_end path_image_join path_image_reversepath)
  then have ins_cj2: "inside(path_image ?cc2 \<union> path_image ?cc) = inside (path_image ?cj2)"
    by auto
  have "inside(path_image ?cj2) = complex_of ` (inside(path_image ?j2))"
    using inside_bijective_linear_image[of ?j2 "complex_of"] j2_path
    using cj2_and_j2 complex_of_bij complex_of_linear
    by presburger
  then have i2: "inside (path_image (complex_of \<circ> c2) \<union> path_image (complex_of \<circ> c))
        = complex_of ` inside (path_image c2 \<union> path_image c)"
    using cj2_and_j2 
    by (simp add: ins_cj2 \<open>inside (path_image c2 \<union> path_image c) = inside (path_image (c2 +++ reversepath c))\<close>) 

  (* Very similar to the proof of i1 *)
  let ?j3 = "c2 +++ (reversepath c1)"
  let ?cj3 = "?cc2 +++ (reversepath ?cc1)"
  have cj3_and_j3: "path_image ?cj3 = complex_of ` (path_image ?j3)"
    by (metis path_compose_join path_compose_reversepath path_image_compose)
  have "pathstart (reversepath c1) = b"
    using c1_end by auto 
  then have j3_path: "path (c2 +++ (reversepath c1))"
    using c2_end c2_simple c1_simple unfolding simple_path_def path_def
    by (metis continuous_on_joinpaths path_def path_reversepath)
  then have path_j3: "path ?j3 \<and> path_image ?j3 = path_image c2 \<union> path_image c1"
    using \<open>pathstart (reversepath c1) = b\<close> c2_end path_image_join path_image_reversepath by blast 
   then have "inside(path_image c2 \<union> path_image c1) = inside(path_image ?j3)"
    by auto
  have "pathstart (reversepath ?cc1) = complex_of b"
    using cc1_end by auto 
  then have cj3_path: "path ?cj3"
    using cc2_end cc2_simple cc1_simple unfolding simple_path_def path_def
    by (metis continuous_on_joinpaths path_def path_reversepath)
  then have path_cj3: "path ?cj3 \<and> path_image ?cj3 = path_image ?cc2 \<union> path_image ?cc1"  
    by (metis \<open>pathstart (reversepath (complex_of \<circ> c1)) = complex_of b\<close> cc2_end path_image_join path_image_reversepath)
  then have ins_cj3: "inside(path_image ?cc2 \<union> path_image ?cc1) = inside (path_image ?cj3)"
    by auto
  have "inside(path_image ?cj3) = complex_of ` (inside(path_image ?j3))"
    using inside_bijective_linear_image[of ?j3 "complex_of"] j3_path
    using cj3_and_j3 complex_of_bij complex_of_linear
    by presburger
  then have i3: "inside (path_image (complex_of \<circ> c1) \<union> path_image (complex_of \<circ> c2))
      = complex_of ` inside (path_image c1 \<union> path_image c2)" 
    by (simp add: path_cj3 path_j3 sup_commute)
  obtain y where y_prop: "y \<in> path_image c \<inter> inside (path_image c1 \<union> path_image c2)"
    using ne_12 by auto 
  then have y_in1: "complex_of y \<in> path_image ?cc"
    by (metis IntD1 image_eqI path_image_compose)
  have y_in2: "complex_of y \<in> complex_of ` (inside (path_image c1 \<union> path_image c2))"
    using y_prop by auto 
  then have cne_12: "path_image ?cc \<inter> inside(path_image ?cc1 \<union> path_image ?cc2) \<noteq> {}"
    using ne_12 y_in1 y_in2 i3 by force
  obtain for_reals: "inside(path_image ?cc1 \<union> path_image ?cc) \<inter> inside(path_image ?cc2 \<union> path_image ?cc) = {}"
          "inside(path_image ?cc1 \<union> path_image ?cc) \<union> inside(path_image ?cc2 \<union> path_image ?cc) \<union>
           (path_image ?cc - {complex_of a, complex_of b}) = inside(path_image ?cc1 \<union> path_image ?cc2)"
    using split_inside_simple_closed_curve[OF cc1_simple cc1_start cc1_end cc2_simple cc2_start
      cc2_end cc_simple cc_start cc_end ca_neq_cb cc1c2 cc1c cc2c cne_12]
    by auto
  let ?rin1 = "real_of ` inside(path_image ?cc1 \<union> path_image ?cc)"
  let ?rin2 = "real_of ` inside(path_image ?cc2 \<union> path_image ?cc)"
  
  have h1: "inside(path_image c1 \<union> path_image c) \<inter> inside(path_image c2 \<union> path_image c) \<noteq> {} \<Longrightarrow> False"
  proof-
    assume "inside(path_image c1 \<union> path_image c) \<inter> inside(path_image c2 \<union> path_image c) \<noteq> {}"
    then obtain a where a_prop: "a \<in> inside(path_image c1 \<union> path_image c) \<and> a \<in> inside(path_image c2 \<union> path_image c)"
      by auto
    have in1: "complex_of a \<in> inside (path_image (complex_of \<circ> c1) \<union> path_image (complex_of \<circ> c))"
      using a_prop i1 by auto
    have in2: "complex_of a \<in> inside (path_image (complex_of \<circ> c2) \<union> path_image (complex_of \<circ> c))"
      using a_prop i2 by auto
    show "False" using in1 in2 for_reals(1) by auto
  qed
  have h: "path_image (complex_of \<circ> c) - {complex_of a, complex_of b} = complex_of ` (path_image c) - complex_of `{a,b}"
    using path_image_compose by auto
  have "complex_of ` path_image c - complex_of ` {a, b} = complex_of ` (path_image c - {a, b})"
  proof - 
    have "\<And>x. x \<in> (complex_of ` path_image c - complex_of ` {a, b}) \<longleftrightarrow> x \<in> complex_of ` (path_image c - {a, b})"
      using Diff_iff bij_betw_imp_inj_on complex_of_bij image_iff inj_eq by (smt (z3))
    then show ?thesis by blast
  qed
  then have "path_image (complex_of \<circ> c) - {complex_of a, complex_of b} = complex_of ` (path_image c - {a,b})"
    using h by simp
  then have h2: "inside(path_image c1 \<union> path_image c) \<union> inside(path_image c2 \<union> path_image c) \<union>
      (path_image c - {a,b}) = inside(path_image c1 \<union> path_image c2)"
  proof-
    have "\<And>x . x \<in> inside(path_image c1 \<union> path_image c2) \<longleftrightarrow> complex_of x \<in> complex_of ` inside (path_image c1 \<union> path_image c2)"
      using i3 by (metis bij_betw_imp_inj_on complex_of_bij image_iff inj_eq)
    then have in_iff: "\<And>x. x \<in> inside(path_image c1 \<union> path_image c2) \<longleftrightarrow> complex_of x \<in> inside (path_image (complex_of \<circ> c1) \<union> path_image (complex_of \<circ> c)) \<union>
        inside (path_image (complex_of \<circ> c2) \<union> path_image (complex_of \<circ> c)) \<union>
        (path_image (complex_of \<circ> c) - {complex_of a, complex_of b})"
      using for_reals(2)
      using i3 by presburger
    have "\<And>x. complex_of x \<in> inside (path_image (complex_of \<circ> c1) \<union> path_image (complex_of \<circ> c)) \<union>
        inside (path_image (complex_of \<circ> c2) \<union> path_image (complex_of \<circ> c)) \<union>
        (path_image (complex_of \<circ> c) - {complex_of a, complex_of b})
        \<longleftrightarrow> complex_of x \<in> inside (path_image (complex_of \<circ> c1) \<union> path_image (complex_of \<circ> c))
          \<or> complex_of x \<in> inside (path_image (complex_of \<circ> c2) \<union> path_image (complex_of \<circ> c))
          \<or> complex_of x \<in> (path_image (complex_of \<circ> c) - {complex_of a, complex_of b})"
      by blast
    then have "\<And>x. complex_of x \<in> inside (path_image (complex_of \<circ> c1) \<union> path_image (complex_of \<circ> c)) \<union>
        inside (path_image (complex_of \<circ> c2) \<union> path_image (complex_of \<circ> c)) \<union>
        (path_image (complex_of \<circ> c) - {complex_of a, complex_of b})
        \<longleftrightarrow> x \<in> inside(path_image c1 \<union> path_image c) \<union> inside(path_image c2 \<union> path_image c) \<union>
           (path_image c - {a,b})"
      using i1 i2 i3 Un_iff \<open>path_image (complex_of \<circ> c) - {complex_of a, complex_of b} = complex_of ` (path_image c - {a, b})\<close> bij_betw_imp_inj_on complex_of_bij image_iff inj_def
      by (smt (verit, best))
    then have "\<And>x. x \<in> inside(path_image c1 \<union> path_image c2) \<longleftrightarrow> x \<in> (inside(path_image c1 \<union> path_image c) \<union> inside(path_image c2 \<union> path_image c) \<union>
          (path_image c - {a,b}))"
      using in_iff by meson
    then show ?thesis by auto
qed
  show ?thesis using that h1 h2 by auto 
qed

lemma split_inside_simple_closed_curve_real2:
  fixes c :: "real \<Rightarrow> real^2"
  assumes c1_simple:"simple_path c1" and c1_start: "pathstart c1 = a" and c1_end: "pathfinish c1 = b"
  assumes c2_simple: "simple_path c2" and c2_start: "pathstart c2 = a" and c2_end: "pathfinish c2 = b"
  assumes c_simple: "simple_path c" and c_start: "pathstart c = a" and c_end: "pathfinish c = b"
  assumes a_neq_b: "a \<noteq> b"
      and c1c2: "path_image c1 \<inter> path_image c2 = {a,b}"
      and c1c: "path_image c1 \<inter> path_image c = {a,b}"
      and c2c: "path_image c2 \<inter> path_image c = {a,b}"
      and ne_12: "path_image c \<inter> inside(path_image c1 \<union> path_image c2) \<noteq> {}"
  obtains "inside(path_image c1 \<union> path_image c) \<inter> inside(path_image c2 \<union> path_image c) = {}"
          "inside(path_image c1 \<union> path_image c) \<union> inside(path_image c2 \<union> path_image c) \<union>
            (path_image c - {a,b}) = inside(path_image c1 \<union> path_image c2)"
proof - 
  have good_type: "c1_on_open_R2_axioms TYPE((real, 2) vec)"
    unfolding c1_on_open_R2_axioms_def by auto
  then show ?thesis
    using c1_on_open_R2.split_inside_simple_closed_curve_locale[of _ _ _ c1 a b c2 c] assms
    unfolding c1_on_open_R2_def c1_on_open_euclidean_def c1_on_open_def 
    using good_type that by blast
qed

end