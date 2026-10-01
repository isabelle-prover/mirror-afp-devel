section \<open>The Detour Calculus\<close>
theory Detour_Calculus
  imports "HOL-Complex_Analysis.Complex_Analysis" "Path_Automation.Path_Automation" Detour_Prerequisites
begin

(* TODO Move *)
lemma shiftpath_reversepath_loop:
  assumes "x \<in> {0..1}" "pathstart p = pathfinish p"
  shows   "shiftpath c (reversepath p) x = reversepath (shiftpath (1-c) p) x"
  using assms
  by (auto simp: shiftpath_def reversepath_def algebra_simps pathstart_def pathfinish_def)

(* TODO Move *)
lemma eqloops_reversepath_cong:
  assumes "p \<equiv>\<^sub>\<circle> q"
  shows   "reversepath p \<equiv>\<^sub>\<circle> reversepath q"
proof -
  obtain c where pq:
     "pathstart p = pathfinish p" "pathstart q = pathfinish q" "path q" "p \<equiv>\<^sub>p shiftpath' c q"
    using assms unfolding eq_loops_def by blast

  have "reversepath p \<equiv>\<^sub>p shiftpath' (1-frac c) (reversepath q)"
  proof -
    have "reversepath p \<equiv>\<^sub>p reversepath (shiftpath' c q)"
      by (intro eq_paths_reverse pq)
    also have "shiftpath' c q = shiftpath' (frac c) q"
      by (simp add: shiftpath'_frac)
    also have *: "reversepath (shiftpath' (frac c) q) \<equiv>\<^sub>p reversepath (shiftpath (frac c) q)"
      by (rule eq_paths_sym, intro eq_paths_reverse eq_paths_shiftpath_shiftpath')
         (use pq less_imp_le[OF frac_lt_1[of c]] in auto)
    also have "\<dots> \<equiv>\<^sub>p shiftpath (1 - frac c) (reversepath q)"
    proof (rule eq_paths_refl')
      show "reversepath (shiftpath (frac c) q) x = shiftpath (1 - frac c) (reversepath q) x" 
        if "x \<in> {0..1}" for x
        using that pq by (subst shiftpath_reversepath_loop) auto
    qed (use * in blast)
    also have "\<dots> \<equiv>\<^sub>p shiftpath' (1 - frac c) (reversepath q)"
      by (intro eq_paths_shiftpath_shiftpath') (use pq less_imp_le[OF frac_lt_1[of c]] in auto)
    finally show ?thesis .
  qed
  thus ?thesis
    using pq unfolding eq_loops_def by auto
qed


subsection \<open>Local deformations of a path\<close>

locale detour_rel_aux_locale =
  fixes \<epsilon> :: real and X :: "complex set" and p :: "real \<Rightarrow> complex" and p' :: "real \<Rightarrow> complex"
  assumes \<epsilon>_pos: "\<epsilon> > 0"
  assumes p'_simple [simp, intro]: "simple_path p'"
  assumes p'_valid [simp, intro]: "valid_path p'"
  assumes X_subset: "X \<subseteq> path_image p"
  assumes X_disjoint: "X \<inter> path_image p' = {}"
  assumes homotopic: "homotopic_paths (path_image p \<union> (\<Union>x\<in>X. cball x \<epsilon>)) p p'"
begin

lemma X_disjoint' [simp]: "x \<in> X \<Longrightarrow> x \<notin> path_image p'"
  and X_subset' [simp]:   "x \<in> X \<Longrightarrow> x \<in> path_image p"
  using X_subset X_disjoint by auto

lemma p'_path [simp, intro]: "path p'"
  using p'_simple by (rule simple_path_imp_path)

lemma path_image_p': "path_image p' \<subseteq> path_image p \<union> (\<Union>x\<in>X. cball x \<epsilon>)"
  by (metis homotopic homotopic_paths_imp_subset)

lemma same_ends [simp]: "pathstart p' = pathstart p" "pathfinish p' = pathfinish p"
  using homotopic by (simp_all add: homotopic_paths_imp_pathstart homotopic_paths_imp_pathfinish)

lemma ends_not_in_X: "pathstart p \<notin> X" "pathfinish p \<notin> X"
  using X_subset X_disjoint
  by (metis X_disjoint' pathstart_in_path_image pathfinish_in_path_image same_ends)+

lemma translate:
  "detour_rel_aux_locale \<epsilon> ((+) a ` X) ((+) a \<circ> p) ((+) a \<circ> p')"
proof
  show "simple_path ((+) a \<circ> p')"
    by (subst simple_path_translation_eq) (rule p'_simple)
  show "(+) a ` X \<subseteq> path_image ((+) a \<circ> p)" and "(+) a ` X \<inter> path_image ((+) a \<circ> p') = {}"
    by (auto simp: path_image_compose)
  show "homotopic_paths (path_image ((+) a \<circ> p) \<union> (\<Union>x\<in>(+) a ` X. cball x \<epsilon>)) ((+) a \<circ> p) ((+) a \<circ> p')"
    by (intro homotopic_paths_continuous_image[OF homotopic] continuous_intros)
       (auto simp: path_image_compose)
qed (use \<epsilon>_pos in \<open>auto simp: valid_path_translation_eq\<close>)

lemma orthogonal_transformation:
  assumes f [intro]: "orthogonal_transformation f"
  shows   "detour_rel_aux_locale \<epsilon> (f ` X) (f \<circ> p) (f \<circ> p')"
proof
  from f(1) have f': "linear f" "inj f"
    using orthogonal_transformation f orthogonal_transformation_inj by blast+
  have [simp]: "f x = f y \<longleftrightarrow> x = y" for x y
    using f'(2) by (auto simp: inj_def)
  note [continuous_intros] = linear_continuous_on_compose[OF _ f'(1)]   

  show "simple_path (f \<circ> p')"
    by (subst simple_path_linear_image_eq[OF f'(1,2)]) (rule p'_simple)
  show "valid_path (f \<circ> p')"
    by (intro linear_image_valid_path f') blast
  show "f ` X \<subseteq> path_image (f \<circ> p)" and "f ` X \<inter> path_image (f \<circ> p') = {}"
    by (auto simp: path_image_compose)
  show "homotopic_paths (path_image (f \<circ> p) \<union> (\<Union>x\<in>f ` X. cball x \<epsilon>)) (f \<circ> p) (f \<circ> p')"
  proof (rule homotopic_paths_continuous_image[OF homotopic] continuous_intros)
    have "f ` (path_image p \<union> (\<Union>x\<in>X. cball x \<epsilon>)) = f ` path_image p \<union> (\<Union>x\<in>X. f ` cball x \<epsilon>)"
      by blast
    also have "(\<lambda>x. f ` cball x \<epsilon>) = (\<lambda>x. cball (f x) \<epsilon>)"
      by (intro ext image_orthogonal_transformation_cball f)
    also have "(\<Union>x\<in>X. cball (f x) \<epsilon>) = (\<Union>x\<in>f`X. cball x \<epsilon>)"
      by blast
    also have "f ` path_image p \<union> \<dots> = path_image (f \<circ> p) \<union> (\<Union>x\<in>f ` X. cball x \<epsilon>)"
      by (simp add: path_image_compose)
    finally show "f \<in> path_image p \<union> (\<Union>x\<in>X. cball x \<epsilon>) \<rightarrow> path_image (f \<circ> p) \<union> (\<Union>x\<in>f ` X. cball x \<epsilon>)"
      by auto
  qed (intro continuous_intros)
qed (use \<epsilon>_pos in auto)

lemma rotate:
  assumes "norm z = 1"
  shows   "detour_rel_aux_locale \<epsilon> ((*) z ` X) ((*) z \<circ> p) ((*) z \<circ> p')"
  by (rule orthogonal_transformation) (use assms in auto)
  
lemma analytic_image:
  assumes inj: "inj_on f (path_image p \<union> (\<Union>x\<in>X. cball x \<epsilon>))" 
  assumes ana: "f analytic_on (path_image p \<union> (\<Union>x\<in>X. cball x \<epsilon>))"
  assumes cball_image: "\<And>x. x \<in> X \<Longrightarrow> f ` cball x \<epsilon> \<subseteq> cball (f x) \<epsilon>'"
  assumes "\<epsilon>' > 0"
  shows   "detour_rel_aux_locale \<epsilon>' (f ` X) (f \<circ> p) (f \<circ> p')"
proof
  show "\<epsilon>' > 0"
    by fact
  show "valid_path (f \<circ> p')"
    using path_image_p' by (intro valid_path_compose_analytic[OF _ ana]) auto
  have cont: "continuous_on (path_image p \<union> (\<Union>x\<in>X. cball x \<epsilon>)) f"
    by (intro holomorphic_on_imp_continuous_on analytic_imp_holomorphic ana)
  show "simple_path (f \<circ> p')"
    using p'_simple path_image_p'
    by (intro simple_path_continuous_image inj_on_subset[OF inj] continuous_on_subset[OF cont])
  have "inj_on f (path_image p')"
    by (rule inj_on_subset) (use inj path_image_p' in auto)
  show "f ` X \<subseteq> path_image (f \<circ> p)" and "f ` X \<inter> path_image (f \<circ> p') = {}"
    using path_image_p' inj X_subset by (fastforce simp: path_image_compose inj_on_def)+
  show "homotopic_paths (path_image (f \<circ> p) \<union> (\<Union>x\<in>f ` X. cball x \<epsilon>')) (f \<circ> p) (f \<circ> p')"
  proof (rule homotopic_paths_continuous_image[OF homotopic cont])
    have "f ` (path_image p \<union> (\<Union>x\<in>X. cball x \<epsilon>)) = path_image (f \<circ> p) \<union> (\<Union>x\<in>X. f ` cball x \<epsilon>)"
      by (auto simp: path_image_compose)
    also have "(\<Union>x\<in>X. f ` cball x \<epsilon>) \<subseteq> (\<Union>x\<in>f`X. cball x \<epsilon>')"
      using cball_image by fast
    finally show "f \<in> path_image p \<union> (\<Union>x\<in>X. cball x \<epsilon>) \<rightarrow>
         path_image (f \<circ> p) \<union> (\<Union>x\<in>f ` X. cball x \<epsilon>')"
      by blast
  qed
qed

lemma reverse [intro!]:
  "detour_rel_aux_locale \<epsilon> X (reversepath p) (reversepath p')"
  by unfold_locales
     (use \<epsilon>_pos homotopic in \<open>auto simp: homotopic_paths_reversepath simple_path_reversepath_iff\<close>)

theorem winding_number_unchanged:
  assumes "z \<notin> path_image p \<union> (\<Union>x\<in>X. cball x \<epsilon>)"
  shows   "winding_number p' z = winding_number p z"
proof -
  from homotopic have "homotopic_paths (-{z}) p p'"
    by (rule homotopic_paths_subset) (use assms in auto)
  hence "winding_number p z = winding_number p' z"
    by (intro winding_number_homotopic_paths)
  thus ?thesis
    by simp
qed

lemma congI:
  assumes "p \<equiv>\<^sub>p p2" "p' \<equiv>\<^sub>p p'2" "valid_path p'2"
  shows   "detour_rel_aux_locale \<epsilon> X p2 p'2"
proof
  note [simp] = assms(1,2)[THEN eq_paths_imp_path_image_eq, symmetric]
  show "simple_path p'2"
    using eq_paths_imp_simple_path_iff[of p' p'2] assms p'_simple by simp
  show "X \<subseteq> path_image p2"
    using X_subset by simp
  show "X \<inter> path_image p'2 = {}"
    using X_disjoint by simp
  let ?S = "(path_image p \<union> (\<Union>x\<in>X. cball x \<epsilon>))"
  have "homotopic_paths ?S p2 p"
    by (intro eq_paths_imp_homotopic) (use assms in \<open>simp_all add: eq_paths_sym_iff\<close>)
  also have "homotopic_paths ?S p p'"
    by (rule homotopic)
  also have "homotopic_paths ?S p' p'2" using path_image_p'
    by (intro eq_paths_imp_homotopic) (use assms in \<open>simp_all add: eq_paths_sym_iff\<close>)
  finally show "homotopic_paths (path_image p2 \<union> (\<Union>x\<in>X. cball x \<epsilon>)) p2 p'2"
    by simp
qed (use \<epsilon>_pos assms in auto)

lemma mono:
  assumes "\<epsilon> \<le> \<epsilon>'"
  shows   "detour_rel_aux_locale \<epsilon>' X p p'"
  by standard
     (use assms \<epsilon>_pos X_subset X_disjoint p'_simple
      in  \<open>auto intro!: homotopic_paths_subset[OF homotopic]\<close>)

lemma cnj: "detour_rel_aux_locale \<epsilon> (cnj ` X) (cnj \<circ> p) (cnj \<circ> p')"
  by unfold_locales
     (auto simp: valid_path_cnj \<epsilon>_pos path_image_compose dist_cnj
           intro!: homotopic_paths_continuous_image [OF homotopic])

end

lemma detour_rel_aux_locale_refl [intro!]: 
  "\<epsilon> > 0 \<Longrightarrow> simple_path p \<Longrightarrow> valid_path p \<Longrightarrow> detour_rel_aux_locale \<epsilon> {} p p"
  by unfold_locales (auto dest: simple_path_imp_path)

lemma eq_paths_imp_detour_rel_aux_locale: 
  assumes "\<epsilon> > 0" "simple_path p" "valid_path q" "eq_paths p q"
  shows   "detour_rel_aux_locale \<epsilon> {} p q"
  by unfold_locales
     (use assms eq_paths_imp_simple_path_iff[OF assms(4)] in \<open>auto intro!: eq_paths_imp_homotopic\<close>)


lemma detour_rel_aux_join_aux1:
  assumes setdist: "setdist_gt \<epsilon> X1 (path_image p2)"
  shows "(\<Union>x\<in>X1. cball x \<epsilon>) \<inter> path_image p2 = {}"
  using setdist unfolding setdist_gt_def by force

lemma detour_rel_aux_join_aux2:
  assumes "detour_rel_aux_locale \<epsilon> X2 p2 p2'"
  assumes setdist: "setdist_gt \<epsilon> X1 (path_image p2)"
  shows   "X1 \<inter> path_image p2' = {}"
proof safe
  fix x assume x: "x \<in> X1" "x \<in> path_image p2'"
  interpret p2: detour_rel_aux_locale \<epsilon> X2 p2 p2'
    by fact
  from x(2) have "x \<in> path_image p2 \<union> (\<Union>y\<in>X2. cball y \<epsilon>)"
    using p2.path_image_p' by blast
  thus "x \<in> {}"
  proof safe
    assume x': "x \<in> path_image p2"
    from x and p2.\<epsilon>_pos have "x \<in> (\<Union>y\<in>X1. cball y \<epsilon>)"
      by force
    with x' show "x \<in> {}"
      using detour_rel_aux_join_aux1[OF setdist] by blast
  next
    fix z assume z: "z \<in> X2" "x \<in> cball z \<epsilon>"
    have "\<epsilon> < dist x z"
      using z(1) x p2.X_subset by (intro setdist_gtD[OF setdist]) auto
    with z(2) show "x \<in> {}"
      by (auto simp: dist_commute)
  qed
qed

locale detour_rel_aux_locale_join =
  p1: detour_rel_aux_locale \<epsilon> X1 p1 p1' +
  p2: detour_rel_aux_locale \<epsilon> X2 p2 p2' for \<epsilon> X1 p1 p1' X2 p2 p2' +
  assumes p12_simple: "simple_path (p1 +++ p2)"
  assumes pathfinish_p1 [simp]: "pathfinish p1 = pathstart p2"
  assumes setdist: "setdist_gt (2*\<epsilon>) X1 (path_image p2)" "setdist_gt (2*\<epsilon>) X2 (path_image p1)"
begin

lemma cball_X1_inter_p2: "(\<Union>x\<in>X1. cball x \<epsilon>) \<inter> path_image p2 = {}"
  and cball_X2_inter_p1: "(\<Union>x\<in>X2. cball x \<epsilon>) \<inter> path_image p1 = {}"
  by (intro detour_rel_aux_join_aux1 setdist[THEN setdist_gt_mono]; use p1.\<epsilon>_pos in simp)+

lemma X1_inter_p2: "X1 \<inter> path_image p2' = {}"
  and X2_inter_p1: "X2 \<inter> path_image p1' = {}"
proof -
  show "X1 \<inter> path_image p2' = {}"
  proof (rule detour_rel_aux_join_aux2)
    show "detour_rel_aux_locale \<epsilon> X2 p2 p2'"
      by (rule p2.detour_rel_aux_locale_axioms)
    show "setdist_gt \<epsilon> X1 (path_image p2)"
      by (intro setdist[THEN setdist_gt_mono]) (use p1.\<epsilon>_pos in auto)
  qed
next
  show "X2 \<inter> path_image p1' = {}"
  proof (rule detour_rel_aux_join_aux2)
    show "detour_rel_aux_locale \<epsilon> X1 p1 p1'"
      by (rule p1.detour_rel_aux_locale_axioms)
    show "setdist_gt \<epsilon> X2 (path_image p1)"
      by (intro setdist[THEN setdist_gt_mono]) (use p1.\<epsilon>_pos in auto)
  qed
qed

lemma X1_inter_p2' [simp]: "x \<in> X1 \<Longrightarrow> x \<notin> path_image p2'"
  and X2_inter_p1' [simp]: "x \<in> X2 \<Longrightarrow> x \<notin> path_image p1'"
  using X1_inter_p2 X2_inter_p1 by blast+

lemma X1_X2_disjoint: "X1 \<inter> X2 = {}"
proof -
  have "X1 \<inter> X2 \<subseteq> (\<Union>x\<in>X1. cball x \<epsilon>) \<inter> path_image p2"
    using p1.\<epsilon>_pos by (intro Int_mono) auto
  also have "\<dots> = {}"
    by (intro cball_X1_inter_p2)
  finally show ?thesis by blast
qed

lemma X1_X2_disjoint' [simp]: "x \<in> X1 \<Longrightarrow> x \<notin> X2"
  using X1_X2_disjoint by auto

lemma cball_X1_inter_cball_X2: 
  assumes "x \<in> X1" "y \<in> X2"
  shows   "cball x \<epsilon> \<inter> cball y \<epsilon> = {}"
proof safe
  fix z assume z: "z \<in> cball x \<epsilon>" "z \<in> cball y \<epsilon>"
  have "dist x y \<le> dist x z + dist y z"
    using dist_triangle2 by blast
  also from z have "dist x z + dist y z \<le> 2 * \<epsilon>"
    by (auto simp: dist_commute)
  finally have "dist x y \<le> 2 * \<epsilon>" .
  moreover have "dist x y > 2 * \<epsilon>"
    by (intro setdist_gtD[OF setdist(1)]) (use z p2.X_subset assms in auto)
  ultimately show "z \<in> {}"
    by simp
qed

lemma cball_X1_inter_cball_X2':
  shows   "(\<Union>y\<in>X1. cball y \<epsilon>) \<inter> (\<Union>y\<in>X2. cball y \<epsilon>) = {}"
  using cball_X1_inter_cball_X2 by blast

sublocale p12: detour_rel_aux_locale \<epsilon> "X1 \<union> X2" "p1 +++ p2" "p1' +++ p2'"
proof
  show "\<epsilon> > 0"
    by (rule p1.\<epsilon>_pos)

  have [simp]: "arc p1" "arc p2"
    using p12_simple by (elim simple_path_joinE; simp)+
  have [simp]: "arc p1'"
    by (metis \<open>arc p1\<close> arc_distinct_ends p1.p'_simple p1.same_ends simple_path_eq_arc)
  have [simp]: "arc p2'"
    by (metis \<open>arc p2\<close> arc_distinct_ends p2.p'_simple p2.same_ends simple_path_eq_arc)

  show "homotopic_paths (path_image (p1 +++ p2) \<union> (\<Union>x\<in>X1 \<union> X2. cball x \<epsilon>))
          (p1 +++ p2) (p1' +++ p2')"
    by (intro homotopic_paths_join homotopic_paths_subset[OF p1.homotopic]
              homotopic_paths_subset[OF p2.homotopic] Un_mono)
       (auto simp: path_image_join)

  show "(X1 \<union> X2) \<inter> path_image (p1' +++ p2') = {}"
    by (auto simp: path_image_join)

  show "X1 \<union> X2 \<subseteq> path_image (p1 +++ p2)"
    using p1.X_subset p2.X_subset by (subst path_image_join) auto

  show "valid_path (p1' +++ p2')"
    by (intro valid_path_join) auto

  show "simple_path (p1' +++ p2')"
  proof (rule simple_path_joinI)
    show "path_image p1' \<inter> path_image p2' \<subseteq>
          insert (pathstart p2') (if pathstart p1' = pathfinish p2' then {pathstart p1'} else {})"
    proof (intro subsetI)
      fix x assume "x \<in> path_image p1' \<inter> path_image p2'"
      also have "\<dots> \<subseteq> (path_image p1 \<union> (\<Union>x\<in>X1. cball x \<epsilon>)) \<inter> (path_image p2 \<union> (\<Union>x\<in>X2. cball x \<epsilon>))"
        using p1.path_image_p' p2.path_image_p' by blast
      also have "\<dots> \<subseteq> path_image p1 \<inter> path_image p2"
        using cball_X1_inter_p2 cball_X2_inter_p1 cball_X1_inter_cball_X2' by fast
      also have "\<dots> \<subseteq> insert (pathstart p2) (if pathstart p1 = pathfinish p2 then {pathstart p1} else {})"  
        using p12_simple by (rule simple_path_joinE') auto
      finally show "x \<in> insert (pathstart p2') (if pathstart p1' = pathfinish p2' then
                           {pathstart p1'} else {})"
        by (simp cong: if_cong)
    qed
  qed auto
qed

end



locale detour_rel_aux_loop = detour_rel_aux_locale +
  assumes simple_loop [simp, intro]: "simple_loop p"
begin

lemma loop [simp]: "pathfinish p = pathstart p"
  and p_simple [simp, intro]: "simple_path p"
  and p_path [simp, intro]: "path p"
  and p'_simple_loop [simp, intro]: "simple_loop p'"
  using simple_loop unfolding simple_loop_def by (auto intro: simple_path_imp_path)

theorem same_orientation:
  assumes "winding_number p z \<noteq> 0" "z \<notin> path_image p \<union> (\<Union>x\<in>X. cball x \<epsilon>)"
  shows   "simple_loop_orientation p' = simple_loop_orientation p"
proof -
  from assms have "z \<in> inside (path_image p)"
    using simple_loop_winding_number_cases[of p z] by (auto split: if_splits)
  with assms have winding_number: "winding_number p z \<in> {-1, 1}"
    using simple_closed_path_winding_number_inside[of p] by auto
  have p'_image: "path_image p' \<subseteq> path_image p \<union> (\<Union>x\<in>X. cball x \<epsilon>)"
    using homotopic_paths_imp_subset[OF homotopic] by auto
  from homotopic have "homotopic_paths (-{z}) p p'"
    by (rule homotopic_paths_subset) (use assms in auto)
  hence 1: "winding_number p z = winding_number p' z"
    by (intro winding_number_homotopic_paths)
  have 2: "simple_loop_orientation p = winding_number p z"
    by (intro simple_loop_orientation_eqI) (use assms winding_number in auto)
  have 3: "simple_loop_orientation p' = winding_number p' z"
    using p'_image assms 1 winding_number by (intro simple_loop_orientation_eqI) auto
  from 1 2 3 show ?thesis
    by (metis of_int_eq_iff)
qed

end


subsection \<open>The left/right detour relation\<close>

locale detour_rel_locale =
  pl: detour_rel_aux_locale \<epsilon> "L \<union> R" p pl + 
  pr: detour_rel_aux_locale \<epsilon> "L \<union> R" p pr
  for \<epsilon> L R p pl pr +
  assumes L_closed [intro]: "closed L" and R_closed [intro]: "closed R"
      and winding_number_L: "x \<in> L \<Longrightarrow> winding_number pl x - winding_number pr x = -1"
      and winding_number_R: "x \<in> R \<Longrightarrow> winding_number pl x - winding_number pr x = 1"
begin

lemma L_R_disjoint: "L \<inter> R = {}"
  using winding_number_L winding_number_R by force

lemma ends_not_in_L: "pathstart p \<notin> L" "pathfinish p \<notin> L"
  and ends_not_in_R: "pathstart p \<notin> R" "pathfinish p \<notin> R"
  using pl.ends_not_in_X pr.ends_not_in_X by blast+

lemma \<epsilon>_pos: "\<epsilon> > 0"
  using pl.\<epsilon>_pos .

lemma swap: "detour_rel_locale \<epsilon> R L p pr pl"
proof -
  interpret pl': detour_rel_aux_locale \<epsilon> "R \<union> L" p pr
    using pr.detour_rel_aux_locale_axioms by (simp add: Un_commute)
  interpret pr': detour_rel_aux_locale \<epsilon> "R \<union> L" p pl
    using pl.detour_rel_aux_locale_axioms by (simp add: Un_commute)
  show ?thesis
  proof
    show "winding_number pr x - winding_number pl x = -1" if "x \<in> R" for x
      using winding_number_R[of x] that by Groebner_Basis.algebra
    show "winding_number pr x - winding_number pl x = 1" if "x \<in> L" for x
      using winding_number_L[of x] that by Groebner_Basis.algebra
  qed auto
qed

lemma reverse [intro!]:
  "detour_rel_locale \<epsilon> R L (reversepath p) (reversepath pl) (reversepath pr)"
proof -
  interpret revpl: detour_rel_aux_locale \<epsilon> "R \<union> L" "reversepath p" "reversepath pl"
    by (subst Un_commute, rule pl.reverse)
  interpret revpr: detour_rel_aux_locale \<epsilon> "R \<union> L" "reversepath p" "reversepath pr"
    by (subst Un_commute, rule pr.reverse)
  show ?thesis
  proof unfold_locales
    show "winding_number (reversepath pl) x - winding_number (reversepath pr) x = -1"
      if "x \<in> R" for x
      using winding_number_R[OF that] that by (simp add: winding_number_reversepath algebra_simps)
  next
    show "winding_number (reversepath pl) x - winding_number (reversepath pr) x = 1"
      if "x \<in> L" for x
      using winding_number_L[OF that] that by (simp add: winding_number_reversepath algebra_simps)
  qed auto
qed

(* 
  TODO: the following should be enough for f: analytic and injective
  Then winding numbers are preserved. Lipschitz follows from analyticity as well.
  But can we get rid of the explicit Lipschitz constants?

  In fact it should even be sufficient if f is injective and continuously differentiable
  as a function \<real>\<^sup>2 \<rightarrow> \<real>\<^sup>2. Whether it preserves or flips winding numbers is determined by the
  sign of the determinant of its Jacobian (which must be constant due to injectivity).
*)
lemma winding_preserving:
  assumes ana: "f analytic_on (path_image p \<union> (\<Union>x\<in>L\<union>R. cball x \<epsilon>))"
  assumes "winding_preserving (path_image p \<union> (\<Union>x\<in>L\<union>R. cball x \<epsilon>)) f (\<lambda>x. x)"
  assumes cball_image: "\<And>x. x \<in> L \<union> R \<Longrightarrow> f ` cball x \<epsilon> \<subseteq> cball (f x) \<epsilon>'"
  assumes "path p"
  assumes "\<epsilon>' > 0"
  shows "detour_rel_locale \<epsilon>' (f ` L) (f ` R) (f \<circ> p) (f \<circ> pl) (f \<circ> pr)"
proof -
  interpret f: winding_preserving "path_image p \<union> (\<Union>x\<in>L\<union>R. cball x \<epsilon>)" f "\<lambda>x. x"
    by fact
  have cont: "continuous_on (path_image p \<union> (\<Union>x\<in>L\<union>R. cball x \<epsilon>)) f"
    by (intro holomorphic_on_imp_continuous_on analytic_imp_holomorphic ana)

  have "detour_rel_aux_locale \<epsilon>' (f ` (L \<union> R)) (f \<circ> p) (f \<circ> pl)"
    by (rule pl.analytic_image)
       (use cball_image \<open>\<epsilon>' > 0\<close>
        in   \<open>auto intro!: analytic_on_subset[OF ana] inj_on_subset[OF f.inj]\<close>)
  then interpret pl': detour_rel_aux_locale \<epsilon>' "f ` L \<union> f ` R" "f \<circ> p" "f \<circ> pl"
    by (simp add: image_Un)

  have "detour_rel_aux_locale \<epsilon>' (f ` (L \<union> R)) (f \<circ> p) (f \<circ> pr)"
    by (rule pr.analytic_image)
       (use cball_image \<open>\<epsilon>' > 0\<close>
        in   \<open>auto intro!: analytic_on_subset[OF ana] inj_on_subset[OF f.inj]\<close>)
  then interpret pr': detour_rel_aux_locale \<epsilon>' "f ` L \<union> f ` R" "f \<circ> p" "f \<circ> pr"
    by (simp add: image_Un)

  have eq: "winding_number (f \<circ> pl) (f x) - winding_number (f \<circ> pr) (f x) =
            winding_number pl x - winding_number pr x" if "x \<in> L \<union> R" for x
  proof -
    have *: "f x \<notin> path_image (f \<circ> pr)" "f x \<notin> path_image (f \<circ> pl)"
      by (metis image_Un image_eqI pr'.X_disjoint' pl'.X_disjoint' that)+
    hence "winding_number (f \<circ> pl) (f x) - winding_number (f \<circ> pr) (f x) =
          winding_number (f \<circ> pl) (f x) + winding_number (reversepath (f \<circ> pr)) (f x)"
      by (subst winding_number_reversepath) auto
    also have "\<dots> = winding_number ((f \<circ> pl) +++ reversepath (f \<circ> pr)) (f x)"
      using * by (subst winding_number_join) auto
    also have "\<dots> = winding_number (f \<circ> (pl +++ reversepath pr)) (f x)"
      by (simp add: path_compose_join path_compose_reversepath)
    also have "\<dots> = winding_number (pl +++ reversepath pr) x"
      using that pl.X_subset pl.path_image_p' pr.path_image_p'
      by (intro f.winding_number_eq) (auto simp: path_image_join)
    also have "\<dots> = winding_number pl x - winding_number pr x"
      using pr.X_disjoint pl.X_disjoint that
      by (simp add: winding_number_reversepath winding_number_join)
    finally show ?thesis .
  qed
    
  show ?thesis
  proof
    have "compact (path_image p)"
      using \<open>path p\<close> by auto
    hence "compact L" "compact R"
      using L_closed R_closed pl.X_subset by (metis compact_Int_closed inf.absorb2 le_sup_iff)+
    hence "compact (f ` L)" "compact (f ` R)"
      by (intro compact_continuous_image[OF continuous_on_subset[OF cont]];
          use pl.X_subset in force)+
    thus "closed (f ` L)" "closed (f ` R)"
      by (blast intro: compact_imp_closed)+
  next
    show "winding_number (f \<circ> pl) x - winding_number (f \<circ> pr) x = -1" if "x \<in> f ` L" for x
      using that winding_number_L eq by (auto simp: f.winding_number_eq)
  next
    show "winding_number (f \<circ> pl) x - winding_number (f \<circ> pr) x = 1" if "x \<in> f ` R" for x
      using that winding_number_R eq by (auto simp: f.winding_number_eq)
  qed
qed

lemma winding_preserving_flip:
  assumes ana: "f analytic_on (path_image p \<union> (\<Union>x\<in>L\<union>R. cball x \<epsilon>))"
  assumes "winding_preserving (path_image p \<union> (\<Union>x\<in>L\<union>R. cball x \<epsilon>)) f (\<lambda>x. -cnj x)"
  assumes cball_image: "\<And>x. x \<in> L \<union> R \<Longrightarrow> f ` cball x \<epsilon> \<subseteq> cball (f x) \<epsilon>'"
  assumes "path p"
  assumes "\<epsilon>' > 0"
  shows "detour_rel_locale \<epsilon>' (f ` R) (f ` L) (f \<circ> p) (f \<circ> pl) (f \<circ> pr)"
proof -
  interpret f: winding_preserving "path_image p \<union> (\<Union>x\<in>L\<union>R. cball x \<epsilon>)" f "\<lambda>x. -cnj x"
    by fact
  have cont: "continuous_on (path_image p \<union> (\<Union>x\<in>L\<union>R. cball x \<epsilon>)) f"
    by (intro holomorphic_on_imp_continuous_on analytic_imp_holomorphic ana)

  have "detour_rel_aux_locale \<epsilon>' (f ` (R \<union> L)) (f \<circ> p) (f \<circ> pl)"
    by (subst Un_commute, rule pl.analytic_image)
       (use cball_image \<open>\<epsilon>' > 0\<close>
        in   \<open>auto intro!: analytic_on_subset[OF ana] inj_on_subset[OF f.inj]\<close>)
  then interpret pl': detour_rel_aux_locale \<epsilon>' "f ` R \<union> f ` L" "f \<circ> p" "f \<circ> pl"
    by (simp add: image_Un)

  have "detour_rel_aux_locale \<epsilon>' (f ` (R \<union> L)) (f \<circ> p) (f \<circ> pr)"
    by (subst Un_commute, rule pr.analytic_image)
       (use cball_image \<open>\<epsilon>' > 0\<close>
        in   \<open>auto intro!: analytic_on_subset[OF ana] inj_on_subset[OF f.inj]\<close>)
  then interpret pr': detour_rel_aux_locale \<epsilon>' "f ` R \<union> f ` L" "f \<circ> p" "f \<circ> pr"
    by (simp add: image_Un)

  have eq: "winding_number (f \<circ> pl) (f x) - winding_number (f \<circ> pr) (f x) =
            -cnj (winding_number pl x - winding_number pr x)" if "x \<in> L \<union> R" for x
  proof -
    have *: "f x \<notin> path_image (f \<circ> pr)" "f x \<notin> path_image (f \<circ> pl)"
      by (metis Un_ac(3) image_Un image_eqI pl'.X_disjoint' pr'.X_disjoint' that)+
    hence "winding_number (f \<circ> pl) (f x) - winding_number (f \<circ> pr) (f x) =
          winding_number (f \<circ> pl) (f x) + winding_number (reversepath (f \<circ> pr)) (f x)"
      by (subst winding_number_reversepath) auto
    also have "\<dots> = winding_number ((f \<circ> pl) +++ reversepath (f \<circ> pr)) (f x)"
      using * by (subst winding_number_join) auto
    also have "\<dots> = winding_number (f \<circ> (pl +++ reversepath pr)) (f x)"
      by (simp add: path_compose_join path_compose_reversepath)
    also have "\<dots> = -cnj (winding_number (pl +++ reversepath pr) x)"
      using that pl.X_subset pl.path_image_p' pr.path_image_p'
      by (intro f.winding_number_eq) (auto simp: path_image_join)
    also have "winding_number (pl +++ reversepath pr) x =
               winding_number pl x - winding_number pr x"
      using pr.X_disjoint pl.X_disjoint that
      by (simp add: winding_number_reversepath winding_number_join)
    finally show ?thesis .
  qed
    
  show ?thesis
  proof
    have "compact (path_image p)"
      using \<open>path p\<close> by auto
    hence "compact L" "compact R"
      using L_closed R_closed pl.X_subset by (metis compact_Int_closed inf.absorb2 le_sup_iff)+
    hence "compact (f ` L)" "compact (f ` R)"
      by (intro compact_continuous_image[OF continuous_on_subset[OF cont]];
          use pl.X_subset in force)+
    thus "closed (f ` L)" "closed (f ` R)"
      by (blast intro: compact_imp_closed)+
  next
    show "winding_number (f \<circ> pl) x - winding_number (f \<circ> pr) x = -1" if "x \<in> f ` R" for x
    proof -
      from that obtain x' where x': "x' \<in> R" "x = f x'"
        by auto
      have "winding_number (f \<circ> pl) x - winding_number (f \<circ> pr) x =
             -cnj (winding_number pl x' - winding_number pr x')"
        unfolding x' using x' by (subst eq) auto
      also have "winding_number pl x' - winding_number pr x' = 1"
        by (rule winding_number_R) fact
      also have "-cnj 1 = -1"
        by simp
      finally show ?thesis .
    qed
  next
     show "winding_number (f \<circ> pl) x - winding_number (f \<circ> pr) x = 1" if "x \<in> f ` L" for x
    proof -
      from that obtain x' where x': "x' \<in> L" "x = f x'"
        by auto
      have "winding_number (f \<circ> pl) x - winding_number (f \<circ> pr) x =
             -cnj (winding_number pl x' - winding_number pr x')"
        unfolding x' using x' by (subst eq) auto
      also have "winding_number pl x' - winding_number pr x' = -1"
        by (rule winding_number_L) fact
      also have "-cnj (-1) = 1"
        by simp
      finally show ?thesis .
    qed
  qed
qed

lemma congI:
  assumes "p \<equiv>\<^sub>p p'" "pl \<equiv>\<^sub>p pl'" "pr \<equiv>\<^sub>p pr'" "valid_path pl'" "valid_path pr'"
  shows   "detour_rel_locale \<epsilon> L R p' pl' pr'"
proof -
  interpret pl': detour_rel_aux_locale \<epsilon> "L \<union> R" p' pl'
    by (rule detour_rel_aux_locale.congI[OF _ assms(1,2)])
       (fact pl.detour_rel_aux_locale_axioms assms)+
  interpret pr': detour_rel_aux_locale \<epsilon> "L \<union> R" p' pr'
    by (rule detour_rel_aux_locale.congI[OF _ assms(1,3)])
       (fact pr.detour_rel_aux_locale_axioms assms)+

  have [simp]: "winding_number pl' x = winding_number pl x" if "x \<in> L \<union> R" for x
    using that by (intro winding_number_homotopic_paths
                     eq_paths_imp_homotopic[OF eq_paths_sym] assms) auto
  have [simp]: "winding_number pr' x = winding_number pr x" if "x \<in> L \<union> R" for x
    using that by (intro winding_number_homotopic_paths
                     eq_paths_imp_homotopic[OF eq_paths_sym] assms) auto
  show ?thesis
  proof
    show "winding_number pl' x - winding_number pr' x = -1" if "x \<in> L" for x
      using winding_number_L[OF that] that by simp
    show "winding_number pl' x - winding_number pr' x = 1" if "x \<in> R" for x
      using winding_number_R[OF that] that by simp
  qed auto
qed

lemma mono:
  assumes "\<epsilon> \<le> \<epsilon>'"
  shows   "detour_rel_locale \<epsilon>' L R p pl pr"
proof -
  interpret pl': detour_rel_aux_locale \<epsilon>' "L \<union> R" p pl
    using pl.mono[OF assms] .
  interpret pr': detour_rel_aux_locale \<epsilon>' "L \<union> R" p pr
    using pr.mono[OF assms] .
  show ?thesis
    by standard (auto simp: winding_number_L winding_number_R)
qed

lemma cnj: "detour_rel_locale \<epsilon> (cnj ` R) (cnj ` L) (cnj \<circ> p) (cnj \<circ> pl) (cnj \<circ> pr)"
proof -
  interpret pl': detour_rel_aux_locale \<epsilon> "cnj ` R \<union> cnj ` L" "cnj \<circ> p" "cnj \<circ> pl"
    unfolding image_Un [symmetric] Un_commute[of R] by (rule pl.cnj)
  interpret pr': detour_rel_aux_locale \<epsilon> "cnj ` R \<union> cnj ` L" "cnj \<circ> p" "cnj \<circ> pr"
    unfolding image_Un [symmetric] Un_commute[of R] by (rule pr.cnj)
  show ?thesis
  proof
    have eq: "winding_number (cnj \<circ> pl) (cnj z) - winding_number (cnj \<circ> pr) (cnj z) =
              -cnj (winding_number pl z - winding_number pr z)" if "z \<in> L \<union> R" for z
      by (subst (1 2) winding_number_cnj) (use that in auto)   
    show "winding_number (cnj \<circ> pl) z - winding_number (cnj \<circ> pr) z = -1" if "z \<in> cnj ` R" for z
      using that winding_number_R by (auto simp: eq)
    show "winding_number (cnj \<circ> pl) z - winding_number (cnj \<circ> pr) z = 1" if "z \<in> cnj ` L" for z
      using that winding_number_L by (auto simp: eq)
  qed (auto intro!: closed_injective_linear_image linear_cnj simp: inj_def)
qed

end


locale detour_rel_locale_join =
  p1: detour_rel_locale \<epsilon> L1 R1 p1 pl1 pr1 +
  p2: detour_rel_locale \<epsilon> L2 R2 p2 pl2 pr2 for \<epsilon> L1 R1 p1 pl1 pr1 L2 R2 p2 pl2 pr2 +
  assumes p12_simple: "simple_path (p1 +++ p2)"
  assumes pathfinish_p1 [simp]: "pathfinish p1 = pathstart p2"
  assumes setdist: "setdist_gt (2*\<epsilon>) (L1 \<union> R1) (path_image p2)"
                   "setdist_gt (2*\<epsilon>) (L2 \<union> R2) (path_image p1)"
begin

sublocale pl: detour_rel_aux_locale_join \<epsilon> "L1 \<union> R1" p1 pl1 "L2 \<union> R2" p2 pl2
  by unfold_locales (use p12_simple setdist in \<open>simp_all add: Un_ac\<close>)

sublocale pr: detour_rel_aux_locale_join \<epsilon> "L1 \<union> R1" p1 pr1 "L2 \<union> R2" p2 pr2
  by unfold_locales (use p12_simple setdist in \<open>simp_all add: Un_ac\<close>)

sublocale p12: detour_rel_locale \<epsilon> "L1 \<union> L2" "R1 \<union> R2" "p1 +++ p2" "pl1 +++ pl2" "pr1 +++ pr2"
proof -
  write winding_number ("ind")
  interpret pl': detour_rel_aux_locale \<epsilon> "(L1 \<union> L2) \<union> (R1 \<union> R2)" "p1 +++ p2" "pl1 +++ pl2"
    using pl.p12.detour_rel_aux_locale_axioms by (simp add: Un_ac)

  interpret pr': detour_rel_aux_locale \<epsilon> "(L1 \<union> L2) \<union> (R1 \<union> R2)" "p1 +++ p2" "pr1 +++ pr2"
    using pr.p12.detour_rel_aux_locale_axioms by (simp add: Un_ac)

  show "detour_rel_locale \<epsilon> (L1 \<union> L2) (R1 \<union> R2) (p1 +++ p2) (pl1 +++ pl2) (pr1 +++ pr2)"
  proof
    show "closed (L1 \<union> L2)" "closed (R1 \<union> R2)"
      by auto
  
    show "ind (pl1 +++ pl2) x - ind (pr1 +++ pr2) x = -1" if "x \<in> L1 \<union> L2" for x
      using that
    proof
      assume x: "x \<in> L1"
      have "x \<in> cball x \<epsilon>" "x \<in> path_image p1"
        using p1.\<epsilon>_pos p1.pl.X_subset x by auto
      with x have "x \<notin> path_image p2 \<union> (\<Union>x\<in>L2 \<union> R2. cball x \<epsilon>)"
        using pl.cball_X1_inter_cball_X2[of x] pl.cball_X1_inter_p2 by blast
      thus ?thesis using p1.winding_number_L[of x]
        p2.pr.winding_number_unchanged[of x] p2.pl.winding_number_unchanged[of x] x
        by (simp add: winding_number_join algebra_simps)
    next
      assume x: "x \<in> L2"
      have "x \<in> cball x \<epsilon>" "x \<in> path_image p2"
        using p1.\<epsilon>_pos p1.pl.X_subset x by auto
      with x have "x \<notin> path_image p1 \<union> (\<Union>x\<in>L1 \<union> R1. cball x \<epsilon>)"
        using pl.cball_X1_inter_cball_X2[of _ x] pl.cball_X2_inter_p1 by blast
      thus ?thesis using p2.winding_number_L[of x]
        p1.pr.winding_number_unchanged[of x] p1.pl.winding_number_unchanged[of x] x
        by (simp add: winding_number_join algebra_simps)
    qed
  
    show "ind (pl1 +++ pl2) x - ind (pr1 +++ pr2) x = 1" if "x \<in> R1 \<union> R2" for x
      using that
    proof
      assume x: "x \<in> R1"
      have "x \<in> cball x \<epsilon>" "x \<in> path_image p1"
        using p1.\<epsilon>_pos p1.pl.X_subset x by auto
      with x have "x \<notin> path_image p2 \<union> (\<Union>x\<in>L2 \<union> R2. cball x \<epsilon>)"
        using pl.cball_X1_inter_cball_X2[of x] pl.cball_X1_inter_p2 by blast
      thus ?thesis using p1.winding_number_R[of x]
        p2.pr.winding_number_unchanged[of x] p2.pl.winding_number_unchanged[of x] x
        by (simp add: winding_number_join algebra_simps)
    next
      assume x: "x \<in> R2"
      have "x \<in> cball x \<epsilon>" "x \<in> path_image p2"
        using p1.\<epsilon>_pos p1.pl.X_subset x by auto
      with x have "x \<notin> path_image p1 \<union> (\<Union>x\<in>L1 \<union> R1. cball x \<epsilon>)"
        using pl.cball_X1_inter_cball_X2[of _ x] pl.cball_X2_inter_p1 by blast
      thus ?thesis using p2.winding_number_R[of x]
        p1.pr.winding_number_unchanged[of x] p1.pl.winding_number_unchanged[of x] x
        by (simp add: winding_number_join algebra_simps)
    qed
  qed
qed

end


locale detour_rel_loop = detour_rel_locale +
  assumes simple_loop [simp, intro]: "simple_loop p"
  assumes nontrivial: "\<exists>z. winding_number p z \<noteq> 0 \<and> z \<notin> path_image p \<union> (\<Union>x\<in>L\<union>R. cball x \<epsilon>)"
begin

sublocale pl: detour_rel_aux_loop \<epsilon> "L \<union> R" p pl
  by unfold_locales (fact simple_loop)

sublocale pr: detour_rel_aux_loop \<epsilon> "L \<union> R" p pr
  by unfold_locales (fact simple_loop)

lemma same_orientation:
  "simple_loop_orientation pl = simple_loop_orientation p"
  "simple_loop_orientation pr = simple_loop_orientation p"
proof -
  from nontrivial obtain z
    where z: "winding_number p z \<noteq> 0" "z \<notin> path_image p \<union> (\<Union>x\<in>L\<union>R. cball x \<epsilon>)"
    by auto
  show "simple_loop_orientation pl = simple_loop_orientation p"
    using pl.same_orientation[OF z] .
  show "simple_loop_orientation pr = simple_loop_orientation p"
    using pr.same_orientation[OF z] .
qed

lemma reverse_loop [intro!]:
  "detour_rel_loop \<epsilon> R L (reversepath p) (reversepath pl) (reversepath pr)"
proof -
  interpret rev: detour_rel_locale \<epsilon> R L "reversepath p" "reversepath pl" "reversepath pr"
    by (rule reverse)
  show ?thesis
  proof
    from nontrivial obtain z
      where z: "winding_number p z \<noteq> 0" "z \<notin> path_image p \<union> (\<Union>x\<in>L\<union>R. cball x \<epsilon>)"
      by blast
    show "\<exists>z. winding_number (reversepath p) z \<noteq> 0 \<and>
              z \<notin> path_image (reversepath p) \<union> (\<Union>x\<in>R \<union> L. cball x \<epsilon>)"
      using z by (intro exI[of _ z]) (auto simp: winding_number_reversepath)
  qed auto
qed

theorem
  assumes x: "x \<in> L"
  shows winding_number_L_left:  "winding_number pl x = (if simple_loop_cw p then -1 else 0)"
    and winding_number_L_right: "winding_number pr x = (if simple_loop_ccw  p then 1 else 0)"
    and inside_pl_L_iff:        "x \<in> inside (path_image pl) \<longleftrightarrow> simple_loop_cw p"
    and inside_pr_L_iff:        "x \<in> inside (path_image pr) \<longleftrightarrow> simple_loop_ccw  p"
proof -
  have [simp]: "x \<notin> path_image pl" "x \<notin> path_image pr"
    using x by auto

  define ort where "ort \<equiv> simple_loop_orientation p"
  have ort: "simple_loop_orientation pl = ort" "simple_loop_orientation pr = ort"
    unfolding ort_def by (fact same_orientation)+
  have ort_cases: "ort \<in> {-1, 1}"
    using simple_loop_orientation_cases[of p] by (auto simp: ort_def)

  have *: "winding_number pl x \<in> {0, ort}" "winding_number pr x \<in> {0, ort}"
    using simple_loop_winding_number_cases[of pl x] simple_loop_winding_number_cases[of pr x] ort
    by auto

  show l: "winding_number pl x = (if simple_loop_cw p then -1 else 0)"
   and r: "winding_number pr x = (if simple_loop_ccw p then 1 else 0)"
    using ort_cases using simple_path_not_cw_and_ccw[of p] * winding_number_L[OF x]
     by (auto simp: ort_def simple_loop_orientation_def split: if_splits)

  show "x \<in> inside (path_image pl) \<longleftrightarrow> simple_loop_cw p"
   and "x \<in> inside (path_image pr) \<longleftrightarrow> simple_loop_ccw  p"
    using l r simple_loop_winding_number_cases[of pl x]
          simple_loop_winding_number_cases[of pr x] ort by (auto split: if_splits)
qed

corollary
  assumes x: "x \<in> R"
  shows winding_number_R_left:  "winding_number pl x = (if simple_loop_ccw p then 1 else 0)"
    and winding_number_R_right: "winding_number pr x = (if simple_loop_cw p then -1 else 0)"
    and inside_pl_R_iff:        "x \<in> inside (path_image pl) \<longleftrightarrow> simple_loop_ccw p"
   and  inside_pr_R_iff:        "x \<in> inside (path_image pr) \<longleftrightarrow> simple_loop_cw  p"
proof -
  interpret rev: detour_rel_loop \<epsilon> R L "reversepath p" "reversepath pl" "reversepath pr"
    by (rule reverse_loop)
  show "winding_number pl x = (if simple_loop_ccw p then 1 else 0)"
    using rev.winding_number_L_left[OF x] x
    by (auto simp: winding_number_reversepath minus_equation_iff)
  show "winding_number pr x = (if simple_loop_cw p then -1 else 0)"
    using rev.winding_number_L_right[OF x] x
    by (auto simp: winding_number_reversepath minus_equation_iff)
  show "x \<in> inside (path_image pl) \<longleftrightarrow> simple_loop_ccw p"
   and "x \<in> inside (path_image pr) \<longleftrightarrow> simple_loop_cw  p"
    using rev.inside_pl_L_iff[OF x] rev.inside_pr_L_iff[OF x] by auto
qed

end


lemma detour_rel_locale_swap: "detour_rel_locale \<epsilon> L R p pl pr \<longleftrightarrow> detour_rel_locale \<epsilon> R L p pr pl"
  using detour_rel_locale.swap by blast

lemma eq_paths_imp_detour_rel_locale: 
  assumes "\<epsilon> > 0" "simple_path p" "eq_paths p pl" "eq_paths p pr" "valid_path pl" "valid_path pr"
  shows   "detour_rel_locale \<epsilon> {} {} p pl pr"
proof -
  interpret pl: detour_rel_aux_locale \<epsilon> "{} \<union> {}" p pl
    using assms by (auto intro!: eq_paths_imp_detour_rel_aux_locale)
  interpret pr: detour_rel_aux_locale \<epsilon> "{} \<union> {}" p pr
    using assms by (auto intro!: eq_paths_imp_detour_rel_aux_locale)
  show ?thesis
    by standard auto
qed

lemma detour_rel_localeI [intro?]:
  assumes "detour_rel_aux_locale \<epsilon> (L \<union> R) p pl" "detour_rel_aux_locale \<epsilon> (L \<union> R) p pr"
          "closed L" "closed R"
          "\<And>x. x \<in> L \<Longrightarrow> winding_number pl x - winding_number pr x = -1"
          "\<And>x. x \<in> R \<Longrightarrow> winding_number pl x - winding_number pr x = 1"
  shows "detour_rel_locale \<epsilon> L R p pl pr"
proof -
  interpret pl: detour_rel_aux_locale \<epsilon> "L \<union> R" p pl by fact
  interpret pr: detour_rel_aux_locale \<epsilon> "L \<union> R" p pr by fact
  show ?thesis using assms(3-)
    by unfold_locales auto
qed



definition detour_rel where
  "detour_rel L R p pl pr \<longleftrightarrow>
     (simple_path p \<and> valid_path p \<longrightarrow>
      eventually (\<lambda>\<epsilon>. detour_rel_locale \<epsilon> L R p (pl \<epsilon>) (pr \<epsilon>)) (at_right 0))"

lemma detour_rel_congI:
  assumes "detour_rel L R p pl pr" "p \<equiv>\<^sub>p p'" "valid_path p" "L = L'" "R = R'"
          "eventually (\<lambda>\<epsilon>. pl \<epsilon> \<equiv>\<^sub>p pl' \<epsilon>) (at_right 0)"
          "eventually (\<lambda>\<epsilon>. pr \<epsilon> \<equiv>\<^sub>p pr' \<epsilon>) (at_right 0)"
          "eventually (\<lambda>\<epsilon>. valid_path (pl' \<epsilon>)) (at_right 0)"
          "eventually (\<lambda>\<epsilon>. valid_path (pr' \<epsilon>)) (at_right 0)"
  shows   "detour_rel L' R' p' pl' pr'"
  unfolding detour_rel_def
proof safe
  assume "simple_path p'" "valid_path p'"
  hence "simple_path p"
    using assms(2) eq_paths_imp_simple_path_iff by blast
  with assms have "eventually (\<lambda>\<epsilon>. detour_rel_locale \<epsilon> L R p (pl \<epsilon>) (pr \<epsilon>)) (at_right 0)"
    by (auto simp: detour_rel_def)
  thus "eventually (\<lambda>\<epsilon>. detour_rel_locale \<epsilon> L' R' p' (pl' \<epsilon>) (pr' \<epsilon>)) (at_right 0)"
    using assms(6-9)
  proof eventually_elim
    case (elim \<epsilon>)
    show ?case
      using detour_rel_locale.congI[OF elim(1) assms(2) elim(2-5)] assms by auto
  qed
qed

lemma detour_rel_eq_paths_trans [trans]:
  assumes "p \<equiv>\<^sub>p p'" "detour_rel L R p' pl pr" "valid_path p'"
  shows   "detour_rel L R p pl pr"
  unfolding detour_rel_def
proof safe
  assume "simple_path p" "valid_path p"
  with assms(1) have "simple_path p'"
    by (simp add: eq_paths_imp_simple_path_iff)
  with assms have "eventually (\<lambda>\<epsilon>. detour_rel_locale \<epsilon> L R p' (pl \<epsilon>) (pr \<epsilon>)) (at_right 0)"
    by (auto simp: detour_rel_def)
  thus "eventually (\<lambda>\<epsilon>. detour_rel_locale \<epsilon> L R p (pl \<epsilon>) (pr \<epsilon>)) (at_right 0)"
  proof eventually_elim
    case (elim \<epsilon>)
    interpret detour_rel_locale \<epsilon> L R p' "pl \<epsilon>" "pr \<epsilon>"
      by fact
    show ?case using assms
      by (intro congI) (auto simp: eq_paths_sym_iff)
  qed
qed

lemma detour_rel_eq_paths_trans' [trans]:
  assumes "detour_rel L R p pl pr" "p \<equiv>\<^sub>p p'" "valid_path p"
  shows   "detour_rel L R p' pl pr"
  using detour_rel_eq_paths_trans[of p' p L R pl pr] assms
  by (simp add: eq_paths_sym_iff)

lemma detour_rel_imp_valid_simple_path:
  assumes "detour_rel L R p pl pr" "simple_path p" "valid_path p"
  shows   "eventually (\<lambda>\<epsilon>. simple_path (pl \<epsilon>) \<and> simple_path (pr \<epsilon>) \<and> 
             valid_path (pl \<epsilon>) \<and> valid_path (pr \<epsilon>)) (at_right 0)"
proof -
  from assms have "eventually (\<lambda>\<epsilon>. detour_rel_locale \<epsilon> L R p (pl \<epsilon>) (pr \<epsilon>)) (at_right 0)"
    by (auto simp: detour_rel_def)
  thus ?thesis
  proof eventually_elim
    case (elim \<epsilon>)
    then interpret detour_rel_locale \<epsilon> L R p "pl \<epsilon>" "pr \<epsilon>" .
    show ?case
      by blast
  qed
qed


subsection \<open>Inference rules\<close>

lemma detour_rel_image:
  assumes ind: "winding_preserving A f (\<lambda>x. x)"
  assumes ana: "f analytic_on A"
  assumes lipschitz: "M-lipschitz_on A f" "M > 0"
  assumes rel: "detour_rel L R p pl pr"
  assumes p: "valid_path (f \<circ> p) \<Longrightarrow> valid_path p" "path_image p \<subseteq> interior A" and "closed A"
  shows   "detour_rel (f ` L) (f ` R) (f \<circ> p) (\<lambda>\<epsilon>. f \<circ> pl (\<epsilon> / M)) (\<lambda>\<epsilon>. f \<circ> pr (\<epsilon> / M))"
  unfolding detour_rel_def
proof safe
  assume "simple_path (f \<circ> p)" "valid_path (f \<circ> p)"
  hence [simp]: "valid_path p"
    using p by (auto dest: simple_path_imp_path)
  hence [simp]: "path p"
    by (rule valid_path_imp_path)
  interpret f: winding_preserving A f "\<lambda>x. x"
    by fact
  have cont: "continuous_on A f"
    using lipschitz by (simp add: lipschitz_on_continuous_on)
  have "simple_path p"
    using \<open>simple_path (f \<circ> p)\<close> by (auto simp: simple_path_def loop_free_def)

  have ev: "\<forall>\<^sub>F \<epsilon> in at_right 0. detour_rel_locale \<epsilon> L R p (pl \<epsilon>) (pr \<epsilon>)"
    using \<open>simple_path p\<close> \<open>valid_path p\<close> rel unfolding detour_rel_def by blast
  then obtain \<epsilon>0 :: real where "detour_rel_locale \<epsilon>0 L R p (pl \<epsilon>0) (pr \<epsilon>0)"
    by fastforce
  interpret eps0: detour_rel_locale \<epsilon>0 L R p "pl \<epsilon>0" "pr \<epsilon>0" 
    by fact

  have "eventually (\<lambda>\<epsilon>. (\<Union>x\<in>path_image p. cball x \<epsilon>) \<subseteq> A) (at_right 0)"
    by (rule eventually_path_image_cball_subset) (use assms in auto)
  moreover have "eventually (\<lambda>\<epsilon>. \<epsilon> > 0) (at_right (0 :: real))"
    by (simp add: eventually_at_right_less)
  ultimately have "\<forall>\<^sub>F \<epsilon> in at_right 0.
                     detour_rel_locale (M * \<epsilon>) (f ` L) (f ` R) (f \<circ> p) (f \<circ> pl \<epsilon>) (f \<circ> pr \<epsilon>)"
    using ev
  proof eventually_elim
    case (elim \<epsilon>)
    interpret detour_rel_locale \<epsilon> L R p "pl \<epsilon>" "pr \<epsilon>"
      by fact
    show "detour_rel_locale (M * \<epsilon>) (f ` L) (f ` R) (f \<circ> p) (f \<circ> pl \<epsilon>) (f \<circ> pr \<epsilon>)"
    proof (rule winding_preserving)
      fix x assume x: "x \<in> L \<union> R"
      show "f ` cball x \<epsilon> \<subseteq> cball (f x) (M * \<epsilon>)"
      proof safe
        fix u assume u: "u \<in> cball x \<epsilon>"
        have "u \<in> A"
          using elim u x pl.X_subset by blast
        hence "dist (f u) (f x) \<le> M * dist u x"
          by (intro lipschitz_onD[OF lipschitz(1)])
             (use u x elim pl.X_subset p interior_subset in blast)+
        also have "\<dots> \<le> M * \<epsilon>"
          by (intro mult_left_mono) (use u elim lipschitz(2) in \<open>auto simp: dist_commute\<close>)
        finally show "f u \<in> cball (f x) (M * \<epsilon>)"
          by (simp add: dist_commute)
      qed
    next
      show "f analytic_on (path_image p \<union> (\<Union>x\<in>L \<union> R. cball x \<epsilon>))"
        by (intro analytic_on_subset[OF ana]) (use elim(1,2) in fastforce)+
    next
      show "winding_preserving (path_image p \<union> (\<Union>x\<in>L \<union> R. cball x \<epsilon>)) f (\<lambda>x. x)"
        by (rule winding_preserving_subset[OF ind])
           (use elim(1,2) in fastforce)
    qed (use \<open>path p\<close> \<open>M > 0\<close> \<epsilon>_pos in auto)
  qed
  also have "at_right 0 = filtermap ((*) (1 / M)) (at_right 0)"
    using filtermap_times_pos_at_right[of "1/M" 0] \<open>M > 0\<close> by simp
  finally show "\<forall>\<^sub>F \<epsilon> in at_right 0. detour_rel_locale \<epsilon>
                                     (f ` L) (f ` R) (f \<circ> p) (f \<circ> pl (\<epsilon> / M)) (f \<circ> pr (\<epsilon> / M))"
    using \<open>M > 0\<close> by (simp add: eventually_filtermap o_def)
qed

lemma detour_rel_mult:
  assumes "detour_rel L R p pl pr" "c \<noteq> 0"
  shows   "detour_rel ((*) c ` L) ((*) c ` R) ((*) c \<circ> p) 
             (\<lambda>\<epsilon>. (*) c \<circ> pl (\<epsilon> / norm c)) (\<lambda>\<epsilon>. (*) c \<circ> pr (\<epsilon> / norm c))"
proof (rule detour_rel_image)
  show "winding_preserving UNIV ((*) c) (\<lambda>x. x)"
    by (rule winding_preserving_mult) fact
  show "(cmod c)-lipschitz_on UNIV ((*) c)"
    by (rule lipschitz_intros)+ auto
  show "valid_path p" if "valid_path ((*) c \<circ> p)"
  proof -
    from that have "valid_path ((*) (inverse c) \<circ> ((*) c \<circ> p))"
      by (rule valid_path_compose_analytic) auto
    also have "\<dots> = p"
      using \<open>c \<noteq> 0\<close> by (simp add: fun_eq_iff)
    finally show "valid_path p" .
  qed
qed (use assms in auto)

lemma detour_rel_uminus:
  assumes "detour_rel L R p pl pr"
  shows   "detour_rel ((\<lambda>x. -x) ` L) ((\<lambda>x. -x) ` R) ((\<lambda>x. -x) \<circ> p) 
             (\<lambda>\<epsilon>. (\<lambda>x. -x) \<circ> pl \<epsilon>) (\<lambda>\<epsilon>. (\<lambda>x. -x) \<circ> pr \<epsilon>)"
  using detour_rel_mult[OF assms, of "-1"] by (simp add: o_def)

lemma detour_rel_cnj:
  assumes "detour_rel L R p pl pr"
  shows   "detour_rel (cnj ` R) (cnj ` L) (cnj \<circ> p) (\<lambda>\<epsilon>. cnj \<circ> pl \<epsilon>) (\<lambda>\<epsilon>. cnj \<circ> pr \<epsilon>)"
  unfolding detour_rel_def
proof safe
  assume "simple_path (cnj \<circ> p)" "valid_path (cnj \<circ> p)"
  with assms have "eventually (\<lambda>\<epsilon>. detour_rel_locale \<epsilon> L R p (pl \<epsilon>) (pr \<epsilon>)) (at_right 0)"
    by (simp add: detour_rel_def valid_path_cnj)
  thus "eventually (\<lambda>\<epsilon>. detour_rel_locale \<epsilon> (cnj ` R) (cnj ` L)
           (cnj \<circ> p) (cnj \<circ> pl \<epsilon>) (cnj \<circ> pr \<epsilon>)) (at_right 0)"
  proof eventually_elim
    case (elim \<epsilon>)
    thus ?case by (rule detour_rel_locale.cnj)
  qed
qed

lemma detour_rel_translate:
  assumes "detour_rel L R p pl pr"
  shows   "detour_rel ((+) c ` L) ((+) c ` R) ((+) c \<circ> p)  (\<lambda>\<epsilon>. (+) c \<circ> pl \<epsilon>) (\<lambda>\<epsilon>. (+) c \<circ> pr \<epsilon>)"
proof -
  have "detour_rel ((+) c ` L) ((+) c ` R) ((+) c \<circ> p)  (\<lambda>\<epsilon>. (+) c \<circ> pl (\<epsilon> / 1)) (\<lambda>\<epsilon>. (+) c \<circ> pr (\<epsilon> / 1))"
  proof (rule detour_rel_image)
    show "winding_preserving UNIV ((+) c) (\<lambda>x. x)"
      by (rule winding_preserving_translate)
    show "1-lipschitz_on UNIV ((+) c)"
      by (rule lipschitz_intros)+ auto?
    show "valid_path p" if "valid_path ((+) c \<circ> p)"
      using that by (simp add: valid_path_translation_eq)
  qed (use assms in \<open>auto intro!: analytic_intros\<close>)
  thus ?thesis
    by simp
qed

lemma detour_relI:
  assumes "eps > 0" "closed L" "closed R"
  assumes "\<And>\<epsilon>. \<epsilon> > 0 \<Longrightarrow> \<epsilon> < eps \<Longrightarrow> simple_path p \<Longrightarrow> valid_path p \<Longrightarrow> detour_rel_aux_locale \<epsilon> (L \<union> R) p (pl \<epsilon>)"
  assumes "\<And>\<epsilon>. \<epsilon> > 0 \<Longrightarrow> \<epsilon> < eps \<Longrightarrow> simple_path p \<Longrightarrow> valid_path p\<Longrightarrow> detour_rel_aux_locale \<epsilon> (L \<union> R) p (pr \<epsilon>)"
  assumes "\<And>\<epsilon> x. \<epsilon> > 0 \<Longrightarrow> \<epsilon> < eps \<Longrightarrow> x \<in> L \<Longrightarrow> simple_path p \<Longrightarrow> valid_path p\<Longrightarrow>
             winding_number (pl \<epsilon>) x - winding_number (pr \<epsilon>) x = -1"
  assumes "\<And>\<epsilon> x. \<epsilon> > 0 \<Longrightarrow> \<epsilon> < eps \<Longrightarrow> x \<in> R \<Longrightarrow> simple_path p \<Longrightarrow> valid_path p\<Longrightarrow>
             winding_number (pl \<epsilon>) x - winding_number (pr \<epsilon>) x = 1"
  shows   "detour_rel L R p pl pr"
  unfolding detour_rel_def eventually_at
proof (intro impI exI[of _ eps], safe)
  fix \<epsilon> :: real assume \<epsilon>: "\<epsilon> > 0" "dist \<epsilon> 0 < eps"
  assume simple: "simple_path p" and valid: "valid_path p"
  interpret pl: detour_rel_aux_locale \<epsilon> "L \<union> R" p "pl \<epsilon>"
    by (rule assms) (use \<epsilon> simple valid in auto)
  interpret pr: detour_rel_aux_locale \<epsilon> "L \<union> R" p "pr \<epsilon>"
    by (rule assms) (use \<epsilon> simple valid in auto)
  show "detour_rel_locale \<epsilon> L R p (pl \<epsilon>) (pr \<epsilon>)"
    by unfold_locales (use \<epsilon> assms(1,2,3,6,7) simple valid in auto)
qed (rule \<open>eps > 0\<close>)

lemma detour_rel_swap: "detour_rel L R p pl pr \<Longrightarrow> detour_rel R L p pr pl"
  unfolding detour_rel_def by (simp add: detour_rel_locale_swap)

lemma detour_rel_swap_iff: "detour_rel L R p pl pr \<longleftrightarrow> detour_rel R L p pr pl"
  unfolding detour_rel_def by (simp add: detour_rel_locale_swap)


named_theorems detour_rel_intros

lemma detour_rel_refl [detour_rel_intros, simp, intro!]: "detour_rel {} {} p (\<lambda>_. p) (\<lambda>_. p)"
  unfolding detour_rel_def using eventually_at_right_less[of 0]
  by unfold_locales
     (auto simp: simple_path_imp_path
           intro!: eventually_mono[OF eventually_at_right_less[of 0]] detour_rel_localeI)

lemma detour_rel_rescale:
  assumes "detour_rel L R p pl pr" "c \<ge> 1"
  shows   "detour_rel L R p (\<lambda>\<epsilon>. pl (\<epsilon> / c)) (\<lambda>\<epsilon>. pr (\<epsilon> / c))"
  unfolding detour_rel_def
proof safe
  assume "simple_path p" "valid_path p"
  with assms have "eventually (\<lambda>\<epsilon>. detour_rel_locale \<epsilon> L R p (pl \<epsilon>) (pr \<epsilon>)) (at_right 0)"
    by (auto simp: detour_rel_def)
  also have "at_right 0 = filtermap ((*) (inverse c)) (at_right 0)"
    using \<open>c \<ge> 1\<close> by (simp add: filtermap_times_pos_at_right)
  finally show "eventually (\<lambda>\<epsilon>. detour_rel_locale \<epsilon> L R p (pl (\<epsilon> / c)) (pr (\<epsilon> / c))) (at_right 0)"
    unfolding eventually_filtermap using eventually_at_right_less[of "0 :: real"]
  proof eventually_elim
    case (elim \<epsilon>)
    have "inverse c * \<epsilon> \<le> 1 * \<epsilon>"
      using elim assms by (intro mult_right_mono) (auto simp: field_simps)
    hence "detour_rel_locale \<epsilon> L R p (pl (inverse c * \<epsilon>)) (pr (inverse c * \<epsilon>))"
      by (intro detour_rel_locale.mono [OF elim(1)]) auto
    thus ?case
      by (simp add: field_simps)
  qed
qed

lemma eq_paths_imp_detour_rel:
  assumes "eq_paths p pl" "eq_paths p pr" "valid_path pl" "valid_path pr"
  shows   "detour_rel {} {} p (\<lambda>_. pl) (\<lambda>_. pr)"
proof -
  have "eventually (\<lambda>\<epsilon>::real. \<epsilon> > 0) (at_right 0)"
    by (simp add: eventually_at_right_less)
  hence "eventually (\<lambda>\<epsilon>. detour_rel_locale \<epsilon> {} {} p pl pr) (at_right 0)" if "simple_path p" "valid_path p"
    by eventually_elim (use assms that in \<open>auto intro!: eq_paths_imp_detour_rel_locale\<close>)
  thus ?thesis
    by (auto simp: detour_rel_def)
qed

lemma detour_rel_reverse [detour_rel_intros, intro!]:
  assumes "detour_rel L R p pl pr"
  shows   "detour_rel R L (reversepath p) (\<lambda>\<epsilon>. reversepath (pl \<epsilon>)) (\<lambda>\<epsilon>. reversepath (pr \<epsilon>))"
  unfolding detour_rel_def
proof safe
  assume "simple_path (reversepath p)" "valid_path (reversepath p)"
  with assms have "eventually (\<lambda>\<epsilon>. detour_rel_locale \<epsilon> L R p (pl \<epsilon>) (pr \<epsilon>)) (at_right 0)"
    by (auto simp: detour_rel_def simple_path_reversepath_iff)
  thus "eventually (\<lambda>\<epsilon>. detour_rel_locale \<epsilon> R L (reversepath p)
                          (reversepath (pl \<epsilon>)) (reversepath (pr \<epsilon>))) (at_right 0)"
    by eventually_elim (auto intro!: detour_rel_locale.reverse)
qed

lemma detour_rel_join [detour_rel_intros, intro?]:
  assumes "detour_rel L1 R1 p1 pl1 pr1"
  assumes "detour_rel L2 R2 p2 pl2 pr2"
  assumes [simp]: "pathfinish p1 = pathstart p2"
  shows   "detour_rel (L1 \<union> L2) (R1 \<union> R2) (p1 +++ p2) (\<lambda>\<epsilon>. pl1 \<epsilon> +++ pl2 \<epsilon>) (\<lambda>\<epsilon>. pr1 \<epsilon> +++ pr2 \<epsilon>)"
  unfolding detour_rel_def
proof safe
  assume simple: "simple_path (p1 +++ p2)" and valid: "valid_path (p1 +++ p2)"
  have arc [intro, simp]: "arc p1" "arc p2"
    using simple_path_joinE[OF simple] by auto
  hence simple' [intro, simp]: "simple_path p1" "simple_path p2"
    by (auto intro: arc_imp_simple_path)
  hence path' [intro, simp]: "path p1" "path p2"
    by (auto intro: simple_path_imp_path)
  have [intro, simp]: "valid_path p1" "valid_path p2"
    using valid by (auto dest!: valid_path_join_D1)

  from assms(1) obtain \<epsilon>0 where "detour_rel_locale \<epsilon>0 L1 R1 p1 (pl1 \<epsilon>0) (pr1 \<epsilon>0)"
    unfolding detour_rel_def by fastforce
  then interpret p1: detour_rel_locale \<epsilon>0 L1 R1 p1 "pl1 \<epsilon>0" "pr1 \<epsilon>0" .
  from assms(2) obtain \<epsilon>0' where "detour_rel_locale \<epsilon>0' L2 R2 p2 (pl2 \<epsilon>0') (pr2 \<epsilon>0')"
    unfolding detour_rel_def by fastforce
  then interpret p2: detour_rel_locale \<epsilon>0' L2 R2 p2 "pl2 \<epsilon>0'" "pr2 \<epsilon>0'" .

  have p1_LR2: False if x: "x \<in> path_image p1" "x \<in> L2 \<union> R2" for x
  proof -
    have "x \<in> path_image p2"
      using x(2) by auto
    hence "x = pathstart p2 \<or> x = pathfinish p2 \<and> pathstart p1 = pathfinish p2"
      using x(1) using simple_path_joinE''[OF simple, of x] by simp
    thus False
      using x(2) p2.ends_not_in_L p2.ends_not_in_R by auto
  qed

  have p2_LR1: False if x: "x \<in> path_image p2" "x \<in> L1 \<union> R1" for x
  proof -
    have x': "x \<in> path_image p1"
      using x(2) by auto
    hence "x = pathstart p2 \<or> x = pathfinish p2 \<and> pathstart p1 = pathfinish p2"
      using x(1) using simple_path_joinE''[OF simple, of x] by simp
    thus False
      using x(2) p1.ends_not_in_L p1.ends_not_in_R by auto
  qed

  have "(2 :: real) > 0"
    by simp
  note ev_lift = eventually_setdist_gt_at_right_0_mult_iff[OF this, symmetric]

  have "eventually (\<lambda>\<epsilon>. setdist_gt \<epsilon> (L1 \<union> R1) (path_image p2)) (at_right 0)"
  proof (subst setdist_gt_sym, rule compact_closed_imp_eventually_setdist_gt_at_right_0)
    show "compact (path_image p2)"
      by (simp add: compact_arc_image)
    show "path_image p2 \<inter> (L1 \<union> R1) = {}"
      using p2_LR1 by blast
  qed (auto intro: finite_imp_closed)

  moreover have "eventually (\<lambda>\<epsilon>. setdist_gt \<epsilon> (L2 \<union> R2) (path_image p1)) (at_right 0)"
  proof (subst setdist_gt_sym, rule compact_closed_imp_eventually_setdist_gt_at_right_0)
    show "compact (path_image p1)"
      by (simp add: compact_arc_image)
    show "path_image p1 \<inter> (L2 \<union> R2) = {}"
            using p1_LR2 by blast
        qed (auto intro: finite_imp_closed)

  moreover have "eventually (\<lambda>\<epsilon>. detour_rel_locale \<epsilon> L1 R1 p1 (pl1 \<epsilon>) (pr1 \<epsilon>)) (at_right 0)"
                "eventually (\<lambda>\<epsilon>. detour_rel_locale \<epsilon> L2 R2 p2 (pl2 \<epsilon>) (pr2 \<epsilon>)) (at_right 0)"
    using assms(1,2) unfolding detour_rel_def by auto
  ultimately show "eventually (\<lambda>\<epsilon>. detour_rel_locale \<epsilon> (L1 \<union> L2) (R1 \<union> R2)
                       (p1 +++ p2) (pl1 \<epsilon> +++ pl2 \<epsilon>) (pr1 \<epsilon> +++ pr2 \<epsilon>)) (at_right 0)"
    unfolding ev_lift
  proof eventually_elim
    case (elim \<epsilon>)
    interpret p1: detour_rel_locale \<epsilon> L1 R1 p1 "pl1 \<epsilon>" "pr1 \<epsilon>"
      by fact
    interpret p2: detour_rel_locale \<epsilon> L2 R2 p2 "pl2 \<epsilon>" "pr2 \<epsilon>"
      by fact
    interpret detour_rel_locale_join \<epsilon> L1 R1 p1 "pl1 \<epsilon>" "pr1 \<epsilon>" L2 R2 p2 "pl2 \<epsilon>" "pr2 \<epsilon>"
      by unfold_locales (use elim in \<open>simp_all add: simple\<close>)
    show ?case
      using p12.detour_rel_locale_axioms .
  qed
qed


subsection \<open>Basic avoidance patterns\<close>


subsubsection \<open>Generic helper lemmas\<close>

lemma detour_rel_avoid_basic:
  fixes p :: "real \<Rightarrow> complex" and L R :: "complex set"
  defines "S \<equiv> (\<lambda>\<epsilon>. path_image p \<union> (\<Union>y\<in>L\<union>R. cball y \<epsilon>))"
  assumes simple: "\<And>\<epsilon>. \<epsilon> > 0 \<Longrightarrow> \<epsilon> < eps \<Longrightarrow> simple_path p \<Longrightarrow> simple_path (p1 \<epsilon> +++ pl \<epsilon> +++ p2 \<epsilon>)"
                  "\<And>\<epsilon>. \<epsilon> > 0 \<Longrightarrow> \<epsilon> < eps \<Longrightarrow> simple_path p \<Longrightarrow> simple_path (p1 \<epsilon> +++ pr \<epsilon> +++ p2 \<epsilon>)"
  assumes LR_subset: "simple_path p \<Longrightarrow> L \<union> R \<subseteq> path_image p"
  assumes homo: "\<And>\<epsilon>. \<epsilon> > 0 \<Longrightarrow> \<epsilon> < eps \<Longrightarrow> simple_path p \<Longrightarrow> homotopic_paths (S \<epsilon>) p (p1 \<epsilon> +++ pl \<epsilon> +++ p2 \<epsilon>)"
                "\<And>\<epsilon>. \<epsilon> > 0 \<Longrightarrow> \<epsilon> < eps \<Longrightarrow> simple_path p \<Longrightarrow> homotopic_paths (S \<epsilon>) p (p1 \<epsilon> +++ pr \<epsilon> +++ p2 \<epsilon>)"
  assumes ind: "\<And>\<epsilon> x. \<epsilon> > 0 \<Longrightarrow> \<epsilon> < eps \<Longrightarrow> simple_path p \<Longrightarrow> x \<in> L \<Longrightarrow> winding_number (pl \<epsilon> +++ reversepath (pr \<epsilon>)) x = -1"
               "\<And>\<epsilon> x. \<epsilon> > 0 \<Longrightarrow> \<epsilon> < eps \<Longrightarrow> simple_path p \<Longrightarrow> x \<in> R \<Longrightarrow> winding_number (pl \<epsilon> +++ reversepath (pr \<epsilon>)) x = 1"
  assumes ends: "\<And>\<epsilon>. \<epsilon> > 0 \<Longrightarrow> \<epsilon> < eps \<Longrightarrow> simple_path p \<Longrightarrow> pathfinish (pl \<epsilon>) = pathstart (p2 \<epsilon>)"
                "\<And>\<epsilon>. \<epsilon> > 0 \<Longrightarrow> \<epsilon> < eps \<Longrightarrow> simple_path p \<Longrightarrow> pathfinish (pr \<epsilon>) = pathstart (p2 \<epsilon>)"
                "\<And>\<epsilon>. \<epsilon> > 0 \<Longrightarrow> \<epsilon> < eps \<Longrightarrow> simple_path p \<Longrightarrow> pathstart (pl \<epsilon>) = pathfinish (p1 \<epsilon>)"
                "\<And>\<epsilon>. \<epsilon> > 0 \<Longrightarrow> \<epsilon> < eps \<Longrightarrow> simple_path p \<Longrightarrow> pathstart (pr \<epsilon>) = pathfinish (p1 \<epsilon>)"
  assumes LR: "\<And>\<epsilon>. \<epsilon> > 0 \<Longrightarrow> \<epsilon> < eps \<Longrightarrow> simple_path p \<Longrightarrow> path_image (pl \<epsilon>) \<inter> (L \<union> R) = {}"
              "\<And>\<epsilon>. \<epsilon> > 0 \<Longrightarrow> \<epsilon> < eps \<Longrightarrow> simple_path p \<Longrightarrow> path_image (pr \<epsilon>) \<inter> (L \<union> R) = {}"
              "\<And>\<epsilon>. \<epsilon> > 0 \<Longrightarrow> \<epsilon> < eps \<Longrightarrow> simple_path p \<Longrightarrow> path_image (p1 \<epsilon>) \<inter> (L \<union> R) = {}"
              "\<And>\<epsilon>. \<epsilon> > 0 \<Longrightarrow> \<epsilon> < eps \<Longrightarrow> simple_path p \<Longrightarrow> path_image (p2 \<epsilon>) \<inter> (L \<union> R) = {}"
  assumes valid: "\<And>\<epsilon>. \<epsilon> > 0 \<Longrightarrow> \<epsilon> < eps \<Longrightarrow> valid_path p \<Longrightarrow> valid_path (pl \<epsilon>)"
                 "\<And>\<epsilon>. \<epsilon> > 0 \<Longrightarrow> \<epsilon> < eps \<Longrightarrow> valid_path p \<Longrightarrow> valid_path (pr \<epsilon>)"
                 "\<And>\<epsilon>. \<epsilon> > 0 \<Longrightarrow> \<epsilon> < eps \<Longrightarrow> valid_path p \<Longrightarrow> valid_path (p1 \<epsilon>)"
                 "\<And>\<epsilon>. \<epsilon> > 0 \<Longrightarrow> \<epsilon> < eps \<Longrightarrow> valid_path p \<Longrightarrow> valid_path (p2 \<epsilon>)"
  assumes "eps > 0" and closed: "closed L" "closed R"
  shows   "detour_rel L R p (\<lambda>\<epsilon>. p1 \<epsilon> +++ pl \<epsilon> +++ p2 \<epsilon>) (\<lambda>\<epsilon>. p1 \<epsilon> +++ pr \<epsilon> +++ p2 \<epsilon>)"
proof (rule detour_relI[OF \<open>eps > 0\<close>])
  fix \<epsilon> assume \<epsilon>: "\<epsilon> > 0" "\<epsilon> < eps"
  assume simple_p: "simple_path p"
  hence [simp]: "path p"
    by (auto dest: simple_path_imp_path)
  assume valid_p: "valid_path p"
  note LR' = LR[OF \<epsilon>]
  note simple' = simple[OF \<epsilon>]
  note homo' = homo[OF \<epsilon>]
  note valid = valid[OF \<epsilon> valid_p]
  note [simp] = ends[OF \<epsilon>]
  have [simp]: "path (pl \<epsilon>)" "path (pr \<epsilon>)" "path (p1 \<epsilon>)" "path (p2 \<epsilon>)"
    using simple' simple_path_imp_path simple_p by force+

  show pl: "detour_rel_aux_locale \<epsilon> (L \<union> R) p (p1 \<epsilon> +++ pl \<epsilon> +++ p2 \<epsilon>)"
    by unfold_locales (use \<open>\<epsilon> > 0\<close> simple' simple_p valid LR_subset homo' LR' in \<open>auto simp: S_def path_image_join\<close>)
  show pr: "detour_rel_aux_locale \<epsilon> (L \<union> R) p (p1 \<epsilon> +++ pr \<epsilon> +++ p2 \<epsilon>)"
    by unfold_locales (use \<open>\<epsilon> > 0\<close> simple' simple_p valid LR_subset homo' LR' in \<open>auto simp: S_def path_image_join\<close>)

  write winding_number ("ind")
  have ind_eq: "(x \<in> L \<longrightarrow> ind (pl \<epsilon>) x - ind (pr \<epsilon>) x = -1) \<and>
                (x \<in> R \<longrightarrow> ind (pl \<epsilon>) x - ind (pr \<epsilon>) x = 1)" if "x \<in> L \<union> R" for x
  proof -
    have "ind (pl \<epsilon> +++ reversepath (pr \<epsilon>)) x = ind (pl \<epsilon>) x + ind (reversepath (pr \<epsilon>)) x"
      using that LR' simple_p by (subst winding_number_join) auto
    also have "ind (reversepath (pr \<epsilon>)) x = -ind (pr \<epsilon>) x"
      using that LR' simple_p by (subst winding_number_reversepath) auto
    finally show ?thesis
      using ind[OF \<epsilon>, of x] that simple_p by auto
  qed

  show "ind (p1 \<epsilon> +++ pl \<epsilon> +++ p2 \<epsilon>) x - ind (p1 \<epsilon> +++ pr \<epsilon> +++ p2 \<epsilon>) x = -1" if "x \<in> L" for x
    using that LR' ind_eq[of x] simple_p
    by (subst winding_number_join winding_number_reversepath; auto simp: path_image_join)+
  show "ind (p1 \<epsilon> +++ pl \<epsilon> +++ p2 \<epsilon>) x - ind (p1 \<epsilon> +++ pr \<epsilon> +++ p2 \<epsilon>) x = 1" if "x \<in> R" for x
    using that LR' ind_eq[of x] simple_p
    by (subst winding_number_join winding_number_reversepath; auto simp: path_image_join)+        
qed fact+

text \<open>
  This is the main rule for proving the common avoidance pattern where we avoid a single
  bad point \<open>bad\<close> on a curve by replacing some segment of it with a circular arc with
  radius \<open>\<epsilon>\<close> around \<open>bad\<close>. We only need to show that the original path \<open>p\<close> splits into
  segments \<open>p\<^sub>1\<close>, \<open>p\<^sub>2\<close>, and \<open>p\<^sub>3\<close> such that \<open>p\<^sub>1\<close> and \<open>p\<^sub>2\<close> do not overlap and none of
  the segments crosses the \<open>\<epsilon>\<close>-sphere around \<open>bad\<close>.
\<close>
lemma detour_rel_avoid_basic_part_circlepath_left:
  fixes p :: "real \<Rightarrow> complex" and bad :: complex and a b a' b' :: "real \<Rightarrow> real"
  defines "S  \<equiv> (\<lambda>\<epsilon>. path_image p \<union> cball bad \<epsilon>)"
  defines "cl \<equiv> (\<lambda>\<epsilon>. part_circlepath bad \<epsilon> (a' \<epsilon>) (b' \<epsilon>))"
  defines "cr \<equiv> (\<lambda>\<epsilon>. part_circlepath bad \<epsilon> (a \<epsilon>) (b \<epsilon>))"
  assumes "bad \<in> path_image p - {pathstart p, pathfinish p}"
  assumes eq_paths: "\<And>\<epsilon>. \<epsilon> > 0 \<Longrightarrow> \<epsilon> < eps \<Longrightarrow> simple_path p \<Longrightarrow> eq_paths p (p1 \<epsilon> +++ pm \<epsilon> +++ p2 \<epsilon>)"
  assumes p12_disjoint:
     "\<And>\<epsilon>. \<epsilon> > 0 \<Longrightarrow> \<epsilon> < eps \<Longrightarrow> simple_path p \<Longrightarrow>
             path_image (p1 \<epsilon>) \<inter> path_image (p2 \<epsilon>) \<subseteq> {pathstart p} \<inter> {pathfinish p}"
  assumes p1_dnc: "\<And>\<epsilon>. \<epsilon> > 0 \<Longrightarrow> \<epsilon> < eps \<Longrightarrow> simple_path p \<Longrightarrow> does_not_cross (p1 \<epsilon>) (sphere bad \<epsilon>)"
  assumes p2_dnc: "\<And>\<epsilon>. \<epsilon> > 0 \<Longrightarrow> \<epsilon> < eps \<Longrightarrow> simple_path p \<Longrightarrow> does_not_cross (p2 \<epsilon>) (sphere bad \<epsilon>)"
  assumes pm_dnc: "\<And>\<epsilon>. \<epsilon> > 0 \<Longrightarrow> \<epsilon> < eps \<Longrightarrow> simple_path p \<Longrightarrow> does_not_cross (pm \<epsilon>) (sphere bad \<epsilon>)"
  assumes finish_p1: "\<And>\<epsilon>. \<epsilon> > 0 \<Longrightarrow> \<epsilon> < eps \<Longrightarrow> simple_path p \<Longrightarrow> pathfinish (p1 \<epsilon>) = bad + rcis \<epsilon> (a \<epsilon>)"
  assumes start_p2:  "\<And>\<epsilon>. \<epsilon> > 0 \<Longrightarrow> \<epsilon> < eps \<Longrightarrow> simple_path p \<Longrightarrow> pathstart  (p2 \<epsilon>) = bad + rcis \<epsilon> (b \<epsilon>)"
  assumes valid:     "\<And>\<epsilon>. \<epsilon> > 0 \<Longrightarrow> \<epsilon> < eps \<Longrightarrow> valid_path p \<Longrightarrow> valid_path (p1 \<epsilon>)"
                     "\<And>\<epsilon>. \<epsilon> > 0 \<Longrightarrow> \<epsilon> < eps \<Longrightarrow> valid_path p \<Longrightarrow> valid_path (p2 \<epsilon>)"
  assumes pm_ends:   "\<And>\<epsilon>. \<epsilon> > 0 \<Longrightarrow> \<epsilon> < eps \<Longrightarrow> simple_path p \<Longrightarrow> pathstart  (pm \<epsilon>) = pathfinish (p1 \<epsilon>)"
                     "\<And>\<epsilon>. \<epsilon> > 0 \<Longrightarrow> \<epsilon> < eps \<Longrightarrow> simple_path p \<Longrightarrow> pathfinish (pm \<epsilon>) = pathstart (p2 \<epsilon>)"
  assumes ab:  "\<And>\<epsilon>. \<epsilon> > 0 \<Longrightarrow> \<epsilon> < eps \<Longrightarrow> simple_path p \<Longrightarrow> a \<epsilon> \<noteq> b \<epsilon>   \<and> \<bar>b \<epsilon> - a \<epsilon>\<bar>   < 2 * pi"
  assumes ab': "\<And>\<epsilon>. \<epsilon> > 0 \<Longrightarrow> \<epsilon> < eps \<Longrightarrow> simple_path p \<Longrightarrow> a' \<epsilon> \<noteq> b' \<epsilon> \<and> \<bar>b' \<epsilon> - a' \<epsilon>\<bar> < 2 * pi \<and>
                 cis (a' \<epsilon>) = cis (a \<epsilon>) \<and> cis (b' \<epsilon>) = cis (b \<epsilon>) \<and>
                 b \<epsilon> - a \<epsilon> + a' \<epsilon> - b' \<epsilon> = 2 * pi"
  assumes "eps > 0"
  shows   "detour_rel {bad} {} p (\<lambda>\<epsilon>. p1 \<epsilon> +++ cl \<epsilon> +++ p2 \<epsilon>) (\<lambda>\<epsilon>. p1 \<epsilon> +++ cr \<epsilon> +++ p2 \<epsilon>)"
proof (rule detour_rel_avoid_basic[of "Min {eps, dist bad (pathstart p), dist bad (pathfinish p)}"])
  show "Min {eps, dist bad (pathstart p), dist bad (pathfinish p)} > 0"
    using \<open>eps > 0\<close> \<open>bad \<in> _\<close> by auto
  show "closed {bad}" "closed ({} :: complex set)"
    by auto
  show "{bad} \<union> {} \<subseteq> path_image p"
    using \<open>bad \<in> _\<close> by auto
next
  fix \<epsilon> :: real
  assume "\<epsilon> > 0" "\<epsilon> < Min {eps, dist bad (pathstart p), dist bad (pathfinish p)}"
  hence \<epsilon>: "\<epsilon> > 0" "\<epsilon> < eps" and \<epsilon>': "\<epsilon> < dist bad (pathstart p)" "\<epsilon> < dist bad (pathfinish p)"
    by auto
  show "valid_path (p1 \<epsilon>)" "valid_path (p2 \<epsilon>)" if "valid_path p"
    using valid that \<epsilon> by auto
  note [simp] = pathstart_part_circlepath' pathfinish_part_circlepath'

  assume simple_p: "simple_path p"
  note eq_paths = eq_paths[OF \<epsilon> simple_p]

  have [simp]: "pathstart (p1 \<epsilon>) = pathstart p" "pathfinish (p2 \<epsilon>) = pathfinish p"
    using eq_paths_imp_same_ends[OF eq_paths] by simp_all
  note [simp] = pm_ends[OF \<epsilon> simple_p] finish_p1[OF \<epsilon> simple_p] start_p2[OF \<epsilon> simple_p]

  have *: "simple_path (p1 \<epsilon> +++ pm \<epsilon> +++ p2 \<epsilon>)"
    using simple_p eq_paths eq_paths_imp_simple_path_iff by blast
  hence **: "arc (p1 \<epsilon>) \<and> arc (pm \<epsilon>) \<and> arc (p2 \<epsilon>)"
    by (elim simple_path_joinE arc_join; auto simp: arc_join_eq)
  have "path (p1 \<epsilon> +++ pm \<epsilon> +++ p2 \<epsilon>)"
    using eq_paths by (simp add: eq_paths_imp_path)
  hence [simp]: "path (pm \<epsilon>)" "path (p1 \<epsilon>)" "path (p2 \<epsilon>)"
    using pm_ends[OF \<epsilon>] by (auto simp: arc_imp_path)

  note ab = ab[OF \<epsilon> simple_p]
  note ab' = ab'[OF \<epsilon> simple_p]

  show "pathfinish (cl \<epsilon>) = pathstart (p2 \<epsilon>)" "pathfinish (cr \<epsilon>) = pathstart (p2 \<epsilon>)"
       "pathstart (cl \<epsilon>) = pathfinish (p1 \<epsilon>)" "pathstart (cr \<epsilon>) = pathfinish (p1 \<epsilon>)"
    using ab' by (auto simp: cl_def cr_def rcis_def pathfinish_part_circlepath'
                             pathstart_part_circlepath' exp_eq_polar)

  show "path_image (cl \<epsilon>) \<inter> ({bad} \<union> {}) = {}" "path_image (cr \<epsilon>) \<inter> ({bad} \<union> {}) = {}"
    using \<epsilon> by (auto simp: cl_def cr_def path_image_def part_circlepath_def)

  have p1_cball: "path_image (p1 \<epsilon>) \<inter> ball bad \<epsilon> = {}"
  proof -
    have "path_image (p1 \<epsilon>) \<subseteq> cball bad \<epsilon> \<or> path_image (p1 \<epsilon>) \<inter> ball bad \<epsilon> = {}"
      using path_fully_inside_or_fully_outside'[of "p1 \<epsilon>" "cball bad \<epsilon>"] p1_dnc[OF \<epsilon> simple_p]
      by simp
    moreover have "pathstart (p1 \<epsilon>) \<in> path_image (p1 \<epsilon>)" "pathstart (p1 \<epsilon>) \<notin> cball bad \<epsilon>"
      by (intro pathstart_in_path_image) (use \<epsilon>' in auto)
    ultimately show "path_image (p1 \<epsilon>) \<inter> ball bad \<epsilon> = {}"
      by auto
  qed

  have p1_dnc': "path_image (p1 \<epsilon>) \<inter> cball bad \<epsilon> \<subseteq> {pathfinish (p1 \<epsilon>)}"
  proof
    fix x assume x: "x \<in> path_image (p1 \<epsilon>) \<inter> cball bad \<epsilon>"
    then obtain t where t: "t \<in> {0..1}" "p1 \<epsilon> t = x"
      by (auto simp: path_image_def)
    from x p1_cball have "x \<in> sphere bad \<epsilon>"
      by auto
    with t and p1_dnc[OF \<epsilon> simple_p] have "t \<in> {0, 1}"
      by (auto simp: does_not_cross_def)
    moreover have "pathstart (p1 \<epsilon>) \<notin> cball bad \<epsilon>"
      using \<epsilon>' by auto
    ultimately have "t = 1"
      using t x by (auto simp: pathstart_def)
    thus "x \<in> {pathfinish (p1 \<epsilon>)}"
      using t x by (auto simp: pathfinish_def)
  qed

  have p2_cball: "path_image (p2 \<epsilon>) \<inter> ball bad \<epsilon> = {}"
  proof -
    have "path_image (p2 \<epsilon>) \<subseteq> cball bad \<epsilon> \<or> path_image (p2 \<epsilon>) \<inter> ball bad \<epsilon> = {}"
      using path_fully_inside_or_fully_outside'[of "p2 \<epsilon>" "cball bad \<epsilon>"] p2_dnc[OF \<epsilon> simple_p]
      by simp
    moreover have "pathfinish (p2 \<epsilon>) \<in> path_image (p2 \<epsilon>)" "pathfinish (p2 \<epsilon>) \<notin> cball bad \<epsilon>"
      by (intro pathfinish_in_path_image) (use \<epsilon>' in auto)
    ultimately show "path_image (p2 \<epsilon>) \<inter> ball bad \<epsilon> = {}"
      by auto
  qed

  have p2_dnc': "path_image (p2 \<epsilon>) \<inter> cball bad \<epsilon> \<subseteq> {pathstart (p2 \<epsilon>)}"
  proof
    fix x assume x: "x \<in> path_image (p2 \<epsilon>) \<inter> cball bad \<epsilon>"
    then obtain t where t: "t \<in> {0..1}" "p2 \<epsilon> t = x"
      by (auto simp: path_image_def)
    from x p2_cball have "x \<in> sphere bad \<epsilon>"
      by auto
    with t and p2_dnc[OF \<epsilon> simple_p] have "t \<in> {0, 1}"
      by (auto simp: does_not_cross_def)
    moreover have "pathfinish (p2 \<epsilon>) \<notin> cball bad \<epsilon>"
      using \<epsilon>' by auto
    ultimately have "t = 0"
      using t x by (auto simp: pathfinish_def)
    thus "x \<in> {pathstart (p2 \<epsilon>)}"
      using t x by (auto simp: pathstart_def)
  qed

  have "bad \<in> path_image p"
    using \<open>bad \<in> _\<close> by blast
  also have "path_image p = path_image (p1 \<epsilon> +++ pm \<epsilon> +++ p2 \<epsilon>)"
    using eq_paths by (rule eq_paths_imp_path_image_eq)
  also have "\<dots> = path_image (p1 \<epsilon>) \<union> path_image (pm \<epsilon>) \<union> path_image (p2 \<epsilon>)"
    by (simp add: path_image_join Un_assoc)
  also have "\<dots> \<subseteq> -ball bad \<epsilon> \<union> path_image (pm \<epsilon>) \<union> -ball bad \<epsilon>"
    by (intro Un_mono) (use p1_cball p2_cball in auto)
  finally have "bad \<in> path_image (pm \<epsilon>)"
    using \<epsilon> by auto  

  have pm_cball: "path_image (pm \<epsilon>) \<subseteq> cball bad \<epsilon>"
  proof -
    have "path_image (pm \<epsilon>) \<subseteq> cball bad \<epsilon> \<or> path_image (pm \<epsilon>) \<inter> ball bad \<epsilon> = {}"
      using path_fully_inside_or_fully_outside'[of "pm \<epsilon>" "cball bad \<epsilon>"] pm_dnc[OF \<epsilon> simple_p]
      by simp
    moreover have "bad \<in> ball bad \<epsilon>"
      using \<epsilon> by auto
    ultimately show "path_image (pm \<epsilon>) \<subseteq> cball bad \<epsilon>"
      using \<open>bad \<in> path_image (pm \<epsilon>)\<close> by blast
  qed

  show "path_image (p1 \<epsilon>) \<inter> ({bad} \<union> {}) = {}"
  proof -
    have "bad \<in> ball bad \<epsilon>"
      using \<epsilon> by auto
    moreover have "pathfinish (p1 \<epsilon>) \<in> sphere bad \<epsilon>"
      using \<epsilon> by (auto simp: dist_norm)
    hence "path_image (p1 \<epsilon>) \<inter> ball bad \<epsilon> = {}"
      using p1_cball by force
    ultimately show ?thesis
      by auto
  qed

  show "path_image (p2 \<epsilon>) \<inter> ({bad} \<union> {}) = {}"
  proof -
    have "bad \<in> ball bad \<epsilon>"
      using \<epsilon> by auto
    moreover have "pathstart (p2 \<epsilon>) \<in> sphere bad \<epsilon>"
      using \<epsilon> by (auto simp: dist_norm)
    hence "path_image (p2 \<epsilon>) \<inter> ball bad \<epsilon> = {}"
      using p2_cball by force
    ultimately show ?thesis
      by auto
  qed

  have simple_circ: "simple_path (p1 \<epsilon> +++ part_circlepath bad \<epsilon> a'' b'' +++ p2 \<epsilon>)"
    if "a'' \<noteq> b''" "\<bar>b'' - a''\<bar> < 2 * pi" "pathfinish (p1 \<epsilon>) = bad + rcis \<epsilon> a''"
       "pathstart (p2 \<epsilon>) = bad + rcis \<epsilon> b''" for a'' b''
  proof (intro simple_path_join3I)
    show "arc (p1 \<epsilon>)" "arc (p2 \<epsilon>)"
      using ** by simp_all
    show "arc (part_circlepath bad \<epsilon> a'' b'')"
      using that \<epsilon> by (auto intro!: arc_part_circlepath)
    show "path_image (p1 \<epsilon>) \<inter> path_image (p2 \<epsilon>) \<subseteq> {pathstart (p1 \<epsilon>)} \<inter> {pathfinish (p2 \<epsilon>)}"
      using p12_disjoint[OF \<epsilon> simple_p] by simp
    show "pathfinish (p1 \<epsilon>) = pathstart (part_circlepath bad \<epsilon> a'' b'')"
         "pathfinish (part_circlepath bad \<epsilon> a'' b'') = pathstart (p2 \<epsilon>)"
      using that by (auto simp: rcis_def exp_eq_polar)
    show "path_image (p1 \<epsilon>) \<inter> path_image (part_circlepath bad \<epsilon> a'' b'') \<subseteq>
            {pathstart (part_circlepath bad \<epsilon> a'' b'')}"
      using path_image_part_circlepath_subset'[of \<epsilon> bad a'' b''] p1_dnc' \<epsilon> that 
      by (force simp: does_not_cross_def rcis_def exp_eq_polar)
    show "path_image (part_circlepath bad \<epsilon> a'' b'') \<inter> path_image (p2 \<epsilon>) \<subseteq> {pathstart (p2 \<epsilon>)}"
      using path_image_part_circlepath_subset'[of \<epsilon> bad a'' b''] p2_dnc' \<epsilon> that 
      by (force simp: does_not_cross_def)
  qed

  show "simple_path (p1 \<epsilon> +++ cl \<epsilon> +++ p2 \<epsilon>)" "simple_path (p1 \<epsilon> +++ cr \<epsilon> +++ p2 \<epsilon>)"
    unfolding cl_def cr_def
    by (rule simple_circ; use ab finish_p1[OF \<epsilon>] start_p2[OF \<epsilon>] ab ab' in \<open>simp add: rcis_def\<close>)+

  have homo_circ: "homotopic_paths (S \<epsilon>) p (p1 \<epsilon> +++ part_circlepath bad \<epsilon> a'' b'' +++ p2 \<epsilon>)"
    if "cis a'' = cis (a \<epsilon>)" "cis b'' = cis (b \<epsilon>)" for a'' b''
  proof -
    have "homotopic_paths (S \<epsilon>) p (p1 \<epsilon> +++ pm \<epsilon> +++ p2 \<epsilon>)"
      by (intro eq_paths_imp_homotopic[OF eq_paths]) (auto simp: S_def)
    also have "homotopic_paths (S \<epsilon>) (pm \<epsilon>) (part_circlepath bad \<epsilon> a'' b'')"
    proof (rule homotopic_paths_subset[OF simply_connected_imp_homotopic_paths])
      show "simply_connected (cball bad \<epsilon>)"
        by (rule convex_imp_simply_connected) auto
    next
      have "path_image (part_circlepath bad \<epsilon> a'' b'') \<subseteq> sphere bad \<epsilon>"
        using \<epsilon> by (intro path_image_part_circlepath_subset') auto
      also have "\<dots> \<subseteq> cball bad \<epsilon>"
        by auto
      finally show "path_image (part_circlepath bad \<epsilon> a'' b'') \<subseteq> cball bad \<epsilon>" .
    next
      show "same_ends (part_circlepath bad \<epsilon> a'' b'') (pm \<epsilon>)"
        using that by (auto simp: rcis_def rcis_def exp_eq_polar)
    next
      show "path_image (pm \<epsilon>) \<subseteq> cball bad \<epsilon>"
        by fact
    qed (auto simp: S_def)
    hence "homotopic_paths (S \<epsilon>) (p1 \<epsilon> +++ pm \<epsilon> +++ p2 \<epsilon>)
             (p1 \<epsilon> +++ part_circlepath bad \<epsilon> a'' b'' +++ p2 \<epsilon>)"
      using \<open>path_image p = _\<close>
      by (intro homotopic_paths_join) (auto simp: S_def path_image_join)
    finally show ?thesis .
  qed

  have "homotopic_paths (S \<epsilon>) p (p1 \<epsilon> +++ cl \<epsilon> +++ p2 \<epsilon>)"
       "homotopic_paths (S \<epsilon>) p (p1 \<epsilon> +++ cr \<epsilon> +++ p2 \<epsilon>)"
    unfolding cl_def cr_def by (rule homo_circ; use ab' in simp)+
  thus "homotopic_paths (path_image p \<union> (\<Union>y\<in>{bad} \<union> {}. cball y \<epsilon>)) p (p1 \<epsilon> +++ cl \<epsilon> +++ p2 \<epsilon>)"
       "homotopic_paths (path_image p \<union> (\<Union>y\<in>{bad} \<union> {}. cball y \<epsilon>)) p (p1 \<epsilon> +++ cr \<epsilon> +++ p2 \<epsilon>)"
    by (simp_all add: S_def)

  show "winding_number (cl \<epsilon> +++ reversepath (cr \<epsilon>)) x = -1" if "x \<in> {bad}" for x
  proof -
    let ?\<gamma> = "part_circlepath bad \<epsilon>"
    have "cl \<epsilon> +++ reversepath (cr \<epsilon>) = ?\<gamma> (a' \<epsilon>) (b' \<epsilon>) +++ ?\<gamma> (b \<epsilon>) (a \<epsilon>)"
      by (simp add: cl_def cr_def)
    also have "?\<gamma> (a' \<epsilon>) (b' \<epsilon>) = ?\<gamma> (a \<epsilon> + 2 * pi) (b \<epsilon>)"
      using ab' by (intro part_circlepath_cong) (auto simp flip: cis_mult)
    also have "\<dots> +++ ?\<gamma> (b \<epsilon>) (a \<epsilon>) \<equiv>\<^sub>p ?\<gamma> (a \<epsilon> + 2 * pi) (a \<epsilon>)"
      by (intro eq_paths_part_circlepaths) (use ab ab' in \<open>auto simp: closed_segment_eq_real_ivl\<close>)
    also have "\<dots> = reversepath (?\<gamma> (a \<epsilon>) (a \<epsilon> + 2 * pi))"
      by simp
    also have "\<dots> \<equiv>\<^sub>\<circle> reversepath (circlepath bad \<epsilon>)"
      by (intro eqloops_reversepath_cong eq_loops_full_part_circlepath) auto
    also have "winding_number \<dots> bad = -1"
      using \<epsilon> by (simp add: winding_number_reversepath winding_number_circlepath)
    finally show ?thesis
      using \<epsilon> that by auto
  qed
qed (auto simp: cl_def cr_def)

lemma detour_rel_avoid_basic_part_circlepath_right:
  fixes p :: "real \<Rightarrow> complex" and bad :: complex and a b a' b' :: "real \<Rightarrow> real"
  defines "S \<equiv> (\<lambda>\<epsilon>. path_image p \<union> cball bad \<epsilon>)"
  defines "cl \<equiv> (\<lambda>\<epsilon>. part_circlepath bad \<epsilon> (a' \<epsilon>) (b' \<epsilon>))"
  defines "cr \<equiv> (\<lambda>\<epsilon>. part_circlepath bad \<epsilon> (a \<epsilon>) (b \<epsilon>))"
  assumes "bad \<in> path_image p - {pathstart p, pathfinish p}"
  assumes eq_paths:     "\<And>\<epsilon>. \<epsilon> > 0 \<Longrightarrow> \<epsilon> < eps \<Longrightarrow> simple_path p \<Longrightarrow> eq_paths p (p1 \<epsilon> +++ pm \<epsilon> +++ p2 \<epsilon>)"
  assumes p12_disjoint: "\<And>\<epsilon>. \<epsilon> > 0 \<Longrightarrow> \<epsilon> < eps \<Longrightarrow> simple_path p \<Longrightarrow> path_image (p1 \<epsilon>) \<inter> path_image (p2 \<epsilon>) \<subseteq> {pathstart p} \<inter> {pathfinish p}"
  assumes p1_dnc: "\<And>\<epsilon>. \<epsilon> > 0 \<Longrightarrow> \<epsilon> < eps \<Longrightarrow> simple_path p \<Longrightarrow> does_not_cross (p1 \<epsilon>) (sphere bad \<epsilon>)"
  assumes p2_dnc: "\<And>\<epsilon>. \<epsilon> > 0 \<Longrightarrow> \<epsilon> < eps \<Longrightarrow> simple_path p \<Longrightarrow> does_not_cross (p2 \<epsilon>) (sphere bad \<epsilon>)"
  assumes pm_dnc: "\<And>\<epsilon>. \<epsilon> > 0 \<Longrightarrow> \<epsilon> < eps \<Longrightarrow> simple_path p \<Longrightarrow> does_not_cross (pm \<epsilon>) (sphere bad \<epsilon>)"
  assumes finish_p1: "\<And>\<epsilon>. \<epsilon> > 0 \<Longrightarrow> \<epsilon> < eps \<Longrightarrow> simple_path p \<Longrightarrow> pathfinish (p1 \<epsilon>) = bad + rcis \<epsilon> (a \<epsilon>)"
  assumes start_p2:  "\<And>\<epsilon>. \<epsilon> > 0 \<Longrightarrow> \<epsilon> < eps \<Longrightarrow> simple_path p \<Longrightarrow> pathstart (p2 \<epsilon>) = bad + rcis \<epsilon> (b \<epsilon>)"
  assumes pm_ends:   "\<And>\<epsilon>. \<epsilon> > 0 \<Longrightarrow> \<epsilon> < eps \<Longrightarrow> simple_path p \<Longrightarrow> pathstart (pm \<epsilon>) = pathfinish (p1 \<epsilon>)"
                     "\<And>\<epsilon>. \<epsilon> > 0 \<Longrightarrow> \<epsilon> < eps \<Longrightarrow> simple_path p \<Longrightarrow> pathfinish (pm \<epsilon>) = pathstart (p2 \<epsilon>)"
  assumes valid:     "\<And>\<epsilon>. \<epsilon> > 0 \<Longrightarrow> \<epsilon> < eps \<Longrightarrow> valid_path p \<Longrightarrow> valid_path (p1 \<epsilon>)"
                     "\<And>\<epsilon>. \<epsilon> > 0 \<Longrightarrow> \<epsilon> < eps \<Longrightarrow> valid_path p \<Longrightarrow> valid_path (p2 \<epsilon>)"
  assumes ab:  "\<And>\<epsilon>. \<epsilon> > 0 \<Longrightarrow> \<epsilon> < eps \<Longrightarrow> simple_path p \<Longrightarrow> a \<epsilon> \<noteq> b \<epsilon> \<and> \<bar>b \<epsilon> - a \<epsilon>\<bar> < 2 * pi"
  assumes ab': "\<And>\<epsilon>. \<epsilon> > 0 \<Longrightarrow> \<epsilon> < eps \<Longrightarrow> simple_path p \<Longrightarrow> a' \<epsilon> \<noteq> b' \<epsilon> \<and> \<bar>b' \<epsilon> - a' \<epsilon>\<bar> < 2 * pi \<and>
                 cis (a' \<epsilon>) = cis (a \<epsilon>) \<and> cis (b' \<epsilon>) = cis (b \<epsilon>) \<and>
                 b \<epsilon> - a \<epsilon> + a' \<epsilon> - b' \<epsilon> = 2 * pi"
  assumes "eps > 0"
  shows   "detour_rel {} {bad} p (\<lambda>\<epsilon>. p1 \<epsilon> +++ cr \<epsilon> +++ p2 \<epsilon>) (\<lambda>\<epsilon>. p1 \<epsilon> +++ cl \<epsilon> +++ p2 \<epsilon>)"
  using detour_rel_avoid_basic_part_circlepath_left[of bad p eps p1 pm p2 a b a' b'] assms
  by (simp add: detour_rel_swap)
 


subsubsection \<open>Straight line\<close>

definition avoid_linepath where
  "avoid_linepath left a b bad \<epsilon> =
     linepath a (bad - (\<epsilon> / dist a b) *\<^sub>R (b - a)) +++
     part_circlepath bad \<epsilon> (Arg (b - a) + (if left then pi else -pi)) (Arg (b - a)) +++
     linepath (bad + (\<epsilon> / dist a b) *\<^sub>R (b - a)) b"

lemma valid_path_avoid_linepath:
  assumes "a \<noteq> b"
  shows   "valid_path (avoid_linepath left a b bad \<epsilon>)"
  unfolding avoid_linepath_def using assms
  by (intro valid_path_join valid_path_linepath valid_path_part_circlepath)
     (auto simp: scaleR_conv_of_real rcis_def cis_Arg complex_sgn_def dist_norm norm_minus_commute
                 field_simps rcis_def exp_eq_polar simp flip: cis_divide cis_mult)

lemma avoid_linepath_translate:
  "(+) c \<circ> avoid_linepath left a b bad \<epsilon> =
   avoid_linepath left (c + a) (c + b) (c + bad) \<epsilon>"
  unfolding avoid_linepath_def path_compose_join linepath_translate 
            part_circlepath_translate by (simp add: algebra_simps)

lemma avoid_linepath_mult:
  assumes "a \<noteq> b"
  shows   "(*) c \<circ> avoid_linepath left a b 0 \<epsilon> =
           avoid_linepath left (c * a) (c * b) 0 (norm c * \<epsilon>)"
proof (cases "c = 0")
  assume "c = 0"
  thus ?thesis
    by (auto simp: avoid_linepath_def joinpaths_def
                   fun_eq_iff part_circlepath_def linepath_def)
next
  assume [simp]: "c \<noteq> 0"
  define \<beta> where "\<beta> = (if left then pi else -pi)"
  have *: "part_circlepath 0 (\<epsilon> * cmod c) (\<beta> + Arg (b * c - a * c)) (Arg (b * c - a * c)) =
           part_circlepath 0 (\<epsilon> * cmod c) (\<beta> + (Arg c + Arg (b - a))) (Arg c + Arg (b - a))"
    by (rule part_circlepath_cong)
       (use assms in \<open>simp_all flip: cis_mult cis_divide sgn_mult
                               add: cis_Arg ring_distribs mult_ac\<close>)
  show ?thesis
  unfolding avoid_linepath_def path_compose_join linepath_mult_complex 
            part_circlepath_mult_complex \<beta>_def [symmetric] dist_mult_left
  using assms * by (simp add: algebra_simps)
qed

lemma detour_rel_linepath_semicircle_left_aux1:
  assumes "a < 0" "b > 0"
  shows "detour_rel {0} {} (linepath (complex_of_real a) (complex_of_real b))
           (avoid_linepath True  (complex_of_real a) (complex_of_real b) 0)
           (avoid_linepath False (complex_of_real a) (complex_of_real b) 0)"
proof -
  define p where "p \<equiv> linepath (of_real a) (of_real b :: complex)"
  define p1 where "p1 \<equiv> (\<lambda>\<epsilon>. linepath (of_real a) (-of_real \<epsilon> :: complex))"
  define p2 where "p2 \<equiv> (\<lambda>\<epsilon>. linepath (of_real \<epsilon> :: complex) (of_real b))"
  define pm where "pm \<equiv> (\<lambda>\<epsilon>. linepath (-of_real \<epsilon>) (of_real \<epsilon> :: complex))"
  define cl where "cl \<equiv> (\<lambda>\<epsilon>. part_circlepath 0 \<epsilon> pi 0)"
  define cr where "cr \<equiv> (\<lambda>\<epsilon>. part_circlepath 0 \<epsilon> (-pi) 0)"
  note [simp] = closed_segment_eq_real_ivl1 closed_segment_same_Im
  note homoI = homotopic_paths_subset[OF simply_connected_imp_homotopic_paths]

  note [[goals_limit = 30]]
  have "detour_rel {0} {} p (\<lambda>\<epsilon>. p1 \<epsilon> +++ cl \<epsilon> +++ p2 \<epsilon>) (\<lambda>\<epsilon>. p1 \<epsilon> +++ cr \<epsilon> +++ p2 \<epsilon>)"
    unfolding cl_def cr_def
  proof (rule detour_rel_avoid_basic_part_circlepath_left [where eps = "min (-a) b"])
    show "0 \<in> path_image p - {pathstart p, pathfinish p}"
      using assms by (auto simp: p_def)
  next
    fix \<epsilon> assume \<epsilon>: "\<epsilon> > 0" "\<epsilon> < min (-a) b"
    define S where
      "S \<equiv> path_image (linepath (complex_of_real a) (of_real b)) \<union> (\<Union>y\<in>{0} \<union> {}. cball y \<epsilon>)"

    show "eq_paths p (p1 \<epsilon> +++ pm \<epsilon> +++ p2 \<epsilon>)"
      unfolding p1_def pm_def p2_def p_def using \<epsilon>
      by (auto intro!: eq_paths_joinpaths_linepath')

    show "path_image (p1 \<epsilon>) \<inter> path_image (p2 \<epsilon>) \<subseteq> {pathstart p} \<inter> {pathfinish p}"
      using assms \<epsilon> by (auto simp: p1_def p2_def)

    have *: "path_image (p1 \<epsilon>) \<inter> sphere 0 \<epsilon> \<subseteq> {pathfinish (p1 \<epsilon>)}"
            "path_image (p2 \<epsilon>) \<inter> sphere 0 \<epsilon> \<subseteq> {pathstart (p2 \<epsilon>)}" using \<epsilon>
      by (auto simp: p1_def p2_def complex_eq_iff simp flip: complex_is_Real_iff elim!: Reals_cases)
    show "does_not_cross (p1 \<epsilon>) (sphere 0 \<epsilon>)" "does_not_cross (p2 \<epsilon>) (sphere 0 \<epsilon>)"
      by (subst does_not_cross_simple_path; use \<epsilon> * in \<open>force simp: p1_def p2_def\<close>)+
    have "path_image (pm \<epsilon>) \<subseteq> cball 0 \<epsilon>"
      unfolding pm_def path_image_linepath using \<epsilon> by (intro closed_segment_subset) auto
    thus "does_not_cross (pm \<epsilon>) (sphere 0 \<epsilon>)"
    proof (subst does_not_cross_simple_path)
      show "path_image (pm \<epsilon>) \<inter> sphere 0 \<epsilon> \<subseteq> {pathstart (pm \<epsilon>), pathfinish (pm \<epsilon>)}"
      proof
        fix z assume z: "z \<in> path_image (pm \<epsilon>) \<inter> sphere 0 \<epsilon>"
        then obtain x where x: "x \<in> {-\<epsilon>..\<epsilon>}" "z = of_real x"
          using \<epsilon> by (auto simp: pm_def complex_eq_iff)
        with z have "x \<in> {-\<epsilon>, \<epsilon>}"
          by auto
        thus "z \<in> {pathstart (pm \<epsilon>), pathfinish (pm \<epsilon>)}"
          using x by (auto simp: pm_def)
      qed
    qed (use \<epsilon> in \<open>auto simp: pm_def\<close>)
  qed (use assms in \<open>auto simp: p1_def rcis_def p2_def pm_def split: if_splits\<close>)

  thus ?thesis using assms
    by (auto simp: p_def p1_def cl_def cr_def p2_def avoid_linepath_def [abs_def]
                   scaleR_conv_of_real dist_real_def simp flip: of_real_diff)
qed

lemma detour_rel_linepath_semicircle_left_aux2:
  assumes "0 \<in> open_segment a b"
  shows "detour_rel {0} {} (linepath a b)
           (avoid_linepath True  a b 0)
           (avoid_linepath False a b 0)"
proof -
  define \<alpha> where "\<alpha> = sgn (b - a)"
  have [simp]: "\<alpha> \<noteq> 0" "a \<noteq> 0" "b \<noteq> 0"
    using assms by (auto simp: open_segment_def \<alpha>_def sgn_eq_0_iff)
  define a' b' where "a' = complex_of_real (-norm a)" and "b' = complex_of_real (norm b)"
  let ?\<gamma> = "\<lambda>left a b. avoid_linepath left a b 0"

  obtain u where u: "u \<in> {0<..<1}" "(1 - u) *\<^sub>R a + u *\<^sub>R b = 0"
    using assms by (auto simp: in_segment)
  hence b_eq: "b = (-(1 - u) / u) *\<^sub>R a"
    by (simp add: field_simps scaleR_conv_of_real)
  have "-norm a = norm b \<longleftrightarrow> a = 0 \<and> b = 0"
  proof safe
    assume "-norm a = norm b"
    hence "norm a = 0 \<and> norm b = 0"
      using norm_ge_zero[of a] norm_ge_zero[of b] by linarith
    thus "a = 0" "b = 0"
      by auto
  qed auto
  hence ne: "a \<noteq> b" "a' \<noteq> b'"
    using assms by (auto simp: a'_def b'_def in_segment)

  have "detour_rel {0} {} (linepath a' b') (?\<gamma> True a' b') (?\<gamma> False a' b')"
    unfolding a'_def b'_def
    by (rule detour_rel_linepath_semicircle_left_aux1) (use assms in \<open>auto simp: open_segment_def\<close>)
  hence "detour_rel ((*) \<alpha> ` {0}) ((*) \<alpha> ` {}) ((*) \<alpha> \<circ> linepath a' b')
           (\<lambda>\<epsilon>. (*) \<alpha> \<circ> ?\<gamma> True a' b' (\<epsilon> / norm \<alpha>)) (\<lambda>\<epsilon>. (*) \<alpha> \<circ> ?\<gamma> False a' b' (\<epsilon> / norm \<alpha>))"
    by (rule detour_rel_mult) auto
  hence "detour_rel {0} {} (linepath (\<alpha> * a') (\<alpha> * b'))
           (?\<gamma> True (\<alpha> * a') (\<alpha> * b')) (?\<gamma> False (\<alpha> * a') (\<alpha> * b'))"
    by (auto simp: linepath_mult_complex avoid_linepath_mult ne)
  also have "\<alpha> * a' = a"
    using ne u(1) by (simp add: a'_def b'_def b_eq \<alpha>_def complex_sgn_def 
                                field_simps scaleR_conv_of_real norm_divide)
  also have "\<alpha> * b' = b"
  proof -
    have "\<alpha> * b' = sgn (b - a) * complex_of_real (cmod b)"
      unfolding \<alpha>_def a'_def b'_def by simp
    also have "b - a = -(1 / u) *\<^sub>R a"
      using u(1) by (simp add: b_eq scaleR_conv_of_real field_simps)
    also have "sgn \<dots> = -sgn a"
      unfolding scaleR_conv_of_real using u(1) by (subst sgn_mult) (auto simp: sgn_of_real)
    also have "-sgn a * complex_of_real (norm b) = -(norm a * sgn a) * of_real ((1 - u) / u)"
      using u(1) by (simp add: b_eq field_simps)
    also have "norm a * sgn a = a"
      using \<open>a \<noteq> 0\<close> by (simp add: complex_sgn_def scaleR_conv_of_real)
    also have "-a * of_real ((1 - u) / u) = b"
      using u(1) by (simp add: b_eq scaleR_conv_of_real field_simps)
    finally show ?thesis .
  qed
  finally show ?thesis .
qed

lemma detour_rel_linepath_semicircle_left [detour_rel_intros]:
  assumes "bad \<in> open_segment a b"
  shows   "detour_rel {bad} {} (linepath a b)
             (avoid_linepath True  a b bad)
             (avoid_linepath False a b bad)"
proof -
  let ?\<gamma> = "avoid_linepath"
  show ?thesis
  proof -
    have "detour_rel {0} {} (linepath (a - bad) (b - bad))
            (?\<gamma> True  (a - bad) (b - bad) 0) (?\<gamma> False (a - bad) (b - bad) 0)"
    proof (rule detour_rel_linepath_semicircle_left_aux2)
      have "bad \<in> open_segment a b \<longleftrightarrow> -bad + bad \<in> open_segment (-bad + a) (-bad + b)"
        by (rule open_segment_translation_eq [symmetric])
      also have "-bad + bad = 0"
        by simp
      finally show "0 \<in> open_segment (a - bad) (b - bad)"
        using assms by simp
    qed
    hence "detour_rel ((+) bad ` {0}) ((+) bad ` {})
            ((+) bad \<circ> linepath (a - bad) (b - bad))
            (\<lambda>\<epsilon>. (+) bad \<circ> ?\<gamma> True  (a - bad) (b - bad) 0 \<epsilon>)
            (\<lambda>\<epsilon>. (+) bad \<circ> ?\<gamma> False (a - bad) (b - bad) 0 \<epsilon>)"
      by (rule detour_rel_translate)
    thus ?thesis
      by (auto simp: linepath_translate avoid_linepath_translate)
  qed
qed

lemma detour_rel_linepath_semicircle_right [detour_rel_intros]:
  assumes "bad \<in> open_segment a b"
  shows   "detour_rel {} {bad} (linepath a b)
             (avoid_linepath False a b bad)
             (avoid_linepath True  a b bad)"
  using detour_rel_linepath_semicircle_left[OF assms] by (simp add: detour_rel_swap)


subsubsection \<open>Circular arc\<close>

definition avoid_part_circlepath ::
    "bool \<Rightarrow> complex \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> complex" where
  "avoid_part_circlepath left x r a b \<phi> \<epsilon> = (
     let s = sgn (b - a);
         bad = x + rcis r \<phi>;
         \<alpha> = 2 * arcsin (\<epsilon> / (2 * r));
         \<beta> = arcsin (\<epsilon> / (2 * r)) + pi / 2
     in  part_circlepath x r a (\<phi> - s * \<alpha>) +++
         part_circlepath bad \<epsilon> (\<phi> - s * \<beta> + (if left = (a > b) then 0 else 2 * s * pi)) (\<phi> + s * \<beta>) +++
         part_circlepath x r (\<phi> + s * \<alpha>) b)"

lemma avoid_part_circlepath_translate:
  "(+) c \<circ> avoid_part_circlepath left x r a b \<phi> \<epsilon> =
   avoid_part_circlepath left (c + x) r a b \<phi> \<epsilon>"
proof -
  define \<delta> where "\<delta> = (if left then 0 else 2 * pi)"
  show ?thesis
  unfolding avoid_part_circlepath_def path_compose_join linepath_translate 
            part_circlepath_translate \<delta>_def [symmetric] Let_def  by (simp add: add_ac)
qed

lemma avoid_part_circlepath_mult_scaleR_0:
  assumes [simp]: "bad \<noteq> 0" and "c > 0"
  shows   "(*\<^sub>R) c \<circ> avoid_part_circlepath left 0 r a b \<phi> \<epsilon> =
             avoid_part_circlepath left 0 (norm c * r) a b \<phi> (norm c * \<epsilon>)"
proof -
  define \<delta> where "\<delta> = (if left then 0 else 2 * pi)"
  show ?thesis
  unfolding avoid_part_circlepath_def path_compose_join linepath_scaleR
            part_circlepath_scaleR \<delta>_def [symmetric] Let_def
  by (intro arg_cong2[of _ _ _ _ "(+++)"] part_circlepath_cong refl)
     (use \<open>c > 0\<close> in \<open>simp_all flip: cis_mult cis_divide 
                               add: cis_Arg sgn_mult scaleR_conv_of_real rcis_def\<close>)
qed

lemma avoid_part_circlepath_mult:
  assumes [simp]: "c \<noteq> 0"
  shows   "(*) c \<circ> avoid_part_circlepath left 0 r a b \<phi> \<epsilon> =
             avoid_part_circlepath left 0 (norm c * r)
               (a + Arg c) (b + Arg c) (\<phi> + Arg c) (norm c * \<epsilon>)"
proof -
  define \<delta> where "\<delta> = (if left then 0 else 2 * pi)"
  show ?thesis
  unfolding avoid_part_circlepath_def path_compose_join linepath_mult_complex
            part_circlepath_mult_complex \<delta>_def [symmetric] Let_def
  by (intro arg_cong2[of _ _ _ _ "(+++)"] part_circlepath_cong refl)
     (simp_all flip: cis_mult cis_divide cis_cnj
                          add: cis_Arg sgn_mult divide_conv_cnj norm_mult rcis_def 
                               complex_sgn_def scaleR_conv_of_real)
qed

lemma avoid_part_circlepath_cong:
  assumes "cis a = cis a'" "b' = b + a' - a" "\<phi>' = \<phi> + a' - a"
  shows "avoid_part_circlepath left x r a b \<phi> =
         avoid_part_circlepath left x r a' b' \<phi>'"
  unfolding avoid_part_circlepath_def Let_def
  by (rule ext, intro arg_cong2[of _ _ _ _ "(+++)"] part_circlepath_cong refl)
     (use assms in \<open>simp_all flip: cis_mult cis_divide add: rcis_def\<close>)

lemma avoid_part_circlepath_wf_aux1:
  assumes "r \<ge> 0" "r \<le> 2"
  shows    "(1 + of_real r * cis (arcsin (r / 2) + pi / 2)) = cis (2 * arcsin (r / 2))"
proof -
  have "(r / 2)\<^sup>2 \<le> (2 / 2) ^ 2"
    using assms by (intro power_mono) auto
  hence "(r / 2) ^ 2 \<le> 1"
    by (simp add: power2_eq_square)
  thus ?thesis using assms
    by (simp add: complex_eq_iff cos_arcsin sin_double cos_double sin_add cos_add power2_eq_square)
qed


locale avoid_part_circlepath_locale =
  fixes x :: complex and r a b \<phi> \<epsilon> :: real
  assumes \<epsilon>: "\<epsilon> > 0" "\<epsilon> < 2 * r" and ab: "a \<noteq> b"
begin

definition s where "s = sgn (b - a)"
definition bad where "bad = x + rcis r \<phi>"
definition "\<alpha> = 2 * arcsin (\<epsilon> / (2 * r))"
definition "\<beta> = arcsin (\<epsilon> / (2 * r)) + pi / 2"

lemma ends:
  "x + rcis r (\<phi> - s * \<alpha>) = bad +
     rcis \<epsilon> (\<phi> - s * \<beta> + (if left = (a > b) then 0 else 2 * s * pi))" (is ?th1)
  "x + rcis r (\<phi> + s * \<alpha>) = bad + rcis \<epsilon> (\<phi> + s * \<beta>)" (is ?th2)
proof -
  have *: "x + rcis r (\<phi> - s * \<alpha>) = bad + rcis \<epsilon> (\<phi> - s * \<beta>)" if s: "s \<in> {-1, 1}" for s
  proof -
    have "bad + rcis \<epsilon> (\<phi> - s * \<beta>) = x + (rcis r \<phi> + rcis \<epsilon> (\<phi> - s * \<beta>))"
      by (auto simp: rcis_def bad_def simp flip: cis_divide cis_mult)
    also have "rcis \<epsilon> (\<phi> - s * \<beta>) = \<epsilon> *\<^sub>R cis \<phi> * cis (-s * \<beta>)" using ab
      by (auto simp: rcis_def scaleR_conv_of_real s_def divide_conv_cnj sgn_if
               simp flip: cis_divide cis_cnj)
    also have "rcis r \<phi> + \<epsilon> *\<^sub>R cis \<phi> * cis (-s * \<beta>) =
                 (cis \<phi> * of_real r) * (1 + of_real (\<epsilon> / r) * cis (-s * \<beta>))"
      using \<epsilon> by (simp add: field_simps scaleR_conv_of_real rcis_def)
    also have *: "(1 + of_real (\<epsilon> / r) * cis \<beta>) = cis \<alpha>"
      using avoid_part_circlepath_wf_aux1[of "\<epsilon> / r"] \<epsilon>
      by (simp add: \<beta>_def \<alpha>_def mult_ac divide_simps
               del: div_mult_self3 div_mult_self4 div_mult_self2 div_mult_self1)
    hence "(1 + of_real (\<epsilon> / r) * cis (-s*\<beta>)) = cis (-s*\<alpha>)"
    proof (cases "s = 1")
      case [simp]: True
      have "cnj ((1 + of_real (\<epsilon> / r) * cis (-s*\<beta>))) = cnj (cis (-s*\<alpha>))"
        using * by (simp add: cis_cnj)
      thus ?thesis
        using complex_cnj_cancel_iff by blast
    qed (use * s ab in auto)
    also have "x + cis \<phi> * of_real r * \<dots> = x + rcis r (\<phi> - s * \<alpha>)" using ab
      by (auto simp: s_def sgn_if scaleR_conv_of_real rcis_def divide_conv_cnj
               simp flip: cis_divide cis_cnj cis_mult)
    finally show ?thesis
      by (simp add: rcis_def scaleR_conv_of_real divide_conv_cnj mult_ac
               flip: cis_divide cis_cnj)
  qed

  have "rcis \<epsilon> (\<phi> - s * \<beta> + (if left = (a > b) then 0 else 2 * s * pi)) = rcis \<epsilon> (\<phi> - s * \<beta>)"
    by (auto simp: rcis_def s_def sgn_if simp flip: cis_divide cis_mult)
  with *[of s] show ?th1 using ab
    by (auto simp: s_def sgn_if)

  from *[of "-s"] show ?th2 using ab
    by (auto simp: s_def sgn_if)
qed

lemma valid_path: "valid_path (avoid_part_circlepath left x r a b \<phi> \<epsilon>)"
  unfolding avoid_part_circlepath_def Let_def s_def [symmetric]
            bad_def [symmetric] \<alpha>_def [symmetric] \<beta>_def [symmetric]
  by (intro valid_path_join valid_path_linepath valid_path_part_circlepath)
     (use ends in \<open>simp_all add: rcis_def exp_eq_polar\<close>)

end

lemma valid_path_avoid_part_circlepath:
  assumes "\<epsilon> \<in> {0<..<2*r}" "a \<noteq> b"
  shows   "valid_path (avoid_part_circlepath left x r a b \<phi> \<epsilon>)"
proof -
  interpret avoid_part_circlepath_locale x r a b \<phi> \<epsilon>
    by standard (use assms in auto)
  show ?thesis
    by (rule valid_path)
qed

lemma valid_path_avoid_part_circlepath':
  assumes "a \<noteq> b" "r > 0"
  shows   "eventually (\<lambda>\<epsilon>. valid_path (avoid_part_circlepath left x r a b \<phi> \<epsilon>)) (at_right 0)"
proof -
  have "eventually (\<lambda>\<epsilon>. \<epsilon> \<in> {0<..<2*r}) (at_right 0)"
    using assms(2) eventually_at_right_real by force
  thus ?thesis
    by eventually_elim (use assms in \<open>auto intro!: valid_path_avoid_part_circlepath\<close>)
qed

lemma sphere_inter_sphere_pos_real_line_aux1:
  assumes r: "r \<ge> 0" "r \<le> 1"
  shows   "dist 1 (cis (2 * arcsin (r / 2))) = r"
proof -
  have "r ^ 2 / 4 \<le> 1 ^ 2 / 4"
    using r by (intro divide_right_mono power_mono) auto
  also have "\<dots> \<le> 1"
    by simp
  finally have *: "r ^ 2 / 4 \<le> 1" .
  thus "dist 1 (cis (2 * arcsin (r / 2))) = r"
    using r * by (simp add: dist_norm norm_complex_def cos_arcsin power2_eq_square
                            algebra_simps cos_double sin_double)
qed

lemma sphere_inter_sphere_pos_real_line_aux2':
  assumes r: "r \<ge> 0" "r \<le> 1"
  assumes dist: "dist 1 (cis x) = r"
  shows "[x = 2 * arcsin (r / 2)] (rmod 2 * pi) \<or> [x = -2 * arcsin (r / 2)] (rmod 2 * pi)"
proof -
  have "r ^ 2 \<le> 1"
    using power_mono[of r 1 2] assms by simp
  have "r ^ 2 = norm (cis x - 1) ^ 2"
    by (subst dist [symmetric]) (auto simp: dist_norm norm_minus_commute)
  also have "\<dots> = (cos x - 1) ^ 2 + (sin x)\<^sup>2"
    unfolding cmod_power2 by simp
  also have "\<dots> = sin x ^ 2 + cos x ^ 2 - 2 * cos x + 1"
    by (simp add: power2_eq_square algebra_simps)
  also have "sin x ^ 2 + cos x ^ 2 = 1"
    by (rule sin_cos_squared_add)
  finally have "cos x = 1 - r ^ 2 / 2"
    by (simp add: field_simps)
  also have "cos x = cos \<bar>x\<bar>"
    by simp
  also have "1 - r ^ 2 / 2 = sqrt (1 - (r / 2) ^ 2) ^ 2 - (r / 2) ^ 2"
    using r \<open>r ^ 2 \<le> 1\<close> by (simp add: power2_eq_square algebra_simps)
  also have "\<dots> = cos (2 * arcsin (r / 2))"
    using r by (simp add: cos_double cos_arcsin)
  finally have *: "cos \<bar>x\<bar> = cos (2 * arcsin (r / 2))" .
  from cos_eq_cos_conv_rmod [OF this] show ?thesis
    by (cases "x \<ge> 0") (auto simp: rcong_uminus_left_iff)
qed

lemma sphere_inter_sphere_pos_real_line_aux2:
  assumes r: "r \<ge> 0" "r \<le> 1" and x: "x \<in> {-pi..pi}"
  assumes dist: "dist 1 (cis x) = r"
  shows "\<bar>x\<bar> = 2 * arcsin (r / 2)"
proof -
  have "arcsin (r / 2) \<ge> arcsin 0" "arcsin (r / 2) \<le> arcsin (1 / 2)"
    using assms by (intro arcsin_le_arcsin; simp)+
  hence arcsin: "arcsin (r / 2) \<in> {0..pi / 6}"
    by auto

  have "[x = 2 * arcsin (r / 2)] (rmod 2 * pi) \<or> [x = -2 * arcsin (r / 2)] (rmod 2 * pi)"
    by (intro sphere_inter_sphere_pos_real_line_aux2') (use assms in auto)
  hence "x = 2 * arcsin (r / 2) \<or> x = -2 * arcsin (r / 2)"
  proof (rule disj_forward)
    assume "[x = 2 * arcsin (r / 2)] (rmod 2 * pi)"
    moreover have "\<bar>x - 2 * arcsin (r / 2)\<bar> < \<bar>2 * pi\<bar>"
      using pi_gt_zero arcsin x unfolding atLeastAtMost_iff by linarith
    ultimately show "x = 2 * arcsin (r / 2)"
      by (rule rcong_imp_eq)
  next
    assume "[x = -2 * arcsin (r / 2)] (rmod 2 * pi)"
    moreover have "\<bar>x - (-2 * arcsin (r / 2))\<bar> < \<bar>2 * pi\<bar>"
      using pi_gt_zero arcsin x unfolding atLeastAtMost_iff by linarith
    ultimately show "x = -2 * arcsin (r / 2)"
      by (rule rcong_imp_eq)
  qed
  thus ?thesis using arcsin
    by (auto simp: abs_if)
qed

lemma sphere_inter_sphere_aux1:
  assumes r: "r \<ge> 0" "r \<le> 1"
  shows   "dist (cis \<phi>) (cis (\<phi> + 2 * arcsin (r / 2))) = r"
proof -
  have "dist (cis \<phi> * 1) (cis \<phi> * cis (2 * arcsin (r / 2))) =
        dist 1 (cis (2 * arcsin (r / 2)))"
    by (subst dist_mult_left) auto
  also have "\<dots> = r"
    by (rule sphere_inter_sphere_pos_real_line_aux1) (use assms in auto)
  finally show ?thesis
    by (simp add: cis_mult)
qed

lemma sphere_inter_sphere_aux2:
  assumes r: "r \<ge> 0" "r \<le> 1"
  assumes dist: "dist (cis \<phi>) (cis x) = r"
  shows "[x = \<phi> + 2 * arcsin (r / 2)] (rmod 2 * pi) \<or> [x = \<phi> - 2 * arcsin (r / 2)] (rmod 2 * pi)"
proof -
  have "dist (cis \<phi> * 1) (cis \<phi> * cis (x - \<phi>)) =
           dist 1 (cis (x - \<phi>))"
    by (subst dist_mult_left) auto
  also have "cis \<phi> * cis (x - \<phi>) = cis x"
    by (simp add: cis_mult)
  finally have *: "dist 1 (cis (x - \<phi>)) = r"
    using dist by simp
  have "[x - \<phi> = 2 * arcsin (r / 2)] (rmod 2 * pi) \<or>
        [x - \<phi> = -2 * arcsin (r / 2)] (rmod 2 * pi)"
    by (intro sphere_inter_sphere_pos_real_line_aux2') (use * r in auto)
  hence "[x - \<phi> + \<phi> = 2 * arcsin (r / 2) + \<phi>] (rmod 2 * pi) \<or>
         [x - \<phi> + \<phi> = -2 * arcsin (r / 2) + \<phi>] (rmod 2 * pi)"
    by (rule disj_forward; intro rcong_intros)
  thus ?thesis
    by (simp add: algebra_simps)
qed
  
lemma detour_rel_part_circlepath_semicircle_left_aux1:
  assumes ab: "a < 0" "0 < b" "a \<ge> -pi" "b \<le> pi"
  shows "detour_rel {1} {} (part_circlepath 0 1 a b)
           (avoid_part_circlepath True  0 1 a b 0)
           (avoid_part_circlepath False 0 1 a b 0)"
proof -
  define \<alpha> where "\<alpha> = (\<lambda>\<epsilon>. 2 * arcsin (\<epsilon>/2))"
  define \<beta> where "\<beta> = (\<lambda>\<epsilon>. arcsin (\<epsilon>/2) + pi / 2)"
  define p where "p \<equiv> part_circlepath 0 1 a b"
  define p1 where "p1 \<equiv> (\<lambda>\<epsilon>. part_circlepath 0 1 a (-\<alpha> \<epsilon>))"
  define p2 where "p2 \<equiv> (\<lambda>\<epsilon>. part_circlepath 0 1 (\<alpha> \<epsilon>) b)"
  define pm where "pm \<equiv> (\<lambda>\<epsilon>. part_circlepath 0 1 (-\<alpha> \<epsilon>) (\<alpha> \<epsilon>))"

  define cl :: "real \<Rightarrow> real \<Rightarrow> complex"
    where "cl = (\<lambda>\<epsilon>. part_circlepath 1 \<epsilon> (-\<beta> \<epsilon> + 2 * pi) (\<beta> \<epsilon>))"
  define cr :: "real \<Rightarrow> real \<Rightarrow> complex"
    where "cr = (\<lambda>\<epsilon>. part_circlepath 1 \<epsilon> (-\<beta> \<epsilon>) (\<beta> \<epsilon>))"
  note [simp] = closed_segment_eq_real_ivl1 closed_segment_same_Im
  note homoI = homotopic_paths_subset[OF simply_connected_imp_homotopic_paths]

  define eps where "eps = Min {1, - (sin (a / 2) * 2), sin (b / 2) * 2}"

  note [[goals_limit = 30]]
  have "detour_rel {1} {} p (\<lambda>\<epsilon>. p1 \<epsilon> +++ cl \<epsilon> +++ p2 \<epsilon>) (\<lambda>\<epsilon>. p1 \<epsilon> +++ cr \<epsilon> +++ p2 \<epsilon>)"
    unfolding cl_def cr_def
  proof (rule detour_rel_avoid_basic_part_circlepath_left [where eps = eps])
    have "1 = p (a / (a - b))" "a / (a - b) \<in> {0..1}"
      using ab by (auto simp: p_def part_circlepath_altdef linepath_def field_simps)
    hence "1 \<in> path_image p"
      unfolding path_image_def by auto
    moreover have "1 \<notin> {pathstart p, pathfinish p}"
      using ab by (auto simp: p_def rcis_def cis_eq_1_iff' rcis_def exp_eq_polar)
    ultimately show "1 \<in> path_image p - {pathstart p, pathfinish p}"
      by blast
    show "eps > 0"
      unfolding eps_def using ab
      by (subst Min_gr_iff) (auto intro!: sin_lt_zero' sin_gt_zero)
  next
    fix \<epsilon> :: real assume \<epsilon>: "\<epsilon> > 0" "\<epsilon> < eps"
    have "eps \<le> x" if "x \<in> {1, -sin (a/2) * 2, sin (b/2) * 2}" for x
      using that unfolding eps_def by (intro Min.coboundedI) auto
    with \<epsilon> have \<epsilon>: "\<epsilon> > 0" "\<epsilon> < 1" "\<epsilon> < -sin (a/2) * 2" "\<epsilon> < sin (b/2) * 2"
      unfolding insert_iff empty_iff simp_thms by force+

    have "arcsin (\<epsilon> / 2) > 0"
      using \<epsilon> by (intro arcsin_pos) auto
    moreover have "arcsin (\<epsilon> / 2) < arcsin 1"
      using \<epsilon> by (subst arcsin_less_mono) auto
    ultimately have arcsin: "arcsin (\<epsilon> / 2) > 0" "arcsin (\<epsilon> / 2) < pi / 2"
      using \<epsilon> by simp_all

    define S where "S \<equiv> path_image p \<union> (cball 1 \<epsilon>)"
    have [simp]: "path (p1 \<epsilon>)" "path (p2 \<epsilon>)" "path (pm \<epsilon>)"
      by (simp_all add: p1_def p2_def pm_def)
    have "\<alpha> \<epsilon> > 0"
      using \<epsilon> by (simp add: \<alpha>_def arcsin_pos)
    have "arcsin (\<epsilon> / 2) < arcsin (sin (-a/2))"
      using \<epsilon> ab by (subst arcsin_less_mono) auto
    hence "a < -\<alpha> \<epsilon>"
      using \<epsilon> ab by (simp add: \<alpha>_def field_simps arcsin_sin del: sin_minus)
    have "arcsin (\<epsilon> / 2) < arcsin (sin (b/2))"
      using \<epsilon> ab by (subst arcsin_less_mono) auto
    hence "b > \<alpha> \<epsilon>"
      using \<epsilon> ab by (simp add: \<alpha>_def field_simps arcsin_sin del: sin_minus)
    note \<alpha> = \<open>a < -\<alpha> \<epsilon>\<close> \<open>\<alpha> \<epsilon> < b\<close> \<open>\<alpha> \<epsilon> > 0\<close>

    have "(\<epsilon> / 2) ^ 2 \<le> (1 / 2) ^ 2"
      using \<epsilon> by (intro power_mono divide_right_mono) auto
    hence *: "1 - (\<epsilon> / 2)\<^sup>2 \<ge> 0"
      by (simp add: power_divide)
    have **: "cis (\<alpha> \<epsilon>) = 1 + complex_of_real \<epsilon> * cis (\<beta> \<epsilon>)"
      using \<alpha> \<epsilon> ab * unfolding \<beta>_def \<alpha>_def
      by (auto simp add: complex_eq_iff diff_divide_distrib
                    cos_diff sin_diff add_divide_distrib cos_add sin_add cos_arcsin
                    cos_double sin_double power_divide power2_eq_square [symmetric])

    have ends: "pathstart (p1 \<epsilon>) = rcis 1 a"
               "pathfinish (p1 \<epsilon>) = pathstart (pm \<epsilon>)"
               "pathfinish (pm \<epsilon>) = pathstart (p2 \<epsilon>)"
               "pathstart (pm \<epsilon>) = 1 + rcis \<epsilon> (- \<beta> \<epsilon>)"
               "pathstart (p2 \<epsilon>) = 1 + rcis \<epsilon> (\<beta> \<epsilon>)"
               "pathfinish (p2 \<epsilon>) = rcis 1 b"
               "pathstart (cl \<epsilon>) = pathstart (pm \<epsilon>)" "pathstart (cr \<epsilon>) = pathstart (pm \<epsilon>)"
               "pathfinish (cl \<epsilon>) = pathstart (p2 \<epsilon>)" "pathfinish (cr \<epsilon>) = pathstart (p2 \<epsilon>)"
      by (auto simp: p1_def p2_def pm_def cl_def cr_def rcis_def ** divide_conv_cnj rcis_def exp_eq_polar
               simp flip: cis_cnj cis_divide)

    have "eq_paths p (p1 \<epsilon> +++ part_circlepath 0 1 (-\<alpha> \<epsilon>) b)"
      unfolding p1_def p_def
      by (rule eq_paths_sym[OF eq_paths_part_circlepaths]) (use \<epsilon> \<alpha> in auto)
    also have "eq_paths \<dots> (p1 \<epsilon> +++ pm \<epsilon> +++ p2 \<epsilon>)"
      unfolding p1_def p2_def pm_def
      by (intro eq_paths_join eq_paths_sym[OF eq_paths_part_circlepaths]) (use \<epsilon> \<alpha> in auto)
    finally show "eq_paths p (p1 \<epsilon> +++ pm \<epsilon> +++ p2 \<epsilon>)" .

    show "path_image (p1 \<epsilon>) \<inter> path_image (p2 \<epsilon>) \<subseteq> {pathstart p} \<inter> {pathfinish p}"
    proof (intro subsetI; elim IntE)
      fix x assume x: "x \<in> path_image (p1 \<epsilon>)" "x \<in> path_image (p2 \<epsilon>)"
      from x(1) obtain u where u: "u \<in> {a..-\<alpha> \<epsilon>}" "x = cis u"
        unfolding p1_def using ab \<alpha>
        by (subst (asm) path_image_part_circlepath') (auto simp: rcis_def)
      from x(2) obtain v where v: "v \<in> {\<alpha> \<epsilon>..b}" "x = cis v"
        unfolding p2_def using ab \<alpha>
        by (subst (asm) path_image_part_circlepath') (auto simp: rcis_def)
      from u v have "cis (u - v) = 1"
        by (simp flip: cis_divide)
      then obtain n where n': "u - v = 2 * pi * of_int n"
        by (auto simp: cis_eq_1_iff)
      hence n: "of_int n = (u - v) / (2 * pi)"
        by simp

      have "of_int n < (1 :: real)"
        unfolding n using u v ab \<alpha> by simp
      hence "n < 1"
        by linarith
      moreover have "of_int n \<ge> (-1 :: real)"
        unfolding n using u v ab \<alpha> by (simp add: field_simps)
      hence "n \<ge> -1"
        by linarith
      ultimately have "n = 0 \<or> n = -1"
        by linarith
      thus "x \<in> {pathstart p} \<inter> {pathfinish p}"
      proof
        assume "n = 0"
        thus ?thesis using u v \<alpha> ab n' by auto
      next
        assume "n = -1"
        hence "u \<ge> -pi" "v \<le> pi" "u - v = -2 * pi"
          using u v ab n' \<alpha> by simp_all
        hence "u = -pi \<and> v = pi \<and> a = -pi \<and> b = pi"
          using u v ab unfolding atLeastAtMost_iff by linarith
        thus ?thesis using u v
          by (auto simp: p_def rcis_def rcis_def exp_eq_polar)
      qed
    qed

    show "does_not_cross (p1 \<epsilon>) (sphere 1 \<epsilon>)"
    proof (subst does_not_cross_simple_path)
      show "path_image (p1 \<epsilon>) \<inter> sphere 1 \<epsilon> \<subseteq> {pathstart (p1 \<epsilon>), pathfinish (p1 \<epsilon>)}"
      proof (intro subsetI; elim IntE)
        fix x assume x: "x \<in> path_image (p1 \<epsilon>)" "x \<in> sphere 1 \<epsilon>"
        obtain t where t: "t \<in> {a..-\<alpha> \<epsilon>}" "x = cis t"
          using x(1) \<alpha> unfolding p1_def path_image_part_circlepath' by (auto simp: rcis_def)
        with x(2) \<epsilon> ab \<alpha> have "\<bar>t\<bar> = \<alpha> \<epsilon>"
          unfolding \<alpha>_def by (intro sphere_inter_sphere_pos_real_line_aux2) auto
        moreover have "t < 0"
          using t(1) \<alpha> ab by auto
        ultimately have "t = -\<alpha> \<epsilon>"
          by simp
        thus "x \<in> {pathstart (p1 \<epsilon>), pathfinish (p1 \<epsilon>)}"
          by (auto simp: p1_def rcis_def t rcis_def exp_eq_polar)
      qed
    qed (use \<epsilon> \<alpha> ab in \<open>auto simp: p1_def simple_path_part_circlepath\<close>)

    show "does_not_cross (p2 \<epsilon>) (sphere 1 \<epsilon>)"
    proof (subst does_not_cross_simple_path)
      show "path_image (p2 \<epsilon>) \<inter> sphere 1 \<epsilon> \<subseteq> {pathstart (p2 \<epsilon>), pathfinish (p2 \<epsilon>)}"
      proof (intro subsetI; elim IntE)
        fix x assume x: "x \<in> path_image (p2 \<epsilon>)" "x \<in> sphere 1 \<epsilon>"
        obtain t where t: "t \<in> {\<alpha> \<epsilon>..b}" "x = cis t"
          using x(1) \<alpha> unfolding p2_def path_image_part_circlepath' by (auto simp: rcis_def)
        with x(2) \<epsilon> ab \<alpha> have "\<bar>t\<bar> = \<alpha> \<epsilon>"
          unfolding \<alpha>_def by (intro sphere_inter_sphere_pos_real_line_aux2) auto
        moreover have "t > 0"
          using t(1) \<alpha> ab by auto
        ultimately have "t = \<alpha> \<epsilon>"
          by simp
        thus "x \<in> {pathstart (p2 \<epsilon>), pathfinish (p2 \<epsilon>)}"
          by (auto simp: p2_def rcis_def t rcis_def exp_eq_polar)
      qed
    qed (use \<epsilon> \<alpha> ab in \<open>auto simp: p2_def simple_path_part_circlepath\<close>)

    show "does_not_cross (pm \<epsilon>) (sphere 1 \<epsilon>)"
    proof (subst does_not_cross_simple_path)
      show "path_image (pm \<epsilon>) \<inter> sphere 1 \<epsilon> \<subseteq> {pathstart (pm \<epsilon>), pathfinish (pm \<epsilon>)}"
      proof (intro subsetI; elim IntE)
        fix x assume x: "x \<in> path_image (pm \<epsilon>)" "x \<in> sphere 1 \<epsilon>"
        obtain t where t: "t \<in> {-\<alpha> \<epsilon>..\<alpha> \<epsilon>}" "x = cis t"
          using x(1) \<alpha> unfolding pm_def path_image_part_circlepath' by (auto simp: rcis_def)
        with x(2) \<epsilon> ab \<alpha> have "\<bar>t\<bar> = \<alpha> \<epsilon>"
          unfolding \<alpha>_def by (intro sphere_inter_sphere_pos_real_line_aux2) auto
        hence "t = \<alpha> \<epsilon> \<or> t = -\<alpha> \<epsilon>"
          by (cases "t \<ge> 0") auto
        thus "x \<in> {pathstart (pm \<epsilon>), pathfinish (pm \<epsilon>)}"
          by (auto simp: pm_def rcis_def t rcis_def exp_eq_polar)
      qed
    qed (use \<epsilon> \<alpha> ab in \<open>auto simp: pm_def simple_path_part_circlepath\<close>)

    show "- \<beta> \<epsilon> \<noteq> \<beta> \<epsilon> \<and> \<bar>\<beta> \<epsilon> - - \<beta> \<epsilon>\<bar> < 2 * pi"
      using arcsin by (auto simp: \<beta>_def)

    show "- \<beta> \<epsilon> + 2 * pi \<noteq> \<beta> \<epsilon> \<and>
         \<bar>\<beta> \<epsilon> - (- \<beta> \<epsilon> + 2 * pi)\<bar> < 2 * pi \<and>
         cis (- \<beta> \<epsilon> + 2 * pi) = cis (- \<beta> \<epsilon>) \<and>
         cis (\<beta> \<epsilon>) = cis (\<beta> \<epsilon>) \<and> \<beta> \<epsilon> - - \<beta> \<epsilon> + (- \<beta> \<epsilon> + 2 * pi) - \<beta> \<epsilon> = 2 * pi"
      using arcsin by (auto simp: \<beta>_def divide_conv_cnj simp flip: cis_divide cis_cnj cis_mult)

    show "pathfinish (p1 \<epsilon>) = 1 + rcis \<epsilon> (- \<beta> \<epsilon>)"
         "pathstart  (p2 \<epsilon>) = 1 + rcis \<epsilon> (\<beta> \<epsilon>)"
         "pathstart  (pm \<epsilon>) = pathfinish (p1 \<epsilon>)"
         "pathfinish (pm \<epsilon>) = pathstart  (p2 \<epsilon>)"
      by (auto simp: ends)
  qed (auto simp: p1_def p2_def)
  thus ?thesis using ab
    by (simp add: p_def p1_def cl_def p2_def cr_def \<alpha>_def \<beta>_def
                  avoid_part_circlepath_def [abs_def] Let_def)
qed

lemma avoid_part_circlepath_extend_right:
  assumes "a < b \<and> b < c \<or> c < b \<and> b < a" "\<phi> \<in> open_segment a b" "r > 0"
  assumes \<epsilon>: "\<epsilon> > 0" "\<epsilon> < r * (2 * sin (\<bar>b - \<phi>\<bar> / 2))"
  shows "avoid_part_circlepath left x r a b \<phi> \<epsilon> +++ part_circlepath x r b c \<equiv>\<^sub>p
         avoid_part_circlepath left x r a c \<phi> \<epsilon>"
proof -
  note \<open>\<epsilon> < r * (2 * sin (\<bar>b - \<phi>\<bar> / 2))\<close>
  also have "r * (2 * sin (\<bar>b - \<phi>\<bar> / 2)) \<le> r * (2 * 1)"
    using \<open>r > 0\<close> by (intro mult_left_mono sin_le_one) (use assms in auto)
  finally have \<epsilon>': "\<epsilon> < 2 * r"
    by simp
  then interpret avoid_part_circlepath_locale x r a b \<phi> \<epsilon>
    by unfold_locales (use assms in auto)

  have s': "sgn (c - a) = s"
    using assms by (auto simp add: s_def)
  define \<delta> where "\<delta> = (if left = (b < a) then 0 else 2 * s * pi)"
  have eq: "left = (c < a) \<longleftrightarrow> left = (b < a)"
    using assms by auto
  note defs = s_def [symmetric] s' \<alpha>_def [symmetric] \<beta>_def [symmetric] \<delta>_def [symmetric] eq

  have "arcsin (\<epsilon> / (2 * r)) < arcsin (sin (min (pi/2) (\<bar>b - \<phi>\<bar> / 2)))"
    using assms \<epsilon>' by (intro arcsin_less_arcsin) (auto simp: field_simps min_def)
  also have "\<dots> = min (pi/2) (\<bar>b - \<phi>\<bar> / 2)"
    by (subst arcsin_sin) (use pi_gt_zero in \<open>auto simp del: pi_gt_zero\<close>)
  also have "\<dots> \<le> \<bar>b - \<phi>\<bar> / 2"
    by linarith
  finally have "\<alpha> < \<bar>b - \<phi>\<bar>"
    by (simp add: \<alpha>_def)
  hence **: "if b < c then \<phi> + s * \<alpha> < b else \<phi> + s * \<alpha> > b"
    using assms(1,2) by (auto simp: s_def abs_if open_segment_eq_real_ivl split: if_splits)

  have *: "rcis r \<phi> + rcis \<epsilon> (\<phi> + s * \<beta>) = rcis r (\<phi> + s * \<alpha>)"
          "rcis r (\<phi> - s * \<alpha>) = rcis r \<phi> + rcis \<epsilon> (\<phi> - s * \<beta> + \<delta>)"
    using ends(1)[of left] ends(2) unfolding \<delta>_def bad_def by (simp_all add: \<delta>_def)

  have "avoid_part_circlepath left x r a b \<phi> \<epsilon> +++ part_circlepath x r b c \<equiv>\<^sub>p 
        part_circlepath x r a (\<phi> - s * \<alpha>) +++ part_circlepath (x + rcis r \<phi>) \<epsilon> (\<phi> - s * \<beta> + \<delta>) (\<phi> + s * \<beta>) +++
        part_circlepath x r (\<phi> + s * \<alpha>) b +++ part_circlepath x r b c"
    unfolding avoid_part_circlepath_def Let_def defs by path (use * in simp_all)
  also have "\<dots> \<equiv>\<^sub>p part_circlepath x r a (\<phi> - s * \<alpha>) +++
                   part_circlepath (x + rcis r \<phi>) \<epsilon> (\<phi> - s * \<beta> + \<delta>) (\<phi> + s * \<beta>) +++
                   part_circlepath x r (\<phi> + s * \<alpha>) c"
    using * ** assms
    by (intro eq_paths_join eq_paths_refl eq_paths_part_circlepaths)
       (auto simp: closed_segment_eq_real_ivl rcis_def exp_eq_polar)
  also have "\<dots> = avoid_part_circlepath left x r a c \<phi> \<epsilon>"
    unfolding avoid_part_circlepath_def Let_def defs by simp
  finally show ?thesis .
qed

lemma avoid_part_circlepath_extend_left:
  assumes "c < a \<and> a < b \<or> c > a \<and> a > b" "\<phi> \<in> open_segment a b" "r > 0"
  assumes \<epsilon>: "\<epsilon> > 0" "\<epsilon> < r * (2 * sin (\<bar>a - \<phi>\<bar> / 2))"
  shows   "part_circlepath x r c a +++ avoid_part_circlepath left x r a b \<phi> \<epsilon> \<equiv>\<^sub>p
           avoid_part_circlepath left x r c b \<phi> \<epsilon>"
proof -
  note \<open>\<epsilon> < r * (2 * sin (\<bar>a - \<phi>\<bar> / 2))\<close>
  also have "r * (2 * sin (\<bar>a - \<phi>\<bar> / 2)) \<le> r * (2 * 1)"
    using \<open>r > 0\<close> by (intro mult_left_mono sin_le_one) (use assms in auto)
  finally have \<epsilon>': "\<epsilon> < 2 * r"
    by simp
  then interpret avoid_part_circlepath_locale x r a b \<phi> \<epsilon>
    by unfold_locales (use assms in auto)

  have s': "sgn (b - c) = s"
    using assms by (auto simp: s_def)
  define \<delta> where "\<delta> = (if left = (b < a) then 0 else 2 * s * pi)"
  have eq: "left = (b < c) \<longleftrightarrow> left = (b < a)"
    using assms by auto
  note defs = s_def [symmetric] s' \<alpha>_def [symmetric] \<beta>_def [symmetric] \<delta>_def [symmetric] eq

  have "arcsin (\<epsilon> / (2 * r)) < arcsin (sin (min (pi/2) (\<bar>a - \<phi>\<bar> / 2)))"
    using assms \<epsilon>' by (intro arcsin_less_arcsin) (auto simp: field_simps min_def)
  also have "\<dots> = min (pi/2) (\<bar>a - \<phi>\<bar> / 2)"
    by (subst arcsin_sin) (use pi_gt_zero in \<open>auto simp del: pi_gt_zero\<close>)
  also have "\<dots> \<le> \<bar>a - \<phi>\<bar> / 2"
    by linarith
  finally have "\<alpha> < \<bar>a - \<phi>\<bar>"
    by (simp add: \<alpha>_def)
  hence **: "if c < a then \<phi> - s * \<alpha> > a else \<phi> - s * \<alpha> < a"
    using assms(1,2) by (auto simp: s_def abs_if open_segment_eq_real_ivl split: if_splits)

  have *: "rcis r \<phi> + rcis \<epsilon> (\<phi> + s * \<beta>) = rcis r (\<phi> + s * \<alpha>)"
          "rcis r (\<phi> - s * \<alpha>) = rcis r \<phi> + rcis \<epsilon> (\<phi> - s * \<beta> + \<delta>)"
    using ends(1)[of left] ends(2) unfolding \<delta>_def bad_def by (simp_all add: \<delta>_def)

  have "part_circlepath x r c a +++ avoid_part_circlepath left x r a b \<phi> \<epsilon> \<equiv>\<^sub>p 
        (part_circlepath x r c a +++ part_circlepath x r a (\<phi> - s * \<alpha>)) +++
        (part_circlepath (x + rcis r \<phi>) \<epsilon> (\<phi> - s * \<beta> + \<delta>) (\<phi> + s * \<beta>) +++
         part_circlepath x r (\<phi> + s * \<alpha>) b)"
    unfolding avoid_part_circlepath_def Let_def defs by path (use * in simp_all)
  also have "\<dots> \<equiv>\<^sub>p part_circlepath x r c (\<phi> - s * \<alpha>) +++
                   part_circlepath (x + rcis r \<phi>) \<epsilon> (\<phi> - s * \<beta> + \<delta>) (\<phi> + s * \<beta>) +++
                   part_circlepath x r (\<phi> + s * \<alpha>) b"
    using * ** assms
    by (intro eq_paths_join eq_paths_refl eq_paths_part_circlepaths)
       (auto simp: closed_segment_eq_real_ivl rcis_def exp_eq_polar)
  also have "\<dots> = avoid_part_circlepath left x r c b \<phi> \<epsilon>"
    unfolding avoid_part_circlepath_def Let_def defs by simp
  finally show ?thesis .
qed

lemma avoid_part_circlepath_reverse:
  assumes "a \<noteq> b" "\<epsilon> > 0" "\<epsilon> < 2 * r"
  shows "reversepath (avoid_part_circlepath left x r a b \<phi> \<epsilon>) \<equiv>\<^sub>p
         avoid_part_circlepath (\<not>left) x r b a \<phi> \<epsilon>"
proof -
  interpret avoid_part_circlepath_locale x r a b \<phi> \<epsilon>
    by unfold_locales (use assms in auto)

  have s: "sgn (a - b) = -s"
    using assms by (auto simp: s_def sgn_if)
  define \<delta> where "\<delta> = (if left = (b < a) then 0 else 2 * s * pi)"
  define \<delta>' where "\<delta>' = (if (\<not>left) \<noteq> (a < b) then 0 else 2 * (-s) * pi)"
  note defs = s_def [symmetric] s \<alpha>_def [symmetric] \<beta>_def [symmetric]
              \<delta>_def [symmetric] \<delta>'_def [symmetric]

  have *: "rcis r (\<phi> - s * \<alpha>) = rcis r \<phi> + rcis \<epsilon> (\<phi> - s * \<beta> + \<delta>)"
          "rcis r \<phi> + rcis \<epsilon> (\<phi> + s * \<beta>) = rcis r (\<phi> + s * \<alpha>)"
    using ends(1)[of left] ends(2) unfolding \<delta>_def bad_def by (simp_all add: \<delta>_def)
  have "reversepath (avoid_part_circlepath left x r a b \<phi> \<epsilon>) \<equiv>\<^sub>p
          part_circlepath x r b (\<phi> + s * \<alpha>) +++
          part_circlepath (x + rcis r \<phi>) \<epsilon> (\<phi> + s * \<beta>) (\<phi> - s * \<beta> + \<delta>) +++
          part_circlepath x r (\<phi> - s * \<alpha>) a"
    unfolding avoid_part_circlepath_def Let_def defs by path (use * in simp_all)
  also have "\<dots> = avoid_part_circlepath (\<not>left) x r b a \<phi> \<epsilon>"
    unfolding avoid_part_circlepath_def Let_def defs
    by (intro arg_cong2[of _ _ _ _ "(+++)"] part_circlepath_cong refl)
       (simp_all flip: cis_mult add: \<delta>'_def \<delta>_def s_def sgn_if)
  finally show ?thesis .
qed


lemma detour_rel_part_circlepath_semicircle_left_aux2:
  assumes ab: "a < 0" "0 < b"
  shows "detour_rel {1} {} (part_circlepath 0 1 a b)
           (avoid_part_circlepath True  0 1 a b 0)
           (avoid_part_circlepath False 0 1 a b 0)"
proof -
  let ?\<gamma> = "\<lambda>left a b. avoid_part_circlepath left 0 1 a b 0"
  define a' where "a' = max a (-pi/2)"
  define b' where "b' = min b (pi/2)"

  define p1 where "p1 = part_circlepath 0 1 a' b'"
  define p2 where "p2 = part_circlepath 0 1 a b'"
  define p3 where "p3 = part_circlepath 0 1 a b"

  have less: "a' < b'" "a < b'"
    using ab pi_gt_zero by (auto simp: a'_def b'_def simp del: pi_gt_zero)

  have 1: "detour_rel {1} {} p1
             (\<lambda>\<epsilon>. ?\<gamma> True a' b' \<epsilon>) (\<lambda>\<epsilon>. ?\<gamma> False a' b' \<epsilon>)"
    using ab unfolding p1_def a'_def b'_def
    by (intro detour_rel_part_circlepath_semicircle_left_aux1)
       (auto simp: min_le_iff_disj le_max_iff_disj)

  have 2: "detour_rel {1} {} p2 (\<lambda>\<epsilon>. ?\<gamma> True a b' \<epsilon>) (\<lambda>\<epsilon>. ?\<gamma> False a b' \<epsilon>)"
  proof (cases "a = a'")
    case False
    hence "a < a'"
      by (auto simp: a'_def)

    have "detour_rel ({} \<union> {1}) ({} \<union> {}) (part_circlepath 0 1 a a' +++ p1)
            (\<lambda>\<epsilon>. part_circlepath 0 1 a a' +++ ?\<gamma> True a' b' \<epsilon>)
            (\<lambda>\<epsilon>. part_circlepath 0 1 a a' +++ ?\<gamma> False a' b' \<epsilon>)"
      by (intro detour_rel_join 1 detour_rel_refl) (auto simp: p1_def)
    thus ?thesis
    proof (rule detour_rel_congI)
      have "2 * sin (\<bar>a'\<bar> / 2) > 0" using assms
        by (intro mult_pos_pos sin_gt_zero) (auto simp: a'_def max_def)
      hence "eventually (\<lambda>x. x < 2 * sin (\<bar>a'\<bar> / 2)) (at_right 0)"
        using eventually_at_right_field by blast
      moreover have "eventually (\<lambda>x :: real. x > 0) (at_right 0)"
        by (simp add: eventually_at_right_less)
      ultimately have "\<forall>\<^sub>F \<epsilon> in at_right 0. part_circlepath 0 1 a a' +++ ?\<gamma> left a' b' \<epsilon> \<equiv>\<^sub>p ?\<gamma> left a b' \<epsilon>"
        (is "?P left") for left
      proof eventually_elim
        case (elim \<epsilon>)
        have "a' < 0" "b' > 0"
          using False a'_def b'_def pi_gt_zero assms by (auto simp: min_def max_def)
        moreover have "b' - a' \<le> pi"
          by (auto simp: b'_def a'_def)
        ultimately show ?case using \<open>a < a'\<close> \<open>a' < b'\<close> elim
          by (intro avoid_part_circlepath_extend_left)
             (use assms in \<open>auto simp: open_segment_eq_real_ivl\<close>)
      qed
      from this[of True] and this[of False] show "?P True" "?P False" .
      show "part_circlepath 0 1 a a' +++ p1 \<equiv>\<^sub>p p2"
        unfolding p1_def p2_def
        by (intro eq_paths_part_circlepaths)
           (use \<open>a < a'\<close> \<open>a' < b'\<close> in \<open>auto simp: closed_segment_eq_real_ivl\<close>)
    qed (use less in \<open>auto simp: p1_def intro!: valid_path_avoid_part_circlepath'\<close>)
  qed (use 1 in \<open>simp_all add: a'_def p1_def p2_def\<close>)

  show "detour_rel {1} {} p3 (\<lambda>\<epsilon>. ?\<gamma> True a b \<epsilon>) (\<lambda>\<epsilon>. ?\<gamma> False a b \<epsilon>)"
  proof (cases "b = b'")
    case False
    hence "b > b'"
      by (auto simp: b'_def)
    have "detour_rel ({1} \<union> {}) ({} \<union> {}) (p2 +++ part_circlepath 0 1 b' b)
            (\<lambda>\<epsilon>. ?\<gamma> True a b' \<epsilon> +++ part_circlepath 0 1 b' b)
            (\<lambda>\<epsilon>. ?\<gamma> False a b' \<epsilon> +++ part_circlepath 0 1 b' b)"
      by (intro detour_rel_join 2 detour_rel_refl) (auto simp: p2_def)
    thus ?thesis
    proof (rule detour_rel_congI)
      have "2 * sin (\<bar>b'\<bar> / 2) > 0" using assms
        by (intro mult_pos_pos sin_gt_zero) (auto simp: b'_def min_def)
      hence "eventually (\<lambda>x. x < 2 * sin (\<bar>b'\<bar> / 2)) (at_right 0)"
        using eventually_at_right_field by blast
      moreover have "eventually (\<lambda>x :: real. x > 0) (at_right 0)"
        by (simp add: eventually_at_right_less)
      ultimately have "\<forall>\<^sub>F \<epsilon> in at_right 0. ?\<gamma> left a b' \<epsilon> +++ part_circlepath 0 1 b' b \<equiv>\<^sub>p ?\<gamma> left a b \<epsilon>"
        (is "?P left") for left
      proof eventually_elim
        case (elim \<epsilon>)
        have "b' > 0"
          using assms by (auto simp: b'_def)
        thus ?case using \<open>b > b'\<close> \<open>a < b'\<close> elim
          by (intro avoid_part_circlepath_extend_right)
             (use assms in \<open>auto simp: open_segment_eq_real_ivl\<close>)
      qed
      from this[of True] and this[of False] show "?P True" "?P False" .
      show "p2 +++ part_circlepath 0 1 b' b \<equiv>\<^sub>p p3"
        unfolding p2_def p3_def
        by (intro eq_paths_part_circlepaths)
           (use \<open>b > b'\<close> \<open>a < b'\<close> in \<open>auto simp: closed_segment_eq_real_ivl\<close>)
    qed (use assms in \<open>auto simp: p2_def intro!: valid_path_avoid_part_circlepath'\<close>)
  qed (use 2 in \<open>simp_all add: a'_def p2_def p3_def\<close>)
qed

lemma detour_rel_part_circlepath_semicircle_left_aux3:
  assumes ab: "0 \<in> open_segment a b"
  shows "detour_rel {1} {} (part_circlepath 0 1 a b)
           (avoid_part_circlepath True  0 1 a b 0)
           (avoid_part_circlepath False 0 1 a b 0)"
proof (cases "a < b")
  case True
  thus ?thesis
    using detour_rel_part_circlepath_semicircle_left_aux2[of a b] assms
    by (simp add: open_segment_eq_real_ivl)
next
  case False
  hence "a > b"
    using ab by (auto simp: open_segment_eq_real_ivl split: if_splits)
  let ?\<gamma> = "\<lambda>left a b. avoid_part_circlepath left 0 1 a b 0"
  have "detour_rel {1} {} (part_circlepath 0 1 b a) (?\<gamma> True b a) (?\<gamma> False b a)"
    using detour_rel_part_circlepath_semicircle_left_aux2[of b a] assms \<open>a > b\<close>
    by (simp add: open_segment_eq_real_ivl)
  note detour_rel_swap[OF detour_rel_reverse [OF this]]
  thus ?thesis
  proof (rule detour_rel_congI)
    have "eventually (\<lambda>\<epsilon> :: real. \<epsilon> > 0 \<and> \<epsilon> < 2) (at_right 0)"
      using eventually_at_right_field zero_less_numeral by blast
    hence *: "\<forall>\<^sub>F \<epsilon> in at_right 0. reversepath (?\<gamma> left b a \<epsilon>) \<equiv>\<^sub>p ?\<gamma> (\<not>left) a b \<epsilon>"
      (is "?P left") for left
    proof eventually_elim
      case (elim \<epsilon>)
      thus ?case using \<open>a > b\<close>
        by (intro avoid_part_circlepath_reverse) (use assms in auto)
    qed

    show "\<forall>\<^sub>F \<epsilon> in at_right 0.
       reversepath (avoid_part_circlepath True 0 1 b a 0 \<epsilon>) \<equiv>\<^sub>p
       avoid_part_circlepath False 0 1 a b 0 \<epsilon>"
      using *[of True] by simp
    show "\<forall>\<^sub>F \<epsilon> in at_right 0.
       reversepath (avoid_part_circlepath False 0 1 b a 0 \<epsilon>) \<equiv>\<^sub>p
       avoid_part_circlepath True 0 1 a b 0 \<epsilon>"
      using *[of False] by simp
  qed (use ab in \<open>auto intro!: valid_path_avoid_part_circlepath'\<close>)
qed

lemma detour_rel_part_circlepath_semicircle_left_aux4:
  assumes "\<phi> \<in> open_segment a b" "bad = rcis r \<phi>" "r > 0"
  shows "detour_rel {bad} {} (part_circlepath 0 r a b)
           (avoid_part_circlepath True  0 r a b \<phi>)
           (avoid_part_circlepath False 0 r a b \<phi>)"
proof -
  {
    fix left :: bool
    have "(\<lambda>\<epsilon>. (*) bad \<circ> avoid_part_circlepath left 0 1 (a - \<phi>) (b - \<phi>) 0 (\<epsilon> / norm bad)) =
               avoid_part_circlepath left 0 r (a - \<phi> + Arg (rcis r \<phi>))
               (b - \<phi> + Arg (rcis r \<phi>)) (Arg (rcis r \<phi>))"
      (is "?l = _") using assms by (subst avoid_part_circlepath_mult) simp_all
    also have "\<dots> = avoid_part_circlepath left 0 r a b \<phi>"
      using \<open>r > 0\<close>
      by (intro avoid_part_circlepath_cong)
         (auto simp: rcis_def cis_Arg simp flip: cis_mult cis_divide)
    finally have "?l = \<dots>" .
  } note eq = this

  have "0 \<in> open_segment (a - \<phi>) (b - \<phi>)"
    using assms by (auto simp: open_segment_eq_real_ivl)
  have "detour_rel {1} {} (part_circlepath 0 1 (a - \<phi>) (b - \<phi>))
          (avoid_part_circlepath True 0 1 (a - \<phi>) (b - \<phi>) 0)
          (avoid_part_circlepath False 0 1 (a - \<phi>) (b - \<phi>) 0)"
    by (rule detour_rel_part_circlepath_semicircle_left_aux3) fact
  hence "detour_rel ((*) bad ` {1}) ((*) bad ` {}) ((*) bad \<circ> part_circlepath 0 1 (a - \<phi>) (b - \<phi>))
          (\<lambda>\<epsilon>. (*) bad \<circ> avoid_part_circlepath True 0 1 (a - \<phi>) (b - \<phi>) 0 (\<epsilon> / norm bad))
          (\<lambda>\<epsilon>. (*) bad \<circ> avoid_part_circlepath False 0 1 (a - \<phi>) (b - \<phi>) 0 (\<epsilon> / norm bad))"
    by (rule detour_rel_mult) (use assms in auto)
  also have "(*) bad \<circ> part_circlepath 0 1 (a - \<phi>) (b - \<phi>) =
              part_circlepath 0 (cmod bad) (a - \<phi> + Arg bad) (b - \<phi> + Arg bad)"
    by (simp add: part_circlepath_mult_complex)
  also have "\<dots> = part_circlepath 0 r a b"
    using assms by (intro part_circlepath_cong)
                   (auto simp: rcis_def norm_mult cis_Arg simp flip: cis_mult cis_divide)
  also note eq[of True]
  also note eq[of False]
  finally show ?thesis by simp
qed





lemma detour_rel_part_circlepath_semicircle_left [detour_rel_intros]:
  assumes "\<phi> \<in> open_segment a b" "bad = x + rcis r \<phi>" "r > 0"
  shows "detour_rel {bad} {} (part_circlepath x r a b)
           (avoid_part_circlepath True  x r a b \<phi>)
           (avoid_part_circlepath False x r a b \<phi>)"
proof -
  have "detour_rel {bad - x} {} (part_circlepath 0 r a b)
           (avoid_part_circlepath True  0 r a b \<phi>)
           (avoid_part_circlepath False 0 r a b \<phi>)"
    by (rule detour_rel_part_circlepath_semicircle_left_aux4) (use assms in auto)
  hence "detour_rel ((+) x ` {bad - x}) ((+) x ` {}) ((+) x \<circ> part_circlepath 0 r a b)
           (\<lambda>\<epsilon>. (+) x \<circ> avoid_part_circlepath True  0 r a b \<phi> \<epsilon>)
           (\<lambda>\<epsilon>. (+) x \<circ> avoid_part_circlepath False 0 r a b \<phi> \<epsilon>)"
    by (rule detour_rel_translate)
  thus ?thesis
    by (simp add: part_circlepath_translate avoid_part_circlepath_translate)
qed

lemma detour_rel_part_circlepath_semicircle_right [detour_rel_intros]:
  assumes "\<phi> \<in> open_segment a b" "bad = x + rcis r \<phi>" "r > 0"
  shows "detour_rel {} {bad} (part_circlepath x r a b)
           (avoid_part_circlepath False x r a b \<phi>)
           (avoid_part_circlepath True  x r a b \<phi>)"
  using detour_rel_part_circlepath_semicircle_left[OF assms] by (rule detour_rel_swap)


subsubsection \<open>Line--line corner\<close>

definition avoid_linepath_linepath where
  "avoid_linepath_linepath left a b c \<epsilon> = (
     let s = sgn (Arg (c - b) - Arg (a - b));
         \<delta> = (if left \<longleftrightarrow> Arg (a - b) \<ge> Arg (c - b) then 0 else 2 * s * pi)
     in  linepath a (b + \<epsilon> *\<^sub>R sgn (a - b)) +++
         part_circlepath b \<epsilon> (Arg (a - b) + \<delta>) (Arg (c - b)) +++
         linepath (b + \<epsilon> *\<^sub>R sgn (c - b)) c)"

lemma avoid_linepath_linepath_translate:
  "(+) d \<circ> avoid_linepath_linepath left a b c \<epsilon> =
   avoid_linepath_linepath left (d + a) (d + b) (d + c) \<epsilon>"
  unfolding avoid_linepath_linepath_def path_compose_join linepath_translate 
            part_circlepath_translate Let_def by (simp add: algebra_simps)

lemma avoid_linepath_linepath_mult:
  assumes "a \<noteq> 0" "b \<noteq> 0"
  shows   "(*) c \<circ> avoid_linepath_linepath left a 0 b \<epsilon> =
           avoid_linepath_linepath left (c * a) 0 (c * b) (norm c * \<epsilon>)"
proof (cases "c = 0")
  assume "c = 0"
  thus ?thesis
    by (auto simp: avoid_linepath_linepath_def joinpaths_def
                   fun_eq_iff part_circlepath_def linepath_def)
next
  assume [simp]: "c \<noteq> 0"
  define \<beta> where "\<beta> = (if left = (Arg b \<le> Arg a) then 0 else 2 * sgn (Arg b - Arg a) * pi)"
  define \<beta>' where "\<beta>' = (if left = (Arg (c * b) \<le> Arg (c * a)) then 0 else 2 * sgn (Arg (c * b) - Arg (c * a)) * pi)"
  have [simp]: "cis \<beta> = 1" "cis \<beta>' = 1"
    by (auto simp: \<beta>_def \<beta>'_def sgn_if)

  have "(*) c \<circ> avoid_linepath_linepath left a 0 b \<epsilon> = 
          linepath (c * a) (c * (\<epsilon> *\<^sub>R sgn a)) +++
          part_circlepath 0 (norm c * \<epsilon>) (Arg a + \<beta> + Arg c) (Arg b + Arg c) +++
          linepath (c * (\<epsilon> *\<^sub>R sgn b)) (c * b)"
    unfolding avoid_linepath_linepath_def path_compose_join linepath_mult_complex 
              part_circlepath_mult_complex Let_def \<beta>_def by simp
  also have "part_circlepath 0 (norm c * \<epsilon>) (Arg a + \<beta> + Arg c) (Arg b + Arg c) =
             part_circlepath 0 (norm c * \<epsilon>) (Arg (c * a) + \<beta>') (Arg (c * b))"
  proof (rule part_circlepath_cong)
    show "cis (Arg (c * a) + \<beta>') = cis (Arg a + \<beta> + Arg c)"
      using assms by (auto simp flip: cis_mult simp: cis_Arg sgn_mult)
    have "Arg (c * b) - Arg (c * a) = Arg b - Arg a + \<beta>' - \<beta>"
      using assms Arg_bounded[of a] Arg_bounded[of b] Arg_bounded[of c]
      by (simp add: Arg_times' \<beta>'_def \<beta>_def) (* this takes a few seconds *)
    thus "Arg (c * b) = Arg (c * a) + \<beta>' + (Arg b + Arg c) - (Arg a + \<beta> + Arg c)"
      by simp
  qed auto
  also have "linepath (c * a) (c * (\<epsilon> *\<^sub>R sgn a)) +++ \<dots> +++ linepath (c * (\<epsilon> *\<^sub>R sgn b)) (c * b) =
               linepath (c * a) ((norm c * \<epsilon>) *\<^sub>R sgn (c * a)) +++
               part_circlepath 0 (norm c * \<epsilon>) (Arg (c * a) + \<beta>') (Arg (c * b)) +++
               linepath ((norm c * \<epsilon>) *\<^sub>R sgn (c * b)) (c * b)"
    by (simp add: algebra_simps scaleR_conv_of_real complex_sgn_def norm_mult)
  also have "\<dots> = avoid_linepath_linepath left (c * a) 0 (c * b) (norm c * \<epsilon>)"
     unfolding avoid_linepath_linepath_def path_compose_join linepath_mult_complex 
               part_circlepath_mult_complex Let_def \<beta>'_def by simp
   finally show ?thesis .
qed


lemma norm_linepath_0: "norm (linepath 0 a x) = \<bar>x\<bar> * norm a"
  by (simp add: linepath_def)

lemma norm_linepath_0': "norm (linepath a 0 x) = \<bar>1 - x\<bar> * norm a"
  by (simp add: linepath_def)

lemma detour_rel_avoid_linepath_linepath_aux1:
  assumes "1 \<notin> closed_segment 0 c" "c \<notin> closed_segment 0 1" "Arg c > 0"
  shows   "detour_rel {0} {} (linepath 1 0 +++ linepath 0 c)
             (avoid_linepath_linepath True 1 0 c) (avoid_linepath_linepath False 1 0 c)"
proof -
  define p1 where "p1 = (\<lambda>\<epsilon>. linepath 1 (of_real \<epsilon>) :: real \<Rightarrow> complex)"
  define p2 where "p2 = (\<lambda>\<epsilon>. linepath (\<epsilon> *\<^sub>R sgn c) c :: real \<Rightarrow> complex)"
  define pm1 where "pm1 = (\<lambda>\<epsilon>. linepath (of_real \<epsilon>) 0 :: real \<Rightarrow> complex)"
  define pm2 where "pm2 = (\<lambda>\<epsilon>. linepath 0 (\<epsilon> *\<^sub>R sgn c) :: real \<Rightarrow> complex)"
  define cl where "cl = (\<lambda>\<epsilon>. part_circlepath 0 \<epsilon> (2 * pi) (Arg c))"
  define cr where "cr = (\<lambda>\<epsilon>. part_circlepath 0 \<epsilon> 0 (Arg c))"

  have [simp]: "c \<noteq> 0"
    using assms by auto
  hence [simp]: "sgn c \<noteq> 0"
    by (simp add: sgn_zero_iff)
  note [simp] = closed_segment_same_Im closed_segment_eq_real_ivl

  have "detour_rel {0} {} (linepath 1 0 +++ linepath 0 c) 
          (\<lambda>\<epsilon>. p1 \<epsilon> +++ cl \<epsilon> +++ p2 \<epsilon>) (\<lambda>\<epsilon>. p1 \<epsilon> +++ cr \<epsilon> +++ p2 \<epsilon>)"
    unfolding cl_def cr_def
  proof (rule detour_rel_avoid_basic_part_circlepath_left [where eps = "min 1 (norm c)"])
    fix \<epsilon> assume \<epsilon>: "\<epsilon> > 0" "\<epsilon> < min 1 (norm c)"

    have "\<epsilon> *\<^sub>R sgn c \<noteq> c"
      using \<epsilon> by (auto simp: scaleR_conv_of_real complex_sgn_def field_simps)
    have "\<epsilon> *\<^sub>R sgn c = linepath 0 c (\<epsilon> / norm c)"
      by (auto simp: linepath_def complex_sgn_def field_simps)
    also have "\<dots> \<in> closed_segment 0 c"
      using \<epsilon> by (subst in_segment) auto
    finally have "\<epsilon> *\<^sub>R sgn c \<in> closed_segment 0 c" .
    hence "linepath 1 0 +++ linepath 0 c \<equiv>\<^sub>p (p1 \<epsilon> +++ pm1 \<epsilon>) +++ (pm2 \<epsilon> +++ p2 \<epsilon>)"
      unfolding p1_def pm1_def pm2_def p2_def using \<epsilon> \<open>\<epsilon> *\<^sub>R sgn c \<noteq> c\<close>
      by (intro eq_paths_join eq_paths_linepaths') auto
    also have "\<dots> \<equiv>\<^sub>p p1 \<epsilon> +++ (pm1 \<epsilon> +++ pm2 \<epsilon>) +++ p2 \<epsilon>"
      unfolding p1_def pm1_def pm2_def p2_def by path
    finally show "linepath 1 0 +++ linepath 0 c \<equiv>\<^sub>p p1 \<epsilon> +++ (pm1 \<epsilon> +++ pm2 \<epsilon>) +++ p2 \<epsilon>" .

    have *: "Im z \<noteq> 0 \<or> Re z < 0" if "z \<in> closed_segment (\<epsilon> *\<^sub>R sgn c) c" for z
    proof (cases "Im c = 0")
      case False
      thus ?thesis using \<epsilon>
        using in_closed_segment_imp_Im_in_closed_segment[OF that]
        by (auto split: if_splits simp: field_simps mult_le_0_iff zero_le_mult_iff)
    next
      case True
      hence "Re c < 0"
        using assms(3) by (simp add: Arg_pos_iff)
      have "Re z \<in> closed_segment (Re (\<epsilon> *\<^sub>R sgn c)) (Re c)"
        by (intro in_closed_segment_imp_Re_in_closed_segment that)
      have "closed_segment (\<epsilon> *\<^sub>R sgn c) c \<subseteq> {z. Re z < 0}"
        by (intro closed_segment_subset)
           (use \<open>Re c < 0\<close> \<epsilon> in \<open>auto simp: scaleR_conv_of_real field_simps
                                   mult_pos_neg mult_neg_pos convex_halfspace_Re_lt\<close>)
      thus ?thesis
        using that by auto
    qed

    show "path_image (p1 \<epsilon>) \<inter> path_image (p2 \<epsilon>)
         \<subseteq> {pathstart (linepath 1 0 +++ linepath 0 c)} \<inter>
            {pathfinish (linepath 1 0 +++ linepath 0 c)}"
      using \<epsilon> by (auto simp: p1_def p2_def complex_eq_iff dest: *)

    show "0 \<noteq> Arg c \<and> \<bar>Arg c - 0\<bar> < 2 * pi"
         "2 * pi \<noteq> Arg c \<and> \<bar>Arg c - 2 * pi\<bar> < 2 * pi \<and> cis (2 * pi) = cis 0 \<and>
         cis (Arg c) = cis (Arg c) \<and> Arg c - 0 + 2 * pi - Arg c = 2 * pi"
      using assms Arg_bounded[of c] by (auto)

    show "does_not_cross (p1 \<epsilon>) (sphere 0 \<epsilon>)"
      using \<epsilon> by (subst does_not_cross_simple_path) (auto simp: p1_def complex_eq_iff cmod_eq_Re)
    show "does_not_cross (pm1 \<epsilon> +++ pm2 \<epsilon>) (sphere 0 \<epsilon>)" using \<epsilon>
      by (auto simp: does_not_cross_def joinpaths_def pm1_def pm2_def 
                     abs_mult norm_sgn norm_linepath_0')
    show "does_not_cross (p2 \<epsilon>) (sphere 0 \<epsilon>)"
      unfolding does_not_cross_def
    proof
      fix t :: real assume t: "t \<in> {0<..<1}"
      have "norm (p2 \<epsilon> t) = norm (linepath (\<epsilon> *\<^sub>R sgn c) c t)"
        by (simp add: p2_def)
      also have "linepath (\<epsilon> *\<^sub>R sgn c) c t = ((1 - t) * (\<epsilon> * inverse (cmod c)) + t) *\<^sub>R c"
        by (simp add: linepath_def complex_sgn_def algebra_simps)
      also have "norm \<dots> = ((1 - t) * (\<epsilon> * inverse (norm c)) + t) * norm c"
        using t \<epsilon> by (subst norm_scaleR) simp_all
      also have "\<dots> = \<epsilon> + t * (norm c - \<epsilon>)"
        by (auto simp: algebra_simps)
      also have "\<dots> \<noteq> \<epsilon>"
        using \<epsilon> t by auto
      finally show "p2 \<epsilon> t \<notin> sphere 0 \<epsilon>"
        by simp
    qed
  qed (auto simp: p1_def p2_def pm1_def pm2_def path_image_join complex_sgn_def 
                  rcis_def scaleR_conv_of_real field_simps cis_Arg)
  thus ?thesis
    using \<open>Arg c > 0\<close>
    by (simp add: p1_def p2_def cl_def cr_def avoid_linepath_linepath_def [abs_def] scaleR_conv_of_real)
qed


lemma detour_rel_avoid_linepath_linepath_aux2:
  assumes "1 \<notin> closed_segment 0 c" "c \<notin> closed_segment 0 1"
  shows   "detour_rel {0} {} (linepath 1 0 +++ linepath 0 c)
             (avoid_linepath_linepath True 1 0 c) (avoid_linepath_linepath False 1 0 c)"
proof (cases "Arg c > 0")
  case True
  thus ?thesis
    using detour_rel_avoid_linepath_linepath_aux1[of c] assms by simp
next
  case False
  have "Arg c \<noteq> 0"
  proof
    assume "Arg c = 0"
    hence "c \<in> \<real>" "Re c \<ge> 0"
      by (auto simp: Arg_eq_0)
    thus False using assms
      by (auto simp: complex_is_Real_iff closed_segment_same_Im closed_segment_eq_real_ivl)
  qed
  with False have "Arg c < 0"
    by auto
  have [simp]: "Arg (cnj c) = -Arg c"
    using \<open>Arg c < 0\<close> by (auto simp: Arg_cnj elim!: Reals_cases split: if_splits)
  have [simp]: "cnj (sgn (cnj c)) = sgn c"
    by (auto simp: complex_sgn_def)

  have *: "detour_rel {0} {} (linepath 1 0 +++ linepath 0 (cnj c))
             (avoid_linepath_linepath True 1 0 (cnj c)) (avoid_linepath_linepath False 1 0 (cnj c))"
  proof (rule detour_rel_avoid_linepath_linepath_aux1)
    have "cnj 1 \<notin> closed_segment (cnj 0) (cnj c)"
      by (subst closed_segment_cnj) (use assms in auto)
    thus "1 \<notin> closed_segment 0 (cnj c)"
      by simp
  next
    have "cnj c \<notin> closed_segment (cnj 0) (cnj 1)"
      by (subst closed_segment_cnj) (use assms in auto)
    thus "cnj c \<notin> closed_segment 0 1"
      by simp
  qed (use \<open>Arg c < 0\<close> in auto)

  have "detour_rel {} {0} (linepath 1 0 +++ linepath 0 c)
         (\<lambda>\<epsilon>. cnj \<circ> avoid_linepath_linepath True 1 0 (cnj c) \<epsilon>)
         (\<lambda>\<epsilon>. cnj \<circ> avoid_linepath_linepath False 1 0 (cnj c) \<epsilon>)"
    using detour_rel_cnj[OF *] by (simp add: path_compose_join linepath_cnj')
  also have "(\<lambda>\<epsilon>. cnj \<circ> avoid_linepath_linepath True 1 0 (cnj c) \<epsilon>) = 
               avoid_linepath_linepath False 1 0 c" using \<open>Arg c < 0\<close>
    by (auto simp: avoid_linepath_linepath_def path_compose_join linepath_cnj'
                   part_circlepath_cnj' fun_eq_iff)
  also have "(\<lambda>\<epsilon>. cnj \<circ> avoid_linepath_linepath False 1 0 (cnj c) \<epsilon>) = 
               avoid_linepath_linepath True 1 0 c" using \<open>Arg c < 0\<close>
    by (auto simp: avoid_linepath_linepath_def path_compose_join linepath_cnj'
                   part_circlepath_cnj' fun_eq_iff)
  finally have "detour_rel {} {0} (linepath 1 0 +++ linepath 0 c)
                  (avoid_linepath_linepath False 1 0 c)
                  (avoid_linepath_linepath True 1 0 c)" .
  from detour_rel_swap[OF this] show ?thesis
    by simp
qed

lemma detour_rel_avoid_linepath_linepath_aux3:
  assumes "a \<notin> closed_segment 0 c" "c \<notin> closed_segment a 0"
  shows   "detour_rel {0} {} (linepath a 0 +++ linepath 0 c)
             (avoid_linepath_linepath True a 0 c) (avoid_linepath_linepath False a 0 c)"
proof -
  define c' where "c' = c / a"
  have "a \<noteq> 0" "c \<noteq> 0"
    using assms by auto
  hence c_eq: "c = a * c'"
    by (auto simp: c'_def)

  have *: "detour_rel {0} {} (linepath 1 0 +++ linepath 0 c')
             (avoid_linepath_linepath True 1 0 c') (avoid_linepath_linepath False 1 0 c')"
  proof (rule detour_rel_avoid_linepath_linepath_aux2)
    show "1 \<notin> closed_segment 0 c'"
      using assms by (simp add: c_eq in_segment(1) scaleR_conv_of_real)
    show "c' \<notin> closed_segment 0 1"
    proof
      assume "c' \<in> closed_segment 0 1"
      hence "a * c' \<in> closed_segment (a * 0) (a * 1)"
        by (subst closed_segment_mult [symmetric]) auto
      thus False
        using assms by (simp add: c_eq closed_segment_commute)
    qed
  qed

  show ?thesis
    using detour_rel_mult[OF *, of a] \<open>a \<noteq> 0\<close> \<open>c \<noteq> 0\<close>
    by (simp add: path_compose_join linepath_mult_complex c_eq avoid_linepath_linepath_mult)
qed

lemma detour_rel_avoid_linepath_linepath_left [detour_rel_intros]:
  assumes "a \<notin> closed_segment b c" "c \<notin> closed_segment a b"
  shows   "detour_rel {b} {} (linepath a b +++ linepath b c)
             (avoid_linepath_linepath True a b c) (avoid_linepath_linepath False a b c)"
proof -
  have *: "detour_rel {0} {} (linepath (a - b) 0 +++ linepath 0 (c - b))
               (avoid_linepath_linepath True (a - b) 0 (c - b))
               (avoid_linepath_linepath False (a - b) 0 (c - b))"
  proof (rule detour_rel_avoid_linepath_linepath_aux3)
    show "a - b \<notin> closed_segment 0 (c - b)"
      using assms(1) closed_segment_translation_eq[of b "a - b" 0 "c - b"] by auto
    show "c - b \<notin> closed_segment (a - b) 0"
      using assms(2) closed_segment_translation_eq[of b "c - b" "a - b" 0] by auto
  qed
  show ?thesis
    using detour_rel_translate[OF *, of b]
    by (simp add: path_compose_join linepath_translate avoid_linepath_linepath_translate)
qed

lemma detour_rel_avoid_linepath_linepath_right [detour_rel_intros]:
  assumes "a \<notin> closed_segment b c" "c \<notin> closed_segment a b"
  shows   "detour_rel {} {b} (linepath a b +++ linepath b c)
             (avoid_linepath_linepath False a b c) (avoid_linepath_linepath True a b c)"
  using detour_rel_swap[OF detour_rel_avoid_linepath_linepath_left[OF assms]] by simp



subsubsection \<open>Line--arc corner\<close>

(*
TODO: Generalise the thing below to this. Not sure if correct.
definition avoid_linepath_circlepath_gen where
  "avoid_linepath_circlepath_gen left z x r a b \<epsilon> =
     (let \<alpha> = 2 * arcsin (\<epsilon> / (2 * r));
          \<beta> = pi / 3 + arcsin (\<epsilon> / (2 * r));
          \<phi> = Arg (x - (z + cis a)) - a
      in  linepath x (z + cis a + rcis \<epsilon> (a + \<phi>)) +++
          part_circlepath (z + cis a) \<epsilon> (a + \<phi> + (if left then 0 else 2 * pi)) (a + \<beta>) +++
          part_circlepath z r (a + \<alpha>) b)"
*)

text \<open>
  Avoidance pattern for a bad point lying on the junction between a straight vertical line coming
  from above to the point $e^{2i\pi/3}$ and a circular arc with radius 1 around the origin that
  continues from there to the right.

  The bad point is avoided by cutting out a circle of radius \<open>\<epsilon>\<close> around it from the path
  and replacing the removed section with a circular arc of radius \<open>\<epsilon>\<close> around the bad point.
\<close>
definition avoid_linepath_circlepath where
  "avoid_linepath_circlepath left y a \<epsilon> =
     (let \<alpha> = 2 * arcsin (\<epsilon> / 2);
          bad = cis (2*pi/3);
          \<beta> = pi / 3 + arcsin (\<epsilon> / 2)
      in  linepath (-1/2 + y *\<^sub>R \<i>) (bad + \<epsilon> *\<^sub>R \<i>) +++
          part_circlepath bad \<epsilon> (pi/2) (pi/2 - \<beta> + (if left then 0 else 2 * pi)) +++
          part_circlepath 0 1 (2*pi/3 - \<alpha>) a)"

lemma cis_double: "cis (2 * x) = cis x ^ 2"
  by (simp add: complex_eq_iff cos_double sin_double power2_eq_square)

lemma valid_path_avoid_linepath_circlepath:
  assumes "\<epsilon> \<ge> 0" "\<epsilon> \<le> 2"
  shows   "valid_path (avoid_linepath_circlepath left y a \<epsilon>)"
proof -
  have "(\<epsilon> / 2) ^ 2 \<le> (2 / 2) ^ 2"
    by (intro power_mono) (use assms in auto)
  thus ?thesis using assms (* TODO: cleanup *)
  unfolding avoid_linepath_circlepath_def Let_def
  apply (intro valid_path_join valid_path_linepath valid_path_part_circlepath)
   apply (auto simp: rcis_def scaleR_conv_of_real cis_double divide_conv_cnj norm_power rcis_def exp_eq_polar
               simp flip: cis_divide cis_mult)
  apply (auto simp: complex_eq_iff cos_arcsin power2_eq_square cos_120 sin_120 sin_30 cos_30)
  apply (auto simp: field_simps simp del: div_mult_self3 div_mult_self4 div_mult_self2 div_mult_self1)
  done
qed

locale avoid_linepath_circlepath_locale =
  fixes y a \<epsilon> :: real
  assumes \<epsilon>: "\<epsilon> \<in> {0<..<2}"
begin

definition \<alpha> where "\<alpha> = 2 * arcsin (\<epsilon> / 2)"
definition bad where "bad = cis (2 * pi / 3)"
definition \<beta> where "\<beta> = pi / 3 + arcsin (\<epsilon> / 2)"

lemma ends: "bad + \<epsilon> *\<^sub>R \<i> = bad + rcis \<epsilon> (pi / 2)"
            "bad + rcis \<epsilon> (pi/2 - \<beta> + (if left then 2 * pi else 0)) = cis (2*pi/3 - \<alpha>)"
proof -
  note [simp del] = div_mult_self3 div_mult_self4 div_mult_self2 div_mult_self1
  show "bad + \<epsilon> *\<^sub>R \<i> = bad + rcis \<epsilon> (pi / 2)"
    by (auto simp: rcis_def scaleR_conv_of_real)
  have "(\<epsilon> / 2) ^ 2 \<le> 1 ^ 2"
    using \<epsilon> by (intro power_mono) auto
  hence "cis (2 * pi / 3) + complex_of_real \<epsilon> * (cis (pi / 6) * cnj (cis (arcsin (\<epsilon> / 2)))) =
          cis (2 * pi / 3) * cnj (cis (2 * arcsin (\<epsilon> / 2)))" using \<epsilon>
    by (auto simp: complex_eq_iff cos_120 sin_120 cos_60 sin_60 cos_30 sin_30 cos_double sin_double cos_arcsin real_sqrt_divide
                   field_simps power2_eq_square sin_120' cos_120')
  hence "bad + rcis \<epsilon> (pi/2 - \<beta>) = cis (2*pi/3 - \<alpha>)"
    by (auto simp: rcis_def bad_def divide_conv_cnj \<alpha>_def \<beta>_def simp flip: cis_divide)
  thus "bad + rcis \<epsilon> (pi/2 - \<beta> + (if left then 2 * pi else 0)) = cis (2*pi/3 - \<alpha>)"
    unfolding rcis_def by (subst cis_mult [symmetric]) auto
qed

end


lemma detour_rel_avoid_linepath_circlepath_left:
  fixes a b c :: real
  assumes "y > sqrt 3 / 2" "a > pi / 2" "a < 2 * pi / 3"
  defines "bad \<equiv> cis (2 * pi / 3)"
  shows   "detour_rel {bad} {} (linepath (-1/2 + y *\<^sub>R \<i>) bad +++ part_circlepath 0 1 (2*pi/3) a)
             (avoid_linepath_circlepath True y a) (avoid_linepath_circlepath False y a)"
proof -
  define \<alpha> where "\<alpha> = (\<lambda>\<epsilon>. 2 * arcsin (\<epsilon>/2))"
  define \<beta> where "\<beta> = (\<lambda>\<epsilon>. pi / 3 + arcsin (\<epsilon> / 2))"
  define p where "p = linepath (-1/2 + y *\<^sub>R \<i>) bad +++ part_circlepath 0 1 (2*pi/3) a"
  define p1 where "p1 = (\<lambda>\<epsilon>. linepath (-1/2 + y *\<^sub>R \<i>) (bad + \<epsilon> *\<^sub>R \<i>))"
  define pm1 where "pm1 = (\<lambda>\<epsilon>. linepath (bad + \<epsilon> *\<^sub>R \<i>) bad)"
  define pm2 where "pm2 = (\<lambda>\<epsilon>. part_circlepath 0 1 (2*pi/3) (2*pi/3 - \<alpha> \<epsilon>))"
  define p2 where "p2 = (\<lambda>\<epsilon>. part_circlepath 0 1 (2*pi/3 - \<alpha> \<epsilon>) a)"
  define cl where "cl = (\<lambda>\<epsilon>. part_circlepath bad \<epsilon> (pi/2) (pi/2 - \<beta> \<epsilon>))"
  define cr where "cr = (\<lambda>\<epsilon>. part_circlepath bad \<epsilon> (pi/2) (pi/2 - \<beta> \<epsilon> + 2 * pi))"

  note [simp] = closed_segment_eq_real_ivl open_segment_eq_real_ivl closed_segment_same_Re
                sin_30 cos_30 sin_60 cos_60 sin_120 cos_120 sin_120' cos_120'
  have [simp]: "rcis 1 = cis"
    by (simp add: rcis_def fun_eq_iff)

  have "sin (pi - a) < sin (pi / 2)"
    by (subst sin_mono_less_eq) (use assms in auto)
  hence "sin a < 1"
    by simp
  have "sin (pi - a) > sin (pi / 3)"
    by (subst sin_mono_less_eq) (use assms in auto)
  hence "sin a > sqrt 3 / 2"
    by simp

  define eps where "eps = Min {1, y - sqrt 3 / 2, sin (pi / 3 - a / 2) * 2}"

  note [[goals_limit = 20]]
  have "detour_rel {bad} {} p (\<lambda>\<epsilon>. p1 \<epsilon> +++ cl \<epsilon> +++ p2 \<epsilon>) (\<lambda>\<epsilon>. p1 \<epsilon> +++ cr \<epsilon> +++ p2 \<epsilon>)"
    unfolding cl_def cr_def
  proof (rule detour_rel_avoid_basic_part_circlepath_left [where eps = eps])
    show "eps > 0"
      unfolding eps_def using assms by (auto intro!: sin_gt_zero)
  next
    show "bad \<in> path_image p - {pathstart p, pathfinish p}"
      using assms \<open>sin a > sqrt 3 / 2\<close>
      by (auto simp: p_def path_image_join rcis_def complex_eq_iff rcis_def exp_eq_polar)
  next
    fix \<epsilon> :: real
    assume "\<epsilon> > 0" "\<epsilon> < eps"
    hence \<epsilon>: "\<epsilon> > 0" "\<epsilon> < 1" "\<epsilon> < y - sqrt 3 / 2" "\<epsilon> < sin (pi / 3 - a / 2) * 2"
      unfolding eps_def by (auto simp: min_less_iff_disj)
    assume simple: "simple_path p"

    have "arcsin (\<epsilon> / 2) < arcsin (1 / 2)"
      using \<epsilon> by (intro arcsin_less_arcsin) auto
    hence arcsin: "arcsin (\<epsilon> / 2) > 0" "arcsin (\<epsilon> / 2) < pi / 6"
      using \<epsilon> by (auto intro!: arcsin_pos)

    have "arcsin (\<epsilon> / 2) < arcsin (sin (pi / 3 - a / 2))"
      using \<epsilon> by (intro arcsin_less_arcsin) (auto simp:)
    also have "\<dots> = pi / 3 - a / 2"
      using assms by (subst arcsin_sin) auto
    finally have \<alpha>: "\<alpha> \<epsilon> > 0" "a < 2 * pi / 3 - \<alpha> \<epsilon>"
      using assms \<epsilon> by (auto simp: \<alpha>_def intro!: arcsin_pos)

    have "(\<epsilon> / 2) ^ 2 \<le> (1 / 2) ^ 2"
      using \<epsilon> by (intro power_mono divide_right_mono) auto
    hence \<epsilon>': "(\<epsilon> / 2)\<^sup>2 < 1"
      by (simp add: power_divide)

    have "cis (pi * 13 / 6) = cis (pi / 6 + 2 * pi)"
      by (simp add: field_simps)
    also have "\<dots> = cis (pi / 6)"
      by (subst cis_mult [symmetric]) auto
    finally have [simp]: "cos (pi * 13 / 6) = sqrt 3 / 2" "sin (pi * 13 / 6) = 1/2"
      by (simp_all add: complex_eq_iff)

    have ends: "pathstart (p1 \<epsilon>) = -1 / 2 + of_real y * \<i>"
               "pathfinish (p1 \<epsilon>) = pathstart (pm1 \<epsilon>)"
               "pathfinish (pm1 \<epsilon>) = pathstart (pm2 \<epsilon>)"
               "pathfinish (pm2 \<epsilon>) = pathstart (p2 \<epsilon>)"
               "pathfinish (p2 \<epsilon>) = cis a"
               "pathstart (cl \<epsilon>) = pathfinish (p1 \<epsilon>)" "pathstart (cr \<epsilon>) = pathfinish (p1 \<epsilon>)"
               "pathfinish (cl \<epsilon>) = pathstart (p2 \<epsilon>)" "pathfinish (cr \<epsilon>) = pathstart (p2 \<epsilon>)"
            using \<epsilon> \<epsilon>'
      by (auto simp: complex_eq_iff \<alpha>_def \<beta>_def cos_double sin_double sin_arccos rcis_def
                     bad_def cos_diff sin_diff cos_arcsin divide_conv_cnj sin_add cos_add
                     algebra_simps power2_eq_square cl_def cr_def p1_def p2_def pm1_def pm2_def
                     rcis_def exp_eq_polar
               simp del: div_mult_self3 div_mult_self4 div_mult_self2 div_mult_self1)

    show eq: "p \<equiv>\<^sub>p p1 \<epsilon> +++ (pm1 \<epsilon> +++ pm2 \<epsilon>) +++ p2 \<epsilon>"
    proof -
      have "p \<equiv>\<^sub>p (p1 \<epsilon> +++ pm1 \<epsilon>) +++ (pm2 \<epsilon> +++ p2 \<epsilon>)"
        unfolding p_def p1_def p2_def pm1_def pm2_def using assms \<epsilon> \<epsilon>' \<alpha>
        by (intro eq_paths_join eq_paths_linepaths' eq_paths_part_circlepaths')
           (auto simp: complex_eq_iff rcis_def exp_eq_polar)
      also have "\<dots> \<equiv>\<^sub>p p1 \<epsilon> +++ (pm1 \<epsilon> +++ pm2 \<epsilon> +++ p2 \<epsilon>)"
        by (rule eq_paths_join_assoc1)
           (auto simp: pm1_def pm2_def p1_def p2_def bad_def rcis_def exp_eq_polar)
      also have "\<dots> \<equiv>\<^sub>p p1 \<epsilon> +++ (pm1 \<epsilon> +++ pm2 \<epsilon>) +++ p2 \<epsilon>"
        by (intro eq_paths_join eq_paths_join_assoc2)
           (auto simp: pm1_def pm2_def p1_def p2_def bad_def rcis_def exp_eq_polar)
      finally show ?thesis .
    qed

    show "pi / 2 \<noteq> pi / 2 - \<beta> \<epsilon> + 2 * pi \<and> \<bar>pi / 2 - \<beta> \<epsilon> + 2 * pi - pi / 2\<bar> < 2 * pi"
      using \<epsilon> \<epsilon>' arcsin by (auto simp: \<beta>_def abs_if)

    show "pi / 2 \<noteq> pi / 2 - \<beta> \<epsilon> \<and>
         \<bar>pi / 2 - \<beta> \<epsilon> - pi / 2\<bar> < 2 * pi \<and>
         cis (pi / 2) = cis (pi / 2) \<and>
         cis (pi / 2 - \<beta> \<epsilon>) = cis (pi / 2 - \<beta> \<epsilon> + 2 * pi) \<and>
         pi / 2 - \<beta> \<epsilon> + 2 * pi - pi / 2 + pi / 2 - (pi / 2 - \<beta> \<epsilon>) = 2 * pi"
      using arcsin unfolding cis_divide [symmetric] cis_mult [symmetric] by (auto simp add: \<beta>_def)

    show "pathfinish (p1 \<epsilon>) = bad + rcis \<epsilon> (pi / 2)"
         "pathstart (p2 \<epsilon>) = bad + rcis \<epsilon> (pi / 2 - \<beta> \<epsilon> + 2 * pi)"
         "pathstart (pm1 \<epsilon> +++ pm2 \<epsilon>) = pathfinish (p1 \<epsilon>)"
         "pathfinish (pm1 \<epsilon> +++ pm2 \<epsilon>) = pathstart (p2 \<epsilon>)"
      using ends unfolding cl_def cr_def by (simp_all add: rcis_def exp_eq_polar)

    show "path_image (p1 \<epsilon>) \<inter> path_image (p2 \<epsilon>) \<subseteq> {pathstart p} \<inter> {pathfinish p}"
    proof (intro subsetI; elim IntE)
      fix x assume x: "x \<in> path_image (p1 \<epsilon>)" "x \<in> path_image (p2 \<epsilon>)"
      have *: "Re x = -1/2" "Im x \<in> {sqrt 3 / 2 + \<epsilon>..y}"
        using \<epsilon> \<epsilon>' x(1) by (auto simp: p1_def bad_def)
      have "1 = (-1 / 2) ^ 2 + (sqrt 3 / 2) ^ 2"
        by (simp add: field_simps)
      also have "\<dots> < (-1 / 2) ^ 2 + (sqrt 3 / 2) ^ 2 + \<epsilon> ^ 2"
        using \<epsilon> by simp
      also have "\<dots> \<le> Re x ^ 2 + (sqrt 3 / 2) ^ 2 + 2 * \<epsilon> * (sqrt 3 / 2) + \<epsilon> ^ 2"
        using \<epsilon> * by simp
      also have "\<dots> = Re x ^ 2 + (sqrt 3 / 2 + \<epsilon>) ^ 2"
        by (simp add: power2_eq_square algebra_simps)
      also have "\<dots> \<le> Re x ^ 2 + Im x ^ 2"
        using \<epsilon> * by (intro add_left_mono power_mono) auto
      also have "\<dots> = norm x ^ 2"
        unfolding cmod_power2 ..
      also have "\<dots> = 1"
        using x(2) by (auto simp: p2_def path_image_part_circlepath')
      finally show "x \<in> {pathstart p} \<inter> {pathfinish p}"
        by simp
    qed

    show "does_not_cross (p1 \<epsilon>) (sphere bad \<epsilon>)"
    proof (subst does_not_cross_simple_path)
      show "path_image (p1 \<epsilon>) \<inter> sphere bad \<epsilon> \<subseteq> {pathstart (p1 \<epsilon>), pathfinish (p1 \<epsilon>)}"
      proof (intro subsetI; elim IntE)
        fix x assume x: "x \<in> path_image (p1 \<epsilon>)" "x \<in> sphere bad \<epsilon>"
        from x have "x = pathfinish (p1 \<epsilon>)"
          using \<epsilon> by (auto simp: p1_def dist_norm norm_complex_def complex_eq_iff bad_def)
        thus "x \<in> {pathstart (p1 \<epsilon>), pathfinish (p1 \<epsilon>)}"
          by blast
      qed
    qed (use \<epsilon> in \<open>auto simp: p1_def bad_def complex_eq_iff intro!: simple_path_linepath\<close>)

    show "does_not_cross (p2 \<epsilon>) (sphere bad \<epsilon>)"
    proof (subst does_not_cross_simple_path)
      show "path_image (p2 \<epsilon>) \<inter> sphere bad \<epsilon> \<subseteq> {pathstart (p2 \<epsilon>), pathfinish (p2 \<epsilon>)}"
      proof (intro subsetI; elim IntE)
        fix x assume x: "x \<in> path_image (p2 \<epsilon>)" "x \<in> sphere bad \<epsilon>"
        from x obtain t where t: "t \<in> {a..2 * pi / 3 - \<alpha> \<epsilon>}" "x = cis t"
          using \<alpha> by (auto simp: p2_def path_image_part_circlepath')
        have "[2 * pi / 3 = t + \<alpha> \<epsilon>] (rmod 2 * pi) \<or> [2 * pi / 3 = t - \<alpha> \<epsilon>] (rmod 2 * pi)"
          unfolding \<alpha>_def by (intro sphere_inter_sphere_aux2)
                             (use \<epsilon> x(2) t(2) in \<open>auto simp: bad_def dist_commute\<close>)
        hence "(2 * pi / 3 - t - \<alpha> \<epsilon>) rmod (2 * pi) = 0 \<or> (2 * pi / 3 - t + \<alpha> \<epsilon>) rmod (2 * pi) = 0"
          by (auto simp: rcong_conv_diff_rmod_eq_0 algebra_simps)
        also have "(2 * pi / 3 - t - \<alpha> \<epsilon>) rmod (2 * pi) = 2 * pi / 3 - t - \<alpha> \<epsilon>"
          using \<alpha> assms t(1) by (intro rmod_idem) auto
        also have "(2 * pi / 3 - t + \<alpha> \<epsilon>) rmod (2 * pi) = 2 * pi / 3 - t + \<alpha> \<epsilon>"
          using \<alpha> assms t(1) by (intro rmod_idem) auto
        finally have "t = 2 * pi / 3 + \<alpha> \<epsilon> \<or> t = 2 * pi / 3 - \<alpha> \<epsilon>"
          by (auto simp: algebra_simps)
        with t(1) assms \<alpha> have "t = 2 * pi / 3 - \<alpha> \<epsilon>"
          by auto
        hence "x = pathstart (p2 \<epsilon>)"
          using t by (auto simp: p2_def rcis_def exp_eq_polar)
        thus "x \<in> {pathstart (p2 \<epsilon>), pathfinish (p2 \<epsilon>)}"
          by blast
      qed
    next
      have "a + \<alpha> \<epsilon> \<ge> -4 / 3 * pi"
        unfolding \<alpha>_def using assms(2) arcsin(1) pi_gt3 by linarith
      thus "simple_path (p2 \<epsilon>)"
        unfolding p2_def using \<alpha> \<epsilon>
        by (subst simple_path_part_circlepath) (auto simp: abs_if)
    qed

    show "does_not_cross (pm1 \<epsilon> +++ pm2 \<epsilon>) (sphere bad \<epsilon>)"
    proof (subst does_not_cross_simple_path)
      show "path_image (pm1 \<epsilon> +++ pm2 \<epsilon>) \<inter> sphere bad \<epsilon> \<subseteq>
              {pathstart (pm1 \<epsilon> +++ pm2 \<epsilon>), pathfinish (pm1 \<epsilon> +++ pm2 \<epsilon>)}"
      proof (intro subsetI; elim IntE)
        fix x assume x: "x \<in> path_image (pm1 \<epsilon> +++ pm2 \<epsilon>)" "x \<in> sphere bad \<epsilon>"
        hence "x \<in> path_image (pm1 \<epsilon>) \<union> path_image (pm2 \<epsilon>)"
          by (subst (asm) path_image_join) (auto simp: pm1_def pm2_def bad_def rcis_def exp_eq_polar)
        thus "x \<in> {pathstart (pm1 \<epsilon> +++ pm2 \<epsilon>), pathfinish (pm1 \<epsilon> +++ pm2 \<epsilon>)}"
        proof
          assume "x \<in> path_image (pm1 \<epsilon>)"
          hence x: "Re x = Re bad" "Im x \<in> {Im bad..Im bad + \<epsilon>}"
            using \<epsilon> by (auto simp: pm1_def )
          have "Im x = Im bad + dist x bad"
            using x by (auto simp: dist_norm norm_complex_def)
          also have "dist x bad = \<epsilon>"
            using \<open>x \<in> sphere bad \<epsilon>\<close> by (auto simp: dist_commute)
          finally show ?thesis using x
            by (auto simp: complex_eq_iff pm1_def)
        next
          assume "x \<in> path_image (pm2 \<epsilon>)"
          then obtain t where t: "t \<in> {2*pi/3 - \<alpha> \<epsilon>..2*pi/3}" "x = cis t"
            unfolding pm2_def path_image_part_circlepath' using \<alpha> by auto
          have "t = 2 * pi / 3 - \<alpha> \<epsilon>"
          proof (rule ccontr)
            assume "t \<noteq> 2 * pi / 3 - \<alpha> \<epsilon>"
            with t(1) have t': "t \<in> {2*pi/3 - \<alpha> \<epsilon><..2*pi/3}"
              by auto
            have "[2 * pi / 3 = t + \<alpha> \<epsilon>] (rmod 2 * pi) \<or> [2 * pi / 3 = t - \<alpha> \<epsilon>] (rmod 2 * pi)"
              unfolding \<alpha>_def by (intro sphere_inter_sphere_aux2)
                                 (use \<epsilon> x(2) t(2) in \<open>auto simp: bad_def dist_commute\<close>)
            hence "(2 * pi / 3 - t - \<alpha> \<epsilon>) rmod (2 * pi) = 0 \<or> (2 * pi / 3 - t + \<alpha> \<epsilon>) rmod (2 * pi) = 0"
              by (auto simp: rcong_conv_diff_rmod_eq_0 algebra_simps)
            also have "(2 * pi / 3 - t - \<alpha> \<epsilon>) rmod (2 * pi) = 8 * pi / 3 - t - \<alpha> \<epsilon>"
              using \<alpha> assms t(1) t'
              by (intro rmod_unique[where n = "-1"]) (auto simp: algebra_simps) 
            also have "(2 * pi / 3 - t + \<alpha> \<epsilon>) rmod (2 * pi) = 2 * pi / 3 - t + \<alpha> \<epsilon>"
              using \<alpha> assms t(1) by (intro rmod_idem) auto
            finally have "t = 2 * pi / 3 + \<alpha> \<epsilon> \<or> t = 8 * pi / 3 - \<alpha> \<epsilon>"
              by (auto simp: algebra_simps)
            with t' t(1) \<alpha> assms show False
              by auto
          qed
          thus ?thesis using t
            by (auto simp: pm2_def rcis_def exp_eq_polar)
        qed
      qed
    next
      have "pm1 \<epsilon> +++ pm2 \<epsilon> \<le>\<^sub>p (pm1 \<epsilon> +++ pm2 \<epsilon>) +++ p2 \<epsilon>"
        by (rule is_subpath_joinI1) (auto simp: pm1_def pm2_def p2_def bad_def rcis_def exp_eq_polar)
      also have "\<dots> \<le>\<^sub>p p1 \<epsilon> +++ (pm1 \<epsilon> +++ pm2 \<epsilon>) +++ p2 \<epsilon>"
        by (rule is_subpath_joinI2)
           (auto simp: p1_def pm1_def pm2_def p2_def bad_def rcis_def exp_eq_polar)
      also have "\<dots> \<equiv>\<^sub>p p"
        using eq by (simp add: eq_paths_sym_iff)
      finally show "simple_path (pm1 \<epsilon> +++ pm2 \<epsilon>)"
      using simple subpath_imp_simple_path by blast
    qed
  qed (auto simp: p1_def p2_def)
  thus ?thesis
    by (simp add: p_def p1_def cl_def p2_def avoid_linepath_circlepath_def [abs_def]
                  Let_def bad_def \<alpha>_def \<beta>_def cr_def)
qed

lemmas detour_rel_avoid_linepath_circlepath_right =
  detour_rel_swap[OF detour_rel_avoid_linepath_circlepath_left]


subsection \<open>Consequences of the detour relation\<close>

locale detour =
  aux: detour_rel_aux_locale \<epsilon> "I \<union> X" p p'
  for \<epsilon> :: real and I X P :: "complex set" and p_orig p p' :: "real \<Rightarrow> complex" +
  assumes eq_loops: "eq_loops p_orig p"
  assumes simple_loop_original: "simple_loop p_orig"
  assumes same_orientation': "simple_loop_orientation p' = simple_loop_orientation p"
  assumes I_inside:  "I \<subseteq> inside (path_image p')"
  assumes X_outside: "X \<subseteq> outside (path_image p')"
  assumes disjoint:  "P \<inter> (path_image p_orig \<union> (\<Union>x\<in>I\<union>X. cball x \<epsilon>)) = {}"
begin

lemma same_orientation: "simple_loop_orientation p' = simple_loop_orientation p_orig"
  using same_orientation' eq_loops_imp_same_orientation [OF eq_loops] by simp

text \<open>
  \<open>p'\<close> is a simple loop that can be obtained from \<open>p\<close> through local deformations in
  \<open>\<epsilon>\<close>-neighbourhoods of \<open>I \<union> X\<close>.
\<close>

lemma same_ends: "pathstart p' = pathstart p" "pathfinish p' = pathfinish p"
  by simp_all

lemmas valid = aux.p'_valid

lemma simple_loop: "simple_loop p'"
  by (metis local.same_orientation simple_loop_orientation_eq_0_iff simple_loop_original)

lemma path_image_eq [simp]: "path_image p = path_image p_orig"
  by (rule sym, rule eq_loops_imp_path_image_eq, rule eq_loops)

lemma homotopic': "homotopic_paths (path_image p_orig \<union> (\<Union>x\<in>I \<union> X. cball x \<epsilon>)) p p'"
  using aux.homotopic by simp

lemma homotopic'': "homotopic_loops (path_image p_orig \<union> (\<Union>x\<in>I \<union> X. cball x \<epsilon>)) p p'"
  by (intro homotopic_paths_imp_homotopic_loops homotopic')
     (use same_ends eq_loops in \<open>auto dest: eq_loops_imp_loop\<close>)

lemma homotopic: "homotopic_loops (path_image p_orig \<union> (\<Union>x\<in>I \<union> X. cball x \<epsilon>)) p_orig p'"
proof -
  have "homotopic_loops (path_image p_orig \<union> (\<Union>x\<in>I \<union> X. cball x \<epsilon>)) p_orig p"
    by (intro eq_loops_imp_homotopic [OF eq_loops]) auto
  with homotopic'' show ?thesis
    using homotopic_loops_trans by blast
qed
    
  



lemma path_image_subset: "path_image p' \<subseteq> path_image p_orig \<union> (\<Union>x\<in>I\<union>X. cball x \<epsilon>)"
  using aux.path_image_p' by simp

text \<open>
  All the points in \<open>I\<close> are strictly inside \<open>p'\<close>, all the points in \<open>X\<close> are strictly outside,
  and all the points in \<open>P\<close> are unchanged (i.e.\ if they were outside before they still are and
  if they were inside before, they still are).
\<close>
lemma I_not_on_path: "I \<inter> path_image p' = {}"
  using aux.X_disjoint by blast

lemma X_not_on_path: "X \<inter> path_image p' = {}"
  using aux.X_disjoint by blast

lemma P_not_on_path: "P \<inter> path_image p' = {}"
  using disjoint aux.path_image_p' by auto

lemma I_X_disjoint: "I \<inter> X = {}"
proof -
  have "inside (path_image p') \<inter> outside (path_image p') = {}"
    using simple_loop by simp
  thus ?thesis
    using I_inside X_outside by blast
qed

lemma I_P_disjoint: "I \<inter> P = {}"
  using path_image_eq aux.X_subset disjoint path_image_subset by blast

lemma X_P_disjoint: "X \<inter> P = {}"
  using path_image_eq aux.X_subset disjoint path_image_subset by blast

lemma winding_number_unchanged:
  assumes "z \<in> P"
  shows   "winding_number p' z = winding_number p_orig z"
  using disjoint aux.winding_number_unchanged[of z]
        eq_loops_imp_winding_number_eq [OF eq_loops, of z] assms by (auto simp: disjoint_iff)

lemma P_inside_iff:
  assumes "z \<in> P"
  shows   "z \<in> inside (path_image p') \<longleftrightarrow> z \<in> inside (path_image p_orig)"
proof -
  from assms have [simp]: "z \<notin> path_image p_orig" "z \<notin> path_image p'"
    using disjoint P_not_on_path by auto
  show ?thesis
    using winding_number_unchanged [OF assms] simple_loop simple_loop_original
    by (simp add: inside_simple_loop_iff)
qed

lemma P_outside_iff:
  assumes "z \<in> P"
  shows   "z \<in> outside (path_image p') \<longleftrightarrow> z \<in> outside (path_image p_orig)"
proof -
  from assms have [simp]: "z \<notin> path_image p_orig" "z \<notin> path_image p'"
    using disjoint P_not_on_path by auto
  show ?thesis
    using winding_number_unchanged [OF assms] simple_loop simple_loop_original
    by (simp add: outside_simple_loop_iff)
qed

lemma winding_number_I:
  assumes "z \<in> I"
  shows   "winding_number p' z = simple_loop_orientation p_orig"
  using assms I_inside same_orientation simple_loop simple_loop_winding_number_cases
        same_orientation' by auto

lemma winding_number_X:
  assumes "z \<in> X"
  shows   "winding_number p' z = 0"
  using assms X_outside
  by (metis aux.p'_path simple_loop simple_loop_def subsetD winding_number_zero_in_outside)

end


text \<open>
  Our final result: If \<open>p\<close> is a simple closed curve that is in detour relation with
  a family of deformed versions \<open>p'\<close> of itself, then for any closed set \<open>P\<close> of points
  of interest not on \<open>p\<close> there is an \<open>\<epsilon> > 0\<close> such that all curves \<open>p'(\<epsilon>)\<close> for \<open>\<epsilon>' < \<epsilon>\<close>
  have basically the same properties as \<open>p\<close>; namely:

    \<^item> \<open>p'(\<epsilon>)\<close> is \<open>pr(\<epsilon>)\<close> also a closed curve with the same orientation and the same
      start/end as \<open>p\<close>.

    \<^item> \<open>p'(\<epsilon>)\<close> is homotopic to \<open>p\<close> with a homotopy transformation that only passes through the
      original path image of \<open>p\<close> plus \<open>\<epsilon>\<close>-balls around \<open>I \<union> X\<close>. In other words, \<open>p\<close> is
      identical to \<open>p'(\<epsilon>)\<close> except for small deformations of size \<open>\<epsilon>\<close> around \<open>I \<union> X\<close>.

    \<^item> All points in \<open>I\<close> (``include'') are inside \<open>p'(\<epsilon>)\<close> and all points in \<open>X\<close> (``exclude'')
      are outside.      

    \<^item> Each point in \<open>P\<close> (``preserve'') is in \<open>p'(\<epsilon>)\<close> if and only if it was already in \<open>p\<close>.
\<close>
theorem detour_generic:
  assumes rel: "detour_rel I X p pl pr"
  assumes eq: "eq_loops p_orig p"
  assumes p_orig: "simple_loop p_orig" and valid: "valid_path p"
  assumes P: "closed P" "P \<inter> path_image p_orig = {}"
  defines "p' \<equiv> (if simple_loop_ccw p_orig then pr else pl)"
  shows   "eventually (\<lambda>\<epsilon>. detour \<epsilon> I X P p_orig p (p' \<epsilon>)) (at_right 0)"
proof -
  have [simp, intro]: "path p_orig"
    using p_orig by (auto simp: simple_loop_def simple_path_imp_path)
  note [simp] = simple_loop_ccw_conv_cw[OF p_orig]
  note [simp] = eq_loops_imp_path_image_eq [OF eq]
  have p: "simple_loop p"
    using p_orig eq_loops_imp_simple_loop_iff [OF eq] by simp
  hence [simp, intro]: "path p"
    by (auto simp: simple_loop_def simple_path_imp_path)
  from rel p valid have ev1: "eventually (\<lambda>\<epsilon>. detour_rel_locale \<epsilon> I X p (pl \<epsilon>) (pr \<epsilon>)) (at_right 0)"
    by (auto simp: detour_rel_def simple_loop_def)
  then obtain eps0 where "detour_rel_locale eps0 I X p (pl eps0) (pr eps0)"
    by fastforce
  then interpret eps0: detour_rel_locale eps0 I X p "pl eps0" "pr eps0" .

  obtain z0 where z0: "z0 \<in> inside (path_image p)"
    using p by (metis simple_closed_path_wn3 simple_loop_def)
  define P' where "P' = insert z0 P"
  have P': "closed P'" "P' \<inter> (path_image p \<union> (I \<union> X)) = {}" "z0 \<in> P'"
    using P eps0.pl.X_subset z0 inside_no_overlap[of "path_image p"]
    by (auto simp: P'_def simp del: inside_no_overlap)

  have "compact (path_image p \<inter> (I \<union> X))"
    by (intro compact_Int_closed compact_path_image) auto
  also have "path_image p \<inter> (I \<union> X) = I \<union> X"
    by auto
  finally have "compact (I \<union> X)" .
  with P' have ev2: "eventually (\<lambda>\<epsilon>. setdist_gt \<epsilon> (I \<union> X) P') (at_right 0)"
    by (intro compact_closed_imp_eventually_setdist_gt_at_right_0) auto

  show ?thesis
    using ev1 ev2
  proof eventually_elim
    case (elim \<epsilon>)
    interpret detour_rel_locale \<epsilon> I X p "pl \<epsilon>" "pr \<epsilon>"
      by (rule elim)
    have disjoint: "P' \<inter> (path_image p \<union> (\<Union>x\<in>I\<union>X. cball x \<epsilon>)) = {}"
    proof (intro equalityI subsetI, elim IntE UnE)
      fix x assume x: "x \<in> P'" "x \<in> (\<Union>x\<in>I\<union>X. cball x \<epsilon>)"
      then obtain y where y: "y \<in> I \<union> X" "dist y x \<le> \<epsilon>"
        by auto
      moreover from y(1) x(1) have "dist y x > \<epsilon>"
        by (rule setdist_gtD[OF elim(2)])
      ultimately show "x \<in> {}"
        by simp
    qed (use P' in auto)
      
    interpret detour_rel_loop \<epsilon> I X p "pl \<epsilon>" "pr \<epsilon>"
    proof
      show "simple_loop p"
        by fact
    next
      have "z0 \<notin> path_image p \<union> (\<Union>x\<in>I\<union>X. cball x \<epsilon>)"
        using disjoint P' by blast
      moreover from this have "winding_number p z0 \<noteq> 0"
        using p z0 by (simp add: simple_loop_winding_number_cases)
      ultimately show "\<exists>z. winding_number p z \<noteq> 0 \<and> z \<notin> path_image p \<union> (\<Union>x\<in>I\<union>X. cball x \<epsilon>)"
        using z0 P' by (intro exI[of _ z0]) auto
    qed
    note [[goals_limit = 30]]
    show ?case
    proof
      show "\<epsilon> > 0" "simple_path (p' \<epsilon>)" "simple_loop p_orig"
        using \<epsilon>_pos p_orig by (auto simp: p'_def simple_loop_def)
      show "I \<union> X \<subseteq> path_image p" "(I \<union> X) \<inter> path_image (p' \<epsilon>) = {}"
           "homotopic_paths (path_image p \<union> (\<Union>x\<in>I \<union> X. cball x \<epsilon>)) p (p' \<epsilon>)"
        using pl.homotopic pr.homotopic pl.X_disjoint pr.X_disjoint pl.X_subset
        unfolding p'_def by (simp_all add: Un_commute)
      show "simple_loop_orientation (p' \<epsilon>) = simple_loop_orientation p"
        unfolding p'_def by (simp add: same_orientation)
      show "P \<inter> (path_image p_orig \<union> (\<Union>x\<in>I \<union> X. cball x \<epsilon>)) = {}"
        using disjoint unfolding P'_def by auto
      show "I \<subseteq> inside (path_image (p' \<epsilon>))"
        unfolding p'_def using inside_pl_L_iff inside_pr_L_iff
        using eq eq_loops_imp_ccw_iff eq_loops_imp_cw_iff by fastforce
      show "X \<subseteq> outside (path_image (p' \<epsilon>))"
      proof
        fix x assume x: "x \<in> X"
        hence "x \<notin> path_image (p' \<epsilon>)"
          unfolding p'_def by auto
        moreover have "x \<notin> inside (path_image (p' \<epsilon>))"
          using x inside_pl_R_iff inside_pr_R_iff unfolding p'_def
          using eq eq_loops_imp_ccw_iff eq_loops_imp_cw_iff by fastforce
        ultimately show "x \<in> outside (path_image (p' \<epsilon>))"
          by (simp add: inside_outside)
      qed
      show "valid_path (p' \<epsilon>)"
        using p'_def pl.p'_valid pr.p'_valid by simp
    qed fact+
  qed
qed

corollary detour_ccw:
  assumes "detour_rel I X p pl pr" "p_orig \<equiv>\<^sub>\<circle> p"
  assumes "simple_loop_ccw p_orig" "valid_path p"
  assumes "closed P" "P \<inter> path_image p_orig = {}"
  shows   "eventually (\<lambda>\<epsilon>. detour \<epsilon> I X P p_orig p (pr \<epsilon>)) (at_right 0)"
  using detour_generic[OF assms(1), of p_orig P] assms by (auto simp: simple_loop_ccw_def)

corollary detour_cw:
  assumes "detour_rel I X p pl pr" "p_orig \<equiv>\<^sub>\<circle> p"
  assumes "simple_loop_cw p_orig" "valid_path p" "closed P" "P \<inter> path_image p_orig = {}"
  shows   "eventually (\<lambda>\<epsilon>. detour \<epsilon> I X P p_orig p (pl \<epsilon>)) (at_right 0)"
proof -
  from assms(3) have "\<not>simple_loop_ccw p_orig"
    using simple_path_not_cw_and_ccw by blast
  moreover have "simple_loop p_orig"
    using assms(3) by (auto simp: simple_loop_cw_def)
  ultimately show ?thesis
    using detour_generic[OF assms(1), of p_orig P] assms by simp
qed

end
