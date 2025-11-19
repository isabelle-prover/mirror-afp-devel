\<^marker>\<open>creator "Niklas Krofta"\<close>
section \<open>Matrix groups\<close>
theory Matrix_Group
  imports 
    "Topological_Group" 
    "Topological_Group_Examples"
    "HOL-Analysis.Determinants"
begin

paragraph \<open>Summary\<close>
text \<open>
  In this section we define the general linear group and some of its subgroups.
  We also introduce topologies on vector types and use them to prove the aforementioned groups
  to be topological groups.
\<close>

subsection \<open>Topologies on vector types\<close>

definition vec_topology :: "'a topology \<Rightarrow> ('a^'n) topology" where 
"vec_topology T = quot_topology (product_topology (\<lambda>i. T) UNIV) vec_lambda"

lemma producttop_vectop_homeo:
  shows "homeomorphic_map (product_topology (\<lambda>i. T) UNIV) (vec_topology T) vec_lambda"
proof -
  have "inj_on vec_lambda (topspace (product_topology (\<lambda>i. T) UNIV))" unfolding inj_on_def by force
  then show ?thesis unfolding vec_topology_def 
    using injective_quotient_map_homeo[OF projection_quotient_map] by blast
qed

lemma homeo_inverse_homeo:
  assumes homeo: "homeomorphic_map X Y f" and fg_id: "\<forall>y \<in> topspace Y. f (g y) = y" and
    g_image: "\<forall>y \<in> topspace Y. g y \<in> topspace X"
  shows "homeomorphic_map Y X g"
proof -
  from homeo obtain h where 
    h_homeo: "homeomorphic_map Y X h" and hf_id: "(\<forall>x \<in> topspace X. h (f x) = x)"
    by (smt (verit) homeomorphic_map_maps homeomorphic_maps_map)
  have "g y = h y" if "y \<in> topspace Y" for y
  proof -
    have "g y = h (f (g y))" using hf_id that g_image by fastforce
    then show ?thesis using fg_id that by simp
  qed
  then show ?thesis using homeomorphic_map_eq[OF h_homeo] by presburger
qed

lemma vectop_producttop_homeo:
  shows "homeomorphic_map (vec_topology T) (product_topology (\<lambda>i. T) UNIV) vec_nth"
proof -
  let ?T' = "product_topology (\<lambda>i. T) UNIV"
  have "vec_lambda (vec_nth v) = v" for v :: "'a^'n" by simp
  moreover have "vec_nth v \<in> topspace ?T'" if "v \<in> topspace (vec_topology T)" for v :: "'a^'n"
  proof -
    have "\<exists>f \<in> topspace ?T'. v = vec_lambda f" using that 
      unfolding vec_topology_def topspace_quot_topology image_def by fast
    then show ?thesis by fastforce
  qed
  ultimately show ?thesis using homeo_inverse_homeo[OF producttop_vectop_homeo] by blast
qed

lemma vec_topology_euclidean [simp]:
  defines "T :: ('a :: topological_space) topology \<equiv> euclidean"
  defines "T\<^sub>v\<^sub>e\<^sub>c :: ('a^'n) topology \<equiv> euclidean"
  shows "vec_topology T = T\<^sub>v\<^sub>e\<^sub>c"
proof -
  have "openin (vec_topology T) U" if "openin T\<^sub>v\<^sub>e\<^sub>c U" for U
  proof -
    have hU: "open U" using open_openin that unfolding T\<^sub>v\<^sub>e\<^sub>c_def by blast
    have "\<exists>U'. openin (vec_topology T) U' \<and> x \<in> U' \<and> U' \<subseteq> U" if "x \<in> U" for x
    proof -
      from that hU obtain V :: "'n \<Rightarrow> 'a set" where 
        hV: "(\<forall>i. open (V i) \<and> x$i \<in> V i) \<and> (\<forall>y. (\<forall>i. y$i \<in> V i) \<longrightarrow> y \<in> U)" unfolding open_vec_def by force
      let ?W = "\<Pi>\<^sub>E i\<in>UNIV. V i"
      from hV have "openin T (V i)" for i using open_openin unfolding T_def by blast
      then have "openin (product_topology (\<lambda>i. T) UNIV) ?W" by (simp add: openin_PiE)
      then have is_open: "openin (vec_topology T) (vec_lambda`?W)" 
        using producttop_vectop_homeo homeomorphic_map_openness openin_subset by metis
      have "vec_nth x \<in> ?W" using hV by fast
      then have contains_x: "x \<in> (vec_lambda`?W)" unfolding image_def by force
      have "y \<in> U" if "vec_nth y \<in> ?W" for y
      proof -
        from that have "y$i \<in> V i" for i by fast
        then show ?thesis using hV by blast
      qed
      then have "(vec_lambda`?W) \<subseteq> U" by force
      then show ?thesis using contains_x is_open by meson                                                              
    qed
    then show ?thesis by (meson openin_subopen)
  qed
  moreover have "openin T\<^sub>v\<^sub>e\<^sub>c U" if "openin (vec_topology T) U" for U
  proof -
    from that have hU: "openin (product_topology (\<lambda>i. T) UNIV) (vec_nth`U)"
      using vectop_producttop_homeo homeomorphic_map_openness openin_subset by metis
    have "\<exists>V. (\<forall>i. open (V i) \<and> x $ i \<in> V i) \<and> (\<forall>y. (\<forall>i. y $ i \<in> V i) \<longrightarrow> y \<in> U)" if "x \<in> U" for x
    proof -
      from that have "vec_nth x \<in> (vec_nth`U)" unfolding image_def by blast
      then obtain V :: "'n \<Rightarrow> 'a set" 
        where hV: "(\<forall>i. openin T (V i)) \<and> vec_nth x \<in> (\<Pi>\<^sub>E i\<in>UNIV. V i) \<and> (\<Pi>\<^sub>E i\<in>UNIV. V i) \<subseteq> (vec_nth`U)"
        using hU product_topology_open_contains_basis by (metis (no_types, lifting))
      then have "open (V i) \<and> x$i \<in> V i" for i unfolding T_def using open_openin by fast
      moreover have "y \<in> U" if "\<forall>i. y$i \<in> V i" for y
      proof -
        have "vec_nth y \<in> (\<Pi>\<^sub>E i\<in>UNIV. V i)" using that by blast
        then show ?thesis using hV by (metis image_iff in_mono vec_nth_inject)
      qed
      ultimately show ?thesis by blast
    qed
    then have "open U" unfolding open_vec_def by blast
    then show ?thesis unfolding T\<^sub>v\<^sub>e\<^sub>c_def using open_openin by blast
  qed
  ultimately show ?thesis using topology_eq by meson
qed

lemma vec_projection_continuous:
  shows "continuous_map (vec_topology T) T (\<lambda>v. v$i)"
  using homeomorphic_imp_continuous_map[OF vectop_producttop_homeo] by fast

lemma vec_components_continuous_imp_continuous:
  fixes f :: "'x \<Rightarrow> 'a^'n"
  assumes "\<forall>i. continuous_map X T (\<lambda>x. (f x) $ i)"
  shows "continuous_map X (vec_topology T) f"
proof -
  have "continuous_map X (product_topology (\<lambda>i. T) UNIV) (vec_nth \<circ> f)" using assms by auto
  moreover have "f = vec_lambda \<circ> (vec_nth \<circ> f)" by fastforce
  ultimately show ?thesis using continuous_map_compose 
      homeomorphic_imp_continuous_map[OF producttop_vectop_homeo] by fastforce
qed

definition matrix_topology :: "'a topology \<Rightarrow> ('a^'n^'m) topology" where
"matrix_topology T = vec_topology (vec_topology T)"

lemma matrix_topology_euclidean[simp]:
  shows "matrix_topology euclidean = euclidean"
  unfolding matrix_topology_def by simp

lemma matrix_projection_continuous:
  shows "continuous_map (matrix_topology T) T (\<lambda>A. A$i$j)"
proof -
  have "(\<lambda>A. A$i$j) = (\<lambda>x. x$j) \<circ> (\<lambda>A. A$i)" by fastforce
  then show ?thesis unfolding matrix_topology_def 
    using vec_projection_continuous continuous_map_compose by metis
qed

lemma matrix_components_continuous_imp_continuous:
  fixes f :: "'x \<Rightarrow> 'a^'n^'m"
  assumes "\<And>i j. continuous_map X T (\<lambda>x. (f x) $ i $ j)"
  shows "continuous_map X (matrix_topology T) f"
  unfolding matrix_topology_def using vec_components_continuous_imp_continuous assms by metis

subsection \<open>The general linear group as a topological group\<close>

definition GL :: "(('a :: field)^'n^'n) monoid" where
"GL = \<lparr>carrier = {A. invertible A}, monoid.mult = (**), one = mat 1\<rparr>"

definition GL_topology :: "(real^'n^'n) topology" where
"GL_topology = subtopology euclidean (carrier GL)"

lemma topspace_GL: "topspace GL_topology = {A. invertible A}"
  unfolding GL_topology_def topspace_subtopology GL_def by simp

subsubsection \<open>Continuity of matrix operations\<close>

lemma det_continuous:
  defines "T :: (real^'n^'n) topology \<equiv> euclidean"
  shows "continuous_map T euclideanreal det"
proof -
  let ?T' = "matrix_topology euclideanreal"
  let ?S = "{\<pi>. \<pi> permutes (UNIV :: 'n set)}"
  have S_finite: "finite ?S" by simp
  have "finite (UNIV :: 'n set)" by simp
  then have "continuous_map ?T' euclideanreal (\<lambda>A. \<Prod> i \<in> (UNIV :: 'n set). (A $ i $ \<pi> i))" 
    for \<pi> :: "'n \<Rightarrow> 'n" using continuous_map_prod[OF _ matrix_projection_continuous] by fast
  then have "continuous_map ?T' euclideanreal (\<lambda>A. of_int (sign \<pi>) * (\<Prod> i \<in> (UNIV :: 'n set). (A $ i $ \<pi> i)))"
    for \<pi> :: "'n \<Rightarrow> 'n" using continuous_map_real_mult_left by fast
  from continuous_map_sum[OF S_finite this] have "continuous_map ?T' euclideanreal
    (\<lambda>A. \<Sum> \<pi>\<in>?S. of_int (sign \<pi>) * (\<Prod> i \<in> (UNIV :: 'n set). A $ i $ \<pi> i))" by fast
  then show ?thesis unfolding T_def matrix_topology_euclidean det_def by force
qed

lemma matrix_mul_continuous:
  defines "T1 :: (real^'n^'m) topology \<equiv> euclidean"
  defines "T2 :: (real^'r^'n) topology \<equiv> euclidean"
  defines "T3 :: (real^'r^'m) topology \<equiv> euclidean"
  shows "continuous_map (prod_topology T1 T2) T3 (\<lambda>(A,B). A ** B)"
proof -
  let ?T = "prod_topology T1 T2"
  have "continuous_map ?T euclideanreal (\<lambda>AB. (fst AB ** snd AB) $ i $ j)" for i :: 'm and j :: 'r
  proof -
    have eq: "(\<lambda>AB. (fst AB ** snd AB) $ i $ j) = (\<lambda>AB. (\<Sum>(k::'n)\<in>UNIV. fst AB $ i $ k * snd AB $ k $ j))"
      unfolding matrix_matrix_mult_def by auto
    have 
      comp1: "(\<lambda>AB. fst AB $ i $ k) = (\<lambda>A. A$i$k) \<circ> fst" and 
      comp2: "(\<lambda>AB. snd AB $ k $ j) = (\<lambda>B. B$k$j) \<circ> snd"
      for k :: 'n by auto
    from comp1 have "continuous_map ?T euclideanreal (\<lambda>AB. fst AB $ i $ k)" for k :: 'n
      unfolding T1_def matrix_topology_euclidean[symmetric]
      using continuous_map_compose[OF continuous_map_fst matrix_projection_continuous] by metis
    moreover from comp2 have "continuous_map ?T euclideanreal (\<lambda>AB. snd AB $ k $ j)" for k :: 'n
      unfolding T2_def matrix_topology_euclidean[symmetric]
      using continuous_map_compose[OF continuous_map_snd matrix_projection_continuous] by metis
    ultimately have summand_continuous: 
      "continuous_map ?T euclideanreal (\<lambda>AB. fst AB $ i $ k * snd AB $ k $ j)" for k :: 'n
      using continuous_map_real_mult by blast
    have finite: "finite (UNIV :: 'n set)" by simp
    have "continuous_map ?T euclideanreal (\<lambda>AB. (\<Sum>(k::'n)\<in>UNIV. fst AB $ i $ k * snd AB $ k $ j))"
      using continuous_map_sum[OF finite summand_continuous] by fast
    then show ?thesis unfolding eq by blast
  qed
  from matrix_components_continuous_imp_continuous[OF this] show ?thesis
    unfolding T3_def matrix_topology_euclidean[symmetric] by (simp add: case_prod_beta')
qed

lemma transpose_continuous:
  shows "continuous_map (euclidean :: (('a :: topological_space)^'n^'m) topology) euclidean transpose"
proof -
  have "continuous_map euclidean euclidean (\<lambda>A. (transpose A) $ i $ j)" for i :: 'n and j :: 'm
    unfolding transpose_def matrix_topology_euclidean[symmetric] 
    using matrix_projection_continuous[of euclidean j i] by fastforce
  from matrix_components_continuous_imp_continuous[OF this] show ?thesis 
    unfolding matrix_topology_euclidean by blast
qed

subsubsection \<open>Continuity of matrix inversion\<close>

lemma matrix_mul_columns:
  fixes A :: "('a :: semiring_1)^'n^'m" and B :: "'a^'k^'n"
  shows "column j (A ** B) = A *v (column j B)"
  unfolding column_def matrix_matrix_mult_def matrix_vector_mult_def by force

lemma matrix_columns_unique:
  assumes "\<forall>j. column j A = column j B"
  shows "A = B"
  using assms unfolding column_def by (simp add: vec_eq_iff)

lemma matrix_inv_is_inv:
  assumes "invertible A"
  shows "A ** (matrix_inv A) = mat 1" and "(matrix_inv A) ** A = mat 1"  
proof -
  show "A ** matrix_inv A = mat 1" 
    using assms unfolding invertible_def matrix_inv_def by (simp add: verit_sko_ex')
  show "(matrix_inv A) ** A = mat 1" 
    using assms unfolding invertible_def matrix_inv_def by (simp add: verit_sko_ex')
qed

lemma invertible_imp_right_inverse_is_inverse:
  assumes invertible: "invertible A" and "A ** B = mat 1"
  shows "matrix_inv A = B"
  using matrix_inv_is_inv[OF invertible] assms by (metis matrix_mul_assoc matrix_mul_lid)

lemma matrix_inv_invertible:
  assumes "invertible A"
  shows "invertible (matrix_inv A)"
  using assms matrix_inv_is_inv invertible_def by fast

lemma det_inv:
  fixes A :: "('a :: field)^'n^'n"
  assumes "det A \<noteq> 0"
  shows "det (matrix_inv A) = 1 / det A"
proof -
  have "A ** (matrix_inv A) = mat 1" using assms invertible_det_nz matrix_inv_is_inv(1) by fast
  then have "det A * det (matrix_inv A) = 1" using det_mul[of A "matrix_inv A"] by auto
  then show ?thesis using assms by (metis nonzero_mult_div_cancel_left)
qed

text \<open>See proposition "cramer" from HOL-Analysis.Determinants\<close>
definition cramer_inv :: "('a :: field)^'n^'n \<Rightarrow> 'a^'n^'n" where 
"cramer_inv A = (\<chi> i j. det(\<chi> k l. if l = i then (axis j 1) $ k else A$k$l) / det A)"

lemma cramer_inv_is_inverse:
  assumes invertible: "invertible (A :: ('a :: field)^'n^'n)"
  shows "matrix_inv A = cramer_inv A"
proof -
  have "A ** (cramer_inv A) = mat 1"
  proof -
    have "column j (cramer_inv A) = (\<chi> i. det(\<chi> k l. if l = i then (axis j 1) $ k else A$k$l) / det A)" for j 
      unfolding cramer_inv_def column_def by simp
    moreover have "det A \<noteq> 0" using invertible unfolding invertible_det_nz by force
    ultimately have "A *v (column j (cramer_inv A)) = axis j 1" for j using cramer by auto
    then have "column j (A ** (cramer_inv A)) = axis j 1" for j unfolding matrix_mul_columns by auto
    moreover have "column j (mat 1) = axis j 1" for j :: 'n unfolding column_def mat_def axis_def by simp
    ultimately show ?thesis using matrix_columns_unique by metis
  qed
  then show ?thesis using invertible invertible_imp_right_inverse_is_inverse unfolding GL_def by fastforce 
qed

lemma matrix_inv_continuous:
  shows "continuous_map (GL_topology :: (real^'n^'n) topology) GL_topology matrix_inv"
proof -
  define B :: "real^'n^'n \<Rightarrow> 'n \<Rightarrow> 'n \<Rightarrow> 'n \<Rightarrow> 'n \<Rightarrow> real" where
    "B = (\<lambda>A i j k l. if l = i then (axis j 1) $ k else A$k$l)"
  define C :: "real^'n^'n \<Rightarrow> 'n \<Rightarrow> 'n \<Rightarrow> real^'n^'n" where
    "C A i j = (\<chi> k l. B A i j k l)" for A i j
  have det_GL_continuous: "continuous_map GL_topology euclideanreal det"
    unfolding GL_topology_def using continuous_map_from_subtopology[OF det_continuous] by fast
  have "continuous_map euclidean euclideanreal (\<lambda>A. B A i j k l)" for i j k l
  proof (cases "l = i")
    case True
    then have "(\<lambda>A. B A i j k l) = (\<lambda>A. (axis j 1) $ k)" unfolding B_def by force
    moreover have "continuous_map euclidean euclideanreal (\<lambda>A. (axis j 1) $ k)" by simp
    ultimately show ?thesis by (smt (verit) continuous_map_eq)
  next
    case False
    then have "(\<lambda>A. B A i j k l) = (\<lambda>A. A$k$l)" unfolding B_def by simp
    then show ?thesis unfolding matrix_topology_euclidean[symmetric] 
      using matrix_projection_continuous[of euclideanreal k l] by force
  qed
  then have "continuous_map euclidean euclideanreal (\<lambda>A. (C A i j) $ k $ l)"
    for i j k l unfolding C_def by simp
  from matrix_components_continuous_imp_continuous[OF this]
  have "continuous_map euclidean euclidean (\<lambda>A. C A i j)" for i j 
    unfolding matrix_topology_euclidean[symmetric] by blast
  from continuous_map_compose[OF this det_continuous]
  have "continuous_map euclidean euclideanreal (\<lambda>A. det (C A i j))" for i j by force
  then have "continuous_map GL_topology euclideanreal (\<lambda>A. det (C A i j))" for i j
    unfolding GL_topology_def using continuous_map_from_subtopology by fast
  from continuous_map_real_divide[OF this det_GL_continuous]
  have "continuous_map GL_topology euclideanreal (\<lambda>A. det (C A i j) / det A)" for i j
    unfolding topspace_GL invertible_det_nz by simp
  then have "continuous_map GL_topology euclideanreal (\<lambda>A. (\<chi> i j. det (C A i j) / det A) $ i $ j)" for i j by simp
  from matrix_components_continuous_imp_continuous[OF this]
  have "continuous_map (GL_topology :: (real^'n^'n) topology) euclidean cramer_inv" 
    unfolding cramer_inv_def C_def B_def matrix_topology_euclidean[symmetric] by blast
  from continuous_map_eq[OF this] have "continuous_map (GL_topology :: (real^'n^'n) topology) euclidean matrix_inv"
    unfolding topspace_GL using cramer_inv_is_inverse by (metis mem_Collect_eq)
  moreover have "matrix_inv A \<in> topspace GL_topology" if "A \<in> topspace GL_topology" for A :: "real^'n^'n"
    using that unfolding topspace_GL
    by (metis invertible_imp_right_inverse_is_inverse invertible_left_inverse invertible_right_inverse mem_Collect_eq)
  ultimately show ?thesis unfolding GL_topology_def Pi_def image_def using continuous_map_into_subtopology by auto
qed

subsubsection \<open>The general linear group is topological\<close>

lemma
  GL_group: "group GL" and 
  GL_carrier [simp]: "carrier GL = {A. invertible A}" and
  GL_inv [simp]: "A  \<in> carrier GL \<Longrightarrow> inv\<^bsub>GL\<^esub> A = matrix_inv A"
proof -
  show "carrier GL = {A. invertible A}" unfolding GL_def by simp
  show "group GL"
  proof (unfold_locales, goal_cases)
    case 3
    then show ?case unfolding GL_def by (simp add: invertible_def)
    case 6
    then show ?case using GL_def unfolding Units_def invertible_def
      by (smt (verit, ccfv_threshold) Collect_mono invertible_def mem_Collect_eq monoid.select_convs(1) monoid.select_convs(2) partial_object.select_convs(1))
  qed (unfold GL_def, auto simp: matrix_mul_assoc invertible_mult)
  interpret group GL by fact
  show "A \<in> carrier GL \<Longrightarrow> inv\<^bsub>GL\<^esub> A = matrix_inv A"
    using matrix_inv_is_inv matrix_inv_invertible inv_equality unfolding GL_def by fastforce
qed

lemma
  GL_topological_group: "topological_group GL GL_topology" and 
  GL_open: "openin (euclidean :: (real^'n^'n) topology) (carrier GL)"
proof -
  have group_is_space: "topspace GL_topology = carrier GL" unfolding topspace_GL GL_def by simp
  have "continuous_map (prod_topology GL_topology GL_topology) euclidean (\<lambda>(A,B). A ** B)"
    unfolding GL_topology_def subtopology_Times[symmetric] using matrix_mul_continuous continuous_map_from_subtopology by fast
  from continuous_map_into_subtopology[OF this] 
  have "continuous_map (prod_topology GL_topology GL_topology) GL_topology (\<lambda>(A,B). A \<otimes>\<^bsub>GL\<^esub> B)"
    unfolding GL_topology_def Pi_def topspace_prod_topology topspace_subtopology GL_def using invertible_mult by auto
  moreover from continuous_map_eq[OF matrix_inv_continuous] 
  have "continuous_map GL_topology GL_topology (\<lambda>A. inv\<^bsub>GL\<^esub> A)" unfolding group_is_space using GL_inv by metis
  ultimately show "topological_group GL GL_topology" using GL_group group_is_space
    unfolding topological_group_def topological_group_axioms_def by blast
  have "openin euclideanreal ((topspace euclideanreal) - {0})" by auto
  from openin_continuous_map_preimage[OF det_continuous this] 
  have "openin euclidean {(A :: real^'n^'n) \<in> topspace euclidean. det A \<in> ((topspace euclideanreal) - {0})}" by blast
  moreover have "carrier GL = {A :: real^'n^'n. det A \<noteq> 0}"     
    using group_is_space[symmetric] invertible_det_nz unfolding topspace_GL by blast
  ultimately show "openin (euclidean :: (real^'n^'n) topology) (carrier GL)" by fastforce
qed

subsection \<open>Subgroups of the general linear group\<close>

definition SL :: "(('a :: field)^'n^'n) monoid" where
"SL = GL \<lparr>carrier := {A. det A = 1}\<rparr>"

lemma det_homomorphism: "group_hom GL unit_group det"
proof -
  have "det \<in> carrier GL \<rightarrow> carrier unit_group"
    unfolding GL_carrier unit_group_def using invertible_det_nz by fastforce
  moreover have "det (A \<otimes>\<^bsub>GL\<^esub> B) = det A \<otimes>\<^bsub>unit_group\<^esub> det B" for A B
    unfolding GL_def unit_group_def using det_mul by auto
  ultimately have "det \<in> hom GL unit_group" unfolding hom_def by blast 
  then show ?thesis using GL_group group_unit_group
    unfolding group_hom_def group_hom_axioms_def by blast
qed
                              
lemma
  SL_kernel_det: "carrier (SL :: (('a :: field)^'n^'n) monoid) = kernel GL unit_group det" and
  SL_subgroup: "subgroup (carrier SL) (GL :: ('a^'n^'n) monoid)" and
  SL_carrier [simp]: "carrier SL = {A. det A = 1}"                  
proof -                           
  interpret group_hom "GL :: ('a^'n^'n) monoid" unit_group det using det_homomorphism by blast
  show "carrier SL = {A. det A = 1}" unfolding SL_def by simp
  then show "carrier (SL :: ('a^'n^'n) monoid) = kernel GL unit_group det"     
    unfolding kernel_def GL_carrier unit_group_def using invertible_det_nz by force
  then show "subgroup (carrier SL) (GL :: ('a^'n^'n) monoid)" using subgroup_kernel by presburger
qed

lemma                      
  SL_topological_group: "topological_group SL (subtopology GL_topology (carrier SL))" and
  SL_closed: "closedin GL_topology (carrier SL)"
proof -
  interpret topological_group GL GL_topology using GL_topological_group by blast
  show "topological_group SL (subtopology GL_topology (carrier SL))" 
    unfolding SL_def using topological_subgroup[OF SL_subgroup] by force
  have "closedin euclideanreal {1}" by simp
  then have "closedin GL_topology {A \<in> topspace GL_topology. det A = 1}" unfolding GL_topology_def 
    using continuous_map_from_subtopology[OF det_continuous] closedin_continuous_map_preimage 
    by (smt (verit, ccfv_SIG) Collect_cong singleton_iff)
  moreover have "{A \<in> topspace GL_topology. det A = 1} = {A. det A = 1}" 
    using topspace_GL using invertible_det_nz by fastforce
  ultimately show "closedin GL_topology (carrier SL)" unfolding SL_carrier by (smt (verit))
qed

definition GO :: "(real^'n^'n) monoid" where
"GO = GL \<lparr>carrier := {A. orthogonal_matrix A}\<rparr>"

lemma
  GO_subgroup: "subgroup {A :: real^'n^'n. orthogonal_matrix A} GL" and
  GO_carrier [simp]: "carrier GO = {A. orthogonal_matrix A}"
proof -
  show "carrier GO = {A. orthogonal_matrix A}" unfolding GO_def by force
  show "subgroup {A :: real^'n^'n. orthogonal_matrix A} GL"
  proof (unfold_locales, goal_cases)
    case 1
    then show ?case unfolding GL_carrier orthogonal_matrix_def invertible_def by blast
  next
    case (2 A B)
    then show ?case unfolding GL_def using orthogonal_matrix_mul[of A B] by force
  next
    case 3
    then show ?case unfolding GL_def using orthogonal_matrix_id by simp
  next
    case (4 A)
    then have "A \<in> carrier GL" unfolding GL_carrier orthogonal_matrix_def invertible_def by blast  
    moreover from 4 have "orthogonal_matrix (matrix_inv A)"
      by (metis invertible_imp_right_inverse_is_inverse invertible_right_inverse mem_Collect_eq orthogonal_matrix_def orthogonal_matrix_transpose)
    ultimately show ?case using GL_inv by fastforce
  qed
qed

lemma
  GO_topological_group: "topological_group GO (subtopology GL_topology (carrier GO))" and
  GO_closed: "closedin (GL_topology :: (real^'n^'n) topology) (carrier GO)"
proof -
  interpret topological_group GL GL_topology using GL_topological_group by blast
  show "topological_group GO (subtopology GL_topology (carrier GO))"
    unfolding GO_def using topological_subgroup[OF GO_subgroup] by simp
  have one_closed: "closedin euclidean {(mat 1) :: real^'n^'n}" by fastforce
  have "continuous_map euclidean (prod_topology euclidean euclidean) (\<lambda>A :: real^'n^'n. (transpose A, A))"
    using continuous_map_pairedI[OF transpose_continuous continuous_map_id] by force
  from continuous_map_compose[OF this matrix_mul_continuous]
  have "continuous_map euclidean euclidean (\<lambda>A :: real^'n^'n. (transpose A) ** A)" by force
  from closedin_continuous_map_preimage[OF this one_closed]
  have "closedin euclidean {A :: real^'n^'n. (transpose A) ** A = mat 1}" by force
  moreover have "carrier GO = {A :: real^'n^'n. (transpose A) ** A = mat 1}"
    using orthogonal_matrix unfolding GO_carrier by blast
  ultimately have "closedin (euclidean :: (real^'n^'n) topology) (carrier GO)" by (smt (verit, del_insts))
  moreover have "carrier GO \<subseteq> carrier GL"
    unfolding GO_carrier GL_carrier orthogonal_matrix_def invertible_def by blast
  ultimately show "closedin (GL_topology :: (real^'n^'n) topology) (carrier GO)" 
    unfolding GL_topology_def using closedin_subset_topspace by blast
qed

definition SO :: "(real^'n^'n) monoid" where
"SO = GL \<lparr>carrier := {A. orthogonal_matrix A \<and> det A = 1}\<rparr>"

lemma
  SO_carrier [simp]: "carrier SO = {A. orthogonal_matrix A \<and> det A = 1}" and
  SO_subgroup: "subgroup {A :: real^'n^'n. orthogonal_matrix A \<and> det A = 1} GL"
proof -
  show "carrier SO = {A. orthogonal_matrix A \<and> det A = 1}" unfolding SO_def by auto
  have eq: "{A :: real^'n^'n. orthogonal_matrix A \<and> det A = 1} = {A. orthogonal_matrix A} \<inter> {A. det A = 1}" by fastforce
  show "subgroup {A :: real^'n^'n. orthogonal_matrix A \<and> det A = 1} GL"
    unfolding eq using subgroup_intersection[OF GO_subgroup SL_subgroup] by simp
qed

lemma
  SO_topological_group: "topological_group SO (subtopology GL_topology (carrier SO))" and
  SO_closed: "closedin GL_topology (carrier SO)"
proof-
  interpret topological_group GL GL_topology using GL_topological_group by blast
  show "topological_group SO (subtopology GL_topology (carrier SO))"
    unfolding SO_def using topological_subgroup[OF SO_subgroup] by simp
  have "carrier SO = carrier SL \<inter> carrier GO" unfolding SO_carrier SL_carrier GO_carrier by blast
  then show "closedin GL_topology (carrier SO)" using closedin_Int[OF SL_closed GO_closed] by metis
qed

end