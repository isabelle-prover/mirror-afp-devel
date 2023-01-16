
theory Binary_operations
 imports Bij_betw_simplicial_complex_bool_func
begin

section\<open>Binary operations over Boolean functions and simplicial complexes\<close>

text\<open>In this theory some results on binary operations over Boolean functions and
  their relationship to operations over the induced simplicial complexes are
  presented. We follow the presentation by Chastain and Scoville~\<^cite>\<open>\<open>Sect. 1.1\<close> in "CHSC"\<close>.\<close>

definition bool_fun_or :: "nat \<Rightarrow> (bool vec \<Rightarrow> bool) \<Rightarrow> (bool vec \<Rightarrow> bool) \<Rightarrow> (bool vec \<Rightarrow> bool)"
  where "(bool_fun_or n f g) \<equiv> (\<lambda>x. f x \<or> g x)"

definition bool_fun_and :: "nat \<Rightarrow> (bool vec \<Rightarrow> bool) \<Rightarrow> (bool vec \<Rightarrow> bool) \<Rightarrow> (bool vec \<Rightarrow> bool)"
  where "(bool_fun_and n f g) \<equiv> (\<lambda>x. f x \<and> g x)"

lemma eq_union_or:
  "simplicial_complex_induced_by_monotone_boolean_function n (bool_fun_or n f g)
  = simplicial_complex_induced_by_monotone_boolean_function n f
    \<union> simplicial_complex_induced_by_monotone_boolean_function n g"
  (is "?sc n (?bf_or n f g) = ?sc n f \<union> ?sc n g")
proof
  show "?sc n f \<union> ?sc n g \<subseteq> ?sc n (?bf_or n f g)"
  proof
    fix \<sigma> :: "nat set"
    assume "\<sigma> \<in> (?sc n f \<union> ?sc n g)"
    hence sigma: "\<sigma> \<in> ?sc n f \<or> \<sigma> \<in> ?sc n g" by auto
    have "f (simplicial_complex.bool_vec_from_simplice n \<sigma>)
           \<or> g (simplicial_complex.bool_vec_from_simplice n \<sigma>)"
    proof (cases "\<sigma> \<in> ?sc n f")
      case True
      from simplicial_complex.simplicial_complex_implies_true [OF True]
      show "f (simplicial_complex.bool_vec_from_simplice n \<sigma>)
           \<or> g (simplicial_complex.bool_vec_from_simplice n \<sigma>)" by fast
    next
      case False
      hence sigmain: "\<sigma> \<in> ?sc n g" using sigma by fast
      from simplicial_complex.simplicial_complex_implies_true [OF sigmain]
      show "f (simplicial_complex.bool_vec_from_simplice n \<sigma>)
           \<or> g (simplicial_complex.bool_vec_from_simplice n \<sigma>)" by fast
    qed
    thus "\<sigma> \<in> ?sc n (?bf_or n f g)"
      using simplicial_complex_induced_by_monotone_boolean_function_def
      using bool_fun_or_def sigma by auto
  qed
next
  show "?sc n (?bf_or n f g) \<subseteq> ?sc n f \<union> ?sc n g"
  proof
    fix \<sigma>::"nat set"
    assume sigma: "\<sigma> \<in> ?sc n (?bf_or n f g)"
    hence "bool_fun_or n f g (simplicial_complex.bool_vec_from_simplice n \<sigma>)"
      unfolding simplicial_complex.bool_vec_from_simplice_def
      unfolding simplicial_complex_induced_by_monotone_boolean_function_def
      unfolding ceros_of_boolean_input_def
      by auto (smt (verit) dim_vec eq_vecI index_vec)+
    hence "(f (simplicial_complex.bool_vec_from_simplice n \<sigma>))
            \<or> (g (simplicial_complex.bool_vec_from_simplice n \<sigma>))"
      unfolding bool_fun_or_def
      by auto
    hence "\<sigma> \<in> ?sc n f \<or> \<sigma> \<in> ?sc n g"
      by (smt (z3) sigma bool_fun_or_def mem_Collect_eq
            simplicial_complex_induced_by_monotone_boolean_function_def)
    thus "\<sigma> \<in> simplicial_complex_induced_by_monotone_boolean_function n f
          \<union> simplicial_complex_induced_by_monotone_boolean_function n g"
      by auto
  qed
qed

lemma eq_inter_and:
  "simplicial_complex_induced_by_monotone_boolean_function n (bool_fun_and n f g)
  = simplicial_complex_induced_by_monotone_boolean_function n f
    \<inter> simplicial_complex_induced_by_monotone_boolean_function n g"
  (is "?sc n (?bf_and n f g) = ?sc n f \<inter> ?sc n g")
proof
  show "?sc n f \<inter> ?sc n g \<subseteq> ?sc n (?bf_and n f g)"
  proof
    fix \<sigma> :: "nat set"
    assume "\<sigma> \<in> (?sc n f \<inter> ?sc n g)"
    hence sigma: "\<sigma> \<in> ?sc n f \<and> \<sigma> \<in> ?sc n g" by auto
    have "f (simplicial_complex.bool_vec_from_simplice n \<sigma>)
           \<and> g (simplicial_complex.bool_vec_from_simplice n \<sigma>)"
    proof -
      from sigma have sigmaf: "\<sigma> \<in> ?sc n f" and sigmag: "\<sigma> \<in> ?sc n g"
        by auto
      have "f (simplicial_complex.bool_vec_from_simplice n \<sigma>)"
        using simplicial_complex.simplicial_complex_implies_true [OF sigmaf] .
      moreover have "g (simplicial_complex.bool_vec_from_simplice n \<sigma>)"
        using simplicial_complex.simplicial_complex_implies_true [OF sigmag] .
      ultimately show ?thesis by fast
    qed
    thus "\<sigma> \<in> ?sc n (?bf_and n f g)"
      unfolding simplicial_complex_induced_by_monotone_boolean_function_def
      unfolding bool_fun_and_def
      using sigma apply auto
      by (smt (z3) Collect_cong ceros_of_boolean_input_def dim_vec index_vec mem_Collect_eq
          simplicial_complex.bool_vec_from_simplice_def
          simplicial_complex_induced_by_monotone_boolean_function_def)
  qed
next
  show "?sc n (?bf_and n f g) \<subseteq> ?sc n f \<inter> ?sc n g"
  proof
    fix \<sigma> :: "nat set"
    assume sigma: "\<sigma> \<in> ?sc n (?bf_and n f g)"
    hence "bool_fun_and n f g (simplicial_complex.bool_vec_from_simplice n \<sigma>)"
      unfolding simplicial_complex.bool_vec_from_simplice_def
      unfolding simplicial_complex_induced_by_monotone_boolean_function_def
      unfolding ceros_of_boolean_input_def
      by auto (smt (verit) dim_vec eq_vecI index_vec)+
    hence "(f (simplicial_complex.bool_vec_from_simplice n \<sigma>))
          \<and> (g (simplicial_complex.bool_vec_from_simplice n \<sigma>))"
      unfolding bool_fun_and_def
      by auto
    hence "\<sigma> \<in> ?sc n f \<and> \<sigma> \<in> ?sc n g"
      using bool_fun_and_def sigma simplicial_complex_induced_by_monotone_boolean_function_def by auto
    thus "\<sigma> \<in> simplicial_complex_induced_by_monotone_boolean_function n f
          \<inter> simplicial_complex_induced_by_monotone_boolean_function n g"
      by auto
  qed
qed

definition bool_fun_ast :: "(nat \<times> nat) \<Rightarrow> (bool vec \<Rightarrow> bool) \<times> (bool vec \<Rightarrow> bool)
    \<Rightarrow> (bool vec \<times> bool vec \<Rightarrow> bool)"
  where "(bool_fun_ast n f) \<equiv> (\<lambda> (x,y). (fst f x) \<and> (snd f y))"

definition
  simplicial_complex_induced_by_monotone_boolean_function_ast
    :: "(nat \<times> nat) \<Rightarrow> ((bool vec \<times> bool vec \<Rightarrow> bool)) \<Rightarrow> (nat set * nat set) set"
  where "simplicial_complex_induced_by_monotone_boolean_function_ast n f =
        {z. \<exists>x y. dim_vec x = fst n \<and> dim_vec y = snd n \<and> f (x, y)
          \<and> ((ceros_of_boolean_input x), (ceros_of_boolean_input y)) = z}"

lemma fst_es_simplice:
  "a \<in> simplicial_complex_induced_by_monotone_boolean_function_ast n f
    \<Longrightarrow> (\<exists>x y. f (x, y) \<and> (ceros_of_boolean_input x) = fst(a))"
  by (smt (verit) fst_conv mem_Collect_eq
        simplicial_complex_induced_by_monotone_boolean_function_ast_def)

lemma snd_es_simplice:
  "a \<in> simplicial_complex_induced_by_monotone_boolean_function_ast n f
    \<Longrightarrow> (\<exists>x y. f (x, y) \<and> (ceros_of_boolean_input y) = snd(a))"
  by (smt (verit) snd_conv mem_Collect_eq
      simplicial_complex_induced_by_monotone_boolean_function_ast_def)

definition set_ast :: "(nat set) set \<Rightarrow> (nat set) set \<Rightarrow> ((nat set*nat set) set)"
  where "set_ast A B \<equiv> {c. \<exists>a\<in>A. \<exists>b\<in>B. c = (a,b)}"

definition set_fst :: "(nat*nat) set \<Rightarrow> nat set"
  where "set_fst AB = {a. \<exists>ab\<in>AB. a = fst ab}"

lemma set_fst_simp [simp]:
  assumes "y \<noteq> {}"
  shows "set_fst (x \<times> y) = x"
proof
  show "set_fst (x \<times> y) \<subseteq> x"
    by (smt (verit) SigmaE mem_Collect_eq prod.sel(1) set_fst_def subsetI)
  show "x \<subseteq> set_fst (x \<times> y)"
  proof
    fix a::"nat"
    assume "a \<in> x"
    then obtain b where "b \<in> y" and "(a,b) \<in> (x\<times>y)"
      using assms by blast
    then show "a \<in> set_fst (x \<times> y)"
      using set_fst_def by fastforce
  qed
qed

definition set_snd :: "(nat*nat) set \<Rightarrow> nat set"
  where "set_snd AB = {b. \<exists>ab\<in>AB. b = snd(ab)}"

lemma
  simplicial_complex_ast_implies_fst_true:
  assumes "\<gamma> \<in> simplicial_complex_induced_by_monotone_boolean_function_ast nn
     (bool_fun_ast nn f)"
  shows "fst f (simplicial_complex.bool_vec_from_simplice (fst nn) (fst \<gamma>))"
  using assms
  unfolding simplicial_complex.bool_vec_from_simplice_def
  unfolding simplicial_complex_induced_by_monotone_boolean_function_ast_def
  unfolding bool_fun_ast_def
  unfolding ceros_of_boolean_input_def
  apply auto
  by (smt (verit, ccfv_threshold) bool_fun_ast_def case_prod_conv dim_vec index_vec vec_eq_iff)

lemma
  simplicial_complex_ast_implies_snd_true:
  assumes "\<gamma> \<in> simplicial_complex_induced_by_monotone_boolean_function_ast nn
     (bool_fun_ast nn f)"
  shows "snd f (simplicial_complex.bool_vec_from_simplice (snd nn) (snd \<gamma>))"
  using assms
  unfolding simplicial_complex.bool_vec_from_simplice_def
  unfolding simplicial_complex_induced_by_monotone_boolean_function_ast_def
  unfolding bool_fun_ast_def
  unfolding ceros_of_boolean_input_def
  by auto (smt (verit, ccfv_threshold) bool_fun_ast_def
        case_prod_conv dim_vec index_vec vec_eq_iff)

lemma eq_ast:
"simplicial_complex_induced_by_monotone_boolean_function_ast (n, m) (bool_fun_ast (n, m) f)
= set_ast (simplicial_complex_induced_by_monotone_boolean_function n (fst f))
          (simplicial_complex_induced_by_monotone_boolean_function m (snd f))"
proof
  show "set_ast (simplicial_complex_induced_by_monotone_boolean_function n (fst f))
     (simplicial_complex_induced_by_monotone_boolean_function m (snd f))
    \<subseteq> simplicial_complex_induced_by_monotone_boolean_function_ast (n, m)
        (bool_fun_ast (n, m) f)"
  proof
    fix \<gamma>::"nat set*nat set"
    assume pert: "\<gamma> \<in> set_ast (simplicial_complex_induced_by_monotone_boolean_function n (fst f))
     (simplicial_complex_induced_by_monotone_boolean_function m (snd f))"
    hence f: "(fst \<gamma>) \<in> simplicial_complex_induced_by_monotone_boolean_function n (fst f)"
      unfolding set_ast_def
      by auto
    have sigma: "fst f (simplicial_complex.bool_vec_from_simplice n (fst \<gamma>))"
      using simplicial_complex.simplicial_complex_implies_true [OF f] .
    from pert have g: "(snd \<gamma>) \<in> simplicial_complex_induced_by_monotone_boolean_function m (snd f)"
      unfolding set_ast_def by auto
    have tau: "(snd f) (simplicial_complex.bool_vec_from_simplice m (snd \<gamma>))"
      using simplicial_complex.simplicial_complex_implies_true [OF g] .
    from sigma and tau have sigtau: "bool_fun_ast (n, m) f
        ((simplicial_complex.bool_vec_from_simplice n (fst \<gamma>)),
         (simplicial_complex.bool_vec_from_simplice m (snd \<gamma>)))"
      unfolding bool_fun_ast_def
      by auto
    from sigtau
    show "\<gamma> \<in> simplicial_complex_induced_by_monotone_boolean_function_ast (n, m)
              (bool_fun_ast (n, m) f)"
      unfolding simplicial_complex_induced_by_monotone_boolean_function_ast_def
      unfolding bool_fun_ast_def
      using sigma apply auto
      using f g simplicial_complex_induced_by_monotone_boolean_function_def by fastforce
  qed
next
  show "simplicial_complex_induced_by_monotone_boolean_function_ast (n, m)
     (bool_fun_ast (n, m) f)
    \<subseteq> set_ast (simplicial_complex_induced_by_monotone_boolean_function n (fst f))
        (simplicial_complex_induced_by_monotone_boolean_function m (snd f))"
    proof
    fix \<gamma> :: "nat set*nat set"
    assume pert: "\<gamma> \<in> simplicial_complex_induced_by_monotone_boolean_function_ast (n, m)
     (bool_fun_ast (n, m) f)"
    have sigma: "(fst \<gamma>) \<in> simplicial_complex_induced_by_monotone_boolean_function n (fst f)"
      unfolding bool_fun_ast_def
      unfolding simplicial_complex_induced_by_monotone_boolean_function_def
      unfolding simplicial_complex_induced_by_monotone_boolean_function_ast_def
      apply auto
      apply (rule exI [of _ "simplicial_complex.bool_vec_from_simplice n (fst \<gamma>)"], safe)
      using simplicial_complex.bool_vec_from_simplice_def apply auto[1]
        apply (metis fst_conv pert simplicial_complex_ast_implies_fst_true)
      using ceros_of_boolean_input_def simplicial_complex.bool_vec_from_simplice_def
        apply fastforce
      using ceros_of_boolean_input_def pert
          simplicial_complex.bool_vec_from_simplice_def
          simplicial_complex_induced_by_monotone_boolean_function_ast_def by force
   have tau: "(snd \<gamma>) \<in> simplicial_complex_induced_by_monotone_boolean_function m (snd f)"
      unfolding bool_fun_ast_def
      unfolding simplicial_complex_induced_by_monotone_boolean_function_def
      unfolding simplicial_complex_induced_by_monotone_boolean_function_ast_def
      apply auto
      apply (rule exI [of _ "simplicial_complex.bool_vec_from_simplice m (snd \<gamma>)"], safe)
      using simplicial_complex.bool_vec_from_simplice_def apply auto[1]
        apply (metis snd_conv pert simplicial_complex_ast_implies_snd_true)
      using ceros_of_boolean_input_def simplicial_complex.bool_vec_from_simplice_def
       apply fastforce
      using ceros_of_boolean_input_def pert
        simplicial_complex.bool_vec_from_simplice_def
        simplicial_complex_induced_by_monotone_boolean_function_ast_def by force
    from sigma and tau
    show "\<gamma> \<in> set_ast
        (simplicial_complex_induced_by_monotone_boolean_function n (fst f))
        (simplicial_complex_induced_by_monotone_boolean_function m (snd f))"
      using set_ast_def
      by force
  qed
qed

end