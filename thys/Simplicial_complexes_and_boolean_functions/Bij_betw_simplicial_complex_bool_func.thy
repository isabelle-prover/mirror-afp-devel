
theory Bij_betw_simplicial_complex_bool_func
  imports
    Simplicial_complex
begin

section\<open>Bijection between simplicial complexes and monotone Boolean functions\<close>

context simplicial_complex
begin

lemma ceros_of_boolean_input_in_set:
  assumes s: "\<sigma> \<in> simplices"
  shows "ceros_of_boolean_input (vec n (\<lambda>i. i \<notin> \<sigma>)) = \<sigma>"
  unfolding ceros_of_boolean_input_def using s unfolding simplices_def by auto

lemma
  assumes sigma: "\<sigma> \<in> simplices"
  and nempty: "\<sigma> \<noteq> {}"
  shows "Max \<sigma> < n"
proof -
  have "Max \<sigma> \<in> \<sigma>" using linorder_class.Max_in [OF finite_simplex [OF sigma] nempty] .
  thus ?thesis using sigma unfolding simplices_def by auto
qed

definition bool_vec_from_simplice :: "nat set => (bool vec)"
  where "bool_vec_from_simplice \<sigma> = vec n (\<lambda>i. i \<notin> \<sigma>)"

lemma [simp]:
  assumes "\<sigma> \<in> simplices"
  shows "ceros_of_boolean_input (bool_vec_from_simplice \<sigma>) = \<sigma>"
  unfolding bool_vec_from_simplice_def
  unfolding ceros_of_boolean_input_def
  unfolding dim_vec
  using assms unfolding simplices_def by auto

lemma [simp]:
  assumes n: "dim_vec f = n"
  shows "bool_vec_from_simplice (ceros_of_boolean_input f) = f"
  unfolding bool_vec_from_simplice_def
  unfolding ceros_of_boolean_input_def
  using n by auto

lemma "bool_vec_from_simplice {0} = vec n (\<lambda>i. i \<notin> {0})"
  unfolding bool_vec_from_simplice_def by auto

lemma "bool_vec_from_simplice {1,2} =
    vec n (\<lambda>i. i \<notin> {1,2})"
  unfolding bool_vec_from_simplice_def by auto

lemma simplicial_complex_implies_true:
  assumes "\<sigma> \<in> simplicial_complex_induced_by_monotone_boolean_function n f"
  shows "f (bool_vec_from_simplice \<sigma>)"
  unfolding bool_vec_from_simplice_def
  using assms
  unfolding simplicial_complex_induced_by_monotone_boolean_function_def
  unfolding ceros_of_boolean_input_def
  apply auto
  by (smt (verit, best) dim_vec eq_vecI index_vec)

definition bool_vec_set_from_simplice_set :: "nat set set => (bool vec) set"
  where "bool_vec_set_from_simplice_set K =
     {\<sigma>. (dim_vec \<sigma> = n) \<and> (\<exists>k\<in>K. \<sigma> = bool_vec_from_simplice k)}"

definition boolean_function_from_simplicial_complex :: "nat set set => (bool vec => bool)"
  where "boolean_function_from_simplicial_complex K =
          (\<lambda>x. x \<in> (bool_vec_set_from_simplice_set K))"

lemma "Collect (boolean_function_from_simplicial_complex K) = (bool_vec_set_from_simplice_set K)"
  unfolding boolean_function_from_simplicial_complex_def by simp

text\<open>The Boolean function induced by a simplicial complex is monotone.
  This result is proven in Scoville as part of the proof of Proposition 6.16.
  The opposite direction has been proven as
  @{thm monotone_bool_fun_induces_simplicial_complex}.\<close>

lemma
  simplicial_complex_induces_monotone_bool_fun:
  assumes mon: "simplicial_complex (K::nat set set)"
  shows "boolean_functions.monotone_bool_fun n (boolean_function_from_simplicial_complex K)"
proof (unfold boolean_functions.monotone_bool_fun_def)
  show "mono_on (carrier_vec n) (boolean_function_from_simplicial_complex K)"
  proof (intro mono_onI)
  fix r and s::"bool vec"
  assume r_le_s: "r \<le> s"
  show "boolean_function_from_simplicial_complex K r
        \<le> boolean_function_from_simplicial_complex K s"
  proof (cases "boolean_function_from_simplicial_complex K r")
    case False then show ?thesis by simp
  next
    case True
    have ce: "ceros_of_boolean_input s \<subseteq> ceros_of_boolean_input r"
      using monotone_ceros_of_boolean_input [OF r_le_s] .
    from True obtain k where r_def: "r = vec n (\<lambda>i. i \<notin> k)"
      and k: "k \<in> K"
      unfolding boolean_function_from_simplicial_complex_def
      unfolding bool_vec_set_from_simplice_set_def
      unfolding bool_vec_from_simplice_def by auto
    have r_in_K: "ceros_of_boolean_input r \<in> K"
      using k mon
      unfolding r_def
      unfolding ceros_of_boolean_input_def
      unfolding dim_vec
      using simplicial_complex_def [of K] by fastforce
    have "boolean_function_from_simplicial_complex K s"
    proof (unfold boolean_function_from_simplicial_complex_def
        bool_vec_set_from_simplice_set_def, rule, rule conjI)
      show "dim_vec s = n"
        by (metis less_eq_vec_def dim_vec r_def r_le_s)
      show "\<exists>k\<in>K. s = bool_vec_from_simplice k"
        proof (rule bexI [of _ "ceros_of_boolean_input s"], unfold bool_vec_from_simplice_def)
          show "ceros_of_boolean_input s \<in> K"
            using simplicial_complex_monotone [OF mon r_in_K ce] .
          show "s = vec n (\<lambda>i. i \<notin> ceros_of_boolean_input s)"
            using ce unfolding ceros_of_boolean_input_def
            using r_le_s
            unfolding less_eq_vec_def
            unfolding r_def
            unfolding dim_vec by auto
        qed
      qed
     thus ?thesis by simp
   qed
 qed
qed

lemma shows "(simplicial_complex_induced_by_monotone_boolean_function n) \<in>
          boolean_functions.monotone_bool_fun_set n
          \<rightarrow> (simplicial_complex_set::nat set set set)"
proof
  fix x::"bool vec \<Rightarrow> bool"
  assume x: "x \<in> boolean_functions.monotone_bool_fun_set n"
  show "simplicial_complex_induced_by_monotone_boolean_function n x \<in> simplicial_complex_set"
    using monotone_bool_fun_induces_simplicial_complex [of x] x
    unfolding boolean_functions.monotone_bool_fun_set_def
    unfolding boolean_functions.monotone_bool_fun_def simplicial_complex_set_def
    by auto
qed

lemma shows "boolean_function_from_simplicial_complex
          \<in> (simplicial_complex_set::nat set set set)
          \<rightarrow> boolean_functions.monotone_bool_fun_set n"
proof
  fix x::"nat set set" assume x: "x \<in> simplicial_complex_set"
  show "boolean_function_from_simplicial_complex x \<in> boolean_functions.monotone_bool_fun_set n"
    using simplicial_complex_induces_monotone_bool_fun [of x]
    unfolding boolean_functions.monotone_bool_fun_set_def
    unfolding boolean_functions.monotone_bool_fun_def
    using x unfolding simplicial_complex_set_def
    unfolding mem_Collect_eq by fast
qed

text\<open>Given a Boolean function @{term f}, if we build its associated
  simplicial complex and then the associated Boolean function,
  we obtain @{term f}.

  The result holds for every Boolean function @{term f}
  (the premise on @{term f} being monotone can be omitted).\<close>

lemma
  boolean_function_from_simplicial_complex_simplicial_complex_induced_by_monotone_boolean_function:
  fixes f :: "bool vec \<Rightarrow> bool"
  assumes dim: "v \<in> carrier_vec n"
  shows "boolean_function_from_simplicial_complex
    (simplicial_complex_induced_by_monotone_boolean_function n f) v = f v"
proof (intro iffI)
  assume xb: "f v"
  show bf: "boolean_function_from_simplicial_complex
      (simplicial_complex_induced_by_monotone_boolean_function n f) v"
  proof -
   have "f v \<and> v = bool_vec_from_simplice (ceros_of_boolean_input v)"
    unfolding ceros_of_boolean_input_def
    unfolding bool_vec_from_simplice_def
    using xb dim unfolding carrier_vec_def by auto
   then show ?thesis
    unfolding simplicial_complex_induced_by_monotone_boolean_function_def
    unfolding boolean_function_from_simplicial_complex_def
    unfolding bool_vec_set_from_simplice_set_def
    unfolding mem_Collect_eq
    using dim unfolding carrier_vec_def by blast
   qed
next
  assume "boolean_function_from_simplicial_complex
      (simplicial_complex_induced_by_monotone_boolean_function n f) v"
  then show "f v"
    unfolding simplicial_complex_induced_by_monotone_boolean_function_def
    unfolding boolean_function_from_simplicial_complex_def
    unfolding bool_vec_set_from_simplice_set_def
    unfolding mem_Collect_eq
    using \<open>boolean_function_from_simplicial_complex
      (simplicial_complex_induced_by_monotone_boolean_function n f) v\<close>
      boolean_function_from_simplicial_complex_def
      simplicial_complex.bool_vec_set_from_simplice_set_def
      simplicial_complex_implies_true by fastforce
qed

text\<open>Given a simplicial complex @{term K}, if we build its associated
  Boolean function, and then the associated simplicial complex,
  we obtain @{term K}.\<close>

lemma
  simplicial_complex_induced_by_monotone_boolean_function_boolean_function_from_simplicial_complex:
  fixes K :: "nat set set"
  assumes K: "simplicial_complex K"
  shows "simplicial_complex_induced_by_monotone_boolean_function n
    (boolean_function_from_simplicial_complex K) = K"
proof (intro equalityI)
  show "simplicial_complex_induced_by_monotone_boolean_function n
    (boolean_function_from_simplicial_complex K) \<subseteq> K"
  proof
    fix x :: "nat set"
    assume x: "x \<in> simplicial_complex_induced_by_monotone_boolean_function
              n (boolean_function_from_simplicial_complex K)"
    show "x \<in> K"
      using x
      unfolding boolean_function_from_simplicial_complex_def
      unfolding simplicial_complex_induced_by_monotone_boolean_function_def
      unfolding bool_vec_from_simplice_def bool_vec_set_from_simplice_set_def
      using K
      unfolding simplicial_complex_def simplices_def
      by auto (metis assms bool_vec_from_simplice_def
          ceros_of_boolean_input_in_set simplicial_complex_def)
  qed
next
  show "K \<subseteq> simplicial_complex_induced_by_monotone_boolean_function n
            (boolean_function_from_simplicial_complex K)"
 proof
   fix x :: "nat set"
   assume "x \<in> K"
   hence x: "x \<in> simplices" using K unfolding simplicial_complex_def by simp
   have bvs: "ceros_of_boolean_input (bool_vec_from_simplice x) = x"
     unfolding one_bool_def
     unfolding bool_vec_from_simplice_def
     using ceros_of_boolean_input_in_set [OF x] .
   show "x \<in> simplicial_complex_induced_by_monotone_boolean_function n
          (boolean_function_from_simplicial_complex K)"
     unfolding boolean_function_from_simplicial_complex_def
     unfolding simplicial_complex_induced_by_monotone_boolean_function_def
     unfolding bool_vec_from_simplice_def bool_vec_set_from_simplice_set_def
     using x bool_vec_from_simplice_def bvs
     by (metis (mono_tags, lifting) \<open>x \<in> K\<close> dim_vec mem_Collect_eq)
 qed
qed

end

end