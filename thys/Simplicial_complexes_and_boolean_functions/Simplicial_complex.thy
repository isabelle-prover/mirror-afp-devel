
theory Simplicial_complex
  imports
    Boolean_functions
begin

section\<open>Simplicial Complexes\<close>

lemma Pow_singleton: "Pow {a} = {{},{a}}" by auto

lemma Pow_pair: "Pow {a,b} = {{},{a},{b},{a,b}}" by auto

locale simplicial_complex
  = fixes n::"nat"
begin

text\<open>A simplex (in $n$ vertexes) is any set of vertexes,
  including the empty set.\<close>

definition simplices :: "nat set set"
  where "simplices = Pow {0..<n}"

lemma "{} \<in> simplices"
  unfolding simplices_def by simp

lemma "{0..<n} \<in> simplices"
  unfolding simplices_def by simp

lemma finite_simplex:
  assumes "\<sigma> \<in> simplices"
  shows "finite \<sigma>"
  by (metis Pow_iff assms finite_atLeastLessThan finite_subset simplices_def)

text\<open>A simplicial complex (in $n$ vertexes) is a collection of
  sets of vertexes such that every subset of
  a set of vertexes also belongs to the simplicial complex.\<close>

definition simplicial_complex :: "nat set set => bool"
  where "simplicial_complex K \<equiv>  (\<forall>\<sigma>\<in>K. (\<sigma> \<in> simplices) \<and> (Pow \<sigma>) \<subseteq> K)"

lemma
  finite_simplicial_complex:
  assumes "simplicial_complex K"
  shows "finite K"
  by (metis assms finite_Pow_iff finite_atLeastLessThan rev_finite_subset simplices_def simplicial_complex_def subsetI)

lemma finite_simplices:
  assumes "simplicial_complex K"
  and "v \<in> K"
shows "finite v"
  using assms finite_simplex simplicial_complex.simplicial_complex_def by blast


definition simplicial_complex_set :: "nat set set set"
  where "simplicial_complex_set = (Collect simplicial_complex)"

lemma simplicial_complex_empty_set:
  fixes K::"nat set set"
  assumes k: "simplicial_complex K"
  shows "K = {} \<or> {} \<in> K" using k unfolding simplicial_complex_def Pow_def by auto

lemma
  simplicial_complex_monotone:
  fixes K::"nat set set"
  assumes k: "simplicial_complex K" and s: "s \<in> K" and rs: "r \<subseteq> s"
  shows "r \<in> K"
  using k rs s
  unfolding simplicial_complex_def Pow_def by auto

text\<open>One example of simplicial complex with four simplices.\<close>

lemma
  assumes three: "(3::nat) < n"
  shows "simplicial_complex {{},{0},{1},{2},{3}}"
  apply (simp_all add: Pow_singleton simplicial_complex_def simplices_def)
  using Suc_lessD three by presburger

lemma "\<not> simplicial_complex {{0,1},{1}}"
  by (simp add: Pow_pair simplicial_complex_def)

text\<open>Another example of simplicial complex with five simplices.\<close>

lemma
  assumes three: "(3::nat) < n"
  shows "simplicial_complex {{},{0},{1},{2},{3},{0,1}}"
  apply (simp add: Pow_pair Pow_singleton simplicial_complex_def simplices_def)
  using Suc_lessD three by presburger

text\<open>Another example of simplicial complex with ten simplices.\<close>

lemma
  assumes three: "(3::nat) < n"
  shows "simplicial_complex
    {{2,3},{1,3},{1,2},{0,3},{0,2},{3},{2},{1},{0},{}}"
  apply (simp add: Pow_pair Pow_singleton simplicial_complex_def simplices_def)
  using Suc_lessD three by presburger

end

section\<open>Simplicial complex induced by a monotone Boolean function\<close>

text\<open>In this section we introduce the definition of the
  simplicial complex induced by a monotone Boolean function,
  following the definition in Scoville~\<^cite>\<open>\<open>Def. 6.9\<close> in "SC19"\<close>.\<close>

text\<open>First we introduce the set of tuples for which
  a Boolean function is @{term False}.\<close>

definition ceros_of_boolean_input :: "bool vec => nat set"
  where "ceros_of_boolean_input v = {x. x < dim_vec v \<and> vec_index v x = False}"

lemma
  ceros_of_boolean_input_l_dim:
  assumes a: "a \<in> ceros_of_boolean_input v"
  shows "a < dim_vec v"
  using a unfolding ceros_of_boolean_input_def by simp

lemma "ceros_of_boolean_input v = {x. x < dim_vec v \<and> \<not> vec_index v x}"
  unfolding ceros_of_boolean_input_def by simp

lemma
  ceros_of_boolean_input_complementary:
  shows "ceros_of_boolean_input v = {x. x < dim_vec v} - {x. vec_index v x}"
  unfolding ceros_of_boolean_input_def by auto

(*lemma ceros_in_UNIV: "ceros_of_boolean_input f \<subseteq> (UNIV::nat set)"
  using subset_UNIV .*)

lemma monotone_ceros_of_boolean_input:
  fixes r and s::"bool vec"
  assumes r_le_s: "r \<le> s"
  shows "ceros_of_boolean_input s \<subseteq> ceros_of_boolean_input r"
proof (intro subsetI, unfold ceros_of_boolean_input_def, intro CollectI, rule conjI)
  fix x
  assume "x \<in> {x. x < dim_vec s \<and> vec_index s x = False}"
  hence xl: "x < dim_vec s" and nr: "vec_index s x = False" by simp_all
  show "vec_index r x = False"
    using r_le_s nr xl unfolding less_eq_vec_def
    by auto
  show "x < dim_vec r"
  using r_le_s xl unfolding less_eq_vec_def
    by auto
qed


text\<open>We introduce here instantiations of the typ\<open>bool\<close>
  type for the type classes class\<open>zero\<close> and class\<open>one\<close>
  that will simplify notation at some points:\<close>

instantiation bool :: "{zero,one}"
begin

definition
 zero_bool_def: "0 == False"

definition
 one_bool_def: "1 == True"

instance  proof  qed

end

text\<open>Definition of the simplicial complex induced
  by a Boolean function \<open>f\<close> in dimension \<open>n\<close>.\<close>

definition
  simplicial_complex_induced_by_monotone_boolean_function
    :: "nat => (bool vec => bool) => nat set set"
  where "simplicial_complex_induced_by_monotone_boolean_function n f =
        {y. \<exists>x. dim_vec x = n \<and> f x \<and> ceros_of_boolean_input x = y}"

text\<open>The simplicial complex induced by a Boolean function
  is a subset of the powerset of the set of vertexes.\<close>

lemma
  simplicial_complex_induced_by_monotone_boolean_function_subset:
  "simplicial_complex_induced_by_monotone_boolean_function n (v::bool vec => bool)
    \<subseteq> Pow (({0..n}::nat set))"
  using ceros_of_boolean_input_def
   simplicial_complex_induced_by_monotone_boolean_function_def
  by force

corollary
  "simplicial_complex_induced_by_monotone_boolean_function n (v::bool vec => bool)
    \<subseteq> Pow ((UNIV::nat set))" by simp

text\<open>The simplicial complex induced by a
  monotone Boolean function is a simplicial complex.
  This result is proven in Scoville as part of the
  proof of Proposition 6.16~\<^cite>\<open>\<open>Prop. 6.16\<close> in "SC19"\<close>.\<close>

context simplicial_complex
begin

lemma
  monotone_bool_fun_induces_simplicial_complex:
  assumes mon: "boolean_functions.monotone_bool_fun n f"
  shows "simplicial_complex (simplicial_complex_induced_by_monotone_boolean_function n f)"
  unfolding simplicial_complex_def
proof (rule, unfold simplicial_complex_induced_by_monotone_boolean_function_def, safe)
    fix \<sigma> :: "nat set" and x :: "bool vec"
    assume fx: "f x" and dim_vec_x: "n = dim_vec x"
    show "ceros_of_boolean_input x \<in> simplicial_complex.simplices (dim_vec x)"
      using ceros_of_boolean_input_def dim_vec_x simplices_def by force
  next
    fix \<sigma> :: "nat set" and x :: "bool vec" and \<tau> :: "nat set"
    assume fx: "f x" and dim_vec_x: "n = dim_vec x" and tau_def: "\<tau> \<subseteq> ceros_of_boolean_input x"
    show "\<exists>xb. dim_vec xb = dim_vec x \<and> f xb \<and> ceros_of_boolean_input xb = \<tau>"
    proof (rule exI [of _ "vec n (\<lambda>i. if i \<in> \<tau> then False else True)"], intro conjI)
     show "dim_vec (vec n (\<lambda>i. if i \<in> \<tau> then False else True)) = dim_vec x"
      unfolding dim_vec using dim_vec_x .
     from mon have mono: "mono_on (carrier_vec n) f"
      unfolding boolean_functions.monotone_bool_fun_def .
     show "f (vec n (\<lambda>i. if i \<in> \<tau> then False else True))"
     proof -
      have "f x \<le> f (vec n (\<lambda>i. if i \<in> \<tau> then False else True))"
      proof (rule mono_onD [OF mono])
        show "x \<in> carrier_vec n" using dim_vec_x by simp
        show "vec n (\<lambda>i. if i \<in> \<tau> then False else True) \<in> carrier_vec n" by simp
        show "x \<le> vec n (\<lambda>i. if i \<in> \<tau> then False else True)"
          using tau_def dim_vec_x unfolding ceros_of_boolean_input_def
          using less_eq_vec_def by fastforce
      qed
      thus ?thesis using fx by simp
    qed
    show "ceros_of_boolean_input (vec n (\<lambda>i. if i \<in> \<tau> then False else True)) = \<tau>"
      using \<open>\<tau> \<subseteq> ceros_of_boolean_input x\<close> ceros_of_boolean_input_def dim_vec_x by auto
  qed
qed

end

text\<open>Example 6.10 in Scoville, the threshold function
  for $2$ in dimension $4$ (with vertexes $0$,$1$,$2$,$3$)\<close>

definition bool_fun_threshold_2_3 :: "bool vec => bool"
  where "bool_fun_threshold_2_3 = (\<lambda>v. if 2 \<le> count_true v then True else False)"

lemma set_list_four: shows "{0..<4} = set [0,1,2,3::nat]" by auto

lemma comp_fun_commute_lambda:
  "comp_fun_commute_on UNIV ((+)
  \<circ> (\<lambda>i. if vec 4 f $ i then 1 else (0::nat)))"
  unfolding comp_fun_commute_on_def by auto

lemma "bool_fun_threshold_2_3
          (vec 4 (\<lambda>i. if i = 0 \<or> i = 1 then True else False)) = True"
  unfolding bool_fun_threshold_2_3_def
  unfolding count_true_def
  unfolding dim_vec
  unfolding sum.eq_fold
  using index_vec [of _ 4]
  apply auto
  unfolding set_list_four
  unfolding comp_fun_commute_on.fold_set_fold_remdups [OF comp_fun_commute_lambda, simplified]
  by simp

lemma
  "0 \<notin> ceros_of_boolean_input (vec 4 (\<lambda>i. if i = 0 \<or> i = 1 then True else False))"
  and "1 \<notin> ceros_of_boolean_input (vec 4 (\<lambda>i. if i = 0 \<or> i = 1 then True else False))"
  and "2 \<in> ceros_of_boolean_input (vec 4 (\<lambda>i. if i = 0 \<or> i = 1 then True else False))"
  and "3 \<in> ceros_of_boolean_input (vec 4 (\<lambda>i. if i = 0 \<or> i = 1 then True else False))"
  and "{2,3} \<subseteq> ceros_of_boolean_input (vec 4 (\<lambda>i. if i = 0 \<or> i = 1 then True else False))"
  unfolding ceros_of_boolean_input_def by simp_all

lemma "bool_fun_threshold_2_3 (vec 4 (\<lambda>i. if i = 3 then True else False)) = False"
  unfolding bool_fun_threshold_2_3_def
  unfolding count_true_def
  unfolding dim_vec
  unfolding sum.eq_fold
  using index_vec [of _ 4]
  apply auto
  unfolding set_list_four
  unfolding comp_fun_commute_on.fold_set_fold_remdups [OF comp_fun_commute_lambda, simplified]
  by simp

lemma "bool_fun_threshold_2_3 (vec 4 (\<lambda>i. if i = 0 then False else True))"
  unfolding bool_fun_threshold_2_3_def
  unfolding count_true_def
  unfolding dim_vec
  unfolding sum.eq_fold
  using index_vec [of _ 4]
  apply auto
  unfolding set_list_four
  unfolding comp_fun_commute_on.fold_set_fold_remdups [OF comp_fun_commute_lambda, simplified]
  by simp

section\<open>The simplicial complex induced by the threshold function\<close>

lemma
  empty_set_in_simplicial_complex_induced:
  "{} \<in> simplicial_complex_induced_by_monotone_boolean_function 4 bool_fun_threshold_2_3"
  unfolding simplicial_complex_induced_by_monotone_boolean_function_def
  unfolding bool_fun_threshold_2_3_def
  apply rule
  apply (rule exI [of _ "vec 4 (\<lambda>x. True)"])
  unfolding count_true_def ceros_of_boolean_input_def by auto

lemma singleton_in_simplicial_complex_induced:
  assumes x: "x < 4"
  shows "{x} \<in> simplicial_complex_induced_by_monotone_boolean_function 4 bool_fun_threshold_2_3"
  (is "?A \<in> simplicial_complex_induced_by_monotone_boolean_function 4 bool_fun_threshold_2_3")
proof (unfold simplicial_complex_induced_by_monotone_boolean_function_def, rule,
      rule exI [of _ "vec 4 (\<lambda>i. if i \<in> ?A then False else True)"],
      intro conjI)
  show "dim_vec (vec 4 (\<lambda>i. if i \<in> {x} then False else True)) = 4" by simp
  show "bool_fun_threshold_2_3 (vec 4 (\<lambda>i. if i \<in> ?A then False else True))"
    unfolding bool_fun_threshold_2_3_def
    unfolding count_true_def
    unfolding dim_vec
    unfolding sum.eq_fold
    using index_vec [of _ 4]
    apply auto
    unfolding set_list_four
    unfolding comp_fun_commute_on.fold_set_fold_remdups [OF comp_fun_commute_lambda, simplified]
    by simp
  show "ceros_of_boolean_input (vec 4 (\<lambda>i. if i \<in> ?A then False else True)) = ?A"
    unfolding ceros_of_boolean_input_def using x by auto
qed

lemma pair_in_simplicial_complex_induced:
  assumes x: "x < 4" and y: "y < 4"
  shows "{x,y} \<in> simplicial_complex_induced_by_monotone_boolean_function 4 bool_fun_threshold_2_3"
  (is "?A \<in> simplicial_complex_induced_by_monotone_boolean_function 4 bool_fun_threshold_2_3")
proof (unfold simplicial_complex_induced_by_monotone_boolean_function_def, rule,
      rule exI [of _ "vec 4 (\<lambda>i. if i \<in> ?A then False else True)"],
      intro conjI)
  show "dim_vec (vec 4 (\<lambda>i. if i \<in> {x, y} then False else True)) = 4" by simp
  show "bool_fun_threshold_2_3 (vec 4 (\<lambda>i. if i \<in> ?A then False else True))"
    unfolding bool_fun_threshold_2_3_def
    unfolding count_true_def
    unfolding dim_vec
    unfolding sum.eq_fold
    using index_vec [of _ 4]
    apply auto
    unfolding set_list_four
    unfolding comp_fun_commute_on.fold_set_fold_remdups [OF comp_fun_commute_lambda, simplified]
    by simp
  show "ceros_of_boolean_input (vec 4 (\<lambda>i. if i \<in> ?A then False else True)) = ?A"
    unfolding ceros_of_boolean_input_def using x y by auto
qed

lemma finite_False: "finite {x. x < dim_vec a \<and> vec_index (a::bool vec) x = False}" by auto

lemma finite_True: "finite {x. x < dim_vec a \<and> vec_index (a::bool vec) x = True}" by auto

lemma UNIV_disjoint: "{x. x < dim_vec a \<and> vec_index (a::bool vec) x = True}
  \<inter> {x. x < dim_vec a \<and> vec_index (a::bool vec) x = False} = {}"
  by auto

lemma UNIV_union: "{x. x < dim_vec a \<and> vec_index (a::bool vec) x = True}
  \<union> {x. x < dim_vec a \<and> vec_index (a::bool vec) x = False} = {x. x < dim_vec a}"
  by auto

lemma card_UNIV_union:
  "card {x. x < dim_vec a \<and> vec_index (a::bool vec) x = True}
  + card {x. x < dim_vec a \<and> vec_index (a::bool vec) x = False}
  = card {x. x < dim_vec a}"
  (is "card ?true + card ?false = _")
proof -
  have "card ?true + card ?false = card (?true \<union> ?false) + card (?true \<inter> ?false)"
    using card_Un_Int [OF finite_True [of a] finite_False [of a]] .
  also have "... = card {x. x < dim_vec a}"
    unfolding UNIV_union UNIV_disjoint by simp
  finally show ?thesis by simp
qed

lemma card_complementary:
  "card (ceros_of_boolean_input v)
    + card {x. x < (dim_vec v) \<and> (vec_index v x = True)} = (dim_vec v)"
  unfolding ceros_of_boolean_input_def
  using card_UNIV_union [of v] by simp

corollary
  card_ceros_of_boolean_input:
  shows "card (ceros_of_boolean_input a) \<le> dim_vec a"
 using card_complementary [of a] by simp

lemma
  vec_fun:
  assumes "v \<in> carrier_vec n"
  shows "\<exists>f. v = vec n f" using assms unfolding carrier_vec_def by fastforce

corollary
  assumes "dim_vec v = n"
  shows "\<exists>f. v = vec n f"
  using carrier_vecI [OF assms] unfolding carrier_vec_def by fastforce

lemma
  vec_l_eq:
  assumes "i < n"
  shows "vec (Suc n) f $ i = vec n f $ i"
  by (simp add: assms less_SucI)

lemma
  card_boolean_function:
  assumes d: "v \<in> carrier_vec n"
  shows "card {x. x < n  \<and> v $ x = True} = (\<Sum>i = 0..<n. if v $ i then 1 else (0::nat))"
using d proof (induction n arbitrary: v rule: nat_less_induct)
  case (1 n)
  assume hyp: "\<forall>m<n. \<forall>x. x \<in> carrier_vec m \<longrightarrow>
      card {xa. xa < m \<and> x $ xa = True} = (\<Sum>i = 0..<m. if x $ i then 1 else 0)"
    and d: "v \<in> carrier_vec n"
  show "card {x. x < n \<and> v $ x = True} = (\<Sum>i = 0..<n. if v $ i then 1 else 0)"
  using d proof (cases n)
    case 0
    then show ?thesis by simp
  next
    case (Suc m)
    assume v: "v \<in> carrier_vec n"
    obtain f :: "nat => bool" where v_f: "v = vec n f" using vec_fun [OF v] by auto
    have "card {x. x < m \<and> (vec m f) $ x = True} = (\<Sum>i = 0..<m. if (vec m f) $ i then 1 else 0)"
      using hyp v Suc by simp
    show ?thesis unfolding v_f unfolding Suc
    proof (cases "vec (Suc m) f $ m = True")
      case True
      have one: "{x. x < Suc m \<and> vec (Suc m) f $ x = True} =
          ({x. x < m \<and> vec (Suc m) f $ x = True} \<union> {x. x = m \<and> (vec (Suc m) f) $ x = True})"
        by auto
      have two: "disjnt {x. x < m \<and> vec (Suc m) f $ x = True} {x. x = m \<and> (vec (Suc m) f) $ x = True}"
        using disjnt_iff by blast
      have "card {x. x < Suc m \<and> vec (Suc m) f $ x = True}
            = card {x. x < m \<and> (vec (Suc m) f) $ x = True} + card {x. x = m \<and> (vec (Suc m) f) $ x = True}"
        unfolding one
        by (rule card_Un_disjnt [OF _ _ two], simp_all)
      also have "... = card {x. x < m \<and> (vec  m f) $ x = True} + 1"
      proof -
        have one: "{x. x < m \<and> vec (Suc m) f $ x = True} = {x. x < m \<and> vec m f $ x = True}"
          using vec_l_eq [of _ m] by auto
        have eq: "{x. x = m \<and> vec (Suc m) f $ x = True} = {m}" using True by auto
        hence two: "card {x. x = m \<and> vec (Suc m) f $ x = True} = 1" by simp
        show ?thesis using one two by simp
      qed
      finally have lhs: "card {x. x < Suc m \<and> vec (Suc m) f $ x = True} = card {x. x < m \<and> vec m f $ x = True} + 1" .
      have "(\<Sum>i = 0..<Suc m. if vec (Suc m) f $ i then 1 else 0) =
           (\<Sum>i = 0..<m. if vec (Suc m) f $ i then 1 else 0) + (if vec (Suc m) f $ m then 1 else 0)"
        by simp
      also have "... = (\<Sum>i = 0..<m. if vec m f $ i then 1 else 0) + 1"
        using vec_l_eq [of _ m] True by simp
      finally have rhs: "(\<Sum>i = 0..<Suc m. if vec (Suc m) f $ i then 1 else 0) =
        (\<Sum>i = 0..<m. if vec m f $ i then 1 else 0) + 1" .
      show "card {x. x < Suc m \<and> vec (Suc m) f $ x = True} =
        (\<Sum>i = 0..<Suc m. if vec (Suc m) f $ i then 1 else 0)"
        unfolding lhs rhs using hyp Suc by simp
    next
      case False
      have one: "{x. x < Suc m \<and> vec (Suc m) f $ x = True} =
          ({x. x < m \<and> vec (Suc m) f $ x = True} \<union> {x. x = m \<and> (vec (Suc m) f) $ x = True})"
        by auto
      have two: "disjnt {x. x < m \<and> vec (Suc m) f $ x = True} {x. x = m \<and> (vec (Suc m) f) $ x = True}"
        using disjnt_iff by blast
      have "card {x. x < Suc m \<and> vec (Suc m) f $ x = True}
            = card {x. x < m \<and> (vec (Suc m) f) $ x = True} + card {x. x = m \<and> (vec (Suc m) f) $ x = True}"
        unfolding one
        by (rule card_Un_disjnt [OF _ _ two], simp_all)
      also have "... = card {x. x < m \<and> (vec  m f) $ x = True} + 0"
      proof -
        have one: "{x. x < m \<and> vec (Suc m) f $ x = True} = {x. x < m \<and> vec m f $ x = True}"
          using vec_l_eq [of _ m] by auto
        have eq: "{x. x = m \<and> vec (Suc m) f $ x = True} = {}" using False by auto
        hence two: "card {x. x = m \<and> vec (Suc m) f $ x = True} = 0" by simp
        show ?thesis using one two by simp
      qed
      finally have lhs: "card {x. x < Suc m \<and> vec (Suc m) f $ x = True} = card {x. x < m \<and> vec m f $ x = True} + 0" .
      have "(\<Sum>i = 0..<Suc m. if vec (Suc m) f $ i then 1 else 0) =
           (\<Sum>i = 0..<m. if vec (Suc m) f $ i then 1 else 0) + (if vec (Suc m) f $ m then 1 else 0)"
        by simp
      also have "... = (\<Sum>i = 0..<m. if vec m f $ i then 1 else 0)"
        using vec_l_eq [of _ m] False by simp
      finally have rhs: "(\<Sum>i = 0..<Suc m. if vec (Suc m) f $ i then 1 else 0) =
        (\<Sum>i = 0..<m. if vec m f $ i then 1 else 0)" .
      show "card {x. x < Suc m \<and> vec (Suc m) f $ x = True} =
        (\<Sum>i = 0..<Suc m. if vec (Suc m) f $ i then 1 else 0)"
        unfolding lhs rhs using hyp Suc by simp
    qed
  qed
qed

lemma card_ceros_count_UNIV:
  shows "card (ceros_of_boolean_input a) + count_true ((a::bool vec)) = dim_vec a"
  using card_complementary [of a]
  using card_boolean_function
  unfolding ceros_of_boolean_input_def
  unfolding count_true_def by simp

text\<open>We calculate the carrier set of the @{const ceros_of_boolean_input}
  function for dimensions $2$, $3$ and $4$.\<close>


text\<open>Vectors of dimension $2$.\<close>

lemma
  dim_vec_2_cases:
  assumes dx: "dim_vec x = 2"
  shows "(x $ 0 = x $ 1 = True) \<or> (x $ 0 = False \<and> x $ 1 = True)
       \<or> (x $ 0 = True \<and> x $ 1 = False) \<or> (x $ 0 = x $ 1 = False)"
  by auto

lemma tt_2: assumes dx: "dim_vec x = 2"
  and be: "x $ 0 = True \<and> x $ 1 = True"
  shows "ceros_of_boolean_input x = {}"
  using dx be unfolding ceros_of_boolean_input_def using less_2_cases by auto

lemma tf_2: assumes dx: "dim_vec x = 2"
  and be: "x $ 0 = True \<and> x $ 1 = False"
  shows "ceros_of_boolean_input x = {1}"
  using dx be unfolding ceros_of_boolean_input_def using less_2_cases by auto

lemma ft_2: assumes dx: "dim_vec x = 2"
  and be: "x $ 0 = False \<and> x $ 1 = True"
  shows "ceros_of_boolean_input x = {0}"
  using dx be unfolding ceros_of_boolean_input_def using less_2_cases by auto

lemma ff_2: assumes dx: "dim_vec x = 2"
  and be: "x $ 0 = False \<and> x $ 1 = False"
  shows "ceros_of_boolean_input x = {0,1}"
  using dx be unfolding ceros_of_boolean_input_def using less_2_cases by auto

lemma
  assumes dx: "dim_vec x = 2"
  shows "ceros_of_boolean_input x \<in> {{},{0},{1},{0,1}}"
  using dim_vec_2_cases [OF ]
  using tt_2 [OF dx] tf_2 [OF dx] ft_2 [OF dx] ff_2 [OF dx]
  by (metis insertCI)

text\<open>Vectors of dimension $3$.\<close>

lemma less_3_cases:
  assumes n: "n < 3" shows "n = 0 \<or> n = 1 \<or> n = (2::nat)"
  using n by linarith

lemma
  dim_vec_3_cases:
  assumes dx: "dim_vec x = 3"
  shows "(x $ 0 = x $ 1 = x $ 2 = False) \<or> (x $ 0 = x $ 1 = False \<and> x $ 2 = True)
       \<or> (x $ 0 = x $ 2 = False \<and> x $ 1 = True) \<or> (x $ 0 = False \<and> x $ 1 = x $ 2 = True)
       \<or> (x $ 0 = True \<and> x $ 1 = x $ 2 = False) \<or> (x $ 0 = x $ 2 = True \<and> x $ 1 = False)
       \<or> (x $ 0 = x $ 1 = True \<and> x $ 2 = False) \<or> (x $ 0 = x $ 1 = x $ 2 = True)"
  by auto

lemma fff_3: assumes dx: "dim_vec x = 3"
  and be: "x $ 0 = False \<and> x $ 1 = False \<and> x $ 2 = False"
  shows "ceros_of_boolean_input x = {0,1,2}"
  using dx be
  unfolding ceros_of_boolean_input_def
  using less_3_cases by auto

lemma fft_3: assumes dx: "dim_vec x = 3"
  and be: "x $ 0 = False \<and> x $ 1 = False \<and> x $ 2 = True"
  shows "ceros_of_boolean_input x = {0,1}"
  using dx be unfolding ceros_of_boolean_input_def
  using less_3_cases by auto

lemma ftf_3: assumes dx: "dim_vec x = 3"
  and be: "x $ 0 = False \<and> x $ 1 = True \<and> x $ 2 = False"
  shows "ceros_of_boolean_input x = {0,2}"
  using dx be unfolding ceros_of_boolean_input_def
  using less_3_cases by fastforce

lemma ftt_3: assumes dx: "dim_vec x = 3"
  and be: "x $ 0 = False \<and> x $ 1 = True \<and> x $ 2 = True"
  shows "ceros_of_boolean_input x = {0}"
  using dx be unfolding ceros_of_boolean_input_def
  using less_3_cases by auto

lemma tff_3: assumes dx: "dim_vec x = 3"
  and be: "x $ 0 = True \<and> x $ 1 = False \<and> x $ 2 = False"
  shows "ceros_of_boolean_input x = {1,2}"
  using dx be unfolding ceros_of_boolean_input_def
  using less_3_cases by auto

lemma tft_3: assumes dx: "dim_vec x = 3"
  and be: "x $ 0 = True \<and> x $ 1 = False \<and> x $ 2 = True"
  shows "ceros_of_boolean_input x = {1}"
  using dx be unfolding ceros_of_boolean_input_def
  using less_3_cases by auto

lemma ttf_3: assumes dx: "dim_vec x = 3"
  and be: "x $ 0 = True \<and> x $ 1 = True \<and> x $ 2 = False"
  shows "ceros_of_boolean_input x = {2}"
  using dx be unfolding ceros_of_boolean_input_def
  using less_3_cases by fastforce

lemma ttt_3: assumes dx: "dim_vec x = 3"
  and be: "x $ 0 = True \<and> x $ 1 = True \<and> x $ 2 = True"
  shows "ceros_of_boolean_input x = {}"
  using dx be unfolding ceros_of_boolean_input_def
  using less_3_cases by auto

lemma
  assumes dx: "dim_vec x = 3"
  shows "ceros_of_boolean_input x \<in> {{},{0},{1},{2},{0,1},{0,2},{1,2},{0,1,2}}"
  using dim_vec_3_cases [OF ]
  using fff_3 [OF dx] fft_3 [OF dx] ftf_3 [OF dx] ftt_3 [OF dx]
  using tff_3 [OF dx] tft_3 [OF dx] ttf_3 [OF dx] ttt_3 [OF dx]
  by (smt (z3) insertCI)

text\<open>Vectors of dimension $4$.\<close>

lemma less_4_cases:
  assumes n: "n < 4"
  shows "n = 0 \<or> n = 1 \<or> n = 2 \<or> n = (3::nat)"
  using n by linarith

lemma
  dim_vec_4_cases:
  assumes dx: "dim_vec x = 4"
  shows "(x $ 0 = x $ 1 = x $ 2 = x $ 3 = False) \<or> (x $ 0 = x $ 1 = x $ 2 = False \<and> x $ 3 = True)
       \<or> (x $ 0 = x $ 1 = x $ 3 = False \<and> x $ 2 = True) \<or> (x $ 0 = x $ 1 = False \<and> x $ 2 = x $ 3 = True)
       \<or> (x $ 0 = x $ 2 = x $ 3 = False \<and> x $ 1 = True) \<or> (x $ 0 = x $ 2 = False \<and> x $ 1 = x $ 3 = True)
       \<or> (x $ 0 = x $ 3 = False \<and> x $ 1 = x $ 2 = True) \<or> (x $ 0 = False \<and> x $ 1 = x $ 2 = x $ 3 = True)
       \<or> (x $ 0 = True \<and> x $ 1 = x $ 2 = x $ 3 = False) \<or> (x $ 0 = x $ 3 = True \<and> x $ 1 = x $ 2 = False)
       \<or> (x $ 0 = x $ 2 = True \<and> x $ 1 = x $ 3 = False) \<or> (x $ 0 = x $ 2 = x $ 3 = True \<and> x $ 1 = False)
       \<or> (x $ 0 = x $ 1 = True \<and> x $ 2 = x $ 3 = False) \<or> (x $ 0 = x $ 1 = x $ 3 = True \<and> x $ 2 = False)
       \<or> (x $ 0 = x $ 1 = x $ 2 = True \<and> x $ 3 = False) \<or> (x $ 0 = x $ 1 = x $ 2 = x $ 3 = True)"
  by blast

lemma ffff_4: assumes dx: "dim_vec x = 4"
  and be: "x $ 0 = False \<and> x $ 1 = False \<and> x $ 2 = False \<and> x $ 3 = False"
  shows "ceros_of_boolean_input x = {0,1,2,3}"
  using dx be
  unfolding ceros_of_boolean_input_def
  using less_4_cases by auto

lemma ffft_4: assumes dx: "dim_vec x = 4"
  and be: "x $ 0 = False \<and> x $ 1 = False \<and> x $ 2 = False \<and> x $ 3 = True"
  shows "ceros_of_boolean_input x = {0,1,2}"
  using dx be
  unfolding ceros_of_boolean_input_def
  using less_4_cases by auto

lemma fftf_4: assumes dx: "dim_vec x = 4"
  and be: "x $ 0 = False \<and> x $ 1 = False \<and> x $ 2 = True \<and> x $ 3 = False"
  shows "ceros_of_boolean_input x = {0,1,3}"
  using dx be
  unfolding ceros_of_boolean_input_def
  using less_4_cases by auto

lemma fftt_4: assumes dx: "dim_vec x = 4"
  and be: "x $ 0 = False \<and> x $ 1 = False \<and> x $ 2 = True \<and> x $ 3 = True"
  shows "ceros_of_boolean_input x = {0,1}"
  using dx be
  unfolding ceros_of_boolean_input_def
  using less_4_cases by auto

lemma ftff_4: assumes dx: "dim_vec x = 4"
  and be: "x $ 0 = False \<and> x $ 1 = True \<and> x $ 2 = False \<and> x $ 3 = False"
  shows "ceros_of_boolean_input x = {0,2,3}"
  using dx be
  unfolding ceros_of_boolean_input_def
  using less_4_cases by auto

lemma ftft_4: assumes dx: "dim_vec x = 4"
  and be: "x $ 0 = False \<and> x $ 1 = True \<and> x $ 2 = False \<and> x $ 3 = True"
  shows "ceros_of_boolean_input x = {0,2}"
  using dx be
  unfolding ceros_of_boolean_input_def
  using less_4_cases by auto

lemma fttf_4: assumes dx: "dim_vec x = 4"
  and be: "x $ 0 = False \<and> x $ 1 = True \<and> x $ 2 = True \<and> x $ 3 = False"
  shows "ceros_of_boolean_input x = {0,3}"
  using dx be
  unfolding ceros_of_boolean_input_def
  using less_4_cases by auto

lemma fttt_4: assumes dx: "dim_vec x = 4"
  and be: "x $ 0 = False \<and> x $ 1 = True \<and> x $ 2 = True \<and> x $ 3 = True"
  shows "ceros_of_boolean_input x = {0}"
  using dx be
  unfolding ceros_of_boolean_input_def
  using less_4_cases by auto

lemma tfff_4: assumes dx: "dim_vec x = 4"
  and be: "x $ 0 = True \<and> x $ 1 = False \<and> x $ 2 = False \<and> x $ 3 = False"
  shows "ceros_of_boolean_input x = {1,2,3}"
  using dx be
  unfolding ceros_of_boolean_input_def
  using less_4_cases by auto

lemma tfft_4: assumes dx: "dim_vec x = 4"
  and be: "x $ 0 = True \<and> x $ 1 = False \<and> x $ 2 = False \<and> x $ 3 = True"
  shows "ceros_of_boolean_input x = {1,2}"
  using dx be
  unfolding ceros_of_boolean_input_def
  using less_4_cases by auto

lemma tftf_4: assumes dx: "dim_vec x = 4"
  and be: "x $ 0 = True \<and> x $ 1 = False \<and> x $ 2 = True \<and> x $ 3 = False"
  shows "ceros_of_boolean_input x = {1,3}"
  using dx be
  unfolding ceros_of_boolean_input_def
  using less_4_cases by auto

lemma tftt_4: assumes dx: "dim_vec x = 4"
  and be: "x $ 0 = True \<and> x $ 1 = False \<and> x $ 2 = True \<and> x $ 3 = True"
  shows "ceros_of_boolean_input x = {1}"
  using dx be
  unfolding ceros_of_boolean_input_def
  using less_4_cases by auto

lemma ttff_4: assumes dx: "dim_vec x = 4"
  and be: "x $ 0 = True \<and> x $ 1 = True \<and> x $ 2 = False \<and> x $ 3 = False"
  shows "ceros_of_boolean_input x = {2,3}"
  using dx be
  unfolding ceros_of_boolean_input_def
  using less_4_cases by auto

lemma ttft_4: assumes dx: "dim_vec x = 4"
  and be: "x $ 0 = True \<and> x $ 1 = True \<and> x $ 2 = False \<and> x $ 3 = True"
  shows "ceros_of_boolean_input x = {2}"
  using dx be
  unfolding ceros_of_boolean_input_def
  using less_4_cases by auto

lemma tttf_4: assumes dx: "dim_vec x = 4"
  and be: "x $ 0 = True \<and> x $ 1 = True \<and> x $ 2 = True \<and> x $ 3 = False"
  shows "ceros_of_boolean_input x = {3}"
  using dx be
  unfolding ceros_of_boolean_input_def
  using less_4_cases by auto

lemma tttt_4: assumes dx: "dim_vec x = 4"
  and be: "x $ 0 = True \<and> x $ 1 = True \<and> x $ 2 = True \<and> x $ 3 = True"
  shows "ceros_of_boolean_input x = {}"
  using dx be
  unfolding ceros_of_boolean_input_def
  using less_4_cases by auto

lemma
  ceros_of_boolean_input_set:
  assumes dx: "dim_vec x = 4"
  shows "ceros_of_boolean_input x \<in> {{},{0},{1},{2},{3},{0,1},{0,2},{0,3},{1,2},{1,3},{2,3},
    {0,1,2},{0,1,3},{0,2,3},{1,2,3},{0,1,2,3}}"
  using dim_vec_4_cases [OF ]
  using ffff_4 [OF dx] ffft_4 [OF dx] fftf_4 [OF dx] fftt_4 [OF dx]
  using ftff_4 [OF dx] ftft_4 [OF dx] fttf_4 [OF dx] fttt_4 [OF dx]
  using tfff_4 [OF dx] tfft_4 [OF dx] tftf_4 [OF dx] tftt_4 [OF dx]
  using ttff_4 [OF dx] ttft_4 [OF dx] tttf_4 [OF dx] tttt_4 [OF dx]
  by (smt (z3) insertCI)

context simplicial_complex
begin

text\<open>The simplicial complex induced by the monotone Boolean function
  @{const bool_fun_threshold_2_3} has the following explicit expression.\<close>

lemma
  simplicial_complex_induced_by_monotone_boolean_function_4_bool_fun_threshold_2_3:
  shows "{{},{0},{1},{2},{3},{0,1},{0,2},{0,3},{1,2},{1,3},{2,3}}
    = simplicial_complex_induced_by_monotone_boolean_function 4 bool_fun_threshold_2_3"
  (is "{{},?a,?b,?c,?d,?e,?f,?g,?h,?i,?j} = _")
proof (rule)
  show "{{},?a,?b,?c,?d,?e,?f,?g,?h,?i,?j}
    \<subseteq> simplicial_complex_induced_by_monotone_boolean_function 4 bool_fun_threshold_2_3"
    by (simp add:
        empty_set_in_simplicial_complex_induced
        singleton_in_simplicial_complex_induced pair_in_simplicial_complex_induced)+
  show "simplicial_complex_induced_by_monotone_boolean_function 4 bool_fun_threshold_2_3
    \<subseteq> {{},?a,?b,?c,?d,?e,?f,?g,?h,?i,?j}"
      unfolding simplicial_complex_induced_by_monotone_boolean_function_def
      unfolding bool_fun_threshold_2_3_def
    proof
    fix y::"nat set"
    assume y: "y \<in> {y. \<exists>x. dim_vec x = 4 \<and> (if 2 \<le> count_true x then True else False) \<and> ceros_of_boolean_input x = y}"
      then obtain x::"bool vec"
        where ct_ge_2: "(if 2 \<le> count_true x then True else False)"
          and cx: "ceros_of_boolean_input x = y" and dx: "dim_vec x = 4" by auto
      have "count_true x + card (ceros_of_boolean_input x) = dim_vec x"
       using card_ceros_count_UNIV [of x] by simp
      hence "card (ceros_of_boolean_input x) \<le> 2"
        using ct_ge_2
        using card_boolean_function
        using dx by presburger
      hence card_le: "card y \<le> 2" using cx by simp
      have "y \<in> {{},?a,?b,?c,?d,?e,?f,?g,?h,?i,?j}"
      proof (rule ccontr)
        assume "y \<notin> {{},?a,?b,?c,?d,?e,?f,?g,?h,?i,?j}"
        then have y_nin: "y \<notin> set [{},?a,?b,?c,?d,?e,?f,?g,?h,?i,?j]" by simp
        have "y \<in> set [{0,1,2},{0,1,3},{0,2,3},{1,2,3},{0,1,2,3}]"
          using ceros_of_boolean_input_set [OF dx] y_nin
          unfolding cx by simp
        hence "card y \<ge> 3" by auto
        thus False using card_le by simp
      qed
      then show "y \<in> {{},?a,?b,?c,?d,?e,?f,?g,?h,?i,?j}"
      by simp
  qed
qed

end

end
