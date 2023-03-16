section \<open>Algebra-only Theorems\<close>

text \<open>This section verifies the linear algebraic counter-parts of the graph-theoretic theorems
about Random walks. The graph-theoretic results are then derived in Section~\ref{sec:random_walks}.\<close>

theory Expander_Graphs_Algebra
  imports 
    "HOL-Library.Monad_Syntax"
    Expander_Graphs_TTS
begin

lemma pythagoras: 
  fixes v w :: "'a::real_inner"
  assumes "v \<bullet> w  = 0"
  shows "norm (v+w)^2 = norm v^2 + norm w^2"  
  using assms by (simp add:power2_norm_eq_inner algebra_simps inner_commute)

definition diag :: "('a :: zero)^'n \<Rightarrow> 'a^'n^'n"
  where "diag v = (\<chi> i j. if i = j then (v $ i) else 0)"

definition ind_vec :: "'n set \<Rightarrow> real^'n"
  where "ind_vec S = (\<chi> i. of_bool( i \<in> S))"

lemma diag_mult_eq: "diag x ** diag y = diag (x * y)"
  unfolding diag_def 
  by (vector matrix_matrix_mult_def) 
   (auto simp add:if_distrib if_distribR sum.If_cases)

lemma diag_vec_mult_eq: "diag x *v y = x * y"
  unfolding diag_def matrix_vector_mult_def 
  by (simp add:if_distrib if_distribR sum.If_cases times_vec_def)

definition matrix_norm_bound :: "real^'n^'m \<Rightarrow> real \<Rightarrow> bool"
  where "matrix_norm_bound A l = (\<forall>x. norm (A *v x) \<le> l * norm x)"

lemma  matrix_norm_boundI:
  assumes "\<And>x. norm (A *v x) \<le> l * norm x"
  shows "matrix_norm_bound A l"
  using assms unfolding matrix_norm_bound_def by simp

lemma matrix_norm_boundD:
  assumes "matrix_norm_bound A l"
  shows "norm (A *v x) \<le> l * norm x"
  using assms unfolding matrix_norm_bound_def by simp

lemma matrix_norm_bound_nonneg:
  fixes A :: "real^'n^'m"
  assumes "matrix_norm_bound A l"
  shows "l \<ge> 0" 
proof -
  have "0 \<le> norm (A *v 1)" by simp
  also have "... \<le> l * norm (1::real^'n)" 
    using assms(1) unfolding matrix_norm_bound_def by simp
  finally have "0 \<le> l  * norm (1::real^'n)"
    by simp
  moreover have "norm (1::real^'n) > 0"
    by simp
  ultimately show ?thesis 
    by (simp add: zero_le_mult_iff)
qed

lemma  matrix_norm_bound_0: 
  assumes "matrix_norm_bound A 0" 
  shows "A = (0::real^'n^'m)"
proof (intro iffD2[OF matrix_eq] allI)
  fix x :: "real^'n"
  have "norm (A *v x) = 0"
    using assms unfolding matrix_norm_bound_def by simp
  thus "A *v x = 0 *v x"
    by simp
qed

lemma matrix_norm_bound_diag:
  fixes x :: "real^'n"
  assumes "\<And>i. \<bar>x $ i\<bar> \<le> l"
  shows "matrix_norm_bound (diag x) l"
proof (rule matrix_norm_boundI)
  fix y :: "real^'n"

  have l_ge_0: "l \<ge> 0" using assms by fastforce

  have a: "\<bar>x $ i * v\<bar> \<le> \<bar>l * v\<bar>" for v i
    using l_ge_0 assms by (simp add:abs_mult mult_right_mono)

  have "norm (diag x *v y) = sqrt (\<Sum>i \<in> UNIV. (x $ i * y $ i)^2)"
    unfolding matrix_vector_mult_def diag_def norm_vec_def L2_set_def
    by (auto simp add:if_distrib if_distribR sum.If_cases)
  also have "... \<le> sqrt (\<Sum>i \<in> UNIV. (l * y $ i)^2)"
    by (intro real_sqrt_le_mono sum_mono iffD1[OF abs_le_square_iff] a)
  also have "... = l * norm y"
    using l_ge_0 by (simp add:norm_vec_def L2_set_def algebra_simps 
        sum_distrib_left[symmetric] real_sqrt_mult)
  finally show "norm (diag x *v y) \<le> l * norm y" by simp
qed

lemma vector_scaleR_matrix_ac_2: "b *\<^sub>R (A::real^'n^'m) *v x = b *\<^sub>R (A *v x)" 
  unfolding vector_transpose_matrix[symmetric]  transpose_scalar
  by (intro vector_scaleR_matrix_ac)

lemma  matrix_norm_bound_scale: 
  assumes "matrix_norm_bound A l"
  shows "matrix_norm_bound (b *\<^sub>R A) (\<bar>b\<bar> * l)"
proof (intro matrix_norm_boundI)
  fix x
  have "norm (b *\<^sub>R A *v x) = norm (b *\<^sub>R (A *v x))" 
    by (metis transpose_scalar vector_scaleR_matrix_ac vector_transpose_matrix)
  also have "... = \<bar>b\<bar> * norm (A *v x)" 
    by simp
  also have "... \<le> \<bar>b\<bar> * (l * norm x)"
    using assms matrix_norm_bound_def by (intro mult_left_mono) auto
  also have "... \<le> (\<bar>b\<bar> * l) * norm x" by simp
  finally show "norm (b *\<^sub>R A *v x) \<le> (\<bar>b\<bar> * l) * norm x" by simp
qed

definition nonneg_mat :: "real^'n^'m \<Rightarrow> bool"
  where "nonneg_mat A = (\<forall>i j. A $ i $ j \<ge> 0)"

lemma nonneg_mat_1:
  shows "nonneg_mat (mat 1)"
  unfolding nonneg_mat_def mat_def by auto

lemma nonneg_mat_prod:
  assumes "nonneg_mat A" "nonneg_mat B"
  shows "nonneg_mat (A ** B)"
  using assms unfolding nonneg_mat_def matrix_matrix_mult_def 
  by (auto intro:sum_nonneg)

lemma nonneg_mat_transpose:
  "nonneg_mat (transpose A) = nonneg_mat A"
  unfolding nonneg_mat_def transpose_def 
  by auto

definition spec_bound :: "real^'n^'n \<Rightarrow> real \<Rightarrow> bool"
  where "spec_bound M l = (l \<ge> 0 \<and> (\<forall>v. v \<bullet> 1 = 0 \<longrightarrow> norm (M *v v) \<le> l * norm v))"

lemma spec_boundD1:
  assumes "spec_bound M l"
  shows "0 \<le> l" 
  using assms unfolding spec_bound_def by simp

lemma spec_boundD2:
  assumes "spec_bound M l"
  assumes "v \<bullet> 1 = 0 "
  shows "norm (M *v v) \<le> l * norm v" 
  using assms unfolding spec_bound_def by simp

lemma spec_bound_mono:
  assumes "spec_bound M \<alpha>" "\<alpha> \<le> \<beta>"
  shows "spec_bound M \<beta>"
proof -
  have "norm (M *v v) \<le> \<beta> * norm v" if "inner v 1 = 0"  for v
  proof -
    have "norm (M *v v) \<le> \<alpha> * norm v" 
      by (intro spec_boundD2[OF assms(1)] that)
    also have "... \<le> \<beta> * norm v"
      by (intro mult_right_mono assms(2)) auto
    finally show ?thesis by simp
  qed
  moreover have "\<beta> \<ge> 0"
    using assms(2) spec_boundD1[OF assms(1)] by simp
  ultimately show ?thesis 
    unfolding spec_bound_def by simp
qed

definition markov :: "real^'n^'n \<Rightarrow> bool"
  where "markov M = (nonneg_mat M \<and> M *v 1  = 1 \<and> 1 v* M = 1)"

lemma markov_symI:
  assumes "nonneg_mat A" "transpose A = A" "A *v 1 = 1"
  shows "markov A"
proof -
  have "1 v* A = transpose A *v 1"
    unfolding vector_transpose_matrix[symmetric] by simp
  also have "... = 1" unfolding assms(2,3) by simp
  finally have "1 v* A = 1" by simp
  thus ?thesis
    unfolding markov_def using assms by auto
qed

lemma markov_apply:
  assumes "markov M"
  shows "M *v 1 = 1" "1 v* M = 1"
  using assms unfolding markov_def by auto

lemma markov_transpose:
  "markov A = markov (transpose A)"
  unfolding markov_def nonneg_mat_transpose by auto
fun matrix_pow where 
  "matrix_pow M 0 = mat 1" |
  "matrix_pow M (Suc n) = M ** (matrix_pow M n)"

lemma markov_orth_inv: 
  assumes "markov A"
  shows "inner (A *v x) 1 = inner x 1"
proof -
  have "inner (A *v x) 1 = inner x (1 v* A)"
    using dot_lmul_matrix inner_commute by metis
  also have "... = inner x 1"
    using markov_apply[OF assms(1)] by simp
  finally show ?thesis by simp
qed

lemma markov_id:
  "markov (mat 1)"
  unfolding markov_def using nonneg_mat_1 by simp

lemma markov_mult:
  assumes "markov A" "markov B"
  shows "markov (A ** B)"
proof -
  have "nonneg_mat (A ** B)"
    using assms unfolding markov_def by (intro nonneg_mat_prod) auto
  moreover have "(A ** B) *v 1 = 1" 
    using assms unfolding markov_def
    unfolding matrix_vector_mul_assoc[symmetric] by simp
  moreover have "1 v* (A ** B) = 1" 
    using assms unfolding markov_def
    unfolding vector_matrix_mul_assoc[symmetric] by simp
  ultimately show ?thesis
    unfolding markov_def by simp
qed

lemma markov_matrix_pow:
  assumes "markov A"
  shows "markov (matrix_pow A k)"
  using markov_id assms markov_mult
  by (induction k, auto)

lemma spec_bound_prod: 
  assumes "markov A" "markov B"
  assumes "spec_bound A la" "spec_bound B lb"
  shows "spec_bound (A ** B) (la*lb)"
proof -
  have la_ge_0: "la \<ge> 0" using spec_boundD1[OF assms(3)] by simp

  have "norm ((A ** B) *v x) \<le> (la * lb) * norm x" if "inner x 1 = 0" for x
  proof -
    have "norm ((A ** B) *v x) = norm (A *v (B *v x))"
      by (simp add:matrix_vector_mul_assoc)
    also have "... \<le> la * norm (B *v x)"
      by (intro spec_boundD2[OF assms(3)]) (simp add:markov_orth_inv that assms(2))
    also have "... \<le> la * (lb * norm x)" 
      by (intro spec_boundD2[OF assms(4)] mult_left_mono that la_ge_0)
    finally show ?thesis by simp
  qed
  moreover have "la * lb \<ge> 0"
    using la_ge_0 spec_boundD1[OF assms(4)] by simp
  ultimately show ?thesis
    using spec_bound_def by auto
qed

lemma spec_bound_pow: 
  assumes "markov A"
  assumes "spec_bound A l"
  shows "spec_bound (matrix_pow A k) (l^k)"
proof (induction k)
  case 0
  then show ?case unfolding spec_bound_def by simp
next
  case (Suc k)
  have "spec_bound (A ** matrix_pow A k) (l * l ^ k)"
    by (intro spec_bound_prod assms Suc markov_matrix_pow)
  thus ?case by simp
qed

fun intersperse :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list"
  where 
    "intersperse x [] = []" |
    "intersperse x (y#[]) = y#[]" |
    "intersperse x (y#z#zs) = y#x#intersperse x (z#zs)"

lemma intersperse_snoc:
  assumes "xs \<noteq> []"
  shows "intersperse z (xs@[y]) = intersperse z xs@[z,y]"
  using assms
proof (induction xs rule:list_nonempty_induct)
  case (single x)
  then show ?case by simp
next
  case (cons x xs)
  then obtain xsh xst where t:"xs = xsh#xst"
    by (metis neq_Nil_conv)
  have "intersperse z ((x # xs) @ [y]) = x#z#intersperse z (xs@[y])"
    unfolding t by simp
  also have "... = x#z#intersperse z xs@[z,y]"
    using cons by simp
  also have "... = intersperse z (x#xs)@[z,y]"
    unfolding t by simp
  finally show ?case by simp
qed

lemma foldl_intersperse:
  assumes "xs \<noteq> []"
  shows "foldl f a ((intersperse x xs)@[x]) = foldl (\<lambda>y z. f (f y z) x) a xs"
  using assms by (induction xs rule:rev_nonempty_induct) (auto simp add:intersperse_snoc)

lemma foldl_intersperse_2:
  shows "foldl f a (intersperse y (x#xs)) = foldl (\<lambda>x z. f (f x y) z) (f a x) xs"
proof (induction xs rule:rev_induct)
  case Nil
  then show ?case by simp
next
  case (snoc xst xs)
  have "foldl f a (intersperse y ((x # xs) @ [xst])) = foldl (\<lambda>x. f (f x y)) (f a x) (xs @ [xst])" 
    by (subst intersperse_snoc, auto simp add:snoc)
  then show ?case  by simp
qed


context regular_graph_tts
begin

definition stat :: "real^'n"
  where "stat = (1 / real CARD('n)) *\<^sub>R 1"

definition J :: "('c :: field)^'n^'n"
  where "J = (\<chi> i j. of_nat 1 / of_nat CARD('n))"

lemma inner_1_1: "1 \<bullet> (1::real^'n) = CARD('n)"
  unfolding inner_vec_def by simp

definition proj_unit :: "real^'n \<Rightarrow> real^'n"
  where "proj_unit v = (1 \<bullet> v) *\<^sub>R stat"

definition proj_rem :: "real^'n \<Rightarrow> real^'n" 
  where "proj_rem v = v - proj_unit v"

lemma proj_rem_orth: "1 \<bullet> (proj_rem v) = 0"
  unfolding proj_rem_def proj_unit_def inner_diff_right stat_def
  by (simp add:inner_1_1)

lemma split_vec: "v = proj_unit v + proj_rem v" 
  unfolding proj_rem_def by simp

lemma apply_J: "J *v x = proj_unit x"
proof (intro iffD2[OF vec_eq_iff] allI)
  fix i
  have "(J *v x) $ i = inner (\<chi> j. 1 / real CARD('n)) x" 
    unfolding matrix_vector_mul_component J_def by simp
  also have "... = inner stat x"
    unfolding stat_def scaleR_vec_def by auto
  also have "... = (proj_unit x) $ i"
    unfolding proj_unit_def stat_def by simp
  finally show "(J *v x) $ i = (proj_unit x) $ i" by simp
qed 

lemma spec_bound_J: "spec_bound (J :: real^'n^'n) 0"
proof -
  have "norm (J *v v) = 0" if "inner v 1 = 0" for v :: "real^'n"
  proof -
    have "inner (proj_unit v + proj_rem v) 1 = 0"
      using that by (subst (asm) split_vec[of "v"], simp)
    hence "inner (proj_unit v) 1 = 0"
      using proj_rem_orth inner_commute unfolding inner_add_left 
      by (metis add_cancel_left_right)
    hence "proj_unit v = 0"
      unfolding proj_unit_def stat_def by simp
    hence "J *v v = 0"
      unfolding apply_J by simp
    thus ?thesis by simp
  qed
  thus ?thesis
    unfolding spec_bound_def by simp
qed

lemma matrix_decomposition_lemma_aux:
  fixes A :: "real^'n^'n"
  assumes "markov A"
  shows "spec_bound A l \<longleftrightarrow> matrix_norm_bound (A - (1-l) *\<^sub>R J) l" (is "?L \<longleftrightarrow> ?R")
proof 
  assume a:"?L"
  hence l_ge_0: "l \<ge> 0" using spec_boundD1 by auto 
  show "?R" 
  proof (rule matrix_norm_boundI)
    fix x :: "real^'n"
    have "(A - (1-l) *\<^sub>R J) *v x = A *v x - (1-l) *\<^sub>R (proj_unit x)"
      by (simp add:algebra_simps vector_scaleR_matrix_ac_2 apply_J)
    also have "... = A *v proj_unit x + A *v proj_rem x - (1-l) *\<^sub>R (proj_unit x)"
      by (subst split_vec[of "x"], simp add:algebra_simps)
    also have "... = proj_unit x + A *v proj_rem x - (1-l) *\<^sub>R (proj_unit x)"
      using markov_apply[OF assms(1)]
      unfolding proj_unit_def stat_def by (simp add:algebra_simps)
    also have "... = A *v proj_rem x + l *\<^sub>R proj_unit x" (is "_ = ?R1")
      by (simp add:algebra_simps)
    finally have d:"(A - (1-l) *\<^sub>R J) *v x = ?R1" by simp

    have "inner (l *\<^sub>R proj_unit x) (A *v proj_rem x) = 
      inner ((l * inner 1 x / real CARD('n)) *\<^sub>R 1 v* A) (proj_rem x)"
      by (subst dot_lmul_matrix[symmetric]) (simp add:proj_unit_def stat_def) 
    also have "... = (l * inner 1 x / real CARD('n)) * inner 1 (proj_rem x)" 
      unfolding scaleR_vector_matrix_assoc markov_apply[OF assms] by simp
    also have "... = 0"
      unfolding proj_rem_orth by simp
    finally have b:"inner (l *\<^sub>R proj_unit x) (A *v proj_rem x) = 0" by simp

    have c: "inner (proj_rem x) (proj_unit x) = 0" 
      using proj_rem_orth[of "x"]
      unfolding proj_unit_def stat_def by (simp add:inner_commute)

    have "norm (?R1)^2 = norm (A *v proj_rem x)^2 + norm (l *\<^sub>R proj_unit x)^2" 
      using b by (intro pythagoras) (simp add:inner_commute)
    also have "... \<le> (l * norm (proj_rem x))^2 + norm (l *\<^sub>R proj_unit x)^2" 
      using proj_rem_orth[of "x"]
      by (intro add_mono power_mono spec_boundD2 a) (auto simp add:inner_commute)
    also have "... = l^2 * (norm (proj_rem x)^2 + norm (proj_unit x)^2)"
      by (simp add:algebra_simps)
    also have "... = l^2 * (norm (proj_rem x + proj_unit x)^2)"
      using c by (subst pythagoras) auto
    also have "... = l^2 * norm x^2"
      by (subst (3) split_vec[of "x"]) (simp add:algebra_simps)
    also have "... = (l * norm x)^2"
      by (simp add:algebra_simps)
    finally have "norm (?R1)^2 \<le> (l * norm x)^2" by simp
    hence "norm (?R1) \<le> l * norm x"
      using l_ge_0 by (subst (asm) power_mono_iff) auto

    thus "norm ((A - (1-l) *\<^sub>R J) *v x) \<le> l * norm x"
      unfolding d by simp
  qed
next  
  assume a:"?R" 
  have "norm (A *v x) \<le> l * norm x" if "inner x 1 = 0" for x 
  proof -
    have "(1 - l) *\<^sub>R J *v x = (1 - l) *\<^sub>R (proj_unit x)" 
      by (simp add:vector_scaleR_matrix_ac_2 apply_J)
    also have "... = 0"
      unfolding proj_unit_def using that by (simp add:inner_commute)
    finally have b: "(1 - l) *\<^sub>R J *v x = 0" by simp

    have "norm (A *v x) = norm ((A - (1-l) *\<^sub>R J) *v x  + ((1-l) *\<^sub>R J) *v x)"
      by (simp add:algebra_simps)
    also have "... \<le> norm ((A - (1-l) *\<^sub>R J) *v x) + norm (((1-l) *\<^sub>R J) *v x)"
      by (intro norm_triangle_ineq)
    also have "... \<le> l * norm x + 0"
      using a b unfolding  matrix_norm_bound_def by (intro add_mono, auto)
    also have "... = l * norm x"
      by simp
    finally show ?thesis by simp
  qed

  moreover have "l \<ge> 0" 
    using a matrix_norm_bound_nonneg by blast

  ultimately show "?L" 
    unfolding spec_bound_def by simp
qed

lemma matrix_decomposition_lemma:
  fixes A :: "real^'n^'n"
  assumes "markov A"
  shows "spec_bound A l \<longleftrightarrow> (\<exists>E. A = (1-l) *\<^sub>R J + l *\<^sub>R E \<and> matrix_norm_bound E 1 \<and> l \<ge> 0)" 
    (is "?L \<longleftrightarrow> ?R")
proof -
  have "?L \<longleftrightarrow> matrix_norm_bound (A - (1-l) *\<^sub>R J) l" 
    using matrix_decomposition_lemma_aux[OF assms] by simp
  also have "... \<longleftrightarrow> ?R"
  proof
    assume a:"matrix_norm_bound (A - (1 - l) *\<^sub>R J) l"
    hence l_ge_0: "l \<ge> 0" using matrix_norm_bound_nonneg by auto
    define E where "E = (1/l) *\<^sub>R (A - (1-l) *\<^sub>R J)"
    have "A = J" if "l = 0" 
    proof -
      have "matrix_norm_bound (A - J) 0"
        using a that by simp
      hence "A - J = 0" using matrix_norm_bound_0 by blast
      thus "A = J" by simp
    qed
    hence "A = (1-l) *\<^sub>R J + l *\<^sub>R E"
      unfolding E_def by simp
    moreover have "matrix_norm_bound E 1" 
    proof (cases "l = 0")
      case True
      hence "E = 0" if "l = 0"
        unfolding E_def by simp
      thus "matrix_norm_bound E 1" if "l = 0"
        using that unfolding matrix_norm_bound_def by auto
    next
      case False
      hence "l > 0" using l_ge_0 by simp
      moreover have "matrix_norm_bound E (\<bar>1 / l\<bar>* l)"
        unfolding E_def
        by (intro matrix_norm_bound_scale a)
      ultimately show ?thesis by auto
    qed
    ultimately show ?R using l_ge_0 by auto
  next
    assume a:?R
    then obtain E where E_def: "A = (1 - l) *\<^sub>R J + l *\<^sub>R E"  "matrix_norm_bound E 1" "l \<ge> 0"
      by auto
    have "matrix_norm_bound (l *\<^sub>R E) (abs l*1)" 
      by (intro matrix_norm_bound_scale E_def(2))
    moreover have "l \<ge> 0" using E_def by simp 
    moreover have " l *\<^sub>R E = (A - (1 - l) *\<^sub>R J)" 
      using E_def(1) by simp
    ultimately show "matrix_norm_bound (A - (1 - l) *\<^sub>R J) l"
      by simp  
  qed
  finally show ?thesis by simp
qed

lemma hitting_property_alg:
  fixes S :: "('n :: finite) set"
  assumes l_range: "l \<in> {0..1}"
  defines "P \<equiv> diag (ind_vec S)"
  defines "\<mu> \<equiv> card S / CARD('n)"
  assumes "\<And>M. M \<in> set Ms \<Longrightarrow> spec_bound M l \<and> markov M"
  shows "foldl (\<lambda>x M. P *v (M *v x)) (P *v stat) Ms \<bullet> 1 \<le> (\<mu> + l * (1-\<mu>))^(length Ms+1)"
proof -
  define t :: "real^'n" where "t = (\<chi> i. of_bool (i \<in> S))"
  define r where "r = foldl (\<lambda>x M. P *v (M *v x)) (P *v stat) Ms"
  have P_proj: "P ** P = P"
    unfolding P_def diag_mult_eq ind_vec_def by (intro arg_cong[where f="diag"]) (vector)

  have P_1_left: "1 v* P = t"
    unfolding P_def diag_def ind_vec_def vector_matrix_mult_def t_def by simp

  have P_1_right: "P *v 1 = t"
    unfolding P_def diag_def ind_vec_def matrix_vector_mult_def t_def by simp

  have P_norm :"matrix_norm_bound P 1"
    unfolding P_def ind_vec_def by (intro matrix_norm_bound_diag) simp

  have norm_t: "norm t = sqrt (real (card S))" 
    unfolding t_def norm_vec_def L2_set_def of_bool_def
    by (simp add:sum.If_cases if_distrib if_distribR)

  have \<mu>_range: "\<mu> \<ge> 0" "\<mu> \<le> 1" 
    unfolding \<mu>_def by (auto simp add:card_mono) 

  define condition :: "real^'n \<Rightarrow> nat \<Rightarrow> bool" 
    where "condition = (\<lambda>x n. norm x \<le> (\<mu> + l * (1-\<mu>))^n * sqrt (card S)/CARD('n) \<and> P *v x = x)" 

  have a:"condition r (length Ms)"
    unfolding r_def using assms(4)
  proof (induction Ms rule:rev_induct)
    case Nil
    have "norm (P *v stat) = (1 / real CARD('n)) * norm t"
      unfolding stat_def matrix_vector_mult_scaleR P_1_right by simp
    also have "... \<le>  (1 / real CARD('n)) * sqrt (real (card S))"
      using  norm_t by (intro mult_left_mono) auto
    also have "... = sqrt (card S)/CARD('n)" by simp
    finally have "norm (P *v stat) \<le> sqrt (card S)/CARD('n)" by simp
    moreover have "P *v (P *v stat) = P *v stat"
      unfolding matrix_vector_mul_assoc P_proj by simp
    ultimately show ?case unfolding condition_def by simp
  next
    case (snoc M xs)
    hence "spec_bound M l \<and> markov M"
        using snoc(2) by simp
    then obtain E where E_def: "M = (1-l) *\<^sub>R J + l *\<^sub>R E" "matrix_norm_bound E 1" 
      using iffD1[OF matrix_decomposition_lemma] by auto

    define y where "y = foldl (\<lambda>x M. P *v (M *v x)) (P *v stat) xs"
    have b:"condition y (length xs)"
      using snoc unfolding y_def by simp
    hence a:"P *v y = y" using condition_def by simp

    have "norm (P *v (M *v y)) = norm (P *v ((1-l)*\<^sub>R J *v y) + P *v (l *\<^sub>R E *v y))"
      by (simp add:E_def algebra_simps)
    also have "... \<le> norm (P *v ((1-l)*\<^sub>R J *v y)) + norm (P *v (l *\<^sub>R E *v y)) "
      by (intro norm_triangle_ineq)
    also have "... = (1 - l) * norm (P *v (J *v y)) + l * norm (P *v (E *v y))"
      using l_range
      by (simp add:vector_scaleR_matrix_ac_2 matrix_vector_mult_scaleR)
    also have "... = (1-l) * \<bar>1 \<bullet> (P *v y)/real CARD('n)\<bar> * norm t + l * norm (P *v (E *v y))"
      by (subst a[symmetric]) 
        (simp add:apply_J proj_unit_def stat_def P_1_right matrix_vector_mult_scaleR)
    also have "... = (1-l) * \<bar>t \<bullet> y\<bar>/real CARD('n) * norm t + l * norm (P *v (E *v y))"
      by (subst dot_lmul_matrix[symmetric]) (simp add:P_1_left)
    also have "... \<le> (1-l) * (norm t * norm y) / real CARD('n) * norm t + l * (1 * norm (E *v y))"
      using P_norm Cauchy_Schwarz_ineq2 l_range
      by (intro add_mono mult_right_mono mult_left_mono divide_right_mono matrix_norm_boundD) auto
    also have "... = (1-l) * \<mu> * norm y + l * norm (E *v y)"
      unfolding \<mu>_def norm_t by simp
    also have "... \<le> (1-l) * \<mu> * norm y + l * (1 * norm y)"
      using \<mu>_range l_range
      by (intro add_mono matrix_norm_boundD mult_left_mono E_def) auto
    also have "... = (\<mu> + l * (1-\<mu>)) * norm y"
      by (simp add:algebra_simps)
    also have "... \<le> (\<mu> + l * (1-\<mu>)) * ((\<mu> + l * (1-\<mu>))^length xs * sqrt (card S)/CARD('n))"
      using b \<mu>_range l_range unfolding condition_def
      by (intro mult_left_mono) auto
    also have "... = (\<mu> + l * (1-\<mu>))^(length xs +1) * sqrt (card S)/CARD('n)"
      by simp
    finally have "norm (P *v (M *v y)) \<le> (\<mu> + l * (1-\<mu>))^(length xs +1) * sqrt (card S)/CARD('n)"
      by simp

    moreover have "P *v (P *v (M *v y)) = P *v (M *v y)"
      unfolding matrix_vector_mul_assoc matrix_mul_assoc P_proj 
      by simp

    ultimately have "condition (P *v (M *v y)) (length (xs@[M]))"
      unfolding condition_def by simp
  
    then show ?case 
      unfolding y_def by simp
  qed

  have "inner r 1 = inner (P *v r) 1"
    using a condition_def by simp
  also have "... = inner (1 v* P) r"
    unfolding dot_lmul_matrix by (simp add:inner_commute)
  also have "... = inner t r"
    unfolding P_1_left by simp
  also have "... \<le> norm t * norm r"
    by (intro norm_cauchy_schwarz)
  also have "... \<le> sqrt (card S) * ((\<mu> + l * (1-\<mu>))^(length Ms) * sqrt(card S)/CARD('n))"
    using a unfolding condition_def norm_t
    by (intro mult_mono) auto
  also have "... = (\<mu> + 0) * ((\<mu> + l * (1-\<mu>))^(length Ms))"
    by (simp add:\<mu>_def)
  also have "... \<le> (\<mu> + l * (1-\<mu>)) * (\<mu> + l * (1-\<mu>))^(length Ms)"
    using \<mu>_range l_range
    by (intro mult_right_mono zero_le_power add_mono) auto
  also have "... = (\<mu> + l * (1-\<mu>))^(length Ms+1)" by simp
  finally show ?thesis 
    unfolding r_def by simp
qed

lemma upto_append:
  assumes "i \<le> j" "j \<le> k"
  shows  "[i..<j]@[j..<k] = [i..<k]"
  using assms by (metis less_eqE upt_add_eq_append)

definition bool_list_split :: "bool list \<Rightarrow> (nat list \<times> nat)"
  where "bool_list_split xs = foldl (\<lambda>(ys,z) x. (if x then (ys@[z],0) else (ys,z+1))) ([],0) xs" 

lemma bool_list_split:
  assumes "bool_list_split xs = (ys,z)"
  shows "xs = concat (map (\<lambda>k. replicate k False@[True]) ys)@replicate z False"
  using assms
proof (induction xs arbitrary: ys z rule:rev_induct)
  case Nil
  then show ?case unfolding bool_list_split_def by simp
next
  case (snoc x xs)
  obtain u v where uv_def: "bool_list_split xs = (u,v)" 
    by (metis surj_pair)

  show ?case 
  proof (cases x)
    case True
    have a:"ys = u@[v]" "z = 0"
      using snoc(2) True uv_def unfolding bool_list_split_def by auto
    have "xs@[x] = concat (map (\<lambda>k. replicate k False@[True]) u)@replicate v False@[True]"
      using snoc(1)[OF uv_def] True by simp
    also have "... = concat (map (\<lambda>k. replicate k False@[True]) (u@[v]))@replicate 0 False"
      by simp
    also have "... = concat (map (\<lambda>k. replicate k False@[True]) (ys))@replicate z False"
      using a by simp
    finally show ?thesis by simp
  next
    case False
    have a:"ys = u" "z = v+1"
      using snoc(2) False uv_def unfolding bool_list_split_def by auto
    have "xs@[x] = concat (map (\<lambda>k. replicate k False@[True]) u)@replicate (v+1) False"
      using snoc(1)[OF uv_def] False unfolding replicate_add by simp
    also have "... = concat (map (\<lambda>k. replicate k False@[True]) (ys))@replicate z False"
      using a by simp
    finally show ?thesis by simp
  qed
qed

lemma bool_list_split_count:
  assumes "bool_list_split xs = (ys,z)"
  shows "length (filter id xs) = length ys"
  unfolding bool_list_split[OF assms(1)] by (simp add:filter_concat comp_def)

lemma foldl_concat:
  "foldl f a (concat xss) = foldl (\<lambda>y xs. foldl f y xs) a xss"
  by (induction xss rule:rev_induct, auto)

lemma hitting_property_alg_2:
  fixes S :: "('n :: finite) set" and l :: nat 
  fixes M :: "real^'n^'n"
  assumes \<alpha>_range: "\<alpha> \<in> {0..1}"
  assumes "I \<subseteq> {..<l}"
  defines "P i \<equiv> (if i \<in> I then diag (ind_vec S) else mat 1)"
  defines "\<mu> \<equiv> real (card S) / real (CARD('n))"
  assumes "spec_bound M \<alpha>" "markov M"
  shows 
    "foldl (\<lambda>x M. M *v x) stat (intersperse M (map P [0..<l])) \<bullet> 1 \<le> (\<mu>+\<alpha>*(1-\<mu>))^card I"
    (is "?L \<le> ?R")
proof (cases "I \<noteq> {}")
  case True
  define xs where "xs = map (\<lambda>i. i \<in> I) [0..<l]"
  define Q where "Q = diag (ind_vec S)"
  define P' where "P' = (\<lambda>x. if x then Q else mat 1)"

  let ?rep = "(\<lambda>x. replicate x (mat 1))"

  have P_eq: "P i = P' (i \<in> I)" for i
    unfolding P_def P'_def Q_def by simp

  have "l > 0" 
    using True assms(2) by auto
  hence xs_ne: "xs \<noteq> []" 
    unfolding xs_def by simp

  obtain ys z where ys_z: "bool_list_split xs = (ys,z)"
    by (metis surj_pair)


  have "length ys = length (filter id xs)" 
    using bool_list_split_count[OF ys_z] by simp
  also have "... = card (I \<inter> {0..<l})"
    unfolding xs_def filter_map by (simp add:comp_def distinct_length_filter)
  also have "... = card I"
    using Int_absorb2[OF assms(2)] unfolding atLeast0LessThan by simp
  finally have  len_ys: "length ys = card I" by simp

  hence "length ys > 0"
    using True assms(2) by (metis card_gt_0_iff finite_nat_iff_bounded)
  then obtain yh yt where ys_split: "ys = yh#yt" 
    by (metis length_greater_0_conv neq_Nil_conv)

  have a:"foldl (\<lambda>x N. M *v (N *v x)) x (?rep z) \<bullet> 1 = x \<bullet> 1" for x
  proof (induction z)
    case 0
    then show ?case by simp
  next
    case (Suc z)
    have "foldl (\<lambda>x N. M *v (N *v x)) x (?rep (z+1)) \<bullet> 1 = x \<bullet> 1"
      unfolding replicate_add using Suc 
      by (simp add:markov_orth_inv[OF assms(6)])
    then show ?case by simp
  qed

  have "M *v stat = stat" 
    using assms(6) unfolding stat_def matrix_vector_mult_scaleR markov_def by simp
  hence b: "foldl (\<lambda>x N. M *v (N *v x)) stat (?rep yh) = stat"
    by (induction yh, auto)

  have "foldl (\<lambda>x N. N *v (M *v x)) a (?rep x) = matrix_pow M x *v a" for x a
  proof (induction x)
    case 0
    then show ?case by simp
  next
    case (Suc x)
    have "foldl (\<lambda>x N. N *v (M *v x)) a (?rep (x+1)) =  matrix_pow M (x+1) *v a"
      unfolding replicate_add using Suc by (simp add: matrix_vector_mul_assoc)
    then show ?case by simp
  qed
  hence c: "foldl (\<lambda>x N. N *v (M *v x)) a (?rep x @ [Q]) = Q *v (matrix_pow M (x+1) *v a)" for x a
    by (simp add:matrix_vector_mul_assoc matrix_mul_assoc)

  have d: "spec_bound N \<alpha> \<and> markov N" if t1: "N \<in> set (map (\<lambda>x. matrix_pow M (x + 1)) yt)" for N
  proof -
    obtain y where N_def: "N = matrix_pow M (y+1)"
      using t1 by auto
    hence d1: "spec_bound N (\<alpha>^(y+1))"
      unfolding N_def using spec_bound_pow assms(5,6) by blast
    have "spec_bound N (\<alpha>^1)" 
      using \<alpha>_range by (intro spec_bound_mono[OF d1] power_decreasing) auto 
    moreover have "markov N"
      unfolding N_def by (intro markov_matrix_pow assms(6))
    ultimately show ?thesis by simp
  qed

  have "?L = foldl (\<lambda>x M. M *v x) stat (intersperse M (map P' xs)) \<bullet> 1"
    unfolding P_eq xs_def map_map by (simp add:comp_def)
  also have "... = foldl (\<lambda>x M. M *v x) stat (intersperse M (map P' xs)@[M]) \<bullet> 1"
    by (simp add:markov_orth_inv[OF assms(6)]) 
  also have "... = foldl (\<lambda>x N. M *v (N *v x)) stat (map P' xs) \<bullet> 1"
    using xs_ne by (subst foldl_intersperse) auto
  also have "... = foldl (\<lambda>x N. M *v (N *v x)) stat ((ys \<bind> (\<lambda>x. ?rep x @ [Q])) @ ?rep z) \<bullet> 1"
    unfolding bool_list_split[OF ys_z] P'_def List.bind_def by (simp add: comp_def map_concat)
  also have "... = foldl (\<lambda>x N. M *v (N *v x)) stat (ys \<bind> (\<lambda>x. ?rep x @ [Q])) \<bullet> 1"
    by (simp add: a)
  also have "... = foldl (\<lambda>x N. M *v (N *v x)) stat (?rep yh @[Q]@(yt \<bind>(\<lambda>x. ?rep x @ [Q]))) \<bullet> 1"
    unfolding ys_split by simp
  also have "... = foldl (\<lambda>x N. M *v (N *v x)) stat ([Q]@(yt \<bind>(\<lambda>x. ?rep x @ [Q]))) \<bullet> 1"
    by (simp add:b)
  also have "... = foldl (\<lambda>x N. N *v x) stat (intersperse M (Q#(yt \<bind>(\<lambda>x.?rep x@[Q])))@[M])\<bullet>1"
    by (subst foldl_intersperse, auto)
  also have "... = foldl (\<lambda>x N. N *v x) stat (intersperse M (Q#(yt \<bind>(\<lambda>x.?rep x@[Q])))) \<bullet> 1"
    by (simp add:markov_orth_inv[OF assms(6)]) 
  also have "... = foldl (\<lambda>x N. N *v (M *v x)) (Q *v stat) (yt \<bind>(\<lambda>x.?rep x@[Q])) \<bullet> 1" 
    by (subst foldl_intersperse_2, simp)
  also have "... = foldl (\<lambda>a x. foldl (\<lambda>x N. N *v (M *v x)) a (?rep x @ [Q])) (Q *v stat) yt \<bullet> 1"
    unfolding List.bind_def foldl_concat foldl_map by simp
  also have "... = foldl (\<lambda>a x. Q *v (matrix_pow M (x+1) *v a)) (Q *v stat) yt \<bullet> 1"
    unfolding c by simp
  also have "... = foldl (\<lambda>a N. Q *v (N *v a)) (Q *v stat) (map (\<lambda>x. matrix_pow M (x+1)) yt) \<bullet> 1"
    by (simp add:foldl_map)
  also have "... \<le> (\<mu> + \<alpha>*(1-\<mu>))^(length (map (\<lambda>x. matrix_pow M (x+1)) yt)+1)"
    unfolding \<mu>_def Q_def by (intro hitting_property_alg \<alpha>_range d) simp
  also have "... = (\<mu> + \<alpha>*(1-\<mu>))^(length ys)" 
    unfolding ys_split by simp
  also have "... = ?R" unfolding len_ys by simp
  finally show ?thesis by simp
next
  case False
  hence I_empty: "I = {}" by simp

  have "?L = stat \<bullet> (1 :: real^'n)"
  proof (cases "l > 0")
    case True
    have "?L = foldl (\<lambda>x M. M *v x) stat ((intersperse M (map P [0..<l]))@[M]) \<bullet> 1"
      by (simp add:markov_orth_inv[OF assms(6)]) 
    also have "... = foldl (\<lambda>x N. M *v (N *v x)) stat (map P [0..<l])  \<bullet> 1"
      using True by (subst foldl_intersperse, auto)
    also have "... = foldl (\<lambda>x N. M *v (N *v x)) stat (map (\<lambda>_. mat 1) [0..<l])  \<bullet> 1"
      unfolding  P_def using I_empty by simp
    also have "... = foldl (\<lambda>x _. M *v x) stat [0..<l] \<bullet> 1"
      unfolding foldl_map by simp
    also have "... = stat \<bullet> (1 :: real^'n)"
      by (induction l, auto simp add:markov_orth_inv[OF assms(6)])
    finally show ?thesis by simp
  next
    case False
    then show ?thesis by simp
  qed
  also have "... = 1"
    unfolding stat_def by (simp add:inner_vec_def)
  also have "... \<le> ?R" unfolding I_empty by simp
  finally show ?thesis by simp
qed

lemma uniform_property_alg:
  fixes x :: "('n :: finite)" and l :: nat
  assumes "i < l"
  defines "P j \<equiv> (if j = i then diag (ind_vec {x}) else mat 1)"
  assumes "markov M"
  shows "foldl (\<lambda>x M. M *v x) stat (intersperse M (map P [0..<l])) \<bullet> 1 = 1 / CARD('n)"
    (is "?L = ?R") 
proof -
  have a:"l > 0" using assms(1) by simp

  have 0: "foldl (\<lambda>x N. M *v (N *v x)) y (xs) \<bullet> 1 = y  \<bullet> 1" if "set xs \<subseteq> {mat 1}" for xs y
    using that
  proof (induction xs rule:rev_induct)
    case Nil
    then show ?case by simp
  next
    case (snoc x xs)
    have "x = mat 1" 
      using snoc(2) by simp
    hence "foldl (\<lambda>x N. M *v (N *v x)) y (xs @ [x]) \<bullet> 1 = foldl (\<lambda>x N. M *v (N *v x)) y xs \<bullet> 1"
      by (simp add:markov_orth_inv[OF assms(3)])
    also have "... = y \<bullet> 1"
      using snoc(2) by (intro snoc(1)) auto
    finally show ?case by simp
  qed

  have M_stat: "M *v stat = stat" 
    using assms(3) unfolding stat_def matrix_vector_mult_scaleR markov_def by simp

  hence 1: "(foldl (\<lambda>x N. M *v (N *v x)) stat xs) = stat" if "set xs \<subseteq> {mat 1}" for xs
    using that by (induction xs, auto)

  have "?L = foldl (\<lambda>x M. M *v x) stat ((intersperse M (map P [0..<l]))@[M]) \<bullet> 1"
    by (simp add:markov_orth_inv[OF assms(3)]) 
  also have "... = foldl (\<lambda>x N. M *v (N *v x)) stat (map P [0..<l]) \<bullet> 1"
    using a by (subst foldl_intersperse) auto
  also have "... = foldl (\<lambda>x N. M *v (N *v x)) stat (map P ([0..<i+1]@[i+1..<l])) \<bullet> 1"
    using assms(1) by (subst upto_append) auto
  also have "... = foldl (\<lambda>x N. M *v (N *v x)) stat (map P [0..<i + 1]) \<bullet> 1"
    unfolding map_append foldl_append  P_def by (subst 0) auto
  also have "... = foldl (\<lambda>x N. M *v (N *v x)) stat (map P ([0..<i]@[i])) \<bullet> 1"
    by simp
  also have "... = (M *v (diag (ind_vec {x}) *v stat)) \<bullet> 1"
    unfolding map_append foldl_append P_def by (subst 1) auto
  also have "... = (diag (ind_vec {x}) *v stat) \<bullet> 1" 
    by (simp add:markov_orth_inv[OF assms(3)]) 
  also have "... = ((1/CARD('n)) *\<^sub>R ind_vec {x}) \<bullet> 1" 
    unfolding diag_def ind_vec_def  stat_def matrix_vector_mult_def 
    by (intro arg_cong2[where f="(\<bullet>)"] refl) 
      (vector of_bool_def sum.If_cases if_distrib if_distribR)
  also have "... = (1/CARD('n)) * (ind_vec {x} \<bullet> 1)"
    by simp
  also have "... = (1/CARD('n)) * 1"
    unfolding inner_vec_def ind_vec_def of_bool_def 
    by (intro arg_cong2[where f="(*)"] refl) (simp)
  finally show ?thesis by simp
qed

end

lemma foldl_matrix_mult_expand:
  fixes Ms :: "(('r::{semiring_1,comm_monoid_mult})^'a^'a) list"
  shows "(foldl (\<lambda>x M. M *v x) a Ms) $ k = (\<Sum>x | length x = length Ms+1 \<and> x! length Ms = k. 
  (\<Prod> i< length Ms. (Ms ! i) $ (x ! (i+1)) $ (x ! i)) * a $ (x ! 0))"
proof (induction Ms arbitrary: k rule:rev_induct)
  case Nil
  have "length x = Suc 0 \<Longrightarrow> x = [x!0]" for x :: "'a list"
    by (cases x, auto)
  hence "{x. length x = Suc 0 \<and> x ! 0 = k} = {[k]}" 
    by auto 
  thus ?case by auto
next
  case (snoc M Ms)
  let ?l = "length Ms"

  have 0: "finite {w. length w = Suc (length Ms) \<and> w ! length Ms = i}" for i :: 'a
    using finite_lists_length_eq[where A="UNIV::'a set" and n="?l +1"] by simp

  have "take (?l+1) x @ [x ! (?l+1)] = x" if "length x = ?l+2" for x :: "'a list"
  proof -
    have "take (?l+1) x @ [x ! (?l+1)] = take (Suc (?l+1)) x"
      using that by (intro take_Suc_conv_app_nth[symmetric], simp)
    also have "... = x" 
      using that by simp
    finally show ?thesis by simp
  qed
  hence 1: "bij_betw  (take (?l+1)) {w. length w=?l+2 \<and> w!(?l+1) =k} {w. length w = ?l+1}"
    by (intro bij_betwI[where g="\<lambda>x. x@[k]"]) (auto simp add:nth_append)

  have "foldl (\<lambda>x M. M *v x) a (Ms @ [M]) $ k = (\<Sum>j\<in>UNIV. M$k$j *(foldl (\<lambda>x M. M *v x) a Ms $ j))"
    by (simp add:matrix_vector_mult_def)
  also have "... = 
    (\<Sum>j\<in>UNIV. M$k$j * (\<Sum>w|length w=?l+1\<and>w!?l=j. (\<Prod>i<?l. Ms!i $ w!(i+1) $ w!i) * a $ w!0))"
    unfolding snoc by simp
  also have "... = 
    (\<Sum>j\<in>UNIV. (\<Sum>w|length w=?l+1\<and>w!?l=j. M$k$w!?l * (\<Prod>i<?l. Ms!i $ w!(i+1) $ w!i) * a $ w!0))"
    by (intro sum.cong refl) (simp add: sum_distrib_left algebra_simps)
  also have "... = (\<Sum>w\<in> (\<Union>j \<in> UNIV. {w. length w=?l+1 \<and> w!?l =j}). 
    M$k$w!?l*(\<Prod>i<?l. Ms!i $ w!(i+1) $ w!i) * a $ w!0)"
    using 0 by (subst sum.UNION_disjoint, simp, simp) auto 
  also have "... = (\<Sum>w | length w=?l+1. M$k$(w!?l)*(\<Prod>i<?l. Ms!i $ w!(i+1) $ w!i) * a $ w!0)"
    by (intro sum.cong arg_cong2[where f="(*)"] refl) auto
  also have "... = (\<Sum>w \<in> take (?l+1) ` {w. length w=?l+2 \<and> w!(?l+1) =k}. 
    M$k$w!?l*(\<Prod>i<?l. Ms!i $ w!(i+1) $ w!i) * a $ w!0)"
    using 1 unfolding bij_betw_def by (intro sum.cong refl, auto) 
  also have "... = (\<Sum>w|length w=?l+2\<and>w!(?l+1)=k. M$k$w!?l*(\<Prod>i<?l. Ms!i $ w!(i+1) $ w!i)* a$w!0)"
    using 1 unfolding bij_betw_def by (subst sum.reindex, auto)
  also have "... = (\<Sum>w|length w=?l+2\<and>w!(?l+1)=k. 
    (Ms@[M])!?l$k$w!?l*(\<Prod>i<?l. (Ms@[M])!i $ w!(i+1) $ w!i)* a$w!0)"
    by (intro sum.cong arg_cong2[where f="(*)"] prod.cong refl) (auto simp add:nth_append)
  also have "... = (\<Sum>w|length w=?l+2\<and>w!(?l+1)=k. (\<Prod>i<(?l+1). (Ms@[M])!i $ w!(i+1) $ w!i)* a$w!0)"
    by (intro sum.cong, auto simp add:algebra_simps)
  finally have "foldl (\<lambda>x M. M *v x) a (Ms @ [M]) $ k = 
    (\<Sum> w | length w = ?l+2 \<and> w ! (?l+1) = k. (\<Prod>i<(?l+1). (Ms@[M])!i $ w!(i+1) $ w!i)* a$w!0)"
    by simp
  then show ?case by simp
qed

lemma foldl_matrix_mult_expand_2:
  fixes Ms :: "(real^'a^'a) list"
  shows "(foldl (\<lambda>x M. M *v x) a Ms) \<bullet> 1 = (\<Sum>x | length x = length Ms+1. 
          (\<Prod> i< length Ms. (Ms ! i) $ (x ! (i+1)) $ (x ! i)) * a $ (x ! 0))"
  (is "?L = ?R")
proof -
  let ?l = "length Ms"
  have "?L = (\<Sum>j \<in> UNIV. (foldl (\<lambda>x M. M *v x) a Ms) $ j)"
    by (simp add:inner_vec_def)
  also have "... = (\<Sum>j\<in>UNIV. \<Sum>x|length x=?l+1 \<and> x!?l=j.(\<Prod>i<?l. Ms!i $ x!(i+1) $ x!i) * a $ x!0)"
    unfolding foldl_matrix_mult_expand by simp
  also have "... = (\<Sum>x \<in> (\<Union>j\<in> UNIV.{w. length w = length Ms+1 \<and> w ! length Ms = j}).
          (\<Prod> i< length Ms. (Ms ! i) $ (x ! (i+1)) $ (x ! i)) * a $ (x ! 0))"
    using finite_lists_length_eq[where A="UNIV::'a set" and n="?l +1"]
    by (intro sum.UNION_disjoint[symmetric]) auto
  also have "... = ?R"
    by (intro sum.cong, auto)
  finally show ?thesis by simp
qed

end
