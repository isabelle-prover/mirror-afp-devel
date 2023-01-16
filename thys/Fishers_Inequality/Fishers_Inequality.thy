(* Title: Fishers_Inequality.thy
   Author: Chelsea Edmonds
*)

section \<open>Fisher's Inequality\<close>

text \<open>This theory presents the proof of Fisher's Inequality \<^cite>\<open>"fisherExaminationDifferentPossible1940a"\<close>
 on BIBD's (i.e. uniform Fisher's) and the generalised nonuniform Fisher's Inequality \<close>
theory Fishers_Inequality imports Rank_Argument_General Linear_Bound_Argument
begin

subsection \<open> Uniform Fisher's Inequality \<close>
context ordered_bibd
begin

text \<open>Row/Column transformation steps \<close>

text\<open>Following design theory lecture notes from MATH3301 at the University of Queensland
 \<^cite>\<open>"HerkeLectureNotes2016"\<close>, a simple transformation to produce an upper triangular matrix using elementary
row operations is to (1) Subtract the first row from each other row, and (2) add all columns to the first column\<close>

lemma transform_N_step1_vals: 
  defines mdef: "M \<equiv> (N * N\<^sup>T)"
  assumes "i < dim_row M" 
  assumes "j < dim_col M"
  shows "i = 0 \<Longrightarrow> j = 0 \<Longrightarrow> (add_row_to_multiple (-1) [1..<dim_row M] 0 M) $$ (i, j) = (int \<r>)" \<comment> \<open> top left elem \<close>
  and "i \<noteq> 0 \<Longrightarrow> j = 0 \<Longrightarrow> (add_row_to_multiple (-1) [1..<dim_row M] 0 M) $$ (i, j) = (int \<Lambda>) - (int \<r>)" \<comment> \<open> first column ex. 1 \<close>
  and "i = 0 \<Longrightarrow> j \<noteq> 0 \<Longrightarrow> (add_row_to_multiple (-1) [1..<dim_row M] 0 M) $$ (i, j) = (int \<Lambda>)" \<comment> \<open> first row ex. 1 \<close>
  and "i \<noteq> 0 \<Longrightarrow> j \<noteq> 0 \<Longrightarrow> i = j \<Longrightarrow> (add_row_to_multiple (-1) [1..<dim_row M] 0 M) $$ (i, j) = (int \<r>) - (int \<Lambda>)" \<comment> \<open> diagonal ex. 1 \<close>
  and "i \<noteq> 0 \<Longrightarrow> j \<noteq> 0 \<Longrightarrow> i \<noteq> j \<Longrightarrow> (add_row_to_multiple (-1) [1..<dim_row M] 0 M) $$ (i, j) = 0" \<comment> \<open> everything else \<close>
  using transpose_N_mult_diag v_non_zero assms
proof (simp) 
  show "i = 0 \<Longrightarrow> j \<noteq> 0 \<Longrightarrow> (add_row_to_multiple (-1) [1..<dim_row M] 0 M) $$ (i, j) = (int \<Lambda>)" 
    using transpose_N_mult_off_diag v_non_zero assms transpose_N_mult_dim(2) by force
next
  assume a: "j = 0" "i\<noteq>0"
  then have ail: "((-1) * M $$(0, j)) = -(int \<r>)"
    using transpose_N_mult_diag v_non_zero mdef by auto 
  then have ijne: "j \<noteq> i" using a by simp
  then have aij: "M $$ (i, j) = (int \<Lambda>)" using assms(2) mdef transpose_N_mult_off_diag a v_non_zero
    by (metis transpose_N_mult_dim(1)) 
  then have "add_row_to_multiple (-1) [1..<dim_row M] 0 M $$ (i, j) = (-1)*(int \<r>) + (int \<Lambda>)" 
    using ail add_first_row_to_multiple_index(2) assms(2) assms(3) a by (metis mult_minus1) 
  then show "(add_row_to_multiple (-1) [1..<dim_row M] 0 M) $$ (i, j) = (int \<Lambda>) - (int \<r>)"
    by linarith 
next 
  assume a: "i \<noteq> 0" "j \<noteq> 0" 
  have ail: "((-1) * M $$(0, j)) = -(int \<Lambda>)" 
    using assms transpose_N_mult_off_diag a v_non_zero transpose_N_mult_dim(1) by auto  
  then have  "i = j \<Longrightarrow> M $$ (i, j) = (int \<r>)" 
    using assms transpose_N_mult_diag a v_non_zero by (metis transpose_N_mult_dim(1)) 
  then show "i = j \<Longrightarrow> (add_row_to_multiple (-1) [1..<dim_row M] 0 M) $$ (i, j) = (int \<r>) - (int \<Lambda>)"
    using ail add_first_row_to_multiple_index(2) assms a by (metis uminus_add_conv_diff) 
  then have "i \<noteq> j \<Longrightarrow> M $$ (i, j) = (int \<Lambda>)" using assms transpose_N_mult_off_diag a v_non_zero
    by (metis transpose_N_mult_dim(1) transpose_N_mult_dim(2)) 
  then show "i \<noteq> j \<Longrightarrow> (add_row_to_multiple (-1) [1..<dim_row M] 0 M) $$ (i, j) = 0" 
    using ail add_first_row_to_multiple_index(2) assms a by (metis add.commute add.right_inverse)
qed

lemma transform_N_step2_vals: 
  defines mdef: "M \<equiv> (add_row_to_multiple (-1) [1..<dim_row (N * N\<^sup>T)] 0 (N * N\<^sup>T))"
  assumes "i < dim_row (M)"
  assumes "j < dim_col (M)"
  shows "i = 0 \<Longrightarrow> j = 0 \<Longrightarrow> add_multiple_cols 1 0 [1..<dim_col M] M $$ (i, j) = 
    (int \<r>) + (int \<Lambda>) * (\<v> - 1)" \<comment> \<open> top left element \<close>
  and "i = 0 \<Longrightarrow> j \<noteq> 0 \<Longrightarrow> add_multiple_cols 1 0 [1..<dim_col M] M $$ (i, j)  = (int \<Lambda>)" \<comment> \<open> top row \<close>
  and "i \<noteq> 0 \<Longrightarrow> i = j \<Longrightarrow> add_multiple_cols 1 0 [1..<dim_col M] M $$ (i, j) = (int \<r>) - (int \<Lambda>)" \<comment> \<open> Diagonal \<close>
  and "i \<noteq> 0 \<Longrightarrow> i \<noteq> j \<Longrightarrow>  add_multiple_cols 1 0 [1..<dim_col M] M $$ (i, j) = 0" \<comment> \<open>Everything else\<close>
proof -
  show "i = 0 \<Longrightarrow> j \<noteq> 0 \<Longrightarrow> add_multiple_cols 1 0 [1..<dim_col M] M $$ (i, j)  = (int \<Lambda>)"
    using add_all_cols_to_first assms transform_N_step1_vals(3) by simp
  show "i \<noteq> 0 \<Longrightarrow> i = j \<Longrightarrow> add_multiple_cols 1 0 [1..<dim_col M] M $$ (i, j) = (int \<r>) - (int \<Lambda>)"
    using add_all_cols_to_first assms transform_N_step1_vals(4) by simp
next
  assume a: "i = 0" "j =0"
  then have size: "card {1..<dim_col M} = \<v> - 1" using assms by simp 
  have val: "\<And> l . l \<in> {1..<dim_col M} \<Longrightarrow> M $$ (i, l) = (int \<Lambda>)" 
    using mdef transform_N_step1_vals(3) by (simp add: a(1))
  have "add_multiple_cols 1 0 [1..<dim_col M] M $$ (i, j) = (\<Sum>l\<in>{1..<dim_col M}.  M $$(i,l)) + M$$(i,0)" 
    using a assms add_all_cols_to_first by blast 
  also have "... = (\<Sum>l\<in>{1..<dim_col M}.  (int \<Lambda>)) + M$$(i,0)" using val by simp
  also have "... = (\<v> - 1) * (int \<Lambda>) + M$$(i,0)" using size by (metis sum_constant) 
  finally show "add_multiple_cols 1 0 [1..<dim_col M] M $$ (i, j) = (int \<r>) + (int \<Lambda>) * (\<v> - 1)" 
    using transform_N_step1_vals(1) a(1) a(2) assms(1) assms(2) by simp 
next
  assume a: "i \<noteq> 0"  "i \<noteq> j"
  then show "add_multiple_cols 1 0 [1..<dim_col M] M $$ (i, j) = 0" 
  proof (cases "j \<noteq> 0")
    case True
    then show ?thesis using add_all_cols_to_first assms a transform_N_step1_vals(5) by simp
  next 
    case False
    then have iin: "i \<in> {1..<dim_col M}" using a(1) assms by simp
    have cond: "\<And> l . l \<in> {1..<dim_col M} \<Longrightarrow> l <dim_col (N * N\<^sup>T) \<and> l \<noteq> 0" using assms by simp 
    then have val: "\<And> l . l \<in> {1..<dim_col M } - {i} \<Longrightarrow> M $$ (i, l) = 0" 
      using assms(3) transform_N_step1_vals(5) a False assms(1)
      by (metis DiffE iin index_mult_mat(2) index_mult_mat(3) index_transpose_mat(3) insertI1) 
    have val2: "M $$ (i, i) = (int \<r>) - (int \<Lambda>)" using mdef transform_N_step1_vals(4) a False
       assms(1) transpose_N_mult_dim(1) transpose_N_mult_dim(2)
      by (metis cond iin) 
    have val3: "M$$ (i, 0) = (int \<Lambda>) - (int \<r>)" 
      using assms(3) transform_N_step1_vals(2) a False assms(1) assms(2)
      by (metis add_row_to_multiple_dim(1) transpose_N_mult_dim(2) v_non_zero)
    have "add_multiple_cols 1 0 [1..<dim_col M] M $$ (i, j) = (\<Sum>l\<in>{1..<dim_col M}.  M $$(i,l)) + M$$(i,0)" 
      using assms add_all_cols_to_first False by blast
    also have "... = M $$ (i, i)  + (\<Sum>l\<in>{1..<dim_col M} - {i}.  M $$(i,l)) + M$$(i,0)"
      by (metis iin finite_atLeastLessThan sum.remove)
    finally show ?thesis using val val2 val3 by simp
  qed
qed

text \<open>Transformed matrix is upper triangular \<close>
lemma transform_upper_triangular: 
  defines mdef: "M \<equiv> (add_row_to_multiple (-1) [1..<dim_row (N * N\<^sup>T)] 0 (N * N\<^sup>T))"
  shows "upper_triangular (add_multiple_cols 1 0 [1..<dim_col M] M)"
  using transform_N_step2_vals(4) by (intro upper_triangularI) (simp add: assms)

text \<open>Find the determinant of the $NN^T$ matrix using transformed matrix values\<close>
lemma determinant_inc_mat_square: "det (N * N\<^sup>T) = (\<r> + \<Lambda> * (\<v> - 1))* (\<r> - \<Lambda>)^(\<v> - 1)"
proof -
\<comment> \<open> Show the matrix is now lower triangular, therefore the det is the product of the sum of diagonal \<close>
  have cm: "(N * N\<^sup>T) \<in> carrier_mat \<v> \<v>"
    using transpose_N_mult_dim(1) transpose_N_mult_dim(2) by blast  
  define C where "C \<equiv>(add_row_to_multiple (-1) [1..<dim_row (N * N\<^sup>T)] 0 (N * N\<^sup>T))"
  have "0 \<notin> set [1..<dim_row (N * N\<^sup>T)]" by simp
  then have detbc: "det (N * N\<^sup>T) = det C" 
    using C_def add_row_to_multiple_det v_non_zero by (metis cm) 
  define D where "D \<equiv> add_multiple_cols 1 0 [1..<dim_col C] C"
  have d00: "D $$ (0, 0) = ((int \<r>) + (int \<Lambda>) * (\<v> - 1))" using transform_N_step2_vals(1)
    by (simp add: C_def D_def v_non_zero) 
  have ine0: "\<And> i. i \<in> {1..<dim_row D} \<Longrightarrow> i \<noteq> 0" by simp
  have "\<And> i. i \<in> {1..<dim_row D} \<Longrightarrow> i < dim_row (N * N\<^sup>T)" using D_def C_def by simp       
  then have diagnon0: "\<And> i. i \<in> {1..<\<v>} \<Longrightarrow> D $$ (i, i) = (int \<r>) - (int \<Lambda>)"   
    using transform_N_step2_vals(3) ine0 D_def C_def by simp (* Slow *)
  have alll: "\<And> l. l \<in> set [1..<dim_col C] \<Longrightarrow> l < \<v>" using C_def by simp
  have cmc: "C \<in> carrier_mat \<v> \<v>" using cm C_def
    by (simp add: add_row_to_multiple_carrier)
  have dimgt2: "dim_row D \<ge> 2"
    using t_lt_order D_def C_def by (simp)  
  then have fstterm: "0 \<in> { 0 ..< dim_row D}" by (simp add: points_list_length)
  have "0 \<notin> set [1..<dim_col C]" by simp
  then have "det (N * N\<^sup>T) = det D" using add_multiple_cols_det alll cmc D_def C_def
    by (metis detbc) 
  also have "... = prod_list (diag_mat D)" using det_upper_triangular
    using transform_upper_triangular D_def C_def by fastforce 
  also have "... = (\<Prod> i = 0 ..< dim_row D. D $$ (i,i))" using prod_list_diag_prod by blast  
  also have "... = (\<Prod> i = 0 ..< \<v>. D $$ (i,i))"  by (simp add: D_def C_def)  
  finally have "det (N * N\<^sup>T) = D $$ (0, 0) * (\<Prod> i =  1 ..< \<v>. D $$ (i,i))" 
    using dimgt2 by (simp add: prod.atLeast_Suc_lessThan v_non_zero) 
  then have "det (N * N\<^sup>T) = (\<r> + \<Lambda> * (\<v> - 1)) * ((int \<r>) - (int \<Lambda>))^(\<v> - 1)"
    using d00 diagnon0 by simp
  then have "det (N * N\<^sup>T) = (\<r> + \<Lambda> * (\<v> - 1)) * ( \<r> - \<Lambda>)^(\<v> - 1)"
    using index_lt_replication
    by (metis (no_types, lifting) less_imp_le_nat of_nat_diff of_nat_mult of_nat_power)
  then show ?thesis by blast 
qed

text \<open>Fisher's Inequality using the rank argument. 
Note that to use the rank argument we must first map N to a real matrix. It is useful to explicitly
include the parameters which should be used in the application of the @{thm [source] "rank_argument_det"} lemma \<close>
theorem Fishers_Inequality_BIBD: "\<v> \<le> \<b>"
proof (intro rank_argument_det[of "map_mat real_of_int N" "\<v>" "\<b>"], simp_all)
  show "N \<in> carrier_mat \<v> (length \<B>s)" using blocks_list_length N_carrier_mat by simp
  let ?B = "map_mat (real_of_int) (N * N\<^sup>T)"
  have b_split: "?B = map_mat (real_of_int) N * (map_mat (real_of_int) N)\<^sup>T"
    using semiring_hom.mat_hom_mult  of_int_hom.semiring_hom_axioms transpose_carrier_mat map_mat_transpose
    by (metis (no_types, lifting) N_carrier_mat) 
  have db: "det ?B = (\<r> + \<Lambda> * (\<v> - 1))* (\<r> - \<Lambda>)^(\<v> - 1)"
    using determinant_inc_mat_square by simp
  have lhn0: "(\<r> + \<Lambda> * (\<v> - 1)) > 0"
    using r_gzero by blast 
  have "(\<r> - \<Lambda>) > 0"
    using index_lt_replication zero_less_diff by blast  
  then have det_not_0:  "det ?B \<noteq> 0" using lhn0 db
    by (metis gr_implies_not0 mult_is_0 of_nat_eq_0_iff power_not_zero) 
  thus "det (of_int_hom.mat_hom N * (of_int_hom.mat_hom N)\<^sup>T) \<noteq> (0:: real)" using b_split by simp
qed

end

subsection \<open>Generalised Fisher's Inequality \<close>

context simp_ordered_const_intersect_design
begin

text \<open>Lemma to reason on sum coefficients \<close>
lemma sum_split_coeffs_0: 
  fixes c :: "nat \<Rightarrow> real"
  assumes "\<b> \<ge> 2"
  assumes "\<m> > 0"
  assumes "j' < \<b>"
  assumes "0 = (\<Sum> j \<in> {0..<\<b>} . (c j)^2 * ((card (\<B>s ! j))- (int \<m>))) +
           \<m> * ((\<Sum> j \<in> {0..<\<b>} . c j)^2)"
  shows "c j' = 0"
proof (rule ccontr)
  assume cine0: "c j' \<noteq> 0"
  have innerge: "\<And> j . j < \<b>  \<Longrightarrow> (c j)^2 * (card (\<B>s ! j) - (int \<m>))  \<ge> 0" 
    using inter_num_le_block_size assms(1) by simp
  then have lhsge: "(\<Sum> j \<in> {0..<\<b>} . (c j)^2 * ((card (\<B>s ! j))- (int \<m>))) \<ge> 0"
    using sum_bounded_below[of "{0..<\<b>}" "0" "\<lambda> i. (c i)^2 * ((card (\<B>s ! i))- (int \<m>))"] by simp
  have "\<m> * ((\<Sum> j \<in> {0..<\<b>} . c j)^2) \<ge> 0" by simp
  then have rhs0: "\<m> * ((\<Sum> j \<in> {0..<\<b>} . c j)^2) = 0" 
    using assms(2) assms(4) lhsge by linarith
  then have "(\<Sum> j \<in> {0..<\<b>} . (c j)^2 * ((card (\<B>s ! j))- (int \<m>))) = 0" 
    using assms by linarith
  then have lhs0inner: "\<And> j . j < \<b>  \<Longrightarrow> (c j)^2 * (card (\<B>s ! j) - (int \<m>)) = 0" 
    using innerge sum_nonneg_eq_0_iff[of "{0..<\<b>}" "\<lambda> j . (c j)^2 * (card (\<B>s ! j) - (int \<m>))"] 
    by simp
  thus False proof (cases "card (\<B>s ! j') = \<m>")
    case True
    then have cj0: "\<And> j. j \<in> {0..<\<b>} - {j'} \<Longrightarrow> (c j) = 0"
      using lhs0inner const_intersect_block_size_diff assms True by auto
    then have "(\<Sum> i \<in> {0..<\<b>} . c i) \<noteq> 0" 
      using sum.remove[of "{0..<\<b>}" "j'" "\<lambda> i. c i"] assms(3) cine0 cj0 by simp
    then show ?thesis using rhs0 assms by simp
  next
    case False
    then have ne: "(card (\<B>s ! j') - (int \<m>)) \<noteq> 0"
      by linarith  
    then have "(c j')^2 * (card (\<B>s ! j') - (int \<m>)) \<noteq> 0" using cine0
      by auto 
    then show ?thesis using lhs0inner assms(3) by auto
  qed
qed

text \<open>The general non-uniform version of fisher's inequality is also known as the "Block town problem".
In this case we are working in a constant intersect design, hence the inequality is the opposite
way around compared to the BIBD version. The theorem below is the more traditional set theoretic 
approach. This proof is based off one by Jukna \<^cite>\<open>"juknaExtremalCombinatorics2011"\<close> \<close>
theorem general_fishers_inequality:  "\<b> \<le> \<v>"
proof (cases "\<m> = 0 \<or> \<b> = 1")
  case True
  then show ?thesis using empty_inter_implies_b_lt_v v_non_zero by linarith
next
  case False
  then have mge: "\<m> > 0" by simp 
  then have bge: "\<b> \<ge> 2" using b_positive False blocks_list_length by linarith
  define NR :: "real mat" where "NR \<equiv> lift_01_mat N"
  show ?thesis 
  proof (intro lin_bound_argument2[of NR])
    show "distinct (cols NR)" using lift_01_distinct_cols_N NR_def by simp
    show nrcm: "NR \<in> carrier_mat \<v> \<b>" using NR_def N_carrier_mat_01_lift by simp 
    have scalar_prod_real1: "\<And> i. i <\<b> \<Longrightarrow>  ((col NR i) \<bullet> (col NR i)) = card (\<B>s ! i)"
      using scalar_prod_block_size_lift_01 NR_def by auto 
    have scalar_prod_real2: "\<And> i j. i <\<b> \<Longrightarrow> j <\<b> \<Longrightarrow> i \<noteq> j \<Longrightarrow> ((col NR i) \<bullet> (col NR j)) = \<m>"
      using scalar_prod_inter_num_lift_01 NR_def indexed_const_intersect by auto
    show "\<And>f. vec \<v> (\<lambda>i. \<Sum>j = 0..<\<b>. f (col NR j) * (col NR j) $ i) = 0\<^sub>v \<v> \<Longrightarrow> \<forall>v\<in>set (cols NR). f v = 0"
    proof (intro ballI)
      fix f v
      assume eq0: "vec \<v> (\<lambda>i. \<Sum>j = 0..<\<b>. f (col NR j) * col NR j $ i) = 0\<^sub>v \<v>"
      assume vin: "v \<in> set (cols NR)"
      define c where "c \<equiv> (\<lambda> j. f (col NR j))"
      obtain j' where v_def: "col NR j' = v" and jvlt: "j' < dim_col NR"
        using vin by (metis cols_length cols_nth index_less_size_conv nth_index)
      have dim_col: "\<And>j. j \<in> {0..< \<b>} \<Longrightarrow> dim_vec (col NR j) = \<v>" using nrcm by auto
      \<comment> \<open> Summation reasoning to obtain conclusion on coefficients \<close>
      have "0 = (vec \<v> (\<lambda>i. \<Sum>j = 0..<\<b>. c j * (col NR j) $ i)) \<bullet> (vec \<v> (\<lambda>i. \<Sum>j = 0..<\<b>. c j * (col NR j) $ i))" 
        using vec_prod_zero eq0 c_def by simp
      also have "... = (\<Sum> j1 \<in> {0..<\<b>} . c j1 * c j1 * ((col NR j1) \<bullet> (col NR j1))) + (\<Sum> j1 \<in> {0..<\<b>} . 
        (\<Sum> j2 \<in> ({0..< \<b>} - {j1}) . c j1 * c j2 * ((col NR j1) \<bullet> (col NR j2))))" 
        using scalar_prod_double_sum_fn_vec[of \<b> "col NR" \<v> c] dim_col by simp
      also have "... = (\<Sum> j1 \<in> {0..<\<b>} . (c j1) * (c j1) * (card (\<B>s ! j1))) + (\<Sum> j1 \<in> {0..<\<b>} . 
        (\<Sum> j2 \<in> ({0..< \<b>} - {j1}) . c j1 * c j2 * ((col NR j1) \<bullet> (col NR j2))))"
        using scalar_prod_real1 by simp
      also have "... = (\<Sum> j1 \<in> {0..<\<b>} . (c j1)^2 * (card (\<B>s ! j1))) + (\<Sum> j1 \<in> {0..<\<b>} . 
        (\<Sum> j2 \<in> ({0..< \<b>} - {j1}) . c j1 * c j2 * ((col NR j1) \<bullet> (col NR j2))))"
        by (metis power2_eq_square) 
      also have "... = (\<Sum> j1 \<in> {0..<\<b>} . (c j1)^2 * (card (\<B>s ! j1))) + (\<Sum> j1 \<in> {0..<\<b>} . 
        (\<Sum> j2 \<in> ({0..< \<b>} - {j1}) . c j1 * c j2 * \<m>))" using scalar_prod_real2  by auto
      also have "... = (\<Sum> j1 \<in> {0..<\<b>} . (c j1)^2 * (card (\<B>s ! j1))) + 
         \<m> * (\<Sum> j1 \<in> {0..<\<b>} . (\<Sum> j2 \<in> ({0..< \<b>} - {j1}) . c j1 * c j2))" 
        using double_sum_mult_hom[of "\<m>" "\<lambda> i j . c i * c j" "\<lambda> i.{0..<\<b>} - {i}" "{0..<\<b>}"]
        by (metis (no_types, lifting) mult_of_nat_commute sum.cong) 
      also have "... = (\<Sum> j \<in> {0..<\<b>} . (c j)^2 * (card (\<B>s ! j))) + 
         \<m> * ((\<Sum> j \<in> {0..<\<b>} . c j)^2 - (\<Sum> j \<in> {0..<\<b>} . c j * c j))" 
        using double_sum_split_square_diff by auto 
      also have "... = (\<Sum> j \<in> {0..<\<b>} . (c j)^2 * (card (\<B>s ! j))) + (-\<m>) * (\<Sum> j \<in> {0..<\<b>} . (c j)^2) + 
         \<m> * ((\<Sum> j \<in> {0..<\<b>} . c j)^2)" by (simp add: algebra_simps power2_eq_square)
      also have "... = (\<Sum> j \<in> {0..<\<b>} . (c j)^2 * (card (\<B>s ! j))) + (\<Sum> j \<in> {0..<\<b>} . (-\<m>)* (c j)^2) + 
         \<m> * ((\<Sum> j \<in> {0..<\<b>} . c j)^2)" by (simp add: sum_distrib_left) 
      also have "... = (\<Sum> j \<in> {0..<\<b>} . (c j)^2 * (card (\<B>s ! j))+ (-\<m>)* (c j)^2) + 
         \<m> * ((\<Sum> j \<in> {0..<\<b>} . c j)^2)" by (metis (no_types) sum.distrib)
      finally have sum_rep: "0 = (\<Sum> j \<in> {0..<\<b>} . (c j)^2 * ((card (\<B>s ! j))- (int \<m>))) + 
         \<m> * ((\<Sum> j \<in> {0..<\<b>} . c j)^2)" by (simp add: algebra_simps)
      thus "f v = 0" using sum_split_coeffs_0[of "j'" "c"] mge bge jvlt nrcm c_def v_def by simp
    qed
  qed
qed

end

text \<open>Using the dual design concept, it is easy to translate the set theoretic general definition
of Fisher's inequality to a more traditional design theoretic version on pairwise balanced designs. 
Two versions of this are given using different trivial (but crucial) conditions on design properties\<close>
context ordered_pairwise_balance
begin

corollary general_nonuniform_fishers: \<comment> \<open>only valid on incomplete designs \<close>
  assumes "\<Lambda> > 0" 
  assumes "\<And> bl. bl \<in># \<B> \<Longrightarrow> incomplete_block bl" 
    \<comment> \<open> i.e. not a super trivial design with only complete blocks \<close>
  shows "\<v> \<le> \<b>"
proof -
  have "mset (\<B>s*) = dual_blocks \<V> \<B>s" using dual_blocks_ordered_eq by simp
  then interpret des: simple_const_intersect_design "set [0..<(length \<B>s)]" "mset (\<B>s*)" \<Lambda> 
    using assms dual_is_simp_const_inter_des by simp
  interpret odes: simp_ordered_const_intersect_design "[0..<length \<B>s]" "\<B>s*" \<Lambda> 
    using distinct_upt des.wellformed by (unfold_locales) (blast)
  have "length (\<B>s*) \<le> length [0..<length \<B>s]" using odes.general_fishers_inequality
    using odes.blocks_list_length odes.points_list_length by presburger
  then have "\<v> \<le> length \<B>s"
    by (simp add: dual_blocks_len points_list_length) 
  then show ?thesis by auto
qed

corollary general_nonuniform_fishers_comp: 
  assumes "\<Lambda> > 0" 
  assumes "count \<B> \<V> < \<Lambda>" \<comment> \<open> i.e. not a super trivial design with only complete blocks and single blocks \<close>
  shows "\<v> \<le> \<b>"
proof -
  define B where "B = (removeAll_mset \<V> \<B>)"
  have b_smaller: "size B \<le> \<b>" using B_def removeAll_size_lt by simp
  then have b_incomp: "\<And> bl. bl \<in># B \<Longrightarrow> card bl < \<v>"
    using wellformed B_def by (simp add: psubsetI psubset_card_mono) 
  have index_gt: "(\<Lambda> - (count \<B> \<V>)) > 0" using assms by simp 
  interpret pbd: pairwise_balance \<V> B "(\<Lambda> - (count \<B> \<V>))"
    using remove_all_complete_blocks_pbd B_def assms(2) by blast 
  obtain Bs where m: "mset Bs = B"
    using ex_mset by blast 
  interpret opbd: ordered_pairwise_balance \<V>s Bs "(\<Lambda> - (count \<B> \<V>))" 
    by (intro pbd.ordered_pbdI) (simp_all add: m distinct)
  have "\<v> \<le> (size B)" using b_incomp opbd.general_nonuniform_fishers
    using index_gt m by blast 
  then show ?thesis using b_smaller m by auto
qed

end
end