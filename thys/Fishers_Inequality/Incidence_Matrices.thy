(* Author: Chelsea Edmonds
Theory: Incidence_Matrices.thy 
*)

section \<open> Incidence Vectors and Matrices \<close>
text \<open>Incidence Matrices are an important representation for any incidence set system. The majority
of basic definitions and properties proved in this theory are based on Stinson \<^cite>\<open>"stinsonCombinatorialDesignsConstructions2004"\<close>
and Colbourn \<^cite>\<open>"colbournHandbookCombinatorialDesigns2007"\<close>.\<close>

theory Incidence_Matrices imports "Design_Extras" Matrix_Vector_Extras "List-Index.List_Index"
 "Design_Theory.Design_Isomorphisms"
begin

subsection \<open>Incidence Vectors \<close>
text \<open>A function which takes an ordered list of points, and a block, 
returning a 0-1 vector $v$ where there is a 1 in the ith position if point i is in that block \<close>

definition inc_vec_of :: "'a list \<Rightarrow> 'a set \<Rightarrow> ('b :: {ring_1}) vec" where
"inc_vec_of Vs bl \<equiv> vec (length Vs) (\<lambda> i . if (Vs ! i) \<in> bl then 1 else 0)"

lemma inc_vec_one_zero_elems: "set\<^sub>v (inc_vec_of Vs bl) \<subseteq> {0, 1}"
  by (auto simp add: vec_set_def inc_vec_of_def)

lemma finite_inc_vec_elems: "finite (set\<^sub>v (inc_vec_of Vs bl))"
  using finite_subset inc_vec_one_zero_elems by blast

lemma inc_vec_elems_max_two: "card (set\<^sub>v (inc_vec_of Vs bl)) \<le> 2"
  using card_mono inc_vec_one_zero_elems finite.insertI card_0_eq card_2_iff
  by (smt (verit)  insert_absorb2 linorder_le_cases linordered_nonzero_semiring_class.zero_le_one 
      obtain_subset_with_card_n one_add_one subset_singletonD trans_le_add1) 

lemma inc_vec_dim: "dim_vec (inc_vec_of Vs bl) = length Vs"
  by (simp add: inc_vec_of_def)

lemma inc_vec_index: "i < length Vs \<Longrightarrow> inc_vec_of Vs bl $ i = (if (Vs ! i) \<in> bl then 1 else 0)"
  by (simp add: inc_vec_of_def)

lemma inc_vec_index_one_iff:  "i < length Vs \<Longrightarrow> inc_vec_of Vs bl $ i = 1 \<longleftrightarrow> Vs ! i \<in> bl"
  by (auto simp add: inc_vec_of_def ) 

lemma inc_vec_index_zero_iff: "i < length Vs \<Longrightarrow> inc_vec_of Vs bl $ i = 0 \<longleftrightarrow> Vs ! i \<notin> bl"
  by (auto simp add: inc_vec_of_def)

lemma inc_vec_of_bij_betw: 
  assumes "inj_on f (set Vs)"
  assumes "bl \<subseteq> (set Vs)"
  shows "inc_vec_of Vs bl = inc_vec_of (map f Vs) (f ` bl)"
proof (intro eq_vecI, simp_all add: inc_vec_dim)
  fix i assume "i < length Vs"
  then have "Vs ! i \<in> bl \<longleftrightarrow> (map f Vs) ! i \<in> (f ` bl)"
    by (metis assms(1) assms(2) inj_on_image_mem_iff nth_map nth_mem)
  then show "inc_vec_of Vs bl $ i = inc_vec_of (map f Vs) (f ` bl) $ i"
    using inc_vec_index by (metis \<open>i < length Vs\<close> length_map) 
qed

subsection \<open> Incidence Matrices \<close>

text \<open> A function which takes a list of points, and list of sets of points, and returns 
a $v \times b$ 0-1 matrix $M$, where $v$ is the number of points, and $b$ the number of sets, such 
that there is a 1 in the i, j position if and only if point i is in block j. The matrix has 
type @{typ "('b :: ring_1) mat"} to allow for operations commonly used on matrices \<^cite>\<open>"stinsonCombinatorialDesignsConstructions2004"\<close>\<close>

definition inc_mat_of :: "'a list \<Rightarrow> 'a set list \<Rightarrow> ('b :: {ring_1}) mat" where
"inc_mat_of Vs Bs \<equiv> mat (length Vs) (length Bs) (\<lambda> (i,j) . if (Vs ! i) \<in> (Bs ! j) then 1 else 0)"

text \<open> Basic lemmas on the @{term "inc_mat_of"} matrix result (elements/dimensions/indexing)\<close>

lemma inc_mat_one_zero_elems: "elements_mat (inc_mat_of Vs Bs) \<subseteq> {0, 1}"
  by (auto simp add: inc_mat_of_def elements_mat_def)

lemma fin_incidence_mat_elems: "finite (elements_mat (inc_mat_of Vs Bs))"
  using finite_subset inc_mat_one_zero_elems by auto 

lemma inc_matrix_elems_max_two: "card (elements_mat (inc_mat_of Vs Bs)) \<le> 2"
  using inc_mat_one_zero_elems order_trans card_2_iff
  by (smt (verit, del_insts) antisym bot.extremum card.empty insert_commute insert_subsetI 
      is_singletonI is_singleton_altdef linorder_le_cases not_one_le_zero one_le_numeral  subset_insert) 

lemma inc_mat_of_index [simp]: "i < dim_row (inc_mat_of Vs Bs) \<Longrightarrow> j < dim_col (inc_mat_of Vs Bs) \<Longrightarrow> 
  inc_mat_of Vs Bs $$ (i, j) = (if (Vs ! i) \<in> (Bs ! j) then 1 else 0)"
  by (simp add: inc_mat_of_def)

lemma inc_mat_dim_row: "dim_row (inc_mat_of Vs Bs) = length Vs"
  by (simp add: inc_mat_of_def)

lemma inc_mat_dim_vec_row: "dim_vec (row (inc_mat_of Vs Bs) i) = length Bs"
  by (simp add:  inc_mat_of_def)

lemma inc_mat_dim_col: "dim_col (inc_mat_of Vs Bs) = length Bs"
  by (simp add:  inc_mat_of_def)

lemma inc_mat_dim_vec_col: "dim_vec (col (inc_mat_of Vs Bs) i) = length Vs"
  by (simp add:  inc_mat_of_def)

lemma inc_matrix_point_in_block_one: "i < length Vs \<Longrightarrow> j < length Bs \<Longrightarrow> Vs ! i \<in> Bs ! j
    \<Longrightarrow> (inc_mat_of Vs Bs) $$ (i, j) = 1"
  by (simp add: inc_mat_of_def)   

lemma inc_matrix_point_not_in_block_zero: "i < length Vs \<Longrightarrow> j < length Bs \<Longrightarrow> Vs ! i \<notin> Bs ! j \<Longrightarrow> 
    (inc_mat_of Vs Bs) $$ (i, j) = 0"
  by(simp add: inc_mat_of_def)

lemma inc_matrix_point_in_block: "i < length Vs \<Longrightarrow> j < length Bs \<Longrightarrow> (inc_mat_of Vs Bs) $$ (i, j) = 1 
    \<Longrightarrow> Vs ! i \<in> Bs ! j"
  using inc_matrix_point_not_in_block_zero by (metis zero_neq_one) 

lemma inc_matrix_point_not_in_block:  "i < length Vs \<Longrightarrow> j < length Bs \<Longrightarrow> 
    (inc_mat_of Vs Bs) $$ (i, j) = 0 \<Longrightarrow> Vs ! i \<notin> Bs ! j"
  using inc_matrix_point_in_block_one by (metis zero_neq_one)

lemma inc_matrix_point_not_in_block_iff:  "i < length Vs \<Longrightarrow> j < length Bs \<Longrightarrow> 
    (inc_mat_of Vs Bs) $$ (i, j) = 0 \<longleftrightarrow> Vs ! i \<notin> Bs ! j"
  using inc_matrix_point_not_in_block inc_matrix_point_not_in_block_zero by blast

lemma inc_matrix_point_in_block_iff:  "i < length Vs \<Longrightarrow> j < length Bs \<Longrightarrow>
    (inc_mat_of Vs Bs) $$ (i, j) = 1 \<longleftrightarrow> Vs ! i \<in> Bs ! j"
  using inc_matrix_point_in_block inc_matrix_point_in_block_one by blast

lemma inc_matrix_subset_implies_one: 
  assumes "I \<subseteq> {..< length Vs}"
  assumes "j < length Bs"
  assumes "(!) Vs ` I \<subseteq> Bs ! j"
  assumes "i \<in> I"
  shows "(inc_mat_of Vs Bs) $$ (i, j) = 1"
proof - 
  have iin: "Vs ! i \<in> Bs ! j" using assms(3) assms(4) by auto
  have "i < length Vs" using assms(1) assms(4) by auto
  thus ?thesis using iin inc_matrix_point_in_block_iff assms(2) by blast  
qed

lemma inc_matrix_one_implies_membership: "I \<subseteq> {..< length Vs} \<Longrightarrow> j < length Bs \<Longrightarrow> 
    (\<And> i. i\<in>I \<Longrightarrow> (inc_mat_of Vs Bs) $$ (i, j) = 1) \<Longrightarrow> i \<in> I \<Longrightarrow> Vs ! i \<in> Bs ! j"
  using inc_matrix_point_in_block subset_iff by blast 

lemma inc_matrix_elems_one_zero: "i < length Vs \<Longrightarrow> j < length Bs \<Longrightarrow> 
    (inc_mat_of Vs Bs) $$ (i, j) = 0 \<or> (inc_mat_of Vs Bs) $$ (i, j) = 1"
  using inc_matrix_point_in_block_one inc_matrix_point_not_in_block_zero by blast

text \<open>Reasoning on Rows/Columns of the incidence matrix \<close>

lemma inc_mat_col_def:  "j < length Bs \<Longrightarrow> i < length Vs \<Longrightarrow> 
    (col (inc_mat_of Vs Bs) j) $ i = (if (Vs ! i \<in> Bs ! j) then 1 else 0)"
  by (simp add: inc_mat_of_def) 

lemma inc_mat_col_list_map_elem: "j < length Bs \<Longrightarrow> i < length Vs \<Longrightarrow> 
    col (inc_mat_of Vs Bs) j $ i = map_vec (\<lambda> x . if (x \<in> (Bs ! j)) then 1 else 0) (vec_of_list Vs) $ i"
  by (simp add: inc_mat_of_def index_vec_of_list)

lemma inc_mat_col_list_map:  "j < length Bs \<Longrightarrow> 
    col (inc_mat_of Vs Bs) j = map_vec (\<lambda> x . if (x \<in> (Bs ! j)) then 1 else 0) (vec_of_list Vs)"
  by (intro eq_vecI) 
    (simp_all add: inc_mat_dim_row inc_mat_dim_col inc_mat_col_list_map_elem index_vec_of_list)

lemma inc_mat_row_def: "j < length Bs \<Longrightarrow> i < length Vs \<Longrightarrow> 
    (row (inc_mat_of Vs Bs) i) $ j = (if (Vs ! i \<in> Bs ! j) then 1 else 0)"
  by (simp add: inc_mat_of_def)

lemma inc_mat_row_list_map_elem: "j < length Bs \<Longrightarrow> i < length Vs \<Longrightarrow> 
    row (inc_mat_of Vs Bs) i $ j = map_vec (\<lambda> bl . if ((Vs ! i) \<in> bl) then 1 else 0) (vec_of_list Bs) $ j"
  by (simp add: inc_mat_of_def vec_of_list_index)

lemma inc_mat_row_list_map: "i < length Vs \<Longrightarrow> 
    row (inc_mat_of Vs Bs) i = map_vec (\<lambda> bl . if ((Vs ! i) \<in> bl) then 1 else 0) (vec_of_list Bs)"
  by (intro eq_vecI) 
    (simp_all add: inc_mat_dim_row inc_mat_dim_col inc_mat_row_list_map_elem index_vec_of_list)

text \<open> Connecting @{term "inc_vec_of"} and @{term "inc_mat_of"} \<close>

lemma inc_mat_col_inc_vec: "j < length Bs \<Longrightarrow> col (inc_mat_of Vs Bs) j = inc_vec_of Vs (Bs ! j)"
  by (auto simp add: inc_mat_of_def inc_vec_of_def)

lemma inc_mat_of_cols_inc_vecs: "cols (inc_mat_of Vs Bs) = map (\<lambda> j . inc_vec_of Vs j) Bs"
proof (intro nth_equalityI)
  have l1: "length (cols (inc_mat_of Vs Bs)) = length Bs"
    using inc_mat_dim_col by simp
  have l2: "length (map (\<lambda> j . inc_vec_of Vs j) Bs) = length Bs"
    using length_map by simp
  then show "length (cols (inc_mat_of Vs Bs)) = length (map (inc_vec_of Vs) Bs)" 
    using l1 l2 by simp
  show "\<And> i. i < length (cols (inc_mat_of Vs Bs)) \<Longrightarrow> 
    (cols (inc_mat_of Vs Bs) ! i) = (map (\<lambda> j . inc_vec_of Vs j) Bs) ! i"
    using inc_mat_col_inc_vec l1 by (metis cols_nth inc_mat_dim_col nth_map) 
qed

lemma inc_mat_of_bij_betw: 
  assumes "inj_on f (set Vs)"
  assumes "\<And> bl . bl \<in> (set Bs) \<Longrightarrow> bl \<subseteq> (set Vs)"
  shows "inc_mat_of Vs Bs = inc_mat_of (map f Vs) (map ((`) f) Bs)"
proof (intro eq_matI, simp_all add: inc_mat_dim_row inc_mat_dim_col, intro impI)
  fix i j assume ilt: "i < length Vs" and jlt: " j < length Bs" and "Vs ! i \<notin> Bs ! j"
  then show "f (Vs ! i) \<notin> f ` Bs ! j"
    by (meson assms(1) assms(2) ilt inj_on_image_mem_iff jlt nth_mem) 
qed

text \<open>Definitions for the incidence matrix representation of common incidence system properties \<close>

definition non_empty_col :: "('a :: {zero_neq_one}) mat \<Rightarrow> nat \<Rightarrow> bool" where
"non_empty_col M j \<equiv> \<exists> k. k \<noteq> 0 \<and> k \<in>$ col M j"

definition proper_inc_mat :: "('a :: {zero_neq_one}) mat \<Rightarrow> bool" where
"proper_inc_mat M \<equiv> (dim_row M > 0 \<and> dim_col M > 0)"

text \<open>Matrix version of the representation number property @{term "point_replication_number"}\<close>
definition mat_rep_num :: "('a :: {zero_neq_one}) mat \<Rightarrow> nat \<Rightarrow> nat" where
"mat_rep_num M i \<equiv> count_vec (row M i) 1"

text \<open>Matrix version of the points index property @{term "points_index"}\<close>
definition mat_point_index :: "('a :: {zero_neq_one}) mat \<Rightarrow> nat set \<Rightarrow> nat" where
"mat_point_index M I \<equiv> card {j . j < dim_col M \<and> (\<forall> i \<in> I. M $$ (i, j) = 1)}"

definition mat_inter_num :: "('a :: {zero_neq_one}) mat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
"mat_inter_num M j1 j2 \<equiv> card {i . i < dim_row M \<and> M $$ (i, j1) = 1 \<and>  M $$ (i, j2) = 1}"

text \<open>Matrix version of the block size property\<close>
definition mat_block_size :: "('a :: {zero_neq_one}) mat \<Rightarrow> nat \<Rightarrow> nat" where
"mat_block_size M j \<equiv> count_vec (col M j) 1"

lemma non_empty_col_obtains: 
  assumes "non_empty_col M j"
  obtains i where "i < dim_row M" and "(col M j) $ i \<noteq> 0"
proof -
  have d: "dim_vec (col M j) = dim_row M" by simp
  from assms obtain k where "k \<noteq> 0" and "k \<in>$ col M j" 
    by (auto simp add: non_empty_col_def)
  thus ?thesis using vec_contains_obtains_index d
    by (metis that) 
qed

lemma non_empty_col_alt_def: 
  assumes "j < dim_col M" 
  shows "non_empty_col M j \<longleftrightarrow> (\<exists> i. i < dim_row M \<and> M $$ (i, j) \<noteq> 0)"
proof (intro iffI)
  show "non_empty_col M j \<Longrightarrow> \<exists>i<dim_row M. M $$ (i, j) \<noteq> 0"
    by(metis assms index_col non_empty_col_obtains)
next 
  assume "\<exists>i<dim_row M. M $$ (i, j) \<noteq> 0"
  then obtain i where ilt: " i < dim_row M" and ne: "M $$ (i, j) \<noteq> 0" by blast
  then have ilt2: " i < dim_vec (col M j)" by simp
  then have "(col M j) $ i \<noteq> 0" using ne by (simp add: assms) 
  then obtain k where "(col M j) $ i = k" and "k \<noteq> 0"
    by simp
  then show "non_empty_col M j " using non_empty_col_def
    by (metis ilt2 vec_setI) 
qed

lemma proper_inc_mat_map: "proper_inc_mat M \<Longrightarrow> proper_inc_mat (map_mat f M)"
  by (simp add: proper_inc_mat_def)

lemma mat_point_index_alt: "mat_point_index M I = card {j \<in> {0..<dim_col M} . (\<forall> i \<in> I . M $$(i, j) = 1)}"
  by (simp add: mat_point_index_def)

lemma mat_block_size_sum_alt: 
  fixes M :: "'a :: {ring_1} mat"
  shows "elements_mat M \<subseteq> {0, 1} \<Longrightarrow> j < dim_col M \<Longrightarrow> of_nat (mat_block_size M j) = sum_vec (col M j)"
  unfolding mat_block_size_def using count_vec_sum_ones_alt col_elems_subset_mat subset_trans
  by metis  

lemma mat_rep_num_sum_alt: 
  fixes M :: "'a :: {ring_1} mat"
  shows "elements_mat M \<subseteq> {0, 1} \<Longrightarrow> i < dim_row M \<Longrightarrow> of_nat (mat_rep_num M i) = sum_vec (row M i)"
  using count_vec_sum_ones_alt
  by (metis mat_rep_num_def row_elems_subset_mat subset_trans) 

lemma mat_point_index_two_alt: 
  assumes "i1 < dim_row M"
  assumes "i2 < dim_row M"
  shows "mat_point_index M {i1, i2} = card {j . j < dim_col M \<and> M $$(i1, j) = 1 \<and> M $$ (i2, j) = 1}"
proof -
  let ?I = "{i1, i2}"
  have ss: "{i1, i2} \<subseteq> {..<dim_row M}" using assms by blast
  have filter: "\<And> j . j < dim_col M \<Longrightarrow> (\<forall> i \<in> ?I . M $$(i, j) = 1) \<longleftrightarrow> M $$(i1, j) = 1 \<and> M $$ (i2, j) = 1"
    by auto
  have "?I \<subseteq> {..< dim_row M}" using assms(1) assms(2) by fastforce
  thus ?thesis using filter ss unfolding mat_point_index_def
    by meson 
qed

text \<open> Transpose symmetries \<close>

lemma trans_mat_rep_block_size_sym: "j < dim_col M \<Longrightarrow> mat_block_size M j = mat_rep_num M\<^sup>T j"
  "i < dim_row M \<Longrightarrow> mat_rep_num M i = mat_block_size M\<^sup>T i"
  unfolding mat_block_size_def mat_rep_num_def by simp_all

lemma trans_mat_point_index_inter_sym: 
  "i1 < dim_row M \<Longrightarrow> i2 < dim_row M \<Longrightarrow> mat_point_index M {i1, i2} = mat_inter_num M\<^sup>T i1 i2"
  "j1 < dim_col M \<Longrightarrow> j2 < dim_col M \<Longrightarrow> mat_inter_num M j1 j2 = mat_point_index M\<^sup>T {j1, j2}"
   apply (simp_all add: mat_inter_num_def mat_point_index_two_alt)
   apply (metis (no_types, lifting) index_transpose_mat(1))
  by (metis (no_types, lifting) index_transpose_mat(1))

subsection \<open>0-1 Matrices \<close>
text \<open>Incidence matrices contain only two elements: 0 and 1. We define a locale which provides
a context to work in for matrices satisfying this condition for any @{typ "'b :: zero_neq_one"} type.\<close>
locale zero_one_matrix = 
  fixes matrix :: "'b :: {zero_neq_one} mat" ("M")
  assumes elems01: "elements_mat M \<subseteq> {0, 1}"
begin

text \<open> Row and Column Properties of the Matrix \<close>

lemma row_elems_ss01:"i < dim_row M \<Longrightarrow> vec_set (row M i) \<subseteq> {0, 1}"
  using row_elems_subset_mat elems01 by blast

lemma col_elems_ss01: 
  assumes "j < dim_col M"
  shows "vec_set (col M j) \<subseteq> {0, 1}"
proof -
  have "vec_set (col M j) \<subseteq> elements_mat M" using assms 
    by (simp add: col_elems_subset_mat assms) 
  thus ?thesis using elems01 by blast
qed

lemma col_nth_0_or_1_iff: 
  assumes "j < dim_col M"
  assumes "i < dim_row M"
  shows "col M j $ i = 0 \<longleftrightarrow> col M j $ i \<noteq> 1"
proof (intro iffI)
  have dv: "i < dim_vec (col M j)" using assms by simp
  have sv: "set\<^sub>v (col M j) \<subseteq> {0, 1}" using col_elems_ss01 assms by simp
  then show "col M j $ i = 0 \<Longrightarrow> col M j $ i \<noteq> 1" using dv by simp
  show "col M j $ i \<noteq> 1 \<Longrightarrow> col M j $ i = 0" using dv sv
    by (meson insertE singletonD subset_eq vec_setI) 
qed

lemma row_nth_0_or_1_iff: 
  assumes "j < dim_col M"
  assumes "i < dim_row M"
  shows "row M i $ j = 0 \<longleftrightarrow> row M i $ j \<noteq> 1"
proof (intro iffI)
  have dv: "j < dim_vec (row M i)" using assms by simp
  have sv: "set\<^sub>v (row M i) \<subseteq> {0, 1}" using row_elems_ss01 assms by simp
  then show "row M i $ j = 0 \<Longrightarrow> row M i $ j \<noteq> 1" by simp
  show "row M i $ j \<noteq> 1 \<Longrightarrow> row M i $ j = 0" using dv sv
    by (meson insertE singletonD subset_eq vec_setI) 
qed

lemma transpose_entries: "elements_mat (M\<^sup>T) \<subseteq> {0, 1}"
  using elems01 transpose_mat_elems by metis 

lemma M_not_zero_simp: "j < dim_col M \<Longrightarrow> i < dim_row M \<Longrightarrow> M $$ (i, j) \<noteq> 0 \<Longrightarrow> M $$ (i, j) = 1"
  using elems01 by auto

lemma M_not_one_simp: "j < dim_col M \<Longrightarrow> i < dim_row M \<Longrightarrow> M $$ (i, j) \<noteq> 1 \<Longrightarrow> M $$ (i, j) = 0"
  using elems01 by auto

text \<open>Definition for mapping a column to a block \<close>
definition map_col_to_block :: "'a :: {zero_neq_one} vec  \<Rightarrow> nat set" where
"map_col_to_block c \<equiv> { i \<in> {..<dim_vec c} . c $ i = 1}"

lemma map_col_to_block_alt: "map_col_to_block c = {i . i < dim_vec c \<and> c$ i = 1}"
  by (simp add: map_col_to_block_def)

lemma map_col_to_block_elem: "i < dim_vec c \<Longrightarrow> i \<in> map_col_to_block c \<longleftrightarrow>  c $ i = 1"
  by (simp add: map_col_to_block_alt)

lemma in_map_col_valid_index: "i \<in> map_col_to_block c \<Longrightarrow> i < dim_vec c"
  by (simp add: map_col_to_block_alt)

lemma map_col_to_block_size: "j < dim_col M \<Longrightarrow> card (map_col_to_block (col M j)) = mat_block_size M j"
  unfolding mat_block_size_def map_col_to_block_alt using count_vec_alt[of "col M j" "1"] Collect_cong
  by (metis (no_types, lifting))

lemma in_map_col_valid_index_M: "j < dim_col M \<Longrightarrow> i \<in> map_col_to_block (col M j) \<Longrightarrow> i < dim_row M"
  using in_map_col_valid_index by (metis dim_col) 

lemma map_col_to_block_elem_not: "c \<in> set (cols M) \<Longrightarrow> i < dim_vec c \<Longrightarrow> i \<notin> map_col_to_block c \<longleftrightarrow> c $ i = 0"
  apply (auto simp add: map_col_to_block_alt)
  using elems01 by (metis col_nth_0_or_1_iff dim_col obtain_col_index) 

lemma obtain_block_index_map_block_set: 
  assumes "bl \<in># {# map_col_to_block c . c \<in># mset (cols M)#}"
  obtains j where "j < dim_col M" and "bl = map_col_to_block (col M j)"
proof -
  obtain c where bleq: "bl = map_col_to_block c" and "c \<in># mset (cols M)"
    using assms by blast
  then have "c \<in> set (cols M)" by simp
  thus ?thesis using bleq obtain_col_index
    by (metis that)
qed

lemma mat_ord_inc_sys_point[simp]: "x < dim_row M \<Longrightarrow> [0..<(dim_row M)] ! x = x"
  by simp

lemma mat_ord_inc_sys_block[simp]: "j < dim_col M \<Longrightarrow> 
  (map (map_col_to_block) (cols M)) ! j = map_col_to_block (col M j)"
  by auto

lemma ordered_to_mset_col_blocks:
  "{# map_col_to_block c . c \<in># mset (cols M)#} = mset (map (map_col_to_block) (cols M))"
  by simp

text \<open> Lemmas on incidence matrix properties \<close>
lemma non_empty_col_01: 
  assumes "j < dim_col M"
  shows "non_empty_col M j \<longleftrightarrow> 1 \<in>$ col M j"
proof (intro iffI)
  assume "non_empty_col M j"
  then obtain k where kn0: "k \<noteq> 0" and kin: "k \<in>$ col M j" using non_empty_col_def
    by blast
  then have "k \<in> elements_mat M" using vec_contains_col_elements_mat assms
    by metis 
  then have "k = 1" using kn0
    using elems01 by blast 
  thus "1 \<in>$ col M j" using kin by simp
next
  assume "1 \<in>$ col M j"
  then show "non_empty_col M j" using non_empty_col_def
    by (metis zero_neq_one)
qed

lemma mat_rep_num_alt: 
  assumes "i < dim_row M"
  shows "mat_rep_num M i = card {j . j < dim_col M \<and> M $$ (i, j) = 1}"
proof (simp add: mat_rep_num_def)
  have eq: "\<And> j. (j < dim_col M \<and> M $$ (i, j) = 1) = (row M i $ j = 1 \<and> j < dim_vec (row M i))" 
    using assms by auto
  have "count_vec (row M i) 1 = card {j. (row M i) $ j = 1 \<and>  j < dim_vec (row M i)}"
    using count_vec_alt[of "row M i" "1"] by simp
  thus "count_vec (row M i) 1 = card {j. j < dim_col M \<and> M $$ (i, j) = 1}"
    using eq Collect_cong by simp
qed

lemma mat_rep_num_alt_col: "i < dim_row M \<Longrightarrow> mat_rep_num M i = size {#c \<in># (mset (cols M)) . c $ i = 1#}"
  using mat_rep_num_alt index_to_col_card_size_prop[of i M] by auto

text \<open> A zero one matrix is an incidence system \<close>

lemma map_col_to_block_wf: "\<And>c. c \<in> set (cols M) \<Longrightarrow> map_col_to_block c \<subseteq> {0..<dim_row M}"
  by (auto simp add: map_col_to_block_def)(metis dim_col obtain_col_index)

lemma one_implies_block_nempty: "j < dim_col M \<Longrightarrow> 1 \<in>$ (col M j) \<Longrightarrow> map_col_to_block (col M j) \<noteq> {}"
  unfolding map_col_to_block_def using vec_setE by force 

interpretation incidence_sys: incidence_system "{0..<dim_row M}" 
    "{# map_col_to_block c . c \<in># mset (cols M)#}"
  using map_col_to_block_wf by (unfold_locales) auto 

interpretation fin_incidence_sys: finite_incidence_system "{0..<dim_row M}" 
    "{# map_col_to_block c . c \<in># mset (cols M)#}"
  by (unfold_locales) (simp)

lemma block_nempty_implies_all_zeros: "j < dim_col M \<Longrightarrow> map_col_to_block (col M j) = {} \<Longrightarrow> 
    i < dim_row M \<Longrightarrow> col M j $ i = 0"
  by (metis col_nth_0_or_1_iff dim_col one_implies_block_nempty vec_setI)

lemma block_nempty_implies_no_one: "j < dim_col M \<Longrightarrow> map_col_to_block (col M j) = {} \<Longrightarrow> \<not> (1 \<in>$ (col M j))"
  using one_implies_block_nempty by blast

lemma mat_is_design:
  assumes "\<And>j. j < dim_col M\<Longrightarrow> 1 \<in>$ (col M j)"
  shows "design {0..<dim_row M} {# map_col_to_block c . c \<in># mset (cols M)#}"
proof (unfold_locales)
  fix bl 
  assume "bl \<in># {# map_col_to_block c . c \<in># mset (cols M)#}"
  then obtain j where "j < dim_col M" and map: "bl = map_col_to_block (col M j)"
    using obtain_block_index_map_block_set by auto
  thus "bl \<noteq> {}" using assms one_implies_block_nempty
    by simp 
qed

lemma mat_is_proper_design: 
  assumes "\<And>j. j < dim_col M \<Longrightarrow> 1 \<in>$ (col M j)"
  assumes "dim_col M > 0"
  shows "proper_design {0..<dim_row M} {# map_col_to_block c . c \<in># mset (cols M)#}"
proof -
  interpret des: design "{0..<dim_row M}" "{# map_col_to_block c . c \<in># mset (cols M)#}"
    using mat_is_design assms by simp
  show ?thesis proof (unfold_locales)
    have "length (cols M) \<noteq> 0" using assms(2) by auto
    then have "size {# map_col_to_block c . c \<in># mset (cols M)#} \<noteq> 0" by auto
    then show "incidence_sys.\<b> \<noteq> 0" by simp
  qed
qed

text \<open> Show the 01 injective function preserves system properties \<close>

lemma inj_on_01_hom_index:
  assumes "inj_on_01_hom f"
  assumes "i < dim_row M" "j < dim_col M"
  shows "M $$ (i, j) = 1  \<longleftrightarrow> (map_mat f M) $$ (i, j) = 1"
    and "M $$ (i, j) = 0  \<longleftrightarrow> (map_mat f M) $$ (i, j) = 0"
proof -
  interpret hom: inj_on_01_hom f using assms by simp
  show "M $$ (i, j) = 1  \<longleftrightarrow> (map_mat f M) $$ (i, j) = 1" 
    using assms col_nth_0_or_1_iff
    by (simp add: hom.inj_1_iff) 
  show "M $$ (i, j) = 0  \<longleftrightarrow> (map_mat f M) $$ (i, j) = 0"
    using assms col_nth_0_or_1_iff
    by (simp add: hom.inj_0_iff) 
qed

lemma preserve_non_empty: 
  assumes "inj_on_01_hom f" 
  assumes "j < dim_col M"
  shows "non_empty_col M j \<longleftrightarrow> non_empty_col (map_mat f M) j"
proof(simp add: non_empty_col_def, intro iffI) 
  interpret hom: inj_on_01_hom f using assms(1) by simp
  assume "\<exists>k. k \<noteq> 0 \<and> k \<in>$ col M j"
  then obtain k where kneq: "k \<noteq> 0" and kin: "k \<in>$ col M j" by blast
  then have "f k \<in>$ col (map_mat f M) j" using vec_contains_img
    by (metis assms(2) col_map_mat) 
  then have "f k \<noteq> 0" using assms(1) kneq kin assms(2) col_elems_ss01 hom.inj_0_iff by blast
  thus "\<exists>k. k \<noteq> 0 \<and> k \<in>$ col (map_mat f M) j"
    using \<open>f k \<in>$ col (map_mat f M) j\<close> by blast
next
  interpret hom: inj_on_01_hom f using assms(1) by simp
  assume "\<exists>k. k \<noteq> 0 \<and> k \<in>$ col (map_mat f M) j"
  then obtain k where kneq: "k \<noteq> 0" and kin: "k \<in>$ col (map_mat f M) j" by blast
  then have "k \<in>$ map_vec f (col M j)" using assms(2) col_map_mat by simp
  then have "k \<in> f ` set\<^sub>v (col M j)"
    by (smt (verit) image_eqI index_map_vec(1) index_map_vec(2) vec_setE vec_setI) 
  then obtain k' where keq: "k = f k'" and kin2: "k' \<in> set\<^sub>v (col M j)"
    by blast 
  then have "k' \<noteq> 0" using assms(1) kneq hom.inj_0_iff by blast 
  thus  "\<exists>k. k \<noteq> 0 \<and> k \<in>$ col M j" using kin2 by auto
qed

lemma preserve_mat_rep_num:
  assumes "inj_on_01_hom f"
  assumes "i < dim_row M"
  shows "mat_rep_num M i = mat_rep_num (map_mat f M) i"
  unfolding mat_rep_num_def using injective_lim.lim_inj_hom_count_vec inj_on_01_hom_def row_map_mat
  by (metis assms(1) assms(2) inj_on_01_hom.inj_1_iff insert_iff row_elems_ss01)

lemma preserve_mat_block_size: 
  assumes "inj_on_01_hom f"
  assumes "j < dim_col M"
  shows "mat_block_size M j = mat_block_size (map_mat f M) j"
  unfolding mat_block_size_def using injective_lim.lim_inj_hom_count_vec inj_on_01_hom_def col_map_mat
  by (metis assms(1) assms(2) inj_on_01_hom.inj_1_iff insert_iff col_elems_ss01)


lemma preserve_mat_point_index: 
  assumes "inj_on_01_hom f"
  assumes "\<And> i. i \<in> I \<Longrightarrow> i < dim_row M"
  shows "mat_point_index M I = mat_point_index (map_mat f M) I"
proof -
  have "\<And> i j. i \<in> I \<Longrightarrow> j < dim_col M \<and> M $$ (i, j) = 1 \<longleftrightarrow> 
      j < dim_col (map_mat f M) \<and> (map_mat f M) $$ (i, j) = 1"
    using assms(2) inj_on_01_hom_index(1) assms(1) by (metis index_map_mat(3)) 
  thus ?thesis unfolding mat_point_index_def
    by (metis (no_types, opaque_lifting) index_map_mat(3)) 
qed

lemma preserve_mat_inter_num: 
  assumes "inj_on_01_hom f"
  assumes "j1 < dim_col M" "j2 < dim_col M"
  shows "mat_inter_num M j1 j2 = mat_inter_num (map_mat f M) j1 j2"
  unfolding mat_inter_num_def using assms
  by (metis (no_types, opaque_lifting) index_map_mat(2) inj_on_01_hom_index(1)) 

lemma lift_mat_01_index_iff: 
  "i < dim_row M \<Longrightarrow> j < dim_col M \<Longrightarrow> (lift_01_mat M) $$ (i, j) = 0 \<longleftrightarrow> M $$ (i, j) = 0"
  "i < dim_row M \<Longrightarrow> j < dim_col M \<Longrightarrow> (lift_01_mat M) $$ (i, j) = 1 \<longleftrightarrow> M $$ (i, j) = 1"
  by (simp) (metis col_nth_0_or_1_iff index_col lift_01_mat_simp(3) of_zero_neq_one_def zero_neq_one) 

lemma lift_mat_elems: "elements_mat (lift_01_mat M) \<subseteq> {0, 1}"
proof -
  have "elements_mat (lift_01_mat M) = of_zero_neq_one ` (elements_mat M)"
    by (simp add: lift_01_mat_def map_mat_elements)
  then have "elements_mat (lift_01_mat M) \<subseteq> of_zero_neq_one ` {0, 1}" using elems01
    by fastforce 
  thus ?thesis
    by simp 
qed

lemma lift_mat_is_0_1: "zero_one_matrix (lift_01_mat M)"
  using lift_mat_elems by (unfold_locales)

lemma lift_01_mat_distinct_cols: "distinct (cols M) \<Longrightarrow> distinct (cols (lift_01_mat M))"
  using of_injective_lim.mat_cols_hom_lim_distinct_iff lift_01_mat_def
  by (metis elems01 map_vec_mat_cols) 

end

text \<open>Some properties must be further restricted to matrices having a @{typ "'a :: ring_1"} type \<close>
locale zero_one_matrix_ring_1 = zero_one_matrix M for M :: "'b :: {ring_1} mat"
begin

lemma map_col_block_eq: 
  assumes "c \<in> set(cols M)"
  shows "inc_vec_of [0..<dim_vec c] (map_col_to_block c) = c"
proof (intro eq_vecI, simp add: map_col_to_block_def inc_vec_of_def, intro impI)
  show "\<And>i. i < dim_vec c \<Longrightarrow> c $ i \<noteq> 1 \<Longrightarrow> c $ i = 0"
    using assms map_col_to_block_elem map_col_to_block_elem_not by auto 
  show "dim_vec (inc_vec_of [0..<dim_vec c] (map_col_to_block c)) = dim_vec c"
    unfolding inc_vec_of_def by simp 
qed

lemma inc_mat_of_map_rev: "inc_mat_of [0..<dim_row M] (map map_col_to_block (cols M)) = M"
proof (intro eq_matI, simp_all add: inc_mat_of_def, intro conjI impI)
  show "\<And>i j. i < dim_row M \<Longrightarrow> j < dim_col M \<Longrightarrow> i \<in> map_col_to_block (col M j) \<Longrightarrow> M $$ (i, j) = 1"
    by (simp add: map_col_to_block_elem)
  show "\<And>i j. i < dim_row M \<Longrightarrow> j < dim_col M \<Longrightarrow> i \<notin> map_col_to_block (col M j) \<Longrightarrow> M $$ (i, j) = 0"
    by (metis col_nth_0_or_1_iff dim_col index_col map_col_to_block_elem)
qed

lemma M_index_square_itself: "j < dim_col M \<Longrightarrow> i < dim_row M \<Longrightarrow> (M $$ (i, j))^2 = M $$ (i, j)"
  using M_not_zero_simp by (cases "M $$ (i, j) = 0")(simp_all, metis power_one) 

lemma M_col_index_square_itself: "j < dim_col M \<Longrightarrow> i < dim_row M \<Longrightarrow> ((col M j) $ i)^2 = (col M j) $ i"
  using index_col M_index_square_itself by auto 


text \<open> Scalar Prod Alternative definitions for matrix properties \<close>

lemma scalar_prod_inc_vec_block_size_mat:
  assumes "j < dim_col M"
  shows "(col M j) \<bullet> (col M j) = of_nat (mat_block_size M j)"
proof -
  have "(col M j) \<bullet> (col M j) = (\<Sum> i \<in> {0..<dim_row M} . (col M j) $ i * (col M j) $ i)" 
     using assms  scalar_prod_def sum.cong by (smt (verit, ccfv_threshold) dim_col) 
  also have "... = (\<Sum> i \<in> {0..<dim_row M} . ((col M j) $ i)^2)"
    by (simp add: power2_eq_square ) 
  also have "... = (\<Sum> i \<in> {0..<dim_row M} . ((col M j) $ i))"
    using M_col_index_square_itself assms by auto
  finally show ?thesis using sum_vec_def mat_block_size_sum_alt
    by (metis assms dim_col elems01) 
qed

lemma scalar_prod_inc_vec_mat_inter_num: 
  assumes "j1 < dim_col M" "j2 < dim_col M"
  shows "(col M j1) \<bullet> (col M j2) = of_nat (mat_inter_num M j1 j2)"
proof -
  have split: "{0..<dim_row M} = {i \<in> {0..<dim_row M} . (M $$ (i, j1) = 1) \<and> (M $$ (i, j2) = 1) } \<union> 
    {i \<in> {0..<dim_row M} . M $$ (i, j1) = 0 \<or> M $$ (i, j2) = 0}" using assms M_not_zero_simp by auto
  have inter: "{i \<in> {0..<dim_row M} . (M $$ (i, j1) = 1) \<and> (M $$ (i, j2) = 1) } \<inter> 
    {i \<in> {0..<dim_row M} . M $$ (i, j1) = 0 \<or> M $$ (i, j2) = 0} = {}" by auto
  have "(col M j1) \<bullet> (col M j2) = (\<Sum> i \<in> {0..<dim_row M} . (col M j1) $ i * (col M j2) $ i)" 
    using assms scalar_prod_def by (metis (full_types) dim_col) 
  also have "... = (\<Sum> i \<in> {0..<dim_row M} . M $$ (i, j1) * M $$ (i, j2))" 
    using assms by simp
  also have "... = (\<Sum> i \<in> {i \<in> {0..<dim_row M} . (M $$ (i, j1) = 1) \<and> (M $$ (i, j2) = 1) } . M $$ (i, j1) * M $$ (i, j2)) 
      + (\<Sum> i \<in> {i \<in> {0..<dim_row M} . M $$ (i, j1) = 0 \<or> M $$ (i, j2) = 0} . M $$ (i, j1) * M $$ (i, j2))" 
    using split inter sum.union_disjoint[of " {i \<in> {0..<dim_row M} . (M $$ (i, j1) = 1) \<and> (M $$ (i, j2) = 1)}" 
      "{i \<in> {0..<dim_row M} . M $$ (i, j1) = 0 \<or> M $$ (i, j2) = 0}" "\<lambda> i . M $$ (i, j1) * M $$ (i, j2)"]
    by (metis (no_types, lifting) finite_Un finite_atLeastLessThan) 
  also have "... = (\<Sum> i \<in> {i \<in> {0..<dim_row M} . (M $$ (i, j1) = 1) \<and> (M $$ (i, j2) = 1) } . 1) 
      + (\<Sum> i \<in> {i \<in> {0..<dim_row M} . M $$ (i, j1) = 0 \<or> M $$ (i, j2) = 0} . 0)" 
    using sum.cong mem_Collect_eq by (smt (z3) mult.right_neutral mult_not_zero) 
  finally have "(col M j1) \<bullet> (col M j2) = 
      of_nat (card {i . i < dim_row M \<and> (M $$ (i, j1) = 1) \<and> (M $$ (i, j2) = 1)})"
    by simp 
  then show ?thesis using mat_inter_num_def[of M j1 j2] by simp
qed

end

text \<open> Any matrix generated by @{term "inc_mat_of"} is a 0-1 matrix.\<close>
lemma inc_mat_of_01_mat: "zero_one_matrix_ring_1 (inc_mat_of Vs Bs)"
  by (unfold_locales) (simp add: inc_mat_one_zero_elems) 

subsection \<open>Ordered Incidence Systems \<close>
text \<open>We impose an arbitrary ordering on the point set and block collection to enable
matrix reasoning. Note that this is also common in computer algebra representations of designs \<close>

locale ordered_incidence_system =
  fixes \<V>s :: "'a list" and \<B>s :: "'a set list"
  assumes wf_list: "b \<in># (mset \<B>s) \<Longrightarrow> b \<subseteq> set \<V>s"
  assumes distinct: "distinct \<V>s"

text \<open>An ordered incidence system, as it is defined on lists, can only represent finite incidence systems \<close>
sublocale ordered_incidence_system \<subseteq> finite_incidence_system "set \<V>s" "mset \<B>s"
  by(unfold_locales) (auto simp add: wf_list)

lemma ordered_incidence_sysI: 
  assumes "finite_incidence_system \<V> \<B>" 
  assumes "\<V>s \<in> permutations_of_set \<V>" and "\<B>s \<in> permutations_of_multiset \<B>"
  shows "ordered_incidence_system \<V>s \<B>s"
proof -
  have veq: "\<V> = set \<V>s" using assms permutations_of_setD(1) by auto 
  have beq: "\<B> = mset \<B>s" using assms permutations_of_multisetD by auto
  interpret fisys: finite_incidence_system "set \<V>s" "mset \<B>s" using assms(1) veq beq by simp
  show ?thesis proof (unfold_locales)
    show "\<And>b. b \<in># mset \<B>s \<Longrightarrow> b \<subseteq> set \<V>s" using fisys.wellformed
      by simp 
    show "distinct \<V>s" using assms permutations_of_setD(2) by auto
  qed
qed

lemma ordered_incidence_sysII: 
  assumes "finite_incidence_system \<V> \<B>" and "set \<V>s = \<V>" and "distinct \<V>s" and "mset \<B>s = \<B>"
  shows "ordered_incidence_system \<V>s \<B>s"
proof -
  interpret fisys: finite_incidence_system "set \<V>s" "mset \<B>s" using assms by simp
  show ?thesis using fisys.wellformed assms by (unfold_locales) (simp_all)
qed

context ordered_incidence_system 
begin
text \<open>For ease of notation, establish the same notation as for incidence systems \<close>

abbreviation "\<V> \<equiv> set \<V>s"
abbreviation "\<B> \<equiv> mset \<B>s"

text \<open>Basic properties on ordered lists \<close>
lemma points_indexing: "\<V>s \<in> permutations_of_set \<V>"
  by (simp add: permutations_of_set_def distinct)

lemma blocks_indexing: "\<B>s \<in> permutations_of_multiset \<B>"
  by (simp add: permutations_of_multiset_def)

lemma points_list_empty_iff: "\<V>s = [] \<longleftrightarrow> \<V> = {}"
  using finite_sets points_indexing
  by (simp add: elem_permutation_of_set_empty_iff) 

lemma points_indexing_inj: "\<forall> i \<in> I . i < length \<V>s \<Longrightarrow> inj_on ((!) \<V>s) I"
  by (simp add: distinct inj_on_nth)

lemma blocks_list_empty_iff: "\<B>s = [] \<longleftrightarrow> \<B> = {#}"
  using blocks_indexing by (simp) 

lemma blocks_list_nempty: "proper_design \<V> \<B> \<Longrightarrow> \<B>s \<noteq> []"
  using mset.simps(1) proper_design.design_blocks_nempty by blast

lemma points_list_nempty: "proper_design \<V> \<B> \<Longrightarrow> \<V>s \<noteq> []"
  using proper_design.design_points_nempty points_list_empty_iff by blast

lemma points_list_length: "length \<V>s = \<v>"
  using points_indexing
  by (simp add: length_finite_permutations_of_set) 

lemma blocks_list_length: "length \<B>s = \<b>"
  using blocks_indexing length_finite_permutations_of_multiset by blast

lemma valid_points_index: "i < \<v> \<Longrightarrow> \<V>s ! i \<in> \<V>"
  using points_list_length by simp 

lemma valid_points_index_cons: "x \<in> \<V> \<Longrightarrow> \<exists> i. \<V>s ! i = x \<and> i < \<v>"
  using points_list_length by (auto simp add: in_set_conv_nth)

lemma valid_points_index_obtains: 
  assumes "x \<in> \<V>"
  obtains i where "\<V>s ! i = x \<and> i < \<v>"
  using valid_points_index_cons assms by auto

lemma valid_blocks_index: "j < \<b> \<Longrightarrow> \<B>s ! j \<in># \<B>"
  using blocks_list_length by (metis nth_mem_mset)

lemma valid_blocks_index_cons: "bl \<in># \<B> \<Longrightarrow> \<exists> j . \<B>s ! j = bl \<and> j < \<b>"
  by (auto simp add: in_set_conv_nth)

lemma valid_blocks_index_obtains: 
  assumes "bl \<in># \<B>"
  obtains j where  "\<B>s ! j = bl \<and> j < \<b>"
  using assms valid_blocks_index_cons by auto

lemma block_points_valid_point_index: 
  assumes "bl \<in># \<B>" "x \<in> bl"
  obtains i where "i < length \<V>s \<and> \<V>s ! i = x"
  using wellformed valid_points_index_obtains assms
  by (metis points_list_length wf_invalid_point) 

lemma points_set_index_img: "\<V> = image(\<lambda> i . (\<V>s ! i)) ({..<\<v>})"
  using valid_points_index_cons valid_points_index by auto

lemma blocks_mset_image: "\<B> = image_mset (\<lambda> i . (\<B>s ! i)) (mset_set {..<\<b>})"
  by (simp add: mset_list_by_index)

lemma incidence_cond_indexed[simp]: "i < \<v> \<Longrightarrow> j < \<b> \<Longrightarrow> incident (\<V>s ! i) (\<B>s ! j) \<longleftrightarrow> (\<V>s ! i) \<in> (\<B>s ! j)"
  using incidence_alt_def valid_points_index valid_blocks_index by simp

lemma bij_betw_points_index: "bij_betw (\<lambda> i. \<V>s ! i) {0..<\<v>} \<V>"
proof (simp add: bij_betw_def, intro conjI)
  show "inj_on ((!) \<V>s) {0..<\<v>}"
    by (simp add: points_indexing_inj points_list_length) 
  show "(!) \<V>s ` {0..<\<v>} = \<V>" 
  proof (intro subset_antisym subsetI)
    fix x assume "x \<in> (!) \<V>s ` {0..<\<v>}" 
    then obtain i where "x = \<V>s ! i" and "i < \<v>" by auto
    then show "x \<in> \<V>"
      by (simp add: valid_points_index) 
  next 
    fix x assume "x \<in> \<V>"
    then obtain i where "\<V>s ! i = x" and "i <\<v>"
      using valid_points_index_cons by auto 
    then show "x \<in> (!) \<V>s ` {0..<\<v>}" by auto
  qed
qed

text \<open>Some lemmas on cardinality due to different set descriptor filters \<close>
lemma card_filter_point_indices: "card {i \<in> {0..<\<v>}. P (\<V>s ! i)} = card {v \<in> \<V> . P v }"
proof -
  have "{v \<in> \<V> . P v }= (\<lambda> i. \<V>s ! i) ` {i \<in> {0..<\<v>}. P (\<V>s ! i)}"
    by (metis Compr_image_eq lessThan_atLeast0 points_set_index_img)
  thus ?thesis using inj_on_nth points_list_length
    by (metis (no_types, lifting) card_image distinct lessThan_atLeast0 lessThan_iff mem_Collect_eq)
qed

lemma card_block_points_filter: 
  assumes "j < \<b>"
  shows "card (\<B>s ! j) = card {i \<in> {0..<\<v>} . (\<V>s ! i) \<in> (\<B>s ! j)}"
proof -
  obtain bl where "bl \<in># \<B>" and blis: "bl = \<B>s ! j"
    using assms by auto
  then have cbl: "card bl = card {v \<in> \<V> . v \<in> bl}" using block_size_alt by simp
  have "\<V> = (\<lambda> i. \<V>s ! i) ` {0..<\<v>}" using bij_betw_points_index
    using lessThan_atLeast0 points_set_index_img by presburger
  then have "Set.filter (\<lambda> v . v \<in> bl) \<V> = Set.filter (\<lambda> v . v \<in> bl) ((\<lambda> i. \<V>s ! i) ` {0..<\<v>})"
    by presburger 
  have "card {i \<in> {0..<\<v>} . (\<V>s ! i) \<in> bl} = card {v \<in> \<V> . v \<in> bl}" 
    using card_filter_point_indices by simp
  thus ?thesis using cbl blis by simp
qed

lemma obtains_two_diff_block_indexes: 
  assumes "j1 < \<b>"
  assumes "j2 < \<b>"
  assumes "j1 \<noteq> j2"
  assumes "\<b> \<ge> 2"
  obtains bl1 bl2 where "bl1 \<in># \<B>" and "\<B>s ! j1 = bl1" and "bl2 \<in># \<B> - {#bl1#}" and "\<B>s ! j2 = bl2"
proof -
  have j1lt: "min j1 (length \<B>s) = j1" using assms by auto
  obtain bl1 where bl1in: "bl1 \<in># \<B>" and bl1eq: "\<B>s ! j1 = bl1"
    using assms(1) valid_blocks_index by blast
  then have split: "\<B>s = take j1 \<B>s @ \<B>s!j1 # drop (Suc j1) \<B>s" 
    using assms id_take_nth_drop by auto
  then have lj1: "length (take j1 \<B>s) = j1" using j1lt by (simp add: length_take[of j1 \<B>s]) 
  have "\<B> = mset (take j1 \<B>s @ \<B>s!j1 # drop (Suc j1) \<B>s)" using split assms(1) by presburger 
  then have bsplit: "\<B> = mset (take j1 \<B>s) + {#bl1#} + mset (drop (Suc j1) \<B>s)" by (simp add: bl1eq)
  then have btake: "\<B> - {#bl1#} = mset (take j1 \<B>s) + mset (drop (Suc j1) \<B>s)" by simp
  thus ?thesis proof (cases "j2 < j1")
    case True
    then have "j2 < length (take j1 \<B>s)" using lj1 by simp
    then obtain bl2 where bl2eq: "bl2 = (take j1 \<B>s) ! j2" by auto
    then have bl2eq2: "bl2 = \<B>s ! j2"
      by (simp add: True) 
    then have "bl2 \<in># \<B> - {#bl1#}" using btake
      by (metis bl2eq \<open>j2 < length (take j1 \<B>s)\<close> nth_mem_mset union_iff) 
    then show ?thesis using bl2eq2 bl1in bl1eq that by auto
  next
    case False
    then have j2gt: "j2 \<ge> Suc j1" using assms by simp
    then obtain i where ieq: "i = j2 - Suc j1"
      by simp 
    then have j2eq: "j2 = (Suc j1) + i" using j2gt by presburger
    have "length (drop (Suc j1) \<B>s) = \<b> - (Suc j1)" using blocks_list_length by auto
    then have "i < length (drop (Suc j1) \<B>s)" using ieq assms blocks_list_length
      using diff_less_mono j2gt by presburger 
    then obtain bl2 where bl2eq: "bl2 = (drop (Suc j1) \<B>s) ! i" by auto
    then have bl2in: "bl2 \<in># \<B> - {#bl1#}" using btake nth_mem_mset union_iff
      by (metis \<open>i < length (drop (Suc j1) \<B>s)\<close>) 
    then have "bl2 = \<B>s ! j2" using bl2eq nth_drop blocks_list_length assms j2eq
      by (metis Suc_leI)
    then show ?thesis using bl1in bl1eq bl2in that by auto
  qed
qed

lemma filter_size_blocks_eq_card_indexes: "size {# b \<in># \<B> . P b #} = card {j \<in> {..<(\<b>)}. P (\<B>s ! j)}"
proof -
  have "\<B> = image_mset (\<lambda> j . \<B>s ! j) (mset_set {..<(\<b>)})" 
    using blocks_mset_image by simp
  then have helper: "{# b \<in># \<B> . P b #} = image_mset (\<lambda> j . \<B>s ! j) {# j \<in># (mset_set {..< \<b>}). P (\<B>s ! j) #} "
    by (simp add: filter_mset_image_mset)
  have "card {j \<in> {..<\<b>}. P (\<B>s ! j)} = size {# j \<in># (mset_set {..< \<b>}). P (\<B>s ! j) #}"
    using card_size_filter_eq [of "{..<\<b>}"] by simp
  thus ?thesis using helper by simp
qed

lemma blocks_index_ne_belong: 
  assumes "i1 < length \<B>s"
  assumes "i2 < length \<B>s"
  assumes "i1 \<noteq> i2"
  shows "\<B>s ! i2 \<in># \<B> - {#(\<B>s ! i1)#}"
proof (cases "\<B>s ! i1 = \<B>s ! i2")
  case True
  then have "count (mset \<B>s) (\<B>s ! i1) \<ge> 2" using count_min_2_indices assms by fastforce
  then have "count ((mset \<B>s) - {#(\<B>s ! i1)#}) (\<B>s ! i1) \<ge> 1"
    by (metis Nat.le_diff_conv2 add_leD2 count_diff count_single nat_1_add_1) 
  then show ?thesis
    by (metis True count_inI not_one_le_zero)
next
  case False
  have "\<B>s ! i2 \<in># \<B>" using assms
    by simp 
  then show ?thesis using False
    by (metis in_remove1_mset_neq)
qed

lemma inter_num_points_filter_def: 
  assumes "j1 < \<b>" "j2 < \<b>" "j1 \<noteq> j2"
  shows "card {x \<in> {0..<\<v>} . ((\<V>s ! x) \<in> (\<B>s ! j1) \<and> (\<V>s ! x) \<in> (\<B>s ! j2)) } = (\<B>s ! j1) |\<inter>| (\<B>s ! j2)"
proof - 
  have inter: "\<And> v. v \<in> \<V> \<Longrightarrow> v \<in> (\<B>s ! j1) \<and> v \<in> (\<B>s ! j2) \<longleftrightarrow> v \<in> (\<B>s ! j1) \<inter> (\<B>s ! j2)"
    by simp 
  obtain bl1 bl2 where bl1in: "bl1 \<in># \<B>" and bl1eq: "\<B>s ! j1 = bl1" and bl2in: "bl2 \<in># \<B> - {#bl1#}" 
    and bl2eq: "\<B>s ! j2 = bl2" 
    using assms obtains_two_diff_block_indexes
    by (metis blocks_index_ne_belong size_mset valid_blocks_index) 
  have "card {x \<in> {0..<\<v>} . (\<V>s ! x) \<in> (\<B>s ! j1) \<and> (\<V>s ! x) \<in> (\<B>s ! j2) } = 
      card {v \<in> \<V> . v \<in> (\<B>s ! j1) \<and> v \<in> (\<B>s ! j2) }" 
    using card_filter_point_indices by simp
  also have "... = card {v \<in> \<V> . v \<in> bl1 \<and> v \<in> bl2 }" using bl1eq bl2eq by simp
  finally show ?thesis using points_inter_num_rep bl1in bl2in
    by (simp add: bl1eq bl2eq) 
qed

text \<open>Define an incidence matrix for this ordering of an incidence system \<close>

abbreviation N :: "int mat" where
"N \<equiv> inc_mat_of \<V>s \<B>s"

sublocale zero_one_matrix_ring_1 "N"
  using inc_mat_of_01_mat .

lemma N_alt_def_dim: "N = mat \<v> \<b> (\<lambda> (i,j) . if (incident (\<V>s ! i) (\<B>s ! j)) then 1 else 0) " 
  using incidence_cond_indexed inc_mat_of_def 
  by (intro eq_matI) (simp_all add: inc_mat_dim_row inc_mat_dim_col inc_matrix_point_in_block_one 
      inc_matrix_point_not_in_block_zero points_list_length)

text \<open>Matrix Dimension related lemmas \<close>
 
lemma N_carrier_mat: "N \<in> carrier_mat \<v> \<b>" 
  by (simp add: N_alt_def_dim)

lemma dim_row_is_v[simp]: "dim_row N = \<v>"
  by (simp add: N_alt_def_dim)

lemma dim_col_is_b[simp]: "dim_col N = \<b>"
  by (simp add:  N_alt_def_dim)

lemma dim_vec_row_N: "dim_vec (row N i) = \<b>"
  by (simp add:  N_alt_def_dim)

lemma dim_vec_col_N: "dim_vec (col N i) = \<v>" by simp 

lemma dim_vec_N_col: 
  assumes "j < \<b>"
  shows "dim_vec (cols N ! j) = \<v>"
proof -
  have "cols N ! j = col N j" using assms dim_col_is_b by simp
  then have "dim_vec (cols N ! j) = dim_vec (col N j)" by simp
  thus ?thesis using dim_col assms by (simp) 
qed

lemma N_carrier_mat_01_lift: "lift_01_mat N \<in> carrier_mat \<v> \<b>"
  by auto

text \<open>Transpose properties \<close>

lemma transpose_N_mult_dim: "dim_row (N * N\<^sup>T) = \<v>" "dim_col (N * N\<^sup>T) = \<v>"
  by (simp_all)

lemma N_trans_index_val: "i < dim_col N \<Longrightarrow> j < dim_row N \<Longrightarrow> 
    N\<^sup>T $$ (i, j) = (if (\<V>s ! j) \<in> (\<B>s ! i) then 1 else 0)"
  by (simp add: inc_mat_of_def)

text \<open>Matrix element and index related lemmas \<close>
lemma mat_row_elems: "i < \<v> \<Longrightarrow> vec_set (row N i) \<subseteq> {0, 1}"
  using points_list_length
  by (simp add: row_elems_ss01) 

lemma mat_col_elems: "j < \<b> \<Longrightarrow> vec_set (col N j) \<subseteq> {0, 1}"
  using blocks_list_length by (metis col_elems_ss01 dim_col_is_b)

lemma matrix_elems_one_zero: "i < \<v> \<Longrightarrow> j < \<b> \<Longrightarrow> N $$ (i, j) = 0 \<or> N $$ (i, j) = 1"
  by (metis blocks_list_length inc_matrix_elems_one_zero points_list_length)

lemma matrix_point_in_block_one: "i < \<v> \<Longrightarrow> j < \<b> \<Longrightarrow> (\<V>s ! i)\<in> (\<B>s ! j) \<Longrightarrow>N $$ (i, j) = 1"
  by (metis inc_matrix_point_in_block_one points_list_length blocks_list_length )   

lemma matrix_point_not_in_block_zero: "i < \<v> \<Longrightarrow> j < \<b> \<Longrightarrow> \<V>s ! i \<notin> \<B>s ! j \<Longrightarrow> N $$ (i, j) = 0"
  by(metis inc_matrix_point_not_in_block_zero points_list_length blocks_list_length)

lemma matrix_point_in_block: "i < \<v> \<Longrightarrow> j < \<b> \<Longrightarrow> N $$ (i, j) = 1 \<Longrightarrow> \<V>s ! i \<in> \<B>s ! j"
  by (metis blocks_list_length points_list_length  inc_matrix_point_in_block)

lemma matrix_point_not_in_block: "i < \<v> \<Longrightarrow> j < \<b> \<Longrightarrow> N $$ (i, j) = 0 \<Longrightarrow> \<V>s ! i \<notin> \<B>s ! j"
  by (metis blocks_list_length points_list_length inc_matrix_point_not_in_block)

lemma matrix_point_not_in_block_iff: "i < \<v> \<Longrightarrow> j < \<b> \<Longrightarrow> N $$ (i, j) = 0 \<longleftrightarrow> \<V>s ! i \<notin> \<B>s ! j"
  by (metis blocks_list_length points_list_length inc_matrix_point_not_in_block_iff)

lemma matrix_point_in_block_iff: "i < \<v> \<Longrightarrow> j < \<b> \<Longrightarrow> N $$ (i, j) = 1 \<longleftrightarrow> \<V>s ! i \<in> \<B>s ! j"
  by (metis blocks_list_length points_list_length inc_matrix_point_in_block_iff)

lemma matrix_subset_implies_one: "I \<subseteq> {..< \<v>} \<Longrightarrow> j < \<b> \<Longrightarrow> (!) \<V>s ` I \<subseteq> \<B>s ! j \<Longrightarrow> i \<in> I \<Longrightarrow> 
  N $$ (i, j) = 1"
  by (metis blocks_list_length points_list_length inc_matrix_subset_implies_one)

lemma matrix_one_implies_membership: 
"I \<subseteq> {..< \<v>} \<Longrightarrow> j < size \<B> \<Longrightarrow> \<forall>i\<in>I. N $$ (i, j) = 1 \<Longrightarrow> i \<in> I \<Longrightarrow> \<V>s ! i \<in> \<B>s ! j"
  by (simp add: matrix_point_in_block_iff subset_iff)

text \<open>Incidence Vector's of Incidence Matrix columns \<close>

lemma col_inc_vec_of: "j < length \<B>s \<Longrightarrow> inc_vec_of \<V>s (\<B>s ! j) = col N j"
  by (simp add: inc_mat_col_inc_vec) 

lemma inc_vec_eq_iff_blocks: 
  assumes "bl \<in># \<B>"
  assumes "bl' \<in># \<B>"
  shows "inc_vec_of \<V>s bl = inc_vec_of \<V>s bl' \<longleftrightarrow> bl = bl'"
proof (intro iffI eq_vecI, simp_all add: inc_vec_dim assms)
  define v1 :: "'c :: {ring_1} vec" where "v1 = inc_vec_of \<V>s bl"
  define v2 :: "'c :: {ring_1} vec" where "v2 = inc_vec_of \<V>s bl'"
  assume a: "v1 = v2"
  then have "dim_vec v1 = dim_vec v2"
    by (simp add: inc_vec_dim) 
  then have "\<And> i. i < dim_vec v1 \<Longrightarrow> v1 $ i = v2 $ i" using a by simp
  then have "\<And> i. i < length \<V>s \<Longrightarrow> v1 $ i = v2 $ i" by (simp add: v1_def inc_vec_dim)
  then have "\<And> i. i < length \<V>s \<Longrightarrow> (\<V>s ! i)  \<in> bl \<longleftrightarrow> (\<V>s ! i)  \<in> bl'"
    using  inc_vec_index_one_iff v1_def v2_def by metis 
  then have "\<And> x. x \<in> \<V> \<Longrightarrow> x \<in> bl \<longleftrightarrow> x \<in> bl'"
    using points_list_length valid_points_index_cons by auto 
  then show "bl = bl'" using wellformed assms
    by (meson subset_antisym subset_eq)
qed

text \<open>Incidence matrix column properties\<close>

lemma N_col_def: "j < \<b> \<Longrightarrow> i < \<v> \<Longrightarrow> (col N j) $ i = (if (\<V>s ! i \<in> \<B>s ! j) then 1 else 0)"
  by (metis inc_mat_col_def points_list_length blocks_list_length) 

lemma N_col_def_indiv: "j < \<b> \<Longrightarrow> i < \<v> \<Longrightarrow> \<V>s ! i \<in> \<B>s ! j \<Longrightarrow> (col N j) $ i = 1"
     "j < \<b> \<Longrightarrow> i < \<v> \<Longrightarrow> \<V>s ! i \<notin> \<B>s ! j \<Longrightarrow> (col N j) $ i = 0"
  by(simp_all add: inc_matrix_point_in_block_one inc_matrix_point_not_in_block_zero points_list_length)

lemma N_col_list_map_elem: "j < \<b> \<Longrightarrow> i < \<v> \<Longrightarrow> 
    col N j $ i = map_vec (\<lambda> x . if (x \<in> (\<B>s ! j)) then 1 else 0) (vec_of_list \<V>s) $ i"
  by (metis inc_mat_col_list_map_elem points_list_length blocks_list_length) 

lemma N_col_list_map: "j < \<b> \<Longrightarrow> col N j = map_vec (\<lambda> x . if (x \<in> (\<B>s ! j)) then 1 else 0) (vec_of_list \<V>s)"
  by (metis inc_mat_col_list_map blocks_list_length) 

lemma N_col_mset_point_set_img: "j < \<b> \<Longrightarrow> 
    vec_mset (col N j) = image_mset (\<lambda> x. if (x \<in> (\<B>s ! j)) then 1 else 0) (mset_set \<V>)"
  using vec_mset_img_map N_col_list_map points_indexing
  by (metis (no_types, lifting) finite_sets permutations_of_multisetD permutations_of_set_altdef) 

lemma matrix_col_to_block: 
  assumes "j < \<b>"
  shows "\<B>s ! j = (\<lambda> k . \<V>s ! k) ` {i \<in> {..< \<v>} . (col N j) $ i = 1}"
proof (intro subset_antisym subsetI)
  fix x assume assm1: "x \<in> \<B>s ! j"
  then have "x \<in> \<V>" using wellformed assms valid_blocks_index by blast 
  then obtain i where vs: "\<V>s ! i = x" and "i < \<v>"
    using valid_points_index_cons by auto 
  then have inset: "i \<in> {..< \<v>}"
    by fastforce
  then have "col N j $ i = 1" using assm1 N_col_def assms vs
    using \<open>i < \<v>\<close> by presburger 
  then have "i \<in> {i. i \<in> {..< \<v>} \<and> col N j $ i = 1}"
    using inset by blast
  then show "x \<in> (!) \<V>s ` {i.  i \<in> {..<\<v>} \<and> col N j $ i = 1}" using vs by blast
next
  fix x assume assm2: "x \<in> ((\<lambda> k . \<V>s ! k) ` {i \<in> {..< \<v>} . col N j $ i = 1})"
  then obtain k where "x = \<V>s !k" and inner: "k \<in>{i \<in> {..< \<v>} . col N j $ i = 1}"
    by blast 
  then have ilt: "k < \<v>" by auto
  then have "N $$ (k, j) = 1" using inner
    by (metis (mono_tags) N_col_def assms matrix_point_in_block_iff matrix_point_not_in_block_zero mem_Collect_eq) 
  then show "x \<in> \<B>s ! j" using ilt
    using \<open>x = \<V>s ! k\<close> assms matrix_point_in_block_iff by blast
qed

lemma matrix_col_to_block_v2: "j < \<b> \<Longrightarrow> \<B>s ! j = (\<lambda> k . \<V>s ! k) ` map_col_to_block (col N j)"
  using matrix_col_to_block map_col_to_block_def by fastforce

lemma matrix_col_in_blocks: "j < \<b> \<Longrightarrow> (!) \<V>s ` map_col_to_block (col N j) \<in># \<B>"
  using matrix_col_to_block_v2 by (metis (no_types, lifting) valid_blocks_index) 

lemma inc_matrix_col_block: 
  assumes "c \<in> set (cols N)"
  shows "(\<lambda> x. \<V>s ! x) ` (map_col_to_block c) \<in># \<B>"
proof -
  obtain j where "c = col N j" and "j < \<b>" using assms cols_length cols_nth in_mset_conv_nth 
    ordered_incidence_system_axioms set_mset_mset by (metis dim_col_is_b)  
  thus ?thesis
    using matrix_col_in_blocks by blast 
qed

text \<open> Incidence Matrix Row Definitions \<close>
lemma N_row_def: "j < \<b> \<Longrightarrow> i < \<v> \<Longrightarrow> (row N i) $ j = (if (\<V>s ! i \<in> \<B>s ! j) then 1 else 0)"
  by (metis inc_mat_row_def points_list_length blocks_list_length) 

lemma N_row_list_map_elem: "j < \<b> \<Longrightarrow> i < \<v> \<Longrightarrow> 
    row N i $ j = map_vec (\<lambda> bl . if ((\<V>s ! i) \<in> bl) then 1 else 0) (vec_of_list \<B>s) $ j"
  by (metis inc_mat_row_list_map_elem points_list_length blocks_list_length) 

lemma N_row_list_map: "i < \<v> \<Longrightarrow> 
    row N i = map_vec (\<lambda> bl . if ((\<V>s ! i) \<in> bl) then 1 else 0) (vec_of_list \<B>s)"
  by (simp add: inc_mat_row_list_map points_list_length blocks_list_length) 

lemma N_row_mset_blocks_img: "i < \<v> \<Longrightarrow> 
    vec_mset (row N i) = image_mset (\<lambda> x . if ((\<V>s ! i) \<in> x) then 1 else 0) \<B>"
  using vec_mset_img_map N_row_list_map by metis

text \<open>Alternate Block representations \<close>

lemma block_mat_cond_rep:
  assumes "j < length \<B>s"
  shows "(\<B>s ! j) = {\<V>s ! i | i. i < length \<V>s \<and> N $$ (i, j) = 1}"
proof -
  have cond: "\<And> i. i < length \<V>s \<and> N $$ (i, j) = 1 \<longleftrightarrow>i \<in> {..< \<v>} \<and> (col N j) $ i = 1"
    using assms points_list_length by auto
  have "(\<B>s ! j) = (\<lambda> k . \<V>s ! k) ` {i \<in> {..< \<v>} . (col N j) $ i = 1}" 
    using matrix_col_to_block assms by simp
  also have "... = {\<V>s ! i | i. i \<in> {..< \<v>} \<and> (col N j) $ i = 1}" by auto
  finally show "(\<B>s ! j) = {\<V>s ! i | i. i < length \<V>s \<and> N $$ (i, j) = 1}"
    using Collect_cong cond by auto
qed

lemma block_mat_cond_rep': "j < length \<B>s \<Longrightarrow> (\<B>s ! j) = ((!) \<V>s) ` {i . i < length \<V>s \<and> N $$ (i, j) = 1}"
  by (simp add: block_mat_cond_rep setcompr_eq_image)

lemma block_mat_cond_rev: 
  assumes "j < length \<B>s"
  shows "{i . i < length \<V>s \<and> N $$ (i, j) = 1} = ((List_Index.index) \<V>s) ` (\<B>s ! j)"
proof (intro Set.set_eqI iffI)
  fix i assume a1: "i \<in> {i. i < length \<V>s \<and> N $$ (i, j) = 1}"
  then have ilt1: "i < length \<V>s" and Ni1: "N $$ (i, j) = 1" by auto
  then obtain x where "\<V>s ! i = x" and "x \<in> (\<B>s ! j)"
    using assms inc_matrix_point_in_block by blast  
  then have "List_Index.index \<V>s x = i" using distinct  index_nth_id ilt1 by auto
  then show "i \<in> List_Index.index \<V>s ` \<B>s ! j" by (metis \<open>x \<in> \<B>s ! j\<close> imageI) 
next
  fix i assume a2: "i \<in> List_Index.index \<V>s ` \<B>s ! j"
  then obtain x where ieq: "i = List_Index.index \<V>s x" and xin: "x \<in> \<B>s !j"
    by blast 
  then have ilt: "i < length \<V>s"
    by (smt (z3) assms index_first index_le_size nat_less_le nth_mem_mset points_list_length 
        valid_points_index_cons wf_invalid_point)
  then have "N $$ (i, j) = 1" using xin inc_matrix_point_in_block_one
    by (metis ieq assms index_conv_size_if_notin less_irrefl_nat nth_index)
  then show "i \<in> {i. i < length \<V>s \<and> N $$ (i, j) = 1}" using ilt by simp
qed

text \<open>Incidence Matrix incidence system properties \<close>
lemma incomplete_block_col:
  assumes "j < \<b>"
  assumes "incomplete_block (\<B>s ! j)"
  shows "0 \<in>$ (col N j)" 
proof -
  obtain x where "x \<in> \<V>" and "x \<notin> (\<B>s ! j)"
    by (metis Diff_iff assms(2) incomplete_block_proper_subset psubset_imp_ex_mem)
  then obtain i where "\<V>s ! i = x" and "i< \<v>" 
    using valid_points_index_cons by blast 
  then have "N $$ (i, j) = 0"
    using \<open>x \<notin> \<B>s ! j\<close> assms(1) matrix_point_not_in_block_zero by blast 
  then have "col N j $ i = 0"
    using N_col_def \<open>\<V>s ! i = x\<close> \<open>i < \<v>\<close> \<open>x \<notin> \<B>s ! j\<close> assms(1) by fastforce 
  thus ?thesis using vec_setI
    by (smt (z3) \<open>i < \<v>\<close> dim_col dim_row_is_v)
qed

lemma mat_rep_num_N_row: 
  assumes "i < \<v>"
  shows "mat_rep_num N i = \<B> rep (\<V>s ! i)"
proof -
  have "count (image_mset (\<lambda> x . if ((\<V>s ! i) \<in> x) then 1 else (0 :: int )) \<B>) 1 = 
    size (filter_mset (\<lambda> x . (\<V>s ! i) \<in> x) \<B>)"
    using count_mset_split_image_filter[of "\<B>" "1" "\<lambda> x . (0 :: int)" "\<lambda> x . (\<V>s ! i) \<in> x"] by simp
  then have "count (image_mset (\<lambda> x . if ((\<V>s ! i) \<in> x) then 1 else (0 :: int )) \<B>) 1
    = \<B> rep (\<V>s ! i)" by (simp add: point_rep_number_alt_def)
  thus ?thesis using N_row_mset_blocks_img assms
    by (simp add: mat_rep_num_def) 
qed

lemma point_rep_mat_row_sum:  "i < \<v> \<Longrightarrow> sum_vec (row N i) = \<B> rep (\<V>s ! i)"
  using count_vec_sum_ones_alt mat_rep_num_N_row mat_row_elems mat_rep_num_def by metis 

lemma mat_block_size_N_col: 
  assumes "j < \<b>"
  shows "mat_block_size N j = card (\<B>s ! j)"
proof -
  have val_b: "\<B>s ! j \<in># \<B>" using assms valid_blocks_index by auto 
  have "\<And> x. x \<in># mset_set \<V> \<Longrightarrow> (\<lambda>x . (0 :: int)) x \<noteq> 1" using zero_neq_one by simp
  then have "count (image_mset (\<lambda> x. if (x \<in> (\<B>s ! j)) then 1 else (0 :: int)) (mset_set \<V>)) 1 = 
    size (filter_mset (\<lambda> x . x \<in> (\<B>s ! j)) (mset_set \<V>))"
    using count_mset_split_image_filter [of "mset_set \<V>" "1" "(\<lambda> x . (0 :: int))" "\<lambda> x . x \<in> \<B>s ! j"] 
    by simp
  then have "count (image_mset (\<lambda> x. if (x \<in> (\<B>s ! j)) then 1 else (0 :: int)) (mset_set \<V>)) 1 = card (\<B>s ! j)"
    using val_b block_size_alt by (simp add: finite_sets)
  thus ?thesis using N_col_mset_point_set_img assms mat_block_size_def by metis 
qed

lemma block_size_mat_rep_sum: "j < \<b> \<Longrightarrow> sum_vec (col N j) = mat_block_size N j"
  using count_vec_sum_ones_alt mat_block_size_N_col mat_block_size_def by (metis mat_col_elems) 

lemma mat_point_index_rep:
  assumes "I \<subseteq> {..<\<v>}"
  shows "mat_point_index N I = \<B> index ((\<lambda> i. \<V>s ! i) ` I)"
proof - 
  have "\<And> i . i \<in> I \<Longrightarrow> \<V>s ! i \<in> \<V>" using assms valid_points_index by auto 
  then have eqP: "\<And> j. j < dim_col N \<Longrightarrow> ((\<lambda> i. \<V>s ! i) ` I) \<subseteq> (\<B>s ! j) \<longleftrightarrow> (\<forall> i \<in> I . N $$ (i, j) = 1)"
  proof (intro iffI subsetI, simp_all)
    show "\<And>j i. j < length \<B>s \<Longrightarrow> (\<And>i. i \<in> I \<Longrightarrow> \<V>s ! i \<in> \<V>) \<Longrightarrow> (!) \<V>s ` I \<subseteq> \<B>s ! j \<Longrightarrow> 
        \<forall>i\<in>I. N $$ (i, j) = 1"
      using matrix_subset_implies_one assms by simp
    have "\<And>x.  x\<in> (!) \<V>s ` I \<Longrightarrow> \<exists> i \<in> I. \<V>s ! i = x"
      by auto 
    then show "\<And>j x. j < length \<B>s \<Longrightarrow> \<forall>i\<in>I. N $$ (i, j) = 1 \<Longrightarrow> x \<in> (!) \<V>s ` I 
        \<Longrightarrow> (\<And>i. i \<in> I \<Longrightarrow> \<V>s ! i \<in> \<V>) \<Longrightarrow> x \<in> \<B>s ! j"
      using assms matrix_one_implies_membership by (metis blocks_list_length) 
  qed
  have "card {j . j < dim_col N \<and> (\<forall> i \<in> I . N $$(i, j) = 1)} = 
      card {j . j < dim_col N \<and> ((\<lambda> i . \<V>s ! i) ` I) \<subseteq> \<B>s ! j}"
    using eqP by (metis (mono_tags, lifting))
  also have "... = size {# b \<in># \<B> . ((\<lambda> i . \<V>s ! i) ` I) \<subseteq> b #}"
    using filter_size_blocks_eq_card_indexes by auto
  also have "... = points_index \<B> ((\<lambda> i . \<V>s ! i) ` I)"
    by (simp add: points_index_def)
  finally have "card {j . j < dim_col N \<and> (\<forall> i \<in> I . N $$(i, j) = 1)} = \<B> index ((\<lambda> i . \<V>s ! i) ` I)"
    by blast
  thus ?thesis unfolding mat_point_index_def by simp
qed

lemma incidence_mat_two_index: "i1 < \<v> \<Longrightarrow> i2 < \<v> \<Longrightarrow> 
    mat_point_index N {i1, i2} = \<B> index {\<V>s ! i1, \<V>s ! i2}"
  using mat_point_index_two_alt[of  i1 N i2 ] mat_point_index_rep[of "{i1, i2}"] dim_row_is_v
  by (metis (no_types, lifting) empty_subsetI image_empty image_insert insert_subset lessThan_iff) 

lemma ones_incidence_mat_block_size: 
  assumes "j < \<b>"
  shows "((u\<^sub>v \<v>) \<^sub>v* N) $ j = mat_block_size N j"
proof - 
  have "dim_vec ((u\<^sub>v \<v>) \<^sub>v* N) = \<b>" by (simp) 
  then have "((u\<^sub>v \<v>) \<^sub>v* N) $ j = (u\<^sub>v \<v>) \<bullet> col N j" using assms by simp 
  also have "... = (\<Sum> i \<in> {0 ..< \<v>}. (u\<^sub>v \<v>) $ i * (col N j) $ i)" 
    by (simp add: scalar_prod_def)
  also have "... = sum_vec (col N j)" using dim_row_is_v by (simp add: sum_vec_def)
  finally show ?thesis  using block_size_mat_rep_sum assms by simp
qed

lemma mat_block_size_conv:  "j < dim_col N \<Longrightarrow> card (\<B>s ! j) = mat_block_size N j"
  by (simp add: mat_block_size_N_col)

lemma mat_inter_num_conv: 
  assumes "j1 < dim_col N" "j2 < dim_col N"
  shows "(\<B>s ! j1) |\<inter>| (\<B>s ! j2) = mat_inter_num N j1 j2"
proof -
  have eq_sets: "\<And> P. (\<lambda> i . \<V>s ! i) ` {i \<in> {0..<\<v>}. P (\<V>s ! i)} = {x \<in> \<V> . P x}"
    by (metis Compr_image_eq lessThan_atLeast0 points_set_index_img)
  have bin: "\<B>s ! j1 \<in># \<B>" "\<B>s ! j2 \<in># \<B>" using assms dim_col_is_b by simp_all
  have "(\<B>s ! j1) |\<inter>| (\<B>s ! j2) = card ((\<B>s ! j1) \<inter> (\<B>s ! j2))" 
    by (simp add: intersection_number_def)
  also have "... = card {x . x \<in> (\<B>s ! j1) \<and> x \<in> (\<B>s ! j2)}"
    by (simp add: Int_def) 
  also have "... = card {x \<in> \<V>. x \<in> (\<B>s ! j1) \<and> x \<in> (\<B>s ! j2)}" using wellformed bin
    by (meson wf_invalid_point) 
  also have "... = card ((\<lambda> i . \<V>s ! i) ` {i \<in> {0..<\<v>}. (\<V>s ! i) \<in> (\<B>s ! j1) \<and> (\<V>s ! i) \<in> (\<B>s ! j2)})" 
    using eq_sets[of "\<lambda> x. x \<in> (\<B>s ! j1) \<and> x \<in> (\<B>s ! j2)"] by simp
  also have "... = card ({i \<in> {0..<\<v>}. (\<V>s ! i) \<in> (\<B>s ! j1) \<and> (\<V>s ! i) \<in> (\<B>s ! j2)})"
    using points_indexing_inj card_image
    by (metis (no_types, lifting) lessThan_atLeast0 lessThan_iff mem_Collect_eq points_list_length) 
  also have "... = card ({i . i < \<v> \<and> (\<V>s ! i) \<in> (\<B>s ! j1) \<and> (\<V>s ! i) \<in> (\<B>s ! j2)})" by auto
  also have "... = card ({i . i < \<v> \<and> N $$ (i, j1) = 1 \<and> N $$ (i, j2) = 1})" using assms
    by (metis (no_types, opaque_lifting) inc_mat_dim_col inc_matrix_point_in_block_iff points_list_length) 
  finally have "(\<B>s ! j1) |\<inter>| (\<B>s ! j2) = card {i . i < dim_row N \<and> N $$ (i, j1) = 1 \<and> N $$ (i, j2) = 1}"
    using dim_row_is_v by presburger
  thus ?thesis using assms by (simp add: mat_inter_num_def)
qed

lemma non_empty_col_map_conv: 
  assumes "j < dim_col N"
  shows "non_empty_col N j \<longleftrightarrow> \<B>s ! j \<noteq> {}"
proof (intro iffI)
  assume "non_empty_col N j"
  then obtain i where ilt: "i < dim_row N" and "(col N j) $ i \<noteq> 0"
    using non_empty_col_obtains assms by blast
  then have "(col N j) $ i = 1"
    using assms
    by (metis N_col_def_indiv(1) N_col_def_indiv(2) dim_col_is_b dim_row_is_v) 
  then have "\<V>s ! i \<in> \<B>s ! j"
    by (smt (verit, best) assms ilt inc_mat_col_def dim_col_is_b inc_mat_dim_col inc_mat_dim_row) 
  thus "\<B>s ! j \<noteq> {}" by blast
next
  assume a: "\<B>s ! j \<noteq> {}"
  have "\<B>s ! j \<in># \<B>" using assms dim_col_is_b by simp
  then obtain x where "x \<in> \<B>s ! j" and "x \<in> \<V>" using wellformed a by auto
  then obtain i where "\<V>s ! i \<in> \<B>s ! j" and "i < dim_row N" using dim_row_is_v
    using valid_points_index_cons by auto 
  then have "N $$ (i, j) = 1"
    using assms by (meson inc_mat_of_index)  
  then show "non_empty_col N j" using non_empty_col_alt_def
    using \<open>i < dim_row N\<close> assms by fastforce 
qed

lemma scalar_prod_inc_vec_inter_num: 
  assumes "j1 < \<b>" "j2 < \<b>"
  shows "(col N j1) \<bullet> (col N j2) = (\<B>s ! j1) |\<inter>| (\<B>s ! j2)"
  using scalar_prod_inc_vec_mat_inter_num assms N_carrier_mat
  by (simp add: mat_inter_num_conv)

lemma scalar_prod_block_size_lift_01: 
  assumes "i < \<b>"
  shows "((col (lift_01_mat N) i) \<bullet> (col (lift_01_mat N) i)) = (of_nat (card (\<B>s ! i)) :: ('b :: {ring_1}))"
proof -
  interpret z1: zero_one_matrix_ring_1 "(lift_01_mat N)"
    by (intro_locales) (simp add: lift_mat_is_0_1)
  show ?thesis using assms z1.scalar_prod_inc_vec_block_size_mat preserve_mat_block_size 
      mat_block_size_N_col lift_01_mat_def
    by (metis inc_mat_dim_col lift_01_mat_simp(2) of_inj_on_01_hom.inj_on_01_hom_axioms size_mset)
qed

lemma scalar_prod_inter_num_lift_01: 
  assumes "j1 < \<b>" "j2 < \<b>"
  shows "((col (lift_01_mat N) j1) \<bullet> (col (lift_01_mat N) j2)) = (of_nat ((\<B>s ! j1) |\<inter>| (\<B>s ! j2)) :: ('b :: {ring_1}))"
proof -
  interpret z1: zero_one_matrix_ring_1 "(lift_01_mat N)"
    by (intro_locales) (simp add: lift_mat_is_0_1)
  show ?thesis using assms z1.scalar_prod_inc_vec_mat_inter_num preserve_mat_inter_num 
    mat_inter_num_conv lift_01_mat_def blocks_list_length inc_mat_dim_col
    by (metis  lift_01_mat_simp(2) of_inj_on_01_hom.inj_on_01_hom_axioms)
qed

text \<open> The System complement's incidence matrix flips 0's and 1's \<close>

lemma map_block_complement_entry: "j < \<b> \<Longrightarrow> (map block_complement \<B>s) ! j = block_complement (\<B>s ! j)"
  using blocks_list_length by (metis nth_map) 

lemma complement_mat_entries: 
  assumes "i < \<v>" and "j < \<b>"
  shows "(\<V>s ! i \<notin> \<B>s ! j) \<longleftrightarrow> (\<V>s ! i \<in> (map block_complement \<B>s) ! j)"
  using assms block_complement_def map_block_complement_entry valid_points_index by simp

lemma length_blocks_complement: "length (map block_complement \<B>s) = \<b>"
  by auto 

lemma ordered_complement: "ordered_incidence_system \<V>s (map block_complement \<B>s)"
proof -
  interpret inc: finite_incidence_system \<V> "complement_blocks"
    by (simp add: complement_finite)
  have "map inc.block_complement \<B>s \<in> permutations_of_multiset complement_blocks"
    using complement_image by (simp add: permutations_of_multiset_def)
  then show ?thesis using ordered_incidence_sysI[of "\<V>" "complement_blocks" "\<V>s" "(map block_complement \<B>s)"]
    by (simp add: inc.finite_incidence_system_axioms points_indexing) 
qed

interpretation ordered_comp: ordered_incidence_system "\<V>s" "(map block_complement \<B>s)"
  using ordered_complement by simp

lemma complement_mat_entries_val: 
  assumes "i < \<v>" and "j < \<b>"
  shows "ordered_comp.N $$ (i, j) = (if \<V>s ! i \<in> \<B>s ! j then 0 else 1)"
proof -
  have cond: "(\<V>s ! i \<notin> \<B>s ! j) \<longleftrightarrow> (\<V>s ! i \<in> (map block_complement \<B>s) ! j)"
    using complement_mat_entries assms by simp
  then have "ordered_comp.N $$ (i, j) = (if (\<V>s ! i \<in> (map block_complement \<B>s) ! j) then 1 else 0)"
    using assms ordered_comp.matrix_point_in_block_one ordered_comp.matrix_point_not_in_block_iff 
    by force 
  then show ?thesis using cond by simp
qed

lemma ordered_complement_mat: "ordered_comp.N = mat \<v> \<b> (\<lambda> (i,j) . if (\<V>s ! i) \<in> (\<B>s ! j) then 0 else 1)"
  using complement_mat_entries_val by (intro eq_matI, simp_all)

lemma ordered_complement_mat_map: "ordered_comp.N = map_mat (\<lambda>x. if x = 1 then 0 else 1) N"
  apply (intro eq_matI, simp_all)
  using ordered_incidence_system.matrix_point_in_block_iff ordered_incidence_system_axioms 
    complement_mat_entries_val by (metis blocks_list_length) 


end

text \<open>Establishing connection between incidence system and ordered incidence system locale \<close>

lemma (in incidence_system) alt_ordering_sysI: "Vs \<in> permutations_of_set \<V> \<Longrightarrow> Bs \<in> permutations_of_multiset \<B> \<Longrightarrow> 
    ordered_incidence_system Vs Bs"
  by (unfold_locales) (simp_all add: permutations_of_multisetD permutations_of_setD wellformed)

lemma (in finite_incidence_system) exists_ordering_sysI: "\<exists> Vs Bs . Vs \<in> permutations_of_set \<V> \<and> 
  Bs \<in> permutations_of_multiset \<B> \<and> ordered_incidence_system Vs Bs"
proof -
  obtain Vs where "Vs \<in> permutations_of_set \<V>"
    by (meson all_not_in_conv finite_sets permutations_of_set_empty_iff) 
  obtain Bs where "Bs \<in> permutations_of_multiset \<B>"
    by (meson all_not_in_conv permutations_of_multiset_not_empty) 
  then show ?thesis using alt_ordering_sysI \<open>Vs \<in> permutations_of_set \<V>\<close> by blast 
qed

lemma inc_sys_orderedI: 
  assumes "incidence_system V B" and "distinct Vs" and "set Vs = V" and "mset Bs = B" 
  shows "ordered_incidence_system Vs Bs"
proof -
  interpret inc: incidence_system V B using assms by simp
  show ?thesis proof (unfold_locales)
    show "\<And>b. b \<in># mset Bs \<Longrightarrow> b \<subseteq> set Vs" using inc.wellformed assms by simp
    show "distinct Vs" using assms(2)permutations_of_setD(2) by auto 
  qed
qed

text \<open>Generalise the idea of an incidence matrix to an unordered context \<close>

definition is_incidence_matrix :: "'c :: {ring_1} mat \<Rightarrow> 'a set \<Rightarrow> 'a set multiset \<Rightarrow> bool" where
"is_incidence_matrix N V B \<longleftrightarrow> 
  (\<exists> Vs Bs . (Vs \<in> permutations_of_set V \<and> Bs \<in> permutations_of_multiset B \<and> N = (inc_mat_of Vs Bs)))"

lemma (in incidence_system) is_incidence_mat_alt: "is_incidence_matrix N \<V> \<B> \<longleftrightarrow> 
  (\<exists> Vs Bs. (set Vs = \<V> \<and> mset Bs = \<B> \<and> ordered_incidence_system Vs Bs \<and> N = (inc_mat_of Vs Bs)))"
proof (intro iffI, simp add: is_incidence_matrix_def)
  assume "\<exists>Vs. Vs \<in> permutations_of_set \<V> \<and> (\<exists>Bs. Bs \<in> permutations_of_multiset \<B> \<and> N = inc_mat_of Vs Bs)"
  then obtain Vs Bs where "Vs \<in> permutations_of_set \<V> \<and> Bs \<in> permutations_of_multiset \<B> \<and> N = inc_mat_of Vs Bs"
    by auto
  then show "\<exists>Vs. set Vs = \<V> \<and> (\<exists>Bs. mset Bs = \<B> \<and> ordered_incidence_system Vs Bs \<and> N = inc_mat_of Vs Bs)"
    using incidence_system.alt_ordering_sysI incidence_system_axioms permutations_of_multisetD permutations_of_setD(1) 
    by blast 
next
  assume "\<exists>Vs Bs. set Vs = \<V> \<and> mset Bs = \<B> \<and> ordered_incidence_system Vs Bs \<and> N = inc_mat_of Vs Bs"
  then obtain Vs Bs where s: "set Vs = \<V>" and ms: "mset Bs = \<B>" and "ordered_incidence_system Vs Bs" 
    and n: "N = inc_mat_of Vs Bs" by auto 
  then interpret ois: ordered_incidence_system Vs Bs by simp 
  have vs: "Vs \<in> permutations_of_set \<V>"
    using ois.points_indexing s by blast 
  have "Bs \<in> permutations_of_multiset \<B>" using ois.blocks_indexing ms by blast
  then show "is_incidence_matrix N \<V> \<B> " using n vs
    using is_incidence_matrix_def by blast 
qed

lemma (in ordered_incidence_system) is_incidence_mat_true: "is_incidence_matrix N \<V> \<B> = True"
  using blocks_indexing is_incidence_matrix_def points_indexing by blast

subsection\<open>Incidence Matrices on Design Subtypes \<close>

locale ordered_design = ordered_incidence_system \<V>s \<B>s + design "set \<V>s" "mset \<B>s" 
  for \<V>s and \<B>s
begin

lemma incidence_mat_non_empty_blocks: 
  assumes "j < \<b>"
  shows "1 \<in>$ (col N j)" 
proof -
  obtain bl where isbl: "\<B>s ! j = bl" by simp
  then have "bl \<in># \<B>"
    using assms valid_blocks_index by auto 
  then obtain x where inbl: "x \<in> bl"
    using blocks_nempty by blast
  then obtain i where isx: "\<V>s ! i = x" and vali: "i < \<v>"
    using \<open>bl \<in># \<B>\<close> valid_points_index_cons wf_invalid_point by blast
  then have "N $$ (i, j) = 1"
    using \<open>\<B>s ! j = bl\<close> \<open>x \<in> bl\<close> assms matrix_point_in_block_one by blast
  thus ?thesis using vec_setI
    by (smt (verit, ccfv_SIG) N_col_def isx vali isbl inbl assms dim_vec_col_N of_nat_less_imp_less) 
qed

lemma all_cols_non_empty: "j < dim_col N \<Longrightarrow> non_empty_col N j"
  using blocks_nempty non_empty_col_map_conv dim_col_is_b by simp 
end

locale ordered_simple_design = ordered_design \<V>s \<B>s + simple_design "(set \<V>s)" "mset \<B>s" for \<V>s \<B>s
begin

lemma block_list_distinct: "distinct \<B>s"
  using block_mset_distinct by auto
  
lemma distinct_cols_N: "distinct (cols N)"
proof -
  have "inj_on (\<lambda> bl . inc_vec_of \<V>s bl) (set \<B>s)" using inc_vec_eq_iff_blocks 
    by (simp add: inc_vec_eq_iff_blocks inj_on_def) 
  then show ?thesis using distinct_map inc_mat_of_cols_inc_vecs block_list_distinct
    by (simp add: distinct_map inc_mat_of_cols_inc_vecs ) 
qed

lemma simp_blocks_length_card: "length \<B>s = card (set \<B>s)"
  using design_support_def simple_block_size_eq_card by fastforce

lemma blocks_index_inj_on: "inj_on (\<lambda> i . \<B>s ! i) {0..<length \<B>s}"
  by (auto simp add: inj_on_def) (metis simp_blocks_length_card card_distinct nth_eq_iff_index_eq)

lemma x_in_block_set_img: assumes "x \<in> set \<B>s" shows "x \<in> (!) \<B>s ` {0..<length \<B>s}"
proof -
  obtain i where "\<B>s ! i = x" and "i < length \<B>s" using assms
    by (meson in_set_conv_nth) 
  thus ?thesis by auto
qed

lemma blocks_index_simp_bij_betw: "bij_betw (\<lambda> i . \<B>s ! i) {0..<length \<B>s} (set \<B>s)"
  using blocks_index_inj_on x_in_block_set_img by (auto simp add: bij_betw_def) 

lemma blocks_index_simp_unique:  "i1 < length \<B>s \<Longrightarrow> i2 < length \<B>s \<Longrightarrow> i1 \<noteq> i2 \<Longrightarrow> \<B>s ! i1 \<noteq> \<B>s ! i2"
  using block_list_distinct nth_eq_iff_index_eq by blast 

lemma lift_01_distinct_cols_N: "distinct (cols (lift_01_mat N))"
  using  lift_01_mat_distinct_cols distinct_cols_N by simp

end

locale ordered_proper_design = ordered_design \<V>s \<B>s + proper_design "set \<V>s" "mset \<B>s" 
  for \<V>s and \<B>s
begin

lemma mat_is_proper: "proper_inc_mat N"
  using design_blocks_nempty v_non_zero 
  by (auto simp add: proper_inc_mat_def)

end

locale ordered_constant_rep = ordered_proper_design \<V>s \<B>s + constant_rep_design "set \<V>s" "mset \<B>s" \<r> 
  for \<V>s and \<B>s and \<r>

begin

lemma incidence_mat_rep_num: "i < \<v> \<Longrightarrow> mat_rep_num N i = \<r>"
  using mat_rep_num_N_row rep_number valid_points_index by simp 

lemma incidence_mat_rep_num_sum: "i < \<v> \<Longrightarrow> sum_vec (row N i) = \<r>"
  using incidence_mat_rep_num  mat_rep_num_N_row
  by (simp add: point_rep_mat_row_sum)  

lemma transpose_N_mult_diag: 
  assumes "i = j" and "i < \<v>" and "j < \<v>" 
  shows "(N * N\<^sup>T) $$ (i, j) = \<r>"
proof -
  have unsq: "\<And> k . k < \<b> \<Longrightarrow> (N $$ (i, k))^2 = N $$ (i, k)"
    using assms(2) matrix_elems_one_zero by fastforce
  then have "(N * N\<^sup>T) $$ (i, j) = (\<Sum>k \<in>{0..<\<b>} . N $$ (i, k) * N $$ (j, k))"
    using assms(2) assms(3) transpose_mat_mult_entries[of "i" "N" "j"] by (simp) 
  also have "... = (\<Sum>k \<in>{0..<\<b>} . (N $$ (i, k))^2)" using assms(1)
    by (simp add: power2_eq_square)
  also have "... = (\<Sum>k \<in>{0..<\<b>} . N $$ (i, k))"
    by (meson atLeastLessThan_iff sum.cong unsq) 
  also have "... = (\<Sum>k \<in>{0..<\<b>} . (row N i) $ k)"
    using assms(2) dim_col_is_b dim_row_is_v by auto 
  finally have "(N * N\<^sup>T) $$ (i, j) = sum_vec (row N i)"
    by (simp add: sum_vec_def)
  thus ?thesis using incidence_mat_rep_num_sum
    using assms(2) by presburger 
qed

end

locale ordered_block_design = ordered_proper_design \<V>s \<B>s + block_design "set \<V>s" "mset \<B>s" \<k>
  for \<V>s and \<B>s and \<k>

begin 

(* Every col has k ones *)
lemma incidence_mat_block_size: "j < \<b> \<Longrightarrow> mat_block_size N j = \<k>"
  using mat_block_size_N_col uniform valid_blocks_index by fastforce

lemma incidence_mat_block_size_sum: "j < \<b> \<Longrightarrow> sum_vec (col N j) = \<k>"
  using incidence_mat_block_size block_size_mat_rep_sum by presburger 

lemma ones_mult_incidence_mat_k_index: "j < \<b> \<Longrightarrow> ((u\<^sub>v \<v>) \<^sub>v* N) $ j = \<k>"
  using ones_incidence_mat_block_size uniform incidence_mat_block_size by blast 

lemma ones_mult_incidence_mat_k: "((u\<^sub>v \<v>) \<^sub>v* N) = \<k> \<cdot>\<^sub>v (u\<^sub>v \<b>)"
  using ones_mult_incidence_mat_k_index dim_col_is_b by (intro eq_vecI) (simp_all)

end

locale ordered_incomplete_design = ordered_block_design \<V>s \<B>s \<k> + incomplete_design \<V> \<B> \<k>
  for \<V>s and \<B>s and \<k>

begin 

lemma incidence_mat_incomplete:  "j < \<b> \<Longrightarrow> 0 \<in>$ (col N j)"
  using valid_blocks_index incomplete_block_col incomplete_imp_incomp_block by blast 

end

locale ordered_t_wise_balance = ordered_proper_design \<V>s \<B>s + t_wise_balance "set \<V>s" "mset \<B>s" \<t> \<Lambda>\<^sub>t
  for \<V>s and \<B>s and \<t> and \<Lambda>\<^sub>t

begin

lemma incidence_mat_des_index: 
  assumes "I \<subseteq> {0..<\<v>}"
  assumes "card I = \<t>"
  shows "mat_point_index N I = \<Lambda>\<^sub>t"
proof -
  have card: "card ((!) \<V>s ` I) = \<t>" using assms points_indexing_inj
    by (metis (mono_tags, lifting) card_image ex_nat_less_eq not_le points_list_length subset_iff) 
  have "((!) \<V>s ` I) \<subseteq> \<V>" using assms
    by (metis atLeastLessThan_iff image_subset_iff subsetD valid_points_index)
  then have "\<B> index ((!) \<V>s ` I) = \<Lambda>\<^sub>t" using balanced assms(2) card by simp
  thus ?thesis using mat_point_index_rep assms(1) lessThan_atLeast0 by presburger 
qed

end

locale ordered_pairwise_balance = ordered_t_wise_balance \<V>s \<B>s 2 \<Lambda> + pairwise_balance "set \<V>s" "mset \<B>s" \<Lambda>
  for \<V>s and \<B>s and \<Lambda>
begin

lemma incidence_mat_des_two_index: 
  assumes "i1 < \<v>"
  assumes "i2 < \<v>"
  assumes "i1 \<noteq> i2"
  shows "mat_point_index N {i1, i2} = \<Lambda>"
  using incidence_mat_des_index incidence_mat_two_index 
proof -
  have "\<V>s ! i1 \<noteq> \<V>s ! i2" using assms(3)
    by (simp add: assms(1) assms(2) distinct nth_eq_iff_index_eq points_list_length) 
  then have pair: "card {\<V>s ! i1, \<V>s ! i2} = 2" using card_2_iff by blast
  have "{\<V>s ! i1, \<V>s ! i2} \<subseteq> \<V>" using assms
    by (simp add: valid_points_index) 
  then have "\<B> index {\<V>s ! i1, \<V>s ! i2} = \<Lambda>" using pair
    using balanced by blast 
  thus ?thesis using incidence_mat_two_index assms by simp
qed

lemma transpose_N_mult_off_diag: 
  assumes "i \<noteq> j" and "i < \<v>" and "j < \<v>"
  shows "(N * N\<^sup>T) $$ (i, j) = \<Lambda>"
proof -
  have rev: "\<And> k. k \<in> {0..<\<b>} \<Longrightarrow> \<not> (N $$ (i, k) = 1 \<and> N $$ (j, k) = 1) \<longleftrightarrow> N $$ (i, k) = 0 \<or> N $$ (j, k) = 0"
    using assms matrix_elems_one_zero by auto
  then have split: "{0..<\<b>} = {k \<in> {0..<\<b>}. N $$ (i, k) = 1 \<and> N $$ (j, k) = 1} \<union> 
      {k \<in> {0..<\<b>}. N $$ (i, k) = 0 \<or> N $$ (j, k) = 0}"
    by blast
  have zero: "\<And> k . k \<in> {0..<\<b>} \<Longrightarrow> N $$ (i, k) = 0 \<or> N $$ (j, k) = 0 \<Longrightarrow> N $$ (i, k) * N$$ (j, k) = 0"
    by simp 
  have djnt: "{k \<in> {0..<\<b>}. N $$ (i, k) = 1 \<and> N $$ (j, k) = 1} \<inter> 
    {k \<in> {0..<\<b>}. N $$ (i, k) = 0 \<or> N $$ (j, k) = 0} = {}" using rev by auto
  have fin1: "finite {k \<in> {0..<\<b>}. N $$ (i, k) = 1 \<and> N $$ (j, k) = 1}" by simp
  have fin2: "finite {k \<in> {0..<\<b>}. N $$ (i, k) = 0 \<or> N $$ (j, k) = 0}" by simp
  have "(N * N\<^sup>T) $$ (i, j) = (\<Sum>k \<in>{0..<\<b>} . N $$ (i, k) * N $$ (j, k))"
    using assms(2) assms(3) transpose_mat_mult_entries[of "i" "N" "j"] by (simp)
  also have "... = (\<Sum>k \<in>({k' \<in> {0..<\<b>}. N $$ (i, k') = 1 \<and> N $$ (j, k') = 1} \<union> 
    {k' \<in> {0..<\<b>}. N $$ (i, k') = 0 \<or> N $$ (j, k') = 0}) . N $$ (i, k) * N $$ (j, k))"
    using split by metis
  also have "... = (\<Sum>k \<in>{k' \<in> {0..<\<b>}. N $$ (i, k') = 1 \<and> N $$ (j, k') = 1} . N $$ (i, k) * N $$ (j, k)) + 
    (\<Sum>k \<in>{k' \<in> {0..<\<b>}. N $$ (i, k') = 0 \<or> N $$ (j, k') = 0} . N $$ (i, k) * N $$ (j, k))"
    using fin1 fin2 djnt sum.union_disjoint by blast 
  also have "... = card {k' \<in> {0..<\<b>}. N $$ (i, k') = 1 \<and> N $$ (j, k') = 1}" 
    by (simp add: zero)
  also have "... = mat_point_index N {i, j}" 
    using assms mat_point_index_two_alt[of i N j] by simp
  finally show ?thesis using incidence_mat_des_two_index assms by simp
qed

end

context pairwise_balance
begin

lemma ordered_pbdI: 
  assumes "\<B> = mset \<B>s" and "\<V> = set \<V>s" and "distinct \<V>s"
  shows "ordered_pairwise_balance \<V>s \<B>s \<Lambda>"
proof -
  interpret ois: ordered_incidence_system \<V>s \<B>s 
    using ordered_incidence_sysII assms finite_incidence_system_axioms by blast 
  show ?thesis using b_non_zero blocks_nempty assms t_lt_order balanced 
    by (unfold_locales)(simp_all)
qed
end

locale ordered_regular_pairwise_balance = ordered_pairwise_balance "\<V>s" "\<B>s" \<Lambda> + 
  regular_pairwise_balance "set \<V>s" "mset \<B>s" \<Lambda> \<r> for \<V>s and \<B>s and \<Lambda> and \<r>

sublocale ordered_regular_pairwise_balance \<subseteq> ordered_constant_rep
  by unfold_locales

context ordered_regular_pairwise_balance
begin

text \<open> Stinson's Theorem 1.15. Stinson \<^cite>\<open>"stinsonCombinatorialDesignsConstructions2004"\<close> 
gives an iff condition for incidence matrices of regular pairwise 
balanced designs. The other direction is proven in the @{term "zero_one_matrix"} context \<close>
lemma rpbd_incidence_matrix_cond: "N * (N\<^sup>T) = \<Lambda> \<cdot>\<^sub>m (J\<^sub>m \<v>) + (\<r> - \<Lambda>) \<cdot>\<^sub>m (1\<^sub>m \<v>)"
proof (intro eq_matI)
  fix i j
  assume ilt: "i < dim_row (int \<Lambda> \<cdot>\<^sub>m J\<^sub>m \<v> + int (\<r> - \<Lambda>) \<cdot>\<^sub>m 1\<^sub>m \<v>)" 
    and jlt: "j < dim_col (int \<Lambda> \<cdot>\<^sub>m J\<^sub>m \<v> + int (\<r> - \<Lambda>) \<cdot>\<^sub>m 1\<^sub>m \<v>)"
  then have "(int \<Lambda> \<cdot>\<^sub>m J\<^sub>m \<v> + int (\<r> - \<Lambda>) \<cdot>\<^sub>m 1\<^sub>m \<v>) $$ (i, j) = 
    (int \<Lambda> \<cdot>\<^sub>m J\<^sub>m \<v>) $$(i, j) + (int (\<r> - \<Lambda>) \<cdot>\<^sub>m 1\<^sub>m \<v>) $$ (i, j)" 
    by simp
  then have split: "(int \<Lambda> \<cdot>\<^sub>m J\<^sub>m \<v> + int (\<r> - \<Lambda>) \<cdot>\<^sub>m 1\<^sub>m \<v>) $$ (i, j) = 
    (int \<Lambda> \<cdot>\<^sub>m J\<^sub>m \<v>) $$(i, j) + (\<r> - \<Lambda>) * ((1\<^sub>m \<v>) $$ (i, j))"
    using ilt jlt by simp
  have lhs: "(int \<Lambda> \<cdot>\<^sub>m J\<^sub>m \<v>) $$(i, j) = \<Lambda>" using ilt jlt by simp
  show "(N * N\<^sup>T) $$ (i, j) = (int \<Lambda> \<cdot>\<^sub>m J\<^sub>m \<v> + int (\<r> - \<Lambda>) \<cdot>\<^sub>m 1\<^sub>m \<v>) $$ (i, j)"
  proof (cases "i = j")
    case True
    then have rhs: "(int (\<r> - \<Lambda>) \<cdot>\<^sub>m 1\<^sub>m \<v>) $$ (i, j) = (\<r> - \<Lambda>)" using ilt by fastforce 
    have "(int \<Lambda> \<cdot>\<^sub>m J\<^sub>m \<v> + int (\<r> - \<Lambda>) \<cdot>\<^sub>m 1\<^sub>m \<v>) $$ (i, j) = \<Lambda> + (\<r> - \<Lambda>)"
      using True jlt by auto
    then have "(int \<Lambda> \<cdot>\<^sub>m J\<^sub>m \<v> + int (\<r> - \<Lambda>) \<cdot>\<^sub>m 1\<^sub>m \<v>) $$ (i, j) = \<r>" 
      using reg_index_lt_rep by (simp add: nat_diff_split)
    then show ?thesis using lhs split rhs True transpose_N_mult_diag ilt jlt by simp
  next
    case False
    then have "(1\<^sub>m \<v>) $$ (i, j) = 0" using ilt jlt by simp
    then have "(\<r> - \<Lambda>) * ((1\<^sub>m \<v>) $$ (i, j)) = 0" using ilt jlt
      by (simp add: \<open>1\<^sub>m \<v> $$ (i, j) = 0\<close>) 
    then show ?thesis using lhs transpose_N_mult_off_diag ilt jlt False by simp
  qed
next
  show "dim_row (N * N\<^sup>T) = dim_row (int \<Lambda> \<cdot>\<^sub>m J\<^sub>m \<v> + int (\<r> - \<Lambda>) \<cdot>\<^sub>m 1\<^sub>m \<v>)"
    using transpose_N_mult_dim(1) by auto
next
  show "dim_col (N * N\<^sup>T) = dim_col (int \<Lambda> \<cdot>\<^sub>m J\<^sub>m \<v> + int (\<r> - \<Lambda>) \<cdot>\<^sub>m 1\<^sub>m \<v>)"
    using transpose_N_mult_dim(1) by auto
qed
end

locale ordered_bibd = ordered_proper_design \<V>s \<B>s + bibd "set \<V>s" "mset \<B>s" \<k> \<Lambda> 
  for \<V>s and \<B>s and \<k> and \<Lambda>

sublocale ordered_bibd \<subseteq> ordered_incomplete_design
  by unfold_locales

sublocale ordered_bibd \<subseteq> ordered_constant_rep \<V>s \<B>s \<r>
  by unfold_locales

sublocale ordered_bibd \<subseteq> ordered_pairwise_balance
  by unfold_locales

locale ordered_sym_bibd = ordered_bibd \<V>s \<B>s \<k> \<Lambda> + symmetric_bibd "set \<V>s" "mset \<B>s" \<k> \<Lambda> 
  for \<V>s and \<B>s and \<k> and \<Lambda>


sublocale ordered_sym_bibd \<subseteq> ordered_simple_design
  by (unfold_locales)

locale ordered_const_intersect_design = ordered_proper_design \<V>s \<B>s + const_intersect_design "set \<V>s" "mset \<B>s" \<m>
  for \<V>s \<B>s \<m>


locale simp_ordered_const_intersect_design = ordered_const_intersect_design + ordered_simple_design
begin 

lemma max_one_block_size_inter: 
  assumes "\<b> \<ge> 2"
  assumes "bl \<in># \<B>"
  assumes "card bl = \<m>"
  assumes "bl2 \<in># \<B> - {#bl#}"
  shows "\<m> < card bl2"
proof -
  have sd: "simple_design \<V> \<B>"
    by (simp add: simple_design_axioms) 
  have bl2in: "bl2 \<in># \<B>" using assms(4)
    by (meson in_diffD)
  have blin: "bl \<in># {#b \<in># \<B> . card b = \<m>#}" using assms(3) assms(2) by simp
  then have slt: "size {#b \<in># \<B> . card b = \<m>#} = 1" using simple_const_inter_iff sd assms(1)
    by (metis count_empty count_eq_zero_iff less_one nat_less_le size_eq_0_iff_empty) 
  then have "size {#b \<in># (\<B> - {#bl#}) . card b = \<m>#} = 0" using blin
    by (smt (verit) add_mset_eq_singleton_iff count_eq_zero_iff count_filter_mset 
        filter_mset_add_mset insert_DiffM size_1_singleton_mset size_eq_0_iff_empty) 
  then have ne: "card bl2 \<noteq> \<m>" using assms(4)
    by (metis (mono_tags, lifting) filter_mset_empty_conv size_eq_0_iff_empty) 
  thus ?thesis using inter_num_le_block_size assms bl2in nat_less_le by presburger 
qed

lemma block_size_inter_num_cases:
  assumes "bl \<in># \<B>"
  assumes "\<b> \<ge> 2"
  shows "\<m> < card bl \<or> (card bl = \<m> \<and> (\<forall> bl' \<in># (\<B> - {#bl#}) . \<m> < card bl'))"
proof (cases "card bl = \<m>")
  case True
  have "(\<And> bl'. bl' \<in># (\<B> - {#bl#}) \<Longrightarrow> \<m> < card bl')"
    using max_one_block_size_inter True assms by simp
  then show ?thesis using True by simp
next
  case False
  then have "\<m> < card bl" using assms inter_num_le_block_size nat_less_le by presburger
  then show ?thesis by simp
qed

lemma indexed_const_intersect: 
  assumes "j1 < \<b>"
  assumes "j2 < \<b>"
  assumes "j1 \<noteq> j2"
  shows "(\<B>s ! j1) |\<inter>| (\<B>s ! j2) = \<m>"
proof -
  obtain bl1 bl2 where "bl1 \<in># \<B>" and "\<B>s ! j1 = bl1" and "bl2 \<in># \<B> - {#bl1#}" and "\<B>s ! j2 = bl2" 
    using obtains_two_diff_block_indexes assms by fastforce 
  thus ?thesis by (simp add: const_intersect)
qed

lemma const_intersect_block_size_diff: 
  assumes "j' < \<b>" and "j < \<b>" and "j \<noteq> j'" and "card (\<B>s ! j') = \<m>" and "\<b> \<ge> 2"
  shows "card (\<B>s ! j) - \<m> > 0"
proof -
  obtain bl1 bl2 where "bl1 \<in># \<B>" and "\<B>s ! j' = bl1" and "bl2 \<in># \<B> - {#bl1#}" and "\<B>s ! j = bl2"
    using assms(1) assms(2) assms(3) obtains_two_diff_block_indexes by fastforce 
  then have "\<m> < card (bl2)" 
    using max_one_block_size_inter assms(4) assms(5) by blast  
  thus ?thesis
    by (simp add: \<open>\<B>s ! j = bl2\<close>) 
qed

lemma scalar_prod_inc_vec_const_inter: 
  assumes "j1 < \<b>" "j2 < \<b>" "j1 \<noteq> j2"
  shows "(col N j1) \<bullet> (col N j2) = \<m>"
  using scalar_prod_inc_vec_inter_num indexed_const_intersect assms by simp

end

subsection \<open> Zero One Matrix Incidence System Existence \<close>
text \<open>We prove 0-1 matrices with certain properties imply the existence of an incidence system
with particular properties. This leads to Stinson's theorem in the other direction \<^cite>\<open>"stinsonCombinatorialDesignsConstructions2004"\<close> \<close>

context zero_one_matrix
begin

lemma mat_is_ordered_incidence_sys: "ordered_incidence_system [0..<(dim_row M)] (map (map_col_to_block) (cols M))"
  apply (unfold_locales, simp_all)
  using map_col_to_block_wf atLeastLessThan_upt by blast

interpretation mat_ord_inc_sys: ordered_incidence_system "[0..<(dim_row M)]" "(map (map_col_to_block) (cols M))"
  by (simp add: mat_is_ordered_incidence_sys)

lemma mat_ord_inc_sys_N: "mat_ord_inc_sys.N = lift_01_mat M" 
  by (intro eq_matI, simp_all add: inc_mat_of_def map_col_to_block_elem) 
    (metis lift_01_mat_simp(3) lift_mat_01_index_iff(2) of_zero_neq_one_def)

lemma map_col_to_block_mat_rep_num:
  assumes "x <dim_row M"
  shows "({# map_col_to_block c . c \<in># mset (cols M)#} rep x) = mat_rep_num M x"
proof -
  have "mat_rep_num M x = mat_rep_num (lift_01_mat M) x" 
    using preserve_mat_rep_num mat_ord_inc_sys_N
    by (metis assms lift_01_mat_def of_inj_on_01_hom.inj_on_01_hom_axioms)
  then have "mat_rep_num M x = (mat_rep_num mat_ord_inc_sys.N x)" using mat_ord_inc_sys_N by (simp) 
  then have "mat_rep_num M x = mset (map (map_col_to_block) (cols M)) rep x"
    using assms atLeastLessThan_upt card_atLeastLessThan mat_ord_inc_sys.mat_rep_num_N_row 
      mat_ord_inc_sys_point minus_nat.diff_0 by presburger
  thus ?thesis using ordered_to_mset_col_blocks
    by presburger 
qed

end 

context zero_one_matrix_ring_1
begin

lemma transpose_cond_index_vals: 
  assumes "M * (M\<^sup>T) = \<Lambda> \<cdot>\<^sub>m (J\<^sub>m (dim_row M)) + (r - \<Lambda>) \<cdot>\<^sub>m (1\<^sub>m (dim_row M))"
  assumes "i < dim_row (M * (M\<^sup>T))"
  assumes "j < dim_col (M * (M\<^sup>T))"
  shows "i = j \<Longrightarrow> (M * (M\<^sup>T)) $$ (i, j) = r" "i \<noteq> j \<Longrightarrow> (M * (M\<^sup>T)) $$ (i, j) = \<Lambda>"
  using assms by auto

end

locale zero_one_matrix_int = zero_one_matrix_ring_1 M for M :: "int mat"
begin

text \<open>Some useful conditions on the transpose product for matrix system properties \<close>
lemma transpose_cond_diag_r:
  assumes "i < dim_row (M * (M\<^sup>T))"
  assumes "\<And> j. i = j \<Longrightarrow> (M * (M\<^sup>T)) $$ (i, j) = r"
  shows "mat_rep_num M i = r"
proof -
  have eqr: "(M * M\<^sup>T) $$ (i, i) = r" using assms(2)
    by simp
  have unsq: "\<And> k . k < dim_col M \<Longrightarrow> (M $$ (i, k))^2 = M $$ (i, k)"
    using assms elems01 by fastforce
  have "sum_vec (row M i) = (\<Sum>k \<in>{0..<(dim_col M)} . (row M i) $ k)"
    using assms by (simp add: sum_vec_def)
  also have "... = (\<Sum>k \<in>{0..<(dim_col M)} . M $$ (i, k))"
    using assms by auto
  also have "... = (\<Sum>k \<in>{0..<(dim_col M)} . M $$ (i, k)^2)"
    using atLeastLessThan_iff sum.cong unsq by simp
  also have "... = (\<Sum>k \<in>{0..<(dim_col M)} . M $$ (i, k) * M $$ (i, k))"
    using assms by (simp add: power2_eq_square)
  also have "... = (M * M\<^sup>T) $$ (i, i)" 
    using assms transpose_mat_mult_entries[of "i" "M" "i"] by simp
  finally have "sum_vec (row M i) = r" using eqr by simp
  thus ?thesis using mat_rep_num_sum_alt
    by (metis assms(1) elems01 index_mult_mat(2) of_nat_eq_iff) 
qed


lemma transpose_cond_non_diag:
  assumes "i1 < dim_row (M * (M\<^sup>T))"
  assumes "i2 < dim_row (M * (M\<^sup>T))"
  assumes "i1 \<noteq> i2"
  assumes "\<And> j i. j \<noteq> i \<Longrightarrow> i < dim_row (M * (M\<^sup>T)) \<Longrightarrow> j < dim_row (M * (M\<^sup>T)) \<Longrightarrow> (M * (M\<^sup>T)) $$ (i, j) = \<Lambda>"
  shows "\<Lambda> = mat_point_index M {i1, i2}"
proof -
  have ilt: "i1 < dim_row M" "i2 < dim_row M"
    using assms(1) assms (2) by auto
  have rev: "\<And> k. k \<in> {0..<dim_col M} \<Longrightarrow> 
      \<not> (M $$ (i1, k) = 1 \<and> M $$ (i2, k) = 1) \<longleftrightarrow> M $$ (i1, k) = 0 \<or> M $$ (i2, k) = 0"
    using assms elems01 by fastforce 
  then have split: "{0..<dim_col M} = {k \<in> {0..<dim_col M}. M $$ (i1, k) = 1 \<and> M $$ (i2, k) = 1} \<union> 
      {k \<in> {0..<dim_col M}. M $$ (i1, k) = 0 \<or> M $$ (i2, k) = 0}"
    by blast
  have zero: "\<And> k . k \<in> {0..<dim_col M} \<Longrightarrow> M $$ (i1, k) = 0 \<or> M $$ (i2, k) = 0 \<Longrightarrow> M $$ (i1, k) * M$$ (i2, k) = 0"
    by simp 
  have djnt: "{k \<in> {0..<dim_col M}. M $$ (i1, k) = 1 \<and> M $$ (i2, k) = 1} \<inter> 
      {k \<in> {0..<dim_col M}. M $$ (i1, k) = 0 \<or> M $$ (i2, k) = 0} = {}" 
    using rev by auto
  have fin1: "finite {k \<in> {0..<dim_col M}. M $$ (i1, k) = 1 \<and> M $$ (i2, k) = 1}" by simp
  have fin2: "finite {k \<in> {0..<dim_col M}. M $$ (i1, k) = 0 \<or> M $$ (i2, k) = 0}" by simp
  have "mat_point_index M {i1, i2} = card {k' \<in> {0..<dim_col M}. M $$ (i1, k') = 1 \<and>M $$ (i2, k') = 1}"
    using mat_point_index_two_alt ilt assms(3) by auto
  then have "mat_point_index M {i1, i2} = 
    (\<Sum>k \<in>{k' \<in> {0..<dim_col M}. M $$ (i1, k') = 1 \<and> M $$ (i2, k') = 1} . M $$ (i1, k) * M $$ (i2, k)) + 
    (\<Sum>k \<in>{k' \<in> {0..<dim_col M}. M $$ (i1, k') = 0 \<or> M $$ (i2, k') = 0} . M $$ (i1, k) * M $$ (i2, k))"
    by (simp add: zero) (* Odd behaviour if I use also have here *)
  also have "... = (\<Sum>k \<in>({k' \<in> {0..<dim_col M}. M $$ (i1, k') = 1 \<and> M $$ (i2, k') = 1} \<union> 
    {k' \<in> {0..<dim_col M}. M $$ (i1, k') = 0 \<or> M $$ (i2, k') = 0}) . M $$ (i1, k) * M $$ (i2, k))"
    using fin1 fin2 djnt sum.union_disjoint by (metis (no_types, lifting)) 
  also have "... =  (\<Sum>k \<in>{0..<dim_col M} . M $$ (i1, k) * M $$ (i2, k))"
    using split by metis
  finally have "mat_point_index M {i1, i2} = (M * (M\<^sup>T)) $$ (i1, i2)"
    using assms(1) assms(2) transpose_mat_mult_entries[of "i1" "M" "i2"] by simp
  thus ?thesis using assms by presburger 
qed

lemma trans_cond_implies_map_rep_num:
  assumes "M * (M\<^sup>T) = \<Lambda> \<cdot>\<^sub>m (J\<^sub>m (dim_row M)) + (r - \<Lambda>) \<cdot>\<^sub>m (1\<^sub>m (dim_row M))"
  assumes "x < dim_row M"
  shows "(image_mset map_col_to_block (mset (cols M))) rep x = r"
proof -
  interpret ois: ordered_incidence_system "[0..<dim_row M]" "map map_col_to_block (cols M)"
    using mat_is_ordered_incidence_sys by simp
  have eq: "ois.\<B> rep x = sum_vec (row M x)" using ois.point_rep_mat_row_sum
    by (simp add: assms(2) inc_mat_of_map_rev) 
  then have "\<And> j. x = j \<Longrightarrow> (M * (M\<^sup>T)) $$ (x, j) = r" using assms(1) transpose_cond_index_vals
    by (metis assms(2) index_mult_mat(2) index_mult_mat(3) index_transpose_mat(3)) 
  thus ?thesis using eq transpose_cond_diag_r assms(2) index_mult_mat(2)
    by (metis map_col_to_block_mat_rep_num) 
qed

lemma trans_cond_implies_map_index:
  assumes "M * (M\<^sup>T) = \<Lambda> \<cdot>\<^sub>m (J\<^sub>m (dim_row M)) + (r - \<Lambda>) \<cdot>\<^sub>m (1\<^sub>m (dim_row M))"
  assumes "ps \<subseteq> {0..<dim_row M}"
  assumes "card ps = 2"
  shows "(image_mset map_col_to_block (mset (cols M))) index ps = \<Lambda>"
proof - 
  interpret ois: ordered_incidence_system "[0..<dim_row M]" "map map_col_to_block (cols M)"
    using mat_is_ordered_incidence_sys by simp
  obtain i1 i2 where i1in: "i1 <dim_row M" and i2in: "i2 <dim_row M" and psis: "ps = {i1, i2}" and neqi: "i1 \<noteq> i2"
    using assms(2) assms(3) card_2_iff insert_subset by (metis atLeastLessThan_iff) 
  have cond: "\<And> j i. j \<noteq> i \<Longrightarrow> i < dim_row (M * (M\<^sup>T)) \<Longrightarrow> j < dim_row (M * (M\<^sup>T)) \<Longrightarrow> (M * (M\<^sup>T)) $$ (i, j) = \<Lambda>"
    using assms(1) by simp
  then have "(image_mset map_col_to_block (mset (cols M))) index ps = mat_point_index M ps"
     using ois.incidence_mat_two_index psis i1in i2in by (simp add: neqi inc_mat_of_map_rev)
  thus ?thesis using cond transpose_cond_non_diag[of i1 i2 \<Lambda>] i1in i2in index_mult_mat(2)[of "M" "M\<^sup>T"] 
       neqi of_nat_eq_iff psis by simp
qed

text \<open> Stinson Theorem 1.15 existence direction \<close>
lemma rpbd_exists: 
  assumes "dim_row M \<ge> 2" \<comment> \<open>Min two points\<close>
  assumes "dim_col M \<ge> 1" \<comment> \<open>Min one block\<close>
  assumes "\<And> j. j < dim_col M \<Longrightarrow> 1 \<in>$ col M j" \<comment> \<open>no empty blocks \<close>
  assumes "M * (M\<^sup>T) = \<Lambda> \<cdot>\<^sub>m (J\<^sub>m (dim_row M)) + (r - \<Lambda>) \<cdot>\<^sub>m (1\<^sub>m (dim_row M))"
  shows "ordered_regular_pairwise_balance [0..<dim_row M] (map map_col_to_block (cols M)) \<Lambda> r"
proof -
  interpret ois: ordered_incidence_system "[0..<dim_row M]" "(map map_col_to_block (cols M))"
    using mat_is_ordered_incidence_sys by simp
  interpret pdes: ordered_design "[0..<dim_row M]" "(map map_col_to_block (cols M))"
    using assms(2) mat_is_design assms(3)
    by (simp add: ordered_design_def ois.ordered_incidence_system_axioms)  
  show ?thesis using assms trans_cond_implies_map_index trans_cond_implies_map_rep_num 
    by (unfold_locales) (simp_all)
qed

lemma vec_k_uniform_mat_block_size: 
  assumes "((u\<^sub>v (dim_row M)) \<^sub>v* M) = k \<cdot>\<^sub>v (u\<^sub>v (dim_col M))"
  assumes "j < dim_col M"
  shows "mat_block_size M j = k"
proof -
  have "mat_block_size M j = sum_vec (col M j)" using assms(2)
    by (simp add: elems01 mat_block_size_sum_alt) 
  also have "... = ((u\<^sub>v (dim_row M)) \<^sub>v* M) $ j" using assms(2) 
    by (simp add: sum_vec_def scalar_prod_def)
  finally show ?thesis using  assms(1) assms(2) by (simp)
qed

lemma vec_k_impl_uniform_block_size: 
  assumes "((u\<^sub>v (dim_row M)) \<^sub>v* M) = k \<cdot>\<^sub>v (u\<^sub>v (dim_col M))"
  assumes "bl \<in># (image_mset map_col_to_block (mset (cols M)))"
  shows "card bl = k"
proof -
  obtain j where jlt: "j < dim_col M" and bleq: "bl = map_col_to_block (col M j)"
    using assms(2) obtain_block_index_map_block_set by blast 
  then have "card (map_col_to_block (col M j)) = mat_block_size M j"
    by (simp add: map_col_to_block_size) 
  thus ?thesis using vec_k_uniform_mat_block_size assms(1) bleq jlt by blast 
qed

lemma bibd_exists: 
  assumes "dim_col M \<ge> 1" \<comment> \<open>Min one block\<close>
  assumes "\<And> j. j < dim_col M \<Longrightarrow> 1 \<in>$ col M j" \<comment> \<open>no empty blocks \<close>
  assumes "M * (M\<^sup>T) = \<Lambda> \<cdot>\<^sub>m (J\<^sub>m (dim_row M)) + (r - \<Lambda>) \<cdot>\<^sub>m (1\<^sub>m (dim_row M))"
  assumes "((u\<^sub>v (dim_row M)) \<^sub>v* M) = k \<cdot>\<^sub>v (u\<^sub>v (dim_col M))"
  assumes "(r ::nat) \<ge> 0"
  assumes "k \<ge> 2" "k < dim_row M"
  shows "ordered_bibd [0..<dim_row M] (map map_col_to_block (cols M)) k \<Lambda>"
proof -
  interpret ipbd: ordered_regular_pairwise_balance "[0..<dim_row M]" "(map map_col_to_block (cols M))" \<Lambda> r
    using rpbd_exists assms by simp
  show ?thesis using vec_k_impl_uniform_block_size by (unfold_locales, simp_all add: assms)
qed

end

subsection \<open>Isomorphisms and Incidence Matrices \<close>
text \<open>If two incidence systems have the same incidence matrix, they are isomorphic. Similarly
if two incidence systems are isomorphic there exists an ordering such that they have the same
incidence matrix \<close>
locale two_ordered_sys = D1: ordered_incidence_system \<V>s \<B>s + D2: ordered_incidence_system \<V>s' \<B>s'
  for "\<V>s" and "\<B>s" and "\<V>s'" and "\<B>s'" 

begin

lemma equal_inc_mat_isomorphism: 
  assumes "D1.N = D2.N"
  shows "incidence_system_isomorphism D1.\<V> D1.\<B> D2.\<V> D2.\<B> (\<lambda> x . \<V>s' ! (List_Index.index \<V>s x))"
proof (unfold_locales)
  show "bij_betw (\<lambda>x. \<V>s' ! List_Index.index \<V>s x) D1.\<V> D2.\<V>" 
  proof -
    have comp: "(\<lambda>x. \<V>s' ! List_Index.index \<V>s x) = (\<lambda> i. \<V>s' ! i) \<circ> (\<lambda> y . List_Index.index \<V>s y)"
      by (simp add: comp_def)
    have leq: "length \<V>s = length \<V>s'" 
      using assms D1.dim_row_is_v D1.points_list_length D2.dim_row_is_v D2.points_list_length by force 
    have bij1: "bij_betw (\<lambda> i. \<V>s' !i) {..<length \<V>s} (set \<V>s') " using leq
      by (simp add: bij_betw_nth D2.distinct) 
    have "bij_betw (List_Index.index \<V>s) (set \<V>s) {..<length \<V>s}" using D1.distinct
      by (simp add: bij_betw_index lessThan_atLeast0) 
    thus ?thesis using bij_betw_trans comp bij1 by simp
  qed
next
  have len:  "length (map ((`) (\<lambda>x. \<V>s' ! List_Index.index \<V>s x)) \<B>s) = length \<B>s'"
    using length_map assms D1.dim_col_is_b by force 
  have mat_eq: "\<And> i j . D1.N $$ (i, j) = D2.N $$ (i, j)" using assms
    by simp 
  have vslen: "length \<V>s = length \<V>s'" using assms
      using D1.dim_row_is_v D1.points_list_length D2.dim_row_is_v D2.points_list_length by force 
  have "\<And> j. j < length \<B>s' \<Longrightarrow> (map ((`) (\<lambda>x. \<V>s' ! List_Index.index \<V>s x)) \<B>s) ! j = \<B>s' ! j"
  proof -
    fix j assume a: "j < length \<B>s'" 
    then have "(map ((`) (\<lambda>x. \<V>s' ! List_Index.index \<V>s x)) \<B>s) ! j = (\<lambda>x. \<V>s' ! List_Index.index \<V>s x) ` (\<B>s ! j)"
      by (metis D1.blocks_list_length D1.dim_col_is_b D2.blocks_list_length D2.dim_col_is_b assms nth_map) 
    also have "... = (\<lambda> i . \<V>s' ! i) ` ((\<lambda> x. List_Index.index \<V>s x) ` (\<B>s ! j))" 
      by blast
    also have "... = ((\<lambda> i . \<V>s' ! i) ` {i . i < length \<V>s \<and> D1.N $$ (i, j) = 1})" 
      using D1.block_mat_cond_rev a assms
      by (metis (no_types, lifting) D1.blocks_list_length D1.dim_col_is_b D2.blocks_list_length D2.dim_col_is_b) 
    also have "... = ((\<lambda> i . \<V>s' ! i) ` {i . i < length \<V>s' \<and> D2.N $$ (i, j) = 1})" 
      using vslen mat_eq by simp
    finally have "(map ((`) (\<lambda>x. \<V>s' ! List_Index.index \<V>s x)) \<B>s) ! j = (\<B>s' ! j)" 
      using D2.block_mat_cond_rep' a by presburger
    then show "(map ((`) (\<lambda>x. \<V>s' ! List_Index.index \<V>s x)) \<B>s) ! j = (\<B>s' ! j)" by simp
  qed
  then have "map ((`) (\<lambda>x. \<V>s' ! List_Index.index \<V>s x)) \<B>s = \<B>s'" 
    using len nth_equalityI[of "(map ((`) (\<lambda>x. \<V>s' ! List_Index.index \<V>s x)) \<B>s)" "\<B>s'"] by simp
  then show "image_mset ((`) (\<lambda>x. \<V>s' ! List_Index.index \<V>s x)) D1.\<B> = D2.\<B>"
    using mset_map by auto
qed

lemma equal_inc_mat_isomorphism_ex: "D1.N = D2.N \<Longrightarrow> \<exists> \<pi> . incidence_system_isomorphism D1.\<V> D1.\<B> D2.\<V> D2.\<B> \<pi>"
  using equal_inc_mat_isomorphism by auto 

lemma equal_inc_mat_isomorphism_obtain: 
  assumes "D1.N = D2.N"
  obtains \<pi> where "incidence_system_isomorphism D1.\<V> D1.\<B> D2.\<V> D2.\<B> \<pi>"
  using equal_inc_mat_isomorphism assms by auto 

end

context incidence_system_isomorphism
begin

lemma exists_eq_inc_mats:
  assumes "finite \<V>" "finite \<V>'"
  obtains N where "is_incidence_matrix N \<V> \<B>" and "is_incidence_matrix N \<V>' \<B>'"
proof -
  obtain Vs where vsis: "Vs \<in> permutations_of_set \<V>" using assms
    by (meson all_not_in_conv permutations_of_set_empty_iff) 
  obtain Bs where bsis: "Bs \<in> permutations_of_multiset \<B>"
    by (meson all_not_in_conv permutations_of_multiset_not_empty) 
  have inj: "inj_on \<pi> \<V>" using bij
    by (simp add: bij_betw_imp_inj_on) 
  then have mapvs: "map \<pi> Vs \<in> permutations_of_set \<V>'" using permutations_of_set_image_inj
    using \<open>Vs \<in> permutations_of_set \<V>\<close> iso_points_map by blast 
  have "permutations_of_multiset (image_mset ((`)\<pi>) \<B>) = map ((`) \<pi>) ` permutations_of_multiset \<B>"
    using block_img permutations_of_multiset_image by blast 
  then have mapbs: "map ((`) \<pi>) Bs \<in> permutations_of_multiset \<B>'" using bsis block_img by blast 
  define N :: "'c :: {ring_1} mat" where "N \<equiv> inc_mat_of Vs Bs" 
  have "is_incidence_matrix N \<V> \<B>"
    using N_def bsis is_incidence_matrix_def vsis by blast
  have "\<And> bl . bl \<in> (set Bs) \<Longrightarrow> bl \<subseteq> (set Vs)"
    by (meson bsis in_multiset_in_set ordered_incidence_system.wf_list source.alt_ordering_sysI vsis) 
  then have "N = inc_mat_of (map \<pi> Vs) (map ((`) \<pi>) Bs)" 
    using inc_mat_of_bij_betw inj
    by (metis N_def permutations_of_setD(1) vsis) 
  then have "is_incidence_matrix N \<V>' \<B>'"
    using mapbs mapvs is_incidence_matrix_def by blast 
  thus ?thesis
    using \<open>is_incidence_matrix N \<V> \<B>\<close> that by auto 
qed

end

end