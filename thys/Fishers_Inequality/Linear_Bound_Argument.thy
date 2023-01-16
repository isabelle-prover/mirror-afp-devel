(* Title: Linear_Bound_Argument.thy
   Author: Chelsea Edmonds
*)
section \<open>Linear Bound Argument - General \<close>
text \<open>Lemmas to enable general reasoning using the linear bound argument for combinatorial proofs.
Jukna \<^cite>\<open>"juknaExtremalCombinatorics2011"\<close> presents a good overview of the mathematical background 
this theory is based on and applications \<close>
theory Linear_Bound_Argument imports Incidence_Matrices Jordan_Normal_Form.DL_Rank 
Jordan_Normal_Form.Ring_Hom_Matrix
begin

subsection \<open>Vec Space Extensions\<close>
text \<open>Simple extensions to the existing vector space locale on linear independence \<close>
context vec_space
begin 
lemma lin_indpt_set_card_lt_dim: 
  fixes A :: "'a vec set"
  assumes "A \<subseteq> carrier_vec n"
  assumes "lin_indpt A"
  shows "card A \<le> dim"
  using assms(1) assms(2) fin_dim li_le_dim(2) by blast

lemma lin_indpt_dim_col_lt_dim: 
  fixes A :: "'a mat"
  assumes "A \<in> carrier_mat n nc"
  assumes "distinct (cols A)"
  assumes "lin_indpt (set (cols A))"
  shows "nc \<le> dim"
proof -
  have b: "card (set (cols A)) = dim_col A" using cols_length assms(2)
    by (simp add: distinct_card) 
  have "set (cols A) \<subseteq> carrier_vec n" using assms(1) cols_dim by blast
  thus ?thesis using lin_indpt_set_card_lt_dim assms b by auto
qed

lemma lin_comb_imp_lin_dep_fin: 
  fixes A :: "'a vec set"
  assumes "finite A"
  assumes "A \<subseteq> carrier_vec n"
  assumes "lincomb c A = 0\<^sub>v n"
  assumes "\<exists> a. a \<in> A \<and> c a \<noteq> 0"
  shows "lin_dep A"
  unfolding lin_dep_def using assms lincomb_as_lincomb_list_distinct sumlist_nth by auto

text \<open>While a trivial definition, this enables us to directly reference the definition outside
of a locale context, as @{term "lin_indpt"} is an inherited definition \<close>
definition lin_indpt_vs:: "'a vec set \<Rightarrow> bool" where
"lin_indpt_vs A \<longleftrightarrow> lin_indpt A"

lemma lin_comb_sum_lin_indpt: 
  fixes A :: "'a vec list"
  assumes "set (A) \<subseteq> carrier_vec n"
  assumes "distinct A"
  assumes "\<And> f. lincomb_list (\<lambda>i. f (A ! i)) A = 0\<^sub>v n \<Longrightarrow> \<forall>v\<in> (set A). f v = 0"
  shows "lin_indpt (set A)"
  by (rule finite_lin_indpt2, auto simp add: assms lincomb_as_lincomb_list_distinct)

lemma lin_comb_mat_lin_indpt: 
  fixes A :: "'a vec list"
  assumes "set (A) \<subseteq> carrier_vec n"
  assumes "distinct A"
  assumes "\<And> f. mat_of_cols n A *\<^sub>v vec (length A) (\<lambda>i. f (A ! i))  = 0\<^sub>v n \<Longrightarrow> \<forall>v\<in> (set A). f v = 0"
  shows "lin_indpt (set A)"
proof (rule lin_comb_sum_lin_indpt, auto simp add: assms)
  fix f v 
  have "\<And> v. v \<in> set A \<Longrightarrow> dim_vec v = n"
    using assms by auto
  then show "lincomb_list (\<lambda>i. f (A ! i)) A = 0\<^sub>v n \<Longrightarrow> v \<in> set A \<Longrightarrow> f v = 0"
    using  lincomb_list_as_mat_mult[of A "(\<lambda>i. f (A ! i))"] assms(3)[of f] by auto
qed

lemma lin_comb_mat_lin_indpt_vs: 
  fixes A :: "'a vec list"
  assumes "set (A) \<subseteq> carrier_vec n"
  assumes "distinct A"
  assumes "\<And> f. mat_of_cols n A *\<^sub>v vec (length A) (\<lambda>i. f (A ! i))  = 0\<^sub>v n \<Longrightarrow> \<forall>v\<in> (set A). f v = 0"
  shows "lin_indpt_vs (set A)"
  using lin_comb_mat_lin_indpt lin_indpt_vs_def assms by auto


end

subsection \<open>Linear Bound Argument Lemmas\<close>

text \<open>Three general representations of the linear bound argument, requiring a direct fact of 
linear independence onthe rows of the vector space over either a set A of vectors, list xs of vectors
or a Matrix' columns \<close>
lemma lin_bound_arg_general_set: 
  fixes A ::"('a :: {field})vec set"
  assumes "A \<subseteq> carrier_vec nr"
  assumes "vec_space.lin_indpt_vs nr A"
  shows "card A \<le> nr"
  using vec_space.lin_indpt_set_card_lt_dim[of "A" "nr"] vec_space.lin_indpt_vs_def[of nr A] 
    vec_space.dim_is_n assms by metis 

lemma lin_bound_arg_general_list: 
  fixes xs ::"('a :: {field})vec list"
  assumes "distinct xs"
  assumes "(set xs) \<subseteq> carrier_vec nr"
  assumes "vec_space.lin_indpt_vs nr (set xs)"
  shows "length (xs) \<le> nr"
  using lin_bound_arg_general_set[of "set xs" nr] distinct_card assms
  by force 

lemma lin_bound_arg_general: 
  fixes A ::"('a :: {field}) mat"
  assumes "distinct (cols A)"
  assumes "A \<in> carrier_mat nr nc"
  assumes "vec_space.lin_indpt_vs nr (set (cols A))"
  shows "nc \<le> nr"
proof -
  have ss: "set (cols A) \<subseteq> carrier_vec nr" using assms cols_dim by blast 
  have "length (cols A) = nc"
    using assms(2) cols_length by blast 
  thus ?thesis using lin_bound_arg_general_list[of "cols A" "nr"] ss assms by simp
qed

text\<open>The linear bound argument lemma on a matrix requiring the lower level assumption on a linear
combination. This removes the need to directly refer to any aspect of the linear algebra libraries \<close>
lemma lin_bound_argument: 
  fixes A :: "('a :: {field}) mat"
  assumes "distinct (cols A)"
  assumes "A \<in> carrier_mat nr nc"
  assumes "\<And> f. A *\<^sub>v vec nc (\<lambda>i. f (col A i)) = 0\<^sub>v nr \<Longrightarrow> \<forall>v\<in> (set (cols A)). f v = 0"
  shows "nc \<le> nr"
proof (intro lin_bound_arg_general[of "A" nr nc] vec_space.lin_comb_mat_lin_indpt_vs, simp_all add: assms)
  show "set (cols A) \<subseteq> carrier_vec nr" using assms cols_dim by blast
next
  have mA: "mat_of_cols nr (cols A) = A" using mat_of_cols_def assms by auto
  have "\<And> f. vec (dim_col A) (\<lambda>i. f (cols A ! i)) = vec nc (\<lambda>i. f (col A i))"
  proof (intro eq_vecI, simp_all add: assms)
    show "\<And>f i. i < nc \<Longrightarrow> vec (dim_col A) (\<lambda>i. f (cols A ! i)) $ i = f (col A i)"
      using assms(2) by force
    show "dim_col A = nc " using assms by simp
  qed
  then show "\<And>f. mat_of_cols nr (cols A) *\<^sub>v vec (dim_col A) (\<lambda>i. f (cols A ! i)) = 0\<^sub>v nr \<Longrightarrow> 
      \<forall>v\<in>set (cols A). f v = 0"
    using mA assms(3) by metis
qed

text \<open>A further extension to present the linear combination directly as a sum. This manipulation from 
vector product to a summation was found to commonly be repeated in proofs applying this rule \<close>
lemma lin_bound_argument2: 
  fixes A :: "('a :: {field}) mat"
  assumes "distinct (cols A)"
  assumes "A \<in> carrier_mat nr nc"
  assumes "\<And> f. vec nr (\<lambda>i. \<Sum> j \<in> {0..<nc} . f (col A j) * (col A j) $ i) = 0\<^sub>v nr \<Longrightarrow> 
    \<forall>v\<in> (set (cols A)). f v = 0"
  shows "nc \<le> nr"
proof (intro lin_bound_argument[of A nr nc], simp add: assms, simp add: assms)
  fix f 
  have "A *\<^sub>v vec nc (\<lambda>i. f (col A i)) = 
      vec (dim_row A) (\<lambda>i. \<Sum> j \<in> {0..<nc} . (row A i $ j) * f (col A j))"
    by (auto simp add: mult_mat_vec_def scalar_prod_def assms(2)) 
  also have "... = vec (dim_row A) (\<lambda>i. \<Sum> j \<in> {0..<nc} . f (col A j) * (col A j $ i))"
    using assms(2) by (intro eq_vecI, simp_all) (meson mult.commute) 
  finally show "A *\<^sub>v vec nc (\<lambda>i. f (col A i)) = 0\<^sub>v nr \<Longrightarrow> \<forall>v\<in>set (cols A). f v = 0" 
    using assms(3)[of f] assms(2) by fastforce 
qed

end