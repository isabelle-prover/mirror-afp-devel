(* Title: Fishers_Inequality_Variations.thy
   Author: Chelsea Edmonds
*)

section \<open>Variations on Fisher's Inequality \<close>

theory Fishers_Inequality_Variations imports Dual_Systems Rank_Argument_General
Vector_Matrix_Mod Linear_Bound_Argument
begin

subsection \<open> Matrix mod properties \<close>
text \<open>This is reasoning on properties specific to incidence matrices under @{term "mat_mod"}. Ultimately, 
this definition was not used in the final proof but it is left as is in case of future use \<close>

context mat_mod
begin

lemma mat_mod_proper_iff:  "proper_inc_mat (mat_mod N)  \<longleftrightarrow> proper_inc_mat N"
  by (simp add: proper_inc_mat_def)

lemma mat_mod_rep_num_eq:  "i < dim_row N \<Longrightarrow> elements_mat N \<subseteq> {0..<m} \<Longrightarrow> 
    mat_rep_num (mat_mod N) i = mat_rep_num N i"
  by (simp add: mat_mod_count_row_eq mat_rep_num_def)

lemma mat_point_index_eq: "elements_mat N \<subseteq> {0..<m} \<Longrightarrow> 
    mat_point_index (mat_mod N) I = mat_point_index N I"
  by (simp add:  mat_mod_eq_cond) 

lemma mod_mat_inter_num_eq: "elements_mat N \<subseteq> {0..<m} \<Longrightarrow> 
    mat_inter_num (mat_mod N) j1 j2 = mat_inter_num N j1 j2"
  by (simp add: mat_mod_eq_cond) 

lemma mod_mat_block_size: "elements_mat N \<subseteq> {0..<m} \<Longrightarrow> mat_block_size (mat_mod N) j = mat_block_size N j"
  by (simp add: mat_mod_eq_cond) 

lemma mat_mod_non_empty_col_iff: "elements_mat M \<subseteq> {0..<m} \<Longrightarrow> 
    non_empty_col (mat_mod M) j \<longleftrightarrow> non_empty_col M j"
  using mat_mod_eq_cond by auto 
end

context mat_mod_type
begin

lemma mat_rep_num_MM_Rel: 
  assumes "MM_Rel A B"
  assumes "i < dim_row A"
  shows "mat_rep_num (mat_mod A) i = mat_rep_num B i"
  unfolding mat_rep_num_def using vec_count_MV_Rel_direct assms mat_mod_vec_mod_row row_map_mat
  by (metis MM_Rel_def MV_Rel_def index_map_mat(2) mat_mod_dim(1) to_int_mod_ring_hom.hom_one) 


lemma mat_block_size_MM_Rel: 
  assumes "MM_Rel A B"
  assumes " j < dim_col A"
  shows "mat_block_size (mat_mod A) j = mat_block_size B j"
  unfolding mat_block_size_def using vec_count_MV_Rel_direct assms MM_Rel_MV_Rel_col
  by (metis mat_mod_vec_mod_col to_int_mod_ring_hom.hom_one) 

lemma mat_inter_num_MM_Rel: 
  assumes "MM_Rel A B"
  assumes "j1 < dim_col A" "j2 < dim_col B"
  shows "mat_inter_num (mat_mod A) j1 j2 = mat_inter_num B j1 j2"
  unfolding mat_inter_num_def using assms index_map_mat mat_mod_dim(2)
  by (smt (z3) Collect_cong MM_Rel_def to_int_mod_ring_hom.hom_1 to_int_mod_ring_hom.hom_one) 


text \<open> Lift 01 and mat mod equivalence on 0-1 matrices \<close>

lemma of_int_mod_ring_lift_01_eq: 
  assumes "zero_one_matrix N"
  shows "map_mat (of_int_mod_ring) N = (lift_01_mat) N"
  apply (auto simp add: mat_eq_iff[of "map_mat (of_int_mod_ring) N" "lift_01_mat N"])
  using assms zero_one_matrix.M_not_one_simp by fastforce

lemma to_int_mod_ring_lift_01_eq: 
  assumes "zero_one_matrix N"
  shows "to_int_mat N = (lift_01_mat) N"
  apply (auto simp add: mat_eq_iff[of "to_int_mat N" "lift_01_mat N"])
  using assms using zero_one_matrix.M_not_zero_simp by fastforce 

end

subsection \<open>The Odd-town Problem\<close>
text \<open> The odd-town problem \<^cite>\<open>"babaiLINEARALGEBRAMETHODS1988"\<close> is perhaps one of the most common 
introductory problems for applying the linear algebra bound method to a combinatorial problem. 
In mathematical literature, it is considered simpler than Fisher's Inequality, however presents some 
interesting challenges to formalisation. Most significantly, it considers the incidence matrix to have 
elements of types integers mod 2. \<close>

text \<open>Initially, define a locale to represent the odd town context (a town with v people, and b groups) 
which must each be of odd size, but have an even intersection number with any other group \<close>
locale odd_town = ordered_design + 
  assumes odd_groups: "bl \<in># \<B> \<Longrightarrow> odd (card bl)"
  and even_inters: "bl1 \<in># \<B> \<Longrightarrow> bl2 \<in># (\<B> - {#bl1#})  \<Longrightarrow> even (bl1 |\<inter>| bl2)"
begin

lemma odd_town_no_repeat_clubs: "distinct_mset \<B>"
proof (rule ccontr)
  assume "\<not> distinct_mset \<B>"
  then obtain a where ain: "a \<in># \<B>" and countne: "count \<B> a \<noteq> 1"
    by (auto simp add: distinct_mset_def)
  then have "count \<B> a > 1"
    using nat_less_le by auto 
  then have ain2: "a \<in># (\<B> - {#a#})"
    by (simp add: in_diff_count) 
  then have "odd (a |\<inter>| a)" using odd_groups ain by simp
  thus False using even_inters ain ain2
    by blast 
qed

lemma odd_blocks_mat_block_size: "j < dim_col N \<Longrightarrow> odd (mat_block_size N j)"
  using mat_block_size_conv odd_groups 
  by (metis dim_col_is_b valid_blocks_index) 

lemma odd_block_size_mod_2: 
  assumes "CARD('b::prime_card) = 2"
  assumes "j < \<b>"
  shows "of_nat (card (\<B>s ! j)) = (1 :: 'b mod_ring)"
proof -
  have cb2: "CARD('b) = 2" using assms by simp
  then have "odd (card (\<B>s ! j))" using \<open>j < \<b>\<close> odd_groups by auto 
  then show "of_nat (card (\<B>s ! j)) = (1 :: 'b mod_ring)"
    by(transfer' fixing: j \<B>s, simp add: cb2) presburger
qed

lemma valid_indices_block_min: "j1 < dim_col N \<Longrightarrow> j2 < dim_col N \<Longrightarrow> j1 \<noteq> j2 \<Longrightarrow> \<b> \<ge> 2"
  by simp

lemma even_inter_mat_intersections: "j1 < dim_col N \<Longrightarrow> j2 < dim_col N \<Longrightarrow> j1 \<noteq> j2
  \<Longrightarrow> even (mat_inter_num N j1 j2)"
  using even_inters mat_inter_num_conv valid_indices_block_min
  by (metis dim_col_is_b obtains_two_diff_block_indexes) 

lemma even_inter_mod_2: 
  assumes "CARD('b::prime_card) = 2"
  assumes "i < \<b>" and jlt: "j < \<b>" and ne: "i \<noteq> j"
  shows "of_nat ((\<B>s ! i) |\<inter>| (\<B>s ! j)) = (0 :: 'b mod_ring)"
proof -
  have cb2: "CARD('b) = 2" using assms by simp
  have "even ((\<B>s ! i) |\<inter>| (\<B>s ! j))" using even_inters assms
    using blocks_index_ne_belong blocks_list_length valid_blocks_index by presburger 
  then show "of_nat ((\<B>s ! i) |\<inter>| (\<B>s ! j)) = (0 :: 'b mod_ring)"
    by (transfer' fixing: i j \<B>s, simp add: cb2)
qed

end

text \<open>The odd town locale must be simple by definition \<close>
sublocale odd_town \<subseteq> ordered_simple_design
  using odd_town_no_repeat_clubs by (unfold_locales) (meson distinct_mset_def) 

context odd_town 
begin

text \<open>The upper bound lemma (i.e. variation on Fisher's) for the odd town property using the linear 
bound argument. Notice it follows exactly the same pattern as the generalised version, however
it's sum manipulation argument is significantly simpler (in line with the mathematical proofs) \<close>
lemma upper_bound_clubs: 
  assumes "CARD('b::prime_card) = 2"
  shows "\<b> \<le> \<v>"
proof -
  have cb2: "CARD('b) = 2" using assms by simp
  then interpret mmt: mat_mod_type 2 "TYPE('b::prime_card)" 
    using assms by (unfold_locales) (simp_all)
  define N2 :: "'b mod_ring mat" where "N2 \<equiv> lift_01_mat N"
  show ?thesis proof (intro lin_bound_argument2[of "N2"])
    show "distinct (cols (N2))" using lift_01_distinct_cols_N N2_def by simp
    show n2cm:"N2 \<in> carrier_mat \<v> \<b>" using N2_def N_carrier_mat_01_lift by simp 
    have scalar_prod_odd: "\<And> i. i <\<b> \<Longrightarrow> ((col N2 i) \<bullet> (col N2 i)) = 1"
      using scalar_prod_block_size_lift_01 N2_def odd_block_size_mod_2 assms by (metis cb2) 
    have scalar_prod_even: "\<And> i j. i <\<b> \<Longrightarrow> j <\<b> \<Longrightarrow> i \<noteq> j \<Longrightarrow> ((col N2 i) \<bullet> (col N2 j)) = 0"
      using even_inter_mod_2 scalar_prod_inter_num_lift_01 N2_def assms by metis 
    show "\<And>f. vec \<v> (\<lambda>i. \<Sum>j = 0..<\<b>. f (col N2 j) * (col N2 j) $ i) = 0\<^sub>v \<v> \<Longrightarrow> \<forall>v\<in>set (cols N2). f v = 0"
    proof (auto)
      fix f v 
      assume eq0: "vec \<v> (\<lambda>i. \<Sum>j = 0..<length \<B>s. f (col N2 j) * (col N2 j) $ i) = 0\<^sub>v \<v>" 
      assume vin: "v \<in> set (cols N2)"
      define c where "c \<equiv> (\<lambda> j. f (col N2 j))"
      have inner: "\<And> j l. v $ l * (c j * (col N2 j) $ l) = c j * v $ l *  (col N2 j) $ l" 
        using mult.commute by auto
      obtain j' where v_def: "col N2 j' = v" and jvlt: "j' < dim_col N2"
        using vin by (metis cols_length cols_nth index_less_size_conv nth_index) 
      then have jvltb: "j' < \<b>" using n2cm by simp
      then have even0: "\<And> j. j \<in> {0..<\<b>} - {j'} \<Longrightarrow>  c j * (v \<bullet> (col N2 j)) = 0"
        using scalar_prod_even v_def by fastforce
      have vinc: "v \<in> carrier_vec \<v>" using n2cm set_cols_carrier vin by blast
      then have "0 = v \<bullet> vec \<v> (\<lambda>i. \<Sum>j = 0..<\<b>. c j * (col N2 j) $ i)"
        using eq0 c_def by auto  
      also have "... = (\<Sum> l =0..<dim_row N2 . v $ l *  (\<Sum> j = 0..<dim_col N2 . (c j * (col N2 j) $ l)))"
        unfolding scalar_prod_def using n2cm by auto 
      also have "... = (\<Sum> l =0..<dim_row N2 . (\<Sum> j = 0..<dim_col N2 . v $ l * (c j * (col N2 j) $ l)))"
        by (simp add: sum_distrib_left) 
      also have "... = (\<Sum> j \<in> {0..<dim_col N2} .  v \<bullet> (c j \<cdot>\<^sub>v (col N2 j)))" 
        using sum.swap scalar_prod_def[of v] by simp
      also have "... = v \<bullet> (c j' \<cdot>\<^sub>v v) + (\<Sum> j \<in> {0..<dim_col N2} - {j'}.  v \<bullet> (c j \<cdot>\<^sub>v (col N2 j)))" 
        using jvlt sum.remove[of "{0..<dim_col N2}" "j'" "\<lambda> j. v \<bullet> (c j \<cdot>\<^sub>v (col N2 j))"] v_def by simp
      also have "... = v \<bullet> (c j' \<cdot>\<^sub>v v) + (\<Sum> j \<in> {0..<\<b>} - {j'}.  c j * (v \<bullet> (col N2 j)))" 
        using n2cm scalar_prod_smult_distrib col_dim v_def by force 
      also have "... = v \<bullet> (c j' \<cdot>\<^sub>v v)" 
        using even0 by (simp add: sum.neutral)
      also have "... = (c j') * (v \<bullet> v)" 
        using scalar_prod_smult_distrib by (simp add: v_def)                 
      finally have "0 = (c j')" using v_def jvlt n2cm scalar_prod_odd by fastforce 
      then show "f v = 0" using c_def v_def by simp 
    qed
  qed
qed

end

end